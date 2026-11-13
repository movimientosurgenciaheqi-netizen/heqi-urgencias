"""
Servidor de derivaciones HEQI
- Recibe cada derivación (datos + PDF) enviada por el formulario web.
- Panel para Admisión: En espera / Pendiente / Aceptado / Servicio no disponible / Concluido fuera, con registro de quién y cuándo.
- Alarma de pedidos nuevos, estadísticas y descarga en planilla (CSV).

Variables de entorno:
  DATABASE_URL  PostgreSQL (recomendado en la nube). Si no hay, usa SQLite local (derivaciones.db).
  SECRET_KEY    clave larga al azar para las sesiones.
  ADMIN_USERS   usuarios del panel, formato "usuario:clave,usuario2:clave2".
  FORM_TOKEN    clave compartida con el formulario (la misma que API_TOKEN en el formulario).
"""
import os, io, csv, json, sqlite3, datetime, hmac, hashlib, secrets
from functools import wraps
from flask import Flask, request, jsonify, session, redirect, Response, send_file, render_template_string
from werkzeug.security import generate_password_hash, check_password_hash

app = Flask(__name__)
app.secret_key = os.environ.get('SECRET_KEY', 'cambiar-esta-clave')
app.config['MAX_CONTENT_LENGTH'] = 8 * 1024 * 1024
DB_URL = os.environ.get('DATABASE_URL', '')
PG = DB_URL.startswith('postgres')
FORM_TOKEN = os.environ.get('FORM_TOKEN', '')
CAMBIO_PIN = os.environ.get('CAMBIO_PIN', 'heqi')
USUARIOS_PIN = os.environ.get('USUARIOS_PIN', '1993')
# Paneles del sistema: al agregar un panel nuevo, se suma acá y aparece solo en Usuarios
MODULOS = [('traslados', '🚑 Traslados y estadísticas'), ('camas', '🛏 Comando de Camas'), ('actas', '📝 Actas con firma')]
ROLES = {'absoluto': 'Administrador absoluto', 'sub': 'Sub-administrador', 'modulos': 'Usuario por paneles'}
USUARIOS_FIJOS_CONFIGURADOS = 'ADMIN_USERS' in os.environ
USERS = dict(u.split(':', 1) for u in os.environ.get('ADMIN_USERS', 'admision:heqi2026').split(',') if ':' in u)
ESTADOS = {'en_espera': 'En espera', 'pendiente': 'Pendiente', 'aceptado': 'Aceptado', 'no_corresponde': 'Servicio no disponible - red IPS', 'concluido': 'Concluido fuera de Ingavi'}
CAMPOS = ['paciente', 'ci', 'edad', 'institucion', 'medico', 'telefono', 'diagnostico', 'cie10',
          'especialidad', 'criterio', 'news2', 'sofa', 'complejidad', 'alerta', 'rea']

# ---------- Base de datos ----------
def conectar():
    if PG:
        import psycopg2
        return psycopg2.connect(DB_URL.replace('postgres://', 'postgresql://', 1))
    return sqlite3.connect(os.environ.get('SQLITE_PATH', 'derivaciones.db'))

def q(sql):
    return sql.replace('?', '%s') if PG else sql

def iniciar():
    con = conectar(); cur = con.cursor()
    blob = 'BYTEA' if PG else 'BLOB'
    idcol = 'SERIAL PRIMARY KEY' if PG else 'INTEGER PRIMARY KEY AUTOINCREMENT'
    cur.execute(f"""CREATE TABLE IF NOT EXISTS derivaciones(
        id {idcol}, recibido TEXT, paciente TEXT, ci TEXT, edad TEXT, institucion TEXT, medico TEXT, telefono TEXT,
        diagnostico TEXT, cie10 TEXT, especialidad TEXT, criterio TEXT, news2 TEXT, sofa TEXT, complejidad TEXT, alerta TEXT, rea TEXT,
        estado TEXT DEFAULT 'en_espera', decidido_por TEXT, decidido_en TEXT, observacion TEXT,
        pdf_nombre TEXT, pdf {blob})""")
    con.commit()
    cur.execute('CREATE TABLE IF NOT EXISTS usuarios(usuario TEXT PRIMARY KEY, nombre TEXT, clave_hash TEXT, rol TEXT, creado TEXT)')
    con.commit()
    try:
        cur.execute('ALTER TABLE usuarios ADD COLUMN ' + ('IF NOT EXISTS ' if PG else '') + 'modulos TEXT')
        con.commit()
    except Exception:
        con.rollback() if PG else None
    cur.execute('CREATE TABLE IF NOT EXISTS camas_estado(id INTEGER PRIMARY KEY, version INTEGER, data TEXT, actualizado TEXT, usuario TEXT)')
    con.commit()
    cur.execute(f"""CREATE TABLE IF NOT EXISTS actas(
        id {idcol}, codigo TEXT UNIQUE, titulo TEXT, asunto TEXT, lugar TEXT, fecha TEXT, hora TEXT,
        pdf_nombre TEXT, pdf {blob}, pdf_hash TEXT, abierta INTEGER DEFAULT 1, creado TEXT, creado_por TEXT)""")
    con.commit()
    cur.execute(f"""CREATE TABLE IF NOT EXISTS firmas_acta(
        id {idcol}, acta_id INTEGER, nombre TEXT, apellido TEXT, ci TEXT, correo TEXT, telefono TEXT,
        dependencia TEXT, cargo TEXT, firma TEXT, fecha TEXT, hash TEXT)""")
    con.commit()
    for col in ('medico_acepta', 'concluido_donde'):
        try:
            cur.execute('ALTER TABLE derivaciones ADD COLUMN ' + ('IF NOT EXISTS ' if PG else '') + col + ' TEXT')
            con.commit()
        except Exception:
            con.rollback() if PG else None
    con.close()

def ahora():
    # Hora de Paraguay (UTC-3 todo el año)
    return datetime.datetime.now(datetime.timezone(datetime.timedelta(hours=-3))).strftime('%Y-%m-%d %H:%M:%S')

def fila_dict(cur, row):
    return {d[0]: v for d, v in zip(cur.description, row)}

# ---------- Seguridad ----------
def requiere_login(f):
    @wraps(f)
    def w(*a, **k):
        if not session.get('usuario'):
            return (jsonify(error='sesión vencida'), 401) if request.path.startswith('/api/') else redirect('/login')
        return f(*a, **k)
    return w

def rol_normal(rol, mods):
    # Compatibilidad con usuarios creados antes: admin -> absoluto, operador -> traslados
    if rol == 'admin': return 'absoluto', []
    if rol in ('absoluto', 'sub'): return rol, []
    m = [x for x in (mods or '').split(',') if x in dict(MODULOS)]
    if rol == 'operador' and not m: m = ['traslados']
    return 'modulos', m

# Cierre de sesión automático por inactividad (minutos). Se puede cambiar con la variable SESION_MINUTOS en Vercel.
SESION_MINUTOS = int(os.environ.get('SESION_MINUTOS', '30'))

@app.before_request
def vencimiento_sesion():
    import time
    if not session.get('usuario'): return
    p = request.path
    if p.startswith(('/acta/', '/icon/', '/favicon', '/apple-touch', '/manifest', '/api/derivaciones', '/login', '/logout')): return
    # Abrir el link desde afuera (ícono, WhatsApp, escribir la dirección) siempre pide usuario y contraseña;
    # moverse dentro del sistema (panel, camas, actas) no la pide de nuevo.
    if request.method == 'GET' and p in ('/', '/camas'):
        ref = request.referrer or ''
        if not ref.startswith(request.host_url.rstrip('/')):
            session.clear(); return redirect('/login')
    ahora_s = time.time(); ult = session.get('ult', ahora_s)
    if ahora_s - ult > SESION_MINUTOS * 60:
        session.clear()
        return (jsonify(error='sesión vencida'), 401) if p.startswith('/api/') else redirect('/login')
    # los sondeos automáticos (alarma, sincronización) no cuentan como actividad
    if not p.startswith(('/api/lista', '/api/camas/version')):
        session['ult'] = ahora_s

def refrescar_sesion():
    u = session.get('usuario')
    if not u or u in USERS: return
    try:
        con = conectar(); cur = con.cursor()
        cur.execute(q('SELECT rol, modulos FROM usuarios WHERE usuario=?'), (u,)); r = cur.fetchone(); con.close()
    except Exception:
        return
    if not r: session.clear(); return
    session['rol'], session['mods'] = rol_normal(r[0], r[1])

def permisos():
    refrescar_sesion()
    if session.get('rol') in ('absoluto', 'sub', 'admin'): return [k for k, _ in MODULOS]
    return [m for m in session.get('mods', []) if m in dict(MODULOS)]

def requiere_modulo(mod):
    def deco(f):
        @wraps(f)
        def w(*a, **k):
            if not session.get('usuario'):
                return (jsonify(error='sesión vencida'), 401) if request.path.startswith('/api/') else redirect('/login')
            if mod not in permisos():
                return (jsonify(error='Sin permiso para este panel'), 403) if request.path.startswith('/api/') else ('No tenés permiso para este panel. <a href="/">Volver</a>', 403)
            return f(*a, **k)
        return w
    return deco

def requiere_absoluto(f):
    # Solo el administrador absoluto, y después de ingresar el PIN de usuarios (vale 15 minutos)
    @wraps(f)
    def w(*a, **k):
        if not session.get('usuario'): return jsonify(error='sesión vencida'), 401
        if session.get('rol') not in ('absoluto', 'admin'): return jsonify(error='Solo el administrador absoluto'), 403
        import time
        if session.get('pin_usuarios', 0) < time.time(): return jsonify(error='pin', pin=True), 403
        return f(*a, **k)
    return w

@app.route('/api/usuarios/pin', methods=['POST'])
def usuarios_pin():
    import time
    if session.get('rol') not in ('absoluto', 'admin'): return jsonify(error='Solo el administrador absoluto'), 403
    pin = str(request.get_json(force=True).get('pin', '')).strip()
    if not hmac.compare_digest(pin.encode(), USUARIOS_PIN.encode()):
        return jsonify(error='PIN incorrecto'), 403
    session['pin_usuarios'] = time.time() + 15 * 60
    return jsonify(ok=True)

@app.after_request
def cors(resp):
    if request.path == '/api/derivaciones':
        resp.headers['Access-Control-Allow-Origin'] = '*'
        resp.headers['Access-Control-Allow-Headers'] = 'Content-Type, X-Form-Token'
        resp.headers['Access-Control-Allow-Methods'] = 'POST, OPTIONS'
    return resp

# ---------- Recepción desde el formulario ----------
@app.route('/api/derivaciones', methods=['POST', 'OPTIONS'])
def recibir():
    if request.method == 'OPTIONS':
        return ('', 204)
    if FORM_TOKEN and not hmac.compare_digest(request.headers.get('X-Form-Token', ''), FORM_TOKEN):
        return jsonify(error='token inválido'), 403
    datos = json.loads(request.form.get('datos', '{}'))
    pdf = request.files.get('pdf')
    vals = [str(datos.get(c, ''))[:2000] for c in CAMPOS]
    con = conectar(); cur = con.cursor()
    sql = q('INSERT INTO derivaciones(recibido,' + ','.join(CAMPOS) + ',estado,pdf_nombre,pdf) VALUES(?,' + ','.join('?' * len(CAMPOS)) + ",'en_espera',?,?)")
    contenido = pdf.read() if pdf else None
    if PG:
        import psycopg2
        contenido = psycopg2.Binary(contenido) if contenido else None
    cur.execute(sql + (' RETURNING id' if PG else ''), [ahora()] + vals + [pdf.filename if pdf else '', contenido])
    nuevo = cur.fetchone()[0] if PG else cur.lastrowid
    con.commit(); con.close()
    return jsonify(ok=True, id=nuevo)

# ---------- Panel ----------
@app.route('/login', methods=['GET', 'POST'])
def login():
    err = ''
    if request.method == 'POST':
        u = request.form.get('usuario', '').strip().lower(); c = request.form.get('clave', '')
        if u in USERS and hmac.compare_digest(USERS[u].encode(), c.encode()) and usuario_fijo_activo():
            session.clear(); session['usuario'] = u; session['ult'] = __import__('time').time(); session['rol'] = 'absoluto'; session['mods'] = []; return redirect('/')
        con = conectar(); cur = con.cursor()
        cur.execute(q('SELECT clave_hash, rol, modulos FROM usuarios WHERE usuario=?'), (u,))
        r = cur.fetchone(); con.close()
        if r and check_password_hash(r[0], c):
            rol, mods = rol_normal(r[1], r[2])
            session.clear(); session['usuario'] = u; session['ult'] = __import__('time').time(); session['rol'] = rol; session['mods'] = mods; return redirect('/')
        err = 'Usuario o contraseña incorrectos.'
    return render_template_string(LOGIN_HTML, err=err)

@app.route('/logout')
def logout():
    session.clear(); return redirect('/login')

@app.route('/')
@requiere_login
def panel():
    rol, perms = session.get('rol', 'modulos'), permisos()
    if not perms and rol not in ('absoluto', 'sub'): return 'Tu usuario no tiene paneles asignados. Pedí acceso al administrador. <a href="/logout">Salir</a>', 403
    if perms == ['camas']: return redirect('/camas')
    return render_template_string(PANEL_HTML, usuario=session['usuario'], rol=rol, perms=perms, mods=MODULOS, roles=ROLES)

@app.route('/api/lista')
@requiere_modulo('traslados')
def lista():
    con = conectar(); cur = con.cursor()
    cur.execute('SELECT id,recibido,' + ','.join(CAMPOS) + ',estado,decidido_por,decidido_en,observacion,medico_acepta,concluido_donde,pdf_nombre FROM derivaciones ORDER BY id DESC LIMIT 2000')
    filas = [fila_dict(cur, r) for r in cur.fetchall()]
    con.close()
    return jsonify(filas)

@app.route('/api/estado/<int:i>', methods=['POST'])
@requiere_modulo('traslados')
def estado(i):
    d = request.get_json(force=True)
    e = d.get('estado')
    if e not in ESTADOS: return jsonify(error='estado inválido'), 400
    if not hmac.compare_digest(str(d.get('pin', '')).strip().lower().encode(), CAMBIO_PIN.strip().lower().encode()):
        return jsonify(error='PIN incorrecto'), 403
    if e == 'aceptado' and not str(d.get('medico_acepta', '')).strip(): return jsonify(error='Falta el médico que acepta'), 400
    if e == 'concluido' and not str(d.get('concluido_donde', '')).strip(): return jsonify(error='Falta dónde concluyó'), 400
    con = conectar(); cur = con.cursor()
    if e == 'en_espera':
        cur.execute(q('UPDATE derivaciones SET estado=?, decidido_por=NULL, decidido_en=NULL, medico_acepta=NULL, concluido_donde=NULL WHERE id=?'), (e, i))
    else:
        cur.execute(q('UPDATE derivaciones SET estado=?, decidido_por=?, decidido_en=?, observacion=?, medico_acepta=?, concluido_donde=? WHERE id=?'),
                    (e, session['usuario'], ahora(), d.get('observacion', '')[:1000], (d.get('medico_acepta', '') if e == 'aceptado' else '')[:200], (d.get('concluido_donde', '') if e == 'concluido' else '')[:300], i))
    con.commit(); con.close()
    return jsonify(ok=True)

def usuario_fijo_activo():
    # El usuario de ejemplo (admision/heqi2026) deja de funcionar solo cuando ya existe un administrador propio.
    if USUARIOS_FIJOS_CONFIGURADOS: return True
    con = conectar(); cur = con.cursor()
    cur.execute("SELECT COUNT(*) FROM usuarios WHERE rol IN ('admin','absoluto')")
    n = cur.fetchone()[0]; con.close()
    return n == 0

def requiere_admin(f):
    @wraps(f)
    def w(*a, **k):
        if not session.get('usuario'): return jsonify(error='sesión vencida'), 401
        if session.get('rol') != 'admin': return jsonify(error='solo administradores'), 403
        return f(*a, **k)
    return w

@app.route('/api/usuarios', methods=['GET', 'POST'])
@requiere_absoluto
def usuarios():
    con = conectar(); cur = con.cursor()
    if request.method == 'GET':
        cur.execute('SELECT usuario, nombre, rol, modulos, creado FROM usuarios ORDER BY usuario')
        filas = []
        for r in cur.fetchall():
            x = fila_dict(cur, r); x['rol'], m = rol_normal(x['rol'], x['modulos']); x['modulos'] = m; filas.append(x)
        if usuario_fijo_activo():
            filas += [{'usuario': u, 'nombre': '(usuario de inicio: se desactiva al crear tu administrador absoluto)', 'rol': 'absoluto', 'modulos': [], 'creado': '', 'fijo': True} for u in USERS]
        con.close(); return jsonify(filas)
    d = request.get_json(force=True)
    u = str(d.get('usuario', '')).strip().lower(); clave = str(d.get('clave', ''))
    rol = d.get('rol') if d.get('rol') in ROLES else 'modulos'
    mods = [m for m in (d.get('modulos') or []) if m in dict(MODULOS)] if rol == 'modulos' else []
    if not u or not all(ch.isalnum() or ch in '._-' for ch in u): con.close(); return jsonify(error='Usuario inválido: solo letras, números, punto o guion'), 400
    if u in USERS: con.close(); return jsonify(error='Ese usuario es fijo y no se puede cambiar acá'), 400
    if rol == 'modulos' and not mods: con.close(); return jsonify(error='Marcá al menos un panel para este usuario'), 400
    cur.execute(q('SELECT usuario FROM usuarios WHERE usuario=?'), (u,))
    existe = cur.fetchone()
    if u == session.get('usuario') and rol != 'absoluto': con.close(); return jsonify(error='No podés quitarte a vos mismo el rol de administrador absoluto'), 400
    if clave and len(clave) < 6: con.close(); return jsonify(error='La contraseña debe tener al menos 6 caracteres'), 400
    if not existe and not clave: con.close(); return jsonify(error='Escribí una contraseña para el usuario nuevo'), 400
    nombre = str(d.get('nombre', ''))[:120]
    if existe:
        if clave:
            cur.execute(q('UPDATE usuarios SET nombre=?, clave_hash=?, rol=?, modulos=? WHERE usuario=?'), (nombre, generate_password_hash(clave), rol, ','.join(mods), u))
        else:
            cur.execute(q('UPDATE usuarios SET nombre=?, rol=?, modulos=? WHERE usuario=?'), (nombre, rol, ','.join(mods), u))
    else:
        cur.execute(q('INSERT INTO usuarios(usuario, nombre, clave_hash, rol, modulos, creado) VALUES(?,?,?,?,?,?)'), (u, nombre, generate_password_hash(clave), rol, ','.join(mods), ahora()))
    con.commit(); con.close()
    return jsonify(ok=True)

@app.route('/api/usuarios/<u>', methods=['DELETE'])
@requiere_absoluto
def borrar_usuario(u):
    u = u.strip().lower()
    if u == session.get('usuario'): return jsonify(error='No podés borrar tu propio usuario'), 400
    con = conectar(); cur = con.cursor()
    cur.execute(q('DELETE FROM usuarios WHERE usuario=?'), (u,))
    con.commit(); con.close()
    return jsonify(ok=True)


# ================= ACTAS CON FIRMA =================
CAMPOS_FIRMA = ['nombre', 'apellido', 'ci', 'correo', 'telefono', 'dependencia', 'cargo']

def acta_por_codigo(cur, codigo):
    cur.execute(q('SELECT id,codigo,titulo,asunto,lugar,fecha,hora,pdf_nombre,pdf_hash,abierta,creado FROM actas WHERE codigo=?'), (codigo,))
    r = cur.fetchone()
    return fila_dict(cur, r) if r else None

@app.route('/api/actas', methods=['GET', 'POST'])
@requiere_modulo('actas')
def api_actas():
    con = conectar(); cur = con.cursor()
    if request.method == 'GET':
        cur.execute('SELECT a.id,a.codigo,a.titulo,a.asunto,a.lugar,a.fecha,a.hora,a.pdf_nombre,a.abierta,a.creado,(SELECT COUNT(*) FROM firmas_acta f WHERE f.acta_id=a.id) AS firmas FROM actas a ORDER BY a.id DESC')
        filas = [fila_dict(cur, r) for r in cur.fetchall()]; con.close(); return jsonify(filas)
    f = request.form; pdf = request.files.get('pdf')
    titulo = f.get('titulo', '').strip()[:200]
    if not titulo: con.close(); return jsonify(error='Falta el título del acta'), 400
    contenido = pdf.read() if pdf else None
    if contenido and len(contenido) > 3_500_000: con.close(); return jsonify(error='El PDF supera 3,5 MB. Comprimilo o reducilo.'), 400
    pdf_hash = hashlib.sha256(contenido).hexdigest() if contenido else ''
    if PG and contenido:
        import psycopg2; contenido = psycopg2.Binary(contenido)
    codigo = secrets.token_urlsafe(9)
    cur.execute(q('INSERT INTO actas(codigo,titulo,asunto,lugar,fecha,hora,pdf_nombre,pdf,pdf_hash,abierta,creado,creado_por) VALUES(?,?,?,?,?,?,?,?,?,1,?,?)'),
                (codigo, titulo, f.get('asunto', '')[:300], f.get('lugar', '')[:200], f.get('fecha', '')[:20], f.get('hora', '')[:10],
                 pdf.filename if pdf else '', contenido, pdf_hash, ahora(), session['usuario']))
    con.commit(); con.close()
    return jsonify(ok=True, codigo=codigo)

@app.route('/api/actas/<int:i>', methods=['POST', 'DELETE'])
@requiere_modulo('actas')
def api_acta(i):
    con = conectar(); cur = con.cursor()
    if request.method == 'DELETE':
        cur.execute(q('DELETE FROM firmas_acta WHERE acta_id=?'), (i,)); cur.execute(q('DELETE FROM actas WHERE id=?'), (i,))
    else:
        cur.execute(q('UPDATE actas SET abierta=? WHERE id=?'), (1 if request.get_json(force=True).get('abierta') else 0, i))
    con.commit(); con.close(); return jsonify(ok=True)

@app.route('/api/actas/<int:i>/firmas')
@requiere_modulo('actas')
def api_firmas(i):
    con = conectar(); cur = con.cursor()
    cur.execute(q('SELECT id,nombre,apellido,ci,dependencia,cargo,fecha,hash FROM firmas_acta WHERE acta_id=? ORDER BY id'), (i,))
    filas = [fila_dict(cur, r) for r in cur.fetchall()]; con.close(); return jsonify(filas)

@app.route('/api/firmas/<int:i>', methods=['DELETE'])
@requiere_modulo('actas')
def api_borrar_firma(i):
    con = conectar(); cur = con.cursor(); cur.execute(q('DELETE FROM firmas_acta WHERE id=?'), (i,)); con.commit(); con.close()
    return jsonify(ok=True)

@app.route('/actas/<int:i>/presentes')
@requiere_modulo('actas')
def hoja_presentes(i):
    con = conectar(); cur = con.cursor()
    cur.execute(q('SELECT codigo FROM actas WHERE id=?'), (i,)); r = cur.fetchone()
    if not r: con.close(); return 'Acta no encontrada', 404
    a = acta_por_codigo(cur, r[0])
    cur.execute(q('SELECT nombre,apellido,ci,correo,telefono,dependencia,cargo,firma,fecha,hash FROM firmas_acta WHERE acta_id=? ORDER BY id'), (i,))
    firmas = [fila_dict(cur, x) for x in cur.fetchall()]; con.close()
    return render_template_string(PRESENTES_HTML, a=a, firmas=firmas, generado=ahora(), usuario=session['usuario'])

# ---- páginas públicas (sin usuario): ver el acta y firmar ----
@app.route('/acta/<codigo>')
def acta_publica(codigo):
    con = conectar(); cur = con.cursor(); a = acta_por_codigo(cur, codigo)
    if not a: con.close(); return 'Acta no encontrada o link incorrecto.', 404
    cur.execute(q('SELECT COUNT(*) FROM firmas_acta WHERE acta_id=?'), (a['id'],)); n = cur.fetchone()[0]; con.close()
    return render_template_string(ACTA_PUBLICA_HTML, a=a, n=n)

@app.route('/acta/<codigo>/pdf')
def acta_pdf(codigo):
    con = conectar(); cur = con.cursor()
    cur.execute(q('SELECT pdf_nombre,pdf FROM actas WHERE codigo=?'), (codigo,)); r = cur.fetchone(); con.close()
    if not r or not r[1]: return 'Esta acta no tiene PDF adjunto.', 404
    return send_file(io.BytesIO(bytes(r[1])), mimetype='application/pdf', download_name=r[0] or 'acta.pdf')

@app.route('/acta/<codigo>/firmar', methods=['POST'])
def acta_firmar(codigo):
    con = conectar(); cur = con.cursor(); a = acta_por_codigo(cur, codigo)
    if not a: con.close(); return jsonify(error='Acta no encontrada'), 404
    if not a['abierta']: con.close(); return jsonify(error='El acta ya está cerrada: no admite más firmas.'), 400
    d = request.get_json(force=True)
    v = {c: str(d.get(c, '')).strip()[:150] for c in CAMPOS_FIRMA}
    firma = str(d.get('firma', ''))
    if not v['nombre'] or not v['apellido']: con.close(); return jsonify(error='Completá nombre y apellido.'), 400
    if not firma.startswith('data:image/png;base64,') or len(firma) > 400_000 or len(firma) < 1500: con.close(); return jsonify(error='Dibujá tu firma en el recuadro.'), 400
    if v['ci']:
        cur.execute(q('SELECT COUNT(*) FROM firmas_acta WHERE acta_id=? AND ci=?'), (a['id'], v['ci']))
        if cur.fetchone()[0]: con.close(); return jsonify(error='Esta cédula ya firmó el acta.'), 400
    fecha = ahora()
    huella = hashlib.sha256('|'.join([a['codigo'], a['pdf_hash'] or '', fecha] + [v[c] for c in CAMPOS_FIRMA] + [hashlib.sha256(firma.encode()).hexdigest()]).encode()).hexdigest()
    cur.execute(q('INSERT INTO firmas_acta(acta_id,' + ','.join(CAMPOS_FIRMA) + ',firma,fecha,hash) VALUES(?,' + ','.join('?' * len(CAMPOS_FIRMA)) + ',?,?,?)'),
                [a['id']] + [v[c] for c in CAMPOS_FIRMA] + [firma, fecha, huella])
    con.commit(); con.close()
    return jsonify(ok=True, codigo=huella[:12].upper(), fecha=fecha)

ACTA_PUBLICA_HTML = r"""<!doctype html><html lang="es"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>{{ a.titulo }} - Firma</title><link rel="icon" type="image/png" href="/icon/fav-48.png"><link rel="apple-touch-icon" href="/apple-touch-icon.png"><link rel="manifest" href="/manifest.webmanifest"><meta name="theme-color" content="#1d4a42"><meta name="apple-mobile-web-app-capable" content="yes"><meta name="mobile-web-app-capable" content="yes"><meta name="apple-mobile-web-app-title" content="HEQI"><style>
:root{--verde:#1d4a42;--verde2:#2e7d5b;--linea:#dfe5e3;--gris:#5b6b70;--fondo:#f1f4f3;--rojo:#b03a2e}
*{box-sizing:border-box}body{margin:0;font-family:"Segoe UI",Roboto,Arial,sans-serif;background:var(--fondo);color:#1b2a28}
header{background:var(--verde);color:#fff;padding:16px 18px}header small{opacity:.8}header h1{margin:4px 0 0;font-size:1.25rem}
.wrap{max-width:640px;margin:0 auto;padding:14px}
.card{background:#fff;border:1px solid var(--linea);border-radius:14px;padding:16px;margin-bottom:14px}
.dato{display:grid;grid-template-columns:90px 1fr;gap:4px 10px;font-size:.92rem}.dato b{color:var(--gris);font-size:.8rem;text-transform:uppercase}
.btnpdf{display:block;text-align:center;margin-top:12px;padding:12px;border-radius:10px;border:2px solid var(--verde);color:var(--verde);font-weight:800;text-decoration:none}
label{display:block;font-weight:700;font-size:.88rem;margin:12px 0 5px}label i{color:var(--rojo);font-style:normal}
input{width:100%;padding:11px;border:1.5px solid var(--linea);border-radius:9px;font:inherit}
#pad{width:100%;height:190px;border:2px dashed #b9c6c2;border-radius:10px;background:#fff;touch-action:none;display:block}
.fila{display:flex;justify-content:space-between;align-items:center;margin-top:6px;color:var(--gris);font-size:.82rem}
.fila button{border:1.5px solid var(--linea);background:#fff;border-radius:8px;padding:6px 10px;font-weight:700}
.ok{width:100%;margin-top:16px;padding:14px;border:0;border-radius:12px;background:var(--verde2);color:#fff;font-size:1.05rem;font-weight:800}
.ok:disabled{opacity:.6}.nota{font-size:.8rem;color:var(--gris);margin-top:10px}
.chk{display:flex;gap:8px;align-items:flex-start;margin-top:14px;font-size:.88rem}.chk input{width:auto;margin-top:3px}
#hecho{display:none;text-align:center}#hecho h2{color:var(--verde2)}
.err{color:var(--rojo);font-weight:700;margin-top:10px}
</style></head><body>
<header style="display:flex;align-items:center;gap:10px"><img src="/icon/logo-mark.png" alt="HEQI" style="height:42px;background:#fff;border-radius:8px;padding:3px 5px;vertical-align:middle;margin:0"><div><small>HEQI - Acta de reunión</small><h1>{{ a.titulo }}</h1></div></header>
<div class="wrap">
  <div class="card">
    <div class="dato">{% if a.asunto %}<b>Asunto</b><span>{{ a.asunto }}</span>{% endif %}{% if a.lugar %}<b>Lugar</b><span>{{ a.lugar }}</span>{% endif %}
      {% if a.fecha %}<b>Fecha</b><span>{{ a.fecha }}{% if a.hora %} - {{ a.hora }}{% endif %}</span>{% endif %}<b>Firmas</b><span>{{ n }} hasta ahora</span></div>
    {% if a.pdf_nombre %}<a class="btnpdf" href="/acta/{{ a.codigo }}/pdf" target="_blank">📄 Leer el acta (PDF)</a>{% endif %}
  </div>
  {% if a.abierta %}
  <div class="card" id="formulario">
    <h2 style="margin:0 0 4px;font-size:1.1rem">✍️ Registrar mi asistencia y firma</h2>
    <p class="nota" style="margin:0">Completá tus datos para quedar registrado en la hoja de presentes de esta acta.</p>
    <label>Nombre <i>*</i></label><input id="nombre" autocomplete="given-name">
    <label>Apellido <i>*</i></label><input id="apellido" autocomplete="family-name">
    <label>Cédula de identidad</label><input id="ci" inputmode="numeric">
    <label>Correo electrónico</label><input id="correo" type="email" placeholder="tu.correo@ips.gov.py">
    <label>Teléfono</label><input id="telefono" inputmode="tel">
    <label>Dependencia / Servicio</label><input id="dependencia" placeholder="Ej.: Urgencias HEQI">
    <label>Cargo / Función</label><input id="cargo" placeholder="Ej.: Jefe de Área">
    <label>Firma <i>*</i></label><canvas id="pad"></canvas>
    <div class="fila"><span>Dibujá tu firma con el dedo</span><button type="button" id="limpiar">Limpiar</button></div>
    <div class="chk"><input type="checkbox" id="acepto"><span>Leí el acta y confirmo mi asistencia.</span></div>
    <div class="err" id="err"></div>
    <button class="ok" id="enviar">✓ Confirmar mi firma</button>
    <p class="nota">🔒 Tu firma queda sellada con un código único (SHA-256) junto con los datos del acta: si algo se modifica, el código deja de coincidir. Es una firma electrónica simple de registro.</p>
  </div>
  {% else %}
  <div class="card"><b>Esta acta ya está cerrada</b> y no admite más firmas.</div>
  {% endif %}
  <div class="card" id="hecho"><h2>✓ ¡Firma registrada!</h2><p>Gracias. Tu firma quedó incorporada a la hoja de presentes.</p><p class="nota" id="hechoCod"></p></div>
</div>
<script>
(function(){
  const pad=document.getElementById('pad'); if(!pad) return;
  const ctx=pad.getContext('2d'); let dib=false, trazos=0;
  function ajustar(){ const r=pad.getBoundingClientRect(), k=window.devicePixelRatio||1; pad.width=r.width*k; pad.height=r.height*k; ctx.setTransform(k,0,0,k,0,0); ctx.lineWidth=2.4; ctx.lineCap='round'; ctx.lineJoin='round'; ctx.strokeStyle='#0d1b3a'; trazos=0; }
  ajustar(); window.addEventListener('resize',()=>{ if(!trazos) ajustar(); });
  const pos=e=>{ const r=pad.getBoundingClientRect(); return [e.clientX-r.left,e.clientY-r.top]; };
  pad.addEventListener('pointerdown',e=>{ dib=true; pad.setPointerCapture(e.pointerId); const [x,y]=pos(e); ctx.beginPath(); ctx.moveTo(x,y); });
  pad.addEventListener('pointermove',e=>{ if(!dib) return; const [x,y]=pos(e); ctx.lineTo(x,y); ctx.stroke(); trazos++; });
  ['pointerup','pointercancel','pointerleave'].forEach(t=>pad.addEventListener(t,()=>dib=false));
  document.getElementById('limpiar').onclick=()=>{ ctx.clearRect(0,0,pad.width,pad.height); trazos=0; };
  const $=id=>document.getElementById(id);
  $('enviar').onclick=async()=>{
    $('err').textContent='';
    if(!$('nombre').value.trim()||!$('apellido').value.trim()){ $('err').textContent='Completá nombre y apellido.'; return; }
    if(trazos<8){ $('err').textContent='Dibujá tu firma en el recuadro.'; return; }
    if(!$('acepto').checked){ $('err').textContent='Marcá la casilla de confirmación.'; return; }
    $('enviar').disabled=true; $('enviar').textContent='Guardando…';
    const d={firma:pad.toDataURL('image/png')}; ['nombre','apellido','ci','correo','telefono','dependencia','cargo'].forEach(k=>d[k]=$(k).value);
    try{
      const r=await fetch(location.pathname.replace(/\/$/,'')+'/firmar',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(d)});
      const j=await r.json();
      if(r.ok){ $('formulario').style.display='none'; $('hecho').style.display='block'; $('hechoCod').textContent='Código de verificación: '+j.codigo+' - '+j.fecha; window.scrollTo(0,0); }
      else { $('err').textContent=j.error||'No se pudo guardar.'; }
    }catch(e){ $('err').textContent='Sin conexión. Intentá de nuevo.'; }
    $('enviar').disabled=false; $('enviar').textContent='✓ Confirmar mi firma';
  };
})();
</script></body></html>"""

PRESENTES_HTML = r"""<!doctype html><html lang="es"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Hoja de presentes - {{ a.titulo }}</title><link rel="icon" type="image/png" href="/icon/fav-48.png"><link rel="apple-touch-icon" href="/apple-touch-icon.png"><link rel="manifest" href="/manifest.webmanifest"><meta name="theme-color" content="#1d4a42"><meta name="apple-mobile-web-app-capable" content="yes"><meta name="mobile-web-app-capable" content="yes"><meta name="apple-mobile-web-app-title" content="HEQI"><style>
@page{size:A4;margin:14mm}
body{font-family:Arial,Helvetica,sans-serif;color:#111;margin:0;padding:16px;font-size:11px}
.barra{display:flex;gap:8px;margin-bottom:12px}.barra button{padding:10px 14px;border-radius:8px;border:0;background:#1d4a42;color:#fff;font-weight:700;font-size:13px}
h1{font-size:16px;margin:0 0 2px;color:#1d4a42}h2{font-size:13px;margin:0 0 8px;font-weight:normal}
.cab{border:1.5px solid #1d4a42;border-radius:6px;padding:8px 10px;margin-bottom:10px}
.cab table td{padding:2px 8px 2px 0;font-size:11px}
table.f{width:100%;border-collapse:collapse}
table.f th{background:#e8efed;border:1px solid #9aa8a5;padding:5px;font-size:10px;text-align:left}
table.f td{border:1px solid #9aa8a5;padding:4px 5px;vertical-align:middle;font-size:10.5px}
table.f tr{page-break-inside:avoid}
td.firma img{height:46px;max-width:150px;display:block}
.cod{font-family:monospace;font-size:9px;color:#444}
.pie{margin-top:10px;font-size:9px;color:#444;line-height:1.4}
@media print{.barra{display:none}body{padding:0}}
</style></head><body>
<div class="barra"><button onclick="window.print()">🖨 Imprimir / Guardar PDF</button></div>
<img src="/icon/logo-full.png" alt="HEQI" style="height:70px;float:right"><h1>HOJA DE PRESENTES Y FIRMAS</h1><h2>Hospital de Especialidades Quirúrgicas Ingavi (HEQI) - IPS</h2>
<div class="cab"><table>
<tr><td><b>Acta:</b></td><td>{{ a.titulo }}</td></tr>
{% if a.asunto %}<tr><td><b>Asunto:</b></td><td>{{ a.asunto }}</td></tr>{% endif %}
{% if a.lugar %}<tr><td><b>Lugar:</b></td><td>{{ a.lugar }}</td></tr>{% endif %}
{% if a.fecha %}<tr><td><b>Fecha:</b></td><td>{{ a.fecha }}{% if a.hora %} - {{ a.hora }}{% endif %}</td></tr>{% endif %}
<tr><td><b>Firmantes:</b></td><td>{{ firmas|length }}</td></tr>
{% if a.pdf_hash %}<tr><td><b>Huella del PDF:</b></td><td class="cod">{{ a.pdf_hash }}</td></tr>{% endif %}
</table></div>
<table class="f"><thead><tr><th>N°</th><th>Nombre y apellido</th><th>CI</th><th>Dependencia / Cargo</th><th>Fecha y hora</th><th>Firma</th><th>Verificación</th></tr></thead><tbody>
{% for f in firmas %}<tr><td>{{ loop.index }}</td><td><b>{{ f.nombre }} {{ f.apellido }}</b>{% if f.correo %}<br>{{ f.correo }}{% endif %}</td><td>{{ f.ci }}</td>
<td>{{ f.dependencia }}{% if f.dependencia and f.cargo %}<br>{% endif %}{{ f.cargo }}</td><td>{{ f.fecha }}</td><td class="firma"><img src="{{ f.firma }}" alt="firma"></td><td class="cod">{{ f.hash[:12]|upper }}</td></tr>
{% else %}<tr><td colspan="7" style="text-align:center;padding:20px">Todavía no hay firmas.</td></tr>{% endfor %}
</tbody></table>
<p class="pie">Firmas electrónicas simples registradas mediante el enlace del acta. Cada firma está sellada con un código SHA-256 calculado con los datos del acta, del firmante, la imagen de la firma y la hora; los primeros 12 caracteres figuran en la columna Verificación.
Hoja generada el {{ generado }} por {{ usuario }}.</p>
</body></html>"""

# ================= COMANDO DE CAMAS =================
from markupsafe import escape as _esc

@app.route('/camas')
@requiere_modulo('camas')
def camas():
    return Response(CAMAS_HTML.replace('__USUARIO__', str(_esc(session['usuario']))), mimetype='text/html')

def _camas_fila(cur):
    cur.execute('SELECT version, data, actualizado, usuario FROM camas_estado WHERE id=1')
    return cur.fetchone()

@app.route('/api/camas/version')
@requiere_modulo('camas')
def camas_version():
    con = conectar(); cur = con.cursor(); r = _camas_fila(cur); con.close()
    return jsonify(version=r[0] if r else 0, actualizado=r[2] if r else '', usuario=r[3] if r else '')

@app.route('/api/camas/estado', methods=['GET', 'POST'])
@requiere_modulo('camas')
def camas_estado():
    con = conectar(); cur = con.cursor(); r = _camas_fila(cur)
    if request.method == 'GET':
        con.close(); return jsonify(version=r[0] if r else 0, data=r[1] if r else None)
    d = request.get_json(force=True)
    actual = r[0] if r else 0
    if int(d.get('base', -1)) != actual:
        con.close(); return jsonify(version=actual, data=r[1] if r else None), 409
    data = d.get('data')
    if not isinstance(data, str) or len(data) > 4_000_000:
        con.close(); return jsonify(error='Datos inválidos o demasiado grandes'), 400
    if r and r[1]:
        try:
            cur.execute('CREATE TABLE IF NOT EXISTS camas_respaldo(id ' + ('SERIAL PRIMARY KEY' if PG else 'INTEGER PRIMARY KEY AUTOINCREMENT') + ', fecha TEXT, usuario TEXT, version INTEGER, data TEXT)')
            cur.execute('SELECT MAX(fecha) FROM camas_respaldo'); ult = cur.fetchone()[0]
            if not ult or ult < (datetime.datetime.now(datetime.timezone(datetime.timedelta(hours=-3))) - datetime.timedelta(minutes=30)).strftime('%Y-%m-%d %H:%M:%S'):
                cur.execute(q('INSERT INTO camas_respaldo(fecha, usuario, version, data) VALUES(?,?,?,?)'), (ahora(), r[3] or '', r[0], r[1]))
                cur.execute('DELETE FROM camas_respaldo WHERE id NOT IN (SELECT id FROM camas_respaldo ORDER BY id DESC LIMIT 100)')
        except Exception:
            con.rollback() if PG else None
            r = _camas_fila(cur)
    if r:
        cur.execute(q('UPDATE camas_estado SET version=?, data=?, actualizado=?, usuario=? WHERE id=1 AND version=?'), (actual + 1, data, ahora(), session['usuario'], actual))
        if cur.rowcount != 1:
            con.rollback(); r = _camas_fila(cur); con.close(); return jsonify(version=r[0], data=r[1]), 409
    else:
        cur.execute(q('INSERT INTO camas_estado(id, version, data, actualizado, usuario) VALUES(1,?,?,?,?)'), (1, data, ahora(), session['usuario']))
    con.commit(); con.close()
    return jsonify(ok=True, version=actual + 1)

@app.route('/camas/respaldos', methods=['GET', 'POST'])
@requiere_modulo('camas')
def camas_respaldos():
    if session.get('rol') not in ('absoluto', 'sub', 'admin'): return 'Solo administradores.', 403
    con = conectar(); cur = con.cursor(); msg = ''
    try:
        cur.execute('SELECT id, fecha, usuario, version FROM camas_respaldo ORDER BY id DESC LIMIT 100'); filas = cur.fetchall()
    except Exception:
        con.rollback() if PG else None; filas = []
    if request.method == 'POST':
        rid = int(request.form.get('id', 0))
        cur.execute(q('SELECT data FROM camas_respaldo WHERE id=?'), (rid,)); d = cur.fetchone()
        r = _camas_fila(cur)
        if d and r:
            cur.execute(q('INSERT INTO camas_respaldo(fecha, usuario, version, data) VALUES(?,?,?,?)'), (ahora(), 'antes de restaurar', r[0], r[1]))
            cur.execute(q('UPDATE camas_estado SET version=?, data=?, actualizado=?, usuario=? WHERE id=1'), (r[0] + 1, d[0], ahora(), session['usuario'] + ' (restauró respaldo)'))
            con.commit(); msg = 'Respaldo restaurado. Recargá el Comando de Camas.'
    con.close()
    filas_html = ''.join(f'<tr><td>{f[1]}</td><td>{_esc(f[2] or "")}</td><td>v{f[3]}</td><td><form method="post" onsubmit="return confirm(\'¿Restaurar este respaldo? El estado actual queda guardado como respaldo.\')"><input type="hidden" name="id" value="{f[0]}"><button>Restaurar</button></form></td></tr>' for f in filas)
    return Response('<!doctype html><html lang="es"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Respaldos - Comando de Camas</title><style>body{font-family:Arial,sans-serif;margin:16px;color:#1b2a28}table{border-collapse:collapse;width:100%}td,th{border-bottom:1px solid #ddd;padding:8px;text-align:left}button{padding:6px 12px;border-radius:8px;border:1px solid #1d4a42;background:#fff;color:#1d4a42;font-weight:700}.m{background:#e5efeb;padding:10px;border-radius:8px;margin:10px 0}</style></head><body><a href="/camas">← Volver al Comando de Camas</a><h2>Respaldos automáticos del Comando de Camas</h2><p>Se guarda una copia cada 30 minutos de uso (últimas 100).</p>' + (f'<div class="m">{msg}</div>' if msg else '') + '<table><tr><th>Fecha</th><th>Guardado por</th><th>Versión</th><th></th></tr>' + (filas_html or '<tr><td colspan=4>Todavía no hay respaldos.</td></tr>') + '</table></body></html>', mimetype='text/html')

CAMAS_HTML = r'''<!DOCTYPE html>
<html lang="es">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<title>Comando de Camas - HEQI</title><link rel="icon" type="image/png" href="/icon/fav-48.png"><link rel="apple-touch-icon" href="/apple-touch-icon.png"><link rel="manifest" href="/manifest.webmanifest"><meta name="theme-color" content="#1d4a42"><meta name="apple-mobile-web-app-capable" content="yes"><meta name="mobile-web-app-capable" content="yes"><meta name="apple-mobile-web-app-title" content="HEQI">
<script src="https://cdnjs.cloudflare.com/ajax/libs/xlsx/0.18.5/xlsx.full.min.js"></script>
<link href="https://fonts.googleapis.com/css2?family=Source+Sans+3:wght@400;600;700&display=swap" rel="stylesheet">
<style>
:root{
  --bg:#f3f6f5;--surface:#fff;--ink:#1d2b28;--muted:#5d6e6a;--line:#d6e0dd;--ips:#1f6f5c;--ips-soft:#e3efeb;
  --ok:#2f8a5b;--ok-bg:#e4f3ea;--warn:#a86a12;--warn-bg:#fbf0dc;--bad:#b23a3a;--bad-bg:#f8e3e3;--off:#eceff0;
  --t-rojo:#c62828;--t-naranja:#e8650c;--t-amarillo:#e0a800;--t-verde:#2e7d32;--t-azul:#1565c0;
  color-scheme:light;
}
@media (prefers-color-scheme:dark){:root:not([data-theme="light"]){
  --bg:#121a18;--surface:#1a2522;--ink:#e3ece9;--muted:#9fb1ac;--line:#2d3c38;--ips:#4fb393;--ips-soft:#1f332d;
  --ok:#5cc48c;--ok-bg:#183128;--warn:#e0a84a;--warn-bg:#352a17;--bad:#ef7a7a;--bad-bg:#3a1f1f;--off:#1e2826;color-scheme:dark;}}
*{box-sizing:border-box}html,body{margin:0}
body{background:var(--bg);color:var(--ink);font:16px/1.45 "Source Sans 3",system-ui,-apple-system,"Segoe UI",Arial,sans-serif;padding-bottom:env(safe-area-inset-bottom,0)}
header{background:var(--ips);color:#fff;padding:calc(12px + env(safe-area-inset-top,0)) 16px 12px}
header h1{margin:0;font-size:1.2rem}header p{margin:2px 0 0;font-size:.88rem;opacity:.85}
nav{display:flex;gap:2px;padding:0 10px;background:var(--surface);border-bottom:1px solid var(--line);overflow-x:auto;position:sticky;top:0;z-index:5}
nav button{border:0;background:none;color:var(--muted);font:inherit;font-weight:600;padding:12px 11px;border-bottom:3px solid transparent;cursor:pointer;white-space:nowrap}
nav button[aria-selected="true"]{color:var(--ips);border-color:var(--ips)}
main{max-width:1200px;margin:0 auto;padding:14px}
.panel{display:none}.panel.on{display:block}
.box{background:var(--surface);border:1px solid var(--line);border-radius:10px;padding:14px;margin-bottom:14px}
h2{font-size:1.1rem;margin:0}h3{font-size:1rem;margin:14px 0 8px}
.note{font-size:.85rem;color:var(--muted)}
label{display:block;font-size:.85rem;color:var(--muted);margin:8px 0 3px;font-weight:600}
input,select,textarea{width:100%;font:inherit;padding:7px 9px;border:1px solid var(--line);border-radius:7px;background:var(--surface);color:var(--ink)}
textarea{min-height:58px;resize:vertical}
.row{display:flex;gap:10px;flex-wrap:wrap;align-items:end}.row>*{flex:1 1 140px}
button.b{font:inherit;font-weight:600;border:1px solid var(--ips);background:var(--ips);color:#fff;border-radius:7px;padding:7px 13px;cursor:pointer}
button.g{background:transparent;color:var(--ips)}button.s{padding:3px 9px;font-size:.85rem}
button.r{border-color:var(--bad);color:var(--bad);background:transparent}
button:focus-visible,input:focus-visible,select:focus-visible,textarea:focus-visible{outline:3px solid var(--warn);outline-offset:1px}
.sec-head{display:flex;justify-content:space-between;align-items:baseline;gap:10px;flex-wrap:wrap;margin-bottom:10px}
.occ{font-weight:700;font-size:.95rem}.occ.full{color:var(--bad)}.occ.warn{color:var(--warn)}
.beds{display:grid;grid-template-columns:repeat(auto-fill,minmax(190px,1fr));gap:8px}
.bed{border:1px solid var(--line);border-left:7px solid var(--off);border-radius:8px;padding:8px 9px;background:var(--surface);text-align:left;font:inherit;color:inherit;cursor:pointer;min-height:96px;display:flex;flex-direction:column;gap:3px}
.bed.free{border-style:dashed;border-left-width:1px;color:var(--muted);justify-content:center;align-items:center;background:transparent}
.bed .top{display:flex;justify-content:space-between;gap:6px;font-size:.8rem;color:var(--muted);font-weight:600}
.bed .nm{font-weight:700;line-height:1.2}.bed .dx{font-size:.85rem;color:var(--muted);line-height:1.25}
.chips{display:flex;flex-wrap:wrap;gap:4px;margin-top:2px}
.chip{font-size:.75rem;font-weight:700;padding:1px 7px;border-radius:9px;background:var(--off);color:var(--muted);white-space:nowrap}
.chip.w{background:var(--warn-bg);color:var(--warn)}.chip.bd{background:var(--bad-bg);color:var(--bad)}.chip.ok{background:var(--ok-bg);color:var(--ok)}.chip.i{background:var(--ips-soft);color:var(--ips)}
.news{font-size:.75rem;font-weight:700;padding:0 6px;border-radius:9px}
.n-b{background:var(--ok-bg);color:var(--ok)}.n-m{background:var(--warn-bg);color:var(--warn)}.n-a{background:var(--bad-bg);color:var(--bad)}
.t-rojo{border-left-color:var(--t-rojo)}.t-naranja{border-left-color:var(--t-naranja)}.t-amarillo{border-left-color:var(--t-amarillo)}.t-verde{border-left-color:var(--t-verde)}.t-azul{border-left-color:var(--t-azul)}
.dot{display:inline-block;width:10px;height:10px;border-radius:50%;margin-right:5px;vertical-align:0}
.prov{font-size:.72rem;font-weight:700;color:var(--warn)}
/* modal */
.ov{position:fixed;inset:0;background:rgba(0,0,0,.45);display:none;z-index:20;padding:20px 10px;overflow-y:auto}
.ov.on{display:block}
.md{background:var(--surface);max-width:860px;margin:0 auto;border-radius:12px;padding:16px;padding-top:calc(16px + env(safe-area-inset-top,0))}
.md-h{display:flex;justify-content:space-between;align-items:flex-start;gap:10px;border-bottom:1px solid var(--line);padding-bottom:10px;margin-bottom:6px}
details{border:1px solid var(--line);border-radius:8px;margin:8px 0;padding:0 12px}
summary{cursor:pointer;font-weight:700;padding:10px 0}
details[open] summary{border-bottom:1px solid var(--line);margin-bottom:8px}
.score{font-size:1.6rem;font-weight:700;line-height:1}
.items{list-style:none;margin:0;padding:0}
.items li{display:flex;justify-content:space-between;align-items:center;gap:8px;flex-wrap:wrap;padding:7px 0;border-bottom:1px solid var(--line);font-size:.93rem}
.items li:last-child{border-bottom:0}
.acts{display:flex;gap:4px;flex-wrap:wrap;align-items:center}
.acts input[type=date]{width:auto;padding:3px 6px;font-size:.85rem}
.check{display:flex;gap:8px;align-items:flex-start;margin:6px 0;font-size:.93rem;color:var(--ink);font-weight:400}
.check input{width:auto;margin-top:4px}
.sug{border-radius:8px;padding:9px 11px;margin:8px 0;font-weight:600;font-size:.93rem}
.sug.b{background:var(--ok-bg);color:var(--ok)}.sug.m{background:var(--warn-bg);color:var(--warn)}.sug.a{background:var(--bad-bg);color:var(--bad)}
pre.res{white-space:pre-wrap;background:var(--bg);border:1px solid var(--line);border-radius:8px;padding:10px;font:inherit;font-size:.92rem;margin:8px 0}
.msg{border-radius:8px;padding:9px 11px;margin-top:8px;font-size:.93rem;display:none}.msg.on{display:block}
.msg.err{background:var(--bad-bg);color:var(--bad)}.msg.ok{background:var(--ok-bg);color:var(--ok)}
.kpis{display:grid;grid-template-columns:repeat(auto-fit,minmax(150px,1fr));gap:10px;margin-bottom:14px}
.kpi{background:var(--surface);border:1px solid var(--line);border-radius:10px;padding:12px}.kpi b{display:block;font-size:1.6rem;line-height:1.1}.kpi span{font-size:.86rem;color:var(--muted)}
.hb{display:grid;grid-template-columns:170px 1fr 60px;gap:8px;align-items:center;margin:6px 0;font-size:.92rem}
.hb .bar{background:var(--line);height:14px;border-radius:6px;overflow:hidden}.hb .bar i{display:block;height:100%;background:var(--ips)}
.hb b{text-align:right}
.tbl{overflow-x:auto}table{border-collapse:collapse;width:100%;font-size:.92rem}
th,td{padding:7px 8px;border-bottom:1px solid var(--line);text-align:left;vertical-align:top}th{color:var(--muted);font-size:.85rem}
.tri{display:flex;gap:6px;flex-wrap:wrap}.tri label{margin:0;display:flex;align-items:center;gap:4px;color:var(--ink);font-weight:600;border:1px solid var(--line);border-radius:7px;padding:5px 9px;cursor:pointer}
.tri input{width:auto}
.crit{list-style:none;margin:6px 0;padding:0}.crit li{padding:4px 0;font-size:.93rem;display:flex;gap:7px}
.crit .y{color:var(--ok);font-weight:700}.crit .n{color:var(--bad);font-weight:700}.crit .q{color:var(--warn);font-weight:700}
.alr{border-left:5px solid var(--bad);background:var(--bad-bg);color:var(--ink);border-radius:8px;padding:10px 12px;margin-bottom:14px}.alr h2{color:var(--bad);margin-bottom:6px}.alr ul{margin:0;padding-left:18px}.alr li{margin:3px 0}
.pz{display:grid;grid-template-columns:repeat(auto-fill,minmax(118px,1fr));gap:8px}
.tile{--pc:var(--ink);min-height:96px;border:2px solid var(--pc);border-radius:9px;padding:9px;display:flex;cursor:pointer;font:inherit;color:var(--ink);background-color:var(--surface)}
.tile .lb{background:var(--surface);border-radius:5px;padding:5px 6px;margin:auto;text-align:center;font-size:.78rem;line-height:1.25;width:100%;font-weight:600}
.tile .lb b{font-size:.86rem}.tile .det{font-weight:400;color:var(--muted)}
.pz-libre{--pc:var(--ok)}
.pz-ocu{--pc:#7d8a87;background-color:#bfc7c5}
.pz-res{--pc:#2f6fb3;background-image:radial-gradient(var(--pc) 1.4px,transparent 1.7px);background-size:8px 8px}
.pz-alta{--pc:var(--ok);background-image:repeating-linear-gradient(45deg,var(--pc) 0 1.5px,transparent 1.5px 9px)}
.pz-sucia{--pc:var(--warn);background-image:repeating-linear-gradient(45deg,var(--pc) 0 1.5px,transparent 1.5px 9px),repeating-linear-gradient(-45deg,var(--pc) 0 1.5px,transparent 1.5px 9px)}
.pz-limp{--pc:var(--warn);background-image:repeating-linear-gradient(-45deg,var(--pc) 0 1.5px,transparent 1.5px 9px)}
.pz-bloq{--pc:var(--ink);background-image:linear-gradient(var(--pc) 1px,transparent 1px),linear-gradient(90deg,var(--pc) 1px,transparent 1px);background-size:8px 8px}
.pz-cont{--pc:var(--bad);background-image:radial-gradient(circle,transparent 2px,var(--pc) 2.4px 3.1px,transparent 3.5px);background-size:10px 10px}
.prov-t{border-style:dashed}
.pz-leg{display:flex;flex-wrap:wrap;gap:12px;font-size:.85rem;margin-bottom:6px}.pz-leg span{display:flex;align-items:center;gap:5px}
.sw{display:inline-block;width:20px;height:16px;border:2px solid var(--pc);border-radius:3px;background-color:var(--surface)}
.sw.pz-ocu{background-color:#bfc7c5}
@media (prefers-color-scheme:dark){:root:not([data-theme="light"]) .pz-ocu,:root:not([data-theme="light"]) .sw.pz-ocu{background-color:#56625f}}
fieldset{border:1px solid var(--line);border-radius:8px;margin:10px 0;padding:6px 10px}legend{font-weight:700;font-size:.92rem;padding:0 4px}
@media (max-width:640px){.hb{grid-template-columns:110px 1fr 46px}.ov{padding:0}.md{border-radius:0;min-height:100%}}
</style>
</head>
<body>
<header>
  <h1><img src="/icon/logo-mark.png" alt="HEQI" style="height:42px;background:#fff;border-radius:8px;padding:3px 5px;vertical-align:middle;margin-right:10px">Comando de Camas</h1>
  <p><a href="/" style="color:inherit;font-weight:700">← Volver al panel</a> · <a href="#" id="pase-top" style="color:inherit;font-weight:700">📋 Pase de guardia</a> · <a href="/camas/respaldos" style="color:inherit;font-weight:700">🗂 Respaldos</a> · Sesión: __USUARIO__ · <span id="sync-st">Conectando…</span></p>
</header>
<nav role="tablist">
  <button role="tab" aria-selected="true" data-p="piz">Pizarra de camas</button>
  <button role="tab" aria-selected="false" data-p="camas">Pacientes y alertas</button>
  <button role="tab" aria-selected="false" data-p="esp">Esperando cama</button>
  <button role="tab" aria-selected="false" data-p="cons">Consultorio amarillo</button>
  <button role="tab" aria-selected="false" data-p="csl">Consultas del día</button>
  <button role="tab" aria-selected="false" data-p="der">Traslados internos y externos</button>
  <button role="tab" aria-selected="false" data-p="cont">Contingencia</button>
  <button role="tab" aria-selected="false" data-p="ind">Indicadores e informe</button>
</nav>
<main>
  <section class="panel on" id="p-piz">
    <div class="kpis" id="k-piz"></div>
    <div id="pizarra"></div>
    <div class="box"><div class="pz-leg" id="pz-leg"></div><p class="note">Tocá una cama ocupada para abrir la ficha. Tocá una cama vacía para cambiar su estado, reservarla o ingresar un paciente.</p></div>
    <div class="box"><h2 style="margin-top:0">🔧 Camas bloqueadas y reclamos</h2><div id="pz-bloq"></div></div>
    <div class="box"><h2 style="margin-top:0">🔁 Movimientos de camas</h2><div style="margin-bottom:8px"><button class="b g s" id="mov-csv">Descargar registro (Excel / CSV)</button></div><div id="pz-mov"></div></div>
  </section>
  <section class="panel" id="p-esp">
    <div class="kpis" id="k-esp"></div>
    <div class="box"><h2>Pacientes esperando cama</h2><ul class="items" id="esp-body"></ul></div>
    <div class="box"><h2>Agregar a la lista de espera</h2>
      <div class="row"><div><label for="e-nom">Paciente</label><input id="e-nom"></div><div><label for="e-ci">Cédula</label><input id="e-ci" inputmode="numeric"></div><div style="flex:0 1 90px"><label for="e-edad">Edad</label><input id="e-edad" type="number"></div></div>
      <div class="row"><div><label for="e-tri">Triage</label><select id="e-tri"><option>Rojo</option><option>Naranja</option><option selected>Amarillo</option><option>Verde</option><option>Azul</option></select></div><div><label for="e-sec">Necesita cama en</label><select id="e-sec"><option value="rea">Reanimación</option><option value="obs" selected>Polivalente 1</option><option value="ec">Polivalente 2</option></select></div></div>
      <div class="row"><div><label for="e-ori">Origen</label><select id="e-ori"><option>Urgencias HEQI</option><option>Derivado externo</option></select></div><div><label for="e-lug">Lugar (sector o centro que deriva)</label><input id="e-lug" placeholder="Ej. Hospital Regional de Ciudad del Este"></div></div>
      <label for="e-mot">Motivo y diagnóstico</label><input id="e-mot">
      <div style="margin-top:10px"><button class="b" id="esp-ok">Agregar a la espera</button></div><div class="msg" id="esp-msg"></div>
    </div>
  </section>
  <section class="panel" id="p-camas">
    <div class="box" style="display:flex;gap:8px;flex-wrap:wrap;align-items:center"><b>📋 Informe de pase de guardia</b><button class="b s" id="pase-print">Imprimir / PDF</button><button class="b g s" id="pase-word">Descargar Word</button></div>
    <div class="kpis" id="k-camas"></div>
    <div id="alertas"></div>
    <div id="sectores"></div>
  </section>

  <section class="panel" id="p-cons">
    <div class="box">
      <h2>Consultorio de códigos amarillos</h2>
      <p class="note">Funciona dentro de la Sala de trabajo clínico. Con el NEWS2 se orienta quién se va con tratamiento ambulatorio y quién se queda.</p>
      <div class="row">
        <div><label for="c-nom">Paciente</label><input id="c-nom" placeholder="Apellido y nombre"></div>
        <div><label for="c-ci">Cédula</label><input id="c-ci" inputmode="numeric"></div>
        <div style="flex:0 1 90px"><label for="c-edad">Edad</label><input id="c-edad" type="number" min="0"></div>
      </div>
      <label for="c-mot">Motivo de consulta</label><input id="c-mot">
      <h3>Signos vitales para NEWS2</h3>
      <div class="row" id="c-vit"></div>
      <div id="c-news"></div>
      <label for="c-plan">Plan</label><textarea id="c-plan"></textarea>
      <div class="row" style="margin-top:10px">
        <div style="flex:0 0 auto"><button class="b g" data-c="alta">Alta - tratamiento ambulatorio</button></div>
        <div style="flex:0 0 auto"><button class="b g" data-c="obs">Observar en sala de trabajo</button></div>
        <div style="flex:0 0 auto"><button class="b" data-c="int">Internar</button></div>
      </div>
      <div class="row" id="c-introw" style="display:none">
        <div><label for="c-sec">Internar en</label><select id="c-sec"><option value="obs">Polivalente 1</option><option value="ec">Polivalente 2</option></select></div>
        <div style="flex:0 0 auto"><button class="b" id="c-intok">Confirmar internación</button></div>
      </div>
      <div class="msg" id="c-msg" role="status"></div>
    </div>
    <div class="box">
      <h2>Consultas de hoy</h2>
      <div class="tbl"><table><thead><tr><th>Hora</th><th>Paciente</th><th>Motivo</th><th>NEWS2</th><th>Decisión</th></tr></thead><tbody id="c-body"></tbody></table></div>
    </div>
  </section>

  <section class="panel" id="p-csl">
    <div class="box"><h2>Consultas del día</h2><p class="note">Cargá el listado exportado del SIH (o de otro sistema) en CSV o Excel, en cualquier momento. Tiene que traer, como mínimo, las columnas Edad y Prioridad (color); si trae Fecha y Especialidad, también se analizan.</p>
      <div class="row"><div><label for="cs-file">Archivo</label><input id="cs-file" type="file" accept=".csv,.xlsx,.xls,.txt"></div></div>
      <div class="acts" style="margin-top:8px"><button class="b g s" id="cs-demo">Cargar datos de ejemplo</button><button class="b r s" id="cs-clear">Borrar consultas cargadas</button></div><div class="msg" id="cs-msg"></div></div>
    <div class="box" id="cs-out"></div>
  </section>
  <section class="panel" id="p-cont">
    <div class="box"><h2>Tablero de contingencia</h2><p class="note">Para desastres, catástrofes o múltiples víctimas: muestra con cuántas camas y camillas se cuenta ahora, según el estado real de la Urgencia.</p></div>
    <div class="kpis" id="ct-k"></div>
    <div class="box"><div class="sec-head"><h2>Simulación de múltiples víctimas</h2><button class="b g s" id="ct-reset">Reiniciar</button></div><div class="kpis" id="ct-vic" style="margin-top:8px"></div><div id="ct-res"></div></div>
    <div class="box"><h2>Recursos de reserva</h2><ul class="items" id="ct-rec"></ul>
      <div class="row"><div><label for="ct-n">Agregar recurso</label><input id="ct-n" placeholder="Ej. Colchonetas"></div><div style="flex:0 1 100px"><label for="ct-c">Cantidad</label><input id="ct-c" type="number" min="0"></div><div style="flex:0 0 auto"><button class="b" id="ct-add">Agregar</button></div></div></div>
  </section>
  <section class="panel" id="p-der">
    <div class="box">
      <h2>Resúmenes para traslados internos y externos</h2>
      <p class="note">Se arma solo con el destino propuesto en cada ficha. Copiá el bloque de cada servicio y envialo a su referente para consultar disponibilidad de cama.</p>
      <div class="row"><div><label for="d-serv">Servicio</label><select id="d-serv"></select></div></div>
    </div>
    <div id="d-out"></div>
  </section>

  <section class="panel" id="p-ind">
    <div class="box"><div class="sec-head"><h2>Informe final para jefatura</h2><div class="acts"><button class="b s" id="if-word">Descargar en Word</button><button class="b g s" id="if-print">Imprimir</button></div></div><p class="note">Reúne gestión de camas (ocupación, giro, estadía media, intervalo de sustitución), censo diario, destinos, espera de cama, calidad, caracterización de las consultas cargadas y capacidad de contingencia.</p></div>
    <div class="box"><div class="sec-head"><h2>Censo diario</h2><button class="b g s" id="cen-save">Guardar censo de hoy</button></div><p class="note">Cada día queda una foto de la Urgencia: pacientes por sector, esperando cama y consultas. En la aplicación real se guarda sola al cierre de guardia.</p>
      <div id="cen-bar"></div><div class="tbl"><table><thead><tr><th>Fecha</th><th>REA</th><th>CR</th><th>PV1</th><th>PV2</th><th>STC</th><th>Total</th><th>Esperando</th><th>Consultas</th></tr></thead><tbody id="cen-body"></tbody></table></div></div>
    <div class="box"><div class="sec-head"><h2>Informe general</h2><div class="acts"><select id="inf-p" style="width:auto"><option value="7">Últimos 7 días</option><option value="30" selected>Últimos 30 días</option></select><button class="b g s" id="inf-print">Imprimir informe</button><button class="b s" id="inf-csv">Descargar registro (Excel)</button></div></div>
      <h3>Ocupación, estadía media y giro de cama</h3><div class="tbl"><table><thead><tr><th>Sector</th><th>Camas</th><th>Ocupación</th><th>Estadía media</th><th>Giro</th><th>Egresos</th><th>Óbitos</th></tr></thead><tbody id="inf-sec"></tbody></table></div>
      <p class="note">Ocupación mayor a 100% significa que hubo más pacientes que camas fijas (sofás y camillas provisorias).</p>
      <h3>Lugares de externación</h3><div class="tbl"><table><thead><tr><th>Destino</th><th>Pacientes</th><th>%</th></tr></thead><tbody id="inf-dest"></tbody></table></div>
      <h3>Registro de movilización</h3><p class="note" id="inf-n"></p><div class="tbl"><table><thead><tr><th>Egreso</th><th>Paciente</th><th>Sector</th><th>Ingreso</th><th>Estadía</th><th>Destino</th><th>Diagnóstico</th></tr></thead><tbody id="inf-reg"></tbody></table></div>
    </div>
    <div class="kpis" id="k-ind"></div>
    <div class="box"><h2>Ocupación por sector</h2><div id="i-occ"></div><p class="note">Las camillas provisorias y sofás se suman aparte de las camas fijas.</p></div>
    <div class="box"><h2>Gravedad actual (NEWS2)</h2><div id="i-grav"></div><p class="note" id="i-sofa"></p><p class="note">SOFA-2 (JAMA 2025). El componente respiratorio usa SpO2/FiO2 convertido a PaO2/FiO2 con la ecuación de Ellis-Severinghaus.</p></div>
    <div class="box"><h2>Egresos de los últimos 30 días por destino</h2><div id="i-egr"></div></div>
    <div class="box"><h2>Giro de cama y estadía media (30 días)</h2><div class="tbl"><table><thead><tr><th>Sector</th><th>Egresos</th><th>Giro de cama</th><th>Estadía media</th></tr></thead><tbody id="i-giro"></tbody></table></div></div>
    <div class="box"><h2>Condición al egreso (registrados hoy)</h2><div class="tbl"><table><thead><tr><th>Paciente</th><th>Desde</th><th>Egreso</th><th>Condición</th><th>Criterios</th></tr></thead><tbody id="i-cond"></tbody></table></div></div>
  </section>
</main>

<div class="ov" id="ov" role="dialog" aria-modal="true"><div class="md" id="md"></div></div>

<script>
let NOW=new Date();const H=36e5,D=864e5;
const SEC=[
 {id:'rea',n:'Reanimación',sub:'Cuidados críticos de Urgencias: AVM, hemodiálisis, vasoactivos',fijas:8,extra:0,pref:'REA'},
 {id:'cr',n:'Código rojo',sub:'Espacio virtual para los pacientes graves que llegan. No se oferta ni se reserva',fijas:0,extra:20,pref:'CR',virtual:true},
 {id:'obs',n:'Polivalente 1',sub:'Internados de mayor estadía',fijas:10,extra:0,pref:'PV1'},
 {id:'ec',n:'Polivalente 2',sub:'Internados de resolución rápida',fijas:5,extra:0,pref:'PV2'},
 {id:'stc',n:'Sala de trabajo clínico',sub:'Amarillos para reevaluar o internar. No se niega lugar',fijas:5,extra:20,pref:'STC'}];
const SECN=Object.fromEntries(SEC.map(s=>[s.id,s]));
const TRI=['Rojo','Naranja','Amarillo','Verde','Azul'];
const TRIC={Rojo:'var(--t-rojo)',Naranja:'var(--t-naranja)',Amarillo:'var(--t-amarillo)',Verde:'var(--t-verde)',Azul:'var(--t-azul)'};
const SERV=['Clínica Médica','Cirugía General','Urología','Traumatología','Neurocirugía','Mastología','Coloproctología'];
const DEST=['Queda en Urgencias',...SERV,'UTI','Terciarizado externo','Sanatorio Español','Otra red IPS','Externar a sala de menor complejidad','Alta'];
const EGR=['Traslado a sala HEQI','UTI HEQI','Otra red IPS','Terciarizado','Externado a sala de menor complejidad','Alta','Óbito'];
const RED=['Geriátrico IPS','Hospital Central IPS','Hospital 12 de Junio','DHAI (Hospitales de Área del Interior)'];
const TERCS=['Sanatorio Español','Otro sanatorio (especificar)'];
const GERM=['Ninguno','BLEE','SAMR','Acinetobacter multirresistente','Pseudomonas multirresistente','Clostridioides difficile','Otro'];
const GRADOS=['I','II','III','IV','No estadificable'];
const TIPOS=['Imagen (MEPROTEC)','Laboratorio externo','Anatomía patológica','Laboratorio especial','Procedimiento diagnóstico'];
const EXT=['Laboratorio externo','Anatomía patológica'];
const ACT=['Pendiente de programación','Programado','Suspendido','Pendiente de envío','Enviado'];
const BEDST=['Libre','Reservada','Sucia','En limpieza','Bloqueada','Contaminada'];
let bedSt={},espera=[];let SEMBRANDO=true,movs=[],_nc=0;const nid=()=>Date.now()*100+((_nc++)%100);const USUARIO='__USUARIO__';
const DEV=[['aire','Aire ambiente'],['cn','Cánula nasal'],['ms','Mascarilla simple'],['mr','Mascarilla con reservorio'],['vtr','Venturi'],['cnaf','Cánula nasal de alto flujo'],['vni','VNI'],['vmi','VMI (intubado)']];
const ADV=['cnaf','vni','vmi'];
const TA=['Diagnóstico establecido y plan terapéutico definido, sin incertidumbre diagnóstica','Estabilidad clínica de 48 h o más: sin vasoactivos ni inotrópicos, sin VNI ni VMI, sin oxígeno, sin deterioro de conciencia','Internación restante estimada menor a 10 días','Sin estudios complejos pendientes (TC, RM, angiografía, ecocardiograma transesofágico, endoscopía, hemodinamia)','No requiere cirugía ni procedimientos invasivos previstos','Sin interconsultas complejas (cardiocirugía, cardiología intervencionista, neurocirugía, especialidades quirúrgicas)','Si recibe antibiótico: esquema definido, buena respuesta y duración total de 10 días o menos','Seguimiento resoluble con laboratorio básico y control clínico diario','Paciente y familia informados y de acuerdo con el traslado'];
const TB=['Insuficiencia cardíaca en descomplejización','ACV isquémico establecido (más de 72 h, 2 TC de control estables)','Infección con foco controlado (NAC, ITU sin obstrucción, celulitis sin colección)','EPOC o asma en descenso','Descompensación metabólica resuelta','Otros'];
const TC=['Inestabilidad hemodinámica, respiratoria o neurológica en las últimas 48 h','Antibiótico previsto mayor a 10 días (endocarditis, osteomielitis, absceso no drenado, bacteriemia por S. aureus, infección protésica)','Sangrado activo o hemorragia digestiva con indicación de nueva endoscopía','Necesidad de hemodiálisis, nutrición parenteral, transfusión o vía central','Estudio complejo, procedimiento o valoración quirúrgica pendiente'];
const TD=['Cura avanzada: escaras o lesiones de piel sin debridamiento ni cirugía, internación restante menor a 10 días','Cateterismo programado: SCA sin elevación del ST, estable, cateterismo no urgente'];
const COMPLEJO=/\b(tac|tc|tomograf|rm|resonan|angio|endoscop|eda|colonoscop|ecocardiograma transes|ete|hemodinam|cateterismo|colangio)/i;
const AYUNO_RX=/angio|contraste|uro-?tac|colangio|cpre|endoscop|\beda\b|colonoscop|ecograf[ií]a (abdominal|hep|vesic)/i;
const AYUNO={test:n=>AYUNO_RX.test(n)&&!/sin contraste/i.test(n)};
const CONTRASTE=n=>/angio|contraste|uro-?tac/i.test(n)&&!/sin contraste/i.test(n);
const $=id=>document.getElementById(id);
const esc=s=>String(s??'').replace(/[&<>"]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
const two=n=>String(n).padStart(2,'0');
const fdate=d=>two(d.getDate())+'/'+two(d.getMonth()+1)+'/'+d.getFullYear();
const fdt=d=>fdate(d)+' '+two(d.getHours())+':'+two(d.getMinutes());
const dur=ms=>{const h=Math.max(0,Math.round(ms/H));return h<24?h+' h':Math.floor(h/24)+' d '+(h%24)+' h'};
const iso=d=>d.getFullYear()+'-'+two(d.getMonth()+1)+'-'+two(d.getDate());const dtl=d=>iso(d)+'T'+two(d.getHours())+':'+two(d.getMinutes());
const fi=s=>s?s.split('-').reverse().join('/'):'';
let HOY=iso(NOW);
const edadDe=f=>{if(!f)return '';const b=new Date(f+'T00:00');let a=NOW.getFullYear()-b.getFullYear();if(NOW.getMonth()<b.getMonth()||(NOW.getMonth()===b.getMonth()&&NOW.getDate()<b.getDate()))a--;return a};
const at=(f,h)=>new Date(f+'T'+(h||'00:00'));

/* NEWS2 */
function news2(v){
  if(!v)return null;if(['fr','sat','pas','fc','temp'].some(k=>v[k]===''||v[k]==null))return null;
  const fr=+v.fr,sat=+v.sat,pas=+v.pas,fc=+v.fc,t=+v.temp,p=[];
  p.push(fr<=8?3:fr<=11?1:fr<=20?0:fr<=24?2:3);p.push(sat<=91?3:sat<=93?2:sat<=95?1:0);p.push(v.o2?2:0);
  p.push(pas<=90?3:pas<=100?2:pas<=110?1:pas<=219?0:3);p.push(fc<=40?3:fc<=50?1:fc<=90?0:fc<=110?1:fc<=130?2:3);
  p.push(v.conc&&v.conc!=='A'?3:0);p.push(t<=35?3:t<=36?1:t<=38?0:t<=39?1:2);
  const s=p.reduce((a,b)=>a+b,0),any3=p.some(x=>x===3);
  return {s,r:s>=7?'a':s>=5||any3?'m':'b',txt:s>=7?'riesgo alto':s>=5?'riesgo medio':any3?'riesgo bajo-medio (un parámetro en 3)':'riesgo bajo'};
}
/* FiO2 según dispositivo y litros */
function fio2(r){const L=+r.L||0;
  if(r.dev==='aire')return 21;
  if(r.dev==='cn')return L?Math.min(44,21+4*Math.min(L,6)):null;
  if(r.dev==='ms')return L?(L<5?35:Math.min(60,40+(Math.floor(L)-5)*10)):null;
  if(r.dev==='mr')return L?(L<6?60:Math.min(90,60+(Math.floor(L)-6)*10)):null;
  return r.fio2!==''&&r.fio2!=null?+r.fio2:null}
/* PaO2 estimada desde SpO2 (Ellis-Severinghaus) */
function pao2Sat(sat){const s=Math.min(sat,97)/100;const a=11700/(1/s-1),b=Math.sqrt(Math.pow(50,3)+a*a);return Math.cbrt(b+a)-Math.cbrt(b-a)}
function resp(p){const sat=p.vit.sat,f=fio2(p.resp);if(sat===''||sat==null||!f)return null;
  const pao2=pao2Sat(+sat),pafi=pao2/(f/100),safi=(+sat)/(f/100),adv=ADV.includes(p.resp.dev);
  let sc=pafi>300?0:pafi>225?1:pafi>150?2:pafi>75?3:4;if(!adv&&sc>2)sc=2;if(p.resp.dev==='ecmo')sc=4;
  return {f,pao2,pafi,safi,sc,adv,flag:+sat>=97}}
/* SOFA-2 */
function sofa(p){const x=p.sof;let s=0,n=0;const v=k=>x[k]===''||x[k]==null?null:+x[k];
  const r=resp(p);if(r){n++;s+=r.sc}
  const g=v('gcs');if(g!=null||x.delir){n++;s+=g==null?1:g<=5?4:g<=8?3:g<=12?2:(g<=14||x.delir)?1:0}
  const pam=v('pam'),dv=v('vaso')||0;if(pam!=null||dv||x.otro||x.mec){n++;s+=x.mec||dv>0.4?4:dv>0.2||(dv>0&&x.otro)?3:dv>0||x.otro?2:pam!=null&&pam<70?1:0}
  const bi=v('bili');if(bi!=null){n++;s+=bi>12?4:bi>6?3:bi>3?2:bi>1.2?1:0}
  const cr=v('cr');if(cr!=null||x.diur||x.dial){n++;let k=0;if(cr!=null)k=cr>3.5?3:cr>2?2:cr>1.2?1:0;k=Math.max(k,{'':0,d1:1,d2:2,d3:3}[x.diur||'']);if(x.dial)k=4;s+=k}
  const pl=v('plaq');if(pl!=null){n++;s+=pl<=50?4:pl<=80?3:pl<=100?2:pl<=150?1:0}
  return n?{s,n,r}:null}
const vaso=p=>(+p.sof.vaso>0)||p.sof.otro||p.sof.mec;
const vent=p=>['vni','vmi'].includes(p.resp.dev);
/* Alta a sala desde Reanimación */
function altaSala(p){
  const it=[],g=p.gas,r=news2(p.vit),so=sofa(p),A=p.alt,dev=p.resp.dev,L=+p.resp.L||0;
  if(g.ph===''||g.hco3===''||g.pco2==='')it.push(['n','Gasometría incompleta: pH, PaCO2 y bicarbonato son obligatorios en Reanimación']);
  else{const ok=+g.ph>7.30&&+g.hco3>15;it.push([ok?'y':'n',`pH ${g.ph} y bicarbonato ${g.hco3} ${ok?'(pH mayor a 7,30 y HCO3 mayor a 15)':'(se requiere pH mayor a 7,30 y HCO3 mayor a 15)'}`])}
  it.push(r?[r.s<5?'y':'n',`NEWS2 ${r.s} ${r.s<5?'(menor a 5)':'(5 o más)'}`]:['n','NEWS2 sin calcular']);
  if(so&&p.sofaPrev!==''){const d=so.s-(+p.sofaPrev);it.push([d<0?'y':d===0?'q':'n',`Delta SOFA-2 ${d>0?'+':''}${d} (de ${p.sofaPrev} a ${so.s}): ${d<0?'en mejoría':d===0?'estable, vigilar':'en empeoramiento'}`])}
  else it.push(['n','Delta SOFA-2 sin calcular: cargá el SOFA-2 actual y el de hace 24 h']);
  const bajo=dev==='aire'||(['cn','ms'].includes(dev)&&L>0&&L<5);
  it.push([bajo?'y':'n',bajo?(dev==='aire'?'Aire ambiente':`Oxígeno de bajo flujo, ${L} L/min (menor a 5)`):'Soporte de oxígeno no es de bajo flujo menor a 5 L/min (o falta cargar los litros)']);
  if(dev!=='aire')it.push([A.o2Desc?'y':'n',A.o2Desc?'Oxígeno en plan de descenso':'Oxígeno sin plan de descenso']);
  it.push(A.hSinVent===''?['n','Falta cargar las horas sin VMI, VNI ni alto flujo']:[+A.hSinVent>=48?'y':'n',`${A.hSinVent} h sin VMI, VNI ni alto flujo (se requieren 48 h o más)`]);
  if(vaso(p))it.push(['n','Con vasopresores, inotrópicos o soporte mecánico']);
  else it.push(A.hSinVaso===''?['n','Falta cargar las horas sin vasopresores']:[+A.hSinVaso>=24?'y':'n',`${A.hSinVaso} h sin vasopresores (se requieren 24 h o más)`]);
  if(A.postqx)it.push(A.hReanim===''?['n','Postquirúrgico de alta complejidad: falta cargar las horas de reanimado y estable']:[+A.hReanim>=12?'y':'n',`Postquirúrgico de alta complejidad o cirugía prolongada: ${A.hReanim} h reanimado y estable (se requieren 12 h o más)`]);
  return {it,ok:it.every(x=>x[0]!=='n')}}
/* Tercerización */
function tercer(p){
  const t=p.terc,auto=[],pendQx=p.qx.some(q=>!['Realizado','Sin efecto'].includes(q.estado));
  const pendComp=p.est.filter(e=>ACT.includes(e.estado)&&COMPLEJO.test(e.nom));
  if(p.resp.dev!=='aire'||p.vit.o2)auto.push('Tiene oxígeno o soporte respiratorio');if(vent(p))auto.push('Está en VMI o VNI');
  if(vaso(p))auto.push('Recibe vasopresores o inotrópicos');if(p.vit.conc&&p.vit.conc!=='A')auto.push('Deterioro de conciencia');
  if(pendQx)auto.push('Tiene cirugía o procedimiento pendiente');if(pendComp.length)auto.push('Estudio complejo pendiente: '+pendComp.map(e=>e.nom).join(', '));
  if(p.sof.dial)auto.push('Requiere diálisis');const r=news2(p.vit);if(r&&r.s>=5)auto.push('NEWS2 de 5 o más');
  const faltA=TA.filter((_,i)=>!t.a[i]),hayC=TC.filter((_,i)=>t.c[i]),perfil=t.perfil||t.d.some(Boolean);
  const ok=!faltA.length&&!hayC.length&&!auto.length&&perfil;
  return {ok,auto,faltA,hayC,perfil,dest:ok?(t.d.some(Boolean)?'Sanatorio Español':'Terciarizado externo'):''}}
/* Aislamiento */
function aisl(p){const o=p.ais.origen==='Adquirido en Urgencias'?' (adquirido en Urgencias)':' (presente al ingreso)';
  if(p.ais.kpc==='Confirmado')return {k:'a',t:'EPC confirmado'+o+': requiere sala de aislamiento.',chip:['bd','EPC'+(p.ais.origen==='Adquirido en Urgencias'?' adquirido':'')+': sala de aislamiento']};
  if(p.ais.germ==='Clostridioides difficile')return {k:'a',t:'Clostridioides difficile'+o+': requiere sala de aislamiento, no solo contacto.',chip:['bd','C. difficile: sala de aislamiento']};
  if(p.ais.kpc==='Sospecha')return {k:'m',t:'Sospecha de EPC: aislamiento de contacto preventivo hasta el resultado del hisopado.',chip:['w','Sospecha EPC']};
  if(p.ais.germ&&p.ais.germ!=='Ninguno')return {k:'m',t:`${p.ais.germ}${o}: aislamiento de contacto in situ.`,chip:['w','Contacto: '+p.ais.germ]};
  return null}
/* Escaras */
function escara(p){const e=p.esc,ult=e.evol[e.evol.length-1];
  if(!e.ing&&!e.evol.length)return null;
  if(!e.ing){const f=e.evol[0];return {adq:true,t:`Escara adquirida en Urgencias el ${fi(f.fecha)}: ${f.loc||'sin localizar'}, grado ${f.grado}${e.evol.length>1?'. Última evolución: grado '+ult.grado:''}`}}
  const base=`Escara al ingreso: ${e.loc||'sin localizar'}, grado ${e.grado||'s/d'}`;
  if(!e.evol.length)return {adq:false,t:base+'. Sin evolución registrada.'};
  const gi=GRADOS.indexOf(e.grado),gu=GRADOS.indexOf(ult.grado);
  return {adq:false,prog:gu>gi&&gi>=0,t:base+`. Última evolución ${fi(ult.fecha)}: ${ult.loc||e.loc}, grado ${ult.grado}${gu>gi&&gi>=0?' (progresó)':gu<gi?' (mejoró)':''}.`}}
/* Alertas */
function alertas(p){const a=[];const hh=d=>two(d.getHours())+':'+two(d.getMinutes());
  if(!p.dest)a.push(['w','Falta definir el servicio a destinar (obligatorio para el pase de guardia)']);
  if(p.resp&&p.resp.dev==='vmi'){const vm=p.vm||{};if(!vm.corr)a.push(['w','Intubado: cargar fecha y hora del corrugado']);else{const h=(NOW-new Date(vm.corr))/H;if(h>=72)a.push(['bd',`Cambiar corrugado: colocado hace ${Math.floor(h)} h (más de 72 h)`]);else if(h>=60)a.push(['w',`Corrugado: cambio en ${Math.ceil(72-h)} h`])}}
  p.est.filter(e=>ACT.includes(e.estado)).forEach(e=>{const dias=Math.round((NOW-new Date(e.fsol+'T12:00'))/D);
    if(e.estado==='Pendiente de programación')a.push([dias>=1?'bd':'w',`${e.nom}: solicitado ${fi(e.fsol)}, todavía sin programar${dias>=1?' ('+dias+' día'+(dias>1?'s':'')+')':''}`]);
    if(e.estado==='Suspendido')a.push(['bd',`${e.nom}: suspendido${e.smot?' ('+e.smot+')':''}, falta reprogramar`]);
    if(e.estado==='Pendiente de envío')a.push(['bd',`${e.nom}: ${e.tipo.toLowerCase()} pendiente de envío`]);
    if(e.estado==='Enviado'){const de=Math.round((NOW-new Date((e.fenv||e.fsol)+'T12:00'))/D);a.push([de>=2?'bd':'w',`${e.nom}: enviado ${fi(e.fenv||e.fsol)}, esperando resultado${de>=2?' hace '+de+' días':''}`])}
    if(e.estado==='Programado'){
      if(e.tipo==='Imagen (MEPROTEC)'&&!e.hora)a.push(['bd',`${e.nom}: programado ${fi(e.fprog)} sin hora de agendamiento (pedir la hora a MEPROTEC)`]);
      const t=at(e.fprog,e.hora||'23:59'),h=(t-NOW)/H;
      if(h<0)a.push(['bd',`${e.nom}: programado ${fi(e.fprog)}${e.hora?' '+e.hora:''} y no figura como realizado`]);
      else if(h<=24){let x=`${e.nom} programado ${e.fprog===HOY?'hoy':'mañana'}${e.hora?' a las '+e.hora:''}`;
        if(e.ayuno&&e.hora){const ay=new Date(t-6*H);x+=`. Ayuno desde las ${hh(ay)}${ay<=NOW?' (ya en ayuno)':''}`}else if(e.ayuno)x+='. Requiere ayuno de 6 h';
        if(CONTRASTE(e.nom))x+='. Verificar creatinina y alergia al contraste';a.push(['w',x])}
      else a.push(['i',`${e.nom} programado ${fi(e.fprog)}${e.hora?' '+e.hora:''}`])}});
  p.qx.forEach(q=>{if(q.estado==='Pendiente de presentar')a.push(['w',`Cirugía ${q.nom}: pendiente de presentar a ${q.serv}`]);
    if(q.estado==='Presentado')a.push(['w',`Cirugía ${q.nom}: presentada, sin fecha quirúrgica`]);
    if(q.estado==='Suspendido')a.push(['bd',`Cirugía ${q.nom}: suspendida, falta reprogramar`]);
    if(q.estado==='Con fecha'){const t=at(q.fecha,q.hora||'23:59'),h=(t-NOW)/H;
      if(h<0)a.push(['bd',`Cirugía ${q.nom}: fecha ${fi(q.fecha)} vencida, no figura como realizada`]);
      else if(h<=24){let x=`Cirugía ${q.nom} ${q.fecha===HOY?'hoy':'mañana'}${q.hora?' a las '+q.hora:''}`;if(q.hora){const ay=new Date(t-8*H);x+=`. Ayuno desde las ${hh(ay)}${ay<=NOW?' (ya en ayuno)':''}`}else x+='. Falta hora: confirmar con quirófano';a.push(['w',x])}}});
  const es=escara(p);if(es&&es.adq)a.push(['bd','Escara adquirida en Urgencias']);if(es&&es.prog)a.push(['bd','Escara al ingreso que progresó de grado']);
  if(p.ais.origen==='Adquirido en Urgencias'&&(p.ais.kpc!=='No'||p.ais.germ!=='Ninguno'))a.push(['bd','Germen multirresistente adquirido en Urgencias']);
  const so=sofa(p);if(so&&p.sofaPrev!==''&&so.s>+p.sofaPrev)a.push(['bd',`SOFA-2 en empeoramiento (de ${p.sofaPrev} a ${so.s})`]);
  return a}
const newsBadge=p=>{const r=news2(p.vit);return r?`<span class="news n-${r.r}">NEWS2 ${r.s}</span>`:'<span class="news" style="background:var(--off);color:var(--muted)">Sin NEWS2</span>'};
function sugerencia(p){
  if(p.sector==='rea'&&altaSala(p).ok)return {k:'b',t:'Cumple criterios de alta a sala desde Reanimación.'};
  const r=news2(p.vit);if(!r)return {k:'m',t:'Cargá los signos vitales para calcular el NEWS2 y orientar el destino.'};
  const tc=tercer(p);
  if(r.s>=7)return {k:'a',t:`NEWS2 ${r.s}: no candidato a sala. Evaluar Reanimación o UTI.`};
  if(r.s>=5)return {k:'m',t:`NEWS2 ${r.s}: no candidato a sala común. Mantener en Urgencias o evaluar mayor complejidad.`};
  if(p.sector==='rea')return {k:'m',t:`NEWS2 ${r.s}, pero todavía no cumple todos los criterios de alta a sala.`};
  return {k:'b',t:`NEWS2 ${r.s}: candidato a sala${tc.ok?'. Además cumple criterios para '+tc.dest:''}.`}}

/* Datos ficticios */
let seed=11;const rnd=()=>(seed=(seed*16807)%2147483647)/2147483647;const pick=a=>a[Math.floor(rnd()*a.length)];
let pac=[],egresos=[],consultas=[],uid=1;
const nT=()=>({a:TA.map(()=>false),perfil:'',otro:'',c:TC.map(()=>false),d:TD.map(()=>false),dec:''});
const nS=()=>({gcs:'',delir:false,pam:'',vaso:'',otro:false,mec:false,bili:'',cr:'',diur:'',dial:false,plaq:''});
function mk(o){const p=Object.assign({id:nid(),nom:'',ci:'',fnac:'',edad:'',sexo:'',reg:'',tri:'Amarillo',sector:'obs',cama:'',tipoCama:'Fija',ingreso:new Date(NOW-6*H),motivo:'',dx:'',plan:'',
  esc:{ing:false,loc:'',grado:'',evol:[]},vit:{fr:'',sat:'',o2:false,pas:'',fc:'',conc:'A',temp:''},resp:{dev:'aire',L:'',fio2:''},sof:nS(),sofaPrev:'',gas:{ph:'',pco2:'',hco3:''},
  ais:{kpc:'No',germ:'Ninguno',origen:'Al ingreso'},est:[],qx:[],terc:nT(),dest:'',altaProb:'',alt:{hSinVent:'',o2Desc:false,hSinVaso:'',postqx:false,hReanim:''},vm:{iot:'',corr:''}},o);
  p.sof=Object.assign(nS(),o.sof||{});p.vit.o2=p.resp.dev!=='aire';if(p.fnac)p.edad=edadDe(p.fnac);pac.push(p);regMov('Ingreso',p,p.origen||'',p.cama);return p}
const V=(fr,sat,pas,fc,conc,temp)=>({fr,sat,o2:false,pas,fc,conc,temp});
function ES(tipo,nom,estado,fsol,fprog='',hora=''){if(tipo==='Imagen')tipo='Imagen (MEPROTEC)';const ext=EXT.includes(tipo);
  if(estado==='Agendado')estado='Programado';if(estado==='Pendiente')estado=ext?'Enviado':'Pendiente de programación';
  return {id:nid(),tipo,nom,estado,fsol,fprog,hora,ayuno:AYUNO.test(nom),freal:'',res:'',reag:0,fenv:estado==='Enviado'?fsol:'',smot:''}}
const dd=n=>iso(new Date(+NOW+n*D));
(function(){
  const d=h=>new Date(NOW-h*H);
  mk({nom:'Ramírez, Carlos',ci:'3452871',fnac:'1968-04-12',sexo:'M',reg:'260145',tri:'Rojo',sector:'rea',cama:'REA 1',ingreso:d(52),motivo:'Politraumatismo por accidente de moto',dx:'TCE grave, contusión pulmonar bilateral',plan:'AVM, neuroprotección, control de TAC',vit:V(16,94,108,104,'V',37.4),resp:{dev:'vmi',L:'',fio2:50},sof:{gcs:7,pam:72,vaso:0.15,bili:1.1,cr:1.0,plaq:118},sofaPrev:9,gas:{ph:7.33,pco2:38,hco3:20},est:[ES('Imagen','TAC de cráneo de control','Agendado',dd(-1),HOY,'21:00')],qx:[{id:nid(),nom:'Craniectomía descompresiva',serv:'Neurocirugía',estado:'Presentado',fecha:''}],dest:'UTI'});
  mk({nom:'Benítez, Rosa',ci:'1874520',fnac:'1955-09-03',sexo:'F',reg:'260152',tri:'Rojo',sector:'rea',cama:'REA 2',ingreso:d(30),motivo:'Dolor abdominal y shock',dx:'Shock séptico de foco abdominal, perforación de víscera hueca operada',plan:'Noradrenalina, antibiótico de amplio espectro, control de lactato',vit:V(24,93,92,118,'A',38.6),resp:{dev:'mr',L:10,fio2:''},sof:{gcs:15,pam:64,vaso:0.3,bili:2.4,cr:2.1,diur:'d1',plaq:96},sofaPrev:9,gas:{ph:7.24,pco2:30,hco3:13},est:[ES('Laboratorio especial','Hisopado rectal para EPC','Pendiente',HOY)],ais:{kpc:'Sospecha',germ:'Ninguno',origen:'Al ingreso'},esc:{ing:false,loc:'',grado:'',evol:[{fecha:HOY,loc:'Sacra',grado:'II',nota:'Detectada en el cambio de posición'}]},dest:'UTI'});
  mk({nom:'González, Hugo',ci:'2289014',fnac:'1977-01-20',sexo:'M',reg:'260160',tri:'Rojo',sector:'rea',cama:'REA 3',ingreso:d(20),motivo:'Cefalea súbita y deterioro de conciencia',dx:'Hemorragia subaracnoidea Fisher IV',plan:'Control de presión, nimodipino, angiotomografía',vit:V(18,97,148,88,'V',37.0),resp:{dev:'vmi',L:'',fio2:35},sof:{gcs:9,pam:96,bili:0.8,cr:0.9,plaq:210},sofaPrev:5,gas:{ph:7.41,pco2:36,hco3:23},est:[ES('Imagen','Angiotomografía cerebral','Agendado',HOY,dd(1),'08:00')],qx:[{id:nid(),nom:'Embolización o clipaje',serv:'Neurocirugía',estado:'Pendiente de presentar',fecha:''}]});
  mk({nom:'Villalba, Teresa',ci:'1023944',fnac:'1960-06-30',sexo:'F',tri:'Naranja',sector:'rea',cama:'REA 5',ingreso:d(70),motivo:'Disnea',dx:'Insuficiencia renal aguda con sobrecarga de volumen, ya dializada',plan:'Control de función renal',vit:V(18,96,128,86,'A',36.6),sof:{gcs:15,pam:88,bili:0.9,cr:1.9,plaq:160},sofaPrev:5,gas:{ph:7.36,pco2:38,hco3:21},est:[ES('Laboratorio externo','Panel respiratorio viral','Pendiente',dd(-3))],ais:{kpc:'No',germ:'BLEE',origen:'Adquirido en Urgencias'},dest:'Clínica Médica'});
  mk({nom:'Duarte, Pedro',ci:'4630217',fnac:'1992-02-14',sexo:'M',reg:'260171',tri:'Rojo',sector:'rea',cama:'REA 6',ingreso:d(10),motivo:'Herida de arma blanca en tórax',dx:'Hemoneumotórax derecho, avenado',plan:'Control de débito, transfusión',vit:V(22,94,104,112,'A',36.9),resp:{dev:'cn',L:3,fio2:''},sof:{gcs:15,pam:68,bili:'',cr:1.0,plaq:140},sofaPrev:3,gas:{ph:7.31,pco2:35,hco3:18},qx:[{id:nid(),nom:'Toracotomía si débito mayor a 1500 ml',serv:'Cirugía General',estado:'Pendiente de presentar',fecha:''}]});
  mk({nom:'Acosta, Miguel',ci:'2201788',fnac:'1964-11-08',sexo:'M',tri:'Rojo',sector:'cr',cama:'CR 1',tipoCama:'Camilla',ingreso:d(2),motivo:'Dolor torácico opresivo',dx:'IAM con supradesnivel del ST anterior',plan:'Gestión de traslado a hemodinamia',vit:V(20,95,98,96,'A',36.5),dest:'Terciarizado externo'});
  mk({nom:'Ortiz, Elena',ci:'3399120',fnac:'1949-03-22',sexo:'F',tri:'Naranja',sector:'cr',cama:'CR 2',tipoCama:'Camilla',ingreso:d(1),motivo:'Hemiparesia derecha de 2 horas',dx:'Sospecha de ACV isquémico',plan:'TC sin contraste, evaluar ventana',vit:V(18,96,176,84,'A',36.4),est:[ES('Imagen','TC de cráneo sin contraste','Agendado',HOY,HOY,'19:00')]});
  const obsDx=[['Neumonía adquirida en la comunidad','Clínica Médica','Amarillo',V(18,97,122,86,'A',36.8),2,['Laboratorio externo','Panel respiratorio viral']],['Colecistitis aguda','Cirugía General','Amarillo',V(18,97,126,92,'A',37.9),null,['Imagen','Ecografía abdominal']],['Fractura de cadera derecha','Traumatología','Naranja',V(16,96,142,80,'A',36.6)],['Pielonefritis obstructiva','Urología','Naranja',V(22,95,104,108,'A',38.9),null,['Imagen','Uro-TAC con contraste']],['Insuficiencia cardíaca descompensada','Clínica Médica','Amarillo',V(18,96,132,84,'A',36.5),0,['Imagen','Ecocardiograma transtorácico']],['Obstrucción intestinal','Cirugía General','Naranja',V(20,96,112,104,'A',37.2),null,['Imagen','TAC de abdomen con contraste']],['Celulitis de miembro inferior','Clínica Médica','Amarillo',V(16,98,130,86,'A',36.7),2],['Retención urinaria aguda','Urología','Verde',V(14,98,140,78,'A',36.4)],['Síndrome febril, sospecha de dengue','Clínica Médica','Amarillo',V(16,97,150,72,'A',38.1),null,['Laboratorio externo','Dengue NS1 e IgM']]];
  obsDx.forEach((o,i)=>{const y=1940+Math.floor(rnd()*55);const p=mk({nom:pick(['Insfrán','Cáceres','Franco','Rojas','Giménez','Martínez','Torres','Ayala','Sosa','Núñez'])+', '+pick(['Ana','Luis','María','Jorge','Celia','Ramón','Lucía','Hugo','Sonia','Pablo']),ci:String(1200000+Math.floor(rnd()*5e6)),fnac:y+'-'+two(1+Math.floor(rnd()*12))+'-'+two(1+Math.floor(rnd()*28)),sexo:pick(['F','M']),reg:rnd()<.6?String(260100+i*7):'',tri:o[2],sector:'obs',cama:'PV1 '+(i+1),ingreso:d(8+Math.floor(rnd()*90)),motivo:o[0]==='Fractura de cadera derecha'?'Caída de propia altura':'Consulta por '+o[0].toLowerCase(),dx:o[0],plan:'Tratamiento según protocolo',vit:o[3],dest:o[1]});
    if(o[5]){const ag=o[5][0]==='Imagen';p.est.push(ES(o[5][0],o[5][1],ag?'Agendado':'Pendiente',dd(ag?0:-2),ag?(i===5?dd(-1):dd(1)):'',ag?pick(['07:00','08:00','10:30']):''))}
    if(['Cirugía General','Traumatología','Urología'].includes(o[1])){p.qx.push({id:nid(),nom:{'Fractura de cadera derecha':'Artroplastia parcial de cadera','Colecistitis aguda':'Colecistectomía','Pielonefritis obstructiva':'Colocación de catéter doble J','Obstrucción intestinal':'Laparotomía exploradora'}[o[0]]||'RTU',serv:o[1],estado:pick(['Pendiente de presentar','Presentado','Con fecha']),fecha:''});p.qx.forEach(q=>{if(q.estado==='Con fecha')q.fecha=dd(2)})}
    if(o[4]!=null){p.terc.a=TA.map(()=>true);p.terc.perfil=o[4]===0?TB[0]:TB[2];if(o[0].startsWith('Celulitis'))p.terc.a[8]=false}
    if(i===2)p.esc={ing:true,loc:'Talón derecho',grado:'I',evol:[{fecha:dd(-1),loc:'Talón derecho',grado:'II',nota:'Flictena'}]};
    if(i===3)p.ais={kpc:'Confirmado',germ:'Ninguno',origen:'Al ingreso'};
    if(i===6)p.ais={kpc:'No',germ:'Clostridioides difficile',origen:'Adquirido en Urgencias'};
  });
  [['Cólico renal','Urología','Verde',V(16,98,132,88,'A',36.6)],['Hipoglucemia corregida','Alta','Amarillo',V(14,98,124,76,'A',36.3)],['Crisis hipertensiva','Clínica Médica','Amarillo',V(16,97,182,90,'A',36.5)],['Gastroenteritis con deshidratación','Alta','Verde',V(18,98,108,102,'A',37.4)]].forEach((o,i)=>mk({nom:pick(['Paredes','Galeano','Benítez','Vera','Ríos'])+', '+pick(['Rosa','Juan','Olga','Diego','Nidia']),ci:String(2200000+Math.floor(rnd()*4e6)),fnac:(1950+Math.floor(rnd()*50))+'-05-1'+i,sexo:pick(['F','M']),tri:o[2],sector:'ec',cama:'PV2 '+(i+1),ingreso:d(2+i*1.5),motivo:o[0],dx:o[0],plan:'Reevaluar en 4 horas',vit:o[3],dest:o[1]}));
  for(let i=0;i<8;i++){const fija=i<5;const p=mk({nom:pick(['Morel','Aquino','Cabrera','Fleitas','López','Medina','Ruiz','Zárate'])+', '+pick(['Blanca','Oscar','Liz','Mario','Gloria','Raúl','Edith','César']),ci:String(3100000+Math.floor(rnd()*4e6)),fnac:(1945+Math.floor(rnd()*45))+'-0'+(1+i)+'-15',sexo:pick(['F','M']),tri:'Amarillo',sector:'stc',cama:fija?'STC '+(i+1):'STC P'+(i-4),tipoCama:fija?'Fija':pick(['Sofá','Camilla provisoria']),ingreso:d(1+rnd()*7),motivo:pick(['Dolor abdominal','Disnea leve','Fiebre','Mareos','Dolor lumbar','Vómitos']),dx:'En evaluación',plan:'Reevaluar con resultados',vit:V(16+Math.floor(rnd()*8),94+Math.floor(rnd()*5),105+Math.floor(rnd()*40),80+Math.floor(rnd()*30),'A',36.4+Math.round(rnd()*20)/10)});
    if(i%3===0)p.est.push(ES('Laboratorio externo','Dengue NS1 e IgM','Pendiente',HOY))}
  const TIP={rea:[['Traslado a sala',.5],['UTI',.12],['Terciarizado externo',.06],['Óbito',.21],['Alta',.11]],obs:[['Alta',.56],['Traslado a sala',.24],['Terciarizado externo',.1],['Externado a sala de menor complejidad',.04],['Óbito',.06]],ec:[['Alta',.7],['Traslado a sala',.2],['Terciarizado externo',.08],['Óbito',.02]],cr:[['Traslado a sala',.35],['UTI',.15],['Terciarizado externo',.25],['Alta',.15],['Óbito',.1]],stc:[['Alta',.65],['Traslado a sala',.15],['Terciarizado externo',.1],['Externado a sala de menor complejidad',.1]]};
  const PD={rea:2.5,obs:3.3,ec:3.3,cr:1.5,stc:10};
  for(let day=1;day<=30;day++)for(const sc of SEC){const n=Math.floor(PD[sc.id]+rnd());for(let k=0;k<n;k++){let r=rnd(),acc=0,t='Alta';for(const[x,w]of TIP[sc.id]){acc+=w;if(r<acc){t=x;break}}
    const est=sc.id==='rea'?40+rnd()*80:sc.id==='obs'?40+rnd()*70:sc.id==='ec'?12+rnd()*36:sc.id==='cr'?1+rnd()*4:4+rnd()*10;
    egresos.push({nom:'',sector:sc.id,tipo:t,dest:t==='Traslado a sala'?pick(SERV):'',horas:est,fecha:new Date(NOW-day*D)})}}
  const MAP={'Traslado a sala':'Traslado a sala HEQI','UTI':'UTI HEQI','Terciarizado externo':'Terciarizado'};
  const NN=['Benítez','González','Ramírez','Ortiz','Villalba','Martínez','Giménez','Duarte','Acosta','Rojas','Cáceres','Franco','Ayala','Torres','Sosa'],PN=['Ana','Carlos','María','Luis','Rosa','Pedro','Lucía','Jorge','Elena','Ramón','Teresa','Miguel'];
  const DX={rea:['Politraumatismo','Shock séptico','HSA','TCE grave','Postoperatorio de laparotomía'],obs:['Neumonía','Insuficiencia cardíaca','Pielonefritis','ACV isquémico','Celulitis'],ec:['Cólico renal','Crisis hipertensiva','Hipoglucemia','Gastroenteritis'],cr:['IAM','ACV','Politraumatismo'],stc:['Dolor abdominal','Fiebre','Disnea leve']};
  const SW=['Clínica Médica','Clínica Médica','Clínica Médica','Clínica Médica','Cirugía General','Cirugía General','Traumatología','Traumatología','Urología','Neurocirugía','Coloproctología','Mastología'];
  egresos.forEach(e=>{e.tipo=MAP[e.tipo]||e.tipo;if(e.tipo==='Traslado a sala HEQI')e.dest=pick(SW);if(e.tipo==='Terciarizado'&&rnd()<.35){e.tipo='Otra red IPS';e.dest=pick(RED)}else if(e.tipo==='Terciarizado')e.dest=rnd()<.6?'Sanatorio Español':pick(['Sanatorio Migone','Sanatorio San Roque','Sanatorio La Costa']);
    e.nom=pick(NN)+', '+pick(PN);e.ci=String(1000000+Math.floor(rnd()*6e6));e.edad=20+Math.floor(rnd()*70);e.dx=pick(DX[e.sector]);e.ingreso=new Date(+e.fecha-e.horas*H)});
  consultas.push({hora:'16:10',nom:'Silva, Marta',motivo:'Dolor abdominal',news:2,dec:'Alta - tratamiento ambulatorio'},{hora:'17:05',nom:'Pereira, Hugo',motivo:'Disnea',news:6,dec:'Internado en Polivalente 1'});
})();

/* Estados de cama y espera (ficticios) */
bedSt={'REA 4':{st:'Contaminada',nota:'Limpieza terminal (EPC)'},'REA 7':{st:'Bloqueada',nota:'Monitor en reparación',ticket:'SOL-2026-1184'},'REA 8':{st:'Reservada',nota:'TCE grave derivado de Ciudad del Este',hora:'19:30',espId:1},'PV1 10':{st:'En limpieza',nota:''},'PV2 5':{st:'Sucia',nota:''}};
espera=[{id:1,nom:'Galeano, Derlis',ci:'4987123',edad:31,tri:'Rojo',motivo:'TCE grave por accidente de moto, intubado',sector:'rea',origen:'Derivado externo',lugar:'Hospital Regional de Ciudad del Este',sol:new Date(NOW-1.5*H)},
 {id:2,nom:'Fleitas, Nidia',ci:'2765410',edad:68,tri:'Amarillo',motivo:'Neumonía, requiere internación',sector:'obs',origen:'Urgencias HEQI',lugar:'Sala de trabajo clínico',sol:new Date(NOW-5*H)},
 {id:3,nom:'Ojeda, Ramón',ci:'1550982',edad:59,tri:'Rojo',motivo:'Shock séptico de foco urinario, en AVM',sector:'rea',origen:'Derivado externo',lugar:'Hospital de Luque',sol:new Date(NOW-2*H)}];
let espUid=4,espBajas=[];
pac.forEach(p=>{if(p.cama==='REA 5')p.alt={hSinVent:72,o2Desc:false,hSinVaso:60,postqx:false,hReanim:''};if(p.cama==='REA 6')p.alt={hSinVent:10,o2Desc:true,hSinVaso:8,postqx:false,hReanim:''};if(p.cama==='REA 2')p.alt={hSinVent:'',o2Desc:false,hSinVaso:0,postqx:true,hReanim:6};if(p.sector==='obs'&&['PV1 1','PV1 5','PV1 9'].includes(p.cama))p.altaProb='Mañana';if(p.sector==='ec'&&['PV2 2','PV2 4'].includes(p.cama))p.altaProb='Hoy';
  if(p.cama==='PV1 7')p.est.push(ES('Anatomía patológica','Anatomía patológica de tejido debridado','Pendiente de envío',dd(-1)));
  if(p.cama==='REA 5')p.est.push(ES('Procedimiento diagnóstico','Ecocardiograma transtorácico','Pendiente de programación',dd(-1)));
  if(p.cama==='PV1 3')p.qx.forEach(q=>{if(q.estado==='Con fecha')q.hora='07:30'})});

/* Camas */
const occ=s=>pac.filter(p=>p.sector===s);
function freeFixed(s,allowRes){const S=SECN[s],used=new Set(occ(s).map(p=>p.cama)),r=[];for(let i=1;i<=S.fijas;i++){const c=S.pref+' '+i,b=bedSt[c];if(!used.has(c)&&(!b||b.st==='Libre'||(allowRes&&b.st==='Reservada')))r.push(c)}return r}
function regMov(tipo,p,de,a){if(SEMBRANDO)return;movs.push({f:new Date(),tipo,nom:p&&p.nom||'',ci:p&&p.ci||'',de:de||'',a:a||'',u:USUARIO});if(movs.length>3000)movs=movs.slice(-3000)}
function liberar(p){if(p.tipoCama!=='Fija')return;const a=aisl(p);bedSt[p.cama]={st:a&&a.k==='a'?'Contaminada':'Sucia',nota:a&&a.k==='a'?'Limpieza terminal':'' }}
function nextProv(s){const S=SECN[s],used=new Set(occ(s).map(p=>p.cama));for(let i=1;i<=S.extra;i++){const c=S.pref+(S.virtual?' ':' P')+i;if(!used.has(c))return c}return null}
function pend(p){const ch=[],act=p.est.filter(e=>ACT.includes(e.estado)),al=alertas(p);
  if(act.length)ch.push(`<span class="chip w">${act.length} estudio${act.length>1?'s':''} pendiente${act.length>1?'s':''}</span>`);
  const ay=al.find(x=>/Ayuno desde/.test(x[1]));if(ay)ch.push(`<span class="chip bd">${esc(ay[1].match(/Ayuno desde las \d\d:\d\d/)[0].replace('las ',''))}</span>`);
  const nr=al.filter(x=>x[0]==='bd').length;if(nr)ch.push(`<span class="chip bd">${nr} alerta${nr>1?'s':''}</span>`);
  if(p.altaProb)ch.push(`<span class="chip i">Alta probable ${p.altaProb.toLowerCase()}</span>`);
  p.qx.filter(q=>!['Realizado','Sin efecto'].includes(q.estado)).forEach(q=>ch.push(`<span class="chip ${q.estado==='Con fecha'?'i':'w'}">Qx: ${q.estado==='Con fecha'&&q.fecha?'fecha '+fi(q.fecha).slice(0,5)+(q.hora?' '+q.hora:''):q.estado==='Presentado'?'sin fecha':q.estado==='Suspendido'?'suspendida':'sin presentar'}</span>`));
  const a=aisl(p);if(a)ch.push(`<span class="chip ${a.chip[0]}">${esc(a.chip[1])}</span>`);
  const es=escara(p);if(es)ch.push(`<span class="chip bd">${es.adq?'Escara adquirida':es.prog?'Escara progresó':'Escara al ingreso'}</span>`);
  if(p.sector==='rea'&&altaSala(p).ok)ch.push('<span class="chip ok">Apto para sala</span>');
  const tc=tercer(p);if(tc.ok)ch.push(`<span class="chip i">Candidato: ${tc.dest}</span>`);
  if(p.dest)ch.push(`<span class="chip ok">→ ${esc(p.dest)}</span>`);return ch.join('')}
function renderCamas(){
  const tot=SEC.reduce((a,s)=>a+s.fijas,0),ocF=pac.filter(p=>p.tipoCama==='Fija').length,prov=pac.filter(p=>p.tipoCama!=='Fija').length;
  const alto=pac.filter(p=>{const r=news2(p.vit);return r&&r.s>=7}).length;
  const adqE=pac.filter(p=>{const e=escara(p);return e&&e.adq}).length,adqG=pac.filter(p=>p.ais.origen==='Adquirido en Urgencias'&&(p.ais.kpc!=='No'||p.ais.germ!=='Ninguno')).length;
  $('k-camas').innerHTML=[[`${ocF}/${tot}`,'Camas fijas ocupadas'],[prov,'En sofá o camilla provisoria'],[alto,'Pacientes con NEWS2 7 o más'],[pac.filter(p=>aisl(p)&&aisl(p).k==='a').length,'Requieren sala de aislamiento'],[adqE,'Escaras adquiridas en Urgencias'],[adqG,'Gérmenes adquiridos en Urgencias']].map(([v,t])=>`<div class="kpi"><b>${v}</b><span>${t}</span></div>`).join('');
  const al=[];pac.forEach(p=>alertas(p).forEach(([k,x])=>al.push(`<li><b>${esc(p.cama)} - ${esc(p.nom)}:</b> ${esc(x)}</li>`)));
  $('alertas').innerHTML=al.length?`<details class="alr" ${window._alOpen?'open':''} ontoggle="window._alOpen=this.open"><summary style="color:var(--bad)">Alertas de Urgencias (${al.length}) - tocá para ver</summary><ul>${al.join('')}</ul></details>`:'';
  $('sectores').innerHTML=SEC.map(S=>{if(S.virtual){const l=occ(S.id);return `<div class="box"><div class="sec-head"><div><h2>${S.n}</h2><span class="note">${S.sub}</span></div><span class="occ ${l.length?'warn':''}">${l.length?l.length+' camilla'+(l.length>1?'s':''):'Sin código rojo'}</span></div><div class="beds">${l.map(card).join('')}<button class="bed free" data-prov="${S.id}">+ Ingresar código rojo</button></div></div>`}
    const l=occ(S.id),fo=l.filter(p=>p.tipoCama==='Fija').length,pr=l.length-fo,k=fo>=S.fijas?'full':fo>=S.fijas*.8?'warn':'';
    let cards='';for(let i=1;i<=S.fijas;i++){const c=S.pref+' '+i,p=l.find(x=>x.cama===c);cards+=p?card(p):`<button class="bed free" data-new="${S.id}" data-cama="${c}">${c}<br>Libre - ingresar</button>`}
    l.filter(p=>p.tipoCama!=='Fija').forEach(p=>cards+=card(p));
    if(S.extra)cards+=`<button class="bed free" data-prov="${S.id}">+ Agregar en sofá o camilla provisoria<br><span class="note">${pr} de ${S.extra} en uso</span></button>`;
    return `<div class="box"><div class="sec-head"><div><h2>${S.n}</h2><span class="note">${S.sub}</span></div><span class="occ ${k}">${fo}/${S.fijas} camas${pr?' + '+pr+' provisorias':''}</span></div><div class="beds">${cards}</div></div>`}).join('')}
function card(p){const so=sofa(p);return `<button class="bed t-${p.tri.toLowerCase()}" data-open="${p.id}"><span class="top"><span>${esc(p.cama)}${!['Fija','Camilla'].includes(p.tipoCama)?' <span class="prov">'+p.tipoCama+'</span>':''}</span><span>${dur(NOW-p.ingreso)}</span></span><span class="nm">${esc(p.nom)}, ${esc(p.edad)} a</span><span class="dx">${esc(p.dx||p.motivo)}</span><span class="chips">${newsBadge(p)}${p.sector==='rea'&&so?`<span class="news n-${so.s>=8?'a':so.s>=2?'m':'b'}">SOFA-2 ${so.s}</span>`:''}${pend(p)}</span></button>`}

/* Ingreso */
function abrirIngreso(sector,cama){window._espId=null;
  const S=SECN[sector],prov=!cama;
  $('md').innerHTML=`<div class="md-h"><div><h2>Ingreso a ${S.n}</h2><span class="note">${S.virtual?'Camilla de código rojo':prov?'Lugar provisorio':'Cama '+cama}</span></div><button class="b g s" data-close>Cerrar</button></div>
  ${prov&&!S.virtual?`<label for="i-tc">Tipo de lugar</label><select id="i-tc"><option>Camilla provisoria</option><option>Sofá</option></select>`:''}
  <div class="row"><div><label for="i-nom">Paciente</label><input id="i-nom" placeholder="Apellido y nombre"></div><div><label for="i-ci">Cédula</label><input id="i-ci" inputmode="numeric"></div></div>
  <div class="row"><div><label for="i-fn">Fecha de nacimiento</label><input id="i-fn" type="date"></div><div style="flex:0 1 90px"><label for="i-edad">Edad</label><input id="i-edad" type="number" min="0"></div><div><label for="i-sexo">Sexo</label><select id="i-sexo"><option value="">-</option><option>F</option><option>M</option></select></div><div><label for="i-reg">Registro de internación (opcional)</label><input id="i-reg"></div></div>
  <label>Clasificación de triage</label><div class="tri">${TRI.map(t=>`<label><input type="radio" name="i-tri" value="${t}" ${t===(sector==='rea'||sector==='cr'?'Rojo':'Amarillo')?'checked':''}><span class="dot" style="background:${TRIC[t]}"></span>${t}</label>`).join('')}</div>
  <label for="i-mot">Motivo de consulta</label><input id="i-mot">
  <div class="row"><div><label for="i-esc">Escara al ingreso</label><select id="i-esc"><option value="">No</option><option value="1">Sí</option></select></div><div><label for="i-escl">Localización</label><input id="i-escl"></div><div style="flex:0 1 140px"><label for="i-escg">Grado</label><select id="i-escg"><option value="">-</option>${GRADOS.map(g=>`<option>${g}</option>`).join('')}</select></div></div>
  <div style="margin-top:12px"><button class="b" id="i-ok">Ingresar y abrir ficha</button></div><div class="msg" id="i-msg"></div>`;
  $('ov').classList.add('on');
  $('i-fn').oninput=()=>{$('i-edad').value=edadDe($('i-fn').value)};
  $('i-ok').onclick=()=>{const nom=$('i-nom').value.trim(),ci=$('i-ci').value.trim(),ed=$('i-edad').value,m=$('i-msg');
    if(!nom||!ci||ed===''){m.className='msg on err';m.textContent='Nombre, cédula y edad (o fecha de nacimiento) son obligatorios.';return}
    if(pac.some(p=>p.ci===ci)){m.className='msg on err';m.textContent='Esta cédula ya está ingresada en Urgencias. Usá "Mover" desde su ficha.';return}
    let c=cama,tc='Fija';if(prov){c=nextProv(sector);tc=S.virtual?'Camilla':$('i-tc').value;if(!c){m.className='msg on err';m.textContent='Se alcanzó el máximo de lugares provisorios.';return}}
    const p=mk({nom,ci,fnac:$('i-fn').value,edad:+ed,sexo:$('i-sexo').value,reg:$('i-reg').value.trim(),tri:document.querySelector('input[name=i-tri]:checked').value,sector,cama:c,tipoCama:tc,ingreso:new Date(NOW),motivo:$('i-mot').value.trim(),esc:{ing:!!$('i-esc').value,loc:$('i-escl').value.trim(),grado:$('i-escg').value,evol:[]}});
    if(bedSt[c]){delete bedSt[c]}if(window._espId){espera=espera.filter(x=>x.id!==window._espId);window._espId=null}renderAll();abrirFicha(p.id)}}

/* Ficha */
let cur=null,confEgr=false;
function abrirFicha(id){cur=pac.find(p=>p.id===id);if(!cur)return;confEgr=false;renderFicha();$('ov').classList.add('on')}
function vitInputs(pref,v,conO2=true){const f=[['fr','FR (rpm)'],['sat','SatO2 (%)'],['pas','PA sistólica'],['fc','FC (lpm)'],['temp','Temperatura (°C)']];
  return f.map(([k,l])=>`<div style="flex:1 1 110px"><label for="${pref}${k}">${l}</label><input id="${pref}${k}" data-v="${k}" type="number" step="any" value="${esc(v[k])}"></div>`).join('')+
  (conO2?`<div style="flex:1 1 110px"><label for="${pref}o2">Oxígeno</label><select id="${pref}o2" data-v="o2"><option value="">Aire ambiente</option><option value="1" ${v.o2?'selected':''}>Con O2</option></select></div>`:'')+
  `<div style="flex:1 1 130px"><label for="${pref}conc">Conciencia</label><select id="${pref}conc" data-v="conc">${[['A','Alerta'],['C','Confusión nueva'],['V','Responde a la voz'],['P','Responde al dolor'],['U','No responde']].map(([a,b])=>`<option value="${a}" ${v.conc===a?'selected':''}>${b}</option>`).join('')}</select></div>`}
function estRow(e){const inp=v=>`<input type="date" data-ed="${e.id}" aria-label="Fecha" value="${v||''}"><input type="time" data-eh="${e.id}" aria-label="Hora" value="${e.hora||''}" style="width:auto;padding:3px 6px;font-size:.85rem">`;
  const B=(k,x,c='b s')=>`<button class="${c}" data-${k}="${e.id}">${x}</button>`;let st,acts;
  if(e.estado==='Pendiente de programación'){st='<span class="chip w">Pendiente de programación</span>';acts=inp('')+B('ea','Programar')+B('ex','Sin efecto','b r s')}
  else if(e.estado==='Programado'){const v=at(e.fprog,e.hora||'23:59')<NOW;st=`<span class="chip ${v||(!e.hora&&e.tipo==='Imagen (MEPROTEC)')?'bd':'i'}">Programado ${fi(e.fprog)}${e.hora?' '+e.hora:' - sin hora'}${v?' - vencido':''}${e.reag?' (reprogramado '+e.reag+')':''}</span>`;
    acts=inp(e.fprog)+B('ea','Reprogramar','b g s')+B('er','Realizado')+B('esu','Suspender','b g s')+B('ex','Sin efecto','b r s')}
  else if(e.estado==='Suspendido'){st=`<span class="chip bd">Suspendido${e.smot?': '+esc(e.smot):''}</span>`;acts=inp('')+B('ea','Reprogramar')+B('ex','Sin efecto','b r s')}
  else if(e.estado==='Pendiente de envío'){st='<span class="chip bd">Pendiente de envío</span>';acts=B('env','Enviado')+B('ex','Sin efecto','b r s')}
  else {st=`<span class="chip w">Enviado ${fi(e.fenv||e.fsol)} - esperando resultado</span>`;acts=B('er','Resultado recibido')+B('ex','Sin efecto','b r s')}
  const ay=e.ayuno?' <span class="chip bd">Ayuno 6 h</span>':'';
  return `<li><span><b>${esc(e.nom)}</b> <span class="note">${e.tipo} · solicitado ${fi(e.fsol)}</span><br>${st}${ay}</span><span class="acts">${acts}</span></li>`}
function renderFicha(){
  const p=cur,S=SECN[p.sector],sf=p.sof,t=p.terc;
  const ord=e=>e.estado==='Programado'?'1'+e.fprog+(e.hora||'99'):'0'+e.estado;const sol=p.est.filter(e=>ACT.includes(e.estado)).sort((a,b)=>ord(a)<ord(b)?-1:1);
  const real=p.est.filter(e=>e.estado==='Realizado'),nul=p.est.filter(e=>e.estado==='Sin efecto'),al=alertas(p);
  $('md').innerHTML=`<div class="md-h"><div><h2>${esc(p.nom)}, <span id="h-edad">${esc(p.edad)}</span> años</h2><span class="note">${S.n} - ${esc(p.cama)}${p.tipoCama!=='Fija'?' ('+p.tipoCama+')':''} · ingreso ${fdt(p.ingreso)} · ${dur(NOW-p.ingreso)}</span></div><button class="b s" id="f-tras" style="margin-right:6px">🔄 Trasladar de cama</button><button class="b g s" data-close>Cerrar</button></div>
  ${al.length?`<div class="alr"><h2>Alertas</h2><ul>${al.map(x=>`<li>${esc(x[1])}</li>`).join('')}</ul></div>`:''}
  <details open><summary>Datos del paciente</summary>
    <div class="row"><div><label>Paciente</label><input data-f="nom" value="${esc(p.nom)}"></div><div><label>Cédula</label><input data-f="ci" value="${esc(p.ci)}"></div></div>
    <div class="row"><div><label>Fecha de nacimiento</label><input data-f="fnac" type="date" value="${esc(p.fnac)}"></div><div style="flex:0 1 90px"><label>Edad</label><input data-f="edad" type="number" value="${esc(p.edad)}" id="f-edad"></div><div><label>Sexo</label><select data-f="sexo"><option value="">-</option><option ${p.sexo==='F'?'selected':''}>F</option><option ${p.sexo==='M'?'selected':''}>M</option></select></div></div>
    <div class="row"><div><label>Registro de internación (opcional)</label><input data-f="reg" value="${esc(p.reg)}"></div><div><label>Triage</label><select data-f="tri">${TRI.map(x=>`<option ${x===p.tri?'selected':''}>${x}</option>`).join('')}</select></div></div>
    <label>Motivo de consulta</label><input data-f="motivo" value="${esc(p.motivo)}">
  </details>
  <details open><summary>Diagnósticos y plan</summary>
    <label>Diagnósticos actuales</label><textarea data-f="dx">${esc(p.dx)}</textarea>
    <label>Plan</label><textarea data-f="plan">${esc(p.plan)}</textarea>
  </details>
  <details open><summary>Escaras</summary>
    <div class="row"><div><label>Escara al ingreso</label><select data-es="ing"><option value="">No</option><option value="1" ${p.esc.ing?'selected':''}>Sí</option></select></div><div><label>Localización</label><input data-es="loc" value="${esc(p.esc.loc)}"></div><div style="flex:0 1 140px"><label>Grado</label><select data-es="grado"><option value="">-</option>${GRADOS.map(g=>`<option ${p.esc.grado===g?'selected':''}>${g}</option>`).join('')}</select></div></div>
    <h3>Evolución de escaras</h3>
    <ul class="items">${p.esc.evol.map(v=>`<li><span><b>${fi(v.fecha)}</b> · ${esc(v.loc)} · grado ${esc(v.grado)}${v.nota?'<br><span class="note">'+esc(v.nota)+'</span>':''}</span></li>`).join('')||'<li class="note">Sin registros de evolución.</li>'}</ul>
    <div class="row"><div style="flex:0 1 150px"><label>Fecha</label><input id="ev-f" type="date" value="${HOY}"></div><div><label>Localización</label><input id="ev-l" value="${esc(p.esc.loc)}"></div><div style="flex:0 1 140px"><label>Grado</label><select id="ev-g">${GRADOS.map(g=>`<option>${g}</option>`).join('')}</select></div></div>
    <div class="row"><div><label>Nota</label><input id="ev-n"></div><div style="flex:0 0 auto"><button class="b" id="ev-ok">Registrar evolución</button></div></div>
    <div id="f-esc"></div>
  </details>
  <details open><summary>Aislamiento y gérmenes multirresistentes</summary>
    <div class="row"><div><label>EPC / EPC</label><select data-a="kpc">${[['No','No'],['Sospecha','Sospecha (hisopado rectal solicitado)'],['Confirmado','Confirmado']].map(([a,b])=>`<option value="${a}" ${p.ais.kpc===a?'selected':''}>${b}</option>`).join('')}</select></div>
    <div><label>Otro germen</label><select data-a="germ">${GERM.map(g=>`<option ${p.ais.germ===g?'selected':''}>${g}</option>`).join('')}</select></div>
    <div><label>Origen</label><select data-a="origen">${['Al ingreso','Adquirido en Urgencias'].map(g=>`<option ${p.ais.origen===g?'selected':''}>${g}</option>`).join('')}</select></div></div>
    <div id="f-ais"></div><p class="note">Al marcar sospecha de EPC se solicita solo el hisopado rectal. EPC y C. difficile requieren sala de aislamiento; los demás, aislamiento de contacto in situ.</p>
  </details>
  <details open><summary>NEWS2</summary><div class="row">${vitInputs('fv-',p.vit)}</div><div id="f-news"></div></details>
  <details open><summary>SOFA-2 (JAMA 2025)</summary>
    <h3>Respiratorio: SpO2/FiO2 convertido a PaO2/FiO2</h3>
    <div class="row"><div><label>Soporte de oxígeno</label><select data-r="dev">${DEV.map(([a,b])=>`<option value="${a}" ${p.resp.dev===a?'selected':''}>${b}</option>`).join('')}<option value="ecmo" ${p.resp.dev==='ecmo'?'selected':''}>ECMO</option></select></div>
      <div id="r-lw"><label>Litros por minuto</label><input data-r="L" type="number" step="0.5" value="${esc(p.resp.L)}"></div>
      <div id="r-fw"><label>FiO2 (%)</label><input data-r="fio2" type="number" value="${esc(p.resp.fio2)}"></div></div>
    <div id="r-vm" class="box" style="margin-top:8px"><b>🫁 Intubado - corrugado (circuito del ventilador)</b>
      <div class="row"><div><label>Fecha y hora de intubación</label><input data-vm="iot" type="datetime-local" value="${esc((p.vm||{}).iot||'')}"></div>
      <div><label>Corrugado colocado o último cambio</label><input data-vm="corr" type="datetime-local" value="${esc((p.vm||{}).corr||'')}"></div></div>
      <button class="b g s" id="vm-now" style="margin-top:6px">✔ Cambié el corrugado ahora</button>
      <p class="note">Alarma a las 72 h del último cambio.</p></div>
    <div id="f-resp"></div>
    <h3>Otros órganos</h3>
    <div class="row">
      <div><label>Glasgow</label><input data-s="gcs" type="number" min="3" max="15" value="${esc(sf.gcs)}"></div>
      <div><label>Fármacos para delirium</label><select data-s="delir"><option value="">No</option><option value="1" ${sf.delir?'selected':''}>Sí</option></select></div>
      <div><label>PAM (mmHg)</label><input data-s="pam" type="number" value="${esc(sf.pam)}"></div>
      <div><label>Noradrenalina + adrenalina (µg/kg/min)</label><input data-s="vaso" type="number" step="0.01" value="${esc(sf.vaso)}"></div>
      <div><label>Otro vasopresor o inotrópico</label><select data-s="otro"><option value="">No</option><option value="1" ${sf.otro?'selected':''}>Sí</option></select></div>
      <div><label>Soporte circulatorio mecánico</label><select data-s="mec"><option value="">No</option><option value="1" ${sf.mec?'selected':''}>Sí</option></select></div>
      <div><label>Bilirrubina total (mg/dl)</label><input data-s="bili" type="number" step="any" value="${esc(sf.bili)}"></div>
      <div><label>Creatinina (mg/dl)</label><input data-s="cr" type="number" step="any" value="${esc(sf.cr)}"></div>
      <div><label>Diuresis</label><select data-s="diur">${[['','Normal o sin dato'],['d1','Menor a 0,5 ml/kg/h por 6 a 12 h'],['d2','Menor a 0,3 ml/kg/h por 12 h o más'],['d3','Menor a 0,3 ml/kg/h por 24 h o anuria 12 h']].map(([a,b])=>`<option value="${a}" ${sf.diur===a?'selected':''}>${b}</option>`).join('')}</select></div>
      <div><label>Diálisis o criterios de terapia renal</label><select data-s="dial"><option value="">No</option><option value="1" ${sf.dial?'selected':''}>Sí</option></select></div>
      <div><label>Plaquetas (x1000)</label><input data-s="plaq" type="number" value="${esc(sf.plaq)}"></div>
      <div><label>SOFA-2 de hace 24 h</label><input data-f="sofaPrev" type="number" value="${esc(p.sofaPrev)}"></div>
    </div><div id="f-sofa-r"></div>
  </details>
  ${p.sector==='rea'?`<details open><summary>Gasometría y criterios de alta a sala (Reanimación)</summary>
    <div class="row"><div><label>pH (obligatorio)</label><input data-g="ph" type="number" step="0.01" value="${esc(p.gas.ph)}"></div><div><label>PaCO2 (obligatorio)</label><input data-g="pco2" type="number" step="any" value="${esc(p.gas.pco2)}"></div><div><label>Bicarbonato (obligatorio)</label><input data-g="hco3" type="number" step="any" value="${esc(p.gas.hco3)}"></div></div>
    <h3>Checklist de alta a sala</h3>
    <div class="row"><div><label>Horas sin VMI, VNI ni alto flujo</label><input data-al="hSinVent" type="number" value="${esc(p.alt.hSinVent)}"></div><div><label>Oxígeno en plan de descenso</label><select data-al="o2Desc"><option value="">No</option><option value="1" ${p.alt.o2Desc?'selected':''}>Sí</option></select></div><div><label>Horas sin vasopresores</label><input data-al="hSinVaso" type="number" value="${esc(p.alt.hSinVaso)}"></div></div>
    <div class="row"><div><label>Postquirúrgico de alta complejidad o cirugía prolongada</label><select data-al="postqx"><option value="">No</option><option value="1" ${p.alt.postqx?'selected':''}>Sí</option></select></div><div><label>Horas reanimado y estable</label><input data-al="hReanim" type="number" value="${esc(p.alt.hReanim)}"></div></div>
    <div id="f-alta"></div></details>`:''}
  <details open><summary>Estudios relevantes</summary>
    <p class="note">Solo estudios complejos, costosos o externos: imágenes de MEPROTEC (con hora de agendamiento), laboratorio externo, anatomía patológica, panel respiratorio, dengue, ecocardiograma, endoscopía. La rutina diaria no se carga acá.</p>
    <h3>Pendientes (${sol.length})</h3><ul class="items">${sol.map(estRow).join('')||'<li class="note">Sin estudios pendientes.</li>'}</ul>
    <h3>Realizados (${real.length})</h3><ul class="items">${real.map(e=>`<li style="display:block"><span><b>${esc(e.nom)}</b> <span class="note">${e.tipo}</span> <span class="chip ok">${EXT.includes(e.tipo)?'Resultado recibido':'Realizado'} ${fi(e.freal)}</span></span><input data-res="${e.id}" placeholder="Resultado final (opcional)" value="${esc(e.res)}" style="margin-top:5px"></li>`).join('')||'<li class="note">Ninguno todavía.</li>'}</ul>
    ${nul.length?`<h3>Sin efecto</h3><ul class="items">${nul.map(e=>`<li><span>${esc(e.nom)}</span><span class="chip">Sin efecto</span></li>`).join('')}</ul>`:''}
    <fieldset><legend>Solicitar estudio</legend>
      <div class="row"><div style="flex:0 1 190px"><label>Tipo</label><select id="ne-t">${TIPOS.map(x=>`<option>${x}</option>`).join('')}</select></div><div><label>Estudio</label><input id="ne-n" placeholder="Ej. Angiotomografía, panel viral"></div></div>
      <div class="row"><div><label>Fecha de solicitud</label><input id="ne-fs" type="date" value="${HOY}"></div><div id="ne-mw"><label>Estado inicial</label><select id="ne-m"><option>Pendiente de programación</option><option>Programado</option></select></div><div id="ne-fw" style="display:none"><label>Fecha programada</label><input id="ne-fa" type="date"></div><div id="ne-hw" style="display:none"><label>Hora</label><input id="ne-h" type="time"></div></div>
      <label class="check" id="ne-aw"><input type="checkbox" id="ne-ay">Requiere ayuno de 6 h</label>
      <button class="b" id="ne-ok">Solicitar</button>
    </fieldset>
  </details>
  <details open><summary>Procedimientos quirúrgicos</summary>
    <ul class="items">${p.qx.map(q=>`<li><span><b>${esc(q.nom)}</b> <span class="note">${esc(q.serv)}</span><br><span class="chip ${q.estado==='Realizado'?'ok':q.estado==='Sin efecto'?'':q.estado==='Con fecha'?'i':'w'}">${q.estado==='Presentado'?'Presentado, pendiente de fecha':q.estado}${q.estado==='Con fecha'&&q.fecha?': '+fi(q.fecha)+(q.hora?' '+q.hora:' (sin hora)'):''}</span></span><span class="acts">${qxActs(q)}</span></li>`).join('')||'<li class="note">Sin procedimientos quirúrgicos.</li>'}</ul>
    <p class="note">Cirugías y procedimientos: amputación, endoscopía, drenajes, etc.</p><div class="row" style="margin-top:8px"><div><label>Procedimiento</label><input id="nq-n"></div><div style="flex:0 1 170px"><label>Servicio</label><select id="nq-s">${SERV.filter(s=>s!=='Clínica Médica').map(s=>`<option>${s}</option>`).join('')}</select></div><div style="flex:0 0 auto"><button class="b" id="nq-ok">Agregar</button></div></div>
  </details>
  <details><summary>Checklist de derivación a tercerizados</summary>
    <fieldset><legend>A. Criterios obligatorios (todos)</legend>${TA.map((c,i)=>`<label class="check"><input type="checkbox" data-ta="${i}" ${t.a[i]?'checked':''}>${c}</label>`).join('')}</fieldset>
    <fieldset><legend>B. Perfil elegible</legend><select data-tp><option value="">Elegir perfil</option>${TB.map(x=>`<option ${t.perfil===x?'selected':''}>${x}</option>`).join('')}</select><input data-to placeholder="Si es Otros, especificar" value="${esc(t.otro)}" style="margin-top:6px"></fieldset>
    <fieldset><legend>C. Excluyentes (si hay alguno, no se terciariza)</legend>${TC.map((c,i)=>`<label class="check"><input type="checkbox" data-tx="${i}" ${t.c[i]?'checked':''}>${c}</label>`).join('')}</fieldset>
    <fieldset><legend>D. Sanatorio Español (además de A, B y C)</legend>${TD.map((c,i)=>`<label class="check"><input type="checkbox" data-tdd="${i}" ${t.d[i]?'checked':''}>${c}</label>`).join('')}</fieldset>
    <div id="f-terc"></div>
  </details>
  <details open><summary>Plan de traslado</summary>
    <div id="f-sug"></div>
    <div class="row"><div><label>Alta o traslado probable</label><select data-f="altaProb">${['','Hoy','Mañana'].map(x=>`<option value="${x}" ${p.altaProb===x?'selected':''}>${x||'No'}</option>`).join('')}</select></div></div>
    <div class="row"><div><label>Servicio a destinar (obligatorio)</label><select data-f="dest"><option value="">Sin definir</option>${DEST.map(d=>`<option ${p.dest===d?'selected':''}>${d}</option>`).join('')}</select></div></div>
    <h3 id="h-tras">🔄 Traslado de cama (dentro de Urgencias)</h3><p class="note">Elegí el sector y la cama de destino. La cama anterior pasa sola a "Sucia" (o "Contaminada" si hay aislamiento) y el movimiento queda registrado.</p>
    <div class="row"><div><label>Sector</label><select id="mv-s">${SEC.map(s=>`<option value="${s.id}" ${s.id===p.sector?'selected':''}>${s.n}</option>`).join('')}</select></div><div><label>Lugar</label><select id="mv-c"></select></div><div style="flex:0 0 auto"><button class="b" id="mv-ok">Trasladar</button></div></div>
    <h3>Egreso de Urgencias</h3>
    <div class="row"><div><label>Tipo de egreso</label><select id="eg-t">${EGR.map(x=>`<option>${x}</option>`).join('')}</select></div><div id="eg-sw"><label id="eg-sl">Destino</label><select id="eg-s"></select></div><div id="eg-ow" style="display:none"><label>¿Cuál?</label><input id="eg-o"></div></div>
    <div style="margin-top:8px"><button class="b r" id="eg-ok">Registrar egreso</button></div>
    <div class="msg" id="f-msg"></div>
  </details>
  <details open><summary>Resumen clínico</summary><pre class="res" id="f-res"></pre><button class="b g s" id="f-copy">Copiar resumen</button></details>`;
  live();moverOpts();respVis();
  const egT=$('eg-t'),sw=()=>{const v=egT.value,l=v==='Traslado a sala HEQI'?SERV:v==='Otra red IPS'?RED:v==='Terciarizado'?TERCS:null;$('eg-sw').style.display=l?'':'none';
    if(l){$('eg-sl').textContent=v==='Traslado a sala HEQI'?'Servicio':v==='Otra red IPS'?'Centro de la red':'Sanatorio';$('eg-s').innerHTML=l.map(x=>`<option ${p.dest===x?'selected':''}>${x}</option>`).join('')}ow()},
    ow=()=>{$('eg-ow').style.display=egT.value==='Terciarizado'&&$('eg-s').value.startsWith('Otro')?'':'none'};egT.onchange=()=>{sw();confEgr=false};$('eg-s').onchange=ow;
    if(p.dest==='Terciarizado externo'||p.dest==='Sanatorio Español')egT.value='Terciarizado';else if(p.dest==='UTI')egT.value='UTI HEQI';else if(p.dest==='Alta')egT.value='Alta';else if(p.dest==='Otra red IPS')egT.value='Otra red IPS';else if(SERV.includes(p.dest))egT.value='Traslado a sala HEQI';sw();
  const nf=()=>{const ext=EXT.includes($('ne-t').value),ag=!ext&&$('ne-m').value==='Programado';$('ne-mw').style.display=ext?'none':'';$('ne-fw').style.display=ag?'':'none';$('ne-hw').style.display=ag?'':'none';$('ne-aw').style.display=ext?'none':''};
  $('ne-t').onchange=nf;$('ne-m').onchange=nf;nf();
  $('ne-n').oninput=()=>{$('ne-ay').checked=AYUNO.test($('ne-n').value)};
}
function respVis(){const d=cur.resp.dev;if($('r-vm'))$('r-vm').style.display=d==='vmi'?'':'none';$('r-lw').style.display=['cn','ms','mr'].includes(d)?'':'none';$('r-fw').style.display=['vtr','cnaf','vni','vmi','ecmo'].includes(d)?'':'none'}
function qxActs(q){const b=(a,x,cl='b s')=>`<button class="${cl}" data-qa="${a}" data-q="${q.id}">${x}</button>`;
  const inp=v=>`<input type="date" data-qf="${q.id}" aria-label="Fecha quirúrgica" value="${v||''}"><input type="time" data-qh="${q.id}" aria-label="Hora" value="${q.hora||''}" style="width:auto;padding:3px 6px;font-size:.85rem">`;
  if(q.estado==='Pendiente de presentar')return b('pres','Presentado')+b('nul','Sin efecto','b r s');
  if(q.estado==='Presentado')return inp('')+b('fecha','Dar fecha')+b('nul','Sin efecto','b r s');
  if(q.estado==='Con fecha')return inp(q.fecha)+b('fecha','Reprogramar','b g s')+b('real','Realizado')+b('susp','Suspender','b g s')+b('nul','Sin efecto','b r s');
  if(q.estado==='Suspendido')return inp('')+b('fecha','Reprogramar')+b('nul','Sin efecto','b r s');return ''}
function moverOpts(){const s=$('mv-s').value,opts=freeFixed(s).map(c=>`<option value="F|${c}">${c}</option>`);if(SECN[s].virtual){$('mv-c').innerHTML='<option value="P|Camilla">Camilla de código rojo</option>';return}if(SECN[s].extra&&nextProv(s))opts.push('<option value="P|Camilla provisoria">Camilla provisoria</option>','<option value="P|Sofá">Sofá</option>');
  $('mv-c').innerHTML=opts.join('')||'<option value="">Sin lugar libre</option>'}
function resumen(p){const r=news2(p.vit),so=sofa(p),S=SECN[p.sector],a=aisl(p),tc=tercer(p),es=escara(p);
  const ep=p.est.filter(e=>ACT.includes(e.estado)).map(e=>e.nom+' ('+e.estado.toLowerCase()+(e.estado==='Programado'?' '+fi(e.fprog)+(e.hora?' '+e.hora:''):e.estado==='Enviado'?' '+fi(e.fenv||e.fsol):'')+')'),er=p.est.filter(e=>e.estado==='Realizado').map(e=>e.nom+(e.res?': '+e.res:''));
  const qx=p.qx.filter(q=>q.estado!=='Sin efecto').map(q=>q.nom+' - '+(q.estado==='Presentado'?'presentado, pendiente de fecha':q.estado.toLowerCase())+(q.fecha&&q.estado==='Con fecha'?' '+fi(q.fecha):''));
  const L=[`${p.nom}, ${p.edad} años${p.fnac?' (nac. '+fi(p.fnac)+')':''}, CI ${p.ci}${p.reg?', registro '+p.reg:''}`,`Ubicación: ${S.n}, ${p.cama} (${dur(NOW-p.ingreso)} en Urgencias)`,
   `Triage: ${p.tri}. NEWS2: ${r?r.s+' ('+r.txt+')':'sin dato'}${so?'. SOFA-2: '+so.s+(p.sofaPrev!==''?' (delta '+(so.s-p.sofaPrev>0?'+':'')+(so.s-p.sofaPrev)+')':''):''}${so&&so.r?'. SaFi '+Math.round(so.r.safi)+', PaFi estimada '+Math.round(so.r.pafi):''}`];
  if(p.sector==='rea'&&p.gas.ph!=='')L.push(`Gasometría: pH ${p.gas.ph}, PaCO2 ${p.gas.pco2}, HCO3 ${p.gas.hco3}. ${altaSala(p).ok?'Cumple criterios de alta a sala.':'No cumple criterios de alta a sala.'}`);
  L.push(`Motivo de consulta: ${p.motivo||'-'}`,`Diagnósticos: ${p.dx||'-'}`,`Plan: ${p.plan||'-'}`,`Estudios pendientes: ${ep.join(', ')||'ninguno'}`,`Estudios realizados: ${er.join('; ')||'ninguno'}`,
   `Procedimiento quirúrgico: ${qx.join('; ')||'no'}`,`Aislamiento: ${a?a.t:'no requiere'}`,`Escara: ${es?es.t:'no'}`,`Tercerización: ${tc.ok?'cumple el checklist ('+tc.dest+')':'no cumple el checklist'}`,`Destino propuesto: ${p.dest||'sin definir'}`);
  return L.join('\n')}
const critHTML=it=>`<ul class="crit">${it.map(([k,x])=>`<li><span class="${k}">${k==='y'?'Sí':k==='q'?'Ojo':'No'}</span><span>${esc(x)}</span></li>`).join('')}</ul>`;
function live(){const p=cur,r=news2(p.vit);
  $('f-news').innerHTML=r?`<div class="sug ${r.r}"><span class="score">${r.s}</span> NEWS2 - ${r.txt}</div>`:'<div class="sug m">Completá FR, SatO2, PAS, FC y temperatura para calcular el NEWS2.</div>';
  const so=sofa(p),rr=resp(p);
  $('f-resp').innerHTML=rr?`<div class="sug ${rr.sc>=3?'a':rr.sc>=1?'m':'b'}">FiO2 ${rr.f}% · SaFi ${Math.round(rr.safi)} · PaO2 estimada ${Math.round(rr.pao2)} mmHg · PaFi estimada ${Math.round(rr.pafi)} → ${rr.sc} punto${rr.sc!==1?'s':''}${rr.adv?'':' (sin soporte avanzado, máximo 2)'}</div>${rr.flag?'<p class="note">Con SpO2 de 97% o más la estimación pierde precisión: conviene bajar la FiO2 hasta SpO2 92 a 96% o usar gasometría.</p>':''}`:'<p class="note">Cargá la SatO2 (en NEWS2) y el soporte de oxígeno para calcular SaFi y PaFi estimada.</p>';
  let dl='';if(so&&p.sofaPrev!==''){const d=so.s-(+p.sofaPrev);dl=` · delta ${d>0?'+':''}${d} (${d<0?'en mejoría':d===0?'estable':'en empeoramiento'})`}
  $('f-sofa-r').innerHTML=so?`<div class="sug ${so.s>=8?'a':so.s>=2?'m':'b'}"><span class="score">${so.s}</span> SOFA-2${so.n<6?' parcial ('+so.n+' de 6 órganos)':''}${dl}</div>`:'<p class="note">Sin datos de SOFA-2.</p>';
  const a=aisl(p);$('f-ais').innerHTML=a?`<div class="sug ${a.k}">${a.t}</div>`:'<div class="sug b">No requiere aislamiento.</div>';
  const es=escara(p);$('f-esc').innerHTML=`<div class="sug ${es?(es.adq||es.prog?'a':'m'):'b'}">${es?es.t:'Sin escara al ingreso ni registrada en la evolución.'}</div>`;
  if($('f-alta')){const al=altaSala(p);$('f-alta').innerHTML=`<div class="sug ${al.ok?'b':'a'}">${al.ok?'Cumple criterios de alta a sala.':'No cumple criterios de alta a sala.'}</div>`+critHTML(al.it)}
  const tc=tercer(p),it=[];tc.auto.forEach(x=>it.push(['n','Detectado en la ficha: '+x]));tc.faltA.forEach(x=>it.push(['n','Falta criterio A: '+x]));if(!tc.perfil)it.push(['n','Falta elegir un perfil (B) o una opción del Sanatorio Español (D)']);tc.hayC.forEach(x=>it.push(['n','Excluyente: '+x]));
  $('f-terc').innerHTML=`<div class="sug ${tc.ok?'b':'m'}">${tc.ok?'Cumple el checklist: candidato a '+tc.dest+'.':'No cumple el checklist de tercerización.'}</div>${it.length?critHTML(it):''}`;
  const s=sugerencia(p);$('f-sug').innerHTML=`<div class="sug ${s.k}">${s.t}</div>`;
  $('f-res').textContent=resumen(p)}
function msgF(x,k){const m=$('f-msg');m.className='msg on '+k;m.textContent=x;m.scrollIntoView({block:'nearest'})}
async function copiar(txt,btn){try{await navigator.clipboard.writeText(txt)}catch(e){const t=document.createElement('textarea');t.value=txt;document.body.appendChild(t);t.select();try{document.execCommand('copy')}catch(_){}t.remove()}const o=btn.textContent;btn.textContent='Copiado';setTimeout(()=>btn.textContent=o,1500)}

$('md').addEventListener('input',e=>{const t=e.target;if(!cur)return;const p=cur;
  if(t.dataset.f){p[t.dataset.f]=t.value;if(t.dataset.f==='fnac'){p.edad=edadDe(t.value);$('f-edad').value=p.edad;$('h-edad').textContent=p.edad}if(t.dataset.f==='edad')$('h-edad').textContent=t.value;live()}
  else if(t.dataset.v){p.vit[t.dataset.v]=t.dataset.v==='o2'?!!t.value:t.value;live()}
  else if(t.dataset.vm){p.vm=p.vm||{};p.vm[t.dataset.vm]=t.value;live()}
  else if(t.dataset.r){p.resp[t.dataset.r]=t.value;if(t.dataset.r==='dev'){p.vit.o2=t.value!=='aire';const o=$('fv-o2');if(o)o.value=p.vit.o2?'1':'';respVis()}live()}
  else if(t.dataset.s){p.sof[t.dataset.s]=['delir','otro','mec','dial'].includes(t.dataset.s)?!!t.value:t.value;live()}
  else if(t.dataset.g){p.gas[t.dataset.g]=t.value;live()}
  else if(t.dataset.al){p.alt[t.dataset.al]=['o2Desc','postqx'].includes(t.dataset.al)?!!t.value:t.value;live()}
  else if(t.dataset.es){p.esc[t.dataset.es]=t.dataset.es==='ing'?!!t.value:t.value;live()}
  else if(t.dataset.a){p.ais[t.dataset.a]=t.value;if(t.dataset.a==='kpc'&&t.value==='Sospecha'&&!p.est.some(x=>/hisopado rectal/i.test(x.nom)&&x.estado!=='Sin efecto')){p.est.push(ES('Laboratorio especial','Hisopado rectal para EPC','Pendiente',HOY));renderFicha()}else live()}
  else if(t.dataset.res){const x=p.est.find(y=>y.id==t.dataset.res);if(x){x.res=t.value;live()}}
  else if(t.dataset.ta!=null){p.terc.a[+t.dataset.ta]=t.checked;live()}
  else if(t.dataset.tx!=null){p.terc.c[+t.dataset.tx]=t.checked;live()}
  else if(t.dataset.tdd!=null){p.terc.d[+t.dataset.tdd]=t.checked;live()}
  else if(t.hasAttribute('data-tp')){p.terc.perfil=t.value;live()}
  else if(t.hasAttribute('data-to')){p.terc.otro=t.value;live()}});
$('md').addEventListener('change',e=>{if(e.target.id==='mv-s')moverOpts()});
$('md').addEventListener('click',e=>{const t=e.target.closest('button');if(!t)return;
  if(t.hasAttribute('data-close')){cerrar();return}
  if(!cur)return;const p=cur,est=id=>p.est.find(x=>x.id==id);
  if(t.dataset.ea){const x=est(t.dataset.ea),f=document.querySelector(`[data-ed="${x.id}"]`).value,h=document.querySelector(`[data-eh="${x.id}"]`).value;if(!f){msgF('Elegí la fecha de programación.','err');return}
    if(x.tipo==='Imagen (MEPROTEC)'&&!h){msgF('Las imágenes de MEPROTEC necesitan la hora de agendamiento.','err');return}
    if(['Programado','Suspendido'].includes(x.estado))x.reag++;x.estado='Programado';x.fprog=f;x.hora=h;renderFicha();return}
  if(t.dataset.er){const x=est(t.dataset.er);x.estado='Realizado';x.freal=HOY;renderFicha();return}
  if(t.dataset.esu){const x=est(t.dataset.esu);x.estado='Suspendido';x.smot=prompt('Motivo de la suspensión (opcional)')||'';renderFicha();return}
  if(t.dataset.env){const x=est(t.dataset.env);x.estado='Enviado';x.fenv=HOY;renderFicha();return}
  if(t.dataset.ex){est(t.dataset.ex).estado='Sin efecto';renderFicha();return}
  if(t.id==='ne-ok'){const n=$('ne-n').value.trim();if(!n){msgF('Escribí el nombre del estudio.','err');return}const tp=$('ne-t').value,ext=EXT.includes(tp),ag=!ext&&$('ne-m').value==='Programado',fa=$('ne-fa').value,hh=$('ne-h').value;
    if(ag&&!fa){msgF('Indicá la fecha programada.','err');return}if(ag&&tp==='Imagen (MEPROTEC)'&&!hh){msgF('Las imágenes de MEPROTEC necesitan la hora de agendamiento.','err');return}
    const x=ES(tp,n,ext?'Pendiente de envío':ag?'Programado':'Pendiente de programación',$('ne-fs').value||HOY,ag?fa:'',ag?hh:'');x.ayuno=!ext&&$('ne-ay').checked;p.est.push(x);renderFicha();return}
  if(t.id==='ev-ok'){p.esc.evol.push({fecha:$('ev-f').value||HOY,loc:$('ev-l').value.trim(),grado:$('ev-g').value,nota:$('ev-n').value.trim()});renderFicha();return}
  if(t.id==='nq-ok'){const n=$('nq-n').value.trim();if(!n)return;p.qx.push({id:nid(),nom:n,serv:$('nq-s').value,estado:'Pendiente de presentar',fecha:''});renderFicha();return}
  if(t.dataset.qa){const q=p.qx.find(x=>x.id==t.dataset.q),a=t.dataset.qa;
    if(a==='pres'){q.estado='Presentado';q.fecha=''}
    if(a==='fecha'){const f=document.querySelector(`[data-qf="${q.id}"]`).value;if(!f){msgF('Elegí la fecha quirúrgica.','err');return}q.estado='Con fecha';q.fecha=f;q.hora=document.querySelector(`[data-qh="${q.id}"]`).value}
    if(a==='susp')q.estado='Suspendido';
    if(a==='real')q.estado='Realizado';if(a==='nul')q.estado='Sin efecto';renderFicha();return}
  if(t.id==='f-tras'){const h=$('h-tras');if(h){const d=h.closest('details');if(d)d.open=true;h.scrollIntoView({behavior:'smooth',block:'start'});setTimeout(()=>$('mv-s').focus(),400)}return}
  if(t.id==='vm-now'){p.vm=p.vm||{};p.vm.corr=dtl(NOW);regMov('Cambio de corrugado',p,p.cama,'');renderFicha();msgF('Cambio de corrugado registrado.','ok');return}
  if(t.id==='mv-ok'){const v=$('mv-c').value;if(!v){msgF('No hay lugar libre en ese sector.','err');return}const s=$('mv-s').value,[k,c]=v.split('|');
    const deC=p.cama;liberar(p);if(k==='F'){p.cama=c;p.tipoCama='Fija';delete bedSt[c]}else{p.cama=nextProv(s);p.tipoCama=c}p.sector=s;regMov('Movimiento interno',p,deC,p.cama);renderFicha();msgF('Paciente movido a '+SECN[s].n+', '+p.cama+'.','ok');return}
  if(t.id==='eg-ok'){const tp=$('eg-t').value,r=news2(p.vit),so=sofa(p);let dest=['Traslado a sala HEQI','Otra red IPS','Terciarizado'].includes(tp)?$('eg-s').value:'';if(dest.startsWith('Otro sanatorio')){dest=$('eg-o').value.trim();if(!dest){msgF('Indicá a qué sanatorio se terciariza.','err');return}}
    const aSala=['Traslado a sala HEQI','Otra red IPS','Externado a sala de menor complejidad','Terciarizado'].includes(tp);let aviso='';
    if(aSala&&p.sector==='rea'&&!altaSala(p).ok)aviso='No cumple criterios de alta a sala desde Reanimación.';
    else if(aSala&&r&&r.s>=5)aviso='NEWS2 de 5 o más: no candidato a sala.';
    else if(tp==='Terciarizado'&&!tercer(p).ok)aviso='No cumple el checklist de tercerización.';
    if(aviso&&!confEgr){confEgr=true;msgF(aviso+' Si igual querés registrarlo, tocá de nuevo "Registrar egreso".','err');return}
    const es=escara(p);
    regMov('Egreso: '+tp,p,p.cama,dest||tp);egresos.push({nom:p.nom,ci:p.ci,edad:p.edad,dx:p.dx,ingreso:p.ingreso,sector:p.sector,tipo:tp,dest,horas:(NOW-p.ingreso)/H,fecha:new Date(NOW),reg:true,news:r?r.s:null,sofa:so?so.s:null,gas:p.sector==='rea'&&p.gas.ph!==''?`pH ${p.gas.ph} / HCO3 ${p.gas.hco3}`:'',cond:aviso?'Egreso sin cumplir criterios: '+aviso:'Cumple criterios',ais:aisl(p)?aisl(p).chip[1]:'',esc:es?(es.adq?'escara adquirida':'escara al ingreso'):''});
    liberar(p);pac=pac.filter(x=>x.id!==p.id);cerrar();return}
  if(t.id==='f-copy')copiar(resumen(p),t)});
function cerrar(){$('ov').classList.remove('on');cur=null;renderAll()}
$('ov').addEventListener('click',e=>{if(e.target.id==='ov')cerrar()});
document.addEventListener('keydown',e=>{if(e.key==='Escape'&&$('ov').classList.contains('on'))cerrar()});
$('sectores').addEventListener('click',e=>{const b=e.target.closest('button');if(!b)return;
  if(b.dataset.open)abrirFicha(+b.dataset.open);if(b.dataset.new)abrirIngreso(b.dataset.new,b.dataset.cama);if(b.dataset.prov)abrirIngreso(b.dataset.prov,null)});

/* Consultorio amarillo */
let cv={fr:'',sat:'',o2:false,pas:'',fc:'',conc:'A',temp:''};
function renderCons(){$('c-vit').innerHTML=vitInputs('cv-',cv);consLive();
  $('c-body').innerHTML=consultas.slice().reverse().map(c=>`<tr><td>${c.hora}</td><td>${esc(c.nom)}</td><td>${esc(c.motivo)}</td><td>${c.news==null?'-':c.news}</td><td>${esc(c.dec)}</td></tr>`).join('')}
function consLive(){const r=news2(cv);$('c-news').innerHTML=r?`<div class="sug ${r.r}"><span class="score">${r.s}</span> NEWS2 - ${r.txt}. ${r.s>=5?'Probablemente requiere internación.':r.r==='m'?'Reevaluar antes de decidir.':'Probable tratamiento ambulatorio u observación corta.'}</div>`:'<p class="note">Cargá los signos vitales para calcular el NEWS2.</p>'}
$('c-vit').addEventListener('input',e=>{const k=e.target.dataset.v;if(!k)return;cv[k]=k==='o2'?!!e.target.value:e.target.value;consLive()});
function cmsg(x,k){$('c-msg').className='msg on '+k;$('c-msg').textContent=x}
function consBase(){const nom=$('c-nom').value.trim(),ci=$('c-ci').value.trim(),ed=$('c-edad').value;if(!nom||!ci||!ed){cmsg('Nombre, cédula y edad son obligatorios.','err');return null}return {nom,ci,edad:+ed,motivo:$('c-mot').value.trim(),plan:$('c-plan').value.trim()}}
function consFin(b,dec){const r=news2(cv);consultas.push({hora:two(NOW.getHours())+':'+two(NOW.getMinutes()),nom:b.nom,motivo:b.motivo,news:r?r.s:null,dec});
  ['c-nom','c-ci','c-edad','c-mot','c-plan'].forEach(i=>$(i).value='');cv={fr:'',sat:'',o2:false,pas:'',fc:'',conc:'A',temp:''};$('c-introw').style.display='none';renderCons();renderAll()}
function lugarSTC(){let c=freeFixed('stc')[0],tc='Fija';if(!c){c=nextProv('stc');tc='Camilla provisoria'}return c?[c,tc]:null}
const respDe=v=>({dev:v.o2?'cn':'aire',L:v.o2?2:'',fio2:''});
document.querySelectorAll('[data-c]').forEach(btn=>btn.onclick=()=>{const b=consBase();if(!b)return;const a=btn.dataset.c;
  if(a==='alta'){cmsg(b.nom+': alta con tratamiento ambulatorio.','ok');consFin(b,'Alta - tratamiento ambulatorio')}
  if(a==='obs'){const l=lugarSTC();if(!l){cmsg('Se alcanzó el máximo de lugares en sala de trabajo.','err');return}
    mk({...b,tri:'Amarillo',sector:'stc',cama:l[0],tipoCama:l[1],ingreso:new Date(NOW),vit:{...cv},resp:respDe(cv),dx:'En evaluación'});cmsg(b.nom+': queda en sala de trabajo, '+l[0]+(l[1]!=='Fija'?' ('+l[1]+')':'')+'.','ok');consFin(b,'Observación en sala de trabajo')}
  if(a==='int')$('c-introw').style.display='flex'});
$('c-intok').onclick=()=>{const b=consBase();if(!b)return;const s=$('c-sec').value,c=freeFixed(s)[0];
  if(!c){const l=lugarSTC();if(!l){cmsg('Sin lugar disponible.','err');return}mk({...b,tri:'Amarillo',sector:'stc',cama:l[0],tipoCama:l[1],ingreso:new Date(NOW),vit:{...cv},resp:respDe(cv),dx:'En evaluación',plan:b.plan+' - Pendiente cama en '+SECN[s].n});cmsg('Sin cama libre en '+SECN[s].n+'. Queda en sala de trabajo, '+l[0]+', pendiente de cama.','err');consFin(b,'Internación pendiente de cama ('+SECN[s].n+')');return}
  mk({...b,tri:'Amarillo',sector:s,cama:c,ingreso:new Date(NOW),vit:{...cv},resp:respDe(cv),dx:'En evaluación'});cmsg(b.nom+': internado en '+SECN[s].n+', '+c+'.','ok');consFin(b,'Internado en '+SECN[s].n)};

/* Derivación */
function renderDer(){const sel=$('d-serv'),cur2=sel.value,servs=[...new Set(pac.filter(p=>p.dest&&p.dest!=='Alta'&&p.dest!=='Queda en Urgencias').map(p=>p.dest))];
  sel.innerHTML='<option value="">Todos los servicios</option>'+DEST.filter(d=>d!=='Alta').map(d=>`<option ${d===cur2?'selected':''}>${d}</option>`).join('');
  const list=cur2?[cur2]:DEST.filter(d=>servs.includes(d));
  $('d-out').innerHTML=list.map(d=>{const l=pac.filter(p=>p.dest===d);if(!l.length)return `<div class="box"><h2>${d}</h2><p class="note">Sin pacientes con este destino.</p></div>`;
    const txt=`Urgencias HEQI - pacientes para ${d} - ${fdt(NOW)}\n`+l.map((p,i)=>{const r=news2(p.vit),a=aisl(p),es=escara(p);const so=sofa(p);return `${i+1}. ${p.nom}, ${p.edad} a, ${p.reg?'registro '+p.reg:'CI '+p.ci}, NEWS2 ${r?r.s:'s/d'}${so?', SOFA-2 '+so.s+(so.r?' (SaFi '+Math.round(so.r.safi)+')':''):''}, Dx: ${p.dx||'-'}. Ubicación: ${SECN[p.sector].n} ${p.cama}.${p.qx.some(q=>!['Realizado','Sin efecto'].includes(q.estado))?' Qx pendiente.':''}${a?' '+a.chip[1]+'.':''}${es?' '+(es.adq?'Escara adquirida':'Escara al ingreso')+'.':''}`}).join('\n');
    return `<div class="box"><div class="sec-head"><h2>${d}</h2><span class="note">${l.length} paciente${l.length>1?'s':''}</span></div><pre class="res">${esc(txt)}</pre><button class="b g s" data-copy="${encodeURIComponent(txt)}">Copiar para enviar</button></div>`}).join('')||'<div class="box"><p class="note">Ningún paciente tiene destino propuesto.</p></div>'}
$('d-serv').onchange=renderDer;
$('d-out').addEventListener('click',e=>{const b=e.target.closest('[data-copy]');if(b)copiar(decodeURIComponent(b.dataset.copy),b)});

/* Indicadores */
function renderInd(){const e30=egresos.filter(e=>NOW-e.fecha<=30*D),tot=SEC.reduce((a,s)=>a+s.fijas,0),mean=a=>a.length?a.reduce((x,y)=>x+y,0)/a.length:0,ob=e30.filter(e=>e.tipo==='Óbito').length;
  $('k-ind').innerHTML=[[pac.length,'Pacientes en Urgencias ahora'],[e30.length,'Egresos en 30 días'],[(e30.length/tot).toFixed(1),'Giro de cama global (30 días)'],[dur(mean(e30.map(e=>e.horas))*H),'Estadía media'],[(ob/e30.length*100).toFixed(1)+'%','Mortalidad en Urgencias']].map(([v,t])=>`<div class="kpi"><b>${v}</b><span>${t}</span></div>`).join('');
  $('i-occ').innerHTML=SEC.map(S=>{if(S.virtual)return `<div class="hb"><span>${S.n}</span><div class="note">espacio virtual</div><b>${occ(S.id).length}</b></div>`;const l=occ(S.id),fo=l.filter(p=>p.tipoCama==='Fija').length,pr=l.length-fo;return `<div class="hb"><span>${S.n}</span><div class="bar"><i style="width:${Math.min(100,fo/S.fijas*100)}%;${fo>=S.fijas?'background:var(--bad)':''}"></i></div><b>${fo}/${S.fijas}${pr?' +'+pr:''}</b></div>`}).join('');
  const g={b:0,m:0,a:0,n:0};pac.forEach(p=>{const r=news2(p.vit);if(!r)g.n++;else g[r.s>=7?'a':r.s>=5?'m':'b']++});const gm=Math.max(1,...Object.values(g));
  $('i-grav').innerHTML=[['b','Bajo (0 a 4)','var(--ok)'],['m','Medio (5 a 6)','var(--warn)'],['a','Alto (7 o más)','var(--bad)'],['n','Sin dato','var(--muted)']].map(([k,t,c])=>`<div class="hb"><span>${t}</span><div class="bar"><i style="width:${g[k]/gm*100}%;background:${c}"></i></div><b>${g[k]}</b></div>`).join('');
  const sr=occ('rea').map(p=>sofa(p)).filter(Boolean),ap=occ('rea').filter(p=>altaSala(p).ok).length;$('i-sofa').textContent=sr.length?`Reanimación: SOFA-2 promedio ${mean(sr.map(x=>x.s)).toFixed(1)}; ${ap} de ${occ('rea').length} pacientes cumplen criterios de alta a sala.`:'';
  const byT={};e30.forEach(e=>{const k=e.tipo==='Traslado a sala HEQI'?'Sala de '+e.dest:e.dest?e.tipo+': '+e.dest:e.tipo;byT[k]=(byT[k]||0)+1});const tm=Math.max(...Object.values(byT));
  $('i-egr').innerHTML=Object.entries(byT).sort((a,b)=>b[1]-a[1]).map(([k,v])=>`<div class="hb"><span>${k}</span><div class="bar"><i style="width:${v/tm*100}%"></i></div><b>${v}</b></div>`).join('');
  $('i-giro').innerHTML=SEC.map(S=>{const l=e30.filter(e=>e.sector===S.id);return `<tr><td>${S.n}</td><td>${l.length}</td><td>${S.virtual?'-':(l.length/S.fijas).toFixed(1)}</td><td>${dur(mean(l.map(e=>e.horas))*H)}</td></tr>`}).join('');
  const hoy=egresos.filter(e=>e.reg);$('i-cond').innerHTML=hoy.length?hoy.slice().reverse().map(e=>`<tr><td>${esc(e.nom)}</td><td>${SECN[e.sector].n}</td><td>${e.tipo}${e.dest?' - '+e.dest:''}</td><td>NEWS2 ${e.news??'s/d'}${e.sofa!=null?' · SOFA-2 '+e.sofa:''}${e.gas?' · '+e.gas:''}${e.ais?' · '+esc(e.ais):''}${e.esc?' · '+e.esc:''}</td><td><span class="chip ${e.cond==='Cumple criterios'?'ok':'bd'}">${esc(e.cond)}</span></td></tr>`).join(''):'<tr><td colspan="5" class="note">Todavía no se registraron egresos en esta sesión.</td></tr>'}

/* Pizarra de camas */
const PZ={Libre:'pz-libre',Ocupada:'pz-ocu',Reservada:'pz-res','Alta probable':'pz-alta',Sucia:'pz-sucia','En limpieza':'pz-limp',Bloqueada:'pz-bloq',Contaminada:'pz-cont',Aislamiento:'pz-cont'};
function tileInfo(c){const p=pac.find(x=>x.cama===c);if(p){const a=aisl(p);if(p.altaProb)return {st:'Alta probable',det:esc(p.nom)+'<br>alta '+p.altaProb.toLowerCase(),p};if(a&&a.k==='a')return {st:'Aislamiento',lab:'OCUPADA - AISLAMIENTO',det:esc(p.nom),p};return {st:'Ocupada',det:esc(p.nom),p}}
  const b=bedSt[c];if(b&&b.st!=='Libre'){const dB=b.st==='Bloqueada'&&b.desde?Math.floor(Math.max(0,Date.now()-new Date(b.desde))/D):null;return {st:b.st,det:esc(b.nota||'')+(b.ticket?'<br>Reclamo '+esc(b.ticket):'')+(b.aviso?' ('+esc(b.aviso)+')':'')+(dB!==null?`<br><b style="color:${dB>=7?'#b03a2e':dB>=2?'#9a6200':'inherit'}">${dB} día(s) bloqueada</b>`:'')+(b.hora?'<br>'+b.hora:'')}}return {st:'Libre',det:''}}
function tile(c,prov){const t=tileInfo(c);const tri=t.p?`<span class="dot" style="background:${TRIC[t.p.tri]}"></span>`:'';
  return `<button class="tile ${PZ[t.st]}${prov?' prov-t':''}" data-tile="${c}"><span class="lb"><b>${tri}${c}${prov&&t.p.tipoCama!=='Camilla'?' ('+t.p.tipoCama.toLowerCase()+')':''}</b><br>${t.lab||t.st.toUpperCase()}${t.det?'<br><span class="det">'+t.det+'</span>':''}</span></button>`}
function renderPiz(){const cnt={};let html='';
  SEC.forEach(S=>{if(S.virtual){const l=occ(S.id);html+=`<div class="box"><div class="sec-head"><h2>${S.n}</h2><span class="note"><b>${l.length?l.length+' camilla'+(l.length>1?'s':'')+' en uso':'Sin código rojo'}</b> · espacio virtual, no se oferta</span></div><div class="pz">${l.map(p=>tile(p.cama,true)).join('')}<button class="tile pz-libre" style="border-style:dashed" data-crnew><span class="lb">+ Ingresar código rojo</span></button></div></div>`;return}
    const c2={};let tiles='';for(let i=1;i<=S.fijas;i++){const c=S.pref+' '+i,st=tileInfo(c).st;c2[st]=(c2[st]||0)+1;cnt[st]=(cnt[st]||0)+1;tiles+=tile(c)}
    occ(S.id).filter(p=>p.tipoCama!=='Fija').forEach(p=>tiles+=tile(p.cama,true));const pr=occ(S.id).filter(p=>p.tipoCama!=='Fija').length;
    const w=espera.filter(e=>e.sector===S.id).length;
    html+=`<div class="box"><div class="sec-head"><h2>${S.n}</h2><span class="note">${Object.entries(c2).map(([k,v])=>v+' '+k.toLowerCase()).join(' · ')}${pr?' · '+pr+' provisorias':''}${w?' · <b style="color:var(--bad)">'+w+' esperando cama</b>':''}</span></div><div class="pz">${tiles}</div></div>`});
  const ocu=(cnt['Ocupada']||0)+(cnt['Alta probable']||0)+(cnt['Aislamiento']||0);
  $('k-piz').innerHTML=[[cnt['Libre']||0,'Camas libres'],[ocu,'Ocupadas'],[cnt['Reservada']||0,'Reservadas'],[(cnt['Sucia']||0)+(cnt['En limpieza']||0)+(cnt['Contaminada']||0),'Sucias o en limpieza'],[cnt['Bloqueada']||0,'Bloqueadas'],[espera.length,'Pacientes esperando cama']].map(([v,t],i)=>`<div class="kpi"${i===5&&v?' style="border-color:var(--bad)"':''}><b${i===5&&v?' style="color:var(--bad)"':''}>${v}</b><span>${t}</span></div>`).join('');
  $('pizarra').innerHTML=html;
  $('pz-leg').innerHTML=['Libre','Ocupada','Reservada','Alta probable','Sucia','En limpieza','Bloqueada','Contaminada'].map(s=>`<span><i class="sw ${PZ[s]}"></i>${s}</span>`).join('')}
$('pizarra').addEventListener('click',e=>{if(e.target.closest('[data-crnew]')){abrirIngreso('cr',null);return}const b=e.target.closest('[data-tile]');if(!b)return;const c=b.dataset.tile,t=tileInfo(c);if(t.p){abrirFicha(t.p.id);return}abrirCama(c)});
function abrirCama(c){const s=SEC.find(S=>c.startsWith(S.pref+' ')).id,b=bedSt[c]||{st:'Libre',nota:''},w=espera.filter(e=>e.sector===s);
  $('md').innerHTML=`<div class="md-h"><div><h2>${c}</h2><span class="note">${SECN[s].n} · estado actual: ${b.st}${b.nota?' - '+esc(b.nota):''}${b.hora?' '+b.hora:''}</span></div><button class="b g s" data-close>Cerrar</button></div>
  <h3>Cambiar estado</h3>${s==='rea'?'':'<p class="note">Solo las camas de Reanimación se reservan. '+(s==='cr'?'Código rojo es demanda espontánea de los que llegan graves.':'')+'</p>'}<div class="acts">${BEDST.filter(x=>x!=='Reservada'||s==='rea').map(x=>`<button class="b ${x===b.st?'':'g'} s" data-bst="${x}">${x}</button>`).join('')}</div>
  <div class="row"><div><label for="bs-n">Detalle (para quién se reserva, motivo del bloqueo)</label><input id="bs-n" value="${esc(b.nota||'')}" placeholder="Ej. TCE grave derivado de Ciudad del Este"></div><div style="flex:0 1 120px"><label for="bs-h">Hora</label><input id="bs-h" type="time" value="${b.hora||''}"></div></div>
  <div class="row"><div><label for="bs-t">N.° de reclamo / ticket (obligatorio si se bloquea)</label><input id="bs-t" value="${esc(b.ticket||'')}" placeholder="Ej. SOL-2026-1184"></div>
    <div><label for="bs-a">Se avisó a (obligatorio si se bloquea)</label><select id="bs-a"><option value="">Elegir…</option>${['Mantenimiento','Biomédica','Patrimonio','Limpieza','Informática','Enfermería','Dirección','Otro'].map(x=>`<option ${b.aviso===x?'selected':''}>${x}</option>`).join('')}</select></div></div>
  <div class="row"><div><label for="bs-r">Estado del reclamo</label><select id="bs-r">${['Abierto','En proceso','Reiterado'].map(x=>`<option ${b.estRec===x?'selected':''}>${x}</option>`).join('')}</select></div>
    <div><label>Bloqueada desde</label><input disabled value="${b.st==='Bloqueada'&&b.desde?fdt(new Date(b.desde)):'-'}"></div></div><div class="msg" id="bs-msg"></div>
  ${w.length&&s==='rea'?`<label for="bs-e">Reservar para un paciente en espera</label><select id="bs-e"><option value="">-</option>${w.map(e=>`<option value="${e.id}" ${b.espId===e.id?'selected':''}>${esc(e.nom)} - ${esc(e.lugar||e.origen)}</option>`).join('')}</select>`:''}
  <h3>Ingresar paciente</h3><div class="acts"><button class="b" data-bing>Paciente nuevo</button>${w.map(e=>`<button class="b g s" data-bespe="${e.id}">${esc(e.nom)} (en espera)</button>`).join('')}</div>`;
  $('ov').classList.add('on');
  $('md').onclick=null;
  $('md').querySelectorAll('[data-bst]').forEach(x=>x.onclick=()=>{const st=x.dataset.bst;let nota=$('bs-n').value.trim(),espId=null;const se=$('bs-e');if(st==='Reservada'&&se&&se.value){espId=+se.value;const e=espera.find(y=>y.id===espId);if(!nota)nota=e.nom+' - '+(e.lugar||e.origen)}
    const tk=$('bs-t').value.trim(),av=$('bs-a').value;if(st==='Bloqueada'&&(!tk||!av||!nota)){$('bs-msg').className='msg on err';$('bs-msg').textContent='Para bloquear la cama cargá el motivo (detalle), a quién se avisó y el número de reclamo.';return}
    const prev=bedSt[c]||{};regMov('Cama: '+st+(st==='Bloqueada'?' ('+nota+')':''),null,c,st==='Bloqueada'?('Aviso a '+av+', reclamo '+tk):'');
    if(st==='Libre')delete bedSt[c];else bedSt[c]={st,nota,hora:$('bs-h').value,espId,ticket:tk,aviso:av,estRec:$('bs-r').value,desde:st==='Bloqueada'?(prev.st==='Bloqueada'&&prev.desde?prev.desde:new Date().toISOString()):''};cerrar()});
  $('md').querySelector('[data-bing]').onclick=()=>abrirIngreso(s,c);
  $('md').querySelectorAll('[data-bespe]').forEach(x=>x.onclick=()=>ingresarDesdeEspera(+x.dataset.bespe,c))}
function ingresarDesdeEspera(id,cama){const e=espera.find(x=>x.id===id);if(!e)return;abrirIngreso(e.sector,cama);window._espId=id;
  $('i-nom').value=e.nom;$('i-ci').value=e.ci;$('i-edad').value=e.edad;$('i-mot').value=e.motivo;const r=document.querySelector(`input[name=i-tri][value="${e.tri}"]`);if(r)r.checked=true}

/* Pacientes esperando cama */
function renderEsp(){const l=espera.slice().sort((a,b)=>a.sol-b.sol);
  $('k-esp').innerHTML=[[espera.length,'Pacientes esperando cama'],[l.length?dur(NOW-l[0].sol):'-','Mayor tiempo de espera'],[espera.filter(e=>e.origen==='Derivado externo').length,'Derivados de otros centros'],[espBajas.length,'Salieron de la lista sin cama']].map(([v,t])=>`<div class="kpi"><b>${v}</b><span>${t}</span></div>`).join('');
  $('esp-body').innerHTML=l.map(e=>{const res=Object.entries(bedSt).find(([c,b])=>b.st==='Reservada'&&b.espId===e.id);const h=(NOW-e.sol)/H;
    const libres=freeFixed(e.sector);const opts=(res?[res[0]]:[]).concat(libres).map(c=>`<option>${c}</option>`).join('')+(SECN[e.sector].extra&&nextProv(e.sector)?'<option value="__prov">Camilla provisoria o sofá</option>':'');
    return `<li style="display:block"><div style="display:flex;justify-content:space-between;gap:8px;flex-wrap:wrap"><span><span class="dot" style="background:${TRIC[e.tri]}"></span><b>${esc(e.nom)}</b>, ${e.edad} a · CI ${esc(e.ci)}<br><span class="note">${esc(e.motivo)}</span><br><span class="note">Necesita: <b>${SECN[e.sector].n}</b> · ${esc(e.origen)}${e.lugar?' - '+esc(e.lugar):''}</span></span><span class="chip ${h>=4?'bd':'w'}">Espera ${dur(NOW-e.sol)}</span></div>
    ${res?`<span class="chip i">Cama reservada: ${res[0]}</span>`:''}
    <div class="acts" style="margin-top:6px">${opts?`<select data-asel="${e.id}" style="width:auto">${opts}</select><button class="b s" data-asig="${e.id}">Asignar cama</button>`:'<span class="chip bd">Sin cama libre en el sector</span>'}${!res&&libres.length&&e.sector==='rea'?`<button class="b g s" data-resv="${e.id}">Reservar ${libres[0]}</button>`:''}<select data-bmot="${e.id}" style="width:auto"><option value="">Sale de la lista por...</option>${['Se retiró','Derivado a otro centro','Ya no requiere cama','Falleció'].map(x=>`<option>${x}</option>`).join('')}</select><button class="b r s" data-baja="${e.id}">Quitar</button></div></li>`}).join('')||'<li class="note">No hay pacientes esperando cama.</li>'}
$('esp-body').addEventListener('click',ev=>{const t=ev.target.closest('button');if(!t)return;
  if(t.dataset.asig){const id=+t.dataset.asig,e=espera.find(x=>x.id===id),v=document.querySelector(`[data-asel="${id}"]`).value;ingresarDesdeEspera(id,v==='__prov'?null:v)}
  if(t.dataset.resv){const id=+t.dataset.resv,e=espera.find(x=>x.id===id),c=freeFixed(e.sector)[0];if(c){bedSt[c]={st:'Reservada',nota:e.nom+' - '+(e.lugar||e.origen),hora:two(NOW.getHours())+':'+two(NOW.getMinutes()),espId:id};renderAll()}}
  if(t.dataset.baja){const id=+t.dataset.baja,m=document.querySelector(`[data-bmot="${id}"]`).value;if(!m){alert('Elegí por qué sale de la lista.');return}
    espBajas.push({...espera.find(x=>x.id===id),motivoBaja:m});Object.keys(bedSt).forEach(c=>{if(bedSt[c].espId===id)delete bedSt[c]});espera=espera.filter(x=>x.id!==id);renderAll()}});
$('esp-ok').onclick=()=>{const nom=$('e-nom').value.trim(),ci=$('e-ci').value.trim(),ed=$('e-edad').value;if(!nom||!ci||!ed){$('esp-msg').className='msg on err';$('esp-msg').textContent='Nombre, cédula y edad son obligatorios.';return}
  espera.push({id:nid(),nom,ci,edad:+ed,tri:$('e-tri').value,motivo:$('e-mot').value.trim(),sector:$('e-sec').value,origen:$('e-ori').value,lugar:$('e-lug').value.trim(),sol:new Date(NOW)});
  ['e-nom','e-ci','e-edad','e-mot','e-lug'].forEach(i=>$(i).value='');$('esp-msg').className='msg on ok';$('esp-msg').textContent='Paciente agregado a la lista de espera de cama.';renderAll()};

/* Informe general y registro de movilización */
function periodo(){const d=+($('inf-p')?$('inf-p').value:30);return {d,ini:new Date(+NOW-d*D)}}
function datosInforme(){const {d,ini}=periodo(),E=egresos.filter(e=>e.fecha>=ini),ov=(a,b)=>Math.max(0,(Math.min(+b,+NOW)-Math.max(+a,+ini))/H);
  const sec=SEC.map(S=>{const l=E.filter(e=>e.sector===S.id),hp=l.reduce((a,e)=>a+ov(e.ingreso,e.fecha),0)+occ(S.id).filter(p=>p.tipoCama==='Fija').reduce((a,p)=>a+ov(p.ingreso,NOW),0);
    const cd=S.fijas*d*24;return {n:S.n,virtual:S.virtual,camas:S.fijas,egr:l.length,hp,ocup:S.virtual?null:hp/cd*100,est:l.length?l.reduce((a,e)=>a+e.horas,0)/l.length:0,giro:S.virtual?null:l.length/S.fijas,isus:S.virtual||!l.length?null:Math.max(0,cd-hp)/l.length,ob:l.filter(e=>e.tipo==='Óbito').length}});
  const dest={};E.forEach(e=>{const k=e.tipo+(e.dest?' - '+e.dest:'');dest[k]=(dest[k]||0)+1});
  return {d,ini,E,sec,dest}}
function renderInforme(){const I=datosInforme(),tot=I.E.length;
  $('inf-sec').innerHTML=I.sec.map(s=>`<tr><td>${s.n}</td><td>${s.virtual?'virtual':s.camas}</td><td><b style="color:${s.ocup>100?'var(--bad)':'inherit'}">${s.virtual?'-':s.ocup.toFixed(0)+'%'}</b></td><td>${dur(s.est*H)}</td><td>${s.virtual?'-':s.giro.toFixed(1)}</td><td>${s.egr}</td><td>${s.ob}</td></tr>`).join('');
  $('inf-dest').innerHTML=Object.entries(I.dest).sort((a,b)=>b[1]-a[1]).map(([k,v])=>`<tr><td>${esc(k)}</td><td>${v}</td><td>${(v/tot*100).toFixed(1)}%</td></tr>`).join('');
  const l=I.E.slice().sort((a,b)=>b.fecha-a.fecha);
  $('inf-reg').innerHTML=l.slice(0,60).map(e=>`<tr><td>${fdt(e.fecha)}</td><td>${esc(e.nom)}<br><span class="note">CI ${esc(e.ci)} · ${e.edad} a</span></td><td>${SECN[e.sector].n}</td><td>${fdt(e.ingreso)}</td><td>${dur(e.horas*H)}</td><td>${esc(e.tipo)}${e.dest?'<br><span class="note">'+esc(e.dest)+'</span>':''}</td><td>${esc(e.dx||'')}</td></tr>`).join('');
  $('inf-n').textContent=`${tot} egresos en ${I.d} días. Se muestran los 60 más recientes; el archivo descargado trae todos.`}
function csv(){const I=datosInforme(),q=x=>'"'+String(x??'').replace(/"/g,'""')+'"';
  const rows=[['Fecha de egreso','Paciente','Cédula','Edad','Sector','Fecha de ingreso','Horas en Urgencias','Tipo de egreso','Destino','Diagnóstico']].concat(I.E.slice().sort((a,b)=>a.fecha-b.fecha).map(e=>[fdt(e.fecha),e.nom,e.ci,e.edad,SECN[e.sector].n,fdt(e.ingreso),e.horas.toFixed(1),e.tipo,e.dest,e.dx]));
  const blob=new Blob(['\ufeff'+rows.map(r=>r.map(q).join(';')).join('\n')],{type:'text/csv;charset=utf-8'}),a=document.createElement('a');a.href=URL.createObjectURL(blob);a.download=`movilizacion_urgencias_HEQI_${HOY}.csv`;document.body.appendChild(a);a.click();a.remove()}
function imprimir(){const I=datosInforme(),tot=I.E.length,w=window.open('','_blank');if(!w){alert('El navegador bloqueó la ventana de impresión.');return}
  w.document.write(`<html><head><meta charset="utf-8"><title>Informe Urgencias HEQI</title><link rel="icon" type="image/png" href="/icon/fav-48.png"><link rel="apple-touch-icon" href="/apple-touch-icon.png"><link rel="manifest" href="/manifest.webmanifest"><meta name="theme-color" content="#1d4a42"><meta name="apple-mobile-web-app-capable" content="yes"><meta name="mobile-web-app-capable" content="yes"><meta name="apple-mobile-web-app-title" content="HEQI"><style>body{font-family:Arial,sans-serif;font-size:12px;margin:24px}h1{font-size:16px}h2{font-size:14px;margin-top:18px}table{border-collapse:collapse;width:100%}th,td{border:1px solid #999;padding:4px 6px;text-align:left}th{background:#eee}</style></head><body>
  <h1>Urgencias Polivalentes y Reanimación - HEQI</h1><p>Informe general de los últimos ${I.d} días (${fdate(I.ini)} al ${fdate(NOW)}). Comando de Camas - Urgencias HEQI.</p>
  <h2>Ocupación, estadía media y giro de cama</h2><table><tr><th>Sector</th><th>Camas</th><th>Ocupación</th><th>Estadía media</th><th>Giro de cama</th><th>Egresos</th><th>Óbitos</th></tr>${I.sec.map(s=>`<tr><td>${s.n}</td><td>${s.virtual?'virtual':s.camas}</td><td>${s.virtual?'-':s.ocup.toFixed(0)+'%'}</td><td>${dur(s.est*H)}</td><td>${s.virtual?'-':s.giro.toFixed(1)}</td><td>${s.egr}</td><td>${s.ob}</td></tr>`).join('')}</table>
  <h2>Lugares de externación</h2><table><tr><th>Destino</th><th>Pacientes</th><th>%</th></tr>${Object.entries(I.dest).sort((a,b)=>b[1]-a[1]).map(([k,v])=>`<tr><td>${k}</td><td>${v}</td><td>${(v/tot*100).toFixed(1)}%</td></tr>`).join('')}</table>
  <p style="margin-top:30px">Firma y sello: ______________________</p></body></html>`);w.document.close();w.focus();w.print()}

/* Censo diario */
let censos=[];
(function(){for(let d=30;d>=1;d--){const f=new Date(NOW-d*D);const oc={rea:6+Math.floor(rnd()*3),obs:8+Math.floor(rnd()*3),ec:3+Math.floor(rnd()*3),cr:Math.floor(rnd()*4),stc:5+Math.floor(rnd()*10)};
  censos.push({fecha:iso(f),oc,total:Object.values(oc).reduce((a,b)=>a+b,0),espera:Math.floor(rnd()*4),consultas:330+Math.floor(rnd()*170)})}})();
function censoHoy(){const oc={};SEC.forEach(S=>oc[S.id]=occ(S.id).length);return {fecha:HOY,oc,total:pac.length,espera:espera.length,consultas:consData.filter(c=>c.fecha===HOY).length||null}}
function guardarCenso(){const c=censoHoy();censos=censos.filter(x=>x.fecha!==HOY);censos.push(c);renderCenso();alert('Censo del '+fi(HOY)+' guardado. En la aplicación real esto se hace solo a la hora de cierre de guardia.')}
function renderCenso(){const l=censos.slice(-14),mx=Math.max(...l.map(c=>c.total),1);
  $('cen-body').innerHTML=l.slice().reverse().map(c=>`<tr><td>${fi(c.fecha)}</td>${SEC.map(S=>`<td>${c.oc[S.id]}</td>`).join('')}<td><b>${c.total}</b></td><td>${c.espera}</td><td>${c.consultas??'-'}</td></tr>`).join('');
  $('cen-bar').innerHTML=l.map(c=>`<div class="hb"><span>${fi(c.fecha).slice(0,5)}</span><div class="bar"><i style="width:${c.total/mx*100}%"></i></div><b>${c.total}</b></div>`).join('')}

/* Contingencia: desastres y múltiples víctimas */
let recursos=[{n:'Camillas plegables de reserva',c:6},{n:'Sillas de ruedas',c:4},{n:'Ventiladores de transporte',c:2},{n:'Monitores portátiles',c:3}],victimas={Rojo:0,Amarillo:0,Verde:0,Negro:0};
function capacidad(){const libres={};['rea','obs','ec','stc'].forEach(s=>libres[s]=freeFixed(s).length);
  const liberables=pac.filter(p=>p.sector!=='rea'&&(p.altaProb||tercer(p).ok||(news2(p.vit)&&news2(p.vit).s<5&&p.dest))).length;
  const reaLib=occ('rea').filter(p=>altaSala(p).ok).length;
  const stcExtra=SECN.stc.extra-occ('stc').filter(p=>p.tipoCama!=='Fija').length;
  const rec=recursos.reduce((a,r)=>a+(/camilla|silla/i.test(r.n)?+r.c:0),0);
  return {libres,liberables,reaLib,stcExtra,rec,rojo:libres.rea+reaLib,amarillo:libres.obs+libres.ec+libres.stc+liberables,verde:stcExtra+rec}}
function renderCont(){const k=capacidad();
  $('ct-k').innerHTML=[[k.libres.rea,'Camas libres en Reanimación'],[k.reaLib,'De Reanimación que pueden pasar a sala'],[k.libres.obs+k.libres.ec,'Camas libres en Polivalentes'],[k.liberables,'Pacientes que pueden liberar cama (alta, sala o tercerizar)'],[k.stcExtra,'Sofás o camillas provisorias disponibles'],[k.rec,'Camillas y sillas de reserva']].map(([v,t])=>`<div class="kpi"><b>${v}</b><span>${t}</span></div>`).join('');
  $('ct-rec').innerHTML=recursos.map((r,i)=>`<li><span>${esc(r.n)}</span><span class="acts"><button class="b g s" data-rm="${i}" aria-label="Restar">-</button><b style="min-width:28px;text-align:center">${r.c}</b><button class="b g s" data-rp="${i}" aria-label="Sumar">+</button><button class="b r s" data-rx="${i}">Quitar</button></span></li>`).join('');
  $('ct-vic').innerHTML=Object.keys(victimas).map(c=>`<div class="kpi" style="border-left:6px solid ${c==='Negro'?'#222':TRIC[c]}"><span>${c}</span><div class="acts" style="margin-top:4px"><button class="b g s" data-vm="${c}">-</button><b style="font-size:1.4rem;min-width:34px;text-align:center">${victimas[c]}</b><button class="b g s" data-vp="${c}">+</button></div></div>`).join('');
  const it=[['Rojo',victimas.Rojo,k.rojo,'camas de Reanimación libres o liberables'],['Amarillo',victimas.Amarillo,k.amarillo,'camas de Polivalentes y Sala de trabajo, más las liberables'],['Verde',victimas.Verde,k.verde,'sofás, camillas provisorias y de reserva']];
  $('ct-res').innerHTML=critHTML(it.map(([c,v,cap,t])=>[v<=cap?'y':'n',`${c}: ${v} víctimas para ${cap} lugares (${t})${v>cap?' - faltan '+(v-cap)+', activar derivación o expansión':''}`]))+(victimas.Rojo>0?'<p class="note">Los rojos ingresan a Código rojo sin límite (espacio virtual) mientras se les busca cama.</p>':'')}
$('p-cont').addEventListener('click',e=>{const b=e.target.closest('button');if(!b)return;const d=b.dataset;
  if(d.rm)recursos[+d.rm].c=Math.max(0,recursos[+d.rm].c-1);if(d.rp)recursos[+d.rp].c++;if(d.rx)recursos.splice(+d.rx,1);
  if(d.vm)victimas[d.vm]=Math.max(0,victimas[d.vm]-1);if(d.vp)victimas[d.vp]++;
  if(b.id==='ct-add'){const n=$('ct-n').value.trim(),c=+$('ct-c').value||0;if(n){recursos.push({n,c});$('ct-n').value='';$('ct-c').value=''}}
  if(b.id==='ct-reset')Object.keys(victimas).forEach(k=>victimas[k]=0);renderCont()});

/* Consultas del día (importadas del SIH u otro sistema) */
let consData=[];const COLORES=['Rojo','Naranja','Amarillo','Verde','Azul'];
const RANGOS=[[0,14,'0 a 14'],[15,29,'15 a 29'],[30,44,'30 a 44'],[45,59,'45 a 59'],[60,74,'60 a 74'],[75,200,'75 o más']];
const rango=e=>{const r=RANGOS.find(([a,b])=>e>=a&&e<=b);return r?r[2]:'Sin dato'};
function normColor(x){x=String(x||'').toLowerCase();return COLORES.find(c=>x.includes(c.toLowerCase()))||(x.includes('1')?'Rojo':x.includes('2')?'Naranja':x.includes('3')?'Amarillo':x.includes('4')?'Verde':x.includes('5')?'Azul':'Sin clasificar')}
function normFecha(x){x=String(x||'').trim();let m=x.match(/(\d{1,2})[\/\-.](\d{1,2})[\/\-.](\d{4})/);if(m)return m[3]+'-'+two(+m[2])+'-'+two(+m[1]);m=x.match(/(\d{4})-(\d{2})-(\d{2})/);if(m)return m[0];if(typeof x==='number'||/^\d{5}$/.test(x)){const d=new Date(Math.round((+x-25569)*864e5));return iso(new Date(d.getTime()+d.getTimezoneOffset()*6e4))}return HOY}
function cargarFilas(rows){if(!rows.length)return 0;const h=rows[0].map(x=>String(x).toLowerCase());const ix=k=>h.findIndex(x=>k.some(y=>x.includes(y)));
  const iE=ix(['edad']),iC=ix(['prioridad','color','clasif','nivel','triage']),iF=ix(['fecha']),iS=ix(['especialidad','servicio']),iT=ix(['situaci','estado']);
  if(iE<0||iC<0){$('cs-msg').className='msg on err';$('cs-msg').textContent='No encontré las columnas de edad y prioridad (color). Revisá que el archivo tenga encabezados.';return 0}
  const out=rows.slice(1).filter(r=>r.length>1).map(r=>({edad:+String(r[iE]).replace(/\D/g,'')||null,color:normColor(r[iC]),fecha:iF>=0?normFecha(r[iF]):HOY,esp:iS>=0?String(r[iS]):'',sit:iT>=0?String(r[iT]):''}));
  consData=consData.concat(out);return out.length}
function parseCSV(t){const sep=(t.split('\n')[0].match(/;/g)||[]).length>(t.split('\n')[0].match(/,/g)||[]).length?';':',';return t.split(/\r?\n/).filter(l=>l.trim()).map(l=>{const r=[];let c='',q=false;for(const ch of l){if(ch==='"')q=!q;else if(ch===sep&&!q){r.push(c);c=''}else c+=ch}r.push(c);return r.map(x=>x.trim())})}
$('cs-file').onchange=async e=>{const f=e.target.files[0];if(!f)return;let n=0;
  try{if(/\.xlsx?$/i.test(f.name)){if(!window.XLSX){$('cs-msg').className='msg on err';$('cs-msg').textContent='Para leer Excel hace falta conexión a internet. Guardalo como CSV y cargalo de nuevo.';return}
      const wb=XLSX.read(await f.arrayBuffer(),{type:'array'});n=cargarFilas(XLSX.utils.sheet_to_json(wb.Sheets[wb.SheetNames[0]],{header:1,raw:false}))}
    else n=cargarFilas(parseCSV(await f.text()))}catch(err){$('cs-msg').className='msg on err';$('cs-msg').textContent='No se pudo leer el archivo.';return}
  if(n){$('cs-msg').className='msg on ok';$('cs-msg').textContent=`Se cargaron ${n} consultas de ${f.name}.`}renderConsultas();e.target.value=''};
$('cs-demo').onclick=()=>{const P=[['Azul',.47,31.7],['Verde',.44,47],['Amarillo',.065,58.3],['Naranja',.02,62.5],['Rojo',.005,66.7]];
  for(let i=0;i<412;i++){let r=rnd(),acc=0,c=P[0];for(const p of P){acc+=p[1];if(r<acc){c=p;break}}const e=Math.max(0,Math.round(c[2]+(rnd()+rnd()+rnd()-1.5)*28));
    consData.push({edad:e,color:c[0],fecha:HOY,esp:e<15?'URGENCIAS PEDIATRICAS':pick(['URGENCIAS CLINICA MEDICA','URGENCIAS CLINICA MEDICA','URGENCIAS CIRUGIA','URGENCIAS TRAUMATOLOGIA','URGENCIAS UROLOGIA']),sit:'Finalizado'})}
  $('cs-msg').className='msg on ok';$('cs-msg').textContent='Se cargaron 412 consultas de ejemplo.';renderConsultas()};
$('cs-clear').onclick=()=>{consData=[];$('cs-msg').className='msg';renderConsultas()};
function analisisConsultas(){const L=consData,tot=L.length,porC={},ed={},cruz={};COLORES.concat(['Sin clasificar']).forEach(c=>{porC[c]=0;ed[c]=[]});
  L.forEach(x=>{porC[x.color]=(porC[x.color]||0)+1;if(x.edad!=null)(ed[x.color]=ed[x.color]||[]).push(x.edad);const r=x.edad==null?'Sin dato':rango(x.edad);cruz[r]=cruz[r]||{};cruz[r][x.color]=(cruz[r][x.color]||0)+1});
  const dias=[...new Set(L.map(x=>x.fecha))].sort();const porDia=dias.map(d=>[d,L.filter(x=>x.fecha===d).length]);
  const esp={};L.forEach(x=>{if(x.esp)esp[x.esp]=(esp[x.esp]||0)+1});
  return {tot,porC,ed,cruz,porDia,esp,banal:(porC.Azul+porC.Verde)/(tot||1)*100}}
function renderConsultas(){const A=analisisConsultas();if(!A.tot){$('cs-out').innerHTML='<p class="note">Todavía no hay consultas cargadas.</p>';return}
  const mx=Math.max(...COLORES.map(c=>A.porC[c]),1),mean=a=>a.length?(a.reduce((x,y)=>x+y,0)/a.length).toFixed(1):'-';
  $('cs-out').innerHTML=`<div class="kpis"><div class="kpi"><b>${A.tot}</b><span>Consultas totales</span></div><div class="kpi"><b>${A.banal.toFixed(1)}%</b><span>Azul y verde (baja complejidad)</span></div><div class="kpi"><b>${A.porC.Rojo+A.porC.Naranja+A.porC.Amarillo}</b><span>Alta prioridad (rojo, naranja, amarillo)</span></div><div class="kpi"><b>${A.porDia.length}</b><span>Día${A.porDia.length>1?'s':''} analizado${A.porDia.length>1?'s':''}</span></div></div>
  <h3>Consultas por color y edad media</h3>${COLORES.map(c=>`<div class="hb"><span><span class="dot" style="background:${TRIC[c]}"></span>${c} · edad media ${mean(A.ed[c])}</span><div class="bar"><i style="width:${A.porC[c]/mx*100}%;background:${TRIC[c]}"></i></div><b>${A.porC[c]}</b></div>`).join('')}
  <h3>Rango de edad por color</h3><div class="tbl"><table><thead><tr><th>Edad</th>${COLORES.map(c=>`<th>${c}</th>`).join('')}<th>Total</th></tr></thead><tbody>${RANGOS.map(r=>r[2]).concat(['Sin dato']).filter(r=>A.cruz[r]).map(r=>`<tr><td>${r}</td>${COLORES.map(c=>`<td>${A.cruz[r][c]||0}</td>`).join('')}<td><b>${Object.values(A.cruz[r]).reduce((a,b)=>a+b,0)}</b></td></tr>`).join('')}</tbody></table></div>
  ${A.porDia.length>1?`<h3>Consultas por día</h3><div class="tbl"><table><tbody>${A.porDia.map(([d,n])=>`<tr><td>${fi(d)}</td><td>${n}</td></tr>`).join('')}</tbody></table></div>`:''}
  ${Object.keys(A.esp).length?`<h3>Por especialidad</h3><div class="tbl"><table><tbody>${Object.entries(A.esp).sort((a,b)=>b[1]-a[1]).map(([k,v])=>`<tr><td>${esc(k)}</td><td>${v}</td></tr>`).join('')}</tbody></table></div>`:''}`}

/* Informe final para jefatura */
function informeFinalHTML(){const I=datosInforme(),A=analisisConsultas(),tot=I.E.length,k=capacidad(),fis=I.sec.filter(s=>!s.virtual);
  const cd=fis.reduce((a,s)=>a+s.camas,0)*I.d*24,hp=fis.reduce((a,s)=>a+s.hp,0),eg=fis.reduce((a,s)=>a+s.egr,0),ob=I.E.filter(e=>e.tipo==='Óbito').length;
  const cs=censos.filter(c=>c.fecha>=iso(I.ini)),mean=a=>a.length?(a.reduce((x,y)=>x+y,0)/a.length):0;
  const adqE=pac.filter(p=>{const e=escara(p);return e&&e.adq}).length,adqG=pac.filter(p=>p.ais.origen==='Adquirido en Urgencias'&&(p.ais.kpc!=='No'||p.ais.germ!=='Ninguno')).length,sinCrit=egresos.filter(e=>e.reg&&e.cond&&e.cond!=='Cumple criterios').length;
  const T=(hd,rows)=>`<table><tr>${hd.map(x=>`<th>${x}</th>`).join('')}</tr>${rows.map(r=>`<tr>${r.map(x=>`<td>${x}</td>`).join('')}</tr>`).join('')}</table>`;
  return `<h1>Informe final de gestión - Urgencias Polivalentes y Reanimación HEQI</h1><p>Período: últimos ${I.d} días (${fdate(I.ini)} al ${fdate(NOW)}). Generado el ${fdt(NOW)}. Comando de Camas - Urgencias HEQI.</p>
  <h2>1. Indicadores de gestión de camas</h2>
  <p>Camas fijas ofertables: ${fis.reduce((a,s)=>a+s.camas,0)} (Código rojo es espacio virtual y no se cuenta). Porcentaje de ocupación global: <b>${(hp/cd*100).toFixed(0)}%</b>. Giro de cama global: <b>${(eg/fis.reduce((a,s)=>a+s.camas,0)).toFixed(1)}</b>. Estadía media global: <b>${dur(mean(I.E.map(e=>e.horas))*H)}</b>. Intervalo de sustitución: <b>${eg?dur(Math.max(0,cd-hp)/eg*H):'-'}</b>. Mortalidad en Urgencias: <b>${(ob/(tot||1)*100).toFixed(1)}%</b> (${ob} óbitos en ${tot} egresos).</p>
  ${T(['Sector','Camas','Ocupación','Estadía media','Giro de cama','Intervalo de sustitución','Egresos','Óbitos'],I.sec.map(s=>[s.n,s.virtual?'virtual':s.camas,s.virtual?'-':s.ocup.toFixed(0)+'%',dur(s.est*H),s.virtual?'-':s.giro.toFixed(1),s.isus==null?'-':dur(s.isus*H),s.egr,s.ob]))}
  <p>Ocupación mayor a 100% indica pacientes en sofás o camillas provisorias por encima de las camas fijas. Intervalo de sustitución: tiempo promedio que una cama queda vacía entre un egreso y el siguiente ingreso.</p>
  <h2>2. Censo diario</h2><p>Promedio de pacientes en Urgencias por día: <b>${mean(cs.map(c=>c.total)).toFixed(1)}</b> (máximo ${Math.max(0,...cs.map(c=>c.total))}). Promedio de pacientes esperando cama al cierre: <b>${mean(cs.map(c=>c.espera)).toFixed(1)}</b>.</p>
  <h2>3. Lugares de externación</h2>${T(['Destino','Pacientes','%'],Object.entries(I.dest).sort((a,b)=>b[1]-a[1]).map(([kk,v])=>[kk,v,(v/(tot||1)*100).toFixed(1)+'%']))}
  <h2>4. Espera de cama</h2><p>Pacientes esperando cama ahora: <b>${espera.length}</b>${espera.length?' (mayor espera: '+dur(NOW-Math.min(...espera.map(e=>+e.sol)))+')':''}. Salieron de la lista sin cama: ${espBajas.length}.</p>
  <h2>5. Calidad y seguridad</h2>${T(['Indicador','Valor'],[['Escaras adquiridas en Urgencias (pacientes actuales)',adqE],['Gérmenes multirresistentes adquiridos en Urgencias',adqG],['Pacientes que requieren sala de aislamiento',pac.filter(p=>aisl(p)&&aisl(p).k==='a').length],['Egresos registrados sin cumplir criterios',sinCrit]])}
  <h2>6. Caracterización de las consultas</h2>${A.tot?`<p>Consultas analizadas: <b>${A.tot}</b>. Azul y verde (baja complejidad): <b>${A.banal.toFixed(1)}%</b>.</p>
  ${T(['Color','Consultas','%','Edad media'],COLORES.map(c=>[c,A.porC[c],(A.porC[c]/A.tot*100).toFixed(1)+'%',A.ed[c].length?(A.ed[c].reduce((x,y)=>x+y,0)/A.ed[c].length).toFixed(1):'-']))}
  <p>Rango de edad por color:</p>${T(['Edad',...COLORES,'Total'],RANGOS.map(r=>r[2]).concat(['Sin dato']).filter(r=>A.cruz[r]).map(r=>[r,...COLORES.map(c=>A.cruz[r][c]||0),Object.values(A.cruz[r]).reduce((a,b)=>a+b,0)]))}`:'<p>No se cargaron consultas para este informe.</p>'}
  <h2>7. Capacidad de contingencia al momento del informe</h2>${T(['Recurso','Disponible'],[['Camas libres en Reanimación',k.libres.rea],['Pacientes de Reanimación aptos para sala',k.reaLib],['Camas libres en Polivalentes',k.libres.obs+k.libres.ec],['Pacientes que pueden liberar cama',k.liberables],['Sofás o camillas provisorias',k.stcExtra],...recursos.map(r=>[r.n,r.c])])}
  <p style="margin-top:40px">Firma y sello de la jefatura: ______________________</p>`}
const CSSI='body{font-family:Arial,sans-serif;font-size:11pt;margin:24px}h1{font-size:15pt}h2{font-size:13pt;margin-top:18px}table{border-collapse:collapse;width:100%;margin:6px 0}th,td{border:1px solid #888;padding:4px 6px;text-align:left}th{background:#e6e6e6}';
function informeWord(){const html=`<html xmlns:o="urn:schemas-microsoft-com:office:office" xmlns:w="urn:schemas-microsoft-com:office:word"><head><meta charset="utf-8"><title>Informe final</title><link rel="icon" type="image/png" href="/icon/fav-48.png"><link rel="apple-touch-icon" href="/apple-touch-icon.png"><link rel="manifest" href="/manifest.webmanifest"><meta name="theme-color" content="#1d4a42"><meta name="apple-mobile-web-app-capable" content="yes"><meta name="mobile-web-app-capable" content="yes"><meta name="apple-mobile-web-app-title" content="HEQI"><style>${CSSI}</style></head><body>${informeFinalHTML()}</body></html>`;
  const a=document.createElement('a');a.href=URL.createObjectURL(new Blob(['\ufeff'+html],{type:'application/msword'}));a.download=`Informe_final_Urgencias_HEQI_${HOY}.doc`;document.body.appendChild(a);a.click();a.remove()}
function informeImprimir(){const w=window.open('','_blank');if(!w){alert('El navegador bloqueó la ventana de impresión.');return}w.document.write(`<html><head><meta charset="utf-8"><title>Informe final</title><link rel="icon" type="image/png" href="/icon/fav-48.png"><link rel="apple-touch-icon" href="/apple-touch-icon.png"><link rel="manifest" href="/manifest.webmanifest"><meta name="theme-color" content="#1d4a42"><meta name="apple-mobile-web-app-capable" content="yes"><meta name="mobile-web-app-capable" content="yes"><meta name="apple-mobile-web-app-title" content="HEQI"><style>${CSSI}</style></head><body>${informeFinalHTML()}</body></html>`);w.document.close();w.focus();w.print()}

function renderExtra(){const bl=Object.entries(bedSt).filter(([c,b])=>b.st==='Bloqueada');
  $('pz-bloq').innerHTML=bl.length?`<div class="tbl"><table><tr><th>Cama</th><th>Motivo</th><th>Se avisó a</th><th>N.° reclamo</th><th>Estado</th><th>Desde</th><th>Días</th></tr>${bl.map(([c,b])=>{const d=b.desde?Math.floor(Math.max(0,Date.now()-new Date(b.desde))/D):'';return `<tr><td>${c}</td><td>${esc(b.nota||'')}</td><td>${esc(b.aviso||'-')}</td><td>${esc(b.ticket||'-')}</td><td>${esc(b.estRec||'Abierto')}</td><td>${b.desde?fdt(new Date(b.desde)):'-'}</td><td style="font-weight:700;color:${d>=7?'#b03a2e':d>=2?'#9a6200':'inherit'}">${d}</td></tr>`}).join('')}</table></div></div><p class="note">Amarillo: más de 48 h. Rojo: más de 7 días. Camas-día perdidas en este momento: ${bl.reduce((x,[c,b])=>x+(b.desde?Math.max(0,Date.now()-new Date(b.desde))/D:0),0).toFixed(1)}.</p>`:'<p class="note">No hay camas bloqueadas.</p>';
  const m=movs.slice(-60).reverse();$('pz-mov').innerHTML=m.length?`<div class="tbl"><table><tr><th>Fecha y hora</th><th>Movimiento</th><th>Paciente</th><th>De</th><th>A</th><th>Usuario</th></tr>${m.map(x=>`<tr><td>${fdt(new Date(x.f))}</td><td>${esc(x.tipo)}</td><td>${esc(x.nom)}${x.ci?' ('+esc(x.ci)+')':''}</td><td>${esc(x.de)}</td><td>${esc(x.a)}</td><td>${esc(x.u)}</td></tr>`).join('')}</table></div></div>`:'<p class="note">Todavía no hay movimientos registrados.</p>'}
function renderAll(){renderExtra();renderPiz();renderEsp();renderCamas();renderDer();renderInd();renderInforme();renderCenso();renderCont()}
function tab(p){document.querySelectorAll('nav button').forEach(b=>b.setAttribute('aria-selected',b.dataset.p===p));document.querySelectorAll('.panel').forEach(s=>s.classList.toggle('on',s.id==='p-'+p));if(p==='cons')renderCons();if(p==='piz')renderPiz();if(p==='esp')renderEsp();if(p==='der')renderDer();if(p==='ind'){renderInd();renderInforme();renderCenso()}if(p==='cont')renderCont();if(p==='csl')renderConsultas()}
document.querySelectorAll('nav button').forEach(b=>b.onclick=()=>tab(b.dataset.p));
$('inf-p').onchange=renderInforme;$('cen-save').onclick=guardarCenso;$('if-word').onclick=informeWord;$('if-print').onclick=informeImprimir;renderConsultas();$('inf-csv').onclick=csv;$('inf-print').onclick=imprimir;
SEMBRANDO=false;
// ================= SINCRONIZACIÓN CON EL SERVIDOR =================
const CLAVES=['pac','egresos','consultas','bedSt','espera','espBajas','censos','recursos','consData','movs'];
function enc(v){if(v instanceof Date)return {$d:v.getTime()};if(Array.isArray(v))return v.map(enc);if(v&&typeof v==='object'){const o={};for(const k in v)o[k]=enc(v[k]);return o}return v}
function dec(v){if(Array.isArray(v))return v.map(dec);if(v&&typeof v==='object'){if('$d' in v&&Object.keys(v).length===1)return new Date(v.$d);const o={};for(const k in v)o[k]=dec(v[k]);return o}return v}
function estado(){return {pac,egresos,consultas,bedSt,espera,espBajas,censos,recursos,consData,movs}}
function aplicar(d){pac=d.pac||[];egresos=d.egresos||[];consultas=d.consultas||[];bedSt=d.bedSt||{};espera=d.espera||[];espBajas=d.espBajas||[];censos=d.censos||[];recursos=d.recursos||recursos;consData=d.consData||[];movs=d.movs||[];
  pac.forEach(p=>{p.vm=p.vm||{iot:'',corr:''}})}
let VER=0,BASE=null,guardando=false,timer=null;const J=x=>JSON.stringify(x);
function st(t,c){const e=$('sync-st');if(e){e.textContent=t;e.style.color=c||''}}
function fusion(base,local,remoto){const r={};
  const porId=(b,l,m)=>{const B=new Map((b||[]).map(x=>[x.id,J(x)])),L=new Map((l||[]).map(x=>[x.id,x])),out=new Map((m||[]).map(x=>[x.id,x]));
    for(const [id,x] of L)if(B.get(id)!==J(x))out.set(id,x);for(const id of B.keys())if(!L.has(id))out.delete(id);return [...out.values()]};
  const agregados=(b,l,m)=>{const B=new Set((b||[]).map(J)),M=new Set((m||[]).map(J));return (m||[]).concat((l||[]).filter(x=>!B.has(J(x))&&!M.has(J(x))))};
  r.pac=porId(base.pac,local.pac,remoto.pac);r.espera=porId(base.espera,local.espera,remoto.espera);
  r.bedSt=Object.assign({},remoto.bedSt||{});const ks=new Set([...Object.keys(base.bedSt||{}),...Object.keys(local.bedSt||{})]);
  for(const k of ks){if(J((local.bedSt||{})[k])!==J((base.bedSt||{})[k])){if((local.bedSt||{})[k])r.bedSt[k]=local.bedSt[k];else delete r.bedSt[k]}}
  ['egresos','consultas','espBajas','censos','consData','movs'].forEach(k=>r[k]=agregados(base[k],local[k],remoto[k]));
  r.recursos=J(local.recursos)!==J(base.recursos)?local.recursos:remoto.recursos;return r}
let CARGA_OK=false;
async function bajar(){const r=await fetch('/api/camas/estado');if(r.status===401){location='/login';return null}if(!r.ok){throw new Error('permiso '+r.status)}const j=await r.json();if(typeof j.version!=='number')throw new Error('respuesta inválida');return j}
function errorCarga(){CARGA_OK=false;let b=document.getElementById('err-carga');if(!b){b=document.createElement('div');b.id='err-carga';b.style.cssText='position:fixed;inset:0;background:rgba(120,20,10,.92);color:#fff;z-index:9999;display:flex;flex-direction:column;align-items:center;justify-content:center;text-align:center;padding:24px;font-size:1.1rem';b.innerHTML='<b style="font-size:1.3rem">⚠ No se pudieron cargar los datos del Comando de Camas</b><p>Los datos NO se perdieron. Volvé a iniciar sesión para continuar.</p><a href="/logout" style="background:#fff;color:#7a1f14;padding:12px 20px;border-radius:10px;font-weight:700;text-decoration:none">Volver a iniciar sesión</a>';document.body.appendChild(b)}}
async function iniciarSync(){
  try{const j=await bajar();if(!j)return;VER=j.version;
    if(j.data){aplicar(dec(JSON.parse(j.data)))}else{aplicar({})}
    BASE=J(enc(estado()));CARGA_OK=true;st('✔ Sincronizado','#c8f2dc')}catch(e){st('⚠ No se pudieron cargar los datos','#ffd0c8');errorCarga()}
  renderAll();renderCons()}
async function subir(){if(guardando||!CARGA_OK)return;const actual=J(enc(estado()));if(actual===BASE)return;guardando=true;st('Guardando…');
  try{let r=await fetch('/api/camas/estado',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({base:VER,data:actual})});
    if(r.status===409){const j=await r.json();const mezcla=fusion(JSON.parse(BASE),JSON.parse(actual),JSON.parse(j.data||'{}'));const abierto=$('ov').classList.contains('on');
      aplicar(dec(mezcla));VER=j.version;const nuevo=J(enc(estado()));
      r=await fetch('/api/camas/estado',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({base:VER,data:nuevo})});
      if(abierto&&cur){cur=pac.find(p=>p.id===cur.id)||null;if(cur)renderFicha();else cerrar()}renderAll()}
    if(r.ok){const j=await r.json();VER=j.version;BASE=J(enc(estado()));st('✔ Guardado '+two(new Date().getHours())+':'+two(new Date().getMinutes()),'#c8f2dc')}
    else if(r.status===401){location='/login'}else st('⚠ No se pudo guardar, reintentando…','#ffd0c8')}
  catch(e){st('⚠ Sin conexión: se reintentará','#ffd0c8')}
  guardando=false}
function programar(){NOW=new Date();HOY=iso(NOW);clearTimeout(timer);timer=setTimeout(subir,900)}
['click','change','input'].forEach(ev=>document.addEventListener(ev,programar,true));
setInterval(async()=>{NOW=new Date();HOY=iso(NOW);
  try{const r=await fetch('/api/camas/version');if(r.status===401||r.status===403){errorCarga();return}if(!r.ok)return;const j=await r.json();
    if(j.version>VER&&!guardando&&J(enc(estado()))===BASE&&!$('ov').classList.contains('on')){const k=await bajar();if(!k)return;aplicar(dec(JSON.parse(k.data||'{}')));VER=k.version;BASE=J(enc(estado()));renderAll();st('✔ Actualizado por '+(j.usuario||'otro usuario'),'#c8f2dc')}
    else if(!$('ov').classList.contains('on'))renderAll();
  }catch(e){}},10000);
setInterval(subir,15000);
$('mov-csv').onclick=()=>{const q=x=>'"'+String(x??'').replace(/"/g,'""')+'"';const t='\ufeff'+['Fecha y hora;Movimiento;Paciente;CI;De;A;Usuario'].concat(movs.map(x=>[fdt(new Date(x.f)),x.tipo,x.nom,x.ci,x.de,x.a,x.u].map(q).join(';'))).join('\n');
  const a=document.createElement('a');a.href=URL.createObjectURL(new Blob([t],{type:'text/csv'}));a.download='movimientos_camas_HEQI.csv';a.click()};

function informePaseHTML(){const ahora=new Date(),h24=new Date(+ahora-24*H),S=x=>esc(x==null?'':String(x));
  const fn=d=>d?fi(d):'';const m24=movs.filter(x=>new Date(x.f)>=h24),cnt=t=>m24.filter(x=>x.tipo.startsWith(t)).length;
  const bl=Object.entries(bedSt).filter(([c,b])=>b.st==='Bloqueada');
  let crit=[],prox=[];pac.forEach(p=>alertas(p).forEach(([k,t])=>{const lin=`<b>${S(p.cama)}</b> - ${S(p.nom)}: ${S(t)}`;if(k==='bd')crit.push(lin);else if(/programad|Cirugía|Ayuno|corrugado|destinar/i.test(t))prox.push(lin)}));
  const est=p=>p.est.filter(e=>ACT.includes(e.estado)).map(e=>`${S(e.nom)} (${S(e.estado)}${e.fprog?' '+fi(e.fprog)+(e.hora?' '+e.hora:''):''})`);
  const qx=p=>p.qx.filter(q=>!['Realizado','Sin efecto'].includes(q.estado)).map(q=>`Cx ${S(q.nom)} (${S(q.estado)}${q.fecha?' '+fi(q.fecha)+(q.hora?' '+q.hora:''):''})`);
  const fila=p=>{const r=news2(p.vit),so=sofa(p),al=alertas(p).filter(a=>a[0]==='bd').map(a=>S(a[1]));
    return `<tr><td><b>${S(p.cama)}</b></td><td><b>${S(p.nom)}</b><br>CI ${S(p.ci)}<br>Nac. ${p.fnac?fn(p.fnac):'-'} (${S(p.edad)} a)<br>Reg. ${S(p.reg)||'-'}</td>
      <td>${fdt(p.ingreso)}<br>${dur(ahora-p.ingreso)}</td><td>${S(p.dx)||S(p.motivo)}</td><td>${r?'NEWS2 '+r.s:'-'}${so?'<br>SOFA '+so.s:''}</td>
      <td>${[...est(p),...qx(p)].join('<br>')||'-'}${al.length?'<br><span style="color:#b03a2e">⚠ '+al.join('<br>⚠ ')+'</span>':''}</td>
      <td>${p.dest?'<b>'+S(p.dest)+'</b>':'<b style="color:#b03a2e">SIN DEFINIR</b>'}${p.altaProb?'<br>Alta/traslado '+S(p.altaProb).toLowerCase():''}</td></tr>`};
  let tab='';SEC.forEach(Sx=>{const L=pac.filter(p=>p.sector===Sx.id).sort((a,b)=>String(a.cama).localeCompare(String(b.cama),'es',{numeric:true}));if(!L.length)return;
    tab+=`<h2>${S(Sx.n)} (${L.length})</h2><table><tr><th>Cama</th><th>Paciente</th><th>Ingreso</th><th>Diagnóstico</th><th>Scores</th><th>Pendientes</th><th>Servicio a destinar</th></tr>${L.map(fila).join('')}</table>`});
  const sinDest=pac.filter(p=>!p.dest).length;
  return `<h1>Pase de guardia - Urgencias Polivalentes y Reanimación HEQI</h1><p>Generado el ${fdt(ahora)} por ${S(USUARIO)}.</p>
  <h2>Resumen</h2><p>Pacientes en Urgencias: <b>${pac.length}</b> · Esperando cama: <b>${espera.length}</b> · Camas bloqueadas: <b>${bl.length}</b> · Sin servicio a destinar: <b style="color:${sinDest?'#b03a2e':'inherit'}">${sinDest}</b><br>
  Últimas 24 h: ${cnt('Ingreso')} ingresos · ${cnt('Egreso')} egresos · ${cnt('Movimiento interno')} traslados de cama.</p>
  ${crit.length?`<h2>⚠ Alertas críticas</h2><p>${crit.join('<br>')}</p>`:''}
  ${prox.length?`<h2>⏰ Para tener en cuenta en esta guardia</h2><p>${prox.join('<br>')}</p>`:''}
  ${bl.length?`<h2>🔧 Camas bloqueadas</h2><p>${bl.map(([c,b])=>`<b>${c}</b>: ${S(b.nota)} - aviso a ${S(b.aviso||'-')}, reclamo ${S(b.ticket||'-')}${b.desde?' - '+Math.floor(Math.max(0,Date.now()-new Date(b.desde))/D)+' día(s)':''}`).join('<br>')}</p>`:''}
  ${tab||'<p>No hay pacientes internados en Urgencias.</p>'}`}
function paseImprimir(){const w=window.open('','_blank');if(!w){alert('El navegador bloqueó la ventana de impresión.');return}w.document.write(`<html><head><meta charset="utf-8"><title>Pase de guardia</title><link rel="icon" type="image/png" href="/icon/fav-48.png"><link rel="apple-touch-icon" href="/apple-touch-icon.png"><link rel="manifest" href="/manifest.webmanifest"><meta name="theme-color" content="#1d4a42"><meta name="apple-mobile-web-app-capable" content="yes"><meta name="mobile-web-app-capable" content="yes"><meta name="apple-mobile-web-app-title" content="HEQI"><style>${CSSI}</style></head><body>${informePaseHTML()}</body></html>`);w.document.close();w.focus();w.print()}
function paseWord(){const html=`<html xmlns:o="urn:schemas-microsoft-com:office:office" xmlns:w="urn:schemas-microsoft-com:office:word"><head><meta charset="utf-8"><title>Pase de guardia</title><link rel="icon" type="image/png" href="/icon/fav-48.png"><link rel="apple-touch-icon" href="/apple-touch-icon.png"><link rel="manifest" href="/manifest.webmanifest"><meta name="theme-color" content="#1d4a42"><meta name="apple-mobile-web-app-capable" content="yes"><meta name="mobile-web-app-capable" content="yes"><meta name="apple-mobile-web-app-title" content="HEQI"><style>${CSSI}</style></head><body>${informePaseHTML()}</body></html>`;
  const a=document.createElement('a');a.href=URL.createObjectURL(new Blob(['\ufeff',html],{type:'application/msword'}));a.download='Pase_de_guardia_Urgencias_HEQI_'+iso(new Date())+'.doc';a.click()}
$('pase-print').onclick=paseImprimir;$('pase-word').onclick=paseWord;$('pase-top').onclick=e=>{e.preventDefault();paseImprimir()};
iniciarSync();
</script>
</body>
</html>
'''

# ================= LOGO E ÍCONOS =================
import base64 as _b64
LOGOS = {"fav-48": "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", "icon-180": "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", "icon-192": "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", "icon-512": "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60GNREQcvno/cKvVIiIpCK43PUxbG5dk2cgtkqRO3cqRR1+nBoIDLiZPguJJlg4dNvdWevgbXNbvYPI5KIAL8yIPDf4eY1n4uK3W2hPp1Bsd4WCgvJwcL5h84kEUhm+t8hnLOtXMOcO+x8sU+WhZtqc08DEKEVhxHHtiO1mhSEB/5v07nNaSneWJeJnu+3gBQGa/iGzyd77B5Aq1jq36BMTTRqWnS4YaUxVFsnuCB7kzYll7IhCxmiV0XucOkutqVM6cf7LmUbe0Tlgky5DBNUJoKF0UsmzR8fVGawkJekajhpc8e091QFAAR27NS1Lgh1oHjSTVUSfwmGnydS9YOuP9sAsASNNU+irX1tbu3bu3tLQkSVepW3/58uXOzo6019bN//pijiconzHecsy8vbr49v/UWsuAsNXV1bt37y4vL8uUmH6///Lly83NTalnb2QvLskArBdfSa1nu93+8MMP79+/v7Cw0O12mVmCQjJuZWNjwzOw1m9gnYZzmjRpdm3kKed8xEkKQO/evbu2ttZutwFAiqkkp7q5uSlKq85Q7ekofHtaY3jcLAO/GqN+TtQQ9dozmVwvUz/v3r177969brcrPR8vX7786aeffvrpJz+1WEgAZdyxbyNvTEeAI0paG6wP09na8wuNo0709JidoACuuwF+NbGgQ+cfzT6YtB5MqL+hj4x7w2p+fv7jjz/+xS9+8cUXXzx48MArAGkP/vrrr//85z/LfPA6V/Ch7u2hR32WJMFRRm79576WQ0RDt9u9c+fOBx988Ktf/eqXv/ylDL5n5q2trW+++eavf/3rN998I1lNSQN4j2FaB9Q7b49ac+MFDUJ5Lz2JqN1ur62tff755//0T//0xRdfrKysJEkiSeBXr149evTot7/97Z///GdZWD3a7u9t3UE5tETk+FCDvFKcISJKkmR+fv7nP//5P/7jP37++ecffPCBF6PSkva73/3u66+/rutLmGp1hsNIob1KPvGMHJXJmL4ioScSDRTH8WefffbVV1999dVX0rcofA87OzsvXrz47gAvX74sy9KzwHrtdbxtdKJvfWXsp4cGdYMCCLhgiEnoBwz55po4jqVFaGVlZXl5eWlpyTPUr66ufvTRR0+fPpW4kHSHwpszThsNw9Pz9hovONTAP4pc79A54D56TkRLS0tra2tLS0v379+XNmZE3NnZ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", "logo-full": "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rutgUwwPD58+fVrTtNbWVnB3DcMYGBj45JNPZmdnP/zww8cff7yoqEhVVSip+eijj0DYJRIJhFBVVVVFRQVYLrDzsC1AclevXr1y5YokSbdu3YK8XElJyZYtWwghn3766cDAQEFBwZNPPrl+/XpN0yYnJyFhe+HChcuXL0OCkef5RCLx6aefrlu3zu12T05OvvXWW59++ilCCIJkiqKEQqF4PN7b23v06NF169bBzoPlUlFRIcvyu++++6tf/WrNmjXf+973tmzZApFY8PPdbrfP57NGEGwNGUtZpLk2v0AwjRkDyWTS4/FAaV8qleJ5PpVKTU1Ntba27ty58xvf+MahQ4c+/PDDwcHB8vJySBZBMuDAgQPNzc1Op3PNmjU8z/f39//qV7+6evVqYWFhPB4fGhoSBGHTpk1r167VdR1iPBCegSCHtcQJqBPKTa2GIliAIPlA4vb390MGduvWrZAWg/Tu+fPn/+f//J9QSPDoo4/GYjEo6erq6vpf/+t/iaIYDocTiUR9ff1TTz21f//+6upq5tMD1KSu693d3f/0T/9UUFAQi8WGhobm5+cbGhpefvlluAsEacPh8O9+97ve3l6IfyiK4vf7H3rooWeffVYURQiXs1JDYLyPPvooFAoxKxdU33e/+92SkpLa2tpjx4599tlnU1NT69atc7lc4+PjN2/erKio2LJlS2Fh4djYGGhmiFv4/X5r8TFY6WD1DQ8P/7//9/+A9CGoVltb+9prr+3cubO+vv7ll1+em5u7cuXKf/tv/62pqQkU2sTEREVFxcMPP1xcXDw4OOhwOLxeryzLk5OT586dGxgYqKysfPXVV59//nmgyMnJSZ7n3377bcgMb9682TRNSZKi0ejvf//7c+fOxeNxsFCeeeaZp556Kh6PezweWZbB+gXqSiQSn3zySTQahTK6yclJSum+ffuefvrpRCJx/PhxTdO2b9/+2muvNTc3g0t/4cKFv//7v79x40Z3d/fOnTt1XYeMyNGjRyORCCFkdHR0dnbWNM3t27fv3bvX6XSGw2GQTb29vT/60Y/Ky8t1XYesZlVV1auvvtrZ2VlfX+/1es+dOxcOh9evX19aWhoMBk+ePClJ0rZt29atWwcmQ3qL9qoqZuDwoEaxrq5OEASoJICLulyutWvX1tTUbNiwobi42DCM2tra73//+2VlZR9++OHIyMjY2Bh4z1u2bHnsscf27dsHUfKnnnoqHA6//fbbo6OjV65cgaCZw+HYt2/fn/7pn5aWlsZisZqamra2tsbGRjBgbE0xkiRVVlbW1NRUVlaWl5ezshK/379x48ZQKLRhw4aCggJQL5IktbW1vfTSS9u3by8oKAByFARh3759Bw8eBM/E6/W2trb29vbyPA9KOJlMAjXMzMzIsszK0E3TdLlca9asKSkpAfE5Pz8PAafm5uZnn332+eefd7lcqqrW1dV1dnZeu3aNUjo2NgauF+iQmZmZZDLJIqtwWb/f39HRAZHVubk5iBNomkYIgZRgRUXF97//fZ7njx07NjMzc/ToUbAwa2pqXnjhhSeeeIIQIkkSlFlBFtvamQnUIIoilArIsjw3N5dIJARBUBQlHo/rut7T09PR0VFRUfHSSy9xHPfGG28MDAxcuHCB4ziPx/PYY489//zzzzzzjNPppJRCyWhDQwMMRygtLV2/fv2TTz7JJF1BQcE3v/nN2dlZsMwppe3t7e3t7X19faqqjo+Pq6oKZzQ3NxeLxQKBQFtb2/T0dGlpqa7rRUVFGzZsADOvr68PZEd1dfXDDz/8ne98p7q6uq+vjxDS3Nz83HPPPfTQQxAvBL/p2rVroKtN0wwEAo2NjSMjIyAXwL2qqqrq7Ox89tlnQehjjOvr62tra0EeybIMDwwZr1AoJAjCU089xXHc66+/PjY2dvHiRTggr9f7xBNP/Mmf/ElFRUWOqNuZuyhuCygUDofPnDkzNze3ZcsWCCeCQL127dqFCxdaW1s3bNjg8/kg3jUzMwOxO6hdLioq6uzsbGpqKiwsZLwExbK3bt2anZ2FSF1paenmzZtbW1t5npdlubu7e2BgADjc6XSyxC5Tzn19fVBAtGXLFhDnYO9duXLl+vXrzc3NO3bsIISMj4+fOnVK0zQQ8ExhyrJ8/fr1M2fOtLa2sqql69evQ/kf2CGapkFFQVtbG6TO4bvJZHJwcPDs2bOqqhYVFYFwDQQCZWVlHR0dwPxgpV+/fh1OHYo2WIdHbW3tli1bSkpKrN0P09PTEKPSNA3YGIxtQkh1dfXu3bvLy8tN0xweHobNiUajwButra0bN26EgtVQKHTu3LlEItHZ2Qm1b8DqrJUEqoVu3LgBjMEaLyBE0dra2tHRAaHsSCTS29t748YN8PTKy8tbWlrgr/C0XV1d8Xi8ubm5vr4+HA6fO3fO7/dv374dKAGEXSwWO3bs2MTExGOPPbZ27dpQKHTy5MnR0VFWzW8YhizLra2t69evp5SCU7dr1676+vpoNHrlypWbN2+CTwjC2ufzgVMKpvjJkyeTyeTOnTtrampYFE3TtO7u7u7u7urq6p07d2qadu7cucHBQdgEiKxCbWBNTQ08iaqqQ0NDXV1dsiw7HA6IroMxwvP89u3bW1paHA5HLBaDikVIWTscjubm5s7OzsrKSihNWfa4rtyZEGIJsK0sEQmnC6kbFr+Cz4CJaI0CWzv0WH8Ts5RYWtbqnbO0UsbOfVAsINpZhA2+CNsHYTHIcELw1tZED0zL0s3Ae6Ca2LOx+Ketd5HFDMFwYgjlzHVkzXu27hh2Bdg0WzOeDUbA6oWyHhzWdQU5FZaPYqkUTdOgXQCso4x99NZ4r3W8nq3bldE0bAL7E5NTrM0KNhNakKztPPAx6B2Bj6XXAFonS4OfCTk3Vhph7fC0pr44joMmAafTyVIR7ANgREBxgrWli9FkegegFfCBVWOzpJ+1zJWhBMBnlluttkImtDVfpzfUZ4RyslVgoiXmbNly5VZ2tWKJW5+ThSuZRWdr2Uy/oLUP2tqRbCsQtTZKW1+Huabp4CW2mo90bJulWBEtDdFvi51acWVsrc+2lmjWqGqtPbAmjq3iMv2MbGFb2H9rI7Jtk23t5LfFBMuIKGUVRhlnwWdsH0dLDMmz7p4txLhUp/hSgRPbjdiH2UEst4Fw2UyYe0dGls9kgUXIiGhkLadgRGMFNcoIvpSRLKzITulwONkB/2w3SiaTMzMzoiiWlpYysW1rYE1vD88+HDcdFQLIPR0ZyQYht9QcVasGY8+TjkCVXtmYI+Rpuka18kxGyZUxWG+NCTMZkQXRwyo6bR+2QnLkOBIwO7Nlp96lxmOseHrHMsrW7vZK7+i3NdSDK5UFLH0pbK/0U7Gx91JYMlaCSCQSFy5cuHr1alVV1a5du6CYy2bDWIkjHfNmKaCudGw1m6pkVTvZByfY2GmpiJy1GN0GkGcjoxyRmrMgSthqXGwXt0LdMNPOOntsKdQzK5JaFmG3+jFhuX9sNTxCcrzrstCjaNrK8fPphAIOj9VFyQXGLyOWZsaS9BwFJAAIfPDBBydPnuzv749EIlBIweqnMt6avRcrzkpH8rIpbUaOzOvIaIdn3z3rYeEvrozfWtbh2nh+qfNlRjvzoGxlRuyXzMzJok6tvMTCSzZbKR1q7cuy+OXy/V2aFJ8lr8KOMx3oKcsAA1ZwaD1gG8gXI4J05435QuzDoI5qamrWr19fUlLCYCNY3IW1Jtm8UxZ2shGKDXeIPQOr9WHXZ/V36IuDU5iZyi7OnOd0d4h9wCaYrNRvVS9LYSKylBWUU7NMprUs2wonY63sY/4eVPazkB5DiGF4OVZgGIYZxeoN0jHamMyyogqtZrpbjoD0d2QtGwY/98fNneWWGrzKCEjTtFQqFY1GIbIM5dcQz2RtBxAmLSwsZCHERCIxMzPjcrlKSkqgCAPaeSGJDKgqTEGx1nLWkwH5awj3eTweqEL2eDxNTU3QPwGlj1CTDaFOhpXEqhNZ8R2QFBSXQME+lOBB7zKQi6ZpsizHYjG32+31elnYBmpcFEVBCDmdTqi9ZGVcLAaTSCSgOtfhcEBBmZVt4CJQWi2KImwgwwFhRMw2wQqybAvOwUMmEony8nKXywUlAXBN1tdiGEYoFEokEj6fD+pyjcUFFQtQUAFVSiztzJwr8D6SyaSiKFBBBVIpGo3GYjFJkqCSlhFJIpGAIiGPxwM5PVEUvV4v24Q7RdV3gwn5B1NBs1gzpNouXLhw8eLF6elpwEqpqal56KGHNm3aBFX5six/9NFH3d3dnZ2dTz75JBSgaJp28eLF999/v7a29tvf/nZBQcH58+cPHz7c0NDw/PPPBwKBs2fPHjt2DApWIUvh9Xqh12HLli01NTW6rl+5cuXQoUOAqhIIBLZs2SIIwuTk5KFDh0Kh0HPPPdfa2jozM/PRRx8B4gNUDkGjSW1t7dq1a9va2qAwTdf1ycnJ3t7es2fP3rx5E5AKoDd027ZtbKQWNL+vWbPmqaeegg7R6elpSHv29vYmEomioqLGxsZ169a1tbUBcAsoN6gdPX/+vMvl6uzs3LRpE3RgQ2JpcHDwxIkT165dC4VClFK3293Q0PDQQw91dHT4fD5rB3O6cWGLM0Ea9sSJEz6f76WXXnI6ncPDw3/84x+hdXjjxo0gI+bn548cOTI4OPjwww8//vjjkEiYmJjo6em5ePHi0NCQruvQTLNhw4Zdu3ZBNRJToalU6vTp02fOnOE4bvv27dDBKMvyhQsXzp8/7/F49u7dC03DsEUALPDYY491dHRcvnz5+PHjJSUlzzzzDEAz3ZeBpythwns/MfO2ckjTtKGhoXfeeeett94aHh4G6R6PxzmOa29vf/XVV1944QW/3y/LMlTJvfzyy7t27YI2DkVRPv3005/+9Ketra3wy6NHj/7sZz/bsGHDzp07A4HAsWPH/s//+T+pVKq4uNjn80E5pa7rdXV1f/EXfwG9VBcuXPjnf/7njRs3ArE6HA5N006cOPGjH/0olUo1NDS0trbOz8+/++67R44cgcJr6FuNx+OEkJ07d/7gBz/YvXu3IAizs7OHDh165513rl69CroIbldZWTk0NPTyyy/X1taapnno0KHf/OY3W7ZsgXIfVVXPnj37i1/84ty5cwCKAQWD69evP3DgwJNPPgk1+7Is37p161e/+tUHH3zgcDhefPHF2tpa6EGBruijR4/+4he/GBkZASycubk5SZJ27Njx/e9/f/fu3ax3xJansQbfmWkNFWH/9E//1NDQsHnzZqfTee7cuZ/85CeRSATgeaDkFYpFL1++zPP8zp07RVGcmpp65513Pvzww+Hh4VQqBUWF8Xh87dq1w8PDr732WnV1NetWGRkZ+fGPf/zee+9xHPfqq69WV1fX1NRAc9bvfvc7yNc3NTWBdLty5cpPfvIT6PwoLCz84IMPfvvb39bV1bW3txcXF68wd3cPxxM9oJoQTiIej7/99tv/9E//NDMzs379+ocffrikpGR8fPzEiROHDx+empqqqqp64oknUqnU2NhYKBSanJyEBkLw3UOhUDgcDgaDUHE2MzMzNTVVUlICTY/T09MARbV37966ujpZlmdnZ7u6uq5cufKzn/2svb19w4YNsVgsHo+PjY3Nzs6ydOX09DRgDU5NTUEd+ejoaDKZbGlp2blzZ1lZGdRYfvLJJ++9915JScnmzZsLCgq6urp+/OMfX7t2raWl5dFHHy0vLw8GgydOnABwMbfb/d3vfpfn+Wg0Ojc3B33Puq6fOXPmRz/60fnz50tLS59++uny8vJbt26BSh8fH3c6nQcOHPB4PIqinDx58syZM4lEIh6Pnz59uq+vr7q6GtzUrq4uKD3bvHnziy++KIrip59+evLkyePHjwcCgbq6uoaGBtZuslTgxxq0hKp9aMiEDYlEIvF4/PDhw5s2bXr11VcdDoeqqsPDw5OTk7Ozs2Bbnj179pe//OXQ0FBHR8e2bdsqKipG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", "logo-mark": "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"}

@app.route('/icon/<nombre>.png')
def icono(nombre):
    if nombre not in LOGOS: return 'No encontrado', 404
    r = Response(_b64.b64decode(LOGOS[nombre]), mimetype='image/png'); r.headers['Cache-Control'] = 'public, max-age=604800'; return r

@app.route('/favicon.ico')
def favicon():
    return icono('fav-48')

@app.route('/apple-touch-icon.png')
def apple_icon():
    return icono('icon-180')

@app.route('/manifest.webmanifest')
def manifest():
    m = {'name': 'Gestión Hospitalaria HEQI', 'short_name': 'HEQI', 'start_url': '/', 'display': 'standalone',
         'background_color': '#ffffff', 'theme_color': '#1d4a42',
         'icons': [{'src': '/icon/icon-192.png', 'sizes': '192x192', 'type': 'image/png'},
                   {'src': '/icon/icon-512.png', 'sizes': '512x512', 'type': 'image/png'}]}
    return Response(json.dumps(m), mimetype='application/manifest+json')

@app.route('/pdf/<int:i>')
@requiere_modulo('traslados')
def ver_pdf(i):
    con = conectar(); cur = con.cursor()
    cur.execute(q('SELECT pdf_nombre,pdf FROM derivaciones WHERE id=?'), (i,))
    r = cur.fetchone(); con.close()
    if not r or not r[1]: return 'Sin PDF', 404
    return send_file(io.BytesIO(bytes(r[1])), mimetype='application/pdf', download_name=r[0] or f'derivacion_{i}.pdf')

@app.route('/planilla.csv')
@requiere_modulo('traslados')
def planilla():
    con = conectar(); cur = con.cursor()
    cur.execute('SELECT id,recibido,' + ','.join(CAMPOS) + ',estado,decidido_por,decidido_en,observacion,medico_acepta,concluido_donde FROM derivaciones ORDER BY id')
    out = io.StringIO(); w = csv.writer(out, delimiter=';')
    w.writerow([d[0] for d in cur.description])
    for r in cur.fetchall():
        r = list(r); r[-6] = ESTADOS.get(r[-6], r[-6]); w.writerow(r)
    con.close()
    return Response('\ufeff' + out.getvalue(), mimetype='text/csv',
                    headers={'Content-Disposition': 'attachment; filename=derivaciones_HEQI.csv'})

LOGIN_HTML = r"""<!doctype html><html lang="es"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Gestión Hospitalaria - HEQI</title><link rel="icon" type="image/png" href="/icon/fav-48.png"><link rel="apple-touch-icon" href="/apple-touch-icon.png"><link rel="manifest" href="/manifest.webmanifest"><meta name="theme-color" content="#1d4a42"><meta name="apple-mobile-web-app-capable" content="yes"><meta name="mobile-web-app-capable" content="yes"><meta name="apple-mobile-web-app-title" content="HEQI"><style>
body{margin:0;font-family:Segoe UI,Roboto,Arial,sans-serif;background:#eef2f7;display:flex;min-height:100vh;align-items:center;justify-content:center;color:#1b2330}
form{background:#fff;padding:26px 22px;border-radius:14px;border:1px solid #d5dde8;width:100%;max-width:360px;margin:16px}
h1{color:#1d4a42;font-size:1.3rem;margin:0 0 14px}label{display:block;font-weight:600;font-size:.85rem;color:#5b6b82;margin:12px 0 5px}
input{width:100%;box-sizing:border-box;padding:11px;border:1.5px solid #d5dde8;border-radius:9px;font-size:1rem}
button{width:100%;margin-top:18px;padding:12px;border:0;border-radius:9px;background:#1d4a42;color:#fff;font-weight:700;font-size:1rem}
.e{color:#b3261e;font-size:.88rem;margin-top:8px}</style></head><body>
<form method="post"><img src="/icon/logo-full.png" alt="Hospital de Especialidades Quirúrgicas Ingavi" style="display:block;max-width:220px;margin:0 auto 12px"><h1 style="text-align:center">Gestión Hospitalaria</h1><label>Usuario</label><input name="usuario" autocomplete="username" required>
<label>Contraseña</label><input name="clave" type="password" autocomplete="current-password" required>
{% if err %}<div class="e">{{err}}</div>{% endif %}<button>Ingresar</button></form></body></html>"""

PANEL_HTML = r"""<!doctype html><html lang="es"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Gestión Hospitalaria - HEQI</title><link rel="icon" type="image/png" href="/icon/fav-48.png"><link rel="apple-touch-icon" href="/apple-touch-icon.png"><link rel="manifest" href="/manifest.webmanifest"><meta name="theme-color" content="#1d4a42"><meta name="apple-mobile-web-app-capable" content="yes"><meta name="mobile-web-app-capable" content="yes"><meta name="apple-mobile-web-app-title" content="HEQI"><style>
:root{--verde:#1d4a42;--verde2:#2e7d5b;--rojo:#b03a2e;--ambar:#b7791f;--gris:#5b6b70;--linea:#dfe5e3;--fondo:#f1f4f3;--tinta:#1b2a28;--es:#b03a2e;--pe:#7a8a87;--ok:#2e7d5b;--na:#b7791f}
*{box-sizing:border-box}body{margin:0;font-family:"Segoe UI",Roboto,Arial,sans-serif;background:var(--fondo);color:var(--tinta)}
header{background:var(--verde);color:#fff;padding:14px 22px;display:flex;align-items:center;gap:12px;position:sticky;top:0;z-index:5}
header h1{font-size:1.15rem;margin:0;flex:1;font-weight:700}header small{display:block;font-weight:400;opacity:.75;font-size:.78rem}
header a,header button{color:#fff;border:1.5px solid rgba(255,255,255,.4);background:transparent;border-radius:8px;padding:6px 11px;font-size:.82rem;text-decoration:none;cursor:pointer}
.wrap{max-width:1280px;margin:0 auto;padding:18px}
.tabs{display:flex;gap:8px;margin-bottom:16px}
.tabs button{border:1.5px solid var(--linea);background:#fff;border-radius:10px;padding:9px 16px;font-weight:700;color:var(--gris);cursor:pointer;font-size:.92rem}
.tabs button.on{background:var(--verde);border-color:var(--verde);color:#fff}
.num{display:inline-block;min-width:20px;padding:0 6px;border-radius:10px;background:var(--rojo);color:#fff;font-size:.75rem;margin-left:5px}
.card{background:#fff;border:1px solid var(--linea);border-radius:14px;padding:16px 18px}
.periodo{display:flex;align-items:flex-end;gap:12px;flex-wrap:wrap;margin-bottom:16px}
.periodo label{display:block;font-size:.8rem;color:var(--gris);text-align:center;margin-bottom:4px}
.periodo input{padding:9px 10px;border:1.5px solid var(--linea);border-radius:9px;font:inherit}
.periodo .esp{flex:1}
.btn{border:1.5px solid var(--linea);background:#fff;border-radius:9px;padding:9px 14px;font-weight:600;cursor:pointer;font:inherit}
.kpis{display:grid;grid-template-columns:repeat(auto-fit,minmax(170px,1fr));gap:14px;margin-bottom:16px}
.kpi{text-align:center;padding:18px 10px}.kpi b{display:block;font-size:2rem;line-height:1.1}.kpi span{color:var(--gris);font-size:.9rem}
.graf{display:grid;grid-template-columns:1fr 1fr;gap:16px}@media(max-width:900px){.graf{grid-template-columns:1fr}}
.graf h3{margin:0 0 10px;font-size:1rem;text-align:center}
.leyenda{display:flex;gap:14px;justify-content:center;font-size:.82rem;color:var(--gris);margin-top:6px;flex-wrap:wrap}.leyenda i{display:inline-block;width:11px;height:11px;margin-right:5px;vertical-align:-1px}
svg text{font-family:"Segoe UI",Roboto,Arial,sans-serif}
.filtros{display:flex;gap:8px;flex-wrap:wrap;margin-bottom:10px}
.filtros button{border:1.5px solid var(--linea);background:#fff;border-radius:20px;padding:7px 13px;font-weight:700;color:var(--gris);cursor:pointer}
.filtros button.on{background:var(--verde);border-color:var(--verde);color:#fff}
input[type=search]{width:100%;padding:11px;border:1.5px solid var(--linea);border-radius:9px;margin-bottom:12px;font:inherit}
.ped{background:#fff;border:1px solid var(--linea);border-left:6px solid var(--pe);border-radius:12px;padding:12px 14px;margin-bottom:10px}
.ped.rojo{box-shadow:0 0 0 2px var(--rojo) inset}
.ped h4{margin:0;font-size:1rem}.ped p{margin:2px 0 0;color:var(--gris);font-size:.85rem}
.etq{display:inline-block;font-size:.74rem;font-weight:700;padding:3px 8px;border-radius:6px;background:#e5efeb;color:var(--verde);margin:5px 4px 0 0}
.b4{display:grid;grid-template-columns:repeat(4,1fr);gap:6px;margin-top:10px}
.b4 button{border:2px solid var(--linea);background:#fff;border-radius:10px;padding:9px 4px;font-weight:700;cursor:pointer;font-size:.85rem}
.pie{display:flex;justify-content:space-between;margin-top:8px;font-size:.78rem;color:var(--gris);gap:8px;flex-wrap:wrap}.pie a{color:var(--verde);font-weight:700}
#aviso{position:fixed;left:50%;bottom:18px;transform:translateX(-50%);background:#1b2a28;color:#fff;padding:10px 16px;border-radius:9px;display:none;z-index:9}
.vacio{text-align:center;color:var(--gris);padding:30px}
.lu{display:block;font-size:.8rem;color:var(--gris);margin-bottom:4px}
@media(max-width:640px){header{flex-wrap:wrap;padding:12px}header h1{flex:1 1 55%;font-size:1rem}header a,header button{padding:6px 8px;font-size:.78rem}.tabs{flex-wrap:wrap}.tabs button,.tabs a.tablink{padding:8px 11px;font-size:.85rem}}
.tabs a.tablink{border:1.5px solid var(--linea);background:#fff;border-radius:10px;padding:9px 16px;font-weight:700;color:var(--verde);text-decoration:none;font-size:.92rem}
#vActas input{width:100%;padding:10px;border:1.5px solid var(--linea);border-radius:9px;font:inherit}
.acta{background:#fff;border:1px solid var(--linea);border-radius:12px;padding:14px;margin-bottom:10px}
.acta h4{margin:0;font-size:1rem}.firmas{margin-top:10px;border-top:1px solid var(--linea);padding-top:8px}
#vUsu input,#vUsu select{width:100%;padding:10px;border:1.5px solid var(--linea);border-radius:9px;font:inherit}
.tabla{background:#fff;border:1px solid var(--linea);border-radius:14px;overflow-x:auto;-webkit-overflow-scrolling:touch}
table{border-collapse:collapse;width:100%;min-width:980px;font-size:.88rem}
th{background:#f6f8f7;text-align:left;padding:12px;color:#33413e;font-size:.78rem;text-transform:uppercase;letter-spacing:.03em;border-bottom:2px solid var(--verde);white-space:nowrap}
td{padding:12px;border-bottom:1px solid var(--linea);vertical-align:top}
tr.alta td{background:#fff6e0}
.cod{font-weight:800;color:var(--verde);white-space:nowrap}.sub{color:var(--gris);font-size:.8rem;margin-top:3px;line-height:1.35}
.nom{font-weight:700}
.orig{font-weight:700}.orig:before{content:"📍 "}
.alerta{display:inline-block;margin-top:5px;font-size:.72rem;font-weight:800;color:#fff;background:var(--rojo);border-radius:5px;padding:3px 7px}
.alerta.amb{background:#f6e7cf;color:#8a5a00}
.chip{display:inline-block;font-size:.74rem;font-weight:800;padding:5px 10px;border-radius:999px;white-space:nowrap}
.e-en_espera{background:#fff3b0;color:#6b5800}.e-pendiente{background:#ffd8a8;color:#7a3e00}.e-aceptado{background:#2e7d5b;color:#fff}.e-no_corresponde{background:#d6ecf3;color:#0f5a70}.e-concluido{background:#e6e1f2;color:#4a3a7a}
.p0{background:var(--rojo);color:#fff}.p1{background:#f6e7cf;color:#8a5a00}.p2{background:#e5efeb;color:var(--verde)}
.acc2{display:flex;gap:6px}.acc2 a,.acc2 button{border:1.5px solid var(--linea);background:#fff;border-radius:9px;padding:7px 10px;font-weight:700;font-size:.8rem;cursor:pointer;color:var(--tinta);text-decoration:none;white-space:nowrap}
.acc2 button.cambiar{border-color:var(--verde);color:var(--verde)}
#modal{position:fixed;inset:0;background:rgba(10,20,18,.55);display:none;align-items:center;justify-content:center;z-index:20;padding:16px}
#modal.on{display:flex}
#modal .caja{background:#fff;border-radius:16px;padding:20px;width:100%;max-width:420px;max-height:92vh;overflow:auto}
#modal h3{margin:0 0 4px;font-size:1.1rem}#modal .info{margin:0 0 12px;color:var(--gris);font-size:.86rem}
#modal label{display:block;font-weight:700;font-size:.85rem;margin:12px 0 5px}
#modal input{width:100%;padding:11px;border:1.5px solid var(--linea);border-radius:9px;font:inherit}
.opciones{display:grid;grid-template-columns:1fr 1fr;gap:8px}
.opciones button{border:2px solid transparent;border-radius:10px;padding:11px 6px;font-weight:800;cursor:pointer;font-size:.86rem;opacity:.55}
.opciones button.on{opacity:1;border-color:var(--tinta)}
#modal .acc{display:flex;gap:8px;margin-top:16px}#modal .acc button{flex:1;padding:12px;border-radius:9px;font-weight:800;border:1.5px solid var(--linea);background:#fff;cursor:pointer}
#modal .acc .ok{background:var(--verde);color:#fff;border-color:var(--verde)}
</style></head><body>
<header><img src="/icon/logo-mark.png" alt="HEQI" style="height:42px;background:#fff;border-radius:8px;padding:3px 5px;vertical-align:middle;margin-right:10px"><h1>Gestión Hospitalaria<small>HEQI Ingavi - Sesión: {{usuario}}</small></h1>
<button id="bSonido">🔔 Activar alarma</button><a href="/planilla.csv" id="lPlanilla">Planilla</a><a href="/logout">Salir</a></header>
<div class="wrap">
  <div class="tabs"><button data-t="pedidos" class="on">🚑 Traslados <span class="num" id="nEsp"></span></button><button data-t="estad">Estadísticas</button><a href="/camas" class="tablink">🛏 Comando de Camas</a><button data-t="actas" id="tabActas" style="display:none">📝 Actas</button><button data-t="usu" id="tabUsu" style="display:none">👥 Usuarios</button></div>

  <section id="vPedidos">
    <div class="filtros" id="filtros"></div>
    <input type="search" id="buscar" placeholder="Buscar paciente, CI, institución o diagnóstico">
    <div id="lista"></div>
  </section>

  <section id="vActas" hidden>
    <div class="card" style="margin-bottom:14px">
      <h3 style="margin:0 0 10px;font-size:1rem">Nueva acta para firmar</h3>
      <div style="display:grid;grid-template-columns:repeat(auto-fit,minmax(200px,1fr));gap:10px;align-items:end">
        <div><label class="lu">Título / N° de acta *</label><input id="aT" placeholder="Ej.: Acta MECIP 261/2026"></div>
        <div><label class="lu">Asunto</label><input id="aA" placeholder="Ej.: Reunión de planificación"></div>
        <div><label class="lu">Lugar</label><input id="aL" placeholder="Ej.: Sala de reuniones HEQI"></div>
        <div><label class="lu">Fecha</label><input id="aF" type="date"></div>
        <div><label class="lu">Hora</label><input id="aH" type="time"></div>
        <div><label class="lu">PDF del acta (hasta 3,5 MB)</label><input id="aP" type="file" accept="application/pdf"></div>
        <button class="btn" id="aG" style="background:var(--verde);color:#fff;border-color:var(--verde)">Crear acta y link</button>
      </div>
    </div>
    <div id="aLista"></div>
  </section>
  <section id="vUsu" hidden>
    <div class="card" id="uPinBox" style="max-width:380px;margin:0 auto 14px" hidden>
      <h3 style="margin:0 0 6px;font-size:1rem">🔒 Zona de usuarios</h3><p class="sub" style="margin:0 0 10px">Ingresá tu PIN de administrador absoluto.</p>
      <input id="uPin" type="password" inputmode="numeric" autocomplete="off" placeholder="PIN" style="width:100%;padding:11px;border:1.5px solid var(--linea);border-radius:9px;font:inherit">
      <button class="btn" id="uPinOk" style="width:100%;margin-top:10px;background:var(--verde);color:#fff;border-color:var(--verde)">Entrar</button>
    </div>
    <div id="uZona" hidden>
    <div class="card" style="margin-bottom:14px">
      <h3 style="margin:0 0 10px;font-size:1rem">Agregar o editar usuario</h3>
      <div style="display:grid;grid-template-columns:repeat(auto-fit,minmax(180px,1fr));gap:10px;align-items:end">
        <div><label class="lu">Usuario</label><input id="uU" placeholder="ej.: drgomez" autocomplete="off"></div>
        <div><label class="lu">Nombre</label><input id="uN" placeholder="Dr. Gómez - Guardia"></div>
        <div><label class="lu">Contraseña (mín. 6)</label><input id="uC" type="password" autocomplete="new-password" placeholder="Al editar: vacío = no cambia"></div>
        <div><label class="lu">Rol</label><select id="uR"><option value="modulos">Usuario por paneles</option><option value="sub">Sub-administrador (ve todo, no crea usuarios)</option><option value="absoluto">Administrador absoluto</option></select></div>
      </div>
      <div id="uModsW" style="margin-top:12px"><label class="lu">Paneles a los que tiene acceso</label><div id="uMods" style="display:flex;gap:14px;flex-wrap:wrap"></div></div>
      <button class="btn" id="uG" style="margin-top:12px;background:var(--verde);color:#fff;border-color:var(--verde)">Guardar usuario</button>
      <p class="sub" style="margin-top:8px"><b>Absoluto:</b> todo, incluidos usuarios. <b>Sub-administrador:</b> todos los paneles, sin usuarios. <b>Por paneles:</b> solo los paneles marcados.</p>
    </div>
    <div id="uLista"></div>
    </div>
  </section>
  <section id="vEstad" hidden>
    <div class="card periodo">
      <div><label>Desde</label><input type="date" id="desde"></div>
      <div><label>Hasta</label><input type="date" id="hasta"></div>
      <button class="btn" id="bLimpiar">Limpiar</button><div class="esp"></div>
      <button class="btn" id="bAct">⟳ Actualizar</button>
    </div>
    <div class="kpis" id="kpis"></div>
    <div class="graf">
      <div class="card"><h3>Pedidos por especialidad: aceptados vs. servicio no disponible</h3><div id="gEsp"></div>
        <div class="leyenda"><span><i style="background:var(--verde)"></i>Aceptados</span><span><i style="background:var(--rojo)"></i>Servicio no disponible</span><span><i style="background:var(--pe)"></i>En espera / pendientes</span></div></div>
      <div class="card"><h3>Pedidos por institución de origen</h3><div id="gInst"></div></div>
      <div class="card"><h3>Pedidos por complejidad</h3><div id="gComp"></div></div>
      <div class="card"><h3>Pedidos por día</h3><div id="gDia"></div></div>
    </div>
  </section>
</div>
<div id="aviso"></div>
<div id="modal" role="dialog" aria-modal="true"><div class="caja">
  <h3>Cambiar estado</h3><p class="info" id="mInfo"></p>
  <div class="opciones" id="mOpc"></div>
  <div id="mMedWrap"><label for="mMed">Médico que acepta *</label><input id="mMed" placeholder="Ej.: Dr. Gómez - Traumatología"></div>
  <div id="mConWrap"><label for="mCon">¿Dónde concluyó? *</label>
    <select id="mCon" style="width:100%;padding:11px;border:1.5px solid var(--linea);border-radius:9px;font:inherit"><option value="">Elegir…</option><option>Resuelto en origen</option><option>Trasladado a otro centro</option><option>Otro motivo</option></select>
    <input id="mConDet" placeholder="Detalle: centro o motivo (ej.: Hospital Central, alta, fallecido)" style="margin-top:8px"></div>
  <label for="mPin">PIN para guardar *</label><input id="mPin" type="password" autocomplete="off" placeholder="PIN">
  <div class="acc"><button id="mNo">Cancelar</button><button class="ok" id="mOk">Guardar</button></div>
</div></div>
<script>
const DEMO=false;
const ROL='{{rol}}';const PERMS={{perms|tojson}};const MODS={{mods|tojson}};const ROLES={{roles|tojson}};
const EST={en_espera:['En espera','--es'],pendiente:['Pendiente','--pe'],aceptado:['Aceptado','--ok'],no_corresponde:['Servicio no disponible - red IPS','--na'],concluido:['Concluido fuera de Ingavi','--pe']};
let DATA=[], tab='pedidos', ver='en_espera', ultimoId=null, sonido=false, ctx=null;


const $=id=>document.getElementById(id);
const esc=s=>String(s??'').replace(/[&<>"]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
function aviso(t){ const a=$('aviso'); a.textContent=t; a.style.display='block'; clearTimeout(aviso.t); aviso.t=setTimeout(()=>a.style.display='none',2500); }
function pitido(){ if(!sonido||!ctx) return; [0,.35,.7].forEach(t=>{ const o=ctx.createOscillator(),g=ctx.createGain(); o.frequency.value=880; o.connect(g); g.connect(ctx.destination); g.gain.setValueAtTime(.25,ctx.currentTime+t); g.gain.exponentialRampToValueAtTime(.001,ctx.currentTime+t+.3); o.start(ctx.currentTime+t); o.stop(ctx.currentTime+t+.3); }); }
$('bSonido').onclick=()=>{ ctx=ctx||new (window.AudioContext||window.webkitAudioContext)(); sonido=true; pitido(); $('bSonido').textContent='🔔 Alarma activa'; if('Notification' in window&&Notification.permission==='default') Notification.requestPermission(); };
function prioridad(d){
  if(d.rea==='Sí') return ['ALTA',0,'Requiere REA / UTI'];
  if(d.complejidad==='Alta'||(+d.news2>=7)) return ['ALTA',0,'NEWS2 '+(d.news2||'')+' - evaluación multidisciplinaria'];
  if(d.complejidad==='Media'||(+d.news2>=5)) return ['MEDIA',1,'NEWS2 '+(d.news2||'')];
  return ['BAJA',2,''];
}
const rojo=d=>prioridad(d)[1]===0;
const codigo=d=>'HEQI-'+String(d.recibido||'').slice(0,4)+'-'+String(d.id).padStart(4,'0');
const fcorta=s=>{ const t=String(s||''); return t.length>=16?t.slice(8,10)+'/'+t.slice(5,7)+' '+t.slice(11,16):t; };
const fecha=s=>new Date(String(s).replace(' ','T'));
const minutos=d=>d.decidido_en?Math.round((fecha(d.decidido_en)-fecha(d.recibido))/6e4):null;

async function cargar(){
  if(!DEMO){ try{ const r=await fetch('/api/lista'); if(r.status===401){ location='/login'; return; } DATA=await r.json(); }catch(e){ return; } }
  const maxId=DATA.length?Math.max(...DATA.map(d=>d.id)):0;
  if(ultimoId!==null&&maxId>ultimoId){ const n=DATA.filter(d=>d.id>ultimoId); pitido(); aviso(n.length+' pedido(s) nuevo(s)');
    if('Notification' in window&&Notification.permission==='granted') n.forEach(d=>new Notification('Nuevo pedido de traslado'+(rojo(d)?' - COMPLEJIDAD ALTA':''),{body:d.paciente+' - '+d.institucion+' - '+d.diagnostico})); }
  ultimoId=maxId; pintar();
}
const ICO={en_espera:'⏳',pendiente:'🕓',aceptado:'✅',no_corresponde:'↪',concluido:'🏁'};
let cambio=null;
function abrirCambio(id){
  const d=DATA.find(x=>x.id===id); if(!d) return; cambio={id,estado:d.estado};
  $('mInfo').innerHTML=`<b>${codigo(d)}</b> - ${esc(d.paciente)}<br>📍 ${esc(d.institucion||'')} - ${esc(d.diagnostico||'')}`;
  $('mMed').value=d.medico_acepta||''; $('mPin').value=''; $('mCon').value=''; $('mConDet').value=''; pintarOpc(); $('modal').classList.add('on');
}
function pintarOpc(){
  $('mOpc').innerHTML=Object.keys(EST).map(k=>`<button data-k="${k}" class="e-${k} ${cambio.estado===k?'on':''}">${ICO[k]} ${EST[k][0]}</button>`).join('');
  $('mOpc').querySelectorAll('button').forEach(b=>b.onclick=()=>{ cambio.estado=b.dataset.k; pintarOpc(); });
  $('mMedWrap').style.display=cambio.estado==='aceptado'?'':'none';
  $('mConWrap').style.display=cambio.estado==='concluido'?'':'none';
}
$('mNo').onclick=()=>{ $('modal').classList.remove('on'); cambio=null; };
$('mOk').onclick=async()=>{
  if(!cambio) return; const {id,estado}=cambio, medico=$('mMed').value.trim(), pin=$('mPin').value;
  if(estado==='aceptado'&&!medico){ aviso('Escribí el médico que acepta'); $('mMed').focus(); return; }
  let donde='';
  if(estado==='concluido'){ if(!$('mCon').value){ aviso('Elegí dónde concluyó'); return; } donde=$('mCon').value+($('mConDet').value.trim()?': '+$('mConDet').value.trim():''); if($('mCon').value!=='Resuelto en origen'&&!$('mConDet').value.trim()){ aviso('Escribí el centro o el motivo'); $('mConDet').focus(); return; } }
  if(!pin.trim()){ aviso('Escribí el PIN'); $('mPin').focus(); return; }
  if(DEMO){ if(pin.trim().toLowerCase()!=='heqi'){ aviso('PIN incorrecto: no se guardó'); return; }
    const d=DATA.find(x=>x.id===id); d.estado=estado; d.medico_acepta=estado==='aceptado'?medico:''; d.concluido_donde=estado==='concluido'?donde:''; d.decidido_por=estado==='en_espera'?'':'ejemplo'; d.decidido_en=estado==='en_espera'?'':new Date().toISOString().slice(0,19).replace('T',' ');
    $('modal').classList.remove('on'); aviso('Guardado: '+EST[estado][0]); pintar(); return; }
  const r=await fetch('/api/estado/'+id,{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({estado,medico_acepta:medico,concluido_donde:donde,pin})});
  if(r.status===403){ aviso('PIN incorrecto: no se guardó'); $('mPin').value=''; $('mPin').focus(); return; }
  if(r.ok){ $('modal').classList.remove('on'); cambio=null; aviso('Guardado: '+EST[estado][0]); cargar(); } else aviso('No se pudo guardar');
};
document.querySelectorAll('.tabs button').forEach(b=>b.onclick=()=>{ tab=b.dataset.t; document.querySelectorAll('.tabs button').forEach(x=>x.classList.toggle('on',x===b)); $('vPedidos').hidden=tab!=='pedidos'; $('vEstad').hidden=tab!=='estad'; $('vUsu').hidden=tab!=='usu'; $('vActas').hidden=tab!=='actas'; if(tab==='usu') cargarUsuarios(); if(tab==='actas') cargarActas(); pintar(); });

function pintar(){ const enEsp=DATA.filter(d=>d.estado==='en_espera').length; $('nEsp').textContent=enEsp||''; $('nEsp').style.display=enEsp?'':'none';
  document.title=(enEsp?'('+enEsp+') ':'')+'Gestión Hospitalaria - HEQI'; if(tab==='pedidos') pintarPedidos(); else if(tab==='estad') pintarEstad(); }

function pintarPedidos(){
  const c=k=>DATA.filter(d=>d.estado===k).length;
  $('filtros').innerHTML=[['en_espera','En espera'],['pendiente','Pendientes'],['aceptado','Registro de aceptados'],['no_corresponde','Servicio no disponible'],['concluido','Concluidos fuera'],['todos','Todos']]
    .map(([k,t])=>`<button data-k="${k}" class="${ver===k?'on':''}">${t} (${k==='todos'?DATA.length:c(k)})</button>`).join('');
  $('filtros').querySelectorAll('button').forEach(b=>b.onclick=()=>{ ver=b.dataset.k; pintarPedidos(); });
  const qq=$('buscar').value.toLowerCase();
  const L=DATA.filter(d=>(ver==='todos'||d.estado===ver)&&(!qq||[d.paciente,d.ci,d.institucion,d.diagnostico,codigo(d)].join(' ').toLowerCase().includes(qq)))
    .sort((a,b)=>{ const ab=x=>x.estado==='en_espera'||x.estado==='pendiente'; return (ab(a)&&ab(b)?prioridad(a)[1]-prioridad(b)[1]:0)||(b.id-a.id); });
  if(!L.length){ $('lista').innerHTML='<div class="vacio">No hay pedidos en esta lista.</div>'; return; }
  $('lista').innerHTML=`<div class="tabla"><table><thead><tr><th>Código</th><th>Paciente</th><th>Origen / Remitente</th><th>Diagnóstico</th><th>Prioridad</th><th>Estado</th><th>Acciones</th></tr></thead><tbody>`+
  L.slice(0,500).map(d=>{ const [pt,pn,pm]=prioridad(d);
    return `<tr class="${pn===0?'alta':''}">
      <td><div class="cod">${codigo(d)}</div><div class="sub">${fcorta(d.recibido)}</div></td>
      <td><div class="nom">${esc(d.paciente)}</div><div class="sub">${d.edad?esc(d.edad)+' años':''}${d.ci?' · CI '+esc(d.ci):''}</div></td>
      <td><div class="orig">${esc(d.institucion||'Sin dato')}</div><div class="sub">${d.medico?esc(d.medico):''}${d.telefono?'<br>Tel. '+esc(d.telefono):''}</div></td>
      <td><div class="nom">${esc(d.diagnostico)}</div><div class="sub">${d.cie10?'CIE-10 '+esc(d.cie10)+' · ':''}${esc(d.especialidad||'')}</div>
        ${d.rea==='Sí'?'<span class="alerta">⚡ REQUIERE REA / UTI</span> ':''}${(+d.news2>=7||d.complejidad==='Alta')?'<span class="alerta">⚠ NEWS2 '+esc(d.news2)+' - EVALUACIÓN MULTIDISCIPLINARIA</span>':(+d.news2>=5?'<span class="alerta amb">NEWS2 '+esc(d.news2)+' - riesgo medio</span>':'')}</td>
      <td><span class="chip p${pn}">${pt}</span>${pm?`<div class="sub">${esc(pm)}</div>`:''}</td>
      <td><span class="chip e-${d.estado}">${EST[d.estado]?EST[d.estado][0]:esc(d.estado)}</span>
        ${d.estado==='aceptado'&&d.medico_acepta?`<div class="sub">✅ Acepta: <b>${esc(d.medico_acepta)}</b></div>`:''}${d.estado==='concluido'&&d.concluido_donde?`<div class="sub">🏁 ${esc(d.concluido_donde)}</div>`:''}
        ${d.decidido_en?`<div class="sub">${fcorta(d.decidido_en)} · ${esc(d.decidido_por||'')}${minutos(d)!==null?' · '+minutos(d)+' min':''}</div>`:''}</td>
      <td><div class="acc2">${DEMO?'':(d.pdf_nombre?`<a href="/pdf/${d.id}" target="_blank" title="Ver PDF">📄 PDF</a>`:'<span class="sub" title="Llegó sin PDF">sin PDF</span>')}<button class="cambiar" data-id="${d.id}">✏️ Estado</button></div></td></tr>`; }).join('')+`</tbody></table></div>`;
  $('lista').querySelectorAll('button.cambiar').forEach(b=>b.onclick=()=>abrirCambio(+b.dataset.id));
}
$('buscar').oninput=pintarPedidos;

// ---------- Estadísticas ----------
const hoyISO=()=>new Date().toISOString().slice(0,10);
function rangoDefecto(){ const d=new Date(); d.setDate(1); $('desde').value=d.toISOString().slice(0,10); $('hasta').value=hoyISO(); }
rangoDefecto(); $('bLimpiar').onclick=()=>{ rangoDefecto(); pintarEstad(); }; $('bAct').onclick=()=>cargar(); $('desde').onchange=pintarEstad; $('hasta').onchange=pintarEstad;
function enRango(){ const a=$('desde').value, b=$('hasta').value; return DATA.filter(d=>{ const f=String(d.recibido).slice(0,10); return (!a||f>=a)&&(!b||f<=b); }); }
function barrasV(cats,series,alto=230){
  const W=560,H=alto,pl=40,pb=70,pt=10,max=Math.max(1,...series.flatMap(s=>s.v)); const paso=Math.ceil(max/5)||1, top=paso*5;
  const gw=(W-pl-10)/cats.length, bw=Math.min(26,(gw-10)/series.length);
  let s=`<svg viewBox="0 0 ${W} ${H}" width="100%" role="img">`;
  for(let i=0;i<=5;i++){ const y=pt+(H-pt-pb)*(1-i/5); s+=`<line x1="${pl}" x2="${W-6}" y1="${y}" y2="${y}" stroke="#e6ebea"/><text x="${pl-6}" y="${y+4}" font-size="11" text-anchor="end" fill="#5b6b70">${paso*i}</text>`; }
  cats.forEach((c,i)=>{ const x0=pl+i*gw+(gw-bw*series.length)/2;
    series.forEach((se,j)=>{ const h=(H-pt-pb)*se.v[i]/top; s+=`<rect x="${x0+j*bw}" y="${H-pb-h}" width="${bw-3}" height="${h}" rx="3" fill="${se.c}"><title>${c}: ${se.v[i]}</title></rect>`; });
    s+=`<text transform="translate(${pl+i*gw+gw/2},${H-pb+14}) rotate(-28)" font-size="11" text-anchor="end" fill="#33413e">${esc(c)}</text>`; });
  return s+'</svg>';
}
function barrasH(items,color){
  const W=560,fila=30,H=Math.max(60,items.length*fila+24),pl=190,max=Math.max(1,...items.map(x=>x[1]));
  let s=`<svg viewBox="0 0 ${W} ${H}" width="100%" role="img">`;
  items.forEach(([t,v],i)=>{ const y=8+i*fila, w=(W-pl-50)*v/max; s+=`<text x="${pl-8}" y="${y+16}" font-size="12" text-anchor="end" fill="#33413e">${esc(t.length>28?t.slice(0,27)+'…':t)}</text><rect x="${pl}" y="${y+3}" width="${w}" height="${fila-10}" rx="4" fill="${color}"/><text x="${pl+w+6}" y="${y+16}" font-size="12" fill="#33413e">${v}</text>`; });
  return s+'</svg>';
}
function pintarEstad(){
  const P=enRango(), c=k=>P.filter(d=>d.estado===k).length, dec=c('aceptado')+c('no_corresponde');
  const t=P.map(minutos).filter(x=>x!==null&&x>=0), tm=t.length?Math.round(t.reduce((a,b)=>a+b,0)/t.length):null;
  $('kpis').innerHTML=[[P.length,'Recibidos','var(--tinta)'],[c('aceptado'),'Aceptados','var(--verde2)'],[c('no_corresponde'),'Servicio no disponible','var(--rojo)'],[c('concluido'),'Concluidos fuera de Ingavi','#4a3a7a'],
    [dec?Math.round(c('aceptado')/dec*100)+'%':'-','Tasa de aceptación','var(--ambar)'],[c('en_espera')+c('pendiente'),'En espera / pendientes','var(--pe)'],[tm!==null?tm+' min':'-','Tiempo medio de respuesta','var(--verde)']]
    .map(([n,tx,col])=>`<div class="card kpi"><b style="color:${col}">${n}</b><span>${tx}</span></div>`).join('');
  const esps=['Polivalente','Cirugía General y Trauma','Traumatología','Urología','Valoración individual','No puede resolverse'];
  const grupo=d=>/^VALORACI/.test(d.especialidad)?'Valoración individual':/^(NO PUEDE|SOLICITUD|DIAGN|REQUIERE|NO CORR)/.test(d.especialidad)?'No puede resolverse':d.especialidad;
  $('gEsp').innerHTML=barrasV(esps.map(e=>e.replace('Cirugía General y Trauma','Cirugía General')),[
    {c:'#1d4a42',v:esps.map(e=>P.filter(d=>grupo(d)===e&&d.estado==='aceptado').length)},
    {c:'#b03a2e',v:esps.map(e=>P.filter(d=>grupo(d)===e&&d.estado==='no_corresponde').length)},
    {c:'#9aa8a5',v:esps.map(e=>P.filter(d=>grupo(d)===e&&(d.estado==='en_espera'||d.estado==='pendiente')).length)}]);
  const porI={}; P.forEach(d=>porI[d.institucion||'Sin dato']=(porI[d.institucion||'Sin dato']||0)+1);
  $('gInst').innerHTML=barrasH(Object.entries(porI).sort((a,b)=>b[1]-a[1]).slice(0,10),'#2e7d5b');
  $('gComp').innerHTML=barrasH(['Baja','Media','Alta'].map(k=>[k,P.filter(d=>d.complejidad===k).length]),'#b7791f');
  const dias={}; P.forEach(d=>{ const f=String(d.recibido).slice(5,10).split('-').reverse().join('/'); dias[f]=(dias[f]||0)+1; });
  const ks=Object.keys(dias).sort((a,b)=>a.split('/').reverse().join('').localeCompare(b.split('/').reverse().join(''))).slice(-31);
  $('gDia').innerHTML=barrasV(ks,[{c:'#1d4a42',v:ks.map(k=>dias[k])}],220);
}
const TIENE=m=>PERMS.includes(m);
(function(){ const t=q=>document.querySelector(q);
  if(!TIENE('traslados')){ t('.tabs button[data-t="pedidos"]').style.display='none'; t('.tabs button[data-t="estad"]').style.display='none'; ['bSonido','lPlanilla'].forEach(i=>$(i)&&($(i).style.display='none')); $('vPedidos').hidden=true; }
  if(!TIENE('camas')) t('.tabs a.tablink').style.display='none';
  if(TIENE('actas')) $('tabActas').style.display='';
  if(ROL==='absoluto'||ROL==='admin') $('tabUsu').style.display='';
  if(!TIENE('traslados')){ const prim=[...document.querySelectorAll('.tabs button')].find(b=>b.style.display!=='none'); if(prim) setTimeout(()=>prim.click(),0); }
})();
$('uR').onchange=()=>{ $('uModsW').style.display=$('uR').value==='modulos'?'':'none'; };
$('uMods').innerHTML=MODS.map(([k,n])=>`<label style="display:flex;gap:6px;align-items:center;font-weight:600"><input type="checkbox" value="${k}" style="width:auto">${n}</label>`).join('');
$('uPinOk').onclick=async()=>{ const r=await fetch('/api/usuarios/pin',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({pin:$('uPin').value})}); const j=await r.json().catch(()=>({}));
  $('uPin').value=''; if(r.ok){ aviso('Acceso a usuarios habilitado por 15 minutos'); cargarUsuarios(); } else aviso(j.error||'PIN incorrecto'); };
$('uPin').onkeydown=e=>{ if(e.key==='Enter') $('uPinOk').click(); };
async function cargarUsuarios(){
  const r=await fetch('/api/usuarios'); const jj=r.ok?null:await r.json().catch(()=>({}));
  if(!r.ok&&jj&&jj.pin){ $('uPinBox').hidden=false; $('uZona').hidden=true; setTimeout(()=>$('uPin').focus(),50); return; }
  if(!r.ok){ $('uZona').hidden=false; $('uPinBox').hidden=true; $('uLista').innerHTML='<div class="vacio">Solo el administrador absoluto.</div>'; return; }
  $('uPinBox').hidden=true; $('uZona').hidden=false; $('uModsW').style.display=$('uR').value==='modulos'?'':'none';
  const U=await r.json();
  const nomMod=k=>(MODS.find(m=>m[0]===k)||[k,k])[1];
  $('uLista').innerHTML=`<div class="tabla"><table style="min-width:600px"><thead><tr><th>Usuario</th><th>Nombre</th><th>Rol y permisos</th><th>Creado</th><th></th></tr></thead><tbody>`+
    U.map(u=>`<tr><td class="nom">${esc(u.usuario)}</td><td>${esc(u.nombre)}</td><td><span class="chip ${u.rol==='absoluto'?'p0':u.rol==='sub'?'p1':'p2'}">${esc(ROLES[u.rol]||u.rol)}</span>${u.rol==='modulos'?'<div class="sub">'+(u.modulos||[]).map(nomMod).join(' · ')+'</div>':''}</td><td class="sub">${esc(u.creado)}</td>
      <td>${u.fijo?'<span class="sub">fijo</span>':`<div class="acc2"><button data-u="${esc(u.usuario)}" class="uEd">✏️ Editar</button><button data-u="${esc(u.usuario)}" class="uBo">🗑 Borrar</button></div>`}</td></tr>`).join('')+`</tbody></table></div>`;
  $('uLista').querySelectorAll('.uEd').forEach(b=>b.onclick=()=>{ const u=U.find(x=>x.usuario===b.dataset.u); $('uU').value=u.usuario; $('uN').value=u.nombre||''; $('uR').value=u.rol; $('uC').value=''; $('uModsW').style.display=u.rol==='modulos'?'':'none'; $('uMods').querySelectorAll('input').forEach(c=>c.checked=(u.modulos||[]).includes(c.value)); window.scrollTo(0,0); aviso('Editá y guardá (contraseña vacía = no cambia)'); });
  $('uLista').querySelectorAll('.uBo').forEach(b=>b.onclick=async()=>{ if(!confirm('¿Borrar el usuario '+b.dataset.u+'?')) return;
    const r=await fetch('/api/usuarios/'+encodeURIComponent(b.dataset.u),{method:'DELETE'}); const j=await r.json().catch(()=>({})); aviso(r.ok?'Usuario borrado':(j.error||'No se pudo borrar')); cargarUsuarios(); });
}
$('uG').onclick=async()=>{
  const body={usuario:$('uU').value.trim(),nombre:$('uN').value.trim(),clave:$('uC').value,rol:$('uR').value,modulos:[...$('uMods').querySelectorAll('input:checked')].map(c=>c.value)};
  if(!body.usuario){ aviso('Completá el usuario'); return; }
  if(body.rol==='modulos'&&!body.modulos.length){ aviso('Marcá al menos un panel'); return; }
  const r=await fetch('/api/usuarios',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(body)}); const j=await r.json().catch(()=>({}));
  if(r.ok){ aviso('Usuario guardado: '+body.usuario); $('uU').value=$('uN').value=$('uC').value=''; $('uMods').querySelectorAll('input').forEach(c=>c.checked=false); cargarUsuarios(); } else if(j.pin){ cargarUsuarios(); } else aviso(j.error||'No se pudo guardar');
};
async function cargarActas(){
  const r=await fetch('/api/actas'); if(!r.ok){ $('aLista').innerHTML='<div class="vacio">Solo administradores.</div>'; return; }
  const A=await r.json();
  if(!A.length){ $('aLista').innerHTML='<div class="vacio">Todavía no creaste actas.</div>'; return; }
  $('aLista').innerHTML=A.map(a=>{ const link=location.origin+'/acta/'+a.codigo;
    return `<div class="acta"><h4>${esc(a.titulo)} <span class="chip ${a.abierta?'e-aceptado':'e-no_corresponde'}" style="margin-left:6px">${a.abierta?'Abierta':'Cerrada'}</span></h4>
      <div class="sub">${esc(a.asunto||'')}${a.lugar?' · '+esc(a.lugar):''}${a.fecha?' · '+esc(a.fecha):''}${a.hora?' '+esc(a.hora):''}${a.pdf_nombre?' · 📄 PDF adjunto':' · sin PDF'}</div>
      <div style="margin:8px 0;font-weight:800">✍️ ${a.firmas} firma(s)</div>
      <div class="sub" style="word-break:break-all">🔗 ${esc(link)}</div>
      <div class="acc2" style="flex-wrap:wrap;margin-top:10px">
        <button data-l="${esc(link)}" class="aCop">🔗 Copiar link</button>
        <a href="https://wa.me/?text=${encodeURIComponent('Acta para revisión y firma: '+a.titulo+'\n'+link)}" target="_blank">📲 WhatsApp</a>
        <button data-i="${a.id}" class="aVer">👥 Ver firmas</button>
        <a href="/actas/${a.id}/presentes" target="_blank">🖨 Hoja de presentes</a>
        <button data-i="${a.id}" data-ab="${a.abierta?0:1}" class="aCer">${a.abierta?'🔒 Cerrar firmas':'🔓 Reabrir'}</button>
        <button data-i="${a.id}" class="aBo">🗑 Borrar</button></div>
      <div class="firmas" id="fir${a.id}" hidden></div></div>`; }).join('');
  $('aLista').querySelectorAll('.aCop').forEach(b=>b.onclick=async()=>{ try{ await navigator.clipboard.writeText(b.dataset.l); aviso('Link copiado'); }catch(e){ prompt('Copiá el link:',b.dataset.l); } });
  $('aLista').querySelectorAll('.aCer').forEach(b=>b.onclick=async()=>{ await fetch('/api/actas/'+b.dataset.i,{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({abierta:b.dataset.ab==='1'})}); aviso(b.dataset.ab==='1'?'Acta reabierta':'Acta cerrada: no admite más firmas'); cargarActas(); });
  $('aLista').querySelectorAll('.aBo').forEach(b=>b.onclick=async()=>{ if(!confirm('¿Borrar el acta y TODAS sus firmas? No se puede deshacer.')) return; await fetch('/api/actas/'+b.dataset.i,{method:'DELETE'}); aviso('Acta borrada'); cargarActas(); });
  $('aLista').querySelectorAll('.aVer').forEach(b=>b.onclick=async()=>{ const box=$('fir'+b.dataset.i); if(!box.hidden){ box.hidden=true; return; }
    const F=await (await fetch('/api/actas/'+b.dataset.i+'/firmas')).json();
    box.innerHTML=F.length?F.map((f,k)=>`<div style="display:flex;justify-content:space-between;gap:8px;padding:6px 0;border-bottom:1px solid var(--linea)"><span><b>${k+1}. ${esc(f.nombre)} ${esc(f.apellido)}</b><span class="sub"> ${f.ci?'CI '+esc(f.ci)+' · ':''}${esc(f.cargo||f.dependencia||'')} · ${esc(f.fecha)}</span></span><button data-f="${f.id}" class="fBo" style="border:1.5px solid var(--linea);background:#fff;border-radius:8px">🗑</button></div>`).join(''):'<div class="sub">Sin firmas todavía.</div>';
    box.hidden=false;
    box.querySelectorAll('.fBo').forEach(x=>x.onclick=async()=>{ if(!confirm('¿Quitar esta firma?')) return; await fetch('/api/firmas/'+x.dataset.f,{method:'DELETE'}); aviso('Firma quitada'); cargarActas(); });
  });
}
$('aG').onclick=async()=>{
  if(!$('aT').value.trim()){ aviso('Escribí el título del acta'); return; }
  const fd=new FormData(); fd.append('titulo',$('aT').value); fd.append('asunto',$('aA').value); fd.append('lugar',$('aL').value); fd.append('fecha',$('aF').value?$('aF').value.split('-').reverse().join('/'):''); fd.append('hora',$('aH').value);
  const f=$('aP').files[0]; if(f){ if(f.size>3.5*1024*1024){ aviso('El PDF supera 3,5 MB'); return; } fd.append('pdf',f,f.name); }
  $('aG').disabled=true; const r=await fetch('/api/actas',{method:'POST',body:fd}); const j=await r.json().catch(()=>({})); $('aG').disabled=false;
  if(r.ok){ aviso('Acta creada: ya podés compartir el link'); ['aT','aA','aL','aF','aH','aP'].forEach(k=>$(k).value=''); cargarActas(); } else aviso(j.error||'No se pudo crear');
};
if(TIENE('traslados')){ cargar(); if(!DEMO) setInterval(cargar,15000); }
</script></body></html>
"""

iniciar()
if __name__ == '__main__':
    app.run(host='0.0.0.0', port=int(os.environ.get('PORT', 5000)))
