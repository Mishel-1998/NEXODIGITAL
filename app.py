# ==============================================================================
# PROYECTO: NEXODIGITAL - SOLUCIONES WEB Y COMERCIALES
# Control Principal de la Aplicación Flask (Backend)
# ==============================================================================
# Este archivo contiene la configuración central del servidor y los controladores
# (rutas y vistas) que gestionan la lógica de negocio para:
# 1. Página de inicio y presentación de la empresa
# 2. Catálogo y gestión de Servicios (CRUD) y sus Categorías (CRUD)
# 3. Directorio de Proveedores e infraestructura (CRUD)
# 4. Directorio de Clientes y cartera comercial (CRUD)
# 5. Emisión de Facturas y Cotizaciones (CRUD) con detalle relacional real
#
# Persistencia de datos: PostgreSQL, mediante conexion/conexion.py (conexión centralizada).
# Todas las tablas están relacionadas mediante claves primarias y foráneas:
#   clientes  <--(cliente_cedula)--  facturacion  --(factura_numero)-->  detalle_factura
#   tipos_servicio <--(tipo_servicio_id)--  servicios  <--(servicio_id)--  detalle_factura
# ==============================================================================

import os
import json
import math
import random
import re
import secrets
import psycopg2
from html.parser import HTMLParser
from functools import wraps
from datetime import date, datetime, timedelta
from urllib.parse import urljoin, urlencode, urlparse
from urllib.request import Request, urlopen
from flask import Flask, render_template, redirect, url_for, flash, request, session
from flask_login import LoginManager, login_user, logout_user, login_required, current_user
import bcrypt
from werkzeug.security import generate_password_hash, check_password_hash

# Modelos de Usuario, Roles, Permisos y Logs de Auditoría (RBAC)
from models import Usuario, User, Role, ActivityLog

# Importación de clases de formularios creadas con Flask-WTF
from forms.cliente_form import ClienteForm
from forms.tipo_negocio_form import TipoNegocioForm
from forms.servicio_form import ServicioForm
from forms.tipo_servicio_form import TipoServicioForm
from forms.proveedor_form import ProveedorForm
from forms.categoria_proveedor_form import CategoriaProveedorForm
from forms.facturacion_form import FacturacionForm
from forms.login_form import LoginForm
from forms.usuario_form import UsuarioForm
from forms.producto_form import ProductoForm
from forms.dos_factores_form import DosFactoresForm

# Módulo propio de conexión centralizada a PostgreSQL (carpeta conexion/)
from conexion.conexion import close_db_connection, get_db_connection


class _ImagenMetaParser(HTMLParser):
    """Obtiene la imagen principal declarada por una página web."""

    def __init__(self):
        super().__init__()
        self.imagen_url = None

    def handle_starttag(self, tag, attrs):
        if tag.lower() != 'meta' or self.imagen_url:
            return

        atributos = {clave.lower(): valor for clave, valor in attrs}
        referencia = (atributos.get('property') or atributos.get('name') or '').lower()
        if referencia in ('og:image', 'og:image:url', 'twitter:image', 'twitter:image:src'):
            self.imagen_url = atributos.get('content')


def resolver_url_imagen(valor):
    """Resuelve una imagen, conservando enlaces HTTPS válidos como respaldo."""
    url = (valor or '').strip()
    partes = urlparse(url)
    if partes.scheme not in ('http', 'https') or not partes.netloc:
        return None

    try:
        solicitud = Request(url, headers={'User-Agent': 'NexoDigital/1.0'})
        with urlopen(solicitud, timeout=8) as respuesta:
            tipo_contenido = respuesta.headers.get_content_type().lower()
            if tipo_contenido.startswith('image/'):
                return url

            if tipo_contenido in ('application/octet-stream', 'binary/octet-stream') and \
                    partes.path.lower().endswith(('.jpg', '.jpeg', '.png', '.gif', '.webp', '.avif')):
                return url

            if not (tipo_contenido.startswith('text/html') or tipo_contenido == 'application/xhtml+xml'):
                return None

            contenido = respuesta.read(2_000_000).decode(
                respuesta.headers.get_content_charset() or 'utf-8',
                errors='replace'
            )
            parser = _ImagenMetaParser()
            parser.feed(contenido)
            if parser.imagen_url:
                imagen = urljoin(url, parser.imagen_url.strip())
                imagen_partes = urlparse(imagen)
                if imagen_partes.scheme in ('http', 'https') and imagen_partes.netloc:
                    return imagen
    except Exception:
        # El enlace puede ser válido aunque el servidor remoto bloquee la
        # verificación desde backend. El navegador aún puede cargarlo.
        return url

    return url

# ------------------------------------------------------------------------------
# INICIALIZACIÓN DE LA APLICACIÓN FLASK
# ------------------------------------------------------------------------------
app = Flask(__name__)

# Clave secreta para la protección de sesiones y seguridad contra ataques CSRF en formularios
app.config['SECRET_KEY'] = os.getenv('SECRET_KEY')
if not app.config['SECRET_KEY']:
    if os.getenv('FLASK_ENV', 'development').lower() != 'production':
        app.config['SECRET_KEY'] = 'clave-local-nexodigital-2026'
    else:
        raise RuntimeError('SECRET_KEY es obligatoria fuera del modo de desarrollo.')

# Expiración automática de sesión tras 30 minutos de inactividad
app.config['PERMANENT_SESSION_LIFETIME'] = timedelta(minutes=30)
app.config['SESSION_COOKIE_HTTPONLY'] = True
app.config['SESSION_COOKIE_SAMESITE'] = 'Lax'
app.config['SESSION_COOKIE_SECURE'] = os.getenv('FLASK_ENV', 'development').lower() == 'production'
app.teardown_appcontext(close_db_connection)


@app.after_request
def asegurar_codificacion_utf8(response):
    """Declara UTF-8 explícitamente para que los textos en español no se deformen."""
    if response.mimetype == 'text/html':
        response.headers['Content-Type'] = 'text/html; charset=utf-8'
    return response


# ------------------------------------------------------------------------------
# CONFIGURACIÓN DE AUTENTICACIÓN (Flask-Login)
# ------------------------------------------------------------------------------
login_manager = LoginManager()
login_manager.init_app(app)
login_manager.login_view = 'login'
login_manager.login_message = 'Por favor inicia sesión para acceder a esta página.'
login_manager.login_message_category = 'warning'


@login_manager.user_loader
def load_user(user_id):
    """
    Función de callback requerida por Flask-Login para recuperar la instancia del
    usuario autenticado desde la base de datos a partir de su ID de sesión.
    """
    return Usuario.get_by_id(user_id)


# ------------------------------------------------------------------------------
# FUNCIONES AUXILIARES: CAPTCHA, AUDITORÍA Y CONTROL DE ACCESO (RBAC)
# ------------------------------------------------------------------------------

def generar_captcha():
    """Genera una operación aritmética aleatoria sencilla para verificación humana."""
    num1 = random.randint(1, 9)
    num2 = random.randint(1, 9)
    session['captcha_respuesta'] = str(num1 + num2)
    session['captcha_pregunta'] = f"{num1} + {num2} = ?"
    return session['captcha_pregunta']


def validar_password_segura(password):
    """Valida que la contraseña tenga longitud y complejidad suficientes."""
    if len(password) < 8:
        return False
    if not re.search(r'[A-Z]', password):
        return False
    if not re.search(r'[a-z]', password):
        return False
    if not re.search(r'\d', password):
        return False
    if not re.search(r'[^A-Za-z0-9]', password):
        return False
    return True


def validar_nombre_persona(valor):
    """Valida que un nombre o apellido contenga solo letras y espacios."""
    if not valor:
        return False
    return bool(re.fullmatch(r'[A-Za-zÁÉÍÓÚáéíóúÑñ\s]+', valor.strip()))


def validar_telefono_10_digitos(valor):
    """Valida que el teléfono tenga exactamente 10 dígitos numéricos."""
    if not valor:
        return False
    return bool(re.fullmatch(r'\d{10}', valor.strip()))


def verificar_recaptcha(token):
    """Valida reCAPTCHA si está configurado; si no, acepta la verificación local."""
    if not token:
        return True
    secret_key = os.getenv('RECAPTCHA_SECRET_KEY')
    if not secret_key:
        return True
    try:
        payload = urlencode({'secret': secret_key, 'response': token}).encode('utf-8')
        req = Request(
            'https://www.google.com/recaptcha/api/siteverify',
            data=payload,
            headers={'Content-Type': 'application/x-www-form-urlencoded'}
        )
        with urlopen(req, timeout=8) as response:
            data = json.loads(response.read().decode('utf-8'))
        return bool(data.get('success'))
    except Exception:
        return False


def registrar_log(accion, detalles=None):
    """Registra un evento en la tabla logs_actividad para auditoría de seguridad."""
    try:
        user_id = current_user.id if current_user.is_authenticated else None
        user_name = current_user.usuario if current_user.is_authenticated else session.get('temp_user_nombre', 'Anónimo')
        ip = request.remote_addr or '127.0.0.1'
        ActivityLog.registrar(user_id, user_name, accion, ip, detalles)
    except Exception as e:
        app.logger.warning(f"Error registrando log de auditoría: {e}")


def role_required(*roles_permitidos):
    """
    Decorador para proteger rutas según los roles asignados al usuario actual.
    Si el usuario no está autenticado, redirige al login.
    Si no posee los roles permitidos, registra la denegación en la auditoría y redirige.
    """
    def decorador(f):
        @wraps(f)
        def wrapper(*args, **kwargs):
            if not current_user.is_authenticated:
                flash('Por favor inicia sesión para acceder a esta página.', 'warning')
                return redirect(url_for('login', next=request.path))

            if current_user.rol_nombre not in roles_permitidos:
                registrar_log(
                    'ACCESO_DENEGADO_ROL',
                    f"Ruta: {request.path} | Rol actual: {current_user.rol_nombre} | Roles permitidos: {list(roles_permitidos)}"
                )
                flash(f'Acceso denegado: tu rol actual ({current_user.rol_nombre}) no tiene permisos para esta acción.', 'danger')
                return redirect(url_for('dashboard'))

            return f(*args, **kwargs)
        return wrapper
    return decorador


def permission_required(codigo_permiso):
    """
    Decorador para proteger rutas según la tabla relacional rol_permisos.
    Verifica que el rol asignado al usuario cuente con el permiso granular requerido.
    """
    def decorador(f):
        @wraps(f)
        def wrapper(*args, **kwargs):
            if not current_user.is_authenticated:
                flash('Por favor inicia sesión para acceder a esta página.', 'warning')
                return redirect(url_for('login', next=request.path))

            if not current_user.has_permission(codigo_permiso):
                registrar_log(
                    'ACCESO_DENEGADO_PERMISO',
                    f"Ruta: {request.path} | Permiso requerido: {codigo_permiso} | Rol: {current_user.rol_nombre}"
                )
                flash('Acceso denegado: no dispones de los permisos granulares necesarios para esta operación.', 'danger')
                return redirect(url_for('dashboard'))

            return f(*args, **kwargs)
        return wrapper
    return decorador


# ==============================================================================
# RUTAS PÚBLICAS Y VISTAS GENERALES
# ==============================================================================

def asegurar_servicios_minimos(cursor):
    """Garantiza que el catálogo persistido tenga al menos dos servicios."""
    cursor.execute('SELECT COUNT(*) AS total FROM servicios')
    faltantes = max(0, 2 - cursor.fetchone()['total'])
    if not faltantes:
        return

    catalogo_base = (
        ('Desarrollo Web', 'Página web empresarial', 250.00,
         'Diseño de un sitio web profesional, adaptable y optimizado.',
         'https://images.unsplash.com/photo-1547658719-da2b51169166'),
        ('Diseño y Catálogos', 'Catálogo digital', 120.00,
         'Catálogo de productos con precios y contacto directo por WhatsApp.',
         'https://images.unsplash.com/photo-1460925895917-afdab827c52f'),
    )
    for tipo_nombre, nombre, precio, descripcion, imagen in catalogo_base[:faltantes]:
        cursor.execute(
            '''INSERT INTO tipos_servicio (nombre) VALUES (%s)
               ON CONFLICT (nombre) DO NOTHING''',
            (tipo_nombre,)
        )
        cursor.execute('SELECT id FROM tipos_servicio WHERE nombre = %s', (tipo_nombre,))
        tipo_id = cursor.fetchone()['id']
        cursor.execute(
            '''INSERT INTO servicios
               (tipo_servicio_id, nombre, precio_base, imagen, descripcion, disponible)
               VALUES (%s, %s, %s, %s, %s, TRUE)''',
            (tipo_id, nombre, precio, imagen, descripcion)
        )


@app.route('/')
def inicio():
    """
    Ruta raíz del sitio web (Pública).
    Renderiza la vista principal con información de la empresa y catálogo destacado.
    Accesible libremente para visitantes no autenticados y usuarios con sesión activa.
    Los visitantes no autenticados ven solo servicios disponibles.
    Los usuarios autenticados pueden ver también los servicios que se darán más adelante.
    """
    mensaje = "Soluciones digitales para hacer crecer tu negocio"
    empresa = {
        "nombre": "Nexo Digital",
        "ubicacion": "Quito / Puyo - Ecuador",
        "modalidad": "Atención 100% en línea"
    }
    tipos_servicio = []
    servicios_destacados = []
    base_datos_disponible = False
    try:
        conn = get_db_connection()
        cursor = conn.cursor()
        asegurar_servicios_minimos(cursor)
        conn.commit()
        base_datos_disponible = True
        cursor.execute('SELECT * FROM tipos_servicio ORDER BY nombre')
        tipos_servicio = cursor.fetchall()

        # La portada muestra solo los tres servicios vigentes con mayor
        # demanda; el catálogo completo queda en /servicios.
        cursor.execute('''
            SELECT s.*, t.nombre AS tipo_nombre,
                   COUNT(d.id) AS unidades_solicitadas
            FROM servicios s
            JOIN tipos_servicio t ON s.tipo_servicio_id = t.id
            LEFT JOIN detalle_factura d ON d.servicio_id = s.id
            WHERE s.disponible = TRUE
            GROUP BY s.id, t.nombre
            ORDER BY unidades_solicitadas DESC, s.id ASC
            LIMIT 3
        ''')
        servicios_destacados = cursor.fetchall()
        cursor.close()
        conn.close()
    except psycopg2.Error:
        app.logger.exception('No se pudo cargar el catálogo de la portada.')

    return render_template(
        'index.html',
        mensaje=mensaje,
        empresa=empresa,
        servicios=servicios_destacados,
        tipos_servicio=tipos_servicio,
        base_datos_disponible=base_datos_disponible
    )



# ==============================================================================
# MÓDULO DE AUTENTICACIÓN, REGISTRO Y SEGURIDAD (Semana 14 & RBAC)
# ==============================================================================

@app.route('/registro', methods=['GET', 'POST'])
def registro():
    """
    Ruta para el registro de nuevos usuarios con validación de seguridad,
    mayoría de edad y formulario completo.
    """
    if current_user.is_authenticated:
        return redirect(url_for('dashboard'))

    form = UsuarioForm()
    try:
        roles_bd = Role.get_all()
    except Exception:
        app.logger.exception('No se pudieron cargar los roles durante el registro.')
        flash('No se pudo conectar con la base de datos. Revisa DATABASE_URL y los logs de Render.', 'danger')
        return render_template(
            '500.html',
            diagnostico='La base de datos no respondió al cargar los roles.'
        ), 503
    form.rol_id.choices = [(r['id'], r['nombre']) for r in roles_bd]

    if request.method == 'GET':
        pregunta = generar_captcha()
        form.captcha_pregunta.data = pregunta
        return render_template('registro.html', form=form, captcha_pregunta_texto=pregunta)

    if form.validate_on_submit():
        token_recaptcha = (form.recaptcha_token.data or request.form.get('g-recaptcha-response') or '').strip()
        if not verificar_recaptcha(token_recaptcha):
            flash('La validación anti-bot falló. Inténtalo nuevamente.', 'danger')
            pregunta = generar_captcha()
            form.captcha_pregunta.data = pregunta
            return render_template('registro.html', form=form, captcha_pregunta_texto=pregunta)

        respuesta_esperada = session.get('captcha_respuesta')
        respuesta_usuario = (form.captcha_respuesta.data or '').strip()
        if not respuesta_esperada or respuesta_usuario != respuesta_esperada:
            flash('La respuesta de verificación anti-bot es incorrecta.', 'danger')
            pregunta = generar_captcha()
            form.captcha_pregunta.data = pregunta
            return render_template('registro.html', form=form, captcha_pregunta_texto=pregunta)

        usuario_limpio = form.usuario.data.strip()
        correo_limpio = form.correo.data.strip().lower()
        nombres_limpios = form.nombres.data.strip()
        apellidos_limpios = form.apellidos.data.strip()
        telefono_limpio = (form.telefono.data or '').strip()

        if not validar_nombre_persona(nombres_limpios):
            flash('Los nombres solo pueden contener letras y espacios.', 'danger')
            pregunta = generar_captcha()
            form.captcha_pregunta.data = pregunta
            return render_template('registro.html', form=form, captcha_pregunta_texto=pregunta)

        if not validar_nombre_persona(apellidos_limpios):
            flash('Los apellidos solo pueden contener letras y espacios.', 'danger')
            pregunta = generar_captcha()
            form.captcha_pregunta.data = pregunta
            return render_template('registro.html', form=form, captcha_pregunta_texto=pregunta)

        if not validar_telefono_10_digitos(telefono_limpio):
            flash('El teléfono debe contener exactamente 10 dígitos numéricos.', 'danger')
            pregunta = generar_captcha()
            form.captcha_pregunta.data = pregunta
            return render_template('registro.html', form=form, captcha_pregunta_texto=pregunta)

        if not form.mayor_edad.data:
            flash('Debes confirmar que eres mayor de edad para registrarte.', 'danger')
            pregunta = generar_captcha()
            form.captcha_pregunta.data = pregunta
            return render_template('registro.html', form=form, captcha_pregunta_texto=pregunta)

        if not form.acepta_terminos.data:
            flash('Debes aceptar los términos y condiciones para continuar.', 'danger')
            pregunta = generar_captcha()
            form.captcha_pregunta.data = pregunta
            return render_template('registro.html', form=form, captcha_pregunta_texto=pregunta)

        try:
            fecha_nacimiento = form.fecha_nacimiento.data
            hoy = date.today()
            edad = hoy.year - fecha_nacimiento.year - ((hoy.month, hoy.day) < (fecha_nacimiento.month, fecha_nacimiento.day))
            if edad < 18:
                raise ValueError
        except Exception:
            flash('La fecha de nacimiento es obligatoria y debes ser mayor de edad.', 'danger')
            pregunta = generar_captcha()
            form.captcha_pregunta.data = pregunta
            return render_template('registro.html', form=form, captcha_pregunta_texto=pregunta)

        if not validar_password_segura(form.password.data):
            flash('La contraseña debe tener al menos 8 caracteres, incluir mayúsculas, minúsculas, números y un símbolo.', 'danger')
            pregunta = generar_captcha()
            form.captcha_pregunta.data = pregunta
            return render_template('registro.html', form=form, captcha_pregunta_texto=pregunta)

        if Usuario.get_by_usuario(usuario_limpio):
            flash('El nombre de usuario ya se encuentra registrado. Elige otro.', 'danger')
            pregunta = generar_captcha()
            form.captcha_pregunta.data = pregunta
            return render_template('registro.html', form=form, captcha_pregunta_texto=pregunta)

        if Usuario.get_by_correo(correo_limpio):
            flash('Ya existe una cuenta con este correo electrónico. Inicia sesión o usa otro.', 'danger')
            pregunta = generar_captcha()
            form.captcha_pregunta.data = pregunta
            return render_template('registro.html', form=form, captcha_pregunta_texto=pregunta)

        conn = get_db_connection()
        cursor = conn.cursor()
        cursor.execute(
            '''SELECT 1
               FROM information_schema.columns
               WHERE table_name = 'usuarios' AND column_name = 'telefono' '''
        )
        telefono_configurado = cursor.fetchone() is not None
        if not telefono_configurado:
            cursor.close()
            conn.close()
            flash('La base de datos aun no tiene configurado el campo de celular. Ejecuta la migracion indicada.', 'danger')
            pregunta = generar_captcha()
            form.captcha_pregunta.data = pregunta
            return render_template('registro.html', form=form, captcha_pregunta_texto=pregunta)
        cursor.execute(
            'SELECT 1 FROM usuarios WHERE telefono = %s LIMIT 1',
            (telefono_limpio,)
        )
        telefono_repetido = cursor.fetchone() is not None
        cursor.close()
        conn.close()
        if telefono_repetido:
            flash('Ya existe una cuenta con este número de celular. Usa otro.', 'danger')
            pregunta = generar_captcha()
            form.captcha_pregunta.data = pregunta
            return render_template('registro.html', form=form, captcha_pregunta_texto=pregunta)

        rol_obj = Role.get_by_id(form.rol_id.data)
        rol_nombre = rol_obj['nombre'] if rol_obj else 'Cliente'
        # Los roles operativos pueden iniciar sesión inmediatamente.
        # Solo una cuenta que solicita privilegios de Administrador requiere
        # aprobación explícita desde el panel administrativo.
        aprobado = (rol_nombre != 'Administrador')
        password_hashed = User.hash_password(form.password.data)

        conn = None
        cursor = None
        try:
            conn = get_db_connection()
            cursor = conn.cursor()
            cursor.execute("SELECT column_name FROM information_schema.columns WHERE table_name = 'usuarios' AND column_name IN ('nombres', 'apellidos', 'telefono', 'fecha_nacimiento', 'es_mayor_edad', 'acepta_terminos')")
            columnas_extra = {row['column_name'] for row in cursor.fetchall()}

            campos = ['usuario', 'correo', 'password', 'rol_id', 'activo', 'email_confirmado', 'aprobado', 'dos_factores_activo']
            valores = [usuario_limpio, correo_limpio, password_hashed, form.rol_id.data, True, True, aprobado, False]

            if 'nombres' in columnas_extra:
                campos.append('nombres'); valores.append(nombres_limpios)
            if 'apellidos' in columnas_extra:
                campos.append('apellidos'); valores.append(apellidos_limpios)
            if 'telefono' in columnas_extra:
                campos.append('telefono'); valores.append(telefono_limpio)
            if 'fecha_nacimiento' in columnas_extra:
                campos.append('fecha_nacimiento'); valores.append(form.fecha_nacimiento.data)
            if 'es_mayor_edad' in columnas_extra:
                campos.append('es_mayor_edad'); valores.append(True)
            if 'acepta_terminos' in columnas_extra:
                campos.append('acepta_terminos'); valores.append(True)

            placeholders = ', '.join(['%s'] * len(campos))
            columnas_sql = ', '.join(campos)
            sql = f'''INSERT INTO usuarios ({columnas_sql}) VALUES ({placeholders}) RETURNING id'''
            cursor.execute(sql, tuple(valores))
            nuevo_id = cursor.fetchone()['id']
            conn.commit()
        except psycopg2.IntegrityError:
            if conn:
                conn.rollback()
            app.logger.exception('Registro rechazado por una restricción de PostgreSQL.')
            flash('No se pudo guardar: el usuario, correo o teléfono ya existe. Verifica los datos e inténtalo nuevamente.', 'danger')
            pregunta = generar_captcha()
            form.captcha_pregunta.data = pregunta
            return render_template('registro.html', form=form, captcha_pregunta_texto=pregunta), 409
        except psycopg2.Error:
            if conn:
                conn.rollback()
            app.logger.exception('PostgreSQL falló al guardar un nuevo usuario.')
            flash('No se pudo guardar la información porque la base de datos no respondió. Inténtalo nuevamente en unos segundos.', 'danger')
            pregunta = generar_captcha()
            form.captcha_pregunta.data = pregunta
            return render_template('registro.html', form=form, captcha_pregunta_texto=pregunta), 503
        finally:
            if cursor:
                cursor.close()
            if conn:
                conn.close()

        ActivityLog.registrar(
            nuevo_id, usuario_limpio, 'REGISTRO_USUARIO',
            request.remote_addr, f"Rol solicitado: {rol_nombre} | Aprobado: {aprobado} | Mayor de edad: true"
        )

        if not aprobado:
            flash(
                f'La información se ha guardado correctamente. Es un gusto tenerte en NexoDigital, '
                f'{usuario_limpio}. Como solicitaste el rol de {rol_nombre}, un Administrador activo '
                'deberá aprobar tu acceso antes de poder iniciar sesión.',
                'warning'
            )
        else:
            flash(
                f'La información se ha guardado correctamente. Es un gusto tenerte en NexoDigital, '
                f'{usuario_limpio}. Tu cuenta con rol {rol_nombre} ya está lista; puedes iniciar sesión.',
                'success'
            )

        return redirect(url_for('login'))

    pregunta = session.get('captcha_pregunta') or generar_captcha()
    form.captcha_pregunta.data = pregunta
    return render_template('registro.html', form=form, captcha_pregunta_texto=pregunta)


@app.route('/health')
def health():
    """Comprobación simple para Render: proceso web y PostgreSQL."""
    conn = None
    cursor = None
    try:
        conn = get_db_connection()
        cursor = conn.cursor()
        cursor.execute('SELECT 1')
        cursor.fetchone()
        cursor.execute(
            '''SELECT table_name
               FROM information_schema.tables
               WHERE table_schema = 'public'
                 AND table_name IN (
                     'roles', 'usuarios', 'clientes', 'servicios',
                     'facturacion', 'detalle_factura', 'solicitudes',
                     'proveedores'
                 )'''
        )
        tablas = {fila['table_name'] for fila in cursor.fetchall()}
        tablas_requeridas = {
            'roles', 'usuarios', 'clientes', 'servicios',
            'facturacion', 'detalle_factura', 'solicitudes', 'proveedores'
        }
        faltantes = sorted(tablas_requeridas - tablas)
        if faltantes:
            app.logger.error('Esquema incompleto. Faltan tablas: %s', ', '.join(faltantes))
            return {
                'status': 'error',
                'database': 'connected',
                'schema': 'incomplete',
                'missing_tables': faltantes
            }, 503

        cursor.execute(
            '''SELECT table_name, column_name
               FROM information_schema.columns
               WHERE table_schema = 'public'
                 AND (
                     (table_name = 'solicitudes' AND column_name IN
                        ('estado', 'responsable_id', 'trabajo_realizado', 'evidencia_url'))
                     OR
                     (table_name = 'usuarios' AND column_name IN
                        ('activo', 'aprobado', 'rol_id'))
                 )'''
        )
        columnas = {(fila['table_name'], fila['column_name']) for fila in cursor.fetchall()}
        columnas_requeridas = {
            ('solicitudes', 'estado'),
            ('solicitudes', 'responsable_id'),
            ('solicitudes', 'trabajo_realizado'),
            ('solicitudes', 'evidencia_url'),
            ('usuarios', 'activo'),
            ('usuarios', 'aprobado'),
            ('usuarios', 'rol_id')
        }
        columnas_faltantes = sorted(
            f'{tabla}.{columna}'
            for tabla, columna in columnas_requeridas - columnas
        )
        if columnas_faltantes:
            app.logger.error(
                'Columnas requeridas ausentes: %s',
                ', '.join(columnas_faltantes)
            )
            return {
                'status': 'error',
                'database': 'connected',
                'schema': 'incomplete',
                'missing_columns': columnas_faltantes
            }, 503
        return {'status': 'ok', 'database': 'connected', 'schema': 'ready'}, 200
    except Exception:
        app.logger.exception('Healthcheck de PostgreSQL fallido.')
        return {
            'status': 'error',
            'database': 'unavailable',
            'configuration': (
                'Configura DATABASE_URL o DB_PASSWORD en el archivo .env '
                'de la raíz del proyecto.'
            )
        }, 503
    finally:
        if cursor:
            cursor.close()
        if conn:
            conn.close()


@app.route('/registro/disponibilidad')
def disponibilidad_registro():
    """Comprueba en PostgreSQL si un usuario, correo o teléfono ya existe."""
    campo = (request.args.get('campo') or '').strip().lower()
    valor = (request.args.get('valor') or '').strip()
    columnas_permitidas = {
        'usuario': 'usuario',
        'correo': 'correo',
        'telefono': 'telefono',
    }
    columna = columnas_permitidas.get(campo)
    if not columna or not valor:
        return {'disponible': False, 'mensaje': 'Dato no válido.'}, 400

    if campo == 'correo':
        valor = valor.lower()
    elif campo == 'telefono':
        valor = re.sub(r'\D', '', valor)

    conn = get_db_connection()
    try:
        cursor = conn.cursor()
        cursor.execute(
            '''SELECT 1
               FROM information_schema.columns
               WHERE table_name = 'usuarios' AND column_name = %s''',
            (columna,)
        )
        if cursor.fetchone() is None:
            return {
                'disponible': False,
                'mensaje': 'Este campo aun no esta configurado en la base de datos.'
            }, 503
        cursor.execute(
            f'SELECT 1 FROM usuarios WHERE {columna} = %s LIMIT 1',
            (valor,)
        )
        existe = cursor.fetchone() is not None
        cursor.close()
        return {
            'disponible': not existe,
            'mensaje': (
                'Este dato ya está registrado.'
                if existe else 'Disponible.'
            ),
        }
    finally:
        conn.close()


@app.route('/login', methods=['GET', 'POST'])
def login():
    """
    Ruta para el inicio de sesión de usuarios.
    Permite autenticarse por nombre de usuario o por correo electrónico.
    Verifica contraseñas seguras (Bcrypt con fallback a Werkzeug).
    Bloquea a usuarios con rol Administrador que aún no han sido aprobados por un Administrador activo.
    Gestiona flujo de 2FA si está habilitado y caducidad de sesión.
    """
    if current_user.is_authenticated:
        return redirect(url_for('dashboard'))

    form = LoginForm()
    if form.validate_on_submit():
        identificador = (form.usuario.data or '').strip()
        password = form.password.data or ''
        try:
            user = Usuario.get_by_usuario_o_correo(identificador)
        except psycopg2.Error:
            app.logger.exception('No se pudo consultar el usuario durante el login.')
            flash('La base de datos de Render no está disponible en este momento. Espera unos segundos y vuelve a intentarlo.', 'warning')
            return render_template('login.html', form=form), 503

        # La identidad se busca por usuario/correo y la contraseña se verifica
        # contra su hash; nunca se compara la contraseña dentro de SQL.
        if user and user.check_password(password):
            # Validar si el usuario está activo
            if not user.activo:
                registrar_log('LOGIN_BLOQUEADO', f"Usuario inactivo: {user.usuario}")
                flash('Tu cuenta se encuentra temporalmente desactivada. Contacta al Administrador.', 'danger')
                return render_template('login.html', form=form)

            # Validar si el usuario requiere aprobación y aún no ha sido autorizado
            if not user.aprobado:
                registrar_log('LOGIN_PENDIENTE_APROBACION', f"Intento de acceso no aprobado ({user.rol_nombre}): {user.usuario}")
                flash(f'Tu solicitud de rol {user.rol_nombre} está pendiente de aprobación por un Administrador activo del sistema.', 'warning')
                return render_template('login.html', form=form)

            # Verificación en dos pasos (2FA) si está activada
            if user.dos_factores_activo:
                codigo_otp = f"{random.randint(100000, 999999)}"
                session['2fa_user_id'] = user.id
                session['2fa_codigo'] = codigo_otp
                session['2fa_remember'] = form.recordarme.data
                session['temp_user_nombre'] = user.usuario

                try:
                    conn = get_db_connection()
                    cur = conn.cursor()
                    cur.execute('UPDATE usuarios SET dos_factores_codigo = %s WHERE id = %s', (codigo_otp, user.id))
                    conn.commit()
                    cur.close()
                    conn.close()
                except psycopg2.Error:
                    if 'cur' in locals() and cur:
                        cur.close()
                    if 'conn' in locals() and conn:
                        conn.close()
                    app.logger.exception('No se pudo guardar el código 2FA durante el login.')
                    flash('La base de datos no pudo preparar la verificación 2FA. Inténtalo nuevamente.', 'warning')
                    return render_template('login.html', form=form), 503

                registrar_log('SOLICITUD_2FA', f"Código 2FA generado para {user.usuario}")
                flash('Ingresa el código de verificación en dos pasos (2FA) para completar el acceso.', 'info')
                return redirect(url_for('verificar_2fa'))

            # Inicio de sesión normal
            session.permanent = True
            login_user(user, remember=form.recordarme.data)
            registrar_log('LOGIN_EXITOSO', f"Inicio de sesión exitoso como {user.rol_nombre}")
            flash(f'¡Bienvenido/a al sistema, {user.usuario}!', 'success')
            next_page = request.args.get('next')
            if not next_page or not next_page.startswith('/'):
                next_page = url_for('dashboard')
            return redirect(next_page)
        else:
            session['temp_user_nombre'] = identificador
            app.logger.warning(
                'Login rechazado: usuario_encontrado=%s | identificador_normalizado=%s',
                user is not None,
                identificador.lower()
            )
            registrar_log('LOGIN_FALLIDO', f"Credenciales incorrectas para: {identificador}")
            flash('Credenciales incorrectas. Verifica tu usuario/correo y contraseña.', 'danger')

    return render_template('login.html', form=form)


@app.route('/verificar-2fa', methods=['GET', 'POST'])
def verificar_2fa():
    """
    Ruta para validar el segundo factor de autenticación (OTP numérico de 6 dígitos).
    """
    user_id = session.get('2fa_user_id')
    codigo_esperado = session.get('2fa_codigo')
    if not user_id or not codigo_esperado:
        flash('No hay una sesión 2FA activa. Inicia sesión nuevamente.', 'warning')
        return redirect(url_for('login'))

    form = DosFactoresForm()
    if form.validate_on_submit():
        if form.codigo.data.strip() == codigo_esperado:
            user = Usuario.get_by_id(user_id)
            if user:
                session.permanent = True
                login_user(user, remember=session.get('2fa_remember', False))
                # Limpiar variables temporales de 2FA
                session.pop('2fa_user_id', None)
                session.pop('2fa_codigo', None)
                session.pop('2fa_remember', None)
                session.pop('temp_user_nombre', None)

                registrar_log('LOGIN_2FA_EXITOSO', f"2FA validado para {user.usuario}")
                flash(f'¡Autenticación en dos pasos exitosa! Bienvenido/a, {user.usuario}.', 'success')
                return redirect(url_for('dashboard'))
        flash('Código de verificación 2FA incorrecto o expirado.', 'danger')

    return render_template('verificar_2fa.html', form=form, codigo_simulado=codigo_esperado)


@app.route('/confirmar-correo/<token>')
def confirmar_correo(token):
    """
    Simulación de confirmación de correo electrónico.
    """
    user = Usuario.get_by_usuario_o_correo(token)
    if user:
        conn = get_db_connection()
        cur = conn.cursor()
        cur.execute('UPDATE usuarios SET email_confirmado = TRUE WHERE id = %s', (user.id,))
        conn.commit()
        cur.close()
        conn.close()
        registrar_log('EMAIL_CONFIRMADO', f"Correo confirmado para {user.usuario}")
        flash('¡Tu dirección de correo ha sido confirmada con éxito!', 'success')
    else:
        flash('Token o enlace de confirmación inválido.', 'danger')
    return redirect(url_for('login'))


@app.route('/logout')
@login_required
def logout():
    """
    Ruta para el cierre de sesión seguro.
    Registra el evento en auditoría, destruye la sesión con logout_user y redirige al login.
    """
    registrar_log('LOGOUT', f'Sesión cerrada por {current_user.usuario}')
    logout_user()
    flash('Has cerrado sesión correctamente. ¡Hasta pronto!', 'info')
    return redirect(url_for('login'))


@app.route('/dashboard')
@login_required
def dashboard():
    """
    Panel administrativo principal protegido por autenticación.
    Muestra métricas globales y accesos rápidos adaptados al rol del usuario.
    """
    conn = get_db_connection()
    cursor = conn.cursor()

    if current_user.rol_nombre == 'Cliente':
        total_clientes = 0
    else:
        cursor.execute('SELECT COUNT(*) AS total FROM clientes')
        total_clientes = cursor.fetchone()['total']

    cursor.execute('SELECT COUNT(*) AS total FROM servicios')
    total_servicios = cursor.fetchone()['total']

    if current_user.rol_nombre == 'Cliente':
        cursor.execute('''
            SELECT COUNT(*) AS total
            FROM facturacion f
            JOIN clientes c ON f.cliente_cedula = c.cedula
            WHERE LOWER(TRIM(c.correo)) = LOWER(TRIM(%s))
               OR c.cedula = %s
        ''', (current_user.correo, current_user.usuario))
    else:
        cursor.execute('SELECT COUNT(*) AS total FROM facturacion')
    total_facturas = cursor.fetchone()['total']

    if current_user.rol_nombre == 'Cliente':
        total_proveedores = 0
    else:
        cursor.execute('SELECT COUNT(*) AS total FROM proveedores')
        total_proveedores = cursor.fetchone()['total']

    # Si es Cliente, muestra únicamente sus propios documentos comerciales
    if current_user.rol_nombre == 'Cliente':
        cursor.execute('''
            SELECT f.*, c.nombre AS cliente_nombre, e.nombre AS estado_nombre
            FROM facturacion f
            JOIN clientes c ON f.cliente_cedula = c.cedula
            JOIN estados_documento e ON f.estado_id = e.id
            WHERE LOWER(TRIM(c.correo)) = LOWER(TRIM(%s))
               OR c.cedula = %s
            ORDER BY f.fecha DESC, f.numero DESC
            LIMIT 5
        ''', (current_user.correo, current_user.usuario))
    else:
        # Consulta JOIN general para Administrador, Gestor y Soporte
        cursor.execute('''
            SELECT f.*, c.nombre AS cliente_nombre, e.nombre AS estado_nombre
            FROM facturacion f
            JOIN clientes c ON f.cliente_cedula = c.cedula
            JOIN estados_documento e ON f.estado_id = e.id
            ORDER BY f.fecha DESC, f.numero DESC
            LIMIT 5
        ''')
    ultimas_facturas = cursor.fetchall()

    cursor.close()
    conn.close()

    return render_template(
        'dashboard.html',
        total_clientes=total_clientes,
        total_servicios=total_servicios,
        total_facturas=total_facturas,
        total_proveedores=total_proveedores,
        ultimas_facturas=ultimas_facturas
    )


# ==============================================================================
# MÓDULO EXCLUSIVO DE ADMINISTRACIÓN (RBAC & AUDITORÍA)
# ==============================================================================

@app.route('/admin/usuarios')
@login_required
@role_required('Administrador')
def admin_usuarios():
    """
    Panel de gestión de cuentas y roles de usuario.
    Permite autorizar nuevas solicitudes de rol Administrador y reasignar roles.
    Muestra la matriz de permisos granulares asociada en la tabla rol_permisos.
    """
    usuarios = Usuario.get_all()
    roles = Role.get_all()

    conn = get_db_connection()
    cur = conn.cursor()
    cur.execute('''
        SELECT r.id AS rol_id, r.nombre AS rol_nombre, p.codigo, p.descripcion
        FROM roles r
        JOIN rol_permisos rp ON r.id = rp.rol_id
        JOIN permisos p ON rp.permiso_id = p.id
        ORDER BY r.id, p.codigo
    ''')
    filas_permisos = cur.fetchall()
    cur.close()
    conn.close()

    permisos_por_rol = {}
    for f in filas_permisos:
        permisos_por_rol.setdefault(f['rol_nombre'], []).append({
            'codigo': f['codigo'],
            'descripcion': f['descripcion']
        })

    return render_template(
        'admin_usuarios.html',
        usuarios=usuarios,
        roles=roles,
        permisos_por_rol=permisos_por_rol
    )


@app.route('/admin/aprobar-usuario/<int:id>', methods=['POST'])
@login_required
@role_required('Administrador')
def admin_aprobar_usuario(id):
    """
    Aprueba una solicitud de rol Administrador pendiente.
    Exclusivo para administradores activos del sistema.
    """
    user = Usuario.get_by_id(id)
    if not user:
        flash('El usuario indicado no existe.', 'danger')
        return redirect(url_for('admin_usuarios'))

    conn = get_db_connection()
    cur = conn.cursor()
    cur.execute('UPDATE usuarios SET aprobado = TRUE, activo = TRUE WHERE id = %s', (id,))
    conn.commit()
    cur.close()
    conn.close()

    registrar_log('APROBAR_ADMINISTRADOR', f"El administrador {current_user.usuario} aprobó la cuenta de {user.usuario}")
    flash(f'El usuario {user.usuario} ha sido aprobado exitosamente como Administrador. Ya puede iniciar sesión.', 'success')
    return redirect(url_for('admin_usuarios'))


@app.route('/admin/cambiar-rol/<int:id>', methods=['POST'])
@login_required
@role_required('Administrador')
def admin_cambiar_rol(id):
    """
    Modifica el rol asignado a un usuario existente en PostgreSQL.
    """
    nuevo_rol_id = request.form.get('nuevo_rol_id', type=int)
    if not nuevo_rol_id:
        flash('Rol inválido.', 'danger')
        return redirect(url_for('admin_usuarios'))

    rol_obj = Role.get_by_id(nuevo_rol_id)
    if not rol_obj:
        flash('El rol seleccionado no es válido.', 'danger')
        return redirect(url_for('admin_usuarios'))

    user = Usuario.get_by_id(id)
    if not user:
        flash('El usuario no existe.', 'danger')
        return redirect(url_for('admin_usuarios'))

    conn = get_db_connection()
    cur = conn.cursor()
    # Si un Administrador activo le asigna el rol Administrador, queda aprobado automáticamente
    cur.execute('UPDATE usuarios SET rol_id = %s, aprobado = TRUE WHERE id = %s', (nuevo_rol_id, id))
    conn.commit()
    cur.close()
    conn.close()

    registrar_log('CAMBIO_ROL', f"El administrador {current_user.usuario} cambió el rol de {user.usuario} a {rol_obj['nombre']}")
    flash(f'Rol de {user.usuario} actualizado exitosamente a {rol_obj["nombre"]}.', 'success')
    return redirect(url_for('admin_usuarios'))


@app.route('/admin/restablecer-password/<int:id>', methods=['POST'])
@login_required
@role_required('Administrador')
def admin_restablecer_password(id):
    """Genera una contraseña temporal para una cuenta sin usar correo electrónico."""
    user = Usuario.get_by_id(id)
    if not user:
        flash('El usuario no existe.', 'danger')
        return redirect(url_for('admin_usuarios'))

    password_temporal = f"Nexo-{secrets.token_urlsafe(6)}!"
    password_hashed = User.hash_password(password_temporal)

    conn = get_db_connection()
    cur = conn.cursor()
    cur.execute(
        '''UPDATE usuarios
           SET password = %s, activo = TRUE, aprobado = TRUE,
               dos_factores_activo = TRUE, dos_factores_codigo = NULL
           WHERE id = %s''',
        (password_hashed, id)
    )
    conn.commit()
    cur.close()
    conn.close()

    registrar_log(
        'RESTABLECER_PASSWORD',
        f'El administrador {current_user.usuario} generó una contraseña temporal para {user.usuario}'
    )
    flash(
        f'Contraseña temporal para {user.usuario}: {password_temporal}. '
        'Entrégala de forma privada y solicita cambiarla después de iniciar sesión.',
        'warning'
    )
    return redirect(url_for('admin_usuarios'))


@app.route('/admin/logs')
@login_required
@role_required('Administrador')
def admin_logs():
    """
    Visualiza el registro histórico de auditoría de actividad del sistema con paginación de 20 por página.
    """
    filtros = {
        'fecha_desde': request.args.get('fecha_desde', '').strip(),
        'fecha_hasta': request.args.get('fecha_hasta', '').strip(),
        'hora_desde': request.args.get('hora_desde', '').strip(),
        'hora_hasta': request.args.get('hora_hasta', '').strip(),
        'persona': request.args.get('persona', '').strip(),
        'accion': request.args.get('accion', '').strip(),
        'ip': request.args.get('ip', '').strip(),
        'detalles': request.args.get('detalles', '').strip(),
    }
    for nombre_filtro, formato in (
        ('fecha_desde', '%Y-%m-%d'),
        ('fecha_hasta', '%Y-%m-%d'),
        ('hora_desde', '%H:%M'),
        ('hora_hasta', '%H:%M'),
    ):
        valor = filtros[nombre_filtro]
        if valor:
            try:
                datetime.strptime(valor, formato)
            except ValueError:
                filtros[nombre_filtro] = ''
                flash(f'El filtro {nombre_filtro.replace("_", " ")} no es válido.', 'warning')

    # Configuración de paginado: 20 registros por página
    por_pagina = 20
    try:
        pagina = int(request.args.get('page', 1))
        if pagina < 1:
            pagina = 1
    except (ValueError, TypeError):
        pagina = 1

    total_logs = ActivityLog.contar(**filtros)
    total_paginas = max(1, math.ceil(total_logs / por_pagina))
    if pagina > total_paginas and total_logs > 0:
        pagina = total_paginas

    offset = (pagina - 1) * por_pagina
    logs = ActivityLog.buscar(**filtros, limit=por_pagina, offset=offset)
    acciones_disponibles = ActivityLog.acciones_disponibles()

    inicio_registro = offset + 1 if total_logs > 0 else 0
    fin_registro = min(offset + por_pagina, total_logs)

    # Rango de páginas con elipsis inteligente
    def generar_rango(actual, total, ventana=2):
        if total <= 7:
            return list(range(1, total + 1))
        pags = set([1, total])
        for p in range(max(1, actual - ventana), min(total + 1, actual + ventana + 1)):
            pags.add(p)
        resultado = []
        prev = 0
        for p in sorted(pags):
            if prev and p - prev > 1:
                resultado.append(None)
            resultado.append(p)
            prev = p
        return resultado

    paginas_numeros = generar_rango(pagina, total_paginas)
    filtros_activos = {k: v for k, v in filtros.items() if v}

    return render_template(
        'admin_logs.html',
        logs=logs,
        filtros=filtros,
        filtros_activos=filtros_activos,
        acciones_disponibles=acciones_disponibles,
        pagina=pagina,
        total_paginas=total_paginas,
        total_logs=total_logs,
        por_pagina=por_pagina,
        inicio_registro=inicio_registro,
        fin_registro=fin_registro,
        paginas_numeros=paginas_numeros
    )


@app.route('/solicitudes', methods=['GET'])
@login_required
@role_required('Administrador', 'Gestor de proyectos', 'Soporte técnico')
def solicitudes():
    """Muestra las peticiones de clientes y permite responderlas y asignarlas."""
    conn = get_db_connection()
    cursor = conn.cursor()
    if current_user.rol_nombre == 'Soporte técnico':
        cursor.execute('''
            SELECT s.*, u.usuario AS responsable_nombre,
                   r.usuario AS resuelto_por_nombre
            FROM solicitudes s
            LEFT JOIN usuarios u ON u.id = s.responsable_id
            LEFT JOIN usuarios r ON r.id = s.resuelto_por_id
            WHERE s.responsable_id = %s
            ORDER BY s.fecha DESC, s.id DESC
        ''', (current_user.id,))
    else:
        cursor.execute('''
            SELECT s.*, u.usuario AS responsable_nombre,
                   r.usuario AS resuelto_por_nombre
            FROM solicitudes s
            LEFT JOIN usuarios u ON u.id = s.responsable_id
            LEFT JOIN usuarios r ON r.id = s.resuelto_por_id
            ORDER BY s.fecha DESC, s.id DESC
        ''')
    solicitudes_registradas = cursor.fetchall()
    cursor.execute('''
        SELECT u.id, u.usuario
        FROM usuarios u
        JOIN roles r ON r.id = u.rol_id
        WHERE u.activo = TRUE
          AND r.nombre IN ('Administrador', 'Gestor de proyectos', 'Soporte técnico', 'Usuario interno')
        ORDER BY u.usuario
    ''')
    responsables = cursor.fetchall()
    cursor.close()
    conn.close()
    return render_template(
        'solicitudes.html',
        solicitudes=solicitudes_registradas,
        responsables=responsables
    )


@app.route('/api/solicitudes', methods=['POST'])
def crear_solicitud():
    """Registra una petición pública directamente en PostgreSQL."""
    datos = request.get_json(silent=True) or request.form
    nombre = (datos.get('nombre') or '').strip()
    correo = (datos.get('correo') or '').strip().lower()
    telefono = (datos.get('telefono') or '').strip()
    tipo_servicio = (datos.get('tipo_servicio') or '').strip()
    mensaje = (datos.get('mensaje') or '').strip()

    correo_valido = re.fullmatch(r'[^@\s]+@[^@\s]+\.[^@\s]{2,}', correo)
    nombre_valido = re.fullmatch(
        r"[^\W\d_]+(?:[ .'-][^\W\d_]+)*",
        nombre,
        flags=re.UNICODE
    )
    telefono_valido = not telefono or re.fullmatch(r'\d{10}', telefono)
    if (
        not nombre_valido or len(nombre) < 4 or len(nombre) > 150
        or not correo_valido or len(correo) > 150
        or not telefono_valido or len(tipo_servicio) < 2
        or len(mensaje) < 10 or len(mensaje) > 5000
    ):
        return {
            'ok': False,
            'mensaje': 'Revisa nombre, correo, teléfono (10 números), servicio y descripción.'
        }, 400

    conn = None
    cursor = None
    try:
        conn = get_db_connection()
        cursor = conn.cursor()
        cursor.execute('''
            INSERT INTO solicitudes (nombre, correo, telefono, tipo_servicio, mensaje)
            VALUES (%s, %s, %s, %s, %s)
            RETURNING id
        ''', (nombre, correo, telefono or None, tipo_servicio, mensaje))
        solicitud_id = cursor.fetchone()['id']
        conn.commit()
        return {'ok': True, 'id': solicitud_id}, 201
    except psycopg2.Error as error:
        if conn:
            conn.rollback()
        app.logger.exception('No se pudo guardar la solicitud en PostgreSQL.')
        if getattr(error, 'pgcode', None) == '42P01':
            mensaje_error = 'La tabla solicitudes no existe en la base de datos conectada.'
        elif getattr(error, 'pgcode', None) == '42703':
            mensaje_error = 'La tabla solicitudes no tiene una columna requerida por la aplicación.'
        else:
            mensaje_error = 'La base de datos rechazó la solicitud. Revisa la conexión y el esquema.'
        return {
            'ok': False,
            'mensaje': mensaje_error
        }, 503
    finally:
        if cursor:
            cursor.close()
        if conn:
            conn.close()


@app.route('/solicitudes/<int:id>/actualizar', methods=['POST'])
@login_required
@role_required('Administrador', 'Gestor de proyectos', 'Soporte técnico')
def actualizar_solicitud(id):
    """Actualiza una petición, su respuesta y el trabajo realizado/evidencia."""
    estado = (request.form.get('estado') or '').strip()
    responsable_id = request.form.get('responsable_id', type=int)
    respuesta_cliente = (request.form.get('respuesta_cliente') or '').strip()
    trabajo_realizado = (request.form.get('trabajo_realizado') or '').strip()
    evidencia_url = (request.form.get('evidencia_url') or '').strip()
    estados_validos = {'Pendiente', 'En revisión', 'Asignada', 'En proceso', 'Resuelta', 'Descartada'}
    if estado not in estados_validos:
        flash('El estado seleccionado no es válido.', 'danger')
        return redirect(url_for('solicitudes'))
    if evidencia_url:
        evidencia_partes = urlparse(evidencia_url)
        if evidencia_partes.scheme not in ('http', 'https') or not evidencia_partes.netloc:
            flash('La evidencia debe ser un enlace http(s) válido.', 'danger')
            return redirect(url_for('solicitudes'))
    if estado == 'Resuelta' and not (trabajo_realizado or evidencia_url):
        flash('Para marcar una petición como resuelta agrega el trabajo realizado o un enlace de evidencia.', 'warning')
        return redirect(url_for('solicitudes'))

    conn = get_db_connection()
    cursor = conn.cursor()
    cursor.execute('SELECT responsable_id FROM solicitudes WHERE id = %s', (id,))
    solicitud_actual = cursor.fetchone()
    if not solicitud_actual:
        cursor.close()
        conn.close()
        flash('La solicitud no existe.', 'danger')
        return redirect(url_for('solicitudes'))
    if current_user.rol_nombre == 'Soporte técnico' and solicitud_actual['responsable_id'] != current_user.id:
        cursor.close()
        conn.close()
        flash('Solo puedes actualizar trabajos asignados a tu usuario.', 'danger')
        return redirect(url_for('solicitudes'))
    if current_user.rol_nombre == 'Soporte técnico':
        responsable_id = current_user.id
    cursor.execute('''
        UPDATE solicitudes
        SET estado = %s, responsable_id = %s,
            respuesta_cliente = %s, trabajo_realizado = %s, evidencia_url = %s,
            resuelto_por_id = CASE
                WHEN %s IN ('Resuelta', 'Descartada') THEN %s
                ELSE NULL
            END,
            fecha_resolucion = CASE
                WHEN %s IN ('Resuelta', 'Descartada') THEN CURRENT_TIMESTAMP
                ELSE NULL
            END
        WHERE id = %s
    ''', (
        estado, responsable_id or None, respuesta_cliente or None,
        trabajo_realizado or None, evidencia_url or None,
        estado, current_user.id, estado, id
    ))
    if cursor.rowcount == 0:
        conn.rollback()
        cursor.close()
        conn.close()
        flash('La solicitud no existe.', 'danger')
        return redirect(url_for('solicitudes'))
    conn.commit()
    cursor.close()
    conn.close()
    registrar_log('ACTUALIZAR_SOLICITUD', f'Solicitud {id}: {estado}, responsable {responsable_id or "sin asignar"}')
    flash('La solicitud fue actualizada correctamente.', 'success')
    return redirect(url_for('solicitudes'))


# ==============================================================================
# MÓDULOS DE ADMINISTRACIÓN Y GESTIÓN CRUD (Protegidos por Roles y Permisos RBAC)
# ==============================================================================

@app.route('/productos')
@app.route('/servicio')
@app.route('/servicios')
def servicios():
    """
    Ruta del catálogo completo de servicios (Pública para consulta y lectura).
    Permite que usuarios no autenticados conozcan la oferta y descripción de servicios.
    Usa JOIN para mostrar el nombre de la categoría (tipo_servicio) de cada servicio.
    Soporta motor de búsqueda multicriterio (por nombre, descripción y categoría)
    tanto por parámetros URL (?q=...&tipo=...) como en tiempo real vía JavaScript.
    """
    q = request.args.get('q', '').strip()
    tipo = request.args.get('tipo', '').strip()

    tipos_servicio = []
    lista_servicios = []
    base_datos_disponible = False
    try:
        conn = get_db_connection()
        cursor = conn.cursor()
        asegurar_servicios_minimos(cursor)
        conn.commit()
        cursor.execute('SELECT * FROM tipos_servicio ORDER BY nombre')
        tipos_servicio = cursor.fetchall()

        params = []
        where_clauses = []
        if q:
            where_clauses.append("(s.nombre ILIKE %s OR s.descripcion ILIKE %s OR t.nombre ILIKE %s)")
            params.extend([f"%{q}%", f"%{q}%", f"%{q}%"])
        if tipo:
            where_clauses.append("t.nombre = %s")
            params.append(tipo)

        sql_where = (" WHERE " + " AND ".join(where_clauses)) if where_clauses else ""
        query = f'''
            SELECT s.*, t.nombre AS tipo_nombre,
                   COUNT(d.id) AS detalles_relacionados
            FROM servicios s
            JOIN tipos_servicio t ON s.tipo_servicio_id = t.id
            LEFT JOIN detalle_factura d ON d.servicio_id = s.id
            {sql_where}
            GROUP BY s.id, t.nombre
            ORDER BY s.disponible DESC, s.id ASC
        '''
        cursor.execute(query, tuple(params))
        lista_servicios = cursor.fetchall()
        base_datos_disponible = True
        cursor.close()
        conn.close()
    except psycopg2.Error:
        app.logger.exception('No se pudo cargar el catálogo de servicios.')
        flash(
            'No se puede consultar el catálogo porque la conexión con la base de datos no está disponible.',
            'warning'
        )
    return render_template(
        'servicios.html',
        servicios=lista_servicios,
        tipos_servicio=tipos_servicio,
        query_busqueda=q,
        tipo_seleccionado=tipo,
        base_datos_disponible=base_datos_disponible
    ), (200 if base_datos_disponible else 503)



@app.route('/proveedores')
@role_required('Administrador', 'Soporte técnico')
def proveedores():
    """
    Ruta del directorio de proveedores tecnológicos.
    Acceso para Administrador y Soporte técnico (infraestructura).
    Usa JOIN con estados_proveedor y categorias_proveedor para mostrar los nombres relacionados.
    """
    conn = get_db_connection()
    cursor = conn.cursor()
    cursor.execute('''
        SELECT p.*, e.nombre AS estado_nombre, c.nombre AS categoria_nombre
        FROM proveedores p
        JOIN estados_proveedor e ON p.estado_id = e.id
        JOIN categorias_proveedor c ON p.categoria_id = c.id
        ORDER BY p.nombre ASC, p.id ASC
    ''')
    lista_proveedores = cursor.fetchall()
    cursor.close()
    conn.close()
    return render_template('proveedores.html', proveedores=lista_proveedores)


@app.route('/clientes')
@role_required('Administrador', 'Gestor de proyectos', 'Usuario interno')
def clientes():
    """
    Ruta del directorio de clientes comerciales.
    Acceso restringido a Administrador, Gestor de proyectos y Usuario interno.
    Soporte técnico y Clientes NO tienen acceso para proteger datos sensibles.
    Usa JOIN con tipos_negocio para mostrar el nombre de la categoría de negocio.
    """
    conn = get_db_connection()
    cursor = conn.cursor()
    cursor.execute('''
        SELECT c.*, t.nombre AS negocio_nombre
        FROM clientes c
        JOIN tipos_negocio t ON c.tipo_negocio_id = t.id
    ''')
    lista_clientes = cursor.fetchall()
    cursor.close()
    conn.close()
    return render_template('clientes.html', clientes=lista_clientes)


@app.route('/facturacion')
@role_required('Administrador', 'Gestor de proyectos', 'Cliente')
def facturacion():
    """
    Ruta principal del panel comercial de Facturación y Cotizaciones.
    - Administrador, Gestor de proyectos y Usuario interno: ven los documentos del negocio.
    - Cliente: ve únicamente sus propios proyectos y cotizaciones contratadas.
    Usa JOIN con clientes y estados_documento.
    """
    conn = get_db_connection()
    cursor = conn.cursor()

    if current_user.rol_nombre == 'Cliente':
        cursor.execute('''
            SELECT f.*, c.nombre AS cliente_nombre, e.nombre AS estado_nombre
            FROM facturacion f
            JOIN clientes c ON f.cliente_cedula = c.cedula
            JOIN estados_documento e ON f.estado_id = e.id
            WHERE LOWER(TRIM(c.correo)) = LOWER(TRIM(%s))
               OR c.cedula = %s
            ORDER BY f.numero DESC
        ''', (current_user.correo, current_user.usuario))
    else:
        cursor.execute('''
            SELECT f.*, c.nombre AS cliente_nombre, e.nombre AS estado_nombre
            FROM facturacion f
            JOIN clientes c ON f.cliente_cedula = c.cedula
            JOIN estados_documento e ON f.estado_id = e.id
            ORDER BY f.numero DESC
        ''')
    filas = cursor.fetchall()

    lista_facturas = []
    for f in filas:
        doc = dict(f)
        cursor.execute(
            'SELECT COUNT(*) AS total FROM detalle_factura WHERE factura_numero = %s', (doc['numero'],)
        )
        conteo = cursor.fetchone()['total']
        doc['servicios_detalle'] = [None] * conteo  # solo se usa para |length en la plantilla
        lista_facturas.append(doc)

    cursor.close()
    conn.close()
    return render_template('facturacion.html', facturas=lista_facturas)


# ==============================================================================
# MÓDULO CRUD: CLIENTES
# ==============================================================================

@app.route('/clientes/nuevo', methods=['GET', 'POST'])
@role_required('Administrador', 'Gestor de proyectos')
def nuevo_cliente():
    """
    Crea y registra un nuevo cliente en el sistema. La cédula es la clave primaria.
    """
    conn = get_db_connection()
    cursor = conn.cursor()
    cursor.execute('SELECT * FROM tipos_negocio ORDER BY nombre')
    tipos_negocio = cursor.fetchall()

    form = ClienteForm()
    form.tipo_negocio_id.choices = [(t['id'], t['nombre']) for t in tipos_negocio]

    if form.validate_on_submit():
        cursor.execute('SELECT * FROM clientes WHERE cedula = %s', (form.cedula.data.strip(),))
        existente = cursor.fetchone()
        if existente is not None:
            cursor.close()
            conn.close()
            flash('Ya existe un cliente registrado con esa cédula.', 'danger')
            return render_template('formulario_cliente.html', form=form, editando=False)

        cursor.execute(
            '''INSERT INTO clientes (cedula, nombre, telefono, correo, tipo_negocio_id, ciudad)
               VALUES (%s, %s, %s, %s, %s, %s)''',
            (form.cedula.data.strip(), form.nombre.data.strip(), form.telefono.data.strip(),
             form.correo.data.strip(), form.tipo_negocio_id.data, form.ciudad.data.strip())
        )
        conn.commit()
        cursor.close()
        conn.close()

        registrar_log('CREAR_CLIENTE', f"Cliente {form.nombre.data.strip()} ({form.cedula.data.strip()}) creado por {current_user.usuario}")
        flash('Cliente registrado correctamente.', 'success')
        return redirect(url_for('clientes'))

    cursor.close()
    conn.close()
    return render_template('formulario_cliente.html', form=form, editando=False)


@app.route('/clientes/editar/<cedula>', methods=['GET', 'POST'])
@role_required('Administrador', 'Gestor de proyectos')
def editar_cliente(cedula):
    """
    Edita la información de un cliente existente identificado por su cédula (PK).
    La cédula no se modifica desde este formulario, ya que otras tablas dependen de ella.
    """
    conn = get_db_connection()
    cursor = conn.cursor()
    cursor.execute('SELECT * FROM clientes WHERE cedula = %s', (cedula,))
    cliente = cursor.fetchone()

    if cliente is None:
        cursor.close()
        conn.close()
        flash('El cliente seleccionado no existe.', 'danger')
        return redirect(url_for('clientes'))

    cursor.execute('SELECT * FROM tipos_negocio ORDER BY nombre')
    tipos_negocio = cursor.fetchall()

    form = ClienteForm(data=dict(cliente)) if request.method == 'GET' else ClienteForm()
    form.tipo_negocio_id.choices = [(t['id'], t['nombre']) for t in tipos_negocio]
    if request.method == 'GET':
        form.tipo_negocio_id.data = cliente['tipo_negocio_id']

    if form.validate_on_submit():
        cursor.execute(
            '''UPDATE clientes SET nombre=%s, telefono=%s, correo=%s, tipo_negocio_id=%s, ciudad=%s
               WHERE cedula=%s''',
            (form.nombre.data.strip(), form.telefono.data.strip(),
             form.correo.data.strip(), form.tipo_negocio_id.data, form.ciudad.data.strip(), cedula)
        )
        conn.commit()
        cursor.close()
        conn.close()

        registrar_log('EDITAR_CLIENTE', f"Cliente {form.nombre.data.strip()} ({cedula}) actualizado por {current_user.usuario}")
        flash(f'Cliente "{form.nombre.data.strip()}" actualizado correctamente.', 'success')
        return redirect(url_for('clientes'))

    cursor.close()
    conn.close()
    return render_template('formulario_cliente.html', form=form, editando=True, cedula=cedula)


@app.route('/clientes/eliminar/<cedula>', methods=['POST'])
@role_required('Administrador')
def eliminar_cliente(cedula):
    """
    Elimina un cliente de PostgreSQL según su cédula, siempre que no tenga facturas asociadas.
    Acceso exclusivo para el rol Administrador.
    """
    conn = get_db_connection()
    cursor = conn.cursor()
    cursor.execute('SELECT * FROM clientes WHERE cedula = %s', (cedula,))
    cliente = cursor.fetchone()

    if cliente is None:
        cursor.close()
        conn.close()
        flash('El cliente seleccionado no existe.', 'danger')
        return redirect(url_for('clientes'))

    cursor.execute(
        'SELECT COUNT(*) AS total FROM facturacion WHERE cliente_cedula = %s', (cedula,)
    )
    facturas_asociadas = cursor.fetchone()['total']

    if facturas_asociadas > 0:
        cursor.close()
        conn.close()
        flash(f'No se puede eliminar a "{cliente["nombre"]}" porque tiene {facturas_asociadas} factura(s) o cotización(es) registradas.', 'danger')
        return redirect(url_for('clientes'))

    cursor.execute('DELETE FROM clientes WHERE cedula = %s', (cedula,))
    conn.commit()
    cursor.close()
    conn.close()

    registrar_log('ELIMINAR_CLIENTE', f"Cliente {cliente['nombre']} ({cedula}) eliminado por {current_user.usuario}")
    flash(f'Cliente "{cliente["nombre"]}" eliminado correctamente.', 'success')
    return redirect(url_for('clientes'))


# ==============================================================================
# MÓDULO CRUD: TIPOS DE NEGOCIO (categorías de clientes)
# ==============================================================================

@app.route('/tipos-negocio')
@role_required('Administrador')
def tipos_negocio():
    """
    Lista las categorías de tipo de negocio disponibles para clasificar clientes.
    """
    conn = get_db_connection()
    cursor = conn.cursor()
    cursor.execute('SELECT * FROM tipos_negocio ORDER BY nombre')
    lista_tipos = cursor.fetchall()
    cursor.close()
    conn.close()
    return render_template('tipos_negocio.html', tipos=lista_tipos)


@app.route('/tipos-negocio/nuevo', methods=['GET', 'POST'])
@role_required('Administrador')
def nuevo_tipo_negocio():
    """
    Registra una nueva categoría de tipo de negocio.
    """
    form = TipoNegocioForm()
    if form.validate_on_submit():
        conn = get_db_connection()
        cursor = conn.cursor()
        cursor.execute('INSERT INTO tipos_negocio (nombre) VALUES (%s)', (form.nombre.data.strip(),))
        conn.commit()
        cursor.close()
        conn.close()
        registrar_log('CREAR_TIPO_NEGOCIO', f"Tipo de negocio {form.nombre.data.strip()} creado por {current_user.usuario}")
        flash('Tipo de negocio registrado correctamente.', 'success')
        return redirect(url_for('tipos_negocio'))
    return render_template('formulario_tipo_negocio.html', form=form, editando=False)


@app.route('/tipos-negocio/editar/<int:id>', methods=['GET', 'POST'])
@role_required('Administrador')
def editar_tipo_negocio(id):
    """
    Edita el nombre de una categoría de tipo de negocio existente.
    """
    conn = get_db_connection()
    cursor = conn.cursor()
    cursor.execute('SELECT * FROM tipos_negocio WHERE id = %s', (id,))
    tipo = cursor.fetchone()

    if tipo is None:
        cursor.close()
        conn.close()
        flash('El tipo de negocio seleccionado no existe.', 'danger')
        return redirect(url_for('tipos_negocio'))

    form = TipoNegocioForm(data=dict(tipo)) if request.method == 'GET' else TipoNegocioForm()

    if form.validate_on_submit():
        cursor.execute('UPDATE tipos_negocio SET nombre=%s WHERE id=%s', (form.nombre.data.strip(), id))
        conn.commit()
        cursor.close()
        conn.close()
        registrar_log('EDITAR_TIPO_NEGOCIO', f"Tipo de negocio ID {id} actualizado a {form.nombre.data.strip()} por {current_user.usuario}")
        flash(f'Tipo de negocio "{form.nombre.data.strip()}" actualizado correctamente.', 'success')
        return redirect(url_for('tipos_negocio'))

    cursor.close()
    conn.close()
    return render_template('formulario_tipo_negocio.html', form=form, editando=True, id=id)


@app.route('/tipos-negocio/eliminar/<int:id>', methods=['POST'])
@role_required('Administrador')
def eliminar_tipo_negocio(id):
    """
    Elimina un tipo de negocio, siempre que ningún cliente lo esté usando.
    """
    conn = get_db_connection()
    cursor = conn.cursor()
    cursor.execute('SELECT * FROM tipos_negocio WHERE id = %s', (id,))
    tipo = cursor.fetchone()

    if tipo is None:
        cursor.close()
        conn.close()
        flash('El tipo de negocio seleccionado no existe.', 'danger')
        return redirect(url_for('tipos_negocio'))

    cursor.execute('SELECT COUNT(*) AS total FROM clientes WHERE tipo_negocio_id = %s', (id,))
    en_uso = cursor.fetchone()['total']
    if en_uso > 0:
        cursor.close()
        conn.close()
        flash(f'No se puede eliminar "{tipo["nombre"]}" porque hay clientes asignados a esta categoría.', 'danger')
        return redirect(url_for('tipos_negocio'))

    cursor.execute('DELETE FROM tipos_negocio WHERE id = %s', (id,))
    conn.commit()
    cursor.close()
    conn.close()
    registrar_log('ELIMINAR_TIPO_NEGOCIO', f"Tipo de negocio {tipo['nombre']} (ID {id}) eliminado por {current_user.usuario}")
    flash(f'Tipo de negocio "{tipo["nombre"]}" eliminado correctamente.', 'success')
    return redirect(url_for('tipos_negocio'))


# ==============================================================================
# MÓDULO CRUD: TIPOS DE SERVICIO (categorías)
# ==============================================================================

@app.route('/tipos-servicio')
@role_required('Administrador')
def tipos_servicio():
    """
    Lista las categorías de servicio disponibles en el catálogo.
    """
    conn = get_db_connection()
    cursor = conn.cursor()
    cursor.execute('SELECT * FROM tipos_servicio ORDER BY nombre')
    lista_tipos = cursor.fetchall()
    cursor.close()
    conn.close()
    return render_template('tipos_servicio.html', tipos=lista_tipos)


@app.route('/tipos-servicio/nuevo', methods=['GET', 'POST'])
@role_required('Administrador')
def nuevo_tipo_servicio():
    """
    Registra una nueva categoría de servicio.
    """
    form = TipoServicioForm()
    if form.validate_on_submit():
        conn = get_db_connection()
        cursor = conn.cursor()
        cursor.execute('INSERT INTO tipos_servicio (nombre) VALUES (%s)', (form.nombre.data.strip(),))
        conn.commit()
        cursor.close()
        conn.close()
        registrar_log('CREAR_TIPO_SERVICIO', f"Categoría de servicio {form.nombre.data.strip()} creada por {current_user.usuario}")
        flash('Categoría registrada correctamente.', 'success')
        return redirect(url_for('tipos_servicio'))
    return render_template('formulario_tipo_servicio.html', form=form, editando=False)


@app.route('/tipos-servicio/editar/<int:id>', methods=['GET', 'POST'])
@role_required('Administrador')
def editar_tipo_servicio(id):
    """
    Edita el nombre de una categoría de servicio existente.
    """
    conn = get_db_connection()
    cursor = conn.cursor()
    cursor.execute('SELECT * FROM tipos_servicio WHERE id = %s', (id,))
    tipo = cursor.fetchone()

    if tipo is None:
        cursor.close()
        conn.close()
        flash('La categoría seleccionada no existe.', 'danger')
        return redirect(url_for('tipos_servicio'))

    form = TipoServicioForm(data=dict(tipo)) if request.method == 'GET' else TipoServicioForm()

    if form.validate_on_submit():
        cursor.execute('UPDATE tipos_servicio SET nombre=%s WHERE id=%s', (form.nombre.data.strip(), id))
        conn.commit()
        cursor.close()
        conn.close()
        registrar_log('EDITAR_TIPO_SERVICIO', f"Categoría de servicio ID {id} actualizada a {form.nombre.data.strip()} por {current_user.usuario}")
        flash(f'Categoría "{form.nombre.data.strip()}" actualizada correctamente.', 'success')
        return redirect(url_for('tipos_servicio'))

    cursor.close()
    conn.close()
    return render_template('formulario_tipo_servicio.html', form=form, editando=True, id=id)


@app.route('/tipos-servicio/eliminar/<int:id>', methods=['POST'])
@role_required('Administrador')
def eliminar_tipo_servicio(id):
    """
    Elimina una categoría de servicio, siempre que ningún servicio la esté usando.
    """
    conn = get_db_connection()
    cursor = conn.cursor()
    cursor.execute('SELECT * FROM tipos_servicio WHERE id = %s', (id,))
    tipo = cursor.fetchone()

    if tipo is None:
        cursor.close()
        conn.close()
        flash('La categoría seleccionada no existe.', 'danger')
        return redirect(url_for('tipos_servicio'))

    cursor.execute('SELECT COUNT(*) AS total FROM servicios WHERE tipo_servicio_id = %s', (id,))
    en_uso = cursor.fetchone()['total']
    if en_uso > 0:
        cursor.close()
        conn.close()
        flash(f'No se puede eliminar "{tipo["nombre"]}" porque hay servicios asignados a esta categoría.', 'danger')
        return redirect(url_for('tipos_servicio'))

    cursor.execute('DELETE FROM tipos_servicio WHERE id = %s', (id,))
    conn.commit()
    cursor.close()
    conn.close()
    registrar_log('ELIMINAR_TIPO_SERVICIO', f"Categoría de servicio {tipo['nombre']} (ID {id}) eliminada por {current_user.usuario}")
    flash(f'Categoría "{tipo["nombre"]}" eliminada correctamente.', 'success')
    return redirect(url_for('tipos_servicio'))


# ==============================================================================
# MÓDULO CRUD: SERVICIOS / PRODUCTOS
# ==============================================================================

@app.route('/productos/nuevo', methods=['GET', 'POST'])
@app.route('/servicio/nuevo', methods=['GET', 'POST'])
@role_required('Administrador', 'Gestor de proyectos')
def nuevo_servicio():
    """
    Registra un nuevo servicio en el catálogo, asociado a una categoría (tipo_servicio_id).
    Acceso para Administrador y Gestor de proyectos.
    """
    conn = get_db_connection()
    cursor = conn.cursor()
    cursor.execute('SELECT * FROM tipos_servicio ORDER BY nombre')
    tipos = cursor.fetchall()

    form = ServicioForm()
    form.tipo_servicio_id.choices = [(t['id'], t['nombre']) for t in tipos]

    if form.validate_on_submit():
        imagen_ingresada = form.imagen.data.strip() if form.imagen.data else ''
        imagen_url = resolver_url_imagen(imagen_ingresada) if imagen_ingresada else None
        if not imagen_url:
            imagen_url = "https://images.unsplash.com/photo-1460925895917-afdab827c52f"

        cursor.execute(
            '''INSERT INTO servicios (tipo_servicio_id, nombre, precio_base, imagen, descripcion, disponible)
               VALUES (%s, %s, %s, %s, %s, %s)''',
            (form.tipo_servicio_id.data, form.nombre.data.strip(), float(form.precio.data),
             imagen_url, form.descripcion.data.strip(), form.disponible.data)
        )
        conn.commit()
        cursor.close()
        conn.close()

        registrar_log('CREAR_SERVICIO', f"Servicio {form.nombre.data.strip()} creado por {current_user.usuario}")
        flash('Servicio registrado correctamente.', 'success')
        return redirect(url_for('servicios'))

    cursor.close()
    conn.close()
    return render_template('formulario_servicio.html', form=form, editando=False)


@app.route('/productos/editar/<int:id>', methods=['GET', 'POST'])
@app.route('/servicios/editar/<int:id>', methods=['GET', 'POST'])
@app.route('/servicio/editar/<int:id>', methods=['GET', 'POST'])
@role_required('Administrador', 'Gestor de proyectos', 'Soporte técnico')
@permission_required('servicios.editar')
def editar_servicio(id):
    """
    Edita un servicio existente identificado por su id real de PostgreSQL.
    Acceso para Administrador y Gestor de proyectos.
    """
    conn = get_db_connection()
    cursor = conn.cursor()
    cursor.execute('SELECT * FROM servicios WHERE id = %s', (id,))
    servicio = cursor.fetchone()

    if servicio is None:
        cursor.close()
        conn.close()
        flash('El servicio seleccionado no existe.', 'danger')
        return redirect(url_for('servicios'))

    cursor.execute('SELECT * FROM tipos_servicio ORDER BY nombre')
    tipos = cursor.fetchall()

    datos_form = dict(servicio)
    datos_form['precio'] = servicio['precio_base']  # el form usa 'precio', la BD usa 'precio_base'

    form = ServicioForm(data=datos_form) if request.method == 'GET' else ServicioForm()
    form.tipo_servicio_id.choices = [(t['id'], t['nombre']) for t in tipos]
    if request.method == 'GET':
        form.tipo_servicio_id.data = servicio['tipo_servicio_id']

    if form.validate_on_submit():
        imagen_ingresada = form.imagen.data.strip() if form.imagen.data else ''
        imagen_url = resolver_url_imagen(imagen_ingresada) if imagen_ingresada else servicio['imagen']
        if not imagen_url:
            imagen_url = "https://images.unsplash.com/photo-1460925895917-afdab827c52f"

        cursor.execute(
            '''UPDATE servicios SET tipo_servicio_id=%s, nombre=%s, precio_base=%s, imagen=%s, descripcion=%s, disponible=%s
               WHERE id=%s''',
            (form.tipo_servicio_id.data, form.nombre.data.strip(), float(form.precio.data),
             imagen_url, form.descripcion.data.strip(), form.disponible.data, id)
        )
        conn.commit()
        cursor.close()
        conn.close()

        registrar_log('EDITAR_SERVICIO', f"Servicio {form.nombre.data.strip()} (ID {id}) editado por {current_user.usuario}")
        flash(f'Servicio "{form.nombre.data.strip()}" actualizado correctamente.', 'success')
        return redirect(url_for('servicios'))

    cursor.close()
    conn.close()
    return render_template('formulario_servicio.html', form=form, editando=True, id=id)


@app.route('/productos/eliminar/<int:id>', methods=['POST'])
@app.route('/servicios/eliminar/<int:id>', methods=['POST'])
@app.route('/servicio/eliminar/<int:id>', methods=['POST'])
@role_required('Administrador')
def eliminar_servicio(id):
    """
    Elimina un servicio del catálogo en PostgreSQL.
    Acceso exclusivo para el rol Administrador.
    """
    conn = get_db_connection()
    cursor = conn.cursor()
    cursor.execute('SELECT * FROM servicios WHERE id = %s', (id,))
    servicio = cursor.fetchone()

    if servicio is None:
        cursor.close()
        conn.close()
        flash('El servicio seleccionado no existe.', 'danger')
        return redirect(url_for('servicios'))

    cursor.execute(
        'SELECT COUNT(*) AS total FROM detalle_factura WHERE servicio_id = %s',
        (id,)
    )
    relaciones = cursor.fetchone()['total']
    if relaciones > 0:
        cursor.close()
        conn.close()
        flash(
            f'No se puede eliminar "{servicio["nombre"]}" porque está relacionado '
            f'con {relaciones} detalle(s) de factura o cotización. Puedes editarlo '
            'o marcarlo como no disponible.',
            'danger'
        )
        return redirect(url_for('servicios'))

    cursor.execute('DELETE FROM servicios WHERE id = %s', (id,))
    conn.commit()
    cursor.close()
    conn.close()

    registrar_log('ELIMINAR_SERVICIO', f"Servicio {servicio['nombre']} (ID {id}) eliminado por {current_user.usuario}")
    flash(f'Servicio "{servicio["nombre"]}" eliminado correctamente.', 'success')
    return redirect(url_for('servicios'))


# ==============================================================================
# MÓDULO CRUD: PROVEEDORES
# ==============================================================================

@app.route('/proveedores/nuevo', methods=['GET', 'POST'])
@role_required('Administrador', 'Soporte técnico')
def nuevo_proveedor():
    """
    Registra un nuevo proveedor de servicios o infraestructura en PostgreSQL.
    Acceso para Administrador y Soporte técnico.
    """
    conn = get_db_connection()
    cursor = conn.cursor()
    cursor.execute('SELECT * FROM estados_proveedor ORDER BY id')
    estados = cursor.fetchall()
    cursor.execute('SELECT * FROM categorias_proveedor ORDER BY nombre')
    categorias = cursor.fetchall()

    form = ProveedorForm()
    form.estado_id.choices = [(e['id'], e['nombre']) for e in estados]
    form.categoria_id.choices = [(c['id'], c['nombre']) for c in categorias]

    if form.validate_on_submit():
        cursor.execute(
            'INSERT INTO proveedores (nombre, categoria_id, sitio, estado_id) VALUES (%s, %s, %s, %s)',
            (form.nombre.data.strip(), form.categoria_id.data,
             form.sitio.data.strip(), form.estado_id.data)
        )
        conn.commit()
        cursor.close()
        conn.close()

        registrar_log('CREAR_PROVEEDOR', f"Proveedor {form.nombre.data.strip()} creado por {current_user.usuario}")
        flash('Proveedor registrado correctamente.', 'success')
        return redirect(url_for('proveedores'))

    cursor.close()
    conn.close()
    return render_template('formulario_proveedor.html', form=form, editando=False)


@app.route('/proveedores/editar/<int:id>', methods=['GET', 'POST'])
@role_required('Administrador', 'Soporte técnico')
def editar_proveedor(id):
    """
    Modifica los datos de un proveedor existente en PostgreSQL.
    Acceso para Administrador y Soporte técnico.
    """
    conn = get_db_connection()
    cursor = conn.cursor()
    cursor.execute('SELECT * FROM proveedores WHERE id = %s', (id,))
    proveedor = cursor.fetchone()

    if proveedor is None:
        cursor.close()
        conn.close()
        flash('El proveedor seleccionado no existe.', 'danger')
        return redirect(url_for('proveedores'))

    cursor.execute('SELECT * FROM estados_proveedor ORDER BY id')
    estados = cursor.fetchall()
    cursor.execute('SELECT * FROM categorias_proveedor ORDER BY nombre')
    categorias = cursor.fetchall()

    form = ProveedorForm(data=dict(proveedor)) if request.method == 'GET' else ProveedorForm()
    form.estado_id.choices = [(e['id'], e['nombre']) for e in estados]
    form.categoria_id.choices = [(c['id'], c['nombre']) for c in categorias]
    if request.method == 'GET':
        form.estado_id.data = proveedor['estado_id']
        form.categoria_id.data = proveedor['categoria_id']

    if form.validate_on_submit():
        cursor.execute(
            'UPDATE proveedores SET nombre=%s, categoria_id=%s, sitio=%s, estado_id=%s WHERE id=%s',
            (form.nombre.data.strip(), form.categoria_id.data,
             form.sitio.data.strip(), form.estado_id.data, id)
        )
        conn.commit()
        cursor.close()
        conn.close()

        registrar_log('EDITAR_PROVEEDOR', f"Proveedor {form.nombre.data.strip()} (ID {id}) actualizado por {current_user.usuario}")
        flash(f'Proveedor "{form.nombre.data.strip()}" actualizado correctamente.', 'success')
        return redirect(url_for('proveedores'))

    cursor.close()
    conn.close()
    return render_template('formulario_proveedor.html', form=form, editando=True, id=id)


@app.route('/proveedores/eliminar/<int:id>', methods=['POST'])
@role_required('Administrador')
def eliminar_proveedor(id):
    """
    Elimina un proveedor de PostgreSQL.
    Acceso exclusivo para el rol Administrador.
    """
    conn = get_db_connection()
    cursor = conn.cursor()
    cursor.execute('SELECT * FROM proveedores WHERE id = %s', (id,))
    proveedor = cursor.fetchone()

    if proveedor is None:
        cursor.close()
        conn.close()
        flash('El proveedor seleccionado no existe.', 'danger')
        return redirect(url_for('proveedores'))

    cursor.execute('DELETE FROM proveedores WHERE id = %s', (id,))
    conn.commit()
    cursor.close()
    conn.close()

    registrar_log('ELIMINAR_PROVEEDOR', f"Proveedor {proveedor['nombre']} (ID {id}) eliminado por {current_user.usuario}")
    flash(f'Proveedor "{proveedor["nombre"]}" eliminado correctamente.', 'success')
    return redirect(url_for('proveedores'))


# ==============================================================================
# MÓDULO CRUD: CATEGORÍAS DE PROVEEDOR
# ==============================================================================

@app.route('/categorias-proveedor')
@role_required('Administrador', 'Soporte técnico')
def categorias_proveedor():
    """
    Lista las categorías de infraestructura disponibles para clasificar proveedores.
    """
    conn = get_db_connection()
    cursor = conn.cursor()
    cursor.execute('SELECT * FROM categorias_proveedor ORDER BY nombre')
    lista_categorias = cursor.fetchall()
    cursor.close()
    conn.close()
    return render_template('categorias_proveedor.html', categorias=lista_categorias)


@app.route('/categorias-proveedor/nueva', methods=['GET', 'POST'])
@role_required('Administrador', 'Soporte técnico')
def nueva_categoria_proveedor():
    """
    Registra una nueva categoría de proveedor.
    """
    form = CategoriaProveedorForm()
    if form.validate_on_submit():
        conn = get_db_connection()
        cursor = conn.cursor()
        cursor.execute('INSERT INTO categorias_proveedor (nombre) VALUES (%s)', (form.nombre.data.strip(),))
        conn.commit()
        cursor.close()
        conn.close()

        registrar_log('CREAR_CATEGORIA_PROVEEDOR', f"Categoría {form.nombre.data.strip()} creada por {current_user.usuario}")
        flash('Categoría registrada correctamente.', 'success')
        return redirect(url_for('categorias_proveedor'))
    return render_template('formulario_categoria_proveedor.html', form=form, editando=False)


@app.route('/categorias-proveedor/editar/<int:id>', methods=['GET', 'POST'])
@role_required('Administrador', 'Soporte técnico')
def editar_categoria_proveedor(id):
    """
    Edita el nombre de una categoría de proveedor existente.
    """
    conn = get_db_connection()
    cursor = conn.cursor()
    cursor.execute('SELECT * FROM categorias_proveedor WHERE id = %s', (id,))
    categoria = cursor.fetchone()

    if categoria is None:
        cursor.close()
        conn.close()
        flash('La categoría seleccionada no existe.', 'danger')
        return redirect(url_for('categorias_proveedor'))

    form = CategoriaProveedorForm(data=dict(categoria)) if request.method == 'GET' else CategoriaProveedorForm()

    if form.validate_on_submit():
        cursor.execute('UPDATE categorias_proveedor SET nombre=%s WHERE id=%s', (form.nombre.data.strip(), id))
        conn.commit()
        cursor.close()
        conn.close()

        registrar_log('EDITAR_CATEGORIA_PROVEEDOR', f"Categoría ID {id} actualizada a {form.nombre.data.strip()} por {current_user.usuario}")
        flash(f'Categoría "{form.nombre.data.strip()}" actualizada correctamente.', 'success')
        return redirect(url_for('categorias_proveedor'))

    cursor.close()
    conn.close()
    return render_template('formulario_categoria_proveedor.html', form=form, editando=True, id=id)


@app.route('/categorias-proveedor/eliminar/<int:id>', methods=['POST'])
@role_required('Administrador', 'Soporte técnico')
def eliminar_categoria_proveedor(id):
    """
    Elimina una categoría de proveedor, siempre que ningún proveedor la esté usando.
    """
    conn = get_db_connection()
    cursor = conn.cursor()
    cursor.execute('SELECT * FROM categorias_proveedor WHERE id = %s', (id,))
    categoria = cursor.fetchone()

    if categoria is None:
        cursor.close()
        conn.close()
        flash('La categoría seleccionada no existe.', 'danger')
        return redirect(url_for('categorias_proveedor'))

    cursor.execute('SELECT COUNT(*) AS total FROM proveedores WHERE categoria_id = %s', (id,))
    en_uso = cursor.fetchone()['total']
    if en_uso > 0:
        cursor.close()
        conn.close()
        flash(f'No se puede eliminar "{categoria["nombre"]}" porque hay proveedores asignados a esta categoría.', 'danger')
        return redirect(url_for('categorias_proveedor'))

    cursor.execute('DELETE FROM categorias_proveedor WHERE id = %s', (id,))
    conn.commit()
    cursor.close()
    conn.close()

    registrar_log('ELIMINAR_CATEGORIA_PROVEEDOR', f"Categoría {categoria['nombre']} (ID {id}) eliminada por {current_user.usuario}")
    flash(f'Categoría "{categoria["nombre"]}" eliminada correctamente.', 'success')
    return redirect(url_for('categorias_proveedor'))


# ==============================================================================
# MÓDULO CRUD: FACTURACIÓN
# ==============================================================================

@app.route('/facturacion/nueva', methods=['GET', 'POST'])
@role_required('Administrador', 'Gestor de proyectos')
@permission_required('facturas.crear')
def nueva_factura():
    """
    Emite un nuevo documento comercial (Factura o Cotización).
    El cliente se selecciona de una lista real (cliente_cedula), y cada servicio
    incluido se guarda como una fila propia en detalle_factura.
    Acceso para Administrador, Gestor de proyectos y Usuario interno.
    Genera automáticamente el número correlativo si no se especifica.
    """
    form = FacturacionForm()
    tipo_solicitado = request.args.get('tipo', 'Cotizacion' if request.args.get('servicio_id') is not None else 'Factura')

    conn = get_db_connection()
    cursor = conn.cursor()

    cursor.execute('SELECT * FROM clientes ORDER BY nombre')
    clientes_registrados = cursor.fetchall()
    form.cliente_cedula.choices = [(c['cedula'], c['nombre']) for c in clientes_registrados]

    cursor.execute('SELECT * FROM estados_documento ORDER BY id')
    estados = cursor.fetchall()
    form.estado_id.choices = [(e['id'], e['nombre']) for e in estados]
    id_por_nombre = {e['nombre']: e['id'] for e in estados}

    if request.method == 'GET':
        cursor.execute("SELECT last_value, is_called FROM " + ("secuencia_cotizaciones" if tipo_solicitado == 'Cotizacion' else "secuencia_facturas"))
        seq_row = cursor.fetchone()
        proximo = (seq_row['last_value'] + 1) if (seq_row and seq_row['is_called']) else (seq_row['last_value'] if seq_row else 1)
        form.tipo.data = tipo_solicitado
        if tipo_solicitado == 'Cotizacion':
            form.numero.data = f"COT-2026-{proximo:04d}"
            form.validez.data = "15 días"
            form.estado_id.data = id_por_nombre.get('En revision')
        else:
            form.numero.data = f"001-001-{proximo:04d}"
            form.validez.data = "30 días"
            form.estado_id.data = id_por_nombre.get('Pendiente')
        form.fecha.data = str(date.today())
        form.anticipo.data = 0.00
        form.saldo_pendiente.data = 0.00

    if form.validate_on_submit():
        tipo_doc = form.tipo.data
        numero_limpio = form.numero.data.strip() if form.numero.data else ''
        numero_param = None

        if numero_limpio:
            cursor.execute('SELECT 1 FROM facturacion WHERE numero = %s', (numero_limpio,))
            if cursor.fetchone() is not None:
                cursor.execute('SELECT * FROM servicios')
                servicios_catalogo = cursor.fetchall()
                cursor.close()
                conn.close()
                flash(f'Ya existe un documento con el número "{numero_limpio}". Usa un número distinto.', 'danger')
                return render_template(
                    'formulario_facturacion.html', form=form, editando=False,
                    servicios_catalogo=servicios_catalogo, clientes_registrados=clientes_registrados,
                    servicio_seleccionado_id=request.args.get('servicio_id', type=int)
                )
            numero_param = numero_limpio

        servicios_detalle = []
        if form.servicios_json.data:
            try:
                servicios_detalle = json.loads(form.servicios_json.data)
            except (TypeError, ValueError, json.JSONDecodeError):
                servicios_detalle = []

        if not servicios_detalle:
            conn.rollback()
            cursor.close()
            conn.close()
            flash('Agrega al menos un servicio antes de guardar el documento.', 'danger')
            cursor_reintento = get_db_connection()
            try:
                with cursor_reintento.cursor() as cursor_catalogo:
                    cursor_catalogo.execute('SELECT * FROM servicios ORDER BY nombre')
                    servicios_catalogo = cursor_catalogo.fetchall()
            finally:
                cursor_reintento.close()
            return render_template(
                'formulario_facturacion.html', form=form, editando=False,
                servicios_catalogo=servicios_catalogo, clientes_registrados=clientes_registrados,
                servicio_seleccionado_id=request.args.get('servicio_id', type=int)
            )

        precios_catalogo = {}
        ids_catalogo = {
            int(item.get('id')) for item in servicios_detalle
            if str(item.get('id', '')).isdigit()
        }
        if ids_catalogo:
            cursor.execute(
                'SELECT id, nombre, precio_base FROM servicios WHERE id = ANY(%s)',
                (list(ids_catalogo),)
            )
            precios_catalogo = {row['id']: row for row in cursor.fetchall()}

        detalles_validados = []
        for item in servicios_detalle:
            servicio_id = int(item.get('id')) if str(item.get('id', '')).isdigit() else None
            catalogo = precios_catalogo.get(servicio_id)
            precio = float(catalogo['precio_base']) if catalogo else float(item.get('precio', 0))
            cantidad = int(item.get('cantidad', 1))
            ajuste = float(item.get('ajuste', 0))
            if cantidad < 1 or precio < 0:
                conn.rollback()
                cursor.close()
                conn.close()
                flash('La cantidad y el precio de cada servicio deben ser válidos.', 'danger')
                return redirect(url_for('nueva_factura', tipo=tipo_doc))
            detalles_validados.append({
                'id': servicio_id,
                'servicio': catalogo['nombre'] if catalogo else str(item.get('servicio', 'Servicio')).strip(),
                'cantidad': cantidad,
                'precio': precio,
                'ajuste': ajuste,
                'total': (precio + ajuste) * cantidad
            })

        servicios_detalle = detalles_validados
        subtotal_calculado = round(sum(item['total'] for item in servicios_detalle), 2)
        aplica_iva = float(form.iva.data or 0) > 0
        subtotal_val = subtotal_calculado
        iva_val = round(subtotal_val * 0.15, 2) if aplica_iva else 0.0
        total_val = round(subtotal_val + iva_val, 2)
        anticipo_val = float(form.anticipo.data) if form.anticipo.data else 0.0
        saldo_val = round(total_val - anticipo_val, 2)      
        # Evitar que el abono sea mayor al total
        if anticipo_val > total_val:
            conn.rollback()
            cursor.close()
            conn.close()

            flash(
                f'El abono (${anticipo_val:.2f}) no puede ser  mayor '
                f'al total del documento (${total_val:.2f}).',
                'danger'
            )
            return redirect(url_for('nueva_factura', tipo=tipo_doc))
        # REGLA DEL SISTEMA:
        # Una factura final solo puede emitirse cuando el pago está completo.
        if tipo_doc == 'Factura' and saldo_val > 0:
            conn.rollback()
            cursor.close()
            conn.close()

            flash(
                f'No se puede emitir una factura final con saldo '
                f'pendiente de ${saldo_val:.2f}. '
                'warning'
            )
            return redirect(url_for('nueva_factura', tipo='Cotizacion'))
        estado_id_final = form.estado_id.data 

        if tipo_doc == 'Factura' and saldo_val == 0:
            estado_id_final = id_por_nombre.get('Pagada', estado_id_final) 

        notas_final = form.notas.data.strip() if form.notas.data else (
            "Propuesta emitida por NexoDigital." if tipo_doc == 'Cotizacion' else "Comprobante emitido por NexoDigital."
        )

        # Inserción con autogeneración secuencial atómica (trigger en PostgreSQL si numero_param es None)
        cursor.execute(
            '''INSERT INTO facturacion
               (numero, tipo, cliente_cedula, fecha, validez, subtotal, iva, monto, anticipo, saldo_pendiente, estado_id, notas)
               VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
               RETURNING numero''',
            (numero_param, tipo_doc, form.cliente_cedula.data, str(form.fecha.data),
             form.validez.data.strip() if form.validez.data else "15 días",
             subtotal_val, iva_val, total_val, anticipo_val, saldo_val, estado_id_final, notas_final)
        )
        row_insertado = cursor.fetchone()
        numero_limpio = row_insertado['numero']


        for item in servicios_detalle:
            cursor.execute(
                '''INSERT INTO detalle_factura (factura_numero, servicio_id, nombre_servicio, cantidad, precio_base, ajuste, total)
                   VALUES (%s, %s, %s, %s, %s, %s, %s)''',
                (numero_limpio, item.get('id'), item.get('servicio', 'Servicio'),
                 int(item.get('cantidad', 1)), float(item.get('precio', 0)),
                 float(item.get('ajuste', 0)), float(item.get('total', item.get('precio', 0))))
            )

        conn.commit()
        cursor.close()
        conn.close()

        nombre_doc = "Cotización" if tipo_doc == 'Cotizacion' else "Factura"
        registrar_log('EMITIR_FACTURA', f"{nombre_doc} {numero_limpio} emitida por {current_user.usuario} por un monto de ${total_val:.2f}")
        flash(f'{nombre_doc} "{numero_limpio}" guardada correctamente.', 'success')
        return redirect(url_for('facturacion'))

    cursor.execute('SELECT * FROM servicios')
    servicios_catalogo = cursor.fetchall()
    cursor.close()
    conn.close()

    return render_template(
        'formulario_facturacion.html',
        form=form,
        editando=False,
        servicios_catalogo=servicios_catalogo,
        clientes_registrados=clientes_registrados,
        servicio_seleccionado_id=request.args.get('servicio_id', type=int)
    )


@app.route('/facturacion/editar/<numero>', methods=['GET', 'POST'])
@role_required('Administrador', 'Gestor de proyectos')
@permission_required('facturas.editar')
def editar_factura(numero):
    """
    Edita un documento comercial existente, identificado por su número (clave primaria).
    El número no se modifica desde este formulario, ya que detalle_factura depende de él.
    Acceso para Administrador y Gestor de proyectos.
    """
    conn = get_db_connection()
    cursor = conn.cursor()
    cursor.execute('SELECT * FROM facturacion WHERE numero = %s', (numero,))
    fila = cursor.fetchone()

    if fila is None:
        cursor.close()
        conn.close()
        flash('El documento seleccionado no existe.', 'danger')
        return redirect(url_for('facturacion'))

    factura = dict(fila)
    cursor.execute('SELECT * FROM detalle_factura WHERE factura_numero = %s', (numero,))
    detalle_actual = cursor.fetchall()
    factura['servicios_detalle'] = [
        {'id': d['servicio_id'], 'servicio': d['nombre_servicio'], 'cantidad': int(d['cantidad']),
         'precio': float(d['precio_base']), 'ajuste': float(d['ajuste']), 'total': float(d['total'])}
        for d in detalle_actual
    ]

    cursor.execute('SELECT * FROM clientes ORDER BY nombre')
    clientes_registrados = cursor.fetchall()
    cursor.execute('SELECT * FROM estados_documento ORDER BY id')
    estados = cursor.fetchall()

    form = FacturacionForm(data=factura) if request.method == 'GET' else FacturacionForm()
    form.cliente_cedula.choices = [(c['cedula'], c['nombre']) for c in clientes_registrados]
    form.estado_id.choices = [(e['id'], e['nombre']) for e in estados]

    if request.method == 'GET':
        form.cliente_cedula.data = factura['cliente_cedula']
        form.estado_id.data = factura['estado_id']
        form.servicios_json.data = json.dumps(factura['servicios_detalle'])

    if form.validate_on_submit():
        servicios_detalle = []
        if form.servicios_json.data:
            try:
                servicios_detalle = json.loads(form.servicios_json.data)
            except Exception:
                servicios_detalle = factura.get('servicios_detalle', [])

        subtotal_val = float(form.subtotal.data) if form.subtotal.data is not None else float(form.monto.data)
        iva_val = float(form.iva.data) if form.iva.data is not None else round(subtotal_val * 0.15, 2)
        total_val = float(form.monto.data)
        anticipo_val = float(form.anticipo.data) if form.anticipo.data is not None else 0.00
        saldo_val = float(form.saldo_pendiente.data) if form.saldo_pendiente.data is not None else max(0.0, total_val - anticipo_val)
        tipo_doc = form.tipo.data
        notas_final = form.notas.data.strip() if form.notas.data else "Documento generado por NexoDigital."

        cursor.execute(
            '''UPDATE facturacion SET
               tipo=%s, cliente_cedula=%s, fecha=%s, validez=%s,
               subtotal=%s, iva=%s, monto=%s, anticipo=%s, saldo_pendiente=%s, estado_id=%s, notas=%s
               WHERE numero=%s''',
            (tipo_doc, form.cliente_cedula.data, str(form.fecha.data),
             form.validez.data.strip() if form.validez.data else "15 días",
             subtotal_val, iva_val, total_val, anticipo_val, saldo_val, form.estado_id.data, notas_final, numero)
        )

        cursor.execute('DELETE FROM detalle_factura WHERE factura_numero = %s', (numero,))
        for item in servicios_detalle:
            cursor.execute(
                '''INSERT INTO detalle_factura (factura_numero, servicio_id, nombre_servicio, cantidad, precio_base, ajuste, total)
                   VALUES (%s, %s, %s, %s, %s, %s, %s)''',
                (numero, item.get('id'), item.get('servicio', 'Servicio'),
                 int(item.get('cantidad', 1)), float(item.get('precio', 0)),
                 float(item.get('ajuste', 0)), float(item.get('total', item.get('precio', 0))))
            )

        conn.commit()
        cursor.close()
        conn.close()

        nombre_doc = "Cotización" if tipo_doc == 'Cotizacion' else "Factura"
        registrar_log('EDITAR_FACTURA', f"{nombre_doc} {numero} actualizada por {current_user.usuario}")
        flash(f'{nombre_doc} "{numero}" actualizada correctamente.', 'success')
        return redirect(url_for('facturacion'))

    cursor.execute('SELECT * FROM servicios')
    servicios_catalogo = cursor.fetchall()
    cursor.close()
    conn.close()

    return render_template(
        'formulario_facturacion.html',
        form=form,
        editando=True,
        numero=numero,
        servicios_catalogo=servicios_catalogo,
        clientes_registrados=clientes_registrados,
        detalle_existente=factura['servicios_detalle']
    )


@app.route('/facturacion/eliminar/<numero>', methods=['POST'])
@role_required('Administrador')
@permission_required('facturas.eliminar')
def eliminar_factura(numero):
    """
    Elimina un documento comercial identificado por su número. El detalle asociado
    se borra automáticamente gracias a ON DELETE CASCADE en detalle_factura.
    Acceso exclusivo para el rol Administrador.
    """
    conn = get_db_connection()
    cursor = conn.cursor()
    cursor.execute('SELECT * FROM facturacion WHERE numero = %s', (numero,))
    fila = cursor.fetchone()

    if fila is None:
        cursor.close()
        conn.close()
        flash('El documento seleccionado no existe.', 'danger')
        return redirect(url_for('facturacion'))

    tipo_str = "Cotización" if fila['tipo'] == 'Cotizacion' else "Factura"

    cursor.execute('DELETE FROM facturacion WHERE numero = %s', (numero,))
    conn.commit()
    cursor.close()
    conn.close()

    registrar_log('ELIMINAR_FACTURA', f"{tipo_str} {numero} eliminada por {current_user.usuario}")
    flash(f'{tipo_str} "{numero}" eliminada correctamente.', 'success')
    return redirect(url_for('facturacion'))


@app.route('/facturacion/comprobante/<numero>')
@role_required('Administrador', 'Gestor de proyectos', 'Cliente')
@permission_required('facturas.ver_propias')
def ver_comprobante(numero):
    """
    Genera la vista imprimible del comprobante, identificado por su número (PK).
    Acceso para Administrador, Gestor de proyectos y Cliente (solo sus propios comprobantes).
    """
    conn = get_db_connection()
    cursor = conn.cursor()
    cursor.execute('''
        SELECT f.*, c.nombre AS cliente_nombre, c.correo AS cliente_correo, e.nombre AS estado_nombre
        FROM facturacion f
        JOIN clientes c ON f.cliente_cedula = c.cedula
        JOIN estados_documento e ON f.estado_id = e.id
        WHERE f.numero = %s
    ''', (numero,))
    fila = cursor.fetchone()

    if fila is None:
        cursor.close()
        conn.close()
        flash('El documento seleccionado no existe.', 'danger')
        return redirect(url_for('facturacion'))

    # Si el usuario es Cliente, verificar que el comprobante pertenezca a sus datos
    if current_user.rol_nombre == 'Cliente':
        cliente_correo = (fila.get('cliente_correo') or '').strip().lower()
        cliente_cedula = (fila.get('cliente_cedula') or '').strip()
        cliente_nombre = (fila.get('cliente_nombre') or '').strip().lower()
        usuario_actual = current_user.usuario.strip().lower()
        correo_actual = current_user.correo.strip().lower()

        if (correo_actual != cliente_correo and
            usuario_actual != cliente_cedula.lower() and
            usuario_actual not in cliente_nombre):
            cursor.close()
            conn.close()
            registrar_log(
                'ACCESO_DENEGADO_COMPROBANTE',
                f"Cliente {current_user.usuario} intentó ver comprobante ajeno {numero} de {fila.get('cliente_nombre')}"
            )
            flash('No tienes autorización para ver comprobantes emitidos a otros clientes.', 'danger')
            return redirect(url_for('facturacion'))

    factura = dict(fila)
    cursor.execute('SELECT * FROM detalle_factura WHERE factura_numero = %s', (numero,))
    detalle = cursor.fetchall()
    cursor.close()
    conn.close()

    factura['servicios_detalle'] = [
        {'id': d['servicio_id'], 'servicio': d['nombre_servicio'], 'cantidad': d['cantidad'],
         'precio': d['precio_base'], 'ajuste': d['ajuste'], 'total': d['total']}
        for d in detalle
    ]

    return render_template('comprobante_factura.html', factura=factura, numero=numero)



# ==============================================================================
# MÓDULO: PANEL DE ESTADÍSTICAS (solo lectura)
# ==============================================================================
# Panel de resultados para la toma de decisiones del negocio. Muestra qué
# servicios son los más solicitados, usando una consulta RELACIONADA entre dos
# tablas (detalle_factura y servicios) mediante la clave foránea servicio_id.
# Cumple el requisito de "consulta relacionada entre dos tablas con JOIN".

@app.route('/estadisticas')
@role_required('Administrador', 'Gestor de proyectos', 'Cliente')
@permission_required('reportes.ver')
def estadisticas():
    """
    Panel de resultados del negocio y ranking de demanda de servicios.
    Calcula, a partir de las facturas reales:
      - El ranking de servicios más solicitados (JOIN detalle_factura + servicios).
      - Totales generales (servicios vendidos e ingresos para administradores/gestores).
    Permite acceso a Administrador, Gestor de proyectos y Clientes (solo ranking de demanda).
    """
    conn = get_db_connection()
    cursor = conn.cursor()

    # Consulta relacionada (JOIN) entre detalle_factura y servicios mediante la
    # clave foránea servicio_id. Se agrupa por servicio y se ordena del más
    # solicitado al menos solicitado.
    es_cliente = (current_user.rol_nombre == 'Cliente')
    if es_cliente:
        cursor.execute('''
            SELECT s.nombre AS servicio, t.nombre AS categoria
            FROM detalle_factura d
            JOIN servicios s ON d.servicio_id = s.id
            JOIN tipos_servicio t ON s.tipo_servicio_id = t.id
            GROUP BY s.nombre, t.nombre
            ORDER BY COUNT(*) DESC, s.nombre ASC
        ''')
    else:
        cursor.execute('''
            SELECT s.nombre AS servicio,
                   t.nombre AS categoria,
                   SUM(d.cantidad) AS unidades,
                   SUM(d.total) AS ingresos
            FROM detalle_factura d
            JOIN servicios s ON d.servicio_id = s.id
            JOIN tipos_servicio t ON s.tipo_servicio_id = t.id
            GROUP BY s.nombre, t.nombre
            ORDER BY unidades DESC
        ''')
    ranking = cursor.fetchall()

    if es_cliente:
        fila_totales = {'total_unidades': 0, 'total_ingresos': 0}
    else:
        cursor.execute('''
            SELECT COALESCE(SUM(cantidad), 0) AS total_unidades,
                   COALESCE(SUM(total), 0) AS total_ingresos
            FROM detalle_factura
        ''')
        fila_totales = cursor.fetchone()

    cursor.close()
    conn.close()

    # El servicio más solicitado es el primero del ranking (si existe).
    servicio_top = ranking[0]['servicio'] if ranking else 'Sin datos aún'
    servicio_mayor_ingreso = (
        max(ranking, key=lambda fila: fila['ingresos'] or 0)['servicio']
        if ranking and not es_cliente else 'Sin datos aún'
    )
    # La unidad máxima sirve para dibujar el ancho de las barras en la plantilla.
    max_unidades = ranking[0]['unidades'] if ranking and not es_cliente else 0
    total_ingresos_mostrar = fila_totales['total_ingresos'] if not es_cliente else 0.0

    return render_template(
        'estadisticas.html',
        ranking=ranking,
        total_unidades=fila_totales['total_unidades'],
        total_ingresos=total_ingresos_mostrar,
        servicio_top=servicio_top,
        max_unidades=max_unidades,
        es_cliente=es_cliente
    )


# ==============================================================================
# MANEJADORES DE ERRORES PERSONALIZADOS (404, 403, 500)
# ==============================================================================

@app.errorhandler(404)
def error_404(e):
    """Manejo elegante de rutas inexistentes o recursos no encontrados."""
    return render_template('404.html'), 404


@app.errorhandler(403)
def error_403(e):
    """Manejo de acceso denegado por falta de permisos o roles."""
    registrar_log('ERROR_403_ACCESO_PROHIBIDO', f"Ruta: {request.path}")
    return render_template('403.html'), 403


@app.errorhandler(psycopg2.Error)
def error_postgresql(e):
    """Evita mostrar un 500 genérico cuando PostgreSQL está temporalmente ocupado."""
    app.logger.exception('Error de PostgreSQL en %s.', request.path)
    return render_template(
        '500.html',
        codigo_http=503,
        titulo_error='Base de datos temporalmente no disponible',
        mensaje_error='La operación no se completó. Tus datos no se guardaron o quedaron a medias; inténtalo nuevamente en unos segundos.'
    ), 503


@app.errorhandler(500)
def error_500(e):
    """Manejo de errores internos del servidor o desconexión de base de datos."""
    registrar_log('ERROR_500_SERVIDOR', f"Excepción interna en {request.path}: {str(e)}")
    return render_template('500.html'), 500


@app.errorhandler(Exception)
def error_general(e):
    """
    Captura global de excepciones no controladas en producción.
    Si estamos en modo DEBUG de desarrollo, permite la propagación para que Flask
    muestre el depurador detallado en consola.
    """
    if app.debug:
        raise e
    registrar_log('EXCEPCION_NO_CONTROLADA', f"Error en {request.path}: {str(e)}")
    return render_template('500.html'), 500


# ==============================================================================
# PUNTO DE ENTRADA PRINCIPAL DE LA APLICACIÓN
# ==============================================================================
if __name__ == '__main__':
    # Render proporciona el puerto mediante la variable PORT.
    app.run(
        host='0.0.0.0',
        port=int(os.getenv('PORT', '5000')),
        debug=os.getenv('FLASK_DEBUG', '').lower() == 'true'
    )
