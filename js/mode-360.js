// ═══════════════════════════════════════════════════════════════
//  MODO 360° — Motor de lienzo panorámico equirectangular
//  Renderiza un mapa 2D (equirectangular) y proyecta en vista esfera
//  mediante GPU WebGL (Shader de Raycasting en tiempo real a 60-144 FPS).
//  Reutiliza: paleta de color, tamaño de pincel, opacidad, historia,
//             y el puntero clásico del sistema (CURSOR.png).
//  Archivo independiente — no altera la lógica de ilustración/animación.
// ═══════════════════════════════════════════════════════════════

/* ───── Estado global del modo 360° ───── */
const MODE360 = {
    W: 4096,   // ancho del mapa equirectangular (relación 2:1)
    H: 2048,   // alto del mapa equirectangular

    // Cámara del mapa plano
    cam: { x: 0, y: 0, z: 1 },

    // Cámara de la esfera
    yaw: 0,
    pitch: 0,
    fov: 1.5,

    // Canvas de arte (para composición multicapa)
    artCanvas: null,
    artCtx: null,

    // Canvas de vista esférica y estado WebGL GPU
    pvCanvas: null,
    gl: null,
    glProg: null,
    glTex: null,
    glUniforms: {},

    // Bandera de textura desactualizada
    srcStale: true,

    // Opciones
    poleCompensation: true,
    showGuides: true,

    // Dibujo
    lastPt: null,
    isDrawing: false,

    // Navegación mapa
    mapPts: new Map(),
    mapPan: null,
    mapPinch: null,
    cursorPos: null,

    // Navegación esfera
    spherePts: new Map(),
    sphereDrag: null,
    spherePinch: null,

    // Historial (snapshots de canvas acelerados por hardware)
    history: [],
    historyIndex: -1,
    MAX_HISTORY: 30,

    // Render flags
    renderPending: false,
    pvRenderPending: false,
};

/* ─── Sistema de capas 360° ─── */
let layers360 = [];
let selectedLayerIndex360 = 0;

/* ─── DOM del overlay ─── */
let overlay360 = null;
let mapCanvas360 = null;
let mapCtx360 = null;
let cursorCanvas360 = null;
let cursorCtx360 = null;
let _cur360View = 'map';

// ─────────────────────────────────────────────────────────────
//  PUNTO DE ENTRADA
// ─────────────────────────────────────────────────────────────
function initProject360() {
    if (layers360.length === 0) {
        layers360 = [_new360Layer('Fondo 360')];
        selectedLayerIndex360 = 0;
    }

    if (!overlay360) _build360Overlay();

    if (!MODE360.artCanvas) {
        MODE360.artCanvas = document.createElement('canvas');
        MODE360.artCanvas.width  = MODE360.W;
        MODE360.artCanvas.height = MODE360.H;
        MODE360.artCtx = MODE360.artCanvas.getContext('2d', { willReadFrequently: true });
    }

    const sh = window.innerHeight;
    const sw = window.innerWidth;
    MODE360.cam.z = Math.min(sw / (MODE360.W + 100), sh / (MODE360.H + 100));
    MODE360.cam.x = 0;
    MODE360.cam.y = 0;

    MODE360.srcStale = true;
    MODE360.history = [];
    MODE360.historyIndex = -1;
    _360PushHistory();

    overlay360.style.display = 'flex';
    overlay360.classList.remove('hidden');

    const area = document.getElementById('area360');
    if (typeof eyedropperPreview !== 'undefined' && eyedropperPreview && area && eyedropperPreview.parentElement !== area) {
        area.appendChild(eyedropperPreview);
    }

    // Populate the main sidebar layer panel with 360 layers
    _360UpdateLayersUI();

    _resizeMapCanvas();
    _request360Render();
    _draw360Cursor();
}

function exit360Mode() {
    if (overlay360) {
        overlay360.style.display = 'none';
        overlay360.classList.add('hidden');
    }
    const mainEl = document.querySelector('main');
    if (typeof eyedropperPreview !== 'undefined' && eyedropperPreview && mainEl && eyedropperPreview.parentElement !== mainEl) {
        mainEl.appendChild(eyedropperPreview);
    }
    is360Mode = false;
    projectType = 'illustration';
    if (typeof updateAnimationUIState === 'function') updateAnimationUIState(false);
    // Restore the layer panel to illustration layers
    if (typeof updateLayersUI === 'function') updateLayersUI();
    requestRender();
}

// ─────────────────────────────────────────────────────────────
//  CONSTRUCCIÓN DEL OVERLAY
// ─────────────────────────────────────────────────────────────
function _build360Overlay() {
    /* ── Estilos ── */
    const style = document.createElement('style');
    style.textContent = `
    #overlay-360 { position:fixed;inset:0;z-index:900;display:none;flex-direction:column;background:#0d0d14;font-family:'Outfit','Segoe UI',sans-serif; }
    #bar360 { display:flex;align-items:center;gap:6px;flex-wrap:wrap;padding:5px 10px;
        background:rgba(15,15,22,0.97);border-bottom:1px solid rgba(255,255,255,0.07);user-select:none;z-index:20; }
    .btn360 { font:600 11px 'Outfit',sans-serif;background:rgba(255,255,255,0.06);border:1px solid rgba(255,255,255,0.1);
        color:rgba(255,255,255,0.65);border-radius:6px;padding:4px 9px;cursor:pointer;transition:all .15s;white-space:nowrap; }
    .btn360:hover { background:rgba(255,255,255,0.12);color:#fff; }
    .btn360.a360 { background:linear-gradient(135deg,rgba(108,99,255,.45),rgba(167,139,250,.35));
        border-color:rgba(108,99,255,.6);color:#fff; }
    .lbl360 { display:flex;align-items:center;gap:5px;font-size:11px;color:rgba(255,255,255,.5);cursor:pointer; }
    .lbl360 input[type=checkbox] { accent-color:#6c63ff; }
    .sep360 { width:1px;height:20px;background:rgba(255,255,255,.08);margin:0 3px; }
    #area360 { position:relative;display:flex;flex:1;min-height:0;overflow:hidden; }
    #canvas360-map, #canvas360-sphere { position:absolute;inset:0;width:100%;height:100%;touch-action:none;cursor:none;display:block; }
    #canvas360-cursor { position:absolute;inset:0;width:100%;height:100%;pointer-events:none;z-index:10; }
    `;
    document.head.appendChild(style);

    /* ── Overlay principal ── */
    overlay360 = document.createElement('div');
    overlay360.id = 'overlay-360';
    overlay360.classList.add('hidden');
    document.body.appendChild(overlay360);

    /* ── Barra superior ── */
    const bar = document.createElement('div');
    bar.id = 'bar360';
    overlay360.appendChild(bar);

    const badge = document.createElement('span');
    badge.style.cssText = 'font:700 12px Outfit;letter-spacing:1px;background:linear-gradient(90deg,#6c63ff,#a78bfa);-webkit-background-clip:text;-webkit-text-fill-color:transparent;';
    badge.textContent = '🌐 MODO 360°';
    bar.appendChild(badge);

    const sep = () => { const d = document.createElement('div'); d.className = 'sep360'; return d; };

    bar.appendChild(sep());

    // Vista mapa / esfera
    const btnMap    = _mkBtn360('🗺️ Mapa', 'btn360-map', 'a360');
    const btnSphere = _mkBtn360('🌐 Esfera', 'btn360-sphere');
    bar.appendChild(btnMap); bar.appendChild(btnSphere);

    bar.appendChild(sep());

    // Opciones
    const chkComp   = _mkChk360('Comp. polos', 'chk360-comp', true);
    const chkGuides = _mkChk360('Guías', 'chk360-guides', true);
    bar.appendChild(chkComp); bar.appendChild(chkGuides);

    bar.appendChild(sep());

    // Modo Lazo (Libre / Rectangular)
    const btnLassoMode = _mkBtn360('📐 Lazo: Libre', 'btn360-lasso-mode');
    btnLassoMode.title = 'Alternar entre Lazo Libre y Lazo Rectangular';
    btnLassoMode.style.display = (typeof currentBrush !== 'undefined' && currentBrush && currentBrush.isLasso) ? 'inline-block' : 'none';
    btnLassoMode.addEventListener('click', () => {
        lassoFillMode = (lassoFillMode === 'libre' ? 'rectangulo' : 'libre');
        _sync360LassoUI();
        if (typeof updateTopSubtoolBar === 'function') updateTopSubtoolBar();
        _draw360Cursor();
    });
    bar.appendChild(btnLassoMode);

    // Gotero (Herramienta y Modo)
    const btnEyedropper = _mkBtn360('💧 Gotero', 'btn360-eyedropper');
    btnEyedropper.title = 'Herramienta Gotero (T)';
    btnEyedropper.addEventListener('click', () => {
        if (typeof currentTool !== 'undefined' && currentTool === 'eyedropper') {
            selectTool('pincel', (typeof lastBrushTool !== 'undefined' ? lastBrushTool : 'Pincel'));
        } else {
            selectTool('eyedropper', 'Gotero');
        }
        _draw360Cursor();
    });
    bar.appendChild(btnEyedropper);

    const btnEyedropperMode = _mkBtn360('🎨 Gotero: Captura', 'btn360-eyedropper-mode');
    btnEyedropperMode.title = 'Alternar entre Modo Captura (con capas y fondo) y Modo Original (píxel puro)';
    btnEyedropperMode.style.display = (typeof currentTool !== 'undefined' && currentTool === 'eyedropper') ? 'inline-block' : 'none';
    btnEyedropperMode.addEventListener('click', () => {
        eyedropperMode = (typeof eyedropperMode !== 'undefined' && eyedropperMode === 'captura' ? 'original' : 'captura');
        _sync360EyedropperUI();
        if (typeof updateEyedropperModeUI === 'function') updateEyedropperModeUI();
        _draw360Cursor();
    });
    bar.appendChild(btnEyedropperMode);

    // Acciones
    const btnUndo   = _mkBtn360('↩ Deshacer', 'btn360-undo');
    const btnRedo   = _mkBtn360('↪ Rehacer',  'btn360-redo');
    const btnExport = _mkBtn360('⬇ PNG', 'btn360-export');
    btnExport.style.cssText += 'background:rgba(108,99,255,.2);border-color:rgba(108,99,255,.4);';
    bar.appendChild(btnUndo); bar.appendChild(btnRedo); bar.appendChild(btnExport);

    // Salir (derecha)
    const btnExit = _mkBtn360('✕ Salir', 'btn360-exit');
    btnExit.style.cssText += 'margin-left:auto;background:rgba(200,50,50,.15);border-color:rgba(200,50,50,.3);color:#f87171;';
    bar.appendChild(btnExit);

    /* ── Área de canvas ── */
    const area = document.createElement('div');
    area.id = 'area360';
    overlay360.appendChild(area);

    // Canvas mapa 2D
    mapCanvas360 = document.createElement('canvas');
    mapCanvas360.id = 'canvas360-map';
    mapCtx360 = mapCanvas360.getContext('2d');
    area.appendChild(mapCanvas360);

    // Canvas vista esférica 3D (GPU WebGL)
    MODE360.pvCanvas = document.createElement('canvas');
    MODE360.pvCanvas.id = 'canvas360-sphere';
    MODE360.pvCanvas.style.display = 'none';
    area.appendChild(MODE360.pvCanvas);
    _init360GL();

    // Canvas overlay exclusivo para el puntero
    cursorCanvas360 = document.createElement('canvas');
    cursorCanvas360.id = 'canvas360-cursor';
    cursorCtx360 = cursorCanvas360.getContext('2d');
    area.appendChild(cursorCanvas360);

    /* ── Eventos de la barra ── */
    btnMap.addEventListener('click', () => _set360View('map'));
    btnSphere.addEventListener('click', () => _set360View('sphere'));

    document.getElementById('chk360-comp').addEventListener('change', e => {
        MODE360.poleCompensation = e.target.checked;
        _draw360Cursor();
    });
    document.getElementById('chk360-guides').addEventListener('change', e => {
        MODE360.showGuides = e.target.checked;
        _request360Render();
    });

    btnUndo.addEventListener('click', _360Undo);
    btnRedo.addEventListener('click', _360Redo);
    btnExport.addEventListener('click', _360Export);
    btnExit.addEventListener('click', () => {
        if (confirm('¿Salir del modo 360°? Los cambios se guardarán automáticamente.')) {
            saveCurrentProject().then(() => exit360Mode());
        }
    });

    /* ── Resize observer ── */
    new ResizeObserver(() => {
        _resizeMapCanvas();
        _request360Render();
        if (_cur360View === 'sphere') _request360PvRender();
        _draw360Cursor();
    }).observe(area);

    /* ── Eventos canvas ── */
    _bindMapEvents();
    _bindSphereEvents();
}

function _mkBtn360(label, id, extraClass) {
    const b = document.createElement('button');
    b.className = 'btn360' + (extraClass ? ' ' + extraClass : '');
    b.id = id; b.textContent = label;
    return b;
}

function _mkChk360(label, id, checked) {
    const lbl = document.createElement('label');
    lbl.className = 'lbl360';
    const chk = document.createElement('input');
    chk.type = 'checkbox'; chk.id = id; chk.checked = !!checked;
    lbl.appendChild(chk);
    lbl.appendChild(document.createTextNode(label));
    return lbl;
}

// ─────────────────────────────────────────────────────────────
//  MOTOR WEBGL GPU PARA LA ESFERA (CERO LAG A 60-144 FPS)
// ─────────────────────────────────────────────────────────────
function _init360GL() {
    if (!MODE360.pvCanvas) return false;
    const gl = MODE360.pvCanvas.getContext('webgl', {
        alpha: false,
        depth: false,
        stencil: false,
        antialias: false,
        powerPreference: 'high-performance',
        preserveDrawingBuffer: false
    }) || MODE360.pvCanvas.getContext('experimental-webgl');

    if (!gl) {
        console.error("WebGL no disponible");
        return false;
    }

    const vsSrc = `
        attribute vec2 a_pos;
        void main() {
            gl_Position = vec4(a_pos, 0.0, 1.0);
        }
    `;

    const fsSrc = `
        precision highp float;
        uniform sampler2D u_tex;
        uniform vec2 u_res;
        uniform float u_yaw;
        uniform float u_pitch;
        uniform float u_fov;
        uniform vec3 u_bgCol;

        const float PI = 3.14159265358979323846;

        void main() {
            float tf = tan(u_fov * 0.5);
            float asp = u_res.x / u_res.y;
            
            float nx = ((gl_FragCoord.x / u_res.x) * 2.0 - 1.0) * tf * asp;
            float ny = ((gl_FragCoord.y / u_res.y) * 2.0 - 1.0) * tf;
            
            float cp = cos(u_pitch);
            float sp = sin(u_pitch);
            float y2 = ny * cp + sp;
            float z2 = -ny * sp + cp;
            
            float len = sqrt(nx * nx + y2 * y2 + z2 * z2);
            float lon = atan(nx, z2) + u_yaw;
            float lat = asin(clamp(y2 / len, -1.0, 1.0));
            
            // UV equirectangular
            float u = (lon / (2.0 * PI)) + 0.5;
            float v = 0.5 - (lat / PI);
            
            vec4 col = texture2D(u_tex, vec2(u, v));
            gl_FragColor = vec4(mix(u_bgCol, col.rgb, col.a), 1.0);
        }
    `;

    function compile(src, type) {
        const s = gl.createShader(type);
        gl.shaderSource(s, src);
        gl.compileShader(s);
        if (!gl.getShaderParameter(s, gl.COMPILE_STATUS)) {
            console.error(gl.getShaderInfoLog(s));
            gl.deleteShader(s);
            return null;
        }
        return s;
    }

    const vs = compile(vsSrc, gl.VERTEX_SHADER);
    const fs = compile(fsSrc, gl.FRAGMENT_SHADER);
    if (!vs || !fs) return false;

    const prog = gl.createProgram();
    gl.attachShader(prog, vs);
    gl.attachShader(prog, fs);
    gl.linkProgram(prog);
    if (!gl.getProgramParameter(prog, gl.LINK_STATUS)) {
        console.error(gl.getProgramInfoLog(prog));
        return false;
    }
    gl.useProgram(prog);

    // Buffer de rectángulo completo
    const buf = gl.createBuffer();
    gl.bindBuffer(gl.ARRAY_BUFFER, buf);
    gl.bufferData(gl.ARRAY_BUFFER, new Float32Array([
        -1, -1,
         1, -1,
        -1,  1,
        -1,  1,
         1, -1,
         1,  1
    ]), gl.STATIC_DRAW);

    const aPos = gl.getAttribLocation(prog, 'a_pos');
    gl.enableVertexAttribArray(aPos);
    gl.vertexAttribPointer(aPos, 2, gl.FLOAT, false, 0, 0);

    // Uniforms
    MODE360.glUniforms = {
        tex: gl.getUniformLocation(prog, 'u_tex'),
        res: gl.getUniformLocation(prog, 'u_res'),
        yaw: gl.getUniformLocation(prog, 'u_yaw'),
        pitch: gl.getUniformLocation(prog, 'u_pitch'),
        fov: gl.getUniformLocation(prog, 'u_fov'),
        bgCol: gl.getUniformLocation(prog, 'u_bgCol')
    };

    // Textura equirectangular
    const tex = gl.createTexture();
    gl.bindTexture(gl.TEXTURE_2D, tex);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.REPEAT);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);

    MODE360.gl = gl;
    MODE360.glProg = prog;
    MODE360.glTex = tex;
    return true;
}

// ─────────────────────────────────────────────────────────────
//  VISTAS
// ─────────────────────────────────────────────────────────────
function _set360View(v) {
    _cur360View = v;
    document.getElementById('btn360-map').classList.toggle('a360', v === 'map');
    document.getElementById('btn360-sphere').classList.toggle('a360', v === 'sphere');
    mapCanvas360.style.display     = v === 'map'    ? 'block' : 'none';
    MODE360.pvCanvas.style.display = v === 'sphere' ? 'block' : 'none';
    if (v === 'sphere') {
        MODE360.srcStale = true;
        _request360PvRender();
    } else {
        _request360Render();
    }
    _draw360Cursor();
}

// ─────────────────────────────────────────────────────────────
//  RESIZE
// ─────────────────────────────────────────────────────────────
function _resizeMapCanvas() {
    if (!mapCanvas360 || !mapCanvas360.parentElement) return;
    const p = mapCanvas360.parentElement;
    const w = p.clientWidth  || window.innerWidth;
    const h = p.clientHeight || window.innerHeight;

    mapCanvas360.width  = w;
    mapCanvas360.height = h;

    if (cursorCanvas360) {
        cursorCanvas360.width  = w;
        cursorCanvas360.height = h;
    }

    if (MODE360.pvCanvas) {
        MODE360.pvCanvas.width  = w;
        MODE360.pvCanvas.height = h;
    }
}

// ─────────────────────────────────────────────────────────────
//  SUAVIZADO DE LAZO EN ESPACIO DE PANTALLA (SIN DIENTES / TREMOR)
// ─────────────────────────────────────────────────────────────
function _360SmoothScreenLasso(pts, passes = 4) {
    if (!pts || pts.length < 3) return pts || [];

    // 1. Filtrar puntos duplicados o micro-oscilaciones de hardware (< 1.5px)
    const cleaned = [pts[0]];
    for (let i = 1; i < pts.length; i++) {
        const prev = cleaned[cleaned.length - 1];
        if (Math.hypot(pts[i].x - prev.x, pts[i].y - prev.y) >= 1.5) {
            cleaned.push(pts[i]);
        }
    }
    if (cleaned.length < 3) return cleaned;

    // 2. Remuestreo equidistante uniforme a lo largo del trazo
    const step = 4.0;
    const resampled = [cleaned[0]];
    let prev = cleaned[0];
    let acc = 0;

    for (let i = 1; i < cleaned.length; i++) {
        const curr = cleaned[i];
        let d = Math.hypot(curr.x - prev.x, curr.y - prev.y);
        while (d > 0 && acc + d >= step) {
            const t = (step - acc) / d;
            const nx = prev.x + (curr.x - prev.x) * t;
            const ny = prev.y + (curr.y - prev.y) * t;
            resampled.push({ x: nx, y: ny });
            prev = { x: nx, y: ny };
            d = Math.hypot(curr.x - prev.x, curr.y - prev.y);
            acc = 0;
        }
        acc += d;
        prev = curr;
    }
    if (resampled.length < 3) return cleaned;

    // 3. Suavizado gaussiano cíclico para polígonos cerrados
    let p = resampled;
    const n = p.length;
    for (let iter = 0; iter < passes; iter++) {
        const s = new Array(n);
        for (let i = 0; i < n; i++) {
            const prevPt = p[(i - 1 + n) % n];
            const currPt = p[i];
            const nextPt = p[(i + 1) % n];
            s[i] = {
                x: prevPt.x * 0.22 + currPt.x * 0.56 + nextPt.x * 0.22,
                y: prevPt.y * 0.22 + currPt.y * 0.56 + nextPt.y * 0.22
            };
        }
        p = s;
    }
    return p;
}

function _360DrawSmoothPolygon(ctx, pts) {
    if (!pts || pts.length < 3) return;
    const n = pts.length;
    const p0 = pts[0];
    const pLast = pts[n - 1];
    const midStart = { x: (pLast.x + p0.x) * 0.5, y: (pLast.y + p0.y) * 0.5 };

    ctx.beginPath();
    ctx.moveTo(midStart.x, midStart.y);
    for (let i = 0; i < n; i++) {
        const curr = pts[i];
        const next = pts[(i + 1) % n];
        const mid = { x: (curr.x + next.x) * 0.5, y: (curr.y + next.y) * 0.5 };
        ctx.quadraticCurveTo(curr.x, curr.y, mid.x, mid.y);
    }
    ctx.closePath();
}

// ─────────────────────────────────────────────────────────────
//  HERRAMIENTA GOTERO EN MODO 360° (ORIGINAL / CAPTURA)
// ─────────────────────────────────────────────────────────────
function _rgbToHex360(r, g, b) {
    if (typeof rgbToHex === 'function') return rgbToHex(r, g, b);
    return '#' + [r, g, b].map(x => {
        const h = Math.max(0, Math.min(255, Math.round(x))).toString(16);
        return h.length === 1 ? '0' + h : h;
    }).join('');
}

function _pickColorAt360(mapX, mapY) {
    const W = MODE360.W, H = MODE360.H;
    const px = ((Math.floor(mapX) % W) + W) % W;
    const py = Math.max(0, Math.min(H - 1, Math.floor(mapY)));

    const temp = document.createElement('canvas');
    temp.width = 1; temp.height = 1;
    const tctx = temp.getContext('2d');

    const bgCol = (typeof bgMode !== 'undefined' && bgMode === 1 && typeof solidBgColor !== 'undefined') ? solidBgColor : '#1a1a24';
    tctx.fillStyle = bgCol;
    tctx.fillRect(0, 0, 1, 1);

    for (const l of layers360) {
        if (!l.visible) continue;
        tctx.save();
        tctx.globalAlpha = l.opacity;
        tctx.globalCompositeOperation = l.blendMode;
        tctx.drawImage(l.canvas, -px, -py);
        tctx.restore();
    }

    const data = tctx.getImageData(0, 0, 1, 1).data;
    return _rgbToHex360(data[0], data[1], data[2]);
}

function _pickColorRaw360(mapX, mapY) {
    const W = MODE360.W, H = MODE360.H;
    const px = ((Math.floor(mapX) % W) + W) % W;
    const py = Math.max(0, Math.min(H - 1, Math.floor(mapY)));

    // 1. Capa activa primero
    const active = layers360[selectedLayerIndex360];
    if (active && active.visible) {
        const d = active.ctx.getImageData(px, py, 1, 1).data;
        if (d[3] > 0) return _rgbToHex360(d[0], d[1], d[2]);
    }

    // 2. Capas visibles de arriba hacia abajo
    for (let i = layers360.length - 1; i >= 0; i--) {
        if (i === selectedLayerIndex360) continue;
        const l = layers360[i];
        if (!l.visible) continue;
        const d = l.ctx.getImageData(px, py, 1, 1).data;
        if (d[3] > 0) return _rgbToHex360(d[0], d[1], d[2]);
    }

    // 3. Fondo
    const bgCol = (typeof bgMode !== 'undefined' && bgMode === 1 && typeof solidBgColor !== 'undefined') ? solidBgColor : '#1a1a24';
    return bgCol;
}

function _update360EyedropperPreview(sx, sy, mapPt) {
    if (!eyedropperPreview || eyedropperPreview.classList.contains('copied')) return;
    eyedropperPreview.classList.remove('hidden');
    eyedropperPreview.style.left = sx + 'px';
    eyedropperPreview.style.top  = sy + 'px';

    const color = (typeof eyedropperMode !== 'undefined' && eyedropperMode === 'original'
        ? _pickColorRaw360(mapPt[0], mapPt[1])
        : _pickColorAt360(mapPt[0], mapPt[1])) || '#000000';

    const circle = eyedropperPreview.querySelector('.color-circle');
    const hex    = eyedropperPreview.querySelector('.color-hex');
    const modeEl = eyedropperPreview.querySelector('.ed-mode-label');
    if (circle) circle.style.background = color;
    if (hex)    hex.textContent = color;
    if (modeEl) modeEl.textContent = (typeof eyedropperMode !== 'undefined' && eyedropperMode === 'original') ? '🎨 Original' : '📷 Captura';
}

function _apply360Eyedropper(mapPt) {
    const color = (typeof eyedropperMode !== 'undefined' && eyedropperMode === 'original'
        ? _pickColorRaw360(mapPt[0], mapPt[1])
        : _pickColorAt360(mapPt[0], mapPt[1]));
    if (color) {
        selectedColor = color;
        if (typeof mainColorPicker !== 'undefined' && mainColorPicker) {
            mainColorPicker.value = color;
        }
        if (typeof updateTintedTexture === 'function') updateTintedTexture();

        if (eyedropperPreview) {
            eyedropperPreview.classList.add('copied');
            if (eyedropperFadeTimeout) clearTimeout(eyedropperFadeTimeout);
            eyedropperFadeTimeout = setTimeout(() => {
                eyedropperPreview.classList.add('hidden');
                eyedropperPreview.classList.remove('copied');
                eyedropperFadeTimeout = null;
            }, 1500);
        }
    }
}

function _sync360EyedropperUI() {
    const btnTool = document.getElementById('btn360-eyedropper');
    const isEd = (typeof currentTool !== 'undefined' && currentTool === 'eyedropper');
    if (btnTool) {
        if (isEd) btnTool.classList.add('a360');
        else btnTool.classList.remove('a360');
    }

    const btnMode = document.getElementById('btn360-eyedropper-mode');
    if (btnMode) {
        btnMode.style.display = isEd ? 'inline-block' : 'none';
        btnMode.textContent = (typeof eyedropperMode !== 'undefined' && eyedropperMode === 'original')
            ? '🎨 Gotero: Original' : '📷 Gotero: Captura';
        if (typeof eyedropperMode !== 'undefined' && eyedropperMode === 'original') {
            btnMode.classList.add('a360');
        } else {
            btnMode.classList.remove('a360');
        }
    }
}
window._sync360EyedropperUI = _sync360EyedropperUI;

// ─────────────────────────────────────────────────────────────
//  PUNTERO CLÁSICO Y PREVIEW (RENDERIZADO LIGERO AISLADO)
// ─────────────────────────────────────────────────────────────
function _draw360Cursor() {
    if (!cursorCanvas360 || !cursorCtx360) return;
    const cw = cursorCanvas360.width, ch = cursorCanvas360.height;
    cursorCtx360.clearRect(0, 0, cw, ch);

    // Sincronizar visibilidad de botones en la barra 360
    if (typeof _sync360LassoUI === 'function') _sync360LassoUI();
    if (typeof _sync360EyedropperUI === 'function') _sync360EyedropperUI();

    // ── Previsualización en vivo de trazo de Lazo (Relleno o Borrador) ──
    if (_360IsLassoActive && currentBrush && currentBrush.isLasso) {
        const isEraser = _360IsEraser();
        const mode = (typeof lassoFillMode !== 'undefined' ? lassoFillMode : 'libre');
        const fillCol = isEraser ? 'rgba(248, 113, 113, 0.32)' : 'rgba(108, 99, 255, 0.32)';
        const strokeCol = currentBrush.lassoColor || (isEraser ? '#f87171' : '#a78bfa');

        cursorCtx360.save();
        cursorCtx360.fillStyle = fillCol;
        cursorCtx360.strokeStyle = strokeCol;
        cursorCtx360.lineWidth = 1.5;
        cursorCtx360.setLineDash([6, 4]);

        if (mode === 'rectangulo' && _360LassoScreenAnchor && _360LassoScreenEnd) {
            const rx = Math.min(_360LassoScreenAnchor.x, _360LassoScreenEnd.x);
            const ry = Math.min(_360LassoScreenAnchor.y, _360LassoScreenEnd.y);
            const rw = Math.abs(_360LassoScreenEnd.x - _360LassoScreenAnchor.x);
            const rh = Math.abs(_360LassoScreenEnd.y - _360LassoScreenAnchor.y);
            cursorCtx360.fillRect(rx, ry, rw, rh);
            cursorCtx360.strokeRect(rx, ry, rw, rh);
        } else if (_360LassoScreenPath && _360LassoScreenPath.length > 1) {
            if (_360LassoScreenPath.length > 2) {
                const previewSmoothed = _360SmoothScreenLasso(_360LassoScreenPath, 2);
                _360DrawSmoothPolygon(cursorCtx360, previewSmoothed);
            } else {
                cursorCtx360.beginPath();
                cursorCtx360.moveTo(_360LassoScreenPath[0].x, _360LassoScreenPath[0].y);
                cursorCtx360.lineTo(_360LassoScreenPath[1].x, _360LassoScreenPath[1].y);
                cursorCtx360.closePath();
            }
            cursorCtx360.fill();
            cursorCtx360.stroke();
        }
        cursorCtx360.restore();
    }

    if (!MODE360.cursorPos) return;

    // Si está en paneo (arrastre o barra espaciadora), usar cursor grab nativo
    const isPan = !!(MODE360.mapPan || MODE360.sphereDrag || (typeof isSpacePressed !== 'undefined' && isSpacePressed));
    if (isPan) {
        if (mapCanvas360) mapCanvas360.style.cursor = 'grab';
        if (MODE360.pvCanvas) MODE360.pvCanvas.style.cursor = 'grab';
        return;
    } else {
        if (mapCanvas360 && mapCanvas360.style.cursor !== 'none') mapCanvas360.style.cursor = 'none';
        if (MODE360.pvCanvas && MODE360.pvCanvas.style.cursor !== 'none') MODE360.pvCanvas.style.cursor = 'none';
    }

    // Modo cursor ('always' = siempre visible incluso al pintar; 'auto' = oculto al pintar)
    const shouldShow = (typeof cursorMode === 'undefined' || cursorMode === 'always' || (!MODE360.isDrawing && !_360IsLassoActive));
    if (!shouldShow) return;

    const { x, y } = MODE360.cursorPos;

    // 1. Silueta / anillo del pincel (solo si NO es lazo y NO es gotero)
    const isLasso = !!(currentBrush && currentBrush.isLasso);
    const isEyedropper = (typeof currentTool !== 'undefined' && currentTool === 'eyedropper');
    if (!isLasso && !isEyedropper) {
        const r = _360BrushSize() / 2;
        if (r > 0) {
            cursorCtx360.save();
            const isEraser = _360IsEraser();
            const col = isEraser ? 'rgba(248,113,113,0.9)' : ((typeof selectedColor !== 'undefined' && selectedColor) ? selectedColor : '#ffffff');

            cursorCtx360.strokeStyle = col;
            cursorCtx360.lineWidth = 1.5;
            cursorCtx360.beginPath();

            if (_cur360View === 'map') {
                const z = MODE360.cam.z;
                const docY = MODE360.cam.y + y / z;
                const lat = (docY / MODE360.H - 0.5) * Math.PI;
                const sx = MODE360.poleCompensation ? Math.min(1 / Math.max(Math.cos(lat), 0.05), MODE360.W / 2 / r) : 1;
                cursorCtx360.ellipse(x, y, Math.max(1, r * sx * z), Math.max(1, r * z), 0, 0, Math.PI * 2);
            } else {
                // En vista esfera
                cursorCtx360.arc(x, y, Math.max(1, r), 0, Math.PI * 2);
            }
            cursorCtx360.stroke();

            // Borde exterior oscuro para contraste sobre cualquier fondo
            cursorCtx360.strokeStyle = 'rgba(0,0,0,0.35)';
            cursorCtx360.lineWidth = 0.5;
            cursorCtx360.stroke();
            cursorCtx360.restore();
        }
    }

    // 2. Icono clásico del puntero (CURSOR.png)
    if (typeof customCursorImg !== 'undefined' && customCursorImg && (customCursorImg.complete || customCursorImg.naturalWidth > 0)) {
        cursorCtx360.drawImage(customCursorImg, x, y);
    }
}
window._draw360Cursor = _draw360Cursor;

// ─────────────────────────────────────────────────────────────
//  RENDER MAPA PLANO (OPTIMIZADO CON FAST BLIT)
// ─────────────────────────────────────────────────────────────
function _request360Render() {
    if (!MODE360.renderPending) {
        MODE360.renderPending = true;
        requestAnimationFrame(_render360Map);
    }
}

function _render360Map() {
    MODE360.renderPending = false;
    if (!mapCanvas360 || !mapCtx360) return;

    const W = MODE360.W, H = MODE360.H;
    const cw = mapCanvas360.width, ch = mapCanvas360.height;
    const cam = MODE360.cam;
    cam.x = ((cam.x % W) + W) % W;
    const z = cam.z, ox = -cam.x * z, oy = -cam.y * z;

    mapCtx360.fillStyle = '#0d0d14';
    mapCtx360.fillRect(0, 0, cw, ch);

    // Suavizado rápido durante paneo/zoom
    const isInteracting = !!(MODE360.mapPan || (MODE360.mapPts && MODE360.mapPts.size > 1));
    mapCtx360.imageSmoothingEnabled = !isInteracting && (z > 0.5);
    if (!isInteracting) {
        mapCtx360.imageSmoothingQuality = 'low';
    }

    // Calcular únicamente repeticiones horizontales visibles
    const startK = Math.max(-1, Math.floor(-ox / (W * z)));
    const endK   = Math.min(3, Math.ceil((cw - ox) / (W * z)));

    const bgCol = (typeof bgMode !== 'undefined' && bgMode === 1 && typeof solidBgColor !== 'undefined') ? solidBgColor : '#1a1a24';

    for (let k = startK; k <= endK; k++) {
        const dx = ox + k * W * z;
        if (dx + W * z < 0 || dx > cw) continue;

        // Fondo del lienzo
        mapCtx360.fillStyle = bgCol;
        mapCtx360.fillRect(dx, oy, W * z, H * z);

        // Capas
        _composit360ToCtx(mapCtx360, dx, oy, W * z, H * z);

        // Guías de cuadrícula equirectangular
        if (MODE360.showGuides) {
            mapCtx360.save();
            mapCtx360.strokeStyle = 'rgba(108,99,255,.35)';
            mapCtx360.fillStyle   = 'rgba(160,140,255,.6)';
            mapCtx360.lineWidth   = 1;
            mapCtx360.font        = `${Math.max(9, Math.round(11 * z))}px Outfit,sans-serif`;
            mapCtx360.setLineDash([4, 6]);
            for (let i = 0; i <= 4; i++) {
                const gx = dx + i * (W / 4) * z;
                mapCtx360.beginPath(); mapCtx360.moveTo(gx, oy); mapCtx360.lineTo(gx, oy + H * z); mapCtx360.stroke();
                if (i < 4) mapCtx360.fillText(i * 90 + '°', gx + 3, oy + Math.max(12, 13 * z));
            }
            mapCtx360.beginPath(); mapCtx360.moveTo(dx, oy + H / 2 * z); mapCtx360.lineTo(dx + W * z, oy + H / 2 * z); mapCtx360.stroke();
            mapCtx360.setLineDash([]);
            mapCtx360.restore();
        }
    }

    // Borde delimitador del lienzo principal
    mapCtx360.strokeStyle = 'rgba(108,99,255,.5)';
    mapCtx360.lineWidth = 1.5;
    mapCtx360.strokeRect(ox, oy, W * z, H * z);
}

function _composit360ToCtx(ctx, dx, dy, dw, dh) {
    for (const l of layers360) {
        if (!l.visible) continue;
        ctx.save();
        ctx.globalAlpha = l.opacity;
        ctx.globalCompositeOperation = l.blendMode;
        ctx.drawImage(l.canvas, dx, dy, dw, dh);
        ctx.restore();
    }
}

// ─────────────────────────────────────────────────────────────
//  RENDER ESFERA 3D (WEBGL GPU SHADER — CERO LAG A 60-144 FPS)
// ─────────────────────────────────────────────────────────────
function _request360PvRender() {
    if (!MODE360.pvRenderPending) {
        MODE360.pvRenderPending = true;
        requestAnimationFrame(_render360Sphere);
    }
}

function _render360Sphere() {
    MODE360.pvRenderPending = false;
    if (!MODE360.gl) {
        if (!_init360GL()) return;
    }
    const gl = MODE360.gl;
    const w = MODE360.pvCanvas.width;
    const h = MODE360.pvCanvas.height;
    if (w <= 0 || h <= 0) return;

    // Subir textura a la GPU únicamente si las capas se modificaron
    if (MODE360.srcStale) {
        let srcCv;
        if (layers360.length === 1 && layers360[0].visible && layers360[0].opacity === 1.0 && layers360[0].blendMode === 'source-over') {
            srcCv = layers360[0].canvas;
        } else {
            if (!MODE360.artCtx) {
                MODE360.artCanvas = document.createElement('canvas');
                MODE360.artCanvas.width  = MODE360.W;
                MODE360.artCanvas.height = MODE360.H;
                MODE360.artCtx = MODE360.artCanvas.getContext('2d', { willReadFrequently: true });
            }
            MODE360.artCtx.clearRect(0, 0, MODE360.W, MODE360.H);
            _composit360ToCtx(MODE360.artCtx, 0, 0, MODE360.W, MODE360.H);
            srcCv = MODE360.artCanvas;
        }

        gl.bindTexture(gl.TEXTURE_2D, MODE360.glTex);
        gl.pixelStorei(gl.UNPACK_FLIP_Y_WEBGL, false);
        gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, gl.RGBA, gl.UNSIGNED_BYTE, srcCv);
        MODE360.srcStale = false;
    }

    // Color de fondo
    let br = 0.05, bg2 = 0.05, bb = 0.08;
    if (typeof bgMode !== 'undefined' && bgMode === 1 && typeof solidBgColor !== 'undefined') {
        const hc = solidBgColor.replace('#', '');
        br  = (parseInt(hc.slice(0, 2), 16) || 0) / 255;
        bg2 = (parseInt(hc.slice(2, 4), 16) || 0) / 255;
        bb  = (parseInt(hc.slice(4, 6), 16) || 0) / 255;
    }

    gl.viewport(0, 0, w, h);
    gl.useProgram(MODE360.glProg);

    gl.uniform2f(MODE360.glUniforms.res, w, h);
    gl.uniform1f(MODE360.glUniforms.yaw, MODE360.yaw);
    gl.uniform1f(MODE360.glUniforms.pitch, MODE360.pitch);
    gl.uniform1f(MODE360.glUniforms.fov, MODE360.fov);
    gl.uniform3f(MODE360.glUniforms.bgCol, br, bg2, bb);

    gl.activeTexture(gl.TEXTURE0);
    gl.bindTexture(gl.TEXTURE_2D, MODE360.glTex);
    gl.uniform1i(MODE360.glUniforms.tex, 0);

    gl.drawArrays(gl.TRIANGLES, 0, 6);
}

// ─────────────────────────────────────────────────────────────
//  DIBUJO
// ─────────────────────────────────────────────────────────────
function _360BrushSize() { return (typeof baseBrushSize !== 'undefined' ? baseBrushSize : 12); }
function _360Opacity()   { return (typeof brushOpacity   !== 'undefined' ? brushOpacity   : 1.0); }

function _360IsEraser() {
    return !!(typeof currentBrush !== 'undefined' && currentBrush && currentBrush.isEraser);
}
function _360InvalidateEraserCache() {}

// BATCH BRUSH: trazos continuos infinitos con cálculo de camino más corto y wrap toroidal
function _360Seg(p0, p1) {
    const l = layers360[selectedLayerIndex360];
    if (!l) return;
    const W = MODE360.W, H = MODE360.H;
    const r = _360BrushSize() / 2;
    if (r <= 0) return;

    // Normalizar inicio a coordenadas canónicas [0, W)
    const x0 = ((p0[0] % W) + W) % W;
    const y0 = Math.max(0, Math.min(H, p0[1]));

    // Distancia horizontal más corta en la esfera (camino más corto sin saltos ni límites de giros)
    let dx = p1[0] - p0[0];
    dx = dx - Math.round(dx / W) * W;

    const y1 = Math.max(0, Math.min(H, p1[1]));
    const dy = y1 - y0;

    const dist = Math.hypot(dx, dy);
    const step = Math.max(1.5, r * 0.3);
    const n    = Math.max(1, Math.ceil(dist / step));

    const isEraser = _360IsEraser();
    const color    = (typeof selectedColor !== 'undefined') ? selectedColor : '#000';
    const opacity  = _360Opacity();
    const poleComp = MODE360.poleCompensation;
    const MAX_SX   = W / 2 / r;

    l.ctx.save();
    l.ctx.globalCompositeOperation = isEraser ? 'destination-out' : 'source-over';
    l.ctx.globalAlpha = opacity;
    l.ctx.fillStyle   = color;

    l.ctx.beginPath();
    for (let i = 0; i <= n; i++) {
        const t = i / n;
        const rawX = x0 + dx * t;
        const y    = y0 + dy * t;

        // Proyección al lienzo equirectangular [0, W)
        const canX = ((rawX % W) + W) % W;

        const lat = (y / H - 0.5) * Math.PI;
        const sx  = poleComp ? Math.min(1 / Math.max(Math.cos(lat), 0.05), MAX_SX) : 1;
        const rx  = r * sx;

        // 1. Estampado principal
        l.ctx.moveTo(canX + rx, y);
        l.ctx.ellipse(canX, y, rx, r, 0, 0, Math.PI * 2);

        // 2. Wrap si cruza el extremo izquierdo
        if (canX - rx < 0) {
            l.ctx.moveTo(canX + W + rx, y);
            l.ctx.ellipse(canX + W, y, rx, r, 0, 0, Math.PI * 2);
        }
        // 3. Wrap si cruza el extremo derecho
        if (canX + rx > W) {
            l.ctx.moveTo(canX - W + rx, y);
            l.ctx.ellipse(canX - W, y, rx, r, 0, 0, Math.PI * 2);
        }
    }
    l.ctx.fill();
    l.ctx.restore();

    MODE360.srcStale = true;
    hasUnsavedChanges = true;
}

function _360MapCoord(sx, sy) {
    return [MODE360.cam.x + sx / MODE360.cam.z, MODE360.cam.y + sy / MODE360.cam.z];
}

// ─────────────────────────────────────────────────────────────
//  HISTORIAL (UNDO / REDO) Y BUFFER TEMPORAL PARA MODO 360°
// ─────────────────────────────────────────────────────────────
let _360PreStrokeCanvas = null;

function _360SavePreStroke() {
    const l = layers360[selectedLayerIndex360];
    if (!l) return;
    if (!_360PreStrokeCanvas) {
        _360PreStrokeCanvas = document.createElement('canvas');
        _360PreStrokeCanvas.width = MODE360.W;
        _360PreStrokeCanvas.height = MODE360.H;
    }
    const pctx = _360PreStrokeCanvas.getContext('2d');
    pctx.clearRect(0, 0, MODE360.W, MODE360.H);
    pctx.drawImage(l.canvas, 0, 0);
}

function _360RevertToLastSnap() {
    const l = layers360[selectedLayerIndex360];
    if (!l || !_360PreStrokeCanvas) return;
    l.ctx.clearRect(0, 0, MODE360.W, MODE360.H);
    l.ctx.drawImage(_360PreStrokeCanvas, 0, 0);
}

function _360CaptureSnapshot() {
    // Snapshot ALL layers (canvas data + metadata) for full multi-layer undo
    return layers360.map(l => {
        const sc = document.createElement('canvas');
        sc.width = MODE360.W; sc.height = MODE360.H;
        sc.getContext('2d').drawImage(l.canvas, 0, 0);
        return {
            id: l.id,
            name: l.name,
            visible: l.visible,
            opacity: l.opacity,
            blendMode: l.blendMode,
            snap: sc
        };
    });
}

function _360PushHistory() {
    if (layers360.length === 0) return;

    // Truncar rama de rehacer (redo)
    if (MODE360.historyIndex < MODE360.history.length - 1) {
        MODE360.history.splice(MODE360.historyIndex + 1);
    }
    MODE360.history.push({
        layers: _360CaptureSnapshot(),
        selectedLayerIndex360
    });
    if (MODE360.history.length > MODE360.MAX_HISTORY) {
        MODE360.history.shift();
    }
    MODE360.historyIndex = MODE360.history.length - 1;
    hasUnsavedChanges = true;
}

function _360Snap() {
    _360PushHistory();
}

function _360RestoreSnapshot(state) {
    if (!state || !state.layers) return;
    // Rebuild layers360 from snapshot
    layers360 = state.layers.map(sl => {
        const cv = document.createElement('canvas');
        cv.width = MODE360.W; cv.height = MODE360.H;
        const lctx = cv.getContext('2d', { willReadFrequently: true });
        lctx.drawImage(sl.snap, 0, 0);
        return {
            id: sl.id,
            name: sl.name,
            visible: sl.visible,
            opacity: sl.opacity,
            blendMode: sl.blendMode,
            canvas: cv,
            ctx: lctx
        };
    });
    selectedLayerIndex360 = Math.max(0, Math.min(state.selectedLayerIndex360, layers360.length - 1));
    MODE360.srcStale = true;
    _360UpdateLayersUI();
    _request360Render();
    if (_cur360View === 'sphere') _request360PvRender();
    hasUnsavedChanges = true;
}

function _360Undo() {
    if (MODE360.historyIndex <= 0) return;
    MODE360.historyIndex--;
    _360RestoreSnapshot(MODE360.history[MODE360.historyIndex]);
}

function _360Redo() {
    if (MODE360.historyIndex >= MODE360.history.length - 1) return;
    MODE360.historyIndex++;
    _360RestoreSnapshot(MODE360.history[MODE360.historyIndex]);
}

// ─────────────────────────────────────────────────────────────
//  SISTEMA DE ESTABILIZADORES (VIVO Y POST) PARA MODO 360°
// ─────────────────────────────────────────────────────────────
let _360StabQueue = [];
let _360LastRawX = 0;
let _360LastUnwrappedX = 0;
let _360RawStroke = [];
let _360PostUnwrappedX = 0;
let _360PostLastRawX = 0;

function _360StartStroke(pt) {
    _360SavePreStroke();
    MODE360.isDrawing = true;
    MODE360.lastPt = pt;

    const sEnabled = (typeof stabEnabled !== 'undefined' ? stabEnabled : 0);
    const sMode    = (typeof stabMode    !== 'undefined' ? stabMode    : 'post');

    if (sEnabled > 0 && sMode === 'realtime') {
        _360StabQueue = [{ x: pt[0], y: pt[1], ux: pt[0] }];
        _360LastRawX = pt[0];
        _360LastUnwrappedX = pt[0];
        _360Seg(pt, pt);
    } else if (sEnabled > 0 && sMode === 'post') {
        _360RawStroke = [{ x: pt[0], y: pt[1], ux: pt[0] }];
        _360PostLastRawX = pt[0];
        _360PostUnwrappedX = pt[0];
        _360Seg(pt, pt);
    } else {
        _360Seg(pt, pt);
    }
}

function _360MoveStroke(c) {
    if (!MODE360.isDrawing || !MODE360.lastPt) return;

    const sEnabled = (typeof stabEnabled !== 'undefined' ? stabEnabled : 0);
    const sMode    = (typeof stabMode    !== 'undefined' ? stabMode    : 'post');

    if (sEnabled > 0 && sMode === 'realtime') {
        const W = MODE360.W;
        let dx = c[0] - _360LastRawX;
        dx = dx - Math.round(dx / W) * W;
        _360LastUnwrappedX += dx;
        _360LastRawX = c[0];

        _360StabQueue.push({ x: c[0], y: c[1], ux: _360LastUnwrappedX });

        const windowSize = Math.max(2, Math.round(sEnabled * 1.5));
        if (_360StabQueue.length >= windowSize) {
            const out = _360StabQueue.shift();
            let sumUX = out.ux;
            let sumY  = out.y;
            for (let i = 0; i < _360StabQueue.length; i++) {
                sumUX += _360StabQueue[i].ux;
                sumY  += _360StabQueue[i].y;
            }
            const n = _360StabQueue.length + 1;
            const avgUX = sumUX / n;
            const avgY  = sumY / n;

            const blend = Math.min(0.85, (sEnabled / 15) * 0.7 + 0.15);
            const finalUX = out.ux * (1 - blend) + avgUX * blend;
            const finalY  = out.y  * (1 - blend) + avgY  * blend;
            const canX = ((finalUX % W) + W) % W;
            const nextPt = [canX, finalY];

            _360Seg(MODE360.lastPt, nextPt);
            MODE360.lastPt = nextPt;
        }
    } else if (sEnabled > 0 && sMode === 'post') {
        const W = MODE360.W;
        let dx = c[0] - _360PostLastRawX;
        dx = dx - Math.round(dx / W) * W;
        _360PostUnwrappedX += dx;
        _360PostLastRawX = c[0];
        _360RawStroke.push({ x: c[0], y: c[1], ux: _360PostUnwrappedX });

        _360Seg(MODE360.lastPt, c);
        MODE360.lastPt = c;
    } else {
        _360Seg(MODE360.lastPt, c);
        MODE360.lastPt = c;
    }
}

function _360EndStroke(updateFn) {
    if (!MODE360.isDrawing) return;

    const sEnabled = (typeof stabEnabled !== 'undefined' ? stabEnabled : 0);
    const sMode    = (typeof stabMode    !== 'undefined' ? stabMode    : 'post');

    if (sEnabled > 0 && sMode === 'realtime') {
        const W = MODE360.W;
        while (_360StabQueue.length > 0) {
            const p = _360StabQueue.shift();
            const canX = ((p.ux % W) + W) % W;
            const nextPt = [canX, p.y];
            _360Seg(MODE360.lastPt, nextPt);
            MODE360.lastPt = nextPt;
        }
        _360StabQueue = [];
    } else if (sEnabled > 0 && sMode === 'post' && _360RawStroke.length > 2) {
        _360RevertToLastSnap();
        const passes = Math.round(sEnabled * 2);
        const smoothed = _360SmoothStroke(_360RawStroke, passes);
        if (smoothed && smoothed.length > 1) {
            _360Seg(smoothed[0], smoothed[0]);
            for (let i = 1; i < smoothed.length; i++) {
                _360Seg(smoothed[i - 1], smoothed[i]);
            }
        }
        _360RawStroke = [];
        MODE360.srcStale = true;
    }

    MODE360.isDrawing = false;
    MODE360.lastPt = null;
    _360PushHistory();
    if (typeof updateFn === 'function') updateFn();
}

function _360SmoothStroke(rawPts, passes) {
    if (!rawPts || rawPts.length <= 2) {
        return (rawPts || []).map(p => [((p.ux % MODE360.W) + MODE360.W) % MODE360.W, p.y]);
    }

    const W = MODE360.W;
    const step = 6;
    const resampled = [{ ux: rawPts[0].ux, y: rawPts[0].y }];
    let prev = rawPts[0];
    let acc = 0;

    for (let i = 1; i < rawPts.length; i++) {
        const curr = rawPts[i];
        let d = Math.hypot(curr.ux - prev.ux, curr.y - prev.y);
        while (d > 0 && acc + d >= step) {
            const t = (step - acc) / d;
            const nx = prev.ux + (curr.ux - prev.ux) * t;
            const ny = prev.y  + (curr.y  - prev.y)  * t;
            resampled.push({ ux: nx, y: ny });
            prev = { ux: nx, y: ny };
            d = Math.hypot(curr.ux - prev.ux, curr.y - prev.y);
            acc = 0;
        }
        acc += d;
        prev = curr;
    }
    resampled.push({ ux: rawPts[rawPts.length - 1].ux, y: rawPts[rawPts.length - 1].y });
    if (resampled.length <= 2) {
        return rawPts.map(p => [((p.ux % W) + W) % W, p.y]);
    }

    let pts = resampled;
    const numPasses = Math.min(40, Math.max(1, passes));
    for (let iter = 0; iter < numPasses; iter++) {
        const next = [pts[0]];
        for (let i = 1; i < pts.length - 1; i++) {
            next.push({
                ux: pts[i - 1].ux * 0.25 + pts[i].ux * 0.5 + pts[i + 1].ux * 0.25,
                y:  pts[i - 1].y  * 0.25 + pts[i].y  * 0.5 + pts[i + 1].y  * 0.25
            });
        }
        next.push(pts[pts.length - 1]);
        pts = next;
    }

    return pts.map(p => [((p.ux % W) + W) % W, p.y]);
}

// ─────────────────────────────────────────────────────────────
//  SISTEMA DE LAZOS (RELLENO Y BORRADOR - LIBRE Y RECTANGULAR)
// ─────────────────────────────────────────────────────────────
let _360IsLassoActive = false;
let _360LassoAnchor = null;
let _360LassoEnd = null;
let _360LassoScreenAnchor = null;
let _360LassoScreenEnd = null;
let _360LassoPath = [];
let _360LassoScreenPath = [];

function _360StartLasso(mapPt, screenPt) {
    _360SavePreStroke();  // snapshot for undo
    _360IsLassoActive = true;
    _360LassoAnchor = { x: mapPt[0], y: mapPt[1] };
    _360LassoEnd = { x: mapPt[0], y: mapPt[1] };
    _360LassoScreenAnchor = { x: screenPt.x, y: screenPt.y };
    _360LassoScreenEnd = { x: screenPt.x, y: screenPt.y };
    _360LassoPath = [{ x: mapPt[0], y: mapPt[1] }];
    _360LassoScreenPath = [{ x: screenPt.x, y: screenPt.y }];
}

function _360MoveLasso(mapPt, screenPt) {
    if (!_360IsLassoActive) return;
    _360LassoEnd = { x: mapPt[0], y: mapPt[1] };
    _360LassoScreenEnd = { x: screenPt.x, y: screenPt.y };

    const mode = (typeof lassoFillMode !== 'undefined' ? lassoFillMode : 'libre');
    if (mode === 'libre') {
        const lastScr = _360LassoScreenPath[_360LassoScreenPath.length - 1];
        if (!lastScr || Math.hypot(screenPt.x - lastScr.x, screenPt.y - lastScr.y) >= 2) {
            _360LassoPath.push({ x: mapPt[0], y: mapPt[1] });
            _360LassoScreenPath.push({ x: screenPt.x, y: screenPt.y });
        }
    }
}

function _360EndLasso() {
    if (!_360IsLassoActive) return;
    _360ExecuteLasso();
    _360IsLassoActive = false;
    _360LassoAnchor = null;
    _360LassoEnd = null;
    _360LassoScreenAnchor = null;
    _360LassoScreenEnd = null;
    _360LassoPath = [];
    _360LassoScreenPath = [];
}

// Dispatcher — en vista esfera usa reproyección inversa (sin distorsión);
// en vista mapa usa el método equirectangular clásico.
function _360ExecuteLasso() {
    if (_cur360View === 'sphere') {
        _360ExecuteLassoSphere();
    } else {
        _360ExecuteLassoMap();
    }
}

// ── Vista MAPA: dibuja directamente en espacio equirectangular ──────────────
function _360ExecuteLassoMap() {
    const l = layers360[selectedLayerIndex360];
    if (!l) return;
    const isEraser = _360IsEraser();
    const mode = (typeof lassoFillMode !== 'undefined' ? lassoFillMode : 'libre');
    const W = MODE360.W, H = MODE360.H;
    const opacity = _360Opacity();
    const color = (typeof selectedColor !== 'undefined' && selectedColor) ? selectedColor : '#000000';

    l.ctx.save();
    if (isEraser) {
        l.ctx.globalCompositeOperation = 'destination-out';
    } else if (l.alphaLocked) {
        l.ctx.globalCompositeOperation = 'source-atop';
    } else {
        l.ctx.globalCompositeOperation = 'source-over';
    }
    l.ctx.globalAlpha = opacity;
    l.ctx.fillStyle = color;

    if (mode === 'rectangulo') {
        if (!_360LassoAnchor || !_360LassoEnd) { l.ctx.restore(); return; }
        const rx = Math.min(_360LassoAnchor.x, _360LassoEnd.x);
        const ry = Math.max(0, Math.min(H, Math.min(_360LassoAnchor.y, _360LassoEnd.y)));
        const rw = Math.abs(_360LassoEnd.x - _360LassoAnchor.x);
        const rh = Math.min(H - ry, Math.abs(_360LassoEnd.y - _360LassoAnchor.y));
        if (rw > 0 && rh > 0) {
            l.ctx.fillRect(rx, ry, rw, rh);
            if (rx + rw > W) l.ctx.fillRect(rx - W, ry, rw, rh);
            if (rx < 0)      l.ctx.fillRect(rx + W, ry, rw, rh);
        }
    } else {
        if (!_360LassoPath || _360LassoPath.length < 3) { l.ctx.restore(); return; }
        let lastRawX = _360LassoPath[0].x, unwrappedX = lastRawX;
        const unwrapped = [{ x: unwrappedX, y: _360LassoPath[0].y }];
        for (let i = 1; i < _360LassoPath.length; i++) {
            let dx = _360LassoPath[i].x - lastRawX;
            dx -= Math.round(dx / W) * W;
            unwrappedX += dx;
            lastRawX = _360LassoPath[i].x;
            unwrapped.push({ x: unwrappedX, y: _360LassoPath[i].y });
        }
        const pts = typeof smoothLassoPath === 'function' ? smoothLassoPath(unwrapped, 3) : unwrapped;
        if (pts.length < 3) { l.ctx.restore(); return; }
        let minUX = Infinity, maxUX = -Infinity;
        for (const p of pts) { if (p.x < minUX) minUX = p.x; if (p.x > maxUX) maxUX = p.x; }
        const baseShift = Math.floor(minUX / W) * W;
        const drawPolyAt = (shift) => {
            l.ctx.beginPath();
            l.ctx.moveTo(pts[0].x - shift, pts[0].y);
            for (let i = 1; i < pts.length; i++) l.ctx.lineTo(pts[i].x - shift, pts[i].y);
            l.ctx.closePath(); l.ctx.fill();
        };
        drawPolyAt(baseShift); drawPolyAt(baseShift + W); drawPolyAt(baseShift - W);
    }

    l.ctx.restore();
    MODE360.srcStale = true;
    _360PushHistory();
    _request360Render();
}

// ── Vista ESFERA: reproyección inversa pixel-perfect ─────────────────────────
// Para cada texel equirectangular en la región visible, lo proyecta a pantalla
// y comprueba si cae dentro del lazo dibujado. Resultado: forma exactamente
// como se ve en pantalla, sin distorsión ni problemas en los polos.
function _360ExecuteLassoSphere() {
    const l = layers360[selectedLayerIndex360];
    if (!l) return;
    const isEraser = _360IsEraser();
    const mode = (typeof lassoFillMode !== 'undefined' ? lassoFillMode : 'libre');
    const W = MODE360.W, H = MODE360.H;
    const opacity = _360Opacity();
    const color = (typeof selectedColor !== 'undefined' && selectedColor) ? selectedColor : '#000000';

    const cv = MODE360.pvCanvas;
    if (!cv) return;
    const rect = cv.getBoundingClientRect();
    const pvW = cv.width || rect.width;
    const pvH = cv.height || rect.height;
    if (pvW <= 0 || pvH <= 0) return;

    const scaleX = (rect.width > 0 ? pvW / rect.width : 1);
    const scaleY = (rect.height > 0 ? pvH / rect.height : 1);

    // ── 1. Bounding box y dibujo de máscara en espacio de pantalla ───────────
    let minPX = 0, maxPX = pvW - 1, minPY = 0, maxPY = pvH - 1;
    let rx = 0, ry = 0, rw = 0, rh = 0;
    let smoothScreenPath = null;

    if (mode === 'rectangulo') {
        if (!_360LassoScreenAnchor || !_360LassoScreenEnd) return;
        rx = Math.min(_360LassoScreenAnchor.x, _360LassoScreenEnd.x) * scaleX;
        ry = Math.min(_360LassoScreenAnchor.y, _360LassoScreenEnd.y) * scaleY;
        rw = Math.abs(_360LassoScreenEnd.x - _360LassoScreenAnchor.x) * scaleX;
        rh = Math.abs(_360LassoScreenEnd.y - _360LassoScreenAnchor.y) * scaleY;
        if (rw < 1 || rh < 1) return;

        minPX = Math.max(0, Math.floor(rx) - 1);
        maxPX = Math.min(pvW - 1, Math.ceil(rx + rw) + 1);
        minPY = Math.max(0, Math.floor(ry) - 1);
        maxPY = Math.min(pvH - 1, Math.ceil(ry + rh) + 1);
    } else {
        if (!_360LassoScreenPath || _360LassoScreenPath.length < 3) return;
        const scaledPath = _360LassoScreenPath.map(p => ({ x: p.x * scaleX, y: p.y * scaleY }));
        const sEnabled = (typeof stabEnabled !== 'undefined' ? stabEnabled : 0);
        const fovFactor = Math.max(1, (MODE360.fov || 1.0) / 1.0);
        const passes = Math.round(Math.min(24, Math.max(4, 5 * fovFactor + sEnabled * 3)));
        smoothScreenPath = _360SmoothScreenLasso(scaledPath, passes);
        if (!smoothScreenPath || smoothScreenPath.length < 3) return;

        let sminX = Infinity, smaxX = -Infinity, sminY = Infinity, smaxY = -Infinity;
        for (let i = 0; i < smoothScreenPath.length; i++) {
            const p = smoothScreenPath[i];
            if (p.x < sminX) sminX = p.x;
            if (p.x > smaxX) smaxX = p.x;
            if (p.y < sminY) sminY = p.y;
            if (p.y > smaxY) smaxY = p.y;
        }
        minPX = Math.max(0, Math.floor(sminX) - 2);
        maxPX = Math.min(pvW - 1, Math.ceil(smaxX) + 2);
        minPY = Math.max(0, Math.floor(sminY) - 2);
        maxPY = Math.min(pvH - 1, Math.ceil(smaxY) + 2);
    }

    if (minPX > maxPX || minPY > maxPY) return;

    // Renderizar máscara con suavizado Bézier y anti-aliasing
    const maskCv = document.createElement('canvas');
    maskCv.width = pvW;
    maskCv.height = pvH;
    const mctx = maskCv.getContext('2d');
    mctx.fillStyle = '#fff';
    mctx.imageSmoothingEnabled = true;

    if (mode === 'rectangulo') {
        mctx.fillRect(rx, ry, rw, rh);
    } else {
        _360DrawSmoothPolygon(mctx, smoothScreenPath);
        mctx.fill();
    }

    const maskRaw = mctx.getImageData(0, 0, pvW, pvH).data;
    // Máscara de cobertura subpíxel con anti-aliasing (0 a 255)
    const maskCov = new Uint8Array(pvW * pvH);
    for (let py = minPY; py <= maxPY; py++) {
        const row = py * pvW;
        for (let px = minPX; px <= maxPX; px++) {
            maskCov[row + px] = maskRaw[(row + px) * 4];
        }
    }

    // ── 2. Parámetros de la cámara ──────────────────────────────────────────
    const tf  = Math.tan(MODE360.fov / 2);
    const asp = pvW / pvH;
    const cp  = Math.cos(MODE360.pitch);
    const sp  = Math.sin(MODE360.pitch);
    const yaw = MODE360.yaw;

    // ── 3. Rango de latitud visible para el lazo (incluyendo polos) ─────────
    let minLat = 999, maxLat = -999;
    const sampleLatAt = (px, py) => {
        const nx = ((px / pvW) * 2 - 1) * tf * asp;
        const ny = (1 - (py / pvH) * 2) * tf;
        const y2 = ny * cp + sp;
        const z2 = -ny * sp + cp;
        const len = Math.hypot(nx, y2, z2);
        return Math.asin(Math.max(-1, Math.min(1, y2 / Math.max(0.0001, len))));
    };

    // Muestreo del contorno y grilla del bounding box
    const gridN = 16;
    for (let i = 0; i <= gridN; i++) {
        const px = minPX + (maxPX - minPX) * (i / gridN);
        for (let j = 0; j <= gridN; j++) {
            const py = minPY + (maxPY - minPY) * (j / gridN);
            const lat = sampleLatAt(px, py);
            if (lat < minLat) minLat = lat;
            if (lat > maxLat) maxLat = lat;
        }
    }

    // Comprobación analítica si el Polo Norte está dentro del bbox de pantalla
    if (sp > 0.001) {
        const np_ny = cp / sp;
        const np_px = 0.5 * pvW;
        const np_py = (1 - np_ny / tf) * 0.5 * pvH;
        if (np_px >= minPX && np_px <= maxPX && np_py >= minPY && np_py <= maxPY) {
            maxLat = Math.PI / 2;
        }
    }

    // Comprobación analítica si el Polo Sur está dentro del bbox de pantalla
    if (sp < -0.001) {
        const sp_ny = cp / sp;
        const sp_px = 0.5 * pvW;
        const sp_py = (1 - sp_ny / tf) * 0.5 * pvH;
        if (sp_px >= minPX && sp_px <= maxPX && sp_py >= minPY && sp_py <= maxPY) {
            minLat = -Math.PI / 2;
        }
    }

    // Margen de seguridad de latitud para no recortar bordes
    const pad = 0.12;
    minLat = Math.max(-Math.PI / 2, minLat - pad);
    maxLat = Math.min( Math.PI / 2, maxLat + pad);

    const eyMin = Math.max(0,     Math.floor((0.5 - maxLat / Math.PI) * H));
    const eyMax = Math.min(H - 1, Math.ceil ((0.5 - minLat / Math.PI) * H));
    const rowCount = eyMax - eyMin + 1;
    if (rowCount <= 0) return;

    // ── 4. Precomputar tablas trigonométricas (0 llamadas trig en el loop) ──
    const preCosLon = new Float32Array(W);
    const preSinLon = new Float32Array(W);
    const twoPI = 2 * Math.PI;
    for (let ex = 0; ex < W; ex++) {
        const lon = (ex / W - 0.5) * twoPI;
        const diff = lon - yaw;
        preCosLon[ex] = Math.cos(diff);
        preSinLon[ex] = Math.sin(diff);
    }

    const preCosLat = new Float32Array(rowCount);
    const preSinLat = new Float32Array(rowCount);
    for (let i = 0; i < rowCount; i++) {
        const lat = (0.5 - (eyMin + i) / H) * Math.PI;
        preCosLat[i] = Math.cos(lat);
        preSinLat[i] = Math.sin(lat);
    }

    // ── 5. Parsear color de dibujo / borrador ──────────────────────────────
    let cr = 0, cg = 0, cb = 0, ca = 255;
    if (!isEraser) {
        const tmpCv = document.createElement('canvas');
        tmpCv.width = tmpCv.height = 1;
        const tc = tmpCv.getContext('2d');
        tc.fillStyle = color;
        tc.fillRect(0, 0, 1, 1);
        const cd = tc.getImageData(0, 0, 1, 1).data;
        cr = cd[0]; cg = cd[1]; cb = cd[2]; ca = cd[3];
    }
    const srcA = (ca / 255) * opacity;
    const fastOpaque = (!isEraser && srcA >= 0.999 && !l.alphaLocked) || (isEraser && srcA >= 0.999);

    // ── 6. Cargar datos de la capa y mapear píxeles con anti-aliasing ──────
    const layerData = l.ctx.getImageData(0, eyMin, W, rowCount);
    const ld = layerData.data;

    const invTfAsp = 1.0 / (tf * asp);
    const invTf    = 1.0 / tf;
    const halfPvW  = 0.5 * pvW;
    const halfPvH  = 0.5 * pvH;

    let modified = false;

    for (let i = 0; i < rowCount; i++) {
        const cLat = preCosLat[i];
        const sLat = preSinLat[i];
        const sLat_cp = sLat * cp;
        const sLat_sp = sLat * sp;
        const rowOffset = i * W;

        for (let ex = 0; ex < W; ex++) {
            const cLon = preCosLon[ex];
            const sLon = preSinLon[ex];

            // Dirección unitaria 3D en la esfera
            const d3x = cLat * sLon;
            const d3z = cLat * cLon;

            // Coordenada Z en espacio de cámara tras rotación de pitch
            const dz2 = sLat_sp + d3z * cp;
            if (dz2 <= 0.001) continue; // Descartar hemisferio trasero

            const dy2 = sLat_cp - d3z * sp;

            // Proyección perspectiva a pantalla (exacta a WebGL)
            const invDz2 = 1.0 / dz2;
            const px = ((d3x * invDz2 * invTfAsp + 1.0) * halfPvW) | 0;
            if (px < minPX || px > maxPX) continue;

            const py = ((1.0 - dy2 * invDz2 * invTf) * halfPvH) | 0;
            if (py < minPY || py > maxPY) continue;

            // Cobertura subpíxel del lazo (0..255)
            const covByte = maskCov[py * pvW + px];
            if (covByte === 0) continue;

            modified = true;
            const ei = (rowOffset + ex) * 4;

            // Píxel completamente opaco en el interior
            if (fastOpaque && covByte === 255) {
                if (isEraser) {
                    ld[ei + 3] = 0;
                } else {
                    ld[ei]     = cr;
                    ld[ei + 1] = cg;
                    ld[ei + 2] = cb;
                    ld[ei + 3] = 255;
                }
            } else {
                // Mezcla anti-aliased suave en bordes (elimina dientes y escalonamiento)
                const effectiveSrcA = srcA * (covByte / 255.0);
                if (isEraser) {
                    const prevA = ld[ei + 3];
                    ld[ei + 3] = Math.max(0, prevA - Math.round(effectiveSrcA * prevA)) | 0;
                } else if (l.alphaLocked) {
                    const dstA = ld[ei + 3];
                    if (dstA > 0) {
                        ld[ei]     = Math.round(cr * effectiveSrcA + ld[ei]     * (1 - effectiveSrcA));
                        ld[ei + 1] = Math.round(cg * effectiveSrcA + ld[ei + 1] * (1 - effectiveSrcA));
                        ld[ei + 2] = Math.round(cb * effectiveSrcA + ld[ei + 2] * (1 - effectiveSrcA));
                    }
                } else {
                    const dstA = ld[ei + 3] / 255;
                    const outA = effectiveSrcA + dstA * (1 - effectiveSrcA);
                    if (outA > 0) {
                        ld[ei]     = Math.round((cr * effectiveSrcA + ld[ei]     * dstA * (1 - effectiveSrcA)) / outA);
                        ld[ei + 1] = Math.round((cg * effectiveSrcA + ld[ei + 1] * dstA * (1 - effectiveSrcA)) / outA);
                        ld[ei + 2] = Math.round((cb * effectiveSrcA + ld[ei + 2] * dstA * (1 - effectiveSrcA)) / outA);
                        ld[ei + 3] = Math.round(outA * 255);
                    }
                }
            }
        }
    }

    // ── 7. Aplicar al lienzo y actualizar visor ────────────────────────────
    if (modified) {
        l.ctx.putImageData(layerData, 0, eyMin);
        MODE360.srcStale = true;
        _360PushHistory();
        _request360PvRender();
    }
}

function _sync360LassoUI() {
    const btn = document.getElementById('btn360-lasso-mode');
    if (!btn) return;
    const isLasso = !!(typeof currentBrush !== 'undefined' && currentBrush && currentBrush.isLasso);
    btn.style.display = isLasso ? 'inline-block' : 'none';
    const mode = (typeof lassoFillMode !== 'undefined' ? lassoFillMode : 'libre');
    btn.textContent = (mode === 'rectangulo' ? '📐 Lazo: Rectángulo' : '📐 Lazo: Libre');
    if (mode === 'rectangulo') btn.classList.add('a360'); else btn.classList.remove('a360');
}
window._sync360LassoUI = _sync360LassoUI;

// ─────────────────────────────────────────────────────────────
//  EVENTOS DEL MAPA PLANO
// ─────────────────────────────────────────────────────────────
function _bindMapEvents() {
    const cv = mapCanvas360;
    cv.addEventListener('contextmenu', e => e.preventDefault());

    cv.addEventListener('pointermove', e => {
        const r = cv.getBoundingClientRect();
        const sx = e.clientX - r.left, sy = e.clientY - r.top;
        MODE360.cursorPos = { x: sx, y: sy };
        if (typeof currentTool !== 'undefined' && currentTool === 'eyedropper') {
            const mapPt = _360MapCoord(sx, sy);
            _update360EyedropperPreview(sx, sy, mapPt);
        }
        _draw360Cursor();
    });
    cv.addEventListener('pointerleave', () => {
        MODE360.cursorPos = null;
        if (typeof currentTool !== 'undefined' && currentTool === 'eyedropper' && eyedropperPreview && !eyedropperPreview.classList.contains('copied')) {
            eyedropperPreview.classList.add('hidden');
        }
        _draw360Cursor();
    });

    cv.addEventListener('pointerdown', e => {
        cv.setPointerCapture(e.pointerId);
        const r  = cv.getBoundingClientRect();
        const sx = e.clientX - r.left, sy = e.clientY - r.top;
        MODE360.mapPts.set(e.pointerId, { x: sx, y: sy });
        MODE360.cursorPos = { x: sx, y: sy };

        if (MODE360.mapPts.size === 2) {
            MODE360.mapPan = null;
            MODE360.mapPinch = _mapPinch360();
            _draw360Cursor();
            return;
        }
        const isPan = e.button === 2 || e.button === 1 || (typeof isSpacePressed !== 'undefined' && isSpacePressed);
        if (isPan) {
            MODE360.mapPan = { sx, sy, cx: MODE360.cam.x, cy: MODE360.cam.y };
            cv.style.cursor = 'grabbing';
            _draw360Cursor();
            return;
        }

        if (typeof currentTool !== 'undefined' && currentTool === 'eyedropper') {
            if (eyedropperFadeTimeout) { clearTimeout(eyedropperFadeTimeout); eyedropperFadeTimeout = null; }
            if (eyedropperPreview) eyedropperPreview.classList.remove('hidden', 'copied');
            const mapPt = _360MapCoord(sx, sy);
            _update360EyedropperPreview(sx, sy, mapPt);
            _draw360Cursor();
            return;
        }

        if (currentBrush && currentBrush.isLasso) {
            _360StartLasso(_360MapCoord(sx, sy), { x: sx, y: sy });
        } else {
            _360StartStroke(_360MapCoord(sx, sy));
        }
        _request360Render();
        _draw360Cursor();
    });

    cv.addEventListener('pointermove', e => {
        const r  = cv.getBoundingClientRect();
        const sx = e.clientX - r.left, sy = e.clientY - r.top;
        if (MODE360.mapPts.has(e.pointerId)) MODE360.mapPts.set(e.pointerId, { x: sx, y: sy });
        MODE360.cursorPos = { x: sx, y: sy };

        if (MODE360.mapPinch && MODE360.mapPts.size === 2) {
            const n  = _mapPinch360();
            const bx = MODE360.cam.x + MODE360.mapPinch.mx / MODE360.cam.z;
            const by = MODE360.cam.y + MODE360.mapPinch.my / MODE360.cam.z;
            MODE360.cam.z = Math.min(20, Math.max(.05, MODE360.cam.z * n.d / MODE360.mapPinch.d));
            MODE360.cam.x = bx - n.mx / MODE360.cam.z;
            MODE360.cam.y = by - n.my / MODE360.cam.z;
            _clamp360Y();
            MODE360.mapPinch = n;
            _request360Render();
            _draw360Cursor();
            return;
        }
        if (MODE360.mapPan) {
            MODE360.cam.x = MODE360.mapPan.cx - (sx - MODE360.mapPan.sx) / MODE360.cam.z;
            MODE360.cam.y = MODE360.mapPan.cy - (sy - MODE360.mapPan.sy) / MODE360.cam.z;
            _clamp360Y();
            _request360Render();
            _draw360Cursor();
            return;
        }

        if (typeof currentTool !== 'undefined' && currentTool === 'eyedropper') {
            const mapPt = _360MapCoord(sx, sy);
            _update360EyedropperPreview(sx, sy, mapPt);
            _draw360Cursor();
            return;
        }

        if (_360IsLassoActive) {
            _360MoveLasso(_360MapCoord(sx, sy), { x: sx, y: sy });
            _draw360Cursor();
        } else if (MODE360.isDrawing && MODE360.lastPt) {
            const evts = e.getCoalescedEvents ? e.getCoalescedEvents() : [e];
            const er = r;
            for (const ev of evts) {
                const c = _360MapCoord(ev.clientX - er.left, ev.clientY - er.top);
                _360MoveStroke(c);
            }
            _request360Render();
        }
        _draw360Cursor();
    });

    const mapUp = e => {
        MODE360.mapPts.delete(e.pointerId);
        if (MODE360.mapPts.size < 2) MODE360.mapPinch = null;
        if (MODE360.mapPts.size === 0) {
            const r = cv.getBoundingClientRect();
            if (typeof currentTool !== 'undefined' && currentTool === 'eyedropper') {
                const mapPt = _360MapCoord(e.clientX - r.left, e.clientY - r.top);
                _apply360Eyedropper(mapPt);
                MODE360.mapPan = null;
                cv.style.cursor = 'none';
                _draw360Cursor();
                return;
            }
            if (_360IsLassoActive) {
                _360EndLasso();
                _request360Render();
            } else {
                _360EndStroke(() => _request360Render());
            }
            MODE360.mapPan = null;
            cv.style.cursor = 'none';
        }
        _draw360Cursor();
        _request360Render();
    };
    cv.addEventListener('pointerup', mapUp);
    cv.addEventListener('pointercancel', mapUp);

    cv.addEventListener('wheel', e => {
        e.preventDefault();
        const r  = cv.getBoundingClientRect();
        const mx = e.clientX - r.left, my = e.clientY - r.top;
        const bx = MODE360.cam.x + mx / MODE360.cam.z;
        const by = MODE360.cam.y + my / MODE360.cam.z;
        MODE360.cam.z = Math.min(20, Math.max(.05, MODE360.cam.z * Math.exp(-e.deltaY * .002)));
        MODE360.cam.x = bx - mx / MODE360.cam.z;
        MODE360.cam.y = by - my / MODE360.cam.z;
        _clamp360Y();
        _request360Render();
        _draw360Cursor();
    }, { passive: false });
}

function _mapPinch360() {
    const [A, B] = [...MODE360.mapPts.values()];
    return { d: Math.hypot(A.x-B.x, A.y-B.y)||1, mx:(A.x+B.x)/2, my:(A.y+B.y)/2 };
}

function _clamp360Y() {
    const h = mapCanvas360 ? mapCanvas360.height : window.innerHeight;
    const maxY = Math.max(0, MODE360.H - h / MODE360.cam.z);
    MODE360.cam.y = Math.min(maxY, Math.max(0, MODE360.cam.y));
}

// ─────────────────────────────────────────────────────────────
//  EVENTOS DE LA ESFERA
// ─────────────────────────────────────────────────────────────
function _bindSphereEvents() {
    const cv = MODE360.pvCanvas;
    cv.addEventListener('contextmenu', e => e.preventDefault());

    cv.addEventListener('pointermove', e => {
        if (!MODE360.isDrawing && !MODE360.sphereDrag) {
            const r = cv.getBoundingClientRect();
            const sx = e.clientX - r.left, sy = e.clientY - r.top;
            MODE360.cursorPos = { x: sx, y: sy };
            if (typeof currentTool !== 'undefined' && currentTool === 'eyedropper') {
                const mapPt = _sphToMap(e);
                _update360EyedropperPreview(sx, sy, mapPt);
            }
            _draw360Cursor();
        }
    });
    cv.addEventListener('pointerleave', () => {
        MODE360.cursorPos = null;
        if (typeof currentTool !== 'undefined' && currentTool === 'eyedropper' && eyedropperPreview && !eyedropperPreview.classList.contains('copied')) {
            eyedropperPreview.classList.add('hidden');
        }
        _draw360Cursor();
    });

    cv.addEventListener('pointerdown', e => {
        cv.setPointerCapture(e.pointerId);
        MODE360.spherePts.set(e.pointerId, { x: e.clientX, y: e.clientY });
        const r = cv.getBoundingClientRect();
        const sx = e.clientX - r.left, sy = e.clientY - r.top;
        MODE360.cursorPos = { x: sx, y: sy };

        if (MODE360.spherePts.size === 2) {
            MODE360.sphereDrag  = null;
            MODE360.spherePinch = _sphrPinch();
            _draw360Cursor();
            return;
        }
        const isPan = e.button !== 0 || (typeof isSpacePressed !== 'undefined' && isSpacePressed);
        if (isPan) {
            MODE360.sphereDrag = { x: e.clientX, y: e.clientY };
            cv.style.cursor = 'grabbing';
            _draw360Cursor();
            return;
        }

        if (typeof currentTool !== 'undefined' && currentTool === 'eyedropper') {
            if (eyedropperFadeTimeout) { clearTimeout(eyedropperFadeTimeout); eyedropperFadeTimeout = null; }
            if (eyedropperPreview) eyedropperPreview.classList.remove('hidden', 'copied');
            const mapPt = _sphToMap(e);
            _update360EyedropperPreview(sx, sy, mapPt);
            _draw360Cursor();
            return;
        }

        if (currentBrush && currentBrush.isLasso) {
            _360StartLasso(_sphToMap(e), { x: sx, y: sy });
        } else {
            _360StartStroke(_sphToMap(e));
        }
        MODE360.srcStale = true;
        _request360PvRender();
        _draw360Cursor();
    });

    cv.addEventListener('pointermove', e => {
        const r = cv.getBoundingClientRect();
        const sx = e.clientX - r.left, sy = e.clientY - r.top;
        MODE360.cursorPos = { x: sx, y: sy };
        if (MODE360.spherePts.has(e.pointerId)) MODE360.spherePts.set(e.pointerId, { x: e.clientX, y: e.clientY });

        if (MODE360.spherePinch && MODE360.spherePts.size === 2) {
            const n = _sphrPinch();
            _sphLook(n.mx - MODE360.spherePinch.mx, n.my - MODE360.spherePinch.my);
            MODE360.fov = Math.min(2.4, Math.max(.3, MODE360.fov * MODE360.spherePinch.d / n.d));
            MODE360.spherePinch = n;
            _request360PvRender();
            _draw360Cursor();
            return;
        }
        if (MODE360.sphereDrag) {
            _sphLook(e.clientX - MODE360.sphereDrag.x, e.clientY - MODE360.sphereDrag.y);
            MODE360.sphereDrag = { x: e.clientX, y: e.clientY };
            _request360PvRender();
            _draw360Cursor();
            return;
        }

        if (typeof currentTool !== 'undefined' && currentTool === 'eyedropper') {
            const mapPt = _sphToMap(e);
            _update360EyedropperPreview(sx, sy, mapPt);
            _draw360Cursor();
            return;
        }

        if (_360IsLassoActive) {
            const rr = cv.getBoundingClientRect();
            _360MoveLasso(_sphToMap(e), { x: e.clientX - rr.left, y: e.clientY - rr.top });
            _draw360Cursor();
        } else if (MODE360.isDrawing && MODE360.lastPt) {
            const evts = e.getCoalescedEvents ? e.getCoalescedEvents() : [e];
            for (const ev of evts) {
                const c = _sphToMap(ev);
                _360MoveStroke(c);
            }
            MODE360.srcStale = true;
            _request360PvRender();
        }
        _draw360Cursor();
    });

    const sphUp = e => {
        MODE360.spherePts.delete(e.pointerId);
        if (MODE360.spherePts.size < 2) MODE360.spherePinch = null;
        if (MODE360.spherePts.size === 0) {
            if (typeof currentTool !== 'undefined' && currentTool === 'eyedropper') {
                const mapPt = _sphToMap(e);
                _apply360Eyedropper(mapPt);
                MODE360.sphereDrag = null;
                cv.style.cursor = 'none';
                _draw360Cursor();
                return;
            }
            if (_360IsLassoActive) {
                _360EndLasso();
                MODE360.srcStale = true;
                _request360PvRender();
            } else {
                _360EndStroke(() => {
                    MODE360.srcStale = true;
                    _request360PvRender();
                });
            }
            MODE360.sphereDrag = null;
            cv.style.cursor = 'none';
        }
        _draw360Cursor();
    };
    cv.addEventListener('pointerup', sphUp);
    cv.addEventListener('pointercancel', sphUp);

    cv.addEventListener('wheel', e => {
        e.preventDefault();
        MODE360.fov = Math.min(2.4, Math.max(.3, MODE360.fov * Math.exp(e.deltaY * .001)));
        _request360PvRender();
        _draw360Cursor();
    }, { passive: false });
}

function _sphLook(dx, dy) {
    const k = MODE360.fov / Math.max(300, MODE360.pvCanvas.clientHeight || 300);
    MODE360.yaw   -= dx * k;
    MODE360.pitch  = Math.max(-1.5, Math.min(1.5, MODE360.pitch + dy * k));
}

function _sphrPinch() {
    const [A, B] = [...MODE360.spherePts.values()];
    return { d: Math.hypot(A.x-B.x, A.y-B.y)||1, mx:(A.x+B.x)/2, my:(A.y+B.y)/2 };
}

function _sphToMap(e) {
    const r  = MODE360.pvCanvas.getBoundingClientRect();
    const rw = MODE360.pvCanvas.width, rh = MODE360.pvCanvas.height;
    const tf = Math.tan(MODE360.fov / 2), asp = rw / rh;
    const nx = ((e.clientX - r.left) / r.width  * 2 - 1) * tf * asp;
    const ny = (1 - (e.clientY - r.top) / r.height * 2) * tf;
    const cp = Math.cos(MODE360.pitch), sp = Math.sin(MODE360.pitch);
    const y2 = ny * cp + sp, z2 = -ny * sp + cp;
    const lon = Math.atan2(nx, z2) + MODE360.yaw;
    const len = Math.hypot(nx, y2, z2);
    const lat = Math.asin(Math.max(-1, Math.min(1, y2 / Math.max(0.0001, len))));
    const u = ((lon / (2 * Math.PI) + 0.5) % 1 + 1) % 1;
    const v = Math.max(0, Math.min(1, 0.5 - lat / Math.PI));
    return [u * MODE360.W, v * MODE360.H];
}

// ─────────────────────────────────────────────────────────────
//  EXPORTAR PNG
// ─────────────────────────────────────────────────────────────
function _360Export() {
    const c = document.createElement('canvas');
    c.width = MODE360.W; c.height = MODE360.H;
    _composit360ToCtx(c.getContext('2d'), 0, 0, MODE360.W, MODE360.H);
    const a = document.createElement('a');
    a.href     = c.toDataURL('image/png');
    a.download = ((typeof currentProjectTitle !== 'undefined' ? currentProjectTitle : null) || 'panorama-360') + '.png';
    a.click();
}

// ─────────────────────────────────────────────────────────────
//  CAPAS 360°
// ─────────────────────────────────────────────────────────────
function _new360Layer(name) {
    const cv = document.createElement('canvas');
    cv.width = MODE360.W; cv.height = MODE360.H;
    return { id: Date.now() + Math.random(), name: name || 'Capa 360', canvas: cv, ctx: cv.getContext('2d', { willReadFrequently: true }), visible: true, opacity: 1.0, blendMode: 'source-over' };
}

/* ── Añadir capa nueva arriba de la activa ── */
function add360Layer(name) {
    const newL = _new360Layer(name || ('Capa ' + (layers360.length + 1)));
    layers360.splice(selectedLayerIndex360 + 1, 0, newL);
    selectedLayerIndex360++;
    _360PushHistory();
    _360UpdateLayersUI();
    MODE360.srcStale = true;
    _request360Render();
}

/* ── Duplicar capa activa ── */
function duplicate360Layer() {
    const src = layers360[selectedLayerIndex360];
    if (!src) return;
    const newL = _new360Layer(src.name + ' copia');
    newL.visible   = src.visible;
    newL.opacity   = src.opacity;
    newL.blendMode = src.blendMode;
    newL.ctx.drawImage(src.canvas, 0, 0);
    layers360.splice(selectedLayerIndex360 + 1, 0, newL);
    selectedLayerIndex360++;
    _360PushHistory();
    _360UpdateLayersUI();
    MODE360.srcStale = true;
    _request360Render();
}

/* ── Eliminar capa activa ── */
function delete360Layer(idx) {
    if (layers360.length <= 1) return;
    const i = (idx !== undefined) ? idx : selectedLayerIndex360;
    layers360.splice(i, 1);
    selectedLayerIndex360 = Math.max(0, Math.min(selectedLayerIndex360, layers360.length - 1));
    _360PushHistory();
    _360UpdateLayersUI();
    MODE360.srcStale = true;
    _request360Render();
}

/* ── Combinar capa activa con la inferior ── */
function _360MergeLayerDown(idx) {
    const i = (idx !== undefined) ? idx : selectedLayerIndex360;
    if (i <= 0) return;
    const top = layers360[i];
    const bot = layers360[i - 1];
    bot.ctx.save();
    bot.ctx.globalAlpha = top.opacity;
    bot.ctx.globalCompositeOperation = top.blendMode;
    bot.ctx.drawImage(top.canvas, 0, 0);
    bot.ctx.restore();
    layers360.splice(i, 1);
    selectedLayerIndex360 = Math.max(0, i - 1);
    _360PushHistory();
    _360UpdateLayersUI();
    MODE360.srcStale = true;
    _request360Render();
}

/* ── Panel de capas 360°: renderiza layers360 en el panel lateral existente ── */
const _360BlendModes = [
    { value: 'source-over', label: 'NORMAL' },
    { value: 'multiply',    label: 'MULTIPLICAR' },
    { value: 'overlay',     label: 'SUPERPOSICIÓN' },
    { value: 'plus-lighter',label: 'AÑADIR' },
    { value: 'screen',      label: 'PANTALLA' },
];

function _360UpdateLayersUI() {
    if (typeof is360Mode === 'undefined' || !is360Mode) return;
    const list = typeof layersList !== 'undefined' ? layersList : document.getElementById('layers-list');
    if (!list) return;

    // Status bar
    const posSpan  = document.getElementById('layer-status-pos');
    const nameSpan = document.getElementById('layer-status-name');
    if (posSpan && nameSpan && layers360[selectedLayerIndex360]) {
        posSpan.textContent  = `${selectedLayerIndex360 + 1}/${layers360.length}`;
        nameSpan.textContent = layers360[selectedLayerIndex360].name;
    }

    list.innerHTML = '';

    // Render from top (highest index) to bottom, matching illustration panel convention
    for (let i = layers360.length - 1; i >= 0; i--) {
        const l = layers360[i];

        /* ── Thumbnail ── */
        const thumbCanvas = document.createElement('canvas');
        thumbCanvas.width = 40; thumbCanvas.height = 30;
        const tctx = thumbCanvas.getContext('2d');
        tctx.drawImage(l.canvas, 0, 0, 40, 30);

        /* ── List item ── */
        const li = document.createElement('li');
        li.className = 'layer-item' + (i === selectedLayerIndex360 ? ' active-layer' : '');
        li.dataset.index = i;
        li._layerObj360 = l;

        const mainInfo = document.createElement('div');
        mainInfo.className = 'layer-main-info';

        /* Thumbnail */
        const thumb = document.createElement('div');
        thumb.className = 'layer-thumbnail';
        const thumbImg = document.createElement('img');
        thumbImg.src = thumbCanvas.toDataURL('image/webp', 0.8);
        thumbImg.style.cssText = 'width:100%;height:100%;object-fit:cover;display:block;';
        thumbImg.draggable = false;
        thumb.appendChild(thumbImg);
        mainInfo.appendChild(thumb);

        /* Name (double-click to edit) */
        const nameEl = document.createElement('span');
        nameEl.className = 'layer-name';
        nameEl.textContent = l.name;
        nameEl.ondblclick = (e) => {
            e.stopPropagation();
            const inp = document.createElement('input');
            inp.type = 'text'; inp.value = l.name;
            inp.style.cssText = 'width:80px;font-size:11px;padding:2px;border:1px solid #6c63ff;border-radius:3px;margin-left:5px;';
            const save = () => { if (inp.value.trim()) l.name = inp.value.trim(); _360UpdateLayersUI(); _360PushHistory(); };
            inp.onblur = save;
            inp.onkeydown = ev => { if (ev.key === 'Enter') { ev.preventDefault(); save(); } };
            mainInfo.replaceChild(inp, nameEl);
            inp.focus(); inp.select();
        };
        mainInfo.appendChild(nameEl);

        /* Reorder buttons */
        const reorderWrap = document.createElement('div');
        reorderWrap.className = 'layer-reorder-btns';

        const moveUpBtn = document.createElement('button');
        moveUpBtn.className = 'layer-reorder-btn';
        moveUpBtn.title = 'Subir capa';
        moveUpBtn.innerHTML = '<img src="iconos acciones de capas/flecha arriba.png" alt="Subir">';
        moveUpBtn.disabled = (i === layers360.length - 1);
        moveUpBtn.onclick = (e) => {
            e.stopPropagation();
            if (i >= layers360.length - 1) return;
            const [moved] = layers360.splice(i, 1);
            layers360.splice(i + 1, 0, moved);
            if (selectedLayerIndex360 === i) selectedLayerIndex360 = i + 1;
            else if (selectedLayerIndex360 === i + 1) selectedLayerIndex360 = i;
            _360PushHistory(); _360UpdateLayersUI();
            MODE360.srcStale = true; _request360Render();
        };
        reorderWrap.appendChild(moveUpBtn);

        const moveDownBtn = document.createElement('button');
        moveDownBtn.className = 'layer-reorder-btn';
        moveDownBtn.title = 'Bajar capa';
        moveDownBtn.innerHTML = '<img src="iconos acciones de capas/flecha abajo.png" alt="Bajar">';
        moveDownBtn.disabled = (i === 0);
        moveDownBtn.onclick = (e) => {
            e.stopPropagation();
            if (i <= 0) return;
            const [moved] = layers360.splice(i, 1);
            layers360.splice(i - 1, 0, moved);
            if (selectedLayerIndex360 === i) selectedLayerIndex360 = i - 1;
            else if (selectedLayerIndex360 === i - 1) selectedLayerIndex360 = i;
            _360PushHistory(); _360UpdateLayersUI();
            MODE360.srcStale = true; _request360Render();
        };
        reorderWrap.appendChild(moveDownBtn);
        mainInfo.appendChild(reorderWrap);
        li.appendChild(mainInfo);

        /* Controls row */
        const controls = document.createElement('div');
        controls.className = 'layer-controls';
        controls.onmousedown  = () => { li.draggable = false; };
        controls.onmouseup    = () => { li.draggable = true; };
        controls.onmouseleave = () => { li.draggable = true; };

        /* Opacity slider */
        const opSlider = document.createElement('input');
        opSlider.type = 'range'; opSlider.className = 'layer-opacity-slider';
        opSlider.min = 0; opSlider.max = 100;
        opSlider.value = Math.round(l.opacity * 100);
        opSlider.oninput  = () => { l.opacity = opSlider.value / 100; MODE360.srcStale = true; _request360Render(); };
        opSlider.onchange = (e) => { _360PushHistory(); e.target.blur(); };
        controls.appendChild(opSlider);

        /* Buttons */
        const buttons = document.createElement('div');
        buttons.className = 'layer-buttons';

        /* Visibility */
        const visBtn = document.createElement('button');
        visBtn.className = 'mini-tool-btn' + (l.visible ? '' : ' status-invisible');
        visBtn.title = 'Visible';
        visBtn.innerHTML = '<img src="imagenes/simbolo ojo abierto.png">';
        visBtn.onclick = (e) => {
            e.stopPropagation();
            l.visible = !l.visible;
            MODE360.srcStale = true;
            _360PushHistory(); _360UpdateLayersUI(); _request360Render();
        };
        buttons.appendChild(visBtn);

        /* Merge down */
        const mergeBtn = document.createElement('button');
        mergeBtn.className = 'mini-tool-btn';
        mergeBtn.title = 'Combinar con la de abajo';
        mergeBtn.innerHTML = '<img src="simbolo combinar con el de abajo.png">';
        mergeBtn.disabled = (i === 0);
        mergeBtn.onclick = (e) => { e.stopPropagation(); _360MergeLayerDown(i); };
        buttons.appendChild(mergeBtn);

        /* Delete */
        const delBtn = document.createElement('button');
        delBtn.className = 'mini-tool-btn delete';
        delBtn.title = 'Borrar';
        delBtn.textContent = '×';
        delBtn.onclick = (e) => { e.stopPropagation(); delete360Layer(i); };
        buttons.appendChild(delBtn);

        controls.appendChild(buttons);

        /* Blend mode */
        const blendSel = document.createElement('select');
        blendSel.className = 'layer-blend-select';
        _360BlendModes.forEach(bm => {
            const opt = document.createElement('option');
            opt.value = bm.value; opt.textContent = bm.label;
            if (bm.value === l.blendMode) opt.selected = true;
            blendSel.appendChild(opt);
        });
        blendSel.onchange = () => { l.blendMode = blendSel.value; MODE360.srcStale = true; _360PushHistory(); _request360Render(); };
        controls.appendChild(blendSel);

        li.appendChild(controls);

        /* Click to select layer */
        li.addEventListener('pointerdown', (e) => {
            if (e.target.tagName === 'BUTTON' || e.target.tagName === 'INPUT' || e.target.tagName === 'SELECT') return;
            if (selectedLayerIndex360 !== i) {
                selectedLayerIndex360 = i;
                _360UpdateLayersUI();
                _360PushHistory();
            }
        });

        list.appendChild(li);
    }
}
window._360UpdateLayersUI = _360UpdateLayersUI;

// ─────────────────────────────────────────────────────────────
//  SERIALIZACIÓN (para save-system.js)
// ─────────────────────────────────────────────────────────────
function serialize360() {
    return {
        layers: layers360.map(l => ({ name: l.name, visible: l.visible, opacity: l.opacity, blend: l.blendMode, data: l.canvas.toDataURL('image/webp', 0.92) })),
        selectedLayerIndex360,
        yaw:   MODE360.yaw,
        pitch: MODE360.pitch,
        fov:   MODE360.fov,
    };
}

async function deserialize360(data) {
    if (!data || !data.layers) return;
    layers360 = [];
    for (const lData of data.layers) {
        const l = _new360Layer(lData.name);
        l.visible   = lData.visible !== false;
        l.opacity   = lData.opacity !== undefined ? lData.opacity : 1.0;
        l.blendMode = lData.blend || 'source-over';
        const img = await new Promise(res => { const i = new Image(); i.onload = () => res(i); i.src = lData.data; });
        l.ctx.drawImage(img, 0, 0);
        layers360.push(l);
    }
    selectedLayerIndex360 = data.selectedLayerIndex360 || 0;
    MODE360.yaw   = data.yaw   || 0;
    MODE360.pitch = data.pitch || 0;
    MODE360.fov   = data.fov   || 1.5;
    MODE360.srcStale = true;
    MODE360.history = [];
    MODE360.historyIndex = -1;
    _360PushHistory();
    // Refresh layer panel after load
    if (typeof is360Mode !== 'undefined' && is360Mode) _360UpdateLayersUI();
}

// ─────────────────────────────────────────────────────────────
//  ATAJOS DE TECLADO Y VINCULACIÓN DE CONTROLES
// ─────────────────────────────────────────────────────────────
document.addEventListener('keydown', e => {
    if (typeof is360Mode === 'undefined' || !is360Mode) return;
    if (e.target.tagName === 'INPUT' || e.target.tagName === 'TEXTAREA' || e.target.tagName === 'SELECT') return;

    // Rehacer (Ctrl+Y o Ctrl+Shift+Z)
    if ((e.ctrlKey || e.metaKey) && (e.key.toLowerCase() === 'y' || (e.shiftKey && e.key.toLowerCase() === 'z'))) {
        e.preventDefault();
        if (e.repeat) return;
        _360Redo();
        return;
    }
    // Deshacer (Ctrl+Z)
    if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === 'z' && !e.shiftKey) {
        e.preventDefault();
        if (e.repeat) return;
        _360Undo();
        return;
    }
    if (e.code === 'Space') {
        _draw360Cursor();
        return;
    }
    const k = e.key.toLowerCase();
    if (k === '[' && typeof sizeSlider !== 'undefined' && sizeSlider) {
        sizeSlider.value = Math.max(1, parseFloat(sizeSlider.value) - 3);
        sizeSlider.dispatchEvent(new Event('input'));
        _draw360Cursor();
    } else if (k === ']' && typeof sizeSlider !== 'undefined' && sizeSlider) {
        sizeSlider.value = Math.min(300, parseFloat(sizeSlider.value) + 3);
        sizeSlider.dispatchEvent(new Event('input'));
        _draw360Cursor();
    }
});

document.addEventListener('keyup', e => {
    if (typeof is360Mode === 'undefined' || !is360Mode) return;
    if (e.code === 'Space') {
        _draw360Cursor();
    }
});

if (typeof sizeSlider !== 'undefined' && sizeSlider) {
    sizeSlider.addEventListener('input', () => {
        if (typeof is360Mode !== 'undefined' && is360Mode) _draw360Cursor();
    });
}
