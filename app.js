console.log("Pro Illustrator: Cargando motor gráfico...");
const canvas = document.getElementById('drawing-canvas');
const ctx = canvas.getContext('2d', { desynchronized: true });

// UI Elements
const sizeSlider = document.getElementById('brush-size');
const sizeValue = document.getElementById('size-value');
const opacitySlider = document.getElementById('brush-opacity');
const opacityValue = document.getElementById('opacity-value');
const eyeIcon = document.getElementById('eye-icon');
const multiToolMenu = document.getElementById('multi-tool-menu');
const toolsList = document.getElementById('tools-list');
const brushTypeMenu = document.getElementById('brush-type-menu');
const brushTypesList = document.getElementById('brush-types-list');
const layersMenu = document.getElementById('layers-menu');
const layersList = document.getElementById('layers-list');
const colorsMenu = document.getElementById('colors-menu');
const paletteGrid = document.getElementById('palette-grid');
const mainColorPicker = document.getElementById('main-color-picker');
const addToPaletteBtn = document.getElementById('add-to-palette-btn');
const activeToolIndicator = document.getElementById('active-tool-indicator');
const filtersMenu = document.getElementById('filters-menu');
const filterModal = document.getElementById('filter-modal');
const resetRotationBtn = document.getElementById('reset-rotation-btn');
const bucketModeBtn = document.getElementById('bucket-mode-btn');
const blurSettingsContainer = document.getElementById('blur-settings-container');
const blurSlider = document.getElementById('brush-blur');
const blurValueLabel = document.getElementById('blur-value');


const mainShortcutInput = document.getElementById('main-tool-shortcut');
const brushShortcutInput = document.getElementById('brush-menu-shortcut');
const layersShortcutInput = document.getElementById('layers-menu-shortcut');
const colorsShortcutInput = document.getElementById('colors-menu-shortcut');
const configShortcutInput = document.getElementById('config-shortcut');

const mainActionsMenu = document.getElementById('main-actions-menu');
const saveSlotsMenu = document.getElementById('save-slots-menu');
const configMenu = document.getElementById('config-menu');
const resizePanel = document.getElementById('resize-panel');
const slotsContainer = document.getElementById('slots-container');

// Startup Elements
const startupModal = document.getElementById('startup-modal');
const mainApp = document.getElementById('main-app');
const canvasWidthInput = document.getElementById('canvas-width');
const canvasHeightInput = document.getElementById('canvas-height');
const createBtn = document.getElementById('create-btn');
const importBtn = document.getElementById('import-btn');
const fileInput = document.getElementById('file-input');

// Logical Canvas Size
let paperWidth = 1920; let paperHeight = 1080;

// Canvas Buffers
const strokeCanvas = document.createElement('canvas'); const sctx = strokeCanvas.getContext('2d', { willReadFrequently: true });
const groupCanvas = document.createElement('canvas'); const gctx = groupCanvas.getContext('2d', { willReadFrequently: true });
const maskBuffer = document.createElement('canvas'); const mctx = maskBuffer.getContext('2d', { willReadFrequently: true });

// UI Globals
const checkerPatternCanvas = document.createElement('canvas'); let checkerPattern = null;
let selectedColor = '#000000';


// Procedural Airbrush Texture to avoid "Tainted Canvas" Security Errors when running locally
function createProceduralAirbrushTexture() {
    const size = 256;
    const cv = document.createElement('canvas'); cv.width = size; cv.height = size;
    const cx = cv.getContext('2d');
    const imgData = cx.createImageData(size, size);
    const center = size / 2;
    const radius = center - 40; // margin for blur
    for (let y = 0; y < size; y++) {
        for (let x = 0; x < size; x++) {
            const dx = x - center; const dy = y - center;
            const dist = Math.sqrt(dx * dx + dy * dy);
            const normalizedDist = dist / radius;
            if (normalizedDist > 1) continue;
            const falloff = Math.pow(1 - normalizedDist, 1.5);
            const grain = Math.random();
            const pos = (y * size + x) * 4;
            imgData.data[pos] = 0; imgData.data[pos + 1] = 0; imgData.data[pos + 2] = 0;
            imgData.data[pos + 3] = falloff * grain * 255;
        }
    }
    cx.putImageData(imgData, 0, 0);
    cv.complete = true;
    return cv;
}


const airbrushTexture = createProceduralAirbrushTexture();
const tintedAirbrushCanvas = document.createElement('canvas'); const tactx = tintedAirbrushCanvas.getContext('2d');
// No need for onload as it's procedural now

// View & State
let viewScale = 0.5; let viewPosX = 0; let viewPosY = 0; let viewRotation = 0;
let isDrawing = false; let lastX = 0; let lastY = 0; let lastPressure = 0.5; let smoothedPressure = 0.5;
let rotationPivot = null;

// Lasso/Bucket State
let lassoPath = [];
let bucketMode = 'capa';

// ─────────────────────────────────────────────────────────────
//  SELECTION SYSTEM
// ─────────────────────────────────────────────────────────────
// selectionMask: offscreen canvas that is pure-white where selected, transparent elsewhere
let selectionCanvas = null; let selCtx = null;
let hasSelection = false;
let copyMode = 'capa';  // 'capa' | 'todas' | 'canvas'
let pasteInNewLayer = true;
let cursorMode = 'always'; // 'always' | 'auto'

// Lasso selection state
let lassoSelPath = [];       // current stroke being drawn
let lassoSelMode = 'cuadrado';  // 'libre' | 'cuadrado'
let lassoSelBtn = null;      // floating toggle button
let lassoDesBtn = null;      // floating toggle for desel
let lassoSelStartX = 0; let lassoSelStartY = 0; // for square mode

// Shape Tool State
let shapeStartX = 0, shapeStartY = 0;
let shapeFill = false;
let shapeFillBtn = null;

// Modify Selection state
let modifySelMode = 'capa';  // 'capa' | 'lienzo'
let modifySelBtn = null;     // floating mode toggle
let clearSelBtn = null;      // "Quitar selección" button
let modSelCanvas = null; let modSelCtx = null; // captured pixels
let modSelBounds = null;     // { x, y, w, h } in world coords, current transform
let modSelOrigBounds = null; // original bounds before drag
let modSelHandle = null;     // which handle is being dragged: 'tl','tc','tr','ml','mr','bl','bc','br','move'
let modSelDragStart = null;  // { wx, wy } world coords at drag start
let modSelActive = false;    // true while a transform is in progress
let modSelInitialized = false; // true once pixels captured

// Canvas Resize State
let isResizingCanvas = false;
let resizePreviewW = 0;
let resizePreviewH = 0;
let resizeActiveHandle = null; // 'tl','tc','tr','ml','mr','bl','bc','br'
let resizeStartMouse = null;
let resizeStartDim = null;

// ─────────────────────────────────────────────────────────────
// TOOL STATE
// ─────────────────────────────────────────────────────────────
let currentTool = 'pincel';
let lastBrushTool = 'Pincel Duro';

// Color & Palette
let isAddingToPalette = false;
let paletteColors = []; let paletteRows = 5; const paletteCols = 5;

// Layer System
let layers = []; let selectedLayerIndex = 0; let transparentBG = false;

// ─────────────────────────────────────────────────────────────
//  HISTORY (UNDO / REDO)
// ─────────────────────────────────────────────────────────────
const MAX_HISTORY = 40;
let historyStack = [];   // array of state snapshots
let historyIndex = -1;   // pointer into historyStack
let _historyPaused = false; // internal flag to prevent recursive pushes during restore

/** Capture the current full state into a lightweight snapshot object */
function captureHistoryState() {
    return {
        paperWidth,
        paperHeight,
        selectedLayerIndex,
        layers: layers.map(l => ({
            id: l.id,
            name: l.name,
            opacity: l.opacity,
            visible: l.visible,
            blendMode: l.blendMode,
            clippingMask: l.clippingMask,
            alphaLocked: l.alphaLocked,
            // Capture pixel data as a raw ImageData copy
            imageData: l.ctx.getImageData(0, 0, paperWidth, paperHeight)
        })),
        // Selection mask snapshot (null if none)
        selectionData: (selectionCanvas && hasSelection)
            ? selCtx.getImageData(0, 0, paperWidth, paperHeight)
            : null,
        hasSelection
    };
}

/** Push a new history entry (call BEFORE or AFTER an action — see usage) */
function pushHistory() {
    if (_historyPaused) return;
    // Truncate redo branch
    if (historyIndex < historyStack.length - 1) {
        historyStack.splice(historyIndex + 1);
    }
    historyStack.push(captureHistoryState());
    if (historyStack.length > MAX_HISTORY) historyStack.shift();
    historyIndex = historyStack.length - 1;
}

/** Restore app state from a snapshot */
function restoreHistoryState(snapshot) {
    _historyPaused = true;
    try {
        // Restore canvas dimensions first if they changed (resize undo/redo)
        if (snapshot.paperWidth && snapshot.paperHeight) {
            paperWidth = snapshot.paperWidth;
            paperHeight = snapshot.paperHeight;
        }

        // Resize all shared off-screen buffers to match restored dimensions
        strokeCanvas.width = paperWidth; strokeCanvas.height = paperHeight;
        groupCanvas.width = paperWidth; groupCanvas.height = paperHeight;
        maskBuffer.width = paperWidth; maskBuffer.height = paperHeight;

        // Rebuild layers array from snapshot
        layers = snapshot.layers.map(sl => {
            const lCanvas = document.createElement('canvas');
            lCanvas.width = sl.imageData.width;
            lCanvas.height = sl.imageData.height;
            const lCtx = lCanvas.getContext('2d', { willReadFrequently: true });
            lCtx.putImageData(sl.imageData, 0, 0);
            return {
                id: sl.id,
                name: sl.name,
                opacity: sl.opacity,
                visible: sl.visible,
                blendMode: sl.blendMode,
                clippingMask: sl.clippingMask,
                alphaLocked: sl.alphaLocked,
                canvas: lCanvas,
                ctx: lCtx,
                thumbData: ''
            };
        });
        selectedLayerIndex = Math.max(0, Math.min(snapshot.selectedLayerIndex, layers.length - 1));

        // Restore selection
        hasSelection = snapshot.hasSelection;
        if (hasSelection && snapshot.selectionData) {
            // Rebuild selection canvas at the correct (restored) size
            selectionCanvas = document.createElement('canvas');
            selectionCanvas.width = paperWidth; selectionCanvas.height = paperHeight;
            selCtx = selectionCanvas.getContext('2d');
            selCtx.putImageData(snapshot.selectionData, 0, 0);
        } else {
            if (selectionCanvas && selCtx) selCtx.clearRect(0, 0, paperWidth, paperHeight);
            hasSelection = false;
        }

        // Reset any mid-action selection state
        modSelInitialized = false; modSelCanvas = null; modSelBounds = null; modSelOrigBounds = null;

        // Recenter view if canvas size changed
        const winW = canvas.parentElement?.clientWidth || window.innerWidth;
        const winH = canvas.parentElement?.clientHeight || window.innerHeight;
        viewScale = Math.min(winW / (paperWidth + 100), winH / (paperHeight + 100));
        viewPosX = 0; viewPosY = 0;

        updateThumbnails();
        updateLayersUI();
        showSelectionButtons(currentTool);
    } finally {
        _historyPaused = false;
    }
}

function undo() {
    if (historyIndex <= 0) return; // nothing more to undo
    historyIndex--;
    restoreHistoryState(historyStack[historyIndex]);
}

function redo() {
    if (historyIndex >= historyStack.length - 1) return; // nothing to redo
    historyIndex++;
    restoreHistoryState(historyStack[historyIndex]);
}

// Tool Data
let toolsData = [
    { id: 'zoom', name: 'Zoom', shortcut: '' },
    { id: 'pan', name: 'Pan', shortcut: '' },
    { id: 'rotate', name: 'Girar Lienzo', shortcut: '' },
    { id: 'bucket', name: 'Cubeta', shortcut: '' },
    { id: 'lazo-sel', name: 'Lazo Seleccionador', shortcut: '' },
    { id: 'lazo-des', name: 'Lazo Deseleccionador', shortcut: '' },
    { id: 'modify-sel', name: 'Modificar Selección', shortcut: '' },
];
const brushTypesData = [
    // size = baseBrushSize default, opacity = 0..1, blur = px
    { id: 'duro', name: 'Pincel Duro', shortcut: '', hardness: 0.8, useCompositing: true, useTexture: false, size: 2, opacity: 1.00, blur: 0 },
    { id: 'suave', name: 'Pincel Suave', shortcut: '', hardness: 0.3, useCompositing: false, useTexture: false, size: 3, opacity: 0.11, blur: 0 },
    { id: 'borrador', name: 'Borrador', shortcut: '', hardness: 0.8, useCompositing: false, useTexture: false, isEraser: true, size: 3, opacity: 1.00, blur: 0 },
    { id: 'aero-duro', name: 'Aerógrafo Duro', shortcut: '', hardness: 0.8, useCompositing: true, useTexture: false, size: 1, opacity: 1.00, blur: 12 },
    { id: 'aero-suave', name: 'Aerógrafo Suave', shortcut: '', hardness: 0.2, useCompositing: true, useTexture: true, size: 3, opacity: 1.00, blur: 25 },
    { id: 'lazo-relleno', name: 'Lazo de Relleno', shortcut: '', hardness: 1.0, isLasso: true, lassoColor: '#ff00ff', size: 10, opacity: 1.00, blur: 0 },
    { id: 'lazo-borrador', name: 'Lazo Borrador', ashortcut: '', hardness: 1.0, isLasso: true, lassoColor: '#ff0000', isEraser: true, size: 10, opacity: 1.00, blur: 0 },
    // ── Shape tools ──
    { id: 'linea', name: 'Línea', shortcut: '', isShape: true, shapeType: 'line', useCompositing: true, useTexture: false, hardness: 1.0, size: 3, opacity: 1.00, blur: 0 },
    { id: 'rectangulo', name: 'Rectángulo', shortcut: '', isShape: true, shapeType: 'rect', useCompositing: true, useTexture: false, hardness: 1.0, size: 2, opacity: 1.00, blur: 0 },
    { id: 'circulo', name: 'Círculo / Elipse', shortcut: '', isShape: true, shapeType: 'ellipse', useCompositing: true, useTexture: false, hardness: 1.0, size: 2, opacity: 1.00, blur: 0 },
];


const blendModes = [
    { value: 'source-over', label: 'NORMAL' },
    { value: 'multiply', label: 'MULTIPLICAR' },
    { value: 'overlay', label: 'SUPERPOSICIÓN' },
    { value: 'plus-lighter', label: 'AÑADIR' },
    { value: 'screen', label: 'PANTALLA' },
];

let currentBrush = brushTypesData[0];
let baseBrushSize = currentBrush.size;
let brushOpacity = currentBrush.opacity;
let brushSpacing = 0.1;
let currentBlur = currentBrush.blur;

updateTintedTexture();


// ─────────────────────────────────────────────────────────────
//  INIT
// ─────────────────────────────────────────────────────────────
function init() {
    createCheckerPattern(); setupScreen();
    window.addEventListener('resize', setupScreen);
    document.addEventListener('contextmenu', e => e.preventDefault());

    // Core event listeners - attached ONLY ONCE
    canvas.addEventListener('pointerdown', handlePointerDown);
    canvas.addEventListener('pointermove', handlePointerMove);
    canvas.addEventListener('pointerup', handlePointerUp);
    canvas.addEventListener('pointercancel', handlePointerUp);
    requestAnimationFrame(render);

    createBtn.onclick = () => startApp(parseInt(canvasWidthInput.value) | 0, parseInt(canvasHeightInput.value) | 0);
    importBtn.onclick = () => fileInput.click();
    fileInput.onchange = (e) => {
        const file = e.target.files[0]; if (!file) return;
        const reader = new FileReader(); reader.onload = (ev) => {
            const img = new Image(); img.onload = () => startApp(img.width, img.height, img); img.src = ev.target.result;
        }; reader.readAsDataURL(file);
    };

    sizeSlider.oninput = (e) => { baseBrushSize = e.target.value | 0; sizeValue.textContent = baseBrushSize; currentBrush.size = baseBrushSize; };
    opacitySlider.oninput = (e) => { brushOpacity = e.target.value / 100; opacityValue.textContent = e.target.value + '%'; currentBrush.opacity = brushOpacity; if (eyeIcon) eyeIcon.src = (e.target.value | 0) === 0 ? 'simbolo ojo cerrado.png' : 'simbolo ojo abierto.png'; };
    blurSlider.oninput = (e) => { currentBlur = e.target.value | 0; blurValueLabel.textContent = currentBlur; currentBrush.blur = currentBlur; updateTintedTexture(); };


    resetRotationBtn.onclick = resetRotation;
    document.addEventListener('keydown', handleGlobalShortcuts);

    document.getElementById('new-layer-btn').onclick = () => addLayer("Nueva Capa");
    document.getElementById('insert-layer-btn').onclick = () => addLayer("Capa desde lienzo", true);
    document.getElementById('toggle-bg-btn').onclick = toggleBackground;

    [mainShortcutInput, brushShortcutInput, layersShortcutInput, colorsShortcutInput, configShortcutInput].forEach(inp => {
        if (inp) inp.addEventListener('input', () => { if (inp.value.length > 1) inp.value = inp.value.slice(-1); saveShortcuts(); });
    });

    mainColorPicker.oninput = (e) => { selectedColor = e.target.value; updateTintedTexture(); };

    addToPaletteBtn.onclick = () => { isAddingToPalette = true; addToPaletteBtn.classList.add('active-waiting'); };

    // Main Actions UI
    document.getElementById('btn-config').onclick = () => toggleMenu(configMenu);
    document.getElementById('btn-main-actions').onclick = () => toggleMenu(mainActionsMenu);
    document.getElementById('action-download-png').onclick = () => { downloadImage(); toggleMenu(null); };
    document.getElementById('action-copy-all').onclick = () => { copyFlatImageToClipboard(); toggleMenu(null); };
    document.getElementById('action-show-save-slots').onclick = () => { toggleMenu(saveSlotsMenu); renderSaveSlots(); };

    // Filters Menu
    document.getElementById('btn-filters').onclick = () => toggleMenu(filtersMenu);
    document.querySelectorAll('.filter-opt-btn').forEach(btn => {
        btn.onclick = () => {
            toggleMenu(null);
            openFilterModal(btn.dataset.filter);
        };
    });

    // Filter Modal Actions
    document.getElementById('filter-apply-btn').onclick = commitFilter;
    document.getElementById('filter-cancel-btn').onclick = cancelFilter;

    // Config Menu Toggles
    document.getElementById('toggle-copy-mode').onclick = (e) => {
        const modes = ['capa', 'todas', 'canvas'];
        const labels = ['POR CAPA', 'TODAS LAS CAPAS', 'LIENZO COMPLETO'];
        const next = (modes.indexOf(copyMode) + 1) % modes.length;
        copyMode = modes[next];
        e.target.textContent = labels[next];
    };
    document.getElementById('toggle-paste-layer').onclick = (e) => {
        pasteInNewLayer = !pasteInNewLayer;
        e.target.textContent = pasteInNewLayer ? 'ON' : 'OFF';
    };
    document.getElementById('toggle-cursor-mode').onclick = (e) => {
        cursorMode = cursorMode === 'always' ? 'auto' : 'always';
        e.target.textContent = cursorMode === 'always' ? 'SIEMPRE VISIBLE' : 'AUTOMÁTICO';
        applyCursor(false); // restore cursor immediately if switching to 'always'
    };

    // Resize Canvas
    document.getElementById('btn-resize-canvas').onclick = () => { openResizeModal(); toggleMenu(null); };

    // Fullscreen
    const fsBtn = document.getElementById('btn-fullscreen');
    fsBtn.onclick = () => toggleFullscreen();
    document.addEventListener('fullscreenchange', () => {
        fsBtn.textContent = document.fullscreenElement ? 'Salir de pantalla completa' : 'Pantalla completa';
    });

    // Build floating selection UI buttons (hidden by default)
    buildSelectionUI();

    initPalette(); loadShortcuts(); setupMultiToolMenu(); setupBrushMenu();
}

// ─────────────────────────────────────────────────────────────
//  FILTERS LOGIC
// ─────────────────────────────────────────────────────────────
let activeFilterType = null;
let filterOriginalImgData = null;

// Curves state
let curvePoints = [{x: 0, y: 255}, {x: 255, y: 0}];
let draggingCurvePoint = null;
let edgesBgMode = 'transparent';
let blackWhiteBgMode = 'transparent';

function openFilterModal(type) {
    activeFilterType = type;
    const l = layers[selectedLayerIndex];
    filterOriginalImgData = l.ctx.getImageData(0, 0, paperWidth, paperHeight);

    const title = document.getElementById('filter-title');
    const desc = document.getElementById('filter-desc');
    const container = document.getElementById('filter-controls-container');
    container.innerHTML = '';

    if (type === 'blackwhite') {
        title.textContent = 'Blanco y Negro (Lineart)';
        desc.textContent = 'Extrae el lineart basándote en la luminosidad.';
        addFilterToggle('Fondo', ['transparent', 'white'], blackWhiteBgMode, (v) => { blackWhiteBgMode = v; applyFilters(); });
        addFilterSlider('Punto Negro', 0, 255, 20, (v) => applyFilters());
        addFilterSlider('Punto Blanco', 0, 255, 230, (v) => applyFilters());
        addFilterSlider('Sensibilidad (Gamma)', 1, 30, 10, (v) => applyFilters()); // 1.0 * 10
    } else if (type === 'levels') {
        title.textContent = 'Curvas de Nivel';
        desc.textContent = 'Ajusta el histograma arrastrando los puntos.';
        curvePoints = [{x: 0, y: 255}, {x: 255, y: 0}]; // Reset to default when opening
        addFilterCurveEditor(container);
    } else if (type === 'hue') {
        title.textContent = 'Cambiar Tono';
        desc.textContent = 'Cambia el matiz (0-360°).';
        addFilterSlider('Matiz', 0, 360, 0, (v) => applyFilters());
    } else if (type === 'edges') {
        title.textContent = 'Encontrar Bordes';
        desc.textContent = 'Genera lineart a partir de los bordes.';
        edgesBgMode = 'transparent';
        addFilterToggle('Fondo', ['transparent', 'white'], 'transparent', (v) => { edgesBgMode = v; applyFilters(); });
        addFilterSlider('Sensibilidad', 1, 150, 40, (v) => applyFilters());
        addFilterSlider('Fuerza Negro', 1, 30, 12, (v) => applyFilters()); // 1.2 * 10
        addFilterSlider('Limpieza', 0, 100, 15, (v) => applyFilters());
    } else if (type === 'invert') {
        title.textContent = 'Invertir Colores';
        desc.textContent = 'Invierte todos los colores de la capa.';
    }

    filterModal.classList.remove('hidden');
    makeDraggable(filterModal, document.getElementById('filter-header'));
    
    if (type === 'levels') {
        drawFilterHistogram();
        updateCurveUI();
    }
    
    applyFilters();
}

function addFilterSlider(label, min, max, val, oninput) {
    const wrap = document.createElement('div');
    wrap.style.cssText = 'display:flex; flex-direction:column; gap:4px;';

    wrap.innerHTML = `
        <div style="display:flex; justify-content:space-between; align-items:center;">
            <label style="font-size:11px; font-weight:700; color:#444;">${label}</label>
            <span class="val-display" style="font-size:11px; font-weight:700; background:#eee; padding:2px 6px; border-radius:4px;">${val}</span>
        </div>
        <div style="display:flex; gap:8px; align-items:center;">
            <button class="step-btn mini-tool-btn" style="width:24px; height:24px;">-</button>
            <input type="range" min="${min}" max="${max}" value="${val}" style="flex:1; height:4px;">
            <button class="step-btn mini-tool-btn" style="width:24px; height:24px;">+</button>
        </div>
    `;

    const input = wrap.querySelector('input');
    const display = wrap.querySelector('.val-display');
    const [btnDown, btnUp] = wrap.querySelectorAll('.step-btn');

    const update = (v) => {
        v = Math.max(min, Math.min(max, v));
        input.value = v;
        display.textContent = v;
        oninput(parseInt(v));
    };

    input.oninput = () => update(input.value);
    btnDown.onclick = () => update(parseInt(input.value) - 1);
    btnUp.onclick = () => update(parseInt(input.value) + 1);

    document.getElementById('filter-controls-container').appendChild(wrap);
}

function addFilterToggle(label, modes, current, onclick) {
    const wrap = document.createElement('div');
    wrap.style.cssText = 'display:flex; flex-direction:column; gap:6px; margin-bottom:5px;';
    wrap.innerHTML = `
        <label style="font-size:11px; font-weight:700; color:#444;">${label}</label>
        <div style="display:flex; gap:5px; background:#f0f0f0; padding:4px; border-radius:10px;">
            ${modes.map(m => `<button class="layer-action-btn" style="flex:1; border:none; border-radius:6px; background:${m===current?'#000':'transparent'}; color:${m===current?'#fff':'#666'}; padding:6px; font-size:10px; font-weight:700; cursor:pointer;">${m === 'transparent' ? 'TRANSPARENTE' : 'BLANCO'}</button>`).join('')}
        </div>
    `;
    const btns = wrap.querySelectorAll('button');
    btns.forEach((btn, idx) => {
        btn.onclick = () => {
            btns.forEach(b => { b.style.background = 'transparent'; b.style.color = '#666'; });
            btn.style.background = '#000';
            btn.style.color = '#fff';
            onclick(modes[idx]);
        };
    });
    document.getElementById('filter-controls-container').appendChild(wrap);
}

// ── Curve Editor UI & Logic ──

function addFilterCurveEditor(container) {
    const area = document.createElement('div');
    area.className = 'curve-area';
    area.innerHTML = `
        <canvas id="histoCanvas" width="256" height="256"></canvas>
        <svg id="curveSvg" viewBox="0 0 256 256">
            <polyline id="curveLine"></polyline>
        </svg>
        <div class="curve-hint"><b>Doble Click</b>: añadir/quitar | <b>Arrastrar</b>: ajustar</div>
    `;
    container.appendChild(area);

    const svg = area.querySelector('#curveSvg');
    
    svg.addEventListener('mousedown', handleCurveMouseDown);
    svg.addEventListener('dblclick', handleCurveDblClick);
    
    // Global listeners for dragging
    window.addEventListener('mousemove', handleCurveMouseMove);
    window.addEventListener('mouseup', handleCurveMouseUp);
}

function getCurveMousePos(e) {
    const svg = document.getElementById('curveSvg');
    if (!svg) return {x:0, y:0};
    const rect = svg.getBoundingClientRect();
    return {
        x: Math.round(Math.max(0, Math.min(255, e.clientX - rect.left))),
        y: Math.round(Math.max(0, Math.min(255, e.clientY - rect.top)))
    };
}

function handleCurveMouseDown(e) {
    const pos = getCurveMousePos(e);
    const hitIndex = curvePoints.findIndex(p => Math.hypot(p.x - pos.x, p.y - pos.y) < 12);
    if (hitIndex !== -1) draggingCurvePoint = hitIndex;
}

function handleCurveMouseMove(e) {
    if (draggingCurvePoint === null) return;
    const pos = getCurveMousePos(e);
    
    if (draggingCurvePoint === 0) {
        curvePoints[0].y = pos.y;
    } else if (draggingCurvePoint === curvePoints.length - 1) {
        curvePoints[curvePoints.length - 1].y = pos.y;
    } else {
        const prevX = curvePoints[draggingCurvePoint - 1].x;
        const nextX = curvePoints[draggingCurvePoint + 1].x;
        curvePoints[draggingCurvePoint].x = Math.max(prevX + 1, Math.min(nextX - 1, pos.x));
        curvePoints[draggingCurvePoint].y = pos.y;
    }
    updateCurveUI();
    applyFilters();
}

function handleCurveMouseUp() {
    draggingCurvePoint = null;
}

function handleCurveDblClick(e) {
    const pos = getCurveMousePos(e);
    const hitIndex = curvePoints.findIndex(p => Math.hypot(p.x - pos.x, p.y - pos.y) < 12);

    if (hitIndex > 0 && hitIndex < curvePoints.length - 1) {
        curvePoints.splice(hitIndex, 1);
    } else if (hitIndex === -1) {
        curvePoints.push(pos);
        curvePoints.sort((a, b) => a.x - b.x);
    }
    updateCurveUI();
    applyFilters();
}

function updateCurveUI() {
    const line = document.getElementById('curveLine');
    const svg = document.getElementById('curveSvg');
    if (!line || !svg) return;

    line.setAttribute('points', curvePoints.map(p => `${p.x},${p.y}`).join(' '));
    
    // Clear old circles
    svg.querySelectorAll('.curve-point').forEach(c => c.remove());
    
    curvePoints.forEach((p, i) => {
        const c = document.createElementNS("http://www.w3.org/2000/svg", "circle");
        c.setAttribute("cx", p.x); 
        c.setAttribute("cy", p.y); 
        c.setAttribute("r", 5);
        c.setAttribute("class", "curve-point");
        svg.appendChild(c);
    });
}

function drawFilterHistogram() {
    const hCanvas = document.getElementById('histoCanvas');
    if (!hCanvas || !filterOriginalImgData) return;
    const hCtx = hCanvas.getContext('2d');
    const data = filterOriginalImgData.data;
    const hist = new Array(256).fill(0);
    
    for (let i = 0; i < data.length; i += 4) {
        const avg = Math.round((data[i] + data[i+1] + data[i+2]) / 3);
        hist[avg]++;
    }
    
    const max = Math.max(...hist);
    hCtx.clearRect(0, 0, 256, 256);
    hCtx.fillStyle = 'rgba(255, 255, 255, 0.4)';
    for (let i = 0; i < 256; i++) {
        const h = (hist[i] / (max || 1)) * 256;
        hCtx.fillRect(i, 256 - h, 1, h);
    }
}

function makeDraggable(el, handle) {
    let pos1 = 0, pos2 = 0, pos3 = 0, pos4 = 0;
    handle.onmousedown = (e) => {
        e.preventDefault();
        pos3 = e.clientX; pos4 = e.clientY;
        document.onmouseup = () => { document.onmouseup = null; document.onmousemove = null; };
        document.onmousemove = (e) => {
            e.preventDefault();
            pos1 = pos3 - e.clientX; pos2 = pos4 - e.clientY;
            pos3 = e.clientX; pos4 = e.clientY;
            el.style.top = (el.offsetTop - pos2) + "px";
            el.style.left = (el.offsetLeft - pos1) + "px";
        };
    };
}

function applyFilters() {
    if (!filterOriginalImgData) return;
    const sliders = document.getElementById('filter-controls-container').querySelectorAll('input[type="range"]');
    const l = layers[selectedLayerIndex];

    // Create copy for processing
    const workingData = new ImageData(new Uint8ClampedArray(filterOriginalImgData.data), paperWidth, paperHeight);
    const data = workingData.data;

    if (activeFilterType === 'blackwhite') {
        const bPoint = parseInt(sliders[0].value);
        const wPoint = parseInt(sliders[1].value);
        const gamma = parseInt(sliders[2].value) / 10;
        
        for (let i = 0; i < data.length; i += 4) {
            const origA = data[i+3];
            const luma = 0.299 * data[i] + 0.587 * data[i + 1] + 0.114 * data[i + 2];
            let alpha;
            if (luma <= bPoint) alpha = 255;
            else if (luma >= wPoint) alpha = 0;
            else alpha = 255 * (1 - (luma - bPoint) / (wPoint - bPoint || 1));

            alpha = Math.pow(alpha / 255, gamma) * 255;
            if (alpha > 255) alpha = 255;

            // Combinar alpha calculado con el original para respetar transparencia
            const combinedA = alpha * (origA / 255);

            if (blackWhiteBgMode === 'transparent') {
                data[i] = data[i+1] = data[i+2] = 0;
                data[i+3] = combinedA;
            } else {
                const val = 255 - combinedA;
                data[i] = data[i+1] = data[i+2] = val;
                data[i+3] = 255;
            }
        }
    } else if (activeFilterType === 'levels') {
        const lut = new Uint8Array(256);
        for (let i = 0; i < curvePoints.length - 1; i++) {
            const p1 = curvePoints[i], p2 = curvePoints[i+1];
            for (let x = p1.x; x <= p2.x; x++) {
                const t = (x - p1.x) / (p2.x - p1.x || 1);
                lut[x] = 255 - (p1.y + t * (p2.y - p1.y));
            }
        }
        for (let i = 0; i < data.length; i += 4) {
            data[i] = lut[data[i]];
            data[i + 1] = lut[data[i + 1]];
            data[i + 2] = lut[data[i + 2]];
        }
    } else if (activeFilterType === 'hue') {
        const hueShift = parseInt(sliders[0].value);
        for (let i = 0; i < data.length; i += 4) {
            const [r, g, b] = [data[i], data[i + 1], data[i + 2]];
            let [h, s, l] = rgbToHsl(r, g, b);
            h = (h + hueShift) % 360;
            const [nr, ng, nb] = hslToRgb(h, s, l);
            data[i] = nr; data[i + 1] = ng; data[i + 2] = nb;
        }
    } else if (activeFilterType === 'edges') {
        const sens = parseInt(sliders[0].value) / 10;
        const gamma = parseInt(sliders[1].value) / 10;
        const clean = parseInt(sliders[2].value);
        
        const width = paperWidth;
        const height = paperHeight;
        const gray = new Float32Array(width * height);
        const orig = filterOriginalImgData.data;

        // 1. Grayscale pass
        for (let i = 0; i < orig.length; i += 4) {
            gray[i/4] = 0.299 * orig[i] + 0.587 * orig[i+1] + 0.114 * orig[i+2];
        }

        // 2. Sobel pass
        for (let y = 1; y < height - 1; y++) {
            for (let x = 1; x < width - 1; x++) {
                const i = y * width + x;
                // Kernels
                const gx = -gray[i-width-1] + gray[i-width+1] - 2*gray[i-1] + 2*gray[i+1] - gray[i+width-1] + gray[i+width+1];
                const gy = -gray[i-width-1] - 2*gray[i-width] - gray[i-width+1] + gray[i+width-1] + 2*gray[i+width] + gray[i+width+1];
                
                let mag = Math.sqrt(gx*gx + gy*gy) * sens;
                mag = Math.max(0, mag - clean);
                let alpha = Math.pow(mag / 255, 1 / gamma) * 255;
                if (alpha > 255) alpha = 255;

                const idx = i * 4;
                const origA = orig[idx+3];
                const combinedA = alpha * (origA / 255);

                if (edgesBgMode === 'transparent') {
                    data[idx] = data[idx+1] = data[idx+2] = 0;
                    data[idx+3] = combinedA;
                } else {
                    const val = 255 - combinedA;
                    data[idx] = data[idx+1] = data[idx+2] = val;
                    data[idx+3] = 255;
                }
            }
        }
    } else if (activeFilterType === 'invert') {
        for (let i = 0; i < data.length; i += 4) {
            data[i] = 255 - data[i];
            data[i+1] = 255 - data[i+1];
            data[i+2] = 255 - data[i+2];
        }
    }

    l.ctx.putImageData(workingData, 0, 0);
}

function commitFilter() {
    pushHistory(); // Capture the new state
    filterModal.classList.add('hidden');
    filterOriginalImgData = null;
    updateThumbnails(); updateLayersUI();
}

function cancelFilter() {
    if (filterOriginalImgData) {
        layers[selectedLayerIndex].ctx.putImageData(filterOriginalImgData, 0, 0);
    }
    filterModal.classList.add('hidden');
    filterOriginalImgData = null;
}

// Helper: RGB to HSL
function rgbToHsl(r, g, b) {
    r /= 255; g /= 255; b /= 255;
    const max = Math.max(r, g, b), min = Math.min(r, g, b);
    let h, s, l = (max + min) / 2;
    if (max === min) h = s = 0;
    else {
        const d = max - min;
        s = l > 0.5 ? d / (2 - max - min) : d / (max + min);
        switch (max) {
            case r: h = (g - b) / d + (g < b ? 6 : 0); break;
            case g: h = (b - r) / d + 2; break;
            case b: h = (r - g) / d + 4; break;
        }
        h *= 60;
    }
    return [h, s, l];
}

// Helper: HSL to RGB
function hslToRgb(h, s, l) {
    let r, g, b;
    if (s === 0) r = g = b = l;
    else {
        const hue2rgb = (p, q, t) => {
            if (t < 0) t += 1; if (t > 1) t -= 1;
            if (t < 1 / 6) return p + (q - p) * 6 * t;
            if (t < 1 / 2) return q;
            if (t < 2 / 3) return p + (q - p) * (2 / 3 - t) * 6;
            return p;
        };
        const q = l < 0.5 ? l * (1 + s) : l + s - l * s;
        const p = 2 * l - q;
        r = hue2rgb(p, q, h / 360 + 1 / 3);
        g = hue2rgb(p, q, h / 360);
        b = hue2rgb(p, q, h / 360 - 1 / 3);
    }
    return [Math.round(r * 255), Math.round(g * 255), Math.round(b * 255)];
}

// ─────────────────────────────────────────────────────────────
//  FULLSCREEN
// ─────────────────────────────────────────────────────────────
function toggleFullscreen() {
    if (!document.fullscreenElement) {
        document.documentElement.requestFullscreen().catch(err => console.warn('Fullscreen error:', err));
    } else {
        document.exitFullscreen();
    }
}

// ─────────────────────────────────────────────────────────────
//  RESIZE CANVAS
// ─────────────────────────────────────────────────────────────
let resizeAnchor = 'tl';

document.getElementById('resize-cancel-btn').onclick = () => {
    isResizingCanvas = false;
    resizeActiveHandle = null;
    canvas.style.cursor = '';
    resizePanel.classList.add('hidden');
};

document.getElementById('resize-apply-btn').onclick = () => {
    const newW = parseInt(document.getElementById('resize-width').value) | 0;
    const newH = parseInt(document.getElementById('resize-height').value) | 0;
    if (newW < 1 || newH < 1 || newW > 8000 || newH > 8000) {
        alert('Dimensiones inválidas (1–8000 px)');
        return;
    }
    isResizingCanvas = false;
    resizeActiveHandle = null;
    canvas.style.cursor = '';
    resizePanel.classList.add('hidden');
    resizeCanvas(newW, newH, resizeAnchor);
};

// Sync inputs with preview
document.getElementById('resize-width').oninput = (e) => {
    if (!isResizingCanvas) return;
    resizePreviewW = parseInt(e.target.value) || 1;
};
document.getElementById('resize-height').oninput = (e) => {
    if (!isResizingCanvas) return;
    resizePreviewH = parseInt(e.target.value) || 1;
};

// Anchor dot clicks
document.querySelectorAll('.anchor-dot').forEach(b => {
    b.onclick = () => {
        resizeAnchor = b.dataset.anchor;
        document.querySelectorAll('.anchor-dot').forEach(x => x.classList.remove('active'));
        b.classList.add('active');
    };
});

function openResizeModal() {
    isResizingCanvas = true;
    resizePreviewW = paperWidth;
    resizePreviewH = paperHeight;
    
    document.getElementById('resize-width').value = paperWidth;
    document.getElementById('resize-height').value = paperHeight;

    // Reset anchor to mc (center) as requested or keep mc default
    resizeAnchor = 'mc';
    document.querySelectorAll('.anchor-dot').forEach(b => {
        b.classList.toggle('active', b.dataset.anchor === resizeAnchor);
    });

    resizePanel.classList.remove('hidden');
    makeDraggable(resizePanel, document.getElementById('resize-header'));
}

/**
 * Resize the logical canvas, preserving existing layer content at the chosen anchor.
 * anchor: 'tl' | 'tc' | 'tr' | 'ml' | 'mc' | 'mr' | 'bl' | 'bc' | 'br'
 */
function resizeCanvas(newW, newH, anchor = 'tl') {
    // Compute the offset at which old content is pasted into the new canvas
    let ox = 0, oy = 0;
    const dw = newW - paperWidth;
    const dh = newH - paperHeight;

    const col = anchor[1]; // 'l', 'c', 'r'
    const row = anchor[0]; // 't', 'm', 'b'

    if (col === 'c') ox = Math.round(dw / 2);
    else if (col === 'r') ox = dw;

    if (row === 'm') oy = Math.round(dh / 2);
    else if (row === 'b') oy = dh;

    // Resize each layer
    layers.forEach(l => {
        const newCanvas = document.createElement('canvas');
        newCanvas.width = newW; newCanvas.height = newH;
        const newCtx = newCanvas.getContext('2d');
        newCtx.drawImage(l.canvas, ox, oy);
        l.canvas = newCanvas;
        l.ctx = newCtx;
    });

    // Update logical size
    paperWidth = newW;
    paperHeight = newH;

    // Resize shared buffers
    strokeCanvas.width = newW; strokeCanvas.height = newH;
    groupCanvas.width = newW; groupCanvas.height = newH;
    maskBuffer.width = newW; maskBuffer.height = newH;

    // Ensure selection canvas matches
    if (selectionCanvas) {
        const newSel = document.createElement('canvas');
        newSel.width = newW; newSel.height = newH;
        const newSelCtx = newSel.getContext('2d');
        if (hasSelection) newSelCtx.drawImage(selectionCanvas, ox, oy);
        selectionCanvas = newSel; selCtx = newSelCtx;
    }

    // Reset view to fit new canvas
    const winW = canvas.parentElement.clientWidth;
    const winH = canvas.parentElement.clientHeight;
    viewScale = Math.min(winW / (newW + 100), winH / (newH + 100));
    viewPosX = 0; viewPosY = 0;

    updateThumbnails();
    updateLayersUI();
    pushHistory(); // snapshot AFTER resize
}

// ─────────────────────────────────────────────────────────────
//  INDEXED DB & SAVE SYSTEM
// ─────────────────────────────────────────────────────────────
const DB_NAME = 'IllustratorProDB'; const DB_VERSION = 1;
const getDB = () => new Promise((res, rej) => {
    const req = indexedDB.open(DB_NAME, DB_VERSION);
    req.onupgradeneeded = () => req.result.createObjectStore('slots');
    req.onsuccess = () => res(req.result); req.onerror = () => rej(req.error);
});

async function saveToSlot(id) {
    const db = await getDB();

    // Generate a flat 160x90 thumbnail of the current canvas state
    const thumbCanvas = document.createElement('canvas');
    thumbCanvas.width = 160; thumbCanvas.height = 90;
    const tctx = thumbCanvas.getContext('2d');
    tctx.fillStyle = '#ffffff';
    tctx.fillRect(0, 0, 160, 90);
    const flat = getFlatImage();
    tctx.drawImage(flat, 0, 0, 160, 90);
    const thumbDataURL = thumbCanvas.toDataURL('image/jpeg', 0.7);

    const project = {
        w: paperWidth, h: paperHeight,
        thumb: thumbDataURL,
        savedAt: Date.now(),
        layers: layers.map(l => ({ name: l.name, opacity: l.opacity, visible: l.visible, blend: l.blendMode, clipping: l.clippingMask, alphaLocked: l.alphaLocked, data: l.canvas.toDataURL() }))
    };
    const tx = db.transaction('slots', 'readwrite');
    tx.objectStore('slots').put(project, id);
    return new Promise(res => tx.oncomplete = () => {
        alert(`Proyecto guardado en RANURA ${id}`);
        renderSaveSlots(); // refresh thumbnails
        res();
    });
}

async function loadFromSlot(id) {
    const db = await getDB();
    const tx = db.transaction('slots', 'readonly');
    const project = await new Promise(res => tx.objectStore('slots').get(id).onsuccess = e => res(e.target.result));
    if (!project) { alert("Esta ranura está vacía."); return; }

    if (!confirm("Se perderá el progreso actual. ¿Cargar ranura?")) return;

    paperWidth = project.w; paperHeight = project.h;
    setupLogicalCanvas();
    layers = [];
    for (const lData of project.layers) {
        const lCanvas = document.createElement('canvas'); lCanvas.width = paperWidth; lCanvas.height = paperHeight;
        const lCtx = lCanvas.getContext('2d');
        const img = await new Promise(res => { const i = new Image(); i.onload = () => res(i); i.src = lData.data; });
        lCtx.drawImage(img, 0, 0);
        layers.push({ id: Date.now() + Math.random(), name: lData.name, canvas: lCanvas, ctx: lCtx, visible: lData.visible, opacity: lData.opacity, blendMode: lData.blend || 'source-over', clippingMask: !!lData.clipping, alphaLocked: !!lData.alphaLocked, thumbData: '' });
    }
    selectedLayerIndex = layers.length - 1;
    // Reset history for fresh project load
    historyStack = []; historyIndex = -1;
    updateThumbnails(); updateLayersUI();
    pushHistory(); // seed history with loaded state
    toggleMenu(null);
}

async function renderSaveSlots() {
    slotsContainer.innerHTML = '<div style="text-align:center; padding:12px; color:#aaa; font-size:12px;">Cargando...</div>';

    // Load all 5 slots in parallel from IndexedDB
    const db = await getDB();
    const projects = await Promise.all(
        [1, 2, 3, 4, 5].map(i => new Promise(res => {
            const tx = db.transaction('slots', 'readonly');
            tx.objectStore('slots').get(i).onsuccess = e => res(e.target.result || null);
        }))
    );

    slotsContainer.innerHTML = '';

    projects.forEach((project, idx) => {
        const i = idx + 1;
        const isEmpty = !project;

        const div = document.createElement('div');
        div.style.cssText = [
            'display:flex', 'flex-direction:column', 'gap:8px',
            'background:#f9f9f9', 'border-radius:12px',
            'border:1px solid #eee', 'overflow:hidden',
            'transition: box-shadow 0.2s'
        ].join(';');
        div.onmouseenter = () => div.style.boxShadow = '0 4px 16px rgba(0,0,0,0.10)';
        div.onmouseleave = () => div.style.boxShadow = '';

        // ── Thumbnail area ──
        const thumbWrap = document.createElement('div');
        thumbWrap.style.cssText = 'position:relative; width:100%; aspect-ratio:16/9; background:#e0e0e0; overflow:hidden;';

        if (isEmpty) {
            // Checkerboard placeholder
            thumbWrap.style.backgroundImage = [
                'linear-gradient(45deg, #ccc 25%, transparent 25%)',
                'linear-gradient(-45deg,#ccc 25%, transparent 25%)',
                'linear-gradient(45deg, transparent 75%,#ccc 75%)',
                'linear-gradient(-45deg,transparent 75%,#ccc 75%)'
            ].join(',');
            thumbWrap.style.backgroundSize = '16px 16px';
            thumbWrap.style.backgroundPosition = '0 0, 0 8px, 8px -8px, -8px 0px';
            const emptyLabel = document.createElement('div');
            emptyLabel.textContent = 'Vacía';
            emptyLabel.style.cssText = 'position:absolute; inset:0; display:flex; align-items:center; justify-content:center; font-size:12px; font-weight:700; color:#aaa; letter-spacing:1px;';
            thumbWrap.appendChild(emptyLabel);
        } else {
            if (project.thumb) {
                const img = document.createElement('img');
                img.src = project.thumb;
                img.style.cssText = 'width:100%; height:100%; object-fit:cover; display:block;';
                thumbWrap.appendChild(img);
            } else {
                // Old save without thumbnail — show a text label
                const oldLabel = document.createElement('div');
                oldLabel.textContent = 'Sin vista previa';
                oldLabel.style.cssText = 'position:absolute; inset:0; display:flex; align-items:center; justify-content:center; font-size:11px; color:#888;';
                thumbWrap.appendChild(oldLabel);
            }
        }
        div.appendChild(thumbWrap);

        // ── Footer: slot info + buttons ──
        const footer = document.createElement('div');
        footer.style.cssText = 'display:flex; justify-content:space-between; align-items:center; padding:8px 10px;';

        const info = document.createElement('div');
        info.style.cssText = 'display:flex; flex-direction:column; gap:2px;';

        const slotLabel = document.createElement('span');
        slotLabel.textContent = `RANURA ${i}`;
        slotLabel.style.cssText = 'font-size:11px; font-weight:700; color:#555;';
        info.appendChild(slotLabel);

        if (!isEmpty) {
            const meta = document.createElement('span');
            const date = project.savedAt ? new Date(project.savedAt).toLocaleDateString('es', { day: '2-digit', month: '2-digit', year: '2-digit', hour: '2-digit', minute: '2-digit' }) : '';
            meta.textContent = `${project.w}×${project.h}px${date ? '  ·  ' + date : ''}`;
            meta.style.cssText = 'font-size:9px; color:#aaa; font-weight:600; letter-spacing:0.3px;';
            info.appendChild(meta);
        }

        const btns = document.createElement('div');
        btns.style.cssText = 'display:flex; gap:5px;';

        const saveBtn = document.createElement('button');
        saveBtn.className = 'layer-action-btn';
        saveBtn.textContent = 'GUARDAR';
        saveBtn.style.cssText = 'background:#e8f5e9; color:#2e7d32; min-width:58px;';
        saveBtn.onclick = () => saveToSlot(i);

        const loadBtn = document.createElement('button');
        loadBtn.className = 'layer-action-btn';
        loadBtn.textContent = 'CARGAR';
        loadBtn.style.cssText = `background:#e3f2fd; color:#1565c0; min-width:58px; opacity:${isEmpty ? 0.4 : 1}; pointer-events:${isEmpty ? 'none' : 'auto'};`;
        loadBtn.onclick = () => loadFromSlot(i);
        if (isEmpty) loadBtn.disabled = true;

        btns.appendChild(saveBtn);
        btns.appendChild(loadBtn);
        footer.appendChild(info);
        footer.appendChild(btns);
        div.appendChild(footer);

        slotsContainer.appendChild(div);
    });
}

// ─────────────────────────────────────────────────────────────
//  SELECTION UI FACTORY
// ─────────────────────────────────────────────────────────────
function buildSelectionUI() {
    const container = document.getElementById('indicator-container');

    // Lasso Sel mode toggle
    lassoSelBtn = document.createElement('button');
    lassoSelBtn.id = 'lasso-sel-mode-btn';
    lassoSelBtn.className = 'indicator-extra-btn hidden';
    lassoSelBtn.textContent = 'LAZO: CUADRADO';
    lassoSelBtn.onclick = () => {
        lassoSelMode = lassoSelMode === 'libre' ? 'cuadrado' : 'libre';
        lassoSelBtn.textContent = `LAZO: ${lassoSelMode.toUpperCase()}`;
    };
    container.appendChild(lassoSelBtn);

    // Lasso Des mode toggle
    lassoDesBtn = document.createElement('button');
    lassoDesBtn.id = 'lasso-des-mode-btn';
    lassoDesBtn.className = 'indicator-extra-btn hidden';
    lassoDesBtn.textContent = 'LAZO: CUADRADO';
    lassoDesBtn.onclick = () => {
        lassoSelMode = lassoSelMode === 'libre' ? 'cuadrado' : 'libre';
        lassoDesBtn.textContent = `LAZO: ${lassoSelMode.toUpperCase()}`;
    };
    container.appendChild(lassoDesBtn);

    // Modify Sel: scope toggle
    modifySelBtn = document.createElement('button');
    modifySelBtn.id = 'modify-sel-scope-btn';
    modifySelBtn.className = 'indicator-extra-btn hidden';
    modifySelBtn.textContent = 'ÁMBITO: CAPA';
    modifySelBtn.onclick = () => {
        if (modSelInitialized) return; // can't change while modifying
        modifySelMode = modifySelMode === 'capa' ? 'lienzo' : 'capa';
        modifySelBtn.textContent = `ÁMBITO: ${modifySelMode === 'capa' ? 'CAPA' : 'LIENZO'}`;
    };
    container.appendChild(modifySelBtn);

    // Modify Sel: quit button
    clearSelBtn = document.createElement('button');
    clearSelBtn.id = 'clear-sel-btn';
    clearSelBtn.className = 'indicator-extra-btn hidden sel-danger';
    clearSelBtn.textContent = 'QUITAR SELECCIÓN';
    clearSelBtn.onclick = clearSelection;
    container.appendChild(clearSelBtn);

    // Shape Fill toggle
    shapeFillBtn = document.createElement('button');
    shapeFillBtn.id = 'shape-fill-btn';
    shapeFillBtn.className = 'indicator-extra-btn hidden';
    shapeFillBtn.textContent = 'RELLENO: OFF';
    shapeFillBtn.onclick = () => {
        shapeFill = !shapeFill;
        shapeFillBtn.textContent = `RELLENO: ${shapeFill ? 'ON' : 'OFF'}`;
        shapeFillBtn.style.background = shapeFill ? '#0066ff' : '';
        shapeFillBtn.style.color = shapeFill ? 'white' : '';
    };
    container.appendChild(shapeFillBtn);
}

function showSelectionButtons(tool) {
    // Hide all extras first
    [lassoSelBtn, lassoDesBtn, modifySelBtn, clearSelBtn, bucketModeBtn, shapeFillBtn].forEach(b => { if (b) b.classList.add('hidden'); });

    if (tool === 'lazo-sel') { if (lassoSelBtn) lassoSelBtn.classList.remove('hidden'); if (hasSelection && clearSelBtn) clearSelBtn.classList.remove('hidden'); }
    if (tool === 'lazo-des') { if (lassoDesBtn) lassoDesBtn.classList.remove('hidden'); if (hasSelection && clearSelBtn) clearSelBtn.classList.remove('hidden'); }
    if (tool === 'modify-sel') { if (modifySelBtn) modifySelBtn.classList.remove('hidden'); if (clearSelBtn) clearSelBtn.classList.remove('hidden'); }
    if (tool === 'bucket') { if (bucketModeBtn) bucketModeBtn.classList.remove('hidden'); }
    // Show fill toggle for rect & ellipse shapes
    if (tool === 'pincel' && currentBrush.isShape && currentBrush.shapeType !== 'line') {
        if (shapeFillBtn) shapeFillBtn.classList.remove('hidden');
    }
}

// ─────────────────────────────────────────────────────────────
//  SELECTION MASK HELPERS
// ─────────────────────────────────────────────────────────────
function ensureSelectionCanvas() {
    if (!selectionCanvas || selectionCanvas.width !== paperWidth || selectionCanvas.height !== paperHeight) {
        selectionCanvas = document.createElement('canvas');
        selectionCanvas.width = paperWidth; selectionCanvas.height = paperHeight;
        selCtx = selectionCanvas.getContext('2d');
    }
}

// Add a closed polygon path to the selection mask
function addPathToSelection(path) {
    if (path.length < 3) return;
    ensureSelectionCanvas();
    selCtx.save();
    selCtx.globalCompositeOperation = 'source-over';
    selCtx.fillStyle = 'white';
    selCtx.beginPath();
    selCtx.moveTo(path[0].x, path[0].y);
    path.forEach(p => selCtx.lineTo(p.x, p.y));
    selCtx.closePath();
    selCtx.fill();
    selCtx.restore();
    hasSelection = true;
}

// Subtract a closed polygon path from the selection mask
function subtractPathFromSelection(path) {
    if (path.length < 3 || !selectionCanvas) return;
    selCtx.save();
    selCtx.globalCompositeOperation = 'destination-out';
    selCtx.fillStyle = 'white';
    selCtx.beginPath();
    selCtx.moveTo(path[0].x, path[0].y);
    path.forEach(p => selCtx.lineTo(p.x, p.y));
    selCtx.closePath();
    selCtx.fill();
    selCtx.restore();
    // check if still anything selected
    const d = selCtx.getImageData(0, 0, paperWidth, paperHeight).data;
    hasSelection = d.some((v, i) => i % 4 === 3 && v > 0);
}

function clearSelection() {
    if (selectionCanvas && selCtx) selCtx.clearRect(0, 0, paperWidth, paperHeight);
    hasSelection = false;
    // commit any pending modify
    if (modSelInitialized) commitModifySelection();
    modSelInitialized = false; modSelBounds = null; modSelOrigBounds = null;
    if (lassoSelBtn) lassoSelBtn.classList.remove('hidden'); // keep lasso btn visible if on that tool
    if (clearSelBtn) clearSelBtn.classList.add('hidden');
    showSelectionButtons(currentTool);
}

// Build a square path from two world corners
function squarePath(ax, ay, bx, by) {
    return [{ x: ax, y: ay }, { x: bx, y: ay }, { x: bx, y: by }, { x: ax, y: by }];
}

// ─────────────────────────────────────────────────────────────
//  MODIFY SELECTION – capture & apply
// ─────────────────────────────────────────────────────────────
function initModifySelection() {
    if (modSelInitialized) return;
    // Capture pixels
    const bounds = getSelectionBounds();
    if (!bounds) return;

    modSelBounds = { ...bounds };
    modSelOrigBounds = { ...bounds };

    modSelCanvas = document.createElement('canvas');
    modSelCanvas.width = bounds.w; modSelCanvas.height = bounds.h;
    modSelCtx = modSelCanvas.getContext('2d');

    if (modifySelMode === 'capa') {
        // Cut from active layer, clipped to selection
        const l = layers[selectedLayerIndex];
        modSelCtx.save();
        // clip to selection shape
        selCtx.save();
        const selImgData = l.ctx.getImageData(bounds.x, bounds.y, bounds.w, bounds.h);
        modSelCtx.putImageData(selImgData, 0, 0);
        // Mask by selection canvas
        modSelCtx.globalCompositeOperation = 'destination-in';
        modSelCtx.drawImage(selectionCanvas, -bounds.x, -bounds.y);
        modSelCtx.restore();
        // Erase from source layer
        l.ctx.save();
        l.ctx.globalCompositeOperation = 'destination-out';
        l.ctx.drawImage(selectionCanvas, 0, 0);
        l.ctx.restore();
    } else {
        // Capture flattened lienzo
        const flat = document.createElement('canvas'); flat.width = paperWidth; flat.height = paperHeight;
        const fctx = flat.getContext('2d');
        layers.forEach(l => { if (l.visible) { fctx.save(); fctx.globalAlpha = l.opacity; fctx.globalCompositeOperation = l.blendMode; fctx.drawImage(l.canvas, 0, 0); fctx.restore(); } });
        const flatImgData = fctx.getImageData(bounds.x, bounds.y, bounds.w, bounds.h);
        modSelCtx.putImageData(flatImgData, 0, 0);
        modSelCtx.globalCompositeOperation = 'destination-in';
        modSelCtx.drawImage(selectionCanvas, -bounds.x, -bounds.y);
        modSelCtx.resetTransform();
        // Erase from all visible layers
        layers.forEach(l => { if (l.visible) { l.ctx.save(); l.ctx.globalCompositeOperation = 'destination-out'; l.ctx.drawImage(selectionCanvas, 0, 0); l.ctx.restore(); } });
    }
    modSelInitialized = true;
    updateThumbnails(); updateLayersUI();
}

function getSelectionBounds() {
    if (!selectionCanvas) return null;
    const d = selCtx.getImageData(0, 0, paperWidth, paperHeight).data;
    let minX = paperWidth, minY = paperHeight, maxX = 0, maxY = 0, found = false;
    for (let y = 0; y < paperHeight; y++) {
        for (let x = 0; x < paperWidth; x++) {
            if (d[(y * paperWidth + x) * 4 + 3] > 0) {
                if (x < minX) minX = x; if (x > maxX) maxX = x;
                if (y < minY) minY = y; if (y > maxY) maxY = y;
                found = true;
            }
        }
    }
    if (!found) return null;
    return { x: minX, y: minY, w: maxX - minX + 1, h: maxY - minY + 1 };
}

function commitModifySelection() {
    if (!modSelInitialized || !modSelCanvas || !modSelBounds) return;
    const b = modSelBounds;
    const target = layers[selectedLayerIndex].ctx;
    target.save();
    target.drawImage(modSelCanvas, b.x, b.y, b.w, b.h);
    target.restore();
    modSelInitialized = false; modSelCanvas = null; modSelBounds = null; modSelOrigBounds = null;
    updateThumbnails(); updateLayersUI();
}

// ─────────────────────────────────────────────────────────────
//  CLIPBOARD & EXPORT
// ─────────────────────────────────────────────────────────────
// ─────────────────────────────────────────────────────────────
//  SHARED LAYER COMPOSITOR (respects clipping mask groups)
// ─────────────────────────────────────────────────────────────
/**
 * Composites all visible layers onto destCtx, fully respecting
 * clipping mask groups — the same logic used by the render loop.
 */
function compositeLayers(destCtx) {
    const gC = document.createElement('canvas'); gC.width = paperWidth; gC.height = paperHeight; const gX = gC.getContext('2d');
    const mC = document.createElement('canvas'); mC.width = paperWidth; mC.height = paperHeight; const mX = mC.getContext('2d');

    let i = 0;
    while (i < layers.length) {
        const l = layers[i];
        if (!l.visible) { i++; continue; }

        // Collect clipping group
        let group = [l];
        let next = i + 1;
        while (next < layers.length && layers[next].clippingMask) {
            if (layers[next].visible) group.push(layers[next]);
            next++;
        }

        if (group.length > 1) {
            // ── Render clipping group ──
            gX.clearRect(0, 0, paperWidth, paperHeight);
            gX.save(); gX.globalAlpha = group[0].opacity; gX.globalCompositeOperation = group[0].blendMode;
            gX.drawImage(group[0].canvas, 0, 0); gX.restore();

            for (let k = 1; k < group.length; k++) {
                mX.clearRect(0, 0, paperWidth, paperHeight);
                mX.save(); mX.globalAlpha = group[k].opacity;
                mX.drawImage(group[k].canvas, 0, 0); mX.restore();
                mX.globalCompositeOperation = 'destination-in';
                mX.drawImage(group[0].canvas, 0, 0);
                mX.globalCompositeOperation = 'source-over';
                gX.save(); gX.globalCompositeOperation = group[k].blendMode;
                gX.drawImage(mC, 0, 0); gX.restore();
            }
            destCtx.drawImage(gC, 0, 0);
            i = next;
        } else {
            // ── Normal layer ──
            destCtx.save();
            destCtx.globalAlpha = l.opacity;
            destCtx.globalCompositeOperation = l.blendMode;
            destCtx.drawImage(l.canvas, 0, 0);
            destCtx.restore();
            i++;
        }
    }
}

function getFlatImage() {
    const flat = document.createElement('canvas');
    flat.width = paperWidth; flat.height = paperHeight;
    const fctx = flat.getContext('2d');

    if (!transparentBG) {
        fctx.fillStyle = 'white';
        fctx.fillRect(0, 0, paperWidth, paperHeight);
    }

    compositeLayers(fctx);
    return flat;
}

function downloadImage() {
    const flat = getFlatImage();
    const link = document.createElement('a');
    link.download = 'ilustracion_pro.png';
    link.href = flat.toDataURL('image/png');
    link.click();
}

async function copyFlatImageToClipboard() {
    const flat = getFlatImage();
    flat.toBlob(async blob => {
        try {
            const item = new ClipboardItem({ "image/png": blob });
            await navigator.clipboard.write([item]);
            alert("Imagen completa copiada al portapapeles");
        } catch (err) { alert("Error al copiar: " + err); }
    }, 'image/png');
}

async function copyToClipboard() {
    if (!hasSelection) { alert("Selecciona un área primero para copiar."); return; }
    const bounds = getSelectionBounds();
    if (!bounds) return;

    const temp = document.createElement('canvas');
    temp.width = bounds.w; temp.height = bounds.h;
    const tctx = temp.getContext('2d');

    if (copyMode === 'capa') {
        // Solo la capa activa, recortada por la selección
        const l = layers[selectedLayerIndex];
        tctx.save();
        tctx.drawImage(selectionCanvas, -bounds.x, -bounds.y);
        tctx.globalCompositeOperation = 'source-in';
        tctx.drawImage(l.canvas, -bounds.x, -bounds.y);
        tctx.restore();
    } else if (copyMode === 'todas') {
        // Todas las capas visibles SIN fondo blanco, con clipping masks, recortado por selección
        const flat = document.createElement('canvas'); flat.width = paperWidth; flat.height = paperHeight;
        const fctx = flat.getContext('2d');
        compositeLayers(fctx);
        tctx.save();
        tctx.drawImage(selectionCanvas, -bounds.x, -bounds.y);
        tctx.globalCompositeOperation = 'source-in';
        tctx.drawImage(flat, -bounds.x, -bounds.y);
        tctx.restore();
    } else {
        // Lienzo completo (incluye fondo blanco si corresponde), recortado por selección
        const flat = getFlatImage();
        tctx.save();
        tctx.drawImage(selectionCanvas, -bounds.x, -bounds.y);
        tctx.globalCompositeOperation = 'source-in';
        tctx.drawImage(flat, -bounds.x, -bounds.y);
        tctx.restore();
    }

    temp.toBlob(async blob => {
        try {
            const item = new ClipboardItem({ "image/png": blob });
            await navigator.clipboard.write([item]);
            console.log("Copiado al portapapeles");
        } catch (err) { alert("Error al copiar: " + err); }
    }, 'image/png');
}

async function pasteFromClipboard() {
    try {
        const items = await navigator.clipboard.read();
        for (const item of items) {
            for (const type of item.types) {
                if (type.startsWith('image/')) {
                    const blob = await item.getType(type);
                    const img = new Image();
                    img.src = URL.createObjectURL(blob);
                    img.onload = () => {
                        // Center image
                        const x = (paperWidth - img.width) / 2;
                        const y = (paperHeight - img.height) / 2;

                        if (pasteInNewLayer) {
                            // ── Nueva capa ──
                            const lCanvas = document.createElement('canvas');
                            lCanvas.width = paperWidth; lCanvas.height = paperHeight;
                            const lCtx = lCanvas.getContext('2d', { willReadFrequently: true });
                            lCtx.drawImage(img, x, y);

                            const newLayer = { id: Date.now(), name: "Pegado", canvas: lCanvas, ctx: lCtx, visible: true, opacity: 1.0, thumbData: '', alphaLocked: false, clippingMask: false, blendMode: 'source-over' };
                            layers.splice(selectedLayerIndex + 1, 0, newLayer);
                            selectedLayerIndex++;

                            // Select the image area so Modify tool can pick it up
                            ensureSelectionCanvas();
                            selCtx.clearRect(0, 0, paperWidth, paperHeight);
                            selCtx.fillStyle = 'white';
                            selCtx.fillRect(x, y, img.width, img.height);
                            hasSelection = true;

                            updateThumbnails(); updateLayersUI();
                            pushHistory(); // snapshot AFTER paste layer created

                            // Trigger Modify Selection mode immediately
                            selectTool('modify-sel', 'Modificar Selección');
                            initModifySelection();
                        } else {
                            // ── Capa actual (modo fantasma) ──
                            // La imagen NO se escribe en la capa todavía.
                            // Se construye el modSelCanvas manualmente para que flote
                            // sobre la capa sin destruir su contenido previo.

                            // Cancelar cualquier modificación pendiente antes de empezar
                            if (modSelInitialized) commitModifySelection();

                            // Fijar la selección al área pegada
                            ensureSelectionCanvas();
                            selCtx.clearRect(0, 0, paperWidth, paperHeight);
                            selCtx.fillStyle = 'white';
                            selCtx.fillRect(x, y, img.width, img.height);
                            hasSelection = true;

                            // Construir el canvas fantasma directamente con la imagen
                            modSelCanvas = document.createElement('canvas');
                            modSelCanvas.width = img.width;
                            modSelCanvas.height = img.height;
                            modSelCtx = modSelCanvas.getContext('2d');
                            modSelCtx.drawImage(img, 0, 0);

                            // Definir límites del fantasma
                            modSelBounds = { x, y, w: img.width, h: img.height };
                            modSelOrigBounds = { ...modSelBounds };
                            modSelInitialized = true;

                            updateThumbnails(); updateLayersUI();
                            // NO pushHistory aquí — se hará al confirmar con commitModifySelection

                            // Activar la herramienta Modificar Selección
                            selectTool('modify-sel', 'Modificar Selección');
                        }
                    };
                    return;
                }
            }
        }
    } catch (err) { console.error("Error al pegar:", err); }
}


// Handle hit-test for the 8 handles + center move
const HANDLE_R = 8; // radius in world px
function getModifyHandle(wx, wy) {
    if (!modSelBounds) return null;
    const b = modSelBounds;
    const handles = {
        tl: [b.x, b.y],
        tc: [b.x + b.w / 2, b.y],
        tr: [b.x + b.w, b.y],
        ml: [b.x, b.y + b.h / 2],
        mr: [b.x + b.w, b.y + b.h / 2],
        bl: [b.x, b.y + b.h],
        bc: [b.x + b.w / 2, b.y + b.h],
        br: [b.x + b.w, b.y + b.h],
    };
    const hitR = HANDLE_R / viewScale;
    for (const [k, [hx, hy]] of Object.entries(handles)) {
        if (Math.hypot(wx - hx, wy - hy) <= hitR) return k;
    }
    // Check if inside bounds → move
    if (wx >= b.x && wx <= b.x + b.w && wy >= b.y && wy <= b.y + b.h) return 'move';
    return null;
}

function applyModifyDrag(dx, dy, handle, origB) {
    const b = { ...origB };
    switch (handle) {
        case 'move': b.x += dx; b.y += dy; break;
        case 'tl': b.x += dx; b.y += dy; b.w -= dx; b.h -= dy; break;
        case 'tc': b.y += dy; b.h -= dy; break;
        case 'tr': b.y += dy; b.w += dx; b.h -= dy; break;
        case 'ml': b.x += dx; b.w -= dx; break;
        case 'mr': b.w += dx; break;
        case 'bl': b.x += dx; b.w -= dx; b.h += dy; break;
        case 'bc': b.h += dy; break;
        case 'br': b.w += dx; b.h += dy; break;
    }
    if (b.w < 1) b.w = 1;
    if (b.h < 1) b.h = 1;
    return b;
}

// ─────────────────────────────────────────────────────────────
//  CANVAS RESIZE INTERACTION
// ─────────────────────────────────────────────────────────────
function getCanvasResizeHandle(wx, wy) {
    if (!isResizingCanvas) return null;
    const nw = resizePreviewW;
    const nh = resizePreviewH;

    // Mirror the anchor-offset logic from the renderer
    const dw = nw - paperWidth;
    const dh = nh - paperHeight;
    const col = resizeAnchor[1];
    const row = resizeAnchor[0];
    let ox = 0, oy = 0;
    if (col === 'c') ox = Math.round(dw / 2);
    else if (col === 'r') ox = dw;
    if (row === 'm') oy = Math.round(dh / 2);
    else if (row === 'b') oy = dh;

    const x0 = -ox, y0 = -oy;

    const handles = {
        tl: [x0, y0],
        tc: [x0 + nw / 2, y0],
        tr: [x0 + nw, y0],
        ml: [x0, y0 + nh / 2],
        mr: [x0 + nw, y0 + nh / 2],
        bl: [x0, y0 + nh],
        bc: [x0 + nw / 2, y0 + nh],
        br: [x0 + nw, y0 + nh],
    };
    const hitR = HANDLE_R / viewScale;
    for (const [k, [hx, hy]] of Object.entries(handles)) {
        if (Math.hypot(wx - hx, wy - hy) <= hitR) return k;
    }
    return null;
}

function applyCanvasResizeDrag(dx, dy, handle, origW, origH) {
    let nw = origW;
    let nh = origH;
    switch (handle) {
        case 'tl': nw = origW - dx; nh = origH - dy; break;
        case 'tc': nh = origH - dy; break;
        case 'tr': nw = origW + dx; nh = origH - dy; break;
        case 'ml': nw = origW - dx; break;
        case 'mr': nw = origW + dx; break;
        case 'bl': nw = origW - dx; nh = origH + dy; break;
        case 'bc': nh = origH + dy; break;
        case 'br': nw = origW + dx; nh = origH + dy; break;
    }
    return { nw: Math.max(1, Math.min(8000, Math.round(nw))), nh: Math.max(1, Math.min(8000, Math.round(nh))) };
}

// ─────────────────────────────────────────────────────────────
//  CANVAS SETUP
// ─────────────────────────────────────────────────────────────
function createCheckerPattern() {
    checkerPatternCanvas.width = 20; checkerPatternCanvas.height = 20;
    const pctx = checkerPatternCanvas.getContext('2d');
    pctx.fillStyle = '#ffffff'; pctx.fillRect(0, 0, 20, 20);
    pctx.fillStyle = '#f0f0f0'; pctx.fillRect(0, 0, 10, 10); pctx.fillRect(10, 10, 10, 10);
    checkerPattern = ctx.createPattern(checkerPatternCanvas, 'repeat');
}
function startApp(w, h, initialImg = null) {
    paperWidth = w || 1920; paperHeight = h || 1080;
    const winW = canvas.parentElement.clientWidth; const winH = canvas.parentElement.clientHeight;
    viewScale = Math.min(winW / (paperWidth + 100), winH / (paperHeight + 100));
    setupLogicalCanvas(initialImg);
    // Seed the history with the initial blank state
    historyStack = []; historyIndex = -1;
    pushHistory();
    startupModal.style.display = 'none'; mainApp.classList.remove('blur-content'); mainApp.style.pointerEvents = 'auto';
    updateTintedTexture();
}

function setupScreen() {
    if (!canvas || !canvas.parentElement) return;
    const w = canvas.parentElement.clientWidth || window.innerWidth;
    const h = canvas.parentElement.clientHeight || window.innerHeight;
    canvas.width = w; canvas.height = h;
}
function setupLogicalCanvas(initialImg) {
    strokeCanvas.width = paperWidth; strokeCanvas.height = paperHeight;
    groupCanvas.width = paperWidth; groupCanvas.height = paperHeight;
    maskBuffer.width = paperWidth; maskBuffer.height = paperHeight;
    layers = []; addLayer("Capa 1");
    if (initialImg) layers[0].ctx.drawImage(initialImg, 0, 0);
    updateThumbnails();
}

// ─────────────────────────────────────────────────────────────
//  PALETTE
// ─────────────────────────────────────────────────────────────
function initPalette() {
    const saved = localStorage.getItem('illustrator_palette');
    if (saved) { try { paletteColors = JSON.parse(saved); paletteRows = Math.max(5, Math.ceil(paletteColors.length / paletteCols)); } catch (e) { paletteColors = Array(paletteRows * paletteCols).fill(null); } }
    else { paletteColors = Array(paletteRows * paletteCols).fill(null); }
    renderPalette();
}
function renderPalette() {
    paletteGrid.innerHTML = '';
    paletteColors.forEach((color, index) => {
        const cell = document.createElement('div'); cell.className = 'palette-cell'; if (color) cell.style.background = color;
        cell.onclick = () => {
            if (isAddingToPalette) { paletteColors[index] = selectedColor; isAddingToPalette = false; addToPaletteBtn.classList.remove('active-waiting'); checkAndExpandPalette(index); savePalette(); renderPalette(); }
            else if (color) { selectedColor = color; mainColorPicker.value = color; updateTintedTexture(); }
        };

        cell.oncontextmenu = (e) => { e.preventDefault(); showColorContextMenu(e.clientX, e.clientY, index); };
        paletteGrid.appendChild(cell);
    });
}
function savePalette() { localStorage.setItem('illustrator_palette', JSON.stringify(paletteColors)); }
function checkAndExpandPalette(index) { if (Math.floor(index / paletteCols) === paletteRows - 1) { paletteRows++; paletteColors = paletteColors.concat(Array(paletteCols).fill(null)); } }
function showColorContextMenu(x, y, index) {
    const old = document.querySelector('.ctx-menu'); if (old) old.remove();
    const menu = document.createElement('div'); menu.className = 'ctx-menu'; menu.style.left = x + 'px'; menu.style.top = y + 'px';
    const color = paletteColors[index];
    if (color) { const cp = document.createElement('div'); cp.className = 'ctx-item'; cp.textContent = `Copiar ${color}`; cp.onclick = () => { if (navigator.clipboard) navigator.clipboard.writeText(color); menu.remove(); }; menu.appendChild(cp); }
    const del = document.createElement('div'); del.className = 'ctx-item delete'; del.textContent = 'Eliminar';
    del.onclick = () => { paletteColors[index] = null; checkAndShrinkPalette(); savePalette(); renderPalette(); menu.remove(); }; menu.appendChild(del);
    document.body.appendChild(menu); document.addEventListener('click', () => menu.remove(), { once: true });
}
function checkAndShrinkPalette() {
    if (paletteRows <= 5) return;
    while (paletteRows > 5) {
        const start = (paletteRows - 1) * paletteCols;
        const rowEmpty = paletteColors.slice(start, start + paletteCols).every(c => c === null);
        if (rowEmpty) { const prevStart = (paletteRows - 2) * paletteCols; if (paletteColors.slice(prevStart, prevStart + paletteCols).every(c => c === null)) { paletteColors.splice(start, paletteCols); paletteRows--; } else break; } else break;
    }
}

// ─────────────────────────────────────────────────────────────
//  LAYERS
// ─────────────────────────────────────────────────────────────
function addLayer(name, fromCanvas = false) {
    const lCanvas = document.createElement('canvas'); lCanvas.width = paperWidth; lCanvas.height = paperHeight;
    const lCtx = lCanvas.getContext('2d', { willReadFrequently: true });
    if (fromCanvas && layers.length > 0) {
        // Flatten all layers respecting clipping mask groups
        compositeLayers(lCtx);
    }
    const newLayer = { id: Date.now(), name, canvas: lCanvas, ctx: lCtx, visible: true, opacity: 1.0, thumbData: '', alphaLocked: false, clippingMask: false, blendMode: 'source-over' };
    if (layers.length === 0) { layers.push(newLayer); selectedLayerIndex = 0; }
    else { layers.splice(selectedLayerIndex + 1, 0, newLayer); selectedLayerIndex++; }
    updateThumbnails(); updateLayersUI();
    pushHistory(); // snapshot AFTER adding the new layer
}
function toggleBackground() {
    transparentBG = !transparentBG;
    const btn = document.getElementById('toggle-bg-btn'); if (btn) btn.textContent = transparentBG ? "Fondo transparente OFF" : "Fondo transparente ON";
}
function mergeLayerDown(index) {
    if (index <= 0) return;
    const curr = layers[index];
    const target = layers[index - 1];

    const maxOp = Math.max(curr.opacity, target.opacity);
    if (maxOp <= 0) {
        layers.splice(index, 1);
        updateThumbnails(); updateLayersUI();
        pushHistory(); // snapshot AFTER removing zero-opacity layer
        return;
    }

    // Create a temporary buffer to perform the 'Smart Merge'
    const tempCanvas = document.createElement('canvas');
    tempCanvas.width = paperWidth; tempCanvas.height = paperHeight;
    const tctx = tempCanvas.getContext('2d');

    // 1. Draw target (bottom) with relative opacity
    tctx.save();
    tctx.globalAlpha = target.opacity / maxOp;
    tctx.drawImage(target.canvas, 0, 0);
    tctx.restore();

    // 2. Draw current (top) respecting clipping mask if applicable
    if (curr.clippingMask) {
        // curr clips onto target — draw curr into a buffer then mask to target
        const clipBuf = document.createElement('canvas');
        clipBuf.width = paperWidth; clipBuf.height = paperHeight;
        const cctx = clipBuf.getContext('2d');
        cctx.save();
        cctx.globalAlpha = curr.opacity / maxOp;
        cctx.drawImage(curr.canvas, 0, 0);
        cctx.restore();
        cctx.globalCompositeOperation = 'destination-in';
        cctx.drawImage(target.canvas, 0, 0); // clip to target's shape
        tctx.save();
        tctx.globalCompositeOperation = curr.blendMode;
        tctx.drawImage(clipBuf, 0, 0);
        tctx.restore();
    } else {
        tctx.save();
        tctx.globalAlpha = curr.opacity / maxOp;
        tctx.globalCompositeOperation = curr.blendMode;
        tctx.drawImage(curr.canvas, 0, 0);
        tctx.restore();
    }

    // 3. Update target layer
    target.ctx.clearRect(0, 0, paperWidth, paperHeight);
    target.ctx.drawImage(tempCanvas, 0, 0);
    target.opacity = maxOp;

    layers.splice(index, 1);
    selectedLayerIndex = Math.max(0, index - 1);
    updateThumbnails(); updateLayersUI();
    pushHistory(); // snapshot AFTER merge is complete
}
function updateThumbnails() {
    const tThumb = document.createElement('canvas'); tThumb.width = 80; tThumb.height = 60; const tctx = tThumb.getContext('2d');
    layers.forEach(l => {
        tctx.clearRect(0, 0, 80, 60); tctx.fillStyle = '#ffffff'; tctx.fillRect(0, 0, 80, 60);
        tctx.fillStyle = '#f0f0f0'; tctx.fillRect(0, 0, 10, 10); tctx.fillRect(10, 10, 10, 10);
        tctx.drawImage(l.canvas, 0, 0, 80, 60); l.thumbData = tThumb.toDataURL();
    });
}
function updateLayersUI() {
    layersList.innerHTML = '';
    for (let i = layers.length - 1; i >= 0; i--) {
        const l = layers[i]; const li = document.createElement('li');
        li.className = `layer-item ${i === selectedLayerIndex ? 'active-layer' : ''}`;
        li.draggable = true;

        // Drag and Drop Logic
        li.ondragstart = (e) => {
            e.dataTransfer.setData('text/plain', i);
            li.classList.add('dragging');
        };
        li.ondragend = () => li.classList.remove('dragging');
        li.ondragover = (e) => {
            e.preventDefault();
            li.classList.add('drag-over');
        };
        li.ondragleave = () => li.classList.remove('drag-over');
        li.ondrop = (e) => {
            e.preventDefault();
            li.classList.remove('drag-over');
            const fromIndex = parseInt(e.dataTransfer.getData('text/plain'));
            const toIndex = i;
            if (fromIndex === toIndex) return;

            // Reorder array
            const movedLayer = layers.splice(fromIndex, 1)[0];
            layers.splice(toIndex, 0, movedLayer);

            // Adjust selection
            selectedLayerIndex = toIndex;
            updateThumbnails();
            updateLayersUI();
        };

        li.onclick = () => { selectedLayerIndex = i; updateLayersUI(); pushHistory(); };
        const blendOptions = blendModes.map(m => `<option value="${m.value}" ${l.blendMode === m.value ? 'selected' : ''}>${m.label}</option>`).join('');
        li.innerHTML = `
            <div class="layer-main-info"><div class="layer-thumbnail" style="background-image:url(${l.thumbData});background-size:cover"></div><div class="layer-identity"><input type="text" class="layer-name-input" value="${l.name}"><select class="layer-blend-select">${blendOptions}</select></div></div>
            <div class="layer-controls">
                <input type="range" class="layer-opacity-slider" min="0" max="100" value="${l.opacity * 100}">
                <div class="layer-buttons">
                    <button class="mini-tool-btn vis-btn ${!l.visible ? 'status-invisible' : ''}"><img src="${l.visible ? 'simbolo ojo abierto.png' : 'simbolo ojo cerrado.png'}"></button>
                    <button class="mini-tool-btn merge-btn"><img src="simbolo descargar.png"></button>
                    <button class="mini-tool-btn alpha-btn ${l.alphaLocked ? 'status-alpha' : ''}"><img src="Simbolo alpha.png"></button>
                    <button class="mini-tool-btn clip-btn ${l.clippingMask ? 'status-clipping' : ''}"><img src="Simbolo mascara de recorte.png"></button>
                    <button class="mini-tool-btn delete-btn">×</button>
                </div>
            </div>`;
        li.querySelector('.layer-name-input').onchange = e => { l.name = e.target.value; updateLayersUI(); }; li.querySelector('.layer-name-input').onclick = e => e.stopPropagation();
        li.querySelector('.layer-blend-select').onchange = e => { l.blendMode = e.target.value; updateLayersUI(); }; li.querySelector('.layer-blend-select').onclick = e => e.stopPropagation();
        li.querySelector('.layer-opacity-slider').oninput = e => { l.opacity = e.target.value / 100; updateLayersUI(); }; li.querySelector('.layer-opacity-slider').addEventListener('pointerup', () => { pushHistory(); }); li.querySelector('.layer-opacity-slider').onclick = e => e.stopPropagation();
        li.querySelector('.vis-btn').onclick = e => { e.stopPropagation(); l.visible = !l.visible; updateLayersUI(); };
        li.querySelector('.alpha-btn').onclick = e => { e.stopPropagation(); l.alphaLocked = !l.alphaLocked; updateLayersUI(); };
        li.querySelector('.clip-btn').onclick = e => { e.stopPropagation(); l.clippingMask = !l.clippingMask; updateLayersUI(); pushHistory(); };
        li.querySelector('.merge-btn').onclick = e => { e.stopPropagation(); mergeLayerDown(i); };
        li.querySelector('.delete-btn').onclick = e => { e.stopPropagation(); if (layers.length > 1) { layers.splice(i, 1); selectedLayerIndex = Math.max(0, selectedLayerIndex - 1); updateLayersUI(); pushHistory(); } };
        layersList.appendChild(li);
    }
}

// ─────────────────────────────────────────────────────────────
//  BUCKET FILL
// ─────────────────────────────────────────────────────────────
function executeBucket(worldX, worldY) {
    const startX = Math.floor(worldX); const startY = Math.floor(worldY);
    if (startX < 0 || startX >= paperWidth || startY < 0 || startY >= paperHeight) return;
    let refData;
    if (bucketMode === 'lienzo') {
        const temp = document.createElement('canvas'); temp.width = paperWidth; temp.height = paperHeight; const tc = temp.getContext('2d');
        layers.forEach(l => { if (l.visible) { tc.save(); tc.globalAlpha = l.opacity; tc.globalCompositeOperation = l.blendMode; tc.drawImage(l.canvas, 0, 0); tc.restore(); } });
        refData = tc.getImageData(0, 0, paperWidth, paperHeight);
    } else { refData = layers[selectedLayerIndex].ctx.getImageData(0, 0, paperWidth, paperHeight); }
    const targetColor = getPixel(refData, startX, startY);
    const fillRGBA = hexToRgbaArray(selectedColor, Math.floor(brushOpacity * 255));
    if (colorsMatch(targetColor, fillRGBA)) return;
    const width = paperWidth; const height = paperHeight;
    const visited = new Uint8Array(width * height); const stack = [[startX, startY]];
    const layerCtx = layers[selectedLayerIndex].ctx;
    const imgData = layerCtx.getImageData(0, 0, paperWidth, paperHeight); const resultPixels = imgData.data;
    while (stack.length > 0) {
        const [x, y] = stack.pop(); if (x < 0 || x >= width || y < 0 || y >= height) continue;
        const pos = y * width + x; if (visited[pos]) continue;
        if (colorsMatch(getPixel(refData, x, y), targetColor)) {
            const pp = pos * 4; resultPixels[pp] = fillRGBA[0]; resultPixels[pp + 1] = fillRGBA[1]; resultPixels[pp + 2] = fillRGBA[2]; resultPixels[pp + 3] = fillRGBA[3];
            visited[pos] = 1; stack.push([x + 1, y], [x - 1, y], [x, y + 1], [x, y - 1]);
        }
    }
    layerCtx.putImageData(imgData, 0, 0); updateThumbnails(); updateLayersUI();
    pushHistory(); // snapshot AFTER bucket fill committed
}
function getPixel(imgData, x, y) { const pos = (y * imgData.width + x) * 4; return [imgData.data[pos], imgData.data[pos + 1], imgData.data[pos + 2], imgData.data[pos + 3]]; }
function colorsMatch(c1, c2, t = 5) { return Math.abs(c1[0] - c2[0]) < t && Math.abs(c1[1] - c2[1]) < t && Math.abs(c1[2] - c2[2]) < t && Math.abs(c1[3] - c2[3]) < t; }
function hexToRgbaArray(hex, a) { return [parseInt(hex.slice(1, 3), 16), parseInt(hex.slice(3, 5), 16), parseInt(hex.slice(5, 7), 16), a]; }

// ─────────────────────────────────────────────────────────────
//  POINTER EVENTS
// ─────────────────────────────────────────────────────────────
function screenToWorld(sx, sy) {
    const dx = sx - canvas.width / 2 - viewPosX; const dy = sy - canvas.height / 2 - viewPosY;
    const cos = Math.cos(-viewRotation); const sin = Math.sin(-viewRotation);
    const x2 = dx * cos - dy * sin; const y2 = dx * sin + dy * cos;
    return { x: x2 / viewScale + paperWidth / 2, y: y2 / viewScale + paperHeight / 2 };
}

/** Apply cursor visibility based on cursorMode and current drawing state */
function applyCursor(drawing) {
    if (cursorMode === 'auto' && drawing) {
        canvas.style.cursor = 'none';
    } else {
        canvas.style.cursor = '';
    }
}

function handlePointerDown(e) {
    if (e.target !== canvas) return;
    if (e.button !== 0 && e.pointerType === 'mouse') return;
    canvas.setPointerCapture(e.pointerId);
    isDrawing = true;
    applyCursor(true);
    sctx.clearRect(0, 0, strokeCanvas.width, strokeCanvas.height);
    lassoPath = []; lassoSelPath = [];
    const world = screenToWorld(e.offsetX, e.offsetY);
    lastX = world.x; lastY = world.y;
    const rawP = (e.pressure === 0.5 && e.pointerType !== 'mouse') ? 0.1 : e.pressure || 0.1;
    lastPressure = rawP; smoothedPressure = rawP;

    if (currentTool === 'rotate') { rotationPivot = { sx: e.offsetX, sy: e.offsetY, startRotation: viewRotation }; }
    else if (isResizingCanvas) {
        const handle = getCanvasResizeHandle(world.x, world.y);
        if (handle) {
            resizeActiveHandle = handle;
            resizeStartMouse = { x: world.x, y: world.y };
            resizeStartDim = { w: resizePreviewW, h: resizePreviewH };
            canvas.setPointerCapture(e.pointerId);
        }
        // Don't activate normal drawing during resize mode
        isDrawing = false;
        e.preventDefault();
        return;
    }
    else if (currentTool === 'bucket') { executeBucket(world.x, world.y); }
    else if (currentTool === 'lazo-sel' || currentTool === 'lazo-des') {
        lassoSelStartX = world.x; lassoSelStartY = world.y;
        if (lassoSelMode === 'libre') lassoSelPath = [{ x: world.x, y: world.y }];
        else lassoSelPath = squarePath(world.x, world.y, world.x, world.y);
    }
    else if (currentTool === 'modify-sel') {
        if (!modSelInitialized && hasSelection) initModifySelection();
        if (modSelInitialized) {
            const handle = getModifyHandle(world.x, world.y);
            if (handle) { modSelHandle = handle; modSelDragStart = { wx: world.x, wy: world.y }; modSelOrigBounds = { ...modSelBounds }; modSelActive = true; }
        }
    }
    else if (currentTool === 'pincel') {
        if (currentBrush.isLasso) {
            lassoPath.push({ x: world.x, y: world.y });
        } else if (currentBrush.isShape) {
            // Save the anchor point; clear the stroke canvas for a fresh preview
            shapeStartX = world.x; shapeStartY = world.y;
            sctx.clearRect(0, 0, strokeCanvas.width, strokeCanvas.height);
        } else {
            drawPoint(lastX, lastY, smoothedPressure);
        }
    }
    e.preventDefault();
}

function handlePointerMove(e) {
    // Canvas resize drag is independent of isDrawing
    if (isResizingCanvas) {
        // Update cursor based on which handle is hovered
        if (!resizeActiveHandle) {
            const world2 = screenToWorld(e.offsetX, e.offsetY);
            const hov = getCanvasResizeHandle(world2.x, world2.y);
            const cursorMap = { tl: 'nwse-resize', tc: 'ns-resize', tr: 'nesw-resize', ml: 'ew-resize', mr: 'ew-resize', bl: 'nesw-resize', bc: 'ns-resize', br: 'nwse-resize' };
            canvas.style.cursor = hov ? (cursorMap[hov] || 'crosshair') : 'default';
        }
        if (resizeActiveHandle) {
            e.preventDefault();
            const world = screenToWorld(e.offsetX, e.offsetY);
            const dx = world.x - resizeStartMouse.x;
            const dy = world.y - resizeStartMouse.y;
            const res = applyCanvasResizeDrag(dx, dy, resizeActiveHandle, resizeStartDim.w, resizeStartDim.h);
            resizePreviewW = res.nw;
            resizePreviewH = res.nh;
            // Sync back to inputs
            document.getElementById('resize-width').value = resizePreviewW;
            document.getElementById('resize-height').value = resizePreviewH;
        }
        return;
    }

    if (!isDrawing) return;
    e.preventDefault();
    const world = screenToWorld(e.offsetX, e.offsetY);

    if (currentTool === 'pan') { viewPosX += e.movementX; viewPosY += e.movementY; }
    else if (currentTool === 'zoom') { viewScale *= 1 + e.movementY * -0.005; viewScale = Math.max(0.01, Math.min(20, viewScale)); }
    else if (currentTool === 'rotate') { viewRotation = rotationPivot.startRotation + (e.offsetX - rotationPivot.sx) * 0.01; resetRotationBtn.classList.remove('hidden'); }
    else if (currentTool === 'lazo-sel' || currentTool === 'lazo-des') {
        if (lassoSelMode === 'libre') lassoSelPath.push({ x: world.x, y: world.y });
        else lassoSelPath = squarePath(lassoSelStartX, lassoSelStartY, world.x, world.y);
    }
    else if (currentTool === 'modify-sel' && modSelActive && modSelHandle) {
        const dx = world.x - modSelDragStart.wx; const dy = world.y - modSelDragStart.wy;
        modSelBounds = applyModifyDrag(dx, dy, modSelHandle, modSelOrigBounds);
    }
    else if (currentTool === 'pincel') {
        const [cX, cY] = [world.x, world.y];
        if (currentBrush.isLasso) {
            lassoPath.push({ x: world.x, y: world.y });
        } else if (currentBrush.isShape) {
            // Live preview: clear strokeCanvas and redraw shape from anchor to cursor
            let ex = cX, ey = cY;
            if (e.shiftKey) [ex, ey] = constrainShape(shapeStartX, shapeStartY, cX, cY);
            sctx.clearRect(0, 0, strokeCanvas.width, strokeCanvas.height);
            drawShapeOnCtx(sctx, shapeStartX, shapeStartY, ex, ey);
        } else {
            smoothedPressure += ((e.pressure || 0.1) - smoothedPressure) * 0.3;
            const dist = Math.hypot(cX - lastX, cY - lastY); const step = Math.max(0.2, baseBrushSize * 0.5 * brushSpacing); const steps = Math.floor(dist / step);
            for (let i = 0; i <= steps; i++) { const t = steps === 0 ? 1 : i / steps; drawPoint(lastX + (cX - lastX) * t, lastY + (cY - lastY) * t, lastPressure + (smoothedPressure - lastPressure) * t); }
            [lastX, lastY, lastPressure] = [cX, cY, smoothedPressure];
        }
    }
}

function handlePointerUp(e) {
    // Release canvas resize drag regardless of isDrawing
    if (resizeActiveHandle) {
        try { canvas.releasePointerCapture(e.pointerId); } catch(_) {}
        resizeActiveHandle = null;
        canvas.style.cursor = 'default';
        e.preventDefault();
        return;
    }

    if (!isDrawing) return;
    canvas.releasePointerCapture(e.pointerId);
    applyCursor(false);

    if (currentTool === 'lazo-sel') {
        if (lassoSelPath.length >= 3) {
            addPathToSelection(lassoSelPath);
            if (clearSelBtn) clearSelBtn.classList.remove('hidden');
            pushHistory(); // snapshot AFTER selection was added
        }
        lassoSelPath = [];
    }
    else if (currentTool === 'lazo-des') {
        if (lassoSelPath.length >= 3) {
            subtractPathFromSelection(lassoSelPath);
            pushHistory(); // snapshot AFTER selection was subtracted
        }
        lassoSelPath = [];
        if (!hasSelection && clearSelBtn) clearSelBtn.classList.add('hidden');
    }
    else if (currentTool === 'modify-sel') {
        modSelActive = false; modSelHandle = null;
        pushHistory(); // snapshot AFTER move/resize is settled
    }
    else if (currentTool === 'pincel') {
        if (currentBrush.isLasso) {
            executeLassoFill();
        } else if (currentBrush.isShape) {
            // Finalize shape onto strokeCanvas (apply shift-constrain on release too)
            const world = screenToWorld(e.offsetX, e.offsetY);
            let ex = world.x, ey = world.y;
            if (e.shiftKey) [ex, ey] = constrainShape(shapeStartX, shapeStartY, ex, ey);
            sctx.clearRect(0, 0, strokeCanvas.width, strokeCanvas.height);
            drawShapeOnCtx(sctx, shapeStartX, shapeStartY, ex, ey);

            // Commit to layer
            const l = layers[selectedLayerIndex];
            l.ctx.save();
            l.ctx.globalAlpha = brushOpacity;
            if (l.alphaLocked) l.ctx.globalCompositeOperation = 'source-atop';
            l.ctx.drawImage(strokeCanvas, 0, 0);
            l.ctx.restore();
            sctx.clearRect(0, 0, strokeCanvas.width, strokeCanvas.height);

            updateThumbnails(); updateLayersUI();
            pushHistory();
        } else if (currentBrush.useCompositing) {
            const l = layers[selectedLayerIndex]; l.ctx.save(); l.ctx.globalAlpha = brushOpacity;
            if (l.alphaLocked) l.ctx.globalCompositeOperation = 'source-atop';

            // Apply ghost layer blur if needed
            if ((currentBrush.id === 'aero-duro' || currentBrush.id === 'aero-suave') && currentBlur > 0) {
                l.ctx.filter = `blur(${currentBlur}px)`;
            }

            l.ctx.drawImage(strokeCanvas, 0, 0); l.ctx.restore();
            sctx.clearRect(0, 0, strokeCanvas.width, strokeCanvas.height);

            updateThumbnails(); updateLayersUI();
            pushHistory(); // snapshot AFTER stroke is committed to the layer
        } else {
            updateThumbnails(); updateLayersUI();
            pushHistory();
        }
    }

    isDrawing = false; lassoPath = [];
    if (currentTool === 'rotate') selectTool('pincel', lastBrushTool);
}

// ─────────────────────────────────────────────────────────────
//  BRUSH DRAWING
// ─────────────────────────────────────────────────────────────
function executeLassoFill() {
    if (lassoPath.length < 3) return;
    const l = layers[selectedLayerIndex]; l.ctx.save();
    if (currentBrush.isEraser) l.ctx.globalCompositeOperation = 'destination-out';
    else if (l.alphaLocked) l.ctx.globalCompositeOperation = 'source-atop';
    l.ctx.globalAlpha = brushOpacity; l.ctx.fillStyle = selectedColor;
    l.ctx.beginPath(); l.ctx.moveTo(lassoPath[0].x, lassoPath[0].y);
    lassoPath.forEach(p => l.ctx.lineTo(p.x, p.y)); l.ctx.closePath(); l.ctx.fill(); l.ctx.restore();
}
function drawPoint(x, y, pressure) {
    const size = baseBrushSize * (0.2 + pressure * 1.8); if (size <= 0) return;
    const l = layers[selectedLayerIndex];
    if (currentBrush.useCompositing) { sctx.save(); if (currentBrush.isEraser) sctx.globalCompositeOperation = 'destination-out'; renderStamp(sctx, x, y, size, 1.0); sctx.restore(); }
    else { l.ctx.save(); if (currentBrush.isEraser) l.ctx.globalCompositeOperation = 'destination-out'; else if (l.alphaLocked) l.ctx.globalCompositeOperation = 'source-atop'; renderStamp(l.ctx, x, y, size, brushOpacity * 0.4); l.ctx.restore(); }
}

// ─────────────────────────────────────────────────────────────
//  SHAPE DRAWING HELPERS
// ─────────────────────────────────────────────────────────────
/**
 * Constrain endpoint: line → 45° snap, rect/ellipse → equal sides
 */
function constrainShape(x1, y1, x2, y2) {
    const type = currentBrush.shapeType;
    if (type === 'line') {
        const dx = x2 - x1, dy = y2 - y1;
        const angle = Math.atan2(dy, dx);
        const snapped = Math.round(angle / (Math.PI / 4)) * (Math.PI / 4);
        const dist = Math.hypot(dx, dy);
        return [x1 + Math.cos(snapped) * dist, y1 + Math.sin(snapped) * dist];
    } else {
        const dx = x2 - x1, dy = y2 - y1;
        const side = Math.min(Math.abs(dx), Math.abs(dy));
        return [x1 + Math.sign(dx) * side, y1 + Math.sign(dy) * side];
    }
}

/**
 * Draw the current shape into a given context (used for live preview on strokeCanvas)
 */
function drawShapeOnCtx(tctx, x1, y1, x2, y2) {
    const type = currentBrush.shapeType;
    tctx.save();
    tctx.strokeStyle = selectedColor;
    tctx.fillStyle = selectedColor;
    tctx.lineWidth = Math.max(1, baseBrushSize);
    tctx.lineCap = 'round';
    tctx.lineJoin = 'round';

    if (type === 'line') {
        tctx.beginPath();
        tctx.moveTo(x1, y1);
        tctx.lineTo(x2, y2);
        tctx.stroke();
    } else if (type === 'rect') {
        const rx = Math.min(x1, x2), ry = Math.min(y1, y2);
        const rw = Math.abs(x2 - x1), rh = Math.abs(y2 - y1);
        if (rw < 1 || rh < 1) { tctx.restore(); return; }
        if (shapeFill) tctx.fillRect(rx, ry, rw, rh);
        else tctx.strokeRect(rx, ry, rw, rh);
    } else if (type === 'ellipse') {
        const cx = (x1 + x2) / 2, cy = (y1 + y2) / 2;
        const radiusX = Math.max(1, Math.abs(x2 - x1) / 2);
        const radiusY = Math.max(1, Math.abs(y2 - y1) / 2);
        tctx.beginPath();
        tctx.ellipse(cx, cy, radiusX, radiusY, 0, 0, Math.PI * 2);
        if (shapeFill) tctx.fill();
        else tctx.stroke();
    }
    tctx.restore();
}
function updateTintedTexture() {
    if (!airbrushTexture) return;
    tintedAirbrushCanvas.width = airbrushTexture.width;
    tintedAirbrushCanvas.height = airbrushTexture.height;
    tactx.clearRect(0, 0, tintedAirbrushCanvas.width, tintedAirbrushCanvas.height);

    tactx.save();
    // Soft airbrush still uses the noise texture, but we can apply its own blur if desired.
    // However, the user said the blur slider also affects the ghost layer.
    // We'll keep the baked blur at 0 for the texture itself to avoid double-blurring
    // if the ghost layer is already blurred.
    tactx.drawImage(airbrushTexture, 0, 0);
    tactx.restore();

    tactx.globalCompositeOperation = 'source-in';

    tactx.fillStyle = selectedColor;
    tactx.fillRect(0, 0, tintedAirbrushCanvas.width, tintedAirbrushCanvas.height);
}
function renderStamp(tctx, x, y, size, alpha) {
    if (currentBrush.useTexture && airbrushTexture) {
        tctx.save();
        tctx.globalAlpha = alpha;
        tctx.drawImage(tintedAirbrushCanvas, x - size, y - size, size * 2, size * 2);
        tctx.restore();
    }
    else { const g = tctx.createRadialGradient(x, y, size * currentBrush.hardness, x, y, size); g.addColorStop(0, hexToRgba(selectedColor, alpha)); g.addColorStop(1, hexToRgba(selectedColor, 0)); tctx.fillStyle = g; tctx.beginPath(); tctx.arc(x, y, size, 0, Math.PI * 2); tctx.fill(); }
}



function hexToRgba(hex, alpha) { const r = parseInt(hex.slice(1, 3), 16), g = parseInt(hex.slice(3, 5), 16), b = parseInt(hex.slice(5, 7), 16); return `rgba(${r},${g},${b},${alpha})`; }

// ─────────────────────────────────────────────────────────────
//  RENDER LOOP
// ─────────────────────────────────────────────────────────────
// Marching ants dash offset
let dashOffset = 0;

function render() {
    dashOffset = (dashOffset - 0.3) % 20;
    ctx.clearRect(0, 0, canvas.width, canvas.height); ctx.save();
    ctx.translate(canvas.width / 2 + viewPosX, canvas.height / 2 + viewPosY);
    ctx.rotate(viewRotation); ctx.scale(viewScale, viewScale);
    ctx.translate(-paperWidth / 2, -paperHeight / 2);

    // Paper bg
    ctx.save(); ctx.shadowColor = 'rgba(0,0,0,0.5)'; ctx.shadowBlur = 40; ctx.shadowOffsetX = 10; ctx.shadowOffsetY = 20;
    ctx.fillStyle = transparentBG ? checkerPattern : '#ffffff'; ctx.fillRect(0, 0, paperWidth, paperHeight); ctx.restore();

    // Layers
    let i = 0;
    while (i < layers.length) {
        const l = layers[i];
        
        // Check if there are layers above clipping to this one
        let next = i + 1;
        let groupCount = 0;
        while (next < layers.length && layers[next].clippingMask) {
            next++;
            groupCount++;
        }

        if (groupCount > 0) {
            // We have a clipping group starting at index i
            let group = [l];
            for (let k = i + 1; k < next; k++) {
                if (layers[k].visible) group.push(layers[k]);
            }
            
            // If the base layer is invisible, the whole clipped stack is invisible
            if (!l.visible) {
                i = next;
                continue;
            }

            // ── Clipping mask group render ──
            gctx.clearRect(0, 0, paperWidth, paperHeight);
            // Draw the base layer (group[0] = CAPA B) 
            gctx.save();
            gctx.globalAlpha = group[0].opacity;
            gctx.globalCompositeOperation = group[0].blendMode;
            gctx.drawImage(group[0].canvas, 0, 0);
            gctx.restore();

            // For each clipping layer
            for (let k = 1; k < group.length; k++) {
                mctx.clearRect(0, 0, paperWidth, paperHeight);
                mctx.globalCompositeOperation = 'source-over';
                mctx.save();
                mctx.globalAlpha = group[k].opacity;
                mctx.drawImage(group[k].canvas, 0, 0);
                mctx.restore();
                
                mctx.globalCompositeOperation = 'destination-in';
                mctx.drawImage(group[0].canvas, 0, 0);
                mctx.globalCompositeOperation = 'source-over'; // reset
                
                gctx.save();
                gctx.globalCompositeOperation = group[k].blendMode;
                gctx.drawImage(maskBuffer, 0, 0);
                gctx.restore();
            }

            // Live stroke preview inside a clipping group
            const actInGrp = group.findIndex(layer => layer === layers[selectedLayerIndex]);
            if (actInGrp !== -1 && isDrawing && currentBrush.useCompositing && !currentBrush.isLasso) {
                mctx.clearRect(0, 0, paperWidth, paperHeight);
                mctx.globalCompositeOperation = 'source-over';
                mctx.save();
                mctx.globalAlpha = brushOpacity;
                if ((currentBrush.id === 'aero-duro' || currentBrush.id === 'aero-suave') && currentBlur > 0) {
                    mctx.filter = `blur(${currentBlur}px)`;
                }
                mctx.drawImage(strokeCanvas, 0, 0);
                mctx.restore();
                mctx.filter = 'none';

                if (actInGrp > 0) {
                    mctx.globalCompositeOperation = 'destination-in';
                    mctx.drawImage(group[0].canvas, 0, 0);
                    mctx.globalCompositeOperation = 'source-over';
                } else if (layers[selectedLayerIndex].alphaLocked) {
                    mctx.globalCompositeOperation = 'destination-in';
                    mctx.drawImage(layers[selectedLayerIndex].canvas, 0, 0);
                    mctx.globalCompositeOperation = 'source-over';
                }
                gctx.save();
                gctx.globalCompositeOperation = layers[selectedLayerIndex].blendMode;
                gctx.drawImage(maskBuffer, 0, 0);
                gctx.restore();
            }

            ctx.drawImage(groupCanvas, 0, 0);
            i = next;
        } else {
            // No clipping mask, just normal render
            if (l.visible) {
                ctx.save();
                ctx.globalAlpha = l.opacity;
                ctx.globalCompositeOperation = l.blendMode;
                ctx.drawImage(l.canvas, 0, 0);
                
                if (i === selectedLayerIndex && isDrawing && currentBrush.useCompositing && !currentBrush.isLasso) {
                    mctx.clearRect(0, 0, paperWidth, paperHeight);
                    mctx.globalCompositeOperation = 'source-over';
                    mctx.save();
                    mctx.globalAlpha = brushOpacity;
                    if ((currentBrush.id === 'aero-duro' || currentBrush.id === 'aero-suave') && currentBlur > 0) {
                        mctx.filter = `blur(${currentBlur}px)`;
                    }
                    mctx.drawImage(strokeCanvas, 0, 0);
                    mctx.restore();
                    mctx.filter = 'none';
                    if (l.alphaLocked) {
                        mctx.globalCompositeOperation = 'destination-in';
                        mctx.drawImage(l.canvas, 0, 0);
                        mctx.globalCompositeOperation = 'source-over';
                    }
                    ctx.drawImage(maskBuffer, 0, 0);
                }
                ctx.restore();
            }
            i++;
        }
    }

    // ── Draw floating modify preview ──
    if (currentTool === 'modify-sel' && modSelInitialized && modSelCanvas && modSelBounds) {
        const b = modSelBounds;
        ctx.save();
        // Clip to paper bounds so the preview is cut off at the canvas edge
        ctx.beginPath();
        ctx.rect(0, 0, paperWidth, paperHeight);
        ctx.clip();
        ctx.drawImage(modSelCanvas, b.x, b.y, b.w, b.h);
        // Bounding box (also clipped)
        ctx.strokeStyle = '#ff00ff'; ctx.lineWidth = 2 / viewScale; ctx.setLineDash([]);
        ctx.strokeRect(b.x, b.y, b.w, b.h);
        ctx.restore();
        // Handles: drawn outside clip so they remain selectable even near edges
        ctx.save();
        const hr = HANDLE_R / viewScale;
        const handlePositions = [
            [b.x, b.y], [b.x + b.w / 2, b.y], [b.x + b.w, b.y],
            [b.x, b.y + b.h / 2], [b.x + b.w, b.y + b.h / 2],
            [b.x, b.y + b.h], [b.x + b.w / 2, b.y + b.h], [b.x + b.w, b.y + b.h],
        ];
        handlePositions.forEach(([hx, hy]) => {
            ctx.fillStyle = 'white'; ctx.beginPath(); ctx.arc(hx, hy, hr, 0, Math.PI * 2); ctx.fill();
            ctx.strokeStyle = '#ff00ff'; ctx.lineWidth = 2 / viewScale; ctx.setLineDash([]); ctx.stroke();
        });
        ctx.restore();
    }
    
    // ── Draw canvas resize preview ──
    if (isResizingCanvas) {
        const nw = resizePreviewW;
        const nh = resizePreviewH;

        // Compute anchor offset: where old content will land in the new canvas
        const dw = nw - paperWidth;
        const dh = nh - paperHeight;
        const col = resizeAnchor[1]; // l, c, r
        const row = resizeAnchor[0]; // t, m, b
        let ox = 0, oy = 0;
        if (col === 'c') ox = Math.round(dw / 2);
        else if (col === 'r') ox = dw;
        if (row === 'm') oy = Math.round(dh / 2);
        else if (row === 'b') oy = dh;

        ctx.save();

        // Shadow zone: area that will be empty in new canvas (outside current content)
        ctx.fillStyle = 'rgba(0, 102, 255, 0.08)';
        ctx.fillRect(-ox, -oy, nw, nh);

        // Existing canvas position highlight (where old content will be)
        ctx.strokeStyle = 'rgba(0,0,0,0.2)';
        ctx.lineWidth = 1 / viewScale;
        ctx.setLineDash([4 / viewScale, 4 / viewScale]);
        ctx.strokeRect(-ox, -oy, nw, nh);

        // New canvas border (bold blue, animated-ish)
        ctx.strokeStyle = '#0066ff';
        ctx.lineWidth = 2 / viewScale;
        ctx.setLineDash([]);
        ctx.strokeRect(-ox, -oy, nw, nh);

        // Size label
        ctx.fillStyle = 'rgba(0, 102, 255, 0.9)';
        ctx.font = `bold ${14 / viewScale}px Outfit, sans-serif`;
        ctx.textAlign = 'center';
        ctx.fillText(`${nw} × ${nh}`, -ox + nw / 2, -oy - 8 / viewScale);

        // Handles on the new canvas boundary
        const hr = HANDLE_R / viewScale;
        const handlePositions = [
            [-ox, -oy], [-ox + nw / 2, -oy], [-ox + nw, -oy],
            [-ox, -oy + nh / 2], [-ox + nw, -oy + nh / 2],
            [-ox, -oy + nh], [-ox + nw / 2, -oy + nh], [-ox + nw, -oy + nh],
        ];
        handlePositions.forEach(([hx, hy]) => {
            ctx.fillStyle = 'white';
            ctx.beginPath(); ctx.arc(hx, hy, hr, 0, Math.PI * 2); ctx.fill();
            ctx.strokeStyle = '#0066ff';
            ctx.lineWidth = 2 / viewScale;
            ctx.setLineDash([]);
            ctx.stroke();
        });

        ctx.restore();
    }

    // ── Draw lasso fill/erase preview ──
    if (isDrawing && currentBrush.isLasso && lassoPath.length > 1) {
        ctx.save();
        ctx.globalAlpha = brushOpacity * 0.5;
        ctx.fillStyle = currentBrush.isEraser ? 'rgba(255,0,0,0.4)' : selectedColor;
        ctx.beginPath(); ctx.moveTo(lassoPath[0].x, lassoPath[0].y); lassoPath.forEach(p => ctx.lineTo(p.x, p.y)); ctx.closePath(); ctx.fill();
        ctx.globalAlpha = 1.0; ctx.strokeStyle = currentBrush.lassoColor; ctx.lineWidth = 2 / viewScale; ctx.setLineDash([5 / viewScale, 5 / viewScale]);
        ctx.beginPath(); ctx.moveTo(lassoPath[0].x, lassoPath[0].y); lassoPath.forEach(p => ctx.lineTo(p.x, p.y)); ctx.closePath(); ctx.stroke();
        ctx.restore();
    }

    // ── Draw lasso selection stroke in progress ──
    if ((currentTool === 'lazo-sel' || currentTool === 'lazo-des') && isDrawing && lassoSelPath.length > 1) {
        ctx.save();
        ctx.fillStyle = currentTool === 'lazo-sel' ? 'rgba(255,0,255,0.15)' : 'rgba(255,0,0,0.15)';
        ctx.beginPath(); ctx.moveTo(lassoSelPath[0].x, lassoSelPath[0].y); lassoSelPath.forEach(p => ctx.lineTo(p.x, p.y)); ctx.closePath(); ctx.fill();
        ctx.strokeStyle = currentTool === 'lazo-sel' ? '#ff00ff' : '#ff0000';
        ctx.lineWidth = 2 / viewScale; ctx.setLineDash([5 / viewScale, 5 / viewScale]);
        ctx.beginPath(); ctx.moveTo(lassoSelPath[0].x, lassoSelPath[0].y); lassoSelPath.forEach(p => ctx.lineTo(p.x, p.y)); ctx.closePath(); ctx.stroke();
        ctx.restore();
    }

    // ── Draw persistent selection mask outline (marching ants) ──
    if (hasSelection && selectionCanvas) {
        ctx.save();

        // Extract the border of the selection mask to create the marching ants outline
        const selOutlineCanvas = document.createElement('canvas');
        selOutlineCanvas.width = paperWidth; selOutlineCanvas.height = paperHeight;
        const soc = selOutlineCanvas.getContext('2d');

        soc.drawImage(selectionCanvas, 1, 0);
        soc.drawImage(selectionCanvas, -1, 0);
        soc.drawImage(selectionCanvas, 0, 1);
        soc.drawImage(selectionCanvas, 0, -1);
        soc.globalCompositeOperation = 'destination-out';
        soc.drawImage(selectionCanvas, 0, 0);

        soc.globalCompositeOperation = 'source-in';
        soc.fillStyle = '#ff00ff';
        soc.fillRect(0, 0, paperWidth, paperHeight);

        ctx.save();
        ctx.setLineDash([7 / viewScale, 5 / viewScale]);
        ctx.lineDashOffset = dashOffset / viewScale;
        ctx.drawImage(selOutlineCanvas, 0, 0);
        ctx.restore();

        ctx.restore();
    }

    ctx.restore();

    // Rotation pivot dot
    if (currentTool === 'rotate' && isDrawing) {
        ctx.beginPath(); ctx.arc(rotationPivot.sx, rotationPivot.sy, 5, 0, Math.PI * 2);
        ctx.fillStyle = 'rgba(0,0,0,0.4)'; ctx.fill(); ctx.strokeStyle = 'white'; ctx.stroke();
    }
    requestAnimationFrame(render);
}

// ─────────────────────────────────────────────────────────────
//  TOOL MANAGEMENT
// ─────────────────────────────────────────────────────────────
function resetRotation() {
    viewRotation = 0;
    if (resetRotationBtn) resetRotationBtn.classList.add('hidden');
    selectTool('pincel', lastBrushTool);
}

/** Sync the UI sliders/labels to match the current brush's stored values */
function syncBrushUI() {
    baseBrushSize = currentBrush.size;
    brushOpacity = currentBrush.opacity;
    currentBlur = currentBrush.blur;

    sizeSlider.value = baseBrushSize;
    sizeValue.textContent = baseBrushSize;

    const opPct = Math.round(brushOpacity * 100);
    opacitySlider.value = opPct;
    opacityValue.textContent = opPct + '%';
    if (eyeIcon) eyeIcon.src = opPct === 0 ? 'simbolo ojo cerrado.png' : 'simbolo ojo abierto.png';

    blurSlider.value = currentBlur;
    if (blurValueLabel) blurValueLabel.textContent = currentBlur;
}

function selectTool(id, name) {
    if (currentTool === 'modify-sel' && id !== 'modify-sel' && modSelInitialized) commitModifySelection();
    
    if (isResizingCanvas) {
        isResizingCanvas = false;
        resizePanel.classList.add('hidden');
    }

    if (id === 'pincel') {
        currentTool = 'pincel'; lastBrushTool = name;
        if (activeToolIndicator) activeToolIndicator.textContent = name;
        document.querySelector('.tool-btn.active')?.classList.remove('active');
        document.getElementById('btn-brush')?.classList.add('active');
        const b = brushTypesData.find(x => x.name === name);
        if (b) currentBrush = b;
    } else {
        currentTool = id;
        if (activeToolIndicator) activeToolIndicator.textContent = name;
    }
    showSelectionButtons(id);

    // Load this brush's remembered size / opacity / blur into the UI
    syncBrushUI();

    // Show/Hide Blur slider
    if (id === 'pincel' && (currentBrush.id === 'aero-duro' || currentBrush.id === 'aero-suave')) {
        blurSettingsContainer.classList.remove('hidden');
    } else {
        blurSettingsContainer.classList.add('hidden');
    }

    updateTintedTexture();
}



function handleGlobalShortcuts(e) {
    if (e.target.tagName === 'INPUT' || e.target.tagName === 'SELECT') return;
    const key = e.key.toLowerCase();
    const ms = (mainShortcutInput?.value || '').toLowerCase();
    const bs = (brushShortcutInput?.value || '').toLowerCase();
    const ls = (layersShortcutInput?.value || '').toLowerCase();
    const cs = (colorsShortcutInput?.value || '').toLowerCase();
    const cfs = (configShortcutInput?.value || '').toLowerCase();

    if (key === ms && ms !== '') { toggleMenu(multiToolMenu); return; }
    if (key === bs && bs !== '') { toggleMenu(brushTypeMenu); return; }
    if (key === ls && ls !== '') { toggleMenu(layersMenu); return; }
    if (key === cs && cs !== '') { toggleMenu(colorsMenu); return; }
    if (key === cfs && cfs !== '') { toggleMenu(configMenu); return; }

    if (e.ctrlKey && key === 'c') { e.preventDefault(); copyToClipboard(); return; }
    if (e.ctrlKey && key === 'v') { e.preventDefault(); pasteFromClipboard(); return; }
    if (e.ctrlKey && (key === 'z')) { e.preventDefault(); undo(); return; }
    if (e.ctrlKey && (key === 'y' || (e.shiftKey && key === 'z'))) { e.preventDefault(); redo(); return; }
    if (e.key === 'Escape' && hasSelection) { clearSelection(); return; }
    const t = toolsData.find(x => (x.shortcut || '').toLowerCase() === key); if (t) selectTool(t.id, t.name);
    const bt = brushTypesData.find(x => (x.shortcut || '').toLowerCase() === key); if (bt) selectTool('pincel', bt.name);
}
function toggleMenu(m) {
    const menus = [multiToolMenu, brushTypeMenu, layersMenu, colorsMenu, mainActionsMenu, saveSlotsMenu, configMenu, filtersMenu];
    if (!m) { menus.forEach(x => x?.classList.add('hidden')); return; }
    const isHidden = m.classList.contains('hidden');
    menus.forEach(x => { if (x && x !== m) x.classList.add('hidden'); });
    if (isHidden) m.classList.remove('hidden'); else m.classList.add('hidden');
}
function setupMultiToolMenu() { if (toolsList) renderMenuList(toolsList, toolsData, 'tool'); }
function setupBrushMenu() { if (brushTypesList) renderMenuList(brushTypesList, brushTypesData, 'brush'); }
function renderMenuList(cont, data, type) {
    cont.innerHTML = '';
    data.forEach(item => {
        const li = document.createElement('li'); li.className = 'tool-item';
        li.innerHTML = `<span>${item.name}</span><input type="text" class="tool-shortcut-input" maxlength="1" value="${item.shortcut || ''}">`;
        li.onclick = e => { if (e.target.tagName !== 'INPUT') { type === 'brush' ? selectTool('pincel', item.name) : selectTool(item.id, item.name); } };
        li.querySelector('input').onkeydown = e => { if (e.key.length === 1) { e.preventDefault(); checkAndAssignShortcut(item, e.key.toLowerCase(), type); } };
        cont.appendChild(li);
    });
}
function checkAndAssignShortcut(item, key, type) {
    const ms = (mainShortcutInput?.value || '').toLowerCase(), bs = (brushShortcutInput?.value || '').toLowerCase(), ls = (layersShortcutInput?.value || '').toLowerCase(), cs = (colorsShortcutInput?.value || '').toLowerCase();
    let conflict = key === ms ? 'Atajo Principal' : key === bs ? 'Atajo Pincel' : key === ls ? 'Atajo Capas' : key === cs ? 'Atajo Colores' : null;
    const tc = toolsData.find(t => (t.shortcut || '').toLowerCase() === key && t !== item);
    const bc = brushTypesData.find(b => (b.shortcut || '').toLowerCase() === key && b !== item);
    if (tc) conflict = tc.name; else if (bc) conflict = bc.name;
    if (conflict) {
        if (confirm(`La tecla "${key.toUpperCase()}" ya está siendo usada por "${conflict}".`)) {
            if (key === ms && mainShortcutInput) mainShortcutInput.value = ''; if (key === bs && brushShortcutInput) brushShortcutInput.value = '';
            if (key === ls && layersShortcutInput) layersShortcutInput.value = ''; if (key === cs && colorsShortcutInput) colorsShortcutInput.value = '';
            if (tc) tc.shortcut = ''; else if (bc) bc.shortcut = ''; item.shortcut = key; saveShortcuts();
        }
    } else { item.shortcut = key; saveShortcuts(); }
    setupMultiToolMenu(); setupBrushMenu();
}
function saveShortcuts() {
    localStorage.setItem('illustrator_state_v13', JSON.stringify({
        main: mainShortcutInput?.value || '', brushMenu: brushShortcutInput?.value || '',
        layersMenu: layersShortcutInput?.value || '', colorsMenu: colorsShortcutInput?.value || '',
        config: configShortcutInput?.value || '',
        tools: toolsData.map(t => ({ id: t.id, shortcut: t.shortcut })),
        brushes: brushTypesData.map(b => ({ id: b.id, shortcut: b.shortcut }))
    }));
}
function loadShortcuts() {
    const saved = localStorage.getItem('illustrator_state_v13'); if (!saved) return;
    try {
        const s = JSON.parse(saved);
        if (mainShortcutInput) mainShortcutInput.value = s.main || '';
        if (brushShortcutInput) brushShortcutInput.value = s.brushMenu || '';
        if (layersShortcutInput) layersShortcutInput.value = s.layersMenu || '';
        if (colorsShortcutInput) colorsShortcutInput.value = s.colorsMenu || '';
        if (configShortcutInput) configShortcutInput.value = s.config || 'S';
        s.tools?.forEach(st => { const t = toolsData.find(x => x.id === st.id); if (t) t.shortcut = st.shortcut; });
        s.brushes?.forEach(sb => { const b = brushTypesData.find(x => x.id === sb.id); if (b) b.shortcut = sb.shortcut; });
    } catch (e) { }
}

document.querySelectorAll('.tool-btn').forEach(btn => {
    btn.addEventListener('click', () => {
        if (btn.id === 'btn-filters' || btn.id === 'btn-brush' || btn.id === 'btn-colors' || btn.id === 'btn-layers' || btn.id === 'btn-config' || btn.id === 'btn-main-actions' || btn.id === 'btn-multi') return;

        toggleMenu(null);
        document.querySelector('.tool-btn.active')?.classList.remove('active');
        btn.classList.add('active');
    });
});

// The specialized toggle logic for these buttons is now in init() or handled via id-specific listeners there.
// Specifically the brush button:
document.getElementById('btn-brush').onclick = () => {
    if (currentTool === 'pincel') toggleMenu(brushTypeMenu);
    else selectTool('pincel', lastBrushTool);
};
document.getElementById('btn-multi').onclick = () => toggleMenu(multiToolMenu);
document.getElementById('btn-layers').onclick = () => toggleMenu(layersMenu);
document.getElementById('btn-colors').onclick = () => toggleMenu(colorsMenu);


init();
