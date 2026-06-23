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

const blurSettingsContainer = document.getElementById('blur-settings-container');
const blurSlider = document.getElementById('brush-blur');
const blurValueLabel = document.getElementById('blur-value');
const eyedropperPreview = document.getElementById('eyedropper-preview');
const stabilizerSlider = document.getElementById('stabilizer-slider');
const stabilizerValue = document.getElementById('stabilizer-value');


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
const canvasPresetSelect = document.getElementById('canvas-preset-select');
const createBtn = document.getElementById('create-btn');
const importBtn = document.getElementById('import-btn');
const fileInput = document.getElementById('file-input');

// Handle canvas preset selection
if (canvasPresetSelect) {
    canvasPresetSelect.addEventListener('change', (e) => {
        const val = e.target.value;
        if (val !== 'custom') {
            const [w, h] = val.split('x');
            canvasWidthInput.value = w;
            canvasHeightInput.value = h;
        }
    });

    const resetToCustom = () => {
        canvasPresetSelect.value = 'custom';
    };
    canvasWidthInput.addEventListener('input', resetToCustom);
    canvasHeightInput.addEventListener('input', resetToCustom);
}

const swapDimensionsBtn = document.getElementById('swap-dimensions-btn');
if (swapDimensionsBtn) {
    swapDimensionsBtn.addEventListener('click', () => {
        const temp = canvasWidthInput.value;
        canvasWidthInput.value = canvasHeightInput.value;
        canvasHeightInput.value = temp;
        
        if (canvasPresetSelect) {
            canvasPresetSelect.value = 'custom';
        }
    });
}

let startupImportState = 0; // 0: default, 1: waiting for paste
let layerImportState = 0; // 0: default, 1: waiting for paste (layers panel)
let isDraggingLayer = false; // true while an internal layer drag-and-drop is in progress

// Logical Canvas Size
let paperWidth = 1920; let paperHeight = 1080;

// Canvas Buffers
const strokeCanvas = document.createElement('canvas'); const sctx = strokeCanvas.getContext('2d', { willReadFrequently: true });
const groupCanvas = document.createElement('canvas'); const gctx = groupCanvas.getContext('2d', { willReadFrequently: true });
const maskBuffer = document.createElement('canvas'); const mctx = maskBuffer.getContext('2d', { willReadFrequently: true });
const selectionOutlineCanvas = document.createElement('canvas'); const selectionOutlineCtx = selectionOutlineCanvas.getContext('2d');

// Composite Cache Canvas (Option B)
const layersCacheCanvas = document.createElement('canvas');
const layersCacheCtx = layersCacheCanvas.getContext('2d');
let layersCacheDirty = true;
let layersCacheUntilIndex = -1;

// On-Demand Rendering (Option A)
let renderRequested = false;
function requestRender() {
    if (!renderRequested) {
        renderRequested = true;
        requestAnimationFrame(render);
    }
}

function updateLayersCache(limit) {
    if (!layersCacheDirty && layersCacheUntilIndex === limit) return;

    layersCacheCtx.clearRect(0, 0, paperWidth, paperHeight);

    let i = 0;
    while (i < limit) {
        const l = layers[i];
        if (!l.visible) { i++; continue; }

        // Check if there are layers above clipping to this one, but only up to limit
        let next = i + 1;
        let groupCount = 0;
        while (next < limit && layers[next].clippingMask) {
            next++;
            groupCount++;
        }

        if (groupCount > 0) {
            let group = [l];
            for (let k = i + 1; k < next; k++) {
                if (layers[k].visible) group.push(layers[k]);
            }

            if (!l.visible) {
                i = next;
                continue;
            }

            // Render clipping group
            gctx.clearRect(0, 0, paperWidth, paperHeight);
            gctx.save();
            gctx.globalAlpha = group[0].opacity;
            gctx.globalCompositeOperation = group[0].blendMode;
            gctx.drawImage(group[0].canvas, 0, 0);
            gctx.restore();

            for (let k = 1; k < group.length; k++) {
                mctx.clearRect(0, 0, paperWidth, paperHeight);
                mctx.globalCompositeOperation = 'source-over';
                mctx.save();
                mctx.globalAlpha = group[k].opacity;
                mctx.drawImage(group[k].canvas, 0, 0);
                mctx.restore();

                mctx.globalCompositeOperation = 'destination-in';
                mctx.drawImage(group[0].canvas, 0, 0);
                mctx.globalCompositeOperation = 'source-over';

                gctx.save();
                gctx.globalCompositeOperation = group[k].blendMode;
                gctx.drawImage(maskBuffer, 0, 0);
                gctx.restore();
            }

            layersCacheCtx.drawImage(groupCanvas, 0, 0);
            i = next;
        } else {
            // Normal layer
            layersCacheCtx.save();
            layersCacheCtx.globalAlpha = l.opacity;
            layersCacheCtx.globalCompositeOperation = l.blendMode;
            layersCacheCtx.drawImage(l.canvas, 0, 0);
            layersCacheCtx.restore();
            i++;
        }
    }

    layersCacheDirty = false;
    layersCacheUntilIndex = limit;
}


// UI Globals
const checkerPatternLightCanvas = document.createElement('canvas'); let checkerPatternLight = null;
const checkerPatternDarkCanvas = document.createElement('canvas'); let checkerPatternDark = null;
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

// Stabilizer state
let stabEnabled = 3;
let globalLayerCounter = 1;
let eyedropperMode = 'captura'; // 'captura' | 'original'
let newLayerShortcut = '*';
let pressureSensitivity = 0.6;
let velocitySensitivity = 0.0;   // 0 = off, 1 = full
let velocityMode = 'slow';        // 'slow' = slow→thick, 'fast' = fast→thick
let lastPointerTime = 0;
let lastPointerSpeed = 0;        // pixels/ms, exponentially smoothed (heavy, ~0.06)
let stabMode = 'post';
let rawStrokePath = [];
let isPostStrokePreview = false;
let stabPoints = [];
let stabOutX = null, stabOutY = null, stabOutP = null;
let isSpacePressed = false;
let isTemporaryPan = false;

// Lasso/Bucket State
let lassoPath = [];
let lassoLastScreenX = null, lassoLastScreenY = null;
let bucketMode = 'capa';        // 'capa' | 'lienzo' — which source to sample from
let bucketTolerance = 32;       // 0–255 color match tolerance
let bucketContiguous = true;    // flood-fill (true) vs global pixel replace (false)
let bucketFillMode = 'solid';   // 'solid' | 'erase'
let bucketPanel = null;         // floating settings panel
const customCursorImg = new Image();
customCursorImg.src = 'CURSOR.png';
let screenCursorX = 0;
let screenCursorY = 0;

// ─────────────────────────────────────────────────────────────
//  SELECTION SYSTEM
// ─────────────────────────────────────────────────────────────
// selectionMask: offscreen canvas that is pure-white where selected, transparent elsewhere
let selectionCanvas = null; let selCtx = null;
let hasSelection = false;
let copyMode = 'capa';  // 'capa' | 'todas' | 'canvas'
let pasteInNewLayer = false;
let internalClipboardBounds = null;
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
let shapeFromCenterRect = false;
let shapeFromCenterCircle = true;
let shapeFromCenterBtn = null;
let shapeFillBtn = null;
let shapeModifiableLine = false;
let shapeModifiableRect = true;
let shapeModifiableCircle = true;
let shapeModifiableBtn = null;

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
let modSelLayersData = [];   // Array of { layer, canvas } for multi-layer transform
let modSelRotation = 0;
let modSelFlipX = 1;
let modSelFlipY = 1;
let isImportingNewImage = false; // flag for ghost import
let isModifyingShape = false; // flag for shape modification
let flipControls = null;
let flipHBtn = null;
let flipVBtn = null;
let modSelPerspectiveMode = false; // true = 4-corner perspective warp mode
let perspCorners = null; // [{ x, y }, ...] TL, TR, BL, BR in world coords
let perspDragCorner = null; // index of corner being dragged (0-3) or 'move'
let perspDragStart = null; // { wx, wy } world coords at drag start
let perspCornersAtDragStart = null; // snapshot of corners when drag began
let perspBtn = null; // reference to the perspective toggle button

// Canvas Resize State
let isResizingCanvas = false;
let resizePreviewW = 0;
let resizePreviewH = 0;
let resizeActiveHandle = null; // 'tl','tc','tr','ml','mr','bl','bc','br'
let resizeStartMouse = null;
let resizeStartDim = null;
let resizeLibre = true;
let resizeOffsetX = 0;
let resizeOffsetY = 0;
let resizeStartOffsetX = 0;
let resizeStartOffsetY = 0;
let fitScreenBtn = null;
let eyedropperFadeTimeout = null;
let zoomPivotWorld = null;
let zoomPivotScreen = null;
let pushSnapshot = null;
let pushSnapshotPixels = null;
let pushDisplacementX = null;
let pushDisplacementY = null;
let blurBuffer = null;
let smudgeBuffer = null;
let brushMaskCanvas = document.createElement('canvas');
let brushMaskCtx = brushMaskCanvas.getContext('2d');
let blurTempCanvas = document.createElement('canvas');
let blurTempCtx = blurTempCanvas.getContext('2d');
let bleedCanvas = document.createElement('canvas');
let bleedCtx = bleedCanvas.getContext('2d');
// ─────────────────────────────────────────────────────────────
// TOOL STATE
// ─────────────────────────────────────────────────────────────
let currentTool = 'pincel';
let lastBrushTool = 'Pincel Duro';

// Color & Palette
let isAddingToPalette = false;
let paletteColors = []; let paletteRows = 5; const paletteCols = 5;

// Layer System
let layers = []; let selectedLayerIndex = 0; let bgMode = 1; let solidBgColor = '#ffffff';

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
            imageData: l.ctx.getImageData(0, 0, paperWidth, paperHeight)
        })),
        selectionData: (selectionCanvas && hasSelection)
            ? selCtx.getImageData(0, 0, paperWidth, paperHeight)
            : null,
        hasSelection,
        currentTool,
        lastBrushTool,
        modSelInitialized,
        modSelBounds: modSelInitialized ? { ...modSelBounds } : null,
        modSelCanvasData: (modSelInitialized && modSelCanvas)
            ? modSelCtx.getImageData(0, 0, modSelCanvas.width, modSelCanvas.height)
            : null,
        modSelMode: modifySelMode,
        modSelLayersIndices: modSelInitialized ? modSelLayersData.map(item => layers.indexOf(item.layer)) : [],
        modSelRotation: modSelRotation,
        modSelFlipX: modSelFlipX,
        modSelFlipY: modSelFlipY
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
        const dimensionsChanged = (snapshot.paperWidth !== paperWidth || snapshot.paperHeight !== paperHeight);
        // Restore canvas dimensions first if they changed (resize undo/redo)
        if (snapshot.paperWidth && snapshot.paperHeight) {
            paperWidth = snapshot.paperWidth;
            paperHeight = snapshot.paperHeight;
        }

        // Resize all shared off-screen buffers to match restored dimensions
        strokeCanvas.width = paperWidth; strokeCanvas.height = paperHeight;
        groupCanvas.width = paperWidth; groupCanvas.height = paperHeight;
        maskBuffer.width = paperWidth; maskBuffer.height = paperHeight;
        layersCacheCanvas.width = paperWidth; layersCacheCanvas.height = paperHeight;
        layersCacheDirty = true;

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
            selectionCanvas = document.createElement('canvas');
            selectionCanvas.width = paperWidth; selectionCanvas.height = paperHeight;
            selCtx = selectionCanvas.getContext('2d');
            selCtx.putImageData(snapshot.selectionData, 0, 0);
        } else {
            if (selectionCanvas && selCtx) selCtx.clearRect(0, 0, paperWidth, paperHeight);
            hasSelection = false;
        }
        updateSelectionOutline();

        // Restore Modify Selection state
        modSelInitialized = snapshot.modSelInitialized || false;
        modifySelMode = snapshot.modSelMode || 'capa';
        if (modSelInitialized && snapshot.modSelCanvasData && snapshot.modSelBounds) {
            modSelBounds = { ...snapshot.modSelBounds };
            modSelOrigBounds = { ...modSelBounds };
            modSelCanvas = document.createElement('canvas');
            modSelCanvas.width = snapshot.modSelCanvasData.width;
            modSelCanvas.height = snapshot.modSelCanvasData.height;
            modSelCtx = modSelCanvas.getContext('2d');
            modSelCtx.putImageData(snapshot.modSelCanvasData, 0, 0);

            modSelLayersData = (snapshot.modSelLayersIndices || []).map(idx => {
                if (idx >= 0 && idx < layers.length) {
                    return { layer: layers[idx], canvas: modSelCanvas };
                }
                return null;
            }).filter(Boolean);
            modSelRotation = snapshot.modSelRotation || 0;
            modSelFlipX = snapshot.modSelFlipX !== undefined ? snapshot.modSelFlipX : 1;
            modSelFlipY = snapshot.modSelFlipY !== undefined ? snapshot.modSelFlipY : 1;
        } else {
            modSelInitialized = false; modSelCanvas = null; modSelBounds = null; modSelOrigBounds = null;
            modSelLayersData = [];
            modSelRotation = 0; modSelFlipX = 1; modSelFlipY = 1;
        }

        // Restore tool selection ONLY for Modify Selection when active
        if (snapshot.currentTool === 'modify-sel' && modSelInitialized) {
            selectTool('modify-sel', 'Modificar Selección');
        } else {
            // For other tools, just ensure the selection buttons match the current state
            showSelectionButtons(currentTool);
        }

        updateThumbnails();
        updateLayersUI();
        updateTintedTexture();
    } finally {
        _historyPaused = false;
    }
}

function undo() {
    if (historyIndex <= 0) return; // nothing more to undo
    endPushSession();
    historyIndex--;
    restoreHistoryState(historyStack[historyIndex]);
}

function redo() {
    if (historyIndex >= historyStack.length - 1) return; // nothing to redo
    endPushSession();
    historyIndex++;
    restoreHistoryState(historyStack[historyIndex]);
}

// Tool Data
let toolsData = [
    { id: 'zoom', name: 'Zoom', shortcut: 'z' },
    { id: 'pan', name: 'Pan', shortcut: 'x' },
    { id: 'rotate', name: 'Girar Lienzo', shortcut: 'r' },
    { id: 'bucket', name: 'Cubeta', shortcut: 'b', opacity: 1.0 },
    { id: 'lazo-sel', name: 'Lazo Seleccionador', shortcut: 'n' },
    { id: 'lazo-des', name: 'Lazo Deseleccionador', shortcut: 'j' },
    { id: 'modify-sel', name: 'Modificar Selección', shortcut: 'm' },
    { id: 'eyedropper', name: 'Gotero', shortcut: 't' },
];
const brushTypesData = [
    // size = baseBrushSize default, opacity = 0..1, blur = px
    { id: 'duro', name: 'Pincel Duro', shortcut: 'a', hardness: 0.8, useCompositing: true, useTexture: false, size: 2, opacity: 1.00, blur: 0 },
    { id: 'suave', name: 'Pincel Suave', shortcut: 'c', hardness: 0.3, useCompositing: false, useTexture: false, size: 2, opacity: 0.15, blur: 0 },
    { id: 'borrador', name: 'Borrador', shortcut: 's', hardness: 0.8, useCompositing: false, useTexture: false, isEraser: true, size: 3, opacity: 1.00, blur: 0 },
    { id: 'borrador-suave', name: 'Borrador Suave', shortcut: 's', modifier: '+shift', hardness: 0.3, useCompositing: false, useTexture: false, isEraser: true, size: 7, opacity: 0.50, blur: 0 },
    { id: 'aero-duro', name: 'Aerógrafo Duro', shortcut: 'e', hardness: 0.8, useCompositing: true, useTexture: false, size: 1, opacity: 1.00, blur: 12 },
    { id: 'aero-suave', name: 'Aerógrafo Suave', shortcut: 'd', hardness: 0.2, useCompositing: true, useTexture: true, size: 3, opacity: 1.00, blur: 25 },
    { id: 'lazo-relleno', name: 'Lazo de Relleno', shortcut: 'q', hardness: 1.0, isLasso: true, lassoColor: '#ff00ff', size: 10, opacity: 1.00, blur: 0 },
    { id: 'lazo-borrador', name: 'Lazo Borrador', shortcut: 'w', hardness: 1.0, isLasso: true, lassoColor: '#ff0000', isEraser: true, size: 10, opacity: 1.00, blur: 0 },
    // ── Shape tools ──
    { id: 'linea', name: 'Línea', shortcut: 'f', isShape: true, shapeType: 'line', useCompositing: true, useTexture: false, hardness: 1.0, size: 3, opacity: 1.00, blur: 0 },
    { id: 'rectangulo', name: 'Rectángulo', shortcut: 'g', isShape: true, shapeType: 'rect', useCompositing: true, useTexture: false, hardness: 1.0, size: 3, opacity: 1.00, blur: 0 },
    { id: 'circulo', name: 'Círculo / Elipse', shortcut: 'h', isShape: true, shapeType: 'ellipse', useCompositing: true, useTexture: false, hardness: 1.0, size: 3, opacity: 1.00, blur: 0 },
    { id: 'push-brush', name: 'Empujar', isPush: true, shortcut: 'v', size: 5, opacity: 0.5, blur: 0 },
    { id: 'difuminar-arrastre', name: 'Difuminar (Arrastre)', shortcut: 'l', isSmudge: true, useTexture: true, size: 5, opacity: 0.5, blur: 0 },
    { id: 'difuminar-gauss', name: 'Difuminar (Gausiano)', shortcut: 'ñ', isGaussBlur: true, useTexture: false, hardness: 0.5, size: 18, opacity: 1.0, blur: 2 },
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


function resetImportButton() {
    startupImportState = 0;
    const importBtn = document.getElementById('import-btn');
    if (importBtn) {
        importBtn.classList.remove('waiting-paste');
        importBtn.textContent = 'Importar imagen';
    }
}

function resetLayerImportButton() {
    layerImportState = 0;
    const btn = document.getElementById('import-layer-btn');
    if (btn) btn.classList.remove('waiting-paste');
}

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

    // Fast Zoom with Mouse Wheel (Centered at cursor)
    canvas.addEventListener('wheel', (e) => {
        e.preventDefault();
        const delta = -e.deltaY;
        const factor = Math.pow(1.1, delta / 100);

        const rect = canvas.getBoundingClientRect();
        const mouseX = e.clientX - rect.left;
        const mouseY = e.clientY - rect.top;

        // World coordinates before zoom
        const worldBefore = screenToWorld(mouseX, mouseY);

        // Update scale
        viewScale *= factor;
        viewScale = Math.max(0.01, Math.min(viewScale, 50));

        // World coordinates after zoom
        const worldAfter = screenToWorld(mouseX, mouseY);

        // Adjust view position to keep mouse over the same world point
        viewPosX += (worldAfter.x - worldBefore.x);
        viewPosY += (worldAfter.y - worldBefore.y);
        requestRender();
    }, { passive: false });

    flipControls = document.getElementById('flip-controls');
    flipHBtn = document.getElementById('flip-h-btn');
    flipVBtn = document.getElementById('flip-v-btn');
    if (flipHBtn) flipHBtn.onclick = () => flipSelection('h');
    if (flipVBtn) flipVBtn.onclick = () => flipSelection('v');

    // Perspective button (created dynamically, placed alongside flip buttons)
    if (flipControls) {
        perspBtn = document.createElement('button');
        perspBtn.className = 'floating-flip-btn';
        perspBtn.id = 'perspective-mode-btn';
        perspBtn.title = 'Modo Perspectiva';
        perspBtn.innerHTML = `<img src="perspectiva.png" style="width:28px;height:28px;object-fit:contain;">`;
        perspBtn.style.cssText = 'background:rgba(30,30,40,0.9); border:1px solid rgba(255,255,255,0.2); color:white; padding:8px; cursor:pointer; border-radius:10px; transition:all 0.2s;';
        perspBtn.onclick = togglePerspectiveMode;
        flipControls.appendChild(perspBtn);
    }

    initPalette();
    loadShortcuts();
    setupMultiToolMenu();
    setupBrushMenu();

    requestRender();

    createBtn.onclick = () => {
        startApp(parseInt(canvasWidthInput.value) | 0, parseInt(canvasHeightInput.value) | 0);
        resetImportButton();
    };
    importBtn.onclick = () => {
        if (startupImportState === 0) {
            startupImportState = 1;
            importBtn.classList.add('waiting-paste');
            importBtn.textContent = 'ESPERANDO CTRL + V...';
        } else {
            resetImportButton();
            fileInput.click();
        }
    };

    // Drag & Drop (external files only — internal layer drags are ignored via isDraggingLayer)
    window.addEventListener('dragover', (e) => e.preventDefault());
    window.addEventListener('drop', (e) => {
        e.preventDefault();
        if (isDraggingLayer) return; // internal layer reorder — do nothing here
        const files = e.dataTransfer.files;
        if (files && files.length > 0) {
            handleIncomingFile(files[0]);
        }
    });

    // Listener for Paste
    window.addEventListener('paste', (e) => {
        // 1. Try to get images from items (standard for images copied from web/apps)
        const items = (e.clipboardData || e.originalEvent.clipboardData).items;
        let found = false;
        for (let i = 0; i < items.length; i++) {
            if (items[i].type.indexOf("image") !== -1) {
                const file = items[i].getAsFile();
                if (file) {
                    handleIncomingFile(file);
                    found = true;
                    break;
                }
            }
        }

        // 2. If not found, try to get files (standard for files copied from desktop/explorer)
        if (!found) {
            const files = (e.clipboardData || e.originalEvent.clipboardData).files;
            if (files && files.length > 0) {
                for (let i = 0; i < files.length; i++) {
                    if (files[i].type.indexOf("image") !== -1) {
                        handleIncomingFile(files[i]);
                        break;
                    }
                }
            }
        }
    });

    fileInput.onchange = (e) => {
        const file = e.target.files[0];
        if (file) {
            handleIncomingFile(file);
            e.target.value = ''; // Clear value so same file can be imported again
        }
    };

    sizeSlider.oninput = (e) => { baseBrushSize = parseFloat(e.target.value); sizeValue.textContent = baseBrushSize < 10 ? baseBrushSize.toFixed(1) : Math.round(baseBrushSize); currentBrush.size = baseBrushSize; requestRender(); };
    sizeSlider.onpointerup = (e) => e.target.blur();

    // ── Size Preset Popup ──────────────────────────────────────
    (function initSizePresets() {
        const PRESETS = [0.1, 0.3, 0.5, 0.7, 1, 2, 3, 5, 7, 9, 12, 16, 20, 25, 30, 40, 50, 60, 75, 100];
        const tab     = document.getElementById('size-preset-tab');
        const popup   = document.getElementById('size-preset-popup');
        const grid    = document.getElementById('size-preset-grid');
        if (!tab || !popup || !grid) return;

        // Build circles
        function drawCircle(sz) {
            const MAX_R = 16;
            const canvasSize = MAX_R * 2 + 2;
            const c = document.createElement('canvas');
            c.width = canvasSize; c.height = canvasSize;
            const cx = c.getContext('2d');
            const r = Math.min(MAX_R, Math.max(0.8, sz * 0.32));
            cx.beginPath();
            cx.arc(canvasSize / 2, canvasSize / 2, r, 0, Math.PI * 2);
            cx.fillStyle = 'rgba(210,210,230,0.85)';
            cx.fill();
            return c;
        }

        function refreshActive() {
            grid.querySelectorAll('.size-preset-btn').forEach(btn => {
                btn.classList.toggle('active-size', parseFloat(btn.dataset.size) === baseBrushSize);
            });
        }

        PRESETS.forEach(sz => {
            const btn = document.createElement('button');
            btn.className = 'size-preset-btn';
            btn.dataset.size = sz;
            btn.appendChild(drawCircle(sz));
            const label = document.createElement('span');
            label.textContent = sz + ' px';
            btn.appendChild(label);
            btn.addEventListener('pointerdown', e => {
                e.stopPropagation();
                baseBrushSize = sz;
                sizeSlider.value = sz;
                sizeValue.textContent = sz < 10 ? sz.toFixed(1) : sz;
                currentBrush.size = sz;
                requestRender();
                refreshActive();
            });
            grid.appendChild(btn);
        });

        // Hover logic with a small delay so it doesn't flash
        let hideTimer = null;
        function showPopup() {
            clearTimeout(hideTimer);
            popup.classList.remove('hidden');
            refreshActive();
        }
        function hidePopup() {
            hideTimer = setTimeout(() => popup.classList.add('hidden'), 180);
        }

        tab.addEventListener('pointerenter', showPopup);
        tab.addEventListener('pointerleave', hidePopup);
        popup.addEventListener('pointerenter', () => clearTimeout(hideTimer));
        popup.addEventListener('pointerleave', hidePopup);
    })();
    // ──────────────────────────────────────────────────────────

    opacitySlider.oninput = (e) => { 
        brushOpacity = e.target.value / 100; 
        opacityValue.textContent = e.target.value + '%'; 
        if (currentTool === 'bucket') {
            const t = toolsData.find(x => x.id === 'bucket');
            if (t) t.opacity = brushOpacity;
        } else if (currentBrush) {
            currentBrush.opacity = brushOpacity; 
        }
        if (eyeIcon) eyeIcon.src = (e.target.value | 0) === 0 ? 'simbolo ojo cerrado.png' : 'simbolo ojo abierto.png'; 
        requestRender(); 
    };
    opacitySlider.onpointerup = (e) => e.target.blur();

    // ── Opacity Preset Popup ───────────────────────────────────
    (function initOpacityPresets() {
        const PRESETS = [5,10,15,20,25,30,35,40,45,50,55,60,65,70,75,80,85,90,95,100];
        const tab   = document.getElementById('opacity-preset-tab');
        const popup = document.getElementById('opacity-preset-popup');
        const grid  = document.getElementById('opacity-preset-grid');
        if (!tab || !popup || !grid) return;

        // Draw a small circle with a checkerboard behind + fill at the given opacity
        function drawOpacityCircle(pct) {
            const SIZE = 34; const R = 13;
            const c = document.createElement('canvas');
            c.width = SIZE; c.height = SIZE;
            const cx = c.getContext('2d');
            const cx2 = SIZE / 2, cy2 = SIZE / 2;

            // Checkerboard pattern (shows through the transparent areas)
            const sq = 4;
            for (let row = 0; row < SIZE / sq; row++) {
                for (let col = 0; col < SIZE / sq; col++) {
                    cx.fillStyle = (row + col) % 2 === 0 ? '#555' : '#333';
                    cx.fillRect(col * sq, row * sq, sq, sq);
                }
            }
            // Clip to circle and draw the colour fill at given opacity
            cx.save();
            cx.beginPath(); cx.arc(cx2, cy2, R, 0, Math.PI * 2); cx.clip();
            cx.clearRect(0, 0, SIZE, SIZE);
            // Re-draw checker inside clip
            for (let row = 0; row < SIZE / sq; row++) {
                for (let col = 0; col < SIZE / sq; col++) {
                    cx.fillStyle = (row + col) % 2 === 0 ? '#555' : '#333';
                    cx.fillRect(col * sq, row * sq, sq, sq);
                }
            }
            cx.globalAlpha = pct / 100;
            cx.fillStyle = 'rgba(210,210,230,1)';
            cx.fillRect(0, 0, SIZE, SIZE);
            cx.restore();
            // Circle border
            cx.beginPath(); cx.arc(cx2, cy2, R, 0, Math.PI * 2);
            cx.strokeStyle = 'rgba(255,255,255,0.18)'; cx.lineWidth = 1; cx.stroke();
            return c;
        }

        function refreshActive() {
            const cur = Math.round(brushOpacity * 100);
            grid.querySelectorAll('.size-preset-btn').forEach(btn => {
                btn.classList.toggle('active-size', parseInt(btn.dataset.opacity) === cur);
            });
        }

        PRESETS.forEach(pct => {
            const btn = document.createElement('button');
            btn.className = 'size-preset-btn';
            btn.dataset.opacity = pct;
            btn.appendChild(drawOpacityCircle(pct));
            const label = document.createElement('span');
            label.textContent = pct + '%';
            btn.appendChild(label);
            btn.addEventListener('pointerdown', e => {
                e.stopPropagation();
                brushOpacity = pct / 100;
                opacitySlider.value = pct;
                opacityValue.textContent = pct + '%';
                if (currentTool === 'bucket') {
                    const t = toolsData.find(x => x.id === 'bucket');
                    if (t) t.opacity = brushOpacity;
                } else if (currentBrush) {
                    currentBrush.opacity = brushOpacity;
                }
                if (eyeIcon) eyeIcon.src = pct === 0 ? 'simbolo ojo cerrado.png' : 'simbolo ojo abierto.png';
                requestRender();
                refreshActive();
            });
            grid.appendChild(btn);
        });

        let hideTimer = null;
        function showPopup() { clearTimeout(hideTimer); popup.classList.remove('hidden'); refreshActive(); }
        function hidePopup() { hideTimer = setTimeout(() => popup.classList.add('hidden'), 180); }

        tab.addEventListener('pointerenter', showPopup);
        tab.addEventListener('pointerleave', hidePopup);
        popup.addEventListener('pointerenter', () => clearTimeout(hideTimer));
        popup.addEventListener('pointerleave', hidePopup);
    })();
    // ──────────────────────────────────────────────────────────

    blurSlider.oninput = (e) => { currentBlur = e.target.value | 0; blurValueLabel.textContent = currentBlur; currentBrush.blur = currentBlur; updateTintedTexture(); };
    blurSlider.onpointerup = (e) => e.target.blur();

    const stabModeBtn = document.getElementById('stab-mode-btn');
    if (stabModeBtn) {
        stabModeBtn.addEventListener('click', () => {
            stabMode = stabMode === 'post' ? 'realtime' : 'post';
            stabModeBtn.textContent = stabMode === 'post' ? 'POST' : 'VIVO';
            stabModeBtn.style.color = stabMode === 'post' ? '#8cf' : '#aaa';
        });
    }

    stabilizerSlider.oninput = (e) => { stabEnabled = e.target.value | 0; stabilizerValue.textContent = stabEnabled; };
    stabilizerSlider.onpointerup = (e) => e.target.blur();

    const pressureSlider = document.getElementById('pressure-slider');
    const pressureValueLabel = document.getElementById('pressure-value');
    if (pressureSlider) {
        pressureSlider.oninput = (e) => {
            // Slider 0-200 → sensitivity 0.0-2.0
            pressureSensitivity = parseInt(e.target.value) / 100;
            pressureValueLabel.textContent = e.target.value + '%';
        };
        pressureSlider.onpointerup = (e) => e.target.blur();
    }

    const velocitySlider     = document.getElementById('velocity-slider');
    const velocityValueLabel = document.getElementById('velocity-value');
    if (velocitySlider) {
        velocitySlider.oninput = (e) => {
            velocitySensitivity = parseInt(e.target.value) / 100;
            velocityValueLabel.textContent = e.target.value + '%';
        };
        velocitySlider.onpointerup = (e) => e.target.blur();
    }

    const velocityModeBtn = document.getElementById('velocity-mode-btn');
    if (velocityModeBtn) {
        velocityModeBtn.addEventListener('click', () => {
            velocityMode = velocityMode === 'slow' ? 'fast' : 'slow';
            velocityModeBtn.textContent  = velocityMode === 'slow' ? 'LENTO=+' : 'RÁPIDO=+';
            velocityModeBtn.style.color  = velocityMode === 'slow' ? '#aaa' : '#8cf';
        });
    }

    resetRotationBtn.onclick = resetRotation;
    function handleKeyDown(e) {
        if (e.code === 'Space' && e.target.tagName !== 'INPUT' && e.target.tagName !== 'SELECT') {
            isSpacePressed = true;
            if (currentTool !== 'pan') {
                canvas.style.cursor = 'grab';
            }
        }
        handleGlobalShortcuts(e);
        requestRender();
    }

    function handleKeyUp(e) {
        if (e.code === 'Space') {
            isSpacePressed = false;
            canvas.style.cursor = '';
        }
        requestRender();
    }

    document.addEventListener('keydown', handleKeyDown);
    document.addEventListener('keyup', handleKeyUp);


    const newLayerBtn = document.getElementById('new-layer-btn');
    newLayerBtn.onclick = () => addLayer("Nueva Capa");
    newLayerBtn.addEventListener('contextmenu', (e) => {
        e.preventDefault();
        const k = prompt('Ingresa 1 tecla para el atajo "Nueva Capa", o deja vacío para eliminar:', newLayerShortcut);
        if (k !== null) {
            newLayerShortcut = k.toLowerCase().substring(0, 1);
            saveShortcuts();
        }
    });

    // Quick layer action buttons
    const qAlpha = document.getElementById('qbtn-alpha');
    const qClip  = document.getElementById('qbtn-clip');
    const qMerge = document.getElementById('qbtn-merge');
    const ACTIVE_STYLE  = 'background: rgba(0,200,80,0.75); border-color: #00cc44; color: #fff;';
    const IDLE_STYLE    = 'background: rgba(255,255,255,0.4); backdrop-filter:blur(5px); border: 1px solid rgba(255,255,255,0.5); color: #333;';

    if (qAlpha) {
        qAlpha.addEventListener('pointerdown', (e) => {
            e.stopPropagation();
            const l = layers[selectedLayerIndex];
            if (!l) return;
            l.alphaLocked = !l.alphaLocked;
            updateLayersUI(); pushHistory();
        });
    }
    if (qClip) {
        qClip.addEventListener('pointerdown', (e) => {
            e.stopPropagation();
            const l = layers[selectedLayerIndex];
            if (!l) return;
            l.clippingMask = !l.clippingMask;
            layersCacheDirty = true;
            updateLayersUI(); pushHistory(); requestRender();
        });
    }
    if (qMerge) {
        qMerge.addEventListener('pointerdown', (e) => {
            e.stopPropagation();
            if (selectedLayerIndex <= 0) return;
            // Flash green briefly
            qMerge.style.cssText += ACTIVE_STYLE;
            setTimeout(() => { if (qMerge) qMerge.style.cssText = IDLE_STYLE + ' padding:3px 10px; border-radius:12px; font-size:10px; font-weight:bold; cursor:pointer; transition:all 0.2s; white-space:nowrap;'; }, 400);
            mergeLayerDown(selectedLayerIndex);
            updateThumbnails(); updateLayersUI();
        });
    }
    window._syncQuickLayerBtns = function() {
        const l = layers[selectedLayerIndex];
        if (!l) return;
        const BASE = 'padding:3px 10px; border-radius:12px; font-size:10px; font-weight:bold; cursor:pointer; transition:all 0.2s; white-space:nowrap; backdrop-filter:blur(5px);';
        if (qAlpha) qAlpha.style.cssText = BASE + (l.alphaLocked ? ACTIVE_STYLE : IDLE_STYLE);
        if (qClip)  qClip.style.cssText  = BASE + (l.clippingMask ? ACTIVE_STYLE : IDLE_STYLE);
        if (qMerge) qMerge.style.cssText = BASE + IDLE_STYLE;
    };
    document.getElementById('duplicate-layer-btn').onclick = duplicateSelectedLayer;
    document.getElementById('import-layer-btn').onclick = () => {
        if (layerImportState === 0) {
            layerImportState = 1;
            document.getElementById('import-layer-btn').classList.add('waiting-paste');
        } else {
            resetLayerImportButton();
            toggleMenu(null);
            fileInput.click();
        }
    };
    document.getElementById('insert-layer-btn').onclick = () => addLayer("Capa desde lienzo", true);
    
    const toggleBgBtn = document.getElementById('toggle-bg-btn');
    toggleBgBtn.onclick = toggleBackground;
    toggleBgBtn.oncontextmenu = (e) => {
        e.preventDefault();
        const input = document.createElement('input');
        input.type = 'color';
        input.value = solidBgColor;
        input.oninput = (ev) => {
            solidBgColor = ev.target.value;
            if (bgMode !== 1) {
                bgMode = 1;
                updateBgUI();
            }
            requestRender();
        };
        input.click();
    };

    document.getElementById('move-layer-btn').onclick = () => { toggleMenu(null); moveLayerContent(); };

    [mainShortcutInput, brushShortcutInput, layersShortcutInput, colorsShortcutInput, configShortcutInput].forEach(inp => {
        if (inp) inp.addEventListener('input', () => { if (inp.value.length > 1) inp.value = inp.value.slice(-1); saveShortcuts(); });
    });

    mainColorPicker.oninput = (e) => { selectedColor = e.target.value; updateTintedTexture(); };
    mainColorPicker.onchange = (e) => { e.target.blur(); };

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
        document.getElementById('copy-mode-value').textContent = labels[next];
    };
    document.getElementById('toggle-paste-layer').onclick = (e) => {
        pasteInNewLayer = !pasteInNewLayer;
        document.getElementById('paste-layer-value').textContent = pasteInNewLayer ? 'ON' : 'OFF';
    };
    document.getElementById('toggle-cursor-mode').onclick = (e) => {
        cursorMode = cursorMode === 'always' ? 'auto' : 'always';
        document.getElementById('cursor-mode-value').textContent = cursorMode === 'always' ? 'SIEMPRE VISIBLE' : 'AUTOMÁTICO';
        applyCursor(false);
    };

    // Resize Canvas
    document.getElementById('btn-resize-canvas').onclick = () => { openResizeModal(); toggleMenu(null); };
    document.getElementById('toggle-resize-libre').onclick = (e) => {
        resizeLibre = !resizeLibre;
        e.target.textContent = resizeLibre ? 'ON' : 'OFF';
        e.target.style.background = resizeLibre ? '#0066ff' : '';
        e.target.style.color = resizeLibre ? 'white' : '';
        if (!resizeLibre) {
            // Recalculate offsets from anchor when turning off Libre mode
            const dw = resizePreviewW - paperWidth;
            const dh = resizePreviewH - paperHeight;
            const col = resizeAnchor[1];
            const row = resizeAnchor[0];
            if (col === 'l') resizeOffsetX = 0;
            else if (col === 'c') resizeOffsetX = Math.round(dw / 2);
            else if (col === 'r') resizeOffsetX = dw;
            if (row === 't') resizeOffsetY = 0;
            else if (row === 'm') resizeOffsetY = Math.round(dh / 2);
            else if (row === 'b') resizeOffsetY = dh;
        }
    };

    // Fullscreen
    const fsBtn = document.getElementById('btn-fullscreen');
    const fsTitle = document.getElementById('fullscreen-title');
    fsBtn.onclick = () => toggleFullscreen();
    document.addEventListener('fullscreenchange', () => {
        fsTitle.textContent = document.fullscreenElement ? 'Salir de pantalla completa' : 'Pantalla completa';
    });

    // Build floating selection UI buttons (hidden by default)
    buildSelectionUI();

    initPalette(); loadShortcuts(); setupMultiToolMenu(); setupBrushMenu();
    applyCursor(false);
}

// ─────────────────────────────────────────────────────────────
//  FILTERS LOGIC
// ─────────────────────────────────────────────────────────────
let activeFilterType = null;
let filterOriginalImgData = null;

// Curves state
let curvesData = {
    rgb: [{ x: 0, y: 255 }, { x: 255, y: 0 }],
    r: [{ x: 0, y: 255 }, { x: 255, y: 0 }],
    g: [{ x: 0, y: 255 }, { x: 255, y: 0 }],
    b: [{ x: 0, y: 255 }, { x: 255, y: 0 }]
};
let curvesSmoothState = { rgb: true, r: true, g: true, b: true };
let activeCurveChannel = 'rgb';
let draggingCurvePoint = null;
let edgesBgMode = 'transparent';
let blackWhiteBgMode = 'transparent';
let filterPrevTool = 'pincel';
let chromaKeyColor = '#00ff00';
let chromaThreshold = 30;
let chromaFuzziness = 20;
let chromaMaskCanvas = null;
let chromaMaskCtx = null;
let chromaDebugBG = null; // null, '#ff0000', '#00ff00', '#0000ff'
let outlineCache = { params: {}, solid: null, outerDist: null, innerDist: null };
let chromaLassoMode = 'none'; // 'none', 'add' (regenerador), 'sub' (eliminador), 'clear' (nulo), 'pick'

function selectChromaLasso(mode) {
    const lassoBtns = document.querySelectorAll('.chroma-lasso-btn');
    if (chromaLassoMode === mode) {
        chromaLassoMode = 'none';
        lassoBtns.forEach(b => b.style.boxShadow = '');
    } else {
        chromaLassoMode = mode;
        currentTool = 'none';
        lassoBtns.forEach(b => {
            b.style.boxShadow = b.dataset.mode === mode ? '0 0 0 3px rgba(0,0,0,0.4) inset' : '';
        });
    }
}

function openFilterModal(type) {
    // Guardar la herramienta anterior, pero nunca guardar 'none' para no bloquear los filtros
    filterPrevTool = (currentTool && currentTool !== 'none') ? currentTool : filterPrevTool;
    currentTool = 'none';
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
        blackWhiteBgMode = 'transparent'; // Resetear siempre al abrir el modal
        addFilterToggle('Fondo', ['transparent', 'white'], blackWhiteBgMode, (v) => { blackWhiteBgMode = v; applyFilters(); });
        addFilterSlider('Punto Negro', 0, 255, 20, (v) => applyFilters());
        addFilterSlider('Punto Blanco', 0, 255, 230, (v) => applyFilters());
        addFilterSlider('Sensibilidad (Gamma)', 1, 30, 10, (v) => applyFilters()); // 1.0 * 10
    } else if (type === 'levels') {
        title.textContent = 'Curvas de Nivel';
        desc.textContent = 'Ajusta el histograma arrastrando los puntos.';
        curvesData = {
            rgb: [{ x: 0, y: 255 }, { x: 255, y: 0 }],
            r: [{ x: 0, y: 255 }, { x: 255, y: 0 }],
            g: [{ x: 0, y: 255 }, { x: 255, y: 0 }],
            b: [{ x: 0, y: 255 }, { x: 255, y: 0 }]
        };
        curvesSmoothState = { rgb: true, r: true, g: true, b: true };
        activeCurveChannel = 'rgb';
        addFilterCurveEditor(container);
    } else if (type === 'hue') {
        title.textContent = 'Cambiar Tono';
        desc.textContent = 'Ajusta tono, saturación y brillo.';
        addFilterSlider('Tono', 0, 360, 0, (v) => applyFilters());
        addFilterSlider('Saturación', -100, 100, 0, (v) => applyFilters());
        addFilterSlider('Brillo', -100, 100, 0, (v) => applyFilters());
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
    } else if (type === 'sharpen') {
        title.textContent = 'Marcar Nitidez';
        desc.textContent = 'Aumenta la nitidez y el contraste en los bordes.';
        addFilterSlider('Fuerza', 1, 100, 50, (v) => applyFilters());
    } else if (type === 'gauss') {
        title.textContent = 'Difuminado Gaussiano';
        desc.textContent = 'Aplica un desenfoque gaussiano a toda la capa.';
        addFilterSlider('Radio', 1, 50, 5, (v) => applyFilters());
    } else if (type === 'posterize') {
        title.textContent = 'Posterizar';
        desc.textContent = 'Reduce la cantidad de colores por canal.';
        addFilterSlider('Niveles', 2, 32, 6, (v) => applyFilters());
    } else if (type === 'outline') {
        title.textContent = 'Contorno (Stroke)';
        desc.textContent = 'Añade un contorno exterior a los bordes sólidos del PNG.';

        // Color picker para el contorno
        const outlineColorWrap = document.createElement('div');
        outlineColorWrap.style.cssText = 'display:flex; justify-content:space-between; align-items:center; padding:6px 0;';
        outlineColorWrap.innerHTML = `
            <label style="font-size:11px; font-weight:700; color:#444;">Color del contorno</label>
            <div style="display:flex; align-items:center; gap:8px;">
                <div id="outline-color-swatch" style="width:28px; height:28px; border-radius:6px; border:2px solid rgba(0,0,0,0.15); background:#000000; box-shadow:0 2px 6px rgba(0,0,0,0.2); cursor:pointer;"></div>
                <input type="color" id="outline-color-picker" value="#000000" style="width:0; height:0; opacity:0; position:absolute; pointer-events:none;">
            </div>
        `;
        container.appendChild(outlineColorWrap);

        const outlinePicker = outlineColorWrap.querySelector('#outline-color-picker');
        const outlineSwatch = outlineColorWrap.querySelector('#outline-color-swatch');
        outlineSwatch.onclick = () => outlinePicker.click();
        outlinePicker.oninput = () => {
            outlineSwatch.style.background = outlinePicker.value;
            applyFilters();
        };

        addFilterSlider('Grosor Externo (px)', 0, 40, 4, (v) => applyFilters());
        addFilterSlider('Umbral Alpha', 1, 255, 10, (v) => applyFilters());
        addFilterSlider('Opacidad (%)', 0, 100, 100, (v) => applyFilters());
        addFilterSlider('Suavizado bordes', 0, 8, 0, (v) => applyFilters());
        addFilterSlider('Grosor Interno (px)', 0, 40, 0, (v) => applyFilters());
    } else if (type === 'chroma') {
        title.textContent = 'Quitar Fondo (Chroma Key)';
        desc.textContent = 'Selecciona un color para volverlo transparente. Usa los lazos para refinar.';
        chromaDebugBG = '#0000ff';

        // Debug BG Buttons
        const debugWrap = document.createElement('div');
        debugWrap.style.cssText = 'display:flex; gap:5px; margin-bottom:12px; justify-content:center;';
        debugWrap.innerHTML = `
            <button class="chroma-debug-btn" data-color="#ff0000" style="width:30px; height:20px; background:#ff0000; border:2px solid white; border-radius:4px; cursor:pointer;"></button>
            <button class="chroma-debug-btn" data-color="#00ff00" style="width:30px; height:20px; background:#00ff00; border:2px solid white; border-radius:4px; cursor:pointer;"></button>
            <button class="chroma-debug-btn" data-color="#0000ff" style="width:30px; height:20px; background:#0000ff; border:2px solid black; border-radius:4px; cursor:pointer;"></button>
            <button class="chroma-debug-btn" data-color="none" style="width:30px; height:20px; background:white; border:2px solid #ccc; border-radius:4px; cursor:pointer; font-size:10px; font-weight:bold;">X</button>
        `;
        container.appendChild(debugWrap);

        debugWrap.querySelectorAll('.chroma-debug-btn').forEach(btn => {
            btn.onclick = () => {
                const color = btn.dataset.color;
                chromaDebugBG = color === 'none' ? null : color;
                debugWrap.querySelectorAll('.chroma-debug-btn').forEach(b => b.style.borderColor = 'white');
                if (color !== 'none') btn.style.borderColor = 'black';
            };
        });

        // Color Picker UI
        const colorWrap = document.createElement('div');
        colorWrap.style.cssText = 'display:flex; flex-direction:column; gap:8px; margin-bottom:10px;';
        colorWrap.innerHTML = `
            <div style="display:flex; justify-content:space-between; align-items:center;">
                <label style="font-size:11px; font-weight:700; color:#444;">Color a eliminar</label>
                <div id="chroma-color-preview" style="width:24px; height:24px; border-radius:4px; border:2px solid white; box-shadow:0 0 5px rgba(0,0,0,0.2); background:${chromaKeyColor};"></div>
            </div>
            <button id="chroma-pick-btn" class="layer-action-btn" style="width:100%; font-size:10px;">SELECCIONAR COLOR DEL LIENZO</button>
        `;
        container.appendChild(colorWrap);

        colorWrap.querySelector('#chroma-pick-btn').onclick = () => {
            chromaLassoMode = 'pick';
            colorWrap.querySelector('#chroma-pick-btn').textContent = 'HAZ CLICK EN EL COLOR...';
        };

        addFilterSlider('Tolerancia', 0, 255, chromaThreshold, (v) => { chromaThreshold = v; applyFilters(); });
        addFilterSlider('Suavizado (Fuzziness)', 0, 255, chromaFuzziness, (v) => { chromaFuzziness = v; applyFilters(); });

        // Lasso Actions
        const qKey = brushTypesData.find(b => b.id === 'lazo-relleno')?.shortcut.toUpperCase() || 'Q';
        const sKey = brushTypesData.find(b => b.id === 'borrador')?.shortcut.toUpperCase() || 'S';
        const wKey = brushTypesData.find(b => b.id === 'lazo-borrador')?.shortcut.toUpperCase() || 'W';

        const lassoWrap = document.createElement('div');
        lassoWrap.style.cssText = 'display:flex; flex-direction:column; gap:6px; margin-top:10px;';
        lassoWrap.innerHTML = `
            <button class="layer-action-btn chroma-lasso-btn" data-mode="add" style="font-size:10px; background:#4caf50; color:white; border:none; height:32px; display:flex; justify-content:space-between; align-items:center; padding:0 10px;">
                <span>LAZO REGENERADOR</span> <span style="opacity:0.7; font-weight:bold;">[${qKey}]</span>
            </button>
            <button class="layer-action-btn chroma-lasso-btn" data-mode="clear" style="font-size:10px; background:#607d8b; color:white; border:none; height:32px; display:flex; justify-content:space-between; align-items:center; padding:0 10px;">
                <span>LAZO NULO</span> <span style="opacity:0.7; font-weight:bold;">[${sKey}]</span>
            </button>
            <button class="layer-action-btn chroma-lasso-btn" data-mode="sub" style="font-size:10px; background:#f44336; color:white; border:none; height:32px; display:flex; justify-content:space-between; align-items:center; padding:0 10px;">
                <span>LAZO ELIMINADOR</span> <span style="opacity:0.7; font-weight:bold;">[${wKey}]</span>
            </button>
        `;
        container.appendChild(lassoWrap);

        const lassoBtns = lassoWrap.querySelectorAll('.chroma-lasso-btn');
        lassoBtns.forEach(btn => {
            btn.onclick = () => selectChromaLasso(btn.dataset.mode);
        });

        // Setup manual mask canvas
        if (!chromaMaskCanvas) {
            chromaMaskCanvas = document.createElement('canvas');
            chromaMaskCanvas.width = paperWidth;
            chromaMaskCanvas.height = paperHeight;
            chromaMaskCtx = chromaMaskCanvas.getContext('2d');
        }
        chromaMaskCtx.clearRect(0, 0, paperWidth, paperHeight);
        chromaLassoMode = 'pick';
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
    input.onpointerup = (e) => e.target.blur();
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
            ${modes.map(m => `<button class="layer-action-btn" style="flex:1; border:none; border-radius:6px; background:${m === current ? '#000' : 'transparent'}; color:${m === current ? '#fff' : '#666'}; padding:6px; font-size:10px; font-weight:700; cursor:pointer;">${m === 'transparent' ? 'TRANSPARENTE' : 'BLANCO'}</button>`).join('')}
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

function generateCurveLut(points, isSmooth) {
    const lut = new Uint8Array(256);
    if (!isSmooth || points.length < 3) {
        for (let i = 0; i < points.length - 1; i++) {
            const p1 = points[i], p2 = points[i + 1];
            for (let x = p1.x; x <= p2.x; x++) {
                const t = (x - p1.x) / (p2.x - p1.x || 1);
                lut[x] = Math.max(0, Math.min(255, 255 - (p1.y + t * (p2.y - p1.y))));
            }
        }
    } else {
        const n = points.length;
        const m = new Float32Array(n);
        const d = new Float32Array(n - 1);
        for (let i = 0; i < n - 1; i++) {
            d[i] = (points[i+1].y - points[i].y) / (points[i+1].x - points[i].x || 1);
        }
        m[0] = d[0];
        m[n - 1] = d[n - 2];
        for (let i = 1; i < n - 1; i++) {
            if (d[i-1] * d[i] <= 0) m[i] = 0;
            else m[i] = (d[i-1] + d[i]) / 2;
        }
        for (let i = 0; i < n - 1; i++) {
            const p0 = points[i], p1 = points[i+1];
            const h = p1.x - p0.x;
            for (let x = p0.x; x <= p1.x; x++) {
                if (h === 0) {
                    lut[x] = Math.max(0, Math.min(255, 255 - p0.y));
                    continue;
                }
                const t = (x - p0.x) / h;
                const t2 = t * t;
                const t3 = t2 * t;
                const h00 = 2*t3 - 3*t2 + 1;
                const h10 = t3 - 2*t2 + t;
                const h01 = -2*t3 + 3*t2;
                const h11 = t3 - t2;
                const y = h00 * p0.y + h10 * h * m[i] + h01 * p1.y + h11 * h * m[i+1];
                lut[x] = Math.max(0, Math.min(255, 255 - y));
            }
        }
    }
    return lut;
}

function addFilterCurveEditor(container) {
    const header = document.createElement('div');
    header.style.marginBottom = '10px';
    header.style.display = 'flex';
    header.style.justifyContent = 'center';
    header.style.alignItems = 'center';
    header.style.gap = '10px';
    header.innerHTML = `
        <select id="curveChannelSelect" style="flex: 1; border: 1px solid #444; border-radius: 5px; padding: 4px; font-size: 12px; cursor: pointer; outline: none; font-weight: bold; color: black;">
            <option value="rgb">RGB (Global)</option>
            <option value="r">Rojo (Red)</option>
            <option value="g">Verde (Green)</option>
            <option value="b">Azul (Blue)</option>
        </select>
        <label style="font-size: 11px; display: flex; align-items: center; gap: 4px; cursor: pointer; color: #ddd; white-space: nowrap;" title="Interpola la curva con suavizado Spline">
            <input type="checkbox" id="curveSmoothToggle" checked> Curva "S"
        </label>
    `;
    container.appendChild(header);

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

    const select = header.querySelector('#curveChannelSelect');
    const smoothToggle = header.querySelector('#curveSmoothToggle');
    
    const updateSelectColor = () => {
        if (activeCurveChannel === 'rgb') select.style.background = 'orange';
        else if (activeCurveChannel === 'r') select.style.background = '#ff5555';
        else if (activeCurveChannel === 'g') select.style.background = '#55ff55';
        else if (activeCurveChannel === 'b') select.style.background = '#5555ff';
        smoothToggle.checked = curvesSmoothState[activeCurveChannel];
    };

    select.value = activeCurveChannel;
    updateSelectColor();
    
    select.addEventListener('change', (e) => {
        activeCurveChannel = e.target.value;
        updateSelectColor();
        drawFilterHistogram();
        updateCurveUI();
    });

    smoothToggle.addEventListener('change', (e) => {
        curvesSmoothState[activeCurveChannel] = e.target.checked;
        updateCurveUI();
        applyFilters();
    });

    const svg = area.querySelector('#curveSvg');

    svg.style.touchAction = 'none'; // Prevent scroll on touch/pen
    svg.addEventListener('pointerdown', handleCurveMouseDown);
    svg.addEventListener('dblclick', handleCurveDblClick);

    // Global listeners for dragging
    window.addEventListener('pointermove', handleCurveMouseMove);
    window.addEventListener('pointerup', handleCurveMouseUp);
}

function getCurveMousePos(e) {
    const svg = document.getElementById('curveSvg');
    if (!svg) return { x: 0, y: 0 };
    const rect = svg.getBoundingClientRect();
    return {
        x: Math.round(Math.max(0, Math.min(255, e.clientX - rect.left))),
        y: Math.round(Math.max(0, Math.min(255, e.clientY - rect.top)))
    };
}

function handleCurveMouseDown(e) {
    const pos = getCurveMousePos(e);
    const curvePoints = curvesData[activeCurveChannel];
    const hitIndex = curvePoints.findIndex(p => Math.hypot(p.x - pos.x, p.y - pos.y) < 12);
    if (hitIndex !== -1) {
        draggingCurvePoint = hitIndex;
        e.preventDefault(); // Prevent text selection/drag behaviors
    }
}

function handleCurveMouseMove(e) {
    if (draggingCurvePoint === null) return;
    const pos = getCurveMousePos(e);
    const curvePoints = curvesData[activeCurveChannel];

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
    const curvePoints = curvesData[activeCurveChannel];
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

    const curvePoints = curvesData[activeCurveChannel];
    const isSmooth = curvesSmoothState[activeCurveChannel];
    
    if (isSmooth && curvePoints.length > 2) {
        const lut = generateCurveLut(curvePoints, true);
        const pathPoints = [];
        let lastP = curvePoints[0];
        pathPoints.push(`${lastP.x},${lastP.y}`);
        for (let x = curvePoints[0].x; x <= curvePoints[curvePoints.length - 1].x; x++) {
            pathPoints.push(`${x},${255 - lut[x]}`);
        }
        line.setAttribute('points', pathPoints.join(' '));
    } else {
        line.setAttribute('points', curvePoints.map(p => `${p.x},${p.y}`).join(' '));
    }

    let strokeColor = 'white';
    if (activeCurveChannel === 'r') strokeColor = '#ff5555';
    if (activeCurveChannel === 'g') strokeColor = '#55ff55';
    if (activeCurveChannel === 'b') strokeColor = '#5555ff';
    line.setAttribute('stroke', strokeColor);

    // Clear old circles
    svg.querySelectorAll('.curve-point').forEach(c => c.remove());

    curvePoints.forEach((p, i) => {
        const c = document.createElementNS("http://www.w3.org/2000/svg", "circle");
        c.setAttribute("cx", p.x);
        c.setAttribute("cy", p.y);
        c.setAttribute("r", 5);
        c.setAttribute("class", "curve-point");
        c.setAttribute("fill", strokeColor);
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
        let val;
        if (activeCurveChannel === 'r') val = data[i];
        else if (activeCurveChannel === 'g') val = data[i+1];
        else if (activeCurveChannel === 'b') val = data[i+2];
        else val = Math.round((data[i] + data[i + 1] + data[i + 2]) / 3);
        hist[val]++;
    }

    const max = Math.max(...hist);
    hCtx.clearRect(0, 0, 256, 256);
    
    if (activeCurveChannel === 'r') hCtx.fillStyle = 'rgba(255, 85, 85, 0.4)';
    else if (activeCurveChannel === 'g') hCtx.fillStyle = 'rgba(85, 255, 85, 0.4)';
    else if (activeCurveChannel === 'b') hCtx.fillStyle = 'rgba(85, 85, 255, 0.4)';
    else hCtx.fillStyle = 'rgba(255, 255, 255, 0.4)';
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
            const origA = data[i + 3];
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
                data[i] = data[i + 1] = data[i + 2] = 0;
                data[i + 3] = combinedA;
            } else {
                const val = 255 - combinedA;
                data[i] = data[i + 1] = data[i + 2] = val;
                data[i + 3] = 255;
            }
        }
    } else if (activeFilterType === 'levels') {
        const lutRGB = generateCurveLut(curvesData.rgb, curvesSmoothState.rgb);
        const lutR = generateCurveLut(curvesData.r, curvesSmoothState.r);
        const lutG = generateCurveLut(curvesData.g, curvesSmoothState.g);
        const lutB = generateCurveLut(curvesData.b, curvesSmoothState.b);

        for (let i = 0; i < data.length; i += 4) {
            data[i] = lutRGB[lutR[data[i]]];
            data[i + 1] = lutRGB[lutG[data[i + 1]]];
            data[i + 2] = lutRGB[lutB[data[i + 2]]];
        }
    } else if (activeFilterType === 'hue') {
        const hueShift = parseInt(sliders[0].value);
        const satAdjust = parseInt(sliders[1].value) / 100;
        const briAdjust = parseInt(sliders[2].value) / 100;
        for (let i = 0; i < data.length; i += 4) {
            const [r, g, b] = [data[i], data[i + 1], data[i + 2]];
            let [h, s, l] = rgbToHsl(r, g, b);
            h = (h + hueShift) % 360;
            s = Math.max(0, Math.min(1, s + satAdjust));
            l = Math.max(0, Math.min(1, l + briAdjust));
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

        // 1. Grayscale pass (include alpha so transparent boundaries create contrast)
        for (let i = 0; i < orig.length; i += 4) {
            const r = orig[i], g = orig[i + 1], b = orig[i + 2], a = orig[i + 3];
            const lum = 0.299 * r + 0.587 * g + 0.114 * b;
            gray[i / 4] = a < 64 ? -2000 : lum;
        }

        // 2. Sobel pass
        for (let y = 1; y < height - 1; y++) {
            for (let x = 1; x < width - 1; x++) {
                const i = y * width + x;
                const gx = -gray[i - width - 1] + gray[i - width + 1] - 2 * gray[i - 1] + 2 * gray[i + 1] - gray[i + width - 1] + gray[i + width + 1];
                const gy = -gray[i - width - 1] - 2 * gray[i - width] - gray[i - width + 1] + gray[i + width - 1] + 2 * gray[i + width] + gray[i + width + 1];

                let mag = Math.sqrt(gx * gx + gy * gy) * sens;
                mag = Math.max(0, mag - clean);
                let edge = Math.pow(mag / 255, 1 / gamma) * 255;
                if (edge > 255) edge = 255;

                const idx = i * 4;

                if (edgesBgMode === 'transparent') {
                    data[idx] = data[idx + 1] = data[idx + 2] = 0;
                    data[idx + 3] = edge;
                } else {
                    const val = 255 - edge;
                    data[idx] = data[idx + 1] = data[idx + 2] = val;
                    data[idx + 3] = 255;
                }
            }
        }
    } else if (activeFilterType === 'invert') {
        for (let i = 0; i < data.length; i += 4) {
            data[i] = 255 - data[i];
            data[i + 1] = 255 - data[i + 1];
            data[i + 2] = 255 - data[i + 2];
        }
    } else if (activeFilterType === 'sharpen') {
        const force = parseInt(sliders[0].value) / 50;
        const width = paperWidth;
        const height = paperHeight;
        const orig = filterOriginalImgData.data;

        for (let y = 1; y < height - 1; y++) {
            for (let x = 1; x < width - 1; x++) {
                const i = (y * width + x) * 4;
                const t = ((y - 1) * width + x) * 4;
                const b = ((y + 1) * width + x) * 4;
                const l = (y * width + (x - 1)) * 4;
                const r = (y * width + (x + 1)) * 4;

                for (let c = 0; c < 3; c++) {
                    let val = orig[i + c] * (1 + 4 * force)
                        - orig[t + c] * force
                        - orig[b + c] * force
                        - orig[l + c] * force
                        - orig[r + c] * force;
                    data[i + c] = Math.min(255, Math.max(0, val));
                }
                data[i + 3] = orig[i + 3]; // keep alpha
            }
        }
    } else if (activeFilterType === 'gauss') {
        const radius = Math.min(parseInt(sliders[0].value), 200);
        const tmpCanvas = document.createElement('canvas');
        tmpCanvas.width = paperWidth;
        tmpCanvas.height = paperHeight;
        const tmpCtx = tmpCanvas.getContext('2d');
        tmpCtx.putImageData(filterOriginalImgData, 0, 0);

        l.ctx.save();
        l.ctx.clearRect(0, 0, paperWidth, paperHeight);
        l.ctx.filter = `blur(${radius}px)`;
        l.ctx.drawImage(tmpCanvas, 0, 0);
        l.ctx.restore();
        requestRender();
        return; // skip the generic putImageData at the end
    } else if (activeFilterType === 'posterize') {
        const levels = parseInt(sliders[0].value);
        const step = 255 / (levels - 1);
        for (let i = 0; i < data.length; i += 4) {
            data[i]     = Math.round(data[i]     / step) * step;
            data[i + 1] = Math.round(data[i + 1] / step) * step;
            data[i + 2] = Math.round(data[i + 2] / step) * step;
        }
    } else if (activeFilterType === 'outline') {
        const size       = parseInt(sliders[0].value);
        const threshold  = parseInt(sliders[1].value);  // alpha mínimo para considerarse sólido
        const opacity    = parseInt(sliders[2].value) / 100;
        const feather    = parseInt(sliders[3].value);  // suavizado en px
        const innerSize  = parseInt(sliders[4].value);

        const colorPicker = document.getElementById('outline-color-picker');
        const [oR, oG, oB] = hexToRgbArray(colorPicker ? colorPicker.value : '#000000');
        const oA = Math.round(opacity * 255);

        const w = paperWidth, h = paperHeight;
        const orig = filterOriginalImgData.data;

        // Verify cache to avoid expensive recalculation on color/opacity change
        if (outlineCache.params.size !== size || outlineCache.params.threshold !== threshold || 
            outlineCache.params.feather !== feather || outlineCache.params.inner !== innerSize ||
            !outlineCache.solid) {
            
            const solid = new Uint8Array(w * h);
            const trans = new Uint8Array(w * h);
            for (let i = 0; i < orig.length; i += 4) {
                if (orig[i + 3] >= threshold) solid[i >> 2] = 1;
                else trans[i >> 2] = 1;
            }

            // Function to compute distance map
            const computeDist = (mask, radius) => {
                const map = new Float32Array(w * h).fill(Infinity);
                if (radius <= 0) return map;
                const hDil = new Uint8Array(w * h);
                const rowP = new Int32Array(w + 1);
                for (let y = 0; y < h; y++) {
                    const base = y * w; rowP[0] = 0;
                    for (let x = 0; x < w; x++) rowP[x + 1] = rowP[x] + mask[base + x];
                    for (let x = 0; x < w; x++) {
                        const l = Math.max(0, x - radius), r = Math.min(w - 1, x + radius);
                        if (rowP[r + 1] - rowP[l] > 0) hDil[base + x] = 1;
                    }
                }
                const dil = new Uint8Array(w * h);
                const colP = new Int32Array(h + 1);
                for (let x = 0; x < w; x++) {
                    colP[0] = 0;
                    for (let y = 0; y < h; y++) colP[y + 1] = colP[y] + hDil[y * w + x];
                    for (let y = 0; y < h; y++) {
                        const t = Math.max(0, y - radius), b = Math.min(h - 1, y + radius);
                        if (colP[b + 1] - colP[t] > 0) dil[y * w + x] = 1;
                    }
                }
                for (let y = 0; y < h; y++) {
                    for (let x = 0; x < w; x++) {
                        const idx = y * w + x;
                        if (mask[idx]) { map[idx] = 0; continue; }
                        if (!dil[idx]) continue;
                        let minDist2 = Infinity;
                        const yMin = Math.max(0, y - radius), yMax = Math.min(h - 1, y + radius);
                        const xMin = Math.max(0, x - radius), xMax = Math.min(w - 1, x + radius);
                        outer: for (let ny = yMin; ny <= yMax; ny++) {
                            const dy = ny - y, dy2 = dy * dy;
                            if (dy2 >= minDist2) continue;
                            for (let nx = xMin; nx <= xMax; nx++) {
                                if (!mask[ny * w + nx]) continue;
                                const d2 = (nx - x)*(nx - x) + dy2;
                                if (d2 < minDist2) { minDist2 = d2; if (minDist2 === 1) break outer; }
                            }
                        }
                        map[idx] = Math.sqrt(minDist2);
                    }
                }
                return map;
            };

            outlineCache.solid = solid;
            outlineCache.outerDist = computeDist(solid, size);
            outlineCache.innerDist = computeDist(trans, innerSize);
            outlineCache.params = { size, threshold, feather, inner: innerSize };
        }

        const solid = outlineCache.solid;
        const outerDist = outlineCache.outerDist;
        const innerDist = outlineCache.innerDist;

        for (let i = 0; i < data.length; i += 4) {
            const idx = i >> 2;
            const isSolid = solid[idx];
            
            let alpha = 0;
            if (!isSolid && outerDist[idx] <= size && size > 0) {
                alpha = oA;
                if (feather > 0) {
                    const edge = outerDist[idx] / size;
                    const start = 1 - (feather / size);
                    if (edge > start) alpha = Math.round(oA * (1 - (edge - start) / (1 - start || 0.001)));
                }
            } else if (isSolid && innerDist[idx] <= innerSize && innerSize > 0) {
                alpha = oA;
                if (feather > 0) {
                    const edge = innerDist[idx] / innerSize;
                    const start = 1 - (feather / innerSize);
                    if (edge > start) alpha = Math.round(oA * (1 - (edge - start) / (1 - start || 0.001)));
                }
            }

            if (alpha <= 0) continue;

            const origA = orig[i + 3];
            
            if (origA === 0) {
                // Si el pixel original es 100% transparente, solo pintamos el contorno
                data[i] = oR; data[i + 1] = oG; data[i + 2] = oB; data[i + 3] = alpha;
            } else {
                // Composición Source-Over: El contorno (Source) se pinta SIEMPRE por encima del pixel original (Destination)
                const aSrc = alpha / 255;
                const aDst = origA / 255;
                const outA = aSrc + aDst * (1 - aSrc);
                data[i]     = Math.round((oR * aSrc + orig[i] * aDst * (1 - aSrc)) / outA);
                data[i + 1] = Math.round((oG * aSrc + orig[i + 1] * aDst * (1 - aSrc)) / outA);
                data[i + 2] = Math.round((oB * aSrc + orig[i + 2] * aDst * (1 - aSrc)) / outA);
                data[i + 3] = Math.round(outA * 255);
            }
        }
    } else if (activeFilterType === 'chroma') {
        const keyRGB = hexToRgbArray(chromaKeyColor, 255);
        const threshSq = chromaThreshold * chromaThreshold;
        const fuzzyRange = chromaFuzziness;

        // Manual mask data for fast access
        const mData = chromaMaskCtx.getImageData(0, 0, paperWidth, paperHeight).data;

        for (let i = 0; i < data.length; i += 4) {
            // Check manual mask first: R=255 means add, G=255 means sub
            if (mData[i] > 200) {
                // Regenerate: keep original alpha
                continue;
            } else if (mData[i + 1] > 200) {
                // Remove: force alpha to 0
                data[i + 3] = 0;
                continue;
            }

            const r = data[i], g = data[i + 1], b = data[i + 2];
            const dr = r - keyRGB[0], dg = g - keyRGB[1], db = b - keyRGB[2];
            const dist = Math.sqrt(dr * dr + dg * dg + db * db);

            let alpha = 255;
            if (dist < chromaThreshold) {
                alpha = 0;
            } else if (dist < chromaThreshold + fuzzyRange) {
                alpha = 255 * ((dist - chromaThreshold) / (fuzzyRange || 1));
            }

            data[i + 3] = Math.min(data[i + 3], alpha);
        }
    }

    l.ctx.putImageData(workingData, 0, 0);
    requestRender();
}

function commitFilter() {
    pushHistory(); // Capture the new state
    filterModal.classList.add('hidden');
    filterOriginalImgData = null;
    activeFilterType = null;
    chromaDebugBG = null;
    outlineCache.solid = null; outlineCache.outerDist = null; outlineCache.innerDist = null;
    // Asegurar que la herramienta restaurada sea válida y nunca 'none'
    currentTool = (filterPrevTool && filterPrevTool !== 'none') ? filterPrevTool : 'pincel';
    chromaLassoMode = 'none';
    blackWhiteBgMode = 'transparent'; // Limpiar estado para próxima apertura
    layersCacheDirty = true;
    updateThumbnails(); updateLayersUI();
    requestRender();
}

function cancelFilter() {
    if (filterOriginalImgData) {
        layers[selectedLayerIndex].ctx.putImageData(filterOriginalImgData, 0, 0);
    }
    filterModal.classList.add('hidden');
    filterOriginalImgData = null;
    activeFilterType = null;
    chromaDebugBG = null;
    outlineCache.solid = null; outlineCache.outerDist = null; outlineCache.innerDist = null;
    currentTool = filterPrevTool;
    chromaLassoMode = 'none';
    requestRender();
}

// Helper: RGB to HSL
function lerp(a, b, t) { return a + (b - a) * t; }

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
let preResizeToolId = null;
let preResizeToolName = null;

document.getElementById('resize-cancel-btn').onclick = () => {
    isResizingCanvas = false;
    resizeActiveHandle = null;
    canvas.style.cursor = '';
    resizePanel.classList.add('hidden');
    if (preResizeToolId) {
        selectTool(preResizeToolId, preResizeToolName);
        preResizeToolId = null;
        preResizeToolName = null;
    }
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
    if (preResizeToolId) {
        selectTool(preResizeToolId, preResizeToolName);
        preResizeToolId = null;
        preResizeToolName = null;
    }
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
    if (currentTool !== 'pan') {
        preResizeToolId = currentTool;
        preResizeToolName = activeToolIndicator ? activeToolIndicator.textContent : 'Pan';
        selectTool('pan', 'Pan');
    } else {
        preResizeToolId = null;
        preResizeToolName = null;
    }

    isResizingCanvas = true;
    resizePreviewW = paperWidth;
    resizePreviewH = paperHeight;

    document.getElementById('resize-width').value = paperWidth;
    document.getElementById('resize-height').value = paperHeight;

    resizeAnchor = 'mc';
    document.querySelectorAll('.anchor-dot').forEach(b => {
        b.classList.toggle('active', b.dataset.anchor === resizeAnchor);
    });

    // Initialize offsets based on center anchor
    resizeOffsetX = 0;
    resizeOffsetY = 0;
    resizeLibre = true;
    const btn = document.getElementById('toggle-resize-libre');
    if (btn) {
        btn.textContent = 'ON';
        btn.style.background = '#0066ff';
        btn.style.color = 'white';
    }

    resizePanel.classList.remove('hidden');
    makeDraggable(resizePanel, document.getElementById('resize-header'));
}

/**
 * Resize the logical canvas, preserving existing layer content at the chosen anchor.
 * anchor: 'tl' | 'tc' | 'tr' | 'ml' | 'mc' | 'mr' | 'bl' | 'bc' | 'br'
 */
function resizeCanvas(newW, newH, anchor = 'tl') {
    let ox = 0, oy = 0;
    if (resizeLibre) {
        ox = resizeOffsetX;
        oy = resizeOffsetY;
    } else {
        const dw = newW - paperWidth;
        const dh = newH - paperHeight;
        const col = anchor[1]; // 'l', 'c', 'r'
        const row = anchor[0]; // 't', 'm', 'b'
        if (col === 'c') ox = Math.round(dw / 2);
        else if (col === 'r') ox = dw;
        if (row === 'm') oy = Math.round(dh / 2);
        else if (row === 'b') oy = dh;
    }

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
    selectionOutlineCanvas.width = newW; selectionOutlineCanvas.height = newH;
    layersCacheCanvas.width = newW; layersCacheCanvas.height = newH;
    layersCacheDirty = true;

    // Ensure selection canvas matches
    if (selectionCanvas) {
        const newSel = document.createElement('canvas');
        newSel.width = newW; newSel.height = newH;
        const newSelCtx = newSel.getContext('2d');
        if (hasSelection) newSelCtx.drawImage(selectionCanvas, ox, oy);
        selectionCanvas = newSel; selCtx = newSelCtx;
    }
    updateSelectionOutline();

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
    if (!confirm(`Guardar proyecto en RANURA ${id}?`)) return;
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

    // Load all 10 slots in parallel from IndexedDB
    const db = await getDB();
    const projects = await Promise.all(
        [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15].map(i => new Promise(res => {
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
        thumbWrap.style.cssText = 'position:relative; width:100%; aspect-ratio:2/1; background:#e0e0e0; overflow:hidden;';

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

        // ── Footer: slot label + buttons ──
        const footer = document.createElement('div');
        footer.style.cssText = 'display:flex; flex-direction:column; align-items:center; gap:4px; padding:6px 6px 8px;';

        const slotLabel = document.createElement('span');
        slotLabel.textContent = `RANURA ${i}`;
        slotLabel.style.cssText = 'font-size:10px; font-weight:700; color:#555;';
        footer.appendChild(slotLabel);

        const btns = document.createElement('div');
        btns.style.cssText = 'display:flex; gap:4px; width:100%;';

        const saveBtn = document.createElement('button');
        saveBtn.textContent = 'GUARDAR';
        saveBtn.style.cssText = 'flex:1; padding:3px 0; font-size:9px; font-weight:700; border:none; border-radius:5px; cursor:pointer; background:#e8f5e9; color:#2e7d32;';
        saveBtn.onclick = () => saveToSlot(i);

        const loadBtn = document.createElement('button');
        loadBtn.textContent = 'CARGAR';
        loadBtn.style.cssText = `flex:1; padding:3px 0; font-size:9px; font-weight:700; border:none; border-radius:5px; cursor:pointer; background:#e3f2fd; color:#1565c0; opacity:${isEmpty ? 0.4 : 1}; pointer-events:${isEmpty ? 'none' : 'auto'};`;
        loadBtn.onclick = () => loadFromSlot(i);
        if (isEmpty) loadBtn.disabled = true;

        btns.appendChild(saveBtn);
        btns.appendChild(loadBtn);
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

    // Fit to Screen button
    fitScreenBtn = document.createElement('button');
    fitScreenBtn.id = 'fit-screen-btn';
    fitScreenBtn.className = 'indicator-extra-btn hidden';
    fitScreenBtn.textContent = 'ENCAJAR EN PANTALLA';
    fitScreenBtn.onclick = () => {
        const winW = canvas.width;
        const winH = canvas.height;
        viewScale = Math.min(winW / (paperWidth + 100), winH / (paperHeight + 100));
        viewPosX = 0;
        viewPosY = 0;
        viewRotation = 0;
        if (resetRotationBtn) resetRotationBtn.classList.add('hidden');
        requestRender();
    };
    container.appendChild(fitScreenBtn);

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

    // Shape From Center toggle
    shapeFromCenterBtn = document.createElement('button');
    shapeFromCenterBtn.id = 'shape-center-btn';
    shapeFromCenterBtn.className = 'indicator-extra-btn hidden';
    shapeFromCenterBtn.onclick = () => {
        const type = currentBrush.shapeType;
        if (type === 'rect') {
            shapeFromCenterRect = !shapeFromCenterRect;
        } else if (type === 'ellipse') {
            shapeFromCenterCircle = !shapeFromCenterCircle;
        }
        updateShapeFromCenterUI();
    };
    container.appendChild(shapeFromCenterBtn);

    // Shape Modifiable toggle
    shapeModifiableBtn = document.createElement('button');
    shapeModifiableBtn.id = 'shape-modifiable-btn';
    shapeModifiableBtn.className = 'indicator-extra-btn hidden';
    shapeModifiableBtn.onclick = () => {
        const type = currentBrush.shapeType;
        if (type === 'rect') shapeModifiableRect = !shapeModifiableRect;
        else if (type === 'ellipse') shapeModifiableCircle = !shapeModifiableCircle;
        else if (type === 'line') shapeModifiableLine = !shapeModifiableLine;
        updateShapeModifiableUI();
    };
    container.appendChild(shapeModifiableBtn);
}

function updateShapeFromCenterUI() {
    if (!shapeFromCenterBtn || !currentBrush) return;
    const type = currentBrush.shapeType;
    const active = (type === 'rect') ? shapeFromCenterRect : shapeFromCenterCircle;

    shapeFromCenterBtn.textContent = `DESDE CENTRO: ${active ? 'ON' : 'OFF'}`;
    shapeFromCenterBtn.style.background = active ? '#0066ff' : '';
    shapeFromCenterBtn.style.color = active ? 'white' : '';
}

function updateShapeModifiableUI() {
    if (!shapeModifiableBtn || !currentBrush) return;
    const type = currentBrush.shapeType;
    let active = false;
    if (type === 'rect') active = shapeModifiableRect;
    else if (type === 'ellipse') active = shapeModifiableCircle;
    else if (type === 'line') active = shapeModifiableLine;

    shapeModifiableBtn.textContent = `MODIFICABLE: ${active ? 'ON' : 'OFF'}`;
    shapeModifiableBtn.style.background = active ? '#0066ff' : '';
    shapeModifiableBtn.style.color = active ? 'white' : '';
    shapeModifiableBtn.style.display = 'block';
    shapeModifiableBtn.style.marginTop = '5px';
}

function showSelectionButtons(tool) {
    // Hide all extras first
    [lassoSelBtn, lassoDesBtn, modifySelBtn, clearSelBtn, shapeFillBtn, shapeFromCenterBtn, shapeModifiableBtn, fitScreenBtn].forEach(b => { if (b) b.classList.add('hidden'); });

    if (tool === 'lazo-sel') { if (lassoSelBtn) lassoSelBtn.classList.remove('hidden'); if (hasSelection && clearSelBtn) clearSelBtn.classList.remove('hidden'); }
    if (tool === 'lazo-des') { if (lassoDesBtn) lassoDesBtn.classList.remove('hidden'); if (hasSelection && clearSelBtn) clearSelBtn.classList.remove('hidden'); }
    if (tool === 'modify-sel') { if (modifySelBtn) modifySelBtn.classList.remove('hidden'); if (clearSelBtn) clearSelBtn.classList.remove('hidden'); }
    if (tool === 'bucket') { /* bucket panel handled by showBucketPanel() */ }
    
    if (tool === 'pincel' && currentBrush.isShape) {
        if (currentBrush.shapeType !== 'line') {
            if (shapeFillBtn) shapeFillBtn.classList.remove('hidden');
            if (shapeFromCenterBtn) {
                shapeFromCenterBtn.classList.remove('hidden');
                updateShapeFromCenterUI();
            }
        }
        if (shapeModifiableBtn) {
            shapeModifiableBtn.classList.remove('hidden');
            updateShapeModifiableUI();
        }
    }
    if (tool === 'zoom') { if (fitScreenBtn) fitScreenBtn.classList.remove('hidden'); }
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

// Helper to remove antialiasing from selection mask so scaling doesn't stretch translucent boundaries
function makeSelectionCrisp() {
    if (!selectionCanvas || !selCtx) return;
    const imgData = selCtx.getImageData(0, 0, paperWidth, paperHeight);
    const d = imgData.data;
    for (let i = 3; i < d.length; i += 4) {
        d[i] = d[i] > 127 ? 255 : 0;
    }
    selCtx.putImageData(imgData, 0, 0);
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
    
    makeSelectionCrisp();
    
    hasSelection = true;
    updateSelectionOutline();
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
    
    makeSelectionCrisp();
    
    // check if still anything selected
    const d = selCtx.getImageData(0, 0, paperWidth, paperHeight).data;
    hasSelection = d.some((v, i) => i % 4 === 3 && v > 0);
    updateSelectionOutline();
}

function clearSelection() {
    const wasSelection = hasSelection;
    if (selectionCanvas && selCtx) selCtx.clearRect(0, 0, paperWidth, paperHeight);
    hasSelection = false;
    // commit any pending modify
    if (modSelInitialized) commitModifySelection();
    modSelInitialized = false; modSelBounds = null; modSelOrigBounds = null;
    if (lassoSelBtn) lassoSelBtn.classList.remove('hidden'); // keep lasso btn visible if on that tool
    if (clearSelBtn) clearSelBtn.classList.add('hidden');
    showSelectionButtons(currentTool);
    updateSelectionOutline();
    if (wasSelection) pushHistory();
    requestRender();
}

function updateSelectionOutline() {
    if (!selectionOutlineCanvas || !selectionOutlineCtx) return;
    selectionOutlineCtx.clearRect(0, 0, paperWidth, paperHeight);

    if (!hasSelection || !selectionCanvas) return;

    selectionOutlineCtx.save();
    // Shift selection mask in 4 directions to construct outline
    selectionOutlineCtx.drawImage(selectionCanvas, 1, 0);
    selectionOutlineCtx.drawImage(selectionCanvas, -1, 0);
    selectionOutlineCtx.drawImage(selectionCanvas, 0, 1);
    selectionOutlineCtx.drawImage(selectionCanvas, 0, -1);

    // Subtract original selection to leave outer border
    selectionOutlineCtx.globalCompositeOperation = 'destination-out';
    selectionOutlineCtx.drawImage(selectionCanvas, 0, 0);

    // Color outline solid magenta
    selectionOutlineCtx.globalCompositeOperation = 'source-in';
    selectionOutlineCtx.fillStyle = '#ff00ff';
    selectionOutlineCtx.fillRect(0, 0, paperWidth, paperHeight);
    selectionOutlineCtx.restore();
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
    const bounds = getSelectionBounds();
    if (!bounds) return;

    modSelBounds = { ...bounds };
    modSelOrigBounds = { ...bounds };
    modSelCanvas = document.createElement('canvas');
    modSelCanvas.width = bounds.w; modSelCanvas.height = bounds.h;
    modSelCtx = modSelCanvas.getContext('2d');
    modSelLayersData = [];

    if (modifySelMode === 'capa') {
        const l = layers[selectedLayerIndex];
        const part = captureLayerSelection(l, bounds);
        modSelLayersData.push({ layer: l, canvas: part });
        modSelCtx.drawImage(part, 0, 0);
        l.ctx.save();
        l.ctx.globalCompositeOperation = 'destination-out';
        l.ctx.drawImage(selectionCanvas, 0, 0);
        l.ctx.restore();
    } else {
        layers.forEach(l => {
            if (!l.visible) return;
            const part = captureLayerSelection(l, bounds);
            modSelLayersData.push({ layer: l, canvas: part });
            modSelCtx.save();
            modSelCtx.globalAlpha = l.opacity;
            modSelCtx.globalCompositeOperation = l.blendMode;
            modSelCtx.drawImage(part, 0, 0);
            modSelCtx.restore();
            l.ctx.save();
            l.ctx.globalCompositeOperation = 'destination-out';
            l.ctx.drawImage(selectionCanvas, 0, 0);
            l.ctx.restore();
        });
    }
    modSelInitialized = true;
    modSelRotation = 0;
    modSelFlipX = 1;
    modSelFlipY = 1;
    updateThumbnails(); updateLayersUI();
}

function flipSelection(axis) {
    if (!modSelInitialized) return;
    if (axis === 'h') modSelFlipX *= -1;
    else modSelFlipY *= -1;
    requestRender();
}

function togglePerspectiveMode() {
    if (!modSelInitialized) return;
    modSelPerspectiveMode = !modSelPerspectiveMode;
    if (modSelPerspectiveMode) {
        initPerspectiveCorners();
        if (perspBtn) {
            perspBtn.style.background = 'rgba(80,130,255,0.9)';
            perspBtn.style.boxShadow = '0 0 12px rgba(80,130,255,0.6)';
        }
    } else {
        perspCorners = null;
        if (perspBtn) {
            perspBtn.style.background = 'rgba(30,30,40,0.9)';
            perspBtn.style.boxShadow = '';
        }
    }
    requestRender();
}

function initPerspectiveCorners() {
    if (!modSelBounds) return;
    const b = modSelBounds;
    const cx = b.x + b.w / 2, cy = b.y + b.h / 2;
    // Derive rotated corner positions from the current bounding box + rotation
    const corners = [
        { lx: b.x,       ly: b.y },
        { lx: b.x + b.w, ly: b.y },
        { lx: b.x,       ly: b.y + b.h },
        { lx: b.x + b.w, ly: b.y + b.h },
    ];
    perspCorners = corners.map(({ lx, ly }) => {
        const dx = lx - cx, dy = ly - cy;
        const cos = Math.cos(modSelRotation), sin = Math.sin(modSelRotation);
        return {
            x: cx + dx * cos - dy * sin,
            y: cy + dx * sin + dy * cos
        };
    });
}

function worldToScreen(wx, wy) {
    const paperX = wx - paperWidth / 2;
    const paperY = wy - paperHeight / 2;
    const cos = Math.cos(viewRotation);
    const sin = Math.sin(viewRotation);
    const rx = paperX * cos - paperY * sin;
    const ry = paperX * sin + paperY * cos;
    return {
        x: canvas.width / 2 + viewPosX + rx * viewScale,
        y: canvas.height / 2 + viewPosY + ry * viewScale
    };
}

function updateFlipButtonsPosition() {
    if (!modSelInitialized || !modSelBounds || !flipControls) {
        if (flipControls) flipControls.classList.add('hidden');
        return;
    }
    flipControls.classList.remove('hidden');
    const b = modSelBounds;
    // Position buttons near the rotation handle (top center)
    const handleDist = 40;
    const rotX = b.x + b.w / 2 + Math.sin(modSelRotation) * handleDist;
    const rotY = b.y - Math.cos(modSelRotation) * handleDist;

    // We want them to follow the top edge but offset a bit
    const screenPos = worldToScreen(b.x + b.w / 2, b.y - 100);
    flipControls.style.left = `${screenPos.x}px`;
    flipControls.style.top = `${screenPos.y}px`;
    flipControls.style.transform = `translate(-50%, -100%) rotate(${viewRotation}rad)`;
}

function captureLayerSelection(layer, bounds) {
    const part = document.createElement('canvas');
    part.width = bounds.w; part.height = bounds.h;
    const pctx = part.getContext('2d');
    pctx.drawImage(layer.canvas, -bounds.x, -bounds.y);
    pctx.globalCompositeOperation = 'destination-in';
    pctx.drawImage(selectionCanvas, -bounds.x, -bounds.y);
    return part;
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

// ─────────────────────────────────────────────────────────────
//  PERSPECTIVE WARP RENDERER (bilinear scanline)
// ─────────────────────────────────────────────────────────────
/**
 * Draws an affine-mapped triangle from the source image onto the canvas.
 * Expands the clipping path slightly to hide Canvas 2D antialiasing seams.
 */
function drawTexturedTriangle(ctx, img, u0, v0, u1, v1, u2, v2, x0, y0, x1, y1, x2, y2) {
    ctx.save();
    
    // 1. Create expanded clipping path to avoid seams (líneas entrecortadas)
    // The padding must scale inversely with viewScale so it always covers ~2 screen pixels
    const cx = (x0 + x1 + x2) / 3;
    const cy = (y0 + y1 + y2) / 3;
    const pad = 2.5 / (typeof viewScale !== 'undefined' ? viewScale : 1); 
    
    const ex = (x, y) => {
        const dx = x - cx, dy = y - cy;
        const dist = Math.hypot(dx, dy) || 1;
        // Push vertices away from centroid to slightly overlap adjacent triangles
        return [x + (dx / dist) * pad, y + (dy / dist) * pad];
    };
    
    const [px0, py0] = ex(x0, y0);
    const [px1, py1] = ex(x1, y1);
    const [px2, py2] = ex(x2, y2);

    ctx.beginPath();
    ctx.moveTo(px0, py0);
    ctx.lineTo(px1, py1);
    ctx.lineTo(px2, py2);
    ctx.closePath();
    ctx.clip();

    // 2. Compute the affine transformation matrix
    const det = (u0 - u2) * (v1 - v2) - (u1 - u2) * (v0 - v2);
    if (Math.abs(det) < 0.0001) { ctx.restore(); return; }
    
    const a = ((x0 - x2) * (v1 - v2) - (x1 - x2) * (v0 - v2)) / det;
    const b = ((y0 - y2) * (v1 - v2) - (y1 - y2) * (v0 - v2)) / det;
    const c = ((u0 - u2) * (x1 - x2) - (u1 - u2) * (x0 - x2)) / det;
    const d = ((u0 - u2) * (y1 - y2) - (u1 - u2) * (y0 - y2)) / det;
    const e = x0 - a * u0 - c * v0;
    const f = y0 - b * u0 - d * v0;

    // 3. Apply exact mathematical transform (multiplies current transform)
    ctx.transform(a, b, c, d, e, f);
    ctx.drawImage(img, 0, 0);
    ctx.restore();
}

/**
 * corners: [TL, TR, BL, BR] each {x, y} in destination world coords
 * Renders src canvas warped into the quadrilateral using a Grid Mesh.
 */
function renderPerspectiveWarpPreview(destCtx, srcCanvas, corners) {
    const [tl, tr, bl, br] = corners;
    const srcW = srcCanvas.width, srcH = srcCanvas.height;
    if (srcW < 1 || srcH < 1) return;

    // 10x10 Grid for high quality deformation
    const cols = 10;
    const rows = 10;
    
    // Bilinear interpolation to find coordinate inside the arbitrary quad
    const getPos = (u, v) => {
        const topX = tl.x + (tr.x - tl.x) * u;
        const topY = tl.y + (tr.y - tl.y) * u;
        const botX = bl.x + (br.x - bl.x) * u;
        const botY = bl.y + (br.y - bl.y) * u;
        return {
            x: topX + (botX - topX) * v,
            y: topY + (botY - topY) * v
        };
    };

    // Draw mesh triangles
    for (let j = 0; j < rows; j++) {
        for (let i = 0; i < cols; i++) {
            // UV coords in [0, 1]
            const u0 = i / cols, v0 = j / rows;
            const u1 = (i + 1) / cols, v1 = j / rows;
            const u2 = i / cols, v2 = (j + 1) / rows;
            const u3 = (i + 1) / cols, v3 = (j + 1) / rows;

            // Target coordinates
            const p0 = getPos(u0, v0); // TL
            const p1 = getPos(u1, v1); // TR
            const p2 = getPos(u2, v2); // BL
            const p3 = getPos(u3, v3); // BR

            // Source coordinates in pixels
            const srcU0 = u0 * srcW, srcV0 = v0 * srcH;
            const srcU1 = u1 * srcW, srcV1 = v1 * srcH;
            const srcU2 = u2 * srcW, srcV2 = v2 * srcH;
            const srcU3 = u3 * srcW, srcV3 = v3 * srcH;

            // Triangle 1: TL -> TR -> BL
            drawTexturedTriangle(
                destCtx, srcCanvas,
                srcU0, srcV0, srcU1, srcV1, srcU2, srcV2,
                p0.x, p0.y, p1.x, p1.y, p2.x, p2.y
            );

            // Triangle 2: BR -> BL -> TR
            drawTexturedTriangle(
                destCtx, srcCanvas,
                srcU3, srcV3, srcU2, srcV2, srcU1, srcV1,
                p3.x, p3.y, p2.x, p2.y, p1.x, p1.y
            );
        }
    }
}

/**
 * Applies perspective warp permanently onto target layer context(s).
 * corners: [TL, TR, BL, BR] world coords.
 */
function applyPerspectiveWarpToLayer(targetCtx, srcCanvas, corners) {
    const tmp = document.createElement('canvas');
    tmp.width = paperWidth; tmp.height = paperHeight;
    const tctx = tmp.getContext('2d');
    renderPerspectiveWarpPreview(tctx, srcCanvas, corners);
    targetCtx.drawImage(tmp, 0, 0);
}

function commitModifySelection() {
    if (!modSelInitialized || !modSelBounds) return;

    // ── Perspective warp commit ──
    if (modSelPerspectiveMode && perspCorners) {
        if (!isImportingNewImage && modSelLayersData.length > 0) {
            modSelLayersData.forEach(item => {
                item.layer.ctx.save();
                applyPerspectiveWarpToLayer(item.layer.ctx, item.canvas, perspCorners);
                item.layer.ctx.restore();
            });
        } else if (isImportingNewImage) {
            if (pasteInNewLayer && !isModifyingShape) {
                const lCanvas = document.createElement('canvas'); lCanvas.width = paperWidth; lCanvas.height = paperHeight;
                const lCtx = lCanvas.getContext('2d', { willReadFrequently: true });
                applyPerspectiveWarpToLayer(lCtx, modSelCanvas, perspCorners);
                const newLayer = { id: Date.now(), name: 'Imagen Importada', canvas: lCanvas, ctx: lCtx, visible: true, opacity: 1.0, thumbData: '', alphaLocked: false, clippingMask: false, blendMode: 'source-over' };
                layers.splice(selectedLayerIndex + 1, 0, newLayer); selectedLayerIndex++;
            } else {
                const target = layers[selectedLayerIndex].ctx;
                target.save();
                if (layers[selectedLayerIndex].alphaLocked) target.globalCompositeOperation = 'source-atop';
                applyPerspectiveWarpToLayer(target, modSelCanvas, perspCorners);
                target.restore();
            }
            isImportingNewImage = false;
        }
        // Reset perspective state
        modSelPerspectiveMode = false; perspCorners = null;
        if (perspBtn) { perspBtn.style.background = 'rgba(30,30,40,0.9)'; perspBtn.style.boxShadow = ''; }
        modSelInitialized = false; modSelCanvas = null; modSelBounds = null; modSelOrigBounds = null;
        modSelRotation = 0; modSelFlipX = 1; modSelFlipY = 1; modSelLayersData = [];
        if (flipControls) flipControls.classList.add('hidden');
        updateThumbnails(); updateLayersUI(); pushHistory();
        return;
    }

    if (isImportingNewImage) {
        if (pasteInNewLayer && !isModifyingShape) {
            // Create the new layer for the imported image
            const lCanvas = document.createElement('canvas');
            lCanvas.width = paperWidth; lCanvas.height = paperHeight;
            const lCtx = lCanvas.getContext('2d', { willReadFrequently: true });

            const b = modSelBounds;
            lCtx.save();
            lCtx.imageSmoothingEnabled = true;
            lCtx.imageSmoothingQuality = 'high';
            const cx = b.x + b.w / 2;
            const cy = b.y + b.h / 2;
            lCtx.translate(cx, cy);
            lCtx.rotate(modSelRotation);
            lCtx.scale(modSelFlipX, modSelFlipY);
            lCtx.translate(-cx, -cy);
            lCtx.drawImage(modSelCanvas, Math.round(b.x), Math.round(b.y), Math.round(b.w), Math.round(b.h));
            lCtx.restore();

            const newLayer = {
                id: Date.now(),
                name: "Imagen Importada",
                canvas: lCanvas,
                ctx: lCtx,
                visible: true,
                opacity: 1.0,
                thumbData: '',
                alphaLocked: false,
                clippingMask: false,
                blendMode: 'source-over'
            };
            layers.splice(selectedLayerIndex + 1, 0, newLayer);
            selectedLayerIndex++;
        } else {
            // Draw directly onto the current active layer
            const target = layers[selectedLayerIndex].ctx;
            const b = modSelBounds;
            target.save();
            target.imageSmoothingEnabled = true;
            target.imageSmoothingQuality = 'high';
            if (layers[selectedLayerIndex].alphaLocked) target.globalCompositeOperation = 'source-atop';
            const cx = b.x + b.w / 2;
            const cy = b.y + b.h / 2;
            target.translate(cx, cy);
            target.rotate(modSelRotation);
            target.scale(modSelFlipX, modSelFlipY);
            target.translate(-cx, -cy);
            target.drawImage(modSelCanvas, Math.round(b.x), Math.round(b.y), Math.round(b.w), Math.round(b.h));
            target.restore();
        }
        isImportingNewImage = false;
    } else {
        if (modSelLayersData.length === 0) return;
        const b = modSelBounds;
        modSelLayersData.forEach(item => {
            const target = item.layer.ctx;
            target.save();
            target.imageSmoothingEnabled = true;
            target.imageSmoothingQuality = 'high';
            const cx = b.x + b.w / 2;
            const cy = b.y + b.h / 2;
            target.translate(cx, cy);
            target.rotate(modSelRotation);
            target.scale(modSelFlipX, modSelFlipY);
            target.translate(-cx, -cy);
            target.drawImage(item.canvas, Math.round(b.x), Math.round(b.y), Math.round(b.w), Math.round(b.h));
            target.restore();
        });
    }

    modSelInitialized = false; modSelCanvas = null; modSelBounds = null; modSelOrigBounds = null;
    modSelRotation = 0; modSelFlipX = 1; modSelFlipY = 1;
    modSelLayersData = [];
    if (flipControls) flipControls.classList.add('hidden');
    updateThumbnails(); updateLayersUI();
    pushHistory();
    
    if (isModifyingShape) {
        isModifyingShape = false;
        selectTool('pincel', 'Pincel');
    }
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

    if (bgMode === 1) {
        fctx.fillStyle = solidBgColor;
        fctx.fillRect(0, 0, paperWidth, paperHeight);
    }

    compositeLayers(fctx);
    return flat;
}

function downloadImage() {
    const flat = getFlatImage();
    const link = document.createElement('a');

    const now = new Date();
    const pad = (n) => n.toString().padStart(2, '0');
    const dateStr = `${now.getFullYear()}${pad(now.getMonth() + 1)}${pad(now.getDate())}`;
    const timeStr = `${pad(now.getHours())}${pad(now.getMinutes())}${pad(now.getSeconds())}`;

    link.download = `ilustracion_${dateStr}_${timeStr}.png`;
    link.href = flat.toDataURL('image/png');
    link.click();
}

function handleIncomingFile(file) {
    if (!file || !file.type.startsWith('image/')) return;
    const reader = new FileReader();
    reader.onload = (ev) => {
        const img = new Image();
        img.onload = () => {
            if (startupImportState === 1 || layers.length === 0) {
                // If we are at startup or have no layers, start app with this image
                startApp(img.width, img.height, img);
                resetImportButton();
                if (layerImportState === 1) resetLayerImportButton();
            } else {
                // App already running, import as new layer
                importAsNewLayer(img);
                if (layerImportState === 1) resetLayerImportButton();
            }
        };
        img.src = ev.target.result;
    };
    reader.readAsDataURL(file);
}

function importAsNewLayer(img) {
    if (modSelInitialized) commitModifySelection();
    endPushSession();
    clearSelection();

    // Position at the center of the current screen view
    const viewCenter = screenToWorld(canvas.width / 2, canvas.height / 2);
    const x = Math.round(viewCenter.x - img.width / 2);
    const y = Math.round(viewCenter.y - img.height / 2);

    // Initial transformation setup (No cropping!)
    modSelCanvas = document.createElement('canvas');
    modSelCanvas.width = img.width;
    modSelCanvas.height = img.height;
    modSelCtx = modSelCanvas.getContext('2d');
    modSelCtx.drawImage(img, 0, 0);

    modSelBounds = { x, y, w: img.width, h: img.height };
    modSelOrigBounds = { ...modSelBounds };
    modSelRotation = 0;
    modSelFlipX = 1;
    modSelFlipY = 1;
    modSelLayersData = [];
    isImportingNewImage = true;
    modSelInitialized = true;

    // Trigger Modify Selection mode immediately
    selectTool('modify-sel', 'Modificar Selección');
    // initModifySelection is NOT needed because we manually initialized above

    updateThumbnails(); updateLayersUI();
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
    if (!hasSelection) { alert("Selecciona un área primero para copiar."); return false; }
    const bounds = getSelectionBounds();
    if (!bounds) return false;
    internalClipboardBounds = { ...bounds };

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

    return new Promise((resolve) => {
        temp.toBlob(async blob => {
            try {
                const item = new ClipboardItem({ "image/png": blob });
                await navigator.clipboard.write([item]);
                console.log("Copiado al portapapeles");
                resolve(true);
            } catch (err) { 
                alert("Error al copiar: " + err); 
                resolve(false);
            }
        }, 'image/png');
    });
}

async function cutToClipboard() {
    if (!hasSelection) { alert("Selecciona un área primero para cortar."); return; }
    if (modSelInitialized) { alert("Aplica la modificación antes de cortar."); return; }

    const success = await copyToClipboard();
    if (success) {
        const l = layers[selectedLayerIndex];
        l.ctx.save();
        l.ctx.globalCompositeOperation = 'destination-out';
        l.ctx.drawImage(selectionCanvas, 0, 0);
        l.ctx.restore();
        clearSelection(); // Remove selection mask after deletion
        updateThumbnails(); updateLayersUI();
        pushHistory();
    }
}

async function pasteFromClipboard(pasteInPlace = false) {
    clearSelection();
    try {
        const items = await navigator.clipboard.read();
        for (const item of items) {
            for (const type of item.types) {
                if (type.startsWith('image/')) {
                    const blob = await item.getType(type);
                    const img = new Image();
                    img.src = URL.createObjectURL(blob);
                    img.onload = () => {
                        // Position top-left of image at the center of the current screen view
                        const viewCenter = screenToWorld(canvas.width / 2, canvas.height / 2);
                        let x = Math.round(viewCenter.x - img.width / 2);
                        let y = Math.round(viewCenter.y - img.height / 2);

                        if (pasteInPlace && internalClipboardBounds && internalClipboardBounds.w === img.width && internalClipboardBounds.h === img.height) {
                            x = internalClipboardBounds.x;
                            y = internalClipboardBounds.y;
                        }

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
                            updateSelectionOutline();

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
                            updateSelectionOutline();

                            // Construir el canvas fantasma directamente con la imagen
                            modSelCanvas = document.createElement('canvas');
                            modSelCanvas.width = img.width;
                            modSelCanvas.height = img.height;
                            modSelCtx = modSelCanvas.getContext('2d');
                            modSelCtx.drawImage(img, 0, 0);

                            // Definir límites del fantasma
                            modSelBounds = { x, y, w: img.width, h: img.height };
                            modSelOrigBounds = { ...modSelBounds };

                            // IMPORTANTE: Registrar la capa y el canvas para que commitModifySelection sepa dónde guardar
                            modSelLayersData = [{ layer: layers[selectedLayerIndex], canvas: modSelCanvas }];

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
const HANDLE_R = 10; // visual radius in world px
function getModifyHandle(wx, wy) {
    if (!modSelBounds) return null;
    const hitR = 15 / viewScale;

    // ── Perspective mode: only 4 corner handles + interior move ──
    if (modSelPerspectiveMode && perspCorners) {
        for (let ci = 0; ci < 4; ci++) {
            if (Math.hypot(wx - perspCorners[ci].x, wy - perspCorners[ci].y) <= hitR) return `pc${ci}`;
        }
        // Check if inside perspective quad (simple bounding box of corners)
        const xs = perspCorners.map(c => c.x), ys = perspCorners.map(c => c.y);
        if (wx >= Math.min(...xs) && wx <= Math.max(...xs) && wy >= Math.min(...ys) && wy <= Math.max(...ys)) return 'move';
        return null;
    }

    const b = modSelBounds;
    const cx = b.x + b.w / 2;
    const cy = b.y + b.h / 2;

    // 1. Check handles
    const handlePositions = {
        tl: [b.x, b.y],
        tc: [b.x + b.w / 2, b.y],
        tr: [b.x + b.w, b.y],
        ml: [b.x, b.y + b.h / 2],
        mr: [b.x + b.w, b.y + b.h / 2],
        bl: [b.x, b.y + b.h],
        bc: [b.x + b.w / 2, b.y + b.h],
        br: [b.x + b.w, b.y + b.h],
    };

    for (const [k, [hx, hy]] of Object.entries(handlePositions)) {
        const dx = hx - cx, dy = hy - cy;
        const rx = dx * Math.cos(modSelRotation) - dy * Math.sin(modSelRotation);
        const ry = dx * Math.sin(modSelRotation) + dy * Math.cos(modSelRotation);
        if (Math.hypot(wx - (cx + rx), wy - (cy + ry)) <= hitR) return k;
    }

    // 2. Check rotation handle
    const rotDist = 40 / viewScale;
    const dxL = (b.x + b.w / 2) - cx, dyL = b.y - rotDist - cy;
    const rxL = dxL * Math.cos(modSelRotation) - dyL * Math.sin(modSelRotation);
    const ryL = dxL * Math.sin(modSelRotation) + dyL * Math.cos(modSelRotation);
    if (Math.hypot(wx - (cx + rxL), wy - (cy + ryL)) <= hitR * 1.5) return 'rot';

    // 3. Check if inside bounds
    const dx = wx - cx, dy = wy - cy;
    const invCos = Math.cos(-modSelRotation), invSin = Math.sin(-modSelRotation);
    const localX = dx * invCos - dy * invSin + cx;
    const localY = dx * invSin + dy * invCos + cy;

    if (localX >= b.x && localX <= b.x + b.w && localY >= b.y && localY <= b.y + b.h) return 'move';
    return null;
}

function applyModifyDrag(dx, dy, handle, origB, shiftKey = false, worldX = 0, worldY = 0) {
    const b = { ...origB };
    if (handle === 'rot') {
        const cx = b.x + b.w / 2;
        const cy = b.y + b.h / 2;
        let angle = Math.atan2(worldY - cy, worldX - cx) + Math.PI / 2;
        if (shiftKey) {
            const snap = Math.PI / 4; // 45 degrees
            angle = Math.round(angle / snap) * snap;
        }
        modSelRotation = angle;
        return b;
    }
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

    if (shiftKey && handle !== 'move') {
        const ratio = origB.w / (origB.h || 1);
        const dw = Math.abs(b.w - origB.w);
        const dh = Math.abs(b.h - origB.h);

        if (dw / origB.w > dh / (origB.h || 1)) {
            b.h = b.w / ratio;
        } else {
            b.w = b.h * ratio;
        }

        // Adjust position based on anchor to keep scaling intuitive
        if (handle === 'tl') { b.x = origB.x + (origB.w - b.w); b.y = origB.y + (origB.h - b.h); }
        else if (handle === 'tc') { b.x = origB.x + (origB.w - b.w) / 2; b.y = origB.y + (origB.h - b.h); }
        else if (handle === 'tr') { b.y = origB.y + (origB.h - b.h); }
        else if (handle === 'ml') { b.x = origB.x + (origB.w - b.w); b.y = origB.y + (origB.h - b.h) / 2; }
        else if (handle === 'mr') { b.y = origB.y + (origB.h - b.h) / 2; }
        else if (handle === 'bl') { b.x = origB.x + (origB.w - b.w); }
        else if (handle === 'bc') { b.x = origB.x + (origB.w - b.w) / 2; }
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

    let ox = 0, oy = 0;
    if (resizeLibre) {
        ox = resizeOffsetX;
        oy = resizeOffsetY;
    } else {
        const dw = nw - paperWidth;
        const dh = nh - paperHeight;
        const col = resizeAnchor[1];
        const row = resizeAnchor[0];
        if (col === 'c') ox = Math.round(dw / 2);
        else if (col === 'r') ox = dw;
        if (row === 'm') oy = Math.round(dh / 2);
        else if (row === 'b') oy = dh;
    }

    const x0 = -ox, y0 = -oy;

    // Check if inside the area for moving
    if (wx >= x0 && wx <= x0 + nw && wy >= y0 && wy <= y0 + nh) {
        // If it's not a handle, it's a move
        const handles = {
            tl: [x0, y0], tc: [x0 + nw / 2, y0], tr: [x0 + nw, y0],
            ml: [x0, y0 + nh / 2], mr: [x0 + nw, y0 + nh / 2],
            bl: [x0, y0 + nh], bc: [x0 + nw / 2, y0 + nh], br: [x0 + nw, y0 + nh],
        };
        // Hit radius: 20 screen pixels for canvas resize (crucial for usability)
        const hitR = 20 / viewScale;
        for (const [k, [hx, hy]] of Object.entries(handles)) {
            if (Math.hypot(wx - hx, wy - hy) <= hitR) return k;
        }
        return 'move';
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
    const finalW = Math.max(1, Math.min(8000, Math.round(nw)));
    const finalH = Math.max(1, Math.min(8000, Math.round(nh)));

    // Calculate how much the offsets should change to keep opposite edges pinned
    let dox = 0, doy = 0;
    if (handle.includes('l')) dox = finalW - origW;
    if (handle.includes('t')) doy = finalH - origH;

    return { nw: finalW, nh: finalH, dox, doy };
}

// ─────────────────────────────────────────────────────────────
//  CANVAS SETUP
// ─────────────────────────────────────────────────────────────
function createCheckerPattern() {
    checkerPatternLightCanvas.width = 20; checkerPatternLightCanvas.height = 20;
    const pctx1 = checkerPatternLightCanvas.getContext('2d');
    pctx1.fillStyle = '#ffffff'; pctx1.fillRect(0, 0, 20, 20);
    pctx1.fillStyle = '#f0f0f0'; pctx1.fillRect(0, 0, 10, 10); pctx1.fillRect(10, 10, 10, 10);
    checkerPatternLight = ctx.createPattern(checkerPatternLightCanvas, 'repeat');

    checkerPatternDarkCanvas.width = 20; checkerPatternDarkCanvas.height = 20;
    const pctx2 = checkerPatternDarkCanvas.getContext('2d');
    pctx2.fillStyle = '#2a2a2a'; pctx2.fillRect(0, 0, 20, 20);
    pctx2.fillStyle = '#3a3a3a'; pctx2.fillRect(0, 0, 10, 10); pctx2.fillRect(10, 10, 10, 10);
    checkerPatternDark = ctx.createPattern(checkerPatternDarkCanvas, 'repeat');
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
    requestRender();
}
function setupLogicalCanvas(initialImg) {
    strokeCanvas.width = paperWidth; strokeCanvas.height = paperHeight;
    groupCanvas.width = paperWidth; groupCanvas.height = paperHeight;
    maskBuffer.width = paperWidth; maskBuffer.height = paperHeight;
    selectionOutlineCanvas.width = paperWidth; selectionOutlineCanvas.height = paperHeight;
    layersCacheCanvas.width = paperWidth; layersCacheCanvas.height = paperHeight;
    layersCacheDirty = true;
    updateSelectionOutline();
    layers = []; addLayer("Capa 1");
    if (initialImg) layers[0].ctx.drawImage(initialImg, 0, 0);
    updateThumbnails();
}

// ─────────────────────────────────────────────────────────────
//  PALETTE
// ─────────────────────────────────────────────────────────────
function initPalette() {
    const saved = localStorage.getItem('illustrator_palette_v2');
    if (saved) {
        try {
            paletteColors = JSON.parse(saved);
            paletteRows = Math.max(5, Math.ceil(paletteColors.length / paletteCols));
        } catch (e) { paletteColors = Array(paletteRows * paletteCols).fill(null).map(() => ({ c: null, s: null })); }
    } else {
        // Try to migrate from old format
        const old = localStorage.getItem('illustrator_palette');
        if (old) {
            try {
                const colors = JSON.parse(old);
                paletteColors = colors.map(c => ({ c: c, s: null }));
                paletteRows = Math.max(5, Math.ceil(paletteColors.length / paletteCols));
            } catch (e) { paletteColors = Array(paletteRows * paletteCols).fill(null).map(() => ({ c: null, s: null })); }
        } else {
            paletteColors = Array(paletteRows * paletteCols).fill(null).map(() => ({ c: null, s: null }));
        }
    }
    renderPalette();
}
function renderPalette() {
    paletteGrid.innerHTML = '';
    paletteColors.forEach((item, index) => {
        const cell = document.createElement('div'); cell.className = 'palette-cell';
        if (item && item.c) cell.style.background = item.c;

        if (item && item.s) {
            const badge = document.createElement('div');
            badge.className = 'palette-shortcut-badge';
            badge.textContent = item.s.toUpperCase();
            cell.appendChild(badge);
        }

        cell.onclick = () => {
            if (isAddingToPalette) {
                paletteColors[index].c = selectedColor;
                isAddingToPalette = false;
                addToPaletteBtn.classList.remove('active-waiting');
                checkAndExpandPalette(index);
                savePalette();
                renderPalette();
            }
            else if (item && item.c) { selectedColor = item.c; mainColorPicker.value = item.c; updateTintedTexture(); }
        };

        cell.oncontextmenu = (e) => { e.preventDefault(); showColorContextMenu(e.clientX, e.clientY, index); };
        paletteGrid.appendChild(cell);
    });
}
function savePalette() { localStorage.setItem('illustrator_palette_v2', JSON.stringify(paletteColors)); }
function checkAndExpandPalette(index) { if (Math.floor(index / paletteCols) === paletteRows - 1) { paletteRows++; paletteColors = paletteColors.concat(Array(paletteCols).fill(null).map(() => ({ c: null, s: null }))); } }
function showColorContextMenu(x, y, index) {
    const old = document.querySelector('.ctx-menu'); if (old) old.remove();
    const menu = document.createElement('div'); menu.className = 'ctx-menu'; menu.style.left = x + 'px'; menu.style.top = y + 'px';
    const item = paletteColors[index];

    if (item && item.c) {
        const cp = document.createElement('div'); cp.className = 'ctx-item'; cp.textContent = `Copiar ${item.c}`;
        cp.onclick = () => { if (navigator.clipboard) navigator.clipboard.writeText(item.c); menu.remove(); };
        menu.appendChild(cp);

        const sh = document.createElement('div'); sh.className = 'ctx-item'; sh.textContent = 'Asignar Atajo';
        sh.onclick = () => {
            const key = prompt(`Asignar atajo a este color (Tecla única):`, item.s || "");
            if (key !== null) {
                const lowKey = key.trim().toLowerCase().slice(0, 1);
                if (lowKey) checkAndAssignColorShortcut(index, lowKey);
                else { paletteColors[index].s = null; savePalette(); renderPalette(); }
            }
            menu.remove();
        };
        menu.appendChild(sh);
    }

    const del = document.createElement('div'); del.className = 'ctx-item delete'; del.textContent = 'Eliminar';
    del.onclick = () => { paletteColors[index] = { c: null, s: null }; checkAndShrinkPalette(); savePalette(); renderPalette(); menu.remove(); }; menu.appendChild(del);
    document.body.appendChild(menu); document.addEventListener('click', () => menu.remove(), { once: true });
}

function checkAndAssignColorShortcut(index, key) {
    const ms = (mainShortcutInput?.value || '').toLowerCase(), bs = (brushShortcutInput?.value || '').toLowerCase(), ls = (layersShortcutInput?.value || '').toLowerCase(), cs = (colorsShortcutInput?.value || '').toLowerCase();
    let conflict = key === ms ? 'Atajo Principal' : key === bs ? 'Atajo Pincel' : key === ls ? 'Atajo Capas' : key === cs ? 'Atajo Colores' : null;

    const tc = toolsData.find(t => (t.shortcut || '').toLowerCase() === key);
    const bc = brushTypesData.find(b => (b.shortcut || '').toLowerCase() === key);
    const cc = paletteColors.find((p, idx) => (p.s || '').toLowerCase() === key && idx !== index);

    if (tc) conflict = tc.name;
    else if (bc) conflict = bc.name;
    else if (cc) conflict = `Color en paleta (${cc.c})`;

    if (conflict) {
        if (confirm(`La tecla "${key.toUpperCase()}" ya está siendo usada por "${conflict}". ¿Quieres sobrescribirla?`)) {
            if (key === ms && mainShortcutInput) mainShortcutInput.value = '';
            if (key === bs && brushShortcutInput) brushShortcutInput.value = '';
            if (key === ls && layersShortcutInput) layersShortcutInput.value = '';
            if (key === cs && colorsShortcutInput) colorsShortcutInput.value = '';
            if (tc) tc.shortcut = '';
            if (bc) bc.shortcut = '';
            if (cc) cc.s = null;

            paletteColors[index].s = key;
            savePalette(); saveShortcuts(); renderPalette();
            setupMultiToolMenu(); setupBrushMenu();
        }
    } else {
        paletteColors[index].s = key;
        savePalette(); renderPalette();
    }
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
    if (name === "Nueva Capa" || name === "Capa 1") {
        let max = 0;
        for (const l of layers) {
            const m = l.name.match(/^Capa (\d+)$/i);
            if (m) {
                const num = parseInt(m[1], 10);
                if (num > max) max = num;
            }
        }
        if (globalLayerCounter <= max) globalLayerCounter = max + 1;
        name = "Capa " + globalLayerCounter;
        globalLayerCounter++;
    }
    endPushSession();
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

/**
 * Selecciona todo el contenido de la capa activa y activa la herramienta
 * "Modificar Selección" para que el usuario pueda mover / transformar la capa.
 */
function moveLayerContent() {
    if (layers.length === 0 || selectedLayerIndex < 0 || selectedLayerIndex >= layers.length) return;

    // Reset any existing modify-sel session
    if (currentTool === 'modify-sel' && modSelInitialized) commitModifySelection();

    // Fill the selection canvas with a full-canvas white rectangle
    ensureSelectionCanvas();
    selCtx.clearRect(0, 0, paperWidth, paperHeight);
    selCtx.fillStyle = 'white';
    selCtx.fillRect(0, 0, paperWidth, paperHeight);
    hasSelection = true;
    updateSelectionOutline();

    // Switch to 'capa' mode so only this layer's pixels move
    modifySelMode = 'capa';

    // Activate Modificar Selección immediately
    selectTool('modify-sel', 'Modificar Selección');
    initModifySelection();

    requestRender();
}

function duplicateSelectedLayer() {
    if (layers.length === 0 || selectedLayerIndex < 0 || selectedLayerIndex >= layers.length) return;
    endPushSession();
    const current = layers[selectedLayerIndex];
    const lCanvas = document.createElement('canvas'); lCanvas.width = paperWidth; lCanvas.height = paperHeight;
    const lCtx = lCanvas.getContext('2d', { willReadFrequently: true });
    lCtx.drawImage(current.canvas, 0, 0);
    const newLayer = {
        id: Date.now(),
        name: current.name + " copia",
        canvas: lCanvas,
        ctx: lCtx,
        visible: current.visible,
        opacity: current.opacity,
        thumbData: current.thumbData,
        alphaLocked: current.alphaLocked,
        clippingMask: current.clippingMask,
        blendMode: current.blendMode
    };
    layers.splice(selectedLayerIndex + 1, 0, newLayer);
    selectedLayerIndex++;
    updateThumbnails(); updateLayersUI();
    pushHistory();
}

function updateBgUI() {
    const btnIcon = document.getElementById('toggle-bg-icon');
    if (btnIcon) btnIcon.src = `iconos acciones de capas/modo ${bgMode}.png`;
    const btn = document.getElementById('toggle-bg-btn');
    if (btn) btn.title = bgMode === 1 ? "Fondo sólido (Click derecho para color)" : (bgMode === 2 ? "Fondo transparente (Oscuro)" : "Fondo transparente (Claro)");
}

function toggleBackground() {
    bgMode = bgMode === 1 ? 2 : (bgMode === 2 ? 3 : 1);
    updateBgUI();
    requestRender();
}
function mergeLayerDown(index) {
    if (index <= 0) return;
    endPushSession();
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
    pushHistory();
}

function updateThumbnails() {
    layersCacheDirty = true;
    layers.forEach(l => {
        const thumbCanvas = document.createElement('canvas');
        thumbCanvas.width = 40;
        thumbCanvas.height = 30;
        const tctx = thumbCanvas.getContext('2d');
        tctx.drawImage(l.canvas, 0, 0, 40, 30);
        l.thumbData = thumbCanvas.toDataURL();
    });
}

function updateLayersUI() {
    if (!layersList) return;

    const posSpan = document.getElementById('layer-status-pos');
    const nameSpan = document.getElementById('layer-status-name');
    if (posSpan && nameSpan && layers[selectedLayerIndex]) {
        posSpan.textContent = `${selectedLayerIndex + 1}/${layers.length}`;
        nameSpan.textContent = layers[selectedLayerIndex].name;
    }
    if (window._syncQuickLayerBtns) window._syncQuickLayerBtns();

    layersList.innerHTML = '';
    for (let i = layers.length - 1; i >= 0; i--) {
        const l = layers[i];
        const li = document.createElement('li');
        li.className = 'layer-item' + (i === selectedLayerIndex ? ' active-layer' : '');
        li.dataset.index = i;
        const mainInfo = document.createElement('div');
        mainInfo.className = 'layer-main-info';
        const thumb = document.createElement('div');
        thumb.className = 'layer-thumbnail';
        if (l.thumbData) {
            const thumbImg = document.createElement('img');
            thumbImg.src = l.thumbData;
            thumbImg.style.cssText = 'width:100%;height:100%;object-fit:cover;display:block;';
            thumbImg.draggable = false; // prevent browser's native image drag
            thumbImg.ondragstart = () => false;
            thumb.appendChild(thumbImg);
        }
        mainInfo.appendChild(thumb);
        const nameSpan = document.createElement('span');
        nameSpan.className = 'layer-name';
        nameSpan.textContent = l.name;
        nameSpan.ondblclick = (e) => {
            e.stopPropagation();
            const input = document.createElement('input');
            input.type = 'text';
            input.value = l.name;
            input.style.cssText = 'width: 80px; font-size: 11px; padding: 2px; border: 1px solid #007bff; border-radius: 3px; margin-left: 5px;';
            const saveName = () => {
                if (input.value.trim() !== '') {
                    l.name = input.value.trim();
                }
                updateLayersUI();
                pushHistory();
            };
            input.onblur = saveName;
            input.onkeydown = (ev) => { if (ev.key === 'Enter') { ev.preventDefault(); saveName(); } };
            mainInfo.replaceChild(input, nameSpan);
            input.focus();
            input.select();
        };
        mainInfo.appendChild(nameSpan);
        li.appendChild(mainInfo);
        const controls = document.createElement('div');
        controls.className = 'layer-controls';
        
        // Evitar que el drag and drop se active al usar el slider de opacidad u otros controles
        controls.onmousedown = () => { li.draggable = false; };
        controls.onmouseup = () => { li.draggable = true; };
        controls.onmouseleave = () => { li.draggable = true; };

        const opacitySlider = document.createElement('input');
        opacitySlider.type = 'range';
        opacitySlider.className = 'layer-opacity-slider';
        opacitySlider.min = 0;
        opacitySlider.max = 100;
        opacitySlider.value = Math.round(l.opacity * 100);
        opacitySlider.oninput = () => { l.opacity = opacitySlider.value / 100; layersCacheDirty = true; requestRender(); };
        opacitySlider.onchange = (e) => { pushHistory(); e.target.blur(); };
        controls.appendChild(opacitySlider);
        const buttons = document.createElement('div');
        buttons.className = 'layer-buttons';
        const visBtn = document.createElement('button');
        visBtn.className = 'mini-tool-btn' + (l.visible ? '' : ' status-invisible');
        visBtn.title = 'Visible';
        visBtn.innerHTML = '<img src="simbolo ojo abierto.png">';
        visBtn.onclick = (e) => { e.stopPropagation(); l.visible = !l.visible; layersCacheDirty = true; updateThumbnails(); updateLayersUI(); pushHistory(); requestRender(); };
        buttons.appendChild(visBtn);
        const lockBtn = document.createElement('button');
        lockBtn.className = 'mini-tool-btn' + (l.alphaLocked ? ' status-alpha' : '');
        lockBtn.title = 'Bloquear Alpha';
        lockBtn.innerHTML = '<img src="Simbolo alpha.png">';
        lockBtn.onclick = (e) => { e.stopPropagation(); l.alphaLocked = !l.alphaLocked; updateLayersUI(); pushHistory(); };
        buttons.appendChild(lockBtn);
        const clipBtn = document.createElement('button');
        clipBtn.className = 'mini-tool-btn' + (l.clippingMask ? ' status-clipping' : '');
        clipBtn.title = 'Máscara de Recorte';
        clipBtn.innerHTML = '<img src="Simbolo mascara de recorte.png">';
        clipBtn.onclick = (e) => { e.stopPropagation(); l.clippingMask = !l.clippingMask; layersCacheDirty = true; updateLayersUI(); pushHistory(); requestRender(); };
        buttons.appendChild(clipBtn);
        const mergeBtn = document.createElement('button');
        mergeBtn.className = 'mini-tool-btn';
        mergeBtn.title = 'Combinar con la de abajo';
        mergeBtn.innerHTML = '<img src="simbolo combinar con el de abajo.png">';
        mergeBtn.onclick = (e) => { e.stopPropagation(); mergeLayerDown(i); updateThumbnails(); updateLayersUI(); };
        buttons.appendChild(mergeBtn);
        const delBtn = document.createElement('button');
        delBtn.className = 'mini-tool-btn delete';
        delBtn.title = 'Borrar';
        delBtn.textContent = '×';
        delBtn.onclick = (e) => {
            e.stopPropagation();
            if (layers.length <= 1) return;
            layers.splice(i, 1);
            if (selectedLayerIndex >= layers.length) selectedLayerIndex = layers.length - 1;
            updateThumbnails();
            updateLayersUI();
            pushHistory();
            requestRender();
        };
        buttons.appendChild(delBtn);
        controls.appendChild(buttons);
        const blendSelect = document.createElement('select');
        blendSelect.className = 'layer-blend-select';
        blendModes.forEach(bm => {
            const opt = document.createElement('option');
            opt.value = bm.value;
            opt.textContent = bm.label;
            if (bm.value === l.blendMode) opt.selected = true;
            blendSelect.appendChild(opt);
        });
        blendSelect.onchange = () => { l.blendMode = blendSelect.value; layersCacheDirty = true; pushHistory(); requestRender(); };
        controls.appendChild(blendSelect);
        li.appendChild(controls);
        li.onclick = () => {
            if (selectedLayerIndex !== i) {
                endPushSession();
                selectedLayerIndex = i;
                updateLayersUI();
                pushHistory();
                requestRender();
            }
        };

        // ── Drag-and-drop reordering ──
        li.draggable = true;
        li.addEventListener('dragstart', (e) => {
            isDraggingLayer = true;
            e.dataTransfer.effectAllowed = 'move';
            e.dataTransfer.setData('text/plain', i);
            setTimeout(() => li.classList.add('dragging'), 0);
        });
        li.addEventListener('dragend', () => {
            isDraggingLayer = false;
            li.classList.remove('dragging');
            document.querySelectorAll('.layer-item.drag-over').forEach(el => el.classList.remove('drag-over'));
        });
        li.addEventListener('dragover', (e) => {
            e.preventDefault();
            e.dataTransfer.dropEffect = 'move';
            document.querySelectorAll('.layer-item.drag-over').forEach(el => el.classList.remove('drag-over'));
            li.classList.add('drag-over');
        });
        li.addEventListener('dragleave', () => {
            li.classList.remove('drag-over');
        });
        li.addEventListener('drop', (e) => {
            e.preventDefault();
            li.classList.remove('drag-over');
            const fromIndex = parseInt(e.dataTransfer.getData('text/plain'));
            const toIndex = parseInt(li.dataset.index);
            if (fromIndex === toIndex) return;

            // Move layer in the array
            const [moved] = layers.splice(fromIndex, 1);
            layers.splice(toIndex, 0, moved);

            // Keep selectedLayerIndex pointing to the same layer
            if (selectedLayerIndex === fromIndex) {
                selectedLayerIndex = toIndex;
            } else if (fromIndex < toIndex) {
                if (selectedLayerIndex > fromIndex && selectedLayerIndex <= toIndex) selectedLayerIndex--;
            } else {
                if (selectedLayerIndex >= toIndex && selectedLayerIndex < fromIndex) selectedLayerIndex++;
            }

            layersCacheDirty = true;
            updateThumbnails();
            updateLayersUI();
            pushHistory();
            requestRender();
        });

        layersList.appendChild(li);
    }
}

function screenToWorld(sx, sy) {
    const dx = sx - canvas.width / 2 - viewPosX; const dy = sy - canvas.height / 2 - viewPosY;
    const cos = Math.cos(-viewRotation); const sin = Math.sin(-viewRotation);
    const x2 = dx * cos - dy * sin; const y2 = dx * sin + dy * cos;
    return { x: x2 / viewScale + paperWidth / 2, y: y2 / viewScale + paperHeight / 2 };
}

function applyCursor(drawing) {
    canvas.style.setProperty('cursor', 'none', 'important');
    if (drawing) {
        document.documentElement.style.setProperty('cursor', 'none', 'important');
    } else {
        document.documentElement.style.removeProperty('cursor');
    }
}

// ─────────────────────────────────────────────────────────────
//  BUCKET FILL
// ─────────────────────────────────────────────────────────────
function executeBucket(worldX, worldY) {
    const px = Math.floor(worldX);
    const py = Math.floor(worldY);
    if (px < 0 || px >= paperWidth || py < 0 || py >= paperHeight) return;

    const l = layers[selectedLayerIndex];
    if (!l) return;

    // --- Build source pixel data (what we sample from) ---
    let srcData;
    if (bucketMode === 'lienzo') {
        // Composite all layers into a temp canvas for sampling
        const tmpC = document.createElement('canvas'); tmpC.width = paperWidth; tmpC.height = paperHeight;
        const tmpX = tmpC.getContext('2d');
        if (bgMode === 1) { tmpX.fillStyle = solidBgColor; tmpX.fillRect(0, 0, paperWidth, paperHeight); }
        compositeLayers(tmpX);
        srcData = tmpX.getImageData(0, 0, paperWidth, paperHeight).data;
    } else {
        srcData = l.ctx.getImageData(0, 0, paperWidth, paperHeight).data;
    }

    // --- Target color we click on ---
    const idx0 = (py * paperWidth + px) * 4;
    const tR = srcData[idx0];
    const tG = srcData[idx0 + 1];
    const tB = srcData[idx0 + 2];
    const tA = srcData[idx0 + 3];

    // --- Fill color ---
    let fillR, fillG, fillB, fillA;
    if (bucketFillMode === 'erase') {
        fillR = fillG = fillB = fillA = 0;
    } else {
        const fc = hexToRgbArray(selectedColor);
        fillR = fc[0]; fillG = fc[1]; fillB = fc[2]; fillA = Math.round(brushOpacity * 255);
    }

    // Skip if target === fill (would infinite loop or do nothing)
    if (bucketFillMode !== 'erase') {
        const sameColor = (tR === fillR && tG === fillG && tB === fillB && tA === fillA);
        if (sameColor && tA > 0) return;
    }

    // --- Color distance helper ---
    const tol = bucketTolerance;
    function colorMatch(i) {
        const dr = srcData[i] - tR;
        const dg = srcData[i + 1] - tG;
        const db = srcData[i + 2] - tB;
        const da = srcData[i + 3] - tA;
        return (dr * dr + dg * dg + db * db + da * da) <= tol * tol * 4;
    }

    // --- Prepare destination ImageData (always the active layer) ---
    const dstImgData = l.ctx.getImageData(0, 0, paperWidth, paperWidth === paperWidth ? paperHeight : paperHeight);
    const dst = dstImgData.data;

    function applyPixel(i) {
        if (bucketFillMode === 'erase') {
            dst[i] = dst[i + 1] = dst[i + 2] = dst[i + 3] = 0;
        } else {
            dst[i] = fillR; dst[i + 1] = fillG; dst[i + 2] = fillB; dst[i + 3] = fillA;
        }
    }

    const W = paperWidth;
    const H = paperHeight;

    if (bucketContiguous) {
        // ── Contiguous flood fill (4-connected stack BFS) ──
        const visited = new Uint8Array(W * H);
        const stack = [px + py * W];
        visited[px + py * W] = 1;

        while (stack.length > 0) {
            const pos = stack.pop();
            const x = pos % W;
            const y = (pos / W) | 0;
            const i = pos * 4;

            applyPixel(i);

            const neighbors = [
                x > 0     ? pos - 1 : -1,
                x < W - 1 ? pos + 1 : -1,
                y > 0     ? pos - W : -1,
                y < H - 1 ? pos + W : -1,
            ];
            for (const n of neighbors) {
                if (n >= 0 && !visited[n] && colorMatch(n * 4)) {
                    visited[n] = 1;
                    stack.push(n);
                }
            }
        }
    } else {
        // ── Global: replace all matching pixels in the layer ──
        for (let i = 0; i < srcData.length; i += 4) {
            if (colorMatch(i)) applyPixel(i);
        }
    }

    // Apply selection mask if active
    if (hasSelection && selectionCanvas) {
        const origLayer = l.ctx.getImageData(0, 0, W, H).data; // snapshot BEFORE write
        const selData = selCtx.getImageData(0, 0, W, H).data;
        // Blend fill with original based on selection mask
        for (let i = 0; i < dst.length; i += 4) {
            const sa = selData[i + 3];
            if (sa < 128) {
                dst[i]     = origLayer[i];
                dst[i + 1] = origLayer[i + 1];
                dst[i + 2] = origLayer[i + 2];
                dst[i + 3] = origLayer[i + 3];
            }
        }
        l.ctx.putImageData(dstImgData, 0, 0);
    } else {
        l.ctx.putImageData(dstImgData, 0, 0);
    }

    updateThumbnails();
    updateLayersUI();
    pushHistory();
    requestRender();
}

function buildBucketPanel() {
    if (document.getElementById('bucket-settings-panel')) return;
    const panel = document.createElement('div');
    panel.id = 'bucket-settings-panel';
    panel.className = 'floating-menu hidden';
    panel.style.cssText = 'position:fixed !important; top:80px; left:auto !important; right:20px; width:260px; z-index:2000; pointer-events:auto;';
    panel.innerHTML = `
        <div class="menu-header" style="cursor:default"><label>⚙ Configuración Cubeta</label></div>
        <div style="padding:14px; display:flex; flex-direction:column; gap:14px;">

            <div>
                <div style="display:flex; justify-content:space-between; align-items:center; margin-bottom:6px;">
                    <label style="font-size:11px; font-weight:700; color:#888;">TOLERANCIA</label>
                    <span id="bucket-tol-value" style="font-size:12px; font-weight:700; color:#0066ff;">32</span>
                </div>
                <input type="range" id="bucket-tol-slider" min="0" max="255" value="32"
                    style="width:100%; accent-color:#0066ff;">
                <div style="display:flex; justify-content:space-between; margin-top:2px;">
                    <span style="font-size:9px; color:#aaa;">Exacto</span>
                    <span style="font-size:9px; color:#aaa;">Todo</span>
                </div>
            </div>

            <div>
                <label style="font-size:11px; font-weight:700; color:#888; display:block; margin-bottom:8px;">MODO DE RELLENO</label>
                <div style="display:flex; gap:6px;">
                    <button id="bucket-fill-solid" class="bucket-mode-pill active-pill">🎨 Color</button>
                    <button id="bucket-fill-erase" class="bucket-mode-pill">🧹 Borrar</button>
                </div>
            </div>

            <div>
                <label style="font-size:11px; font-weight:700; color:#888; display:block; margin-bottom:8px;">ÁREA DE RELLENO</label>
                <div style="display:flex; gap:6px;">
                    <button id="bucket-area-contig" class="bucket-mode-pill active-pill">⬤ Contiguo</button>
                    <button id="bucket-area-global" class="bucket-mode-pill">◎ Global</button>
                </div>
            </div>

            <div>
                <label style="font-size:11px; font-weight:700; color:#888; display:block; margin-bottom:8px;">FUENTE DE MUESTRA</label>
                <div style="display:flex; gap:6px;">
                    <button id="bucket-src-layer" class="bucket-mode-pill active-pill">Capa activa</button>
                    <button id="bucket-src-canvas" class="bucket-mode-pill">Lienzo completo</button>
                </div>
            </div>
        </div>`;
    document.body.appendChild(panel);
    bucketPanel = panel;

    // Pill helper
    function setPills(groupIds, activeId) {
        groupIds.forEach(id => {
            const btn = document.getElementById(id);
            if (btn) btn.classList.toggle('active-pill', id === activeId);
        });
    }

    // Tolerance
    const tolSlider = document.getElementById('bucket-tol-slider');
    const tolVal = document.getElementById('bucket-tol-value');
    tolSlider.oninput = () => {
        bucketTolerance = parseInt(tolSlider.value);
        tolVal.textContent = bucketTolerance;
    };
    tolSlider.onpointerup = (e) => e.target.blur();

    // Fill mode
    document.getElementById('bucket-fill-solid').onclick = () => {
        bucketFillMode = 'solid';
        setPills(['bucket-fill-solid', 'bucket-fill-erase'], 'bucket-fill-solid');
    };
    document.getElementById('bucket-fill-erase').onclick = () => {
        bucketFillMode = 'erase';
        setPills(['bucket-fill-solid', 'bucket-fill-erase'], 'bucket-fill-erase');
    };

    // Contiguous
    document.getElementById('bucket-area-contig').onclick = () => {
        bucketContiguous = true;
        setPills(['bucket-area-contig', 'bucket-area-global'], 'bucket-area-contig');
    };
    document.getElementById('bucket-area-global').onclick = () => {
        bucketContiguous = false;
        setPills(['bucket-area-contig', 'bucket-area-global'], 'bucket-area-global');
    };

    // Source
    document.getElementById('bucket-src-layer').onclick = () => {
        bucketMode = 'capa';
        setPills(['bucket-src-layer', 'bucket-src-canvas'], 'bucket-src-layer');
    };
    document.getElementById('bucket-src-canvas').onclick = () => {
        bucketMode = 'lienzo';
        setPills(['bucket-src-layer', 'bucket-src-canvas'], 'bucket-src-canvas');
    };
}

function showBucketPanel(show) {
    if (!bucketPanel) buildBucketPanel();
    if (show) bucketPanel.classList.remove('hidden');
    else bucketPanel.classList.add('hidden');
}

function handlePointerDown(e) {
    if (e.target !== canvas) return;
    screenCursorX = e.offsetX; screenCursorY = e.offsetY;
    if (e.button !== 0 && e.button !== 1 && !isSpacePressed && e.pointerType === 'mouse') return;
    canvas.setPointerCapture(e.pointerId);
    isDrawing = true;
    applyCursor(true);
    sctx.clearRect(0, 0, strokeCanvas.width, strokeCanvas.height);
    lassoPath = []; lassoSelPath = [];
    lassoLastScreenX = null; lassoLastScreenY = null;
    const world = screenToWorld(e.offsetX, e.offsetY);

    // Filter Priority
    if (activeFilterType === 'chroma') {
        if (chromaLassoMode === 'pick') {
            const color = pickColorAt(world.x, world.y);
            if (color) {
                chromaKeyColor = color;
                const prev = document.getElementById('chroma-color-preview');
                if (prev) prev.style.background = color;
                const btn = document.getElementById('chroma-pick-btn');
                if (btn) btn.textContent = 'SELECCIONAR COLOR DEL LIENZO';
                chromaLassoMode = 'add';
                const addBtn = document.querySelector('.chroma-lasso-btn[data-mode="add"]');
                if (addBtn) {
                    document.querySelectorAll('.chroma-lasso-btn').forEach(b => b.style.boxShadow = '');
                    addBtn.style.boxShadow = '0 0 0 3px rgba(0,0,0,0.3) inset';
                }
                applyFilters();
            }
            requestRender();
            return;
        } else if (chromaLassoMode === 'add' || chromaLassoMode === 'sub' || chromaLassoMode === 'clear') {
            isDrawing = true;
            lassoPath = [{ x: world.x, y: world.y }];
            requestRender();
            return;
        }
        if (currentTool === 'zoom' || currentTool === 'pan' || e.button === 1 || isSpacePressed) { /* ok */ }
        else return;
    }

    if (e.button === 1 || isSpacePressed) {
        isTemporaryPan = true;
        currentTool = 'pan';
    } else {
        isTemporaryPan = false;
    }

    lastX = world.x; lastY = world.y;
    const rawP = (e.pressure === 0.5 && e.pointerType !== 'mouse') ? 0.1 : e.pressure || 0.1;
    lastPressure = rawP; smoothedPressure = rawP;

    if (currentTool === 'rotate') { rotationPivot = { sx: e.offsetX, sy: e.offsetY, startRotation: viewRotation }; }
    else if (currentTool === 'zoom') {
        const w = screenToWorld(e.offsetX, e.offsetY);
        if (w.x >= 0 && w.x <= paperWidth && w.y >= 0 && w.y <= paperHeight) {
            zoomPivotWorld = w;
            zoomPivotScreen = { x: e.offsetX, y: e.offsetY };
        } else {
            zoomPivotWorld = null;
            zoomPivotScreen = null;
        }
    }
    else if (isResizingCanvas) {
        const handle = getCanvasResizeHandle(world.x, world.y);
        if (handle) {
            resizeActiveHandle = handle;
            resizeStartMouse = { x: world.x, y: world.y };
            resizeStartDim = { w: resizePreviewW, h: resizePreviewH };
            resizeStartOffsetX = resizeOffsetX;
            resizeStartOffsetY = resizeOffsetY;
            canvas.setPointerCapture(e.pointerId);
        }
        isDrawing = false;
        e.preventDefault();
        requestRender();
        return;
    }
    else if (currentTool === 'bucket') { executeBucket(world.x, world.y); }
    else if (currentTool === 'eyedropper') {
        if (eyedropperFadeTimeout) { clearTimeout(eyedropperFadeTimeout); eyedropperFadeTimeout = null; }
        eyedropperPreview?.classList.remove('hidden', 'copied');
        updateEyedropperPreview(e.offsetX, e.offsetY, world.x, world.y);
        requestRender();
        return;
    }
    else if (currentTool === 'push') {
        isDrawing = true;
        canvas.setPointerCapture(e.pointerId);
        if (!pushSnapshot) {
            pushSnapshot = document.createElement('canvas');
            pushSnapshot.width = paperWidth;
            pushSnapshot.height = paperHeight;
            pushSnapshot.getContext('2d').drawImage(layers[selectedLayerIndex].canvas, 0, 0);
            pushSnapshotPixels = pushSnapshot.getContext('2d').getImageData(0, 0, paperWidth, paperHeight).data;
            pushDisplacementX = new Float32Array(paperWidth * paperHeight);
            pushDisplacementY = new Float32Array(paperWidth * paperHeight);
        }
    }

    else if (currentTool === 'lazo-sel' || currentTool === 'lazo-des') {
        lassoSelStartX = world.x; lassoSelStartY = world.y;
        if (lassoSelMode === 'libre') lassoSelPath = [{ x: world.x, y: world.y }];
        else lassoSelPath = squarePath(world.x, world.y, world.x, world.y);
    }
    else if (currentTool === 'modify-sel') {
        if (!modSelInitialized && hasSelection) initModifySelection();
        if (modSelInitialized) {
            const handle = getModifyHandle(world.x, world.y);
            if (handle) {
                modSelHandle = handle;
                modSelDragStart = { wx: world.x, wy: world.y };
                modSelOrigBounds = { ...modSelBounds };
                modSelActive = true;
                // Snapshot perspective corners for drag-delta computation
                if (modSelPerspectiveMode && perspCorners) {
                    perspDragStart = { wx: world.x, wy: world.y };
                    perspCornersAtDragStart = perspCorners.map(c => ({ ...c }));
                }
            }
        }
    }
    else if (currentTool === 'pincel') {
        if (currentBrush.isBlur) { blurBuffer = null; }
        else if (currentBrush.isGaussBlur) {
            blurBuffer = document.createElement('canvas');
            blurBuffer.width = paperWidth;
            blurBuffer.height = paperHeight;
            const bctx = blurBuffer.getContext('2d');
            bctx.filter = `blur(${currentBrush.blur}px)`;
            bctx.drawImage(layers[selectedLayerIndex].canvas, 0, 0);
        }
        else if (currentBrush.isSmudge) {
            const side = Math.ceil(baseBrushSize * 2.5);
            smudgeBuffer = document.createElement('canvas');
            smudgeBuffer.width = side; smudgeBuffer.height = side;
            const sctx = smudgeBuffer.getContext('2d');
            sctx.drawImage(layers[selectedLayerIndex].canvas, world.x - side / 2, world.y - side / 2, side, side, 0, 0, side, side);
        }

        if (currentBrush.isLasso) {
            lassoPath.push({ x: world.x, y: world.y });
            lassoLastScreenX = e.offsetX; lassoLastScreenY = e.offsetY;
        } else if (currentBrush.isShape) {
            shapeStartX = world.x; shapeStartY = world.y;
            sctx.clearRect(0, 0, strokeCanvas.width, strokeCanvas.height);
        } else {
            if (stabEnabled > 0 && stabMode === 'post' && !currentBrush.isLasso && !currentBrush.isShape && currentBrush.id !== 'push-brush' && !activeFilterType && !currentBrush.isGaussBlur && !currentBrush.isSmudge) {
                isPostStrokePreview = true;
                rawStrokePath = [{ x: lastX, y: lastY, p: smoothedPressure }];
            }

            if (stabEnabled > 0 && stabMode === 'realtime' && !currentBrush.isGaussBlur && !currentBrush.isSmudge) {
                stabPoints = [];
                stabOutX = null; stabOutY = null; stabOutP = null;
                stabPoints.push({ x: lastX, y: lastY, p: smoothedPressure });
            } else {
                drawPoint(lastX, lastY, smoothedPressure);
            }
        }
    }

    // Handle Chroma Filter picking
    if (activeFilterType === 'chroma' && chromaLassoMode === 'pick') {
        const color = pickColorAt(world.x, world.y);
        if (color) {
            chromaKeyColor = color;
            const prev = document.getElementById('chroma-color-preview');
            if (prev) prev.style.background = color;
            const btn = document.getElementById('chroma-pick-btn');
            if (btn) btn.textContent = 'SELECCIONAR COLOR DEL LIENZO';
            chromaLassoMode = 'none';
            applyFilters();
        }
    } else if (activeFilterType === 'chroma' && (chromaLassoMode === 'add' || chromaLassoMode === 'sub')) {
        lassoPath = [{ x: world.x, y: world.y }];
        isDrawing = true;
    }
    e.preventDefault();
    requestRender();
}

function handlePointerMove(e) {
    screenCursorX = e.offsetX; screenCursorY = e.offsetY;
    // Canvas resize drag is independent of isDrawing
    if (isResizingCanvas) {
        // Update cursor based on which handle is hovered
        if (!resizeActiveHandle) {
            const world2 = screenToWorld(e.offsetX, e.offsetY);
            const hov = getCanvasResizeHandle(world2.x, world2.y);
            const cursorMap = { tl: 'nwse-resize', tc: 'ns-resize', tr: 'nesw-resize', ml: 'ew-resize', mr: 'ew-resize', bl: 'nesw-resize', bc: 'ns-resize', br: 'nwse-resize', move: 'move' };
            canvas.style.cursor = hov ? (cursorMap[hov] || 'crosshair') : 'default';
        }
        if (resizeActiveHandle) {
            e.preventDefault();
            const world = screenToWorld(e.offsetX, e.offsetY);
            const dx = world.x - resizeStartMouse.x;
            const dy = world.y - resizeStartMouse.y;

            if (resizeActiveHandle === 'move') {
                resizeOffsetX -= dx;
                resizeOffsetY -= dy;
                resizeStartMouse = { x: world.x, y: world.y }; // update for next move
            } else {
                const res = applyCanvasResizeDrag(dx, dy, resizeActiveHandle, resizeStartDim.w, resizeStartDim.h);
                resizePreviewW = res.nw;
                resizePreviewH = res.nh;

                if (resizeLibre) {
                    // Update offsets to keep the correct edges pinned
                    // Since we already calculated res.dox/doy based on origW/H
                    // we need to add the incremental change or reset to start dim.
                    // To avoid accumulation errors, we use the diff from startDim.
                    resizeOffsetX = resizeStartOffsetX + res.dox;
                    resizeOffsetY = resizeStartOffsetY + res.doy;
                }

                // Sync back to inputs
                document.getElementById('resize-width').value = resizePreviewW;
                document.getElementById('resize-height').value = resizePreviewH;
            }
        }
        requestRender();
        return;
    }

    if (!isDrawing) {
        requestRender();
        return;
    }
    applyCursor(true); // Re-force cursor visibility during move to fight aggressive browser hiding
    e.preventDefault();
    const world = screenToWorld(e.offsetX, e.offsetY);

    if (currentTool === 'pan') { viewPosX += e.movementX; viewPosY += e.movementY; }
    else if (currentTool === 'push') {
        executePush(world.x, world.y, e.movementX / viewScale, e.movementY / viewScale);
    }
    else if (currentTool === 'zoom') {
        const oldScale = viewScale;
        viewScale *= 1 + e.movementY * -0.005;
        viewScale = Math.max(0.01, Math.min(20, viewScale));

        if (zoomPivotWorld && zoomPivotScreen) {
            // Zoom towards pivot
            const cos = Math.cos(viewRotation);
            const sin = Math.sin(viewRotation);
            const dx = (zoomPivotWorld.x - paperWidth / 2) * viewScale;
            const dy = (zoomPivotWorld.y - paperHeight / 2) * viewScale;
            const rdx = dx * cos - dy * sin;
            const rdy = dx * sin + dy * cos;

            viewPosX = zoomPivotScreen.x - canvas.width / 2 - rdx;
            viewPosY = zoomPivotScreen.y - canvas.height / 2 - rdy;
        }
    }
    else if (currentTool === 'rotate') { viewRotation = rotationPivot.startRotation + (e.offsetX - rotationPivot.sx) * 0.01; resetRotationBtn.classList.remove('hidden'); }
    else if (currentTool === 'lazo-sel' || currentTool === 'lazo-des') {
        if (lassoSelMode === 'libre') lassoSelPath.push({ x: world.x, y: world.y });
        else lassoSelPath = squarePath(lassoSelStartX, lassoSelStartY, world.x, world.y);
    }
    else if (currentTool === 'modify-sel' && modSelActive && modSelHandle) {
        if (modSelPerspectiveMode && perspCorners && modSelHandle.startsWith('pc')) {
            // Move a single perspective corner
            const ci = parseInt(modSelHandle[2]);
            const dx = world.x - modSelDragStart.wx;
            const dy = world.y - modSelDragStart.wy;
            perspCorners[ci].x = perspCornersAtDragStart[ci].x + dx;
            perspCorners[ci].y = perspCornersAtDragStart[ci].y + dy;
        } else if (modSelPerspectiveMode && perspCorners && modSelHandle === 'move') {
            // Move all corners together
            const dx = world.x - modSelDragStart.wx;
            const dy = world.y - modSelDragStart.wy;
            for (let ci = 0; ci < 4; ci++) {
                perspCorners[ci].x = perspCornersAtDragStart[ci].x + dx;
                perspCorners[ci].y = perspCornersAtDragStart[ci].y + dy;
            }
            // Keep modSelBounds centroid in sync for flip buttons positioning
            const mxs = perspCorners.map(c => c.x), mys = perspCorners.map(c => c.y);
            modSelBounds = { x: Math.min(...mxs), y: Math.min(...mys), w: Math.max(...mxs) - Math.min(...mxs), h: Math.max(...mys) - Math.min(...mys) };
        } else {
            const dx = world.x - modSelDragStart.wx; const dy = world.y - modSelDragStart.wy;
            modSelBounds = applyModifyDrag(dx, dy, modSelHandle, modSelOrigBounds, e.shiftKey, world.x, world.y);
        }
    }
    else if (currentTool === 'eyedropper') {
        updateEyedropperPreview(e.offsetX, e.offsetY, world.x, world.y);
    }
    else if (currentTool === 'pincel') {
        const [cX, cY] = [world.x, world.y];
        if (currentBrush.isLasso) {
            // Solo añade punto si el cursor se movió al menos 2px en pantalla (filtra micro-temblores)
            const dxScr = e.offsetX - (lassoLastScreenX ?? e.offsetX);
            const dyScr = e.offsetY - (lassoLastScreenY ?? e.offsetY);
            if (dxScr * dxScr + dyScr * dyScr >= 4) {
                lassoPath.push({ x: world.x, y: world.y });
                lassoLastScreenX = e.offsetX;
                lassoLastScreenY = e.offsetY;
            }
        } else if (currentBrush.isShape) {
            // Live preview: clear strokeCanvas and redraw shape from anchor to cursor
            let ex = cX, ey = cY;
            if (e.shiftKey) [ex, ey] = constrainShape(shapeStartX, shapeStartY, cX, cY);
            sctx.clearRect(0, 0, strokeCanvas.width, strokeCanvas.height);
            drawShapeOnCtx(sctx, shapeStartX, shapeStartY, ex, ey);
        } else {
            smoothedPressure += ((e.pressure || 0.1) - smoothedPressure) * 0.3;
            if (stabEnabled > 0 && stabMode === 'realtime' && !currentBrush.isGaussBlur && !currentBrush.isSmudge) {
                const sp = stabilizePoint(cX, cY, smoothedPressure, stabEnabled);
                lastX = cX; lastY = cY; lastPressure = smoothedPressure;
                if (sp) {
                    if (stabOutX !== null) {
                        drawStabLineTo(stabOutX, stabOutY, stabOutP, sp.x, sp.y, sp.p);
                    } else {
                        drawPoint(sp.x, sp.y, sp.p);
                    }
                    stabOutX = sp.x; stabOutY = sp.y; stabOutP = sp.p;
                }
            } else {
                if (stabEnabled > 0 && stabMode === 'post' && !currentBrush.isGaussBlur && !currentBrush.isSmudge) {
                    rawStrokePath.push({ x: cX, y: cY, p: smoothedPressure });
                }
                // Track pointer speed for velocity sensitivity
                const now = performance.now();
                const dt = now - lastPointerTime;
                if (dt > 0) {
                    const dist = Math.hypot(cX - lastX, cY - lastY);
                    const rawSpeed = dist / dt;
                    // Heavy smoothing (alpha=0.06) prevents jitter/dots
                    lastPointerSpeed += (rawSpeed - lastPointerSpeed) * 0.06;
                }
                lastPointerTime = now;
                drawStabLineTo(lastX, lastY, lastPressure, cX, cY, smoothedPressure);
                [lastX, lastY, lastPressure] = [cX, cY, smoothedPressure];
            }
        }
    }

    if (activeFilterType === 'chroma' && (chromaLassoMode === 'add' || chromaLassoMode === 'sub' || chromaLassoMode === 'clear')) {
        lassoPath.push({ x: world.x, y: world.y });
    }
    requestRender();
}

function handlePointerUp(e) {
    // Release canvas resize drag regardless of isDrawing
    if (resizeActiveHandle) {
        try { canvas.releasePointerCapture(e.pointerId); } catch (_) { }
        resizeActiveHandle = null;
        canvas.style.cursor = 'default';
        e.preventDefault();
        requestRender();
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
        updateFlipButtonsPosition();
        if (!isModifyingShape) pushHistory(); // snapshot AFTER move/resize is settled
    }
    else if (currentTool === 'pincel') {
        if (stabEnabled > 0 && stabMode === 'realtime' && !currentBrush.isLasso && !currentBrush.isShape && !currentBrush.useCompositing && !currentBrush.isGaussBlur && !currentBrush.isSmudge) {
            while (stabPoints.length > 0) {
                const p = stabPoints.shift();
                drawPoint(p.x, p.y, p.p);
            }
            stabPoints = [];
        }

        if (stabMode === 'post' && stabEnabled > 0 && rawStrokePath.length > 2 && isPostStrokePreview && !currentBrush.isGaussBlur && !currentBrush.isSmudge) {
            sctx.clearRect(0, 0, strokeCanvas.width, strokeCanvas.height);
            isPostStrokePreview = false;
            
            const passes = Math.round(stabEnabled * 2);
            const smoothed = smoothStrokePath(rawStrokePath, passes);
            
            drawPoint(smoothed[0].x, smoothed[0].y, smoothed[0].p);
            for (let i = 1; i < smoothed.length; i++) {
                drawStabLineTo(smoothed[i-1].x, smoothed[i-1].y, smoothed[i-1].p, smoothed[i].x, smoothed[i].y, smoothed[i].p);
            }
            rawStrokePath = [];
        } else {
            isPostStrokePreview = false;
        }
        if (currentBrush.isLasso) {
            executeLassoFill();
            updateThumbnails(); updateLayersUI();
            pushHistory();
        } else if (currentBrush.isShape) {
            // Finalize shape onto strokeCanvas (apply shift-constrain on release too)
            const world = screenToWorld(e.offsetX, e.offsetY);
            let ex = world.x, ey = world.y;
            if (e.shiftKey) [ex, ey] = constrainShape(shapeStartX, shapeStartY, ex, ey);
            sctx.clearRect(0, 0, strokeCanvas.width, strokeCanvas.height);
            drawShapeOnCtx(sctx, shapeStartX, shapeStartY, ex, ey);

            let isModifiable = false;
            if (currentBrush.shapeType === 'rect') isModifiable = shapeModifiableRect;
            else if (currentBrush.shapeType === 'ellipse') isModifiable = shapeModifiableCircle;
            else if (currentBrush.shapeType === 'line') isModifiable = shapeModifiableLine;

            if (isModifiable) {
                let minX, minY, maxX, maxY;
                if (currentBrush.shapeType === 'line') {
                    minX = Math.min(shapeStartX, ex); maxX = Math.max(shapeStartX, ex);
                    minY = Math.min(shapeStartY, ey); maxY = Math.max(shapeStartY, ey);
                } else if (currentBrush.shapeType === 'rect') {
                    if (shapeFromCenterRect) {
                        const rw = Math.abs(ex - shapeStartX) * 2;
                        const rh = Math.abs(ey - shapeStartY) * 2;
                        minX = shapeStartX - rw / 2; maxX = shapeStartX + rw / 2;
                        minY = shapeStartY - rh / 2; maxY = shapeStartY + rh / 2;
                    } else {
                        minX = Math.min(shapeStartX, ex); maxX = Math.max(shapeStartX, ex);
                        minY = Math.min(shapeStartY, ey); maxY = Math.max(shapeStartY, ey);
                    }
                } else if (currentBrush.shapeType === 'ellipse') {
                    if (shapeFromCenterCircle) {
                        const rx = Math.max(1, Math.abs(ex - shapeStartX));
                        const ry = Math.max(1, Math.abs(ey - shapeStartY));
                        minX = shapeStartX - rx; maxX = shapeStartX + rx;
                        minY = shapeStartY - ry; maxY = shapeStartY + ry;
                    } else {
                        const cx = (shapeStartX + ex) / 2; cy = (shapeStartY + ey) / 2;
                        const rx = Math.max(1, Math.abs(ex - shapeStartX) / 2);
                        const ry = Math.max(1, Math.abs(ey - shapeStartY) / 2);
                        minX = cx - rx; maxX = cx + rx;
                        minY = cy - ry; maxY = cy + ry;
                    }
                }

                const pad = Math.max(1, baseBrushSize) * 2 + 5;
                minX -= pad; minY -= pad; maxX += pad; maxY += pad;
                const w = maxX - minX;
                const h = maxY - minY;

                if (w > 0 && h > 0) {
                    modSelCanvas = document.createElement('canvas');
                    modSelCanvas.width = w; modSelCanvas.height = h;
                    modSelCtx = modSelCanvas.getContext('2d');
                    modSelCtx.globalAlpha = brushOpacity;
                    modSelCtx.save();
                    modSelCtx.translate(-minX, -minY);
                    drawShapeOnCtx(modSelCtx, shapeStartX, shapeStartY, ex, ey);
                    modSelCtx.restore();
                    sctx.clearRect(0, 0, strokeCanvas.width, strokeCanvas.height);

                    modSelBounds = { x: minX, y: minY, w, h };
                    modSelOrigBounds = { ...modSelBounds };
                    modSelRotation = 0;
                    modSelFlipX = 1; modSelFlipY = 1;
                    
                    isImportingNewImage = true;
                    isModifyingShape = true;
                    modSelInitialized = true;
                    
                    selectTool('modify-sel', 'Modificar Selección');
                    updateThumbnails(); updateLayersUI();
                    
                    isDrawing = false;
                    return;
                }
            }

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

    else if (currentTool === 'eyedropper') {
        const world = screenToWorld(e.offsetX, e.offsetY);
        const color = eyedropperMode === 'original'
            ? pickColorRaw(world.x, world.y)
            : pickColorAt(world.x, world.y);
        if (color) {
            selectedColor = color;
            mainColorPicker.value = color;
            updateTintedTexture();

            // Visual feedback: success flash and fade out
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

    else if (currentTool === 'push') {
        updateThumbnails(); updateLayersUI();
        pushHistory();
    }

    if (activeFilterType === 'chroma' && (chromaLassoMode === 'add' || chromaLassoMode === 'sub' || chromaLassoMode === 'clear')) {
        if (lassoPath.length >= 3) {
            chromaMaskCtx.save();
            if (chromaLassoMode === 'clear') {
                chromaMaskCtx.globalCompositeOperation = 'destination-out';
                chromaMaskCtx.fillStyle = 'black';
            } else {
                chromaMaskCtx.globalCompositeOperation = 'source-over';
                chromaMaskCtx.fillStyle = chromaLassoMode === 'add' ? '#FF0000' : '#00FF00';
            }
            chromaMaskCtx.beginPath();
            chromaMaskCtx.moveTo(lassoPath[0].x, lassoPath[0].y);
            lassoPath.forEach(p => chromaMaskCtx.lineTo(p.x, p.y));
            chromaMaskCtx.closePath();
            chromaMaskCtx.fill();
            chromaMaskCtx.restore();
            applyFilters();
        }
    }

    isDrawing = false; lassoPath = [];
    if (currentTool === 'pan' && isTemporaryPan) {
        if (activeFilterType) currentTool = 'none';
        else {
            const activeToolName = activeToolIndicator?.textContent || 'Pincel';
            const t = toolsData.find(x => x.name === activeToolName);
            if (t) currentTool = t.id;
            else currentTool = 'pincel';
        }
        showSelectionButtons(currentTool);
        isTemporaryPan = false;
    }
    if (currentTool === 'rotate') selectTool('pincel', lastBrushTool);
    requestRender();
}

// ─────────────────────────────────────────────────────────────
//  BRUSH DRAWING
// ─────────────────────────────────────────────────────────────
// Gaussian smoothing: promedia cada punto con sus vecinos
// (Elimina temblor de alta frecuencia sin dejar lados rectos)
function smoothLassoPath(pts, passes) {
    if (pts.length <= 3) return pts;
    let p = pts;
    for (let iter = 0; iter < passes; iter++) {
        const s = [p[0]]; // preservar primer punto
        for (let i = 1; i < p.length - 1; i++) {
            s.push({
                x: p[i - 1].x * 0.25 + p[i].x * 0.5 + p[i + 1].x * 0.25,
                y: p[i - 1].y * 0.25 + p[i].y * 0.5 + p[i + 1].y * 0.25
            });
        }
        s.push(p[p.length - 1]); // preservar último punto
        p = s;
    }
    return p;
}

function smoothStrokePath(pts, passes) {
    if (pts.length <= 3) return pts;
    let p = pts;
    for (let iter = 0; iter < passes; iter++) {
        const s = [p[0]]; // preservar primer punto
        for (let i = 1; i < p.length - 1; i++) {
            s.push({
                x: p[i - 1].x * 0.25 + p[i].x * 0.5 + p[i + 1].x * 0.25,
                y: p[i - 1].y * 0.25 + p[i].y * 0.5 + p[i + 1].y * 0.25,
                p: p[i - 1].p * 0.25 + p[i].p * 0.5 + p[i + 1].p * 0.25
            });
        }
        s.push(p[p.length - 1]); // preservar último punto
        p = s;
    }
    return p;
}

function executeLassoFill() {
    if (lassoPath.length < 3) return;
    // Pasadas adaptativas: a menos zoom más suavizado para compensar el temblor amplificado
    const passes = Math.round(Math.min(24, Math.max(1, 3 / viewScale)));
    const smoothPath = smoothLassoPath(lassoPath, passes);
    if (smoothPath.length < 3) return;
    const l = layers[selectedLayerIndex]; l.ctx.save();
    if (currentBrush.isEraser) l.ctx.globalCompositeOperation = 'destination-out';
    else if (l.alphaLocked) l.ctx.globalCompositeOperation = 'source-atop';
    l.ctx.globalAlpha = brushOpacity; l.ctx.fillStyle = selectedColor;
    l.ctx.beginPath(); l.ctx.moveTo(smoothPath[0].x, smoothPath[0].y);
    smoothPath.forEach(p => l.ctx.lineTo(p.x, p.y)); l.ctx.closePath(); l.ctx.fill(); l.ctx.restore();
}
function drawPoint(x, y, pressure) {
    // Pressure: sensitivity 0-2.0, scaled so at 2.0 range is ~0% to 300% of base size
    const minScale = Math.max(0.01, 1.0 - (0.9 * pressureSensitivity));
    const maxScale = 1.0 + (1.5 * pressureSensitivity);
    
    // Apply an exponential curve so light pressure stays thin, and hard pressure grows rapidly
    const curvedPressure = Math.pow(pressure, 2.5);
    
    let size = baseBrushSize * (minScale + curvedPressure * (maxScale - minScale));
    let localOpacity = brushOpacity;

    if (currentBrush.isGaussBlur) {
        size = baseBrushSize;
        localOpacity = brushOpacity;
    }

    // Velocity size modulation
    if (velocitySensitivity > 0 && !currentBrush.isGaussBlur) {
        // Sqrt curve: smooth transitions, avoids harsh jumps at low speeds
        const normalised = Math.min(1.0, Math.sqrt(lastPointerSpeed / 2.5));
        // 'slow' mode: slow→thick (default). 'fast' mode: fast→thick (inverted)
        const factor = velocityMode === 'slow'
            ? (1.0 - velocitySensitivity * normalised * 0.82)
            : (1.0 - velocitySensitivity * (1.0 - normalised) * 0.82);
        size *= Math.max(0.05, factor);
    }
    size = Math.max(0.05, size);
    if (size <= 0) return;
    const l = layers[selectedLayerIndex];

    if (currentBrush.isBlur) {
        l.ctx.save();
        const side = Math.ceil(size * 2);
        if (side < 1) { l.ctx.restore(); return; }

        if (brushMaskCanvas.width < side || brushMaskCanvas.height < side) {
            brushMaskCanvas.width = side + 20; brushMaskCanvas.height = side + 20;
            blurTempCanvas.width = side + 20; blurTempCanvas.height = side + 20;
            bleedCanvas.width = side + 20; bleedCanvas.height = side + 20;
        }

        // 1. Capture current area
        blurTempCtx.clearRect(0, 0, side, side);
        blurTempCtx.drawImage(l.canvas, x - side / 2, y - side / 2, side, side, 0, 0, side, side);

        // 2. Perform Blur directly into bleedCanvas (without opacity-boosting bleed hacks)
        bleedCtx.clearRect(0, 0, side, side);
        const samples = 6;
        const radius = Math.max(1, currentBrush.blur / 6);
        bleedCtx.globalAlpha = 1 / samples;
        for (let i = 0; i < samples; i++) {
            const ang = (i / samples) * Math.PI * 2;
            bleedCtx.drawImage(blurTempCanvas, Math.cos(ang) * radius, Math.sin(ang) * radius);
        }
        bleedCtx.globalAlpha = 1.0;

        // 3. Create the Mask in brushMaskCanvas
        brushMaskCtx.clearRect(0, 0, side, side);
        if (currentBrush.useTexture && tintedAirbrushCanvas) {
            brushMaskCtx.drawImage(tintedAirbrushCanvas, 0, 0, side, side);
        } else {
            const g = brushMaskCtx.createRadialGradient(side / 2, side / 2, (side / 2) * currentBrush.hardness, side / 2, side / 2, side / 2);
            g.addColorStop(0, 'white'); g.addColorStop(1, 'rgba(255,255,255,0)');
            brushMaskCtx.fillStyle = g; brushMaskCtx.fillRect(0, 0, side, side);
        }

        // Apply brush opacity to the mask itself
        brushMaskCtx.globalCompositeOperation = 'destination-in';
        brushMaskCtx.fillStyle = `rgba(255, 255, 255, ${localOpacity})`;
        brushMaskCtx.fillRect(0, 0, side, side);
        brushMaskCtx.globalCompositeOperation = 'source-over';

        // 4. Mask the Blurred image
        bleedCtx.globalCompositeOperation = 'destination-in';
        bleedCtx.drawImage(brushMaskCanvas, 0, 0);
        bleedCtx.globalCompositeOperation = 'source-over';

        // 5. Update Layer using correct interpolation
        if (l.alphaLocked) {
            l.ctx.globalCompositeOperation = 'source-atop';
            l.ctx.drawImage(bleedCanvas, 0, 0, side, side, x - side / 2, y - side / 2, side, side);
        } else {
            l.ctx.globalCompositeOperation = 'destination-out';
            l.ctx.drawImage(brushMaskCanvas, 0, 0, side, side, x - side / 2, y - side / 2, side, side);
            l.ctx.globalCompositeOperation = 'lighter';
            l.ctx.drawImage(bleedCanvas, 0, 0, side, side, x - side / 2, y - side / 2, side, side);
        }
        l.ctx.restore();
    }
    else if (currentBrush.isGaussBlur && blurBuffer) {
        l.ctx.save();

        const side = Math.ceil(size * 2);
        if (side < 1) { l.ctx.restore(); return; }

        if (brushMaskCanvas.width < side || brushMaskCanvas.height < side) {
            brushMaskCanvas.width = side + 20; brushMaskCanvas.height = side + 20;
            bleedCanvas.width = side + 20; bleedCanvas.height = side + 20;
        }

        // 1. Get blurred area from global blur buffer
        bleedCtx.clearRect(0, 0, side, side);
        bleedCtx.drawImage(blurBuffer, x - side / 2, y - side / 2, side, side, 0, 0, side, side);

        // 2. Create mask
        brushMaskCtx.clearRect(0, 0, side, side);
        if (currentBrush.useTexture && tintedAirbrushCanvas) {
            brushMaskCtx.drawImage(tintedAirbrushCanvas, 0, 0, side, side);
        } else {
            const g = brushMaskCtx.createRadialGradient(side / 2, side / 2, (side / 2) * currentBrush.hardness, side / 2, side / 2, side / 2);
            g.addColorStop(0, 'white'); g.addColorStop(1, 'rgba(255,255,255,0)');
            brushMaskCtx.fillStyle = g; brushMaskCtx.fillRect(0, 0, side, side);
        }

        // Apply brush opacity to mask
        brushMaskCtx.globalCompositeOperation = 'destination-in';
        brushMaskCtx.fillStyle = `rgba(255, 255, 255, ${localOpacity})`;
        brushMaskCtx.fillRect(0, 0, side, side);
        brushMaskCtx.globalCompositeOperation = 'source-over';

        // 3. Mask the blurred image
        bleedCtx.globalCompositeOperation = 'destination-in';
        bleedCtx.drawImage(brushMaskCanvas, 0, 0);
        bleedCtx.globalCompositeOperation = 'source-over';

        // 4. Update Layer
        if (l.alphaLocked) {
            l.ctx.globalCompositeOperation = 'source-atop';
            l.ctx.drawImage(bleedCanvas, 0, 0, side, side, x - side / 2, y - side / 2, side, side);
        } else {
            l.ctx.globalCompositeOperation = 'destination-out';
            l.ctx.drawImage(brushMaskCanvas, 0, 0, side, side, x - side / 2, y - side / 2, side, side);
            l.ctx.globalCompositeOperation = 'lighter';
            l.ctx.drawImage(bleedCanvas, 0, 0, side, side, x - side / 2, y - side / 2, side, side);
        }
        l.ctx.restore();
    }
    else if (currentBrush.isSmudge && smudgeBuffer) {
        l.ctx.save();

        const side = Math.ceil(size * 2.5);
        if (side < 1) { l.ctx.restore(); return; }

        if (brushMaskCanvas.width < side || brushMaskCanvas.height < side) {
            brushMaskCanvas.width = side + 20; brushMaskCanvas.height = side + 20;
            bleedCanvas.width = side + 20; bleedCanvas.height = side + 20;
        }

        // 1. Prepare the smudge tip in bleedCanvas
        bleedCtx.clearRect(0, 0, side, side);
        bleedCtx.drawImage(smudgeBuffer, 0, 0, smudgeBuffer.width, smudgeBuffer.height, 0, 0, side, side);

        // 2. Create mask
        brushMaskCtx.clearRect(0, 0, side, side);
        if (currentBrush.useTexture && tintedAirbrushCanvas) {
            brushMaskCtx.drawImage(tintedAirbrushCanvas, 0, 0, side, side);
        } else {
            const g = brushMaskCtx.createRadialGradient(side / 2, side / 2, (side / 2) * currentBrush.hardness, side / 2, side / 2, side / 2);
            g.addColorStop(0, 'white'); g.addColorStop(1, 'rgba(255,255,255,0)');
            brushMaskCtx.fillStyle = g; brushMaskCtx.fillRect(0, 0, side, side);
        }

        // Apply brush opacity to mask
        brushMaskCtx.globalCompositeOperation = 'destination-in';
        brushMaskCtx.fillStyle = `rgba(255, 255, 255, ${localOpacity})`;
        brushMaskCtx.fillRect(0, 0, side, side);
        brushMaskCtx.globalCompositeOperation = 'source-over';

        // 3. Mask the smudge tip
        bleedCtx.globalCompositeOperation = 'destination-in';
        bleedCtx.drawImage(brushMaskCanvas, 0, 0);
        bleedCtx.globalCompositeOperation = 'source-over';

        // 4. Update Layer
        if (l.alphaLocked) {
            l.ctx.globalCompositeOperation = 'source-atop';
            l.ctx.drawImage(bleedCanvas, 0, 0, side, side, x - side / 2, y - side / 2, side, side);
        } else {
            l.ctx.globalCompositeOperation = 'destination-out';
            l.ctx.drawImage(brushMaskCanvas, 0, 0, side, side, x - side / 2, y - side / 2, side, side);
            l.ctx.globalCompositeOperation = 'lighter';
            l.ctx.drawImage(bleedCanvas, 0, 0, side, side, x - side / 2, y - side / 2, side, side);
        }

        // 5. Update smudge buffer (intelligent pick up, without opacity-boosting bleed hacks)
        const sctx = smudgeBuffer.getContext('2d');
        blurTempCtx.clearRect(0, 0, side, side);
        blurTempCtx.drawImage(l.canvas, x - side / 2, y - side / 2, side, side, 0, 0, side, side);

        sctx.globalAlpha = 0.12;
        sctx.globalCompositeOperation = 'source-atop';
        sctx.drawImage(blurTempCanvas, 0, 0, side, side, 0, 0, smudgeBuffer.width, smudgeBuffer.height);
        sctx.globalCompositeOperation = 'source-over';

        sctx.globalAlpha = 0.02;
        sctx.drawImage(blurTempCanvas, 0, 0, side, side, 0, 0, smudgeBuffer.width, smudgeBuffer.height);

        l.ctx.restore();
    }
    else {
        const isHardSolid = !currentBrush.useTexture && !currentBrush.isBlur && !currentBrush.isSmudge && currentBrush.hardness >= 0.8 && !currentBrush.isLasso && !currentBrush.isShape;
        if (isHardSolid) {
            const ctx = (currentBrush.useCompositing || isPostStrokePreview) ? sctx : l.ctx;
            ctx.save();
            if (currentBrush.isEraser && !currentBrush.useCompositing && !isPostStrokePreview) ctx.globalCompositeOperation = 'destination-out';
            else if (!currentBrush.useCompositing && l.alphaLocked && !isPostStrokePreview) ctx.globalCompositeOperation = 'source-atop';
            if (!currentBrush.useCompositing) ctx.globalAlpha = localOpacity;
            else ctx.globalAlpha = 1.0;
            ctx.fillStyle = selectedColor;
            ctx.beginPath();
            ctx.arc(x, y, size, 0, Math.PI * 2);
            ctx.fill();
            ctx.restore();
        }
        else if (currentBrush.useCompositing) { sctx.save(); renderStamp(sctx, x, y, size, 1.0); sctx.restore(); }
        else { 
            const ctx = isPostStrokePreview ? sctx : l.ctx;
            ctx.save(); 
            if (currentBrush.isEraser && !currentBrush.useCompositing && !isPostStrokePreview) ctx.globalCompositeOperation = 'destination-out'; 
            else if (l.alphaLocked && !isPostStrokePreview) ctx.globalCompositeOperation = 'source-atop'; 
            renderStamp(ctx, x, y, size, localOpacity * 0.4); 
            ctx.restore(); 
        }
    }
}

// ─────────────────────────────────────────────────────────────
//  PUSH TOOL (high-quality per-pixel displacement)
// ─────────────────────────────────────────────────────────────

function endPushSession() {
    pushSnapshot = null;
    pushSnapshotPixels = null;
    pushDisplacementX = null;
    pushDisplacementY = null;
}

function executePush(worldX, worldY, dx, dy) {
    if (!pushSnapshot || !pushSnapshotPixels || !pushDisplacementX || !pushDisplacementY) return;
    if (Math.abs(dx) < 0.1 && Math.abs(dy) < 0.1) return;

    const radius = baseBrushSize * 8;
    const strength = brushOpacity * 1.0;
    const l = layers[selectedLayerIndex];
    if (!l) return;

    const W = paperWidth;
    const H = paperHeight;

    const margin = radius + 2;
    const iStart = Math.max(0, Math.floor(worldX - margin));
    const iEnd = Math.min(W, Math.ceil(worldX + margin));
    const jStart = Math.max(0, Math.floor(worldY - margin));
    const jEnd = Math.min(H, Math.ceil(worldY + margin));
    const boxW = iEnd - iStart;
    const boxH = jEnd - jStart;
    if (boxW <= 0 || boxH <= 0) return;

    const tempDX = new Float32Array(boxW * boxH);
    const tempDY = new Float32Array(boxW * boxH);

    const getOldDX = (px, py) => {
        if (px < 0 || px >= W || py < 0 || py >= H) return 0;
        return pushDisplacementX[py * W + px];
    };
    const getOldDY = (px, py) => {
        if (px < 0 || px >= W || py < 0 || py >= H) return 0;
        return pushDisplacementY[py * W + px];
    };

    let selectionPixels = null;
    if (hasSelection && selectionCanvas) {
        selectionPixels = selCtx.getImageData(0, 0, W, H).data;
    }

    // Step 1: Advect displacements
    for (let j = jStart; j < jEnd; j++) {
        for (let i = iStart; i < iEnd; i++) {
            const pos = j * W + i;
            let selFactor = 1.0;
            if (hasSelection && selectionPixels) {
                selFactor = selectionPixels[pos * 4 + 3] / 255;
            }

            const dist = Math.hypot(i - worldX, j - worldY);
            let wx = 0, wy = 0;
            if (dist < radius) {
                const weight = Math.pow(1 - dist / radius, 1.5) * selFactor;
                wx = dx * weight * strength;
                wy = dy * weight * strength;
            }

            const srcX = i - wx;
            const srcY = j - wy;

            const x0 = Math.floor(srcX), x1 = x0 + 1;
            const y0 = Math.floor(srcY), y1 = y0 + 1;
            const fx = srcX - x0, fy = srcY - y0;

            const dx00 = getOldDX(x0, y0), dx10 = getOldDX(x1, y0);
            const dx01 = getOldDX(x0, y1), dx11 = getOldDX(x1, y1);
            const topX = dx00 + fx * (dx10 - dx00);
            const botX = dx01 + fx * (dx11 - dx01);
            const interpDX = topX + fy * (botX - topX);

            const dy00 = getOldDY(x0, y0), dy10 = getOldDY(x1, y0);
            const dy01 = getOldDY(x0, y1), dy11 = getOldDY(x1, y1);
            const topY = dy00 + fx * (dy10 - dy00);
            const botY = dy01 + fx * (dy11 - dy01);
            const interpDY = topY + fy * (botY - topY);

            const localPos = (j - jStart) * boxW + (i - iStart);
            tempDX[localPos] = wx + interpDX;
            tempDY[localPos] = wy + interpDY;
        }
    }

    // Step 2: Write back advected displacements and sample new image
    const destData = l.ctx.getImageData(iStart, jStart, boxW, boxH);
    const src = pushSnapshotPixels;
    const dest = destData.data;

    for (let j = jStart; j < jEnd; j++) {
        for (let i = iStart; i < iEnd; i++) {
            const globalPos = j * W + i;
            const localPos = (j - jStart) * boxW + (i - iStart);

            const finalDX = tempDX[localPos];
            const finalDY = tempDY[localPos];
            pushDisplacementX[globalPos] = finalDX;
            pushDisplacementY[globalPos] = finalDY;

            const sx = i - finalDX;
            const sy = j - finalDY;

            const x0 = Math.floor(sx), x1 = x0 + 1;
            const y0 = Math.floor(sy), y1 = y0 + 1;
            const fx = sx - x0, fy = sy - y0;

            const getP = (px, py) => {
                if (px < 0 || px >= W || py < 0 || py >= H) return [0, 0, 0, 0];
                const p = (py * W + px) * 4;
                return [src[p], src[p + 1], src[p + 2], src[p + 3]];
            };

            const p00 = getP(x0, y0), p10 = getP(x1, y0), p01 = getP(x0, y1), p11 = getP(x1, y1);
            const dPos = localPos * 4;
            for (let k = 0; k < 4; k++) {
                const top = p00[k] + fx * (p10[k] - p00[k]);
                const bot = p01[k] + fx * (p11[k] - p01[k]);
                dest[dPos + k] = top + fy * (bot - top);
            }
        }
    }

    l.ctx.putImageData(destData, iStart, jStart);
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
        let rx, ry, rw, rh;
        if (shapeFromCenterRect) {
            rw = Math.abs(x2 - x1) * 2;
            rh = Math.abs(y2 - y1) * 2;
            rx = x1 - rw / 2;
            ry = y1 - rh / 2;
        } else {
            rx = Math.min(x1, x2);
            ry = Math.min(y1, y2);
            rw = Math.abs(x2 - x1);
            rh = Math.abs(y2 - y1);
        }
        if (rw < 1 || rh < 1) { tctx.restore(); return; }
        if (shapeFill) tctx.fillRect(rx, ry, rw, rh);
        else tctx.strokeRect(rx, ry, rw, rh);
    } else if (type === 'ellipse') {
        let cx, cy, radiusX, radiusY;
        if (shapeFromCenterCircle) {
            cx = x1; cy = y1;
            radiusX = Math.max(1, Math.abs(x2 - x1));
            radiusY = Math.max(1, Math.abs(y2 - y1));
        } else {
            cx = (x1 + x2) / 2; cy = (y1 + y2) / 2;
            radiusX = Math.max(1, Math.abs(x2 - x1) / 2);
            radiusY = Math.max(1, Math.abs(y2 - y1) / 2);
        }
        tctx.beginPath();
        tctx.ellipse(cx, cy, radiusX, radiusY, 0, 0, Math.PI * 2);
        if (shapeFill) tctx.fill();
        else tctx.stroke();
    }
    tctx.restore();
}
function updateTintedTexture() {
    const indicator = document.getElementById('color-preview-btn-indicator');
    if (indicator) indicator.style.backgroundColor = selectedColor;

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
    requestRender();
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

function stabilizePoint(x, y, p, strength) {
    if (strength <= 0) return { x, y, p, ready: true };
    stabPoints.push({ x, y, p });
    if (stabPoints.length <= strength) return null;
    const out = stabPoints.shift();
    let ax = out.x, ay = out.y, ap = out.p;
    for (let i = 0; i < stabPoints.length; i++) {
        ax += stabPoints[i].x;
        ay += stabPoints[i].y;
        ap += stabPoints[i].p;
    }
    const n = stabPoints.length + 1;
    ax /= n; ay /= n; ap /= n;
    const blend = Math.min(1, strength / 20);
    return {
        x: out.x * (1 - blend * 0.6) + ax * (blend * 0.6),
        y: out.y * (1 - blend * 0.6) + ay * (blend * 0.6),
        p: out.p * (1 - blend * 0.4) + ap * (blend * 0.4),
        ready: true
    };
}

function drawStabLineTo(sx, sy, sp, ex, ey, ep) {
    const isHardSolid = !currentBrush.useTexture && !currentBrush.isBlur && !currentBrush.isSmudge && currentBrush.hardness >= 0.8 && !currentBrush.isLasso && !currentBrush.isShape;
    
    if (isHardSolid) {
        const avgPressure = (sp + ep) / 2;
        const curvedPressure = Math.pow(avgPressure, 2.5);
        const minScale = Math.max(0.01, 1.0 - (0.9 * pressureSensitivity));
        const maxScale = 1.0 + (1.5 * pressureSensitivity);
        let size = baseBrushSize * (minScale + curvedPressure * (maxScale - minScale));
        // Velocity size modulation
        if (velocitySensitivity > 0) {
            const normalised = Math.min(1.0, Math.sqrt(lastPointerSpeed / 2.5));
            const factor = velocityMode === 'slow'
                ? (1.0 - velocitySensitivity * normalised * 0.82)
                : (1.0 - velocitySensitivity * (1.0 - normalised) * 0.82);
            size *= Math.max(0.05, factor);
        }
        size = Math.max(0.05, size);
        if (size <= 0) return;
        const l = layers[selectedLayerIndex];
        const ctx = (currentBrush.useCompositing || isPostStrokePreview) ? sctx : l.ctx;
        
        ctx.save();
        if (currentBrush.isEraser && !currentBrush.useCompositing && !isPostStrokePreview) ctx.globalCompositeOperation = 'destination-out';
        else if (!currentBrush.useCompositing && l.alphaLocked && !isPostStrokePreview) ctx.globalCompositeOperation = 'source-atop';
        
        if (!currentBrush.useCompositing) ctx.globalAlpha = brushOpacity;
        else ctx.globalAlpha = 1.0;
        
        ctx.strokeStyle = selectedColor;
        ctx.lineWidth = size * 2;
        ctx.lineCap = 'round';
        ctx.lineJoin = 'round';
        
        ctx.beginPath();
        ctx.moveTo(sx, sy);
        ctx.lineTo(ex, ey);
        ctx.stroke();
        ctx.restore();
        return;
    }

    const dist = Math.hypot(ex - sx, ey - sy);
    const step = Math.max(0.2, baseBrushSize * 0.5 * brushSpacing);
    const steps = Math.floor(dist / step);
    for (let i = 0; i <= steps; i++) {
        const t = steps === 0 ? 1 : i / steps;
        drawPoint(sx + (ex - sx) * t, sy + (ey - sy) * t, sp + (ep - sp) * t);
    }
}



function hexToRgba(hex, alpha) { const r = parseInt(hex.slice(1, 3), 16), g = parseInt(hex.slice(3, 5), 16), b = parseInt(hex.slice(5, 7), 16); return `rgba(${r},${g},${b},${alpha})`; }

// ─────────────────────────────────────────────────────────────
//  RENDER LOOP
// ─────────────────────────────────────────────────────────────
function drawLayerContent(targetCtx, layerObj) {
    targetCtx.drawImage(layerObj.canvas, 0, 0);
    if (currentTool === 'modify-sel' && modSelInitialized && !isImportingNewImage) {
        const tItem = modSelLayersData.find(x => x.layer === layerObj);
        if (tItem) {
            if (modSelPerspectiveMode && perspCorners) {
                renderPerspectiveWarpPreview(targetCtx, tItem.canvas, perspCorners);
            } else {
                const b = modSelBounds;
                const cx = b.x + b.w / 2;
                const cy = b.y + b.h / 2;
                targetCtx.save();
                targetCtx.imageSmoothingEnabled = true;
                targetCtx.imageSmoothingQuality = 'high';
                targetCtx.translate(cx, cy);
                targetCtx.rotate(modSelRotation);
                targetCtx.scale(modSelFlipX, modSelFlipY);
                targetCtx.translate(-cx, -cy);
                targetCtx.drawImage(tItem.canvas, b.x, b.y, b.w, b.h);
                targetCtx.restore();
            }
        }
    }
}

function render() {
    renderRequested = false;
    const isPreviewing = isDrawing && (currentBrush.useCompositing || isPostStrokePreview) && !currentBrush.isLasso && !activeFilterType;
    ctx.clearRect(0, 0, canvas.width, canvas.height); ctx.save();
    ctx.translate(canvas.width / 2 + viewPosX, canvas.height / 2 + viewPosY);
    ctx.rotate(viewRotation); ctx.scale(viewScale, viewScale);
    ctx.translate(-paperWidth / 2, -paperHeight / 2);

    // Paper bg
    ctx.save(); ctx.shadowColor = 'rgba(0,0,0,0.5)'; ctx.shadowBlur = 40; ctx.shadowOffsetX = 10; ctx.shadowOffsetY = 20;
    if (activeFilterType === 'chroma' && chromaDebugBG) {
        ctx.fillStyle = chromaDebugBG;
    } else {
        if (bgMode === 1) ctx.fillStyle = solidBgColor;
        else if (bgMode === 2) ctx.fillStyle = checkerPatternDark;
        else ctx.fillStyle = checkerPatternLight;
    }
    ctx.fillRect(0, 0, paperWidth, paperHeight); ctx.restore();

    // Layers
    let activeGroupStart = selectedLayerIndex;
    while (activeGroupStart > 0 && layers[activeGroupStart].clippingMask) {
        activeGroupStart--;
    }

    if (activeGroupStart > 0) {
        updateLayersCache(activeGroupStart);
        ctx.drawImage(layersCacheCanvas, 0, 0);
    }

    let i = activeGroupStart;
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

            // Live stroke preview inside a clipping group
            const actInGrp = group.findIndex(layer => layer === layers[selectedLayerIndex]);

            gctx.clearRect(0, 0, paperWidth, paperHeight);
            
            // Draw the base layer (group[0] = CAPA B)
            if (actInGrp === 0 && isPreviewing) {
                mctx.clearRect(0, 0, paperWidth, paperHeight);
                mctx.globalCompositeOperation = 'source-over';
                drawLayerContent(mctx, group[0]);
                
                mctx.save();
                mctx.globalAlpha = currentBrush.useCompositing ? brushOpacity : 1.0;
                if ((currentBrush.id === 'aero-duro' || currentBrush.id === 'aero-suave') && currentBlur > 0) {
                    mctx.filter = `blur(${currentBlur}px)`;
                }
                if (group[0].alphaLocked) mctx.globalCompositeOperation = 'source-atop';
                if (currentBrush.isEraser) mctx.globalCompositeOperation = 'destination-out';
                mctx.drawImage(strokeCanvas, 0, 0);
                mctx.restore();
                mctx.filter = 'none';

                gctx.save();
                gctx.globalAlpha = group[0].opacity;
                gctx.globalCompositeOperation = group[0].blendMode;
                gctx.drawImage(maskBuffer, 0, 0);
                gctx.restore();
            } else {
                gctx.save();
                gctx.globalAlpha = group[0].opacity;
                gctx.globalCompositeOperation = group[0].blendMode;
                drawLayerContent(gctx, group[0]);
                gctx.restore();
            }

            // For each clipping layer
            for (let k = 1; k < group.length; k++) {
                mctx.clearRect(0, 0, paperWidth, paperHeight);
                mctx.globalCompositeOperation = 'source-over';
                mctx.save();
                mctx.globalAlpha = group[k].opacity;
                drawLayerContent(mctx, group[k]);
                mctx.restore();

                if (actInGrp === k && isPreviewing) {
                    mctx.save();
                    mctx.globalAlpha = currentBrush.useCompositing ? brushOpacity : 1.0;
                    if ((currentBrush.id === 'aero-duro' || currentBrush.id === 'aero-suave') && currentBlur > 0) {
                        mctx.filter = `blur(${currentBlur}px)`;
                    }
                    if (group[k].alphaLocked) mctx.globalCompositeOperation = 'source-atop';
                    if (currentBrush.isEraser) mctx.globalCompositeOperation = 'destination-out';
                    mctx.drawImage(strokeCanvas, 0, 0);
                    mctx.restore();
                    mctx.filter = 'none';
                }

                mctx.globalCompositeOperation = 'destination-in';
                // Use the composite of base layer + transform for clipping mask
                drawLayerContent(mctx, group[0]);
                mctx.globalCompositeOperation = 'source-over'; // reset

                gctx.save();
                gctx.globalCompositeOperation = group[k].blendMode;
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

                if (i === selectedLayerIndex && isPreviewing) {
                    mctx.clearRect(0, 0, paperWidth, paperHeight);
                    mctx.globalCompositeOperation = 'source-over';
                    drawLayerContent(mctx, l);

                    mctx.save();
                    mctx.globalAlpha = currentBrush.useCompositing ? brushOpacity : 1.0;
                    if ((currentBrush.id === 'aero-duro' || currentBrush.id === 'aero-suave') && currentBlur > 0) {
                        mctx.filter = `blur(${currentBlur}px)`;
                    }
                    if (l.alphaLocked) mctx.globalCompositeOperation = 'source-atop';
                    if (currentBrush.isEraser) mctx.globalCompositeOperation = 'destination-out';
                    mctx.drawImage(strokeCanvas, 0, 0);
                    mctx.restore();
                    mctx.filter = 'none';

                    ctx.drawImage(maskBuffer, 0, 0);
                } else {
                    drawLayerContent(ctx, l);
                }
                ctx.restore();
            }
            i++;
        }
    }

    // ── Draw floating modify preview ──
    if (currentTool === 'modify-sel' && modSelInitialized && modSelCanvas && modSelBounds) {
        ctx.save();
        ctx.beginPath();
        ctx.rect(0, 0, paperWidth, paperHeight);
        ctx.clip();
        ctx.imageSmoothingEnabled = true;
        ctx.imageSmoothingQuality = 'high';

        if (modSelPerspectiveMode && perspCorners) {
            // ── Perspective warp preview using scanline rendering ──
            if (isImportingNewImage) {
                renderPerspectiveWarpPreview(ctx, modSelCanvas, perspCorners);
            }

            // Draw the quadrilateral outline
            ctx.restore();
            ctx.save();
            ctx.strokeStyle = '#ff00ff'; ctx.lineWidth = 2 / viewScale; ctx.setLineDash([]);
            ctx.beginPath();
            ctx.moveTo(perspCorners[0].x, perspCorners[0].y); // TL
            ctx.lineTo(perspCorners[1].x, perspCorners[1].y); // TR
            ctx.lineTo(perspCorners[3].x, perspCorners[3].y); // BR
            ctx.lineTo(perspCorners[2].x, perspCorners[2].y); // BL
            ctx.closePath();
            ctx.stroke();

            // Draw 4 corner handles
            const hr2 = HANDLE_R / viewScale;
            const cornerColors = ['#ff00ff', '#ff00ff', '#ff00ff', '#ff00ff'];
            perspCorners.forEach((c, ci) => {
                ctx.fillStyle = 'white'; ctx.beginPath(); ctx.arc(c.x, c.y, hr2, 0, Math.PI * 2); ctx.fill();
                ctx.strokeStyle = cornerColors[ci]; ctx.lineWidth = 2.5 / viewScale; ctx.stroke();
            });
            ctx.restore();
        } else {
            // ── Normal scale/rotate preview ──
            const b = modSelBounds;
            const cx = b.x + b.w / 2;
            const cy = b.y + b.h / 2;
            if (isImportingNewImage) {
                ctx.translate(cx, cy);
                ctx.rotate(modSelRotation);
                ctx.scale(modSelFlipX, modSelFlipY);
                ctx.translate(-cx, -cy);
                ctx.drawImage(modSelCanvas, b.x, b.y, b.w, b.h);
            }
            ctx.strokeStyle = '#ff00ff'; ctx.lineWidth = 2 / viewScale; ctx.setLineDash([]);
            ctx.strokeRect(b.x, b.y, b.w, b.h);
            ctx.restore();

            // ── Draw handles & rotation lever ──
            ctx.save();
            const hr = HANDLE_R / viewScale;
            const rotDist = 40 / viewScale;
            const topCenterX = b.x + b.w / 2;
            const topCenterY = b.y;
            const drawH = (hx, hy) => {
                const dx = hx - cx, dy = hy - cy;
                const rx = dx * Math.cos(modSelRotation) - dy * Math.sin(modSelRotation);
                const ry = dx * Math.sin(modSelRotation) + dy * Math.cos(modSelRotation);
                ctx.fillStyle = 'white'; ctx.beginPath(); ctx.arc(cx + rx, cy + ry, hr, 0, Math.PI * 2); ctx.fill();
                ctx.strokeStyle = '#ff00ff'; ctx.lineWidth = 2 / viewScale; ctx.setLineDash([]); ctx.stroke();
            };
            const dxL = topCenterX - rotDist * 0 - cx, dyL = topCenterY - rotDist - cy;
            const rxL = dxL * Math.cos(modSelRotation) - dyL * Math.sin(modSelRotation);
            const ryL = dxL * Math.sin(modSelRotation) + dyL * Math.cos(modSelRotation);
            const dxTC = topCenterX - cx, dyTC = topCenterY - cy;
            const rxTC = dxTC * Math.cos(modSelRotation) - dyTC * Math.sin(modSelRotation);
            const ryTC = dxTC * Math.sin(modSelRotation) + dyTC * Math.cos(modSelRotation);
            ctx.strokeStyle = '#ff00ff'; ctx.lineWidth = 2 / viewScale;
            ctx.beginPath(); ctx.moveTo(cx + rxTC, cy + ryTC); ctx.lineTo(cx + rxL, cy + ryL); ctx.stroke();
            ctx.fillStyle = '#ff00ff'; ctx.beginPath(); ctx.arc(cx + rxL, cy + ryL, hr * 1.2, 0, Math.PI * 2); ctx.fill();
            ctx.strokeStyle = 'white'; ctx.stroke();
            const handlePositions = [
                [b.x, b.y], [b.x + b.w / 2, b.y], [b.x + b.w, b.y],
                [b.x, b.y + b.h / 2], [b.x + b.w, b.y + b.h / 2],
                [b.x, b.y + b.h], [b.x + b.w / 2, b.y + b.h], [b.x + b.w, b.y + b.h],
            ];
            handlePositions.forEach(([hx, hy]) => drawH(hx, hy));
            ctx.restore();
        }

        // Update flip buttons position
        updateFlipButtonsPosition();
    } else {
        if (flipControls) flipControls.classList.add('hidden');
    }

    // ── Draw canvas resize preview ──
    if (isResizingCanvas) {
        const nw = resizePreviewW;
        const nh = resizePreviewH;

        let ox = 0, oy = 0;
        if (resizeLibre) {
            ox = resizeOffsetX;
            oy = resizeOffsetY;
        } else {
            const dw = nw - paperWidth;
            const dh = nh - paperHeight;
            const col = resizeAnchor[1]; // l, c, r
            const row = resizeAnchor[0]; // t, m, b
            if (col === 'c') ox = Math.round(dw / 2);
            else if (col === 'r') ox = dw;
            if (row === 'm') oy = Math.round(dh / 2);
            else if (row === 'b') oy = dh;
        }

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
        const hr = (HANDLE_R + 2) / viewScale;
        const handlePositions = [
            [-ox, -oy], [-ox + nw / 2, -oy], [-ox + nw, -oy],
            [-ox, -oy + nh / 2], [-ox + nw, -oy + nh / 2],
            [-ox, -oy + nh], [-ox + nw / 2, -oy + nh], [-ox + nw, -oy + nh],
        ];
        handlePositions.forEach(([hx, hy]) => {
            ctx.fillStyle = 'white';
            ctx.beginPath(); ctx.arc(hx, hy, hr, 0, Math.PI * 2); ctx.fill();
            ctx.strokeStyle = '#0066ff';
            ctx.lineWidth = 3 / viewScale; // Thicker border for "physical" feel
            ctx.setLineDash([]);
            ctx.stroke();
            // Inner dot for more detail
            ctx.fillStyle = '#0066ff';
            ctx.beginPath(); ctx.arc(hx, hy, hr * 0.4, 0, Math.PI * 2); ctx.fill();
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

    // ── Draw persistent selection mask outline (static cached) ──
    if (hasSelection && selectionOutlineCanvas) {
        ctx.save();
        ctx.drawImage(selectionOutlineCanvas, 0, 0);
        ctx.restore();
    }

    // ── Draw filter lasso preview ──
    if (activeFilterType === 'chroma' && isDrawing && (chromaLassoMode === 'add' || chromaLassoMode === 'sub' || chromaLassoMode === 'clear') && lassoPath.length > 1) {
        ctx.save();
        ctx.globalAlpha = 0.5;
        if (chromaLassoMode === 'clear') {
            ctx.fillStyle = 'rgba(255, 255, 255, 0.4)';
            ctx.strokeStyle = '#607d8b';
        } else {
            ctx.fillStyle = chromaLassoMode === 'add' ? 'rgba(76, 175, 80, 0.4)' : 'rgba(244, 67, 54, 0.4)';
            ctx.strokeStyle = chromaLassoMode === 'add' ? '#4caf50' : '#f44336';
        }
        ctx.beginPath(); ctx.moveTo(lassoPath[0].x, lassoPath[0].y); lassoPath.forEach(p => ctx.lineTo(p.x, p.y)); ctx.closePath(); ctx.fill();
        ctx.lineWidth = 2 / viewScale; ctx.setLineDash([5 / viewScale, 5 / viewScale]);
        ctx.beginPath(); ctx.moveTo(lassoPath[0].x, lassoPath[0].y); lassoPath.forEach(p => ctx.lineTo(p.x, p.y)); ctx.closePath(); ctx.stroke();
        ctx.restore();
    }

    ctx.restore();

    // Rotation pivot dot
    if (currentTool === 'rotate' && isDrawing) {
        ctx.beginPath(); ctx.arc(rotationPivot.sx, rotationPivot.sy, 5, 0, Math.PI * 2);
        ctx.fillStyle = 'rgba(0,0,0,0.4)'; ctx.fill(); ctx.strokeStyle = 'white'; ctx.stroke();
    }
    // ── Software Cursor (Drawn in screen space) ──
    if (cursorMode === 'always' || (cursorMode === 'auto' && !isDrawing)) {
        const isBrush = (currentTool === 'pincel' || currentTool === 'push');
        if (isBrush) {
            const screenR = baseBrushSize * viewScale;
            ctx.beginPath();
            ctx.arc(screenCursorX, screenCursorY, screenR, 0, Math.PI * 2);
            ctx.strokeStyle = 'rgba(255,255,255,0.6)';
            ctx.lineWidth = 1.5;
            ctx.stroke();
            ctx.beginPath();
            ctx.arc(screenCursorX, screenCursorY, screenR, 0, Math.PI * 2);
            ctx.strokeStyle = 'rgba(0,0,0,0.2)';
            ctx.lineWidth = 0.5;
            ctx.stroke();
        }
        ctx.drawImage(customCursorImg, screenCursorX, screenCursorY);
    }
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
    if (currentTool === 'bucket') {
        const t = toolsData.find(x => x.id === 'bucket');
        if (t) brushOpacity = t.opacity !== undefined ? t.opacity : 1.0;
        baseBrushSize = currentBrush.size;
        currentBlur = currentBrush.blur;
    } else {
        baseBrushSize = currentBrush.size;
        brushOpacity = currentBrush.opacity;
        currentBlur = currentBrush.blur;
    }

    if (currentTool === 'push') {
        sizeSlider.min = 0;
        sizeSlider.max = 30;
    } else {
        sizeSlider.min = 0.1;
        sizeSlider.max = 100;
    }

    sizeSlider.value = baseBrushSize;
    sizeValue.textContent = baseBrushSize < 10 ? baseBrushSize.toFixed(1) : Math.round(baseBrushSize);

    const opPct = Math.round(brushOpacity * 100);
    opacitySlider.value = opPct;
    opacityValue.textContent = opPct + '%';
    if (eyeIcon) eyeIcon.src = opPct === 0 ? 'simbolo ojo cerrado.png' : 'simbolo ojo abierto.png';

    blurSlider.value = currentBlur;
    if (blurValueLabel) blurValueLabel.textContent = currentBlur;
}

function selectTool(id, name) {
    if (activeFilterType) {
        if (id !== 'zoom' && id !== 'pan') return; // Only allow zoom/pan
        chromaLassoMode = 'none'; // Disable lasso when navigating
        // Remove highlighting from chroma lasso buttons
        document.querySelectorAll('.chroma-lasso-btn').forEach(b => b.style.boxShadow = '');
    }
    if (currentTool === 'modify-sel' && id !== 'modify-sel' && modSelInitialized) commitModifySelection();
    if (currentTool === 'push') {
        const isTargetPush = (id === 'push' || (id === 'pincel' && name === 'Empujar'));
        if (!isTargetPush) {
            endPushSession();
        }
    }

    if (isResizingCanvas) {
        isResizingCanvas = false;
        resizePanel.classList.add('hidden');
    }

    if (id === 'pincel') {
        const b = brushTypesData.find(x => x.name === name);
        document.querySelector('.tool-btn.active')?.classList.remove('active');
        document.getElementById('btn-brush')?.classList.add('active');

        if (b && b.isPush) {
            currentTool = 'push';
            if (activeToolIndicator) activeToolIndicator.textContent = name;
            currentBrush = b;
        } else {
            currentTool = 'pincel'; lastBrushTool = name;
            if (activeToolIndicator) activeToolIndicator.textContent = name;
            if (b) currentBrush = b;
        }
    } else if (id === 'push') {
        currentTool = 'push';
        if (activeToolIndicator) activeToolIndicator.textContent = name;
        const b = brushTypesData.find(x => x.isPush);
        if (b) currentBrush = b;
    } else {
        currentTool = id;
        if (activeToolIndicator) activeToolIndicator.textContent = name;
    }
    showSelectionButtons(id);
    // Show / hide bucket settings panel
    showBucketPanel(id === 'bucket');

    // Load this brush's remembered size / opacity / blur into the UI
    syncBrushUI();

    // Show/Hide Blur slider
    const isBlurTool = (currentBrush.id === 'aero-duro' || currentBrush.id === 'aero-suave' ||
        currentBrush.isBlur || currentBrush.isGaussBlur);
    if (id === 'pincel' && isBlurTool) {
        blurSettingsContainer.classList.remove('hidden');
        if (currentBrush.isGaussBlur) {
            blurSlider.min = 1; blurSlider.max = 40;
            if (currentBrush.blur > 40) currentBrush.blur = 40;
            if (currentBrush.blur < 1) currentBrush.blur = 1;
        } else {
            blurSlider.min = 0; blurSlider.max = 100;
        }
    } else {
        blurSettingsContainer.classList.add('hidden');
    }

    if (id === 'eyedropper') {
        eyedropperPreview?.classList.remove('hidden');
        // Wire toggle button (only once)
        const modeBtn = document.getElementById('eyedropper-mode-btn');
        if (modeBtn && !modeBtn._wired) {
            modeBtn._wired = true;
            modeBtn.addEventListener('pointerdown', (ev) => {
                ev.stopPropagation();
                eyedropperMode = eyedropperMode === 'captura' ? 'original' : 'captura';
                modeBtn.textContent = eyedropperMode === 'original' ? '🎨 Original' : '📷 Captura';
                modeBtn.style.background = eyedropperMode === 'original'
                    ? 'rgba(0,180,80,0.75)' : 'rgba(0,0,0,0.55)';
            });
        }
    } else {
        eyedropperPreview?.classList.add('hidden');
    }

    updateTintedTexture();
}

function rgbToHex(r, g, b) {
    return "#" + ((1 << 24) + (r << 16) + (g << 8) + b).toString(16).slice(1).toUpperCase();
}

function hexToRgbArray(hex) {
    const r = parseInt(hex.slice(1, 3), 16);
    const g = parseInt(hex.slice(3, 5), 16);
    const b = parseInt(hex.slice(5, 7), 16);
    return [r, g, b];
}

function pickColorAt(worldX, worldY) {
    const startX = Math.floor(worldX); const startY = Math.floor(worldY);
    if (startX < 0 || startX >= paperWidth || startY < 0 || startY >= paperHeight) return null;

    const temp = document.createElement('canvas'); temp.width = 1; temp.height = 1;
    const tctx = temp.getContext('2d');

    if (bgMode === 1) { tctx.fillStyle = solidBgColor; tctx.fillRect(0, 0, 1, 1); }

    layers.forEach(l => {
        if (!l.visible) return;
        tctx.save();
        tctx.globalAlpha = l.opacity;
        tctx.globalCompositeOperation = l.blendMode;
        tctx.drawImage(l.canvas, -startX, -startY);
        tctx.restore();
    });

    const data = tctx.getImageData(0, 0, 1, 1).data;
    return rgbToHex(data[0], data[1], data[2]);
}

/**
 * Mode 2: Read raw pixel from the most relevant layer, ignoring blend modes.
 * Priority: active layer first, then search top-to-bottom for any visible layer with an opaque pixel.
 * Falls back to background color if all are transparent.
 */
function pickColorRaw(worldX, worldY) {
    const px = Math.floor(worldX); const py = Math.floor(worldY);
    if (px < 0 || px >= paperWidth || py < 0 || py >= paperHeight) return null;

    const byteIndex = (py * paperWidth + px) * 4;

    // 1. Try active layer first
    const active = layers[selectedLayerIndex];
    if (active && active.visible) {
        const d = active.ctx.getImageData(px, py, 1, 1).data;
        if (d[3] > 0) return rgbToHex(d[0], d[1], d[2]);
    }

    // 2. Search layers top-to-bottom (excluding active, already tried)
    for (let i = layers.length - 1; i >= 0; i--) {
        if (i === selectedLayerIndex) continue;
        const l = layers[i];
        if (!l.visible) continue;
        const d = l.ctx.getImageData(px, py, 1, 1).data;
        if (d[3] > 0) return rgbToHex(d[0], d[1], d[2]);
    }

    // 3. No layer has a pixel here — return background
    if (bgMode === 1) return solidBgColor;
    return '#ffffff';
}

function updateEyedropperPreview(screenX, screenY, worldX, worldY) {
    if (!eyedropperPreview || eyedropperPreview.classList.contains('copied')) return;
    eyedropperPreview.style.left = screenX + 'px';
    eyedropperPreview.style.top  = screenY + 'px';

    const color = (eyedropperMode === 'original' ? pickColorRaw(worldX, worldY) : pickColorAt(worldX, worldY)) || '#000000';
    const circle = eyedropperPreview.querySelector('.color-circle');
    const hex    = eyedropperPreview.querySelector('.color-hex');
    const modeEl = eyedropperPreview.querySelector('.ed-mode-label');
    if (circle) circle.style.background = color;
    if (hex)    hex.textContent = color;
    if (modeEl) modeEl.textContent = eyedropperMode === 'original' ? '🎨 Original' : '📷 Captura';
}



function handleGlobalShortcuts(e) {
    if (e.target.tagName === 'INPUT' || e.target.tagName === 'SELECT') return;
    const key = e.key.toLowerCase();

    // Allow Zoom and Pan shortcuts during filters
    if (activeFilterType) {
        if (activeFilterType === 'levels' && (e.key === 'ArrowUp' || e.key === 'ArrowDown')) {
            const channels = ['rgb', 'r', 'g', 'b'];
            let idx = channels.indexOf(activeCurveChannel);
            if (e.key === 'ArrowUp') idx = (idx - 1 + channels.length) % channels.length;
            else idx = (idx + 1) % channels.length;
            
            const select = document.getElementById('curveChannelSelect');
            if (select) {
                select.value = channels[idx];
                select.dispatchEvent(new Event('change'));
            }
            e.preventDefault();
            return;
        }

        const qS = brushTypesData.find(b => b.id === 'lazo-relleno')?.shortcut || 'q';
        const sS = brushTypesData.find(b => b.id === 'borrador')?.shortcut || 's';
        const wS = brushTypesData.find(b => b.id === 'lazo-borrador')?.shortcut || 'w';

        if (key === qS) { selectChromaLasso('add'); return; }
        if (key === sS) { selectChromaLasso('clear'); return; }
        if (key === wS) { selectChromaLasso('sub'); return; }
        if (key !== 'z' && key !== 'x') return;
    }

    if (!activeFilterType && !isModifyingShape && layerImportState === 0) {
        if (e.key === 'ArrowUp' || e.key === 'ArrowDown') {
            e.preventDefault();
            if (layers.length > 1) {
                endPushSession();
                if (e.key === 'ArrowUp') {
                    selectedLayerIndex = (selectedLayerIndex + 1) % layers.length;
                } else {
                    selectedLayerIndex = (selectedLayerIndex - 1 + layers.length) % layers.length;
                }
                updateLayersUI();
                pushHistory();
                requestRender();
            }
            return;
        }
    }

    const ms = (mainShortcutInput?.value || '').toLowerCase();
    const bs = (brushShortcutInput?.value || '').toLowerCase();
    const ls = (layersShortcutInput?.value || '').toLowerCase();
    const cs = (colorsShortcutInput?.value || '').toLowerCase();
    const cfs = (configShortcutInput?.value || '').toLowerCase();
    const nls = (newLayerShortcut || '').toLowerCase();

    if (key === nls && nls !== '') { addLayer("Nueva Capa"); return; }

    if (key === ms && ms !== '') { toggleMenu(multiToolMenu); return; }
    if (key === bs && bs !== '') { toggleMenu(brushTypeMenu); return; }
    if (key === ls && ls !== '') { toggleMenu(layersMenu); return; }
    if (key === cs && cs !== '') { toggleMenu(colorsMenu); return; }
    if (key === cfs && cfs !== '') { toggleMenu(configMenu); return; }

    if (e.ctrlKey && key === 'c') { e.preventDefault(); copyToClipboard(); return; }
    if (e.ctrlKey && key === 'x') { e.preventDefault(); cutToClipboard(); return; }
    if (e.ctrlKey && e.altKey && key === 'v') {
        if (startupImportState === 1 || layerImportState === 1) return;
        e.preventDefault(); pasteFromClipboard(true); return; 
    }
    if (e.ctrlKey && key === 'v') {
        if (startupImportState === 1 || layerImportState === 1) return; // Let the window 'paste' listener handle it
        e.preventDefault(); pasteFromClipboard(false); return;
    }
    if (e.ctrlKey && (key === 'z') && !e.shiftKey) { 
        e.preventDefault(); 
        if (isModifyingShape) {
            isModifyingShape = false;
            modSelInitialized = false; 
            modSelCanvas = null; 
            modSelBounds = null; 
            modSelOrigBounds = null;
            modSelRotation = 0; modSelFlipX = 1; modSelFlipY = 1;
            modSelLayersData = [];
            if (flipControls) flipControls.classList.add('hidden');
            selectTool('pincel', 'Pincel');
            updateThumbnails(); updateLayersUI();
            requestRender();
            return;
        }
        undo(); 
        return; 
    }
    if (e.ctrlKey && (key === 'y' || (e.shiftKey && key === 'z'))) { e.preventDefault(); redo(); return; }

    if (e.key === 'Enter' || e.key === 'Escape') {
        if (modSelInitialized) {
            e.preventDefault();
            commitModifySelection();
            if (e.key === 'Escape') clearSelection();
            return;
        }
        if (e.key === 'Escape' && hasSelection) {
            clearSelection();
            return;
        }
    }

    if (e.key === 'Delete' && hasSelection && !modSelInitialized) {
        e.preventDefault();
        const l = layers[selectedLayerIndex];
        l.ctx.save();
        l.ctx.globalCompositeOperation = 'destination-out';
        l.ctx.drawImage(selectionCanvas, 0, 0);
        l.ctx.restore();
        clearSelection(); // Remove selection mask after deletion
        updateThumbnails(); updateLayersUI();
        pushHistory();
        return;
    }

    const t = toolsData.find(x => {
        const k = (x.shortcut || '').toLowerCase();
        if (!k || k !== key) return false;
        const mod = x.modifier || 'normal';
        if (mod === '+shift') return e.shiftKey && !e.ctrlKey;
        if (mod === '+shift+ctrl') return e.shiftKey && e.ctrlKey;
        return !e.shiftKey && !e.ctrlKey;
    });
    if (t) { selectTool(t.id, t.name); return; }
    const bt = brushTypesData.find(x => {
        const k = (x.shortcut || '').toLowerCase();
        if (!k || k !== key) return false;
        const mod = x.modifier || 'normal';
        if (mod === '+shift') return e.shiftKey && !e.ctrlKey;
        if (mod === '+shift+ctrl') return e.shiftKey && e.ctrlKey;
        return !e.shiftKey && !e.ctrlKey;
    });
    if (bt) { selectTool('pincel', bt.name); return; }

    // Check palette shortcuts
    const pc = paletteColors.find(p => (p.s || '').toLowerCase() === key);
    if (pc && pc.c) {
        selectedColor = pc.c;
        mainColorPicker.value = pc.c;
        updateTintedTexture();
    }
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
        const nameSpan = document.createElement('span');
        nameSpan.textContent = item.name;
        const shortcutInput = document.createElement('input');
        shortcutInput.type = 'text';
        shortcutInput.className = 'tool-shortcut-input';
        shortcutInput.maxLength = 1;
        shortcutInput.value = item.shortcut || '';
        const modSelect = document.createElement('select');
        modSelect.className = 'tool-shortcut-modifier';
        modSelect.style.cssText = 'font-size:10px; padding:1px 2px; border:1px solid #ccc; border-radius:3px; background:#222; color:#ddd; cursor:pointer; margin-left:3px;';
        modSelect.title = 'Modificador del atajo';
        [['normal', 'Normal'], ['+shift', '+Shift'], ['+shift+ctrl', '+Shift+Ctrl']].forEach(([v, l]) => {
            const opt = document.createElement('option');
            opt.value = v; opt.textContent = l;
            if ((item.modifier || 'normal') === v) opt.selected = true;
            modSelect.appendChild(opt);
        });
        modSelect.onchange = () => { item.modifier = modSelect.value; saveShortcuts(); };
        li.appendChild(nameSpan);
        li.appendChild(shortcutInput);
        li.appendChild(modSelect);
        li.onclick = e => { if (e.target.tagName !== 'INPUT' && e.target.tagName !== 'SELECT') { type === 'brush' ? selectTool('pincel', item.name) : selectTool(item.id, item.name); } };
        shortcutInput.onkeydown = e => { if (e.key.length === 1) { e.preventDefault(); checkAndAssignShortcut(item, e.key.toLowerCase(), type); } };
        cont.appendChild(li);
    });
}
function checkAndAssignShortcut(item, key, type) {
    // Read the modifier currently selected in the dropdown for this item
    const itemModifier = item.modifier || 'normal';
    const combo = key + '|' + itemModifier; // unique combo: e.g. "b|normal" vs "b|+shift"

    const ms = (mainShortcutInput?.value || '').toLowerCase(), bs = (brushShortcutInput?.value || '').toLowerCase(), ls = (layersShortcutInput?.value || '').toLowerCase(), cs = (colorsShortcutInput?.value || '').toLowerCase();

    // Menu-level shortcuts only use 'normal' modifier, so only conflict if modifier is also 'normal'
    let conflict = null;
    if (itemModifier === 'normal') {
        conflict = key === ms ? 'Atajo Principal' : key === bs ? 'Atajo Pincel' : key === ls ? 'Atajo Capas' : key === cs ? 'Atajo Colores' : null;
    }

    // Check tool/brush conflicts: same key AND same modifier
    const tc = toolsData.find(t => (t.shortcut || '').toLowerCase() === key && (t.modifier || 'normal') === itemModifier && t !== item);
    const bc = brushTypesData.find(b => (b.shortcut || '').toLowerCase() === key && (b.modifier || 'normal') === itemModifier && b !== item);
    // Palette shortcuts are always 'normal'
    const cc = itemModifier === 'normal' ? paletteColors.find(p => (p.s || '').toLowerCase() === key) : null;

    if (tc) conflict = tc.name;
    else if (bc) conflict = bc.name;
    else if (cc) conflict = `Color en paleta (${cc.c})`;

    const modLabel = itemModifier === 'normal' ? '' : ' (' + itemModifier + ')';
    if (conflict) {
        if (confirm(`La tecla "${key.toUpperCase()}${modLabel}" ya está siendo usada por "${conflict}". ¿Quieres sobrescribirla?`)) {
            if (itemModifier === 'normal') {
                if (key === ms && mainShortcutInput) mainShortcutInput.value = '';
                if (key === bs && brushShortcutInput) brushShortcutInput.value = '';
                if (key === ls && layersShortcutInput) layersShortcutInput.value = '';
                if (key === cs && colorsShortcutInput) colorsShortcutInput.value = '';
            }
            if (tc) tc.shortcut = '';
            else if (bc) bc.shortcut = '';
            if (cc) cc.s = null;

            item.shortcut = key;
            saveShortcuts();
            savePalette();
        }
    } else { item.shortcut = key; saveShortcuts(); }
    setupMultiToolMenu(); setupBrushMenu(); renderPalette();
}
function saveShortcuts() {
    localStorage.setItem('illustrator_state_v13', JSON.stringify({
        main: mainShortcutInput?.value || '', brushMenu: brushShortcutInput?.value || '',
        layersMenu: layersShortcutInput?.value || '', colorsMenu: colorsShortcutInput?.value || '',
        config: configShortcutInput?.value || '',
        newLayer: newLayerShortcut,
        tools: toolsData.map(t => ({ id: t.id, shortcut: t.shortcut, modifier: t.modifier || 'normal' })),
        brushes: brushTypesData.map(b => ({ id: b.id, shortcut: b.shortcut, modifier: b.modifier || 'normal' }))
    }));
}
function loadShortcuts() {
    const saved = localStorage.getItem('illustrator_state_v13'); if (!saved) return;
    try {
        const s = JSON.parse(saved);
        if (mainShortcutInput) mainShortcutInput.value = s.main || '+';
        if (brushShortcutInput) brushShortcutInput.value = s.brushMenu || '}';
        if (layersShortcutInput) layersShortcutInput.value = s.layersMenu || '.';
        if (colorsShortcutInput) colorsShortcutInput.value = s.colorsMenu || '-';
        if (configShortcutInput) configShortcutInput.value = s.config || '{';
        newLayerShortcut = s.newLayer !== undefined ? s.newLayer : '*';
        s.tools?.forEach(st => { const t = toolsData.find(x => x.id === st.id); if (t) { t.shortcut = st.shortcut || t.shortcut; t.modifier = st.modifier || 'normal'; } });
        s.brushes?.forEach(sb => { const b = brushTypesData.find(x => x.id === sb.id); if (b) { b.shortcut = sb.shortcut || b.shortcut; b.modifier = sb.modifier || 'normal'; } });
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
