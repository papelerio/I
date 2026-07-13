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
const configMenu = document.getElementById('config-menu');
const resizePanel = document.getElementById('resize-panel');

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
let currentProjectId = null;     // ID of current project (null if none loaded)
let currentProjectTitle = 'Sin título'; // Title of current project
let currentProjectTime = 0;      // Accumulated active editing time in seconds
let currentProjectOrder = 0;     // Drag order weight of current project
let projectTimerInterval = null; // Timer interval for active time tracking
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
let lassoFillMode = 'libre';    // 'libre' | 'rectangulo' — fill/eraser lasso draw mode
let lassoFillStartX = 0, lassoFillStartY = 0; // anchor for rectangle mode
let lassoFillModeBtn = null;    // top-left indicator button for fill-lasso mode
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
let eyedropperModeBtn = null; // Eyedropper mode toggle button in indicator container
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

