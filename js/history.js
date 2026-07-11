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

