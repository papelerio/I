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

    // Save active frame state first if in animation mode
    if (typeof isAnimationMode !== 'undefined' && isAnimationMode && typeof saveCurrentFrameState === 'function') {
        saveCurrentFrameState();
    }

    // Helper function to resize a single layer
    const resizeSingleLayer = (l) => {
        const newCanvas = document.createElement('canvas');
        newCanvas.width = newW; newCanvas.height = newH;
        const newCtx = newCanvas.getContext('2d', { willReadFrequently: true });
        newCtx.drawImage(l.canvas, ox, oy);
        l.canvas = newCanvas;
        l.ctx = newCtx;
    };

    // Resize active layers
    layers.forEach(resizeSingleLayer);

    // If in animation mode, resize ALL layers in ALL animation frames
    if (typeof isAnimationMode !== 'undefined' && isAnimationMode && typeof animationFrames !== 'undefined' && Array.isArray(animationFrames)) {
        animationFrames.forEach((frame, fIdx) => {
            if (fIdx === currentFrameIndex) {
                frame.layers = layers;
            } else if (frame && Array.isArray(frame.layers)) {
                frame.layers.forEach(resizeSingleLayer);
            }
        });
    }

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
        const newSelCtx = newSel.getContext('2d', { willReadFrequently: true });
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
    if (typeof isAnimationMode !== 'undefined' && isAnimationMode && typeof updateFrameThumbnails === 'function') {
        updateFrameThumbnails();
    }
    pushHistory(); // snapshot AFTER resize
    requestRender();
}

/**
 * Rota todo el lienzo (y todas las capas) 90° a la derecha o a la izquierda.
 * direction: 'cw'  → sentido horario (derecha, +90°)
 *            'ccw' → sentido antihorario (izquierda, −90°)
 *
 * La rotación se hace desde el centro del lienzo actual, de modo que
 * cualquier valor de ancho/alto/offset previamente configurado queda
 * correctamente incorporado: el nuevo ancho = alto anterior y viceversa.
 */
function rotateCanvas(direction) {
    endPushSession();

    if (typeof isAnimationMode !== 'undefined' && isAnimationMode && typeof saveCurrentFrameState === 'function') {
        saveCurrentFrameState();
    }

    const oldW = paperWidth;
    const oldH = paperHeight;
    const newW = oldH;   // tras rotar 90° el ancho y el alto se intercambian
    const newH = oldW;

    // Función auxiliar: dibuja un canvas fuente rotado sobre uno nuevo
    function rotateLayerCanvas(srcCanvas) {
        const dst = document.createElement('canvas');
        dst.width  = newW;
        dst.height = newH;
        const ctx = dst.getContext('2d', { willReadFrequently: true });
        ctx.translate(newW / 2, newH / 2);
        ctx.rotate(direction === 'cw' ? Math.PI / 2 : -Math.PI / 2);
        ctx.drawImage(srcCanvas, -oldW / 2, -oldH / 2);
        return dst;
    }

    // Rotar todas las capas activas
    layers.forEach(l => {
        const rotated = rotateLayerCanvas(l.canvas);
        l.canvas = rotated;
        l.ctx    = rotated.getContext('2d', { willReadFrequently: true });
    });

    // Si está en modo animación, rotar todas las capas de TODOS los fotogramas
    if (typeof isAnimationMode !== 'undefined' && isAnimationMode && typeof animationFrames !== 'undefined' && Array.isArray(animationFrames)) {
        animationFrames.forEach((frame, fIdx) => {
            if (fIdx === currentFrameIndex) {
                frame.layers = layers;
            } else if (frame && Array.isArray(frame.layers)) {
                frame.layers.forEach(l => {
                    const rotated = rotateLayerCanvas(l.canvas);
                    l.canvas = rotated;
                    l.ctx = rotated.getContext('2d', { willReadFrequently: true });
                });
            }
        });
    }

    // Actualizar dimensiones lógicas
    paperWidth  = newW;
    paperHeight = newH;

    // Rotar buffers compartidos (solo redimensionar, no rotar su contenido)
    const buffersToResize = [strokeCanvas, groupCanvas, maskBuffer,
                              selectionOutlineCanvas, layersCacheCanvas];
    buffersToResize.forEach(buf => {
        buf.width  = newW;
        buf.height = newH;
    });
    layersCacheDirty = true;

    // Rotar canvas de selección si existe
    if (selectionCanvas) {
        const rotatedSel = rotateLayerCanvas(selectionCanvas);
        selectionCanvas = rotatedSel;
        selCtx = rotatedSel.getContext('2d');
        if (!hasSelection) selCtx.clearRect(0, 0, newW, newH);
    }
    updateSelectionOutline();

    // Actualizar inputs del panel para reflejar el nuevo tamaño
    const wInput = document.getElementById('resize-width');
    const hInput = document.getElementById('resize-height');
    if (wInput) wInput.value = newW;
    if (hInput) hInput.value = newH;

    // Sincronizar preview de resize
    resizePreviewW = newW;
    resizePreviewH = newH;
    resizeOffsetX  = 0;
    resizeOffsetY  = 0;

    // Ajustar vista para que el lienzo rotado quepa en pantalla
    const winW = canvas.parentElement.clientWidth;
    const winH = canvas.parentElement.clientHeight;
    viewScale = Math.min(winW / (newW + 100), winH / (newH + 100));
    viewPosX  = 0;
    viewPosY  = 0;

    updateThumbnails();
    updateLayersUI();
    if (typeof isAnimationMode !== 'undefined' && isAnimationMode && typeof updateFrameThumbnails === 'function') {
        updateFrameThumbnails();
    }
    pushHistory();
    requestRender();
}

// ── Listeners de los botones de rotación ──
document.getElementById('rotate-canvas-left-btn').onclick  = () => rotateCanvas('ccw');
document.getElementById('rotate-canvas-right-btn').onclick = () => rotateCanvas('cw');

/**
 * Evaluates all layers (or frames in animation mode) to find the exact bounding box
 * of illustrated pixels exceeding the specified alpha threshold.
 */
function calculateAutoFitBounds(alphaThreshold = 10) {
    let layersToScan = [];

    if (typeof isAnimationMode !== 'undefined' && isAnimationMode && typeof animationFrames !== 'undefined' && Array.isArray(animationFrames) && animationFrames.length > 0) {
        animationFrames.forEach(f => {
            if (f && Array.isArray(f.layers)) {
                layersToScan.push(...f.layers);
            }
        });
    } else if (typeof layers !== 'undefined' && Array.isArray(layers)) {
        layersToScan = layers;
    }

    if (layersToScan.length === 0) {
        return { foundAny: false, contentW: 0, contentH: 0, minX: 0, minY: 0 };
    }

    const w = paperWidth;
    const h = paperHeight;
    let globalMinX = w;
    let globalMinY = h;
    let globalMaxX = -1;
    let globalMaxY = -1;
    let foundAny = false;

    layersToScan.forEach(l => {
        if (!l.ctx || !l.canvas) return;
        let data;
        try {
            data = l.ctx.getImageData(0, 0, w, h).data;
        } catch (e) {
            return;
        }

        let lMinX = w, lMinY = h, lMaxX = -1, lMaxY = -1;
        let lFound = false;

        // Top-down scan for minY
        for (let y = 0; y < h; y++) {
            const offset = y * w * 4;
            for (let x = 0; x < w; x++) {
                if (data[offset + x * 4 + 3] >= alphaThreshold) {
                    lMinY = y;
                    lFound = true;
                    break;
                }
            }
            if (lFound) break;
        }

        if (!lFound) return; // Layer is completely transparent above threshold

        // Bottom-up scan for maxY
        for (let y = h - 1; y >= lMinY; y--) {
            const offset = y * w * 4;
            let rowHasPixel = false;
            for (let x = 0; x < w; x++) {
                if (data[offset + x * 4 + 3] >= alphaThreshold) {
                    lMaxY = y;
                    rowHasPixel = true;
                    break;
                }
            }
            if (rowHasPixel) break;
        }

        // Left-right scan for minX
        for (let x = 0; x < w; x++) {
            let colHasPixel = false;
            for (let y = lMinY; y <= lMaxY; y++) {
                if (data[(y * w + x) * 4 + 3] >= alphaThreshold) {
                    lMinX = x;
                    colHasPixel = true;
                    break;
                }
            }
            if (colHasPixel) break;
        }

        // Right-left scan for maxX
        for (let x = w - 1; x >= lMinX; x--) {
            let colHasPixel = false;
            for (let y = lMinY; y <= lMaxY; y++) {
                if (data[(y * w + x) * 4 + 3] >= alphaThreshold) {
                    lMaxX = x;
                    colHasPixel = true;
                    break;
                }
            }
            if (colHasPixel) break;
        }

        if (lMinX < globalMinX) globalMinX = lMinX;
        if (lMinY < globalMinY) globalMinY = lMinY;
        if (lMaxX > globalMaxX) globalMaxX = lMaxX;
        if (lMaxY > globalMaxY) globalMaxY = lMaxY;
        foundAny = true;
    });

    if (!foundAny) {
        return { foundAny: false, contentW: 0, contentH: 0, minX: 0, minY: 0 };
    }

    const contentW = Math.max(1, globalMaxX - globalMinX + 1);
    const contentH = Math.max(1, globalMaxY - globalMinY + 1);

    return {
        foundAny: true,
        contentW,
        contentH,
        minX: globalMinX,
        minY: globalMinY,
        maxX: globalMaxX,
        maxY: globalMaxY
    };
}

/**
 * Calculates auto-fit bounds for current alpha threshold, updates modal text,
 * and sets up canvas resize preview guide box.
 */
function updateAutoFitBoundsAndGuide() {
    const slider = document.getElementById('autofit-alpha-slider');
    const threshold = parseInt(slider ? slider.value : 10) || 10;

    const res = calculateAutoFitBounds(threshold);
    const sizeEl = document.getElementById('autofit-result-size');
    const posEl = document.getElementById('autofit-result-pos');

    if (res.foundAny) {
        if (sizeEl) sizeEl.textContent = `${res.contentW} x ${res.contentH} px`;
        if (posEl) posEl.textContent = `(${res.minX}, ${res.minY})`;

        // Update visual preview guide box on the main canvas
        isResizingCanvas = true;
        resizeLibre = true;
        resizePreviewW = res.contentW;
        resizePreviewH = res.contentH;
        resizeOffsetX = -res.minX;
        resizeOffsetY = -res.minY;

        // Also sync input fields in main resize panel if open
        const wInput = document.getElementById('resize-width');
        const hInput = document.getElementById('resize-height');
        if (wInput) wInput.value = res.contentW;
        if (hInput) hInput.value = res.contentH;
    } else {
        if (sizeEl) sizeEl.textContent = 'Sin píxeles detectados';
        if (posEl) posEl.textContent = '(-, -)';
    }

    if (typeof requestRender === 'function') requestRender();
}

/**
 * Opens the dedicated Auto-Fit Bounding Box Modal with Alpha Threshold slider
 */
function openAutoFitModal() {
    const modal = document.getElementById('autofit-modal');
    if (!modal) return;

    modal.classList.remove('hidden');
    if (typeof makeDraggable === 'function') {
        const header = document.getElementById('autofit-header');
        if (header) makeDraggable(modal, header);
    }

    const slider = document.getElementById('autofit-alpha-slider');
    const valLabel = document.getElementById('autofit-alpha-val');

    if (slider) {
        // Fast numeric text update while dragging (no heavy calculation)
        slider.oninput = () => {
            if (valLabel) valLabel.textContent = slider.value;
        };

        // Heavy pixel scan & preview guide box update ONLY when user releases slider (onchange)
        slider.onchange = () => {
            if (valLabel) valLabel.textContent = slider.value;
            updateAutoFitBoundsAndGuide();
        };
    }

    updateAutoFitBoundsAndGuide();
}

/**
 * Applies the calculated auto-fit bounding box resize
 */
function applyAutoFit() {
    const slider = document.getElementById('autofit-alpha-slider');
    const threshold = parseInt(slider ? slider.value : 10) || 10;
    const res = calculateAutoFitBounds(threshold);

    if (!res.foundAny) {
        alert('No se encontraron píxeles que superen el umbral Alpha seleccionado.');
        return;
    }

    // Hide modals
    const modal = document.getElementById('autofit-modal');
    if (modal) modal.classList.add('hidden');
    const resizePanel = document.getElementById('resize-panel');
    if (resizePanel) resizePanel.classList.add('hidden');

    isResizingCanvas = false;
    resizeActiveHandle = null;
    canvas.style.cursor = '';

    // Set free offset crop position
    resizeLibre = true;
    resizeOffsetX = -res.minX;
    resizeOffsetY = -res.minY;

    // Apply canvas resize
    resizeCanvas(res.contentW, res.contentH);

    if (preResizeToolId) {
        selectTool(preResizeToolId, preResizeToolName);
        preResizeToolId = null;
        preResizeToolName = null;
    }
}

// ── Bindings para el modal de Ajuste Automático ──
const autoFitBtn = document.getElementById('resize-auto-fit-btn');
if (autoFitBtn) {
    autoFitBtn.onclick = openAutoFitModal;
}

const autofitApplyBtn = document.getElementById('autofit-apply-btn');
if (autofitApplyBtn) {
    autofitApplyBtn.onclick = applyAutoFit;
}

const autofitCancelBtn = document.getElementById('autofit-cancel-btn');
if (autofitCancelBtn) {
    autofitCancelBtn.onclick = () => {
        const modal = document.getElementById('autofit-modal');
        if (modal) modal.classList.add('hidden');

        // Hide canvas guide box if main resize-panel is also closed
        const resizePanel = document.getElementById('resize-panel');
        if (!resizePanel || resizePanel.classList.contains('hidden')) {
            isResizingCanvas = false;
        } else {
            // Restore main resize panel preview
            const wInput = document.getElementById('resize-width');
            const hInput = document.getElementById('resize-height');
            if (wInput && hInput) {
                resizePreviewW = parseInt(wInput.value) || paperWidth;
                resizePreviewH = parseInt(hInput.value) || paperHeight;
                resizeOffsetX = 0;
                resizeOffsetY = 0;
            }
        }
        if (typeof requestRender === 'function') requestRender();
    };
}
