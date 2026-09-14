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
