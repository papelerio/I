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

