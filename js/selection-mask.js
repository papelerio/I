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
