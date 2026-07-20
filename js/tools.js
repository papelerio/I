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
    if (eyeIcon) eyeIcon.src = opPct === 0 ? 'simbolo ojo cerrado.png' : 'imagenes/simbolo ojo abierto.png';

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
    } else {
        eyedropperPreview?.classList.add('hidden');
    }

    // Refresh active states in the grid menus
    if (typeof setupMultiToolMenu === 'function') setupMultiToolMenu();
    if (typeof setupBrushMenu === 'function') setupBrushMenu();

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
