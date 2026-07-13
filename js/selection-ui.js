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

    // Eyedropper Mode button
    eyedropperModeBtn = document.createElement('button');
    eyedropperModeBtn.id = 'eyedropper-mode-indicator-btn';
    eyedropperModeBtn.className = 'indicator-extra-btn hidden';
    eyedropperModeBtn.onclick = () => {
        eyedropperMode = eyedropperMode === 'captura' ? 'original' : 'captura';
        updateEyedropperModeUI();
    };
    container.appendChild(eyedropperModeBtn);

    // Fill-Lasso / Lasso-Eraser draw mode button
    lassoFillModeBtn = document.createElement('button');
    lassoFillModeBtn.id = 'lasso-fill-mode-btn';
    lassoFillModeBtn.className = 'indicator-extra-btn hidden';
    lassoFillModeBtn.onclick = () => {
        lassoFillMode = lassoFillMode === 'libre' ? 'rectangulo' : 'libre';
        updateLassoFillModeUI();
    };
    container.appendChild(lassoFillModeBtn);
}

function updateEyedropperModeUI() {
    if (!eyedropperModeBtn) return;
    eyedropperModeBtn.textContent = eyedropperMode === 'original' ? '🎨 ORIGINAL' : '📷 CAPTURA';
    eyedropperModeBtn.style.background = eyedropperMode === 'original'
        ? 'rgba(0,180,80,0.75)' : 'rgba(0,0,0,0.55)';
}

function updateLassoFillModeUI() {
    if (!lassoFillModeBtn) return;
    const isRect = lassoFillMode === 'rectangulo';
    lassoFillModeBtn.textContent = isRect ? '⬛ RECTÁNGULO' : '✏️ LIBRE';
    lassoFillModeBtn.style.background = isRect ? '#0066ff' : '';
    lassoFillModeBtn.style.color = isRect ? 'white' : '';
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
    [lassoSelBtn, lassoDesBtn, modifySelBtn, clearSelBtn, shapeFillBtn, shapeFromCenterBtn, shapeModifiableBtn, fitScreenBtn, eyedropperModeBtn, lassoFillModeBtn].forEach(b => { if (b) b.classList.add('hidden'); });

    if (tool === 'lazo-sel') { if (lassoSelBtn) lassoSelBtn.classList.remove('hidden'); if (hasSelection && clearSelBtn) clearSelBtn.classList.remove('hidden'); }
    if (tool === 'lazo-des') { if (lassoDesBtn) lassoDesBtn.classList.remove('hidden'); if (hasSelection && clearSelBtn) clearSelBtn.classList.remove('hidden'); }
    if (tool === 'modify-sel') { if (modifySelBtn) modifySelBtn.classList.remove('hidden'); if (clearSelBtn) clearSelBtn.classList.remove('hidden'); }
    if (tool === 'bucket') { /* bucket panel handled by showBucketPanel() */ }
    
    if (tool === 'eyedropper') {
        if (eyedropperModeBtn) {
            eyedropperModeBtn.classList.remove('hidden');
            updateEyedropperModeUI();
        }
    }

    if (tool === 'pincel' && currentBrush.isLasso) {
        if (lassoFillModeBtn) {
            lassoFillModeBtn.classList.remove('hidden');
            updateLassoFillModeUI();
        }
    }

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

