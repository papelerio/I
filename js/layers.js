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
        visBtn.innerHTML = '<img src="imagenes/simbolo ojo abierto.png">';
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
