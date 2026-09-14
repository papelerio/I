// ─────────────────────────────────────────────────────────────
//  ANIMATION SYSTEM (MÓDULO DE FOTOGRAMAS Y REPRODUCCIÓN)
// ─────────────────────────────────────────────────────────────

let animationEventsInitialized = false;
let contextMenuTargetIndex = -1;
const frameContextMenu = document.getElementById('frame-context-menu');

/**
 * Deep clones a layer structure including canvas contents
 */
function cloneLayerStructure(layer) {
    const newCanvas = document.createElement('canvas');
    newCanvas.width = paperWidth;
    newCanvas.height = paperHeight;
    const newCtx = newCanvas.getContext('2d');
    if (layer.canvas) {
        newCtx.drawImage(layer.canvas, 0, 0);
    }
    return {
        id: Date.now() + Math.random(),
        name: layer.name,
        canvas: newCanvas,
        ctx: newCtx,
        visible: layer.visible,
        opacity: layer.opacity,
        blendMode: layer.blendMode || 'source-over',
        clippingMask: !!layer.clippingMask,
        alphaLocked: !!layer.alphaLocked
    };
}

/**
 * Muestra el menú contextual en la posición del ratón
 */
function showFrameContextMenu(e, index) {
    e.preventDefault();
    e.stopPropagation();
    if (!frameContextMenu) return;
    contextMenuTargetIndex = index;

    const frame = animationFrames[index];
    if (frameCtxOnion && frame) {
        const isGuide = onionSkinFrames.has(frame.id);
        frameCtxOnion.innerHTML = isGuide ? '🧅 Dejar de ser guía' : '🧅 Usar de guía cebolla';
    }

    const menuW = 175;
    const menuH = 180;
    let posX = e.clientX;
    let posY = e.clientY - menuH;

    if (posY < 10) posY = e.clientY + 10;
    if (posX + menuW > window.innerWidth - 10) posX = window.innerWidth - menuW - 10;

    frameContextMenu.style.left = posX + 'px';
    frameContextMenu.style.top = posY + 'px';
    frameContextMenu.classList.remove('hidden');
}

/**
 * Oculta el menú contextual de fotogramas
 */
function hideFrameContextMenu() {
    if (frameContextMenu) {
        frameContextMenu.classList.add('hidden');
    }
}

/**
 * Saves active layers state into current frame slot in animationFrames array
 */
function saveCurrentFrameState() {
    if (!isAnimationMode || !animationFrames[currentFrameIndex]) return;
    animationFrames[currentFrameIndex].layers = layers;
}

/**
 * Updates UI elements for Animation Mode vs Illustration Mode
 */
function updateAnimationUIState(enabled) {
    const isAnim = !!enabled;
    if (typeof animationBottomBar !== 'undefined' && animationBottomBar) {
        if (isAnim) {
            animationBottomBar.classList.remove('hidden');
        } else {
            animationBottomBar.classList.add('hidden');
        }
    }
    if (typeof bottomSlidersWrapper !== 'undefined' && bottomSlidersWrapper) {
        if (isAnim) {
            bottomSlidersWrapper.classList.add('animation-mode');
        } else {
            bottomSlidersWrapper.classList.remove('animation-mode');
        }
    }
    document.body.classList.toggle('animation-mode', isAnim);
}

/**
 * Initializes an animation project with 1 default frame
 */
function initAnimationProject() {
    isAnimationMode = true;
    projectType = 'animation';
    animationFrames = [];
    currentFrameIndex = 0;

    // Ensure layers array has at least one layer
    if (!layers || layers.length === 0) {
        createFirstLayer();
    }

    // Add initial frame 0 with existing layers
    animationFrames.push({
        id: 'frame_' + Date.now(),
        name: 'Fotograma 1',
        layers: layers
    });

    updateAnimationUIState(true);

    setupAnimationEvents();
    updateFrameThumbnails();
}

/**
 * Binds DOM event listeners for animation UI controls and context menu
 */
function setupAnimationEvents() {
    if (animationEventsInitialized) return;
    animationEventsInitialized = true;

    if (addFrameBtn) {
        addFrameBtn.addEventListener('click', () => {
            addAnimationFrame(false);
        });
    }

    if (animPlayBtn) {
        animPlayBtn.addEventListener('click', () => {
            toggleAnimationPlayback();
        });
    }

    if (animFpsInput) {
        animFpsInput.addEventListener('change', (e) => {
            let val = parseInt(e.target.value, 10);
            if (isNaN(val) || val < 1) val = 1;
            if (val > 60) val = 60;
            animationFPS = val;
            animFpsInput.value = val;
            if (isAnimationPlaying) {
                stopAnimationPlayback();
                startAnimationPlayback();
            }
        });
    }

    if (animOnionInput) {
        animOnionInput.addEventListener('change', (e) => {
            let val = parseInt(e.target.value, 10);
            if (isNaN(val) || val < 0) val = 0;
            if (val > 100) val = 100;
            onionSkinOpacity = val / 100;
            animOnionInput.value = val;
            layersCacheDirty = true;
            requestRender();
        });
    }

    if (animClearOnionBtn) {
        animClearOnionBtn.addEventListener('click', () => {
            clearAllOnionSkinGuides();
        });
    }

    if (frameCtxOnion) {
        frameCtxOnion.addEventListener('click', () => {
            hideFrameContextMenu();
            if (contextMenuTargetIndex >= 0) toggleFrameOnionSkin(contextMenuTargetIndex);
        });
    }

    // Handlers para el menú contextual del fotograma
    const ctxDup = document.getElementById('frame-ctx-dup');
    const ctxDupEnd = document.getElementById('frame-ctx-dup-end');
    const ctxDupStart = document.getElementById('frame-ctx-dup-start');
    const ctxDel = document.getElementById('frame-ctx-del');

    if (ctxDup) ctxDup.addEventListener('click', () => { hideFrameContextMenu(); if (contextMenuTargetIndex >= 0) duplicateAnimationFrame(contextMenuTargetIndex, 'next'); });
    if (ctxDupEnd) ctxDupEnd.addEventListener('click', () => { hideFrameContextMenu(); if (contextMenuTargetIndex >= 0) duplicateAnimationFrame(contextMenuTargetIndex, 'end'); });
    if (ctxDupStart) ctxDupStart.addEventListener('click', () => { hideFrameContextMenu(); if (contextMenuTargetIndex >= 0) duplicateAnimationFrame(contextMenuTargetIndex, 'start'); });
    if (ctxDel) ctxDel.addEventListener('click', () => { hideFrameContextMenu(); if (contextMenuTargetIndex >= 0) deleteAnimationFrame(contextMenuTargetIndex); });

    window.addEventListener('pointerdown', (e) => {
        if (frameContextMenu && !frameContextMenu.contains(e.target)) {
            hideFrameContextMenu();
        }
    });
    window.addEventListener('keydown', (e) => {
        if (e.key === 'Escape') hideFrameContextMenu();
    });
}

/**
 * Switches to a specified frame index
 */
function switchAnimationFrame(targetIndex) {
    if (targetIndex < 0 || targetIndex >= animationFrames.length) return;

    if (isAnimationPlaying) {
        stopAnimationPlayback();
    }

    saveCurrentFrameState();
    currentFrameIndex = targetIndex;
    layers = animationFrames[currentFrameIndex].layers;

    if (typeof selectedLayerIndex !== 'undefined') {
        selectedLayerIndex = Math.max(0, Math.min(selectedLayerIndex, layers.length - 1));
    }

    if (typeof updateThumbnails === 'function') {
        updateThumbnails();
    }
    if (typeof updateLayersUI === 'function') {
        updateLayersUI();
    }

    layersCacheDirty = true;
    requestRender();
    updateFrameThumbnails();

    if (typeof pushHistory === 'function') {
        pushHistory();
    }
}

/**
 * Adds a new animation frame
 * @param {boolean} duplicateCurrent If true, duplicates layers from current frame
 */
function addAnimationFrame(duplicateCurrent = false) {
    saveCurrentFrameState();

    let newLayers = [];
    if (duplicateCurrent && animationFrames[currentFrameIndex]) {
        newLayers = animationFrames[currentFrameIndex].layers.map(cloneLayerStructure);
    } else {
        // Create 1 fresh default layer
        const lCanvas = document.createElement('canvas');
        lCanvas.width = paperWidth;
        lCanvas.height = paperHeight;
        const lCtx = lCanvas.getContext('2d');
        newLayers.push({
            id: Date.now() + Math.random(),
            name: 'Capa 1',
            canvas: lCanvas,
            ctx: lCtx,
            visible: true,
            opacity: 1,
            blendMode: 'source-over',
            clippingMask: false,
            alphaLocked: false
        });
    }

    const newFrame = {
        id: 'frame_' + Date.now() + '_' + Math.floor(Math.random()*1000),
        name: `Fotograma ${animationFrames.length + 1}`,
        layers: newLayers
    };

    animationFrames.splice(currentFrameIndex + 1, 0, newFrame);
    switchAnimationFrame(currentFrameIndex + 1);
}

/**
 * Duplicates a frame at specific index with position options ('next' | 'start' | 'end')
 */
function duplicateAnimationFrame(index, position = 'next') {
    saveCurrentFrameState();
    const sourceFrame = animationFrames[index];
    if (!sourceFrame) return;

    const clonedLayers = sourceFrame.layers.map(cloneLayerStructure);
    const newFrame = {
        id: 'frame_' + Date.now() + '_' + Math.floor(Math.random()*1000),
        name: `${sourceFrame.name} (copia)`,
        layers: clonedLayers
    };

    let targetIdx = index + 1;
    if (position === 'start') {
        targetIdx = 0;
        animationFrames.unshift(newFrame);
    } else if (position === 'end') {
        targetIdx = animationFrames.length;
        animationFrames.push(newFrame);
    } else {
        animationFrames.splice(index + 1, 0, newFrame);
    }

    switchAnimationFrame(targetIdx);
}

/**
 * Deletes a frame at specific index
 */
function deleteAnimationFrame(index) {
    if (animationFrames.length <= 1) {
        alert("El proyecto debe contener al menos 1 casilla de animación.");
        return;
    }

    saveCurrentFrameState();
    animationFrames.splice(index, 1);

    if (currentFrameIndex >= animationFrames.length) {
        currentFrameIndex = animationFrames.length - 1;
    }

    layers = animationFrames[currentFrameIndex].layers;
    if (typeof updateThumbnails === 'function') {
        updateThumbnails();
    }
    if (typeof updateLayersUI === 'function') {
        updateLayersUI();
    }

    layersCacheDirty = true;
    requestRender();
    updateFrameThumbnails();
}

/**
 * Toggles animation playback
 */
function toggleAnimationPlayback() {
    if (isAnimationPlaying) {
        stopAnimationPlayback();
    } else {
        startAnimationPlayback();
    }
}

/**
 * Starts playback loop
 */
function startAnimationPlayback() {
    if (isAnimationPlaying || animationFrames.length <= 1) return;

    saveCurrentFrameState();
    isAnimationPlaying = true;

    if (animPlayBtn) {
        animPlayBtn.classList.add('playing');
        animPlayBtn.innerHTML = '⏸';
        animPlayBtn.title = 'Pausar';
    }

    const intervalMs = Math.max(16, Math.round(1000 / animationFPS));
    animationInterval = setInterval(() => {
        currentFrameIndex = (currentFrameIndex + 1) % animationFrames.length;
        layers = animationFrames[currentFrameIndex].layers;
        layersCacheDirty = true;
        requestRender();

        // Highlight active frame thumbnail & update counter
        updateActiveFrameThumbnailUI();
    }, intervalMs);
}

/**
 * Stops playback loop
 */
function stopAnimationPlayback() {
    isAnimationPlaying = false;
    if (animationInterval) {
        clearInterval(animationInterval);
        animationInterval = null;
    }

    if (animPlayBtn) {
        animPlayBtn.classList.remove('playing');
        animPlayBtn.innerHTML = '▶';
        animPlayBtn.title = 'Reproducir';
    }

    if (typeof updateThumbnails === 'function') {
        updateThumbnails();
    }
    if (typeof updateLayersUI === 'function') {
        updateLayersUI();
    }
    updateActiveFrameThumbnailUI();
}

/**
 * Updates frame thumbnails strip UI
 */
function updateFrameThumbnails() {
    if (!animationFramesStrip) return;
    animationFramesStrip.innerHTML = '';

    animationFrames.forEach((frame, idx) => {
        const thumbDiv = document.createElement('div');
        const isOnionActive = onionSkinFrames.has(frame.id);
        thumbDiv.className = `frame-thumb-item ${idx === currentFrameIndex ? 'active-frame' : ''} ${isOnionActive ? 'onion-skin-active' : ''}`;
        thumbDiv.dataset.index = idx;
        thumbDiv.title = `Clic: Seleccionar | Doble clic: Alternar guía cebolla | Clic derecho: Opciones`;

        // Render preview canvas
        const previewCanvas = document.createElement('canvas');
        previewCanvas.className = 'frame-thumb-canvas';
        previewCanvas.width = 120;
        previewCanvas.height = Math.round(120 * (paperHeight / paperWidth));
        
        renderFrameCompositeToCanvas(frame, previewCanvas);

        const numSpan = document.createElement('span');
        numSpan.className = 'frame-thumb-number';
        numSpan.textContent = idx + 1;

        thumbDiv.appendChild(previewCanvas);
        thumbDiv.appendChild(numSpan);

        thumbDiv.addEventListener('click', () => {
            switchAnimationFrame(idx);
        });

        thumbDiv.addEventListener('dblclick', (e) => {
            e.stopPropagation();
            toggleFrameOnionSkin(idx);
        });

        thumbDiv.addEventListener('contextmenu', (e) => {
            showFrameContextMenu(e, idx);
        });

        animationFramesStrip.appendChild(thumbDiv);
    });

    if (animFrameCounter) {
        animFrameCounter.textContent = `${currentFrameIndex + 1} / ${animationFrames.length}`;
    }
}

/**
 * Quick update of only active frame thumbnail highlight and text counter
 */
function updateActiveFrameThumbnailUI() {
    if (!animationFramesStrip) return;

    const items = animationFramesStrip.querySelectorAll('.frame-thumb-item');
    items.forEach((item, idx) => {
        if (idx === currentFrameIndex) {
            item.classList.add('active-frame');
            item.scrollIntoView({ behavior: 'smooth', block: 'nearest', inline: 'nearest' });
        } else {
            item.classList.remove('active-frame');
        }
    });

    if (animFrameCounter) {
        animFrameCounter.textContent = `${currentFrameIndex + 1} / ${animationFrames.length}`;
    }
}

/**
 * Renders composite of frame layers into a preview thumbnail canvas
 */
function renderFrameCompositeToCanvas(frame, destCanvas, clearFirst = true) {
    const dctx = destCanvas.getContext('2d');
    if (clearFirst) {
        dctx.clearRect(0, 0, destCanvas.width, destCanvas.height);
    }

    if (!frame || !frame.layers) return;

    // Render layers from bottom to top
    for (let i = 0; i < frame.layers.length; i++) {
        const l = frame.layers[i];
        if (!l.visible || !l.canvas) continue;
        dctx.save();
        dctx.globalAlpha = l.opacity;
        dctx.globalCompositeOperation = l.blendMode || 'source-over';
        dctx.drawImage(l.canvas, 0, 0, destCanvas.width, destCanvas.height);
        dctx.restore();
    }
}

/**
 * Updates current frame thumbnail canvas live after drawing stroke
 */
function updateCurrentFrameThumbnail() {
    if (!isAnimationMode || !animationFramesStrip) return;
    const activeItem = animationFramesStrip.querySelector(`.frame-thumb-item[data-index="${currentFrameIndex}"]`);
    if (!activeItem) return;

    const thumbCanvas = activeItem.querySelector('.frame-thumb-canvas');
    if (thumbCanvas && animationFrames[currentFrameIndex]) {
        // Update frame layers reference to current global layers
        animationFrames[currentFrameIndex].layers = layers;
        renderFrameCompositeToCanvas(animationFrames[currentFrameIndex], thumbCanvas);
    }
}

/**
 * Toggles a frame as onion skin guide
 */
function toggleFrameOnionSkin(index) {
    const frame = animationFrames[index];
    if (!frame) return;
    if (onionSkinFrames.has(frame.id)) {
        onionSkinFrames.delete(frame.id);
    } else {
        onionSkinFrames.add(frame.id);
    }
    updateFrameThumbnails();
    layersCacheDirty = true;
    requestRender();
}

/**
 * Clears all active onion skin guides
 */
function clearAllOnionSkinGuides() {
    onionSkinFrames.clear();
    updateFrameThumbnails();
    layersCacheDirty = true;
    requestRender();
}

const onionSkinBufferCanvas = document.createElement('canvas');

/**
 * Renders onion skin guides onto the target canvas
 */
function renderOnionSkinOverlay(targetCtx) {
    if (!isAnimationMode || !onionSkinFrames || onionSkinFrames.size === 0) return;

    if (onionSkinBufferCanvas.width !== paperWidth || onionSkinBufferCanvas.height !== paperHeight) {
        onionSkinBufferCanvas.width = paperWidth;
        onionSkinBufferCanvas.height = paperHeight;
    }

    const obctx = onionSkinBufferCanvas.getContext('2d');
    obctx.clearRect(0, 0, paperWidth, paperHeight);

    let hasGuideContent = false;

    animationFrames.forEach((frame, idx) => {
        // Regla de optimización: Omitir el fotograma que se está editando actualmente
        if (idx === currentFrameIndex) return;

        if (onionSkinFrames.has(frame.id)) {
            renderFrameCompositeToCanvas(frame, onionSkinBufferCanvas, false);
            hasGuideContent = true;
        }
    });

    if (hasGuideContent) {
        // Estampar la unión de todas las guías cebolla en 1 solo pase de transparencia
        targetCtx.save();
        targetCtx.globalAlpha = onionSkinOpacity;
        targetCtx.globalCompositeOperation = 'source-over';
        targetCtx.drawImage(onionSkinBufferCanvas, 0, 0);
        targetCtx.restore();
    }
}

/**
 * Updates the label and tooltip of the project type toggle button in Preferences menu
 */
function updateProjectTypeButtonLabel() {
    const label = document.getElementById('toggle-project-type-label');
    const btn = document.getElementById('btn-toggle-project-type');
    if (!label) return;
    if (typeof isAnimationMode !== 'undefined' && isAnimationMode) {
        label.textContent = 'A Ilustración';
        if (btn) btn.title = 'Convertir proyecto a Ilustración (solo se conserva el fotograma actual)';
    } else {
        label.textContent = 'A Animación';
        if (btn) btn.title = 'Convertir proyecto a Animación';
    }
}

/**
 * Toggles the current project between Illustration and Animation mode
 */
function toggleProjectType() {
    if (typeof isAnimationMode !== 'undefined' && isAnimationMode) {
        // Confirm migration from Animation to Illustration
        const ok = confirm('¿Deseas convertir este proyecto a Ilustración?\n\nSolo se conservará el fotograma actual. Todos los demás fotogramas serán eliminados permanentemente.');
        if (!ok) return;

        if (typeof saveCurrentFrameState === 'function') {
            saveCurrentFrameState();
        }

        // Keep active frame's layers as main layers
        if (typeof animationFrames !== 'undefined' && animationFrames[currentFrameIndex]) {
            layers = animationFrames[currentFrameIndex].layers;
        }

        isAnimationMode = false;
        projectType = 'illustration';
        animationFrames = [];

        updateAnimationUIState(false);
        if (typeof updateLayersUI === 'function') updateLayersUI();
    } else {
        // Migrate from Illustration to Animation
        isAnimationMode = true;
        projectType = 'animation';

        if (!layers || layers.length === 0) {
            if (typeof createFirstLayer === 'function') createFirstLayer();
        }

        animationFrames = [{
            id: 'frame_' + Date.now(),
            name: 'Fotograma 1',
            layers: layers
        }];
        currentFrameIndex = 0;

        updateAnimationUIState(true);
        if (typeof setupAnimationEvents === 'function') setupAnimationEvents();
        if (typeof updateFrameThumbnails === 'function') updateFrameThumbnails();
        if (typeof updateLayersUI === 'function') updateLayersUI();
    }

    updateProjectTypeButtonLabel();
    if (typeof saveCurrentProject === 'function') saveCurrentProject();
    if (typeof pushHistory === 'function') pushHistory();
    if (typeof requestRender === 'function') requestRender();
}
