// ─────────────────────────────────────────────────────────────
//  INDEXED DB & GALLERY SAVE SYSTEM
// ─────────────────────────────────────────────────────────────
const DB_NAME = 'IllustratorProDB'; const DB_VERSION = 1;
const getDB = () => new Promise((res, rej) => {
    const req = indexedDB.open(DB_NAME, DB_VERSION);
    req.onupgradeneeded = () => req.result.createObjectStore('slots');
    req.onsuccess = () => res(req.result); req.onerror = () => rej(req.error);
});

let gallerySelectedProjectId = null;
let galleryMode = 'grid'; // 'grid' | 'detail'
let draggedProjectId = null;
let dragLastX = 0;
let dragLastY = 0;
let lastSwappedTarget = null;
let lastSwapTime = 0;
const SAME_TARGET_COOLDOWN = 100; // ms — short cooldown ONLY when hovering over the exact same target repeatedly

function formatTime(seconds) {
    const h = Math.floor(seconds / 3600);
    const m = Math.floor((seconds % 3600) / 60);
    const s = seconds % 60;
    return `${h.toString().padStart(2, '0')}:${m.toString().padStart(2, '0')}:${s.toString().padStart(2, '0')}`;
}

/**
 * FLIP (First, Last, Invert, Play) animation helper to smoothly swap nodes in the grid
 * Supports simultaneous animations for fast continuous dragging.
 */
function flipReorder(parent, draggedEl, targetEl) {
    const children = Array.from(parent.children);
    // 1. Get initial screen visual positions (First)
    const rects = children.map(child => ({
        el: child,
        rect: child.getBoundingClientRect()
    }));

    // 2. Perform DOM reorder
    const sourceIdx = children.indexOf(draggedEl);
    const targetIdx = children.indexOf(targetEl);
    if (sourceIdx < targetIdx) {
        parent.insertBefore(draggedEl, targetEl.nextSibling);
    } else {
        parent.insertBefore(draggedEl, targetEl);
    }

    // 3. Measure final positions and animate transitions (Last, Invert, Play)
    const newChildren = Array.from(parent.children);
    newChildren.forEach(child => {
        if (child === draggedEl) return;

        const old = rects.find(r => r.el === child);
        if (!old) return;

        // Temporarily clear transform/transition to read true untransformed target layout rect
        const prevTransform = child.style.transform;
        const prevTransition = child.style.transition;
        child.style.transition = 'none';
        child.style.transform = 'none';

        const newRect = child.getBoundingClientRect();
        const dx = old.rect.left - newRect.left;
        const dy = old.rect.top - newRect.top;

        if (Math.abs(dx) > 0.5 || Math.abs(dy) > 0.5) {
            // Apply invert offset immediately from current visual location
            child.style.transform = `translate(${dx}px, ${dy}px)`;
            child.offsetHeight; // Force reflow

            // Smooth fast animation to target (0,0)
            child.style.transition = 'transform 0.18s cubic-bezier(0.2, 0, 0.2, 1)';
            child.style.transform = 'translate(0, 0)';

            const onTransitionEnd = (e) => {
                if (e && e.propertyName !== 'transform') return;
                child.style.transition = '';
                child.style.transform = '';
                child.removeEventListener('transitionend', onTransitionEnd);
            };
            child.addEventListener('transitionend', onTransitionEnd);
        } else {
            child.style.transform = prevTransform;
            child.style.transition = prevTransition;
        }
    });
}

async function saveCurrentProject() {
    if (!currentProjectId) {
        currentProjectId = 'proj_' + Date.now();
    }
    const db = await getDB();

    // If this is a new project, assign it a new order weight placing it at the top
    if (currentProjectOrder === undefined || currentProjectOrder === null || currentProjectOrder === 0) {
        const txCheck = db.transaction('slots', 'readonly');
        const existing = await new Promise(res => txCheck.objectStore('slots').get(currentProjectId).onsuccess = e => res(e.target.result));
        if (existing && existing.order !== undefined) {
            currentProjectOrder = existing.order;
        } else {
            // Find the lowest order weight among existing projects to put the new one at the very top (lowest order weight = first in ascending sort)
            const txList = db.transaction('slots', 'readonly');
            const storeList = txList.objectStore('slots');
            const projects = [];
            await new Promise((resolve) => {
                storeList.openCursor().onsuccess = (event) => {
                    const cursor = event.target.result;
                    if (cursor) {
                        projects.push(cursor.value);
                        cursor.continue();
                    } else {
                        resolve();
                    }
                };
            });
            const orders = projects.map(p => p.order !== undefined ? p.order : 0);
            const minOrder = orders.length > 0 ? Math.min(...orders) : 0;
            currentProjectOrder = minOrder - 1;
        }
    }

    // Generate thumbnail preserving the real aspect ratio of the canvas
    const MAX_DIM = 800;
    const flat = getFlatImage();
    const ratio = flat.height / flat.width;
    let thumbW, thumbH;
    if (flat.width >= flat.height) {
        thumbW = Math.min(MAX_DIM, flat.width);
        thumbH = Math.round(thumbW * ratio);
    } else {
        thumbH = Math.min(MAX_DIM, flat.height);
        thumbW = Math.round(thumbH / ratio);
    }

    const thumbCanvas = document.createElement('canvas');
    thumbCanvas.width = thumbW;
    thumbCanvas.height = thumbH;
    const tctx = thumbCanvas.getContext('2d');

    // Simulate background to prevent transparent areas from turning black in JPEG thumbnail
    if (bgMode === 1) {
        tctx.fillStyle = solidBgColor;
        tctx.fillRect(0, 0, thumbW, thumbH);
    } else if (bgMode === 2) {
        const pat = tctx.createPattern(checkerPatternDarkCanvas, 'repeat');
        tctx.fillStyle = pat;
        tctx.fillRect(0, 0, thumbW, thumbH);
    } else {
        const pat = tctx.createPattern(checkerPatternLightCanvas, 'repeat');
        tctx.fillStyle = pat;
        tctx.fillRect(0, 0, thumbW, thumbH);
    }

    tctx.drawImage(flat, 0, 0, thumbW, thumbH);

    const thumbDataURL = thumbCanvas.toDataURL('image/webp', 0.90);

    if (typeof saveCurrentFrameState === 'function') {
        saveCurrentFrameState();
    }

    const project = {
        id: currentProjectId,
        title: currentProjectTitle,
        time: currentProjectTime,
        order: currentProjectOrder,
        w: paperWidth, h: paperHeight,
        thumb: thumbDataURL,
        savedAt: Date.now(),
        bgMode: bgMode,
        solidBgColor: solidBgColor,
        projectType: projectType || 'illustration',
        isAnimationMode: !!isAnimationMode,
        currentFrameIndex: currentFrameIndex || 0,
        animationFPS: animationFPS || 12,
        animationFrames: isAnimationMode ? animationFrames.map(f => ({
            id: f.id,
            name: f.name,
            layers: f.layers.map(l => ({
                name: l.name,
                opacity: l.opacity,
                visible: l.visible,
                blend: l.blendMode,
                clipping: l.clippingMask,
                alphaLocked: l.alphaLocked,
                data: l.canvas.toDataURL('image/webp', 0.95)
            }))
        })) : null,
        layers: layers.map(l => ({
            name: l.name,
            opacity: l.opacity,
            visible: l.visible,
            blend: l.blendMode,
            clipping: l.clippingMask,
            alphaLocked: l.alphaLocked,
            data: l.canvas.toDataURL('image/webp', 0.95)
        }))
    };

    const tx = db.transaction('slots', 'readwrite');
    tx.objectStore('slots').put(project, currentProjectId);
    return new Promise(res => tx.oncomplete = () => {
        res();
    });
}

async function loadProject(id) {
    const db = await getDB();
    const tx = db.transaction('slots', 'readonly');
    const project = await new Promise(res => tx.objectStore('slots').get(id).onsuccess = e => res(e.target.result));
    if (!project) { alert("Proyecto no encontrado."); return; }

    currentProjectId = project.id || id;
    currentProjectTitle = project.title || "Sin título";
    currentProjectTime = project.time || 0;
    currentProjectOrder = project.order !== undefined ? project.order : 0;

    // Restaurar configuración de fondo (retrocompatible: proyectos viejos usan modo 1 blanco)
    bgMode = project.bgMode !== undefined ? project.bgMode : 1;
    solidBgColor = project.solidBgColor || '#ffffff';

    paperWidth = project.w; paperHeight = project.h;
    setupLogicalCanvas();

    projectType = project.projectType || 'illustration';
    isAnimationMode = !!project.isAnimationMode;
    animationFPS = project.animationFPS || 12;
    currentFrameIndex = project.currentFrameIndex || 0;

    if (isAnimationMode && project.animationFrames && project.animationFrames.length > 0) {
        animationFrames = [];
        for (const fData of project.animationFrames) {
            const fLayers = [];
            for (const lData of fData.layers) {
                const lCanvas = document.createElement('canvas'); lCanvas.width = paperWidth; lCanvas.height = paperHeight;
                const lCtx = lCanvas.getContext('2d');
                const img = await new Promise(res => { const i = new Image(); i.onload = () => res(i); i.src = lData.data; });
                lCtx.drawImage(img, 0, 0);
                fLayers.push({
                    id: Date.now() + Math.random(),
                    name: lData.name,
                    canvas: lCanvas,
                    ctx: lCtx,
                    visible: lData.visible,
                    opacity: lData.opacity,
                    blendMode: lData.blend || 'source-over',
                    clippingMask: !!lData.clipping,
                    alphaLocked: !!lData.alphaLocked
                });
            }
            animationFrames.push({
                id: fData.id,
                name: fData.name,
                layers: fLayers
            });
        }
        if (currentFrameIndex >= animationFrames.length) currentFrameIndex = 0;
        layers = animationFrames[currentFrameIndex].layers;

        if (typeof updateAnimationUIState === 'function') {
            updateAnimationUIState(true);
        } else if (typeof animationBottomBar !== 'undefined' && animationBottomBar) {
            animationBottomBar.classList.remove('hidden');
        }
        if (typeof animFpsInput !== 'undefined' && animFpsInput) {
            animFpsInput.value = animationFPS;
        }
        if (typeof setupAnimationEvents === 'function') {
            setupAnimationEvents();
        }
        if (typeof updateFrameThumbnails === 'function') {
            updateFrameThumbnails();
        }
    } else {
        isAnimationMode = false;
        if (typeof updateAnimationUIState === 'function') {
            updateAnimationUIState(false);
        } else if (typeof animationBottomBar !== 'undefined' && animationBottomBar) {
            animationBottomBar.classList.add('hidden');
        }
        layers = [];
        for (const lData of project.layers) {
            const lCanvas = document.createElement('canvas'); lCanvas.width = paperWidth; lCanvas.height = paperHeight;
            const lCtx = lCanvas.getContext('2d');
            const img = await new Promise(res => { const i = new Image(); i.onload = () => res(i); i.src = lData.data; });
            lCtx.drawImage(img, 0, 0);
            layers.push({
                id: Date.now() + Math.random(),
                name: lData.name,
                canvas: lCanvas,
                ctx: lCtx,
                visible: lData.visible,
                opacity: lData.opacity,
                blendMode: lData.blend || 'source-over',
                clippingMask: !!lData.clipping,
                alphaLocked: !!lData.alphaLocked,
                thumbData: ''
            });
        }
    }

    selectedLayerIndex = layers.length - 1;

    // Reset history for fresh project load
    historyStack = []; historyIndex = -1;
    updateThumbnails(); updateLayersUI();
    updateBgUI(); // sincronizar ícono del botón de fondo
    pushHistory(); // seed history with loaded state

    // Hide gallery, show editor
    document.getElementById('gallery-screen').classList.add('hidden');
    mainApp.classList.remove('blur-content');
    mainApp.style.pointerEvents = 'auto';

    startProjectTimer();
    toggleMenu(null);
}

async function deleteProject(id) {
    if (!confirm('¿Estás seguro de que deseas eliminar esta obra? Esta acción no se puede deshacer.')) return;
    const db = await getDB();
    const tx = db.transaction('slots', 'readwrite');
    tx.objectStore('slots').delete(id);
    await new Promise(res => tx.oncomplete = res);

    gallerySelectedProjectId = null;
    galleryMode = 'grid';
    renderGallery();
}

async function renameProject(id) {
    const db = await getDB();
    const tx = db.transaction('slots', 'readonly');
    const project = await new Promise(res => tx.objectStore('slots').get(id).onsuccess = e => res(e.target.result));
    if (!project) return;

    const newTitle = prompt('Nuevo título para la obra:', project.title || 'Sin título');
    if (newTitle === null) return; // cancelled

    project.title = newTitle.trim() || 'Sin título';

    const tx2 = db.transaction('slots', 'readwrite');
    tx2.objectStore('slots').put(project, id);
    await new Promise(res => tx2.oncomplete = res);

    if (id === currentProjectId) {
        currentProjectTitle = project.title;
    }

    renderGallery();
}

async function renderGallery() {
    const db = await getDB();
    const tx = db.transaction('slots', 'readonly');
    const store = tx.objectStore('slots');

    // Fetch all records
    const projects = [];
    await new Promise((resolve) => {
        store.openCursor().onsuccess = (event) => {
            const cursor = event.target.result;
            if (cursor) {
                projects.push(cursor.value);
                cursor.continue();
            } else {
                resolve();
            }
        };
    });

    // Sort projects by order ascending
    projects.sort((a, b) => (a.order || 0) - (b.order || 0));

    // Update Title with Count
    const titleEl = document.getElementById('gallery-title');
    if (titleEl) {
        titleEl.textContent = `MI GALERÍA (${projects.length})`;
    }

    const gridEl = document.getElementById('gallery-grid');
    const detailEl = document.getElementById('gallery-detail');
    const backBtn = document.getElementById('gallery-back-btn');
    const editBtn = document.getElementById('gallery-edit-btn');

    // Grid mode
    if (galleryMode === 'grid') {
        gridEl.classList.remove('hidden');
        detailEl.classList.add('hidden');
        backBtn.classList.add('hidden');
        editBtn.disabled = !gallerySelectedProjectId;

        gridEl.innerHTML = '';
        if (projects.length === 0) {
            gridEl.innerHTML = '<div style="grid-column: 1/-1; text-align: center; padding: 40px; color: #888; font-size: 14px;">No tienes obras guardadas.<br>¡Haz clic en "+" para crear una!</div>';
        }

        projects.forEach(p => {
            const item = document.createElement('div');
            item.className = 'gallery-item';
            item.dataset.id = p.id;
            if (p.id === gallerySelectedProjectId) {
                item.classList.add('selected');
            }

            // HTML5 Drag and Drop bindings
            item.setAttribute('draggable', 'true');
            item.addEventListener('dragstart', (e) => {
                draggedProjectId = p.id;
                item.classList.add('dragging');
                e.dataTransfer.setData('text/plain', p.id);
                e.dataTransfer.effectAllowed = 'move';
                dragLastX = e.clientX;
                dragLastY = e.clientY;
                lastSwappedTarget = null;
                lastSwapTime = 0;
            });
            item.addEventListener('dragend', async () => {
                item.classList.remove('dragging');

                // Save final DOM order directly to the database
                const children = Array.from(gridEl.children);
                const orderIds = children.map(child => child.dataset.id);

                const db2 = await getDB();
                const tx2 = db2.transaction('slots', 'readwrite');
                const store2 = tx2.objectStore('slots');

                orderIds.forEach((id, idx) => {
                    const proj = projects.find(x => x.id === id);
                    if (proj) {
                        proj.order = idx;
                        store2.put(proj, id);
                    }
                });
                await new Promise(r => tx2.oncomplete = r);
                document.querySelectorAll('.gallery-item').forEach(el => el.classList.remove('drag-over'));
            });
            item.addEventListener('dragover', (e) => {
                e.preventDefault();
                e.dataTransfer.dropEffect = 'move';

                const draggedEl = gridEl.querySelector('.dragging');
                if (!draggedEl || draggedEl === item) return;

                const now = Date.now();
                // Short cooldown ONLY if continuously hovering the exact same target item that was just swapped
                if (lastSwappedTarget === item && (now - lastSwapTime < SAME_TARGET_COOLDOWN)) {
                    return;
                }

                const rect = item.getBoundingClientRect();
                const midX = rect.left + rect.width / 2;
                const midY = rect.top + rect.height / 2;

                const children = Array.from(gridEl.children);
                const targetIdx = children.indexOf(item);
                const draggedIdx = children.indexOf(draggedEl);

                let shouldSwap = false;
                const isSameRow = (e.clientY >= rect.top && e.clientY <= rect.bottom);

                if (draggedIdx < targetIdx) {
                    if (e.clientY > rect.bottom) {
                        shouldSwap = true;
                    } else if (isSameRow) {
                        shouldSwap = e.clientX > midX;
                    } else if (e.clientY > midY) {
                        shouldSwap = true;
                    }
                } else {
                    if (e.clientY < rect.top) {
                        shouldSwap = true;
                    } else if (isSameRow) {
                        shouldSwap = e.clientX < midX;
                    } else if (e.clientY < midY) {
                        shouldSwap = true;
                    }
                }

                if (shouldSwap) {
                    lastSwappedTarget = item;
                    lastSwapTime = now;
                    dragLastX = e.clientX;
                    dragLastY = e.clientY;
                    flipReorder(gridEl, draggedEl, item);
                }
            });
            item.addEventListener('dragleave', () => {
                item.classList.remove('drag-over');
            });
            item.addEventListener('drop', (e) => {
                e.preventDefault();
            });

            const thumbContainer = document.createElement('div');
            thumbContainer.className = 'gallery-thumb-container';

            if (p.thumb) {
                const img = document.createElement('img');
                img.className = 'gallery-thumb-img';
                img.src = p.thumb;
                thumbContainer.appendChild(img);
            } else {
                thumbContainer.innerHTML = '<span style="color:#aaa; font-size:10px;">Sin vista previa</span>';
            }

            const isAnim = !!(p.isAnimationMode || p.projectType === 'animation' || (p.animationFrames && p.animationFrames.length > 0));
            if (isAnim) {
                const badge = document.createElement('div');
                badge.className = 'gallery-anim-badge';
                badge.title = 'Proyecto de Animación';
                badge.textContent = '🎞️';
                thumbContainer.appendChild(badge);
            }

            const label = document.createElement('span');
            label.className = 'gallery-item-label';
            label.textContent = p.title || 'Sin título';

            item.appendChild(thumbContainer);
            item.appendChild(label);

            item.onclick = () => {
                if (item.classList.contains('dragging')) return;
                gallerySelectedProjectId = p.id;
                galleryMode = 'detail';
                renderGallery();
            };

            gridEl.appendChild(item);
        });
    } else if (galleryMode === 'detail' && gallerySelectedProjectId) {
        const project = projects.find(p => p.id === gallerySelectedProjectId);
        if (!project) {
            galleryMode = 'grid';
            gallerySelectedProjectId = null;
            renderGallery();
            return;
        }

        gridEl.classList.add('hidden');
        detailEl.classList.remove('hidden');
        backBtn.classList.remove('hidden');
        editBtn.disabled = false;

        document.getElementById('detail-img').src = project.thumb || '';
        document.getElementById('detail-title').textContent = project.title || 'Sin título';
        document.getElementById('detail-layers-count').textContent = project.layers ? project.layers.length : 0;

        const w = project.w || 1920;
        const h = project.h || 1080;
        document.getElementById('detail-size').textContent = `${w} x ${h}`;
        document.getElementById('detail-time').textContent = formatTime(project.time || 0);
    }
}

async function duplicateProject(id) {
    const db = await getDB();
    const tx = db.transaction('slots', 'readonly');
    const project = await new Promise(res => tx.objectStore('slots').get(id).onsuccess = e => res(e.target.result));
    if (!project) return;

    const newId = 'proj_' + Date.now();
    const duplicate = Object.assign({}, project, {
        id: newId,
        title: (project.title || 'Sin título') + ' (copia)',
        order: (project.order || 0) - 0.5,
        savedAt: Date.now()
    });

    const tx2 = db.transaction('slots', 'readwrite');
    tx2.objectStore('slots').put(duplicate, newId);
    await new Promise(res => tx2.oncomplete = res);

    renderGallery();
}

/**
 * Clones the LAST SAVED state (Version A) from IndexedDB into a new gallery entry ("versión anterior"),
 * and immediately saves the CURRENT active session (Version B) to disk.
 */
async function saveProjectDuplicateFromMenu() {
    if (!currentProjectId) return;

    const db = await getDB();
    const tx = db.transaction('slots', 'readonly');
    const lastSavedProject = await new Promise(res => tx.objectStore('slots').get(currentProjectId).onsuccess = e => res(e.target.result));

    if (lastSavedProject) {
        // Clone the previous saved state from DB
        const backupId = 'proj_' + Date.now();
        const backupProject = Object.assign({}, lastSavedProject, {
            id: backupId,
            title: (lastSavedProject.title || 'Sin título') + ' (versión anterior)',
            order: (lastSavedProject.order !== undefined ? lastSavedProject.order : 0) + 0.1,
            savedAt: Date.now()
        });

        const tx2 = db.transaction('slots', 'readwrite');
        tx2.objectStore('slots').put(backupProject, backupId);
        await new Promise(res => tx2.oncomplete = res);

        // Save current active session state immediately
        await saveCurrentProject();

        alert(`¡Guardado completo!\n\n• Versión anterior respaldada en la galería como: "${backupProject.title}"\n• Proyecto actual guardado.`);
    } else {
        // If current project was never saved to DB before, save active state
        await saveCurrentProject();

        const txNew = db.transaction('slots', 'readonly');
        const project = await new Promise(res => txNew.objectStore('slots').get(currentProjectId).onsuccess = e => res(e.target.result));
        if (project) {
            const backupId = 'proj_' + Date.now();
            const backupProject = Object.assign({}, project, {
                id: backupId,
                title: (project.title || 'Sin título') + ' (copia inicial)',
                order: (project.order !== undefined ? project.order : 0) + 0.1,
                savedAt: Date.now()
            });

            const txWrite = db.transaction('slots', 'readwrite');
            txWrite.objectStore('slots').put(backupProject, backupId);
            await new Promise(res => txWrite.oncomplete = res);

            alert(`Proyecto actual guardado y copia inicial respaldada en la galería como: "${backupProject.title}".`);
        }
    }
}

// ─── Gallery Context Menu ────────────────────────────────────
(function initGalleryContextMenu() {
    const menu = document.createElement('div');
    menu.id = 'gallery-context-menu';
    menu.style.display = 'none';
    menu.innerHTML = `
        <div class="gallery-ctx-item" id="gctx-edit">
            <span class="gallery-ctx-icon">🎨</span> Editar
        </div>
        <div class="gallery-ctx-separator"></div>
        <div class="gallery-ctx-item" id="gctx-rename">
            <span class="gallery-ctx-icon">✏️</span> Renombrar
        </div>
        <div class="gallery-ctx-item" id="gctx-duplicate">
            <span class="gallery-ctx-icon">📋</span> Duplicar
        </div>
        <div class="gallery-ctx-separator"></div>
        <div class="gallery-ctx-item" id="gctx-copy">
            <span class="gallery-ctx-icon">🖼️</span> Copiar imagen
        </div>
        <div class="gallery-ctx-item" id="gctx-download">
            <span class="gallery-ctx-icon">⬇️</span> Descargar PNG
        </div>
        <div class="gallery-ctx-separator"></div>
        <div class="gallery-ctx-item danger" id="gctx-delete">
            <span class="gallery-ctx-icon">🗑️</span> Eliminar
        </div>
    `;
    document.body.appendChild(menu);

    let targetId = null;

    function showMenu(x, y, id) {
        targetId = id;
        menu.style.display = 'block';
        const mw = 180, mh = 270;
        const left = x + mw > window.innerWidth  ? x - mw : x;
        const top  = y + mh > window.innerHeight ? y - mh : y;
        menu.style.left = left + 'px';
        menu.style.top  = top  + 'px';
        // Re-trigger animation
        menu.style.animation = 'none';
        menu.offsetHeight;
        menu.style.animation = '';
    }

    function hideMenu() {
        menu.style.display = 'none';
        targetId = null;
    }

    /**
     * Reconstruye la imagen completa a resolución nativa cargando todas las capas
     * desde IndexedDB y composicionándolas, igual que getFlatImage() en el editor.
     * Devuelve { canvas, title } o null si no se encuentra el proyecto.
     */
    async function renderProjectFullRes(id) {
        const db = await getDB();
        const tx = db.transaction('slots', 'readonly');
        const project = await new Promise(res => tx.objectStore('slots').get(id).onsuccess = e => res(e.target.result));
        if (!project) return null;

        const w = project.w || 1920;
        const h = project.h || 1080;

        // Cargar todas las capas como imágenes de forma asíncrona
        const layerImages = await Promise.all((project.layers || []).map(lData =>
            new Promise(res => {
                const img = new Image();
                img.onload = () => res({ img, lData });
                img.onerror = () => res(null);
                img.src = lData.data;
            })
        ));

        // Crear canvas de salida a resolución completa
        const flat = document.createElement('canvas');
        flat.width = w;
        flat.height = h;
        const fctx = flat.getContext('2d');

        // Pintar fondo sólido si está configurado en el proyecto (por defecto modo 1, color blanco)
        const projBgMode = project.bgMode !== undefined ? project.bgMode : 1;
        const projSolidColor = project.solidBgColor || '#ffffff';
        if (projBgMode === 1) {
            fctx.fillStyle = projSolidColor;
            fctx.fillRect(0, 0, w, h);
        }

        // Composicionar capas en orden (índice 0 = fondo)
        for (const entry of layerImages) {
            if (!entry) continue;
            const { img, lData } = entry;
            if (lData.visible === false) continue;
            fctx.save();
            fctx.globalAlpha = (lData.opacity !== undefined) ? lData.opacity : 1.0;
            fctx.globalCompositeOperation = lData.blend || 'source-over';
            fctx.drawImage(img, 0, 0, w, h);
            fctx.restore();
        }

        return { canvas: flat, title: project.title || 'proyecto' };
    }

    // ── Editar ──────────────────────────────────────────────────
    document.getElementById('gctx-edit').addEventListener('click', () => {
        const id = targetId; hideMenu();
        if (id) loadProject(id);
    });

    // ── Renombrar ───────────────────────────────────────────────
    document.getElementById('gctx-rename').addEventListener('click', () => {
        const id = targetId; hideMenu();
        if (id) renameProject(id);
    });

    // ── Duplicar ────────────────────────────────────────────────
    document.getElementById('gctx-duplicate').addEventListener('click', () => {
        const id = targetId; hideMenu();
        if (id) duplicateProject(id);
    });

    // ── Copiar imagen al portapapeles ────────────────────────────
    document.getElementById('gctx-copy').addEventListener('click', async () => {
        const id = targetId; hideMenu();
        if (!id) return;
        const btn = document.getElementById('gctx-copy');
        if (btn) btn.textContent = '⏳ Procesando…';
        const data = await renderProjectFullRes(id);
        if (!data) { if (btn) btn.innerHTML = '<span class="gallery-ctx-icon">🖼️</span> Copiar imagen'; alert('No se pudo cargar el proyecto.'); return; }
        try {
            const pngBlob = await new Promise(res => data.canvas.toBlob(res, 'image/png'));
            await navigator.clipboard.write([
                new ClipboardItem({ 'image/png': pngBlob })
            ]);
            if (btn) { btn.textContent = '✅ Copiado'; setTimeout(() => { btn.innerHTML = '<span class="gallery-ctx-icon">🖼️</span> Copiar imagen'; }, 1800); }
        } catch (err) {
            console.warn('No se pudo copiar:', err);
            if (btn) btn.innerHTML = '<span class="gallery-ctx-icon">🖼️</span> Copiar imagen';
            alert('No se pudo copiar la imagen. El navegador puede requerir permisos.');
        }
    });

    // ── Descargar PNG ────────────────────────────────────────────
    document.getElementById('gctx-download').addEventListener('click', async () => {
        const id = targetId; hideMenu();
        if (!id) return;
        const data = await renderProjectFullRes(id);
        if (!data) { alert('No se pudo cargar el proyecto.'); return; }
        const a = document.createElement('a');
        a.href = data.canvas.toDataURL('image/png');
        a.download = (data.title.replace(/[<>:"/\\|?*]/g, '_') || 'proyecto') + '.png';
        a.click();
    });

    // ── Eliminar ─────────────────────────────────────────────────
    document.getElementById('gctx-delete').addEventListener('click', () => {
        const id = targetId; hideMenu();
        if (id) deleteProject(id);
    });

    // Close on outside click or Escape
    document.addEventListener('pointerdown', (e) => {
        if (menu.style.display !== 'none' && !menu.contains(e.target)) hideMenu();
    }, true);
    document.addEventListener('keydown', (e) => {
        if (e.key === 'Escape') hideMenu();
    });

    // Listen for right-click on gallery grid items
    document.getElementById('gallery-grid').addEventListener('contextmenu', (e) => {
        const item = e.target.closest('.gallery-item');
        if (!item) return;
        e.preventDefault();
        showMenu(e.clientX, e.clientY, item.dataset.id);
    });
})();

