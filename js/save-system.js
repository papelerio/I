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
let lastTargetId = null;

function formatTime(seconds) {
    const h = Math.floor(seconds / 3600);
    const m = Math.floor((seconds % 3600) / 60);
    const s = seconds % 60;
    return `${h.toString().padStart(2, '0')}:${m.toString().padStart(2, '0')}:${s.toString().padStart(2, '0')}`;
}

/**
 * FLIP (First, Last, Invert, Play) animation helper to smoothly swap nodes in the grid
 */
function flipReorder(parent, draggedEl, targetEl) {
    const children = Array.from(parent.children);
    // 1. Get initial screen positions (First)
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
        const old = rects.find(r => r.el === child);
        if (!old) return;
        const newRect = child.getBoundingClientRect();
        const dx = old.rect.left - newRect.left;
        const dy = old.rect.top - newRect.top;

        if (dx || dy) {
            child.style.transition = 'none';
            child.style.transform = `translate(${dx}px, ${dy}px)`;
            child.offsetHeight; // Force reflow
            child.style.transition = 'transform 0.25s cubic-bezier(0.25, 0.8, 0.25, 1)';
            child.style.transform = 'translate(0, 0)';

            // Reset transition styles once finished
            const onTransitionEnd = () => {
                child.style.transition = '';
                child.style.transform = '';
                child.removeEventListener('transitionend', onTransitionEnd);
            };
            child.addEventListener('transitionend', onTransitionEnd);
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
    tctx.drawImage(flat, 0, 0, thumbW, thumbH);

    const thumbDataURL = thumbCanvas.toDataURL('image/jpeg', 0.92);

    const project = {
        id: currentProjectId,
        title: currentProjectTitle,
        time: currentProjectTime,
        order: currentProjectOrder,
        w: paperWidth, h: paperHeight,
        thumb: thumbDataURL,
        savedAt: Date.now(),
        layers: layers.map(l => ({
            name: l.name,
            opacity: l.opacity,
            visible: l.visible,
            blend: l.blendMode,
            clipping: l.clippingMask,
            alphaLocked: l.alphaLocked,
            data: l.canvas.toDataURL()
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

    paperWidth = project.w; paperHeight = project.h;
    setupLogicalCanvas();
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
    selectedLayerIndex = layers.length - 1;

    // Reset history for fresh project load
    historyStack = []; historyIndex = -1;
    updateThumbnails(); updateLayersUI();
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
            });
            item.addEventListener('dragend', async () => {
                item.classList.remove('dragging');
                lastTargetId = null;

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
                if (draggedEl && draggedEl !== item && p.id !== lastTargetId) {
                    lastTargetId = p.id;
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
