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
        const isNavigation  = (id === 'zoom' || id === 'pan');  // Navegar no termina la sesión de empuje
        if (!isTargetPush && !isNavigation) {
            endPushSession();
        }
    }

    if (isResizingCanvas) {
        isResizingCanvas = false;
        resizePanel.classList.add('hidden');
    }

    if (id === 'pincel') {
        let b = brushTypesData.find(x => x.name === name || x.id === name || (x.displayName && x.displayName === name));

        // Redirect to remembered subtool if this brush belongs to a subtool group
        for (const groupKey in subtoolRegistry) {
            const group = subtoolRegistry[groupKey];
            if (group.isGroupMatch(id, name, b)) {
                if (name === group.containerName || !b) {
                    const rememberedId = lastSubtoolByGroup[groupKey];
                    const rememberedBrush = brushTypesData.find(x => x.id === rememberedId);
                    if (rememberedBrush) {
                        b = rememberedBrush;
                        name = rememberedBrush.name;
                    }
                } else if (b) {
                    saveSubtoolMemory(groupKey, b.id);
                }
                break;
            }
        }

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
        let targetToolId = id;
        let targetToolName = name;

        // Subtool group routing for multi-tools
        for (const groupKey in subtoolRegistry) {
            const group = subtoolRegistry[groupKey];
            if (group.isGroupMatch(id, name, null)) {
                if (name === group.containerName) {
                    const rememberedId = lastSubtoolByGroup[groupKey];
                    const rememberedItem = toolsData.find(x => x.id === rememberedId);
                    if (rememberedItem) {
                        targetToolId = rememberedItem.id;
                        targetToolName = rememberedItem.name;
                    }
                } else {
                    saveSubtoolMemory(groupKey, id);
                }
                break;
            }
        }

        currentTool = targetToolId;
        if (activeToolIndicator) activeToolIndicator.textContent = targetToolName;
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

    // Update dynamic top subtool icon bar
    updateTopSubtoolBar();

    updateTintedTexture();
}

// ─────────────────────────────────────────────────────────────
//  TOP BAR SUBTOOL SYSTEM (Automated & Dynamic with Memory)
// ─────────────────────────────────────────────────────────────
let lastSubtoolByGroup = {
    'borrador': 'borrador',    // default
    'aerografo': 'aero-suave', // default: aerógrafo suave
    'lazos': 'lazo-relleno',   // default: lazo de relleno
    'lazos-sel': 'lazo-sel'    // default: lazo seleccionador
};

try {
    const savedSubtools = localStorage.getItem('last_subtools_memory');
    if (savedSubtools) {
        Object.assign(lastSubtoolByGroup, JSON.parse(savedSubtools));
    }
} catch (e) {}

function saveSubtoolMemory(groupKey, subtoolId) {
    lastSubtoolByGroup[groupKey] = subtoolId;
    try {
        localStorage.setItem('last_subtools_memory', JSON.stringify(lastSubtoolByGroup));
    } catch (e) {}
}

const subtoolRegistry = {
    'borrador': {
        groupKey: 'borrador',
        containerName: 'Borrador',
        matches: (toolId, brush) => toolId === 'pincel' && brush && (brush.id === 'borrador' || brush.id === 'borrador-suave'),
        isGroupMatch: (toolId, name, brush) => name === 'Borrador' || (brush && (brush.id === 'borrador' || brush.id === 'borrador-suave')),
        items: [
            {
                id: 'borrador',
                name: 'Borrador Duro',
                icon: 'iconos pinceles/borrador duro.png',
                action: () => {
                    const b = brushTypesData.find(x => x.id === 'borrador');
                    if (b) {
                        currentBrush = b;
                        saveSubtoolMemory('borrador', 'borrador');
                        syncBrushUI();
                    }
                },
                isActive: (brush) => brush && brush.id === 'borrador'
            },
            {
                id: 'borrador-suave',
                name: 'Borrador Suave',
                icon: 'iconos pinceles/borrador suave.png',
                action: () => {
                    const b = brushTypesData.find(x => x.id === 'borrador-suave');
                    if (b) {
                        currentBrush = b;
                        saveSubtoolMemory('borrador', 'borrador-suave');
                        syncBrushUI();
                    }
                },
                isActive: (brush) => brush && brush.id === 'borrador-suave'
            }
        ]
    },
    'aerografo': {
        groupKey: 'aerografo',
        containerName: 'Aerógrafo',
        matches: (toolId, brush) => toolId === 'pincel' && brush && (brush.id === 'aero-suave' || brush.id === 'aero-duro'),
        isGroupMatch: (toolId, name, brush) => name === 'Aerógrafo' || name === 'Aerografo' || (brush && (brush.id === 'aero-suave' || brush.id === 'aero-duro')),
        items: [
            {
                id: 'aero-suave',
                name: 'Aerógrafo Suave',
                icon: 'iconos pinceles/aerografo suave.png',
                action: () => {
                    const b = brushTypesData.find(x => x.id === 'aero-suave');
                    if (b) {
                        currentBrush = b;
                        saveSubtoolMemory('aerografo', 'aero-suave');
                        syncBrushUI();
                    }
                },
                isActive: (brush) => brush && brush.id === 'aero-suave'
            },
            {
                id: 'aero-duro',
                name: 'Aerógrafo Duro',
                icon: 'iconos pinceles/aerografo duro.png',
                action: () => {
                    const b = brushTypesData.find(x => x.id === 'aero-duro');
                    if (b) {
                        currentBrush = b;
                        saveSubtoolMemory('aerografo', 'aero-duro');
                        syncBrushUI();
                    }
                },
                isActive: (brush) => brush && brush.id === 'aero-duro'
            }
        ]
    },
    'lazos': {
        groupKey: 'lazos',
        containerName: 'Lazos de Dibujo',
        matches: (toolId, brush) => toolId === 'pincel' && brush && (brush.id === 'lazo-relleno' || brush.id === 'lazo-borrador'),
        isGroupMatch: (toolId, name, brush) => name === 'Lazos de Dibujo' || name === 'Lazo de Relleno' || name === 'Lazo Borrador' || (brush && (brush.id === 'lazo-relleno' || brush.id === 'lazo-borrador')),
        items: [
            {
                id: 'lazo-relleno',
                name: 'Lazo de Relleno',
                icon: 'iconos pinceles/lazo de relleno.png',
                brushId: 'lazo-relleno',
                hasShortcut: true,
                action: () => {
                    const b = brushTypesData.find(x => x.id === 'lazo-relleno');
                    if (b) {
                        currentBrush = b;
                        saveSubtoolMemory('lazos', 'lazo-relleno');
                        syncBrushUI();
                    }
                },
                isActive: (brush) => brush && brush.id === 'lazo-relleno'
            },
            {
                id: 'lazo-borrador',
                name: 'Lazo Borrador',
                icon: 'iconos pinceles/lazo borrador.png',
                brushId: 'lazo-borrador',
                hasShortcut: true,
                action: () => {
                    const b = brushTypesData.find(x => x.id === 'lazo-borrador');
                    if (b) {
                        currentBrush = b;
                        saveSubtoolMemory('lazos', 'lazo-borrador');
                        syncBrushUI();
                    }
                },
                isActive: (brush) => brush && brush.id === 'lazo-borrador'
            },
            {
                id: 'lazo-mode-toggle',
                name: () => `Modo Lazo: ${lassoFillMode === 'rectangulo' ? 'Rectangular' : 'Libre'}`,
                icon: () => lassoFillMode === 'rectangulo' ? 'iconos pinceles/rectangular.png' : 'iconos pinceles/libre.png',
                hasShortcut: false,
                isToggle: true,
                action: () => {
                    lassoFillMode = lassoFillMode === 'libre' ? 'rectangulo' : 'libre';
                    if (typeof updateLassoFillModeUI === 'function') updateLassoFillModeUI();
                },
                isActive: () => lassoFillMode === 'rectangulo'
            }
        ]
    },
    'lazos-sel': {
        groupKey: 'lazos-sel',
        containerName: 'Lazos de Selección',
        matches: (toolId, brush) => toolId === 'lazo-sel' || toolId === 'lazo-des',
        isGroupMatch: (toolId, name, brush) => toolId === 'lazo-sel' || toolId === 'lazo-des' || name === 'Lazos de Selección' || name === 'Lazos de Seleccion' || name === 'Lazo Seleccionador' || name === 'Lazo Deseleccionador',
        items: [
            {
                id: 'lazo-sel',
                name: 'Lazo Seleccionador',
                icon: 'iconos multiherramientas/lazo seleccionador.png',
                toolId: 'lazo-sel',
                hasShortcut: true,
                action: () => {
                    selectTool('lazo-sel', 'Lazo Seleccionador');
                    saveSubtoolMemory('lazos-sel', 'lazo-sel');
                },
                isActive: () => currentTool === 'lazo-sel'
            },
            {
                id: 'lazo-des',
                name: 'Lazo Deseleccionador',
                icon: 'iconos multiherramientas/lazo deseleccionador.png',
                toolId: 'lazo-des',
                hasShortcut: true,
                action: () => {
                    selectTool('lazo-des', 'Lazo Deseleccionador');
                    saveSubtoolMemory('lazos-sel', 'lazo-des');
                },
                isActive: () => currentTool === 'lazo-des'
            },
            {
                id: 'lazo-sel-mode-toggle',
                name: () => `Modo Selección: ${lassoSelMode === 'cuadrado' || lassoSelMode === 'rectangulo' ? 'Rectangular' : 'Libre'}`,
                icon: () => (lassoSelMode === 'cuadrado' || lassoSelMode === 'rectangulo') ? 'iconos pinceles/rectangular.png' : 'iconos pinceles/libre.png',
                hasShortcut: false,
                isToggle: true,
                action: () => {
                    lassoSelMode = (lassoSelMode === 'libre') ? 'cuadrado' : 'libre';
                    updateTopSubtoolBar();
                },
                isActive: () => lassoSelMode === 'cuadrado' || lassoSelMode === 'rectangulo'
            }
        ]
    },
    'modify-sel': {
        groupKey: 'modify-sel',
        containerName: 'Modificar Selección',
        matches: (toolId, brush) => toolId === 'modify-sel',
        isGroupMatch: (toolId, name, brush) => toolId === 'modify-sel' || name === 'Modificar Selección' || name === 'Modificar Seleccion',
        items: [
            {
                id: 'flip-h',
                name: 'Voltear Horizontalmente',
                icon: 'voltear horizontalmente.png',
                isInstant: true,
                action: () => {
                    if (typeof flipSelection === 'function') flipSelection('h');
                }
            },
            {
                id: 'flip-v',
                name: 'Voltear Verticalmente',
                icon: 'voltear verticalmente.png',
                isInstant: true,
                action: () => {
                    if (typeof flipSelection === 'function') flipSelection('v');
                }
            },
            {
                id: 'perspective',
                name: 'Perspectiva',
                icon: 'perspectiva.png',
                isToggle: true,
                action: () => {
                    if (typeof togglePerspectiveMode === 'function') togglePerspectiveMode();
                },
                isActive: () => typeof modSelPerspectiveMode !== 'undefined' && modSelPerspectiveMode
            }
        ]
    }
};

function updateTopSubtoolBar() {
    const topBar = document.getElementById('top-subtool-bar');
    if (!topBar) return;

    let activeGroup = null;
    for (const key in subtoolRegistry) {
        if (subtoolRegistry[key].matches(currentTool, currentBrush)) {
            activeGroup = subtoolRegistry[key];
            break;
        }
    }

    if (!activeGroup) {
        topBar.classList.add('hidden');
        topBar.innerHTML = '';
        return;
    }

    topBar.innerHTML = '';
    activeGroup.items.forEach(item => {
        const btn = document.createElement('button');
        const active = typeof item.isActive === 'function' ? item.isActive(currentBrush) : false;
        const itemIcon = typeof item.icon === 'function' ? item.icon() : item.icon;
        const itemName = typeof item.name === 'function' ? item.name() : item.name;

        let btnClass = 'top-subtool-btn';
        if (item.isToggle) btnClass += ' toggle-btn';
        if (item.isInstant) btnClass += ' instant-btn';
        if (active) btnClass += ' active';

        btn.className = btnClass;
        btn.title = itemName;

        const img = document.createElement('img');
        img.src = itemIcon;
        img.alt = itemName;
        btn.appendChild(img);

        const toolObj = item.toolId ? toolsData.find(x => x.id === item.toolId) : null;
        const brushObj = item.brushId ? brushTypesData.find(x => x.id === item.brushId) : null;
        const targetObj = toolObj || brushObj;
        const targetType = toolObj ? 'tool' : 'brush';
        const shortcutKey = item.hasShortcut && targetObj ? (targetObj.shortcut || '') : '';

        if (shortcutKey) {
            const badge = document.createElement('div');
            badge.className = 'top-subtool-badge';
            let modPrefix = '';
            if (targetObj?.modifier === '+shift') modPrefix = '⇧';
            else if (targetObj?.modifier === '+shift+ctrl') modPrefix = '⌃⇧';
            badge.textContent = modPrefix + shortcutKey.toUpperCase();
            btn.appendChild(badge);
        }

        btn.onclick = (e) => {
            e.stopPropagation();
            item.action();
            updateTopSubtoolBar();
            if (typeof setupMultiToolMenu === 'function') setupMultiToolMenu();
            if (typeof setupBrushMenu === 'function') setupBrushMenu();
        };

        if (item.hasShortcut && targetObj) {
            btn.oncontextmenu = (e) => {
                e.preventDefault();
                e.stopPropagation();
                if (typeof openShortcutEditModal === 'function') {
                    openShortcutEditModal(targetObj, targetType);
                }
            };
        }

        topBar.appendChild(btn);
    });

    topBar.classList.remove('hidden');
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
