function handleGlobalShortcuts(e) {
    const galleryScreen = document.getElementById('gallery-screen');
    if (galleryScreen && !galleryScreen.classList.contains('hidden')) return;

    if (e.target.tagName === 'INPUT' || e.target.tagName === 'SELECT') return;
    const key = e.key.toLowerCase();

    // Allow Zoom and Pan shortcuts during filters
    if (activeFilterType) {
        if (activeFilterType === 'levels' && (e.key === 'ArrowUp' || e.key === 'ArrowDown')) {
            const channels = ['rgb', 'r', 'g', 'b'];
            let idx = channels.indexOf(activeCurveChannel);
            if (e.key === 'ArrowUp') idx = (idx - 1 + channels.length) % channels.length;
            else idx = (idx + 1) % channels.length;
            
            const select = document.getElementById('curveChannelSelect');
            if (select) {
                select.value = channels[idx];
                select.dispatchEvent(new Event('change'));
            }
            e.preventDefault();
            return;
        }

        const qS = brushTypesData.find(b => b.id === 'lazo-relleno')?.shortcut || 'q';
        const sS = brushTypesData.find(b => b.id === 'borrador')?.shortcut || 's';
        const wS = brushTypesData.find(b => b.id === 'lazo-borrador')?.shortcut || 'w';

        if (key === qS) { selectChromaLasso('add'); return; }
        if (key === sS) { selectChromaLasso('clear'); return; }
        if (key === wS) { selectChromaLasso('sub'); return; }
        if (key !== 'z' && key !== 'x') return;
    }

    if (!activeFilterType && !isModifyingShape && layerImportState === 0) {
        if (e.key === 'ArrowUp' || e.key === 'ArrowDown') {
            e.preventDefault();
            if (layers.length > 1) {
                endPushSession();
                if (e.key === 'ArrowUp') {
                    selectedLayerIndex = (selectedLayerIndex + 1) % layers.length;
                } else {
                    selectedLayerIndex = (selectedLayerIndex - 1 + layers.length) % layers.length;
                }
                updateLayersUI();
                pushHistory();
                requestRender();
            }
            return;
        }
    }

    const ms = (mainShortcutInput?.value || '').toLowerCase();
    const bs = (brushShortcutInput?.value || '').toLowerCase();
    const ls = (layersShortcutInput?.value || '').toLowerCase();
    const cs = (colorsShortcutInput?.value || '').toLowerCase();
    const cfs = (configShortcutInput?.value || '').toLowerCase();
    const nls = (newLayerShortcut || '').toLowerCase();

    if (key === nls && nls !== '') { addLayer("Nueva Capa"); return; }

    if (key === ms && ms !== '') { toggleMenu(multiToolMenu); return; }
    if (key === bs && bs !== '') { toggleMenu(brushTypeMenu); return; }
    if (key === ls && ls !== '') { toggleMenu(layersMenu); return; }
    if (key === cs && cs !== '') { toggleMenu(colorsMenu); return; }
    if (key === cfs && cfs !== '') { toggleMenu(configMenu); return; }

    if (e.ctrlKey && key === 'c') { e.preventDefault(); copyToClipboard(); return; }
    if (e.ctrlKey && key === 'x') { e.preventDefault(); cutToClipboard(); return; }
    if (e.ctrlKey && key === 's') {
        e.preventDefault();
        saveCurrentProject().then(() => {
            // Full-screen green border flash to confirm save
            const overlay = document.getElementById('save-flash-overlay');
            if (overlay) {
                overlay.classList.remove('flashing');
                // Force reflow so the animation restarts if triggered again quickly
                void overlay.offsetWidth;
                overlay.classList.add('flashing');
                overlay.addEventListener('animationend', () => {
                    overlay.classList.remove('flashing');
                }, { once: true });
            }
        });
        return;
    }
    if (e.ctrlKey && e.altKey && key === 'v') {
        if (startupImportState === 1 || layerImportState === 1) return;
        e.preventDefault(); pasteFromClipboard(true); return; 
    }
    if (e.ctrlKey && key === 'v') {
        if (startupImportState === 1 || layerImportState === 1) return; // Let the window 'paste' listener handle it
        e.preventDefault(); pasteFromClipboard(false); return;
    }
    if (e.ctrlKey && (key === 'z') && !e.shiftKey) { 
        e.preventDefault(); 
        if (isModifyingShape) {
            isModifyingShape = false;
            modSelInitialized = false; 
            modSelCanvas = null; 
            modSelBounds = null; 
            modSelOrigBounds = null;
            modSelRotation = 0; modSelFlipX = 1; modSelFlipY = 1;
            modSelLayersData = [];
            if (flipControls) flipControls.classList.add('hidden');
            selectTool('pincel', 'Pincel');
            updateThumbnails(); updateLayersUI();
            requestRender();
            return;
        }
        undo(); 
        return; 
    }
    if (e.ctrlKey && (key === 'y' || (e.shiftKey && key === 'z'))) { e.preventDefault(); redo(); return; }

    if (e.key === 'Enter' || e.key === 'Escape') {
        if (modSelInitialized) {
            e.preventDefault();
            commitModifySelection();
            if (e.key === 'Escape') clearSelection();
            return;
        }
        if (e.key === 'Escape' && hasSelection) {
            clearSelection();
            return;
        }
    }

    if (e.key === 'Delete' && hasSelection && !modSelInitialized) {
        e.preventDefault();
        const l = layers[selectedLayerIndex];
        l.ctx.save();
        l.ctx.globalCompositeOperation = 'destination-out';
        l.ctx.drawImage(selectionCanvas, 0, 0);
        l.ctx.restore();
        clearSelection(); // Remove selection mask after deletion
        updateThumbnails(); updateLayersUI();
        pushHistory();
        return;
    }

    const t = toolsData.find(x => {
        const k = (x.shortcut || '').toLowerCase();
        if (!k || k !== key) return false;
        const mod = x.modifier || 'normal';
        if (mod === '+shift') return e.shiftKey && !e.ctrlKey;
        if (mod === '+shift+ctrl') return e.shiftKey && e.ctrlKey;
        return !e.shiftKey && !e.ctrlKey;
    });
    if (t) { selectTool(t.id, t.name); return; }
    const bt = brushTypesData.find(x => {
        const k = (x.shortcut || '').toLowerCase();
        if (!k || k !== key) return false;
        const mod = x.modifier || 'normal';
        if (mod === '+shift') return e.shiftKey && !e.ctrlKey;
        if (mod === '+shift+ctrl') return e.shiftKey && e.ctrlKey;
        return !e.shiftKey && !e.ctrlKey;
    });
    if (bt) { selectTool('pincel', bt.name); return; }

    // Check palette shortcuts
    const pc = paletteColors.find(p => (p.s || '').toLowerCase() === key);
    if (pc && pc.c) {
        selectedColor = pc.c;
        mainColorPicker.value = pc.c;
        updateTintedTexture();
    }
}
function toggleMenu(m) {
    const menus = [multiToolMenu, brushTypeMenu, layersMenu, colorsMenu, mainActionsMenu, configMenu, filtersMenu];
    if (!m) { menus.forEach(x => x?.classList.add('hidden')); return; }
    const isHidden = m.classList.contains('hidden');
    menus.forEach(x => { if (x && x !== m) x.classList.add('hidden'); });
    if (isHidden) m.classList.remove('hidden'); else m.classList.add('hidden');
}
function setupMultiToolMenu() { if (toolsList) renderMenuList(toolsList, toolsData, 'tool'); }
function setupBrushMenu() { if (brushTypesList) renderMenuList(brushTypesList, brushTypesData, 'brush'); }
// Icon path mapping helper for brushes
function getBrushIconPath(id) {
    const mapping = {
        'duro': 'iconos pinceles/pincel.png',
        'suave': 'iconos pinceles/pincel suave.png',
        'borrador': 'iconos pinceles/borrador duro.png',
        'borrador-suave': 'iconos pinceles/borrador suave.png',
        'aero-duro': 'iconos pinceles/aerografo duro.png',
        'aero-suave': 'iconos pinceles/aerografo suave.png',
        'lazo-relleno': 'iconos pinceles/lazo de relleno.png',
        'lazo-borrador': 'iconos pinceles/lazo borrador.png',
        'linea': 'iconos pinceles/linea.png',
        'rectangulo': 'iconos pinceles/rectangulo.png',
        'circulo': 'iconos pinceles/elipce.png',
        'push-brush': 'iconos pinceles/empujar.png',
        'difuminar-arrastre': 'iconos pinceles/difuminar arrastre.png',
        'difuminar-gauss': 'iconos pinceles/difuminado de agua.png'
    };
    return mapping[id] || 'iconos pinceles/pincel.png';
}

// Icon path mapping helper for multi-tools
function getToolIconPath(id) {
    const mapping = {
        'zoom': 'iconos multiherramientas/zoom.png',
        'pan': 'iconos multiherramientas/pan.png',
        'rotate': 'iconos multiherramientas/rotar lienzo.png',
        'bucket': 'iconos multiherramientas/cubeta.png',
        'lazo-sel': 'iconos multiherramientas/lazo seleccionador.png',
        'lazo-des': 'iconos multiherramientas/lazo deseleccionador.png',
        'modify-sel': 'iconos multiherramientas/modificar seleccion.png',
        'eyedropper': 'iconos multiherramientas/gotero.png'
    };
    return mapping[id] || 'iconos multiherramientas/zoom.png';
}

// Modal helper to save shortcuts and check conflicts
function saveShortcutFromModal(item, key, modifier, type) {
    key = key.toLowerCase();
    
    // Check main menu shortcuts
    const ms = (mainShortcutInput?.value || '').toLowerCase();
    const bs = (brushShortcutInput?.value || '').toLowerCase();
    const ls = (layersShortcutInput?.value || '').toLowerCase();
    const cs = (colorsShortcutInput?.value || '').toLowerCase();
    const cfs = (configShortcutInput?.value || '').toLowerCase();
    
    let conflict = null;
    if (modifier === 'normal') {
        if (key === ms) conflict = 'Atajo Principal';
        else if (key === bs) conflict = 'Atajo Pincel';
        else if (key === ls) conflict = 'Atajo Capas';
        else if (key === cs) conflict = 'Atajo Colores';
        else if (key === cfs) conflict = 'Atajo Preferencias';
    }
    
    // Check conflicts inside tools and brushes
    const tc = toolsData.find(t => (t.shortcut || '').toLowerCase() === key && (t.modifier || 'normal') === modifier && t !== item);
    const bc = brushTypesData.find(b => (b.shortcut || '').toLowerCase() === key && (b.modifier || 'normal') === modifier && b !== item);
    const cc = modifier === 'normal' ? paletteColors.find(p => (p.s || '').toLowerCase() === key) : null;
    
    if (tc) conflict = tc.name;
    else if (bc) conflict = bc.name;
    else if (cc) conflict = `Color en paleta (${cc.c})`;
    
    const modLabel = modifier === 'normal' ? '' : ' (' + modifier + ')';
    if (conflict) {
        if (!confirm(`La tecla "${key.toUpperCase()}${modLabel}" ya está siendo usada por "${conflict}". ¿Quieres sobrescribirla?`)) {
            return false;
        }
        if (modifier === 'normal') {
            if (key === ms && mainShortcutInput) mainShortcutInput.value = '';
            if (key === bs && brushShortcutInput) brushShortcutInput.value = '';
            if (key === ls && layersShortcutInput) layersShortcutInput.value = '';
            if (key === cs && colorsShortcutInput) colorsShortcutInput.value = '';
            if (key === cfs && configShortcutInput) configShortcutInput.value = '';
        }
        if (tc) tc.shortcut = '';
        else if (bc) bc.shortcut = '';
        if (cc) cc.s = null;
    }
    
    item.shortcut = key;
    item.modifier = modifier;
    saveShortcuts();
    if (modifier === 'normal' && cc) savePalette();
    
    setupMultiToolMenu();
    setupBrushMenu();
    if (typeof renderPalette === 'function') renderPalette();
    return true;
}

// Open shortcut edit modal
function openShortcutEditModal(item, type) {
    const existing = document.getElementById('shortcut-edit-modal');
    if (existing) existing.remove();

    const overlay = document.createElement('div');
    overlay.id = 'shortcut-edit-modal';
    overlay.className = 'shortcut-modal-overlay';

    const content = document.createElement('div');
    content.className = 'shortcut-modal-content';

    const header = document.createElement('div');
    header.className = 'shortcut-modal-header';
    const icon = document.createElement('img');
    icon.src = type === 'brush' ? getBrushIconPath(item.id) : getToolIconPath(item.id);
    const title = document.createElement('span');
    title.textContent = item.name;
    header.appendChild(icon);
    header.appendChild(title);

    const body = document.createElement('div');
    body.className = 'shortcut-modal-body';

    // Shortcut Key field
    const fieldKey = document.createElement('div');
    fieldKey.className = 'shortcut-field-group';
    const labelKey = document.createElement('label');
    labelKey.textContent = 'Tecla de Atajo';
    const inputKey = document.createElement('input');
    inputKey.type = 'text';
    inputKey.className = 'shortcut-modal-input';
    inputKey.maxLength = 1;
    inputKey.placeholder = 'Ninguno';
    inputKey.value = item.shortcut || '';
    
    inputKey.onkeydown = e => {
        if (e.key.length === 1) {
            e.preventDefault();
            inputKey.value = e.key.toLowerCase();
        } else if (e.key === 'Backspace' || e.key === 'Delete') {
            e.preventDefault();
            inputKey.value = '';
        }
    };

    fieldKey.appendChild(labelKey);
    fieldKey.appendChild(inputKey);

    // Modifier field
    const fieldMod = document.createElement('div');
    fieldMod.className = 'shortcut-field-group';
    const labelMod = document.createElement('label');
    labelMod.textContent = 'Modificador';
    const selectMod = document.createElement('select');
    selectMod.className = 'shortcut-modal-input';
    selectMod.style.textAlign = 'left';
    
    [['normal', 'Ninguno'], ['+shift', 'Shift'], ['+shift+ctrl', 'Shift + Ctrl']].forEach(([v, l]) => {
        const opt = document.createElement('option');
        opt.value = v; opt.textContent = l;
        if ((item.modifier || 'normal') === v) opt.selected = true;
        selectMod.appendChild(opt);
    });

    fieldMod.appendChild(labelMod);
    fieldMod.appendChild(selectMod);

    body.appendChild(fieldKey);
    body.appendChild(fieldMod);

    // Actions
    const actions = document.createElement('div');
    actions.className = 'shortcut-modal-actions';
    const cancelBtn = document.createElement('button');
    cancelBtn.className = 'shortcut-modal-btn cancel';
    cancelBtn.textContent = 'Cancelar';
    cancelBtn.onclick = () => overlay.remove();

    const saveBtn = document.createElement('button');
    saveBtn.className = 'shortcut-modal-btn save';
    saveBtn.textContent = 'Guardar';
    saveBtn.onclick = () => {
        const success = saveShortcutFromModal(item, inputKey.value, selectMod.value, type);
        if (success) overlay.remove();
    };

    actions.appendChild(cancelBtn);
    actions.appendChild(saveBtn);

    content.appendChild(header);
    content.appendChild(body);
    content.appendChild(actions);
    overlay.appendChild(content);
    document.body.appendChild(overlay);

    inputKey.focus();
}

function renderMenuList(cont, data, type) {
    cont.innerHTML = '';
    cont.classList.add('tools-grid');
    
    data.forEach(item => {
        const card = document.createElement('div');
        
        let isActive = false;
        if (type === 'brush') {
            if (item.isPush) {
                isActive = (currentTool === 'push');
            } else {
                isActive = (currentTool === 'pincel' && currentBrush && currentBrush.id === item.id);
            }
        } else {
            isActive = (currentTool === item.id);
        }
        
        card.className = 'grid-item-card' + (isActive ? ' active' : '');
        card.title = item.name;
        
        // Icon Image
        const img = document.createElement('img');
        img.src = type === 'brush' ? getBrushIconPath(item.id) : getToolIconPath(item.id);
        img.alt = item.name;
        card.appendChild(img);
        
        // Shortcut Badge
        if (item.shortcut) {
            const badge = document.createElement('div');
            badge.className = 'grid-item-shortcut-badge';
            
            let modPrefix = '';
            if (item.modifier === '+shift') modPrefix = '⇧';
            else if (item.modifier === '+shift+ctrl') modPrefix = '⌃⇧';
            
            badge.textContent = modPrefix + item.shortcut.toUpperCase();
            card.appendChild(badge);
        }
        
        // Left click to select
        card.onclick = () => {
            if (type === 'brush') {
                selectTool('pincel', item.name);
            } else {
                selectTool(item.id, item.name);
            }
            setupMultiToolMenu();
            setupBrushMenu();
        };
        
        // Right click to edit shortcut
        card.oncontextmenu = (e) => {
            e.preventDefault();
            openShortcutEditModal(item, type);
        };
        
        cont.appendChild(card);
    });
}
function checkAndAssignShortcut(item, key, type) {
    // Read the modifier currently selected in the dropdown for this item
    const itemModifier = item.modifier || 'normal';
    const combo = key + '|' + itemModifier; // unique combo: e.g. "b|normal" vs "b|+shift"

    const ms = (mainShortcutInput?.value || '').toLowerCase(), bs = (brushShortcutInput?.value || '').toLowerCase(), ls = (layersShortcutInput?.value || '').toLowerCase(), cs = (colorsShortcutInput?.value || '').toLowerCase();

    // Menu-level shortcuts only use 'normal' modifier, so only conflict if modifier is also 'normal'
    let conflict = null;
    if (itemModifier === 'normal') {
        conflict = key === ms ? 'Atajo Principal' : key === bs ? 'Atajo Pincel' : key === ls ? 'Atajo Capas' : key === cs ? 'Atajo Colores' : null;
    }

    // Check tool/brush conflicts: same key AND same modifier
    const tc = toolsData.find(t => (t.shortcut || '').toLowerCase() === key && (t.modifier || 'normal') === itemModifier && t !== item);
    const bc = brushTypesData.find(b => (b.shortcut || '').toLowerCase() === key && (b.modifier || 'normal') === itemModifier && b !== item);
    // Palette shortcuts are always 'normal'
    const cc = itemModifier === 'normal' ? paletteColors.find(p => (p.s || '').toLowerCase() === key) : null;

    if (tc) conflict = tc.name;
    else if (bc) conflict = bc.name;
    else if (cc) conflict = `Color en paleta (${cc.c})`;

    const modLabel = itemModifier === 'normal' ? '' : ' (' + itemModifier + ')';
    if (conflict) {
        if (confirm(`La tecla "${key.toUpperCase()}${modLabel}" ya está siendo usada por "${conflict}". ¿Quieres sobrescribirla?`)) {
            if (itemModifier === 'normal') {
                if (key === ms && mainShortcutInput) mainShortcutInput.value = '';
                if (key === bs && brushShortcutInput) brushShortcutInput.value = '';
                if (key === ls && layersShortcutInput) layersShortcutInput.value = '';
                if (key === cs && colorsShortcutInput) colorsShortcutInput.value = '';
            }
            if (tc) tc.shortcut = '';
            else if (bc) bc.shortcut = '';
            if (cc) cc.s = null;

            item.shortcut = key;
            saveShortcuts();
            savePalette();
        }
    } else { item.shortcut = key; saveShortcuts(); }
    setupMultiToolMenu(); setupBrushMenu(); renderPalette();
}
function saveShortcuts() {
    localStorage.setItem('illustrator_state_v13', JSON.stringify({
        main: mainShortcutInput?.value || '', brushMenu: brushShortcutInput?.value || '',
        layersMenu: layersShortcutInput?.value || '', colorsMenu: colorsShortcutInput?.value || '',
        config: configShortcutInput?.value || '',
        newLayer: newLayerShortcut,
        tools: toolsData.map(t => ({ id: t.id, shortcut: t.shortcut, modifier: t.modifier || 'normal' })),
        brushes: brushTypesData.map(b => ({ id: b.id, shortcut: b.shortcut, modifier: b.modifier || 'normal' }))
    }));
}
function loadShortcuts() {
    const saved = localStorage.getItem('illustrator_state_v13'); if (!saved) return;
    try {
        const s = JSON.parse(saved);
        if (mainShortcutInput) mainShortcutInput.value = s.main || '+';
        if (brushShortcutInput) brushShortcutInput.value = s.brushMenu || '}';
        if (layersShortcutInput) layersShortcutInput.value = s.layersMenu || '.';
        if (colorsShortcutInput) colorsShortcutInput.value = s.colorsMenu || '-';
        if (configShortcutInput) configShortcutInput.value = s.config || '{';
        newLayerShortcut = s.newLayer !== undefined ? s.newLayer : '*';
        s.tools?.forEach(st => { const t = toolsData.find(x => x.id === st.id); if (t) { t.shortcut = st.shortcut || t.shortcut; t.modifier = st.modifier || 'normal'; } });
        s.brushes?.forEach(sb => { const b = brushTypesData.find(x => x.id === sb.id); if (b) { b.shortcut = sb.shortcut || b.shortcut; b.modifier = sb.modifier || 'normal'; } });
    } catch (e) { }
}

document.querySelectorAll('.tool-btn').forEach(btn => {
    btn.addEventListener('click', () => {
        if (btn.id === 'btn-filters' || btn.id === 'btn-brush' || btn.id === 'btn-colors' || btn.id === 'btn-layers' || btn.id === 'btn-config' || btn.id === 'btn-main-actions' || btn.id === 'btn-multi') return;

        toggleMenu(null);
        document.querySelector('.tool-btn.active')?.classList.remove('active');
        btn.classList.add('active');
    });
});

// The specialized toggle logic for these buttons is now in init() or handled via id-specific listeners there.
// Specifically the brush button:
document.getElementById('btn-brush').onclick = () => {
    if (currentTool === 'pincel') toggleMenu(brushTypeMenu);
    else selectTool('pincel', lastBrushTool);
};
document.getElementById('btn-multi').onclick = () => toggleMenu(multiToolMenu);
document.getElementById('btn-layers').onclick = () => toggleMenu(layersMenu);
document.getElementById('btn-colors').onclick = () => toggleMenu(colorsMenu);
