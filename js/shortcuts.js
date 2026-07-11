function handleGlobalShortcuts(e) {
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
function renderMenuList(cont, data, type) {
    cont.innerHTML = '';
    data.forEach(item => {
        const li = document.createElement('li'); li.className = 'tool-item';
        const nameSpan = document.createElement('span');
        nameSpan.textContent = item.name;
        const shortcutInput = document.createElement('input');
        shortcutInput.type = 'text';
        shortcutInput.className = 'tool-shortcut-input';
        shortcutInput.maxLength = 1;
        shortcutInput.value = item.shortcut || '';
        const modSelect = document.createElement('select');
        modSelect.className = 'tool-shortcut-modifier';
        modSelect.style.cssText = 'font-size:10px; padding:1px 2px; border:1px solid #ccc; border-radius:3px; background:#222; color:#ddd; cursor:pointer; margin-left:3px;';
        modSelect.title = 'Modificador del atajo';
        [['normal', 'Normal'], ['+shift', '+Shift'], ['+shift+ctrl', '+Shift+Ctrl']].forEach(([v, l]) => {
            const opt = document.createElement('option');
            opt.value = v; opt.textContent = l;
            if ((item.modifier || 'normal') === v) opt.selected = true;
            modSelect.appendChild(opt);
        });
        modSelect.onchange = () => { item.modifier = modSelect.value; saveShortcuts(); };
        li.appendChild(nameSpan);
        li.appendChild(shortcutInput);
        li.appendChild(modSelect);
        li.onclick = e => { if (e.target.tagName !== 'INPUT' && e.target.tagName !== 'SELECT') { type === 'brush' ? selectTool('pincel', item.name) : selectTool(item.id, item.name); } };
        shortcutInput.onkeydown = e => { if (e.key.length === 1) { e.preventDefault(); checkAndAssignShortcut(item, e.key.toLowerCase(), type); } };
        cont.appendChild(li);
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
