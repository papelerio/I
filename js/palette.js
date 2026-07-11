// ─────────────────────────────────────────────────────────────
function initPalette() {
    const saved = localStorage.getItem('illustrator_palette_v2');
    if (saved) {
        try {
            paletteColors = JSON.parse(saved);
            paletteRows = Math.max(5, Math.ceil(paletteColors.length / paletteCols));
        } catch (e) { paletteColors = Array(paletteRows * paletteCols).fill(null).map(() => ({ c: null, s: null })); }
    } else {
        // Try to migrate from old format
        const old = localStorage.getItem('illustrator_palette');
        if (old) {
            try {
                const colors = JSON.parse(old);
                paletteColors = colors.map(c => ({ c: c, s: null }));
                paletteRows = Math.max(5, Math.ceil(paletteColors.length / paletteCols));
            } catch (e) { paletteColors = Array(paletteRows * paletteCols).fill(null).map(() => ({ c: null, s: null })); }
        } else {
            paletteColors = Array(paletteRows * paletteCols).fill(null).map(() => ({ c: null, s: null }));
        }
    }
    renderPalette();
}
function renderPalette() {
    paletteGrid.innerHTML = '';
    paletteColors.forEach((item, index) => {
        const cell = document.createElement('div'); cell.className = 'palette-cell';
        if (item && item.c) cell.style.background = item.c;

        if (item && item.s) {
            const badge = document.createElement('div');
            badge.className = 'palette-shortcut-badge';
            badge.textContent = item.s.toUpperCase();
            cell.appendChild(badge);
        }

        cell.onclick = () => {
            if (isAddingToPalette) {
                paletteColors[index].c = selectedColor;
                isAddingToPalette = false;
                addToPaletteBtn.classList.remove('active-waiting');
                checkAndExpandPalette(index);
                savePalette();
                renderPalette();
            }
            else if (item && item.c) { selectedColor = item.c; mainColorPicker.value = item.c; updateTintedTexture(); }
        };

        cell.oncontextmenu = (e) => { e.preventDefault(); showColorContextMenu(e.clientX, e.clientY, index); };
        paletteGrid.appendChild(cell);
    });
}
function savePalette() { localStorage.setItem('illustrator_palette_v2', JSON.stringify(paletteColors)); }
function checkAndExpandPalette(index) { if (Math.floor(index / paletteCols) === paletteRows - 1) { paletteRows++; paletteColors = paletteColors.concat(Array(paletteCols).fill(null).map(() => ({ c: null, s: null }))); } }
function showColorContextMenu(x, y, index) {
    const old = document.querySelector('.ctx-menu'); if (old) old.remove();
    const menu = document.createElement('div'); menu.className = 'ctx-menu'; menu.style.left = x + 'px'; menu.style.top = y + 'px';
    const item = paletteColors[index];

    if (item && item.c) {
        const cp = document.createElement('div'); cp.className = 'ctx-item'; cp.textContent = `Copiar ${item.c}`;
        cp.onclick = () => { if (navigator.clipboard) navigator.clipboard.writeText(item.c); menu.remove(); };
        menu.appendChild(cp);

        const sh = document.createElement('div'); sh.className = 'ctx-item'; sh.textContent = 'Asignar Atajo';
        sh.onclick = () => {
            const key = prompt(`Asignar atajo a este color (Tecla única):`, item.s || "");
            if (key !== null) {
                const lowKey = key.trim().toLowerCase().slice(0, 1);
                if (lowKey) checkAndAssignColorShortcut(index, lowKey);
                else { paletteColors[index].s = null; savePalette(); renderPalette(); }
            }
            menu.remove();
        };
        menu.appendChild(sh);
    }

    const del = document.createElement('div'); del.className = 'ctx-item delete'; del.textContent = 'Eliminar';
    del.onclick = () => { paletteColors[index] = { c: null, s: null }; checkAndShrinkPalette(); savePalette(); renderPalette(); menu.remove(); }; menu.appendChild(del);
    document.body.appendChild(menu); document.addEventListener('click', () => menu.remove(), { once: true });
}

function checkAndAssignColorShortcut(index, key) {
    const ms = (mainShortcutInput?.value || '').toLowerCase(), bs = (brushShortcutInput?.value || '').toLowerCase(), ls = (layersShortcutInput?.value || '').toLowerCase(), cs = (colorsShortcutInput?.value || '').toLowerCase();
    let conflict = key === ms ? 'Atajo Principal' : key === bs ? 'Atajo Pincel' : key === ls ? 'Atajo Capas' : key === cs ? 'Atajo Colores' : null;

    const tc = toolsData.find(t => (t.shortcut || '').toLowerCase() === key);
    const bc = brushTypesData.find(b => (b.shortcut || '').toLowerCase() === key);
    const cc = paletteColors.find((p, idx) => (p.s || '').toLowerCase() === key && idx !== index);

    if (tc) conflict = tc.name;
    else if (bc) conflict = bc.name;
    else if (cc) conflict = `Color en paleta (${cc.c})`;

    if (conflict) {
        if (confirm(`La tecla "${key.toUpperCase()}" ya está siendo usada por "${conflict}". ¿Quieres sobrescribirla?`)) {
            if (key === ms && mainShortcutInput) mainShortcutInput.value = '';
            if (key === bs && brushShortcutInput) brushShortcutInput.value = '';
            if (key === ls && layersShortcutInput) layersShortcutInput.value = '';
            if (key === cs && colorsShortcutInput) colorsShortcutInput.value = '';
            if (tc) tc.shortcut = '';
            if (bc) bc.shortcut = '';
            if (cc) cc.s = null;

            paletteColors[index].s = key;
            savePalette(); saveShortcuts(); renderPalette();
            setupMultiToolMenu(); setupBrushMenu();
        }
    } else {
        paletteColors[index].s = key;
        savePalette(); renderPalette();
    }
}

function checkAndShrinkPalette() {
    if (paletteRows <= 5) return;
    while (paletteRows > 5) {
        const start = (paletteRows - 1) * paletteCols;
        const rowEmpty = paletteColors.slice(start, start + paletteCols).every(c => c === null);
        if (rowEmpty) { const prevStart = (paletteRows - 2) * paletteCols; if (paletteColors.slice(prevStart, prevStart + paletteCols).every(c => c === null)) { paletteColors.splice(start, paletteCols); paletteRows--; } else break; } else break;
    }
}

// ─────────────────────────────────────────────────────────────
//  LAYERS
