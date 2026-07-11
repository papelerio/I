function startProjectTimer() {
    if (projectTimerInterval) clearInterval(projectTimerInterval);
    projectTimerInterval = setInterval(() => {
        if (document.visibilityState === 'visible' && !mainApp.classList.contains('blur-content')) {
            currentProjectTime++;
        }
    }, 1000);
}

function stopProjectTimer() {
    if (projectTimerInterval) {
        clearInterval(projectTimerInterval);
        projectTimerInterval = null;
    }
}

// ─────────────────────────────────────────────────────────────
//  INIT
// ─────────────────────────────────────────────────────────────
function init() {
    createCheckerPattern(); setupScreen();
    window.addEventListener('resize', setupScreen);
    document.addEventListener('contextmenu', e => e.preventDefault());

    // Render Gallery on startup
    renderGallery();

    // Gallery UI listeners
    document.getElementById('gallery-back-btn').onclick = () => {
        galleryMode = 'grid';
        renderGallery();
    };
    document.getElementById('gallery-add-btn').onclick = () => {
        startupModal.style.display = 'flex';
    };
    document.getElementById('gallery-edit-btn').onclick = () => {
        if (gallerySelectedProjectId) {
            loadProject(gallerySelectedProjectId);
        }
    };
    document.getElementById('detail-delete-btn').onclick = () => {
        if (gallerySelectedProjectId) {
            deleteProject(gallerySelectedProjectId);
        }
    };
    document.getElementById('detail-rename-btn').onclick = () => {
        if (gallerySelectedProjectId) {
            renameProject(gallerySelectedProjectId);
        }
    };

    // Core event listeners - attached ONLY ONCE
    canvas.addEventListener('pointerdown', handlePointerDown);
    canvas.addEventListener('pointermove', handlePointerMove);
    canvas.addEventListener('pointerup', handlePointerUp);
    canvas.addEventListener('pointercancel', handlePointerUp);

    // Fast Zoom with Mouse Wheel (Centered at cursor)
    canvas.addEventListener('wheel', (e) => {
        e.preventDefault();
        const delta = -e.deltaY;
        const factor = Math.pow(1.1, delta / 100);

        const rect = canvas.getBoundingClientRect();
        const mouseX = e.clientX - rect.left;
        const mouseY = e.clientY - rect.top;

        // World coordinates before zoom
        const worldBefore = screenToWorld(mouseX, mouseY);

        // Update scale
        viewScale *= factor;
        viewScale = Math.max(0.01, Math.min(viewScale, 50));

        // World coordinates after zoom
        const worldAfter = screenToWorld(mouseX, mouseY);

        // Adjust view position to keep mouse over the same world point
        viewPosX += (worldAfter.x - worldBefore.x);
        viewPosY += (worldAfter.y - worldBefore.y);
        requestRender();
    }, { passive: false });

    flipControls = document.getElementById('flip-controls');
    flipHBtn = document.getElementById('flip-h-btn');
    flipVBtn = document.getElementById('flip-v-btn');
    if (flipHBtn) flipHBtn.onclick = () => flipSelection('h');
    if (flipVBtn) flipVBtn.onclick = () => flipSelection('v');

    // Perspective button (created dynamically, placed alongside flip buttons)
    if (flipControls) {
        perspBtn = document.createElement('button');
        perspBtn.className = 'floating-flip-btn';
        perspBtn.id = 'perspective-mode-btn';
        perspBtn.title = 'Modo Perspectiva';
        perspBtn.innerHTML = `<img src="perspectiva.png" style="width:28px;height:28px;object-fit:contain;">`;
        perspBtn.style.cssText = 'background:rgba(30,30,40,0.9); border:1px solid rgba(255,255,255,0.2); color:white; padding:8px; cursor:pointer; border-radius:10px; transition:all 0.2s;';
        perspBtn.onclick = togglePerspectiveMode;
        flipControls.appendChild(perspBtn);
    }

    initPalette();
    loadShortcuts();
    setupMultiToolMenu();
    setupBrushMenu();

    requestRender();

    createBtn.onclick = () => {
        startApp(parseInt(canvasWidthInput.value) | 0, parseInt(canvasHeightInput.value) | 0);
        resetImportButton();
    };
    importBtn.onclick = () => {
        if (startupImportState === 0) {
            startupImportState = 1;
            importBtn.classList.add('waiting-paste');
            importBtn.textContent = 'ESPERANDO CTRL + V...';
        } else {
            resetImportButton();
            fileInput.click();
        }
    };

    // Drag & Drop (external files only — internal layer drags are ignored via isDraggingLayer)
    window.addEventListener('dragover', (e) => e.preventDefault());
    window.addEventListener('drop', (e) => {
        e.preventDefault();
        if (isDraggingLayer) return; // internal layer reorder — do nothing here
        const files = e.dataTransfer.files;
        if (files && files.length > 0) {
            handleIncomingFile(files[0]);
        }
    });

    // Listener for Paste
    window.addEventListener('paste', (e) => {
        // 1. Try to get images from items (standard for images copied from web/apps)
        const items = (e.clipboardData || e.originalEvent.clipboardData).items;
        let found = false;
        for (let i = 0; i < items.length; i++) {
            if (items[i].type.indexOf("image") !== -1) {
                const file = items[i].getAsFile();
                if (file) {
                    handleIncomingFile(file);
                    found = true;
                    break;
                }
            }
        }

        // 2. If not found, try to get files (standard for files copied from desktop/explorer)
        if (!found) {
            const files = (e.clipboardData || e.originalEvent.clipboardData).files;
            if (files && files.length > 0) {
                for (let i = 0; i < files.length; i++) {
                    if (files[i].type.indexOf("image") !== -1) {
                        handleIncomingFile(files[i]);
                        break;
                    }
                }
            }
        }
    });

    fileInput.onchange = (e) => {
        const file = e.target.files[0];
        if (file) {
            handleIncomingFile(file);
            e.target.value = ''; // Clear value so same file can be imported again
        }
    };

    sizeSlider.oninput = (e) => { baseBrushSize = parseFloat(e.target.value); sizeValue.textContent = baseBrushSize < 10 ? baseBrushSize.toFixed(1) : Math.round(baseBrushSize); currentBrush.size = baseBrushSize; requestRender(); };
    sizeSlider.onpointerup = (e) => e.target.blur();

    // ── Size Preset Popup ──────────────────────────────────────
    (function initSizePresets() {
        const PRESETS = [0.1, 0.3, 0.5, 0.7, 1, 2, 3, 5, 7, 9, 12, 16, 20, 25, 30, 40, 50, 60, 75, 100];
        const tab     = document.getElementById('size-preset-tab');
        const popup   = document.getElementById('size-preset-popup');
        const grid    = document.getElementById('size-preset-grid');
        if (!tab || !popup || !grid) return;

        // Build circles
        function drawCircle(sz) {
            const MAX_R = 16;
            const canvasSize = MAX_R * 2 + 2;
            const c = document.createElement('canvas');
            c.width = canvasSize; c.height = canvasSize;
            const cx = c.getContext('2d');
            const r = Math.min(MAX_R, Math.max(0.8, sz * 0.32));
            cx.beginPath();
            cx.arc(canvasSize / 2, canvasSize / 2, r, 0, Math.PI * 2);
            cx.fillStyle = 'rgba(210,210,230,0.85)';
            cx.fill();
            return c;
        }

        function refreshActive() {
            grid.querySelectorAll('.size-preset-btn').forEach(btn => {
                btn.classList.toggle('active-size', parseFloat(btn.dataset.size) === baseBrushSize);
            });
        }

        PRESETS.forEach(sz => {
            const btn = document.createElement('button');
            btn.className = 'size-preset-btn';
            btn.dataset.size = sz;
            btn.appendChild(drawCircle(sz));
            const label = document.createElement('span');
            label.textContent = sz + ' px';
            btn.appendChild(label);
            btn.addEventListener('pointerdown', e => {
                e.stopPropagation();
                baseBrushSize = sz;
                sizeSlider.value = sz;
                sizeValue.textContent = sz < 10 ? sz.toFixed(1) : sz;
                currentBrush.size = sz;
                requestRender();
                refreshActive();
            });
            grid.appendChild(btn);
        });

        // Hover logic with a small delay so it doesn't flash
        let hideTimer = null;
        function showPopup() {
            clearTimeout(hideTimer);
            popup.classList.remove('hidden');
            refreshActive();
        }
        function hidePopup() {
            hideTimer = setTimeout(() => popup.classList.add('hidden'), 180);
        }

        tab.addEventListener('pointerenter', showPopup);
        tab.addEventListener('pointerleave', hidePopup);
        popup.addEventListener('pointerenter', () => clearTimeout(hideTimer));
        popup.addEventListener('pointerleave', hidePopup);
    })();
    // ──────────────────────────────────────────────────────────

    opacitySlider.oninput = (e) => { 
        brushOpacity = e.target.value / 100; 
        opacityValue.textContent = e.target.value + '%'; 
        if (currentTool === 'bucket') {
            const t = toolsData.find(x => x.id === 'bucket');
            if (t) t.opacity = brushOpacity;
        } else if (currentBrush) {
            currentBrush.opacity = brushOpacity; 
        }
        if (eyeIcon) eyeIcon.src = (e.target.value | 0) === 0 ? 'simbolo ojo cerrado.png' : 'imagenes/simbolo ojo abierto.png'; 
        requestRender(); 
    };
    opacitySlider.onpointerup = (e) => e.target.blur();

    // ── Opacity Preset Popup ───────────────────────────────────
    (function initOpacityPresets() {
        const PRESETS = [5,10,15,20,25,30,35,40,45,50,55,60,65,70,75,80,85,90,95,100];
        const tab   = document.getElementById('opacity-preset-tab');
        const popup = document.getElementById('opacity-preset-popup');
        const grid  = document.getElementById('opacity-preset-grid');
        if (!tab || !popup || !grid) return;

        // Draw a small circle with a checkerboard behind + fill at the given opacity
        function drawOpacityCircle(pct) {
            const SIZE = 34; const R = 13;
            const c = document.createElement('canvas');
            c.width = SIZE; c.height = SIZE;
            const cx = c.getContext('2d');
            const cx2 = SIZE / 2, cy2 = SIZE / 2;

            // Checkerboard pattern (shows through the transparent areas)
            const sq = 4;
            for (let row = 0; row < SIZE / sq; row++) {
                for (let col = 0; col < SIZE / sq; col++) {
                    cx.fillStyle = (row + col) % 2 === 0 ? '#555' : '#333';
                    cx.fillRect(col * sq, row * sq, sq, sq);
                }
            }
            // Clip to circle and draw the colour fill at given opacity
            cx.save();
            cx.beginPath(); cx.arc(cx2, cy2, R, 0, Math.PI * 2); cx.clip();
            cx.clearRect(0, 0, SIZE, SIZE);
            // Re-draw checker inside clip
            for (let row = 0; row < SIZE / sq; row++) {
                for (let col = 0; col < SIZE / sq; col++) {
                    cx.fillStyle = (row + col) % 2 === 0 ? '#555' : '#333';
                    cx.fillRect(col * sq, row * sq, sq, sq);
                }
            }
            cx.globalAlpha = pct / 100;
            cx.fillStyle = 'rgba(210,210,230,1)';
            cx.fillRect(0, 0, SIZE, SIZE);
            cx.restore();
            // Circle border
            cx.beginPath(); cx.arc(cx2, cy2, R, 0, Math.PI * 2);
            cx.strokeStyle = 'rgba(255,255,255,0.18)'; cx.lineWidth = 1; cx.stroke();
            return c;
        }

        function refreshActive() {
            const cur = Math.round(brushOpacity * 100);
            grid.querySelectorAll('.size-preset-btn').forEach(btn => {
                btn.classList.toggle('active-size', parseInt(btn.dataset.opacity) === cur);
            });
        }

        PRESETS.forEach(pct => {
            const btn = document.createElement('button');
            btn.className = 'size-preset-btn';
            btn.dataset.opacity = pct;
            btn.appendChild(drawOpacityCircle(pct));
            const label = document.createElement('span');
            label.textContent = pct + '%';
            btn.appendChild(label);
            btn.addEventListener('pointerdown', e => {
                e.stopPropagation();
                brushOpacity = pct / 100;
                opacitySlider.value = pct;
                opacityValue.textContent = pct + '%';
                if (currentTool === 'bucket') {
                    const t = toolsData.find(x => x.id === 'bucket');
                    if (t) t.opacity = brushOpacity;
                } else if (currentBrush) {
                    currentBrush.opacity = brushOpacity;
                }
                if (eyeIcon) eyeIcon.src = pct === 0 ? 'simbolo ojo cerrado.png' : 'imagenes/simbolo ojo abierto.png';
                requestRender();
                refreshActive();
            });
            grid.appendChild(btn);
        });

        let hideTimer = null;
        function showPopup() { clearTimeout(hideTimer); popup.classList.remove('hidden'); refreshActive(); }
        function hidePopup() { hideTimer = setTimeout(() => popup.classList.add('hidden'), 180); }

        tab.addEventListener('pointerenter', showPopup);
        tab.addEventListener('pointerleave', hidePopup);
        popup.addEventListener('pointerenter', () => clearTimeout(hideTimer));
        popup.addEventListener('pointerleave', hidePopup);
    })();
    // ──────────────────────────────────────────────────────────

    blurSlider.oninput = (e) => { currentBlur = e.target.value | 0; blurValueLabel.textContent = currentBlur; currentBrush.blur = currentBlur; updateTintedTexture(); };
    blurSlider.onpointerup = (e) => e.target.blur();

    const stabModeBtn = document.getElementById('stab-mode-btn');
    if (stabModeBtn) {
        stabModeBtn.addEventListener('click', () => {
            stabMode = stabMode === 'post' ? 'realtime' : 'post';
            stabModeBtn.textContent = stabMode === 'post' ? 'POST' : 'VIVO';
            stabModeBtn.style.color = stabMode === 'post' ? '#8cf' : '#aaa';
        });
    }

    stabilizerSlider.oninput = (e) => { stabEnabled = e.target.value | 0; stabilizerValue.textContent = stabEnabled; };
    stabilizerSlider.onpointerup = (e) => e.target.blur();

    const pressureSlider = document.getElementById('pressure-slider');
    const pressureValueLabel = document.getElementById('pressure-value');
    if (pressureSlider) {
        pressureSlider.oninput = (e) => {
            // Slider 0-200 → sensitivity 0.0-2.0
            pressureSensitivity = parseInt(e.target.value) / 100;
            pressureValueLabel.textContent = e.target.value + '%';
        };
        pressureSlider.onpointerup = (e) => e.target.blur();
    }

    const velocitySlider     = document.getElementById('velocity-slider');
    const velocityValueLabel = document.getElementById('velocity-value');
    if (velocitySlider) {
        velocitySlider.oninput = (e) => {
            velocitySensitivity = parseInt(e.target.value) / 100;
            velocityValueLabel.textContent = e.target.value + '%';
        };
        velocitySlider.onpointerup = (e) => e.target.blur();
    }

    const velocityModeBtn = document.getElementById('velocity-mode-btn');
    if (velocityModeBtn) {
        velocityModeBtn.addEventListener('click', () => {
            velocityMode = velocityMode === 'slow' ? 'fast' : 'slow';
            velocityModeBtn.textContent  = velocityMode === 'slow' ? 'LENTO=+' : 'RÁPIDO=+';
            velocityModeBtn.style.color  = velocityMode === 'slow' ? '#aaa' : '#8cf';
        });
    }

    resetRotationBtn.onclick = resetRotation;
    function handleKeyDown(e) {
        if (e.code === 'Space' && e.target.tagName !== 'INPUT' && e.target.tagName !== 'SELECT') {
            isSpacePressed = true;
            if (currentTool !== 'pan') {
                canvas.style.cursor = 'grab';
            }
        }
        handleGlobalShortcuts(e);
        requestRender();
    }

    function handleKeyUp(e) {
        if (e.code === 'Space') {
            isSpacePressed = false;
            canvas.style.cursor = '';
        }
        requestRender();
    }

    document.addEventListener('keydown', handleKeyDown);
    document.addEventListener('keyup', handleKeyUp);


    const newLayerBtn = document.getElementById('new-layer-btn');
    newLayerBtn.onclick = () => addLayer("Nueva Capa");
    newLayerBtn.addEventListener('contextmenu', (e) => {
        e.preventDefault();
        const k = prompt('Ingresa 1 tecla para el atajo "Nueva Capa", o deja vacío para eliminar:', newLayerShortcut);
        if (k !== null) {
            newLayerShortcut = k.toLowerCase().substring(0, 1);
            saveShortcuts();
        }
    });

    // Quick layer action buttons
    const qAlpha = document.getElementById('qbtn-alpha');
    const qClip  = document.getElementById('qbtn-clip');
    const qMerge = document.getElementById('qbtn-merge');
    const ACTIVE_STYLE  = 'background: rgba(0,200,80,0.75); border-color: #00cc44; color: #fff;';
    const IDLE_STYLE    = 'background: rgba(255,255,255,0.4); backdrop-filter:blur(5px); border: 1px solid rgba(255,255,255,0.5); color: #333;';

    if (qAlpha) {
        qAlpha.addEventListener('pointerdown', (e) => {
            e.stopPropagation();
            const l = layers[selectedLayerIndex];
            if (!l) return;
            l.alphaLocked = !l.alphaLocked;
            updateLayersUI(); pushHistory();
        });
    }
    if (qClip) {
        qClip.addEventListener('pointerdown', (e) => {
            e.stopPropagation();
            const l = layers[selectedLayerIndex];
            if (!l) return;
            l.clippingMask = !l.clippingMask;
            layersCacheDirty = true;
            updateLayersUI(); pushHistory(); requestRender();
        });
    }
    if (qMerge) {
        qMerge.addEventListener('pointerdown', (e) => {
            e.stopPropagation();
            if (selectedLayerIndex <= 0) return;
            // Flash green briefly
            qMerge.style.cssText += ACTIVE_STYLE;
            setTimeout(() => { if (qMerge) qMerge.style.cssText = IDLE_STYLE + ' padding:3px 10px; border-radius:12px; font-size:10px; font-weight:bold; cursor:pointer; transition:all 0.2s; white-space:nowrap;'; }, 400);
            mergeLayerDown(selectedLayerIndex);
            updateThumbnails(); updateLayersUI();
        });
    }
    window._syncQuickLayerBtns = function() {
        const l = layers[selectedLayerIndex];
        if (!l) return;
        const BASE = 'padding:3px 10px; border-radius:12px; font-size:10px; font-weight:bold; cursor:pointer; transition:all 0.2s; white-space:nowrap; backdrop-filter:blur(5px);';
        if (qAlpha) qAlpha.style.cssText = BASE + (l.alphaLocked ? ACTIVE_STYLE : IDLE_STYLE);
        if (qClip)  qClip.style.cssText  = BASE + (l.clippingMask ? ACTIVE_STYLE : IDLE_STYLE);
        if (qMerge) qMerge.style.cssText = BASE + IDLE_STYLE;
    };
    document.getElementById('duplicate-layer-btn').onclick = duplicateSelectedLayer;
    document.getElementById('import-layer-btn').onclick = () => {
        if (layerImportState === 0) {
            layerImportState = 1;
            document.getElementById('import-layer-btn').classList.add('waiting-paste');
        } else {
            resetLayerImportButton();
            toggleMenu(null);
            fileInput.click();
        }
    };
    document.getElementById('insert-layer-btn').onclick = () => addLayer("Capa desde lienzo", true);
    
    const toggleBgBtn = document.getElementById('toggle-bg-btn');
    toggleBgBtn.onclick = toggleBackground;
    toggleBgBtn.oncontextmenu = (e) => {
        e.preventDefault();
        const input = document.createElement('input');
        input.type = 'color';
        input.value = solidBgColor;
        input.oninput = (ev) => {
            solidBgColor = ev.target.value;
            if (bgMode !== 1) {
                bgMode = 1;
                updateBgUI();
            }
            requestRender();
        };
        input.click();
    };

    document.getElementById('move-layer-btn').onclick = () => { toggleMenu(null); moveLayerContent(); };

    [mainShortcutInput, brushShortcutInput, layersShortcutInput, colorsShortcutInput, configShortcutInput].forEach(inp => {
        if (inp) inp.addEventListener('input', () => { if (inp.value.length > 1) inp.value = inp.value.slice(-1); saveShortcuts(); });
    });

    mainColorPicker.oninput = (e) => { selectedColor = e.target.value; updateTintedTexture(); };
    mainColorPicker.onchange = (e) => { e.target.blur(); };

    addToPaletteBtn.onclick = () => { isAddingToPalette = true; addToPaletteBtn.classList.add('active-waiting'); };

    // Main Actions UI
    document.getElementById('btn-config').onclick = () => toggleMenu(configMenu);
    document.getElementById('btn-main-actions').onclick = () => toggleMenu(mainActionsMenu);
    document.getElementById('action-download-png').onclick = () => { downloadImage(); toggleMenu(null); };
    document.getElementById('action-copy-all').onclick = () => { copyFlatImageToClipboard(); toggleMenu(null); };
    document.getElementById('action-save-project').onclick = async () => { await saveCurrentProject(); alert('Proyecto guardado.'); toggleMenu(null); };
    document.getElementById('action-gallery').onclick = async () => { await saveCurrentProject(); stopProjectTimer(); document.getElementById('gallery-screen').classList.remove('hidden'); mainApp.classList.add('blur-content'); mainApp.style.pointerEvents = 'none'; gallerySelectedProjectId = null; galleryMode = 'grid'; renderGallery(); toggleMenu(null); };

    // Filters Menu
    document.getElementById('btn-filters').onclick = () => toggleMenu(filtersMenu);
    document.querySelectorAll('.filter-opt-btn').forEach(btn => {
        btn.onclick = () => {
            toggleMenu(null);
            openFilterModal(btn.dataset.filter);
        };
    });

    // Filter Modal Actions
    document.getElementById('filter-apply-btn').onclick = commitFilter;
    document.getElementById('filter-cancel-btn').onclick = cancelFilter;

    // Config Menu Toggles
    document.getElementById('toggle-copy-mode').onclick = (e) => {
        const modes = ['capa', 'todas', 'canvas'];
        const labels = ['POR CAPA', 'TODAS LAS CAPAS', 'LIENZO COMPLETO'];
        const next = (modes.indexOf(copyMode) + 1) % modes.length;
        copyMode = modes[next];
        document.getElementById('copy-mode-value').textContent = labels[next];
    };
    document.getElementById('toggle-paste-layer').onclick = (e) => {
        pasteInNewLayer = !pasteInNewLayer;
        document.getElementById('paste-layer-value').textContent = pasteInNewLayer ? 'ON' : 'OFF';
    };
    document.getElementById('toggle-cursor-mode').onclick = (e) => {
        cursorMode = cursorMode === 'always' ? 'auto' : 'always';
        document.getElementById('cursor-mode-value').textContent = cursorMode === 'always' ? 'SIEMPRE VISIBLE' : 'AUTOMÁTICO';
        applyCursor(false);
    };

    // Resize Canvas
    document.getElementById('btn-resize-canvas').onclick = () => { openResizeModal(); toggleMenu(null); };
    document.getElementById('toggle-resize-libre').onclick = (e) => {
        resizeLibre = !resizeLibre;
        e.target.textContent = resizeLibre ? 'ON' : 'OFF';
        e.target.style.background = resizeLibre ? '#0066ff' : '';
        e.target.style.color = resizeLibre ? 'white' : '';
        if (!resizeLibre) {
            // Recalculate offsets from anchor when turning off Libre mode
            const dw = resizePreviewW - paperWidth;
            const dh = resizePreviewH - paperHeight;
            const col = resizeAnchor[1];
            const row = resizeAnchor[0];
            if (col === 'l') resizeOffsetX = 0;
            else if (col === 'c') resizeOffsetX = Math.round(dw / 2);
            else if (col === 'r') resizeOffsetX = dw;
            if (row === 't') resizeOffsetY = 0;
            else if (row === 'm') resizeOffsetY = Math.round(dh / 2);
            else if (row === 'b') resizeOffsetY = dh;
        }
    };

    // Fullscreen
    const fsBtn = document.getElementById('btn-fullscreen');
    const fsTitle = document.getElementById('fullscreen-title');
    fsBtn.onclick = () => toggleFullscreen();
    document.addEventListener('fullscreenchange', () => {
        fsTitle.textContent = document.fullscreenElement ? 'Salir de pantalla completa' : 'Pantalla completa';
    });

    // Build floating selection UI buttons (hidden by default)
    buildSelectionUI();

    initPalette(); loadShortcuts(); setupMultiToolMenu(); setupBrushMenu();
    applyCursor(false);
}

updateTintedTexture();
init();

