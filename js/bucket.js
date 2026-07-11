// ─────────────────────────────────────────────────────────────
function executeBucket(worldX, worldY) {
    const px = Math.floor(worldX);
    const py = Math.floor(worldY);
    if (px < 0 || px >= paperWidth || py < 0 || py >= paperHeight) return;

    const l = layers[selectedLayerIndex];
    if (!l) return;

    // --- Build source pixel data (what we sample from) ---
    let srcData;
    if (bucketMode === 'lienzo') {
        // Composite all layers into a temp canvas for sampling
        const tmpC = document.createElement('canvas'); tmpC.width = paperWidth; tmpC.height = paperHeight;
        const tmpX = tmpC.getContext('2d');
        if (bgMode === 1) { tmpX.fillStyle = solidBgColor; tmpX.fillRect(0, 0, paperWidth, paperHeight); }
        compositeLayers(tmpX);
        srcData = tmpX.getImageData(0, 0, paperWidth, paperHeight).data;
    } else {
        srcData = l.ctx.getImageData(0, 0, paperWidth, paperHeight).data;
    }

    // --- Target color we click on ---
    const idx0 = (py * paperWidth + px) * 4;
    const tR = srcData[idx0];
    const tG = srcData[idx0 + 1];
    const tB = srcData[idx0 + 2];
    const tA = srcData[idx0 + 3];

    // --- Fill color ---
    let fillR, fillG, fillB, fillA;
    if (bucketFillMode === 'erase') {
        fillR = fillG = fillB = fillA = 0;
    } else {
        const fc = hexToRgbArray(selectedColor);
        fillR = fc[0]; fillG = fc[1]; fillB = fc[2]; fillA = Math.round(brushOpacity * 255);
    }

    // Skip if target === fill (would infinite loop or do nothing)
    if (bucketFillMode !== 'erase') {
        const sameColor = (tR === fillR && tG === fillG && tB === fillB && tA === fillA);
        if (sameColor && tA > 0) return;
    }

    // --- Color distance helper ---
    const tol = bucketTolerance;
    function colorMatch(i) {
        const dr = srcData[i] - tR;
        const dg = srcData[i + 1] - tG;
        const db = srcData[i + 2] - tB;
        const da = srcData[i + 3] - tA;
        return (dr * dr + dg * dg + db * db + da * da) <= tol * tol * 4;
    }

    // --- Prepare destination ImageData (always the active layer) ---
    const dstImgData = l.ctx.getImageData(0, 0, paperWidth, paperWidth === paperWidth ? paperHeight : paperHeight);
    const dst = dstImgData.data;

    function applyPixel(i) {
        if (bucketFillMode === 'erase') {
            dst[i] = dst[i + 1] = dst[i + 2] = dst[i + 3] = 0;
        } else {
            dst[i] = fillR; dst[i + 1] = fillG; dst[i + 2] = fillB; dst[i + 3] = fillA;
        }
    }

    const W = paperWidth;
    const H = paperHeight;

    if (bucketContiguous) {
        // ── Contiguous flood fill (4-connected stack BFS) ──
        const visited = new Uint8Array(W * H);
        const stack = [px + py * W];
        visited[px + py * W] = 1;

        while (stack.length > 0) {
            const pos = stack.pop();
            const x = pos % W;
            const y = (pos / W) | 0;
            const i = pos * 4;

            applyPixel(i);

            const neighbors = [
                x > 0     ? pos - 1 : -1,
                x < W - 1 ? pos + 1 : -1,
                y > 0     ? pos - W : -1,
                y < H - 1 ? pos + W : -1,
            ];
            for (const n of neighbors) {
                if (n >= 0 && !visited[n] && colorMatch(n * 4)) {
                    visited[n] = 1;
                    stack.push(n);
                }
            }
        }
    } else {
        // ── Global: replace all matching pixels in the layer ──
        for (let i = 0; i < srcData.length; i += 4) {
            if (colorMatch(i)) applyPixel(i);
        }
    }

    // Apply selection mask if active
    if (hasSelection && selectionCanvas) {
        const origLayer = l.ctx.getImageData(0, 0, W, H).data; // snapshot BEFORE write
        const selData = selCtx.getImageData(0, 0, W, H).data;
        // Blend fill with original based on selection mask
        for (let i = 0; i < dst.length; i += 4) {
            const sa = selData[i + 3];
            if (sa < 128) {
                dst[i]     = origLayer[i];
                dst[i + 1] = origLayer[i + 1];
                dst[i + 2] = origLayer[i + 2];
                dst[i + 3] = origLayer[i + 3];
            }
        }
        l.ctx.putImageData(dstImgData, 0, 0);
    } else {
        l.ctx.putImageData(dstImgData, 0, 0);
    }

    updateThumbnails();
    updateLayersUI();
    pushHistory();
    requestRender();
}

function buildBucketPanel() {
    if (document.getElementById('bucket-settings-panel')) return;
    const panel = document.createElement('div');
    panel.id = 'bucket-settings-panel';
    panel.className = 'floating-menu hidden';
    panel.style.cssText = 'position:fixed !important; top:80px; left:auto !important; right:20px; width:260px; z-index:2000; pointer-events:auto;';
    panel.innerHTML = `
        <div class="menu-header" style="cursor:default"><label>⚙ Configuración Cubeta</label></div>
        <div style="padding:14px; display:flex; flex-direction:column; gap:14px;">

            <div>
                <div style="display:flex; justify-content:space-between; align-items:center; margin-bottom:6px;">
                    <label style="font-size:11px; font-weight:700; color:#888;">TOLERANCIA</label>
                    <span id="bucket-tol-value" style="font-size:12px; font-weight:700; color:#0066ff;">32</span>
                </div>
                <input type="range" id="bucket-tol-slider" min="0" max="255" value="32"
                    style="width:100%; accent-color:#0066ff;">
                <div style="display:flex; justify-content:space-between; margin-top:2px;">
                    <span style="font-size:9px; color:#aaa;">Exacto</span>
                    <span style="font-size:9px; color:#aaa;">Todo</span>
                </div>
            </div>

            <div>
                <label style="font-size:11px; font-weight:700; color:#888; display:block; margin-bottom:8px;">MODO DE RELLENO</label>
                <div style="display:flex; gap:6px;">
                    <button id="bucket-fill-solid" class="bucket-mode-pill active-pill">🎨 Color</button>
                    <button id="bucket-fill-erase" class="bucket-mode-pill">🧹 Borrar</button>
                </div>
            </div>

            <div>
                <label style="font-size:11px; font-weight:700; color:#888; display:block; margin-bottom:8px;">ÁREA DE RELLENO</label>
                <div style="display:flex; gap:6px;">
                    <button id="bucket-area-contig" class="bucket-mode-pill active-pill">⬤ Contiguo</button>
                    <button id="bucket-area-global" class="bucket-mode-pill">◎ Global</button>
                </div>
            </div>

            <div>
                <label style="font-size:11px; font-weight:700; color:#888; display:block; margin-bottom:8px;">FUENTE DE MUESTRA</label>
                <div style="display:flex; gap:6px;">
                    <button id="bucket-src-layer" class="bucket-mode-pill active-pill">Capa activa</button>
                    <button id="bucket-src-canvas" class="bucket-mode-pill">Lienzo completo</button>
                </div>
            </div>
        </div>`;
    document.body.appendChild(panel);
    bucketPanel = panel;

    // Pill helper
    function setPills(groupIds, activeId) {
        groupIds.forEach(id => {
            const btn = document.getElementById(id);
            if (btn) btn.classList.toggle('active-pill', id === activeId);
        });
    }

    // Tolerance
    const tolSlider = document.getElementById('bucket-tol-slider');
    const tolVal = document.getElementById('bucket-tol-value');
    tolSlider.oninput = () => {
        bucketTolerance = parseInt(tolSlider.value);
        tolVal.textContent = bucketTolerance;
    };
    tolSlider.onpointerup = (e) => e.target.blur();

    // Fill mode
    document.getElementById('bucket-fill-solid').onclick = () => {
        bucketFillMode = 'solid';
        setPills(['bucket-fill-solid', 'bucket-fill-erase'], 'bucket-fill-solid');
    };
    document.getElementById('bucket-fill-erase').onclick = () => {
        bucketFillMode = 'erase';
        setPills(['bucket-fill-solid', 'bucket-fill-erase'], 'bucket-fill-erase');
    };

    // Contiguous
    document.getElementById('bucket-area-contig').onclick = () => {
        bucketContiguous = true;
        setPills(['bucket-area-contig', 'bucket-area-global'], 'bucket-area-contig');
    };
    document.getElementById('bucket-area-global').onclick = () => {
        bucketContiguous = false;
        setPills(['bucket-area-contig', 'bucket-area-global'], 'bucket-area-global');
    };

    // Source
    document.getElementById('bucket-src-layer').onclick = () => {
        bucketMode = 'capa';
        setPills(['bucket-src-layer', 'bucket-src-canvas'], 'bucket-src-layer');
    };
    document.getElementById('bucket-src-canvas').onclick = () => {
        bucketMode = 'lienzo';
        setPills(['bucket-src-layer', 'bucket-src-canvas'], 'bucket-src-canvas');
    };
}

function showBucketPanel(show) {
    if (!bucketPanel) buildBucketPanel();
    if (show) bucketPanel.classList.remove('hidden');
    else bucketPanel.classList.add('hidden');
}

