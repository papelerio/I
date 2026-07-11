//  PERSPECTIVE WARP RENDERER (bilinear scanline)
// ─────────────────────────────────────────────────────────────
/**
 * Draws an affine-mapped triangle from the source image onto the canvas.
 * Expands the clipping path slightly to hide Canvas 2D antialiasing seams.
 */
function drawTexturedTriangle(ctx, img, u0, v0, u1, v1, u2, v2, x0, y0, x1, y1, x2, y2) {
    ctx.save();
    
    // 1. Create expanded clipping path to avoid seams (líneas entrecortadas)
    // The padding must scale inversely with viewScale so it always covers ~2 screen pixels
    const cx = (x0 + x1 + x2) / 3;
    const cy = (y0 + y1 + y2) / 3;
    const pad = 2.5 / (typeof viewScale !== 'undefined' ? viewScale : 1); 
    
    const ex = (x, y) => {
        const dx = x - cx, dy = y - cy;
        const dist = Math.hypot(dx, dy) || 1;
        // Push vertices away from centroid to slightly overlap adjacent triangles
        return [x + (dx / dist) * pad, y + (dy / dist) * pad];
    };
    
    const [px0, py0] = ex(x0, y0);
    const [px1, py1] = ex(x1, y1);
    const [px2, py2] = ex(x2, y2);

    ctx.beginPath();
    ctx.moveTo(px0, py0);
    ctx.lineTo(px1, py1);
    ctx.lineTo(px2, py2);
    ctx.closePath();
    ctx.clip();

    // 2. Compute the affine transformation matrix
    const det = (u0 - u2) * (v1 - v2) - (u1 - u2) * (v0 - v2);
    if (Math.abs(det) < 0.0001) { ctx.restore(); return; }
    
    const a = ((x0 - x2) * (v1 - v2) - (x1 - x2) * (v0 - v2)) / det;
    const b = ((y0 - y2) * (v1 - v2) - (y1 - y2) * (v0 - v2)) / det;
    const c = ((u0 - u2) * (x1 - x2) - (u1 - u2) * (x0 - x2)) / det;
    const d = ((u0 - u2) * (y1 - y2) - (u1 - u2) * (y0 - y2)) / det;
    const e = x0 - a * u0 - c * v0;
    const f = y0 - b * u0 - d * v0;

    // 3. Apply exact mathematical transform (multiplies current transform)
    ctx.transform(a, b, c, d, e, f);
    ctx.drawImage(img, 0, 0);
    ctx.restore();
}

/**
 * corners: [TL, TR, BL, BR] each {x, y} in destination world coords
 * Renders src canvas warped into the quadrilateral using a Grid Mesh.
 */
function renderPerspectiveWarpPreview(destCtx, srcCanvas, corners) {
    const [tl, tr, bl, br] = corners;
    const srcW = srcCanvas.width, srcH = srcCanvas.height;
    if (srcW < 1 || srcH < 1) return;

    // 10x10 Grid for high quality deformation
    const cols = 10;
    const rows = 10;
    
    // Bilinear interpolation to find coordinate inside the arbitrary quad
    const getPos = (u, v) => {
        const topX = tl.x + (tr.x - tl.x) * u;
        const topY = tl.y + (tr.y - tl.y) * u;
        const botX = bl.x + (br.x - bl.x) * u;
        const botY = bl.y + (br.y - bl.y) * u;
        return {
            x: topX + (botX - topX) * v,
            y: topY + (botY - topY) * v
        };
    };

    // Draw mesh triangles
    for (let j = 0; j < rows; j++) {
        for (let i = 0; i < cols; i++) {
            // UV coords in [0, 1]
            const u0 = i / cols, v0 = j / rows;
            const u1 = (i + 1) / cols, v1 = j / rows;
            const u2 = i / cols, v2 = (j + 1) / rows;
            const u3 = (i + 1) / cols, v3 = (j + 1) / rows;

            // Target coordinates
            const p0 = getPos(u0, v0); // TL
            const p1 = getPos(u1, v1); // TR
            const p2 = getPos(u2, v2); // BL
            const p3 = getPos(u3, v3); // BR

            // Source coordinates in pixels
            const srcU0 = u0 * srcW, srcV0 = v0 * srcH;
            const srcU1 = u1 * srcW, srcV1 = v1 * srcH;
            const srcU2 = u2 * srcW, srcV2 = v2 * srcH;
            const srcU3 = u3 * srcW, srcV3 = v3 * srcH;

            // Triangle 1: TL -> TR -> BL
            drawTexturedTriangle(
                destCtx, srcCanvas,
                srcU0, srcV0, srcU1, srcV1, srcU2, srcV2,
                p0.x, p0.y, p1.x, p1.y, p2.x, p2.y
            );

            // Triangle 2: BR -> BL -> TR
            drawTexturedTriangle(
                destCtx, srcCanvas,
                srcU3, srcV3, srcU2, srcV2, srcU1, srcV1,
                p3.x, p3.y, p2.x, p2.y, p1.x, p1.y
            );
        }
    }
}

/**
 * Applies perspective warp permanently onto target layer context(s).
 * corners: [TL, TR, BL, BR] world coords.
 */
function applyPerspectiveWarpToLayer(targetCtx, srcCanvas, corners) {
    const tmp = document.createElement('canvas');
    tmp.width = paperWidth; tmp.height = paperHeight;
    const tctx = tmp.getContext('2d');
    renderPerspectiveWarpPreview(tctx, srcCanvas, corners);
    targetCtx.drawImage(tmp, 0, 0);
}

function commitModifySelection() {
    if (!modSelInitialized || !modSelBounds) return;

    // ── Perspective warp commit ──
    if (modSelPerspectiveMode && perspCorners) {
        if (!isImportingNewImage && modSelLayersData.length > 0) {
            modSelLayersData.forEach(item => {
                item.layer.ctx.save();
                applyPerspectiveWarpToLayer(item.layer.ctx, item.canvas, perspCorners);
                item.layer.ctx.restore();
            });
        } else if (isImportingNewImage) {
            if (pasteInNewLayer && !isModifyingShape) {
                const lCanvas = document.createElement('canvas'); lCanvas.width = paperWidth; lCanvas.height = paperHeight;
                const lCtx = lCanvas.getContext('2d', { willReadFrequently: true });
                applyPerspectiveWarpToLayer(lCtx, modSelCanvas, perspCorners);
                const newLayer = { id: Date.now(), name: 'Imagen Importada', canvas: lCanvas, ctx: lCtx, visible: true, opacity: 1.0, thumbData: '', alphaLocked: false, clippingMask: false, blendMode: 'source-over' };
                layers.splice(selectedLayerIndex + 1, 0, newLayer); selectedLayerIndex++;
            } else {
                const target = layers[selectedLayerIndex].ctx;
                target.save();
                if (layers[selectedLayerIndex].alphaLocked) target.globalCompositeOperation = 'source-atop';
                applyPerspectiveWarpToLayer(target, modSelCanvas, perspCorners);
                target.restore();
            }
            isImportingNewImage = false;
        }
        // Reset perspective state
        modSelPerspectiveMode = false; perspCorners = null;
        if (perspBtn) { perspBtn.style.background = 'rgba(30,30,40,0.9)'; perspBtn.style.boxShadow = ''; }
        modSelInitialized = false; modSelCanvas = null; modSelBounds = null; modSelOrigBounds = null;
        modSelRotation = 0; modSelFlipX = 1; modSelFlipY = 1; modSelLayersData = [];
        if (flipControls) flipControls.classList.add('hidden');
        updateThumbnails(); updateLayersUI(); pushHistory();
        return;
    }

    if (isImportingNewImage) {
        if (pasteInNewLayer && !isModifyingShape) {
            // Create the new layer for the imported image
            const lCanvas = document.createElement('canvas');
            lCanvas.width = paperWidth; lCanvas.height = paperHeight;
            const lCtx = lCanvas.getContext('2d', { willReadFrequently: true });

            const b = modSelBounds;
            lCtx.save();
            lCtx.imageSmoothingEnabled = true;
            lCtx.imageSmoothingQuality = 'high';
            const cx = b.x + b.w / 2;
            const cy = b.y + b.h / 2;
            lCtx.translate(cx, cy);
            lCtx.rotate(modSelRotation);
            lCtx.scale(modSelFlipX, modSelFlipY);
            lCtx.translate(-cx, -cy);
            lCtx.drawImage(modSelCanvas, Math.round(b.x), Math.round(b.y), Math.round(b.w), Math.round(b.h));
            lCtx.restore();

            const newLayer = {
                id: Date.now(),
                name: "Imagen Importada",
                canvas: lCanvas,
                ctx: lCtx,
                visible: true,
                opacity: 1.0,
                thumbData: '',
                alphaLocked: false,
                clippingMask: false,
                blendMode: 'source-over'
            };
            layers.splice(selectedLayerIndex + 1, 0, newLayer);
            selectedLayerIndex++;
        } else {
            // Draw directly onto the current active layer
            const target = layers[selectedLayerIndex].ctx;
            const b = modSelBounds;
            target.save();
            target.imageSmoothingEnabled = true;
            target.imageSmoothingQuality = 'high';
            if (layers[selectedLayerIndex].alphaLocked) target.globalCompositeOperation = 'source-atop';
            const cx = b.x + b.w / 2;
            const cy = b.y + b.h / 2;
            target.translate(cx, cy);
            target.rotate(modSelRotation);
            target.scale(modSelFlipX, modSelFlipY);
            target.translate(-cx, -cy);
            target.drawImage(modSelCanvas, Math.round(b.x), Math.round(b.y), Math.round(b.w), Math.round(b.h));
            target.restore();
        }
        isImportingNewImage = false;
    } else {
        if (modSelLayersData.length === 0) return;
        const b = modSelBounds;
        modSelLayersData.forEach(item => {
            const target = item.layer.ctx;
            target.save();
            target.imageSmoothingEnabled = true;
            target.imageSmoothingQuality = 'high';
            const cx = b.x + b.w / 2;
            const cy = b.y + b.h / 2;
            target.translate(cx, cy);
            target.rotate(modSelRotation);
            target.scale(modSelFlipX, modSelFlipY);
            target.translate(-cx, -cy);
            target.drawImage(item.canvas, Math.round(b.x), Math.round(b.y), Math.round(b.w), Math.round(b.h));
            target.restore();
        });
    }

    modSelInitialized = false; modSelCanvas = null; modSelBounds = null; modSelOrigBounds = null;
    modSelRotation = 0; modSelFlipX = 1; modSelFlipY = 1;
    modSelLayersData = [];
    if (flipControls) flipControls.classList.add('hidden');
    updateThumbnails(); updateLayersUI();
    pushHistory();
    
    if (isModifyingShape) {
        isModifyingShape = false;
        selectTool('pincel', 'Pincel');
    }
}

// ─────────────────────────────────────────────────────────────
