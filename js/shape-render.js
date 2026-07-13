/**
 * Constrain endpoint: line → 45° snap, rect/ellipse → equal sides
 */
function constrainShape(x1, y1, x2, y2) {
    const type = currentBrush.shapeType;
    if (type === 'line') {
        const dx = x2 - x1, dy = y2 - y1;
        const angle = Math.atan2(dy, dx);
        const snapped = Math.round(angle / (Math.PI / 4)) * (Math.PI / 4);
        const dist = Math.hypot(dx, dy);
        return [x1 + Math.cos(snapped) * dist, y1 + Math.sin(snapped) * dist];
    } else {
        const dx = x2 - x1, dy = y2 - y1;
        const side = Math.min(Math.abs(dx), Math.abs(dy));
        return [x1 + Math.sign(dx) * side, y1 + Math.sign(dy) * side];
    }
}

/**
 * Draw the current shape into a given context (used for live preview on strokeCanvas)
 */
function drawShapeOnCtx(tctx, x1, y1, x2, y2) {
    const type = currentBrush.shapeType;
    tctx.save();
    tctx.strokeStyle = selectedColor;
    tctx.fillStyle = selectedColor;
    tctx.lineWidth = Math.max(1, baseBrushSize);
    tctx.lineCap = 'round';
    tctx.lineJoin = 'round';

    if (type === 'line') {
        tctx.beginPath();
        tctx.moveTo(x1, y1);
        tctx.lineTo(x2, y2);
        tctx.stroke();
    } else if (type === 'rect') {
        let rx, ry, rw, rh;
        if (shapeFromCenterRect) {
            rw = Math.abs(x2 - x1) * 2;
            rh = Math.abs(y2 - y1) * 2;
            rx = x1 - rw / 2;
            ry = y1 - rh / 2;
        } else {
            rx = Math.min(x1, x2);
            ry = Math.min(y1, y2);
            rw = Math.abs(x2 - x1);
            rh = Math.abs(y2 - y1);
        }
        if (rw < 1 || rh < 1) { tctx.restore(); return; }
        if (shapeFill) tctx.fillRect(rx, ry, rw, rh);
        else tctx.strokeRect(rx, ry, rw, rh);
    } else if (type === 'ellipse') {
        let cx, cy, radiusX, radiusY;
        if (shapeFromCenterCircle) {
            cx = x1; cy = y1;
            radiusX = Math.max(1, Math.abs(x2 - x1));
            radiusY = Math.max(1, Math.abs(y2 - y1));
        } else {
            cx = (x1 + x2) / 2; cy = (y1 + y2) / 2;
            radiusX = Math.max(1, Math.abs(x2 - x1) / 2);
            radiusY = Math.max(1, Math.abs(y2 - y1) / 2);
        }
        tctx.beginPath();
        tctx.ellipse(cx, cy, radiusX, radiusY, 0, 0, Math.PI * 2);
        if (shapeFill) tctx.fill();
        else tctx.stroke();
    }
    tctx.restore();
}
function updateTintedTexture() {
    const indicator = document.getElementById('color-preview-btn-indicator');
    if (indicator) indicator.style.backgroundColor = selectedColor;

    if (!airbrushTexture) return;
    tintedAirbrushCanvas.width = airbrushTexture.width;
    tintedAirbrushCanvas.height = airbrushTexture.height;
    tactx.clearRect(0, 0, tintedAirbrushCanvas.width, tintedAirbrushCanvas.height);

    tactx.save();
    // Soft airbrush still uses the noise texture, but we can apply its own blur if desired.
    // However, the user said the blur slider also affects the ghost layer.
    // We'll keep the baked blur at 0 for the texture itself to avoid double-blurring
    // if the ghost layer is already blurred.
    tactx.drawImage(airbrushTexture, 0, 0);
    tactx.restore();

    tactx.globalCompositeOperation = 'source-in';

    tactx.fillStyle = selectedColor;
    tactx.fillRect(0, 0, tintedAirbrushCanvas.width, tintedAirbrushCanvas.height);
    requestRender();
}
function renderStamp(tctx, x, y, size, alpha) {
    if (currentBrush.useTexture && airbrushTexture) {
        tctx.save();
        tctx.globalAlpha = alpha;
        tctx.drawImage(tintedAirbrushCanvas, x - size, y - size, size * 2, size * 2);
        tctx.restore();
    }
    else { const g = tctx.createRadialGradient(x, y, size * currentBrush.hardness, x, y, size); g.addColorStop(0, hexToRgba(selectedColor, alpha)); g.addColorStop(1, hexToRgba(selectedColor, 0)); tctx.fillStyle = g; tctx.beginPath(); tctx.arc(x, y, size, 0, Math.PI * 2); tctx.fill(); }
}

function stabilizePoint(x, y, p, strength) {
    if (strength <= 0) return { x, y, p, ready: true };
    stabPoints.push({ x, y, p });
    if (stabPoints.length <= strength) return null;
    const out = stabPoints.shift();
    let ax = out.x, ay = out.y, ap = out.p;
    for (let i = 0; i < stabPoints.length; i++) {
        ax += stabPoints[i].x;
        ay += stabPoints[i].y;
        ap += stabPoints[i].p;
    }
    const n = stabPoints.length + 1;
    ax /= n; ay /= n; ap /= n;
    const blend = Math.min(1, strength / 20);
    return {
        x: out.x * (1 - blend * 0.6) + ax * (blend * 0.6),
        y: out.y * (1 - blend * 0.6) + ay * (blend * 0.6),
        p: out.p * (1 - blend * 0.4) + ap * (blend * 0.4),
        ready: true
    };
}

function drawStabLineTo(sx, sy, sp, ex, ey, ep) {
    const isHardSolid = !currentBrush.useTexture && !currentBrush.isBlur && !currentBrush.isSmudge && currentBrush.hardness >= 0.8 && !currentBrush.isLasso && !currentBrush.isShape;
    
    if (isHardSolid) {
        const avgPressure = (sp + ep) / 2;
        const curvedPressure = Math.pow(avgPressure, 2.5);
        const minScale = Math.max(0.01, 1.0 - (0.9 * pressureSensitivity));
        const maxScale = 1.0 + (1.5 * pressureSensitivity);
        let size = baseBrushSize * (minScale + curvedPressure * (maxScale - minScale));
        // Velocity size modulation
        if (velocitySensitivity > 0) {
            const normalised = Math.min(1.0, Math.sqrt(lastPointerSpeed / 2.5));
            const factor = velocityMode === 'slow'
                ? (1.0 - velocitySensitivity * normalised * 0.82)
                : (1.0 - velocitySensitivity * (1.0 - normalised) * 0.82);
            size *= Math.max(0.05, factor);
        }
        size = Math.max(0.05, size);
        if (size <= 0) return;
        const l = layers[selectedLayerIndex];
        const ctx = (currentBrush.useCompositing || isPostStrokePreview) ? sctx : l.ctx;
        
        ctx.save();
        if (currentBrush.isEraser && !currentBrush.useCompositing && !isPostStrokePreview) ctx.globalCompositeOperation = 'destination-out';
        else if (!currentBrush.useCompositing && l.alphaLocked && !isPostStrokePreview) ctx.globalCompositeOperation = 'source-atop';
        
        if (!currentBrush.useCompositing) ctx.globalAlpha = brushOpacity;
        else ctx.globalAlpha = 1.0;
        
        ctx.strokeStyle = selectedColor;
        ctx.lineWidth = size * 2;
        ctx.lineCap = 'round';
        ctx.lineJoin = 'round';
        
        ctx.beginPath();
        ctx.moveTo(sx, sy);
        ctx.lineTo(ex, ey);
        ctx.stroke();
        ctx.restore();
        return;
    }

    const dist = Math.hypot(ex - sx, ey - sy);
    const step = Math.max(0.2, baseBrushSize * 0.5 * brushSpacing);
    const steps = Math.floor(dist / step);
    for (let i = 0; i <= steps; i++) {
        const t = steps === 0 ? 1 : i / steps;
        drawPoint(sx + (ex - sx) * t, sy + (ey - sy) * t, sp + (ep - sp) * t);
    }
}



function hexToRgba(hex, alpha) { const r = parseInt(hex.slice(1, 3), 16), g = parseInt(hex.slice(3, 5), 16), b = parseInt(hex.slice(5, 7), 16); return `rgba(${r},${g},${b},${alpha})`; }

// ─────────────────────────────────────────────────────────────
//  RENDER LOOP
// ─────────────────────────────────────────────────────────────
function drawLayerContent(targetCtx, layerObj) {
    targetCtx.drawImage(layerObj.canvas, 0, 0);
    if (currentTool === 'modify-sel' && modSelInitialized && !isImportingNewImage) {
        const tItem = modSelLayersData.find(x => x.layer === layerObj);
        if (tItem) {
            if (modSelPerspectiveMode && perspCorners) {
                renderPerspectiveWarpPreview(targetCtx, tItem.canvas, perspCorners);
            } else {
                const b = modSelBounds;
                const cx = b.x + b.w / 2;
                const cy = b.y + b.h / 2;
                targetCtx.save();
                targetCtx.imageSmoothingEnabled = true;
                targetCtx.imageSmoothingQuality = 'high';
                targetCtx.translate(cx, cy);
                targetCtx.rotate(modSelRotation);
                targetCtx.scale(modSelFlipX, modSelFlipY);
                targetCtx.translate(-cx, -cy);
                targetCtx.drawImage(tItem.canvas, b.x, b.y, b.w, b.h);
                targetCtx.restore();
            }
        }
    }
}


