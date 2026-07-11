// (Elimina temblor de alta frecuencia sin dejar lados rectos)
function smoothLassoPath(pts, passes) {
    if (pts.length <= 3) return pts;
    let p = pts;
    for (let iter = 0; iter < passes; iter++) {
        const s = [p[0]]; // preservar primer punto
        for (let i = 1; i < p.length - 1; i++) {
            s.push({
                x: p[i - 1].x * 0.25 + p[i].x * 0.5 + p[i + 1].x * 0.25,
                y: p[i - 1].y * 0.25 + p[i].y * 0.5 + p[i + 1].y * 0.25
            });
        }
        s.push(p[p.length - 1]); // preservar último punto
        p = s;
    }
    return p;
}

function smoothStrokePath(pts, passes) {
    if (pts.length <= 3) return pts;
    let p = pts;
    for (let iter = 0; iter < passes; iter++) {
        const s = [p[0]]; // preservar primer punto
        for (let i = 1; i < p.length - 1; i++) {
            s.push({
                x: p[i - 1].x * 0.25 + p[i].x * 0.5 + p[i + 1].x * 0.25,
                y: p[i - 1].y * 0.25 + p[i].y * 0.5 + p[i + 1].y * 0.25,
                p: p[i - 1].p * 0.25 + p[i].p * 0.5 + p[i + 1].p * 0.25
            });
        }
        s.push(p[p.length - 1]); // preservar último punto
        p = s;
    }
    return p;
}

function executeLassoFill() {
    if (lassoPath.length < 3) return;
    // Pasadas adaptativas: a menos zoom más suavizado para compensar el temblor amplificado
    const passes = Math.round(Math.min(24, Math.max(1, 3 / viewScale)));
    const smoothPath = smoothLassoPath(lassoPath, passes);
    if (smoothPath.length < 3) return;
    const l = layers[selectedLayerIndex]; l.ctx.save();
    if (currentBrush.isEraser) l.ctx.globalCompositeOperation = 'destination-out';
    else if (l.alphaLocked) l.ctx.globalCompositeOperation = 'source-atop';
    l.ctx.globalAlpha = brushOpacity; l.ctx.fillStyle = selectedColor;
    l.ctx.beginPath(); l.ctx.moveTo(smoothPath[0].x, smoothPath[0].y);
    smoothPath.forEach(p => l.ctx.lineTo(p.x, p.y)); l.ctx.closePath(); l.ctx.fill(); l.ctx.restore();
}
function drawPoint(x, y, pressure) {
    // Pressure: sensitivity 0-2.0, scaled so at 2.0 range is ~0% to 300% of base size
    const minScale = Math.max(0.01, 1.0 - (0.9 * pressureSensitivity));
    const maxScale = 1.0 + (1.5 * pressureSensitivity);
    
    // Apply an exponential curve so light pressure stays thin, and hard pressure grows rapidly
    const curvedPressure = Math.pow(pressure, 2.5);
    
    let size = baseBrushSize * (minScale + curvedPressure * (maxScale - minScale));
    let localOpacity = brushOpacity;

    if (currentBrush.isGaussBlur) {
        size = baseBrushSize;
        localOpacity = brushOpacity;
    }

    // Velocity size modulation
    if (velocitySensitivity > 0 && !currentBrush.isGaussBlur) {
        // Sqrt curve: smooth transitions, avoids harsh jumps at low speeds
        const normalised = Math.min(1.0, Math.sqrt(lastPointerSpeed / 2.5));
        // 'slow' mode: slow→thick (default). 'fast' mode: fast→thick (inverted)
        const factor = velocityMode === 'slow'
            ? (1.0 - velocitySensitivity * normalised * 0.82)
            : (1.0 - velocitySensitivity * (1.0 - normalised) * 0.82);
        size *= Math.max(0.05, factor);
    }
    size = Math.max(0.05, size);
    if (size <= 0) return;
    const l = layers[selectedLayerIndex];

    if (currentBrush.isBlur) {
        l.ctx.save();
        const side = Math.ceil(size * 2);
        if (side < 1) { l.ctx.restore(); return; }

        if (brushMaskCanvas.width < side || brushMaskCanvas.height < side) {
            brushMaskCanvas.width = side + 20; brushMaskCanvas.height = side + 20;
            blurTempCanvas.width = side + 20; blurTempCanvas.height = side + 20;
            bleedCanvas.width = side + 20; bleedCanvas.height = side + 20;
        }

        // 1. Capture current area
        blurTempCtx.clearRect(0, 0, side, side);
        blurTempCtx.drawImage(l.canvas, x - side / 2, y - side / 2, side, side, 0, 0, side, side);

        // 2. Perform Blur directly into bleedCanvas (without opacity-boosting bleed hacks)
        bleedCtx.clearRect(0, 0, side, side);
        const samples = 6;
        const radius = Math.max(1, currentBrush.blur / 6);
        bleedCtx.globalAlpha = 1 / samples;
        for (let i = 0; i < samples; i++) {
            const ang = (i / samples) * Math.PI * 2;
            bleedCtx.drawImage(blurTempCanvas, Math.cos(ang) * radius, Math.sin(ang) * radius);
        }
        bleedCtx.globalAlpha = 1.0;

        // 3. Create the Mask in brushMaskCanvas
        brushMaskCtx.clearRect(0, 0, side, side);
        if (currentBrush.useTexture && tintedAirbrushCanvas) {
            brushMaskCtx.drawImage(tintedAirbrushCanvas, 0, 0, side, side);
        } else {
            const g = brushMaskCtx.createRadialGradient(side / 2, side / 2, (side / 2) * currentBrush.hardness, side / 2, side / 2, side / 2);
            g.addColorStop(0, 'white'); g.addColorStop(1, 'rgba(255,255,255,0)');
            brushMaskCtx.fillStyle = g; brushMaskCtx.fillRect(0, 0, side, side);
        }

        // Apply brush opacity to the mask itself
        brushMaskCtx.globalCompositeOperation = 'destination-in';
        brushMaskCtx.fillStyle = `rgba(255, 255, 255, ${localOpacity})`;
        brushMaskCtx.fillRect(0, 0, side, side);
        brushMaskCtx.globalCompositeOperation = 'source-over';

        // 4. Mask the Blurred image
        bleedCtx.globalCompositeOperation = 'destination-in';
        bleedCtx.drawImage(brushMaskCanvas, 0, 0);
        bleedCtx.globalCompositeOperation = 'source-over';

        // 5. Update Layer using correct interpolation
        if (l.alphaLocked) {
            l.ctx.globalCompositeOperation = 'source-atop';
            l.ctx.drawImage(bleedCanvas, 0, 0, side, side, x - side / 2, y - side / 2, side, side);
        } else {
            l.ctx.globalCompositeOperation = 'destination-out';
            l.ctx.drawImage(brushMaskCanvas, 0, 0, side, side, x - side / 2, y - side / 2, side, side);
            l.ctx.globalCompositeOperation = 'lighter';
            l.ctx.drawImage(bleedCanvas, 0, 0, side, side, x - side / 2, y - side / 2, side, side);
        }
        l.ctx.restore();
    }
    else if (currentBrush.isGaussBlur && blurBuffer) {
        l.ctx.save();

        const side = Math.ceil(size * 2);
        if (side < 1) { l.ctx.restore(); return; }

        if (brushMaskCanvas.width < side || brushMaskCanvas.height < side) {
            brushMaskCanvas.width = side + 20; brushMaskCanvas.height = side + 20;
            bleedCanvas.width = side + 20; bleedCanvas.height = side + 20;
        }

        // 1. Get blurred area from global blur buffer
        bleedCtx.clearRect(0, 0, side, side);
        bleedCtx.drawImage(blurBuffer, x - side / 2, y - side / 2, side, side, 0, 0, side, side);

        // 2. Create mask
        brushMaskCtx.clearRect(0, 0, side, side);
        if (currentBrush.useTexture && tintedAirbrushCanvas) {
            brushMaskCtx.drawImage(tintedAirbrushCanvas, 0, 0, side, side);
        } else {
            const g = brushMaskCtx.createRadialGradient(side / 2, side / 2, (side / 2) * currentBrush.hardness, side / 2, side / 2, side / 2);
            g.addColorStop(0, 'white'); g.addColorStop(1, 'rgba(255,255,255,0)');
            brushMaskCtx.fillStyle = g; brushMaskCtx.fillRect(0, 0, side, side);
        }

        // Apply brush opacity to mask
        brushMaskCtx.globalCompositeOperation = 'destination-in';
        brushMaskCtx.fillStyle = `rgba(255, 255, 255, ${localOpacity})`;
        brushMaskCtx.fillRect(0, 0, side, side);
        brushMaskCtx.globalCompositeOperation = 'source-over';

        // 3. Mask the blurred image
        bleedCtx.globalCompositeOperation = 'destination-in';
        bleedCtx.drawImage(brushMaskCanvas, 0, 0);
        bleedCtx.globalCompositeOperation = 'source-over';

        // 4. Update Layer
        if (l.alphaLocked) {
            l.ctx.globalCompositeOperation = 'source-atop';
            l.ctx.drawImage(bleedCanvas, 0, 0, side, side, x - side / 2, y - side / 2, side, side);
        } else {
            l.ctx.globalCompositeOperation = 'destination-out';
            l.ctx.drawImage(brushMaskCanvas, 0, 0, side, side, x - side / 2, y - side / 2, side, side);
            l.ctx.globalCompositeOperation = 'lighter';
            l.ctx.drawImage(bleedCanvas, 0, 0, side, side, x - side / 2, y - side / 2, side, side);
        }
        l.ctx.restore();
    }
    else if (currentBrush.isSmudge && smudgeBuffer) {
        l.ctx.save();

        const side = Math.ceil(size * 2.5);
        if (side < 1) { l.ctx.restore(); return; }

        if (brushMaskCanvas.width < side || brushMaskCanvas.height < side) {
            brushMaskCanvas.width = side + 20; brushMaskCanvas.height = side + 20;
            bleedCanvas.width = side + 20; bleedCanvas.height = side + 20;
        }

        // 1. Prepare the smudge tip in bleedCanvas
        bleedCtx.clearRect(0, 0, side, side);
        bleedCtx.drawImage(smudgeBuffer, 0, 0, smudgeBuffer.width, smudgeBuffer.height, 0, 0, side, side);

        // 2. Create mask
        brushMaskCtx.clearRect(0, 0, side, side);
        if (currentBrush.useTexture && tintedAirbrushCanvas) {
            brushMaskCtx.drawImage(tintedAirbrushCanvas, 0, 0, side, side);
        } else {
            const g = brushMaskCtx.createRadialGradient(side / 2, side / 2, (side / 2) * currentBrush.hardness, side / 2, side / 2, side / 2);
            g.addColorStop(0, 'white'); g.addColorStop(1, 'rgba(255,255,255,0)');
            brushMaskCtx.fillStyle = g; brushMaskCtx.fillRect(0, 0, side, side);
        }

        // Apply brush opacity to mask
        brushMaskCtx.globalCompositeOperation = 'destination-in';
        brushMaskCtx.fillStyle = `rgba(255, 255, 255, ${localOpacity})`;
        brushMaskCtx.fillRect(0, 0, side, side);
        brushMaskCtx.globalCompositeOperation = 'source-over';

        // 3. Mask the smudge tip
        bleedCtx.globalCompositeOperation = 'destination-in';
        bleedCtx.drawImage(brushMaskCanvas, 0, 0);
        bleedCtx.globalCompositeOperation = 'source-over';

        // 4. Update Layer
        if (l.alphaLocked) {
            l.ctx.globalCompositeOperation = 'source-atop';
            l.ctx.drawImage(bleedCanvas, 0, 0, side, side, x - side / 2, y - side / 2, side, side);
        } else {
            l.ctx.globalCompositeOperation = 'destination-out';
            l.ctx.drawImage(brushMaskCanvas, 0, 0, side, side, x - side / 2, y - side / 2, side, side);
            l.ctx.globalCompositeOperation = 'lighter';
            l.ctx.drawImage(bleedCanvas, 0, 0, side, side, x - side / 2, y - side / 2, side, side);
        }

        // 5. Update smudge buffer (intelligent pick up, without opacity-boosting bleed hacks)
        const sctx = smudgeBuffer.getContext('2d');
        blurTempCtx.clearRect(0, 0, side, side);
        blurTempCtx.drawImage(l.canvas, x - side / 2, y - side / 2, side, side, 0, 0, side, side);

        sctx.globalAlpha = 0.12;
        sctx.globalCompositeOperation = 'source-atop';
        sctx.drawImage(blurTempCanvas, 0, 0, side, side, 0, 0, smudgeBuffer.width, smudgeBuffer.height);
        sctx.globalCompositeOperation = 'source-over';

        sctx.globalAlpha = 0.02;
        sctx.drawImage(blurTempCanvas, 0, 0, side, side, 0, 0, smudgeBuffer.width, smudgeBuffer.height);

        l.ctx.restore();
    }
    else {
        const isHardSolid = !currentBrush.useTexture && !currentBrush.isBlur && !currentBrush.isSmudge && currentBrush.hardness >= 0.8 && !currentBrush.isLasso && !currentBrush.isShape;
        if (isHardSolid) {
            const ctx = (currentBrush.useCompositing || isPostStrokePreview) ? sctx : l.ctx;
            ctx.save();
            if (currentBrush.isEraser && !currentBrush.useCompositing && !isPostStrokePreview) ctx.globalCompositeOperation = 'destination-out';
            else if (!currentBrush.useCompositing && l.alphaLocked && !isPostStrokePreview) ctx.globalCompositeOperation = 'source-atop';
            if (!currentBrush.useCompositing) ctx.globalAlpha = localOpacity;
            else ctx.globalAlpha = 1.0;
            ctx.fillStyle = selectedColor;
            ctx.beginPath();
            ctx.arc(x, y, size, 0, Math.PI * 2);
            ctx.fill();
            ctx.restore();
        }
        else if (currentBrush.useCompositing) { sctx.save(); renderStamp(sctx, x, y, size, 1.0); sctx.restore(); }
        else { 
            const ctx = isPostStrokePreview ? sctx : l.ctx;
            ctx.save(); 
            if (currentBrush.isEraser && !currentBrush.useCompositing && !isPostStrokePreview) ctx.globalCompositeOperation = 'destination-out'; 
            else if (l.alphaLocked && !isPostStrokePreview) ctx.globalCompositeOperation = 'source-atop'; 
            renderStamp(ctx, x, y, size, localOpacity * 0.4); 
            ctx.restore(); 
        }
    }
}

