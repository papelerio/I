function render() {
    renderRequested = false;
    const isPreviewing = isDrawing && (currentBrush.useCompositing || isPostStrokePreview) && !currentBrush.isLasso && !activeFilterType;
    ctx.clearRect(0, 0, canvas.width, canvas.height); ctx.save();
    ctx.imageSmoothingEnabled = imageSmoothing;
    ctx.imageSmoothingQuality = imageSmoothing ? 'high' : 'low';
    ctx.translate(canvas.width / 2 + viewPosX, canvas.height / 2 + viewPosY);
    ctx.rotate(viewRotation); ctx.scale(viewScale, viewScale);
    ctx.translate(-paperWidth / 2, -paperHeight / 2);

    // Paper bg
    ctx.save(); ctx.shadowColor = 'rgba(0,0,0,0.5)'; ctx.shadowBlur = 40; ctx.shadowOffsetX = 10; ctx.shadowOffsetY = 20;
    if (activeFilterType === 'chroma' && chromaDebugBG) {
        ctx.fillStyle = chromaDebugBG;
    } else {
        if (bgMode === 1) ctx.fillStyle = solidBgColor;
        else if (bgMode === 2) ctx.fillStyle = checkerPatternDark;
        else ctx.fillStyle = checkerPatternLight;
    }
    ctx.fillRect(0, 0, paperWidth, paperHeight); ctx.restore();

    // Layers
    let activeGroupStart = selectedLayerIndex;
    while (activeGroupStart > 0 && layers[activeGroupStart].clippingMask) {
        activeGroupStart--;
    }

    if (activeGroupStart > 0) {
        updateLayersCache(activeGroupStart);
        ctx.drawImage(layersCacheCanvas, 0, 0);
    }

    let i = activeGroupStart;
    while (i < layers.length) {
        const l = layers[i];

        // Check if there are layers above clipping to this one
        let next = i + 1;
        let groupCount = 0;
        while (next < layers.length && layers[next].clippingMask) {
            next++;
            groupCount++;
        }

        if (groupCount > 0) {
            // We have a clipping group starting at index i
            let group = [l];
            for (let k = i + 1; k < next; k++) {
                if (layers[k].visible) group.push(layers[k]);
            }

            // If the base layer is invisible, the whole clipped stack is invisible
            if (!l.visible) {
                i = next;
                continue;
            }

            // Live stroke preview inside a clipping group
            const actInGrp = group.findIndex(layer => layer === layers[selectedLayerIndex]);

            gctx.clearRect(0, 0, paperWidth, paperHeight);
            
            // Draw the base layer (group[0] = CAPA B)
            if (actInGrp === 0 && isPreviewing) {
                mctx.clearRect(0, 0, paperWidth, paperHeight);
                mctx.globalCompositeOperation = 'source-over';
                drawLayerContent(mctx, group[0]);
                
                mctx.save();
                mctx.globalAlpha = currentBrush.useCompositing ? brushOpacity : 1.0;
                if ((currentBrush.id === 'aero-duro' || currentBrush.id === 'aero-suave') && currentBlur > 0) {
                    mctx.filter = `blur(${currentBlur}px)`;
                }
                if (group[0].alphaLocked) mctx.globalCompositeOperation = 'source-atop';
                if (currentBrush.isEraser) mctx.globalCompositeOperation = 'destination-out';
                mctx.drawImage(strokeCanvas, 0, 0);
                mctx.restore();
                mctx.filter = 'none';

                gctx.save();
                gctx.globalAlpha = group[0].opacity;
                gctx.globalCompositeOperation = group[0].blendMode;
                gctx.drawImage(maskBuffer, 0, 0);
                gctx.restore();
            } else {
                gctx.save();
                gctx.globalAlpha = group[0].opacity;
                gctx.globalCompositeOperation = group[0].blendMode;
                drawLayerContent(gctx, group[0]);
                gctx.restore();
            }

            // For each clipping layer
            for (let k = 1; k < group.length; k++) {
                mctx.clearRect(0, 0, paperWidth, paperHeight);
                mctx.globalCompositeOperation = 'source-over';
                mctx.save();
                mctx.globalAlpha = group[k].opacity;
                drawLayerContent(mctx, group[k]);
                mctx.restore();

                if (actInGrp === k && isPreviewing) {
                    mctx.save();
                    mctx.globalAlpha = currentBrush.useCompositing ? brushOpacity : 1.0;
                    if ((currentBrush.id === 'aero-duro' || currentBrush.id === 'aero-suave') && currentBlur > 0) {
                        mctx.filter = `blur(${currentBlur}px)`;
                    }
                    if (group[k].alphaLocked) mctx.globalCompositeOperation = 'source-atop';
                    if (currentBrush.isEraser) mctx.globalCompositeOperation = 'destination-out';
                    mctx.drawImage(strokeCanvas, 0, 0);
                    mctx.restore();
                    mctx.filter = 'none';
                }

                mctx.globalCompositeOperation = 'destination-in';
                // Use the composite of base layer + transform for clipping mask
                drawLayerContent(mctx, group[0]);
                mctx.globalCompositeOperation = 'source-over'; // reset

                gctx.save();
                gctx.globalCompositeOperation = group[k].blendMode;
                gctx.drawImage(maskBuffer, 0, 0);
                gctx.restore();
            }

            ctx.drawImage(groupCanvas, 0, 0);
            i = next;
        } else {
            // No clipping mask, just normal render
            if (l.visible) {
                ctx.save();
                ctx.globalAlpha = l.opacity;
                ctx.globalCompositeOperation = l.blendMode;

                if (i === selectedLayerIndex && isPreviewing) {
                    mctx.clearRect(0, 0, paperWidth, paperHeight);
                    mctx.globalCompositeOperation = 'source-over';
                    drawLayerContent(mctx, l);

                    mctx.save();
                    mctx.globalAlpha = currentBrush.useCompositing ? brushOpacity : 1.0;
                    if ((currentBrush.id === 'aero-duro' || currentBrush.id === 'aero-suave') && currentBlur > 0) {
                        mctx.filter = `blur(${currentBlur}px)`;
                    }
                    if (l.alphaLocked) mctx.globalCompositeOperation = 'source-atop';
                    if (currentBrush.isEraser) mctx.globalCompositeOperation = 'destination-out';
                    mctx.drawImage(strokeCanvas, 0, 0);
                    mctx.restore();
                    mctx.filter = 'none';

                    ctx.drawImage(maskBuffer, 0, 0);
                } else {
                    drawLayerContent(ctx, l);
                }
                ctx.restore();
            }
            i++;
        }
    }

    // ── Canvas X-ray border (shown while modifying selection / pasting) ──
    if (currentTool === 'modify-sel' && modSelInitialized) {
        ctx.save();
        const dashLen = 10 / viewScale;
        const gapLen  = 7  / viewScale;
        const lw      = 2  / viewScale;

        // Outer glow: slightly thicker semi-transparent stroke for visibility on any bg
        ctx.strokeStyle = 'rgba(59,130,246,0.25)';
        ctx.lineWidth   = (lw + 4) / viewScale * viewScale; // keep in world units
        ctx.lineWidth   = (lw * 3);
        ctx.setLineDash([dashLen, gapLen]);
        ctx.lineDashOffset = 0;
        ctx.strokeRect(-0.5 / viewScale, -0.5 / viewScale,
                       paperWidth + 1 / viewScale, paperHeight + 1 / viewScale);

        // Sharp inner dashed blue line
        ctx.strokeStyle = '#3b82f6';
        ctx.lineWidth   = lw;
        ctx.setLineDash([dashLen, gapLen]);
        ctx.strokeRect(0, 0, paperWidth, paperHeight);

        // Corner markers: small solid squares at the four corners for extra clarity
        const m = 6 / viewScale; // marker half-size
        ctx.setLineDash([]);
        ctx.fillStyle = '#3b82f6';
        [[0, 0], [paperWidth, 0], [0, paperHeight], [paperWidth, paperHeight]].forEach(([cx, cy]) => {
            ctx.fillRect(cx - m, cy - m, m * 2, m * 2);
        });

        ctx.restore();
    }

    // ── Draw floating modify preview ──
    if (currentTool === 'modify-sel' && modSelInitialized && modSelCanvas && modSelBounds) {
        ctx.save();
        ctx.beginPath();
        ctx.rect(0, 0, paperWidth, paperHeight);
        ctx.clip();
        ctx.imageSmoothingEnabled = imageSmoothing;
        ctx.imageSmoothingQuality = imageSmoothing ? 'high' : 'low';

        if (modSelPerspectiveMode && perspCorners) {
            // ── Perspective warp preview using scanline rendering ──
            if (isImportingNewImage) {
                renderPerspectiveWarpPreview(ctx, modSelCanvas, perspCorners);
            }

            // Draw the quadrilateral outline
            ctx.restore();
            ctx.save();
            ctx.strokeStyle = '#ff00ff'; ctx.lineWidth = 2 / viewScale; ctx.setLineDash([]);
            ctx.beginPath();
            ctx.moveTo(perspCorners[0].x, perspCorners[0].y); // TL
            ctx.lineTo(perspCorners[1].x, perspCorners[1].y); // TR
            ctx.lineTo(perspCorners[3].x, perspCorners[3].y); // BR
            ctx.lineTo(perspCorners[2].x, perspCorners[2].y); // BL
            ctx.closePath();
            ctx.stroke();

            // Draw 4 corner handles
            const hr2 = HANDLE_R / viewScale;
            const cornerColors = ['#ff00ff', '#ff00ff', '#ff00ff', '#ff00ff'];
            perspCorners.forEach((c, ci) => {
                ctx.fillStyle = 'white'; ctx.beginPath(); ctx.arc(c.x, c.y, hr2, 0, Math.PI * 2); ctx.fill();
                ctx.strokeStyle = cornerColors[ci]; ctx.lineWidth = 2.5 / viewScale; ctx.stroke();
            });
            ctx.restore();
        } else {
            // ── Normal scale/rotate preview ──
            const b = modSelBounds;
            const cx = b.x + b.w / 2;
            const cy = b.y + b.h / 2;
            if (isImportingNewImage) {
                ctx.translate(cx, cy);
                ctx.rotate(modSelRotation);
                ctx.scale(modSelFlipX, modSelFlipY);
                ctx.translate(-cx, -cy);
                ctx.drawImage(modSelCanvas, b.x, b.y, b.w, b.h);
            }
            ctx.strokeStyle = '#ff00ff'; ctx.lineWidth = 2 / viewScale; ctx.setLineDash([]);
            ctx.strokeRect(b.x, b.y, b.w, b.h);
            ctx.restore();

            // ── Draw handles & rotation lever ──
            ctx.save();
            const hr = HANDLE_R / viewScale;
            const rotDist = 40 / viewScale;
            const topCenterX = b.x + b.w / 2;
            const topCenterY = b.y;
            const drawH = (hx, hy) => {
                const dx = hx - cx, dy = hy - cy;
                const rx = dx * Math.cos(modSelRotation) - dy * Math.sin(modSelRotation);
                const ry = dx * Math.sin(modSelRotation) + dy * Math.cos(modSelRotation);
                ctx.fillStyle = 'white'; ctx.beginPath(); ctx.arc(cx + rx, cy + ry, hr, 0, Math.PI * 2); ctx.fill();
                ctx.strokeStyle = '#ff00ff'; ctx.lineWidth = 2 / viewScale; ctx.setLineDash([]); ctx.stroke();
            };
            const dxL = topCenterX - rotDist * 0 - cx, dyL = topCenterY - rotDist - cy;
            const rxL = dxL * Math.cos(modSelRotation) - dyL * Math.sin(modSelRotation);
            const ryL = dxL * Math.sin(modSelRotation) + dyL * Math.cos(modSelRotation);
            const dxTC = topCenterX - cx, dyTC = topCenterY - cy;
            const rxTC = dxTC * Math.cos(modSelRotation) - dyTC * Math.sin(modSelRotation);
            const ryTC = dxTC * Math.sin(modSelRotation) + dyTC * Math.cos(modSelRotation);
            ctx.strokeStyle = '#ff00ff'; ctx.lineWidth = 2 / viewScale;
            ctx.beginPath(); ctx.moveTo(cx + rxTC, cy + ryTC); ctx.lineTo(cx + rxL, cy + ryL); ctx.stroke();
            ctx.fillStyle = '#ff00ff'; ctx.beginPath(); ctx.arc(cx + rxL, cy + ryL, hr * 1.2, 0, Math.PI * 2); ctx.fill();
            ctx.strokeStyle = 'white'; ctx.stroke();
            const handlePositions = [
                [b.x, b.y], [b.x + b.w / 2, b.y], [b.x + b.w, b.y],
                [b.x, b.y + b.h / 2], [b.x + b.w, b.y + b.h / 2],
                [b.x, b.y + b.h], [b.x + b.w / 2, b.y + b.h], [b.x + b.w, b.y + b.h],
            ];
            handlePositions.forEach(([hx, hy]) => drawH(hx, hy));
            ctx.restore();
        }

        // Update flip buttons position
        updateFlipButtonsPosition();
    } else {
        if (flipControls) flipControls.classList.add('hidden');
    }

    // ── Draw canvas resize preview ──
    if (isResizingCanvas) {
        const nw = resizePreviewW;
        const nh = resizePreviewH;

        let ox = 0, oy = 0;
        if (resizeLibre) {
            ox = resizeOffsetX;
            oy = resizeOffsetY;
        } else {
            const dw = nw - paperWidth;
            const dh = nh - paperHeight;
            const col = resizeAnchor[1]; // l, c, r
            const row = resizeAnchor[0]; // t, m, b
            if (col === 'c') ox = Math.round(dw / 2);
            else if (col === 'r') ox = dw;
            if (row === 'm') oy = Math.round(dh / 2);
            else if (row === 'b') oy = dh;
        }

        ctx.save();

        // Shadow zone: area that will be empty in new canvas (outside current content)
        ctx.fillStyle = 'rgba(0, 102, 255, 0.08)';
        ctx.fillRect(-ox, -oy, nw, nh);

        // Existing canvas position highlight (where old content will be)
        ctx.strokeStyle = 'rgba(0,0,0,0.2)';
        ctx.lineWidth = 1 / viewScale;
        ctx.setLineDash([4 / viewScale, 4 / viewScale]);
        ctx.strokeRect(-ox, -oy, nw, nh);

        // New canvas border (bold blue, animated-ish)
        ctx.strokeStyle = '#0066ff';
        ctx.lineWidth = 2 / viewScale;
        ctx.setLineDash([]);
        ctx.strokeRect(-ox, -oy, nw, nh);

        // Size label
        ctx.fillStyle = 'rgba(0, 102, 255, 0.9)';
        ctx.font = `bold ${14 / viewScale}px Outfit, sans-serif`;
        ctx.textAlign = 'center';
        ctx.fillText(`${nw} × ${nh}`, -ox + nw / 2, -oy - 8 / viewScale);

        // Handles on the new canvas boundary
        const hr = (HANDLE_R + 2) / viewScale;
        const handlePositions = [
            [-ox, -oy], [-ox + nw / 2, -oy], [-ox + nw, -oy],
            [-ox, -oy + nh / 2], [-ox + nw, -oy + nh / 2],
            [-ox, -oy + nh], [-ox + nw / 2, -oy + nh], [-ox + nw, -oy + nh],
        ];
        handlePositions.forEach(([hx, hy]) => {
            ctx.fillStyle = 'white';
            ctx.beginPath(); ctx.arc(hx, hy, hr, 0, Math.PI * 2); ctx.fill();
            ctx.strokeStyle = '#0066ff';
            ctx.lineWidth = 3 / viewScale; // Thicker border for "physical" feel
            ctx.setLineDash([]);
            ctx.stroke();
            // Inner dot for more detail
            ctx.fillStyle = '#0066ff';
            ctx.beginPath(); ctx.arc(hx, hy, hr * 0.4, 0, Math.PI * 2); ctx.fill();
        });

        ctx.restore();
    }

    // ── Draw lasso fill/erase preview ──
    if (isDrawing && currentBrush.isLasso && lassoPath.length > 1) {
        ctx.save();
        ctx.globalAlpha = brushOpacity * 0.5;
        ctx.fillStyle = currentBrush.isEraser ? 'rgba(255,0,0,0.4)' : selectedColor;
        ctx.beginPath(); ctx.moveTo(lassoPath[0].x, lassoPath[0].y); lassoPath.forEach(p => ctx.lineTo(p.x, p.y)); ctx.closePath(); ctx.fill();
        ctx.globalAlpha = 1.0; ctx.strokeStyle = currentBrush.lassoColor; ctx.lineWidth = 2 / viewScale; ctx.setLineDash([5 / viewScale, 5 / viewScale]);
        ctx.beginPath(); ctx.moveTo(lassoPath[0].x, lassoPath[0].y); lassoPath.forEach(p => ctx.lineTo(p.x, p.y)); ctx.closePath(); ctx.stroke();
        ctx.restore();
    }

    // ── Draw lasso selection stroke in progress ──
    if ((currentTool === 'lazo-sel' || currentTool === 'lazo-des') && isDrawing && lassoSelPath.length > 1) {
        ctx.save();
        ctx.fillStyle = currentTool === 'lazo-sel' ? 'rgba(255,0,255,0.15)' : 'rgba(255,0,0,0.15)';
        ctx.beginPath(); ctx.moveTo(lassoSelPath[0].x, lassoSelPath[0].y); lassoSelPath.forEach(p => ctx.lineTo(p.x, p.y)); ctx.closePath(); ctx.fill();
        ctx.strokeStyle = currentTool === 'lazo-sel' ? '#ff00ff' : '#ff0000';
        ctx.lineWidth = 2 / viewScale; ctx.setLineDash([5 / viewScale, 5 / viewScale]);
        ctx.beginPath(); ctx.moveTo(lassoSelPath[0].x, lassoSelPath[0].y); lassoSelPath.forEach(p => ctx.lineTo(p.x, p.y)); ctx.closePath(); ctx.stroke();
        ctx.restore();
    }

    // ── Draw persistent selection mask outline (static cached) ──
    if (hasSelection && selectionOutlineCanvas) {
        ctx.save();
        ctx.drawImage(selectionOutlineCanvas, 0, 0);
        ctx.restore();
    }

    // ── Draw filter lasso preview ──
    if (activeFilterType === 'chroma' && isDrawing && (chromaLassoMode === 'add' || chromaLassoMode === 'sub' || chromaLassoMode === 'clear') && lassoPath.length > 1) {
        ctx.save();
        ctx.globalAlpha = 0.5;
        if (chromaLassoMode === 'clear') {
            ctx.fillStyle = 'rgba(255, 255, 255, 0.4)';
            ctx.strokeStyle = '#607d8b';
        } else {
            ctx.fillStyle = chromaLassoMode === 'add' ? 'rgba(76, 175, 80, 0.4)' : 'rgba(244, 67, 54, 0.4)';
            ctx.strokeStyle = chromaLassoMode === 'add' ? '#4caf50' : '#f44336';
        }
        ctx.beginPath(); ctx.moveTo(lassoPath[0].x, lassoPath[0].y); lassoPath.forEach(p => ctx.lineTo(p.x, p.y)); ctx.closePath(); ctx.fill();
        ctx.lineWidth = 2 / viewScale; ctx.setLineDash([5 / viewScale, 5 / viewScale]);
        ctx.beginPath(); ctx.moveTo(lassoPath[0].x, lassoPath[0].y); lassoPath.forEach(p => ctx.lineTo(p.x, p.y)); ctx.closePath(); ctx.stroke();
        ctx.restore();
    }

    ctx.restore();

    // Rotation pivot dot
    if (currentTool === 'rotate' && isDrawing) {
        ctx.beginPath(); ctx.arc(rotationPivot.sx, rotationPivot.sy, 5, 0, Math.PI * 2);
        ctx.fillStyle = 'rgba(0,0,0,0.4)'; ctx.fill(); ctx.strokeStyle = 'white'; ctx.stroke();
    }
    // ── Software Cursor (Drawn in screen space) ──
    if (cursorMode === 'always' || (cursorMode === 'auto' && !isDrawing)) {
        const isBrush = (currentTool === 'pincel' || currentTool === 'push');
        if (isBrush) {
            const screenR = baseBrushSize * viewScale;
            ctx.beginPath();
            ctx.arc(screenCursorX, screenCursorY, screenR, 0, Math.PI * 2);
            ctx.strokeStyle = 'rgba(255,255,255,0.6)';
            ctx.lineWidth = 1.5;
            ctx.stroke();
            ctx.beginPath();
            ctx.arc(screenCursorX, screenCursorY, screenR, 0, Math.PI * 2);
            ctx.strokeStyle = 'rgba(0,0,0,0.2)';
            ctx.lineWidth = 0.5;
            ctx.stroke();
        }
        ctx.drawImage(customCursorImg, screenCursorX, screenCursorY);
    }
}

// ─────────────────────────────────────────────────────────────
