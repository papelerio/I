
function handlePointerDown(e) {
    if (e.target !== canvas) return;
    screenCursorX = e.offsetX; screenCursorY = e.offsetY;
    if (e.button !== 0 && e.button !== 1 && !isSpacePressed && e.pointerType === 'mouse') return;
    canvas.setPointerCapture(e.pointerId);
    isDrawing = true;
    applyCursor(true);
    sctx.clearRect(0, 0, strokeCanvas.width, strokeCanvas.height);
    lassoPath = []; lassoSelPath = [];
    lassoLastScreenX = null; lassoLastScreenY = null;
    const world = screenToWorld(e.offsetX, e.offsetY);

    // Filter Priority
    if (activeFilterType === 'chroma') {
        if (chromaLassoMode === 'pick') {
            const color = pickColorAt(world.x, world.y);
            if (color) {
                chromaKeyColor = color;
                const prev = document.getElementById('chroma-color-preview');
                if (prev) prev.style.background = color;
                const btn = document.getElementById('chroma-pick-btn');
                if (btn) btn.textContent = 'SELECCIONAR COLOR DEL LIENZO';
                chromaLassoMode = 'add';
                const addBtn = document.querySelector('.chroma-lasso-btn[data-mode="add"]');
                if (addBtn) {
                    document.querySelectorAll('.chroma-lasso-btn').forEach(b => b.style.boxShadow = '');
                    addBtn.style.boxShadow = '0 0 0 3px rgba(0,0,0,0.3) inset';
                }
                applyFilters();
            }
            requestRender();
            return;
        } else if (chromaLassoMode === 'add' || chromaLassoMode === 'sub' || chromaLassoMode === 'clear') {
            isDrawing = true;
            lassoPath = [{ x: world.x, y: world.y }];
            requestRender();
            return;
        }
        if (currentTool === 'zoom' || currentTool === 'pan' || e.button === 1 || isSpacePressed) { /* ok */ }
        else return;
    }

    if (e.button === 1 || isSpacePressed) {
        isTemporaryPan = true;
        currentTool = 'pan';
    } else {
        isTemporaryPan = false;
    }

    lastX = world.x; lastY = world.y;
    const rawP = (e.pressure === 0.5 && e.pointerType !== 'mouse') ? 0.1 : e.pressure || 0.1;
    lastPressure = rawP; smoothedPressure = rawP;

    if (currentTool === 'rotate') { rotationPivot = { sx: e.offsetX, sy: e.offsetY, startRotation: viewRotation }; }
    else if (currentTool === 'zoom') {
        const w = screenToWorld(e.offsetX, e.offsetY);
        if (w.x >= 0 && w.x <= paperWidth && w.y >= 0 && w.y <= paperHeight) {
            zoomPivotWorld = w;
            zoomPivotScreen = { x: e.offsetX, y: e.offsetY };
        } else {
            zoomPivotWorld = null;
            zoomPivotScreen = null;
        }
    }
    else if (isResizingCanvas) {
        const handle = getCanvasResizeHandle(world.x, world.y);
        if (handle) {
            resizeActiveHandle = handle;
            resizeStartMouse = { x: world.x, y: world.y };
            resizeStartDim = { w: resizePreviewW, h: resizePreviewH };
            resizeStartOffsetX = resizeOffsetX;
            resizeStartOffsetY = resizeOffsetY;
            canvas.setPointerCapture(e.pointerId);
        }
        isDrawing = false;
        e.preventDefault();
        requestRender();
        return;
    }
    else if (currentTool === 'bucket') { executeBucket(world.x, world.y); }
    else if (currentTool === 'eyedropper') {
        if (eyedropperFadeTimeout) { clearTimeout(eyedropperFadeTimeout); eyedropperFadeTimeout = null; }
        eyedropperPreview?.classList.remove('hidden', 'copied');
        updateEyedropperPreview(e.offsetX, e.offsetY, world.x, world.y);
        requestRender();
        return;
    }
    else if (currentTool === 'push') {
        isDrawing = true;
        canvas.setPointerCapture(e.pointerId);
        if (!pushSnapshot) {
            pushSnapshot = document.createElement('canvas');
            pushSnapshot.width = paperWidth;
            pushSnapshot.height = paperHeight;
            pushSnapshot.getContext('2d').drawImage(layers[selectedLayerIndex].canvas, 0, 0);
            pushSnapshotPixels = pushSnapshot.getContext('2d').getImageData(0, 0, paperWidth, paperHeight).data;
            pushDisplacementX = new Float32Array(paperWidth * paperHeight);
            pushDisplacementY = new Float32Array(paperWidth * paperHeight);
        }
    }

    else if (currentTool === 'lazo-sel' || currentTool === 'lazo-des') {
        lassoSelStartX = world.x; lassoSelStartY = world.y;
        if (lassoSelMode === 'libre') lassoSelPath = [{ x: world.x, y: world.y }];
        else lassoSelPath = squarePath(world.x, world.y, world.x, world.y);
    }
    else if (currentTool === 'modify-sel') {
        if (!modSelInitialized && hasSelection) initModifySelection();
        if (modSelInitialized) {
            const handle = getModifyHandle(world.x, world.y);
            if (handle) {
                modSelHandle = handle;
                modSelDragStart = { wx: world.x, wy: world.y };
                modSelOrigBounds = { ...modSelBounds };
                modSelActive = true;
                // Snapshot perspective corners for drag-delta computation
                if (modSelPerspectiveMode && perspCorners) {
                    perspDragStart = { wx: world.x, wy: world.y };
                    perspCornersAtDragStart = perspCorners.map(c => ({ ...c }));
                }
            }
        }
    }
    else if (currentTool === 'pincel') {
        if (currentBrush.isBlur) { blurBuffer = null; }
        else if (currentBrush.isGaussBlur) {
            blurBuffer = document.createElement('canvas');
            blurBuffer.width = paperWidth;
            blurBuffer.height = paperHeight;
            const bctx = blurBuffer.getContext('2d');
            bctx.filter = `blur(${currentBrush.blur}px)`;
            bctx.drawImage(layers[selectedLayerIndex].canvas, 0, 0);
        }
        else if (currentBrush.isSmudge) {
            const side = Math.ceil(baseBrushSize * 2.5);
            smudgeBuffer = document.createElement('canvas');
            smudgeBuffer.width = side; smudgeBuffer.height = side;
            const sctx = smudgeBuffer.getContext('2d');
            sctx.drawImage(layers[selectedLayerIndex].canvas, world.x - side / 2, world.y - side / 2, side, side, 0, 0, side, side);
        }

        if (currentBrush.isLasso) {
            lassoPath.push({ x: world.x, y: world.y });
            lassoLastScreenX = e.offsetX; lassoLastScreenY = e.offsetY;
        } else if (currentBrush.isShape) {
            shapeStartX = world.x; shapeStartY = world.y;
            sctx.clearRect(0, 0, strokeCanvas.width, strokeCanvas.height);
        } else {
            if (stabEnabled > 0 && stabMode === 'post' && !currentBrush.isLasso && !currentBrush.isShape && currentBrush.id !== 'push-brush' && !activeFilterType && !currentBrush.isGaussBlur && !currentBrush.isSmudge) {
                isPostStrokePreview = true;
                rawStrokePath = [{ x: lastX, y: lastY, p: smoothedPressure }];
            }

            if (stabEnabled > 0 && stabMode === 'realtime' && !currentBrush.isGaussBlur && !currentBrush.isSmudge) {
                stabPoints = [];
                stabOutX = null; stabOutY = null; stabOutP = null;
                stabPoints.push({ x: lastX, y: lastY, p: smoothedPressure });
            } else {
                drawPoint(lastX, lastY, smoothedPressure);
            }
        }
    }

    // Handle Chroma Filter picking
    if (activeFilterType === 'chroma' && chromaLassoMode === 'pick') {
        const color = pickColorAt(world.x, world.y);
        if (color) {
            chromaKeyColor = color;
            const prev = document.getElementById('chroma-color-preview');
            if (prev) prev.style.background = color;
            const btn = document.getElementById('chroma-pick-btn');
            if (btn) btn.textContent = 'SELECCIONAR COLOR DEL LIENZO';
            chromaLassoMode = 'none';
            applyFilters();
        }
    } else if (activeFilterType === 'chroma' && (chromaLassoMode === 'add' || chromaLassoMode === 'sub')) {
        lassoPath = [{ x: world.x, y: world.y }];
        isDrawing = true;
    }
    e.preventDefault();
    requestRender();
}

function handlePointerMove(e) {
    screenCursorX = e.offsetX; screenCursorY = e.offsetY;
    // Canvas resize drag is independent of isDrawing
    if (isResizingCanvas) {
        // Update cursor based on which handle is hovered
        if (!resizeActiveHandle) {
            const world2 = screenToWorld(e.offsetX, e.offsetY);
            const hov = getCanvasResizeHandle(world2.x, world2.y);
            const cursorMap = { tl: 'nwse-resize', tc: 'ns-resize', tr: 'nesw-resize', ml: 'ew-resize', mr: 'ew-resize', bl: 'nesw-resize', bc: 'ns-resize', br: 'nwse-resize', move: 'move' };
            canvas.style.cursor = hov ? (cursorMap[hov] || 'crosshair') : 'default';
        }
        if (resizeActiveHandle) {
            e.preventDefault();
            const world = screenToWorld(e.offsetX, e.offsetY);
            const dx = world.x - resizeStartMouse.x;
            const dy = world.y - resizeStartMouse.y;

            if (resizeActiveHandle === 'move') {
                resizeOffsetX -= dx;
                resizeOffsetY -= dy;
                resizeStartMouse = { x: world.x, y: world.y }; // update for next move
            } else {
                const res = applyCanvasResizeDrag(dx, dy, resizeActiveHandle, resizeStartDim.w, resizeStartDim.h);
                resizePreviewW = res.nw;
                resizePreviewH = res.nh;

                if (resizeLibre) {
                    // Update offsets to keep the correct edges pinned
                    // Since we already calculated res.dox/doy based on origW/H
                    // we need to add the incremental change or reset to start dim.
                    // To avoid accumulation errors, we use the diff from startDim.
                    resizeOffsetX = resizeStartOffsetX + res.dox;
                    resizeOffsetY = resizeStartOffsetY + res.doy;
                }

                // Sync back to inputs
                document.getElementById('resize-width').value = resizePreviewW;
                document.getElementById('resize-height').value = resizePreviewH;
            }
        }
        requestRender();
        return;
    }

    if (!isDrawing) {
        requestRender();
        return;
    }
    applyCursor(true); // Re-force cursor visibility during move to fight aggressive browser hiding
    e.preventDefault();
    const world = screenToWorld(e.offsetX, e.offsetY);

    if (currentTool === 'pan') { viewPosX += e.movementX; viewPosY += e.movementY; }
    else if (currentTool === 'push') {
        executePush(world.x, world.y, e.movementX / viewScale, e.movementY / viewScale);
    }
    else if (currentTool === 'zoom') {
        const oldScale = viewScale;
        viewScale *= 1 + e.movementY * -0.005;
        viewScale = Math.max(0.01, Math.min(20, viewScale));

        if (zoomPivotWorld && zoomPivotScreen) {
            // Zoom towards pivot
            const cos = Math.cos(viewRotation);
            const sin = Math.sin(viewRotation);
            const dx = (zoomPivotWorld.x - paperWidth / 2) * viewScale;
            const dy = (zoomPivotWorld.y - paperHeight / 2) * viewScale;
            const rdx = dx * cos - dy * sin;
            const rdy = dx * sin + dy * cos;

            viewPosX = zoomPivotScreen.x - canvas.width / 2 - rdx;
            viewPosY = zoomPivotScreen.y - canvas.height / 2 - rdy;
        }
    }
    else if (currentTool === 'rotate') { viewRotation = rotationPivot.startRotation + (e.offsetX - rotationPivot.sx) * 0.01; resetRotationBtn.classList.remove('hidden'); }
    else if (currentTool === 'lazo-sel' || currentTool === 'lazo-des') {
        if (lassoSelMode === 'libre') lassoSelPath.push({ x: world.x, y: world.y });
        else lassoSelPath = squarePath(lassoSelStartX, lassoSelStartY, world.x, world.y);
    }
    else if (currentTool === 'modify-sel' && modSelActive && modSelHandle) {
        if (modSelPerspectiveMode && perspCorners && modSelHandle.startsWith('pc')) {
            // Move a single perspective corner
            const ci = parseInt(modSelHandle[2]);
            const dx = world.x - modSelDragStart.wx;
            const dy = world.y - modSelDragStart.wy;
            perspCorners[ci].x = perspCornersAtDragStart[ci].x + dx;
            perspCorners[ci].y = perspCornersAtDragStart[ci].y + dy;
        } else if (modSelPerspectiveMode && perspCorners && modSelHandle === 'move') {
            // Move all corners together
            const dx = world.x - modSelDragStart.wx;
            const dy = world.y - modSelDragStart.wy;
            for (let ci = 0; ci < 4; ci++) {
                perspCorners[ci].x = perspCornersAtDragStart[ci].x + dx;
                perspCorners[ci].y = perspCornersAtDragStart[ci].y + dy;
            }
            // Keep modSelBounds centroid in sync for flip buttons positioning
            const mxs = perspCorners.map(c => c.x), mys = perspCorners.map(c => c.y);
            modSelBounds = { x: Math.min(...mxs), y: Math.min(...mys), w: Math.max(...mxs) - Math.min(...mxs), h: Math.max(...mys) - Math.min(...mys) };
        } else {
            const dx = world.x - modSelDragStart.wx; const dy = world.y - modSelDragStart.wy;
            modSelBounds = applyModifyDrag(dx, dy, modSelHandle, modSelOrigBounds, e.shiftKey, world.x, world.y);
        }
    }
    else if (currentTool === 'eyedropper') {
        updateEyedropperPreview(e.offsetX, e.offsetY, world.x, world.y);
    }
    else if (currentTool === 'pincel') {
        const [cX, cY] = [world.x, world.y];
        if (currentBrush.isLasso) {
            // Solo añade punto si el cursor se movió al menos 2px en pantalla (filtra micro-temblores)
            const dxScr = e.offsetX - (lassoLastScreenX ?? e.offsetX);
            const dyScr = e.offsetY - (lassoLastScreenY ?? e.offsetY);
            if (dxScr * dxScr + dyScr * dyScr >= 4) {
                lassoPath.push({ x: world.x, y: world.y });
                lassoLastScreenX = e.offsetX;
                lassoLastScreenY = e.offsetY;
            }
        } else if (currentBrush.isShape) {
            // Live preview: clear strokeCanvas and redraw shape from anchor to cursor
            let ex = cX, ey = cY;
            if (e.shiftKey) [ex, ey] = constrainShape(shapeStartX, shapeStartY, cX, cY);
            sctx.clearRect(0, 0, strokeCanvas.width, strokeCanvas.height);
            drawShapeOnCtx(sctx, shapeStartX, shapeStartY, ex, ey);
        } else {
            smoothedPressure += ((e.pressure || 0.1) - smoothedPressure) * 0.3;
            if (stabEnabled > 0 && stabMode === 'realtime' && !currentBrush.isGaussBlur && !currentBrush.isSmudge) {
                const sp = stabilizePoint(cX, cY, smoothedPressure, stabEnabled);
                lastX = cX; lastY = cY; lastPressure = smoothedPressure;
                if (sp) {
                    if (stabOutX !== null) {
                        drawStabLineTo(stabOutX, stabOutY, stabOutP, sp.x, sp.y, sp.p);
                    } else {
                        drawPoint(sp.x, sp.y, sp.p);
                    }
                    stabOutX = sp.x; stabOutY = sp.y; stabOutP = sp.p;
                }
            } else {
                if (stabEnabled > 0 && stabMode === 'post' && !currentBrush.isGaussBlur && !currentBrush.isSmudge) {
                    rawStrokePath.push({ x: cX, y: cY, p: smoothedPressure });
                }
                // Track pointer speed for velocity sensitivity
                const now = performance.now();
                const dt = now - lastPointerTime;
                if (dt > 0) {
                    const dist = Math.hypot(cX - lastX, cY - lastY);
                    const rawSpeed = dist / dt;
                    // Heavy smoothing (alpha=0.06) prevents jitter/dots
                    lastPointerSpeed += (rawSpeed - lastPointerSpeed) * 0.06;
                }
                lastPointerTime = now;
                drawStabLineTo(lastX, lastY, lastPressure, cX, cY, smoothedPressure);
                [lastX, lastY, lastPressure] = [cX, cY, smoothedPressure];
            }
        }
    }

    if (activeFilterType === 'chroma' && (chromaLassoMode === 'add' || chromaLassoMode === 'sub' || chromaLassoMode === 'clear')) {
        lassoPath.push({ x: world.x, y: world.y });
    }
    requestRender();
}

function handlePointerUp(e) {
    // Release canvas resize drag regardless of isDrawing
    if (resizeActiveHandle) {
        try { canvas.releasePointerCapture(e.pointerId); } catch (_) { }
        resizeActiveHandle = null;
        canvas.style.cursor = 'default';
        e.preventDefault();
        requestRender();
        return;
    }

    if (!isDrawing) return;
    canvas.releasePointerCapture(e.pointerId);
    applyCursor(false);

    if (currentTool === 'lazo-sel') {
        if (lassoSelPath.length >= 3) {
            addPathToSelection(lassoSelPath);
            if (clearSelBtn) clearSelBtn.classList.remove('hidden');
            pushHistory(); // snapshot AFTER selection was added
        }
        lassoSelPath = [];
    }
    else if (currentTool === 'lazo-des') {
        if (lassoSelPath.length >= 3) {
            subtractPathFromSelection(lassoSelPath);
            pushHistory(); // snapshot AFTER selection was subtracted
        }
        lassoSelPath = [];
        if (!hasSelection && clearSelBtn) clearSelBtn.classList.add('hidden');
    }
    else if (currentTool === 'modify-sel') {
        modSelActive = false; modSelHandle = null;
        updateFlipButtonsPosition();
        if (!isModifyingShape) pushHistory(); // snapshot AFTER move/resize is settled
    }
    else if (currentTool === 'pincel') {
        if (stabEnabled > 0 && stabMode === 'realtime' && !currentBrush.isLasso && !currentBrush.isShape && !currentBrush.useCompositing && !currentBrush.isGaussBlur && !currentBrush.isSmudge) {
            while (stabPoints.length > 0) {
                const p = stabPoints.shift();
                drawPoint(p.x, p.y, p.p);
            }
            stabPoints = [];
        }

        if (stabMode === 'post' && stabEnabled > 0 && rawStrokePath.length > 2 && isPostStrokePreview && !currentBrush.isGaussBlur && !currentBrush.isSmudge) {
            sctx.clearRect(0, 0, strokeCanvas.width, strokeCanvas.height);
            isPostStrokePreview = false;
            
            const passes = Math.round(stabEnabled * 2);
            const smoothed = smoothStrokePath(rawStrokePath, passes);
            
            drawPoint(smoothed[0].x, smoothed[0].y, smoothed[0].p);
            for (let i = 1; i < smoothed.length; i++) {
                drawStabLineTo(smoothed[i-1].x, smoothed[i-1].y, smoothed[i-1].p, smoothed[i].x, smoothed[i].y, smoothed[i].p);
            }
            rawStrokePath = [];
        } else {
            isPostStrokePreview = false;
        }
        if (currentBrush.isLasso) {
            executeLassoFill();
            updateThumbnails(); updateLayersUI();
            pushHistory();
        } else if (currentBrush.isShape) {
            // Finalize shape onto strokeCanvas (apply shift-constrain on release too)
            const world = screenToWorld(e.offsetX, e.offsetY);
            let ex = world.x, ey = world.y;
            if (e.shiftKey) [ex, ey] = constrainShape(shapeStartX, shapeStartY, ex, ey);
            sctx.clearRect(0, 0, strokeCanvas.width, strokeCanvas.height);
            drawShapeOnCtx(sctx, shapeStartX, shapeStartY, ex, ey);

            let isModifiable = false;
            if (currentBrush.shapeType === 'rect') isModifiable = shapeModifiableRect;
            else if (currentBrush.shapeType === 'ellipse') isModifiable = shapeModifiableCircle;
            else if (currentBrush.shapeType === 'line') isModifiable = shapeModifiableLine;

            if (isModifiable) {
                let minX, minY, maxX, maxY;
                if (currentBrush.shapeType === 'line') {
                    minX = Math.min(shapeStartX, ex); maxX = Math.max(shapeStartX, ex);
                    minY = Math.min(shapeStartY, ey); maxY = Math.max(shapeStartY, ey);
                } else if (currentBrush.shapeType === 'rect') {
                    if (shapeFromCenterRect) {
                        const rw = Math.abs(ex - shapeStartX) * 2;
                        const rh = Math.abs(ey - shapeStartY) * 2;
                        minX = shapeStartX - rw / 2; maxX = shapeStartX + rw / 2;
                        minY = shapeStartY - rh / 2; maxY = shapeStartY + rh / 2;
                    } else {
                        minX = Math.min(shapeStartX, ex); maxX = Math.max(shapeStartX, ex);
                        minY = Math.min(shapeStartY, ey); maxY = Math.max(shapeStartY, ey);
                    }
                } else if (currentBrush.shapeType === 'ellipse') {
                    if (shapeFromCenterCircle) {
                        const rx = Math.max(1, Math.abs(ex - shapeStartX));
                        const ry = Math.max(1, Math.abs(ey - shapeStartY));
                        minX = shapeStartX - rx; maxX = shapeStartX + rx;
                        minY = shapeStartY - ry; maxY = shapeStartY + ry;
                    } else {
                        const cx = (shapeStartX + ex) / 2; cy = (shapeStartY + ey) / 2;
                        const rx = Math.max(1, Math.abs(ex - shapeStartX) / 2);
                        const ry = Math.max(1, Math.abs(ey - shapeStartY) / 2);
                        minX = cx - rx; maxX = cx + rx;
                        minY = cy - ry; maxY = cy + ry;
                    }
                }

                const pad = Math.max(1, baseBrushSize) * 2 + 5;
                minX -= pad; minY -= pad; maxX += pad; maxY += pad;
                const w = maxX - minX;
                const h = maxY - minY;

                if (w > 0 && h > 0) {
                    modSelCanvas = document.createElement('canvas');
                    modSelCanvas.width = w; modSelCanvas.height = h;
                    modSelCtx = modSelCanvas.getContext('2d');
                    modSelCtx.globalAlpha = brushOpacity;
                    modSelCtx.save();
                    modSelCtx.translate(-minX, -minY);
                    drawShapeOnCtx(modSelCtx, shapeStartX, shapeStartY, ex, ey);
                    modSelCtx.restore();
                    sctx.clearRect(0, 0, strokeCanvas.width, strokeCanvas.height);

                    modSelBounds = { x: minX, y: minY, w, h };
                    modSelOrigBounds = { ...modSelBounds };
                    modSelRotation = 0;
                    modSelFlipX = 1; modSelFlipY = 1;
                    
                    isImportingNewImage = true;
                    isModifyingShape = true;
                    modSelInitialized = true;
                    
                    selectTool('modify-sel', 'Modificar Selección');
                    updateThumbnails(); updateLayersUI();
                    
                    isDrawing = false;
                    return;
                }
            }

            // Commit to layer
            const l = layers[selectedLayerIndex];
            l.ctx.save();
            l.ctx.globalAlpha = brushOpacity;
            if (l.alphaLocked) l.ctx.globalCompositeOperation = 'source-atop';
            l.ctx.drawImage(strokeCanvas, 0, 0);
            l.ctx.restore();
            sctx.clearRect(0, 0, strokeCanvas.width, strokeCanvas.height);

            updateThumbnails(); updateLayersUI();
            pushHistory();
        } else if (currentBrush.useCompositing) {
            const l = layers[selectedLayerIndex]; l.ctx.save(); l.ctx.globalAlpha = brushOpacity;
            if (l.alphaLocked) l.ctx.globalCompositeOperation = 'source-atop';

            // Apply ghost layer blur if needed
            if ((currentBrush.id === 'aero-duro' || currentBrush.id === 'aero-suave') && currentBlur > 0) {
                l.ctx.filter = `blur(${currentBlur}px)`;
            }

            l.ctx.drawImage(strokeCanvas, 0, 0); l.ctx.restore();
            sctx.clearRect(0, 0, strokeCanvas.width, strokeCanvas.height);

            updateThumbnails(); updateLayersUI();
            pushHistory(); // snapshot AFTER stroke is committed to the layer
        } else {
            updateThumbnails(); updateLayersUI();
            pushHistory();
        }
    }

    else if (currentTool === 'eyedropper') {
        const world = screenToWorld(e.offsetX, e.offsetY);
        const color = eyedropperMode === 'original'
            ? pickColorRaw(world.x, world.y)
            : pickColorAt(world.x, world.y);
        if (color) {
            selectedColor = color;
            mainColorPicker.value = color;
            updateTintedTexture();

            // Visual feedback: success flash and fade out
            if (eyedropperPreview) {
                eyedropperPreview.classList.add('copied');
                if (eyedropperFadeTimeout) clearTimeout(eyedropperFadeTimeout);
                eyedropperFadeTimeout = setTimeout(() => {
                    eyedropperPreview.classList.add('hidden');
                    eyedropperPreview.classList.remove('copied');
                    eyedropperFadeTimeout = null;
                }, 1500);
            }
        }
    }

    else if (currentTool === 'push') {
        updateThumbnails(); updateLayersUI();
        pushHistory();
    }

    if (activeFilterType === 'chroma' && (chromaLassoMode === 'add' || chromaLassoMode === 'sub' || chromaLassoMode === 'clear')) {
        if (lassoPath.length >= 3) {
            chromaMaskCtx.save();
            if (chromaLassoMode === 'clear') {
                chromaMaskCtx.globalCompositeOperation = 'destination-out';
                chromaMaskCtx.fillStyle = 'black';
            } else {
                chromaMaskCtx.globalCompositeOperation = 'source-over';
                chromaMaskCtx.fillStyle = chromaLassoMode === 'add' ? '#FF0000' : '#00FF00';
            }
            chromaMaskCtx.beginPath();
            chromaMaskCtx.moveTo(lassoPath[0].x, lassoPath[0].y);
            lassoPath.forEach(p => chromaMaskCtx.lineTo(p.x, p.y));
            chromaMaskCtx.closePath();
            chromaMaskCtx.fill();
            chromaMaskCtx.restore();
            applyFilters();
        }
    }

    isDrawing = false; lassoPath = [];
    if (currentTool === 'pan' && isTemporaryPan) {
        if (activeFilterType) currentTool = 'none';
        else {
            const activeToolName = activeToolIndicator?.textContent || 'Pincel';
            const t = toolsData.find(x => x.name === activeToolName);
            if (t) currentTool = t.id;
            else currentTool = 'pincel';
        }
        showSelectionButtons(currentTool);
        isTemporaryPan = false;
    }
    if (currentTool === 'rotate') selectTool('pincel', lastBrushTool);
    requestRender();
}

// ─────────────────────────────────────────────────────────────
//  BRUSH DRAWING
// ─────────────────────────────────────────────────────────────
// Gaussian smoothing: promedia cada punto con sus vecinos
// (Elimina temblor de alta frecuencia sin dejar lados rectos)
