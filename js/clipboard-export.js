// ─────────────────────────────────────────────────────────────
//  CLIPBOARD & EXPORT
// ─────────────────────────────────────────────────────────────
// ─────────────────────────────────────────────────────────────
//  SHARED LAYER COMPOSITOR (respects clipping mask groups)
// ─────────────────────────────────────────────────────────────
/**
 * Composites all visible layers onto destCtx, fully respecting
 * clipping mask groups — the same logic used by the render loop.
 */
function compositeLayers(destCtx) {
    const gC = document.createElement('canvas'); gC.width = paperWidth; gC.height = paperHeight; const gX = gC.getContext('2d');
    const mC = document.createElement('canvas'); mC.width = paperWidth; mC.height = paperHeight; const mX = mC.getContext('2d');

    let i = 0;
    while (i < layers.length) {
        const l = layers[i];
        if (!l.visible) { i++; continue; }

        // Collect clipping group
        let group = [l];
        let next = i + 1;
        while (next < layers.length && layers[next].clippingMask) {
            if (layers[next].visible) group.push(layers[next]);
            next++;
        }

        if (group.length > 1) {
            // ── Render clipping group ──
            gX.clearRect(0, 0, paperWidth, paperHeight);
            gX.save(); gX.globalAlpha = group[0].opacity; gX.globalCompositeOperation = group[0].blendMode;
            gX.drawImage(group[0].canvas, 0, 0); gX.restore();

            for (let k = 1; k < group.length; k++) {
                mX.clearRect(0, 0, paperWidth, paperHeight);
                mX.save(); mX.globalAlpha = group[k].opacity;
                mX.drawImage(group[k].canvas, 0, 0); mX.restore();
                mX.globalCompositeOperation = 'destination-in';
                mX.drawImage(group[0].canvas, 0, 0);
                mX.globalCompositeOperation = 'source-over';
                gX.save(); gX.globalCompositeOperation = group[k].blendMode;
                gX.drawImage(mC, 0, 0); gX.restore();
            }
            destCtx.drawImage(gC, 0, 0);
            i = next;
        } else {
            // ── Normal layer ──
            destCtx.save();
            destCtx.globalAlpha = l.opacity;
            destCtx.globalCompositeOperation = l.blendMode;
            destCtx.drawImage(l.canvas, 0, 0);
            destCtx.restore();
            i++;
        }
    }
}

function getFlatImage() {
    const flat = document.createElement('canvas');
    flat.width = paperWidth; flat.height = paperHeight;
    const fctx = flat.getContext('2d');

    if (bgMode === 1) {
        fctx.fillStyle = solidBgColor;
        fctx.fillRect(0, 0, paperWidth, paperHeight);
    }

    compositeLayers(fctx);
    return flat;
}

function downloadImage() {
    const flat = getFlatImage();
    const link = document.createElement('a');

    const now = new Date();
    const pad = (n) => n.toString().padStart(2, '0');
    const dateStr = `${now.getFullYear()}${pad(now.getMonth() + 1)}${pad(now.getDate())}`;
    const timeStr = `${pad(now.getHours())}${pad(now.getMinutes())}${pad(now.getSeconds())}`;

    link.download = `ilustracion_${dateStr}_${timeStr}.png`;
    link.href = flat.toDataURL('image/png');
    link.click();
}

function handleIncomingFile(file) {
    if (!file || !file.type.startsWith('image/')) return;
    const reader = new FileReader();
    reader.onload = (ev) => {
        const img = new Image();
        img.onload = () => {
            if (startupImportState === 1 || layers.length === 0) {
                // If we are at startup or have no layers, start app with this image
                startApp(img.width, img.height, img);
                resetImportButton();
                if (layerImportState === 1) resetLayerImportButton();
            } else {
                // App already running, import as new layer
                importAsNewLayer(img);
                if (layerImportState === 1) resetLayerImportButton();
            }
        };
        img.src = ev.target.result;
    };
    reader.readAsDataURL(file);
}

function importAsNewLayer(img) {
    if (modSelInitialized) commitModifySelection();
    endPushSession();
    clearSelection();

    // Position at the center of the current screen view
    const viewCenter = screenToWorld(canvas.width / 2, canvas.height / 2);
    const x = Math.round(viewCenter.x - img.width / 2);
    const y = Math.round(viewCenter.y - img.height / 2);

    // Initial transformation setup (No cropping!)
    modSelCanvas = document.createElement('canvas');
    modSelCanvas.width = img.width;
    modSelCanvas.height = img.height;
    modSelCtx = modSelCanvas.getContext('2d');
    modSelCtx.drawImage(img, 0, 0);

    modSelBounds = { x, y, w: img.width, h: img.height };
    modSelOrigBounds = { ...modSelBounds };
    modSelRotation = 0;
    modSelFlipX = 1;
    modSelFlipY = 1;
    modSelLayersData = [];
    isImportingNewImage = true;
    modSelInitialized = true;

    // Trigger Modify Selection mode immediately
    selectTool('modify-sel', 'Modificar Selección');
    // initModifySelection is NOT needed because we manually initialized above

    updateThumbnails(); updateLayersUI();
}

async function copyFlatImageToClipboard() {
    const flat = getFlatImage();
    flat.toBlob(async blob => {
        try {
            const item = new ClipboardItem({ "image/png": blob });
            await navigator.clipboard.write([item]);
            alert("Imagen completa copiada al portapapeles");
        } catch (err) { alert("Error al copiar: " + err); }
    }, 'image/png');
}

async function copyToClipboard() {
    if (!hasSelection) { alert("Selecciona un área primero para copiar."); return false; }
    const bounds = getSelectionBounds();
    if (!bounds) return false;
    internalClipboardBounds = { ...bounds };

    const temp = document.createElement('canvas');
    temp.width = bounds.w; temp.height = bounds.h;
    const tctx = temp.getContext('2d');

    if (copyMode === 'capa') {
        // Solo la capa activa, recortada por la selección
        const l = layers[selectedLayerIndex];
        tctx.save();
        tctx.drawImage(selectionCanvas, -bounds.x, -bounds.y);
        tctx.globalCompositeOperation = 'source-in';
        tctx.drawImage(l.canvas, -bounds.x, -bounds.y);
        tctx.restore();
    } else if (copyMode === 'todas') {
        // Todas las capas visibles SIN fondo blanco, con clipping masks, recortado por selección
        const flat = document.createElement('canvas'); flat.width = paperWidth; flat.height = paperHeight;
        const fctx = flat.getContext('2d');
        compositeLayers(fctx);
        tctx.save();
        tctx.drawImage(selectionCanvas, -bounds.x, -bounds.y);
        tctx.globalCompositeOperation = 'source-in';
        tctx.drawImage(flat, -bounds.x, -bounds.y);
        tctx.restore();
    } else {
        // Lienzo completo (incluye fondo blanco si corresponde), recortado por selección
        const flat = getFlatImage();
        tctx.save();
        tctx.drawImage(selectionCanvas, -bounds.x, -bounds.y);
        tctx.globalCompositeOperation = 'source-in';
        tctx.drawImage(flat, -bounds.x, -bounds.y);
        tctx.restore();
    }

    return new Promise((resolve) => {
        temp.toBlob(async blob => {
            try {
                const item = new ClipboardItem({ "image/png": blob });
                await navigator.clipboard.write([item]);
                console.log("Copiado al portapapeles");
                resolve(true);
            } catch (err) { 
                alert("Error al copiar: " + err); 
                resolve(false);
            }
        }, 'image/png');
    });
}

async function cutToClipboard() {
    if (!hasSelection) { alert("Selecciona un área primero para cortar."); return; }
    if (modSelInitialized) { alert("Aplica la modificación antes de cortar."); return; }

    const success = await copyToClipboard();
    if (success) {
        const l = layers[selectedLayerIndex];
        l.ctx.save();
        l.ctx.globalCompositeOperation = 'destination-out';
        l.ctx.drawImage(selectionCanvas, 0, 0);
        l.ctx.restore();
        clearSelection(); // Remove selection mask after deletion
        updateThumbnails(); updateLayersUI();
        pushHistory();
    }
}

async function pasteFromClipboard(pasteInPlace = false) {
    clearSelection();
    try {
        const items = await navigator.clipboard.read();
        for (const item of items) {
            for (const type of item.types) {
                if (type.startsWith('image/')) {
                    const blob = await item.getType(type);
                    const img = new Image();
                    img.src = URL.createObjectURL(blob);
                    img.onload = () => {
                        // Position top-left of image at the center of the current screen view
                        const viewCenter = screenToWorld(canvas.width / 2, canvas.height / 2);
                        let x = Math.round(viewCenter.x - img.width / 2);
                        let y = Math.round(viewCenter.y - img.height / 2);

                        if (pasteInPlace && internalClipboardBounds && internalClipboardBounds.w === img.width && internalClipboardBounds.h === img.height) {
                            x = internalClipboardBounds.x;
                            y = internalClipboardBounds.y;
                        }

                        if (pasteInNewLayer) {
                            // ── Nueva capa ──
                            const lCanvas = document.createElement('canvas');
                            lCanvas.width = paperWidth; lCanvas.height = paperHeight;
                            const lCtx = lCanvas.getContext('2d', { willReadFrequently: true });
                            lCtx.drawImage(img, x, y);

                            const newLayer = { id: Date.now(), name: "Pegado", canvas: lCanvas, ctx: lCtx, visible: true, opacity: 1.0, thumbData: '', alphaLocked: false, clippingMask: false, blendMode: 'source-over' };
                            layers.splice(selectedLayerIndex + 1, 0, newLayer);
                            selectedLayerIndex++;

                            // Select the image area so Modify tool can pick it up
                            ensureSelectionCanvas();
                            selCtx.clearRect(0, 0, paperWidth, paperHeight);
                            selCtx.fillStyle = 'white';
                            selCtx.fillRect(x, y, img.width, img.height);
                            hasSelection = true;
                            updateSelectionOutline();

                            updateThumbnails(); updateLayersUI();
                            pushHistory(); // snapshot AFTER paste layer created

                            // Trigger Modify Selection mode immediately
                            selectTool('modify-sel', 'Modificar Selección');
                            initModifySelection();
                        } else {
                            // ── Capa actual (modo fantasma) ──
                            // La imagen NO se escribe en la capa todavía.
                            // Se construye el modSelCanvas manualmente para que flote
                            // sobre la capa sin destruir su contenido previo.

                            // Cancelar cualquier modificación pendiente antes de empezar
                            if (modSelInitialized) commitModifySelection();

                            // Fijar la selección al área pegada
                            ensureSelectionCanvas();
                            selCtx.clearRect(0, 0, paperWidth, paperHeight);
                            selCtx.fillStyle = 'white';
                            selCtx.fillRect(x, y, img.width, img.height);
                            hasSelection = true;
                            updateSelectionOutline();

                            // Construir el canvas fantasma directamente con la imagen
                            modSelCanvas = document.createElement('canvas');
                            modSelCanvas.width = img.width;
                            modSelCanvas.height = img.height;
                            modSelCtx = modSelCanvas.getContext('2d');
                            modSelCtx.drawImage(img, 0, 0);

                            // Definir límites del fantasma
                            modSelBounds = { x, y, w: img.width, h: img.height };
                            modSelOrigBounds = { ...modSelBounds };

                            // IMPORTANTE: Registrar la capa y el canvas para que commitModifySelection sepa dónde guardar
                            modSelLayersData = [{ layer: layers[selectedLayerIndex], canvas: modSelCanvas }];

                            modSelInitialized = true;

                            updateThumbnails(); updateLayersUI();
                            // NO pushHistory aquí — se hará al confirmar con commitModifySelection

                            // Activar la herramienta Modificar Selección
                            selectTool('modify-sel', 'Modificar Selección');
                        }
                    };
                    return;
                }
            }
        }
    } catch (err) { console.error("Error al pegar:", err); }
}


// Handle hit-test for the 8 handles + center move
const HANDLE_R = 10; // visual radius in world px
function getModifyHandle(wx, wy) {
    if (!modSelBounds) return null;
    const hitR = 15 / viewScale;

    // ── Perspective mode: only 4 corner handles + interior move ──
    if (modSelPerspectiveMode && perspCorners) {
        for (let ci = 0; ci < 4; ci++) {
            if (Math.hypot(wx - perspCorners[ci].x, wy - perspCorners[ci].y) <= hitR) return `pc${ci}`;
        }
        // Check if inside perspective quad (simple bounding box of corners)
        const xs = perspCorners.map(c => c.x), ys = perspCorners.map(c => c.y);
        if (wx >= Math.min(...xs) && wx <= Math.max(...xs) && wy >= Math.min(...ys) && wy <= Math.max(...ys)) return 'move';
        return null;
    }

    const b = modSelBounds;
    const cx = b.x + b.w / 2;
    const cy = b.y + b.h / 2;

    // 1. Check handles
    const handlePositions = {
        tl: [b.x, b.y],
        tc: [b.x + b.w / 2, b.y],
        tr: [b.x + b.w, b.y],
        ml: [b.x, b.y + b.h / 2],
        mr: [b.x + b.w, b.y + b.h / 2],
        bl: [b.x, b.y + b.h],
        bc: [b.x + b.w / 2, b.y + b.h],
        br: [b.x + b.w, b.y + b.h],
    };

    for (const [k, [hx, hy]] of Object.entries(handlePositions)) {
        const dx = hx - cx, dy = hy - cy;
        const rx = dx * Math.cos(modSelRotation) - dy * Math.sin(modSelRotation);
        const ry = dx * Math.sin(modSelRotation) + dy * Math.cos(modSelRotation);
        if (Math.hypot(wx - (cx + rx), wy - (cy + ry)) <= hitR) return k;
    }

    // 2. Check rotation handle
    const rotDist = 40 / viewScale;
    const dxL = (b.x + b.w / 2) - cx, dyL = b.y - rotDist - cy;
    const rxL = dxL * Math.cos(modSelRotation) - dyL * Math.sin(modSelRotation);
    const ryL = dxL * Math.sin(modSelRotation) + dyL * Math.cos(modSelRotation);
    if (Math.hypot(wx - (cx + rxL), wy - (cy + ryL)) <= hitR * 1.5) return 'rot';

    // 3. Check if inside bounds
    const dx = wx - cx, dy = wy - cy;
    const invCos = Math.cos(-modSelRotation), invSin = Math.sin(-modSelRotation);
    const localX = dx * invCos - dy * invSin + cx;
    const localY = dx * invSin + dy * invCos + cy;

    if (localX >= b.x && localX <= b.x + b.w && localY >= b.y && localY <= b.y + b.h) return 'move';
    return null;
}

function applyModifyDrag(dx, dy, handle, origB, shiftKey = false, worldX = 0, worldY = 0) {
    const b = { ...origB };
    if (handle === 'rot') {
        const cx = b.x + b.w / 2;
        const cy = b.y + b.h / 2;
        let angle = Math.atan2(worldY - cy, worldX - cx) + Math.PI / 2;
        if (shiftKey) {
            const snap = Math.PI / 4; // 45 degrees
            angle = Math.round(angle / snap) * snap;
        }
        modSelRotation = angle;
        return b;
    }
    switch (handle) {
        case 'move': b.x += dx; b.y += dy; break;
        case 'tl': b.x += dx; b.y += dy; b.w -= dx; b.h -= dy; break;
        case 'tc': b.y += dy; b.h -= dy; break;
        case 'tr': b.y += dy; b.w += dx; b.h -= dy; break;
        case 'ml': b.x += dx; b.w -= dx; break;
        case 'mr': b.w += dx; break;
        case 'bl': b.x += dx; b.w -= dx; b.h += dy; break;
        case 'bc': b.h += dy; break;
        case 'br': b.w += dx; b.h += dy; break;
    }

    if (shiftKey && handle !== 'move') {
        const ratio = origB.w / (origB.h || 1);
        const dw = Math.abs(b.w - origB.w);
        const dh = Math.abs(b.h - origB.h);

        if (dw / origB.w > dh / (origB.h || 1)) {
            b.h = b.w / ratio;
        } else {
            b.w = b.h * ratio;
        }

        // Adjust position based on anchor to keep scaling intuitive
        if (handle === 'tl') { b.x = origB.x + (origB.w - b.w); b.y = origB.y + (origB.h - b.h); }
        else if (handle === 'tc') { b.x = origB.x + (origB.w - b.w) / 2; b.y = origB.y + (origB.h - b.h); }
        else if (handle === 'tr') { b.y = origB.y + (origB.h - b.h); }
        else if (handle === 'ml') { b.x = origB.x + (origB.w - b.w); b.y = origB.y + (origB.h - b.h) / 2; }
        else if (handle === 'mr') { b.y = origB.y + (origB.h - b.h) / 2; }
        else if (handle === 'bl') { b.x = origB.x + (origB.w - b.w); }
        else if (handle === 'bc') { b.x = origB.x + (origB.w - b.w) / 2; }
    }

    if (b.w < 1) b.w = 1;
    if (b.h < 1) b.h = 1;
    return b;
}

// ─────────────────────────────────────────────────────────────
