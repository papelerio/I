// ─────────────────────────────────────────────────────────────
//  CANVAS RESIZE INTERACTION
// ─────────────────────────────────────────────────────────────
function getCanvasResizeHandle(wx, wy) {
    if (!isResizingCanvas) return null;
    const nw = resizePreviewW;
    const nh = resizePreviewH;

    let ox = 0, oy = 0;
    if (resizeLibre) {
        ox = resizeOffsetX;
        oy = resizeOffsetY;
    } else {
        const dw = nw - paperWidth;
        const dh = nh - paperHeight;
        const col = resizeAnchor[1];
        const row = resizeAnchor[0];
        if (col === 'c') ox = Math.round(dw / 2);
        else if (col === 'r') ox = dw;
        if (row === 'm') oy = Math.round(dh / 2);
        else if (row === 'b') oy = dh;
    }

    const x0 = -ox, y0 = -oy;

    // Check if inside the area for moving
    if (wx >= x0 && wx <= x0 + nw && wy >= y0 && wy <= y0 + nh) {
        // If it's not a handle, it's a move
        const handles = {
            tl: [x0, y0], tc: [x0 + nw / 2, y0], tr: [x0 + nw, y0],
            ml: [x0, y0 + nh / 2], mr: [x0 + nw, y0 + nh / 2],
            bl: [x0, y0 + nh], bc: [x0 + nw / 2, y0 + nh], br: [x0 + nw, y0 + nh],
        };
        // Hit radius: 20 screen pixels for canvas resize (crucial for usability)
        const hitR = 20 / viewScale;
        for (const [k, [hx, hy]] of Object.entries(handles)) {
            if (Math.hypot(wx - hx, wy - hy) <= hitR) return k;
        }
        return 'move';
    }
    return null;
}

function applyCanvasResizeDrag(dx, dy, handle, origW, origH) {
    let nw = origW;
    let nh = origH;
    switch (handle) {
        case 'tl': nw = origW - dx; nh = origH - dy; break;
        case 'tc': nh = origH - dy; break;
        case 'tr': nw = origW + dx; nh = origH - dy; break;
        case 'ml': nw = origW - dx; break;
        case 'mr': nw = origW + dx; break;
        case 'bl': nw = origW - dx; nh = origH + dy; break;
        case 'bc': nh = origH + dy; break;
        case 'br': nw = origW + dx; nh = origH + dy; break;
    }
    const finalW = Math.max(1, Math.min(8000, Math.round(nw)));
    const finalH = Math.max(1, Math.min(8000, Math.round(nh)));

    // Calculate how much the offsets should change to keep opposite edges pinned
    let dox = 0, doy = 0;
    if (handle.includes('l')) dox = finalW - origW;
    if (handle.includes('t')) doy = finalH - origH;

    return { nw: finalW, nh: finalH, dox, doy };
}

// ─────────────────────────────────────────────────────────────
