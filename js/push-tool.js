function endPushSession() {
    pushSnapshot = null;
    pushSnapshotPixels = null;
    pushDisplacementX = null;
    pushDisplacementY = null;
}

function executePush(worldX, worldY, dx, dy) {
    if (!pushSnapshot || !pushSnapshotPixels || !pushDisplacementX || !pushDisplacementY) return;
    if (Math.abs(dx) < 0.1 && Math.abs(dy) < 0.1) return;

    const radius = baseBrushSize * 8;
    const strength = brushOpacity * 1.0;
    const l = layers[selectedLayerIndex];
    if (!l) return;

    const W = paperWidth;
    const H = paperHeight;

    const margin = radius + 2;
    const iStart = Math.max(0, Math.floor(worldX - margin));
    const iEnd = Math.min(W, Math.ceil(worldX + margin));
    const jStart = Math.max(0, Math.floor(worldY - margin));
    const jEnd = Math.min(H, Math.ceil(worldY + margin));
    const boxW = iEnd - iStart;
    const boxH = jEnd - jStart;
    if (boxW <= 0 || boxH <= 0) return;

    const tempDX = new Float32Array(boxW * boxH);
    const tempDY = new Float32Array(boxW * boxH);

    const getOldDX = (px, py) => {
        if (px < 0 || px >= W || py < 0 || py >= H) return 0;
        return pushDisplacementX[py * W + px];
    };
    const getOldDY = (px, py) => {
        if (px < 0 || px >= W || py < 0 || py >= H) return 0;
        return pushDisplacementY[py * W + px];
    };

    let selectionPixels = null;
    if (hasSelection && selectionCanvas) {
        selectionPixels = selCtx.getImageData(0, 0, W, H).data;
    }

    // Step 1: Advect displacements
    for (let j = jStart; j < jEnd; j++) {
        for (let i = iStart; i < iEnd; i++) {
            const pos = j * W + i;
            let selFactor = 1.0;
            if (hasSelection && selectionPixels) {
                selFactor = selectionPixels[pos * 4 + 3] / 255;
            }

            const dist = Math.hypot(i - worldX, j - worldY);
            let wx = 0, wy = 0;
            if (dist < radius) {
                const weight = Math.pow(1 - dist / radius, 1.5) * selFactor;
                wx = dx * weight * strength;
                wy = dy * weight * strength;
            }

            const srcX = i - wx;
            const srcY = j - wy;

            const x0 = Math.floor(srcX), x1 = x0 + 1;
            const y0 = Math.floor(srcY), y1 = y0 + 1;
            const fx = srcX - x0, fy = srcY - y0;

            const dx00 = getOldDX(x0, y0), dx10 = getOldDX(x1, y0);
            const dx01 = getOldDX(x0, y1), dx11 = getOldDX(x1, y1);
            const topX = dx00 + fx * (dx10 - dx00);
            const botX = dx01 + fx * (dx11 - dx01);
            const interpDX = topX + fy * (botX - topX);

            const dy00 = getOldDY(x0, y0), dy10 = getOldDY(x1, y0);
            const dy01 = getOldDY(x0, y1), dy11 = getOldDY(x1, y1);
            const topY = dy00 + fx * (dy10 - dy00);
            const botY = dy01 + fx * (dy11 - dy01);
            const interpDY = topY + fy * (botY - topY);

            const localPos = (j - jStart) * boxW + (i - iStart);
            tempDX[localPos] = wx + interpDX;
            tempDY[localPos] = wy + interpDY;
        }
    }

    // Step 2: Write back advected displacements and sample new image
    const destData = l.ctx.getImageData(iStart, jStart, boxW, boxH);
    const src = pushSnapshotPixels;
    const dest = destData.data;

    for (let j = jStart; j < jEnd; j++) {
        for (let i = iStart; i < iEnd; i++) {
            const globalPos = j * W + i;
            const localPos = (j - jStart) * boxW + (i - iStart);

            const finalDX = tempDX[localPos];
            const finalDY = tempDY[localPos];
            pushDisplacementX[globalPos] = finalDX;
            pushDisplacementY[globalPos] = finalDY;

            const sx = i - finalDX;
            const sy = j - finalDY;

            const x0 = Math.floor(sx), x1 = x0 + 1;
            const y0 = Math.floor(sy), y1 = y0 + 1;
            const fx = sx - x0, fy = sy - y0;

            const getP = (px, py) => {
                if (px < 0 || px >= W || py < 0 || py >= H) return [0, 0, 0, 0];
                const p = (py * W + px) * 4;
                return [src[p], src[p + 1], src[p + 2], src[p + 3]];
            };

            const p00 = getP(x0, y0), p10 = getP(x1, y0), p01 = getP(x0, y1), p11 = getP(x1, y1);
            const dPos = localPos * 4;
            for (let k = 0; k < 4; k++) {
                const top = p00[k] + fx * (p10[k] - p00[k]);
                const bot = p01[k] + fx * (p11[k] - p01[k]);
                dest[dPos + k] = top + fy * (bot - top);
            }
        }
    }

    l.ctx.putImageData(destData, iStart, jStart);
}

