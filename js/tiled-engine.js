// ─────────────────────────────────────────────────────────────
//  TILED CANVAS ENGINE (Motor de Lienzo por Baldosas)
// ─────────────────────────────────────────────────────────────
const TILE_SIZE = 512;

// Buffer temporal por baldosas para el trazo en vivo (sustituye a strokeCanvas para herramientas adaptadas)
const strokeTiles = new Map();

/**
 * Obtiene o crea una baldosa (512x512) para una capa o buffer de baldosas.
 */
function getOrCreateTile(tilesMap, col, row) {
    const key = `${col}_${row}`;
    let tile = tilesMap.get(key);
    if (!tile) {
        const tCanvas = document.createElement('canvas');
        tCanvas.width = TILE_SIZE;
        tCanvas.height = TILE_SIZE;
        const tCtx = tCanvas.getContext('2d');
        tile = { canvas: tCanvas, ctx: tCtx, col, row };
        tilesMap.set(key, tile);
    }
    return tile;
}

function distToSegmentSquared(px, py, x1, y1, x2, y2) {
    const dx = x2 - x1, dy = y2 - y1;
    const l2 = dx * dx + dy * dy;
    if (l2 === 0) return (px - x1) * (px - x1) + (py - y1) * (py - y1);
    let t = ((px - x1) * dx + (py - y1) * dy) / l2;
    t = Math.max(0, Math.min(1, t));
    const nx = x1 + t * dx, ny = y1 + t * dy;
    return (px - nx) * (px - nx) + (py - ny) * (py - ny);
}

/**
 * Dibuja un segmento de línea en las baldosas que intersecta.
 * La tarjeta gráfica (Canvas) recorta automáticamente en los límites de cada baldosa.
 */
function drawTiledSegment(tilesMap, sx, sy, ex, ey, lineWidth, color, alpha = 1.0, isRound = true) {
    const r = lineWidth / 2 + 2;
    const minX = Math.min(sx, ex) - r;
    const maxX = Math.max(sx, ex) + r;
    const minY = Math.min(sy, ey) - r;
    const maxY = Math.max(sy, ey) + r;

    const minCol = Math.floor(minX / TILE_SIZE);
    const maxCol = Math.floor(maxX / TILE_SIZE);
    const minRow = Math.floor(minY / TILE_SIZE);
    const maxRow = Math.floor(maxY / TILE_SIZE);

    const maxDistSq = Math.pow(363 + r, 2);

    for (let c = minCol; c <= maxCol; c++) {
        const tcX = (c + 0.5) * TILE_SIZE;
        for (let row = minRow; row <= maxRow; row++) {
            const tcY = (row + 0.5) * TILE_SIZE;
            if (minCol !== maxCol || minRow !== maxRow) {
                if (distToSegmentSquared(tcX, tcY, sx, sy, ex, ey) > maxDistSq) continue;
            }
            const tile = getOrCreateTile(tilesMap, c, row);
            tile.ctx.save();
            tile.ctx.translate(-c * TILE_SIZE, -row * TILE_SIZE);
            tile.ctx.globalAlpha = alpha;
            tile.ctx.strokeStyle = color;
            tile.ctx.lineWidth = lineWidth;
            tile.ctx.lineCap = isRound ? 'round' : 'square';
            tile.ctx.lineJoin = isRound ? 'round' : 'miter';
            tile.ctx.beginPath();
            tile.ctx.moveTo(sx, sy);
            tile.ctx.lineTo(ex, ey);
            tile.ctx.stroke();
            tile.ctx.restore();
        }
    }
}

/**
 * Dibuja un punto/círculo en las baldosas que intersecta.
 */
function drawTiledPoint(tilesMap, x, y, radius, color, alpha = 1.0) {
    const minX = x - radius - 1;
    const maxX = x + radius + 1;
    const minY = y - radius - 1;
    const maxY = y + radius + 1;

    const minCol = Math.floor(minX / TILE_SIZE);
    const maxCol = Math.floor(maxX / TILE_SIZE);
    const minRow = Math.floor(minY / TILE_SIZE);
    const maxRow = Math.floor(maxY / TILE_SIZE);

    for (let c = minCol; c <= maxCol; c++) {
        for (let row = minRow; row <= maxRow; row++) {
            const tile = getOrCreateTile(tilesMap, c, row);
            tile.ctx.save();
            tile.ctx.translate(-c * TILE_SIZE, -row * TILE_SIZE);
            tile.ctx.globalAlpha = alpha;
            tile.ctx.fillStyle = color;
            tile.ctx.beginPath();
            tile.ctx.arc(x, y, radius, 0, Math.PI * 2);
            tile.ctx.fill();
            tile.ctx.restore();
        }
    }
}

/**
 * Vuelca las baldosas temporales del trazo a las baldosas permanentes de la capa activa.
 */
function commitStrokeTilesToLayer(layer, alpha = 1.0) {
    if (!layer.tiles) layer.tiles = new Map();
    for (const [key, sTile] of strokeTiles.entries()) {
        const [c, r] = key.split('_').map(Number);
        const lTile = getOrCreateTile(layer.tiles, c, r);
        lTile.ctx.save();
        lTile.ctx.globalAlpha = alpha;
        if (layer.alphaLocked) lTile.ctx.globalCompositeOperation = 'source-atop';
        lTile.ctx.drawImage(sTile.canvas, 0, 0);
        lTile.ctx.restore();
    }
    strokeTiles.clear();
}
