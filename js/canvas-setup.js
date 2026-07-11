// ─────────────────────────────────────────────────────────────
//  CANVAS SETUP
// ─────────────────────────────────────────────────────────────
function createCheckerPattern() {
    checkerPatternLightCanvas.width = 20; checkerPatternLightCanvas.height = 20;
    const pctx1 = checkerPatternLightCanvas.getContext('2d');
    pctx1.fillStyle = '#ffffff'; pctx1.fillRect(0, 0, 20, 20);
    pctx1.fillStyle = '#f0f0f0'; pctx1.fillRect(0, 0, 10, 10); pctx1.fillRect(10, 10, 10, 10);
    checkerPatternLight = ctx.createPattern(checkerPatternLightCanvas, 'repeat');

    checkerPatternDarkCanvas.width = 20; checkerPatternDarkCanvas.height = 20;
    const pctx2 = checkerPatternDarkCanvas.getContext('2d');
    pctx2.fillStyle = '#2a2a2a'; pctx2.fillRect(0, 0, 20, 20);
    pctx2.fillStyle = '#3a3a3a'; pctx2.fillRect(0, 0, 10, 10); pctx2.fillRect(10, 10, 10, 10);
    checkerPatternDark = ctx.createPattern(checkerPatternDarkCanvas, 'repeat');
}
function startApp(w, h, initialImg = null) {
    paperWidth = w || 1920; paperHeight = h || 1080;
    
    // Set up new project state
    currentProjectId = 'proj_' + Date.now();
    currentProjectTitle = prompt('Título del proyecto:', 'Sin título') || 'Sin título';
    currentProjectTime = 0;
    
    const winW = canvas.parentElement.clientWidth; const winH = canvas.parentElement.clientHeight;
    viewScale = Math.min(winW / (paperWidth + 100), winH / (paperHeight + 100));
    setupLogicalCanvas(initialImg);
    // Seed the history with the initial blank state
    historyStack = []; historyIndex = -1;
    pushHistory();
    startupModal.style.display = 'none'; 
    document.getElementById('gallery-screen').classList.add('hidden');
    mainApp.classList.remove('blur-content'); 
    mainApp.style.pointerEvents = 'auto';
    
    updateTintedTexture();
    startProjectTimer();
    saveCurrentProject(); // Initial save to make it appear in the gallery
}

function setupScreen() {
    if (!canvas || !canvas.parentElement) return;
    const w = canvas.parentElement.clientWidth || window.innerWidth;
    const h = canvas.parentElement.clientHeight || window.innerHeight;
    canvas.width = w; canvas.height = h;
    requestRender();
}
function setupLogicalCanvas(initialImg) {
    strokeCanvas.width = paperWidth; strokeCanvas.height = paperHeight;
    groupCanvas.width = paperWidth; groupCanvas.height = paperHeight;
    maskBuffer.width = paperWidth; maskBuffer.height = paperHeight;
    selectionOutlineCanvas.width = paperWidth; selectionOutlineCanvas.height = paperHeight;
    layersCacheCanvas.width = paperWidth; layersCacheCanvas.height = paperHeight;
    layersCacheDirty = true;
    updateSelectionOutline();
    layers = []; addLayer("Capa 1");
    if (initialImg) layers[0].ctx.drawImage(initialImg, 0, 0);
    updateThumbnails();
}

// ─────────────────────────────────────────────────────────────
//  PALETTE
// ─────────────────────────────────────────────────────────────
