// ─────────────────────────────────────────────────────────────
//  FILTERS LOGIC
// ─────────────────────────────────────────────────────────────
let activeFilterType = null;
let filterOriginalImgData = null;

// Curves state
let curvesData = {
    rgb: [{ x: 0, y: 255 }, { x: 255, y: 0 }],
    r: [{ x: 0, y: 255 }, { x: 255, y: 0 }],
    g: [{ x: 0, y: 255 }, { x: 255, y: 0 }],
    b: [{ x: 0, y: 255 }, { x: 255, y: 0 }]
};
let curvesSmoothState = { rgb: true, r: true, g: true, b: true };
let activeCurveChannel = 'rgb';
let draggingCurvePoint = null;
let edgesBgMode = 'transparent';
let blackWhiteBgMode = 'transparent';
let filterPrevTool = 'pincel';
let chromaKeyColor = '#00ff00';
let chromaThreshold = 30;
let chromaFuzziness = 20;
let chromaMaskCanvas = null;
let chromaMaskCtx = null;
let chromaDebugBG = null; // null, '#ff0000', '#00ff00', '#0000ff'
let outlineCache = { params: {}, solid: null, outerDist: null, innerDist: null };
let chromaLassoMode = 'none'; // 'none', 'add' (regenerador), 'sub' (eliminador), 'clear' (nulo), 'pick'

function selectChromaLasso(mode) {
    const lassoBtns = document.querySelectorAll('.chroma-lasso-btn');
    if (chromaLassoMode === mode) {
        chromaLassoMode = 'none';
        lassoBtns.forEach(b => b.style.boxShadow = '');
    } else {
        chromaLassoMode = mode;
        currentTool = 'none';
        lassoBtns.forEach(b => {
            b.style.boxShadow = b.dataset.mode === mode ? '0 0 0 3px rgba(0,0,0,0.4) inset' : '';
        });
    }
}

function openFilterModal(type) {
    // Guardar la herramienta anterior, pero nunca guardar 'none' para no bloquear los filtros
    filterPrevTool = (currentTool && currentTool !== 'none') ? currentTool : filterPrevTool;
    currentTool = 'none';
    activeFilterType = type;
    const l = layers[selectedLayerIndex];
    filterOriginalImgData = l.ctx.getImageData(0, 0, paperWidth, paperHeight);

    const title = document.getElementById('filter-title');
    const desc = document.getElementById('filter-desc');
    const container = document.getElementById('filter-controls-container');
    container.innerHTML = '';

    if (type === 'blackwhite') {
        title.textContent = 'Blanco y Negro (Lineart)';
        desc.textContent = 'Extrae el lineart basándote en la luminosidad.';
        blackWhiteBgMode = 'transparent'; // Resetear siempre al abrir el modal
        addFilterToggle('Fondo', ['transparent', 'white'], blackWhiteBgMode, (v) => { blackWhiteBgMode = v; applyFilters(); });
        addFilterSlider('Punto Negro', 0, 255, 20, (v) => applyFilters());
        addFilterSlider('Punto Blanco', 0, 255, 230, (v) => applyFilters());
        addFilterSlider('Sensibilidad (Gamma)', 1, 30, 10, (v) => applyFilters()); // 1.0 * 10
    } else if (type === 'levels') {
        title.textContent = 'Curvas de Nivel';
        desc.textContent = 'Ajusta el histograma arrastrando los puntos.';
        curvesData = {
            rgb: [{ x: 0, y: 255 }, { x: 255, y: 0 }],
            r: [{ x: 0, y: 255 }, { x: 255, y: 0 }],
            g: [{ x: 0, y: 255 }, { x: 255, y: 0 }],
            b: [{ x: 0, y: 255 }, { x: 255, y: 0 }]
        };
        curvesSmoothState = { rgb: true, r: true, g: true, b: true };
        activeCurveChannel = 'rgb';
        addFilterCurveEditor(container);
    } else if (type === 'hue') {
        title.textContent = 'Cambiar Tono';
        desc.textContent = 'Ajusta tono, saturación y brillo.';
        addFilterSlider('Tono', 0, 360, 0, (v) => applyFilters());
        addFilterSlider('Saturación', -100, 100, 0, (v) => applyFilters());
        addFilterSlider('Brillo', -100, 100, 0, (v) => applyFilters());
    } else if (type === 'edges') {
        title.textContent = 'Encontrar Bordes';
        desc.textContent = 'Genera lineart a partir de los bordes.';
        edgesBgMode = 'transparent';
        addFilterToggle('Fondo', ['transparent', 'white'], 'transparent', (v) => { edgesBgMode = v; applyFilters(); });
        addFilterSlider('Sensibilidad', 1, 150, 40, (v) => applyFilters());
        addFilterSlider('Fuerza Negro', 1, 30, 12, (v) => applyFilters()); // 1.2 * 10
        addFilterSlider('Limpieza', 0, 100, 15, (v) => applyFilters());
    } else if (type === 'invert') {
        title.textContent = 'Invertir Colores';
        desc.textContent = 'Invierte todos los colores de la capa.';
    } else if (type === 'sharpen') {
        title.textContent = 'Marcar Nitidez';
        desc.textContent = 'Aumenta la nitidez y el contraste en los bordes.';
        addFilterSlider('Fuerza', 1, 100, 50, (v) => applyFilters());
    } else if (type === 'gauss') {
        title.textContent = 'Difuminado Gaussiano';
        desc.textContent = 'Aplica un desenfoque gaussiano a toda la capa.';
        addFilterSlider('Radio', 1, 50, 5, (v) => applyFilters());
    } else if (type === 'posterize') {
        title.textContent = 'Posterizar';
        desc.textContent = 'Reduce la cantidad de colores por canal.';
        addFilterSlider('Niveles', 2, 32, 6, (v) => applyFilters());
    } else if (type === 'outline') {
        title.textContent = 'Contorno (Stroke)';
        desc.textContent = 'Añade un contorno exterior a los bordes sólidos del PNG.';

        // Color picker para el contorno
        const outlineColorWrap = document.createElement('div');
        outlineColorWrap.style.cssText = 'display:flex; justify-content:space-between; align-items:center; padding:6px 0;';
        outlineColorWrap.innerHTML = `
            <label style="font-size:11px; font-weight:700; color:#444;">Color del contorno</label>
            <div style="display:flex; align-items:center; gap:8px;">
                <div id="outline-color-swatch" style="width:28px; height:28px; border-radius:6px; border:2px solid rgba(0,0,0,0.15); background:#000000; box-shadow:0 2px 6px rgba(0,0,0,0.2); cursor:pointer;"></div>
                <input type="color" id="outline-color-picker" value="#000000" style="width:0; height:0; opacity:0; position:absolute; pointer-events:none;">
            </div>
        `;
        container.appendChild(outlineColorWrap);

        const outlinePicker = outlineColorWrap.querySelector('#outline-color-picker');
        const outlineSwatch = outlineColorWrap.querySelector('#outline-color-swatch');
        outlineSwatch.onclick = () => outlinePicker.click();
        outlinePicker.oninput = () => {
            outlineSwatch.style.background = outlinePicker.value;
            applyFilters();
        };

        addFilterSlider('Grosor Externo (px)', 0, 40, 4, (v) => applyFilters());
        addFilterSlider('Umbral Alpha', 1, 255, 10, (v) => applyFilters());
        addFilterSlider('Opacidad (%)', 0, 100, 100, (v) => applyFilters());
        addFilterSlider('Suavizado bordes', 0, 8, 0, (v) => applyFilters());
        addFilterSlider('Grosor Interno (px)', 0, 40, 0, (v) => applyFilters());
    } else if (type === 'chroma') {
        title.textContent = 'Quitar Fondo (Chroma Key)';
        desc.textContent = 'Selecciona un color para volverlo transparente. Usa los lazos para refinar.';
        chromaDebugBG = '#0000ff';

        // Debug BG Buttons
        const debugWrap = document.createElement('div');
        debugWrap.style.cssText = 'display:flex; gap:5px; margin-bottom:12px; justify-content:center;';
        debugWrap.innerHTML = `
            <button class="chroma-debug-btn" data-color="#ff0000" style="width:30px; height:20px; background:#ff0000; border:2px solid white; border-radius:4px; cursor:pointer;"></button>
            <button class="chroma-debug-btn" data-color="#00ff00" style="width:30px; height:20px; background:#00ff00; border:2px solid white; border-radius:4px; cursor:pointer;"></button>
            <button class="chroma-debug-btn" data-color="#0000ff" style="width:30px; height:20px; background:#0000ff; border:2px solid black; border-radius:4px; cursor:pointer;"></button>
            <button class="chroma-debug-btn" data-color="none" style="width:30px; height:20px; background:white; border:2px solid #ccc; border-radius:4px; cursor:pointer; font-size:10px; font-weight:bold;">X</button>
        `;
        container.appendChild(debugWrap);

        debugWrap.querySelectorAll('.chroma-debug-btn').forEach(btn => {
            btn.onclick = () => {
                const color = btn.dataset.color;
                chromaDebugBG = color === 'none' ? null : color;
                debugWrap.querySelectorAll('.chroma-debug-btn').forEach(b => b.style.borderColor = 'white');
                if (color !== 'none') btn.style.borderColor = 'black';
            };
        });

        // Color Picker UI
        const colorWrap = document.createElement('div');
        colorWrap.style.cssText = 'display:flex; flex-direction:column; gap:8px; margin-bottom:10px;';
        colorWrap.innerHTML = `
            <div style="display:flex; justify-content:space-between; align-items:center;">
                <label style="font-size:11px; font-weight:700; color:#444;">Color a eliminar</label>
                <div id="chroma-color-preview" style="width:24px; height:24px; border-radius:4px; border:2px solid white; box-shadow:0 0 5px rgba(0,0,0,0.2); background:${chromaKeyColor};"></div>
            </div>
            <button id="chroma-pick-btn" class="layer-action-btn" style="width:100%; font-size:10px;">SELECCIONAR COLOR DEL LIENZO</button>
        `;
        container.appendChild(colorWrap);

        colorWrap.querySelector('#chroma-pick-btn').onclick = () => {
            chromaLassoMode = 'pick';
            colorWrap.querySelector('#chroma-pick-btn').textContent = 'HAZ CLICK EN EL COLOR...';
        };

        addFilterSlider('Tolerancia', 0, 255, chromaThreshold, (v) => { chromaThreshold = v; applyFilters(); });
        addFilterSlider('Suavizado (Fuzziness)', 0, 255, chromaFuzziness, (v) => { chromaFuzziness = v; applyFilters(); });

        // Lasso Actions
        const qKey = brushTypesData.find(b => b.id === 'lazo-relleno')?.shortcut.toUpperCase() || 'Q';
        const sKey = brushTypesData.find(b => b.id === 'borrador')?.shortcut.toUpperCase() || 'S';
        const wKey = brushTypesData.find(b => b.id === 'lazo-borrador')?.shortcut.toUpperCase() || 'W';

        const lassoWrap = document.createElement('div');
        lassoWrap.style.cssText = 'display:flex; flex-direction:column; gap:6px; margin-top:10px;';
        lassoWrap.innerHTML = `
            <button class="layer-action-btn chroma-lasso-btn" data-mode="add" style="font-size:10px; background:#4caf50; color:white; border:none; height:32px; display:flex; justify-content:space-between; align-items:center; padding:0 10px;">
                <span>LAZO REGENERADOR</span> <span style="opacity:0.7; font-weight:bold;">[${qKey}]</span>
            </button>
            <button class="layer-action-btn chroma-lasso-btn" data-mode="clear" style="font-size:10px; background:#607d8b; color:white; border:none; height:32px; display:flex; justify-content:space-between; align-items:center; padding:0 10px;">
                <span>LAZO NULO</span> <span style="opacity:0.7; font-weight:bold;">[${sKey}]</span>
            </button>
            <button class="layer-action-btn chroma-lasso-btn" data-mode="sub" style="font-size:10px; background:#f44336; color:white; border:none; height:32px; display:flex; justify-content:space-between; align-items:center; padding:0 10px;">
                <span>LAZO ELIMINADOR</span> <span style="opacity:0.7; font-weight:bold;">[${wKey}]</span>
            </button>
        `;
        container.appendChild(lassoWrap);

        const lassoBtns = lassoWrap.querySelectorAll('.chroma-lasso-btn');
        lassoBtns.forEach(btn => {
            btn.onclick = () => selectChromaLasso(btn.dataset.mode);
        });

        // Setup manual mask canvas
        if (!chromaMaskCanvas) {
            chromaMaskCanvas = document.createElement('canvas');
            chromaMaskCanvas.width = paperWidth;
            chromaMaskCanvas.height = paperHeight;
            chromaMaskCtx = chromaMaskCanvas.getContext('2d');
        }
        chromaMaskCtx.clearRect(0, 0, paperWidth, paperHeight);
        chromaLassoMode = 'pick';
    }

    filterModal.classList.remove('hidden');
    makeDraggable(filterModal, document.getElementById('filter-header'));

    if (type === 'levels') {
        drawFilterHistogram();
        updateCurveUI();
    }

    applyFilters();
}

function addFilterSlider(label, min, max, val, oninput) {
    const wrap = document.createElement('div');
    wrap.style.cssText = 'display:flex; flex-direction:column; gap:4px;';

    wrap.innerHTML = `
        <div style="display:flex; justify-content:space-between; align-items:center;">
            <label style="font-size:11px; font-weight:700; color:#444;">${label}</label>
            <span class="val-display" style="font-size:11px; font-weight:700; background:#eee; padding:2px 6px; border-radius:4px;">${val}</span>
        </div>
        <div style="display:flex; gap:8px; align-items:center;">
            <button class="step-btn mini-tool-btn" style="width:24px; height:24px;">-</button>
            <input type="range" min="${min}" max="${max}" value="${val}" style="flex:1; height:4px;">
            <button class="step-btn mini-tool-btn" style="width:24px; height:24px;">+</button>
        </div>
    `;

    const input = wrap.querySelector('input');
    const display = wrap.querySelector('.val-display');
    const [btnDown, btnUp] = wrap.querySelectorAll('.step-btn');

    const update = (v) => {
        v = Math.max(min, Math.min(max, v));
        input.value = v;
        display.textContent = v;
        oninput(parseInt(v));
    };

    input.oninput = () => update(input.value);
    input.onpointerup = (e) => e.target.blur();
    btnDown.onclick = () => update(parseInt(input.value) - 1);
    btnUp.onclick = () => update(parseInt(input.value) + 1);

    document.getElementById('filter-controls-container').appendChild(wrap);
}

function addFilterToggle(label, modes, current, onclick) {
    const wrap = document.createElement('div');
    wrap.style.cssText = 'display:flex; flex-direction:column; gap:6px; margin-bottom:5px;';
    wrap.innerHTML = `
        <label style="font-size:11px; font-weight:700; color:#444;">${label}</label>
        <div style="display:flex; gap:5px; background:#f0f0f0; padding:4px; border-radius:10px;">
            ${modes.map(m => `<button class="layer-action-btn" style="flex:1; border:none; border-radius:6px; background:${m === current ? '#000' : 'transparent'}; color:${m === current ? '#fff' : '#666'}; padding:6px; font-size:10px; font-weight:700; cursor:pointer;">${m === 'transparent' ? 'TRANSPARENTE' : 'BLANCO'}</button>`).join('')}
        </div>
    `;
    const btns = wrap.querySelectorAll('button');
    btns.forEach((btn, idx) => {
        btn.onclick = () => {
            btns.forEach(b => { b.style.background = 'transparent'; b.style.color = '#666'; });
            btn.style.background = '#000';
            btn.style.color = '#fff';
            onclick(modes[idx]);
        };
    });
    document.getElementById('filter-controls-container').appendChild(wrap);
}

// ── Curve Editor UI & Logic ──

function generateCurveLut(points, isSmooth) {
    const lut = new Uint8Array(256);
    if (!isSmooth || points.length < 3) {
        for (let i = 0; i < points.length - 1; i++) {
            const p1 = points[i], p2 = points[i + 1];
            for (let x = p1.x; x <= p2.x; x++) {
                const t = (x - p1.x) / (p2.x - p1.x || 1);
                lut[x] = Math.max(0, Math.min(255, 255 - (p1.y + t * (p2.y - p1.y))));
            }
        }
    } else {
        const n = points.length;
        const m = new Float32Array(n);
        const d = new Float32Array(n - 1);
        for (let i = 0; i < n - 1; i++) {
            d[i] = (points[i+1].y - points[i].y) / (points[i+1].x - points[i].x || 1);
        }
        m[0] = d[0];
        m[n - 1] = d[n - 2];
        for (let i = 1; i < n - 1; i++) {
            if (d[i-1] * d[i] <= 0) m[i] = 0;
            else m[i] = (d[i-1] + d[i]) / 2;
        }
        for (let i = 0; i < n - 1; i++) {
            const p0 = points[i], p1 = points[i+1];
            const h = p1.x - p0.x;
            for (let x = p0.x; x <= p1.x; x++) {
                if (h === 0) {
                    lut[x] = Math.max(0, Math.min(255, 255 - p0.y));
                    continue;
                }
                const t = (x - p0.x) / h;
                const t2 = t * t;
                const t3 = t2 * t;
                const h00 = 2*t3 - 3*t2 + 1;
                const h10 = t3 - 2*t2 + t;
                const h01 = -2*t3 + 3*t2;
                const h11 = t3 - t2;
                const y = h00 * p0.y + h10 * h * m[i] + h01 * p1.y + h11 * h * m[i+1];
                lut[x] = Math.max(0, Math.min(255, 255 - y));
            }
        }
    }
    return lut;
}

function addFilterCurveEditor(container) {
    const header = document.createElement('div');
    header.style.marginBottom = '10px';
    header.style.display = 'flex';
    header.style.justifyContent = 'center';
    header.style.alignItems = 'center';
    header.style.gap = '10px';
    header.innerHTML = `
        <select id="curveChannelSelect" style="flex: 1; border: 1px solid #444; border-radius: 5px; padding: 4px; font-size: 12px; cursor: pointer; outline: none; font-weight: bold; color: black;">
            <option value="rgb">RGB (Global)</option>
            <option value="r">Rojo (Red)</option>
            <option value="g">Verde (Green)</option>
            <option value="b">Azul (Blue)</option>
        </select>
        <label style="font-size: 11px; display: flex; align-items: center; gap: 4px; cursor: pointer; color: #ddd; white-space: nowrap;" title="Interpola la curva con suavizado Spline">
            <input type="checkbox" id="curveSmoothToggle" checked> Curva "S"
        </label>
    `;
    container.appendChild(header);

    const area = document.createElement('div');
    area.className = 'curve-area';
    area.innerHTML = `
        <canvas id="histoCanvas" width="256" height="256"></canvas>
        <svg id="curveSvg" viewBox="0 0 256 256">
            <polyline id="curveLine"></polyline>
        </svg>
        <div class="curve-hint"><b>Doble Click</b>: añadir/quitar | <b>Arrastrar</b>: ajustar</div>
    `;
    container.appendChild(area);

    const select = header.querySelector('#curveChannelSelect');
    const smoothToggle = header.querySelector('#curveSmoothToggle');
    
    const updateSelectColor = () => {
        if (activeCurveChannel === 'rgb') select.style.background = 'orange';
        else if (activeCurveChannel === 'r') select.style.background = '#ff5555';
        else if (activeCurveChannel === 'g') select.style.background = '#55ff55';
        else if (activeCurveChannel === 'b') select.style.background = '#5555ff';
        smoothToggle.checked = curvesSmoothState[activeCurveChannel];
    };

    select.value = activeCurveChannel;
    updateSelectColor();
    
    select.addEventListener('change', (e) => {
        activeCurveChannel = e.target.value;
        updateSelectColor();
        drawFilterHistogram();
        updateCurveUI();
    });

    smoothToggle.addEventListener('change', (e) => {
        curvesSmoothState[activeCurveChannel] = e.target.checked;
        updateCurveUI();
        applyFilters();
    });

    const svg = area.querySelector('#curveSvg');

    svg.style.touchAction = 'none'; // Prevent scroll on touch/pen
    svg.addEventListener('pointerdown', handleCurveMouseDown);
    svg.addEventListener('dblclick', handleCurveDblClick);

    // Global listeners for dragging
    window.addEventListener('pointermove', handleCurveMouseMove);
    window.addEventListener('pointerup', handleCurveMouseUp);
}

function getCurveMousePos(e) {
    const svg = document.getElementById('curveSvg');
    if (!svg) return { x: 0, y: 0 };
    const rect = svg.getBoundingClientRect();
    return {
        x: Math.round(Math.max(0, Math.min(255, e.clientX - rect.left))),
        y: Math.round(Math.max(0, Math.min(255, e.clientY - rect.top)))
    };
}

function handleCurveMouseDown(e) {
    const pos = getCurveMousePos(e);
    const curvePoints = curvesData[activeCurveChannel];
    const hitIndex = curvePoints.findIndex(p => Math.hypot(p.x - pos.x, p.y - pos.y) < 12);
    if (hitIndex !== -1) {
        draggingCurvePoint = hitIndex;
        e.preventDefault(); // Prevent text selection/drag behaviors
    }
}

function handleCurveMouseMove(e) {
    if (draggingCurvePoint === null) return;
    const pos = getCurveMousePos(e);
    const curvePoints = curvesData[activeCurveChannel];

    if (draggingCurvePoint === 0) {
        curvePoints[0].y = pos.y;
    } else if (draggingCurvePoint === curvePoints.length - 1) {
        curvePoints[curvePoints.length - 1].y = pos.y;
    } else {
        const prevX = curvePoints[draggingCurvePoint - 1].x;
        const nextX = curvePoints[draggingCurvePoint + 1].x;
        curvePoints[draggingCurvePoint].x = Math.max(prevX + 1, Math.min(nextX - 1, pos.x));
        curvePoints[draggingCurvePoint].y = pos.y;
    }
    updateCurveUI();
    applyFilters();
}

function handleCurveMouseUp() {
    draggingCurvePoint = null;
}

function handleCurveDblClick(e) {
    const pos = getCurveMousePos(e);
    const curvePoints = curvesData[activeCurveChannel];
    const hitIndex = curvePoints.findIndex(p => Math.hypot(p.x - pos.x, p.y - pos.y) < 12);

    if (hitIndex > 0 && hitIndex < curvePoints.length - 1) {
        curvePoints.splice(hitIndex, 1);
    } else if (hitIndex === -1) {
        curvePoints.push(pos);
        curvePoints.sort((a, b) => a.x - b.x);
    }
    updateCurveUI();
    applyFilters();
}

function updateCurveUI() {
    const line = document.getElementById('curveLine');
    const svg = document.getElementById('curveSvg');
    if (!line || !svg) return;

    const curvePoints = curvesData[activeCurveChannel];
    const isSmooth = curvesSmoothState[activeCurveChannel];
    
    if (isSmooth && curvePoints.length > 2) {
        const lut = generateCurveLut(curvePoints, true);
        const pathPoints = [];
        let lastP = curvePoints[0];
        pathPoints.push(`${lastP.x},${lastP.y}`);
        for (let x = curvePoints[0].x; x <= curvePoints[curvePoints.length - 1].x; x++) {
            pathPoints.push(`${x},${255 - lut[x]}`);
        }
        line.setAttribute('points', pathPoints.join(' '));
    } else {
        line.setAttribute('points', curvePoints.map(p => `${p.x},${p.y}`).join(' '));
    }

    let strokeColor = 'white';
    if (activeCurveChannel === 'r') strokeColor = '#ff5555';
    if (activeCurveChannel === 'g') strokeColor = '#55ff55';
    if (activeCurveChannel === 'b') strokeColor = '#5555ff';
    line.setAttribute('stroke', strokeColor);

    // Clear old circles
    svg.querySelectorAll('.curve-point').forEach(c => c.remove());

    curvePoints.forEach((p, i) => {
        const c = document.createElementNS("http://www.w3.org/2000/svg", "circle");
        c.setAttribute("cx", p.x);
        c.setAttribute("cy", p.y);
        c.setAttribute("r", 5);
        c.setAttribute("class", "curve-point");
        c.setAttribute("fill", strokeColor);
        svg.appendChild(c);
    });
}

function drawFilterHistogram() {
    const hCanvas = document.getElementById('histoCanvas');
    if (!hCanvas || !filterOriginalImgData) return;
    const hCtx = hCanvas.getContext('2d');
    const data = filterOriginalImgData.data;
    const hist = new Array(256).fill(0);

    for (let i = 0; i < data.length; i += 4) {
        let val;
        if (activeCurveChannel === 'r') val = data[i];
        else if (activeCurveChannel === 'g') val = data[i+1];
        else if (activeCurveChannel === 'b') val = data[i+2];
        else val = Math.round((data[i] + data[i + 1] + data[i + 2]) / 3);
        hist[val]++;
    }

    const max = Math.max(...hist);
    hCtx.clearRect(0, 0, 256, 256);
    
    if (activeCurveChannel === 'r') hCtx.fillStyle = 'rgba(255, 85, 85, 0.4)';
    else if (activeCurveChannel === 'g') hCtx.fillStyle = 'rgba(85, 255, 85, 0.4)';
    else if (activeCurveChannel === 'b') hCtx.fillStyle = 'rgba(85, 85, 255, 0.4)';
    else hCtx.fillStyle = 'rgba(255, 255, 255, 0.4)';
    for (let i = 0; i < 256; i++) {
        const h = (hist[i] / (max || 1)) * 256;
        hCtx.fillRect(i, 256 - h, 1, h);
    }
}

function makeDraggable(el, handle) {
    let pos1 = 0, pos2 = 0, pos3 = 0, pos4 = 0;
    handle.onmousedown = (e) => {
        e.preventDefault();
        pos3 = e.clientX; pos4 = e.clientY;
        document.onmouseup = () => { document.onmouseup = null; document.onmousemove = null; };
        document.onmousemove = (e) => {
            e.preventDefault();
            pos1 = pos3 - e.clientX; pos2 = pos4 - e.clientY;
            pos3 = e.clientX; pos4 = e.clientY;
            el.style.top = (el.offsetTop - pos2) + "px";
            el.style.left = (el.offsetLeft - pos1) + "px";
        };
    };
}

function applyFilters() {
    if (!filterOriginalImgData) return;
    const sliders = document.getElementById('filter-controls-container').querySelectorAll('input[type="range"]');
    const l = layers[selectedLayerIndex];

    // Create copy for processing
    const workingData = new ImageData(new Uint8ClampedArray(filterOriginalImgData.data), paperWidth, paperHeight);
    const data = workingData.data;

    if (activeFilterType === 'blackwhite') {
        const bPoint = parseInt(sliders[0].value);
        const wPoint = parseInt(sliders[1].value);
        const gamma = parseInt(sliders[2].value) / 10;

        for (let i = 0; i < data.length; i += 4) {
            const origA = data[i + 3];
            const luma = 0.299 * data[i] + 0.587 * data[i + 1] + 0.114 * data[i + 2];
            let alpha;
            if (luma <= bPoint) alpha = 255;
            else if (luma >= wPoint) alpha = 0;
            else alpha = 255 * (1 - (luma - bPoint) / (wPoint - bPoint || 1));

            alpha = Math.pow(alpha / 255, gamma) * 255;
            if (alpha > 255) alpha = 255;

            // Combinar alpha calculado con el original para respetar transparencia
            const combinedA = alpha * (origA / 255);

            if (blackWhiteBgMode === 'transparent') {
                data[i] = data[i + 1] = data[i + 2] = 0;
                data[i + 3] = combinedA;
            } else {
                const val = 255 - combinedA;
                data[i] = data[i + 1] = data[i + 2] = val;
                data[i + 3] = 255;
            }
        }
    } else if (activeFilterType === 'levels') {
        const lutRGB = generateCurveLut(curvesData.rgb, curvesSmoothState.rgb);
        const lutR = generateCurveLut(curvesData.r, curvesSmoothState.r);
        const lutG = generateCurveLut(curvesData.g, curvesSmoothState.g);
        const lutB = generateCurveLut(curvesData.b, curvesSmoothState.b);

        for (let i = 0; i < data.length; i += 4) {
            data[i] = lutRGB[lutR[data[i]]];
            data[i + 1] = lutRGB[lutG[data[i + 1]]];
            data[i + 2] = lutRGB[lutB[data[i + 2]]];
        }
    } else if (activeFilterType === 'hue') {
        const hueShift = parseInt(sliders[0].value);
        const satAdjust = parseInt(sliders[1].value) / 100;
        const briAdjust = parseInt(sliders[2].value) / 100;
        for (let i = 0; i < data.length; i += 4) {
            const [r, g, b] = [data[i], data[i + 1], data[i + 2]];
            let [h, s, l] = rgbToHsl(r, g, b);
            h = (h + hueShift) % 360;
            s = Math.max(0, Math.min(1, s + satAdjust));
            l = Math.max(0, Math.min(1, l + briAdjust));
            const [nr, ng, nb] = hslToRgb(h, s, l);
            data[i] = nr; data[i + 1] = ng; data[i + 2] = nb;
        }
    } else if (activeFilterType === 'edges') {
        const sens = parseInt(sliders[0].value) / 10;
        const gamma = parseInt(sliders[1].value) / 10;
        const clean = parseInt(sliders[2].value);

        const width = paperWidth;
        const height = paperHeight;
        const gray = new Float32Array(width * height);
        const orig = filterOriginalImgData.data;

        // 1. Grayscale pass (include alpha so transparent boundaries create contrast)
        for (let i = 0; i < orig.length; i += 4) {
            const r = orig[i], g = orig[i + 1], b = orig[i + 2], a = orig[i + 3];
            const lum = 0.299 * r + 0.587 * g + 0.114 * b;
            gray[i / 4] = a < 64 ? -2000 : lum;
        }

        // 2. Sobel pass
        for (let y = 1; y < height - 1; y++) {
            for (let x = 1; x < width - 1; x++) {
                const i = y * width + x;
                const gx = -gray[i - width - 1] + gray[i - width + 1] - 2 * gray[i - 1] + 2 * gray[i + 1] - gray[i + width - 1] + gray[i + width + 1];
                const gy = -gray[i - width - 1] - 2 * gray[i - width] - gray[i - width + 1] + gray[i + width - 1] + 2 * gray[i + width] + gray[i + width + 1];

                let mag = Math.sqrt(gx * gx + gy * gy) * sens;
                mag = Math.max(0, mag - clean);
                let edge = Math.pow(mag / 255, 1 / gamma) * 255;
                if (edge > 255) edge = 255;

                const idx = i * 4;

                if (edgesBgMode === 'transparent') {
                    data[idx] = data[idx + 1] = data[idx + 2] = 0;
                    data[idx + 3] = edge;
                } else {
                    const val = 255 - edge;
                    data[idx] = data[idx + 1] = data[idx + 2] = val;
                    data[idx + 3] = 255;
                }
            }
        }
    } else if (activeFilterType === 'invert') {
        for (let i = 0; i < data.length; i += 4) {
            data[i] = 255 - data[i];
            data[i + 1] = 255 - data[i + 1];
            data[i + 2] = 255 - data[i + 2];
        }
    } else if (activeFilterType === 'sharpen') {
        const force = parseInt(sliders[0].value) / 50;
        const width = paperWidth;
        const height = paperHeight;
        const orig = filterOriginalImgData.data;

        for (let y = 1; y < height - 1; y++) {
            for (let x = 1; x < width - 1; x++) {
                const i = (y * width + x) * 4;
                const t = ((y - 1) * width + x) * 4;
                const b = ((y + 1) * width + x) * 4;
                const l = (y * width + (x - 1)) * 4;
                const r = (y * width + (x + 1)) * 4;

                for (let c = 0; c < 3; c++) {
                    let val = orig[i + c] * (1 + 4 * force)
                        - orig[t + c] * force
                        - orig[b + c] * force
                        - orig[l + c] * force
                        - orig[r + c] * force;
                    data[i + c] = Math.min(255, Math.max(0, val));
                }
                data[i + 3] = orig[i + 3]; // keep alpha
            }
        }
    } else if (activeFilterType === 'gauss') {
        const radius = Math.min(parseInt(sliders[0].value), 200);
        const tmpCanvas = document.createElement('canvas');
        tmpCanvas.width = paperWidth;
        tmpCanvas.height = paperHeight;
        const tmpCtx = tmpCanvas.getContext('2d');
        tmpCtx.putImageData(filterOriginalImgData, 0, 0);

        l.ctx.save();
        l.ctx.clearRect(0, 0, paperWidth, paperHeight);
        l.ctx.filter = `blur(${radius}px)`;
        l.ctx.drawImage(tmpCanvas, 0, 0);
        l.ctx.restore();
        requestRender();
        return; // skip the generic putImageData at the end
    } else if (activeFilterType === 'posterize') {
        const levels = parseInt(sliders[0].value);
        const step = 255 / (levels - 1);
        for (let i = 0; i < data.length; i += 4) {
            data[i]     = Math.round(data[i]     / step) * step;
            data[i + 1] = Math.round(data[i + 1] / step) * step;
            data[i + 2] = Math.round(data[i + 2] / step) * step;
        }
    } else if (activeFilterType === 'outline') {
        const size       = parseInt(sliders[0].value);
        const threshold  = parseInt(sliders[1].value);  // alpha mínimo para considerarse sólido
        const opacity    = parseInt(sliders[2].value) / 100;
        const feather    = parseInt(sliders[3].value);  // suavizado en px
        const innerSize  = parseInt(sliders[4].value);

        const colorPicker = document.getElementById('outline-color-picker');
        const [oR, oG, oB] = hexToRgbArray(colorPicker ? colorPicker.value : '#000000');
        const oA = Math.round(opacity * 255);

        const w = paperWidth, h = paperHeight;
        const orig = filterOriginalImgData.data;

        // Verify cache to avoid expensive recalculation on color/opacity change
        if (outlineCache.params.size !== size || outlineCache.params.threshold !== threshold || 
            outlineCache.params.feather !== feather || outlineCache.params.inner !== innerSize ||
            !outlineCache.solid) {
            
            const solid = new Uint8Array(w * h);
            const trans = new Uint8Array(w * h);
            for (let i = 0; i < orig.length; i += 4) {
                if (orig[i + 3] >= threshold) solid[i >> 2] = 1;
                else trans[i >> 2] = 1;
            }

            // Function to compute distance map
            const computeDist = (mask, radius) => {
                const map = new Float32Array(w * h).fill(Infinity);
                if (radius <= 0) return map;
                const hDil = new Uint8Array(w * h);
                const rowP = new Int32Array(w + 1);
                for (let y = 0; y < h; y++) {
                    const base = y * w; rowP[0] = 0;
                    for (let x = 0; x < w; x++) rowP[x + 1] = rowP[x] + mask[base + x];
                    for (let x = 0; x < w; x++) {
                        const l = Math.max(0, x - radius), r = Math.min(w - 1, x + radius);
                        if (rowP[r + 1] - rowP[l] > 0) hDil[base + x] = 1;
                    }
                }
                const dil = new Uint8Array(w * h);
                const colP = new Int32Array(h + 1);
                for (let x = 0; x < w; x++) {
                    colP[0] = 0;
                    for (let y = 0; y < h; y++) colP[y + 1] = colP[y] + hDil[y * w + x];
                    for (let y = 0; y < h; y++) {
                        const t = Math.max(0, y - radius), b = Math.min(h - 1, y + radius);
                        if (colP[b + 1] - colP[t] > 0) dil[y * w + x] = 1;
                    }
                }
                for (let y = 0; y < h; y++) {
                    for (let x = 0; x < w; x++) {
                        const idx = y * w + x;
                        if (mask[idx]) { map[idx] = 0; continue; }
                        if (!dil[idx]) continue;
                        let minDist2 = Infinity;
                        const yMin = Math.max(0, y - radius), yMax = Math.min(h - 1, y + radius);
                        const xMin = Math.max(0, x - radius), xMax = Math.min(w - 1, x + radius);
                        outer: for (let ny = yMin; ny <= yMax; ny++) {
                            const dy = ny - y, dy2 = dy * dy;
                            if (dy2 >= minDist2) continue;
                            for (let nx = xMin; nx <= xMax; nx++) {
                                if (!mask[ny * w + nx]) continue;
                                const d2 = (nx - x)*(nx - x) + dy2;
                                if (d2 < minDist2) { minDist2 = d2; if (minDist2 === 1) break outer; }
                            }
                        }
                        map[idx] = Math.sqrt(minDist2);
                    }
                }
                return map;
            };

            outlineCache.solid = solid;
            outlineCache.outerDist = computeDist(solid, size);
            outlineCache.innerDist = computeDist(trans, innerSize);
            outlineCache.params = { size, threshold, feather, inner: innerSize };
        }

        const solid = outlineCache.solid;
        const outerDist = outlineCache.outerDist;
        const innerDist = outlineCache.innerDist;

        for (let i = 0; i < data.length; i += 4) {
            const idx = i >> 2;
            const isSolid = solid[idx];
            
            let alpha = 0;
            if (!isSolid && outerDist[idx] <= size && size > 0) {
                alpha = oA;
                if (feather > 0) {
                    const edge = outerDist[idx] / size;
                    const start = 1 - (feather / size);
                    if (edge > start) alpha = Math.round(oA * (1 - (edge - start) / (1 - start || 0.001)));
                }
            } else if (isSolid && innerDist[idx] <= innerSize && innerSize > 0) {
                alpha = oA;
                if (feather > 0) {
                    const edge = innerDist[idx] / innerSize;
                    const start = 1 - (feather / innerSize);
                    if (edge > start) alpha = Math.round(oA * (1 - (edge - start) / (1 - start || 0.001)));
                }
            }

            if (alpha <= 0) continue;

            const origA = orig[i + 3];
            
            if (origA === 0) {
                // Si el pixel original es 100% transparente, solo pintamos el contorno
                data[i] = oR; data[i + 1] = oG; data[i + 2] = oB; data[i + 3] = alpha;
            } else {
                // Composición Source-Over: El contorno (Source) se pinta SIEMPRE por encima del pixel original (Destination)
                const aSrc = alpha / 255;
                const aDst = origA / 255;
                const outA = aSrc + aDst * (1 - aSrc);
                data[i]     = Math.round((oR * aSrc + orig[i] * aDst * (1 - aSrc)) / outA);
                data[i + 1] = Math.round((oG * aSrc + orig[i + 1] * aDst * (1 - aSrc)) / outA);
                data[i + 2] = Math.round((oB * aSrc + orig[i + 2] * aDst * (1 - aSrc)) / outA);
                data[i + 3] = Math.round(outA * 255);
            }
        }
    } else if (activeFilterType === 'chroma') {
        const keyRGB = hexToRgbArray(chromaKeyColor, 255);
        const threshSq = chromaThreshold * chromaThreshold;
        const fuzzyRange = chromaFuzziness;

        // Manual mask data for fast access
        const mData = chromaMaskCtx.getImageData(0, 0, paperWidth, paperHeight).data;

        for (let i = 0; i < data.length; i += 4) {
            // Check manual mask first: R=255 means add, G=255 means sub
            if (mData[i] > 200) {
                // Regenerate: keep original alpha
                continue;
            } else if (mData[i + 1] > 200) {
                // Remove: force alpha to 0
                data[i + 3] = 0;
                continue;
            }

            const r = data[i], g = data[i + 1], b = data[i + 2];
            const dr = r - keyRGB[0], dg = g - keyRGB[1], db = b - keyRGB[2];
            const dist = Math.sqrt(dr * dr + dg * dg + db * db);

            let alpha = 255;
            if (dist < chromaThreshold) {
                alpha = 0;
            } else if (dist < chromaThreshold + fuzzyRange) {
                alpha = 255 * ((dist - chromaThreshold) / (fuzzyRange || 1));
            }

            data[i + 3] = Math.min(data[i + 3], alpha);
        }
    }

    l.ctx.putImageData(workingData, 0, 0);
    requestRender();
}

function commitFilter() {
    pushHistory(); // Capture the new state
    filterModal.classList.add('hidden');
    filterOriginalImgData = null;
    activeFilterType = null;
    chromaDebugBG = null;
    outlineCache.solid = null; outlineCache.outerDist = null; outlineCache.innerDist = null;
    // Asegurar que la herramienta restaurada sea válida y nunca 'none'
    currentTool = (filterPrevTool && filterPrevTool !== 'none') ? filterPrevTool : 'pincel';
    chromaLassoMode = 'none';
    blackWhiteBgMode = 'transparent'; // Limpiar estado para próxima apertura
    layersCacheDirty = true;
    updateThumbnails(); updateLayersUI();
    requestRender();
}

function cancelFilter() {
    if (filterOriginalImgData) {
        layers[selectedLayerIndex].ctx.putImageData(filterOriginalImgData, 0, 0);
    }
    filterModal.classList.add('hidden');
    filterOriginalImgData = null;
    activeFilterType = null;
    chromaDebugBG = null;
    outlineCache.solid = null; outlineCache.outerDist = null; outlineCache.innerDist = null;
    currentTool = filterPrevTool;
    chromaLassoMode = 'none';
    requestRender();
}

// Helper: RGB to HSL
function lerp(a, b, t) { return a + (b - a) * t; }

function rgbToHsl(r, g, b) {
    r /= 255; g /= 255; b /= 255;
    const max = Math.max(r, g, b), min = Math.min(r, g, b);
    let h, s, l = (max + min) / 2;
    if (max === min) h = s = 0;
    else {
        const d = max - min;
        s = l > 0.5 ? d / (2 - max - min) : d / (max + min);
        switch (max) {
            case r: h = (g - b) / d + (g < b ? 6 : 0); break;
            case g: h = (b - r) / d + 2; break;
            case b: h = (r - g) / d + 4; break;
        }
        h *= 60;
    }
    return [h, s, l];
}

// Helper: HSL to RGB
function hslToRgb(h, s, l) {
    let r, g, b;
    if (s === 0) r = g = b = l;
    else {
        const hue2rgb = (p, q, t) => {
            if (t < 0) t += 1; if (t > 1) t -= 1;
            if (t < 1 / 6) return p + (q - p) * 6 * t;
            if (t < 1 / 2) return q;
            if (t < 2 / 3) return p + (q - p) * (2 / 3 - t) * 6;
            return p;
        };
        const q = l < 0.5 ? l * (1 + s) : l + s - l * s;
        const p = 2 * l - q;
        r = hue2rgb(p, q, h / 360 + 1 / 3);
        g = hue2rgb(p, q, h / 360);
        b = hue2rgb(p, q, h / 360 - 1 / 3);
    }
    return [Math.round(r * 255), Math.round(g * 255), Math.round(b * 255)];
}

