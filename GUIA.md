# GUIA.md — Índice del Ilustrador Digital Pro
> Léela primero para encontrar qué archivo editar sin cargar todo el código.

---

## MAPA DE MODULOS

| Archivo | Líneas | Descripción |
|---|---|---|
| js/globals.js | 358 | Variables globales, buffers canvas, datos de herramientas/pinceles/modos |
| js/history.js | 228 | Sistema de Undo/Redo (captureHistoryState, pushHistory, restoreHistoryState) |
| js/init.js | 544 | Función init() y todos los event listeners iniciales |
| js/filters.js | 930 | Filtros: Blanco y Negro, Curvas, Tono, Bordes, Nitidez, Contorno, Chroma Key |
| js/canvas-resize-modal.js | 168 | UI del panel de redimensionado de lienzo |
| js/save-system.js | 159 | IndexedDB: guardar/cargar ranuras de proyecto |
| js/selection-ui.js | 157 | Botones flotantes de selección (buildSelectionUI, showSelectionButtons) |
| js/selection-mask.js | 261 | Máscara de selección: addPathToSelection, clearSelection, updateSelectionOutline |
| js/modify-selection.js | 247 | Perspectiva warp: drawTexturedTriangle, renderPerspectiveWarpPreview, commitModifySelection |
| js/clipboard-export.js | 424 | Portapapeles, exportar PNG, importar archivos, getModifyHandle, applyModifyDrag |
| js/canvas-resize-logic.js | 68 | Handles de resize del lienzo: getCanvasResizeHandle, applyCanvasResizeDrag |
| js/canvas-setup.js | 51 | createCheckerPattern, startApp, setupScreen, setupLogicalCanvas |
| js/palette.js | 125 | Paleta de colores: initPalette, renderPalette, savePalette |
| js/layers.js | 374 | Capas: addLayer, mergeLayerDown, updateLayersUI, updateThumbnails |
| js/bucket.js | 232 | Cubeta: executeBucket (flood-fill), buildBucketPanel |
| js/pointer-events.js | 586 | handlePointerDown, handlePointerMove, handlePointerUp — enrutador central |
| js/brush-drawing.js | 280 | drawPoint, smoothLassoPath, executeLassoFill — motor de pintura |
| js/push-tool.js | 133 | Herramienta Empujar: endPushSession, executePush |
| js/shape-render.js | 207 | Figuras + stabilizer: constrainShape, drawShapeOnCtx, renderStamp, stabilizePoint |
| js/render.js | 387 | Loop de renderizado principal: drawLayerContent, render |
| js/tools.js | 211 | Gestión herramientas: selectTool, syncBrushUI, pickColorAt, updateEyedropperPreview |
| js/shortcuts.js | 278 | Atajos: handleGlobalShortcuts, toggleMenu, saveShortcuts, loadShortcuts |

---

## INDICE DE FUNCIONES POR ARCHIVO

### js/globals.js
- requestRender() — solicita frame de animación
- updateLayersCache(limit) — cache de composición de capas inferiores
- createProceduralAirbrushTexture() — genera textura aerógrafo sin archivos externos
- DATOS: toolsData[], brushTypesData[], blendModes[]
- ESTADO: viewScale, viewPosX/Y, viewRotation, layers[], selectedLayerIndex
- ESTADO: currentTool, currentBrush, selectedColor, hasSelection, historyStack

### js/history.js
- captureHistoryState() — snapshot completo del estado
- pushHistory() — agrega snapshot al stack (máx 40)
- restoreHistoryState(snapshot) — restaura layers, selección, transformaciones
- undo() — va al estado anterior
- redo() — va al estado siguiente

### js/init.js
- resetImportButton() / resetLayerImportButton()
- init() — conecta TODOS los event listeners de la UI
  Incluye: sliders (tamaño, opacidad, blur, stabilizer, presión, velocidad)
  botones (nueva capa, duplicar, fondo, mover, resize, filtros, fullscreen)
  presets popup, drag&drop de archivos, paste, keyboard handlers
  buildSelectionUI(), initPalette(), loadShortcuts()

### js/filters.js
- selectChromaLasso(mode) — activa modo lasso del chroma key
- openFilterModal(type) — abre modal y construye UI del filtro
- addFilterSlider(label, min, max, val, cb) — crea slider con botones +/-
- addFilterToggle(label, modes, current, cb) — crea botones toggle
- generateCurveLut(points, isSmooth) — genera look-up table para curvas
- addFilterCurveEditor(container) — editor SVG de curvas interactivo
- handleCurveMouseDown/Move/Up/DblClick() — interacción con puntos de curva
- updateCurveUI() — redibuja la línea SVG
- drawFilterHistogram() — dibuja histograma del canal
- makeDraggable(el, handle) — hace el modal arrastrable
- applyFilters() — aplica filtro activo (blackwhite/levels/hue/edges/invert/sharpen/gauss/posterize/outline/chroma)
- commitFilter() — confirma y guarda historial
- cancelFilter() — restaura estado original
- rgbToHsl(r,g,b) / hslToRgb(h,s,l) — conversiones de color

### js/canvas-resize-modal.js
- toggleFullscreen() — pantalla completa
- openResizeModal() — abre el panel de resize
- resizeCanvas(newW, newH, anchor) — ejecuta redimensionado con reposicionado de capas
- Listeners: resize-cancel-btn, resize-apply-btn, anchor dots

### js/save-system.js
- saveToSlot(id) — guarda en IndexedDB con thumbnail 160x90
- loadFromSlot(id) — carga desde IndexedDB
- renderSaveSlots() — construye UI de 15 ranuras con thumbnails

### js/selection-ui.js
- buildSelectionUI() — crea botones flotantes: lassoSelBtn, lassoDesBtn, modifySelBtn, fitScreenBtn, clearSelBtn, shapeFillBtn, shapeFromCenterBtn, shapeModifiableBtn
- updateShapeFromCenterUI() — actualiza botón "Desde Centro"
- updateShapeModifiableUI() — actualiza botón "Modificable"
- showSelectionButtons(tool) — muestra/oculta botones según herramienta

### js/selection-mask.js
- ensureSelectionCanvas() — crea selectionCanvas si no existe
- makeSelectionCrisp() — binariza máscara (elimina antialiasing)
- addPathToSelection(path) — añade polígono a la selección
- subtractPathFromSelection(path) — quita polígono de la selección
- clearSelection() — borra selección y confirma transforms pendientes
- updateSelectionOutline() — dibuja contorno magenta
- squarePath(ax, ay, bx, by) — crea path rectangular
- initModifySelection() — captura píxeles para transformación
- flipSelection(axis) — voltea h/v
- togglePerspectiveMode() / initPerspectiveCorners()
- worldToScreen(wx, wy) — convierte coords mundo a pantalla
- updateFlipButtonsPosition() — posiciona botones flip
- captureLayerSelection(layer, bounds) — extrae región seleccionada de capa
- getSelectionBounds() — calcula bounding box de la selección

### js/modify-selection.js
- drawTexturedTriangle(ctx, img, u0,v0,u1,v1,u2,v2, x0,y0,x1,y1,x2,y2) — triangle affine warp
- renderPerspectiveWarpPreview(destCtx, srcCanvas, corners) — malla 10x10 de perspectiva
- applyPerspectiveWarpToLayer(targetCtx, srcCanvas, corners) — aplica permanentemente
- commitModifySelection() — confirma transform (normal o perspectiva), escribe en capas

### js/clipboard-export.js
- compositeLayers(destCtx) — composita capas con clipping masks
- getFlatImage() — canvas plano de todas las capas
- downloadImage() — descarga PNG con timestamp
- handleIncomingFile(file) — procesa imagen entrante (drag/paste/browse)
- importAsNewLayer(img) — importa imagen como capa flotante
- copyFlatImageToClipboard() — copia imagen completa
- copyToClipboard() — copia selección (modos: capa/todas/canvas)
- cutToClipboard() — corta selección
- pasteFromClipboard(pasteInPlace) — pega imagen
- getModifyHandle(wx, wy) — detecta qué handle de transform se está tocando: 'tl','tc','tr','ml','mr','bl','bc','br','move','rot','pc0-pc3'
- applyModifyDrag(dx, dy, handle, origB, shiftKey, worldX, worldY) — calcula nueva bounding box

### js/canvas-resize-logic.js
- getCanvasResizeHandle(wx, wy) — detecta handle del resize del lienzo
- applyCanvasResizeDrag(dx, dy, handle, origW, origH) — calcula nuevas dimensiones

### js/canvas-setup.js
- createCheckerPattern() — patrón tablero para fondos transparentes
- startApp(w, h, initialImg) — lanza la app: oculta startup modal, llama setupLogicalCanvas, pushHistory
- setupScreen() — adapta canvas al tamaño de ventana
- setupLogicalCanvas(initialImg) — crea buffers, capa inicial, viewScale inicial

### js/palette.js
- initPalette() — carga de localStorage y construye la UI de paleta
- renderPalette() — redibuja grilla de colores (5 cols, N filas)
- savePalette() — guarda en localStorage ('illustrator_palette_v2')
- checkAndExpandPalette(index) — añade fila si la última está llena
- showColorContextMenu(x, y, index) — menú: Eliminar / Asignar Atajo / Copiar hex
- checkAndAssignColorShortcut(index, key) — asigna tecla a color
- checkAndShrinkPalette() — elimina filas vacías al final

### js/layers.js
- addLayer(name, fromCanvas) — crea capa nueva (vacía o desde lienzo)
- moveLayerContent() — usa modSelCanvas para mover contenido de capa
- duplicateSelectedLayer() — copia la capa activa encima de ella
- updateBgUI() / toggleBackground() — cicla entre bg transparente/blanco/color
- mergeLayerDown(index) — fusiona capa[index] con capa[index-1]
- updateThumbnails() — regenera miniaturas (32x18px) para todas las capas
- updateLayersUI() — reconstruye el panel de capas completo:
  * Drag & drop de reorden, slider de opacidad, selector de blend mode
  * Toggle de visibilidad, rename, clipping mask, alpha lock, eliminar
  * Sincroniza qAlpha/qClip botones rápidos

### js/bucket.js
- executeBucket(worldX, worldY) — flood fill desde coordenadas mundo
  * bucketMode: 'capa' | 'lienzo' (fuente de muestra)
  * bucketContiguous: true=flood fill, false=reemplazo global
  * bucketFillMode: 'solid' | 'erase'
  * bucketTolerance: 0-255
- buildBucketPanel() — panel flotante con toggles de configuración
- showBucketPanel(show) — muestra/oculta el panel

### js/pointer-events.js
- handlePointerDown(e) — inicio de evento de entrada
  Enruta a: zoom/pan/rotate, eyedropper, bucket, lazo-sel, lazo-des,
  modify-sel (initModifySelection), canvas-resize, shape, smudge, push, pincel normal
- handlePointerMove(e) — durante el movimiento
  Gestiona: stabilizer realtime, lasso path, modify sel drag, canvas resize drag,
  smudge buffer, push execution, shape preview, brush drawPoint
- handlePointerUp(e) — fin de evento
  Confirma: post-stabilization stroke, push session, lasso fill,
  shape commit (modificable o no), selection update, history push

### js/brush-drawing.js
- smoothLassoPath(pts, passes) — suavizado Gaussiano de path de lasso
- smoothStrokePath(pts, passes) — suavizado del stroke de post-stabilización
- executeLassoFill() — rellena/borra con polígono del lasso
- drawPoint(x, y, pressure) — dibuja stamp del pincel
  Modos soportados: duro, suave, aerógrafo (duro/suave), borrador, borrador-suave,
  smudge (difuminar arrastre), gauss blur (difuminar gaussiano)

### js/push-tool.js
- endPushSession() — libera pushSnapshot y pushDisplacementX/Y
- executePush(worldX, worldY, dx, dy) — desplaza píxeles con falloff radial

### js/shape-render.js
- constrainShape(x1, y1, x2, y2) — snap 45° para línea, proporciones iguales para rect/elipse
- drawShapeOnCtx(tctx, x1, y1, x2, y2) — dibuja línea/rect/elipse según currentBrush.shapeType
- updateTintedTexture() — pre-tinta la textura de aerógrafo con selectedColor
- renderStamp(tctx, x, y, size, alpha) — dibuja un stamp del pincel con opacity y blur
- stabilizePoint(x, y, p, strength) — weighted average del punto nuevo con stabPoints[]
- drawStabLineTo(sx, sy, sp, ex, ey, ep) — interpola y dibuja segmentos estabilizados
- hexToRgba(hex, alpha) — convierte '#rrggbb' + alpha a 'rgba(r,g,b,a)'

### js/render.js
- drawLayerContent(targetCtx, layerObj) — copia canvas de capa a destino
- render() — frame principal de renderizado:
  1. Prepara transform de cámara (viewScale, viewPosX/Y, viewRotation)
  2. Dibuja fondo (checker/color sólido/transparente)
  3. updateLayersCache() para capas inferiores a la activa
  4. Dibuja capa activa con strokeCanvas superpuesto
  5. Dibuja capas superiores
  6. Dibuja handles de Modify Selection (8 handles + rotación + perspectiva)
  7. Dibuja handles de Canvas Resize
  8. Dibuja lasso path en tiempo real
  9. Dibuja selectionOutlineCanvas (contorno magenta)
  10. Dibuja cursor personalizado
  11. Dibuja debug background de Chroma Key si está activo

### js/tools.js
- resetRotation() — viewRotation = 0 y oculta botón reset
- syncBrushUI() — actualiza sizeSlider, opacitySlider, blurSlider con currentBrush
- selectTool(id, name) — cambia currentTool, actualiza cursor, llama showSelectionButtons,
  gestiona panels (bucket, flip controls), resetea estados anteriores
- rgbToHex(r, g, b) — '#rrggbb'
- hexToRgbArray(hex) — [r, g, b]
- pickColorAt(worldX, worldY) — muestra el color compuesto (todas las capas)
- pickColorRaw(worldX, worldY) — color de la capa activa solamente
- updateEyedropperPreview(sx, sy, wx, wy) — actualiza el círculo de preview del gotero

### js/shortcuts.js
- handleGlobalShortcuts(e) — maneja teclas globales:
  Ctrl+Z=undo, Ctrl+Y/Ctrl+Shift+Z=redo
  Ctrl+C=copy, Ctrl+X=cut, Ctrl+V=paste, Ctrl+Shift+V=pasteInPlace
  Teclas de herramientas (z/x/r/b/n/j/m/t) y pinceles (a/c/s/e/d/q/w/f/g/h/v/l/ñ)
  Nueva capa (newLayerShortcut), atajos de color de paleta
  Menús: configShortcut abre configMenu, etc.
- toggleMenu(m) — abre m si estaba cerrado, cierra todos si m=null
- setupMultiToolMenu() — construye lista de herramientas
- setupBrushMenu() — construye lista de pinceles
- renderMenuList(cont, data, type) — genera items de menú con atajos editables
- checkAndAssignShortcut(item, key, type) — asigna atajo con click derecho
- saveShortcuts() — guarda en localStorage ('illustrator_shortcuts_v2')
- loadShortcuts() — carga de localStorage y aplica a toolsData/brushTypesData

---

## VARIABLES GLOBALES CLAVE

| Variable | Tipo | Descripción |
|---|---|---|
| canvas | HTMLCanvasElement | Canvas principal visible |
| ctx | CanvasRenderingContext2D | Contexto del canvas principal |
| layers | Array | Capas: {id, name, canvas, ctx, opacity, visible, blendMode, clippingMask, alphaLocked} |
| selectedLayerIndex | int | Índice de la capa activa |
| currentTool | string | 'pincel','bucket','eyedropper','pan','zoom','rotate','lazo-sel','lazo-des','modify-sel','none' |
| currentBrush | object | Brush activo de brushTypesData[] |
| selectedColor | string | Color activo '#rrggbb' |
| viewScale | float | Zoom del lienzo |
| viewPosX/Y | float | Posición de la cámara |
| viewRotation | float | Rotación en radianes |
| paperWidth/Height | int | Dimensiones lógicas del canvas |
| hasSelection | bool | Si hay selección activa |
| selectionCanvas | canvas | Máscara: blanco=seleccionado, transparente=no |
| modSelInitialized | bool | Si hay transformación activa |
| modSelBounds | object | {x, y, w, h} bounding box de la transformación |
| historyStack | Array | Stack de snapshots (máx 40) |
| historyIndex | int | Posición actual en historial |
| strokeCanvas | canvas | Buffer del trazo en tiempo real |
| baseBrushSize | float | Tamaño del pincel actual |
| brushOpacity | float | Opacidad 0-1 |
| stabEnabled | int | Nivel de stabilización 0-10 |
| stabMode | string | 'post' | 'realtime' |

---

## FLUJOS DE EVENTOS PRINCIPALES

Trazo de pincel:
pointerdown → handlePointerDown → isDrawing=true → drawPoint
pointermove → handlePointerMove → drawPoint (realtime stab) / rawStrokePath.push (post stab)
pointerup → handlePointerUp → [post-stab: smoothStrokePath → drawStabLineTo] → pushHistory → requestRender

Filtro:
click filtro → openFilterModal(type) → applyFilters (preview live)
→ commitFilter → pushHistory | cancelFilter → restaura datos originales

Undo/Redo:
Ctrl+Z → undo → historyIndex-- → restoreHistoryState → updateLayersUI → requestRender

Guardar proyecto:
click GUARDAR → saveToSlot(id) → IndexedDB.put → renderSaveSlots
click CARGAR → loadFromSlot(id) → IndexedDB.get → setupLogicalCanvas → layers[] → pushHistory

---

## ESTRUCTURA DEL PROYECTO

ANTIGRAVITY CPT/
 index.html     <- HTML principal (carga módulos en orden al final del body)
 style.css      <- Estilos globales
 GUIA.md        <- Este archivo
 app.js         <- ARCHIVO ORIGINAL (respaldo, no se carga)
 js/            <- Todos los módulos
  globals.js, history.js, init.js, filters.js,
  canvas-resize-modal.js, save-system.js,
  selection-ui.js, selection-mask.js, modify-selection.js,
  clipboard-export.js, canvas-resize-logic.js, canvas-setup.js,
  palette.js, layers.js, bucket.js, pointer-events.js,
  brush-drawing.js, push-tool.js, shape-render.js,
  render.js, tools.js, shortcuts.js
