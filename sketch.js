// Sphere v08 — same as v07, tuned for weak GPUs. The additive canvas render is
// fill-rate + draw-call bound, so: each point / particle is a single merged
// sprite (bright core + glow baked in) instead of two draws; the membrane is
// drawn at half density; and an adaptive governor raises the point stride when
// the frame rate drops, keeping it smooth on slow machines (full quality on
// fast ones and always for the PNG/video export).

const N_POINTS = 11000;    // default number of points on the sphere shell
const N_BUCKETS = 32;      // pre-tinted sphere sprites (A→B gradient)
const SPRITE_PX = 96;      // offscreen size of each sprite
const DISP = 0.34;         // radial displacement as a fraction of base radius
const MAX_FLOAT = 3000;    // capacity of the floating-particle pool

let dirs = [];             // unit direction of each sphere point
let coreSprites = [];      // merged crisp-core + glow sprite, one per colour bucket
let membraneSprite = null; // soft bloom in the membrane colour (single colour)

// Floating particles (screen space).
let fx, fy, fvx, fvy;      // position / velocity
let ax, ay;                // fixed anchor (its spot in the floating cloud)
let hx, hy;                // home = anchor + a small wobble; the particle springs to it
let fesc;                  // fixed random threshold [0,1); low = penetrates first
let fAlpha;                // opacity
let fInside;               // 1 = the particle now lives (floats) inside the sphere
let floatGlow = null, floatCore = null;  // outside (floating) particle sprites
let insideGlow = null, insideCore = null; // inside (absorbed) particle sprites
let floatT = 0;            // flow-field time
let floatReady = false;    // spread particles once the canvas has its real size
let cursorOver = false;    // is the mouse actually hovering the canvas?

// UV grid (rows × cols) — geometry for the line / fill render modes.
let gridDirs = [];
let gRows = 0, gCols = 0;
let gPX = null, gPY = null, gA = null;   // per-vertex projected x/y and rim alpha

// Performance: a frozen noise shape (skips ~16k noise() calls/frame) and a
// low-resolution render buffer (cuts the additive-blend fill-rate).
let noiseField = null;     // precomputed noise per sphere point (static shape)
let gridNoiseField = null; // precomputed noise per grid vertex (static shape)
let lowBuf = null, lowCtx = null;   // offscreen buffer for the Render-scale down-render

// ── UI-controlled settings ──────────────────────────────────────────────────
// These are ALL initialised from the matching input in index.html at setup()
// (see the bind() calls). To change a default, edit only the `value="…"` in
// index.html — nothing here needs touching.
let sphereCount, renderMode;
let noiseScaleVal, noiseOffsetX, noiseOffsetY, noiseSpeed;
let glow, pointSize, hollow, renderScale, staticShape;
let gradDiameter, gradDensity, particleBlend;
let particlesOn, particleCount, pullForce, floatTrail, reach, cloudSize, breakthrough;
let membraneOn, membraneGap, membraneOpacity, membraneDelay;
// ─────────────────────────────────────────────────────────────────────────────

let noiseHist = [];
let membNT = 0;
let noiseT = 0;
let rot = 0;

let playing = true;
let mediaRecorder = null;
let recordedChunks = [];
let isRecording = false;
let recordingHdCanvas = null;
let recordingHdCtx = null;
let recTimer = null, recStartMs = 0;   // in-button recording seconds counter

function calcCanvas(ratioStr) {
  const [a, b] = ratioStr.split(':').map(Number);
  const container = document.getElementById('canvas-container');
  const maxW = container.clientWidth;
  const maxH = container.clientHeight;
  let w = maxW, h = w * (b / a);
  if (h > maxH) { h = maxH; w = h * (a / b); }
  return [Math.round(w), Math.round(h)];
}

function currentRatio() {
  return document.getElementById('sel-ratio').value;
}

// Fibonacci sphere — an even spread of `count` unit vectors over the sphere.
function buildPoints(count) {
  dirs = new Array(count);
  const ga = Math.PI * (3 - Math.sqrt(5));
  for (let i = 0; i < count; i++) {
    const y = 1 - (i / (count - 1)) * 2;
    const r = Math.sqrt(Math.max(0, 1 - y * y));
    const th = i * ga;
    dirs[i] = { x: Math.cos(th) * r, y: y, z: Math.sin(th) * r };
  }
}

// UV lat/long grid whose resolution scales with the density slider (used by the
// wireframe / rings / meridians / fill modes so they have proper connectivity).
function buildGrid(density) {
  gRows = Math.round(constrain(Math.sqrt(density) * 0.62, 14, 72));
  gCols = gRows * 2;
  gridDirs = new Array(gRows * gCols);
  let idx = 0;
  for (let r = 0; r < gRows; r++) {
    const phi = (r / (gRows - 1)) * Math.PI;   // 0..π latitude
    const y = Math.cos(phi), rr = Math.sin(phi);
    for (let c = 0; c < gCols; c++) {
      const th = (c / gCols) * Math.PI * 2;
      gridDirs[idx++] = { x: Math.cos(th) * rr, y: y, z: Math.sin(th) * rr };
    }
  }
  gPX = new Float32Array(gRows * gCols);
  gPY = new Float32Array(gRows * gCols);
  gA = new Float32Array(gRows * gCols);
}

// Precompute the noise value of every point/vertex ONCE (frozen shape). The
// per-frame render then only rotates + projects — no noise() at all.
function buildNoiseField() {
  const freq = map(noiseScaleVal, 1, 100, 0.4, 5.0);
  const offX = noiseOffsetX * 0.01, offY = noiseOffsetY * 0.01;
  noiseField = new Float32Array(sphereCount);
  for (let i = 0; i < sphereCount; i++) {
    const d = dirs[i];
    noiseField[i] = noise(d.x * freq + offX, d.y * freq + offY, d.z * freq + noiseT);
  }
  const gn = gRows * gCols;
  gridNoiseField = new Float32Array(gn);
  for (let i = 0; i < gn; i++) {
    const d = gridDirs[i];
    gridNoiseField[i] = noise(d.x * freq + offX, d.y * freq + offY, d.z * freq + noiseT);
  }
}

// Allocate the floating-particle pool and scatter it around the sphere.
function buildFloaters() {
  fx = new Float32Array(MAX_FLOAT); fy = new Float32Array(MAX_FLOAT);
  fvx = new Float32Array(MAX_FLOAT); fvy = new Float32Array(MAX_FLOAT);
  ax = new Float32Array(MAX_FLOAT); ay = new Float32Array(MAX_FLOAT);
  hx = new Float32Array(MAX_FLOAT); hy = new Float32Array(MAX_FLOAT);
  fesc = new Float32Array(MAX_FLOAT); fAlpha = new Float32Array(MAX_FLOAT);
  fInside = new Uint8Array(MAX_FLOAT);
  for (let i = 0; i < MAX_FLOAT; i++) {
    fesc[i] = Math.random();
    respawnFloater(i);
  }
}

// Send every particle back to a fresh floating spot outside the sphere.
function resetFloaters() {
  for (let i = 0; i < MAX_FLOAT; i++) respawnFloater(i);
}

// Place particle i (and its home) at a random spot on the canvas, outside the sphere.
function respawnFloater(i) {
  const cx = width / 2, cy = height / 2;
  const R = Math.min(width, height) * 0.29;
  let x, y, dc, tries = 0;
  do {
    x = random(4, width - 4); y = random(4, height - 4);
    dc = Math.hypot(x - cx, y - cy); tries++;
  } while (dc < R * 1.25 && tries < 10);
  fx[i] = x; fy[i] = y;
  ax[i] = x; ay[i] = y;
  hx[i] = x; hy[i] = y;
  fvx[i] = random(-1, 1); fvy[i] = random(-1, 1);
  fAlpha[i] = 1;
  if (fInside) fInside[i] = 0;
}

function makeSprite(r, g, bl, stops) {
  const cv = document.createElement('canvas');
  cv.width = SPRITE_PX; cv.height = SPRITE_PX;
  const cx = cv.getContext('2d');
  const cen = SPRITE_PX / 2;
  const grad = cx.createRadialGradient(cen, cen, 0, cen, cen, cen);
  for (const [pos, a] of stops) grad.addColorStop(pos, `rgba(${r},${g},${bl},${a})`);
  cx.fillStyle = grad;
  cx.fillRect(0, 0, SPRITE_PX, SPRITE_PX);
  return cv;
}

// One MERGED sprite per colour bucket: a crisp bright core baked into a soft
// glow halo, so each point is a single drawImage instead of two (≈40% fewer
// additive draws — the dominant cost). `coreStop` keeps the grain crisp.
function buildSprites() {
  const ca = color(document.getElementById('colorAPick').value);
  const cb = color(document.getElementById('colorBPick').value);
  const gCore = map(glow, 1, 100, 0.16, 0.5);
  const coreStop = map(pointSize, 1, 100, 0.09, 0.5);

  coreSprites = new Array(N_BUCKETS);   // reused as the merged sprite set
  for (let b = 0; b < N_BUCKETS; b++) {
    const t = b / (N_BUCKETS - 1);
    const c = lerpColor(ca, cb, t);
    const r = Math.round(red(c)), g = Math.round(green(c)), bl = Math.round(blue(c));
    coreSprites[b] = makeSprite(r, g, bl, [
      [0.0, 0.98], [coreStop, 0.92], [coreStop * 1.7, gCore],
      [0.5, gCore * 0.35], [0.78, gCore * 0.1], [1.0, 0]
    ]);
  }

  // Membrane bloom in its own colour.
  const mc = color(document.getElementById('membraneColorPick').value);
  membraneSprite = makeSprite(Math.round(red(mc)), Math.round(green(mc)), Math.round(blue(mc)), [
    [0.0, gCore], [0.30, gCore * 0.5], [0.6, gCore * 0.12], [1.0, 0]
  ]);
}

// Single-colour sprite pair (soft glow + crisp core) in the given colour.
function buildParticleSprites(hex) {
  const c = color(hex);
  const r = Math.round(red(c)), g = Math.round(green(c)), bl = Math.round(blue(c));
  return [
    makeSprite(r, g, bl, [[0.0, 0.5], [0.4, 0.18], [1.0, 0]]),
    makeSprite(r, g, bl, [[0.0, 0.95], [0.5, 0.85], [0.75, 0.2], [1.0, 0]])
  ];
}

// Sprites for outside (floating) and inside (absorbed) particles.
function buildFloatSprites() {
  [floatGlow, floatCore] = buildParticleSprites(document.getElementById('floatColorPick').value);
  [insideGlow, insideCore] = buildParticleSprites(document.getElementById('insideColorPick').value);
}

// Read a control's current value into a global (so defaults live in index.html)
// and keep it in sync on every change. `onChange` runs any needed rebuild;
// `isToggle` reads a checkbox's checked state instead of its value.
function bind(id, setter, onChange, isToggle) {
  const el = document.getElementById(id);
  const read = () => (isToggle ? el.checked : el.value);
  setter(read());                                    // apply the HTML default now
  const run = () => { setter(read()); if (onChange) onChange(); };
  el.addEventListener('input', run);
  el.addEventListener('change', run);
}

function setup() {
  const [cW, cH] = calcCanvas(currentRatio());
  createCanvas(cW, cH).parent('canvas-container');
  pixelDensity(1);
  colorMode(RGB, 255);

  // Rebuild the frozen noise field when a noise-shaping control changes (only matters in static mode).
  const refreshField = () => { if (staticShape) buildNoiseField(); };

  // Every tunable is read from its HTML input — defaults live only in index.html.
  bind('noise-seed-slider', v => noiseSeed(+v), refreshField);
  bind('noise-scale-slider', v => noiseScaleVal = +v, refreshField);
  bind('noise-x-slider', v => noiseOffsetX = +v, refreshField);
  bind('noise-y-slider', v => noiseOffsetY = +v, refreshField);
  bind('noise-speed-slider', v => noiseSpeed = +v * 0.001);
  bind('glow-slider', v => glow = +v, buildSprites);
  bind('pointsize-slider', v => pointSize = +v, buildSprites);
  bind('density-slider', v => sphereCount = +v, () => { buildPoints(sphereCount); buildGrid(sphereCount); refreshField(); });
  bind('render-mode', v => renderMode = v);
  bind('render-scale-slider', v => renderScale = +v);
  bind('static-shape-toggle', v => staticShape = v, () => { if (staticShape) buildNoiseField(); }, true);
  bind('hollow-slider', v => hollow = +v);
  bind('grad-diameter-slider', v => gradDiameter = +v);
  bind('grad-density-slider', v => gradDensity = +v);
  bind('particle-blend', v => particleBlend = v);
  bind('particles-toggle', v => particlesOn = v, null, true);
  bind('count-slider', v => particleCount = +v);
  bind('pull-slider', v => pullForce = +v);
  bind('elastic-slider', v => floatTrail = +v);
  bind('reach-slider', v => reach = +v);
  bind('cloud-size-slider', v => cloudSize = +v);
  bind('breakthrough-slider', v => breakthrough = +v);
  bind('membrane-toggle', v => membraneOn = v, null, true);
  bind('membrane-gap-slider', v => membraneGap = +v);
  bind('membrane-opacity-slider', v => membraneOpacity = +v);
  bind('membrane-delay-slider', v => membraneDelay = +v);

  // Build geometry + sprites from the values just read.
  buildFloaters();
  buildPoints(sphereCount);
  buildGrid(sphereCount);
  buildNoiseField();
  buildSprites();
  buildFloatSprites();

  select("#reset-particles").mousePressed(resetFloaters);
  select("#play-pause").mousePressed(togglePlay);
  select("#record-btn").mousePressed(toggleRecording);
  select("#export-png").mousePressed(exportPNG);

  document.getElementById('sel-ratio').addEventListener('change', function () {
    const [cW, cH] = calcCanvas(currentRatio());
    resizeCanvas(cW, cH);
    resetFloaters();
  });

  // Track whether the cursor is genuinely over the canvas (mouseX/Y default to
  // 0,0, which would otherwise pull every particle into the top-left corner).
  const cnv = document.querySelector('#canvas-container canvas');
  cnv.addEventListener('mouseenter', function () { cursorOver = true; });
  cnv.addEventListener('mouseleave', function () { cursorOver = false; });

  loop();   // always animating so floaters + interaction stay live
}

// Called from index.html when any colour changes.
window.onColorChange = function () { buildSprites(); buildFloatSprites(); };

function togglePlay() {
  playing = !playing;
  document.getElementById('play-pause').textContent = playing ? '⏸ Pause' : '▶ Play';
}

// Return the value of noiseT as it was `delayMs` ago (from the history log).
function delayedNoiseT(now, delayMs) {
  const target = now - delayMs;
  let v = noiseHist.length ? noiseHist[0].v : noiseT;
  for (let i = 0; i < noiseHist.length; i++) {
    if (noiseHist[i].t <= target) v = noiseHist[i].v; else break;
  }
  return v;
}

function draw() {
  // In static-shape mode the noise is frozen (no per-frame recompute) — only the
  // rotation advances, so the fixed organic blob just spins.
  if (playing) { if (!staticShape) noiseT += noiseSpeed; rot += 0.0035; }
  floatT += 0.006;

  // Log noiseT so the membrane can sample a delayed value; keep ~6 s of history.
  const now = millis();
  noiseHist.push({ t: now, v: noiseT });
  while (noiseHist.length > 1 && noiseHist[0].t < now - 6000) noiseHist.shift();
  membNT = delayedNoiseT(now, membraneDelay);

  if (!floatReady) { resetFloaters(); floatReady = true; }
  if (particlesOn) updateFloaters();

  // Render scale < 100% renders the whole (fill-rate heavy) additive scene into a
  // smaller offscreen buffer and upscales it — the glow is soft so it stays close,
  // but the additive blend touches far fewer pixels. Full quality for exports.
  const rs = renderScale / 100;
  if (rs > 0.999) {
    renderScene(drawingContext, width, height, true, 1, 1);
  } else {
    const bw = Math.max(2, Math.round(width * rs)), bh = Math.max(2, Math.round(height * rs));
    if (!lowBuf) { lowBuf = document.createElement('canvas'); lowCtx = lowBuf.getContext('2d'); }
    if (lowBuf.width !== bw || lowBuf.height !== bh) { lowBuf.width = bw; lowBuf.height = bh; }
    renderScene(lowCtx, bw, bh, true, rs, 1);
    const dc = drawingContext;
    dc.globalCompositeOperation = 'source-over';
    dc.globalAlpha = 1;
    dc.imageSmoothingEnabled = true;
    dc.drawImage(lowBuf, 0, 0, width, height);
  }

  if (isRecording && recordingHdCtx) {
    recordingHdCtx.clearRect(0, 0, recordingHdCanvas.width, recordingHdCanvas.height);
    recordingHdCtx.drawImage(drawingContext.canvas, 0, 0, recordingHdCanvas.width, recordingHdCanvas.height);
  }
}

// Advance the floating-particle physics (uses the live canvas + cursor).
// Each particle springs to a slowly drifting "home" (its floating anchor) so a
// swarm gathered by the cursor spreads back out once the cursor leaves. Points
// that penetrate the membrane get a home inside the sphere and float in there.
function updateFloaters() {
  const cx = width / 2, cy = height / 2;
  const minDim = Math.min(width, height);
  const R = minDim * 0.29;
  const gapWorld = minDim * map(membraneGap, 0, 100, 0.0, 0.05);
  const Rmem = R + gapWorld + minDim * 0.015;   // barrier radius

  const overC = cursorOver;
  const captureR = map(reach, 1, 100, minDim * 0.18, minDim * 0.65);
  const grabAmt = map(pullForce, 1, 100, 0.09, 0.22);       // how firmly captured particles are pulled into their cloud slot
  const returnEase = map(floatTrail, 1, 100, 0.09, 0.03);   // higher trail = slower, softer return
  const maxSp = minDim * 0.022;
  const wanderR = minDim * 0.025;
  const cloudR = captureR * map(cloudSize, 1, 100, 0.0, 1.4);   // 0 = tight ball on the cursor … large = wide filled cloud
  const frac = breakthrough / 100;
  const cursorInside = overC && Math.hypot(mouseX - cx, mouseY - cy) < Rmem * 1.1;

  for (let i = 0; i < particleCount; i++) {
    // Home = the particle's fixed anchor plus a small INDEPENDENT wobble. The
    // cloud keeps its spread (no drift to edges, no streaky filaments) and a
    // released particle returns to its own spot.
    const a = noise(i * 0.123, floatT * 0.5) * Math.PI * 4;
    hx[i] = ax[i] + Math.cos(a) * wanderR;
    hy[i] = ay[i] + Math.sin(a) * wanderR;

    // Cursor capture weight: 1 next to the cursor, 0 at the edge of reach.
    const canFollow = fInside[i] ? cursorInside : overC;
    let w = 0;
    if (canFollow) {
      const d = Math.hypot(mouseX - fx[i], mouseY - fy[i]);
      if (d < captureR) {
        w = 1 - d / captureR;
        // Ease toward a personal slot that fills the cloud disc around the cursor
        // (√fesc = even fill, no empty centre). Cloud size 0 → every slot is the
        // cursor → a tight ball; larger → a wide filled cloud.
        const ang = i * 2.39996 + floatT * 0.5;
        const rad = cloudR * Math.sqrt(fesc[i]);
        const tx = mouseX + Math.cos(ang) * rad, ty = mouseY + Math.sin(ang) * rad;
        const grab = grabAmt * w;
        fx[i] += (tx - fx[i]) * grab;
        fy[i] += (ty - fy[i]) * grab;
      }
    }

    // Residual velocity (from membrane slides / edges) just decays.
    fvx[i] *= 0.85; fvy[i] *= 0.85;
    fx[i] += fvx[i]; fy[i] += fvy[i];

    // Ease back home when the cursor isn't holding it (no spring → no rebound).
    // (1-w)² so even a moderately-captured particle commits to its cloud slot.
    const ease = returnEase * (1 - w) * (1 - w);
    fx[i] += (hx[i] - fx[i]) * ease;
    fy[i] += (hy[i] - fy[i]) * ease;

    // Membrane: contain / cross.
    const rx = fx[i] - cx, ry = fy[i] - cy, dc = Math.hypot(rx, ry) || 0.0001;
    if (fInside[i]) {
      // Stay inside — stop at the inner wall and slide (no bounce).
      if (dc > Rmem) {
        fx[i] = cx + rx / dc * Rmem; fy[i] = cy + ry / dc * Rmem;
        const vr = fvx[i] * rx / dc + fvy[i] * ry / dc;
        if (vr > 0) { fvx[i] -= vr * rx / dc; fvy[i] -= vr * ry / dc; }
      }
    } else if (dc < Rmem) {
      const penetrator = fesc[i] < frac;
      if (penetrator && cursorInside) {
        // Cross into the sphere and adopt an anchor inside — it now floats in there.
        fInside[i] = 1;
        const ang = Math.random() * Math.PI * 2, rr = Math.random() * Rmem * 0.65;
        ax[i] = cx + Math.cos(ang) * rr; ay[i] = cy + Math.sin(ang) * rr;
        hx[i] = ax[i]; hy[i] = ay[i];
      } else {
        // Stop at the outer wall and slide along it (no bounce).
        fx[i] = cx + rx / dc * Rmem; fy[i] = cy + ry / dc * Rmem;
        const vr = fvx[i] * rx / dc + fvy[i] * ry / dc;
        if (vr < 0) { fvx[i] -= vr * rx / dc; fvy[i] -= vr * ry / dc; }
      }
    }

    // Stop at the canvas edges (outside particles only) — no bounce.
    if (!fInside[i]) {
      if (fx[i] < 0)      { fx[i] = 0;      if (fvx[i] < 0) fvx[i] = 0; }
      if (fx[i] > width)  { fx[i] = width;  if (fvx[i] > 0) fvx[i] = 0; }
      if (fy[i] < 0)      { fy[i] = 0;      if (fvy[i] < 0) fvy[i] = 0; }
      if (fy[i] > height) { fy[i] = height; if (fvy[i] > 0) fvy[i] = 0; }
    }

    // Speed clamp.
    const sp = Math.sqrt(fvx[i] * fvx[i] + fvy[i] * fvy[i]);
    if (sp > maxSp) { fvx[i] *= maxSp / sp; fvy[i] *= maxSp / sp; }
  }
}

// Draw the whole scene (sphere shell + membrane + floaters) onto ctx at W×H.
// `opaque` paints the dark background (transparent for PNG export); `scale`
// rescales positions/sizes when rendering at a different resolution.
function renderScene(ctx, W, H, opaque, scale, stride) {
  const cx = W / 2, cy = H / 2;
  const minDim = Math.min(W, H);
  const R = minDim * 0.29;
  const focal = R * 3.4;

  const freq = map(noiseScaleVal, 1, 100, 0.4, 5.0);
  const offX = noiseOffsetX * 0.01;
  const offY = noiseOffsetY * 0.01;

  // With a coarser stride each point covers for more, so grow it a little (but
  // not fully, so slow machines also draw fewer pixels overall).
  const sizeComp = Math.pow(stride, 0.4);
  const glowSize = minDim * map(glow, 1, 100, 0.008, 0.030) * sizeComp;
  const membSize = glowSize * 1.5 * Math.SQRT2;   // ×√2 to cover the half-density membrane
  const gapWorld = minDim * map(membraneGap, 0, 100, 0.0, 0.05);
  const membAlpha = membraneOpacity / 100;
  const rimPow = map(hollow, 0, 100, 0.15, 4.0);

  const cyR = Math.cos(rot), syR = Math.sin(rot);
  // Steep tilt: the auto-spin is around the pole axis, so tilting that axis into
  // the screen puts both (antipodal) poles near the disc centre, where the hollow
  // fade hides the "vortex" where the lines converge — while the spin stays lively.
  const tilt = 1.3, ct = Math.cos(tilt), st = Math.sin(tilt);

  // Background.
  ctx.globalCompositeOperation = 'source-over';
  ctx.globalAlpha = 1;
  if (opaque) { ctx.fillStyle = 'rgb(4,5,12)'; ctx.fillRect(0, 0, W, H); }
  else        { ctx.clearRect(0, 0, W, H); }

  // Radial background gradient — chosen colour at the centre fading to fully
  // transparent at the edge. Diameter = radius; density = strength / spread.
  if (gradDensity > 0) {
    const gc = color(document.getElementById('gradColorPick').value);
    const gr = Math.round(red(gc)), gg = Math.round(green(gc)), gb = Math.round(blue(gc));
    const gRad = Math.max(1, minDim * map(gradDiameter, 0, 100, 0.1, 1.6));
    const a0 = map(gradDensity, 0, 100, 0.0, 1.0);
    const grad = ctx.createRadialGradient(cx, cy, 0, cx, cy, gRad);
    grad.addColorStop(0.0, `rgba(${gr},${gg},${gb},${a0})`);
    grad.addColorStop(map(gradDensity, 0, 100, 0.15, 0.7), `rgba(${gr},${gg},${gb},${a0 * 0.35})`);
    grad.addColorStop(1.0, `rgba(${gr},${gg},${gb},0)`);
    ctx.fillStyle = grad;
    ctx.fillRect(0, 0, W, H);
  }

  ctx.globalCompositeOperation = 'lighter';

  // ── Sphere shell + membrane ──
  const geo = { cx, cy, R, focal, freq, offX, offY, rimPow, gapWorld, membAlpha,
                cyR, syR, ct, st, minDim, sizeComp, stride };
  if (renderMode === 'points') {
    const drawMemb = membraneOn && membAlpha > 0;
    for (let i = 0, k = 0; i < sphereCount; i += stride, k++) {
      const d = dirs[i];
      const n = staticShape ? noiseField[i] : noise(d.x * freq + offX, d.y * freq + offY, d.z * freq + noiseT);
      const rBase = R * (1 + (n - 0.5) * 2 * DISP);

      const rx = d.x * cyR + d.z * syR;
      const rz = -d.x * syR + d.z * cyR;
      const ry = d.y * ct - rz * st;
      const rz2 = d.y * st + rz * ct;

      const rim = 1 - Math.abs(rz2);
      const facing = map(rz2, -1, 1, 0.55, 1.0);
      const alpha = Math.pow(rim, rimPow) * facing;
      if (alpha < 0.004) continue;

      const bucket = Math.min(N_BUCKETS - 1, Math.max(0, Math.round(n * (N_BUCKETS - 1))));

      // Membrane — delayed-noise wobble, half density (every other drawn point;
      // it is a soft blur so the missing half is invisible, but saves a big draw).
      if (drawMemb && (k & 1) === 0) {
        const nm = staticShape ? n : noise(d.x * freq + offX, d.y * freq + offY, d.z * freq + membNT);
        const rm = R * (1 + (nm - 0.5) * 2 * DISP) + gapWorld;
        const perspM = focal / (focal - rz2 * rm);
        const mx = cx + rx * rm * perspM, my = cy + ry * rm * perspM;
        const ms = membSize * perspM;
        ctx.globalAlpha = alpha * membAlpha;
        ctx.drawImage(membraneSprite, mx - ms / 2, my - ms / 2, ms, ms);
      }

      // Point — one merged sprite (crisp core + glow) = a single additive draw.
      const persp = focal / (focal - rz2 * rBase);
      const sx = cx + rx * rBase * persp, sy = cy + ry * rBase * persp;
      const gs = glowSize * persp;
      ctx.globalAlpha = alpha;
      ctx.drawImage(coreSprites[bucket], sx - gs / 2, sy - gs / 2, gs, gs);
    }
  } else if (renderMode === 'spikes') {
    drawSpikes(ctx, geo, noiseT, 0, 1);
  } else {
    // Grid line / fill modes.
    const rowCols = gridRowColors();
    ctx.lineCap = 'round';
    if (membraneOn && membAlpha > 0) {
      const mHex = document.getElementById('membraneColorPick').value;
      const membCols = new Array(gRows).fill(mHex);
      projectGrid(geo, membNT, gapWorld);
      drawGridMode(ctx, geo, membCols, membAlpha * 0.75);
    }
    projectGrid(geo, noiseT, 0);
    drawGridMode(ctx, geo, rowCols, 1);
  }

  // ── Floating particles (soft glow + crisp core, full density) ──
  ctx.globalCompositeOperation = particleBlend;   // per-particle blend mode
  const fGlow = minDim * 0.018, fCore = minDim * 0.0055;
  for (let i = 0; particlesOn && i < particleCount; i++) {
    const al = fAlpha[i];
    if (al <= 0.004) continue;
    const sx = cx + (fx[i] - width / 2) * scale;
    const sy = cy + (fy[i] - height / 2) * scale;
    // White while floating outside; the inside colour once drawn into the sphere.
    const glowS = fInside[i] ? insideGlow : floatGlow;
    const coreS = fInside[i] ? insideCore : floatCore;
    ctx.globalAlpha = al * 0.7;
    ctx.drawImage(glowS, sx - fGlow / 2, sy - fGlow / 2, fGlow, fGlow);
    ctx.globalAlpha = al;
    ctx.drawImage(coreS, sx - fCore / 2, sy - fCore / 2, fCore, fCore);
  }

  ctx.globalAlpha = 1;
  ctx.globalCompositeOperation = 'source-over';
}

/* ── Alternate render modes (wireframe / rings / meridians / fill / spikes) ── */

// One colour per latitude row, lerped along the A→B gradient.
function gridRowColors() {
  const ca = color(document.getElementById('colorAPick').value);
  const cb = color(document.getElementById('colorBPick').value);
  const out = new Array(gRows);
  for (let r = 0; r < gRows; r++) {
    const c = lerpColor(ca, cb, gRows > 1 ? r / (gRows - 1) : 0);
    out[r] = `rgb(${red(c) | 0},${green(c) | 0},${blue(c) | 0})`;
  }
  return out;
}

// Project every grid vertex for a given noise time / radius offset into gPX/gPY/gA.
function projectGrid(g, useT, extraR) {
  const N = gRows * gCols;
  for (let i = 0; i < N; i++) {
    const d = gridDirs[i];
    const n = staticShape ? gridNoiseField[i] : noise(d.x * g.freq + g.offX, d.y * g.freq + g.offY, d.z * g.freq + useT);
    const rr = g.R * (1 + (n - 0.5) * 2 * DISP) + extraR;
    const rx = d.x * g.cyR + d.z * g.syR;
    const rz = -d.x * g.syR + d.z * g.cyR;
    const ry = d.y * g.ct - rz * g.st;
    const rz2 = d.y * g.st + rz * g.ct;
    const persp = g.focal / (g.focal - rz2 * rr);
    gPX[i] = g.cx + rx * rr * persp;
    gPY[i] = g.cy + ry * rr * persp;
    const rim = 1 - Math.abs(rz2);
    gA[i] = Math.pow(rim, g.rimPow) * map(rz2, -1, 1, 0.55, 1.0);
  }
}

// A glowing segment: a wide faint halo pass + a thin bright core pass (additive).
function glowLine(ctx, x0, y0, x1, y1, a, wCore, wHalo) {
  if (a <= 0.004) return;
  ctx.globalAlpha = a * 0.28; ctx.lineWidth = wHalo;
  ctx.beginPath(); ctx.moveTo(x0, y0); ctx.lineTo(x1, y1); ctx.stroke();
  ctx.globalAlpha = Math.min(1, a); ctx.lineWidth = wCore;
  ctx.beginPath(); ctx.moveTo(x0, y0); ctx.lineTo(x1, y1); ctx.stroke();
}

function drawGridMode(ctx, g, rowCols, alphaScale) {
  const wCore = g.minDim * 0.0016 * g.sizeComp * (0.6 + glow / 140);
  const wHalo = wCore * 4.5;
  const step = Math.max(1, g.stride);

  if (renderMode === 'fill') {
    // Translucent glowing shell — additive quads shaded by latitude & facing.
    for (let r = 0; r < gRows - 1; r += step) {
      ctx.fillStyle = rowCols[r];
      const b0 = r * gCols, b1 = (r + 1) * gCols;
      for (let c = 0; c < gCols; c += step) {
        const c2 = (c + step) % gCols;
        const i0 = b0 + c, i1 = b0 + c2, i2 = b1 + c2, i3 = b1 + c;
        const a = 0.25 * (gA[i0] + gA[i1] + gA[i2] + gA[i3]);
        if (a < 0.012) continue;
        ctx.globalAlpha = Math.min(1, a * 0.55 * alphaScale);
        ctx.beginPath();
        ctx.moveTo(gPX[i0], gPY[i0]); ctx.lineTo(gPX[i1], gPY[i1]);
        ctx.lineTo(gPX[i2], gPY[i2]); ctx.lineTo(gPX[i3], gPY[i3]);
        ctx.closePath(); ctx.fill();
      }
    }
    return;
  }

  const rings = renderMode === 'rings' || renderMode === 'wireframe';
  const meridians = renderMode === 'meridians' || renderMode === 'wireframe';
  const mStep = renderMode === 'wireframe' ? step * 2 : step;   // thin out wireframe meridians

  if (rings) {
    for (let r = 0; r < gRows; r += step) {
      ctx.strokeStyle = rowCols[r];
      const b = r * gCols;
      for (let c = 0; c < gCols; c++) {
        const i0 = b + c, i1 = b + ((c + 1) % gCols);
        glowLine(ctx, gPX[i0], gPY[i0], gPX[i1], gPY[i1], 0.5 * (gA[i0] + gA[i1]) * alphaScale, wCore, wHalo);
      }
    }
  }
  if (meridians) {
    for (let c = 0; c < gCols; c += mStep) {
      for (let r = 0; r < gRows - 1; r++) {
        const i0 = r * gCols + c, i1 = (r + 1) * gCols + c;
        ctx.strokeStyle = rowCols[r];
        glowLine(ctx, gPX[i0], gPY[i0], gPX[i1], gPY[i1], 0.5 * (gA[i0] + gA[i1]) * alphaScale, wCore, wHalo);
      }
    }
  }
}

// Radial glowing lines from an inner core out to a thinned set of Fibonacci
// points (many overlapping additive lines would blow out to white).
function drawSpikes(ctx, g, useT, extraR, alphaScale) {
  const wCore = g.minDim * 0.0012 * g.sizeComp * (0.6 + glow / 140);
  const wHalo = wCore * 3.2;
  const ca = color(document.getElementById('colorAPick').value);
  const cb = color(document.getElementById('colorBPick').value);
  const innerF = 0.34;
  const spikeStep = Math.max(g.stride, Math.ceil(sphereCount / 1300));
  alphaScale *= 0.5;
  for (let i = 0; i < sphereCount; i += spikeStep) {
    const d = dirs[i];
    const n = staticShape ? noiseField[i] : noise(d.x * g.freq + g.offX, d.y * g.freq + g.offY, d.z * g.freq + useT);
    const rOut = g.R * (1 + (n - 0.5) * 2 * DISP) + extraR;
    const rIn = g.R * innerF + extraR;
    const rx = d.x * g.cyR + d.z * g.syR;
    const rz = -d.x * g.syR + d.z * g.cyR;
    const ry = d.y * g.ct - rz * g.st;
    const rz2 = d.y * g.st + rz * g.ct;
    const rim = 1 - Math.abs(rz2);
    const a = Math.pow(rim, g.rimPow) * map(rz2, -1, 1, 0.55, 1.0) * alphaScale;
    if (a < 0.006) continue;
    const pO = g.focal / (g.focal - rz2 * rOut), pI = g.focal / (g.focal - rz2 * rIn);
    const ox = g.cx + rx * rOut * pO, oy = g.cy + ry * rOut * pO;
    const ix = g.cx + rx * rIn * pI, iy = g.cy + ry * rIn * pI;
    const c = lerpColor(ca, cb, (d.y + 1) * 0.5);
    ctx.strokeStyle = `rgb(${red(c) | 0},${green(c) | 0},${blue(c) | 0})`;
    glowLine(ctx, ix, iy, ox, oy, a, wCore, wHalo);
  }
}

// Export the current frame as a transparent PNG at 4K (3840 px long edge).
function exportPNG() {
  const LONG = 3840;
  let EW, EH;
  if (width >= height) { EW = LONG; EH = Math.round(LONG * height / width); }
  else                 { EH = LONG; EW = Math.round(LONG * width / height); }

  const cv = document.createElement('canvas');
  cv.width = EW; cv.height = EH;
  const ectx = cv.getContext('2d');
  const scale = Math.min(EW, EH) / Math.min(width, height);

  renderScene(ectx, EW, EH, false, scale, 1);   // full quality for export

  cv.toBlob(function (blob) {
    const a = document.createElement('a');
    a.href = URL.createObjectURL(blob);
    a.download = 'sphere.png';
    a.click();
    URL.revokeObjectURL(a.href);
  }, 'image/png');
}

/* ── Video recording ── */

function getBestMimeType() {
  const candidates = ['video/mp4;codecs=avc1', 'video/mp4', 'video/webm;codecs=vp9', 'video/webm'];
  return candidates.find(function (t) { return MediaRecorder.isTypeSupported(t); }) || 'video/webm';
}

function exportDims() {
  let ew, eh;
  if (width >= height) { ew = 1920; eh = Math.round(1920 * height / width); }
  else                 { eh = 1920; ew = Math.round(1920 * width / height); }
  return { ew, eh };
}

function toggleRecording() {
  if (isRecording) stopRecording(); else startRecording();
}

function startRecording() {
  let { ew, eh } = exportDims();
  recordingHdCanvas = document.createElement('canvas');
  recordingHdCanvas.width = ew;
  recordingHdCanvas.height = eh;
  recordingHdCtx = recordingHdCanvas.getContext('2d');

  let mimeType = getBestMimeType();
  recordedChunks = [];
  mediaRecorder = new MediaRecorder(recordingHdCanvas.captureStream(30), {
    mimeType, videoBitsPerSecond: 19_000_000
  });
  mediaRecorder.ondataavailable = function (e) { if (e.data.size > 0) recordedChunks.push(e.data); };
  mediaRecorder.onstop = function () {
    let ext = mimeType.includes('mp4') ? 'mp4' : 'webm';
    let blob = new Blob(recordedChunks, { type: mimeType });
    let link = document.createElement('a');
    link.href = URL.createObjectURL(blob);
    link.download = 'sphere.' + ext;
    link.click();
    URL.revokeObjectURL(link.href);
    recordingHdCanvas = null;
    recordingHdCtx = null;
  };
  mediaRecorder.start(100);
  isRecording = true;
  const btn = document.getElementById('record-btn');
  btn.classList.add('recording');
  // Live seconds counter in the button while recording.
  recStartMs = performance.now();
  const tick = () => { btn.textContent = '⏹ ' + fmtDur((performance.now() - recStartMs) / 1000); };
  tick();
  recTimer = setInterval(tick, 250);
}

// Format seconds as m:ss.
function fmtDur(sec) {
  const m = Math.floor(sec / 60), s = Math.floor(sec % 60);
  return m + ':' + String(s).padStart(2, '0');
}

function stopRecording() {
  if (mediaRecorder && mediaRecorder.state !== 'inactive') mediaRecorder.stop();
  isRecording = false;
  if (recTimer) { clearInterval(recTimer); recTimer = null; }
  const btn = document.getElementById('record-btn');
  btn.textContent = '⏺ Record';
  btn.classList.remove('recording');
}

function windowResized() {
  const [cW, cH] = calcCanvas(currentRatio());
  resizeCanvas(cW, cH);
  resetFloaters();
}
