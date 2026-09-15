// Ghisha Modulator (Sphere) v13 — a noise-morphed sphere of glowing points with an
// iridescent shell, a soft membrane and interactive floating particles. Each point
// / particle is a single merged sprite (bright core + glow baked in). Rendered
// additively on black; on white the additive layer is multiplied onto the page so
// colours survive. Exports a transparent PNG, an opaque JPG and WebM/MP4 video,
// all at the selected 1080p / 4K long edge.

const N_BUCKETS = 32;      // pre-tinted sphere sprites (A→B gradient)
const N_IRIS = 96;         // pre-tinted sprites around the hue wheel (iridescence)
const SPRITE_PX = 96;      // offscreen size of each sprite
const DISP = 0.34;         // radial displacement as a fraction of base radius
const MAX_FLOAT = 3000;    // capacity of the floating-particle pool

let dirs = [];             // unit direction of each sphere point
let coreSprites = [];      // merged crisp-core + glow sprite, one per colour bucket
let membraneSprite = null; // soft bloom sprite for the point-based (v10) membrane
let irisSprites = [];      // glow sprite around the full hue wheel (iridescent bands)
const irisSat = 0.51;      // iridescence saturation (fixed)

// Floating particles (screen space).
let fx, fy, fvx, fvy;      // position / velocity
let ax, ay;                // fixed anchor (its spot in the floating cloud)
let hx, hy;                // home = anchor + a small wobble; the particle springs to it
let fesc;                  // fixed random threshold [0,1); low = penetrates first
let fAlpha;                // opacity
let fInside;               // 1 = the particle now lives (floats) inside the sphere
let fchg;                  // escape charge: builds while an inside particle is pulled out
let floatGlow = null, floatCore = null;  // outside (floating) particle sprites
let floatGlowW = null, floatCoreW = null; // lighter outside-particle sprites for white bg
let insideGlow = null, insideCore = null; // inside (absorbed) particle sprites
let floatT = 0;            // flow-field time
let floatReady = false;    // spread particles once the canvas has its real size
let cursorOver = false;    // is the mouse actually hovering the canvas?

// ── Fixed look (controls removed from the UI in v13 — defaults preserved) ──
const COLOR_A = '#b25be1', COLOR_B = '#ffffff';   // sphere shell A→B duotone
const MEMBRANE_COLOR = '#c5a0de';
const FLOAT_COLOR = '#1b0e45', INSIDE_COLOR = '#7D26E6';
const FLOAT_COLOR_WHITE = '#b99be0';              // lighter outside particles on white bg
const GRAD_A_COLOR = '#4D0079';                   // Gradient A — fixed purple
const noiseSpeed = 0.008;
const hollow = 40;
const irisCoverage = 50, irisPatch = 45, irisBands = 35, irisScale = 14,
      irisSeed = 0, irisAngle = 42, irisHue = 40;   // iridescence (Angle 42, Coverage 50)
const pullForce = 1, floatTrail = 1, reach = 45, cloudSize = 25, breakthrough = 45;
const membraneOpacity = 50, membraneDelay = 400;
const membGradDiameter = 60, membGradDensity = 100, membGradCenter = 72, membGradWidth = 16;

// ── Live (slider / toggle-controlled) settings ──
let sphereCount, pointSize;             // both driven by the single Quality slider
let noiseScaleVal, glow;
let sphereShiftX = 0, sphereShiftY = 0, sphereScale = 1;
let particleCount, membraneType, membraneGap = 37;   // gap: points 37 / solid 70
// Two background gradients (below the sphere) — ported from the rasteriser.
let gradDiameter, gradDensity, gradOpacity, gradPosX, gradPosY;
let gradBDiameter, gradBDensity, gradBOpacity, gradBPosX, gradBPosY, gradBColor = '#8C31EC';
let bgColor = '#000000';                // Background toggle: black / white
let exportLong = 1920;                  // Quality toggle: 1080p → 1920, 4K → 3840
// ─────────────────────────────────────────────────────────────────────────────

let noiseHist = [];
let membNT = 0;
let noiseT = 40.0;   // start off-origin on Z: p5 noise folds negatives (noise(-z)==noise(z)),
                     // so sampling across 0 mirrors the shape. A base keeps Z positive.
let rot = 0;

let playing = true;
let mediaRecorder = null;
let recordedChunks = [];
let isRecording = false;
let recordingHdCanvas = null;
let recordingHdCtx = null;
let recTimer = null, recStartMs = 0;   // in-button recording seconds counter

function calcCanvas(ratioStr) {
  const CANVAS_SCALE = 0.95;   // shrink to 95% of the fitted size, stays centered
  const [a, b] = ratioStr.split(':').map(Number);
  const container = document.getElementById('canvas-container');
  const maxW = container.clientWidth * CANVAS_SCALE;
  const maxH = container.clientHeight * CANVAS_SCALE;
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

// Allocate the floating-particle pool and scatter it around the sphere.
function buildFloaters() {
  fx = new Float32Array(MAX_FLOAT); fy = new Float32Array(MAX_FLOAT);
  fvx = new Float32Array(MAX_FLOAT); fvy = new Float32Array(MAX_FLOAT);
  ax = new Float32Array(MAX_FLOAT); ay = new Float32Array(MAX_FLOAT);
  hx = new Float32Array(MAX_FLOAT); hy = new Float32Array(MAX_FLOAT);
  fesc = new Float32Array(MAX_FLOAT); fAlpha = new Float32Array(MAX_FLOAT);
  fInside = new Uint8Array(MAX_FLOAT);
  fchg = new Float32Array(MAX_FLOAT);
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
  const cx = width / 2 + (sphereShiftX / 100) * 0.42 * width, cy = height / 2 + (sphereShiftY / 100) * 0.42 * height;
  const R = Math.min(width, height) * 0.29 * sphereScale;
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
  if (fchg) fchg[i] = 0;
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
  const ca = color(COLOR_A);
  const cb = color(COLOR_B);
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
  // Point-based (v10) membrane bloom in its own colour — a single soft sprite.
  const mc = color(MEMBRANE_COLOR);
  membraneSprite = makeSprite(Math.round(red(mc)), Math.round(green(mc)), Math.round(blue(mc)), [
    [0.0, gCore], [0.30, gCore * 0.5], [0.6, gCore * 0.12], [1.0, 0]
  ]);
  buildIrisSprites();       // iridescence hue-wheel sprites
}

// Smooth 0→1 ramp between two edges (for soft coverage-mask boundaries).
function smoothstep(e0, e1, x) {
  const t = Math.min(1, Math.max(0, (x - e0) / (e1 - e0)));
  return t * t * (3 - 2 * t);
}

// HSV (h,s,v in 0..1) → [r,g,b] 0..255. Used to build the iridescent spectrum.
function hsv2rgb(h, s, v) {
  const i = Math.floor(h * 6), f = h * 6 - i;
  const p = v * (1 - s), q = v * (1 - f * s), t = v * (1 - (1 - f) * s);
  let r, g, b;
  switch (i % 6) {
    case 0: r = v; g = t; b = p; break;
    case 1: r = q; g = v; b = p; break;
    case 2: r = p; g = v; b = t; break;
    case 3: r = p; g = q; b = v; break;
    case 4: r = t; g = p; b = v; break;
    default: r = v; g = p; b = q;
  }
  return [Math.round(r * 255), Math.round(g * 255), Math.round(b * 255)];
}

// A full hue wheel of glow sprites (same crisp-core + glow profile as the shell).
// Each point indexes into this by its computed hue, so the smooth hue field paints
// continuous iridescent bands. `irisSat` sets vividness (low = pearly, high = oily).
function buildIrisSprites() {
  const gCore = map(glow, 1, 100, 0.16, 0.5);
  const coreStop = map(pointSize, 1, 100, 0.09, 0.5);
  irisSprites = new Array(N_IRIS);
  for (let k = 0; k < N_IRIS; k++) {
    const [r, g, bl] = hsv2rgb(k / N_IRIS, irisSat, 1.0);
    irisSprites[k] = makeSprite(r, g, bl, [
      [0.0, 1.0], [coreStop, 0.95], [coreStop * 1.7, gCore],
      [0.5, gCore * 0.35], [0.78, gCore * 0.1], [1.0, 0]
    ]);
  }
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
  [floatGlow, floatCore] = buildParticleSprites(FLOAT_COLOR);
  [floatGlowW, floatCoreW] = buildParticleSprites(FLOAT_COLOR_WHITE);
  [insideGlow, insideCore] = buildParticleSprites(INSIDE_COLOR);
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

  // Every tunable is read from its HTML input — defaults live only in index.html.
  bind('noise-seed-slider', v => noiseSeed(+v));
  bind('noise-scale-slider', v => noiseScaleVal = +v);
  bind('glow-slider', v => glow = +v, buildSprites);

  // Quality — a single slider driving both point density and point size, inversely:
  // higher quality = more points + smaller points; lower = fewer points + bigger points.
  const applyQuality = q => {
    sphereCount = Math.round(map(q, 1, 100, 2000, 16000));
    pointSize   = map(q, 1, 100, 45, 12.5);
  };
  bind('quality-slider', v => applyQuality(+v),
       () => { buildPoints(sphereCount); buildSprites(); });

  bind('sphere-x-slider', v => sphereShiftX = +v);
  bind('sphere-y-slider', v => sphereShiftY = +v);
  bind('sphere-scale-slider', v => sphereScale = (+v) / 100);

  // Two background gradients (below the sphere) — ported from the rasteriser.
  bind('grad-diameter-slider', v => gradDiameter = +v);
  bind('grad-density-slider',  v => gradDensity = +v);
  bind('grad-opacity-slider',  v => gradOpacity = +v);
  bind('grad-x-slider',        v => gradPosX = +v);
  bind('grad-y-slider',        v => gradPosY = +v);
  bind('gradB-diameter-slider', v => gradBDiameter = +v);
  bind('gradB-density-slider',  v => gradBDensity = +v);
  bind('gradB-opacity-slider',  v => gradBOpacity = +v);
  bind('gradB-x-slider',        v => gradBPosX = +v);
  bind('gradB-y-slider',        v => gradBPosY = +v);

  bind('count-slider', v => particleCount = +v);
  bind('membrane-type', v => { membraneType = v; membraneGap = (v === 'solid') ? 70 : 37; });

  // Build geometry + sprites from the values just read.
  buildFloaters();
  buildPoints(sphereCount);
  buildSprites();
  buildFloatSprites();

  // Gradient B colour — fixed swatch palette.
  document.querySelectorAll('#gradB-swatches .swatch-btn').forEach(btn => {
    btn.addEventListener('click', () => {
      document.querySelectorAll('#gradB-swatches .swatch-btn').forEach(b => b.classList.remove('is-selected'));
      btn.classList.add('is-selected');
      gradBColor = btn.getAttribute('data-color');
    });
  });

  // Background colour toggle (black / white).
  document.querySelectorAll('#bg-toggle .toggle-btn').forEach(btn => {
    btn.addEventListener('click', () => {
      document.querySelectorAll('#bg-toggle .toggle-btn').forEach(b => b.classList.remove('is-selected'));
      btn.classList.add('is-selected');
      bgColor = btn.getAttribute('data-bg');
    });
  });

  // Export quality toggle (1080p / 4K).
  document.querySelectorAll('#quality-toggle .toggle-btn').forEach(btn => {
    btn.addEventListener('click', () => {
      document.querySelectorAll('#quality-toggle .toggle-btn').forEach(b => b.classList.remove('is-selected'));
      btn.classList.add('is-selected');
      exportLong = btn.getAttribute('data-quality') === '4k' ? 3840 : 1920;
    });
  });

  select("#play-pause").mousePressed(togglePlay);
  select("#record-btn").mousePressed(toggleRecording);
  select("#export-png").mousePressed(exportPNG);
  select("#export-jpg").mousePressed(exportJPG);

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
  // The noise morph and the auto-spin advance while playing.
  if (playing) { noiseT += noiseSpeed; rot += 0.0035; }
  floatT += 0.006;

  // Log noiseT so the membrane can sample a delayed value; keep ~6 s of history.
  const now = millis();
  noiseHist.push({ t: now, v: noiseT });
  while (noiseHist.length > 1 && noiseHist[0].t < now - 6000) noiseHist.shift();
  membNT = delayedNoiseT(now, membraneDelay);

  if (!floatReady) { resetFloaters(); floatReady = true; }
  updateFloaters();

  renderScene(drawingContext, width, height, true, 1);

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
  const cx = width / 2 + (sphereShiftX / 100) * 0.42 * width, cy = height / 2 + (sphereShiftY / 100) * 0.42 * height;
  const minDim = Math.min(width, height);
  const R = minDim * 0.29 * sphereScale;
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
  const membResist = 0.32;   // how much of an inside particle's outward push the membrane holds back
  const membEscape = 12;     // escape charge needed to pull an inside particle back out (~firm tug)

  for (let i = 0; i < particleCount; i++) {
    // Home = the particle's fixed anchor plus a small INDEPENDENT wobble. The
    // cloud keeps its spread (no drift to edges, no streaky filaments) and a
    // released particle returns to its own spot.
    const a = noise(i * 0.123, floatT * 0.5) * Math.PI * 4;
    hx[i] = ax[i] + Math.cos(a) * wanderR;
    hy[i] = ay[i] + Math.sin(a) * wanderR;

    // Cursor capture weight: 1 next to the cursor, 0 at the edge of reach. Inside
    // particles can now be grabbed from outside too, so the cursor can pull them
    // back out (against the membrane's resistance).
    const canFollow = overC;
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
        const grab = grabAmt * w * (fInside[i] ? 0.6 : 1);   // inside particles resist a little
        fx[i] += (tx - fx[i]) * grab;
        fy[i] += (ty - fy[i]) * grab;
      }
    }

    // Residual velocity (from membrane slides / edges) just decays.
    fvx[i] *= 0.85; fvy[i] *= 0.85;
    fx[i] += fvx[i]; fy[i] += fvy[i];

    // Ease back home when the cursor isn't holding it (no spring → no rebound).
    // (1-w)² so even a moderately-captured particle commits to its cloud slot.
    // A captured INSIDE particle skips this so its inside-home can't fight the
    // cursor while it's being dragged out.
    if (!(fInside[i] && w > 0.05)) {
      const ease = returnEase * (1 - w) * (1 - w);
      fx[i] += (hx[i] - fx[i]) * ease;
      fy[i] += (hy[i] - fy[i]) * ease;
    }

    // Membrane: contain / cross.
    const rx = fx[i] - cx, ry = fy[i] - cy, dc = Math.hypot(rx, ry) || 0.0001;
    if (fInside[i]) {
      if (dc > Rmem && w > 0.05) {
        // Being pulled out: the membrane resists (keeps only 1-membResist of the
        // outward overshoot each frame, so it can't instantly fly free), but a
        // firm, sustained pull builds an "escape charge" that finally releases it.
        const held = Rmem + (dc - Rmem) * (1 - membResist);
        fx[i] = cx + rx / dc * held; fy[i] = cy + ry / dc * held;
        fchg[i] += w * Math.min(1, (held - Rmem) / (Rmem * 0.06));
        if (fchg[i] > membEscape) {
          fInside[i] = 0; fchg[i] = 0;
          ax[i] = fx[i]; ay[i] = fy[i]; hx[i] = fx[i]; hy[i] = fy[i];
        }
      } else {
        // Not being pulled clear → drain the charge and stay contained inside
        // (slide along the inner wall, no bounce).
        fchg[i] *= 0.9;
        if (dc > Rmem) {
          fx[i] = cx + rx / dc * Rmem; fy[i] = cy + ry / dc * Rmem;
          const vr = fvx[i] * rx / dc + fvy[i] * ry / dc;
          if (vr > 0) { fvx[i] -= vr * rx / dc; fvy[i] -= vr * ry / dc; }
        }
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
// `opaque` paints the background (transparent for the PNG export); `scale`
// rescales particle positions when rendering at a different resolution.
function renderScene(ctx, W, H, opaque, scale) {
  const cx0 = W / 2, cy0 = H / 2;                         // base centre (particle reference)
  const cx = cx0 + (sphereShiftX / 100) * 0.42 * W;       // sphere + membrane centre (X shift)
  const cy = cy0 + (sphereShiftY / 100) * 0.42 * H;       // sphere + membrane centre (Y shift)
  const minDim = Math.min(W, H);
  const R = minDim * 0.29 * sphereScale;
  const focal = R * 3.4;

  const freq = map(noiseScaleVal, 1, 4, 0.25, 0.61);
  const offX = 50.3, offY = 80.7;   // base offsets break p5-noise's mirror symmetry
  const glowSize = minDim * map(glow, 1, 100, 0.008, 0.030) * sphereScale;
  // Iridescence params (computed once per frame). A smooth low-frequency hue field,
  // repeated `bands` times over the surface, paints continuous multi-colour bands.
  const irFreq = map(irisScale, 1, 100, 0.25, 3.0);   // lower = wider, flowier bands
  const irBandsN = map(irisBands, 1, 100, 0.4, 7.0);  // spectral cycles across the field
  const irOff = irisSeed * 0.171 + 20.0;              // pattern seed offset
  const irHueF = irisHue / 100;                       // base hue offset
  const irAngleAmt = irisAngle / 100 * 4.0;           // view-angle bands (projection tightens them at the rim)
  // Coverage mask: a separate low-frequency noise decides WHERE iridescence shows.
  const mFreq = map(irisPatch, 1, 100, 3.0, 0.25);    // higher slider = bigger patches
  const mOff = 60.0;
  const mCut = map(irisCoverage, 0, 100, 1.06, -0.06);// 0 → nowhere, 100 → whole sphere
  const gapWorld = minDim * map(membraneGap, 0, 100, 0.0, 0.05);
  const membAlpha = membraneOpacity / 100;
  const membSize = glowSize * 1.5 * Math.SQRT2;    // point-membrane bloom size (half-density)
  const rimPow = map(hollow, 0, 100, 0.15, 4.0);

  const cyR = Math.cos(rot), syR = Math.sin(rot);
  // Steep tilt: the auto-spin is around the pole axis, so tilting that axis into
  // the screen puts both (antipodal) poles near the disc centre, where the hollow
  // fade hides the "vortex" where the lines converge — while the spin stays lively.
  const tilt = 1.3, ct = Math.cos(tilt), st = Math.sin(tilt);

  // Background base fill — black / white toggle. PNG export passes opaque=false so
  // the base is left transparent (the gradients + sphere still render).
  ctx.globalCompositeOperation = 'source-over';
  ctx.globalAlpha = 1;
  if (opaque) { ctx.fillStyle = bgColor; ctx.fillRect(0, 0, W, H); }
  else        { ctx.clearRect(0, 0, W, H); }

  // Two radial gradients BELOW the sphere (ported from the rasteriser): Gradient A
  // is a fixed purple; Gradient B uses the swatch palette. Drawn with normal
  // (source-over) blending so they read correctly on a white background too.
  drawRadialGradient(ctx, W, H, GRAD_A_COLOR, gradDiameter, gradDensity, gradOpacity, gradPosX, gradPosY);
  drawGradientB(ctx, W, H);

  // Glow blend for the sphere + membrane + particles: additive on black (bright
  // glow), multiply on white (so the colours darken the page instead of blowing
  // out to white). The visual weight stays similar; colours survive on white.
  const glowBlend = (bgColor.toLowerCase() === '#ffffff') ? 'multiply' : 'lighter';
  ctx.globalCompositeOperation = glowBlend;

  // ── Membrane ── two types (dropdown):
  //   'solid'  → a single noise-shaped 2D blob filled with a radial gradient
  //             (one fill; drawn BEHIND the shell).
  //   'points' → a soft bloom sprite drawn per shell point at half density, at a
  //             delayed-noise-wobbled radius (interleaved with the shell, below).
  const geo = { cx, cy, R, focal, freq, offX, offY, rimPow, gapWorld, membAlpha,
                cyR, syR, ct, st, minDim };
  if (membAlpha > 0 && membraneType === 'solid') {
    drawMembraneShape(ctx, geo);
  }
  const drawMembPoints = membAlpha > 0 && membraneType === 'points';

  // ── Sphere shell (glowing points) ──
  for (let i = 0, k = 0; i < sphereCount; i++, k++) {
    const d = dirs[i];
    const n = noise(d.x * freq + offX, d.y * freq + offY, d.z * freq + noiseT);
    const rBase = R * (1 + (n - 0.5) * 2 * DISP);

    const rx = d.x * cyR + d.z * syR;
    const rz = -d.x * syR + d.z * cyR;
    const ry = d.y * ct - rz * st;
    const rz2 = d.y * st + rz * ct;

    const rim = 1 - Math.abs(rz2);
    const facing = map(rz2, -1, 1, 0.55, 1.0);
    const alpha = Math.pow(rim, rimPow) * facing;
    if (alpha < 0.004) continue;

    // Point membrane: a soft bloom at every other point, wobbled by the DELAYED
    // noise (membNT) and pushed out by the gap, so it trails the shell's shape.
    if (drawMembPoints && (k & 1) === 0) {
      const nm = noise(d.x * freq + offX, d.y * freq + offY, d.z * freq + membNT);
      const rm = R * (1 + (nm - 0.5) * 2 * DISP) + gapWorld;
      const perspM = focal / (focal - rz2 * rm);
      const mx = cx + rx * rm * perspM, my = cy + ry * rm * perspM;
      const ms = membSize * perspM;
      ctx.globalAlpha = alpha * membAlpha;
      ctx.drawImage(membraneSprite, mx - ms / 2, my - ms / 2, ms, ms);
    }

    const bucket = Math.min(N_BUCKETS - 1, Math.max(0, Math.round(n * (N_BUCKETS - 1))));
    const persp = focal / (focal - rz2 * rBase);
    const sx = cx + rx * rBase * persp, sy = cy + ry * rBase * persp;
    const gs = glowSize * persp;

    // Iridescence coverage: a low-frequency mask noise decides WHERE the bands show
    // (soft edge → patches fade in). Below the mask the point keeps its base (A→B)
    // colour; above it turns iridescent. Cross-faded by `w` for a seamless boundary.
    const mnoise = noise(d.x * mFreq + mOff, d.y * mFreq + 5.1, d.z * mFreq + noiseT);
    const w = smoothstep(mCut - 0.13, mCut + 0.13, mnoise);
    if (w < 0.997) {                                       // base part
      ctx.globalAlpha = alpha * (1 - w);
      ctx.drawImage(coreSprites[bucket], sx - gs / 2, sy - gs / 2, gs, gs);
    }
    if (w > 0.003) {                                       // iridescent part
      // Smooth hue field → continuous multi-colour bands; rz2 term tightens them
      // toward the grazing rim (projection) like a real bubble.
      const field = noise(d.x * irFreq + irOff, d.y * irFreq + 8.3, d.z * irFreq + noiseT);
      let hf = irHueF + field * irBandsN + rz2 * irAngleAmt;
      hf -= Math.floor(hf);                                // wrap to [0,1)
      ctx.globalAlpha = alpha * w;
      ctx.drawImage(irisSprites[Math.min(N_IRIS - 1, Math.floor(hf * N_IRIS))], sx - gs / 2, sy - gs / 2, gs, gs);
    }
  }

  // ── Floating particles (soft glow + crisp core, full density) ──
  ctx.globalCompositeOperation = glowBlend;   // additive on black, multiply on white
  const fGlow = minDim * 0.018, fCore = minDim * 0.0055;
  const whiteBg = glowBlend === 'multiply';
  for (let i = 0; i < particleCount; i++) {
    const al = fAlpha[i];
    if (al <= 0.004) continue;
    const sx = cx0 + (fx[i] - width / 2) * scale;   // particles use the base centre; their
    const sy = cy0 + (fy[i] - height / 2) * scale;  // physics already carries the X / Y shift

    // Inside particles keep their colour. Outside particles: dark on black, but a
    // LIGHTER colour at 30% opacity on white so they don't punch through the page.
    const outside = !fInside[i];
    const glowS = outside ? (whiteBg ? floatGlowW : floatGlow) : insideGlow;
    const coreS = outside ? (whiteBg ? floatCoreW : floatCore) : insideCore;
    const op = (whiteBg && outside) ? 0.3 : 1;
    ctx.globalAlpha = al * 0.7 * op;
    ctx.drawImage(glowS, sx - fGlow / 2, sy - fGlow / 2, fGlow, fGlow);
    ctx.globalAlpha = al * op;
    ctx.drawImage(coreS, sx - fCore / 2, sy - fCore / 2, fCore, fCore);
  }

  ctx.globalAlpha = 1;
  ctx.globalCompositeOperation = 'source-over';
}

// A radial gradient (hex colour at its centre → transparent at the edge), ported
// from the rasteriser. posX/posY (−100..100) slide the centre; density → alpha,
// diameter → radius, opacity → the whole layer via globalAlpha.
function drawRadialGradient(ctx, W, H, hex, diameter, density, opacity, posX, posY) {
  if (!(density > 0) || !(opacity > 0)) return;
  const minDim = Math.min(W, H);
  const gx = W / 2 + (posX / 100) * (W / 2);
  const gy = H / 2 + (posY / 100) * (H / 2);
  const gc = color(hex);
  const gr = Math.round(red(gc)), gg = Math.round(green(gc)), gb = Math.round(blue(gc));
  const gRad = Math.max(1, minDim * map(diameter, 0, 100, 0.1, 1.6));
  const a0 = map(density, 0, 100, 0.0, 1.0);
  const grad = ctx.createRadialGradient(gx, gy, 0, gx, gy, gRad);
  grad.addColorStop(0.0, `rgba(${gr},${gg},${gb},${a0})`);
  grad.addColorStop(map(density, 0, 100, 0.15, 0.7), `rgba(${gr},${gg},${gb},${a0 * 0.35})`);
  grad.addColorStop(1.0, `rgba(${gr},${gg},${gb},0)`);
  const prevAlpha = ctx.globalAlpha;
  ctx.globalAlpha = prevAlpha * (opacity / 100);
  ctx.fillStyle = grad;
  ctx.fillRect(0, 0, W, H);
  ctx.globalAlpha = prevAlpha;
}

// Gradient B — swatch-coloured radial gradient. Normal (source-over) blending so
// it composites correctly on white as well as black (no additive wash-out).
function drawGradientB(ctx, W, H) {
  if (!(gradBDensity > 0)) return;
  ctx.globalCompositeOperation = 'source-over';
  ctx.globalAlpha = 1;
  drawRadialGradient(ctx, W, H, gradBColor, gradBDiameter, gradBDensity, gradBOpacity, gradBPosX, gradBPosY);
}

// Membrane as a single 2D noise-wobbled blob filled with a radial gradient
// (membrane colour at the centre → fully transparent at the edge). One fill per
// frame instead of thousands of point sprites. The wobble spins with the sphere.
function drawMembraneShape(ctx, g) {
  const cx = g.cx, cy = g.cy, minDim = g.minDim;
  const R = g.R, gapWorld = g.gapWorld, freq = g.freq, offX = g.offX, offY = g.offY;
  const cyR = g.cyR, syR = g.syR, ct = g.ct, st = g.st;
  const RmemBase = R + gapWorld;
  const M = 120;

  // The outline traces the sphere's ACTUAL silhouette: for each screen angle the
  // silhouette direction is (cosθ, sinθ, 0) in view space (z = 0, so it projects
  // 1:1). Inverse-rotate it into object space to read the SAME noise the sphere
  // uses — at membNT, so the delayed-wobble membrane still trails the shape.
  ctx.beginPath();
  for (let i = 0; i <= M; i++) {
    const th = (i / M) * Math.PI * 2;
    const vx = Math.cos(th), vy = Math.sin(th);
    // inverse tilt-X: rz = -vy·st, dy = vy·ct, rx = vx ; then inverse rot-Y
    const rz = -vy * st, dy = vy * ct, rx = vx;
    const dx = rx * cyR - rz * syR, dz = rx * syR + rz * cyR;
    const nval = noise(dx * freq + offX, dy * freq + offY, dz * freq + membNT);
    const rr = R * (1 + (nval - 0.5) * 2 * DISP) + gapWorld;
    const px = cx + vx * rr, py = cy + vy * rr;
    if (i === 0) ctx.moveTo(px, py); else ctx.lineTo(px, py);
  }
  ctx.closePath();

  const mc = color(MEMBRANE_COLOR);
  const mr = Math.round(red(mc)), mg = Math.round(green(mc)), mb = Math.round(blue(mc));

  // A perfectly CIRCULAR radial gradient: transparent → colour → transparent
  // (alpha ▸ colour ▸ alpha). Because the fill is clipped to the wobbly silhouette,
  // the fixed colour ring is crossed differently around the shape — where the edge
  // sits inside the ring the colour reads sharp, where the edge bulges past it the
  // colour has already faded, so it drifts off into nothing. All four stops are
  // manual:
  //   diameter → overall radius of the gradient circle
  //   position → where along that radius the colour peaks (0 centre … 1 rim)
  //   width    → half-thickness of the colour band before it fades either side
  //   density  → peak opacity of the colour
  const a0 = map(membGradDensity, 0, 100, 0.0, 1.0) * g.membAlpha;
  const gRad = Math.max(1, RmemBase * map(membGradDiameter, 0, 100, 0.4, 2.2));
  const pos = map(membGradCenter, 0, 100, 0.0, 1.0);    // colour peak (fraction of gRad)
  const halfW = map(membGradWidth, 0, 100, 0.02, 0.6);  // band half-width (fraction of gRad)
  const clampOff = o => (o < 0 ? 0 : o > 1 ? 1 : o);
  const col = a => `rgba(${mr},${mg},${mb},${a})`;
  const grad = ctx.createRadialGradient(cx, cy, 0, cx, cy, gRad);
  // Offsets are non-decreasing after clamping, so they're always valid.
  grad.addColorStop(0, col(0));
  grad.addColorStop(clampOff(pos - halfW), col(0));
  grad.addColorStop(clampOff(pos), col(a0));
  grad.addColorStop(clampOff(pos + halfW), col(0));
  grad.addColorStop(1, col(0));
  ctx.globalAlpha = 1;
  ctx.fillStyle = grad;
  ctx.fill();
}

// Export long-edge follows the Quality toggle (1080p → 1920, 4K → 3840).
function exportSize() {
  let EW, EH;
  if (width >= height) { EW = exportLong; EH = Math.round(exportLong * height / width); }
  else                 { EH = exportLong; EW = Math.round(exportLong * width / height); }
  return [EW, EH];
}

// Render the full-quality scene into an offscreen canvas. opaque=true paints the
// black/white background; opaque=false leaves it transparent (gradients kept).
function renderExport(opaque) {
  const [EW, EH] = exportSize();
  const cv = document.createElement('canvas');
  cv.width = EW; cv.height = EH;
  const scale = Math.min(EW, EH) / Math.min(width, height);
  renderScene(cv.getContext('2d'), EW, EH, opaque, scale);
  return cv;
}

function downloadCanvas(cv, name, type, quality) {
  cv.toBlob(function (blob) {
    const a = document.createElement('a');
    a.href = URL.createObjectURL(blob);
    a.download = name;
    a.click();
    URL.revokeObjectURL(a.href);
  }, type, quality);
}

// PNG — no background fill (transparent) but WITH gradients + sphere + particles.
function exportPNG() { downloadCanvas(renderExport(false), 'sphere.png', 'image/png'); }

// JPG — opaque background (black / white toggle) with gradients + everything.
function exportJPG() { downloadCanvas(renderExport(true), 'sphere.jpg', 'image/jpeg', 0.92); }

// Keyboard: "s" saves the background-free PNG, "r" toggles recording. Ignored while
// typing in a field so it doesn't fire from the sliders / selects.
function keyPressed() {
  const t = document.activeElement && document.activeElement.tagName;
  if (t === 'INPUT' || t === 'TEXTAREA' || t === 'SELECT') return;
  if (key === 's' || key === 'S') exportPNG();
  else if (key === 'r' || key === 'R') toggleRecording();
}

/* ── Video recording ── */

function getBestMimeType() {
  const candidates = ['video/mp4;codecs=avc1', 'video/mp4', 'video/webm;codecs=vp9', 'video/webm'];
  return candidates.find(function (t) { return MediaRecorder.isTypeSupported(t); }) || 'video/webm';
}

function exportDims() {
  let ew, eh;
  if (width >= height) { ew = exportLong; eh = Math.round(exportLong * height / width); }
  else                 { eh = exportLong; ew = Math.round(exportLong * width / height); }
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
  // Live seconds counter in the Record button while recording.
  const btn = document.getElementById('record-btn');
  if (btn) btn.classList.add('recording');
  recStartMs = performance.now();
  const tick = () => { if (btn) btn.textContent = '⏹ ' + fmtDur((performance.now() - recStartMs) / 1000); };
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
  if (btn) { btn.textContent = '⏺ Record'; btn.classList.remove('recording'); }
}

function windowResized() {
  const [cW, cH] = calcCanvas(currentRatio());
  resizeCanvas(cW, cH);
  resetFloaters();
}
