var cvs = document.getElementById('cvs');
var ctx = cvs.getContext('2d');
var bgCvs = document.getElementById('bg-canvas');
var bgCtx = bgCvs.getContext('2d');

var mask = document.getElementById('mask');
var pauseMask = document.getElementById('pause-mask');
var gameOverMask = document.getElementById('game-over-mask');
var btnStart = document.getElementById('btn-start');
var btnRestart = document.getElementById('btn-restart');
var btnLeft = document.getElementById('btn-left');
var btnRight = document.getElementById('btn-right');
var btnDrop = document.getElementById('btn-drop');
var feverBar = document.getElementById('fever-bar');
var levelBar = document.getElementById('level-bar');
var levelLabel = document.getElementById('level-label');

var SENS = 8, N = 7, CX = 180, CY = 180;
var R_INT = 20, R_EXT = 135;
var AN = (R_EXT - R_INT) / N, PASO = (Math.PI * 2) / SENS;

var COLS = [null, '#FF007F', '#05FFA1', '#00F5FF', '#FFB800', '#00FF00', '#2E67FF', '#A020F0', '#808080', '#FFA500', '#FFFF00'];

var gameMode = 'arcade'; // 'arcade' or 'practice'
var difficulty = 'normal';
var practiceSettings = {
    colors: 4,
    speedMult: 1,
    feverFreq: 'NORMAL',
    waveEnabled: false
};

var grid, piece = null, pieceSecondary = null, nextP = null, running = false, isPaused = false, isGameOver = false;
var rotV = 0, rotT = 0;
var animLock = false, freeze = 0, shake = 0;

var parts = [], shock = [], halos = [], stars = [], textSplashes = [], shatteredPieces = [];
var score = 0, hi = localStorage.getItem('radiax_hi') || 0;
var speed = 1.0, combo = 0;

var currentLevel = 1, levelProgress = 0;
var feverPoints = 0, isFeverActive = false;
var feverDurationMs = 12000;
var feverEndTime = 0;
var feverStartTime = 0; // Seguimiento del inicio para efectos
var feverTransitioning = false; // Estado para transiciones
var pauseStartTime = 0;
var bombaFinalPendiente = false;
var rachaSinMatch = 0, tiempoUltimaBomba = Date.now();

// --- ESTRUCTURAS Y CACHÉ PRE-ASIGNADAS ---
var cachedWhiteNoise = null;
var matchMark = Array.from({ length: SENS }, function() { return new Uint8Array(N); });

// Audio Lookahead Scheduler Centralizado
var audioCtx = null;
var masterGain = null;
var musicSchedulerTimer = null;
var nextNoteTime = 0.0;
var stepM = 0;
var musicStartTime = 0.0;
var LOOKAHEAD_MS = 25.0;
var SCHEDULE_AHEAD_TIME = 0.12;

// Flag para melodía secundaria de bajos profundos (se activa con setTimeout a los 10s)
var secondaryDeepActive = false;
var secondaryDeepTimer = null;

// Throttle para el fondo: ~30fps (suave y rápido)
var bgLastTime = 0;
var BG_INTERVAL = 33; // ms entre frames del fondo (~30fps)

// --- GESTIÓN DE FONDO ESPACIAL (ALTO RENDIMIENTO, THROTTLED A 20fps) ---
function resizeBg() {
    bgCvs.width = Math.max(480, Math.floor(window.innerWidth * 0.7));
    bgCvs.height = Math.max(360, Math.floor(window.innerHeight * 0.7));
}
window.addEventListener('resize', resizeBg);
resizeBg();

function initEstrellas() {
    stars = [];
    var count = 120; // reducido de 140 para mejor rendimiento
    for (var i = 0; i < count; i++) {
        stars.push({
            x: (Math.random() - 0.5) * bgCvs.width * 2,
            y: (Math.random() - 0.5) * bgCvs.height * 2,
            z: Math.random() * 1000,
            pz: 1000,
            colorType: i % 3
        });
    }
}

function renderFondoEspacial(now) {
    // Throttle: solo renderizar el fondo a ~20fps para no bloquear el hilo principal
    if (now - bgLastTime < BG_INTERVAL) return;
    bgLastTime = now;

    var w = bgCvs.width, h = bgCvs.height;
    var bgCenterX = w / 2, bgCenterY = h / 2;

    bgCtx.fillStyle = isFeverActive ? 'rgba(8, 2, 18, 0.55)' : 'rgba(3, 3, 8, 0.4)';
    bgCtx.fillRect(0, 0, w, h);

    // Lógica de aceleración/desaceleración de estrellas
    var speedZ = 3.5;
    var targetSpeedZ = isFeverActive ? 28.0 : 3.5;
    
    var timeElapsed = Date.now() - (isFeverActive ? feverStartTime : feverEndTime);
    var transitionDuration = 2000; // 2 segundos de transición

    if (timeElapsed < transitionDuration) {
        var t = timeElapsed / transitionDuration;
        // Ease in-out simple
        var factor = t < 0.5 ? 2 * t * t : -1 + (4 - 2 * t) * t;
        
        if (isFeverActive) {
            // Acelerando al inicio del fever
            speedZ = 3.5 + (28.0 - 3.5) * factor;
        } else {
            // Desacelerando al final del fever
            speedZ = 28.0 - (28.0 - 3.5) * factor;
        }
    } else {
        speedZ = targetSpeedZ;
    }

    var colorPalettes = ['#00F5FF', '#FF007F', '#FFB800'];

    // Dibujar todas las estrellas en un solo path por color
    for (var cIdx = 0; cIdx < 3; cIdx++) {
        var curColor = colorPalettes[cIdx];
        bgCtx.fillStyle = curColor;
        bgCtx.strokeStyle = curColor;
        bgCtx.beginPath();

        for (var i = cIdx; i < stars.length; i += 3) {
            var st = stars[i];

            st.pz = st.z;
            st.z -= speedZ;

            if (st.z <= 10) {
                st.z = 1000;
                st.pz = 1000;
                st.x = (Math.random() - 0.5) * w * 2;
                st.y = (Math.random() - 0.5) * h * 2;
            }

            var k = 280 / st.z;
            var px = bgCenterX + st.x * k;
            var py = bgCenterY + st.y * k;

            if (isFeverActive) {
                var prevK = 280 / st.pz;
                bgCtx.moveTo(bgCenterX + st.x * prevK, bgCenterY + st.y * prevK);
                bgCtx.lineTo(px, py);
            } else {
                var size = Math.max(0.8, (1 - st.z / 1000) * 2.0);
                bgCtx.moveTo(px + size, py);
                bgCtx.arc(px, py, size, 0, Math.PI * 2);
            }
        }

        if (isFeverActive) {
            bgCtx.lineWidth = 1.6;
            bgCtx.stroke();
        } else {
            bgCtx.fill();
        }
    }
}

// --- MOTOR DE AUDIO TECHNO-MELANCÓLICO CON LOOKAHEAD ---
function initAudio() {
    try {
        if (!audioCtx) {
            audioCtx = new (window.AudioContext || window.webkitAudioContext)();
            masterGain = audioCtx.createGain();
            masterGain.gain.setValueAtTime(0.85, audioCtx.currentTime);
            masterGain.connect(audioCtx.destination);
        }
        if (audioCtx.state === 'suspended') {
            audioCtx.resume();
        }

        if (!cachedWhiteNoise && audioCtx) {
            var bufLen = audioCtx.sampleRate * 2.0;
            cachedWhiteNoise = audioCtx.createBuffer(1, bufLen, audioCtx.sampleRate);
            var channelData = cachedWhiteNoise.getChannelData(0);
            for (var i = 0; i < bufLen; i++) {
                channelData[i] = Math.random() * 2.0 - 1.0;
            }
        }

        // Solo iniciar música si está corriendo y no está ya sonando
        if (running && !isPaused && !isGameOver && !musicSchedulerTimer) {
            startMusic();
        }
    } catch(e) {}
}

function stopMusic() {
    if (musicSchedulerTimer) {
        clearInterval(musicSchedulerTimer);
        musicSchedulerTimer = null;
    }
    if (secondaryDeepTimer) {
        clearTimeout(secondaryDeepTimer);
        secondaryDeepTimer = null;
    }
}

function startMusic() {
    stopMusic();
    if (!audioCtx || audioCtx.state !== 'running' || !running || isPaused || isGameOver) return;

    nextNoteTime = audioCtx.currentTime + 0.05;
    musicStartTime = audioCtx.currentTime;
    musicSchedulerTimer = setInterval(audioSchedulerTick, LOOKAHEAD_MS);

    // Activar melodía secundaria de bajos profundos exactamente a los 10 segundos
    // Usar un timer de pared (wall-clock) en lugar de contar pasos musicales
    if (secondaryDeepTimer) clearTimeout(secondaryDeepTimer);
    if (!secondaryDeepActive) {
        secondaryDeepTimer = setTimeout(function() {
            secondaryDeepActive = true;
            secondaryDeepTimer = null;
        }, 10000);
    }
}

function audioSchedulerTick() {
    if (!audioCtx || audioCtx.state !== 'running' || !running || isPaused || isGameOver) return;

    var stepDuration = isFeverActive ? 0.068 : 0.117; // 128 BPM Techno

    while (nextNoteTime < audioCtx.currentTime + SCHEDULE_AHEAD_TIME) {
        scheduleMusicStep(stepM, nextNoteTime);
        nextNoteTime += stepDuration;
        stepM++;
    }
}

// Batería Techno
function playDrumKick(t) {
    if (!audioCtx || !masterGain) return;
    var osc = audioCtx.createOscillator(), g = audioCtx.createGain();
    osc.type = 'sine';
    osc.frequency.setValueAtTime(175, t);
    osc.frequency.exponentialRampToValueAtTime(32, t + 0.09);
    g.gain.setValueAtTime(0.42, t);
    g.gain.exponentialRampToValueAtTime(0.001, t + 0.09);
    osc.connect(g); g.connect(masterGain);
    osc.start(t); osc.stop(t + 0.09);
    osc.onended = function() { osc.disconnect(); g.disconnect(); };
}

function playDrumSnare(t) {
    if (!audioCtx || !cachedWhiteNoise || !masterGain) return;
    var noise = audioCtx.createBufferSource();
    noise.buffer = cachedWhiteNoise;
    var filt = audioCtx.createBiquadFilter();
    filt.type = 'highpass';
    filt.frequency.setValueAtTime(1200, t);
    var g = audioCtx.createGain();
    g.gain.setValueAtTime(0.2, t);
    g.gain.exponentialRampToValueAtTime(0.001, t + 0.075);
    noise.connect(filt); filt.connect(g); g.connect(masterGain);
    noise.start(t); noise.stop(t + 0.075);
    noise.onended = function() { noise.disconnect(); filt.disconnect(); g.disconnect(); };
}

function playDrumHiHat(t, open) {
    if (!audioCtx || !cachedWhiteNoise || !masterGain) return;
    var dur = open ? 0.065 : 0.026;
    var noise = audioCtx.createBufferSource();
    noise.buffer = cachedWhiteNoise;
    var filt = audioCtx.createBiquadFilter();
    filt.type = 'highpass';
    filt.frequency.setValueAtTime(7500, t);
    var g = audioCtx.createGain();
    g.gain.setValueAtTime(open ? 0.065 : 0.038, t);
    g.gain.exponentialRampToValueAtTime(0.001, t + dur);
    noise.connect(filt); filt.connect(g); g.connect(masterGain);
    noise.start(t); noise.stop(t + dur);
    noise.onended = function() { noise.disconnect(); filt.disconnect(); g.disconnect(); };
}

function soundComboChime(comboCount) {
    try {
        if (!audioCtx || !masterGain || audioCtx.state !== 'running') return;
        var t = audioCtx.currentTime;
        var mult = Math.min(5, Math.max(1, comboCount));
        var chordNotes = [
            523.25 * (1 + mult * 0.08),
            659.25 * (1 + mult * 0.08),
            783.99 * (1 + mult * 0.08),
            1046.5 * (1 + mult * 0.08)
        ];
        for (var i = 0; i < chordNotes.length; i++) {
            var noteT = t + (i * 0.038);
            var osc = audioCtx.createOscillator(), g = audioCtx.createGain();
            osc.type = 'triangle';
            osc.frequency.setValueAtTime(chordNotes[i], noteT);
            osc.frequency.exponentialRampToValueAtTime(chordNotes[i] * 1.12, noteT + 0.18);
            g.gain.setValueAtTime(0.24, noteT);
            g.gain.exponentialRampToValueAtTime(0.001, noteT + 0.18);
            osc.connect(g); g.connect(masterGain);
            osc.start(noteT); osc.stop(noteT + 0.18);
        }
    } catch(e) {}
}

function playLevelUpSound() {
    try {
        if (!audioCtx || !masterGain || audioCtx.state !== 'running') return;
        var t = audioCtx.currentTime;
        var notes = [523.25, 659.25, 783.99, 1046.50, 1318.51, 1567.98];
        for (var i = 0; i < notes.length; i++) {
            var noteTime = t + (i * 0.10);
            var osc = audioCtx.createOscillator(), g = audioCtx.createGain();
            osc.type = (i >= notes.length - 2) ? 'triangle' : 'sine';
            osc.frequency.setValueAtTime(notes[i], noteTime);

            var dur = (i === notes.length - 1) ? 0.6 : 0.2;
            g.gain.setValueAtTime(0.25, noteTime);
            g.gain.exponentialRampToValueAtTime(0.001, noteTime + dur);

            osc.connect(g);
            g.connect(masterGain);
            osc.start(noteTime);
            osc.stop(noteTime + dur);
        }
    } catch(e) {}
}

function playGameOverSound() {
    try {
        if (!audioCtx || !masterGain || audioCtx.state !== 'running') return;
        var t = audioCtx.currentTime;
        var sadNotes = [392.0, 369.99, 349.23, 311.13, 293.66, 261.63, 233.08, 196.0];
        for (var i = 0; i < sadNotes.length; i++) {
            var noteTime = t + (i * 0.25);
            var osc = audioCtx.createOscillator(), g = audioCtx.createGain();
            osc.type = 'triangle';
            osc.frequency.setValueAtTime(sadNotes[i], noteTime);

            var dur = (i === sadNotes.length - 1) ? 1.3 : 0.32;
            g.gain.setValueAtTime(0.24, noteTime);
            g.gain.exponentialRampToValueAtTime(0.001, noteTime + dur);

            osc.connect(g);
            g.connect(masterGain);
            osc.start(noteTime);
            osc.stop(noteTime + dur);
        }
    } catch(e) {}
}

// --- COMPOSICIÓN TECHNO-MELANCÓLICA EN DO MENOR (Cm - Ab - Fm - G) ---

// 1. Melodía Grave & Melancólica Principal (Cuerpo Analógico Cálido)
var technoMelancholicLow = [
    // Compás 1: Cm (Profundo y nostálgico)
    261.63, 261.63, 311.13, 392.00, 311.13, 261.63, 293.66, 261.63,
    // Compás 2: Ab (Subida emotiva melancólica)
    207.65, 207.65, 261.63, 311.13, 261.63, 207.65, 233.08, 261.63,
    // Compás 3: Fm (Tristeza y tensión nocturna)
    174.61, 174.61, 207.65, 261.63, 207.65, 174.61, 196.00, 207.65,
    // Compás 4: G (Cadencia hipnótica techno)
    196.00, 196.00, 246.94, 293.66, 392.00, 293.66, 246.94, 196.00
];

// 2. Arpegio Rítmico Techno (16th-notes hipnóticas)
var technoArpNotes = [
    // Cm
    523.25, 622.25, 783.99, 622.25, 523.25, 622.25, 783.99, 1046.50,
    // Ab
    415.30, 523.25, 622.25, 523.25, 415.30, 523.25, 622.25, 830.61,
    // Fm
    349.23, 415.30, 523.25, 415.30, 349.23, 415.30, 523.25, 698.46,
    // G
    392.00, 493.88, 587.33, 493.88, 392.00, 493.88, 587.33, 783.99
];

// 3. Contrapunto Melancólico Agudo (Lead flotante)
var technoHighLead = [
    // Cm
    783.99, 0, 622.25, 0, 783.99, 1046.50, 932.33, 783.99,
    // Ab
    622.25, 0, 523.25, 0, 622.25, 830.61, 783.99, 622.25,
    // Fm
    523.25, 0, 415.30, 0, 523.25, 698.46, 622.25, 523.25,
    // G
    587.33, 0, 493.88, 0, 587.33, 783.99, 698.46, 587.33
];

// 4. Bajo Techno Rodante Principal (Rolling Techno Sub-Bass)
var technoBassline = [
    // Cm
    65.41, 65.41, 130.81, 65.41, 65.41, 130.81, 65.41, 130.81,
    // Ab
    51.91, 51.91, 103.83, 51.91, 51.91, 103.83, 51.91, 103.83,
    // Fm
    43.65, 43.65, 87.31, 43.65, 43.65, 87.31, 43.65, 87.31,
    // G
    49.00, 49.00, 98.00, 49.00, 49.00, 98.00, 49.00, 98.00
];

// 5. Melodía Secundaria de Bajos Profundos (Se activa tras 80 pasos / ~10 segundos)
var technoSecondaryDeepBass = [
    // Cm (Contrapunto de bajos analógicos marcados)
    130.81, 130.81, 155.56, 196.00, 155.56, 130.81, 116.54, 130.81,
    // Ab
    103.83, 103.83, 130.81, 155.56, 130.81, 103.83, 92.50, 103.83,
    // Fm
    87.31, 87.31, 103.83, 130.81, 103.83, 87.31, 77.78, 87.31,
    // G
    98.00, 98.00, 123.47, 146.83, 196.00, 146.83, 123.47, 98.00
];

function scheduleMusicStep(stepNumber, t) {
    var step32 = stepNumber % 32;
    var notaLow = technoMelancholicLow[step32];
    var notaArp = technoArpNotes[step32];
    var notaHigh = technoHighLead[step32];
    var notaBass = technoBassline[step32];
    var notaSecDeep = technoSecondaryDeepBass[step32];

    // Melodía secundaria de bajos: activada por timer wall-clock (10s exactos)
    var hasSecondaryDeep = running && secondaryDeepActive;

    if (isFeverActive) {
        notaLow *= 1.5;
        notaArp *= 1.5;
        notaBass *= 1.5;
        notaSecDeep *= 1.5;
        if (notaHigh > 0) notaHigh *= 1.5;
    }

    // 1. Melodía Grave Melancólica (Cuerpo Analógico Cálido)
    var oscLow = audioCtx.createOscillator(), gLow = audioCtx.createGain(), filtLow = audioCtx.createBiquadFilter();
    oscLow.type = 'sawtooth';
    oscLow.frequency.setValueAtTime(notaLow, t);
    filtLow.type = 'lowpass';
    filtLow.frequency.setValueAtTime(isFeverActive ? 1400 : (750 + Math.sin(stepNumber * 0.25) * 350), t);
    filtLow.Q.setValueAtTime(3.0, t);
    var durLow = isFeverActive ? 0.065 : 0.115;
    gLow.gain.setValueAtTime(isFeverActive ? 0.034 : 0.028, t);
    gLow.gain.exponentialRampToValueAtTime(0.001, t + durLow);
    oscLow.connect(filtLow); filtLow.connect(gLow); gLow.connect(masterGain);
    oscLow.start(t); oscLow.stop(t + durLow);
    oscLow.onended = function() { oscLow.disconnect(); filtLow.disconnect(); gLow.disconnect(); };

    // 2. Arpegio Rítmico Techno
    var oscArp = audioCtx.createOscillator(), gArp = audioCtx.createGain(), filtArp = audioCtx.createBiquadFilter();
    oscArp.type = isFeverActive ? 'sawtooth' : 'square';
    oscArp.frequency.setValueAtTime(notaArp, t);
    filtArp.type = 'lowpass';
    filtArp.frequency.setValueAtTime(isFeverActive ? 2800 : (1600 + Math.sin(stepNumber * 0.3) * 800), t);
    filtArp.Q.setValueAtTime(isFeverActive ? 4.0 : 2.5, t);
    var durArp = isFeverActive ? 0.055 : 0.095;
    gArp.gain.setValueAtTime(isFeverActive ? 0.024 : 0.016, t);
    gArp.gain.exponentialRampToValueAtTime(0.001, t + durArp);
    oscArp.connect(filtArp); filtArp.connect(gArp); gArp.connect(masterGain);
    oscArp.start(t); oscArp.stop(t + durArp);
    oscArp.onended = function() { oscArp.disconnect(); filtArp.disconnect(); gArp.disconnect(); };

    // 3. Contrapunto Agudo Melancólico
    if (notaHigh > 0) {
        var oscH = audioCtx.createOscillator(), gH = audioCtx.createGain();
        oscH.type = 'sine';
        oscH.frequency.setValueAtTime(notaHigh, t);
        var durH = isFeverActive ? 0.12 : 0.22;
        gH.gain.setValueAtTime(0.02, t);
        gH.gain.exponentialRampToValueAtTime(0.001, t + durH);
        oscH.connect(gH); gH.connect(masterGain);
        oscH.start(t); oscH.stop(t + durH);
        oscH.onended = function() { oscH.disconnect(); gH.disconnect(); };
    }

    // 4. Bajo Techno Rodante Principal
    var oscB = audioCtx.createOscillator(), gB = audioCtx.createGain(), filtB = audioCtx.createBiquadFilter();
    oscB.type = 'sawtooth';
    oscB.frequency.setValueAtTime(notaBass, t);
    filtB.type = 'lowpass';
    filtB.frequency.setValueAtTime(isFeverActive ? 850 : 500, t);
    var durB = isFeverActive ? 0.06 : 0.105;
    gB.gain.setValueAtTime(0.036, t);
    gB.gain.exponentialRampToValueAtTime(0.001, t + durB);
    oscB.connect(filtB); filtB.connect(gB); gB.connect(masterGain);
    oscB.start(t); oscB.stop(t + durB);
    oscB.onended = function() { oscB.disconnect(); filtB.disconnect(); gB.disconnect(); };

    // 5. Melodía Secundaria de Bajos Profundos (Capa desbloqueada a los 10 segundos)
    if (hasSecondaryDeep && notaSecDeep > 0) {
        var oscSec = audioCtx.createOscillator(), gSec = audioCtx.createGain(), filtSec = audioCtx.createBiquadFilter();
        oscSec.type = 'sawtooth';
        oscSec.frequency.setValueAtTime(notaSecDeep, t);
        filtSec.type = 'lowpass';
        filtSec.frequency.setValueAtTime(isFeverActive ? 950 : 650, t);
        filtSec.Q.setValueAtTime(3.5, t);
        var durSec = isFeverActive ? 0.065 : 0.115;
        gSec.gain.setValueAtTime(isFeverActive ? 0.042 : 0.036, t);
        gSec.gain.exponentialRampToValueAtTime(0.001, t + durSec);
        oscSec.connect(filtSec); filtSec.connect(gSec); gSec.connect(masterGain);
        oscSec.start(t); oscSec.stop(t + durSec);
        oscSec.onended = function() { oscSec.disconnect(); filtSec.disconnect(); gSec.disconnect(); };
    }

    // 6. Batería Techno
    if (step32 % 4 === 0) playDrumKick(t);
    if (step32 % 8 === 4) playDrumSnare(t);
    if (step32 % 2 === 1) playDrumHiHat(t, step32 % 4 === 2);
}

function soundBombExplode() {
    try {
        if (!audioCtx || !cachedWhiteNoise || audioCtx.state !== 'running') return;
        var t = audioCtx.currentTime;
        var noise = audioCtx.createBufferSource();
        noise.buffer = cachedWhiteNoise;
        var filt = audioCtx.createBiquadFilter();
        filt.type = 'lowpass';
        filt.frequency.setValueAtTime(4000, t);
        filt.frequency.exponentialRampToValueAtTime(80, t + 0.45);
        var gN = audioCtx.createGain();
        gN.gain.setValueAtTime(0.65, t);
        gN.gain.exponentialRampToValueAtTime(0.001, t + 0.45);
        noise.connect(filt); filt.connect(gN); gN.connect(masterGain);
        noise.start(t); noise.stop(t + 0.45);
    } catch(e) {}
}

function soundImpact() {
    try {
        if (!audioCtx || !masterGain || audioCtx.state !== 'running') return;
        var t = audioCtx.currentTime;
        var osc = audioCtx.createOscillator(), g = audioCtx.createGain();
        osc.type = 'triangle';
        osc.frequency.setValueAtTime(180, t);
        osc.frequency.exponentialRampToValueAtTime(35, t + 0.12);
        g.gain.setValueAtTime(0.3, t);
        g.gain.exponentialRampToValueAtTime(0.001, t + 0.12);
        osc.connect(g); g.connect(masterGain);
        osc.start(t); osc.stop(t + 0.12);
    } catch(e) {}
}

// --- LÓGICA DEL TABLERO Y JUEGO ---
function initGrid() {
    grid = Array.from({ length: SENS }, function() {
        return Array.from({ length: N }, function() { return { color: 0, off: 0, flash: 0 }; });
    });
}

function registrarPiezaDestruida() {
    levelProgress += 1;
    if (levelProgress >= 100) {
        if (currentLevel < 50) {
            var completedLevel = currentLevel;
            currentLevel++;
            levelProgress = 0;
            
            var speedBase = 1.0;
            var speedIncr = 0.02;
            
            if (gameMode === 'arcade') {
                if (difficulty === 'hard') {
                    speedBase = 1.1;
                } else if (difficulty === 'adrenaline') {
                    speedBase = 1.15;
                }
            } else {
                speedBase = practiceSettings.speedMult;
            }

            speed = speedBase + ((currentLevel - 1) * speedIncr);

            addTextSplash('LEVEL ' + completedLevel + ' COMPLETED!', '#05FFA1', true);
            playLevelUpSound();
            shake = 16.0;

            for (var s = 0; s < SENS; s++) {
                createExplosionAmpliada(s, 2, COLS[(s % 4) + 1]);
            }

            document.getElementById('val-level').innerText = currentLevel;
        } else {
            levelProgress = 100;
            addTextSplash('MAX LEVEL 50 REACHED!!', '#FF007F', true);
        }
    }
    levelBar.style.width = levelProgress + '%';
    levelLabel.innerText = 'NIVEL ' + currentLevel + ' - ' + levelProgress + '%';
}

function getNextPieceData() {
    var ahora = Date.now();
    
    var bombProb = 40000;
    if (gameMode === 'arcade') {
        if (difficulty === 'adrenaline') bombProb = 25000;
    } else {
        if (practiceSettings.feverFreq === 'FRECUENTE') bombProb = 25000;
        if (practiceSettings.feverFreq === 'MUY FRECUENTE') bombProb = 12000;
    }

    var esBomba = bombaFinalPendiente || (rachaSinMatch >= 10) || (ahora - tiempoUltimaBomba >= bombProb);
    if (esBomba) {
        rachaSinMatch = 0;
        tiempoUltimaBomba = ahora;
        bombaFinalPendiente = false;
    }

    var numColors = 4;
    var allowedIndices = [1, 3, 4]; // Magenta, Cyan, Amarilla (Evitar Verde #2)

    if (gameMode === 'arcade') {
        if (difficulty === 'easy') {
            allowedIndices = [1, 3, 4];
        } else if (difficulty === 'normal') {
            allowedIndices = [1, 3, 4, 6]; 
        } else if (difficulty === 'hard' || difficulty === 'adrenaline') {
            allowedIndices = [1, 3, 4, 6, 7];
        }
    } else {
        numColors = practiceSettings.colors;
        allowedIndices = [];
        for (var i = 1; i <= numColors; i++) {
            if (i !== 2) allowedIndices.push(i); // Saltar el verde de la bomba
        }
        // Si el usuario pidió N colores, nos aseguramos de tener N colores que no sean el 2
        while (allowedIndices.length < numColors) {
            var nextIdx = allowedIndices.length + 1;
            if (nextIdx === 2) nextIdx++;
            if (nextIdx > 10) break;
            allowedIndices.push(nextIdx);
        }
    }

    var randomColor = allowedIndices[Math.floor(Math.random() * allowedIndices.length)];
    return { dir: Math.floor(Math.random() * SENS), color: esBomba ? 5 : randomColor };
}

function spawn() {
    if (isGameOver) return;
    if (!nextP) nextP = getNextPieceData();
    var spdActual = isFeverActive ? speed * 2.2 : speed;
    piece = { dir: nextP.dir, r: R_EXT + 100, spd: spdActual, color: nextP.color };

    if (isFeverActive && piece.color !== 5) {
        // En Fever Mode, forzamos que la segunda pieza sea del mismo color para facilitar combos
        pieceSecondary = { dir: (nextP.dir + 4) % SENS, r: R_EXT + 100, spd: spdActual, color: piece.color };
    } else {
        pieceSecondary = null;
    }
    nextP = getNextPieceData();
    halos = [];
}

function quickDrop() {
    if (animLock || isPaused || !running || isGameOver) return;
    if (piece) piece.spd = 16.0;
    if (pieceSecondary) pieceSecondary.spd = 16.0;
}

function togglePause() {
    if (!running || isGameOver) return;
    isPaused = !isPaused;
    if (isPaused) {
        pauseStartTime = Date.now();
        pauseMask.classList.remove('hidden');
        stopMusic();
    } else {
        if (pauseStartTime > 0) {
            var pausedDuration = Date.now() - pauseStartTime;
            if (isFeverActive) {
                feverEndTime += pausedDuration;
            }
        }
        pauseMask.classList.add('hidden');
        initAudio();
        startMusic();
    }
}

function triggerGameOver() {
    running = false;
    isGameOver = true;
    animLock = true;
    stopMusic();

    soundBombExplode();
    setTimeout(playGameOverSound, 300);

    shake = 30.0;

    for (var s = 0; s < SENS; s++) {
        for (var n = 0; n < N; n++) {
            if (grid[s][n].color !== 0) {
                var angle = s * PASO - Math.PI / 2 + PASO / 2 + rotV;
                var dist = R_INT + n * AN + AN / 2;
                var px = CX + Math.cos(angle) * dist;
                var py = CY + Math.sin(angle) * dist;
                var blastSpeed = 4.5 + Math.random() * 8.0;
                var spreadAng = angle + (Math.random() - 0.5) * 0.4;

                shatteredPieces.push({
                    x: px,
                    y: py,
                    vx: Math.cos(spreadAng) * blastSpeed,
                    vy: Math.sin(spreadAng) * blastSpeed,
                    rot: Math.random() * Math.PI * 2,
                    vrot: (Math.random() - 0.5) * 0.2,
                    color: COLS[grid[s][n].color] || '#FF007F',
                    size: AN * 0.85,
                    life: 1.0,
                    decay: 0.012 + Math.random() * 0.012
                });
                grid[s][n] = { color: 0, off: 0, flash: 0 };
            }
        }
    }

    if (piece) {
        var aP = piece.dir * PASO - Math.PI / 2 + PASO / 2;
        shatteredPieces.push({
            x: CX + Math.cos(aP) * piece.r,
            y: CY + Math.sin(aP) * piece.r,
            vx: Math.cos(aP) * 7.5,
            vy: Math.sin(aP) * 7.5,
            rot: 0, vrot: 0.18,
            color: COLS[piece.color] || '#00F5FF',
            size: AN, life: 1.0, decay: 0.015
        });
        piece = null;
    }
    if (pieceSecondary) {
        var aP = pieceSecondary.dir * PASO - Math.PI / 2 + PASO / 2;
        shatteredPieces.push({
            x: CX + Math.cos(aP) * pieceSecondary.r,
            y: CY + Math.sin(aP) * pieceSecondary.r,
            vx: Math.cos(aP) * 7.5,
            vy: Math.sin(aP) * 7.5,
            rot: 0, vrot: -0.18,
            color: COLS[pieceSecondary.color] || '#00F5FF',
            size: AN, life: 1.0, decay: 0.015
        });
        pieceSecondary = null;
    }

    document.getElementById('go-score').innerText = score;
    document.getElementById('go-level').innerText = currentLevel;
    document.getElementById('go-hi').innerText = hi;

    setTimeout(function() {
        gameOverMask.classList.remove('hidden');
    }, 450);
}

function addFeverProgress(amount) {
    if (isFeverActive || isGameOver) return;
    
    var mult = 1.0;
    if (gameMode === 'arcade' && difficulty === 'adrenaline') mult = 1.8;
    if (gameMode === 'practice') {
        if (practiceSettings.feverFreq === 'FRECUENTE') mult = 1.8;
        if (practiceSettings.feverFreq === 'MUY FRECUENTE') mult = 3.5;
    }

    feverPoints += amount * mult;
    if (feverPoints >= 100) {
        feverPoints = 100;
        isFeverActive = true;
        feverStartTime = Date.now();
        feverEndTime = feverStartTime + feverDurationMs;
        feverBar.style.width = '100%';
        addTextSplash('FEVER 12s EXTREME!', '#FFB800', true);
        shake = 15;
        soundFeverTransition(true);
        startMusic();
    } else {
        feverBar.style.width = feverPoints + '%';
    }
}

function addScore(pts) {
    var finalPts = isFeverActive ? pts * 2 : pts;
    score += finalPts;
    document.getElementById('val-score').innerText = score;
    if (score > hi) { hi = score; localStorage.setItem('radiax_hi', hi); }
    addFeverProgress(pts * 0.4);
}

function soundFeverTransition(isStarting) {
    try {
        if (!audioCtx || !masterGain || audioCtx.state !== 'running') return;
        var t = audioCtx.currentTime;
        var dur = 2.2;
        
        // 1. Capa de "Motor/Turbina" (Oscilador SuperSaw)
        var oscs = [];
        var detunes = [-10, -5, 0, 5, 10];
        var gEngine = audioCtx.createGain();
        
        detunes.forEach(function(d) {
            var o = audioCtx.createOscillator();
            o.type = 'sawtooth';
            o.detune.setValueAtTime(d, t);
            if (isStarting) {
                o.frequency.setValueAtTime(60, t);
                o.frequency.exponentialRampToValueAtTime(800, t + dur);
            } else {
                o.frequency.setValueAtTime(800, t);
                o.frequency.exponentialRampToValueAtTime(60, t + dur);
            }
            o.connect(gEngine);
            oscs.push(o);
        });

        // 2. Filtro Resonante (Barrido de frecuencia espacial)
        var filt = audioCtx.createBiquadFilter();
        filt.type = 'lowpass';
        filt.Q.setValueAtTime(15, t); // Alta resonancia para el "silbido" espacial
        if (isStarting) {
            filt.frequency.setValueAtTime(100, t);
            filt.frequency.exponentialRampToValueAtTime(8000, t + dur);
        } else {
            filt.frequency.setValueAtTime(8000, t);
            filt.frequency.exponentialRampToValueAtTime(100, t + dur);
        }

        // 3. Capa de Ruido (Viento estelar)
        var noise = audioCtx.createBufferSource();
        noise.buffer = cachedWhiteNoise;
        var gNoise = audioCtx.createGain();
        var nFilt = audioCtx.createBiquadFilter();
        nFilt.type = 'bandpass';
        nFilt.frequency.setValueAtTime(isStarting ? 500 : 4000, t);
        nFilt.frequency.exponentialRampToValueAtTime(isStarting ? 4000 : 500, t + dur);
        
        gNoise.gain.setValueAtTime(0, t);
        gNoise.gain.linearRampToValueAtTime(0.1, t + 0.5);
        gNoise.gain.linearRampToValueAtTime(0, t + dur);

        // Envolvente principal
        gEngine.gain.setValueAtTime(0, t);
        gEngine.gain.linearRampToValueAtTime(0.2, t + 0.2);
        gEngine.gain.exponentialRampToValueAtTime(0.001, t + dur);

        // Conexiones
        gEngine.connect(filt);
        filt.connect(masterGain);
        
        noise.connect(nFilt);
        nFilt.connect(gNoise);
        gNoise.connect(masterGain);

        oscs.forEach(function(o) { o.start(t); o.stop(t + dur); });
        noise.start(t);
        noise.stop(t + dur);
    } catch(e) {}
}

// Rotación 100% fluida sin reinicios de audio
function rotate(d) {
    if (!running || isPaused || isGameOver) return;
    rotT += d * PASO;
}

function createExplosion(sector, nivel, colorHex) {
    var aC = sector * PASO - Math.PI / 2 + PASO / 2 + rotV, rM = R_INT + (nivel * AN) + AN / 2;
    var bx = CX + Math.cos(aC) * rM, by = CY + Math.sin(aC) * rM;
    var maxParts = Math.min(22, 50 - parts.length);
    for (var i = 0; i < maxParts; i++) {
        var ang = Math.random() * Math.PI * 2, v = 2.0 + Math.random() * 5.0;
        parts.push({ x: bx, y: by, vx: Math.cos(ang) * v, vy: Math.sin(ang) * v, r: 1.5 + Math.random() * 2.5, color: colorHex, life: 1.0, decay: 0.025 + Math.random() * 0.03 });
    }
    if (shock.length < 5) {
        shock.push({ x: bx, y: by, r: 5, alpha: 0.9, color: colorHex });
    }
}

function createExplosionAmpliada(sector, nivel, colorHex) {
    var aC = sector * PASO - Math.PI / 2 + PASO / 2 + rotV, rM = R_INT + (nivel * AN) + AN / 2;
    var bx = CX + Math.cos(aC) * rM, by = CY + Math.sin(aC) * rM;
    var maxParts = Math.min(32, 70 - parts.length);
    for (var i = 0; i < maxParts; i++) {
        var ang = Math.random() * Math.PI * 2, v = 3.0 + Math.random() * 6.5;
        parts.push({ x: bx, y: by, vx: Math.cos(ang) * v, vy: Math.sin(ang) * v, r: 2.0 + Math.random() * 3.5, color: colorHex, life: 1.0, decay: 0.02 + Math.random() * 0.025 });
    }
    if (shock.length < 5) {
        shock.push({ x: bx, y: by, r: 10, alpha: 1.0, color: '#00FF00' });
    }
}

function addTextSplash(txt, col, isBig) {
    if (!col) col = '#00F5FF';
    textSplashes.push({
        txt: txt,
        y: CY - 10,
        alpha: 1.0,
        col: col,
        isBig: !!isBig
    });
}

function detonarBomba(sectorCentro, nivelCentro) {
    animLock = true;
    freeze = 22;
    shake = 32.0;
    soundBombExplode();

    var n = nivelCentro;
    var sectoresADestruir = [];
    var modoExplosion = "NORMAL";

    // --- 1. DETECCIÓN DE COMBOS NATURALES (Filas N-1, N, N+1) ---
    var filasABuscar = [n - 1, n, n + 1];
    var hayComboNatural = false;

    for (var i = 0; i < filasABuscar.length; i++) {
        var r = filasABuscar[i];
        if (r < 0 || r >= N) continue;
        for (var s = 0; s < SENS; s++) {
            var c = grid[s][r].color;
            if (c === 0 || c >= 5) continue;
            // Combo horizontal
            if (grid[(s + 1) % SENS][r].color === c && grid[(s + 2) % SENS][r].color === c) {
                hayComboNatural = true; break;
            }
            // Combo vertical
            if (r < N - 2 && grid[s][r + 1].color === c && grid[s][r + 2].color === c) {
                hayComboNatural = true; break;
            }
        }
        if (hayComboNatural) break;
    }

    if (hayComboNatural) {
        modoExplosion = "COMBO_TRIPLE";
        addTextSplash("SMART BOMB: COMBO DETECTED!", "#05FFA1", true);
        // Destruir las 3 filas
        filasABuscar.forEach(function(r) {
            if (r >= 0 && r < N) {
                for (var s = 0; s < SENS; s++) if (grid[s][r].color !== 0) sectoresADestruir.push({s: s, n: r});
            }
        });
    } 

    // --- 2. TRANSFORMACIÓN DE COLOR (Si no hay combo, intentar crear uno en N o N-1) ---
    if (sectoresADestruir.length === 0) {
        var filasTransformar = [n, n - 1];
        var transformado = false;
        for (var i = 0; i < filasTransformar.length; i++) {
            var r = filasTransformar[i];
            if (r < 0 || r >= N) continue;
            for (var s = 0; s < SENS; s++) {
                if (grid[s][r].color === 0 || grid[s][r].color >= 5) continue;
                // Probar si cambiando este color a uno de sus vecinos horizontales crea un match
                var colorVecino = grid[(s + 1) % SENS][r].color;
                if (colorVecino > 0 && colorVecino < 5 && grid[(s - 1 + SENS) % SENS][r].color === colorVecino) {
                    grid[s][r].color = colorVecino; // ¡Transformación!
                    transformado = true;
                }
                if (transformado) break;
            }
            if (transformado) {
                modoExplosion = "TRANSFORM";
                addTextSplash("SMART BOMB: COLOR SYNC!", "#00F5FF", true);
                filasTransformar.forEach(function(r2) {
                    if (r2 >= 0 && r2 < N) {
                        for (var s = 0; s < SENS; s++) if (grid[s][r2].color !== 0) sectoresADestruir.push({s: s, n: r2});
                    }
                });
                break;
            }
        }
    }

    // --- 3. FALLBACK: ELIMINAR ANILLO COMPLETO ---
    if (sectoresADestruir.length === 0) {
        addTextSplash("RING CLEAR", "#FFB800");
        for (var s = 0; s < SENS; s++) {
            if (grid[s][n].color !== 0) sectoresADestruir.push({s: s, n: n});
        }
    }

    // --- EJECUCIÓN ---
    sectoresADestruir.forEach(function(pos) { grid[pos.s][pos.n].flash = 35; });

    setTimeout(function() {
        sectoresADestruir.forEach(function(pos) {
            if (grid[pos.s][pos.n].color !== 0) {
                createExplosionAmpliada(pos.s, pos.n, COLS[grid[pos.s][pos.n].color] || '#00FF00');
                grid[pos.s][pos.n] = { color: 0, off: 0, flash: 0 };
                registrarPiezaDestruida();
            }
        });

        setTimeout(function() {
            aplicarGravedadCascada();
            setTimeout(function() { animLock = false; checkMatches(); }, 240);
        }, 120);
    }, 360);
}

function aplicarGravedadCascada() {
    for (var s = 0; s < SENS; s++) {
        var ac = 0;
        for (var n = 0; n < N; n++) {
            if (grid[s][n].color !== 0) {
                if (n !== ac) {
                    grid[s][ac] = { color: grid[s][n].color, off: (n - ac) * AN, flash: 0 };
                    grid[s][n] = { color: 0, off: 0, flash: 0 };
                }
                ac++;
            }
        }
    }
}

function procesarAterrizaje(pObj) {
    var aP = pObj.dir * PASO - Math.PI / 2 + PASO / 2;
    var aR = (aP - rotV + Math.PI / 2) % (Math.PI * 2);
    if (aR < 0) aR += Math.PI * 2;
    var sCur = Math.floor(aR / PASO) % SENS;

    var targetN = -1;
    for (var n = 0; n < N; n++) { if (grid[sCur][n].color === 0) { targetN = n; break; } }

    if (targetN === -1) {
        if (pObj.r <= R_EXT) {
            triggerGameOver();
            return false;
        }
    } else {
        if (pObj.r <= R_INT + (targetN * AN)) {
            if (pObj.color === 5) {
                detonarBomba(sCur, targetN);
                return true;
            } else {
                grid[sCur][targetN] = { color: pObj.color, off: 0, flash: 10 };
                soundImpact(); shake = 6.0;
                if (navigator.vibrate) navigator.vibrate(35);
                addScore(10);
                return true;
            }
        }
    }
    return false;
}

function update() {
    for (var i = shatteredPieces.length - 1; i >= 0; i--) {
        var sp = shatteredPieces[i];
        sp.x += sp.vx;
        sp.y += sp.vy;
        sp.rot += sp.vrot;
        sp.life -= sp.decay;
        if (sp.life <= 0) shatteredPieces.splice(i, 1);
    }

    if (!running || isPaused || isGameOver) return;

    if (isFeverActive) {
        var remainingMs = feverEndTime - Date.now();
        if (remainingMs > 0) {
            feverBar.style.width = Math.min(100, Math.max(0, (remainingMs / feverDurationMs) * 100)) + '%';
        } else {
            isFeverActive = false;
            feverPoints = 0;
            feverBar.style.width = '0%';
            feverEndTime = Date.now(); // Para la desaceleración del fondo
            bombaFinalPendiente = true;

            soundFeverTransition(false);

            if ((gameMode === 'practice' && practiceSettings.waveEnabled) || (gameMode === 'arcade' && difficulty === 'adrenaline')) {
                triggerWaveMode();
            }

            startMusic();
        }
    }

    if (freeze > 0) { freeze--; return; }

    rotV += (rotT - rotV) * 0.22;
    if (shake > 0) { shake *= 0.85; if (shake < 0.2) shake = 0; }

    for (var i = halos.length - 1; i >= 0; i--) { halos[i].a -= 0.04; if (halos[i].a <= 0) halos.splice(i, 1); }
    for (var i = parts.length - 1; i >= 0; i--) { var p = parts[i]; p.x += p.vx; p.y += p.vy; p.life -= p.decay; if (p.life <= 0) parts.splice(i, 1); }
    for (var i = shock.length - 1; i >= 0; i--) { var o = shock[i]; o.r += 3.5; o.alpha -= 0.04; if (o.alpha <= 0) shock.splice(i, 1); }
    
    for (var i = textSplashes.length - 1; i >= 0; i--) {
        var t = textSplashes[i];
        t.y -= t.isBig ? 0.35 : 0.5;
        t.alpha -= t.isBig ? 0.0055 : 0.009;
        if (t.alpha <= 0) textSplashes.splice(i, 1);
    }

    var animG = false;
    for (var s = 0; s < SENS; s++) {
        for (var n = 0; n < N; n++) {
            if (grid[s][n].off > 0) { grid[s][n].off -= 3.0; if (grid[s][n].off < 0) grid[s][n].off = 0; animG = true; }
            if (grid[s][n].flash > 0) grid[s][n].flash--;
        }
    }

    if (animLock || animG) return;

    var algunoAterrizo = false;
    if (piece) {
        piece.r -= piece.spd;
        if (halos.length < 3) halos.push({ r: piece.r, dir: piece.dir, color: piece.color, a: 0.5 });
        if (procesarAterrizaje(piece)) { piece = null; algunoAterrizo = true; }
    }
    if (pieceSecondary) {
        pieceSecondary.r -= pieceSecondary.spd;
        if (halos.length < 3) halos.push({ r: pieceSecondary.r, dir: pieceSecondary.dir, color: pieceSecondary.color, a: 0.5 });
        if (procesarAterrizaje(pieceSecondary)) { pieceSecondary = null; algunoAterrizo = true; }
    }

    if (algunoAterrizo && !piece && !pieceSecondary) {
        combo = 0; rachaSinMatch++; checkMatches();
    }
}

function triggerWaveMode() {
    if (isGameOver) return;
    animLock = true;
    var step = 0;
    var waveInterval = setInterval(function() {
        if (isGameOver || step >= SENS) {
            clearInterval(waveInterval);
            animLock = false;
            if (!piece && !pieceSecondary) spawn();
            return;
        }
        
        var colIdx = [1, 3, 4, 6, 7][step % 5];
        
        var targetN = -1;
        for (var n = 0; n < N; n++) { if (grid[step][n].color === 0) { targetN = n; break; } }
        
        if (targetN !== -1) {
            grid[step][targetN] = { color: colIdx, off: 60, flash: 15 };
            createExplosion(step, targetN, COLS[colIdx]);
            soundImpact();
        } else {
            triggerGameOver();
            clearInterval(waveInterval);
        }
        
        step++;
    }, 90); // Ajustado a 90ms según pedido
}

function checkMatches() {
    if (isGameOver) return;

    for (var s = 0; s < SENS; s++) {
        matchMark[s].fill(0);
    }

    var match = false, maxTiro = 0, es2x2 = false;

    // 1. Matches 2x2
    for (var s = 0; s < SENS; s++) {
        var sNext = (s + 1) % SENS;
        for (var n = 0; n < N - 1; n++) {
            var c = grid[s][n].color;
            if (c !== 0 && c < 5 && c === grid[sNext][n].color && c === grid[s][n + 1].color && c === grid[sNext][n + 1].color) {
                match = true; es2x2 = true;
                matchMark[s][n] = matchMark[sNext][n] = matchMark[s][n + 1] = matchMark[sNext][n + 1] = 1;
            }
        }
    }

    // 2. Matches Verticales
    for (var s = 0; s < SENS; s++) {
        var racha = 1;
        for (var n = 0; n < N; n++) {
            var c = grid[s][n].color;
            if (c !== 0 && c < 5 && n < N - 1 && grid[s][n + 1].color === c) racha++;
            else {
                if (racha >= 3) { match = true; if (racha > maxTiro) maxTiro = racha; for (var k = n - racha + 1; k <= n; k++) matchMark[s][k] = 1; }
                racha = 1;
            }
        }
    }

    // 3. Matches Horizontales
    for (var n = 0; n < N; n++) {
        for (var s = 0; s < SENS; s++) {
            var c = grid[s][n].color;
            if (c === 0 || c >= 5) continue;
            var celdasCount = 1;
            for (var step = 1; step < SENS; step++) {
                var nextS = (s + step) % SENS;
                if (grid[nextS][n].color === c) celdasCount++;
                else break;
            }
            if (celdasCount >= 3) {
                match = true; if (celdasCount > maxTiro) maxTiro = celdasCount;
                for (var step = 0; step < celdasCount; step++) {
                    matchMark[(s + step) % SENS][n] = 1;
                }
            }
        }
    }

    if (match) {
        animLock = true;
        combo++;
        rachaSinMatch = 0;

        for (var s = 0; s < SENS; s++) {
            for (var n = 0; n < N; n++) {
                if (matchMark[s][n]) grid[s][n].flash = 25;
            }
        }

        soundComboChime(combo);
        soundBombExplode();

        shake = Math.min(26.0, 12.0 + (combo * 4.0));
        if (navigator.vibrate) {
            navigator.vibrate([40, 30, Math.min(120, 50 + combo * 20)]);
        }

        if (es2x2) {
            addTextSplash('2x2 BLOCK CLEAR!', '#FF007F', true);
            addScore(150);
        } else if (maxTiro > 3) {
            addTextSplash(maxTiro + ' IN A SHOT!', '#FFB800', true);
            addScore(100 * maxTiro);
        } else if (combo > 1) {
            addTextSplash('COMBO x' + combo + '!', '#00F5FF', true);
            addScore(50 * combo);
        } else {
            addScore(30);
        }

        var microDemoraMs = (combo > 1 || es2x2 || maxTiro > 3) ? 460 : 250;
        freeze = (combo > 1 || es2x2 || maxTiro > 3) ? 14 : 7;

        setTimeout(function() {
            for (var s = 0; s < SENS; s++) {
                for (var n = 0; n < N; n++) {
                    if (matchMark[s][n]) {
                        createExplosion(s, n, COLS[grid[s][n].color]);
                        grid[s][n] = { color: 0, off: 0, flash: 0 };
                        registrarPiezaDestruida();
                    }
                }
            }
            aplicarGravedadCascada();
            setTimeout(function() { animLock = false; checkMatches(); }, 240);
        }, microDemoraMs);
    } else {
        animLock = false;
        if (!piece && !pieceSecondary) spawn();
    }
}

function drawArc(r1, r2, a1, a2, color, flash) {
    ctx.beginPath(); ctx.arc(0, 0, r1, a1, a2, false); ctx.arc(0, 0, r2, a2, a1, true);
    ctx.closePath(); ctx.fillStyle = flash ? '#FFFFFF' : color; ctx.fill();
    ctx.strokeStyle = 'rgba(5, 3, 12, 0.85)'; ctx.lineWidth = 1.4; ctx.stroke();
}

function render() {
    ctx.clearRect(0, 0, 360, 360);
    ctx.save();
    if (shake > 0) ctx.translate((Math.random() - 0.5) * shake, (Math.random() - 0.5) * shake);

    ctx.strokeStyle = isFeverActive ? '#FFB800' : 'rgba(255, 0, 127, 0.5)';
    ctx.lineWidth = 1.8;
    ctx.beginPath();
    ctx.arc(CX, CY, R_EXT + 100, 0, Math.PI * 2);
    ctx.stroke();

    // Previsualización limpia
    if (nextP && !isGameOver && piece) {
        var midR = R_EXT + 45;
        if (piece.r <= midR) {
            var fadeRatio = Math.min(1.0, (midR - piece.r) / 35.0);
            var aC = nextP.dir * PASO - Math.PI / 2 + PASO / 2;
            var pulseAlpha = 0.55 + Math.sin(Date.now() * 0.008) * 0.15;

            ctx.save();
            ctx.translate(CX, CY);
            ctx.globalAlpha = fadeRatio * pulseAlpha;
            drawArc(R_EXT + 12, R_EXT + 22, aC - PASO/2, aC + PASO/2, COLS[nextP.color]);
            ctx.restore();
        }
    }

    for (var i = 0; i < halos.length; i++) {
        var ht = halos[i];
        var aC = ht.dir * PASO - Math.PI / 2 + PASO / 2;
        ctx.save(); ctx.translate(CX, CY); ctx.globalAlpha = ht.a * 0.5;
        drawArc(ht.r, ht.r + AN, aC - PASO/2, aC + PASO/2, COLS[ht.color]);
        ctx.restore();
    }

    // --- RENDERIZADO DEL TABLERO RADIAL ROTATORIO (OPTIMIZADO EN 2 PASES) ---
    ctx.save();
    ctx.translate(CX, CY);
    ctx.rotate(rotV);
    var ms = Date.now();

    // Paso 1: Todas las celdas vacías en un solo trazo por lotes
    ctx.beginPath();
    ctx.strokeStyle = 'rgba(0, 245, 255, 0.16)';
    ctx.lineWidth = 1.2;
    for (var s = 0; s < SENS; s++) {
        var a1 = s * PASO - Math.PI / 2, a2 = a1 + PASO;
        for (var n = 0; n < N; n++) {
            if (grid[s][n].color === 0) {
                var r1 = R_INT + n * AN + grid[s][n].off, r2 = r1 + AN;
                ctx.moveTo(Math.cos(a1) * r1, Math.sin(a1) * r1);
                ctx.arc(0, 0, r1, a1, a2, false);
                ctx.arc(0, 0, r2, a2, a1, true);
                ctx.closePath();
            }
        }
    }
    ctx.stroke();

    // Paso 2: Dibujar celdas ocupadas
    for (var s = 0; s < SENS; s++) {
        var a1 = s * PASO - Math.PI / 2, a2 = a1 + PASO;
        for (var n = 0; n < N; n++) {
            var c = grid[s][n].color;
            if (c !== 0) {
                var r1 = R_INT + n * AN + grid[s][n].off, r2 = r1 + AN;
                drawArc(r1, r2, a1, a2, COLS[c], grid[s][n].flash > 0);
            }
        }
    }

    // Centro radial abierto
    ctx.strokeStyle = 'rgba(0, 245, 255, 0.25)';
    ctx.lineWidth = 1.5;
    ctx.beginPath();
    ctx.arc(0, 0, R_INT, 0, Math.PI * 2);
    ctx.stroke();

    ctx.restore();

    // Pieza que cae
    if (piece && !isGameOver) {
        var aC = piece.dir * PASO - Math.PI / 2 + PASO / 2;
        ctx.save(); ctx.translate(CX, CY);
        if (piece.color === 5 && Math.floor(ms / 80) % 2 === 0) {
            drawArc(piece.r, piece.r + AN, aC - PASO/2, aC + PASO/2, '#FFFFFF');
        } else {
            drawArc(piece.r, piece.r + AN, aC - PASO/2, aC + PASO/2, COLS[piece.color]);
        }
        ctx.restore();
    }

    if (pieceSecondary && !isGameOver) {
        var aC = pieceSecondary.dir * PASO - Math.PI / 2 + PASO / 2;
        ctx.save(); ctx.translate(CX, CY);
        drawArc(pieceSecondary.r, pieceSecondary.r + AN, aC - PASO/2, aC + PASO/2, COLS[pieceSecondary.color]);
        ctx.restore();
    }

    for (var i = 0; i < shatteredPieces.length; i++) {
        var sp = shatteredPieces[i];
        ctx.save();
        ctx.translate(sp.x, sp.y);
        ctx.rotate(sp.rot);
        ctx.globalAlpha = Math.max(0, sp.life);
        ctx.fillStyle = sp.color;
        ctx.fillRect(-sp.size / 2, -sp.size / 2, sp.size, sp.size);
        ctx.restore();
    }

    for (var i = 0; i < shock.length; i++) {
        var o = shock[i]; ctx.save(); ctx.globalAlpha = o.alpha; ctx.strokeStyle = o.color; ctx.lineWidth = 2.0;
        ctx.beginPath(); ctx.arc(o.x, o.y, o.r, 0, Math.PI * 2); ctx.stroke(); ctx.restore();
    }
    for (var i = 0; i < parts.length; i++) {
        var p = parts[i]; ctx.save(); ctx.globalAlpha = p.life; ctx.fillStyle = p.color;
        ctx.beginPath(); ctx.arc(p.x, p.y, p.r, 0, Math.PI * 2); ctx.fill(); ctx.restore();
    }

    // --- CARTELES DE COMBO CON BADGE OSCURO DE ALTO CONTRASTE (100% LEGIBLES) ---
    for (var i = 0; i < textSplashes.length; i++) {
        var t = textSplashes[i];
        ctx.save();
        ctx.globalAlpha = Math.max(0, t.alpha);
        ctx.font = t.isBig ? 'bold 19px "Courier New", monospace' : 'bold 15px "Courier New", monospace';
        ctx.textAlign = 'center';
        ctx.textBaseline = 'middle';

        var txtWidth = ctx.measureText(t.txt).width;
        var badgeW = txtWidth + 24;
        var badgeH = t.isBig ? 32 : 24;
        var badgeX = CX - badgeW / 2;
        var badgeY = t.y - badgeH / 2;

        ctx.fillStyle = 'rgba(6, 4, 16, 0.92)';
        ctx.strokeStyle = t.col;
        ctx.lineWidth = 2.0;
        ctx.beginPath();
        if (ctx.roundRect) {
            ctx.roundRect(badgeX, badgeY, badgeW, badgeH, 6);
        } else {
            ctx.rect(badgeX, badgeY, badgeW, badgeH);
        }
        ctx.fill();
        ctx.stroke();

        ctx.fillStyle = '#FFFFFF';
        ctx.fillText(t.txt, CX, t.y);

        ctx.restore();
    }
    ctx.restore();
}

function loop(now) {
    renderFondoEspacial(now || performance.now());
    update();
    render();
    requestAnimationFrame(loop);
}

initEstrellas();

var tX = 0, tY = 0;
cvs.addEventListener('touchstart', function(e) {
    initAudio();
    tX = e.touches[0].clientX;
    tY = e.touches[0].clientY;
}, {passive: true});

cvs.addEventListener('touchend', function(e) {
    var dX = e.changedTouches[0].clientX - tX, dY = e.changedTouches[0].clientY - tY;
    if (Math.abs(dY) > 35 && dY > 0 && Math.abs(dY) > Math.abs(dX)) quickDrop();
    else if (Math.abs(dX) > 25) rotate(dX > 0 ? 1 : -1);
}, {passive: true});

function startGame() {
    mask.style.display = 'none';
    pauseMask.classList.add('hidden');
    gameOverMask.classList.add('hidden');

    var speedBase = 1.0;
    if (gameMode === 'arcade') {
        if (difficulty === 'hard') speedBase = 1.1;
        if (difficulty === 'adrenaline') speedBase = 1.15;
    } else {
        speedBase = practiceSettings.speedMult;
    }

    score = 0; speed = speedBase;
    currentLevel = 1; levelProgress = 0;
    document.getElementById('val-level').innerText = 1;
    levelBar.style.width = '0%';
    levelLabel.innerText = 'NIVEL 1 - 0%';

    rachaSinMatch = 0; bombaFinalPendiente = false;
    tiempoUltimaBomba = Date.now(); feverPoints = 0; isFeverActive = false; feverBar.style.width = '0%';
    document.getElementById('val-score').innerText = 0;

    isPaused = false;
    isGameOver = false;
    shatteredPieces = [];
    parts = [];
    shock = [];
    halos = [];
    stepM = 0;
    animLock = false;

    // Reset melodía secundaria
    secondaryDeepActive = false;
    if (secondaryDeepTimer) { clearTimeout(secondaryDeepTimer); secondaryDeepTimer = null; }

    initGrid();
    spawn();
    running = true;
    setTimeout(initAudio, 50);
}

// --- MANEJO DE MENÚS ---
var mainMenu = document.getElementById('main-menu');
var arcadeMenu = document.getElementById('arcade-menu');
var practiceMenu = document.getElementById('practice-menu');

document.getElementById('btn-arcade-menu').onclick = function() {
    mainMenu.classList.add('hidden');
    arcadeMenu.classList.remove('hidden');
};

document.getElementById('btn-practice-menu').onclick = function() {
    mainMenu.classList.add('hidden');
    practiceMenu.classList.remove('hidden');
};

document.querySelectorAll('.btn-back').forEach(function(btn) {
    btn.onclick = function() {
        arcadeMenu.classList.add('hidden');
        practiceMenu.classList.add('hidden');
        mainMenu.classList.remove('hidden');
    };
});

document.querySelectorAll('.btn-mode').forEach(function(btn) {
    btn.onclick = function() {
        gameMode = 'arcade';
        difficulty = btn.getAttribute('data-mode');
        startGame();
    };
});

// Settings Práctica
document.getElementById('p-colors-up').onclick = function() {
    if (practiceSettings.colors < 10) practiceSettings.colors++;
    document.getElementById('val-p-colors').innerText = practiceSettings.colors;
};
document.getElementById('p-colors-down').onclick = function() {
    if (practiceSettings.colors > 1) practiceSettings.colors--;
    document.getElementById('val-p-colors').innerText = practiceSettings.colors;
};

document.getElementById('p-speed-up').onclick = function() {
    if (practiceSettings.speedMult < 5) practiceSettings.speedMult += 0.5;
    document.getElementById('val-p-speed').innerText = practiceSettings.speedMult + 'X';
};
document.getElementById('p-speed-down').onclick = function() {
    if (practiceSettings.speedMult > 1) practiceSettings.speedMult -= 0.5;
    document.getElementById('val-p-speed').innerText = practiceSettings.speedMult + 'X';
};

var feverOptions = ['NORMAL', 'FRECUENTE', 'MUY FRECUENTE'];
document.getElementById('p-fever-up').onclick = function() {
    var idx = feverOptions.indexOf(practiceSettings.feverFreq);
    if (idx < feverOptions.length - 1) practiceSettings.feverFreq = feverOptions[idx + 1];
    document.getElementById('val-p-fever').innerText = practiceSettings.feverFreq;
};
document.getElementById('p-fever-down').onclick = function() {
    var idx = feverOptions.indexOf(practiceSettings.feverFreq);
    if (idx > 0) practiceSettings.feverFreq = feverOptions[idx - 1];
    document.getElementById('val-p-fever').innerText = practiceSettings.feverFreq;
};

document.getElementById('p-wave-toggle').onclick = function() {
    practiceSettings.waveEnabled = !practiceSettings.waveEnabled;
    document.getElementById('val-p-wave').innerText = practiceSettings.waveEnabled ? 'ON' : 'OFF';
};

document.getElementById('btn-practice-start').onclick = function() {
    gameMode = 'practice';
    startGame();
};

btnRestart.onclick = startGame;

pauseMask.onclick = function() {
    togglePause();
};

btnLeft.onclick = function() { rotate(-1); };
btnRight.onclick = function() { rotate(1); };
btnDrop.onclick = function() { quickDrop(); };

// --- GESTIÓN DE TECLADO SIN REINICIOS DE AUDIO ---
window.addEventListener('keydown', function(e) {
    if (!running && isGameOver && (e.key === 'Enter' || e.key === ' ')) {
        e.preventDefault();
        startGame();
        return;
    }

    if (!running) return;

    if (e.key === 'p' || e.key === 'P' || e.key === 'Escape') {
        e.preventDefault();
        togglePause();
        return;
    }

    if (isPaused || isGameOver) return;

    if (e.key === 'ArrowLeft' || e.key === 'a' || e.key === 'A') {
        e.preventDefault();
        rotate(-1);
    } else if (e.key === 'ArrowRight' || e.key === 'd' || e.key === 'D') {
        e.preventDefault();
        rotate(1);
    } else if (e.key === 'ArrowDown' || e.key === 's' || e.key === 'S' || e.key === ' ' || e.code === 'Space') {
        e.preventDefault();
        quickDrop();
    }
});

initGrid();
loop();
