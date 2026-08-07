const { spawn } = require('child_process');
const fs = require('fs');
const http = require('http');
const path = require('path');
const { chromium } = require('playwright-core');

const REPO_ROOT = path.join(__dirname, '..');
const PORT = 3154;
const BASE_URL = `http://127.0.0.1:${PORT}`;

const sleep = ms => new Promise(resolve => setTimeout(resolve, ms));

async function waitForHealth() {
  for (let attempt = 0; attempt < 50; attempt++) {
    const healthy = await new Promise(resolve => {
      http.get(`${BASE_URL}/health`, response => {
        response.resume();
        resolve(response.statusCode === 200);
      }).on('error', () => resolve(false));
    });
    if (healthy) return;
    await sleep(200);
  }
  throw new Error('game server unavailable');
}

function chromiumBinary() {
  const candidates = process.platform === 'win32'
    ? [
        'C:\\Program Files\\Google\\Chrome\\Application\\chrome.exe',
        'C:\\Program Files (x86)\\Microsoft\\Edge\\Application\\msedge.exe',
        'C:\\Program Files\\Microsoft\\Edge\\Application\\msedge.exe'
      ]
    : [];
  return candidates.find(candidate => fs.existsSync(candidate));
}

async function main() {
  const executablePath = chromiumBinary();
  if (!executablePath) {
    console.log('OK parcours navigateur Gomoku IA ignoré (navigateur absent)');
    return;
  }

  const server = spawn('node', ['server.js'], {
    cwd: REPO_ROOT,
    env: {
      ...process.env,
      PORT: String(PORT),
      NODE_ENV: 'test',
      JWT_SECRET: 'test-only-secret-with-more-than-32-characters',
      ALLOWED_ORIGIN: BASE_URL
    },
    stdio: ['ignore', 'pipe', 'pipe']
  });
  server.stderr.on('data', data => process.stderr.write(String(data)));

  let browser;
  try {
    await waitForHealth();
    browser = await chromium.launch({ executablePath });
    const page = await browser.newPage({ viewport: { width: 390, height: 844 } });
    const errors = [];
    page.on('pageerror', error => errors.push(error.message));
    await page.goto(`${BASE_URL}/gomoku-ai?difficulty=medium&name=Test`);
    await page.waitForFunction(() => Array.isArray(window.board) && window.board.length === 225);

    const targets = [[0, 0], [0, 14], [7, 7], [14, 0], [14, 14]];
    const mapped = await page.evaluate(targetCells => targetCells.map(([row, col]) => {
      const canvas = document.getElementById('board');
      const rect = canvas.getBoundingClientRect();
      const point = {
        clientX: rect.left + ORIGIN + col * CELL + CELL / 2,
        clientY: rect.top + ORIGIN + row * CELL + CELL / 2
      };
      const cell = pointerCell(point);
      return { expected: [row, col], actual: cell ? [cell.r, cell.c] : null };
    }), targets);
    if (mapped.some(item => !item.actual || item.actual[0] !== item.expected[0] || item.actual[1] !== item.expected[1])) {
      throw new Error(`mapping de cases invalide: ${JSON.stringify(mapped)}`);
    }

    const scaledMapped = await page.evaluate(targetCells => {
      const canvas = document.getElementById('board');
      canvas.style.width = `${(canvas.width / DPR) * 0.72}px`;
      canvas.style.height = `${(canvas.height / DPR) * 0.72}px`;
      const rect = canvas.getBoundingClientRect();
      const scaleX = rect.width / (canvas.width / DPR);
      const scaleY = rect.height / (canvas.height / DPR);
      return targetCells.map(([row, col]) => {
        const point = {
          clientX: rect.left + (ORIGIN + col * CELL + CELL / 2) * scaleX,
          clientY: rect.top + (ORIGIN + row * CELL + CELL / 2) * scaleY
        };
        const cell = pointerCell(point);
        return { expected: [row, col], actual: cell ? [cell.r, cell.c] : null };
      });
    }, targets);
    if (scaledMapped.some(item => !item.actual || item.actual[0] !== item.expected[0] || item.actual[1] !== item.expected[1])) {
      throw new Error(`mapping redimensionné invalide: ${JSON.stringify(scaledMapped)}`);
    }
    await page.evaluate(() => { calcLayout(); draw(); });

    const center = await page.evaluate(() => {
      const rect = document.getElementById('board').getBoundingClientRect();
      return { x: rect.left + ORIGIN + 7 * CELL + CELL / 2, y: rect.top + ORIGIN + 7 * CELL + CELL / 2 };
    });
    await page.mouse.click(center.x, center.y);
    await sleep(70);
    const duringAnimation = await page.evaluate(() => ({
      humanPlaced: board[7 * SIZE + 7] === HUMAN,
      animationActive: !!stoneAnimations[7 * SIZE + 7]
    }));
    if (!duringAnimation.humanPlaced || !duringAnimation.animationActive) {
      throw new Error(`animation humaine absente: ${JSON.stringify(duringAnimation)}`);
    }

    await sleep(680);
    const beforeAiTurn = await page.evaluate(() => ({
      human: board.filter(value => value === HUMAN).length,
      ai: board.filter(value => value === AI).length,
      humanAnimationFinished: !stoneAnimations[7 * SIZE + 7]
    }));
    if (beforeAiTurn.human !== 1 || beforeAiTurn.ai !== 0 || !beforeAiTurn.humanAnimationFinished) {
      throw new Error(`l'IA a joué avant la fin du tour humain: ${JSON.stringify(beforeAiTurn)}`);
    }

    await page.waitForFunction(() => board.filter(Boolean).length >= 2, null, { timeout: 3000 });
    await page.waitForFunction(() => Object.keys(stoneAnimations).length === 0, null, { timeout: 3000 });
    const finalState = await page.evaluate(() => ({
      stones: board.filter(Boolean).length,
      human: board.filter(value => value === HUMAN).length,
      ai: board.filter(value => value === AI).length,
      animationsFinished: Object.keys(stoneAnimations).length === 0
    }));
    if (finalState.human < 1 || finalState.ai < 1 || !finalState.animationsFinished) {
      throw new Error(`l'IA n'a pas répondu: ${JSON.stringify(finalState)}`);
    }
    if (errors.length) throw new Error(`exceptions navigateur: ${errors.join(' | ')}`);

    console.log('  OK les cases touchées correspondent exactement aux cases jouées, même après redimensionnement');
    console.log('  OK le X humain démarre avec son animation progressive');
    console.log('  OK l’IA attend la fin complète du X avant de jouer');
    console.log('  OK l’IA répond, dessine son O et termine les deux animations');
    console.log('  OK aucune exception JavaScript dans le mode IA');
    console.log('OK parcours navigateur Gomoku IA passé');
  } finally {
    if (browser) await browser.close().catch(() => undefined);
    server.kill('SIGKILL');
  }
}

main().catch(error => {
  console.error(error);
  process.exit(1);
});
