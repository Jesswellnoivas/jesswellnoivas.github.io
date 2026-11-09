/*
 * Jesswell – digitalização de documentos no telemóvel (sem bibliotecas, sem servidor).
 * Usado pela câmara (camara/index.html) e pela app da equipa (fotos da galeria e da câmara do telemóvel).
 *
 *  - qualidade: nitidez (variância do Laplaciano) e luz, só na zona do papel;
 *  - papel: deteção pelo contraste com o fundo (Otsu + maior mancha clara) e 4 cantos;
 *  - endireitar: correção de perspetiva para um retângulo;
 *  - documento: tira sombras/fundo cinzento, reforça o texto (cinzento, pequeno aumento de nitidez);
 *  - tamanho: lado maior até 2000 px, JPEG 85 %;
 *  - rever: ecrã para ver o resultado, ajustar os cantos com o dedo, ligar/desligar o filtro.
 */
(function () {
  'use strict';
  var LADO = 2000, Q = 0.85, MINI = 96;
  var LIMITE_NITIDEZ = 90;   // nitidez relativa ao contraste; abaixo: tremida/desfocada (calibrado: nítidas 230–760, tremidas < 75)
  var LIMITE_LUZ = 60;       // média de cinzento do papel abaixo disto: escura demais (o filtro recupera acima disto)

  function canvas(w, h) { var c = document.createElement('canvas'); c.width = Math.max(1, Math.round(w)); c.height = Math.max(1, Math.round(h)); return c; }
  function reduzir(fonte, lado) {
    var w = fonte.naturalWidth || fonte.videoWidth || fonte.width, h = fonte.naturalHeight || fonte.videoHeight || fonte.height;
    var e = Math.min(1, lado / Math.max(w, h)), c = canvas(w * e, h * e), x = c.getContext('2d');
    x.imageSmoothingQuality = 'high'; x.drawImage(fonte, 0, 0, c.width, c.height); return c;
  }
  function cinzento(c) {
    var d = c.getContext('2d').getImageData(0, 0, c.width, c.height).data, g = new Float32Array(c.width * c.height);
    for (var i = 0, j = 0; i < g.length; i++, j += 4) g[i] = 0.299 * d[j] + 0.587 * d[j + 1] + 0.114 * d[j + 2];
    return g;
  }

  /* ---------- deteção do papel ---------- */
  function otsu(g) {
    var h = new Array(256).fill(0), n = g.length, i;
    for (i = 0; i < n; i++) h[g[i] | 0]++;
    var soma = 0; for (i = 0; i < 256; i++) soma += i * h[i];
    var sB = 0, wB = 0, melhor = 0, t = 128;
    for (i = 0; i < 256; i++) {
      wB += h[i]; if (!wB) continue; var wF = n - wB; if (!wF) break;
      sB += i * h[i]; var mB = sB / wB, mF = (soma - sB) / wF, v = wB * wF * (mB - mF) * (mB - mF);
      if (v > melhor) { melhor = v; t = i; }
    }
    return t;
  }
  function morfo(m, w, h, r, dilatar) {   // erosão/dilatação quadrada (separável)
    var t = new Uint8Array(m.length), o = new Uint8Array(m.length), x, y, k, v;
    for (y = 0; y < h; y++) for (x = 0; x < w; x++) {
      v = dilatar ? 0 : 1;
      for (k = -r; k <= r; k++) { var xx = x + k; var p = (xx < 0 || xx >= w) ? (dilatar ? 0 : 0) : m[y * w + xx]; if (dilatar ? p : !p) { v = dilatar ? 1 : 0; break; } }
      t[y * w + x] = v;
    }
    for (y = 0; y < h; y++) for (x = 0; x < w; x++) {
      v = dilatar ? 0 : 1;
      for (k = -r; k <= r; k++) { var yy = y + k; var q = (yy < 0 || yy >= h) ? 0 : t[yy * w + x]; if (dilatar ? q : !q) { v = dilatar ? 1 : 0; break; } }
      o[y * w + x] = v;
    }
    return o;
  }
  function maiorMancha(m, w, h) {
    var lab = new Int32Array(m.length), pilha = new Int32Array(m.length), melhor = 0, melhorN = 0, id = 0;
    for (var s = 0; s < m.length; s++) {
      if (!m[s] || lab[s]) continue;
      id++; var n = 0, top = 0; pilha[top++] = s; lab[s] = id;
      while (top) {
        var p = pilha[--top]; n++; var x = p % w, y = (p - x) / w;
        if (x > 0 && m[p - 1] && !lab[p - 1]) { lab[p - 1] = id; pilha[top++] = p - 1; }
        if (x < w - 1 && m[p + 1] && !lab[p + 1]) { lab[p + 1] = id; pilha[top++] = p + 1; }
        if (y > 0 && m[p - w] && !lab[p - w]) { lab[p - w] = id; pilha[top++] = p - w; }
        if (y < h - 1 && m[p + w] && !lab[p + w]) { lab[p + w] = id; pilha[top++] = p + w; }
      }
      if (n > melhorN) { melhorN = n; melhor = id; }
    }
    return { lab: lab, id: melhor, n: melhorN };
  }
  function areaQuad(q) {
    var a = 0; for (var i = 0; i < 4; i++) { var p = q[i], r = q[(i + 1) % 4]; a += p[0] * r[1] - r[0] * p[1]; } return Math.abs(a) / 2;
  }
  function convexo(q) {
    var s = 0;
    for (var i = 0; i < 4; i++) {
      var a = q[i], b = q[(i + 1) % 4], c = q[(i + 2) % 4];
      var z = (b[0] - a[0]) * (c[1] - b[1]) - (b[1] - a[1]) * (c[0] - b[0]);
      if (!z) return false; if (!s) s = Math.sign(z); else if (Math.sign(z) !== s) return false;
    }
    return true;
  }
  // Devolve 4 cantos [sup-esq, sup-dir, inf-dir, inf-esq] em coordenadas da fonte, ou null
  function detetarPapel(fonte) {
    var c = reduzir(fonte, 480), w = c.width, h = c.height, g = cinzento(c), n = w * h, i;
    var t = otsu(g), m = new Uint8Array(n), claros = 0;
    for (i = 0; i < n; i++) if (g[i] > t) { m[i] = 1; claros++; }
    if (claros / n > 0.92 || claros / n < 0.06) return null;            // tudo papel ou nada de papel
    var r = Math.max(1, Math.round(Math.max(w, h) / 160));
    m = morfo(morfo(m, w, h, r, false), w, h, r, true);                     // abertura: separa o papel de reflexos
    var mm = maiorMancha(m, w, h);
    if (mm.n < n * 0.12) return null;
    var tl, tr, br, bl, sMin = 1e9, sMax = -1e9, dMin = 1e9, dMax = -1e9;
    for (i = 0; i < n; i++) {
      if (mm.lab[i] !== mm.id) continue;
      var x = i % w, y = (i - x) / w, s = x + y, d = x - y;
      if (s < sMin) { sMin = s; tl = [x, y]; } if (s > sMax) { sMax = s; br = [x, y]; }
      if (d > dMax) { dMax = d; tr = [x, y]; } if (d < dMin) { dMin = d; bl = [x, y]; }
    }
    var q = [tl, tr, br, bl];
    if (!convexo(q)) return null;
    var a = areaQuad(q);
    if (a < n * 0.12 || mm.n / a < 0.8) return null;                       // pouco retangular
    if (a > n * 0.97) return null;                                          // já é só papel
    var e = (fonte.naturalWidth || fonte.videoWidth || fonte.width) / w;
    return q.map(function (p) { return [(p[0] + 0.5) * e, (p[1] + 0.5) * e]; });
  }

  /* ---------- qualidade ---------- */
  function qualidade(fonte, cantos) {
    var c = reduzir(fonte, 900), w = c.width, h = c.height, g = cinzento(c);
    var e = w / (fonte.naturalWidth || fonte.videoWidth || fonte.width);
    var x0 = 1, y0 = 1, x1 = w - 2, y1 = h - 2;
    if (cantos) {   // só dentro do papel (com margem)
      var xs = cantos.map(function (p) { return p[0] * e; }), ys = cantos.map(function (p) { return p[1] * e; });
      x0 = Math.max(1, Math.round(Math.max(xs[0], xs[3]) + 4)); x1 = Math.min(w - 2, Math.round(Math.min(xs[1], xs[2]) - 4));
      y0 = Math.max(1, Math.round(Math.max(ys[0], ys[1]) + 4)); y1 = Math.min(h - 2, Math.round(Math.min(ys[2], ys[3]) - 4));
      if (x1 - x0 < 40 || y1 - y0 < 40) { x0 = 1; y0 = 1; x1 = w - 2; y1 = h - 2; }
    }
    var s = 0, s2 = 0, k = 0, luz = 0, luz2 = 0;
    for (var y = y0; y <= y1; y++) for (var x = x0; x <= x1; x++) {
      var p = y * w + x, l = g[p - 1] + g[p + 1] + g[p - w] + g[p + w] - 4 * g[p];
      s += l; s2 += l * l; luz += g[p]; luz2 += g[p] * g[p]; k++;
    }
    var media = s / k, vl = s2 / k - media * media, ml = luz / k, vg = Math.max(1, luz2 / k - ml * ml);
    // nitidez relativa ao contraste (uma foto escura mas nítida não é tremida)
    return { nitidez: 100 * vl / vg, bruta: vl, luz: ml };
  }

  /* ---------- endireitar (perspetiva) ---------- */
  function homografia(de, para) {   // resolve H (8 incógnitas) tal que para = H·de
    var A = [], b = [];
    for (var i = 0; i < 4; i++) {
      var x = de[i][0], y = de[i][1], u = para[i][0], v = para[i][1];
      A.push([x, y, 1, 0, 0, 0, -u * x, -u * y]); b.push(u);
      A.push([0, 0, 0, x, y, 1, -v * x, -v * y]); b.push(v);
    }
    for (var c = 0; c < 8; c++) {
      var piv = c; for (var r = c + 1; r < 8; r++) if (Math.abs(A[r][c]) > Math.abs(A[piv][c])) piv = r;
      var tA = A[c]; A[c] = A[piv]; A[piv] = tA; var tb = b[c]; b[c] = b[piv]; b[piv] = tb;
      for (r = 0; r < 8; r++) {
        if (r === c) continue; var f = A[r][c] / A[c][c];
        for (var k = c; k < 8; k++) A[r][k] -= f * A[c][k]; b[r] -= f * b[c];
      }
    }
    return b.map(function (v, i) { return v / A[i][i]; });
  }
  function dist(a, b) { return Math.hypot(a[0] - b[0], a[1] - b[1]); }
  function endireitar(fonte, q, lado) {
    var W = Math.max(dist(q[0], q[1]), dist(q[3], q[2])), H = Math.max(dist(q[0], q[3]), dist(q[1], q[2]));
    var e = Math.min(1, (lado || LADO) / Math.max(W, H)); W = Math.round(W * e); H = Math.round(H * e);
    var src = fonte instanceof HTMLCanvasElement ? fonte : reduzir(fonte, 1e5);
    var sw = src.width, sh = src.height, sd = src.getContext('2d').getImageData(0, 0, sw, sh).data;
    var out = canvas(W, H), od = out.getContext('2d').createImageData(W, H), o = od.data;
    var m = homografia([[0, 0], [W - 1, 0], [W - 1, H - 1], [0, H - 1]], q);
    for (var y = 0; y < H; y++) for (var x = 0; x < W; x++) {
      var z = m[6] * x + m[7] * y + 1, sx = (m[0] * x + m[1] * y + m[2]) / z, sy = (m[3] * x + m[4] * y + m[5]) / z;
      var x0 = Math.floor(sx), y0 = Math.floor(sy), fx = sx - x0, fy = sy - y0, j = (y * W + x) * 4;
      if (x0 < 0 || y0 < 0 || x0 >= sw - 1 || y0 >= sh - 1) { o[j] = o[j + 1] = o[j + 2] = 255; o[j + 3] = 255; continue; }
      var a = (y0 * sw + x0) * 4, b2 = a + 4, c2 = a + sw * 4, d2 = c2 + 4;
      for (var ch = 0; ch < 3; ch++)
        o[j + ch] = (sd[a + ch] * (1 - fx) + sd[b2 + ch] * fx) * (1 - fy) + (sd[c2 + ch] * (1 - fx) + sd[d2 + ch] * fx) * fy;
      o[j + 3] = 255;
    }
    out.getContext('2d').putImageData(od, 0, 0);
    return out;
  }

  /* ---------- filtro documento ---------- */
  function documento(c) {
    var w = c.width, h = c.height, x = c.getContext('2d'), id = x.getImageData(0, 0, w, h), d = id.data, n = w * h, i;
    var g = new Float32Array(n);
    for (i = 0; i < n; i++) g[i] = 0.299 * d[i * 4] + 0.587 * d[i * 4 + 1] + 0.114 * d[i * 4 + 2];
    // fundo: imagem pequena (1/24) com o máximo local, suavizada e ampliada → tira sombras e papel cinzento
    var f = 24, bw = Math.max(2, Math.ceil(w / f)), bh = Math.max(2, Math.ceil(h / f)), bg = new Float32Array(bw * bh);
    for (var by = 0; by < bh; by++) for (var bx = 0; bx < bw; bx++) {
      var mx = 0, v = [];
      for (var yy = by * f; yy < Math.min(h, by * f + f); yy += 2) for (var xx = bx * f; xx < Math.min(w, bx * f + f); xx += 2) v.push(g[yy * w + xx]);
      v.sort(function (a, b) { return a - b; }); mx = v[Math.floor(v.length * 0.9)] || 255;   // percentil 90 = cor do papel
      bg[by * bw + bx] = mx;
    }
    var bg2 = new Float32Array(bg.length);   // suaviza 3×3
    for (by = 0; by < bh; by++) for (bx = 0; bx < bw; bx++) {
      var s = 0, k = 0;
      for (var oy = -1; oy <= 1; oy++) for (var ox = -1; ox <= 1; ox++) { var X = bx + ox, Y = by + oy; if (X >= 0 && Y >= 0 && X < bw && Y < bh) { s += bg[Y * bw + X]; k++; } }
      bg2[by * bw + bx] = s / k;
    }
    var out = new Float32Array(n);
    for (var y = 0; y < h; y++) {
      var fy = Math.min(bh - 1.001, Math.max(0, y / f - 0.5)), y0 = Math.floor(fy), ty = fy - y0;
      for (var x2 = 0; x2 < w; x2++) {
        var fx = Math.min(bw - 1.001, Math.max(0, x2 / f - 0.5)), x0 = Math.floor(fx), tx = fx - x0;
        var b = (bg2[y0 * bw + x0] * (1 - tx) + bg2[y0 * bw + x0 + 1] * tx) * (1 - ty) + (bg2[(y0 + 1) * bw + x0] * (1 - tx) + bg2[(y0 + 1) * bw + x0 + 1] * tx) * ty;
        // relação com a cor do papel (1 = papel); curva que escurece o texto fraco sem o apagar
        var p = y * w + x2, rel = g[p] / Math.max(40, b);
        rel = rel >= 0.96 ? 1 : Math.pow(rel / 0.96, 2.6);
        out[p] = rel * 255;
      }
    }
    // nitidez ligeira (máscara de desfocagem 3×3)
    for (y = 1; y < h - 1; y++) for (x2 = 1; x2 < w - 1; x2++) {
      p = y * w + x2;
      var mm = (out[p - 1] + out[p + 1] + out[p - w] + out[p + w] + 4 * out[p]) / 8;
      v = out[p] + 0.6 * (out[p] - mm); v = v < 0 ? 0 : v > 255 ? 255 : v;
      d[p * 4] = d[p * 4 + 1] = d[p * 4 + 2] = v; d[p * 4 + 3] = 255;
    }
    x.putImageData(id, 0, 0);
    return c;
  }

  /* ---------- tudo junto ---------- */
  function avisosDe(qa) {
    var a = [];
    if (qa.nitidez < LIMITE_NITIDEZ) a.push('Foto tremida ou desfocada — tire outra');
    if (qa.luz < LIMITE_LUZ) a.push('Foto escura — tire outra com mais luz');
    return a;
  }
  // fonte: Image, ImageBitmap, canvas ou vídeo. Devolve { dados, thumb, avisos, recortada, cantos, filtro, base }
  function processar(fonte, opcoes) {
    opcoes = opcoes || {};
    var base = reduzir(fonte, 2600);                        // guarda-se para rever/ajustar depois
    var cantos = opcoes.cantos === undefined ? detetarPapel(base) : opcoes.cantos;
    var qa = qualidade(base, cantos);
    var filtro = opcoes.filtro === undefined ? !!cantos : opcoes.filtro;
    var c = cantos ? endireitar(base, cantos, LADO) : reduzir(base, LADO);
    if (filtro) documento(c);
    return { dados: c.toDataURL('image/jpeg', Q).split(',')[1], thumb: reduzir(c, MINI).toDataURL('image/jpeg', 0.7),
      avisos: avisosDe(qa), recortada: !!cantos, cantos: cantos, filtro: filtro, base: base, qualidade: qa };
  }
  function abrirFicheiro(f) {
    return new Promise(function (ok, falha) {
      var url = URL.createObjectURL(f), img = new Image();
      img.onload = function () { URL.revokeObjectURL(url); ok(img); };
      img.onerror = function () { URL.revokeObjectURL(url); falha(new Error('Não foi possível abrir a foto "' + f.name + '".')); };
      img.src = url;
    });
  }

  /* ---------- rever: ver o resultado, ajustar cantos, filtro ---------- */
  var CSS = '#jws{position:fixed;inset:0;z-index:99999;background:#111;color:#fff;display:flex;flex-direction:column;font-family:-apple-system,Roboto,Arial,sans-serif}' +
    '#jws .zona{flex:1;position:relative;overflow:hidden;touch-action:none}#jws canvas{position:absolute;left:0;top:0}' +
    '#jws .barra{display:flex;gap:8px;padding:10px 12px 22px;flex-wrap:wrap;justify-content:center;background:#000}' +
    '#jws button{padding:11px 14px;border-radius:10px;border:none;font-size:15px;background:#333;color:#fff}#jws button.ok{background:#356853;font-weight:600}' +
    '#jws .aviso{padding:10px 14px;background:#7a1f1f;font-size:14px;text-align:center}#jws .dica{padding:8px 14px;font-size:13px;opacity:.8;text-align:center}';
  // Troca a imagem de trabalho (canvas grande) por um JPEG, para não encher a memória com muitas fotos
  function compactar(item) {
    if (item && item.base && !item.baseUrl) { item.baseUrl = item.base.toDataURL('image/jpeg', 0.9); }
    if (item) delete item.base;
    return item;
  }
  function carregarBase(item) {
    if (item.base) return Promise.resolve(item.base);
    return new Promise(function (ok, falha) {
      var img = new Image();
      img.onload = function () { var c = reduzir(img, 1e5); ok(c); };
      img.onerror = falha; img.src = item.baseUrl;
    });
  }
  function rever(item) {
    if (!item || (!item.base && !item.baseUrl)) return Promise.resolve(null);
    return carregarBase(item).then(function (base) {
      return reverCom(item, base).then(function (r) {
        if (r && r !== 'apagar') { delete r.base; r.baseUrl = item.baseUrl || base.toDataURL('image/jpeg', 0.9); }
        return r;
      });
    });
  }
  function reverCom(item, base) {
    item = Object.assign({}, item, { base: base });
    return new Promise(function (resolve) {
      if (!document.getElementById('jws-css')) { var st = document.createElement('style'); st.id = 'jws-css'; st.textContent = CSS; document.head.appendChild(st); }
      var el = document.createElement('div'); el.id = 'jws'; document.body.appendChild(el);
      var estado = { modo: 'ver', cantos: item.cantos ? item.cantos.map(function (p) { return p.slice(); }) : null, filtro: item.filtro };
      var atual = item;
      function fechar(r) { el.remove(); resolve(r); }
      function ecraVer() {
        estado.modo = 'ver';
        el.innerHTML = (atual.avisos && atual.avisos.length ? '<div class="aviso">' + atual.avisos.join('<br>') + '</div>' : '') +
          '<div class="zona"><canvas></canvas></div><div class="barra">' +
          '<button data-a="apagar">Apagar</button><button data-a="cantos">Ajustar cantos</button>' +
          '<button data-a="filtro">' + (estado.filtro ? 'Cores originais' : 'Modo documento') + '</button>' +
          '<button class="ok" data-a="ok">OK</button></div>';
        var img = new Image();
        img.onload = function () {
          var z = el.querySelector('.zona'), cv = el.querySelector('canvas'), e = Math.min(z.clientWidth / img.width, z.clientHeight / img.height);
          cv.width = img.width * e; cv.height = img.height * e; cv.style.left = (z.clientWidth - cv.width) / 2 + 'px'; cv.style.top = (z.clientHeight - cv.height) / 2 + 'px';
          cv.getContext('2d').drawImage(img, 0, 0, cv.width, cv.height);
        };
        img.src = 'data:image/jpeg;base64,' + atual.dados;
      }
      function refazer() {
        var n = processar(item.base, { cantos: estado.cantos, filtro: estado.filtro });
        n.avisos = item.avisos; atual = n; ecraVer();
      }
      function ecraCantos() {
        estado.modo = 'cantos';
        var b = item.base, W = b.width, H = b.height;
        var q = estado.cantos || [[W * 0.08, H * 0.08], [W * 0.92, H * 0.08], [W * 0.92, H * 0.92], [W * 0.08, H * 0.92]];
        el.innerHTML = '<div class="dica">Arraste os 4 cantos para os cantos da fatura</div><div class="zona"><canvas></canvas></div><div class="barra">' +
          '<button data-a="sem">Usar foto inteira</button><button data-a="voltar">Cancelar</button><button class="ok" data-a="aplicar">Aplicar</button></div>';
        var z = el.querySelector('.zona'), cv = el.querySelector('canvas'), e = Math.min(z.clientWidth / W, z.clientHeight / H);
        cv.width = W * e; cv.height = H * e; var ox = (z.clientWidth - cv.width) / 2, oy = (z.clientHeight - cv.height) / 2;
        cv.style.left = ox + 'px'; cv.style.top = oy + 'px';
        var ctx = cv.getContext('2d'), arr = -1;
        function des() {
          ctx.drawImage(b, 0, 0, cv.width, cv.height);
          ctx.strokeStyle = '#4ade80'; ctx.lineWidth = 3; ctx.beginPath();
          q.forEach(function (p, i) { var X = p[0] * e, Y = p[1] * e; if (i) ctx.lineTo(X, Y); else ctx.moveTo(X, Y); }); ctx.closePath(); ctx.stroke();
          q.forEach(function (p) { ctx.beginPath(); ctx.arc(p[0] * e, p[1] * e, 14, 0, 7); ctx.fillStyle = 'rgba(74,222,128,.35)'; ctx.fill(); ctx.stroke(); });
        }
        function pos(ev) { var r = cv.getBoundingClientRect(); return [(ev.clientX - r.left) / e, (ev.clientY - r.top) / e]; }
        z.addEventListener('pointerdown', function (ev) {
          var p = pos(ev), best = 1e9; arr = -1;
          q.forEach(function (c, i) { var d = Math.hypot(c[0] - p[0], c[1] - p[1]); if (d < best) { best = d; arr = i; } });
          if (best * e > 60) arr = -1; else z.setPointerCapture(ev.pointerId);
        });
        z.addEventListener('pointermove', function (ev) {
          if (arr < 0) return; var p = pos(ev);
          q[arr] = [Math.max(0, Math.min(W, p[0])), Math.max(0, Math.min(H, p[1]))]; des();
        });
        z.addEventListener('pointerup', function () { arr = -1; });
        des();
        estado.tmp = q;
      }
      el.addEventListener('click', function (ev) {
        var a = ev.target && ev.target.getAttribute && ev.target.getAttribute('data-a'); if (!a) return;
        if (a === 'ok') fechar(atual);
        else if (a === 'apagar') fechar('apagar');
        else if (a === 'filtro') { estado.filtro = !estado.filtro; refazer(); }
        else if (a === 'cantos') ecraCantos();
        else if (a === 'voltar') ecraVer();
        else if (a === 'sem') { estado.cantos = null; refazer(); }
        else if (a === 'aplicar') { if (convexo(estado.tmp)) { estado.cantos = estado.tmp; if (!item.cantos && estado.filtro === false) estado.filtro = true; refazer(); } }
      });
      ecraVer();
    });
  }

  window.JWScan = {
    versao: 1, processar: processar, abrirFicheiro: abrirFicheiro, rever: rever, compactar: compactar,
    detetarPapel: detetarPapel, qualidade: qualidade, endireitar: endireitar, documento: documento,
    limites: { nitidez: LIMITE_NITIDEZ, luz: LIMITE_LUZ }
  };
})();
