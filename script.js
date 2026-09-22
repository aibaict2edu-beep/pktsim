/* =====================================================================
   PacketPath — TCP/IP & ルーティング動作シミュレータ
   index.html / style.css と対で動作する単一スクリプト。
   ===================================================================== */

(function () {
  'use strict';

  /* ------------------------------------------------------------------ *
   * 0. 汎用ユーティリティ
   * ------------------------------------------------------------------ */

  let idSeq = 1;
  function uid(prefix) { return prefix + '-' + (idSeq++); }

  function randHex(n) {
    let s = '';
    for (let i = 0; i < n; i++) s += Math.floor(Math.random() * 16).toString(16);
    return s;
  }
  function randMac(seedByte) {
    const b = (seedByte !== undefined) ? seedByte.toString(16).padStart(2, '0') : randHex(2);
    return ['02', 'a1', 'c3', b, randHex(2), randHex(2)].join(':');
  }
  function randPort() { return 49152 + Math.floor(Math.random() * 12000); }

  function nowStamp() {
    const d = new Date();
    return d.toTimeString().slice(0, 8);
  }

  function el(tag, cls, text) {
    const e = document.createElement(tag);
    if (cls) e.className = cls;
    if (text !== undefined) e.textContent = text;
    return e;
  }

  function clamp(v, lo, hi) { return Math.max(lo, Math.min(hi, v)); }

  /* ------------------------------------------------------------------ *
   * 1. グラフ／ダイクストラ法
   * ------------------------------------------------------------------ *
   * topology = { nodes: Map(id -> node), links: [link, ...] }
   * node     = { id, type, name, ip, mac, x, y, w, h }
   * link     = { id, a, b, cost, down, routable }
   * ------------------------------------------------------------------ */

  function buildAdjacency(topology) {
    const adj = new Map();
    topology.nodes.forEach((_, id) => adj.set(id, []));
    topology.links.forEach((l) => {
      if (l.down) return;
      const cost = l.cost || 0;
      if (!adj.has(l.a) || !adj.has(l.b)) return;
      adj.get(l.a).push({ to: l.b, cost, link: l });
      adj.get(l.b).push({ to: l.a, cost, link: l });
    });
    return adj;
  }

  function dijkstra(topology, srcId, dstId) {
    const adj = buildAdjacency(topology);
    const dist = new Map();
    const prev = new Map();
    const visited = new Set();
    topology.nodes.forEach((_, id) => dist.set(id, Infinity));
    if (!topology.nodes.has(srcId) || !topology.nodes.has(dstId)) {
      return { reachable: false, path: [], cost: Infinity };
    }
    dist.set(srcId, 0);
    const pq = [[0, srcId]];
    while (pq.length) {
      pq.sort((a, b) => a[0] - b[0]);
      const [d, u] = pq.shift();
      if (visited.has(u)) continue;
      visited.add(u);
      if (u === dstId) break;
      (adj.get(u) || []).forEach((edge) => {
        if (visited.has(edge.to)) return;
        const nd = d + edge.cost;
        if (nd < dist.get(edge.to)) {
          dist.set(edge.to, nd);
          prev.set(edge.to, u);
          pq.push([nd, edge.to]);
        }
      });
    }
    if (dist.get(dstId) === Infinity) return { reachable: false, path: [], cost: Infinity };
    const path = [dstId];
    let cur = dstId;
    while (cur !== srcId) {
      cur = prev.get(cur);
      if (cur === undefined) return { reachable: false, path: [], cost: Infinity };
      path.unshift(cur);
    }
    return { reachable: true, path, cost: dist.get(dstId) };
  }

  function findLinkBetween(topology, aId, bId) {
    return topology.links.find(
      (l) => (l.a === aId && l.b === bId) || (l.a === bId && l.b === aId)
    );
  }

  function firstL3Hop(topology, path) {
    for (let i = 1; i < path.length - 1; i++) {
      const n = topology.nodes.get(path[i]);
      if (n && n.type === 'router') return n;
    }
    return topology.nodes.get(path[path.length - 1]);
  }

  /* ------------------------------------------------------------------ *
   * 2. 固定トポロジの構築
   * ------------------------------------------------------------------ */

  const PRESET_COSTS = {
    'rt-s_rt-a': 3, 'rt-a_rt-r': 2, // ルートA 合計 5
    'rt-s_rt-b': 4, 'rt-b_rt-r': 4, // ルートB 合計 8
    'rt-s_rt-c': 6, 'rt-c_rt-r': 1  // ルートC 合計 7
  };

  function makeFixedTopology() {
    const nodes = new Map();
    const links = [];

    function addNode(id, type, name, ip, mac, x, y) {
      nodes.set(id, { id, type, name, ip: ip || null, mac: mac || null, x, y });
    }
    function addLink(id, a, b, cost, routable) {
      links.push({ id, a, b, cost: cost || 0, down: false, routable: !!routable });
    }

    // 送信側 PC
    addNode('pc-s1', 'pc', 'PC-S1', '192.168.1.11', randMac(0x11), 70, 120);
    addNode('pc-s2', 'pc', 'PC-S2', '192.168.1.12', randMac(0x12), 70, 280);
    addNode('pc-s3', 'pc', 'PC-S3', '192.168.1.13', randMac(0x13), 70, 440);
    addNode('sw-s', 'switch', 'SW-S', null, randMac(0x20), 230, 280);
    addNode('rt-s', 'router', 'RT-S', '192.168.1.1', randMac(0x30), 380, 280);

    // 中継ルーター（3経路・双方に直結）
    addNode('rt-a', 'router', 'RT-A', null, randMac(0x41), 590, 110);
    addNode('rt-b', 'router', 'RT-B', null, randMac(0x42), 590, 280);
    addNode('rt-c', 'router', 'RT-C', null, randMac(0x43), 590, 450);

    // 受信側
    addNode('rt-r', 'router', 'RT-R', '192.168.2.1', randMac(0x50), 800, 280);
    addNode('sw-r', 'switch', 'SW-R', null, randMac(0x60), 950, 280);
    addNode('pc-r1', 'pc', 'PC-R1', '192.168.2.11', randMac(0x71), 1060, 120);
    addNode('pc-r2', 'pc', 'PC-R2', '192.168.2.12', randMac(0x72), 1060, 280);
    addNode('pc-r3', 'pc', 'PC-R3', '192.168.2.13', randMac(0x73), 1060, 440);

    addLink(uid('l'), 'pc-s1', 'sw-s', 0, false);
    addLink(uid('l'), 'pc-s2', 'sw-s', 0, false);
    addLink(uid('l'), 'pc-s3', 'sw-s', 0, false);
    addLink(uid('l'), 'sw-s', 'rt-s', 0, false);

    addLink('rt-s_rt-a', 'rt-s', 'rt-a', PRESET_COSTS['rt-s_rt-a'], true);
    addLink('rt-a_rt-r', 'rt-a', 'rt-r', PRESET_COSTS['rt-a_rt-r'], true);
    addLink('rt-s_rt-b', 'rt-s', 'rt-b', PRESET_COSTS['rt-s_rt-b'], true);
    addLink('rt-b_rt-r', 'rt-b', 'rt-r', PRESET_COSTS['rt-b_rt-r'], true);
    addLink('rt-s_rt-c', 'rt-s', 'rt-c', PRESET_COSTS['rt-s_rt-c'], true);
    addLink('rt-c_rt-r', 'rt-c', 'rt-r', PRESET_COSTS['rt-c_rt-r'], true);

    addLink(uid('l'), 'rt-r', 'sw-r', 0, false);
    addLink(uid('l'), 'sw-r', 'pc-r1', 0, false);
    addLink(uid('l'), 'sw-r', 'pc-r2', 0, false);
    addLink(uid('l'), 'sw-r', 'pc-r3', 0, false);

    return { nodes, links };
  }

  const ROUTE_DEFS = [
    { key: 'A', label: 'ルートA', mid: 'rt-a', seg: ['rt-s_rt-a', 'rt-a_rt-r'] },
    { key: 'B', label: 'ルートB', mid: 'rt-b', seg: ['rt-s_rt-b', 'rt-b_rt-r'] },
    { key: 'C', label: 'ルートC', mid: 'rt-c', seg: ['rt-s_rt-c', 'rt-c_rt-r'] }
  ];

  function getRouteCosts(topology) {
    return ROUTE_DEFS.map((rd) => {
      const l1 = topology.links.find((l) => l.id === rd.seg[0]);
      const l2 = topology.links.find((l) => l.id === rd.seg[1]);
      const down = (l1 && l1.down) || (l2 && l2.down);
      const cost = down ? Infinity : (l1.cost + l2.cost);
      return { ...rd, cost, down, l1, l2 };
    });
  }

  /* ------------------------------------------------------------------ *
   * 3. SVG 描画
   * ------------------------------------------------------------------ */

  const SVG_NS = 'http://www.w3.org/2000/svg';

  function nodeSize(type) {
    if (type === 'pc') return { w: 58, h: 42 };
    if (type === 'switch') return { w: 76, h: 38 };
    return { w: 66, h: 50 }; // router
  }

  function nodeIconMarkup(type) {
    if (type === 'pc') {
      return (
        '<rect class="n-icon" x="-15" y="-15" width="30" height="19" rx="1.5"></rect>' +
        '<line class="n-icon" x1="-5" y1="4" x2="5" y2="4"></line>' +
        '<line class="n-icon" x1="-9" y1="8" x2="9" y2="8"></line>'
      );
    }
    if (type === 'switch') {
      let ports = '';
      for (let i = -3; i <= 3; i++) {
        ports += `<rect class="n-icon" x="${i * 8 - 2}" y="4" width="4" height="4"></rect>`;
      }
      return '<rect class="n-icon" x="-30" y="-8" width="60" height="12" rx="1.5"></rect>' + ports;
    }
    // router
    return (
      '<circle class="n-icon" cx="0" cy="-2" r="10"></circle>' +
      '<path class="n-icon" d="M -10,-2 A 10,10 0 0,1 4,-10" marker-end="url(#arrowhead)"></path>' +
      '<path class="n-icon" d="M 10,-2 A 10,10 0 0,1 -4,6" marker-end="url(#arrowhead)"></path>'
    );
  }

  function shortenedEndpoints(ax, ay, bx, by, pad) {
    const dx = bx - ax, dy = by - ay;
    const dist = Math.hypot(dx, dy) || 1;
    const ux = dx / dist, uy = dy / dist;
    return {
      x1: ax + ux * pad, y1: ay + uy * pad,
      x2: bx - ux * pad, y2: by - uy * pad
    };
  }

  function renderTopology(svgEl, topology, state) {
    state = state || {};
    let html = `<defs>
      <marker id="arrowhead" markerWidth="6" markerHeight="6" refX="5" refY="3" orient="auto">
        <path d="M0,0 L6,3 L0,6 z" fill="var(--text-dim)"></path>
      </marker>
    </defs>`;

    // links first (under nodes)
    topology.links.forEach((l) => {
      const a = topology.nodes.get(l.a), b = topology.nodes.get(l.b);
      if (!a || !b) return;
      const pad = Math.max(nodeSize(a.type).w, nodeSize(a.type).h) / 2 + 6;
      const pts = shortenedEndpoints(a.x, a.y, b.x, b.y, pad);
      const isActive = state.activePathLinkIds && state.activePathLinkIds.has(l.id);
      const clickable = l.routable !== false || state.freeMode;
      let cls = 'link-line';
      if (clickable) cls += ' is-routable';
      if (l.down) cls += ' is-down';
      if (isActive) cls += ' is-active-path';
      html += `<line class="${cls}" data-link-id="${l.id}" x1="${pts.x1}" y1="${pts.y1}" x2="${pts.x2}" y2="${pts.y2}"></line>`;
      html += `<line class="link-hit" data-link-id="${l.id}" style="cursor:${clickable ? 'pointer' : 'default'}" x1="${pts.x1}" y1="${pts.y1}" x2="${pts.x2}" y2="${pts.y2}"></line>`;

      if (l.routable) {
        const mx = (pts.x1 + pts.x2) / 2, my = (pts.y1 + pts.y2) / 2;
        const label = l.down ? 'DOWN' : String(l.cost);
        const bw = l.down ? 40 : 18;
        html += `<rect class="link-cost-bg" x="${mx - bw / 2}" y="${my - 9}" width="${bw}" height="16" rx="3"></rect>`;
        html += `<text class="link-cost${l.down ? ' is-down' : ''}" x="${mx}" y="${my + 3}" text-anchor="middle">${label}</text>`;
      }
    });

    // nodes
    topology.nodes.forEach((n) => {
      const size = nodeSize(n.type);
      const isRouter = n.type === 'router';
      const isSelected = state.selectedNodeId === n.id;
      const isHover = state.hoverNodeId === n.id;
      let boxCls = 'n-box' + (isRouter ? ' is-router' : '') + (isHover ? ' is-hover' : '');
      let groupCls = state.freeMode ? 'free-node' : 'topo-node';
      if (isSelected) groupCls += ' is-selected';
      const title = `${n.name}${n.ip ? '\n' + n.ip : ''}${n.mac ? '\n' + n.mac : ''}`;
      html += `<g class="${groupCls}" data-node-id="${n.id}" transform="translate(${n.x},${n.y})">
        <title>${title}</title>
        <rect class="${boxCls}" x="${-size.w / 2}" y="${-size.h / 2}" width="${size.w}" height="${size.h}" rx="${isRouter ? 10 : 5}"></rect>
        ${nodeIconMarkup(n.type)}
        <text class="n-label" y="${size.h / 2 + 15}">${n.name}</text>
        ${n.ip ? `<text class="n-sub" y="${size.h / 2 + 27}">${n.ip}</text>` : ''}
      </g>`;
    });

    svgEl.innerHTML = html;
  }

  function animatePacket(svgEl, topology, path, opts) {
    opts = opts || {};
    if (!path || path.length < 2) return;
    let d = '';
    path.forEach((id, i) => {
      const n = topology.nodes.get(id);
      if (!n) return;
      d += (i === 0 ? 'M ' : 'L ') + n.x + ' ' + n.y + ' ';
    });
    const dur = Math.max(0.9, (path.length - 1) * 0.7);
    const dot = document.createElementNS(SVG_NS, 'circle');
    dot.setAttribute('r', '6');
    dot.setAttribute('class', 'pkt-dot');
    const motion = document.createElementNS(SVG_NS, 'animateMotion');
    motion.setAttribute('dur', dur + 's');
    motion.setAttribute('path', d.trim());
    motion.setAttribute('fill', 'freeze');
    motion.setAttribute('repeatCount', '1');
    dot.appendChild(motion);
    svgEl.appendChild(dot);
    setTimeout(() => { if (dot.parentNode) dot.parentNode.removeChild(dot); }, dur * 1000 + 150);
    if (typeof opts.onDone === 'function') setTimeout(opts.onDone, dur * 1000);
  }

  /* ------------------------------------------------------------------ *
   * 4. ログ出力
   * ------------------------------------------------------------------ */

  function makeLogger(containerEl) {
    return function log(level, msg, delay) {
      const write = () => {
        const line = el('div', 'log-line lv-' + level);
        const t = el('span', 'log-time', nowStamp());
        const m = el('span', 'log-msg', msg);
        line.appendChild(t);
        line.appendChild(m);
        containerEl.appendChild(line);
        containerEl.scrollTop = containerEl.scrollHeight;
      };
      if (delay) setTimeout(write, delay);
      else write();
    };
  }

  /* ------------------------------------------------------------------ *
   * 5. 送信シミュレーション本体
   * ------------------------------------------------------------------ */

  function simulateSend(topology, srcId, dstId, logFn, svgEl, opts) {
    opts = opts || {};
    const src = topology.nodes.get(srcId);
    const dst = topology.nodes.get(dstId);
    if (!src || !dst) return;

    const result = dijkstra(topology, srcId, dstId);
    let t = 0;
    const STEP = 260;

    logFn('sys', `送信開始: ${src.name} (${src.ip || '—'}) → ${dst.name} (${dst.ip || '—'})`, t); t += STEP;

    if (opts.onRouteComputed) opts.onRouteComputed(result);

    if (!result.reachable) {
      logFn('fail', '到達可能な経路がありません（経路上の全リンクが障害中です）', t);
      if (opts.onFinish) setTimeout(() => opts.onFinish(result), t + 200);
      return;
    }

    const gw = firstL3Hop(topology, result.path);

    logFn('arp', `${src.name}: ARP要求（ブロードキャスト）— ${gw.ip || gw.name} のMACアドレスは？`, t); t += STEP;
    logFn('arp', `${gw.name}: ARP応答 — MACアドレス ${gw.mac} を通知`, t); t += STEP;

    const sport = randPort();
    logFn('tcp', `${src.name} → ${dst.name} : TCP SYN  (sport=${sport}, dport=80, seq=0)`, t); t += STEP;
    logFn('tcp', `${dst.name} → ${src.name} : TCP SYN-ACK (ack=1, seq=0)`, t); t += STEP;
    logFn('tcp', `${src.name} → ${dst.name} : TCP ACK (ack=1) — コネクション確立`, t); t += STEP;

    logFn('tcp', `TCPセグメント生成: sport=${sport} dport=80 flags=PSH,ACK`, t); t += STEP;
    logFn('ip', `IPパケット生成: src=${src.ip || '-'} dst=${dst.ip || '-'} TTL=64 proto=TCP`, t); t += STEP;
    logFn('frame', `イーサネットフレーム生成: src=${src.mac} dst=${gw.mac} (type=0x0800)`, t); t += STEP;

    if (opts.routeLabel) {
      logFn('route', `経路選択: ${opts.routeLabel}（合計コスト ${result.cost}）を採用`, t); t += STEP;
    }

    let ttl = 64;
    for (let i = 1; i < result.path.length - 1; i++) {
      const n = topology.nodes.get(result.path[i]);
      if (n.type === 'router') {
        ttl -= 1;
        const nextNode = topology.nodes.get(result.path[i + 1]);
        const link = findLinkBetween(topology, n.id, nextNode.id);
        const metricNote = link && link.routable ? ` (metric ${link.cost})` : '';
        logFn('route', `${n.name}: 宛先 ${dst.ip || dst.name} への経路検索 → ネクストホップ ${nextNode.name}${metricNote}、TTL=${ttl}`, t); t += STEP;
        logFn('frame', `${n.name}: フレーム再構築 src=${n.mac} dst=${nextNode.mac}`, t); t += STEP;
      } else if (n.type === 'switch') {
        logFn('sys', `${n.name}: MACアドレステーブル参照 → 該当ポートへフォワード`, t); t += STEP;
      }
    }

    logFn('ok', `${dst.name}: フレーム受信 → デカプセル化 → パケット到達（通信成功）`, t); t += STEP;

    animatePacket(svgEl, topology, result.path);

    if (opts.onFinish) setTimeout(() => opts.onFinish(result), t + 200);
  }

  /* ------------------------------------------------------------------ *
   * 6. 固定トポロジ モード
   * ------------------------------------------------------------------ */

  const Fixed = {
    topo: makeFixedTopology(),
    svg: null,
    logEl: null,
    rtMode: 'preset',
    failRate: 15,
    hoverNodeId: null
  };

  function fixedLog(level, msg, delay) {
    makeLogger(Fixed.logEl)(level, msg, delay);
  }

  function fixedRender() {
    renderTopology(Fixed.svg, Fixed.topo, { hoverNodeId: Fixed.hoverNodeId });
    fixedRenderRouteCompare();
    fixedRenderRoutingTable();
  }

  function fixedRenderRouteCompare() {
    const wrap = document.getElementById('route-compare');
    const costs = getRouteCosts(Fixed.topo);
    const best = Math.min(...costs.filter((c) => !c.down).map((c) => c.cost), Infinity);
    wrap.innerHTML = '';
    costs.forEach((c) => {
      const row = el('div', 'route-row');
      if (c.down) row.classList.add('is-unavailable');
      else if (c.cost === best) row.classList.add('is-chosen');
      row.innerHTML = `<span class="route-tag">${c.key}</span>
        <span>RT-S → ${c.mid.toUpperCase()} → RT-R</span>
        <span class="route-cost">${c.down ? '不通' : 'コスト ' + c.cost}</span>`;
      wrap.appendChild(row);
    });
  }

  function fixedRenderRoutingTable() {
    const wrap = document.getElementById('routing-table');
    wrap.innerHTML = '';
    const manual = Fixed.rtMode === 'manual';
    ROUTE_DEFS.forEach((rd) => {
      const box = el('div', 'rt-router');
      const segNames = [
        ['RT-S → ' + rd.key, rd.seg[0]],
        [rd.key + ' → RT-R', rd.seg[1]]
      ];
      let rows = '';
      segNames.forEach(([label, linkId]) => {
        const link = Fixed.topo.links.find((l) => l.id === linkId);
        rows += `<tr>
          <td>${label}</td>
          <td><input type="number" min="1" max="99" value="${link.cost}" data-link-id="${link.id}" class="rt-cost-input" ${manual ? '' : 'disabled'}></td>
          <td><button class="btn btn-mini rt-toggle" data-link-id="${link.id}">${link.down ? '<span class="rt-down">DOWN</span>' : 'UP'}</button></td>
        </tr>`;
      });
      box.innerHTML = `<div class="rt-router-name">中継 ${rd.key}（${rd.mid.toUpperCase()}）</div>
        <table class="rt-tbl">
          <tr><th>区間</th><th>メトリック</th><th>状態</th></tr>
          ${rows}
        </table>`;
      wrap.appendChild(box);
    });

    wrap.querySelectorAll('.rt-cost-input').forEach((inp) => {
      inp.addEventListener('change', () => {
        const link = Fixed.topo.links.find((l) => l.id === inp.dataset.linkId);
        const v = clamp(parseInt(inp.value, 10) || 1, 1, 99);
        link.cost = v;
        fixedRender();
      });
    });
    wrap.querySelectorAll('.rt-toggle').forEach((btn) => {
      btn.addEventListener('click', () => {
        const link = Fixed.topo.links.find((l) => l.id === btn.dataset.linkId);
        link.down = !link.down;
        fixedLog('sys', `${link.id.replace('_', ' → ').toUpperCase()} を${link.down ? '障害（ダウン）状態に設定' : '復旧'}しました`);
        fixedRender();
      });
    });
  }

  function fixedPopulateSelects() {
    const srcSel = document.getElementById('src-pc');
    const dstSel = document.getElementById('dst-pc');
    srcSel.innerHTML = '';
    dstSel.innerHTML = '';
    Fixed.topo.nodes.forEach((n) => {
      if (n.type !== 'pc') return;
      srcSel.appendChild(new Option(`${n.name} (${n.ip})`, n.id));
      dstSel.appendChild(new Option(`${n.name} (${n.ip})`, n.id));
    });
    srcSel.value = 'pc-s1';
    dstSel.value = 'pc-r2';
  }

  function fixedOpenLinkModal(linkId) {
    const link = Fixed.topo.links.find((l) => l.id === linkId);
    if (!link || !link.routable) return;

    if (Fixed.rtMode === 'preset') {
      // プリセットモードではコストは変更不可。UP/DOWNのみ即時切替。
      link.down = !link.down;
      fixedLog('sys', `${link.id.toUpperCase()} を${link.down ? '障害（ダウン）状態に設定' : '復旧'}しました`);
      fixedRender();
      return;
    }

    openCostModal({
      title: 'リンク設定',
      subtitle: `${link.a.toUpperCase()} — ${link.b.toUpperCase()}`,
      initialCost: link.cost,
      costEditable: true,
      initialDown: link.down,
      onSave: (cost, down) => {
        link.cost = cost;
        link.down = down;
        fixedLog('sys', `${link.id.toUpperCase()} を更新しました（コスト=${cost}, 状態=${down ? 'DOWN' : 'UP'}）`);
        fixedRender();
      }
    });
  }

  function fixedMaybeTriggerFailure() {
    if (Math.random() * 100 >= Fixed.failRate) return;
    const upLinks = Fixed.topo.links.filter((l) => l.routable && !l.down);
    if (upLinks.length === 0) return;
    const victim = upLinks[Math.floor(Math.random() * upLinks.length)];
    victim.down = true;
    fixedLog('fail', `【自動障害】${victim.id.toUpperCase()} でリンク障害が発生しました（次回送信から経路に反映されます）`);
    fixedRender();
  }

  function fixedSend() {
    const srcId = document.getElementById('src-pc').value;
    const dstId = document.getElementById('dst-pc').value;
    const statusEl = document.getElementById('send-status');
    if (srcId === dstId) {
      statusEl.textContent = '送信元と宛先が同じです。別のPCを選択してください。';
      return;
    }
    statusEl.textContent = '送信中…';

    const sendOpts = {
      onRouteComputed: (result) => {
        if (result.reachable) {
          const costs = getRouteCosts(Fixed.topo);
          const chosen = costs.find((c) => result.path.includes(c.mid));
          sendOpts.routeLabel = chosen ? `${chosen.label}（RT-S→${chosen.key}→RT-R）` : null;
        }
        // 経路比較パネルは選択結果を強調
        renderRouteCompareWithChoice(result);
      },
      routeLabel: null,
      onFinish: (result) => {
        statusEl.textContent = result.reachable ? '送信完了' : '送信失敗（不通）';
        fixedMaybeTriggerFailure();
      }
    };
    simulateSend(Fixed.topo, srcId, dstId, fixedLog, Fixed.svg, sendOpts);
  }

  function renderRouteCompareWithChoice(result) {
    const wrap = document.getElementById('route-compare');
    const costs = getRouteCosts(Fixed.topo);
    wrap.innerHTML = '';
    costs.forEach((c) => {
      const row = el('div', 'route-row');
      const isChosen = result.reachable && result.path.includes(c.mid);
      if (c.down) row.classList.add('is-unavailable');
      if (isChosen) row.classList.add('is-chosen');
      row.innerHTML = `<span class="route-tag">${c.key}</span>
        <span>RT-S → ${c.mid.toUpperCase()} → RT-R</span>
        <span class="route-cost">${c.down ? '不通' : 'コスト ' + c.cost}</span>`;
      wrap.appendChild(row);
    });

    // ハイライトするリンクをSVGに反映
    const activeIds = new Set();
    if (result.reachable) {
      for (let i = 0; i < result.path.length - 1; i++) {
        const l = findLinkBetween(Fixed.topo, result.path[i], result.path[i + 1]);
        if (l) activeIds.add(l.id);
      }
    }
    renderTopology(Fixed.svg, Fixed.topo, { activePathLinkIds: activeIds, hoverNodeId: Fixed.hoverNodeId });
    setTimeout(() => fixedRender(), 2600);
  }

  function initFixedMode() {
    Fixed.svg = document.getElementById('topo-svg');
    Fixed.logEl = document.getElementById('log');
    fixedPopulateSelects();
    fixedRender();

    Fixed.svg.addEventListener('click', (e) => {
      const linkTarget = e.target.closest('[data-link-id]');
      if (linkTarget) { fixedOpenLinkModal(linkTarget.dataset.linkId); return; }
    });
    Fixed.svg.addEventListener('mousemove', (e) => {
      const nodeTarget = e.target.closest('[data-node-id]');
      const id = nodeTarget ? nodeTarget.dataset.nodeId : null;
      if (id !== Fixed.hoverNodeId) { Fixed.hoverNodeId = id; fixedRender(); }
    });

    document.getElementById('send-btn').addEventListener('click', fixedSend);
    document.getElementById('clear-log').addEventListener('click', () => { Fixed.logEl.innerHTML = ''; });

    document.getElementById('rt-mode').addEventListener('change', (e) => {
      Fixed.rtMode = e.target.value;
      if (Fixed.rtMode === 'preset') {
        Object.keys(PRESET_COSTS).forEach((linkId) => {
          const link = Fixed.topo.links.find((l) => l.id === linkId);
          if (link) link.cost = PRESET_COSTS[linkId];
        });
        fixedLog('sys', 'プリセットのルーティングテーブルを読み込みました');
      } else {
        fixedLog('sys', '手動編集モードに切り替えました（コストを編集できます）');
      }
      fixedRender();
    });

    const failRateInput = document.getElementById('fail-rate');
    const failRateOut = document.getElementById('fail-rate-out');
    failRateInput.addEventListener('input', () => {
      Fixed.failRate = parseInt(failRateInput.value, 10);
      failRateOut.textContent = Fixed.failRate + '%';
    });

    document.getElementById('reset-links').addEventListener('click', () => {
      Fixed.topo.links.forEach((l) => { l.down = false; });
      fixedLog('sys', 'すべてのリンクを復旧しました');
      fixedRender();
    });

    fixedLog('sys', '準備完了。送信元・宛先PCを選び「パケットを送信」を押してください。');
  }

  /* ------------------------------------------------------------------ *
   * 7. コスト編集モーダル（共通）
   * ------------------------------------------------------------------ */

  let modalSaveCb = null;
  function openCostModal(cfg) {
    const backdrop = document.getElementById('cost-modal-backdrop');
    document.getElementById('cost-modal-title').textContent = cfg.title || 'リンク設定';
    document.getElementById('cost-modal-sub').textContent = cfg.subtitle || '';
    const costInput = document.getElementById('cost-input');
    costInput.value = cfg.initialCost != null ? cfg.initialCost : 1;
    costInput.disabled = cfg.costEditable === false;
    document.getElementById('cost-down-check').checked = !!cfg.initialDown;
    modalSaveCb = cfg.onSave;
    backdrop.classList.remove('is-hidden');
  }
  function closeCostModal() {
    document.getElementById('cost-modal-backdrop').classList.add('is-hidden');
    modalSaveCb = null;
  }

  function initModal() {
    document.getElementById('cost-cancel').addEventListener('click', closeCostModal);
    document.getElementById('cost-modal-backdrop').addEventListener('click', (e) => {
      if (e.target.id === 'cost-modal-backdrop') closeCostModal();
    });
    document.getElementById('cost-save').addEventListener('click', () => {
      const cost = clamp(parseInt(document.getElementById('cost-input').value, 10) || 1, 1, 99);
      const down = document.getElementById('cost-down-check').checked;
      if (modalSaveCb) modalSaveCb(cost, down);
      closeCostModal();
    });
  }

  /* ------------------------------------------------------------------ *
   * 8. 自由配置モード
   * ------------------------------------------------------------------ */

  const Free = {
    topo: { nodes: new Map(), links: [] },
    svg: null,
    logEl: null,
    interactionMode: 'move',
    linkFirstPick: null,
    hoverNodeId: null,
    typeCounters: { pc: 0, switch: 0, router: 0 },
    placeCursor: { x: 140, y: 120 },
    dragging: null
  };

  function freeLog(level, msg, delay) { makeLogger(Free.logEl)(level, msg, delay); }

  const FREE_TYPE_LABEL = { pc: 'PC', switch: 'SW', router: 'RT' };

  function freeAddNode(type) {
    Free.typeCounters[type] += 1;
    const n = Free.typeCounters[type];
    const id = uid('f' + type);
    const name = `${FREE_TYPE_LABEL[type]}-${n}`;
    let ip = null, mac = randMac();
    if (type === 'pc' || type === 'router') {
      ip = `10.${type === 'pc' ? 20 : 30}.0.${n}`;
    }
    // カスケード配置（重なり回避の簡易ロジック）
    const cols = 6;
    const idx = Free.topo.nodes.size;
    const x = 140 + (idx % cols) * 160;
    const y = 100 + Math.floor(idx / cols) * 150;
    Free.topo.nodes.set(id, { id, type, name, ip, mac, x, y });
    freeRender();
    freePopulateSelects();
    freeLog('sys', `${name} を追加しました`);
  }

  function freeRender() {
    renderTopology(Free.svg, Free.topo, {
      freeMode: true,
      hoverNodeId: Free.hoverNodeId,
      selectedNodeId: Free.linkFirstPick
    });
  }

  function freePopulateSelects() {
    const srcSel = document.getElementById('free-src-pc');
    const dstSel = document.getElementById('free-dst-pc');
    const curSrc = srcSel.value, curDst = dstSel.value;
    srcSel.innerHTML = '';
    dstSel.innerHTML = '';
    let count = 0;
    Free.topo.nodes.forEach((n) => {
      if (n.type !== 'pc') return;
      count++;
      srcSel.appendChild(new Option(`${n.name} (${n.ip})`, n.id));
      dstSel.appendChild(new Option(`${n.name} (${n.ip})`, n.id));
    });
    if (count === 0) {
      srcSel.appendChild(new Option('PCがありません', ''));
      dstSel.appendChild(new Option('PCがありません', ''));
    } else {
      if ([...Free.topo.nodes.keys()].includes(curSrc)) srcSel.value = curSrc;
      if ([...Free.topo.nodes.keys()].includes(curDst)) dstSel.value = curDst;
    }
  }

  function freeSetMode(mode) {
    Free.interactionMode = mode;
    Free.linkFirstPick = null;
    document.querySelectorAll('#panel-free [data-mode]').forEach((b) => {
      b.classList.toggle('is-active', b.dataset.mode === mode);
    });
    const hint = document.getElementById('free-hint');
    if (mode === 'move') hint.textContent = 'ノードをドラッグして移動できます。リンクをクリックするとコスト／障害を編集できます。';
    if (mode === 'link') hint.textContent = '「接続」モードで2つのノードを順にクリックするとリンクを作成します。';
    if (mode === 'delete') hint.textContent = '「削除」モードでノードまたはリンクをクリックすると削除します。';
    freeRender();
  }

  function freeHandleNodeClick(nodeId) {
    if (Free.interactionMode === 'delete') {
      Free.topo.links = Free.topo.links.filter((l) => l.a !== nodeId && l.b !== nodeId);
      const n = Free.topo.nodes.get(nodeId);
      Free.topo.nodes.delete(nodeId);
      freeLog('sys', `${n ? n.name : nodeId} を削除しました`);
      freeRender();
      freePopulateSelects();
      return;
    }
    if (Free.interactionMode === 'link') {
      if (!Free.linkFirstPick) {
        Free.linkFirstPick = nodeId;
        freeRender();
        return;
      }
      if (Free.linkFirstPick === nodeId) { Free.linkFirstPick = null; freeRender(); return; }
      const a = Free.linkFirstPick, b = nodeId;
      Free.linkFirstPick = null;
      if (findLinkBetween(Free.topo, a, b)) {
        freeLog('sys', 'そのノード間には既にリンクがあります');
        freeRender();
        return;
      }
      const nodeA = Free.topo.nodes.get(a), nodeB = Free.topo.nodes.get(b);
      const routable = nodeA.type === 'router' || nodeB.type === 'router';
      openCostModal({
        title: '新しいリンク',
        subtitle: `${nodeA.name} — ${nodeB.name}`,
        initialCost: 1,
        costEditable: routable,
        initialDown: false,
        onSave: (cost, down) => {
          const id = uid('fl');
          Free.topo.links.push({ id, a, b, cost: routable ? cost : 0, down, routable });
          freeLog('sys', `${nodeA.name} — ${nodeB.name} を接続しました`);
          freeRender();
        }
      });
    }
  }

  function freeHandleLinkClick(linkId) {
    const link = Free.topo.links.find((l) => l.id === linkId);
    if (!link) return;
    if (Free.interactionMode === 'delete') {
      Free.topo.links = Free.topo.links.filter((l) => l.id !== linkId);
      freeLog('sys', 'リンクを削除しました');
      freeRender();
      return;
    }
    const nodeA = Free.topo.nodes.get(link.a), nodeB = Free.topo.nodes.get(link.b);
    openCostModal({
      title: 'リンク設定',
      subtitle: `${nodeA.name} — ${nodeB.name}`,
      initialCost: link.cost,
      costEditable: link.routable,
      initialDown: link.down,
      onSave: (cost, down) => {
        if (link.routable) link.cost = cost;
        link.down = down;
        freeLog('sys', `${nodeA.name} — ${nodeB.name} を更新しました`);
        freeRender();
      }
    });
  }

  function freeSend() {
    const srcId = document.getElementById('free-src-pc').value;
    const dstId = document.getElementById('free-dst-pc').value;
    const statusEl = document.getElementById('free-send-status');
    if (!srcId || !dstId) { statusEl.textContent = '送信元・宛先のPCを配置してください。'; return; }
    if (srcId === dstId) { statusEl.textContent = '送信元と宛先が同じです。'; return; }
    statusEl.textContent = '送信中…';
    simulateSend(Free.topo, srcId, dstId, freeLog, Free.svg, {
      onFinish: (result) => { statusEl.textContent = result.reachable ? '送信完了' : '送信失敗（不通）'; }
    });
  }

  function svgPointFromEvent(svgEl, evt) {
    const pt = svgEl.createSVGPoint();
    pt.x = evt.clientX; pt.y = evt.clientY;
    const ctm = svgEl.getScreenCTM();
    if (!ctm) return { x: 0, y: 0 };
    const loc = pt.matrixTransform(ctm.inverse());
    return { x: loc.x, y: loc.y };
  }

  function initFreeMode() {
    Free.svg = document.getElementById('free-svg');
    Free.logEl = document.getElementById('free-log');
    freeRender();
    freePopulateSelects();

    document.querySelectorAll('#panel-free [data-add]').forEach((btn) => {
      btn.addEventListener('click', () => freeAddNode(btn.dataset.add));
    });
    document.querySelectorAll('#panel-free [data-mode]').forEach((btn) => {
      btn.addEventListener('click', () => freeSetMode(btn.dataset.mode));
    });
    document.getElementById('free-clear').addEventListener('click', () => {
      Free.topo.nodes.clear();
      Free.topo.links = [];
      Free.typeCounters = { pc: 0, switch: 0, router: 0 };
      freeRender();
      freePopulateSelects();
      freeLog('sys', 'すべて消去しました');
    });
    document.getElementById('free-send-btn').addEventListener('click', freeSend);
    document.getElementById('free-clear-log').addEventListener('click', () => { Free.logEl.innerHTML = ''; });

    // クリック（ノード／リンク）
    Free.svg.addEventListener('click', (e) => {
      if (Free.dragging && Free.dragging.moved) return; // ドラッグ直後のクリックは無視
      const nodeTarget = e.target.closest('[data-node-id]');
      if (nodeTarget) { freeHandleNodeClick(nodeTarget.dataset.nodeId); return; }
      const linkTarget = e.target.closest('[data-link-id]');
      if (linkTarget) { freeHandleLinkClick(linkTarget.dataset.linkId); return; }
    });

    Free.svg.addEventListener('mousemove', (e) => {
      const nodeTarget = e.target.closest('[data-node-id]');
      const id = nodeTarget ? nodeTarget.dataset.nodeId : null;
      if (id !== Free.hoverNodeId) { Free.hoverNodeId = id; freeRender(); }
    });

    // ドラッグ移動（moveモードのみ）
    Free.svg.addEventListener('mousedown', (e) => {
      if (Free.interactionMode !== 'move') return;
      const nodeTarget = e.target.closest('[data-node-id]');
      if (!nodeTarget) return;
      const id = nodeTarget.dataset.nodeId;
      const node = Free.topo.nodes.get(id);
      const start = svgPointFromEvent(Free.svg, e);
      Free.dragging = { id, offX: node.x - start.x, offY: node.y - start.y, moved: false };
      nodeTarget.classList.add('is-dragging');
    });
    window.addEventListener('mousemove', (e) => {
      if (!Free.dragging) return;
      const node = Free.topo.nodes.get(Free.dragging.id);
      if (!node) return;
      const p = svgPointFromEvent(Free.svg, e);
      node.x = clamp(p.x + Free.dragging.offX, 30, 1090);
      node.y = clamp(p.y + Free.dragging.offY, 30, 530);
      Free.dragging.moved = true;
      freeRender();
    });
    window.addEventListener('mouseup', () => {
      if (Free.dragging) setTimeout(() => { Free.dragging = null; }, 0);
    });

    freeLog('sys', '「PC」「スイッチ」「ルーター」を追加してネットワークを組み立ててください。');
  }

  /* ------------------------------------------------------------------ *
   * 9. タブ切替 & 初期化
   * ------------------------------------------------------------------ */

  function initTabs() {
    const tabFixed = document.getElementById('tab-fixed');
    const tabFree = document.getElementById('tab-free');
    const panelFixed = document.getElementById('panel-fixed');
    const panelFree = document.getElementById('panel-free');

    function activate(which) {
      const isFixed = which === 'fixed';
      tabFixed.classList.toggle('is-active', isFixed);
      tabFree.classList.toggle('is-active', !isFixed);
      tabFixed.setAttribute('aria-selected', String(isFixed));
      tabFree.setAttribute('aria-selected', String(!isFixed));
      panelFixed.classList.toggle('is-hidden', !isFixed);
      panelFree.classList.toggle('is-hidden', isFixed);
      panelFixed.hidden = !isFixed;
      panelFree.hidden = isFixed;
    }
    tabFixed.addEventListener('click', () => activate('fixed'));
    tabFree.addEventListener('click', () => activate('free'));
  }

  document.addEventListener('DOMContentLoaded', () => {
    initTabs();
    initModal();
    initFixedMode();
    initFreeMode();
  });
})();
