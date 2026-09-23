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

  const FLOW_PALETTE = ['#4fd8c4', '#f0a94e', '#e2584c', '#8ab4d6', '#c99ae0', '#9fd68a', '#f2789a', '#f7d774'];

  /* ------------------------------------------------------------------ *
   * 0b. IPアドレス／サブネットマスク ユーティリティ
   * ------------------------------------------------------------------ */

  function parseIp(str) {
    if (typeof str !== 'string') return null;
    const m = str.trim().match(/^(\d{1,3})\.(\d{1,3})\.(\d{1,3})\.(\d{1,3})$/);
    if (!m) return null;
    const parts = m.slice(1, 5).map(Number);
    if (parts.some((p) => p < 0 || p > 255)) return null;
    return (parts[0] << 24) | (parts[1] << 16) | (parts[2] << 8) | parts[3];
  }

  function isValidIpFormat(str) { return parseIp(str) !== null; }

  // "/24" または "255.255.255.0" のどちらも受け付け、プレフィックス長(0-32)を返す。不正なら null。
  function parseMaskToPrefix(str) {
    if (typeof str !== 'string') return null;
    const s = str.trim();
    if (s.startsWith('/')) {
      const n = parseInt(s.slice(1), 10);
      if (Number.isInteger(n) && n >= 0 && n <= 32 && String(n) === s.slice(1)) return n;
      return null;
    }
    const asIp = parseIp(s);
    if (asIp === null) return null;
    const unsigned = asIp >>> 0;
    // 連続した1のあとに連続した0が続く形式かどうかを検証
    let prefix = 0;
    let seenZero = false;
    for (let bit = 31; bit >= 0; bit--) {
      const isOne = (unsigned >>> bit) & 1;
      if (isOne) {
        if (seenZero) return null; // 0の後に1が来る＝不正なマスク
        prefix++;
      } else {
        seenZero = true;
      }
    }
    return prefix;
  }

  function isValidMaskFormat(str) { return parseMaskToPrefix(str) !== null; }

  function networkKey(ip, prefix) {
    const ipInt = parseIp(ip);
    if (ipInt === null || prefix === null) return null;
    const maskBits = prefix === 0 ? 0 : (0xFFFFFFFF << (32 - prefix)) >>> 0;
    return ((ipInt & maskBits) >>> 0) + '/' + prefix;
  }

  function intToIp(n) {
    const u = n >>> 0;
    return [(u >>> 24) & 255, (u >>> 16) & 255, (u >>> 8) & 255, u & 255].join('.');
  }

  function networkLabelFor(ip, mask) {
    const ipInt = parseIp(ip);
    const prefix = parseMaskToPrefix(mask);
    if (ipInt === null || prefix === null) return null;
    const maskBits = prefix === 0 ? 0 : (0xFFFFFFFF << (32 - prefix)) >>> 0;
    const netInt = (ipInt & maskBits) >>> 0;
    return `${intToIp(netInt)}/${prefix}`;
  }

  /* ------------------------------------------------------------------ *
   * 0c. 単純Union-Find（自由配置のサブネット判定に使用）
   * ------------------------------------------------------------------ */

  function createUnionFind() {
    const parent = new Map();
    function find(x) {
      if (!parent.has(x)) parent.set(x, x);
      if (parent.get(x) !== x) parent.set(x, find(parent.get(x)));
      return parent.get(x);
    }
    function union(a, b) {
      const ra = find(a), rb = find(b);
      if (ra !== rb) parent.set(ra, rb);
    }
    return { find, union, keys: () => Array.from(parent.keys()) };
  }

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

  // 指定したIPアドレスを持つルーターノードを探す（トップレベルip、またはインタフェースip）
  function findRouterByIp(topology, ip) {
    let found = null;
    topology.nodes.forEach((n) => {
      if (found || n.type !== 'router') return;
      if (n.ip === ip) { found = n; return; }
      if (n.ifaces) {
        Object.values(n.ifaces).forEach((iface) => { if (iface.ip === ip) found = n; });
      }
    });
    return found;
  }

  // 「PC → デフォルトゲートウェイ」を計算する（ここは固定・確定した区間）。
  // ゲートウェイから先は、各ルーターがその時点で持つ分散ルーティングテーブルにより
  // 1ホップずつその場で決まるため、ここでは事前には分からない。
  function computeGatewayRoute(topology, srcId, dstId) {
    const src = topology.nodes.get(srcId);
    if (!src || !src.gateway) return { reachable: false, path: [], cost: Infinity, error: 'no-gateway' };
    const gwNode = findRouterByIp(topology, src.gateway);
    if (!gwNode) return { reachable: false, path: [], cost: Infinity, error: 'gateway-unreachable' };
    const leg1 = dijkstra(topology, srcId, gwNode.id);
    if (!leg1.reachable) return { reachable: false, path: [], cost: Infinity, error: 'gateway-unreachable' };
    return { reachable: true, path: leg1.path, cost: leg1.cost, gatewayId: gwNode.id };
  }

  // ルーターごとのルーティングテーブルを算出（現在そのルーターが持っている情報をそのまま表示する）
  function computeRoutingTable(topology, routerId, segments) {
    const router = topology.nodes.get(routerId);
    const linkCount = topology.links.filter((l) => l.a === routerId || l.b === routerId).length;
    if (linkCount === 0) return { rows: [], emptyNote: '経路情報なし（リンクが接続されていません）' };

    const vec = (router && router.rtVector) || {};
    let rows = [];
    segments.forEach((seg) => {
      if (seg.repId === routerId) return;
      const entry = vec[seg.repId];
      if (!entry) { rows.push({ network: seg.label, nextHop: '—', metric: '未学習', type: 'unreachable' }); return; }
      if (entry.nextHop === null) {
        rows.push({ network: seg.label, nextHop: '直結', metric: entry.cost, type: 'connected' });
      } else {
        const nextHopNode = topology.nodes.get(entry.nextHop);
        rows.push({ network: seg.label, nextHop: nextHopNode ? nextHopNode.name : '?', metric: entry.cost, type: 'remote' });
      }
    });

    if (linkCount === 1) {
      rows = rows.filter((r) => r.type === 'connected');
      if (rows.length === 0) return { rows: [], emptyNote: '直結ネットワークの情報のみ（他ネットワークへの経路は未学習）' };
    }
    return { rows, emptyNote: rows.length === 0 ? '経路情報なし（まだ学習していません）' : null };
  }

  // トポロジ内の「ネットワークセグメント」（switch経由でつながるPC群）を列挙する。固定・自由配置の両方で共通利用
  function computeNetworkSegments(topo) {
    const uf = freeBuildClusters(topo);
    const clusters = new Map();
    uf.keys().forEach((key) => {
      const root = uf.find(key);
      if (!clusters.has(root)) clusters.set(root, []);
      clusters.get(root).push(key);
    });
    const segments = [];
    clusters.forEach((keys) => {
      const memberIds = new Set();
      let repId = null, label = null;
      keys.forEach((k) => {
        if (k.includes('::')) return;
        const n = topo.nodes.get(k);
        if (n && n.type === 'pc') {
          memberIds.add(k);
          if (!repId && isValidIpFormat(n.ip) && isValidMaskFormat(n.mask)) {
            repId = k;
            label = networkLabelFor(n.ip, n.mask);
          }
        }
      });
      if (repId) segments.push({ label, repId, memberIds });
    });
    return segments;
  }

  function segmentForNode(segments, nodeId) {
    return segments.find((s) => s.memberIds && s.memberIds.has(nodeId)) || null;
  }

  /* ------------------------------------------------------------------ *
   * 1b. 距離ベクター型ルーティング（RIP方式）
   * 各ルーターが自分の rtVector（宛先セグメントrepId -> {cost, nextHop}）を保持し、
   * 隣接ルーターとのみ定期的に情報交換して収束していく。
   * ------------------------------------------------------------------ */

  const RV_INFINITY = 50;
  const RV_INTERVAL_MS = 2500;

  // routerIdから他のルーターを跨がずに（スイッチ経由のみで）segRepIdへ到達できるか
  function rvIsDirectlyConnected(topo, routerId, segRepId) {
    if (routerId === segRepId) return false;
    const visited = new Set([routerId]);
    const queue = [routerId];
    while (queue.length) {
      const cur = queue.shift();
      const adjacentLinks = topo.links.filter((l) => (l.a === cur || l.b === cur) && !l.down);
      for (const l of adjacentLinks) {
        const other = l.a === cur ? l.b : l.a;
        if (visited.has(other)) continue;
        if (other === segRepId) return true;
        const n = topo.nodes.get(other);
        if (!n) continue;
        if (n.type === 'router' && other !== routerId) continue; // 他のルーターを跨がない
        visited.add(other);
        queue.push(other);
      }
    }
    return false;
  }

  // ルーターごとの隣接ルーター一覧（router-router直結リンクのみ）
  function rvNeighbors(topo, routerId) {
    return topo.links
      .filter((l) => l.routable && (l.a === routerId || l.b === routerId))
      .map((l) => ({ id: l.a === routerId ? l.b : l.a, link: l }))
      .filter((nb) => { const n = topo.nodes.get(nb.id); return n && n.type === 'router'; });
  }

  // ルーターのテーブルを初期化する（coldStart=trueなら空から、falseなら直結情報のみ仕込んでおく）
  function rvInitTables(topo, segments, coldStart) {
    topo.nodes.forEach((n) => {
      if (n.type !== 'router') return;
      n.rtVector = {};
      if (coldStart) return;
      segments.forEach((seg) => {
        if (seg.repId === n.id) return;
        if (rvIsDirectlyConnected(topo, n.id, seg.repId)) {
          n.rtVector[seg.repId] = { cost: 0, nextHop: null };
        }
      });
    });
  }

  // 1回分の情報交換（同期的なラウンド）。直結セグメントの再確認 → 隣接ルーターへの通知、の順で行う
  function rvExchangeTick(topo, segments, logFn) {
    topo.nodes.forEach((n) => {
      if (n.type !== 'router') return;
      if (!n.rtVector) n.rtVector = {};
      segments.forEach((seg) => {
        if (seg.repId === n.id) return;
        if (rvIsDirectlyConnected(topo, n.id, seg.repId)) {
          n.rtVector[seg.repId] = { cost: 0, nextHop: null };
        }
      });
    });

    const nextTables = new Map();
    topo.nodes.forEach((n) => { if (n.type === 'router') nextTables.set(n.id, Object.assign({}, n.rtVector)); });

    topo.nodes.forEach((n) => {
      if (n.type !== 'router') return;
      const myTable = n.rtVector;
      rvNeighbors(topo, n.id).forEach((nb) => {
        if (nb.link.down) return;
        const nbTable = nextTables.get(nb.id);
        if (!nbTable) return;
        Object.keys(myTable).forEach((segId) => {
          if (segId === nb.id) return;
          const advertised = myTable[segId].cost + nb.link.cost;
          const existing = nbTable[segId];
          const shouldAccept = !existing || advertised < existing.cost || existing.nextHop === n.id;
          if (!shouldAccept) return;
          if (advertised >= RV_INFINITY) {
            if (existing && existing.nextHop === n.id) delete nbTable[segId];
          } else {
            nbTable[segId] = { cost: advertised, nextHop: n.id };
          }
        });
      });
    });

    topo.nodes.forEach((n) => {
      if (n.type !== 'router') return;
      n.rtVector = nextTables.get(n.id);
    });
  }

  function startRvTimer(store, topo, rerender) {
    stopRvTimer(store);
    store.rvTimer = setInterval(() => {
      const segments = computeNetworkSegments(topo);
      rvExchangeTick(topo, segments);
      if (rerender) rerender();
    }, RV_INTERVAL_MS);
  }

  function stopRvTimer(store) {
    if (store.rvTimer) { clearInterval(store.rvTimer); store.rvTimer = null; }
  }

  // リンク状態の変化を即座に隣接ルーターへ伝える（トリガード・アップデート：最初の1ホップ分のみ即時反映）
  function rvTriggerUpdate(topo) {
    const segments = computeNetworkSegments(topo);
    rvExchangeTick(topo, segments);
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

    function addNode(id, type, name, ip, mac, x, y, extra) {
      const node = { id, type, name, ip: ip || null, mac: mac || null, x, y };
      Object.assign(node, extra || {});
      if (type === 'router') node.ifaces = {};
      nodes.set(id, node);
    }
    function addLink(id, a, b, cost, routable) {
      links.push({ id, a, b, cost: cost || 0, baseCost: cost || 0, load: 0, down: false, routable: !!routable });
    }

    // 送信側 PC（デフォルトゲートウェイ = RT-S）
    addNode('pc-s1', 'pc', 'PC-S1', '192.168.1.11', randMac(0x11), 70, 120, { mask: '/24', gateway: '192.168.1.1' });
    addNode('pc-s2', 'pc', 'PC-S2', '192.168.1.12', randMac(0x12), 70, 280, { mask: '/24', gateway: '192.168.1.1' });
    addNode('pc-s3', 'pc', 'PC-S3', '192.168.1.13', randMac(0x13), 70, 440, { mask: '/24', gateway: '192.168.1.1' });
    addNode('sw-s', 'switch', 'SW-S', null, randMac(0x20), 230, 280);
    addNode('rt-s', 'router', 'RT-S', '192.168.1.1', randMac(0x30), 380, 280);

    // 中継ルーター（3経路・双方に直結）
    addNode('rt-a', 'router', 'RT-A', null, randMac(0x41), 590, 110);
    addNode('rt-b', 'router', 'RT-B', null, randMac(0x42), 590, 280);
    addNode('rt-c', 'router', 'RT-C', null, randMac(0x43), 590, 450);

    // 受信側（デフォルトゲートウェイ = RT-R）
    addNode('rt-r', 'router', 'RT-R', '192.168.2.1', randMac(0x50), 800, 280);
    addNode('sw-r', 'switch', 'SW-R', null, randMac(0x60), 950, 280);
    addNode('pc-r1', 'pc', 'PC-R1', '192.168.2.11', randMac(0x71), 1060, 120, { mask: '/24', gateway: '192.168.2.1' });
    addNode('pc-r2', 'pc', 'PC-R2', '192.168.2.12', randMac(0x72), 1060, 280, { mask: '/24', gateway: '192.168.2.1' });
    addNode('pc-r3', 'pc', 'PC-R3', '192.168.2.13', randMac(0x73), 1060, 440, { mask: '/24', gateway: '192.168.2.1' });

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

    // 中継リンクの各ルーターインタフェースにIPアドレスを割り当てる（両端は同じサブネット）
    const topo = { nodes, links };
    const ifaceSubnets = {
      'rt-s_rt-a': '10.1.1', 'rt-a_rt-r': '10.1.2',
      'rt-s_rt-b': '10.1.3', 'rt-b_rt-r': '10.1.4',
      'rt-s_rt-c': '10.1.5', 'rt-c_rt-r': '10.1.6'
    };
    Object.keys(ifaceSubnets).forEach((linkId) => {
      const link = links.find((l) => l.id === linkId);
      const net = ifaceSubnets[linkId];
      const nodeA = nodes.get(link.a), nodeB = nodes.get(link.b);
      nodeA.ifaces[linkId] = { ip: `${net}.1`, mask: '/30' };
      nodeB.ifaces[linkId] = { ip: `${net}.2`, mask: '/30' };
    });

    return topo;
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

  /* ---- メッシュ接続（RT-A—RT-B、RT-B—RT-C）: 固定トポロジのみ ---- */

  const MESH_LINK_DEFS = [
    { id: 'rt-a_rt-b', a: 'rt-a', b: 'rt-b', label: 'RT-A — RT-B' },
    { id: 'rt-b_rt-c', a: 'rt-b', b: 'rt-c', label: 'RT-B — RT-C' }
  ];
  const MESH_DEFAULT_COST = 3;

  function addMeshLinks(topo) {
    MESH_LINK_DEFS.forEach((md, idx) => {
      if (topo.links.some((l) => l.id === md.id)) return;
      topo.links.push({ id: md.id, a: md.a, b: md.b, cost: MESH_DEFAULT_COST, baseCost: MESH_DEFAULT_COST, load: 0, down: false, routable: true, mesh: true });
      const nodeA = topo.nodes.get(md.a), nodeB = topo.nodes.get(md.b);
      const net = `10.1.${7 + idx}`;
      if (nodeA && nodeA.ifaces) nodeA.ifaces[md.id] = { ip: `${net}.1`, mask: '/30' };
      if (nodeB && nodeB.ifaces) nodeB.ifaces[md.id] = { ip: `${net}.2`, mask: '/30' };
    });
  }

  function removeMeshLinks(topo) {
    MESH_LINK_DEFS.forEach((md) => {
      const l = topo.links.find((x) => x.id === md.id);
      if (l && l._recoveryTimer) { clearTimeout(l._recoveryTimer); l._recoveryTimer = null; }
      const nodeA = topo.nodes.get(md.a), nodeB = topo.nodes.get(md.b);
      if (nodeA && nodeA.ifaces) delete nodeA.ifaces[md.id];
      if (nodeB && nodeB.ifaces) delete nodeB.ifaces[md.id];
    });
    topo.links = topo.links.filter((l) => !l.mesh);
  }

  // RT-SからRT-Rまでの「ルーターのみを通る単純経路」をすべて列挙する（メッシュ有効時の経路比較用）
  function enumerateRouterPaths(topology, srcId, dstId) {
    const routerIds = new Set();
    topology.nodes.forEach((n, id) => { if (n.type === 'router') routerIds.add(id); });
    const adj = new Map();
    routerIds.forEach((id) => adj.set(id, []));
    topology.links.forEach((l) => {
      if (!l.routable || !routerIds.has(l.a) || !routerIds.has(l.b)) return;
      adj.get(l.a).push({ to: l.b, link: l });
      adj.get(l.b).push({ to: l.a, link: l });
    });
    const results = [];
    function dfs(current, visited, path, cost, hasDown) {
      if (current === dstId) { results.push({ path: path.slice(), cost, down: hasDown }); return; }
      (adj.get(current) || []).forEach((edge) => {
        if (visited.has(edge.to)) return;
        visited.add(edge.to);
        path.push(edge.to);
        dfs(edge.to, visited, path, cost + edge.link.cost, hasDown || edge.link.down);
        path.pop();
        visited.delete(edge.to);
      });
    }
    dfs(srcId, new Set([srcId]), [srcId], 0, false);
    return results;
  }

  function extractRouterSubpath(topology, fullPath) {
    return fullPath.filter((id) => {
      const n = topology.nodes.get(id);
      return n && n.type === 'router';
    });
  }

  /* ------------------------------------------------------------------ *
   * 3. SVG 描画
   * ------------------------------------------------------------------ */

  const SVG_NS = 'http://www.w3.org/2000/svg';

  function formatIpMask(ip, mask) {
    if (!ip) return '';
    if (!mask) return ip;
    const prefix = parseMaskToPrefix(mask);
    return prefix !== null ? `${ip}/${prefix}` : `${ip} ${mask}`;
  }


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
      if (l.mesh) cls += ' is-mesh';
      if (l.down) cls += ' is-down';
      if (isActive) cls += ' is-active-path';
      html += `<line class="${cls}" data-link-id="${l.id}" x1="${pts.x1}" y1="${pts.y1}" x2="${pts.x2}" y2="${pts.y2}"></line>`;
      html += `<line class="link-hit" data-link-id="${l.id}" style="cursor:${clickable ? 'pointer' : 'default'}" x1="${pts.x1}" y1="${pts.y1}" x2="${pts.x2}" y2="${pts.y2}"></line>`;

      if (l.routable) {
        const mx = (pts.x1 + pts.x2) / 2, my = (pts.y1 + pts.y2) / 2;
        const label = l.down ? 'DOWN' : String(l.cost);
        const bw = l.down ? 52 : 26;
        const bh = l.down ? 20 : 21;
        const labelY = l.down ? my : my - 14; // コスト値は上にずらす。DOWNは位置そのまま
        html += `<rect class="link-cost-bg" x="${mx - bw / 2}" y="${labelY - bh / 2}" width="${bw}" height="${bh}" rx="3"></rect>`;
        html += `<text class="link-cost${l.down ? ' is-down' : ''}" x="${mx}" y="${labelY + 5}" text-anchor="middle">${label}</text>`;
      }
    });

    // 送信中／送信済みの経路を表すフロー（流れるライン）オーバーレイ
    html += renderFlowOverlay(topology, state.flows, state.speedFactor);

    // nodes
    topology.nodes.forEach((n) => {
      const size = nodeSize(n.type);
      const isRouter = n.type === 'router';
      const isSelected = state.selectedNodeId === n.id;
      const isHover = state.hoverNodeId === n.id;
      const hasError = state.errorNodeIds && state.errorNodeIds.has(n.id);
      let boxCls = 'n-box' + (isRouter ? ' is-router' : '') + (isHover ? ' is-hover' : '') + (hasError ? ' has-error' : '');
      let groupCls = state.freeMode ? 'free-node' : 'topo-node';
      if (isSelected) groupCls += ' is-selected';
      const title = `${n.name}${n.ip ? '\n' + n.ip : ''}${n.mac ? '\n' + n.mac : ''}`;
      html += `<g class="${groupCls}" data-node-id="${n.id}" transform="translate(${n.x},${n.y})">
        <title>${title}</title>
        <rect class="${boxCls}" x="${-size.w / 2}" y="${-size.h / 2}" width="${size.w}" height="${size.h}" rx="${isRouter ? 10 : 5}"></rect>
        ${nodeIconMarkup(n.type)}
        <text class="n-label" y="${size.h / 2 + 15}">${n.name}</text>
        ${n.ip ? `<text class="n-sub" y="${size.h / 2 + 27}">${formatIpMask(n.ip, n.mask)}</text>` : ''}
        ${hasError ? `<g class="n-error-badge" transform="translate(${size.w / 2 - 4},${-size.h / 2 + 4})"><circle r="8"></circle><text y="4">!</text></g>` : ''}
      </g>`;
    });

    // 転送中パケットのアイコン（フローラインの一番上に表示）
    html += renderPacketIcons(topology, state.flows);

    svgEl.innerHTML = html;
  }

  function renderFlowOverlay(topology, flows, speedFactor) {
    if (!flows || !flows.length) return '';
    const groups = new Map();
    flows.forEach((flow) => {
      for (let i = 0; i < flow.path.length - 1; i++) {
        const aId = flow.path[i], bId = flow.path[i + 1];
        const a = topology.nodes.get(aId), b = topology.nodes.get(bId);
        if (!a || !b) continue;
        const key = [aId, bId].sort().join('|');
        if (!groups.has(key)) groups.set(key, []);
        groups.get(key).push({ flow, a, b });
      }
    });
    const dashDur = (FLOW_DASH_BASE_SEC / (speedFactor || 1)).toFixed(2);
    let html = '';
    groups.forEach((entries) => {
      const n = entries.length;
      entries.forEach((e, idx) => {
        const offset = (idx - (n - 1) / 2) * 5;
        const dx = e.b.x - e.a.x, dy = e.b.y - e.a.y;
        const len = Math.hypot(dx, dy) || 1;
        const px = -dy / len, py = dx / len;
        const pad = Math.max(nodeSize(e.a.type).w, nodeSize(e.a.type).h) / 2 + 4;
        const pts = shortenedEndpoints(e.a.x, e.a.y, e.b.x, e.b.y, pad);
        const x1 = pts.x1 + px * offset, y1 = pts.y1 + py * offset;
        const x2 = pts.x2 + px * offset, y2 = pts.y2 + py * offset;
        const state = e.flow.state;
        const cls = 'flow-line ' + (state === 'flowing' ? 'is-flowing' : (state === 'lost' ? 'is-failed' : 'is-done'));
        const style = state === 'flowing' ? ` style="animation-duration:${dashDur}s"` : '';
        html += `<line class="${cls}" stroke="${e.flow.color}"${style} x1="${x1.toFixed(1)}" y1="${y1.toFixed(1)}" x2="${x2.toFixed(1)}" y2="${y2.toFixed(1)}"></line>`;
      });
    });
    return html;
  }

  function packetIconMarkup(color, motionPath, dur, staticX, staticY) {
    const envelope = `<rect x="-8" y="-6" width="16" height="12" rx="2" fill="${color}" stroke="#0b1119" stroke-width="1"></rect>` +
      `<path d="M -8,-6 L 0,1 L 8,-6" fill="none" stroke="#0b1119" stroke-width="1"></path>`;
    if (motionPath) {
      return `<g class="pkt-icon">${envelope}<animateMotion dur="${dur}s" path="${motionPath}" fill="freeze" repeatCount="1"></animateMotion></g>`;
    }
    return `<g class="pkt-icon" transform="translate(${staticX},${staticY})">${envelope}</g>`;
  }

  function renderPacketIcons(topology, flows) {
    if (!flows || !flows.length) return '';
    let html = '';
    flows.forEach((flow) => {
      if (flow.state === 'flowing' && flow.segmentFrom && flow.segmentTo) {
        const a = topology.nodes.get(flow.segmentFrom), b = topology.nodes.get(flow.segmentTo);
        if (!a || !b) return;
        const p = flow.segmentProgressAtRestart || 0;
        const sx = a.x + (b.x - a.x) * p, sy = a.y + (b.y - a.y) * p;
        const dur = Math.max(0.05, flow.segmentDurationMs / 1000);
        html += packetIconMarkup(flow.color, `M ${sx.toFixed(1)} ${sy.toFixed(1)} L ${b.x} ${b.y}`, dur.toFixed(2));
      } else if (flow.state === 'done' && !flow.iconGone) {
        const endId = flow.path[flow.path.length - 1];
        const n = topology.nodes.get(endId);
        if (n) html += packetIconMarkup(flow.color, null, null, n.x, n.y);
      }
    });
    return html;
  }

  function nextFlowColor(store) {
    const c = FLOW_PALETTE[store.colorIdx % FLOW_PALETTE.length];
    store.colorIdx += 1;
    return c;
  }

  /* ---- 送信フロー・エンジン ---- */

  const HOP_BASE_MS = 700;
  const FLOW_DASH_BASE_SEC = 0.55;
  const INITIAL_TTL = 8;
  const LINK_LOAD_PER_USE = 2;

  function startFlow(store, topology, path, dstId, destSegRepId, rerender, logFn) {
    if (!path || path.length < 1) return null;
    const flow = {
      id: uid('flow'),
      color: nextFlowColor(store),
      dstId,
      destSegRepId,
      path: path.slice(),
      currentIndex: 0,
      state: 'flowing',
      ttl: INITIAL_TTL,
      segmentFrom: null,
      segmentTo: null,
      segmentStartedAt: null,
      segmentDurationMs: null,
      segmentProgressAtRestart: 0,
      segmentTimer: null,
      doneAt: null,
      iconGone: false,
      store,
      topology,
      rerender,
      logFn
    };
    store.flows.push(flow);
    if (path.length < 2) {
      decideNextHop(flow);
      if (flow.state !== 'flowing') return flow;
    }
    advanceFlowSegment(flow);
    return flow;
  }

  function markLinkUsed(topology, fromId, toId) {
    const link = findLinkBetween(topology, fromId, toId);
    if (link && link.routable) {
      link.load = (link.load || 0) + LINK_LOAD_PER_USE;
      recalcLinkCost(link);
    }
  }

  function loseFlow(flow, atNodeId, reasonMsg) {
    flow.state = 'lost';
    flow.doneAt = Date.now();
    const n = flow.topology.nodes.get(atNodeId);
    if (flow.logFn) flow.logFn('fail', `${n ? n.name : atNodeId} 付近でパケットが失われました（${reasonMsg}）`);
    flow.rerender();
    if (flow.onResolved) flow.onResolved('lost');
  }

  // ルーターが自分の（その時点の）ルーティングテーブルを見て、次のホップをその場で決める
  function decideNextHop(flow) {
    const topology = flow.topology;
    const currentId = flow.path[flow.path.length - 1];
    const currentNode = topology.nodes.get(currentId);
    if (!currentNode || currentNode.type !== 'router') return;
    if (currentId === flow.dstId) return;

    const vec = currentNode.rtVector || {};
    const entry = flow.destSegRepId ? vec[flow.destSegRepId] : null;

    if (!entry) {
      loseFlow(flow, currentId, '宛先への経路情報が未学習');
      return;
    }
    if (flow.logFn) {
      const desc = entry.nextHop === null ? '直結' : (topology.nodes.get(entry.nextHop) ? topology.nodes.get(entry.nextHop).name : '?');
      flow.logFn('route', `${currentNode.name}: 自分のルーティングテーブルを参照 → 宛先まで残りコスト${entry.cost}、ネクストホップ ${desc}`);
    }
    if (entry.nextHop === null) {
      // 直結：スイッチ経由で宛先PCまでの区間を延長する
      const result = dijkstra(topology, currentId, flow.dstId);
      if (!result.reachable) { loseFlow(flow, currentId, '宛先セグメントへの物理経路がありません'); return; }
      flow.path = flow.path.concat(result.path.slice(1));
    } else {
      const link = findLinkBetween(topology, currentId, entry.nextHop);
      if (!link || link.down) { loseFlow(flow, currentId, 'ネクストホップへのリンクが利用できません'); return; }
      flow.path.push(entry.nextHop);
    }
  }

  function advanceFlowSegment(flow) {
    if (flow.state !== 'flowing') return;
    const fromId = flow.path[flow.currentIndex];
    const toId = flow.path[flow.currentIndex + 1];
    const fromNode = flow.topology.nodes.get(fromId);
    // ルーターを通過する時点でTTLを消費する（PC・スイッチでは消費しない）
    if (fromNode && fromNode.type === 'router' && flow.currentIndex > 0) {
      flow.ttl -= 1;
      if (flow.ttl <= 0) { loseFlow(flow, fromId, 'TTL超過'); return; }
    }
    const link = findLinkBetween(flow.topology, fromId, toId);
    if (link && link.down) { loseFlow(flow, fromId, 'リンク障害'); return; }
    const hopMs = HOP_BASE_MS / (flow.store.speedFactor || 1);
    flow.segmentFrom = fromId;
    flow.segmentTo = toId;
    flow.segmentStartedAt = Date.now();
    flow.segmentDurationMs = hopMs;
    flow.segmentProgressAtRestart = 0;
    clearTimeout(flow.segmentTimer);
    flow.segmentTimer = setTimeout(() => onSegmentComplete(flow), hopMs);
    flow.rerender();
  }

  function onSegmentComplete(flow) {
    if (flow.state !== 'flowing') return;
    markLinkUsed(flow.topology, flow.segmentFrom, flow.segmentTo);
    flow.currentIndex++;
    const arrivedId = flow.path[flow.currentIndex];

    if (arrivedId === flow.dstId) {
      flow.state = 'done';
      flow.doneAt = Date.now();
      const n = flow.topology.nodes.get(arrivedId);
      if (flow.logFn) flow.logFn('ok', `${n ? n.name : arrivedId}: フレーム受信 → デカプセル化 → パケット到達（通信成功）`);
      flow.rerender();
      if (flow.onResolved) flow.onResolved('done');
      setTimeout(() => { flow.iconGone = true; flow.rerender(); }, 600);
      return;
    }

    if (flow.currentIndex >= flow.path.length - 1) {
      // 経路の末端＝ここから先はまだ決まっていない。ルーターならその場で次を決める
      decideNextHop(flow);
      if (flow.state !== 'flowing') return;
    }
    advanceFlowSegment(flow);
  }

  // 送信1回分（最大5回まで自動再送を試みる「セッション」）
  function startDeliverySession(store, topology, srcId, dstId, rerender, logFn, onSettled) {
    let attempt = 0;
    const MAX_ATTEMPTS = 5;
    function tryAttempt() {
      attempt++;
      const route = computeGatewayRoute(topology, srcId, dstId);
      if (!route.reachable) {
        const src = topology.nodes.get(srcId);
        logFn('fail', `${src ? src.name : srcId}: 経路を計算できません（${route.error === 'no-gateway' ? 'デフォルトゲートウェイ未設定' : 'ゲートウェイに到達不可'}）`);
        if (onSettled) onSettled('failed');
        return;
      }
      const segments = computeNetworkSegments(topology);
      const destSeg = segmentForNode(segments, dstId);
      const flow = startFlow(store, topology, route.path, dstId, destSeg ? destSeg.repId : null, rerender, logFn);
      if (!flow) { if (onSettled) onSettled('failed'); return; }
      flow.onResolved = (state) => {
        if (state === 'done') { if (onSettled) onSettled('done'); return; }
        if (attempt >= MAX_ATTEMPTS) {
          logFn('fail', `送信失敗：${attempt}回再送を試みましたが到達できませんでした`);
          if (onSettled) onSettled('failed');
          return;
        }
        logFn('sys', `約1秒後に再送します（${attempt}/${MAX_ATTEMPTS}回目）`);
        setTimeout(tryAttempt, 1000);
      };
    }
    tryAttempt();
  }

  // 速度スライダー変更時：進行中の区間を、現在の進捗位置から新しい速度で再スケジュールする
  function applyFlowSpeedChange(store) {
    const now = Date.now();
    store.flows.forEach((flow) => {
      if (flow.state !== 'flowing' || !flow.segmentStartedAt) return;
      const elapsed = now - flow.segmentStartedAt;
      const progress = clamp(elapsed / flow.segmentDurationMs, 0, 0.97);
      const newHopMs = HOP_BASE_MS / (store.speedFactor || 1);
      const remaining = newHopMs * (1 - progress);
      clearTimeout(flow.segmentTimer);
      flow.segmentProgressAtRestart = progress;
      flow.segmentStartedAt = now;
      flow.segmentDurationMs = remaining;
      flow.segmentTimer = setTimeout(() => onSegmentComplete(flow), remaining);
      flow.rerender();
    });
  }

  /* ---- 時間経過によるコスト自動変動／自動障害（共通） ---- */

  const DRIFT_INTERVAL_MS = 3000;
  const LOAD_DECAY_PER_TICK = 1;
  const AUTO_RECOVER_MIN_MS = 3000;
  const AUTO_RECOVER_MAX_MS = 6000;

  // link.baseCost（編集された基準値）＋link.load（利用による負荷）から実効コストを再計算する
  function recalcLinkCost(link) {
    const base = link.baseCost != null ? link.baseCost : link.cost;
    link.load = Math.max(0, link.load || 0);
    link.cost = clamp(base + link.load, base, 10);
  }

  // リンクのUP/DOWNはこの関数を通して変更する（自動復帰タイマーの管理を一元化するため）
  function setLinkDownState(store, topology, link, downValue, logFn, rerender) {
    if (downValue && !link.down) {
      link.down = true;
      if (store.autoRecoverEnabled) scheduleAutoRecover(store, topology, link, logFn, rerender);
      if (link.routable) rvTriggerUpdate(topology); // トリガード・アップデート：即座に隣へ伝播
    } else if (!downValue && link.down) {
      link.down = false;
      if (link._recoveryTimer) { clearTimeout(link._recoveryTimer); link._recoveryTimer = null; }
      if (link.routable) rvTriggerUpdate(topology);
    }
  }

  function scheduleAutoRecover(store, topology, link, logFn, rerender) {
    if (link._recoveryTimer) clearTimeout(link._recoveryTimer);
    const wait = AUTO_RECOVER_MIN_MS + Math.random() * (AUTO_RECOVER_MAX_MS - AUTO_RECOVER_MIN_MS);
    link._recoveryTimer = setTimeout(() => {
      link._recoveryTimer = null;
      if (!link.down) return;
      link.down = false;
      const na = topology.nodes.get(link.a), nb = topology.nodes.get(link.b);
      const label = `${na ? na.name : link.a} — ${nb ? nb.name : link.b}`;
      logFn('ok', `${label} が復旧しました（自動復帰）`);
      rerender();
    }, wait);
  }

  function enableAutoRecoverForCurrentDownLinks(store, topology, logFn, rerender) {
    topology.links.forEach((l) => { if (l.down) scheduleAutoRecover(store, topology, l, logFn, rerender); });
  }

  function disableAutoRecoverTimers(topology) {
    topology.links.forEach((l) => { if (l._recoveryTimer) { clearTimeout(l._recoveryTimer); l._recoveryTimer = null; } });
  }

  function driftTick(topology, store, logFn, rerender) {
    const routableLinks = topology.links.filter((l) => l.routable);
    routableLinks.forEach((link) => {
      if (link.down) return; // ダウン中は変動を一時停止
      const failRoll = Math.random() * 100;
      if (failRoll < store.driftFailRate) {
        setLinkDownState(store, topology, link, true, logFn, rerender);
        const na = topology.nodes.get(link.a), nb = topology.nodes.get(link.b);
        const label = `${na ? na.name : link.a} — ${nb ? nb.name : link.b}`;
        logFn('fail', `【時間経過】${label} でリンク障害が発生しました${store.autoRecoverEnabled ? '（自動復帰します）' : '（手動で復旧してください）'}`);
        return;
      }
      // 利用状況（負荷）による自然減衰：3秒ごとに-1、基準値まで下がる
      if ((link.load || 0) > 0) {
        link.load = Math.max(0, link.load - LOAD_DECAY_PER_TICK);
        recalcLinkCost(link);
      }
    });
  }

  function startDriftTimer(topology, store, logFn, rerender) {
    stopDriftTimer(store);
    store.driftTimer = setInterval(() => {
      driftTick(topology, store, logFn, rerender);
      rerender();
    }, DRIFT_INTERVAL_MS);
  }

  function stopDriftTimer(store) {
    if (store.driftTimer) {
      clearInterval(store.driftTimer);
      store.driftTimer = null;
    }
  }

  /* ------------------------------------------------------------------ *
   * 4. ログ出力
   * ------------------------------------------------------------------ */

  function makeLogger(containerEl, badgeEl) {
    return function log(level, msg, delay) {
      const write = () => {
        const line = el('div', 'log-line lv-' + level + ' is-new');
        const t = el('span', 'log-time', nowStamp());
        const m = el('span', 'log-msg', msg);
        line.appendChild(t);
        line.appendChild(m);
        containerEl.appendChild(line);
        containerEl.scrollTop = containerEl.scrollHeight;
        setTimeout(() => line.classList.remove('is-new'), 1150);
        if (badgeEl) {
          badgeEl.textContent = String(containerEl.children.length);
          badgeEl.hidden = false;
        }
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

    const result = computeGatewayRoute(topology, srcId, dstId);
    let t = 0;
    const STEP = 260;

    logFn('sys', `送信開始: ${src.name} (${src.ip || '—'}) → ${dst.name} (${dst.ip || '—'})`, t); t += STEP;

    if (!result.reachable) {
      if (opts.onRouteComputed) opts.onRouteComputed(result);
      const msg = result.error === 'no-gateway' ? 'デフォルトゲートウェイが設定されていません'
        : result.error === 'gateway-unreachable' ? 'デフォルトゲートウェイに到達できません'
        : '到達可能な経路がありません';
      logFn('fail', msg, t);
      if (opts.onFinish) setTimeout(() => opts.onFinish(result), t + 200);
      return;
    }

    if (opts.onRouteComputed) opts.onRouteComputed(result);

    // 送信直後（ARP解決あたり）に自動障害を抽選。ルーター間のリンクすべてが対象。
    if (opts.failRate) {
      const upRoutable = topology.links.filter((l) => l.routable && !l.down);
      if (upRoutable.length && Math.random() * 100 < opts.failRate) {
        const failureLink = upRoutable[Math.floor(Math.random() * upRoutable.length)];
        const failLogDelay = t;
        if (opts.markDown) opts.markDown(failureLink);
        const na = topology.nodes.get(failureLink.a), nb = topology.nodes.get(failureLink.b);
        const label = `${na ? na.name : failureLink.a} — ${nb ? nb.name : failureLink.b}`;
        logFn('fail', `【自動障害】${label} でリンク障害が発生しました`, t); t += STEP;
        if (opts.onLinkDown) setTimeout(() => opts.onLinkDown(), failLogDelay + 40);
      }
    }

    const gw = findRouterByIp(topology, src.gateway);

    logFn('arp', `${src.name}: ARP要求（ブロードキャスト）— デフォルトゲートウェイ ${gw.ip || src.gateway} のMACアドレスは？`, t); t += STEP;
    logFn('arp', `${gw.name}: ARP応答 — MACアドレス ${gw.mac} を通知`, t); t += STEP;

    const sport = randPort();
    logFn('tcp', `${src.name} → ${dst.name} : TCP SYN  (sport=${sport}, dport=80, seq=0)`, t); t += STEP;
    logFn('tcp', `${dst.name} → ${src.name} : TCP SYN-ACK (ack=1, seq=0)`, t); t += STEP;
    logFn('tcp', `${src.name} → ${dst.name} : TCP ACK (ack=1) — コネクション確立`, t); t += STEP;

    logFn('tcp', `TCPセグメント生成: sport=${sport} dport=80 flags=PSH,ACK`, t); t += STEP;
    logFn('ip', `IPパケット生成: src=${src.ip || '-'} dst=${dst.ip || '-'} TTL=${INITIAL_TTL} proto=TCP`, t); t += STEP;
    logFn('frame', `イーサネットフレーム生成: src=${src.mac} dst=${gw.mac} (type=0x0800)`, t); t += STEP;

    logFn('sys', `${gw.name} に到着後は、各ルーターがその時点のルーティングテーブルを見て1ホップずつ中継先を決定します`, t); t += STEP;

    if (opts.onFinish) setTimeout(() => opts.onFinish(result), t + 200);
  }

  /* ------------------------------------------------------------------ *
   * 6. 固定トポロジ モード
   * ------------------------------------------------------------------ */

  const Fixed = {
    topo: makeFixedTopology(),
    svg: null,
    logEl: null,
    logBadge: null,
    rtMode: 'preset',
    failRate: 15,
    hoverNodeId: null,
    flows: [],
    colorIdx: 0,
    driftEnabled: false,
    driftFailRate: 5,
    driftTimer: null,
    openPopoverNodeId: null,
    autoRecoverEnabled: false,
    speedFactor: 1,
    meshEnabled: false,
    lastChosenPath: null,
    nodeErrors: new Map(),
    coldStart: false,
    rvTimer: null
  };

  function fixedValidate() {
    Fixed.nodeErrors = validateTopologyIps(Fixed.topo);
  }

  function fixedHasAnyError() {
    let any = false;
    Fixed.nodeErrors.forEach((v) => { if (v.hasError) any = true; });
    return any;
  }

  function fixedLog(level, msg, delay) {
    makeLogger(Fixed.logEl, Fixed.logBadge)(level, msg, delay);
  }

  function fixedRender() {
    renderTopology(Fixed.svg, Fixed.topo, {
      hoverNodeId: Fixed.hoverNodeId,
      flows: Fixed.flows,
      speedFactor: Fixed.speedFactor,
      errorNodeIds: new Set(Array.from(Fixed.nodeErrors.entries()).filter(([, v]) => v.hasError).map(([k]) => k))
    });
    fixedRenderRouteCompare(Fixed.lastChosenPath);
    fixedRenderRoutingTable();
    fixedUpdateSendButtonState();
    if (Fixed.openPopoverNodeId) {
      const n = Fixed.topo.nodes.get(Fixed.openPopoverNodeId);
      if (n) renderFixedRtPopoverContent(n); else closeFixedRtPopover();
    }
  }

  function fixedUpdateSendButtonState() {
    const btn = document.getElementById('send-btn');
    if (btn) btn.disabled = fixedHasAnyError();
  }

  function fixedRenderRouteCompare(chosenFullPath) {
    const wrap = document.getElementById('route-compare');
    wrap.innerHTML = '';

    if (!Fixed.meshEnabled) {
      const costs = getRouteCosts(Fixed.topo);
      const best = Math.min(...costs.filter((c) => !c.down).map((c) => c.cost), Infinity);
      costs.forEach((c) => {
        const row = el('div', 'route-row');
        const isChosen = chosenFullPath ? chosenFullPath.includes(c.mid) : (!c.down && c.cost === best);
        if (c.down) row.classList.add('is-unavailable');
        else if (isChosen) row.classList.add('is-chosen');
        row.innerHTML = `<span class="route-tag">${c.key}</span>
          <span>RT-S → ${c.mid.toUpperCase()} → RT-R</span>
          <span class="route-cost">${c.down ? '不通' : 'コスト ' + c.cost}</span>`;
        wrap.appendChild(row);
      });
      return;
    }

    // メッシュ有効時：ルーターのみを通る単純経路をすべて列挙し、コスト最小の上位5件（同コストは含める）
    const all = enumerateRouterPaths(Fixed.topo, 'rt-s', 'rt-r');
    all.forEach((p) => { p.effCost = p.down ? Infinity : p.cost; });
    all.sort((a, b) => a.effCost - b.effCost);
    const top = [];
    let cutoff = null;
    for (let i = 0; i < all.length; i++) {
      if (top.length < 5) {
        top.push(all[i]);
        if (top.length === 5) cutoff = all[i].effCost;
      } else if (all[i].effCost === cutoff) {
        top.push(all[i]);
      } else {
        break;
      }
    }
    const chosenRouterPath = chosenFullPath ? extractRouterSubpath(Fixed.topo, chosenFullPath) : null;
    top.forEach((p, idx) => {
      const row = el('div', 'route-row');
      const label = p.path.map((id) => Fixed.topo.nodes.get(id).name).join('→');
      const isChosen = chosenRouterPath && JSON.stringify(chosenRouterPath) === JSON.stringify(p.path);
      if (p.down) row.classList.add('is-unavailable');
      else if (isChosen) row.classList.add('is-chosen');
      row.innerHTML = `<span class="route-tag">${idx + 1}</span>
        <span>${label}</span>
        <span class="route-cost">${p.down ? '不通' : 'コスト ' + p.cost}</span>`;
      wrap.appendChild(row);
    });
    if (top.length === 0) {
      wrap.innerHTML = '<p class="empty-note">RT-SからRT-Rへ到達できる経路がありません。</p>';
    }
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
          <td><input type="number" min="1" max="99" value="${link.baseCost}" data-link-id="${link.id}" class="rt-cost-input" ${manual ? '' : 'disabled'}></td>
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

    if (Fixed.meshEnabled) {
      const meshBox = el('div', 'rt-router');
      let meshRows = '';
      MESH_LINK_DEFS.forEach((md) => {
        const link = Fixed.topo.links.find((l) => l.id === md.id);
        if (!link) return;
        meshRows += `<tr>
          <td>${md.label}</td>
          <td><input type="number" min="1" max="99" value="${link.baseCost}" data-link-id="${link.id}" class="rt-cost-input" ${manual ? '' : 'disabled'}></td>
          <td><button class="btn btn-mini rt-toggle" data-link-id="${link.id}">${link.down ? '<span class="rt-down">DOWN</span>' : 'UP'}</button></td>
        </tr>`;
      });
      meshBox.innerHTML = `<div class="rt-router-name">メッシュ接続</div>
        <table class="rt-tbl">
          <tr><th>区間</th><th>メトリック</th><th>状態</th></tr>
          ${meshRows}
        </table>`;
      wrap.appendChild(meshBox);
    }

    wrap.querySelectorAll('.rt-cost-input').forEach((inp) => {
      inp.addEventListener('change', () => {
        const link = Fixed.topo.links.find((l) => l.id === inp.dataset.linkId);
        const v = clamp(parseInt(inp.value, 10) || 1, 1, 99);
        link.baseCost = v;
        recalcLinkCost(link);
        fixedRender();
      });
    });
    wrap.querySelectorAll('.rt-toggle').forEach((btn) => {
      btn.addEventListener('click', () => {
        const link = Fixed.topo.links.find((l) => l.id === btn.dataset.linkId);
        setLinkDownState(Fixed, Fixed.topo, link, !link.down, fixedLog, fixedRender);
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
      setLinkDownState(Fixed, Fixed.topo, link, !link.down, fixedLog, fixedRender);
      fixedLog('sys', `${link.id.toUpperCase()} を${link.down ? '障害（ダウン）状態に設定' : '復旧'}しました`);
      fixedRender();
      return;
    }

    openCostModal({
      title: 'リンク設定',
      subtitle: `${link.a.toUpperCase()} — ${link.b.toUpperCase()}`,
      initialCost: link.baseCost != null ? link.baseCost : link.cost,
      costEditable: true,
      initialDown: link.down,
      onSave: (cost, down) => {
        link.baseCost = cost;
        recalcLinkCost(link);
        setLinkDownState(Fixed, Fixed.topo, link, down, fixedLog, fixedRender);
        fixedLog('sys', `${link.id.toUpperCase()} を更新しました（コスト=${cost}, 状態=${down ? 'DOWN' : 'UP'}）`);
        fixedRender();
      }
    });
  }

  /* ---- ルーティングテーブル ポップオーバー（クリックしたルーターの経路情報） ---- */

  function fixedRoutingTableHtml(router) {
    const segments = computeNetworkSegments(Fixed.topo);
    const { rows, emptyNote } = computeRoutingTable(Fixed.topo, router.id, segments);
    if (emptyNote && rows.length === 0) {
      return `<p class="popover-note">${emptyNote}</p>`;
    }
    const body = rows.map((r) => `<tr>
        <td>${r.network}</td>
        <td>${r.nextHop}</td>
        <td class="${r.type === 'unreachable' ? 'rt-down' : ''}">${r.metric}</td>
      </tr>`).join('');
    return `<table class="rt-tbl">
      <tr><th>宛先ネットワーク</th><th>ネクストホップ</th><th>メトリック</th></tr>
      ${body}
    </table>`;
  }

  function renderFixedRtPopoverContent(node) {
    const pop = document.getElementById('fixed-rt-popover');
    const errRec = Fixed.nodeErrors.get(node.id) || { self: {}, ifaces: {} };

    let ipSection = '<div class="popover-section-title">IPアドレス設定</div>';
    if (node.ip) {
      // RT-S / RT-R のPC側インタフェースは固定（編集不可）
      ipSection += popoverIfaceBlockHtml('PC側インタフェース', node.ip, '/24', null, 'top', false);
    }
    const linkIds = Object.keys(node.ifaces || {});
    ipSection += linkIds.map((linkId) => {
      const link = Fixed.topo.links.find((l) => l.id === linkId);
      const otherId = link ? (link.a === node.id ? link.b : link.a) : null;
      const other = otherId ? Fixed.topo.nodes.get(otherId) : null;
      const label = `→ ${other ? other.name : '?'} 側`;
      const iface = node.ifaces[linkId];
      return popoverIfaceBlockHtml(label, iface.ip, iface.mask, errRec.ifaces[linkId], linkId, true);
    }).join('');

    pop.innerHTML = `<div class="ip-popover-title"><span>${node.name} の設定</span><button type="button" class="ip-popover-close" id="fixed-rt-popover-close">×</button></div>
      ${ipSection}
      <div class="popover-section-title">ルーティングテーブル</div>
      ${fixedRoutingTableHtml(node)}`;

    pop.querySelectorAll('.ip-field, .mask-input').forEach((input) => {
      input.addEventListener('input', () => {
        const key = input.dataset.key, field = input.dataset.field;
        if (!node.ifaces[key]) node.ifaces[key] = { ip: '', mask: '' };
        if (field === 'ip') node.ifaces[key].ip = input.value; else node.ifaces[key].mask = input.value;
        fixedValidate();
        renderTopology(Fixed.svg, Fixed.topo, {
          hoverNodeId: Fixed.hoverNodeId,
          flows: Fixed.flows,
          speedFactor: Fixed.speedFactor,
          errorNodeIds: new Set(Array.from(Fixed.nodeErrors.entries()).filter(([, v]) => v.hasError).map(([k]) => k))
        });
        fixedUpdateSendButtonState();
      });
    });
    document.getElementById('fixed-rt-popover-close').addEventListener('click', closeFixedRtPopover);
  }

  function positionFixedRtPopover(node) {
    const pop = document.getElementById('fixed-rt-popover');
    const wrap = Fixed.svg.closest('.stage-canvas-wrap');
    if (!node || !wrap) return;
    const pt = Fixed.svg.createSVGPoint();
    pt.x = node.x; pt.y = node.y;
    const ctm = Fixed.svg.getScreenCTM();
    if (!ctm) return;
    const screenPt = pt.matrixTransform(ctm);
    const wrapRect = wrap.getBoundingClientRect();
    let left = screenPt.x - wrapRect.left + 36;
    let top = screenPt.y - wrapRect.top - 20;
    left = clamp(left, 8, wrapRect.width - 280);
    top = clamp(top, 8, wrapRect.height - 20);
    pop.style.left = left + 'px';
    pop.style.top = top + 'px';
  }

  function openFixedRtPopover(nodeId) {
    const node = Fixed.topo.nodes.get(nodeId);
    if (!node) return;
    Fixed.openPopoverNodeId = nodeId;
    renderFixedRtPopoverContent(node);
    positionFixedRtPopover(node);
    document.getElementById('fixed-rt-popover').classList.remove('is-hidden');
  }

  function closeFixedRtPopover() {
    Fixed.openPopoverNodeId = null;
    document.getElementById('fixed-rt-popover').classList.add('is-hidden');
  }

  function fixedSend() {
    const srcId = document.getElementById('src-pc').value;
    const dstId = document.getElementById('dst-pc').value;
    const statusEl = document.getElementById('send-status');
    if (srcId === dstId) {
      statusEl.textContent = '送信元と宛先が同じです。別のPCを選択してください。';
      return;
    }
    if (fixedHasAnyError()) {
      statusEl.textContent = 'IPアドレス設定にエラーがあるため送信できません。';
      return;
    }
    statusEl.textContent = '送信中…';

    const sendOpts = {
      failRate: Fixed.failRate,
      markDown: (link) => setLinkDownState(Fixed, Fixed.topo, link, true, fixedLog, fixedRender),
      onLinkDown: () => fixedRender(),
      onRouteComputed: (result) => {
        fixedRenderRouteCompare();
        if (result.reachable) {
          startDeliverySession(Fixed, Fixed.topo, srcId, dstId, fixedRender, fixedLog, (state) => {
            statusEl.textContent = state === 'done' ? '送信完了' : '送信失敗（不通）';
          });
        } else {
          statusEl.textContent = '送信失敗（不通）';
          fixedRender();
        }
      },
      onFinish: () => { /* 実際の到達可否はフローの解決時に statusEl を更新する */ }
    };
    simulateSend(Fixed.topo, srcId, dstId, fixedLog, Fixed.svg, sendOpts);
  }

  function initFixedMode() {
    Fixed.svg = document.getElementById('topo-svg');
    Fixed.logEl = document.getElementById('log');
    Fixed.logBadge = document.getElementById('log-badge');
    fixedPopulateSelects();
    fixedValidate();
    rvInitTables(Fixed.topo, computeNetworkSegments(Fixed.topo), Fixed.coldStart);
    startRvTimer(Fixed, Fixed.topo, fixedRender);
    fixedRender();

    Fixed.svg.addEventListener('click', (e) => {
      const nodeTarget = e.target.closest('[data-node-id]');
      if (nodeTarget) {
        const node = Fixed.topo.nodes.get(nodeTarget.dataset.nodeId);
        if (node && node.type === 'router') {
          if (Fixed.openPopoverNodeId === node.id) { closeFixedRtPopover(); } else { openFixedRtPopover(node.id); }
        }
        return;
      }
      const linkTarget = e.target.closest('[data-link-id]');
      if (linkTarget) { fixedOpenLinkModal(linkTarget.dataset.linkId); return; }
    });
    // 右クリックでも常にルーティングテーブルを確認できるようにする（左クリックの挙動は変更しない）
    Fixed.svg.addEventListener('contextmenu', (e) => {
      const nodeTarget = e.target.closest('[data-node-id]');
      if (!nodeTarget) return;
      const node = Fixed.topo.nodes.get(nodeTarget.dataset.nodeId);
      if (!node || node.type !== 'router') return;
      e.preventDefault();
      openFixedRtPopover(node.id);
    });
    document.addEventListener('click', (e) => {
      if (!Fixed.openPopoverNodeId) return;
      const popover = document.getElementById('fixed-rt-popover');
      if (popover.contains(e.target)) return;
      if (e.target.closest('[data-node-id]')) return;
      closeFixedRtPopover();
    });
    Fixed.svg.addEventListener('mousemove', (e) => {
      const nodeTarget = e.target.closest('[data-node-id]');
      const id = nodeTarget ? nodeTarget.dataset.nodeId : null;
      if (id !== Fixed.hoverNodeId) { Fixed.hoverNodeId = id; fixedRender(); }
    });

    document.getElementById('send-btn').addEventListener('click', fixedSend);
    document.getElementById('clear-log').addEventListener('click', () => {
      Fixed.logEl.innerHTML = '';
      Fixed.logBadge.hidden = true;
      Fixed.logBadge.textContent = '0';
    });

    document.getElementById('rt-mode').addEventListener('change', (e) => {
      Fixed.rtMode = e.target.value;
      if (Fixed.rtMode === 'preset') {
        Object.keys(PRESET_COSTS).forEach((linkId) => {
          const link = Fixed.topo.links.find((l) => l.id === linkId);
          if (link) { link.baseCost = PRESET_COSTS[linkId]; link.load = 0; recalcLinkCost(link); }
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
      Fixed.topo.links.forEach((l) => { setLinkDownState(Fixed, Fixed.topo, l, false, fixedLog, fixedRender); });
      Fixed.flows = [];
      fixedLog('sys', 'すべてのリンクを復旧し、経路のハイライトをリセットしました');
      fixedRender();
    });

    document.getElementById('drift-toggle').addEventListener('change', (e) => {
      Fixed.driftEnabled = e.target.checked;
      if (Fixed.driftEnabled) {
        startDriftTimer(Fixed.topo, Fixed, fixedLog, fixedRender);
        fixedLog('sys', '時間経過によるコスト自動変動を有効にしました');
      } else {
        stopDriftTimer(Fixed);
        fixedLog('sys', '時間経過によるコスト自動変動を停止しました');
      }
    });
    document.getElementById('drift-fail-rate').addEventListener('input', (e) => {
      Fixed.driftFailRate = clamp(parseInt(e.target.value, 10) || 0, 0, 100);
    });

    document.getElementById('auto-recover-toggle').addEventListener('change', (e) => {
      Fixed.autoRecoverEnabled = e.target.checked;
      if (Fixed.autoRecoverEnabled) {
        enableAutoRecoverForCurrentDownLinks(Fixed, Fixed.topo, fixedLog, fixedRender);
        fixedLog('sys', '障害の自動復帰（3〜6秒）を有効にしました');
      } else {
        disableAutoRecoverTimers(Fixed.topo);
        fixedLog('sys', '障害の自動復帰を停止しました（今後は手動復旧のみ）');
      }
    });

    const flowSpeedInput = document.getElementById('flow-speed');
    const flowSpeedOut = document.getElementById('flow-speed-out');
    flowSpeedInput.addEventListener('input', () => {
      Fixed.speedFactor = parseFloat(flowSpeedInput.value) || 1;
      flowSpeedOut.textContent = Fixed.speedFactor.toFixed(1) + 'x';
      applyFlowSpeedChange(Fixed);
      fixedRender();
    });

    document.getElementById('mesh-toggle').addEventListener('change', (e) => {
      Fixed.meshEnabled = e.target.checked;
      if (Fixed.meshEnabled) {
        addMeshLinks(Fixed.topo);
        fixedLog('sys', 'メッシュ接続（RT-A—RT-B, RT-B—RT-C）を有効にしました');
      } else {
        removeMeshLinks(Fixed.topo);
        fixedLog('sys', 'メッシュ接続を無効にしました（RT-A—RT-B, RT-B—RT-Cは経路計算・表示から除外されます）');
      }
      fixedValidate();
      rvTriggerUpdate(Fixed.topo);
      fixedRender();
    });

    document.getElementById('coldstart-toggle').addEventListener('change', (e) => {
      Fixed.coldStart = e.target.checked;
      rvInitTables(Fixed.topo, computeNetworkSegments(Fixed.topo), Fixed.coldStart);
      fixedLog('sys', Fixed.coldStart
        ? '各ルーターのテーブルを空にしました。ここから収束していく様子を観察できます'
        : '各ルーターのテーブルに直結情報を再度仕込みました');
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
    logBadge: null,
    interactionMode: 'move',
    linkFirstPick: null,
    hoverNodeId: null,
    typeCounters: { pc: 0, switch: 0, router: 0 },
    placeCursor: { x: 140, y: 120 },
    dragging: null,
    flows: [],
    colorIdx: 0,
    ifaceCounter: 0,
    openPopoverNodeId: null,
    nodeErrors: new Map(),
    driftEnabled: false,
    driftFailRate: 5,
    driftTimer: null,
    failRate: 15,
    autoRecoverEnabled: false,
    speedFactor: 1,
    undoStack: [],
    redoStack: [],
    coldStart: false,
    rvTimer: null
  };

  function freeLog(level, msg, delay) { makeLogger(Free.logEl, Free.logBadge)(level, msg, delay); }

  const FREE_TYPE_LABEL = { pc: 'PC', switch: 'SW', router: 'RT' };

  /* ---- IPアドレス／サブネット整合性チェック（自由配置） ---- */

  function freeBuildClusters(topo) {
    // 現実のルーターと同じ挙動：どのリンクも、その両端は同じサブネットに属する必要がある
    const uf = createUnionFind();
    topo.nodes.forEach((n) => { if (n.type !== 'router') uf.find(n.id); });
    topo.links.forEach((l) => {
      const na = topo.nodes.get(l.a), nb = topo.nodes.get(l.b);
      if (!na || !nb) return;
      const keyA = na.type === 'router' ? `${na.id}::${l.id}` : na.id;
      const keyB = nb.type === 'router' ? `${nb.id}::${l.id}` : nb.id;
      uf.union(keyA, keyB);
    });
    return uf;
  }

  function freeResolveEntry(topo, key) {
    if (key.includes('::')) {
      const idx = key.indexOf('::');
      const routerId = key.slice(0, idx), linkId = key.slice(idx + 2);
      const r = topo.nodes.get(routerId);
      const iface = r && r.ifaces && r.ifaces[linkId];
      if (!iface) return null;
      return { ip: iface.ip, mask: iface.mask, ownerNodeId: routerId, ifaceKey: linkId };
    }
    const n = topo.nodes.get(key);
    if (n && n.type === 'pc') return { ip: n.ip, mask: n.mask, ownerNodeId: key, ifaceKey: null };
    return null; // スイッチはIPを持たない
  }

  function freeMarkError(errorMap, entry, kind) {
    if (!entry) return;
    const nodeId = entry.ownerNodeId;
    if (!errorMap.has(nodeId)) errorMap.set(nodeId, { hasError: false, self: {}, ifaces: {} });
    const rec = errorMap.get(nodeId);
    rec.hasError = true;
    const target = entry.ifaceKey ? (rec.ifaces[entry.ifaceKey] || (rec.ifaces[entry.ifaceKey] = {})) : rec.self;
    target[kind] = true;
  }

  // ネットワークアドレス／ブロードキャストアドレスをホストIPとして使っていないか判定
  function isReservedHostAddress(ip, mask) {
    const ipInt = parseIp(ip);
    const prefix = parseMaskToPrefix(mask);
    if (ipInt === null || prefix === null) return false;
    if (prefix >= 31) return false; // /31, /32はホスト部の特例のため対象外
    const maskBits = prefix === 0 ? 0 : (0xFFFFFFFF << (32 - prefix)) >>> 0;
    const hostBits = (~maskBits) >>> 0;
    const hostPart = (ipInt & hostBits) >>> 0;
    return hostPart === 0 || hostPart === hostBits;
  }

  // 任意のトポロジ（固定／自由配置どちらも）に対してIP設定を検証する共通ロジック
  function validateTopologyIps(topo) {
    const errorMap = new Map();
    topo.nodes.forEach((n) => { errorMap.set(n.id, { hasError: false, self: {}, ifaces: {} }); });

    const entries = [];
    topo.nodes.forEach((n) => {
      if (n.type === 'pc') {
        entries.push({ ip: n.ip, mask: n.mask, ownerNodeId: n.id, ifaceKey: null });
      } else if (n.type === 'router') {
        Object.keys(n.ifaces || {}).forEach((linkId) => {
          const iface = n.ifaces[linkId];
          entries.push({ ip: iface.ip, mask: iface.mask, ownerNodeId: n.id, ifaceKey: linkId });
        });
      }
    });

    entries.forEach((e) => {
      e.formatOk = isValidIpFormat(e.ip) && isValidMaskFormat(e.mask);
      if (!e.formatOk) { freeMarkError(errorMap, e, 'format'); }
      else if (isReservedHostAddress(e.ip, e.mask)) { freeMarkError(errorMap, e, 'reserved'); }
    });

    const byIp = new Map();
    entries.forEach((e) => {
      const key = (e.ip || '').trim();
      if (!key) return;
      if (!byIp.has(key)) byIp.set(key, []);
      byIp.get(key).push(e);
    });
    byIp.forEach((list) => {
      if (list.length > 1) list.forEach((e) => freeMarkError(errorMap, e, 'dup'));
    });

    // サブネット整合性チェック（同一リンクの両端は必ず同じサブネット）
    const uf = freeBuildClusters(topo);
    const clusters = new Map();
    uf.keys().forEach((key) => {
      const root = uf.find(key);
      if (!clusters.has(root)) clusters.set(root, []);
      clusters.get(root).push(key);
    });
    clusters.forEach((keys) => {
      const resolved = keys
        .map((k) => ({ key: k, entry: freeResolveEntry(topo, k) }))
        .filter((r) => r.entry && isValidIpFormat(r.entry.ip) && isValidMaskFormat(r.entry.mask));
      if (resolved.length < 2) return;
      const tally = new Map();
      resolved.forEach((r) => {
        const nk = networkKey(r.entry.ip, parseMaskToPrefix(r.entry.mask));
        tally.set(nk, (tally.get(nk) || 0) + 1);
      });
      let majorityNet = null, majorityCount = -1;
      tally.forEach((count, nk) => { if (count > majorityCount) { majorityCount = count; majorityNet = nk; } });
      resolved.forEach((r) => {
        const nk = networkKey(r.entry.ip, parseMaskToPrefix(r.entry.mask));
        if (nk !== majorityNet) freeMarkError(errorMap, r.entry, 'subnet');
      });
    });

    // デフォルトゲートウェイの検証（PCのみ）：未設定／書式不正／実在しないインタフェース／別セグメント
    topo.nodes.forEach((n) => {
      if (n.type !== 'pc') return;
      const rec = errorMap.get(n.id);
      const gw = n.gateway;
      if (!gw) { rec.hasError = true; rec.gateway = { missing: true }; return; }
      if (!isValidIpFormat(gw)) { rec.hasError = true; rec.gateway = { format: true }; return; }
      let matchedTopLevel = false, matchedIfaceKey = null;
      topo.nodes.forEach((rn) => {
        if (rn.type !== 'router') return;
        if (rn.ip === gw) matchedTopLevel = true;
        if (rn.ifaces) {
          Object.keys(rn.ifaces).forEach((linkId) => {
            if (rn.ifaces[linkId].ip === gw) matchedIfaceKey = `${rn.id}::${linkId}`;
          });
        }
      });
      if (!matchedTopLevel && !matchedIfaceKey) { rec.hasError = true; rec.gateway = { unreachable: true }; return; }
      if (matchedIfaceKey && uf.find(matchedIfaceKey) !== uf.find(n.id)) {
        rec.hasError = true; rec.gateway = { subnet: true };
      }
    });

    return errorMap;
  }

  function freeValidate() {
    Free.nodeErrors = validateTopologyIps(Free.topo);
  }

  function freeHasAnyError() {
    let any = false;
    Free.nodeErrors.forEach((v) => { if (v.hasError) any = true; });
    return any;
  }

  function freeUpdateSendButtonState() {
    const btn = document.getElementById('free-send-btn');
    const statusEl = document.getElementById('free-send-status');
    const hasError = freeHasAnyError();
    btn.disabled = hasError;
    if (hasError && !statusEl.textContent) statusEl.textContent = 'IPアドレス設定にエラーがあるため送信できません。';
    if (!hasError && statusEl.textContent === 'IPアドレス設定にエラーがあるため送信できません。') statusEl.textContent = '';
  }

  function freeRevalidateAndRender() {
    freeValidate();
    freeRender();
    freeUpdateSendButtonState();
  }

  /* ---- IP編集ポップオーバー ---- */

  function svgToScreen(svgEl, x, y) {
    const pt = svgEl.createSVGPoint();
    pt.x = x; pt.y = y;
    const ctm = svgEl.getScreenCTM();
    if (!ctm) return { x: 0, y: 0 };
    return pt.matrixTransform(ctm);
  }

  function positionIpPopover(node) {
    const pop = document.getElementById('ip-popover');
    const wrap = Free.svg.closest('.stage-canvas-wrap');
    if (!node || !wrap) return;
    const screenPt = svgToScreen(Free.svg, node.x, node.y);
    const wrapRect = wrap.getBoundingClientRect();
    let left = screenPt.x - wrapRect.left + 36;
    let top = screenPt.y - wrapRect.top - 20;
    left = clamp(left, 8, wrapRect.width - 280);
    top = clamp(top, 8, wrapRect.height - 20);
    pop.style.left = left + 'px';
    pop.style.top = top + 'px';
  }

  // IPポップオーバー共通ヘルパー（固定トポロジ・自由配置の両方で使用）
  function popoverFieldErrorText(errObj) {
    if (!errObj) return '';
    if (errObj.format) return '書式が正しくありません（例: 192.168.1.1 と /24 または 255.255.255.0）';
    if (errObj.reserved) return 'ネットワークアドレス／ブロードキャストアドレスはホストIPに使用できません';
    if (errObj.dup) return 'このIPアドレスは他のノードと重複しています';
    if (errObj.subnet) return '接続関係から見てサブネットが不整合です';
    return '';
  }

  function popoverIfaceBlockHtml(label, ip, mask, errObj, dataKey, editable) {
    const hasErr = errObj && (errObj.format || errObj.reserved || errObj.dup || errObj.subnet);
    if (!editable) {
      return `<div class="iface-block">
        <div class="iface-label">${label}（固定）</div>
        <div class="iface-row"><span class="iface-fixed-value">${ip || ''} ${mask || ''}</span></div>
      </div>`;
    }
    return `<div class="iface-block">
      <div class="iface-label">${label}</div>
      <div class="iface-row">
        <input type="text" class="ip-field ${hasErr ? 'has-error' : ''}" data-key="${dataKey}" data-field="ip" value="${ip || ''}" placeholder="192.168.1.1">
        <input type="text" class="mask-input ${hasErr ? 'has-error' : ''}" data-key="${dataKey}" data-field="mask" value="${mask || ''}" placeholder="/24">
      </div>
      <div class="iface-error-msg">${popoverFieldErrorText(errObj)}</div>
    </div>`;
  }

  function gatewayFieldErrorText(errObj) {
    if (!errObj) return '';
    if (errObj.missing) return 'デフォルトゲートウェイが未設定です';
    if (errObj.format) return 'IPアドレスの書式が正しくありません';
    if (errObj.unreachable) return 'そのIPを持つルーターのインタフェースが存在しません';
    if (errObj.subnet) return 'このPCと同じセグメント内のルーターではありません';
    return '';
  }

  function popoverGatewayBlockHtml(gateway, errObj, editable) {
    if (!editable) {
      return `<div class="iface-block">
        <div class="iface-label">デフォルトゲートウェイ（固定）</div>
        <div class="iface-row"><span class="iface-fixed-value">${gateway || ''}</span></div>
      </div>`;
    }
    const hasErr = !!errObj;
    return `<div class="iface-block">
      <div class="iface-label">デフォルトゲートウェイ</div>
      <div class="iface-row">
        <input type="text" class="ip-field gateway-field ${hasErr ? 'has-error' : ''}" data-key="gateway" data-field="gateway" value="${gateway || ''}" placeholder="192.168.1.1">
      </div>
      <div class="iface-error-msg">${gatewayFieldErrorText(errObj)}</div>
    </div>`;
  }

  function renderIpPopoverContent(node) {
    const pop = document.getElementById('ip-popover');
    if (!node) return;
    const errRec = Free.nodeErrors.get(node.id) || { self: {}, ifaces: {} };

    let body = '';
    if (node.type === 'pc') {
      body = `<div class="popover-section-title">IPアドレス設定</div>` +
        popoverIfaceBlockHtml('IPアドレス／マスク', node.ip, node.mask, errRec.self, 'self', true) +
        popoverGatewayBlockHtml(node.gateway, errRec.gateway, true);
    } else if (node.type === 'router') {
      const linkIds = Object.keys(node.ifaces || {});
      if (linkIds.length === 0) {
        body = '<div class="popover-section-title">IPアドレス設定</div><p class="iface-empty">まだリンクが接続されていません。</p>';
      } else {
        body = '<div class="popover-section-title">IPアドレス設定</div>' + linkIds.map((linkId) => {
          const link = Free.topo.links.find((l) => l.id === linkId);
          const otherId = link ? (link.a === node.id ? link.b : link.a) : null;
          const other = otherId ? Free.topo.nodes.get(otherId) : null;
          const label = `→ ${other ? other.name : '?'} 側`;
          const iface = node.ifaces[linkId];
          return popoverIfaceBlockHtml(label, iface.ip, iface.mask, errRec.ifaces[linkId], linkId, true);
        }).join('');
      }
      const segments = computeNetworkSegments(Free.topo);
      const { rows, emptyNote } = computeRoutingTable(Free.topo, node.id, segments);
      let rtHtml;
      if (emptyNote && rows.length === 0) {
        rtHtml = `<p class="popover-note">${emptyNote}</p>`;
      } else {
        const trs = rows.map((r) => `<tr>
            <td>${r.network}</td>
            <td>${r.nextHop}</td>
            <td class="${r.type === 'unreachable' ? 'rt-down' : ''}">${r.metric}</td>
          </tr>`).join('');
        rtHtml = `<table class="rt-tbl">
          <tr><th>宛先ネットワーク</th><th>ネクストホップ</th><th>メトリック</th></tr>
          ${trs}
        </table>`;
      }
      body += `<div class="popover-section-title">ルーティングテーブル</div>${rtHtml}`;
    }

    pop.innerHTML = `<div class="ip-popover-title"><span>${node.name} の設定</span><button type="button" class="ip-popover-close" id="ip-popover-close">×</button></div>${body}`;

    pop.querySelectorAll('.ip-field, .mask-input').forEach((input) => {
      input.addEventListener('focus', () => { freePushUndo(); });
      input.addEventListener('input', () => {
        const key = input.dataset.key, field = input.dataset.field;
        if (field === 'gateway') {
          node.gateway = input.value;
        } else if (node.type === 'pc') {
          if (field === 'ip') node.ip = input.value; else node.mask = input.value;
        } else if (node.type === 'router') {
          if (!node.ifaces[key]) node.ifaces[key] = { ip: '', mask: '' };
          if (field === 'ip') node.ifaces[key].ip = input.value; else node.ifaces[key].mask = input.value;
        }
        freeValidate();
        freeRenderSvg();
        freeUpdateSendButtonState();
        refreshIpPopoverFieldStyles(node);
      });
    });
    document.getElementById('ip-popover-close').addEventListener('click', closeIpPopover);
  }

  function refreshIpPopoverFieldStyles(node) {
    const pop = document.getElementById('ip-popover');
    const errRec = Free.nodeErrors.get(node.id) || { self: {}, ifaces: {} };
    pop.querySelectorAll('.ip-field, .mask-input').forEach((input) => {
      const key = input.dataset.key;
      const errObj = key === 'gateway' ? errRec.gateway : (key === 'self' ? errRec.self : errRec.ifaces[key]);
      const hasErr = key === 'gateway' ? !!errObj : (errObj && (errObj.format || errObj.reserved || errObj.dup || errObj.subnet));
      input.classList.toggle('has-error', !!hasErr);
      const msgEl = input.closest('.iface-block').querySelector('.iface-error-msg');
      if (msgEl) msgEl.textContent = key === 'gateway' ? gatewayFieldErrorText(errObj) : popoverFieldErrorText(errObj);
    });
  }

  function openIpPopover(nodeId) {
    const node = Free.topo.nodes.get(nodeId);
    if (!node) return;
    Free.openPopoverNodeId = nodeId;
    renderIpPopoverContent(node);
    positionIpPopover(node);
    document.getElementById('ip-popover').classList.remove('is-hidden');
    freeRender();
  }

  function closeIpPopover() {
    Free.openPopoverNodeId = null;
    document.getElementById('ip-popover').classList.add('is-hidden');
  }

  /* ---- 元に戻す／やり直す（Undo/Redo） ---- */

  function freeSnapshot() {
    return {
      nodes: Array.from(Free.topo.nodes.entries()).map(([id, n]) => [id, JSON.parse(JSON.stringify(n))]),
      links: Free.topo.links.map((l) => {
        const copy = Object.assign({}, l);
        delete copy._recoveryTimer;
        return JSON.parse(JSON.stringify(copy));
      }),
      typeCounters: Object.assign({}, Free.typeCounters),
      ifaceCounter: Free.ifaceCounter
    };
  }

  function freeRestoreSnapshot(snap) {
    Free.topo.links.forEach((l) => { if (l._recoveryTimer) { clearTimeout(l._recoveryTimer); l._recoveryTimer = null; } });
    Free.topo.nodes = new Map(snap.nodes.map(([id, n]) => [id, JSON.parse(JSON.stringify(n))]));
    Free.topo.links = snap.links.map((l) => JSON.parse(JSON.stringify(l)));
    Free.typeCounters = Object.assign({}, snap.typeCounters);
    Free.ifaceCounter = snap.ifaceCounter;
    if (Free.openPopoverNodeId && !Free.topo.nodes.has(Free.openPopoverNodeId)) closeIpPopover();
    freeRevalidateAndRender();
    freePopulateSelects();
  }

  // ノード／リンク／IP設定／コストなどの「実質的な変更」の直前に呼ぶ
  function freePushUndo() {
    Free.undoStack.push(freeSnapshot());
    if (Free.undoStack.length > 50) Free.undoStack.shift();
    Free.redoStack = [];
    freeUpdateUndoRedoButtons();
  }

  function freeUndo() {
    if (!Free.undoStack.length) return;
    const cur = freeSnapshot();
    const prev = Free.undoStack.pop();
    Free.redoStack.push(cur);
    freeRestoreSnapshot(prev);
    freeLog('sys', '元に戻しました');
    freeUpdateUndoRedoButtons();
  }

  function freeRedo() {
    if (!Free.redoStack.length) return;
    const cur = freeSnapshot();
    const next = Free.redoStack.pop();
    Free.undoStack.push(cur);
    freeRestoreSnapshot(next);
    freeLog('sys', 'やり直しました');
    freeUpdateUndoRedoButtons();
  }

  function freeUpdateUndoRedoButtons() {
    const undoBtn = document.getElementById('free-undo');
    const redoBtn = document.getElementById('free-redo');
    if (undoBtn) undoBtn.disabled = Free.undoStack.length === 0;
    if (redoBtn) redoBtn.disabled = Free.redoStack.length === 0;
  }

  function freeAddNode(type) {
    freePushUndo();
    Free.typeCounters[type] += 1;
    const n = Free.typeCounters[type];
    const id = uid('f' + type);
    const name = `${FREE_TYPE_LABEL[type]}-${n}`;
    const mac = randMac();
    const node = { id, type, name, mac, x: 0, y: 0 };
    if (type === 'pc') {
      node.ip = `10.20.0.${n}`;
      node.mask = '/24';
      node.gateway = '';
    } else if (type === 'router') {
      node.ifaces = {}; // linkId -> {ip, mask}
    }
    // カスケード配置（重なり回避の簡易ロジック）
    const cols = 6;
    const idx = Free.topo.nodes.size;
    node.x = 140 + (idx % cols) * 160;
    node.y = 100 + Math.floor(idx / cols) * 150;
    Free.topo.nodes.set(id, node);
    freeRevalidateAndRender();
    freePopulateSelects();
    freeLog('sys', `${name} を追加しました`);
  }

  function freeRenderSvg() {
    renderTopology(Free.svg, Free.topo, {
      freeMode: true,
      hoverNodeId: Free.hoverNodeId,
      selectedNodeId: Free.linkFirstPick,
      flows: Free.flows,
      speedFactor: Free.speedFactor,
      errorNodeIds: new Set(Array.from(Free.nodeErrors.entries()).filter(([, v]) => v.hasError).map(([k]) => k))
    });
  }

  function freeRender() {
    freeRenderSvg();
    if (Free.openPopoverNodeId) {
      const n = Free.topo.nodes.get(Free.openPopoverNodeId);
      if (n) renderIpPopoverContent(n); else closeIpPopover();
    }
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
    closeIpPopover();
    document.querySelectorAll('#panel-free [data-mode]').forEach((b) => {
      b.classList.toggle('is-active', b.dataset.mode === mode);
    });
    const hint = document.getElementById('free-hint');
    if (mode === 'move') hint.textContent = 'ノードをドラッグして移動できます。PC／ルーターをクリックするとIP設定を編集できます。';
    if (mode === 'link') hint.textContent = '「接続」モードで2つのノードを順にクリックするとリンクを作成します（ルーターは最大4本まで）。';
    if (mode === 'delete') hint.textContent = '「削除」モードでノードまたはリンクをクリックすると削除します。';
    freeRender();
  }

  function freeFindSegmentPcFor(switchId) {
    const links = Free.topo.links.filter((l) => l.a === switchId || l.b === switchId);
    for (const l of links) {
      const otherId = l.a === switchId ? l.b : l.a;
      const n = Free.topo.nodes.get(otherId);
      if (n && n.type === 'pc' && isValidIpFormat(n.ip) && isValidMaskFormat(n.mask)) return n;
    }
    return null;
  }

  function freeHostIpNear(refIp, refMask) {
    const prefix = parseMaskToPrefix(refMask);
    const ipInt = parseIp(refIp);
    const maskBits = prefix === 0 ? 0 : (0xFFFFFFFF << (32 - prefix)) >>> 0;
    const netInt = (ipInt & maskBits) >>> 0;
    const lastOctet = ipInt & 0xFF;
    const hostInt = (netInt + (lastOctet === 250 ? 251 : 250)) >>> 0;
    return intToIp(hostInt);
  }

  // 新規ルーターインタフェースの初期IPを、接続先に合わせて自動設定する
  // （現実のルーターと同様、直結でも同じサブネットが必要なため）
  function freeAssignDefaultIface(routerNode, linkId, otherNode) {
    if (otherNode.type === 'pc' && isValidIpFormat(otherNode.ip) && isValidMaskFormat(otherNode.mask)) {
      routerNode.ifaces[linkId] = { ip: freeHostIpNear(otherNode.ip, otherNode.mask), mask: otherNode.mask };
      return;
    }
    if (otherNode.type === 'switch') {
      const match = freeFindSegmentPcFor(otherNode.id);
      if (match) {
        routerNode.ifaces[linkId] = { ip: freeHostIpNear(match.ip, match.mask), mask: match.mask };
        return;
      }
    }
    Free.ifaceCounter += 1;
    routerNode.ifaces[linkId] = { ip: `10.90.${Free.ifaceCounter}.1`, mask: '/24' };
  }

  function freeLinkCountForNode(nodeId) {
    return Free.topo.links.filter((l) => l.a === nodeId || l.b === nodeId).length;
  }

  function freeRemoveLinkIfaces(link) {
    [link.a, link.b].forEach((nid) => {
      const n = Free.topo.nodes.get(nid);
      if (n && n.type === 'router' && n.ifaces) delete n.ifaces[link.id];
    });
  }

  function freeHandleNodeClick(nodeId) {
    if (Free.interactionMode === 'move') {
      const n = Free.topo.nodes.get(nodeId);
      if (!n || n.type === 'switch') return;
      if (Free.openPopoverNodeId === nodeId) { closeIpPopover(); freeRender(); return; }
      openIpPopover(nodeId);
      return;
    }
    if (Free.interactionMode === 'delete') {
      freePushUndo();
      const linksToRemove = Free.topo.links.filter((l) => l.a === nodeId || l.b === nodeId);
      linksToRemove.forEach(freeRemoveLinkIfaces);
      Free.topo.links = Free.topo.links.filter((l) => l.a !== nodeId && l.b !== nodeId);
      const n = Free.topo.nodes.get(nodeId);
      Free.topo.nodes.delete(nodeId);
      if (Free.openPopoverNodeId === nodeId) closeIpPopover();
      freeLog('sys', `${n ? n.name : nodeId} を削除しました`);
      freeRevalidateAndRender();
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
      if ((nodeA.type === 'router' && freeLinkCountForNode(a) >= 4) ||
          (nodeB.type === 'router' && freeLinkCountForNode(b) >= 4)) {
        freeLog('fail', 'ルーターは最大4本までしか接続できません（接続を中止しました）');
        freeRender();
        return;
      }
      const routable = nodeA.type === 'router' || nodeB.type === 'router';
      openCostModal({
        title: '新しいリンク',
        subtitle: `${nodeA.name} — ${nodeB.name}`,
        initialCost: 1,
        costEditable: routable,
        initialDown: false,
        onSave: (cost, down) => {
          freePushUndo();
          const id = uid('fl');
          const link = { id, a, b, cost: routable ? cost : 0, baseCost: routable ? cost : 0, load: 0, down, routable };
          Free.topo.links.push(link);
          if (nodeA.type === 'router' && nodeB.type === 'router') {
            // ルーター同士は新しい共通サブネットを生成し、両端を同じサブネットにする
            Free.ifaceCounter += 1;
            const net = `10.91.${Free.ifaceCounter}`;
            nodeA.ifaces[id] = { ip: `${net}.1`, mask: '/30' };
            nodeB.ifaces[id] = { ip: `${net}.2`, mask: '/30' };
          } else {
            if (nodeA.type === 'router') freeAssignDefaultIface(nodeA, id, nodeB);
            if (nodeB.type === 'router') freeAssignDefaultIface(nodeB, id, nodeA);
          }
          if (down && Free.autoRecoverEnabled) scheduleAutoRecover(Free, Free.topo, link, freeLog, freeRender);
          freeLog('sys', `${nodeA.name} — ${nodeB.name} を接続しました`);
          freeRevalidateAndRender();
        }
      });
    }
  }

  function freeHandleLinkClick(linkId) {
    const link = Free.topo.links.find((l) => l.id === linkId);
    if (!link) return;
    if (Free.interactionMode === 'delete') {
      freePushUndo();
      freeRemoveLinkIfaces(link);
      Free.topo.links = Free.topo.links.filter((l) => l.id !== linkId);
      freeLog('sys', 'リンクを削除しました');
      freeRevalidateAndRender();
      return;
    }
    const nodeA = Free.topo.nodes.get(link.a), nodeB = Free.topo.nodes.get(link.b);
    openCostModal({
      title: 'リンク設定',
      subtitle: `${nodeA.name} — ${nodeB.name}`,
      initialCost: link.baseCost != null ? link.baseCost : link.cost,
      costEditable: link.routable,
      initialDown: link.down,
      onSave: (cost, down) => {
        freePushUndo();
        if (link.routable) { link.baseCost = cost; recalcLinkCost(link); }
        setLinkDownState(Free, Free.topo, link, down, freeLog, freeRender);
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
    if (freeHasAnyError()) { statusEl.textContent = 'IPアドレス設定にエラーがあるため送信できません。'; return; }
    statusEl.textContent = '送信中…';
    simulateSend(Free.topo, srcId, dstId, freeLog, Free.svg, {
      failRate: Free.failRate,
      markDown: (link) => setLinkDownState(Free, Free.topo, link, true, freeLog, freeRender),
      onLinkDown: () => freeRender(),
      onRouteComputed: (result) => {
        if (result.reachable) {
          startDeliverySession(Free, Free.topo, srcId, dstId, freeRender, freeLog, (state) => {
            statusEl.textContent = state === 'done' ? '送信完了' : '送信失敗（不通）';
          });
        } else {
          statusEl.textContent = '送信失敗（不通）';
        }
      },
      onFinish: () => { /* 実際の到達可否はフローの解決時に statusEl を更新する */ }
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
    Free.logBadge = document.getElementById('free-log-badge');
    freeValidate();
    rvInitTables(Free.topo, computeNetworkSegments(Free.topo), Free.coldStart);
    startRvTimer(Free, Free.topo, freeRender);
    freeRender();
    freePopulateSelects();
    freeUpdateSendButtonState();

    document.querySelectorAll('#panel-free [data-add]').forEach((btn) => {
      btn.addEventListener('click', () => freeAddNode(btn.dataset.add));
    });
    document.querySelectorAll('#panel-free [data-mode]').forEach((btn) => {
      btn.addEventListener('click', () => freeSetMode(btn.dataset.mode));
    });
    document.getElementById('free-coldstart-toggle').addEventListener('change', (e) => {
      Free.coldStart = e.target.checked;
      rvInitTables(Free.topo, computeNetworkSegments(Free.topo), Free.coldStart);
      freeLog('sys', Free.coldStart
        ? '各ルーターのテーブルを空にしました。ここから収束していく様子を観察できます'
        : '各ルーターのテーブルに直結情報を再度仕込みました');
      freeRender();
    });
    document.getElementById('free-clear').addEventListener('click', () => {
      freePushUndo();
      Free.topo.nodes.clear();
      Free.topo.links = [];
      Free.typeCounters = { pc: 0, switch: 0, router: 0 };
      Free.flows = [];
      Free.ifaceCounter = 0;
      Free.nodeErrors = new Map();
      closeIpPopover();
      freeRevalidateAndRender();
      freePopulateSelects();
      freeLog('sys', 'すべて消去しました');
    });
    document.getElementById('free-send-btn').addEventListener('click', freeSend);
    document.getElementById('free-undo').addEventListener('click', freeUndo);
    document.getElementById('free-redo').addEventListener('click', freeRedo);
    document.addEventListener('keydown', (e) => {
      const panelFreeEl = document.getElementById('panel-free');
      if (!panelFreeEl || panelFreeEl.hidden) return; // 自由配置タブが表示されているときのみ有効
      const key = e.key.toLowerCase();
      if ((e.ctrlKey || e.metaKey) && key === 'z') { e.preventDefault(); freeUndo(); }
      else if ((e.ctrlKey || e.metaKey) && key === 'y') { e.preventDefault(); freeRedo(); }
    });
    document.getElementById('free-clear-log').addEventListener('click', () => {
      Free.logEl.innerHTML = '';
      Free.logBadge.hidden = true;
      Free.logBadge.textContent = '0';
    });

    const freeFailRateInput = document.getElementById('free-fail-rate');
    const freeFailRateOut = document.getElementById('free-fail-rate-out');
    freeFailRateInput.addEventListener('input', () => {
      Free.failRate = parseInt(freeFailRateInput.value, 10);
      freeFailRateOut.textContent = Free.failRate + '%';
    });

    document.getElementById('free-drift-toggle').addEventListener('change', (e) => {
      Free.driftEnabled = e.target.checked;
      if (Free.driftEnabled) {
        startDriftTimer(Free.topo, Free, freeLog, freeRender);
        freeLog('sys', '時間経過によるコスト自動変動を有効にしました');
      } else {
        stopDriftTimer(Free);
        freeLog('sys', '時間経過によるコスト自動変動を停止しました');
      }
    });
    document.getElementById('free-drift-fail-rate').addEventListener('input', (e) => {
      Free.driftFailRate = clamp(parseInt(e.target.value, 10) || 0, 0, 100);
    });

    document.getElementById('free-auto-recover-toggle').addEventListener('change', (e) => {
      Free.autoRecoverEnabled = e.target.checked;
      if (Free.autoRecoverEnabled) {
        enableAutoRecoverForCurrentDownLinks(Free, Free.topo, freeLog, freeRender);
        freeLog('sys', '障害の自動復帰（3〜6秒）を有効にしました');
      } else {
        disableAutoRecoverTimers(Free.topo);
        freeLog('sys', '障害の自動復帰を停止しました（今後は手動復旧のみ）');
      }
    });

    const freeFlowSpeedInput = document.getElementById('free-flow-speed');
    const freeFlowSpeedOut = document.getElementById('free-flow-speed-out');
    freeFlowSpeedInput.addEventListener('input', () => {
      Free.speedFactor = parseFloat(freeFlowSpeedInput.value) || 1;
      freeFlowSpeedOut.textContent = Free.speedFactor.toFixed(1) + 'x';
      applyFlowSpeedChange(Free);
      freeRender();
    });

    // クリック（ノード／リンク）
    Free.svg.addEventListener('click', (e) => {
      if (Free.dragging && Free.dragging.moved) return; // ドラッグ直後のクリックは無視
      const nodeTarget = e.target.closest('[data-node-id]');
      if (nodeTarget) { freeHandleNodeClick(nodeTarget.dataset.nodeId); return; }
      const linkTarget = e.target.closest('[data-link-id]');
      if (linkTarget) { freeHandleLinkClick(linkTarget.dataset.linkId); return; }
    });

    // 右クリックはモードに関係なく常に設定を確認できる（進行中の接続選択などは維持したまま）
    Free.svg.addEventListener('contextmenu', (e) => {
      const nodeTarget = e.target.closest('[data-node-id]');
      if (!nodeTarget) return;
      const node = Free.topo.nodes.get(nodeTarget.dataset.nodeId);
      if (!node || node.type === 'switch') return;
      e.preventDefault();
      openIpPopover(node.id);
    });

    document.addEventListener('click', (e) => {
      if (!Free.openPopoverNodeId) return;
      const popover = document.getElementById('ip-popover');
      if (popover.contains(e.target)) return;
      if (e.target.closest('[data-node-id]')) return;
      closeIpPopover();
      freeRender();
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
      if (Free.openPopoverNodeId === node.id) positionIpPopover(node);
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
      if (isFixed && typeof closeIpPopover === 'function') closeIpPopover();
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
