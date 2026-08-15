import pathlib
DATA = pathlib.Path(__file__).resolve().parents[2] / 'data' / 'triangle_relations'
# HONEYCOMB FLOW MODEL -- census-first verification of the master metric law.
#
# Theory under test. Let P = G/T be the point group (generic: Z^2 x| C2),
# X = Cayley(P) on the three reflection images (a honeycomb: 3-regular,
# bipartite by orientation). A word w = r_{i1}...r_{il} has prefix walk
# pi_0 = I, pi_j = S_{i1}...S_{ij}; step j traverses the X-edge
# {pi_{j-1}, pi_{j-1} S_{ij}} and deposits pi_{j-1} * 2 v_{ij} into the
# translation. Since S_i v_i = -v_i, the two directions of one edge deposit
# exactly opposite vectors, so t(w) = V(flow(w)) where flow(w) in Z_1(X) is
# the net signed edge-traversal count. Claims to verify:
#   (F) each conjugate lamp t_{n,m} has flow = a single hexagonal face,
#       faces share an edge iff sites are hex-adjacent, with opposite signs,
#       and every edge lies in at most two faces;
#   (N) ||phi(c)||_1 = TV(c) = sum over site-lattice edges |c_u - c_v|;
#   (M) ell(c) = ||phi(c)||_1 + 2 st(c), st = min # extra X-edges needed to
#       connect supp(phi) together with the identity vertex.
# Verification: (1) per-step deposit assertions on every word processed,
# (2) the 500 measured translations (fit set), (3) THE CENSUS: full
# enumeration pred<=18 compared ELEMENT-LEVEL against exact Rust BFS dumps.
from fractions import Fraction as Fr
import json, sys, time, heapq
from collections import Counter
from itertools import combinations

t_start = time.time()
INF9 = 10**9
HEXU = {(0,1),(1,-1),(1,0),(0,-1),(-1,1),(-1,0)}
BASESET = frozenset({(0,0),(-1,1),(-1,0)})

# ---------- witness triangle (0,0),(1,0),(1/3,1/2), exact affine maps ----------
def refl(p0, p1):
    dx, dy = p1[0]-p0[0], p1[1]-p0[1]
    L = dx*dx + dy*dy
    a = (dx*dx - dy*dy)/L
    b = 2*dx*dy/L
    S = ((a, b), (b, -a))
    t = ((1-a)*p0[0] - b*p0[1], -b*p0[0] + (1+a)*p0[1])
    return (S, t)

import os
V0 = (Fr(0), Fr(0)); V1 = (Fr(1), Fr(0))
V2 = (Fr(int(os.environ.get("W_PN", "1")), int(os.environ.get("W_PD", "3"))),
      Fr(int(os.environ.get("W_QN", "1")), int(os.environ.get("W_QD", "2"))))
GENS = [refl(V0, V1), refl(V1, V2), refl(V2, V0)]

def mat_mul(A, B):
    return ((A[0][0]*B[0][0]+A[0][1]*B[1][0], A[0][0]*B[0][1]+A[0][1]*B[1][1]),
            (A[1][0]*B[0][0]+A[1][1]*B[1][0], A[1][0]*B[0][1]+A[1][1]*B[1][1]))
def mat_vec(A, v):
    return (A[0][0]*v[0]+A[0][1]*v[1], A[1][0]*v[0]+A[1][1]*v[1])
def aff_mul(g, h):   # g o h
    return (mat_mul(g[0], h[0]), tuple(x+y for x, y in zip(mat_vec(g[0], h[1]), g[1])))

S = [g[0] for g in GENS]
TV2 = [g[1] for g in GENS]          # 2 v_i  (the affine translation of r_i)
ID2 = ((Fr(1), Fr(0)), (Fr(0), Fr(1)))
IDA = (ID2, (Fr(0), Fr(0)))

# core identity S_i v_i = -v_i
for i in range(3):
    assert mat_vec(S[i], TV2[i]) == tuple(-x for x in TV2[i]), "S_i v_i != -v_i"

# ---------- abstract point group P = Z^2 x| C2, normal form (m1,m2,eps) ----------
# rho1 = S0 S1, rho2 = S0 S2; g = rho1^m1 rho2^m2 S0^eps; right-multiplication:
def stepv(v, i):
    m1, m2, e = v
    if i == 0: return (m1, m2, 1-e)
    if i == 1: return ((m1-1, m2, 1) if e == 0 else (m1+1, m2, 0))
    return ((m1, m2-1, 1) if e == 0 else (m1, m2+1, 0))

R1 = mat_mul(S[0], S[1]); R2 = mat_mul(S[0], S[2])
R1i = mat_mul(S[1], S[0]); R2i = mat_mul(S[2], S[0])
_matcache = {(0,0,0): ID2}
def nf_mat(v):
    if v in _matcache: return _matcache[v]
    m1, m2, e = v
    M = ID2
    for _ in range(abs(m1)): M = mat_mul(M, R1 if m1 > 0 else R1i)
    for _ in range(abs(m2)): M = mat_mul(M, R2 if m2 > 0 else R2i)
    if e: M = mat_mul(M, S[0])
    _matcache[v] = M
    return M
_mat2nf = {}
def check_faithful(v):
    M = nf_mat(v)
    old = _mat2nf.setdefault(M, v)
    assert old == v, f"witness point group not faithful: {old} vs {v}"

E0 = (0, 0, 0)   # basepoint vertex (identity)

def edge_of(u, i):
    """undirected edge {u, u.S_i}; canonical orientation: from the eps=0 endpoint."""
    w = stepv(u, i)
    return (u, w, i) if u[2] == 0 else (w, u, i)

_edge_dep = {}   # edge -> deposit vector for canonical (eps0 -> eps1) traversal
def word_flow(word):
    """process a word; return (flow Counter over edges, exact translation, endpoint nf)."""
    flow = Counter()
    tot = (Fr(0), Fr(0))
    pi_nf = E0
    pi_mat = ID2
    for i in word:
        dep = mat_vec(pi_mat, TV2[i])
        tot = (tot[0]+dep[0], tot[1]+dep[1])
        e = edge_of(pi_nf, i)
        sgn = 1 if pi_nf[2] == 0 else -1
        cdep = dep if sgn == 1 else tuple(-x for x in dep)
        old = _edge_dep.setdefault(e, cdep)
        assert old == cdep, "edge deposit not direction-consistent"
        flow[e] += sgn
        pi_nf = stepv(pi_nf, i)
        pi_mat = mat_mul(pi_mat, S[i])
        check_faithful(pi_nf)
    flow = Counter({e: c for e, c in flow.items() if c})
    return flow, tot, pi_nf, pi_mat

def vflow(flow):
    tx = Fr(0); ty = Fr(0)
    for e, c in flow.items():
        d = _edge_dep[e]
        tx += c*d[0]; ty += c*d[1]
    return (tx, ty)

# ---------- Phase F: faces from actual conjugated lamp words ----------
T1W = [0, 1, 2, 0, 1, 2]
def conj_word(n, m):
    c = ([0, 1]*n if n >= 0 else [1, 0]*(-n)) + ([0, 2]*m if m >= 0 else [2, 0]*(-m))
    return c + T1W + c[::-1]

FW = 9
FACE = {}; VEC = {}
for n in range(-FW, FW+1):
    for m in range(-FW, FW+1):
        fl, tot, endnf, endmat = word_flow(conj_word(n, m))
        assert endnf == E0 and endmat == ID2, "conjugated lamp word not a translation"
        assert vflow(fl) == tot
        assert len(fl) == 6 and all(abs(c) == 1 for c in fl.values()), \
            f"face ({n},{m}) flow is not a hexagon"
        vs = set()
        for (u, v, i) in fl: vs.add(u); vs.add(v)
        assert len(vs) == 6, "hexagon does not have 6 distinct vertices"
        FACE[(n, m)] = dict(fl)
        VEC[(n, m)] = tot
print(f"[F] faces built on |n|,|m|<={FW}: {len(FACE)} hexagons, all verified "
      f"({time.time()-t_start:.1f}s)")

# face sharing structure
edge_owners = {}
for s, f in FACE.items():
    for e in f: edge_owners.setdefault(e, []).append(s)
inner = [s for s in FACE if max(abs(s[0]), abs(s[1])) <= FW-2]
for s in inner:
    for t in FACE:
        if t <= s: continue
        sh = set(FACE[s]) & set(FACE[t])
        d = (t[0]-s[0], t[1]-s[1])
        if d in HEXU:
            assert len(sh) == 1, f"adjacent faces {s},{t} share {len(sh)} edges"
            e = sh.pop()
            assert FACE[s][e] == -FACE[t][e], "shared edge signs not opposite"
        else:
            assert not sh, f"non-adjacent faces {s},{t} share an edge"
for e, own in edge_owners.items():
    assert len(own) <= 2, f"edge in {len(own)} faces"
base_faces = {s for s in FACE if any(E0 in (u, v) for (u, v, i) in FACE[s])}
assert base_faces == set(BASESET), f"faces at identity vertex: {base_faces}"
print(f"[F] sharing structure: axes<->lattice-edges, opposite orientation; "
      f"faces at identity vertex = base sites {sorted(base_faces)}")

# ---------- phi, TV, Steiner ----------
def phi_of(cfg):
    fl = Counter()
    for (n, m, s) in cfg:
        for e, c in FACE[(n, m)].items(): fl[e] += s*c
    return Counter({e: c for e, c in fl.items() if c})

def tv_of(cfg):
    mm = Counter()
    for (n, m, s) in cfg: mm[(n, m)] += s
    tot = 0; seen = set()
    for st in list(mm):
        for dx, dy in HEXU:
            u = (st[0]+dx, st[1]+dy)
            e = (st, u) if st < u else (u, st)
            if e in seen: continue
            seen.add(e)
            tot += abs(mm[st] - mm.get(u, 0))
    return tot

def _components(flow):
    verts = {E0}
    for (u, v, i) in flow: verts.add(u); verts.add(v)
    par = {v: v for v in verts}
    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]; x = par[x]
        return x
    for (u, v, i) in flow: par[find(u)] = find(v)
    comp = {}
    for v in verts: comp.setdefault(find(v), []).append(v)
    return list(comp.values())

def _bfs_between(A, Bset, Bnd, cap=INF9):
    """edge distance in X between vertex sets A and Bset within window; INF if >cap."""
    from collections import deque
    seen = {v: 0 for v in A}
    q = deque(A)
    while q:
        v = q.popleft()
        d = seen[v]
        if d >= cap: continue
        for i in range(3):
            w = stepv(v, i)
            if abs(w[0]) > Bnd or abs(w[1]) > Bnd: continue
            if w in Bset: return d+1
            if w not in seen:
                seen[w] = d+1
                q.append(w)
    return INF9

_st_memo = {}   # support -> (value_or_INF, cap_used)
def steiner_extra(flow, cap=INF9):
    """min # X-edges to add so that supp(flow) + identity vertex is connected.
    Returns INF9 if the value exceeds cap (exact below cap)."""
    key = frozenset(flow)
    hit = _st_memo.get(key)
    if hit is not None:
        val, hcap = hit
        if val < INF9 or hcap >= cap: return val
    comps = _components(flow)
    k = len(comps)
    if k == 1:
        _st_memo[key] = (0, INF9)
        return 0
    verts = [v for c in comps for v in c]
    Bnd = max(max(abs(v[0]), abs(v[1])) for v in verts) + 4
    if k == 2:
        small, big = sorted(comps, key=len)
        ans = _bfs_between(small, set(big), Bnd, cap)
        _st_memo[key] = (ans, cap)
        return ans
    comp = {i: c for i, c in enumerate(comps)}
    B = Bnd
    cid = {}
    for ci, mem in enumerate(comp.values()):
        for v in mem: cid[v] = ci
    def node(v):
        return ('c', cid[v]) if v in cid else ('v', v)
    comps = list(comp.values())
    def node_nbrs(nd):
        out = set()
        if nd[0] == 'v':
            for i in range(3):
                w = stepv(nd[1], i)
                if abs(w[0]) <= B and abs(w[1]) <= B: out.add(node(w))
        else:
            for v in comps[nd[1]]:
                for i in range(3):
                    w = stepv(v, i)
                    if abs(w[0]) <= B and abs(w[1]) <= B:
                        nw = node(w)
                        if nw != nd: out.add(nw)
        return out
    full = (1 << k) - 1
    DP = {}
    for ci in range(k): DP.setdefault(1 << ci, {})[('c', ci)] = 0
    for mask in range(1, full+1):
        d = DP.setdefault(mask, {})
        sub = (mask-1) & mask
        while sub:
            rest = mask ^ sub
            A = DP.get(sub); Bp = DP.get(rest)
            if A and Bp:
                for nd, ca in A.items():
                    cb = Bp.get(nd)
                    if cb is not None and ca+cb < d.get(nd, INF9): d[nd] = ca+cb
            sub = (sub-1) & mask
        pq = [(c, nd) for nd, c in d.items()]
        heapq.heapify(pq)
        while pq:
            c, nd = heapq.heappop(pq)
            if c > d.get(nd, INF9): continue
            for w in node_nbrs(nd):
                if c+1 < d.get(w, INF9):
                    d[w] = c+1; heapq.heappush(pq, (c+1, w))
    ans = min(DP[full].values())
    _st_memo[key] = (ans, INF9)
    return ans

import resource
def _rss_gb():
    return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 2**30

def pred(cfg, cap=22):
    # no per-config memo: the growth loop deduplicates configs via `seen`,
    # so a memo only bloats memory (it contributed to an OOM once)
    cfg = tuple(sorted(cfg))
    seen_site = {}
    for (n, m, s) in cfg:
        if seen_site.setdefault((n, m), s) != s:
            return INF9
    fl = phi_of(cfg)
    n1 = sum(abs(c) for c in fl.values())
    if n1 > cap:
        return INF9
    k = len(_components(fl))
    if n1 + 2*(k-1) > cap:
        return INF9
    if len(_st_memo) > 400000: _st_memo.clear()
    cap_st = (cap - n1)//2
    st = steiner_extra(fl, cap_st)
    return INF9 if st > cap_st else n1 + 2*st

# ---------- Phase 3: the 500 measured translations ----------
recs = [r for r in json.load(open(DATA/"decomp_depth14.json")) if r["cfg"] is not None]
okc = 0; nrm_ok = 0; hole_diffs = []
for r in recs:
    cfg = [tuple(c) for c in r["cfg"]]
    fl = phi_of(cfg)
    n1 = sum(abs(c) for c in fl.values())
    assert n1 == tv_of(cfg), f"||phi||_1 != TV on {cfg}"
    nrm_ok += 1
    L = len(cfg)
    sites = {}
    for (n, m, s) in cfg: sites[(n, m)] = s
    ks = list(sites)
    h_pair = sum(1 for a, b in combinations(ks, 2)
                 if (b[0]-a[0], b[1]-a[1]) in HEXU and sites[a] == sites[b])
    if 6*L - 2*h_pair != n1: hole_diffs.append(cfg)
    p = pred(cfg)
    if p == r["d"]: okc += 1
    else: print(f"  MISS: cfg={cfg} true={r['d']} pred={p}")
print(f"[3] fit set: pred==true on {okc}/{len(recs)}; ||phi||_1==TV on {nrm_ok}/{len(recs)}; "
      f"configs where 6L-2h(site pairs) != ||phi||_1: {len(hole_diffs)} "
      f"({time.time()-t_start:.1f}s)")
st_dist = Counter(steiner_extra(phi_of([tuple(c) for c in r["cfg"]])) for r in recs)
print(f"[3] st distribution on the {len(recs)}: {dict(sorted(st_dist.items()))}")

# stacked-adjacent example where the site-pair hole count is wrong:
stack = [(0, 0, 1), (0, 0, 1), (-1, 0, 1), (-1, 0, 1)]
print(f"[3] stacked pair example {stack}: ||phi||_1={sum(abs(c) for c in phi_of(stack).values())}"
      f" vs 6L-2h(site pairs)={6*4-2*1}  (paper statement must use the min form)")

# ---------- Phase 4: single lamps and the exceptional triangles ----------
sys.path.insert(0, ".")
import heapq as _h
def autk(R=12):
    SIG = [lambda n, m: (-n-1, -m+1), lambda n, m: (-n-2, -m+1), lambda n, m: (-n-1, -m)]
    BASE = {(0, 0): 1, (-1, 1): 2, (-1, 0): 0}
    best = {s: 0 for s in BASE}; pq = []
    for s, z in BASE.items(): _h.heappush(pq, (1, SIG[z](*s), z))
    seen = {}
    while pq:
        k, site, last = _h.heappop(pq)
        if abs(site[0]) > R or abs(site[1]) > R: continue
        if seen.get((site, last), 99) <= k: continue
        seen[(site, last)] = k
        if site not in best or k < best[site]: best[site] = k
        for y in range(3):
            if y != last: _h.heappush(pq, (k+1, SIG[y](*site), y))
    return best
K = autk()
mism = ntest = 0
for n in range(-(FW-2), FW-1):
    for m in range(-(FW-2), FW-1):
        k = K.get((n, m))
        dx = steiner_extra(phi_of([(n, m, 1)]))
        ntest += 1
        if k is None or dx != k:
            mism += 1
            print(f"  single lamp ({n},{m}): d_X {dx} vs sigma-walk k {k}")
print(f"[4] single-lamp law: d_X == sigma-walk k on all |n|,|m|<={FW-2} "
      f"({ntest} sites, mismatches: {mism})")
for sg in (1, -1):
    tri = [(0, 0, sg), (-1, 0, sg), (-1, 1, sg)]
    print(f"[4] uniform base triangle sign {sg:+d}: pred = {pred(tri)} (true 14)")
tri2 = [(0, 0, 1), (1, 0, 1), (0, 1, 1)]
print(f"[4] anchored non-base same-sign triangle {tri2}: pred = {pred(tri2)} (true 12)")

# ---------- Phase 5: full census, config- and element-level ----------
POOL = [s for s in K if K[s] <= 6]
JTn = {tuple(int(x) for x in k.split(",")): v for k, v in json.load(open(DATA/"jump_table.json")).items()}
moves = list(JTn) + [(0, 0)]
seen = set(); frontier = set(); allc = set()
for s in POOL:
    for sg in (1, -1):
        c = ((s[0], s[1], sg),)
        seen.add(c); frontier.add(c); allc.add(c)
t5 = time.time()
for L in range(2, 10):
    new = set()
    for cfg in frontier:
        cl = list(cfg); cand = set(POOL)
        for c in cl:
            for e in moves:
                p = (c[0]+e[0], c[1]+e[1])
                if abs(p[0]) <= FW-2 and abs(p[1]) <= FW-2: cand.add(p)
        for p in cand:
            for sg in (1, -1):
                nc = tuple(sorted(cl+[(p[0], p[1], sg)]))
                if nc in seen: continue
                seen.add(nc)
                if pred(nc) <= 22: new.add(nc); allc.add(nc)
    frontier = new
    print(f"[5] L={L}: {len(new)} configs kept  ({time.time()-t5:.0f}s elapsed)", flush=True)
    if not new: break

cnt = Counter(); by_depth = {}
for c in allc:
    v = pred(c)
    if v <= 18:
        cnt[v] += 1
        by_depth.setdefault(v, []).append(c)
json.dump({str(d): [[list(l) for l in c] for c in cs]
           for d, cs in sorted(by_depth.items())},
          open("census_configs.json", "w"))
print(f"[5] dumped {sum(len(v) for v in by_depth.values())} configs -> census_configs.json")
generic_counts = {6: 6, 8: 6, 10: 42, 12: 96, 14: 350, 16: 1092, 18: 3684}
print("\n[5] CONFIG-LEVEL CENSUS (= generic counts; witness (1/3,1/2) merges 4 at 18):")
allm = True
for d in range(6, 19, 2):
    p = cnt.get(d, 0); t = generic_counts[d]; m = (p == t); allm &= m
    print(f"    depth {d:2d}: predicted {p:5d}  generic {t:5d}  {'MATCH' if m else 'MISS'}")

# element level
print("\n[5] ELEMENT-LEVEL CENSUS (exact vectors vs Rust BFS):")
elem_all = True
for d in range(6, 19, 2):
    vecs = {}
    coll = 0
    for c in by_depth.get(d, []):
        tx = Fr(0); ty = Fr(0)
        for (n, m, s) in c:
            tx += s*VEC[(n, m)][0]; ty += s*VEC[(n, m)][1]
        key = (tx, ty)
        if key in vecs: coll += 1
        vecs[key] = c
    try:
        lines = open(f"rust_cost/translations_d{d}.txt").read().split()
        tr = set()
        for i in range(0, len(lines), 4):
            tr.add((Fr(int(lines[i]), int(lines[i+1])), Fr(int(lines[i+2]), int(lines[i+3]))))
    except FileNotFoundError:
        hint = ("also not in this directory" if not pathlib.Path(f"translations_d{d}.txt").exists()
                else "but IS in this directory: rust_cost was run from here rather "
                     "than from rust_cost/, so move the dumps into rust_cost/")
        print(f"    depth {d:2d}: rust dump rust_cost/translations_d{d}.txt missing "
              f"({hint}); skipped, so the verdict below will read NOT CLOSED")
        elem_all = False; continue
    ps = set(vecs)
    expected_coll = 4 if d == 18 else 0   # witness (1/3,1/2) is not flow-generic:
    # four length-18 collisions (two Z-relations + inverses), see witness_collisions.py;
    # witness (2/7,3/5) has none and returns 3684 (witness_second.py).
    m = (ps == tr) and coll == expected_coll
    elem_all &= m
    print(f"    depth {d:2d}: predicted {len(ps):5d} elements (config collisions {coll}, "
          f"expected {expected_coll}), true {len(tr):5d}, missing {len(tr-ps)}, "
          f"spurious {len(ps-tr)}  {'MATCH' if m else 'MISS'}")

print(f"\n{'*** MASTER LAW ell = ||phi||_1 + 2*Steiner VERIFIED: census exact at both levels (witness-1 collisions as expected; see witness_second.py) ***' if allm and elem_all else 'NOT CLOSED'}")
print(f"total {time.time()-t_start:.0f}s")
