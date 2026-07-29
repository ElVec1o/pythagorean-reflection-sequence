# Diagnose the depth-18 witness collisions at (1/3,1/2): which configs merge.
exec(open("honeycomb_metric_and_census.py").read().split("# ---------- Phase 3")[0])
import json
from fractions import Fraction as Fr
from collections import defaultdict

cfgs = json.load(open("census_configs.json"))["18"]
print(f"{len(cfgs)} configs with formula value 18")
byvec = defaultdict(list)
for c in cfgs:
    tx = Fr(0); ty = Fr(0)
    for (n, m, s) in c:
        tx += s*VEC[(n, m)][0]; ty += s*VEC[(n, m)][1]
    byvec[(tx, ty)].append(c)
coll = {v: cs for v, cs in byvec.items() if len(cs) > 1}
print(f"{len(byvec)} distinct vectors, {len(coll)} collision classes")
for v, cs in sorted(coll.items(), key=str):
    print(f"\nvector ({v[0]}, {v[1]}):")
    for c in cs:
        sites = [(n, m, s) for (n, m, s) in c]
        print(f"   config {sites}")
    # difference relation
    d = defaultdict(int)
    for (n, m, s) in cs[0]: d[(n, m)] += s
    for (n, m, s) in cs[1]: d[(n, m)] -= s
    rel = {k: v2 for k, v2 in d.items() if v2}
    print(f"   relation sum r_s t_s = 0 at this witness, r = {dict(sorted(rel.items()))}")
