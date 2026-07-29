# Second-witness certification: rebuild faces/vectors at (2/7,3/5), re-verify all
# structural asserts there, and compare the census configs' vectors element by
# element against the BFS dumps at that witness. Expected: 3684 distinct at 18.
import os
os.environ["W_PN"] = "2"; os.environ["W_PD"] = "7"
os.environ["W_QN"] = "3"; os.environ["W_QD"] = "5"
exec(open("honeycomb_metric_and_census.py").read().split("# ---------- Phase 3")[0])
import json
from fractions import Fraction as Fr

cfgs = json.load(open("census_configs.json"))
allok = True
for d in range(6, 19, 2):
    vecs = {}
    coll = 0
    for c in cfgs.get(str(d), []):
        tx = Fr(0); ty = Fr(0)
        for (n, m, s) in c:
            tx += s*VEC[(n, m)][0]; ty += s*VEC[(n, m)][1]
        if (tx, ty) in vecs: coll += 1
        vecs[(tx, ty)] = c
    fn = f"rust_cost/translations_w2_7_3_5_d{d}.txt"
    lines = open(fn).read().split()
    tr = set()
    for i in range(0, len(lines), 4):
        tr.add((Fr(int(lines[i]), int(lines[i+1])), Fr(int(lines[i+2]), int(lines[i+3]))))
    ps = set(vecs)
    m = ps == tr
    allok &= m and coll == 0
    print(f"depth {d:2d}: configs {len(cfgs.get(str(d),[]))}, distinct vectors {len(ps)} "
          f"(collisions {coll}), witness-2 truth {len(tr)}, missing {len(tr-ps)}, "
          f"spurious {len(ps-tr)}  {'MATCH' if m and coll==0 else 'MISS'}")
print("\n*** WITNESS 2: FULL ELEMENT-LEVEL MATCH, NO COLLISIONS ***" if allok
      else "\nwitness 2 shows structure differing from witness 1 (see rows)")
