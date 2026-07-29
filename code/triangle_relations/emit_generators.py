import sys
exec(open("stratum_fields.py").read().split("def gens_gen(")[0])
m=int(sys.argv[1]); a=int(sys.argv[2]); b=int(sys.argv[3])
GS,IDS,K=gens_strat(m,a,b)
deg=len(MIN[m])-1
out=[f"{m} {deg}"]
out.append(" ".join(f"{x}" for x in MIN[m][:deg]))
out.append(" ".join(f"{x}" for x in K.S2.c))
for g in GS:
    for x in g:
        out.append(" ".join(f"{t}" for t in x.u.c) + " | " + " ".join(f"{t}" for t in x.v.c))
open(f"gens_{m}_{a}_{b}.txt","w").write("\n".join(out)+"\n")
print(f"wrote gens_{m}_{a}_{b}.txt (deg {deg})")
