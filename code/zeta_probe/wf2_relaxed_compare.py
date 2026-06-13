import mpmath as mp
mp.mp.dps=30
v=[1,3,5,8,13,21,34,55,91,148,235,371,590,931,1451,2254,3513,5455,8418,12959,19949,30640,46905,71699,109490,166969,254047,386192,586349]
u=[1,3,5,8,13,21,34,55,89,144,225,351,554,875,1345,2066,3203,4971,7574,11543,17683,27108,41067,62263,94622,143881,217101,327832,495443,749195,1127236,1697179,2554961,3848384,5777651,8679441,13031206,19574659,29338781,43997388,65932461,98849591,147969934]
n=min(len(v),len(u))
print("n : r_relaxed(n)  r_true(n)   diff")
for i in range(7,n-1):
    rr=mp.mpf(v[i+1])/v[i]; rt=mp.mpf(u[i+1])/u[i]
    print(f"{i:2d}: {mp.nstr(rr,8)}   {mp.nstr(rt,8)}   {mp.nstr(rr-rt,6)}")
# The two ratio sequences r_relaxed(n) and r_true(n): if r=beta2, their
# difference -> 0. Track the difference trend.
print("\ndifference r_relaxed(n)-r_true(n) -- if ->0 then r=beta2:")
diffs=[(mp.mpf(v[i+1])/v[i])-(mp.mpf(u[i+1])/u[i]) for i in range(7,n-1)]
for i,d in enumerate(diffs):
    print(f"  n={i+7}: {mp.nstr(d,6)}")
