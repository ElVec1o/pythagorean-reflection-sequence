import mpmath as mp
mp.mp.dps=30
v=[1,3,5,8,13,21,34,55,91,148,235,371,590,931,1451,2254,3513,5455,8418,12959,19949,30640,46905,71699,109490,166969,254047,386192,586349]
u=[1,3,5,8,13,21,34,55,89,144,225,351,554,875,1345,2066,3203,4971,7574,11543,17683,27108,41067,62263,94622,143881,217101,327832,495443]
n=min(len(v),len(u))
print("n :  v_n     u_n    v_n-u_n   v_n/u_n   (v-u)_n/(v-u)_{n-1}")
prev=None
for i in range(n):
    d=v[i]-u[i]
    rat=v[i]/u[i]
    gr = (d/prev) if (prev and prev>0) else float('nan')
    print(f"{i:2d}: {v[i]:7d} {u[i]:7d} {d:7d}  {rat:.5f}  {gr if gr!=gr else round(gr,4)}")
    prev=d if d>0 else prev
# growth rate of the DIFFERENCE d_n = v_n - u_n
d=[v[i]-u[i] for i in range(n)]
dd=[d[i] for i in range(n) if d[i]>0]
print("\ndifference d_n=v_n-u_n (nonzero):", dd)
# ratio of differences
nz=[(i,d[i]) for i in range(n) if d[i]>0]
print("\nd_n ratios (last 8):")
for j in range(len(nz)-8,len(nz)):
    if j>0 and nz[j-1][1]>0:
        print(f"  n={nz[j][0]}: d={nz[j][1]} ratio={nz[j][1]/nz[j-1][1]:.5f}")
