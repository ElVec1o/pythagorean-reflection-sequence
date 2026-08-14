import mpmath as mp
mp.mp.dps=60
exec(open('SYNTH_dict_verify.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]

# Build candidate bulk-block combinations for t1.
# We have: Se=1-S1b, So=(p/2q)S0b, b0=S0b/(1-S1b), b1=t0=S1b/(1-S1b).
# t1=P12/Se. Hunt for P12 in terms of bulk blocks (S0b, S1b, k-shifts Sbulk(2),Sbulk(3)).

print("Hunting t1 vs bulk-block combos at generic q")
print(f"{'q':>7} {'t1':>13} {'S0b':>11} {'S1b':>11} {'S2b':>11} {'S3b':>11} {'Se':>11}")
for qf in ['0.70','0.80','0.88','0.96','0.985']:
    q=mp.mpf(qf); p=1-q; N=int(70/(1-q))
    b0,b1,t0,t1,L,qp=raw(q,N)
    S0b=Sbulk(0,q);S1b=Sbulk(1,q);S2b=Sbulk(2,q);S3b=Sbulk(3,q)
    print(f"{qf:>7} {float(t1):>13.7f} {float(S0b):>11.6f} {float(S1b):>11.6f} {float(S2b):>11.6f} {float(S3b):>11.6f} {float(1-S1b):>11.6f}")
