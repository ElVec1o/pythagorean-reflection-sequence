# Class C counterexamples

`classC_counterexamples.py` regenerates Theorem "Conjecture C is false" of
`paper/journal/merged_novel_paper.tex`. For each listed Class C leg tuple it

1. finds two distinct elements `w1 != w2` of `W_3` with the same **linear part** under `rho_a`,
   by breadth-first search in `W_3` using the right-angled normal form, in exact rationals;
2. sets `u = w1 w2^-1` and checks `u != 1` in `W_3` in the **Tits geometric representation**,
   which is faithful for every Coxeter system and has integer matrices here, so the check is
   exact and independent of the normal-form code;
3. checks the linear part of `rho_a(u)` is the identity, so `rho_a(u)` is a translation;
4. sets `c = [u, R_0 u R_0]` and checks `c != 1` in `W_3`, again in the Tits representation.

`rho_a(c) = 1` then needs no computation: `rho_a(u)` is a translation, a conjugate of a
translation by an isometry is a translation, and translations commute.

The point-group collisions themselves are found independently, at two primes, by
`code/zeta_probe/tools/pointgroup`.

```bash
python3 classC_counterexamples.py
```

Runs in about 20 s, peak RSS under 100 MB.
