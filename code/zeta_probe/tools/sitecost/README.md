# sitecost

Exact verification of the site-cost law and of the gap-run cycle count of the
transfer model **(M)** in `paper/journal/paper2.tex`, §5 (`sec:sitecost`,
`sec:modelassembly`).

Everything is exact integer arithmetic. There is no floating point in this tool.

## The object

The ground truth is the crossing-pairing optimisation of paper 1 (Metric
formula, as verified), restated as `Definition (the pairing optimisation)` in
paper 2 §5.5. At a site, arrivals are paired with departures; a pair costs

| relation of the two ends | cost |
|---|---|
| same side, same sign (bounce) | 0 |
| same side, opposite signs (sign-flip bounce) | 2 |
| opposite sides (pass) | 1 |

Classes are `0 = (left,+) 1 = (left,-) 2 = (right,+) 3 = (right,-)`.

Edge `j` carries a deposit `d_j`, a travel indicator `f_j ∈ {-1,0,+1}` and a
crossing count `m_j ≥ max(|d_j|,|f_j|)` with `m_j ≡ d_j ≡ f_j (mod 2)`; it is
crossed `u_j = (m_j+f_j)/2` times up and `dn_j = (m_j-f_j)/2` times down, and
`p^u_j` of the up- and `p^d_j` of the down-crossings carry sign `+`, subject to
`d_j = 2 p^d_j - dn_j + u_j - 2 p^u_j`, i.e. `p^d_j = p^u_j + (d_j-f_j)/2`.

At the site between edge `L = j-1` and edge `R = j`:

```
arr = [p^u_L, u_L-p^u_L, p^d_R, dn_R-p^d_R]
dep = [p^d_L, dn_L-p^d_L, p^u_R, u_R-p^u_R]
```

plus a virtual arrival of class `(left,+)` at site 0 and a virtual departure of
class `(delta*==1 ? right : left, eps*)` at site `k*`.

## Solvers

Two independent exact solvers compute the minimum pairing cost:

* **min-cost flow**, successive shortest paths. Distances come from a full
  Bellman-Ford over every arc; the augmenting path is found by a DFS over
  admissible arcs guarded by a visited mark. Reconstructing the path from a
  predecessor array is *unsafe* here, because the residual graph has zero-cost
  arcs and the predecessor relation can then contain a zero-cost cycle; an
  earlier version of this file did exactly that and produced a wrong value on
  one cell out of a few hundred.
* **transportation dynamic program**, row-by-row allocation memoised on the
  remaining column demands. No flow, no potentials.

Setting `SITECOST_DUAL=1` runs both on every site and aborts on any
disagreement.

## Modes

```
sitecost xcheck    <maxentry>            cross-check the two solvers, and the closed form
sitecost interior  <|d|max> <lambda>     the interior local cost law
sitecost marker    <|d|max> <lambda>     the four marker junctions
sitecost universal <|d|max> <lambda>     Site = max(|alpha|,|beta|) on all eight site types
sitecost delete    <|d|max> <lambda>     hypothesis deletions on the three pairing costs
sitecost shield    <edges> <|d|max>      the relaxed length and the defect c, by direct
                                         enumeration of realizations (k*=0 bulk)
```

`lambda` is the number of extra crossing pairs allowed above the minimum, so
`m` runs over `max(|d|,|f|) + 2i` for `0 ≤ i ≤ lambda`.

Run everything under `code/zeta_probe/tools/runcap.sh` (Rule 8):

```
SITECOST_DUAL=1 ./tools/runcap.sh 8000 3600 ./tools/sitecost/target/release/sitecost universal 24 5
```

Peak RSS of every mode below is under 10 MB.

## Results recorded in paper 2

| claim | mode | ground covered | exceptions |
|---|---|---|---|
| both solvers agree | `xcheck 7` | 1 012 664 supply/demand pairs, entries ≤ 7 | 0 |
| `Site = max(\|α\|,\|β\|,\|Φ\|)` (Lemma, transportation value) | `xcheck 7` | same | 0 |
| `Site = max(\|α\|,\|β\|)`, independent of `m` and of the sign splits | `universal 24 5` | 4 532 157 configurations, 8 site types, all four marker data, both deposit signs, \|d\| ≤ 24, `m` up to minimum+10, both solvers on every configuration | 0 |
| the three pairing costs are each necessary | `delete 8 2` | 7524 configurations per deletion, 10 deletions | 2544–7392 counterexamples each (as required) |
| `Site_0 = max(\|d_L-1\|,\|d_R\|)` | `marker 12 3` | 156 cells per junction, all four marker data | 0 |
| the earlier form `max(\|d_L\|-1,\|d_R\|)` | `marker 12 3` | same | **42 misses** at the near junction, 36 at its `k*<0` mirror, all with `d_L < 0` |
| `ℓ_R = Σ m + Σ max(\|α\|,\|β\|)` | `shield 8 4` | 1 048 544 bulk configurations, every sign split, every site bijection | 0 |
| `c = #{cut interior sites}` (the shield law) | `shield 8 4` | same, gap runs to length 6 | 0 |

The `shield` mode is limited by the tabulated permutations: a site of size
greater than 8 aborts with a message. With `k*=0` that caps the deposits at
`|d| ≤ 6`.

## What this does and does not settle

The site-cost law and the marker junctions are **proved** in paper 2 §5.5
(Lemma `lem:transport`, Corollaries `cor:localcost`, `cor:lRclosed`,
`cor:marker`); the runs above are falsification, not the proof. The inequality
`c ≥ L-1` per interior gap run is proved (`prop:cut`); the reverse inequality
`c ≤ L-1` is only verified, by the `shield` mode. That the pairing optimisation
computes the relaxed word length at all is the standing unproved input of
paper 1.
