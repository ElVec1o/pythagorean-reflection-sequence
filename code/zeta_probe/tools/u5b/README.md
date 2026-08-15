# u5b

The reflection-constant probe of the travel-block pole, plus the confluence-grind analysis
scripts built on its output (route D3.2 / D3.3 / D3.5, all closed; see `private/RESEARCH_LOG.md`).

**No statement of any shipping paper depends on the files in this directory.** The constant
`sqrt2/36` that this probe first located numerically is derived elementarily in
`paper/journal/paper2.tex`, and no paper cites `tools/u5b` by name. What is here is an
exploration record that is kept runnable, not a certificate for a published number.

## Status under Rule 9

This directory is a **reproduction directory, not a regeneration pipeline**: everything the
twelve analysis scripts read now ships with the repository, so a fresh clone runs them with no
arguments and no environment variables.

| file | size | produced by | shipped |
|---|---|---|---|
| `u5b_out.txt` | 66 kB, 229 rows (`m = 2..230`) | `target/release/u5b` | yes |
| `u5b_out_m200.bak` | 58 kB, an earlier `m <= 200` run | same | yes |
| `cks.json`, `cks10.json`, `cks_*.json` | under 1 kB each | `borel_ck.py` / `borel_ck2.py` / by hand | yes |

`u5b_out.txt` matches the `*_out.txt` glob in the repository's `.gitignore` and was excluded by
it. That was an accident of the glob, not a size decision: at 66 kB it is smaller than several
files already tracked here, and its own predecessor `u5b_out_m200.bak` was tracked all along.
The `.gitignore` now carries an explicit negation for it.

Of the twelve scripts, ten read a data file and two only write one. `analyze_u5b.py` reads
`u5b_out.txt`; `refine_C.py` reads `u5b_out_m200.bak`; the eight `borel_*` analysis scripts read
`cks.json`; `borel_ck.py` and `borel_ck2.py` derive the `c_k` symbolically and write.

## Regenerating `u5b_out.txt`

```
cargo build --release
../runcap.sh 14000 7200 target/release/u5b <m_start> <m_end>      # writes ./u5b_out.txt
```

The Rust probe is scalar (peak RSS 1 MB), appends, and resumes: it reads the existing
`u5b_out.txt`, skips every `m` already present, and reports progress and an ETA per pole. All
arithmetic is `rug`/MPFR at 1536 bits, about 462 decimal digits.

Cost is dominated by the tail, since the number of terms in the defect sum grows like `1/tau`
and `tau ~ (2/pi^2) m^{-2}`. Measured on this machine: `m = 2..8` in under a second,
`m = 228..230` in 164 s, so about 55 s per pole at the top of the range and roughly 70 minutes
for the whole `m = 2..230` from empty. Disk: 66 kB.

Regeneration is exact, not approximate. Rerunning `m = 228..230` into an empty directory
reproduced the three shipped rows byte for byte at all 40 printed digits.

## The analysis scripts

Each locates its input in this order: an explicit path argument, then `$U5B_DIR`, then this
directory. The third case is the normal one.

```
../runcap.sh 14000 900 python3 analyze_u5b.py        # rel/tau -> C, the reflection constant
../runcap.sh 14000 900 python3 refine_C.py           # Richardson refinement of C on the .bak run
../runcap.sh 14000 900 python3 borel_summary.py      # the route D3.5 summary
```

`borel_analyze.py`, `borel_gevrey_tau.py`, `borel_least_term.py`, `borel_pade.py`,
`borel_refine.py`, `borel_singfit.py` and `borel_laplace.py` read `cks.json` and run in seconds.
The `d32_*`, `d33_*`, `d34work/*`, `derive_c3.py` and `derive_ck.py` scripts are self-contained
and read no data file.

## The two derivations of the `c_k`, and their disagreement

`borel_ck.py` and `borel_ck2.py` derive the asymptotic coefficients `c_k` of
`dev_m ~ sum_k c_k w^{-(2k-1)}` symbolically. Both take the number of coefficients as their
first positional argument, so neither routes its output through the path-locating helper; both
write `cks_ck<NPAIR>.json` next to the script unless given `--out PATH`. Neither overwrites the
tracked `cks.json` by default. An earlier version did, which is how the two files below came to
differ without a record.

Three facts are recorded here and are **not** resolved:

* `cks.json` and `cks10.json` agree in `c_1..c_5` and disagree from `c_6` on.
* `borel_ck.py --out ... 6` reproduces `c_1, c_2, c_3` of `cks.json` and prints `match=False`
  for `c_4, c_5`.
* At `NPAIR = 3` the same script returns an irrational expression for `c_3`, which it gets right
  at `NPAIR = 6`. So the derivation needs `NPAIR` well above the index of the coefficient
  wanted, and the `c_4, c_5` mismatch at `NPAIR = 6` is consistent with the same truncation
  effect. That is an observation about the pattern, not a demonstration; no run at higher
  `NPAIR` has been made, and until one is, `c_6` and beyond in both JSON files are unverified.

Only `c_1 = 1/18` and `c_2 = -41/600` are independently derived elsewhere (`derive_ck.py`, and
the McMahon expansion recorded in the research log). The downstream Borel and Pade scripts use
`c_1..c_10` from `cks.json` and inherit this uncertainty; their conclusions are exploratory and
route D3.5 is closed, so nothing rests on them.
