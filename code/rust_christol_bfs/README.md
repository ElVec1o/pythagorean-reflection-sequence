# rust_christol_bfs

Rust implementation of the **Christol mod-p BFS** on the universal
orbit-growth state space `Q ⋉ M_p` from the Bonfioli universality paper (v8.2).

This is a clean, self-contained port of the algorithm in
`code/g_modules/G12_modp_bfs.py` (and `G43_christol_modp.py`), tuned for the
24 GB Mac mini M4. Roughly **300-400× faster** than the Python at the same
depth, with a much smaller per-state memory footprint.

## What the BFS computes

For each prime `p`, the BFS enumerates the distinct states reachable by
applying the three Bonfioli generators `R_0, R_1, R_2` starting from the
identity, where two states are identified iff they agree on
`(sign, lstr, trans mod p)` — i.e. the natural projection of the integer
algebraic state space onto its mod-p quotient.

The layer sizes `|S_p(d)|` give a growth signature:

- **Saturated** (finite, e.g. `p=2` → 4): mod-p generating function is rational.
- **Polynomial**: mod-p generating function is algebraic of some degree.
- **Exponential**: mod-p Christol state space is **infinite**, which is
  strongly suggestive of transcendence of `U(t)` over `Q(t)` (and hence
  generic transcendence of `β_2`).

## Build

```bash
cd code/rust_christol_bfs
cargo build --release
```

## Run

```bash
# Quick sanity + depth 35 (~ 20 s, ~ 2 GB):
./target/release/christol_bfs --prime 3 --max-depth 35

# Overnight target (depth 50+, multi-GB):
./target/release/christol_bfs \
    --prime 3 \
    --max-depth 100 \
    --snapshot-dir /tmp/christol_p3 \
    > /tmp/christol_p3.log 2>&1 &
tail -f /tmp/christol_p3.log
```

CLI flags:

| flag             | default        | meaning                                  |
|------------------|---------------|------------------------------------------|
| `--prime P`      | 3             | prime to BFS modulo                      |
| `--max-depth D`  | 100           | hard depth cap                           |
| `--seen-cap N`   | 200,000,000   | abort if `|seen|` exceeds N              |
| `--time-cap S`   | 43,200 (12 h) | abort after S seconds                    |
| `--snapshot-dir` | none          | writes `snapshot_pP.json` after each layer |

## Built-in sanity checks

Every run executes three checks before the main BFS:

1. **mod 251, d ≤ 10** must equal `[1,3,5,8,13,21,34,55,89,144,225]`
   (matches `U_EXACT[0..=10]` from the paper — no mod-collisions yet).
2. **mod 2, d ≤ 10** must equal `[1,3,5,5,4,4,4,4,4,4,4]` (saturates at 4).
3. **mod 3, d ≤ 10** must equal `[1,3,5,8,13,21,34,55,89,141,216]`.

(Note: at `p=3`, depths 9 and 10 are 141 / 216 respectively, **not**
144 / 225 — the integer values. The mod-3 quotient already identifies 3
states by depth 9 and 9 states by depth 10. This is expected and
matches `G12_modp_bfs.json`.)

If sanity fails, the binary aborts before doing any real work.

## Output

Final line of stdout is a single-line JSON record:

```json
{"prime":3,"max_depth_reached":35,"state_counts":[1,3,5,...,4596666],
 "wall_s":16.62,"aborted":false,"abort_reason":"",
 "growth_fit":{"type":"exponential","rate":1.4763}}
```

`growth_fit.type` ∈ `{"saturated","polynomial","exponential","ambiguous"}`.
The classifier compares log-linear vs power-law tail fits (R² with a
0.005 margin) on the upper half of the data, after the first 5 layers.

## Interpretation guide

| `growth_fit.type` | Meaning for transcendence                                       |
|---|---|
| `saturated`    | Finite mod-p automaton → `U(t) mod p` is rational. Weak signal. |
| `polynomial`   | Algebraic mod-p of some finite degree. No transcendence signal. |
| `exponential`  | **Strongest signal**: mod-p Christol state space appears infinite, consistent with `U(t)` transcendental over `Q(t)`. |
| `ambiguous`    | Insufficient depth — push deeper.                                |

For `p = 2`: saturates at 4 — no signal.
For `p = 3, 5, 7`: empirically exponential (see paper §G43).

## Caveat (same as in the paper)

`|S_p(d)|` is the size of the BFS-state-space **lift** mod p, not the
p-kernel of the sequence `(u_d mod p)` itself. Exponential growth of the
lift is **strongly suggestive** of transcendence but is not a proof: in
principle, massive cancellation across distinct lifted states could
collapse the underlying mod-p sequence to a p-automatic one whose lift
grows exponentially. Bridging the lift-vs-kernel gap is the remaining
hard step — see `paper/paper.tex` §HANDOFF.
