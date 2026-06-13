# `paper/OEIS/` — OEIS submission drafts

| Path | Role |
|---|---|
| `clean/` | **Canonical** drafts in OEIS `%`-field format (the source of truth for the math: data, g.f., recurrence, growth-rate polynomial, cross-refs). |
| `submit/` | **Paste-ready handoff** — one file per submission split per web-form field, plus `README_AGENT.md` with the staggered submission order and the editor rules (full author name, ~25-term DATA, no redundant b-file, recurrence-index link). |
| `b396406_depth42.txt` | Live b-file extension for the published **A396406** (terms 0..42). |

## Status

- **A396406** (2D, the universal sequence) — **published**.
- **A396927** (5D Class C) — **published**.
- 4D / 6D / 3D Class C / 3D Class B — prepared in `submit/`, to be filed on a
  stagger (lead 5D is done; then 4D, 6D; then 3D-C; then 3D-B standalone).
- 3D cube corner `(1,1,1)` — **dropped**: it is a duplicate of
  [A008137](https://oeis.org/A008137) (affine Weyl group B̃₃ growth series).

Earlier flat staging copies (`A_*.txt`, `b_A_*.txt`) were removed: they had
drifted out of sync with `clean/` and were the source of repeated transcription
errors. Edit `clean/` only; regenerate `submit/` blocks from it.
