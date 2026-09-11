# erdos-lean-remainder

The last of the Lean material: two finished standalone proofs, 73 formalization attempts of which
**70 still contain `sorry`**, and three SAT repair certificates for R(5,5).

Author: Jared Wilder. First public timestamp: 2026-09-10.

## Two finished proofs

`lean-proofs/Erdos503.lean` — 354 lines, **0 `sorry`**, a complete multi-part proof. Every 3-point
set of bounded diameter spanning only two distinct distances yields at most C(d+2, 2) points.

`lean-proofs/Erdos289Head.lean` — 68 lines, **0 `sorry`**, using `decide +kernel`. Reciprocal-sum
bounds F1 and the W4n and W4b forms in pure naturals and in rationals, exhaustive over [5, 60].

## 73 formalization attempts, and the number that matters

`formalizer-line/` holds `erdos-1.lean` through `erdos-146.lean` plus scratch files.

**70 of the 73 contain `sorry`. Three do not.**

These are the daemon's attempts at formalizing statements across the Erdos frontier. They are
published because the attempt record is the point: it shows which problems a formalizer can even
state cleanly and where it stalls. **None of them proves anything, and the three without `sorry`
should be read before being believed** — a file without `sorry` may still be stating something
trivial.

## R(5,5) repair certificates

`ramsey-r55/` holds `repair-240.cnf`, `repair-480.cnf` and `repair-723.cnf`, three SAT instances at
84 MB each, in DRAT/LRAT-adjacent form.

**These are artifacts, not a Ramsey result.** R(5,5) is famously open; the literature bracket is
roughly 43 to 48 and nothing here moves it. The certificates are published as reproducible SAT
instances, and any claim attached to them would have to come from a solver run that is not included
here.

## Where the finished work is

The clean, audited, kernel-verified material is elsewhere:
[erdos-theorems](https://github.com/jaredwilder/erdos-theorems) for 79 clean-axiom declarations,
[lean-forge-graph-theory](https://github.com/jaredwilder/lean-forge-graph-theory) for 218 sorry-free
files, [erdos595-barrier-tower](https://github.com/jaredwilder/erdos595-barrier-tower) for 27, and
the index at
[erdos-release-index](https://github.com/jaredwilder/erdos-release-index).

This repository is the tail: what was attempted, what was left unfinished, and what was generated
but never adjudicated.

## License

Apache-2.0.
