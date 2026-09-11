# Erdős Lean remainder: completed formal results and unfinished formalizations

This repository is the canonical public home for the Erdős #503 Lean/geometry material and the finite Erdős #289 Lean fragment, alongside 73 earlier formalization attempts and three large SAT instances for `R(5,5)`.

Author: Jared Wilder. First public timestamp: 2026-09-10.

## 1. Erdős 503 — formal construction, exact values, and new geometric extensions

`lean-proofs/Erdos503.lean` is 354 lines with **0 `sorry`** and eight theorems, all with axiom footprint

```text
{propext, Classical.choice, Quot.sound}.
```

No `sorryAx`, `ofReduceBool`, or `native_decide` is used.

The main formal writeup [`ERDOS-503-ISOSCELES.md`](ERDOS-503-ISOSCELES.md) develops the orthogonal-join construction:

> **Orthogonality plus equal radii force every cross distance in the join to the common value `sqrt(2R^2)`.**

It derives superadditivity

`S(d1+d2) >= S(d1)+S(d2)`

and reproduces exact isosceles numbers in dimensions 2, 3, 6, 8, and 22.

The new companion note [`ERDOS-503-GEOMETRY-EXTENSIONS.md`](ERDOS-503-GEOMETRY-EXTENSIONS.md) adds two unconditional geometric results:

- **`f(1)=3` exactly**;
- for every `d>=2`, **`f(d) >= C(d+1,2)+1`** via the centered regular-simplex edge-midpoint construction.

The simplex-midpoint construction is a direct two-distance-set argument; every midpoint is also equidistant from the center.

## 2. Erdős 289 — finite reciprocal-sum bounds

`lean-proofs/Erdos289Head.lean` is 68 lines with **0 `sorry`**, using kernel `decide`. It proves the finite reciprocal-sum bounds F1, W4n and W4b in natural and rational forms over `[5,60]`.

The broader all-prime p-adic theorem now has its canonical compact writeup in `jaredwilder/erdos-proved-lemmas`.

## 3. Earlier formalization attempts

`formalizer-line/` contains 73 historical Lean attempts across the Erdős problem set.

- **70 contain `sorry`.**
- **3 do not contain `sorry`.**

These are formalization records rather than a curated theorem collection. Each still requires ordinary inspection of both theorem content and source fidelity.

The more curated formal material from the same research estate lives in `erdos-theorems`, `lean-forge-graph-theory`, and `erdos595-barrier-tower`.

## 4. `R(5,5)` SAT instances

`ramsey-r55/` contains three large SAT instances:

- `repair-240.cnf`
- `repair-480.cnf`
- `repair-723.cnf`

Each is about 84 MB. They are reproducible SAT instances; no solver certificate establishing a new unrestricted Ramsey bound is included here.

## Related repositories

- [erdos-proved-lemmas](https://github.com/jaredwilder/erdos-proved-lemmas) — compact proved child theorems;
- [erdos-theorems](https://github.com/jaredwilder/erdos-theorems) — 79 declarations with clean axiom-footprint accounting;
- [lean-forge-graph-theory](https://github.com/jaredwilder/lean-forge-graph-theory) — 218 sorry-free theorem files;
- [erdos595-barrier-tower](https://github.com/jaredwilder/erdos595-barrier-tower) — 27 sorry-free barrier-theorem files;
- [erdos-release-index](https://github.com/jaredwilder/erdos-release-index) — cross-repository index.

## License

Apache-2.0.
