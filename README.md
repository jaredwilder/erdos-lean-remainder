# Erdős Lean remainder: two completed proofs and unfinished formalizations

This repository contains **two completed kernel-clean Lean developments**—an Erdős 503 orthogonal-join construction with exact isosceles numbers, and a finite reciprocal-sum bound for Erdős 289—alongside 73 earlier statement/proof attempts and three large SAT instances for `R(5,5)`.

Author: Jared Wilder. First public timestamp: 2026-09-10.

## 1. Erdős 503: orthogonal joins and exact isosceles numbers

`lean-proofs/Erdos503.lean` is 354 lines with **0 `sorry`** and eight theorems, all with axiom footprint

```text
{propext, Classical.choice, Quot.sound}.
```

No `sorryAx`, `ofReduceBool`, or `native_decide` is used.

The accompanying writeup [`ERDOS-503-ISOSCELES.md`](ERDOS-503-ISOSCELES.md) develops the central construction:

> **Orthogonality plus equal radii force every cross distance in the join to the common value `sqrt(2R^2)`.**

From this the file derives superadditivity

```text
S(d1+d2) >= S(d1)+S(d2)
```

and reproduces the following exact isosceles numbers:

| d | iso(d) | construction |
|---|---:|---|
| 2 | **6** | pentagon plus centre (Kelly) |
| 3 | **8** | pentagon + two axis points + centre (Croft/Kelly) |
| 6 | **28** | Schläfli 27 plus centre |
| 8 | **45** | 45-point two-distance set in `R^8` |
| 22 | **276** | McLaughlin 275 plus centre |

It also proves that the Delsarte–Goethals–Seidel and Blokhuis bounds differ by exactly 1:

```text
d(d+3)/2 + 1 = C(d+2,2).
```

The `d=22` value was not found in the limited literature sources checked for this release; that observation is not a comprehensive priority search. Independent numerical checks include all 3,654 triples at `d=8`.

## 2. Erdős 289: finite reciprocal-sum bounds

`lean-proofs/Erdos289Head.lean` is 68 lines with **0 `sorry`**, using kernel `decide`. It proves the finite reciprocal-sum bounds F1, W4n and W4b in natural and rational forms over the range `[5,60]`.

## 3. Earlier formalization attempts

`formalizer-line/` contains 73 historical Lean attempts across the Erdős problem set.

- **70 contain `sorry`.**
- **3 do not contain `sorry`.**

These files are useful as formalization records, not as a curated theorem collection. Absence of `sorry` alone is not enough to establish that a statement is mathematically substantive or faithful to its source; each file still needs ordinary theorem/source inspection.

The more curated formal material from the same research estate lives in `erdos-theorems`, `lean-forge-graph-theory`, and `erdos595-barrier-tower`.

## 4. `R(5,5)` SAT instances

`ramsey-r55/` contains three large SAT instances:

- `repair-240.cnf`
- `repair-480.cnf`
- `repair-723.cnf`

Each is about 84 MB and stored in a DRAT/LRAT-adjacent workflow format.

They are **reproducible SAT instances**, not checked proofs of a new Ramsey bound. No solver certificate establishing a new `R(5,5)` result is included here.

## Related repositories

For curated formal mathematics:

- [erdos-theorems](https://github.com/jaredwilder/erdos-theorems) — 79 declarations with clean axiom-footprint accounting;
- [lean-forge-graph-theory](https://github.com/jaredwilder/lean-forge-graph-theory) — 218 sorry-free theorem files;
- [erdos595-barrier-tower](https://github.com/jaredwilder/erdos595-barrier-tower) — 27 sorry-free barrier-theorem files;
- [erdos-release-index](https://github.com/jaredwilder/erdos-release-index) — cross-repository index.

## License

Apache-2.0.