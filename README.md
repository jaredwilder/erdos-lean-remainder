# erdos-lean-remainder

The last of the Lean material: two finished standalone proofs, 73 formalization attempts of which
**70 still contain `sorry`**, and three SAT repair certificates for R(5,5).

Author: Jared Wilder. First public timestamp: 2026-09-10.

## Two finished proofs

`lean-proofs/Erdos503.lean` — 354 lines, **0 `sorry`**, a complete multi-part proof, **8 of 8
theorems with footprint `{propext, Classical.choice, Quot.sound}`** and no `sorryAx`, no
`ofReduceBool`, no `native_decide`.

**What it actually proves is written up in [ERDOS-503-ISOSCELES.md](ERDOS-503-ISOSCELES.md),** which
was sitting unpublished while only the bare Lean file shipped. The centrepiece is an orthogonal
join: **orthogonality plus equal radii force every cross distance to the single value `sqrt(2R^2)`,
with no side condition.** From it the file derives superadditivity `S(d1+d2) >= S(d1)+S(d2)`, and
these exact isosceles numbers:

| d | iso(d) | route |
|---|---|---|
| 2 | **6** | pentagon plus centre (Kelly), reproduced from the mechanism rather than looked up |
| 3 | **8** | join(pentagon, two axis points) plus centre = 5+2+1 (Croft/Kelly), reproduced |
| 6 | **28** | Schlafli 27 plus centre = C(8,2) |
| 8 | **45** | 45-point two-distance set in R^8 = C(10,2), no centre needed |
| 22 | **276** | McLaughlin 275 plus centre = C(24,2) |

It also proves the DGS and Blokhuis bounds differ by **exactly 1**: `d(d+3)/2 + 1 = C(d+2,2)`.

The write-up notes that d = 22 is not listed in Ionin, *Isosceles Sets* (EJC 2009), which records
sharpness at n = 1, 2, 6, 8, nor on erdosproblems.com/503 -- and then says in its own words:
**"No novelty claim is made -- two web sources is not a literature search."** Numeric cross-checks
independent of Lean are included, including 3,654 of 3,654 clean triples at n = 8.

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
