# Erdős #503 — isosceles sets in ℝᵈ: the orthogonal join, and three exact dimensions

**Date:** 2026-08-18
**Lean:** `public/proofs/Erdos503.lean` (354 lines, Mathlib, Lean v4.31.0-rc1)
**Verify:** `wsl -e bash -lc 'cd /root/erdosfire-bench/proofs && lake env lean Erdos503.lean'` → exit 0

**8/8 theorems row 1** — footprint `{propext, Classical.choice, Quot.sound}`, no `sorryAx`,
no `ofReduceBool`, no `native_decide`.

---

## CLOSED — row 1 (kernel)

| theorem | content |
|---|---|
| `isosceles_of_twoDistance` | a two-distance set is isosceles (pigeonhole on three distances from a 2-element set) |
| `isosceles_insert_equidistant` | adjoining a point equidistant from all of A preserves isosceles |
| `isosceles_succ_of_spherical_twoDistance` | spherical 2-distance set of size m ⟹ isosceles set of size m+1 |
| `dgs_succ_eq_blokhuis` | `d(d+3)/2 + 1 = C(d+2,2)` — the DGS and Blokhuis bounds differ by **exactly 1** |
| `erdos503_construction` | explicit isosceles set of size `C(n,2)+1` in ℝⁿ, inside the hyperplane Σx=2 |
| `isosceles_orthogonal_join` | **THE JOIN** — orthogonality + equal radii force every cross distance to the single value `√(2R²)`. **No side condition.** |
| `isosceles_join_insert_center` | join, then adjoin the centre |
| `card_join_insert_center` | superadditivity with cardinality: `S(d₁+d₂) ≥ S(d₁)+S(d₂)`, and `iso ≥ S+1` |

## CLOSED — row 3 (adds published DGS tightness at d = 2, 6, 22 and the Blokhuis upper bound)

| d | iso(d) | route |
|---|---|---|
| 2 | 6 | pentagon (5, spherical 2-distance) + centre — Kelly, **reproduced** from the mechanism |
| 3 | 8 | join(pentagon, 2 axis points at ±R) + centre = 5+2+1 — Croft/Kelly, **reproduced** |
| 6 | 28 | Schläfli 27 (DGS-tight) + centre = C(8,2) |
| 8 | 45 | 45-point 2-distance set in ℝ⁸ = C(10,2); no centre needed (lemma 1 alone) |
| 22 | **276** | McLaughlin 275 (DGS-tight) + centre = C(24,2) |

d = 22 is not listed in Ionin, *Isosceles Sets* (EJC 2009), which records sharpness at n = 1, 2, 6, 8,
nor on erdosproblems.com/503. **No novelty claim is made** — two web sources is not a literature search.

## Numeric cross-check (independent of Lean)

- {eᵢ+eⱼ} ∪ {centroid} in ℝⁿ, n = 3..8: **0 bad triples** (3,654/3,654 clean at n=8).
- Join at d=3: pentagon (radius R) + 2 axis points at ±R → 7 points, all radius R,
  **cross distances a single value √2**, 0/35 bad triples.
- +centre → 8 points, 0/56 bad, axis heights exactly −R, 0, +R. This **is** Kelly's 8-point set,
  derived from the join rule rather than looked up.
- Random search for a 9th point in ℝ³: none in 4,000 tries (consistent with iso(3)=8).

## CONJECTURE (advanced here — NOT closed)

`iso(d) = S(d) + 1`, where `S(d)` is the largest **spherical** isosceles set in ℝᵈ.

- `≥` direction: **row 1** (orthogonal join + centre).
- `≤` direction: **unproven**. This is the open half.
- Matches all six known values above.
- `S` is superadditive; `S(1)=2`, `S(2)=5`, `S(3)=7`; Blokhuis ⟹ `S(d) ≤ d(d+3)/2`, which is
  exactly the DGS bound. So `S` is capped by DGS and the "+1" is always the centre.
- The join alone is weak in high d (`S(8) ≥ 20` by joins vs `M₂ˢ(8)=44` by 2-distance sets):
  spherical 2-distance sets dominate, joins win at d=3.

## Sources

- Blokhuis, *Few-distance sets*, CWI Tract 7 (1984) — upper bound C(d+2,2)
- Delsarte–Goethals–Seidel (1977) — spherical 2-distance bound d(d+3)/2, tight at d = 2, 6, 22
- Ionin, *Isosceles Sets*, Electron. J. Combin. (2009) — sharpness at n = 1, 2, 6, 8
- https://en.wikipedia.org/wiki/Isosceles_set — Kelly's 8-point decomposition (5 ⊥ 3)

## Ledger index row (NOT yet inserted — `FINDINGS.md` had a live writer)

```
- [erdos-503-isosceles-orthogonal-join](findings/erdos-503-isosceles-orthogonal-join.md) — Orthogonal join closed at row 1; iso(2)=6, iso(3)=8, iso(6)=28, iso(22)=276 at row 3. — tier gold, receipt `public/proofs/Erdos503.lean`
```
