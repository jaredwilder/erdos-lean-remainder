# Erdős #503 — exact `f(1)=3` and a quadratic simplex-midpoint construction

Author: Jared Wilder. Public release: 2026-09-11.

Let `f(d)` be the largest size of a finite point set in `R^d` such that every triple of distinct points determines an isosceles triangle.

## Exact one-dimensional value

`f(1)=3`.

Three equally spaced points attain 3. For the upper bound, suppose `a1<a2<a3<a4`. For either interior point `ai`, the triple `(a1,ai,a4)` has longest side `a4-a1`; being isosceles therefore forces

`ai-a1 = a4-ai`,

so both interior points equal the midpoint `(a1+a4)/2`, a contradiction.

## Quadratic construction in every dimension

For every `d>=2`,

`f(d) >= C(d+1,2)+1`.

Take a centered regular `d`-simplex with vertices `u_1,...,u_{d+1}`. Include every edge midpoint

`m_ij=(u_i+u_j)/2`

and the center `0`.

The midpoint set is a two-distance set: the distance between two edge midpoints depends only on whether the corresponding simplex edges share a vertex or are disjoint. Therefore every triangle of midpoints is isosceles. All midpoints are also equidistant from the center, so every triangle containing the center and two midpoints is isosceles.

The resulting set has exactly `C(d+1,2)+1` points.

For `d=2`, the separate pentagon-plus-center construction gives the stronger value 6. The existing [`ERDOS-503-ISOSCELES.md`](ERDOS-503-ISOSCELES.md) contains the kernel-clean orthogonal-join development and exact values in dimensions 2, 3, 6, 8, and 22.

Historical novelty of the simplex-midpoint formulation is a separate literature question.
