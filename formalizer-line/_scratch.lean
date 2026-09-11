/- 
No corrected file exists: `witness_pos` is false as stated.

For any `p : Fin 4 → Point` and distinct `i j : Fin 4`, both `i` and `j` satisfy
`collinear p i j`, so:

  2 ≤ (lineThrough p i j).card

But `atMostOnALine 4 3 p` requires:

  (lineThrough p i j).card ≤ 4 - 3

that is, `card ≤ 1`, a contradiction. Removing `open scoped Classical` would only expose this genuine contradiction; it cannot make `decide` prove the false proposition.
-/