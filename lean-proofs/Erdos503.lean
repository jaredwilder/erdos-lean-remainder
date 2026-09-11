/-
  Erdos Problem #503 -- isosceles sets in R^d.

  THE CLAIM UNDER TEST.  The Weisenberg "extra point" is the CENTRE of a sphere, and
  the Alweiss construction {e_i + e_j} is a SPHERICAL TWO-DISTANCE SET.  Therefore the
  real lower bound is not C(d+1,2)+1 but  M2s(d) + 1,  where M2s(d) is the largest
  spherical two-distance set in R^d.  Two ingredients, both formalised below:
    (1) a two-distance set is isosceles, by pure pigeonhole;
    (2) adjoining a point equidistant from all of A preserves the property.
  Delsarte-Goethals-Seidel:  M2s(d) <= d(d+3)/2.
  Blokhuis:                  iso(d) <= C(d+2,2).
  Arithmetic (3 below):      d(d+3)/2 + 1 = C(d+2,2).   <-- the two bounds MEET.
-/
import Mathlib

namespace Erdos503

open Finset
open scoped symmDiff

/-! ## Part I -- the abstract core -/

variable {E : Type*} [MetricSpace E]

/-- Every three distinct points of `A` span an isosceles triangle. -/
def Isosceles (A : Set E) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → y ≠ z → x ≠ z →
    dist x y = dist y z ∨ dist y z = dist x z ∨ dist x y = dist x z

/-- `A` realises at most the two distances `a` and `b`. -/
def TwoDistance (A : Set E) (a b : ℝ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x ≠ y → dist x y = a ∨ dist x y = b

/-- (1) PIGEONHOLE.  Three distances drawn from a two-element set must repeat. -/
theorem isosceles_of_twoDistance {A : Set E} {a b : ℝ} (h : TwoDistance A a b) :
    Isosceles A := by
  intro x hx y hy z hz hxy hyz hxz
  rcases h x hx y hy hxy with h1 | h1 <;>
    rcases h y hy z hz hyz with h2 | h2 <;>
      rcases h x hx z hz hxz with h3 | h3 <;>
        simp [h1, h2, h3]

/-- (2) THE CENTRE.  Adjoining a point equidistant from all of `A` preserves the property. -/
theorem isosceles_insert_equidistant {A : Set E} {c : E}
    (key : ∀ u ∈ A, ∀ v ∈ A, dist c u = dist c v) (hA : Isosceles A) :
    Isosceles (insert c A) := by
  intro x hx y hy z hz hxy hyz hxz
  simp only [Set.mem_insert_iff] at hx hy hz
  rcases hx with hx | hx
  · rcases hy with hy | hy
    · exact absurd (hx.trans hy.symm) hxy
    · rcases hz with hz | hz
      · exact absurd (hx.trans hz.symm) hxz
      · exact Or.inr (Or.inr (by rw [hx]; exact key y hy z hz))
  · rcases hy with hy | hy
    · rcases hz with hz | hz
      · exact absurd (hy.trans hz.symm) hyz
      · exact Or.inl (by rw [hy, dist_comm x c]; exact key x hx z hz)
    · rcases hz with hz | hz
      · exact Or.inr (Or.inl (by rw [hz, dist_comm y c, dist_comm x c]; exact key y hy x hx))
      · exact hA x hx y hy z hz hxy hyz hxz

/-- (1)+(2):  a spherical two-distance set of size `m` yields an isosceles set of size `m+1`. -/
theorem isosceles_succ_of_spherical_twoDistance [DecidableEq E]
    {A : Finset E} {c : E} {a b r : ℝ}
    (hc : c ∉ A) (h2 : TwoDistance (A : Set E) a b) (hsph : ∀ x ∈ A, dist c x = r) :
    Isosceles ((insert c A : Finset E) : Set E) ∧ (insert c A).card = A.card + 1 := by
  refine ⟨?_, Finset.card_insert_of_notMem hc⟩
  rw [Finset.coe_insert]
  refine isosceles_insert_equidistant ?_ (isosceles_of_twoDistance h2)
  intro u hu v hv
  rw [hsph u (by simpa using hu), hsph v (by simpa using hv)]

/-- (3) THE ARITHMETIC THAT MAKES THE TWO BOUNDS TOUCH: (DGS bound) + 1 = (Blokhuis bound). -/
theorem dgs_succ_eq_blokhuis (d : ℕ) : d * (d + 3) / 2 + 1 = (d + 2).choose 2 := by
  have hr : d * (d + 3) = d * (d + 1) + 2 * d := by ring
  obtain ⟨k, hk⟩ := Nat.even_mul_succ_self d
  have hdvd : d * (d + 3) = 2 * (k + d) := by rw [hr, hk]; ring
  have hs : d + 2 - 1 = d + 1 := by omega
  have h2 : (d + 2) * (d + 2 - 1) = d * (d + 3) + 2 := by rw [hs]; ring
  rw [Nat.choose_two_right, h2, hdvd]
  omega

/-! ## Part II -- a concrete spherical two-distance set of size C(n,2) -/

variable (n : ℕ)

/-- The point `e_i + e_j`, as the indicator of a 2-element set `S`. -/
noncomputable def P (S : Finset (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => if i ∈ S then (1:ℝ) else 0)

/-- The centroid of the construction: the constant vector `2/n`. -/
noncomputable def Ctr : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun _ => (2:ℝ)/n)

@[simp] lemma P_apply (S : Finset (Fin n)) (i : Fin n) :
    P n S i = if i ∈ S then (1:ℝ) else 0 := rfl

@[simp] lemma Ctr_apply (i : Fin n) : Ctr n i = (2:ℝ)/n := rfl

lemma P_injective : Function.Injective (P n) := by
  intro S T h
  ext i
  have hi : P n S i = P n T i := by rw [h]
  rw [P_apply, P_apply] at hi
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [hS, hT] at hi ⊢

/-- Squared distance between two indicator vectors is the size of the symmetric difference. -/
lemma dist_P (S T : Finset (Fin n)) :
    dist (P n S) (P n T) = Real.sqrt ((S ∆ T).card : ℝ) := by
  have h1 : ∀ i ∈ S ∆ T, dist (P n S i) (P n T i) ^ 2 = (1:ℝ) := by
    intro i hi
    rw [Finset.mem_symmDiff] at hi
    rw [P_apply, P_apply]
    rcases hi with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> simp [ha, hb, Real.dist_eq]
  have h0 : ∀ i ∈ (S ∆ T)ᶜ, dist (P n S i) (P n T i) ^ 2 = (0:ℝ) := by
    intro i hi
    rw [Finset.mem_compl, Finset.mem_symmDiff] at hi
    push_neg at hi
    rw [P_apply, P_apply]
    by_cases hS : i ∈ S
    · have hT : i ∈ T := by tauto
      simp [hS, hT]
    · have hT : i ∉ T := by tauto
      simp [hS, hT]
  have hsum : ∑ i, dist (P n S i) (P n T i) ^ 2 = ((S ∆ T).card : ℝ) := by
    rw [← Finset.sum_add_sum_compl (S ∆ T), Finset.sum_congr rfl h1,
        Finset.sum_congr rfl h0, Finset.sum_const, Finset.sum_const,
        nsmul_eq_mul, nsmul_eq_mul]
    ring
  rw [EuclideanSpace.dist_eq, hsum]

/-- Two distinct 2-element sets differ in either 2 or 4 places. -/
lemma card_symmDiff_two {S T : Finset (Fin n)}
    (hS : S.card = 2) (hT : T.card = 2) (hne : S ≠ T) :
    (S ∆ T).card = 2 ∨ (S ∆ T).card = 4 := by
  have hsub : S ∩ T ⊆ S ∪ T := (Finset.inter_subset_left).trans Finset.subset_union_left
  have hk : (S ∩ T).card ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    have e1 : S ∩ T = S :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have e2 : S ∩ T = T :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    exact hne (e1.symm.trans e2)
  have hu : (S ∪ T).card + (S ∩ T).card = 4 := by
    rw [Finset.card_union_add_card_inter, hS, hT]
  have hsd : (S ∆ T).card = (S ∪ T).card - (S ∩ T).card := by
    rw [symmDiff_eq_sup_sdiff_inf]
    simp only [Finset.sup_eq_union, Finset.inf_eq_inter]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
  omega

/-- Distance from the centroid depends only on the cardinality of `S`. -/
lemma dist_Ctr (S : Finset (Fin n)) :
    dist (Ctr n) (P n S)
      = Real.sqrt ((S.card : ℝ) * ((2:ℝ)/n - 1)^2 + (Sᶜ.card : ℝ) * ((2:ℝ)/n)^2) := by
  have hin : ∀ i ∈ S, dist (Ctr n i) (P n S i) ^ 2 = ((2:ℝ)/n - 1)^2 := by
    intro i hi; rw [Ctr_apply, P_apply, if_pos hi]; simp [Real.dist_eq, sq_abs]
  have hout : ∀ i ∈ Sᶜ, dist (Ctr n i) (P n S i) ^ 2 = ((2:ℝ)/n)^2 := by
    intro i hi
    rw [Ctr_apply, P_apply, if_neg (Finset.mem_compl.mp hi)]
    simp
  have hsum : ∑ i, dist (Ctr n i) (P n S i) ^ 2
      = (S.card : ℝ) * ((2:ℝ)/n - 1)^2 + (Sᶜ.card : ℝ) * ((2:ℝ)/n)^2 := by
    rw [← Finset.sum_add_sum_compl S, Finset.sum_congr rfl hin,
        Finset.sum_congr rfl hout, Finset.sum_const, Finset.sum_const,
        nsmul_eq_mul, nsmul_eq_mul]
  rw [EuclideanSpace.dist_eq, hsum]

/-- Every point of the construction, and the centroid, lies on the hyperplane `sum = 2`.
    (This is what lets the set be viewed inside an `(n-1)`-dimensional affine subspace.) -/
lemma sum_P (S : Finset (Fin n)) (hS : S.card = 2) : ∑ i, P n S i = 2 := by
  have hin : ∀ i ∈ S, P n S i = (1:ℝ) := fun i hi => by rw [P_apply, if_pos hi]
  have hout : ∀ i ∈ Sᶜ, P n S i = (0:ℝ) := fun i hi => by
    rw [P_apply, if_neg (Finset.mem_compl.mp hi)]
  rw [← Finset.sum_add_sum_compl S, Finset.sum_congr rfl hin, Finset.sum_congr rfl hout]
  simp [hS]

lemma sum_Ctr (hn : 0 < n) : ∑ i, Ctr n i = 2 := by
  simp only [Ctr_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-! ## The lower bound, assembled -/

/-- In `R^n` there is an isosceles set of size `C(n,2) + 1`, lying inside the
    hyperplane `sum = 2` (hence inside an affine subspace of dimension `n-1`). -/
theorem erdos503_construction (hn : 3 ≤ n) :
    ∃ A : Finset (EuclideanSpace ℝ (Fin n)),
      Isosceles (A : Set (EuclideanSpace ℝ (Fin n)))
      ∧ A.card = n.choose 2 + 1
      ∧ ∀ x ∈ A, ∑ i, x i = 2 := by
  classical
  set B : Finset (EuclideanSpace ℝ (Fin n)) :=
    (Finset.univ.powersetCard 2).image (P n) with hB
  have hmemB : ∀ x ∈ B, ∃ S, S.card = 2 ∧ x = P n S := by
    intro x hx
    rw [hB, Finset.mem_image] at hx
    obtain ⟨S, hS, rfl⟩ := hx
    exact ⟨S, (Finset.mem_powersetCard.mp hS).2, rfl⟩
  have h2 : TwoDistance (B : Set (EuclideanSpace ℝ (Fin n))) (Real.sqrt 2) (Real.sqrt 4) := by
    intro x hx y hy hxy
    obtain ⟨S, hS, rfl⟩ := hmemB x (by simpa using hx)
    obtain ⟨T, hT, rfl⟩ := hmemB y (by simpa using hy)
    have hne : S ≠ T := fun h => hxy (by rw [h])
    rcases card_symmDiff_two n hS hT hne with h | h
    · left; rw [dist_P, h]; norm_num
    · right; rw [dist_P, h]; norm_num
  have hsph : ∀ x ∈ B, dist (Ctr n) x
      = Real.sqrt ((2:ℝ) * ((2:ℝ)/n - 1)^2 + ((n:ℝ) - 2) * ((2:ℝ)/n)^2) := by
    intro x hx
    obtain ⟨S, hS, rfl⟩ := hmemB x hx
    rw [dist_Ctr, hS]
    have hcc : ((Sᶜ.card : ℕ) : ℝ) = (n:ℝ) - 2 := by
      rw [Finset.card_compl, Fintype.card_fin, hS]
      have h2n : (2:ℕ) ≤ n := by omega
      push_cast [h2n]
      ring
    rw [hcc]
    norm_num
  have hcB : Ctr n ∉ B := by
    intro hmem
    obtain ⟨S, hS, hEq⟩ := hmemB _ hmem
    have hcompl : Sᶜ.Nonempty := by
      rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin, hS]; omega
    obtain ⟨i, hi⟩ := hcompl
    have h1 : Ctr n i = P n S i := by rw [hEq]
    rw [Ctr_apply, P_apply, if_neg (Finset.mem_compl.mp hi)] at h1
    have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rcases div_eq_zero_iff.mp h1 with h | h
    · norm_num at h
    · exact hn0 h
  obtain ⟨hiso, hcard⟩ := isosceles_succ_of_spherical_twoDistance hcB h2 hsph
  refine ⟨insert (Ctr n) B, hiso, ?_, ?_⟩
  · rw [hcard, hB, Finset.card_image_of_injective _ (P_injective n),
        Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact sum_Ctr n (by omega)
    · obtain ⟨S, hS, rfl⟩ := hmemB x hx
      exact sum_P n S hS

/-! ## Part III -- THE ORTHOGONAL JOIN

  The operation that explains d = 3.  Two spherical isosceles sets of the SAME radius, sitting
  in orthogonal subspaces, join FREELY: every cross distance collapses to the single value
  `sqrt (2 R^2)`, so all four triple-types are isosceles with no side condition.  The join lands
  back on the radius-`R` sphere, so it iterates:   S(d1 + d2) >= S(d1) + S(d2).

  Kelly's 8-point set in R^3 is exactly  join(pentagon, 2 axis points) + centre  =  5 + 2 + 1.
-/

section Join

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma inner_self_eq_norm_sq' (a : F) : inner ℝ a a = ‖a‖ ^ 2 := by
  have h0 := norm_sub_sq_real a a
  simp only [sub_self, norm_zero] at h0
  linarith

omit [InnerProductSpace ℝ F] in
/-- A union of two same-radius sets stays on the sphere: the join ITERATES. -/
lemma onSphere_union {A B : Set F} {R : ℝ}
    (hA : ∀ a ∈ A, ‖a‖ = R) (hB : ∀ b ∈ B, ‖b‖ = R) :
    ∀ x ∈ A ∪ B, ‖x‖ = R := by
  rintro x (hx | hx)
  · exact hA x hx
  · exact hB x hx

/-- THE ORTHOGONAL JOIN.  No side condition: orthogonality plus equal radii force EVERY
    cross distance to the single value `sqrt (2 R^2)`. -/
theorem isosceles_orthogonal_join {A B : Set F} {R : ℝ}
    (hA : ∀ a ∈ A, ‖a‖ = R) (hB : ∀ b ∈ B, ‖b‖ = R)
    (horth : ∀ a ∈ A, ∀ b ∈ B, inner ℝ a b = (0:ℝ))
    (hIA : Isosceles A) (hIB : Isosceles B) :
    Isosceles (A ∪ B) := by
  have hcross : ∀ a ∈ A, ∀ b ∈ B, dist a b = Real.sqrt (2 * R ^ 2) := by
    intro a ha b hb
    have h : ‖a - b‖ ^ 2 = 2 * R ^ 2 := by
      rw [norm_sub_sq_real, hA a ha, hB b hb, horth a ha b hb]; ring
    rw [dist_eq_norm, ← h, Real.sqrt_sq (norm_nonneg _)]
  have hcross' : ∀ b ∈ B, ∀ a ∈ A, dist b a = Real.sqrt (2 * R ^ 2) := by
    intro b hb a ha; rw [dist_comm]; exact hcross a ha b hb
  intro x hx y hy z hz hxy hyz hxz
  simp only [Set.mem_union] at hx hy hz
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz
  · exact hIA x hx y hy z hz hxy hyz hxz
  · exact Or.inr (Or.inl (by rw [hcross y hy z hz, hcross x hx z hz]))
  · exact Or.inl (by rw [hcross x hx y hy, hcross' y hy z hz])
  · exact Or.inr (Or.inr (by rw [hcross x hx y hy, hcross x hx z hz]))
  · exact Or.inr (Or.inr (by rw [hcross' x hx y hy, hcross' x hx z hz]))
  · exact Or.inl (by rw [hcross' x hx y hy, hcross y hy z hz])
  · exact Or.inr (Or.inl (by rw [hcross' y hy z hz, hcross' x hx z hz]))
  · exact hIB x hx y hy z hz hxy hyz hxz

/-- JOIN, THEN ADD THE CENTRE.  With `A` = regular pentagon (radius R in a plane) and
    `B` = the two axis points at `±R`, this is precisely Kelly's 8-point set in `R^3`. -/
theorem isosceles_join_insert_center {A B : Set F} {R : ℝ}
    (hA : ∀ a ∈ A, ‖a‖ = R) (hB : ∀ b ∈ B, ‖b‖ = R)
    (horth : ∀ a ∈ A, ∀ b ∈ B, inner ℝ a b = (0:ℝ))
    (hIA : Isosceles A) (hIB : Isosceles B) :
    Isosceles (insert 0 (A ∪ B)) := by
  refine isosceles_insert_equidistant ?_ (isosceles_orthogonal_join hA hB horth hIA hIB)
  intro u hu v hv
  rw [dist_zero_left, dist_zero_left, onSphere_union hA hB u hu, onSphere_union hA hB v hv]

lemma disjoint_of_orthogonal {A B : Finset F} {R : ℝ} (hR : R ≠ 0)
    (hA : ∀ a ∈ A, ‖a‖ = R)
    (horth : ∀ a ∈ A, ∀ b ∈ B, inner ℝ a b = (0:ℝ)) :
    Disjoint A B := by
  rw [Finset.disjoint_left]
  intro a ha hb
  have h := horth a ha a hb
  rw [inner_self_eq_norm_sq' a, hA a ha] at h
  exact hR (by simpa using h)

/-- SUPERADDITIVITY, with cardinality:  S(d1+d2) >= S(d1) + S(d2), and iso >= S + 1. -/
theorem card_join_insert_center [DecidableEq F] {A B : Finset F} {R : ℝ} (hR : R ≠ 0)
    (hA : ∀ a ∈ A, ‖a‖ = R) (hB : ∀ b ∈ B, ‖b‖ = R)
    (horth : ∀ a ∈ A, ∀ b ∈ B, inner ℝ a b = (0:ℝ))
    (hIA : Isosceles (A : Set F)) (hIB : Isosceles (B : Set F)) :
    Isosceles ((insert 0 (A ∪ B) : Finset F) : Set F)
      ∧ (insert 0 (A ∪ B)).card = A.card + B.card + 1 := by
  classical
  have hA' : ∀ a ∈ (A : Set F), ‖a‖ = R := by intro a ha; exact hA a (by simpa using ha)
  have hB' : ∀ b ∈ (B : Set F), ‖b‖ = R := by intro b hb; exact hB b (by simpa using hb)
  have ho' : ∀ a ∈ (A : Set F), ∀ b ∈ (B : Set F), inner ℝ a b = (0:ℝ) := by
    intro a ha b hb; exact horth a (by simpa using ha) b (by simpa using hb)
  have hzero : (0:F) ∉ A ∪ B := by
    intro hmem
    rcases Finset.mem_union.mp hmem with h | h
    · exact hR (by simpa using (hA 0 h).symm)
    · exact hR (by simpa using (hB 0 h).symm)
  refine ⟨?_, ?_⟩
  · rw [Finset.coe_insert, Finset.coe_union]
    exact isosceles_join_insert_center hA' hB' ho' hIA hIB
  · rw [Finset.card_insert_of_notMem hzero,
        Finset.card_union_of_disjoint (disjoint_of_orthogonal hR hA horth)]

end Join

end Erdos503

-- No sorries, no extra axioms: machine-checked.
#print axioms Erdos503.isosceles_of_twoDistance
#print axioms Erdos503.isosceles_insert_equidistant
#print axioms Erdos503.isosceles_succ_of_spherical_twoDistance
#print axioms Erdos503.dgs_succ_eq_blokhuis
#print axioms Erdos503.erdos503_construction
#print axioms Erdos503.isosceles_orthogonal_join
#print axioms Erdos503.isosceles_join_insert_center
#print axioms Erdos503.card_join_insert_center
