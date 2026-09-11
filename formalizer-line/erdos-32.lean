import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open Filter
open scoped Topology

/-- The counting function for a set of natural numbers. -/
noncomputable def counting (A : Set ℕ) (N : ℕ) : ℝ := by
  classical
  exact
    ((Finset.filter (fun n => n ∈ A) (Finset.Icc 1 N)).card : ℝ)

/-- Every sufficiently large natural number is a prime plus an element of `A`. -/
def hasPrimeRepresentation (A : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∃ p a : ℕ, Nat.Prime p ∧ a ∈ A ∧ n = p + a

/-- The `o((log N)^2)` sparsity condition. -/
def littleLogSquare (A : Set ℕ) : Prop :=
  (fun N : ℕ => counting A N) =o[atTop]
    (fun N : ℕ => (Real.log (N : ℝ)) ^ 2)

/-- The `O(log N)` sparsity condition. -/
def bigLog (A : Set ℕ) : Prop :=
  (fun N : ℕ => counting A N) =O[atTop]
    (fun N : ℕ => Real.log (N : ℝ))

/-- The lower-limit condition appearing in the third question. -/
def lowerLimitAboveOne (A : Set ℕ) : Prop :=
  1 < Filter.liminf (fun N : ℕ => counting A N / Real.log (N : ℝ)) atTop

/--
The conjunction of the three questions:
existence with `o((log N)^2)` growth, existence with `O(log N)` growth,
and whether every set with the representation property has lower limit
strictly greater than `1`.
-/
def Question : Prop :=
  (∃ A : Set ℕ, littleLogSquare A ∧ hasPrimeRepresentation A) ∧
  (∃ A : Set ℕ, bigLog A ∧ hasPrimeRepresentation A) ∧
  (∀ A : Set ℕ, hasPrimeRepresentation A → lowerLimitAboveOne A)

/--
A finite, decidable toy version of the representation property, used only
to provide concrete positive and negative witnesses.
-/
def toyCoversUpTo (A : Finset ℕ) (N : ℕ) : Prop :=
  ∀ n ∈ Finset.Icc 2 N,
    ∃ p ∈ Finset.Icc 2 n,
      Nat.Prime p ∧ ∃ a ∈ A, n = p + a

def toySparseCover (A : Finset ℕ) (N : ℕ) : Prop :=
  A.card ≤ 1 ∧ toyCoversUpTo A N

theorem witness_pos : toySparseCover ({0} : Finset ℕ) 3 := by
  constructor
  · simp
  · intro n hn
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn3 : n ≤ 3 := (Finset.mem_Icc.mp hn).2
    have hcases : n = 2 ∨ n = 3 := by omega
    rcases hcases with rfl | rfl
    · refine ⟨2, by simp, by norm_num, 0, by simp, by norm_num⟩
    · refine ⟨3, by simp, by norm_num, 0, by simp, by norm_num⟩

theorem witness_neg : ¬ toySparseCover (∅ : Finset ℕ) 3 := by
  intro h
  rcases h with ⟨_, hcover⟩
  have hh := hcover 2 (by simp)
  rcases hh with ⟨p, hp, hprime, a, ha, heq⟩
  simpa using ha

theorem answer : Question := by
  sorry

end