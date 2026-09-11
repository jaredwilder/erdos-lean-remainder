import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open scoped BigOperators

/-
  Erdos problem 265.  The source contains the numerical literals
  1, 2, 3, 5, 6, 12, 21, 24, 64, 80, 88, 104, 2026, and 30.
  It also contains the expressions n ≥ 2, a_n^(1/n), a_n^(1/2^n),
  and a_n^(1/β^n), with β > 1.
-/

def IsIncreasingIntegerSequence (a : ℕ → ℕ) : Prop :=
  1 ≤ a 0 ∧ ∀ n : ℕ, a n < a (n + 1)

def HasRationalReciprocalSums (a : ℕ → ℕ) : Prop :=
  Summable (fun n : ℕ => ((a n : ℝ)⁻¹)) ∧
    Summable (fun n : ℕ => ((a n : ℝ) - 1)⁻¹) ∧
    ∃ p q : ℚ,
      tsum (fun n : ℕ => ((a n : ℝ)⁻¹)) = (p : ℝ) ∧
      tsum (fun n : ℕ => ((a n : ℝ) - 1)⁻¹) = (q : ℝ)

def LimsupAboveOne (u : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 1 < c ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ c < u n

def FiniteRationalWitness (s : Finset ℕ) (p q : ℚ) : Prop :=
  (∀ x ∈ s, 1 < x) ∧
    (s.sum (fun x => (1 : ℚ) / (x : ℚ)) = p) ∧
    (s.sum (fun x => (1 : ℚ) / ((x - 1 : ℕ) : ℚ)) = q)

theorem witness_pos :
    FiniteRationalWitness ({2} : Finset ℕ) (1 / 2 : ℚ) 1 := by
  norm_num [FiniteRationalWitness]

theorem witness_neg :
    ¬ FiniteRationalWitness ({2} : Finset ℕ) 0 0 := by
  norm_num [FiniteRationalWitness]

/-
  This is the open limiting-growth assertion recorded for the problem:
  the two reciprocal series are rational, while the sequence has
  limsup a_n^(1/2^n) > 1.
-/
theorem erdos_problem_265_conjecture :
    ∃ a : ℕ → ℕ,
      IsIncreasingIntegerSequence a ∧
        HasRationalReciprocalSums a ∧
          LimsupAboveOne
            (fun n : ℕ =>
              Real.rpow (a n : ℝ) (1 / ((2 : ℝ) ^ n))) := by
  sorry

end