import Lean

/-! Exponent comparisons for the CRT density of two simultaneous
progressions when one squarefree prime factor is added. -/

set_option autoImplicit false

namespace HypothesisS

def progressionExponent (q base extra : Nat) : Nat :=
  max q (max base extra)

def progressionCompatible (q base extra shift : Nat) : Prop :=
  min q (max base extra) ≤ shift

/-- One extra prime either leaves the period unchanged or adds one exponent. -/
theorem progression_exponent_step (q base extra : Nat) :
    progressionExponent q base extra ≤ progressionExponent q base (extra + 1) ∧
      progressionExponent q base (extra + 1) ≤ progressionExponent q base extra + 1 := by
  unfold progressionExponent
  omega

/-- A prime already in the divisibility condition does not change it. -/
theorem prime_already_in_base_is_redundant (q base shift : Nat) (hBase : 0 < base) :
    progressionExponent q base 1 = progressionExponent q base 0 ∧
      (progressionCompatible q base 1 shift ↔ progressionCompatible q base 0 shift) := by
  have hOne : 1 ≤ base := by omega
  simp [progressionExponent, progressionCompatible, Nat.max_eq_left hOne]

/-- For a prime in the modulus with a nonunit shift, the period is unchanged. -/
theorem divisor_prime_at_nonunit_shift (q shift : Nat) (hQ : 0 < q) (hShift : 0 < shift) :
    progressionExponent q 0 1 = q ∧ progressionCompatible q 0 1 shift := by
  have hOne : 1 ≤ q := by omega
  simp [progressionExponent, progressionCompatible, Nat.max_eq_left hOne,
    Nat.min_eq_right hOne, show 1 ≤ shift by omega]

theorem divisor_prime_at_unit_shift_is_incompatible (q : Nat) (hQ : 0 < q) :
    ¬ progressionCompatible q 0 1 0 := by
  have hOne : 1 ≤ q := by omega
  simp [progressionCompatible, Nat.min_eq_right hOne]

#print axioms progression_exponent_step
#print axioms prime_already_in_base_is_redundant
#print axioms divisor_prime_at_nonunit_shift
#print axioms divisor_prime_at_unit_shift_is_incompatible

end HypothesisS
