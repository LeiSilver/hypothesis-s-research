import Lean

/-! Negating a slope and its offset preserves the local roots.
The statement allows any representative of the negated slope. -/

set_option autoImplicit false

namespace HypothesisS

def signedProgressionValue (slope offset argument : Int) : Int :=
  2 * slope * argument + offset

theorem signed_progression_root (modulus slope offset argument lift : Int) :
    modulus ∣ signedProgressionValue (-slope + lift * modulus) (-offset) argument ↔
      modulus ∣ signedProgressionValue slope offset argument := by
  have hSum :
      signedProgressionValue (-slope + lift * modulus) (-offset) argument +
        signedProgressionValue slope offset argument = modulus * (2 * lift * argument) := by
    unfold signedProgressionValue
    grind
  constructor
  · rintro ⟨quotient, hQuotient⟩
    refine ⟨2 * lift * argument - quotient, ?_⟩
    rw [Int.mul_sub, ← hQuotient]
    omega
  · rintro ⟨quotient, hQuotient⟩
    refine ⟨2 * lift * argument - quotient, ?_⟩
    rw [Int.mul_sub, ← hQuotient]
    omega

theorem signed_progression_constant (modulus slope lift : Int) :
    modulus ∣ 2 * (-slope + lift * modulus) ↔ modulus ∣ 2 * slope := by
  simpa [signedProgressionValue] using signed_progression_root modulus slope 0 1 lift

theorem slope_residue_reflection (modulus n offset b period : Int)
    (hPeriod : modulus ∣ n * period) :
    modulus ∣ n * b + offset ↔ modulus ∣ n * (period - b) - offset := by
  have hSum : (n * b + offset) + (n * (period - b) - offset) = n * period := by
    rw [Int.mul_sub]
    omega
  constructor
  · intro hFirst
    have hSecond : n * (period - b) - offset = n * period - (n * b + offset) := by
      omega
    rw [hSecond]
    exact Int.dvd_sub hPeriod hFirst
  · intro hSecond
    have hFirst : n * b + offset = n * period - (n * (period - b) - offset) := by
      omega
    rw [hFirst]
    exact Int.dvd_sub hPeriod hSecond

#print axioms signed_progression_root
#print axioms signed_progression_constant
#print axioms slope_residue_reflection

end HypothesisS
