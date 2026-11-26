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

#print axioms signed_progression_root
#print axioms signed_progression_constant

end HypothesisS
