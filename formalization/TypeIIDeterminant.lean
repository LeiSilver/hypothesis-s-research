import Lean

/-! The determinant of two affine values detects common factors.
An invertible slope transfers divisibility to the opposite value. -/

set_option autoImplicit false

namespace HypothesisS

theorem common_divisor_of_affine_values (divisor b1 b2 n a1 a2 : Int)
    (hFirst : divisor ∣ b1 * n + a1) (hSecond : divisor ∣ b2 * n + a2) :
    divisor ∣ a1 * b2 - a2 * b1 := by
  obtain ⟨q1, h1⟩ := hFirst
  obtain ⟨q2, h2⟩ := hSecond
  refine ⟨b2 * q1 - b1 * q2, ?_⟩
  calc
    a1 * b2 - a2 * b1 = b2 * (b1 * n + a1) - b1 * (b2 * n + a2) := by grind
    _ = divisor * (b2 * q1 - b1 * q2) := by rw [h1, h2]; grind

theorem determinant_divisor_transfers (divisor b1 b2 n a1 a2 inverse correction : Int)
    (hInverse : inverse * b1 = 1 + divisor * correction)
    (hFirst : divisor ∣ b1 * n + a1)
    (hDeterminant : divisor ∣ a1 * b2 - a2 * b1) :
    divisor ∣ b2 * n + a2 := by
  obtain ⟨q1, h1⟩ := hFirst
  obtain ⟨qDet, hDet⟩ := hDeterminant
  have hProduct : b1 * (b2 * n + a2) = divisor * (b2 * q1 - qDet) := by
    calc
      b1 * (b2 * n + a2) = b2 * (b1 * n + a1) - (a1 * b2 - a2 * b1) := by grind
      _ = divisor * (b2 * q1 - qDet) := by rw [h1, hDet]; grind
  refine ⟨inverse * (b2 * q1 - qDet) - correction * (b2 * n + a2), ?_⟩
  calc
    b2 * n + a2 =
        (1 + divisor * correction) * (b2 * n + a2) -
          divisor * correction * (b2 * n + a2) := by grind
    _ = divisor * (inverse * (b2 * q1 - qDet) - correction * (b2 * n + a2)) := by
      rw [← hInverse, Int.mul_assoc, hProduct]
      grind

#print axioms common_divisor_of_affine_values
#print axioms determinant_divisor_transfers

end HypothesisS
