import Lean

/-! Local period and signed progression identities for the transition range. -/

set_option autoImplicit false

namespace HypothesisS

theorem transition_period_exponent (A J : Nat) (hA : 0 < A) (hJ : 0 < J) :
    max J (A - J) ≤ A + J - 1 := by
  omega

theorem transition_scaled_inverse_period (x y u w t j v D L : Int)
    (hShift : t ∣ y - x) (hInverseX : t ∣ x * u - 1)
    (hInverseY : t ∣ y * w - 1) (hJ : D ∣ j * t) (hV : L ∣ v * t) :
    (D ∣ j * u - j * w) ∧ (L ∣ v * u - v * w) := by
  have hIdentity :
      u - w = (x * u - 1) * w - (y * w - 1) * u + (y - x) * (u * w) := by
    simp only [Int.sub_mul, Int.one_mul]
    have hX : x * (u * w) = (x * u) * w := by ac_rfl
    have hY : y * (u * w) = (y * w) * u := by ac_rfl
    rw [hX, hY]
    omega
  have hDifference : t ∣ u - w := by
    rw [hIdentity]
    exact Int.dvd_add
      (Int.dvd_sub (Int.dvd_mul_of_dvd_left hInverseX)
        (Int.dvd_mul_of_dvd_left hInverseY))
      (Int.dvd_mul_of_dvd_left hShift)
  obtain ⟨c, hc⟩ := hDifference
  constructor
  · rw [← Int.mul_sub, hc, ← Int.mul_assoc]
    exact Int.dvd_mul_of_dvd_left hJ
  · rw [← Int.mul_sub, hc, ← Int.mul_assoc]
    exact Int.dvd_mul_of_dvd_left hV

theorem transition_reflected_progression (E d b N p u : Int) :
    (E ∣ b * N + p - u) ∧ (d ∣ b * N + p) ↔
      (E ∣ (-b) * N - p - (-u)) ∧ (d ∣ (-b) * N - p) := by
  have hResidue : (-b) * N - p - (-u) = -(b * N + p - u) := by
    rw [Int.neg_mul]
    omega
  have hDivisor : (-b) * N - p = -(b * N + p) := by
    rw [Int.neg_mul]
    omega
  rw [hResidue, hDivisor]
  simp

#print axioms transition_period_exponent
#print axioms transition_scaled_inverse_period
#print axioms transition_reflected_progression

end HypothesisS
