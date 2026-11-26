import Lean

/-! Integer identities for the double completion of the long-divisor sum. -/

set_option autoImplicit false

namespace HypothesisS

theorem cleared_double_completion_phase (a v j m x u L n h : Int)
    (hA : a * v + j = m * x) (hU : j * u + v = L * x) :
    (v * j) * (-a * n + h * u) =
      (j * n) * (j - m * x) + (h * v) * (L * x - v) := by
  have hLeft : j - m * x = -a * v := by
    rw [← hA]
    rw [Int.neg_mul]
    omega
  have hRight : L * x - v = j * u := by omega
  rw [hLeft, hRight, Int.mul_add]
  rw [Int.neg_mul, Int.neg_mul]
  have hN : (v * j) * (a * n) = (j * n) * (a * v) := by ac_rfl
  have hH : (v * j) * (h * u) = (h * v) * (j * u) := by ac_rfl
  simp only [Int.mul_neg]
  rw [hN, hH]

theorem double_completion_lift_congruence (D₀ g j₀ j₁ jInv m x : Int)
    (hProduct : D₀ ∣ m * g * x - g * j₀ * j₁)
    (hInverse : D₀ ∣ j₁ * jInv - 1) :
    D₀ ∣ m * (g * x * jInv) - g * j₀ := by
  have hFirst : D₀ ∣ (m * g * x - g * j₀ * j₁) * jInv :=
    Int.dvd_mul_of_dvd_left hProduct
  have hSecond : D₀ ∣ (g * j₀) * (j₁ * jInv - 1) :=
    Int.dvd_mul_of_dvd_right hInverse
  have hIdentity : m * (g * x * jInv) - g * j₀ =
      (m * g * x - g * j₀ * j₁) * jInv +
        (g * j₀) * (j₁ * jInv - 1) := by
    simp only [Int.sub_mul, Int.mul_sub, Int.mul_one]
    have hReorder : m * (g * x * jInv) = m * g * x * jInv := by ac_rfl
    rw [hReorder, ← Int.mul_assoc (g * j₀) j₁ jInv]
    omega
  rw [hIdentity]
  exact Int.dvd_add hFirst hSecond

#print axioms cleared_double_completion_phase
#print axioms double_completion_lift_congruence

end HypothesisS
