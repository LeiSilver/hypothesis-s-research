import Lean

/-! The inverse branch equations and their reflection for clipped Farey arcs. -/

set_option autoImplicit false

namespace HypothesisS

theorem clipped_inverse_branch_identity (a v j m x u L : Int)
    (hA : a * v + j = m * x) (hU : j * u + v = L * x) :
    v * (a * u - 1) = x * (m * u - L) := by
  have hProduct : a * v = m * x - j := by omega
  calc
    v * (a * u - 1) = (a * v) * u - v := by
      rw [Int.mul_sub, Int.mul_one]
      have hReorder : v * (a * u) = a * v * u := by ac_rfl
      rw [hReorder]
    _ = (m * x - j) * u - v := by rw [hProduct]
    _ = x * (m * u) - (j * u + v) := by
      rw [Int.sub_mul]
      have hReorder : m * x * u = x * (m * u) := by ac_rfl
      rw [hReorder]
      omega
    _ = x * (m * u - L) := by rw [hU, Int.mul_sub, Int.mul_comm x L]

theorem clipped_reflected_product_congruence (D g j m x u L c : Int)
    (hProduct : D ∣ m * g * x - g * j)
    (hBranch : D ∣ m * u - L) :
    D ∣ (-m) * (u - c * g * x) - (c * g * j - L) := by
  have hScaled : D ∣ c * (m * g * x - g * j) := Int.dvd_mul_of_dvd_right hProduct
  have hIdentity : (-m) * (u - c * g * x) - (c * g * j - L) =
      c * (m * g * x - g * j) - (m * u - L) := by
    simp only [Int.mul_sub, Int.neg_mul]
    have hFirst : m * (c * g * x) = c * (m * g * x) := by ac_rfl
    have hSecond : c * (g * j) = c * g * j := by ac_rfl
    rw [hFirst, hSecond]
    omega
  rw [hIdentity]
  exact Int.dvd_sub hScaled hBranch

theorem clipped_inverse_pair_displacement (g j v x u u' L c : Int)
    (hU : j * u + v = L * x) (hU' : j * u' + v = (c * g * j - L) * x) :
    j * (u + u') + 2 * v = c * g * j * x := by
  rw [Int.mul_add]
  rw [Int.sub_mul] at hU'
  omega

#print axioms clipped_inverse_branch_identity
#print axioms clipped_reflected_product_congruence
#print axioms clipped_inverse_pair_displacement

end HypothesisS
