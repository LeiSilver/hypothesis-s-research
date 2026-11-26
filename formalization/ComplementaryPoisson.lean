import Lean

/-! Reduced moduli and inverse residues in the complementary-factor completion. -/

set_option autoImplicit false

namespace HypothesisS

theorem completion_gcd_dvd_screen_multiple (q d r : Nat) :
    Nat.gcd q (d * r) ∣ r * Nat.gcd q d := by
  let g := Nat.gcd q (d * r)
  have hQ : g ∣ r * q :=
    Nat.dvd_trans (Nat.gcd_dvd_left q (d * r)) (Nat.dvd_mul_left q r)
  have hD : g ∣ r * d := by
    rw [Nat.mul_comm r d]
    exact Nat.gcd_dvd_right q (d * r)
  rw [← Nat.gcd_mul_left]
  exact Nat.dvd_gcd hQ hD

theorem completion_reduced_multiplier_coprime (q m : Nat) (hq : 0 < q) :
    Nat.Coprime (q / Nat.gcd q m) (m / Nat.gcd q m) := by
  change Nat.gcd (q / Nat.gcd q m) (m / Nat.gcd q m) = 1
  rw [Nat.gcd_div (Nat.gcd_dvd_left q m) (Nat.gcd_dvd_right q m)]
  exact Nat.div_self (Nat.gcd_pos_of_pos_left m hq)

theorem completed_frequency_inverse_residue (q a v j aInv jInv : Int)
    (hPhase : q ∣ a * v + j)
    (hA : q ∣ a * aInv - 1) (hJ : q ∣ j * jInv - 1) :
    q ∣ aInv + v * jInv := by
  have hMultiplyA : q ∣ aInv * (a * v + j) := Int.dvd_mul_of_dvd_right hPhase
  have hRemoveA : q ∣ (a * aInv - 1) * v := Int.dvd_mul_of_dvd_left hA
  have hFirstIdentity : aInv * (a * v + j) - (a * aInv - 1) * v =
      v + aInv * j := by
    simp only [Int.mul_add, Int.sub_mul, Int.one_mul]
    have hReorder : aInv * (a * v) = a * aInv * v := by ac_rfl
    rw [hReorder]
    omega
  have hFirst : q ∣ v + aInv * j := hFirstIdentity ▸ Int.dvd_sub hMultiplyA hRemoveA
  have hMultiplyJ : q ∣ (v + aInv * j) * jInv := Int.dvd_mul_of_dvd_left hFirst
  have hRemoveJ : q ∣ aInv * (j * jInv - 1) := Int.dvd_mul_of_dvd_right hJ
  have hSecondIdentity : (v + aInv * j) * jInv - aInv * (j * jInv - 1) =
      aInv + v * jInv := by
    simp only [Int.add_mul, Int.mul_sub, Int.mul_one, Int.mul_assoc]
    omega
  exact hSecondIdentity ▸ Int.dvd_sub hMultiplyJ hRemoveJ

theorem completed_frequency_determinant_divisible (q a d d' j j' : Int)
    (hFirst : q ∣ a * d + j) (hSecond : q ∣ a * d' + j') :
    q ∣ j * d' - j' * d := by
  have hMultiplyFirst : q ∣ (a * d + j) * d' := Int.dvd_mul_of_dvd_left hFirst
  have hMultiplySecond : q ∣ (a * d' + j') * d := Int.dvd_mul_of_dvd_left hSecond
  have hIdentity : (a * d + j) * d' - (a * d' + j') * d = j * d' - j' * d := by
    simp only [Int.add_mul]
    have hReorder : a * d * d' = a * d' * d := by ac_rfl
    rw [hReorder]
    omega
  exact hIdentity ▸ Int.dvd_sub hMultiplyFirst hMultiplySecond

#print axioms completion_gcd_dvd_screen_multiple
#print axioms completion_reduced_multiplier_coprime
#print axioms completed_frequency_inverse_residue
#print axioms completed_frequency_determinant_divisible

end HypothesisS
