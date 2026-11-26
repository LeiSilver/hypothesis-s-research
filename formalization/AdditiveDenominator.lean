import Lean

/-! Reduction of a frequency on the grid modulo a positive integer. -/

set_option autoImplicit false

namespace HypothesisS

theorem additive_denominator_cross_product (numerator modulus : Nat) :
    numerator * (modulus / Nat.gcd numerator modulus) =
      modulus * (numerator / Nat.gcd numerator modulus) := by
  let common := Nat.gcd numerator modulus
  have hn : numerator / common * common = numerator :=
    Nat.div_mul_cancel (Nat.gcd_dvd_left numerator modulus)
  have hm : modulus / common * common = modulus :=
    Nat.div_mul_cancel (Nat.gcd_dvd_right numerator modulus)
  change numerator * (modulus / common) = modulus * (numerator / common)
  calc
    numerator * (modulus / common) =
        (numerator / common * common) * (modulus / common) := by rw [hn]
    _ = (modulus / common * common) * (numerator / common) := by
      simp only [Nat.mul_comm, Nat.mul_left_comm]
    _ = modulus * (numerator / common) := by rw [hm]

theorem additive_denominator_cofactor_cutoff (numerator modulus cutoff : Nat)
    (hModulus : 0 < modulus) :
    modulus < (modulus / Nat.gcd numerator modulus) * cutoff ↔
      Nat.gcd numerator modulus < cutoff := by
  let common := Nat.gcd numerator modulus
  let denominator := modulus / common
  have hProduct : denominator * common = modulus :=
    Nat.div_mul_cancel (Nat.gcd_dvd_right numerator modulus)
  have hDenominator : 0 < denominator := by
    by_cases hz : denominator = 0
    · rw [hz, Nat.zero_mul] at hProduct
      omega
    · exact Nat.pos_of_ne_zero hz
  change modulus < denominator * cutoff ↔ common < cutoff
  rw [← hProduct]
  constructor
  · intro hLarge
    by_cases hCutoff : common < cutoff
    · exact hCutoff
    · have hOrder : denominator * cutoff ≤ denominator * common :=
        Nat.mul_le_mul_left denominator (by omega)
      omega
  · intro hCutoff
    exact Nat.mul_lt_mul_of_pos_left hCutoff hDenominator

#print axioms additive_denominator_cross_product
#print axioms additive_denominator_cofactor_cutoff

end HypothesisS
