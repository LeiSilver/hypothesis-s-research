import Lean

/-! The short-divisor progression and its residues at a reduced rational center. -/

set_option autoImplicit false

namespace HypothesisS

private theorem dvd_mul_difference_of_equal_residue (a q d₁ d₂ : Nat)
    (hResidue : (a * d₁) % q = (a * d₂) % q) :
    q ∣ a * (d₂ - d₁) := by
  refine ⟨(a * d₂) / q - (a * d₁) / q, ?_⟩
  have hFirst := Nat.mod_add_div (a * d₁) q
  have hSecond := Nat.mod_add_div (a * d₂) q
  simp only [Nat.mul_sub]
  omega

theorem short_divisor_residue_injective (a q d₁ d₂ : Nat)
    (hUnit : Nat.Coprime q a) (hFirst : d₁ < q) (hSecond : d₂ < q)
    (hResidue : (a * d₁) % q = (a * d₂) % q) :
    d₁ = d₂ := by
  have hForward := hUnit.dvd_of_dvd_mul_left
    (dvd_mul_difference_of_equal_residue a q d₁ d₂ hResidue)
  have hBackward := hUnit.dvd_of_dvd_mul_left
    (dvd_mul_difference_of_equal_residue a q d₂ d₁ hResidue.symm)
  have hForwardLt : d₂ - d₁ < q := by omega
  have hBackwardLt : d₁ - d₂ < q := by omega
  have hForwardZero := Nat.mod_eq_zero_of_dvd hForward
  have hBackwardZero := Nat.mod_eq_zero_of_dvd hBackward
  rw [Nat.mod_eq_of_lt hForwardLt] at hForwardZero
  rw [Nat.mod_eq_of_lt hBackwardLt] at hBackwardZero
  omega

theorem short_divisor_residue_nonzero (a q d : Nat)
    (hUnit : Nat.Coprime q a) (hPos : 0 < d) (hShort : d < q) :
    (a * d) % q ≠ 0 := by
  intro hZero
  have hDvd : q ∣ d := hUnit.dvd_of_dvd_mul_left (Nat.dvd_of_mod_eq_zero hZero)
  have hAtMost := Nat.le_of_dvd hPos hDvd
  omega

theorem screened_type_i_period_dvd_product (d square rough : Nat) :
    Nat.lcm (Nat.lcm d (square ^ 2)) rough ∣ d * square ^ 2 * rough := by
  apply Nat.dvd_trans (Nat.lcm_dvd_mul (Nat.lcm d (square ^ 2)) rough)
  exact Nat.mul_dvd_mul_right (Nat.lcm_dvd_mul d (square ^ 2)) rough

#print axioms short_divisor_residue_injective
#print axioms short_divisor_residue_nonzero
#print axioms screened_type_i_period_dvd_product

end HypothesisS
