import Lean

/-! Common divisors and translations in the additive frequency grid. -/

set_option autoImplicit false

namespace HypothesisS

theorem common_denominator_bound (n q₁ q₂ h₁ h₂ : Nat)
    (hn : 0 < n) (hd₁ : q₁ ∣ n) (hd₂ : q₂ ∣ n)
    (hc₁ : n < q₁ * h₁) (hc₂ : n < q₂ * h₂) :
    n < Nat.gcd q₁ q₂ * (h₁ * h₂) := by
  have hq : 0 < q₁ * h₁ := Nat.lt_trans hn hc₁
  have hLcm : Nat.lcm q₁ q₂ ≤ n := Nat.le_of_dvd hn (Nat.lcm_dvd hd₁ hd₂)
  apply Nat.lt_of_mul_lt_mul_left (a := n)
  calc
    n * n < q₁ * h₁ * n := Nat.mul_lt_mul_of_pos_right hc₁ hn
    _ < q₁ * h₁ * (q₂ * h₂) := Nat.mul_lt_mul_of_pos_left hc₂ hq
    _ = (q₁ * q₂) * (h₁ * h₂) := by ac_rfl
    _ = Nat.lcm q₁ q₂ * (Nat.gcd q₁ q₂ * (h₁ * h₂)) := by
      rw [← Nat.gcd_mul_lcm q₁ q₂]
      ac_rfl
    _ ≤ n * (Nat.gcd q₁ q₂ * (h₁ * h₂)) := Nat.mul_le_mul_right _ hLcm

theorem four_denominators_common_bound (n q₁ q₂ q₃ q₄ h₁ h₂ h₃ h₄ : Nat)
    (hn : 0 < n) (hd₁ : q₁ ∣ n) (hd₂ : q₂ ∣ n) (hd₃ : q₃ ∣ n) (hd₄ : q₄ ∣ n)
    (hc₁ : n < q₁ * h₁) (hc₂ : n < q₂ * h₂)
    (hc₃ : n < q₃ * h₃) (hc₄ : n < q₄ * h₄) :
    n < Nat.gcd (Nat.gcd q₁ q₂) (Nat.gcd q₃ q₄) * ((h₁ * h₂) * (h₃ * h₄)) := by
  have hd₁₂ := Nat.dvd_trans (Nat.gcd_dvd_left q₁ q₂) hd₁
  have hd₃₄ := Nat.dvd_trans (Nat.gcd_dvd_left q₃ q₄) hd₃
  have hc₁₂ := common_denominator_bound n q₁ q₂ h₁ h₂ hn hd₁ hd₂ hc₁ hc₂
  have hc₃₄ := common_denominator_bound n q₃ q₄ h₃ h₄ hn hd₃ hd₄ hc₃ hc₄
  exact common_denominator_bound n _ _ _ _ hn hd₁₂ hd₃₄ hc₁₂ hc₃₄

private theorem add_reduced_right (a b n : Int) :
    (a + b % n) % n = (a + b) % n := by
  calc
    (a + b % n) % n = (a % n + b % n) % n := by
      rw [Int.add_emod a (b % n) n, Int.emod_emod]
    _ = (a + b) % n := (Int.add_emod a b n).symm

private theorem sub_reduced_left (a b n : Int) :
    (a % n - b) % n = (a - b) % n := by
  calc
    (a % n - b) % n = (a % n - b % n) % n := by
      rw [Int.sub_emod (a % n) b n, Int.emod_emod]
    _ = (a - b) % n := (Int.sub_emod a b n).symm

private theorem sub_reduced_right (a b n : Int) :
    (a - b % n) % n = (a - b) % n := by
  calc
    (a - b % n) % n = (a % n - b % n) % n := by
      rw [Int.sub_emod a (b % n) n, Int.emod_emod]
    _ = (a - b) % n := (Int.sub_emod a b n).symm

theorem sum_residue_inverse (a b c n : Int)
    (hb₀ : 0 ≤ b) (hbₙ : b < n) (hc₀ : 0 ≤ c) (hcₙ : c < n) :
    (a + b) % n = c ↔ b = (c - a) % n := by
  constructor
  · intro h
    rw [← h, sub_reduced_left]
    have hSub : a + b - a = b := by omega
    rw [hSub, Int.emod_eq_of_lt hb₀ hbₙ]
  · intro h
    rw [h, add_reduced_right]
    have hAdd : a + (c - a) = c := by omega
    rw [hAdd, Int.emod_eq_of_lt hc₀ hcₙ]

theorem difference_residue_inverse (a b c n : Int)
    (hb₀ : 0 ≤ b) (hbₙ : b < n) (hc₀ : 0 ≤ c) (hcₙ : c < n) :
    (a - b) % n = c ↔ b = (a - c) % n := by
  constructor
  · intro h
    rw [← h, sub_reduced_right]
    have hSub : a - (a - b) = b := by omega
    rw [hSub, Int.emod_eq_of_lt hb₀ hbₙ]
  · intro h
    rw [h, sub_reduced_right]
    have hSub : a - (a - c) = c := by omega
    rw [hSub, Int.emod_eq_of_lt hc₀ hcₙ]

#print axioms four_denominators_common_bound
#print axioms sum_residue_inverse
#print axioms difference_residue_inverse

end HypothesisS
