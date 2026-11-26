import Lean

/-! Divisibility and quotients in the full modulus second moment. -/

set_option autoImplicit false

namespace HypothesisS

theorem sampling_factor_dvd_conductor_cofactor (d e k c ell : Nat)
    (hc : c ∣ k) (hEll : ell ∣ e * k) (hUnit : Nat.Coprime ell c) :
    d * ell ∣ (d * e * k) / c := by
  have hSplit : e * k = (e * (k / c)) * c := by
    rw [Nat.mul_assoc, Nat.div_mul_cancel hc]
  have hEllCofactor : ell ∣ e * (k / c) := by
    rw [hSplit] at hEll
    exact hUnit.dvd_of_dvd_mul_right hEll
  have hConductorDvd : c ∣ d * e * k := Nat.dvd_trans hc (Nat.dvd_mul_left k (d * e))
  apply (Nat.dvd_div_iff_mul_dvd hConductorDvd).2
  obtain ⟨m, hm⟩ := hEllCofactor
  refine ⟨m, ?_⟩
  calc
    d * e * k = d * ((e * (k / c)) * c) := by rw [Nat.mul_assoc d, hSplit]
    _ = d * ((ell * m) * c) := by rw [hm]
    _ = c * (d * ell) * m := by ac_rfl

theorem even_common_modulus_divisibility (r s n : Nat) :
    (Nat.lcm 2 (Nat.lcm r s)) ∣ n ↔ 2 ∣ n ∧ r ∣ n ∧ s ∣ n := by
  constructor
  · intro h
    have hPair := Nat.dvd_trans (Nat.dvd_lcm_right 2 (Nat.lcm r s)) h
    exact ⟨Nat.dvd_trans (Nat.dvd_lcm_left 2 (Nat.lcm r s)) h,
      Nat.dvd_trans (Nat.dvd_lcm_left r s) hPair,
      Nat.dvd_trans (Nat.dvd_lcm_right r s) hPair⟩
  · rintro ⟨hTwo, hR, hS⟩
    exact Nat.lcm_dvd hTwo (Nat.lcm_dvd hR hS)

theorem quotient_at_common_multiple (r period m : Nat) (hr : r ∣ period) :
    (period * m) / r = (period / r) * m := by
  rw [Nat.mul_comm period m, Nat.mul_div_assoc m hr, Nat.mul_comm m]

theorem even_common_period_sq_ge_product (r s : Nat) (hr : 0 < r) (hs : 0 < s) :
    r * s ≤ (Nat.lcm 2 (Nat.lcm r s)) ^ 2 := by
  let period := Nat.lcm 2 (Nat.lcm r s)
  have hPeriod : 0 < period := Nat.lcm_pos (by decide) (Nat.lcm_pos hr hs)
  have hPair : Nat.lcm r s ∣ period := Nat.dvd_lcm_right 2 (Nat.lcm r s)
  have hR := Nat.le_of_dvd hPeriod (Nat.dvd_trans (Nat.dvd_lcm_left r s) hPair)
  have hS := Nat.le_of_dvd hPeriod (Nat.dvd_trans (Nat.dvd_lcm_right r s) hPair)
  simpa only [Nat.pow_two] using Nat.mul_le_mul hR hS

#print axioms sampling_factor_dvd_conductor_cofactor
#print axioms even_common_modulus_divisibility
#print axioms quotient_at_common_multiple
#print axioms even_common_period_sq_ge_product

end HypothesisS
