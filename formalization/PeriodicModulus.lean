import Lean

/-! Arithmetic for periodic weights on the modulus in the prime-prefix sum. -/

set_option autoImplicit false

namespace HypothesisS

theorem periodic_modulus_factorization (n c : Nat) (hn : 0 < n) :
    ∃ d q exponent : Nat, n = d * q ∧ d ∣ c ^ exponent ∧ Nat.gcd q c = 1 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hCoprime : Nat.gcd n c = 1
    · exact ⟨1, n, 0, (Nat.one_mul n).symm, Nat.one_dvd _, hCoprime⟩
    let g := Nat.gcd n c
    have hg : 0 < g := Nat.gcd_pos_of_pos_left c hn
    have hgLarge : 1 < g := by
      change g ≠ 1 at hCoprime
      omega
    have hSplit : n / g * g = n := Nat.div_mul_cancel (Nat.gcd_dvd_left n c)
    have hQuotient : 0 < n / g := by
      by_cases hZero : n / g = 0
      · rw [hZero, Nat.zero_mul] at hSplit
        omega
      · exact Nat.pos_of_ne_zero hZero
    obtain ⟨d, q, exponent, hFactor, hPower, hq⟩ :=
      ih (n / g) (Nat.div_lt_self hn hgLarge) hQuotient
    refine ⟨d * g, q, exponent + 1, ?_, ?_, hq⟩
    · calc
        n = (n / g) * g := hSplit.symm
        _ = (d * q) * g := by rw [hFactor]
        _ = (d * g) * q := by ac_rfl
    · rw [Nat.pow_succ]
      exact Nat.mul_dvd_mul hPower (Nat.gcd_dvd_right n c)

theorem periodic_modulus_product_class (d q u c m : Int)
    (hPeriod : m ∣ c) (hClass : q % c = u % c) :
    (d * q) % m = (d * u) % m := by
  have hDifference : c ∣ q - u :=
    Int.dvd_iff_emod_eq_zero.mpr (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hClass)
  obtain ⟨k, hk⟩ := Int.dvd_trans hPeriod hDifference
  apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
  apply Int.dvd_iff_emod_eq_zero.mp
  refine ⟨d * k, ?_⟩
  calc
    d * q - d * u = d * (q - u) := (Int.mul_sub d q u).symm
    _ = m * (d * k) := by
      rw [hk]
      ac_rfl

#print axioms periodic_modulus_factorization
#print axioms periodic_modulus_product_class

end HypothesisS
