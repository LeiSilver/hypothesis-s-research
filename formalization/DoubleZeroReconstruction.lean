import Lean

/-! Divisibility and divisor regrouping for the zero-mode reconstruction. -/

set_option autoImplicit false

namespace HypothesisS

theorem reconstructed_divisor_condition (t f u a n : Nat)
    (ht : 0 < t) (hu : 0 < u) (hf : u ∣ f)
    (ha : Nat.Coprime (f / u) a) :
    (t ∣ n ∧ f ∣ (u * a) * (n / t)) ↔ t * (f / u) ∣ n := by
  have hSplit : u * (f / u) = f := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel hf
  have hCancel : f ∣ (u * a) * (n / t) ↔ (f / u) ∣ a * (n / t) := by
    calc
      f ∣ (u * a) * (n / t) ↔ u * (f / u) ∣ u * (a * (n / t)) := by
        rw [hSplit, Nat.mul_assoc]
      _ ↔ (f / u) ∣ a * (n / t) := Nat.mul_dvd_mul_iff_left hu
  constructor
  · rintro ⟨hT, hF⟩
    have hQ : (f / u) ∣ n / t := ha.dvd_of_dvd_mul_left (hCancel.mp hF)
    have hN : t * (n / t) = n := by
      rw [Nat.mul_comm]
      exact Nat.div_mul_cancel hT
    rw [← hN]
    exact (Nat.mul_dvd_mul_iff_left ht).mpr hQ
  · intro h
    have hT : t ∣ n := Nat.dvd_trans (Nat.dvd_mul_right t (f / u)) h
    have hN : t * (n / t) = n := by
      rw [Nat.mul_comm]
      exact Nat.div_mul_cancel hT
    have hProd : t * (f / u) ∣ t * (n / t) := by
      rw [hN]
      exact h
    have hQ : f / u ∣ n / t := (Nat.mul_dvd_mul_iff_left ht).mp hProd
    exact ⟨hT, hCancel.mpr (Nat.dvd_trans hQ (Nat.dvd_mul_left (n / t) a))⟩

theorem reconstruction_regroups_divisors (D t h : Nat) (ht : 0 < t) :
    t * h ∣ D ↔ t ∣ D ∧ h ∣ D / t := by
  constructor
  · intro hprod
    have hT : t ∣ D := Nat.dvd_trans (Nat.dvd_mul_right t h) hprod
    have hD : t * (D / t) = D := by
      rw [Nat.mul_comm]
      exact Nat.div_mul_cancel hT
    refine ⟨hT, (Nat.mul_dvd_mul_iff_left ht).mp ?_⟩
    rw [hD]
    exact hprod
  · rintro ⟨hT, hquot⟩
    have hD : t * (D / t) = D := by
      rw [Nat.mul_comm]
      exact Nat.div_mul_cancel hT
    rw [← hD]
    exact (Nat.mul_dvd_mul_iff_left ht).mpr hquot

#print axioms reconstructed_divisor_condition
#print axioms reconstruction_regroups_divisors

end HypothesisS
