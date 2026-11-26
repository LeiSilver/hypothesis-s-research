import Lean

/-! Integer identities for reciprocity and the signed Ramanujan period. -/

set_option autoImplicit false

namespace HypothesisS

theorem reciprocity_numerator_divisible_each (k x kInv xInv : Int)
    (hK : x ∣ k * kInv - 1) (hX : k ∣ x * xInv - 1) :
    k ∣ k * kInv + x * xInv - 1 ∧ x ∣ k * kInv + x * xInv - 1 := by
  constructor
  · have hSum := Int.dvd_add (show k ∣ k * kInv from ⟨kInv, rfl⟩) hX
    have hSplit : k * kInv + x * xInv - 1 = k * kInv + (x * xInv - 1) := by
      omega
    rw [hSplit]
    exact hSum
  · have hSum := Int.dvd_add hK (show x ∣ x * xInv from ⟨xInv, rfl⟩)
    have hSplit : k * kInv + x * xInv - 1 = (k * kInv - 1) + x * xInv := by
      omega
    rw [hSplit]
    exact hSum

theorem reflected_periodic_even_weight {α : Type} (f : Int → α)
    (D N p period b bRef : Int) (hPeriod : D ∣ period * N)
    (hReflection : period ∣ b + bRef)
    (hEven : ∀ n : Int, f (-n) = f n)
    (hPeriodic : ∀ u v : Int, D ∣ u - v → f u = f v) :
    f (bRef * N - p) = f (b * N + p) := by
  obtain ⟨a, ha⟩ := hReflection
  have hDvd : D ∣ (b + bRef) * N := by
    rw [ha]
    have hReorder : (period * a) * N = (period * N) * a := by ac_rfl
    rw [hReorder]
    exact Int.dvd_mul_of_dvd_left hPeriod
  have hDiff : (bRef * N - p) - (-(b * N + p)) = (b + bRef) * N := by
    rw [Int.add_mul]
    omega
  calc
    f (bRef * N - p) = f (-(b * N + p)) := hPeriodic _ _ (hDiff.symm ▸ hDvd)
    _ = f (b * N + p) := hEven _

theorem period_divisor_gcd_scales (t k n : Nat) :
    Nat.gcd (t * k) (t * n) = t * Nat.gcd k n :=
  Nat.gcd_mul_left t k n

#print axioms reciprocity_numerator_divisible_each
#print axioms reflected_periodic_even_weight
#print axioms period_divisor_gcd_scales

end HypothesisS
