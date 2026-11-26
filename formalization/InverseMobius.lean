import Lean

/-! Congruences for completing the screened Type II count. -/

set_option autoImplicit false

namespace HypothesisS

theorem inverse_sum_gives_hyperbola (q x y xInv yInv residue : Int)
    (hx : q ∣ x * xInv - 1) (hy : q ∣ y * yInv - 1)
    (hSum : q ∣ xInv + yInv - residue) :
    q ∣ residue * x * y - (x + y) := by
  have hIdentity :
      residue * x * y - (x + y) =
        y * (x * xInv - 1) + x * (y * yInv - 1) -
          x * y * (xInv + yInv - residue) := by
    simp only [Int.mul_sub, Int.mul_add, Int.mul_one]
    have hX : y * (x * xInv) = x * y * xInv := by ac_rfl
    have hY : x * (y * yInv) = x * y * yInv := by ac_rfl
    have hR : residue * x * y = x * y * residue := by ac_rfl
    rw [hX, hY, hR]
    omega
  rw [hIdentity]
  exact Int.dvd_sub
    (Int.dvd_add (Int.dvd_mul_of_dvd_right hx) (Int.dvd_mul_of_dvd_right hy))
    (Int.dvd_mul_of_dvd_right hSum)

theorem inverse_hyperbola_factorization (u t x y k q : Int)
    (h : u * x * y - t * (x + y) = k * q) :
    (u * x - t) * (u * y - t) = t * t + u * (k * q) := by
  have hScaled := congrArg (u * ·) h
  simp only [Int.sub_mul, Int.mul_sub, Int.mul_add] at hScaled ⊢
  have hXY : u * x * (u * y) = u * (u * x * y) := by ac_rfl
  have hX : u * x * t = u * (t * x) := by ac_rfl
  have hY : t * (u * y) = u * (t * y) := by ac_rfl
  rw [hXY, hX, hY]
  omega

theorem screen_reduces_to_complement (g r d m : Nat)
    (hg : 0 < g) (hd : Nat.Coprime r d) :
    g * r ∣ (g * d) * m ↔ r ∣ m := by
  rw [Nat.mul_assoc, Nat.mul_dvd_mul_iff_left hg]
  exact ⟨hd.dvd_of_dvd_mul_left, fun h => Nat.dvd_trans h (Nat.dvd_mul_left m d)⟩

#print axioms inverse_sum_gives_hyperbola
#print axioms inverse_hyperbola_factorization
#print axioms screen_reduces_to_complement

end HypothesisS
