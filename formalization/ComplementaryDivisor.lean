import Lean

/-! The complementary divisor in a factorization carries the
equivalent strict cutoff and recovers the squarefree Möbius sign. -/

set_option autoImplicit false

namespace HypothesisS

theorem complementary_divisor_cutoff (t d m cutoff : Nat)
    (hFactor : t = d * m) (hm : 0 < m) :
    cutoff < d ↔ cutoff * m < t := by
  subst t
  constructor
  · intro hCutoff
    exact Nat.mul_lt_mul_of_pos_right hCutoff hm
  · intro hProduct
    by_cases hCutoff : cutoff < d
    · exact hCutoff
    · have hOrder : d * m ≤ cutoff * m :=
        Nat.mul_le_mul_right m (by omega)
      omega

theorem complementary_mobius_sign (divisorSign complementSign productSign : Int)
    (hProduct : divisorSign * complementSign = productSign)
    (hSquare : complementSign * complementSign = 1) :
    divisorSign = productSign * complementSign := by
  calc
    divisorSign = divisorSign * (complementSign * complementSign) := by simp [hSquare]
    _ = productSign * complementSign := by rw [← Int.mul_assoc, hProduct]

#print axioms complementary_divisor_cutoff
#print axioms complementary_mobius_sign

end HypothesisS
