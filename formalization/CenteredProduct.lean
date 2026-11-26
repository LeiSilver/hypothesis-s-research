import Lean

/-! The two product tests can disagree only within the boundary collar. -/

set_option autoImplicit false

namespace HypothesisS

theorem centered_product_collar
    (x center y cap : Int)
    (hx : 0 ≤ x)
    (hShift : y = center + x ∨ y = center - x)
    (hMismatch :
      (x * y ≤ cap ∧ cap < x * center) ∨
      (x * center ≤ cap ∧ cap < x * y)) :
    cap - x * x ≤ x * y ∧ x * y ≤ cap + x * x := by
  have hSquare : 0 ≤ x * x := Int.mul_nonneg hx hx
  rcases hShift with hPlus | hMinus
  · subst y
    simp only [Int.mul_add] at hMismatch ⊢
    omega
  · subst y
    simp only [Int.mul_sub] at hMismatch ⊢
    omega

#print axioms centered_product_collar

end HypothesisS
