import Lean

/-! Discrete inequalities for the band of short gaps between zero labels. -/

set_option autoImplicit false

namespace HypothesisS

/--
In half-open bins, a gap of at most 'gap' bin widths allows an
index difference of at most 'gap'. Rational coordinates can be
written as integers after clearing a common denominator.
-/
theorem bin_dist_le_scaled_gap {width gap i j x y : Int}
    (hWidth : 0 < width)
    (hxLower : i * width ≤ x) (hxUpper : x < (i + 1) * width)
    (hyLower : j * width ≤ y) (hyUpper : y < (j + 1) * width)
    (hGapXY : x - y ≤ gap * width) (hGapYX : y - x ≤ gap * width) :
    i - j ≤ gap ∧ j - i ≤ gap := by
  have oneSide {a b x₁ x₂ : Int}
      (hLower : a * width ≤ x₁) (hUpper : x₂ < (b + 1) * width)
      (hGap : x₁ - x₂ ≤ gap * width) : a - b ≤ gap := by
    by_cases h : a - b ≤ gap
    · exact h
    have hIndex : b + gap + 1 ≤ a := by omega
    have hProduct :=
      Int.mul_le_mul_of_nonneg_right hIndex (Int.le_of_lt hWidth)
    rw [Int.add_mul, Int.add_mul, Int.one_mul] at hProduct
    rw [Int.add_mul, Int.one_mul] at hUpper
    omega
  exact ⟨oneSide hxLower hyUpper hGapXY, oneSide hyLower hxUpper hGapYX⟩

/-- The elementary quadratic bound used to sum a fixed bin offset. -/
theorem twice_product_le_square_sum (a b : Int) :
    2 * (a * b) ≤ a * a + b * b := by
  have hSquare : 0 ≤ (a - b) * (a - b) := by
    simpa [Int.pow_succ] using Int.sq_nonneg (a - b)
  rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm b a] at hSquare
  omega

#print axioms bin_dist_le_scaled_gap
#print axioms twice_product_le_square_sum

end HypothesisS
