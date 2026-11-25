import Lean

/-!
Algebraic bounds used to cut the congruence lines in §9.3 of the
Hypothesis S manuscript. All inequalities are exact and stated over a
linearly ordered commutative ring.
-/

set_option autoImplicit false

open Std Lean.Grind

namespace HypothesisS

section

variable {R : Type} [CommRing R]

/-- The product of the coordinates on the line with sum h. -/
def reflectionProduct (h x : R) : R := x * (h - x)

/-- The product of the coordinates on the line with signed difference h. -/
def differenceProduct (h x : R) : R := x * (x + h)

theorem reflection_discriminant (h x : R) :
    (h - 2 * x) ^ 2 + 4 * reflectionProduct h x = h ^ 2 := by
  unfold reflectionProduct
  grind

variable [LE R] [LT R] [LawfulOrderLT R] [IsLinearOrder R] [OrderedRing R]

/-- The line contributes nothing strictly above a cutoff at or above its vertex. -/
theorem reflection_excluded_above_cutoff {h x cutoff : R}
    (hVertex : h ^ 2 ≤ 4 * cutoff) : reflectionProduct h x ≤ cutoff := by
  have hSquare := OrderedRing.sq_nonneg (a := h - 2 * x)
  have hIdentity := reflection_discriminant h x
  grind

/-- Vertex exclusion in the modulus-scaled variables of the manuscript. -/
theorem scaled_reflection_excluded_above_cutoff {b modulus x cutoff : R}
    (hVertex : b ^ 2 ≤ 4 * cutoff) :
    reflectionProduct (b * modulus) x ≤ cutoff * modulus ^ 2 := by
  apply reflection_excluded_above_cutoff
  have hScaled :=
    OrderedRing.mul_le_mul_of_nonneg_right hVertex (OrderedRing.sq_nonneg (a := modulus))
  have hLeft : (b * modulus) ^ 2 = b ^ 2 * modulus ^ 2 := by grind
  have hRight : 4 * (cutoff * modulus ^ 2) = (4 * cutoff) * modulus ^ 2 := by grind
  rw [hLeft, hRight]
  exact hScaled

private theorem le_of_square_le_square {a b : R} (hb : 0 ≤ b)
    (hSquare : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_cases hab : a ≤ b
  · exact hab
  have hDifference : 0 < a - b := by grind
  have hSum : 0 < a + b := by grind
  have hPositive := OrderedRing.mul_pos hDifference hSum
  have hFactor : (a - b) * (a + b) = a ^ 2 - b ^ 2 := by grind
  grind

/-- A gap below the vertex bounds the slope on the left branch from below. -/
theorem reflection_left_slope {h x upper margin : R}
    (hLeft : 2 * x ≤ h) (hProduct : reflectionProduct h x ≤ upper)
    (hGap : 4 * upper + margin ^ 2 ≤ h ^ 2) : margin ≤ h - 2 * x := by
  have hIdentity := reflection_discriminant h x
  apply le_of_square_le_square
  · grind
  · grind

/-- A gap below the vertex also bounds the magnitude of the right branch slope. -/
theorem reflection_right_slope {h x upper margin : R}
    (hRight : h ≤ 2 * x) (hProduct : reflectionProduct h x ≤ upper)
    (hGap : 4 * upper + margin ^ 2 ≤ h ^ 2) : margin ≤ 2 * x - h := by
  have hIdentity := reflection_discriminant h x
  have hSameSquare : (2 * x - h) ^ 2 = (h - 2 * x) ^ 2 := by grind
  apply le_of_square_le_square
  · grind
  · grind

theorem reflection_left_separation {h a b lower upper margin : R}
    (hab : a ≤ b) (hSlope : margin ≤ h - 2 * b)
    (hLower : lower ≤ reflectionProduct h a)
    (hUpper : reflectionProduct h b ≤ upper) :
    (b - a) * (b - a + margin) ≤ upper - lower := by
  have hDifference : 0 ≤ b - a := by grind
  have hFactor :
      reflectionProduct h b - reflectionProduct h a = (b - a) * (h - a - b) := by
    unfold reflectionProduct
    grind
  calc
    (b - a) * (b - a + margin) ≤ (b - a) * (h - a - b) :=
      OrderedRing.mul_le_mul_of_nonneg_left (by grind) hDifference
    _ = reflectionProduct h b - reflectionProduct h a := hFactor.symm
    _ ≤ upper - lower := by grind

theorem reflection_right_separation {h a b lower upper margin : R}
    (hab : a ≤ b) (hSlope : margin ≤ 2 * a - h)
    (hLower : lower ≤ reflectionProduct h b)
    (hUpper : reflectionProduct h a ≤ upper) :
    (b - a) * (b - a + margin) ≤ upper - lower := by
  have hDifference : 0 ≤ b - a := by grind
  have hFactor :
      reflectionProduct h a - reflectionProduct h b = (b - a) * (a + b - h) := by
    unfold reflectionProduct
    grind
  calc
    (b - a) * (b - a + margin) ≤ (b - a) * (a + b - h) :=
      OrderedRing.mul_le_mul_of_nonneg_left (by grind) hDifference
    _ = reflectionProduct h a - reflectionProduct h b := hFactor.symm
    _ ≤ upper - lower := by grind

/-- Bound two points on one branch of the reflection line in the same product band. -/
theorem reflection_band_separation {h a b lower upper margin : R}
    (hab : a ≤ b) (hBranch : 2 * b ≤ h ∨ h ≤ 2 * a)
    (haLower : lower ≤ reflectionProduct h a)
    (haUpper : reflectionProduct h a ≤ upper)
    (hbLower : lower ≤ reflectionProduct h b)
    (hbUpper : reflectionProduct h b ≤ upper)
    (hGap : 4 * upper + margin ^ 2 ≤ h ^ 2) :
    (b - a) * (b - a + margin) ≤ upper - lower := by
  rcases hBranch with hLeft | hRight
  · exact reflection_left_separation hab (reflection_left_slope hLeft hbUpper hGap)
      haLower hbUpper
  · exact reflection_right_separation hab (reflection_right_slope hRight haUpper hGap)
      hbLower haUpper

/-- Bound two points in a product band on a difference line, for either sign of h. -/
theorem difference_band_separation {h a b lower upper margin : R}
    (hab : a ≤ b) (hSlope : margin ≤ 2 * a + h)
    (hLower : lower ≤ differenceProduct h a)
    (hUpper : differenceProduct h b ≤ upper) :
    (b - a) * (b - a + margin) ≤ upper - lower := by
  have hDifference : 0 ≤ b - a := by grind
  have hFactor :
      differenceProduct h b - differenceProduct h a = (b - a) * (a + b + h) := by
    unfold differenceProduct
    grind
  calc
    (b - a) * (b - a + margin) ≤ (b - a) * (a + b + h) :=
      OrderedRing.mul_le_mul_of_nonneg_left (by grind) hDifference
    _ = differenceProduct h b - differenceProduct h a := hFactor.symm
    _ ≤ upper - lower := by grind

private theorem linear_width {d margin width : R} (hd : 0 ≤ d)
    (hWidth : d * (d + margin) ≤ width) : margin * d ≤ width := by
  have hSquare := OrderedRing.mul_nonneg hd hd
  have hExpand : d * (d + margin) = d * d + margin * d := by grind
  grind

theorem reflection_band_width {h a b lower upper margin : R}
    (hab : a ≤ b) (hBranch : 2 * b ≤ h ∨ h ≤ 2 * a)
    (haLower : lower ≤ reflectionProduct h a)
    (haUpper : reflectionProduct h a ≤ upper)
    (hbLower : lower ≤ reflectionProduct h b)
    (hbUpper : reflectionProduct h b ≤ upper)
    (hGap : 4 * upper + margin ^ 2 ≤ h ^ 2) :
    margin * (b - a) ≤ upper - lower :=
  linear_width (by grind)
    (reflection_band_separation hab hBranch haLower haUpper hbLower hbUpper hGap)

theorem difference_band_width {h a b lower upper margin : R}
    (hab : a ≤ b) (hSlope : margin ≤ 2 * a + h)
    (hLower : lower ≤ differenceProduct h a)
    (hUpper : differenceProduct h b ≤ upper) :
    margin * (b - a) ≤ upper - lower :=
  linear_width (by grind) (difference_band_separation hab hSlope hLower hUpper)

end

#print axioms scaled_reflection_excluded_above_cutoff
#print axioms reflection_band_width
#print axioms difference_band_width

end HypothesisS
