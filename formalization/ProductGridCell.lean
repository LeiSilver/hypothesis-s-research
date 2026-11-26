import Lean

/-! Product bounds for a rectangular cell meeting the sharp cutoff. -/

set_option autoImplicit false

open Std Lean.Grind

namespace HypothesisS

variable {R : Type} [CommRing R] [LE R] [LT R]
    [LawfulOrderLT R] [IsLinearOrder R] [OrderedRing R]

theorem product_grid_cell_collar
    (loX hiX loY hiY x y cap maxX maxY widthX widthY : R)
    (hX : 0 ≤ loX ∧ loX ≤ x ∧ x ≤ hiX ∧ hiX ≤ maxX)
    (hY : 0 ≤ loY ∧ loY ≤ y ∧ y ≤ hiY ∧ hiY ≤ maxY)
    (hWidthX : hiX - loX ≤ widthX)
    (hWidthY : hiY - loY ≤ widthY)
    (hCross : loX * loY ≤ cap ∧ cap ≤ hiX * hiY) :
    cap - (maxY * widthX + maxX * widthY) ≤ x * y ∧
      x * y ≤ cap + (maxY * widthX + maxX * widthY) := by
  have hLower : loX * loY ≤ x * y := by
    calc
      loX * loY ≤ x * loY :=
        OrderedRing.mul_le_mul_of_nonneg_right hX.2.1 hY.1
      _ ≤ x * y := OrderedRing.mul_le_mul_of_nonneg_left hY.2.1 (by grind)
  have hUpper : x * y ≤ hiX * hiY := by
    calc
      x * y ≤ hiX * y :=
        OrderedRing.mul_le_mul_of_nonneg_right hX.2.2.1 (by grind)
      _ ≤ hiX * hiY := OrderedRing.mul_le_mul_of_nonneg_left hY.2.2.1 (by grind)
  have hHorizontal : (hiX - loX) * hiY ≤ maxY * widthX := by
    calc
      (hiX - loX) * hiY ≤ widthX * hiY :=
        OrderedRing.mul_le_mul_of_nonneg_right hWidthX (by grind)
      _ ≤ widthX * maxY :=
        OrderedRing.mul_le_mul_of_nonneg_left hY.2.2.2 (by grind)
      _ = maxY * widthX := by grind
  have hVertical : loX * (hiY - loY) ≤ maxX * widthY := by
    calc
      loX * (hiY - loY) ≤ loX * widthY :=
        OrderedRing.mul_le_mul_of_nonneg_left hWidthY hX.1
      _ ≤ maxX * widthY :=
        OrderedRing.mul_le_mul_of_nonneg_right (by grind) (by grind)
  have hSpan :
      hiX * hiY - loX * loY =
        (hiX - loX) * hiY + loX * (hiY - loY) := by grind
  grind

#print axioms product_grid_cell_collar

end HypothesisS
