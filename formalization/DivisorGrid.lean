import Lean

/-! Finite shift and interval bounds for rational samples of the divisor grid.
Numerators and grid endpoints are expressed with a common denominator. -/

set_option autoImplicit false

namespace HypothesisS

/-- A sample above the lower cutoff has only finitely many relevant shifts. -/
theorem shift_bound_above_divisor_cutoff (d r q m cap : Nat)
    (hAbove : r < q * d) (hSupport : m * d ≤ cap * r) :
    m ≤ cap * q := by
  apply Nat.le_of_not_gt
  intro hLarger
  have hD : 0 < d := by
    apply Nat.pos_of_ne_zero
    intro hEq
    simp [hEq] at hAbove
  have hCut : cap * r ≤ (cap * q) * d := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left cap (Nat.le_of_lt hAbove)
  have hShift := Nat.mul_lt_mul_of_pos_right hLarger hD
  omega

def rightGridIndex (numerator width : Nat) : Nat :=
  (numerator - 1) / width + 1

/-- The grid intervals are open on the left and closed on the right. -/
theorem right_grid_index_bounds (numerator width : Nat)
    (hNumerator : 0 < numerator) (hWidth : 0 < width) :
    let i := rightGridIndex numerator width
    (i - 1) * width < numerator ∧ numerator ≤ i * width := by
  have hDecomp := Nat.div_add_mod (numerator - 1) width
  have hRemainder := Nat.mod_lt (numerator - 1) hWidth
  simp [rightGridIndex, Nat.add_mul, Nat.mul_comm width] at *
  omega

#print axioms shift_bound_above_divisor_cutoff
#print axioms right_grid_index_bounds

end HypothesisS
