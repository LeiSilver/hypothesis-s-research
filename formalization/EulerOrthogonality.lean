import Lean

/-! Finite arithmetic in the mean-square estimate for deleted Euler factors. -/

set_option autoImplicit false

namespace HypothesisS

/-- Removing local factors whose product is at most the square root of
the modulus leaves a residual modulus at least as large as that square root. -/
theorem residual_modulus_square_bound (localFactors residual : Nat)
    (hLocal : 0 < localFactors)
    (hSquare : localFactors * localFactors ≤ localFactors * residual) :
    localFactors * residual ≤ residual * residual := by
  have hFactor := Nat.le_of_mul_le_mul_left hSquare hLocal
  exact Nat.mul_le_mul_right residual hFactor

/-- The signed odd-character residue factor is diagonal below the sum cutoff. -/
theorem odd_residue_weight_below_sum_cutoff (modulus x y : Nat)
    (hX : 0 < x) (hY : 0 < y) (hSum : x + y < modulus) :
    (if x % modulus = y % modulus then (1 : Int) else 0) -
      (if (x + y) % modulus = 0 then 1 else 0) =
      (if x = y then 1 else 0) := by
  have hXBelow : x < modulus := by omega
  have hYBelow : y < modulus := by omega
  have hNonzero : x ≠ 0 := Nat.ne_of_gt hX
  simp [Nat.mod_eq_of_lt hXBelow, Nat.mod_eq_of_lt hYBelow,
    Nat.mod_eq_of_lt hSum, hNonzero]

#print axioms residual_modulus_square_bound
#print axioms odd_residue_weight_below_sum_cutoff

end HypothesisS
