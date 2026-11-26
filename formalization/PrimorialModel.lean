import Lean

/-! The endpoint term in the finite trapezoidal sum. Integer weights
also cover rational samples after clearing a common denominator. -/

set_option autoImplicit false

namespace HypothesisS

def twiceTrapezoidalSum (left : Int) (samples : List Int) : Int :=
  match samples with
  | [] => 0
  | right :: tail =>
    left + right + twiceTrapezoidalSum right tail

/-- The two endpoints enter once and each interior sample enters twice. -/
theorem twice_trapezoidal_sum_endpoints (left : Int) (samples : List Int) :
    twiceTrapezoidalSum left samples + samples.getLastD left =
      left + 2 * samples.sum := by
  induction samples generalizing left with
  | nil => simp [twiceTrapezoidalSum]
  | cons right tail ih =>
    cases tail with
    | nil => simp [twiceTrapezoidalSum, Int.two_mul, Int.add_assoc]
    | cons next tail =>
      have hTail := ih right
      simp only [twiceTrapezoidalSum, List.getLastD_cons, List.sum_cons, Int.add_assoc] at *
      omega

/-- A vanishing final sample gives the subtraction at the initial endpoint. -/
theorem twice_lattice_sum_from_trapezoidal_sum
    (left : Int) (samples : List Int) (hLast : samples.getLastD left = 0) :
    2 * samples.sum = twiceTrapezoidalSum left samples - left := by
  have hSum := twice_trapezoidal_sum_endpoints left samples
  omega

#print axioms twice_trapezoidal_sum_endpoints
#print axioms twice_lattice_sum_from_trapezoidal_sum

end HypothesisS
