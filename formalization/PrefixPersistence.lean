import Lean

/-! The finite sum estimate when a prefix discrepancy remains large
on an interval of sample points. -/

set_option autoImplicit false

namespace HypothesisS

theorem peak_times_length_le_twice_sum (peak : Nat) (values : List Nat)
    (hValues : ∀ value ∈ values, peak ≤ 2 * value) :
    peak * values.length ≤ 2 * values.sum := by
  induction values with
  | nil => simp
  | cons value tail ih =>
    have hHead := hValues value (List.mem_cons_self)
    have hTail := ih (fun entry hEntry =>
      hValues entry (List.mem_cons_of_mem value hEntry))
    simp only [List.length_cons, List.sum_cons, Nat.mul_succ, Nat.mul_add]
    omega

/-- If the interval length controls the peak up to a jump allowance,
the squared peak is controlled by the mass on the interval and that allowance. -/
theorem squared_peak_bound (peak slope jump : Nat) (values : List Nat)
    (hValues : ∀ value ∈ values, peak ≤ 2 * value)
    (hLength : peak ≤ 4 * slope * values.length + 2 * jump) :
    peak * peak ≤ 8 * slope * values.sum + 2 * jump * peak := by
  have hMass := peak_times_length_le_twice_sum peak values hValues
  calc
    peak * peak ≤ (4 * slope * values.length + 2 * jump) * peak :=
      Nat.mul_le_mul_right peak hLength
    _ = (4 * slope) * (peak * values.length) + 2 * jump * peak := by
      rw [Nat.add_mul]
      ac_rfl
    _ ≤ (4 * slope) * (2 * values.sum) + 2 * jump * peak :=
      Nat.add_le_add_right (Nat.mul_le_mul_left (4 * slope) hMass) _
    _ = (4 * 2) * slope * values.sum + 2 * jump * peak := by ac_rfl
    _ = _ := rfl

#print axioms peak_times_length_le_twice_sum
#print axioms squared_peak_bound

end HypothesisS
