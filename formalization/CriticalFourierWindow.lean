import Lean

/-! The clipped congruence line has no frequency alias at zero when
the sampling period exceeds twice the window radius. -/

set_option autoImplicit false

namespace HypothesisS

def lineFrequency (reflected : Bool) (n t shift : Int) : Int :=
  if reflected then t + n - shift else t - n - shift

/-- The clipping window retains every point on the signed line. -/
theorem line_inside_window (reflected : Bool) (n t shift radius : Int)
    (hn : 0 ≤ n) (hbound : n ≤ radius)
    (hline : lineFrequency reflected n t shift = 0) :
    -radius ≤ t - shift ∧ t - shift ≤ radius := by
  cases reflected <;> simp [lineFrequency] at hline <;> omega

/-- A zero sampled frequency detects exact line membership under clipping. -/
theorem sampled_zero_frequency_iff (reflected : Bool) (n t shift radius period : Int)
    (hn : 0 ≤ n) (hbound : n ≤ radius)
    (htLower : -radius ≤ t - shift) (htUpper : t - shift ≤ radius)
    (hperiod : 2 * radius < period) :
    lineFrequency reflected n t shift % period = 0 ↔
      lineFrequency reflected n t shift = 0 := by
  let frequency := lineFrequency reflected n t shift
  change frequency % period = 0 ↔ frequency = 0
  have hRange : -2 * radius ≤ frequency ∧ frequency ≤ 2 * radius := by
    cases reflected <;> simp [frequency, lineFrequency] <;> omega
  by_cases hNonnegative : 0 ≤ frequency
  · rw [Int.emod_eq_of_lt hNonnegative (by omega : frequency < period)]
  · have hShift : (frequency + period) % period = frequency % period := by
      simp
    rw [← hShift, Int.emod_eq_of_lt (by omega : 0 ≤ frequency + period)
      (by omega : frequency + period < period)]
    omega

#print axioms line_inside_window
#print axioms sampled_zero_frequency_iff

end HypothesisS
