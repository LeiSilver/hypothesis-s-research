import Lean

/-!
The congruence geometry of rectangles formed from one half-modulus cell.
Coordinates may be integers or scaled rational coordinates after a
common positive denominator has been cleared.
-/

set_option autoImplicit false

namespace HypothesisS

private theorem no_multiple_in_open_cell {period index value : Int}
    (hPeriod : 0 < period)
    (hLower : index * period < value)
    (hUpper : value < (index + 1) * period) :
    ¬ period ∣ value := by
  rintro ⟨k, hValue⟩
  rw [Int.mul_comm period k] at hValue
  by_cases h : k ≤ index
  · have hProduct := Int.mul_le_mul_of_nonneg_right h (Int.le_of_lt hPeriod)
    omega
  · have hIndex : index + 1 ≤ k := by omega
    have hProduct := Int.mul_le_mul_of_nonneg_right hIndex (Int.le_of_lt hPeriod)
    omega

/-- The sum of two points in the same open half-modulus cell avoids the lattice. -/
theorem half_cell_sum_not_multiple {period index x x' : Int}
    (hPeriod : 0 < period)
    (hxLower : index * period < 2 * x)
    (hxUpper : 2 * x < (index + 1) * period)
    (hx'Lower : index * period < 2 * x')
    (hx'Upper : 2 * x' < (index + 1) * period) :
    ¬ period ∣ x + x' := by
  exact no_multiple_in_open_cell (index := index) hPeriod (by omega) (by omega)

/-- The difference can be a multiple only if the two points agree. -/
theorem half_cell_difference_multiple_iff {period index x x' : Int}
    (hPeriod : 0 < period)
    (hxLower : index * period < 2 * x)
    (hxUpper : 2 * x < (index + 1) * period)
    (hx'Lower : index * period < 2 * x')
    (hx'Upper : 2 * x' < (index + 1) * period) :
    period ∣ x - x' ↔ x = x' := by
  rw [Int.add_mul, Int.one_mul] at hxUpper hx'Upper
  have hPositive : ¬ (0 < x - x' ∧ period ∣ x - x') := by
    rintro ⟨hSign, hDvd⟩
    exact no_multiple_in_open_cell (index := 0) hPeriod (by simp; omega)
      (by simp; omega) hDvd
  have hNegative : ¬ (x - x' < 0 ∧ period ∣ x - x') := by
    rintro ⟨hSign, hDvd⟩
    exact no_multiple_in_open_cell (index := -1) hPeriod (by simp; omega)
      (by simp; omega) hDvd
  constructor
  · intro hDvd
    by_cases hEqual : x = x'
    · exact hEqual
    exfalso
    have hOrder : x < x' ∨ x' < x := by omega
    rcases hOrder with h | h
    · exact hNegative ⟨by omega, hDvd⟩
    · exact hPositive ⟨by omega, hDvd⟩
  · rintro rfl
    simp

/-- Within the reflected rectangle, only the requested sum line can occur. -/
theorem half_cell_reflection_isolation {period index shift x x' y : Int}
    (hPeriod : 0 < period)
    (hxLower : index * period < 2 * x)
    (hxUpper : 2 * x < (index + 1) * period)
    (hx'Lower : index * period < 2 * x')
    (hx'Upper : 2 * x' < (index + 1) * period)
    (hy : y = shift * period - x') :
    (period ∣ y + x ↔ y + x = shift * period) ∧ ¬ period ∣ y - x := by
  have hShift : period ∣ shift * period := ⟨shift, Int.mul_comm shift period⟩
  have hSum := half_cell_sum_not_multiple hPeriod hxLower hxUpper hx'Lower hx'Upper
  have hDiff := half_cell_difference_multiple_iff hPeriod hxLower hxUpper hx'Lower hx'Upper
  constructor
  · constructor
    · intro hMultiple
      have hDifference := Int.dvd_sub hMultiple hShift
      have hIdentity : (y + x) - shift * period = x - x' := by omega
      rw [hIdentity] at hDifference
      have hEqual := hDiff.mp hDifference
      omega
    · intro hLine
      exact hLine ▸ hShift
  · intro hMultiple
    have hTotal := Int.dvd_sub hShift hMultiple
    have hIdentity : shift * period - (y - x) = x + x' := by omega
    rw [hIdentity] at hTotal
    exact hSum hTotal

/-- Within the translated rectangle, only the requested difference line can occur. -/
theorem half_cell_translation_isolation {period index shift x x' y : Int}
    (hPeriod : 0 < period)
    (hxLower : index * period < 2 * x)
    (hxUpper : 2 * x < (index + 1) * period)
    (hx'Lower : index * period < 2 * x')
    (hx'Upper : 2 * x' < (index + 1) * period)
    (hy : y = shift * period + x') :
    (period ∣ y - x ↔ y - x = shift * period) ∧ ¬ period ∣ y + x := by
  have hShift : period ∣ shift * period := ⟨shift, Int.mul_comm shift period⟩
  have hSum := half_cell_sum_not_multiple hPeriod hxLower hxUpper hx'Lower hx'Upper
  have hDiff := half_cell_difference_multiple_iff hPeriod hxLower hxUpper hx'Lower hx'Upper
  constructor
  · constructor
    · intro hMultiple
      have hDifference := Int.dvd_sub hShift hMultiple
      have hIdentity : shift * period - (y - x) = x - x' := by omega
      rw [hIdentity] at hDifference
      have hEqual := hDiff.mp hDifference
      omega
    · intro hLine
      exact hLine ▸ hShift
  · intro hMultiple
    have hTotal := Int.dvd_sub hMultiple hShift
    have hIdentity : (y + x) - shift * period = x + x' := by omega
    rw [hIdentity] at hTotal
    exact hSum hTotal

#print axioms half_cell_reflection_isolation
#print axioms half_cell_translation_isolation

end HypothesisS
