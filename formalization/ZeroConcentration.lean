import Lean

/-! Finite inequalities for a nonnegative zero-count probe with a signed error. -/

set_option autoImplicit false

namespace HypothesisS

/-- A nonnegative probe majorizes the selected labels on which it is bounded below. -/
theorem selected_count_le_probe_mass {α : Type} (labels : List α)
    (selected : α → Bool) (weight : α → Int) (lower : Int)
    (hNonnegative : ∀ label ∈ labels, 0 ≤ weight label)
    (hSelected : ∀ label ∈ labels, selected label = true → lower ≤ weight label) :
    lower * (labels.filter selected).length ≤ (labels.map weight).sum := by
  induction labels with
  | nil => simp
  | cons label tail ih =>
    have hTail := ih
      (fun x hx => hNonnegative x (List.mem_cons_of_mem label hx))
      (fun x hx => hSelected x (List.mem_cons_of_mem label hx))
    have hHead := hNonnegative label (by simp)
    cases hSelect : selected label with
    | false =>
      simp only [List.filter_cons, hSelect, Bool.false_eq_true, ↓reduceIte,
        List.map_cons, List.sum_cons]
      omega
    | true =>
      have hHeadLower := hSelected label (by simp) hSelect
      simp only [List.filter_cons, hSelect, ↓reduceIte, List.length_cons,
        Int.natCast_succ, Int.mul_add, Int.mul_one, List.map_cons, List.sum_cons]
      omega

/-- Transferring the probe's lower bound through a real-part signal and an error. -/
theorem squared_count_le_signal_error {count lower signal error : Int}
    (hNonnegative : 0 ≤ lower * count)
    (hDominates : lower * count ≤ 2 * signal + error) :
    (lower * count) * (lower * count) ≤
      8 * (signal * signal) + 2 * (error * error) := by
  let a := 2 * signal
  let b := error
  have hRight : 0 ≤ a + b := by
    exact Int.le_trans hNonnegative hDominates
  have hFirst := Int.mul_le_mul_of_nonneg_right hDominates hNonnegative
  have hSecond := Int.mul_le_mul_of_nonneg_left hDominates hRight
  have hSquare : 0 ≤ (a - b) * (a - b) := by
    simpa [Int.pow_succ] using Int.sq_nonneg (a - b)
  rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm b a] at hSquare
  have hSum : (a + b) * (a + b) ≤ 2 * (a * a + b * b) := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm b a]
    omega
  have hScale : a * a = 4 * (signal * signal) := by
    dsimp [a]
    rw [Int.mul_assoc, ← Int.mul_assoc signal 2, Int.mul_comm signal 2,
      Int.mul_assoc 2 signal, ← Int.mul_assoc 2 2]
    rfl
  calc
    (lower * count) * (lower * count) ≤ (a + b) * (a + b) :=
      Int.le_trans hFirst hSecond
    _ ≤ 2 * (a * a + b * b) := hSum
    _ = 8 * (signal * signal) + 2 * (error * error) := by
      rw [hScale]
      dsimp [b]
      omega

#print axioms selected_count_le_probe_mass
#print axioms squared_count_le_signal_error

end HypothesisS
