import Lean

/-! Finite height symmetrization for an even gap kernel, with labels repeated
according to their multiplicity. -/

set_option autoImplicit false

namespace HypothesisS

noncomputable def finitePairSum {α β : Type} (xs : List α) (ys : List β)
    (weight : α → β → Int) : Int :=
  (xs.map (fun x => (ys.map (weight x)).sum)).sum

private theorem sum_map_add_int {α : Type} (xs : List α) (a b : α → Int) :
    (xs.map (fun x => a x + b x)).sum = (xs.map a).sum + (xs.map b).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

private theorem sum_map_zero_int {α : Type} (xs : List α) :
    (xs.map (fun _ => (0 : Int))).sum = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem finitePairSum_transpose {α β : Type} (xs : List α) (ys : List β)
    (weight : α → β → Int) :
    finitePairSum xs ys weight = finitePairSum ys xs (fun y x => weight x y) := by
  induction xs with
  | nil => simp [finitePairSum, sum_map_zero_int]
  | cons x xs ih =>
    calc
      finitePairSum (x :: xs) ys weight =
          (ys.map (weight x)).sum + finitePairSum xs ys weight := by
        rfl
      _ = (ys.map (weight x)).sum + finitePairSum ys xs (fun y z => weight z y) := by
        rw [ih]
      _ = finitePairSum ys (x :: xs) (fun y z => weight z y) := by
        simp only [finitePairSum, List.map_cons, List.sum_cons, sum_map_add_int]

/-- Swapping the labels shows that averaging the two heights preserves the pair sum.
The factor two allows the result to be stated with integer weights. -/
theorem finitePairSum_symmetrized_height {α : Type} (labels : List α)
    (height : α → Int) (gapKernel : α → α → Int)
    (hSymmetric : ∀ x y, gapKernel x y = gapKernel y x) :
    finitePairSum labels labels (fun x y => (height x + height y) * gapKernel x y) =
      2 * finitePairSum labels labels (fun x y => height x * gapKernel x y) := by
  have hSwap :
      finitePairSum labels labels (fun x y => height y * gapKernel x y) =
        finitePairSum labels labels (fun x y => height x * gapKernel x y) := by
    rw [finitePairSum_transpose labels labels (fun x y => height y * gapKernel x y)]
    congr 1
    funext x y
    rw [hSymmetric y x]
  have hLinear :
      finitePairSum labels labels (fun x y => (height x + height y) * gapKernel x y) =
        finitePairSum labels labels (fun x y => height x * gapKernel x y) +
        finitePairSum labels labels (fun x y => height y * gapKernel x y) := by
    simp only [finitePairSum, Int.add_mul, sum_map_add_int]
  omega

#print axioms finitePairSum_transpose
#print axioms finitePairSum_symmetrized_height

end HypothesisS
