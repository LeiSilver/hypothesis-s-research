import Lean

/-! The local conductor sieve as a signed sum over sublists. -/

set_option autoImplicit false

namespace HypothesisS

def signedSubsetSum {α : Type} (items : List α) (weight : List α → Int) : Int :=
  match items with
  | [] => weight []
  | item :: tail =>
    signedSubsetSum tail weight - signedSubsetSum tail (fun subset => weight (item :: subset))

private theorem signedSubsetSum_mul {α : Type} (items : List α)
    (weight : List α → Int) (c : Int) :
    signedSubsetSum items (fun subset => c * weight subset) =
      c * signedSubsetSum items weight := by
  induction items generalizing weight with
  | nil => rfl
  | cons item tail ih =>
    simp only [signedSubsetSum, ih, Int.mul_sub]

/-- The signed sum of multiplicative subset weights factors over the items. -/
theorem signedSubsetSum_product {α : Type} (items : List α) (localWeight : α → Int) :
    signedSubsetSum items (fun subset => (subset.map localWeight).prod) =
      (items.map (fun item => 1 - localWeight item)).prod := by
  induction items with
  | nil => rfl
  | cons item tail ih =>
    simp only [signedSubsetSum, List.map_cons, List.prod_cons, signedSubsetSum_mul, ih]
    rw [Int.sub_mul, Int.one_mul]

/-- A character contributes with weight one exactly when no selected local conductor drops. -/
theorem fullConductor_subset_sieve {α : Type} (items : List α) (drops : α → Bool) :
    signedSubsetSum items (fun subset => (subset.map (fun p => if drops p then 1 else 0)).prod) =
      if items.any drops then 0 else 1 := by
  rw [signedSubsetSum_product]
  induction items with
  | nil => rfl
  | cons item tail ih =>
    cases hDrop : drops item <;> simp [List.any_cons, hDrop, ih]

/-- A conductor exponent determines exactly one block at its prime. -/
theorem localConductor_loss_unique {modulusExponent conductorExponent : Nat}
    (hDivides : conductorExponent ≤ modulusExponent) :
    ∃ loss : Nat, loss ≤ modulusExponent ∧ modulusExponent - loss = conductorExponent ∧
      ∀ other : Nat, other ≤ modulusExponent → modulusExponent - other = conductorExponent →
        other = loss := by
  refine ⟨modulusExponent - conductorExponent, by omega, by omega, ?_⟩
  intro other hOther hExponent
  omega

/-- A short threshold interval contains at most one lattice point. -/
theorem threshold_interval_integer_unique {denominator lower upper x y : Int}
    (hDenominator : 0 < denominator) (hWidth : upper - lower < denominator)
    (hxLower : lower < x * denominator) (hxUpper : x * denominator ≤ upper)
    (hyLower : lower < y * denominator) (hyUpper : y * denominator ≤ upper) :
    x = y := by
  have separated {a b : Int} (h : a < b) :
      a * denominator + denominator ≤ b * denominator := by
    have hSucc : a + 1 ≤ b := by omega
    have hProduct := Int.mul_le_mul_of_nonneg_right hSucc (by omega : 0 ≤ denominator)
    simpa only [Int.add_mul, Int.one_mul] using hProduct
  have hOrder : x < y ∨ x = y ∨ y < x := by omega
  rcases hOrder with h | h | h
  · have hGap := separated h
    omega
  · exact h
  · have hGap := separated h
    omega

#print axioms fullConductor_subset_sieve
#print axioms localConductor_loss_unique
#print axioms threshold_interval_integer_unique

end HypothesisS
