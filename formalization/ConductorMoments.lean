import Lean

/-! Finite identities for the conductor tail and the character moment. -/

set_option autoImplicit false

namespace HypothesisS

noncomputable def weightedMoment (weight : Nat → Rat) (masses : List Rat)
    (offset : Nat) : Rat :=
  match masses with
  | [] => 0
  | mass :: tail =>
    weight offset * mass + weightedMoment weight tail (offset + 1)

noncomputable def tailMomentCorrection (weight : Nat → Rat) (masses : List Rat)
    (offset : Nat) : Rat :=
  match masses with
  | [] => 0
  | _ :: tail =>
    (weight (offset + 1) - weight offset) * tail.sum +
      tailMomentCorrection weight tail (offset + 1)

/-- A finite moment is its constant term plus the weight increments times tail masses. -/
theorem weighted_moment_eq_tail_increments
    (weight : Nat → Rat) (masses : List Rat) (offset : Nat) :
    weightedMoment weight masses offset =
      weight offset * masses.sum + tailMomentCorrection weight masses offset := by
  induction masses generalizing offset with
  | nil => simp [weightedMoment, tailMomentCorrection, Rat.zero_add]
  | cons mass tail ih =>
    have hIncrement :
        weight (offset + 1) * tail.sum =
          weight offset * tail.sum + (weight (offset + 1) - weight offset) * tail.sum := by
      rw [← Rat.add_mul, Rat.add_comm (weight offset), Rat.sub_add_cancel]
    simp only [weightedMoment, tailMomentCorrection, List.sum_cons, ih]
    rw [hIncrement, Rat.mul_add]
    simp only [Rat.add_assoc]

/-- Products in an expanded character polynomial remain below the powered cutoff. -/
theorem product_cutoff_pow (factors : List Nat) (cutoff : Nat)
    (hBound : ∀ factor ∈ factors, factor ≤ cutoff) :
    factors.prod ≤ cutoff ^ factors.length := by
  induction factors with
  | nil => simp
  | cons factor tail ih =>
    have hFactor := hBound factor (by simp)
    have hTail := ih (fun n hn => hBound n (List.mem_cons_of_mem factor hn))
    simpa only [List.prod_cons, List.length_cons, Nat.pow_succ, Nat.mul_comm] using
      Nat.mul_le_mul hFactor hTail

#print axioms weighted_moment_eq_tail_increments
#print axioms product_cutoff_pow

end HypothesisS
