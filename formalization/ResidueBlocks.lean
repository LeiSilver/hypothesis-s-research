import Lean

/-! Counting residues in complete periods followed by an incomplete period.
The labels start at zero after translating the beginning of the interval. -/

set_option autoImplicit false

namespace HypothesisS

private theorem count_full_periods (modulus periods residue : Nat)
    (hResidue : residue < modulus) :
    List.count residue (List.replicate periods (List.range modulus)).flatten =
      periods := by
  induction periods with
  | zero => simp
  | succ periods ih =>
    simp only [List.replicate_succ, List.flatten_cons, List.count_append,
      List.count_range, ih]
    simp [hResidue, Nat.add_comm]

theorem residue_count_in_blocks (modulus periods tail residue : Nat)
    (hResidue : residue < modulus) :
    List.count residue
        ((List.replicate periods (List.range modulus)).flatten ++ List.range tail) =
      periods + (if residue < tail then 1 else 0) := by
  rw [List.count_append, count_full_periods modulus periods residue hResidue,
    List.count_range]

/-- Any two residues differ in count by at most one on the same interval. -/
theorem residue_counts_within_one (modulus periods tail left right : Nat)
    (hLeft : left < modulus) (hRight : right < modulus) :
    let interval :=
      (List.replicate periods (List.range modulus)).flatten ++ List.range tail
    List.count left interval ≤ List.count right interval + 1 ∧
      List.count right interval ≤ List.count left interval + 1 := by
  dsimp
  rw [residue_count_in_blocks modulus periods tail left hLeft,
    residue_count_in_blocks modulus periods tail right hRight]
  by_cases hLeftTail : left < tail <;>
    by_cases hRightTail : right < tail <;> simp [hLeftTail, hRightTail] <;> omega

#print axioms residue_count_in_blocks
#print axioms residue_counts_within_one

end HypothesisS
