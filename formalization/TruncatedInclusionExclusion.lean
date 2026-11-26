import Lean

/-! The finite error bound for inclusion-exclusion truncated by the number
of selected prime factors. -/

set_option autoImplicit false

namespace HypothesisS

def selectionCount : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => selectionCount n k + selectionCount n (k + 1)

def alternatingSign (k : Nat) : Int :=
  if k % 2 = 0 then 1 else -1

def alternatingPrefix (n : Nat) : Nat → Int
  | 0 => 1
  | k + 1 => alternatingPrefix n k +
      alternatingSign (k + 1) * Int.ofNat (selectionCount n (k + 1))

private theorem alternatingSign_succ (k : Nat) :
    alternatingSign (k + 1) = -alternatingSign k := by
  by_cases h : k % 2 = 0
  · have hNext : (k + 1) % 2 ≠ 0 := by omega
    simp [alternatingSign, h, hNext]
  · have hNext : (k + 1) % 2 = 0 := by omega
    simp [alternatingSign, h, hNext]

theorem alternatingPrefix_empty (k : Nat) :
    alternatingPrefix 0 k = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [alternatingPrefix, selectionCount, ih]

/-- Pascal's identity collapses the alternating prefix. -/
theorem alternatingPrefix_nonempty (n k : Nat) :
    alternatingPrefix (n + 1) k =
      alternatingSign k * Int.ofNat (selectionCount n k) := by
  induction k with
  | zero => simp [alternatingPrefix, alternatingSign, selectionCount]
  | succ k ih =>
    simp only [alternatingPrefix, ih, alternatingSign_succ, selectionCount,
      Int.ofNat_eq_natCast, Int.natCast_add, Int.mul_add, Int.neg_mul]
    omega

theorem truncated_inclusion_exclusion_error (n k : Nat) :
    (alternatingPrefix (n + 1) k).natAbs ≤ selectionCount (n + 1) (k + 1) := by
  rw [alternatingPrefix_nonempty]
  by_cases h : k % 2 = 0 <;>
    simp [alternatingSign, h, selectionCount]

#print axioms alternatingPrefix_empty
#print axioms alternatingPrefix_nonempty
#print axioms truncated_inclusion_exclusion_error

end HypothesisS
