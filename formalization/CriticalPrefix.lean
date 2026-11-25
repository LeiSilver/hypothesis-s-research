import Lean

/-!
The finite-sum and scale-index arguments in the critical prefix test.
Cell weights may be signed. Lengths may vanish, and rectangles may start
or end at any grid cut.
-/

set_option autoImplicit false

open Std Lean.Grind

namespace HypothesisS

section Prefix

universe u
variable {R : Type u} [CommRing R]

/-- The sum over consecutive indices beginning at start. -/
def intervalSum (f : Nat → R) (start : Nat) : Nat → R
  | 0 => 0
  | length + 1 => intervalSum f start length + f (start + length)

private theorem intervalSum_split (f : Nat → R) (start first second : Nat) :
    intervalSum f start (first + second) =
      intervalSum f start first + intervalSum f (start + first) second := by
  induction second with
  | zero => simp only [intervalSum, Semiring.add_zero]
  | succ n step =>
    simp only [intervalSum, Nat.add_assoc]
    grind

private theorem intervalSum_sub_prefix (f : Nat → R) (start length : Nat) :
    intervalSum f start length =
      intervalSum f 0 (start + length) - intervalSum f 0 start := by
  have h := intervalSum_split f 0 start length
  simp only [Nat.zero_add] at h
  grind

private theorem intervalSum_sub (f g : Nat → R) (start length : Nat) :
    intervalSum (fun i => f i - g i) start length =
      intervalSum f start length - intervalSum g start length := by
  induction length with
  | zero =>
    simp only [intervalSum]
    grind
  | succ n step =>
    simp only [intervalSum, step]
    grind

/-- Signed mass of a consecutive rectangle of grid cells. -/
def rectangleSum (weight : Nat → Nat → R) (row rows col cols : Nat) : R :=
  intervalSum (fun i => intervalSum (weight i) col cols) row rows

def prefixSum (weight : Nat → Nat → R) (rows cols : Nat) : R :=
  rectangleSum weight 0 rows 0 cols

theorem rectangle_eq_four_prefixes (weight : Nat → Nat → R)
    (row rows col cols : Nat) :
    rectangleSum weight row rows col cols =
      prefixSum weight (row + rows) (col + cols) -
      prefixSum weight row (col + cols) -
      prefixSum weight (row + rows) col + prefixSum weight row col := by
  have hCols (i : Nat) := intervalSum_sub_prefix (weight i) col cols
  change intervalSum (fun i => intervalSum (weight i) col cols) row rows = _
  simp only [hCols, intervalSum_sub,
    intervalSum_sub_prefix (start := row) (length := rows)]
  unfold prefixSum rectangleSum
  grind

variable [LE R] [LT R] [LawfulOrderLT R] [IsLinearOrder R] [OrderedRing R]

theorem rectangle_controlled_by_prefixes (weight : Nat → Nat → R)
    (row rows col cols : Nat) (bound : R)
    (hPrefix : ∀ i j, i ≤ row + rows → j ≤ col + cols →
      -bound ≤ prefixSum weight i j ∧ prefixSum weight i j ≤ bound) :
    -4 * bound ≤ rectangleSum weight row rows col cols ∧
    rectangleSum weight row rows col cols ≤ 4 * bound := by
  have hTop := hPrefix (row + rows) (col + cols) (by omega) (by omega)
  have hLeft := hPrefix row (col + cols) (by omega) (by omega)
  have hRight := hPrefix (row + rows) col (by omega) (by omega)
  have hBottom := hPrefix row col (by omega) (by omega)
  rw [rectangle_eq_four_prefixes]
  constructor <;> grind

end Prefix

section Scales

/-- Nonnegative dyadic indices whose sum lies in a specified band. -/
def ScalePair (lower upper : Nat) : Type :=
  {p : Nat × Nat // lower ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ upper}

/-- The first index and the offset of the sum determine the pair. -/
def scalePairCode {lower upper : Nat} (p : ScalePair lower upper) :
    Fin (upper + 1) × Fin (upper - lower + 1) :=
  (⟨p.val.1, by have hu := p.property.2; omega⟩,
   ⟨p.val.1 + p.val.2 - lower, by have hu := p.property.2; omega⟩)

theorem scalePairCode_injective {lower upper : Nat} {p q : ScalePair lower upper}
    (h : scalePairCode p = scalePairCode q) : p = q := by
  have hFirst := congrArg (fun v => v.1.val) h
  have hSum := congrArg (fun v => v.2.val) h
  change p.val.1 = q.val.1 at hFirst
  change p.val.1 + p.val.2 - lower = q.val.1 + q.val.2 - lower at hSum
  have hp := p.property.1
  have hq := q.property.1
  exact Subtype.ext (Prod.ext hFirst (by omega))

/-- The pairs needing the continuous model also have bounded index difference. -/
def ComparableScalePair (lower upper gap : Nat) : Type :=
  {p : Nat × Nat //
    lower ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ upper ∧
    p.1 ≤ p.2 + gap ∧ p.2 ≤ p.1 + gap}

def comparablePairCode {lower upper gap : Nat} (p : ComparableScalePair lower upper gap) :
    Fin (upper - lower + 2 * gap + 1) × Fin (upper - lower + 2 * gap + 1) :=
  (⟨2 * p.val.1 + gap - lower, by
    rcases p.property with ⟨hLower, hUpper, hFirst, hSecond⟩
    omega⟩,
   ⟨2 * p.val.2 + gap - lower, by
    rcases p.property with ⟨hLower, hUpper, hFirst, hSecond⟩
    omega⟩)

theorem comparablePairCode_injective {lower upper gap : Nat}
    {p q : ComparableScalePair lower upper gap}
    (h : comparablePairCode p = comparablePairCode q) : p = q := by
  have hFirst := congrArg (fun v => v.1.val) h
  have hSecond := congrArg (fun v => v.2.val) h
  change 2 * p.val.1 + gap - lower = 2 * q.val.1 + gap - lower at hFirst
  change 2 * p.val.2 + gap - lower = 2 * q.val.2 + gap - lower at hSecond
  rcases p.property with ⟨hpLower, hpUpper, hpFirst, hpSecond⟩
  rcases q.property with ⟨hqLower, hqUpper, hqFirst, hqSecond⟩
  exact Subtype.ext (Prod.ext (by omega) (by omega))

end Scales

#print axioms rectangle_eq_four_prefixes
#print axioms rectangle_controlled_by_prefixes
#print axioms scalePairCode_injective
#print axioms comparablePairCode_injective

end HypothesisS
