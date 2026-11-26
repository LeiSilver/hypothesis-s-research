import Lean

/-! At a fixed dyadic scale, the maximal blocks in a cell interval
can be assigned injectively to its two endpoints. -/

set_option autoImplicit false

namespace HypothesisS

def leftBoundary (lo width index : Nat) : Prop :=
  (index - 1) * width < lo ∧ lo ≤ index * width

def rightBoundary (hi width index : Nat) : Prop :=
  (index + 1) * width ≤ hi ∧ hi < (index + 2) * width

def parentInside (lo hi width index : Nat) : Prop :=
  if index % 2 = 0 then
    lo ≤ index * width ∧ (index + 2) * width ≤ hi
  else
    lo ≤ (index - 1) * width ∧ (index + 1) * width ≤ hi

/-- A contained block whose parent is outside crosses one endpoint. -/
theorem maximal_block_has_boundary (lo hi width index : Nat)
    (hLo : lo ≤ index * width) (hHi : (index + 1) * width ≤ hi)
    (hParent : ¬parentInside lo hi width index) :
    leftBoundary lo width index ∨ rightBoundary hi width index := by
  by_cases hEven : index % 2 = 0
  · simp [parentInside, hEven, hLo] at hParent
    exact Or.inr ⟨hHi, by omega⟩
  · simp [parentInside, hEven, hHi] at hParent
    exact Or.inl ⟨by omega, hLo⟩

theorem left_boundary_unique (lo width first second : Nat)
    (hFirst : leftBoundary lo width first)
    (hSecond : leftBoundary lo width second) : first = second := by
  unfold leftBoundary at hFirst hSecond
  by_cases hOrder : first < second
  · have hMul := Nat.mul_le_mul_right width (show first ≤ second - 1 by omega)
    omega
  · by_cases hOrder' : second < first
    · have hMul := Nat.mul_le_mul_right width (show second ≤ first - 1 by omega)
      omega
    · omega

theorem right_boundary_unique (hi width first second : Nat)
    (hFirst : rightBoundary hi width first)
    (hSecond : rightBoundary hi width second) : first = second := by
  unfold rightBoundary at hFirst hSecond
  by_cases hOrder : first < second
  · have hMul := Nat.mul_le_mul_right width (show first + 2 ≤ second + 1 by omega)
    omega
  · by_cases hOrder' : second < first
    · have hMul := Nat.mul_le_mul_right width (show second + 2 ≤ first + 1 by omega)
      omega
    · omega

#print axioms maximal_block_has_boundary
#print axioms left_boundary_unique
#print axioms right_boundary_unique

end HypothesisS
