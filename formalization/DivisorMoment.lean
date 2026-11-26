import Lean

/-! The injection on prime exponents used to compare the square
of the divisor function to the four-fold divisor function. -/

set_option autoImplicit false

namespace HypothesisS

structure DivisorAllocation where
  common : Nat
  onlyFirst : Nat
  onlySecond : Nat
  unused : Nat

def allocateDivisorExponents (k a b : Nat) : DivisorAllocation :=
  ⟨min a b, a - min a b, b - min a b, k - max a b⟩

theorem divisor_allocation_sums_to_exponent (k a b : Nat)
    (ha : a ≤ k) (hb : b ≤ k) :
    let allocation := allocateDivisorExponents k a b
    allocation.common + allocation.onlyFirst + allocation.onlySecond +
      allocation.unused = k := by
  simp [allocateDivisorExponents]
  omega

theorem divisor_allocation_is_injective (k a b c d : Nat)
    (h : allocateDivisorExponents k a b = allocateDivisorExponents k c d) :
    a = c ∧ b = d := by
  have hFirst := congrArg
    (fun allocation : DivisorAllocation => allocation.common + allocation.onlyFirst) h
  have hSecond := congrArg
    (fun allocation : DivisorAllocation => allocation.common + allocation.onlySecond) h
  simp [allocateDivisorExponents] at hFirst hSecond
  omega

#print axioms divisor_allocation_sums_to_exponent
#print axioms divisor_allocation_is_injective

end HypothesisS
