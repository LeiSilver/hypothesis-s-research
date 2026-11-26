import Lean

/-! The divisibility step that restricts squarefree Type II values
to coprime squarefree factors. -/

set_option autoImplicit false

namespace HypothesisS

def HasNoSquareDivisor (n : Nat) : Prop :=
  ∀ r : Nat, r * r ∣ n → r ≤ 1

theorem square_of_common_divisor_dvd_product {r d m : Nat}
    (hD : r ∣ d) (hM : r ∣ m) : r * r ∣ d * m :=
  Nat.mul_dvd_mul hD hM

theorem factors_of_squarefree_product {d m : Nat}
    (h : HasNoSquareDivisor (d * m)) (hD : 0 < d) :
    HasNoSquareDivisor d ∧ HasNoSquareDivisor m ∧ d.Coprime m := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hR
    exact h r (Nat.dvd_trans hR (Nat.dvd_mul_right d m))
  · intro r hR
    exact h r (Nat.dvd_trans hR (Nat.dvd_mul_left m d))
  · rw [Nat.coprime_iff_gcd_eq_one]
    exact Nat.le_antisymm
      (h _ (square_of_common_divisor_dvd_product
              (Nat.gcd_dvd_left d m) (Nat.gcd_dvd_right d m)))
      (Nat.gcd_pos_of_pos_left m hD)

#print axioms square_of_common_divisor_dvd_product
#print axioms factors_of_squarefree_product

end HypothesisS
