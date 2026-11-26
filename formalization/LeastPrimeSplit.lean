import Lean

/-! The divisor split after extracting one prime and the log multiplicity of unordered pairs. -/

set_option autoImplicit false

namespace HypothesisS

theorem divisor_split_at_prime (p t d : Nat)
    (hPrimeDivisors : ∀ v : Nat, v ∣ p → v = 1 ∨ v = p) :
    d ∣ p * t ↔ d ∣ t ∨ ∃ e : Nat, e ∣ t ∧ d = p * e := by
  constructor
  · intro h
    obtain ⟨u, e, hu, he, hProduct⟩ := Nat.dvd_mul.mp h
    rcases hPrimeDivisors u hu with hOne | hPrime
    · left
      rw [hOne, Nat.one_mul] at hProduct
      rwa [← hProduct]
    · right
      exact ⟨e, he, by simpa [hPrime] using hProduct.symm⟩
  · rintro (h | ⟨e, he, hProduct⟩)
    · exact Nat.dvd_trans h (Nat.dvd_mul_left t p)
    · exact Nat.dvd_mul.mpr ⟨p, e, Nat.dvd_refl p, he, hProduct.symm⟩

theorem divisor_split_branches_disjoint (p t d e : Nat)
    (hCoprime : ¬ p ∣ t) (h : d ∣ t) :
    d ≠ p * e := by
  intro hProduct
  exact hCoprime (Nat.dvd_trans (by rw [hProduct]; exact Nat.dvd_mul_right p e) h)

noncomputable def pairLogSum : List Int → Int
  | [] => 0
  | x :: xs => (xs.map (fun y => x + y)).sum + pairLogSum xs

private theorem sum_constant_add (x : Int) (xs : List Int) :
    (xs.map (fun y => x + y)).sum = (xs.length : Int) * x + xs.sum := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Int.natCast_add,
      Int.natCast_one]
    rw [ih, Int.add_mul, Int.one_mul]
    omega

theorem pair_log_sum (xs : List Int) :
    pairLogSum xs = ((xs.length : Int) - 1) * xs.sum := by
  induction xs with
  | nil => simp [pairLogSum]
  | cons x xs ih =>
    simp only [pairLogSum, List.length_cons, Int.natCast_add, List.sum_cons]
    rw [sum_constant_add, ih]
    simp only [Int.mul_add, Int.sub_mul, Int.add_mul, Int.one_mul]
    omega

theorem six_factor_log_weight (xs : List Int) (hLength : xs.length = 6) :
    -xs.sum + pairLogSum xs = 4 * xs.sum := by
  rw [pair_log_sum, hLength]
  omega

#print axioms divisor_split_at_prime
#print axioms divisor_split_branches_disjoint
#print axioms six_factor_log_weight

end HypothesisS
