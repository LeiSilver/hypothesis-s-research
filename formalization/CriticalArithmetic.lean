import Lean

/-!
Integer facts used in the prime-only reduction at the critical product.
The signed row for a fixed smaller input is indexed by two progression
branches, and a lower bound on the admissible prime base gives a
quadratic threshold for proper powers.
-/

set_option autoImplicit false

namespace HypothesisS

private theorem positive_multiple_iff {modulus value : Int}
    (hModulus : 0 < modulus) (hValue : 0 < value) :
    modulus ∣ value ↔ ∃ b : Int, 0 < b ∧ value = b * modulus := by
  constructor
  · rintro ⟨b, hb⟩
    have hPositive : 0 < b := by
      by_cases h : 0 < b
      · exact h
      have hProduct : modulus * b ≤ 0 :=
        Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
      omega
    exact ⟨b, hPositive, by simpa only [Int.mul_comm] using hb⟩
  · rintro ⟨b, _, hb⟩
    exact ⟨b, by simpa only [Int.mul_comm] using hb⟩

/-- The equal-residue branch for the larger coordinate. -/
theorem difference_branch_iff {modulus n m : Int}
    (hModulus : 0 < modulus) (hOrder : n < m) :
    modulus ∣ m - n ↔ ∃ b : Int, 0 < b ∧ m = b * modulus + n := by
  have hMultiple := positive_multiple_iff (modulus := modulus)
    (value := m - n) hModulus (by omega)
  constructor
  · intro h
    obtain ⟨b, hPositive, hb⟩ := hMultiple.mp h
    exact ⟨b, hPositive, by omega⟩
  · rintro ⟨b, hPositive, hb⟩
    exact hMultiple.mpr ⟨b, hPositive, by omega⟩

/-- The opposite-residue branch for the larger coordinate. -/
theorem reflection_branch_iff {modulus n m : Int}
    (hModulus : 0 < modulus) (hn : 0 < n) (hm : 0 < m) :
    modulus ∣ m + n ↔ ∃ b : Int, 0 < b ∧ m = b * modulus - n := by
  have hMultiple := positive_multiple_iff (modulus := modulus)
    (value := m + n) hModulus (by omega)
  constructor
  · intro h
    obtain ⟨b, hPositive, hb⟩ := hMultiple.mp h
    exact ⟨b, hPositive, by omega⟩
  · rintro ⟨b, hPositive, hb⟩
    exact hMultiple.mpr ⟨b, hPositive, by omega⟩

theorem equal_residue_branch_iff {modulus n m : Int}
    (hModulus : 0 < modulus) (hOrder : n < m) :
    m % modulus = n % modulus ↔ ∃ b : Int, 0 < b ∧ m = b * modulus + n :=
  Int.emod_eq_emod_iff_emod_sub_eq_zero.trans
    (Int.dvd_iff_emod_eq_zero.symm.trans (difference_branch_iff hModulus hOrder))

theorem opposite_residue_branch_iff {modulus n m : Int}
    (hModulus : 0 < modulus) (hn : 0 < n) (hm : 0 < m) :
    m % modulus = (-n) % modulus ↔ ∃ b : Int, 0 < b ∧ m = b * modulus - n := by
  have hMod := Int.emod_eq_emod_iff_emod_sub_eq_zero (m := m) (n := modulus) (k := -n)
  have hSub : m - -n = m + n := by omega
  rw [hSub] at hMod
  exact hMod.trans
    (Int.dvd_iff_emod_eq_zero.symm.trans (reflection_branch_iff hModulus hn hm))

private theorem no_positive_multiple_below_modulus {modulus value : Int}
    (hModulus : 0 < modulus) (hValue : 0 < value) (hBelow : value < modulus) :
    ¬ modulus ∣ value := by
  intro h
  obtain ⟨b, hb, hProduct⟩ := (positive_multiple_iff hModulus hValue).mp h
  have hLower :=
    Int.mul_le_mul_of_nonneg_right (show (1 : Int) ≤ b by omega)
      (show 0 ≤ modulus by omega)
  simp only [Int.one_mul] at hLower
  omega

/-- For a fixed positive input below half the modulus, the two residues are distinct. -/
theorem signed_row_branches_disjoint {modulus n m : Int}
    (hn : 0 < n) (hSmall : 2 * n < modulus) (hSame : modulus ∣ m - n) :
    ¬ modulus ∣ m + n := by
  intro hOpposite
  obtain ⟨a, ha⟩ := hSame
  obtain ⟨b, hb⟩ := hOpposite
  have hMultiple : modulus ∣ 2 * n := by
    refine ⟨b - a, ?_⟩
    rw [Int.mul_sub]
    omega
  exact no_positive_multiple_below_modulus (by omega) (by omega) hSmall hMultiple

/-- The admissible base cutoff squares at the first proper exponent. -/
theorem proper_power_threshold {base cutoff exponent : Nat}
    (hCutoff : 1 ≤ cutoff) (hBase : cutoff ≤ base) (hExponent : 2 ≤ exponent) :
    cutoff ^ 2 ≤ base ^ exponent := by
  have hMonotoneBase : cutoff ^ 2 ≤ base ^ 2 := Nat.pow_le_pow_left hBase 2
  have hMonotoneExponent : base ^ 2 ≤ base ^ exponent :=
    Nat.pow_le_pow_right (by omega) hExponent
  exact Nat.le_trans hMonotoneBase hMonotoneExponent

theorem reduced_power_threshold {modulus base cutoff exponent : Nat}
    (hBase : 1 < base) (hCutoff : 1 ≤ cutoff) (hExponent : 2 ≤ exponent)
    (hReduced : (base ^ exponent).gcd modulus = 1)
    (hBelow : base < cutoff → base ∣ modulus) :
    cutoff ^ 2 ≤ base ^ exponent := by
  by_cases hLarge : cutoff ≤ base
  · exact proper_power_threshold hCutoff hLarge hExponent
  have hBasePower : base ∣ base ^ exponent := by
    cases exponent with
    | zero => omega
    | succ k => exact ⟨base ^ k, by rw [Nat.pow_succ, Nat.mul_comm]⟩
  have hGcd := Nat.dvd_gcd hBasePower (hBelow (by omega))
  rw [hReduced] at hGcd
  have hAtMostOne := Nat.le_of_dvd (show 0 < (1 : Nat) by decide) hGcd
  omega

#print axioms equal_residue_branch_iff
#print axioms opposite_residue_branch_iff
#print axioms signed_row_branches_disjoint
#print axioms reduced_power_threshold

end HypothesisS
