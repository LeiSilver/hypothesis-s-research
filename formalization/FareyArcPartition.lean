import Lean

/-! Integer arithmetic for the least-denominator assignment of overlapping arcs. -/

set_option autoImplicit false

namespace HypothesisS

theorem overlapping_arcs_determinant_one (K q r det : Int)
    (hK : 0 < K) (hq : q ≤ K) (hr : r ≤ K) (hDet : 0 < det)
    (hOverlap : K * det < q + r) :
    det = 1 := by
  by_cases hOne : det = 1
  · exact hOne
  · have hTwo : 2 ≤ det := by omega
    have hDouble : K * 2 ≤ K * det :=
      Int.mul_le_mul_of_nonneg_left hTwo (Int.le_of_lt hK)
    omega

theorem farey_intermediate_denominator (a q b r m n : Int)
    (hq : 0 < q) (hr : 0 < r) (hDet : b * q - a * r = 1)
    (hLeft : 0 < m * q - a * n) (hRight : 0 < b * n - m * r) :
    q + r ≤ n := by
  have hIdentity : r * (m * q - a * n) + q * (b * n - m * r) = n := by
    calc
      r * (m * q - a * n) + q * (b * n - m * r) =
          (b * q - a * r) * n := by
        simp only [Int.mul_sub, Int.sub_mul]
        have hCancel : r * (m * q) = q * (m * r) := by ac_rfl
        have hA : r * (a * n) = a * r * n := by ac_rfl
        have hB : q * (b * n) = b * q * n := by ac_rfl
        rw [hCancel, hA, hB]
        omega
      _ = n := by simp [hDet]
  have hLeftBound : r * 1 ≤ r * (m * q - a * n) :=
    Int.mul_le_mul_of_nonneg_left (by omega) (Int.le_of_lt hr)
  have hRightBound : q * 1 ≤ q * (b * n - m * r) :=
    Int.mul_le_mul_of_nonneg_left (by omega) (Int.le_of_lt hq)
  simp only [Int.mul_one] at hLeftBound hRightBound
  omega

theorem farey_successor_residue (a q b r : Int)
    (hDet : b * q - a * r = 1) :
    q ∣ a * r + 1 := by
  refine ⟨b, ?_⟩
  rw [Int.mul_comm q b]
  omega

theorem farey_predecessor_residue (a q b r : Int)
    (hDet : a * r - b * q = 1) :
    q ∣ a * r - 1 := by
  refine ⟨b, ?_⟩
  rw [Int.mul_comm q b]
  omega

#print axioms overlapping_arcs_determinant_one
#print axioms farey_intermediate_denominator
#print axioms farey_successor_residue
#print axioms farey_predecessor_residue

end HypothesisS
