import Lean

/-! Reduction of the denominator of the sampled frequency bN/q. -/

set_option autoImplicit false

namespace HypothesisS

theorem slope_reduced_denominator (q n b : Nat) (hq : 0 < q) :
    q / Nat.gcd q (b * n) =
      (q / Nat.gcd q n) / Nat.gcd (q / Nat.gcd q n) b := by
  let d := Nat.gcd q n
  let r := q / d
  let m := n / d
  let e := Nat.gcd r b
  let k := r / e
  have hd : 0 < d := Nat.gcd_pos_of_pos_left n hq
  have hdq : d ∣ q := Nat.gcd_dvd_left q n
  have hdn : d ∣ n := Nat.gcd_dvd_right q n
  have hr : 0 < r := Nat.div_pos (Nat.le_of_dvd hq hdq) hd
  have he : 0 < e := Nat.gcd_pos_of_pos_left b hr
  have hnSplit : n = d * m := by
    rw [Nat.mul_comm]
    exact (Nat.div_mul_cancel hdn).symm
  have hqSplit : q = d * r := by
    rw [Nat.mul_comm]
    exact (Nat.div_mul_cancel hdq).symm
  have hReduced : Nat.Coprime m r := by
    change Nat.gcd (n / d) (q / d) = 1
    rw [Nat.gcd_div hdn hdq, Nat.gcd_comm n q]
    exact Nat.div_self hd
  have hGcd : Nat.gcd q (b * n) = d * e := by
    calc
      Nat.gcd q (b * n) = Nat.gcd (d * r) (b * n) :=
        congrArg (fun v => Nat.gcd v (b * n)) hqSplit
      _ = Nat.gcd (d * r) (b * (d * m)) :=
        congrArg (fun v => Nat.gcd (d * r) (b * v)) hnSplit
      _ = Nat.gcd (d * r) (d * (b * m)) :=
        congrArg (Nat.gcd (d * r)) (by ac_rfl)
      _ = d * Nat.gcd r (b * m) := Nat.gcd_mul_left d r (b * m)
      _ = d * e := by
        rw [Nat.gcd_comm r (b * m), hReduced.gcd_mul_right_cancel b, Nat.gcd_comm b r]
  have hProduct : q = k * (d * e) := by
    have hrSplit : k * e = r := Nat.div_mul_cancel (Nat.gcd_dvd_left r b)
    calc
      q = d * r := hqSplit
      _ = d * (k * e) := by rw [hrSplit]
      _ = k * (d * e) := by ac_rfl
  change q / Nat.gcd q (b * n) = k
  rw [hGcd, hProduct]
  exact Nat.mul_div_cancel k (Nat.mul_pos hd he)

theorem modulus_dvd_reduced_cofactor_product (q n : Nat) :
    q ∣ (q / Nat.gcd q n) * n := by
  let d := Nat.gcd q n
  obtain ⟨m, hm⟩ := Nat.gcd_dvd_right q n
  have hq : q / d * d = q := Nat.div_mul_cancel (Nat.gcd_dvd_left q n)
  change q ∣ (q / d) * n
  refine ⟨m, ?_⟩
  calc
    (q / d) * n = ((q / d) * d) * m := by
      change n = d * m at hm
      rw [hm, Nat.mul_assoc]
    _ = q * m := by rw [hq]

#print axioms slope_reduced_denominator
#print axioms modulus_dvd_reduced_cofactor_product

end HypothesisS
