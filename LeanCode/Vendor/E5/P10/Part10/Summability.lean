import LeanCode.Vendor.E5.P10.Part10.Basic
import LeanCode.Vendor.E5.Defs

open MeasureTheory


theorem exp_ratio (c : ℝ) (hc : 0 < c) : 0 ≤ Real.exp (-c) ∧ Real.exp (-c) < 1 := by
  constructor
  · exact le_of_lt (Real.exp_pos (-c))
  · rw [Real.exp_lt_one_iff]
    exact neg_lt_zero.mpr hc


theorem geom_nat (c : ℝ) (hc : 0 < c) :
  Summable (fun n : ℕ => Real.exp (-c * (n : ℝ))) ∧
    (∑' n : ℕ, Real.exp (-c * (n : ℝ))) ≤ 1 / (1 - Real.exp (-c)) := by
  let r : ℝ := Real.exp (-c)
  have hr : 0 ≤ r ∧ r < 1 := exp_ratio c hc
  have hpow : (fun n : ℕ => Real.exp (-c * (n : ℝ))) = fun n : ℕ => r ^ n := by
    funext n
    rw [show -c * (n : ℝ) = (n : ℝ) * (-c) by ring]
    rw [Real.exp_nat_mul]
  constructor
  · rw [hpow]
    exact summable_geometric_of_lt_one hr.1 hr.2
  · rw [hpow]
    rw [tsum_geometric_of_lt_one hr.1 hr.2]
    simp [r, one_div]


theorem exp_int_summable (c : ℝ) (hc : 0 < c) :
  Summable (fun k : ℤ => Real.exp (-c * |(k : ℝ)|)) ∧
    (∑' k : ℤ, Real.exp (-c * |(k : ℝ)|)) ≤
      (1 + Real.exp (-c)) / (1 - Real.exp (-c)) := by
  let r : ℝ := Real.exp (-c)
  let g : ℕ → ℝ := fun n => Real.exp (-c * (n : ℝ))
  let f : ℤ → ℝ := fun k => Real.exp (-c * |(k : ℝ)|)
  let S : ℝ := ∑' n : ℕ, g n
  have hgeom := geom_nat c hc
  have hg_sum : Summable g := hgeom.1
  have hS_bound : S ≤ 1 / (1 - r) := by
    simpa [S, g, r] using hgeom.2
  have hr : 0 ≤ r ∧ r < 1 := exp_ratio c hc
  have hnat_eq : (fun n : ℕ => f (n : ℤ)) = g := by
    funext n
    simp [f, g]
  have hneg_eq : (fun n : ℕ => f (-(↑n + 1))) = fun n : ℕ => r * g n := by
    funext n
    have h_abs : |((-(↑n + 1) : ℤ) : ℝ)| = (n : ℝ) + 1 := by
      have hcast : ((-(↑n + 1) : ℤ) : ℝ) = -((n : ℝ) + 1) := by norm_num
      rw [hcast]
      rw [abs_of_nonpos]
      · ring
      · have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
    change Real.exp (-c * |((-(↑n + 1) : ℤ) : ℝ)|) =
      Real.exp (-c) * Real.exp (-c * (n : ℝ))
    rw [h_abs]
    rw [show -c * ((n : ℝ) + 1) = -c + (-c * (n : ℝ)) by ring]
    rw [Real.exp_add]
  have hf_nat : Summable (fun n : ℕ => f (n : ℤ)) := by
    rw [hnat_eq]
    exact hg_sum
  have hf_neg : Summable (fun n : ℕ => f (-(↑n + 1))) := by
    rw [hneg_eq]
    exact hg_sum.mul_left r
  have hf_sum : Summable f := Summable.of_nat_of_neg_add_one hf_nat hf_neg
  constructor
  · simpa [f] using hf_sum
  · have hnat_has : HasSum (fun n : ℕ => f (n : ℤ)) S := by
      rw [hnat_eq]
      exact hg_sum.hasSum
    have hneg_has : HasSum (fun n : ℕ => f (-(↑n + 1))) (r * S) := by
      rw [hneg_eq]
      exact hg_sum.hasSum.mul_left r
    have htotal : HasSum f (S + r * S) := HasSum.of_nat_of_neg_add_one hnat_has hneg_has
    have htsum : (∑' k : ℤ, f k) = S + r * S := htotal.tsum_eq
    rw [show (∑' k : ℤ, Real.exp (-c * |(k : ℝ)|)) = ∑' k : ℤ, f k by rfl]
    rw [htsum]
    have hone : 0 ≤ 1 + r := by nlinarith [hr.1]
    have hmul := mul_le_mul_of_nonneg_left hS_bound hone
    have hleft : (1 + r) * S = S + r * S := by ring
    have hright : (1 + r) * (1 / (1 - r)) = (1 + r) / (1 - r) := by ring
    nlinarith [hmul]


theorem rev_triangle (x y : ℝ) : |y| - |x| ≤ |x + y| := by
  have h : |y| ≤ |x + y| + |x| := by
    calc
      |y| = |(x + y) + (-x)| := by ring_nf
      _ ≤ |x + y| + |-x| := abs_add_le (x + y) (-x)
      _ = |x + y| + |x| := by rw [abs_neg]
  linarith


theorem parity_split {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (a : ℤ → E) (ha : Summable a) :
    Summable (fun m : ℤ => a (2 * m)) ∧
      Summable (fun m : ℤ => a (2 * m + 1)) ∧
      (∑' k : ℤ, a k) =
        (∑' m : ℤ, a (2 * m)) + (∑' m : ℤ, a (2 * m + 1)) := by
  let s : Set ℤ := {k | Even k}
  let eEven : ℤ ≃ s :=
    Equiv.ofBijective
      (fun m : ℤ => (⟨2 * m, by
        change Even (2 * m)
        exact even_two_mul m⟩ : s))
      (by
        constructor
        · intro m n hmn
          have hval : 2 * m = 2 * n := congr_arg Subtype.val hmn
          omega
        · intro y
          have hy_mem : (y : ℤ) ∈ s := y.property
          have hy : Even (y : ℤ) := by
            change Even (y : ℤ) at hy_mem
            exact hy_mem
          rcases (even_iff_exists_two_mul.mp hy) with ⟨m, hm⟩
          refine ⟨m, Subtype.ext ?_⟩
          simp [hm])
  let eOdd : ℤ ≃ ↥(sᶜ) :=
    Equiv.ofBijective
      (fun m : ℤ => (⟨2 * m + 1, by
        have hodd : Odd (2 * m + 1 : ℤ) := ⟨m, by ring⟩
        exact (Int.not_even_iff_odd.mpr hodd)
        ⟩ : ↥(sᶜ)))
      (by
        constructor
        · intro m n hmn
          have hval : 2 * m + 1 = 2 * n + 1 := congr_arg Subtype.val hmn
          omega
        · intro y
          have hy_mem : (y : ℤ) ∈ sᶜ := y.property
          have hy_not : ¬ Even (y : ℤ) := by
            change ¬ Even (y : ℤ) at hy_mem
            exact hy_mem
          have hy_odd : Odd (y : ℤ) := Int.not_even_iff_odd.mp hy_not
          rcases (odd_iff_exists_bit1.mp hy_odd) with ⟨m, hm⟩
          refine ⟨m, Subtype.ext ?_⟩
          simp [hm])
  have hEvenSub : Summable (fun x : s => a x) := by
    exact ha.subtype (fun k : ℤ => k ∈ s)
  have hOddSub : Summable (fun x : ↥(sᶜ) => a x) := by
    exact ha.subtype (fun k : ℤ => k ∈ sᶜ)
  have hEvenAux : Summable ((fun x : s => a x) ∘ eEven) :=
    (eEven.summable_iff (f := fun x : s => a x)).mpr hEvenSub
  have hEven : Summable (fun m : ℤ => a (2 * m)) := by
    convert hEvenAux using 1
    ext m
    rfl
  have hOddAux : Summable ((fun x : ↥(sᶜ) => a x) ∘ eOdd) :=
    (eOdd.summable_iff (f := fun x : ↥(sᶜ) => a x)).mpr hOddSub
  have hOdd : Summable (fun m : ℤ => a (2 * m + 1)) := by
    convert hOddAux using 1
    ext m
    rfl
  refine ⟨hEven, hOdd, ?_⟩
  have hsplit := ha.tsum_subtype_add_tsum_subtype_compl s
  have hEvenTsumAux := eEven.tsum_eq (fun x : s => a x)
  have hEvenTsum : (∑' m : ℤ, a (2 * m)) = ∑' x : s, a x := by
    simpa [eEven] using hEvenTsumAux
  have hOddTsumAux := eOdd.tsum_eq (fun x : ↥(sᶜ) => a x)
  have hOddTsum : (∑' m : ℤ, a (2 * m + 1)) = ∑' x : ↥(sᶜ), a x := by
    simpa [eOdd] using hOddTsumAux
  rw [hEvenTsum, hOddTsum]
  exact hsplit.symm


theorem sign (k n : ℤ) :
  (-1 : ℝ) ^ (k + 1) = -((-1 : ℝ) ^ k) ∧
    (-1 : ℝ) ^ (-k) = (-1 : ℝ) ^ k ∧
    (-1 : ℝ) ^ (k + n) = (-1 : ℝ) ^ k * (-1 : ℝ) ^ n ∧
    (-1 : ℝ) ^ (2 * n) = 1 ∧
    (-1 : ℝ) ^ (2 * n + 1) = -1 := by
  have hne : (-1 : ℝ) ≠ 0 := by norm_num
  constructor
  · rw [zpow_add_one₀ hne]
    ring
  constructor
  · rw [neg_one_zpow_eq_ite, neg_one_zpow_eq_ite]
    simp [even_neg]
  constructor
  · exact zpow_add₀ hne k n
  constructor
  · rw [neg_one_zpow_eq_ite]
    have h_even : Even (2 * n) := by
      use n
      ring
    simp [h_even]
  · rw [neg_one_zpow_eq_ite]
    have h_not_even : ¬ Even (2 * n + 1) := by
      intro h
      rcases h with ⟨m, hm⟩
      have : (2 : ℤ) ∣ 1 := by
        use m - n
        linarith
      norm_num at this
    simp [h_not_even]
