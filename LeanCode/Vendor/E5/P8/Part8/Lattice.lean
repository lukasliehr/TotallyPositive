import LeanCode.Vendor.E5.P8.Part8.Defs
import LeanCode.Vendor.E5.Defs
open VendorE5

open MeasureTheory
open scoped BigOperators

namespace Part8

noncomputable section


theorem g_nonneg (g : ℝ → ℝ) (hg : IsTotallyPositive g) :
  ∀ t : ℝ, 0 ≤ g t := by
  intro t
  have ha : StrictMono (fun _ : Fin 1 => t) := by
    intro i j hij
    fin_cases i
    fin_cases j
    simp at hij
  have hb : StrictMono (fun _ : Fin 1 => (0 : ℝ)) := by
    intro i j hij
    fin_cases i
    fin_cases j
    simp at hij
  have h := hg 1 (fun _ : Fin 1 => t) (fun _ : Fin 1 => (0 : ℝ)) ha hb
  simpa using h


theorem geom_Z (c : ℝ) (hc : 0 < c) :
  Summable (fun k : ℤ => Real.exp (-c * |(k : ℝ)|)) ∧
    (∑' k : ℤ, Real.exp (-c * |(k : ℝ)|)) ≤ geomBound c := by
  let r : ℝ := Real.exp (-c)
  have hr_nonneg : 0 ≤ r := (Real.exp_pos _).le
  have hr_lt_one : r < 1 := by
    dsimp [r]
    rw [Real.exp_lt_one_iff]
    linarith
  have hden_ne : 1 - r ≠ 0 := by
    linarith
  have hs_geom : Summable (fun n : ℕ => r ^ n) :=
    summable_geometric_of_lt_one hr_nonneg hr_lt_one
  have hpos_eq (n : ℕ) :
      Real.exp (-c * |(((n : ℕ) : ℤ) : ℝ)|) = r ^ n := by
    have harg : -c * |(((n : ℕ) : ℤ) : ℝ)| = (n : ℝ) * (-c) := by
      simp [abs_of_nonneg]
      ring
    rw [harg, Real.exp_nat_mul]
  have hneg_eq (n : ℕ) :
      Real.exp (-c * |((-(↑n + 1) : ℤ) : ℝ)|) = r ^ (n + 1) := by
    have habs : |((-(↑n + 1) : ℤ) : ℝ)| = (n : ℝ) + 1 := by
      rw [abs_of_nonpos]
      · norm_num
      · norm_num
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
    have harg : -c * |((-(↑n + 1) : ℤ) : ℝ)| = ((n + 1 : ℕ) : ℝ) * (-c) := by
      rw [habs]
      norm_num
      ring
    rw [harg, Real.exp_nat_mul]
  have hpos_sum : Summable (fun n : ℕ => Real.exp (-c * |(((n : ℕ) : ℤ) : ℝ)|)) :=
    hs_geom.congr (fun n => (hpos_eq n).symm)
  have hs_succ : Summable (fun n : ℕ => r ^ (n + 1)) := by
    have hmul : Summable (fun n : ℕ => r * r ^ n) := hs_geom.mul_left r
    refine hmul.congr ?_
    intro n
    rw [pow_succ']
  have hneg_sum : Summable (fun n : ℕ => Real.exp (-c * |((-(↑n + 1) : ℤ) : ℝ)|)) :=
    hs_succ.congr (fun n => (hneg_eq n).symm)
  constructor
  · exact Summable.of_nat_of_neg_add_one
      (f := fun k : ℤ => Real.exp (-c * |(k : ℝ)|)) hpos_sum hneg_sum
  · have hsplit := tsum_of_nat_of_neg_add_one
      (f := fun k : ℤ => Real.exp (-c * |(k : ℝ)|)) hpos_sum hneg_sum
    have hpos_tsum :
        (∑' n : ℕ, Real.exp (-c * |(((n : ℕ) : ℤ) : ℝ)|)) = (1 - r)⁻¹ := by
      calc
        (∑' n : ℕ, Real.exp (-c * |(((n : ℕ) : ℤ) : ℝ)|)) = ∑' n : ℕ, r ^ n := by
          apply tsum_congr
          intro n
          exact hpos_eq n
        _ = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr_nonneg hr_lt_one
    have hneg_tsum :
        (∑' n : ℕ, Real.exp (-c * |((-(↑n + 1) : ℤ) : ℝ)|)) = r * (1 - r)⁻¹ := by
      calc
        (∑' n : ℕ, Real.exp (-c * |((-(↑n + 1) : ℤ) : ℝ)|)) = ∑' n : ℕ, r ^ (n + 1) := by
          apply tsum_congr
          intro n
          exact hneg_eq n
        _ = ∑' n : ℕ, r * r ^ n := by
          apply tsum_congr
          intro n
          rw [pow_succ']
        _ = r * (1 - r)⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one hr_nonneg hr_lt_one]
    have hsum : (∑' k : ℤ, Real.exp (-c * |(k : ℝ)|)) = geomBound c := by
      rw [hsplit, hpos_tsum, hneg_tsum]
      dsimp [geomBound, r]
      field_simp [hden_ne]
    rw [hsum]


theorem rev_triangle (x y : ℝ) : |y| - |x| ≤ |x + y| := by
  have h : |y| ≤ |x + y| + |x| := by
    simpa [add_assoc, add_comm, add_left_comm] using abs_add_le (x + y) (-x)
  linarith


theorem shifted_sum (c w : ℝ) (hc : 0 < c) :
  Summable (fun k : ℤ => Real.exp (-c * |w + k|)) ∧
    (∑' k : ℤ, Real.exp (-c * |w + k|)) ≤ Real.exp c * geomBound c ∧
    ∀ F : Finset ℤ,
      (∑ k ∈ F, Real.exp (-c * |w + k|)) ≤ Real.exp c * geomBound c := by
  let m : ℤ := Int.floor w
  let θ : ℝ := w - (m : ℝ)
  have hfloor : (m : ℝ) ≤ w := by
    dsimp [m]
    exact Int.floor_le w
  have hfloor_lt : w < (m : ℝ) + 1 := by
    dsimp [m]
    exact Int.lt_floor_add_one w
  have hθ_nonneg : 0 ≤ θ := by
    change 0 ≤ w - (m : ℝ)
    linarith
  have hθ_le_one : θ ≤ 1 := by
    change w - (m : ℝ) ≤ 1
    linarith
  have hθ_abs : |θ| ≤ 1 := by
    rw [abs_of_nonneg hθ_nonneg]
    exact hθ_le_one
  have hgeom := geom_Z c hc
  let base : ℤ → ℝ := fun j => Real.exp (-c * |(j : ℝ)|)
  let major : ℤ → ℝ := fun k => Real.exp c * base (k + m)
  have hshift_sum : Summable (fun k : ℤ => base (k + m)) := by
    have hinj : Function.Injective (fun k : ℤ => k + m) := by
      intro a b h
      exact add_right_cancel h
    exact hgeom.1.comp_injective hinj
  have hmajor_sum : Summable major := by
    dsimp [major]
    exact hshift_sum.mul_left (Real.exp c)
  have hle : ∀ k : ℤ, Real.exp (-c * |w + k|) ≤ major k := by
    intro k
    have hwk : θ + (((k + m : ℤ) : ℝ)) = w + (k : ℝ) := by
      change (w - (m : ℝ)) + (((k + m : ℤ) : ℝ)) = w + (k : ℝ)
      norm_num
    have htri := rev_triangle θ (((k + m : ℤ) : ℝ))
    rw [hwk] at htri
    have hlower : |(((k + m : ℤ) : ℝ))| - 1 ≤ |w + (k : ℝ)| := by
      linarith
    have harg : -c * |w + (k : ℝ)| ≤ c + (-c * |(((k + m : ℤ) : ℝ))|) := by
      have hmul := mul_le_mul_of_nonpos_left hlower (by linarith : -c ≤ 0)
      nlinarith
    dsimp [major, base]
    calc
      Real.exp (-c * |w + (k : ℝ)|) ≤ Real.exp (c + (-c * |(((k + m : ℤ) : ℝ))|)) :=
        Real.exp_le_exp.mpr harg
      _ = Real.exp c * Real.exp (-c * |(((k + m : ℤ) : ℝ))|) := by
        rw [Real.exp_add]
  have htarget_sum : Summable (fun k : ℤ => Real.exp (-c * |w + k|)) := by
    exact Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le) hle hmajor_sum
  have hshift_tsum : (∑' k : ℤ, base (k + m)) = ∑' j : ℤ, base j := by
    calc
      (∑' k : ℤ, base (k + m)) = ∑' k : ℤ, base ((Equiv.addRight m) k) := by
        apply tsum_congr
        intro k
        simp [Equiv.addRight]
      _ = ∑' j : ℤ, base j := Equiv.tsum_eq (Equiv.addRight m) base
  have hmajor_bound : (∑' k : ℤ, major k) ≤ Real.exp c * geomBound c := by
    dsimp [major]
    rw [tsum_mul_left, hshift_tsum]
    exact mul_le_mul_of_nonneg_left hgeom.2 (Real.exp_pos c).le
  have htarget_bound : (∑' k : ℤ, Real.exp (-c * |w + k|)) ≤ Real.exp c * geomBound c := by
    exact (htarget_sum.tsum_le_tsum hle hmajor_sum).trans hmajor_bound
  exact ⟨htarget_sum, htarget_bound, fun F => by
    exact (htarget_sum.sum_le_tsum F (fun k hk => (Real.exp_pos _).le)).trans htarget_bound⟩


theorem envelope (f : ℝ → ℝ) (C c R : ℝ)
    (hC : 0 < C) (hc : 0 < c) (hR : 0 ≤ R)
    (hf : ∀ t : ℝ, |f t| ≤ C * Real.exp (-c * |t|)) :
  ∀ (k : ℤ) (x : ℝ), |x| ≤ R →
    |f (x + k)| ≤ C * Real.exp (c * R) * Real.exp (-c * |(k : ℝ)|) := by
  have _ : 0 ≤ R := hR
  intro k x hx
  have htri : |(k : ℝ)| - |x| ≤ |x + (k : ℝ)| := rev_triangle x (k : ℝ)
  have hlower : |(k : ℝ)| - R ≤ |x + (k : ℝ)| := by
    linarith
  have harg : -c * |x + (k : ℝ)| ≤ c * R + (-c * |(k : ℝ)|) := by
    have hmul := mul_le_mul_of_nonpos_left hlower (by linarith : -c ≤ 0)
    nlinarith
  have hexp : Real.exp (-c * |x + (k : ℝ)|) ≤
      Real.exp (c * R) * Real.exp (-c * |(k : ℝ)|) := by
    calc
      Real.exp (-c * |x + (k : ℝ)|) ≤
          Real.exp (c * R + (-c * |(k : ℝ)|)) := Real.exp_le_exp.mpr harg
      _ = Real.exp (c * R) * Real.exp (-c * |(k : ℝ)|) := by
        rw [Real.exp_add]
  calc
    |f (x + k)| ≤ C * Real.exp (-c * |(x + k : ℝ)|) := hf (x + k)
    _ ≤ C * (Real.exp (c * R) * Real.exp (-c * |(k : ℝ)|)) := by
      exact mul_le_mul_of_nonneg_left hexp (le_of_lt hC)
    _ = C * Real.exp (c * R) * Real.exp (-c * |(k : ℝ)|) := by
      ring


theorem decay_lattice (f : ℝ → ℝ) (C c : ℝ)
    (hC : 0 < C) (hc : 0 < c)
    (hf : ∀ t : ℝ, |f t| ≤ C * Real.exp (-c * |t|)) :
  LatticeDominated f ∧
    LatticeEnvelope f (fun k : ℤ => C * Real.exp c * Real.exp (-c * |(k : ℝ)|)) ∧
    (∑' k : ℤ, C * Real.exp c * Real.exp (-c * |(k : ℝ)|)) ≤
      C * Real.exp c * geomBound c := by
  let b : ℤ → ℝ := fun k => C * Real.exp c * Real.exp (-c * |(k : ℝ)|)
  have hgeom := geom_Z c hc
  have hb_sum : Summable b := by
    dsimp [b]
    simpa [mul_assoc] using hgeom.1.mul_left (C * Real.exp c)
  have hb_bound : ∀ (k : ℤ), ∀ x ∈ Set.Icc (0 : ℝ) 1, |f (x + k)| ≤ b k := by
    intro k x hx
    have hxabs : |x| ≤ (1 : ℝ) := by
      rcases hx with ⟨hx0, hx1⟩
      rw [abs_of_nonneg hx0]
      exact hx1
    have henv := envelope f C c 1 hC hc zero_le_one hf k x hxabs
    dsimp [b]
    simpa [mul_assoc] using henv
  have hlatEnv : LatticeEnvelope f b := ⟨hb_sum, hb_bound⟩
  have hlat : LatticeDominated f := ⟨b, hb_sum, hb_bound⟩
  have hscale_nonneg : 0 ≤ C * Real.exp c := by positivity
  have hsum_bound : (∑' k : ℤ, b k) ≤ C * Real.exp c * geomBound c := by
    dsimp [b]
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hgeom.2 hscale_nonneg
  exact ⟨hlat, hlatEnv, hsum_bound⟩


theorem sum_2Z (g : ℝ → ℝ) (C c x : ℝ)
    (hC : 0 < C) (hc : 0 < c)
    (hg : ∀ t : ℝ, |g t| ≤ C * Real.exp (-c * |t|)) :
  Summable (fun n : ℤ => g (x + 2 * n)) ∧
    Summable (fun n : ℤ => |g (x + 2 * n)|) := by
  let M : ℝ := C * Real.exp (c * |x|)
  have h2c : 0 < 2 * c := by positivity
  have hgeom := geom_Z (2 * c) h2c
  have hmajor_sum : Summable (fun n : ℤ => M * Real.exp (-(2 * c) * |(n : ℝ)|)) :=
    hgeom.1.mul_left M
  have hle : ∀ n : ℤ, |g (x + 2 * n)| ≤ M * Real.exp (-(2 * c) * |(n : ℝ)|) := by
    intro n
    have htri := rev_triangle x (2 * (n : ℝ))
    have htwon : |(2 : ℝ) * (n : ℝ)| = 2 * |(n : ℝ)| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [htwon] at htri
    have harg : -c * |x + 2 * (n : ℝ)| ≤ c * |x| + (-(2 * c) * |(n : ℝ)|) := by
      have hmul := mul_le_mul_of_nonpos_left htri (by linarith : -c ≤ 0)
      nlinarith
    have hexp : Real.exp (-c * |x + 2 * (n : ℝ)|) ≤
        Real.exp (c * |x|) * Real.exp (-(2 * c) * |(n : ℝ)|) := by
      calc
        Real.exp (-c * |x + 2 * (n : ℝ)|) ≤
            Real.exp (c * |x| + (-(2 * c) * |(n : ℝ)|)) := Real.exp_le_exp.mpr harg
        _ = Real.exp (c * |x|) * Real.exp (-(2 * c) * |(n : ℝ)|) := by
          rw [Real.exp_add]
    calc
      |g (x + 2 * (n : ℝ))| ≤ C * Real.exp (-c * |x + 2 * (n : ℝ)|) :=
        hg (x + 2 * (n : ℝ))
      _ ≤ C * (Real.exp (c * |x|) * Real.exp (-(2 * c) * |(n : ℝ)|)) := by
        exact mul_le_mul_of_nonneg_left hexp (le_of_lt hC)
      _ = M * Real.exp (-(2 * c) * |(n : ℝ)|) := by
        dsimp [M]
        ring
  have habs_sum : Summable (fun n : ℤ => |g (x + 2 * n)|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hle hmajor_sum
  have hsigned : Summable (fun n : ℤ => g (x + 2 * n)) := by
    apply Summable.of_norm
    simpa [Real.norm_eq_abs] using habs_sum
  exact ⟨hsigned, habs_sum⟩


def haltPartialSum (f : ℝ → ℝ) (F : Finset ℤ) (x : ℝ) : ℝ :=
  ∑ k ∈ F, (-1 : ℝ) ^ k * f (x + k)


theorem halt_summable (f : ℝ → ℝ) (b : ℤ → ℝ)
    (hb : LatticeEnvelope f b) :
  (∀ x : ℝ, Summable (fun k : ℤ => (-1 : ℝ) ^ k * f (x + k))) ∧
    (∀ x : ℝ, Summable (fun k : ℤ => |((-1 : ℝ) ^ k * f (x + k))|)) ∧
    ∀ x : ℝ, |Halt f x| ≤ ∑' k : ℤ, b k := by
  have hcore : ∀ x : ℝ,
      Summable (fun k : ℤ => |((-1 : ℝ) ^ k * f (x + k))|) ∧
        (∑' k : ℤ, |((-1 : ℝ) ^ k * f (x + k))|) ≤ ∑' k : ℤ, b k := by
    intro x
    let m : ℤ := Int.floor x
    let s : ℝ := x - (m : ℝ)
    have hfloor : (m : ℝ) ≤ x := by
      dsimp [m]
      exact Int.floor_le x
    have hfloor_lt : x < (m : ℝ) + 1 := by
      dsimp [m]
      exact Int.lt_floor_add_one x
    have hs_mem : s ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · change 0 ≤ x - (m : ℝ)
        linarith
      · change x - (m : ℝ) ≤ 1
        linarith
    have hshift_sum : Summable (fun k : ℤ => b (k + m)) := by
      have hinj : Function.Injective (fun k : ℤ => k + m) := by
        intro a b h
        exact add_right_cancel h
      exact hb.1.comp_injective hinj
    have hsign_abs (k : ℤ) : |((-1 : ℝ) ^ k)| = 1 := by
      rw [abs_zpow]
      norm_num
    have hle : ∀ k : ℤ, |((-1 : ℝ) ^ k * f (x + k))| ≤ b (k + m) := by
      intro k
      have hxk : x + (k : ℝ) = s + (((k + m : ℤ) : ℝ)) := by
        change x + (k : ℝ) = (x - (m : ℝ)) + (((k + m : ℤ) : ℝ))
        norm_num
      calc
        |((-1 : ℝ) ^ k * f (x + (k : ℝ)))| = |f (s + (((k + m : ℤ) : ℝ)))| := by
          rw [abs_mul, hsign_abs k, one_mul, hxk]
        _ ≤ b (k + m) := hb.2 (k + m) s hs_mem
    have habs_sum : Summable (fun k : ℤ => |((-1 : ℝ) ^ k * f (x + k))|) :=
      Summable.of_nonneg_of_le (fun k => abs_nonneg _) hle hshift_sum
    have hshift_tsum : (∑' k : ℤ, b (k + m)) = ∑' k : ℤ, b k := by
      calc
        (∑' k : ℤ, b (k + m)) = ∑' k : ℤ, b ((Equiv.addRight m) k) := by
          apply tsum_congr
          intro k
          simp [Equiv.addRight]
        _ = ∑' k : ℤ, b k := Equiv.tsum_eq (Equiv.addRight m) b
    have htsum_le : (∑' k : ℤ, |((-1 : ℝ) ^ k * f (x + k))|) ≤
        ∑' k : ℤ, b (k + m) :=
      habs_sum.tsum_le_tsum hle hshift_sum
    exact ⟨habs_sum, htsum_le.trans_eq hshift_tsum⟩
  constructor
  · intro x
    apply Summable.of_norm
    simpa [Real.norm_eq_abs] using (hcore x).1
  constructor
  · intro x
    exact (hcore x).1
  · intro x
    have habs_sum := (hcore x).1
    have hnorm_sum : Summable (fun k : ℤ => ‖(-1 : ℝ) ^ k * f (x + k)‖) := by
      simpa [Real.norm_eq_abs] using habs_sum
    calc
      |Halt f x| = ‖∑' k : ℤ, (-1 : ℝ) ^ k * f (x + k)‖ := by
        simp [Halt, Real.norm_eq_abs]
      _ ≤ ∑' k : ℤ, ‖(-1 : ℝ) ^ k * f (x + k)‖ := norm_tsum_le_tsum_norm hnorm_sum
      _ = ∑' k : ℤ, |((-1 : ℝ) ^ k * f (x + k))| := by
        apply tsum_congr
        intro k
        rw [Real.norm_eq_abs]
      _ ≤ ∑' k : ℤ, b k := (hcore x).2


theorem sign_succ (k : ℤ) :
  (-1 : ℝ) ^ (k + 1) = -((-1 : ℝ) ^ k) ∧
    (-1 : ℝ) ^ (k - 1) = -((-1 : ℝ) ^ k) := by
  constructor
  · rw [zpow_add_one₀ (by norm_num : (-1 : ℝ) ≠ 0)]
    norm_num
  · rw [zpow_sub_one₀ (by norm_num : (-1 : ℝ) ≠ 0)]
    norm_num


theorem halt_anti (f : ℝ → ℝ) (hf : LatticeDominated f) :
  ∀ x : ℝ, Halt f (x + 1) = -Halt f x := by
  rcases hf with ⟨b, hb⟩
  have hs := halt_summable f b hb
  intro x
  have _hsx := hs.1 x
  have _hsx1 := hs.1 (x + 1)
  unfold Halt
  calc
    (∑' k : ℤ, (-1 : ℝ) ^ k * f (x + 1 + k))
        = ∑' j : ℤ, (-1 : ℝ) ^ ((Equiv.addRight (-1 : ℤ)) j) *
            f (x + 1 + (((Equiv.addRight (-1 : ℤ)) j : ℤ) : ℝ)) := by
          exact (Equiv.tsum_eq (Equiv.addRight (-1 : ℤ))
            (fun k : ℤ => (-1 : ℝ) ^ k * f (x + 1 + k))).symm
    _ = ∑' j : ℤ, -((-1 : ℝ) ^ j * f (x + j)) := by
      apply tsum_congr
      intro j
      have hpow : (-1 : ℝ) ^ (((Equiv.addRight (-1 : ℤ)) j : ℤ)) =
          -((-1 : ℝ) ^ j) := by
        simpa [Equiv.addRight, add_comm, sub_eq_add_neg] using (sign_succ j).2
      have harg : x + 1 + (((Equiv.addRight (-1 : ℤ)) j : ℤ) : ℝ) = x + (j : ℝ) := by
        simp [Equiv.addRight]
        ring
      rw [hpow, harg]
      ring
    _ = -∑' j : ℤ, (-1 : ℝ) ^ j * f (x + j) := by
      rw [tsum_neg]


theorem halt_per2 (f : ℝ → ℝ) (hf : LatticeDominated f) :
  ∀ x : ℝ, Halt f (x + 2) = Halt f x := by
  intro x
  have h1 := halt_anti f hf (x + 1)
  have h0 := halt_anti f hf x
  calc
    Halt f (x + 2) = Halt f ((x + 1) + 1) := by ring_nf
    _ = -Halt f (x + 1) := h1
    _ = -(-Halt f x) := by rw [h0]
    _ = Halt f x := by ring


theorem halt_unif (f : ℝ → ℝ) (b : ℤ → ℝ)
    (hb : LatticeEnvelope f b) (m : ℤ) :
  ∀ ε : ℝ, 0 < ε → ∃ F₀ : Finset ℤ, ∀ F : Finset ℤ,
    F₀ ⊆ F →
      ∀ x ∈ Set.Icc (m : ℝ) ((m : ℝ) + 2),
        |Halt f x - haltPartialSum f F x| ≤ ε := by
  intro ε hε
  let u : ℤ → ℝ := fun k => b (k + m) + b (k + m + 1)
  have hb_nonneg : ∀ j : ℤ, 0 ≤ b j := by
    intro j
    have h := hb.2 j 0 (by constructor <;> norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    exact (abs_nonneg _).trans h
  have hsum₁ : Summable (fun k : ℤ => b (k + m)) := by
    have hinj : Function.Injective (fun k : ℤ => k + m) := by
      intro a c h
      exact add_right_cancel h
    exact hb.1.comp_injective hinj
  have hsum₂ : Summable (fun k : ℤ => b (k + m + 1)) := by
    have hinj : Function.Injective (fun k : ℤ => k + m + 1) := by
      intro a c h
      have h1 : a + m = c + m := add_right_cancel h
      exact add_right_cancel h1
    exact hb.1.comp_injective hinj
  have hu : Summable u := by
    dsimp [u]
    exact hsum₁.add hsum₂
  let term : ℤ → ℝ → ℝ := fun k x => (-1 : ℝ) ^ k * f (x + k)
  have hfu : ∀ k x, x ∈ Set.Icc (m : ℝ) ((m : ℝ) + 2) → ‖term k x‖ ≤ u k := by
    intro k x hx
    let s : ℝ := x - (m : ℝ)
    have hs0 : 0 ≤ s := by
      rcases hx with ⟨hx0, hx2⟩
      change 0 ≤ x - (m : ℝ)
      linarith
    have hs2 : s ≤ 2 := by
      rcases hx with ⟨hx0, hx2⟩
      change x - (m : ℝ) ≤ 2
      linarith
    by_cases hs1 : s ≤ 1
    · have hs_mem : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs0, hs1⟩
      have harg : x + (k : ℝ) = s + (((k + m : ℤ) : ℝ)) := by
        change x + (k : ℝ) = (x - (m : ℝ)) + (((k + m : ℤ) : ℝ))
        norm_num
      calc
        ‖term k x‖ = |f (x + (k : ℝ))| := by
          dsimp [term]
          rw [abs_mul, abs_zpow]
          norm_num
        _ = |f (s + (((k + m : ℤ) : ℝ)))| := by rw [harg]
        _ ≤ b (k + m) := hb.2 (k + m) s hs_mem
        _ ≤ u k := by
          dsimp [u]
          exact le_add_of_nonneg_right (hb_nonneg (k + m + 1))
    · have hs1' : 1 ≤ s := le_of_not_ge hs1
      have hsminus_mem : s - 1 ∈ Set.Icc (0 : ℝ) 1 := by
        constructor <;> linarith
      have harg : x + (k : ℝ) = (s - 1) + (((k + m + 1 : ℤ) : ℝ)) := by
        change x + (k : ℝ) = ((x - (m : ℝ)) - 1) + (((k + m + 1 : ℤ) : ℝ))
        norm_num
      calc
        ‖term k x‖ = |f (x + (k : ℝ))| := by
          dsimp [term]
          rw [abs_mul, abs_zpow]
          norm_num
        _ = |f ((s - 1) + (((k + m + 1 : ℤ) : ℝ)))| := by rw [harg]
        _ ≤ b (k + m + 1) := hb.2 (k + m + 1) (s - 1) hsminus_mem
        _ ≤ u k := by
          dsimp [u]
          exact le_add_of_nonneg_left (hb_nonneg (k + m))
  have hT := tendstoUniformlyOn_tsum (f := term) (u := u) hu
    (s := Set.Icc (m : ℝ) ((m : ℝ) + 2)) hfu
  rw [Metric.tendstoUniformlyOn_iff] at hT
  have hEv := hT ε hε
  rw [Filter.eventually_atTop] at hEv
  rcases hEv with ⟨F₀, hF₀⟩
  refine ⟨F₀, ?_⟩
  intro F hsub x hx
  have hdist := hF₀ F hsub x hx
  have hle := le_of_lt hdist
  simpa [term, Halt, haltPartialSum, Real.dist_eq, dist_eq_norm, Real.norm_eq_abs] using hle


theorem halt_cont (f : ℝ → ℝ) (hcont : Continuous f) (hlat : LatticeDominated f) :
  Continuous (Halt f) := by
  rw [continuous_iff_continuousAt]
  intro x0
  rw [Metric.continuousAt_iff]
  intro ε hε
  rcases hlat with ⟨b, hb⟩
  let m : ℤ := Int.floor (x0 - 1 / 2)
  have hm_le : (m : ℝ) ≤ x0 - 1 / 2 := by
    dsimp [m]
    exact Int.floor_le (x0 - 1 / 2)
  have hm_gt : x0 - 1 / 2 < (m : ℝ) + 1 := by
    dsimp [m]
    exact Int.lt_floor_add_one (x0 - 1 / 2)
  have hm_lt_x0 : (m : ℝ) < x0 := by linarith
  have hx0_lt_m2 : x0 < (m : ℝ) + 2 := by linarith
  have hx0_mem : x0 ∈ Set.Icc (m : ℝ) ((m : ℝ) + 2) :=
    ⟨le_of_lt hm_lt_x0, le_of_lt hx0_lt_m2⟩
  have hthird_pos : 0 < ε / 3 := by positivity
  rcases halt_unif f b hb m (ε / 3) hthird_pos with ⟨F, hF⟩
  have hScont : Continuous (haltPartialSum f F) := by
    unfold haltPartialSum
    apply continuous_finsetSum
    intro k hk
    fun_prop
  rcases (Metric.continuousAt_iff.mp hScont.continuousAt) (ε / 3) hthird_pos with
    ⟨δ0, hδ0_pos, hδ0⟩
  let δ : ℝ := min δ0 (1 / 2)
  have hδ_pos : 0 < δ := by
    exact lt_min hδ0_pos (by norm_num)
  refine ⟨δ, hδ_pos, ?_⟩
  intro x hx_dist
  have hδ_le_δ0 : δ ≤ δ0 := min_le_left _ _
  have hδ_le_half : δ ≤ 1 / 2 := min_le_right _ _
  have hx_dist_δ0 : dist x x0 < δ0 := lt_of_lt_of_le hx_dist hδ_le_δ0
  have hx_abs_half : |x - x0| < 1 / 2 := by
    have hx_abs_delta : |x - x0| < δ := by
      simpa [Real.dist_eq] using hx_dist
    exact lt_of_lt_of_le hx_abs_delta hδ_le_half
  have hx_abs_bounds := abs_lt.mp hx_abs_half
  have hx_lower : x0 - 1 / 2 < x := by linarith
  have hx_upper : x < x0 + 1 / 2 := by linarith
  have hx_mem : x ∈ Set.Icc (m : ℝ) ((m : ℝ) + 2) := by
    constructor <;> linarith
  have htail_x : |Halt f x - haltPartialSum f F x| ≤ ε / 3 :=
    hF F (by intro k hk; exact hk) x hx_mem
  have htail_x0 : |Halt f x0 - haltPartialSum f F x0| ≤ ε / 3 :=
    hF F (by intro k hk; exact hk) x0 hx0_mem
  have htail_x0' : |haltPartialSum f F x0 - Halt f x0| ≤ ε / 3 := by
    simpa [abs_sub_comm] using htail_x0
  have hmiddle_dist := hδ0 hx_dist_δ0
  have hmiddle : |haltPartialSum f F x - haltPartialSum f F x0| < ε / 3 := by
    simpa [Real.dist_eq] using hmiddle_dist
  have htri : |Halt f x - Halt f x0| ≤
      |Halt f x - haltPartialSum f F x| +
        |haltPartialSum f F x - haltPartialSum f F x0| +
        |haltPartialSum f F x0 - Halt f x0| := by
    have hdecomp : Halt f x - Halt f x0 =
        (Halt f x - haltPartialSum f F x) +
          (haltPartialSum f F x - haltPartialSum f F x0) +
          (haltPartialSum f F x0 - Halt f x0) := by ring
    rw [hdecomp]
    have h1 := abs_add_le (Halt f x - haltPartialSum f F x)
      (haltPartialSum f F x - haltPartialSum f F x0)
    have h2 := abs_add_le
      ((Halt f x - haltPartialSum f F x) +
        (haltPartialSum f F x - haltPartialSum f F x0))
      (haltPartialSum f F x0 - Halt f x0)
    linarith
  rw [Real.dist_eq]
  exact lt_of_le_of_lt htri (by linarith)


theorem per2_unifcont (u : ℝ → ℝ) (hcont : Continuous u)
    (hper : ∀ x : ℝ, u (x + 2) = u x) :
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ x y : ℝ, |x - y| ≤ δ → |u x - u y| ≤ ε := by
  intro ε hε
  have hUC : UniformContinuousOn u (Set.Icc (-1 : ℝ) 3) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hcont.continuousOn
  rcases (Metric.uniformContinuousOn_iff.mp hUC) ε hε with ⟨δ₁, hδ₁pos, hδ₁⟩
  let δ : ℝ := min (δ₁ / 2) (1 / 2)
  have hδpos : 0 < δ := by
    exact lt_min (div_pos hδ₁pos (by norm_num)) (by norm_num)
  refine ⟨δ, hδpos, ?_⟩
  intro x y hxy
  let n : ℤ := ⌊x / 2⌋
  let x' : ℝ := x - (n : ℝ) * 2
  let y' : ℝ := y - (n : ℝ) * 2
  have hp : Function.Periodic u (2 : ℝ) := hper
  have hxper : u x = u x' := by
    dsimp [x']
    simpa using (hp.sub_int_mul_eq (x := x) n).symm
  have hyper : u y = u y' := by
    dsimp [y']
    simpa using (hp.sub_int_mul_eq (x := y) n).symm
  have hnle : (n : ℝ) ≤ x / 2 := by
    dsimp [n]
    exact Int.floor_le (x / 2)
  have hxlt : x / 2 < (n : ℝ) + 1 := by
    dsimp [n]
    exact Int.lt_floor_add_one (x / 2)
  have hx'nonneg : 0 ≤ x' := by
    dsimp [x']
    nlinarith
  have hx'lt_two : x' < 2 := by
    dsimp [x']
    nlinarith
  have hδ_le_half : δ ≤ 1 / 2 := by
    exact min_le_right _ _
  have hδ_le_halfδ₁ : δ ≤ δ₁ / 2 := by
    exact min_le_left _ _
  have hδ_lt_δ₁ : δ < δ₁ := by
    have hhalf_lt : δ₁ / 2 < δ₁ := by nlinarith
    exact lt_of_le_of_lt hδ_le_halfδ₁ hhalf_lt
  have hxy' : |y - x| ≤ δ := by
    simpa [abs_sub_comm] using hxy
  have hyx_le : y - x ≤ δ := by
    exact (le_abs_self (y - x)).trans hxy'
  have hneg_le_yx : -δ ≤ y - x := by
    have hneg : -|y - x| ≤ y - x := neg_abs_le (y - x)
    linarith
  have hxmem : x' ∈ Set.Icc (-1 : ℝ) 3 := by
    exact ⟨by linarith, by linarith [le_of_lt hx'lt_two]⟩
  have hymem : y' ∈ Set.Icc (-1 : ℝ) 3 := by
    dsimp [y', x'] at *
    constructor <;> nlinarith
  have hdist_le : dist x' y' ≤ δ := by
    rw [Real.dist_eq]
    have hdiff : x' - y' = x - y := by
      dsimp [x', y']
      ring
    rw [hdiff]
    exact hxy
  have hdist_lt : dist x' y' < δ₁ := lt_of_le_of_lt hdist_le hδ_lt_δ₁
  have hu_lt : dist (u x') (u y') < ε := hδ₁ x' hxmem y' hymem hdist_lt
  have hu_le : |u x' - u y'| ≤ ε := by
    rw [← Real.dist_eq]
    exact le_of_lt hu_lt
  simpa [hxper, hyper] using hu_le

end

end Part8
