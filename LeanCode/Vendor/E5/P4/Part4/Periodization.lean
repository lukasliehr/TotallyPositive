import LeanCode.Vendor.E5.P4.Part4.Defs
import LeanCode.Vendor.E5.P4.Part4.KernelBasic
import LeanCode.Vendor.E5.Defs

open MeasureTheory

namespace Part4









theorem sumZ (c : ℝ) (hc : 0 < c) :
    Summable (fun k : ℤ => Real.exp (-c * |(k : ℝ)|)) ∧
    (∑' k : ℤ, Real.exp (-c * |(k : ℝ)|))
        = (1 + Real.exp (-c)) / (1 - Real.exp (-c)) ∧
    (1 + Real.exp (-c)) / (1 - Real.exp (-c)) ≤ 2 / (1 - Real.exp (-c)) := by
  have hr0 : 0 ≤ Real.exp (-c) := (Real.exp_pos _).le
  have hr1 : Real.exp (-c) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hden : 0 < 1 - Real.exp (-c) := by linarith

  have hnat : (fun n : ℕ => Real.exp (-c * |((n : ℤ) : ℝ)|))
      = (fun n : ℕ => Real.exp (-c) ^ n) := by
    funext n
    have h1 : |((n : ℤ) : ℝ)| = (n : ℝ) := by push_cast; exact abs_of_nonneg (Nat.cast_nonneg n)
    rw [h1, show -c * (n : ℝ) = (n : ℝ) * (-c) by ring, Real.exp_nat_mul]

  have hneg : (fun n : ℕ => Real.exp (-c * |((-(↑n + 1) : ℤ) : ℝ)|))
      = (fun n : ℕ => Real.exp (-c) ^ n * Real.exp (-c)) := by
    funext n
    have h1 : |((-(↑n + 1) : ℤ) : ℝ)| = (n : ℝ) + 1 := by
      push_cast; rw [abs_neg, abs_of_nonneg (by positivity)]
    rw [h1, show -c * ((n : ℝ) + 1) = ((n : ℝ) + 1) * (-c) by ring,
      show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.exp_nat_mul, pow_succ]

  have hHS : HasSum (fun k : ℤ => Real.exp (-c * |(k : ℝ)|))
      ((1 - Real.exp (-c))⁻¹ + (1 - Real.exp (-c))⁻¹ * Real.exp (-c)) := by
    apply HasSum.of_nat_of_neg_add_one
    · have h := hasSum_geometric_of_lt_one hr0 hr1
      rw [← hnat] at h; exact h
    · have h := (hasSum_geometric_of_lt_one hr0 hr1).mul_right (Real.exp (-c))
      rw [← hneg] at h; exact h
  refine ⟨hHS.summable, ?_, ?_⟩
  · rw [hHS.tsum_eq]; field_simp
  · rw [← sub_nonneg, div_sub_div_same]
    apply div_nonneg
    · linarith [hr1]
    · linarith [hr1]



theorem periodic_bdd (g : ℝ → ENNReal) (hper : ∀ y : ℝ, g (y + 1) = g y)
    (M : ENNReal) (hM : ∀ y : ℝ, y ∈ Set.Ico (0 : ℝ) 1 → g y ≤ M) :
    ∀ y : ℝ, g y ≤ M := by
  have hper_int : ∀ (y : ℝ) (k : ℤ), g (y + (k : ℝ)) = g y := by
    intro y k
    induction k using Int.induction_on with
    | zero => simp
    | succ i ih => rw [Int.cast_add, Int.cast_one, ← add_assoc, hper, ih]
    | pred i ih =>
      have h := hper (y + (↑(-(i : ℤ) - 1) : ℝ))
      rw [show (y + (↑(-(i : ℤ) - 1) : ℝ)) + 1 = y + (↑(-(i : ℤ)) : ℝ) by push_cast; ring] at h
      rw [← h]; exact ih
  intro y
  have hmem : Int.fract y ∈ Set.Ico (0 : ℝ) 1 := ⟨Int.fract_nonneg y, Int.fract_lt_one y⟩
  have key : Int.fract y + (↑⌊y⌋ : ℝ) = y := by unfold Int.fract; ring
  have hgy : g y = g (Int.fract y) := by
    have h := hper_int (Int.fract y) ⌊y⌋
    rwa [key] at h
  rw [hgy]
  exact hM (Int.fract y) hmem






theorem P_bound (f : ℝ → ℝ) (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hbound : ∀ x : ℝ, |f x| ≤ C * Real.exp (-c * |x|)) :
    ∀ x : ℝ, Summable (fun k : ℤ => |f (x + (k : ℝ))|) ∧
      (∑' k : ℤ, |f (x + (k : ℝ))|) ≤ 2 * C * Real.exp c / (1 - Real.exp (-c)) := by
  obtain ⟨hsumZ, hsumZval, hsumZle⟩ := sumZ c hc
  have hr1 : Real.exp (-c) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hden : 0 < 1 - Real.exp (-c) := by linarith

  have hsummable : ∀ x : ℝ, Summable (fun k : ℤ => |f (x + (k : ℝ))|) := by
    intro x
    refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) ?_
      (hsumZ.mul_left (C * Real.exp (c * |x|)))
    intro k
    calc |f (x + (k : ℝ))| ≤ C * Real.exp (-c * |x + (k : ℝ)|) := hbound _
      _ ≤ C * Real.exp (c * |x|) * Real.exp (-c * |(k : ℝ)|) := by
          rw [mul_assoc, ← Real.exp_add]
          refine mul_le_mul_of_nonneg_left ?_ hC.le
          apply Real.exp_le_exp.mpr
          have hrt : |(k : ℝ)| - |x| ≤ |x + (k : ℝ)| := by
            have h := abs_sub_abs_le_abs_sub (k : ℝ) (-x)
            rw [abs_neg, sub_neg_eq_add, add_comm (k : ℝ) x] at h
            exact h
          nlinarith [mul_le_mul_of_nonneg_left hrt hc.le]

  have hbound01 : ∀ y : ℝ, y ∈ Set.Ico (0 : ℝ) 1 →
      (∑' k : ℤ, |f (y + (k : ℝ))|) ≤ 2 * C * Real.exp c / (1 - Real.exp (-c)) := by
    intro y hy
    obtain ⟨hy0, hy1⟩ := hy
    have hle : ∀ k : ℤ, |f (y + (k : ℝ))| ≤ C * Real.exp c * Real.exp (-c * |(k : ℝ)|) := by
      intro k
      calc |f (y + (k : ℝ))| ≤ C * Real.exp (-c * |y + (k : ℝ)|) := hbound _
        _ ≤ C * Real.exp c * Real.exp (-c * |(k : ℝ)|) := by
            rw [mul_assoc, ← Real.exp_add]
            refine mul_le_mul_of_nonneg_left ?_ hC.le
            apply Real.exp_le_exp.mpr
            have hge : |(k : ℝ)| - 1 ≤ |y + (k : ℝ)| := by
              by_cases hk : 0 ≤ (k : ℝ)
              · rw [abs_of_nonneg hk, abs_of_nonneg (by linarith)]; linarith
              · rw [not_le] at hk
                have hkz : k < 0 := by exact_mod_cast hk
                have hk1 : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
                rw [abs_of_neg hk, abs_of_nonpos (by linarith)]; linarith
            nlinarith [mul_le_mul_of_nonneg_left hge hc.le]
    calc (∑' k : ℤ, |f (y + (k : ℝ))|)
        ≤ ∑' k : ℤ, C * Real.exp c * Real.exp (-c * |(k : ℝ)|) :=
          (hsummable y).tsum_le_tsum hle (hsumZ.mul_left (C * Real.exp c))
      _ = C * Real.exp c * ∑' k : ℤ, Real.exp (-c * |(k : ℝ)|) := tsum_mul_left
      _ = C * Real.exp c * ((1 + Real.exp (-c)) / (1 - Real.exp (-c))) := by rw [hsumZval]
      _ ≤ C * Real.exp c * (2 / (1 - Real.exp (-c))) :=
          mul_le_mul_of_nonneg_left hsumZle (by positivity)
      _ = 2 * C * Real.exp c / (1 - Real.exp (-c)) := by ring

  intro x
  refine ⟨hsummable x, ?_⟩
  have hreindex : (∑' k : ℤ, |f (x + (k : ℝ))|)
      = ∑' k : ℤ, |f (Int.fract x + (k : ℝ))| := by
    rw [← (Equiv.addLeft ⌊x⌋).tsum_eq (fun k : ℤ => |f (Int.fract x + (k : ℝ))|)]
    refine tsum_congr (fun k => ?_)
    have hk : ((Equiv.addLeft ⌊x⌋) k : ℤ) = ⌊x⌋ + k := rfl
    have hxk : x + (k : ℝ) = Int.fract x + (((Equiv.addLeft ⌊x⌋) k : ℤ) : ℝ) := by
      rw [hk]; push_cast; linarith [Int.floor_add_fract x]
    rw [hxk]
  rw [hreindex]
  exact hbound01 (Int.fract x) ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩




theorem H_bdd_antiper (f : ℝ → ℝ) (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hbound : ∀ x : ℝ, |f x| ≤ C * Real.exp (-c * |x|)) :
    (∀ x : ℝ, Summable (fun k : ℤ => (-1 : ℝ) ^ k * f (x + (k : ℝ)))) ∧
    (∀ x : ℝ, |Halt f x| ≤ 2 * C * Real.exp c / (1 - Real.exp (-c))) ∧
    (∀ x : ℝ, Halt f (x + 1) = - Halt f x) := by
  have hnorm_eq : ∀ (x : ℝ) (k : ℤ),
      ‖(-1 : ℝ) ^ k * f (x + (k : ℝ))‖ = |f (x + (k : ℝ))| := by
    intro x k
    rw [Real.norm_eq_abs, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  have hsummN : ∀ x : ℝ, Summable (fun k : ℤ => (-1 : ℝ) ^ k * f (x + (k : ℝ))) := by
    intro x
    apply Summable.of_norm
    simp_rw [hnorm_eq]
    exact (P_bound f C c hC hc hbound x).1
  refine ⟨hsummN, ?_, ?_⟩
  · intro x
    calc |Halt f x| = ‖∑' k : ℤ, (-1 : ℝ) ^ k * f (x + (k : ℝ))‖ := by
            rw [Halt]; exact (Real.norm_eq_abs _).symm
      _ ≤ ∑' k : ℤ, ‖(-1 : ℝ) ^ k * f (x + (k : ℝ))‖ :=
            norm_tsum_le_tsum_norm (by simp_rw [hnorm_eq]; exact (P_bound f C c hC hc hbound x).1)
      _ = ∑' k : ℤ, |f (x + (k : ℝ))| := by simp_rw [hnorm_eq]
      _ ≤ 2 * C * Real.exp c / (1 - Real.exp (-c)) := (P_bound f C c hC hc hbound x).2
  · intro x
    have hg : HasSum (fun j : ℤ => (-1 : ℝ) ^ j * f (x + (j : ℝ))) (Halt f x) :=
      (hsummN x).hasSum
    have hgshift : HasSum (fun k : ℤ => (-1 : ℝ) ^ (k + 1) * f (x + ((k + 1 : ℤ) : ℝ)))
        (Halt f x) := (Equiv.addRight (1 : ℤ)).hasSum_iff.mpr hg
    have hfeq : (fun k : ℤ => (-1 : ℝ) ^ k * f (x + 1 + (k : ℝ)))
        = (fun k : ℤ => -((-1 : ℝ) ^ (k + 1) * f (x + ((k + 1 : ℤ) : ℝ)))) := by
      funext k
      rw [zpow_add_one₀ (by norm_num : (-1 : ℝ) ≠ 0)]
      push_cast
      rw [show x + ((k : ℝ) + 1) = x + 1 + (k : ℝ) by ring]
      ring
    have hHS : HasSum (fun k : ℤ => (-1 : ℝ) ^ k * f (x + 1 + (k : ℝ))) (- Halt f x) := by
      rw [hfeq]; exact hgshift.neg
    exact hHS.tsum_eq



theorem H_meas (f : ℝ → ℝ) (hf : Measurable f) (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hbound : ∀ x : ℝ, |f x| ≤ C * Real.exp (-c * |x|)) :
    Measurable (Halt f) := by
  have hterm : ∀ k : ℤ, Measurable (fun x : ℝ => (-1 : ℝ) ^ k * f (x + (k : ℝ))) :=
    fun k => measurable_const.mul (hf.comp (measurable_id.add_const (k : ℝ)))
  have hsummN : ∀ x : ℝ, Summable (fun k : ℤ => (-1 : ℝ) ^ k * f (x + (k : ℝ))) := by
    intro x
    apply Summable.of_norm
    have hne : (fun k : ℤ => ‖(-1 : ℝ) ^ k * f (x + (k : ℝ))‖)
        = (fun k : ℤ => |f (x + (k : ℝ))|) := by
      funext k; rw [Real.norm_eq_abs, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
    rw [hne]; exact (P_bound f C c hC hc hbound x).1
  exact measurable_of_tendsto_metrizable' (Filter.atTop : Filter (Finset ℤ))
    (f := fun (s : Finset ℤ) (x : ℝ) => ∑ k ∈ s, (-1 : ℝ) ^ k * f (x + (k : ℝ)))
    (fun s => Finset.measurable_sum s (fun k _ => hterm k))
    (tendsto_pi_nhds.mpr (fun x => (hsummN x).hasSum))



theorem antiper_Z (F : ℝ → ℝ) (hF : ∀ x : ℝ, F (x + 1) = - F x) :
    ∀ (x : ℝ) (n : ℤ), F (x + (n : ℝ)) = (-1 : ℝ) ^ n * F x := by
  intro x n
  induction n using Int.induction_on with
  | zero => simp
  | succ i ih =>
    rw [Int.cast_add, Int.cast_one, ← add_assoc, hF, ih,
      zpow_add_one₀ (by norm_num : (-1 : ℝ) ≠ 0)]
    ring
  | pred i ih =>
    have hstep : F (x + (↑(-(i : ℤ)) : ℝ)) = - F (x + (↑(-(i : ℤ) - 1) : ℝ)) := by
      have h := hF (x + (↑(-(i : ℤ) - 1) : ℝ))
      rwa [show (x + (↑(-(i : ℤ) - 1) : ℝ)) + 1 = x + (↑(-(i : ℤ)) : ℝ) by push_cast; ring] at h
    have hB : F (x + (↑(-(i : ℤ) - 1) : ℝ)) = - ((-1 : ℝ) ^ (-(i : ℤ)) * F x) := by
      rw [← ih]; linarith [hstep]
    rw [hB, zpow_sub_one₀ (by norm_num : (-1 : ℝ) ≠ 0), show ((-1 : ℝ))⁻¹ = -1 by norm_num]
    ring


private theorem geom_ratio (a : ℝ) (ha : 0 < a) :
    HasSum (fun n : ℕ => (-Real.exp (-a)) ^ n) (1 + Real.exp (-a))⁻¹ := by
  have habs : |(-Real.exp (-a))| < 1 := by
    rw [abs_neg, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have h := hasSum_geometric_of_abs_lt_one habs
  rwa [sub_neg_eq_add] at h




theorem Ha_pos (a : ℝ) (ha : 0 < a) :
    (∀ x : ℝ, 0 < x → x < 1 →
      Halt (expKernel a) x = a * Real.exp (-a * x) / (1 + Real.exp (-a)) ∧
      0 < Halt (expKernel a) x) ∧
    (∀ x : ℝ, -1 < x → x < 0 →
      Halt (expKernel a) x
          = - (a * Real.exp (-a * (x + 1)) / (1 + Real.exp (-a))) ∧
      Halt (expKernel a) x < 0) := by
  refine ⟨?_, ?_⟩
  ·
    intro x hx0 hx1
    have hpt : ∀ n : ℕ, (-1 : ℝ) ^ ((n : ℤ)) * expKernel a (x + (((n : ℤ)) : ℝ))
        = a * Real.exp (-a * x) * (-Real.exp (-a)) ^ n := by
      intro n
      have hnn : (0 : ℝ) ≤ a * (x + ((n : ℤ) : ℝ)) :=
        mul_nonneg ha.le (by push_cast; positivity)
      rw [expKernel, if_pos hnn, abs_of_pos ha, zpow_natCast, neg_pow (Real.exp (-a)) n,
        ← Real.exp_nat_mul,
        show -(a * (x + ((n : ℤ) : ℝ))) = -a * x + (n : ℝ) * -a by push_cast; ring, Real.exp_add]
      ring
    have hnat : HasSum (fun n : ℕ => (-1 : ℝ) ^ ((n : ℤ)) * expKernel a (x + (((n : ℤ)) : ℝ)))
        (a * Real.exp (-a * x) * (1 + Real.exp (-a))⁻¹) := by
      have h := (geom_ratio a ha).mul_left (a * Real.exp (-a * x))
      simpa only [← hpt] using h
    have hHS : HasSum (fun k : ℤ => (-1 : ℝ) ^ k * expKernel a (x + (k : ℝ)))
        (a * Real.exp (-a * x) * (1 + Real.exp (-a))⁻¹) := by
      have h : HasSum (fun k : ℤ => (-1 : ℝ) ^ k * expKernel a (x + (k : ℝ)))
          (a * Real.exp (-a * x) * (1 + Real.exp (-a))⁻¹ + 0) := by
        refine HasSum.of_nat_of_neg_add_one hnat ?_
        convert hasSum_zero using 1
        funext n
        rw [expKernel, if_neg (not_le.mpr (mul_neg_of_pos_of_neg ha ?_)), mul_zero]
        push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
      rwa [add_zero] at h
    have hval : Halt (expKernel a) x = a * Real.exp (-a * x) / (1 + Real.exp (-a)) := by
      rw [Halt, hHS.tsum_eq, div_eq_mul_inv]
    exact ⟨hval, by rw [hval]; positivity⟩
  ·
    intro x hx1 hx0
    have hf0 : (-1 : ℝ) ^ (((0 : ℕ) : ℤ)) * expKernel a (x + ((((0 : ℕ) : ℤ)) : ℝ)) = 0 := by
      have hlt : a * (x + ((((0 : ℕ) : ℤ)) : ℝ)) < 0 := by
        push_cast; exact mul_neg_of_pos_of_neg ha (by linarith)
      rw [expKernel, if_neg (not_le.mpr hlt), mul_zero]
    have hpt : ∀ n : ℕ, (-1 : ℝ) ^ (((n + 1 : ℕ) : ℤ)) * expKernel a (x + (((n + 1 : ℕ) : ℤ) : ℝ))
        = -(a * Real.exp (-a * (x + 1))) * (-Real.exp (-a)) ^ n := by
      intro n
      have hnn : (0 : ℝ) ≤ a * (x + (((n + 1 : ℕ) : ℤ) : ℝ)) :=
        mul_nonneg ha.le (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) n])
      rw [expKernel, if_pos hnn, abs_of_pos ha, zpow_natCast, pow_succ,
        neg_pow (Real.exp (-a)) n, ← Real.exp_nat_mul,
        show -(a * (x + (((n + 1 : ℕ) : ℤ) : ℝ))) = -a * (x + 1) + (n : ℝ) * -a by
          push_cast; ring, Real.exp_add]
      ring
    have hshift : HasSum
        (fun n : ℕ => (-1 : ℝ) ^ (((n + 1 : ℕ) : ℤ)) * expKernel a (x + (((n + 1 : ℕ) : ℤ) : ℝ)))
        (-(a * Real.exp (-a * (x + 1))) * (1 + Real.exp (-a))⁻¹) := by
      have h := (geom_ratio a ha).mul_left (-(a * Real.exp (-a * (x + 1))))
      simpa only [← hpt] using h
    have hnat : HasSum (fun n : ℕ => (-1 : ℝ) ^ ((n : ℤ)) * expKernel a (x + (((n : ℤ)) : ℝ)))
        (-(a * Real.exp (-a * (x + 1))) * (1 + Real.exp (-a))⁻¹) := by
      have h := (hasSum_nat_add_iff
        (f := fun n : ℕ => (-1 : ℝ) ^ ((n : ℤ)) * expKernel a (x + (((n : ℤ)) : ℝ))) 1).mp hshift
      simp only [Finset.sum_range_one] at h
      rwa [hf0, add_zero] at h
    have hHS : HasSum (fun k : ℤ => (-1 : ℝ) ^ k * expKernel a (x + (k : ℝ)))
        (-(a * Real.exp (-a * (x + 1))) * (1 + Real.exp (-a))⁻¹) := by
      have h : HasSum (fun k : ℤ => (-1 : ℝ) ^ k * expKernel a (x + (k : ℝ)))
          (-(a * Real.exp (-a * (x + 1))) * (1 + Real.exp (-a))⁻¹ + 0) := by
        refine HasSum.of_nat_of_neg_add_one hnat ?_
        convert hasSum_zero using 1
        funext n
        rw [expKernel, if_neg (not_le.mpr (mul_neg_of_pos_of_neg ha ?_)), mul_zero]
        push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
      rwa [add_zero] at h
    have hval : Halt (expKernel a) x = -(a * Real.exp (-a * (x + 1)) / (1 + Real.exp (-a))) := by
      rw [Halt, hHS.tsum_eq, div_eq_mul_inv]; ring
    refine ⟨hval, ?_⟩
    rw [hval]
    have hpos : 0 < a * Real.exp (-a * (x + 1)) / (1 + Real.exp (-a)) := by positivity
    linarith





theorem Ha_neg (a : ℝ) (ha : a < 0) :
    (∀ x : ℝ, 0 < x → x < 1 →
      Halt (expKernel a) x = a * Real.exp (-a * (x - 1)) / (1 + Real.exp a) ∧
      Halt (expKernel a) x < 0) ∧
    (∀ x : ℝ, -1 < x → x < 0 →
      Halt (expKernel a) x = (-a) * Real.exp (-a * x) / (1 + Real.exp a) ∧
      0 < Halt (expKernel a) x) := by
  have geom : HasSum (fun n : ℕ => (-Real.exp a) ^ n) (1 + Real.exp a)⁻¹ := by
    have habs : |(-Real.exp a)| < 1 := by
      rw [abs_neg, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_lt_one_iff.mpr ha
    have h := hasSum_geometric_of_abs_lt_one habs
    rwa [sub_neg_eq_add] at h
  have hz : ∀ n : ℕ, (-1:ℝ)^(-((n:ℤ)+1)) = (-1)^(n+1) := by
    intro n
    rw [show -((n:ℤ)+1) = -(↑(n+1)) by push_cast; ring, zpow_neg, zpow_natCast, ← inv_pow,
        show (-1:ℝ)⁻¹ = -1 by norm_num]
  refine ⟨?_, ?_⟩
  · intro x hx0 hx1
    have hpt : ∀ n : ℕ,
        (-1 : ℝ) ^ (-((n : ℤ) + 1)) * expKernel a (x + ((-((n : ℤ) + 1) : ℤ) : ℝ))
          = a * Real.exp (-a * (x - 1)) * (-Real.exp a) ^ n := by
      intro n
      have hle : a * (x + ((-((n : ℤ) + 1) : ℤ) : ℝ)) ≥ 0 := by
        have : (x + ((-((n : ℤ) + 1) : ℤ) : ℝ)) ≤ 0 := by
          push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
        exact mul_nonneg_of_nonpos_of_nonpos ha.le this
      rw [expKernel, if_pos hle, abs_of_neg ha, hz n, pow_succ, neg_pow (Real.exp a) n,
        ← Real.exp_nat_mul,
        show -(a * (x + ((-((n : ℤ) + 1) : ℤ) : ℝ))) = -a * (x - 1) + (n : ℝ) * a by
          push_cast; ring, Real.exp_add]
      ring
    have hneg : HasSum
        (fun n : ℕ => (-1 : ℝ) ^ (-((n : ℤ) + 1))
            * expKernel a (x + ((-((n : ℤ) + 1) : ℤ) : ℝ)))
        (a * Real.exp (-a * (x - 1)) * (1 + Real.exp a)⁻¹) := by
      have h := geom.mul_left (a * Real.exp (-a * (x - 1)))
      simpa only [← hpt] using h
    have hnat : HasSum (fun n : ℕ => (-1 : ℝ) ^ ((n : ℤ)) * expKernel a (x + (((n : ℤ)) : ℝ)))
        0 := by
      convert hasSum_zero using 1
      funext n
      rw [expKernel, if_neg (not_le.mpr (mul_neg_of_neg_of_pos ha ?_)), mul_zero]
      push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
    have hHS : HasSum (fun k : ℤ => (-1 : ℝ) ^ k * expKernel a (x + (k : ℝ)))
        (a * Real.exp (-a * (x - 1)) * (1 + Real.exp a)⁻¹) := by
      have h : HasSum (fun k : ℤ => (-1 : ℝ) ^ k * expKernel a (x + (k : ℝ)))
          (0 + a * Real.exp (-a * (x - 1)) * (1 + Real.exp a)⁻¹) :=
        HasSum.of_nat_of_neg_add_one hnat hneg
      rwa [zero_add] at h
    have hval : Halt (expKernel a) x = a * Real.exp (-a * (x - 1)) / (1 + Real.exp a) := by
      rw [Halt, hHS.tsum_eq, div_eq_mul_inv]
    refine ⟨hval, ?_⟩
    rw [hval]
    have hden : 0 < 1 + Real.exp a := by positivity
    apply div_neg_of_neg_of_pos _ hden
    exact mul_neg_of_neg_of_pos ha (Real.exp_pos _)
  · intro x hx1 hx0
    have hpt : ∀ n : ℕ,
        (-1 : ℝ) ^ (-((n : ℤ) + 1)) * expKernel a (x + ((-((n : ℤ) + 1) : ℤ) : ℝ))
          = a * Real.exp (-a * (x - 1)) * (-Real.exp a) ^ n := by
      intro n
      have hle : a * (x + ((-((n : ℤ) + 1) : ℤ) : ℝ)) ≥ 0 := by
        have : (x + ((-((n : ℤ) + 1) : ℤ) : ℝ)) ≤ 0 := by
          push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
        exact mul_nonneg_of_nonpos_of_nonpos ha.le this
      rw [expKernel, if_pos hle, abs_of_neg ha, hz n, pow_succ, neg_pow (Real.exp a) n,
        ← Real.exp_nat_mul,
        show -(a * (x + ((-((n : ℤ) + 1) : ℤ) : ℝ))) = -a * (x - 1) + (n : ℝ) * a by
          push_cast; ring, Real.exp_add]
      ring
    have hneg : HasSum
        (fun n : ℕ => (-1 : ℝ) ^ (-((n : ℤ) + 1))
            * expKernel a (x + ((-((n : ℤ) + 1) : ℤ) : ℝ)))
        (a * Real.exp (-a * (x - 1)) * (1 + Real.exp a)⁻¹) := by
      have h := geom.mul_left (a * Real.exp (-a * (x - 1)))
      simpa only [← hpt] using h
    have hnat_pt : ∀ n : ℕ, n ≠ 0 →
        (-1 : ℝ) ^ ((n : ℤ)) * expKernel a (x + (((n : ℤ)) : ℝ)) = 0 := by
      intro n hn
      have hpos : 0 < x + (((n : ℤ)) : ℝ) := by
        have : (1 : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
        push_cast; linarith
      rw [expKernel, if_neg (not_le.mpr (mul_neg_of_neg_of_pos ha hpos)), mul_zero]
    have hnat0 : (-1 : ℝ) ^ (((0 : ℕ) : ℤ)) * expKernel a (x + ((((0 : ℕ) : ℤ)) : ℝ))
        = (-a) * Real.exp (-a * x) := by
      have hle : a * (x + ((((0 : ℕ) : ℤ)) : ℝ)) ≥ 0 :=
        mul_nonneg_of_nonpos_of_nonpos ha.le (by push_cast; linarith)
      rw [expKernel, if_pos hle, abs_of_neg ha]
      push_cast
      rw [show -(a * (x + 0)) = -a * x by ring]
      ring
    have hnat : HasSum (fun n : ℕ => (-1 : ℝ) ^ ((n : ℤ)) * expKernel a (x + (((n : ℤ)) : ℝ)))
        ((-a) * Real.exp (-a * x)) := by
      have h := hasSum_single (α := ℝ) (b := (0 : ℕ))
        (f := fun n : ℕ => (-1 : ℝ) ^ ((n : ℤ)) * expKernel a (x + (((n : ℤ)) : ℝ)))
        (fun n hn => hnat_pt n hn)
      rwa [hnat0] at h
    have hHS : HasSum (fun k : ℤ => (-1 : ℝ) ^ k * expKernel a (x + (k : ℝ)))
        ((-a) * Real.exp (-a * x) + a * Real.exp (-a * (x - 1)) * (1 + Real.exp a)⁻¹) :=
      HasSum.of_nat_of_neg_add_one hnat hneg
    have hval : Halt (expKernel a) x = (-a) * Real.exp (-a * x) / (1 + Real.exp a) := by
      rw [Halt, hHS.tsum_eq]
      have hden : (1 + Real.exp a) ≠ 0 := by positivity
      have he1 : Real.exp (-a * (x - 1)) = Real.exp (-a * x) * Real.exp a := by
        rw [← Real.exp_add]; congr 1; ring
      rw [he1]
      field_simp
      ring
    refine ⟨hval, ?_⟩
    rw [hval]
    have hden : 0 < 1 + Real.exp a := by positivity
    apply div_pos _ hden
    exact mul_pos (by linarith) (Real.exp_pos _)



theorem Ha_profile (a : ℝ) (ha : a ≠ 0) :
    PointwiseOneCrossing (Halt (expKernel a)) 0 (if 0 < a then 1 else -1) := by
  unfold PointwiseOneCrossing
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · rw [if_neg (not_lt.mpr hneg.le)]
    obtain ⟨h01, hm10⟩ := Ha_neg a hneg
    refine ⟨fun y hy1 hy2 => ?_, fun y hy1 hy2 => ?_⟩
    · have := (hm10 y (by linarith) hy2).2; linarith
    · have := (h01 y hy1 (by linarith)).2; linarith
  · rw [if_pos hpos]
    obtain ⟨h01, hm10⟩ := Ha_pos a hpos
    refine ⟨fun y hy1 hy2 => ?_, fun y hy1 hy2 => ?_⟩
    · have := (hm10 y (by linarith) hy2).2; linarith
    · have := (h01 y hy1 (by linarith)).2; linarith

end Part4
