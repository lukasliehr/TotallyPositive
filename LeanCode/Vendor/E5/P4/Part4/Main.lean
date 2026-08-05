import LeanCode.Vendor.E5.P4.Part4.Defs
import LeanCode.Vendor.E5.P4.Part4.KernelBasic
import LeanCode.Vendor.E5.P4.Part4.Translation
import LeanCode.Vendor.E5.P4.Part4.Regularity
import LeanCode.Vendor.E5.P4.Part4.Periodization
import LeanCode.Vendor.E5.Defs
open VendorE5

open MeasureTheory
open scoped ENNReal

namespace Part4








noncomputable def Ta (a : ℝ) (F : ℝ → ℝ) : ℝ → ℝ := conv (expKernel a) F


noncomputable def Jplus (a : ℝ) (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ s in (x - 1)..x, Real.exp (a * s) * F s


noncomputable def Jminus (b : ℝ) (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ s in x..(x + 1), Real.exp (-b * s) * F s




theorem H_conv (a : ℝ) (ha : a ≠ 0) (f : ℝ → ℝ) (hf : Measurable f)
    (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hbound : ∀ x : ℝ, |f x| ≤ C * Real.exp (-c * |x|)) :
    HasExponentialDecay (conv (expKernel a) f) ∧
    (∀ x : ℝ, Halt (conv (expKernel a) f) x = Ta a (Halt f) x) := by
  have haa : (0:ℝ) < |a| := abs_pos.mpr ha
  have hker_env : ∀ t : ℝ, |expKernel a t| ≤ |a| * Real.exp (-|a| * |t|) :=
    kernel_envelope a ha
  have hdc := decay_conv (expKernel a) f (kernel_meas a) hf |a| C |a| c haa hC haa hc
      hker_env hbound
  obtain ⟨hInt, hDecayBound⟩ := hdc
  have hdecay : HasExponentialDecay (conv (expKernel a) f) := by
    refine ⟨|a| * C * (4 / min |a| c), min |a| c / 2, ?_, ?_, hDecayBound⟩
    · positivity
    · have : 0 < min |a| c := lt_min haa hc
      positivity
  refine ⟨hdecay, ?_⟩
  intro x
  have hr1 : Real.exp (-c) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hden : 0 < 1 - Real.exp (-c) := by linarith
  set K : ℝ := 2 * C * Real.exp c / (1 - Real.exp (-c)) with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; positivity
  set F : ℤ → ℝ → ℝ := fun k t => expKernel a t * ((-1 : ℝ) ^ k * f ((x - t) + (k : ℝ)))
    with hFdef
  have hFabs : ∀ (k : ℤ) (t : ℝ), |F k t| = expKernel a t * |f ((x - t) + (k : ℝ))| := by
    intro k t
    rw [hFdef]
    simp only
    rw [abs_mul, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul,
        abs_of_nonneg (kernel_nonneg_bdd a t).1]
  have hFint : ∀ k : ℤ, Integrable (F k) := by
    intro k
    have hik := hInt (x + (k : ℝ))
    have heq : (fun t : ℝ => expKernel a t * f ((x + (k:ℝ)) - t))
        = fun t : ℝ => expKernel a t * f ((x - t) + (k : ℝ)) := by
      funext t; ring_nf
    rw [heq] at hik
    have := hik.const_mul ((-1:ℝ)^k)
    refine this.congr ?_
    filter_upwards with t
    rw [hFdef]; ring
  have hFmeas : ∀ k : ℤ, AEStronglyMeasurable (F k) volume := fun k => (hFint k).1
  have hPb := P_bound f C c hC hc hbound
  have hkint : (∫ t : ℝ, expKernel a t) = 1 := (kernel_int a ha).2
  have hkinteg : Integrable (expKernel a) := (kernel_int a ha).1
  have hfin : (∑' k : ℤ, ∫⁻ t : ℝ, ‖F k t‖ₑ ∂volume) ≠ ∞ := by
    have hmeasEnorm : ∀ k : ℤ, AEMeasurable (fun t => ‖F k t‖ₑ) volume :=
      fun k => (hFmeas k).enorm
    rw [← lintegral_tsum hmeasEnorm]
    have hpt_le : (fun t : ℝ => ∑' k : ℤ, ‖F k t‖ₑ)
        ≤ fun t : ℝ => ENNReal.ofReal (expKernel a t * K) := by
      intro t
      have hval : ∀ k : ℤ, ‖F k t‖ₑ
          = ENNReal.ofReal (expKernel a t) * ENNReal.ofReal |f ((x - t) + (k : ℝ))| := by
        intro k
        rw [Real.enorm_eq_ofReal_abs, hFabs k t,
            ENNReal.ofReal_mul (kernel_nonneg_bdd a t).1]
      calc (∑' k : ℤ, ‖F k t‖ₑ)
          = ∑' k : ℤ, ENNReal.ofReal (expKernel a t) * ENNReal.ofReal |f ((x - t) + (k : ℝ))| := by
            exact tsum_congr hval
        _ = ENNReal.ofReal (expKernel a t) * ∑' k : ℤ, ENNReal.ofReal |f ((x - t) + (k : ℝ))| :=
            ENNReal.tsum_mul_left
        _ = ENNReal.ofReal (expKernel a t)
              * ENNReal.ofReal (∑' k : ℤ, |f ((x - t) + (k : ℝ))|) := by
            rw [ENNReal.ofReal_tsum_of_nonneg (fun n => abs_nonneg _) (hPb (x - t)).1]
        _ ≤ ENNReal.ofReal (expKernel a t) * ENNReal.ofReal K := by
            gcongr
            exact (hPb (x - t)).2
        _ = ENNReal.ofReal (expKernel a t * K) := by
            rw [ENNReal.ofReal_mul (kernel_nonneg_bdd a t).1]
    have hle : (∫⁻ t : ℝ, ∑' k : ℤ, ‖F k t‖ₑ) ≤ ENNReal.ofReal K :=
      calc (∫⁻ t : ℝ, ∑' k : ℤ, ‖F k t‖ₑ)
          ≤ ∫⁻ t : ℝ, ENNReal.ofReal (expKernel a t * K) := lintegral_mono hpt_le
        _ = ENNReal.ofReal (∫ t : ℝ, expKernel a t * K) := by
            rw [ofReal_integral_eq_lintegral_ofReal (hkinteg.mul_const K)
              (ae_of_all _ (fun t => mul_nonneg (kernel_nonneg_bdd a t).1 hKnn))]
        _ = ENNReal.ofReal K := by rw [integral_mul_const, hkint, one_mul]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hswap := integral_tsum (μ := volume) hFmeas hfin
  rw [Halt]
  have hconv_val : ∀ k : ℤ, (-1 : ℝ) ^ k * conv (expKernel a) f (x + (k : ℝ))
      = ∫ t : ℝ, F k t := by
    intro k
    rw [conv]
    rw [← integral_const_mul]
    congr 1
    funext t
    rw [hFdef]
    have : (x + (k:ℝ)) - t = (x - t) + (k : ℝ) := by ring
    rw [this]; ring
  have hLHS : (∑' k : ℤ, (-1 : ℝ) ^ k * conv (expKernel a) f (x + (k : ℝ)))
      = ∑' k : ℤ, ∫ t : ℝ, F k t := tsum_congr hconv_val
  rw [hLHS, ← hswap]
  rw [Ta, conv]
  congr 1
  funext t
  rw [hFdef]
  simp only
  rw [Halt]
  rw [tsum_mul_left]



theorem antiper_T (a : ℝ) (_ha : a ≠ 0) (M : ℝ) (_hM : 0 ≤ M) (F : ℝ → ℝ)
    (_hFmeas : Measurable F) (_hFbdd : ∀ x, |F x| ≤ M) (hFanti : ∀ x, F (x + 1) = - F x) :
    ∀ x : ℝ, Ta a F (x + 1) = - Ta a F x := by
  intro x
  have hfun : (fun t : ℝ => expKernel a t * F (x + 1 - t))
      = (fun t : ℝ => -(expKernel a t * F (x - t))) := by
    funext t
    rw [show x + 1 - t = (x - t) + 1 by ring, hFanti (x - t)]
    ring
  simp only [Ta, conv]
  rw [hfun, integral_neg]



theorem resum_pos (a : ℝ) (ha : 0 < a) (M : ℝ) (hM : 0 ≤ M) (F : ℝ → ℝ)
    (hFmeas : Measurable F) (hFbdd : ∀ x, |F x| ≤ M) (hFanti : ∀ x, F (x + 1) = - F x) :
    ∀ x : ℝ, Ta a F x
        = a * Real.exp (-a * x) / (1 + Real.exp (-a)) * Jplus a F x := by
  intro x
  classical
  set g : ℝ → ℝ := fun t => expKernel a t * F (x - t) with hg
  have hgint : Integrable g := (conv_kernel a ha.ne' M hM F hFmeas hFbdd).1 x
  have hTa : Ta a F x = ∫ t, g t := rfl
  have hZ : HasSum (fun n : ℤ => ∫ u in (0:ℝ)..(1:ℝ), g (u + n)) (∫ t, g t) :=
    hgint.hasSum_intervalIntegral_comp_add_int
  set P : ℝ := ∫ u in (0:ℝ)..(1:ℝ), Real.exp (-a * u) * F (x - u) with hP
  have hpos_term : ∀ n : ℕ,
      (∫ u in (0:ℝ)..(1:ℝ), g (u + (n : ℤ))) = (-Real.exp (-a)) ^ n * (a * P) := by
    intro n
    have hcongr : (∫ u in (0:ℝ)..(1:ℝ), g (u + (n : ℤ)))
        = ∫ u in (0:ℝ)..(1:ℝ), (-Real.exp (-a)) ^ n * (a * (Real.exp (-a * u) * F (x - u))) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le (by norm_num)] at hu
      have hu0 : 0 ≤ u := hu.1
      have hnn : (0:ℝ) ≤ a * (u + (n:ℤ)) := by
        have : (0:ℝ) ≤ (u + (n:ℤ)) := by
          have : (0:ℝ) ≤ (n:ℤ) := by exact_mod_cast Int.natCast_nonneg n
          push_cast
          push_cast at this
          linarith [hu0, this]
        positivity
      have hker : expKernel a (u + (n:ℤ)) = a * Real.exp (-(a * (u + (n:ℤ)))) := by
        simp only [expKernel, if_pos hnn, abs_of_pos ha]
      have hFshift : F (x - (u + (n:ℤ))) = (-1 : ℝ) ^ n * F (x - u) := by
        have h1 : x - (u + (n:ℤ)) = (x - u) + ((-n : ℤ) : ℝ) := by push_cast; ring
        rw [h1, antiper_Z F hFanti (x - u) (-n)]
        congr 1
        rw [zpow_neg]
        rw [zpow_natCast]
        rcases Nat.even_or_odd n with he | ho
        · rw [he.neg_one_pow]; norm_num
        · rw [ho.neg_one_pow]; norm_num
      simp only [hg]
      rw [hker, hFshift]
      have hexp : Real.exp (-(a * (u + (n:ℤ)))) = Real.exp (-(a*u)) * (Real.exp (-a)) ^ n := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        push_cast
        ring
      rw [hexp]
      have : (-Real.exp (-a)) ^ n = (-1 : ℝ) ^ n * (Real.exp (-a)) ^ n := by
        rw [← neg_one_mul (Real.exp (-a)), mul_pow]
      rw [this, show -(a * u) = -a * u by ring]
      ring
    rw [hcongr, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hP]
  have hneg_term : ∀ n : ℕ, (∫ u in (0:ℝ)..(1:ℝ), g (u + (-(↑n + 1) : ℤ))) = 0 := by
    intro n
    have hzero : (∫ u in (0:ℝ)..(1:ℝ), g (u + (-(↑n + 1) : ℤ))) = ∫ u in (0:ℝ)..(1:ℝ), (0:ℝ) := by
      apply intervalIntegral.integral_congr_ae
      have hne : ∀ᵐ u : ℝ, u ≠ 1 := by
        rw [ae_iff]
        simp only [not_not]
        exact measure_singleton 1
      filter_upwards [hne] with u hune hmem
      rw [Set.uIoc_of_le (by norm_num)] at hmem
      have hu1 : u < 1 := lt_of_le_of_ne hmem.2 hune
      have hlt : ¬ (0:ℝ) ≤ a * (u + (-(↑n + 1) : ℤ)) := by
        have : (u + (-(↑n + 1) : ℤ)) < 0 := by
          push_cast
          have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
          linarith [hu1, this]
        have := mul_neg_of_pos_of_neg ha this
        linarith
      simp only [hg, expKernel, if_neg hlt, zero_mul]
    rw [hzero, intervalIntegral.integral_zero]
  have habs : |(-Real.exp (-a))| < 1 := by
    rw [abs_neg, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom : HasSum (fun n : ℕ => (-Real.exp (-a)) ^ n) (1 - (-Real.exp (-a)))⁻¹ :=
    hasSum_geometric_of_abs_lt_one habs
  have hgeomP : HasSum (fun n : ℕ => (-Real.exp (-a)) ^ n * (a * P))
      ((1 - (-Real.exp (-a)))⁻¹ * (a * P)) := hgeom.mul_right (a * P)
  have hposHasSum : HasSum (fun n : ℕ => ∫ u in (0:ℝ)..(1:ℝ), g (u + (n : ℤ)))
      ((1 - (-Real.exp (-a)))⁻¹ * (a * P)) := by
    have : (fun n : ℕ => ∫ u in (0:ℝ)..(1:ℝ), g (u + (n : ℤ)))
        = fun n : ℕ => (-Real.exp (-a)) ^ n * (a * P) := by
      funext n; exact hpos_term n
    rw [this]; exact hgeomP
  have hnegHasSum : HasSum (fun n : ℕ => ∫ u in (0:ℝ)..(1:ℝ), g (u + (-(↑n + 1) : ℤ))) 0 := by
    have : (fun n : ℕ => ∫ u in (0:ℝ)..(1:ℝ), g (u + (-(↑n + 1) : ℤ))) = fun _ : ℕ => (0:ℝ) := by
      funext n; exact hneg_term n
    rw [this]; exact hasSum_zero
  have hZ' : HasSum (fun n : ℤ => ∫ u in (0:ℝ)..(1:ℝ), g (u + n))
      ((1 - (-Real.exp (-a)))⁻¹ * (a * P) + 0) :=
    HasSum.of_nat_of_neg_add_one hposHasSum hnegHasSum
  have hval : (∫ t, g t) = (1 - (-Real.exp (-a)))⁻¹ * (a * P) + 0 :=
    hZ.unique hZ'
  have hPJ : P = Real.exp (-a * x) * Jplus a F x := by
    rw [hP]
    have hsub : (∫ u in (0:ℝ)..(1:ℝ), Real.exp (-a * u) * F (x - u))
        = ∫ s in (x - 1)..(x - 0), Real.exp (-a * (x - s)) * F s := by
      have := intervalIntegral.integral_comp_sub_left
        (fun s => Real.exp (-a * (x - s)) * F s) (a := (0:ℝ)) (b := (1:ℝ)) (d := x)
      rw [← this]
      apply intervalIntegral.integral_congr
      intro u _
      simp only []
      rw [show x - (x - u) = u by ring]
    rw [hsub]
    rw [Jplus]
    rw [sub_zero]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    simp only []
    have he : Real.exp (-a * (x - s)) = Real.exp (-a * x) * Real.exp (a * s) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [he]; ring
  rw [hTa, hval, add_zero, hPJ]
  have hden : (1 - (-Real.exp (-a))) = 1 + Real.exp (-a) := by ring
  rw [hden]
  ring





theorem resum_neg (a : ℝ) (ha : a < 0) (M : ℝ) (hM : 0 ≤ M) (F : ℝ → ℝ)
    (hFmeas : Measurable F) (hFbdd : ∀ x, |F x| ≤ M) (hFanti : ∀ x, F (x + 1) = - F x) :
    ∀ x : ℝ, Ta a F x
        = (-a) * Real.exp (-a * x) / (1 + Real.exp a) * Jminus (-a) F x := by
  intro x
  set b : ℝ := -a with hb
  have hbpos : 0 < b := by rw [hb]; linarith
  have geom : HasSum (fun n : ℕ => (-Real.exp (-b)) ^ n) (1 + Real.exp (-b))⁻¹ := by
    have habs : |(-Real.exp (-b))| < 1 := by
      rw [abs_neg, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_lt_one_iff.mpr (by linarith)
    have h := hasSum_geometric_of_abs_lt_one habs
    rwa [sub_neg_eq_add] at h
  set g : ℝ → ℝ := fun t => expKernel a t * F (x - t) with hgdef
  have hgint : Integrable g := by
    have := (conv_kernel a ha.ne M hM F hFmeas hFbdd).1 x
    simpa only [hgdef] using this
  set gr : ℝ → ℝ := fun τ => expKernel a (-τ) * F (x + τ) with hgrdef
  have hgr_eq : gr = fun τ => g (-τ) := by
    funext τ; simp only [hgrdef, hgdef, sub_neg_eq_add]
  have hgrint : Integrable gr := by
    rw [hgr_eq]; exact hgint.comp_neg
  have hTa_gr : Ta a F x = ∫ τ, gr τ := by
    rw [hgr_eq]
    have : (∫ τ, g (-τ)) = ∫ τ, g τ := integral_neg_eq_self g volume
    rw [this]
    simp only [Ta, conv, hgdef]
  have hHSint : HasSum (fun n : ℤ => ∫ u in (0:ℝ)..1, gr (u + n)) (∫ τ, gr τ) :=
    hgrint.hasSum_intervalIntegral_comp_add_int
  set P : ℝ := ∫ u in (0:ℝ)..1, Real.exp (-b * u) * F (x + u) with hPdef
  have hcellpt : ∀ (n : ℕ) (u : ℝ), 0 ≤ u →
      gr (u + (n : ℤ)) = ((-1)^n * b * Real.exp (-b * n)) * (Real.exp (-b * u) * F (x + u)) := by
    intro n u hu0
    have hknn : 0 ≤ a * (-(u + (n : ℤ))) := by
      have huu : 0 ≤ u + (n : ℝ) := by positivity
      push_cast
      have hrw : a * (-(u + (n:ℝ))) = b * (u + (n:ℝ)) := by rw [hb]; ring
      rw [hrw]; positivity
    have hkval : expKernel a (-(u + (n : ℤ))) = b * Real.exp (-b * (u + n)) := by
      simp only [expKernel]
      rw [if_pos hknn, abs_of_neg ha]
      have hexp : Real.exp (-(a * -(u + ((n:ℤ):ℝ)))) = Real.exp (-b * (u + (n:ℝ))) := by
        congr 1; push_cast; rw [hb]; ring
      rw [hexp]
    have hFval : F (x + (u + (n : ℤ))) = (-1:ℝ)^n * F (x + u) := by
      have h := antiper_Z F hFanti (x + u) (n : ℤ)
      rw [show x + (u + ((n:ℤ):ℝ)) = (x + u) + ((n:ℤ):ℝ) by push_cast; ring]
      rw [h, zpow_natCast]
    simp only [hgrdef]
    rw [hkval, hFval]
    rw [show Real.exp (-b * (u + (n:ℝ))) = Real.exp (-b * u) * Real.exp (-b * n) by
      rw [← Real.exp_add]; congr 1; ring]
    ring
  set cell : ℤ → ℝ := fun k => ∫ u in (0:ℝ)..1, gr (u + (k : ℝ)) with hcelldef
  have hHScell : HasSum cell (∫ τ, gr τ) := hHSint
  have hnat : HasSum (fun n : ℕ => cell (n : ℤ))
      ((1 + Real.exp (-b))⁻¹ * (b * P)) := by
    have hcell : ∀ n : ℕ, cell (n : ℤ) = (-Real.exp (-b))^n * (b * P) := by
      intro n
      have hcongr : cell (n : ℤ)
          = ∫ u in (0:ℝ)..1, ((-1)^n * b * Real.exp (-b * n)) * (Real.exp (-b * u) * F (x + u)) := by
        simp only [hcelldef]
        apply intervalIntegral.integral_congr
        intro u hu
        have hu0 : 0 ≤ u := by
          rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hu
          exact hu.1
        rw [show ((n : ℤ) : ℝ) = ((n : ℕ) : ℝ) by push_cast; ring]
        exact hcellpt n u hu0
      rw [hcongr, intervalIntegral.integral_const_mul, ← hPdef]
      rw [show ((-1:ℝ)^n * b * Real.exp (-b * n)) * P = (-Real.exp (-b))^n * (b * P) by
        rw [show Real.exp (-b * (n:ℝ)) = Real.exp (-b) ^ n by
          rw [← Real.exp_nat_mul]; congr 1; ring]
        rw [neg_pow]; ring]
    have hg := geom.mul_right (b * P)
    simpa only [← hcell] using hg
  have hneg : HasSum (fun n : ℕ => cell (-((n : ℤ) + 1))) 0 := by
    convert hasSum_zero using 1
    funext n
    simp only [hcelldef]
    have Hopen : ∀ u : ℝ, 0 < u → u < 1 → gr (u + ((-((n : ℤ) + 1) : ℤ) : ℝ)) = 0 := by
      intro u hu0 hu1
      have harg : ¬ (0 ≤ a * (-(u + ((-((n:ℤ)+1) : ℤ) : ℝ)))) := by
        have hgt : 0 < (u + ((-((n:ℤ)+1) : ℤ) : ℝ)) * (-1) := by
          have := Nat.cast_nonneg (α := ℝ) n
          push_cast
          nlinarith
        have hval : a * (-(u + ((-((n:ℤ)+1) : ℤ) : ℝ)))
            = a * ((u + ((-((n:ℤ)+1) : ℤ) : ℝ)) * (-1)) := by ring
        rw [hval]
        exact not_le.mpr (mul_neg_of_neg_of_pos ha hgt)
      simp only [hgrdef, expKernel, if_neg harg, zero_mul]
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0:ℝ))]
    · simp
    · have hne : ∀ᵐ u : ℝ ∂volume, u ≠ 1 := by
        have h1 : volume ({(1:ℝ)} : Set ℝ) = 0 := by simp
        exact (ae_iff).mpr (by simp [h1])
      filter_upwards [hne] with u hu1 hmem
      rw [Set.mem_uIoc] at hmem
      rcases hmem with ⟨hl, hr⟩ | ⟨hl, hr⟩
      · exact Hopen u hl (lt_of_le_of_ne hr hu1)
      · linarith
  have hZsplit : HasSum cell ((1 + Real.exp (-b))⁻¹ * (b * P) + 0) :=
    HasSum.of_nat_of_neg_add_one hnat hneg
  rw [add_zero] at hZsplit
  have hval : (∫ τ, gr τ) = (1 + Real.exp (-b))⁻¹ * (b * P) := hHScell.unique hZsplit
  have hP : P = Real.exp (b * x) * Jminus b F x := by
    have hsub : (∫ u in (0:ℝ)..1, (fun s => Real.exp (-b * (s - x)) * F s) (u + x))
        = ∫ s in (0 + x)..(1 + x), Real.exp (-b * (s - x)) * F s :=
      intervalIntegral.integral_comp_add_right (fun s => Real.exp (-b * (s - x)) * F s) x
    simp only [zero_add] at hsub
    have hPeq : P = ∫ u in (0:ℝ)..1, (fun s => Real.exp (-b * (s - x)) * F s) (u + x) := by
      rw [hPdef]
      apply intervalIntegral.integral_congr
      intro u _
      simp only
      rw [show (u + x) - x = u by ring, add_comm x u]
    rw [hPeq, hsub, show (1 + x) = x + 1 by ring, Jminus]
    rw [show (∫ s in x..(x+1), Real.exp (-b * (s - x)) * F s)
        = ∫ s in x..(x+1), Real.exp (b * x) * (Real.exp (-b * s) * F s) by
      apply intervalIntegral.integral_congr
      intro s _
      simp only
      rw [show Real.exp (-b * (s - x)) = Real.exp (b * x) * Real.exp (-b * s) by
        rw [← Real.exp_add]; congr 1; ring]
      ring]
    rw [intervalIntegral.integral_const_mul]
  rw [hTa_gr, hval, hP]
  simp only [hb]
  rw [show Real.exp (- -a) = Real.exp a by norm_num]
  have hden : (1 : ℝ) + Real.exp a ≠ 0 := by positivity
  field_simp




theorem int_pos (x₁ x₂ : ℝ) (hx : x₁ < x₂) (φ : ℝ → ℝ)
    (hint : IntervalIntegrable φ volume x₁ x₂)
    (hpos : ∀ s : ℝ, s ∈ Set.Ioo x₁ x₂ → 0 < φ s) :
    0 < ∫ s in x₁..x₂, φ s :=
  intervalIntegral.intervalIntegral_pos_of_pos_on hint hpos hx







theorem J_plus (a : ℝ) (_ha : 0 < a) (M : ℝ) (_hM : 0 ≤ M) (F : ℝ → ℝ)
    (hFmeas : Measurable F) (hFbdd : ∀ x, |F x| ≤ M) (hFanti : ∀ x, F (x + 1) = - F x) :
    Continuous (Jplus a F) ∧
    (∀ x : ℝ, Jplus a F (x + 1) = - Real.exp a * Jplus a F x) ∧
    (∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ r : ℝ,
      (∀ s : ℝ, s ∈ Set.Ioo r (r + 1) → 0 < ε * F s) →
      ∀ x₁ x₂ : ℝ, r ≤ x₁ → x₁ < x₂ → x₂ ≤ r + 1 →
        ε * Jplus a F x₁ < ε * Jplus a F x₂) := by
  have hFii : ∀ p q : ℝ, IntervalIntegrable F volume p q := by
    intro p q
    rw [intervalIntegrable_iff]
    apply IntegrableOn.of_bound measure_Ioc_lt_top hFmeas.aestronglyMeasurable.restrict M
    filter_upwards with x
    simpa [Real.norm_eq_abs] using hFbdd x
  have hGii : ∀ p q : ℝ, IntervalIntegrable (fun s => Real.exp (a * s) * F s) volume p q := by
    intro p q
    exact (hFii p q).continuousOn_mul
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn)
  set G : ℝ → ℝ := fun s => Real.exp (a * s) * F s with hG
  have incr : ∀ x₁ x₂ : ℝ,
      Jplus a F x₂ - Jplus a F x₁
        = ∫ s in x₁..x₂, (Real.exp (a * s) + Real.exp (a * (s - 1))) * F s := by
    intro x₁ x₂
    have c1 : (∫ s in (x₁ - 1)..x₁, G s) + (∫ s in x₁..x₂, G s)
        = ∫ s in (x₁ - 1)..x₂, G s :=
      intervalIntegral.integral_add_adjacent_intervals (hGii _ _) (hGii _ _)
    have c2 : (∫ s in (x₁ - 1)..(x₂ - 1), G s) + (∫ s in (x₂ - 1)..x₂, G s)
        = ∫ s in (x₁ - 1)..x₂, G s :=
      intervalIntegral.integral_add_adjacent_intervals (hGii _ _) (hGii _ _)
    have hsub : (∫ s in x₁..x₂, G (s - 1)) = ∫ s in (x₁ - 1)..(x₂ - 1), G s := by
      exact intervalIntegral.integral_comp_sub_right (a := x₁) (b := x₂) G 1
    have hGshift : (fun s => G (s - 1)) = fun s => -(Real.exp (a * (s - 1)) * F s) := by
      funext s
      have hfs : F (s - 1) = - F s := by
        have := hFanti (s - 1); rw [sub_add_cancel] at this; linarith
      simp only [hG]
      rw [hfs]; ring
    have hJ1 : Jplus a F x₁ = ∫ s in (x₁ - 1)..x₁, G s := rfl
    have hJ2 : Jplus a F x₂ = ∫ s in (x₂ - 1)..x₂, G s := rfl
    have key : (∫ s in (x₂ - 1)..x₂, G s) - (∫ s in (x₁ - 1)..x₁, G s)
        = (∫ s in x₁..x₂, G s) - (∫ s in (x₁ - 1)..(x₂ - 1), G s) := by
      have e : (∫ s in (x₁ - 1)..x₁, G s) + (∫ s in x₁..x₂, G s)
          = (∫ s in (x₁ - 1)..(x₂ - 1), G s) + (∫ s in (x₂ - 1)..x₂, G s) := by
        rw [c1, c2]
      linarith
    rw [hJ2, hJ1, key, ← hsub, hGshift, intervalIntegral.integral_neg]
    rw [sub_neg_eq_add, ← intervalIntegral.integral_add (hGii _ _)]
    · congr 1; funext s; simp only [hG]; ring
    · exact (hFii _ _).continuousOn_mul
        ((Real.continuous_exp.comp (continuous_const.mul
          (continuous_id.sub continuous_const))).continuousOn)
  have hP : Continuous (fun x => ∫ s in (0 : ℝ)..x, G s) :=
    intervalIntegral.continuous_primitive (fun p q => hGii p q) 0
  have hJP : Jplus a F = fun x => (∫ s in (0 : ℝ)..x, G s) - (∫ s in (0 : ℝ)..(x - 1), G s) := by
    funext x
    have ch : (∫ s in (x - 1)..(0 : ℝ), G s) + (∫ s in (0 : ℝ)..x, G s)
        = ∫ s in (x - 1)..x, G s :=
      intervalIntegral.integral_add_adjacent_intervals (hGii _ _) (hGii _ _)
    have hsym : (∫ s in (x - 1)..(0 : ℝ), G s) = -(∫ s in (0 : ℝ)..(x - 1), G s) := by
      rw [intervalIntegral.integral_symm]
    show Jplus a F x = _
    rw [show Jplus a F x = ∫ s in (x - 1)..x, G s from rfl, ← ch, hsym]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hJP]
    exact hP.sub (hP.comp (continuous_id.sub continuous_const))
  · intro x
    have hstep : Jplus a F (x + 1) = ∫ s in x..(x + 1), G s := by
      show (∫ s in (x + 1 - 1)..(x + 1), G s) = _
      congr 1; ring
    have hsub : (∫ s in (x - 1)..x, G (s + 1)) = ∫ s in x..(x + 1), G s := by
      have h := intervalIntegral.integral_comp_add_right (a := x - 1) (b := x) G 1
      rw [sub_add_cancel] at h
      exact h
    have hshift : (fun s => G (s + 1)) = fun s => -Real.exp a * G s := by
      funext s
      simp only [hG]
      rw [hFanti s, mul_add, Real.exp_add, mul_one]; ring
    rw [hstep, ← hsub, hshift, intervalIntegral.integral_const_mul,
      show Jplus a F x = ∫ s in (x - 1)..x, G s from rfl]
  · intro ε hε r hcross x₁ x₂ hr1 hlt hr2
    have hεJ : ε * Jplus a F x₂ - ε * Jplus a F x₁
        = ∫ s in x₁..x₂, (Real.exp (a * s) + Real.exp (a * (s - 1))) * (ε * F s) := by
      rw [← mul_sub, incr x₁ x₂, ← intervalIntegral.integral_const_mul]
      congr 1; funext s; ring
    have hφpos : ∀ s : ℝ, s ∈ Set.Ioo x₁ x₂ →
        0 < (Real.exp (a * s) + Real.exp (a * (s - 1))) * (ε * F s) := by
      intro s hs
      have hs' : s ∈ Set.Ioo r (r + 1) := by
        constructor
        · exact lt_of_le_of_lt hr1 hs.1
        · exact lt_of_lt_of_le hs.2 hr2
      have hFs : 0 < ε * F s := hcross s hs'
      have hw : 0 < Real.exp (a * s) + Real.exp (a * (s - 1)) := by positivity
      exact mul_pos hw hFs
    have hφii : IntervalIntegrable
        (fun s => (Real.exp (a * s) + Real.exp (a * (s - 1))) * (ε * F s)) volume x₁ x₂ := by
      have : (fun s => (Real.exp (a * s) + Real.exp (a * (s - 1))) * (ε * F s))
          = (fun s => (ε * F s) * (Real.exp (a * s) + Real.exp (a * (s - 1)))) := by
        funext s; ring
      rw [this]
      apply IntervalIntegrable.mul_continuousOn (by
        simpa using (hFii x₁ x₂).const_mul ε)
      exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).add
        (Real.continuous_exp.comp (continuous_const.mul
          (continuous_id.sub continuous_const)))).continuousOn
    have hpos := int_pos x₁ x₂ hlt _ hφii hφpos
    rw [← hεJ] at hpos
    linarith







theorem J_minus (b : ℝ) (hb : 0 < b) (M : ℝ) (hM : 0 ≤ M) (F : ℝ → ℝ)
    (hFmeas : Measurable F) (hFbdd : ∀ x, |F x| ≤ M) (hFanti : ∀ x, F (x + 1) = - F x) :
    Continuous (Jminus b F) ∧
    (∀ x : ℝ, Jminus b F (x + 1) = - Real.exp (-b) * Jminus b F x) ∧
    (∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ r : ℝ,
      (∀ s : ℝ, s ∈ Set.Ioo r (r + 1) → 0 < ε * F s) →
      ∀ x₁ x₂ : ℝ, r ≤ x₁ → x₁ < x₂ → x₂ ≤ r + 1 →
        ε * Jminus b F x₂ < ε * Jminus b F x₁) := by
  have hker : Continuous (fun s : ℝ => Real.exp (-b * s)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hFint : ∀ p q : ℝ, IntervalIntegrable F volume p q := by
    intro p q
    rw [intervalIntegrable_iff]
    apply Measure.integrableOn_of_bounded (M := M)
    · exact (measure_Ioc_lt_top).ne
    · exact hFmeas.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun s => (Real.norm_eq_abs _).symm ▸ hFbdd s)
  set G : ℝ → ℝ := fun s => Real.exp (-b * s) * F s with hGdef
  have hGint : ∀ p q : ℝ, IntervalIntegrable G volume p q := by
    intro p q
    exact (hFint p q).continuousOn_mul hker.continuousOn
  have hGa : ∀ σ : ℝ, G (σ + 1) = - (Real.exp (-b * (σ + 1)) * F σ) := by
    intro σ; simp only [hGdef]; rw [hFanti σ]; ring
  set W : ℝ → ℝ := fun s => (Real.exp (-b * s) + Real.exp (-b * (s + 1))) * F s with hWdef
  have hW1 : Continuous (fun s : ℝ => Real.exp (-b * (s + 1))) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_id.add continuous_const))
  have hWint : ∀ p q : ℝ, IntervalIntegrable W volume p q := by
    intro p q
    exact (hFint p q).continuousOn_mul (hker.add hW1).continuousOn
  have hincr : ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ →
      Jminus b F x₂ - Jminus b F x₁ = - ∫ s in x₁..x₂, W s := by
    intro x₁ x₂ _
    have chas1 : (∫ s in x₁..(x₁ + 1), G s) + (∫ s in (x₁ + 1)..(x₂ + 1), G s)
        = ∫ s in x₁..(x₂ + 1), G s :=
      intervalIntegral.integral_add_adjacent_intervals (hGint _ _) (hGint _ _)
    have chas2 : (∫ s in x₁..x₂, G s) + (∫ s in x₂..(x₂ + 1), G s)
        = ∫ s in x₁..(x₂ + 1), G s :=
      intervalIntegral.integral_add_adjacent_intervals (hGint _ _) (hGint _ _)
    have hdiff : Jminus b F x₂ - Jminus b F x₁
        = (∫ s in (x₁ + 1)..(x₂ + 1), G s) - (∫ s in x₁..x₂, G s) := by
      simp only [Jminus, ← hGdef]
      linarith [chas1.trans chas2.symm]
    have hsub : (∫ s in (x₁ + 1)..(x₂ + 1), G s) = ∫ σ in x₁..x₂, G (σ + 1) :=
      (intervalIntegral.integral_comp_add_right G 1).symm
    have hcongr : (∫ σ in x₁..x₂, G (σ + 1))
        = ∫ σ in x₁..x₂, - (Real.exp (-b * (σ + 1)) * F σ) :=
      intervalIntegral.integral_congr (fun σ _ => hGa σ)
    rw [hdiff, hsub, hcongr, intervalIntegral.integral_neg]
    rw [hWdef]
    have hsplit : (∫ s in x₁..x₂, (Real.exp (-b * s) + Real.exp (-b * (s + 1))) * F s)
        = (∫ s in x₁..x₂, Real.exp (-b * s) * F s)
          + ∫ s in x₁..x₂, Real.exp (-b * (s + 1)) * F s := by
      rw [← intervalIntegral.integral_add (hGint _ _)
        (hFint _ _ |>.continuousOn_mul hW1.continuousOn)]
      apply intervalIntegral.integral_congr
      intro s _; ring
    rw [hsplit, ← hGdef]
    ring
  have hincrG : ∀ x₁ x₂ : ℝ, Jminus b F x₂ - Jminus b F x₁ = - ∫ s in x₁..x₂, W s := by
    intro x₁ x₂
    rcases le_total x₁ x₂ with h | h
    · exact hincr x₁ x₂ h
    · have hh := hincr x₂ x₁ h
      rw [intervalIntegral.integral_symm x₁ x₂] at hh
      linarith [hh]
  have hfe : ∀ x : ℝ, Jminus b F (x + 1) = - Real.exp (-b) * Jminus b F x := by
    intro x
    have hsub : (∫ s in (x + 1)..(x + 1 + 1), G s) = ∫ σ in x..(x + 1), G (σ + 1) :=
      (intervalIntegral.integral_comp_add_right G 1).symm
    have hcongr : (∫ σ in x..(x + 1), G (σ + 1))
        = ∫ σ in x..(x + 1), - Real.exp (-b) * G σ := by
      apply intervalIntegral.integral_congr
      intro σ _
      simp only [hGdef]
      rw [hFanti σ]
      have : Real.exp (-b * (σ + 1)) = Real.exp (-b) * Real.exp (-b * σ) := by
        rw [← Real.exp_add]; ring_nf
      rw [this]; ring
    have hJ1 : Jminus b F (x + 1) = ∫ σ in x..(x + 1), G (σ + 1) := by
      simp only [Jminus, ← hGdef]; rw [← hsub]
    rw [hJ1, hcongr, intervalIntegral.integral_const_mul]
    simp only [Jminus, ← hGdef]
  have hmono : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ r : ℝ,
      (∀ s : ℝ, s ∈ Set.Ioo r (r + 1) → 0 < ε * F s) →
      ∀ x₁ x₂ : ℝ, r ≤ x₁ → x₁ < x₂ → x₂ ≤ r + 1 →
        ε * Jminus b F x₂ < ε * Jminus b F x₁ := by
    intro ε _ r hpos x₁ x₂ hrx₁ hlt hx₂r
    have hposI : 0 < ∫ s in x₁..x₂, ε * W s := by
      apply int_pos x₁ x₂ hlt (fun s => ε * W s) ((hWint x₁ x₂).const_mul ε)
      intro s hs
      rw [hWdef]
      have hsIoo : s ∈ Set.Ioo r (r + 1) :=
        ⟨lt_of_le_of_lt hrx₁ hs.1, lt_of_lt_of_le hs.2 hx₂r⟩
      have hεF : 0 < ε * F s := hpos s hsIoo
      have hwpos : 0 < Real.exp (-b * s) + Real.exp (-b * (s + 1)) := by positivity
      calc (0 : ℝ) < (Real.exp (-b * s) + Real.exp (-b * (s + 1))) * (ε * F s) :=
              mul_pos hwpos hεF
        _ = ε * ((Real.exp (-b * s) + Real.exp (-b * (s + 1))) * F s) := by ring
    have hWval : (∫ s in x₁..x₂, W s) = Jminus b F x₁ - Jminus b F x₂ := by
      linarith [hincrG x₁ x₂]
    have hkey : (∫ s in x₁..x₂, ε * W s) = ε * Jminus b F x₁ - ε * Jminus b F x₂ := by
      rw [intervalIntegral.integral_const_mul, hWval]; ring
    rw [hkey] at hposI
    linarith [hposI]
  have hcont : Continuous (Jminus b F) := by
    rw [Metric.continuous_iff]
    intro x₀ ε hε
    set E : ℝ := Real.exp (b * (|x₀| + 1)) with hE
    have hEpos : 0 < E := Real.exp_pos _
    set C : ℝ := 2 * E * M with hC
    have hCnn : 0 ≤ C := by positivity
    refine ⟨min 1 (ε / (C + 1)), lt_min (by norm_num) (by positivity), ?_⟩
    intro y hy
    have hy1 : |y - x₀| ≤ 1 := by
      have := lt_of_lt_of_le hy (min_le_left _ _)
      rw [Real.dist_eq] at this
      linarith [this]
    have hbound : ∀ s ∈ Set.uIoc x₀ y, ‖W s‖ ≤ C := by
      intro s hs
      rw [Set.mem_uIoc] at hs
      have hslb : x₀ - 1 ≤ s := by
        rcases hs with ⟨h1, _⟩ | ⟨h1, h2⟩
        · linarith [h1]
        · have : x₀ - 1 ≤ y := by
            rcases abs_le.mp hy1 with ⟨hl, _⟩; linarith [hl]
          linarith [this, h1]
      have hns : -b * s ≤ b * (|x₀| + 1) := by
        have hx0 : -|x₀| ≤ x₀ := neg_abs_le x₀
        nlinarith [hslb, hx0, hb, abs_nonneg x₀]
      have hexp1 : Real.exp (-b * s) ≤ E := by
        rw [hE]; exact Real.exp_le_exp.mpr hns
      have hexp2 : Real.exp (-b * (s + 1)) ≤ E := by
        have hle : -b * (s + 1) ≤ -b * s := by nlinarith [hb]
        exact le_trans (Real.exp_le_exp.mpr hle) hexp1
      have hWabs : ‖W s‖ = (Real.exp (-b * s) + Real.exp (-b * (s + 1))) * |F s| := by
        rw [hWdef, Real.norm_eq_abs, abs_mul]
        congr 1
        rw [abs_of_pos (by positivity)]
      rw [hWabs, hC]
      have hFs : |F s| ≤ M := hFbdd s
      have hw : Real.exp (-b * s) + Real.exp (-b * (s + 1)) ≤ 2 * E := by linarith [hexp1, hexp2]
      calc (Real.exp (-b * s) + Real.exp (-b * (s + 1))) * |F s|
          ≤ (2 * E) * M := by
            apply mul_le_mul hw hFs (abs_nonneg _) (by positivity)
        _ = 2 * E * M := by ring
    have hJdiff : Jminus b F y - Jminus b F x₀ = - ∫ s in x₀..y, W s := hincrG x₀ y
    have hnorm : ‖∫ s in x₀..y, W s‖ ≤ C * |y - x₀| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [Real.dist_eq]
    have hyx : Jminus b F y - Jminus b F x₀ = -(∫ s in x₀..y, W s) := hJdiff
    have : |Jminus b F y - Jminus b F x₀| = ‖∫ s in x₀..y, W s‖ := by
      rw [hyx, Real.norm_eq_abs, abs_neg]
    rw [this]
    have hyx2 : dist y x₀ < ε / (C + 1) := lt_of_lt_of_le hy (min_le_right _ _)
    rw [Real.dist_eq] at hyx2
    have hstrict : (C + 1) * |y - x₀| < (C + 1) * (ε / (C + 1)) := by
      apply mul_lt_mul_of_pos_left hyx2 (by positivity)
    have hfinal : (C + 1) * (ε / (C + 1)) = ε := by field_simp
    calc ‖∫ s in x₀..y, W s‖ ≤ C * |y - x₀| := hnorm
      _ ≤ (C + 1) * |y - x₀| := by nlinarith [abs_nonneg (y - x₀), hCnn]
      _ < (C + 1) * (ε / (C + 1)) := hstrict
      _ = ε := hfinal
  exact ⟨hcont, hfe, hmono⟩





theorem cross (J : ℝ → ℝ) (hJcont : Continuous J) (q : ℝ) (hq : 0 < q)
    (hfun : ∀ x : ℝ, J (x + 1) = -q * J x) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (r : ℝ)
    (hmono : ∀ x₁ x₂ : ℝ, r ≤ x₁ → x₁ < x₂ → x₂ ≤ r + 1 → ε * J x₁ < ε * J x₂) :
    ∃ s₀ : ℝ, s₀ ∈ Set.Ioo r (r + 1) ∧ J s₀ = 0 ∧
      (∀ x : ℝ, s₀ - 1 < x → x < s₀ → ε * J x < 0) ∧
      (∀ x : ℝ, s₀ < x → x < s₀ + 1 → 0 < ε * J x) := by
  have hεne : ε ≠ 0 := by rcases hε with h | h <;> rw [h] <;> norm_num

  have hfunε : ∀ x : ℝ, ε * J (x + 1) = -q * (ε * J x) := by
    intro x; rw [hfun x]; ring
  have hr1 : r < r + 1 := by linarith
  have hmono_r : ε * J r < ε * J (r + 1) := hmono r (r + 1) (le_refl r) hr1 (le_refl (r + 1))

  have hJr_neg : ε * J r < 0 := by
    by_contra h
    rw [not_lt] at h
    have hle : ε * J (r + 1) ≤ 0 := by
      rw [hfunε r, neg_mul]; linarith [mul_nonneg hq.le h]
    linarith [hmono_r]
  have hJr1_pos : 0 < ε * J (r + 1) := by
    rw [hfunε r, neg_mul]; linarith [mul_neg_of_pos_of_neg hq hJr_neg]

  obtain ⟨s₀, hs₀mem, hs₀0⟩ :=
    intermediate_value_Ioo hr1.le (continuous_const.mul hJcont).continuousOn
      (show (0 : ℝ) ∈ Set.Ioo (ε * J r) (ε * J (r + 1)) from ⟨hJr_neg, hJr1_pos⟩)
  have hs₀0' : ε * J s₀ = 0 := hs₀0
  have hJs0 : J s₀ = 0 := by
    rcases mul_eq_zero.mp hs₀0' with h | h
    · exact absurd h hεne
    · exact h
  have hs₀r : r < s₀ := hs₀mem.1
  have hs₀r1 : s₀ < r + 1 := hs₀mem.2

  have hsign_lo : ∀ x, r ≤ x → x < s₀ → ε * J x < 0 := by
    intro x hxr hxs
    have := hmono x s₀ hxr hxs hs₀r1.le
    rwa [hs₀0'] at this
  have hsign_hi : ∀ x, s₀ < x → x ≤ r + 1 → 0 < ε * J x := by
    intro x hxs hxr1
    have := hmono s₀ x hs₀r.le hxs hxr1
    rwa [hs₀0'] at this

  have hgoal_lo : ∀ x, s₀ - 1 < x → x < s₀ → ε * J x < 0 := by
    intro x hx1 hx2
    by_cases hxr : r ≤ x
    · exact hsign_lo x hxr hx2
    · rw [not_le] at hxr
      have hpos := hsign_hi (x + 1) (by linarith) (by linarith)
      rw [hfunε x] at hpos
      nlinarith [hpos, hq]

  have hgoal_hi : ∀ x, s₀ < x → x < s₀ + 1 → 0 < ε * J x := by
    intro x hx1 hx2
    by_cases hxr1 : x ≤ r + 1
    · exact hsign_hi x hx1 hxr1
    · rw [not_le] at hxr1
      have hneg := hsign_lo (x - 1) (by linarith) (by linarith)
      have heq : ε * J x = -q * (ε * J (x - 1)) := by
        have h := hfunε (x - 1); rwa [show x - 1 + 1 = x by ring] at h
      rw [heq]; nlinarith [hneg, hq]
  exact ⟨s₀, hs₀mem, hJs0, hgoal_lo, hgoal_hi⟩







theorem Ta_crossing (a : ℝ) (ha : a ≠ 0) (M : ℝ) (hM : 0 ≤ M) (F : ℝ → ℝ)
    (hFmeas : Measurable F) (hFbdd : ∀ x, |F x| ≤ M) (hFanti : ∀ x, F (x + 1) = - F x)
    (r : ℝ) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hFpos : ∀ x : ℝ, x ∈ Set.Ioo r (r + 1) → 0 < ε * F x) :
    Continuous (Ta a F) ∧
    (∀ x : ℝ, |Ta a F x| ≤ M) ∧
    (∀ x : ℝ, Ta a F (x + 1) = - Ta a F x) ∧
    ∃ s₀ : ℝ, ∃ ε' : ℝ, s₀ ∈ Set.Ioo r (r + 1) ∧ (ε' = 1 ∨ ε' = -1) ∧
      Ta a F s₀ = 0 ∧
      (∀ x : ℝ, s₀ - 1 < x → x < s₀ → ε' * Ta a F x < 0) ∧
      (∀ x : ℝ, s₀ < x → x < s₀ + 1 → 0 < ε' * Ta a F x) := by
  obtain ⟨_hint, hbound, hlip⟩ := conv_kernel a ha M hM F hFmeas hFbdd
  have hTabdd : ∀ x : ℝ, |Ta a F x| ≤ M := hbound
  have hLnn : (0 : ℝ) ≤ 2 * M * |a| :=
    mul_nonneg (mul_nonneg (by norm_num) hM) (abs_nonneg a)
  have hcont : Continuous (Ta a F) := by
    set L : ℝ := 2 * M * |a| with hLdef
    have hlipL : ∀ x x' : ℝ, |Ta a F x' - Ta a F x| ≤ L * |x' - x| := hlip
    rw [Metric.continuous_iff]
    intro b ε₀ hε₀
    refine ⟨ε₀ / (L + 1), by positivity, ?_⟩
    intro x hx
    rw [Real.dist_eq] at hx ⊢
    set δ : ℝ := ε₀ / (L + 1) with hδdef
    have hLp : (0 : ℝ) < L + 1 := by linarith
    have hδpos : 0 < δ := by rw [hδdef]; positivity
    have hδcancel : δ * (L + 1) = ε₀ := by
      rw [hδdef]; field_simp
    have hxb : |x - b| ≤ δ := le_of_lt hx
    have key : |Ta a F x - Ta a F b| ≤ L * |x - b| := hlipL b x
    have h1 : L * |x - b| ≤ L * δ := mul_le_mul_of_nonneg_left hxb hLnn
    nlinarith [key, h1, hδcancel, hδpos, hLnn]
  have hanti : ∀ x : ℝ, Ta a F (x + 1) = - Ta a F x :=
    antiper_T a ha M hM F hFmeas hFbdd hFanti
  refine ⟨hcont, hTabdd, hanti, ?_⟩
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · set b : ℝ := -a with hb
    have hbpos : 0 < b := by simp only [hb]; linarith
    obtain ⟨hJcont, hJfun, hJmono⟩ := J_minus b hbpos M hM F hFmeas hFbdd hFanti
    have hε' : (-ε) = 1 ∨ (-ε) = -1 := by rcases hε with h | h <;> simp [h]
    have hmono' : ∀ x₁ x₂ : ℝ, r ≤ x₁ → x₁ < x₂ → x₂ ≤ r + 1 →
        (-ε) * Jminus b F x₁ < (-ε) * Jminus b F x₂ := by
      intro x₁ x₂ h1 h2 h3
      have := hJmono ε hε r hFpos x₁ x₂ h1 h2 h3
      nlinarith [this]
    have hfunq : ∀ x : ℝ, Jminus b F (x + 1) = -(Real.exp (-b)) * Jminus b F x := by
      intro x; rw [hJfun x]
    obtain ⟨s₀, hs₀mem, hJs0, hlo, hhi⟩ :=
      cross (Jminus b F) hJcont (Real.exp (-b)) (Real.exp_pos _) hfunq (-ε) hε' r hmono'
    refine ⟨s₀, -ε, hs₀mem, hε', ?_, ?_, ?_⟩
    · rw [resum_neg a hneg M hM F hFmeas hFbdd hFanti s₀, ← hb, hJs0, mul_zero]
    · intro x hx1 hx2
      rw [resum_neg a hneg M hM F hFmeas hFbdd hFanti x, ← hb]
      have hpre : 0 < (-a) * Real.exp (-a * x) / (1 + Real.exp a) := by
        apply div_pos
        · exact mul_pos (by linarith) (Real.exp_pos _)
        · positivity
      have hJneg := hlo x hx1 hx2
      nlinarith [hpre, hJneg]
    · intro x hx1 hx2
      rw [resum_neg a hneg M hM F hFmeas hFbdd hFanti x, ← hb]
      have hpre : 0 < (-a) * Real.exp (-a * x) / (1 + Real.exp a) := by
        apply div_pos
        · exact mul_pos (by linarith) (Real.exp_pos _)
        · positivity
      have hJpos := hhi x hx1 hx2
      nlinarith [hpre, hJpos]
  · obtain ⟨hJcont, hJfun, hJmono⟩ := J_plus a hpos M hM F hFmeas hFbdd hFanti
    have hmono' : ∀ x₁ x₂ : ℝ, r ≤ x₁ → x₁ < x₂ → x₂ ≤ r + 1 →
        ε * Jplus a F x₁ < ε * Jplus a F x₂ :=
      hJmono ε hε r hFpos
    have hfunq : ∀ x : ℝ, Jplus a F (x + 1) = -(Real.exp a) * Jplus a F x := by
      intro x; rw [hJfun x]
    obtain ⟨s₀, hs₀mem, hJs0, hlo, hhi⟩ :=
      cross (Jplus a F) hJcont (Real.exp a) (Real.exp_pos _) hfunq ε hε r hmono'
    refine ⟨s₀, ε, hs₀mem, hε, ?_, ?_, ?_⟩
    · rw [resum_pos a hpos M hM F hFmeas hFbdd hFanti s₀, hJs0, mul_zero]
    · intro x hx1 hx2
      rw [resum_pos a hpos M hM F hFmeas hFbdd hFanti x]
      have hpre : 0 < a * Real.exp (-a * x) / (1 + Real.exp (-a)) := by
        apply div_pos
        · exact mul_pos hpos (Real.exp_pos _)
        · positivity
      have hJneg := hlo x hx1 hx2
      nlinarith [hpre, hJneg]
    · intro x hx1 hx2
      rw [resum_pos a hpos M hM F hFmeas hFbdd hFanti x]
      have hpre : 0 < a * Real.exp (-a * x) / (1 + Real.exp (-a)) := by
        apply div_pos
        · exact mul_pos hpos (Real.exp_pos _)
        · positivity
      have hJpos := hhi x hx1 hx2
      nlinarith [hpre, hJpos]





theorem main_induction (m : ℕ) (a : Fin (m + 1) → ℝ) (ha : ∀ j, a j ≠ 0) :
    (Measurable (Halt (finiteType m a)) ∧
      (∃ K : ℝ, ∀ x : ℝ, |Halt (finiteType m a) x| ≤ K) ∧
      (∀ x : ℝ, Halt (finiteType m a) (x + 1) = - Halt (finiteType m a) x)) ∧
    (∃ r : ℝ, ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      (∀ x : ℝ, x ∈ Set.Ioo r (r + 1) → 0 < ε * Halt (finiteType m a) x)) ∧
    (1 ≤ m → Continuous (Halt (finiteType m a)) ∧
      StrictOneCrossing (Halt (finiteType m a))) := by
  induction m with
  | zero =>
    have h0 : a 0 ≠ 0 := ha 0
    have henv : ∀ t : ℝ, |expKernel (a 0) t| ≤ |a 0| * Real.exp (-|a 0| * |t|) :=
      fun t => kernel_envelope (a 0) h0 t
    have hCpos : (0 : ℝ) < |a 0| := abs_pos.mpr h0
    obtain ⟨_, hbdd, hanti⟩ := H_bdd_antiper (expKernel (a 0)) |a 0| |a 0| hCpos hCpos henv
    have hmeas : Measurable (Halt (expKernel (a 0))) :=
      H_meas (expKernel (a 0)) (kernel_meas (a 0)) |a 0| |a 0| hCpos hCpos henv
    refine ⟨⟨hmeas, ⟨_, hbdd⟩, hanti⟩, ?_, ?_⟩
    · have hprof := Ha_profile (a 0) h0
      refine ⟨0, (if 0 < a 0 then 1 else -1), ?_, ?_⟩
      · split_ifs <;> [left; right] <;> rfl
      · intro x hx
        exact hprof.2 x hx.1 (by simpa using hx.2)
    · intro hcon
      exact absurd hcon (by omega)
  | succ m ih =>
    set a' : Fin (m + 1) → ℝ := fun i => a i.succ with ha'def
    have ha' : ∀ j, a' j ≠ 0 := fun j => ha j.succ
    have h0 : a 0 ≠ 0 := ha 0
    set g : ℝ → ℝ := finiteType m a' with hgdef
    have hft_eq : finiteType (m + 1) a = conv (expKernel (a 0)) g := rfl
    obtain ⟨hg_meas, _, hg_decay, _, _⟩ := regularity m a' ha'
    obtain ⟨C', c', hC', hc', hg_bound⟩ := hg_decay
    obtain ⟨_, hHconv⟩ :=
      H_conv (a 0) h0 g hg_meas C' c' hC' hc' hg_bound
    obtain ⟨⟨hF_meas, ⟨M, hM_bound⟩, hF_anti⟩, ⟨r, ε, hε, hF_pos⟩, _⟩ := ih a' ha'
    have hM0 : (0 : ℝ) ≤ M := le_trans (abs_nonneg _) (hM_bound 0)
    obtain ⟨hTa_cont, hTa_bdd, hTa_anti, s₀, ε', hs₀mem, hε', hTa0, hTa_lo, hTa_hi⟩ :=
      Ta_crossing (a 0) h0 M hM0 (Halt g) hF_meas hM_bound hF_anti r ε hε hF_pos
    have hHeq : Halt (finiteType (m + 1) a) = Ta (a 0) (Halt g) := by
      rw [hft_eq]; funext x; exact hHconv x
    rw [hHeq]
    refine ⟨⟨hTa_cont.measurable, ⟨M, hTa_bdd⟩, hTa_anti⟩, ?_, ?_⟩
    · exact ⟨s₀, ε', hε', fun x hx => hTa_hi x hx.1 (by simpa using hx.2)⟩
    · intro _
      refine ⟨hTa_cont, ⟨s₀, ε', hε', hTa0, hTa_lo, hTa_hi⟩⟩

end Part4
