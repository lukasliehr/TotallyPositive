import LeanCode.Vendor.E5.P8.Part8.TailMeasures
import LeanCode.Vendor.E5.Defs
open VendorE5

open MeasureTheory
open scoped BigOperators
open scoped Topology

namespace Part8

noncomputable section


def normalizedShift (Cst δ : ℝ) (g : ℝ → ℝ) : ℝ → ℝ :=
  fun x => (1 / Cst) * g (x - δ)


def normalizedProduct (γ : ℝ) (α : ℕ → ℝ) : ℝ → ℂ :=
  fun ξ => Complex.exp (-(γ : ℂ) * ξ ^ 2) * Phi α ξ


theorem h_props (g : ℝ → ℝ) (Cst γ δ : ℝ) (α : ℕ → ℝ)
    (hH1 : IsTotallyPositiveIntegrableContinuous g) (hH2 : g ≠ 0)
    (hH3 : HasExponentialDecay g) (hdata : SchoenbergData g Cst γ δ α) :
  Continuous (normalizedShift Cst δ g) ∧
    (∀ x : ℝ, 0 ≤ normalizedShift Cst δ g x) ∧
    Integrable (normalizedShift Cst δ g) ∧
    Measurable (normalizedShift Cst δ g) ∧
    (∀ ξ : ℝ, FT (normalizedShift Cst δ g) ξ = normalizedProduct γ α ξ) ∧
    ∀ x : ℝ, g x = Cst * normalizedShift Cst δ g (x + δ) := by
  have _hH2 : g ≠ 0 := hH2
  have _hH3 : HasExponentialDecay g := hH3
  rcases hH1 with ⟨hTP, hg_int, hg_cont⟩
  rcases hdata with ⟨hCst, _hγ_nonneg, _hsum, _hmul, hFT, _hFT_ne, _hbound⟩
  have hCst_ne : Cst ≠ 0 := ne_of_gt hCst
  have hCstC_ne : (Cst : ℂ) ≠ 0 := by exact_mod_cast hCst_ne
  have hshift_int : Integrable (fun x : ℝ => g (x - δ)) := hg_int.comp_sub_right δ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold normalizedShift
    fun_prop
  · intro x
    unfold normalizedShift
    have hscale_nonneg : 0 ≤ 1 / Cst := by positivity
    exact mul_nonneg hscale_nonneg (g_nonneg g hTP (x - δ))
  · unfold normalizedShift
    exact hshift_int.const_mul (1 / Cst)
  · unfold normalizedShift
    fun_prop
  · intro ξ
    have hconst :
        FT (normalizedShift Cst δ g) ξ =
          ((1 / Cst : ℝ) : ℂ) * FT (translate δ g) ξ := by
      unfold FT normalizedShift translate
      calc
        (∫ x : ℝ,
            Complex.exp (-2 * Real.pi * Complex.I * ↑ξ * ↑x) *
              ↑((1 / Cst) * g (x - δ))) =
            ∫ x : ℝ,
              ((1 / Cst : ℝ) : ℂ) *
                (Complex.exp (-2 * Real.pi * Complex.I * ↑ξ * ↑x) * ↑(g (x - δ))) := by
          apply integral_congr_ae
          filter_upwards with x
          norm_num
          ring
        _ = ((1 / Cst : ℝ) : ℂ) *
            ∫ x : ℝ, Complex.exp (-2 * Real.pi * Complex.I * ↑ξ * ↑x) * ↑(g (x - δ)) := by
          rw [integral_const_mul]
    have htrans := FT_translate g δ hg_int ξ
    calc
      FT (normalizedShift Cst δ g) ξ =
          ((1 / Cst : ℝ) : ℂ) * FT (translate δ g) ξ := hconst
      _ = ((1 / Cst : ℝ) : ℂ) *
          (Complex.exp (-2 * Real.pi * Complex.I * ↑δ * ↑ξ) * FT g ξ) := by
        rw [htrans]
      _ = normalizedProduct γ α ξ := by
        rw [hFT ξ]
        unfold normalizedProduct Phi
        set e₁ : ℂ := Complex.exp (-2 * Real.pi * Complex.I * ↑δ * ↑ξ)
        set e₂ : ℂ := Complex.exp (-(γ : ℂ) * ↑ξ ^ 2 + 2 * Real.pi * Complex.I * ↑δ * ↑ξ)
        set P : ℂ := ∏' ν : ℕ, expFactor (α ν) ξ
        have hcancel : ((1 / Cst : ℝ) : ℂ) * (Cst : ℂ) = 1 := by
          have hcast : (((1 / Cst : ℝ) : ℂ)) = 1 / (Cst : ℂ) := by norm_num
          rw [hcast]
          exact div_mul_cancel₀ (1 : ℂ) hCstC_ne
        have hexp : e₁ * e₂ = Complex.exp (-(γ : ℂ) * ↑ξ ^ 2) := by
          dsimp [e₁, e₂]
          rw [← Complex.exp_add]
          congr 1
          ring
        calc
          ((1 / Cst : ℝ) : ℂ) *
              (e₁ * ((Cst : ℂ) * e₂ * P)) =
              (((1 / Cst : ℝ) : ℂ) * (Cst : ℂ)) * (e₁ * e₂) * P := by
            ring
          _ = Complex.exp (-(γ : ℂ) * ↑ξ ^ 2) * P := by
            rw [hcancel, hexp]
            ring
  · intro x
    unfold normalizedShift
    rw [show x + δ - δ = x by ring]
    calc
      g x = 1 * g x := by ring
      _ = (Cst * (1 / Cst)) * g x := by rw [mul_one_div_cancel hCst_ne]
      _ = Cst * ((1 / Cst) * g x) := by ring

private def realizeASequence (β : ℕ → ℝ) : ℕ → ℝ
  | 0 => β 0
  | n + 1 => β n

private theorem realizeASequence_succ (β : ℕ → ℝ) (n : ℕ) :
    realizeASequence β (n + 1) = β n := by
  rfl

private theorem realizeASequence_nonzero (β : ℕ → ℝ) (hβ : ∀ j : ℕ, β j ≠ 0) :
    ∀ j : ℕ, realizeASequence β j ≠ 0 := by
  intro j
  rcases j with _ | n <;> simp [realizeASequence, hβ]

private theorem realizeASequence_summable (β : ℕ → ℝ)
    (hβsum : Summable (fun j : ℕ => (β j) ^ 2)) :
    Summable (fun j : ℕ => (realizeASequence β j) ^ 2) := by
  have htail1 : Summable (fun n : ℕ => (realizeASequence β (n + 1)) ^ 2) := by
    simpa [realizeASequence_succ] using hβsum
  exact (summable_nat_add_iff 1).1 htail1

private theorem realizeA_tailProduct_eq (β : ℕ → ℝ) (N : ℕ) (ξ : ℝ) :
    tailProduct (realizeASequence β) 0 (N + 1) ξ = headProduct β N ξ := by
  unfold tailProduct headProduct
  symm
  refine Finset.prod_bij (fun k _hk => k + 1) ?_ ?_ ?_ ?_
  · intro k hk
    simp at hk ⊢
    omega
  · intro a ha b hb hab
    omega
  · intro b hb
    simp at hb
    refine ⟨b - 1, ?_, ?_⟩
    · simp
      omega
    · omega
  · intro k hk
    rw [realizeASequence_succ]

private theorem realizeA_tail_transform (α β : ℕ → ℝ) (ν : ℕ → Measure ℝ)
    (hhead : ∀ ξ : ℝ, Filter.Tendsto (fun N : ℕ => headProduct β N ξ)
      Filter.atTop (𝓝 (Phi α ξ)))
    (hchar : TailCharfunData (realizeASequence β) ν) :
    ∀ ξ : ℝ, measureFT (ν 0) ξ = Phi α ξ := by
  intro ξ
  have htail_shift : Filter.Tendsto (fun N : ℕ => tailProduct (realizeASequence β) 0 (N + 1) ξ)
      Filter.atTop (𝓝 (measureFT (ν 0) ξ)) := by
    simpa [Function.comp_def] using (hchar 0 ξ).comp (Filter.tendsto_add_atTop_nat 1)
  have hhead_tail : Filter.Tendsto (fun N : ℕ => tailProduct (realizeASequence β) 0 (N + 1) ξ)
      Filter.atTop (𝓝 (Phi α ξ)) := by
    have hfun : (fun N : ℕ => tailProduct (realizeASequence β) 0 (N + 1) ξ) =
        (fun N : ℕ => headProduct β N ξ) := by
      funext N
      exact realizeA_tailProduct_eq β N ξ
    simpa [hfun] using hhead ξ
  exact tendsto_nhds_unique htail_shift hhead_tail

private theorem phi_probability_measure (α : ℕ → ℝ)
    (hsum : Summable (fun ν : ℕ => (α ν) ^ 2))
    (hmul : ∀ ξ : ℝ, Multipliable (fun ν : ℕ => expFactor (α ν) ξ)) :
    ∃ μ : Measure ℝ, (∃ _ : IsProbabilityMeasure μ, True) ∧
      ∀ ξ : ℝ, measureFT μ ξ = Phi α ξ := by
  classical
  by_cases hne : (nonzeroFactorSet α).Nonempty
  · by_cases hfin : (nonzeroFactorSet α).Finite
    · rcases enum_finite α hfin hne with
        ⟨M, hMpos, e, _he_strict, _he_range, he_nonzero, he_prod⟩
      cases M with
      | zero =>
          norm_num at hMpos
      | succ m =>
          let β : Fin (m + 1) → ℝ := fun i => α (e i)
          have hβ : ∀ i : Fin (m + 1), β i ≠ 0 := by
            intro i
            exact he_nonzero i
          rcases rm_basic m β hβ with
            ⟨hr_meas, hr_nonneg, _hr_bound, hr_int, hr_mass, _hr_genuine⟩
          rcases FT_density (rightNestedCentered (m + 1) β) hr_meas hr_nonneg hr_int with
            ⟨μ, _hμfin, hμmass, hμFT⟩
          have hprob : IsProbabilityMeasure μ := by
            exact isProbabilityMeasure_iff.mpr (by
              rw [hμmass, hr_mass]
              norm_num)
          refine ⟨μ, ⟨hprob, trivial⟩, ?_⟩
          intro ξ
          calc
            measureFT μ ξ = FT (rightNestedCentered (m + 1) β) ξ := hμFT ξ
            _ = ∏ i : Fin (m + 1), expFactor (β i) ξ := rm_FT (m + 1) β (by omega) hβ ξ
            _ = Phi α ξ := by
              symm
              simpa [β] using he_prod ξ
    · have hinf : (nonzeroFactorSet α).Infinite := hfin
      rcases enum_infinite α hsum hmul hinf with
        ⟨e, _he_strict, _he_range, henum⟩
      let β : ℕ → ℝ := fun j => α (e j)
      change (∀ j : ℕ, β j ≠ 0) ∧
          Summable (fun j : ℕ => (β j) ^ 2) ∧
          (∀ ξ : ℝ, Filter.Tendsto (fun N : ℕ => headProduct β N ξ)
            Filter.atTop (𝓝 (Phi α ξ))) ∧
          (∀ m : ℕ, ∀ ξ : ℝ, tailProduct β m m ξ = tailProduct β m m ξ) at henum
      rcases henum with ⟨hβ_nonzero, hβ_sum, hβ_head, _hβ_tail_refl⟩
      let αp : ℕ → ℝ := realizeASequence β
      have hαp_nonzero : ∀ j : ℕ, αp j ≠ 0 := by
        intro j
        simpa [αp] using realizeASequence_nonzero β hβ_nonzero j
      have hαp_sum : Summable (fun j : ℕ => (αp j) ^ 2) := by
        simpa [αp] using realizeASequence_summable β hβ_sum
      rcases tail_limit αp hαp_nonzero hαp_sum with ⟨ν, v, hνlim⟩
      have hchar : TailCharfunData αp ν := tail_charfun αp ν v hνlim
      rcases hνlim.2.2.1 0 with ⟨hνprob0, _htriv⟩
      refine ⟨ν 0, ⟨hνprob0, trivial⟩, ?_⟩
      intro ξ
      exact realizeA_tail_transform α β ν hβ_head (by simpa [αp] using hchar) ξ
  · have hJempty : nonzeroFactorSet α = ∅ := by
      ext ν
      constructor
      · intro hν
        exact False.elim (hne ⟨ν, hν⟩)
      · intro hν
        exact False.elim hν
    have hPhi := enum_empty α hJempty
    let μ : Measure ℝ := Measure.dirac (0 : ℝ)
    refine ⟨μ, ⟨inferInstance, trivial⟩, ?_⟩
    intro ξ
    calc
      measureFT μ ξ = 1 := by
        unfold measureFT μ
        rw [MeasureTheory.integral_dirac]
        simp
      _ = Phi α ξ := by
        symm
        exact hPhi ξ


theorem realize_a (g : ℝ → ℝ) (Cst γ δ : ℝ) (α : ℕ → ℝ)
    (hH1 : IsTotallyPositiveIntegrableContinuous g) (hH2 : g ≠ 0)
    (hH3 : HasExponentialDecay g) (hdata : SchoenbergData g Cst γ δ α)
    (hγ : 0 < γ) :
  ∀ x : ℝ, 0 < normalizedShift Cst δ g x := by
  classical
  rcases h_props g Cst γ δ α hH1 hH2 hH3 hdata with
    ⟨hh_cont, hh_nonneg, hh_int, hh_meas, hh_FT, _hg_shift⟩
  rcases hdata with ⟨_hCst, _hγ_nonneg, hsum, hmul, _hFTg, _hFT_ne, _hbound⟩
  rcases phi_probability_measure α hsum hmul with ⟨μ, ⟨hμprob, _hμtrivial⟩, hμFT⟩
  letI : IsProbabilityMeasure μ := hμprob
  let G : ℝ → ℝ := gaussianKernel γ
  let f : ℝ → ℝ := kernelMeasureConv G μ
  rcases gaussian γ hγ with
    ⟨hG_cont, hG_pos, hG_int, _hG_mass, hG_bound_lip, hG_FT⟩
  rcases hG_bound_lip with ⟨A, L, _hA, hL, hG_bound, hG_lip⟩
  have hG_nonneg : ∀ x : ℝ, 0 ≤ G x := by
    intro x
    exact (hG_pos x).le
  have hG_meas : Measurable G := hG_cont.measurable
  have hconv_basic := convmeas_basic G μ A hG_meas hG_nonneg hG_int hG_bound
  have hf_cont : Continuous f := by
    have hconv_lip : ∀ x x' : ℝ, |f x - f x'| ≤ L * |x - x'| := by
      intro x x'
      by_cases hxx : x = x'
      · subst x'
        simp [f]
      · have hdist_pos : 0 < |x - x'| := abs_pos.mpr (sub_ne_zero.mpr hxx)
        have hω : 0 ≤ L * |x - x'| := mul_nonneg hL.le (abs_nonneg _)
        simpa [f] using convmeas_cont G μ A (L * |x - x'|) |x - x'|
          hG_meas hG_nonneg hG_int hG_bound hω hdist_pos
          (by
            intro s s' hss'
            calc
              |G s - G s'| ≤ L * |s - s'| := hG_lip s s'
              _ ≤ L * |x - x'| := mul_le_mul_of_nonneg_left hss' hL.le)
          x x' le_rfl
    have hLip : LipschitzWith ⟨L, hL.le⟩ f := by
      apply LipschitzWith.of_dist_le_mul
      intro x x'
      rw [Real.dist_eq, Real.dist_eq]
      change |f x - f x'| ≤ L * |x - x'|
      exact hconv_lip x x'
    exact hLip.continuous
  have hf_meas : Measurable f := by
    simpa [f] using hconv_basic.2.1
  have hf_nonneg : ∀ x : ℝ, 0 ≤ f x := by
    intro x
    simpa [f] using (hconv_basic.1 x).2.1
  have hf_int : Integrable f := by
    simpa [f] using hconv_basic.2.2.1
  have hFT_eq : ∀ ξ : ℝ, FT (normalizedShift Cst δ g) ξ = FT f ξ := by
    intro ξ
    have hconvFT : FT f ξ = FT G ξ * measureFT μ ξ := by
      simpa [f] using convmeas_FT G μ A hG_meas hG_nonneg hG_int hG_bound ξ
    calc
      FT (normalizedShift Cst δ g) ξ = normalizedProduct γ α ξ := hh_FT ξ
      _ = Complex.exp (-(γ : ℂ) * ξ ^ 2) * Phi α ξ := by rfl
      _ = FT G ξ * measureFT μ ξ := by
        rw [hG_FT ξ, hμFT ξ]
      _ = FT f ξ := by
        rw [hconvFT]
  have hae : normalizedShift Cst δ g =ᵐ[volume] f := by
    exact fn_unique (normalizedShift Cst δ g) f
      hh_meas hf_meas hh_nonneg hf_nonneg hh_int hf_int hFT_eq
  have hpoint : ∀ x : ℝ, normalizedShift Cst δ g x = f x := by
    exact cont_ae (normalizedShift Cst δ g) f hh_cont hf_cont hae
  rcases mass_window μ with ⟨n, hn⟩
  have hK_int : ∀ x : ℝ, Integrable (fun y : ℝ => G (x - y)) μ := by
    intro x
    exact (hconv_basic.1 x).1
  have hconv_pos := convmeas_pos G μ (n : ℝ) ((n : ℝ) + 1)
    hG_cont hG_nonneg hK_int (by norm_num) hn
  intro x
  rw [hpoint x]
  exact hconv_pos.2.2 hG_pos x


theorem realize_b (g : ℝ → ℝ) (Cst γ δ : ℝ) (α : ℕ → ℝ)
    (hH1 : IsTotallyPositiveIntegrableContinuous g) (hH2 : g ≠ 0)
    (hH3 : HasExponentialDecay g) (hdata : SchoenbergData g Cst γ δ α)
    (hγ : γ = 0) (hfin : (nonzeroFactorSet α).Finite) :
  ∃ M : ℕ, 2 ≤ M ∧ ∃ β : Fin M → ℝ,
    (∀ j, β j ≠ 0) ∧
      ∀ x : ℝ, normalizedShift Cst δ g x = rightNestedCentered M β x := by
  classical
  rcases h_props g Cst γ δ α hH1 hH2 hH3 hdata with
    ⟨hh_cont, hh_nonneg, hh_int, hh_meas, hh_FT, _hg_shift⟩
  let h : ℝ → ℝ := normalizedShift Cst δ g
  by_cases hne : (nonzeroFactorSet α).Nonempty
  · rcases enum_finite α hfin hne with
      ⟨M, hMpos, e, _he_strict, _he_range, he_nonzero, he_prod⟩
    let β : Fin M → ℝ := fun i => α (e i)
    have hβ : ∀ i : Fin M, β i ≠ 0 := by
      intro i
      exact he_nonzero i
    have hFTprod : ∀ ξ : ℝ, FT h ξ = ∏ i : Fin M, expFactor (β i) ξ := by
      intro ξ
      calc
        FT h ξ = normalizedProduct γ α ξ := hh_FT ξ
        _ = Phi α ξ := by simp [normalizedProduct, hγ]
        _ = ∏ i : Fin M, expFactor (β i) ξ := by simpa [β] using he_prod ξ
    cases M with
    | zero =>
        norm_num at hMpos
    | succ M1 =>
        cases M1 with
        | zero =>
            have hβ0 : β 0 ≠ 0 := hβ 0
            have hFTone : ∀ ξ : ℝ, FT h ξ = expFactor (β 0) ξ := by
              intro ξ
              simpa [Fin.prod_univ_one] using hFTprod ξ
            exact False.elim
              (one_factor (β 0) hβ0 ⟨h, hh_cont, hh_nonneg, hh_int, hFTone⟩)
        | succ n =>
            have hMge : 2 ≤ Nat.succ (Nat.succ n) := by omega
            have hbasic := rm_basic (n + 1) β hβ
            rcases hbasic with
              ⟨hf_meas, hf_nonneg, _hf_bound, hf_int, _hf_mass, _hf_genuine⟩
            rcases rm_cont (Nat.succ (Nat.succ n)) β (by omega) hβ with
              ⟨_Λ, _hΛ, _hLip, hf_cont⟩
            have hFTf : ∀ ξ : ℝ,
                FT (rightNestedCentered (Nat.succ (Nat.succ n)) β) ξ =
                  ∏ i : Fin (Nat.succ (Nat.succ n)), expFactor (β i) ξ := by
              intro ξ
              exact rm_FT (Nat.succ (Nat.succ n)) β (by omega) hβ ξ
            have hae : h =ᵐ[volume] rightNestedCentered (Nat.succ (Nat.succ n)) β := by
              exact fn_unique h (rightNestedCentered (Nat.succ (Nat.succ n)) β)
                hh_meas hf_meas hh_nonneg hf_nonneg hh_int hf_int
                (fun ξ => by rw [hFTprod ξ, hFTf ξ])
            have hpoint :
                ∀ x : ℝ, h x = rightNestedCentered (Nat.succ (Nat.succ n)) β x :=
              cont_ae h (rightNestedCentered (Nat.succ (Nat.succ n)) β)
                hh_cont hf_cont hae
            refine ⟨Nat.succ (Nat.succ n), hMge, β, hβ, ?_⟩
            intro x
            exact hpoint x
  · have hJempty : nonzeroFactorSet α = ∅ := by
      ext ν
      constructor
      · intro hν
        exact False.elim (hne ⟨ν, hν⟩)
      · intro hν
        exact False.elim hν
    have hPhi := enum_empty α hJempty
    have hFTone : ∀ ξ : ℝ, FT h ξ = 1 := by
      intro ξ
      calc
        FT h ξ = normalizedProduct γ α ξ := hh_FT ξ
        _ = Phi α ξ := by simp [normalizedProduct, hγ]
        _ = 1 := hPhi ξ
    exact False.elim (dirac_exclusion ⟨h, hh_meas, hh_nonneg, hh_int, hFTone⟩)

private def realizeCSequence (β : ℕ → ℝ) : ℕ → ℝ
  | 0 => β 0
  | 1 => β 1
  | 2 => β 0
  | n + 3 => β (n + 2)

private theorem realizeCSequence_add_three (β : ℕ → ℝ) (n : ℕ) :
    realizeCSequence β (n + 3) = β (n + 2) := by
  rfl

private theorem realizeCSequence_nonzero (β : ℕ → ℝ) (hβ : ∀ j : ℕ, β j ≠ 0) :
    ∀ j : ℕ, realizeCSequence β j ≠ 0 := by
  intro j
  rcases j with _ | _ | _ | n <;> simp [realizeCSequence, hβ]

private theorem realizeCSequence_summable (β : ℕ → ℝ)
    (hβsum : Summable (fun j : ℕ => (β j) ^ 2)) :
    Summable (fun j : ℕ => (realizeCSequence β j) ^ 2) := by
  have htail : Summable (fun n : ℕ => (β (n + 2)) ^ 2) := by
    exact (summable_nat_add_iff 2).2 hβsum
  have htail3 : Summable (fun n : ℕ => (realizeCSequence β (n + 3)) ^ 2) := by
    simpa [realizeCSequence_add_three] using htail
  exact (summable_nat_add_iff 3).1 htail3

private theorem realizeC_tailProduct_eq (β : ℕ → ℝ) (N : ℕ) (ξ : ℝ) :
    tailProduct (realizeCSequence β) 2 (N + 2) ξ =
      ∏ k ∈ Finset.range N, expFactor (β (k + 2)) ξ := by
  unfold tailProduct
  symm
  refine Finset.prod_bij (fun k _hk => k + 3) ?_ ?_ ?_ ?_
  · intro k hk
    simp at hk ⊢
    omega
  · intro a ha b hb hab
    omega
  · intro b hb
    simp at hb
    refine ⟨b - 3, ?_, ?_⟩
    · simp
      omega
    · omega
  · intro k hk
    rw [realizeCSequence_add_three]

private theorem realizeC_head_tail (β : ℕ → ℝ) (N : ℕ) (ξ : ℝ) :
    headProduct β (N + 1) ξ =
      expFactor (realizeCSequence β 0) ξ * expFactor (realizeCSequence β 1) ξ *
        tailProduct (realizeCSequence β) 2 (N + 2) ξ := by
  have htail := realizeC_tailProduct_eq β N ξ
  unfold headProduct
  rw [htail]
  calc
    (∏ j ∈ Finset.range (N + 1 + 1), expFactor (β j) ξ) =
        ∏ j ∈ Finset.range (2 + N), expFactor (β j) ξ := by
      congr 2
      omega
    _ = (∏ j ∈ Finset.range 2, expFactor (β j) ξ) *
        ∏ j ∈ Finset.range N, expFactor (β (2 + j)) ξ := by
      rw [Finset.prod_range_add]
    _ = expFactor (β 0) ξ * expFactor (β 1) ξ *
        ∏ j ∈ Finset.range N, expFactor (β (j + 2)) ξ := by
      have hrange2 : (∏ j ∈ Finset.range 2, expFactor (β j) ξ) =
          expFactor (β 0) ξ * expFactor (β 1) ξ := by
        norm_num [Finset.prod_range_succ]
      rw [hrange2]
      congr 1
      apply Finset.prod_congr rfl
      intro j _hj
      congr 2
      omega
    _ = expFactor (realizeCSequence β 0) ξ * expFactor (realizeCSequence β 1) ξ *
        ∏ j ∈ Finset.range N, expFactor (β (j + 2)) ξ := by
      rfl

private theorem realizeC_prod_limit (α β : ℕ → ℝ) (ν : ℕ → Measure ℝ)
    (hhead : ∀ ξ : ℝ, Filter.Tendsto (fun N : ℕ => headProduct β N ξ)
      Filter.atTop (𝓝 (Phi α ξ)))
    (hchar : TailCharfunData (realizeCSequence β) ν) :
    ∀ ξ : ℝ,
      Phi α ξ =
        expFactor (realizeCSequence β 0) ξ * expFactor (realizeCSequence β 1) ξ *
          measureFT (ν 2) ξ := by
  intro ξ
  let e01 : ℂ := expFactor (realizeCSequence β 0) ξ * expFactor (realizeCSequence β 1) ξ
  have hhead_shift : Filter.Tendsto (fun N : ℕ => headProduct β (N + 1) ξ)
      Filter.atTop (𝓝 (Phi α ξ)) := by
    simpa [Function.comp_def] using (hhead ξ).comp (Filter.tendsto_add_atTop_nat 1)
  have htail_shift : Filter.Tendsto (fun N : ℕ => tailProduct (realizeCSequence β) 2 (N + 2) ξ)
      Filter.atTop (𝓝 (measureFT (ν 2) ξ)) := by
    simpa [Function.comp_def] using (hchar 2 ξ).comp (Filter.tendsto_add_atTop_nat 2)
  have hprod_tail : Filter.Tendsto
      (fun N : ℕ => e01 * tailProduct (realizeCSequence β) 2 (N + 2) ξ)
      Filter.atTop (𝓝 (e01 * measureFT (ν 2) ξ)) := by
    exact Filter.Tendsto.const_mul e01 htail_shift
  have hhead_prod : Filter.Tendsto
      (fun N : ℕ => e01 * tailProduct (realizeCSequence β) 2 (N + 2) ξ)
      Filter.atTop (𝓝 (Phi α ξ)) := by
    have hfun : (fun N : ℕ => headProduct β (N + 1) ξ) =
        (fun N : ℕ => e01 * tailProduct (realizeCSequence β) 2 (N + 2) ξ) := by
      funext N
      simpa [e01, mul_assoc] using realizeC_head_tail β N ξ
    simpa [hfun] using hhead_shift
  have hlim := tendsto_nhds_unique hhead_prod hprod_tail
  simpa [e01, mul_assoc] using hlim


theorem realize_c (g : ℝ → ℝ) (Cst γ δ : ℝ) (α : ℕ → ℝ)
    (hH1 : IsTotallyPositiveIntegrableContinuous g) (hH2 : g ≠ 0)
    (hH3 : HasExponentialDecay g) (hdata : SchoenbergData g Cst γ δ α)
    (hγ : γ = 0) (hinf : (nonzeroFactorSet α).Infinite) :
  ∃ (α' : ℕ → ℝ) (ν : ℕ → Measure ℝ),
    TailLawData α' ν ∧
      let r := rightNestedCentered 2 (fun j : Fin 2 => α' j)
      ∀ x : ℝ, normalizedShift Cst δ g x = kernelMeasureConv r (ν 2) x := by
  classical
  rcases h_props g Cst γ δ α hH1 hH2 hH3 hdata with
    ⟨hh_cont, hh_nonneg, hh_int, hh_meas, hh_FT, _hg_shift⟩
  rcases hdata with ⟨_hCst, _hγ_nonneg, hsum, hmul, _hFTg, _hFT_ne, _hbound⟩
  rcases enum_infinite α hsum hmul hinf with
    ⟨e, _he_strict, _he_range, henum⟩
  let β : ℕ → ℝ := fun j => α (e j)
  change (∀ j : ℕ, β j ≠ 0) ∧
      Summable (fun j : ℕ => (β j) ^ 2) ∧
      (∀ ξ : ℝ, Filter.Tendsto (fun N : ℕ => headProduct β N ξ)
        Filter.atTop (𝓝 (Phi α ξ))) ∧
      (∀ m : ℕ, ∀ ξ : ℝ, tailProduct β m m ξ = tailProduct β m m ξ) at henum
  rcases henum with ⟨hβ_nonzero, hβ_sum, hβ_head, _hβ_tail_refl⟩
  let αp : ℕ → ℝ := realizeCSequence β
  have hαp_nonzero : ∀ j : ℕ, αp j ≠ 0 := by
    intro j
    simpa [αp] using realizeCSequence_nonzero β hβ_nonzero j
  have hαp_sum : Summable (fun j : ℕ => (αp j) ^ 2) := by
    simpa [αp] using realizeCSequence_summable β hβ_sum
  rcases tail_limit αp hαp_nonzero hαp_sum with ⟨ν, v, hνlim⟩
  have htailLaw : TailLawData αp ν := tail_law_data_of_limit αp ν v hνlim
  have hchar : TailCharfunData αp ν := by
    exact tail_charfun αp ν v hνlim
  let β2 : Fin 2 → ℝ := fun j => αp j
  let r : ℝ → ℝ := rightNestedCentered 2 β2
  let f : ℝ → ℝ := kernelMeasureConv r (ν 2)
  have hβ2_nonzero : ∀ j : Fin 2, β2 j ≠ 0 := by
    intro j
    exact hαp_nonzero j
  rcases htailLaw.2.2.1 2 with ⟨hνprob2, _hνtrivial⟩
  letI : IsProbabilityMeasure (ν 2) := hνprob2
  have hr_basic := rm_basic 1 β2 hβ2_nonzero
  rcases hr_basic with ⟨hr_meas, hr_nonneg, ⟨M, hr_bound⟩, hr_int, _hr_mass, _hr_genuine⟩
  have hconv_basic := convmeas_basic r (ν 2) M
    (by simpa [r] using hr_meas)
    (by intro x; simpa [r] using hr_nonneg x)
    (by simpa [r] using hr_int)
    (by intro x; simpa [r] using hr_bound x)
  rcases rm_cont 2 β2 (by norm_num) hβ2_nonzero with ⟨Λ, hΛ, hr_lip, _hr_cont⟩
  have hf_cont : Continuous f := by
    have hconv_lip : ∀ x x' : ℝ, |f x - f x'| ≤ Λ * |x - x'| := by
      intro x x'
      by_cases hxx : x = x'
      · subst x'
        simp [f]
      · have hdist_pos : 0 < |x - x'| := abs_pos.mpr (sub_ne_zero.mpr hxx)
        have hω : 0 ≤ Λ * |x - x'| := mul_nonneg hΛ.le (abs_nonneg _)
        simpa [f] using convmeas_cont r (ν 2) M (Λ * |x - x'|) |x - x'|
          (by simpa [r] using hr_meas)
          (by intro s; simpa [r] using hr_nonneg s)
          (by simpa [r] using hr_int)
          (by intro s; simpa [r] using hr_bound s)
          hω hdist_pos
          (by
            intro s s' hss'
            calc
              |r s - r s'| = |rightNestedCentered 2 β2 s - rightNestedCentered 2 β2 s'| := by
                rfl
              _ ≤ Λ * |s - s'| := hr_lip s s'
              _ ≤ Λ * |x - x'| := mul_le_mul_of_nonneg_left hss' hΛ.le)
          x x' le_rfl
    have hLip : LipschitzWith ⟨Λ, hΛ.le⟩ f := by
      apply LipschitzWith.of_dist_le_mul
      intro x x'
      rw [Real.dist_eq, Real.dist_eq]
      change |f x - f x'| ≤ Λ * |x - x'|
      exact hconv_lip x x'
    exact hLip.continuous
  have hf_meas : Measurable f := by
    simpa [f] using hconv_basic.2.1
  have hf_nonneg : ∀ x : ℝ, 0 ≤ f x := by
    intro x
    simpa [f] using (hconv_basic.1 x).2.1
  have hf_int : Integrable f := by
    simpa [f] using hconv_basic.2.2.1
  have hPhi_prod := realizeC_prod_limit α β ν hβ_head (by simpa [αp] using hchar)
  have hFT_eq : ∀ ξ : ℝ, FT (normalizedShift Cst δ g) ξ = FT f ξ := by
    intro ξ
    have hconvFT : FT f ξ = FT r ξ * measureFT (ν 2) ξ := by
      simpa [f] using convmeas_FT r (ν 2) M
        (by simpa [r] using hr_meas)
        (by intro s; simpa [r] using hr_nonneg s)
        (by simpa [r] using hr_int)
        (by intro s; simpa [r] using hr_bound s) ξ
    have hrFT : FT r ξ = expFactor (αp 0) ξ * expFactor (αp 1) ξ := by
      have h0 := rm_FT 2 β2 (by norm_num) hβ2_nonzero ξ
      have hprod : (∏ j : Fin 2, expFactor (β2 j) ξ) =
          expFactor (αp 0) ξ * expFactor (αp 1) ξ := by
        simp [β2, Fin.prod_univ_two]
      rw [h0, hprod]
    calc
      FT (normalizedShift Cst δ g) ξ = normalizedProduct γ α ξ := hh_FT ξ
      _ = Phi α ξ := by simp [normalizedProduct, hγ]
      _ = expFactor (αp 0) ξ * expFactor (αp 1) ξ * measureFT (ν 2) ξ := by
        simpa [αp, mul_assoc] using hPhi_prod ξ
      _ = FT f ξ := by
        rw [hconvFT, hrFT]
  have hae : normalizedShift Cst δ g =ᵐ[volume] f := by
    exact fn_unique (normalizedShift Cst δ g) f
      hh_meas hf_meas hh_nonneg hf_nonneg hh_int hf_int hFT_eq
  have hpoint : ∀ x : ℝ, normalizedShift Cst δ g x = f x := by
    exact cont_ae (normalizedShift Cst δ g) f hh_cont hf_cont hae
  refine ⟨αp, ν, htailLaw, ?_⟩
  dsimp
  intro x
  simpa [f, r, β2] using hpoint x


theorem g_pos (g : ℝ → ℝ) (Cst γ δ : ℝ) (α : ℕ → ℝ)
    (hH1 : IsTotallyPositiveIntegrableContinuous g) (hH2 : g ≠ 0)
    (hH3 : HasExponentialDecay g) (hdata : SchoenbergData g Cst γ δ α) :
  PositivityTrichotomy g := by
  have hdata_copy := hdata
  rcases h_props g Cst γ δ α hH1 hH2 hH3 hdata_copy with
    ⟨_hh_cont, _hh_nonneg, _hh_int, _hh_meas, _hh_FT, hg_shift⟩
  rcases hdata with ⟨hCst, hγ_nonneg, _hsum, _hmul, _hFT, _hFT_ne, _hbound⟩
  by_cases hγ_pos : 0 < γ
  · have hreal := realize_a g Cst γ δ α hH1 hH2 hH3 hdata_copy hγ_pos
    right
    right
    intro x
    rw [hg_shift x]
    exact mul_pos hCst (hreal (x + δ))
  · have hγ_zero : γ = 0 := le_antisymm (not_lt.mp hγ_pos) hγ_nonneg
    by_cases hfin : (nonzeroFactorSet α).Finite
    · rcases realize_b g Cst γ δ α hH1 hH2 hH3 hdata_copy hγ_zero hfin with
        ⟨M, hM, β, hβ, hreal⟩
      rcases rm_pos M β hM hβ with hright | hleft | hall
      · rcases hright with ⟨u, hu⟩
        left
        refine ⟨u - δ, ?_⟩
        intro x hx
        rw [hg_shift x, hreal (x + δ)]
        exact mul_pos hCst (hu (x + δ) (by linarith))
      · rcases hleft with ⟨u, hu⟩
        right
        left
        refine ⟨u - δ, ?_⟩
        intro x hx
        rw [hg_shift x, hreal (x + δ)]
        exact mul_pos hCst (hu (x + δ) (by linarith))
      · right
        right
        intro x
        rw [hg_shift x, hreal (x + δ)]
        exact mul_pos hCst (hall (x + δ))
    · have hinf : (nonzeroFactorSet α).Infinite := by
        exact hfin
      rcases realize_c g Cst γ δ α hH1 hH2 hH3 hdata_copy hγ_zero hinf with
        ⟨α', ν, hν, hreal⟩
      let β : Fin 2 → ℝ := fun j => α' j
      let r : ℝ → ℝ := rightNestedCentered 2 β
      have hβ : ∀ j, β j ≠ 0 := by
        intro j
        exact hν.1 j
      rcases hν.2.2.1 2 with ⟨hνprob, _hνtrivial⟩
      letI : IsProbabilityMeasure (ν 2) := hνprob
      rcases mass_window (ν 2) with ⟨n, hn⟩
      rcases rm_cont 2 β (by norm_num) hβ with ⟨_Λ, _hΛ, _hLip, hr_cont⟩
      have hr_nonneg : ∀ x : ℝ, 0 ≤ r x := by
        exact (rm_basic 1 β hβ).2.1
      have hr_basic := rm_basic 1 β hβ
      rcases hr_basic.2.2.1 with ⟨M, hr_bound⟩
      have hconv_basic := convmeas_basic r (ν 2) M (by simpa [r] using hr_basic.1)
        hr_nonneg (by simpa [r] using hr_basic.2.2.2.1)
        (by simpa [r] using hr_bound)
      have hK_int : ∀ x : ℝ, Integrable (fun y : ℝ => r (x - y)) (ν 2) := by
        intro x
        exact (hconv_basic.1 x).1
      have hconv_pos := convmeas_pos r (ν 2) (n : ℝ) ((n : ℝ) + 1)
        hr_cont hr_nonneg hK_int (by norm_num) hn
      rcases rm_pos 2 β (by norm_num) hβ with hright | hleft | hall
      · rcases hright with ⟨u, hu⟩
        left
        refine ⟨u + ((n : ℝ) + 1) - δ, ?_⟩
        intro x hx
        rw [hg_shift x]
        have hreal_x : normalizedShift Cst δ g (x + δ) =
            kernelMeasureConv r (ν 2) (x + δ) := by
          simpa [r, β] using hreal (x + δ)
        rw [hreal_x]
        exact mul_pos hCst (hconv_pos.1 u hu (x + δ) (by linarith))
      · rcases hleft with ⟨u, hu⟩
        right
        left
        refine ⟨u + (n : ℝ) - δ, ?_⟩
        intro x hx
        rw [hg_shift x]
        have hreal_x : normalizedShift Cst δ g (x + δ) =
            kernelMeasureConv r (ν 2) (x + δ) := by
          simpa [r, β] using hreal (x + δ)
        rw [hreal_x]
        exact mul_pos hCst (hconv_pos.2.1 u hu (x + δ) (by linarith))
      · right
        right
        intro x
        rw [hg_shift x]
        have hreal_x : normalizedShift Cst δ g (x + δ) =
            kernelMeasureConv r (ν 2) (x + δ) := by
          simpa [r, β] using hreal (x + δ)
        rw [hreal_x]
        exact mul_pos hCst (hconv_pos.2.2 (by simpa [r] using hall) (x + δ))


def deconvolutionChain (α' : ℕ → ℝ) (ν : ℕ → Measure ℝ) : ℕ → ℝ → ℝ :=
  let r := rightNestedCentered 2 (fun j : Fin 2 => α' j)
  fun m => if 2 ≤ m then kernelMeasureConv r (ν m) else kernelMeasureConv r (ν 2)


def deconvolutionSigma (α' : ℕ → ℝ) : ℕ → ℝ :=
  fun m => if 3 ≤ m then α' m else 1


theorem Fm_props (α' : ℕ → ℝ) (ν : ℕ → Measure ℝ)
    (hν : TailLawData α' ν) :
  ∀ m : ℕ, 2 ≤ m →
    Measurable (deconvolutionChain α' ν m) ∧
      (∀ x : ℝ, 0 ≤ deconvolutionChain α' ν m x) ∧
      (∃ M : ℝ, ∀ x : ℝ, deconvolutionChain α' ν m x ≤ M) ∧
      Continuous (deconvolutionChain α' ν m) ∧
      Integrable (deconvolutionChain α' ν m) ∧
      (∫ x : ℝ, deconvolutionChain α' ν m x) = 1 ∧
      LatticeDominated (deconvolutionChain α' ν m) := by
  intro m hm
  let β : Fin 2 → ℝ := fun j => α' j
  let r : ℝ → ℝ := rightNestedCentered 2 β
  have hβ : ∀ j, β j ≠ 0 := by
    intro j
    exact hν.1 j
  rcases hν.2.2.1 m with ⟨hprobνm, _⟩
  letI : IsProbabilityMeasure (ν m) := hprobνm
  have hbasic_r := rm_basic 1 β hβ
  rcases hbasic_r with ⟨hr_meas, hr_nonneg, ⟨M, hr_bound⟩, hr_int, hr_mass, _⟩
  have hconv_basic := convmeas_basic r (ν m) M
    (by simpa [r] using hr_meas)
    (by intro x; simpa [r] using hr_nonneg x)
    (by simpa [r] using hr_int)
    (by intro x; simpa [r] using hr_bound x)
  rcases rm_cont 2 β (by norm_num) hβ with ⟨Λ, hΛ, hr_lip, _hr_cont⟩
  have hconv_lip : ∀ x x' : ℝ,
      |kernelMeasureConv r (ν m) x - kernelMeasureConv r (ν m) x'| ≤ Λ * |x - x'| := by
    intro x x'
    by_cases hxx : x = x'
    · subst x'
      simp
    · have hdist_pos : 0 < |x - x'| := abs_pos.mpr (sub_ne_zero.mpr hxx)
      have hω : 0 ≤ Λ * |x - x'| := mul_nonneg hΛ.le (abs_nonneg _)
      exact convmeas_cont r (ν m) M (Λ * |x - x'|) |x - x'|
        (by simpa [r] using hr_meas)
        (by intro s; simpa [r] using hr_nonneg s)
        (by simpa [r] using hr_int)
        (by intro s; simpa [r] using hr_bound s)
        hω hdist_pos
        (by
          intro s s' hss'
          calc
            |r s - r s'| = |rightNestedCentered 2 β s - rightNestedCentered 2 β s'| := by
              rfl
            _ ≤ Λ * |s - s'| := hr_lip s s'
            _ ≤ Λ * |x - x'| := mul_le_mul_of_nonneg_left hss' hΛ.le)
        x x' le_rfl
  have hconv_cont : Continuous (kernelMeasureConv r (ν m)) := by
    have hLip : LipschitzWith ⟨Λ, hΛ.le⟩ (kernelMeasureConv r (ν m)) := by
      apply LipschitzWith.of_dist_le_mul
      intro x x'
      rw [Real.dist_eq, Real.dist_eq]
      change |kernelMeasureConv r (ν m) x - kernelMeasureConv r (ν m) x'| ≤
        Λ * |x - x'|
      exact hconv_lip x x'
    exact hLip.continuous
  rcases rm_decay 2 β (by norm_num) hβ with ⟨C, c, hC, hc, hr_decay⟩
  have hlat : LatticeDominated (kernelMeasureConv r (ν m)) := by
    exact (convmeas_lattice r (ν m) C c hC hc (by
      intro x
      simpa [r] using hr_decay x)).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [deconvolutionChain, r, β, hm] using hconv_basic.2.1
  · intro x
    simpa [deconvolutionChain, r, β, hm] using (hconv_basic.1 x).2.1
  · refine ⟨M, ?_⟩
    intro x
    simpa [deconvolutionChain, r, β, hm] using (hconv_basic.1 x).2.2
  · simpa [deconvolutionChain, r, β, hm] using hconv_cont
  · simpa [deconvolutionChain, r, β, hm] using hconv_basic.2.2.1
  · calc
      (∫ x : ℝ, deconvolutionChain α' ν m x) =
          ∫ x : ℝ, kernelMeasureConv r (ν m) x := by
        simp [deconvolutionChain, r, β, hm]
      _ = ∫ x : ℝ, r x := hconv_basic.2.2.2
      _ = 1 := by
        simpa [r] using hr_mass
  · simpa [deconvolutionChain, r, β, hm] using hlat

private theorem kernelLaw_eq_centeredExp_density (α : ℝ) (μ : Measure ℝ)
    (hα : α ≠ 0) (hμ : KernelLaw α μ) :
    μ = (volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal (centeredExp α x)) := by
  rcases hμ.1 with ⟨hμprob, _⟩
  letI : IsProbabilityMeasure μ := hμprob
  let ρ : Measure ℝ := (volume : Measure ℝ).withDensity
    (fun x => ENNReal.ofReal (centeredExp α x))
  have hq := q_formula α hα
  have hq_meas : Measurable (centeredExp α) := hq.2.2.1
  have hq_nonneg : ∀ x : ℝ, 0 ≤ centeredExp α x := fun x => (hq.2.2.2.1 x).1
  have hq_int : Integrable (centeredExp α) := hq.2.2.2.2.1
  haveI hρfin : IsFiniteMeasure ρ := by
    dsimp [ρ]
    exact MeasureTheory.isFiniteMeasure_withDensity_ofReal hq_int.hasFiniteIntegral
  have hρFT : ∀ ξ : ℝ, measureFT ρ ξ = expFactor α ξ := by
    intro ξ
    have hdens_meas : Measurable (fun x : ℝ => ENNReal.ofReal (centeredExp α x)) :=
      hq_meas.ennreal_ofReal
    have hdens_top : ∀ᵐ x : ℝ ∂(volume : Measure ℝ),
        ENNReal.ofReal (centeredExp α x) < ⊤ := by
      exact Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
    unfold measureFT ρ
    rw [integral_withDensity_eq_integral_toReal_smul hdens_meas hdens_top]
    calc
      (∫ y : ℝ,
          (ENNReal.ofReal (centeredExp α y)).toReal •
            (Complex.exp (-2 * Real.pi * Complex.I * ↑ξ * ↑y) : ℂ) ∂volume) =
          ∫ y : ℝ, Complex.exp (-2 * Real.pi * Complex.I * ↑ξ * ↑y) *
            ↑(centeredExp α y) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [ENNReal.toReal_ofReal (hq_nonneg y)]
        simp [mul_comm]
      _ = FT (centeredExp α) ξ := by
        rfl
      _ = expFactor α ξ := (q_FT α hα).1 ξ
  have hEq : μ = ρ := by
    exact measure_unique μ ρ (fun ξ => by rw [hμ.2 ξ, hρFT ξ])
  simpa [ρ] using hEq

private theorem kernelMeasureConv_measureConv (r : ℝ → ℝ) (μ ν : Measure ℝ) (M x : ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hr_meas : Measurable r) (hr_nonneg : ∀ s : ℝ, 0 ≤ r s)
    (hr_bound : ∀ s : ℝ, r s ≤ M) :
    kernelMeasureConv r (measureConv μ ν) x =
      ∫ u : ℝ, kernelMeasureConv r ν (x - u) ∂μ := by
  let F : ℝ × ℝ → ℝ := fun p => r (x - (p.1 + p.2))
  have hM_nonneg : 0 ≤ M := le_trans (hr_nonneg 0) (hr_bound 0)
  have hF_meas : Measurable F := by
    dsimp [F]
    exact hr_meas.comp (by fun_prop : Measurable fun p : ℝ × ℝ => x - (p.1 + p.2))
  have hF_int : Integrable F (μ.prod ν) := by
    refine (MeasureTheory.integrable_const (μ := μ.prod ν) M).mono'
      hF_meas.aestronglyMeasurable ?_
    filter_upwards with p
    dsimp [F]
    rw [abs_of_nonneg (hr_nonneg (x - (p.1 + p.2)))]
    exact hr_bound (x - (p.1 + p.2))
  calc
    kernelMeasureConv r (measureConv μ ν) x =
        ∫ y : ℝ, r (x - y) ∂Measure.map (fun p : ℝ × ℝ => p.1 + p.2) (μ.prod ν) := by
      rfl
    _ = ∫ p : ℝ × ℝ, r (x - (p.1 + p.2)) ∂μ.prod ν := by
      rw [MeasureTheory.integral_map]
      · fun_prop
      · exact (hr_meas.comp (by fun_prop : Measurable fun y : ℝ => x - y)).aestronglyMeasurable
    _ = ∫ u : ℝ, ∫ v : ℝ, r (x - (u + v)) ∂ν ∂μ := by
      exact integral_prod F hF_int
    _ = ∫ u : ℝ, kernelMeasureConv r ν (x - u) ∂μ := by
      apply integral_congr_ae
      filter_upwards with u
      unfold kernelMeasureConv
      apply integral_congr_ae
      filter_upwards with v
      congr 1
      ring


theorem chain_pointwise (α' : ℕ → ℝ) (ν : ℕ → Measure ℝ)
    (hν : TailLawData α' ν) :
  ∀ m : ℕ, 3 ≤ m → ∀ x : ℝ,
    deconvolutionChain α' ν (m - 1) x =
      conv (centeredExp (deconvolutionSigma α' m)) (deconvolutionChain α' ν m) x ∧
    Integrable (fun t : ℝ =>
      centeredExp (deconvolutionSigma α' m) t * deconvolutionChain α' ν m (x - t)) := by
  intro m hm x
  let β : Fin 2 → ℝ := fun j => α' j
  let r : ℝ → ℝ := rightNestedCentered 2 β
  have hβ : ∀ j : Fin 2, β j ≠ 0 := by
    intro j
    exact hν.1 j
  rcases prob_space α' hν.1 hν.2.1 with ⟨μ, hμ⟩
  rcases hν.2.2.1 m with ⟨hprobνm, _⟩
  rcases hν.2.2.1 (m - 1) with ⟨hprobνprev, _⟩
  rcases (hμ m).1 with ⟨hprobμm, _⟩
  letI : IsProbabilityMeasure (ν m) := hprobνm
  letI : IsProbabilityMeasure (ν (m - 1)) := hprobνprev
  letI : IsProbabilityMeasure (μ m) := hprobμm
  have hm_one : 1 ≤ m := by omega
  have hm_two : 2 ≤ m := by omega
  have hmprev_two : 2 ≤ m - 1 := by omega
  have hσ : deconvolutionSigma α' m = α' m := by
    simp [deconvolutionSigma, hm]
  have hr_basic := rm_basic 1 β hβ
  rcases hr_basic with ⟨hr_meas, hr_nonneg, ⟨M, hr_bound⟩, _hr_int, _hr_mass, _⟩
  have hchain := chain_meas α' μ ν hμ hν m hm_one
  have hμdens := kernelLaw_eq_centeredExp_density (α' m) (μ m) (hν.1 m) (hμ m)
  have hq := q_formula (α' m) (hν.1 m)
  have hq_meas : Measurable (centeredExp (α' m)) := hq.2.2.1
  have hq_nonneg : ∀ t : ℝ, 0 ≤ centeredExp (α' m) t := fun t => (hq.2.2.2.1 t).1
  have hq_int : Integrable (centeredExp (α' m)) := hq.2.2.2.2.1
  have hFm := Fm_props α' ν hν m hm_two
  rcases hFm with
    ⟨hFm_meas, hFm_nonneg, ⟨MF, hFm_bound⟩, _hFm_cont, _hFm_int,
      _hFm_mass, _hFm_lat⟩
  have hMF_nonneg : 0 ≤ MF := le_trans (hFm_nonneg 0) (hFm_bound 0)
  have hintegrable : Integrable (fun t : ℝ =>
      centeredExp (deconvolutionSigma α' m) t * deconvolutionChain α' ν m (x - t)) := by
    rw [hσ]
    refine (hq_int.const_mul MF).mono' ?_ ?_
    · exact ((hq_meas.mul (hFm_meas.comp
        (by fun_prop : Measurable fun t : ℝ => x - t))).aestronglyMeasurable)
    · filter_upwards with t
      calc
        |centeredExp (α' m) t * deconvolutionChain α' ν m (x - t)| =
            centeredExp (α' m) t * deconvolutionChain α' ν m (x - t) := by
          rw [abs_mul, abs_of_nonneg (hq_nonneg t),
            abs_of_nonneg (hFm_nonneg (x - t))]
        _ ≤ centeredExp (α' m) t * MF := by
          exact mul_le_mul_of_nonneg_left (hFm_bound (x - t)) (hq_nonneg t)
        _ = MF * centeredExp (α' m) t := by ring
  constructor
  · calc
      deconvolutionChain α' ν (m - 1) x = kernelMeasureConv r (ν (m - 1)) x := by
        simp [deconvolutionChain, r, β, hmprev_two]
      _ = kernelMeasureConv r (measureConv (μ m) (ν m)) x := by
        rw [hchain]
      _ = ∫ u : ℝ, kernelMeasureConv r (ν m) (x - u) ∂(μ m) := by
        exact kernelMeasureConv_measureConv r (μ m) (ν m) M x
          (by simpa [r] using hr_meas)
          (by intro s; simpa [r] using hr_nonneg s)
          (by intro s; simpa [r] using hr_bound s)
      _ = ∫ u : ℝ, kernelMeasureConv r (ν m) (x - u) ∂((volume : Measure ℝ).withDensity
            (fun u => ENNReal.ofReal (centeredExp (α' m) u))) := by
        rw [hμdens]
      _ = ∫ u : ℝ, centeredExp (α' m) u * kernelMeasureConv r (ν m) (x - u) := by
        have hdens_meas :
            Measurable (fun u : ℝ => ENNReal.ofReal (centeredExp (α' m) u)) :=
          hq_meas.ennreal_ofReal
        have hdens_top : ∀ᵐ u : ℝ ∂(volume : Measure ℝ),
            ENNReal.ofReal (centeredExp (α' m) u) < ⊤ := by
          exact Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
        rw [integral_withDensity_eq_integral_toReal_smul hdens_meas hdens_top]
        apply integral_congr_ae
        filter_upwards with u
        rw [ENNReal.toReal_ofReal (hq_nonneg u)]
        simp
      _ = conv (centeredExp (deconvolutionSigma α' m)) (deconvolutionChain α' ν m) x := by
        unfold conv
        rw [hσ]
        apply integral_congr_ae
        filter_upwards with u
        simp [deconvolutionChain, r, β, hm_two]
  · exact hintegrable


theorem Hr_props (α₁ α₂ : ℝ) (hα₁ : α₁ ≠ 0) (hα₂ : α₂ ≠ 0) :
  let r := rightNestedCentered 2 (fun j : Fin 2 => if j = 0 then α₁ else α₂)
  (∀ x : ℝ, Summable (fun k : ℤ => (-1 : ℝ) ^ k * r (x + k))) ∧
    Continuous (Halt r) ∧
    (∀ x : ℝ, Halt r (x + 1) = -Halt r x) ∧
    (∀ x : ℝ, Halt r (x + 2) = Halt r x) ∧
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x y : ℝ, |x - y| ≤ δ → |Halt r x - Halt r y| ≤ ε) ∧
    ∃ B : ℝ, ∀ x : ℝ, |Halt r x| ≤ B := by
  let β : Fin 2 → ℝ := fun j => if j = 0 then α₁ else α₂
  let r : ℝ → ℝ := rightNestedCentered 2 β
  have hβ : ∀ j, β j ≠ 0 := by
    intro j
    fin_cases j <;> simp [β, hα₁, hα₂]
  rcases rm_decay 2 β (by norm_num) hβ with ⟨C, c, hC, hc, hr_bound⟩
  rcases rm_cont 2 β (by norm_num) hβ with ⟨_Λ, _hΛ, _hLip, hr_cont⟩
  have hdecay_lattice := decay_lattice r C c hC hc hr_bound
  rcases hdecay_lattice with ⟨hr_lat, hr_env, _hr_sum_bound⟩
  have hhalt_summable := halt_summable r
    (fun k : ℤ => C * Real.exp c * Real.exp (-c * |(k : ℝ)|)) hr_env
  have hhalt_cont : Continuous (Halt r) := halt_cont r hr_cont hr_lat
  have hhalt_anti : ∀ x : ℝ, Halt r (x + 1) = -Halt r x := halt_anti r hr_lat
  have hhalt_per2 : ∀ x : ℝ, Halt r (x + 2) = Halt r x := halt_per2 r hr_lat
  have hhalt_unif :
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x y : ℝ, |x - y| ≤ δ → |Halt r x - Halt r y| ≤ ε :=
    per2_unifcont (Halt r) hhalt_cont hhalt_per2
  refine ⟨hhalt_summable.1, hhalt_cont, hhalt_anti, hhalt_per2, hhalt_unif, ?_⟩
  exact ⟨∑' k : ℤ, C * Real.exp c * Real.exp (-c * |(k : ℝ)|), hhalt_summable.2.2⟩


theorem H_through (α' : ℕ → ℝ) (ν : ℕ → Measure ℝ)
    (hν : TailLawData α' ν) :
  ∀ m : ℕ, 2 ≤ m → ∀ x : ℝ,
    Halt (deconvolutionChain α' ν m) x =
      ∫ y : ℝ, Halt (rightNestedCentered 2 (fun j : Fin 2 => α' j)) (x - y) ∂(ν m) := by
  intro m hm x
  let β : Fin 2 → ℝ := fun j => α' j
  let r : ℝ → ℝ := rightNestedCentered 2 β
  have hβ : ∀ j : Fin 2, β j ≠ 0 := by
    intro j
    exact hν.1 j
  rcases hν.2.2.1 m with ⟨hprobνm, _hνtrivial⟩
  letI : IsProbabilityMeasure (ν m) := hprobνm
  have hr_basic := rm_basic 1 β hβ
  rcases hr_basic with
    ⟨hr_meas, hr_nonneg, ⟨M, hr_bound⟩, hr_int, _hr_mass, _hr_genuine⟩
  have hconv_basic := convmeas_basic r (ν m) M
    (by simpa [r] using hr_meas)
    (by intro s; simpa [r] using hr_nonneg s)
    (by simpa [r] using hr_int)
    (by intro s; simpa [r] using hr_bound s)
  rcases rm_decay 2 β (by norm_num) hβ with ⟨C, c, hC, hc, hr_decay⟩
  rcases (convmeas_lattice r (ν m) C c hC hc (by
      intro s
      simpa [r] using hr_decay s)).2 with ⟨B, hB, _hBsum⟩
  let K : ℝ → ℝ := kernelMeasureConv r (ν m)
  let F : ℤ → ℝ → ℝ := fun k y => (-1 : ℝ) ^ k * r ((x - y) + k)
  have hK_nonneg : ∀ z : ℝ, 0 ≤ K z := by
    intro z
    dsimp [K]
    exact (hconv_basic.1 z).2.1
  have hsign_abs : ∀ k : ℤ, |((-1 : ℝ) ^ k)| = 1 := by
    intro k
    rw [abs_zpow]
    norm_num
  have hF_int : ∀ k : ℤ, Integrable (F k) (ν m) := by
    intro k
    have hint := (hconv_basic.1 (x + k)).1
    have hsame : F k = fun y : ℝ => (-1 : ℝ) ^ k * r ((x + k) - y) := by
      funext y
      dsimp [F]
      congr 2
      ring
    rw [hsame]
    exact hint.const_mul ((-1 : ℝ) ^ k)
  have hF_integral_eq : ∀ k : ℤ,
      (∫ y : ℝ, F k y ∂(ν m)) = (-1 : ℝ) ^ k * K (x + k) := by
    intro k
    have hsame : F k = fun y : ℝ => (-1 : ℝ) ^ k * r ((x + k) - y) := by
      funext y
      dsimp [F]
      congr 2
      ring
    calc
      (∫ y : ℝ, F k y ∂(ν m)) =
          ∫ y : ℝ, (-1 : ℝ) ^ k * r ((x + k) - y) ∂(ν m) := by
        rw [hsame]
      _ = (-1 : ℝ) ^ k * ∫ y : ℝ, r ((x + k) - y) ∂(ν m) := by
        rw [integral_const_mul]
      _ = (-1 : ℝ) ^ k * K (x + k) := by
        rfl
  have hF_norm_integral_eq : ∀ k : ℤ,
      (∫ y : ℝ, ‖F k y‖ ∂(ν m)) = |((-1 : ℝ) ^ k * K (x + k))| := by
    intro k
    have hnorm_point : (fun y : ℝ => ‖F k y‖) = fun y : ℝ => r ((x + k) - y) := by
      funext y
      dsimp [F]
      rw [abs_mul, hsign_abs k, one_mul,
        abs_of_nonneg (by simpa [r] using hr_nonneg ((x - y) + k))]
      congr 1
      ring
    have hK_abs : |((-1 : ℝ) ^ k * K (x + k))| = K (x + k) := by
      rw [abs_mul, hsign_abs k, one_mul]
      exact abs_of_nonneg (hK_nonneg (x + k))
    calc
      (∫ y : ℝ, ‖F k y‖ ∂(ν m)) = ∫ y : ℝ, r ((x + k) - y) ∂(ν m) := by
        rw [hnorm_point]
      _ = K (x + k) := by
        rfl
      _ = |((-1 : ℝ) ^ k * K (x + k))| := hK_abs.symm
  have hK_abs_sum : Summable (fun k : ℤ => |((-1 : ℝ) ^ k * K (x + k))|) := by
    have hs := (halt_summable K B hB).2.1 x
    simpa [K] using hs
  have hF_sum : Summable (fun k : ℤ => ∫ y : ℝ, ‖F k y‖ ∂(ν m)) := by
    exact hK_abs_sum.congr (fun k => (hF_norm_integral_eq k).symm)
  have hinterchange := MeasureTheory.integral_tsum_of_summable_integral_norm
    (μ := ν m) (F := F) hF_int hF_sum
  calc
    Halt (deconvolutionChain α' ν m) x = Halt K x := by
      simp [Halt, deconvolutionChain, K, r, β, hm]
    _ = ∑' k : ℤ, (-1 : ℝ) ^ k * K (x + k) := by
      rfl
    _ = ∑' k : ℤ, ∫ y : ℝ, F k y ∂(ν m) := by
      apply tsum_congr
      intro k
      rw [hF_integral_eq]
    _ = ∫ y : ℝ, ∑' k : ℤ, F k y ∂(ν m) := by
      exact hinterchange
    _ = ∫ y : ℝ, Halt r (x - y) ∂(ν m) := by
      apply integral_congr_ae
      filter_upwards with y
      simp [F, Halt]
    _ = ∫ y : ℝ, Halt (rightNestedCentered 2 (fun j : Fin 2 => α' j)) (x - y) ∂(ν m) := by
      simp [r, β]

private theorem integral_shift_bound (H : ℝ → ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (B η δ q : ℝ) (hη_nonneg : 0 ≤ η) (hB_nonneg : 0 ≤ B)
    (hH_cont : Continuous H)
    (hH_bound : ∀ z : ℝ, |H z| ≤ B)
    (hH_unif : ∀ s t : ℝ, |s - t| ≤ δ → |H s - H t| ≤ η)
    (hμ_tail : μ {y : ℝ | δ ≤ |y|} ≤ ENNReal.ofReal q)
    (hq_nonneg : 0 ≤ q) :
  ∀ x : ℝ, |(∫ y : ℝ, H (x - y) ∂μ) - H x| ≤ η + 2 * B * q := by
  classical
  intro x
  let T : Set ℝ := {y : ℝ | δ ≤ |y|}
  let ind : ℝ → ℝ := T.indicator (fun _ : ℝ => (1 : ℝ))
  let G : ℝ → ℝ := fun y => η + (2 * B) * ind y
  have hT_meas : MeasurableSet T := by
    dsimp [T]
    exact (isClosed_le continuous_const continuous_abs).measurableSet
  have htail_real : μ.real T ≤ q := by
    have htr := (ENNReal.toReal_le_toReal (measure_ne_top μ T) ENNReal.ofReal_ne_top).2 hμ_tail
    rwa [← Measure.real_def, ENNReal.toReal_ofReal hq_nonneg] at htr
  have hHshift_asm : AEStronglyMeasurable (fun y : ℝ => H (x - y)) μ := by
    exact (hH_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hHshift_int : Integrable (fun y : ℝ => H (x - y)) μ := by
    refine Integrable.mono' (integrable_const B) hHshift_asm ?_
    filter_upwards with y
    simpa [Real.norm_eq_abs] using hH_bound (x - y)
  have hconst_int : Integrable (fun _ : ℝ => H x) μ := integrable_const (H x)
  have hsub_int : Integrable (fun y : ℝ => H (x - y) - H x) μ := by
    change Integrable ((fun y : ℝ => H (x - y)) - fun _ : ℝ => H x) μ
    exact hHshift_int.sub hconst_int
  have hf_int : Integrable (fun y : ℝ => |H (x - y) - H x|) μ := by
    simpa [Real.norm_eq_abs] using hsub_int.norm
  have hind_int : Integrable ind μ := by
    dsimp [ind]
    exact (integrable_const (1 : ℝ)).indicator hT_meas
  have hG_int : Integrable G μ := by
    dsimp [G]
    exact (integrable_const η).add (hind_int.const_mul (2 * B))
  have hpoint : ∀ y : ℝ, |H (x - y) - H x| ≤ G y := by
    intro y
    by_cases hy : |y| ≤ δ
    · have hdist : |(x - y) - x| ≤ δ := by
        rw [show (x - y) - x = -y by ring, abs_neg]
        exact hy
      have hsmall := hH_unif (x - y) x hdist
      have hind_nonneg : 0 ≤ ind y := by
        dsimp [ind]
        by_cases hyT : y ∈ T
        · rw [Set.indicator_of_mem hyT]
          norm_num
        · rw [Set.indicator_apply]
          simp [hyT]
      have hextra : 0 ≤ (2 * B) * ind y := mul_nonneg (by nlinarith) hind_nonneg
      dsimp [G]
      nlinarith
    · have hyT : y ∈ T := by
        dsimp [T]
        exact le_of_lt (lt_of_not_ge hy)
      have hdiff : |H (x - y) - H x| ≤ 2 * B := by
        have ha := abs_le.mp (hH_bound (x - y))
        have hb := abs_le.mp (hH_bound x)
        exact abs_sub_le_iff.mpr ⟨by nlinarith, by nlinarith⟩
      dsimp [G, ind]
      rw [Set.indicator_of_mem hyT]
      nlinarith
  have hmono : (∫ y : ℝ, |H (x - y) - H x| ∂μ) ≤ ∫ y : ℝ, G y ∂μ := by
    exact integral_mono hf_int hG_int hpoint
  have hG_eval : (∫ y : ℝ, G y ∂μ) = η + (2 * B) * μ.real T := by
    calc
      (∫ y : ℝ, G y ∂μ) =
          ∫ y : ℝ, (fun _ : ℝ => η) y + (fun y : ℝ => (2 * B) * ind y) y ∂μ := by
        rfl
      _ = (∫ y : ℝ, η ∂μ) + ∫ y : ℝ, (2 * B) * ind y ∂μ := by
        exact integral_add (integrable_const η) (hind_int.const_mul (2 * B))
      _ = η + (2 * B) * μ.real T := by
        rw [integral_const, integral_const_mul]
        rw [integral_indicator hT_meas, setIntegral_const]
        simp [Measure.real, IsProbabilityMeasure.measure_univ]
  have htail_term : (2 * B) * μ.real T ≤ (2 * B) * q := by
    exact mul_le_mul_of_nonneg_left htail_real (by nlinarith)
  have hnorm : |∫ y : ℝ, H (x - y) - H x ∂μ| ≤
      ∫ y : ℝ, |H (x - y) - H x| ∂μ := by
    simpa [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (fun y : ℝ => H (x - y) - H x) (μ := μ)
  have hdiff_eq :
      (∫ y : ℝ, H (x - y) ∂μ) - H x = ∫ y : ℝ, H (x - y) - H x ∂μ := by
    have hconst : (∫ _y : ℝ, H x ∂μ) = H x := by
      simp [integral_const, Measure.real, IsProbabilityMeasure.measure_univ]
    calc
      (∫ y : ℝ, H (x - y) ∂μ) - H x =
          (∫ y : ℝ, H (x - y) ∂μ) - ∫ _y : ℝ, H x ∂μ := by
        rw [hconst]
      _ = ∫ y : ℝ, H (x - y) - H x ∂μ := by
        rw [integral_sub hHshift_int hconst_int]
  calc
    |(∫ y : ℝ, H (x - y) ∂μ) - H x| =
        |∫ y : ℝ, H (x - y) - H x ∂μ| := by
      rw [hdiff_eq]
    _ ≤ ∫ y : ℝ, |H (x - y) - H x| ∂μ := hnorm
    _ ≤ ∫ y : ℝ, G y ∂μ := hmono
    _ = η + (2 * B) * μ.real T := hG_eval
    _ ≤ η + 2 * B * q := by nlinarith


theorem H_unif (α' : ℕ → ℝ) (ν : ℕ → Measure ℝ)
    (hν : TailLawData α' ν) :
  (∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ x : ℝ,
      |Halt (deconvolutionChain α' ν N) x -
        Halt (rightNestedCentered 2 (fun j : Fin 2 => α' j)) x| ≤ ε) ∧
  ∀ K : Set ℝ, IsCompact K →
    TendstoUniformlyOn (fun N x => Halt (deconvolutionChain α' ν N) x)
      (fun x => Halt (rightNestedCentered 2 (fun j : Fin 2 => α' j)) x)
      Filter.atTop K := by
  classical
  let r : ℝ → ℝ := rightNestedCentered 2 (fun j : Fin 2 => α' j)
  have hν_orig : TailLawData α' ν := hν
  rcases hν with ⟨hnonzero, _hsum, hprobν, hvpack⟩
  rcases hvpack with ⟨v, hlim, _hchar⟩
  have hlim_orig : TailLimitData α' ν v := hlim
  have hv_nonneg : ∀ m : ℕ, 0 ≤ v m := hlim.2.2.2.1
  have hv_tendsto : Filter.Tendsto v Filter.atTop (𝓝 0) := hlim.2.2.2.2.1
  have hfun : (fun j : Fin 2 => if j = 0 then α' 0 else α' 1) =
      (fun j : Fin 2 => α' j) := by
    funext j
    fin_cases j <;> simp
  have hHr :
      (∀ x : ℝ, Summable (fun k : ℤ => (-1 : ℝ) ^ k * r (x + k))) ∧
        Continuous (Halt r) ∧
        (∀ x : ℝ, Halt r (x + 1) = -Halt r x) ∧
        (∀ x : ℝ, Halt r (x + 2) = Halt r x) ∧
        (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
          ∀ x y : ℝ, |x - y| ≤ δ → |Halt r x - Halt r y| ≤ ε) ∧
        ∃ B : ℝ, ∀ x : ℝ, |Halt r x| ≤ B := by
    simpa [r, hfun] using Hr_props (α' 0) (α' 1) (hnonzero 0) (hnonzero 1)
  rcases hHr with ⟨_hH_sum, hH_cont, _hH_anti, _hH_per, hH_unif, B, hB⟩
  have hB_nonneg : 0 ≤ B := by
    exact (abs_nonneg (Halt r 0)).trans (hB 0)
  have hglobal : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ x : ℝ, |Halt (deconvolutionChain α' ν N) x - Halt r x| ≤ ε := by
    intro ε hε
    rcases hH_unif (ε / 2) (by linarith) with ⟨δ, hδ_pos, hδ_unif⟩
    let c : ℝ := 2 * B / δ ^ 2
    have hc_tend : Filter.Tendsto (fun N : ℕ => c * v N) Filter.atTop (𝓝 0) := by
      simpa [c] using hv_tendsto.const_mul c
    have hevent : ∀ᶠ N : ℕ in Filter.atTop, c * v N ≤ ε / 2 := by
      exact hc_tend.eventually_le_const (by linarith)
    rcases Filter.eventually_atTop.1 hevent with ⟨N₁, hN₁⟩
    refine ⟨max 2 N₁, ?_⟩
    intro N hN x
    have hN_two : 2 ≤ N := le_trans (Nat.le_max_left 2 N₁) hN
    have hN₁_le : N₁ ≤ N := le_trans (Nat.le_max_right 2 N₁) hN
    have hsmall_tail : 2 * B * (v N / δ ^ 2) ≤ ε / 2 := by
      have hcN := hN₁ N hN₁_le
      have hrewrite : 2 * B * (v N / δ ^ 2) = c * v N := by
        dsimp [c]
        field_simp [ne_of_gt (sq_pos_of_pos hδ_pos)]
      rwa [hrewrite]
    rcases hprobν N with ⟨hprobN, _⟩
    letI : IsProbabilityMeasure (ν N) := hprobN
    have hcheb := tail_cheby α' ν v hlim_orig N δ hδ_pos
    have hq_nonneg : 0 ≤ v N / δ ^ 2 := div_nonneg (hv_nonneg N) (sq_nonneg δ)
    have hint_bound := integral_shift_bound (Halt r) (ν N) B (ε / 2) δ (v N / δ ^ 2)
      (by linarith) hB_nonneg hH_cont hB hδ_unif hcheb hq_nonneg x
    have hthrough := H_through α' ν hν_orig N hN_two x
    calc
      |Halt (deconvolutionChain α' ν N) x - Halt r x| =
          |(∫ y : ℝ, Halt r (x - y) ∂(ν N)) - Halt r x| := by
        rw [hthrough]
      _ ≤ ε / 2 + 2 * B * (v N / δ ^ 2) := hint_bound
      _ ≤ ε := by linarith
  refine ⟨?_, ?_⟩
  · intro ε hε
    rcases hglobal ε hε with ⟨N₀, hN₀⟩
    refine ⟨N₀, ?_⟩
    intro N hN x
    simpa [r] using hN₀ N hN x
  · intro K _hK
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    rcases hglobal (ε / 2) (by linarith) with ⟨N₀, hN₀⟩
    rw [Filter.eventually_atTop]
    refine ⟨N₀, ?_⟩
    intro N hN x _hx
    have hle := hN₀ N hN x
    rw [Real.dist_eq]
    calc
      |Halt (rightNestedCentered 2 (fun j : Fin 2 => α' j)) x -
          Halt (deconvolutionChain α' ν N) x| =
          |Halt (deconvolutionChain α' ν N) x - Halt r x| := by
        rw [abs_sub_comm]
      _ ≤ ε / 2 := hle
      _ < ε := by linarith


theorem progression (x u : ℝ) :
  ∃ nplus nminus : ℤ, u < x + 2 * nplus ∧ x + 2 * nminus < u := by
  obtain ⟨nplus, hnplus⟩ := exists_int_gt ((u - x) / 2 : ℝ)
  obtain ⟨nminus, hnminus⟩ := exists_int_lt ((u - x) / 2 : ℝ)
  refine ⟨nplus, nminus, ?_, ?_⟩
  · nlinarith
  · nlinarith


theorem acol_pos (g : ℝ → ℝ)
    (hH1 : IsTotallyPositiveIntegrableContinuous g) (hH2 : g ≠ 0)
    (hH3 : HasExponentialDecay g) (hH4 : SchoenbergProduct g) :
  ∀ x : ℝ, 0 < Acol g x := by
  rcases hH1 with ⟨hTP, hg_int, hg_cont⟩
  rcases hH3 with ⟨C, c, hC, hc, hg_decay⟩
  rcases hH4 with ⟨Cst, γ, δ, α, hCst, hγ, hsumα, hmul, hFT, hFT_ne, hbound⟩
  have hH1_full : IsTotallyPositiveIntegrableContinuous g := ⟨hTP, hg_int, hg_cont⟩
  have hH3_full : HasExponentialDecay g := ⟨C, c, hC, hc, hg_decay⟩
  have hdata : SchoenbergData g Cst γ δ α :=
    ⟨hCst, hγ, hsumα, hmul, hFT, hFT_ne, hbound⟩
  have htri := g_pos g Cst γ δ α hH1_full hH2 hH3_full hdata
  intro x
  have hsumx : Summable (fun n : ℤ => g (x + 2 * n)) :=
    (sum_2Z g C c x hC hc hg_decay).1
  have hnonneg : ∀ n : ℤ, 0 ≤ g (x + 2 * n) := by
    intro n
    exact g_nonneg g hTP (x + 2 * n)
  unfold Acol
  rcases htri with hright | hleft | hall
  · rcases hright with ⟨u, hu⟩
    rcases progression x u with ⟨nplus, _nminus, hplus, _hminus⟩
    exact hsumx.tsum_pos hnonneg nplus (hu (x + 2 * nplus) hplus)
  · rcases hleft with ⟨u, hu⟩
    rcases progression x u with ⟨_nplus, nminus, _hplus, hminus⟩
    exact hsumx.tsum_pos hnonneg nminus (hu (x + 2 * nminus) hminus)
  · exact hsumx.tsum_pos hnonneg 0 (hall (x + 2 * (0 : ℤ)))


theorem bcol_eq (g : ℝ → ℝ) (x : ℝ) :
  Bcol g x = Acol g (x - 1) := by
  rfl


theorem bcol_pos (g : ℝ → ℝ)
    (hH1 : IsTotallyPositiveIntegrableContinuous g) (hH2 : g ≠ 0)
    (hH3 : HasExponentialDecay g) (hH4 : SchoenbergProduct g) :
  ∀ x : ℝ, 0 < Bcol g x := by
  intro x
  rw [bcol_eq g x]
  exact acol_pos g hH1 hH2 hH3 hH4 (x - 1)


theorem caseG (g : ℝ → ℝ) (Cst γ δ : ℝ) (α : ℕ → ℝ)
    (_hH1 : IsTotallyPositiveIntegrableContinuous g) (_hH2 : g ≠ 0)
    (_hH3 : HasExponentialDecay g) (hdata : SchoenbergData g Cst γ δ α)
    (hγ : 0 < γ) :
  GaussianForm g := by
  rcases hdata with ⟨hCst, _hγ_nonneg, _hsum, _hmul, _hFT, hFT_ne, hbound⟩
  exact ⟨Cst, γ, hCst, hγ, hbound, hFT_ne (1 / 2)⟩


theorem caseF (g : ℝ → ℝ) (Cst γ δ : ℝ) (α : ℕ → ℝ)
    (hH1 : IsTotallyPositiveIntegrableContinuous g) (hH2 : g ≠ 0)
    (hH3 : HasExponentialDecay g) (hdata : SchoenbergData g Cst γ δ α)
    (hγ : γ = 0) (hfin : (nonzeroFactorSet α).Finite) :
  FiniteTypeForm g := by
  rcases h_props g Cst γ δ α hH1 hH2 hH3 hdata with
    ⟨_hh_cont, _hh_nonneg, _hh_int, _hh_meas, _hh_FT, hg_shift⟩
  rcases realize_b g Cst γ δ α hH1 hH2 hH3 hdata hγ hfin with
    ⟨M, hM2, β, hβ, hreal⟩
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, M = m + 1 := by
    exact Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) hM2))
  have hm : 1 ≤ m := by omega
  rcases untranslate m β hβ with ⟨a, A, ha, huntrans⟩
  refine ⟨Cst, -δ - A, m, a, ?_, hm, ha, ?_⟩
  · exact hdata.1
  · intro x
    calc
      g x = Cst * normalizedShift Cst δ g (x + δ) := hg_shift x
      _ = Cst * rightNestedCentered (m + 1) β (x + δ) := by rw [hreal (x + δ)]
      _ = Cst * finiteType m a ((x + δ) + A) := by rw [huntrans (x + δ)]
      _ = Cst * finiteType m a (x - (-δ - A)) := by ring_nf


theorem caseI (g : ℝ → ℝ) (Cst γ δ : ℝ) (α : ℕ → ℝ)
    (hH1 : IsTotallyPositiveIntegrableContinuous g) (hH2 : g ≠ 0)
    (hH3 : HasExponentialDecay g) (hdata : SchoenbergData g Cst γ δ α)
    (hγ : γ = 0) (hinf : (nonzeroFactorSet α).Infinite) :
  InfiniteProductForm g := by
  rcases h_props g Cst γ δ α hH1 hH2 hH3 hdata with
    ⟨_hh_cont, _hh_nonneg, _hh_int, _hh_meas, _hh_FT, hg_shift⟩
  rcases realize_c g Cst γ δ α hH1 hH2 hH3 hdata hγ hinf with
    ⟨α', ν, hν, hreal⟩
  let F := deconvolutionChain α' ν
  let σ := deconvolutionSigma α'
  refine ⟨Cst, -δ, α' 0, α' 1, F, σ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hdata.1
  · exact hν.1 0
  · exact hν.1 1
  · intro x
    calc
      g x = Cst * normalizedShift Cst δ g (x + δ) := hg_shift x
      _ = Cst * kernelMeasureConv (rightNestedCentered 2 (fun j : Fin 2 => α' j))
          (ν 2) (x + δ) := by
        rw [hreal (x + δ)]
      _ = Cst * F 2 (x - (-δ)) := by
        dsimp [F, deconvolutionChain]
        ring_nf
  · intro m hm
    rcases Fm_props α' ν hν m hm with
      ⟨_hmeas, _hnonneg, _hbound, hcont, hint, _hmass, hlat⟩
    exact ⟨hcont, hint, hlat⟩
  · intro m hm
    refine ⟨?_, ?_⟩
    · dsimp [σ, deconvolutionSigma]
      simp [hm, hν.1 m]
    · intro x
      have hchain := chain_pointwise α' ν hν m hm x
      simpa [F, σ] using hchain.1
  · intro K hK
    have hunif := (H_unif α' ν hν).2 K hK
    dsimp [F]
    simpa [rightNestedCentered] using hunif

end

end Part8
