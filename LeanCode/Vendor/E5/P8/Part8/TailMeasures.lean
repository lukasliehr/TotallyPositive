import LeanCode.Vendor.E5.P8.Part8.Uniqueness
import LeanCode.Vendor.E5.Defs

open MeasureTheory
open scoped BigOperators
open scoped Topology
open scoped ENNReal

namespace Part8

noncomputable section


def KernelLaw (α : ℝ) (μ : Measure ℝ) : Prop :=
  (∃ _ : IsProbabilityMeasure μ, True) ∧
    ∀ ξ : ℝ, measureFT μ ξ = expFactor α ξ


def headProduct (α' : ℕ → ℝ) (N : ℕ) (ξ : ℝ) : ℂ :=
  ∏ j ∈ Finset.range (N + 1), expFactor (α' j) ξ


def tailProduct (α' : ℕ → ℝ) (m N : ℕ) (ξ : ℝ) : ℂ :=
  ∏ j ∈ (Finset.range (N + 1)).filter (fun j => m < j), expFactor (α' j) ξ


def TailCharfunData (α' : ℕ → ℝ) (ν : ℕ → Measure ℝ) : Prop :=
  ∀ m : ℕ, ∀ ξ : ℝ,
    Filter.Tendsto (fun N : ℕ => tailProduct α' m N ξ)
      Filter.atTop (𝓝 (measureFT (ν m) ξ))




def TailLimitData (α' : ℕ → ℝ) (ν : ℕ → Measure ℝ) (v : ℕ → ℝ) : Prop :=
  (∀ j : ℕ, α' j ≠ 0) ∧
    Summable (fun j : ℕ => (α' j) ^ 2) ∧
    (∀ m : ℕ, ∃ _ : IsProbabilityMeasure (ν m), True) ∧
    (∀ m : ℕ, 0 ≤ v m) ∧
    Filter.Tendsto v Filter.atTop (𝓝 0) ∧
    (∀ m : ℕ,
      Integrable (fun t : ℝ => t) (ν m) ∧
        (∫ t : ℝ, t ∂(ν m)) = 0 ∧
        Integrable (fun t : ℝ => t ^ 2) (ν m) ∧
        (∫ t : ℝ, t ^ 2 ∂(ν m)) = v m) ∧
    TailCharfunData α' ν


def TailLawData (α' : ℕ → ℝ) (ν : ℕ → Measure ℝ) : Prop :=
  (∀ j : ℕ, α' j ≠ 0) ∧
    Summable (fun j : ℕ => (α' j) ^ 2) ∧
    (∀ m : ℕ, ∃ _ : IsProbabilityMeasure (ν m), True) ∧
    ∃ v : ℕ → ℝ, TailLimitData α' ν v ∧ TailCharfunData α' ν


theorem enum_empty (α : ℕ → ℝ)
    (hJ : nonzeroFactorSet α = ∅) :
  ∀ ξ : ℝ, Phi α ξ = 1 := by
  have hα0 : ∀ ν : ℕ, α ν = 0 := by
    intro ν
    by_contra hν
    have hmem : ν ∈ nonzeroFactorSet α := hν
    rw [hJ] at hmem
    exact hmem.elim
  intro ξ
  unfold Phi
  calc
    (∏' ν : ℕ, expFactor (α ν) ξ) = ∏' ν : ℕ, (1 : ℂ) := by
      exact tprod_congr (fun ν => by rw [hα0 ν]; exact (phi_basic 0 ξ).1)
    _ = 1 := by
      exact tprod_one


theorem enum_finite (α : ℕ → ℝ)
    (hfin : (nonzeroFactorSet α).Finite)
    (hne : (nonzeroFactorSet α).Nonempty) :
  ∃ M : ℕ, 1 ≤ M ∧ ∃ e : Fin M → ℕ,
    StrictMono (fun i : Fin M => e i) ∧
      (∀ ν : ℕ, ν ∈ nonzeroFactorSet α ↔ ∃ i : Fin M, e i = ν) ∧
      (∀ i : Fin M, α (e i) ≠ 0) ∧
      ∀ ξ : ℝ, Phi α ξ = ∏ i : Fin M, expFactor (α (e i)) ξ := by
  classical
  let s : Finset ℕ := hfin.toFinset
  let M : ℕ := s.card
  have hs_coe : (s : Set ℕ) = nonzeroFactorSet α := by
    dsimp [s]
    exact hfin.coe_toFinset
  have hs_nonempty : s.Nonempty := by
    rw [← Finset.coe_nonempty, hs_coe]
    exact hne
  have hMpos : 0 < M := by
    simpa [M] using Finset.card_pos.mpr hs_nonempty
  refine ⟨M, Nat.succ_le_of_lt hMpos, ?_⟩
  let e : Fin M → ℕ := fun i => s.orderEmbOfFin (by rfl : s.card = M) i
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · dsimp [e]
    exact (s.orderEmbOfFin (by rfl : s.card = M)).strictMono
  · intro ν
    constructor
    · intro hν
      have hνsSet : ν ∈ (s : Set ℕ) := by
        rw [hs_coe]
        exact hν
      have hνrange : ν ∈ Set.range (s.orderEmbOfFin (by rfl : s.card = M)) := by
        rwa [Finset.range_orderEmbOfFin]
      rcases hνrange with ⟨i, hi⟩
      exact ⟨i, by simpa [e] using hi⟩
    · rintro ⟨i, hi⟩
      have hi_mem_set : e i ∈ (s : Set ℕ) := by
        dsimp [e]
        exact Finset.orderEmbOfFin_mem s (by rfl : s.card = M) i
      have hνsSet : ν ∈ (s : Set ℕ) := by
        simpa [hi] using hi_mem_set
      rw [hs_coe] at hνsSet
      exact hνsSet
  · intro i
    have hi_mem_set : e i ∈ (s : Set ℕ) := by
      dsimp [e]
      exact Finset.orderEmbOfFin_mem s (by rfl : s.card = M) i
    rw [hs_coe] at hi_mem_set
    exact hi_mem_set
  · intro ξ
    unfold Phi
    calc
      (∏' ν : ℕ, expFactor (α ν) ξ) = ∏ ν ∈ s, expFactor (α ν) ξ := by
        apply tprod_eq_prod
        intro ν hνs
        have hnot : ν ∉ nonzeroFactorSet α := by
          intro hJ
          have hνsSet : ν ∈ (s : Set ℕ) := by
            rw [hs_coe]
            exact hJ
          exact hνs hνsSet
        have hα0 : α ν = 0 := by
          by_contra hα
          exact hnot hα
        rw [hα0]
        exact (phi_basic 0 ξ).1
      _ = ∏ i : Fin M, expFactor (α (e i)) ξ := by
        let emb := s.orderEmbOfFin (by rfl : s.card = M)
        have hmap : Finset.map emb.toEmbedding Finset.univ = s := by
          dsimp [emb]
          exact Finset.map_orderEmbOfFin_univ s (by rfl : s.card = M)
        rw [← hmap]
        change (∏ x ∈ Finset.map emb.toEmbedding Finset.univ, expFactor (α x) ξ) =
          ∏ i : Fin M, expFactor (α (e i)) ξ
        rw [Finset.prod_map]
        simp [e, emb]


theorem enum_infinite (α : ℕ → ℝ)
    (hsum : Summable (fun ν : ℕ => (α ν) ^ 2))
    (hmul : ∀ ξ : ℝ, Multipliable (fun ν : ℕ => expFactor (α ν) ξ))
    (hinf : (nonzeroFactorSet α).Infinite) :
  ∃ e : ℕ → ℕ, StrictMono e ∧
    (∀ ν : ℕ, ν ∈ nonzeroFactorSet α ↔ ∃ j : ℕ, e j = ν) ∧
    (let α' : ℕ → ℝ := fun j => α (e j)
     (∀ j : ℕ, α' j ≠ 0) ∧
      Summable (fun j : ℕ => (α' j) ^ 2) ∧
      (∀ ξ : ℝ, Filter.Tendsto (fun N : ℕ => headProduct α' N ξ)
        Filter.atTop (𝓝 (Phi α ξ))) ∧
      (∀ m : ℕ, ∀ ξ : ℝ, tailProduct α' m m ξ = tailProduct α' m m ξ)) := by
  classical
  let p : ℕ → Prop := fun ν => α ν ≠ 0
  have hinf_p : ({ν : ℕ | p ν}).Infinite := by
    simpa [p, nonzeroFactorSet] using hinf
  let e : ℕ → ℕ := Nat.nth p
  have he_strict : StrictMono e := by
    dsimp [e]
    exact Nat.nth_strictMono hinf_p
  have he_inj : Function.Injective e := he_strict.injective
  have hrange_eq : Set.range e = {ν : ℕ | p ν} := by
    dsimp [e]
    exact Nat.range_nth_of_infinite hinf_p
  refine ⟨e, he_strict, ?_, ?_⟩
  · intro ν
    constructor
    · intro hν
      have hνp : ν ∈ {ν : ℕ | p ν} := by
        simpa [p, nonzeroFactorSet] using hν
      have hνrange : ν ∈ Set.range e := by
        rwa [hrange_eq]
      exact hνrange
    · rintro ⟨j, hj⟩
      have hmem_range : ν ∈ Set.range e := ⟨j, hj⟩
      have hνp : ν ∈ {ν : ℕ | p ν} := by
        rwa [← hrange_eq]
      simpa [p, nonzeroFactorSet] using hνp
  · let αp : ℕ → ℝ := fun j => α (e j)
    have hnonzero : ∀ j : ℕ, αp j ≠ 0 := by
      intro j
      have hj : p (e j) := by
        dsimp [e]
        exact Nat.nth_mem_of_infinite hinf_p j
      simpa [p, αp] using hj
    have hsump : Summable (fun j : ℕ => (αp j) ^ 2) := by
      change Summable ((fun ν : ℕ => (α ν) ^ 2) ∘ e)
      exact hsum.comp_injective he_inj
    have hprod_tend : ∀ ξ : ℝ, Filter.Tendsto (fun N : ℕ => headProduct αp N ξ)
        Filter.atTop (𝓝 (Phi α ξ)) := by
      intro ξ
      let f : ℕ → ℂ := fun ν => expFactor (α ν) ξ
      have hout : ∀ ν : ℕ, ν ∉ Set.range e → f ν = 1 := by
        intro ν hnot
        have hnotp : ¬ p ν := by
          intro hpν
          exact hnot (by
            rw [hrange_eq]
            exact hpν)
        have hα0 : α ν = 0 := not_not.mp hnotp
        dsimp [f]
        rw [hα0]
        exact (phi_basic 0 ξ).1
      have hsupport : Function.mulSupport f ⊆ Set.range e := by
        intro ν hν
        by_contra hnot
        exact hν (hout ν hnot)
      have htprod0 : (∏' j : ℕ, f (e j)) = ∏' ν : ℕ, f ν :=
        Function.Injective.tprod_eq (α := ℂ) he_inj hsupport
      have htprod : (∏' j : ℕ, f (e j)) = Phi α ξ := by
        rw [htprod0]
        rfl
      have hcomp_mul : Multipliable (fun j : ℕ => f (e j)) := by
        exact (Function.Injective.multipliable_iff (α := ℂ) he_inj hout).2 (hmul ξ)
      have htend0 := hcomp_mul.hasProd.tendsto_prod_nat
      have htend1 : Filter.Tendsto (fun N : ℕ => ∏ j ∈ Finset.range (N + 1), f (e j))
          Filter.atTop (𝓝 (∏' j : ℕ, f (e j))) := by
        exact (Filter.tendsto_add_atTop_iff_nat 1).2 htend0
      rw [htprod] at htend1
      simpa [headProduct, αp, f] using htend1
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hnonzero
    · exact hsump
    · exact hprod_tend
    · intro m ξ
      rfl


theorem prob_space (α' : ℕ → ℝ)
    (hnonzero : ∀ j : ℕ, α' j ≠ 0)
    (_hsum : Summable (fun j : ℕ => (α' j) ^ 2)) :
  ∃ μ : ℕ → Measure ℝ, (∀ j : ℕ, KernelLaw (α' j) (μ j)) := by
  have hexists : ∀ j : ℕ, ∃ μj : Measure ℝ, KernelLaw (α' j) μj := by
    intro j
    rcases q_formula (α' j) (hnonzero j) with
      ⟨_hpos, _hneg, hmeas, hnonneg_bound, hint, hint_mass⟩
    rcases FT_density (centeredExp (α' j)) hmeas
        (fun x => (hnonneg_bound x).1) hint with
      ⟨μj, _hfin, hmass, hFTdens⟩
    have hprob : IsProbabilityMeasure μj := by
      exact isProbabilityMeasure_iff.mpr (by
        rw [hmass, hint_mass]
        norm_num)
    have hFTq := (q_FT (α' j) (hnonzero j)).1
    refine ⟨μj, ?_⟩
    constructor
    · exact ⟨hprob, trivial⟩
    · intro ξ
      rw [hFTdens ξ, hFTq ξ]
  choose μ hμ using hexists
  exact ⟨μ, hμ⟩

private def finiteMeasureConv (μ ν : Measure ℝ) : Measure ℝ :=
  Measure.map (fun p : ℝ × ℝ => p.1 + p.2) (μ.prod ν)

private theorem finiteMeasureConv_isProbabilityMeasure (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (finiteMeasureConv μ ν) := by
  unfold finiteMeasureConv
  exact Measure.isProbabilityMeasure_map (μ := μ.prod ν)
    (by fun_prop : AEMeasurable (fun p : ℝ × ℝ => p.1 + p.2) (μ.prod ν))

private theorem finiteMeasureConv_FT (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
  ∀ ξ : ℝ, measureFT (finiteMeasureConv μ ν) ξ = measureFT μ ξ * measureFT ν ξ := by
  intro ξ
  unfold measureFT finiteMeasureConv
  calc
    ∫ y : ℝ, Complex.exp (-2 * Real.pi * Complex.I * ↑ξ * ↑y) ∂
        Measure.map (fun p : ℝ × ℝ => p.1 + p.2) (μ.prod ν) =
        ∫ p : ℝ × ℝ, Complex.exp (-2 * Real.pi * Complex.I * ↑ξ * ↑(p.1 + p.2)) ∂
          μ.prod ν := by
      rw [MeasureTheory.integral_map]
      · fun_prop
      · fun_prop
    _ = ∫ p : ℝ × ℝ,
        Complex.exp (-2 * Real.pi * Complex.I * ↑ξ * ↑p.1) *
          Complex.exp (-2 * Real.pi * Complex.I * ↑ξ * ↑p.2) ∂μ.prod ν := by
      apply integral_congr_ae
      filter_upwards with p
      rw [← Complex.exp_add]
      congr 1
      norm_num
      ring
    _ = (∫ x : ℝ, Complex.exp (-2 * Real.pi * Complex.I * ↑ξ * ↑x) ∂μ) *
        ∫ y : ℝ, Complex.exp (-2 * Real.pi * Complex.I * ↑ξ * ↑y) ∂ν := by
      exact MeasureTheory.integral_prod_mul
        (μ := μ) (ν := ν)
        (f := fun x : ℝ => Complex.exp (-2 * Real.pi * Complex.I * ↑ξ * ↑x))
        (g := fun y : ℝ => Complex.exp (-2 * Real.pi * Complex.I * ↑ξ * ↑y))

private theorem prod_fst_integrable (μ ν : Measure ℝ) [IsFiniteMeasure ν]
    (hμ1 : Integrable (fun x : ℝ => x) μ) :
    Integrable (fun p : ℝ × ℝ => p.1) (μ.prod ν) := by
  simpa using hμ1.mul_prod
    (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) ν)

private theorem prod_snd_integrable (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    (hν1 : Integrable (fun y : ℝ => y) ν) :
    Integrable (fun p : ℝ × ℝ => p.2) (μ.prod ν) := by
  simpa [mul_comm] using
    (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) μ).mul_prod hν1

private theorem prod_fst_integral (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsProbabilityMeasure ν] :
    (∫ p : ℝ × ℝ, p.1 ∂μ.prod ν) = ∫ x : ℝ, x ∂μ := by
  calc
    ∫ p : ℝ × ℝ, p.1 ∂μ.prod ν =
        ∫ p : ℝ × ℝ, (fun x : ℝ => x) p.1 *
          (fun _ : ℝ => (1 : ℝ)) p.2 ∂μ.prod ν := by
      simp
    _ = (∫ x : ℝ, x ∂μ) * ∫ y : ℝ, (1 : ℝ) ∂ν := by
      exact MeasureTheory.integral_prod_mul
        (μ := μ) (ν := ν) (f := fun x : ℝ => x) (g := fun _ : ℝ => (1 : ℝ))
    _ = ∫ x : ℝ, x ∂μ := by
      simp

private theorem prod_snd_integral (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsFiniteMeasure ν] :
    (∫ p : ℝ × ℝ, p.2 ∂μ.prod ν) = ∫ y : ℝ, y ∂ν := by
  calc
    ∫ p : ℝ × ℝ, p.2 ∂μ.prod ν =
        ∫ p : ℝ × ℝ, (fun _ : ℝ => (1 : ℝ)) p.1 *
          (fun y : ℝ => y) p.2 ∂μ.prod ν := by
      simp
    _ = (∫ x : ℝ, (1 : ℝ) ∂μ) * ∫ y : ℝ, y ∂ν := by
      exact MeasureTheory.integral_prod_mul
        (μ := μ) (ν := ν) (f := fun _ : ℝ => (1 : ℝ)) (g := fun y : ℝ => y)
    _ = ∫ y : ℝ, y ∂ν := by
      simp

private theorem prod_fst_sq_integral (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsProbabilityMeasure ν] :
    (∫ p : ℝ × ℝ, p.1 ^ 2 ∂μ.prod ν) = ∫ x : ℝ, x ^ 2 ∂μ := by
  calc
    ∫ p : ℝ × ℝ, p.1 ^ 2 ∂μ.prod ν =
        ∫ p : ℝ × ℝ, (fun x : ℝ => x ^ 2) p.1 *
          (fun _ : ℝ => (1 : ℝ)) p.2 ∂μ.prod ν := by
      simp
    _ = (∫ x : ℝ, x ^ 2 ∂μ) * ∫ y : ℝ, (1 : ℝ) ∂ν := by
      exact MeasureTheory.integral_prod_mul
        (μ := μ) (ν := ν) (f := fun x : ℝ => x ^ 2)
        (g := fun _ : ℝ => (1 : ℝ))
    _ = ∫ x : ℝ, x ^ 2 ∂μ := by
      simp

private theorem prod_snd_sq_integral (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsFiniteMeasure ν] :
    (∫ p : ℝ × ℝ, p.2 ^ 2 ∂μ.prod ν) = ∫ y : ℝ, y ^ 2 ∂ν := by
  calc
    ∫ p : ℝ × ℝ, p.2 ^ 2 ∂μ.prod ν =
        ∫ p : ℝ × ℝ, (fun _ : ℝ => (1 : ℝ)) p.1 *
          (fun y : ℝ => y ^ 2) p.2 ∂μ.prod ν := by
      simp
    _ = (∫ x : ℝ, (1 : ℝ) ∂μ) * ∫ y : ℝ, y ^ 2 ∂ν := by
      exact MeasureTheory.integral_prod_mul
        (μ := μ) (ν := ν) (f := fun _ : ℝ => (1 : ℝ))
        (g := fun y : ℝ => y ^ 2)
    _ = ∫ y : ℝ, y ^ 2 ∂ν := by
      simp

private theorem prod_cross_integral (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (∫ p : ℝ × ℝ, p.1 * p.2 ∂μ.prod ν) =
      (∫ x : ℝ, x ∂μ) * ∫ y : ℝ, y ∂ν := by
  exact MeasureTheory.integral_prod_mul
    (μ := μ) (ν := ν) (f := fun x : ℝ => x) (g := fun y : ℝ => y)

private theorem finiteMeasureConv_moments (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ1 : Integrable (fun x : ℝ => x) μ)
    (hμ2 : Integrable (fun x : ℝ => x ^ 2) μ)
    (hν1 : Integrable (fun y : ℝ => y) ν)
    (hν2 : Integrable (fun y : ℝ => y ^ 2) ν)
    (hμmean : (∫ x : ℝ, x ∂μ) = 0)
    (hνmean : (∫ y : ℝ, y ∂ν) = 0)
    (A B : ℝ)
    (hμsecond : (∫ x : ℝ, x ^ 2 ∂μ) = A)
    (hνsecond : (∫ y : ℝ, y ^ 2 ∂ν) = B) :
    Integrable (fun t : ℝ => t) (finiteMeasureConv μ ν) ∧
      Integrable (fun t : ℝ => t ^ 2) (finiteMeasureConv μ ν) ∧
      (∫ t : ℝ, t ∂finiteMeasureConv μ ν) = 0 ∧
      (∫ t : ℝ, t ^ 2 ∂finiteMeasureConv μ ν) = A + B := by
  have hfst : Integrable (fun p : ℝ × ℝ => p.1) (μ.prod ν) :=
    prod_fst_integrable μ ν hμ1
  have hsnd : Integrable (fun p : ℝ × ℝ => p.2) (μ.prod ν) :=
    prod_snd_integrable μ ν hν1
  have hadd : Integrable (fun p : ℝ × ℝ => p.1 + p.2) (μ.prod ν) := hfst.add hsnd
  have hfst2 : Integrable (fun p : ℝ × ℝ => p.1 ^ 2) (μ.prod ν) := by
    simpa using hμ2.mul_prod
      (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) ν)
  have hsnd2 : Integrable (fun p : ℝ × ℝ => p.2 ^ 2) (μ.prod ν) := by
    simpa [mul_comm] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) μ).mul_prod hν2
  have hcross : Integrable (fun p : ℝ × ℝ => p.1 * p.2) (μ.prod ν) :=
    hμ1.mul_prod hν1
  have hsq_parts :
      Integrable (fun p : ℝ × ℝ => p.1 ^ 2 + 2 * (p.1 * p.2) + p.2 ^ 2)
        (μ.prod ν) :=
    (hfst2.add (hcross.const_mul 2)).add hsnd2
  have hsq : Integrable (fun p : ℝ × ℝ => (p.1 + p.2) ^ 2) (μ.prod ν) := by
    exact (integrable_congr (Filter.Eventually.of_forall (fun p : ℝ × ℝ => by
      ring))).mpr hsq_parts
  have hconv1 : Integrable (fun t : ℝ => t) (finiteMeasureConv μ ν) := by
    unfold finiteMeasureConv
    rw [integrable_map_measure (by fun_prop) (by fun_prop)]
    exact hadd
  have hconv2 : Integrable (fun t : ℝ => t ^ 2) (finiteMeasureConv μ ν) := by
    unfold finiteMeasureConv
    rw [integrable_map_measure (by fun_prop) (by fun_prop)]
    exact hsq
  refine ⟨hconv1, hconv2, ?_, ?_⟩
  · unfold finiteMeasureConv
    calc
      ∫ t : ℝ, t ∂Measure.map (fun p : ℝ × ℝ => p.1 + p.2) (μ.prod ν) =
          ∫ p : ℝ × ℝ, p.1 + p.2 ∂μ.prod ν := by
        rw [MeasureTheory.integral_map]
        · fun_prop
        · fun_prop
      _ = (∫ p : ℝ × ℝ, p.1 ∂μ.prod ν) + ∫ p : ℝ × ℝ, p.2 ∂μ.prod ν := by
        rw [MeasureTheory.integral_add hfst hsnd]
      _ = (∫ x : ℝ, x ∂μ) + ∫ y : ℝ, y ∂ν := by
        rw [prod_fst_integral μ ν, prod_snd_integral μ ν]
      _ = 0 := by
        rw [hμmean, hνmean]
        ring
  · unfold finiteMeasureConv
    calc
      ∫ t : ℝ, t ^ 2 ∂Measure.map (fun p : ℝ × ℝ => p.1 + p.2) (μ.prod ν) =
          ∫ p : ℝ × ℝ, (p.1 + p.2) ^ 2 ∂μ.prod ν := by
        rw [MeasureTheory.integral_map]
        · fun_prop
        · fun_prop
      _ = ∫ p : ℝ × ℝ, (p.1 ^ 2 + 2 * (p.1 * p.2)) + p.2 ^ 2 ∂μ.prod ν := by
        apply integral_congr_ae
        filter_upwards with p
        ring
      _ = (∫ p : ℝ × ℝ, p.1 ^ 2 + 2 * (p.1 * p.2) ∂μ.prod ν) +
            (∫ p : ℝ × ℝ, p.2 ^ 2 ∂μ.prod ν) := by
        simpa only [Pi.add_apply] using
          (MeasureTheory.integral_add (μ := μ.prod ν)
            (f := fun p : ℝ × ℝ => p.1 ^ 2 + 2 * (p.1 * p.2))
            (g := fun p : ℝ × ℝ => p.2 ^ 2)
            (hfst2.add (hcross.const_mul 2)) hsnd2)
      _ = ((∫ p : ℝ × ℝ, p.1 ^ 2 ∂μ.prod ν) +
            (∫ p : ℝ × ℝ, 2 * (p.1 * p.2) ∂μ.prod ν)) +
            (∫ p : ℝ × ℝ, p.2 ^ 2 ∂μ.prod ν) := by
        rw [show
          (∫ p : ℝ × ℝ, p.1 ^ 2 + 2 * (p.1 * p.2) ∂μ.prod ν) =
            (∫ p : ℝ × ℝ, p.1 ^ 2 ∂μ.prod ν) +
              (∫ p : ℝ × ℝ, 2 * (p.1 * p.2) ∂μ.prod ν) by
          simpa only [Pi.add_apply] using
            (MeasureTheory.integral_add (μ := μ.prod ν)
              (f := fun p : ℝ × ℝ => p.1 ^ 2)
              (g := fun p : ℝ × ℝ => 2 * (p.1 * p.2))
              hfst2 (hcross.const_mul 2))]
      _ = (∫ p : ℝ × ℝ, p.1 ^ 2 ∂μ.prod ν) +
            (∫ p : ℝ × ℝ, 2 * (p.1 * p.2) ∂μ.prod ν) +
            (∫ p : ℝ × ℝ, p.2 ^ 2 ∂μ.prod ν) := by
        ring
      _ = (∫ x : ℝ, x ^ 2 ∂μ) +
            2 * ((∫ x : ℝ, x ∂μ) * ∫ y : ℝ, y ∂ν) +
            (∫ y : ℝ, y ^ 2 ∂ν) := by
        rw [prod_fst_sq_integral μ ν, prod_snd_sq_integral μ ν]
        rw [MeasureTheory.integral_const_mul]
        rw [prod_cross_integral μ ν]
      _ = A + B := by
        rw [hμmean, hνmean, hμsecond, hνsecond]
        ring

private theorem finiteKernelProduct (α' : ℕ → ℝ) (μ : ℕ → Measure ℝ)
    (hμ : ∀ j : ℕ, KernelLaw (α' j) (μ j)) :
    ∀ F : Finset ℕ,
      ∃ lam : Measure ℝ, (∃ _ : IsProbabilityMeasure lam, True) ∧
        ∀ ξ : ℝ, measureFT lam ξ = ∏ j ∈ F, expFactor (α' j) ξ := by
  classical
  intro F
  induction F using Finset.induction_on with
  | empty =>
      refine ⟨Measure.dirac (0 : ℝ), ⟨inferInstance, trivial⟩, ?_⟩
      intro ξ
      unfold measureFT
      rw [MeasureTheory.integral_dirac]
      simp
  | insert a s ha hs =>
      rcases hs with ⟨lam, hprob_lam, hFT_lam⟩
      rcases hprob_lam with ⟨hlam_prob, _⟩
      rcases (hμ a).1 with ⟨hμa_prob, _⟩
      letI : IsProbabilityMeasure (μ a) := hμa_prob
      letI : IsProbabilityMeasure lam := hlam_prob
      let lam' : Measure ℝ := finiteMeasureConv (μ a) lam
      have hprob' : IsProbabilityMeasure lam' := by
        dsimp [lam']
        exact finiteMeasureConv_isProbabilityMeasure (μ a) lam
      refine ⟨lam', ⟨hprob', trivial⟩, ?_⟩
      intro ξ
      calc
        measureFT lam' ξ = measureFT (μ a) ξ * measureFT lam ξ := by
          dsimp [lam']
          exact finiteMeasureConv_FT (μ a) lam ξ
        _ = expFactor (α' a) ξ * ∏ j ∈ s, expFactor (α' j) ξ := by
          rw [(hμ a).2 ξ, hFT_lam ξ]
        _ = ∏ j ∈ insert a s, expFactor (α' j) ξ := by
          simpa using (Finset.prod_insert (s := s) (a := a)
            (f := fun j : ℕ => expFactor (α' j) ξ) ha).symm

private theorem kernelLaw_moments (α : ℝ) (μ : Measure ℝ)
    (hμ : KernelLaw α μ) :
    Integrable (fun t : ℝ => t) μ ∧
      Integrable (fun t : ℝ => t ^ 2) μ ∧
      (∫ t : ℝ, t ∂μ) = 0 ∧
      (∫ t : ℝ, t ^ 2 ∂μ) = α ^ 2 := by
  rcases hμ.1 with ⟨hprob, _⟩
  letI : IsProbabilityMeasure μ := hprob
  by_cases hα : α = 0
  · let δ : Measure ℝ := Measure.dirac (0 : ℝ)
    have hδFT : ∀ ξ : ℝ, measureFT δ ξ = expFactor α ξ := by
      intro ξ
      unfold measureFT δ
      rw [MeasureTheory.integral_dirac]
      simp [expFactor, hα]
    have hmeq : μ = δ := by
      exact measure_unique μ δ (fun ξ => by rw [hμ.2 ξ, hδFT ξ])
    rw [hmeq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact MeasureTheory.integrable_dirac (by simp)
    · exact MeasureTheory.integrable_dirac (by simp)
    · rw [MeasureTheory.integral_dirac]
    · rw [MeasureTheory.integral_dirac, hα]
  · let ρ : Measure ℝ := (volume : Measure ℝ).withDensity
        (fun x => ENNReal.ofReal (centeredExp α x))
    rcases q_formula α hα with ⟨_hpos, _hneg, hq_meas, hq_nonneg_bound, hq_int, _hq_mass⟩
    rcases q_moments α hα with ⟨hq_m1_int, hq_m2_int, hq_m1, hq_m2⟩
    haveI hρfin : IsFiniteMeasure ρ := by
      dsimp [ρ]
      exact MeasureTheory.isFiniteMeasure_withDensity_ofReal hq_int.hasFiniteIntegral
    have hdens_meas : Measurable (fun x : ℝ => ENNReal.ofReal (centeredExp α x)) :=
      hq_meas.ennreal_ofReal
    have hdens_top : ∀ᵐ x : ℝ ∂(volume : Measure ℝ),
        ENNReal.ofReal (centeredExp α x) < ⊤ := by
      exact Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)
    have hρFT : ∀ ξ : ℝ, measureFT ρ ξ = expFactor α ξ := by
      intro ξ
      have hFTq := (q_FT α hα).1 ξ
      calc
        measureFT ρ ξ = FT (centeredExp α) ξ := by
          unfold measureFT FT ρ
          rw [integral_withDensity_eq_integral_toReal_smul hdens_meas hdens_top]
          apply integral_congr_ae
          filter_upwards with y
          rw [ENNReal.toReal_ofReal ((hq_nonneg_bound y).1)]
          simp [mul_comm]
        _ = expFactor α ξ := hFTq
    have hmeq : μ = ρ := by
      exact measure_unique μ ρ (fun ξ => by rw [hμ.2 ξ, hρFT ξ])
    rw [hmeq]
    have hfun1 :
        (fun x : ℝ => x * (ENNReal.ofReal (centeredExp α x)).toReal) =ᵐ[volume]
          fun x : ℝ => x * centeredExp α x := by
      filter_upwards with x
      rw [ENNReal.toReal_ofReal ((hq_nonneg_bound x).1)]
    have hfun2 :
        (fun x : ℝ => x ^ 2 * (ENNReal.ofReal (centeredExp α x)).toReal) =ᵐ[volume]
          fun x : ℝ => x ^ 2 * centeredExp α x := by
      filter_upwards with x
      rw [ENNReal.toReal_ofReal ((hq_nonneg_bound x).1)]
    have hint1 : Integrable (fun t : ℝ => t) ρ := by
      dsimp [ρ]
      rw [integrable_withDensity_iff hdens_meas hdens_top]
      exact (integrable_congr hfun1).mpr hq_m1_int
    have hint2 : Integrable (fun t : ℝ => t ^ 2) ρ := by
      dsimp [ρ]
      rw [integrable_withDensity_iff hdens_meas hdens_top]
      exact (integrable_congr hfun2).mpr hq_m2_int
    refine ⟨hint1, hint2, ?_, ?_⟩
    · calc
        ∫ t : ℝ, t ∂ρ =
            ∫ t : ℝ, (ENNReal.ofReal (centeredExp α t)).toReal * t := by
          dsimp [ρ]
          rw [integral_withDensity_eq_integral_toReal_smul hdens_meas hdens_top]
          apply integral_congr_ae
          filter_upwards with t
          simp [smul_eq_mul]
        _ = ∫ t : ℝ, t * centeredExp α t := by
          apply integral_congr_ae
          filter_upwards [hfun1] with t ht
          calc
            (ENNReal.ofReal (centeredExp α t)).toReal * t =
                t * (ENNReal.ofReal (centeredExp α t)).toReal := by ring
            _ = t * centeredExp α t := ht
        _ = 0 := hq_m1
    · calc
        ∫ t : ℝ, t ^ 2 ∂ρ =
            ∫ t : ℝ, (ENNReal.ofReal (centeredExp α t)).toReal * t ^ 2 := by
          dsimp [ρ]
          rw [integral_withDensity_eq_integral_toReal_smul hdens_meas hdens_top]
          apply integral_congr_ae
          filter_upwards with t
          simp [smul_eq_mul]
        _ = ∫ t : ℝ, t ^ 2 * centeredExp α t := by
          apply integral_congr_ae
          filter_upwards [hfun2] with t ht
          calc
            (ENNReal.ofReal (centeredExp α t)).toReal * t ^ 2 =
                t ^ 2 * (ENNReal.ofReal (centeredExp α t)).toReal := by ring
            _ = t ^ 2 * centeredExp α t := ht
        _ = α ^ 2 := hq_m2


theorem moments_X (α' : ℕ → ℝ) (μ : ℕ → Measure ℝ)
    (hμ : ∀ j : ℕ, KernelLaw (α' j) (μ j)) :
  ∀ j : ℕ,
    Integrable (fun t : ℝ => t) (μ j) ∧
      Integrable (fun t : ℝ => t ^ 2) (μ j) ∧
      (∫ t : ℝ, t ∂(μ j)) = 0 ∧
      (∫ t : ℝ, t ^ 2 ∂(μ j)) = (α' j) ^ 2 := by
  intro j
  exact kernelLaw_moments (α' j) (μ j) (hμ j)


theorem sumsq (α' : ℕ → ℝ) (μ : ℕ → Measure ℝ)
    (hμ : ∀ j : ℕ, KernelLaw (α' j) (μ j)) :
  ∀ F : Finset ℕ,
    ∃ lam : Measure ℝ, (∃ _ : IsProbabilityMeasure lam, True) ∧
      (∫ t : ℝ, t ∂lam) = 0 ∧
      (∫ t : ℝ, t ^ 2 ∂lam) = ∑ j ∈ F, (α' j) ^ 2 := by
  classical
  have hstrong : ∀ F : Finset ℕ,
      ∃ lam : Measure ℝ, (∃ _ : IsProbabilityMeasure lam, True) ∧
        Integrable (fun t : ℝ => t) lam ∧
        Integrable (fun t : ℝ => t ^ 2) lam ∧
        (∫ t : ℝ, t ∂lam) = 0 ∧
        (∫ t : ℝ, t ^ 2 ∂lam) = ∑ j ∈ F, (α' j) ^ 2 := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
        refine ⟨Measure.dirac (0 : ℝ), ⟨inferInstance, trivial⟩, ?_, ?_, ?_, ?_⟩
        · exact MeasureTheory.integrable_dirac (by simp)
        · exact MeasureTheory.integrable_dirac (by simp)
        · rw [MeasureTheory.integral_dirac]
        · rw [MeasureTheory.integral_dirac]
          simp
    | insert a s ha hs =>
        rcases hs with
          ⟨lam, hprob_lam, hlam1, hlam2, hlam_mean, hlam_second⟩
        rcases hprob_lam with ⟨hlam_prob, _⟩
        rcases (hμ a).1 with ⟨hμa_prob, _⟩
        haveI : IsProbabilityMeasure lam := hlam_prob
        haveI : IsProbabilityMeasure (μ a) := hμa_prob
        rcases moments_X α' μ hμ a with ⟨hμa1, hμa2, hμa_mean, hμa_second⟩
        let lam' : Measure ℝ := finiteMeasureConv (μ a) lam
        have hprob' : IsProbabilityMeasure lam' := by
          dsimp [lam']
          exact finiteMeasureConv_isProbabilityMeasure (μ a) lam
        rcases finiteMeasureConv_moments (μ a) lam hμa1 hμa2 hlam1 hlam2
            hμa_mean hlam_mean ((α' a) ^ 2) (∑ j ∈ s, (α' j) ^ 2)
            hμa_second hlam_second with
          ⟨hconv1, hconv2, hconv_mean, hconv_second⟩
        refine ⟨lam', ⟨hprob', trivial⟩, hconv1, hconv2, hconv_mean, ?_⟩
        calc
          ∫ t : ℝ, t ^ 2 ∂lam' = (α' a) ^ 2 + ∑ j ∈ s, (α' j) ^ 2 :=
            hconv_second
          _ = ∑ j ∈ insert a s, (α' j) ^ 2 := by
            rw [Finset.sum_insert ha]
  intro F
  rcases hstrong F with ⟨lam, hprob, _hint1, _hint2, hmean, hsecond⟩
  exact ⟨lam, hprob, hmean, hsecond⟩


theorem finsum_charfun (α' : ℕ → ℝ) (μ : ℕ → Measure ℝ)
    (hμ : ∀ j : ℕ, KernelLaw (α' j) (μ j)) :
  ∀ m N : ℕ, m + 1 ≤ N →
    ∃ lam : Measure ℝ, (∃ _ : IsProbabilityMeasure lam, True) ∧
      ∀ ξ : ℝ, measureFT lam ξ = tailProduct α' m N ξ := by
  intro m N _hmN
  rcases finiteKernelProduct α' μ hμ ((Finset.range (N + 1)).filter (fun j => m < j)) with
    ⟨lam, hprob, hFT⟩
  refine ⟨lam, hprob, ?_⟩
  intro ξ
  simpa [tailProduct] using hFT ξ

private def tailVariance (α' : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑' k : ℕ, (α' (k + m + 1)) ^ 2

private theorem tailVariance_summable (α' : ℕ → ℝ)
    (hsum : Summable (fun j : ℕ => (α' j) ^ 2)) (m : ℕ) :
    Summable (fun k : ℕ => (α' (k + m + 1)) ^ 2) := by
  have hshift : Summable (fun k : ℕ => (α' (k + (m + 1))) ^ 2) := by
    simpa using
      ((summable_nat_add_iff (G := ℝ) (f := fun j : ℕ => (α' j) ^ 2) (m + 1)).2 hsum)
  simpa [Nat.add_assoc] using hshift

private theorem tailVariance_nonneg (α' : ℕ → ℝ) (m : ℕ) :
    0 ≤ tailVariance α' m := by
  unfold tailVariance
  exact tsum_nonneg (fun k : ℕ => sq_nonneg (α' (k + m + 1)))

private theorem tailVariance_tendsto_zero (α' : ℕ → ℝ)
    (_hsum : Summable (fun j : ℕ => (α' j) ^ 2)) :
    Filter.Tendsto (tailVariance α') Filter.atTop (𝓝 0) := by
  have htail := tendsto_sum_nat_add (G := ℝ) (fun j : ℕ => (α' j) ^ 2)
  have hcomp := htail.comp (Filter.tendsto_add_atTop_nat 1)
  have hfun : (fun m : ℕ => ∑' k : ℕ, (α' (k + (m + 1))) ^ 2) = tailVariance α' := by
    funext m
    unfold tailVariance
    apply tsum_congr
    intro k
    congr 2
  simpa [Function.comp_def, hfun] using hcomp

private theorem infinitePi_isProbabilityMeasure (μ : ℕ → Measure ℝ)
    (hμprob : ∀ j : ℕ, IsProbabilityMeasure (μ j)) :
    IsProbabilityMeasure (Measure.infinitePi μ) := by
  haveI : ∀ j : ℕ, IsProbabilityMeasure (μ j) := hμprob
  infer_instance

private theorem coordinate_map_infinitePi (μ : ℕ → Measure ℝ)
    (hμprob : ∀ j : ℕ, IsProbabilityMeasure (μ j)) (j : ℕ) :
    Measure.map (fun ω : ℕ → ℝ => ω j) (Measure.infinitePi μ) = μ j := by
  haveI : ∀ j : ℕ, IsProbabilityMeasure (μ j) := hμprob
  exact (measurePreserving_eval_infinitePi μ j).map_eq

private theorem coordinate_kernelLaw (α' : ℕ → ℝ) (μ : ℕ → Measure ℝ)
    (hμ : ∀ j : ℕ, KernelLaw (α' j) (μ j)) (j : ℕ) :
    KernelLaw (α' j) (Measure.map (fun ω : ℕ → ℝ => ω j) (Measure.infinitePi μ)) := by
  have hμprob : ∀ j : ℕ, IsProbabilityMeasure (μ j) := fun j => Classical.choose (hμ j).1
  have hmap : Measure.map (fun ω : ℕ → ℝ => ω j) (Measure.infinitePi μ) = μ j :=
    coordinate_map_infinitePi μ hμprob j
  constructor
  · refine ⟨?_, trivial⟩
    rw [hmap]
    exact hμprob j
  · intro ξ
    rw [hmap]
    exact (hμ j).2 ξ

private def finiteTailIndexSet (m N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun j => m < j)

private def finiteTailSum (m N : ℕ) (ω : ℕ → ℝ) : ℝ :=
  ∑ j ∈ finiteTailIndexSet m N, ω j

private theorem finiteTailIndexSet_subset_of_le (m : ℕ) {N N' : ℕ}
    (hNN' : N ≤ N') :
    finiteTailIndexSet m N ⊆ finiteTailIndexSet m N' := by
  intro j hj
  simp [finiteTailIndexSet] at hj ⊢
  omega

private theorem finiteTailIndexSet_sdiff_eq (m N N' : ℕ) (hmN : m ≤ N) :
    finiteTailIndexSet m N' \ finiteTailIndexSet m N = finiteTailIndexSet N N' := by
  ext j
  simp [finiteTailIndexSet]
  omega

private theorem finiteTailSum_sub_eq (m N N' : ℕ) (hmN : m ≤ N) (hNN' : N ≤ N')
    (ω : ℕ → ℝ) :
    finiteTailSum m N' ω - finiteTailSum m N ω = finiteTailSum N N' ω := by
  classical
  have hsub : finiteTailIndexSet m N ⊆ finiteTailIndexSet m N' :=
    finiteTailIndexSet_subset_of_le m hNN'
  have hsdiff :
      finiteTailIndexSet m N' \ finiteTailIndexSet m N = finiteTailIndexSet N N' :=
    finiteTailIndexSet_sdiff_eq m N N' hmN
  have hsum := Finset.sum_sdiff hsub (f := fun j => ω j)
  rw [hsdiff] at hsum
  unfold finiteTailSum
  linarith

private def tailShiftEmbedding (n : ℕ) : ℕ ↪ ℕ where
  toFun r := r + n + 1
  inj' := by
    intro a b h
    have h' : a + (n + 1) = b + (n + 1) := by
      simpa [Nat.add_assoc] using h
    exact Nat.add_right_cancel h'

private theorem finiteTailIndexSet_eq_map_range (n k : ℕ) (hnk : n ≤ k) :
    finiteTailIndexSet n k =
      Finset.map (tailShiftEmbedding n) (Finset.range (k - n)) := by
  ext j
  simp [finiteTailIndexSet, tailShiftEmbedding]
  constructor
  · intro hj
    rcases hj with ⟨hle, hlt⟩
    refine ⟨j - (n + 1), ?_, ?_⟩ <;> omega
  · rintro ⟨r, hr, rfl⟩
    constructor <;> omega

private theorem finiteTailIndexSet_sum_sq_eq_range (α' : ℕ → ℝ)
    (n k : ℕ) (hnk : n ≤ k) :
    (∑ j ∈ finiteTailIndexSet n k, (α' j) ^ 2) =
      ∑ r ∈ Finset.range (k - n), (α' (r + n + 1)) ^ 2 := by
  classical
  rw [finiteTailIndexSet_eq_map_range n k hnk]
  simp [tailShiftEmbedding]

private theorem finiteTailIndexSet_sum_sq_le_tailVariance (α' : ℕ → ℝ)
    (hsum : Summable (fun j : ℕ => (α' j) ^ 2)) (n k : ℕ) (hnk : n ≤ k) :
    (∑ j ∈ finiteTailIndexSet n k, (α' j) ^ 2) ≤ tailVariance α' n := by
  rw [finiteTailIndexSet_sum_sq_eq_range α' n k hnk]
  unfold tailVariance
  exact (tailVariance_summable α' hsum n).sum_le_tsum (Finset.range (k - n))
    (fun r _hr => sq_nonneg (α' (r + n + 1)))

private theorem finiteTailIndexSet_sum_sq_tendsto_tailVariance (α' : ℕ → ℝ)
    (hsum : Summable (fun j : ℕ => (α' j) ^ 2)) (m : ℕ) :
    Filter.Tendsto
      (fun N : ℕ => ∑ j ∈ finiteTailIndexSet m N, (α' j) ^ 2)
      Filter.atTop (𝓝 (tailVariance α' m)) := by
  have hpartial :
      Filter.Tendsto
        (fun K : ℕ => ∑ r ∈ Finset.range K, (α' (r + m + 1)) ^ 2)
        Filter.atTop (𝓝 (tailVariance α' m)) := by
    unfold tailVariance
    exact (tailVariance_summable α' hsum m).hasSum.tendsto_sum_nat
  have hcomp := hpartial.comp (Filter.tendsto_sub_atTop_nat m)
  refine hcomp.congr' ?_
  filter_upwards [Filter.eventually_atTop.mpr ⟨m, fun N hN => hN⟩] with N hN
  exact (finiteTailIndexSet_sum_sq_eq_range α' m N hN).symm

private theorem measurable_finiteTailSum (m N : ℕ) :
    Measurable (finiteTailSum m N) := by
  unfold finiteTailSum finiteTailIndexSet
  fun_prop

private theorem measureFT_eq_charFun (ρ : Measure ℝ) (ξ : ℝ) :
    measureFT ρ ξ = MeasureTheory.charFun ρ (-2 * Real.pi * ξ) := by
  unfold measureFT
  rw [MeasureTheory.charFun_apply]
  congr with y
  congr 1
  simp [RCLike.inner_apply]
  ring_nf

private theorem finiteTailSum_charFun (μ : ℕ → Measure ℝ)
    (hμprob : ∀ j : ℕ, IsProbabilityMeasure (μ j)) (m N : ℕ) :
    MeasureTheory.charFun (Measure.map (finiteTailSum m N) (Measure.infinitePi μ)) =
      ∏ j ∈ finiteTailIndexSet m N,
        MeasureTheory.charFun (Measure.map (fun ω : ℕ → ℝ => ω j) (Measure.infinitePi μ)) := by
  classical
  letI : ∀ j : ℕ, IsProbabilityMeasure (μ j) := hμprob
  have hInd : ProbabilityTheory.iIndepFun
      (fun j (ω : ℕ → ℝ) => ω j) (Measure.infinitePi μ) := by
    simpa using (ProbabilityTheory.iIndepFun_infinitePi (P := μ)
      (X := fun (_ : ℕ) (x : ℝ) => x) (fun _ => measurable_id))
  have h := ProbabilityTheory.iIndepFun.charFun_map_fun_finsetSum_eq_prod
      (P := Measure.infinitePi μ)
      (s := finiteTailIndexSet m N)
      (X := fun j (ω : ℕ → ℝ) => ω j)
      (mX := by intro j _hj; exact (measurable_pi_apply j).aemeasurable)
      (hX := hInd.restrict (finiteTailIndexSet m N))
  change MeasureTheory.charFun
      (Measure.map (fun ω : ℕ → ℝ => ∑ j ∈ finiteTailIndexSet m N, ω j)
        (Measure.infinitePi μ)) =
      ∏ j ∈ finiteTailIndexSet m N,
        MeasureTheory.charFun (Measure.map (fun ω : ℕ → ℝ => ω j) (Measure.infinitePi μ))
  exact h

private theorem finiteTailSum_law_isProbabilityMeasure (μ : ℕ → Measure ℝ)
    (hμprob : ∀ j : ℕ, IsProbabilityMeasure (μ j)) (m N : ℕ) :
    IsProbabilityMeasure (Measure.map (finiteTailSum m N) (Measure.infinitePi μ)) := by
  letI : ∀ j : ℕ, IsProbabilityMeasure (μ j) := hμprob
  exact Measure.isProbabilityMeasure_map
    (μ := Measure.infinitePi μ)
    (measurable_finiteTailSum m N).aemeasurable

private theorem finiteTailSum_law_measureFT (α' : ℕ → ℝ) (μ : ℕ → Measure ℝ)
    (hμ : ∀ j : ℕ, KernelLaw (α' j) (μ j)) (m N : ℕ) :
    ∀ ξ : ℝ,
      measureFT (Measure.map (finiteTailSum m N) (Measure.infinitePi μ)) ξ =
        tailProduct α' m N ξ := by
  classical
  intro ξ
  have hμprob : ∀ j : ℕ, IsProbabilityMeasure (μ j) :=
    fun j => Classical.choose (hμ j).1
  letI : ∀ j : ℕ, IsProbabilityMeasure (μ j) := hμprob
  have hcf := congrFun (finiteTailSum_charFun μ hμprob m N) (-2 * Real.pi * ξ)
  calc
    measureFT (Measure.map (finiteTailSum m N) (Measure.infinitePi μ)) ξ =
        MeasureTheory.charFun (Measure.map (finiteTailSum m N) (Measure.infinitePi μ))
          (-2 * Real.pi * ξ) := measureFT_eq_charFun _ ξ
    _ = ∏ j ∈ finiteTailIndexSet m N,
          MeasureTheory.charFun (Measure.map (fun ω : ℕ → ℝ => ω j) (Measure.infinitePi μ))
            (-2 * Real.pi * ξ) := by
        simpa using hcf
    _ = ∏ j ∈ finiteTailIndexSet m N,
          measureFT (Measure.map (fun ω : ℕ → ℝ => ω j) (Measure.infinitePi μ)) ξ := by
        apply Finset.prod_congr rfl
        intro j _hj
        exact (measureFT_eq_charFun _ ξ).symm
    _ = ∏ j ∈ finiteTailIndexSet m N, expFactor (α' j) ξ := by
        apply Finset.prod_congr rfl
        intro j _hj
        rw [Measure.infinitePi_map_eval μ j]
        exact (hμ j).2 ξ
    _ = tailProduct α' m N ξ := by
        rfl

private theorem finiteKernelProduct_momentsAndFT (α' : ℕ → ℝ) (μ : ℕ → Measure ℝ)
    (hμ : ∀ j : ℕ, KernelLaw (α' j) (μ j)) :
    ∀ F : Finset ℕ,
      ∃ lam : Measure ℝ, (∃ _ : IsProbabilityMeasure lam, True) ∧
        Integrable (fun t : ℝ => t) lam ∧
        Integrable (fun t : ℝ => t ^ 2) lam ∧
        (∫ t : ℝ, t ∂lam) = 0 ∧
        (∫ t : ℝ, t ^ 2 ∂lam) = ∑ j ∈ F, (α' j) ^ 2 ∧
        ∀ ξ : ℝ, measureFT lam ξ = ∏ j ∈ F, expFactor (α' j) ξ := by
  classical
  intro F
  induction F using Finset.induction_on with
  | empty =>
      refine ⟨Measure.dirac (0 : ℝ), ⟨inferInstance, trivial⟩, ?_, ?_, ?_, ?_, ?_⟩
      · exact MeasureTheory.integrable_dirac (by simp)
      · exact MeasureTheory.integrable_dirac (by simp)
      · rw [MeasureTheory.integral_dirac]
      · rw [MeasureTheory.integral_dirac]
        simp
      · intro ξ
        unfold measureFT
        rw [MeasureTheory.integral_dirac]
        simp
  | insert a s ha hs =>
      rcases hs with
        ⟨lam, hprob_lam, hlam1, hlam2, hlam_mean, hlam_second, hFT_lam⟩
      rcases hprob_lam with ⟨hlam_prob, _⟩
      rcases (hμ a).1 with ⟨hμa_prob, _⟩
      haveI : IsProbabilityMeasure lam := hlam_prob
      haveI : IsProbabilityMeasure (μ a) := hμa_prob
      rcases kernelLaw_moments (α' a) (μ a) (hμ a) with
        ⟨hμa1, hμa2, hμa_mean, hμa_second⟩
      let lam' : Measure ℝ := finiteMeasureConv (μ a) lam
      have hprob' : IsProbabilityMeasure lam' := by
        dsimp [lam']
        exact finiteMeasureConv_isProbabilityMeasure (μ a) lam
      rcases finiteMeasureConv_moments (μ a) lam hμa1 hμa2 hlam1 hlam2
          hμa_mean hlam_mean ((α' a) ^ 2) (∑ j ∈ s, (α' j) ^ 2)
          hμa_second hlam_second with
        ⟨hconv1, hconv2, hconv_mean, hconv_second⟩
      refine ⟨lam', ⟨hprob', trivial⟩, hconv1, hconv2, hconv_mean, ?_, ?_⟩
      · calc
          ∫ t : ℝ, t ^ 2 ∂lam' = (α' a) ^ 2 + ∑ j ∈ s, (α' j) ^ 2 :=
            hconv_second
          _ = ∑ j ∈ insert a s, (α' j) ^ 2 := by
            rw [Finset.sum_insert ha]
      · intro ξ
        calc
          measureFT lam' ξ = measureFT (μ a) ξ * measureFT lam ξ := by
            dsimp [lam']
            exact finiteMeasureConv_FT (μ a) lam ξ
          _ = expFactor (α' a) ξ * ∏ j ∈ s, expFactor (α' j) ξ := by
            rw [(hμ a).2 ξ, hFT_lam ξ]
          _ = ∏ j ∈ insert a s, expFactor (α' j) ξ := by
            simpa using (Finset.prod_insert (s := s) (a := a)
              (f := fun j : ℕ => expFactor (α' j) ξ) ha).symm

private theorem finiteTailSum_law_moments (α' : ℕ → ℝ) (μ : ℕ → Measure ℝ)
    (hμ : ∀ j : ℕ, KernelLaw (α' j) (μ j)) (m N : ℕ) :
    Integrable (fun t : ℝ => t)
        (Measure.map (finiteTailSum m N) (Measure.infinitePi μ)) ∧
      (∫ t : ℝ, t ∂Measure.map (finiteTailSum m N) (Measure.infinitePi μ)) = 0 ∧
      Integrable (fun t : ℝ => t ^ 2)
        (Measure.map (finiteTailSum m N) (Measure.infinitePi μ)) ∧
      (∫ t : ℝ, t ^ 2 ∂Measure.map (finiteTailSum m N) (Measure.infinitePi μ)) =
        ∑ j ∈ finiteTailIndexSet m N, (α' j) ^ 2 := by
  classical
  let law : Measure ℝ := Measure.map (finiteTailSum m N) (Measure.infinitePi μ)
  have hμprob : ∀ j : ℕ, IsProbabilityMeasure (μ j) :=
    fun j => Classical.choose (hμ j).1
  have hlawprob : IsProbabilityMeasure law := by
    dsimp [law]
    exact finiteTailSum_law_isProbabilityMeasure μ hμprob m N
  rcases finiteKernelProduct_momentsAndFT α' μ hμ (finiteTailIndexSet m N) with
    ⟨lam, hprob_lam, hlam1, hlam2, hlam_mean, hlam_second, hFT_lam⟩
  rcases hprob_lam with ⟨hlam_prob, _⟩
  letI : IsProbabilityMeasure law := hlawprob
  letI : IsProbabilityMeasure lam := hlam_prob
  have hsame : law = lam := by
    exact measure_unique law lam (fun ξ => by
      calc
        measureFT law ξ = tailProduct α' m N ξ := by
          dsimp [law]
          exact finiteTailSum_law_measureFT α' μ hμ m N ξ
        _ = ∏ j ∈ finiteTailIndexSet m N, expFactor (α' j) ξ := by
          rfl
        _ = measureFT lam ξ := (hFT_lam ξ).symm)
  change Integrable (fun t : ℝ => t) law ∧
    (∫ t : ℝ, t ∂law) = 0 ∧
    Integrable (fun t : ℝ => t ^ 2) law ∧
    (∫ t : ℝ, t ^ 2 ∂law) = ∑ j ∈ finiteTailIndexSet m N, (α' j) ^ 2
  rw [hsame]
  exact ⟨hlam1, hlam_mean, hlam2, hlam_second⟩

private theorem finiteTailSum_memLp_two (α' : ℕ → ℝ) (μ : ℕ → Measure ℝ)
    (hμ : ∀ j : ℕ, KernelLaw (α' j) (μ j)) (m N : ℕ) :
    MemLp (finiteTailSum m N) 2 (Measure.infinitePi μ) := by
  have hmom := finiteTailSum_law_moments α' μ hμ m N
  have hsq_law :
      Integrable (fun t : ℝ => t ^ 2)
        (Measure.map (finiteTailSum m N) (Measure.infinitePi μ)) := hmom.2.2.1
  have hsq_prod :
      Integrable (fun ω : ℕ → ℝ => (finiteTailSum m N ω) ^ 2)
        (Measure.infinitePi μ) := by
    have hmap := (integrable_map_measure
      (μ := Measure.infinitePi μ)
      (f := finiteTailSum m N)
      (g := fun t : ℝ => t ^ 2)
      (by fun_prop)
      (measurable_finiteTailSum m N).aemeasurable).1 hsq_law
    simpa [Function.comp_def] using hmap
  exact (memLp_two_iff_integrable_sq
    (μ := Measure.infinitePi μ)
    ((measurable_finiteTailSum m N).aestronglyMeasurable)).2 hsq_prod

private theorem finiteTailSum_square_integral (α' : ℕ → ℝ) (μ : ℕ → Measure ℝ)
    (hμ : ∀ j : ℕ, KernelLaw (α' j) (μ j)) (m N : ℕ) :
    Integrable (fun ω : ℕ → ℝ => (finiteTailSum m N ω) ^ 2)
        (Measure.infinitePi μ) ∧
      (∫ ω : ℕ → ℝ, (finiteTailSum m N ω) ^ 2 ∂Measure.infinitePi μ) =
        ∑ j ∈ finiteTailIndexSet m N, (α' j) ^ 2 := by
  have hmom := finiteTailSum_law_moments α' μ hμ m N
  have hsq_law :
      Integrable (fun t : ℝ => t ^ 2)
        (Measure.map (finiteTailSum m N) (Measure.infinitePi μ)) := hmom.2.2.1
  have hsq_prod :
      Integrable (fun ω : ℕ → ℝ => (finiteTailSum m N ω) ^ 2)
        (Measure.infinitePi μ) := by
    have hmap := (integrable_map_measure
      (μ := Measure.infinitePi μ)
      (f := finiteTailSum m N)
      (g := fun t : ℝ => t ^ 2)
      (by fun_prop)
      (measurable_finiteTailSum m N).aemeasurable).1 hsq_law
    simpa [Function.comp_def] using hmap
  refine ⟨hsq_prod, ?_⟩
  have hmap_int :
      (∫ t : ℝ, t ^ 2 ∂Measure.map (finiteTailSum m N) (Measure.infinitePi μ)) =
        ∫ ω : ℕ → ℝ, (finiteTailSum m N ω) ^ 2 ∂Measure.infinitePi μ := by
    rw [MeasureTheory.integral_map]
    · exact (measurable_finiteTailSum m N).aemeasurable
    · fun_prop
  exact hmap_int.symm.trans hmom.2.2.2

private theorem finiteTailSum_integral (α' : ℕ → ℝ) (μ : ℕ → Measure ℝ)
    (hμ : ∀ j : ℕ, KernelLaw (α' j) (μ j)) (m N : ℕ) :
    Integrable (finiteTailSum m N) (Measure.infinitePi μ) ∧
      (∫ ω : ℕ → ℝ, finiteTailSum m N ω ∂Measure.infinitePi μ) = 0 := by
  have hmom := finiteTailSum_law_moments α' μ hμ m N
  have hint_law :
      Integrable (fun t : ℝ => t)
        (Measure.map (finiteTailSum m N) (Measure.infinitePi μ)) := hmom.1
  have hint_prod : Integrable (finiteTailSum m N) (Measure.infinitePi μ) := by
    have hmap := (integrable_map_measure
      (μ := Measure.infinitePi μ)
      (f := finiteTailSum m N)
      (g := fun t : ℝ => t)
      (by fun_prop)
      (measurable_finiteTailSum m N).aemeasurable).1 hint_law
    simpa [Function.comp_def] using hmap
  refine ⟨hint_prod, ?_⟩
  have hmap_int :
      (∫ t : ℝ, t ∂Measure.map (finiteTailSum m N) (Measure.infinitePi μ)) =
        ∫ ω : ℕ → ℝ, finiteTailSum m N ω ∂Measure.infinitePi μ := by
    rw [MeasureTheory.integral_map]
    · exact (measurable_finiteTailSum m N).aemeasurable
    · fun_prop
  exact hmap_int.symm.trans hmom.2.1

private theorem finiteTailSum_sub_square_integral (α' : ℕ → ℝ) (μ : ℕ → Measure ℝ)
    (hμ : ∀ j : ℕ, KernelLaw (α' j) (μ j)) (m N N' : ℕ)
    (hmN : m ≤ N) (hNN' : N ≤ N') :
    Integrable
        (fun ω : ℕ → ℝ => (finiteTailSum m N' ω - finiteTailSum m N ω) ^ 2)
        (Measure.infinitePi μ) ∧
      (∫ ω : ℕ → ℝ, (finiteTailSum m N' ω - finiteTailSum m N ω) ^ 2
          ∂Measure.infinitePi μ) =
        ∑ j ∈ finiteTailIndexSet N N', (α' j) ^ 2 := by
  have hblock := finiteTailSum_square_integral α' μ hμ N N'
  have hcongr :
      (fun ω : ℕ → ℝ => (finiteTailSum m N' ω - finiteTailSum m N ω) ^ 2)
        =ᵐ[Measure.infinitePi μ]
      (fun ω : ℕ → ℝ => (finiteTailSum N N' ω) ^ 2) := by
    filter_upwards with ω
    rw [finiteTailSum_sub_eq m N N' hmN hNN' ω]
  constructor
  · exact (integrable_congr hcongr).mpr hblock.1
  · calc
      ∫ ω : ℕ → ℝ, (finiteTailSum m N' ω - finiteTailSum m N ω) ^ 2
          ∂Measure.infinitePi μ =
          ∫ ω : ℕ → ℝ, (finiteTailSum N N' ω) ^ 2 ∂Measure.infinitePi μ := by
        exact integral_congr_ae hcongr
      _ = ∑ j ∈ finiteTailIndexSet N N', (α' j) ^ 2 := hblock.2

private def finiteTailLp (α' : ℕ → ℝ) (μ : ℕ → Measure ℝ)
    (hμ : ∀ j : ℕ, KernelLaw (α' j) (μ j)) (m N : ℕ) :
    Lp ℝ 2 (Measure.infinitePi μ) :=
  (finiteTailSum_memLp_two α' μ hμ m N).toLp (finiteTailSum m N)

private theorem finiteTailLp_coeFn (α' : ℕ → ℝ) (μ : ℕ → Measure ℝ)
    (hμ : ∀ j : ℕ, KernelLaw (α' j) (μ j)) (m N : ℕ) :
    ⇑(finiteTailLp α' μ hμ m N) =ᵐ[Measure.infinitePi μ] finiteTailSum m N := by
  exact (finiteTailSum_memLp_two α' μ hμ m N).coeFn_toLp

private theorem finiteTailLp_sub_eq (α' : ℕ → ℝ) (μ : ℕ → Measure ℝ)
    (hμ : ∀ j : ℕ, KernelLaw (α' j) (μ j)) (m N N' : ℕ)
    (hmN : m ≤ N) (hNN' : N ≤ N') :
    finiteTailLp α' μ hμ m N' - finiteTailLp α' μ hμ m N =
      finiteTailLp α' μ hμ N N' := by
  let hN' := finiteTailSum_memLp_two α' μ hμ m N'
  let hN := finiteTailSum_memLp_two α' μ hμ m N
  let hblock := finiteTailSum_memLp_two α' μ hμ N N'
  calc
    finiteTailLp α' μ hμ m N' - finiteTailLp α' μ hμ m N =
        (hN'.sub hN).toLp (finiteTailSum m N' - finiteTailSum m N) := by
      dsimp [finiteTailLp, hN', hN]
      exact (MemLp.toLp_sub hN' hN).symm
    _ = finiteTailLp α' μ hμ N N' := by
      dsimp [finiteTailLp, hblock]
      exact MemLp.toLp_congr (hN'.sub hN) hblock
        (Filter.Eventually.of_forall (fun ω => by
          exact finiteTailSum_sub_eq m N N' hmN hNN' ω))

private theorem memLp_two_norm_sq_eq_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ) (hf : MemLp f 2 P) :
    ‖hf.toLp f‖ ^ 2 = ∫ ω, f ω ^ 2 ∂P := by
  rw [Lp.norm_toLp]
  rw [toReal_eLpNorm hf.aestronglyMeasurable]
  rw [lpNorm_eq_integral_norm_rpow_toReal (p := (2 : ℝ≥0∞))
    (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  norm_num
  let B : ℝ := ∫ ω, f ω ^ 2 ∂P
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact integral_nonneg (fun ω => sq_nonneg (f ω))
  have hpow : (B ^ (1 / (2 : ℝ))) ^ 2 = B := by
    simpa using (Real.rpow_inv_natCast_pow (x := B) (n := 2) hB_nonneg (by norm_num))
  change (B ^ (1 / (2 : ℝ))) ^ 2 = ∫ ω, f ω ^ 2 ∂P
  rw [hpow]

private theorem finiteTailLp_norm_sq (α' : ℕ → ℝ) (μ : ℕ → Measure ℝ)
    (hμ : ∀ j : ℕ, KernelLaw (α' j) (μ j)) (m N : ℕ) :
    ‖finiteTailLp α' μ hμ m N‖ ^ 2 =
      ∑ j ∈ finiteTailIndexSet m N, (α' j) ^ 2 := by
  calc
    ‖finiteTailLp α' μ hμ m N‖ ^ 2 =
        ∫ ω : ℕ → ℝ, (finiteTailSum m N ω) ^ 2 ∂Measure.infinitePi μ := by
      exact memLp_two_norm_sq_eq_integral_sq (Measure.infinitePi μ)
        (finiteTailSum m N) (finiteTailSum_memLp_two α' μ hμ m N)
    _ = ∑ j ∈ finiteTailIndexSet m N, (α' j) ^ 2 :=
      (finiteTailSum_square_integral α' μ hμ m N).2

private theorem finiteTailLp_dist_sq (α' : ℕ → ℝ) (μ : ℕ → Measure ℝ)
    (hμ : ∀ j : ℕ, KernelLaw (α' j) (μ j)) (m N N' : ℕ)
    (hmN : m ≤ N) (hNN' : N ≤ N') :
    dist (finiteTailLp α' μ hμ m N') (finiteTailLp α' μ hμ m N) ^ 2 =
      ∑ j ∈ finiteTailIndexSet N N', (α' j) ^ 2 := by
  rw [dist_eq_norm]
  rw [finiteTailLp_sub_eq α' μ hμ m N N' hmN hNN']
  exact finiteTailLp_norm_sq α' μ hμ N N'

private theorem finiteTailLp_cauchy (α' : ℕ → ℝ) (μ : ℕ → Measure ℝ)
    (hμ : ∀ j : ℕ, KernelLaw (α' j) (μ j))
    (hsum : Summable (fun j : ℕ => (α' j) ^ 2)) (m : ℕ) :
    CauchySeq (fun N : ℕ => finiteTailLp α' μ hμ m N) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hev : ∀ᶠ n in Filter.atTop, tailVariance α' n < ε ^ 2 :=
    (tailVariance_tendsto_zero α' hsum).eventually (gt_mem_nhds hε2)
  rcases Filter.eventually_atTop.mp hev with ⟨N0, hN0⟩
  refine ⟨max m N0, ?_⟩
  intro n hn k hk
  have hm_n : m ≤ n := le_trans (le_max_left m N0) hn
  have hm_k : m ≤ k := le_trans (le_max_left m N0) hk
  have hN0_n : N0 ≤ n := le_trans (le_max_right m N0) hn
  have hN0_k : N0 ≤ k := le_trans (le_max_right m N0) hk
  by_cases hnk : n ≤ k
  · have hsumsq_le :
        (∑ j ∈ finiteTailIndexSet n k, (α' j) ^ 2) ≤ tailVariance α' n :=
      finiteTailIndexSet_sum_sq_le_tailVariance α' hsum n k hnk
    have htail_lt : tailVariance α' n < ε ^ 2 := hN0 n hN0_n
    have hdist_sq :
        dist (finiteTailLp α' μ hμ m n) (finiteTailLp α' μ hμ m k) ^ 2 < ε ^ 2 := by
      rw [dist_comm]
      rw [finiteTailLp_dist_sq α' μ hμ m n k hm_n hnk]
      exact lt_of_le_of_lt hsumsq_le htail_lt
    exact lt_of_pow_lt_pow_left₀ 2 hε.le hdist_sq
  · have hkn : k ≤ n := Nat.le_of_not_ge hnk
    have hsumsq_le :
        (∑ j ∈ finiteTailIndexSet k n, (α' j) ^ 2) ≤ tailVariance α' k :=
      finiteTailIndexSet_sum_sq_le_tailVariance α' hsum k n hkn
    have htail_lt : tailVariance α' k < ε ^ 2 := hN0 k hN0_k
    have hdist_sq :
        dist (finiteTailLp α' μ hμ m n) (finiteTailLp α' μ hμ m k) ^ 2 < ε ^ 2 := by
      rw [finiteTailLp_dist_sq α' μ hμ m k n hm_k hkn]
      exact lt_of_le_of_lt hsumsq_le htail_lt
    exact lt_of_pow_lt_pow_left₀ 2 hε.le hdist_sq

private def tailLpLimit (α' : ℕ → ℝ) (μ : ℕ → Measure ℝ)
    (hμ : ∀ j : ℕ, KernelLaw (α' j) (μ j))
    (hsum : Summable (fun j : ℕ => (α' j) ^ 2)) (m : ℕ) :
    Lp ℝ 2 (Measure.infinitePi μ) :=
  Classical.choose (cauchySeq_tendsto_of_complete
    (finiteTailLp_cauchy α' μ hμ hsum m))

private theorem finiteTailLp_tendsto_tailLpLimit (α' : ℕ → ℝ) (μ : ℕ → Measure ℝ)
    (hμ : ∀ j : ℕ, KernelLaw (α' j) (μ j))
    (hsum : Summable (fun j : ℕ => (α' j) ^ 2)) (m : ℕ) :
    Filter.Tendsto (fun N : ℕ => finiteTailLp α' μ hμ m N)
      Filter.atTop (𝓝 (tailLpLimit α' μ hμ hsum m)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete
    (finiteTailLp_cauchy α' μ hμ hsum m))

private theorem tailLpLimit_norm_sq (α' : ℕ → ℝ) (μ : ℕ → Measure ℝ)
    (hμ : ∀ j : ℕ, KernelLaw (α' j) (μ j))
    (hsum : Summable (fun j : ℕ => (α' j) ^ 2)) (m : ℕ) :
    ‖tailLpLimit α' μ hμ hsum m‖ ^ 2 = tailVariance α' m := by
  have hnorm :
      Filter.Tendsto
        (fun N : ℕ => ‖finiteTailLp α' μ hμ m N‖ ^ 2)
        Filter.atTop (𝓝 (‖tailLpLimit α' μ hμ hsum m‖ ^ 2)) :=
    (finiteTailLp_tendsto_tailLpLimit α' μ hμ hsum m).norm.pow 2
  have hvar :
      Filter.Tendsto
        (fun N : ℕ => ‖finiteTailLp α' μ hμ m N‖ ^ 2)
        Filter.atTop (𝓝 (tailVariance α' m)) := by
    refine (finiteTailIndexSet_sum_sq_tendsto_tailVariance α' hsum m).congr' ?_
    exact Filter.Eventually.of_forall (fun N =>
      (finiteTailLp_norm_sq α' μ hμ m N).symm)
  exact tendsto_nhds_unique hnorm hvar

private theorem finiteTailSum_tendsto_L1_tailLpLimit (α' : ℕ → ℝ)
    (μ : ℕ → Measure ℝ) (hμ : ∀ j : ℕ, KernelLaw (α' j) (μ j))
    (hsum : Summable (fun j : ℕ => (α' j) ^ 2)) (m : ℕ) :
    Filter.Tendsto
      (fun N : ℕ =>
        eLpNorm
          (fun ω : ℕ → ℝ =>
            finiteTailSum m N ω - tailLpLimit α' μ hμ hsum m ω)
          1 (Measure.infinitePi μ))
      Filter.atTop (𝓝 0) := by
  let P : Measure (ℕ → ℝ) := Measure.infinitePi μ
  let S : Lp ℝ 2 P := tailLpLimit α' μ hμ hsum m
  have hμprob : ∀ j : ℕ, IsProbabilityMeasure (μ j) :=
    fun j => Classical.choose (hμ j).1
  haveI : IsProbabilityMeasure P := infinitePi_isProbabilityMeasure μ hμprob
  have hdist :
      Filter.Tendsto
        (fun N : ℕ => dist (finiteTailLp α' μ hμ m N) S)
        Filter.atTop (𝓝 0) := by
    exact (tendsto_iff_dist_tendsto_zero).1
      (finiteTailLp_tendsto_tailLpLimit α' μ hμ hsum m)
  have htwo :
      Filter.Tendsto
        (fun N : ℕ =>
          eLpNorm
            (⇑(finiteTailLp α' μ hμ m N) - ⇑S)
            2 P)
        Filter.atTop (𝓝 0) := by
    have hed :
        Filter.Tendsto
          (fun N : ℕ => edist (finiteTailLp α' μ hμ m N) S)
          Filter.atTop (𝓝 0) := by
      simpa [edist_dist] using ENNReal.tendsto_ofReal hdist
    simpa [MeasureTheory.Lp.edist_def, P] using hed
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by exact tendsto_const_nhds)
    htwo ?_ ?_
  · intro N
    exact bot_le
  · intro N
    let fN : Lp ℝ 2 P := finiteTailLp α' μ hμ m N
    have hdiff :
        (fun ω : ℕ → ℝ =>
            finiteTailSum m N ω - S ω)
          =ᵐ[P] (⇑fN - ⇑S) := by
      filter_upwards [finiteTailLp_coeFn α' μ hμ m N] with ω hω
      change finiteTailSum m N ω - S ω = fN ω - S ω
      rw [← hω]
    calc
      eLpNorm
          (fun ω : ℕ → ℝ =>
            finiteTailSum m N ω - tailLpLimit α' μ hμ hsum m ω)
          1 (Measure.infinitePi μ)
          = eLpNorm (⇑fN - ⇑S) 1 P := by
            simpa [P, S, fN] using eLpNorm_congr_ae hdiff
      _ ≤ eLpNorm (⇑fN - ⇑S) 2 P := by
        exact eLpNorm_le_eLpNorm_of_exponent_le
          (μ := P) (f := ⇑fN - ⇑S) (p := 1) (q := 2)
          (by norm_num)
          ((Lp.aestronglyMeasurable fN).sub (Lp.aestronglyMeasurable S))

private theorem finiteTailExp_tendsto_L1_tailLpLimit (α' : ℕ → ℝ)
    (μ : ℕ → Measure ℝ) (hμ : ∀ j : ℕ, KernelLaw (α' j) (μ j))
    (hsum : Summable (fun j : ℕ => (α' j) ^ 2)) (m : ℕ) (c : ℝ) :
    Filter.Tendsto
      (fun N : ℕ =>
        eLpNorm
          ((fun ω : ℕ → ℝ =>
              Complex.exp (Complex.I * (c * finiteTailSum m N ω))) -
            (fun ω : ℕ → ℝ =>
              Complex.exp (Complex.I * (c * tailLpLimit α' μ hμ hsum m ω))))
          1 (Measure.infinitePi μ))
      Filter.atTop (𝓝 0) := by
  let P : Measure (ℕ → ℝ) := Measure.infinitePi μ
  let S : Lp ℝ 2 P := tailLpLimit α' μ hμ hsum m
  have hreal :
      Filter.Tendsto
        (fun N : ℕ =>
          eLpNorm
            (fun ω : ℕ → ℝ =>
              finiteTailSum m N ω - S ω)
            1 P)
        Filter.atTop (𝓝 0) := by
    simpa [P, S] using finiteTailSum_tendsto_L1_tailLpLimit α' μ hμ hsum m
  have hupper :
      Filter.Tendsto
        (fun N : ℕ =>
          ‖c‖ₑ *
            eLpNorm
              (fun ω : ℕ → ℝ =>
                finiteTailSum m N ω - S ω)
              1 P)
        Filter.atTop (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    by_cases hc0 : ‖c‖ₑ = 0
    · exact Filter.Eventually.of_forall (fun N => by
        rw [hc0, zero_mul]
        exact bot_le)
    · have hctop : ‖c‖ₑ ≠ (∞ : ℝ≥0∞) := enorm_ne_top
      have hδpos : 0 < ε / ‖c‖ₑ := ENNReal.div_pos (ne_of_gt hε) hctop
      have hev :=
        (ENNReal.tendsto_nhds_zero.1 hreal) (ε / ‖c‖ₑ) hδpos
      filter_upwards [hev] with N hN
      calc
        ‖c‖ₑ *
            eLpNorm
              (fun ω : ℕ → ℝ =>
                finiteTailSum m N ω - S ω)
              1 P
            ≤ ‖c‖ₑ * (ε / ‖c‖ₑ) := by
              exact mul_le_mul_right hN ‖c‖ₑ
        _ = ε := ENNReal.mul_div_cancel hc0 hctop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by exact tendsto_const_nhds)
    hupper ?_ ?_
  · intro N
    exact bot_le
  · intro N
    calc
      eLpNorm
          ((fun ω : ℕ → ℝ =>
              Complex.exp (Complex.I * (c * finiteTailSum m N ω))) -
            (fun ω : ℕ → ℝ =>
              Complex.exp (Complex.I * (c * tailLpLimit α' μ hμ hsum m ω))))
          1 (Measure.infinitePi μ)
          = eLpNorm
              ((fun ω : ℕ → ℝ =>
                  Complex.exp (Complex.I * (c * finiteTailSum m N ω))) -
                (fun ω : ℕ → ℝ =>
                  Complex.exp (Complex.I * (c * S ω))))
              1 P := by
            rfl
      _ ≤ eLpNorm
            (fun ω : ℕ → ℝ =>
              c • (finiteTailSum m N ω - S ω))
            1 P := by
        apply eLpNorm_mono_ae
        filter_upwards with ω
        have hlip := exp_lip (c * finiteTailSum m N ω) (c * S ω)
        simpa [Pi.sub_apply, Real.norm_eq_abs, smul_eq_mul, mul_sub] using hlip
      _ = ‖c‖ₑ *
            eLpNorm
              (fun ω : ℕ → ℝ =>
                finiteTailSum m N ω - S ω)
              1 P := by
        exact eLpNorm_const_smul c
          (fun ω : ℕ → ℝ => finiteTailSum m N ω - S ω) 1 P

private theorem integrable_complex_exp_I_mul {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f P) (c : ℝ) :
    Integrable (fun ω => Complex.exp (Complex.I * (c * f ω))) P := by
  exact Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall (fun ω => by
    calc
      ‖Complex.exp (Complex.I * (↑c * ↑(f ω)))‖ =
          ‖Complex.exp (Complex.I * ↑(c * f ω))‖ := by
            congr 2
            norm_num
      _ = 1 := Complex.norm_exp_I_mul_ofReal (c * f ω)
      _ ≤ 1 := le_rfl))

private def tailLimitMeasure (α' : ℕ → ℝ) (μ : ℕ → Measure ℝ)
    (hμ : ∀ j : ℕ, KernelLaw (α' j) (μ j))
    (hsum : Summable (fun j : ℕ => (α' j) ^ 2)) (m : ℕ) : Measure ℝ :=
  Measure.map (fun ω : ℕ → ℝ => tailLpLimit α' μ hμ hsum m ω) (Measure.infinitePi μ)

private theorem tailLimitMeasure_isProbabilityMeasure (α' : ℕ → ℝ)
    (μ : ℕ → Measure ℝ) (hμ : ∀ j : ℕ, KernelLaw (α' j) (μ j))
    (hsum : Summable (fun j : ℕ => (α' j) ^ 2)) (m : ℕ) :
    IsProbabilityMeasure (tailLimitMeasure α' μ hμ hsum m) := by
  have hμprob : ∀ j : ℕ, IsProbabilityMeasure (μ j) :=
    fun j => Classical.choose (hμ j).1
  haveI : IsProbabilityMeasure (Measure.infinitePi μ) :=
    infinitePi_isProbabilityMeasure μ hμprob
  unfold tailLimitMeasure
  exact Measure.isProbabilityMeasure_map
    (Lp.aestronglyMeasurable (tailLpLimit α' μ hμ hsum m)).aemeasurable

private theorem tailLimitMeasure_second_moment (α' : ℕ → ℝ)
    (μ : ℕ → Measure ℝ) (hμ : ∀ j : ℕ, KernelLaw (α' j) (μ j))
    (hsum : Summable (fun j : ℕ => (α' j) ^ 2)) (m : ℕ) :
    Integrable (fun t : ℝ => t ^ 2) (tailLimitMeasure α' μ hμ hsum m) ∧
      (∫ t : ℝ, t ^ 2 ∂tailLimitMeasure α' μ hμ hsum m) = tailVariance α' m := by
  let S : Lp ℝ 2 (Measure.infinitePi μ) := tailLpLimit α' μ hμ hsum m
  have hS_sq_prod : Integrable (fun ω : ℕ → ℝ => (S ω) ^ 2) (Measure.infinitePi μ) :=
    (memLp_two_iff_integrable_sq (Lp.aestronglyMeasurable S)).1 (Lp.memLp S)
  have hS_aemeas : AEMeasurable (fun ω : ℕ → ℝ => S ω) (Measure.infinitePi μ) :=
    (Lp.aestronglyMeasurable S).aemeasurable
  have hS_sq_law :
      Integrable (fun t : ℝ => t ^ 2) (tailLimitMeasure α' μ hμ hsum m) := by
    unfold tailLimitMeasure
    exact (integrable_map_measure
      (μ := Measure.infinitePi μ)
      (f := fun ω : ℕ → ℝ => S ω)
      (g := fun t : ℝ => t ^ 2)
      (by fun_prop) hS_aemeas).2 hS_sq_prod
  refine ⟨hS_sq_law, ?_⟩
  have hmap_int :
      (∫ t : ℝ, t ^ 2 ∂tailLimitMeasure α' μ hμ hsum m) =
        ∫ ω : ℕ → ℝ, (S ω) ^ 2 ∂Measure.infinitePi μ := by
    unfold tailLimitMeasure
    rw [MeasureTheory.integral_map]
    · exact hS_aemeas
    · fun_prop
  have hnorm_sq := memLp_two_norm_sq_eq_integral_sq
    (Measure.infinitePi μ) (fun ω : ℕ → ℝ => S ω) (Lp.memLp S)
  rw [Lp.toLp_coeFn S (Lp.memLp S)] at hnorm_sq
  calc
    (∫ t : ℝ, t ^ 2 ∂tailLimitMeasure α' μ hμ hsum m) =
        ∫ ω : ℕ → ℝ, (S ω) ^ 2 ∂Measure.infinitePi μ := hmap_int
    _ = ‖S‖ ^ 2 := hnorm_sq.symm
    _ = tailVariance α' m := tailLpLimit_norm_sq α' μ hμ hsum m

private theorem tailLimitMeasure_mean_zero (α' : ℕ → ℝ)
    (μ : ℕ → Measure ℝ) (hμ : ∀ j : ℕ, KernelLaw (α' j) (μ j))
    (hsum : Summable (fun j : ℕ => (α' j) ^ 2)) (m : ℕ) :
    Integrable (fun t : ℝ => t) (tailLimitMeasure α' μ hμ hsum m) ∧
      (∫ t : ℝ, t ∂tailLimitMeasure α' μ hμ hsum m) = 0 := by
  let P : Measure (ℕ → ℝ) := Measure.infinitePi μ
  let S : Lp ℝ 2 P := tailLpLimit α' μ hμ hsum m
  have hμprob : ∀ j : ℕ, IsProbabilityMeasure (μ j) :=
    fun j => Classical.choose (hμ j).1
  haveI : IsProbabilityMeasure P := infinitePi_isProbabilityMeasure μ hμprob
  have hS_int_prod : Integrable (fun ω : ℕ → ℝ => S ω) P := by
    exact MeasureTheory.MemLp.integrable (q := (2 : ℝ≥0∞)) (by norm_num) (Lp.memLp S)
  have hS_int_comp :
      Integrable ((fun t : ℝ => t) ∘ (fun ω : ℕ → ℝ => S ω)) P := by
    change Integrable (fun ω : ℕ → ℝ => S ω) P
    exact hS_int_prod
  have hS_aemeas : AEMeasurable (fun ω : ℕ → ℝ => S ω) P :=
    (Lp.aestronglyMeasurable S).aemeasurable
  have hint_law :
      Integrable (fun t : ℝ => t) (tailLimitMeasure α' μ hμ hsum m) := by
    unfold tailLimitMeasure
    exact (integrable_map_measure
      (μ := Measure.infinitePi μ)
      (f := fun ω : ℕ → ℝ => S ω)
      (g := fun t : ℝ => t)
      (by fun_prop) hS_aemeas).2 (by
        simpa [P, S] using hS_int_comp)
  refine ⟨hint_law, ?_⟩
  have hmap_int :
      (∫ t : ℝ, t ∂tailLimitMeasure α' μ hμ hsum m) =
        ∫ ω : ℕ → ℝ, S ω ∂P := by
    unfold tailLimitMeasure
    rw [MeasureTheory.integral_map]
    · exact hS_aemeas
    · fun_prop
  have htend_int :
      Filter.Tendsto
        (fun N : ℕ => ∫ ω : ℕ → ℝ, finiteTailSum m N ω ∂P)
        Filter.atTop (𝓝 (∫ ω : ℕ → ℝ, S ω ∂P)) := by
    exact MeasureTheory.tendsto_integral_of_L1'
      (fun ω : ℕ → ℝ => S ω)
      (Lp.aestronglyMeasurable S)
      (Filter.Eventually.of_forall (fun N => by
        simpa [P] using (finiteTailSum_integral α' μ hμ m N).1))
      (by
        refine (finiteTailSum_tendsto_L1_tailLpLimit α' μ hμ hsum m).congr' ?_
        exact Filter.Eventually.of_forall (fun N => by
          apply eLpNorm_congr_ae
          filter_upwards with ω
          rfl))
  have hzero_tend :
      Filter.Tendsto
        (fun N : ℕ => ∫ ω : ℕ → ℝ, finiteTailSum m N ω ∂P)
        Filter.atTop (𝓝 0) := by
    refine (tendsto_const_nhds (x := (0 : ℝ))).congr' ?_
    exact Filter.Eventually.of_forall (fun N => by
      simpa [P] using (finiteTailSum_integral α' μ hμ m N).2.symm)
  have hS_zero : (∫ ω : ℕ → ℝ, S ω ∂P) = 0 :=
    tendsto_nhds_unique htend_int hzero_tend
  exact hmap_int.trans hS_zero

private theorem tailLimitMeasure_charfun (α' : ℕ → ℝ)
    (μ : ℕ → Measure ℝ) (hμ : ∀ j : ℕ, KernelLaw (α' j) (μ j))
    (hsum : Summable (fun j : ℕ => (α' j) ^ 2)) (m : ℕ) (ξ : ℝ) :
    Filter.Tendsto (fun N : ℕ => tailProduct α' m N ξ)
      Filter.atTop (𝓝 (measureFT (tailLimitMeasure α' μ hμ hsum m) ξ)) := by
  let P : Measure (ℕ → ℝ) := Measure.infinitePi μ
  let S : Lp ℝ 2 P := tailLpLimit α' μ hμ hsum m
  let c : ℝ := -2 * Real.pi * ξ
  have hμprob : ∀ j : ℕ, IsProbabilityMeasure (μ j) :=
    fun j => Classical.choose (hμ j).1
  haveI : IsProbabilityMeasure P := infinitePi_isProbabilityMeasure μ hμprob
  have hlim_int :
      Filter.Tendsto
        (fun N : ℕ =>
          ∫ ω : ℕ → ℝ,
            Complex.exp (Complex.I * (c * finiteTailSum m N ω)) ∂P)
        Filter.atTop
        (𝓝 (∫ ω : ℕ → ℝ, Complex.exp (Complex.I * (c * S ω)) ∂P)) := by
    exact MeasureTheory.tendsto_integral_of_L1'
      (fun ω : ℕ → ℝ => Complex.exp (Complex.I * (c * S ω)))
      (by fun_prop)
      (Filter.Eventually.of_forall (fun N =>
        integrable_complex_exp_I_mul P
          (measurable_finiteTailSum m N).aestronglyMeasurable c))
      (by
        refine (finiteTailExp_tendsto_L1_tailLpLimit α' μ hμ hsum m c).congr' ?_
        exact Filter.Eventually.of_forall (fun N => by
          apply eLpNorm_congr_ae
          filter_upwards with ω
          rfl))
  have hfinite_eq_int :
      ∀ N : ℕ,
        tailProduct α' m N ξ =
          ∫ ω : ℕ → ℝ,
            Complex.exp (Complex.I * (c * finiteTailSum m N ω)) ∂P := by
    intro N
    have hmap :
        measureFT (Measure.map (finiteTailSum m N) P) ξ =
          ∫ ω : ℕ → ℝ,
            Complex.exp (Complex.I * (c * finiteTailSum m N ω)) ∂P := by
      unfold measureFT
      rw [MeasureTheory.integral_map]
      · apply integral_congr_ae
        filter_upwards with ω
        congr 1
        dsimp [c]
        norm_num
        ring
      · exact (measurable_finiteTailSum m N).aemeasurable
      · fun_prop
    calc
      tailProduct α' m N ξ =
          measureFT (Measure.map (finiteTailSum m N) (Measure.infinitePi μ)) ξ :=
        (finiteTailSum_law_measureFT α' μ hμ m N ξ).symm
      _ = ∫ ω : ℕ → ℝ,
            Complex.exp (Complex.I * (c * finiteTailSum m N ω)) ∂P := by
        simpa [P] using hmap
  have hlimit_eq_int :
      measureFT (tailLimitMeasure α' μ hμ hsum m) ξ =
        ∫ ω : ℕ → ℝ, Complex.exp (Complex.I * (c * S ω)) ∂P := by
    unfold measureFT tailLimitMeasure
    rw [MeasureTheory.integral_map]
    · apply integral_congr_ae
      filter_upwards with ω
      congr 1
      dsimp [c]
      norm_num
      ring
    · exact (Lp.aestronglyMeasurable S).aemeasurable
    · fun_prop
  rw [hlimit_eq_int]
  exact hlim_int.congr' (Filter.Eventually.of_forall (fun N => (hfinite_eq_int N).symm))


theorem tail_limit (α' : ℕ → ℝ)
    (hnonzero : ∀ j : ℕ, α' j ≠ 0)
    (hsum : Summable (fun j : ℕ => (α' j) ^ 2)) :
  ∃ (ν : ℕ → Measure ℝ) (v : ℕ → ℝ), TailLimitData α' ν v := by
  rcases prob_space α' hnonzero hsum with ⟨μ, hμ⟩
  let ν : ℕ → Measure ℝ := fun m => tailLimitMeasure α' μ hμ hsum m
  let v : ℕ → ℝ := tailVariance α'
  refine ⟨ν, v, ?_⟩
  refine ⟨hnonzero, hsum, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    exact ⟨tailLimitMeasure_isProbabilityMeasure α' μ hμ hsum m, trivial⟩
  · intro m
    exact tailVariance_nonneg α' m
  · exact tailVariance_tendsto_zero α' hsum
  · intro m
    rcases tailLimitMeasure_mean_zero α' μ hμ hsum m with ⟨hmean_int, hmean⟩
    rcases tailLimitMeasure_second_moment α' μ hμ hsum m with ⟨hsecond_int, hsecond⟩
    exact ⟨hmean_int, hmean, hsecond_int, hsecond⟩
  · intro m ξ
    exact tailLimitMeasure_charfun α' μ hμ hsum m ξ


theorem tail_charfun (α' : ℕ → ℝ) (ν : ℕ → Measure ℝ) (v : ℕ → ℝ)
    (hν : TailLimitData α' ν v) :
  TailCharfunData α' ν := by
  exact hν.2.2.2.2.2.2


theorem tail_law_data_of_limit (α' : ℕ → ℝ) (ν : ℕ → Measure ℝ) (v : ℕ → ℝ)
    (hν : TailLimitData α' ν v) :
  TailLawData α' ν := by
  refine ⟨hν.1, hν.2.1, hν.2.2.1, ?_⟩
  exact ⟨v, hν, tail_charfun α' ν v hν⟩


theorem tail_cheby (α' : ℕ → ℝ) (ν : ℕ → Measure ℝ) (v : ℕ → ℝ)
    (hν : TailLimitData α' ν v) :
  ∀ m : ℕ, ∀ δ : ℝ, 0 < δ →
    ν m {t : ℝ | δ ≤ |t|} ≤ ENNReal.ofReal (v m / δ ^ 2) := by
  intro m δ hδ
  let A : Set ℝ := {t : ℝ | δ ≤ |t|}
  rcases hν with
    ⟨_hnonzero, _hsum, hprob_all, hv_nonneg, _hv_tendsto, hmoments, _hchar⟩
  rcases hprob_all m with ⟨hprobνm, _⟩
  letI : IsProbabilityMeasure (ν m) := hprobνm
  rcases hmoments m with ⟨_hint1, _hmean, hint2, hsecond⟩
  have hA_meas : MeasurableSet A := by
    dsimp [A]
    exact (isClosed_le continuous_const continuous_abs).measurableSet
  have hδ2_pos : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hconst : ∀ t ∈ A, δ ^ 2 ≤ t ^ 2 := by
    intro t ht
    have habs : |δ| ≤ |t| := by
      simpa [abs_of_pos hδ, A] using ht
    exact (sq_le_sq).2 habs
  have hset_ge : δ ^ 2 * (ν m).real A ≤ ∫ t in A, t ^ 2 ∂(ν m) := by
    exact setIntegral_ge_of_const_le_real hA_meas (measure_ne_top (ν m) A)
      hconst hint2.integrableOn
  have hset_le : ∫ t in A, t ^ 2 ∂(ν m) ≤ ∫ t : ℝ, t ^ 2 ∂(ν m) := by
    exact setIntegral_le_integral hint2
      (Filter.Eventually.of_forall (fun t : ℝ => sq_nonneg t))
  have hreal_bound : δ ^ 2 * (ν m).real A ≤ v m := by
    calc
      δ ^ 2 * (ν m).real A ≤ ∫ t in A, t ^ 2 ∂(ν m) := hset_ge
      _ ≤ ∫ t : ℝ, t ^ 2 ∂(ν m) := hset_le
      _ = v m := hsecond
  have hreal_div : (ν m).real A ≤ v m / δ ^ 2 := by
    exact (le_div_iff₀' hδ2_pos).2 hreal_bound
  have hdiv_nonneg : 0 ≤ v m / δ ^ 2 := div_nonneg (hv_nonneg m) hδ2_pos.le
  exact (ENNReal.toReal_le_toReal (measure_ne_top (ν m) A) ENNReal.ofReal_ne_top).mp (by
    rw [← Measure.real_def, ENNReal.toReal_ofReal hdiv_nonneg]
    exact hreal_div)


def measureConv (μ ν : Measure ℝ) : Measure ℝ :=
  Measure.map (fun p : ℝ × ℝ => p.1 + p.2) (μ.prod ν)


theorem measconv_FT (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
  ∀ ξ : ℝ, measureFT (measureConv μ ν) ξ = measureFT μ ξ * measureFT ν ξ := by
  intro ξ
  unfold measureFT measureConv
  calc
    ∫ y : ℝ, Complex.exp (-2 * Real.pi * Complex.I * ↑ξ * ↑y) ∂
        Measure.map (fun p : ℝ × ℝ => p.1 + p.2) (μ.prod ν) =
        ∫ p : ℝ × ℝ, Complex.exp (-2 * Real.pi * Complex.I * ↑ξ * ↑(p.1 + p.2)) ∂
          μ.prod ν := by
      rw [MeasureTheory.integral_map]
      · fun_prop
      · fun_prop
    _ = ∫ p : ℝ × ℝ,
        Complex.exp (-2 * Real.pi * Complex.I * ↑ξ * ↑p.1) *
          Complex.exp (-2 * Real.pi * Complex.I * ↑ξ * ↑p.2) ∂μ.prod ν := by
      apply integral_congr_ae
      filter_upwards with p
      rw [← Complex.exp_add]
      congr 1
      norm_num
      ring
    _ = (∫ x : ℝ, Complex.exp (-2 * Real.pi * Complex.I * ↑ξ * ↑x) ∂μ) *
        ∫ y : ℝ, Complex.exp (-2 * Real.pi * Complex.I * ↑ξ * ↑y) ∂ν := by
      exact MeasureTheory.integral_prod_mul
        (μ := μ) (ν := ν)
        (f := fun x : ℝ => Complex.exp (-2 * Real.pi * Complex.I * ↑ξ * ↑x))
        (g := fun y : ℝ => Complex.exp (-2 * Real.pi * Complex.I * ↑ξ * ↑y))

private theorem tailProduct_pred_eq_mul (α' : ℕ → ℝ) {m N : ℕ} (ξ : ℝ)
    (hm : 1 ≤ m) (hN : m ≤ N) :
  tailProduct α' (m - 1) N ξ = expFactor (α' m) ξ * tailProduct α' m N ξ := by
  classical
  let sPrev : Finset ℕ := (Finset.range (N + 1)).filter (fun j => m - 1 < j)
  let sTail : Finset ℕ := (Finset.range (N + 1)).filter (fun j => m < j)
  have hm_not_tail : m ∉ sTail := by
    dsimp [sTail]
    simp
  have hsplit : sPrev = insert m sTail := by
    ext j
    dsimp [sPrev, sTail]
    simp
    omega
  unfold tailProduct
  change (∏ j ∈ sPrev, expFactor (α' j) ξ) =
    expFactor (α' m) ξ * ∏ j ∈ sTail, expFactor (α' j) ξ
  rw [hsplit]
  exact Finset.prod_insert hm_not_tail


theorem chain_meas (α' : ℕ → ℝ) (μ ν : ℕ → Measure ℝ)
    (hμ : ∀ j : ℕ, KernelLaw (α' j) (μ j))
    (hν : TailLawData α' ν) :
  ∀ m : ℕ, 1 ≤ m → ν (m - 1) = measureConv (μ m) (ν m) := by
  classical
  intro m hm
  rcases hν with ⟨_hnonzero, _hsum, hprobν, htail⟩
  rcases htail with ⟨_v, _hlim, hchar⟩
  rcases hprobν (m - 1) with ⟨hprob_prev, _⟩
  rcases hprobν m with ⟨hprob_curr, _⟩
  rcases (hμ m).1 with ⟨hprob_μm, _⟩
  letI : IsProbabilityMeasure (ν (m - 1)) := hprob_prev
  letI : IsProbabilityMeasure (ν m) := hprob_curr
  letI : IsProbabilityMeasure (μ m) := hprob_μm
  haveI : IsProbabilityMeasure (measureConv (μ m) (ν m)) := by
    unfold measureConv
    exact Measure.isProbabilityMeasure_map (μ := (μ m).prod (ν m))
      (by fun_prop : AEMeasurable (fun p : ℝ × ℝ => p.1 + p.2) ((μ m).prod (ν m)))
  apply measure_unique
  intro ξ
  have hsplit_eventually :
      (fun N : ℕ => tailProduct α' (m - 1) N ξ) =ᶠ[Filter.atTop]
        (fun N : ℕ => expFactor (α' m) ξ * tailProduct α' m N ξ) := by
    filter_upwards [Filter.eventually_ge_atTop m] with N hN
    exact tailProduct_pred_eq_mul α' ξ hm hN
  have hmul_tend : Filter.Tendsto
      (fun N : ℕ => expFactor (α' m) ξ * tailProduct α' m N ξ)
      Filter.atTop (𝓝 (expFactor (α' m) ξ * measureFT (ν m) ξ)) := by
    exact (hchar m ξ).const_mul (expFactor (α' m) ξ)
  have hpred_to_mul : Filter.Tendsto
      (fun N : ℕ => tailProduct α' (m - 1) N ξ)
      Filter.atTop (𝓝 (expFactor (α' m) ξ * measureFT (ν m) ξ)) := by
    exact Filter.Tendsto.congr' hsplit_eventually.symm hmul_tend
  have hprev_limit :
      measureFT (ν (m - 1)) ξ = expFactor (α' m) ξ * measureFT (ν m) ξ := by
    exact tendsto_nhds_unique (hchar (m - 1) ξ) hpred_to_mul
  calc
    measureFT (ν (m - 1)) ξ = expFactor (α' m) ξ * measureFT (ν m) ξ := hprev_limit
    _ = measureFT (μ m) ξ * measureFT (ν m) ξ := by rw [(hμ m).2 ξ]
    _ = measureFT (measureConv (μ m) (ν m)) ξ := (measconv_FT (μ m) (ν m) ξ).symm

end

end Part8
