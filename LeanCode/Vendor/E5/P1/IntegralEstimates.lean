import LeanCode.Vendor.E5.P1.Basic
import LeanCode.Vendor.E5.Defs

noncomputable section

open MeasureTheory

namespace VendorE5ExpDecay

private lemma two_mul_sqrt_mul_le_add {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    2 * Real.sqrt (u * v) ≤ u + v := by
  rw [Real.sqrt_mul hu]
  nlinarith [sq_nonneg (Real.sqrt u - Real.sqrt v), Real.sq_sqrt hu, Real.sq_sqrt hv]

theorem totalMass_nonneg {g : ℝ → ℝ}
    (hg : IsTotallyPositiveIntegrable g) :
    0 ≤ totalMass g := by
  exact integral_nonneg fun x => isTotallyPositive_nonneg hg.1 x

theorem intervalIntegral_le_totalMass {g : ℝ → ℝ}
    (hg : IsTotallyPositiveIntegrable g) {p q : ℝ} (_hpq : p ≤ q) :
    (∫ x in Set.Icc p q, g x) ≤ totalMass g := by
  dsimp [totalMass]
  exact integral_mono_measure Measure.restrict_le_self
    (ae_of_all _ fun x => isTotallyPositive_nonneg hg.1 x) hg.2

theorem reflectionPointwise_le {g : ℝ → ℝ}
    (hg : IsTotallyPositive g) {p q t : ℝ}
    (_hpq : p < q) (ht : t ∈ Set.Icc p q) :
    g t * g (p + q - t) ≥ g p * g q := by
  rcases ht with ⟨hpt, htq⟩
  rcases lt_or_eq_of_le hpt with hpt_lt | htp
  · rcases lt_or_eq_of_le htq with htq_lt | htq
    · have hh : 0 < t - p := sub_pos.mpr hpt_lt
      have hk : 0 < q - t := sub_pos.mpr htq_lt
      have hineq := isTotallyPositive_fourPoint hg p (t - p) (q - t) hh hk
      convert hineq using 2 <;> ring_nf
    · have hp : p + q - q = p := by ring
      simp [htq, hp, mul_comm]
  · simp [htp]

theorem amgmPointwise {g : ℝ → ℝ}
    (hg : IsTotallyPositive g) {p q t : ℝ}
    (hpq : p < q) (ht : t ∈ Set.Icc p q) :
    g t + g (p + q - t) ≥ 2 * Real.sqrt (g p * g q) := by
  have ht_nonneg : 0 ≤ g t := isTotallyPositive_nonneg hg t
  have hmirror_nonneg : 0 ≤ g (p + q - t) :=
    isTotallyPositive_nonneg hg (p + q - t)
  have hamgm :
      2 * Real.sqrt (g t * g (p + q - t)) ≤ g t + g (p + q - t) :=
    two_mul_sqrt_mul_le_add ht_nonneg hmirror_nonneg
  have hprod : g p * g q ≤ g t * g (p + q - t) :=
    reflectionPointwise_le hg hpq ht
  have hsqrt : Real.sqrt (g p * g q) ≤ Real.sqrt (g t * g (p + q - t)) :=
    Real.sqrt_le_sqrt hprod
  nlinarith

theorem intervalIntegral_lower {g : ℝ → ℝ}
    (hg : IsTotallyPositiveIntegrable g) {p q : ℝ} (hpq : p < q) :
    (q - p) * Real.sqrt (g p * g q) ≤ (∫ x in Set.Icc p q, g x) := by
  let c : ℝ := Real.sqrt (g p * g q)
  have hpq_le : p ≤ q := hpq.le
  have hg_int : IntervalIntegrable g volume p q := hg.2.intervalIntegrable
  have hsub_mp : MeasurePreserving (fun x : ℝ => p + q - x) volume volume :=
    Measure.measurePreserving_sub_left volume (p + q)
  have hcomp_global : Integrable (fun x : ℝ => g (p + q - x)) := by
    simpa [Function.comp_def] using
      (hsub_mp.integrable_comp hg.2.aestronglyMeasurable).2 hg.2
  have hcomp_int : IntervalIntegrable (fun x : ℝ => g (p + q - x)) volume p q :=
    hcomp_global.intervalIntegrable
  have hconst_int : IntervalIntegrable (fun _ : ℝ => 2 * c) volume p q :=
    intervalIntegral.intervalIntegrable_const
  have hsum_int : IntervalIntegrable (fun x : ℝ => g x + g (p + q - x)) volume p q :=
    hg_int.add hcomp_int
  have hmono :
      (∫ x in p..q, (2 * c : ℝ)) ≤
        (∫ x in p..q, g x + g (p + q - x)) := by
    refine intervalIntegral.integral_mono_on hpq_le hconst_int hsum_int ?_
    intro x hx
    exact amgmPointwise hg.1 hpq hx
  have hconst_eval : (∫ x in p..q, (2 * c : ℝ)) = (q - p) * (2 * c) := by
    simp [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hreflect : (∫ x in p..q, g (p + q - x)) = ∫ x in p..q, g x := by
    have h := intervalIntegral.integral_comp_sub_left (a := p) (b := q) g (p + q)
    convert h using 1
    · ring_nf
  have hsum_eq :
      (∫ x in p..q, g x + g (p + q - x)) = 2 * (∫ x in p..q, g x) := by
    rw [intervalIntegral.integral_add hg_int hcomp_int, hreflect]
    ring
  have hinterval : (q - p) * c ≤ ∫ x in p..q, g x := by
    rw [hconst_eval, hsum_eq] at hmono
    nlinarith
  have hinterval_eq_set : (∫ x in p..q, g x) = ∫ x in Set.Icc p q, g x := by
    rw [intervalIntegral.integral_of_le hpq_le]
    rw [← MeasureTheory.integral_Icc_eq_integral_Ioc (f := g) (x := p) (y := q)]
  simpa [c, hinterval_eq_set] using hinterval

theorem totalMass_pos_of_two_pos {g : ℝ → ℝ}
    (hg : IsTotallyPositiveIntegrable g) {p q : ℝ}
    (hpq : p < q) (hp : 0 < g p) (hq : 0 < g q) :
    0 < totalMass g := by
  have hupper := intervalIntegral_le_totalMass hg (le_of_lt hpq)
  have hlower := intervalIntegral_lower hg hpq
  have hdiff : 0 < q - p := sub_pos.mpr hpq
  have hsqrt : 0 < Real.sqrt (g p * g q) := Real.sqrt_pos.2 (mul_pos hp hq)
  have hpositive : 0 < (q - p) * Real.sqrt (g p * g q) := mul_pos hdiff hsqrt
  exact lt_of_lt_of_le hpositive (hlower.trans hupper)

theorem endpointLeft_bound {g : ℝ → ℝ}
    (hg : IsTotallyPositiveIntegrable g) {p q : ℝ}
    (hpq : p < q) (hq : 0 < g q) :
    g p ≤ (totalMass g) ^ 2 / (g q * (q - p) ^ 2) := by
  have hupper := intervalIntegral_le_totalMass hg (le_of_lt hpq)
  have hlower := intervalIntegral_lower hg hpq
  have hchain : (q - p) * Real.sqrt (g p * g q) ≤ totalMass g :=
    hlower.trans hupper
  have hdiff : 0 < q - p := sub_pos.mpr hpq
  have hgp : 0 ≤ g p := isTotallyPositive_nonneg hg.1 p
  have hprod : 0 ≤ g p * g q := mul_nonneg hgp hq.le
  have hleft_nonneg : 0 ≤ (q - p) * Real.sqrt (g p * g q) :=
    mul_nonneg hdiff.le (Real.sqrt_nonneg _)
  have hmass_nonneg : 0 ≤ totalMass g := totalMass_nonneg hg
  have hsquare :
      ((q - p) * Real.sqrt (g p * g q)) ^ 2 ≤ (totalMass g) ^ 2 :=
    (sq_le_sq₀ hleft_nonneg hmass_nonneg).2 hchain
  have hden_pos : 0 < g q * (q - p) ^ 2 := mul_pos hq (sq_pos_of_pos hdiff)
  rw [le_div_iff₀ hden_pos]
  nlinarith [Real.sq_sqrt hprod, hsquare]

theorem endpointRight_bound {g : ℝ → ℝ}
    (hg : IsTotallyPositiveIntegrable g) {p q : ℝ}
    (hpq : p < q) (hp : 0 < g p) :
    g q ≤ (totalMass g) ^ 2 / (g p * (q - p) ^ 2) := by
  have hupper := intervalIntegral_le_totalMass hg (le_of_lt hpq)
  have hlower := intervalIntegral_lower hg hpq
  have hchain : (q - p) * Real.sqrt (g p * g q) ≤ totalMass g :=
    hlower.trans hupper
  have hdiff : 0 < q - p := sub_pos.mpr hpq
  have hgq : 0 ≤ g q := isTotallyPositive_nonneg hg.1 q
  have hprod : 0 ≤ g p * g q := mul_nonneg hp.le hgq
  have hleft_nonneg : 0 ≤ (q - p) * Real.sqrt (g p * g q) :=
    mul_nonneg hdiff.le (Real.sqrt_nonneg _)
  have hmass_nonneg : 0 ≤ totalMass g := totalMass_nonneg hg
  have hsquare :
      ((q - p) * Real.sqrt (g p * g q)) ^ 2 ≤ (totalMass g) ^ 2 :=
    (sq_le_sq₀ hleft_nonneg hmass_nonneg).2 hchain
  have hden_pos : 0 < g p * (q - p) ^ 2 := mul_pos hp (sq_pos_of_pos hdiff)
  rw [le_div_iff₀ hden_pos]
  nlinarith [Real.sq_sqrt hprod, hsquare]

end VendorE5ExpDecay
