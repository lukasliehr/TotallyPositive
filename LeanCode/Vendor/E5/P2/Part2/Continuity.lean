import LeanCode.Vendor.E5.P2.Part2.Summability
import LeanCode.Vendor.E5.Defs

open MeasureTheory












namespace Part2



theorem summand_cont (f : ℝ → ℝ) (hf : Continuous f) (k : ℤ) :
    Continuous (fun x : ℝ => (-1 : ℝ) ^ k * f (x + k)) :=
  (hf.comp (continuous_id.add continuous_const)).const_mul _




theorem unif_on_ball (f : ℝ → ℝ) (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hb : ∀ t : ℝ, |f t| ≤ C * Real.exp (-c * |t|)) (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn
      (fun (F : Finset ℤ) (x : ℝ) => ∑ k ∈ F, (-1 : ℝ) ^ k * f (x + k))
      (Halt f) Filter.atTop {x : ℝ | |x| ≤ R} := by
  have h := tendstoUniformlyOn_tsum
    (u := fun k : ℤ => C * Real.exp (c * R) * Real.exp (-c * |(k : ℝ)|))
    (f := fun (k : ℤ) (x : ℝ) => (-1 : ℝ) ^ k * f (x + k))
    (s := {x : ℝ | |x| ≤ R})
    (envelope_summable C c R hc)
    (fun k x hx => by
      rw [Real.norm_eq_abs]
      exact envelope f C c hC hc hb R hR k x hx)
  exact h



theorem cont_on_ball (f : ℝ → ℝ) (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hf : Continuous f) (hb : ∀ t : ℝ, |f t| ≤ C * Real.exp (-c * |t|))
    (R : ℝ) (hR : 0 ≤ R) :
    ContinuousOn (Halt f) {x : ℝ | |x| ≤ R} := by
  refine (unif_on_ball f C c hC hc hb R hR).continuousOn ?_
  refine (Filter.Eventually.of_forall (fun F => ?_)).frequently
  exact (continuous_finsetSum F (fun k _ => summand_cont f hf k)).continuousOn



theorem glue (g : ℝ → ℝ)
    (h : ∀ R : ℝ, 0 < R → ContinuousOn g {x : ℝ | |x| ≤ R}) :
    Continuous g := by
  rw [continuous_iff_continuousAt]
  intro x₀
  refine (h (|x₀| + 1) (by positivity)).continuousAt ?_
  apply Filter.mem_of_superset (Metric.ball_mem_nhds x₀ (by norm_num : (0 : ℝ) < 1))
  intro y hy
  rw [Metric.mem_ball, Real.dist_eq] at hy
  rw [Set.mem_setOf_eq]
  have hle := abs_sub_abs_le_abs_sub y x₀
  linarith



theorem cont (f : ℝ → ℝ) (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hf : Continuous f) (hb : ∀ t : ℝ, |f t| ≤ C * Real.exp (-c * |t|)) :
    Continuous (Halt f) :=
  glue (Halt f) (fun R hR => cont_on_ball f C c hC hc hf hb R hR.le)

end Part2
