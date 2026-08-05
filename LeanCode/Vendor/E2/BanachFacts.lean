import LeanCode.Vendor.E2.MatrixDefs

open scoped ENNReal NNReal

namespace VendorE2.Lean_Code

theorem boundedBelow_injective
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : ellp p →L[ℂ] ellp p) :
    OperatorBoundedBelow T → Function.Injective T := by
  intro hbelow x y hxy
  rcases hbelow with ⟨c, hc_pos, hbound⟩
  have hT_sub : T (x - y) = 0 := by
    simp [hxy]
  have hle := hbound (x - y)
  rw [hT_sub, norm_zero] at hle
  have hnorm : ‖x - y‖ = 0 := by
    have hnorm_nonneg : 0 ≤ ‖x - y‖ := norm_nonneg _
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

theorem boundedBelow_closedRange
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : ellp p →L[ℂ] ellp p) :
    OperatorBoundedBelow T → IsClosed (Set.range T) := by
  intro hbelow
  rcases hbelow with ⟨c, hc_pos, hbound⟩
  let K : ℝ≥0 := ⟨c⁻¹, inv_nonneg.mpr hc_pos.le⟩
  have hanti : AntilipschitzWith K T := by
    refine AntilipschitzWith.of_le_mul_dist ?_
    intro x y
    have hbound_xy := hbound (x - y)
    have hdist_bound : c * dist x y ≤ dist (T x) (T y) := by
      simpa [dist_eq_norm, map_sub] using hbound_xy
    change dist x y ≤ c⁻¹ * dist (T x) (T y)
    calc
      dist x y = c⁻¹ * (c * dist x y) := by
        field_simp [hc_pos.ne']
      _ ≤ c⁻¹ * dist (T x) (T y) :=
        mul_le_mul_of_nonneg_left hdist_bound (inv_nonneg.mpr hc_pos.le)
  exact hanti.isClosed_range T.uniformContinuous

theorem operatorBoundedBelow_of_opNorm_sub_le
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T S : ellp p →L[ℂ] ellp p)
    {c ε : ℝ}
    (hT : ∀ x : ellp p, c * ‖x‖ ≤ ‖T x‖)
    (hclose : ‖S - T‖ ≤ ε) (hεc : ε < c) :
    OperatorBoundedBelow S := by
  refine ⟨c - ε, sub_pos.mpr hεc, ?_⟩
  intro x
  have hD_norm : ‖(S - T) x‖ ≤ ε * ‖x‖ := by
    calc
      ‖(S - T) x‖ ≤ ‖S - T‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ε * ‖x‖ := mul_le_mul_of_nonneg_right hclose (norm_nonneg x)
  have hT_tri : ‖T x‖ ≤ ‖S x‖ + ‖(S - T) x‖ := by
    have h_eq : T x = S x - (S - T) x := by simp
    rw [h_eq]
    exact norm_sub_le _ _
  have h_sub : ‖T x‖ - ‖(S - T) x‖ ≤ ‖S x‖ := by
    exact (sub_le_iff_le_add).mpr hT_tri
  calc
    (c - ε) * ‖x‖ = c * ‖x‖ - ε * ‖x‖ := by ring
    _ ≤ ‖T x‖ - ‖(S - T) x‖ := by
      exact sub_le_sub (hT x) hD_norm
    _ ≤ ‖S x‖ := h_sub

theorem operatorBoundedBelow_of_opNorm_sub_lt
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T S : ellp p →L[ℂ] ellp p)
    {c : ℝ}
    (hT : ∀ x : ellp p, c * ‖x‖ ≤ ‖T x‖)
    (hclose : ‖S - T‖ < c) :
    OperatorBoundedBelow S :=
  operatorBoundedBelow_of_opNorm_sub_le p T S hT le_rfl hclose

theorem continuousLinearMap_isUnit_of_bijective
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : ellp p →L[ℂ] ellp p) :
    Function.Bijective T → IsUnit T := by
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr

theorem surjective_maps_ball_onto_ball
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : ellp p →L[ℂ] ellp p) :
    Function.Surjective T →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ y : ellp p, ‖y‖ ≤ δ → ∃ x : ellp p, ‖x‖ ≤ 1 ∧ T x = y := by
  intro hsurj
  rcases ContinuousLinearMap.exists_preimage_norm_le T hsurj with ⟨C, hC_pos, hC⟩
  refine ⟨C⁻¹, inv_pos.mpr hC_pos, ?_⟩
  intro y hy
  rcases hC y with ⟨x, hTx, hx_norm⟩
  refine ⟨x, ?_, hTx⟩
  calc
    ‖x‖ ≤ C * ‖y‖ := hx_norm
    _ ≤ C * C⁻¹ := mul_le_mul_of_nonneg_left hy hC_pos.le
    _ = 1 := by
      field_simp [hC_pos.ne']

theorem exists_continuousLinearFunctional_separating_point_closed_convex
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (C : Set (ellp p)) (x₀ : ellp p)
    (hclosed : IsClosed C) (hconvex : Convex ℝ C) (hx₀ : x₀ ∉ C) :
    ∃ f : ellp p →L[ℂ] ℂ, ∃ α : ℝ,
      α < (f x₀).re ∧ ∀ x ∈ C, (f x).re ≤ α := by
  rcases RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ) hconvex hclosed hx₀ with
    ⟨f, α, hC, hx₀_sep⟩
  refine ⟨f, α, ?_, ?_⟩
  · simpa using hx₀_sep
  · intro x hxC
    exact le_of_lt (by simpa using hC x hxC)

theorem closure_image_closedBall_zero_isClosed
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : ellp p →L[ℂ] ellp p) (R : ℝ) :
    IsClosed (closure (Set.image (fun x => T x)
      (Metric.closedBall (0 : ellp p) R))) := by
  exact isClosed_closure

theorem closure_image_closedBall_zero_convex
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : ellp p →L[ℂ] ellp p) (R : ℝ) :
    Convex ℝ (closure (Set.image (fun x => T x)
      (Metric.closedBall (0 : ellp p) R))) := by
  have hconv : Convex ℝ (Set.image (fun x => T x)
      (Metric.closedBall (0 : ellp p) R)) := by
    simpa using (convex_closedBall (0 : ellp p) R).linear_image
      ((T.restrictScalars ℝ).toLinearMap)
  exact hconv.closure

lemma complex_norm_le_of_forall_norm_one_re_mul_le {z : ℂ} {α : ℝ}
    (h : ∀ θ : ℂ, ‖θ‖ = 1 → (θ * z).re ≤ α) :
    ‖z‖ ≤ α := by
  by_cases hz : z = 0
  · simpa [hz] using h 1 (by simp)
  · have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hnorm : ‖(starRingEnd ℂ) z / (‖z‖ : ℂ)‖ = 1 := by
      rw [norm_div, RCLike.norm_conj, Complex.norm_real,
        Real.norm_of_nonneg hzpos.le]
      exact div_self hzpos.ne'
    have hre : (((starRingEnd ℂ) z / (‖z‖ : ℂ)) * z).re = ‖z‖ := by
      rw [div_mul_eq_mul_div]
      rw [← Complex.normSq_eq_conj_mul_self]
      rw [Complex.normSq_eq_norm_sq]
      rw [← Complex.ofReal_div]
      field_simp [hzpos.ne']
      simp
    rw [← hre]
    exact h _ hnorm

theorem exists_approx_preimage_of_closedBall_subset_closure_image
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : ellp p →L[ℂ] ellp p)
    (δ : ℝ) (hδ : 0 < δ)
    (happrox : ∀ R : ℝ, 0 < R →
      Metric.closedBall (0 : ellp p) (δ * R) ⊆
        closure (Set.image (fun x => T x)
          (Metric.closedBall (0 : ellp p) R))) :
    ∃ C ≥ 0, ∀ y : ellp p,
      ∃ x : ellp p, dist (T x) y ≤ 1 / 2 * ‖y‖ ∧
        ‖x‖ ≤ C * ‖y‖ := by
  let C : ℝ := 2 * δ⁻¹
  have hC_nonneg : 0 ≤ C := by positivity
  refine ⟨C, hC_nonneg, ?_⟩
  intro y
  by_cases hy : y = 0
  · refine ⟨0, ?_, ?_⟩
    · simp [hy]
    · simp [hy]
  · have hynorm_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy
    let R : ℝ := C * ‖y‖
    have hR_pos : 0 < R := by
      have hC_pos : 0 < C := by positivity
      exact mul_pos hC_pos hynorm_pos
    have hδR : δ * R = 2 * ‖y‖ := by
      simp [R, C]
      field_simp [hδ.ne']
    have hy_ball : y ∈ Metric.closedBall (0 : ellp p) (δ * R) := by
      have hynorm_le : ‖y‖ ≤ δ * R := by
        rw [hδR]
        nlinarith [norm_nonneg y]
      simpa [Metric.mem_closedBall, dist_eq_norm] using hynorm_le
    have hy_closure := happrox R hR_pos hy_ball
    have heps_pos : 0 < (1 / 2 : ℝ) * ‖y‖ := by positivity
    rcases Metric.mem_closure_iff.1 hy_closure
        ((1 / 2 : ℝ) * ‖y‖) heps_pos with
      ⟨w, hw_mem, hdist⟩
    rcases hw_mem with ⟨x, hx_ball, rfl⟩
    refine ⟨x, ?_, ?_⟩
    · exact le_of_lt (by simpa [dist_comm] using hdist)
    · have hx_norm : ‖x‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hx_ball
      simpa [R] using hx_norm

theorem surjective_of_closedBall_subset_closure_image
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : ellp p →L[ℂ] ellp p)
    (δ : ℝ) (hδ : 0 < δ)
    (happrox : ∀ R : ℝ, 0 < R →
      Metric.closedBall (0 : ellp p) (δ * R) ⊆
        closure (Set.image (fun x => T x)
          (Metric.closedBall (0 : ellp p) R))) :
    Function.Surjective T := by
  rcases exists_approx_preimage_of_closedBall_subset_closure_image p T δ hδ
      happrox with
    ⟨C, _C0, hC⟩
  choose g hg using hC
  let h y := y - T (g y)
  have hle : ∀ y, ‖h y‖ ≤ 1 / 2 * ‖y‖ := by
    intro y
    rw [← dist_eq_norm, dist_comm]
    exact (hg y).1
  intro y
  have hnle : ∀ n : ℕ, ‖h^[n] y‖ ≤ (1 / 2) ^ n * ‖y‖ := by
    intro n
    induction n with
    | zero =>
        simp only [one_div, one_mul, Function.iterate_zero_apply, pow_zero,
          le_rfl]
    | succ n IH =>
        rw [Function.iterate_succ']
        apply le_trans (hle _) _
        rw [pow_succ', mul_assoc]
        gcongr
  let u n := g (h^[n] y)
  have ule : ∀ n, ‖u n‖ ≤ (1 / 2) ^ n * (C * ‖y‖) := fun n ↦ by
    apply le_trans (hg _).2
    calc
      C * ‖h^[n] y‖ ≤ C * ((1 / 2) ^ n * ‖y‖) := by
        gcongr
        exact hnle n
      _ = (1 / 2) ^ n * (C * ‖y‖) := by ring
  have sNu : Summable fun n => ‖u n‖ := by
    refine .of_nonneg_of_le (fun n => norm_nonneg _) ule ?_
    exact Summable.mul_right _ (summable_geometric_of_lt_one (by simp) (by norm_num))
  have su : Summable u := sNu.of_norm
  let x := tsum u
  have fsumeq : ∀ n : ℕ, T (∑ i ∈ Finset.range n, u i) = y - h^[n] y := by
    intro n
    induction n with
    | zero => simp [T.map_zero]
    | succ n IH =>
        rw [Finset.sum_range_succ, T.map_add, IH,
          Function.iterate_succ_apply', sub_add]
  have htend_sum :
      Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, u i) Filter.atTop
        (nhds x) :=
    su.hasSum.tendsto_sum_nat
  have L₁ :
      Filter.Tendsto (fun n => T (∑ i ∈ Finset.range n, u i))
        Filter.atTop (nhds (T x)) :=
    (T.continuous.tendsto _).comp htend_sum
  simp only [fsumeq] at L₁
  have L₂ : Filter.Tendsto (fun n => y - h^[n] y) Filter.atTop
      (nhds (y - 0)) := by
    refine tendsto_const_nhds.sub ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) hnle ?_
    rw [← zero_mul ‖y‖]
    refine (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one ?_ ?_).mul
      tendsto_const_nhds <;> norm_num
  have feq : T x = y - 0 := tendsto_nhds_unique L₁ L₂
  rw [sub_zero] at feq
  exact ⟨x, feq⟩

end VendorE2.Lean_Code
