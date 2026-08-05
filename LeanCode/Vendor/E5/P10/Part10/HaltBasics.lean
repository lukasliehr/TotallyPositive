import LeanCode.Vendor.E5.P10.Part10.Summability
import LeanCode.Vendor.E5.Defs

open MeasureTheory
open scoped BigOperators


def HasLocalLatticeEnvelopes (f : ℝ → ℝ) : Prop :=
  ∀ R : ℝ, 0 ≤ R →
    ∃ e : ℤ → ℝ, Summable e ∧
      ∀ (k : ℤ) (x : ℝ), |x| ≤ R → |f (x + k)| ≤ e k


theorem env_decay (C c : ℝ) (hC : 0 < C) (hc : 0 < c) (f : ℝ → ℝ)
    (hf : ∀ t : ℝ, |f t| ≤ C * Real.exp (-c * |t|)) :
  (∀ (R : ℝ), 0 ≤ R →
    (∀ (k : ℤ) (x : ℝ), |x| ≤ R →
      |f (x + k)| ≤ C * Real.exp (c * R) * Real.exp (-c * |(k : ℝ)|)) ∧
    Summable (fun k : ℤ => C * Real.exp (c * R) * Real.exp (-c * |(k : ℝ)|))) ∧
  HasLocalLatticeEnvelopes f := by
  have hbound : ∀ (R : ℝ), 0 ≤ R → ∀ (k : ℤ) (x : ℝ), |x| ≤ R →
      |f (x + k)| ≤ C * Real.exp (c * R) * Real.exp (-c * |(k : ℝ)|) := by
    intro R hR k x hx
    have htri : |(k : ℝ)| - |x| ≤ |x + (k : ℝ)| := rev_triangle x (k : ℝ)
    have hlower : |(k : ℝ)| - R ≤ |x + (k : ℝ)| := by linarith
    have harg : -c * |x + (k : ℝ)| ≤ c * R + -c * |(k : ℝ)| := by
      nlinarith [hc, hlower]
    have hexp : Real.exp (-c * |x + (k : ℝ)|) ≤
        Real.exp (c * R) * Real.exp (-c * |(k : ℝ)|) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr harg
    calc
      |f (x + k)| ≤ C * Real.exp (-c * |x + (k : ℝ)|) := hf (x + k)
      _ ≤ C * (Real.exp (c * R) * Real.exp (-c * |(k : ℝ)|)) :=
        mul_le_mul_of_nonneg_left hexp (le_of_lt hC)
      _ = C * Real.exp (c * R) * Real.exp (-c * |(k : ℝ)|) := by ring
  have hsum : ∀ R : ℝ,
      Summable (fun k : ℤ => C * Real.exp (c * R) * Real.exp (-c * |(k : ℝ)|)) := by
    intro R
    have hbase : Summable (fun k : ℤ => Real.exp (-c * |(k : ℝ)|)) :=
      (exp_int_summable c hc).1
    simpa [mul_assoc] using (hbase.mul_left (C * Real.exp (c * R)))
  constructor
  · intro R hR
    exact ⟨hbound R hR, hsum R⟩
  · intro R hR
    exact ⟨fun k : ℤ => C * Real.exp (c * R) * Real.exp (-c * |(k : ℝ)|),
      hsum R, hbound R hR⟩


theorem env_lattice (f : ℝ → ℝ) (b : ℤ → ℝ) (hb_sum : Summable b)
    (hb : ∀ (k : ℤ), ∀ x ∈ Set.Icc (0 : ℝ) 1, |f (x + k)| ≤ b k) :
    (∀ k : ℤ, 0 ≤ b k) ∧ HasLocalLatticeEnvelopes f := by
  have hb_nonneg : ∀ k : ℤ, 0 ≤ b k := by
    intro k
    have h := hb k 0 (by simp)
    exact le_trans (abs_nonneg (f (0 + k))) h
  constructor
  · exact hb_nonneg
  · intro R hR
    let N : ℤ := Int.floor (R + 1) + 1
    let J : Finset ℤ := Finset.Icc (-N) N
    let e : ℤ → ℝ := fun k => (∑ j ∈ J, b (k + j))
    have hshift : ∀ j ∈ J, Summable (fun k : ℤ => b (k + j)) := by
      intro j hj
      simpa [Function.comp_def, Equiv.addRight] using
        ((Equiv.addRight j).summable_iff (f := b)).mpr hb_sum
    have he_sum : Summable e := by
      simpa [e] using summable_sum (s := J) (f := fun j k : ℤ => b (k + j)) hshift
    refine ⟨e, he_sum, ?_⟩
    intro k x hxR
    let j0 : ℤ := Int.floor x
    let x0 : ℝ := x - (j0 : ℝ)
    have hx0_nonneg : 0 ≤ x0 := by
      simp [x0, j0, Int.self_sub_floor, Int.fract_nonneg x]
    have hx0_le_one : x0 ≤ 1 := by
      have hx0_lt : x0 < 1 := by
        simpa [x0, j0, Int.self_sub_floor] using Int.fract_lt_one x
      exact le_of_lt hx0_lt
    have hbase : |f (x0 + (k + j0 : ℤ))| ≤ b (k + j0) :=
      hb (k + j0) x0 ⟨hx0_nonneg, hx0_le_one⟩
    have hx_decomp : x0 + (j0 : ℝ) = x := by
      dsimp [x0]
      ring
    have harg : x + (k : ℝ) = x0 + ((k + j0 : ℤ) : ℝ) := by
      rw [← hx_decomp]
      norm_num
      ring
    have hx_floor_abs : |(j0 : ℝ)| ≤ |x| + 1 := by
      apply abs_le.mpr
      constructor
      · have hlt : x < (j0 : ℝ) + 1 := by
          simp [j0, Int.lt_floor_add_one x]
        have hneg : -|x| ≤ x := neg_abs_le x
        linarith
      · have hle : (j0 : ℝ) ≤ x := by
          simpa [j0] using Int.floor_le x
        have hxle : x ≤ |x| := le_abs_self x
        linarith
    have hx_floor_R : |(j0 : ℝ)| ≤ R + 1 := by
      linarith
    have hN_gt : R + 1 < (N : ℝ) := by
      have h := Int.lt_floor_add_one (R + 1)
      simp [N]
    have hj_abs_lt : |(j0 : ℝ)| < (N : ℝ) := lt_of_le_of_lt hx_floor_R hN_gt
    have hj_bounds := abs_lt.mp hj_abs_lt
    have hj_mem : j0 ∈ J := by
      dsimp [J]
      rw [Finset.mem_Icc]
      constructor
      · exact_mod_cast (le_of_lt hj_bounds.1)
      · exact_mod_cast (le_of_lt hj_bounds.2)
    have hsingle : b (k + j0) ≤ e k := by
      dsimp [e]
      exact Finset.single_le_sum (fun j _hj => hb_nonneg (k + j)) hj_mem
    calc
      |f (x + k)| = |f (x0 + (k + j0 : ℤ))| := by
        rw [harg]
      _ ≤ b (k + j0) := hbase
      _ ≤ e k := hsingle


theorem H_abs (f : ℝ → ℝ) (hf : HasLocalLatticeEnvelopes f) (x : ℝ) :
    Summable (fun k : ℤ => |((-1 : ℝ) ^ k * f (x + k))|) ∧
    Summable (fun k : ℤ => (-1 : ℝ) ^ k * f (x + k)) ∧
    ∀ e : ℤ → ℝ, Summable e →
      (∀ k : ℤ, |f (x + k)| ≤ e k) →
      |Halt f x| ≤ ∑' k : ℤ, e k := by
  have habs_term : ∀ k : ℤ,
      |((-1 : ℝ) ^ k * f (x + k))| = |f (x + k)| := by
    intro k
    rw [abs_mul, abs_zpow]
    norm_num
  rcases hf (|x|) (abs_nonneg x) with ⟨e0, he0, henv0⟩
  have hle0 : ∀ k : ℤ, |((-1 : ℝ) ^ k * f (x + k))| ≤ e0 k := by
    intro k
    rw [habs_term k]
    exact henv0 k x le_rfl
  have habs_sum0 : Summable (fun k : ℤ => |((-1 : ℝ) ^ k * f (x + k))|) :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hle0 he0
  constructor
  · exact habs_sum0
  constructor
  · exact summable_abs_iff.mp habs_sum0
  · intro e he hbound
    have hle : ∀ k : ℤ, |((-1 : ℝ) ^ k * f (x + k))| ≤ e k := by
      intro k
      rw [habs_term k]
      exact hbound k
    have habs_sum : Summable (fun k : ℤ => |((-1 : ℝ) ^ k * f (x + k))|) :=
      Summable.of_nonneg_of_le (fun k => abs_nonneg _) hle he
    have hnorm_sum : Summable (fun k : ℤ => ‖(-1 : ℝ) ^ k * f (x + k)‖) := by
      simpa [Real.norm_eq_abs] using habs_sum
    unfold Halt
    calc
      |∑' k : ℤ, (-1 : ℝ) ^ k * f (x + k)| =
          ‖∑' k : ℤ, (-1 : ℝ) ^ k * f (x + k)‖ := by simp [Real.norm_eq_abs]
      _ ≤ ∑' k : ℤ, ‖(-1 : ℝ) ^ k * f (x + k)‖ :=
        norm_tsum_le_tsum_norm hnorm_sum
      _ = ∑' k : ℤ, |((-1 : ℝ) ^ k * f (x + k))| := by simp [Real.norm_eq_abs]
      _ ≤ ∑' k : ℤ, e k := Summable.tsum_le_tsum hle habs_sum he


theorem H_unif (f : ℝ → ℝ) (hf : HasLocalLatticeEnvelopes f)
    (R : ℝ) (hR : 0 ≤ R) (e : ℤ → ℝ) (he : Summable e)
    (hbound : ∀ (k : ℤ) (x : ℝ), |x| ≤ R → |f (x + k)| ≤ e k) :
    ∀ ε : ℝ, 0 < ε →
      ∃ F₀ : Finset ℤ, ∀ F : Finset ℤ, F₀ ⊆ F →
        ∀ x : ℝ, |x| ≤ R →
          |Halt f x - F.sum (fun k => (-1 : ℝ) ^ k * f (x + k))| ≤ ε := by
  have _hf : HasLocalLatticeEnvelopes f := hf
  have _hR : 0 ≤ R := hR
  let s : Set ℝ := {x : ℝ | |x| ≤ R}
  let term : ℤ → ℝ → ℝ := fun k x => (-1 : ℝ) ^ k * f (x + k)
  have hfu : ∀ k : ℤ, ∀ x ∈ s, ‖term k x‖ ≤ e k := by
    intro k x hx
    have habs : |term k x| = |f (x + k)| := by
      simp [term, abs_mul, abs_zpow]
    simpa [s, term, Real.norm_eq_abs, habs] using hbound k x hx
  have htend : TendstoUniformlyOn
      (fun F : Finset ℤ => fun x : ℝ => ∑ k ∈ F, term k x)
      (fun x : ℝ => tsum (fun k : ℤ => term k x)) Filter.atTop s :=
    tendstoUniformlyOn_tsum he hfu
  intro ε hε
  have hevent := (Metric.tendstoUniformlyOn_iff.mp htend) ε hε
  rcases Filter.eventually_atTop.mp hevent with ⟨F₀, hF₀⟩
  refine ⟨F₀, ?_⟩
  intro F hsub x hx
  have hdist := hF₀ F hsub x hx
  have hle := le_of_lt hdist
  simpa [Halt, s, term, dist_eq_norm, Real.norm_eq_abs, Finset.sum_apply] using hle


theorem H_cont_ball (f : ℝ → ℝ) (hf_cont : Continuous f)
    (hf_env : HasLocalLatticeEnvelopes f) (R : ℝ) (hR : 0 ≤ R) :
    ContinuousOn (Halt f) {x : ℝ | |x| ≤ R} := by
  let s : Set ℝ := {x : ℝ | |x| ≤ R}
  rcases hf_env R hR with ⟨e, he, hbound⟩
  let term : ℤ → ℝ → ℝ := fun k x => (-1 : ℝ) ^ k * f (x + k)
  have hterm_cont : ∀ k : ℤ, ContinuousOn (term k) s := by
    intro k
    have hshift : Continuous (fun x : ℝ => f (x + k)) := by
      exact hf_cont.comp (continuous_id.add continuous_const)
    exact (continuous_const.mul hshift).continuousOn
  have hfu : ∀ k : ℤ, ∀ x ∈ s, ‖term k x‖ ≤ e k := by
    intro k x hx
    have habs : |term k x| = |f (x + k)| := by
      simp [term, abs_mul, abs_zpow]
    simpa [s, term, Real.norm_eq_abs, habs] using hbound k x hx
  have hcont_tsum : ContinuousOn (fun x : ℝ => tsum (fun k : ℤ => term k x)) s :=
    continuousOn_tsum hterm_cont he hfu
  change ContinuousOn (fun x : ℝ => tsum (fun k : ℤ => (-1 : ℝ) ^ k * f (x + k))) s
  simpa [term] using hcont_tsum


theorem H_cont (f : ℝ → ℝ) (hf_cont : Continuous f)
    (hf_env : HasLocalLatticeEnvelopes f) :
    Continuous (Halt f) := by
  rw [continuous_iff_continuousAt]
  intro x
  let R : ℝ := |x| + 1
  have hR : 0 ≤ R := by positivity
  have hball := H_cont_ball f hf_cont hf_env R hR
  have hmem : {y : ℝ | |y| ≤ R} ∈ nhds x := by
    refine Filter.mem_of_superset (Metric.ball_mem_nhds x zero_lt_one) ?_
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] at hy
    have habs : |y| ≤ |y - x| + |x| := by
      calc
        |y| = |(y - x) + x| := by ring_nf
        _ ≤ |y - x| + |x| := abs_add_le (y - x) x
    dsimp [R]
    linarith
  exact hball.continuousAt hmem


theorem H_antiper (f : ℝ → ℝ) (x : ℝ) :
    Halt f (x + 1) = -Halt f x ∧ Halt f (x + 2) = Halt f x := by
  have hstep : ∀ y : ℝ, Halt f (y + 1) = -Halt f y := by
    intro y
    unfold Halt
    rw [← (Equiv.addRight (-1 : ℤ)).tsum_eq
      (fun k : ℤ => (-1 : ℝ) ^ k * f (y + 1 + k))]
    rw [← tsum_neg]
    apply tsum_congr
    intro j
    change (-1 : ℝ) ^ ((Equiv.addRight (-1)) j) *
        f (y + 1 + ((Equiv.addRight (-1)) j : ℤ)) =
      -((-1 : ℝ) ^ j * f (y + j))
    have hsign : (-1 : ℝ) ^ (((Equiv.addRight (-1 : ℤ)) j)) =
        -((-1 : ℝ) ^ j) := by
      have h := (sign (j - 1) 0).1
      have hpow : ((j - 1) + 1 : ℤ) = j := by ring
      rw [hpow] at h
      have htmp : -((-1 : ℝ) ^ j) = (-1 : ℝ) ^ (j - 1) := by linarith
      have heq : ((Equiv.addRight (-1 : ℤ)) j) = j - 1 := by
        change j + (-1 : ℤ) = j - 1
        ring
      rw [heq]
      exact htmp.symm
    have harg : y + 1 + (((Equiv.addRight (-1 : ℤ)) j : ℤ) : ℝ) =
        y + (j : ℝ) := by
      simp [Equiv.addRight]
      ring
    rw [hsign, harg]
    ring
  constructor
  · exact hstep x
  · have harg : x + 2 = (x + 1) + 1 := by ring
    rw [harg, hstep (x + 1), hstep x]
    ring


theorem H_shift (f : ℝ → ℝ) (x : ℝ) (n : ℤ) :
    Halt f (x + n) = (-1 : ℝ) ^ n * Halt f x := by
  unfold Halt
  rw [← (Equiv.addRight (-n)).tsum_eq
    (fun k : ℤ => (-1 : ℝ) ^ k * f (x + n + k))]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro j
  change (-1 : ℝ) ^ ((Equiv.addRight (-n)) j) *
      f (x + n + ((Equiv.addRight (-n)) j : ℤ)) =
    (-1 : ℝ) ^ n * ((-1 : ℝ) ^ j * f (x + j))
  have hsign : (-1 : ℝ) ^ (((Equiv.addRight (-n)) j)) =
      (-1 : ℝ) ^ n * (-1 : ℝ) ^ j := by
    have hadd := (sign j (-n)).2.2.1
    have hneg := (sign n 0).2.1
    have heq : ((Equiv.addRight (-n)) j) = j + -n := by
      rfl
    rw [heq, hadd, hneg]
    ring
  have harg : x + (n : ℝ) + (((Equiv.addRight (-n)) j : ℤ) : ℝ) =
      x + (j : ℝ) := by
    change x + (n : ℝ) + ((j + -n : ℤ) : ℝ) = x + (j : ℝ)
    norm_num
    ring
  rw [hsign, harg]
  ring


theorem H_scale (f : ℝ → ℝ) (C η x : ℝ) :
    Halt (fun y : ℝ => C * f (y - η)) x = C * Halt f (x - η) := by
  unfold Halt
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  change (-1 : ℝ) ^ k * (C * f (x + k - η)) =
    C * ((-1 : ℝ) ^ k * f (x - η + k))
  have harg : x + k - η = x - η + k := by ring
  rw [harg]
  ring


theorem lattice_global (F : ℝ → ℝ) (b : ℤ → ℝ) (hb_sum : Summable b)
    (hb : ∀ (k : ℤ), ∀ x ∈ Set.Icc (0 : ℝ) 1, |F (x + k)| ≤ b k) :
    (∀ y : ℝ, |F y| ≤ ∑' k : ℤ, b k) ∧
      ∀ y : ℝ,
        Summable (fun k : ℤ => |F (y + k)|) ∧
        (∑' k : ℤ, |F (y + k)|) ≤ ∑' k : ℤ, b k ∧
        |Halt F y| ≤ (∑' k : ℤ, |F (y + k)|) ∧
        |Halt F y| ≤ ∑' k : ℤ, b k := by
  have henv := env_lattice F b hb_sum hb
  have hb_nonneg : ∀ k : ℤ, 0 ≤ b k := henv.1
  have hsingle_le_tsum : ∀ j : ℤ, b j ≤ ∑' k : ℤ, b k := by
    intro j
    have hsum := hb_sum.sum_le_tsum ({j} : Finset ℤ) (fun i hi => hb_nonneg i)
    simpa using hsum
  have hdecomp_bound : ∀ y : ℝ, ∃ j0 : ℤ, ∃ y0 : ℝ,
      0 ≤ y0 ∧ y0 ≤ 1 ∧ y = y0 + j0 ∧
        ∀ k : ℤ, |F (y + k)| ≤ b (k + j0) := by
    intro y
    let j0 : ℤ := Int.floor y
    let y0 : ℝ := y - (j0 : ℝ)
    have hy0_nonneg : 0 ≤ y0 := by
      simp [y0, j0, Int.self_sub_floor, Int.fract_nonneg y]
    have hy0_le_one : y0 ≤ 1 := by
      have hy0_lt : y0 < 1 := by
        simpa [y0, j0, Int.self_sub_floor] using Int.fract_lt_one y
      exact le_of_lt hy0_lt
    have hy_decomp : y = y0 + (j0 : ℝ) := by
      dsimp [y0]
      ring
    refine ⟨j0, y0, hy0_nonneg, hy0_le_one, hy_decomp, ?_⟩
    intro k
    have hbase : |F (y0 + (k + j0 : ℤ))| ≤ b (k + j0) :=
      hb (k + j0) y0 ⟨hy0_nonneg, hy0_le_one⟩
    have harg : y + (k : ℝ) = y0 + ((k + j0 : ℤ) : ℝ) := by
      rw [hy_decomp]
      norm_num
      ring
    rw [harg]
    simpa [Int.cast_add] using hbase
  constructor
  · intro y
    rcases hdecomp_bound y with ⟨j0, _y0, _hy0_nonneg, _hy0_le_one, _hy, hbound_shift⟩
    have h0 := hbound_shift 0
    simpa using le_trans h0 (hsingle_le_tsum (0 + j0))
  · intro y
    rcases hdecomp_bound y with ⟨j0, _y0, _hy0_nonneg, _hy0_le_one, _hy, hbound_shift⟩
    let c : ℤ → ℝ := fun k => b (k + j0)
    have hc_sum : Summable c := by
      simpa [c, Function.comp_def, Equiv.addRight] using
        ((Equiv.addRight j0).summable_iff (f := b)).mpr hb_sum
    have hc_tsum : (∑' k : ℤ, c k) = ∑' k : ℤ, b k := by
      simpa [c, Function.comp_def, Equiv.addRight] using
        ((Equiv.addRight j0).tsum_eq b)
    have hle : ∀ k : ℤ, |F (y + k)| ≤ c k := by
      intro k
      simpa [c] using hbound_shift k
    have habs_sum : Summable (fun k : ℤ => |F (y + k)|) :=
      Summable.of_nonneg_of_le (fun k => abs_nonneg _) hle hc_sum
    have hsum_le : (∑' k : ℤ, |F (y + k)|) ≤ ∑' k : ℤ, b k := by
      have hle_c := Summable.tsum_le_tsum hle habs_sum hc_sum
      simpa [hc_tsum] using hle_c
    have hnorm_sum : Summable (fun k : ℤ => ‖(-1 : ℝ) ^ k * F (y + k)‖) := by
      convert habs_sum using 1
      ext k
      simp [Real.norm_eq_abs]
    have hH_le : |Halt F y| ≤ ∑' k : ℤ, |F (y + k)| := by
      unfold Halt
      calc
        |∑' k : ℤ, (-1 : ℝ) ^ k * F (y + k)| =
            ‖∑' k : ℤ, (-1 : ℝ) ^ k * F (y + k)‖ := by
          simp [Real.norm_eq_abs]
        _ ≤ ∑' k : ℤ, ‖(-1 : ℝ) ^ k * F (y + k)‖ :=
          norm_tsum_le_tsum_norm hnorm_sum
        _ = ∑' k : ℤ, |F (y + k)| := by
          apply tsum_congr
          intro k
          simp [Real.norm_eq_abs]
    exact ⟨habs_sum, hsum_le, hH_le, le_trans hH_le hsum_le⟩


theorem antiper_nfold (φ : ℝ → ℝ)
    (hφ : ∀ x : ℝ, φ (x + 1) = -φ x) :
    ∀ (x : ℝ) (n : ℤ), φ (x + n) = (-1 : ℝ) ^ n * φ x := by
  intro x n
  revert x
  refine Int.induction_on n ?zero ?succ ?pred
  · intro x
    simp
  · intro i ih x
    have harg : x + ((i : ℤ) + 1 : ℤ) = (x + (i : ℤ)) + 1 := by
      norm_num
      ring
    rw [harg, hφ, ih]
    have hsign := (sign (i : ℤ) 0).1
    rw [hsign]
    ring
  · intro i ih x
    have hprev : φ (x + ((-(i : ℤ)) - 1 : ℤ)) =
        -φ (x + (-(i : ℤ) : ℤ)) := by
      have h := hφ (x + ((-(i : ℤ)) - 1 : ℤ))
      have harg : x + ((-(i : ℤ)) - 1 : ℤ) + 1 =
          x + (-(i : ℤ) : ℤ) := by
        norm_num
        ring
      rw [harg] at h
      linarith
    rw [hprev, ih]
    have hsign : (-1 : ℝ) ^ ((-(i : ℤ)) - 1 : ℤ) =
        -((-1 : ℝ) ^ (-(i : ℤ) : ℤ)) := by
      have h := (sign ((-(i : ℤ)) - 1) 0).1
      have hpow : (((-(i : ℤ)) - 1 : ℤ) + 1 : ℤ) =
          (-(i : ℤ) : ℤ) := by ring
      rw [hpow] at h
      linarith
    rw [hsign]
    ring


theorem discrete (φ : ℝ → ℝ)
    (hφ : ∀ x : ℝ, φ (x + 1) = -φ x)
    (r ε : ℝ) (hε : ε = 1 ∨ ε = -1) (hr : φ r = 0)
    (hleft : ∀ x : ℝ, r - 1 < x → x < r → ε * φ x < 0)
    (hright : ∀ x : ℝ, r < x → x < r + 1 → 0 < ε * φ x) :
  {x : ℝ | φ x = 0} = {x : ℝ | ∃ n : ℤ, x = r + n} := by
  have _hε : ε = 1 ∨ ε = -1 := hε
  have _hleft := hleft
  ext x
  constructor
  · intro hx
    change φ x = 0 at hx
    let n : ℤ := Int.floor (x - r)
    let θ : ℝ := (x - r) - (n : ℝ)
    have hθ_nonneg : 0 ≤ θ := by
      simp [θ, n, Int.self_sub_floor, Int.fract_nonneg]
    have hθ_lt_one : θ < 1 := by
      simpa [θ, n, Int.self_sub_floor] using Int.fract_lt_one (x - r)
    by_cases hθ_zero : θ = 0
    · refine ⟨n, ?_⟩
      have hsubzero : (x - r) - (n : ℝ) = 0 := by
        simpa [θ, n, Int.self_sub_floor] using hθ_zero
      linarith
    · exfalso
      have hθ_pos : 0 < θ := lt_of_le_of_ne hθ_nonneg (Ne.symm hθ_zero)
      have hshift : x - (n : ℝ) = r + θ := by
        dsimp [θ]
        ring
      have hxnr_left : r < x - (n : ℝ) := by
        rw [hshift]
        linarith
      have hxnr_right : x - (n : ℝ) < r + 1 := by
        rw [hshift]
        linarith
      have hpos := hright (x - (n : ℝ)) hxnr_left hxnr_right
      have hphi_ne : φ (x - (n : ℝ)) ≠ 0 := by
        intro hzero
        rw [hzero, mul_zero] at hpos
        linarith
      have hanti := antiper_nfold φ hφ (x - (n : ℝ)) n
      have harg : x - (n : ℝ) + n = x := by
        exact sub_add_cancel x (n : ℝ)
      rw [harg] at hanti
      have hprod_zero : (-1 : ℝ) ^ n * φ (x - (n : ℝ)) = 0 := by
        rw [← hanti, hx]
      have hpow_ne : (-1 : ℝ) ^ n ≠ 0 := zpow_ne_zero n (by norm_num)
      exact (mul_ne_zero hpow_ne hphi_ne) hprod_zero
  · rintro ⟨n, rfl⟩
    change φ (r + n) = 0
    rw [antiper_nfold φ hφ r n, hr, mul_zero]


theorem no_flat (φ : ℝ → ℝ)
    (hφ : ∀ x : ℝ, φ (x + 1) = -φ x)
    (hcross : StrictOneCrossing φ) :
  ∀ α β : ℝ, α < β → ∃ x : ℝ, α < x ∧ x < β ∧ φ x ≠ 0 := by
  intro α β hαβ
  rcases hcross with ⟨r, ε, hε, hr, hleft, hright⟩
  let x1 : ℝ := (α + β) / 2
  let d : ℝ := min ((β - α) / 4) (1 / 2)
  let x2 : ℝ := x1 + d
  have hd_pos : 0 < d := by
    dsimp [d]
    exact lt_min (by linarith) (by norm_num)
  have hd_le_quarter : d ≤ (β - α) / 4 := by
    dsimp [d]
    exact min_le_left _ _
  have hd_le_half : d ≤ (1 / 2 : ℝ) := by
    dsimp [d]
    exact min_le_right _ _
  have hd_lt_one : d < 1 := by linarith
  have hx1_left : α < x1 := by
    dsimp [x1]
    linarith
  have hx1_right : x1 < β := by
    dsimp [x1]
    linarith
  have hx2_left : α < x2 := by
    dsimp [x2]
    linarith
  have hx2_right : x2 < β := by
    dsimp [x2, x1]
    linarith
  by_cases hx1_zero : φ x1 = 0
  · have hdisc := discrete φ hφ r ε hε hr hleft hright
    have hx1_lat : ∃ n : ℤ, x1 = r + n := by
      have hx1_mem : x1 ∈ ({x : ℝ | ∃ n : ℤ, x = r + n} : Set ℝ) := by
        rw [← hdisc]
        exact hx1_zero
      simpa using hx1_mem
    by_cases hx2_zero : φ x2 = 0
    · have hx2_lat : ∃ n : ℤ, x2 = r + n := by
        have hx2_mem : x2 ∈ ({x : ℝ | ∃ n : ℤ, x = r + n} : Set ℝ) := by
          rw [← hdisc]
          exact hx2_zero
        simpa using hx2_mem
      rcases hx1_lat with ⟨n1, hn1⟩
      rcases hx2_lat with ⟨n2, hn2⟩
      have hdiff_lat : x2 - x1 = (n2 - n1 : ℤ) := by
        rw [hn2, hn1]
        norm_num
      have hdiff_eq : x2 - x1 = d := by
        dsimp [x2]
        ring
      have hint_pos_real : 0 < ((n2 - n1 : ℤ) : ℝ) := by
        linarith
      have hint_lt_one_real : ((n2 - n1 : ℤ) : ℝ) < 1 := by
        linarith
      have hint_pos : 0 < n2 - n1 := by
        exact_mod_cast hint_pos_real
      have hint_lt : n2 - n1 < 1 := by
        exact_mod_cast hint_lt_one_real
      omega
    · exact ⟨x2, hx2_left, hx2_right, hx2_zero⟩
  · exact ⟨x1, hx1_left, hx1_right, hx1_zero⟩


theorem flat_shift (f : ℝ → ℝ) (α β : ℝ) (n : ℤ) (hαβ : α < β)
    (hflat : ∀ x : ℝ, α < x → x < β → Halt f x = 0) :
    ∀ y : ℝ, α + n < y → y < β + n → Halt f y = 0 := by
  have _ : α < β := hαβ
  intro y hy_left hy_right
  have hx_left : α < y - (n : ℝ) := by linarith
  have hx_right : y - (n : ℝ) < β := by linarith
  calc
    Halt f y = Halt f ((y - (n : ℝ)) + n) := by
      congr 1
      ring
    _ = (-1 : ℝ) ^ n * Halt f (y - (n : ℝ)) := H_shift f (y - (n : ℝ)) n
    _ = 0 := by
      rw [hflat (y - (n : ℝ)) hx_left hx_right]
      ring
