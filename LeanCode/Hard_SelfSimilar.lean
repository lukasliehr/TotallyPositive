import LeanCode.E7Vocab
import LeanCode.Construction
import LeanCode.SelfSimilarPrereqs
import LeanCode.Hard_OpnormL1























open Filter Topology
open scoped ENNReal

namespace Assembly.Hard

noncomputable section



theorem sawtooth_int_periodic (t : ℝ) (n : ℤ) :
    Assembly.Construction.sawtooth (t + n) = Assembly.Construction.sawtooth t := by
  unfold Assembly.Construction.sawtooth
  rw [Int.ceil_add_intCast]; push_cast; ring

theorem sawtooth_continuousAt {t : ℝ} (ht : ∀ z : ℤ, (z : ℝ) ≠ t) :
    ContinuousAt Assembly.Construction.sawtooth t := by
  have hfloor : t ≠ (⌊t⌋ : ℝ) := fun h => ht ⌊t⌋ h.symm
  have hfract : ContinuousAt Int.fract t := continuousAt_fract hfloor
  have hEq : Assembly.Construction.sawtooth =ᶠ[nhds t] (fun s => 1 - Int.fract s) := by
    have hlo : (⌊t⌋ : ℝ) < t := lt_of_le_of_ne (Int.floor_le t) (Ne.symm hfloor)
    have hhi : t < (⌊t⌋ : ℝ) + 1 := Int.lt_floor_add_one t
    have hmem : t ∈ Set.Ioo ((⌊t⌋:ℝ)) ((⌊t⌋:ℝ)+1) := ⟨hlo, hhi⟩
    filter_upwards [isOpen_Ioo.mem_nhds hmem] with s hs
    obtain ⟨hs1, hs2⟩ := hs
    have hfl : ⌊s⌋ = ⌊t⌋ := Int.floor_eq_iff.mpr ⟨le_of_lt hs1, hs2⟩
    have hce : ⌈s⌉ = ⌊t⌋ + 1 := by
      apply Int.ceil_eq_iff.mpr; push_cast; constructor <;> linarith
    unfold Assembly.Construction.sawtooth Int.fract
    rw [hce, hfl]; push_cast; ring
  rw [continuousAt_congr hEq]
  exact continuousAt_const.sub hfract




theorem delta_conv (x α a : ℝ) (hα : 0 < α) (ha : a ∉ Assembly.Construction.badSet x α)
    (q : ℕ → ℕ)
    (hr : Filter.Tendsto (fun n => |(q n : ℝ)/α - round ((q n:ℝ)/α)|) Filter.atTop (nhds 0))
    (k : ℤ) :
    Filter.Tendsto (fun n => Assembly.Construction.deltaSeq x α a (k + (q n : ℤ))) Filter.atTop
      (nhds (Assembly.Construction.deltaSeq x α a k)) := by
  set tk : ℝ := ((k:ℝ) + a - x)/α with htk
  have hα0 : α ≠ 0 := ne_of_gt hα
  have htk_ni : ∀ z : ℤ, (z:ℝ) ≠ tk := fun z hz =>
    Assembly.Construction.tk_not_int x α a hα ha k ⟨z, hz⟩
  have harg : ∀ n, (((k + (q n:ℤ) : ℤ):ℝ) + a - x)/α = tk + (q n:ℝ)/α := by
    intro n; rw [htk]; push_cast; field_simp; ring
  set r : ℕ → ℝ := fun n => (q n:ℝ)/α - round ((q n:ℝ)/α) with hrdef
  have hsaweq : ∀ n, Assembly.Construction.sawtooth (tk + (q n:ℝ)/α)
      = Assembly.Construction.sawtooth (tk + r n) := by
    intro n
    have h : tk + (q n:ℝ)/α = (tk + r n) + ((round ((q n:ℝ)/α) : ℤ) : ℝ) := by
      rw [hrdef]; push_cast; ring
    rw [h, sawtooth_int_periodic]
  have hr0 : Filter.Tendsto r Filter.atTop (nhds 0) := by
    rw [Metric.tendsto_atTop] at hr ⊢
    intro ε hε; obtain ⟨N, hN⟩ := hr ε hε
    exact ⟨N, fun n hn => by simpa [hrdef, Real.dist_eq, abs_abs] using hN n hn⟩
  have htend_arg : Filter.Tendsto (fun n => tk + r n) Filter.atTop (nhds tk) := by
    simpa using hr0.const_add tk
  have hcont : ContinuousAt Assembly.Construction.sawtooth tk := sawtooth_continuousAt htk_ni
  have hsaw_tend : Filter.Tendsto (fun n => Assembly.Construction.sawtooth (tk + r n)) Filter.atTop
      (nhds (Assembly.Construction.sawtooth tk)) := hcont.tendsto.comp htend_arg
  have hval : Assembly.Construction.deltaSeq x α a k = a + α * Assembly.Construction.sawtooth tk := by
    unfold Assembly.Construction.deltaSeq; rw [htk]
  rw [hval]
  have heq : (fun n => Assembly.Construction.deltaSeq x α a (k + (q n:ℤ)))
      = fun n => a + α * Assembly.Construction.sawtooth (tk + r n) := by
    funext n; unfold Assembly.Construction.deltaSeq; rw [harg n, hsaweq n]
  rw [heq]
  simpa using (hsaw_tend.const_mul α).const_add a


theorem delta_periodic (x α a : ℝ) (hα : 0 < α) (p m : ℤ)
    (hpm : (p:ℝ)/α = (m:ℤ)) (k : ℤ) :
    Assembly.Construction.deltaSeq x α a (k + p) = Assembly.Construction.deltaSeq x α a k := by
  unfold Assembly.Construction.deltaSeq
  congr 1
  have harg : (((k + p : ℤ):ℝ) + a - x)/α = ((k:ℝ) + a - x)/α + (m:ℤ) := by
    rw [← hpm]; push_cast; field_simp; ring
  rw [harg, sawtooth_int_periodic]



open Assembly.E7

theorem opOfMatrix_apply_of_realizer (A : ℤ → ℤ → ℂ)
    (h : ∃ T : ℓ1 →L[ℂ] ℓ1, ∀ (c : ℓ1) (k : ℤ),
      (T c : ℤ → ℂ) k = ∑' l : ℤ, A k l * (c : ℤ → ℂ) l) :
    ∀ (c : ℓ1) (k : ℤ), (opOfMatrix A c : ℤ → ℂ) k = ∑' l : ℤ, A k l * (c : ℤ → ℂ) l := by
  unfold opOfMatrix; rw [dif_pos h]; exact h.choose_spec


theorem hsummable_base (η : ℝ) (hη : 1 < η) :
    Summable (fun k : ℤ => (1 + |(k:ℝ)|) ^ (-η)) := by
  have hbase : Summable (fun k : ℤ => |(k:ℝ)| ^ (-η)) := Real.summable_abs_int_rpow hη
  apply Summable.of_norm_bounded_eventually hbase
  rw [Filter.eventually_cofinite]
  apply Set.Finite.subset (Set.finite_singleton (0:ℤ))
  intro k hk
  simp only [Set.mem_setOf_eq, not_le] at hk
  simp only [Set.mem_singleton_iff]
  by_contra hk0
  apply absurd hk (not_lt.mpr _)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hkpos : (0:ℝ) < |(k:ℝ)| := by simp only [abs_pos]; exact_mod_cast hk0
  apply Real.rpow_le_rpow_of_nonpos hkpos (by linarith [le_abs_self (k:ℝ)]) (by linarith)

theorem col_summable (A : ℤ → ℤ → ℂ)
    (hdec : Assembly.E7.HasPolynomialOffDiagonalDecay A) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ l : ℤ, Summable (fun k : ℤ => ‖A k l‖) ∧ ∑' k : ℤ, ‖A k l‖ ≤ M := by
  obtain ⟨C, η, hC, hη, hbound⟩ := hdec
  have hbase := hsummable_base η hη
  have hmaj : Summable (fun k : ℤ => C * (1 + |(k:ℝ)|) ^ (-η)) := hbase.mul_left C
  refine ⟨∑' k : ℤ, C * (1 + |(k:ℝ)|) ^ (-η), tsum_nonneg (fun k => by positivity), ?_⟩
  intro l
  have hbnd_l : ∀ k : ℤ, ‖A k l‖ ≤ C * (1 + |((k - l : ℤ):ℝ)|) ^ (-η) := by
    intro k
    have := hbound k l
    have hcast : ((k - l : ℤ):ℝ) = (k:ℝ) - (l:ℝ) := by push_cast; ring
    rw [hcast]; exact this
  have hshift : Summable (fun k : ℤ => C * (1 + |((k - l : ℤ):ℝ)|) ^ (-η)) := by
    have h := ((Equiv.subRight l).summable_iff
      (f := fun k : ℤ => C * (1 + |(k:ℝ)|) ^ (-η))).mpr hmaj
    convert h using 1; funext k; simp [Equiv.subRight]
  have hsum_col : Summable (fun k : ℤ => ‖A k l‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hbnd_l hshift
  refine ⟨hsum_col, ?_⟩
  calc ∑' k : ℤ, ‖A k l‖ ≤ ∑' k : ℤ, C * (1 + |((k - l : ℤ):ℝ)|) ^ (-η) :=
        hsum_col.tsum_le_tsum hbnd_l hshift
    _ = ∑' k : ℤ, C * (1 + |(k:ℝ)|) ^ (-η) := by
        rw [← (Equiv.subRight l).tsum_eq (fun k : ℤ => C * (1 + |(k:ℝ)|) ^ (-η))]; rfl



theorem conj_realizes (A : ℤ → ℤ → ℂ) (G : ℓ1 →L[ℂ] ℓ1)
    (hG : ∀ (c : ℓ1) (k : ℤ), (G c : ℤ → ℂ) k = ∑' l : ℤ, A k l * (c : ℤ → ℂ) l)
    (q : ℤ) (c : ℓ1) (k : ℤ) :
    ((shiftCLM (-q) ∘L G ∘L shiftCLM q) c : ℤ → ℂ) k
      = ∑' l : ℤ, A (k + q) (l + q) * (c : ℤ → ℂ) l := by
  simp only [ContinuousLinearMap.comp_apply]
  rw [shiftCLM_apply]
  have hkq : k - (-q) = k + q := by ring
  rw [hkq, hG]
  calc ∑' l : ℤ, A (k+q) l * (shiftCLM q c : ℤ → ℂ) l
      = ∑' l : ℤ, A (k+q) l * (c : ℤ → ℂ) (l - q) := by
        apply tsum_congr; intro l; rw [shiftCLM_apply q c l]
    _ = ∑' l : ℤ, A (k+q) (l + q) * (c : ℤ → ℂ) l := by
        rw [← (Equiv.addRight q).tsum_eq (fun l => A (k+q) l * (c:ℤ→ℂ) (l - q))]
        apply tsum_congr; intro l; simp [Equiv.addRight]



theorem clm_ext_coord (S T : ℓ1 →L[ℂ] ℓ1)
    (h : ∀ (c : ℓ1) (k : ℤ), (S c : ℤ → ℂ) k = (T c : ℤ → ℂ) k) : S = T := by
  apply ContinuousLinearMap.ext; intro c; apply lp.ext; funext k; exact h c k


theorem conj_eq_of_shift_invariant (A : ℤ → ℤ → ℂ) (G : ℓ1 →L[ℂ] ℓ1)
    (hG : ∀ (c : ℓ1) (k : ℤ), (G c : ℤ → ℂ) k = ∑' l : ℤ, A k l * (c : ℤ → ℂ) l)
    (q : ℤ) (hinv : ∀ k l : ℤ, A (k + q) (l + q) = A k l) :
    shiftCLM (-q) ∘L G ∘L shiftCLM q = G := by
  apply clm_ext_coord; intro c k
  rw [conj_realizes A G hG q c k, hG c k]
  apply tsum_congr; intro l; rw [hinv k l]

theorem projComp_realizes (M : ℤ → ℤ → ℂ) (D : ℓ1 →L[ℂ] ℓ1)
    (hD : ∀ (c : ℓ1) (k : ℤ), (D c : ℤ → ℂ) k = ∑' l : ℤ, M k l * (c : ℤ → ℂ) l)
    (m : ℕ) (c : ℓ1) (k : ℤ) :
    ((projCLM m ∘L D) c : ℤ → ℂ) k
      = ∑' l : ℤ, (if |k| ≤ (m:ℤ) then M k l else 0) * (c : ℤ → ℂ) l := by
  simp only [ContinuousLinearMap.comp_apply]
  rw [projCLM_apply]
  by_cases hk : |k| ≤ (m:ℤ)
  · rw [if_pos hk, hD c k]; apply tsum_congr; intro l; rw [if_pos hk]
  · rw [if_neg hk]; simp only [if_neg hk, zero_mul, tsum_zero]

theorem compProj_realizes (M : ℤ → ℤ → ℂ) (D : ℓ1 →L[ℂ] ℓ1)
    (hD : ∀ (c : ℓ1) (k : ℤ), (D c : ℤ → ℂ) k = ∑' l : ℤ, M k l * (c : ℤ → ℂ) l)
    (m : ℕ) (c : ℓ1) (k : ℤ) :
    ((D ∘L projCLM m) c : ℤ → ℂ) k
      = ∑' l : ℤ, (if |l| ≤ (m:ℤ) then M k l else 0) * (c : ℤ → ℂ) l := by
  simp only [ContinuousLinearMap.comp_apply]
  rw [hD (projCLM m c) k]
  apply tsum_congr; intro l
  rw [projCLM_apply]
  by_cases hl : |l| ≤ (m:ℤ)
  · rw [if_pos hl, if_pos hl]
  · rw [if_neg hl, if_neg hl, mul_zero, zero_mul]


theorem norm_projComp_le (M : ℤ → ℤ → ℂ) (D : ℓ1 →L[ℂ] ℓ1)
    (hD : ∀ (c : ℓ1) (k : ℤ), (D c : ℤ → ℂ) k = ∑' l : ℤ, M k l * (c : ℤ → ℂ) l)
    (m : ℕ) (S : ℝ) (hS : 0 ≤ S)
    (hcol : ∀ l : ℤ, Summable (fun k : ℤ => ‖(if |k| ≤ (m:ℤ) then M k l else 0)‖)
      ∧ ∑' k : ℤ, ‖(if |k| ≤ (m:ℤ) then M k l else 0)‖ ≤ S) :
    ‖projCLM m ∘L D‖ ≤ S := by
  obtain ⟨T, hT_real, hT_norm⟩ :=
    Assembly.Endgame.opnorm_l1_col_sup_proof (fun k l => if |k| ≤ (m:ℤ) then M k l else 0) S hS hcol
  have heq : projCLM m ∘L D = T := by
    apply clm_ext_coord; intro c k; rw [projComp_realizes M D hD m c k, hT_real c k]
  rw [heq]; exact hT_norm


theorem norm_compProj_le (M : ℤ → ℤ → ℂ) (D : ℓ1 →L[ℂ] ℓ1)
    (hD : ∀ (c : ℓ1) (k : ℤ), (D c : ℤ → ℂ) k = ∑' l : ℤ, M k l * (c : ℤ → ℂ) l)
    (m : ℕ) (S : ℝ) (hS : 0 ≤ S)
    (hcol : ∀ l : ℤ, Summable (fun k : ℤ => ‖(if |l| ≤ (m:ℤ) then M k l else 0)‖)
      ∧ ∑' k : ℤ, ‖(if |l| ≤ (m:ℤ) then M k l else 0)‖ ≤ S) :
    ‖D ∘L projCLM m‖ ≤ S := by
  obtain ⟨T, hT_real, hT_norm⟩ :=
    Assembly.Endgame.opnorm_l1_col_sup_proof (fun k l => if |l| ≤ (m:ℤ) then M k l else 0) S hS hcol
  have heq : D ∘L projCLM m = T := by
    apply clm_ext_coord; intro c k; rw [compProj_realizes M D hD m c k, hT_real c k]
  rw [heq]; exact hT_norm


theorem pconv_const (G : ℓ1 →L[ℂ] ℓ1) (Aseq : ℕ → ℓ1 →L[ℂ] ℓ1)
    (heq : ∀ j, Aseq j = G) : PConvergesTo Aseq G := by
  intro m ε hε
  refine ⟨0, fun j _ => ?_⟩
  rw [heq j, sub_self]
  simp only [ContinuousLinearMap.comp_zero, ContinuousLinearMap.zero_comp, norm_zero, add_zero]
  exact hε

theorem row_summable (A : ℤ → ℤ → ℂ) (Cb : ℝ) (hCb : ∀ k l, ‖A k l‖ ≤ Cb)
    (c : ℓ1) (k : ℤ) : Summable (fun l : ℤ => A k l * (c : ℤ → ℂ) l) := by
  have hc : Summable (fun l : ℤ => ‖(c : ℤ → ℂ) l‖) := memℓp_one_iff.mp (lp.memℓp c)
  apply Summable.of_norm_bounded (hc.mul_left Cb)
  intro l; rw [norm_mul]; gcongr; exact hCb k l


theorem diff_realizes (A A' : ℤ → ℤ → ℂ) (G H : ℓ1 →L[ℂ] ℓ1)
    (Cb : ℝ) (hCb : ∀ k l, ‖A k l‖ ≤ Cb) (hCb' : ∀ k l, ‖A' k l‖ ≤ Cb)
    (hG : ∀ (c : ℓ1) (k : ℤ), (G c : ℤ → ℂ) k = ∑' l : ℤ, A k l * (c : ℤ → ℂ) l)
    (hH : ∀ (c : ℓ1) (k : ℤ), (H c : ℤ → ℂ) k = ∑' l : ℤ, A' k l * (c : ℤ → ℂ) l)
    (c : ℓ1) (k : ℤ) :
    ((H - G) c : ℤ → ℂ) k = ∑' l : ℤ, (A' k l - A k l) * (c : ℤ → ℂ) l := by
  have hsumA : Summable (fun l : ℤ => A k l * (c : ℤ → ℂ) l) := row_summable A Cb hCb c k
  have hsumA' : Summable (fun l : ℤ => A' k l * (c : ℤ → ℂ) l) := row_summable A' Cb hCb' c k
  rw [sub_apply]
  show (H c : ℤ → ℂ) k - (G c : ℤ → ℂ) k = _
  rw [hH c k, hG c k, ← hsumA'.tsum_sub hsumA]
  apply tsum_congr; intro l; ring



open Assembly.Construction Assembly.SelfSim


theorem delta_bdd (x α a : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (ha : a ∉ Assembly.Construction.badSet x α) :
    ∀ k : ℤ, Assembly.Construction.deltaSeq x α a k ∈ Set.Icc (-(|a|+α+1)) (|a|+α+1) := by
  intro k; obtain ⟨h0, h1⟩ := Assembly.Construction.deltaSeq_mem_Ioo x α a hα ha k
  exact ⟨by linarith [neg_abs_le a], by linarith [le_abs_self a]⟩


theorem entry_norm (g : ℝ → ℝ) (δ : ℤ → ℝ) (q k l : ℤ) :
    ‖Assembly.GaborSubmatrixC g δ (k + q) (l + q) - Assembly.GaborSubmatrixC g δ k l‖
      = |g ((k:ℝ) - l + δ (k + q)) - g ((k:ℝ) - l + δ k)| := by
  unfold Assembly.GaborSubmatrixC
  rw [← Complex.ofReal_sub, Complex.norm_real]
  congr 1
  have h1 : ((k + q : ℤ):ℝ) + δ (k+q) - ((l + q : ℤ):ℝ) = (k:ℝ) - l + δ (k+q) := by
    push_cast; ring
  have h2 : ((k:ℤ):ℝ) + δ k - ((l:ℤ):ℝ) = (k:ℝ) - l + δ k := by ring
  rw [h1, h2]


theorem col_diff_summable (g : ℝ → ℝ) (hg : Continuous g) (hpd : Assembly.HasPolynomialDecay g)
    (R : ℝ) (hR : 0 < R) (v w : ℤ → ℝ)
    (hv : ∀ k, v k ∈ Set.Icc (-R) R) (hw : ∀ k, w k ∈ Set.Icc (-R) R) (l : ℤ) :
    Summable (fun k : ℤ => |g ((k:ℝ) - l + v k) - g ((k:ℝ) - l + w k)|) := by
  have hbj : Summable (bj g R) := bj_summable g hg hpd hR
  have hshift : Summable (fun k : ℤ => bj g R (k - l)) := by
    have hinj : Function.Injective (fun k : ℤ => k - l) := fun a b h => by simpa using h
    exact hbj.comp_injective hinj
  have hbound : Summable (fun k : ℤ => 2 * bj g R (k - l)) := hshift.mul_left 2
  apply Summable.of_nonneg_of_le (fun k => abs_nonneg _) _ hbound
  intro k
  have hcast : ((k - l : ℤ):ℝ) = (k:ℝ) - l := by push_cast; ring
  have h1 : |g ((k:ℝ) - l + v k)| ≤ bj g R (k - l) := by
    have := le_bj g hg (k - l) (v := v k) (hv k); rwa [hcast] at this
  have h2 : |g ((k:ℝ) - l + w k)| ≤ bj g R (k - l) := by
    have := le_bj g hg (k - l) (v := w k) (hw k); rwa [hcast] at this
  have htri : |g ((k:ℝ) - l + v k) - g ((k:ℝ) - l + w k)|
      ≤ |g ((k:ℝ) - l + v k)| + |g ((k:ℝ) - l + w k)| := by
    have := abs_sub_le (g ((k:ℝ) - l + v k)) 0 (g ((k:ℝ) - l + w k)); simpa using this
  calc |g ((k:ℝ) - l + v k) - g ((k:ℝ) - l + w k)|
      ≤ |g ((k:ℝ) - l + v k)| + |g ((k:ℝ) - l + w k)| := htri
    _ ≤ bj g R (k - l) + bj g R (k - l) := by gcongr
    _ = 2 * bj g R (k - l) := by ring


theorem bj_bddAbove (g : ℝ → ℝ) (hg : Continuous g) (hpd : Assembly.HasPolynomialDecay g)
    (R : ℝ) (hR : 0 < R) : ∃ B, 0 ≤ B ∧ ∀ m : ℤ, bj g R m ≤ B := by
  have hbj : Summable (bj g R) := bj_summable g hg hpd hR
  have hbj_cofin : Filter.Tendsto (bj g R) Filter.cofinite (nhds 0) := hbj.tendsto_cofinite_zero
  have hfin : {m : ℤ | 1 ≤ bj g R m}.Finite := by
    have hev : ∀ᶠ m in Filter.cofinite, bj g R m < 1 :=
      hbj_cofin.eventually (eventually_lt_nhds (by norm_num))
    rw [Filter.eventually_cofinite] at hev
    exact hev.subset (fun m hm => not_lt.mpr hm)
  obtain ⟨B₀, hB₀⟩ := (hfin.image (bj g R)).bddAbove
  refine ⟨max 1 B₀, le_trans zero_le_one (le_max_left _ _), fun m => ?_⟩
  rcases lt_or_ge (bj g R m) 1 with h | h
  · exact h.le.trans (le_max_left _ _)
  · exact (hB₀ (Set.mem_image_of_mem _ h)).trans (le_max_right _ _)


theorem shiftSup_bddAbove (g : ℝ → ℝ) (hg : Continuous g) (R : ℝ)
    (B : ℝ) (hB : ∀ m : ℤ, bj g R m ≤ B) (v w : ℝ)
    (hv : v ∈ Set.Icc (-R) R) (hw : w ∈ Set.Icc (-R) R) :
    BddAbove (Set.range (fun m' : ℤ => |g ((m':ℝ) + v) - g ((m':ℝ) + w)|)) := by
  refine ⟨2 * B, ?_⟩
  rintro _ ⟨m', rfl⟩
  have h1 : |g ((m':ℝ) + v)| ≤ bj g R m' := le_bj g hg m' hv
  have h2 : |g ((m':ℝ) + w)| ≤ bj g R m' := le_bj g hg m' hw
  have htri : |g ((m':ℝ) + v) - g ((m':ℝ) + w)| ≤ |g ((m':ℝ) + v)| + |g ((m':ℝ) + w)| := by
    have := abs_sub_le (g ((m':ℝ) + v)) 0 (g ((m':ℝ) + w)); simpa using this
  calc |g ((m':ℝ) + v) - g ((m':ℝ) + w)| ≤ |g ((m':ℝ) + v)| + |g ((m':ℝ) + w)| := htri
    _ ≤ bj g R m' + bj g R m' := by gcongr
    _ ≤ B + B := by gcongr <;> exact hB m'
    _ = 2 * B := by ring


theorem entry_le_shiftSup (g : ℝ → ℝ) (hg : Continuous g) (R : ℝ)
    (B : ℝ) (hB : ∀ m : ℤ, bj g R m ≤ B) (v w : ℝ)
    (hv : v ∈ Set.Icc (-R) R) (hw : w ∈ Set.Icc (-R) R) (k l : ℤ) :
    |g ((k:ℝ) - l + v) - g ((k:ℝ) - l + w)| ≤ ⨆ m' : ℤ, |g ((m':ℝ) + v) - g ((m':ℝ) + w)| := by
  have hbdd := shiftSup_bddAbove g hg R B hB v w hv hw
  have hcast : ((k - l : ℤ):ℝ) = (k:ℝ) - l := by push_cast; ring
  have := le_ciSup hbdd (k - l); rw [hcast] at this; exact this


theorem columnSum_tendsto (g : ℝ → ℝ) (x α a : ℝ)
    (hg : Continuous g) (hpd : Assembly.HasPolynomialDecay g)
    (hα : 0 < α) (hα1 : α < 1) (ha : a ∉ Assembly.Construction.badSet x α)
    (q : ℕ → ℕ)
    (hr : Filter.Tendsto (fun n => |(q n : ℝ)/α - round ((q n:ℝ)/α)|) Filter.atTop (nhds 0))
    (l : ℤ) :
    Filter.Tendsto
      (fun n => ∑' k : ℤ, |g ((k:ℝ) - l + Assembly.Construction.deltaSeq x α a (k + (q n:ℤ)))
                            - g ((k:ℝ) - l + Assembly.Construction.deltaSeq x α a k)|)
      Filter.atTop (nhds 0) := by
  set R : ℝ := |a| + α + 1 with hR
  have hRpos : 0 < R := by rw [hR]; positivity
  exact Assembly.SelfSim.uniformCont_columnSum g hg hpd hRpos
    (fun k n => Assembly.Construction.deltaSeq x α a (k + (q n:ℤ)))
    (fun k => Assembly.Construction.deltaSeq x α a k)
    (fun k n => delta_bdd x α a hα hα1 ha (k + (q n:ℤ)))
    (fun k => delta_bdd x α a hα hα1 ha k)
    (fun k => delta_conv x α a hα ha q hr k) l


theorem shiftSup_tendsto (g : ℝ → ℝ) (x α a : ℝ)
    (hg : Continuous g) (hpd : Assembly.HasPolynomialDecay g)
    (hα : 0 < α) (hα1 : α < 1) (ha : a ∉ Assembly.Construction.badSet x α)
    (q : ℕ → ℕ)
    (hr : Filter.Tendsto (fun n => |(q n : ℝ)/α - round ((q n:ℝ)/α)|) Filter.atTop (nhds 0))
    (k : ℤ) :
    Filter.Tendsto
      (fun n => ⨆ m' : ℤ, |g ((m':ℝ) + Assembly.Construction.deltaSeq x α a (k + (q n:ℤ)))
                           - g ((m':ℝ) + Assembly.Construction.deltaSeq x α a k)|)
      Filter.atTop (nhds 0) := by
  set R : ℝ := |a| + α + 1 with hR
  have hRpos : 0 < R := by rw [hR]; positivity
  exact Assembly.SelfSim.uniformCont_shiftSup g hg hpd hRpos
    (fun n => Assembly.Construction.deltaSeq x α a (k + (q n:ℤ)))
    (Assembly.Construction.deltaSeq x α a k)
    (fun n => delta_bdd x α a hα hα1 ha (k + (q n:ℤ)))
    (delta_bdd x α a hα hα1 ha k)
    (delta_conv x α a hα ha q hr k)


theorem row_tsum_eq_finset (M : ℤ → ℤ → ℂ) (m : ℕ) (l : ℤ) :
    ∑' k : ℤ, ‖(if |k| ≤ (m:ℤ) then M k l else 0)‖
      = ∑ k ∈ Finset.Icc (-(m:ℤ)) (m:ℤ), ‖M k l‖ := by
  rw [tsum_eq_sum (s := Finset.Icc (-(m:ℤ)) (m:ℤ))]
  · refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [Finset.mem_Icc] at hk
    rw [if_pos (abs_le.mpr ⟨hk.1, hk.2⟩)]
  · intro k hk
    rw [Finset.mem_Icc, not_and_or] at hk
    have hkabs : ¬ |k| ≤ (m:ℤ) := fun h => by rw [abs_le] at h; tauto
    rw [if_neg hkabs, norm_zero]

theorem row_tsum_summable (M : ℤ → ℤ → ℂ) (m : ℕ) (l : ℤ) :
    Summable (fun k : ℤ => ‖(if |k| ≤ (m:ℤ) then M k l else 0)‖) := by
  apply summable_of_finite_support
  apply Set.Finite.subset (Finset.Icc (-(m:ℤ)) (m:ℤ)).finite_toSet
  intro k hk
  simp only [Function.mem_support, ne_eq] at hk
  rw [Finset.coe_Icc, Set.mem_Icc]
  by_contra hcon
  rw [not_and_or] at hcon
  apply hk
  have hkabs : ¬ |k| ≤ (m:ℤ) := fun h => by rw [abs_le] at h; tauto
  rw [if_neg hkabs, norm_zero]


theorem entries_bdd (A : ℤ → ℤ → ℂ) (hdec : Assembly.E7.HasPolynomialOffDiagonalDecay A) :
    ∃ Cb : ℝ, ∀ k l, ‖A k l‖ ≤ Cb := by
  obtain ⟨C, η, hC, hη, hbound⟩ := hdec
  refine ⟨C, fun k l => ?_⟩
  have hle1 : (1 + |(k:ℝ) - (l:ℝ)|) ^ (-η) ≤ 1 := by
    rw [Real.rpow_neg (by positivity), inv_le_one_iff₀]
    right; exact Real.one_le_rpow (by simp [abs_nonneg]) (by linarith)
  calc ‖A k l‖ ≤ C * (1 + |(k:ℝ) - (l:ℝ)|) ^ (-η) := hbound k l
    _ ≤ C * 1 := by gcongr
    _ = C := by ring






theorem winG_e7_decay
    (g : ℝ → ℝ) (δ : ℤ → ℝ)
    (hg : Assembly.HasPolynomialDecay g) (hδ : ∃ R : ℝ, ∀ k : ℤ, |δ k| ≤ R) :
    Assembly.E7.HasPolynomialOffDiagonalDecay (Assembly.GaborSubmatrixC g δ) := by
  obtain ⟨C, η, hC, hη, hbound⟩ :=
    Assembly.Construction.gaborSubmatrix_offDiagonalDecay g δ hg hδ
  refine ⟨C, η, hC, hη, ?_⟩
  intro k l
  have hnorm : ‖Assembly.GaborSubmatrixC g δ k l‖ = ‖Assembly.GaborSubmatrixR g δ k l‖ := by
    simp only [Assembly.GaborSubmatrixC, Assembly.GaborSubmatrixR, Complex.norm_real]
  rw [hnorm]
  have hden : (0 : ℝ) < (1 + |(k : ℝ) - (l : ℝ)|) ^ η :=
    Real.rpow_pos_of_pos (by positivity) η
  have hb := hbound k l
  rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv]
  exact hb





theorem selfSimilar_proof
    (g : ℝ → ℝ) (α a x : ℝ)
    (hg : Continuous g) (hpd : Assembly.HasPolynomialDecay g)
    (hα : 0 < α) (hα1 : α < 1)
    (ha : a ∉ Assembly.Construction.badSet x α) :
    Assembly.E7.opOfMatrix (Assembly.GaborSubmatrixC g (Assembly.Construction.deltaSeq x α a))
      ∈ Assembly.E7.operatorSpectrum
        (Assembly.E7.opOfMatrix (Assembly.GaborSubmatrixC g (Assembly.Construction.deltaSeq x α a))) := by
  set δ : ℤ → ℝ := Assembly.Construction.deltaSeq x α a with hδ
  set A : ℤ → ℤ → ℂ := Assembly.GaborSubmatrixC g δ with hA
  set G : ℓ1 →L[ℂ] ℓ1 := Assembly.E7.opOfMatrix A with hG

  have hδbdd : ∃ R : ℝ, ∀ k : ℤ, |δ k| ≤ R := by
    refine ⟨|a| + α + 1, fun k => ?_⟩
    obtain ⟨h0, h1⟩ := delta_bdd x α a hα hα1 ha k
    rw [abs_le]; exact ⟨h0, h1⟩

  have hdecay : Assembly.E7.HasPolynomialOffDiagonalDecay A :=
    winG_e7_decay g δ hpd hδbdd

  obtain ⟨Mbnd, hMbnd0, hcolA⟩ := col_summable A hdecay

  obtain ⟨T, hTreal, -⟩ := Assembly.Endgame.opnorm_l1_col_sup_proof A Mbnd hMbnd0 hcolA

  have hGreal : ∀ (c : ℓ1) (k : ℤ), (G c : ℤ → ℂ) k = ∑' l : ℤ, A k l * (c : ℤ → ℂ) l :=
    opOfMatrix_apply_of_realizer A ⟨T, hTreal⟩

  obtain ⟨Cb, hCb⟩ := entries_bdd A hdecay



  show G ∈ Assembly.E7.operatorSpectrum G
  rw [Assembly.E7.operatorSpectrum, Set.mem_setOf_eq, Assembly.E7.IsLimitOperator]
  by_cases hirr : Irrational (1 / α)
  ·
    obtain ⟨q, hqmono, hqdist⟩ := Assembly.SelfSim.exists_qn_dist_to_int α hirr
    refine ⟨fun j => (q j : ℤ), ?_, ?_⟩
    ·
      intro Mth
      refine ⟨Mth.toNat, fun j hj => ?_⟩
      have hqj : (Mth.toNat : ℤ) ≤ (q j : ℤ) := by
        have : (Mth.toNat : ℕ) ≤ q j := le_trans hj (hqmono.id_le j)
        exact_mod_cast this
      calc Mth ≤ (Mth.toNat : ℤ) := Int.self_le_toNat Mth
        _ ≤ (q j : ℤ) := hqj
        _ ≤ |(q j : ℤ)| := le_abs_self _
    ·
      intro m ε hε

      set R : ℝ := |a| + α + 1 with hRdef
      have hRpos : 0 < R := by rw [hRdef]; positivity
      obtain ⟨B, hB0, hBbnd⟩ := bj_bddAbove g hg hpd R hRpos

      set Srow : ℕ → ℝ := fun j =>
        ∑ k ∈ Finset.Icc (-(m:ℤ)) (m:ℤ),
          ⨆ m' : ℤ, |g ((m':ℝ) + δ (k + (q j:ℤ))) - g ((m':ℝ) + δ k)| with hSrow
      set Scol : ℕ → ℝ := fun j =>
        ∑ l ∈ Finset.Icc (-(m:ℤ)) (m:ℤ),
          ∑' k : ℤ, |g ((k:ℝ) - l + δ (k + (q j:ℤ))) - g ((k:ℝ) - l + δ k)| with hScol

      have hSrow0 : Filter.Tendsto Srow Filter.atTop (nhds 0) := by
        have : Filter.Tendsto Srow Filter.atTop
            (nhds (∑ _k ∈ Finset.Icc (-(m:ℤ)) (m:ℤ), (0:ℝ))) := by
          apply tendsto_finset_sum
          intro k _
          exact shiftSup_tendsto g x α a hg hpd hα hα1 ha q hqdist k
        simpa using this

      have hScol0 : Filter.Tendsto Scol Filter.atTop (nhds 0) := by
        have : Filter.Tendsto Scol Filter.atTop
            (nhds (∑ _l ∈ Finset.Icc (-(m:ℤ)) (m:ℤ), (0:ℝ))) := by
          apply tendsto_finset_sum
          intro l _
          exact columnSum_tendsto g x α a hg hpd hα hα1 ha q hqdist l
        simpa using this

      have hsum0 : Filter.Tendsto (fun j => Srow j + Scol j) Filter.atTop (nhds 0) := by
        simpa using hSrow0.add hScol0
      have heventually : ∀ᶠ j in Filter.atTop, Srow j + Scol j < ε := by
        have := hsum0.eventually (eventually_lt_nhds hε)
        filter_upwards [this] with j hj
        simpa using hj
      rw [Filter.eventually_atTop] at heventually
      obtain ⟨N, hN⟩ := heventually
      refine ⟨N, fun j hj => ?_⟩

      set qj : ℤ := (q j : ℤ) with hqj
      set H : ℓ1 →L[ℂ] ℓ1 := shiftCLM (-qj) ∘L G ∘L shiftCLM qj with hHdef
      have hHreal : ∀ (c : ℓ1) (k : ℤ), (H c : ℤ → ℂ) k
          = ∑' l : ℤ, A (k + qj) (l + qj) * (c : ℤ → ℂ) l :=
        fun c k => conj_realizes A G hGreal qj c k

      set M : ℤ → ℤ → ℂ := fun k l => A (k + qj) (l + qj) - A k l with hM
      have hDreal : ∀ (c : ℓ1) (k : ℤ), ((H - G) c : ℤ → ℂ) k
          = ∑' l : ℤ, M k l * (c : ℤ → ℂ) l :=
        diff_realizes A (fun k l => A (k + qj) (l + qj)) G H Cb hCb
          (fun k l => hCb (k + qj) (l + qj)) hGreal hHreal

      have hMnorm : ∀ k l : ℤ, ‖M k l‖ = |g ((k:ℝ) - l + δ (k + qj)) - g ((k:ℝ) - l + δ k)| :=
        fun k l => entry_norm g δ qj k l

      have hrowbnd : ‖projCLM m ∘L (H - G)‖ ≤ Srow j := by
        apply norm_projComp_le M (H - G) hDreal m (Srow j)
        · rw [hSrow]; apply Finset.sum_nonneg; intro k _
          exact le_ciSup_of_le (shiftSup_bddAbove g hg R B hBbnd _ _
            (delta_bdd x α a hα hα1 ha (k + qj)) (delta_bdd x α a hα hα1 ha k)) 0
            (by positivity)
        · intro l
          refine ⟨row_tsum_summable M m l, ?_⟩
          rw [row_tsum_eq_finset M m l]
          rw [hSrow]
          apply Finset.sum_le_sum
          intro k _
          rw [hMnorm k l]
          exact entry_le_shiftSup g hg R B hBbnd (δ (k + qj)) (δ k)
            (delta_bdd x α a hα hα1 ha (k + qj)) (delta_bdd x α a hα hα1 ha k) k l

      have hcolbnd : ‖(H - G) ∘L projCLM m‖ ≤ Scol j := by
        apply norm_compProj_le M (H - G) hDreal m (Scol j)
        · rw [hScol]; apply Finset.sum_nonneg; intro l _
          exact tsum_nonneg (fun k => abs_nonneg _)
        · intro l
          by_cases hl : |l| ≤ (m:ℤ)
          ·
            have hsum : Summable (fun k : ℤ =>
                |g ((k:ℝ) - l + δ (k + qj)) - g ((k:ℝ) - l + δ k)|) :=
              col_diff_summable g hg hpd R hRpos (fun k => δ (k + qj)) (fun k => δ k)
                (fun k => delta_bdd x α a hα hα1 ha (k + qj))
                (fun k => delta_bdd x α a hα hα1 ha k) l
            have hsummable : Summable (fun k : ℤ => ‖(if |l| ≤ (m:ℤ) then M k l else 0)‖) := by
              simp only [if_pos hl]
              simpa only [hMnorm] using hsum
            refine ⟨hsummable, ?_⟩
            have heq : (fun k : ℤ => ‖(if |l| ≤ (m:ℤ) then M k l else 0)‖)
                = fun k : ℤ => |g ((k:ℝ) - l + δ (k + qj)) - g ((k:ℝ) - l + δ k)| := by
              funext k; rw [if_pos hl, hMnorm k l]
            rw [heq, hScol]
            simp only []
            have hmem : l ∈ Finset.Icc (-(m:ℤ)) (m:ℤ) := by
              rw [Finset.mem_Icc]; rw [abs_le] at hl; exact hl
            exact Finset.single_le_sum (f := fun l : ℤ =>
              ∑' k : ℤ, |g ((k:ℝ) - l + δ (k + qj)) - g ((k:ℝ) - l + δ k)|)
              (a := l) (fun i _ => tsum_nonneg (fun k => abs_nonneg _)) hmem
          ·
            have hz : (fun k : ℤ => ‖(if |l| ≤ (m:ℤ) then M k l else 0)‖)
                = fun _ => (0:ℝ) := by funext k; rw [if_neg hl, norm_zero]
            rw [hz]
            refine ⟨summable_zero, ?_⟩
            rw [tsum_zero, hScol]
            apply Finset.sum_nonneg; intro l' _
            exact tsum_nonneg (fun k => abs_nonneg _)

      calc ‖projCLM m ∘L ((fun j => shiftCLM (-(q j:ℤ)) ∘L G ∘L shiftCLM (q j:ℤ)) j - G)‖
            + ‖((fun j => shiftCLM (-(q j:ℤ)) ∘L G ∘L shiftCLM (q j:ℤ)) j - G) ∘L projCLM m‖
          = ‖projCLM m ∘L (H - G)‖ + ‖(H - G) ∘L projCLM m‖ := by rw [hHdef, hqj]
        _ ≤ Srow j + Scol j := by gcongr
        _ < ε := hN j hj
  ·

    rw [Irrational] at hirr
    push_neg at hirr
    obtain ⟨r, hr⟩ := hirr
    have hα0 : α ≠ 0 := ne_of_gt hα

    have hinv : (1 : ℝ) / α = (r : ℝ) := hr.symm
    set p : ℤ := (r.den : ℤ) with hp
    have hpden_pos : 0 < r.den := r.pos
    have hp_pos : 0 < p := by rw [hp]; exact_mod_cast hpden_pos
    have hden : (r.den : ℝ) ≠ 0 := by exact_mod_cast hpden_pos.ne'

    have hpm : (p:ℝ)/α = ((r.num : ℤ) : ℝ) := by
      rw [hp]
      have h1 : (r.den : ℝ) / α = (r.den : ℝ) * (1 / α) := by ring
      have hnd : (r.num : ℝ) = (r : ℝ) * (r.den : ℝ) := by
        rw [Rat.cast_def]; field_simp
      push_cast
      rw [h1, hinv, hnd]; ring
    refine ⟨fun j => (j : ℤ) * p, ?_, ?_⟩
    ·
      intro Mth
      refine ⟨(Mth.toNat + 1), fun j hj => ?_⟩
      have hj1 : (Mth.toNat : ℤ) + 1 ≤ (j : ℤ) := by exact_mod_cast hj
      have hjp : (j : ℤ) ≤ (j : ℤ) * p := le_mul_of_one_le_right (by positivity) hp_pos
      calc Mth ≤ (Mth.toNat : ℤ) := Int.self_le_toNat Mth
        _ ≤ (j:ℤ) * p := by
            have : (Mth.toNat : ℤ) ≤ (j:ℤ) := by linarith
            exact le_trans this hjp
        _ ≤ |(j:ℤ) * p| := le_abs_self _
    ·
      apply pconv_const
      intro j

      apply conj_eq_of_shift_invariant A G hGreal ((j:ℤ) * p)
      intro k l

      have hjp_m : (((((j:ℤ) * p : ℤ)):ℝ))/α = (((j:ℤ) * r.num : ℤ) : ℝ) := by
        have hcast : ((((j:ℤ) * p : ℤ)):ℝ) = ((j:ℤ):ℝ) * ((p:ℤ):ℝ) := by push_cast; ring
        rw [hcast, mul_div_assoc, hpm]; push_cast; ring
      have hδeq : δ (k + (j:ℤ) * p) = δ k :=
        delta_periodic x α a hα ((j:ℤ) * p) ((j:ℤ) * r.num) hjp_m k
      rw [hA]
      unfold Assembly.GaborSubmatrixC
      have hlhsarg : (((k + (j:ℤ) * p : ℤ)):ℝ) + δ (k + (j:ℤ) * p) - (((l + (j:ℤ) * p : ℤ)):ℝ)
          = (k:ℝ) + δ k - (l:ℝ) := by
        rw [hδeq]; push_cast; ring
      rw [hlhsarg]

end

end Assembly.Hard
