import LeanCode.Vendor.E5.P5.Part5.Basic
import LeanCode.Vendor.E5.P5.Part5.SignChanges
import LeanCode.Vendor.E5.P5.Part5.VariationDiminishing
import LeanCode.Vendor.E5.P5.Part5.Operators
import LeanCode.Vendor.E5.P5.Part5.RealRooted
import LeanCode.Vendor.E5.Defs
open VendorE5






namespace Part5





theorem simple_case (h3 : Statement_Part_3) (g : ℝ → ℝ) (hg : Continuous g)
    (hint : MeasureTheory.Integrable g) (htp : IsTotallyPositive g) (hne : g ≠ 0)
    (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hbound : ∀ x : ℝ, |g x| ≤ C * Real.exp (-c * |x|))
    (β : ℕ → ℝ) (hrec : MomentReciprocal g β) (hβ0 : 0 < β 0)
    (p : Polynomial ℝ) (n : ℕ) (hn : 1 ≤ n) (hdeg : p.natDegree = n)
    (r : Fin n → ℝ) (hr : StrictMono r) (hroots : ∀ j, p.IsRoot (r j)) :
    RealRooted (PsiD β p) := by
  classical
  set q := PsiD β p with hq
  have hp : p ≠ 0 := by
    intro h; rw [h, Polynomial.natDegree_zero] at hdeg; omega
  obtain ⟨hqdeg0, hqlc⟩ := PsiD_degree β hβ0.ne' p hp
  have hqdeg : q.natDegree = n := by rw [hq, hqdeg0, hdeg]
  have hqne : q ≠ 0 := by
    rw [← Polynomial.leadingCoeff_ne_zero, hq, hqlc]
    exact mul_ne_zero hβ0.ne' (Polynomial.leadingCoeff_ne_zero.mpr hp)
  have hFDq : FD (mom g) q = p := by
    rw [hq]; exact FD_PsiD (mom g) β hrec.1 hrec.2 p
  have hconv : ∀ x, convPoly g q x = p.eval x := by
    intro x
    rw [conv_is_FD g hg C c hC hc hbound q x, hFDq]
  have hpsc : SignChangesFnGE (fun x => p.eval x) n :=
    simple_to_changes p n hn hdeg r hr hroots
  have hqsc0 : SignChangesFnGE (fun x => convPoly g q x) n := by
    have hfe : (fun x => convPoly g q x) = (fun x => p.eval x) := funext hconv
    rw [hfe]; exact hpsc
  have hqsc : SignChangesFnGE (fun x => q.eval x) n :=
    integral_VD h3 g hg htp C c hC hc hbound q n hqsc0
  obtain ⟨z, hzmono, hzroots⟩ := changes_to_zeros q n hqsc
  intro w hw
  by_contra him
  set Q : Polynomial ℂ := q.map (algebraMap ℝ ℂ) with hQ
  have hinj : Function.Injective (algebraMap ℝ ℂ) := by
    rw [Complex.coe_algebraMap]; exact Complex.ofReal_injective
  have hQne : Q ≠ 0 := by rw [hQ, Polynomial.map_ne_zero_iff hinj]; exact hqne
  have hQdeg : Q.natDegree = n := by
    rw [hQ, Polynomial.natDegree_map_eq_of_injective hinj q, hqdeg]
  have haeval : ∀ u : ℂ, Polynomial.aeval u q = Q.eval u := by
    intro u; rw [Polynomial.aeval_def, hQ, Polynomial.eval_map]
  have hwroot : Q.IsRoot w := by
    rw [Polynomial.IsRoot, ← haeval]; exact hw
  have hzQroot : ∀ i, Q.IsRoot ((z i : ℝ) : ℂ) := by
    intro i
    rw [Polynomial.IsRoot, ← haeval]
    have hcoe : ((z i : ℝ) : ℂ) = algebraMap ℝ ℂ (z i) := (Complex.coe_algebraMap ▸ rfl)
    rw [hcoe, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
    rw [show q.eval (z i) = 0 from hzroots i, map_zero]
  set rr : Fin (n + 1) → ℂ := Fin.snoc (fun i => ((z i : ℝ) : ℂ)) w with hrr
  have hcinj : Function.Injective (fun i => ((z i : ℝ) : ℂ)) :=
    Complex.ofReal_injective.comp hzmono.injective
  have hwnotmem : w ∉ Set.range (fun i => ((z i : ℝ) : ℂ)) := by
    rintro ⟨i, hi⟩
    apply him
    rw [← hi, Complex.ofReal_im]
  have hrrinj : Function.Injective rr := by
    rw [hrr]; exact Fin.snoc_injective_of_injective hcinj hwnotmem
  have hrrroots : ∀ j, Q.IsRoot (rr j) := by
    intro j
    rw [hrr]
    induction j using Fin.lastCases with
    | last => rw [Fin.snoc_last]; exact hwroot
    | cast i => rw [Fin.snoc_castSucc]; exact hzQroot i
  have hbnd := roots_bound Q hQne (n + 1) rr hrrinj hrrroots
  rw [hQdeg] at hbnd
  omega

end Part5



theorem Part_5_main (h3 : Statement_Part_3) : Statement_Part_5 := by
  intro g hgtpic hne hdecay
  obtain ⟨htp, hint, hcont⟩ := hgtpic
  obtain ⟨C, c, hC, hc, hbound⟩ := hdecay
  obtain ⟨β, hrec, hβ0⟩ := Part5.beta_exists g hcont hint htp hne C c hC hc hbound
  refine ⟨β, hrec, hβ0, ?_⟩
  intro n
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    intro z hz
    have hjp : jensenPoly β 0 = Polynomial.C (β 0) := by
      simp [jensenPoly]
    rw [hjp, Polynomial.aeval_C] at hz
    have hβ0ne : (algebraMap ℝ ℂ) (β 0) ≠ 0 := by
      rw [Complex.coe_algebraMap]
      exact_mod_cast hβ0.ne'
    exact absurd hz hβ0ne
  · have hβ0ne : β 0 ≠ 0 := hβ0.ne'
    apply Part5.bound_realrooted (jensenPoly β n) n (β 0) hβ0
    intro z
    set J : Polynomial ℝ := jensenPoly β n with hJdef
    set q : ℕ → Polynomial ℝ := fun L => Part5.PsiD β (Part5.simpleApprox n L) with hqdef
    have hXnne : (Polynomial.X ^ n : Polynomial ℝ) ≠ 0 := by
      apply pow_ne_zero
      exact Polynomial.X_ne_zero
    have hJdeg : J.natDegree = n := by
      rw [hJdef, ← Part5.Jensen_form β n]
      rw [(Part5.PsiD_degree β hβ0ne (Polynomial.X ^ n) hXnne).1,
        Polynomial.natDegree_X_pow]
    have hL_facts : ∀ L : ℕ, 1 ≤ L →
        (q L ≠ 0 ∧ (q L).natDegree = n ∧ (q L).leadingCoeff = β 0 ∧
          β 0 * |z.im| ^ n ≤ ‖Polynomial.aeval z (q L)‖) := by
      intro L hL
      obtain ⟨hdegL, hlcL, rL, hrLmono, hrLroots⟩ :=
        Part5.coeff_convergence_zeros n hn L hL
      have hsAne : Part5.simpleApprox n L ≠ 0 := by
        intro hzero
        rw [hzero] at hlcL
        simp at hlcL
      obtain ⟨hqdegL, hqlcL⟩ := Part5.PsiD_degree β hβ0ne (Part5.simpleApprox n L) hsAne
      have hqdeg' : (q L).natDegree = n := by rw [hqdef]; rw [hqdegL, hdegL]
      have hqlc' : (q L).leadingCoeff = β 0 := by
        rw [hqdef]; rw [hqlcL, hlcL, mul_one]
      have hqne : q L ≠ 0 := by
        intro hzero
        rw [hzero, Polynomial.leadingCoeff_zero] at hqlc'
        exact hβ0ne hqlc'.symm
      have hrr : RealRooted (q L) := by
        rw [hqdef]
        exact Part5.simple_case h3 g hcont hint htp hne C c hC hc hbound β hrec hβ0
          (Part5.simpleApprox n L) n hn hdegL rL hrLmono hrLroots
      have hbd := Part5.realrooted_bound (q L) hqne hrr z
      rw [hqlc', hqdeg'] at hbd
      have hlcabs : |β 0| = β 0 := abs_of_pos hβ0
      rw [hlcabs] at hbd
      exact ⟨hqne, hqdeg', hqlc', hbd⟩
    have hcoeff : ∀ j : ℕ,
        Filter.Tendsto (fun L : ℕ => (q L).coeff j) Filter.atTop (nhds (J.coeff j)) := by
      intro j
      have hJcoeff : J.coeff j
          = ∑ m ∈ Finset.range (n + 1),
              ((j + m).choose m : ℝ) * β m * (Polynomial.X ^ n : Polynomial ℝ).coeff (j + m) := by
        rw [hJdef, ← Part5.Jensen_form β n, Part5.PsiD_coeff, Polynomial.natDegree_X_pow]
      rw [hJcoeff]
      have htarget :
          Filter.Tendsto
            (fun L : ℕ => ∑ m ∈ Finset.range (n + 1),
              ((j + m).choose m : ℝ) * β m * (Part5.simpleApprox n L).coeff (j + m))
            Filter.atTop
            (nhds (∑ m ∈ Finset.range (n + 1),
              ((j + m).choose m : ℝ) * β m * (Polynomial.X ^ n : Polynomial ℝ).coeff (j + m))) := by
        apply tendsto_finsetSum
        intro m _
        have := (Part5.coeff_convergence_limit n hn (j + m)).const_mul
          (((j + m).choose m : ℝ) * β m)
        simpa [mul_assoc] using this
      apply Filter.Tendsto.congr' _ htarget
      filter_upwards [Filter.eventually_ge_atTop 1] with L hL
      obtain ⟨hdegL, _, _⟩ := Part5.coeff_convergence_zeros n hn L hL
      rw [hqdef, Part5.PsiD_coeff, hdegL]
    have haeval :
        Filter.Tendsto (fun L : ℕ => Polynomial.aeval z (q L)) Filter.atTop
          (nhds (Polynomial.aeval z J)) := by
      have hJexp : Polynomial.aeval z J
          = ∑ i ∈ Finset.range (n + 1), (J.coeff i) • z ^ i := by
        rw [Polynomial.aeval_eq_sum_range' (n := n + 1) (by rw [hJdeg]; omega)]
      rw [hJexp]
      have htarget :
          Filter.Tendsto
            (fun L : ℕ => ∑ i ∈ Finset.range (n + 1), ((q L).coeff i) • z ^ i)
            Filter.atTop
            (nhds (∑ i ∈ Finset.range (n + 1), (J.coeff i) • z ^ i)) := by
        apply tendsto_finsetSum
        intro i _
        exact (hcoeff i).smul_const (z ^ i)
      apply Filter.Tendsto.congr' _ htarget
      filter_upwards [Filter.eventually_ge_atTop 1] with L hL
      obtain ⟨hqne, hqdegL, _, _⟩ := hL_facts L hL
      rw [Polynomial.aeval_eq_sum_range' (n := n + 1) (by rw [hqdegL]; omega)]
    have hnorm :
        Filter.Tendsto (fun L : ℕ => ‖Polynomial.aeval z (q L)‖) Filter.atTop
          (nhds ‖Polynomial.aeval z J‖) := haeval.norm
    apply ge_of_tendsto hnorm
    filter_upwards [Filter.eventually_ge_atTop 1] with L hL
    exact (hL_facts L hL).2.2.2
