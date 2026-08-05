import LeanCode.Vendor.E5.P6.Part6.Basic
import LeanCode.Vendor.E5.P6.Part6.PolyTools
import LeanCode.Vendor.E5.P6.Part6.Jensen
import LeanCode.Vendor.E5.Defs

open scoped BigOperators

namespace Part6








theorem normal_bound : ∀ (J : ℕ) (lam : ℕ → ℝ) (A M R : ℝ),
    0 ≤ A → 0 ≤ M → 0 < R →
    |∑ j ∈ Finset.range J, lam j| ≤ A →
    (∑ j ∈ Finset.range J, (lam j) ^ 2) ≤ M →
    ∀ z : ℂ, ‖z‖ ≤ R →
      ‖∏ j ∈ Finset.range J, (1 + (lam j : ℂ) * z)‖ ≤ Kbound A M R := by
  intro J lam A M R hA hM hR hsum hsumsq z hz
  classical
  set s := Finset.range J with hs
  set p : ℕ → Prop := fun j => 1/2 < R * |lam j| with hp
  set I := s.filter p with hI
  set Ic := s.filter (fun j => ¬ p j) with hIc
  have hRnn : (0:ℝ) ≤ R := le_of_lt hR
  have hznn : (0:ℝ) ≤ ‖z‖ := norm_nonneg z
  have hlamz : ∀ j, ‖(lam j : ℂ) * z‖ = |lam j| * ‖z‖ := by
    intro j
    rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hsub_le : ∀ (T : Finset ℕ), T ⊆ s → (∑ j ∈ T, (lam j) ^ 2) ≤ M := by
    intro T hT
    calc (∑ j ∈ T, (lam j) ^ 2)
        ≤ ∑ j ∈ s, (lam j) ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hT
          intro i _ _; positivity
      _ ≤ M := hsumsq
  have hfactor :
      ‖∏ j ∈ s, ((1 : ℂ) + (lam j : ℂ) * z)‖
        = (∏ j ∈ I, ‖(1 : ℂ) + (lam j : ℂ) * z‖)
          * (∏ j ∈ Ic, ‖(1 : ℂ) + (lam j : ℂ) * z‖) := by
    rw [Complex.norm_prod, hI, hIc]
    exact (Finset.prod_filter_mul_prod_filter_not s p
      (fun j => ‖(1 : ℂ) + (lam j : ℂ) * z‖)).symm
  have hI_sub : I ⊆ s := Finset.filter_subset _ _
  have hHead_terms : ∀ j ∈ I, |lam j| ≤ 2 * R * (lam j) ^ 2 := by
    intro j hj
    rw [hI, Finset.mem_filter] at hj
    have hpj : 1/2 < R * |lam j| := hj.2
    have habs : (0:ℝ) ≤ |lam j| := abs_nonneg _
    have h1 : 1 < 2 * R * |lam j| := by nlinarith [hpj]
    have : |lam j| * 1 ≤ |lam j| * (2 * R * |lam j|) :=
      mul_le_mul_of_nonneg_left (le_of_lt h1) habs
    have habssq : |lam j| * |lam j| = (lam j) ^ 2 := by
      rw [← abs_mul, ← sq, abs_sq]
    nlinarith [this, habssq]
  have hHead_sum : (∑ j ∈ I, |lam j|) ≤ 2 * R * M := by
    have hstep : (∑ j ∈ I, |lam j|) ≤ ∑ j ∈ I, 2 * R * (lam j) ^ 2 :=
      Finset.sum_le_sum hHead_terms
    have hfac : (∑ j ∈ I, 2 * R * (lam j) ^ 2) = 2 * R * ∑ j ∈ I, (lam j) ^ 2 := by
      rw [Finset.mul_sum]
    have hsq_le : (∑ j ∈ I, (lam j) ^ 2) ≤ M := hsub_le I hI_sub
    have : 2 * R * ∑ j ∈ I, (lam j) ^ 2 ≤ 2 * R * M := by
      apply mul_le_mul_of_nonneg_left hsq_le; positivity
    linarith [hstep, hfac ▸ hstep]
  have hHead_factor_le : ∀ j ∈ I,
      ‖(1 : ℂ) + (lam j : ℂ) * z‖ ≤ Real.exp (|lam j| * R) := by
    intro j hj
    have h1 : ‖(1 : ℂ) + (lam j : ℂ) * z‖ ≤ 1 + |lam j| * ‖z‖ := by
      calc ‖(1 : ℂ) + (lam j : ℂ) * z‖
          ≤ ‖(1 : ℂ)‖ + ‖(lam j : ℂ) * z‖ := norm_add_le _ _
        _ = 1 + |lam j| * ‖z‖ := by rw [norm_one, hlamz j]
    have h2 : (1:ℝ) + |lam j| * ‖z‖ ≤ 1 + |lam j| * R := by
      have : |lam j| * ‖z‖ ≤ |lam j| * R := mul_le_mul_of_nonneg_left hz (abs_nonneg _)
      linarith
    have h3 : (1:ℝ) + |lam j| * R ≤ Real.exp (|lam j| * R) := exp_lower _
    linarith
  have hHead : (∏ j ∈ I, ‖(1 : ℂ) + (lam j : ℂ) * z‖) ≤ Real.exp (2 * R ^ 2 * M) := by
    have hnn : ∀ j ∈ I, (0:ℝ) ≤ ‖(1 : ℂ) + (lam j : ℂ) * z‖ := fun j _ => norm_nonneg _
    calc (∏ j ∈ I, ‖(1 : ℂ) + (lam j : ℂ) * z‖)
        ≤ ∏ j ∈ I, Real.exp (|lam j| * R) := Finset.prod_le_prod hnn hHead_factor_le
      _ = Real.exp (∑ j ∈ I, |lam j| * R) := by rw [← Real.exp_sum]
      _ ≤ Real.exp (2 * R ^ 2 * M) := by
          apply Real.exp_le_exp.mpr
          have : (∑ j ∈ I, |lam j| * R) = (∑ j ∈ I, |lam j|) * R := by rw [Finset.sum_mul]
          rw [this]; nlinarith [hHead_sum, hRnn]
  have hIc_sub : Ic ⊆ s := Finset.filter_subset _ _
  have hTail_small : ∀ j ∈ Ic, ‖(lam j : ℂ) * z‖ ≤ 1/2 := by
    intro j hj
    rw [hIc, Finset.mem_filter] at hj
    have hle : R * |lam j| ≤ 1/2 := not_lt.mp hj.2
    rw [hlamz j]
    calc |lam j| * ‖z‖ ≤ |lam j| * R := mul_le_mul_of_nonneg_left hz (abs_nonneg _)
      _ = R * |lam j| := by ring
      _ ≤ 1/2 := hle
  have hTail_ne : ∀ j ∈ Ic, (1 : ℂ) + (lam j : ℂ) * z ≠ 0 := by
    intro j hj
    have hsm := hTail_small j hj
    have hpos : (0:ℝ) < ‖(1 : ℂ) + (lam j : ℂ) * z‖ := by
      have hrev : (1:ℝ) - ‖(lam j : ℂ) * z‖ ≤ ‖(1 : ℂ) + (lam j : ℂ) * z‖ := by
        calc (1:ℝ) - ‖(lam j : ℂ) * z‖ = ‖(1:ℂ)‖ - ‖-((lam j : ℂ) * z)‖ := by
                rw [norm_one, norm_neg]
          _ ≤ ‖(1:ℂ) - (-((lam j : ℂ) * z))‖ := norm_sub_norm_le _ _
          _ = ‖(1 : ℂ) + (lam j : ℂ) * z‖ := by rw [sub_neg_eq_add]
      linarith [hrev, hsm]
    exact fun h => by rw [h, norm_zero] at hpos; exact lt_irrefl 0 hpos
  have hTail_pos : ∀ j ∈ Ic, (0:ℝ) < ‖(1 : ℂ) + (lam j : ℂ) * z‖ := by
    intro j hj; rw [norm_pos_iff]; exact hTail_ne j hj
  have hTail_log : ∀ j ∈ Ic,
      Real.log ‖(1 : ℂ) + (lam j : ℂ) * z‖
        ≤ ((lam j : ℂ) * z).re + 2 * ‖(lam j : ℂ) * z‖ ^ 2 :=
    fun j hj => (log_abs ((lam j : ℂ) * z) (hTail_ne j hj)).2
  have hIc_lam_bound : |∑ j ∈ Ic, lam j| ≤ A + 2 * R * M := by
    have hsplit : (∑ j ∈ I, lam j) + (∑ j ∈ Ic, lam j) = ∑ j ∈ s, lam j := by
      rw [hI, hIc]; exact Finset.sum_filter_add_sum_filter_not s p lam
    have heq : (∑ j ∈ Ic, lam j) = (∑ j ∈ s, lam j) - (∑ j ∈ I, lam j) := by linarith [hsplit]
    rw [heq]
    have hI_abs : |∑ j ∈ I, lam j| ≤ 2 * R * M := by
      calc |∑ j ∈ I, lam j| ≤ ∑ j ∈ I, |lam j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ 2 * R * M := hHead_sum
    have htri : |(∑ j ∈ s, lam j) - (∑ j ∈ I, lam j)|
        ≤ |∑ j ∈ s, lam j| + |∑ j ∈ I, lam j| := by
      rcases abs_cases ((∑ j ∈ s, lam j) - (∑ j ∈ I, lam j)) with ⟨he, _⟩ | ⟨he, _⟩ <;>
        rw [he] <;>
        nlinarith [le_abs_self (∑ j ∈ s, lam j), neg_abs_le (∑ j ∈ s, lam j),
          le_abs_self (∑ j ∈ I, lam j), neg_abs_le (∑ j ∈ I, lam j)]
    linarith [htri, hsum, hI_abs]
  have hRe_bound : (∑ j ∈ Ic, ((lam j : ℂ) * z).re) ≤ (A + 2 * R * M) * R := by
    have hre_eq : ∀ j, ((lam j : ℂ) * z).re = lam j * z.re := fun j => by rw [Complex.re_ofReal_mul]
    have hsumre : (∑ j ∈ Ic, ((lam j : ℂ) * z).re) = (∑ j ∈ Ic, lam j) * z.re := by
      simp_rw [hre_eq]; rw [Finset.sum_mul]
    rw [hsumre]
    calc (∑ j ∈ Ic, lam j) * z.re
        ≤ |(∑ j ∈ Ic, lam j) * z.re| := le_abs_self _
      _ = |∑ j ∈ Ic, lam j| * |z.re| := by rw [abs_mul]
      _ ≤ |∑ j ∈ Ic, lam j| * ‖z‖ :=
          mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm z) (abs_nonneg _)
      _ ≤ |∑ j ∈ Ic, lam j| * R := mul_le_mul_of_nonneg_left hz (abs_nonneg _)
      _ ≤ (A + 2 * R * M) * R := mul_le_mul_of_nonneg_right hIc_lam_bound hRnn
  have hNormsq_bound : 2 * (∑ j ∈ Ic, ‖(lam j : ℂ) * z‖ ^ 2) ≤ 2 * R ^ 2 * M := by
    have hterm : ∀ j, ‖(lam j : ℂ) * z‖ ^ 2 = (lam j) ^ 2 * ‖z‖ ^ 2 := by
      intro j; rw [hlamz j, mul_pow, sq_abs]
    have hle_term : ∀ j ∈ Ic, ‖(lam j : ℂ) * z‖ ^ 2 ≤ (lam j) ^ 2 * R ^ 2 := by
      intro j _
      rw [hterm j]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact pow_le_pow_left₀ hznn hz 2
    have hsum_le : (∑ j ∈ Ic, ‖(lam j : ℂ) * z‖ ^ 2) ≤ ∑ j ∈ Ic, (lam j) ^ 2 * R ^ 2 :=
      Finset.sum_le_sum hle_term
    have hfac : (∑ j ∈ Ic, (lam j) ^ 2 * R ^ 2) = (∑ j ∈ Ic, (lam j) ^ 2) * R ^ 2 := by
      rw [Finset.sum_mul]
    have hsq_le : (∑ j ∈ Ic, (lam j) ^ 2) ≤ M := hsub_le Ic hIc_sub
    have hR2nn : (0:ℝ) ≤ R ^ 2 := sq_nonneg _
    nlinarith [hsum_le, hfac, hsq_le, hR2nn, mul_le_mul_of_nonneg_right hsq_le hR2nn]
  have hLogSum : (∑ j ∈ Ic, Real.log ‖(1 : ℂ) + (lam j : ℂ) * z‖)
      ≤ R * A + 4 * R ^ 2 * M := by
    have hstep : (∑ j ∈ Ic, Real.log ‖(1 : ℂ) + (lam j : ℂ) * z‖)
        ≤ ∑ j ∈ Ic, (((lam j : ℂ) * z).re + 2 * ‖(lam j : ℂ) * z‖ ^ 2) :=
      Finset.sum_le_sum hTail_log
    have hsplit_sum : (∑ j ∈ Ic, (((lam j : ℂ) * z).re + 2 * ‖(lam j : ℂ) * z‖ ^ 2))
        = (∑ j ∈ Ic, ((lam j : ℂ) * z).re) + 2 * (∑ j ∈ Ic, ‖(lam j : ℂ) * z‖ ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    rw [hsplit_sum] at hstep
    nlinarith [hstep, hRe_bound, hNormsq_bound, hRnn, hM, hA]
  have hTail : (∏ j ∈ Ic, ‖(1 : ℂ) + (lam j : ℂ) * z‖) ≤ Real.exp (R * A + 4 * R ^ 2 * M) := by
    have hprod_eq : (∏ j ∈ Ic, ‖(1 : ℂ) + (lam j : ℂ) * z‖)
        = Real.exp (∑ j ∈ Ic, Real.log ‖(1 : ℂ) + (lam j : ℂ) * z‖) := by
      rw [Real.exp_sum]
      exact (Finset.prod_congr rfl (fun j hj => (Real.exp_log (hTail_pos j hj)).symm))
    rw [hprod_eq]; exact Real.exp_le_exp.mpr hLogSum
  have hTailnn : (0:ℝ) ≤ ∏ j ∈ Ic, ‖(1 : ℂ) + (lam j : ℂ) * z‖ :=
    Finset.prod_nonneg (fun j _ => norm_nonneg _)
  rw [hfactor]
  calc (∏ j ∈ I, ‖(1 : ℂ) + (lam j : ℂ) * z‖) * (∏ j ∈ Ic, ‖(1 : ℂ) + (lam j : ℂ) * z‖)
      ≤ Real.exp (2 * R ^ 2 * M) * Real.exp (R * A + 4 * R ^ 2 * M) :=
        mul_le_mul hHead hTail hTailnn (Real.exp_pos _).le
    _ = Real.exp (R * A + 6 * R ^ 2 * M) := by rw [← Real.exp_add]; ring_nf
    _ = Kbound A M R := by rw [Kbound]



theorem Pn_bounded : ∀ (β : ℕ → ℝ), HypH β → ∀ (n : ℕ), 1 ≤ n →
    ∀ (R : ℝ), 0 < R → ∀ z : ℂ, ‖z‖ ≤ R →
      ‖Pn β n z‖ ≤ Kbound (|delta β|) (Mconst β) R := by
  intro β hβ n hn R hR z hz
  obtain ⟨Λ, hΛ⟩ := Lambda_family β hβ
  obtain ⟨_, _, hprod⟩ := hΛ n hn
  rw [hprod n (le_refl n) z]
  have hsym := symmetric β hβ n hn n (Λ n) (fun z => (hprod n (le_refl n) z).symm)
  have hM0 : (0 : ℝ) ≤ Mconst β := by
    rw [Mconst]; exact add_nonneg (sq_nonneg _) (div_nonneg (abs_nonneg _) hβ.1.le)
  have hA : |∑ j ∈ Finset.range n, Λ n j| ≤ |delta β| := le_of_eq (by rw [hsym.1])
  exact normal_bound n (Λ n) (|delta β|) (Mconst β) R (abs_nonneg _) hM0 hR hA hsym.2.2.2.2 z hz






theorem coeff_convergence : ∀ (c : ℕ → ℕ → ℂ) (d : ℕ → ℕ) (climit : ℕ → ℂ) (C : ℝ → ℝ),
    (∀ n m : ℕ, d n < m → c n m = 0) →
    (∀ ρ : ℝ, 0 < ρ → ∀ n : ℕ, ∀ z : ℂ, ‖z‖ = ρ →
        ‖∑ j ∈ Finset.range (d n + 1), c n j * z ^ j‖ ≤ C ρ) →
    (∀ m : ℕ, Filter.Tendsto (fun n => c n m) Filter.atTop (nhds (climit m))) →
    (∀ z : ℂ, Summable (fun m => climit m * z ^ m)) ∧
    (∀ z : ℂ, Filter.Tendsto (fun n => ∑ j ∈ Finset.range (d n + 1), c n j * z ^ j)
        Filter.atTop (nhds (∑' m, climit m * z ^ m))) := by
  intro c d climit C hzero hcirc hlim
  have hcb : ∀ ρ : ℝ, 0 < ρ → ∀ n m : ℕ, ‖c n m‖ ≤ C ρ * ρ ^ (-(m : ℤ)) := by
    intro ρ hρ n m
    exact coeff_bound (d n) (c n) ρ (C ρ) hρ (hzero n) (fun z hz => hcirc ρ hρ n z hz) m
  have hCnn : ∀ ρ : ℝ, 0 < ρ → 0 ≤ C ρ := by
    intro ρ hρ
    have hz : ‖((ρ : ℂ))‖ = ρ := by simp [Complex.norm_real, abs_of_pos hρ]
    calc (0 : ℝ) ≤ ‖∑ j ∈ Finset.range (d 0 + 1), c 0 j * (ρ : ℂ) ^ j‖ := norm_nonneg _
      _ ≤ C ρ := hcirc ρ hρ 0 (ρ : ℂ) hz
  have hlb : ∀ ρ : ℝ, 0 < ρ → ∀ m : ℕ, ‖climit m‖ ≤ C ρ * ρ ^ (-(m : ℤ)) := by
    intro ρ hρ m
    have htend : Filter.Tendsto (fun n => ‖c n m‖) Filter.atTop (nhds ‖climit m‖) :=
      (hlim m).norm
    refine le_of_tendsto htend ?_
    exact Filter.Eventually.of_forall (fun n => hcb ρ hρ n m)
  have hsummable : ∀ z : ℂ, Summable (fun m => climit m * z ^ m) := by
    intro z
    set ρ : ℝ := 2 * ‖z‖ + 1 with hρdef
    have hρpos : 0 < ρ := by
      have : 0 ≤ ‖z‖ := norm_nonneg z
      simp only [hρdef]; positivity
    have hzρnn : 0 ≤ ‖z‖ / ρ := by positivity
    have hzρlt : ‖z‖ / ρ < 1 := by
      rw [div_lt_one hρpos]; simp only [hρdef]; nlinarith [norm_nonneg z]
    have hgeom : Summable (fun m : ℕ => C ρ * (‖z‖ / ρ) ^ m) :=
      (summable_geometric_of_lt_one hzρnn hzρlt).mul_left (C ρ)
    refine Summable.of_norm ?_
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hgeom
    have hkey : ‖climit m * z ^ m‖ = ‖climit m‖ * ‖z‖ ^ m := by rw [norm_mul, norm_pow]
    rw [hkey]
    have hstep : ‖climit m‖ * ‖z‖ ^ m ≤ (C ρ * ρ ^ (-(m : ℤ))) * ‖z‖ ^ m := by
      apply mul_le_mul_of_nonneg_right (hlb ρ hρpos m); positivity
    refine le_trans hstep (le_of_eq ?_)
    have hconv : ρ ^ (-(m : ℤ)) * ‖z‖ ^ m = (‖z‖ / ρ) ^ m := by
      rw [zpow_neg, zpow_natCast, div_pow, div_eq_mul_inv, mul_comm]
    rw [mul_assoc, hconv]
  refine ⟨hsummable, ?_⟩
  intro z
  set P : ℂ := ∑' m, climit m * z ^ m with hPdef
  set ρ : ℝ := 2 * ‖z‖ + 1 with hρdef
  have hρpos : 0 < ρ := by simp only [hρdef]; positivity
  set r : ℝ := ‖z‖ / ρ with hrdef
  have hrnn : 0 ≤ r := by simp only [hrdef]; positivity
  have hrhalf : r ≤ 1 / 2 := by
    simp only [hrdef]; rw [div_le_iff₀ hρpos]; simp only [hρdef]; nlinarith [norm_nonneg z]
  have hrlt : r < 1 := lt_of_le_of_lt hrhalf (by norm_num)
  have hCnn' : 0 ≤ C ρ := hCnn ρ hρpos
  have hconv : ∀ m : ℕ, ρ ^ (-(m : ℤ)) * ‖z‖ ^ m = r ^ m := by
    intro m; simp only [hrdef]
    rw [zpow_neg, zpow_natCast, div_pow, div_eq_mul_inv, mul_comm]
  have hpn : ∀ n : ℕ, ∑' j, c n j * z ^ j = ∑ j ∈ Finset.range (d n + 1), c n j * z ^ j := by
    intro n
    apply tsum_eq_sum
    intro b hb
    rw [Finset.mem_range, not_lt] at hb
    rw [hzero n b (by omega), zero_mul]
  have hsummc : ∀ n : ℕ, Summable (fun j => c n j * z ^ j) := by
    intro n
    apply summable_of_ne_finset_zero (s := Finset.range (d n + 1))
    intro b hb
    rw [Finset.mem_range, not_lt] at hb
    rw [hzero n b (by omega), zero_mul]
  set g : ℕ → ℕ → ℝ := fun n m => ‖(c n m - climit m) * z ^ m‖ with hgdef
  have hgb : ∀ n m : ℕ, g n m ≤ 2 * C ρ * r ^ m := by
    intro n m
    simp only [hgdef]
    rw [norm_mul, norm_pow]
    have hcm : ‖c n m - climit m‖ ≤ 2 * (C ρ * ρ ^ (-(m : ℤ))) := by
      calc ‖c n m - climit m‖ ≤ ‖c n m‖ + ‖climit m‖ := norm_sub_le _ _
        _ ≤ C ρ * ρ ^ (-(m : ℤ)) + C ρ * ρ ^ (-(m : ℤ)) :=
            add_le_add (hcb ρ hρpos n m) (hlb ρ hρpos m)
        _ = 2 * (C ρ * ρ ^ (-(m : ℤ))) := by ring
    calc ‖c n m - climit m‖ * ‖z‖ ^ m
        ≤ (2 * (C ρ * ρ ^ (-(m : ℤ)))) * ‖z‖ ^ m :=
          mul_le_mul_of_nonneg_right hcm (by positivity)
      _ = 2 * C ρ * (ρ ^ (-(m : ℤ)) * ‖z‖ ^ m) := by ring
      _ = 2 * C ρ * r ^ m := by rw [hconv]
  have hgeomr : Summable (fun m : ℕ => 2 * C ρ * r ^ m) :=
    (summable_geometric_of_lt_one hrnn hrlt).mul_left (2 * C ρ)
  have hgsum : ∀ n : ℕ, Summable (g n) := by
    intro n
    apply Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => hgb n m) hgeomr
  have htailgeom : ∀ M : ℕ, ∑' i : ℕ, r ^ (i + M) ≤ 2 * (1 / 2 : ℝ) ^ M := by
    intro M
    have h1 : ∑' i : ℕ, r ^ (i + M) = r ^ M * (1 - r)⁻¹ := by
      simp_rw [pow_add]
      rw [tsum_mul_right, tsum_geometric_of_lt_one hrnn hrlt, mul_comm]
    rw [h1]
    have hrM : r ^ M ≤ (1 / 2 : ℝ) ^ M := pow_le_pow_left₀ hrnn hrhalf M
    have hinv : (1 - r)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have hhalfMnn : 0 ≤ (1 / 2 : ℝ) ^ M := by positivity
    calc r ^ M * (1 - r)⁻¹ ≤ (1 / 2 : ℝ) ^ M * (1 - r)⁻¹ :=
          mul_le_mul_of_nonneg_right hrM (by positivity)
      _ ≤ (1 / 2 : ℝ) ^ M * 2 := mul_le_mul_of_nonneg_left hinv hhalfMnn
      _ = 2 * (1 / 2 : ℝ) ^ M := by ring
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hchoose : ∃ M₀ : ℕ, (2 * C ρ) * (2 * (1 / 2 : ℝ) ^ M₀) < ε / 2 := by
    have htend : Filter.Tendsto (fun n : ℕ => (2 * C ρ) * (2 * (1 / 2 : ℝ) ^ n))
        Filter.atTop (nhds ((2 * C ρ) * (2 * 0))) := by
      apply Filter.Tendsto.const_mul
      apply Filter.Tendsto.const_mul
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    rw [mul_zero, mul_zero] at htend
    rw [Metric.tendsto_atTop] at htend
    obtain ⟨N, hN⟩ := htend (ε / 2) (by linarith)
    refine ⟨N, ?_⟩
    have := hN N (le_refl N)
    rw [Real.dist_eq, sub_zero] at this
    have hpos : 0 ≤ (2 * C ρ) * (2 * (1 / 2 : ℝ) ^ N) := by positivity
    rw [abs_of_nonneg hpos] at this
    exact this
  obtain ⟨M₀, hM₀⟩ := hchoose
  have htailbound : ∀ n : ℕ, ∑' i : ℕ, g n (i + M₀) < ε / 2 := by
    intro n
    have hsumtail : Summable (fun i => g n (i + M₀)) :=
      (summable_nat_add_iff M₀).2 (hgsum n)
    have hle : ∑' i : ℕ, g n (i + M₀) ≤ ∑' i : ℕ, (2 * C ρ) * r ^ (i + M₀) :=
      hsumtail.tsum_mono ((summable_nat_add_iff M₀).2 hgeomr) (fun i => hgb n (i + M₀))
    have heq : ∑' i : ℕ, (2 * C ρ) * r ^ (i + M₀) = (2 * C ρ) * ∑' i : ℕ, r ^ (i + M₀) := by
      rw [tsum_mul_left]
    rw [heq] at hle
    have : (2 * C ρ) * ∑' i : ℕ, r ^ (i + M₀) ≤ (2 * C ρ) * (2 * (1 / 2 : ℝ) ^ M₀) :=
      mul_le_mul_of_nonneg_left (htailgeom M₀) (by positivity)
    linarith
  have hhead : Filter.Tendsto (fun n => ∑ m ∈ Finset.range M₀, g n m)
      Filter.atTop (nhds 0) := by
    have : Filter.Tendsto (fun n => ∑ m ∈ Finset.range M₀, g n m)
        Filter.atTop (nhds (∑ m ∈ Finset.range M₀, (0 : ℝ))) := by
      apply tendsto_finsetSum
      intro m _
      have hcz : Filter.Tendsto (fun n => (c n m - climit m) * z ^ m)
          Filter.atTop (nhds ((climit m - climit m) * z ^ m)) := by
        apply Filter.Tendsto.mul_const
        apply Filter.Tendsto.sub_const
        exact hlim m
      simp only [sub_self, zero_mul] at hcz
      have := hcz.norm
      simpa only [hgdef, norm_zero] using this
    simpa using this
  rw [Metric.tendsto_atTop] at hhead
  obtain ⟨N, hN⟩ := hhead (ε / 2) (by linarith)
  refine ⟨N, ?_⟩
  intro n hn
  have hheadn : ∑ m ∈ Finset.range M₀, g n m < ε / 2 := by
    have := hN n hn
    rw [Real.dist_eq, sub_zero] at this
    have hnn : 0 ≤ ∑ m ∈ Finset.range M₀, g n m :=
      Finset.sum_nonneg (fun m _ => norm_nonneg _)
    rw [abs_of_nonneg hnn] at this
    exact this
  rw [Complex.dist_eq]
  have hdiff : (∑ j ∈ Finset.range (d n + 1), c n j * z ^ j) - P
      = ∑' m, (c n m - climit m) * z ^ m := by
    rw [← hpn n, hPdef, ← (hsummc n).tsum_sub (hsummable z)]
    exact tsum_congr (fun m => (sub_mul _ _ _).symm)
  rw [hdiff]
  have hnorm_le : ‖∑' m, (c n m - climit m) * z ^ m‖ ≤ ∑' m, g n m := by
    have := norm_tsum_le_tsum_norm (f := fun m => (c n m - climit m) * z ^ m) (hgsum n)
    simpa only [hgdef] using this
  have hsplit : ∑' m, g n m
      = (∑ m ∈ Finset.range M₀, g n m) + ∑' i, g n (i + M₀) :=
    ((hgsum n).sum_add_tsum_nat_add M₀).symm
  calc ‖∑' m, (c n m - climit m) * z ^ m‖
      ≤ ∑' m, g n m := hnorm_le
    _ = (∑ m ∈ Finset.range M₀, g n m) + ∑' i, g n (i + M₀) := hsplit
    _ < ε / 2 + ε / 2 := add_lt_add hheadn (htailbound n)
    _ = ε := by ring


theorem coeff_limit : ∀ (m : ℕ),
    Filter.Tendsto (fun n : ℕ => (n.choose m : ℝ) / (n : ℝ) ^ m)
        Filter.atTop (nhds (1 / (m.factorial : ℝ))) := by
  intro m
  have hprod : Filter.Tendsto
      (fun n : ℕ => ∏ ℓ ∈ Finset.range m, (1 - (ℓ : ℝ) / (n : ℝ)))
      Filter.atTop (nhds (∏ ℓ ∈ Finset.range m, (1 : ℝ))) := by
    apply tendsto_finsetProd
    intro ℓ _
    have h0 : Filter.Tendsto (fun n : ℕ => (ℓ : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (ℓ : ℝ)
    have := (tendsto_const_nhds (x := (1 : ℝ)) (f := Filter.atTop (α := ℕ))).sub h0
    simpa using this
  rw [Finset.prod_const_one] at hprod
  have hlim : Filter.Tendsto
      (fun n : ℕ => (∏ ℓ ∈ Finset.range m, (1 - (ℓ : ℝ) / (n : ℝ))) / (m.factorial : ℝ))
      Filter.atTop (nhds (1 / (m.factorial : ℝ))) :=
    hprod.div_const _
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop m] with n hn
  have hdesc : (n.descFactorial m : ℝ) = ∏ ℓ ∈ Finset.range m, ((n : ℝ) - (ℓ : ℝ)) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    refine Finset.prod_congr rfl (fun ℓ hℓ => ?_)
    have : ℓ ≤ n := le_trans (le_of_lt (Finset.mem_range.mp hℓ)) hn
    rw [Nat.cast_sub this]
  have hchoose : (n.choose m : ℝ)
      = (∏ ℓ ∈ Finset.range m, ((n : ℝ) - (ℓ : ℝ))) / (m.factorial : ℝ) := by
    have hkey : (n.descFactorial m : ℝ) = (m.factorial : ℝ) * (n.choose m : ℝ) := by
      rw [← Nat.cast_mul, Nat.descFactorial_eq_factorial_mul_choose]
    rw [hdesc] at hkey
    field_simp
    linarith [hkey]
  show (∏ ℓ ∈ Finset.range m, (1 - (ℓ : ℝ) / (n : ℝ))) / (m.factorial : ℝ)
      = (n.choose m : ℝ) / (n : ℝ) ^ m
  rw [hchoose]
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0; simp
  · have hnpos : 0 < n := lt_of_lt_of_le hmpos hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hnpos.ne'
    have hprodeq : (∏ ℓ ∈ Finset.range m, (1 - (ℓ : ℝ) / (n : ℝ)))
        = (∏ ℓ ∈ Finset.range m, ((n : ℝ) - (ℓ : ℝ))) / (n : ℝ) ^ m := by
      have hpow : (n : ℝ) ^ m = ∏ _ℓ ∈ Finset.range m, (n : ℝ) := by
        rw [Finset.prod_const, Finset.card_range]
      rw [hpow, ← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl (fun ℓ _ => ?_)
      field_simp
    rw [hprodeq]
    field_simp




theorem Pn_converges : ∀ (β : ℕ → ℝ), HypH β →
    (∀ ρ : ℝ, 0 < ρ → ∀ m : ℕ,
        |β m / (β 0 * (m.factorial : ℝ))| ≤ Kbound (|delta β|) (Mconst β) ρ * ρ ^ (-(m : ℤ))) ∧
    (∀ z : ℂ, Summable (fun m => ((β m / (β 0 * (m.factorial : ℝ)) : ℝ) : ℂ) * z ^ m)) ∧
    (∀ z : ℂ, Filter.Tendsto (fun n => Pn β n z) Filter.atTop
        (nhds (∑' m, ((β m / (β 0 * (m.factorial : ℝ)) : ℝ) : ℂ) * z ^ m))) := by
  intro β hβ
  obtain ⟨hβ0, hrr⟩ := hβ
  have hβ0' : HypH β := ⟨hβ0, hrr⟩
  have hβ0ne : β 0 ≠ 0 := hβ0.ne'
  set cc : ℕ → ℕ → ℂ := fun n m => ((β m / β 0 * (n.choose m : ℝ) / (n : ℝ) ^ m : ℝ) : ℂ) with hcc
  set cl : ℕ → ℂ := fun m => ((β m / (β 0 * (m.factorial : ℝ)) : ℝ) : ℂ) with hcl
  set Cf : ℝ → ℝ := fun ρ => Kbound (|delta β|) (Mconst β) ρ with hCf
  set dd : ℕ → ℕ := fun n => n with hdd
  have hzero : ∀ n m : ℕ, dd n < m → cc n m = 0 := by
    intro n m hnm
    have : n.choose m = 0 := Nat.choose_eq_zero_of_lt hnm
    simp only [hcc, this, Nat.cast_zero, mul_zero, zero_div, Complex.ofReal_zero]
  have hMnn : 0 ≤ Mconst β := by
    rw [Mconst]
    exact add_nonneg (sq_nonneg _) (div_nonneg (abs_nonneg _) hβ0.le)
  have hCf1 : ∀ ρ : ℝ, 0 < ρ → 1 ≤ Cf ρ := by
    intro ρ hρ
    simp only [hCf, Kbound]
    rw [Real.one_le_exp_iff]
    have h1 : 0 ≤ ρ * |delta β| := mul_nonneg hρ.le (abs_nonneg _)
    have h2 : 0 ≤ 6 * ρ ^ 2 * Mconst β :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hMnn
    linarith
  have hcirc : ∀ ρ : ℝ, 0 < ρ → ∀ n : ℕ, ∀ z : ℂ, ‖z‖ = ρ →
      ‖∑ j ∈ Finset.range (dd n + 1), cc n j * z ^ j‖ ≤ Cf ρ := by
    intro ρ hρ n z hz
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      have hsum : (∑ j ∈ Finset.range (dd 0 + 1), cc 0 j * z ^ j) = 1 := by
        simp only [hdd]
        rw [Finset.sum_range_one, hcc]
        simp only [pow_zero, mul_one, Nat.choose_self, Nat.cast_one]
        rw [div_self hβ0ne, div_one, Complex.ofReal_one]
      rw [hsum, norm_one]
      exact hCf1 ρ hρ
    · have hn : 1 ≤ n := hnpos
      have heq : (∑ j ∈ Finset.range (dd n + 1), cc n j * z ^ j) = Pn β n z := by
        rw [(Pn_basic β hβ0' n hn).1 z]
      rw [heq, hCf]
      exact Pn_bounded β hβ0' n hn ρ hρ z (le_of_eq hz)
  have hlim : ∀ m : ℕ, Filter.Tendsto (fun n => cc n m) Filter.atTop (nhds (cl m)) := by
    intro m
    have hcceq : (fun n => cc n m)
        = (fun n : ℕ => ((β m / β 0 : ℝ) : ℂ) * (((n.choose m : ℝ) / (n : ℝ) ^ m : ℝ) : ℂ)) := by
      funext n
      simp only [hcc]
      rw [← Complex.ofReal_mul]
      congr 1
      rw [mul_div_assoc]
    have hR : Filter.Tendsto (fun n : ℕ => (n.choose m : ℝ) / (n : ℝ) ^ m)
        Filter.atTop (nhds (1 / (m.factorial : ℝ))) := coeff_limit m
    have hRc : Filter.Tendsto (fun n : ℕ => (((n.choose m : ℝ) / (n : ℝ) ^ m : ℝ) : ℂ))
        Filter.atTop (nhds (((1 / (m.factorial : ℝ) : ℝ) : ℂ))) :=
      (Complex.continuous_ofReal.tendsto _).comp hR
    have hmul : Filter.Tendsto
        (fun n : ℕ => ((β m / β 0 : ℝ) : ℂ) * (((n.choose m : ℝ) / (n : ℝ) ^ m : ℝ) : ℂ))
        Filter.atTop (nhds (((β m / β 0 : ℝ) : ℂ) * ((1 / (m.factorial : ℝ) : ℝ) : ℂ))) :=
      hRc.const_mul _
    rw [hcceq]
    have hcleq : cl m = ((β m / β 0 : ℝ) : ℂ) * ((1 / (m.factorial : ℝ) : ℝ) : ℂ) := by
      rw [hcl, ← Complex.ofReal_mul]
      apply Complex.ofReal_inj.mpr
      rw [mul_one_div, div_div]
    rw [hcleq]
    exact hmul
  obtain ⟨hSummable, hTendsto⟩ := coeff_convergence cc dd cl Cf hzero hcirc hlim
  refine ⟨?_, ?_, ?_⟩
  · intro ρ hρ m
    have hcb : ∀ n : ℕ, ‖cc n m‖ ≤ Cf ρ * ρ ^ (-(m : ℤ)) := by
      intro n
      exact coeff_bound (dd n) (cc n) ρ (Cf ρ) hρ (hzero n)
        (fun z hz => hcirc ρ hρ n z hz) m
    have hnorm : Filter.Tendsto (fun n => ‖cc n m‖) Filter.atTop (nhds (‖cl m‖)) :=
      (hlim m).norm
    have hle : ‖cl m‖ ≤ Cf ρ * ρ ^ (-(m : ℤ)) :=
      le_of_tendsto hnorm (Filter.Eventually.of_forall hcb)
    have hclnorm : ‖cl m‖ = |β m / (β 0 * (m.factorial : ℝ))| := by
      rw [hcl, Complex.norm_real, Real.norm_eq_abs]
    rw [← hclnorm]
    exact hle
  · intro z
    have := hSummable z
    simp only [hcl] at this
    exact this
  · intro z
    have hT := hTendsto z
    have htsum : (∑' m, cl m * z ^ m)
        = ∑' m, ((β m / (β 0 * (m.factorial : ℝ)) : ℝ) : ℂ) * z ^ m := by rw [hcl]
    rw [htsum] at hT
    refine hT.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact ((Pn_basic β hβ0' n hn).1 z).symm








theorem monotone_subseq : ∀ (x : ℕ → ℝ),
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ (Monotone (x ∘ σ) ∨ Antitone (x ∘ σ)) := by
  intro x
  obtain ⟨g, hinc | hnoninc⟩ := exists_increasing_or_nonincreasing_subseq (· < ·) x
  · refine ⟨g, g.strictMono, Or.inl ?_⟩
    intro m n hmn
    rcases eq_or_lt_of_le hmn with rfl | hlt
    · exact le_refl _
    · exact (hinc m n hlt).le
  · refine ⟨g, g.strictMono, Or.inr ?_⟩
    intro m n hmn
    rcases eq_or_lt_of_le hmn with rfl | hlt
    · exact le_refl _
    · exact not_lt.mp (hnoninc m n hlt)



theorem monotone_conv :
    (∀ (y : ℕ → ℝ) (C : ℝ), Monotone y → (∀ k, y k ≤ C) →
        Filter.Tendsto y Filter.atTop (nhds (⨆ k, y k)) ∧
        (∀ k, y k ≤ ⨆ k, y k) ∧ (⨆ k, y k) ≤ C) ∧
    (∀ (y : ℕ → ℝ) (c : ℝ), Antitone y → (∀ k, c ≤ y k) →
        Filter.Tendsto y Filter.atTop (nhds (⨅ k, y k)) ∧
        (∀ k, (⨅ k, y k) ≤ y k) ∧ c ≤ (⨅ k, y k)) := by
  refine ⟨?_, ?_⟩
  · intro y C hmono hbd
    have hbdd : BddAbove (Set.range y) := ⟨C, by rintro _ ⟨k, rfl⟩; exact hbd k⟩
    exact ⟨tendsto_atTop_ciSup hmono hbdd, fun k => le_ciSup hbdd k, ciSup_le hbd⟩
  · intro y c hanti hbd
    have hbdd : BddBelow (Set.range y) := ⟨c, by rintro _ ⟨k, rfl⟩; exact hbd k⟩
    exact ⟨tendsto_atTop_ciInf hanti hbdd, fun k => ciInf_le hbdd k, le_ciInf hbd⟩



theorem bolzano_weierstrass : ∀ (x : ℕ → ℝ) (C : ℝ), 0 ≤ C → (∀ n, |x n| ≤ C) →
    ∃ (σ : ℕ → ℕ) (xstar : ℝ), StrictMono σ ∧ xstar ∈ Set.Icc (-C) C ∧
      Filter.Tendsto (x ∘ σ) Filter.atTop (nhds xstar) := by
  intro x C _ hbd
  have hmem : ∀ n, x n ∈ Set.Icc (-C) C := fun n => Set.mem_Icc.mpr (abs_le.mp (hbd n))
  obtain ⟨a, ha, φ, hφ, htend⟩ :=
    tendsto_subseq_of_bounded (Metric.isBounded_Icc (-C) C) hmem
  exact ⟨φ, a, hφ, by rwa [closure_Icc] at ha, htend⟩




theorem subseq_facts :
    (∀ σ : ℕ → ℕ, StrictMono σ → ∀ k, k ≤ σ k) ∧
    (∀ (σ : ℕ → ℕ), StrictMono σ → ∀ (x : ℕ → ℂ) (L : ℂ),
        Filter.Tendsto x Filter.atTop (nhds L) →
        Filter.Tendsto (x ∘ σ) Filter.atTop (nhds L)) ∧
    (∀ σ τ : ℕ → ℕ, StrictMono σ → StrictMono τ → StrictMono (σ ∘ τ)) :=
  ⟨fun _ hσ _ => hσ.le_apply,
   fun _ hσ _ _ hx => hx.comp hσ.tendsto_atTop,
   fun _ _ hσ hτ => hσ.comp hτ⟩




theorem diagonal : ∀ (lam : ℕ → ℕ → ℝ) (M : ℝ), 0 ≤ M →
    (∀ n J : ℕ, ∑ i ∈ Finset.range J, (lam n i) ^ 2 ≤ M) →
    ∃ (φ : ℕ → ℕ) (α : ℕ → ℝ), StrictMono φ ∧
      ∀ j : ℕ, Filter.Tendsto (fun k => lam (φ k) j) Filter.atTop (nhds (α j)) := by
  intro lam M hM hbound
  have hmem : ∀ n j : ℕ, lam n j ∈ Set.Icc (-Real.sqrt M) (Real.sqrt M) := by
    intro n j
    have hsq : (lam n j) ^ 2 ≤ M := by
      calc (lam n j) ^ 2
          ≤ ∑ i ∈ Finset.range (j + 1), (lam n i) ^ 2 := by
            apply Finset.single_le_sum (f := fun i => (lam n i) ^ 2)
            · intro i _; exact sq_nonneg _
            · exact Finset.mem_range.mpr (Nat.lt_succ_self j)
        _ ≤ M := hbound n (j + 1)
    have habs : |lam n j| ≤ Real.sqrt M := by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hsq
    rw [Set.mem_Icc]; exact abs_le.mp habs
  set S : Set (ℕ → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-Real.sqrt M) (Real.sqrt M)) with hS_def
  have hS : IsCompact S := isCompact_univ_pi (fun _ => isCompact_Icc)
  set u : ℕ → (ℕ → ℝ) := fun n => fun j => lam n j with hu_def
  have hu : ∀ n, u n ∈ S := by
    intro n; rw [hS_def, Set.mem_univ_pi]; intro j; exact hmem n j
  obtain ⟨a, _ha_mem, φ, hφ_mono, hφ_tendsto⟩ := hS.tendsto_subseq hu
  exact ⟨φ, a, hφ_mono, fun j => (tendsto_pi_nhds.mp hφ_tendsto) j⟩





theorem alpha_family : ∀ (β : ℕ → ℝ), HypH β → ∀ (Λ : ℕ → ℕ → ℝ), IsLambdaFamily β Λ →
    ∃ (φ : ℕ → ℕ) (α : ℕ → ℝ) (γ : ℝ), StrictMono φ ∧
      (∀ j : ℕ, Filter.Tendsto (fun k => Λ (φ k) j) Filter.atTop (nhds (α j))) ∧
      (∀ j : ℕ, |α j| ≤ Real.sqrt (Mconst β / ((j : ℝ) + 1))) ∧
      (∀ N : ℕ, ∑ j ∈ Finset.range N, (α j) ^ 2 ≤ Bconst β) ∧
      Summable (fun j => (α j) ^ 2) ∧
      (∑' j, (α j) ^ 2 ≤ Bconst β) ∧
      0 ≤ γ ∧ Bconst β = 2 * γ + ∑' j, (α j) ^ 2 := by
  intro β hβ Λ hΛ
  have hM0 : 0 ≤ Mconst β := by
    rw [Mconst]; exact add_nonneg (sq_nonneg _) (div_nonneg (abs_nonneg _) hβ.1.le)
  have hdiag : ∀ n J : ℕ, ∑ i ∈ Finset.range J, (Λ (n+1) i) ^ 2 ≤ Mconst β := by
    intro n J
    exact (lambda_decay β hβ Λ hΛ (n+1) (by omega)).1 J
  obtain ⟨φ₀, α, hφ₀mono, hconv0⟩ := diagonal (fun n j => Λ (n+1) j) (Mconst β) hM0 hdiag
  set φ : ℕ → ℕ := fun k => φ₀ k + 1 with hφdef
  have hφmono : StrictMono φ := by
    intro a b h
    simp only [hφdef]
    exact Nat.add_lt_add_right (hφ₀mono h) 1
  have hφ1 : ∀ k, 1 ≤ φ k := by intro k; simp only [hφdef]; omega
  have hprop1 : ∀ j : ℕ, Filter.Tendsto (fun k => Λ (φ k) j) Filter.atTop (nhds (α j)) := hconv0
  have hprop2 : ∀ j : ℕ, |α j| ≤ Real.sqrt (Mconst β / ((j : ℝ) + 1)) := by
    intro j
    have habs : Filter.Tendsto (fun k => |Λ (φ k) j|) Filter.atTop (nhds (|α j|)) :=
      (hprop1 j).abs
    apply le_of_tendsto' habs
    intro k
    exact (lambda_decay β hβ Λ hΛ (φ k) (hφ1 k)).2 j
  have hφtop : Filter.Tendsto φ Filter.atTop Filter.atTop := hφmono.tendsto_atTop
  have hΛprod : ∀ k J : ℕ, φ k ≤ J → ∀ z : ℂ,
      (∏ j ∈ Finset.range J, (1 + (Λ (φ k) j : ℂ) * z)) = Pn β (φ k) z := by
    intro k J hJ z
    exact ((hΛ (φ k) (hφ1 k)).2.2 J hJ z).symm
  have hprop3 : ∀ N : ℕ, ∑ j ∈ Finset.range N, (α j) ^ 2 ≤ Bconst β := by
    intro N
    have hbound : ∀ k, ∑ j ∈ Finset.range N, (Λ (φ k) j) ^ 2
        ≤ (delta β) ^ 2 - ((φ k : ℝ) - 1) / (φ k) * (β 2 / β 0) := by
      intro k
      set J' := max N (φ k) with hJ'
      have hsub : ∑ j ∈ Finset.range N, (Λ (φ k) j) ^ 2
          ≤ ∑ j ∈ Finset.range J', (Λ (φ k) j) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.range_mono (le_max_left N (φ k))
        · intro i _ _; exact sq_nonneg _
      have heq : ∑ j ∈ Finset.range J', (Λ (φ k) j) ^ 2
          = (delta β) ^ 2 - ((φ k : ℝ) - 1) / (φ k) * (β 2 / β 0) := by
        exact (symmetric β hβ (φ k) (hφ1 k) J' (Λ (φ k))
          (fun z => hΛprod k J' (le_max_right N (φ k)) z)).2.2.1
      rw [← heq]; exact hsub
    have hLHS : Filter.Tendsto (fun k => ∑ j ∈ Finset.range N, (Λ (φ k) j) ^ 2)
        Filter.atTop (nhds (∑ j ∈ Finset.range N, (α j) ^ 2)) := by
      apply tendsto_finsetSum
      intro j _
      exact (hprop1 j).pow 2
    have hRHS : Filter.Tendsto (fun k => (delta β) ^ 2 - ((φ k : ℝ) - 1) / (φ k) * (β 2 / β 0))
        Filter.atTop (nhds (Bconst β)) :=
      (B_limit β hβ).1.comp hφtop
    exact le_of_tendsto_of_tendsto' hLHS hRHS hbound
  have hsummable : Summable (fun j => (α j) ^ 2) :=
    summable_of_sum_range_le (fun j => sq_nonneg _) hprop3
  have htsum : ∑' j, (α j) ^ 2 ≤ Bconst β :=
    Real.tsum_le_of_sum_range_le (fun j => sq_nonneg _) hprop3
  refine ⟨φ, α, (Bconst β - ∑' j, (α j) ^ 2) / 2, hφmono, hprop1, hprop2, hprop3,
    hsummable, htsum, ?_, ?_⟩
  · linarith [htsum]
  · ring

end Part6
