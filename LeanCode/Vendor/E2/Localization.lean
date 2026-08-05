import LeanCode.Vendor.E2.Pairing
import LeanCode.Vendor.E2.BanachFacts

open scoped ENNReal

namespace VendorE2.Lean_Code


noncomputable def hat (N : ℕ) (j k : ℤ) : ℝ :=
  max (1 - |((k - j * (N : ℤ) : ℤ) : ℝ)| / (N : ℝ)) 0

lemma hat_nonneg (N : ℕ) (j k : ℤ) : 0 ≤ hat N j k := by
  exact le_max_right _ _

lemma hat_le_one (N : ℕ) (j k : ℤ) : hat N j k ≤ 1 := by
  unfold hat
  refine max_le ?_ zero_le_one
  exact sub_le_self _ (div_nonneg (abs_nonneg _) (Nat.cast_nonneg _))

lemma hat_lipschitz
    (N : ℕ) (hN : 1 ≤ N) (j k l : ℤ) :
    |hat N j k - hat N j l| ≤
      min 1 (|((k - l : ℤ) : ℝ)| / (N : ℝ)) := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have h_le_one : |hat N j k - hat N j l| ≤ (1 : ℝ) := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [hat_nonneg N j k, hat_nonneg N j l,
      hat_le_one N j k, hat_le_one N j l]
  have h_le_dist :
      |hat N j k - hat N j l| ≤ |((k - l : ℤ) : ℝ)| / (N : ℝ) := by
    let A : ℝ := ((k - j * (N : ℤ) : ℤ) : ℝ)
    let B : ℝ := ((l - j * (N : ℤ) : ℤ) : ℝ)
    have hAB : |A - B| = |((k - l : ℤ) : ℝ)| := by
      congr 1
      simp [A, B]
    unfold hat
    change
      |max (1 - |A| / (N : ℝ)) 0 - max (1 - |B| / (N : ℝ)) 0| ≤
        |((k - l : ℤ) : ℝ)| / (N : ℝ)
    calc
      |max (1 - |A| / (N : ℝ)) 0 -
          max (1 - |B| / (N : ℝ)) 0| ≤
          |(1 - |A| / (N : ℝ)) - (1 - |B| / (N : ℝ))| :=
        abs_max_sub_max_le_abs _ _ _
      _ = abs (abs A - abs B) / (N : ℝ) := by
        calc
          |(1 - |A| / (N : ℝ)) - (1 - |B| / (N : ℝ))| =
              |(|B| - |A|) / (N : ℝ)| := by
            congr 1
            field_simp [hNpos.ne']
            ring
          _ = abs (abs B - abs A) / (N : ℝ) := by
            rw [abs_div, abs_of_pos hNpos]
          _ = abs (abs A - abs B) / (N : ℝ) := by
            rw [abs_sub_comm]
      _ ≤ |A - B| / (N : ℝ) := by
        exact div_le_div_of_nonneg_right
          (abs_abs_sub_abs_le_abs_sub A B) hNpos.le
      _ = |((k - l : ℤ) : ℝ)| / (N : ℝ) := by
        rw [hAB]
  exact le_min h_le_one h_le_dist


noncomputable def omega (N : ℕ) (n : ℤ) : ℝ :=
  min 1 (|((n : ℤ) : ℝ)| / (N : ℝ))

lemma omega_nonneg (N : ℕ) (n : ℤ) : 0 ≤ omega N n := by
  unfold omega
  exact le_min zero_le_one
    (div_nonneg (abs_nonneg _) (Nat.cast_nonneg _))

lemma omega_le_one (N : ℕ) (n : ℤ) : omega N n ≤ 1 := by
  unfold omega
  exact min_le_left _ _

lemma omega_neg (N : ℕ) (n : ℤ) : omega N (-n) = omega N n := by
  unfold omega
  simp

lemma omega_norm_le_one (N : ℕ) (n : ℤ) : ‖omega N n‖ ≤ 1 := by
  rw [Real.norm_of_nonneg (omega_nonneg N n)]
  exact omega_le_one N n

lemma tendsto_omega_atTop_zero (n : ℤ) :
    Filter.Tendsto (fun N : ℕ => omega N n) Filter.atTop (nhds 0) := by
  have hdiv :
      Filter.Tendsto (fun N : ℕ => |((n : ℤ) : ℝ)| / (N : ℝ))
        Filter.atTop (nhds 0) := by
    exact Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_natCast_atTop_atTop
  have hone : Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
      Filter.atTop (nhds (1 : ℝ)) :=
    tendsto_const_nhds
  have hmin := Filter.Tendsto.min hone hdiv
  unfold omega
  simpa using hmin

lemma summable_kernel_mul_omega
    (a : ℤ → ℝ) (hsumm : Summable fun n : ℤ => ‖a n‖) (N : ℕ) :
    Summable fun n : ℤ => a n * omega N n := by
  refine Summable.of_norm_bounded hsumm ?_
  intro n
  calc
    ‖a n * omega N n‖ = ‖a n‖ * ‖omega N n‖ := norm_mul _ _
    _ ≤ ‖a n‖ * 1 := by
      exact mul_le_mul_of_nonneg_left (omega_norm_le_one N n) (norm_nonneg _)
    _ = ‖a n‖ := mul_one _

lemma summable_norm_kernel_mul_omega
    (a : ℤ → ℝ) (hsumm : Summable fun n : ℤ => ‖a n‖) (N : ℕ) :
    Summable fun n : ℤ => ‖a n * omega N n‖ := by
  exact hsumm.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => by
    calc
      ‖a n * omega N n‖ = ‖a n‖ * ‖omega N n‖ := norm_mul _ _
      _ ≤ ‖a n‖ * 1 := by
        exact mul_le_mul_of_nonneg_left (omega_norm_le_one N n) (norm_nonneg _)
      _ = ‖a n‖ := mul_one _)

lemma kernel_omega_tendsto_zero
    (a : ℤ → ℝ) (hsumm : Summable fun n : ℤ => ‖a n‖) :
    Filter.Tendsto (fun N : ℕ => ∑' n : ℤ, a n * omega N n)
      Filter.atTop (nhds 0) := by
  have hpoint : ∀ n : ℤ,
      Filter.Tendsto (fun N : ℕ => a n * omega N n)
        Filter.atTop (nhds (0 : ℝ)) := by
    intro n
    simpa using
      (Filter.Tendsto.const_mul (a n) (tendsto_omega_atTop_zero n))
  have hbound : ∀ᶠ N : ℕ in Filter.atTop,
      ∀ n : ℤ, ‖a n * omega N n‖ ≤ ‖a n‖ := by
    exact Filter.Eventually.of_forall fun N n => by
      calc
        ‖a n * omega N n‖ = ‖a n‖ * ‖omega N n‖ := norm_mul _ _
        _ ≤ ‖a n‖ * 1 := by
          exact mul_le_mul_of_nonneg_left (omega_norm_le_one N n) (norm_nonneg _)
        _ = ‖a n‖ := mul_one _
  simpa using
    (tendsto_tsum_of_dominated_convergence
      (f := fun N : ℕ => fun n : ℤ => a n * omega N n)
      (g := fun _ : ℤ => (0 : ℝ))
      (bound := fun n : ℤ => ‖a n‖)
      hsumm hpoint hbound)

theorem exists_one_le_and_kernel_omega_tsum_lt
    (a : ℤ → ℝ) (hsumm : Summable fun n : ℤ => ‖a n‖)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, 1 ≤ N ∧
      tsum (fun n : ℤ => a n * omega N n) < epsilon := by
  have hlim := kernel_omega_tendsto_zero a hsumm
  have hevent : ∀ᶠ N : ℕ in Filter.atTop,
      tsum (fun n : ℤ => a n * omega N n) < epsilon := by
    exact hlim.eventually (eventually_lt_nhds hepsilon)
  rcases Filter.eventually_atTop.1 hevent with ⟨N0, hN0⟩
  refine ⟨max N0 1, le_max_right _ _, ?_⟩
  exact hN0 (max N0 1) (le_max_left _ _)


noncomputable def hatMultiplierSeq (N : ℕ) (j : ℤ) (x : ℤ → ℂ) : ℤ → ℂ :=
  fun k => (hat N j k : ℂ) * x k

noncomputable def hatMultiplier
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ) (j : ℤ) :
    ellp p →L[ℂ] ellp p :=
  lp.mapCLM p
    (fun k : ℤ => (hat N j k : ℂ) • ContinuousLinearMap.id ℂ ℂ)
    zero_le_one
    (by
      intro k
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
      intro z
      calc
        ‖((hat N j k : ℂ) • ContinuousLinearMap.id ℂ ℂ) z‖ =
            ‖(hat N j k : ℂ) * z‖ := by
          simp [smul_eq_mul]
        _ = ‖(hat N j k : ℂ)‖ * ‖z‖ := norm_mul _ _
        _ ≤ 1 * ‖z‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          have h_abs : ‖hat N j k‖ ≤ (1 : ℝ) := by
            rw [Real.norm_of_nonneg (hat_nonneg N j k)]
            exact hat_le_one N j k
          simpa using h_abs)

theorem hatMultiplier_apply
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ) (j : ℤ)
    (x : ellp p) (k : ℤ) :
    (hatMultiplier p N j x) k = (hat N j k : ℂ) * x k := by
  rfl

theorem hatMultiplier_norm_le
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ) (j : ℤ) :
    ‖hatMultiplier p N j‖ ≤ (1 : ℝ) := by
  unfold hatMultiplier
  exact lp.norm_mapCLM_le p
    (fun k : ℤ => (hat N j k : ℂ) • ContinuousLinearMap.id ℂ ℂ)
    zero_le_one
    (by
      intro k
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
      intro z
      calc
        ‖((hat N j k : ℂ) • ContinuousLinearMap.id ℂ ℂ) z‖ =
            ‖(hat N j k : ℂ) * z‖ := by
          simp [smul_eq_mul]
        _ = ‖(hat N j k : ℂ)‖ * ‖z‖ := norm_mul _ _
        _ ≤ 1 * ‖z‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (hat_nonneg N j k)]
          exact hat_le_one N j k)

theorem exists_blockNorm
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) :
    ∃ M : ellp p → ℝ,
      1 ≤ N →
        ∃ α β : ℝ, 0 < α ∧ 0 < β ∧
          ∀ x : ellp p, α * ‖x‖ ≤ M x ∧ M x ≤ β * ‖x‖ := by
  refine ⟨fun x => ‖x‖, ?_⟩
  intro _hN
  refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
  intro x
  constructor <;> simp

noncomputable def blockNorm
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (x : ellp p) : ℝ :=
  Classical.choose (exists_blockNorm p r N) x

lemma hat_far_of_not_adjacent
    (N : ℕ) (hN : 1 ≤ N) (k j : ℤ)
    (hjq : j ≠ k / (N : ℤ)) (hjq1 : j ≠ k / (N : ℤ) + 1) :
    (N : ℤ) ≤ |k - j * (N : ℤ)| := by
  let n : ℤ := (N : ℤ)
  let q : ℤ := k / n
  let r : ℤ := k % n
  have hn_pos : 0 < n := by
    have hN_pos : 0 < N := Nat.zero_lt_of_lt hN
    have : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN_pos
    simpa [n] using this
  have hk : k = q * n + r := by
    calc
      k = k / n * n + k % n := by rw [Int.ediv_mul_add_emod]
      _ = q * n + r := by rfl
  have hr_nonneg : 0 ≤ r := by
    exact Int.emod_nonneg k hn_pos.ne'
  have hr_lt : r < n := by
    exact Int.emod_lt_of_pos k hn_pos
  by_cases hj_lt : j < q
  · have hdist : n ≤ k - j * n := by
      rw [hk]
      nlinarith [mul_le_mul_of_nonneg_right
        (show (1 : ℤ) ≤ q - j by omega) hn_pos.le]
    have hdist_abs : k - j * n ≤ |k - j * n| := le_abs_self _
    simpa [n] using hdist.trans hdist_abs
  · have hj_gt : q + 1 < j := by
      have hj_ne_q : j ≠ q := by simpa [q, n] using hjq
      have hj_ne_q1 : j ≠ q + 1 := by simpa [q, n] using hjq1
      omega
    have hdist : n ≤ j * n - k := by
      rw [hk]
      have htwo : (2 : ℤ) ≤ j - q := by omega
      nlinarith [mul_le_mul_of_nonneg_right htwo hn_pos.le, hr_lt]
    have hneg : j * n - k = -(k - j * n) := by ring
    have hdist_abs : j * n - k ≤ |k - j * n| := by
      rw [hneg]
      exact neg_le_abs _
    simpa [n] using hdist.trans hdist_abs

lemma hat_eq_zero_of_not_adjacent
    (N : ℕ) (hN : 1 ≤ N) (k j : ℤ)
    (hjq : j ≠ k / (N : ℤ)) (hjq1 : j ≠ k / (N : ℤ) + 1) :
    hat N j k = 0 := by
  have hNposR : 0 < (N : ℝ) := by
    have hN_pos : 0 < N := Nat.zero_lt_of_lt hN
    exact_mod_cast hN_pos
  have hfarZ := hat_far_of_not_adjacent N hN k j hjq hjq1
  have hfarR : (N : ℝ) ≤ |((k - j * (N : ℤ) : ℤ) : ℝ)| := by
    exact_mod_cast hfarZ
  unfold hat
  rw [max_eq_right]
  have hdiv : 1 ≤ |((k - j * (N : ℤ) : ℤ) : ℝ)| / (N : ℝ) := by
    exact (le_div_iff₀ hNposR).mpr (by simpa using hfarR)
  linarith

lemma hat_eq_zero_of_far
    (N : ℕ) (hN : 1 ≤ N) (j k : ℤ)
    (hfar : (N : ℤ) ≤ |k - j * (N : ℤ)|) :
    hat N j k = 0 := by
  have hNposR : 0 < (N : ℝ) := by
    have hN_pos : 0 < N := Nat.zero_lt_of_lt hN
    exact_mod_cast hN_pos
  have hfarR : (N : ℝ) ≤ |((k - j * (N : ℤ) : ℤ) : ℝ)| := by
    exact_mod_cast hfar
  unfold hat
  rw [max_eq_right]
  have hdiv : 1 ≤ |((k - j * (N : ℤ) : ℤ) : ℝ)| / (N : ℝ) := by
    exact (le_div_iff₀ hNposR).mpr (by simpa using hfarR)
  linarith

lemma hat_nonzero_abs_lt
    (N : ℕ) (hN : 1 ≤ N) (j k : ℤ)
    (hk : hat N j k ≠ 0) :
    |k - j * (N : ℤ)| < (N : ℤ) := by
  by_contra hnot
  have hfar : (N : ℤ) ≤ |k - j * (N : ℤ)| := by omega
  exact hk (hat_eq_zero_of_far N hN j k hfar)

lemma hat_support_subset_interval
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) :
    {k : ℤ | hat N j k ≠ 0} ⊆
      (Finset.Icc (j * (N : ℤ) - (N : ℤ))
        (j * (N : ℤ) + (N : ℤ)) : Finset ℤ) := by
  intro k hk
  by_contra hk_interval
  have hnot :
      ¬ (j * (N : ℤ) - (N : ℤ) ≤ k ∧
        k ≤ j * (N : ℤ) + (N : ℤ)) := by
    simpa using hk_interval
  have hfar : (N : ℤ) ≤ |k - j * (N : ℤ)| := by
    have hor :
        k < j * (N : ℤ) - (N : ℤ) ∨
          j * (N : ℤ) + (N : ℤ) < k := by
      omega
    rcases hor with hleft | hright
    · have hdist : (N : ℤ) ≤ j * (N : ℤ) - k := by omega
      have hdist_abs : j * (N : ℤ) - k ≤ |k - j * (N : ℤ)| := by
        have hneg : j * (N : ℤ) - k = -(k - j * (N : ℤ)) := by ring
        rw [hneg]
        exact neg_le_abs _
      exact hdist.trans hdist_abs
    · have hdist : (N : ℤ) ≤ k - j * (N : ℤ) := by omega
      exact hdist.trans (le_abs_self _)
  exact hk (hat_eq_zero_of_far N hN j k hfar)

lemma hat_support_finite
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) :
    {k : ℤ | hat N j k ≠ 0}.Finite :=
  (Finset.finite_toSet _).subset (hat_support_subset_interval N hN j)

lemma hat_support_ncard_le
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) :
    {k : ℤ | hat N j k ≠ 0}.ncard ≤ 2 * N + 1 := by
  let s : Finset ℤ :=
    Finset.Icc (j * (N : ℤ) - (N : ℤ)) (j * (N : ℤ) + (N : ℤ))
  have hsubset : {k : ℤ | hat N j k ≠ 0} ⊆ (s : Set ℤ) := by
    simpa [s] using hat_support_subset_interval N hN j
  have hle : {k : ℤ | hat N j k ≠ 0}.ncard ≤ (s : Set ℤ).ncard :=
    Set.ncard_le_ncard hsubset
  rw [Set.ncard_coe_finset] at hle
  have hcard : s.card = 2 * N + 1 := by
    have hcard_int : (s.card : ℤ) = (2 * (N : ℤ) + 1) := by
      dsimp [s]
      rw [Int.card_Icc_of_le]
      · ring
      · omega
    exact_mod_cast hcard_int
  simpa [hcard] using hle

lemma hat_index_support_subset_pair
    (N : ℕ) (hN : 1 ≤ N) (k : ℤ) :
    {j : ℤ | hat N j k ≠ 0} ⊆
      (({k / (N : ℤ), k / (N : ℤ) + 1} : Finset ℤ) : Set ℤ) := by
  intro j hj
  by_contra hj_pair
  have hj_ne : j ≠ k / (N : ℤ) ∧ j ≠ k / (N : ℤ) + 1 := by
    simpa using hj_pair
  exact hj (hat_eq_zero_of_not_adjacent N hN k j hj_ne.1 hj_ne.2)

lemma hat_index_support_finite
    (N : ℕ) (hN : 1 ≤ N) (k : ℤ) :
    {j : ℤ | hat N j k ≠ 0}.Finite :=
  (Finset.finite_toSet _).subset (hat_index_support_subset_pair N hN k)

lemma hat_index_support_ncard_le_two
    (N : ℕ) (hN : 1 ≤ N) (k : ℤ) :
    {j : ℤ | hat N j k ≠ 0}.ncard ≤ 2 := by
  have hsubset := hat_index_support_subset_pair N hN k
  have hle : {j : ℤ | hat N j k ≠ 0}.ncard ≤
      (({k / (N : ℤ), k / (N : ℤ) + 1} : Finset ℤ) : Set ℤ).ncard :=
    Set.ncard_le_ncard hsubset (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at hle
  have hcard : ({k / (N : ℤ), k / (N : ℤ) + 1} : Finset ℤ).card = 2 := by
    simp
  simpa [hcard] using hle

lemma hat_index_support_abs_sub_le_one
    (N : ℕ) (hN : 1 ≤ N) {i j k : ℤ}
    (hi : hat N i k ≠ 0) (hj : hat N j k ≠ 0) :
    |i - j| ≤ 1 := by
  have hi_pair := hat_index_support_subset_pair N hN k hi
  have hj_pair := hat_index_support_subset_pair N hN k hj
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hi_pair hj_pair
  rcases hi_pair with hi_eq | hi_eq <;> rcases hj_pair with hj_eq | hj_eq <;>
    subst i <;> subst j <;> simp

lemma int_ediv_mul_sub_abs_lt
    (N : ℕ) (hN : 1 ≤ N) (n : ℤ) :
    |n - (n / (N : ℤ)) * (N : ℤ)| < (N : ℤ) := by
  have hN_pos : 0 < (N : ℤ) := by
    exact_mod_cast Nat.zero_lt_of_lt hN
  have hmod_nonneg : 0 ≤ n % (N : ℤ) :=
    Int.emod_nonneg n hN_pos.ne'
  have hmod_lt : n % (N : ℤ) < (N : ℤ) :=
    Int.emod_lt_of_pos n hN_pos
  have hdecomp : n = n / (N : ℤ) * (N : ℤ) + n % (N : ℤ) := by
    rw [Int.ediv_mul_add_emod]
  have hdiff : n - (n / (N : ℤ)) * (N : ℤ) = n % (N : ℤ) := by
    omega
  rw [hdiff, abs_of_nonneg hmod_nonneg]
  exact hmod_lt

lemma shifted_hat_index_support_abs_sub_le_two
    (N : ℕ) (hN : 1 ≤ N) {i j k n h : ℤ}
    (hnear : |n - h * (N : ℤ)| < (N : ℤ))
    (hi : hat N i k ≠ 0) (hj : hat N j (k + n) ≠ 0) :
    |i - (j - h)| ≤ 2 := by
  have hN_pos : 0 < (N : ℤ) := by
    exact_mod_cast Nat.zero_lt_of_lt hN
  have hi_lt := hat_nonzero_abs_lt N hN i k hi
  have hj_lt := hat_nonzero_abs_lt N hN j (k + n) hj
  have hcenter :
      |(i - (j - h)) * (N : ℤ)| < 3 * (N : ℤ) := by
    have hrepr :
        (i - (j - h)) * (N : ℤ) =
          ((k + n) - j * (N : ℤ)) -
            (n - h * (N : ℤ)) -
              (k - i * (N : ℤ)) := by
      ring
    rw [hrepr]
    rw [abs_lt] at hi_lt hj_lt hnear ⊢
    constructor <;> omega
  by_contra hnot
  have hd_ge : 3 ≤ |i - (j - h)| := by omega
  rw [abs_mul, abs_of_nonneg hN_pos.le] at hcenter
  nlinarith

lemma shifted_hat_index_support_abs_sub_le_two_div
    (N : ℕ) (hN : 1 ≤ N) {i j k n : ℤ}
    (hi : hat N i k ≠ 0) (hj : hat N j (k + n) ≠ 0) :
    |i - (j - n / (N : ℤ))| ≤ 2 :=
  shifted_hat_index_support_abs_sub_le_two N hN
    (int_ediv_mul_sub_abs_lt N hN n) hi hj

lemma hat_index_support_subset_neighbor_one
    (N : ℕ) (hN : 1 ≤ N) (j k : ℤ)
    (hj : hat N j k ≠ 0) :
    {i : ℤ | hat N i k ≠ 0} ⊆
      ((Finset.Icc (j - 1) (j + 1) : Finset ℤ) : Set ℤ) := by
  intro i hi
  have hdist := hat_index_support_abs_sub_le_one N hN hi hj
  rw [abs_le] at hdist
  simp
  omega

lemma shifted_hat_index_support_subset_neighbor_two_div
    (N : ℕ) (hN : 1 ≤ N) (j k n : ℤ)
    (hj : hat N j (k + n) ≠ 0) :
    {i : ℤ | hat N i k ≠ 0} ⊆
      ((Finset.Icc (j - n / (N : ℤ) - 2)
        (j - n / (N : ℤ) + 2) : Finset ℤ) : Set ℤ) := by
  intro i hi
  have hdist := shifted_hat_index_support_abs_sub_le_two_div N hN hi hj
  rw [abs_le] at hdist
  simp
  omega

lemma neighbor_one_card (j : ℤ) :
    (Finset.Icc (j - 1) (j + 1) : Finset ℤ).card = 3 := by
  have hcard_int :
      ((Finset.Icc (j - 1) (j + 1) : Finset ℤ).card : ℤ) = 3 := by
    rw [Int.card_Icc_of_le]
    · ring
    · omega
  exact_mod_cast hcard_int

lemma neighbor_two_card (j : ℤ) :
    (Finset.Icc (j - 2) (j + 2) : Finset ℤ).card = 5 := by
  have hcard_int :
      ((Finset.Icc (j - 2) (j + 2) : Finset ℤ).card : ℤ) = 5 := by
    rw [Int.card_Icc_of_le]
    · ring
    · omega
  exact_mod_cast hcard_int

lemma finset_sum_Icc_add_left_int
    (a b j : ℤ) (F : ℤ → ℝ) :
    ∑ d ∈ Finset.Icc a b, F (j + d) =
      ∑ i ∈ Finset.Icc (j + a) (j + b), F i := by
  classical
  refine Finset.sum_bij (fun d _hd => j + d) ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_Icc] at hd ⊢
    omega
  · intro d₁ _hd₁ d₂ _hd₂ h
    omega
  · intro i hi
    refine ⟨i - j, ?_, ?_⟩
    · simp only [Finset.mem_Icc] at hi ⊢
      omega
    · omega
  · intro d _hd
    rfl

lemma hatMultiplier_index_support_subset_pair
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) (k : ℤ) :
    {j : ℤ | (hatMultiplier p N j x) k ≠ 0} ⊆
      (({k / (N : ℤ), k / (N : ℤ) + 1} : Finset ℤ) : Set ℤ) := by
  intro j hj
  have hhat : hat N j k ≠ 0 := by
    change (hatMultiplier p N j x) k ≠ 0 at hj
    rw [hatMultiplier_apply] at hj
    exact Complex.ofReal_ne_zero.mp (mul_ne_zero_iff.mp hj).1
  exact hat_index_support_subset_pair N hN k hhat

lemma hatMultiplier_index_support_finite
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) (k : ℤ) :
    {j : ℤ | (hatMultiplier p N j x) k ≠ 0}.Finite :=
  (Finset.finite_toSet _).subset
    (hatMultiplier_index_support_subset_pair p N hN x k)

lemma hatMultiplier_index_support_ncard_le_two
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) (k : ℤ) :
    {j : ℤ | (hatMultiplier p N j x) k ≠ 0}.ncard ≤ 2 := by
  have hsubset := hatMultiplier_index_support_subset_pair p N hN x k
  have hle : {j : ℤ | (hatMultiplier p N j x) k ≠ 0}.ncard ≤
      (({k / (N : ℤ), k / (N : ℤ) + 1} : Finset ℤ) : Set ℤ).ncard :=
    Set.ncard_le_ncard hsubset (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at hle
  have hcard : ({k / (N : ℤ), k / (N : ℤ) + 1} : Finset ℤ).card = 2 := by
    simp
  simpa [hcard] using hle

lemma hatMultiplier_support_subset_hat
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ) (j : ℤ) (x : ellp p) :
    {k : ℤ | (hatMultiplier p N j x) k ≠ 0} ⊆
      {k : ℤ | hat N j k ≠ 0} := by
  intro k hk
  change (hatMultiplier p N j x) k ≠ 0 at hk
  change hat N j k ≠ 0
  rw [hatMultiplier_apply] at hk
  exact Complex.ofReal_ne_zero.mp (mul_ne_zero_iff.mp hk).1

lemma hatMultiplier_support_finite
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ) (hN : 1 ≤ N)
    (j : ℤ) (x : ellp p) :
    {k : ℤ | (hatMultiplier p N j x) k ≠ 0}.Finite :=
  (hat_support_finite N hN j).subset
    (hatMultiplier_support_subset_hat p N j x)

lemma hatMultiplier_support_ncard_le
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ) (hN : 1 ≤ N)
    (j : ℤ) (x : ellp p) :
    {k : ℤ | (hatMultiplier p N j x) k ≠ 0}.ncard ≤ 2 * N + 1 :=
  (Set.ncard_le_ncard (hatMultiplier_support_subset_hat p N j x)
    (hat_support_finite N hN j)).trans
    (hat_support_ncard_le N hN j)






noncomputable def localizedBlockPiece
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) (x : ellp p) : ellp r :=
  ⟨fun k : ℤ => (hat N j k : ℂ) * x k, by
    have hsubset :
        {k : ℤ | (hat N j k : ℂ) * x k ≠ 0} ⊆
          {k : ℤ | hat N j k ≠ 0} := by
      intro k hk
      exact Complex.ofReal_ne_zero.mp (mul_ne_zero_iff.mp hk).1
    have hfinite : {k : ℤ | (hat N j k : ℂ) * x k ≠ 0}.Finite :=
      (hat_support_finite N hN j).subset hsubset
    exact (memℓp_zero hfinite).of_exponent_ge
      (zero_le : (0 : ℝ≥0∞) ≤ r)⟩

theorem localizedBlockPiece_apply
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) (x : ellp p) (k : ℤ) :
    localizedBlockPiece p r N hN j x k = (hat N j k : ℂ) * x k := by
  rfl

lemma shifted_hat_support_finite
    (N : ℕ) (hN : 1 ≤ N) (j n : ℤ) :
    {k : ℤ | hat N j (k + n) ≠ 0}.Finite := by
  let f : ℤ → ℤ := fun k => k + n
  have hf : Set.InjOn f (f ⁻¹' {k : ℤ | hat N j k ≠ 0}) := by
    intro a _ha b _hb hab
    dsimp [f] at hab
    omega
  simpa [f, Set.preimage] using (hat_support_finite N hN j).preimage hf

noncomputable def shiftedLocalizedBlockPiece
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (j n : ℤ) (x : ellp p) : ellp r :=
  ⟨fun k : ℤ => (hat N j (k + n) : ℂ) * x k, by
    have hsubset :
        {k : ℤ | (hat N j (k + n) : ℂ) * x k ≠ 0} ⊆
          {k : ℤ | hat N j (k + n) ≠ 0} := by
      intro k hk
      exact Complex.ofReal_ne_zero.mp (mul_ne_zero_iff.mp hk).1
    have hfinite : {k : ℤ | (hat N j (k + n) : ℂ) * x k ≠ 0}.Finite :=
      (shifted_hat_support_finite N hN j n).subset hsubset
    exact (memℓp_zero hfinite).of_exponent_ge
      (zero_le : (0 : ℝ≥0∞) ≤ r)⟩

theorem shiftedLocalizedBlockPiece_apply
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (j n : ℤ) (x : ellp p) (k : ℤ) :
    shiftedLocalizedBlockPiece p r N hN j n x k =
      (hat N j (k + n) : ℂ) * x k := by
  rfl

noncomputable def localizedMultiplierDifferenceBlock
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (j n : ℤ) (x : ellp p) : ellp r :=
  localizedBlockPiece p r N hN j x -
    shiftedLocalizedBlockPiece p r N hN j n x

theorem localizedMultiplierDifferenceBlock_apply
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (j n : ℤ) (x : ellp p) (k : ℤ) :
    localizedMultiplierDifferenceBlock p r N hN j n x k =
      ((hat N j k : ℂ) - (hat N j (k + n) : ℂ)) * x k := by
  unfold localizedMultiplierDifferenceBlock
  rw [lp.coeFn_sub, Pi.sub_apply, localizedBlockPiece_apply,
    shiftedLocalizedBlockPiece_apply]
  ring

theorem localizedMultiplierDifferenceBlock_norm_le
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (j n : ℤ) (x : ellp p) :
    ‖localizedMultiplierDifferenceBlock p r N hN j n x‖ ≤
      ‖localizedBlockPiece p r N hN j x‖ +
        ‖shiftedLocalizedBlockPiece p r N hN j n x‖ := by
  unfold localizedMultiplierDifferenceBlock
  exact norm_sub_le _ _

theorem localizedMultiplierDifferenceBlock_apply_norm_le_omega
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (j n : ℤ) (x : ellp p) (k : ℤ) :
    ‖localizedMultiplierDifferenceBlock p r N hN j n x k‖ ≤
      omega N n * ‖x k‖ := by
  have hdiff : ‖((hat N j k : ℂ) - (hat N j (k + n) : ℂ))‖ ≤
      omega N n := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have h : |hat N j k - hat N j (k + n)| ≤ omega N (k - (k + n)) := by
      exact hat_lipschitz N hN j k (k + n)
    have hsub : k - (k + n) = -n := by ring
    rw [hsub, omega_neg] at h
    exact h
  rw [localizedMultiplierDifferenceBlock_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right hdiff (norm_nonneg _)

lemma localizedMultiplierDifferenceBlock_support_subset_union
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (j n : ℤ) (x : ellp p) :
    {k : ℤ | localizedMultiplierDifferenceBlock p r N hN j n x k ≠ 0} ⊆
      {k : ℤ | hat N j k ≠ 0} ∪
        {k : ℤ | hat N j (k + n) ≠ 0} := by
  intro k hk
  change localizedMultiplierDifferenceBlock p r N hN j n x k ≠ 0 at hk
  by_cases hleft : hat N j k = 0
  · right
    by_contra hright
    have hright_zero : hat N j (k + n) = 0 := by
      by_contra hright_nonzero
      exact hright hright_nonzero
    rw [localizedMultiplierDifferenceBlock_apply, hleft] at hk
    simp [hright_zero] at hk
  · left
    exact hleft

lemma localizedMultiplierDifferenceBlock_support_finite
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (j n : ℤ) (x : ellp p) :
    {k : ℤ | localizedMultiplierDifferenceBlock p r N hN j n x k ≠ 0}.Finite :=
  ((hat_support_finite N hN j).union
    (shifted_hat_support_finite N hN j n)).subset
    (localizedMultiplierDifferenceBlock_support_subset_union p r N hN j n x)

theorem shiftedLocalizedBlockPiece_eq_shift_localizedBlockPiece
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (j n : ℤ) (x : ellp p) :
    shiftedLocalizedBlockPiece p r N hN j n x =
      shiftOperator r (-n)
        (localizedBlockPiece p r N hN j (shiftOperator p n x)) := by
  ext k
  rw [shiftedLocalizedBlockPiece_apply]
  simp [shiftOperator, reindexOperator, reindexLinearIsometryEquiv, shiftEquiv,
    localizedBlockPiece_apply]

theorem shiftedLocalizedBlockPiece_norm_eq
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (j n : ℤ) (x : ellp p) :
    ‖shiftedLocalizedBlockPiece p r N hN j n x‖ =
      ‖localizedBlockPiece p r N hN j (shiftOperator p n x)‖ := by
  rw [shiftedLocalizedBlockPiece_eq_shift_localizedBlockPiece]
  exact ellp_shift_isometry r (-n)
    (localizedBlockPiece p r N hN j (shiftOperator p n x))

theorem localizedBlockPiece_apply_norm_rpow
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) (x : ellp p)
    (q : ℝ) (k : ℤ) :
    ‖localizedBlockPiece p r N hN j x k‖ ^ q =
      (hat N j k) ^ q * ‖x k‖ ^ q := by
  rw [localizedBlockPiece_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hat_nonneg N j k),
    Real.mul_rpow (hat_nonneg N j k) (norm_nonneg (x k))]

theorem localizedBlockPiece_eq_hatMultiplier
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) (x : ellp p) :
    localizedBlockPiece p p N hN j x = hatMultiplier p N j x := by
  ext k
  rfl

lemma localizedBlockPiece_support_finite
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) (x : ellp p) :
    {k : ℤ | localizedBlockPiece p r N hN j x k ≠ 0}.Finite := by
  refine (hat_support_finite N hN j).subset ?_
  intro k hk
  change localizedBlockPiece p r N hN j x k ≠ 0 at hk
  change hat N j k ≠ 0
  rw [localizedBlockPiece_apply] at hk
  exact Complex.ofReal_ne_zero.mp (mul_ne_zero_iff.mp hk).1

lemma localizedBlockPiece_support_ncard_le
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) (x : ellp p) :
    {k : ℤ | localizedBlockPiece p r N hN j x k ≠ 0}.ncard ≤ 2 * N + 1 :=
  (Set.ncard_le_ncard
    (by
      intro k hk
      change localizedBlockPiece p r N hN j x k ≠ 0 at hk
      change hat N j k ≠ 0
      rw [localizedBlockPiece_apply] at hk
      exact Complex.ofReal_ne_zero.mp (mul_ne_zero_iff.mp hk).1)
    (hat_support_finite N hN j)).trans
    (hat_support_ncard_le N hN j)


noncomputable def localizedBlockNormSeq
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) : ℤ → ℝ :=
  fun j => ‖localizedBlockPiece p r N hN j x‖

theorem localizedBlockNormSeq_apply
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) (j : ℤ) :
    localizedBlockNormSeq p r N hN x j =
      ‖localizedBlockPiece p r N hN j x‖ := by
  rfl

theorem localizedBlockNormSeq_nonneg
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) (j : ℤ) :
    0 ≤ localizedBlockNormSeq p r N hN x j :=
  norm_nonneg _

theorem localizedBlockNormSeq_same_exponent
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) (j : ℤ) :
    localizedBlockNormSeq p p N hN x j = ‖hatMultiplier p N j x‖ := by
  rw [localizedBlockNormSeq_apply, localizedBlockPiece_eq_hatMultiplier]


noncomputable def localizedBlockNormSeqC
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) : ℤ → ℂ :=
  fun j => (localizedBlockNormSeq p r N hN x j : ℂ)

theorem localizedBlockNormSeqC_apply
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) (j : ℤ) :
    localizedBlockNormSeqC p r N hN x j =
      (localizedBlockNormSeq p r N hN x j : ℂ) := by
  rfl

theorem localizedBlockNormSeqC_norm
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) (j : ℤ) :
    ‖localizedBlockNormSeqC p r N hN x j‖ =
      localizedBlockNormSeq p r N hN x j := by
  rw [localizedBlockNormSeqC_apply, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (localizedBlockNormSeq_nonneg p r N hN x j)

theorem localizedBlockNormSeqC_infty_infty_pointwise_norm_le
    (N : ℕ) (hN : 1 ≤ N) (x : ellp (∞ : ℝ≥0∞)) (j : ℤ) :
    ‖localizedBlockNormSeqC (∞ : ℝ≥0∞) (∞ : ℝ≥0∞) N hN x j‖ ≤ ‖x‖ := by
  rw [localizedBlockNormSeqC_norm, localizedBlockNormSeq_same_exponent]
  calc
    ‖hatMultiplier (∞ : ℝ≥0∞) N j x‖ ≤
        ‖hatMultiplier (∞ : ℝ≥0∞) N j‖ * ‖x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖x‖ := by
      exact mul_le_mul_of_nonneg_right
        (hatMultiplier_norm_le (∞ : ℝ≥0∞) N j) (norm_nonneg x)
    _ = ‖x‖ := one_mul _


noncomputable def localizedBlockNormSeqInfty
    (N : ℕ) (hN : 1 ≤ N) (x : ellp (∞ : ℝ≥0∞)) :
    ellp (∞ : ℝ≥0∞) :=
  ⟨localizedBlockNormSeqC (∞ : ℝ≥0∞) (∞ : ℝ≥0∞) N hN x, by
    apply memℓp_infty
    refine ⟨‖x‖, ?_⟩
    rintro _ ⟨j, rfl⟩
    exact localizedBlockNormSeqC_infty_infty_pointwise_norm_le N hN x j⟩

theorem localizedBlockNormSeqInfty_apply
    (N : ℕ) (hN : 1 ≤ N) (x : ellp (∞ : ℝ≥0∞)) (j : ℤ) :
    localizedBlockNormSeqInfty N hN x j =
      localizedBlockNormSeqC (∞ : ℝ≥0∞) (∞ : ℝ≥0∞) N hN x j := by
  rfl

theorem localizedBlockNormSeqInfty_norm_le
    (N : ℕ) (hN : 1 ≤ N) (x : ellp (∞ : ℝ≥0∞)) :
    ‖localizedBlockNormSeqInfty N hN x‖ ≤ ‖x‖ := by
  rw [lp.norm_eq_ciSup]
  exact ciSup_le fun j => by
    change ‖localizedBlockNormSeqC (∞ : ℝ≥0∞) (∞ : ℝ≥0∞) N hN x j‖ ≤ ‖x‖
    exact localizedBlockNormSeqC_infty_infty_pointwise_norm_le N hN x j

lemma hat_left_partition_value
    (N : ℕ) (hN : 1 ≤ N) (k : ℤ) :
    hat N (k / (N : ℤ)) k =
      1 - ((k % (N : ℤ) : ℤ) : ℝ) / (N : ℝ) := by
  let n : ℤ := (N : ℤ)
  let q : ℤ := k / n
  let r : ℤ := k % n
  have hn_posZ : 0 < n := by
    have hN_pos : 0 < N := Nat.zero_lt_of_lt hN
    have : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN_pos
    simpa [n] using this
  have hn_posR : 0 < (N : ℝ) := by
    have hN_pos : 0 < N := Nat.zero_lt_of_lt hN
    exact_mod_cast hN_pos
  have hk : k = q * n + r := by
    calc
      k = k / n * n + k % n := by rw [Int.ediv_mul_add_emod]
      _ = q * n + r := by rfl
  have hr_nonnegZ : 0 ≤ r := Int.emod_nonneg k hn_posZ.ne'
  have hr_ltZ : r < n := Int.emod_lt_of_pos k hn_posZ
  have hdist : |((k - q * n : ℤ) : ℝ)| = (r : ℝ) := by
    have hkr : k - q * n = r := by omega
    rw [hkr]
    exact abs_of_nonneg (by exact_mod_cast hr_nonnegZ)
  have hnonneg : 0 ≤ 1 - (r : ℝ) / (N : ℝ) := by
    have hr_leR : (r : ℝ) ≤ (N : ℝ) := by
      have : r ≤ n := le_of_lt hr_ltZ
      simpa [n] using (by exact_mod_cast this : (r : ℝ) ≤ (n : ℝ))
    have hdiv_le : (r : ℝ) / (N : ℝ) ≤ 1 := by
      exact (div_le_one hn_posR).mpr (by simpa using hr_leR)
    linarith
  unfold hat
  change max (1 - |((k - q * n : ℤ) : ℝ)| / (N : ℝ)) 0 =
    1 - (r : ℝ) / (N : ℝ)
  rw [hdist]
  exact max_eq_left hnonneg

lemma hat_right_partition_value
    (N : ℕ) (hN : 1 ≤ N) (k : ℤ) :
    hat N (k / (N : ℤ) + 1) k =
      ((k % (N : ℤ) : ℤ) : ℝ) / (N : ℝ) := by
  let n : ℤ := (N : ℤ)
  let q : ℤ := k / n
  let r : ℤ := k % n
  have hn_posZ : 0 < n := by
    have hN_pos : 0 < N := Nat.zero_lt_of_lt hN
    have : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN_pos
    simpa [n] using this
  have hn_posR : 0 < (N : ℝ) := by
    have hN_pos : 0 < N := Nat.zero_lt_of_lt hN
    exact_mod_cast hN_pos
  have hk : k = q * n + r := by
    calc
      k = k / n * n + k % n := by rw [Int.ediv_mul_add_emod]
      _ = q * n + r := by rfl
  have hr_nonnegZ : 0 ≤ r := Int.emod_nonneg k hn_posZ.ne'
  have hr_ltZ : r < n := Int.emod_lt_of_pos k hn_posZ
  have hdist : |((k - (q + 1) * n : ℤ) : ℝ)| = (n - r : ℤ) := by
    have hkr : k - (q + 1) * n = r - n := by
      rw [hk]
      ring
    have hnonpos : r - n ≤ 0 := by omega
    rw [hkr]
    rw [abs_of_nonpos]
    · norm_num
    · exact_mod_cast hnonpos
  have hnonneg : 0 ≤ (r : ℝ) / (N : ℝ) := by
    exact div_nonneg (by exact_mod_cast hr_nonnegZ) hn_posR.le
  unfold hat
  change max (1 - |((k - (q + 1) * n : ℤ) : ℝ)| / (N : ℝ)) 0 =
    (r : ℝ) / (N : ℝ)
  rw [hdist]
  have hcalc : 1 - ((n - r : ℤ) : ℝ) / (N : ℝ) =
      (r : ℝ) / (N : ℝ) := by
    have hnR : (n : ℝ) = (N : ℝ) := by simp [n]
    rw [Int.cast_sub, hnR]
    field_simp [hn_posR.ne']
    ring
  rw [hcalc]
  exact max_eq_left hnonneg

lemma exists_hat_ge_half
    (N : ℕ) (hN : 1 ≤ N) (k : ℤ) :
    ∃ j : ℤ, (1 / 2 : ℝ) ≤ hat N j k := by
  let r : ℤ := k % (N : ℤ)
  have hNposR : 0 < (N : ℝ) := by
    have hN_pos : 0 < N := Nat.zero_lt_of_lt hN
    exact_mod_cast hN_pos
  by_cases hleft : (2 : ℤ) * r ≤ (N : ℤ)
  · refine ⟨k / (N : ℤ), ?_⟩
    rw [hat_left_partition_value N hN k]
    have hleftR : (2 : ℝ) * (r : ℝ) ≤ (N : ℝ) := by
      simpa [r] using (by exact_mod_cast hleft :
        (2 : ℝ) * (r : ℝ) ≤ ((N : ℤ) : ℝ))
    have hdiv : (r : ℝ) / (N : ℝ) ≤ (1 / 2 : ℝ) := by
      rw [div_le_iff₀ hNposR]
      nlinarith
    linarith
  · refine ⟨k / (N : ℤ) + 1, ?_⟩
    rw [hat_right_partition_value N hN k]
    have hrightZ : (N : ℤ) ≤ (2 : ℤ) * r := by omega
    have hrightR : (N : ℝ) ≤ (2 : ℝ) * (r : ℝ) := by
      simpa [r] using (by exact_mod_cast hrightZ :
        ((N : ℤ) : ℝ) ≤ (2 : ℝ) * (r : ℝ))
    rw [le_div_iff₀ hNposR]
    nlinarith

theorem norm_le_two_mul_localizedBlockNormSeqInfty_norm
    (N : ℕ) (hN : 1 ≤ N) (x : ellp (∞ : ℝ≥0∞)) :
    ‖x‖ ≤ 2 * ‖localizedBlockNormSeqInfty N hN x‖ := by
  rw [lp.norm_eq_ciSup]
  exact ciSup_le fun k => by
    rcases exists_hat_ge_half N hN k with ⟨j, hj⟩
    have hcoord :
        (1 / 2 : ℝ) * ‖x k‖ ≤
          ‖localizedBlockPiece (∞ : ℝ≥0∞) (∞ : ℝ≥0∞) N hN j x k‖ := by
      rw [localizedBlockPiece_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (hat_nonneg N j k)]
      exact mul_le_mul_of_nonneg_right hj (norm_nonneg _)
    have hpiece_to_seq :
        ‖localizedBlockPiece (∞ : ℝ≥0∞) (∞ : ℝ≥0∞) N hN j x‖ ≤
          ‖localizedBlockNormSeqInfty N hN x‖ := by
      calc
        ‖localizedBlockPiece (∞ : ℝ≥0∞) (∞ : ℝ≥0∞) N hN j x‖ =
            ‖localizedBlockNormSeqInfty N hN x j‖ := by
          rw [localizedBlockNormSeqInfty_apply, localizedBlockNormSeqC_norm,
            localizedBlockNormSeq_apply]
        _ ≤ ‖localizedBlockNormSeqInfty N hN x‖ :=
          lp.norm_apply_le_norm (p := (∞ : ℝ≥0∞))
            (f := localizedBlockNormSeqInfty N hN x) (i := j) (by simp)
    have hhalf :
        (1 / 2 : ℝ) * ‖x k‖ ≤
          ‖localizedBlockNormSeqInfty N hN x‖ :=
      hcoord.trans ((lp.norm_apply_le_norm (p := (∞ : ℝ≥0∞))
        (f := localizedBlockPiece (∞ : ℝ≥0∞) (∞ : ℝ≥0∞) N hN j x)
        (i := k) (by simp)).trans hpiece_to_seq)
    nlinarith

theorem hat_partition_sum
    (N : ℕ) (hN : 1 ≤ N) (k : ℤ) :
    ∑' j : ℤ, hat N j k = 1 := by
  let q : ℤ := k / (N : ℤ)
  calc
    ∑' j : ℤ, hat N j k =
        ∑ j ∈ ({q, q + 1} : Finset ℤ), hat N j k := by
      exact tsum_eq_sum (s := ({q, q + 1} : Finset ℤ)) (fun j hj => by
        have hj_ne : j ≠ q ∧ j ≠ q + 1 := by
          simpa using hj
        exact hat_eq_zero_of_not_adjacent N hN k j
          (by simpa [q] using hj_ne.1) (by simpa [q] using hj_ne.2))
    _ = hat N q k + hat N (q + 1) k :=
      Finset.sum_pair (by omega)
    _ = 1 := by
      rw [hat_left_partition_value N hN k, hat_right_partition_value N hN k]
      ring

theorem hat_sum_neighbor_one_eq_one
    (N : ℕ) (hN : 1 ≤ N) (j k : ℤ)
    (hj : hat N j k ≠ 0) :
    ∑ i ∈ Finset.Icc (j - 1) (j + 1), hat N i k = 1 := by
  calc
    ∑ i ∈ Finset.Icc (j - 1) (j + 1), hat N i k =
        ∑' i : ℤ, hat N i k := by
      exact (tsum_eq_sum
        (s := Finset.Icc (j - 1) (j + 1))
        (fun i hi => by
          by_contra hnonzero
          exact hi (hat_index_support_subset_neighbor_one N hN j k hj hnonzero))).symm
    _ = 1 := hat_partition_sum N hN k

theorem hat_sum_neighbor_two_shift_eq_one
    (N : ℕ) (hN : 1 ≤ N) (j k n : ℤ)
    (hj : hat N j (k + n) ≠ 0) :
    ∑ i ∈ Finset.Icc (j - n / (N : ℤ) - 2)
        (j - n / (N : ℤ) + 2), hat N i k = 1 := by
  calc
    ∑ i ∈ Finset.Icc (j - n / (N : ℤ) - 2)
        (j - n / (N : ℤ) + 2), hat N i k =
        ∑' i : ℤ, hat N i k := by
      exact (tsum_eq_sum
        (s := Finset.Icc (j - n / (N : ℤ) - 2)
          (j - n / (N : ℤ) + 2))
        (fun i hi => by
          by_contra hnonzero
          exact hi
            (shifted_hat_index_support_subset_neighbor_two_div
              N hN j k n hj hnonzero))).symm
    _ = 1 := hat_partition_sum N hN k

theorem localizedBlockPiece_sum_neighbor_one_apply
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (j k : ℤ) (x : ellp p)
    (hj : hat N j k ≠ 0) :
    ∑ i ∈ Finset.Icc (j - 1) (j + 1),
        localizedBlockPiece p r N hN i x k = x k := by
  let s : Finset ℤ := Finset.Icc (j - 1) (j + 1)
  calc
    ∑ i ∈ s, localizedBlockPiece p r N hN i x k =
        ∑ i ∈ s, (hat N i k : ℂ) * x k := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      rw [localizedBlockPiece_apply]
    _ = (∑ i ∈ s, (hat N i k : ℂ)) * x k := by
      rw [Finset.sum_mul]
    _ = x k := by
      have hsumC : (∑ i ∈ s, (hat N i k : ℂ)) = (1 : ℂ) := by
        exact_mod_cast hat_sum_neighbor_one_eq_one N hN j k hj
      rw [hsumC]
      simp

theorem localizedBlockPiece_sum_neighbor_two_shift_apply
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (j k n : ℤ) (x : ellp p)
    (hj : hat N j (k + n) ≠ 0) :
    ∑ i ∈ Finset.Icc (j - n / (N : ℤ) - 2)
        (j - n / (N : ℤ) + 2),
        localizedBlockPiece p r N hN i x k = x k := by
  let s : Finset ℤ :=
    Finset.Icc (j - n / (N : ℤ) - 2) (j - n / (N : ℤ) + 2)
  calc
    ∑ i ∈ s, localizedBlockPiece p r N hN i x k =
        ∑ i ∈ s, (hat N i k : ℂ) * x k := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      rw [localizedBlockPiece_apply]
    _ = (∑ i ∈ s, (hat N i k : ℂ)) * x k := by
      rw [Finset.sum_mul]
    _ = x k := by
      have hsumC : (∑ i ∈ s, (hat N i k : ℂ)) = (1 : ℂ) := by
        exact_mod_cast hat_sum_neighbor_two_shift_eq_one N hN j k n hj
      rw [hsumC]
      simp

theorem hat_tsum_rpow_le_one
    (N : ℕ) (hN : 1 ≤ N) {q : ℝ} (hq : 1 ≤ q) (k : ℤ) :
    (∑' j : ℤ, (hat N j k) ^ q) ≤ 1 := by
  let s : Finset ℤ := {k / (N : ℤ), k / (N : ℤ) + 1}
  have hq_pos : 0 < q := zero_lt_one.trans_le hq
  have hsum_rpow :
      (∑' j : ℤ, (hat N j k) ^ q) =
        ∑ j ∈ s, (hat N j k) ^ q := by
    exact tsum_eq_sum (s := s) (fun j hj => by
      have hj_ne : j ≠ k / (N : ℤ) ∧ j ≠ k / (N : ℤ) + 1 := by
        simpa [s] using hj
      rw [hat_eq_zero_of_not_adjacent N hN k j hj_ne.1 hj_ne.2]
      exact Real.zero_rpow hq_pos.ne')
  have hsum_hat :
      ∑ j ∈ s, hat N j k = 1 := by
    calc
      ∑ j ∈ s, hat N j k = ∑' j : ℤ, hat N j k := by
        exact (tsum_eq_sum (s := s) (fun j hj => by
          have hj_ne : j ≠ k / (N : ℤ) ∧ j ≠ k / (N : ℤ) + 1 := by
            simpa [s] using hj
          exact hat_eq_zero_of_not_adjacent N hN k j hj_ne.1 hj_ne.2)).symm
      _ = 1 := hat_partition_sum N hN k
  calc
    (∑' j : ℤ, (hat N j k) ^ q) =
        ∑ j ∈ s, (hat N j k) ^ q := hsum_rpow
    _ ≤ ∑ j ∈ s, hat N j k := by
      refine Finset.sum_le_sum ?_
      intro j _hj
      exact Real.rpow_le_self_of_le_one
        (hat_nonneg N j k) (hat_le_one N j k) hq
    _ = 1 := hsum_hat

theorem hat_finset_sum_rpow_le_one
    (N : ℕ) (hN : 1 ≤ N) {q : ℝ} (hq : 1 ≤ q)
    (s : Finset ℤ) (k : ℤ) :
    ∑ j ∈ s, (hat N j k) ^ q ≤ 1 := by
  have hq_pos : 0 < q := zero_lt_one.trans_le hq
  have hsumm : Summable fun j : ℤ => (hat N j k) ^ q := by
    refine summable_of_hasFiniteSupport ((hat_index_support_finite N hN k).subset ?_)
    intro j hj
    simp only [Function.support, ne_eq, Set.mem_setOf_eq] at hj ⊢
    contrapose! hj
    rw [hj]
    exact Real.zero_rpow hq_pos.ne'
  calc
    ∑ j ∈ s, (hat N j k) ^ q ≤
        ∑' j : ℤ, (hat N j k) ^ q :=
      Summable.sum_le_tsum s
        (fun j _hj => Real.rpow_nonneg (hat_nonneg N j k) q) hsumm
    _ ≤ 1 := hat_tsum_rpow_le_one N hN hq k

theorem one_le_two_rpow_mul_hat_tsum_rpow
    (N : ℕ) (hN : 1 ≤ N) {q : ℝ} (hq : 1 ≤ q) (k : ℤ) :
    1 ≤ (2 : ℝ) ^ q * (∑' j : ℤ, (hat N j k) ^ q) := by
  have hq_pos : 0 < q := zero_lt_one.trans_le hq
  rcases exists_hat_ge_half N hN k with ⟨j0, hj0⟩
  have hsingle_le : (hat N j0 k) ^ q ≤ ∑' j : ℤ, (hat N j k) ^ q := by
    have hsumm : Summable fun j : ℤ => (hat N j k) ^ q := by
      refine summable_of_hasFiniteSupport ((hat_index_support_finite N hN k).subset ?_)
      intro j hj
      simp only [Function.support, ne_eq, Set.mem_setOf_eq] at hj ⊢
      contrapose! hj
      rw [hj]
      exact Real.zero_rpow hq_pos.ne'
    calc
      (hat N j0 k) ^ q =
          ∑ j ∈ ({j0} : Finset ℤ), (hat N j k) ^ q := by simp
      _ ≤ ∑' j : ℤ, (hat N j k) ^ q :=
        Summable.sum_le_tsum ({j0} : Finset ℤ)
          (fun j _hj => Real.rpow_nonneg (hat_nonneg N j k) q) hsumm
  have hhalf_le : (1 / 2 : ℝ) ^ q ≤ ∑' j : ℤ, (hat N j k) ^ q :=
    (Real.rpow_le_rpow (by norm_num) hj0 hq_pos.le).trans hsingle_le
  have hmul : (2 : ℝ) ^ q * (1 / 2 : ℝ) ^ q = 1 := by
    calc
      (2 : ℝ) ^ q * (1 / 2 : ℝ) ^ q =
          ((2 : ℝ) * (1 / 2 : ℝ)) ^ q := by
        rw [Real.mul_rpow (by norm_num) (by norm_num)]
      _ = (1 : ℝ) ^ q := by norm_num
      _ = 1 := Real.one_rpow q
  calc
    1 = (2 : ℝ) ^ q * (1 / 2 : ℝ) ^ q := hmul.symm
    _ ≤ (2 : ℝ) ^ q * (∑' j : ℤ, (hat N j k) ^ q) := by
      exact mul_le_mul_of_nonneg_left hhalf_le (Real.rpow_nonneg (by norm_num) q)

theorem finite_sum_localizedBlockNormSeq_same_exponent_rpow_le_norm
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p ≠ ∞)
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) (s : Finset ℤ) :
    ∑ j ∈ s, ‖localizedBlockNormSeqC p p N hN x j‖ ^ p.toReal ≤
      ‖x‖ ^ p.toReal := by
  have hp_ne_zero : p ≠ 0 :=
    (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_top
  have hp_ge_one : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hp_top (Fact.out : (1 : ℝ≥0∞) ≤ p)
  let F : ℤ → ℝ := fun k =>
    ∑ j ∈ s, ‖localizedBlockPiece p p N hN j x k‖ ^ p.toReal
  have hsumm_j : ∀ j ∈ s,
      Summable fun k : ℤ =>
        ‖localizedBlockPiece p p N hN j x k‖ ^ p.toReal := by
    intro j _hj
    exact (lp.memℓp (localizedBlockPiece p p N hN j x)).summable hp_pos
  have hF_nonneg : ∀ k : ℤ, 0 ≤ F k := by
    intro k
    exact Finset.sum_nonneg fun _j _hj =>
      Real.rpow_nonneg (norm_nonneg _) _
  have hpartial : ∀ t : Finset ℤ, ∑ k ∈ t, F k ≤ ‖x‖ ^ p.toReal := by
    intro t
    calc
      ∑ k ∈ t, F k =
          ∑ k ∈ t, ∑ j ∈ s,
            (hat N j k) ^ p.toReal * ‖x k‖ ^ p.toReal := by
        refine Finset.sum_congr rfl ?_
        intro k _hk
        simp only [F]
        refine Finset.sum_congr rfl ?_
        intro j _hj
        exact localizedBlockPiece_apply_norm_rpow p p N hN j x p.toReal k
      _ = ∑ k ∈ t, ‖x k‖ ^ p.toReal *
            ∑ j ∈ s, (hat N j k) ^ p.toReal := by
        refine Finset.sum_congr rfl ?_
        intro k _hk
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      _ ≤ ∑ k ∈ t, ‖x k‖ ^ p.toReal := by
        refine Finset.sum_le_sum ?_
        intro k _hk
        have hhat := hat_finset_sum_rpow_le_one N hN hp_ge_one s k
        have hx_nonneg : 0 ≤ ‖x k‖ ^ p.toReal :=
          Real.rpow_nonneg (norm_nonneg _) _
        calc
          ‖x k‖ ^ p.toReal * ∑ j ∈ s, (hat N j k) ^ p.toReal ≤
              ‖x k‖ ^ p.toReal * 1 :=
            mul_le_mul_of_nonneg_left hhat hx_nonneg
          _ = ‖x k‖ ^ p.toReal := mul_one _
      _ ≤ ‖x‖ ^ p.toReal := lp.sum_rpow_le_norm_rpow hp_pos x t
  calc
    ∑ j ∈ s, ‖localizedBlockNormSeqC p p N hN x j‖ ^ p.toReal =
        ∑ j ∈ s, ∑' k : ℤ,
          ‖localizedBlockPiece p p N hN j x k‖ ^ p.toReal := by
      refine Finset.sum_congr rfl ?_
      intro j _hj
      rw [localizedBlockNormSeqC_norm, localizedBlockNormSeq_apply]
      exact lp.norm_rpow_eq_tsum hp_pos (localizedBlockPiece p p N hN j x)
    _ = ∑' k : ℤ, F k := by
      exact (Summable.tsum_finsetSum (s := s)
        (f := fun j k : ℤ =>
          ‖localizedBlockPiece p p N hN j x k‖ ^ p.toReal)
        hsumm_j).symm
    _ ≤ ‖x‖ ^ p.toReal := Real.tsum_le_of_sum_le hF_nonneg hpartial

noncomputable def localizedBlockNormSeqSelf
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) : ellp p := by
  by_cases hp_top : p = ∞
  · subst p
    exact localizedBlockNormSeqInfty N hN x
  · have hp_ne_zero : p ≠ 0 :=
      (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
    have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_top
    have hpartial : ∀ s : Finset ℤ,
        ∑ j ∈ s, ‖localizedBlockNormSeqC p p N hN x j‖ ^ p.toReal ≤
          ‖x‖ ^ p.toReal :=
      finite_sum_localizedBlockNormSeq_same_exponent_rpow_le_norm
        p hp_top N hN x
    have hsumm : Summable fun j : ℤ =>
        ‖localizedBlockNormSeqC p p N hN x j‖ ^ p.toReal :=
      summable_of_sum_le
        (fun _j => Real.rpow_nonneg (norm_nonneg _) _) hpartial
    exact ⟨localizedBlockNormSeqC p p N hN x, memℓp_gen hsumm⟩

theorem localizedBlockNormSeqSelf_apply
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) (j : ℤ) :
    localizedBlockNormSeqSelf p N hN x j =
      localizedBlockNormSeqC p p N hN x j := by
  unfold localizedBlockNormSeqSelf
  by_cases hp_top : p = ∞
  · subst p
    rfl
  · simp [hp_top]

theorem localizedBlockNormSeqSelf_norm_le
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) :
    ‖localizedBlockNormSeqSelf p N hN x‖ ≤ ‖x‖ := by
  by_cases hp_top : p = ∞
  · subst p
    unfold localizedBlockNormSeqSelf
    simpa using localizedBlockNormSeqInfty_norm_le N hN x
  · have hp_ne_zero : p ≠ 0 :=
      (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
    have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_top
    have htsum_le :
        ∑' j : ℤ, ‖localizedBlockNormSeqSelf p N hN x j‖ ^ p.toReal ≤
          ‖x‖ ^ p.toReal := by
      refine Real.tsum_le_of_sum_le
        (fun j => Real.rpow_nonneg (norm_nonneg _) _) ?_
      intro s
      calc
        ∑ j ∈ s, ‖localizedBlockNormSeqSelf p N hN x j‖ ^ p.toReal =
            ∑ j ∈ s, ‖localizedBlockNormSeqC p p N hN x j‖ ^ p.toReal := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          rw [localizedBlockNormSeqSelf_apply]
        _ ≤ ‖x‖ ^ p.toReal :=
          finite_sum_localizedBlockNormSeq_same_exponent_rpow_le_norm
            p hp_top N hN x s
    exact lp.norm_le_of_tsum_le hp_pos (norm_nonneg x) htsum_le

theorem norm_le_two_mul_localizedBlockNormSeqSelf_norm
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) :
    ‖x‖ ≤ 2 * ‖localizedBlockNormSeqSelf p N hN x‖ := by
  by_cases hp_top : p = ∞
  · subst p
    unfold localizedBlockNormSeqSelf
    simpa using norm_le_two_mul_localizedBlockNormSeqInfty_norm N hN x
  · have hp_ne_zero : p ≠ 0 :=
      (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
    have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_top
    have hp_ge_one : 1 ≤ p.toReal := by
      simpa using ENNReal.toReal_mono hp_top (Fact.out : (1 : ℝ≥0∞) ≤ p)
    let G : ℤ → ℤ → ℝ := fun j k =>
      ‖localizedBlockPiece p p N hN j x k‖ ^ p.toReal
    have hsumm_k : ∀ k : ℤ, Summable fun j : ℤ => G j k := by
      intro k
      refine summable_of_hasFiniteSupport ((hat_index_support_finite N hN k).subset ?_)
      intro j hj
      simp only [Function.support, ne_eq, Set.mem_setOf_eq] at hj ⊢
      contrapose! hj
      have hzero : localizedBlockPiece p p N hN j x k = 0 := by
        rw [localizedBlockPiece_apply, hj]
        simp
      simp [G, hzero, Real.zero_rpow hp_pos.ne']
    have hsumm_j : ∀ j : ℤ, Summable fun k : ℤ => G j k := by
      intro j
      exact (lp.memℓp (localizedBlockPiece p p N hN j x)).summable hp_pos
    have hcoord : ∀ k : ℤ,
        ‖x k‖ ^ p.toReal ≤ (2 : ℝ) ^ p.toReal * (∑' j : ℤ, G j k) := by
      intro k
      have hmass := one_le_two_rpow_mul_hat_tsum_rpow N hN hp_ge_one k
      have hx_nonneg : 0 ≤ ‖x k‖ ^ p.toReal :=
        Real.rpow_nonneg (norm_nonneg _) _
      have hG_tsum :
          (∑' j : ℤ, G j k) =
            (∑' j : ℤ, (hat N j k) ^ p.toReal) * ‖x k‖ ^ p.toReal := by
        calc
          (∑' j : ℤ, G j k) =
              ∑' j : ℤ, (hat N j k) ^ p.toReal * ‖x k‖ ^ p.toReal := by
            apply tsum_congr
            intro j
            exact localizedBlockPiece_apply_norm_rpow p p N hN j x p.toReal k
          _ = (∑' j : ℤ, (hat N j k) ^ p.toReal) * ‖x k‖ ^ p.toReal := by
            rw [tsum_mul_right]
      calc
        ‖x k‖ ^ p.toReal = 1 * ‖x k‖ ^ p.toReal := by ring
        _ ≤ ((2 : ℝ) ^ p.toReal *
              (∑' j : ℤ, (hat N j k) ^ p.toReal)) * ‖x k‖ ^ p.toReal := by
          exact mul_le_mul_of_nonneg_right hmass hx_nonneg
        _ = (2 : ℝ) ^ p.toReal *
              ((∑' j : ℤ, (hat N j k) ^ p.toReal) * ‖x k‖ ^ p.toReal) := by
          ring
        _ = (2 : ℝ) ^ p.toReal * (∑' j : ℤ, G j k) := by
          rw [hG_tsum]
    refine lp.norm_le_of_forall_sum_le hp_pos
      (by positivity : 0 ≤ 2 * ‖localizedBlockNormSeqSelf p N hN x‖) ?_
    intro t
    have hfinite_tsum_le :
        (∑' j : ℤ, ∑ k ∈ t, G j k) ≤
          ∑' j : ℤ, ‖localizedBlockNormSeqSelf p N hN x j‖ ^ p.toReal := by
      refine Real.tsum_le_of_sum_le
        (fun j => Finset.sum_nonneg fun k _hk =>
          Real.rpow_nonneg (norm_nonneg _) _) ?_
      intro s
      calc
        ∑ j ∈ s, ∑ k ∈ t, G j k ≤
            ∑ j ∈ s, ‖localizedBlockNormSeqSelf p N hN x j‖ ^ p.toReal := by
          refine Finset.sum_le_sum ?_
          intro j _hj
          calc
            ∑ k ∈ t, G j k ≤ ∑' k : ℤ, G j k :=
              Summable.sum_le_tsum t
                (fun k _hk => Real.rpow_nonneg (norm_nonneg _) _) (hsumm_j j)
            _ = ‖localizedBlockPiece p p N hN j x‖ ^ p.toReal := by
              exact (lp.norm_rpow_eq_tsum hp_pos
                (localizedBlockPiece p p N hN j x)).symm
            _ = ‖localizedBlockNormSeqC p p N hN x j‖ ^ p.toReal := by
              rw [localizedBlockNormSeqC_norm, localizedBlockNormSeq_apply]
            _ = ‖localizedBlockNormSeqSelf p N hN x j‖ ^ p.toReal := by
              rw [localizedBlockNormSeqSelf_apply]
        _ ≤ ∑' j : ℤ,
            ‖localizedBlockNormSeqSelf p N hN x j‖ ^ p.toReal :=
          Summable.sum_le_tsum s
            (fun j _hj => Real.rpow_nonneg (norm_nonneg _) _)
            ((lp.memℓp (localizedBlockNormSeqSelf p N hN x)).summable hp_pos)
    calc
      ∑ k ∈ t, ‖x k‖ ^ p.toReal ≤
          ∑ k ∈ t, (2 : ℝ) ^ p.toReal * (∑' j : ℤ, G j k) := by
        exact Finset.sum_le_sum fun k _hk => hcoord k
      _ = (2 : ℝ) ^ p.toReal * ∑ k ∈ t, (∑' j : ℤ, G j k) := by
        rw [Finset.mul_sum]
      _ = (2 : ℝ) ^ p.toReal * (∑' j : ℤ, ∑ k ∈ t, G j k) := by
        congr 1
        exact (Summable.tsum_finsetSum (s := t)
          (f := fun k j : ℤ => G j k)
          (fun k _hk => hsumm_k k)).symm
      _ ≤ (2 : ℝ) ^ p.toReal *
            (∑' j : ℤ, ‖localizedBlockNormSeqSelf p N hN x j‖ ^ p.toReal) := by
        exact mul_le_mul_of_nonneg_left hfinite_tsum_le
          (Real.rpow_nonneg (by norm_num) p.toReal)
      _ = (2 : ℝ) ^ p.toReal * ‖localizedBlockNormSeqSelf p N hN x‖ ^ p.toReal := by
        rw [lp.norm_rpow_eq_tsum hp_pos]
      _ = (2 * ‖localizedBlockNormSeqSelf p N hN x‖) ^ p.toReal := by
        rw [Real.mul_rpow (by norm_num) (norm_nonneg _)]

theorem localizedBlockNormSeqSelf_equiv_norm
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧
      ∀ x : ellp p,
        α * ‖x‖ ≤ ‖localizedBlockNormSeqSelf p N hN x‖ ∧
          ‖localizedBlockNormSeqSelf p N hN x‖ ≤ β * ‖x‖ := by
  refine ⟨1 / 2, 1, by norm_num, by norm_num, ?_⟩
  intro x
  constructor
  · have h := norm_le_two_mul_localizedBlockNormSeqSelf_norm p N hN x
    nlinarith [norm_nonneg (localizedBlockNormSeqSelf p N hN x), norm_nonneg x]
  · simpa using localizedBlockNormSeqSelf_norm_le p N hN x

theorem hat_partition_properties
    (N : ℕ) (hN : 1 ≤ N) :
    (∀ j k : ℤ, 0 ≤ hat N j k ∧ hat N j k ≤ 1) ∧
      (∀ k : ℤ, ∑' j : ℤ, hat N j k = 1) ∧
        (∀ j k l : ℤ,
          |hat N j k - hat N j l| ≤
            min 1 (|((k - l : ℤ) : ℝ)| / (N : ℝ))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j k
    exact ⟨hat_nonneg N j k, hat_le_one N j k⟩
  · exact hat_partition_sum N hN
  · intro j k l
    exact hat_lipschitz N hN j k l

theorem hatMultiplier_partition_apply
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) (k : ℤ) :
    tsum (fun j : ℤ => (hatMultiplier p N j x) k) = x k := by
  let q : ℤ := k / (N : ℤ)
  calc
    tsum (fun j : ℤ => (hatMultiplier p N j x) k) =
        ∑ j ∈ ({q, q + 1} : Finset ℤ), (hatMultiplier p N j x) k := by
      exact tsum_eq_sum (s := ({q, q + 1} : Finset ℤ)) (fun j hj => by
        have hj_ne : j ≠ q ∧ j ≠ q + 1 := by
          simpa using hj
        have hzero : hat N j k = 0 :=
          hat_eq_zero_of_not_adjacent N hN k j
            (by simpa [q] using hj_ne.1) (by simpa [q] using hj_ne.2)
        rw [hatMultiplier_apply, hzero]
        simp)
    _ = (hatMultiplier p N q x) k + (hatMultiplier p N (q + 1) x) k :=
      Finset.sum_pair (by omega)
    _ = x k := by
      rw [hatMultiplier_apply, hatMultiplier_apply]
      rw [hat_left_partition_value N hN k, hat_right_partition_value N hN k]
      rw [← add_mul]
      norm_num [Complex.ofReal_div]

noncomputable def ellInfinityOfEllOne
    (x : ellp (1 : ℝ≥0∞)) : ellp (∞ : ℝ≥0∞) :=
  ⟨fun k : ℤ => x k, by
    apply memℓp_infty
    refine ⟨‖x‖, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact lp.norm_apply_le_norm (p := (1 : ℝ≥0∞)) (f := x) (i := k) (by norm_num)⟩

theorem ellInfinityOfEllOne_apply
    (x : ellp (1 : ℝ≥0∞)) (k : ℤ) :
    ellInfinityOfEllOne x k = x k :=
  rfl

theorem ellInfinityOfEllOne_norm_le
    (x : ellp (1 : ℝ≥0∞)) :
    ‖ellInfinityOfEllOne x‖ ≤ ‖x‖ := by
  rw [lp.norm_eq_ciSup]
  exact ciSup_le fun k => by
    change ‖x k‖ ≤ ‖x‖
    exact lp.norm_apply_le_norm (p := (1 : ℝ≥0∞)) (f := x) (i := k) (by norm_num)

theorem ellInfinityOfEllOne_hatMultiplier
    (N : ℕ) (j : ℤ) (x : ellp (1 : ℝ≥0∞)) :
    ellInfinityOfEllOne (hatMultiplier (1 : ℝ≥0∞) N j x) =
      hatMultiplier (∞ : ℝ≥0∞) N j (ellInfinityOfEllOne x) := by
  ext k
  simp [ellInfinityOfEllOne_apply, hatMultiplier_apply]

theorem hatMultiplier_one_to_infinity_norm_le
    (N : ℕ) (j : ℤ) (x : ellp (1 : ℝ≥0∞)) :
    ‖ellInfinityOfEllOne (hatMultiplier (1 : ℝ≥0∞) N j x)‖ ≤ ‖x‖ := by
  calc
    ‖ellInfinityOfEllOne (hatMultiplier (1 : ℝ≥0∞) N j x)‖ ≤
        ‖hatMultiplier (1 : ℝ≥0∞) N j x‖ :=
      ellInfinityOfEllOne_norm_le _
    _ ≤ ‖hatMultiplier (1 : ℝ≥0∞) N j‖ * ‖x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖x‖ := by
      exact mul_le_mul_of_nonneg_right
          (hatMultiplier_norm_le (1 : ℝ≥0∞) N j) (norm_nonneg x)
    _ = ‖x‖ := one_mul _

noncomputable def ellInfinityOfEllp
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (x : ellp p) : ellp (∞ : ℝ≥0∞) :=
  ⟨fun k : ℤ => x k, by
    apply memℓp_infty
    refine ⟨‖x‖, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact lp.norm_apply_le_norm (p := p) (f := x) (i := k)
      (by exact (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne')⟩

theorem ellInfinityOfEllp_apply
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (x : ellp p) (k : ℤ) :
    ellInfinityOfEllp p x k = x k := by
  rfl

theorem ellInfinityOfEllp_norm_le
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (x : ellp p) :
    ‖ellInfinityOfEllp p x‖ ≤ ‖x‖ := by
  rw [lp.norm_eq_ciSup]
  exact ciSup_le fun k => by
    change ‖x k‖ ≤ ‖x‖
    exact lp.norm_apply_le_norm (p := p) (f := x) (i := k)
      (by exact (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne')

noncomputable def ellpOfEllOne
    (r : ℝ≥0∞) [Fact (1 ≤ r)] (x : ellp (1 : ℝ≥0∞)) : ellp r :=
  lp.linearMapOfLE ℂ (fun _ : ℤ => ℂ) Fact.out x

theorem ellpOfEllOne_apply
    (r : ℝ≥0∞) [Fact (1 ≤ r)] (x : ellp (1 : ℝ≥0∞)) (k : ℤ) :
    ellpOfEllOne r x k = x k := by
  rfl

theorem ellpOfEllOne_one
    (x : ellp (1 : ℝ≥0∞)) :
    ellpOfEllOne (1 : ℝ≥0∞) x = x := by
  ext k
  rfl

lemma finset_sum_rpow_le_rpow_sum_of_nonneg
    {ι : Type*} (s : Finset ι) (f : ι → ℝ) {p : ℝ}
    (hp : 1 ≤ p) (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∑ i ∈ s, f i ^ p) ≤ (∑ i ∈ s, f i) ^ p := by
  classical
  revert hf
  refine Finset.induction_on s ?base ?step
  · intro _hf
    have hp_pos : 0 < p := zero_lt_one.trans_le hp
    simp [Real.zero_rpow hp_pos.ne']
  · intro a s ha ih hf
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hfs : 0 ≤ ∑ i ∈ s, f i := by
      exact Finset.sum_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have ih' : (∑ i ∈ s, f i ^ p) ≤ (∑ i ∈ s, f i) ^ p := by
      exact ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    calc
      f a ^ p + ∑ i ∈ s, f i ^ p ≤
          f a ^ p + (∑ i ∈ s, f i) ^ p := by
        exact add_le_add_right ih' _
      _ ≤ (f a + ∑ i ∈ s, f i) ^ p :=
        Real.add_rpow_le_rpow_add hfa hfs hp

theorem ellpOfEllOne_norm_le
    (r : ℝ≥0∞) [Fact (1 ≤ r)] (x : ellp (1 : ℝ≥0∞)) :
    ‖ellpOfEllOne r x‖ ≤ ‖x‖ := by
  by_cases hr_top : r = ∞
  · subst r
    have h_eq : ellpOfEllOne (∞ : ℝ≥0∞) x = ellInfinityOfEllOne x := by
      ext k
      rfl
    rw [h_eq]
    exact ellInfinityOfEllOne_norm_le x
  · have hr_ne_zero : r ≠ 0 := by
      exact (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ r)).ne'
    have hr_pos : 0 < r.toReal := ENNReal.toReal_pos hr_ne_zero hr_top
    have hr_ge_one : 1 ≤ r.toReal := by
      simpa using ENNReal.toReal_mono hr_top (Fact.out : (1 : ℝ≥0∞) ≤ r)
    refine lp.norm_le_of_forall_sum_le (E := fun _ : ℤ => ℂ) (p := r)
      hr_pos (norm_nonneg x) ?_
    intro s
    have hs_norm_sum_nonneg : 0 ≤ ∑ i ∈ s, ‖x i‖ := by
      exact Finset.sum_nonneg fun i _hi => norm_nonneg (x i)
    calc
      ∑ i ∈ s, ‖ellpOfEllOne r x i‖ ^ r.toReal =
          ∑ i ∈ s, ‖x i‖ ^ r.toReal := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        simp [ellpOfEllOne_apply]
      _ ≤ (∑ i ∈ s, ‖x i‖) ^ r.toReal :=
        finset_sum_rpow_le_rpow_sum_of_nonneg s (fun i => ‖x i‖)
          hr_ge_one (fun i _hi => norm_nonneg (x i))
      _ ≤ ‖x‖ ^ r.toReal := by
        have hsum_le_norm : ∑ i ∈ s, ‖x i‖ ≤ ‖x‖ := by
          have h := lp.sum_rpow_le_norm_rpow (p := (1 : ℝ≥0∞))
            (f := x) (s := s) (by norm_num)
          simpa using h
        exact Real.rpow_le_rpow hs_norm_sum_nonneg hsum_le_norm hr_pos.le

noncomputable def ellOneOfFiniteSupportInfinity
    (x : ellp (∞ : ℝ≥0∞))
    (h_support : {k : ℤ | x k ≠ 0}.Finite) : ellp (1 : ℝ≥0∞) :=
  ⟨fun k : ℤ => x k, by
    have hsupp_norm : Function.HasFiniteSupport (fun k : ℤ => ‖x k‖) := by
      exact h_support.subset (by
        intro k hk
        simp only [Function.support, ne_eq, Set.mem_setOf_eq] at hk ⊢
        exact norm_ne_zero_iff.mp hk)
    have hsumm : Summable fun k : ℤ => ‖x k‖ :=
      summable_of_hasFiniteSupport hsupp_norm
    apply memℓp_gen
    simpa using hsumm⟩

theorem ellInfinity_tsum_norm_le_ncard_mul_norm
    (x : ellp (∞ : ℝ≥0∞))
    (h_support : {k : ℤ | x k ≠ 0}.Finite) :
    (∑' k : ℤ, ‖x k‖) ≤ ({k : ℤ | x k ≠ 0}.ncard : ℝ) * ‖x‖ := by
  classical
  let s : Finset ℤ := h_support.toFinset
  have hs_support : ∀ k : ℤ, k ∉ s → ‖x k‖ = 0 := by
    intro k hk
    have hk_not : k ∉ ({k : ℤ | x k ≠ 0} : Set ℤ) := by
      simpa [s] using hk
    simp at hk_not
    simp [hk_not]
  have hs_card : s.card = {k : ℤ | x k ≠ 0}.ncard := by
    simp [s, Set.ncard_eq_toFinset_card _ h_support]
  calc
    (∑' k : ℤ, ‖x k‖) = ∑ k ∈ s, ‖x k‖ := tsum_eq_sum hs_support
    _ ≤ ∑ _k ∈ s, ‖x‖ := by
      refine Finset.sum_le_sum ?_
      intro k _hk
      exact lp.norm_apply_le_norm (p := (∞ : ℝ≥0∞)) (f := x) (i := k) (by simp)
    _ = (s.card : ℝ) * ‖x‖ := by simp
    _ = ({k : ℤ | x k ≠ 0}.ncard : ℝ) * ‖x‖ := by rw [hs_card]

theorem ellOneOfFiniteSupportInfinity_norm_le
    (x : ellp (∞ : ℝ≥0∞))
    (h_support : {k : ℤ | x k ≠ 0}.Finite) :
    ‖ellOneOfFiniteSupportInfinity x h_support‖ ≤
      ({k : ℤ | x k ≠ 0}.ncard : ℝ) * ‖x‖ := by
  rw [lp.norm_eq_tsum_rpow]
  · norm_num
    change (∑' i : ℤ, ‖x i‖) ≤ ({k : ℤ | x k ≠ 0}.ncard : ℝ) * ‖x‖
    exact ellInfinity_tsum_norm_le_ncard_mul_norm x h_support
  · norm_num

theorem ellp_norm_le_of_finite_support
    (x : ellp (∞ : ℝ≥0∞)) (L : ℕ)
    (h_support : {k : ℤ | x k ≠ 0}.Finite)
    (h_card : {k : ℤ | x k ≠ 0}.ncard ≤ L) :
    ‖ellOneOfFiniteSupportInfinity x h_support‖ ≤ (L : ℝ) * ‖x‖ := by
  calc
    ‖ellOneOfFiniteSupportInfinity x h_support‖ ≤
        ({k : ℤ | x k ≠ 0}.ncard : ℝ) * ‖x‖ :=
      ellOneOfFiniteSupportInfinity_norm_le x h_support
    _ ≤ (L : ℝ) * ‖x‖ := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast h_card) (norm_nonneg x)

noncomputable def ellpOfFiniteSupport
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (x : ellp p) (h_support : {k : ℤ | x k ≠ 0}.Finite) : ellp r :=
  ⟨fun k : ℤ => x k, by
    exact (memℓp_zero h_support).of_exponent_ge (zero_le : (0 : ℝ≥0∞) ≤ r)⟩

theorem ellpOfFiniteSupport_apply
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (x : ellp p) (h_support : {k : ℤ | x k ≠ 0}.Finite) (k : ℤ) :
    ellpOfFiniteSupport p r x h_support k = x k := by
  rfl

theorem ellpOfFiniteSupport_norm_le_card_mul_norm
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (x : ellp p) (h_support : {k : ℤ | x k ≠ 0}.Finite) (L : ℕ)
    (h_card : {k : ℤ | x k ≠ 0}.ncard ≤ L) :
    ‖ellpOfFiniteSupport p r x h_support‖ ≤ (L : ℝ) * ‖x‖ := by
  let xInf : ellp (∞ : ℝ≥0∞) := ellInfinityOfEllp p x
  have hsupportInf : {k : ℤ | xInf k ≠ 0}.Finite := by
    simpa [xInf, ellInfinityOfEllp_apply] using h_support
  have hcardInf : {k : ℤ | xInf k ≠ 0}.ncard ≤ L := by
    simpa [xInf, ellInfinityOfEllp_apply] using h_card
  have h_eq :
      ellpOfFiniteSupport p r x h_support =
        ellpOfEllOne r (ellOneOfFiniteSupportInfinity xInf hsupportInf) := by
    ext k
    rfl
  rw [h_eq]
  calc
    ‖ellpOfEllOne r (ellOneOfFiniteSupportInfinity xInf hsupportInf)‖ ≤
        ‖ellOneOfFiniteSupportInfinity xInf hsupportInf‖ :=
      ellpOfEllOne_norm_le r _
    _ ≤ (L : ℝ) * ‖xInf‖ :=
      ellp_norm_le_of_finite_support xInf L hsupportInf hcardInf
    _ ≤ (L : ℝ) * ‖x‖ := by
      exact mul_le_mul_of_nonneg_left (ellInfinityOfEllp_norm_le p x)
        (Nat.cast_nonneg L)

theorem localizedBlockPiece_eq_ellpOfFiniteSupport
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) (x : ellp p) :
    localizedBlockPiece p r N hN j x =
      ellpOfFiniteSupport p r (hatMultiplier p N j x)
        (hatMultiplier_support_finite p N hN j x) := by
  ext k
  rfl

theorem localizedBlockPiece_norm_le_card_mul_self_norm
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) (x : ellp p) :
    ‖localizedBlockPiece p r N hN j x‖ ≤
      ((2 * N + 1 : ℕ) : ℝ) *
        ‖localizedBlockPiece p p N hN j x‖ := by
  rw [localizedBlockPiece_eq_ellpOfFiniteSupport,
    localizedBlockPiece_eq_hatMultiplier]
  exact ellpOfFiniteSupport_norm_le_card_mul_norm p r
    (hatMultiplier p N j x)
    (hatMultiplier_support_finite p N hN j x)
    (2 * N + 1)
    (hatMultiplier_support_ncard_le p N hN j x)

theorem localizedBlockNormSeqC_norm_le_card_mul_self_norm
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) (j : ℤ) :
    ‖localizedBlockNormSeqC p r N hN x j‖ ≤
      ((2 * N + 1 : ℕ) : ℝ) *
        ‖localizedBlockNormSeqSelf p N hN x j‖ := by
  rw [localizedBlockNormSeqC_norm, localizedBlockNormSeq_apply,
    localizedBlockNormSeqSelf_apply, localizedBlockNormSeqC_norm,
    localizedBlockNormSeq_apply]
  exact localizedBlockPiece_norm_le_card_mul_self_norm p r N hN j x

theorem hatMultiplier_infinity_to_one_norm_le
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ)
    (x : ellp (∞ : ℝ≥0∞)) :
    ‖ellOneOfFiniteSupportInfinity (hatMultiplier (∞ : ℝ≥0∞) N j x)
        (hatMultiplier_support_finite (∞ : ℝ≥0∞) N hN j x)‖ ≤
      ((2 * N + 1 : ℕ) : ℝ) * ‖x‖ := by
  let y : ellp (∞ : ℝ≥0∞) := hatMultiplier (∞ : ℝ≥0∞) N j x
  have hsupport : {k : ℤ | y k ≠ 0}.Finite := by
    simpa [y] using hatMultiplier_support_finite (∞ : ℝ≥0∞) N hN j x
  have hcard : {k : ℤ | y k ≠ 0}.ncard ≤ 2 * N + 1 := by
    simpa [y] using hatMultiplier_support_ncard_le (∞ : ℝ≥0∞) N hN j x
  have hy_one :
      ‖ellOneOfFiniteSupportInfinity y hsupport‖ ≤
        ((2 * N + 1 : ℕ) : ℝ) * ‖y‖ :=
    ellp_norm_le_of_finite_support y (2 * N + 1) hsupport hcard
  have hy_norm : ‖y‖ ≤ ‖x‖ := by
    calc
      ‖y‖ = ‖hatMultiplier (∞ : ℝ≥0∞) N j x‖ := rfl
      _ ≤ ‖hatMultiplier (∞ : ℝ≥0∞) N j‖ * ‖x‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖x‖ := by
        exact mul_le_mul_of_nonneg_right
          (hatMultiplier_norm_le (∞ : ℝ≥0∞) N j) (norm_nonneg x)
      _ = ‖x‖ := one_mul _
  calc
    ‖ellOneOfFiniteSupportInfinity (hatMultiplier (∞ : ℝ≥0∞) N j x)
        (hatMultiplier_support_finite (∞ : ℝ≥0∞) N hN j x)‖ =
        ‖ellOneOfFiniteSupportInfinity y hsupport‖ := by
      congr
    _ ≤ ((2 * N + 1 : ℕ) : ℝ) * ‖y‖ := hy_one
    _ ≤ ((2 * N + 1 : ℕ) : ℝ) * ‖x‖ := by
      exact mul_le_mul_of_nonneg_left hy_norm (by positivity)

theorem localizedBlockPiece_infty_one_eq_ellOneOfFiniteSupportInfinity
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ)
    (x : ellp (∞ : ℝ≥0∞)) :
    localizedBlockPiece (∞ : ℝ≥0∞) (1 : ℝ≥0∞) N hN j x =
      ellOneOfFiniteSupportInfinity (hatMultiplier (∞ : ℝ≥0∞) N j x)
        (hatMultiplier_support_finite (∞ : ℝ≥0∞) N hN j x) := by
  ext k
  rfl

theorem localizedBlockPiece_infty_eq_ellpOfEllOne
    (r : ℝ≥0∞) [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ)
    (x : ellp (∞ : ℝ≥0∞)) :
    localizedBlockPiece (∞ : ℝ≥0∞) r N hN j x =
      ellpOfEllOne r
        (ellOneOfFiniteSupportInfinity (hatMultiplier (∞ : ℝ≥0∞) N j x)
          (hatMultiplier_support_finite (∞ : ℝ≥0∞) N hN j x)) := by
  ext k
  rfl

theorem localizedBlockPiece_infty_inner_eq_ellInfinityOfEllp
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) (x : ellp p) :
    localizedBlockPiece p (∞ : ℝ≥0∞) N hN j x =
      ellInfinityOfEllp p (hatMultiplier p N j x) := by
  ext k
  rfl

theorem localizedBlockPiece_infty_inner_norm_le
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) (x : ellp p) :
    ‖localizedBlockPiece p (∞ : ℝ≥0∞) N hN j x‖ ≤ ‖x‖ := by
  rw [localizedBlockPiece_infty_inner_eq_ellInfinityOfEllp]
  calc
    ‖ellInfinityOfEllp p (hatMultiplier p N j x)‖ ≤
        ‖hatMultiplier p N j x‖ :=
      ellInfinityOfEllp_norm_le p _
    _ ≤ ‖hatMultiplier p N j‖ * ‖x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖x‖ := by
      exact mul_le_mul_of_nonneg_right
        (hatMultiplier_norm_le p N j) (norm_nonneg x)
    _ = ‖x‖ := one_mul _

theorem localizedBlockPiece_eq_ellpOfEllOne_of_infty_inner
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) (x : ellp p) :
    localizedBlockPiece p r N hN j x =
      ellpOfEllOne r
        (ellOneOfFiniteSupportInfinity (localizedBlockPiece p (∞ : ℝ≥0∞) N hN j x)
          (localizedBlockPiece_support_finite p (∞ : ℝ≥0∞) N hN j x)) := by
  ext k
  rfl

theorem localizedBlockPiece_norm_le_card_mul_norm
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) (x : ellp p) :
    ‖localizedBlockPiece p r N hN j x‖ ≤
      ((2 * N + 1 : ℕ) : ℝ) * ‖x‖ := by
  rw [localizedBlockPiece_eq_ellpOfFiniteSupport]
  let y : ellp p := hatMultiplier p N j x
  have hsupport : {k : ℤ | y k ≠ 0}.Finite := by
    simpa [y] using hatMultiplier_support_finite p N hN j x
  have hcard : {k : ℤ | y k ≠ 0}.ncard ≤ 2 * N + 1 := by
    simpa [y] using hatMultiplier_support_ncard_le p N hN j x
  calc
    ‖ellpOfFiniteSupport p r (hatMultiplier p N j x)
        (hatMultiplier_support_finite p N hN j x)‖ ≤
        ((2 * N + 1 : ℕ) : ℝ) * ‖y‖ :=
      ellpOfFiniteSupport_norm_le_card_mul_norm p r y hsupport (2 * N + 1) hcard
    _ ≤ ((2 * N + 1 : ℕ) : ℝ) * ‖x‖ := by
      exact mul_le_mul_of_nonneg_left
        (by
          calc
            ‖y‖ = ‖hatMultiplier p N j x‖ := rfl
            _ ≤ ‖hatMultiplier p N j‖ * ‖x‖ :=
              ContinuousLinearMap.le_opNorm _ _
            _ ≤ 1 * ‖x‖ := by
              exact mul_le_mul_of_nonneg_right
                (hatMultiplier_norm_le p N j) (norm_nonneg x)
            _ = ‖x‖ := one_mul _)
        (by positivity)

theorem shiftedLocalizedBlockPiece_norm_le_card_mul_norm
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (j n : ℤ) (x : ellp p) :
    ‖shiftedLocalizedBlockPiece p r N hN j n x‖ ≤
      ((2 * N + 1 : ℕ) : ℝ) * ‖x‖ := by
  rw [shiftedLocalizedBlockPiece_norm_eq]
  calc
    ‖localizedBlockPiece p r N hN j (shiftOperator p n x)‖ ≤
        ((2 * N + 1 : ℕ) : ℝ) * ‖shiftOperator p n x‖ :=
      localizedBlockPiece_norm_le_card_mul_norm p r N hN j (shiftOperator p n x)
    _ = ((2 * N + 1 : ℕ) : ℝ) * ‖x‖ := by
      rw [ellp_shift_isometry]

theorem localizedMultiplierDifferenceBlock_norm_le_two_card_mul_norm
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (j n : ℤ) (x : ellp p) :
    ‖localizedMultiplierDifferenceBlock p r N hN j n x‖ ≤
      (2 * ((2 * N + 1 : ℕ) : ℝ)) * ‖x‖ := by
  have hleft := localizedBlockPiece_norm_le_card_mul_norm p r N hN j x
  have hright := shiftedLocalizedBlockPiece_norm_le_card_mul_norm p r N hN j n x
  calc
    ‖localizedMultiplierDifferenceBlock p r N hN j n x‖ ≤
        ‖localizedBlockPiece p r N hN j x‖ +
          ‖shiftedLocalizedBlockPiece p r N hN j n x‖ :=
      localizedMultiplierDifferenceBlock_norm_le p r N hN j n x
    _ ≤
        ((2 * N + 1 : ℕ) : ℝ) * ‖x‖ +
          ((2 * N + 1 : ℕ) : ℝ) * ‖x‖ :=
      add_le_add hleft hright
    _ = (2 * ((2 * N + 1 : ℕ) : ℝ)) * ‖x‖ := by
      ring

theorem localizedBlockNormSeqC_pointwise_norm_le_card_mul_norm
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) (j : ℤ) :
    ‖localizedBlockNormSeqC p r N hN x j‖ ≤
      ((2 * N + 1 : ℕ) : ℝ) * ‖x‖ := by
  rw [localizedBlockNormSeqC_norm, localizedBlockNormSeq_apply]
  exact localizedBlockPiece_norm_le_card_mul_norm p r N hN j x



noncomputable def localizedBlockNormSeqAsInfty
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) : ellp (∞ : ℝ≥0∞) :=
  ⟨localizedBlockNormSeqC p r N hN x, by
    apply memℓp_infty
    refine ⟨((2 * N + 1 : ℕ) : ℝ) * ‖x‖, ?_⟩
    rintro _ ⟨j, rfl⟩
    exact localizedBlockNormSeqC_pointwise_norm_le_card_mul_norm p r N hN x j⟩

theorem localizedBlockNormSeqAsInfty_apply
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) (j : ℤ) :
    localizedBlockNormSeqAsInfty p r N hN x j =
      localizedBlockNormSeqC p r N hN x j := by
  rfl

theorem localizedBlockNormSeqAsInfty_norm_le
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) :
    ‖localizedBlockNormSeqAsInfty p r N hN x‖ ≤
      ((2 * N + 1 : ℕ) : ℝ) * ‖x‖ := by
  rw [lp.norm_eq_ciSup]
  exact ciSup_le fun j => by
    change ‖localizedBlockNormSeqC p r N hN x j‖ ≤
      ((2 * N + 1 : ℕ) : ℝ) * ‖x‖
    exact localizedBlockNormSeqC_pointwise_norm_le_card_mul_norm p r N hN x j

theorem localizedBlockPiece_infty_norm_le
    (r : ℝ≥0∞) [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ)
    (x : ellp (∞ : ℝ≥0∞)) :
    ‖localizedBlockPiece (∞ : ℝ≥0∞) r N hN j x‖ ≤
      ((2 * N + 1 : ℕ) : ℝ) * ‖x‖ := by
  rw [localizedBlockPiece_infty_eq_ellpOfEllOne]
  calc
    ‖ellpOfEllOne r
        (ellOneOfFiniteSupportInfinity (hatMultiplier (∞ : ℝ≥0∞) N j x)
          (hatMultiplier_support_finite (∞ : ℝ≥0∞) N hN j x))‖ ≤
        ‖ellOneOfFiniteSupportInfinity (hatMultiplier (∞ : ℝ≥0∞) N j x)
          (hatMultiplier_support_finite (∞ : ℝ≥0∞) N hN j x)‖ :=
      ellpOfEllOne_norm_le r _
    _ ≤ ((2 * N + 1 : ℕ) : ℝ) * ‖x‖ :=
      hatMultiplier_infinity_to_one_norm_le N hN j x

theorem localizedBlockNormSeqC_infty_r_pointwise_norm_le
    (r : ℝ≥0∞) [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (x : ellp (∞ : ℝ≥0∞)) (j : ℤ) :
    ‖localizedBlockNormSeqC (∞ : ℝ≥0∞) r N hN x j‖ ≤
      ((2 * N + 1 : ℕ) : ℝ) * ‖x‖ := by
  rw [localizedBlockNormSeqC_norm, localizedBlockNormSeq_apply]
  exact localizedBlockPiece_infty_norm_le r N hN j x



noncomputable def localizedBlockNormSeqInftyR
    (r : ℝ≥0∞) [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (x : ellp (∞ : ℝ≥0∞)) :
    ellp (∞ : ℝ≥0∞) :=
  ⟨localizedBlockNormSeqC (∞ : ℝ≥0∞) r N hN x, by
    apply memℓp_infty
    refine ⟨((2 * N + 1 : ℕ) : ℝ) * ‖x‖, ?_⟩
    rintro _ ⟨j, rfl⟩
    exact localizedBlockNormSeqC_infty_r_pointwise_norm_le r N hN x j⟩

theorem localizedBlockNormSeqInftyR_apply
    (r : ℝ≥0∞) [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (x : ellp (∞ : ℝ≥0∞)) (j : ℤ) :
    localizedBlockNormSeqInftyR r N hN x j =
      localizedBlockNormSeqC (∞ : ℝ≥0∞) r N hN x j := by
  rfl

theorem localizedBlockNormSeqInftyR_norm_le
    (r : ℝ≥0∞) [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (x : ellp (∞ : ℝ≥0∞)) :
    ‖localizedBlockNormSeqInftyR r N hN x‖ ≤
      ((2 * N + 1 : ℕ) : ℝ) * ‖x‖ := by
  rw [lp.norm_eq_ciSup]
  exact ciSup_le fun j => by
    change ‖localizedBlockNormSeqC (∞ : ℝ≥0∞) r N hN x j‖ ≤
      ((2 * N + 1 : ℕ) : ℝ) * ‖x‖
    exact localizedBlockNormSeqC_infty_r_pointwise_norm_le r N hN x j

noncomputable def localizedBlockNormSeqAsOuter
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) : ellp p := by
  by_cases hp_top : p = ∞
  · subst p
    exact localizedBlockNormSeqInftyR r N hN x
  · let L : ℝ := ((2 * N + 1 : ℕ) : ℝ)
    have hp_ne_zero : p ≠ 0 :=
      (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
    have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_top
    have hL_nonneg : 0 ≤ L := by positivity
    have hself_summ : Summable fun j : ℤ =>
        ‖localizedBlockNormSeqSelf p N hN x j‖ ^ p.toReal :=
      (lp.memℓp (localizedBlockNormSeqSelf p N hN x)).summable hp_pos
    have hsumm : Summable fun j : ℤ =>
        ‖localizedBlockNormSeqC p r N hN x j‖ ^ p.toReal := by
      refine Summable.of_nonneg_of_le
        (fun j => Real.rpow_nonneg (norm_nonneg _) _) ?_
        (hself_summ.mul_left (L ^ p.toReal))
      intro j
      have hpoint := localizedBlockNormSeqC_norm_le_card_mul_self_norm
        p r N hN x j
      calc
        ‖localizedBlockNormSeqC p r N hN x j‖ ^ p.toReal ≤
            (L * ‖localizedBlockNormSeqSelf p N hN x j‖) ^ p.toReal := by
          exact Real.rpow_le_rpow (norm_nonneg _) hpoint hp_pos.le
        _ = L ^ p.toReal *
              ‖localizedBlockNormSeqSelf p N hN x j‖ ^ p.toReal := by
          rw [Real.mul_rpow hL_nonneg (norm_nonneg _)]
    exact ⟨localizedBlockNormSeqC p r N hN x, memℓp_gen hsumm⟩

theorem localizedBlockNormSeqAsOuter_apply
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) (j : ℤ) :
    localizedBlockNormSeqAsOuter p r N hN x j =
      localizedBlockNormSeqC p r N hN x j := by
  unfold localizedBlockNormSeqAsOuter
  by_cases hp_top : p = ∞
  · subst p
    rfl
  · simp [hp_top]

theorem localizedBlockNormSeqAsOuter_norm_le
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) :
    ‖localizedBlockNormSeqAsOuter p r N hN x‖ ≤
      ((2 * N + 1 : ℕ) : ℝ) * ‖x‖ := by
  by_cases hp_top : p = ∞
  · subst p
    unfold localizedBlockNormSeqAsOuter
    simpa using localizedBlockNormSeqInftyR_norm_le r N hN x
  · let L : ℝ := ((2 * N + 1 : ℕ) : ℝ)
    have hp_ne_zero : p ≠ 0 :=
      (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
    have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_top
    have hL_nonneg : 0 ≤ L := by positivity
    have hself_summ : Summable fun j : ℤ =>
        ‖localizedBlockNormSeqSelf p N hN x j‖ ^ p.toReal :=
      (lp.memℓp (localizedBlockNormSeqSelf p N hN x)).summable hp_pos
    have hcross_summ : Summable fun j : ℤ =>
        ‖localizedBlockNormSeqAsOuter p r N hN x j‖ ^ p.toReal :=
      (lp.memℓp (localizedBlockNormSeqAsOuter p r N hN x)).summable hp_pos
    have hpoint : ∀ j : ℤ,
        ‖localizedBlockNormSeqAsOuter p r N hN x j‖ ^ p.toReal ≤
          L ^ p.toReal *
            ‖localizedBlockNormSeqSelf p N hN x j‖ ^ p.toReal := by
      intro j
      have hnorm := localizedBlockNormSeqC_norm_le_card_mul_self_norm
        p r N hN x j
      rw [localizedBlockNormSeqAsOuter_apply]
      calc
        ‖localizedBlockNormSeqC p r N hN x j‖ ^ p.toReal ≤
            (L * ‖localizedBlockNormSeqSelf p N hN x j‖) ^ p.toReal := by
          exact Real.rpow_le_rpow (norm_nonneg _) hnorm hp_pos.le
        _ = L ^ p.toReal *
              ‖localizedBlockNormSeqSelf p N hN x j‖ ^ p.toReal := by
          rw [Real.mul_rpow hL_nonneg (norm_nonneg _)]
    have htsum_le :
        ∑' j : ℤ,
            ‖localizedBlockNormSeqAsOuter p r N hN x j‖ ^ p.toReal ≤
          (L * ‖x‖) ^ p.toReal := by
      calc
        ∑' j : ℤ,
            ‖localizedBlockNormSeqAsOuter p r N hN x j‖ ^ p.toReal ≤
            ∑' j : ℤ, L ^ p.toReal *
              ‖localizedBlockNormSeqSelf p N hN x j‖ ^ p.toReal :=
          Summable.tsum_le_tsum hpoint hcross_summ
            (hself_summ.mul_left (L ^ p.toReal))
        _ = L ^ p.toReal *
            (∑' j : ℤ,
              ‖localizedBlockNormSeqSelf p N hN x j‖ ^ p.toReal) := by
          rw [tsum_mul_left]
        _ = L ^ p.toReal * ‖localizedBlockNormSeqSelf p N hN x‖ ^ p.toReal := by
          rw [lp.norm_rpow_eq_tsum hp_pos]
        _ ≤ L ^ p.toReal * ‖x‖ ^ p.toReal := by
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (norm_nonneg _)
              (localizedBlockNormSeqSelf_norm_le p N hN x) hp_pos.le)
            (Real.rpow_nonneg hL_nonneg p.toReal)
        _ = (L * ‖x‖) ^ p.toReal := by
          rw [Real.mul_rpow hL_nonneg (norm_nonneg x)]
    exact lp.norm_le_of_tsum_le hp_pos
      (mul_nonneg hL_nonneg (norm_nonneg x)) htsum_le

theorem localizedBlockPiece_self_eq_ellpOfFiniteSupport_cross
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) (x : ellp p) :
    localizedBlockPiece p p N hN j x =
      ellpOfFiniteSupport r p (localizedBlockPiece p r N hN j x)
        (localizedBlockPiece_support_finite p r N hN j x) := by
  ext k
  rfl

theorem localizedBlockPiece_self_norm_le_card_mul_cross_norm
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) (x : ellp p) :
    ‖localizedBlockPiece p p N hN j x‖ ≤
      ((2 * N + 1 : ℕ) : ℝ) *
        ‖localizedBlockPiece p r N hN j x‖ := by
  rw [localizedBlockPiece_self_eq_ellpOfFiniteSupport_cross p r N hN j x]
  exact ellpOfFiniteSupport_norm_le_card_mul_norm r p
    (localizedBlockPiece p r N hN j x)
    (localizedBlockPiece_support_finite p r N hN j x)
    (2 * N + 1)
    (localizedBlockPiece_support_ncard_le p r N hN j x)

theorem localizedBlockNormSeqSelf_norm_le_card_mul_outer_pointwise
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) (j : ℤ) :
    ‖localizedBlockNormSeqSelf p N hN x j‖ ≤
      ((2 * N + 1 : ℕ) : ℝ) *
        ‖localizedBlockNormSeqAsOuter p r N hN x j‖ := by
  rw [localizedBlockNormSeqSelf_apply, localizedBlockNormSeqC_norm,
    localizedBlockNormSeq_apply, localizedBlockNormSeqAsOuter_apply,
    localizedBlockNormSeqC_norm, localizedBlockNormSeq_apply]
  exact localizedBlockPiece_self_norm_le_card_mul_cross_norm p r N hN j x

theorem localizedBlockNormSeqSelf_norm_le_card_mul_outer_norm
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) :
    ‖localizedBlockNormSeqSelf p N hN x‖ ≤
      ((2 * N + 1 : ℕ) : ℝ) *
        ‖localizedBlockNormSeqAsOuter p r N hN x‖ := by
  let L : ℝ := ((2 * N + 1 : ℕ) : ℝ)
  have hL_nonneg : 0 ≤ L := by positivity
  by_cases hp_top : p = ∞
  · subst p
    rw [lp.norm_eq_ciSup]
    exact ciSup_le fun j => by
      have hpoint :=
        localizedBlockNormSeqSelf_norm_le_card_mul_outer_pointwise
          (∞ : ℝ≥0∞) r N hN x j
      have hcoord :
          L * ‖localizedBlockNormSeqAsOuter (∞ : ℝ≥0∞) r N hN x j‖ ≤
            L * ‖localizedBlockNormSeqAsOuter (∞ : ℝ≥0∞) r N hN x‖ := by
        exact mul_le_mul_of_nonneg_left
          (lp.norm_apply_le_norm (p := (∞ : ℝ≥0∞))
            (f := localizedBlockNormSeqAsOuter (∞ : ℝ≥0∞) r N hN x)
            (i := j) (by simp))
          hL_nonneg
      exact hpoint.trans hcoord
  · have hp_ne_zero : p ≠ 0 :=
      (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
    have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_top
    have hself_summ : Summable fun j : ℤ =>
        ‖localizedBlockNormSeqSelf p N hN x j‖ ^ p.toReal :=
      (lp.memℓp (localizedBlockNormSeqSelf p N hN x)).summable hp_pos
    have houter_summ : Summable fun j : ℤ =>
        ‖localizedBlockNormSeqAsOuter p r N hN x j‖ ^ p.toReal :=
      (lp.memℓp (localizedBlockNormSeqAsOuter p r N hN x)).summable hp_pos
    have hpoint : ∀ j : ℤ,
        ‖localizedBlockNormSeqSelf p N hN x j‖ ^ p.toReal ≤
          L ^ p.toReal *
            ‖localizedBlockNormSeqAsOuter p r N hN x j‖ ^ p.toReal := by
      intro j
      have hnorm := localizedBlockNormSeqSelf_norm_le_card_mul_outer_pointwise
        p r N hN x j
      calc
        ‖localizedBlockNormSeqSelf p N hN x j‖ ^ p.toReal ≤
            (L * ‖localizedBlockNormSeqAsOuter p r N hN x j‖) ^ p.toReal := by
          exact Real.rpow_le_rpow (norm_nonneg _) hnorm hp_pos.le
        _ = L ^ p.toReal *
              ‖localizedBlockNormSeqAsOuter p r N hN x j‖ ^ p.toReal := by
          rw [Real.mul_rpow hL_nonneg (norm_nonneg _)]
    have htsum_le :
        ∑' j : ℤ,
            ‖localizedBlockNormSeqSelf p N hN x j‖ ^ p.toReal ≤
          (L * ‖localizedBlockNormSeqAsOuter p r N hN x‖) ^ p.toReal := by
      calc
        ∑' j : ℤ,
            ‖localizedBlockNormSeqSelf p N hN x j‖ ^ p.toReal ≤
            ∑' j : ℤ, L ^ p.toReal *
              ‖localizedBlockNormSeqAsOuter p r N hN x j‖ ^ p.toReal :=
          Summable.tsum_le_tsum hpoint hself_summ
            (houter_summ.mul_left (L ^ p.toReal))
        _ = L ^ p.toReal *
            (∑' j : ℤ,
              ‖localizedBlockNormSeqAsOuter p r N hN x j‖ ^ p.toReal) := by
          rw [tsum_mul_left]
        _ = L ^ p.toReal *
            ‖localizedBlockNormSeqAsOuter p r N hN x‖ ^ p.toReal := by
          rw [lp.norm_rpow_eq_tsum hp_pos]
        _ = (L * ‖localizedBlockNormSeqAsOuter p r N hN x‖) ^ p.toReal := by
          rw [Real.mul_rpow hL_nonneg (norm_nonneg _)]
    exact lp.norm_le_of_tsum_le hp_pos
      (mul_nonneg hL_nonneg (norm_nonneg _)) htsum_le

theorem norm_le_two_mul_card_mul_localizedBlockNormSeqAsOuter_norm
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) :
    ‖x‖ ≤
      (2 * ((2 * N + 1 : ℕ) : ℝ)) *
        ‖localizedBlockNormSeqAsOuter p r N hN x‖ := by
  let L : ℝ := ((2 * N + 1 : ℕ) : ℝ)
  have hself := norm_le_two_mul_localizedBlockNormSeqSelf_norm p N hN x
  have hcross := localizedBlockNormSeqSelf_norm_le_card_mul_outer_norm
    p r N hN x
  calc
    ‖x‖ ≤ 2 * ‖localizedBlockNormSeqSelf p N hN x‖ := hself
    _ ≤ 2 * (L * ‖localizedBlockNormSeqAsOuter p r N hN x‖) := by
      exact mul_le_mul_of_nonneg_left hcross (by norm_num)
    _ = (2 * L) * ‖localizedBlockNormSeqAsOuter p r N hN x‖ := by ring

theorem localizedBlockNormSeqAsOuter_equiv_norm
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧
      ∀ x : ellp p,
        α * ‖x‖ ≤ ‖localizedBlockNormSeqAsOuter p r N hN x‖ ∧
          ‖localizedBlockNormSeqAsOuter p r N hN x‖ ≤ β * ‖x‖ := by
  let L : ℝ := ((2 * N + 1 : ℕ) : ℝ)
  have hL_pos : 0 < L := by positivity
  have hden_pos : 0 < 2 * L := by positivity
  refine ⟨(2 * L)⁻¹, L, inv_pos.mpr hden_pos, hL_pos, ?_⟩
  intro x
  constructor
  · have h :=
      norm_le_two_mul_card_mul_localizedBlockNormSeqAsOuter_norm
        p r N hN x
    calc
      (2 * L)⁻¹ * ‖x‖ ≤
          (2 * L)⁻¹ *
            ((2 * L) * ‖localizedBlockNormSeqAsOuter p r N hN x‖) := by
        exact mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hden_pos.le)
      _ = ‖localizedBlockNormSeqAsOuter p r N hN x‖ := by
        field_simp [hden_pos.ne']
  · exact localizedBlockNormSeqAsOuter_norm_le p r N hN x

theorem norm_le_two_mul_localizedBlockNormSeqInftyR_norm
    (r : ℝ≥0∞) [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (x : ellp (∞ : ℝ≥0∞)) :
    ‖x‖ ≤ 2 * ‖localizedBlockNormSeqInftyR r N hN x‖ := by
  rw [lp.norm_eq_ciSup]
  exact ciSup_le fun k => by
    rcases exists_hat_ge_half N hN k with ⟨j, hj⟩
    have hcoord :
        (1 / 2 : ℝ) * ‖x k‖ ≤
          ‖localizedBlockPiece (∞ : ℝ≥0∞) r N hN j x k‖ := by
      rw [localizedBlockPiece_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (hat_nonneg N j k)]
      exact mul_le_mul_of_nonneg_right hj (norm_nonneg _)
    have hpiece_to_seq :
        ‖localizedBlockPiece (∞ : ℝ≥0∞) r N hN j x‖ ≤
          ‖localizedBlockNormSeqInftyR r N hN x‖ := by
      calc
        ‖localizedBlockPiece (∞ : ℝ≥0∞) r N hN j x‖ =
            ‖localizedBlockNormSeqInftyR r N hN x j‖ := by
          rw [localizedBlockNormSeqInftyR_apply, localizedBlockNormSeqC_norm,
            localizedBlockNormSeq_apply]
        _ ≤ ‖localizedBlockNormSeqInftyR r N hN x‖ :=
          lp.norm_apply_le_norm (p := (∞ : ℝ≥0∞))
            (f := localizedBlockNormSeqInftyR r N hN x) (i := j) (by simp)
    have hhalf :
        (1 / 2 : ℝ) * ‖x k‖ ≤
          ‖localizedBlockNormSeqInftyR r N hN x‖ :=
      hcoord.trans ((lp.norm_apply_le_norm (p := r)
        (f := localizedBlockPiece (∞ : ℝ≥0∞) r N hN j x)
        (i := k)
        (by exact (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ r)).ne')).trans
        hpiece_to_seq)
    nlinarith

theorem localizedBlockNormSeqC_infty_one_pointwise_norm_le
    (N : ℕ) (hN : 1 ≤ N) (x : ellp (∞ : ℝ≥0∞)) (j : ℤ) :
    ‖localizedBlockNormSeqC (∞ : ℝ≥0∞) (1 : ℝ≥0∞) N hN x j‖ ≤
      ((2 * N + 1 : ℕ) : ℝ) * ‖x‖ := by
  rw [localizedBlockNormSeqC_norm, localizedBlockNormSeq_apply,
    localizedBlockPiece_infty_one_eq_ellOneOfFiniteSupportInfinity]
  exact hatMultiplier_infinity_to_one_norm_le N hN j x


noncomputable def localizedBlockNormSeqInftyOne
    (N : ℕ) (hN : 1 ≤ N) (x : ellp (∞ : ℝ≥0∞)) :
    ellp (∞ : ℝ≥0∞) :=
  ⟨localizedBlockNormSeqC (∞ : ℝ≥0∞) (1 : ℝ≥0∞) N hN x, by
    apply memℓp_infty
    refine ⟨((2 * N + 1 : ℕ) : ℝ) * ‖x‖, ?_⟩
    rintro _ ⟨j, rfl⟩
    exact localizedBlockNormSeqC_infty_one_pointwise_norm_le N hN x j⟩

theorem localizedBlockNormSeqInftyOne_apply
    (N : ℕ) (hN : 1 ≤ N) (x : ellp (∞ : ℝ≥0∞)) (j : ℤ) :
    localizedBlockNormSeqInftyOne N hN x j =
      localizedBlockNormSeqC (∞ : ℝ≥0∞) (1 : ℝ≥0∞) N hN x j := by
  rfl

theorem localizedBlockNormSeqInftyOne_norm_le
    (N : ℕ) (hN : 1 ≤ N) (x : ellp (∞ : ℝ≥0∞)) :
    ‖localizedBlockNormSeqInftyOne N hN x‖ ≤
      ((2 * N + 1 : ℕ) : ℝ) * ‖x‖ := by
  rw [lp.norm_eq_ciSup]
  exact ciSup_le fun j => by
    change ‖localizedBlockNormSeqC (∞ : ℝ≥0∞) (1 : ℝ≥0∞) N hN x j‖ ≤
      ((2 * N + 1 : ℕ) : ℝ) * ‖x‖
    exact localizedBlockNormSeqC_infty_one_pointwise_norm_le N hN x j

theorem norm_le_two_mul_localizedBlockNormSeqInftyOne_norm
    (N : ℕ) (hN : 1 ≤ N) (x : ellp (∞ : ℝ≥0∞)) :
    ‖x‖ ≤ 2 * ‖localizedBlockNormSeqInftyOne N hN x‖ := by
  rw [lp.norm_eq_ciSup]
  exact ciSup_le fun k => by
    rcases exists_hat_ge_half N hN k with ⟨j, hj⟩
    have hcoord :
        (1 / 2 : ℝ) * ‖x k‖ ≤
          ‖localizedBlockPiece (∞ : ℝ≥0∞) (1 : ℝ≥0∞) N hN j x k‖ := by
      rw [localizedBlockPiece_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (hat_nonneg N j k)]
      exact mul_le_mul_of_nonneg_right hj (norm_nonneg _)
    have hpiece_to_seq :
        ‖localizedBlockPiece (∞ : ℝ≥0∞) (1 : ℝ≥0∞) N hN j x‖ ≤
          ‖localizedBlockNormSeqInftyOne N hN x‖ := by
      calc
        ‖localizedBlockPiece (∞ : ℝ≥0∞) (1 : ℝ≥0∞) N hN j x‖ =
            ‖localizedBlockNormSeqInftyOne N hN x j‖ := by
          rw [localizedBlockNormSeqInftyOne_apply, localizedBlockNormSeqC_norm,
            localizedBlockNormSeq_apply]
        _ ≤ ‖localizedBlockNormSeqInftyOne N hN x‖ :=
          lp.norm_apply_le_norm (p := (∞ : ℝ≥0∞))
            (f := localizedBlockNormSeqInftyOne N hN x) (i := j) (by simp)
    have hhalf :
        (1 / 2 : ℝ) * ‖x k‖ ≤
          ‖localizedBlockNormSeqInftyOne N hN x‖ :=
      hcoord.trans ((lp.norm_apply_le_norm (p := (1 : ℝ≥0∞))
        (f := localizedBlockPiece (∞ : ℝ≥0∞) (1 : ℝ≥0∞) N hN j x)
        (i := k) (by norm_num)).trans hpiece_to_seq)
    nlinarith

theorem blockNorm_equiv_norm
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧
      ∀ x : ellp p, α * ‖x‖ ≤ blockNorm p r N x ∧
        blockNorm p r N x ≤ β * ‖x‖ :=
  Classical.choose_spec (exists_blockNorm p r N) hN


noncomputable def localizedMultiplierDifferenceNormSeq
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (n : ℤ) (x : ellp p) : ℤ → ℝ :=
  fun j => ‖localizedMultiplierDifferenceBlock p r N hN j n x‖

theorem localizedMultiplierDifferenceNormSeq_apply
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (n : ℤ) (x : ellp p) (j : ℤ) :
    localizedMultiplierDifferenceNormSeq p r N hN n x j =
      ‖localizedMultiplierDifferenceBlock p r N hN j n x‖ := by
  rfl

theorem localizedMultiplierDifferenceNormSeq_nonneg
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (n : ℤ) (x : ellp p) (j : ℤ) :
    0 ≤ localizedMultiplierDifferenceNormSeq p r N hN n x j :=
  norm_nonneg _


noncomputable def localizedMultiplierDifferenceNormSeqC
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (n : ℤ) (x : ellp p) : ℤ → ℂ :=
  fun j => (localizedMultiplierDifferenceNormSeq p r N hN n x j : ℂ)

theorem localizedMultiplierDifferenceNormSeqC_apply
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (n : ℤ) (x : ellp p) (j : ℤ) :
    localizedMultiplierDifferenceNormSeqC p r N hN n x j =
      (localizedMultiplierDifferenceNormSeq p r N hN n x j : ℂ) := by
  rfl

theorem localizedMultiplierDifferenceNormSeqC_norm
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (n : ℤ) (x : ellp p) (j : ℤ) :
    ‖localizedMultiplierDifferenceNormSeqC p r N hN n x j‖ =
      localizedMultiplierDifferenceNormSeq p r N hN n x j := by
  rw [localizedMultiplierDifferenceNormSeqC_apply, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg
    (localizedMultiplierDifferenceNormSeq_nonneg p r N hN n x j)

theorem localizedMultiplierDifferenceNormSeqC_norm_le
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (n : ℤ) (x : ellp p) (j : ℤ) :
    ‖localizedMultiplierDifferenceNormSeqC p r N hN n x j‖ ≤
      ‖localizedBlockNormSeqAsOuter p r N hN x j‖ +
        ‖localizedBlockNormSeqAsOuter p r N hN
          (shiftOperator p n x) j‖ := by
  have hblock_x :
      ‖localizedBlockNormSeqAsOuter p r N hN x j‖ =
        ‖localizedBlockPiece p r N hN j x‖ := by
    rw [localizedBlockNormSeqAsOuter_apply, localizedBlockNormSeqC_norm,
      localizedBlockNormSeq_apply]
  have hblock_shift :
      ‖localizedBlockNormSeqAsOuter p r N hN
          (shiftOperator p n x) j‖ =
        ‖shiftedLocalizedBlockPiece p r N hN j n x‖ := by
    rw [localizedBlockNormSeqAsOuter_apply, localizedBlockNormSeqC_norm,
      localizedBlockNormSeq_apply, shiftedLocalizedBlockPiece_norm_eq]
  rw [localizedMultiplierDifferenceNormSeqC_norm,
    localizedMultiplierDifferenceNormSeq_apply]
  calc
    ‖localizedMultiplierDifferenceBlock p r N hN j n x‖ ≤
        ‖localizedBlockPiece p r N hN j x‖ +
          ‖shiftedLocalizedBlockPiece p r N hN j n x‖ :=
      localizedMultiplierDifferenceBlock_norm_le p r N hN j n x
    _ =
        ‖localizedBlockNormSeqAsOuter p r N hN x j‖ +
          ‖localizedBlockNormSeqAsOuter p r N hN
            (shiftOperator p n x) j‖ := by
      rw [hblock_x, hblock_shift]




noncomputable def localizedMultiplierDifferenceNormSeqAsOuter
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (n : ℤ) (x : ellp p) : ellp p :=
  ⟨localizedMultiplierDifferenceNormSeqC p r N hN n x, by
    have hleft : Memℓp
        (fun j : ℤ => ‖localizedBlockNormSeqAsOuter p r N hN x j‖) p :=
      (lp.memℓp (localizedBlockNormSeqAsOuter p r N hN x)).norm
    have hright : Memℓp
        (fun j : ℤ =>
          ‖localizedBlockNormSeqAsOuter p r N hN
            (shiftOperator p n x) j‖) p :=
      (lp.memℓp
        (localizedBlockNormSeqAsOuter p r N hN
          (shiftOperator p n x))).norm
    exact (hleft.add hright).mono
      (localizedMultiplierDifferenceNormSeqC_norm_le p r N hN n x)⟩

theorem localizedMultiplierDifferenceNormSeqAsOuter_apply
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (n : ℤ) (x : ellp p) (j : ℤ) :
    localizedMultiplierDifferenceNormSeqAsOuter p r N hN n x j =
      localizedMultiplierDifferenceNormSeqC p r N hN n x j := by
  rfl

theorem matrixOperator_apply_hatMultiplier
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (j k : ℤ) (x : ellp p) :
    (dominatedMatrixOperator p A a hA (hatMultiplier p N j x)) k =
      ∑' l : ℤ, A k l * ((hat N j l : ℂ) * x l) := by
  have hT := dominatedMatrixOperator_isMatrixOperator p A a hA
  have happly := (hT (hatMultiplier p N j x) k).2
  simpa [hatMultiplier_apply, mul_assoc] using happly

theorem hatMultiplier_matrixOperator_apply
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (j k : ℤ) (x : ellp p) :
    (hatMultiplier p N j (dominatedMatrixOperator p A a hA x)) k =
      (hat N j k : ℂ) * (∑' l : ℤ, A k l * x l) := by
  have hT := dominatedMatrixOperator_isMatrixOperator p A a hA
  rw [hatMultiplier_apply]
  rw [(hT x k).2]

theorem matrixOperator_commutator_apply
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (j k : ℤ) (x : ellp p) :
    ((hatMultiplier p N j (dominatedMatrixOperator p A a hA x) -
        dominatedMatrixOperator p A a hA (hatMultiplier p N j x)) k) =
      tsum (fun l : ℤ =>
        (((hat N j k : ℂ) - (hat N j l : ℂ)) * A k l * x l)) := by
  let c : ℂ := hat N j k
  let f : ℤ → ℂ := fun l => A k l * x l
  let g : ℤ → ℂ := fun l => A k l * ((hat N j l : ℂ) * x l)
  have hT := dominatedMatrixOperator_isMatrixOperator p A a hA
  have hf : Summable f := by
    simpa [f] using (hT x k).1
  have hg : Summable g := by
    simpa [g, hatMultiplier_apply, mul_assoc] using
      (hT (hatMultiplier p N j x) k).1
  calc
    ((hatMultiplier p N j (dominatedMatrixOperator p A a hA x) -
        dominatedMatrixOperator p A a hA (hatMultiplier p N j x)) k) =
        c * tsum f - tsum g := by
      simp [c, f, g, hatMultiplier_matrixOperator_apply,
        matrixOperator_apply_hatMultiplier]
    _ = tsum (fun l : ℤ => c * f l) - tsum g := by
      rw [tsum_mul_left]
    _ = tsum (fun l : ℤ => c * f l - g l) := by
      rw [Summable.tsum_sub (hf.mul_left c) hg]
    _ = tsum (fun l : ℤ =>
        (((hat N j k : ℂ) - (hat N j l : ℂ)) * A k l * x l)) := by
      apply tsum_congr
      intro l
      simp [c, f, g]
      ring

theorem matrixOperator_commutator_bound
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (j k l : ℤ) (x : ellp p) :
    ‖(((hat N j k : ℂ) - (hat N j l : ℂ)) * A k l * x l)‖ ≤
      (a (k - l) * omega N (k - l)) * ‖x l‖ := by
  have hdiff : ‖((hat N j k : ℂ) - (hat N j l : ℂ))‖ ≤ omega N (k - l) := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hat_lipschitz N hN j k l
  have hdom : ‖A k l‖ ≤ a (k - l) := hA.2.2 k l
  have homega_nonneg : 0 ≤ omega N (k - l) := omega_nonneg N (k - l)
  calc
    ‖(((hat N j k : ℂ) - (hat N j l : ℂ)) * A k l * x l)‖ =
        ‖((hat N j k : ℂ) - (hat N j l : ℂ))‖ * ‖A k l‖ * ‖x l‖ := by
      rw [norm_mul, norm_mul]
    _ ≤ (omega N (k - l) * a (k - l)) * ‖x l‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hdiff hdom (norm_nonneg _) homega_nonneg)
        (norm_nonneg _)
    _ = (a (k - l) * omega N (k - l)) * ‖x l‖ := by ring

theorem matrixOperator_cross_commutator_apply
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (j k : ℤ) (x : ellp p) :
    ((dominatedMatrixOperator r A a hA (localizedBlockPiece p r N hN j x) -
        localizedBlockPiece p r N hN j (dominatedMatrixOperator p A a hA x)) k) =
      tsum (fun l : ℤ =>
        (((hat N j l : ℂ) - (hat N j k : ℂ)) * A k l * x l)) := by
  let c : ℂ := hat N j k
  let f : ℤ → ℂ := fun l => A k l * x l
  let g : ℤ → ℂ := fun l => A k l * ((hat N j l : ℂ) * x l)
  have hTp := dominatedMatrixOperator_isMatrixOperator p A a hA
  have hTr := dominatedMatrixOperator_isMatrixOperator r A a hA
  have hf : Summable f := by
    simpa [f] using (hTp x k).1
  have hg : Summable g := by
    simpa [g, localizedBlockPiece_apply, mul_assoc] using
      (hTr (localizedBlockPiece p r N hN j x) k).1
  calc
    ((dominatedMatrixOperator r A a hA (localizedBlockPiece p r N hN j x) -
        localizedBlockPiece p r N hN j (dominatedMatrixOperator p A a hA x)) k) =
        tsum g - c * tsum f := by
      simp [c, f, g, localizedBlockPiece_apply]
      rw [(hTr (localizedBlockPiece p r N hN j x) k).2]
      rw [(hTp x k).2]
      simp [localizedBlockPiece_apply]
    _ = tsum g - tsum (fun l : ℤ => c * f l) := by
      rw [tsum_mul_left]
    _ = tsum (fun l : ℤ => g l - c * f l) := by
      rw [Summable.tsum_sub hg (hf.mul_left c)]
    _ = tsum (fun l : ℤ =>
        (((hat N j l : ℂ) - (hat N j k : ℂ)) * A k l * x l)) := by
      apply tsum_congr
      intro l
      simp [c, f, g]
      ring

theorem matrixOperator_cross_commutator_bound
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (j k l : ℤ) (x : ellp p) :
    ‖(((hat N j l : ℂ) - (hat N j k : ℂ)) * A k l * x l)‖ ≤
      (a (k - l) * omega N (k - l)) * ‖x l‖ := by
  have h := matrixOperator_commutator_bound p r A a hA N hN j k l x
  have heq :
      (((hat N j l : ℂ) - (hat N j k : ℂ)) * A k l * x l) =
        -(((hat N j k : ℂ) - (hat N j l : ℂ)) * A k l * x l) := by
    ring
  rw [heq, norm_neg]
  exact h


noncomputable def crossHatCommutatorMatrix
    (A : ℤ → ℤ → ℂ) (N : ℕ) (j : ℤ) : ℤ → ℤ → ℂ :=
  fun k l => (((hat N j l : ℂ) - (hat N j k : ℂ)) * A k l)

theorem crossHatCommutatorMatrix_dominated
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) :
    MatrixDominatedBy (crossHatCommutatorMatrix A N j)
      (fun n : ℤ => a n * omega N n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact mul_nonneg (hA.1 n) (omega_nonneg N n)
  · exact summable_norm_kernel_mul_omega a hA.2.1 N
  · intro k l
    unfold crossHatCommutatorMatrix
    have hdiff : ‖((hat N j l : ℂ) - (hat N j k : ℂ))‖ ≤
        omega N (k - l) := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      exact hat_lipschitz N hN j k l
    have hdom : ‖A k l‖ ≤ a (k - l) := hA.2.2 k l
    have homega_nonneg : 0 ≤ omega N (k - l) := omega_nonneg N (k - l)
    calc
      ‖(((hat N j l : ℂ) - (hat N j k : ℂ)) * A k l)‖ =
          ‖((hat N j l : ℂ) - (hat N j k : ℂ))‖ * ‖A k l‖ := by
        rw [norm_mul]
      _ ≤ omega N (k - l) * a (k - l) := by
        exact mul_le_mul hdiff hdom (norm_nonneg _) homega_nonneg
      _ = a (k - l) * omega N (k - l) := by ring

theorem crossHatCommutatorDominatedOperator_norm_le
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) :
    ‖dominatedMatrixOperator p (crossHatCommutatorMatrix A N j)
        (fun n : ℤ => a n * omega N n)
        (crossHatCommutatorMatrix_dominated A a hA N hN j)‖ ≤
      tsum (fun n : ℤ => a n * omega N n) := by
  have hnorm_le := dominatedMatrixOperator_norm_le p
    (crossHatCommutatorMatrix A N j)
    (fun n : ℤ => a n * omega N n)
    (crossHatCommutatorMatrix_dominated A a hA N hN j)
  have htsum_norm_eq :
      tsum (fun n : ℤ => ‖a n * omega N n‖) =
        tsum (fun n : ℤ => a n * omega N n) := by
    apply tsum_congr
    intro n
    exact Real.norm_of_nonneg (mul_nonneg (hA.1 n) (omega_nonneg N n))
  exact hnorm_le.trans_eq htsum_norm_eq

theorem exists_one_le_and_forall_crossHatCommutatorDominatedOperator_norm_lt
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∃ hN : 1 ≤ N,
      ∀ j : ℤ,
        ‖dominatedMatrixOperator p (crossHatCommutatorMatrix A N j)
            (fun n : ℤ => a n * omega N n)
            (crossHatCommutatorMatrix_dominated A a hA N hN j)‖ <
          epsilon := by
  rcases exists_one_le_and_kernel_omega_tsum_lt a hA.2.1 hepsilon with
    ⟨N, hN, hsmall⟩
  refine ⟨N, hN, ?_⟩
  intro j
  exact (crossHatCommutatorDominatedOperator_norm_le p A a hA N hN j).trans_lt hsmall

noncomputable def hatCommutatorMatrix
    (A : ℤ → ℤ → ℂ) (N : ℕ) (j : ℤ) : ℤ → ℤ → ℂ :=
  fun k l => (((hat N j k : ℂ) - (hat N j l : ℂ)) * A k l)

theorem hatCommutatorMatrix_dominated
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) :
    MatrixDominatedBy (hatCommutatorMatrix A N j)
      (fun n : ℤ => a n * omega N n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact mul_nonneg (hA.1 n) (omega_nonneg N n)
  · exact summable_norm_kernel_mul_omega a hA.2.1 N
  · intro k l
    unfold hatCommutatorMatrix
    have hdiff : ‖((hat N j k : ℂ) - (hat N j l : ℂ))‖ ≤
        omega N (k - l) := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact hat_lipschitz N hN j k l
    have hdom : ‖A k l‖ ≤ a (k - l) := hA.2.2 k l
    have homega_nonneg : 0 ≤ omega N (k - l) := omega_nonneg N (k - l)
    calc
      ‖(((hat N j k : ℂ) - (hat N j l : ℂ)) * A k l)‖ =
          ‖((hat N j k : ℂ) - (hat N j l : ℂ))‖ * ‖A k l‖ := by
        rw [norm_mul]
      _ ≤ omega N (k - l) * a (k - l) := by
        exact mul_le_mul hdiff hdom (norm_nonneg _) homega_nonneg
      _ = a (k - l) * omega N (k - l) := by ring

theorem hatCommutatorDominatedOperator_norm_le
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) :
    ‖dominatedMatrixOperator p (hatCommutatorMatrix A N j)
        (fun n : ℤ => a n * omega N n)
        (hatCommutatorMatrix_dominated A a hA N hN j)‖ ≤
      tsum (fun n : ℤ => a n * omega N n) := by
  have hnorm_le := dominatedMatrixOperator_norm_le p (hatCommutatorMatrix A N j)
    (fun n : ℤ => a n * omega N n)
    (hatCommutatorMatrix_dominated A a hA N hN j)
  have htsum_norm_eq :
      tsum (fun n : ℤ => ‖a n * omega N n‖) =
        tsum (fun n : ℤ => a n * omega N n) := by
    apply tsum_congr
    intro n
    exact Real.norm_of_nonneg (mul_nonneg (hA.1 n) (omega_nonneg N n))
  exact hnorm_le.trans_eq htsum_norm_eq

noncomputable def hatCommutatorOperator
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (j : ℤ) : ellp p →L[ℂ] ellp p :=
  (hatMultiplier p N j).comp (dominatedMatrixOperator p A a hA) -
    (dominatedMatrixOperator p A a hA).comp (hatMultiplier p N j)

theorem hatCommutatorOperator_isMatrixOperator
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) :
    IsMatrixOperator p (hatCommutatorMatrix A N j)
      (hatCommutatorOperator p A a hA N j) := by
  intro x k
  have hdom := dominatedMatrixOperator_isMatrixOperator p (hatCommutatorMatrix A N j)
    (fun n : ℤ => a n * omega N n)
    (hatCommutatorMatrix_dominated A a hA N hN j)
  constructor
  · exact (hdom x k).1
  · change ((hatMultiplier p N j (dominatedMatrixOperator p A a hA x) -
        dominatedMatrixOperator p A a hA (hatMultiplier p N j x)) k) =
      tsum (fun l : ℤ => hatCommutatorMatrix A N j k l * x l)
    simpa [hatCommutatorMatrix] using
      matrixOperator_commutator_apply p p A a hA N j k x

theorem hatCommutatorOperator_eq_dominated
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) :
    hatCommutatorOperator p A a hA N j =
      dominatedMatrixOperator p (hatCommutatorMatrix A N j)
        (fun n : ℤ => a n * omega N n)
        (hatCommutatorMatrix_dominated A a hA N hN j) := by
  exact isMatrixOperator_unique p (hatCommutatorMatrix A N j)
    (hatCommutatorOperator p A a hA N j)
    (dominatedMatrixOperator p (hatCommutatorMatrix A N j)
      (fun n : ℤ => a n * omega N n)
      (hatCommutatorMatrix_dominated A a hA N hN j))
    (hatCommutatorOperator_isMatrixOperator p A a hA N hN j)
    (dominatedMatrixOperator_isMatrixOperator p (hatCommutatorMatrix A N j)
      (fun n : ℤ => a n * omega N n)
      (hatCommutatorMatrix_dominated A a hA N hN j))

theorem hatCommutatorOperator_norm_le
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) :
    ‖hatCommutatorOperator p A a hA N j‖ ≤
      tsum (fun n : ℤ => a n * omega N n) := by
  rw [hatCommutatorOperator_eq_dominated p A a hA N hN j]
  exact hatCommutatorDominatedOperator_norm_le p A a hA N hN j

theorem exists_one_le_and_forall_hatCommutatorOperator_norm_lt
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ j : ℤ, ‖hatCommutatorOperator p A a hA N j‖ < epsilon := by
  rcases exists_one_le_and_kernel_omega_tsum_lt a hA.2.1 hepsilon with
    ⟨N, hN, hsmall⟩
  refine ⟨N, hN, ?_⟩
  intro j
  exact (hatCommutatorOperator_norm_le p A a hA N hN j).trans_lt hsmall

theorem lp_norm_le_add_of_pointwise_norm_le_add
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u v w : ellp p)
    (hpoint : ∀ j : ℤ, ‖u j‖ ≤ ‖(v + w) j‖) :
    ‖u‖ ≤ ‖v‖ + ‖w‖ := by
  have hp_ne_zero : p ≠ 0 :=
    (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hmono : ‖u‖ ≤ ‖v + w‖ :=
    lp.norm_mono (p := p) (E := fun _ : ℤ => ℂ)
      (F := fun _ : ℤ => ℂ) hp_ne_zero hpoint
  exact hmono.trans (norm_add_le v w)

theorem lp_norm_le_finset_sum_norm_of_pointwise
    (p : ℝ≥0∞) [Fact (1 ≤ p)] {ι : Type*} (s : Finset ι)
    (u : ellp p) (f : ι → ellp p)
    (hpoint : ∀ k : ℤ, ‖u k‖ ≤ ∑ i ∈ s, ‖f i k‖) :
    ‖u‖ ≤ ∑ i ∈ s, ‖f i‖ := by
  classical
  let z : lp (fun _ : ℤ => ℝ) p := ∑ i ∈ s, lp.toNorm (f i)
  have hpoint_z : ∀ k : ℤ, ‖u k‖ ≤ ‖z k‖ := by
    intro k
    have hz_coord : z k = ∑ i ∈ s, ‖f i k‖ := by
      simp only [z]
      rw [lp.coeFn_sum, Finset.sum_apply]
      simp [lp.toNorm_coe]
    rw [hz_coord, Real.norm_of_nonneg
      (Finset.sum_nonneg fun i _hi => norm_nonneg (f i k))]
    exact hpoint k
  have hp_ne_zero : p ≠ 0 :=
    (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hmono : ‖u‖ ≤ ‖z‖ :=
    lp.norm_mono (p := p) (E := fun _ : ℤ => ℂ)
      (F := fun _ : ℤ => ℝ) hp_ne_zero hpoint_z
  have hz_norm : ‖z‖ ≤ ∑ i ∈ s, ‖lp.toNorm (f i)‖ := by
    dsimp [z]
    exact norm_sum_le s fun i => lp.toNorm (f i)
  calc
    ‖u‖ ≤ ‖z‖ := hmono
    _ ≤ ∑ i ∈ s, ‖lp.toNorm (f i)‖ := hz_norm
    _ = ∑ i ∈ s, ‖f i‖ := by
      simp [lp.norm_toNorm]

theorem lp_norm_le_two_finset_sum_norm_of_pointwise
    (p : ℝ≥0∞) [Fact (1 ≤ p)] {ι κ : Type*}
    (s : Finset ι) (t : Finset κ)
    (u : ellp p) (f : ι → ellp p) (g : κ → ellp p)
    (hpoint : ∀ k : ℤ,
      ‖u k‖ ≤ ∑ i ∈ s, ‖f i k‖ + ∑ i ∈ t, ‖g i k‖) :
    ‖u‖ ≤ ∑ i ∈ s, ‖f i‖ + ∑ i ∈ t, ‖g i‖ := by
  classical
  let z₁ : lp (fun _ : ℤ => ℝ) p := ∑ i ∈ s, lp.toNorm (f i)
  let z₂ : lp (fun _ : ℤ => ℝ) p := ∑ i ∈ t, lp.toNorm (g i)
  let z : lp (fun _ : ℤ => ℝ) p := z₁ + z₂
  have hpoint_z : ∀ k : ℤ, ‖u k‖ ≤ ‖z k‖ := by
    intro k
    have hz₁_coord : z₁ k = ∑ i ∈ s, ‖f i k‖ := by
      simp only [z₁]
      rw [lp.coeFn_sum, Finset.sum_apply]
      simp [lp.toNorm_coe]
    have hz₂_coord : z₂ k = ∑ i ∈ t, ‖g i k‖ := by
      simp only [z₂]
      rw [lp.coeFn_sum, Finset.sum_apply]
      simp [lp.toNorm_coe]
    have hz_coord : z k =
        ∑ i ∈ s, ‖f i k‖ + ∑ i ∈ t, ‖g i k‖ := by
      simp [z, hz₁_coord, hz₂_coord]
    rw [hz_coord, Real.norm_of_nonneg
      (add_nonneg
        (Finset.sum_nonneg fun i _hi => norm_nonneg (f i k))
        (Finset.sum_nonneg fun i _hi => norm_nonneg (g i k)))]
    exact hpoint k
  have hp_ne_zero : p ≠ 0 :=
    (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hmono : ‖u‖ ≤ ‖z‖ :=
    lp.norm_mono (p := p) (E := fun _ : ℤ => ℂ)
      (F := fun _ : ℤ => ℝ) hp_ne_zero hpoint_z
  have hz₁_norm : ‖z₁‖ ≤ ∑ i ∈ s, ‖lp.toNorm (f i)‖ := by
    dsimp [z₁]
    exact norm_sum_le s fun i => lp.toNorm (f i)
  have hz₂_norm : ‖z₂‖ ≤ ∑ i ∈ t, ‖lp.toNorm (g i)‖ := by
    dsimp [z₂]
    exact norm_sum_le t fun i => lp.toNorm (g i)
  calc
    ‖u‖ ≤ ‖z‖ := hmono
    _ = ‖z₁ + z₂‖ := rfl
    _ ≤ ‖z₁‖ + ‖z₂‖ := norm_add_le _ _
    _ ≤ (∑ i ∈ s, ‖lp.toNorm (f i)‖) +
        (∑ i ∈ t, ‖lp.toNorm (g i)‖) :=
      add_le_add hz₁_norm hz₂_norm
    _ = ∑ i ∈ s, ‖f i‖ + ∑ i ∈ t, ‖g i‖ := by
      simp [lp.norm_toNorm]

theorem localizedMultiplierDifferenceBlock_norm_le_omega_neighbor_sums
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (j n : ℤ) (x : ellp p) :
    ‖localizedMultiplierDifferenceBlock p r N hN j n x‖ ≤
      omega N n *
        (∑ i ∈ Finset.Icc (j - 1) (j + 1),
            ‖localizedBlockPiece p r N hN i x‖ +
          ∑ i ∈ Finset.Icc (j - n / (N : ℤ) - 2)
              (j - n / (N : ℤ) + 2),
            ‖localizedBlockPiece p r N hN i x‖) := by
  classical
  let s₁ : Finset ℤ := Finset.Icc (j - 1) (j + 1)
  let s₂ : Finset ℤ :=
    Finset.Icc (j - n / (N : ℤ) - 2) (j - n / (N : ℤ) + 2)
  let cℝ : ℝ := omega N n
  let cℂ : ℂ := (cℝ : ℂ)
  let f : ℤ → ellp r := fun i => cℂ • localizedBlockPiece p r N hN i x
  let g : ℤ → ellp r := fun i => cℂ • localizedBlockPiece p r N hN i x
  have hc_nonneg : 0 ≤ cℝ := omega_nonneg N n
  have hc_norm (z : ℂ) : ‖cℂ * z‖ = cℝ * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hc_nonneg]
  have hpoint : ∀ k : ℤ,
      ‖localizedMultiplierDifferenceBlock p r N hN j n x k‖ ≤
        ∑ i ∈ s₁, ‖f i k‖ + ∑ i ∈ s₂, ‖g i k‖ := by
    intro k
    by_cases hzero :
        localizedMultiplierDifferenceBlock p r N hN j n x k = 0
    · rw [hzero, norm_zero]
      exact add_nonneg
        (Finset.sum_nonneg fun i _hi => norm_nonneg (f i k))
        (Finset.sum_nonneg fun i _hi => norm_nonneg (g i k))
    · have hsupport :=
        localizedMultiplierDifferenceBlock_support_subset_union
          p r N hN j n x (by simpa using hzero)
      have hdiff_le :=
        localizedMultiplierDifferenceBlock_apply_norm_le_omega
          p r N hN j n x k
      rcases hsupport with hleft | hright
      · have hxsum :=
          localizedBlockPiece_sum_neighbor_one_apply
            p r N hN j k x hleft
        have hsum_scaled :
            cℂ * x k = ∑ i ∈ s₁, f i k := by
          calc
            cℂ * x k =
                cℂ * (∑ i ∈ s₁,
                  localizedBlockPiece p r N hN i x k) := by
              rw [hxsum]
            _ = ∑ i ∈ s₁,
                cℂ * localizedBlockPiece p r N hN i x k := by
              rw [Finset.mul_sum]
            _ = ∑ i ∈ s₁, f i k := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              simp [f, smul_eq_mul]
        calc
          ‖localizedMultiplierDifferenceBlock p r N hN j n x k‖ ≤
              cℝ * ‖x k‖ := hdiff_le
          _ = ‖cℂ * x k‖ := (hc_norm (x k)).symm
          _ = ‖∑ i ∈ s₁, f i k‖ := by rw [hsum_scaled]
          _ ≤ ∑ i ∈ s₁, ‖f i k‖ := norm_sum_le s₁ fun i => f i k
          _ ≤ ∑ i ∈ s₁, ‖f i k‖ + ∑ i ∈ s₂, ‖g i k‖ := by
            exact le_add_of_nonneg_right
              (Finset.sum_nonneg fun i _hi => norm_nonneg (g i k))
      · have hxsum :=
          localizedBlockPiece_sum_neighbor_two_shift_apply
            p r N hN j k n x hright
        have hsum_scaled :
            cℂ * x k = ∑ i ∈ s₂, g i k := by
          calc
            cℂ * x k =
                cℂ * (∑ i ∈ s₂,
                  localizedBlockPiece p r N hN i x k) := by
              rw [hxsum]
            _ = ∑ i ∈ s₂,
                cℂ * localizedBlockPiece p r N hN i x k := by
              rw [Finset.mul_sum]
            _ = ∑ i ∈ s₂, g i k := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              simp [g, smul_eq_mul]
        calc
          ‖localizedMultiplierDifferenceBlock p r N hN j n x k‖ ≤
              cℝ * ‖x k‖ := hdiff_le
          _ = ‖cℂ * x k‖ := (hc_norm (x k)).symm
          _ = ‖∑ i ∈ s₂, g i k‖ := by rw [hsum_scaled]
          _ ≤ ∑ i ∈ s₂, ‖g i k‖ := norm_sum_le s₂ fun i => g i k
          _ ≤ ∑ i ∈ s₁, ‖f i k‖ + ∑ i ∈ s₂, ‖g i k‖ := by
            exact le_add_of_nonneg_left
              (Finset.sum_nonneg fun i _hi => norm_nonneg (f i k))
  have hnorm :=
    lp_norm_le_two_finset_sum_norm_of_pointwise
      r s₁ s₂
      (localizedMultiplierDifferenceBlock p r N hN j n x) f g hpoint
  have hsum₁ :
      ∑ i ∈ s₁, ‖f i‖ =
        cℝ * ∑ i ∈ s₁, ‖localizedBlockPiece p r N hN i x‖ := by
    calc
      ∑ i ∈ s₁, ‖f i‖ =
          ∑ i ∈ s₁, cℝ * ‖localizedBlockPiece p r N hN i x‖ := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        simp only [f, cℂ]
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hc_nonneg]
      _ = cℝ * ∑ i ∈ s₁, ‖localizedBlockPiece p r N hN i x‖ := by
        rw [Finset.mul_sum]
  have hsum₂ :
      ∑ i ∈ s₂, ‖g i‖ =
        cℝ * ∑ i ∈ s₂, ‖localizedBlockPiece p r N hN i x‖ := by
    calc
      ∑ i ∈ s₂, ‖g i‖ =
          ∑ i ∈ s₂, cℝ * ‖localizedBlockPiece p r N hN i x‖ := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        simp only [g, cℂ]
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hc_nonneg]
      _ = cℝ * ∑ i ∈ s₂, ‖localizedBlockPiece p r N hN i x‖ := by
        rw [Finset.mul_sum]
  calc
    ‖localizedMultiplierDifferenceBlock p r N hN j n x‖ ≤
        ∑ i ∈ s₁, ‖f i‖ + ∑ i ∈ s₂, ‖g i‖ := hnorm
    _ =
        cℝ *
          (∑ i ∈ s₁, ‖localizedBlockPiece p r N hN i x‖ +
            ∑ i ∈ s₂, ‖localizedBlockPiece p r N hN i x‖) := by
      rw [hsum₁, hsum₂]
      ring
    _ =
        omega N n *
          (∑ i ∈ Finset.Icc (j - 1) (j + 1),
              ‖localizedBlockPiece p r N hN i x‖ +
            ∑ i ∈ Finset.Icc (j - n / (N : ℤ) - 2)
                (j - n / (N : ℤ) + 2),
              ‖localizedBlockPiece p r N hN i x‖) := by
      rfl

theorem localizedMultiplierDifferenceNormSeqAsOuter_norm_le_eight
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (n : ℤ) (x : ellp p) :
    ‖localizedMultiplierDifferenceNormSeqAsOuter p r N hN n x‖ ≤
      8 * omega N n * ‖localizedBlockNormSeqAsOuter p r N hN x‖ := by
  classical
  let D₁ : Finset ℤ := Finset.Icc (-1 : ℤ) 1
  let D₂ : Finset ℤ := Finset.Icc (-2 : ℤ) 2
  let h : ℤ := n / (N : ℤ)
  let cℝ : ℝ := omega N n
  let cℂ : ℂ := (cℝ : ℂ)
  let B : ellp p := localizedBlockNormSeqAsOuter p r N hN x
  let u : ellp p := localizedMultiplierDifferenceNormSeqAsOuter p r N hN n x
  let f : ℤ → ellp p := fun d => cℂ • shiftOperator p (-d) B
  let g : ℤ → ellp p := fun d => cℂ • shiftOperator p (h - d) B
  have hc_nonneg : 0 ≤ cℝ := omega_nonneg N n
  have hB_coord (i : ℤ) :
      ‖B i‖ = ‖localizedBlockPiece p r N hN i x‖ := by
    simp [B, localizedBlockNormSeqAsOuter_apply, localizedBlockNormSeqC_norm,
      localizedBlockNormSeq_apply]
  have hf_coord (d j : ℤ) :
      ‖f d j‖ = cℝ * ‖localizedBlockPiece p r N hN (j + d) x‖ := by
    have hshift :
        (shiftOperator p (-d) B) j = B (j + d) := by
      simp [shiftOperator, reindexOperator, reindexLinearIsometryEquiv, shiftEquiv]
    dsimp [f]
    rw [hshift, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc_nonneg,
      hB_coord]
  have hg_coord (d j : ℤ) :
      ‖g d j‖ =
        cℝ * ‖localizedBlockPiece p r N hN (j - h + d) x‖ := by
    have hshift :
        (shiftOperator p (h - d) B) j = B (j - h + d) := by
      simp [shiftOperator, reindexOperator, reindexLinearIsometryEquiv, shiftEquiv]
      ring
    dsimp [g]
    rw [hshift, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc_nonneg,
      hB_coord]
  have hsum_left (j : ℤ) :
      ∑ d ∈ D₁, ‖f d j‖ =
        cℝ * ∑ i ∈ Finset.Icc (j - 1) (j + 1),
          ‖localizedBlockPiece p r N hN i x‖ := by
    calc
      ∑ d ∈ D₁, ‖f d j‖ =
          ∑ d ∈ D₁,
            cℝ * ‖localizedBlockPiece p r N hN (j + d) x‖ := by
        refine Finset.sum_congr rfl ?_
        intro d _hd
        rw [hf_coord]
      _ =
          cℝ * ∑ d ∈ D₁,
            ‖localizedBlockPiece p r N hN (j + d) x‖ := by
        rw [Finset.mul_sum]
      _ =
          cℝ * ∑ i ∈ Finset.Icc (j - 1) (j + 1),
            ‖localizedBlockPiece p r N hN i x‖ := by
        congr 1
        simpa [D₁, sub_eq_add_neg] using
          finset_sum_Icc_add_left_int (-1 : ℤ) 1 j
            (fun i => ‖localizedBlockPiece p r N hN i x‖)
  have hsum_right (j : ℤ) :
      ∑ d ∈ D₂, ‖g d j‖ =
        cℝ * ∑ i ∈ Finset.Icc (j - h - 2) (j - h + 2),
          ‖localizedBlockPiece p r N hN i x‖ := by
    calc
      ∑ d ∈ D₂, ‖g d j‖ =
          ∑ d ∈ D₂,
            cℝ * ‖localizedBlockPiece p r N hN (j - h + d) x‖ := by
        refine Finset.sum_congr rfl ?_
        intro d _hd
        rw [hg_coord]
      _ =
          cℝ * ∑ d ∈ D₂,
            ‖localizedBlockPiece p r N hN (j - h + d) x‖ := by
        rw [Finset.mul_sum]
      _ =
          cℝ * ∑ i ∈ Finset.Icc (j - h - 2) (j - h + 2),
            ‖localizedBlockPiece p r N hN i x‖ := by
        congr 1
        simpa [D₂, h, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
          finset_sum_Icc_add_left_int (-2 : ℤ) 2 (j - h)
            (fun i => ‖localizedBlockPiece p r N hN i x‖)
  have hpoint : ∀ j : ℤ, ‖u j‖ ≤
      ∑ d ∈ D₁, ‖f d j‖ + ∑ d ∈ D₂, ‖g d j‖ := by
    intro j
    have hblock :=
      localizedMultiplierDifferenceBlock_norm_le_omega_neighbor_sums
        p r N hN j n x
    have hu :
        ‖u j‖ = ‖localizedMultiplierDifferenceBlock p r N hN j n x‖ := by
      simp [u, localizedMultiplierDifferenceNormSeqAsOuter_apply,
        localizedMultiplierDifferenceNormSeqC_norm,
        localizedMultiplierDifferenceNormSeq_apply]
    calc
      ‖u j‖ = ‖localizedMultiplierDifferenceBlock p r N hN j n x‖ := hu
      _ ≤
          cℝ *
            (∑ i ∈ Finset.Icc (j - 1) (j + 1),
                ‖localizedBlockPiece p r N hN i x‖ +
              ∑ i ∈ Finset.Icc (j - h - 2) (j - h + 2),
                ‖localizedBlockPiece p r N hN i x‖) := by
        simpa [cℝ, h] using hblock
      _ =
          ∑ d ∈ D₁, ‖f d j‖ + ∑ d ∈ D₂, ‖g d j‖ := by
        rw [hsum_left j, hsum_right j]
        ring
  have houter :=
    lp_norm_le_two_finset_sum_norm_of_pointwise p D₁ D₂ u f g hpoint
  have hf_norm (d : ℤ) : ‖f d‖ = cℝ * ‖B‖ := by
    dsimp [f]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hc_nonneg, ellp_shift_isometry p (-d) B]
  have hg_norm (d : ℤ) : ‖g d‖ = cℝ * ‖B‖ := by
    dsimp [g]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hc_nonneg, ellp_shift_isometry p (h - d) B]
  have hD₁_card : D₁.card = 3 := by
    simpa [D₁] using neighbor_one_card (0 : ℤ)
  have hD₂_card : D₂.card = 5 := by
    simpa [D₂] using neighbor_two_card (0 : ℤ)
  have hsum_f_norm :
      ∑ d ∈ D₁, ‖f d‖ = 3 * cℝ * ‖B‖ := by
    calc
      ∑ d ∈ D₁, ‖f d‖ = ∑ d ∈ D₁, cℝ * ‖B‖ := by
        refine Finset.sum_congr rfl ?_
        intro d _hd
        rw [hf_norm]
      _ = (D₁.card : ℝ) * (cℝ * ‖B‖) := by simp
      _ = 3 * cℝ * ‖B‖ := by
        rw [hD₁_card]
        ring
  have hsum_g_norm :
      ∑ d ∈ D₂, ‖g d‖ = 5 * cℝ * ‖B‖ := by
    calc
      ∑ d ∈ D₂, ‖g d‖ = ∑ d ∈ D₂, cℝ * ‖B‖ := by
        refine Finset.sum_congr rfl ?_
        intro d _hd
        rw [hg_norm]
      _ = (D₂.card : ℝ) * (cℝ * ‖B‖) := by simp
      _ = 5 * cℝ * ‖B‖ := by
        rw [hD₂_card]
        ring
  calc
    ‖localizedMultiplierDifferenceNormSeqAsOuter p r N hN n x‖ =
        ‖u‖ := rfl
    _ ≤ ∑ d ∈ D₁, ‖f d‖ + ∑ d ∈ D₂, ‖g d‖ := houter
    _ = 8 * omega N n * ‖localizedBlockNormSeqAsOuter p r N hN x‖ := by
      rw [hsum_f_norm, hsum_g_norm]
      simp [B, cℝ]
      ring

theorem localized_multiplier_estimate
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (n : ℤ) (x : ellp p) :
    ‖localizedMultiplierDifferenceNormSeqAsOuter p r N hN n x‖ ≤
      8 * omega N n * ‖localizedBlockNormSeqAsOuter p r N hN x‖ :=
  localizedMultiplierDifferenceNormSeqAsOuter_norm_le_eight p r N hN n x

lemma localizedMultiplierDifferenceNormSeqAsOuter_weighted_summable_norm
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (a : ℤ → ℝ) (ha_nonneg : ∀ n : ℤ, 0 ≤ a n)
    (ha_sum : Summable fun n : ℤ => ‖a n‖)
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) :
    Summable fun n : ℤ =>
      ‖(a n : ℂ) • localizedMultiplierDifferenceNormSeqAsOuter p r N hN n x‖ := by
  let M : ℝ := ‖localizedBlockNormSeqAsOuter p r N hN x‖
  have hM_nonneg : 0 ≤ M := norm_nonneg _
  have hsumm : Summable fun n : ℤ => (8 * M) * ‖a n‖ :=
    ha_sum.mul_left (8 * M)
  refine Summable.of_norm_bounded hsumm ?_
  intro n
  have hdiff := localized_multiplier_estimate p r N hN n x
  have homega_bound : 8 * omega N n * M ≤ 8 * M := by
    nlinarith [omega_nonneg N n, omega_le_one N n, hM_nonneg]
  calc
    ‖‖(a n : ℂ) • localizedMultiplierDifferenceNormSeqAsOuter p r N hN n x‖‖ =
        ‖(a n : ℂ) • localizedMultiplierDifferenceNormSeqAsOuter p r N hN n x‖ := by
      rw [Real.norm_of_nonneg (norm_nonneg _)]
    _ = a n *
        ‖localizedMultiplierDifferenceNormSeqAsOuter p r N hN n x‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (ha_nonneg n)]
    _ ≤ a n * (8 * omega N n * M) := by
      exact mul_le_mul_of_nonneg_left hdiff (ha_nonneg n)
    _ ≤ a n * (8 * M) := by
      exact mul_le_mul_of_nonneg_left homega_bound (ha_nonneg n)
    _ = (8 * M) * ‖a n‖ := by
      rw [Real.norm_of_nonneg (ha_nonneg n)]
      ring

theorem localizedMultiplierDifferenceNormSeqAsOuter_norm_le
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (N : ℕ) (hN : 1 ≤ N) (n : ℤ) (x : ellp p) :
    ‖localizedMultiplierDifferenceNormSeqAsOuter p r N hN n x‖ ≤
      ‖localizedBlockNormSeqAsOuter p r N hN x‖ +
        ‖localizedBlockNormSeqAsOuter p r N hN
          (shiftOperator p n x)‖ := by
  let u : ellp p := localizedMultiplierDifferenceNormSeqAsOuter p r N hN n x
  let v : ellp p := localizedBlockNormSeqAsOuter p r N hN x
  let w : ellp p := localizedBlockNormSeqAsOuter p r N hN (shiftOperator p n x)
  have hpoint : ∀ j : ℤ, ‖u j‖ ≤ ‖(v + w) j‖ := by
    intro j
    have hu_coord :
        u j = localizedMultiplierDifferenceNormSeqC p r N hN n x j := by
      dsimp [u]
      rw [localizedMultiplierDifferenceNormSeqAsOuter_apply]
    have hv_coord :
        v j = (‖localizedBlockPiece p r N hN j x‖ : ℂ) := by
      dsimp [v]
      rw [localizedBlockNormSeqAsOuter_apply, localizedBlockNormSeqC_apply,
        localizedBlockNormSeq_apply]
    have hw_coord :
        w j =
          (‖localizedBlockPiece p r N hN j (shiftOperator p n x)‖ : ℂ) := by
      dsimp [w]
      rw [localizedBlockNormSeqAsOuter_apply, localizedBlockNormSeqC_apply,
        localizedBlockNormSeq_apply]
    have hvw_norm :
        ‖(v + w) j‖ = ‖v j‖ + ‖w j‖ := by
      rw [lp.coeFn_add, Pi.add_apply, hv_coord, hw_coord]
      rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)),
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)]
    calc
      ‖u j‖ = ‖localizedMultiplierDifferenceNormSeqC p r N hN n x j‖ := by
        rw [hu_coord]
      _ ≤
          ‖localizedBlockNormSeqAsOuter p r N hN x j‖ +
            ‖localizedBlockNormSeqAsOuter p r N hN
              (shiftOperator p n x) j‖ :=
        localizedMultiplierDifferenceNormSeqC_norm_le p r N hN n x j
      _ = ‖v j‖ + ‖w j‖ := by
        rfl
      _ = ‖(v + w) j‖ := hvw_norm.symm
  have houter := lp_norm_le_add_of_pointwise_norm_le_add p u v w hpoint
  exact houter

noncomputable def localizedCrossCommutatorBlock
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) (x : ellp p) : ellp r :=
  dominatedMatrixOperator r A a hA (localizedBlockPiece p r N hN j x) -
    localizedBlockPiece p r N hN j (dominatedMatrixOperator p A a hA x)

theorem localizedCrossCommutatorBlock_apply
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (j k : ℤ) (x : ellp p) :
    localizedCrossCommutatorBlock p r A a hA N hN j x k =
      tsum (fun l : ℤ =>
        (((hat N j l : ℂ) - (hat N j k : ℂ)) * A k l * x l)) := by
  simpa [localizedCrossCommutatorBlock] using
    matrixOperator_cross_commutator_apply p r A a hA N hN j k x

theorem localizedCrossCommutatorBlock_apply_crossHatCommutatorMatrix
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (j k : ℤ) (x : ellp p) :
    localizedCrossCommutatorBlock p r A a hA N hN j x k =
      tsum (fun l : ℤ => crossHatCommutatorMatrix A N j k l * x l) := by
  simpa [crossHatCommutatorMatrix] using
    localizedCrossCommutatorBlock_apply p r A a hA N hN j k x

lemma localizedCrossCommutatorDiagonal_summable_norm
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) (x : ellp p) :
    Summable fun n : ℤ =>
      ‖diagonalShiftOperator r A a hA n
        (localizedMultiplierDifferenceBlock p r N hN j n x)‖ := by
  let C : ℝ := (2 * ((2 * N + 1 : ℕ) : ℝ)) * ‖x‖
  have hC_nonneg : 0 ≤ C := by positivity
  have hsumm : Summable fun n : ℤ => C * ‖a n‖ :=
    hA.2.1.mul_left C
  refine Summable.of_norm_bounded hsumm ?_
  intro n
  have hdiag := diagonalShiftOperator_norm_le r A a hA n
  have hdiff :=
    localizedMultiplierDifferenceBlock_norm_le_two_card_mul_norm
      p r N hN j n x
  calc
    ‖‖diagonalShiftOperator r A a hA n
        (localizedMultiplierDifferenceBlock p r N hN j n x)‖‖ =
        ‖diagonalShiftOperator r A a hA n
          (localizedMultiplierDifferenceBlock p r N hN j n x)‖ := by
      rw [Real.norm_of_nonneg (norm_nonneg _)]
    _ ≤ ‖diagonalShiftOperator r A a hA n‖ *
        ‖localizedMultiplierDifferenceBlock p r N hN j n x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ a n * C := by
      exact mul_le_mul hdiag hdiff (norm_nonneg _) (hA.1 n)
    _ = C * ‖a n‖ := by
      rw [Real.norm_of_nonneg (hA.1 n)]
      ring

theorem localizedCrossCommutatorBlock_eq_diagonal_tsum
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) (x : ellp p) :
    localizedCrossCommutatorBlock p r A a hA N hN j x =
      ∑' n : ℤ,
        diagonalShiftOperator r A a hA n
          (localizedMultiplierDifferenceBlock p r N hN j n x) := by
  ext k
  let v : ℤ → ellp r := fun n =>
    diagonalShiftOperator r A a hA n
      (localizedMultiplierDifferenceBlock p r N hN j n x)
  have hsumm_norm :
      Summable fun n : ℤ => ‖v n‖ := by
    simpa [v] using
      localizedCrossCommutatorDiagonal_summable_norm p r A a hA N hN j x
  have hsumm_v : Summable v := hsumm_norm.of_norm
  have hcoord :
      (∑' n : ℤ, v n) k = ∑' n : ℤ, (v n) k := by
    let evalK : ellp r →L[ℂ] ℂ := coordCLM r k
    have hsum_coord : HasSum (fun n : ℤ => evalK (v n))
        (evalK (∑' n : ℤ, v n)) := by
      simpa [evalK, Function.comp_def] using
        hsumm_v.hasSum.map evalK evalK.continuous
    exact hsum_coord.tsum_eq.symm
  have hdiag_apply :
      (∑' n : ℤ, v n) k =
        ∑' n : ℤ,
          A k (k - n) *
            (((hat N j (k - n) : ℂ) - (hat N j k : ℂ)) * x (k - n)) := by
    rw [hcoord]
    apply tsum_congr
    intro n
    simp [v, diagonalShiftOperator_apply,
      localizedMultiplierDifferenceBlock_apply]
  rw [hdiag_apply]
  rw [localizedCrossCommutatorBlock_apply]
  symm
  calc
    (∑' n : ℤ,
        A k (k - n) *
          (((hat N j (k - n) : ℂ) - (hat N j k : ℂ)) * x (k - n))) =
        ∑' n : ℤ,
          (((hat N j (k - n) : ℂ) - (hat N j k : ℂ)) *
            A k (k - n) * x (k - n)) := by
      apply tsum_congr
      intro n
      ring
    _ = ∑' l : ℤ,
        (((hat N j l : ℂ) - (hat N j k : ℂ)) * A k l * x l) := by
      simpa [Function.comp_def] using
        (Equiv.subLeft k).tsum_eq
          (fun l : ℤ =>
            (((hat N j l : ℂ) - (hat N j k : ℂ)) * A k l * x l))

lemma localizedCrossCommutator_bound_series_summable
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) (x : ellp p) :
    Summable fun n : ℤ =>
      a n * ‖localizedMultiplierDifferenceBlock p r N hN j n x‖ := by
  let C : ℝ := (2 * ((2 * N + 1 : ℕ) : ℝ)) * ‖x‖
  have hC_nonneg : 0 ≤ C := by positivity
  have hsumm : Summable fun n : ℤ => C * ‖a n‖ :=
    hA.2.1.mul_left C
  refine Summable.of_norm_bounded hsumm ?_
  intro n
  have hdiff :=
    localizedMultiplierDifferenceBlock_norm_le_two_card_mul_norm
      p r N hN j n x
  calc
    ‖a n * ‖localizedMultiplierDifferenceBlock p r N hN j n x‖‖ =
        a n * ‖localizedMultiplierDifferenceBlock p r N hN j n x‖ := by
      rw [Real.norm_of_nonneg
        (mul_nonneg (hA.1 n) (norm_nonneg _))]
    _ ≤ a n * C := by
      exact mul_le_mul_of_nonneg_left hdiff (hA.1 n)
    _ = C * ‖a n‖ := by
      rw [Real.norm_of_nonneg (hA.1 n)]
      ring

theorem localizedCrossCommutatorBlock_norm_le_tsum_multiplier
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) (x : ellp p) :
    ‖localizedCrossCommutatorBlock p r A a hA N hN j x‖ ≤
      ∑' n : ℤ,
        a n * ‖localizedMultiplierDifferenceBlock p r N hN j n x‖ := by
  let v : ℤ → ellp r := fun n =>
    diagonalShiftOperator r A a hA n
      (localizedMultiplierDifferenceBlock p r N hN j n x)
  have hsumm_norm :
      Summable fun n : ℤ => ‖v n‖ := by
    simpa [v] using
      localizedCrossCommutatorDiagonal_summable_norm p r A a hA N hN j x
  have hseries :
      Summable fun n : ℤ =>
        a n * ‖localizedMultiplierDifferenceBlock p r N hN j n x‖ :=
    localizedCrossCommutator_bound_series_summable p r A a hA N hN j x
  have hpoint : ∀ n : ℤ,
      ‖v n‖ ≤
        a n * ‖localizedMultiplierDifferenceBlock p r N hN j n x‖ := by
    intro n
    calc
      ‖v n‖ ≤ ‖diagonalShiftOperator r A a hA n‖ *
          ‖localizedMultiplierDifferenceBlock p r N hN j n x‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ a n * ‖localizedMultiplierDifferenceBlock p r N hN j n x‖ := by
        exact mul_le_mul_of_nonneg_right
          (diagonalShiftOperator_norm_le r A a hA n) (norm_nonneg _)
  rw [localizedCrossCommutatorBlock_eq_diagonal_tsum p r A a hA N hN j x]
  calc
    ‖∑' n : ℤ, v n‖ ≤ ∑' n : ℤ, ‖v n‖ :=
      norm_tsum_le_tsum_norm hsumm_norm
    _ ≤ ∑' n : ℤ,
        a n * ‖localizedMultiplierDifferenceBlock p r N hN j n x‖ :=
      Summable.tsum_le_tsum hpoint hsumm_norm hseries

theorem localizedCrossCommutatorBlock_self_eq_crossHatCommutatorDominatedOperator
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) (x : ellp p) :
    localizedCrossCommutatorBlock p p A a hA N hN j x =
      dominatedMatrixOperator p (crossHatCommutatorMatrix A N j)
        (fun n : ℤ => a n * omega N n)
        (crossHatCommutatorMatrix_dominated A a hA N hN j) x := by
  ext k
  rw [localizedCrossCommutatorBlock_apply_crossHatCommutatorMatrix]
  exact ((dominatedMatrixOperator_isMatrixOperator p
    (crossHatCommutatorMatrix A N j)
    (fun n : ℤ => a n * omega N n)
    (crossHatCommutatorMatrix_dominated A a hA N hN j)) x k).2.symm

theorem localizedCrossCommutatorBlock_self_eq_neg_hatCommutatorOperator
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) (x : ellp p) :
    localizedCrossCommutatorBlock p p A a hA N hN j x =
      -hatCommutatorOperator p A a hA N j x := by
  unfold localizedCrossCommutatorBlock
  rw [localizedBlockPiece_eq_hatMultiplier p N hN j x,
    localizedBlockPiece_eq_hatMultiplier p N hN j
      (dominatedMatrixOperator p A a hA x)]
  unfold hatCommutatorOperator
  change dominatedMatrixOperator p A a hA (hatMultiplier p N j x) -
      hatMultiplier p N j (dominatedMatrixOperator p A a hA x) =
    -((hatMultiplier p N j).comp (dominatedMatrixOperator p A a hA) x -
      (dominatedMatrixOperator p A a hA).comp (hatMultiplier p N j) x)
  simp

theorem localizedCrossCommutatorBlock_self_norm_eq_hatCommutatorOperator
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) (x : ellp p) :
    ‖localizedCrossCommutatorBlock p p A a hA N hN j x‖ =
      ‖hatCommutatorOperator p A a hA N j x‖ := by
  rw [localizedCrossCommutatorBlock_self_eq_neg_hatCommutatorOperator
    p A a hA N hN j x, norm_neg]

theorem localizedCrossCommutatorBlock_self_norm_le
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) (x : ellp p) :
    ‖localizedCrossCommutatorBlock p p A a hA N hN j x‖ ≤
      tsum (fun n : ℤ => a n * omega N n) * ‖x‖ := by
  rw [localizedCrossCommutatorBlock_self_eq_crossHatCommutatorDominatedOperator
    p A a hA N hN j x]
  calc
    ‖dominatedMatrixOperator p (crossHatCommutatorMatrix A N j)
        (fun n : ℤ => a n * omega N n)
        (crossHatCommutatorMatrix_dominated A a hA N hN j) x‖ ≤
        ‖dominatedMatrixOperator p (crossHatCommutatorMatrix A N j)
          (fun n : ℤ => a n * omega N n)
          (crossHatCommutatorMatrix_dominated A a hA N hN j)‖ * ‖x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ tsum (fun n : ℤ => a n * omega N n) * ‖x‖ := by
      exact mul_le_mul_of_nonneg_right
        (crossHatCommutatorDominatedOperator_norm_le p A a hA N hN j)
        (norm_nonneg x)

theorem exists_one_le_and_forall_localizedCrossCommutatorBlock_self_norm_le
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∃ hN : 1 ≤ N,
      ∀ (j : ℤ) (x : ellp p),
        ‖localizedCrossCommutatorBlock p p A a hA N hN j x‖ ≤
          epsilon * ‖x‖ := by
  rcases exists_one_le_and_kernel_omega_tsum_lt a hA.2.1 hepsilon with
    ⟨N, hN, hsmall⟩
  refine ⟨N, hN, ?_⟩
  intro j x
  calc
    ‖localizedCrossCommutatorBlock p p A a hA N hN j x‖ ≤
        tsum (fun n : ℤ => a n * omega N n) * ‖x‖ :=
      localizedCrossCommutatorBlock_self_norm_le p A a hA N hN j x
    _ ≤ epsilon * ‖x‖ := by
      exact mul_le_mul_of_nonneg_right (le_of_lt hsmall) (norm_nonneg x)


noncomputable def localizedCrossCommutatorNormSeq
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) : ℤ → ℝ :=
  fun j => ‖localizedCrossCommutatorBlock p r A a hA N hN j x‖

theorem localizedCrossCommutatorNormSeq_apply
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) (j : ℤ) :
    localizedCrossCommutatorNormSeq p r A a hA N hN x j =
      ‖localizedCrossCommutatorBlock p r A a hA N hN j x‖ := by
  rfl

theorem localizedCrossCommutatorNormSeq_nonneg
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) (j : ℤ) :
    0 ≤ localizedCrossCommutatorNormSeq p r A a hA N hN x j :=
  norm_nonneg _


noncomputable def localizedCrossCommutatorNormSeqC
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) : ℤ → ℂ :=
  fun j => (localizedCrossCommutatorNormSeq p r A a hA N hN x j : ℂ)

theorem localizedCrossCommutatorNormSeqC_apply
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) (j : ℤ) :
    localizedCrossCommutatorNormSeqC p r A a hA N hN x j =
      (localizedCrossCommutatorNormSeq p r A a hA N hN x j : ℂ) := by
  rfl

theorem localizedCrossCommutatorNormSeqC_norm
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) (j : ℤ) :
    ‖localizedCrossCommutatorNormSeqC p r A a hA N hN x j‖ =
      localizedCrossCommutatorNormSeq p r A a hA N hN x j := by
  rw [localizedCrossCommutatorNormSeqC_apply, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg
    (localizedCrossCommutatorNormSeq_nonneg p r A a hA N hN x j)

theorem localizedCrossCommutatorNormSeqC_norm_le
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) (j : ℤ) :
    ‖localizedCrossCommutatorNormSeqC p r A a hA N hN x j‖ ≤
      ‖dominatedMatrixOperator r A a hA‖ *
          ‖localizedBlockNormSeqAsOuter p r N hN x j‖ +
        ‖localizedBlockNormSeqAsOuter p r N hN
          (dominatedMatrixOperator p A a hA x) j‖ := by
  have hblock_x :
      ‖localizedBlockNormSeqAsOuter p r N hN x j‖ =
        ‖localizedBlockPiece p r N hN j x‖ := by
    rw [localizedBlockNormSeqAsOuter_apply, localizedBlockNormSeqC_norm,
      localizedBlockNormSeq_apply]
  have hblock_Bx :
      ‖localizedBlockNormSeqAsOuter p r N hN
          (dominatedMatrixOperator p A a hA x) j‖ =
        ‖localizedBlockPiece p r N hN j
          (dominatedMatrixOperator p A a hA x)‖ := by
    rw [localizedBlockNormSeqAsOuter_apply, localizedBlockNormSeqC_norm,
      localizedBlockNormSeq_apply]
  rw [localizedCrossCommutatorNormSeqC_norm,
    localizedCrossCommutatorNormSeq_apply]
  unfold localizedCrossCommutatorBlock
  calc
    ‖dominatedMatrixOperator r A a hA
          (localizedBlockPiece p r N hN j x) -
        localizedBlockPiece p r N hN j
          (dominatedMatrixOperator p A a hA x)‖ ≤
        ‖dominatedMatrixOperator r A a hA
            (localizedBlockPiece p r N hN j x)‖ +
          ‖localizedBlockPiece p r N hN j
            (dominatedMatrixOperator p A a hA x)‖ :=
      norm_sub_le _ _
    _ ≤
        ‖dominatedMatrixOperator r A a hA‖ *
            ‖localizedBlockNormSeqAsOuter p r N hN x j‖ +
          ‖localizedBlockNormSeqAsOuter p r N hN
            (dominatedMatrixOperator p A a hA x) j‖ := by
      refine add_le_add ?_ ?_
      · calc
          ‖dominatedMatrixOperator r A a hA
              (localizedBlockPiece p r N hN j x)‖ ≤
              ‖dominatedMatrixOperator r A a hA‖ *
                ‖localizedBlockPiece p r N hN j x‖ :=
            ContinuousLinearMap.le_opNorm _ _
          _ =
              ‖dominatedMatrixOperator r A a hA‖ *
                ‖localizedBlockNormSeqAsOuter p r N hN x j‖ := by
            rw [hblock_x]
      · simp [hblock_Bx]


noncomputable def localizedCrossCommutatorNormSeqAsOuter
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) : ellp p :=
  ⟨localizedCrossCommutatorNormSeqC p r A a hA N hN x, by
    have hblock_x : Memℓp
        (fun j : ℤ => ‖localizedBlockNormSeqAsOuter p r N hN x j‖) p :=
      (lp.memℓp (localizedBlockNormSeqAsOuter p r N hN x)).norm
    have hleft : Memℓp
        (fun j : ℤ =>
          ‖dominatedMatrixOperator r A a hA‖ *
            ‖localizedBlockNormSeqAsOuter p r N hN x j‖) p :=
      hblock_x.const_mul ‖dominatedMatrixOperator r A a hA‖
    have hright : Memℓp
        (fun j : ℤ =>
          ‖localizedBlockNormSeqAsOuter p r N hN
            (dominatedMatrixOperator p A a hA x) j‖) p :=
      (lp.memℓp
        (localizedBlockNormSeqAsOuter p r N hN
          (dominatedMatrixOperator p A a hA x))).norm
    exact (hleft.add hright).mono
      (localizedCrossCommutatorNormSeqC_norm_le p r A a hA N hN x)⟩

theorem localizedCrossCommutatorNormSeqAsOuter_apply
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) (j : ℤ) :
    localizedCrossCommutatorNormSeqAsOuter p r A a hA N hN x j =
      localizedCrossCommutatorNormSeqC p r A a hA N hN x j := by
  rfl

theorem localizedCrossCommutatorNormSeqAsOuter_norm_le
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) :
    ‖localizedCrossCommutatorNormSeqAsOuter p r A a hA N hN x‖ ≤
      ‖dominatedMatrixOperator r A a hA‖ *
          ‖localizedBlockNormSeqAsOuter p r N hN x‖ +
        ‖localizedBlockNormSeqAsOuter p r N hN
          (dominatedMatrixOperator p A a hA x)‖ := by
  let u : ellp p :=
    localizedCrossCommutatorNormSeqAsOuter p r A a hA N hN x
  let v : ellp p :=
    (‖dominatedMatrixOperator r A a hA‖ : ℂ) •
      localizedBlockNormSeqAsOuter p r N hN x
  let w : ellp p :=
    localizedBlockNormSeqAsOuter p r N hN
      (dominatedMatrixOperator p A a hA x)
  have hpoint : ∀ j : ℤ, ‖u j‖ ≤ ‖(v + w) j‖ := by
    intro j
    have hu_coord :
        u j = localizedCrossCommutatorNormSeqC p r A a hA N hN x j := by
      dsimp [u]
      rw [localizedCrossCommutatorNormSeqAsOuter_apply]
    have hx_coord :
        localizedBlockNormSeqAsOuter p r N hN x j =
          (‖localizedBlockPiece p r N hN j x‖ : ℂ) := by
      rw [localizedBlockNormSeqAsOuter_apply, localizedBlockNormSeqC_apply,
        localizedBlockNormSeq_apply]
    have hBx_coord :
        w j =
          (‖localizedBlockPiece p r N hN j
            (dominatedMatrixOperator p A a hA x)‖ : ℂ) := by
      dsimp [w]
      rw [localizedBlockNormSeqAsOuter_apply, localizedBlockNormSeqC_apply,
        localizedBlockNormSeq_apply]
    have hv_coord :
        v j =
          (‖dominatedMatrixOperator r A a hA‖ *
            ‖localizedBlockNormSeqAsOuter p r N hN x j‖ : ℂ) := by
      change
        (((‖dominatedMatrixOperator r A a hA‖ : ℂ) •
            localizedBlockNormSeqAsOuter p r N hN x : ellp p) j) =
          (‖dominatedMatrixOperator r A a hA‖ *
            ‖localizedBlockNormSeqAsOuter p r N hN x j‖ : ℂ)
      rw [lp.coeFn_smul, Pi.smul_apply, hx_coord, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), smul_eq_mul]
    have hvw_norm :
        ‖(v + w) j‖ =
          ‖dominatedMatrixOperator r A a hA‖ *
              ‖localizedBlockNormSeqAsOuter p r N hN x j‖ +
            ‖localizedBlockNormSeqAsOuter p r N hN
              (dominatedMatrixOperator p A a hA x) j‖ := by
      rw [lp.coeFn_add, Pi.add_apply, hv_coord, hBx_coord]
      rw [localizedBlockNormSeqAsOuter_apply, localizedBlockNormSeqC_norm,
        localizedBlockNormSeq_apply]
      rw [← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg
          (add_nonneg
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
            (norm_nonneg _)),
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    calc
      ‖u j‖ = ‖localizedCrossCommutatorNormSeqC p r A a hA N hN x j‖ := by
        rw [hu_coord]
      _ ≤
          ‖dominatedMatrixOperator r A a hA‖ *
              ‖localizedBlockNormSeqAsOuter p r N hN x j‖ +
            ‖localizedBlockNormSeqAsOuter p r N hN
              (dominatedMatrixOperator p A a hA x) j‖ :=
        localizedCrossCommutatorNormSeqC_norm_le p r A a hA N hN x j
      _ = ‖(v + w) j‖ := hvw_norm.symm
  have houter := lp_norm_le_add_of_pointwise_norm_le_add p u v w hpoint
  have hv_norm :
      ‖v‖ =
        ‖dominatedMatrixOperator r A a hA‖ *
          ‖localizedBlockNormSeqAsOuter p r N hN x‖ := by
    change
      ‖(‖dominatedMatrixOperator r A a hA‖ : ℂ) •
          localizedBlockNormSeqAsOuter p r N hN x‖ =
        ‖dominatedMatrixOperator r A a hA‖ *
          ‖localizedBlockNormSeqAsOuter p r N hN x‖
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
  calc
    ‖localizedCrossCommutatorNormSeqAsOuter p r A a hA N hN x‖ = ‖u‖ := rfl
    _ ≤ ‖v‖ + ‖w‖ := houter
    _ =
        ‖dominatedMatrixOperator r A a hA‖ *
            ‖localizedBlockNormSeqAsOuter p r N hN x‖ +
          ‖localizedBlockNormSeqAsOuter p r N hN
            (dominatedMatrixOperator p A a hA x)‖ := by
      rw [hv_norm]

theorem localizedCrossCommutatorNormSeqAsOuter_norm_le_tsum_multiplier
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) :
    ‖localizedCrossCommutatorNormSeqAsOuter p r A a hA N hN x‖ ≤
      ∑' n : ℤ,
        a n * ‖localizedMultiplierDifferenceNormSeqAsOuter p r N hN n x‖ := by
  let u : ellp p :=
    localizedCrossCommutatorNormSeqAsOuter p r A a hA N hN x
  let D : ℤ → ellp p :=
    fun n => localizedMultiplierDifferenceNormSeqAsOuter p r N hN n x
  let w : ℤ → ellp p := fun n => (a n : ℂ) • D n
  let z : ellp p := ∑' n : ℤ, w n
  have hsumm_norm : Summable fun n : ℤ => ‖w n‖ := by
    simpa [w, D] using
      localizedMultiplierDifferenceNormSeqAsOuter_weighted_summable_norm
        p r a hA.1 hA.2.1 N hN x
  have hsumm_w : Summable w := hsumm_norm.of_norm
  have hcoord (j : ℤ) :
      z j = ∑' n : ℤ, w n j := by
    let evalJ : ellp p →L[ℂ] ℂ := coordCLM p j
    have hsum_coord : HasSum (fun n : ℤ => evalJ (w n))
        (evalJ z) := by
      simpa [z, evalJ, Function.comp_def] using
        hsumm_w.hasSum.map evalJ evalJ.continuous
    exact hsum_coord.tsum_eq.symm
  have hw_coord (n j : ℤ) :
      w n j =
        ((a n * localizedMultiplierDifferenceNormSeq p r N hN n x j : ℝ) : ℂ) := by
    change
      (((a n : ℂ) • localizedMultiplierDifferenceNormSeqAsOuter p r N hN n x :
          ellp p) j) =
        ((a n * localizedMultiplierDifferenceNormSeq p r N hN n x j : ℝ) : ℂ)
    rw [lp.coeFn_smul, Pi.smul_apply,
      localizedMultiplierDifferenceNormSeqAsOuter_apply,
      localizedMultiplierDifferenceNormSeqC_apply, smul_eq_mul,
      ← Complex.ofReal_mul]
  have hz_coord (j : ℤ) :
      z j =
        ((∑' n : ℤ,
          a n * localizedMultiplierDifferenceNormSeq p r N hN n x j : ℝ) : ℂ) := by
    calc
      z j = ∑' n : ℤ, w n j := hcoord j
      _ =
          ∑' n : ℤ,
            ((a n * localizedMultiplierDifferenceNormSeq p r N hN n x j : ℝ) : ℂ) := by
        exact tsum_congr fun n => hw_coord n j
      _ =
          ((∑' n : ℤ,
            a n * localizedMultiplierDifferenceNormSeq p r N hN n x j : ℝ) : ℂ) := by
        exact (Complex.ofReal_tsum
          (fun n : ℤ =>
            a n * localizedMultiplierDifferenceNormSeq p r N hN n x j)).symm
  have hz_norm (j : ℤ) :
      ‖z j‖ =
        ∑' n : ℤ,
          a n * localizedMultiplierDifferenceNormSeq p r N hN n x j := by
    rw [hz_coord j, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (tsum_nonneg fun n =>
      mul_nonneg (hA.1 n)
        (localizedMultiplierDifferenceNormSeq_nonneg p r N hN n x j))
  have hpoint : ∀ j : ℤ, ‖u j‖ ≤ ‖z j‖ := by
    intro j
    have hblock :=
      localizedCrossCommutatorBlock_norm_le_tsum_multiplier
        p r A a hA N hN j x
    have hu_norm :
        ‖u j‖ =
          ‖localizedCrossCommutatorBlock p r A a hA N hN j x‖ := by
      dsimp [u]
      rw [localizedCrossCommutatorNormSeqAsOuter_apply,
        localizedCrossCommutatorNormSeqC_norm,
        localizedCrossCommutatorNormSeq_apply]
    calc
      ‖u j‖ =
          ‖localizedCrossCommutatorBlock p r A a hA N hN j x‖ := hu_norm
      _ ≤ ∑' n : ℤ,
          a n * ‖localizedMultiplierDifferenceBlock p r N hN j n x‖ :=
        hblock
      _ = ∑' n : ℤ,
          a n * localizedMultiplierDifferenceNormSeq p r N hN n x j := by
        apply tsum_congr
        intro n
        rw [localizedMultiplierDifferenceNormSeq_apply]
      _ = ‖z j‖ := (hz_norm j).symm
  have hp_ne_zero : p ≠ 0 :=
    (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hmono : ‖u‖ ≤ ‖z‖ :=
    lp.norm_mono (p := p) (E := fun _ : ℤ => ℂ)
      (F := fun _ : ℤ => ℂ) hp_ne_zero hpoint
  have hnorm_tsum : ‖z‖ ≤ ∑' n : ℤ, ‖w n‖ := by
    dsimp [z]
    exact norm_tsum_le_tsum_norm hsumm_norm
  have hsum_norm :
      (∑' n : ℤ, ‖w n‖) =
        ∑' n : ℤ, a n * ‖D n‖ := by
    apply tsum_congr
    intro n
    change ‖(a n : ℂ) • D n‖ = a n * ‖D n‖
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hA.1 n)]
  calc
    ‖localizedCrossCommutatorNormSeqAsOuter p r A a hA N hN x‖ = ‖u‖ := rfl
    _ ≤ ‖z‖ := hmono
    _ ≤ ∑' n : ℤ, ‖w n‖ := hnorm_tsum
    _ = ∑' n : ℤ,
        a n * ‖localizedMultiplierDifferenceNormSeqAsOuter p r N hN n x‖ := by
      simpa [D] using hsum_norm

theorem localizedCrossCommutatorNormSeqAsOuter_norm_le_kernel_omega
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (x : ellp p) :
    ‖localizedCrossCommutatorNormSeqAsOuter p r A a hA N hN x‖ ≤
      (8 * ∑' n : ℤ, a n * omega N n) *
        ‖localizedBlockNormSeqAsOuter p r N hN x‖ := by
  let M : ℝ := ‖localizedBlockNormSeqAsOuter p r N hN x‖
  let D : ℤ → ellp p :=
    fun n => localizedMultiplierDifferenceNormSeqAsOuter p r N hN n x
  have hM_nonneg : 0 ≤ M := norm_nonneg _
  have hleft_summ : Summable fun n : ℤ => a n * ‖D n‖ := by
    have hsumm : Summable fun n : ℤ => (8 * M) * ‖a n‖ :=
      hA.2.1.mul_left (8 * M)
    refine Summable.of_norm_bounded hsumm ?_
    intro n
    have hdiff : ‖D n‖ ≤ 8 * omega N n * M := by
      simpa [D, M] using localized_multiplier_estimate p r N hN n x
    have homega_bound : 8 * omega N n * M ≤ 8 * M := by
      nlinarith [omega_nonneg N n, omega_le_one N n, hM_nonneg]
    calc
      ‖a n * ‖D n‖‖ =
          a n * ‖D n‖ := by
        rw [Real.norm_of_nonneg
          (mul_nonneg (hA.1 n) (norm_nonneg _))]
      _ ≤ a n * (8 * omega N n * M) := by
        exact mul_le_mul_of_nonneg_left hdiff (hA.1 n)
      _ ≤ a n * (8 * M) := by
        exact mul_le_mul_of_nonneg_left homega_bound (hA.1 n)
      _ = (8 * M) * ‖a n‖ := by
        rw [Real.norm_of_nonneg (hA.1 n)]
        ring
  have hkernel_summ : Summable fun n : ℤ => a n * omega N n :=
    summable_kernel_mul_omega a hA.2.1 N
  have hright_summ :
      Summable fun n : ℤ => a n * (8 * omega N n * M) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      hkernel_summ.mul_right (8 * M)
  have hpoint :
      ∀ n : ℤ, a n * ‖D n‖ ≤ a n * (8 * omega N n * M) := by
    intro n
    have hdiff : ‖D n‖ ≤ 8 * omega N n * M := by
      simpa [D, M] using localized_multiplier_estimate p r N hN n x
    exact mul_le_mul_of_nonneg_left hdiff (hA.1 n)
  have htsum_le :
      (∑' n : ℤ, a n * ‖D n‖) ≤
        ∑' n : ℤ, a n * (8 * omega N n * M) :=
    Summable.tsum_le_tsum hpoint hleft_summ hright_summ
  have hright_eq :
      (∑' n : ℤ, a n * (8 * omega N n * M)) =
        (8 * ∑' n : ℤ, a n * omega N n) * M := by
    calc
      (∑' n : ℤ, a n * (8 * omega N n * M)) =
          ∑' n : ℤ, (a n * omega N n) * (8 * M) := by
        apply tsum_congr
        intro n
        ring
      _ = (∑' n : ℤ, a n * omega N n) * (8 * M) := by
        exact Summable.tsum_mul_right (8 * M) hkernel_summ
      _ = (8 * ∑' n : ℤ, a n * omega N n) * M := by
        ring
  calc
    ‖localizedCrossCommutatorNormSeqAsOuter p r A a hA N hN x‖ ≤
        ∑' n : ℤ, a n * ‖D n‖ := by
      simpa [D] using
        localizedCrossCommutatorNormSeqAsOuter_norm_le_tsum_multiplier
          p r A a hA N hN x
    _ ≤ ∑' n : ℤ, a n * (8 * omega N n * M) := htsum_le
    _ =
        (8 * ∑' n : ℤ, a n * omega N n) *
          ‖localizedBlockNormSeqAsOuter p r N hN x‖ := by
      simpa [M] using hright_eq

theorem localized_lower_bound_with_commutator_error
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (j : ℤ) {c : ℝ}
    (hbound : ∀ y : ellp p,
      c * ‖y‖ ≤ ‖dominatedMatrixOperator p A a hA y‖)
    (x : ellp p) :
    c * ‖hatMultiplier p N j x‖ ≤
      ‖hatMultiplier p N j (dominatedMatrixOperator p A a hA x)‖ +
        ‖hatCommutatorOperator p A a hA N j x‖ := by
  have hloc := hbound (hatMultiplier p N j x)
  have htriangle :
      ‖dominatedMatrixOperator p A a hA (hatMultiplier p N j x)‖ ≤
        ‖hatMultiplier p N j (dominatedMatrixOperator p A a hA x)‖ +
          ‖hatCommutatorOperator p A a hA N j x‖ := by
    have hcomm :
        hatCommutatorOperator p A a hA N j x =
          hatMultiplier p N j (dominatedMatrixOperator p A a hA x) -
            dominatedMatrixOperator p A a hA (hatMultiplier p N j x) := by
      rfl
    have hrepr :
        dominatedMatrixOperator p A a hA (hatMultiplier p N j x) =
          hatMultiplier p N j (dominatedMatrixOperator p A a hA x) -
            hatCommutatorOperator p A a hA N j x := by
      rw [hcomm]
      abel
    rw [hrepr]
    exact norm_sub_le _ _
  exact hloc.trans htriangle

theorem localized_lower_bound_cross_with_commutator_error
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) (j : ℤ) {c : ℝ}
    (hbound : ∀ y : ellp r,
      c * ‖y‖ ≤ ‖dominatedMatrixOperator r A a hA y‖)
    (x : ellp p) :
    c * ‖localizedBlockPiece p r N hN j x‖ ≤
      ‖localizedBlockPiece p r N hN j
          (dominatedMatrixOperator p A a hA x)‖ +
        ‖dominatedMatrixOperator r A a hA
            (localizedBlockPiece p r N hN j x) -
          localizedBlockPiece p r N hN j
            (dominatedMatrixOperator p A a hA x)‖ := by
  have hloc := hbound (localizedBlockPiece p r N hN j x)
  have htriangle :
      ‖dominatedMatrixOperator r A a hA
          (localizedBlockPiece p r N hN j x)‖ ≤
        ‖localizedBlockPiece p r N hN j
            (dominatedMatrixOperator p A a hA x)‖ +
          ‖dominatedMatrixOperator r A a hA
              (localizedBlockPiece p r N hN j x) -
            localizedBlockPiece p r N hN j
              (dominatedMatrixOperator p A a hA x)‖ := by
    let u : ellp r :=
      dominatedMatrixOperator r A a hA
        (localizedBlockPiece p r N hN j x)
    let v : ellp r :=
      localizedBlockPiece p r N hN j
        (dominatedMatrixOperator p A a hA x)
    change ‖u‖ ≤ ‖v‖ + ‖u - v‖
    have hrepr : u = v + (u - v) := by
      abel
    calc
      ‖u‖ = ‖v + (u - v)‖ := by
        exact congrArg (fun z : ellp r => ‖z‖) hrepr
      _ ≤ ‖v‖ + ‖u - v‖ := norm_add_le _ _
  exact hloc.trans htriangle

theorem localized_outer_lower_bound_with_commutator_error
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (N : ℕ) (hN : 1 ≤ N) {c : ℝ} (hc_nonneg : 0 ≤ c)
    (hbound : ∀ y : ellp r,
      c * ‖y‖ ≤ ‖dominatedMatrixOperator r A a hA y‖)
    (x : ellp p) :
    c * ‖localizedBlockNormSeqAsOuter p r N hN x‖ ≤
      ‖localizedBlockNormSeqAsOuter p r N hN
          (dominatedMatrixOperator p A a hA x)‖ +
        ‖localizedCrossCommutatorNormSeqAsOuter p r A a hA N hN x‖ := by
  let u : ellp p :=
    (c : ℂ) • localizedBlockNormSeqAsOuter p r N hN x
  let v : ellp p :=
    localizedBlockNormSeqAsOuter p r N hN
      (dominatedMatrixOperator p A a hA x)
  let w : ellp p :=
    localizedCrossCommutatorNormSeqAsOuter p r A a hA N hN x
  have hpoint : ∀ j : ℤ, ‖u j‖ ≤ ‖(v + w) j‖ := by
    intro j
    have hblock :=
      localized_lower_bound_cross_with_commutator_error
        p r A a hA N hN j hbound x
    have hu_norm :
        ‖u j‖ = c * ‖localizedBlockPiece p r N hN j x‖ := by
      change
        ‖(((c : ℂ) • localizedBlockNormSeqAsOuter p r N hN x : ellp p) j)‖ =
          c * ‖localizedBlockPiece p r N hN j x‖
      rw [lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hc_nonneg, localizedBlockNormSeqAsOuter_apply,
        localizedBlockNormSeqC_norm, localizedBlockNormSeq_apply]
    have hv_coord :
        v j =
          (‖localizedBlockPiece p r N hN j
            (dominatedMatrixOperator p A a hA x)‖ : ℂ) := by
      dsimp [v]
      rw [localizedBlockNormSeqAsOuter_apply, localizedBlockNormSeqC_apply,
        localizedBlockNormSeq_apply]
    have hw_coord :
        w j =
          (‖localizedCrossCommutatorBlock p r A a hA N hN j x‖ : ℂ) := by
      dsimp [w]
      rw [localizedCrossCommutatorNormSeqAsOuter_apply,
        localizedCrossCommutatorNormSeqC_apply,
        localizedCrossCommutatorNormSeq_apply]
    have hv_norm :
        ‖v j‖ =
          ‖localizedBlockPiece p r N hN j
            (dominatedMatrixOperator p A a hA x)‖ := by
      rw [hv_coord, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _)]
    have hw_norm :
        ‖w j‖ =
          ‖localizedCrossCommutatorBlock p r A a hA N hN j x‖ := by
      rw [hw_coord, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _)]
    have hvw_norm :
        ‖(v + w) j‖ = ‖v j‖ + ‖w j‖ := by
      rw [lp.coeFn_add, Pi.add_apply, hv_coord, hw_coord]
      rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)),
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)]
    calc
      ‖u j‖ = c * ‖localizedBlockPiece p r N hN j x‖ := hu_norm
      _ ≤
          ‖localizedBlockPiece p r N hN j
              (dominatedMatrixOperator p A a hA x)‖ +
            ‖localizedCrossCommutatorBlock p r A a hA N hN j x‖ := by
        simpa [localizedCrossCommutatorBlock] using hblock
      _ = ‖v j‖ + ‖w j‖ := by
        rw [hv_norm, hw_norm]
      _ = ‖(v + w) j‖ := hvw_norm.symm
  have houter := lp_norm_le_add_of_pointwise_norm_le_add p u v w hpoint
  have hu_norm :
      ‖u‖ = c * ‖localizedBlockNormSeqAsOuter p r N hN x‖ := by
    change
      ‖(c : ℂ) • localizedBlockNormSeqAsOuter p r N hN x‖ =
        c * ‖localizedBlockNormSeqAsOuter p r N hN x‖
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hc_nonneg]
  calc
    c * ‖localizedBlockNormSeqAsOuter p r N hN x‖ = ‖u‖ := hu_norm.symm
    _ ≤ ‖v‖ + ‖w‖ := houter
    _ =
        ‖localizedBlockNormSeqAsOuter p r N hN
            (dominatedMatrixOperator p A a hA x)‖ +
          ‖localizedCrossCommutatorNormSeqAsOuter p r A a hA N hN x‖ := by
      rfl

theorem dominatedMatrixOperator_boundedBelow_of_matrixBoundedBelow
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (hbelow : MatrixBoundedBelowOn p A) :
    OperatorBoundedBelow (dominatedMatrixOperator p A a hA) := by
  rcases hbelow with ⟨T, hT, c, hc_pos, hbound⟩
  refine ⟨c, hc_pos, ?_⟩
  intro x
  have huniq : T = dominatedMatrixOperator p A a hA :=
    isMatrixOperator_unique p A T (dominatedMatrixOperator p A a hA) hT
      (dominatedMatrixOperator_isMatrixOperator p A a hA)
  simpa [huniq] using hbound x

theorem matrixBoundedBelowOn_dominatedMatrixOperator
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ) (hA : MatrixDominatedBy A a)
    (hbelow : MatrixBoundedBelowOn p A) :
    MatrixBoundedBelowOn p A :=
  ⟨dominatedMatrixOperator p A a hA,
    dominatedMatrixOperator_isMatrixOperator p A a hA,
    dominatedMatrixOperator_boundedBelow_of_matrixBoundedBelow p A a hA hbelow⟩

theorem matrixBoundedBelowOn_of_dominatedMatrixOperator_opNorm_sub_lt
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A B : ℤ → ℤ → ℂ) (a b : ℤ → ℝ)
    (hA : MatrixDominatedBy A a) (hB : MatrixDominatedBy B b)
    {c : ℝ}
    (hbelow : ∀ x : ellp p,
      c * ‖x‖ ≤ ‖dominatedMatrixOperator p A a hA x‖)
    (hclose : ‖dominatedMatrixOperator p B b hB -
      dominatedMatrixOperator p A a hA‖ < c) :
    MatrixBoundedBelowOn p B := by
  refine ⟨dominatedMatrixOperator p B b hB,
    dominatedMatrixOperator_isMatrixOperator p B b hB, ?_⟩
  exact operatorBoundedBelow_of_opNorm_sub_lt p
    (dominatedMatrixOperator p A a hA)
    (dominatedMatrixOperator p B b hB) hbelow hclose

theorem matrixBoundedBelowOn_of_dominatedMatrixOperator_close
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A B : ℤ → ℤ → ℂ) (a b : ℤ → ℝ)
    (hA : MatrixDominatedBy A a) (hB : MatrixDominatedBy B b)
    (hbelow : MatrixBoundedBelowOn p A) :
    ∃ c : ℝ, 0 < c ∧
      (‖dominatedMatrixOperator p B b hB -
        dominatedMatrixOperator p A a hA‖ < c →
        MatrixBoundedBelowOn p B) := by
  rcases dominatedMatrixOperator_boundedBelow_of_matrixBoundedBelow p A a hA hbelow with
    ⟨c, hc_pos, hbound⟩
  exact ⟨c, hc_pos, fun hclose =>
    matrixBoundedBelowOn_of_dominatedMatrixOperator_opNorm_sub_lt
      p A B a b hA hB hbound hclose⟩

theorem propagate_lower_bound
    (A : ℤ → ℤ → ℂ) (a : ℤ → ℝ)
    (hA : MatrixDominatedBy A a)
    (r : ℝ≥0∞) [Fact (1 ≤ r)]
    (hr : MatrixBoundedBelowOn r A) :
    ∀ p : ℝ≥0∞, [Fact (1 ≤ p)] → MatrixBoundedBelowOn p A := by
  rcases dominatedMatrixOperator_boundedBelow_of_matrixBoundedBelow
      r A a hA hr with
    ⟨c, hc_pos, hbound_r⟩
  have hepsilon : 0 < c / 16 := by positivity
  rcases exists_one_le_and_kernel_omega_tsum_lt a hA.2.1 hepsilon with
    ⟨N, hN, hsmall⟩
  have hsmall_half :
      8 * (∑' n : ℤ, a n * omega N n) ≤ c / 2 := by
    nlinarith [hsmall]
  intro p hp
  letI : Fact (1 ≤ p) := hp
  rcases localizedBlockNormSeqAsOuter_equiv_norm p r N hN with
    ⟨α, β, hα_pos, hβ_pos, hequiv⟩
  let γ : ℝ := ((c / 2) * α) / β
  have hγ_pos : 0 < γ := by
    exact div_pos (mul_pos (by positivity) hα_pos) hβ_pos
  refine ⟨dominatedMatrixOperator p A a hA,
    dominatedMatrixOperator_isMatrixOperator p A a hA, γ, hγ_pos, ?_⟩
  intro x
  let Bp : ellp p →L[ℂ] ellp p := dominatedMatrixOperator p A a hA
  let Mx : ellp p := localizedBlockNormSeqAsOuter p r N hN x
  let MBx : ellp p := localizedBlockNormSeqAsOuter p r N hN (Bp x)
  let Cx : ellp p := localizedCrossCommutatorNormSeqAsOuter p r A a hA N hN x
  have hloc :
      c * ‖Mx‖ ≤ ‖MBx‖ + ‖Cx‖ := by
    simpa [Bp, Mx, MBx, Cx] using
      localized_outer_lower_bound_with_commutator_error
        p r A a hA N hN (le_of_lt hc_pos) hbound_r x
  have hcomm :
      ‖Cx‖ ≤ (c / 2) * ‖Mx‖ := by
    have hkernel :=
      localizedCrossCommutatorNormSeqAsOuter_norm_le_kernel_omega
        p r A a hA N hN x
    calc
      ‖Cx‖ ≤
          (8 * ∑' n : ℤ, a n * omega N n) * ‖Mx‖ := by
        simpa [Mx, Cx] using hkernel
      _ ≤ (c / 2) * ‖Mx‖ := by
        exact mul_le_mul_of_nonneg_right hsmall_half (norm_nonneg _)
  have habsorb : (c / 2) * ‖Mx‖ ≤ ‖MBx‖ := by
    nlinarith [hloc, hcomm]
  have hMx_lower : α * ‖x‖ ≤ ‖Mx‖ := by
    simpa [Mx] using (hequiv x).1
  have hMBx_upper : ‖MBx‖ ≤ β * ‖Bp x‖ := by
    simpa [Bp, MBx] using (hequiv (Bp x)).2
  have hlocalized :
      (c / 2) * (α * ‖x‖) ≤ β * ‖Bp x‖ := by
    calc
      (c / 2) * (α * ‖x‖) ≤ (c / 2) * ‖Mx‖ := by
        exact mul_le_mul_of_nonneg_left hMx_lower (by positivity)
      _ ≤ ‖MBx‖ := habsorb
      _ ≤ β * ‖Bp x‖ := hMBx_upper
  calc
    γ * ‖x‖ =
        β⁻¹ * ((c / 2) * (α * ‖x‖)) := by
      dsimp [γ]
      field_simp [hβ_pos.ne']
    _ ≤ β⁻¹ * (β * ‖Bp x‖) := by
      exact mul_le_mul_of_nonneg_left hlocalized
        (inv_nonneg.mpr hβ_pos.le)
    _ = ‖dominatedMatrixOperator p A a hA x‖ := by
      field_simp [Bp, hβ_pos.ne']
      rfl

end VendorE2.Lean_Code
