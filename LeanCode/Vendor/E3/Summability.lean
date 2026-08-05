import LeanCode.Vendor.E3.Defs

open MeasureTheory
open scoped ENNReal

namespace VendorE3
noncomputable section









def latticeDecay (a σ y : ℝ) (n : ℤ) : ℝ :=
  Real.rpow (1 + |y + a * (n : ℝ)|) (-σ)


def masterSeries (a σ : ℝ) : ℝ :=
  ∑' n : ℕ, Real.rpow (1 + a * (n : ℝ)) (-σ)



theorem rpow_neg_antitone_one_add_mul
    {a σ s t : ℝ} (ha : 0 < a) (hσ : 1 < σ)
    (hs : 0 ≤ s) (hst : s ≤ t) :
    Real.rpow (1 + a * t) (-σ) ≤ Real.rpow (1 + a * s) (-σ) := by
  have hbase : 0 < 1 + a * s := by positivity
  have hmono : 1 + a * s ≤ 1 + a * t := by
    nlinarith [mul_le_mul_of_nonneg_left hst ha.le]
  have hexp : -σ ≤ 0 := by linarith
  exact Real.rpow_le_rpow_of_nonpos hbase hmono hexp


theorem summable_masterSeries
    {a σ : ℝ} (ha : 0 < a) (hσ : 1 < σ) :
    Summable (fun n : ℕ => Real.rpow (1 + a * (n : ℝ)) (-σ)) := by
  let m : ℝ := min 1 a
  have hmpos : 0 < m := by
    dsimp [m]
    exact lt_min zero_lt_one ha
  have hcomp :
      Summable (fun n : ℕ =>
        Real.rpow m (-σ) * Real.rpow ((n : ℝ) + 1) (-σ)) := by
    have hs : Summable (fun n : ℕ => Real.rpow (n : ℝ) (-σ)) := by
      have hs0 : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := by
        exact (Real.summable_nat_rpow (p := -σ)).mpr (by linarith)
      simpa using hs0
    have hshift :
        Summable (fun n : ℕ => Real.rpow (((n + 1 : ℕ) : ℝ)) (-σ)) := by
      exact (summable_nat_add_iff 1).mpr hs
    have hshift2 :
        Summable (fun n : ℕ => Real.rpow ((n : ℝ) + 1) (-σ)) := by
      simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc]
        using hshift
    exact hshift2.mul_left (Real.rpow m (-σ))
  refine Summable.of_nonneg_of_le
    (f := fun n : ℕ => Real.rpow m (-σ) * Real.rpow ((n : ℝ) + 1) (-σ))
    ?hnonneg ?hle hcomp
  · intro n
    have hbase : 0 ≤ 1 + a * (n : ℝ) := by positivity
    exact Real.rpow_nonneg hbase (-σ)
  · intro n
    have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    have hmn1 : m ≤ 1 := by
      dsimp [m]
      exact min_le_left 1 a
    have hma : m ≤ a := by
      dsimp [m]
      exact min_le_right 1 a
    have hbase_lower_pos : 0 < m * ((n : ℝ) + 1) := by positivity
    have hbase_le : m * ((n : ℝ) + 1) ≤ 1 + a * (n : ℝ) := by
      have hmul : m * (n : ℝ) ≤ a * (n : ℝ) := by
        exact mul_le_mul_of_nonneg_right hma hn0
      nlinarith
    calc
      Real.rpow (1 + a * (n : ℝ)) (-σ)
          ≤ Real.rpow (m * ((n : ℝ) + 1)) (-σ) :=
            Real.rpow_le_rpow_of_nonpos hbase_lower_pos hbase_le (by linarith)
      _ = Real.rpow m (-σ) * Real.rpow ((n : ℝ) + 1) (-σ) := by
            simpa using (Real.mul_rpow hmpos.le
              (by positivity : 0 ≤ (n : ℝ) + 1) :
              (m * ((n : ℝ) + 1)) ^ (-σ) =
                m ^ (-σ) * ((n : ℝ) + 1) ^ (-σ))


theorem one_le_masterSeries
    {a σ : ℝ} (ha : 0 < a) (hσ : 1 < σ) :
    1 ≤ masterSeries a σ := by
  dsimp [masterSeries]
  have hs := summable_masterSeries ha hσ
  have hnonneg :
      ∀ n : ℕ, 0 ≤ Real.rpow (1 + a * (n : ℝ)) (-σ) := by
    intro n
    have hn : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    have hbase : 0 ≤ 1 + a * (n : ℝ) := by positivity
    exact Real.rpow_nonneg hbase (-σ)
  simpa using hs.le_tsum 0 (fun n _hn => hnonneg n)



theorem floor_fract_lattice_split
    {a y : ℝ} (ha : 0 < a) :
    ∃ q : ℤ, ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧
      ∀ n : ℤ,
        y + a * (n : ℝ) = a * (((q + n : ℤ) : ℝ) + θ) ∧
        |y + a * (n : ℝ)| = a * |(((q + n : ℤ) : ℝ) + θ)| := by
  let q : ℤ := ⌊y / a⌋
  let θ : ℝ := Int.fract (y / a)
  refine ⟨q, θ, ?_, ?_, ?_⟩
  · exact Int.fract_nonneg _
  · exact Int.fract_lt_one _
  · intro n
    have hdecomp : (q : ℝ) + θ = y / a := by
      dsimp [q, θ]
      exact Int.floor_add_fract (y / a)
    have hy : y = a * ((q : ℝ) + θ) := by
      rw [hdecomp, mul_div_cancel₀ y ha.ne']
    have hmain : y + a * (n : ℝ) = a * (((q + n : ℤ) : ℝ) + θ) := by
      rw [hy]
      norm_num
      ring
    constructor
    · exact hmain
    · rw [hmain, abs_mul, abs_of_pos ha]

private def twoSidedMajorant (a σ : ℝ) : ℤ → ℝ :=
  Int.rec
    (fun n : ℕ => Real.rpow (1 + a * (n : ℝ)) (-σ))
    (fun n : ℕ => Real.rpow (1 + a * (n : ℝ)) (-σ))

private theorem twoSidedMajorant_nonneg
    {a σ : ℝ} (ha : 0 < a) :
    ∀ k : ℤ, 0 ≤ twoSidedMajorant a σ k := by
  intro k
  cases k with
  | ofNat n =>
      simp [twoSidedMajorant]
      have hbase : 0 ≤ 1 + a * (n : ℝ) := by positivity
      exact Real.rpow_nonneg hbase (-σ)
  | negSucc n =>
      simp [twoSidedMajorant]
      have hbase : 0 ≤ 1 + a * (n : ℝ) := by positivity
      exact Real.rpow_nonneg hbase (-σ)

private theorem twoSidedMajorant_summable
    {a σ : ℝ} (ha : 0 < a) (hσ : 1 < σ) :
    Summable (twoSidedMajorant a σ) := by
  let φ : ℕ → ℝ := fun n => Real.rpow (1 + a * (n : ℝ)) (-σ)
  have hφ : Summable φ := by
    simpa [φ] using (summable_masterSeries (a := a) (σ := σ) ha hσ)
  apply Summable.of_nat_of_neg_add_one
  · change Summable φ
    exact hφ
  · change Summable φ
    exact hφ

private theorem twoSidedMajorant_tsum
    {a σ : ℝ} (ha : 0 < a) (hσ : 1 < σ) :
    (∑' k : ℤ, twoSidedMajorant a σ k) = 2 * masterSeries a σ := by
  let φ : ℕ → ℝ := fun n => Real.rpow (1 + a * (n : ℝ)) (-σ)
  have hφ : Summable φ := by
    simpa [φ] using (summable_masterSeries (a := a) (σ := σ) ha hσ)
  have hsum := tsum_of_nat_of_neg_add_one
      (f := twoSidedMajorant a σ)
      (by
        change Summable φ
        exact hφ)
      (by
        change Summable φ
        exact hφ)
  calc
    (∑' k : ℤ, twoSidedMajorant a σ k)
        = (∑' n : ℕ, twoSidedMajorant a σ n) +
          ∑' n : ℕ, twoSidedMajorant a σ (-(n + 1)) := hsum
    _ = masterSeries a σ + masterSeries a σ := by
        change (∑' n : ℕ, φ n) + (∑' n : ℕ, φ n) =
          masterSeries a σ + masterSeries a σ
        simp [φ, masterSeries]
    _ = 2 * masterSeries a σ := by ring

private theorem twoSidedMajorant_majorizes
    {a σ θ : ℝ} (ha : 0 < a) (hσ : 1 < σ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∀ k : ℤ,
      Real.rpow (1 + a * |(k : ℝ) + θ|) (-σ) ≤
        twoSidedMajorant a σ k := by
  intro k
  cases k with
  | ofNat n =>
      simp [twoSidedMajorant]
      have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
      have habs_ge : (n : ℝ) ≤ |(n : ℝ) + θ| := by
        have hsum_nonneg : 0 ≤ (n : ℝ) + θ := by positivity
        rw [abs_of_nonneg hsum_nonneg]
        linarith
      have hbase_pos : 0 < 1 + a * (n : ℝ) := by positivity
      have hbase_le : 1 + a * (n : ℝ) ≤ 1 + a * |(n : ℝ) + θ| := by
        have hmul := mul_le_mul_of_nonneg_left habs_ge ha.le
        linarith
      exact Real.rpow_le_rpow_of_nonpos hbase_pos hbase_le (by linarith)
  | negSucc n =>
      simp [twoSidedMajorant, Int.cast_negSucc]
      have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
      have harg_nonpos : -1 + -(n : ℝ) + θ ≤ 0 := by
        linarith
      have habs_ge : (n : ℝ) ≤ |-1 + -(n : ℝ) + θ| := by
        rw [abs_of_nonpos harg_nonpos]
        linarith
      have hbase_pos : 0 < 1 + a * (n : ℝ) := by positivity
      have hbase_le :
          1 + a * (n : ℝ) ≤ 1 + a * |-1 + -(n : ℝ) + θ| := by
        have hmul := mul_le_mul_of_nonneg_left habs_ge ha.le
        linarith
      exact Real.rpow_le_rpow_of_nonpos hbase_pos hbase_le (by linarith)


theorem lattice_majorant
    {a σ θ r : ℝ} (ha : 0 < a) (hσ : 1 < σ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ ψ : ℤ → ℝ,
      (∀ k : ℤ, 0 ≤ ψ k) ∧
      Summable ψ ∧
      (∑' k : ℤ, ψ k) = 2 * masterSeries a σ ∧
      ∀ k : ℤ,
        Real.rpow (1 + a * |(k : ℝ) + θ|) (-σ) ≤ ψ k := by
  let φ : ℕ → ℝ := fun n => Real.rpow (1 + a * (n : ℝ)) (-σ)
  let ψ : ℤ → ℝ := Int.rec φ φ
  have hψ_nat : ∀ n : ℕ, ψ (n : ℤ) = φ n := by
    intro n
    rfl
  have hψ_neg : ∀ n : ℕ, ψ (-1 + -(n : ℤ)) = φ n := by
    intro n
    have harg : -1 + -(n : ℤ) = Int.negSucc n := by
      rw [Int.negSucc_eq]
      ring
    rw [harg]
  have hφ : Summable φ := by
    simpa [φ] using (summable_masterSeries (a := a) (σ := σ) ha hσ)
  refine ⟨ψ, ?_, ?_, ?_, ?_⟩
  · intro k
    cases k with
    | ofNat n =>
        change 0 ≤ φ n
        have hbase : 0 ≤ 1 + a * (n : ℝ) := by positivity
        exact Real.rpow_nonneg hbase (-σ)
    | negSucc n =>
        change 0 ≤ φ n
        have hbase : 0 ≤ 1 + a * (n : ℝ) := by positivity
        exact Real.rpow_nonneg hbase (-σ)
  · apply Summable.of_nat_of_neg_add_one
    · simpa [hψ_nat] using hφ
    · simpa [hψ_neg] using hφ
  · have htsum := tsum_of_nat_of_neg_add_one
      (f := ψ)
      (by simpa [hψ_nat] using hφ)
      (by simpa [hψ_neg] using hφ)
    calc
      (∑' k : ℤ, ψ k)
          = (∑' n : ℕ, ψ n) + ∑' n : ℕ, ψ (-(n + 1)) := htsum
      _ = masterSeries a σ + masterSeries a σ := by
          simp [hψ_nat, hψ_neg, φ, masterSeries]
      _ = 2 * masterSeries a σ := by ring
  · intro k
    cases k with
    | ofNat n =>
        simp [ψ, φ]
        have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
        have habs_ge : (n : ℝ) ≤ |(n : ℝ) + θ| := by
          have hsum_nonneg : 0 ≤ (n : ℝ) + θ := by positivity
          rw [abs_of_nonneg hsum_nonneg]
          linarith
        have hbase_pos : 0 < 1 + a * (n : ℝ) := by positivity
        have hbase_le : 1 + a * (n : ℝ) ≤ 1 + a * |(n : ℝ) + θ| := by
          have hmul := mul_le_mul_of_nonneg_left habs_ge ha.le
          linarith
        exact Real.rpow_le_rpow_of_nonpos hbase_pos hbase_le (by linarith)
    | negSucc n =>
        simp [ψ, φ, Int.cast_negSucc]
        have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
        have harg_nonpos : -1 + -(n : ℝ) + θ ≤ 0 := by
          linarith
        have habs_ge : (n : ℝ) ≤ |-1 + -(n : ℝ) + θ| := by
          rw [abs_of_nonpos harg_nonpos]
          linarith
        have hbase_pos : 0 < 1 + a * (n : ℝ) := by positivity
        have hbase_le :
            1 + a * (n : ℝ) ≤ 1 + a * |-1 + -(n : ℝ) + θ| := by
          have hmul := mul_le_mul_of_nonneg_left habs_ge ha.le
          linarith
        exact Real.rpow_le_rpow_of_nonpos hbase_pos hbase_le (by linarith)


theorem summable_lattice_decay_uniform
    {a σ y : ℝ} (ha : 0 < a) (hσ : 1 < σ) :
    Summable (fun n : ℤ => latticeDecay a σ y n) ∧
      (∑' n : ℤ, latticeDecay a σ y n) ≤ 2 * masterSeries a σ := by
  obtain ⟨q, θ, hθ0, hθ1, hsplit⟩ :=
    floor_fract_lattice_split (a := a) (y := y) ha
  obtain ⟨ψ, _hψ_nonneg, hψ_sum, hψ_tsum, hψ_major⟩ :=
    lattice_majorant (a := a) (σ := σ) (θ := θ) (r := 0) ha hσ hθ0 hθ1
  have hpoint :
      ∀ n : ℤ, latticeDecay a σ y n ≤ ψ (q + n) := by
    intro n
    have hsplitn := hsplit n
    have hlat :
        latticeDecay a σ y n =
          Real.rpow (1 + a * |(((q + n : ℤ) : ℝ) + θ)|) (-σ) := by
      rw [latticeDecay, hsplitn.2]
    rw [hlat]
    exact hψ_major (q + n)
  have hcomp : Summable (fun n : ℤ => ψ (q + n)) := by
    exact hψ_sum.comp_injective (fun _m _n h => add_left_cancel h)
  have hnonneg : ∀ n : ℤ, 0 ≤ latticeDecay a σ y n := by
    intro n
    dsimp [latticeDecay]
    have hbase : 0 ≤ 1 + |y + a * (n : ℝ)| := by positivity
    exact Real.rpow_nonneg hbase (-σ)
  have hlat_sum : Summable (fun n : ℤ => latticeDecay a σ y n) :=
    Summable.of_nonneg_of_le hnonneg hpoint hcomp
  have htsum_le :
      (∑' n : ℤ, latticeDecay a σ y n) ≤ ∑' n : ℤ, ψ (q + n) :=
    Summable.tsum_le_tsum hpoint hlat_sum hcomp
  have hshift :
      (∑' n : ℤ, ψ (q + n)) = ∑' k : ℤ, ψ k := by
    simpa using (Equiv.addLeft q).tsum_eq ψ
  constructor
  · exact hlat_sum
  · exact htsum_le.trans (by rw [hshift, hψ_tsum])


theorem summable_lattice_decay_reflected_uniform
    {a σ y : ℝ} (ha : 0 < a) (hσ : 1 < σ) :
    Summable (fun n : ℤ => Real.rpow (1 + |y - a * (n : ℝ)|) (-σ)) ∧
      (∑' n : ℤ, Real.rpow (1 + |y - a * (n : ℝ)|) (-σ))
        ≤ 2 * masterSeries a σ := by
  obtain ⟨hs, hle⟩ := summable_lattice_decay_uniform (y := y) ha hσ
  have hfun :
      (fun n : ℤ => Real.rpow (1 + |y - a * (n : ℝ)|) (-σ)) =
        fun n : ℤ => latticeDecay a σ y (-n) := by
    funext n
    simp [latticeDecay, sub_eq_add_neg]
  have htsum :
      (∑' n : ℤ, latticeDecay a σ y (-n)) =
        ∑' n : ℤ, latticeDecay a σ y n := by
    exact (Equiv.neg ℤ).tsum_eq (fun n : ℤ => latticeDecay a σ y n)
  constructor
  · rw [hfun]
    exact hs.comp_injective (Equiv.neg ℤ).injective
  · rw [hfun, htsum]
    exact hle


theorem lattice_decay_tail_uniform
    {a σ ε : ℝ} (ha : 0 < a) (hσ : 1 < σ) (hε : 0 < ε) :
    ∃ ρ0 : ℝ, 1 ≤ ρ0 ∧ ∀ ρ y : ℝ, ρ0 ≤ ρ →
      (∑' n : ℤ,
        if ρ ≤ |y + a * (n : ℝ)| then latticeDecay a σ y n else 0) ≤ ε := by
  let ψ : ℤ → ℝ := twoSidedMajorant a σ
  have hψ_nonneg : ∀ k : ℤ, 0 ≤ ψ k := by
    intro k
    exact twoSidedMajorant_nonneg (a := a) (σ := σ) ha k
  have hψ_sum : Summable ψ := by
    simpa [ψ] using twoSidedMajorant_summable (a := a) (σ := σ) ha hσ
  let ψNN : ℤ → NNReal := fun k => ⟨ψ k, hψ_nonneg k⟩
  let εNN : NNReal := ⟨ε, hε.le⟩
  have hεNN : (0 : NNReal) < εNN := by
    exact_mod_cast hε
  have htail_eventually :
      ∀ᶠ (s : Finset ℤ) in Filter.atTop,
        (∑' b : {k : ℤ // k ∉ s}, ψNN b) < εNN := by
    exact (tendsto_order.1 (NNReal.tendsto_tsum_compl_atTop_zero ψNN)).2 εNN hεNN
  rcases Filter.eventually_atTop.mp htail_eventually with ⟨s, hs_tail⟩
  let R : ℝ := ∑ k ∈ s, |(k : ℝ)|
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    exact Finset.sum_nonneg fun k _ => abs_nonneg (k : ℝ)
  have hs_bound : ∀ k : ℤ, k ∈ s → |(k : ℝ)| ≤ R := by
    intro k hk
    dsimp [R]
    exact Finset.single_le_sum (s := s) (f := fun j : ℤ => |(j : ℝ)|)
      (fun j _ => abs_nonneg (j : ℝ)) hk
  refine ⟨max 1 (a * (R + 1) + 1), le_max_left _ _, ?_⟩
  intro ρ y hρ
  obtain ⟨q, θ, hθ0, hθ1, hsplit⟩ :=
    floor_fract_lattice_split (a := a) (y := y) ha
  let tail : ℤ → ℝ := fun n =>
    if ρ ≤ |y + a * (n : ℝ)| then latticeDecay a σ y n else 0
  let majorTail : ℤ → ℝ := fun n =>
    if q + n ∉ s then ψ (q + n) else 0
  have htail_nonneg : ∀ n : ℤ, 0 ≤ tail n := by
    intro n
    by_cases hn : ρ ≤ |y + a * (n : ℝ)|
    · simp [tail, hn, latticeDecay,
        Real.rpow_nonneg (by positivity : 0 ≤ 1 + |y + a * (n : ℝ)|) (-σ)]
    · simp [tail, hn]
  have hmajor_nonneg : ∀ n : ℤ, 0 ≤ majorTail n := by
    intro n
    by_cases hmem : q + n ∈ s
    · simp [majorTail, hmem]
    · simp [majorTail, hmem, hψ_nonneg]
  have hmajor_le_full : ∀ n : ℤ, majorTail n ≤ ψ (q + n) := by
    intro n
    by_cases hmem : q + n ∈ s
    · simp [majorTail, hmem, hψ_nonneg]
    · simp [majorTail, hmem]
  have hmajor_sum : Summable majorTail := by
    have hcomp : Summable (fun n : ℤ => ψ (q + n)) :=
      hψ_sum.comp_injective (fun _m _n h => add_left_cancel h)
    exact Summable.of_nonneg_of_le hmajor_nonneg hmajor_le_full hcomp
  have hpoint : ∀ n : ℤ, tail n ≤ majorTail n := by
    intro n
    by_cases hn : ρ ≤ |y + a * (n : ℝ)|
    · have hsplitn := hsplit n
      have hk_not_mem : q + n ∉ s := by
        intro hk
        have hkR : |((q + n : ℤ) : ℝ)| ≤ R := hs_bound (q + n) hk
        have hθabs : |θ| ≤ 1 := by
          rw [abs_of_nonneg hθ0]
          exact hθ1.le
        have habs_le : |(((q + n : ℤ) : ℝ) + θ)| ≤ R + 1 := by
          calc
            |(((q + n : ℤ) : ℝ) + θ)|
                ≤ |((q + n : ℤ) : ℝ)| + |θ| := abs_add_le _ _
            _ ≤ R + 1 := by linarith
        have hy_le : |y + a * (n : ℝ)| ≤ a * (R + 1) := by
          rw [hsplitn.2]
          exact mul_le_mul_of_nonneg_left habs_le ha.le
        have hρ_big : a * (R + 1) + 1 ≤ ρ :=
          (le_max_right (1 : ℝ) (a * (R + 1) + 1)).trans hρ
        linarith
      have hlat :
          latticeDecay a σ y n ≤ ψ (q + n) := by
        have hlat_eq :
            latticeDecay a σ y n =
              Real.rpow (1 + a * |(((q + n : ℤ) : ℝ) + θ)|) (-σ) := by
          rw [latticeDecay, hsplitn.2]
        rw [hlat_eq]
        exact twoSidedMajorant_majorizes (a := a) (σ := σ) (θ := θ)
          ha hσ hθ0 hθ1 (q + n)
      simp [tail, majorTail, hn, hk_not_mem, hlat]
    · have hnonneg := hmajor_nonneg n
      simp [tail, hn, hnonneg]
  have htail_sum : Summable tail :=
    Summable.of_nonneg_of_le htail_nonneg hpoint hmajor_sum
  have hmajor_reindex :
      (∑' n : ℤ, majorTail n) =
        ∑' k : ℤ, if k ∉ s then ψ k else 0 := by
    dsimp [majorTail]
    simpa using
      (Equiv.addLeft q).tsum_eq (fun k : ℤ => if k ∉ s then ψ k else 0)
  have hmajor_subtype :
      (∑' k : ℤ, if k ∉ s then ψ k else 0) =
        ∑' b : {k : ℤ // k ∉ s}, ψ b := by
    calc
      (∑' k : ℤ, if k ∉ s then ψ k else 0) =
          ∑' k : ℤ, ({k : ℤ | k ∉ s} : Set ℤ).indicator ψ k := by
            apply tsum_congr
            intro k
            by_cases hk : k ∉ s <;> simp [Set.indicator, hk]
      _ = ∑' b : {k : ℤ // k ∉ s}, ψ b := by
            exact (tsum_subtype (s := {k : ℤ | k ∉ s}) (f := ψ)).symm
  have hsmall_NN :
      (∑' b : {k : ℤ // k ∉ s}, ψNN b) < εNN :=
    hs_tail s le_rfl
  have hcoe_tail :
      ((∑' b : {k : ℤ // k ∉ s}, ψNN b) : ℝ) =
        ∑' b : {k : ℤ // k ∉ s}, ψ b := by
    apply tsum_congr
    intro b
    rfl
  have hsmall_real :
      (∑' b : {k : ℤ // k ∉ s}, ψ b) < ε := by
    have hsmall_coe_NN :
        (((∑' b : {k : ℤ // k ∉ s}, ψNN b) : NNReal) : ℝ) < (εNN : ℝ) :=
      (NNReal.coe_lt_coe).2 hsmall_NN
    have hsmall_coe : ((∑' b : {k : ℤ // k ∉ s}, ψNN b) : ℝ) < ε := by
      have hεNN_coe : (εNN : ℝ) = ε := by
        exact NNReal.coe_mk ε hε.le
      rw [← hεNN_coe]
      simpa [NNReal.coe_tsum] using hsmall_coe_NN
    rwa [hcoe_tail] at hsmall_coe
  calc
    (∑' n : ℤ,
        if ρ ≤ |y + a * (n : ℝ)| then latticeDecay a σ y n else 0)
        = ∑' n : ℤ, tail n := rfl
    _ ≤ ∑' n : ℤ, majorTail n :=
        Summable.tsum_le_tsum hpoint htail_sum hmajor_sum
    _ = ∑' k : ℤ, if k ∉ s then ψ k else 0 := hmajor_reindex
    _ = ∑' b : {k : ℤ // k ∉ s}, ψ b := hmajor_subtype
    _ ≤ ε := le_of_lt hsmall_real


theorem lattice_decay_shifted_tail_uniform
    {a σ ε : ℝ} (ha : 0 < a) (hσ : 1 < σ) (hε : 0 < ε) :
    ∃ ρ1 : ℝ, 1 ≤ ρ1 ∧ ∀ ρ h y : ℝ, ρ1 ≤ ρ → |h| ≤ 1 →
      (∑' n : ℤ,
        if ρ ≤ |y + a * (n : ℝ)| then
          Real.rpow (1 + |y + h + a * (n : ℝ)|) (-σ)
        else 0) ≤ ε := by
  obtain ⟨ρ0, hρ0_one, htail⟩ :=
    lattice_decay_tail_uniform (a := a) (σ := σ) (ε := ε) ha hσ hε
  refine ⟨ρ0 + 1, by linarith, ?_⟩
  intro ρ h y hρ hh
  let shiftedTail : ℤ → ℝ := fun n =>
    if ρ ≤ |y + a * (n : ℝ)| then
      Real.rpow (1 + |y + h + a * (n : ℝ)|) (-σ)
    else 0
  let unshiftedTail : ℤ → ℝ := fun n =>
    if ρ ≤ |(y + h) + a * (n : ℝ)| + 1 then
      latticeDecay a σ (y + h) n
    else 0
  have hfull :
      Summable (fun n : ℤ => latticeDecay a σ (y + h) n) :=
    (summable_lattice_decay_uniform (a := a) (σ := σ) (y := y + h) ha hσ).1
  have hunshifted_nonneg : ∀ n : ℤ, 0 ≤ unshiftedTail n := by
    intro n
    by_cases hn : ρ ≤ |(y + h) + a * (n : ℝ)| + 1
    · simp [unshiftedTail, hn, latticeDecay,
        Real.rpow_nonneg (by positivity : 0 ≤ 1 + |y + h + a * (n : ℝ)|) (-σ)]
    · simp [unshiftedTail, hn]
  have hunshifted_le_full :
      ∀ n : ℤ, unshiftedTail n ≤ latticeDecay a σ (y + h) n := by
    intro n
    by_cases hn : ρ ≤ |(y + h) + a * (n : ℝ)| + 1
    · simp [unshiftedTail, hn]
    · simp [unshiftedTail, hn, latticeDecay,
        Real.rpow_nonneg (by positivity : 0 ≤ 1 + |y + h + a * (n : ℝ)|) (-σ)]
  have hunshifted_sum : Summable unshiftedTail :=
    Summable.of_nonneg_of_le hunshifted_nonneg hunshifted_le_full hfull
  have hpoint : ∀ n : ℤ, shiftedTail n ≤ unshiftedTail n := by
    intro n
    by_cases hn : ρ ≤ |y + a * (n : ℝ)|
    · have htri :
          |y + a * (n : ℝ)| ≤ |y + h + a * (n : ℝ)| + |h| := by
        calc
          |y + a * (n : ℝ)|
              = |(y + h + a * (n : ℝ)) + (-h)| := by
                congr 1
                ring
          _ ≤ |y + h + a * (n : ℝ)| + |-h| :=
                abs_add_le (y + h + a * (n : ℝ)) (-h)
          _ = |y + h + a * (n : ℝ)| + |h| := by rw [abs_neg]
      have htail_mem : ρ ≤ |(y + h) + a * (n : ℝ)| + 1 := by
        linarith
      have htail_mem' : ρ ≤ |h + (y + a * (n : ℝ))| + 1 := by
        simpa [add_comm, add_left_comm, add_assoc] using htail_mem
      simp [shiftedTail, unshiftedTail, hn, htail_mem', latticeDecay,
        add_comm, add_assoc]
    · have hnonneg : 0 ≤ unshiftedTail n := hunshifted_nonneg n
      simp [shiftedTail, hn, hnonneg]
  have hshifted_nonneg : ∀ n : ℤ, 0 ≤ shiftedTail n := by
    intro n
    by_cases hn : ρ ≤ |y + a * (n : ℝ)|
    · simp [shiftedTail, hn,
        Real.rpow_nonneg (by positivity : 0 ≤ 1 + |y + h + a * (n : ℝ)|) (-σ)]
    · simp [shiftedTail, hn]
  have hshifted_sum : Summable shiftedTail :=
    Summable.of_nonneg_of_le hshifted_nonneg hpoint hunshifted_sum
  have hρ_tail : ρ0 ≤ ρ - 1 := by linarith
  have hunshifted_bound :
      (∑' n : ℤ, unshiftedTail n) ≤ ε := by
    simpa [unshiftedTail, latticeDecay, sub_le_iff_le_add, add_comm,
      add_left_comm, add_assoc]
      using htail (ρ - 1) (y + h) hρ_tail
  calc
    (∑' n : ℤ,
        if ρ ≤ |y + a * (n : ℝ)| then
          Real.rpow (1 + |y + h + a * (n : ℝ)|) (-σ)
        else 0)
        = ∑' n : ℤ, shiftedTail n := rfl
    _ ≤ ∑' n : ℤ, unshiftedTail n :=
        Summable.tsum_le_tsum hpoint hshifted_sum hunshifted_sum
    _ ≤ ε := hunshifted_bound


theorem int_lattice_points_lt_finite
    {a ρ y : ℝ} (ha : 0 < a) (_hρ : 0 < ρ) :
    {n : ℤ | |y + a * (n : ℝ)| < ρ}.Finite := by
  refine BddBelow.finite_of_bddAbove ?_ ?_
  · refine ⟨⌊(-ρ - y) / a⌋, ?_⟩
    intro n hn
    have hlt : (-ρ - y) / a < (n : ℝ) := by
      rw [div_lt_iff₀ ha]
      have habs : |y + a * (n : ℝ)| < ρ := by
        simpa using hn
      have h := (abs_lt.mp habs).1
      nlinarith
    have hfloor : ((⌊(-ρ - y) / a⌋ : ℤ) : ℝ) ≤ (-ρ - y) / a :=
      Int.floor_le _
    exact_mod_cast (hfloor.trans hlt.le)
  · refine ⟨⌈(ρ - y) / a⌉, ?_⟩
    intro n hn
    have hlt : (n : ℝ) < (ρ - y) / a := by
      rw [lt_div_iff₀ ha]
      have habs : |y + a * (n : ℝ)| < ρ := by
        simpa using hn
      have h := (abs_lt.mp habs).2
      nlinarith
    have hceil : (ρ - y) / a ≤ ((⌈(ρ - y) / a⌉ : ℤ) : ℝ) :=
      Int.le_ceil _
    exact_mod_cast (hlt.le.trans hceil)


theorem int_lattice_points_lt_card_le
    {a ρ y : ℝ} (ha : 0 < a) (hρ : 0 < ρ) :
    (({n : ℤ | |y + a * (n : ℝ)| < ρ}.ncard : ℕ) : ℝ) ≤
      2 * ρ / a + 1 := by
  let A : ℝ := (-ρ - y) / a
  let B : ℝ := (ρ - y) / a
  let L : ℤ := ⌈A⌉
  let U : ℤ := ⌈B⌉
  let S : Set ℤ := {n : ℤ | |y + a * (n : ℝ)| < ρ}
  have hsubset : S ⊆ (Finset.Ico L U : Set ℤ) := by
    intro n hn
    have habs : |y + a * (n : ℝ)| < ρ := by simpa [S] using hn
    have hleft : A < (n : ℝ) := by
      dsimp [A]
      rw [div_lt_iff₀ ha]
      have h := (abs_lt.mp habs).1
      nlinarith
    have hright : (n : ℝ) < B := by
      dsimp [B]
      rw [lt_div_iff₀ ha]
      have h := (abs_lt.mp habs).2
      nlinarith
    have hL : L ≤ n := by
      dsimp [L]
      rw [Int.ceil_le]
      exact hleft.le
    have hU : n < U := by
      dsimp [U]
      rw [Int.lt_ceil]
      exact hright
    simpa [Finset.mem_Ico] using ⟨hL, hU⟩
  have hncard_le : S.ncard ≤ (Finset.Ico L U).card := by
    have h := Set.ncard_le_ncard hsubset (Finset.finite_toSet (Finset.Ico L U))
    have hIco : (Set.Ico L U).ncard = (Finset.Ico L U).card := by
      simpa using (Set.ncard_coe_finset (Finset.Ico L U))
    simpa [hIco] using h
  have hcard_bound : ((Finset.Ico L U).card : ℝ) ≤ 2 * ρ / a + 1 := by
    by_cases hLU : L ≤ U
    · have hcard_int : ((Finset.Ico L U).card : ℤ) = U - L :=
        Int.card_Ico_of_le L U hLU
      have hcard_real :
          ((Finset.Ico L U).card : ℝ) = (U : ℝ) - (L : ℝ) := by
        exact_mod_cast hcard_int
      have hU_lt : (U : ℝ) < B + 1 := by
        dsimp [U]
        exact Int.ceil_lt_add_one B
      have hL_ge : A ≤ (L : ℝ) := by
        dsimp [L]
        exact Int.le_ceil A
      rw [hcard_real]
      have hbound_lt : (U : ℝ) - (L : ℝ) < B + 1 - A := by
        linarith
      have hBA : B + 1 - A = 2 * ρ / a + 1 := by
        dsimp [A, B]
        ring_nf
      linarith
    · have hUL : U < L := lt_of_not_ge hLU
      have hempty : Finset.Ico L U = ∅ := by
        ext n
        simp [Finset.mem_Ico]
        omega
      have hpos : 0 < 2 * ρ / a + 1 := by
        have hdiv : 0 < 2 * ρ / a := div_pos (mul_pos (by norm_num) hρ) ha
        linarith
      simp [hempty, hpos.le]
  have hncard_le_real : ((S.ncard : ℕ) : ℝ) ≤ ((Finset.Ico L U).card : ℝ) := by
    exact_mod_cast hncard_le
  have hmain : ((S.ncard : ℕ) : ℝ) ≤ 2 * ρ / a + 1 :=
    hncard_le_real.trans hcard_bound
  simpa [S] using hmain


theorem eventually_abs_le_of_polynomialDecay
    {g : ℝ → ℝ} (hg : HasPolynomialDecay g) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t : ℝ, R ≤ |t| → |g t| ≤ ε := by
  rcases hg with ⟨C, η, hC, hη, hbound⟩
  have hηpos : 0 < η := by linarith
  have hbase_tend : Filter.Tendsto (fun r : ℝ => 1 + r)
      Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.mpr ?_
    intro b
    refine Filter.eventually_atTop.2 ⟨b, ?_⟩
    intro r hr
    linarith
  have hpow_tend : Filter.Tendsto (fun r : ℝ => (1 + r) ^ η)
      Filter.atTop Filter.atTop := by
    exact (tendsto_rpow_atTop hηpos).comp hbase_tend
  have htend : Filter.Tendsto (fun r : ℝ => C / ((1 + r) ^ η))
      Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using (hpow_tend.inv_tendsto_atTop.const_mul C)
  have hev : ∀ᶠ r : ℝ in Filter.atTop,
      dist (C / ((1 + r) ^ η)) 0 < ε :=
    (Metric.tendsto_nhds.mp htend) ε hε
  rcases Filter.eventually_atTop.mp hev with ⟨R0, hR0⟩
  refine ⟨max R0 0, le_max_right _ _, ?_⟩
  intro t ht
  have hR0_abs : R0 ≤ |t| := (le_max_left R0 0).trans ht
  have hdist := hR0 |t| hR0_abs
  have hden_pos : 0 < (1 + |t|) ^ η :=
    Real.rpow_pos_of_pos (by positivity) η
  have hdist_absdiv : |C| / |(1 + |t|) ^ η| < ε := by
    simpa [Real.dist_eq, abs_div] using hdist
  have hsmall : C / ((1 + |t|) ^ η) < ε := by
    simpa [abs_of_pos hC, abs_of_pos hden_pos] using hdist_absdiv
  exact (hbound t).trans hsmall.le


theorem uniformContinuous_of_continuous_polynomialDecay
    {g : ℝ → ℝ} (hgc : Continuous g) (hgd : HasPolynomialDecay g) :
    UniformContinuous g := by
  have htend : Filter.Tendsto g (Filter.cocompact ℝ) (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    rcases eventually_abs_le_of_polynomialDecay hgd (half_pos hε) with
      ⟨R, _hR_nonneg, hR⟩
    have houtside : {t : ℝ | R ≤ |t|} ∈ Filter.cocompact ℝ := by
      refine Filter.mem_cocompact.2 ⟨Set.Icc (-R) R, isCompact_Icc, ?_⟩
      intro t ht
      by_contra hnot
      have habs_lt : |t| < R := lt_of_not_ge hnot
      have ht_interval : t ∈ Set.Icc (-R) R := by
        have hlt := abs_lt.mp habs_lt
        exact ⟨hlt.1.le, hlt.2.le⟩
      exact ht ht_interval
    refine Filter.mem_of_superset houtside ?_
    intro t ht
    have hgsmall : |g t| ≤ ε / 2 := hR t ht
    have hglt : |g t| < ε := by linarith
    simpa [Real.dist_eq] using hglt
  exact hgc.uniformContinuous_of_tendsto_cocompact htend


theorem summable_shift_difference_uniform
    {g : ℝ → ℝ} {a ε : ℝ}
    (hgc : Continuous g) (hgd : HasPolynomialDecay g)
    (ha : 0 < a) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ h y : ℝ, |h| ≤ δ →
        Summable (fun n : ℤ =>
          |g (y + h + a * (n : ℝ)) - g (y + a * (n : ℝ))|) ∧
        (∑' n : ℤ,
          |g (y + h + a * (n : ℝ)) - g (y + a * (n : ℝ))|) ≤ ε := by
  rcases hgd with ⟨C, σ, hC, hσ, hbound⟩
  have hgd' : HasPolynomialDecay g := ⟨C, σ, hC, hσ, hbound⟩
  have hdecay_mul :
      ∀ x : ℝ, |g x| ≤ C * Real.rpow (1 + |x|) (-σ) := by
    intro x
    have hbase_pos : 0 < 1 + |x| := by positivity
    calc
      |g x| ≤ C / ((1 + |x|) ^ σ) := hbound x
      _ = C * Real.rpow (1 + |x|) (-σ) := by
            rw [div_eq_mul_inv]
            rw [← Real.rpow_neg hbase_pos.le]
            rw [← Real.rpow_eq_pow]
  let tailEps : ℝ := ε / (4 * C)
  have htailEps_pos : 0 < tailEps := by
    dsimp [tailEps]
    positivity
  obtain ⟨ρ0, hρ0_one, htail0⟩ :=
    lattice_decay_tail_uniform (a := a) (σ := σ) (ε := tailEps) ha hσ htailEps_pos
  obtain ⟨ρ1, hρ1_one, htail1⟩ :=
    lattice_decay_shifted_tail_uniform (a := a) (σ := σ) (ε := tailEps) ha hσ htailEps_pos
  let ρ : ℝ := max 1 (max ρ0 ρ1)
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hρ0 : ρ0 ≤ ρ := by
    dsimp [ρ]
    exact (le_max_left ρ0 ρ1).trans (le_max_right 1 (max ρ0 ρ1))
  have hρ1 : ρ1 ≤ ρ := by
    dsimp [ρ]
    exact (le_max_right ρ0 ρ1).trans (le_max_right 1 (max ρ0 ρ1))
  let M : ℝ := 2 * ρ / a + 1
  have hM_pos : 0 < M := by
    dsimp [M]
    have hdiv : 0 < 2 * ρ / a := div_pos (mul_pos (by norm_num) hρ_pos) ha
    linarith
  let innerEps : ℝ := ε / (2 * M)
  have hinnerEps_pos : 0 < innerEps := by
    dsimp [innerEps]
    positivity
  have huc := uniformContinuous_of_continuous_polynomialDecay hgc hgd'
  rcases Metric.uniformContinuous_iff.mp huc innerEps hinnerEps_pos with
    ⟨δ0, hδ0_pos, hδ0⟩
  let δ : ℝ := min 1 (δ0 / 2)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min zero_lt_one (half_pos hδ0_pos)
  have hδ_le_one : δ ≤ 1 := by
    dsimp [δ]
    exact min_le_left 1 (δ0 / 2)
  refine ⟨δ, hδ_pos, hδ_le_one, ?_⟩
  intro h y hh
  have hh_one : |h| ≤ 1 := hh.trans hδ_le_one
  have hh_lt_δ0 : |h| < δ0 := by
    have hhalf : δ ≤ δ0 / 2 := by
      dsimp [δ]
      exact min_le_right 1 (δ0 / 2)
    linarith
  let d : ℤ → ℝ := fun n =>
    |g (y + h + a * (n : ℝ)) - g (y + a * (n : ℝ))|
  have hd_nonneg : ∀ n : ℤ, 0 ≤ d n := by
    intro n
    dsimp [d]
    exact abs_nonneg _
  have hd_uniform : ∀ n : ℤ, d n ≤ innerEps := by
    intro n
    have hdist_arg :
        dist (y + h + a * (n : ℝ)) (y + a * (n : ℝ)) = |h| := by
      rw [Real.dist_eq]
      congr 1
      ring
    have hdist : dist (y + h + a * (n : ℝ)) (y + a * (n : ℝ)) < δ0 := by
      rw [hdist_arg]
      exact hh_lt_δ0
    have hgdist := hδ0 hdist
    dsimp [d]
    exact le_of_lt (by simpa [Real.dist_eq] using hgdist)
  let tailShift : ℤ → ℝ := fun n =>
    if ρ ≤ |y + a * (n : ℝ)| then
      Real.rpow (1 + |y + h + a * (n : ℝ)|) (-σ)
    else 0
  let tailBase : ℤ → ℝ := fun n =>
    if ρ ≤ |y + a * (n : ℝ)| then latticeDecay a σ y n else 0
  have htailShift_nonneg : ∀ n : ℤ, 0 ≤ tailShift n := by
    intro n
    by_cases hn : ρ ≤ |y + a * (n : ℝ)|
    · simp [tailShift, hn,
        Real.rpow_nonneg (by positivity : 0 ≤ 1 + |y + h + a * (n : ℝ)|) (-σ)]
    · simp [tailShift, hn]
  have htailBase_nonneg : ∀ n : ℤ, 0 ≤ tailBase n := by
    intro n
    by_cases hn : ρ ≤ |y + a * (n : ℝ)|
    · simp [tailBase, hn, latticeDecay,
        Real.rpow_nonneg (by positivity : 0 ≤ 1 + |y + a * (n : ℝ)|) (-σ)]
    · simp [tailBase, hn]
  have htailShift_le_full :
      ∀ n : ℤ, tailShift n ≤ latticeDecay a σ (y + h) n := by
    intro n
    by_cases hn : ρ ≤ |y + a * (n : ℝ)|
    · simp [tailShift, hn, latticeDecay, add_assoc]
    · simp [tailShift, hn, latticeDecay,
        Real.rpow_nonneg (by positivity : 0 ≤ 1 + |y + h + a * (n : ℝ)|) (-σ)]
  have htailBase_le_full :
      ∀ n : ℤ, tailBase n ≤ latticeDecay a σ y n := by
    intro n
    by_cases hn : ρ ≤ |y + a * (n : ℝ)|
    · simp [tailBase, hn]
    · simp [tailBase, hn, latticeDecay,
        Real.rpow_nonneg (by positivity : 0 ≤ 1 + |y + a * (n : ℝ)|) (-σ)]
  have htailShift_sum : Summable tailShift := by
    exact Summable.of_nonneg_of_le htailShift_nonneg htailShift_le_full
      (summable_lattice_decay_uniform (a := a) (σ := σ) (y := y + h) ha hσ).1
  have htailBase_sum : Summable tailBase := by
    exact Summable.of_nonneg_of_le htailBase_nonneg htailBase_le_full
      (summable_lattice_decay_uniform (a := a) (σ := σ) (y := y) ha hσ).1
  have hd_decay :
      ∀ n : ℤ,
        d n ≤ C * Real.rpow (1 + |y + h + a * (n : ℝ)|) (-σ) +
          C * latticeDecay a σ y n := by
    intro n
    dsimp [d]
    calc
      |g (y + h + a * (n : ℝ)) - g (y + a * (n : ℝ))|
          = |g (y + h + a * (n : ℝ)) + -g (y + a * (n : ℝ))| := by
            ring_nf
      _ ≤ |g (y + h + a * (n : ℝ))| + |-g (y + a * (n : ℝ))| :=
            abs_add_le _ _
      _ = |g (y + h + a * (n : ℝ))| + |g (y + a * (n : ℝ))| := by
            rw [abs_neg]
      _ ≤ C * Real.rpow (1 + |y + h + a * (n : ℝ)|) (-σ) +
          C * latticeDecay a σ y n := by
            gcongr
            · exact hdecay_mul (y + h + a * (n : ℝ))
            · simpa [latticeDecay] using hdecay_mul (y + a * (n : ℝ))
  have hd_sum : Summable d := by
    have hmaj_sum :
        Summable (fun n : ℤ =>
          C * Real.rpow (1 + |y + h + a * (n : ℝ)|) (-σ) +
            C * latticeDecay a σ y n) := by
      have hs1 : Summable (fun n : ℤ =>
          C * latticeDecay a σ (y + h) n) :=
        (summable_lattice_decay_uniform (a := a) (σ := σ) (y := y + h) ha hσ).1.mul_left C
      have hs2 : Summable (fun n : ℤ => C * latticeDecay a σ y n) :=
        (summable_lattice_decay_uniform (a := a) (σ := σ) (y := y) ha hσ).1.mul_left C
      simpa [latticeDecay, add_assoc] using hs1.add hs2
    exact Summable.of_nonneg_of_le hd_nonneg hd_decay hmaj_sum
  constructor
  · exact hd_sum
  · refine hd_sum.tsum_le_of_sum_le ?_
    intro s
    let inner : ℤ → Prop := fun n => |y + a * (n : ℝ)| < ρ
    have hsplit := Finset.sum_filter_add_sum_filter_not (s := s) (p := inner) (f := d)
    have hinner_sum :
        (∑ n ∈ s with inner n, d n) ≤ ε / 2 := by
      have hcard_sum :
          (∑ n ∈ s with inner n, d n) ≤ ((s.filter inner).card : ℝ) * innerEps := by
        have h := Finset.sum_le_card_nsmul (s.filter inner) d innerEps
          (by
            intro n hn
            exact hd_uniform n)
        simpa [nsmul_eq_mul] using h
      have hfilter_subset :
          ((s.filter inner : Finset ℤ) : Set ℤ) ⊆ {n : ℤ | inner n} := by
        intro n hn
        exact (Finset.mem_filter.mp (by simpa using hn)).2
      have hfinite_inner : {n : ℤ | inner n}.Finite := by
        simpa [inner] using int_lattice_points_lt_finite (a := a) (ρ := ρ) (y := y) ha hρ_pos
      have hcard_nat :
          ((s.filter inner : Set ℤ).ncard) ≤ ({n : ℤ | inner n}.ncard) :=
        Set.ncard_le_ncard hfilter_subset hfinite_inner
      have hcard_le_ncard :
          ((s.filter inner).card : ℝ) ≤ (({n : ℤ | inner n}.ncard : ℕ) : ℝ) := by
        have hcard_eq :
            ((s.filter inner : Set ℤ).ncard) = (s.filter inner).card :=
          Set.ncard_coe_finset (s.filter inner)
        have hcard_nat' :
            (s.filter inner).card ≤ ({n : ℤ | inner n}.ncard) := by
          rw [← hcard_eq]
          exact hcard_nat
        exact_mod_cast hcard_nat'
      have hcount :
          (({n : ℤ | inner n}.ncard : ℕ) : ℝ) ≤ M := by
        simpa [inner, M] using
          int_lattice_points_lt_card_le (a := a) (ρ := ρ) (y := y) ha hρ_pos
      have hcard_le_M : ((s.filter inner).card : ℝ) ≤ M :=
        hcard_le_ncard.trans hcount
      have hprod_le : ((s.filter inner).card : ℝ) * innerEps ≤ M * innerEps :=
        mul_le_mul_of_nonneg_right hcard_le_M hinnerEps_pos.le
      have hM_inner : M * innerEps = ε / 2 := by
        dsimp [innerEps]
        field_simp [hM_pos.ne']
      linarith
    have htail_sum :
        (∑ n ∈ s with ¬ inner n, d n) ≤ ε / 2 := by
      have htail_point :
          ∀ n ∈ s.filter (fun n => ¬ inner n),
            d n ≤ C * tailShift n + C * tailBase n := by
        intro n hn
        have hn_not_inner : ¬ inner n := (Finset.mem_filter.mp hn).2
        have hn_tail : ρ ≤ |y + a * (n : ℝ)| := le_of_not_gt hn_not_inner
        have htail_eq_shift :
            tailShift n =
              Real.rpow (1 + |y + h + a * (n : ℝ)|) (-σ) := by
          simp [tailShift, hn_tail]
        have htail_eq_base :
            tailBase n = latticeDecay a σ y n := by
          simp [tailBase, hn_tail]
        simpa [htail_eq_shift, htail_eq_base] using hd_decay n
      have hfinite_tail :
          (∑ n ∈ s with ¬ inner n, d n) ≤
            ∑ n ∈ s with ¬ inner n, (C * tailShift n + C * tailBase n) := by
        exact Finset.sum_le_sum htail_point
      have hfinite_tail_eq :
          (∑ n ∈ s with ¬ inner n, (C * tailShift n + C * tailBase n)) =
            C * (∑ n ∈ s with ¬ inner n, tailShift n) +
              C * (∑ n ∈ s with ¬ inner n, tailBase n) := by
        simp [Finset.mul_sum, Finset.sum_add_distrib]
      have hsum_tailShift :
          (∑ n ∈ s with ¬ inner n, tailShift n) ≤ ∑' n : ℤ, tailShift n :=
        htailShift_sum.sum_le_tsum _ (fun n _ => htailShift_nonneg n)
      have hsum_tailBase :
          (∑ n ∈ s with ¬ inner n, tailBase n) ≤ ∑' n : ℤ, tailBase n :=
        htailBase_sum.sum_le_tsum _ (fun n _ => htailBase_nonneg n)
      have htailShift_tsum :
          (∑' n : ℤ, tailShift n) ≤ tailEps := by
        simpa [tailShift] using htail1 ρ h y hρ1 hh_one
      have htailBase_tsum :
          (∑' n : ℤ, tailBase n) ≤ tailEps := by
        simpa [tailBase] using htail0 ρ y hρ0
      have hfinite_to_tsum :
          (∑ n ∈ s with ¬ inner n, (C * tailShift n + C * tailBase n)) ≤
            C * (∑' n : ℤ, tailShift n) + C * (∑' n : ℤ, tailBase n) := by
        rw [hfinite_tail_eq]
        exact add_le_add
          (mul_le_mul_of_nonneg_left hsum_tailShift hC.le)
          (mul_le_mul_of_nonneg_left hsum_tailBase hC.le)
      have htail_to_eps :
          C * (∑' n : ℤ, tailShift n) + C * (∑' n : ℤ, tailBase n) ≤ ε / 2 := by
        have h1 := mul_le_mul_of_nonneg_left htailShift_tsum hC.le
        have h2 := mul_le_mul_of_nonneg_left htailBase_tsum hC.le
        have htail_eq : C * tailEps + C * tailEps = ε / 2 := by
          dsimp [tailEps]
          field_simp [hC.ne']
          ring
        linarith
      exact hfinite_tail.trans (hfinite_to_tsum.trans htail_to_eps)
    calc
      ∑ n ∈ s, d n
          = (∑ n ∈ s with inner n, d n) +
              ∑ n ∈ s with ¬ inner n, d n := hsplit.symm
      _ ≤ ε := by linarith


theorem window_lattice_row_sums
    {g : ℝ → ℝ} {C σ α y : ℝ}
    (hα : 0 < α) (hdec : HasDecayWithConstants g C σ) :
    (Summable (fun l : ℤ => |g (y - (l : ℝ))|) ∧
      (∑' l : ℤ, |g (y - (l : ℝ))|) ≤
        2 * C * masterSeries 1 σ) ∧
    (Summable (fun j : ℤ => |g (y + α * (j : ℝ))|) ∧
      (∑' j : ℤ, |g (y + α * (j : ℝ))|) ≤
        2 * C * masterSeries α σ) ∧
    (Summable (fun l : ℤ => |g (y - (l : ℝ))| ^ 2) ∧
      (∑' l : ℤ, |g (y - (l : ℝ))| ^ 2) ≤
        2 * C ^ 2 * masterSeries 1 (2 * σ)) := by
  rcases hdec with ⟨hC, hσ, hbound⟩
  have hσ2 : 1 < 2 * σ := by nlinarith
  have hdecay_mul :
      ∀ x : ℝ, |g x| ≤ C * Real.rpow (1 + |x|) (-σ) := by
    intro x
    have hbase_pos : 0 < 1 + |x| := by positivity
    calc
      |g x| ≤ C / ((1 + |x|) ^ σ) := hbound x
      _ = C * Real.rpow (1 + |x|) (-σ) := by
          have hneg :
              Real.rpow (1 + |x|) (-σ) = ((1 + |x|) ^ σ)⁻¹ := by
            simpa using Real.rpow_neg hbase_pos.le σ
          rw [hneg, div_eq_mul_inv]
  have hdecay_sq :
      ∀ x : ℝ, |g x| ^ 2 ≤ C ^ 2 * Real.rpow (1 + |x|) (-(2 * σ)) := by
    intro x
    have hbase_pos : 0 < 1 + |x| := by positivity
    have hx := hdecay_mul x
    have hrpow_nonneg : 0 ≤ Real.rpow (1 + |x|) (-σ) :=
      Real.rpow_nonneg hbase_pos.le (-σ)
    have hright_nonneg : 0 ≤ C * Real.rpow (1 + |x|) (-σ) :=
      mul_nonneg hC.le hrpow_nonneg
    calc
      |g x| ^ 2 ≤ (C * Real.rpow (1 + |x|) (-σ)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hx 2
      _ = C ^ 2 * (Real.rpow (1 + |x|) (-σ)) ^ 2 := by ring
      _ = C ^ 2 * Real.rpow (1 + |x|) (-(2 * σ)) := by
        have hp :
            (Real.rpow (1 + |x|) (-σ)) ^ 2 =
              Real.rpow (1 + |x|) (-σ * (2 : ℝ)) := by
          simpa using (Real.rpow_mul hbase_pos.le (-σ) (2 : ℝ)).symm
        rw [hp]
        ring_nf
  obtain ⟨hs1base, hle1base⟩ :=
    summable_lattice_decay_reflected_uniform (a := 1) (σ := σ) (y := y)
      (by norm_num) hσ
  have hG1sum :
      Summable (fun l : ℤ =>
        C * Real.rpow (1 + |y - 1 * (l : ℝ)|) (-σ)) :=
    hs1base.mul_left C
  have hF1nonneg : ∀ l : ℤ, 0 ≤ |g (y - (l : ℝ))| := by
    intro l
    exact abs_nonneg _
  have hF1le :
      ∀ l : ℤ,
        |g (y - (l : ℝ))| ≤
          C * Real.rpow (1 + |y - 1 * (l : ℝ)|) (-σ) := by
    intro l
    simpa using hdecay_mul (y - (l : ℝ))
  have hF1sum : Summable (fun l : ℤ => |g (y - (l : ℝ))|) :=
    Summable.of_nonneg_of_le hF1nonneg hF1le hG1sum
  have hF1tsum :
      (∑' l : ℤ, |g (y - (l : ℝ))|) ≤ 2 * C * masterSeries 1 σ := by
    calc
      (∑' l : ℤ, |g (y - (l : ℝ))|)
          ≤ ∑' l : ℤ, C * Real.rpow (1 + |y - 1 * (l : ℝ)|) (-σ) :=
            Summable.tsum_le_tsum hF1le hF1sum hG1sum
      _ = C * ∑' l : ℤ, Real.rpow (1 + |y - 1 * (l : ℝ)|) (-σ) := by
            rw [tsum_mul_left]
      _ ≤ C * (2 * masterSeries 1 σ) := mul_le_mul_of_nonneg_left hle1base hC.le
      _ = 2 * C * masterSeries 1 σ := by ring
  obtain ⟨hs2base, hle2base⟩ :=
    summable_lattice_decay_uniform (a := α) (σ := σ) (y := y) hα hσ
  have hG2sum :
      Summable (fun j : ℤ => C * latticeDecay α σ y j) :=
    hs2base.mul_left C
  have hF2nonneg : ∀ j : ℤ, 0 ≤ |g (y + α * (j : ℝ))| := by
    intro j
    exact abs_nonneg _
  have hF2le :
      ∀ j : ℤ,
        |g (y + α * (j : ℝ))| ≤ C * latticeDecay α σ y j := by
    intro j
    simpa [latticeDecay] using hdecay_mul (y + α * (j : ℝ))
  have hF2sum : Summable (fun j : ℤ => |g (y + α * (j : ℝ))|) :=
    Summable.of_nonneg_of_le hF2nonneg hF2le hG2sum
  have hF2tsum :
      (∑' j : ℤ, |g (y + α * (j : ℝ))|) ≤
        2 * C * masterSeries α σ := by
    calc
      (∑' j : ℤ, |g (y + α * (j : ℝ))|)
          ≤ ∑' j : ℤ, C * latticeDecay α σ y j :=
            Summable.tsum_le_tsum hF2le hF2sum hG2sum
      _ = C * ∑' j : ℤ, latticeDecay α σ y j := by
            rw [tsum_mul_left]
      _ ≤ C * (2 * masterSeries α σ) := mul_le_mul_of_nonneg_left hle2base hC.le
      _ = 2 * C * masterSeries α σ := by ring
  obtain ⟨hs3base, hle3base⟩ :=
    summable_lattice_decay_reflected_uniform (a := 1) (σ := 2 * σ) (y := y)
      (by norm_num) hσ2
  have hG3sum :
      Summable (fun l : ℤ =>
        C ^ 2 * Real.rpow (1 + |y - 1 * (l : ℝ)|) (-(2 * σ))) :=
    hs3base.mul_left (C ^ 2)
  have hF3nonneg : ∀ l : ℤ, 0 ≤ |g (y - (l : ℝ))| ^ 2 := by
    intro l
    exact sq_nonneg _
  have hF3le :
      ∀ l : ℤ,
        |g (y - (l : ℝ))| ^ 2 ≤
          C ^ 2 * Real.rpow (1 + |y - 1 * (l : ℝ)|) (-(2 * σ)) := by
    intro l
    simpa using hdecay_sq (y - (l : ℝ))
  have hF3sum : Summable (fun l : ℤ => |g (y - (l : ℝ))| ^ 2) :=
    Summable.of_nonneg_of_le hF3nonneg hF3le hG3sum
  have hF3tsum :
      (∑' l : ℤ, |g (y - (l : ℝ))| ^ 2) ≤
        2 * C ^ 2 * masterSeries 1 (2 * σ) := by
    calc
      (∑' l : ℤ, |g (y - (l : ℝ))| ^ 2)
          ≤ ∑' l : ℤ,
              C ^ 2 * Real.rpow (1 + |y - 1 * (l : ℝ)|) (-(2 * σ)) :=
            Summable.tsum_le_tsum hF3le hF3sum hG3sum
      _ = C ^ 2 *
            ∑' l : ℤ, Real.rpow (1 + |y - 1 * (l : ℝ)|) (-(2 * σ)) := by
            rw [tsum_mul_left]
      _ ≤ C ^ 2 * (2 * masterSeries 1 (2 * σ)) :=
            mul_le_mul_of_nonneg_left hle3base (sq_nonneg C)
      _ = 2 * C ^ 2 * masterSeries 1 (2 * σ) := by ring
  exact ⟨⟨hF1sum, hF1tsum⟩, ⟨⟨hF2sum, hF2tsum⟩, ⟨hF3sum, hF3tsum⟩⟩⟩



theorem lp_norm_apply_le_norm_int
    (c : ellp (2 : ℝ≥0∞)) (k : ℤ) :
    ‖c k‖ ≤ ‖c‖ := by
  simpa using
    lp.norm_apply_le_norm (p := (2 : ℝ≥0∞)) (E := fun _ : ℤ => ℂ)
      (by norm_num) c k



theorem summable_norm_mul_of_square_summable_int
    {u v : ℤ → ℂ}
    (hu : Summable (fun l : ℤ => ‖u l‖ ^ 2))
    (hv : Summable (fun l : ℤ => ‖v l‖ ^ 2)) :
    Summable (fun l : ℤ => ‖u l * v l‖) := by
  have hsum_major :
      Summable (fun l : ℤ => (‖u l‖ ^ 2 + ‖v l‖ ^ 2) / 2) := by
    simpa [div_eq_mul_inv, mul_add] using (hu.add hv).mul_right (2 : ℝ)⁻¹
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ hsum_major
  intro l
  rw [norm_mul]
  have hsq : 0 ≤ (‖u l‖ - ‖v l‖) ^ 2 := sq_nonneg _
  nlinarith [norm_nonneg (u l), norm_nonneg (v l), hsq]


theorem cauchy_schwarz_tsum_int
    {u v : ℤ → ℂ}
    (hu : Summable (fun l : ℤ => ‖u l‖ ^ 2))
    (hv : Summable (fun l : ℤ => ‖v l‖ ^ 2)) :
    (∑' l : ℤ, ‖u l * v l‖) ^ 2 ≤
      (∑' l : ℤ, ‖u l‖ ^ 2) * (∑' l : ℤ, ‖v l‖ ^ 2) := by
  let A : ℝ := ∑' l : ℤ, ‖u l‖ ^ 2
  let B : ℝ := ∑' l : ℤ, ‖v l‖ ^ 2
  have hprod : Summable (fun l : ℤ => ‖u l * v l‖) :=
    summable_norm_mul_of_square_summable_int hu hv
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact tsum_nonneg fun _ => sq_nonneg _
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact tsum_nonneg fun _ => sq_nonneg _
  have hfinite : ∀ s : Finset ℤ,
      ∑ l ∈ s, ‖u l * v l‖ ≤ Real.sqrt A * Real.sqrt B := by
    intro s
    have hcs :
        ∑ l ∈ s, ‖u l * v l‖ ≤
          Real.sqrt (∑ l ∈ s, ‖u l‖ ^ 2) *
            Real.sqrt (∑ l ∈ s, ‖v l‖ ^ 2) := by
      simpa [norm_mul] using
        (Real.sum_mul_le_sqrt_mul_sqrt s
          (fun l : ℤ => ‖u l‖) (fun l : ℤ => ‖v l‖))
    have hAs : ∑ l ∈ s, ‖u l‖ ^ 2 ≤ A := by
      dsimp [A]
      exact hu.sum_le_tsum s (fun _ _ => sq_nonneg _)
    have hBs : ∑ l ∈ s, ‖v l‖ ^ 2 ≤ B := by
      dsimp [B]
      exact hv.sum_le_tsum s (fun _ _ => sq_nonneg _)
    exact hcs.trans <|
      mul_le_mul (Real.sqrt_le_sqrt hAs) (Real.sqrt_le_sqrt hBs)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have htsum_le : (∑' l : ℤ, ‖u l * v l‖) ≤
      Real.sqrt A * Real.sqrt B :=
    hprod.tsum_le_of_sum_le hfinite
  have hsqrt_sq : (Real.sqrt A * Real.sqrt B) ^ 2 = A * B := by
    rw [mul_pow, Real.sq_sqrt hA_nonneg, Real.sq_sqrt hB_nonneg]
  have htsum_nonneg : 0 ≤ (∑' l : ℤ, ‖u l * v l‖) := by
    exact tsum_nonneg (fun l : ℤ => norm_nonneg (u l * v l))
  have hsqrt_nonneg : 0 ≤ Real.sqrt A * Real.sqrt B :=
    mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B)
  calc
    (∑' l : ℤ, ‖u l * v l‖) ^ 2 ≤
        (Real.sqrt A * Real.sqrt B) ^ 2 := by
      nlinarith
    _ = A * B := hsqrt_sq
    _ = (∑' l : ℤ, ‖u l‖ ^ 2) * (∑' l : ℤ, ‖v l‖ ^ 2) := rfl


theorem weighted_cauchy_schwarz_tsum
    {b z : ℤ → ℂ}
    (hb : Summable (fun l : ℤ => ‖b l‖))
    (hz : ∃ M : ℝ, ∀ l : ℤ, ‖z l‖ ≤ M) :
    ‖∑' l : ℤ, b l * z l‖ ^ 2 ≤
      (∑' l : ℤ, ‖b l‖) * (∑' l : ℤ, ‖b l‖ * ‖z l‖ ^ 2) := by
  rcases hz with ⟨M, hM⟩
  let K : ℝ := max M 0
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    exact le_max_right _ _
  have hzK : ∀ l : ℤ, ‖z l‖ ≤ K :=
    fun l => (hM l).trans (le_max_left _ _)
  have hBsum : Summable (fun l : ℤ => ‖b l‖ * ‖z l‖ ^ 2) := by
    have hmaj : Summable (fun l : ℤ => ‖b l‖ * K ^ 2) :=
      hb.mul_right (K ^ 2)
    refine Summable.of_nonneg_of_le
      (fun l => mul_nonneg (norm_nonneg _) (sq_nonneg _)) ?_ hmaj
    intro l
    have hzsq : ‖z l‖ ^ 2 ≤ K ^ 2 := by
      nlinarith [hzK l, norm_nonneg (z l), hK_nonneg]
    exact mul_le_mul_of_nonneg_left hzsq (norm_nonneg _)
  have hnormsum : Summable (fun l : ℤ => ‖b l * z l‖) := by
    have hmaj : Summable (fun l : ℤ => ‖b l‖ * K) := hb.mul_right K
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ hmaj
    intro l
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hzK l) (norm_nonneg _)
  let A : ℝ := ∑' l : ℤ, ‖b l‖
  let B : ℝ := ∑' l : ℤ, ‖b l‖ * ‖z l‖ ^ 2
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact tsum_nonneg fun _ => norm_nonneg _
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)
  have hfinite : ∀ s : Finset ℤ,
      ∑ l ∈ s, ‖b l * z l‖ ≤ Real.sqrt A * Real.sqrt B := by
    intro s
    have hcs_sq :
        (∑ l ∈ s, ‖b l * z l‖) ^ 2 ≤
          (∑ l ∈ s, ‖b l‖) *
            (∑ l ∈ s, ‖b l‖ * ‖z l‖ ^ 2) := by
      refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
        (fun l _ => norm_nonneg (b l))
        (fun l _ => mul_nonneg (norm_nonneg (b l)) (sq_nonneg (‖z l‖))) ?_
      intro l _
      rw [norm_mul]
      ring_nf
      exact le_rfl
    have hAs : ∑ l ∈ s, ‖b l‖ ≤ A := by
      dsimp [A]
      exact hb.sum_le_tsum s (fun _ _ => norm_nonneg _)
    have hBs : ∑ l ∈ s, ‖b l‖ * ‖z l‖ ^ 2 ≤ B := by
      dsimp [B]
      exact hBsum.sum_le_tsum s
        (fun _ _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))
    have hprod_le :
        (∑ l ∈ s, ‖b l‖) *
            (∑ l ∈ s, ‖b l‖ * ‖z l‖ ^ 2) ≤ A * B := by
      exact mul_le_mul hAs hBs
        (Finset.sum_nonneg fun _ _ =>
          mul_nonneg (norm_nonneg _) (sq_nonneg _))
        hA_nonneg
    have hsq_le : (∑ l ∈ s, ‖b l * z l‖) ^ 2 ≤ A * B :=
      hcs_sq.trans hprod_le
    have hsqrtAB : Real.sqrt (A * B) = Real.sqrt A * Real.sqrt B := by
      rw [Real.sqrt_mul hA_nonneg]
    rw [← hsqrtAB]
    exact Real.le_sqrt_of_sq_le hsq_le
  have htsum_le : (∑' l : ℤ, ‖b l * z l‖) ≤
      Real.sqrt A * Real.sqrt B :=
    hnormsum.tsum_le_of_sum_le hfinite
  have hnorm_tsum : ‖∑' l : ℤ, b l * z l‖ ≤
      ∑' l : ℤ, ‖b l * z l‖ :=
    norm_tsum_le_tsum_norm hnormsum
  have hmain_le : ‖∑' l : ℤ, b l * z l‖ ≤ Real.sqrt A * Real.sqrt B :=
    hnorm_tsum.trans htsum_le
  have hsqrt_sq : (Real.sqrt A * Real.sqrt B) ^ 2 = A * B := by
    rw [mul_pow, Real.sq_sqrt hA_nonneg, Real.sq_sqrt hB_nonneg]
  calc
    ‖∑' l : ℤ, b l * z l‖ ^ 2 ≤
        (Real.sqrt A * Real.sqrt B) ^ 2 := by
      nlinarith [norm_nonneg (∑' l : ℤ, b l * z l),
        mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B)]
    _ = A * B := hsqrt_sq
    _ = (∑' l : ℤ, ‖b l‖) * (∑' l : ℤ, ‖b l‖ * ‖z l‖ ^ 2) := rfl



theorem tsum_comp_le_tsum_of_injective_nonneg
    {b : ℤ → ℝ} (hb0 : ∀ j : ℤ, 0 ≤ b j) (hb : Summable b)
    {ν : ℤ → ℤ} (hν : Function.Injective ν) :
    Summable (fun k : ℤ => b (ν k)) ∧
      (∑' k : ℤ, b (ν k)) ≤ ∑' j : ℤ, b j := by
  refine ⟨hb.comp_injective hν, ?_⟩
  simpa [Function.comp_def] using
    (tsum_comp_le_tsum_of_inj (α := ℤ) (β := ℤ) (f := b) hb hb0
      (i := ν) hν)

end

end VendorE3
