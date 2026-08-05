import LeanCode.Vendor.E5.P10.Part10.CaseGaussian
import LeanCode.Vendor.E5.P10.Part10.Deconvolution
import LeanCode.Vendor.E5.Defs

open MeasureTheory
open Filter
open scoped BigOperators Topology


theorem case_F (h4 : Statement_Part_4) (g : ℝ → ℝ)
    (Cst η : ℝ) (m : ℕ) (a : Fin (m + 1) → ℝ)
    (hCst : 0 < Cst) (hm : 1 ≤ m) (ha : ∀ j, a j ≠ 0)
    (hg : ∀ x : ℝ, g x = Cst * finiteType m a (x - η))
    (u v : ℝ) (huv : u < v)
    (hflat : ∀ x : ℝ, u < x → x < v → Halt g x = 0) :
  False := by
  let f : ℝ → ℝ := finiteType m a
  have hφ : ∀ x : ℝ, Halt f (x + 1) = -Halt f x := by
    intro x
    exact (H_antiper f x).1
  have hcross : StrictOneCrossing (Halt f) := by
    exact (h4 m hm a ha).2.2.2
  have hinterval : u - η < v - η := by linarith
  rcases no_flat (Halt f) hφ hcross (u - η) (v - η) hinterval with
    ⟨y, hyu, hyv, hy_ne⟩
  have hflat_y : Halt g (y + η) = 0 := hflat (y + η) (by linarith) (by linarith)
  have hg_fun : g = fun x : ℝ => Cst * f (x - η) := by
    funext x
    exact hg x
  have hscale_y : Halt g (y + η) = Cst * Halt f y := by
    rw [hg_fun]
    have hscale := H_scale f Cst η (y + η)
    convert hscale using 2
    ring_nf
  have hzero : Halt f y = 0 := by
    have hprod : Cst * Halt f y = 0 := by
      rw [← hscale_y, hflat_y]
    exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hCst)
  exact hy_ne hzero


theorem case_I (h4 : Statement_Part_4) (g : ℝ → ℝ)
    (hI : InfiniteProductForm g)
    (u v : ℝ) (huv : u < v)
    (hflat : ∀ x : ℝ, u < x → x < v → Halt g x = 0) :
  False := by
  classical
  rcases hI with
    ⟨Cst, η, a₁, a₂, F, σ, hCst, ha₁, ha₂, hg, hF_all, hstep, hlim⟩
  let S : ℕ → ℝ := fun N => (Finset.Icc 3 N).sum (fun j => σ j)
  let τ : ℕ → ℝ := fun N => S N - (Int.floor (S N) : ℝ)
  let τsub : ℕ → ℝ := fun n => τ (n + 2)
  let ρ : ℝ := (v - u) / 8
  have hρ : 0 < ρ := by
    dsimp [ρ]
    linarith
  have hF_iter : ∀ m : ℕ, 2 ≤ m → Continuous (F m) ∧ LatticeDominated (F m) := by
    intro m hm
    exact ⟨(hF_all m hm).1, (hF_all m hm).2.2⟩
  have hiter := iterate g Cst η F σ hCst hg hF_iter hstep u v huv hflat
  have hshift_flat :
      ∀ N : ℕ, 2 ≤ N →
        ∀ y : ℝ, u - η + τ N < y → y < v - η + τ N → Halt (F N) y = 0 := by
    intro N hN
    have hbase := hiter N hN
    have hαβ : u - η + S N < v - η + S N := by
      dsimp [S]
      linarith
    have hs := flat_shift (F N) (u - η + S N) (v - η + S N)
      (-(Int.floor (S N))) hαβ hbase
    intro y hyu hyv
    have hτ_shift : τ N = S N + ((-(Int.floor (S N)) : ℤ) : ℝ) := by
      dsimp [τ]
      rw [← Int.self_sub_floor (S N)]
      rw [show (((-(Int.floor (S N)) : ℤ) : ℝ)) = -(Int.floor (S N) : ℝ) by norm_num]
      ring
    apply hs y
    · rw [hτ_shift] at hyu
      linarith
    · rw [hτ_shift] at hyv
      linarith
  have hτsub_mem : ∀ n : ℕ, τsub n ∈ Set.Icc (0 : ℝ) 1 := by
    intro n
    constructor
    · change 0 ≤ S (n + 2) - (Int.floor (S (n + 2)) : ℝ)
      simp [Int.self_sub_floor, Int.fract_nonneg]
    · change S (n + 2) - (Int.floor (S (n + 2)) : ℝ) ≤ 1
      exact le_of_lt (by
        simpa [Int.self_sub_floor] using Int.fract_lt_one (S (n + 2)))
  rcases isCompact_Icc.tendsto_subseq hτsub_mem with ⟨t, ht_mem, κ, hκ_mono, hκ_tend⟩
  let L : ℝ := u - η + t + 2 * ρ
  let R : ℝ := v - η + t - 2 * ρ
  let K : Set ℝ := Set.Icc L R
  have hLR : L < R := by
    dsimp [L, R, ρ]
    linarith
  have hK_compact : IsCompact K := by
    dsimp [K]
    exact isCompact_Icc
  let r : ℝ → ℝ := conv (centeredExp a₁) (centeredExp a₂)
  have hNk_tend : Tendsto (fun k : ℕ => κ k + 2) atTop atTop := by
    exact Filter.tendsto_atTop_mono (fun k => Nat.le_add_right (κ k) 2)
      hκ_mono.tendsto_atTop
  have hτ_close : ∀ᶠ k : ℕ in atTop, |τ (κ k + 2) - t| ≤ ρ := by
    have hdist := (Metric.tendsto_nhds.mp hκ_tend) ρ hρ
    refine hdist.mono ?_
    intro k hk
    have hk' : |τsub (κ k) - t| < ρ := by
      simpa [Real.dist_eq, τsub] using hk
    simpa [τsub] using le_of_lt hk'
  have hHr_zero : ∀ x : ℝ, L < x → x < R → Halt r x = 0 := by
    intro x hxL hxR
    have hxK : x ∈ K := by
      dsimp [K]
      exact ⟨le_of_lt hxL, le_of_lt hxR⟩
    have hlimit_atTop :
        Tendsto (fun N : ℕ => Halt (F N) x) atTop (nhds (Halt r x)) := by
      have hunif := hlim K hK_compact
      exact hunif.tendsto_at hxK
    have hlimit_sub :
        Tendsto (fun k : ℕ => Halt (F (κ k + 2)) x) atTop (nhds (Halt r x)) := by
      exact hlimit_atTop.comp hNk_tend
    have hevent_zero : ∀ᶠ k : ℕ in atTop, Halt (F (κ k + 2)) x = 0 := by
      refine hτ_close.mono ?_
      intro k hk
      have hk_bounds := abs_le.mp hk
      have hleft : u - η + τ (κ k + 2) < x := by
        dsimp [L] at hxL
        linarith
      have hright : x < v - η + τ (κ k + 2) := by
        dsimp [R] at hxR
        linarith
      exact hshift_flat (κ k + 2) (by omega) x hleft hright
    have hzero_tend :
        Tendsto (fun k : ℕ => Halt (F (κ k + 2)) x) atTop (nhds (0 : ℝ)) := by
      have heq : (fun _ : ℕ => (0 : ℝ)) =ᶠ[atTop]
          fun k : ℕ => Halt (F (κ k + 2)) x :=
        hevent_zero.mono fun _ hk => hk.symm
      exact Filter.Tendsto.congr' heq tendsto_const_nhds
    exact tendsto_nhds_unique hlimit_sub hzero_tend
  let apar : Fin (1 + 1) → ℝ := fun i => if i = 0 then 1 / a₁ else 1 / a₂
  let f : ℝ → ℝ := finiteType 1 apar
  have hapar_ne : ∀ j : Fin (1 + 1), apar j ≠ 0 := by
    intro j
    fin_cases j <;> simp [apar, one_div, ha₁, ha₂]
  have hcross : StrictOneCrossing (Halt f) := by
    exact (h4 1 (by norm_num) apar hapar_ne).2.2.2
  have hanti : ∀ x : ℝ, Halt f (x + 1) = -Halt f x := by
    intro x
    exact (H_antiper f x).1
  have hr_translate : ∀ x : ℝ, Halt r x = Halt f (x + a₁ + a₂) := by
    intro x
    unfold Halt
    apply tsum_congr
    intro k
    have hq := (qq_translate a₁ a₂ ha₁ ha₂ (x + k)).2
    dsimp [r, f] at hq ⊢
    rw [hq]
    congr 2
    ring
  have hflat_f :
      ∀ z : ℝ, L + a₁ + a₂ < z → z < R + a₁ + a₂ → Halt f z = 0 := by
    intro z hzL hzR
    have hxL : L < z - a₁ - a₂ := by linarith
    have hxR : z - a₁ - a₂ < R := by linarith
    have hr0 := hHr_zero (z - a₁ - a₂) hxL hxR
    have ht := hr_translate (z - a₁ - a₂)
    have harg : z - a₁ - a₂ + a₁ + a₂ = z := by ring
    rw [harg] at ht
    rwa [ht] at hr0
  have hinterval : L + a₁ + a₂ < R + a₁ + a₂ := by
    linarith
  rcases no_flat (Halt f) hanti hcross (L + a₁ + a₂) (R + a₁ + a₂)
      hinterval with ⟨z, hzL, hzR, hz_ne⟩
  exact hz_ne (hflat_f z hzL hzR)


theorem Part_10_main (h4 : Statement_Part_4) : Statement_Part_10 := by
  classical
  intro g hg_cont hg_int hg_decay hreal u v huv
  by_contra hno
  have hflat : ∀ x : ℝ, u < x → x < v → Halt g x = 0 := by
    intro x hux hxv
    by_contra hx_ne
    exact hno ⟨x, hux, hxv, hx_ne⟩
  rcases hg_decay with ⟨C, c, hC, hc, hg_bound⟩
  rcases hreal with ⟨_hA, _hB, hcases⟩
  rcases hcases with hF | hrest
  · rcases hF with ⟨Cst, η, m, a, hCst, hm, ha, hg_form⟩
    exact case_F h4 g Cst η m a hCst hm ha hg_form u v huv hflat
  · rcases hrest with hG | hI
    · rcases hG with ⟨C₀, γ, hC₀, hγ, hFT, hhalf⟩
      exact case_G g hg_cont hg_int C c hC hc hg_bound C₀ γ hC₀ hγ hFT hhalf u v huv hflat
    · exact case_I h4 g hI u v huv hflat
