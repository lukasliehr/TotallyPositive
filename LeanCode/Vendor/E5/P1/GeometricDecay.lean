import Mathlib
import LeanCode.Vendor.E5.Defs

noncomputable section

namespace VendorE5ExpDecay

theorem iterate_contraction (f : ℝ → ℝ) {L ρ v : ℝ}
    (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hstep : ∀ x : ℝ, v < x → f x ≤ ρ * f (x - L)) :
    ∀ n : ℕ, ∀ x : ℝ,
      v ≤ x - (n : ℝ) * L →
        f x ≤ ρ ^ n * f (x - (n : ℝ) * L) := by
  intro n
  induction n with
  | zero =>
      intro x _hx
      simp
  | succ n ih =>
      intro x hx
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
      have htail_gt : v < x - (n : ℝ) * L := by
        have hrewrite : x - (n : ℝ) * L =
            (x - ((n + 1 : ℕ) : ℝ) * L) + L := by
          rw [hcast]
          ring_nf
        rw [hrewrite]
        linarith
      have hstep_tail :
          f (x - (n : ℝ) * L) ≤
            ρ * f (x - ((n + 1 : ℕ) : ℝ) * L) := by
        have h := hstep (x - (n : ℝ) * L) htail_gt
        convert h using 2
        rw [hcast]
        ring_nf
      calc
        f x ≤ ρ ^ n * f (x - (n : ℝ) * L) := ih x htail_gt.le
        _ ≤ ρ ^ n * (ρ * f (x - ((n + 1 : ℕ) : ℝ) * L)) :=
          mul_le_mul_of_nonneg_left hstep_tail (pow_nonneg hρ n)
        _ = ρ ^ (n + 1) * f (x - ((n + 1 : ℕ) : ℝ) * L) := by
          rw [pow_succ]
          ring_nf

theorem geometric_decay (f : ℝ → ℝ) {v L ρ M' : ℝ}
    (hL : 0 < L) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hM' : 0 < M')
    (hstep : ∀ x : ℝ, v < x → f x ≤ ρ * f (x - L))
    (hbound : ∀ z : ℝ, z ≤ v + L → f z ≤ M') :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧
      ∀ x : ℝ, v ≤ x → f x ≤ C * Real.exp (-α * x) := by
  let α : ℝ := - Real.log ρ / L
  have hlog_neg : Real.log ρ < 0 := (Real.log_neg_iff hρ0).2 hρ1
  have hα : 0 < α := by
    dsimp [α]
    exact div_pos (neg_pos.mpr hlog_neg) hL
  have hαL : α * L = - Real.log ρ := by
    dsimp [α]
    field_simp [hL.ne']
  refine ⟨M' * Real.exp (α * (v + L)), α, ?_, hα, ?_⟩
  · exact mul_pos hM' (Real.exp_pos _)
  · intro x hx
    let n : ℕ := Nat.floor ((x - v) / L)
    have hy0 : 0 ≤ (x - v) / L := div_nonneg (sub_nonneg.mpr hx) hL.le
    have hnle : (n : ℝ) ≤ (x - v) / L := Nat.floor_le hy0
    have hylt : (x - v) / L < (n : ℝ) + 1 :=
      Nat.lt_floor_add_one ((x - v) / L)
    have hmul_le : (n : ℝ) * L ≤ x - v := by
      have h := mul_le_mul_of_nonneg_right hnle hL.le
      have hcancel : ((x - v) / L) * L = x - v := by field_simp [hL.ne']
      simpa [hcancel] using h
    have hiter_arg : v ≤ x - (n : ℝ) * L := by linarith
    have hmul_lt : x - v < ((n : ℝ) + 1) * L := by
      have h := mul_lt_mul_of_pos_right hylt hL
      have hcancel : ((x - v) / L) * L = x - v := by field_simp [hL.ne']
      simpa [hcancel] using h
    have hbound_arg : x - (n : ℝ) * L ≤ v + L := by linarith
    have hiter := iterate_contraction f hL hρ0.le hstep n x hiter_arg
    have hb := hbound (x - (n : ℝ) * L) hbound_arg
    have hfm : f x ≤ ρ ^ n * M' := by
      exact hiter.trans (mul_le_mul_of_nonneg_left hb (pow_nonneg hρ0.le n))
    have htail_lt : x - (v + L) < (n : ℝ) * L := by linarith
    have hlog_bound : (n : ℝ) * Real.log ρ ≤ -α * (x - (v + L)) := by
      have hmul_alpha_lt : α * (x - (v + L)) < α * ((n : ℝ) * L) :=
        mul_lt_mul_of_pos_left htail_lt hα
      have haux : α * (x - (v + L)) < -((n : ℝ) * Real.log ρ) := by
        calc
          α * (x - (v + L)) < α * ((n : ℝ) * L) := hmul_alpha_lt
          _ = (n : ℝ) * (α * L) := by ring_nf
          _ = (n : ℝ) * (-Real.log ρ) := by rw [hαL]
          _ = -((n : ℝ) * Real.log ρ) := by ring_nf
      linarith
    have hpow_exp : ρ ^ n = Real.exp ((n : ℝ) * Real.log ρ) := by
      rw [← Real.rpow_natCast]
      rw [Real.rpow_def_of_pos hρ0]
      ring_nf
    have hpow_le : ρ ^ n ≤ Real.exp (-α * (x - (v + L))) := by
      rw [hpow_exp]
      exact Real.exp_le_exp.mpr hlog_bound
    have hterm : ρ ^ n * M' ≤ M' * Real.exp (-α * (x - (v + L))) := by
      have h := mul_le_mul_of_nonneg_right hpow_le hM'.le
      simpa [mul_comm] using h
    calc
      f x ≤ ρ ^ n * M' := hfm
      _ ≤ M' * Real.exp (-α * (x - (v + L))) := hterm
      _ = (M' * Real.exp (α * (v + L))) * Real.exp (-α * x) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        ring_nf

end VendorE5ExpDecay
