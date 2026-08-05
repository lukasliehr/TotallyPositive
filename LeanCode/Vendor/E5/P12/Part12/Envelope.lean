import Mathlib
import LeanCode.Vendor.E5.Defs

open MeasureTheory














namespace Part12



theorem exp_summable (c : ℝ) (hc : 0 < c) :
    Summable (fun n : ℤ => Real.exp (-c * |(n : ℝ)|)) := by

  have hbase : Summable (fun n : ℕ => Real.exp (-c) ^ n) :=
    summable_geometric_of_lt_one (Real.exp_nonneg _)
      (by rw [Real.exp_lt_one_iff]; linarith)
  apply Summable.of_nat_of_neg_add_one
  ·
    refine hbase.congr (fun n => ?_)
    rw [Int.cast_natCast, Nat.abs_cast, ← Real.exp_nat_mul]
    congr 1; ring
  ·
    refine (hbase.mul_right (Real.exp (-c))).congr (fun n => ?_)
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    push_cast
    rw [abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
    congr 1; ring



theorem envelope (g : ℝ → ℝ) (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hbound : ∀ t : ℝ, |g t| ≤ C * Real.exp (-c * |t|)) :
    ∀ x t : ℝ, |g (x + t)| ≤ C * Real.exp (c * |x|) * Real.exp (-c * |t|) := by
  intro x t
  have htri : |t| - |x| ≤ |x + t| := by
    have h := abs_sub_abs_le_abs_sub t (-x)
    rw [abs_neg, sub_neg_eq_add, add_comm t x] at h
    exact h
  have harg : -c * |x + t| ≤ -c * (|t| - |x|) := by
    nlinarith [mul_nonneg hc.le (sub_nonneg.mpr htri)]
  calc |g (x + t)|
      ≤ C * Real.exp (-c * |x + t|) := hbound (x + t)
    _ ≤ C * Real.exp (-c * (|t| - |x|)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) hC.le
    _ = C * Real.exp (c * |x|) * Real.exp (-c * |t|) := by
        rw [show -c * (|t| - |x|) = c * |x| + -c * |t| from by ring, Real.exp_add]; ring




theorem summable_halt (g : ℝ → ℝ) (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hbound : ∀ t : ℝ, |g t| ≤ C * Real.exp (-c * |t|)) (x : ℝ) :
    (Summable (fun k : ℤ => |g (x + k)|) ∧
      ∀ k : ℤ, |g (x + k)| ≤ C * Real.exp (c * |x|) * Real.exp (-c * |(k : ℝ)|)) ∧
    (Summable (fun k : ℤ => (-1 : ℝ) ^ k * g (x + k)) ∧
      Summable (fun k : ℤ => |(-1 : ℝ) ^ k * g (x + k)|)) := by
  have henv : ∀ k : ℤ,
      |g (x + k)| ≤ C * Real.exp (c * |x|) * Real.exp (-c * |(k : ℝ)|) :=
    fun k => envelope g C c hC hc hbound x (k : ℝ)
  have hEnvSum : Summable
      (fun k : ℤ => C * Real.exp (c * |x|) * Real.exp (-c * |(k : ℝ)|)) :=
    (exp_summable c hc).mul_left (C * Real.exp (c * |x|))
  have habs : Summable (fun k : ℤ => |g (x + k)|) :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) henv hEnvSum
  have habs' : Summable (fun k : ℤ => |(-1 : ℝ) ^ k * g (x + k)|) := by
    have heq : (fun k : ℤ => |(-1 : ℝ) ^ k * g (x + k)|)
        = (fun k : ℤ => |g (x + k)|) := by
      funext k; rw [abs_mul, abs_neg_one_zpow, one_mul]
    rw [heq]; exact habs
  exact ⟨⟨habs, henv⟩, Summable.of_abs habs', habs'⟩




theorem summable_cols (g : ℝ → ℝ) (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hbound : ∀ t : ℝ, |g t| ≤ C * Real.exp (-c * |t|)) (x : ℝ) :
    ((∀ n : ℤ, |g (x + 2 * n)| ≤
        C * Real.exp (c * |x|) * Real.exp (-(2 * c) * |(n : ℝ)|)) ∧
      Summable (fun n : ℤ => g (x + 2 * n)) ∧
      Summable (fun n : ℤ => |g (x + 2 * n)|)) ∧
    ((∀ n : ℤ, |g (x - 1 + 2 * n)| ≤
        C * Real.exp (c * (|x| + 1)) * Real.exp (-(2 * c) * |(n : ℝ)|)) ∧
      Summable (fun n : ℤ => g (x - 1 + 2 * n)) ∧
      Summable (fun n : ℤ => |g (x - 1 + 2 * n)|)) := by
  have h2c : (0 : ℝ) < 2 * c := by linarith

  have hexp : ∀ n : ℤ,
      Real.exp (-c * |2 * (n : ℝ)|) = Real.exp (-(2 * c) * |(n : ℝ)|) := by
    intro n
    congr 1
    rw [abs_mul, show |(2 : ℝ)| = 2 from by norm_num]; ring

  have hb_a : ∀ n : ℤ, |g (x + 2 * n)| ≤
      C * Real.exp (c * |x|) * Real.exp (-(2 * c) * |(n : ℝ)|) := by
    intro n
    have h := envelope g C c hC hc hbound x (2 * (n : ℝ))
    rwa [hexp n] at h
  have hEnvSum_a : Summable
      (fun n : ℤ => C * Real.exp (c * |x|) * Real.exp (-(2 * c) * |(n : ℝ)|)) :=
    (exp_summable (2 * c) h2c).mul_left (C * Real.exp (c * |x|))
  have habs_a : Summable (fun n : ℤ => |g (x + 2 * n)|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hb_a hEnvSum_a
  have hsum_a : Summable (fun n : ℤ => g (x + 2 * n)) := Summable.of_abs habs_a

  have hxm1 : |x - 1| ≤ |x| + 1 := by
    rcases abs_cases (x - 1) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; linarith [le_abs_self x]
    · rw [h]; linarith [neg_abs_le x]
  have hb_b : ∀ n : ℤ, |g (x - 1 + 2 * n)| ≤
      C * Real.exp (c * (|x| + 1)) * Real.exp (-(2 * c) * |(n : ℝ)|) := by
    intro n
    have h := envelope g C c hC hc hbound (x - 1) (2 * (n : ℝ))
    rw [hexp n] at h
    have hmono : Real.exp (c * |x - 1|) ≤ Real.exp (c * (|x| + 1)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hxm1 hc.le)
    calc |g (x - 1 + 2 * n)|
        ≤ C * Real.exp (c * |x - 1|) * Real.exp (-(2 * c) * |(n : ℝ)|) := h
      _ ≤ C * Real.exp (c * (|x| + 1)) * Real.exp (-(2 * c) * |(n : ℝ)|) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
          exact mul_le_mul_of_nonneg_left hmono hC.le
  have hEnvSum_b : Summable
      (fun n : ℤ => C * Real.exp (c * (|x| + 1)) * Real.exp (-(2 * c) * |(n : ℝ)|)) :=
    (exp_summable (2 * c) h2c).mul_left (C * Real.exp (c * (|x| + 1)))
  have habs_b : Summable (fun n : ℤ => |g (x - 1 + 2 * n)|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hb_b hEnvSum_b
  have hsum_b : Summable (fun n : ℤ => g (x - 1 + 2 * n)) := Summable.of_abs habs_b
  exact ⟨⟨hb_a, hsum_a, habs_a⟩, ⟨hb_b, hsum_b, habs_b⟩⟩

end Part12
