module

public import LeanCode.Vendor.E1
public import LeanCode.Base

@[expose] public section

noncomputable section




theorem Assembly.Ext.E1_ExponentialDecay_thm
    (g : ℝ → ℝ) (h : Assembly.IsTotallyPositiveIntegrable g) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ x : ℝ, |g x| ≤ C * Real.exp (-c * |x|) :=
  ExpDecay.ExponentialDecay g h

end
