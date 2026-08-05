import Mathlib
import LeanCode.Vendor.E5.Defs

open Filter Topology





namespace Part7


theorem prod_inv {ι : Type*} (f : ι → ℂ) (L : ℂ)
    (hf : ∀ i, f i ≠ 0) (hL : HasProd f L) (hL0 : L ≠ 0) :
    HasProd (fun i => (f i)⁻¹) L⁻¹ := by
  have h1 := Filter.Tendsto.inv₀ hL hL0
  simp only [← Finset.prod_inv_distrib] at h1
  exact h1


theorem prod_norm {ι : Type*} (f : ι → ℂ) (L : ℂ) (hL : HasProd f L) :
    HasProd (fun i => ‖f i‖) ‖L‖ := hL.norm


theorem prod_ge_one {ι : Type*} (h : ι → ℝ) (M : ℝ)
    (hh : ∀ i, 1 ≤ h i) (hM : HasProd h M) : 1 ≤ M :=
  ge_of_tendsto' hM (fun _ => Finset.one_le_prod (fun i _ => hh i))

end Part7
