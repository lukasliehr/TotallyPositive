module

public import LeanCode.Vendor.E5.Defs
public import LeanCode.Vendor.E5.P1_Export
public import LeanCode.Vendor.E5.P2
public import LeanCode.Vendor.E5.P3
public import LeanCode.Vendor.E5.P4
public import LeanCode.Vendor.E5.P5
public import LeanCode.Vendor.E5.P6
public import LeanCode.Vendor.E5.P7
public import LeanCode.Vendor.E5.P8_Export
public import LeanCode.Vendor.E5.P9
public import LeanCode.Vendor.E5.P10
public import LeanCode.Vendor.E5.P11
public import LeanCode.Vendor.E5.P12

@[expose] public section

open MeasureTheory

namespace VendorE5





theorem ZakZero_final : Statement_Part_12 :=
  Part_12_main Part_1_main Part_2_main
    (Part_7_main (Part_5_main Part_3_main) Part_6_main)
    Part_8_main (Part_9_main Part_3_main) (Part_10_main Part_4_main) Part_11_main



noncomputable def Z (g : ℝ → ℝ) (_ : HasExponentialDecay g) :  ℝ × ℝ → ℂ :=
  fun z => ∑' k : ℤ, Complex.exp (2 * Real.pi * Complex.I * k * z.2) * g (z.1 - k)

theorem test (g : ℝ → ℝ) (h : IsTotallyPositiveIntegrableContinuous g) :
  HasExponentialDecay g := Part_1_main g h

theorem VinogradovUlitskaya (g : ℝ → ℝ) (hg : g ≠ 0)
    (h : IsTotallyPositiveIntegrableContinuous g) :
  ∃! x : ℝ, x ∈ Set.Ico (0:ℝ) 1 ∧ Z g (test g h) (x, 1/2) = 0 :=
  ZakZero_final g hg h

#print axioms ZakZero_final
#print axioms VinogradovUlitskaya

end VendorE5
