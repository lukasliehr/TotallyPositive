module

public import LeanCode.Base
public import LeanCode.Vocab
public import LeanCode.ExternalInputs
public import LeanCode.Decay

@[expose] public section

open Matrix
open MeasureTheory
open scoped ENNReal
open lp

namespace Assembly





theorem TotallyPositiveHasDecay (g : ℝ → ℝ) (h : IsTotallyPositiveIntegrableContinuous g) :
    HasPolynomialDecay g :=
  tpic_hasPolynomialDecay g h

end Assembly
