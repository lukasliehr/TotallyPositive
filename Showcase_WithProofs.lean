import Mathlib
import LeanCode
open MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section


def IsTP (g : ℝ → ℝ) : Prop :=
  g ≠ 0 ∧
  ∀ n : ℕ, ∀ a b : Fin n → ℝ,
    StrictMono a → StrictMono b →
    0 ≤ Matrix.det (Matrix.of fun i j => g (a i - b j))


def IsTPIntegrableContinuous (g : ℝ → ℝ) : Prop :=
  IsTP g ∧ Integrable g ∧ Continuous g


def GaborAtom_Function
    (g : ℝ → ℝ) (α β : ℝ) (m n : ℤ) : ℝ → ℂ :=
  fun x =>
    Complex.exp (2 * Real.pi * Complex.I * β * n * x) *
      g (x - α * m)


lemma gaborAtom_memL2
    (g : ℝ → ℝ) (hg : IsTPIntegrableContinuous g)
    (α β : ℝ) (m n : ℤ) :
    MemLp (GaborAtom_Function g α β m n) 2 volume := by
  have hTP : Assembly.IsTotallyPositive g := by
    intro k a b ha hb
    exact hg.1.2 k a b ha hb
  have hAssembly : Assembly.IsTotallyPositiveIntegrableContinuous g :=
    ⟨hTP, hg.2.1, hg.2.2⟩
  change MemLp (Assembly.GaborAtom g α β m n) 2 volume
  exact Assembly.memL2_GaborAtom g hg.2.2
    (Assembly.TotallyPositiveHasDecay g hAssembly) α β m n


def GaborAtom
    (g : ℝ → ℝ) (hg : IsTPIntegrableContinuous g)
    (α β : ℝ) (m n : ℤ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (gaborAtom_memL2 g hg α β m n).toLp


def IsGaborFrame
    (g : ℝ → ℝ) (hyp : IsTPIntegrableContinuous g)
    (α β : ℝ) : Prop :=
  ∃ A B : ℝ, 0 < A ∧ A ≤ B ∧
  ∀ f : Lp ℂ 2 volume,
    let E :=
      ∑' (m : ℤ) (n : ℤ),
        ‖⟪f, GaborAtom g hyp α β m n⟫_ℂ‖ ^ 2
    A * ‖f‖ ^ 2 ≤ E ∧ E ≤ B * ‖f‖ ^ 2


theorem TPFrameSet
    {α β : ℝ} (hyp1 : 0 < α) (hyp2 : 0 < β) (hyp3 : α * β < 1)
    (g : ℝ → ℝ) (hyp4 : IsTPIntegrableContinuous g) :
    IsGaborFrame g hyp4 α β := by
  have hTP : Assembly.IsTotallyPositive g := by
    intro k a b ha hb
    exact hyp4.1.2 k a b ha hb
  have hAssembly : Assembly.IsTotallyPositiveIntegrableContinuous g :=
    ⟨hTP, hyp4.2.1, hyp4.2.2⟩
  rcases Assembly.frameSetConjecture hyp1 hyp2 hyp3 g hAssembly hyp4.1.1 with
    ⟨A, B, hA, hAB, hframe⟩
  refine ⟨A, B, hA, hAB, ?_⟩
  intro f
  have hAtom (m n : ℤ) :
      GaborAtom g hyp4 α β m n =
        Assembly.GaborAtom_L2 g hAssembly.2.2
          (Assembly.TotallyPositiveHasDecay g hAssembly) α β m n := by
    apply Lp.ext_iff.mpr
    calc
      (GaborAtom g hyp4 α β m n : ℝ → ℂ)
          =ᵐ[(volume : Measure ℝ)] GaborAtom_Function g α β m n :=
        MemLp.coeFn_toLp _
      _ = Assembly.GaborAtom g α β m n := by
        rfl
      _ =ᵐ[(volume : Measure ℝ)]
          (Assembly.GaborAtom_L2 g hAssembly.2.2
            (Assembly.TotallyPositiveHasDecay g hAssembly) α β m n : ℝ → ℂ) :=
        (MemLp.coeFn_toLp _).symm
  simpa only [hAtom] using hframe f
