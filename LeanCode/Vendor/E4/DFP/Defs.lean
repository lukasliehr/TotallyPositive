import Mathlib

open Matrix
open scoped BigOperators

noncomputable section

namespace VendorE4


def HasPolynomialOffDiagonalDecay (A : Int -> Int -> Real) : Prop :=
  exists C eta : Real, 0 < C /\ 1 < eta /\
    forall n m : Int, ‖A n m‖ <= C / (1 + |((n - m : Int) : Real)|)^eta



def IsTotallyPositive (A : Int -> Int -> Real) : Prop :=
  forall (r : Nat) (i j : Fin r -> Int), StrictMono i -> StrictMono j ->
    0 <= (Matrix.of fun p q => A (i p) (j q)).det


def IsTotallyPositiveFinite {n m : Nat} (B : Matrix (Fin n) (Fin m) Real) : Prop :=
  forall (r : Nat) (i : Fin r -> Fin n) (j : Fin r -> Fin m),
    StrictMono (fun p => (i p).val) ->
    StrictMono (fun q => (j q).val) ->
      0 <= (Matrix.of fun p q => B (i p) (j q)).det


def IsUniformlyAlternating (u : Int -> Real) : Prop :=
  forall k : Int, u k * u (k + 1) < 0


def IsUniformlyBoundedFromBelow (u : Int -> Real) : Prop :=
  exists c : Real, 0 < c /\ forall k : Int, |u k| >= c


def IsBoundedSequence (u : Int -> Real) : Prop :=
  exists M : Real, 0 < M /\ forall k : Int, |u k| <= M


def MatVec (G : Int -> Int -> Real) (c : Int -> Real) : Int -> Real :=
  fun k => tsum fun l : Int => G k l * c l


def IsL1Sequence (s : Int -> Real) : Prop :=
  Summable fun k : Int => |s k|


def l1Norm (s : Int -> Real) : Real :=
  tsum fun k : Int => |s k|


def pairing (y s : Int -> Real) : Real :=
  tsum fun k : Int => y k * s k


def truncation (K : Finset Int) (s : Int -> Real) : Int -> Real :=
  fun k => if k ∈ K then s k else 0


def UniformlySummableRows (G : Int -> Int -> Real) : Prop :=
  exists M : Real, 0 < M /\
    forall i : Int, Summable (fun j : Int => |G i j|) /\
      (tsum fun j : Int => |G i j|) <= M


def IsStrictlyAlternatingFin {n : Nat} (w : Fin n -> Real) : Prop :=
  (forall i : Fin n, w i ≠ 0) /\
    forall (i : Fin n) (h : i.val + 1 < n),
      w i * w ⟨i.val + 1, h⟩ < 0


def weightedSupNormFin {n : Nat} (v u : Fin n -> Real) : Real :=
  sSup (Set.range fun i : Fin n => |v i / u i|)


def weightedSupNormSeq (v u : Int -> Real) : Real :=
  sSup (Set.range fun i : Int => |v i / u i|)

end VendorE4
