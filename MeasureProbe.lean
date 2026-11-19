module
public import Mathlib
public import WishartSourceContext
public import TauCeti.Probability.Distributions.Wishart.Nonsingular
public meta import Lean
@[expose] public section
open MeasureTheory
open scoped Quaternion Matrix BigOperators RealInnerProductSpace
noncomputable section
namespace WishartInstanceProbe
section
def lawstandard {p : ℕ} (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) :
    Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  TauCeti.Probability.nonsingularWishartMeasure n S
def normstandard (p : ℕ) : NormedAddCommGroup (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  TauCeti.symmetricMatrixNormedAddCommGroup p
end
section
attribute [local instance 4100] Matrix.instStarModule
def lawmatrix {p : ℕ} (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) :
    Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  TauCeti.Probability.nonsingularWishartMeasure n S
def normmatrix (p : ℕ) : NormedAddCommGroup (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  TauCeti.symmetricMatrixNormedAddCommGroup p
end
section
attribute [local instance 4100] Matrix.instStarModule StarAddMonoid.toInvolutiveStar
def lawadd {p : ℕ} (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) :
    Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  TauCeti.Probability.nonsingularWishartMeasure n S
def normadd (p : ℕ) : NormedAddCommGroup (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  TauCeti.symmetricMatrixNormedAddCommGroup p
end
section
attribute [local instance 4100] Matrix.instStarModule StarMul.toInvolutiveStar
def lawmul {p : ℕ} (n : ℝ) (S : Matrix (Fin p) (Fin p) ℝ) :
    Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  TauCeti.Probability.nonsingularWishartMeasure n S
def normmul (p : ℕ) : NormedAddCommGroup (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  TauCeti.symmetricMatrixNormedAddCommGroup p
end
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (expectedName, names) in [
    (``TauCeti.Probability.nonsingularWishartMeasure, [``lawstandard, ``lawmatrix, ``lawadd, ``lawmul]),
    (``TauCeti.symmetricMatrixNormedAddCommGroup, [``normstandard, ``normmatrix, ``normadd, ``normmul])
] do
    let expected := (env.find? expectedName).get!.type
    for name in names do
      let actual := (env.find? name).get!.type
      logInfo m!"WISHART_INSTANCE {name} vs {expectedName} equal={actual == expected}"
end WishartInstanceProbe
end
