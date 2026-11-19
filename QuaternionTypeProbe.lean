module
public import Mathlib
public import TauCeti.Algebra.Quaternion.ComplexMatrix
public meta import Lean
@[expose] public section
open scoped Quaternion Matrix
noncomputable section
namespace WishartQuaternionProbe

def broad : ℍ[ℝ] →⋆ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ := Quaternion.toComplexMatrix

section
attribute [-instance] instCommCStarAlgebraComplex
def noComplexCStar : ℍ[ℝ] →⋆ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ := Quaternion.toComplexMatrix
end

section
attribute [local instance 3000] NormedField.toNormedCommRing
def normedField : ℍ[ℝ] →⋆ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ := Quaternion.toComplexMatrix
end

section
attribute [local instance 3000] NormedField.toNormedCommRing
attribute [local instance 3000] StarMul.toInvolutiveStar
def normedFieldStarMul : ℍ[ℝ] →⋆ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ := Quaternion.toComplexMatrix
end

open Lean Elab Command Meta in
run_cmd do
  let env ← getEnv
  let expected := (env.find? ``Quaternion.toComplexMatrix).get!.type
  for name in [``broad, ``noComplexCStar, ``normedField, ``normedFieldStarMul] do
    let actual := (env.find? name).get!.type
    let a := actual.getAppArgs
    let b := expected.getAppArgs
    let mismatches := (List.range (min a.size b.size)).filter (fun i => a[i]! != b[i]!)
    logInfo m!"WISHART_TYPE {name} exact={actual == expected} differing_arguments={mismatches}"
  liftTermElabM do
    withOptions (fun o => ((o.setBool `pp.all true).setBool `pp.universes false).setBool `pp.proofs true) do
      for i in [:expected.getAppArgs.size] do
        let term ← ppExpr expected.getAppArgs[i]!
        logInfo m!"WISHART_SOURCE_ARG {i} {term}"

end WishartQuaternionProbe
end
