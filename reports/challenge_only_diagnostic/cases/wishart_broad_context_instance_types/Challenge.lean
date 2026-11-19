module
public import Mathlib
public meta import Lean.Elab.Command
public meta import Lean.Meta.PP
public meta import Lean.Data.Json
public meta import Lean.Util.FoldConsts
public import TauCeti.Algebra.Quaternion.ComplexMatrix
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Basic
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Measurable
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.CStarAlgebra.Unitary.Maps
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000
open Set MeasureTheory
open scoped Matrix Quaternion BigOperators Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator ENNReal
namespace Wishart
abbrev SymmetricMatrix (p : ℕ) := selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)
def leadingScale (q m : ℕ) (S : Matrix (Fin (q+m)) (Fin (q+m)) ℝ) := S.submatrix (Fin.castAdd m) (Fin.castAdd m)
def selectedInverseRoot (q m : ℕ) (S : Matrix (Fin (q+m)) (Fin (q+m)) ℝ) := (CFC.sqrt (leadingScale q m S))⁻¹
namespace QuaternionMatrix
instance quaternionRealStarModule : StarModule ℝ ℍ[ℝ] where
  star_smul r q := by simpa only [star_trivial] using Quaternion.star_smul r q
instance quaternionMeasurableSpace : MeasurableSpace ℍ[ℝ] := borel _
instance quaternionBorelSpace : BorelSpace ℍ[ℝ] := ⟨rfl⟩
abbrev Hermitian (p : ℕ) := selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℍ[ℝ])
def complexRepresentation {m n : Type*} (A : Matrix m n ℍ[ℝ]) : Matrix (m × Fin 2) (n × Fin 2) ℂ := Matrix.comp m n (Fin 2) (Fin 2) ℂ (A.map Quaternion.toComplexMatrix)
section
variable {n : Type*} [Fintype n] [DecidableEq n]
def representationLeftInverse : Matrix (n × Fin 2) (n × Fin 2) ℂ →ₗ[ℝ] Matrix n n ℍ[ℝ] where
  toFun A := Matrix.of fun i j => ⟨(A (i,0) (j,0)).re, (A (i,0) (j,0)).im, -(A (i,1) (j,0)).re, (A (i,1) (j,0)).im⟩
  map_add' A B := by ext i j <;> simp [add_comm]
  map_smul' r A := by ext i j <;> simp [QuaternionAlgebra.smul_mk]
def sqrt (A : Matrix n n ℍ[ℝ]) : Matrix n n ℍ[ℝ] := representationLeftInverse (CFC.sqrt (complexRepresentation A))
end
end QuaternionMatrix
namespace FieldGaussian
variable (F : Type*) [NormedRing F] [StarRing F] [CStarRing F]
  [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [SMulCommClass ℝ F F] [IsScalarTower ℝ F F] [MeasurableSpace F] [BorelSpace F]
abbrev Row (m : ℕ) := PiLp 2 (fun _ : Fin m => F)
def rowFactorLinearMap {r m : ℕ} (R : Matrix (Fin r) (Fin m) F) : Row F r →ₗ[ℝ] Row F m where
  toFun z := WithLp.toLp 2 fun j => ∑ i, z i * R i j
  map_add' x y := by ext j; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c z := by ext j; simp [smul_mul_assoc, Finset.smul_sum]
def rowFactorCLM {r m : ℕ} (R : Matrix (Fin r) (Fin m) F) : Row F r →L[ℝ] Row F m := (rowFactorLinearMap F R).toContinuousLinearMap
end FieldGaussian
namespace ComplexMatrix
abbrev Hermitian (p : ℕ) := selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)
def hermitianLebesgue (p : ℕ) : Measure (Hermitian p) := (Module.finBasis ℝ (Hermitian p)).addHaar
end ComplexMatrix
end Wishart

run_cmd do
  let env ← Lean.getEnv
  for prefix in ["Wishart.SymmetricMatrix", "Wishart.selectedInverseRoot",
      "Wishart.QuaternionMatrix.complexRepresentation", "Wishart.QuaternionMatrix.sqrt",
      "Wishart.QuaternionMatrix.representationLeftInverse", "Wishart.FieldGaussian.Row",
      "Wishart.FieldGaussian.rowFactorLinearMap", "Wishart.FieldGaussian.rowFactorCLM",
      "Wishart.ComplexMatrix.hermitianLebesgue"] do
    for i in List.range 12 do
      let name := (prefix ++ "._proof_" ++ toString (i+1)).toName
      if let some ci := env.find? name then
        let pretty ← Lean.Elab.Command.liftTermElabM do
          return (← Lean.Meta.ppExpr ci.type).pretty
        let raw := reprStr ci.type
        let consts := ci.type.getUsedConstants.map Lean.Name.toString
        let row := Lean.Json.mkObj [
          ("kind", Lean.toJson "WISHART_CANONICAL_INSTANCE_TYPE"),
          ("name", Lean.toJson name.toString),
          ("levels", Lean.toJson (ci.levelParams.map Lean.Name.toString)),
          ("readable", Lean.toJson (String.ofList (pretty.toList.take 6000))),
          ("readable_characters", Lean.toJson pretty.length),
          ("readable_truncated", Lean.toJson (decide (6000 < pretty.length))),
          ("raw", Lean.toJson (String.ofList (raw.toList.take 6000))),
          ("raw_characters", Lean.toJson raw.length),
          ("raw_truncated", Lean.toJson (decide (6000 < raw.length))),
          ("type_constants", Lean.toJson consts)]
        Lean.logInfo m!"{row.compress}"
