/-
Copyright (c) 2026 Caius Folkerts. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The exact type serializer adapts the audit accompanying sublattice_resolutions
in caiusdfolkerts/lean. This module is audit infrastructure, not a provider of
mathematical axioms or theorem statements.
-/
module

/- BEGIN GENERATED LOCAL IMPORTS -/
import all PaperVerification.PowerOperators
import all PaperVerification.FermionMomentRecurrence
import all PaperVerification.PowerRecurrence
import all PaperVerification.PowerParameters
import all PaperVerification.PowerFullSupport
import all PaperVerification.PowerBoundary
import all PaperVerification.PowerArtin
import all PaperVerification.PowerSpanning
import all PaperVerification.PowerConjugation
import all PaperVerification.PowerCoordinateRestriction
import all TauCeti.RingTheory.RootsOfUnity.Basic
import all TauCeti.RingTheory.MvPolynomial.Homogeneous
import all PaperVerification.PowerHomogeneity
import all TauCeti.Algebra.Homology.HomologicalComplex.Basic
import all TauCeti.Algebra.Homology.Homotopy
import all TauCeti.Algebra.Homology.Linear
import all TauCeti.LinearAlgebra.CliffordAlgebra.Grading
import all TauCeti.LinearAlgebra.CliffordAlgebra.Contraction
import all TauCeti.LinearAlgebra.ExteriorPower.Basic
import all TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
import all TauCeti.RingTheory.KoszulComplex.Basic
import all TauCeti.RingTheory.KoszulComplex.Regular
import all PaperVerification.KoszulSyzygies
import all PaperVerification.PowerComplex
import all PaperVerification.PowerDegreeSpaces
import all PaperVerification.PowerCoefficientMap
import all PaperVerification.FermionSupport
import all PaperVerification.FermionRadical
import all PaperVerification.HomogeneousLocalization
import all TauCeti.RingTheory.Ideal.Colon
import all TauCeti.RingTheory.Ideal.AssociatedPrime.Basic
import all TauCeti.RingTheory.Ideal.AssociatedPrime.Localization
import all TauCeti.Topology.KrullDimension.Basic
import all TauCeti.Topology.KrullDimension.Local
import all TauCeti.Topology.PureDimension
import all TauCeti.Order.Catenary
import all TauCeti.RingTheory.Catenary
import all TauCeti.Topology.KrullDimension.Irreducible
import all TauCeti.Topology.KrullDimension.ClosedCover
import all TauCeti.RingTheory.KrullDimension.Quotient
import all TauCeti.Algebra.Ring.Subgroup
import all TauCeti.RingTheory.Ideal.Operations
import all TauCeti.Algebra.Module.Projective.LinearMap
import all TauCeti.RingTheory.Regular.LinearMap
import all TauCeti.Algebra.Category.ModuleCat.Ext.Basic
import all TauCeti.Data.ENat.Basic
import all TauCeti.RingTheory.Localization.Module
import all TauCeti.RingTheory.Depth.Basic
import all TauCeti.RingTheory.Localization.Annihilator
import all TauCeti.RingTheory.KrullDimension.Module
import all TauCeti.RingTheory.CohenMacaulay.Basic
import all TauCeti.RingTheory.KrullDimension.Regular
import all TauCeti.Data.ENat.Monoid
import all TauCeti.RingTheory.LocalRing.MaximalIdeal.Generator
import all TauCeti.RingTheory.Ideal.Quotient.Colon
import all TauCeti.RingTheory.CohenMacaulay.Normal
import all TauCeti.RingTheory.IntegralClosure.GoingDown
import all TauCeti.RingTheory.KrullDimension.Fiber
import all TauCeti.RingTheory.LocalRing.Quotient
import all TauCeti.RingTheory.CohenMacaulay.RegularSequence
import all TauCeti.LinearAlgebra.Span.Basic
import all TauCeti.RingTheory.LocalRing.MaximalIdeal.Square
import all TauCeti.RingTheory.RegularLocalRing.Basic
import all TauCeti.Algebra.Module.SpanRank
import all TauCeti.LinearAlgebra.Matrix.Adjugate.Basic
import all TauCeti.RingTheory.Spectrum.Prime.Point
import all TauCeti.RingTheory.Finiteness.Nakayama
import all TauCeti.RingTheory.Regular.RegularSequence
import all TauCeti.RingTheory.Depth.WeaklyRegular
import all TauCeti.RingTheory.CohenMacaulay.Height
import all TauCeti.RingTheory.RegularLocalRing.CohenMacaulay
import all TauCeti.RingTheory.KrullDimension.Integral
import all TauCeti.RingTheory.KrullDimension.Basic
import all TauCeti.RingTheory.KrullDimension.FiniteType
import all TauCeti.RingTheory.KrullDimension.Polynomial
import all PaperVerification.HomogeneousRegularSequence
import all PaperVerification.FermionOrdinaryParameters
import all PaperVerification.PowerGenericParameters
import all TauCeti.LinearAlgebra.Matrix.Rank
import all PaperVerification.MatrixRank
import all PaperVerification.RankSpecialization
import all TauCeti.RingTheory.MvPolynomial.RestrictSupport
import all PaperVerification.PowerDegreeMatrices
import all PaperVerification.PowerDegreeQuotient
import all PaperVerification.PowerStabilizerCharacteristic
import all PaperVerification.PowerGroupedParameters
import all PaperVerification.QuotientLinearAction
import all PaperVerification.PowerPermutationAction
import all PaperVerification.EquivariantHomExact
import all PaperVerification.ProjectedRankSpecialization
import all PaperVerification.EquivariantHomMatrices
import all PaperVerification.EquivariantHomSpecialization
import all PaperVerification.EquivariantHomRank
import all PaperVerification.EquivariantCokernelSpecialization
import all PaperVerification.PowerDegreeActions
import all PaperVerification.PowerOriginalDegreeMatrices
import all PaperVerification.PowerArtinBasis
import all TauCeti.Algebra.DirectSum.Internal
import all TauCeti.LinearAlgebra.Graded.LinearMap
import all TauCeti.Order.CompactlyGenerated
import all TauCeti.Algebra.Module.Submodule.Finite
import all TauCeti.Algebra.Module.GradedModule.Internal
import all TauCeti.Algebra.Module.GradedModule.Quotient
import all PaperVerification.FermionGradedHilbert
import all PaperVerification.FermionFiniteGrading
import all PaperVerification.GradedDimensionComparison
import all PaperVerification.HilbertTowerCount
import all PaperVerification.FermionPolynomialHilbert
import all PaperVerification.FermionIdealHilbert
import all PaperVerification.FermionCompleteIntersectionLength
import all PaperVerification.FermionOrdinaryLength
import all PaperVerification.PowerBasisTheorem
import all PaperVerification.PowerOriginalBasis
import all PaperVerification.PowerOriginalAction
import all PaperVerification.PowerOriginalDegreePresentation
import all PaperVerification.PowerHarmonicWitness
import all PaperVerification.PowerFischerPairing
import all PaperVerification.PowerHarmonicQuotient
import all PaperVerification.PowerStandardHarmonics
import all PaperVerification.PowerStandardDual
import all PaperVerification.EquivariantSection
import all PaperVerification.SelfDualSubrepresentation
import all PaperVerification.PowerResonantStandard
import all TauCeti.RingTheory.MvPolynomial.Symmetric.Homogeneous
import all TauCeti.Data.Sym.Basic
import all TauCeti.RingTheory.MvPolynomial.Symmetric.Complete.Basic
import all TauCeti.RingTheory.PowerSeries.Rescale
import all TauCeti.RingTheory.MvPolynomial.Symmetric.Elementary
import all TauCeti.Algebra.BigOperators.Finset.Range
import all TauCeti.RingTheory.PowerSeries.Geometric
import all TauCeti.RingTheory.MvPolynomial.Symmetric.Complete.Elementary
import all PaperVerification.PowerCoinvariantComparator
import all PaperVerification.PowerCoinvariantStabilizer
import all PaperVerification.PowerCoinvariantAction
import all PaperVerification.PowerCoinvariantStandard
import all PaperVerification.PowerDegreePresentation
import all PaperVerification.PowerEquivariantSpecialization
import all PaperVerification.HomogeneousNullstellensatz
import all PaperVerification.AlternatingFormsFieldDescent
import all PaperVerification.PowerCompleteHomogeneousRegular
import all PaperVerification.HomogeneousKoszulMatrices
import all PaperVerification.HomogeneousKoszulRepresentation
import all PaperVerification.HomogeneousKoszulSpecialization
import all PaperVerification.PowerRegularComparator
import all PaperVerification.PowerEquivariantLowerBound
import all PaperVerification.PowerComparatorLength
import all TauCeti.RingTheory.SimpleModule.Isotypic
import all TauCeti.Algebra.Module.Submodule.Quotient
import all TauCeti.RingTheory.CompositionSeries.Basic
import all TauCeti.RingTheory.CompositionSeries.Multiplicity
import all TauCeti.RingTheory.CompositionSeries.Additivity
import all TauCeti.Algebra.Module.Equiv.Basic
import all TauCeti.RingTheory.Semisimple.Schur
import all TauCeti.RingTheory.Semisimple.RegularIsotypicComponent
import all TauCeti.RingTheory.Semisimple.Multiplicity
import all PaperVerification.SemisimpleHomComparison
import all TauCeti.Algebra.MonoidAlgebra.MapDomain
import all TauCeti.RepresentationTheory.Intertwining
import all TauCeti.RepresentationTheory.Subrepresentation
import all TauCeti.RepresentationTheory.FDRep.Basic
import all TauCeti.RepresentationTheory.AsModule
import all PaperVerification.RepresentationHomComparison
import all PaperVerification.GradedDimensionEquality
import all PaperVerification.PowerGradedRepresentation
import all PaperVerification.GradedRepresentationAssembly
import all PaperVerification.PowerRepresentationTheorem
import all PaperVerification.PowerOriginalRepresentation
import all PaperVerification.PowerOriginalDegreeEquiv
import all PaperVerification.EquivariantCokernelGenericSpecialization
import all PaperVerification.PowerUniversalSlope
import all TauCeti.Algebra.Module.GradedModule.HomogeneousPart
import all TauCeti.Algebra.Module.GradedModule.Polynomial
import all PaperVerification.GradedComponentBasis
import all PaperVerification.PowerHilbertSeries
import all PaperVerification.PowerSumComparator
import all PaperVerification.GradedHilbertTransport
import all PaperVerification.PowerOriginalHilbert
import all PaperVerification.PowerTheoremTwoTwo
import all PaperVerification.PowerTheoremOneOneSufficiency
import all PaperVerification.PowerOriginalArtinSpanning
import all PaperVerification.PowerCoinvariantStandardBridge
import all PaperVerification.PowerExceptionalArtin
import all PaperVerification.PowerTheoremOneOne
import all PaperVerification.EulerJacobian
import all PaperVerification.EulerParameters
import all PaperVerification.JacobianDivergence
import all PaperVerification.JacobianIsolatedOrigin
import all PaperVerification.Eigencomponents
import all PaperVerification.JacobianTorsion
import all PaperVerification.JacobianGrading
import all PaperVerification.JacobianMilnorReduction
import all PaperVerification.JacobianHamiltonian
import all PaperVerification.JacobianPolynomialModule
import all PaperVerification.NegativeWeightedGrading
import all PaperVerification.PolynomialBasisLifting
import all PaperVerification.GradedBasisLifting
import all PaperVerification.JacobianFreeness
import all PaperVerification.JacobianParameter
import all PaperVerification.HypersurfaceFreeness
import all PaperVerification.HomogeneousSection
import all PaperVerification.EulerReduction
import all PaperVerification.ProjectionQuotient
import all PaperVerification.EulerResonance
import all PaperVerification.JacobianDefect
import all PaperVerification.JacobianDegree
import all PaperVerification.HomogeneousQuotientBasis
import all PaperVerification.JacobianEquivariantSection
import all TauCeti.Algebra.MvPolynomial.PDeriv
import all TauCeti.RingTheory.MvPolynomial.LinearSubst
import all TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous
import all PaperVerification.JacobianLinearAction
import all PaperVerification.EquivariantTowers
import all TauCeti.Algebra.Module.GradedModule.DirectSum
import all TauCeti.Algebra.Module.GradedModule.Shift
import all PaperVerification.GradedTowers
import all PaperVerification.NegativeQuotientGrading
import all PaperVerification.JacobianEquivariantTowers
import all PaperVerification.JacobianHilbertBasis
import all PaperVerification.JacobianEquivariantDefect
import all PaperVerification.JacobianHilbertDefect
import all PaperVerification.JacobianHilbertFormula
import all PaperVerification.JacobianEquivariantFormula
import all PaperVerification.JacobianEquivariantExactSequence
import all PaperVerification.HypersurfaceTheoremSixThree
import all PaperVerification.HomogeneousFiniteParameters
import all PaperVerification.HomogeneousModuleFinite
import all TauCeti.RingTheory.Derivation.Ideal
import all TauCeti.RingTheory.Derivation.Localization
import all PaperVerification.DerivationFiniteConstants
import all PaperVerification.VectorJacobianKernel
import all PaperVerification.EulerInjective
import all PaperVerification.VectorEulerBasic
import all PaperVerification.VectorEulerGrading
import all PaperVerification.VectorEulerAction
import all PaperVerification.CompleteIntersectionCodimensionFull
/- END GENERATED LOCAL IMPORTS -/
import Lean
import all Lean.Util.CollectAxioms
-- These private proof bodies occur on the selected theorem dependency paths.
import all Mathlib.Algebra.Order.Antidiag.Pi

/-!
# Checked kernel audit of the principal theorem closure

The generated imports and ownership list are the local source dependency closure
of the principal coinvariant and Jacobian theorem modules, including the
vendored TauCeti modules. Local ownership is determined by imported module
indices and module declaration tables, not declaration namespace spelling.

Every selected local constant is read from the checked kernel environment. The
audit rejects local axioms and unapproved transitive axioms, requires the selected
paper endpoints to be actual theorem declarations with proof bodies, and rejects
unsafe or partial declarations on their traversable dependency paths. Imported
library bodies that are not exposed remain an explicit axiom-summary boundary.

Selected theorem types are exported as lossless expression DAGs. The JSON is
parsed, decoded and compared structurally with the checked type before the audit
can write .lake/reports/audit/kernel-dependencies.json. This checks the imported
environment and does not replace rebuilding the mathematical sources.
-/

set_option stderrAsMessages false

namespace DeformedCoinvariants.KernelAudit

namespace ExactType

open Lean

def formatVersion : String := "lean-expr-dag-v1"

def nameToJson : Name → Json
  | .anonymous => .arr #[.str "anonymous"]
  | .str p s => .arr #[.str "str", nameToJson p, .str s]
  | .num p n => .arr #[.str "num", nameToJson p, toJson n]

partial def nameFromJson (j : Json) : Except String Name := do
  match (← j.getArr?).toList with
  | [.str "anonymous"] => return .anonymous
  | [.str "str", p, s] => return .str (← nameFromJson p) (← s.getStr?)
  | [.str "num", p, n] => return .num (← nameFromJson p) (← n.getNat?)
  | _ => throw "Invalid exact Name constructor or arity"

def binderToJson : BinderInfo → Json
  | .default => .str "default"
  | .implicit => .str "implicit"
  | .strictImplicit => .str "strictImplicit"
  | .instImplicit => .str "instImplicit"

def binderFromJson : Json → Except String BinderInfo
  | .str "default" => .ok .default
  | .str "implicit" => .ok .implicit
  | .str "strictImplicit" => .ok .strictImplicit
  | .str "instImplicit" => .ok .instImplicit
  | _ => .error "Invalid BinderInfo constructor"

def literalToJson : Literal → Json
  | .natVal n => .arr #[.str "natVal", toJson n]
  | .strVal s => .arr #[.str "strVal", .str s]

def literalFromJson (j : Json) : Except String Literal := do
  match (← j.getArr?).toList with
  | [.str "natVal", n] => return .natVal (← n.getNat?)
  | [.str "strVal", s] => return .strVal (← s.getStr?)
  | _ => throw "Invalid Literal constructor or arity"

private structure EncodeState where
  exprMemo : ExprStructMap Nat := {}
  levelMemo : Std.HashMap Level Nat := {}
  expressions : Array Json := #[]
  levels : Array Json := #[]

private abbrev EncodeM := StateT EncodeState (Except String)

private partial def internLevel (u : Level) : EncodeM Nat := do
  if let some id := (← get).levelMemo[u]? then
    return id
  let row ← match u with
    | .zero => pure <| Json.arr #[.str "zero"]
    | .succ v => do
      let v ← internLevel v
      pure <| Json.arr #[.str "succ", toJson v]
    | .max v w => do
      let v ← internLevel v
      let w ← internLevel w
      pure <| Json.arr #[.str "max", toJson v, toJson w]
    | .imax v w => do
      let v ← internLevel v
      let w ← internLevel w
      pure <| Json.arr #[.str "imax", toJson v, toJson w]
    | .param n => pure <| Json.arr #[.str "param", nameToJson n]
    | .mvar _ => throw "Universe metavariable in a checked type export"
  let s ← get
  let id := s.levels.size
  set { s with levels := s.levels.push row, levelMemo := s.levelMemo.insert u id }
  return id

private partial def internExpr (e : Expr) : EncodeM Nat := do
  if let some id := (← get).exprMemo[ExprStructEq.mk e]? then
    return id
  let row ← match e with
    | .bvar i => pure <| Json.arr #[.str "bvar", toJson i]
    | .fvar _ => throw "Free variable in a checked type export"
    | .mvar _ => throw "Expression metavariable in a checked type export"
    | .sort u => do
      let u ← internLevel u
      pure <| Json.arr #[.str "sort", toJson u]
    | .const n us => do
      let us ← us.toArray.mapM internLevel
      pure <| Json.arr #[.str "const", nameToJson n, .arr (us.map toJson)]
    | .app f a => do
      let f ← internExpr f
      let a ← internExpr a
      pure <| Json.arr #[.str "app", toJson f, toJson a]
    | .lam n t b bi => do
      let t ← internExpr t
      let b ← internExpr b
      pure <| Json.arr #[.str "lam", nameToJson n, toJson t, toJson b, binderToJson bi]
    | .forallE n t b bi => do
      let t ← internExpr t
      let b ← internExpr b
      pure <| Json.arr #[.str "forallE", nameToJson n, toJson t, toJson b, binderToJson bi]
    | .letE n t v b nd => do
      let t ← internExpr t
      let v ← internExpr v
      let b ← internExpr b
      pure <| Json.arr #[.str "letE", nameToJson n, toJson t, toJson v, toJson b, .bool nd]
    | .lit l => pure <| Json.arr #[.str "lit", literalToJson l]
    | .mdata _ _ => throw "Metadata is forbidden in an exact checked-type DAG export"
    | .proj n i b => do
      let b ← internExpr b
      pure <| Json.arr #[.str "proj", nameToJson n, toJson i, toJson b]
  let s ← get
  let id := s.expressions.size
  set { s with expressions := s.expressions.push row, exprMemo := s.exprMemo.insert (ExprStructEq.mk e) id }
  return id

private def requireClosed (e : Expr) : Except String Unit := do
  if e.hasFVar then throw "A checked declaration type contains a free variable"
  if e.hasMVar then throw "A checked declaration type contains a metavariable"
  if e.hasLooseBVars then throw "A checked declaration type contains an unbound de Bruijn variable"

private def priorRef {α : Type} (values : Array α) (j : Json) : Except String (Nat × α) := do
  let id ← j.getNat?
  match values[id]? with
  | some value => return (id, value)
  | none => throw s!"DAG reference {id} is not strictly before node {values.size}"

private structure LevelNode where
  value : Level
  references : Array Nat := #[]

private def decodeLevelNode (prev : Array Level) (j : Json) : Except String LevelNode := do
  match (← j.getArr?).toList with
  | [.str "zero"] => return { value := .zero }
  | [.str "succ", u] =>
    let (i, u) ← priorRef prev u
    return { value := .succ u, references := #[i] }
  | [.str "max", u, v] =>
    let (i, u) ← priorRef prev u
    let (k, v) ← priorRef prev v
    return { value := .max u v, references := #[i, k] }
  | [.str "imax", u, v] =>
    let (i, u) ← priorRef prev u
    let (k, v) ← priorRef prev v
    return { value := .imax u v, references := #[i, k] }
  | [.str "param", n] => return { value := .param (← nameFromJson n) }
  | [.str "mvar", _] => throw "Universe metavariables are forbidden in a checked type DAG"
  | _ => throw "Invalid Level constructor or arity"

private structure ExprNode where
  value : Expr
  exprRefs : Array Nat := #[]
  levelRefs : Array Nat := #[]

private def decodeExprNode (prev : Array Expr) (levels : Array Level) (j : Json) :
    Except String ExprNode := do
  match (← j.getArr?).toList with
  | [.str "bvar", i] => return { value := .bvar (← i.getNat?) }
  | [.str "fvar", _] => throw "Free variables are forbidden in a checked type DAG"
  | [.str "mvar", _] => throw "Metavariables are forbidden in a checked type DAG"
  | [.str "sort", u] =>
    let (i, u) ← priorRef levels u
    return { value := .sort u, levelRefs := #[i] }
  | [.str "const", n, us] =>
    let us ← (← us.getArr?).mapM (priorRef levels)
    return { value := .const (← nameFromJson n) (us.toList.map Prod.snd), levelRefs := us.map Prod.fst }
  | [.str "app", f, a] =>
    let (i, f) ← priorRef prev f
    let (k, a) ← priorRef prev a
    return { value := .app f a, exprRefs := #[i, k] }
  | [.str "lam", n, t, b, bi] =>
    let (i, t) ← priorRef prev t
    let (k, b) ← priorRef prev b
    return { value := .lam (← nameFromJson n) t b (← binderFromJson bi), exprRefs := #[i, k] }
  | [.str "forallE", n, t, b, bi] =>
    let (i, t) ← priorRef prev t
    let (k, b) ← priorRef prev b
    return { value := .forallE (← nameFromJson n) t b (← binderFromJson bi), exprRefs := #[i, k] }
  | [.str "letE", n, t, v, b, nd] =>
    let (i, t) ← priorRef prev t
    let (k, v) ← priorRef prev v
    let (l, b) ← priorRef prev b
    return { value := .letE (← nameFromJson n) t v b (← nd.getBool?), exprRefs := #[i, k, l] }
  | [.str "lit", l] => return { value := .lit (← literalFromJson l) }
  | [.str "mdata", _, _] => throw "Metadata is forbidden in an exact checked-type DAG"
  | [.str "proj", n, i, b] =>
    let (k, b) ← priorRef prev b
    return { value := .proj (← nameFromJson n) (← i.getNat?) b, exprRefs := #[k] }
  | _ => throw "Invalid Expr constructor or arity"

structure DecodedType where
  declarationName : Name
  levelParameters : List Name
  type : Expr
  expressionNodes : Nat
  levelNodes : Nat

/-- Decode and validate a strictly postorder, closed, entirely reachable type DAG. -/
def decodeType (j : Json) : Except String DecodedType := do
  unless (← (← j.getObjVal? "format").getStr?) == formatVersion do
    throw "Unsupported type DAG format"
  let declarationName ← nameFromJson (← j.getObjVal? "declaration_name")
  let levelParameters ← (← (← j.getObjVal? "level_parameters").getArr?).toList.mapM nameFromJson
  let levelRows ← (← j.getObjVal? "levels").getArr?
  let exprRows ← (← j.getObjVal? "expressions").getArr?
  let mut levels : Array Level := #[]
  let mut usedLevels : Array Bool := Array.replicate levelRows.size false
  for row in levelRows do
    let node ← decodeLevelNode levels row
    for i in node.references do
      usedLevels := usedLevels.set! i true
    levels := levels.push node.value
  let mut expressions : Array Expr := #[]
  let mut usedExprs : Array Bool := Array.replicate exprRows.size false
  for row in exprRows do
    let node ← decodeExprNode expressions levels row
    for i in node.exprRefs do
      usedExprs := usedExprs.set! i true
    for i in node.levelRefs do
      usedLevels := usedLevels.set! i true
    expressions := expressions.push node.value
  let root ← (← j.getObjVal? "root").getNat?
  let some type := expressions[root]? | throw "Missing type DAG root"
  unless root + 1 == expressions.size do
    throw "A postorder type DAG must have its root last"
  -- Every non-root node must be referenced. With strictly backward references,
  -- this is equivalent to reachability from the unique last/root node.
  for i in [:usedExprs.size] do
    if i != root && !usedExprs[i]! then
      throw s!"Unreachable expression node {i}"
  -- Every level must lead, through strictly backward universe references,
  -- to a use in a reachable expression node.
  for i in [:usedLevels.size] do
    unless usedLevels[i]! do throw s!"Unreachable universe node {i}"
  requireClosed type
  return { declarationName, levelParameters, type, expressionNodes := expressions.size, levelNodes := levels.size }

/--
Export the actual checked type. `complete` is added only after JSON byte
serialization, reparsing, closed/postorder/reachability validation, and an exact
`Expr.equal` comparison. This is neither alpha-equivalence nor definitional equality.
-/
def encodeCheckedType (declName : Name) (levelParams : List Name) (type : Expr) :
    Except String Json := do
  requireClosed type
  let (root, state) ← (internExpr type).run {}
  let payload := Json.mkObj [
    ("format", .str formatVersion),
    ("declaration_name", nameToJson declName),
    ("level_parameters", .arr (levelParams.toArray.map nameToJson)),
    ("levels", .arr state.levels),
    ("expressions", .arr state.expressions),
    ("root", toJson root)]
  let serialized := payload.compress
  let parsed ← Json.parse serialized
  let decoded ← decodeType parsed
  unless decoded.declarationName == declName do
    throw "Exact declaration Name round-trip failed"
  unless decoded.levelParameters == levelParams do
    throw "Exact universe-parameter Name/order round-trip failed"
  unless Expr.equal decoded.type type do
    throw "Exact structural Expr round-trip failed"
  return Json.mkObj [
    ("format", .str formatVersion),
    ("complete", .bool true),
    ("roundtrip_check", .str "Json.compress -> Json.parse -> decodeType -> Expr.equal"),
    ("expression_nodes", toJson state.expressions.size),
    ("level_nodes", toJson state.levels.size),
    ("metadata_nodes", toJson (0 : Nat)),
    ("metadata_policy", .str "reject-all"),
    ("serialized_payload_bytes", toJson serialized.toUTF8.size),
    ("payload", parsed)]

end ExactType


set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8192 in
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  if (← getOptions).getBool "debug.skipKernelTC".toName false then
    throwError "The kernel audit requires debug.skipKernelTC=false"
  let outputDirectory : System.FilePath := ".lake/reports/audit"
  let outputPath := outputDirectory / "kernel-dependencies.json"
  -- A failed audit must not leave a previous success at its output path.
  if ← liftIO outputPath.pathExists then
    liftIO <| IO.FS.removeFile outputPath
  -- BEGIN GENERATED OWNED MODULES
  let projectModules : Array Name := #[
    `PaperVerification.PowerOperators,
    `PaperVerification.FermionMomentRecurrence,
    `PaperVerification.PowerRecurrence,
    `PaperVerification.PowerParameters,
    `PaperVerification.PowerFullSupport,
    `PaperVerification.PowerBoundary,
    `PaperVerification.PowerArtin,
    `PaperVerification.PowerSpanning,
    `PaperVerification.PowerConjugation,
    `PaperVerification.PowerCoordinateRestriction,
    `TauCeti.RingTheory.RootsOfUnity.Basic,
    `TauCeti.RingTheory.MvPolynomial.Homogeneous,
    `PaperVerification.PowerHomogeneity,
    `TauCeti.Algebra.Homology.HomologicalComplex.Basic,
    `TauCeti.Algebra.Homology.Homotopy,
    `TauCeti.Algebra.Homology.Linear,
    `TauCeti.LinearAlgebra.CliffordAlgebra.Grading,
    `TauCeti.LinearAlgebra.CliffordAlgebra.Contraction,
    `TauCeti.LinearAlgebra.ExteriorPower.Basic,
    `TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction,
    `TauCeti.RingTheory.KoszulComplex.Basic,
    `TauCeti.RingTheory.KoszulComplex.Regular,
    `PaperVerification.KoszulSyzygies,
    `PaperVerification.PowerComplex,
    `PaperVerification.PowerDegreeSpaces,
    `PaperVerification.PowerCoefficientMap,
    `PaperVerification.FermionSupport,
    `PaperVerification.FermionRadical,
    `PaperVerification.HomogeneousLocalization,
    `TauCeti.RingTheory.Ideal.Colon,
    `TauCeti.RingTheory.Ideal.AssociatedPrime.Basic,
    `TauCeti.RingTheory.Ideal.AssociatedPrime.Localization,
    `TauCeti.Topology.KrullDimension.Basic,
    `TauCeti.Topology.KrullDimension.Local,
    `TauCeti.Topology.PureDimension,
    `TauCeti.Order.Catenary,
    `TauCeti.RingTheory.Catenary,
    `TauCeti.Topology.KrullDimension.Irreducible,
    `TauCeti.Topology.KrullDimension.ClosedCover,
    `TauCeti.RingTheory.KrullDimension.Quotient,
    `TauCeti.Algebra.Ring.Subgroup,
    `TauCeti.RingTheory.Ideal.Operations,
    `TauCeti.Algebra.Module.Projective.LinearMap,
    `TauCeti.RingTheory.Regular.LinearMap,
    `TauCeti.Algebra.Category.ModuleCat.Ext.Basic,
    `TauCeti.Data.ENat.Basic,
    `TauCeti.RingTheory.Localization.Module,
    `TauCeti.RingTheory.Depth.Basic,
    `TauCeti.RingTheory.Localization.Annihilator,
    `TauCeti.RingTheory.KrullDimension.Module,
    `TauCeti.RingTheory.CohenMacaulay.Basic,
    `TauCeti.RingTheory.KrullDimension.Regular,
    `TauCeti.Data.ENat.Monoid,
    `TauCeti.RingTheory.LocalRing.MaximalIdeal.Generator,
    `TauCeti.RingTheory.Ideal.Quotient.Colon,
    `TauCeti.RingTheory.CohenMacaulay.Normal,
    `TauCeti.RingTheory.IntegralClosure.GoingDown,
    `TauCeti.RingTheory.KrullDimension.Fiber,
    `TauCeti.RingTheory.LocalRing.Quotient,
    `TauCeti.RingTheory.CohenMacaulay.RegularSequence,
    `TauCeti.LinearAlgebra.Span.Basic,
    `TauCeti.RingTheory.LocalRing.MaximalIdeal.Square,
    `TauCeti.RingTheory.RegularLocalRing.Basic,
    `TauCeti.Algebra.Module.SpanRank,
    `TauCeti.LinearAlgebra.Matrix.Adjugate.Basic,
    `TauCeti.RingTheory.Spectrum.Prime.Point,
    `TauCeti.RingTheory.Finiteness.Nakayama,
    `TauCeti.RingTheory.Regular.RegularSequence,
    `TauCeti.RingTheory.Depth.WeaklyRegular,
    `TauCeti.RingTheory.CohenMacaulay.Height,
    `TauCeti.RingTheory.RegularLocalRing.CohenMacaulay,
    `TauCeti.RingTheory.KrullDimension.Integral,
    `TauCeti.RingTheory.KrullDimension.Basic,
    `TauCeti.RingTheory.KrullDimension.FiniteType,
    `TauCeti.RingTheory.KrullDimension.Polynomial,
    `PaperVerification.HomogeneousRegularSequence,
    `PaperVerification.FermionOrdinaryParameters,
    `PaperVerification.PowerGenericParameters,
    `TauCeti.LinearAlgebra.Matrix.Rank,
    `PaperVerification.MatrixRank,
    `PaperVerification.RankSpecialization,
    `TauCeti.RingTheory.MvPolynomial.RestrictSupport,
    `PaperVerification.PowerDegreeMatrices,
    `PaperVerification.PowerDegreeQuotient,
    `PaperVerification.PowerStabilizerCharacteristic,
    `PaperVerification.PowerGroupedParameters,
    `PaperVerification.QuotientLinearAction,
    `PaperVerification.PowerPermutationAction,
    `PaperVerification.EquivariantHomExact,
    `PaperVerification.ProjectedRankSpecialization,
    `PaperVerification.EquivariantHomMatrices,
    `PaperVerification.EquivariantHomSpecialization,
    `PaperVerification.EquivariantHomRank,
    `PaperVerification.EquivariantCokernelSpecialization,
    `PaperVerification.PowerDegreeActions,
    `PaperVerification.PowerOriginalDegreeMatrices,
    `PaperVerification.PowerArtinBasis,
    `TauCeti.Algebra.DirectSum.Internal,
    `TauCeti.LinearAlgebra.Graded.LinearMap,
    `TauCeti.Order.CompactlyGenerated,
    `TauCeti.Algebra.Module.Submodule.Finite,
    `TauCeti.Algebra.Module.GradedModule.Internal,
    `TauCeti.Algebra.Module.GradedModule.Quotient,
    `PaperVerification.FermionGradedHilbert,
    `PaperVerification.FermionFiniteGrading,
    `PaperVerification.GradedDimensionComparison,
    `PaperVerification.HilbertTowerCount,
    `PaperVerification.FermionPolynomialHilbert,
    `PaperVerification.FermionIdealHilbert,
    `PaperVerification.FermionCompleteIntersectionLength,
    `PaperVerification.FermionOrdinaryLength,
    `PaperVerification.PowerBasisTheorem,
    `PaperVerification.PowerOriginalBasis,
    `PaperVerification.PowerOriginalAction,
    `PaperVerification.PowerOriginalDegreePresentation,
    `PaperVerification.PowerHarmonicWitness,
    `PaperVerification.PowerFischerPairing,
    `PaperVerification.PowerHarmonicQuotient,
    `PaperVerification.PowerStandardHarmonics,
    `PaperVerification.PowerStandardDual,
    `PaperVerification.EquivariantSection,
    `PaperVerification.SelfDualSubrepresentation,
    `PaperVerification.PowerResonantStandard,
    `TauCeti.RingTheory.MvPolynomial.Symmetric.Homogeneous,
    `TauCeti.Data.Sym.Basic,
    `TauCeti.RingTheory.MvPolynomial.Symmetric.Complete.Basic,
    `TauCeti.RingTheory.PowerSeries.Rescale,
    `TauCeti.RingTheory.MvPolynomial.Symmetric.Elementary,
    `TauCeti.Algebra.BigOperators.Finset.Range,
    `TauCeti.RingTheory.PowerSeries.Geometric,
    `TauCeti.RingTheory.MvPolynomial.Symmetric.Complete.Elementary,
    `PaperVerification.PowerCoinvariantComparator,
    `PaperVerification.PowerCoinvariantStabilizer,
    `PaperVerification.PowerCoinvariantAction,
    `PaperVerification.PowerCoinvariantStandard,
    `PaperVerification.PowerDegreePresentation,
    `PaperVerification.PowerEquivariantSpecialization,
    `PaperVerification.HomogeneousNullstellensatz,
    `PaperVerification.AlternatingFormsFieldDescent,
    `PaperVerification.PowerCompleteHomogeneousRegular,
    `PaperVerification.HomogeneousKoszulMatrices,
    `PaperVerification.HomogeneousKoszulRepresentation,
    `PaperVerification.HomogeneousKoszulSpecialization,
    `PaperVerification.PowerRegularComparator,
    `PaperVerification.PowerEquivariantLowerBound,
    `PaperVerification.PowerComparatorLength,
    `TauCeti.RingTheory.SimpleModule.Isotypic,
    `TauCeti.Algebra.Module.Submodule.Quotient,
    `TauCeti.RingTheory.CompositionSeries.Basic,
    `TauCeti.RingTheory.CompositionSeries.Multiplicity,
    `TauCeti.RingTheory.CompositionSeries.Additivity,
    `TauCeti.Algebra.Module.Equiv.Basic,
    `TauCeti.RingTheory.Semisimple.Schur,
    `TauCeti.RingTheory.Semisimple.RegularIsotypicComponent,
    `TauCeti.RingTheory.Semisimple.Multiplicity,
    `PaperVerification.SemisimpleHomComparison,
    `TauCeti.Algebra.MonoidAlgebra.MapDomain,
    `TauCeti.RepresentationTheory.Intertwining,
    `TauCeti.RepresentationTheory.Subrepresentation,
    `TauCeti.RepresentationTheory.FDRep.Basic,
    `TauCeti.RepresentationTheory.AsModule,
    `PaperVerification.RepresentationHomComparison,
    `PaperVerification.GradedDimensionEquality,
    `PaperVerification.PowerGradedRepresentation,
    `PaperVerification.GradedRepresentationAssembly,
    `PaperVerification.PowerRepresentationTheorem,
    `PaperVerification.PowerOriginalRepresentation,
    `PaperVerification.PowerOriginalDegreeEquiv,
    `PaperVerification.EquivariantCokernelGenericSpecialization,
    `PaperVerification.PowerUniversalSlope,
    `TauCeti.Algebra.Module.GradedModule.HomogeneousPart,
    `TauCeti.Algebra.Module.GradedModule.Polynomial,
    `PaperVerification.GradedComponentBasis,
    `PaperVerification.PowerHilbertSeries,
    `PaperVerification.PowerSumComparator,
    `PaperVerification.GradedHilbertTransport,
    `PaperVerification.PowerOriginalHilbert,
    `PaperVerification.PowerTheoremTwoTwo,
    `PaperVerification.PowerTheoremOneOneSufficiency,
    `PaperVerification.PowerOriginalArtinSpanning,
    `PaperVerification.PowerCoinvariantStandardBridge,
    `PaperVerification.PowerExceptionalArtin,
    `PaperVerification.PowerTheoremOneOne,
    `PaperVerification.EulerJacobian,
    `PaperVerification.EulerParameters,
    `PaperVerification.JacobianDivergence,
    `PaperVerification.JacobianIsolatedOrigin,
    `PaperVerification.Eigencomponents,
    `PaperVerification.JacobianTorsion,
    `PaperVerification.JacobianGrading,
    `PaperVerification.JacobianMilnorReduction,
    `PaperVerification.JacobianHamiltonian,
    `PaperVerification.JacobianPolynomialModule,
    `PaperVerification.NegativeWeightedGrading,
    `PaperVerification.PolynomialBasisLifting,
    `PaperVerification.GradedBasisLifting,
    `PaperVerification.JacobianFreeness,
    `PaperVerification.JacobianParameter,
    `PaperVerification.HypersurfaceFreeness,
    `PaperVerification.HomogeneousSection,
    `PaperVerification.EulerReduction,
    `PaperVerification.ProjectionQuotient,
    `PaperVerification.EulerResonance,
    `PaperVerification.JacobianDefect,
    `PaperVerification.JacobianDegree,
    `PaperVerification.HomogeneousQuotientBasis,
    `PaperVerification.JacobianEquivariantSection,
    `TauCeti.Algebra.MvPolynomial.PDeriv,
    `TauCeti.RingTheory.MvPolynomial.LinearSubst,
    `TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous,
    `PaperVerification.JacobianLinearAction,
    `PaperVerification.EquivariantTowers,
    `TauCeti.Algebra.Module.GradedModule.DirectSum,
    `TauCeti.Algebra.Module.GradedModule.Shift,
    `PaperVerification.GradedTowers,
    `PaperVerification.NegativeQuotientGrading,
    `PaperVerification.JacobianEquivariantTowers,
    `PaperVerification.JacobianHilbertBasis,
    `PaperVerification.JacobianEquivariantDefect,
    `PaperVerification.JacobianHilbertDefect,
    `PaperVerification.JacobianHilbertFormula,
    `PaperVerification.JacobianEquivariantFormula,
    `PaperVerification.JacobianEquivariantExactSequence,
    `PaperVerification.HypersurfaceTheoremSixThree,
    `PaperVerification.HomogeneousFiniteParameters,
    `PaperVerification.HomogeneousModuleFinite,
    `TauCeti.RingTheory.Derivation.Ideal,
    `TauCeti.RingTheory.Derivation.Localization,
    `PaperVerification.DerivationFiniteConstants,
    `PaperVerification.VectorJacobianKernel,
    `PaperVerification.EulerInjective,
    `PaperVerification.VectorEulerBasic,
    `PaperVerification.VectorEulerGrading,
    `PaperVerification.VectorEulerAction,
    `PaperVerification.CompleteIntersectionCodimensionFull]
  -- END GENERATED OWNED MODULES
  -- BEGIN SELECTED THEOREM ROOTS
  let roots : Array (String × Name × Name) := #[
    ("Theorem 1.1", `PaperVerification.PowerOperators.paper_theorem_1_1, `PaperVerification.PowerTheoremOneOne),
    ("Theorem 2.2", `PaperVerification.PowerOperators.paper_theorem_2_2, `PaperVerification.PowerTheoremTwoTwo),
    ("Theorem 6.2", `PaperVerification.EulerJacobian.paper_theorem_6_2, `PaperVerification.EulerParameters),
    ("Theorem 6.3: scalar clauses", `PaperVerification.JacobianDivergence.paper_theorem_6_3_scalar, `PaperVerification.HypersurfaceTheoremSixThree),
    ("Theorem 6.3: arbitrary homogeneous basis lifts", `PaperVerification.JacobianDivergence.paper_theorem_6_3_basis_lifts, `PaperVerification.HypersurfaceTheoremSixThree),
    ("Theorem 6.3: equivariance", `PaperVerification.JacobianDivergence.paper_theorem_6_3_equivariant, `PaperVerification.HypersurfaceTheoremSixThree),
    ("Proposition 6.5: scalar clauses", `PaperVerification.VectorEuler.paper_proposition_6_5_scalar, `PaperVerification.CompleteIntersectionCodimensionFull),
    ("Proposition 6.5: equivariance", `PaperVerification.VectorEuler.paper_proposition_6_5_equivariant, `PaperVerification.CompleteIntersectionCodimensionFull)]
  -- END SELECTED THEOREM ROOTS
  let allowed : Array Name := #["propext".toName, "Classical.choice".toName,
    "Quot.sound".toName]
  let moduleNames := env.header.moduleNames
  let selectedModules : NameSet :=
    projectModules.foldl (fun names name => names.insert name) {}
  unless selectedModules.size == projectModules.size do
    throwError "Duplicate module in the generated ownership list"
  let moduleOf := fun name =>
    match env.getModuleIdxFor? name with
    | some i => moduleNames[i.toNat]!
    | none => env.mainModule
  -- A changed mathematical import graph must regenerate the explicit list.
  for moduleName in moduleNames do
    let localPrefix := moduleName.toString.startsWith "PaperVerification." ||
      moduleName.toString.startsWith "TauCeti."
    if localPrefix && !selectedModules.contains moduleName then
      throwError "Local import absent from generated audit closure: {moduleName}"
  for moduleName in projectModules do
    unless moduleNames.contains moduleName do
      throwError "Expected local module was not imported: {moduleName}"
  let checked := env.checked.get
  let mut constants : Array (Name × ConstantInfo) := #[]
  let mut declaredIn : NameMap (Array Name) := {}
  let mut loadedProjectModules : Array Name := #[]
  for i in [:moduleNames.size] do
    let moduleName := moduleNames[i]!
    if selectedModules.contains moduleName then
      unless env.header.modules[i]!.importAll do
        throwError "Local module requires import all to expose its kernel bodies: {moduleName}"
      loadedProjectModules := loadedProjectModules.push moduleName
      let moduleData := env.header.moduleData[i]!
      unless moduleData.constNames.size == moduleData.constants.size do
        throwError "Inconsistent imported constant arrays in {moduleName}"
      for name in moduleData.constNames, stored in moduleData.constants do
        let some ci := checked.find? name |
          throwError "Local declaration absent from checked environment: {name}"
        -- Compatible duplicate entries may occur in generated equation lemmas.
        -- Accept them only when their complete ConstantInfo agrees.
        unless ci == stored do
          throwError "Imported local body differs from resolved checked body: {name} in {moduleName}"
        let entries := (declaredIn.find? name).getD #[]
        declaredIn := declaredIn.insert name (entries.push moduleName)
        if entries.isEmpty then
          constants := constants.push (name, ci)
  if constants.isEmpty then
    throwError "No local declarations were selected for the kernel audit"
  unless loadedProjectModules.size == projectModules.size do
    throwError "The audit did not load every selected local module"
  constants := constants.qsort (fun a b => Name.lt a.1 b.1)
  let projectInfo : NameMap ConstantInfo :=
    constants.foldl (fun result pair => result.insert pair.1 pair.2) {}
  let isProject := fun name => projectInfo.contains name
  let kindOf := fun ci : ConstantInfo => match ci with
    | .axiomInfo _ => "axiom"
    | .thmInfo _ => "theorem"
    | .defnInfo _ => "definition"
    | .opaqueInfo _ => "opaque"
    | .quotInfo _ => "quotient"
    | .ctorInfo _ => "constructor"
    | .recInfo _ => "recursor"
    | .inductInfo _ => "inductive"
  liftIO <| IO.eprintln
    s!"KERNEL_AUDIT_PHASE: {constants.size} checked declarations; {projectModules.size} local modules"
  -- Recompute local axiom dependencies from checked types and values. At the
  -- external-library boundary, use Lean's exported axiom summaries; this is
  -- necessary when an imported library theorem deliberately hides its body.
  let axiomState := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  let findExternalAxioms := fun (e : Environment) (name : Name) =>
    if isProject name then none else axiomState.find? e name
  let localAxiomLists := CollectAxioms.runM env do
    constants.mapM fun (name, _) =>
      CollectAxioms.collectAndGet findExternalAxioms name
  let mut nodes : Array Json := #[]
  let mut leaves : NameSet := {}
  let mut localTheorems : Nat := 0
  for (name, ci) in constants, axioms in localAxiomLists do
    if ci.isAxiom then
      throwError "Local axiom is forbidden: {name}"
    if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars then
      throwError "Local declaration has an open checked type: {name}"
    if let some value := ci.value? (allowOpaque := true) then
      if value.hasMVar || value.hasFVar || value.hasLooseBVars then
        throwError "Local declaration has an open checked body: {name}"
    if let .thmInfo _ := ci then
      localTheorems := localTheorems + 1
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unapproved transitive axiom {ax} in local declaration {name}"
    let dependencies := ci.getUsedConstantsAsSet.toArray.qsort Name.lt
    if dependencies.contains "sorryAx".toName then
      throwError "Local declaration contains sorryAx: {name}"
    for dependency in dependencies do
      unless isProject dependency do
        leaves := leaves.insert dependency
      unless (checked.find? dependency).isSome ||
          (axiomState.find? env dependency).isSome do
        throwError "Dependency has neither checked information nor an imported axiom summary: {dependency}"
    let ranges ← findDeclarationRangesCore? name
    nodes := nodes.push <| Json.mkObj [
      ("name", toJson name.toString),
      ("indexed_module", toJson (moduleOf name).toString),
      ("declared_in_modules", toJson (((declaredIn.find? name).getD #[]).map Name.toString)),
      ("source_start_line", toJson (ranges.map (fun r => r.range.pos.line))),
      ("source_end_line", toJson (ranges.map (fun r => r.range.endPos.line))),
      ("declaration_kind", toJson (kindOf ci)),
      ("body_available", toJson (ci.hasValue (allowOpaque := true))),
      ("is_unsafe", toJson ci.isUnsafe),
      ("is_partial", toJson ci.isPartial),
      ("axioms", toJson (axioms.qsort Name.lt |>.map Name.toString)),
      ("dependencies", toJson (dependencies.map Name.toString))]
  if localTheorems == 0 then
    throwError "No local theorems were checked"
  let mut rootInfo : Array Json := #[]
  for (paperResult, name, expectedModule) in roots do
    let some ci := projectInfo.find? name |
      throwError "Selected theorem is absent from the checked local declarations: {name}"
    unless ((declaredIn.find? name).getD #[]).contains expectedModule do
      throwError "Selected theorem is not declared in its expected module: {name} in {expectedModule}"
    -- In particular, an opaque statement or an imported axiom-shaped stub
    -- cannot satisfy the requirement for a principal mathematical theorem.
    let proof ← match ci with
      | .thmInfo value => pure value.value
      | _ => throwError "Selected endpoint is not an actual checked theorem with a proof: {name}"
    if proof.hasMVar || proof.hasFVar || proof.hasLooseBVars then
      throwError "Selected theorem has an open proof: {name}"
    let axioms := CollectAxioms.runM env <|
      CollectAxioms.collectAndGet findExternalAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unapproved transitive axiom {ax} in selected theorem {name}"
    let ty ← liftTermElabM <| PrettyPrinter.ppExpr ci.type
    let exactType ← match ExactType.encodeCheckedType ci.name ci.levelParams ci.type with
      | .ok data => pure data
      | .error message => throwError "Lossless checked-type export failed for {name}: {message}"
    rootInfo := rootInfo.push <| Json.mkObj [
      ("paper_result", toJson paperResult),
      ("name", toJson name.toString),
      ("module", toJson (moduleOf name).toString),
      ("declaration_kind", toJson "theorem"),
      ("proof_body_present", toJson true),
      ("type_readable", toJson ty.pretty),
      ("type_kernel", exactType),
      ("universe_parameters", toJson (ci.levelParams.map Name.toString)),
      ("axioms", toJson (axioms.qsort Name.lt |>.map Name.toString))]
    liftIO <| IO.eprintln s!"KERNEL_AUDIT_PHASE: checked theorem and exact type: {name}"
  -- Traverse actual checked types and available values, including available
  -- imported-library bodies. Hidden external bodies are recorded as summary
  -- boundaries, not described as traversed or independently rechecked here.
  let mut pending := roots.map (fun (_, name, _) => name)
  let mut reachable : NameSet := {}
  let mut externalNodes : Array Json := #[]
  let mut summaryBoundaries : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless reachable.contains name do
      reachable := reachable.insert name
      if name == "sorryAx".toName then
        throwError "Selected theorem dependency path reaches sorryAx"
      match checked.find? name with
      | none =>
        let some axioms := axiomState.find? env name |
          throwError "Selected dependency has no checked information or axiom summary: {name}"
        if isProject name then
          throwError "Local dependency has no checked body: {name}"
        for ax in axioms do
          unless allowed.contains ax do
            throwError "Unapproved boundary axiom {ax} in selected dependency {name}"
        summaryBoundaries := summaryBoundaries.insert name
        externalNodes := externalNodes.push <| Json.mkObj [
          ("name", toJson name.toString),
          ("module", toJson (moduleOf name).toString),
          ("body_available", toJson false),
          ("inspection", toJson "exported axiom summary only")]
      | some ci =>
        if ci.isUnsafe || ci.isPartial then
          throwError "Unsafe or partial declaration on a selected kernel dependency path: {name}"
        let dependencies := ci.getUsedConstantsAsSet.toArray.qsort Name.lt
        for dependency in dependencies do
          pending := pending.push dependency
        if ci.isAxiom && !allowed.contains name then
          unless (axiomState.find? env name).isSome do
            throwError "Opaque imported boundary lacks an exported axiom summary: {name}"
          summaryBoundaries := summaryBoundaries.insert name
        unless isProject name do
          externalNodes := externalNodes.push <| Json.mkObj [
            ("name", toJson name.toString),
            ("module", toJson (moduleOf name).toString),
            ("declaration_kind", toJson (kindOf ci)),
            ("body_available", toJson (ci.hasValue (allowOpaque := true))),
            ("is_unsafe", toJson ci.isUnsafe),
            ("is_partial", toJson ci.isPartial),
            ("dependencies", toJson (dependencies.map Name.toString))]
  let mut leafInfo : Array Json := #[]
  for name in (leaves ++ summaryBoundaries).toArray.qsort Name.lt do
    unless (checked.find? name).isSome || (axiomState.find? env name).isSome do
      throwError "Imported boundary dependency is unavailable: {name}"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unapproved transitive axiom {ax} in imported boundary dependency {name}"
    leafInfo := leafInfo.push <| Json.mkObj [
      ("name", toJson name.toString),
      ("module", toJson (moduleOf name).toString),
      ("axioms", toJson (axioms.qsort Name.lt |>.map Name.toString)),
      ("on_selected_dependency_path", toJson (reachable.contains name)),
      ("hidden_body_boundary", toJson (summaryBoundaries.contains name))]
  let runtimeOnly := constants.filterMap fun (name, ci) =>
    if ci.isUnsafe || ci.isPartial then some <| Json.mkObj [
      ("name", toJson name.toString),
      ("is_unsafe", toJson ci.isUnsafe),
      ("is_partial", toJson ci.isPartial),
      ("reachable_from_selected_theorems", toJson (reachable.contains name))]
    else none
  let graph := Json.mkObj [
    ("format", toJson "deformed-coinvariants-kernel-audit-v1"),
    ("lean_version", toJson Lean.versionString),
    ("audit_module", toJson env.mainModule.toString),
    ("kernel_checking_enabled_for_audit", toJson true),
    ("allowed_axioms", toJson (allowed.map Name.toString)),
    ("local_axiom_analysis", toJson
      "Traversed checked local types and bodies; used Lean exported axiom summaries at external-library boundaries."),
    ("dependency_path_analysis", toJson
      "Rejected unsafe and partial constants on selected paths through checked types and available values; recorded hidden imported bodies as summary boundaries."),
    ("type_export_format", toJson ExactType.formatVersion),
    ("project_modules", toJson (projectModules.qsort Name.lt |>.map Name.toString)),
    ("project_declaration_count", toJson constants.size),
    ("project_theorem_count", toJson localTheorems),
    ("selected_dependency_count", toJson reachable.size),
    ("roots", Json.arr rootInfo),
    ("local_declarations", Json.arr nodes),
    ("unreachable_local_runtime_implementations", Json.arr runtimeOnly),
    ("reachable_external_declarations", Json.arr
      (externalNodes.qsort (fun a b => a.compress < b.compress))),
    ("imported_boundary_dependencies", Json.arr leafInfo),
    ("hidden_body_boundaries", toJson
      (summaryBoundaries.toArray.qsort Name.lt |>.map Name.toString))]
  liftIO <| IO.FS.createDirAll outputDirectory
  let temporaryPath := outputDirectory / "kernel-dependencies.json.tmp"
  liftIO <| IO.FS.writeFile temporaryPath (graph.pretty ++ "\n")
  liftIO <| IO.FS.rename temporaryPath outputPath
  logInfo m!"KERNEL_AUDIT_OK {constants.size} local declarations; {localTheorems} theorems; {roots.size} roots; {projectModules.size} local modules; {reachable.size} inspected dependency nodes"

end DeformedCoinvariants.KernelAudit

