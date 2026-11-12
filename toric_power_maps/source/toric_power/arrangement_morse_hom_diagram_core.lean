module

public import ToricPower.ArrangementMorseStandardComplexAssembly
public import ToricPower.ArrangementMorseHomFamilies
public import Lean

/-! # Affine Morse assembly for the original intrinsic Hom diagram

All changes of equal scalar and additive presentations are checked with
an abstract label functor. Geometric labels are substituted only after
this comparison; the conclusion still names the original Hom diagram.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 200000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local instance 2000] Abelian.toPreadditive
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

namespace ToricPower.IntegralArrangement

variable {X : Scheme.{0}} {I : Type*}
  (opens : I → X.Opens) [∀ i, IsAffineHom (opens i).ι]
  {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (c : UniversalIncidenceObject A) (region : Set (Fin n → ℝ))
  [Linear ℂ (QCoh X)]
  (P : (UniversalIncidenceObject A)ᵒᵖ ⥤ QCoh X)
  [canonicalAdditive : (Cellular.complexHomDiagram P).Additive]

open Lean Elab Tactic Meta in
theorem universalLocalMorse_affineCoresolution_acyclic_homDiagram_core
    (localModels : ∀ i : I, QCoh (opens i).toScheme ⥤
      UniversalIncidenceObject A ⥤ ModuleCat ℂ)
    (comparison : ∀ i : I, localModels i ≅
      quasicoherentAffinePushforward (opens i).ι ⋙ Cellular.complexHomDiagram P)
    (localVanishing : ∀ (i : I) (M : QCoh (opens i).toScheme),
      ((universalLocalMorse A ℂ c region).obj
        ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat ℂ) 0).obj
          ((localModels i).obj M))).Acyclic)
    (l : List I) (K : CochainComplex (QCoh X) ℤ) :
    ((universalLocalMorse A ℂ c region).obj
      (((Cellular.homDiagram ℂ P).mapHomologicalComplex (.up ℤ)).obj
        ((affineConeCoresolution opens l).obj K))).Acyclic := by
  -- Build only the ordinary application of the two checked theorems.
  -- Each argument and both propositions must already have identical
  -- elaborated types. The resulting proof is still checked by the kernel.
  run_tac do
    let get (stx : TSyntax `term) := Term.elabTerm stx none >>= instantiateMVars
    let mut vanishing ← get (← `(universalLocalMorse_affineCoresolution_acyclic_standardComplex
      opens A c region))
    let localExpr (name : Name) : TacticM Expr := do
      for declaration in (← getLCtx) do
        if declaration.userName.eraseMacroScopes == name then return declaration.toExpr
      throwError "Missing local parameter {name}"
    let inputs : Array Expr := #[
      ← get (← `(Cellular.complexHomDiagram P)), ← get (← `(canonicalAdditive)),
      ← localExpr `localModels, ← localExpr `comparison, ← localExpr `localVanishing,
      ← localExpr `l, ← localExpr `K]
    for j in [0:inputs.size] do
      let argument := inputs[j]!
      let .forallE _ expected _ _ ← whnf (← inferType vanishing) |
        throwError "Expected a function at argument {j}"
      let actual ← instantiateMVars (← inferType argument)
      let expected ← instantiateMVars expected
      unless actual == expected do
        throwError "Non-identical argument type at {j}:\n{actual}\n{expected}"
      vanishing := mkApp vanishing argument
    let listSyntax ← Term.exprToSyntax (← localExpr `l)
    let complexSyntax ← Term.exprToSyntax (← localExpr `K)
    let transport ← get (← `(universalLocalMorse_complexHom_acyclic_iff A c region P
      (canonicalAdditive := canonicalAdditive)
      ((affineConeCoresolution opens $listSyntax).obj $complexSyntax)))
    let transportType ← instantiateMVars (← inferType transport)
    unless transportType.isAppOfArity ``Iff 2 do throwError "Expected a proved equivalence"
    let lhs := transportType.getAppArgs[0]!
    let rhs := transportType.getAppArgs[1]!
    let actual ← instantiateMVars (← inferType vanishing)
    unless actual == lhs do throwError "The proved input proposition has changed"
    let goal ← getMainGoal
    let target ← instantiateMVars (← goal.getType)
    unless rhs == target do
      let rc := rhs.getUsedConstants
      let tc := target.getUsedConstants
      throwError "Output presentation mismatch: rhs-only {rc.filter fun n => !tc.contains n}; target-only {tc.filter fun n => !rc.contains n}"
    let proof := mkAppN (mkConst ``Iff.mp) #[lhs, rhs, transport, vanishing]
    if proof.hasMVar || proof.getUsedConstants.contains ``sorryAx then
      throwError "An incomplete proof term is forbidden"
    goal.assign proof


end ToricPower.IntegralArrangement
end
