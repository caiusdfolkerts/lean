module

public import paper_verification.symmetric_basis_degree2
import all paper_verification.symmetric_basis_degree2
public import paper_verification.actual_odd_affine_paving6
import all paper_verification.actual_odd_affine_paving6
public import paper_verification.relative_projective_geometry2
import all paper_verification.relative_projective_geometry2
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

section ComponentSource_0
/- Original module: PaperVerification.SymmetricFreeProjectiveIso -/


/-!
# Free symmetric projective spectra are ordinary projective spaces

A basis gives the actual polynomial equivalence in every homogeneous degree.
The induced `Proj` isomorphism and its inverse preserve the original scalar
structure. No twisting sheaf, Chow group or cohomology comparison is required.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.SymmetricFreeProjectiveIso

open AlgebraicGeometry CategoryTheory Module
open OAI.AlgebraicGeometry.Divisors.LineBundles

variable {R M I : Type} [CommRing R] [AddCommGroup M] [Module R M]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual graded map determined by the chosen basis. -/
def toPolynomial (b : Basis I R M) :
    Symmetric.Grading.BundleCycles.symmetricGrading R M →+*ᵍ
      MvPolynomial.homogeneousSubmodule I R where
  __ := (SymmetricAlgebra.equivMvPolynomial b).toRingHom
  map_mem {n} {x} hx :=
    (SymmetricAlgebra.equivMvPolynomial_isHomogeneous_iff R M b n x).mpr hx

/-- Its inverse preserves the same homogeneous degree. -/
def fromPolynomial (b : Basis I R M) :
    MvPolynomial.homogeneousSubmodule I R →+*ᵍ
      Symmetric.Grading.BundleCycles.symmetricGrading R M where
  __ := (SymmetricAlgebra.equivMvPolynomial b).symm.toRingHom
  map_mem {n} {x} hx := by
    apply (SymmetricAlgebra.equivMvPolynomial_isHomogeneous_iff R M b n _).mp
    change ((SymmetricAlgebra.equivMvPolynomial b)
      ((SymmetricAlgebra.equivMvPolynomial b).symm x)).IsHomogeneous n
    rw [AlgEquiv.apply_symm_apply]
    exact hx

@[simp] theorem fromPolynomial_toPolynomial (b : Basis I R M) :
    (fromPolynomial b).comp (toPolynomial b) = GradedRingHom.id _ := by
  apply GradedRingHom.coe_ringHom_injective
  apply RingHom.ext
  intro x
  exact (SymmetricAlgebra.equivMvPolynomial b).symm_apply_apply x

@[simp] theorem toPolynomial_fromPolynomial (b : Basis I R M) :
    (toPolynomial b).comp (fromPolynomial b) = GradedRingHom.id _ := by
  apply GradedRingHom.coe_ringHom_injective
  apply RingHom.ext
  intro x
  exact (SymmetricAlgebra.equivMvPolynomial b).apply_symm_apply x

/-- The original projective schemes, identified through their genuine
homogeneous coordinate rings. -/
def projectiveIso (b : Basis I R M) :
    Proj (MvPolynomial.homogeneousSubmodule I R) ≅
      SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R M :=
  projIsoOfGradedAlgEquiv (SymmetricAlgebra.equivMvPolynomial b)
    (fun n x hx => (toPolynomial b).map_mem hx)
    (fun n x hx => (fromPolynomial b).map_mem hx)

theorem projectiveIso_hom_over (b : Basis I R M) :
    (projectiveIso b).hom ≫
      SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M =
        gradedProjStructureMap (MvPolynomial.homogeneousSubmodule I R) :=
  projIsoOfGradedAlgEquiv_hom_over (SymmetricAlgebra.equivMvPolynomial b)
    (fun n x hx => (toPolynomial b).map_mem hx)
    (fun n x hx => (fromPolynomial b).map_mem hx)

theorem projectiveIso_inv_over (b : Basis I R M) :
    (projectiveIso b).inv ≫ gradedProjStructureMap (MvPolynomial.homogeneousSubmodule I R) =
      SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M := by
  rw [← projectiveIso_hom_over b, Iso.inv_hom_id_assoc]

end PaperVerification.SymmetricFreeProjectiveIso
end
end
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.SymmetricFreeProjectiveIso"

section ComponentSource_1
/- Original module: PaperVerification.SymmetricProjectiveEmpty -/


/-!
# A zero vector space has empty projective spectrum

The argument uses the actual irrelevant homogeneous ideal: every one of its
module generators vanishes, contradicting the defining condition on a Proj point.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.SymmetricProjectiveEmpty

open AlgebraicGeometry
open OAI.AlgebraicGeometry.Divisors.LineBundles
open SymmetricProjective.Scheme.BundleCycles

theorem symmetricProjective_isEmpty_of_subsingleton (R M : Type)
    [CommRing R] [AddCommGroup M] [Module R M] [Subsingleton M] :
    IsEmpty (symmetricProjectiveScheme R M) := by
  refine ⟨fun x => x.not_irrelevant_le ?_⟩
  change (HomogeneousIdeal.irrelevant
    (Symmetric.Grading.BundleCycles.symmetricGrading R M)).toIdeal ≤
      x.asHomogeneousIdeal.toIdeal
  rw [Symmetric.GradingIdeals.BundleCycles.symmetricIrrelevant_eq_generatorIdeal]
  apply Ideal.span_le.mpr
  rintro a ⟨m,rfl⟩
  rw [Subsingleton.elim m 0, map_zero]
  exact Ideal.zero_mem _

end PaperVerification.SymmetricProjectiveEmpty
end
end
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.SymmetricProjectiveEmpty"


set_option pp.explicit false
set_option pp.proofs false
set_option pp.deepTerms false
set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let opts ← getOptions
  if true && env.header.trustLevel != 0 then
    throwError "The final environment has nonzero kernel trust level"
  if Lean.debug.skipKernelTC.get opts then
    throwError "The final environment disabled kernel type checking"
  if Lean.Elab.inServer.get opts then
    throwError "The final environment unexpectedly uses server mode"
  let required : Array (Name × String) := #[
    (`PaperVerification.SymmetricFreeProjectiveIso.toPolynomial, "definition"),
    (`PaperVerification.SymmetricFreeProjectiveIso.fromPolynomial, "definition"),
    (`PaperVerification.SymmetricFreeProjectiveIso.fromPolynomial_toPolynomial, "theorem"),
    (`PaperVerification.SymmetricFreeProjectiveIso.toPolynomial_fromPolynomial, "theorem"),
    (`PaperVerification.SymmetricFreeProjectiveIso.projectiveIso, "definition"),
    (`PaperVerification.SymmetricFreeProjectiveIso.projectiveIso_hom_over, "theorem"),
    (`PaperVerification.SymmetricFreeProjectiveIso.projectiveIso_inv_over, "theorem"),
    (`PaperVerification.SymmetricProjectiveEmpty.symmetricProjective_isEmpty_of_subsingleton, "theorem")
  ]
  let localNames := env.checked.get.constants.foldStage2 (fun acc name _ => acc.push name) (#[] : Array Name)
  if localNames.isEmpty then throwError "Empty authored declaration audit"
  let mut names := localNames
  for (name, _) in required do
    unless names.contains name do names := names.push name
  let mut rows : Array Json := #[]
  for name in names do
    let some info := env.checked.get.find? name | throwError "Missing checked declaration {name}"
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient primitive"
    if kind == "axiom" then throwError "Authored axiom {name}"
    let value := info.value? (allowOpaque := true)
    if kind == "theorem" || kind == "definition" || kind == "opaque" then
      unless value.isSome do throwError "No actual body {name}"
    for (requiredName, expectedKind) in required do
      if name == requiredName && kind != expectedKind then
        throwError "Endpoint kind mismatch {name}: expected {expectedKind}, got {kind}"
    let axioms ← collectAxioms name
    for ax in axioms do
      if ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound then
        throwError "Unapproved transitive axiom {name}: {ax}"
    let mut fields := [("name", toJson name.toString), ("kind", toJson kind),
      ("actual_body_available", toJson value.isSome),
      ("universe_parameters", toJson (info.levelParams.map Name.toString)),
      ("type_dependencies", toJson (info.type.getUsedConstants.map Name.toString)),
      ("body_dependencies", toJson ((value.map Expr.getUsedConstants).getD #[] |>.map Name.toString)),
      ("transitive_axioms", toJson (axioms.map Name.toString))]
    if required.any (fun e => e.1 == name) then
      let typeText ← liftTermElabM <| return (← Meta.ppExpr info.type).pretty
      fields := fields ++ [("readable_type", toJson typeText)]
    rows := rows.push (Json.mkObj fields)
  IO.FS.createDirAll ".lake/reports"
  let path := ".lake/reports/" ++ (← getEnv).mainModule.toString ++ ".json"
  IO.FS.writeFile path (Json.mkObj [("accepted", toJson true),
    ("nonce", toJson "5f4feb7b2169cd9846f4877f5caed67e"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:5f4feb7b2169cd9846f4877f5caed67e"
