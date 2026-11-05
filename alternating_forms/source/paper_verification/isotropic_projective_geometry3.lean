module

public import paper_verification.actual_odd_affine_paving6
import all paper_verification.actual_odd_affine_paving6
public import paper_verification.oai_chow001_run2
import all paper_verification.oai_chow001_run2
public import paper_verification.section_four_geometry1
import all paper_verification.section_four_geometry1
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

section ComponentSource_0
/- Original module: PaperVerification.HomogeneousQuotientProjectivePresentation -/


/-!
# A genuine projective presentation of a homogeneous polynomial quotient

The embedding is the actual `Proj` morphism of the quotient graded ring.
A finite renumbering of the original variables places its target in the
standard projective space used by the complex-point library.  This is only
packaging of a proved closed immersion; no topological hypothesis is added.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.HomogeneousQuotientProjective

open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [Field K]
  (I : Ideal (MvPolynomial σ K))
  (hI : I.IsHomogeneous (homogeneousSubmodule σ K))

def polynomialQuotientGradedHom : homogeneousSubmodule σ K →+*ᵍ grading I hI where
  __ := Ideal.Quotient.mk I
  map_mem {d} {x} hx := by
    rw [grading_eq_piece]
    exact ⟨x,hx,rfl⟩

theorem polynomialQuotientGradedHom_surjective :
    GradedSurjective (polynomialQuotientGradedHom I hI) := by
  intro d x hx
  rw [grading_eq_piece] at hx
  obtain ⟨p,hp,rfl⟩ := hx
  exact ⟨p,hp,rfl⟩

/-- The original closed embedding into its unquotiented polynomial Proj. -/
def polynomialQuotientProjEmbedding : Proj (grading I hI) ⟶ Proj (homogeneousSubmodule σ K) :=
  Proj.map (polynomialQuotientGradedHom I hI)
    (irrelevant_le_map_of_gradedSurjective _ (polynomialQuotientGradedHom_surjective I hI))

instance polynomialQuotientProjEmbedding_isClosedImmersion :
    IsClosedImmersion (polynomialQuotientProjEmbedding I hI) :=
  isClosedImmersion_projMap_of_gradedSurjective _ (polynomialQuotientGradedHom_surjective I hI)

theorem polynomialQuotientProjEmbedding_over :
    polynomialQuotientProjEmbedding I hI ≫ gradedProjStructureMap (homogeneousSubmodule σ K) =
      HomogeneousQuotientCharts.structureMap I hI :=
  gradedProjMap_over_hom _ _ (fun _ => rfl)

variable [Fintype σ] [Nonempty σ]

/-- The original variable set is nonempty in every relevant Grassmannian
range. Its finite cardinal gives the standard ambient projective dimension. -/
def projectiveVariableEquiv : σ ≃ Fin ((Fintype.card σ - 1) + 1) :=
  (Fintype.equivFin σ).trans
    (finCongr (Nat.sub_add_cancel (Fintype.card_pos_iff.mpr inferInstance)).symm)

def polynomialProjStandardIso :
    Proj (homogeneousSubmodule σ K) ≅
      Proj (homogeneousSubmodule (Fin ((Fintype.card σ - 1)+1)) K) :=
  projIsoOfGradedAlgEquiv (renameEquiv K (projectiveVariableEquiv (σ := σ)).symm)
    (fun _ _ hp => hp.rename_isHomogeneous)
    (fun _ _ hp => hp.rename_isHomogeneous)

theorem polynomialProjStandardIso_hom_over :
    (polynomialProjStandardIso (K := K) (σ := σ)).hom ≫
      gradedProjStructureMap (homogeneousSubmodule (Fin ((Fintype.card σ - 1)+1)) K) =
        gradedProjStructureMap (homogeneousSubmodule σ K) :=
  projIsoOfGradedAlgEquiv_hom_over _ _ _

/-- An actual closed projective embedding over the complex numbers. -/
def projectivePresentation
    (I : Ideal (MvPolynomial σ ℂ))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ ℂ)) :
    OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation
      (Proj (grading I hI)) (HomogeneousQuotientCharts.structureMap I hI) where
  ambientDimension := Fintype.card σ - 1
  embedding := polynomialQuotientProjEmbedding I hI ≫
    (polynomialProjStandardIso (K := ℂ) (σ := σ)).hom
  closedImmersion := by infer_instance
  over_base := by
    change _ ≫ gradedProjStructureMap
      (homogeneousSubmodule (Fin ((Fintype.card σ - 1)+1)) ℂ) = _
    rw [Category.assoc, polynomialProjStandardIso_hom_over,
      polynomialQuotientProjEmbedding_over]

end PaperVerification.HomogeneousQuotientProjective
end
end
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.HomogeneousQuotientProjectivePresentation"

section ComponentSource_1
/- Original module: PaperVerification.IsotropicProjectivePresentation -/


/-!
# The original common-isotropic scheme as a smooth projective presentation

The projective embedding is induced by the original homogeneous quotient,
with its actual scalar structure. Smoothness is transported by the proved
coordinate permutation. No cohomology or Chow hypothesis is part of this data.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.IsotropicAttractingCharts

open AlgebraicGeometry CategoryTheory MvPolynomial
open AlternatingForms IsotropicAttractingCoordinates
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The chain-coordinate model has the original closed projective
embedding, with its structure morphism to the complex numbers. -/
def chainProjectivePresentation (k t : ℕ) (hs : t+2 ≤ k+1) :
    OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation
      (Proj (isotropicProjectiveGrading (t := t)
        (canonicalForms (K := ℂ) (n := 2*k+1) (2*k+1) (2*k))))
      (isotropicStructureMap (canonicalForms (2*k+1) (2*k))) := by
  letI : Nonempty (PluckerIndex (t+2) (2*k+1)) := ⟨oddCoordinatePivot k t hs⟩
  exact HomogeneousQuotientProjective.projectivePresentation
    (isotropicPluckerIdeal (canonicalForms (2*k+1) (2*k)))
    (isotropicPluckerIdeal_isHomogeneous (canonicalForms (2*k+1) (2*k)))

theorem chain_isNoetherian (k t : ℕ) (hs : t+2 ≤ k+1) :
    AlgebraicGeometry.IsNoetherian
      (Proj (isotropicProjectiveGrading (t := t)
        (canonicalForms (K := ℂ) (n := 2*k+1) (2*k+1) (2*k)))) :=
  (chainProjectivePresentation k t hs).isNoetherian

/-- Packaging the proved geometric properties for the standard upstream
intersection and analytic APIs. -/
def chainSmoothProjectivePresentation (k t : ℕ) (hs : t+2 ≤ k+1) :
    OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation where
  carrier := Proj (isotropicProjectiveGrading (t := t)
    (canonicalForms (K := ℂ) (n := 2*k+1) (2*k+1) (2*k)))
  structureMap := isotropicStructureMap _
  projective := chainProjectivePresentation k t hs
  smooth := chainCanonical_isotropicStructureMap_smooth k t

end PaperVerification.IsotropicAttractingCharts
end
end
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.IsotropicProjectivePresentation"

section ComponentSource_2
/- Original module: PaperVerification.OnePlaneProjectiveComparison -/


/-!
# The original one-plane Plücker scheme is ordinary projective space

The comparison is induced by the literal one-entry Plücker indices and the
proved zero relation ideal. Both directions preserve the original homogeneous
degree, and the actual projective isomorphism preserves the scalar structure.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.AlternatingForms

open AlgebraicGeometry CategoryTheory MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] [CharZero K]

/-- A one-entry increasing index has exactly one ordinary coordinate. -/
def onePlaneIndexEquiv (n : ℕ) : Fin n ≃ PluckerIndex 1 n where
  toFun := onePlaneIndex
  invFun I := I.val 0
  left_inv _ := rfl
  right_inv := onePlaneIndex_eta

/-- The exact original homogeneous quotient is the free coordinate ring. -/
def onePlanePolynomialAlgEquiv (n : ℕ) :
    (MvPolynomial (PluckerIndex 1 n) K ⧸ matrixPluckerIdeal) ≃ₐ[K]
      MvPolynomial (Fin n) K :=
  ((Ideal.quotientEquivAlgOfEq K onePlane_matrixPluckerIdeal).trans
    (AlgEquiv.quotientBot K _)).trans (renameEquiv K (onePlaneIndexEquiv n).symm)

@[simp] theorem onePlanePolynomialAlgEquiv_mk (n : ℕ)
    (p : MvPolynomial (PluckerIndex 1 n) K) :
    onePlanePolynomialAlgEquiv (K := K) n (Ideal.Quotient.mk _ p) =
      rename (onePlaneIndexEquiv n).symm p := rfl

@[simp] theorem onePlanePolynomialAlgEquiv_symm (n : ℕ)
    (p : MvPolynomial (Fin n) K) :
    (onePlanePolynomialAlgEquiv (K := K) n).symm p =
      Ideal.Quotient.mk _ (rename (onePlaneIndexEquiv n) p) := rfl

theorem onePlanePolynomialAlgEquiv_mem (n d : ℕ)
    (x : MvPolynomial (PluckerIndex 1 n) K ⧸ matrixPluckerIdeal)
    (hx : x ∈ onePlaneOriginalGrading (K := K) n d) :
    onePlanePolynomialAlgEquiv n x ∈ homogeneousSubmodule (Fin n) K d := by
  change x ∈ HomogeneousQuotientProjective.grading _ _ d at hx
  rw [HomogeneousQuotientProjective.grading_eq_piece] at hx
  obtain ⟨p,hp,rfl⟩ := hx
  change rename (onePlaneIndexEquiv n).symm p ∈ homogeneousSubmodule (Fin n) K d
  exact hp.rename_isHomogeneous

theorem onePlanePolynomialAlgEquiv_symm_mem (n d : ℕ)
    (x : MvPolynomial (Fin n) K) (hx : x ∈ homogeneousSubmodule (Fin n) K d) :
    (onePlanePolynomialAlgEquiv n).symm x ∈ onePlaneOriginalGrading (K := K) n d := by
  change _ ∈ HomogeneousQuotientProjective.grading _ _ d
  rw [HomogeneousQuotientProjective.grading_eq_piece]
  exact ⟨rename (onePlaneIndexEquiv n) x,hx.rename_isHomogeneous,rfl⟩

/-- The actual scheme isomorphism retains all original Plücker coordinates. -/
def onePlaneOriginalProjIsoPolynomial (n : ℕ) :
    Proj (onePlaneOriginalGrading (K := K) n) ≅
      Proj (homogeneousSubmodule (Fin n) K) :=
  (projIsoOfGradedAlgEquiv (onePlanePolynomialAlgEquiv n)
    (onePlanePolynomialAlgEquiv_mem n) (onePlanePolynomialAlgEquiv_symm_mem n)).symm

theorem onePlaneOriginalProjIsoPolynomial_hom_over (n : ℕ) :
    (onePlaneOriginalProjIsoPolynomial (K := K) n).hom ≫
      gradedProjStructureMap (homogeneousSubmodule (Fin n) K) =
        onePlaneOriginalStructureMap n :=
  projIsoOfGradedAlgEquiv_inv_over (onePlanePolynomialAlgEquiv n)
    (onePlanePolynomialAlgEquiv_mem n) (onePlanePolynomialAlgEquiv_symm_mem n)

/-- The original one-plane scheme has a genuine closed projective presentation. -/
def onePlaneOriginalProjectivePresentation (n : ℕ) (hn : 0 < n) :
    OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation
      (Proj (onePlaneOriginalGrading (K := ℂ) n)) (onePlaneOriginalStructureMap n) := by
  letI : Nonempty (PluckerIndex 1 n) := ⟨onePlaneIndex ⟨0,hn⟩⟩
  exact HomogeneousQuotientProjective.projectivePresentation
    (matrixPluckerIdeal (s := 1) (n := n))
    (matrixPluckerIdeal_isHomogeneous (by decide : 0 < 1))

/-- The actual original one-plane scheme is irreducible for every nonzero
ambient dimension, by its prime homogeneous quotient. -/
theorem onePlaneOriginalProj_irreducible (n : ℕ) (hn : 0 < n) :
    IrreducibleSpace (Proj (onePlaneOriginalGrading (K := K) n)) := by
  letI := onePlane_ideal_isPrime (K := K) n
  letI := onePlaneOriginalProj_nonempty (K := K) n hn
  exact projective_irreducibleSpace_of_domain _

end PaperVerification.AlternatingForms
end
end
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.OnePlaneProjectiveComparison"


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
    (`PaperVerification.HomogeneousQuotientProjective.polynomialQuotientGradedHom, "definition"),
    (`PaperVerification.HomogeneousQuotientProjective.polynomialQuotientGradedHom_surjective, "theorem"),
    (`PaperVerification.HomogeneousQuotientProjective.polynomialQuotientProjEmbedding, "definition"),
    (`PaperVerification.HomogeneousQuotientProjective.polynomialQuotientProjEmbedding_isClosedImmersion, "theorem"),
    (`PaperVerification.HomogeneousQuotientProjective.polynomialQuotientProjEmbedding_over, "theorem"),
    (`PaperVerification.HomogeneousQuotientProjective.polynomialProjStandardIso, "definition"),
    (`PaperVerification.HomogeneousQuotientProjective.polynomialProjStandardIso_hom_over, "theorem"),
    (`PaperVerification.HomogeneousQuotientProjective.projectivePresentation, "definition"),
    (`PaperVerification.IsotropicAttractingCharts.chainProjectivePresentation, "definition"),
    (`PaperVerification.IsotropicAttractingCharts.chain_isNoetherian, "theorem"),
    (`PaperVerification.IsotropicAttractingCharts.chainSmoothProjectivePresentation, "definition"),
    (`PaperVerification.AlternatingForms.onePlaneIndexEquiv, "definition"),
    (`PaperVerification.AlternatingForms.onePlanePolynomialAlgEquiv, "definition"),
    (`PaperVerification.AlternatingForms.onePlaneOriginalProjIsoPolynomial, "definition"),
    (`PaperVerification.AlternatingForms.onePlaneOriginalProjIsoPolynomial_hom_over, "theorem"),
    (`PaperVerification.AlternatingForms.onePlaneOriginalProjectivePresentation, "definition"),
    (`PaperVerification.AlternatingForms.onePlaneOriginalProj_irreducible, "theorem")
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
    ("nonce", toJson "17d8d04b7bf8d5e6ca164fc23689d54c"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:17d8d04b7bf8d5e6ca164fc23689d54c"
