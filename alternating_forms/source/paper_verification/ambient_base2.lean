module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import paper_verification.literal005
import all paper_verification.literal005
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let opts ← getOptions
  if env.header.trustLevel != 0 then
    throwError "Header-cache environment has nonzero kernel trust level"
  if Lean.debug.skipKernelTC.get opts then
    throwError "Header-cache environment disabled kernel type checking"
  if Lean.Elab.inServer.get opts then
    throwError "Header-cache environment unexpectedly uses server mode"
  logInfo "HEADER_CACHE_CHECKING_OPTIONS_VERIFIED"

section ComponentSource_0
/- Original module: PaperVerification.ProjGradedSurjection -/


/-!
# Closed immersions induced by surjective graded maps

Surjectivity on each homogeneous piece implies surjectivity on every
degree-zero localization.  The standard affine charts then show that the
induced morphism of actual projective schemes is a closed immersion.
The argument retains the scheme structure; no radical is taken.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousIdeal
open _root_.HomogeneousLocalization
open scoped HomogeneousIdeal

namespace PaperVerification

universe u

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- The exact piecewise surjectivity needed by the Proj construction. -/
def GradedSurjective (f : 𝒜 →+*ᵍ ℬ) : Prop :=
  ∀ d b, b ∈ ℬ d → ∃ a, a ∈ 𝒜 d ∧ f a = b

theorem irrelevant_le_map_of_gradedSurjective (f : 𝒜 →+*ᵍ ℬ)
    (hf : GradedSurjective f) : ℬ₊ ≤ 𝒜₊.map f := by
  apply _root_.toIdeal_le_toIdeal_iff.mp
  apply (HomogeneousIdeal.toIdeal_irrelevant_le ℬ).mpr
  intro d hd b hb
  obtain ⟨a, ha, rfl⟩ := hf d b hb
  change f a ∈ (𝒜₊.map f).toIdeal
  rw [HomogeneousIdeal.toIdeal_map]
  exact Ideal.mem_map_of_mem f
    (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hd ha)

/-- Homogeneous numerators lift without altering their degree or denominator. -/
theorem gradedAwayMap_surjective (f : 𝒜 →+*ᵍ ℬ)
    (hf : GradedSurjective f) {d : ℕ} {s : A} (hs : s ∈ 𝒜 d) :
    Function.Surjective (Away.map f s) := by
  intro z
  obtain ⟨r, b, hb, rfl⟩ := Away.mk_surjective ℬ (f.map_mem hs) z
  obtain ⟨a, ha, rfl⟩ := hf (r • d) b hb
  exact ⟨Away.mk 𝒜 hs r a ha, Away.map_mk f s hs r a ha⟩

/-- The standard affine chart square for a Proj morphism is cartesian. -/
theorem gradedProjMap_chart_isPullback (f : 𝒜 →+*ᵍ ℬ)
    (hf : ℬ₊ ≤ 𝒜₊.map f) {d : ℕ} (hd : 0 < d)
    (s : A) (hs : s ∈ 𝒜 d) :
    IsPullback (Spec.map (CommRingCat.ofHom (Away.map f s)))
      (Proj.awayι ℬ (f s) (f.map_mem hs) hd)
      (Proj.awayι 𝒜 s hs hd) (Proj.map f hf) := by
  apply IsOpenImmersion.isPullback
  · exact Proj.awayι_comp_map f hf hd s hs
  · simp only [Proj.opensRange_awayι, Proj.map_preimage_basicOpen]

/-- A map surjective on every homogeneous piece gives a closed immersion of
Mathlib's projective schemes. -/
theorem isClosedImmersion_projMap_of_gradedSurjective
    (f : 𝒜 →+*ᵍ ℬ) (hf : GradedSurjective f) :
    IsClosedImmersion
      (Proj.map f (irrelevant_le_map_of_gradedSurjective f hf)) := by
  let h := irrelevant_le_map_of_gradedSurjective f hf
  apply IsZariskiLocalAtTarget.of_openCover (Proj.affineOpenCover 𝒜).openCover
  intro s
  let g := Spec.map (CommRingCat.ofHom (Away.map f s.2.1))
  have hg : IsClosedImmersion g :=
    IsClosedImmersion.spec_of_surjective _ (gradedAwayMap_surjective f hf s.2.2)
  let square := gradedProjMap_chart_isPullback f h s.1.2 s.2.1 s.2.2
  change IsClosedImmersion (pullback.snd (Proj.map f h)
    (Proj.awayι 𝒜 s.2.1 s.2.2 s.1.2))
  rw [← square.flip.isoPullback_inv_snd]
  exact IsClosedImmersion.comp _ _

end PaperVerification
end
end
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.ProjGradedSurjection"

section ComponentSource_1
/- Original module: PaperVerification.HomogeneousQuotientClosedImmersion -/


/-!
# Closed immersions between homogeneous polynomial quotients

Inclusion of the original homogeneous ideals induces the canonical graded
quotient map and hence a closed immersion of their projective schemes.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace PaperVerification.HomogeneousQuotientProjective

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [Field K]
  (I J : Ideal (MvPolynomial σ K))
  (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
  (hJ : J.IsHomogeneous (homogeneousSubmodule σ K))
  (hIJ : I ≤ J)

/-- The canonical quotient map, retaining the original polynomial grading. -/
def quotientGradedHom : grading I hI →+*ᵍ grading J hJ where
  __ := Ideal.Quotient.factor hIJ
  map_mem {d} {x} hx := by
    rw [grading_eq_piece] at hx ⊢
    obtain ⟨p, hp, rfl⟩ := hx
    exact ⟨p, hp, rfl⟩

@[simp]
theorem quotientGradedHom_mk (p : MvPolynomial σ K) :
    quotientGradedHom I J hI hJ hIJ (Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk J p := rfl

theorem quotientGradedHom_surjective :
    GradedSurjective (quotientGradedHom I J hI hJ hIJ) := by
  intro d b hb
  rw [grading_eq_piece] at hb
  obtain ⟨p, hp, rfl⟩ := hb
  refine ⟨Ideal.Quotient.mk I p, ?_, rfl⟩
  rw [grading_eq_piece]
  exact ⟨p, hp, rfl⟩

/-- The actual projective closed immersion induced by inclusion of ideals. -/
def quotientProjMap : Proj (grading J hJ) ⟶ Proj (grading I hI) :=
  Proj.map (quotientGradedHom I J hI hJ hIJ)
    (irrelevant_le_map_of_gradedSurjective _
      (quotientGradedHom_surjective I J hI hJ hIJ))

instance quotientProjMap_isClosedImmersion :
    IsClosedImmersion (quotientProjMap I J hI hJ hIJ) :=
  isClosedImmersion_projMap_of_gradedSurjective _
    (quotientGradedHom_surjective I J hI hJ hIJ)

@[simp]
theorem quotientProjMap_preimage_variable (i : σ) :
    quotientProjMap I J hI hJ hIJ ⁻¹ᵁ
      Proj.basicOpen (grading I hI) (Ideal.Quotient.mk I (X i)) =
      Proj.basicOpen (grading J hJ) (Ideal.Quotient.mk J (X i)) := rfl

end PaperVerification.HomogeneousQuotientProjective
end
end
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.HomogeneousQuotientClosedImmersion"


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
    (`PaperVerification.GradedSurjective, "definition"),
    (`PaperVerification.irrelevant_le_map_of_gradedSurjective, "theorem"),
    (`PaperVerification.gradedAwayMap_surjective, "theorem"),
    (`PaperVerification.gradedProjMap_chart_isPullback, "theorem"),
    (`PaperVerification.isClosedImmersion_projMap_of_gradedSurjective, "theorem"),
    (`PaperVerification.HomogeneousQuotientProjective.quotientGradedHom, "definition"),
    (`PaperVerification.HomogeneousQuotientProjective.quotientGradedHom_surjective, "theorem"),
    (`PaperVerification.HomogeneousQuotientProjective.quotientProjMap, "definition")
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
    ("nonce", toJson "f0fa34e727d9746c93363e3b47acfd6b"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:f0fa34e727d9746c93363e3b47acfd6b"
