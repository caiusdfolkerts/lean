module

public import paper_verification.relative_projective_geometry2
import all paper_verification.relative_projective_geometry2
public import paper_verification.symmetric_projective_geometry3
import all paper_verification.symmetric_projective_geometry3
public import paper_verification.twisting_coherence2
import all paper_verification.twisting_coherence2
public import paper_verification.ambient_polarization2
import all paper_verification.ambient_polarization2
public import paper_verification.symmetric_basis_degree2
import all paper_verification.symmetric_basis_degree2
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

section ComponentSource_0
/- Original module: PaperVerification.RelativeProjectivization -/


/-!
# Relative projectivization: the shared scheme construction

This file exposes short names for the recovered complete construction in
`ProjectivizationOfModuleSheaf`. Its scheme is glued from the actual
`Proj (Sym Γ(U,E))` over affine opens. Quasi-coherence proves the required
localization pullbacks; no chart or cohomology assertion is assumed.

The convention is the quotient convention: `Proj (Sym E)` parametrizes
line quotients of `E`. Projective lines in a locally free sheaf `T` use
this construction on `T`'s dual. All subsequent bundle constructions use
this single underlying definition.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.RelativeProjectivization

open CategoryTheory AlgebraicGeometry

variable {X : Scheme.{0}} (E : X.Modules) [E.IsQuasicoherent]

abbrev chart := ProjectivizationOfModuleSheaf.chart E
abbrev gradedRestriction {U V : X.AffineZariskiSite} (i : U ⟶ V) :=
  ProjectivizationOfModuleSheaf.gradedRestriction E i
abbrev chartMap {U V : X.AffineZariskiSite} (i : U ⟶ V) :=
  ProjectivizationOfModuleSheaf.chartMap E i
abbrev chartDiagram := ProjectivizationOfModuleSheaf.diagram E
abbrev gluingData := ProjectivizationOfModuleSheaf.glueData E
abbrev projectivization := ProjectivizationOfModuleSheaf.projectivization E
abbrev toBase := ProjectivizationOfModuleSheaf.projection E
abbrev chartCover := ProjectivizationOfModuleSheaf.openCover E

/-- Restriction to any affine base open is the genuine projective
spectrum of the module of all sections over that open. -/
theorem chart_isPullback (U : X.AffineZariskiSite) :
    IsPullback ((gluingData E).natTrans.app U) ((chartCover E).f U)
      U.val.ι (toBase E) :=
  ProjectivizationOfModuleSheaf.chart_isPullback E U

end PaperVerification.RelativeProjectivization
end
end
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.RelativeProjectivization"

section ComponentSource_1
/- Original module: PaperVerification.SymmetricProjectiveFrame -/


/-!
# Twisting sheaves under an actual basis chart

The geometric projective-space isomorphism is the separately checked
`SymmetricFreeProjectiveIso.projectiveIso`. Its pullback identifies the
actual homogeneous-fraction twisting sheaves in every integer degree.
The basis/graded-algebra construction is imported with its unique owner.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.SymmetricProjectiveFrame

open AlgebraicGeometry CategoryTheory Module
open OAI.AlgebraicGeometry.Divisors.LineBundles

universe u

variable {R M I : Type} [CommRing R] [AddCommGroup M] [Module R M]
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev toPolynomial (b : Basis I R M) := SymmetricFreeProjectiveIso.toPolynomial b
abbrev fromPolynomial (b : Basis I R M) := SymmetricFreeProjectiveIso.fromPolynomial b

/-- An inverse pair of graded maps preserves the irrelevant ideal in the
precise direction required by the projective-spectrum functor. -/
theorem irrelevant_le_map_of_inverse
    {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜) (hfg : f.comp g = GradedRingHom.id ℬ) :
    HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f := by
  apply (HomogeneousIdeal.irrelevant_le ℬ).mpr
  intro n hn x hx
  have hgf : f (g x) = x := congrArg (fun h : ℬ →+*ᵍ ℬ => h x) hfg
  rw [← hgf]
  exact Ideal.mem_map_of_mem f
    (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hn (g.map_mem hx))

/-- The previously constructed actual basis chart, with no second owner
for its graded-coordinate proof. -/
abbrev projectiveIso (b : Basis I R M) := SymmetricFreeProjectiveIso.projectiveIso b

/-- The canonical fraction map identifies every integer twist under the
actual geometric basis chart. -/
def twistingIso (b : Basis I R M) (n : ℤ) :
    (Scheme.Modules.pullback (projectiveIso b).hom).obj
        (Proj.twistingSheaf (Symmetric.Grading.BundleCycles.symmetricGrading R M) n) ≅
      Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule I R) n := by
  exact TwistingSheafMap.pullbackIso (toPolynomial b) (fromPolynomial b)
    (irrelevant_le_map_of_inverse _ _ (SymmetricFreeProjectiveIso.toPolynomial_fromPolynomial b))
    (irrelevant_le_map_of_inverse _ _ (SymmetricFreeProjectiveIso.fromPolynomial_toPolynomial b))
    (SymmetricFreeProjectiveIso.fromPolynomial_toPolynomial b)
    (SymmetricFreeProjectiveIso.toPolynomial_fromPolynomial b) n

end PaperVerification.SymmetricProjectiveFrame
end
end
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.SymmetricProjectiveFrame"

section ComponentSource_2
/- Original module: PaperVerification.SymmetricProjectiveTwisting -/


/-!
# Actual twisting sheaves under generated symmetric-algebra maps

This adapter connects OAI's actual `Proj(Sym M)` morphisms to the
homogeneous-fraction twisting sheaves. It applies to all generated graded
maps, including quotients and coefficient localizations. A full change of
frame is a special case and fixes no distinguished coordinate.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.SymmetricProjectiveTwisting

open AlgebraicGeometry CategoryTheory TopologicalSpace
open OAI.AlgebraicGeometry.Divisors.LineBundles

universe u

variable {R S M N : Type u} [CommRing R] [CommRing S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]

/-- The genuine linear coordinate is homogeneous of degree one. -/
theorem ι_mem (m : M) : SymmetricAlgebra.ι R M m ∈
    Symmetric.Grading.BundleCycles.symmetricGrading R M 1 := by
  change SymmetricAlgebra.ι R M m ∈ LinearMap.range (SymmetricAlgebra.ι R M) ^ 1
  simpa only [pow_one] using LinearMap.mem_range_self (SymmetricAlgebra.ι R M) m

/-- The actual degree-one opens cover the symmetric projective scheme,
with precisely the grading instance used by the cycle-theory sources. -/
theorem ι_cover :
    ⨆ m : M, Proj.basicOpen (Symmetric.Grading.BundleCycles.symmetricGrading R M)
      (SymmetricAlgebra.ι R M m) = ⊤ := by
  refine Proj.iSup_basicOpen_eq_top' _ _ (fun m => ⟨1, ι_mem m⟩) (top_unique ?_)
  rintro a -
  have ha : a ∈ Algebra.adjoin R (Set.range (SymmetricAlgebra.ι R M)) := by
    rw [TauCeti.SymmetricAlgebra.adjoin_range_ι]
    exact Algebra.mem_top
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin hx
  | algebraMap r =>
    exact Subalgebra.algebraMap_mem _
      (algebraMap R (Symmetric.Grading.BundleCycles.symmetricGrading R M 0) r)
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

/-- Every generated graded symmetric-algebra map preserves every actual
integer twist under ordinary sheaf pullback. -/
def generatedMapPullbackIso
    (g : Symmetric.Grading.BundleCycles.symmetricGrading R M →+*ᵍ
      Symmetric.Grading.BundleCycles.symmetricGrading S N)
    (hg : HomogeneousIdeal.irrelevant
        (Symmetric.Grading.BundleCycles.symmetricGrading S N) ≤
      (HomogeneousIdeal.irrelevant
        (Symmetric.Grading.BundleCycles.symmetricGrading R M)).map g)
    (n : ℤ) :
    (AlgebraicGeometry.Scheme.Modules.pullback (Proj.map g hg)).obj
        (Proj.twistingSheaf (Symmetric.Grading.BundleCycles.symmetricGrading R M) n) ≅
      Proj.twistingSheaf (Symmetric.Grading.BundleCycles.symmetricGrading S N) n :=
  TwistingSheafMap.pullbackIso_of_degreeOne_cover g hg
    (SymmetricAlgebra.ι R M) ι_mem ι_cover n

variable {P : Type u} [AddCommGroup P] [Module R P]

/-- Every integer twist is preserved by an arbitrary full linear change
of projective coordinates. -/
def twistingPullbackIso (e : M ≃ₗ[R] P) (n : ℤ) :
    (AlgebraicGeometry.Scheme.Modules.pullback
        (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveIso e).hom).obj
        (Proj.twistingSheaf (Symmetric.Grading.BundleCycles.symmetricGrading R P) n) ≅
      Proj.twistingSheaf (Symmetric.Grading.BundleCycles.symmetricGrading R M) n :=
  generatedMapPullbackIso
    (Symmetric.GradedMap.BundleCycles.symmetricGradedMap e.symm.toLinearMap)
    (SymmetricProjective.Scheme.BundleCycles.symmetricGradedMap_irrelevant _ e.symm.surjective) n

end PaperVerification.SymmetricProjectiveTwisting
end
end
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.SymmetricProjectiveTwisting"

section ComponentSource_3
/- Original module: PaperVerification.RelativeProjectiveTwisting -/


/-!
# The cartesian twisting family on a relative projectivization

The local objects are the homogeneous-fraction twisting sheaves on the
actual affine-base projective charts. Restriction is induced by the literal
restriction of module sections. A basis of those sections gives the usual
polynomial projective chart and preserves every integer twist.

This file supplies the local objects and isomorphisms for module-sheaf
descent. Constructing the global twisting line requires the subsequent
descent of this family, including its identity and composition laws.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.RelativeProjectiveTwisting

open AlgebraicGeometry CategoryTheory Module
open OAI.AlgebraicGeometry.Divisors.LineBundles
open ProjectivizationOfModuleSheaf

variable {X : Scheme.{0}} (M : X.Modules) [M.IsQuasicoherent]

/-- The actual integer twist on an affine-base projective chart. -/
def chartTwist (U : X.AffineZariskiSite) (n : ℤ) : (chart M U).Modules :=
  Proj.twistingSheaf
    (Symmetric.Grading.BundleCycles.symmetricGrading Γ(X, U.val) Γ(M, U.val)) n

/-- The restriction morphism is the map of homogeneous fractions induced
by restriction of the original sheaf's sections. -/
def restriction {U V : X.AffineZariskiSite} (i : U ⟶ V) (n : ℤ) :
    chartTwist M V n ⟶
      (Scheme.Modules.pushforward (chartMap M i)).obj (chartTwist M U n) :=
  TwistingSheafMap.pushforwardHom (gradedRestriction M i)
    (gradedRestriction_irrelevant M i) n

/-- Every chart transition pulls back the original integer twist to the
corresponding twist. This is the cartesian property used in descent. -/
def restrictionIso {U V : X.AffineZariskiSite} (i : U ⟶ V) (n : ℤ) :
    (Scheme.Modules.pullback (chartMap M i)).obj (chartTwist M V n) ≅
      chartTwist M U n :=
  SymmetricProjectiveTwisting.generatedMapPullbackIso
    (gradedRestriction M i) (gradedRestriction_irrelevant M i) n

/-- A local frame gives an isomorphism from the actual polynomial projective
space to the relative chart. The frame size is arbitrary. -/
def frameIso (U : X.AffineZariskiSite) {I : Type}
    (b : Basis I Γ(X, U.val) Γ(M, U.val)) :
    Proj (MvPolynomial.homogeneousSubmodule I Γ(X, U.val)) ≅ chart M U :=
  SymmetricProjectiveFrame.projectiveIso b

/-- All integer twists agree under the same local frame isomorphism. -/
def frameTwistingIso (U : X.AffineZariskiSite) {I : Type}
    (b : Basis I Γ(X, U.val) Γ(M, U.val)) (n : ℤ) :
    (Scheme.Modules.pullback (frameIso M U b).hom).obj (chartTwist M U n) ≅
      Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule I Γ(X, U.val)) n :=
  SymmetricProjectiveFrame.twistingIso b n

end PaperVerification.RelativeProjectiveTwisting
end
end
end ComponentSource_3

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.RelativeProjectiveTwisting"


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
    (`PaperVerification.SymmetricProjectiveFrame.twistingIso, "definition"),
    (`PaperVerification.SymmetricProjectiveTwisting.ι_cover, "theorem"),
    (`PaperVerification.SymmetricProjectiveTwisting.generatedMapPullbackIso, "definition"),
    (`PaperVerification.SymmetricProjectiveTwisting.twistingPullbackIso, "definition"),
    (`PaperVerification.RelativeProjectiveTwisting.chartTwist, "definition"),
    (`PaperVerification.RelativeProjectiveTwisting.restrictionIso, "definition"),
    (`PaperVerification.RelativeProjectiveTwisting.frameTwistingIso, "definition")
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
    ("nonce", toJson "ee35dcaef081f763ef0a20b0431e4b7b"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:ee35dcaef081f763ef0a20b0431e4b7b"
