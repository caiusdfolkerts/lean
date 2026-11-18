module
public import SegreVerified.Stage025.ChartCoordinates
import all Lean.Util.CollectAxioms

set_option Elab.async false
set_option linter.all false

#eval do
  let toolchain ← IO.FS.readFile "lean-toolchain"
  let manifest ← IO.FS.readFile "lake-manifest.json"
  IO.println ("SEGRE_PUBLIC_ENVIRONMENT_BEGIN\n" ++ Lean.versionString ++ "\n" ++
    Lean.githash ++ "\n" ++ toolchain.trimAscii.toString ++ "\n" ++ manifest ++
    "\nSEGRE_PUBLIC_ENVIRONMENT_END")

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  unless env.header.trustLevel == 0 do
    throwError "The retained source check requires kernel trust level zero"
  let imported := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  let rows := CollectAxioms.runM (env.setExporting false) do
    #[``Nat.add_comm, ``Nat.zero_add].mapM fun name =>
      return (name, ← CollectAxioms.collectAndGet imported.find? name)
  for (name, axioms) in rows do
    unless (env.checked.get.find? name).isSome do throwError "Unchecked smoke target: {name}"
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved shared-collector smoke axiom: {ax}"
  logInfo "SEGRE_SHARED_COLLECTOR_READY"


set_option Elab.async false
set_option maxErrors 0
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

@[expose] public section
noncomputable section
set_option autoImplicit false

/-! The actual zero scheme of a quasicoherent functional, independent of tensor geometry. -/

section SegreSectionZeroScheme

/-!
# The genuine zero-scheme of a quasicoherent functional

For an actual morphism M → O_X, the image ideals on affine opens satisfy
localization compatibility because sections of M localize. They therefore
define Mathlib's genuine ideal-sheaf subscheme, rather than a predicate on
a family of chart rings. Its finite/reduced property is compared with the
ordinary finite-dimensional/reduced quotient algebras of any finite affine
cover over a field.

-/

set_option autoImplicit false
open scoped Classical

namespace PaperVerification.Segre.SectionZeroScheme

-- Affine-open coercions and subscheme covers are definitionally equal after
-- unfolding their ordinary definitions. The kernel checks these equalities.
set_option backward.isDefEq.respectTransparency false

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped ProjectiveChartSections

universe u v
variable {X : Scheme.{u}} {M : X.Modules} (φ : M ⟶ 𝟙_ X.Modules)

/-- The actual map to regular functions on an open. -/
def sectionMap (U : X.Opens) : Γ(M, U) →ₗ[Γ(X, U)] Γ(X, U) :=
  (φ.val.app (op U)).hom

/-- The actual image ideal on an affine open. -/
def sectionIdeal (U : X.affineOpens) : Ideal Γ(X, U) :=
  LinearMap.range (sectionMap φ U)

theorem sectionMap_naturality {U V : X.Opens} (h : V ≤ U) (m : Γ(M, U)) :
    sectionMap φ V (M.presheaf.map (homOfLE h).op m) =
      X.presheaf.map (homOfLE h).op (sectionMap φ U m) :=
  PresheafOfModules.naturality_apply φ.val (homOfLE h).op m

/-- Localization of the actual image ideal follows from localization of
the source module; no local freeness or regular-sequence assumption occurs. -/
theorem map_sectionIdeal_basicOpen [M.IsQuasicoherent]
    (U : X.affineOpens) (f : Γ(X, U)) :
    (sectionIdeal φ U).map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom =
      sectionIdeal φ (X.affineBasicOpen f) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    rintro r ⟨m, rfl⟩
    exact ⟨M.presheaf.map (homOfLE (X.basicOpen_le f)).op m,
      sectionMap_naturality φ (X.basicOpen_le f) m⟩
  · rintro r ⟨m, rfl⟩
    obtain ⟨n, m₀, hm⟩ := M.exists_pow_smul_eq_map U.property f rfl
      (X.basicOpen_le f) m
    let J := (sectionIdeal φ U).map
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
    have hmem : X.presheaf.map (homOfLE (X.basicOpen_le f)).op
        (sectionMap φ U m₀) ∈ J :=
      Ideal.mem_map_of_mem _ ⟨m₀, rfl⟩
    have he : X.presheaf.map (homOfLE (X.basicOpen_le f)).op f ^ n *
        sectionMap φ (X.basicOpen f) m =
      X.presheaf.map (homOfLE (X.basicOpen_le f)).op (sectionMap φ U m₀) := by
      have h := congrArg (sectionMap φ (X.basicOpen f)) hm
      simpa only [_root_.map_smul, smul_eq_mul, sectionMap_naturality] using h
    have hu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) :=
      X.toRingedSpace.isUnit_res_basicOpen f
    have hmem' : X.presheaf.map (homOfLE (X.basicOpen_le f)).op f ^ n *
        sectionMap φ (X.basicOpen f) m ∈ J := he.symm ▸ hmem
    exact (Ideal.unit_mul_mem_iff_mem J (hu.pow n)).mp hmem'

/-- The genuine quasicoherent image ideal sheaf. -/
def idealSheaf [M.IsQuasicoherent] : X.IdealSheafData where
  ideal := sectionIdeal φ
  map_ideal_basicOpen := map_sectionIdeal_basicOpen φ

/-- The actual closed zero-scheme of the functional. -/
def zeroScheme [M.IsQuasicoherent] : Scheme.{u} := (idealSheaf φ).subscheme

/-- Its actual closed immersion into the original ambient scheme. -/
def inclusion [M.IsQuasicoherent] : zeroScheme φ ⟶ X :=
  (idealSheaf φ).subschemeι

instance [M.IsQuasicoherent] : IsClosedImmersion (inclusion φ) := by
  unfold inclusion
  infer_instance

/-- Any original affine cover pulls back to the actual quotient-chart
cover of the zero-scheme, retaining the complete ideal and its nilpotents. -/
def affineCover [M.IsQuasicoherent] {ι : Type v} (U : ι → X.affineOpens)
    (hU : (⨆ i, (U i).val) = ⊤) : (zeroScheme φ).AffineOpenCover where
  I₀ := ι
  X i := CommRingCat.of (Γ(X, U i) ⧸ sectionIdeal φ (U i))
  f i := (idealSheaf φ).subschemeCover.f (U i)
  map_prop i := (idealSheaf φ).subschemeCover.map_prop (U i)
  idx x := (X.openCoverOfIsOpenCover (fun i => (U i).val) hU).idx x.val
  covers x := by
    let i := (X.openCoverOfIsOpenCover (fun i => (U i).val) hU).idx x.val
    have hx : x.val ∈ (U i).val := by
      obtain ⟨⟨y, hy⟩, he⟩ :=
        (X.openCoverOfIsOpenCover (fun i => (U i).val) hU).covers x.val
      exact he ▸ hy
    exact ((idealSheaf φ).opensRange_subschemeCover_map (U i)).ge hx

/-- Reducedness of the actual whole zero-scheme is equivalent to
reducedness of the entire quotient algebras on a genuine affine cover. -/
theorem reduced_iff [M.IsQuasicoherent] {ι : Type v}
    (U : ι → X.affineOpens) (hU : (⨆ i, (U i).val) = ⊤) :
    AlgebraicGeometry.IsReduced (zeroScheme φ) ↔
      ∀ i, _root_.IsReduced (Γ(X, U i) ⧸ sectionIdeal φ (U i)) := by
  rw [AlgebraicGeometry.IsReduced.iff_of_openCover (zeroScheme φ)
    (affineCover φ U hU).openCover]
  exact forall_congr' fun i => affine_isReduced_iff _

section Finiteness

variable {Y : Scheme.{u}} [IsAffine Y] [IsLocallyArtinian Y]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Over an affine Artinian base, a finite affine cover detects actual
finite morphisms. This is proved through local quasi-finiteness and
quasi-compactness, not made the definition of a finite scheme. -/
theorem finite_iff_affineCover {Z : Scheme.{u}} (f : Z ⟶ Y)
    (𝒰 : Z.AffineOpenCover) [Finite 𝒰.I₀] :
    IsFinite f ↔ ∀ i, IsFinite (𝒰.f i ≫ f) := by
  -- Supply Mathlib's canonical proved instances explicitly: their dependent
  -- affine-property arguments need not be inferred by instance search.
  let hqc : HasAffineProperty (@QuasiCompact.{u})
      (fun X _ _ _ => CompactSpace X) :=
    AlgebraicGeometry.instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat
  have compact_iff {W : Scheme.{u}} (g : W ⟶ Y) :
      QuasiCompact g ↔ CompactSpace W :=
    @HasAffineProperty.iff_of_isAffine.{u} (@QuasiCompact.{u})
      (fun X _ _ _ => CompactSpace X) hqc W Y g inferInstance
  letI : IsZariskiLocalAtSource (@LocallyQuasiFinite.{u}) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ RingHom.QuasiFinite
      AlgebraicGeometry.instHasRingHomPropertyLocallyQuasiFiniteQuasiFinite
  constructor
  · intro hf i
    letI := hf
    letI : QuasiCompact (𝒰.f i ≫ f) :=
      (compact_iff (𝒰.f i ≫ f)).mpr
        (inferInstanceAs (CompactSpace (Spec (𝒰.X i))))
    exact IsFinite.of_locallyQuasiFinite _
  · intro hf
    haveI : ∀ i, IsFinite (𝒰.f i ≫ f) := hf
    haveI : LocallyQuasiFinite f :=
      (IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyQuasiFinite)
        (f := f) 𝒰.openCover).mpr fun i => by
          change LocallyQuasiFinite (𝒰.f i ≫ f)
          letI : IsFinite (𝒰.f i ≫ f) := hf i
          infer_instance
    haveI : Finite 𝒰.openCover.I₀ := ‹Finite 𝒰.I₀›
    haveI : ∀ i : 𝒰.openCover.I₀, CompactSpace (𝒰.openCover.X i) := by
      intro i
      change CompactSpace (Spec (𝒰.X i))
      infer_instance
    haveI : CompactSpace Z := 𝒰.openCover.compactSpace
    haveI : QuasiCompact f :=
      (compact_iff f).mpr inferInstance
    exact IsFinite.of_locallyQuasiFinite _

end Finiteness

section BaseField

variable (K : Type u) [Field K] [X.Over (Spec (.of K))]

/-- The original structure morphism on an affine chart is exactly the
map induced by its original base-field algebra structure. -/
theorem fromSpec_toBase (U : X.affineOpens) :
    U.property.fromSpec ≫ (X ↘ Spec (.of K)) =
      Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, U))) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec (X ↘ Spec (.of K))
    (isAffineOpen_top _) U.property le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  congr 1
  exact (Scheme.baseRingToStructurePresheaf_app_eq_appLE (R := K) (X := X) U).symm

/-- The structure morphism of the genuine zero-scheme. -/
def toBase [M.IsQuasicoherent] : zeroScheme φ ⟶ Spec (.of K) :=
  inclusion φ ≫ (X ↘ Spec (.of K))

/-- The map of an actual zero-scheme quotient chart to the coefficient
spectrum is the spectrum of the original quotient algebra's scalar map. -/
theorem affineCover_toBase [M.IsQuasicoherent] {ι : Type v}
    (U : ι → X.affineOpens) (hU : (⨆ i, (U i).val) = ⊤) (i : ι) :
    (affineCover φ U hU).f i ≫ toBase φ K =
      Spec.map (CommRingCat.ofHom
        (algebraMap K (Γ(X, U i) ⧸ sectionIdeal φ (U i)))) := by
  change (idealSheaf φ).subschemeCover.f (U i) ≫
    ((idealSheaf φ).subschemeι ≫ (X ↘ Spec (.of K))) = _
  rw [← Category.assoc, (idealSheaf φ).subschemeCover_map_subschemeι,
    (idealSheaf φ).glueDataObjι_ι, Category.assoc,
    fromSpec_toBase K (U i), ← Spec.map_comp]
  congr 1

/-- Actual scheme-theoretic finiteness over the original field is exactly
finite-dimensionality of the complete chart quotient algebras. -/
theorem finite_iff [M.IsQuasicoherent] {ι : Type v} [Finite ι]
    (U : ι → X.affineOpens) (hU : (⨆ i, (U i).val) = ⊤) :
    IsFinite (toBase φ K) ↔
      ∀ i, Module.Finite K (Γ(X, U i) ⧸ sectionIdeal φ (U i)) := by
  haveI : IsLocallyArtinian (Spec (.of K)) :=
    Scheme.isLocallyArtinianScheme_Spec.mpr inferInstance
  haveI : Finite (affineCover φ U hU).I₀ := ‹Finite ι›
  rw [finite_iff_affineCover (toBase φ K) (affineCover φ U hU)]
  simp only [affineCover_toBase, IsFinite.SpecMap_iff,
    CommRingCat.hom_ofHom, RingHom.finite_algebraMap]
  rfl

/-- Combined genuine global finite/reduced criterion. -/
theorem finite_reduced_iff [M.IsQuasicoherent] {ι : Type v} [Finite ι]
    (U : ι → X.affineOpens) (hU : (⨆ i, (U i).val) = ⊤) :
    (IsFinite (toBase φ K) ∧ AlgebraicGeometry.IsReduced (zeroScheme φ)) ↔
      (∀ i, Module.Finite K (Γ(X, U i) ⧸ sectionIdeal φ (U i))) ∧
        (∀ i, _root_.IsReduced (Γ(X, U i) ⧸ sectionIdeal φ (U i))) := by
  rw [finite_iff φ K U hU, reduced_iff φ U hU]

end BaseField
end PaperVerification.Segre.SectionZeroScheme

end SegreSectionZeroScheme

end
end

/-! Future-only kernel audit for one exported mathematical stage.

Append to the stage being checked, with Lean.Util.CollectAxioms available through
both `public import Lean.Util.CollectAxioms` and `import all Lean.Util.CollectAxioms`
in that stage's header, as required by the reviewed FullFlattenedAudit.

Every new declaration in the checked kernel environment is included: public,
private, generated and vendored declarations receive the same direct-sorry and
transitive-axiom checks. This is evidence for this stage only. Later principal
theorems need not exist yet, and the final full principal audit remains required.

This preparation does not execute the audit, export a module or alter a proof.
-/

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  unless env.header.trustLevel == 0 do
    throwError "The stage kernel audit requires kernel trust level zero"
  let names := (env.checked.get.constants.foldStage2
    (fun (names : Array Name) name _ => names.push name) #[]).qsort Name.quickLt
  unless names.size > 0 do throwError "The stage mathematical module is empty"
  -- Reject direct proof holes before computing transitive axiom closures.
  -- The complete successful audit below remains unchanged.
  for name in names do
    let some info := env.checked.get.find? name
      | throwError "Authored declaration is not kernel checked: {name}"
    if let .axiomInfo _ := info then throwError "Authored axiom: {name}"
    if info.type.hasSorry || ((info.value? (allowOpaque := true)).any (·.hasSorry)) then
      throwError "Authored declaration contains a sorry expression: {name}"
  let privateEnv := env.setExporting false
  let importedAxioms := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  -- Match Lean's ordinary export audit, sharing its traversal cache across names.
  let axiomRows := CollectAxioms.runM privateEnv do
    names.mapM fun name =>
      return (name, ← CollectAxioms.collectAndGet importedAxioms.find? name)
  let mut theoremCount : Nat := 0
  for (name, axioms) in axiomRows do
    let some info := env.checked.get.find? name
      | throwError "Authored declaration is not kernel checked: {name}"
    if let .axiomInfo _ := info then throwError "Authored axiom: {name}"
    if info.type.hasSorry || ((info.value? (allowOpaque := true)).any (·.hasSorry)) then
      throwError "Authored declaration contains a sorry expression: {name}"
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved transitive axiom in {name}: {ax}"
    if let .thmInfo _ := info then
      theoremCount := theoremCount + 1
  let report := Json.mkObj [
    ("main_module", toJson env.header.mainModule.toString),
    ("declaration_count", toJson names.size),
    ("theorem_count", toJson theoremCount),
    ("trust_level", toJson env.header.trustLevel.toNat),
    ("allowed_axioms", toJson #["propext", "Classical.choice", "Quot.sound"]),
    ("audit_scope", toJson "current_stage_new_declarations")]
  logInfo m!"SEGRE_STAGE_KERNEL_AUDIT_PASS {report.compress}"
