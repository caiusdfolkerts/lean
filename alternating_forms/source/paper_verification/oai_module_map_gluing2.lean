module

public import paper_verification.oai_base001_run2
import all paper_verification.oai_base001_run2
public import paper_verification.oai_base002_run3
import all paper_verification.oai_base002_run3
public import paper_verification.oai_base000_run4
import all paper_verification.oai_base000_run4
public import Mathlib.CategoryTheory.Sites.SheafHom
import all Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.CategoryTheory.Sites.Subsheaf
import all Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.Topology.Sheaves.Sheaf
import all Mathlib.Topology.Sheaves.Sheaf
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

@[expose] public section ComponentSource_0
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.BasisIsomorphisms -/

/-! # Basis Isomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module

noncomputable section

/-! Module maps are determined on a basis, and compatible isomorphisms on a basis extend to an isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u v

variable {X : Scheme.{u}} {ι : Type v} (B : ι → X.Opens)
variable (hB : Opens.IsBasis (Set.range B)) {M N : X.Modules}

include hB in
theorem BasisIsomorphisms.moduleMap_eq_of_basis (f g : M ⟶ N)
    (h : ∀ i, f.app (B i) = g.app (B i)) : f = g := by
  apply (Scheme.Modules.toPresheaf X).map_injective
  exact TopCat.Sheaf.hom_ext M.presheaf ⟨N.presheaf, N.isSheaf⟩ hB h

theorem MapBasisExtension.ModuleBasisMap.extend_unique (D : MapBasisExtension.ModuleBasisMap B M N) (f : M ⟶ N)
    (hf : ∀ i (s : Γ(M, B i)), f.app (B i) s = D.app i s) : f = D.extend hB := by
  apply BasisIsomorphisms.moduleMap_eq_of_basis B hB
  intro i
  apply ConcreteCategory.hom_ext
  intro s
  exact (hf i s).trans (D.extend_app hB i s).symm

theorem MapBasisExtension.ModuleBasisMap.extend_isIso (D : MapBasisExtension.ModuleBasisMap B M N)
    (hD : ∀ i, Function.Bijective (D.app i)) : IsIso (D.extend hB) := by
  let f : (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) ⟶
      (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) :=
    ⟨(D.extend hB).mapPresheaf⟩
  have hf : IsIso f := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis hB
    intro i
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    have hi : (fun s : Γ(M, B i) => f.hom.app (.op (B i)) s) = D.app i := by
      funext s
      exact D.extend_app hB i s
    change Function.Bijective (fun s : Γ(M, B i) => f.hom.app (.op (B i)) s)
    rw [hi]
    exact hD i
  have : IsIso ((TopCat.Sheaf.forget AddCommGrpCat.{u} X).map f) :=
    @Functor.map_isIso _ _ _ _ _ _ (TopCat.Sheaf.forget AddCommGrpCat.{u} X) f hf
  have : IsIso ((Scheme.Modules.toPresheaf X).map (D.extend hB)) :=
    inferInstanceAs (IsIso ((TopCat.Sheaf.forget AddCommGrpCat.{u} X).map f))
  exact isIso_of_reflects_iso (D.extend hB) (Scheme.Modules.toPresheaf X)

def MapBasisExtension.ModuleBasisMap.extendIso (D : MapBasisExtension.ModuleBasisMap B M N)
    (hD : ∀ i, Function.Bijective (D.app i)) : M ≅ N :=
  @asIso X.Modules _ M N (D.extend hB) (D.extend_isIso B hB hD)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.BasisIsomorphisms"

@[expose] public section ComponentSource_1
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.OpenMapGluing -/

/-! # Open Map Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.OpenMapGluing

noncomputable section

/-! Glue module maps on an open cover using their compatible ambient section values. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u v

variable {X : Scheme.{u}} {M N : X.Modules}

def moduleMapOnOpen (U : X.Opens) (φ : M.restrict U.ι ⟶ N.restrict U.ι)
    (V : X.Opens) (h : V ≤ U) : Γ(M, V) →ₗ[Γ(X, V)] Γ(N, V) :=
  OpenModule.MapValues.openModuleMapValue U.ι φ V (by simpa only [U.opensRange_ι] using h)

variable {ι : Type v} (U : ι → X.Opens)

abbrev SubordinateOpenIndex := {V : X.Opens // ∃ i, V ≤ U i}

def subordinateOpenBasis : SubordinateOpenIndex U → X.Opens := Subtype.val

theorem subordinateOpenBasis_isBasis (hU : ∀ x : X, ∃ i, x ∈ U i) :
    Opens.IsBasis (Set.range (subordinateOpenBasis U)) := by
  rw [Opens.isBasis_iff_nbhd]
  intro V x hx
  obtain ⟨i, hxi⟩ := hU x
  exact ⟨V ⊓ U i, ⟨⟨V ⊓ U i, i, inf_le_right⟩, rfl⟩, ⟨hx, hxi⟩, inf_le_left⟩

structure OpenCoverModuleMaps (M N : X.Modules) where
  localMap : ∀ i, M.restrict (U i).ι ⟶ N.restrict (U i).ι
  agree : ∀ i j (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j),
    moduleMapOnOpen (U i) (localMap i) V hi = moduleMapOnOpen (U j) (localMap j) V hj

namespace OpenCoverModuleMaps

variable {U} (D : OpenCoverModuleMaps U M N)

def basisMap : MapBasisExtension.ModuleBasisMap (subordinateOpenBasis U) M N where
  app V := moduleMapOnOpen (U (Classical.choose V.property))
    (D.localMap (Classical.choose V.property)) V.val (Classical.choose_spec V.property)
  naturality V W h s := by
    have hv := Classical.choose_spec V.property
    have hw := Classical.choose_spec W.property
    change moduleMapOnOpen _ _ V.val hv (M.presheaf.map (homOfLE h).op s) = _
    rw [D.agree (Classical.choose V.property) (Classical.choose W.property) V.val hv (h.trans hw)]
    exact OpenModule.MapValues.openModuleMapValue_natural _ _ h _ _ s

variable (hU : ∀ x : X, ∃ i, x ∈ U i)

def glue : M ⟶ N := D.basisMap.extend (subordinateOpenBasis_isBasis U hU)

theorem glue_app (i : ι) (V : X.Opens) (hi : V ≤ U i) (s : Γ(M, V)) :
    (D.glue hU).app V s = moduleMapOnOpen (U i) (D.localMap i) V hi s := by
  let W : SubordinateOpenIndex U := ⟨V, i, hi⟩
  have h := D.basisMap.extend_app (subordinateOpenBasis_isBasis U hU) W s
  exact h.trans (LinearMap.congr_fun
    (D.agree (Classical.choose W.property) i V (Classical.choose_spec W.property) hi) s)

theorem glue_restrict (i : ι) :
    (Scheme.Modules.restrictFunctor (U i).ι).map (D.glue hU) = D.localMap i := by
  apply OpenModule.MapRecovery.openModuleMapValue_injective (U i).ι
  intro V hV
  rw [OpenModule.MapValues.openModuleMapValue_from_global]
  apply LinearMap.ext
  intro s
  have hi : V ≤ U i := by simpa only [(U i).opensRange_ι] using hV
  exact D.glue_app hU i V hi s

theorem glue_unique (φ : M ⟶ N)
    (hφ : ∀ i, (Scheme.Modules.restrictFunctor (U i).ι).map φ = D.localMap i) : φ = D.glue hU := by
  apply BasisIsomorphisms.moduleMap_eq_of_basis (subordinateOpenBasis U) (subordinateOpenBasis_isBasis U hU)
  intro V
  apply ConcreteCategory.hom_ext
  intro s
  obtain ⟨i, hi⟩ := V.property
  have hv := congrArg (fun ψ => moduleMapOnOpen (U i) ψ V.val hi s) (hφ i)
  have hglobal : moduleMapOnOpen (U i) ((Scheme.Modules.restrictFunctor (U i).ι).map φ) V.val hi s =
      φ.app V.val s := LinearMap.congr_fun (OpenModule.MapValues.openModuleMapValue_from_global (U i).ι φ V.val _) s
  exact hglobal.symm.trans (hv.trans (D.glue_app hU i V.val hi s).symm)

end OpenCoverModuleMaps

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.OpenMapGluing
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.OpenMapGluing"

@[expose] public section ComponentSource_2
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapCoverEquality -/

/-! # Map Cover Equality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapCoverEquality

noncomputable section

/-! Equality of module-sheaf maps can be checked after restriction or canonical pullback on an open cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} {M N : X.Modules} {ι : Type v} (U : ι → X.Opens)
variable (hU : ∀ x : X, ∃ i, x ∈ U i)

include hU

theorem moduleMap_eq_of_restrict_cover (φ ψ : M ⟶ N)
    (h : ∀ i, (Scheme.Modules.restrictFunctor (U i).ι).map φ =
      (Scheme.Modules.restrictFunctor (U i).ι).map ψ) : φ = ψ := by
  apply BasisIsomorphisms.moduleMap_eq_of_basis (OpenMapGluing.subordinateOpenBasis U) (OpenMapGluing.subordinateOpenBasis_isBasis U hU)
  intro V
  obtain ⟨i, hi⟩ := V.property
  have hv := congrArg (fun a => OpenMapGluing.moduleMapOnOpen (U i) a V.val hi) (h i)
  apply ConcreteCategory.hom_ext
  intro s
  have hφ : OpenMapGluing.moduleMapOnOpen (U i) ((Scheme.Modules.restrictFunctor (U i).ι).map φ) V.val hi s =
      φ.app V.val s := LinearMap.congr_fun (OpenModule.MapValues.openModuleMapValue_from_global (U i).ι φ V.val _) s
  have hψ : OpenMapGluing.moduleMapOnOpen (U i) ((Scheme.Modules.restrictFunctor (U i).ι).map ψ) V.val hi s =
      ψ.app V.val s := LinearMap.congr_fun (OpenModule.MapValues.openModuleMapValue_from_global (U i).ι ψ V.val _) s
  exact hφ.symm.trans ((LinearMap.congr_fun hv s).trans hψ)

theorem moduleMap_eq_of_pullback_cover (φ ψ : M ⟶ N)
    (h : ∀ i, (Scheme.Modules.pullback (U i).ι).map φ =
      (Scheme.Modules.pullback (U i).ι).map ψ) : φ = ψ := by
  apply moduleMap_eq_of_restrict_cover U hU
  intro i
  let E := Scheme.Modules.restrictFunctorIsoPullback (U i).ι
  apply (cancel_mono (E.app N).hom).mp
  exact (E.hom.naturality φ).trans
    ((congrArg (fun a => (E.app M).hom ≫ a) (h i)).trans (E.hom.naturality ψ).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapCoverEquality
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapCoverEquality"

@[expose] public section ComponentSource_3
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.EndRecovery -/

/-! Canonical pullback/restriction comparison for arbitrary module-sheaf maps.
The two generic lemmas are retained verbatim from the pinned upstream file;
line-bundle scalar-transfer applications are not needed by map gluing. -/
namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
noncomputable section
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}}

theorem LineBundle.EndRecovery.pullbackModuleRestrictionMap_injective (f : X ⟶ Y) [IsOpenImmersion f]
    (M N : Y.Modules) : Function.Injective (OpenPullback.ModuleValues.pullbackModuleRestrictionMap f (M := M) (N := N)) := by
  intro φ ψ h
  unfold OpenPullback.ModuleValues.pullbackModuleRestrictionMap at h
  exact (cancel_epi ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M)).mp
    ((cancel_mono ((Scheme.Modules.restrictFunctorIsoPullback f).inv.app N)).mp
      (by simpa only [Category.assoc] using h))

theorem LineBundle.EndRecovery.pullbackModuleRestrictionMap_global (f : X ⟶ Y) [IsOpenImmersion f]
    {M N : Y.Modules} (φ : M ⟶ N) :
    OpenPullback.ModuleValues.pullbackModuleRestrictionMap f ((Scheme.Modules.pullback f).map φ) =
      (Scheme.Modules.restrictFunctor f).map φ := by
  unfold OpenPullback.ModuleValues.pullbackModuleRestrictionMap
  rw [← Category.assoc, ← (Scheme.Modules.restrictFunctorIsoPullback f).hom.naturality φ,
    Category.assoc, (Scheme.Modules.restrictFunctorIsoPullback f).hom_inv_id_app, Category.comp_id]

end
end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
end ComponentSource_3

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.EndRecovery"

@[expose] public section ComponentSource_4
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.MapGluing -/

/-! # Map Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.MapGluing

noncomputable section

/-! Compatible maps between canonical module pullbacks glue on an open cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} {ι : Type v} (U : ι → X.Opens) (M N : X.Modules)

structure OpenPullbackModuleMaps where
  localMap : ∀ i, (Scheme.Modules.pullback (U i).ι).obj M ⟶
    (Scheme.Modules.pullback (U i).ι).obj N
  agree : ∀ i j (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j),
    Module.MapSlicePullback.moduleMapPullbackAlong (OpenModule.MapRefinement.openSubsetOverMap hi) (localMap i) =
      Module.MapSlicePullback.moduleMapPullbackAlong (OpenModule.MapRefinement.openSubsetOverMap hj) (localMap j)

namespace OpenPullbackModuleMaps

variable {U M N} (D : OpenPullbackModuleMaps U M N)

def restrictionData : Module.OpenMapGluing.OpenCoverModuleMaps U M N where
  localMap i := ModuleValues.pullbackModuleRestrictionMap (U i).ι (D.localMap i)
  agree i j V hi hj := by
    have hi' : V ≤ (U i).ι.opensRange := by rwa [(U i).opensRange_ι]
    have hj' : V ≤ (U j).ι.opensRange := by rwa [(U j).opensRange_ι]
    have hV : V ≤ V.ι.opensRange := by rw [V.opensRange_ι]
    exact (ModuleValues.openPullbackModuleValue_restriction (U i).ι (D.localMap i) V hi').trans
      ((OpenModule.MapRefinement.openPullbackModuleValue_refine hi (D.localMap i)).symm.trans
        ((congrArg (fun φ => ModuleValues.openPullbackModuleValue V.ι φ V hV) (D.agree i j V hi hj)).trans
          ((OpenModule.MapRefinement.openPullbackModuleValue_refine hj (D.localMap j)).trans
            (ModuleValues.openPullbackModuleValue_restriction (U j).ι (D.localMap j) V hj').symm)))

def glue (hU : ∀ x : X, ∃ i, x ∈ U i) : M ⟶ N := D.restrictionData.glue hU

theorem glue_pullback (hU : ∀ x : X, ∃ i, x ∈ U i) (i : ι) :
    (Scheme.Modules.pullback (U i).ι).map (D.glue hU) = D.localMap i := by
  apply LineBundle.EndRecovery.pullbackModuleRestrictionMap_injective (U i).ι M N
  rw [LineBundle.EndRecovery.pullbackModuleRestrictionMap_global]
  exact D.restrictionData.glue_restrict hU i

theorem glue_unique (hU : ∀ x : X, ∃ i, x ∈ U i) (φ : M ⟶ N)
    (hφ : ∀ i, (Scheme.Modules.pullback (U i).ι).map φ = D.localMap i) : φ = D.glue hU := by
  apply Module.MapCoverEquality.moduleMap_eq_of_pullback_cover U hU
  intro i
  exact (hφ i).trans (D.glue_pullback hU i).symm

theorem existsUnique_glue (hU : ∀ x : X, ∃ i, x ∈ U i) :
    ∃! φ : M ⟶ N, ∀ i, (Scheme.Modules.pullback (U i).ι).map φ = D.localMap i :=
  ⟨D.glue hU, D.glue_pullback hU, D.glue_unique hU⟩

end OpenPullbackModuleMaps

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.MapGluing
end ComponentSource_4

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.MapGluing"

@[expose] public section ComponentSource_5
/- Original module: OAI.AlgebraicGeometry.Picard.Homomorphisms.ModuleHomSheaf -/

/-! # Module Hom Sheaf -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.ModuleHomSheaf

noncomputable section

/-! The sheaf of locally defined linear maps between actual module sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X : Scheme.{u}} (M N : X.Modules)

def IsLinearLocalHom {U : X.Opens}
    (a : (presheafHom M.presheaf N.presheaf).obj (.op U)) : Prop :=
  ∀ (V : Over U) (r : Γ(X, V.left)) (s : Γ(M, V.left)),
    a.app (.op V) (r • s) = r • (show Γ(N, V.left) from a.app (.op V) s)

def linearHomSubfunctor : Subfunctor (presheafHom M.presheaf N.presheaf) where
  obj U := {a | IsLinearLocalHom M N a}
  map {U V} f a ha := by
    intro W r s
    exact ha ((Over.map f.unop).obj W) r s

theorem linearHomSubfunctor_isSheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (linearHomSubfunctor M N).toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type]
  apply ((linearHomSubfunctor M N).isSheaf_iff
    ((isSheaf_iff_isSheaf_of_type _ _).mp (N.isSheaf.hom M.presheaf))).mpr
  intro U a ha V r s
  apply N.isSheaf.section_ext
  intro x hx
  obtain ⟨W, i, hi, hxW⟩ := ha x ((leOfHom V.hom) hx)
  let Z := V.left ⊓ W
  let z : Over U.unop := Over.mk (homOfLE (show Z ≤ U.unop from
    inf_le_left.trans (leOfHom V.hom)))
  let j : z ⟶ V := Over.homMk (homOfLE (show Z ≤ V.left from inf_le_left))
  have hn (t : Γ(M, V.left)) := ConcreteCategory.congr_hom (a.naturality j.op) t
  change ∀ t : Γ(M, V.left),
    a.app (.op z) (M.presheaf.map (homOfLE (show Z ≤ V.left from inf_le_left)).op t) =
      N.presheaf.map (homOfLE (show Z ≤ V.left from inf_le_left)).op (a.app (.op V) t) at hn
  have hl := hi (Over.mk (homOfLE (show Z ≤ W from inf_le_right)))
    (X.presheaf.map (homOfLE (show Z ≤ V.left from inf_le_left)).op r)
    (M.presheaf.map (homOfLE (show Z ≤ V.left from inf_le_left)).op s)
  refine ⟨Z, inf_le_left, ⟨hx, hxW⟩, ?_⟩
  change N.presheaf.map (homOfLE (show Z ≤ V.left from inf_le_left)).op
      (a.app (.op V) (r • s)) =
    N.presheaf.map (homOfLE (show Z ≤ V.left from inf_le_left)).op
      (r • (show Γ(N, V.left) from a.app (.op V) s))
  have hsm := N.val.map_smul (homOfLE (show Z ≤ V.left from inf_le_left)).op r
    (a.app (.op V) s)
  change N.presheaf.map (homOfLE (show Z ≤ V.left from inf_le_left)).op
      (r • (show Γ(N, V.left) from a.app (.op V) s)) = _ at hsm
  erw [hsm, ← hn (r • s), ← hn s]
  erw [M.val.map_smul]
  exact hl

/-- Local module homomorphisms form a genuine sheaf, before any sheafification. -/
def linearHomSheaf : TopCat.Sheaf (Type u) X :=
  ⟨(linearHomSubfunctor M N).toFunctor, linearHomSubfunctor_isSheaf M N⟩

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.ModuleHomSheaf
end ComponentSource_5

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Picard.Homomorphisms.ModuleHomSheaf"


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
    (`OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.MapGluing.OpenPullbackModuleMaps.existsUnique_glue, "theorem")
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
    ("nonce", toJson "81bc052f3e92cd447c813639d295961e"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:81bc052f3e92cd447c813639d295961e"
