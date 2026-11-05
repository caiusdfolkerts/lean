module

public import paper_verification.oai_base001_run2
import all paper_verification.oai_base001_run2
public import paper_verification.oai_base000_run4
import all paper_verification.oai_base000_run4
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

@[expose] public section ComponentSource_0
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.Refinement -/

/-! # Refinement -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.Refinement

noncomputable section

/-! Comparison maps from one open pullback to a refined open pullback, preserving adjunction units. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [IsOpenImmersion f] [IsOpenImmersion g]

def openPullbackRefinementMap (N : Z.Modules) :
    (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj N) ⟶
      (Scheme.Modules.pushforward (f ≫ g)).obj ((Scheme.Modules.pullback (f ≫ g)).obj N) :=
  (Scheme.Modules.pushforward g).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app ((Scheme.Modules.pullback g).obj N)) ≫
    (Scheme.Modules.pushforward g).map ((Scheme.Modules.pushforward f).map
      ((Scheme.Modules.pullbackComp f g).hom.app N)) ≫
    (Scheme.Modules.pushforwardComp f g).hom.app ((Scheme.Modules.pullback (f ≫ g)).obj N)

omit [IsOpenImmersion f] [IsOpenImmersion g] in
theorem openPullbackRefinementMap_unit (N : Z.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N ≫ openPullbackRefinementMap f g N =
      (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app N :=
  Pullback.TensorCompositionUnits.pullbackComp_hom_unit f g N

theorem preimage_le_openRange_of_comp {U : Z.Opens} (hU : U ≤ (f ≫ g).opensRange) :
    g ⁻¹ᵁ U ≤ f.opensRange := by
  have h : g ⁻¹ᵁ U ≤ g ⁻¹ᵁ (f ≫ g).opensRange := fun x hx => hU hx
  rwa [Scheme.Hom.opensRange_comp, g.preimage_image_eq] at h

theorem openPullbackRefinementMap_app_isIso (N : Z.Modules) (U : Z.Opens)
    (hU : U ≤ (f ≫ g).opensRange) : IsIso ((openPullbackRefinementMap f g N).app U) := by
  have h₁ : IsIso (((Scheme.Modules.pushforward g).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        ((Scheme.Modules.pullback g).obj N))).app U) :=
    ModuleValues.openPullbackUnit_app_isIso f ((Scheme.Modules.pullback g).obj N) (g ⁻¹ᵁ U)
      (preimage_le_openRange_of_comp f g hU)
  let := h₁
  change IsIso (((Scheme.Modules.pushforward g).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app ((Scheme.Modules.pullback g).obj N))).app U ≫
    ((Scheme.Modules.pushforward g).map ((Scheme.Modules.pushforward f).map
      ((Scheme.Modules.pullbackComp f g).hom.app N))).app U ≫
      ((Scheme.Modules.pushforwardComp f g).hom.app ((Scheme.Modules.pullback (f ≫ g)).obj N)).app U)
  infer_instance

def refineOpenPullbackMap {M N : Z.Modules}
    (φ : (Scheme.Modules.pullback g).obj M ⟶ (Scheme.Modules.pullback g).obj N) :
    (Scheme.Modules.pullback (f ≫ g)).obj M ⟶ (Scheme.Modules.pullback (f ≫ g)).obj N :=
  (Scheme.Modules.pullbackComp f g).inv.app M ≫ (Scheme.Modules.pullback f).map φ ≫
    (Scheme.Modules.pullbackComp f g).hom.app N

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.Refinement
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.Refinement"

@[expose] public section ComponentSource_1
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.RefinementNaturality -/

/-! # Refinement Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.RefinementNaturality

noncomputable section

/-! Refining a canonical open pullback preserves the ambient values of every local module map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [IsOpenImmersion f] [IsOpenImmersion g] {M N : Z.Modules}
variable (φ : (Scheme.Modules.pullback g).obj M ⟶ (Scheme.Modules.pullback g).obj N)

omit [IsOpenImmersion f] [IsOpenImmersion g] in
theorem openPullbackRefinementMap_natural :
    (Scheme.Modules.pushforward g).map φ ≫ Refinement.openPullbackRefinementMap f g N =
      Refinement.openPullbackRefinementMap f g M ≫
        (Scheme.Modules.pushforward (f ≫ g)).map (Refinement.refineOpenPullbackMap f g φ) := by
  have he : (Scheme.Modules.pullbackComp f g).hom.app M ≫ Refinement.refineOpenPullbackMap f g φ =
      (Scheme.Modules.pullback f).map φ ≫ (Scheme.Modules.pullbackComp f g).hom.app N := by
    exact ((Scheme.Modules.pullbackComp f g).app M).hom_inv_id_assoc _
  have hn : (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app ((Scheme.Modules.pullback g).obj M) ≫
      (Scheme.Modules.pushforward f).map ((Scheme.Modules.pullback f).map φ) =
      φ ≫ (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app ((Scheme.Modules.pullback g).obj N) :=
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality φ).symm
  symm
  dsimp only [Refinement.openPullbackRefinementMap]
  simp only [Category.assoc]
  rw [← (Scheme.Modules.pushforwardComp f g).hom.naturality (Refinement.refineOpenPullbackMap f g φ)]
  change (Scheme.Modules.pushforward g).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app ((Scheme.Modules.pullback g).obj M)) ≫
    (Scheme.Modules.pushforward g).map ((Scheme.Modules.pushforward f).map
      ((Scheme.Modules.pullbackComp f g).hom.app M)) ≫
    (Scheme.Modules.pushforward g).map ((Scheme.Modules.pushforward f).map (Refinement.refineOpenPullbackMap f g φ)) ≫ _ = _
  rw [← Category.assoc ((Scheme.Modules.pushforward g).map ((Scheme.Modules.pushforward f).map
    ((Scheme.Modules.pullbackComp f g).hom.app M))), ← Functor.map_comp, ← Functor.map_comp, he]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.pushforward g).map
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app ((Scheme.Modules.pullback g).obj M))),
    ← Functor.map_comp, hn,
    Functor.map_comp, Category.assoc]

theorem openPullbackModuleValue_comp (U : Z.Opens) (hU : U ≤ (f ≫ g).opensRange) :
    ModuleValues.openPullbackModuleValue (f ≫ g) (Refinement.refineOpenPullbackMap f g φ) U hU =
      ModuleValues.openPullbackModuleValue g φ U (hU.trans (by
        rw [Scheme.Hom.opensRange_comp]
        exact g.image_le_opensRange f.opensRange)) := by
  have hg : U ≤ g.opensRange := hU.trans (by
    rw [Scheme.Hom.opensRange_comp]
    exact g.image_le_opensRange f.opensRange)
  let := ModuleValues.openPullbackUnit_app_isIso g N U hg
  let := ModuleValues.openPullbackUnit_app_isIso (f ≫ g) N U hU
  have hα : ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M ≫
      (Scheme.Modules.pushforward g).map φ) ≫ Refinement.openPullbackRefinementMap f g N =
      (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M ≫
        (Scheme.Modules.pushforward (f ≫ g)).map (Refinement.refineOpenPullbackMap f g φ) := by
    rw [Category.assoc, openPullbackRefinementMap_natural, ← Category.assoc,
      Refinement.openPullbackRefinementMap_unit]
  exact (Module.MapFactorTransport.moduleMapLocalFactor_transport _ _ (Refinement.openPullbackRefinementMap f g N) _ _ hα
    (Refinement.openPullbackRefinementMap_unit f g N) U).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.RefinementNaturality
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.RefinementNaturality"

@[expose] public section ComponentSource_2
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapRefinement -/

/-! # Map Refinement -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapRefinement

noncomputable section

/-! Ambient values of module maps are unchanged under refinement of open subsets. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem openPullbackModuleValue_congr {X Y : Scheme.{u}} {f g : X ⟶ Y}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) {M N : Y.Modules}
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    (U : Y.Opens) (hf : U ≤ f.opensRange) (hg : U ≤ g.opensRange) :
    OpenPullback.ModuleValues.openPullbackModuleValue g (Module.MapPullbackCongruence.moduleMapPullbackCongr h φ) U hg =
      OpenPullback.ModuleValues.openPullbackModuleValue f φ U hf := by
  subst g
  rfl

def openSubsetOver {X : Scheme.{u}} (U : X.Opens) : Over X := Over.mk U.ι

def openSubsetOverMap {X : Scheme.{u}} {U V : X.Opens} (h : U ≤ V) :
    openSubsetOver U ⟶ openSubsetOver V := Over.homMk (X.homOfLE h) (X.homOfLE_ι h)

theorem openPullbackModuleValue_refine {X : Scheme.{u}} {M N : X.Modules}
    {U V : X.Opens} (h : U ≤ V)
    (φ : (Scheme.Modules.pullback V.ι).obj M ⟶ (Scheme.Modules.pullback V.ι).obj N) :
    OpenPullback.ModuleValues.openPullbackModuleValue U.ι (Module.MapSlicePullback.moduleMapPullbackAlong (openSubsetOverMap h) φ) U
        (by rw [U.opensRange_ι]) =
      OpenPullback.ModuleValues.openPullbackModuleValue V.ι φ U (by rwa [V.opensRange_ι]) := by
  have hc : U ≤ (X.homOfLE h ≫ V.ι).opensRange := by
    intro x hx
    change ∃ y : U.toScheme, (X.homOfLE h ≫ V.ι) y = x
    exact ⟨⟨x, hx⟩, congrArg (fun k : U.toScheme ⟶ X => k ⟨x, hx⟩) (X.homOfLE_ι h)⟩
  exact (openPullbackModuleValue_congr (X.homOfLE_ι h)
    (Module.MapPullbackComposition.moduleMapPullbackComp (X.homOfLE h) V.ι φ) U hc _).trans
      (OpenPullback.RefinementNaturality.openPullbackModuleValue_comp (X.homOfLE h) V.ι φ U hc)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapRefinement
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapRefinement"

@[expose] public section ComponentSource_3
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.CechObjectDescent -/

/-! # Cech Object Descent -/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.CechObjectDescent

noncomputable section

/-! Native pullback isomorphisms on open intersections give the actual
matching-section line object. Compatibility is measured by the existing
canonical module pullback, so this adapter retains all pullback paths. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {X Y : Scheme.{u}}

def openPullbackIsoValue (f : Y ⟶ X) [IsOpenImmersion f] {M N : X.Modules}
    (e : (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback f).obj N)
    (U : X.Opens) (hU : U ≤ f.opensRange) : Γ(M, U) ≃ₗ[Γ(X, U)] Γ(N, U) :=
  OpenModule.IsoValues.openModuleIsoValue f
    ((Scheme.Modules.restrictFunctorIsoPullback f).app M ≪≫ e ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback f).symm.app N) U hU

theorem openPullbackIsoValue_apply (f : Y ⟶ X) [IsOpenImmersion f] {M N : X.Modules}
    (e : (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback f).obj N)
    (U : X.Opens) (hU : U ≤ f.opensRange) (s : Γ(M, U)) :
    openPullbackIsoValue f e U hU s = ModuleValues.openPullbackModuleValue f e.hom U hU s :=
  LinearMap.congr_fun (ModuleValues.openPullbackModuleValue_restriction f e.hom U hU) s

theorem openPullbackModuleValue_natural (f : Y ⟶ X) [IsOpenImmersion f] {M N : X.Modules}
    (a : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    {U V : X.Opens} (h : V ≤ U) (hU : U ≤ f.opensRange) (hV : V ≤ f.opensRange)
    (s : Γ(M, U)) :
    ModuleValues.openPullbackModuleValue f a V hV (M.presheaf.map (homOfLE h).op s) =
      N.presheaf.map (homOfLE h).op (ModuleValues.openPullbackModuleValue f a U hU s) := by
  rw [← ModuleValues.openPullbackModuleValue_restriction, ← ModuleValues.openPullbackModuleValue_restriction]
  exact OpenModule.MapValues.openModuleMapValue_natural f (ModuleValues.pullbackModuleRestrictionMap f a) h hU hV s

theorem openPullbackModuleValue_identity (f : Y ⟶ X) [IsOpenImmersion f] (M : X.Modules)
    (U : X.Opens) (hU : U ≤ f.opensRange) (s : Γ(M, U)) :
    ModuleValues.openPullbackModuleValue f (𝟙 ((Scheme.Modules.pullback f).obj M)) U hU s = s := by
  rw [← ModuleValues.openPullbackModuleValue_restriction]
  have he : ModuleValues.pullbackModuleRestrictionMap f (𝟙 ((Scheme.Modules.pullback f).obj M)) =
      𝟙 (M.restrict f) := by
    simp only [ModuleValues.pullbackModuleRestrictionMap, Category.id_comp, Iso.hom_inv_id_app]
  rw [he]
  exact OpenModule.MapValueFunctoriality.openModuleMapValue_identity f M U hU s

theorem openPullbackModuleValue_hom_comp (f : Y ⟶ X) [IsOpenImmersion f] {M N P : X.Modules}
    (a : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    (b : (Scheme.Modules.pullback f).obj N ⟶ (Scheme.Modules.pullback f).obj P)
    (U : X.Opens) (hU : U ≤ f.opensRange) (s : Γ(M, U)) :
    ModuleValues.openPullbackModuleValue f (a ≫ b) U hU s =
      ModuleValues.openPullbackModuleValue f b U hU (ModuleValues.openPullbackModuleValue f a U hU s) := by
  have hc : ModuleValues.pullbackModuleRestrictionMap f (a ≫ b) =
      ModuleValues.pullbackModuleRestrictionMap f a ≫ ModuleValues.pullbackModuleRestrictionMap f b := by
    simp only [ModuleValues.pullbackModuleRestrictionMap, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← ModuleValues.openPullbackModuleValue_restriction, hc, OpenModule.MapValueFunctoriality.openModuleMapValue_hom_comp,
    ModuleValues.openPullbackModuleValue_restriction, ModuleValues.openPullbackModuleValue_restriction]

theorem openPullbackModuleValue_refine_on {U V : X.Opens} (h : U ≤ V)
    {M N : X.Modules}
    (a : (Scheme.Modules.pullback V.ι).obj M ⟶ (Scheme.Modules.pullback V.ι).obj N)
    (W : X.Opens) (hW : W ≤ U) :
    ModuleValues.openPullbackModuleValue U.ι (Module.MapSlicePullback.moduleMapPullbackAlong (OpenModule.MapRefinement.openSubsetOverMap h) a) W
        (by simpa only [Scheme.Opens.opensRange_ι] using hW) =
      ModuleValues.openPullbackModuleValue V.ι a W
        (by simpa only [Scheme.Opens.opensRange_ι] using hW.trans h) := by
  have hUV : W ≤ (X.homOfLE h ≫ V.ι).opensRange := by
    simpa only [X.homOfLE_ι h, Scheme.Opens.opensRange_ι] using hW
  exact (OpenModule.MapRefinement.openPullbackModuleValue_congr (X.homOfLE_ι h)
    (Module.MapPullbackComposition.moduleMapPullbackComp (X.homOfLE h) V.ι a) W hUV _).trans
      (RefinementNaturality.openPullbackModuleValue_comp (X.homOfLE h) V.ι a W hUV)

structure OpenPullbackCechIsos {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (M : ι → X.Modules) where
  iso : ∀ i j, (Scheme.Modules.pullback (U i ⊓ U j).ι).obj (M i) ≅
    (Scheme.Modules.pullback (U i ⊓ U j).ι).obj (M j)
  identity : ∀ i, iso i i = Iso.refl _
  cocycle : ∀ i j k,
    Module.MapSlicePullback.moduleMapPullbackAlong (OpenModule.MapRefinement.openSubsetOverMap
      (show (U i ⊓ U j) ⊓ U k ≤ U i ⊓ U j from inf_le_left)) (iso i j).hom ≫
    Module.MapSlicePullback.moduleMapPullbackAlong (OpenModule.MapRefinement.openSubsetOverMap
      (show (U i ⊓ U j) ⊓ U k ≤ U j ⊓ U k from
        le_inf (inf_le_left.trans inf_le_right) inf_le_right)) (iso j k).hom =
    Module.MapSlicePullback.moduleMapPullbackAlong (OpenModule.MapRefinement.openSubsetOverMap
      (show (U i ⊓ U j) ⊓ U k ≤ U i ⊓ U k from
        le_inf (inf_le_left.trans inf_le_left) inf_le_right)) (iso i k).hom

namespace OpenPullbackCechIsos
variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} {M : ι → X.Modules}
  (D : OpenPullbackCechIsos U M)

def transitions : OpenModule.MatchingSheaf.OpenModuleTransitions U M where
  compare V i j hi hj := openPullbackIsoValue (U i ⊓ U j).ι (D.iso i j) V
    (by simpa only [Scheme.Opens.opensRange_ι] using le_inf hi hj)
  natural V W h i j hi hj s := by
    rw [openPullbackIsoValue_apply, openPullbackIsoValue_apply]
    exact openPullbackModuleValue_natural _ _ h _ _ s
  identity V i hi s := by
    rw [openPullbackIsoValue_apply, D.identity]
    exact openPullbackModuleValue_identity _ _ _ _ s
  composition V i j k hi hj hk s := by
    let W := (U i ⊓ U j) ⊓ U k
    have hV : V ≤ W := le_inf (le_inf hi hj) hk
    have hW : V ≤ W.ι.opensRange := by simpa only [Scheme.Opens.opensRange_ι] using hV
    let a := Module.MapSlicePullback.moduleMapPullbackAlong (OpenModule.MapRefinement.openSubsetOverMap (show W ≤ U i ⊓ U j from inf_le_left))
      (D.iso i j).hom
    let b := Module.MapSlicePullback.moduleMapPullbackAlong (OpenModule.MapRefinement.openSubsetOverMap (show W ≤ U j ⊓ U k from
      le_inf (inf_le_left.trans inf_le_right) inf_le_right)) (D.iso j k).hom
    let c := Module.MapSlicePullback.moduleMapPullbackAlong (OpenModule.MapRefinement.openSubsetOverMap (show W ≤ U i ⊓ U k from
      le_inf (inf_le_left.trans inf_le_left) inf_le_right)) (D.iso i k).hom
    have ha := openPullbackModuleValue_refine_on
      (show W ≤ U i ⊓ U j from inf_le_left) (D.iso i j).hom V hV
    have hb := openPullbackModuleValue_refine_on
      (show W ≤ U j ⊓ U k from le_inf (inf_le_left.trans inf_le_right) inf_le_right)
      (D.iso j k).hom V hV
    have hc := openPullbackModuleValue_refine_on
      (show W ≤ U i ⊓ U k from le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      (D.iso i k).hom V hV
    rw [openPullbackIsoValue_apply, openPullbackIsoValue_apply, openPullbackIsoValue_apply,
      ← ha, ← hb, ← hc]
    exact (openPullbackModuleValue_hom_comp W.ι a b V hW s).symm.trans
      (congrArg (fun t => ModuleValues.openPullbackModuleValue W.ι t V hW s) (D.cocycle i j k))

variable (hU : ∀ x : X, ∃ i, x ∈ U i) (L : ∀ i, Line.Bundles.LineBundle (U i).toScheme)
  (r : ∀ i, (M i).restrict (U i).ι ≅ (L i).sheaf)

def lineBundle : Line.Bundles.LineBundle X := D.transitions.lineBundle hU L r

def lineBundle_recovery (i : ι) :
    ((D.lineBundle hU L r).pullback (U i).ι).sheaf ≅ (L i).sheaf :=
  D.transitions.lineBundle_recovery hU L r i

end OpenPullbackCechIsos

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.CechObjectDescent
end ComponentSource_3

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.CechObjectDescent"

@[expose] public section ComponentSource_4
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.OpenModuleCech -/

/-! # Open Module Cech -/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.OpenModuleCech.IntrinsicOpenModuleCech

noncomputable section

/-! Native descent comparisons on literal open subsets, proved with
arbitrary recovered modules before specializing to open direct images. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ModuleDescentRecovery.NativeModuleDescentRecovery

def cechOfRestrictions {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (M : ι → X.Modules)
    (e : ∀ V : X.Opens, ∀ i j, V ≤ U i → V ≤ U j →
      ((Scheme.Modules.pullback V.ι).obj (M i) ≅ (Scheme.Modules.pullback V.ι).obj (M j)))
    (hid : ∀ V i (h : V ≤ U i), e V i i h h = Iso.refl _)
    (hcomp : ∀ V i j k (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k),
      (e V i j hi hj).hom ≫ (e V j k hj hk).hom = (e V i k hi hk).hom)
    (hrefine : ∀ {V W : X.Opens} (h : W ≤ V) i j (hi : V ≤ U i) (hj : V ≤ U j),
      Module.MapSlicePullback.moduleMapPullbackAlong (OpenModule.MapRefinement.openSubsetOverMap h) (e V i j hi hj).hom =
        (e W i j (h.trans hi) (h.trans hj)).hom) : OpenPullback.CechObjectDescent.OpenPullbackCechIsos U M where
  iso i j := e (U i ⊓ U j) i j inf_le_left inf_le_right
  identity i := hid (U i ⊓ U i) i inf_le_left
  cocycle i j k := by
    let V := (U i ⊓ U j) ⊓ U k
    have a := hrefine (show V ≤ U i ⊓ U j from inf_le_left) i j inf_le_left inf_le_right
    have b := hrefine (show V ≤ U j ⊓ U k from
      le_inf (inf_le_left.trans inf_le_right) inf_le_right) j k inf_le_left inf_le_right
    have c := hrefine (show V ≤ U i ⊓ U k from
      le_inf (inf_le_left.trans inf_le_left) inf_le_right) i k inf_le_left inf_le_right
    exact (congrArg₂ (fun x y => x ≫ y) a b).trans
      ((hcomp V i j k (inf_le_left.trans inf_le_left)
        (inf_le_left.trans inf_le_right) inf_le_right).trans c.symm)

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
  (D : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun i => (U i).ι))
  (M : ι → X.Modules)
  (r : ∀ i, (Scheme.Modules.pullback (U i).ι).obj (M i) ≅ D.obj i)

def onOpen (V : X.Opens) (i j : ι) (hi : V ≤ U i) (hj : V ≤ U j) :
    (Scheme.Modules.pullback V.ι).obj (M i) ≅
      (Scheme.Modules.pullback V.ι).obj (M j) :=
  ModuleDescentRecovery.NativeModuleDescentRecovery.ambientIso D M r V.ι i j
    (X.homOfLE hi) (X.homOfLE hj) (X.homOfLE_ι hi) (X.homOfLE_ι hj)

theorem onOpen_hom (V : X.Opens) (i j : ι) (hi : V ≤ U i) (hj : V ≤ U j) :
    (onOpen U D M r V i j hi hj).hom =
      (ModuleDescentRecovery.NativeModuleDescentRecovery.ambientIso D M r V.ι i j
        (X.homOfLE hi) (X.homOfLE hj) (X.homOfLE_ι hi) (X.homOfLE_ι hj)).hom := rfl

theorem openInclusion_comp {V W Z : X.Opens} (h : W ≤ V) (k : V ≤ Z) :
    X.homOfLE h ≫ X.homOfLE k = X.homOfLE (h.trans k) := by
  apply (cancel_mono Z.ι).mp
  rw [Category.assoc, X.homOfLE_ι k, X.homOfLE_ι h, X.homOfLE_ι (h.trans k)]

theorem onOpen_refine {V W : X.Opens} (h : W ≤ V) (i j : ι) (hi : V ≤ U i) (hj : V ≤ U j) :
    Module.MapSlicePullback.moduleMapPullbackAlong (OpenModule.MapRefinement.openSubsetOverMap h) (onOpen U D M r V i j hi hj).hom =
      (onOpen U D M r W i j (h.trans hi) (h.trans hj)).hom := by
  exact (ModuleDescentRecovery.moduleMapPullbackAlong_eq_pullHom (OpenModule.MapRefinement.openSubsetOverMap h)
    (onOpen U D M r V i j hi hj).hom).trans
    (ModuleDescentRecovery.NativeModuleDescentRecovery.ambientIso_pullback D M r
    (X.homOfLE h) V.ι W.ι (X.homOfLE_ι h) i j
    (X.homOfLE hi) (X.homOfLE hj) (X.homOfLE_ι hi) (X.homOfLE_ι hj)
    (X.homOfLE (h.trans hi)) (X.homOfLE (h.trans hj))
    (X.homOfLE_ι (h.trans hi)) (X.homOfLE_ι (h.trans hj))
    (openInclusion_comp h hi) (openInclusion_comp h hj))

theorem onOpen_cocycle (V : X.Opens) (i j k : ι)
    (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k) :
    (onOpen U D M r V i j hi hj).hom ≫ (onOpen U D M r V j k hj hk).hom =
      (onOpen U D M r V i k hi hk).hom := by
  have a := onOpen_hom U D M r V i j hi hj
  have b := onOpen_hom U D M r V j k hj hk
  have c := onOpen_hom U D M r V i k hi hk
  exact (congrArg₂ (fun x y => x ≫ y) a b).trans
    ((ModuleDescentRecovery.NativeModuleDescentRecovery.ambientIso_comp D M r V.ι i j k
      (X.homOfLE hi) (X.homOfLE hj) (X.homOfLE hk)
      (X.homOfLE_ι hi) (X.homOfLE_ι hj) (X.homOfLE_ι hk)).trans c.symm)

def cech : OpenPullback.CechObjectDescent.OpenPullbackCechIsos U M :=
  cechOfRestrictions U M (onOpen U D M r)
    (fun V i hi => ModuleDescentRecovery.NativeModuleDescentRecovery.ambientIso_self D M r V.ι i (X.homOfLE hi) (X.homOfLE_ι hi))
    (onOpen_cocycle U D M r) (onOpen_refine U D M r)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.OpenModuleCech.IntrinsicOpenModuleCech
end ComponentSource_4

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.OpenModuleCech"

@[expose] public section ComponentSource_5
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.ObjectDescent -/

/-! # Object Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.ObjectDescent.OpenModuleObjectDescent

noncomputable section

/-! Effective Zariski descent of native module-sheaf objects. Local
modules are extended by open direct image; the genuine native descent
maps give the matching-section object and its local recovery. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ModuleDescentRecovery.NativeModuleDescentRecovery

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
  (D : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun i => (U i).ι))

abbrev extension (i : ι) : X.Modules := (Scheme.Modules.pushforward (U i).ι).obj (D.obj i)

def restrictionRecovery (i : ι) : (extension U D i).restrict (U i).ι ≅ D.obj i :=
  (asIso (Scheme.Modules.restrictAdjunction (U i).ι).counit).app
    (show (U i).toScheme.Modules from D.obj i)

def nativeRecovery (i : ι) : (Scheme.Modules.pullback (U i).ι).obj (extension U D i) ≅ D.obj i :=
  (Scheme.Modules.restrictFunctorIsoPullback (U i).ι).symm.app (extension U D i) ≪≫
    restrictionRecovery U D i

def cech : OpenPullback.CechObjectDescent.OpenPullbackCechIsos U (extension U D) :=
  Intrinsic.OpenModuleCech.IntrinsicOpenModuleCech.cech U D (extension U D) (nativeRecovery U D)

/-- The actual glued module is the sheaf of matching sections. -/
def module : X.Modules := (cech U D).transitions.moduleSheaf

def module_recovery (i : ι) : (Scheme.Modules.pullback (U i).ι).obj (module U D) ≅ D.obj i :=
  (Scheme.Modules.restrictFunctorIsoPullback (U i).ι).symm.app (module U D) ≪≫
    (cech U D).transitions.recoveryIso i ≪≫ restrictionRecovery U D i

variable (hU : ∀ x : X, ∃ i, x ∈ U i)
  (hD : ∀ i, Picard.PoincareBundle.Line.Bundles.IsLine (D.obj i))

/-- Each given local object is retained as an actual original line. -/
def localLine (i : ι) : Line.Bundles.LineBundle (U i).toScheme := ⟨D.obj i, hD i⟩

/-- A native line descent datum is effective on every Zariski open
cover. No Noetherian or reducedness assumption is used here. -/
def lineBundle : Line.Bundles.LineBundle X :=
  (cech U D).lineBundle hU (localLine U D hD) (restrictionRecovery U D)

def lineBundle_recovery (i : ι) :
    ((OpenModuleObjectDescent.lineBundle U D hU hD).pullback (U i).ι).sheaf ≅ D.obj i :=
  (cech U D).lineBundle_recovery hU (localLine U D hD) (restrictionRecovery U D) i

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.ObjectDescent.OpenModuleObjectDescent

end ComponentSource_5

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.ObjectDescent"


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
    (`OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.ObjectDescent.OpenModuleObjectDescent.module_recovery, "definition")
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
    ("nonce", toJson "c08d4acd63d27d1030a9a63233fcadf9"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:c08d4acd63d27d1030a9a63233fcadf9"
