module

public import paper_verification.oai_base000_run4
import all paper_verification.oai_base000_run4
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import all Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.LinearAlgebra.Multilinear.Basic
import all Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import all Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.AlgebraicGeometry.AffineScheme
import all Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Topology.Sheaves.Stalks
import all Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Algebra.Group.Commute.Units
import all Mathlib.Algebra.Group.Commute.Units
public import Mathlib.CategoryTheory.Endomorphism
import all Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
import all Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

@[expose] public section ComponentSource_0
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.TupleSheaf -/

/-! # Tuple Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.TupleSheaf

noncomputable section

/-! Arbitrary tuples of regular functions on intersections with fixed opens form a sheaf; gluing is performed in each actual section ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

universe u

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)

def openFrameTuplePresheaf : TopCat.Presheaf (Type u) X where
  obj V := SectionModules.OpenFrameLocalTuple U V.unop
  map h := TypeCat.ofHom (TupleRestrictions.openFrameTupleRestriction U h.unop.le)
  map_id V := by
    apply ConcreteCategory.hom_ext
    intro s
    exact TupleRestrictions.openFrameTupleRestriction_refl U V.unop s
  map_comp h k := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (TupleRestrictions.openFrameTupleRestriction_comp U h.unop.le k.unop.le s).symm

theorem openFrameTuple_components_compatible {α : Type u} (V : α → X.Opens)
    (s : ∀ a, SectionModules.OpenFrameLocalTuple U (V a))
    (hs : ∀ a b, TupleRestrictions.openFrameTupleRestriction U (show V a ⊓ V b ≤ V a from inf_le_left) (s a) =
      TupleRestrictions.openFrameTupleRestriction U (show V a ⊓ V b ≤ V b from inf_le_right) (s b)) (i : ι) :
    X.presheaf.IsCompatible (fun a => V a ⊓ U i) (fun a => s a i) := by
  intro a b
  let Z := (V a ⊓ U i) ⊓ (V b ⊓ U i)
  have hz : Z ≤ (V a ⊓ V b) ⊓ U i :=
    le_inf (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
      (inf_le_left.trans inf_le_right)
  have he := congrArg (fun t : SectionModules.OpenFrameLocalTuple U (V a ⊓ V b) => t i) (hs a b)
  have hr := congrArg (fun z : Γ(X, (V a ⊓ V b) ⊓ U i) => X.presheaf.map (homOfLE hz).op z) he
  exact (Relative.OpenFunctionUnits.openFunction_restriction_comp (inf_le_inf (show V a ⊓ V b ≤ V a from inf_le_left)
    (le_refl (U i))) hz (s a i)).symm.trans
      (hr.trans (Relative.OpenFunctionUnits.openFunction_restriction_comp (inf_le_inf (show V a ⊓ V b ≤ V b from inf_le_right)
        (le_refl (U i))) hz (s b i)))

theorem openFrameTuplePresheaf_isSheaf : (openFrameTuplePresheaf U).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types _).mpr
  intro α V s hs
  have hcoord (i : ι) : ∃! t : Γ(X, (iSup V) ⊓ U i), ∀ a,
      X.presheaf.map (homOfLE (inf_le_inf (le_iSup V a) (le_refl (U i)))).op t = s a i := by
    apply X.sheaf.existsUnique_gluing' (fun a => V a ⊓ U i) ((iSup V) ⊓ U i)
      (fun a => homOfLE (inf_le_inf (le_iSup V a) (le_refl (U i))))
    · intro x hx
      obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hx.1
      exact Opens.mem_iSup.mpr ⟨a, ha, hx.2⟩
    · exact openFrameTuple_components_compatible U V s hs i
  choose t ht hu using hcoord
  refine ⟨t, ?_, ?_⟩
  · intro a
    funext i
    exact ht i a
  · intro q hq
    funext i
    exact hu i (q i) (fun a => congrFun (hq a) i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.TupleSheaf
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.TupleSheaf"

@[expose] public section ComponentSource_1
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.DifferenceNaturality -/

/-! # Difference Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.DifferenceNaturality

noncomputable section

/-! The difference measuring compatibility of two frame coordinates commutes with ordinary regular-function restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (D : Transitions.OpenFrameTransitions U)

theorem openFrameDifference_restriction {V W : X.Opens} (h : W ≤ V)
    (x : SectionModules.OpenFrameLocalTuple U V) (i j : ι) :
    SectionModules.openFrameDifference U D W i j (TupleRestrictions.openFrameTupleRestriction U h x) =
      X.presheaf.map (homOfLE (inf_le_inf (inf_le_inf h (le_refl (U i))) (le_refl (U j)))).op
        (SectionModules.openFrameDifference U D V i j x) := by
  let Q := (V ⊓ U i) ⊓ U j
  let Z := (W ⊓ U i) ⊓ U j
  have a : Z ≤ Q := inf_le_inf (inf_le_inf h (le_refl (U i))) (le_refl (U j))
  have qj : Q ≤ V ⊓ U j := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have zj : Z ≤ W ⊓ U j := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hi := (Relative.OpenFunctionUnits.openFunction_restriction_comp (inf_le_inf h (le_refl (U i)))
    (show Z ≤ W ⊓ U i from inf_le_left) (x i)).trans
      (Relative.OpenFunctionUnits.openFunction_restriction_comp (show Q ≤ V ⊓ U i from inf_le_left) a (x i)).symm
  have hj := (Relative.OpenFunctionUnits.openFunction_restriction_comp (inf_le_inf h (le_refl (U j))) zj (x j)).trans
    (Relative.OpenFunctionUnits.openFunction_restriction_comp qj a (x j)).symm
  have ht := D.restrict Q Z a i j (inf_le_left.trans inf_le_right) inf_le_right
  have hm := (congrArg₂ (fun r s : Γ(X, Z) => r * s) ht.symm hj).trans
    ((X.presheaf.map (homOfLE a).op).hom.map_mul _ _).symm
  exact (congrArg₂ (fun r s : Γ(X, Z) => r - s) hi hm).trans
    ((X.presheaf.map (homOfLE a).op).hom.map_sub _ _).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.DifferenceNaturality
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.DifferenceNaturality"

@[expose] public section ComponentSource_2
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.SectionLocality -/

/-! # Section Locality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.SectionLocality

noncomputable section

/-! Compatibility of frame coordinates can be checked on any open cover, by the separatedness of the actual regular-function sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (D : Transitions.OpenFrameTransitions U)

theorem openFrameSectionModule_mem_of_locally {V : X.Opens} {α : Type u} (W : α → X.Opens)
    (hW : ∀ a, W a ≤ V) (hcover : V ≤ iSup W) (x : SectionModules.OpenFrameLocalTuple U V)
    (hx : ∀ a, TupleRestrictions.openFrameTupleRestriction U (hW a) x ∈ SectionModules.openFrameSectionModule U D (W a)) :
    x ∈ SectionModules.openFrameSectionModule U D V := by
  simp only [SectionModules.openFrameSectionModule, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  intro i j
  let Z := (V ⊓ U i) ⊓ U j
  let Q := fun a => (W a ⊓ U i) ⊓ U j
  have hQ (a : α) : Q a ≤ Z := inf_le_inf (inf_le_inf (hW a) (le_refl (U i))) (le_refl (U j))
  have hc : Z ≤ iSup Q := by
    intro z hz
    obtain ⟨a, ha⟩ := Opens.mem_iSup.mp (hcover hz.1.1)
    exact Opens.mem_iSup.mpr ⟨a, ⟨ha, hz.1.2⟩, hz.2⟩
  apply X.sheaf.eq_of_locally_eq' Q Z (fun a => homOfLE (hQ a)) hc
  intro a
  exact (DifferenceNaturality.openFrameDifference_restriction D (hW a) x i j).symm.trans
    ((hx a i j).trans (X.presheaf.map (homOfLE (hQ a)).op).hom.map_zero.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.SectionLocality
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.SectionLocality"

@[expose] public section ComponentSource_3
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.ModuleSheaf -/

/-! # Module Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.ModuleSheaf

noncomputable section

/-! Compatible frame coordinates form an actual sheaf of modules, proved by unique gluing in the regular-function coordinate sheaf and locality of the transition equations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (D : Transitions.OpenFrameTransitions U)

def openFrameSectionTypePresheaf : TopCat.Presheaf (Type u) X :=
  (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).obj (ModulePresheaf.openFrameModulePresheaf D) ⋙ forget AddCommGrpCat

theorem openFrameSectionTypePresheaf_isSheaf : (openFrameSectionTypePresheaf D).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types _).mpr
  intro α V s hs
  change ∀ a b, RestrictionCompatibility.openFrameSectionRestriction D (show V a ⊓ V b ≤ V a from inf_le_left) (s a) =
    RestrictionCompatibility.openFrameSectionRestriction D (show V a ⊓ V b ≤ V b from inf_le_right) (s b) at hs
  have hvals : (TupleSheaf.openFrameTuplePresheaf U).IsCompatible V (fun a => (s a).val) := by
    intro a b
    exact congrArg Subtype.val (hs a b)
  obtain ⟨t, ht, hu⟩ := (TupleSheaf.openFrameTuplePresheaf_isSheaf U).isSheafUniqueGluing_types (fun a => (s a).val) hvals
  have htmem : t ∈ SectionModules.openFrameSectionModule U D (iSup V) :=
    SectionLocality.openFrameSectionModule_mem_of_locally D V (fun a => le_iSup V a) le_rfl t
      (fun a => (ht a).symm ▸ (s a).property)
  refine ⟨⟨t, htmem⟩, ?_, ?_⟩
  · intro a
    exact Subtype.ext (ht a)
  · intro q hq
    apply Subtype.ext
    exact hu q.val (fun a => congrArg Subtype.val (hq a))

def openFrameModuleSheaf : X.Modules where
  val := ModulePresheaf.openFrameModulePresheaf D
  isSheaf := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp' (forget AddCommGrpCat) _).mpr
    (openFrameSectionTypePresheaf_isSheaf D)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.ModuleSheaf
end ComponentSource_3

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.ModuleSheaf"

@[expose] public section ComponentSource_4
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.CoordinateCompatibility -/

/-! # Coordinate Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame

noncomputable section

/-! A regular function on one frame open produces compatible coordinates on every overlap by the transition cocycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (D : Transitions.OpenFrameTransitions U)

def Transitions.OpenFrameTransitions.frameValues (V : X.Opens) (k : ι) (hV : V ≤ U k) (x : Γ(X, V)) (i : ι) : Γ(X, V ⊓ U i) :=
  (D.value (V ⊓ U i) i k inf_le_right (inf_le_left.trans hV)).val *
    X.presheaf.map (homOfLE (show V ⊓ U i ≤ V from inf_le_left)).op x

theorem Transitions.OpenFrameTransitions.frameValues_restrict (V : X.Opens) (k : ι) (hV : V ≤ U k) (x : Γ(X, V)) (i : ι)
    (W : X.Opens) (hW : W ≤ V ⊓ U i) :
    X.presheaf.map (homOfLE hW).op (D.frameValues V k hV x i) =
      (D.value W i k (hW.trans inf_le_right) (hW.trans (inf_le_left.trans hV))).val *
        X.presheaf.map (homOfLE (hW.trans inf_le_left)).op x := by
  exact ((X.presheaf.map (homOfLE hW).op).hom.map_mul _ _).trans
    (congrArg₂ (fun a b : Γ(X, W) => a * b)
      (D.restrict (V ⊓ U i) W hW i k inf_le_right (inf_le_left.trans hV))
      (Relative.OpenFunctionUnits.openFunction_restriction_comp inf_le_left hW x))

theorem Transitions.OpenFrameTransitions.frameValues_compatible (V : X.Opens) (k : ι) (hV : V ≤ U k) (x : Γ(X, V)) (i j : ι) :
    X.presheaf.map (homOfLE (show (V ⊓ U i) ⊓ U j ≤ V ⊓ U i from inf_le_left)).op
      (D.frameValues V k hV x i) =
        (D.value ((V ⊓ U i) ⊓ U j) i j (inf_le_left.trans inf_le_right) inf_le_right).val *
          X.presheaf.map (homOfLE (show (V ⊓ U i) ⊓ U j ≤ V ⊓ U j from
            le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op (D.frameValues V k hV x j) := by
  let W := (V ⊓ U i) ⊓ U j
  have hi : W ≤ U i := inf_le_left.trans inf_le_right
  have hj : W ≤ U j := inf_le_right
  have hk : W ≤ U k := (inf_le_left.trans inf_le_left).trans hV
  have hc : (D.value W i j hi hj).val * (D.value W j k hj hk).val = (D.value W i k hi hk).val :=
    congrArg Units.val (D.comp W i j k hi hj hk)
  have hl := D.frameValues_restrict V k hV x i W inf_le_left
  have hr := D.frameValues_restrict V k hV x j W (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
  exact hl.trans ((congrArg (fun a : Γ(X, W) => a *
    (X.presheaf.map (homOfLE (show W ≤ V from inf_le_left.trans inf_le_left)).op x)) hc.symm).trans
      ((mul_assoc _ _ _).trans (congrArg (fun a : Γ(X, W) => (D.value W i j hi hj).val * a) hr.symm)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame
end ComponentSource_4

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.CoordinateCompatibility"

@[expose] public section ComponentSource_5
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.SectionGenerators -/

/-! # Section Generators -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame

noncomputable section

/-! A frame on a containing chart gives a linear generator of the module of compatible local coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (D : Transitions.OpenFrameTransitions U)

def SectionGenerators.openFrameGenerator (V : X.Opens) (k : ι) (hV : V ≤ U k) :
    Γ(X, V) →ₗ[Γ(X, V)] SectionModules.openFrameSectionModule U D V :=
  (LinearMap.pi (fun i =>
    (Relative.OpenFunctionScalars.relativeOpenFunctionScalar V (V ⊓ U i) inf_le_left
      (D.value (V ⊓ U i) i k inf_le_right (inf_le_left.trans hV)).val).hom.comp
        (Relative.OpenFunctionUnits.relativeOpenFunctionUnitMap V (V ⊓ U i) inf_le_left))).codRestrict
    (SectionModules.openFrameSectionModule U D V) (by
      intro x
      apply (SectionModules.openFrameSectionModule_mem_iff U D V _).mpr
      intro i j
      exact D.frameValues_compatible V k hV x i j)

theorem SectionGenerators.openFrameGenerator_apply (V : X.Opens) (k : ι) (hV : V ≤ U k) (x : Γ(X, V)) (i : ι) :
    (SectionGenerators.openFrameGenerator D V k hV x).val i = D.frameValues V k hV x i := rfl

theorem Transitions.OpenFrameTransitions.frameValues_self (V : X.Opens) (k : ι) (hV : V ≤ U k) (x : Γ(X, V)) :
    D.frameValues V k hV x k =
      X.presheaf.map (homOfLE (show V ⊓ U k ≤ V from inf_le_left)).op x := by
  exact (congrArg (fun a : Γ(X, V ⊓ U k)ˣ => a.val *
    X.presheaf.map (homOfLE (show V ⊓ U k ≤ V from inf_le_left)).op x)
      (D.self (V ⊓ U k) k inf_le_right)).trans (one_mul _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame
end ComponentSource_5

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.SectionGenerators"

@[expose] public section ComponentSource_6
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.LocalFreeness -/

/-! # Local Freeness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.LocalFreeness

noncomputable section

/-! On any open contained in one frame chart, compatible frame-coordinate sections form a free module of rank one. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens}

theorem openFunctionRestriction_bijective_of_eq {V W : X.Opens} (h : W ≤ V) (he : W = V) :
    Function.Bijective (X.presheaf.map (homOfLE h).op) := by
  have : IsIso (homOfLE h) := homOfLE_isIso_of_eq h he
  exact ConcreteCategory.bijective_of_isIso (X.presheaf.map (homOfLE h).op)

variable (D : Transitions.OpenFrameTransitions U)

theorem openFrameGenerator_injective (V : X.Opens) (k : ι) (hV : V ≤ U k) :
    Function.Injective (SectionGenerators.openFrameGenerator D V k hV) := by
  intro x y h
  apply (openFunctionRestriction_bijective_of_eq inf_le_left (inf_eq_left.mpr hV)).injective
  exact (D.frameValues_self V k hV x).symm.trans
    ((congrArg (fun s : SectionModules.openFrameSectionModule U D V => s.val k) h).trans (D.frameValues_self V k hV y))

theorem openFrameGenerator_surjective (V : X.Opens) (k : ι) (hV : V ≤ U k) :
    Function.Surjective (SectionGenerators.openFrameGenerator D V k hV) := by
  intro s
  obtain ⟨x, hx⟩ := (openFunctionRestriction_bijective_of_eq inf_le_left (inf_eq_left.mpr hV)).surjective (s.val k)
  refine ⟨x, Subtype.ext ?_⟩
  funext i
  let W := (V ⊓ U i) ⊓ U k
  have hWi : W ≤ V ⊓ U i := inf_le_left
  have hWk : W ≤ V ⊓ U k := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have heW : W = V ⊓ U i := inf_eq_left.mpr (inf_le_left.trans hV)
  apply (openFunctionRestriction_bijective_of_eq hWi heW).injective
  have hs := (SectionModules.openFrameSectionModule_mem_iff U D V s.val).mp s.property i k
  have hx' := congrArg (fun z : Γ(X, V ⊓ U k) => X.presheaf.map (homOfLE hWk).op z) hx
  have hk : X.presheaf.map (homOfLE hWk).op (s.val k) =
      X.presheaf.map (homOfLE (hWi.trans inf_le_left)).op x :=
    hx'.symm.trans (Relative.OpenFunctionUnits.openFunction_restriction_comp inf_le_left hWk x)
  exact (D.frameValues_restrict V k hV x i W hWi).trans
    ((congrArg (fun z : Γ(X, W) =>
      (D.value W i k (hWi.trans inf_le_right) (hWi.trans (inf_le_left.trans hV))).val * z) hk).symm.trans hs.symm)

def openFrameLocalEquiv (V : X.Opens) (k : ι) (hV : V ≤ U k) :
    Γ(X, V) ≃ₗ[Γ(X, V)] SectionModules.openFrameSectionModule U D V :=
  LinearEquiv.ofBijective (SectionGenerators.openFrameGenerator D V k hV)
    ⟨openFrameGenerator_injective D V k hV, openFrameGenerator_surjective D V k hV⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.LocalFreeness
end ComponentSource_6

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.LocalFreeness"

@[expose] public section ComponentSource_7
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.GeneratorNaturality -/

/-! # Generator Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.GeneratorNaturality

noncomputable section

/-! The local rank-one generators commute with actual regular-function and frame-section restriction maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (D : Transitions.OpenFrameTransitions U)

theorem openFrameGenerator_restriction {V W : X.Opens} (h : W ≤ V) (k : ι) (hV : V ≤ U k) (x : Γ(X, V)) :
    RestrictionCompatibility.openFrameSectionRestriction D h (SectionGenerators.openFrameGenerator D V k hV x) =
      SectionGenerators.openFrameGenerator D W k (h.trans hV) (X.presheaf.map (homOfLE h).op x) := by
  apply Subtype.ext
  funext i
  exact (D.frameValues_restrict V k hV x i (W ⊓ U i) (inf_le_inf h (le_refl (U i)))).trans
    (congrArg (fun z : Γ(X, W ⊓ U i) =>
      (D.value (W ⊓ U i) i k inf_le_right (inf_le_left.trans (h.trans hV))).val * z)
        (Relative.OpenFunctionUnits.openFunction_restriction_comp h (show W ⊓ U i ≤ W from inf_le_left) x).symm)

theorem openFrameGenerator_smul_one (V : X.Opens) (k : ι) (hV : V ≤ U k) (x : Γ(X, V)) :
    x • SectionGenerators.openFrameGenerator D V k hV 1 = SectionGenerators.openFrameGenerator D V k hV x :=
  ((SectionGenerators.openFrameGenerator D V k hV).map_smul x 1).symm.trans
    (congrArg (SectionGenerators.openFrameGenerator D V k hV) (mul_one x))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.GeneratorNaturality
end ComponentSource_7

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.GeneratorNaturality"

@[expose] public section ComponentSource_8
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers -/

/-! # Powers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers

noncomputable section

/-!
The universal property of tensor powers of module sheaves, expressed in
terms of actual multilinear maps on sections. This provides a concrete
predicate for powers of a line bundle, without an opaque tensor-power API.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

/-- Multilinear maps of sheaves, compatible with every restriction map. -/
structure SheafMultilinearMap (L : X.Modules) (n : ℕ) (M : X.Modules) where
  app (U : X.Opens) : MultilinearMap Γ(X, U) (fun _ : Fin n => Γ(L, U)) Γ(M, U)
  naturality {U V : X.Opens} (h : V ⟶ U) (s : Fin n → Γ(L, U)) :
    M.presheaf.map h.op (app U s) =
      app V (fun i => L.presheaf.map h.op (s i))

namespace SheafMultilinearMap

variable {L M N P : X.Modules} {n : ℕ}

@[ext]
theorem ext {β γ : SheafMultilinearMap L n M} (h : ∀ U, β.app U = γ.app U) : β = γ := by
  cases β
  cases γ
  congr
  exact funext h

/-- The linear map on sections induced by a module-sheaf morphism. -/
def homApp (f : M ⟶ N) (U : X.Opens) : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) where
  toFun s := f.app U s
  map_add' s t := (f.app U).hom.map_add s t
  map_smul' r s := f.app_smul r s

/-- Postcomposition of a multilinear map by a sheaf morphism. -/
def postcomp (β : SheafMultilinearMap L n M) (f : M ⟶ N) :
    SheafMultilinearMap L n N where
  app U := (homApp f U).compMultilinearMap (β.app U)
  naturality {U V} h s := by
    change N.presheaf.map h.op (f.app U (β.app U s)) =
      f.app V (β.app V (fun i => L.presheaf.map h.op (s i)))
    have hf := ConcreteCategory.congr_hom (f.mapPresheaf.naturality h.op) (β.app U s)
    exact hf.symm.trans (congrArg (fun t => f.app V t) (β.naturality h s))

@[simp]
theorem postcomp_id (β : SheafMultilinearMap L n M) : β.postcomp (𝟙 M) = β := by
  ext U s
  rfl

theorem postcomp_comp (β : SheafMultilinearMap L n M) (f : M ⟶ N) (g : N ⟶ P) :
    β.postcomp (f ≫ g) = (β.postcomp f).postcomp g := by
  ext U s
  rfl

/-- The tautological unary multilinear map. -/
def unary (L : X.Modules) : SheafMultilinearMap L 1 L where
  app U := (MultilinearMap.ofSubsingleton Γ(X, U) Γ(L, U) Γ(L, U) (0 : Fin 1))
    LinearMap.id
  naturality _ _ := rfl

/-- A unary multilinear map is an ordinary morphism of module sheaves. -/
def unaryToHom (β : SheafMultilinearMap L 1 M) : L ⟶ M where
  val.app U := ModuleCat.ofHom
    ((MultilinearMap.ofSubsingleton Γ(X, U.unop) Γ(L, U.unop) Γ(M, U.unop)
      (0 : Fin 1)).symm (β.app U.unop))
  val.naturality {U V} h := by
    ext s
    exact (β.naturality h.unop (fun _ => s)).symm

@[simp]
theorem unary_postcomp_unaryToHom (β : SheafMultilinearMap L 1 M) :
    (unary L).postcomp β.unaryToHom = β := by
  ext U s
  change β.app U (fun _ => s 0) = β.app U s
  congr 1
  funext i
  congr 1
  exact Subsingleton.elim _ _

@[simp]
theorem unaryToHom_unary_postcomp (f : L ⟶ M) :
    ((unary L).postcomp f).unaryToHom = f := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  rfl

end SheafMultilinearMap

/-- `P` is an `n`th tensor power of `L` when morphisms out of `P` correspond
bijectively to `n`-multilinear maps out of `L`, by postcomposition. -/
def IsTensorPower (L : X.Modules) (n : ℕ) (P : X.Modules) : Prop :=
  ∃ β : SheafMultilinearMap L n P,
    ∀ Q : X.Modules, Function.Bijective (fun f : P ⟶ Q => β.postcomp f)

theorem isTensorPower_one (L : X.Modules) : IsTensorPower L 1 L := by
  refine ⟨SheafMultilinearMap.unary L, fun Q => ?_⟩
  exact ⟨fun f g h => by
      simpa using congrArg SheafMultilinearMap.unaryToHom h,
    fun β => ⟨β.unaryToHom, β.unary_postcomp_unaryToHom⟩⟩

/-- The universal property determines the tensor power up to isomorphism. -/
theorem IsTensorPower.unique {L P Q : X.Modules} {n : ℕ}
    (hP : IsTensorPower L n P) (hQ : IsTensorPower L n Q) : Nonempty (P ≅ Q) := by
  obtain ⟨β, hβ⟩ := hP
  obtain ⟨γ, hγ⟩ := hQ
  obtain ⟨f, hf⟩ := (hβ Q).surjective γ
  obtain ⟨g, hg⟩ := (hγ P).surjective β
  refine ⟨⟨f, g, ?_, ?_⟩⟩
  · apply (hβ P).injective
    exact (β.postcomp_comp f g).trans
      ((congrArg (fun δ : SheafMultilinearMap L n Q => δ.postcomp g) hf).trans
        (hg.trans β.postcomp_id.symm))
  · apply (hγ Q).injective
    exact (γ.postcomp_comp g f).trans
      ((congrArg (fun δ : SheafMultilinearMap L n P => δ.postcomp f) hg).trans
        (hf.trans γ.postcomp_id.symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers
end ComponentSource_8

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers"

@[expose] public section ComponentSource_9
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Presheaf -/

/-! # Presheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Presheaf

noncomputable section

/-! The presheaf tensor power, with restriction maps over the varying coordinate rings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

variable {X : Scheme.{u}}

/-- Tensor-power sections before sheafification. -/
def tensorPowerSections (L : X.Modules) (n : ℕ) (U : X.Opens) : ModuleCat Γ(X, U) :=
  ModuleCat.of Γ(X, U) (PiTensorProduct Γ(X, U) (fun _ : Fin n => Γ(L, U)))

/-- Restrict every entry of a tensor-generating tuple. -/
def tensorPowerVectorMap (L : X.Modules) {U V : X.Opensᵒᵖ} (h : U ⟶ V)
    {n : ℕ} (s : Fin n → Γ(L, U.unop)) : Fin n → Γ(L, V.unop) :=
  fun i => L.val.map h (s i)

theorem tensorPowerVectorMap_update (L : X.Modules) {U V : X.Opensᵒᵖ} (h : U ⟶ V)
    {n : ℕ} [DecidableEq (Fin n)] (s : Fin n → Γ(L, U.unop)) (i : Fin n) (x : Γ(L, U.unop)) :
    tensorPowerVectorMap L h (Function.update s i x) =
      Function.update (tensorPowerVectorMap L h s) i (L.val.map h x) :=
  Function.comp_update (fun x => L.val.map h x) s i x

/-- Restriction of tensor generators is multilinear over the original coordinate ring. -/
def tensorPowerRestrictionMultilinear (L : X.Modules) (n : ℕ)
    {U V : X.Opensᵒᵖ} (h : U ⟶ V) :
    MultilinearMap Γ(X, U.unop) (fun _ : Fin n => Γ(L, U.unop))
      ((ModuleCat.restrictScalars (X.presheaf.map h).hom).obj (tensorPowerSections L n V.unop)) where
  toFun s := PiTensorProduct.tprod Γ(X, V.unop) (tensorPowerVectorMap L h s)
  map_update_add' s i x y := by
    let t := PiTensorProduct.tprod Γ(X, V.unop) (s := fun _ : Fin n => Γ(L, V.unop))
    exact (congrArg t (tensorPowerVectorMap_update L h s i (x + y))).trans
      ((congrArg (fun a => t (Function.update (tensorPowerVectorMap L h s) i a))
        ((L.val.map h).hom.map_add x y)).trans
        ((t.map_update_add (tensorPowerVectorMap L h s) i _ _).trans
          (congrArg₂ (fun a b => t a + t b)
            (tensorPowerVectorMap_update L h s i x).symm
            (tensorPowerVectorMap_update L h s i y).symm)))
  map_update_smul' s i r x := by
    let t := PiTensorProduct.tprod Γ(X, V.unop) (s := fun _ : Fin n => Γ(L, V.unop))
    exact (congrArg t (tensorPowerVectorMap_update L h s i (r • x))).trans
      ((congrArg (fun a => t (Function.update (tensorPowerVectorMap L h s) i a))
        (L.val.map_smul h r x)).trans
        ((t.map_update_smul (tensorPowerVectorMap L h s) i (X.presheaf.map h r) _).trans
          (congrArg (fun a => (X.presheaf.map h r) • t a)
            (tensorPowerVectorMap_update L h s i x).symm)))

/-- The linear restriction map on tensor-power sections. -/
def tensorPowerRestriction (L : X.Modules) (n : ℕ) {U V : X.Opensᵒᵖ} (h : U ⟶ V) :
    tensorPowerSections L n U.unop ⟶
      (ModuleCat.restrictScalars (X.presheaf.map h).hom).obj (tensorPowerSections L n V.unop) := by
  let Q : ModuleCat Γ(X, U.unop) :=
    (ModuleCat.restrictScalars (X.presheaf.map h).hom).obj (tensorPowerSections L n V.unop)
  let : Module Γ(X, U.unop) Q := Q.isModule
  exact (ModuleCat.ofHom (Y := Q)
    (PiTensorProduct.lift (E := Q) (tensorPowerRestrictionMultilinear L n h)) :
    ModuleCat.of Γ(X, U.unop) (PiTensorProduct Γ(X, U.unop) (fun _ : Fin n => Γ(L, U.unop))) ⟶ Q)

@[simp]
theorem tensorPowerRestriction_tprod (L : X.Modules) (n : ℕ) {U V : X.Opensᵒᵖ} (h : U ⟶ V)
    (s : Fin n → Γ(L, U.unop)) :
    tensorPowerRestriction L n h (PiTensorProduct.tprod Γ(X, U.unop) s) =
      PiTensorProduct.tprod Γ(X, V.unop) (tensorPowerVectorMap L h s) := by
  let Q : ModuleCat Γ(X, U.unop) :=
    (ModuleCat.restrictScalars (X.presheaf.map h).hom).obj (tensorPowerSections L n V.unop)
  let : Module Γ(X, U.unop) Q := Q.isModule
  exact PiTensorProduct.lift.tprod (φ := tensorPowerRestrictionMultilinear L n h) s

/-- The presheaf of tensor powers of a module sheaf. -/
def tensorPowerPresheaf (L : X.Modules) (n : ℕ) : X.PresheafOfModules where
  obj U := tensorPowerSections L n U.unop
  map h := tensorPowerRestriction L n h
  map_id U := by
    apply ModuleCat.hom_ext
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro s
    exact (tensorPowerRestriction_tprod L n (𝟙 U) s).trans
      (congrArg (PiTensorProduct.tprod Γ(X, U.unop))
        (funext (fun i => ConcreteCategory.congr_hom (L.val.map_id U) (s i))))
  map_comp f h := by
    apply ModuleCat.hom_ext
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro s
    change tensorPowerRestriction L n (f ≫ h) (PiTensorProduct.tprod _ s) =
      tensorPowerRestriction L n h (tensorPowerRestriction L n f (PiTensorProduct.tprod _ s))
    rw [tensorPowerRestriction_tprod, tensorPowerRestriction_tprod, tensorPowerRestriction_tprod]
    congr 1
    funext i
    exact L.val.map_comp_apply f h (s i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Presheaf
end ComponentSource_9

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Presheaf"

@[expose] public section ComponentSource_10
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf -/

/-! # Power Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Existence of sheaf tensor powers with the actual multilinear universal property. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {L P Q : X.Modules} {n : ℕ}

section

/-- A morphism from the tensor presheaf gives a natural multilinear map on sections. -/
def Tensor.Powers.SheafMultilinearMap.ofTensorPowerPresheafHom (f : TensorPower.Presheaf.tensorPowerPresheaf L n ⟶ P.val) : Tensor.Powers.SheafMultilinearMap L n P where
  app U := (show PiTensorProduct Γ(X, U) (fun _ : Fin n => Γ(L, U)) →ₗ[Γ(X, U)] Γ(P, U)
    from (f.app (.op U)).hom).compMultilinearMap (PiTensorProduct.tprod Γ(X, U))
  naturality {U V} h s :=
    (PresheafOfModules.naturality_apply f h.op (PiTensorProduct.tprod Γ(X, U) s)).symm.trans
      (congrArg (fun a => f.app (.op V) a) (TensorPower.Presheaf.tensorPowerRestriction_tprod L n h.op s))

/-- A natural multilinear section map extends uniquely to the tensor presheaf. -/
def Tensor.Powers.SheafMultilinearMap.toTensorPowerPresheafHom (β : Tensor.Powers.SheafMultilinearMap L n P) : TensorPower.Presheaf.tensorPowerPresheaf L n ⟶ P.val where
  app U := (ModuleCat.ofHom (PiTensorProduct.lift (β.app U.unop)) :
    ModuleCat.of Γ(X, U.unop) (PiTensorProduct Γ(X, U.unop) (fun _ : Fin n => Γ(L, U.unop))) ⟶
      ModuleCat.of Γ(X, U.unop) Γ(P, U.unop))
  naturality {U V} h := by
    let Qr : ModuleCat Γ(X, U.unop) :=
      (ModuleCat.restrictScalars (X.presheaf.map h).hom).obj (ModuleCat.of Γ(X, V.unop) Γ(P, V.unop))
    let : Module Γ(X, U.unop) Qr := Qr.isModule
    apply ModuleCat.hom_ext
    apply PiTensorProduct.ext (R := Γ(X, U.unop)) (s := fun _ : Fin n => Γ(L, U.unop)) (E := Qr)
    apply MultilinearMap.ext
    intro s
    exact (congrArg (PiTensorProduct.lift (β.app V.unop))
      (TensorPower.Presheaf.tensorPowerRestriction_tprod L n h s)).trans
      ((PiTensorProduct.lift.tprod (φ := β.app V.unop) (TensorPower.Presheaf.tensorPowerVectorMap L h s)).trans
        ((β.naturality h.unop s).symm.trans
          (congrArg (fun a => P.presheaf.map h a) (PiTensorProduct.lift.tprod (φ := β.app U.unop) s).symm)))

/-- Universal maps out of the tensor presheaf are exactly natural multilinear maps. -/
def Tensor.Powers.SheafMultilinearMap.tensorPowerPresheafHomEquiv (L P : X.Modules) (n : ℕ) :
    (TensorPower.Presheaf.tensorPowerPresheaf L n ⟶ P.val) ≃ Tensor.Powers.SheafMultilinearMap L n P where
  toFun := Tensor.Powers.SheafMultilinearMap.ofTensorPowerPresheafHom
  invFun := Tensor.Powers.SheafMultilinearMap.toTensorPowerPresheafHom
  left_inv f := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    exact PiTensorProduct.lift.apply_symm_apply
      (show PiTensorProduct Γ(X, U.unop) (fun _ : Fin n => Γ(L, U.unop)) →ₗ[Γ(X, U.unop)]
        Γ(P, U.unop) from (f.app U).hom)
  right_inv β := by
    apply Tensor.Powers.SheafMultilinearMap.ext
    intro U
    exact PiTensorProduct.lift.symm_apply_apply (β.app U)

end

/-- The tensor power of a sheaf of modules, obtained by sheafifying the tensor presheaf. -/
def TensorPower.PowerSheaf.tensorPowerModule (L : X.Modules) (n : ℕ) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (TensorPower.Presheaf.tensorPowerPresheaf L n)

/-- The tensor-power sheaf has the multilinear universal property. -/
def TensorPower.PowerSheaf.tensorPowerHomEquiv (L P : X.Modules) (n : ℕ) :
    (TensorPower.PowerSheaf.tensorPowerModule L n ⟶ P) ≃ Tensor.Powers.SheafMultilinearMap L n P :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
    (TensorPower.Presheaf.tensorPowerPresheaf L n) P).trans (Tensor.Powers.SheafMultilinearMap.tensorPowerPresheafHomEquiv L P n)

/-- The universal correspondence commutes with postcomposition. -/
theorem TensorPower.PowerSheaf.tensorPowerHomEquiv_postcomp (f : TensorPower.PowerSheaf.tensorPowerModule L n ⟶ P) (h : P ⟶ Q) :
    TensorPower.PowerSheaf.tensorPowerHomEquiv L Q n (f ≫ h) = (TensorPower.PowerSheaf.tensorPowerHomEquiv L P n f).postcomp h := by
  have he := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv_naturality_right f h
  change Tensor.Powers.SheafMultilinearMap.ofTensorPowerPresheafHom
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
      (TensorPower.Presheaf.tensorPowerPresheaf L n) Q (f ≫ h)) = _
  rw [he]
  ext U s
  rfl

/-- Every module sheaf has an actual tensor power of every natural degree. -/
theorem TensorPower.PowerSheaf.tensorPowerModule_isTensorPower (L : X.Modules) (n : ℕ) :
    Tensor.Powers.IsTensorPower L n (TensorPower.PowerSheaf.tensorPowerModule L n) := by
  let β := TensorPower.PowerSheaf.tensorPowerHomEquiv L (TensorPower.PowerSheaf.tensorPowerModule L n) n (𝟙 _)
  refine ⟨β, fun Q => ?_⟩
  have he (f : TensorPower.PowerSheaf.tensorPowerModule L n ⟶ Q) : β.postcomp f = TensorPower.PowerSheaf.tensorPowerHomEquiv L Q n f :=
    (TensorPower.PowerSheaf.tensorPowerHomEquiv_postcomp (𝟙 _) f).symm.trans
      (congrArg (TensorPower.PowerSheaf.tensorPowerHomEquiv L Q n) (Category.id_comp f))
  exact ⟨fun f g h => (TensorPower.PowerSheaf.tensorPowerHomEquiv L Q n).injective
    ((he f).symm.trans (h.trans (he g))), fun γ =>
      ⟨(TensorPower.PowerSheaf.tensorPowerHomEquiv L Q n).symm γ,
        (he _).trans ((TensorPower.PowerSheaf.tensorPowerHomEquiv L Q n).apply_symm_apply γ)⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
end ComponentSource_10

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf"

@[expose] public section ComponentSource_11
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles -/

/-! # Line Bundles -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-!
Ampleness of actual line bundles. A section is nonvanishing where its map
from the structure sheaf is locally an isomorphism. Ampleness means that
positive tensor powers have sections with affine nonvanishing neighborhoods
covering the quasi-compact scheme (Stacks Project, Definition 01PR).
Tensor powers are specified by their universal multilinear property.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- Pullback of a section, viewed as a morphism from the structure module. -/
def Ample.LineBundles.pullbackSection {M : Y.Modules} (f : X ⟶ Y) (s : Line.Bundles.structureModule Y ⟶ M) :
    Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj M :=
  (Line.Bundles.structureModulePullbackIso f).inv ≫ (Scheme.Modules.pullback f).map s

/-- The largest open on which the section is a local frame. -/
def Ample.LineBundles.sectionNonvanishing {M : X.Modules} (s : Line.Bundles.structureModule X ⟶ M) : X.Opens :=
  sSup {U : X.Opens | IsIso (Ample.LineBundles.pullbackSection U.ι s)}

/-- A globally invertible section is nonvanishing everywhere. -/
theorem Ample.LineBundles.sectionNonvanishing_of_isIso {M : X.Modules} (s : Line.Bundles.structureModule X ⟶ M)
    [IsIso s] : Ample.LineBundles.sectionNonvanishing s = ⊤ := by
  apply top_unique
  apply le_sSup
  change IsIso (Ample.LineBundles.pullbackSection (⊤ : X.Opens).ι s)
  dsimp [Ample.LineBundles.pullbackSection]
  infer_instance

/-- Ampleness via affine nonvanishing loci of sections of positive powers. -/
def Line.Bundles.LineBundle.IsAmple (L : Line.Bundles.LineBundle X) : Prop :=
  IsCompact (Set.univ : Set X) ∧
    ∀ x : X, ∃ (n : ℕ) (_ : 0 < n) (P : Line.Bundles.LineBundle X)
      (_ : Tensor.Powers.IsTensorPower L.sheaf n P.sheaf) (s : Line.Bundles.structureModule X ⟶ P.sheaf),
      x ∈ Ample.LineBundles.sectionNonvanishing s ∧ IsAffineOpen (Ample.LineBundles.sectionNonvanishing s)

/-- The trivial line bundle on an affine scheme is ample. -/
theorem Line.Bundles.LineBundle.trivial_isAmple (X : Scheme.{u}) [IsAffine X] : (Line.Bundles.LineBundle.trivial X).IsAmple := by
  refine ⟨isCompact_univ, fun x => ?_⟩
  refine ⟨1, Nat.zero_lt_one, Line.Bundles.LineBundle.trivial X, Tensor.Powers.isTensorPower_one _, 𝟙 _, ?_, ?_⟩
  · change x ∈ @Ample.LineBundles.sectionNonvanishing X (Line.Bundles.structureModule X) (𝟙 _)
    rw [Ample.LineBundles.sectionNonvanishing_of_isIso]
    trivial
  · change IsAffineOpen (@Ample.LineBundles.sectionNonvanishing X (Line.Bundles.structureModule X) (𝟙 _))
    rw [Ample.LineBundles.sectionNonvanishing_of_isIso]
    exact isAffineOpen_top X

/-- Relative ampleness is ampleness over each affine open of the base. -/
def Line.Bundles.LineBundle.IsRelativelyAmple (L : Line.Bundles.LineBundle X) (f : X ⟶ Y) : Prop :=
  ∀ U : Y.Opens, IsAffineOpen U →
    (Line.Bundles.LineBundle.pullback (f ⁻¹ᵁ U).ι L).IsAmple

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
end ComponentSource_11

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles"

@[expose] public section ComponentSource_12
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Isomorphisms -/

/-! # Isomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Invariance of tensor powers and ampleness under isomorphism of line bundles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

namespace Tensor

variable {L M P Q : X.Modules} {n : ℕ}

/-- Precompose every argument of a sheaf-multilinear map by a module morphism. -/
def Powers.SheafMultilinearMap.precomp (β : Powers.SheafMultilinearMap L n P) (f : M ⟶ L) : Powers.SheafMultilinearMap M n P where
  app U := (β.app U).compLinearMap (fun _ => Powers.SheafMultilinearMap.homApp f U)
  naturality {U V} h s := by
    exact (β.naturality h (fun i => f.app U (s i))).trans
      (congrArg (β.app V) (funext fun i =>
        (ConcreteCategory.congr_hom (f.mapPresheaf.naturality h.op) (s i)).symm))

@[simp]
theorem Powers.SheafMultilinearMap.precomp_id (β : Powers.SheafMultilinearMap L n P) : β.precomp (𝟙 L) = β := by
  ext U s
  rfl

theorem Powers.SheafMultilinearMap.precomp_comp (β : Powers.SheafMultilinearMap L n P) (f : M ⟶ L) (h : Q ⟶ M) :
    (β.precomp f).precomp h = β.precomp (h ≫ f) := by
  ext U s
  rfl

theorem Powers.SheafMultilinearMap.precomp_postcomp (β : Powers.SheafMultilinearMap L n P) (f : M ⟶ L) (h : P ⟶ Q) :
    (β.postcomp h).precomp f = (β.precomp f).postcomp h := by
  ext U s
  rfl

/-- An isomorphism of the input module induces an equivalence of multilinear maps. -/
def Powers.SheafMultilinearMap.sourceIso (e : L ≅ M) (n : ℕ) (P : X.Modules) :
    Powers.SheafMultilinearMap L n P ≃ Powers.SheafMultilinearMap M n P where
  toFun β := β.precomp e.inv
  invFun β := β.precomp e.hom
  left_inv β := (β.precomp_comp e.inv e.hom).trans
    ((congrArg (fun f : L ⟶ L => β.precomp f) e.hom_inv_id).trans β.precomp_id)
  right_inv β := (β.precomp_comp e.hom e.inv).trans
    ((congrArg (fun f : M ⟶ M => β.precomp f) e.inv_hom_id).trans β.precomp_id)

end Tensor

/-- Replacing a module by an isomorphic one leaves its tensor powers unchanged. -/
theorem Tensor.Powers.IsTensorPower.of_sourceIso {L M P : X.Modules} {n : ℕ}
    (hP : Tensor.Powers.IsTensorPower L n P) (e : L ≅ M) : Tensor.Powers.IsTensorPower M n P := by
  obtain ⟨β, hβ⟩ := hP
  refine ⟨β.precomp e.inv, fun Q => ?_⟩
  have h : (fun f : P ⟶ Q => (β.precomp e.inv).postcomp f) =
      fun f : P ⟶ Q => Tensor.Powers.SheafMultilinearMap.sourceIso e n Q (β.postcomp f) := by
    funext f
    exact (β.precomp_postcomp e.inv f).symm
  rw [h]
  exact (Tensor.Powers.SheafMultilinearMap.sourceIso e n Q).bijective.comp (hβ Q)

/-- Ampleness depends only on the isomorphism class of the line bundle. -/
theorem Line.Bundles.LineBundle.IsAmple.of_iso {L M : Line.Bundles.LineBundle X} (hL : L.IsAmple)
    (e : L.sheaf ≅ M.sheaf) : M.IsAmple := by
  refine ⟨hL.1, fun x => ?_⟩
  obtain ⟨n, hn, P, hP, s, hxs, hs⟩ := hL.2 x
  exact ⟨n, hn, P, hP.of_sourceIso e, s, hxs, hs⟩

/-- Equivalent module sheaves give the same ampleness condition. -/
theorem Line.Bundles.LineBundle.isAmple_iff_of_iso {L M : Line.Bundles.LineBundle X} (e : L.sheaf ≅ M.sheaf) :
    L.IsAmple ↔ M.IsAmple :=
  ⟨fun h => h.of_iso e, fun h => h.of_iso e.symm⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
end ComponentSource_12

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Isomorphisms"

@[expose] public section ComponentSource_13
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MultilinearRestriction -/

/-! # Multilinear Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Restriction of multilinear maps of module sheaves to an open subscheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {L M N : Y.Modules} {n : ℕ}

/-- Direct image of a multilinear map, with scalars restricted along the
map on coordinate rings. -/
def Tensor.Powers.SheafMultilinearMap.pushforward {P Q : X.Modules} (β : Tensor.Powers.SheafMultilinearMap P n Q) (f : X ⟶ Y) :
    Tensor.Powers.SheafMultilinearMap ((Scheme.Modules.pushforward f).obj P) n
      ((Scheme.Modules.pushforward f).obj Q) where
  app U := {
    toFun := (β.app (f ⁻¹ᵁ U)).toFun
    map_update_add' s i x y := (β.app (f ⁻¹ᵁ U)).map_update_add s i x y
    map_update_smul' s i r x := (β.app (f ⁻¹ᵁ U)).map_update_smul s i (f.app U r) x }
  naturality h s := β.naturality ((TopologicalSpace.Opens.map f.base).map h) s

theorem Tensor.Powers.SheafMultilinearMap.pushforward_postcomp {P Q R : X.Modules} (β : Tensor.Powers.SheafMultilinearMap P n Q)
    (f : X ⟶ Y) (h : Q ⟶ R) :
    (β.postcomp h).pushforward f =
      (β.pushforward f).postcomp ((Scheme.Modules.pushforward f).map h) := by
  ext U s
  rfl

theorem Tensor.Powers.SheafMultilinearMap.pushforward_precomp {P Q R : X.Modules} (β : Tensor.Powers.SheafMultilinearMap P n Q)
    (f : X ⟶ Y) (h : R ⟶ P) :
    (β.precomp h).pushforward f =
      (β.pushforward f).precomp ((Scheme.Modules.pushforward f).map h) := by
  ext U s
  rfl

/-- Restrict a multilinear map along an open immersion. The section formula
uses the corresponding image open and the isomorphism of its coordinate rings. -/
def Tensor.Powers.SheafMultilinearMap.restrict (β : Tensor.Powers.SheafMultilinearMap L n M) (f : X ⟶ Y) [IsOpenImmersion f] :
    Tensor.Powers.SheafMultilinearMap (L.restrict f) n (M.restrict f) where
  app U := {
    toFun := (β.app (f ''ᵁ U)).toFun
    map_update_add' s i x y := (β.app (f ''ᵁ U)).map_update_add s i x y
    map_update_smul' s i r x := (β.app (f ''ᵁ U)).map_update_smul s i ((f.appIso U).inv r) x }
  naturality h s := β.naturality (f.opensFunctor.map h) s

/-- Restriction commutes with postcomposition by a morphism of module sheaves. -/
theorem Tensor.Powers.SheafMultilinearMap.restrict_postcomp (β : Tensor.Powers.SheafMultilinearMap L n M) (f : X ⟶ Y) [IsOpenImmersion f]
    (h : M ⟶ N) :
    (β.postcomp h).restrict f = (β.restrict f).postcomp ((Scheme.Modules.restrictFunctor f).map h) := by
  ext U s
  rfl

/-- Restriction commutes with precomposition in all the multilinear arguments. -/
theorem Tensor.Powers.SheafMultilinearMap.restrict_precomp (β : Tensor.Powers.SheafMultilinearMap L n M) (f : X ⟶ Y) [IsOpenImmersion f]
    (h : N ⟶ L) :
    (β.precomp h).restrict f = (β.restrict f).precomp ((Scheme.Modules.restrictFunctor f).map h) := by
  ext U s
  rfl

/-- The unit of restriction/direct image is compatible with multilinear maps. -/
theorem Tensor.Powers.SheafMultilinearMap.restrict_unit_naturality (β : Tensor.Powers.SheafMultilinearMap L n M)
    (f : X ⟶ Y) [IsOpenImmersion f] :
    ((β.restrict f).pushforward f).precomp ((Scheme.Modules.restrictAdjunction f).unit.app L) =
      β.postcomp ((Scheme.Modules.restrictAdjunction f).unit.app M) := by
  ext U s
  exact (β.naturality (f.isOpenEmbedding.isOpenMap.adjunction.counit.app U) s).symm

/-- The counit of restriction/direct image is compatible with multilinear maps. -/
theorem Tensor.Powers.SheafMultilinearMap.restrict_counit_naturality {P Q : X.Modules} (β : Tensor.Powers.SheafMultilinearMap P n Q)
    (f : X ⟶ Y) [IsOpenImmersion f] :
    ((β.pushforward f).restrict f).postcomp ((Scheme.Modules.restrictAdjunction f).counit.app Q) =
      β.precomp ((Scheme.Modules.restrictAdjunction f).counit.app P) := by
  ext U s
  exact β.naturality (f.isOpenEmbedding.isOpenMap.adjunction.unit.app U) s

/-- The restriction/direct-image adjunction also holds for multilinear maps. -/
def Tensor.Powers.SheafMultilinearMap.restrictHomEquiv (f : X ⟶ Y) [IsOpenImmersion f] (L : Y.Modules) (n : ℕ) (Q : X.Modules) :
    Tensor.Powers.SheafMultilinearMap (L.restrict f) n Q ≃
      Tensor.Powers.SheafMultilinearMap L n ((Scheme.Modules.pushforward f).obj Q) where
  toFun β := (β.pushforward f).precomp ((Scheme.Modules.restrictAdjunction f).unit.app L)
  invFun β := (β.restrict f).postcomp ((Scheme.Modules.restrictAdjunction f).counit.app Q)
  left_inv β := by
    change (((β.pushforward f).precomp
      ((Scheme.Modules.restrictAdjunction f).unit.app L)).restrict f).postcomp
        ((Scheme.Modules.restrictAdjunction f).counit.app Q) = β
    rw [Tensor.Powers.SheafMultilinearMap.restrict_precomp, ← Tensor.Powers.SheafMultilinearMap.precomp_postcomp, Tensor.Powers.SheafMultilinearMap.restrict_counit_naturality, Tensor.Powers.SheafMultilinearMap.precomp_comp]
    exact (congrArg (fun h => β.precomp h)
      ((Scheme.Modules.restrictAdjunction f).left_triangle_components L)).trans β.precomp_id
  right_inv β := by
    change (((β.restrict f).postcomp
      ((Scheme.Modules.restrictAdjunction f).counit.app Q)).pushforward f).precomp
        ((Scheme.Modules.restrictAdjunction f).unit.app L) = β
    rw [Tensor.Powers.SheafMultilinearMap.pushforward_postcomp, Tensor.Powers.SheafMultilinearMap.precomp_postcomp, Tensor.Powers.SheafMultilinearMap.restrict_unit_naturality, ← Tensor.Powers.SheafMultilinearMap.postcomp_comp]
    exact (congrArg (fun h => β.postcomp h)
      ((Scheme.Modules.restrictAdjunction f).right_triangle_components Q)).trans β.postcomp_id

/-- The multilinear adjunction respects postcomposition by a restricted sheaf map. -/
theorem Tensor.Powers.SheafMultilinearMap.restrictHomEquiv_postcomp (β : Tensor.Powers.SheafMultilinearMap L n M)
    (f : X ⟶ Y) [IsOpenImmersion f] {Q : X.Modules} (h : M.restrict f ⟶ Q) :
    Tensor.Powers.SheafMultilinearMap.restrictHomEquiv f L n Q ((β.restrict f).postcomp h) =
      β.postcomp ((Scheme.Modules.restrictAdjunction f).homEquiv M Q h) := by
  change (((β.restrict f).postcomp h).pushforward f).precomp
    ((Scheme.Modules.restrictAdjunction f).unit.app L) = _
  rw [Tensor.Powers.SheafMultilinearMap.pushforward_postcomp, Tensor.Powers.SheafMultilinearMap.precomp_postcomp, Tensor.Powers.SheafMultilinearMap.restrict_unit_naturality, ← Tensor.Powers.SheafMultilinearMap.postcomp_comp]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
end ComponentSource_13

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MultilinearRestriction"

@[expose] public section ComponentSource_14
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.TensorRestriction -/

/-! # Tensor Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor

noncomputable section

/-! The universal tensor-power property is preserved by restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {L P : Y.Modules} {n : ℕ}

/-- An isomorphic representing sheaf has the same universal tensor-power property. -/
theorem Powers.IsTensorPower.of_targetIso {Q : Y.Modules} (hP : Powers.IsTensorPower L n P) (e : P ≅ Q) :
    Powers.IsTensorPower L n Q := by
  obtain ⟨β, hβ⟩ := hP
  refine ⟨β.postcomp e.hom, fun R => ⟨?_, ?_⟩⟩
  · intro a b hab
    apply (cancel_epi e.hom).mp
    apply (hβ R).injective
    exact (β.postcomp_comp e.hom a).trans
      (hab.trans (β.postcomp_comp e.hom b).symm)
  · intro γ
    obtain ⟨a, ha⟩ := (hβ R).surjective γ
    refine ⟨e.inv ≫ a, ?_⟩
    exact (β.postcomp_comp e.hom (e.inv ≫ a)).symm.trans
      ((congrArg (fun h => β.postcomp h) (e.hom_inv_id_assoc a)).trans ha)

/-- A tensor power of a module sheaf restricts to the tensor power on an open subscheme. -/
theorem Powers.IsTensorPower.restrict (hP : Powers.IsTensorPower L n P) (f : X ⟶ Y) [IsOpenImmersion f] :
    Powers.IsTensorPower (L.restrict f) n (P.restrict f) := by
  obtain ⟨β, hβ⟩ := hP
  refine ⟨β.restrict f, fun Q => ⟨?_, ?_⟩⟩
  · intro a b hab
    apply ((Scheme.Modules.restrictAdjunction f).homEquiv P Q).injective
    apply (hβ ((Scheme.Modules.pushforward f).obj Q)).injective
    exact (β.restrictHomEquiv_postcomp f a).symm.trans
      ((congrArg (Powers.SheafMultilinearMap.restrictHomEquiv f L n Q) hab).trans
        (β.restrictHomEquiv_postcomp f b))
  · intro γ
    obtain ⟨a, ha⟩ := (hβ ((Scheme.Modules.pushforward f).obj Q)).surjective
      (Powers.SheafMultilinearMap.restrictHomEquiv f L n Q γ)
    let b := ((Scheme.Modules.restrictAdjunction f).homEquiv P Q).symm a
    refine ⟨b, (Powers.SheafMultilinearMap.restrictHomEquiv f L n Q).injective ?_⟩
    exact (β.restrictHomEquiv_postcomp f b).trans
      ((congrArg (fun h => β.postcomp h)
        (((Scheme.Modules.restrictAdjunction f).homEquiv P Q).apply_symm_apply a)).trans ha)

/-- The canonical module-sheaf pullback along an open immersion preserves tensor powers. -/
theorem Powers.IsTensorPower.pullback_of_isOpenImmersion (hP : Powers.IsTensorPower L n P)
    (f : X ⟶ Y) [IsOpenImmersion f] :
    Powers.IsTensorPower ((Scheme.Modules.pullback f).obj L) n ((Scheme.Modules.pullback f).obj P) :=
  ((hP.restrict f).of_sourceIso ((Scheme.Modules.restrictFunctorIsoPullback f).app L)).of_targetIso
    ((Scheme.Modules.restrictFunctorIsoPullback f).app P)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor
end ComponentSource_14

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.TensorRestriction"

@[expose] public section ComponentSource_15
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.Powers -/

/-! # Powers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Tensor powers of line bundles remain locally free of rank one. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators

universe u

variable {X : Scheme.{u}} {P : X.Modules} {n : ℕ}

/-- Multiplication of local functions is the universal tensor power of the structure module. -/
def LineBundle.Powers.structureModuleTensorMap (X : Scheme.{u}) (n : ℕ) :
    Tensor.Powers.SheafMultilinearMap (Line.Bundles.structureModule X) n (Line.Bundles.structureModule X) where
  app U := MultilinearMap.mkPiAlgebra Γ(X, U) (Fin n) Γ(X, U)
  naturality {U V} h s := by
    change (Fin n → Γ(X, U)) at s
    change X.presheaf.map h.op (∏ i, s i) = ∏ i, X.presheaf.map h.op (s i)
    exact map_prod (X.presheaf.map h.op).hom _ _

/-- A multilinear map out of copies of the structure sheaf is determined by its value on ones. -/
def Tensor.Powers.SheafMultilinearMap.unitToHom (β : Tensor.Powers.SheafMultilinearMap (Line.Bundles.structureModule X) n P) :
    Line.Bundles.structureModule X ⟶ P where
  val.app U := (ModuleCat.ofHom
    ((LinearMap.id : Γ(X, U.unop) →ₗ[Γ(X, U.unop)] Γ(X, U.unop)).smulRight
      (β.app U.unop (fun _ => (1 : Γ(X, U.unop))))) :
      ModuleCat.of Γ(X, U.unop) Γ(X, U.unop) ⟶ ModuleCat.of Γ(X, U.unop) Γ(P, U.unop))
  val.naturality {U V} h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change Γ(X, U.unop) at r
    have hv : P.val.map h (β.app U.unop (fun _ => (1 : Γ(X, U.unop)))) =
        β.app V.unop (fun _ => (1 : Γ(X, V.unop))) :=
      (β.naturality h.unop (fun _ => (1 : Γ(X, U.unop)))).trans
        (congrArg (β.app V.unop) (funext (fun _ => (X.presheaf.map h).hom.map_one)))
    exact (congrArg (fun a : Γ(P, V.unop) => (show Γ(X, V.unop) from X.presheaf.map h r) • a) hv).symm.trans
      (P.val.map_smul h r (β.app U.unop (fun _ => (1 : Γ(X, U.unop))))).symm

theorem LineBundle.Powers.structureModuleTensorMap_postcomp_unitToHom
    (β : Tensor.Powers.SheafMultilinearMap (Line.Bundles.structureModule X) n P) :
    (LineBundle.Powers.structureModuleTensorMap X n).postcomp β.unitToHom = β := by
  apply Tensor.Powers.SheafMultilinearMap.ext
  intro U
  apply MultilinearMap.ext_ring
  change (∏ _i : Fin n, (1 : Γ(X, U))) • β.app U (fun _ => (1 : Γ(X, U))) =
    β.app U (fun _ => (1 : Γ(X, U)))
  simp only [Finset.prod_const_one, one_smul]

theorem LineBundle.Powers.unitToHom_structureModuleTensorMap_postcomp (f : Line.Bundles.structureModule X ⟶ P) :
    ((LineBundle.Powers.structureModuleTensorMap X n).postcomp f).unitToHom = f := by
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro r
  change Γ(X, U) at r
  change r • f.app U (show Γ(X, U) from ∏ _i : Fin n, (1 : Γ(X, U))) = f.app U r
  rw [Finset.prod_const_one]
  have hf := (f.app_smul r (1 : Γ(X, U))).symm
  change r • f.app U (1 : Γ(X, U)) = f.app U (r * (1 : Γ(X, U))) at hf
  exact hf.trans (congrArg (fun a : Γ(X, U) => f.app U a) (mul_one r))

/-- Every tensor power of the structure module is the structure module. -/
theorem LineBundle.Powers.structureModule_isTensorPower (X : Scheme.{u}) (n : ℕ) :
    Tensor.Powers.IsTensorPower (Line.Bundles.structureModule X) n (Line.Bundles.structureModule X) := by
  refine ⟨LineBundle.Powers.structureModuleTensorMap X n, fun P => ?_⟩
  exact ⟨fun f g h => (LineBundle.Powers.unitToHom_structureModuleTensorMap_postcomp f).symm.trans
      ((congrArg Tensor.Powers.SheafMultilinearMap.unitToHom h).trans (LineBundle.Powers.unitToHom_structureModuleTensorMap_postcomp g)),
    fun β => ⟨β.unitToHom, LineBundle.Powers.structureModuleTensorMap_postcomp_unitToHom β⟩⟩

/-- The actual tensor power of a line bundle, with local triviality proved from its frames. -/
def Line.Bundles.LineBundle.tensorPower (L : Line.Bundles.LineBundle X) (n : ℕ) : Line.Bundles.LineBundle X where
  sheaf := TensorPower.PowerSheaf.tensorPowerModule L.sheaf n
  locallyTrivial x := by
    obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyTrivial x
    refine ⟨U, hx, ?_⟩
    exact (((TensorPower.PowerSheaf.tensorPowerModule_isTensorPower L.sheaf n).pullback_of_isOpenImmersion U.ι).of_sourceIso e).unique
      (LineBundle.Powers.structureModule_isTensorPower U.toScheme n)

/-- The constructed line-bundle power satisfies the original tensor-power predicate. -/
theorem Line.Bundles.LineBundle.tensorPower_isTensorPower (L : Line.Bundles.LineBundle X) (n : ℕ) :
    Tensor.Powers.IsTensorPower L.sheaf n (L.tensorPower n).sheaf :=
  TensorPower.PowerSheaf.tensorPowerModule_isTensorPower L.sheaf n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
end ComponentSource_15

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.Powers"

@[expose] public section ComponentSource_16
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps -/

/-! # Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps

noncomputable section

/-! Functorial tensor powers of module sheaves and powers of actual line-bundle sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {L M P Q : X.Modules} {n : ℕ}

/-- The canonical multilinear map into the constructed tensor-power sheaf. -/
def tensorPowerMultilinear (L : X.Modules) (n : ℕ) :
    Tensor.Powers.SheafMultilinearMap L n (PowerSheaf.tensorPowerModule L n) :=
  PowerSheaf.tensorPowerHomEquiv L (PowerSheaf.tensorPowerModule L n) n (𝟙 _)

theorem tensorPowerMultilinear_postcomp (f : PowerSheaf.tensorPowerModule L n ⟶ P) :
    (tensorPowerMultilinear L n).postcomp f = PowerSheaf.tensorPowerHomEquiv L P n f :=
  (PowerSheaf.tensorPowerHomEquiv_postcomp (𝟙 _) f).symm.trans
    (congrArg (PowerSheaf.tensorPowerHomEquiv L P n) (Category.id_comp f))

/-- The canonical multilinear map detects equality of maps out of the tensor power. -/
theorem tensorPower_hom_ext {f h : PowerSheaf.tensorPowerModule L n ⟶ P}
    (he : (tensorPowerMultilinear L n).postcomp f = (tensorPowerMultilinear L n).postcomp h) :
    f = h :=
  (PowerSheaf.tensorPowerHomEquiv L P n).injective
    ((tensorPowerMultilinear_postcomp f).symm.trans
      (he.trans (tensorPowerMultilinear_postcomp h)))

/-- Apply the same module-sheaf morphism to every tensor factor. -/
def tensorPowerMap (f : L ⟶ M) (n : ℕ) : PowerSheaf.tensorPowerModule L n ⟶ PowerSheaf.tensorPowerModule M n :=
  (PowerSheaf.tensorPowerHomEquiv L (PowerSheaf.tensorPowerModule M n) n).symm
    ((tensorPowerMultilinear M n).precomp f)

theorem tensorPowerMap_spec (f : L ⟶ M) (n : ℕ) :
    (tensorPowerMultilinear L n).postcomp (tensorPowerMap f n) =
      (tensorPowerMultilinear M n).precomp f :=
  (tensorPowerMultilinear_postcomp _).trans
    ((PowerSheaf.tensorPowerHomEquiv L (PowerSheaf.tensorPowerModule M n) n).apply_symm_apply _)

@[simp]
theorem tensorPowerMap_id (L : X.Modules) (n : ℕ) : tensorPowerMap (𝟙 L) n = 𝟙 _ := by
  apply tensorPower_hom_ext
  exact (tensorPowerMap_spec (𝟙 L) n).trans
    ((Tensor.Powers.SheafMultilinearMap.precomp_id _).trans (Tensor.Powers.SheafMultilinearMap.postcomp_id _).symm)

theorem tensorPowerMap_comp (f : L ⟶ M) (h : M ⟶ P) (n : ℕ) :
    tensorPowerMap (f ≫ h) n = tensorPowerMap f n ≫ tensorPowerMap h n := by
  apply tensorPower_hom_ext
  calc
    (tensorPowerMultilinear L n).postcomp (tensorPowerMap (f ≫ h) n) =
        (tensorPowerMultilinear P n).precomp (f ≫ h) := tensorPowerMap_spec _ _
    _ = ((tensorPowerMultilinear P n).precomp h).precomp f :=
      (Tensor.Powers.SheafMultilinearMap.precomp_comp _ h f).symm
    _ = ((tensorPowerMultilinear M n).postcomp (tensorPowerMap h n)).precomp f :=
      congrArg (fun β : Tensor.Powers.SheafMultilinearMap M n (PowerSheaf.tensorPowerModule P n) => β.precomp f)
        (tensorPowerMap_spec h n).symm
    _ = ((tensorPowerMultilinear M n).precomp f).postcomp (tensorPowerMap h n) :=
      Tensor.Powers.SheafMultilinearMap.precomp_postcomp _ _ _
    _ = ((tensorPowerMultilinear L n).postcomp (tensorPowerMap f n)).postcomp
        (tensorPowerMap h n) :=
      congrArg (fun β : Tensor.Powers.SheafMultilinearMap L n (PowerSheaf.tensorPowerModule M n) =>
        β.postcomp (tensorPowerMap h n)) (tensorPowerMap_spec f n).symm
    _ = (tensorPowerMultilinear L n).postcomp (tensorPowerMap f n ≫ tensorPowerMap h n) :=
      (Tensor.Powers.SheafMultilinearMap.postcomp_comp _ _ _).symm

/-- Tensor powers form a functor on the actual category of module sheaves. -/
def tensorPowerFunctor (X : Scheme.{u}) (n : ℕ) : X.Modules ⥤ X.Modules where
  obj L := PowerSheaf.tensorPowerModule L n
  map f := tensorPowerMap f n
  map_id L := tensorPowerMap_id L n
  map_comp f h := tensorPowerMap_comp f h n

/-- A map from a tensor power of the unit to the unit is multiplication of its factors. -/
def tensorPowerUnitHom (X : Scheme.{u}) (n : ℕ) :
    PowerSheaf.tensorPowerModule (Line.Bundles.structureModule X) n ⟶ Line.Bundles.structureModule X :=
  (PowerSheaf.tensorPowerHomEquiv (Line.Bundles.structureModule X) (Line.Bundles.structureModule X) n).symm
    (LineBundle.Powers.structureModuleTensorMap X n)

/-- The inverse map is determined by the value of the universal tensor on ones. -/
def tensorPowerUnitInv (X : Scheme.{u}) (n : ℕ) :
    Line.Bundles.structureModule X ⟶ PowerSheaf.tensorPowerModule (Line.Bundles.structureModule X) n :=
  (tensorPowerMultilinear (Line.Bundles.structureModule X) n).unitToHom

theorem tensorPowerUnitHom_spec (X : Scheme.{u}) (n : ℕ) :
    (tensorPowerMultilinear (Line.Bundles.structureModule X) n).postcomp (tensorPowerUnitHom X n) =
      LineBundle.Powers.structureModuleTensorMap X n :=
  (tensorPowerMultilinear_postcomp _).trans
    ((PowerSheaf.tensorPowerHomEquiv (Line.Bundles.structureModule X) (Line.Bundles.structureModule X) n).apply_symm_apply _)

/-- The canonical tensor power of the structure sheaf is canonically the structure sheaf. -/
def tensorPowerUnitIso (X : Scheme.{u}) (n : ℕ) :
    PowerSheaf.tensorPowerModule (Line.Bundles.structureModule X) n ≅ Line.Bundles.structureModule X where
  hom := tensorPowerUnitHom X n
  inv := tensorPowerUnitInv X n
  hom_inv_id := by
    apply tensorPower_hom_ext
    exact (Tensor.Powers.SheafMultilinearMap.postcomp_comp _ _ _).trans
      ((congrArg (fun β : Tensor.Powers.SheafMultilinearMap (Line.Bundles.structureModule X) n (Line.Bundles.structureModule X) =>
        β.postcomp (tensorPowerUnitInv X n)) (tensorPowerUnitHom_spec X n)).trans
          ((LineBundle.Powers.structureModuleTensorMap_postcomp_unitToHom _).trans
            (Tensor.Powers.SheafMultilinearMap.postcomp_id _).symm))
  inv_hom_id := by
    have h := congrArg Tensor.Powers.SheafMultilinearMap.unitToHom (tensorPowerUnitHom_spec X n)
    have he : ((tensorPowerMultilinear (Line.Bundles.structureModule X) n).postcomp
        (tensorPowerUnitHom X n)).unitToHom = tensorPowerUnitInv X n ≫ tensorPowerUnitHom X n := by
      apply Scheme.Modules.hom_ext
      intro U
      apply ConcreteCategory.hom_ext
      intro r
      exact ((tensorPowerUnitHom X n).app_smul r
        ((tensorPowerMultilinear (Line.Bundles.structureModule X) n).app U
          (fun _ => (1 : Γ(X, U))))).symm
    exact he.symm.trans (h.trans (by
      simpa only [Tensor.Powers.SheafMultilinearMap.postcomp_id] using
        (LineBundle.Powers.unitToHom_structureModuleTensorMap_postcomp (X := X) (n := n) (𝟙 (Line.Bundles.structureModule X)))))

/-- Raising a section to a power, as a morphism into the tensor-power sheaf. -/
def tensorPowerSection (s : Line.Bundles.structureModule X ⟶ L) (n : ℕ) :
    Line.Bundles.structureModule X ⟶ PowerSheaf.tensorPowerModule L n :=
  (tensorPowerUnitIso X n).inv ≫ tensorPowerMap s n

/-- On sections, the power of a section is the universal tensor of its repeated value. -/
theorem tensorPowerSection_app (s : Line.Bundles.structureModule X ⟶ L) (n : ℕ) (U : X.Opens)
    (r : Γ(X, U)) :
    (tensorPowerSection s n).app U r =
      r • (tensorPowerMultilinear L n).app U (fun _ => s.app U (1 : Γ(X, U))) := by
  have hs := congrArg (fun β : Tensor.Powers.SheafMultilinearMap (Line.Bundles.structureModule X) n (PowerSheaf.tensorPowerModule L n) =>
    β.app U (fun _ => (1 : Γ(X, U)))) (tensorPowerMap_spec s n)
  change (tensorPowerMap s n).app U
      ((tensorPowerMultilinear (Line.Bundles.structureModule X) n).app U (fun _ => (1 : Γ(X, U)))) =
    (tensorPowerMultilinear L n).app U (fun _ => s.app U (1 : Γ(X, U))) at hs
  exact ((tensorPowerMap s n).app_smul r _).trans
    (congrArg (fun a : Γ(PowerSheaf.tensorPowerModule L n, U) => r • a) hs)

/-- A global frame raises to a global frame in every tensor power. -/
instance tensorPowerSection_isIso (s : Line.Bundles.structureModule X ⟶ L) [IsIso s] (n : ℕ) :
    IsIso (tensorPowerSection s n) := by
  have : IsIso (tensorPowerMap s n) := (tensorPowerFunctor X n).map_isIso s
  dsimp [tensorPowerSection]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps
end ComponentSource_16

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps"

@[expose] public section ComponentSource_17
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps -/

/-! # Restriction Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps

noncomputable section

/-! Canonical restriction comparison for tensor powers, compatible with maps of module sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
  (L : Y.Modules) (n : ℕ)

/-- The restricted tensor-power sheaf has the universal multilinear correspondence. -/
def tensorPowerRestrictHomEquiv (P : X.Modules) :
    ((PowerSheaf.tensorPowerModule L n).restrict f ⟶ P) ≃ Tensor.Powers.SheafMultilinearMap (L.restrict f) n P :=
  ((Scheme.Modules.restrictAdjunction f).homEquiv (PowerSheaf.tensorPowerModule L n) P).trans
    ((PowerSheaf.tensorPowerHomEquiv L ((Scheme.Modules.pushforward f).obj P) n).trans
      (Tensor.Powers.SheafMultilinearMap.restrictHomEquiv f L n P).symm)

theorem tensorPowerRestrictMultilinear_postcomp {P : X.Modules}
    (h : (PowerSheaf.tensorPowerModule L n).restrict f ⟶ P) :
    ((Maps.tensorPowerMultilinear L n).restrict f).postcomp h =
      tensorPowerRestrictHomEquiv f L n P h := by
  apply (Tensor.Powers.SheafMultilinearMap.restrictHomEquiv f L n P).injective
  exact (Tensor.Powers.SheafMultilinearMap.restrictHomEquiv_postcomp _ f h).trans
    ((Maps.tensorPowerMultilinear_postcomp _).trans
      ((Tensor.Powers.SheafMultilinearMap.restrictHomEquiv f L n P).apply_symm_apply _).symm)

theorem tensorPowerRestrict_hom_ext {P : X.Modules}
    {a b : (PowerSheaf.tensorPowerModule L n).restrict f ⟶ P}
    (h : ((Maps.tensorPowerMultilinear L n).restrict f).postcomp a =
      ((Maps.tensorPowerMultilinear L n).restrict f).postcomp b) : a = b :=
  (tensorPowerRestrictHomEquiv f L n P).injective
    ((tensorPowerRestrictMultilinear_postcomp f L n a).symm.trans
      (h.trans (tensorPowerRestrictMultilinear_postcomp f L n b)))

/-- The canonical comparison from the power of the restriction to the restricted power. -/
def tensorPowerRestrictHom : PowerSheaf.tensorPowerModule (L.restrict f) n ⟶ (PowerSheaf.tensorPowerModule L n).restrict f :=
  (PowerSheaf.tensorPowerHomEquiv (L.restrict f) ((PowerSheaf.tensorPowerModule L n).restrict f) n).symm
    ((Maps.tensorPowerMultilinear L n).restrict f)

/-- The inverse comparison, obtained from the restricted universal property. -/
def tensorPowerRestrictInv : (PowerSheaf.tensorPowerModule L n).restrict f ⟶ PowerSheaf.tensorPowerModule (L.restrict f) n :=
  (tensorPowerRestrictHomEquiv f L n (PowerSheaf.tensorPowerModule (L.restrict f) n)).symm
    (Maps.tensorPowerMultilinear (L.restrict f) n)

theorem tensorPowerRestrictHom_spec :
    (Maps.tensorPowerMultilinear (L.restrict f) n).postcomp (tensorPowerRestrictHom f L n) =
      (Maps.tensorPowerMultilinear L n).restrict f :=
  (Maps.tensorPowerMultilinear_postcomp _).trans
    ((PowerSheaf.tensorPowerHomEquiv (L.restrict f) ((PowerSheaf.tensorPowerModule L n).restrict f) n).apply_symm_apply _)

theorem tensorPowerRestrictInv_spec :
    ((Maps.tensorPowerMultilinear L n).restrict f).postcomp (tensorPowerRestrictInv f L n) =
      Maps.tensorPowerMultilinear (L.restrict f) n :=
  (tensorPowerRestrictMultilinear_postcomp f L n _).trans
    ((tensorPowerRestrictHomEquiv f L n (PowerSheaf.tensorPowerModule (L.restrict f) n)).apply_symm_apply _)

/-- Tensor powers commute canonically with restriction to an open subscheme. -/
def tensorPowerRestrictIso : PowerSheaf.tensorPowerModule (L.restrict f) n ≅ (PowerSheaf.tensorPowerModule L n).restrict f where
  hom := tensorPowerRestrictHom f L n
  inv := tensorPowerRestrictInv f L n
  hom_inv_id := by
    apply Maps.tensorPower_hom_ext
    exact (Tensor.Powers.SheafMultilinearMap.postcomp_comp _ _ _).trans
      ((congrArg (fun β : Tensor.Powers.SheafMultilinearMap (L.restrict f) n ((PowerSheaf.tensorPowerModule L n).restrict f) =>
        β.postcomp (tensorPowerRestrictInv f L n)) (tensorPowerRestrictHom_spec f L n)).trans
          ((tensorPowerRestrictInv_spec f L n).trans (Tensor.Powers.SheafMultilinearMap.postcomp_id _).symm))
  inv_hom_id := by
    apply tensorPowerRestrict_hom_ext f L n
    exact (Tensor.Powers.SheafMultilinearMap.postcomp_comp _ _ _).trans
      ((congrArg (fun β : Tensor.Powers.SheafMultilinearMap (L.restrict f) n (PowerSheaf.tensorPowerModule (L.restrict f) n) =>
        β.postcomp (tensorPowerRestrictHom f L n)) (tensorPowerRestrictInv_spec f L n)).trans
          ((tensorPowerRestrictHom_spec f L n).trans (Tensor.Powers.SheafMultilinearMap.postcomp_id _).symm))

variable {L n}

/-- The canonical restriction comparison commutes with maps of all tensor factors. -/
theorem tensorPowerRestrictIso_naturality {M : Y.Modules} (a : L ⟶ M) :
    Maps.tensorPowerMap ((Scheme.Modules.restrictFunctor f).map a) n ≫ (tensorPowerRestrictIso f M n).hom =
      (tensorPowerRestrictIso f L n).hom ≫ (Scheme.Modules.restrictFunctor f).map (Maps.tensorPowerMap a n) := by
  apply Maps.tensorPower_hom_ext
  calc
    (Maps.tensorPowerMultilinear (L.restrict f) n).postcomp
        (Maps.tensorPowerMap ((Scheme.Modules.restrictFunctor f).map a) n ≫
          (tensorPowerRestrictIso f M n).hom) =
      ((Maps.tensorPowerMultilinear (L.restrict f) n).postcomp
        (Maps.tensorPowerMap ((Scheme.Modules.restrictFunctor f).map a) n)).postcomp
          (tensorPowerRestrictIso f M n).hom := Tensor.Powers.SheafMultilinearMap.postcomp_comp _ _ _
    _ = ((Maps.tensorPowerMultilinear (M.restrict f) n).precomp
        ((Scheme.Modules.restrictFunctor f).map a)).postcomp (tensorPowerRestrictIso f M n).hom :=
      congrArg (fun β : Tensor.Powers.SheafMultilinearMap (L.restrict f) n (PowerSheaf.tensorPowerModule (M.restrict f) n) =>
        β.postcomp (tensorPowerRestrictIso f M n).hom) (Maps.tensorPowerMap_spec _ _)
    _ = ((Maps.tensorPowerMultilinear M n).restrict f).precomp ((Scheme.Modules.restrictFunctor f).map a) :=
      (Tensor.Powers.SheafMultilinearMap.precomp_postcomp _ _ _).symm.trans
        (congrArg (fun β : Tensor.Powers.SheafMultilinearMap (M.restrict f) n ((PowerSheaf.tensorPowerModule M n).restrict f) =>
          β.precomp ((Scheme.Modules.restrictFunctor f).map a)) (tensorPowerRestrictHom_spec f M n))
    _ = ((Maps.tensorPowerMultilinear M n).precomp a).restrict f :=
      (Tensor.Powers.SheafMultilinearMap.restrict_precomp _ f a).symm
    _ = ((Maps.tensorPowerMultilinear L n).postcomp (Maps.tensorPowerMap a n)).restrict f :=
      congrArg (fun β : Tensor.Powers.SheafMultilinearMap L n (PowerSheaf.tensorPowerModule M n) => β.restrict f)
        (Maps.tensorPowerMap_spec a n).symm
    _ = ((Maps.tensorPowerMultilinear L n).restrict f).postcomp
        ((Scheme.Modules.restrictFunctor f).map (Maps.tensorPowerMap a n)) :=
      Tensor.Powers.SheafMultilinearMap.restrict_postcomp _ f _
    _ = (Maps.tensorPowerMultilinear (L.restrict f) n).postcomp
        ((tensorPowerRestrictIso f L n).hom ≫ (Scheme.Modules.restrictFunctor f).map (Maps.tensorPowerMap a n)) :=
      (congrArg (fun β : Tensor.Powers.SheafMultilinearMap (L.restrict f) n ((PowerSheaf.tensorPowerModule L n).restrict f) =>
        β.postcomp ((Scheme.Modules.restrictFunctor f).map (Maps.tensorPowerMap a n)))
          (tensorPowerRestrictHom_spec f L n).symm).trans
            (Tensor.Powers.SheafMultilinearMap.postcomp_comp _ _ _).symm

/-- A map that is invertible on an open stays invertible there after taking tensor powers. -/
theorem tensorPowerMap_restrict_isIso {M : Y.Modules} (a : L ⟶ M)
    [IsIso ((Scheme.Modules.restrictFunctor f).map a)] :
    IsIso ((Scheme.Modules.restrictFunctor f).map (Maps.tensorPowerMap a n)) := by
  have : IsIso (Maps.tensorPowerMap ((Scheme.Modules.restrictFunctor f).map a) n) :=
    (Maps.tensorPowerFunctor X n).map_isIso _
  have he := tensorPowerRestrictIso_naturality (n := n) f a
  have : IsIso ((tensorPowerRestrictIso f L n).hom ≫
      (Scheme.Modules.restrictFunctor f).map (Maps.tensorPowerMap a n)) := he ▸ inferInstance
  exact (isIso_comp_left_iff _ _).mp this

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps
end ComponentSource_17

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps"

@[expose] public section ComponentSource_18
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Nonvanishing -/

/-! # Nonvanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Nonvanishing

noncomputable section

/-! Nonvanishing of sections and its behavior under restriction to open subschemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

private theorem isIso_map_of_natIso {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (e : F ≅ G) {M N : C} (s : M ⟶ N) [IsIso (F.map s)] :
    IsIso (G.map s) := by
  have h : e.inv.app M ≫ F.map s ≫ e.hom.app N = G.map s := by
    rw [e.hom.naturality]
    simp
  rw [← h]
  infer_instance

private theorem isIso_map_iff_of_natIso {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (e : F ≅ G) {M N : C} (s : M ⟶ N) :
    IsIso (F.map s) ↔ IsIso (G.map s) := by
  constructor
  · intro h
    let := h
    exact isIso_map_of_natIso e s
  · intro h
    let := h
    exact isIso_map_of_natIso e.symm s

/-- Pullback along a scheme isomorphism reflects invertible module-sheaf maps. -/
theorem isIso_pullback_map_iff (f : X ⟶ Y) [IsIso f] {M N : Y.Modules} (s : M ⟶ N) :
    IsIso ((Scheme.Modules.pullback f).map s) ↔ IsIso s := by
  constructor
  · intro h
    let := h
    have : IsIso ((Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback (inv f)).map s) :=
      inferInstanceAs (IsIso ((Scheme.Modules.pullback (inv f)).map
        ((Scheme.Modules.pullback f).map s)))
    exact isIso_map_of_natIso
      (Scheme.Modules.pullbackComp (inv f) f ≪≫
        Scheme.Modules.pullbackCongr (IsIso.inv_hom_id f) ≪≫ Scheme.Modules.pullbackId Y) s
  · intro h
    let := h
    infer_instance

/-- The choice of the structure-module comparison does not affect invertibility of a section. -/
theorem isIso_pullbackSection_iff (f : X ⟶ Y) {M : Y.Modules} (s : Line.Bundles.structureModule Y ⟶ M) :
    IsIso (Ample.LineBundles.pullbackSection f s) ↔ IsIso ((Scheme.Modules.pullback f).map s) :=
  isIso_comp_left_iff (Line.Bundles.structureModulePullbackIso f).inv ((Scheme.Modules.pullback f).map s)

/-- A local frame remains a local frame under any pullback. -/
instance pullbackSection_isIso (f : X ⟶ Y) {M : Y.Modules}
    (s : Line.Bundles.structureModule Y ⟶ M) [IsIso s] : IsIso (Ample.LineBundles.pullbackSection f s) :=
  (isIso_pullbackSection_iff f s).mpr inferInstance

/-- Successive section pullbacks and composite pullback have the same invertibility condition. -/
theorem isIso_pullbackSection_comp_iff (f : Y ⟶ Z) (h : X ⟶ Y) {M : Z.Modules}
    (s : Line.Bundles.structureModule Z ⟶ M) :
    IsIso (Ample.LineBundles.pullbackSection h (Ample.LineBundles.pullbackSection f s)) ↔ IsIso (Ample.LineBundles.pullbackSection (h ≫ f) s) := by
  simp only [Ample.LineBundles.pullbackSection, Functor.map_comp, isIso_comp_left_iff]
  exact isIso_map_iff_of_natIso (Scheme.Modules.pullbackComp h f) s

/-- Precomposition by an isomorphism does not change the local-frame condition. -/
theorem isIso_pullbackSection_comp_iso_iff (f : Y ⟶ Z) (h : X ⟶ Y) [IsIso h]
    {M : Z.Modules} (s : Line.Bundles.structureModule Z ⟶ M) :
    IsIso (Ample.LineBundles.pullbackSection (h ≫ f) s) ↔ IsIso (Ample.LineBundles.pullbackSection f s) :=
  (isIso_pullbackSection_comp_iff f h s).symm.trans
    ((isIso_pullbackSection_iff h (Ample.LineBundles.pullbackSection f s)).trans
      (isIso_pullback_map_iff h (Ample.LineBundles.pullbackSection f s)))

/-- Frames on an open part of an open subscheme are exactly frames on its image open. -/
theorem isIso_pullbackSection_image_iff (f : X ⟶ Y) [IsOpenImmersion f]
    {M : Y.Modules} (s : Line.Bundles.structureModule Y ⟶ M) (U : X.Opens) :
    IsIso (Ample.LineBundles.pullbackSection U.ι (Ample.LineBundles.pullbackSection f s)) ↔
      IsIso (Ample.LineBundles.pullbackSection (f ''ᵁ U).ι s) :=
  (isIso_pullbackSection_comp_iff f U.ι s).trans
    ((congrArg (fun a : U.toScheme ⟶ Y => IsIso (Ample.LineBundles.pullbackSection a s))
      (f.isoImage_hom_ι U).symm).to_iff.trans
        (isIso_pullbackSection_comp_iso_iff (f ''ᵁ U).ι (f.isoImage U).hom s))

/-- A frame on an open of the target pulls back to a frame on its preimage. -/
theorem isIso_pullbackSection_preimage (f : X ⟶ Y) {M : Y.Modules}
    (s : Line.Bundles.structureModule Y ⟶ M) (V : Y.Opens) [IsIso (Ample.LineBundles.pullbackSection V.ι s)] :
    IsIso (Ample.LineBundles.pullbackSection (f ⁻¹ᵁ V).ι (Ample.LineBundles.pullbackSection f s)) := by
  apply (isIso_pullbackSection_comp_iff f (f ⁻¹ᵁ V).ι s).mpr
  have h : IsIso (Ample.LineBundles.pullbackSection ((f ∣_ V) ≫ V.ι) s) :=
    (isIso_pullbackSection_comp_iff V.ι (f ∣_ V) s).mp inferInstance
  exact (congrArg (fun a : (f ⁻¹ᵁ V).toScheme ⟶ Y => IsIso (Ample.LineBundles.pullbackSection a s))
    (morphismRestrict_ι f V)).mp h

/-- Restricting a section pulls back its nonvanishing open. -/
theorem sectionNonvanishing_pullback (f : X ⟶ Y) [IsOpenImmersion f]
    {M : Y.Modules} (s : Line.Bundles.structureModule Y ⟶ M) :
    Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s) = f ⁻¹ᵁ Ample.LineBundles.sectionNonvanishing s := by
  ext x
  change x ∈ Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection f s) ↔ f x ∈ Ample.LineBundles.sectionNonvanishing s
  simp only [Ample.LineBundles.sectionNonvanishing, TopologicalSpace.Opens.mem_sSup, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨U, hU, hx⟩
    exact ⟨f ''ᵁ U, (isIso_pullbackSection_image_iff f s U).mp hU, ⟨x, hx, rfl⟩⟩
  · rintro ⟨V, hV, hx⟩
    let := hV
    exact ⟨f ⁻¹ᵁ V, isIso_pullbackSection_preimage f s V, hx⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Nonvanishing
end ComponentSource_18

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Nonvanishing"

@[expose] public section ComponentSource_19
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.Nonvanishing -/

/-! # Nonvanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.Nonvanishing

noncomputable section

/-! A section that locally frames a line bundle also frames each of its tensor powers there. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {L M : Y.Modules}

/-- The restriction and pullback functors give the same local invertibility condition. -/
theorem isIso_restrict_map_iff (f : X ⟶ Y) [IsOpenImmersion f] (a : L ⟶ M) :
    IsIso ((Scheme.Modules.restrictFunctor f).map a) ↔
      IsIso ((Scheme.Modules.pullback f).map a) := by
  have h := congrArg (fun z => IsIso z) ((Scheme.Modules.restrictFunctorIsoPullback f).hom.naturality a)
  simpa only [isIso_comp_right_iff, isIso_comp_left_iff] using h.to_iff

/-- Local invertibility of a module morphism implies local invertibility of its tensor power. -/
theorem tensorPowerMap_pullback_isIso (f : X ⟶ Y) [IsOpenImmersion f]
    (a : L ⟶ M) (n : ℕ) [IsIso ((Scheme.Modules.pullback f).map a)] :
    IsIso ((Scheme.Modules.pullback f).map (TensorPower.Maps.tensorPowerMap a n)) := by
  have : IsIso ((Scheme.Modules.restrictFunctor f).map a) :=
    (isIso_restrict_map_iff f a).mpr inferInstance
  exact (isIso_restrict_map_iff f (TensorPower.Maps.tensorPowerMap a n)).mp (TensorPower.RestrictionMaps.tensorPowerMap_restrict_isIso f a)

/-- A frame on an open subscheme raises to a frame on that same open. -/
theorem tensorPowerSection_pullback_isIso (f : X ⟶ Y) [IsOpenImmersion f]
    (s : Line.Bundles.structureModule Y ⟶ L) (n : ℕ) [IsIso (Ample.LineBundles.pullbackSection f s)] :
    IsIso (Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection s n)) := by
  have : IsIso ((Scheme.Modules.pullback f).map s) :=
    (Section.Nonvanishing.isIso_pullbackSection_iff f s).mp inferInstance
  have : IsIso ((Scheme.Modules.pullback f).map (TensorPower.Maps.tensorPowerMap s n)) :=
    tensorPowerMap_pullback_isIso f s n
  apply (Section.Nonvanishing.isIso_pullbackSection_iff f (TensorPower.Maps.tensorPowerSection s n)).mpr
  simp only [TensorPower.Maps.tensorPowerSection, Functor.map_comp]
  infer_instance

/-- Taking a section to a tensor power preserves every point where it already generates. -/
theorem sectionNonvanishing_le_tensorPowerSection (s : Line.Bundles.structureModule Y ⟶ L) (n : ℕ) :
    Ample.LineBundles.sectionNonvanishing s ≤ Ample.LineBundles.sectionNonvanishing (TensorPower.Maps.tensorPowerSection s n) := by
  apply sSup_le
  intro U hU
  have : IsIso (Ample.LineBundles.pullbackSection U.ι s) := hU
  apply le_sSup
  exact tensorPowerSection_pullback_isIso U.ι s n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.Nonvanishing
end ComponentSource_19

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.Nonvanishing"

@[expose] public section ComponentSource_20
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ModuleIsomorphisms -/

/-! # Module Isomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ModuleIsomorphisms

noncomputable section

/-! Local detection of isomorphisms of actual module sheaves on schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {L M : X.Modules}

/-- A module-sheaf map that is invertible on a neighborhood of every point is invertible. -/
theorem moduleMap_isIso_of_locally (a : L ⟶ M)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsIso ((Scheme.Modules.pullback U.ι).map a)) :
    IsIso a := by
  have hs (x : X) : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map a.mapPresheaf) := by
    obtain ⟨U, hx, hU⟩ := h x
    have : IsIso ((Scheme.Modules.restrictFunctor U.ι).map a) :=
      (Power.Nonvanishing.isIso_restrict_map_iff U.ι a).mpr hU
    let y : U.toScheme := ⟨x, hx⟩
    let e := Scheme.Modules.restrictStalkNatIso U.ι y
    have ht : IsIso (((Scheme.Modules.toPresheaf U.toScheme) ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
          ((Scheme.Modules.restrictFunctor U.ι).map a)) :=
      Functor.map_isIso _ _
    have he : IsIso (((Scheme.Modules.restrictFunctor U.ι) ⋙
        Scheme.Modules.toPresheaf U.toScheme ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map a) ↔
        IsIso (((Scheme.Modules.toPresheaf X) ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (U.ι y)).map a) := by
      have hn := congrArg (fun z => IsIso z) (e.hom.naturality a)
      simpa only [isIso_comp_right_iff, isIso_comp_left_iff] using hn.to_iff
    exact he.mp ht
  let b : (⟨L.presheaf, L.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) ⟶
      (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) := ⟨a.mapPresheaf⟩
  have hb : IsIso b := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso b
  have hb' : IsIso ((TopCat.Sheaf.forget AddCommGrpCat.{u} X).map b) :=
    @Functor.map_isIso _ _ _ _ _ _ (TopCat.Sheaf.forget AddCommGrpCat.{u} X) b hb
  have : IsIso ((Scheme.Modules.toPresheaf X).map a) := hb'
  exact isIso_of_reflects_iso a (Scheme.Modules.toPresheaf X)

/-- Local invertibility and global invertibility are equivalent for module-sheaf maps. -/
theorem moduleMap_isIso_iff_locally (a : L ⟶ M) :
    IsIso a ↔ ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsIso ((Scheme.Modules.pullback U.ι).map a) := by
  constructor
  · intro ha x
    let := ha
    exact ⟨⊤, trivial, (Scheme.Modules.pullback (⊤ : X.Opens).ι).map_isIso a⟩
  · exact moduleMap_isIso_of_locally a

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ModuleIsomorphisms
end ComponentSource_20

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ModuleIsomorphisms"

@[expose] public section ComponentSource_21
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Units -/

/-! # Units -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Units

noncomputable section

/-! Positive tensor powers detect invertibility of maps between trivialized line bundles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators

universe u

variable {X : Scheme.{u}}

/-- A structure-module endomorphism acts by multiplication by its value on one. -/
theorem structureModuleEnd_app (a : End (Line.Bundles.structureModule X)) (U : X.Opens) (r : Γ(X, U)) :
    a.asHom.app U r = r * (show Γ(X, U) from a.asHom.app U (1 : Γ(X, U))) := by
  have ha := a.asHom.app_smul r (1 : Γ(X, U))
  change a.asHom.app U (r * (1 : Γ(X, U))) = r * (show Γ(X, U) from a.asHom.app U (1 : Γ(X, U))) at ha
  exact (congrArg (fun z : Γ(X, U) => a.asHom.app U z) (mul_one r)).symm.trans ha

/-- Composition powers of a structure-module endomorphism are ordinary powers of its local function. -/
theorem structureModuleEnd_pow_app (a : End (Line.Bundles.structureModule X)) (n : ℕ) (U : X.Opens)
    (r : Γ(X, U)) :
    (a ^ n).asHom.app U r = r * (show Γ(X, U) from a.asHom.app U (1 : Γ(X, U))) ^ n := by
  induction n with
  | zero =>
    change r = r * (show Γ(X, U) from a.asHom.app U (1 : Γ(X, U))) ^ 0
    rw [pow_zero, mul_one]
  | succ n ih =>
    rw [pow_succ']
    change a.asHom.app U ((a ^ n).asHom.app U r) = _
    exact (structureModuleEnd_app a U _).trans
      ((congrArg (fun z : Γ(X, U) => z * (show Γ(X, U) from a.asHom.app U (1 : Γ(X, U)))) ih).trans
        (by rw [pow_succ, mul_assoc]))

/-- Under the canonical unit comparison, the tensor power of scalar multiplication is its ordinary power. -/
theorem tensorPowerMap_unit_conjugation (a : End (Line.Bundles.structureModule X)) (n : ℕ) :
    (Maps.tensorPowerUnitIso X n).inv ≫ Maps.tensorPowerMap a.asHom n ≫ (Maps.tensorPowerUnitIso X n).hom = (a ^ n).asHom := by
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro r
  change Γ(X, U) at r
  have he := congrArg (fun β : Tensor.Powers.SheafMultilinearMap (Line.Bundles.structureModule X) n (Line.Bundles.structureModule X) =>
    β.app U (fun _ => a.asHom.app U (1 : Γ(X, U)))) (Maps.tensorPowerUnitHom_spec X n)
  change (Maps.tensorPowerUnitHom X n).app U
      ((Maps.tensorPowerMultilinear (Line.Bundles.structureModule X) n).app U
        (fun _ => a.asHom.app U (1 : Γ(X, U)))) =
    (show Γ(X, U) from ∏ _ : Fin n, (show Γ(X, U) from a.asHom.app U (1 : Γ(X, U)))) at he
  change (Maps.tensorPowerUnitHom X n).app U ((Maps.tensorPowerSection a.asHom n).app U r) = (a ^ n).asHom.app U r
  rw [Maps.tensorPowerSection_app]
  let c : Γ(X, U) := a.asHom.app U (1 : Γ(X, U))
  have hp : (∏ _ : Fin n, c) = c ^ n := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hm := (Maps.tensorPowerUnitHom X n).app_smul r
    ((Maps.tensorPowerMultilinear (Line.Bundles.structureModule X) n).app U (fun _ => c))
  change (Maps.tensorPowerUnitHom X n).app U
      (r • (Maps.tensorPowerMultilinear (Line.Bundles.structureModule X) n).app U (fun _ => c)) =
    r * (show Γ(X, U) from (Maps.tensorPowerUnitHom X n).app U
      ((Maps.tensorPowerMultilinear (Line.Bundles.structureModule X) n).app U (fun _ => c))) at hm
  exact hm.trans ((congrArg (fun z : Γ(X, U) => r * z) (he.trans hp)).trans
    (structureModuleEnd_pow_app a n U r).symm)

/-- Taking a positive tensor power reflects invertibility for structure-module endomorphisms. -/
theorem isIso_of_tensorPowerMap_unit (a : End (Line.Bundles.structureModule X)) (n : ℕ) (hn : 0 < n)
    [IsIso (Maps.tensorPowerMap a.asHom n)] : IsIso a.asHom := by
  have : IsIso (a ^ n).asHom := (tensorPowerMap_unit_conjugation a n) ▸ inferInstance
  exact (isUnit_iff_isIso a).mp
    ((isUnit_pow_iff (Nat.ne_of_gt hn)).mp ((isUnit_iff_isIso (a ^ n)).mpr this))

/-- A positive tensor power detects invertibility when both sheaves have chosen line-bundle frames. -/
theorem isIso_of_tensorPowerMap_of_frames {L M : X.Modules} (a : L ⟶ M) (n : ℕ) (hn : 0 < n)
    (e : L ≅ Line.Bundles.structureModule X) (h : M ≅ Line.Bundles.structureModule X)
    [IsIso (Maps.tensorPowerMap a n)] : IsIso a := by
  let b : End (Line.Bundles.structureModule X) := End.of (e.inv ≫ a ≫ h.hom)
  have hb : Maps.tensorPowerMap b.asHom n = Maps.tensorPowerMap e.inv n ≫ Maps.tensorPowerMap a n ≫ Maps.tensorPowerMap h.hom n := by
    dsimp [b]
    rw [Maps.tensorPowerMap_comp, Maps.tensorPowerMap_comp]
  have : IsIso (Maps.tensorPowerMap e.inv n) := (Maps.tensorPowerFunctor X n).map_isIso e.inv
  have : IsIso (Maps.tensorPowerMap h.hom n) := (Maps.tensorPowerFunctor X n).map_isIso h.hom
  have : IsIso (Maps.tensorPowerMap b.asHom n) := hb.symm ▸ inferInstance
  have : IsIso b.asHom := isIso_of_tensorPowerMap_unit b n hn
  have hab : a = e.hom ≫ b.asHom ≫ h.inv := by simp [b]
  rw [hab]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Units
end ComponentSource_21

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Units"

@[expose] public section ComponentSource_22
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Frames -/

/-! # Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Frames

noncomputable section

/-! Actual section frames on nonvanishing opens and regular ratios of sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {L : X.Modules}

/-- A section is a global frame exactly when its nonvanishing open is the whole scheme. -/
theorem isIso_iff_sectionNonvanishing_eq_top (s : Line.Bundles.structureModule X ⟶ L) :
    IsIso s ↔ Ample.LineBundles.sectionNonvanishing s = ⊤ := by
  constructor
  · intro hs
    let := hs
    exact Ample.LineBundles.sectionNonvanishing_of_isIso s
  · intro hs
    apply Local.ModuleIsomorphisms.moduleMap_isIso_of_locally s
    intro x
    have hx : x ∈ Ample.LineBundles.sectionNonvanishing s := hs.symm ▸ (show x ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨U, hU, hxU⟩ := TopologicalSpace.Opens.mem_sSup.mp hx
    change X.Opens at U
    exact ⟨U, hxU, (Nonvanishing.isIso_pullbackSection_iff U.ι s).mp hU⟩

/-- A section really is invertible on its entire nonvanishing open. -/
instance pullbackSection_nonvanishing_isIso (s : Line.Bundles.structureModule X ⟶ L) :
    IsIso (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι s) := by
  apply (isIso_iff_sectionNonvanishing_eq_top _).mpr
  rw [Nonvanishing.sectionNonvanishing_pullback]
  ext x
  change (Ample.LineBundles.sectionNonvanishing s).ι x ∈ Ample.LineBundles.sectionNonvanishing s ↔ True
  exact iff_true_intro x.property

/-- The canonical frame supplied by a section on its nonvanishing open. -/
def sectionFrameIso (s : Line.Bundles.structureModule X ⟶ L) :
    Line.Bundles.structureModule (Ample.LineBundles.sectionNonvanishing s).toScheme ≅
      (Scheme.Modules.pullback (Ample.LineBundles.sectionNonvanishing s).ι).obj L :=
  asIso (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι s)

/-- On the nonvanishing open of s, divide another section by the frame s. -/
def sectionRatioEnd (s t : Line.Bundles.structureModule X ⟶ L) :
    End (Line.Bundles.structureModule (Ample.LineBundles.sectionNonvanishing s).toScheme) :=
  End.of (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι t ≫ (sectionFrameIso s).inv)

/-- The quotient of two sections is a regular function where the denominator is nonvanishing. -/
def sectionRatio (s t : Line.Bundles.structureModule X ⟶ L) : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤) :=
  (sectionRatioEnd s t).asHom.app ⊤ (1 : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤))

/-- The quotient recovers the numerator when multiplied by the denominator frame. -/
theorem sectionRatioEnd_frame (s t : Line.Bundles.structureModule X ⟶ L) :
    (sectionRatioEnd s t).asHom ≫ (sectionFrameIso s).hom =
      Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι t := by
  simp only [sectionRatioEnd, Category.assoc, Iso.inv_hom_id, Category.comp_id]

@[simp]
theorem sectionRatioEnd_self (s : Line.Bundles.structureModule X ⟶ L) : sectionRatioEnd s s = 1 := by
  apply End.ext
  exact (sectionFrameIso s).hom_inv_id

@[simp]
theorem sectionRatio_self (s : Line.Bundles.structureModule X ⟶ L) : sectionRatio s s = 1 := by
  change (sectionRatioEnd s s).asHom.app ⊤ (1 : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤)) = _
  rw [sectionRatioEnd_self]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Frames
end ComponentSource_22

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Frames"

@[expose] public section ComponentSource_23
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates -/

/-! # Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates

noncomputable section

/-! Regular coordinates in a line-bundle frame and their change-of-frame identities. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {L : X.Modules}

/-- A structure-module endomorphism determines its global scalar as a ring homomorphism. -/
def structureModuleEndValue (X : Scheme.{u}) : End (Line.Bundles.structureModule X) →+* Γ(X, ⊤) where
  toFun a := a.asHom.app ⊤ (1 : Γ(X, ⊤))
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' a b :=
    (TensorPower.Units.structureModuleEnd_app a ⊤ (show Γ(X, ⊤) from b.asHom.app ⊤ (1 : Γ(X, ⊤)))).trans
      (mul_comm (show Γ(X, ⊤) from b.asHom.app ⊤ (1 : Γ(X, ⊤)))
        (show Γ(X, ⊤) from a.asHom.app ⊤ (1 : Γ(X, ⊤))))

/-- The endomorphism obtained by writing a section in a global frame. -/
def frameCoordinateEnd (s t : Line.Bundles.structureModule X ⟶ L) [IsIso s] : End (Line.Bundles.structureModule X) :=
  End.of (t ≫ inv s)

/-- The global regular function giving the coordinate of a section in a frame. -/
def frameCoordinate (s t : Line.Bundles.structureModule X ⟶ L) [IsIso s] : Γ(X, ⊤) :=
  structureModuleEndValue X (frameCoordinateEnd s t)

theorem frameCoordinateEnd_frame (s t : Line.Bundles.structureModule X ⟶ L) [IsIso s] :
    (frameCoordinateEnd s t).asHom ≫ s = t := by
  simp only [frameCoordinateEnd, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

@[simp]
theorem frameCoordinate_self (s : Line.Bundles.structureModule X ⟶ L) [IsIso s] : frameCoordinate s s = 1 := by
  change structureModuleEndValue X (End.of (s ≫ inv s)) = 1
  rw [IsIso.hom_inv_id]
  exact map_one (structureModuleEndValue X)

/-- The transition function between two frames is a unit. -/
theorem frameCoordinate_isUnit (s t : Line.Bundles.structureModule X ⟶ L) [IsIso s] [IsIso t] :
    IsUnit (frameCoordinate s t) := by
  have : IsIso (frameCoordinateEnd s t).asHom := by dsimp [frameCoordinateEnd]; infer_instance
  exact ((isUnit_iff_isIso (frameCoordinateEnd s t)).mpr this).map (structureModuleEndValue X)

/-- Changing the frame multiplies every coordinate by the same transition function. -/
theorem frameCoordinate_change (s t r : Line.Bundles.structureModule X ⟶ L) [IsIso s] [IsIso t] :
    frameCoordinate s r = frameCoordinate s t * frameCoordinate t r := by
  have he : frameCoordinateEnd s r = frameCoordinateEnd s t * frameCoordinateEnd t r := by
    apply End.ext
    change r ≫ inv s = (r ≫ inv t) ≫ (t ≫ inv s)
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  exact (congrArg (structureModuleEndValue X) he).trans (map_mul (structureModuleEndValue X) _ _)

/-- The section-ratio construction is the regular coordinate in its canonical denominator frame. -/
theorem sectionRatio_eq_frameCoordinate (s t : Line.Bundles.structureModule X ⟶ L) :
    Section.Frames.sectionRatio s t = frameCoordinate
      (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι s)
      (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι t) := by
  simp only [Section.Frames.sectionRatio, frameCoordinate, structureModuleEndValue,
    Section.Frames.sectionRatioEnd, frameCoordinateEnd, Section.Frames.sectionFrameIso, asIso_inv]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates
end ComponentSource_23

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates"

@[expose] public section ComponentSource_24
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections -/

/-! # Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections

noncomputable section

/-! Global sections as actual module-sheaf maps, and scalars as endomorphisms of the structure module. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

/-- A compatible family of sections is determined by its value on the whole scheme. -/
def moduleSectionsTopEquiv (L : X.Modules) : L.sections ≃ Γ(L, ⊤) where
  toFun s := s.val (.op ⊤)
  invFun z := PresheafOfModules.sectionsMk
    (fun U => L.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op z)
    (fun {U V} h => by
      exact (ConcreteCategory.congr_hom
        (L.presheaf.map_comp (homOfLE (show U.unop ≤ ⊤ from le_top)).op h) z).symm)
  left_inv s := by
    apply Subtype.ext
    funext U
    exact s.property (homOfLE (show U.unop ≤ ⊤ from le_top)).op
  right_inv z := ConcreteCategory.congr_hom (L.presheaf.map_id (.op ⊤)) z

/-- Global sections of a module sheaf are morphisms from the structure module. -/
def moduleSectionHomEquiv (L : X.Modules) : (Line.Bundles.structureModule X ⟶ L) ≃ Γ(L, ⊤) :=
  L.unitHomEquiv.trans (moduleSectionsTopEquiv L)

@[simp]
theorem moduleSectionHomEquiv_apply (L : X.Modules) (s : Line.Bundles.structureModule X ⟶ L) :
    moduleSectionHomEquiv L s = s.app ⊤ (1 : Γ(X, ⊤)) := rfl

/-- The scalar of a structure-module endomorphism determines that endomorphism uniquely. -/
theorem structureModuleEndValue_injective (X : Scheme.{u}) :
    Function.Injective (Frame.Coordinates.structureModuleEndValue X) :=
  ((End.homEquiv (X := Line.Bundles.structureModule X)).trans (moduleSectionHomEquiv (Line.Bundles.structureModule X))).injective

/-- Every global function is the scalar of a structure-module endomorphism. -/
theorem structureModuleEndValue_surjective (X : Scheme.{u}) :
    Function.Surjective (Frame.Coordinates.structureModuleEndValue X) :=
  ((End.homEquiv (X := Line.Bundles.structureModule X)).trans (moduleSectionHomEquiv (Line.Bundles.structureModule X))).surjective

/-- The endomorphism ring of the structure module is the ring of global functions. -/
def structureModuleEndRingEquiv (X : Scheme.{u}) : End (Line.Bundles.structureModule X) ≃+* Γ(X, ⊤) :=
  RingEquiv.ofBijective (Frame.Coordinates.structureModuleEndValue X)
    ⟨structureModuleEndValue_injective X, structureModuleEndValue_surjective X⟩

/-- A structure-module endomorphism is invertible exactly when its global scalar is a unit. -/
theorem structureModuleEnd_isIso_iff (a : End (Line.Bundles.structureModule X)) :
    IsIso a.asHom ↔ IsUnit (Frame.Coordinates.structureModuleEndValue X a) := by
  rw [← isUnit_iff_isIso]
  constructor
  · exact fun h => h.map (Frame.Coordinates.structureModuleEndValue X)
  · intro h
    have hi := h.map (structureModuleEndRingEquiv X).symm.toRingHom
    exact (congrArg IsUnit ((structureModuleEndRingEquiv X).symm_apply_apply a)).mp hi

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections
end ComponentSource_24

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections"

@[expose] public section ComponentSource_25
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.SectionMapValues -/

/-! # Section Map Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.SectionMapValues

noncomputable section

/-! A section viewed as a module-sheaf morphism acts on each open by multiplying its restricted value. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

theorem moduleSectionHomEquiv_symm_app (M : X.Modules) (z : Γ(M, ⊤)) (V : X.Opens) (r : Γ(X, V)) :
    ((Sections.moduleSectionHomEquiv M).symm z).app V r =
      r • M.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op z := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.SectionMapValues
end ComponentSource_25

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.SectionMapValues"

@[expose] public section ComponentSource_26
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.LocalSections -/

/-! # Local Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.LocalSections

noncomputable section

/-! The constructed frame sheaf has canonical sections on each chart, with explicit values on every smaller open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (D : Transitions.OpenFrameTransitions U)

theorem openInclusionImage_le (V : X.Opens) (W : V.toScheme.Opens) : V.ι ''ᵁ W ≤ V := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

def openFrameLocalSection (k : ι) :
    Line.Bundles.structureModule (U k).toScheme ⟶ (ModuleSheaf.openFrameModuleSheaf D).restrict (U k).ι :=
  (Global.Sections.moduleSectionHomEquiv ((ModuleSheaf.openFrameModuleSheaf D).restrict (U k).ι)).symm
    (SectionGenerators.openFrameGenerator D ((U k).ι ''ᵁ ⊤) k (openInclusionImage_le (U k) ⊤) 1)

theorem openFrameLocalSection_app (k : ι) (W : (U k).toScheme.Opens) (r : Γ((U k).toScheme, W)) :
    (openFrameLocalSection D k).app W r =
      SectionGenerators.openFrameGenerator D ((U k).ι ''ᵁ W) k (openInclusionImage_le (U k) W)
        (((U k).ι.appIso W).inv r) := by
  let f := (U k).ι
  let V₀ := f ''ᵁ (⊤ : (U k).toScheme.Opens)
  let V := f ''ᵁ W
  have h : V ≤ V₀ := f.image_mono le_top
  have hg : RestrictionCompatibility.openFrameSectionRestriction D h
      (SectionGenerators.openFrameGenerator D V₀ k (openInclusionImage_le (U k) ⊤) 1) =
        SectionGenerators.openFrameGenerator D V k (openInclusionImage_le (U k) W) 1 :=
    (GeneratorNaturality.openFrameGenerator_restriction D h k (openInclusionImage_le (U k) ⊤) 1).trans
      (congrArg (SectionGenerators.openFrameGenerator D V k (openInclusionImage_le (U k) W))
        (X.presheaf.map (homOfLE h).op).hom.map_one)
  refine (Global.SectionMapValues.moduleSectionHomEquiv_symm_app ((ModuleSheaf.openFrameModuleSheaf D).restrict f)
    (SectionGenerators.openFrameGenerator D V₀ k (openInclusionImage_le (U k) ⊤) 1) W r).trans ?_
  change ((f.appIso W).inv r) • RestrictionCompatibility.openFrameSectionRestriction D h
      (SectionGenerators.openFrameGenerator D V₀ k (openInclusionImage_le (U k) ⊤) 1) =
    SectionGenerators.openFrameGenerator D V k (openInclusionImage_le (U k) W) ((f.appIso W).inv r)
  exact (congrArg (fun z : SectionModules.openFrameSectionModule U D V => ((f.appIso W).inv r) • z) hg).trans
    (GeneratorNaturality.openFrameGenerator_smul_one D V k (openInclusionImage_le (U k) W) ((f.appIso W).inv r))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.LocalSections
end ComponentSource_26

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.LocalSections"

@[expose] public section ComponentSource_27
/- Original module: OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Locality -/

/-! # Locality -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Locality

noncomputable section

/-!
# Local detection of line bundles for PoincareBundle
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- A trivialization on an open subset of an open subscheme gives a
trivialization on its image in the ambient scheme. -/
def imageTrivialization {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (V : Scheme.Opens U)
    (e : (Scheme.Modules.pullback V.ι).obj ((Scheme.Modules.pullback U.ι).obj M) ≅
      Bundles.unitLine V) :
    (Scheme.Modules.pullback (U.ι ''ᵁ V).ι).obj M ≅
      Bundles.unitLine (U.ι ''ᵁ V) := by
  let a := (U.ι.isoImage V).inv
  exact (Scheme.Modules.pullbackCongr (U.ι.isoImage_inv_ι V).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp a (V.ι ≫ U.ι)).app M).symm ≪≫
    (Scheme.Modules.pullback a).mapIso
      (((Scheme.Modules.pullbackComp V.ι U.ι).app M).symm ≪≫ e) ≪≫
    Bundles.pullbackUnitIso a

/-- Local rank one can be checked on an open neighborhood of every point. -/
theorem isLine_of_locally_isLine {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Bundles.IsLine ((Scheme.Modules.pullback U.ι).obj M)) :
    Bundles.IsLine M := by
  intro x
  obtain ⟨U, hx, hU⟩ := h x
  obtain ⟨V, hxV, ⟨e⟩⟩ := hU ⟨x, hx⟩
  refine ⟨U.ι ''ᵁ V, ?_, ⟨imageTrivialization M U V e⟩⟩
  exact ⟨⟨x, hx⟩, hxV, rfl⟩

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Locality
end ComponentSource_27

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Locality"

@[expose] public section ComponentSource_28
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MatchingRecovery -/

/-! # Matching Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule

noncomputable section

/-! The matching-section sheaf recovers every original local module.
Consequently actual line objects, rather than merely their classes,
descend along an open cover with specified coherent transitions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
universe u
variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} {M : ι → X.Modules}
  (D : MatchingSheaf.OpenModuleTransitions U M)

def MatchingSheaf.OpenModuleTransitions.evaluation (V : X.Opens) (i : ι) (hV : V ≤ U i) :
    D.sections V →ₗ[Γ(X, V)] Γ(M i, V) where
  toFun s := (M i).presheaf.map (homOfLE (le_inf le_rfl hV)).op (s.val i)
  map_add' s t := map_add _ _ _
  map_smul' r s := by
    let si : Γ(M i, V ⊓ U i) := s.val i
    let a : V ≤ V ⊓ U i := le_inf le_rfl hV
    let b : V ⊓ U i ≤ V := inf_le_left
    change (M i).presheaf.map (homOfLE (le_inf le_rfl hV)).op
        (@SMul.smul Γ(X, V ⊓ U i) Γ(M i, V ⊓ U i) inferInstance
          (X.presheaf.map (homOfLE b).op r) si) =
      r • (M i).presheaf.map (homOfLE a).op si
    have hr : X.presheaf.map (homOfLE a).op (X.presheaf.map (homOfLE b).op r) = r :=
      (Relative.OpenFunctionUnits.openFunction_restriction_comp b a r).trans
        (ConcreteCategory.congr_hom (X.presheaf.map_id (.op V)) r)
    exact (Scheme.Modules.map_smul (M i) (homOfLE a) _ si).trans
      (congrArg (fun z : Γ(X, V) => z • (M i).presheaf.map (homOfLE a).op si) hr)

def MatchingSheaf.OpenModuleTransitions.generatorTuple (V : X.Opens) (i : ι) (hV : V ≤ U i) (s : Γ(M i, V)) : MatchingSheaf.OpenModuleTransitions.Tuple U M V :=
  fun j => D.compare (V ⊓ U j) i j (inf_le_left.trans hV) inf_le_right
    ((M i).presheaf.map (homOfLE (show V ⊓ U j ≤ V from inf_le_left)).op s)

theorem MatchingSheaf.OpenModuleTransitions.generatorTuple_mem (V : X.Opens) (i : ι) (hV : V ≤ U i) (s : Γ(M i, V)) :
    D.generatorTuple V i hV s ∈ D.sections V := by
  intro j k
  let Q := (V ⊓ U j) ⊓ U k
  have qV : Q ≤ V := inf_le_left.trans inf_le_left
  have qj : Q ≤ V ⊓ U j := inf_le_left
  have qk : Q ≤ V ⊓ U k := le_inf qV inf_le_right
  have hj : (M j).presheaf.map (homOfLE qj).op (D.generatorTuple V i hV s j) =
      D.compare Q i j (qV.trans hV) (inf_le_left.trans inf_le_right)
        ((M i).presheaf.map (homOfLE qV).op s) :=
    (D.natural (V ⊓ U j) Q qj i j _ _ _).symm.trans
      (congrArg (D.compare Q i j _ _) (MatchingSheaf.OpenModuleTransitions.restriction_comp (M i) _ _ _))
  have hk : (M k).presheaf.map (homOfLE qk).op (D.generatorTuple V i hV s k) =
      D.compare Q i k (qV.trans hV) inf_le_right
        ((M i).presheaf.map (homOfLE qV).op s) :=
    (D.natural (V ⊓ U k) Q qk i k _ _ _).symm.trans
      (congrArg (D.compare Q i k _ _) (MatchingSheaf.OpenModuleTransitions.restriction_comp (M i) _ _ _))
  exact (congrArg (D.compare Q j k _ _) hj).trans
    ((D.composition Q i j k _ _ _ _).trans hk.symm)

def MatchingSheaf.OpenModuleTransitions.generator (V : X.Opens) (i : ι) (hV : V ≤ U i) :
    Γ(M i, V) →ₗ[Γ(X, V)] D.sections V where
  toFun s := ⟨D.generatorTuple V i hV s, D.generatorTuple_mem V i hV s⟩
  map_add' s t := by
    apply Subtype.ext
    funext j
    change D.compare _ _ _ _ _ ((M i).presheaf.map _ (s + t)) = _
    rw [map_add, map_add]
    rfl
  map_smul' r s := by
    apply Subtype.ext
    funext j
    change D.compare (V ⊓ U j) i j _ _
        ((M i).presheaf.map (homOfLE (show V ⊓ U j ≤ V from inf_le_left)).op (r • s)) =
      (X.presheaf.map (homOfLE (show V ⊓ U j ≤ V from inf_le_left)).op r) •
        D.compare (V ⊓ U j) i j _ _
          ((M i).presheaf.map (homOfLE (show V ⊓ U j ≤ V from inf_le_left)).op s)
    rw [Scheme.Modules.map_smul, map_smul]

theorem MatchingSheaf.OpenModuleTransitions.evaluation_generator (V : X.Opens) (i : ι) (hV : V ≤ U i) (s : Γ(M i, V)) :
    D.evaluation V i hV (D.generator V i hV s) = s := by
  change (M i).presheaf.map (homOfLE (le_inf le_rfl hV)).op
    (D.compare (V ⊓ U i) i i _ _
      ((M i).presheaf.map (homOfLE (show V ⊓ U i ≤ V from inf_le_left)).op s)) = s
  rw [D.identity, MatchingSheaf.OpenModuleTransitions.restriction_comp, MatchingSheaf.OpenModuleTransitions.restriction_self]

theorem MatchingSheaf.OpenModuleTransitions.generator_evaluation (V : X.Opens) (i : ι) (hV : V ≤ U i) (s : D.sections V) :
    D.generator V i hV (D.evaluation V i hV s) = s := by
  apply Subtype.ext
  funext j
  let Q := (V ⊓ U i) ⊓ U j
  have hQ : V ⊓ U j ≤ Q := le_inf (le_inf inf_le_left (inf_le_left.trans hV)) inf_le_right
  have he := congrArg ((M j).presheaf.map (homOfLE hQ).op) (s.property i j)
  have hl : D.generatorTuple V i hV (D.evaluation V i hV s) j =
      (M j).presheaf.map (homOfLE hQ).op
        (D.compare Q i j (inf_le_left.trans inf_le_right) inf_le_right
          ((M i).presheaf.map (homOfLE (show Q ≤ V ⊓ U i from inf_le_left)).op (s.val i))) := by
    change D.compare (V ⊓ U j) i j _ _
        ((M i).presheaf.map (homOfLE (show V ⊓ U j ≤ V from inf_le_left)).op
          ((M i).presheaf.map (homOfLE (le_inf le_rfl hV)).op (s.val i))) = _
    rw [← D.natural Q (V ⊓ U j) hQ i j]
    congr 1
    exact (MatchingSheaf.OpenModuleTransitions.restriction_comp (M i) _ _ _).trans (MatchingSheaf.OpenModuleTransitions.restriction_comp (M i) _ _ _).symm
  exact hl.trans (he.trans ((MatchingSheaf.OpenModuleTransitions.restriction_comp (M j) _ _ _).trans (MatchingSheaf.OpenModuleTransitions.restriction_self (M j) _ _ _)))

def MatchingSheaf.OpenModuleTransitions.evaluationEquiv (V : X.Opens) (i : ι) (hV : V ≤ U i) :
    D.sections V ≃ₗ[Γ(X, V)] Γ(M i, V) where
  __ := D.evaluation V i hV
  invFun := D.generator V i hV
  left_inv := D.generator_evaluation V i hV
  right_inv := D.evaluation_generator V i hV

theorem MatchingSheaf.OpenModuleTransitions.evaluation_natural {V W : X.Opens} (h : W ≤ V) (i : ι) (hV : V ≤ U i)
    (s : D.sections V) :
    D.evaluation W i (h.trans hV) (D.sectionRestriction h s) =
      (M i).presheaf.map (homOfLE h).op (D.evaluation V i hV s) := by
  exact (MatchingSheaf.OpenModuleTransitions.restriction_comp (M i) _ _ _).trans (MatchingSheaf.OpenModuleTransitions.restriction_comp (M i) _ _ _).symm

theorem MatchingSheaf.OpenModuleTransitions.evaluation_generator_other (V : X.Opens) (i j : ι)
    (hi : V ≤ U i) (hj : V ≤ U j) (s : Γ(M i, V)) :
    D.evaluation V j hj (D.generator V i hi s) = D.compare V i j hi hj s := by
  change (M j).presheaf.map (homOfLE (le_inf le_rfl hj)).op
    (D.compare (V ⊓ U j) i j _ _
      ((M i).presheaf.map (homOfLE (show V ⊓ U j ≤ V from inf_le_left)).op s)) = _
  rw [← D.natural (V ⊓ U j) V (le_inf le_rfl hj) i j,
    MatchingSheaf.OpenModuleTransitions.restriction_comp, MatchingSheaf.OpenModuleTransitions.restriction_self]

/-- The local recovery maps realize the specified overlap comparison. -/
theorem MatchingSheaf.OpenModuleTransitions.evaluation_compare (V : X.Opens) (i j : ι) (hi : V ≤ U i) (hj : V ≤ U j)
    (s : D.sections V) :
    D.compare V i j hi hj (D.evaluation V i hi s) = D.evaluation V j hj s :=
  (D.evaluation_generator_other V i j hi hj (D.evaluation V i hi s)).symm.trans
    (congrArg (D.evaluation V j hj) (D.generator_evaluation V i hi s))

local instance MatchingSheaf.OpenModuleTransitions.matchingRestrictionModule (i : ι) (W : (U i).toScheme.Opensᵒᵖ) :
    Module Γ((U i).toScheme, W.unop) ((D.moduleSheaf.restrict (U i).ι).val.obj W) :=
  ((D.moduleSheaf.restrict (U i).ι).val.obj W).isModule

local instance MatchingSheaf.OpenModuleTransitions.originalRestrictionModule (i : ι) (W : (U i).toScheme.Opensᵒᵖ) :
    Module Γ((U i).toScheme, W.unop) (((M i).restrict (U i).ι).val.obj W) :=
  (((M i).restrict (U i).ι).val.obj W).isModule

def MatchingSheaf.OpenModuleTransitions.recoveryHom (i : ι) : D.moduleSheaf.restrict (U i).ι ⟶ (M i).restrict (U i).ι where
  val.app W := ModuleCat.ofHom
    (X := (D.moduleSheaf.restrict (U i).ι).val.obj W)
    (Y := ((M i).restrict (U i).ι).val.obj W)
    { toFun := D.evaluation ((U i).ι ''ᵁ W.unop) i (OpenFrame.LocalSections.openInclusionImage_le (U i) W.unop)
      map_add' s t := (D.evaluation ((U i).ι ''ᵁ W.unop) i
        (OpenFrame.LocalSections.openInclusionImage_le (U i) W.unop)).map_add s t
      map_smul' r s := by
        exact (D.evaluation ((U i).ι ''ᵁ W.unop) i
          (OpenFrame.LocalSections.openInclusionImage_le (U i) W.unop)).map_smul
            (((U i).ι.appIso W.unop).inv r) s }
  val.naturality {V W} f := by
    ext s
    exact D.evaluation_natural ((U i).ι.image_mono f.unop.le) i
      (OpenFrame.LocalSections.openInclusionImage_le (U i) V.unop) s

instance MatchingSheaf.OpenModuleTransitions.recoveryHom_isIso (i : ι) : IsIso (D.recoveryHom i) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro W
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  change Function.Bijective (D.evaluation ((U i).ι ''ᵁ W) i (OpenFrame.LocalSections.openInclusionImage_le (U i) W))
  exact (D.evaluationEquiv ((U i).ι ''ᵁ W) i (OpenFrame.LocalSections.openInclusionImage_le (U i) W)).bijective

/-- The descended module restricts to the original local module. -/
def MatchingSheaf.OpenModuleTransitions.recoveryIso (i : ι) : D.moduleSheaf.restrict (U i).ι ≅ (M i).restrict (U i).ι :=
  asIso (D.recoveryHom i)

variable (hU : ∀ x : X, ∃ i, x ∈ U i)
  (L : ∀ i, Line.Bundles.LineBundle (U i).toScheme)
  (r : ∀ i, (M i).restrict (U i).ι ≅ (L i).sheaf)

def MatchingSheaf.OpenModuleTransitions.localLineRecovery (i : ι) :
    (Scheme.Modules.pullback (U i).ι).obj D.moduleSheaf ≅ (L i).sheaf :=
  (Scheme.Modules.restrictFunctorIsoPullback (U i).ι).symm.app D.moduleSheaf ≪≫
    D.recoveryIso i ≪≫ r i

/-- Coherent local line objects produce an actual global line bundle. -/
def MatchingSheaf.OpenModuleTransitions.lineBundle : Line.Bundles.LineBundle X where
  sheaf := D.moduleSheaf
  locallyTrivial := by
    apply Picard.PoincareBundle.Line.Locality.isLine_of_locally_isLine
    intro x
    obtain ⟨i, hi⟩ := hU x
    refine ⟨U i, hi, ?_⟩
    exact Picard.PoincareBundle.Line.Bundles.IsLine.of_iso (L i).locallyTrivial
      (D.localLineRecovery L r i).symm

def MatchingSheaf.OpenModuleTransitions.lineBundle_recovery (i : ι) :
    ((D.lineBundle hU L r).pullback (U i).ι).sheaf ≅ (L i).sheaf :=
  D.localLineRecovery L r i

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule
end ComponentSource_28

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MatchingRecovery"

@[expose] public section ComponentSource_29
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapBasisExtension -/

/-! # Map Basis Extension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapBasisExtension

noncomputable section

/-! Compatible linear maps on a topological basis extend to actual module-sheaf maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u v

variable {X : Scheme.{u}} {ι : Type v} (B : ι → X.Opens) (M N : X.Modules)

structure ModuleBasisMap where
  app : ∀ i, Γ(M, B i) →ₗ[Γ(X, B i)] Γ(N, B i)
  naturality : ∀ i j (h : B i ≤ B j) (s : Γ(M, B j)),
    app i (M.presheaf.map (homOfLE h).op s) =
      N.presheaf.map (homOfLE h).op (app j s)

namespace ModuleBasisMap

variable {B M N} (D : ModuleBasisMap B M N)

def presheafMap :
    (inducedFunctor B).op ⋙ M.presheaf ⟶ (inducedFunctor B).op ⋙ N.presheaf where
  app i := AddCommGrpCat.ofHom (D.app i.unop).toAddMonoidHom
  naturality {i j} h := by
    apply ConcreteCategory.hom_ext
    intro s
    exact D.naturality j.unop i.unop h.unop.hom.le s

variable (hB : Opens.IsBasis (Set.range B))

def extendedPresheafMap : M.presheaf ⟶ N.presheaf :=
  TopCat.Sheaf.restrictHomEquivHom M.presheaf ⟨N.presheaf, N.isSheaf⟩ hB D.presheafMap

theorem extendedPresheafMap_app (i : ι) (s : Γ(M, B i)) :
    (D.extendedPresheafMap hB).app (.op (B i)) s = D.app i s := by
  exact ConcreteCategory.congr_hom
    (TopCat.Sheaf.extend_hom_app M.presheaf ⟨N.presheaf, N.isSheaf⟩ hB D.presheafMap i) s

theorem extendedPresheafMap_smul (U : X.Opens) (r : Γ(X, U)) (s : Γ(M, U)) :
    (D.extendedPresheafMap hB).app (.op U) (r • s) =
      r • (D.extendedPresheafMap hB).app (.op U) s := by
  apply N.isSheaf.section_ext
  intro x hx
  obtain ⟨V, ⟨i, rfl⟩, hxi, hi⟩ := Opens.isBasis_iff_nbhd.mp hB hx
  refine ⟨B i, hi, hxi, ?_⟩
  have hn (z : Γ(M, U)) :
      N.presheaf.map (homOfLE hi).op ((D.extendedPresheafMap hB).app (.op U) z) =
        D.app i (M.presheaf.map (homOfLE hi).op z) :=
    (ConcreteCategory.congr_hom ((D.extendedPresheafMap hB).naturality (homOfLE hi).op) z).symm.trans
      (D.extendedPresheafMap_app hB i _)
  rw [hn, Scheme.Modules.map_smul, Scheme.Modules.map_smul, hn, map_smul]

def extend : M ⟶ N where
  val := {
    app U := ModuleCat.ofHom {
      toFun := (D.extendedPresheafMap hB).app U
      map_add' := map_add ((D.extendedPresheafMap hB).app U).hom
      map_smul' := D.extendedPresheafMap_smul hB U.unop }
    naturality h := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      exact ConcreteCategory.congr_hom ((D.extendedPresheafMap hB).naturality h) s }

theorem extend_app (i : ι) (s : Γ(M, B i)) : (D.extend hB).app (B i) s = D.app i s :=
  D.extendedPresheafMap_app hB i s

end ModuleBasisMap

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapBasisExtension
end ComponentSource_29

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapBasisExtension"

@[expose] public section ComponentSource_30
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapLocalFactor -/

/-! # Map Local Factor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapLocalFactor

noncomputable section

/-! Linear local factorizations through a module map that is invertible on the chosen open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {M N P : X.Modules}

def moduleMapAppEquiv (β : N ⟶ P) (U : X.Opens) [IsIso (β.app U)] :
    Γ(N, U) ≃ₗ[Γ(X, U)] Γ(P, U) :=
  LinearEquiv.ofBijective (Tensor.Powers.SheafMultilinearMap.homApp β U)
    (ConcreteCategory.bijective_of_isIso (β.app U))

def moduleMapLocalFactor (α : M ⟶ P) (β : N ⟶ P) (U : X.Opens) [IsIso (β.app U)] :
    Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) :=
  (moduleMapAppEquiv β U).symm.toLinearMap.comp (Tensor.Powers.SheafMultilinearMap.homApp α U)

theorem moduleMapLocalFactor_spec (α : M ⟶ P) (β : N ⟶ P) (U : X.Opens)
    [IsIso (β.app U)] (s : Γ(M, U)) :
    β.app U (moduleMapLocalFactor α β U s) = α.app U s :=
  (moduleMapAppEquiv β U).apply_symm_apply _

theorem moduleMapLocalFactor_natural (α : M ⟶ P) (β : N ⟶ P)
    {U V : X.Opens} (h : V ≤ U) [IsIso (β.app U)] [IsIso (β.app V)] (s : Γ(M, U)) :
    moduleMapLocalFactor α β V (M.presheaf.map (homOfLE h).op s) =
      N.presheaf.map (homOfLE h).op (moduleMapLocalFactor α β U s) := by
  apply (ConcreteCategory.bijective_of_isIso (β.app V)).1
  rw [moduleMapLocalFactor_spec]
  have hα := ConcreteCategory.congr_hom (α.mapPresheaf.naturality (homOfLE h).op) s
  have hβ := ConcreteCategory.congr_hom (β.mapPresheaf.naturality (homOfLE h).op)
    (moduleMapLocalFactor α β U s)
  exact hα.trans ((congrArg (fun z : Γ(P, U) => P.presheaf.map (homOfLE h).op z)
    (moduleMapLocalFactor_spec α β U s)).symm.trans hβ.symm)

theorem moduleMapLocalFactor_unique (α : M ⟶ P) (β : N ⟶ P) (U : X.Opens)
    [IsIso (β.app U)] (φ : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U))
    (hφ : ∀ s, β.app U (φ s) = α.app U s) : φ = moduleMapLocalFactor α β U := by
  apply LinearMap.ext
  intro s
  apply (ConcreteCategory.bijective_of_isIso (β.app U)).1
  exact (hφ s).trans (moduleMapLocalFactor_spec α β U s).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapLocalFactor
end ComponentSource_30

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapLocalFactor"

@[expose] public section ComponentSource_31
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapValues -/

/-! # Map Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapValues

noncomputable section

/-! Read a module map on an open subscheme as compatible linear maps on smaller ambient opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

theorem moduleRestrictionUnit_app_isIso (M : Y.Modules) (U : Y.Opens) (hU : U ≤ f.opensRange) :
    IsIso (((Scheme.Modules.restrictAdjunction f).unit.app M).app U) := by
  rw [Scheme.Modules.restrictAdjunction_unit_app_app]
  have he : f ''ᵁ f ⁻¹ᵁ U = U :=
    (f.image_preimage_eq_opensRange_inf U).trans (inf_eq_right.mpr hU)
  have : IsIso (homOfLE (f.image_preimage_le U)) := homOfLE_isIso_of_eq _ he
  exact M.presheaf.map_isIso _

variable {M N : Y.Modules}

def openModuleMapValue (φ : M.restrict f ⟶ N.restrict f) (U : Y.Opens) (hU : U ≤ f.opensRange) :
    Γ(M, U) →ₗ[Γ(Y, U)] Γ(N, U) := by
  letI := moduleRestrictionUnit_app_isIso f N U hU
  exact Module.MapLocalFactor.moduleMapLocalFactor
    ((Scheme.Modules.restrictAdjunction f).unit.app M ≫ (Scheme.Modules.pushforward f).map φ)
    ((Scheme.Modules.restrictAdjunction f).unit.app N) U

theorem openModuleMapValue_natural (φ : M.restrict f ⟶ N.restrict f)
    {U V : Y.Opens} (h : V ≤ U) (hU : U ≤ f.opensRange) (hV : V ≤ f.opensRange)
    (s : Γ(M, U)) :
    openModuleMapValue f φ V hV (M.presheaf.map (homOfLE h).op s) =
      N.presheaf.map (homOfLE h).op (openModuleMapValue f φ U hU s) := by
  let := moduleRestrictionUnit_app_isIso f N U hU
  let := moduleRestrictionUnit_app_isIso f N V hV
  exact Module.MapLocalFactor.moduleMapLocalFactor_natural _ _ h s

theorem openModuleMapValue_from_global (φ : M ⟶ N) (U : Y.Opens) (hU : U ≤ f.opensRange) :
    openModuleMapValue f ((Scheme.Modules.restrictFunctor f).map φ) U hU =
      Tensor.Powers.SheafMultilinearMap.homApp φ U := by
  let := moduleRestrictionUnit_app_isIso f N U hU
  apply Eq.symm
  apply Module.MapLocalFactor.moduleMapLocalFactor_unique
  intro s
  have h := congrArg (fun ψ : M ⟶ (Scheme.Modules.pushforward f).obj (N.restrict f) => ψ.app U)
    ((Scheme.Modules.restrictAdjunction f).unit.naturality φ)
  exact ConcreteCategory.congr_hom h s

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapValues
end ComponentSource_31

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapValues"

@[expose] public section ComponentSource_32
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapRecovery -/

/-! # Map Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapRecovery

noncomputable section

/-! The ambient values recover the original module map on an open subscheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules}

theorem openModuleMapValue_spec (φ : M.restrict f ⟶ N.restrict f)
    (U : Y.Opens) (hU : U ≤ f.opensRange) (s : Γ(M, U)) :
    ((Scheme.Modules.restrictAdjunction f).unit.app N).app U (MapValues.openModuleMapValue f φ U hU s) =
      ((Scheme.Modules.restrictAdjunction f).unit.app M ≫ (Scheme.Modules.pushforward f).map φ).app U s := by
  let := MapValues.moduleRestrictionUnit_app_isIso f N U hU
  exact Module.MapLocalFactor.moduleMapLocalFactor_spec _ _ U s

theorem openModuleMapValue_injective (φ ψ : M.restrict f ⟶ N.restrict f)
    (h : ∀ (U : Y.Opens) (hU : U ≤ f.opensRange),
      MapValues.openModuleMapValue f φ U hU = MapValues.openModuleMapValue f ψ U hU) : φ = ψ := by
  apply Scheme.Modules.hom_ext
  intro W
  let U := f ''ᵁ W
  have hU : U ≤ f.opensRange := f.image_le_opensRange W
  let : IsIso (((Scheme.Modules.restrictAdjunction f).unit.app M).app U) :=
    MapValues.moduleRestrictionUnit_app_isIso f M U hU
  have hα :
      ((Scheme.Modules.restrictAdjunction f).unit.app M ≫ (Scheme.Modules.pushforward f).map φ).app U =
      ((Scheme.Modules.restrictAdjunction f).unit.app M ≫ (Scheme.Modules.pushforward f).map ψ).app U := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (openModuleMapValue_spec f φ U hU s).symm.trans
      ((congrArg (fun z => ((Scheme.Modules.restrictAdjunction f).unit.app N).app U z)
        (LinearMap.congr_fun (h U hU) s)).trans (openModuleMapValue_spec f ψ U hU s))
  change ((Scheme.Modules.restrictAdjunction f).unit.app M).app U ≫ φ.app (f ⁻¹ᵁ U) =
    ((Scheme.Modules.restrictAdjunction f).unit.app M).app U ≫ ψ.app (f ⁻¹ᵁ U) at hα
  have hh := (cancel_epi (((Scheme.Modules.restrictAdjunction f).unit.app M).app U)).mp hα
  exact (congrArg (fun V : X.Opens => φ.app V = ψ.app V) (f.preimage_image_eq W)).mp hh

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapRecovery
end ComponentSource_32

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapRecovery"

@[expose] public section ComponentSource_33
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapImageValues -/

/-! # Map Image Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapImageValues

noncomputable section

/-! On the image of an open set, ambient map values are the original local map components. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

theorem moduleRestrictionUnit_image (M : Y.Modules) (W : X.Opens) :
    ((Scheme.Modules.restrictAdjunction f).unit.app M).app (f ''ᵁ W) =
      (M.restrict f).presheaf.map (eqToHom (f.preimage_image_eq W)).op := by
  change M.presheaf.map (homOfLE (f.image_preimage_le (f ''ᵁ W))).op =
    M.presheaf.map (f.opensFunctor.map (eqToHom (f.preimage_image_eq W))).op
  congr 1

theorem openModuleMapValue_image {M N : Y.Modules}
    (φ : M.restrict f ⟶ N.restrict f) (W : X.Opens) (s : Γ(M, f ''ᵁ W)) :
    MapValues.openModuleMapValue f φ (f ''ᵁ W) (f.image_le_opensRange W) s = φ.app W s := by
  let : IsIso (((Scheme.Modules.restrictAdjunction f).unit.app N).app (f ''ᵁ W)) :=
    MapValues.moduleRestrictionUnit_app_isIso f N (f ''ᵁ W) (f.image_le_opensRange W)
  apply (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.restrictAdjunction f).unit.app N).app (f ''ᵁ W))).1
  rw [MapRecovery.openModuleMapValue_spec]
  change φ.app (f ⁻¹ᵁ f ''ᵁ W)
    (((Scheme.Modules.restrictAdjunction f).unit.app M).app (f ''ᵁ W) s) =
      ((Scheme.Modules.restrictAdjunction f).unit.app N).app (f ''ᵁ W) (φ.app W s)
  rw [moduleRestrictionUnit_image, moduleRestrictionUnit_image]
  exact ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (eqToHom (f.preimage_image_eq W)).op) s

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapImageValues
end ComponentSource_33

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapImageValues"

@[expose] public section ComponentSource_34
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapComposition -/

/-! # Map Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapComposition

noncomputable section

/-! Ambient values are unchanged by restricting a local module map to a smaller open subscheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [IsOpenImmersion f] [IsOpenImmersion g] {M N : Z.Modules}

def restrictOpenModuleMap (φ : M.restrict g ⟶ N.restrict g) :
    M.restrict (f ≫ g) ⟶ N.restrict (f ≫ g) :=
  (Scheme.Modules.restrictFunctorComp f g).hom.app M ≫
    (Scheme.Modules.restrictFunctor f).map φ ≫ (Scheme.Modules.restrictFunctorComp f g).inv.app N

theorem restrictOpenModuleMap_app (φ : M.restrict g ⟶ N.restrict g) (W : X.Opens) :
    (restrictOpenModuleMap f g φ).app W =
      M.presheaf.map (eqToHom (Scheme.Hom.comp_image f g W).symm).op ≫
        φ.app (f ''ᵁ W) ≫ N.presheaf.map (eqToHom (Scheme.Hom.comp_image f g W)).op := rfl

theorem openModuleMapValue_comp_image (φ : M.restrict g ⟶ N.restrict g)
    (W : X.Opens) (s : Γ(M, (f ≫ g) ''ᵁ W)) :
    MapValues.openModuleMapValue (f ≫ g) (restrictOpenModuleMap f g φ) ((f ≫ g) ''ᵁ W)
      ((f ≫ g).image_le_opensRange W) s =
      MapValues.openModuleMapValue g φ ((f ≫ g) ''ᵁ W)
        ((Scheme.Hom.comp_image f g W).trans_le (g.image_le_opensRange (f ''ᵁ W))) s := by
  let h := (Scheme.Hom.comp_image f g W).symm.le
  let eN := N.presheaf.mapIso (eqToIso (Scheme.Hom.comp_image f g W).symm).op
  have : IsIso (homOfLE h) := homOfLE_isIso_of_eq h (Scheme.Hom.comp_image f g W).symm
  have : IsIso (N.presheaf.map (homOfLE h).op) := N.presheaf.map_isIso _
  apply (ConcreteCategory.bijective_of_isIso (N.presheaf.map (homOfLE h).op)).1
  rw [MapImageValues.openModuleMapValue_image]
  have hn := MapValues.openModuleMapValue_natural g φ h
    ((Scheme.Hom.comp_image f g W).trans_le (g.image_le_opensRange (f ''ᵁ W)))
    (g.image_le_opensRange (f ''ᵁ W)) s
  rw [← hn, MapImageValues.openModuleMapValue_image, restrictOpenModuleMap_app]
  change eN.hom (eN.inv (φ.app (f ''ᵁ W)
    (M.presheaf.map (homOfLE h).op s))) = φ.app (f ''ᵁ W) (M.presheaf.map (homOfLE h).op s)
  exact ConcreteCategory.congr_hom eN.inv_hom_id _

theorem openModuleMapValue_comp (φ : M.restrict g ⟶ N.restrict g)
    (U : Z.Opens) (hU : U ≤ (f ≫ g).opensRange) :
    MapValues.openModuleMapValue (f ≫ g) (restrictOpenModuleMap f g φ) U hU =
      MapValues.openModuleMapValue g φ U (hU.trans (by
        rw [Scheme.Hom.opensRange_comp]
        exact g.image_le_opensRange f.opensRange)) := by
  have he : (f ≫ g) ''ᵁ (f ≫ g) ⁻¹ᵁ U = U :=
    ((f ≫ g).image_preimage_eq_opensRange_inf U).trans (inf_eq_right.mpr hU)
  have H : ∀ h₁ : (f ≫ g) ''ᵁ (f ≫ g) ⁻¹ᵁ U ≤ (f ≫ g).opensRange,
      ∀ h₂ : (f ≫ g) ''ᵁ (f ≫ g) ⁻¹ᵁ U ≤ g.opensRange,
      MapValues.openModuleMapValue (f ≫ g) (restrictOpenModuleMap f g φ)
        ((f ≫ g) ''ᵁ (f ≫ g) ⁻¹ᵁ U) h₁ =
      MapValues.openModuleMapValue g φ ((f ≫ g) ''ᵁ (f ≫ g) ⁻¹ᵁ U) h₂ := by
    intro h₁ h₂
    apply LinearMap.ext
    intro s
    exact openModuleMapValue_comp_image f g φ ((f ≫ g) ⁻¹ᵁ U) s
  have H' := (congrArg (fun V : Z.Opens => ∀ h₁ : V ≤ (f ≫ g).opensRange,
      ∀ h₂ : V ≤ g.opensRange,
      MapValues.openModuleMapValue (f ≫ g) (restrictOpenModuleMap f g φ) V h₁ =
        MapValues.openModuleMapValue g φ V h₂) he).mp H
  exact H' hU _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapComposition
end ComponentSource_34

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapComposition"

@[expose] public section ComponentSource_35
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapValueFunctoriality -/

/-! # Map Value Functoriality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapValueFunctoriality

noncomputable section

/-! Functoriality of actual module-map values on common ambient opens.
These identities turn ordinary overlap isomorphisms into the section
transition data used by effective module-object gluing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {X Y Z : Scheme.{u}}

theorem openModuleMapValue_identity (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (U : X.Opens) (hU : U ≤ f.opensRange) (s : Γ(M, U)) :
    MapValues.openModuleMapValue f (𝟙 (M.restrict f)) U hU s = s := by
  let := MapValues.moduleRestrictionUnit_app_isIso f M U hU
  apply (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.restrictAdjunction f).unit.app M).app U)).injective
  have h : (Scheme.Modules.restrictAdjunction f).unit.app M ≫
      (Scheme.Modules.pushforward f).map (𝟙 (M.restrict f)) =
        (Scheme.Modules.restrictAdjunction f).unit.app M := by
    rw [(Scheme.Modules.pushforward f).map_id]
    exact Category.comp_id _
  exact (MapRecovery.openModuleMapValue_spec f (𝟙 (M.restrict f)) U hU s).trans
    (congrArg (fun a => a.app U s) h)

theorem openModuleMapValue_hom_comp (f : Y ⟶ X) [IsOpenImmersion f]
    {M N P : X.Modules} (a : M.restrict f ⟶ N.restrict f)
    (b : N.restrict f ⟶ P.restrict f) (U : X.Opens) (hU : U ≤ f.opensRange)
    (s : Γ(M, U)) :
    MapValues.openModuleMapValue f (a ≫ b) U hU s =
      MapValues.openModuleMapValue f b U hU (MapValues.openModuleMapValue f a U hU s) := by
  let := MapValues.moduleRestrictionUnit_app_isIso f P U hU
  apply (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.restrictAdjunction f).unit.app P).app U)).injective
  rw [MapRecovery.openModuleMapValue_spec, MapRecovery.openModuleMapValue_spec]
  change b.app (f ⁻¹ᵁ U)
      (a.app (f ⁻¹ᵁ U) (((Scheme.Modules.restrictAdjunction f).unit.app M).app U s)) =
    b.app (f ⁻¹ᵁ U)
      (((Scheme.Modules.restrictAdjunction f).unit.app N).app U
        (MapValues.openModuleMapValue f a U hU s))
  exact congrArg (b.app (f ⁻¹ᵁ U)) (MapRecovery.openModuleMapValue_spec f a U hU s).symm

private theorem restrictFunctorCongr_refl (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) :
    (Scheme.Modules.restrictFunctorCongr (rfl : f = f)).app M = Iso.refl (M.restrict f) := by
  apply Iso.ext
  apply Scheme.Modules.hom_ext
  intro U
  simp only [Iso.app_hom, Scheme.Modules.restrictFunctorCongr_hom_app_app,
    eqToHom_refl, op_id, Iso.refl_hom, Scheme.Modules.Hom.id_app]
  exact M.presheaf.map_id _

def openModuleMapCongr (f g : Y ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g]
    (h : f = g) {M N : X.Modules} (a : M.restrict f ⟶ N.restrict f) :
    M.restrict g ⟶ N.restrict g :=
  (Scheme.Modules.restrictFunctorCongr h).inv.app M ≫ a ≫
    (Scheme.Modules.restrictFunctorCongr h).hom.app N

theorem openModuleMapValue_congr (f g : Y ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g]
    (h : f = g) {M N : X.Modules} (a : M.restrict f ⟶ N.restrict f)
    (U : X.Opens) (hf : U ≤ f.opensRange) (hg : U ≤ g.opensRange) (s : Γ(M, U)) :
    MapValues.openModuleMapValue g (openModuleMapCongr f g h a) U hg s = MapValues.openModuleMapValue f a U hf s := by
  subst g
  have hM := restrictFunctorCongr_refl f M
  have hN := restrictFunctorCongr_refl f N
  change MapValues.openModuleMapValue f
    (((Scheme.Modules.restrictFunctorCongr rfl).app M).inv ≫ a ≫
      ((Scheme.Modules.restrictFunctorCongr rfl).app N).hom) U hg s = _
  rw [hM, hN, Iso.refl_inv, Iso.refl_hom, Category.id_comp, Category.comp_id]

def restrictOpenModuleMapTo (f : Z ⟶ Y) (g : Y ⟶ X) (q : Z ⟶ X)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion q]
    (h : f ≫ g = q) {M N : X.Modules} (a : M.restrict g ⟶ N.restrict g) :
    M.restrict q ⟶ N.restrict q :=
  openModuleMapCongr (f ≫ g) q h (MapComposition.restrictOpenModuleMap f g a)

theorem restrictOpenModuleMapTo_value (f : Z ⟶ Y) (g : Y ⟶ X) (q : Z ⟶ X)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion q]
    (h : f ≫ g = q) {M N : X.Modules} (a : M.restrict g ⟶ N.restrict g)
    (U : X.Opens) (hq : U ≤ q.opensRange) (hg : U ≤ g.opensRange) (s : Γ(M, U)) :
    MapValues.openModuleMapValue q (restrictOpenModuleMapTo f g q h a) U hq s =
      MapValues.openModuleMapValue g a U hg s := by
  have hfg : U ≤ (f ≫ g).opensRange := by simpa only [h] using hq
  exact (openModuleMapValue_congr (f ≫ g) q h (MapComposition.restrictOpenModuleMap f g a) U hfg hq s).trans
    (LinearMap.congr_fun (MapComposition.openModuleMapValue_comp f g a U hfg) s)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapValueFunctoriality
end ComponentSource_35

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapValueFunctoriality"

@[expose] public section ComponentSource_36
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.IsoValues -/

/-! # Iso Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.IsoValues

noncomputable section

/-! An actual module isomorphism on an open subscheme induces linear equivalences of sections on every smaller ambient open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules}

theorem openModuleMapValue_bijective (e : M.restrict f ≅ N.restrict f)
    (U : Y.Opens) (hU : U ≤ f.opensRange) :
    Function.Bijective (MapValues.openModuleMapValue f e.hom U hU) := by
  have := MapValues.moduleRestrictionUnit_app_isIso f M U hU
  have := MapValues.moduleRestrictionUnit_app_isIso f N U hU
  let α := (Scheme.Modules.restrictAdjunction f).unit.app M ≫
    (Scheme.Modules.pushforward f).map e.hom
  have : IsIso (α.app U) := by
    change IsIso (((Scheme.Modules.restrictAdjunction f).unit.app M).app U ≫
      ((Scheme.Modules.pushforward f).map e.hom).app U)
    infer_instance
  exact (Module.MapLocalFactor.moduleMapAppEquiv ((Scheme.Modules.restrictAdjunction f).unit.app N) U).symm.bijective.comp
    (ConcreteCategory.bijective_of_isIso (α.app U))

def openModuleIsoValue (e : M.restrict f ≅ N.restrict f)
    (U : Y.Opens) (hU : U ≤ f.opensRange) : Γ(M, U) ≃ₗ[Γ(Y, U)] Γ(N, U) :=
  LinearEquiv.ofBijective (MapValues.openModuleMapValue f e.hom U hU) (openModuleMapValue_bijective f e U hU)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.IsoValues
end ComponentSource_36

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.IsoValues"

@[expose] public section ComponentSource_37
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf -/

/-! # Product Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf

noncomputable section

/-!
Actual tensor products of module sheaves, obtained by sheafifying the
pointwise tensor product of the underlying module presheaves. Their universal
property follows from the proved sheafification adjunction.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory

universe u

variable {X : Scheme.{u}}

local instance (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)

local instance (X : Scheme.{u}) : SymmetricCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.symmetricCategory (R := X.presheaf)

/-- The tensor product of two actual module sheaves. -/
def tensorModule (M N : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val)

/-- Morphisms out of the tensor sheaf are natural bilinear maps on sections,
encoded by the pointwise tensor product of presheaves. -/
def tensorModuleHomEquiv (M N P : X.Modules) :
    (tensorModule M N ⟶ P) ≃
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val ⟶ P.val) :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ P

/-- Tensoring with the structure sheaf gives back the original module sheaf. -/
def tensorModuleUnitLeftIso (M : X.Modules) :
    tensorModule (Line.Bundles.structureModule X) M ≅ M := by
  have : IsIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit := inferInstance
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (λ_ M.val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).app M

/-- The tensor product of sheaves is symmetric. -/
def tensorModuleCommIso (M N : X.Modules) : tensorModule M N ≅ tensorModule N M :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (CategoryTheory.BraidedCategory.braiding M.val N.val)

/-- Isomorphisms of both factors induce an isomorphism of their tensor sheaves. -/
def tensorModuleCongr {M M' N N' : X.Modules} (e : M ≅ M') (f : N ≅ N') :
    tensorModule M N ≅ tensorModule M' N' :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    ((Scheme.Modules.toPresheafOfModules X).mapIso e ⊗ᵢ
      (Scheme.Modules.toPresheafOfModules X).mapIso f)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf
end ComponentSource_37

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf"

@[expose] public section ComponentSource_38
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.Sheaves -/

/-! # Sheaves -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.Sheaves

noncomputable section

/-! Bilinear maps of module sheaves and the universal property of their actual tensor product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

variable {X : Scheme.{u}}

/-- Bilinear maps on sections compatible with restriction to smaller opens. -/
structure SheafBilinearMap (M N P : X.Modules) where
  app (U : X.Opens) : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) →ₗ[Γ(X, U)] Γ(P, U)
  naturality {U V : X.Opens} (h : V ⟶ U) (x : Γ(M, U)) (y : Γ(N, U)) :
    P.presheaf.map h.op (app U x y) =
      app V (M.presheaf.map h.op x) (N.presheaf.map h.op y)

namespace SheafBilinearMap

variable {M M' N N' P Q R : X.Modules}

@[ext]
theorem ext {β γ : SheafBilinearMap M N P} (h : ∀ U, β.app U = γ.app U) : β = γ := by
  cases β
  cases γ
  congr
  exact funext h

/-- Postcompose a bilinear map by a morphism of module sheaves. -/
def postcomp (β : SheafBilinearMap M N P) (f : P ⟶ Q) : SheafBilinearMap M N Q where
  app U := (β.app U).compr₂ (Tensor.Powers.SheafMultilinearMap.homApp f U)
  naturality {U V} h x y :=
    (ConcreteCategory.congr_hom (f.mapPresheaf.naturality h.op) (β.app U x y)).symm.trans
      (congrArg (fun z => f.app V z) (β.naturality h x y))

/-- Precompose the two arguments independently. -/
def precomp (β : SheafBilinearMap M N P) (f : M' ⟶ M) (g : N' ⟶ N) :
    SheafBilinearMap M' N' P where
  app U := (β.app U).compl₁₂ (Tensor.Powers.SheafMultilinearMap.homApp f U) (Tensor.Powers.SheafMultilinearMap.homApp g U)
  naturality {U V} h x y :=
    (β.naturality h (f.app U x) (g.app U y)).trans
      (congrArg₂ (fun a b => β.app V a b)
        (ConcreteCategory.congr_hom (f.mapPresheaf.naturality h.op) x).symm
        (ConcreteCategory.congr_hom (g.mapPresheaf.naturality h.op) y).symm)

@[simp]
theorem postcomp_id (β : SheafBilinearMap M N P) : β.postcomp (𝟙 P) = β := by
  ext U x y
  rfl

theorem postcomp_comp (β : SheafBilinearMap M N P) (f : P ⟶ Q) (g : Q ⟶ R) :
    β.postcomp (f ≫ g) = (β.postcomp f).postcomp g := by
  ext U x y
  rfl

@[simp]
theorem precomp_id (β : SheafBilinearMap M N P) : β.precomp (𝟙 M) (𝟙 N) = β := by
  ext U x y
  rfl

theorem precomp_postcomp (β : SheafBilinearMap M N P) (f : M' ⟶ M) (g : N' ⟶ N)
    (h : P ⟶ Q) :
    (β.postcomp h).precomp f g = (β.precomp f g).postcomp h := by
  ext U x y
  rfl

/-- A map out of the tensor presheaf gives its bilinear formula on sections. -/
def ofTensorPresheafHom
    (f : PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val ⟶ P.val) :
    SheafBilinearMap M N P where
  app U := TensorProduct.curry (f.app (.op U)).hom
  naturality h x y := (PresheafOfModules.naturality_apply f h.op (x ⊗ₜ y)).symm

/-- A bilinear section formula defines a map out of the tensor presheaf. -/
def toTensorPresheafHom (β : SheafBilinearMap M N P) :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val ⟶ P.val where
  app U := (ModuleCat.ofHom (TensorProduct.lift (β.app U.unop)) :
    ModuleCat.of Γ(X, U.unop) (Γ(M, U.unop) ⊗[Γ(X, U.unop)] Γ(N, U.unop)) ⟶
      ModuleCat.of Γ(X, U.unop) Γ(P, U.unop))
  naturality {_U _V} h := ModuleCat.MonoidalCategory.tensor_ext
    (fun x y => (β.naturality h.unop x y).symm)

/-- The tensor presheaf has exactly the prescribed natural bilinear maps. -/
def tensorPresheafHomEquiv (M N P : X.Modules) :
    (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val ⟶ P.val) ≃
      SheafBilinearMap M N P where
  toFun := ofTensorPresheafHom
  invFun := toTensorPresheafHom
  left_inv f := by
    ext U : 1
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    rfl
  right_inv β := by
    ext U x y
    rfl

/-- The actual sheaf tensor product represents natural bilinear maps. -/
def tensorHomEquiv (M N P : X.Modules) :
    (Tensor.ProductSheaf.tensorModule M N ⟶ P) ≃ SheafBilinearMap M N P :=
  (Tensor.ProductSheaf.tensorModuleHomEquiv M N P).trans (tensorPresheafHomEquiv M N P)

/-- Varying the output sheaf gives the functor represented by the tensor sheaf. -/
def outputFunctor (M N : X.Modules) : X.Modules ⥤ Type u where
  obj P := SheafBilinearMap M N P
  map {P Q} f := TypeCat.ofHom (fun β : SheafBilinearMap M N P => β.postcomp f)
  map_id P := by
    apply ConcreteCategory.ext_apply
    intro β
    exact β.postcomp_id
  map_comp f g := by
    apply ConcreteCategory.ext_apply
    exact fun β => β.postcomp_comp f g

/-- The tensor-to-bilinear equivalence is natural in the output sheaf. -/
theorem tensorHomEquiv_postcomp (f : Tensor.ProductSheaf.tensorModule M N ⟶ P) (h : P ⟶ Q) :
    tensorHomEquiv M N Q (f ≫ h) = (tensorHomEquiv M N P f).postcomp h := by
  have he : Tensor.ProductSheaf.tensorModuleHomEquiv M N Q (f ≫ h) =
      Tensor.ProductSheaf.tensorModuleHomEquiv M N P f ≫ h.val :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv_naturality_right f h
  change ofTensorPresheafHom (Tensor.ProductSheaf.tensorModuleHomEquiv M N Q (f ≫ h)) = _
  rw [he]
  ext U x y
  rfl

/-- The tensor sheaf corepresents the functor of natural bilinear maps. -/
def corepresentable (M N : X.Modules) :
    (outputFunctor M N).CorepresentableBy (Tensor.ProductSheaf.tensorModule M N) where
  homEquiv := tensorHomEquiv M N _
  homEquiv_comp g f := tensorHomEquiv_postcomp f g

end SheafBilinearMap

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.Sheaves
end ComponentSource_38

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.Sheaves"

@[expose] public section ComponentSource_39
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.BilinearRestriction -/

/-! # Bilinear Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear

noncomputable section

/-! Restriction and direct image of bilinear sheaf maps, with their adjunction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- Direct image of a bilinear map, with coordinate-ring scalars restricted. -/
def Sheaves.SheafBilinearMap.pushforward {M N P : X.Modules} (β : Sheaves.SheafBilinearMap M N P) (f : X ⟶ Y) :
    Sheaves.SheafBilinearMap ((Scheme.Modules.pushforward f).obj M)
      ((Scheme.Modules.pushforward f).obj N) ((Scheme.Modules.pushforward f).obj P) where
  app U := {
    toFun x := {
      toFun y := β.app (f ⁻¹ᵁ U) x y
      map_add' y z := (β.app (f ⁻¹ᵁ U) x).map_add y z
      map_smul' r y := (β.app (f ⁻¹ᵁ U) x).map_smul (f.app U r) y }
    map_add' x y := LinearMap.ext fun z =>
      LinearMap.congr_fun ((β.app (f ⁻¹ᵁ U)).map_add x y) z
    map_smul' r x := LinearMap.ext fun z =>
      LinearMap.congr_fun ((β.app (f ⁻¹ᵁ U)).map_smul (f.app U r) x) z }
  naturality h x y := β.naturality ((TopologicalSpace.Opens.map f.base).map h) x y

/-- Restriction of a bilinear map to an open subscheme. -/
def Sheaves.SheafBilinearMap.restrict {M N P : Y.Modules} (β : Sheaves.SheafBilinearMap M N P) (f : X ⟶ Y)
    [IsOpenImmersion f] : Sheaves.SheafBilinearMap (M.restrict f) (N.restrict f) (P.restrict f) where
  app U := {
    toFun x := {
      toFun y := β.app (f ''ᵁ U) x y
      map_add' y z := (β.app (f ''ᵁ U) x).map_add y z
      map_smul' r y := (β.app (f ''ᵁ U) x).map_smul ((f.appIso U).inv r) y }
    map_add' x y := LinearMap.ext fun z =>
      LinearMap.congr_fun ((β.app (f ''ᵁ U)).map_add x y) z
    map_smul' r x := LinearMap.ext fun z =>
      LinearMap.congr_fun ((β.app (f ''ᵁ U)).map_smul ((f.appIso U).inv r) x) z }
  naturality h x y := β.naturality (f.opensFunctor.map h) x y

theorem Sheaves.SheafBilinearMap.precomp_comp {M M' M'' N N' N'' P : X.Modules} (β : Sheaves.SheafBilinearMap M N P)
    (f : M' ⟶ M) (g : N' ⟶ N) (f' : M'' ⟶ M') (g' : N'' ⟶ N') :
    (β.precomp f g).precomp f' g' = β.precomp (f' ≫ f) (g' ≫ g) := by
  ext U x y
  rfl

theorem Sheaves.SheafBilinearMap.pushforward_postcomp {M N P Q : X.Modules} (β : Sheaves.SheafBilinearMap M N P)
    (f : X ⟶ Y) (h : P ⟶ Q) :
    (β.postcomp h).pushforward f =
      (β.pushforward f).postcomp ((Scheme.Modules.pushforward f).map h) := by
  ext U x y
  rfl

theorem Sheaves.SheafBilinearMap.restrict_postcomp {M N P Q : Y.Modules} (β : Sheaves.SheafBilinearMap M N P)
    (f : X ⟶ Y) [IsOpenImmersion f] (h : P ⟶ Q) :
    (β.postcomp h).restrict f =
      (β.restrict f).postcomp ((Scheme.Modules.restrictFunctor f).map h) := by
  ext U x y
  rfl

theorem Sheaves.SheafBilinearMap.restrict_precomp {M M' N N' P : Y.Modules} (β : Sheaves.SheafBilinearMap M N P)
    (f : X ⟶ Y) [IsOpenImmersion f] (a : M' ⟶ M) (b : N' ⟶ N) :
    (β.precomp a b).restrict f = (β.restrict f).precomp
      ((Scheme.Modules.restrictFunctor f).map a) ((Scheme.Modules.restrictFunctor f).map b) := by
  ext U x y
  rfl

theorem Sheaves.SheafBilinearMap.restrict_unit_naturality {M N P : Y.Modules} (β : Sheaves.SheafBilinearMap M N P)
    (f : X ⟶ Y) [IsOpenImmersion f] :
    ((β.restrict f).pushforward f).precomp
        ((Scheme.Modules.restrictAdjunction f).unit.app M)
        ((Scheme.Modules.restrictAdjunction f).unit.app N) =
      β.postcomp ((Scheme.Modules.restrictAdjunction f).unit.app P) := by
  ext U x y
  exact (β.naturality (f.isOpenEmbedding.isOpenMap.adjunction.counit.app U) x y).symm

theorem Sheaves.SheafBilinearMap.restrict_counit_naturality {M N P : X.Modules} (β : Sheaves.SheafBilinearMap M N P)
    (f : X ⟶ Y) [IsOpenImmersion f] :
    ((β.pushforward f).restrict f).postcomp ((Scheme.Modules.restrictAdjunction f).counit.app P) =
      β.precomp ((Scheme.Modules.restrictAdjunction f).counit.app M)
        ((Scheme.Modules.restrictAdjunction f).counit.app N) := by
  ext U x y
  exact β.naturality (f.isOpenEmbedding.isOpenMap.adjunction.unit.app U) x y

/-- The restriction/direct-image adjunction for bilinear maps. -/
def Sheaves.SheafBilinearMap.restrictHomEquiv (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules) (P : X.Modules) :
    Sheaves.SheafBilinearMap (M.restrict f) (N.restrict f) P ≃
      Sheaves.SheafBilinearMap M N ((Scheme.Modules.pushforward f).obj P) where
  toFun β := (β.pushforward f).precomp ((Scheme.Modules.restrictAdjunction f).unit.app M)
    ((Scheme.Modules.restrictAdjunction f).unit.app N)
  invFun β := (β.restrict f).postcomp ((Scheme.Modules.restrictAdjunction f).counit.app P)
  left_inv β := by
    change (((β.pushforward f).precomp ((Scheme.Modules.restrictAdjunction f).unit.app M)
      ((Scheme.Modules.restrictAdjunction f).unit.app N)).restrict f).postcomp
        ((Scheme.Modules.restrictAdjunction f).counit.app P) = β
    rw [Sheaves.SheafBilinearMap.restrict_precomp, ← Sheaves.SheafBilinearMap.precomp_postcomp, Sheaves.SheafBilinearMap.restrict_counit_naturality, Sheaves.SheafBilinearMap.precomp_comp]
    exact (congrArg₂ (fun a b => β.precomp a b)
      ((Scheme.Modules.restrictAdjunction f).left_triangle_components M)
      ((Scheme.Modules.restrictAdjunction f).left_triangle_components N)).trans β.precomp_id
  right_inv β := by
    change (((β.restrict f).postcomp ((Scheme.Modules.restrictAdjunction f).counit.app P)).pushforward f).precomp
      ((Scheme.Modules.restrictAdjunction f).unit.app M)
        ((Scheme.Modules.restrictAdjunction f).unit.app N) = β
    rw [Sheaves.SheafBilinearMap.pushforward_postcomp, Sheaves.SheafBilinearMap.precomp_postcomp, Sheaves.SheafBilinearMap.restrict_unit_naturality, ← Sheaves.SheafBilinearMap.postcomp_comp]
    exact (congrArg (fun h => β.postcomp h)
      ((Scheme.Modules.restrictAdjunction f).right_triangle_components P)).trans β.postcomp_id

/-- Naturality of the bilinear adjunction in its output sheaf. -/
theorem Sheaves.SheafBilinearMap.restrictHomEquiv_postcomp (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules)
    {P Q : X.Modules} (β : Sheaves.SheafBilinearMap (M.restrict f) (N.restrict f) P) (h : P ⟶ Q) :
    Sheaves.SheafBilinearMap.restrictHomEquiv f M N Q (β.postcomp h) =
      (Sheaves.SheafBilinearMap.restrictHomEquiv f M N P β).postcomp ((Scheme.Modules.pushforward f).map h) := by
  change ((β.postcomp h).pushforward f).precomp _ _ = _
  rw [Sheaves.SheafBilinearMap.pushforward_postcomp, Sheaves.SheafBilinearMap.precomp_postcomp]
  rfl

/-- Naturality of the inverse bilinear adjunction in its output sheaf. -/
theorem Sheaves.SheafBilinearMap.restrictHomEquiv_symm_postcomp (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules)
    {P Q : X.Modules} (β : Sheaves.SheafBilinearMap M N ((Scheme.Modules.pushforward f).obj P))
    (h : P ⟶ Q) :
    (Sheaves.SheafBilinearMap.restrictHomEquiv f M N Q).symm (β.postcomp ((Scheme.Modules.pushforward f).map h)) =
      ((Sheaves.SheafBilinearMap.restrictHomEquiv f M N P).symm β).postcomp h := by
  apply (Sheaves.SheafBilinearMap.restrictHomEquiv f M N Q).injective
  rw [Equiv.apply_symm_apply, Sheaves.SheafBilinearMap.restrictHomEquiv_postcomp, Equiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear
end ComponentSource_39

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.BilinearRestriction"

@[expose] public section ComponentSource_40
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Bifunctor -/

/-! # Bifunctor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Bifunctor

noncomputable section

/-! Functorial maps on the actual tensor product of module sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

def tensorBilinear (M N : X.Modules) : Bilinear.Sheaves.SheafBilinearMap M N (ProductSheaf.tensorModule M N) :=
  Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _ (𝟙 _)

theorem tensorBilinear_postcomp {M N P : X.Modules} (f : ProductSheaf.tensorModule M N ⟶ P) :
    (tensorBilinear M N).postcomp f = Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N P f := by
  exact (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp (𝟙 _) f).symm.trans
    (congrArg (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N P) (Category.id_comp f))

def tensorModuleMap {M M' N N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N') :
    ProductSheaf.tensorModule M N ⟶ ProductSheaf.tensorModule M' N' :=
  (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _).symm ((tensorBilinear M' N').precomp f g)

theorem tensorModuleMap_spec {M M' N N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N') :
    (tensorBilinear M N).postcomp (tensorModuleMap f g) =
      (tensorBilinear M' N').precomp f g :=
  (tensorBilinear_postcomp _).trans (Equiv.apply_symm_apply _ _)

theorem tensorModuleMap_id (M N : X.Modules) :
    tensorModuleMap (𝟙 M) (𝟙 N) = 𝟙 (ProductSheaf.tensorModule M N) := by
  apply (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _).injective
  exact (Equiv.apply_symm_apply _ _).trans (Bilinear.Sheaves.SheafBilinearMap.precomp_id _)

theorem tensorModuleMap_comp {M M' M'' N N' N'' : X.Modules}
    (f : M ⟶ M') (g : N ⟶ N') (f' : M' ⟶ M'') (g' : N' ⟶ N'') :
    tensorModuleMap f g ≫ tensorModuleMap f' g' = tensorModuleMap (f ≫ f') (g ≫ g') := by
  apply (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _).injective
  rw [← tensorBilinear_postcomp, Bilinear.Sheaves.SheafBilinearMap.postcomp_comp, tensorModuleMap_spec,
    ← Bilinear.Sheaves.SheafBilinearMap.precomp_postcomp, tensorModuleMap_spec,
    Bilinear.Sheaves.SheafBilinearMap.precomp_comp, ← tensorModuleMap_spec, tensorBilinear_postcomp]

def tensorModuleMapIso {M M' N N' : X.Modules} (e : M ≅ M') (f : N ≅ N') :
    ProductSheaf.tensorModule M N ≅ ProductSheaf.tensorModule M' N' where
  hom := tensorModuleMap e.hom f.hom
  inv := tensorModuleMap e.inv f.inv
  hom_inv_id := by rw [tensorModuleMap_comp, e.hom_inv_id, f.hom_inv_id, tensorModuleMap_id]
  inv_hom_id := by rw [tensorModuleMap_comp, e.inv_hom_id, f.inv_hom_id, tensorModuleMap_id]

instance tensorModuleMap_isIso {M M' N N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N')
    [IsIso f] [IsIso g] : IsIso (tensorModuleMap f g) :=
  (tensorModuleMapIso (asIso f) (asIso g)).isIso_hom

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Bifunctor
end ComponentSource_40

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Bifunctor"

@[expose] public section ComponentSource_41
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackComparison -/

/-! # Pullback Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The canonical tensor comparison for arbitrary pullback of module sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

theorem Bilinear.Sheaves.SheafBilinearMap.pushforward_precomp {M M' N N' P : X.Modules}
    (β : Bilinear.Sheaves.SheafBilinearMap M N P) (f : X ⟶ Y) (a : M' ⟶ M) (b : N' ⟶ N) :
    (β.precomp a b).pushforward f = (β.pushforward f).precomp
      ((Scheme.Modules.pushforward f).map a) ((Scheme.Modules.pushforward f).map b) := by
  ext U x y
  rfl

theorem Tensor.PullbackComparison.tensorHomEquiv_precomp {M M' N N' P : Y.Modules}
    (a : M ⟶ M') (b : N ⟶ N') (h : Tensor.ProductSheaf.tensorModule M' N' ⟶ P) :
    Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N P (Tensor.Bifunctor.tensorModuleMap a b ≫ h) =
      (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M' N' P h).precomp a b := by
  rw [← Tensor.Bifunctor.tensorBilinear_postcomp, Bilinear.Sheaves.SheafBilinearMap.postcomp_comp, Tensor.Bifunctor.tensorModuleMap_spec,
    ← Bilinear.Sheaves.SheafBilinearMap.precomp_postcomp, Tensor.Bifunctor.tensorBilinear_postcomp]

/-- A bilinear map on inverse images induces a bilinear map into its direct image. -/
def Tensor.PullbackComparison.bilinearPullbackUnit (f : X ⟶ Y) (M N : Y.Modules) (P : X.Modules)
    (β : Bilinear.Sheaves.SheafBilinearMap ((Scheme.Modules.pullback f).obj M)
      ((Scheme.Modules.pullback f).obj N) P) :
    Bilinear.Sheaves.SheafBilinearMap M N ((Scheme.Modules.pushforward f).obj P) :=
  (β.pushforward f).precomp ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N)

theorem Tensor.PullbackComparison.bilinearPullbackUnit_postcomp (f : X ⟶ Y) (M N : Y.Modules) {P Q : X.Modules}
    (β : Bilinear.Sheaves.SheafBilinearMap ((Scheme.Modules.pullback f).obj M)
      ((Scheme.Modules.pullback f).obj N) P) (h : P ⟶ Q) :
    Tensor.PullbackComparison.bilinearPullbackUnit f M N Q (β.postcomp h) =
      (Tensor.PullbackComparison.bilinearPullbackUnit f M N P β).postcomp ((Scheme.Modules.pushforward f).map h) := by
  exact (congrArg (fun γ => γ.precomp
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N))
      (β.pushforward_postcomp f h)).trans (Bilinear.Sheaves.SheafBilinearMap.precomp_postcomp _ _ _ _)

theorem Tensor.PullbackComparison.bilinearPullbackUnit_precomp (f : X ⟶ Y) {M M' N N' : Y.Modules} (P : X.Modules)
    (β : Bilinear.Sheaves.SheafBilinearMap ((Scheme.Modules.pullback f).obj M')
      ((Scheme.Modules.pullback f).obj N') P) (a : M ⟶ M') (b : N ⟶ N') :
    Tensor.PullbackComparison.bilinearPullbackUnit f M N P (β.precomp
      ((Scheme.Modules.pullback f).map a) ((Scheme.Modules.pullback f).map b)) =
      (Tensor.PullbackComparison.bilinearPullbackUnit f M' N' P β).precomp a b := by
  unfold Tensor.PullbackComparison.bilinearPullbackUnit
  rw [Bilinear.Sheaves.SheafBilinearMap.pushforward_precomp, Bilinear.Sheaves.SheafBilinearMap.precomp_comp,
    Bilinear.Sheaves.SheafBilinearMap.precomp_comp]
  exact congrArg₂ (fun c d => (β.pushforward f).precomp c d)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality a).symm
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality b).symm

/-- The canonical map from the inverse image of a tensor product to the tensor of inverse images. -/
def Tensor.PullbackComparison.tensorPullbackComparison (f : X ⟶ Y) (M N : Y.Modules) :
    (Scheme.Modules.pullback f).obj (Tensor.ProductSheaf.tensorModule M N) ⟶
      Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    ((Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _).symm
      (Tensor.PullbackComparison.bilinearPullbackUnit f M N _
        (Tensor.Bifunctor.tensorBilinear ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N))))

theorem Tensor.PullbackComparison.tensorPullbackComparison_spec (f : X ⟶ Y) (M N : Y.Modules) :
    Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
        (Tensor.PullbackComparison.tensorPullbackComparison f M N)) =
      Tensor.PullbackComparison.bilinearPullbackUnit f M N _
        (Tensor.Bifunctor.tensorBilinear ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)) := by
  unfold Tensor.PullbackComparison.tensorPullbackComparison
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem Tensor.PullbackComparison.tensorPullbackComparison_natural (f : X ⟶ Y) {M M' N N' : Y.Modules}
    (a : M ⟶ M') (b : N ⟶ N') :
    (Scheme.Modules.pullback f).map (Tensor.Bifunctor.tensorModuleMap a b) ≫ Tensor.PullbackComparison.tensorPullbackComparison f M' N' =
      Tensor.PullbackComparison.tensorPullbackComparison f M N ≫ Tensor.Bifunctor.tensorModuleMap
        ((Scheme.Modules.pullback f).map a) ((Scheme.Modules.pullback f).map b) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _).injective
  rw [(Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_left,
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_right,
    Tensor.PullbackComparison.tensorHomEquiv_precomp, Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp,
    Tensor.PullbackComparison.tensorPullbackComparison_spec, Tensor.PullbackComparison.tensorPullbackComparison_spec,
    ← Tensor.PullbackComparison.bilinearPullbackUnit_postcomp, Tensor.Bifunctor.tensorModuleMap_spec,
    Tensor.PullbackComparison.bilinearPullbackUnit_precomp]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
end ComponentSource_41

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackComparison"

@[expose] public section ComponentSource_42
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.TensorCompositionUnits -/

/-! # Tensor Composition Units -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The pullback composition comparison respects the units used by tensor pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

theorem Pullback.TensorCompositionUnits.pullbackComp_hom_unit (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M ≫
      (Scheme.Modules.pushforward g).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          ((Scheme.Modules.pullback g).obj M)) ≫
      (Scheme.Modules.pushforward g).map ((Scheme.Modules.pushforward f).map
        ((Scheme.Modules.pullbackComp f g).hom.app M)) ≫
      (Scheme.Modules.pushforwardComp f g).hom.app ((Scheme.Modules.pullback (f ≫ g)).obj M) =
        (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M := by
  let L := Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f
  let R := Scheme.Modules.pushforward f ⋙ Scheme.Modules.pushforward g
  let adj := (Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f)
  let e := Scheme.Modules.pullbackComp f g
  let b := Scheme.Modules.pushforwardComp f g
  have hu : adj.unit.app M ≫ b.hom.app (L.obj M) =
      (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M ≫
        (Scheme.Modules.pushforward (f ≫ g)).map (e.inv.app M) := by
    have h := unit_conjugateEquiv adj
      (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)) e.inv M
    rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
    exact h
  have he : e.inv.app M ≫ e.hom.app M = 𝟙 _ := e.inv_hom_id_app M
  change adj.unit.app M ≫ R.map (e.hom.app M) ≫
    b.hom.app ((Scheme.Modules.pullback (f ≫ g)).obj M) = _
  rw [b.hom.naturality, ← Category.assoc, hu, Category.assoc, ← Functor.map_comp,
    he, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

theorem Pullback.TensorCompositionUnits.pullbackComp_homEquiv (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (P : X.Modules)
    (h : (Scheme.Modules.pullback (f ≫ g)).obj M ⟶ P) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
        ((Scheme.Modules.pullbackComp f g).hom.app M ≫ h)) ≫
      (Scheme.Modules.pushforwardComp f g).hom.app P =
      (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _ h := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  have hn : (Scheme.Modules.pushforward g).map ((Scheme.Modules.pushforward f).map h) ≫
      (Scheme.Modules.pushforwardComp f g).hom.app P =
      (Scheme.Modules.pushforwardComp f g).hom.app ((Scheme.Modules.pullback (f ≫ g)).obj M) ≫
        (Scheme.Modules.pushforward (f ≫ g)).map h :=
    (Scheme.Modules.pushforwardComp f g).hom.naturality h
  rw [hn]
  simpa only [Category.assoc] using
    congrArg (fun a => a ≫ (Scheme.Modules.pushforward (f ≫ g)).map h)
      (Pullback.TensorCompositionUnits.pullbackComp_hom_unit f g M)

theorem Bilinear.Sheaves.SheafBilinearMap.pushforward_comp {M N P : X.Modules}
    (β : Bilinear.Sheaves.SheafBilinearMap M N P) (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((β.pushforward f).pushforward g).postcomp
      ((Scheme.Modules.pushforwardComp f g).hom.app P) =
      (β.pushforward (f ≫ g)).precomp
        ((Scheme.Modules.pushforwardComp f g).hom.app M)
        ((Scheme.Modules.pushforwardComp f g).hom.app N) := by
  ext U
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
end ComponentSource_42

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.TensorCompositionUnits"

@[expose] public section ComponentSource_43
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.ModuleValues -/

/-! # Module Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.ModuleValues

noncomputable section

/-! Ambient section values for local maps between canonical pullbacks of module sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

theorem openPullbackUnit_app_isIso (M : Y.Modules) (U : Y.Opens) (hU : U ≤ f.opensRange) :
    IsIso (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U) := by
  let : IsIso (((Scheme.Modules.restrictAdjunction f).unit.app M).app U) :=
    OpenModule.MapValues.moduleRestrictionUnit_app_isIso f M U hU
  have h := congrArg (fun ψ : M ⟶ (Scheme.Modules.pushforward f).obj
      ((Scheme.Modules.pullback f).obj M) => ψ.app U)
    ((Scheme.Modules.restrictAdjunction f).unit_leftAdjointUniq_hom_app
      (Scheme.Modules.pullbackPushforwardAdjunction f) M)
  rw [← h, Scheme.Modules.Hom.comp_app]
  infer_instance

variable {M N : Y.Modules}

def pullbackModuleRestrictionMap
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N) :
    M.restrict f ⟶ N.restrict f :=
  (Scheme.Modules.restrictFunctorIsoPullback f).hom.app M ≫ φ ≫
    (Scheme.Modules.restrictFunctorIsoPullback f).inv.app N

def openPullbackModuleValue
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    (U : Y.Opens) (hU : U ≤ f.opensRange) : Γ(M, U) →ₗ[Γ(Y, U)] Γ(N, U) := by
  letI := openPullbackUnit_app_isIso f N U hU
  exact Module.MapLocalFactor.moduleMapLocalFactor
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫ (Scheme.Modules.pushforward f).map φ)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) U

theorem openPullbackModuleValue_spec
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    (U : Y.Opens) (hU : U ≤ f.opensRange) (s : Γ(M, U)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).app U
      (openPullbackModuleValue f φ U hU s) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
        (Scheme.Modules.pushforward f).map φ).app U s := by
  let := openPullbackUnit_app_isIso f N U hU
  exact Module.MapLocalFactor.moduleMapLocalFactor_spec _ _ U s

theorem openPullbackModuleValue_restriction
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    (U : Y.Opens) (hU : U ≤ f.opensRange) :
    OpenModule.MapValues.openModuleMapValue f (pullbackModuleRestrictionMap f φ) U hU =
      openPullbackModuleValue f φ U hU := by
  let := openPullbackUnit_app_isIso f N U hU
  have hM : (Scheme.Modules.restrictAdjunction f).unit.app M ≫
      (Scheme.Modules.pushforward f).map ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M) =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M :=
    (Scheme.Modules.restrictAdjunction f).unit_leftAdjointUniq_hom_app
      (Scheme.Modules.pullbackPushforwardAdjunction f) M
  have hN : (Scheme.Modules.restrictAdjunction f).unit.app N ≫
      (Scheme.Modules.pushforward f).map ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app N) =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N :=
    (Scheme.Modules.restrictAdjunction f).unit_leftAdjointUniq_hom_app
      (Scheme.Modules.pullbackPushforwardAdjunction f) N
  have hα : ((Scheme.Modules.restrictAdjunction f).unit.app M ≫
      (Scheme.Modules.pushforward f).map (pullbackModuleRestrictionMap f φ)) ≫
      (Scheme.Modules.pushforward f).map ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app N) =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
        (Scheme.Modules.pushforward f).map φ := by
    have he : pullbackModuleRestrictionMap f φ ≫
        (Scheme.Modules.restrictFunctorIsoPullback f).hom.app N =
        (Scheme.Modules.restrictFunctorIsoPullback f).hom.app M ≫ φ := by
      simp only [pullbackModuleRestrictionMap, Category.assoc,
        (Scheme.Modules.restrictFunctorIsoPullback f).inv_hom_id_app, Category.comp_id]
    rw [Category.assoc, ← Functor.map_comp, he, Functor.map_comp, ← Category.assoc, hM]
  apply Module.MapLocalFactor.moduleMapLocalFactor_unique
  intro s
  have hNs := congrArg (fun ψ : N ⟶ (Scheme.Modules.pushforward f).obj
    ((Scheme.Modules.pullback f).obj N) => ψ.app U) hN
  rw [← hNs]
  change ((Scheme.Modules.pushforward f).map ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app N)).app U
    (((Scheme.Modules.restrictAdjunction f).unit.app N).app U
      (OpenModule.MapValues.openModuleMapValue f (pullbackModuleRestrictionMap f φ) U hU s)) = _
  rw [OpenModule.MapRecovery.openModuleMapValue_spec]
  exact ConcreteCategory.congr_hom (congrArg (fun ψ => ψ.app U) hα) s

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.ModuleValues
end ComponentSource_43

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.ModuleValues"

@[expose] public section ComponentSource_44
/- Original module: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapFactorTransport -/

/-! # Map Factor Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapFactorTransport

noncomputable section

/-! Local linear factorizations are unchanged by compatible comparison maps of their codomains. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {M N P Q : X.Modules}

theorem moduleMapLocalFactor_transport (α : M ⟶ P) (β : N ⟶ P) (ρ : P ⟶ Q)
    (α' : M ⟶ Q) (β' : N ⟶ Q) (hα : α ≫ ρ = α') (hβ : β ≫ ρ = β')
    (U : X.Opens) [IsIso (β.app U)] [IsIso (β'.app U)] :
    MapLocalFactor.moduleMapLocalFactor α β U = MapLocalFactor.moduleMapLocalFactor α' β' U := by
  apply MapLocalFactor.moduleMapLocalFactor_unique
  intro s
  rw [← hβ, ← hα]
  change ρ.app U (β.app U (MapLocalFactor.moduleMapLocalFactor α β U s)) = ρ.app U (α.app U s)
  rw [MapLocalFactor.moduleMapLocalFactor_spec]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapFactorTransport
end ComponentSource_44

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapFactorTransport"


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
    (`OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapFactorTransport.moduleMapLocalFactor_transport, "theorem")
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
    ("nonce", toJson "efd9cd5d1c7eaf760a00d8c75bae5887"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:efd9cd5d1c7eaf760a00d8c75bae5887"
