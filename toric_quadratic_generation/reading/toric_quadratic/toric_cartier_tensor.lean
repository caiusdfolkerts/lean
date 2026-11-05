module

public import PaperVerification.ToricCartierProducts
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.Topology.Sheaves.LocallySurjective

@[expose] public section

/-!
# The genuine tensor sheaf of two fractional Cartier sheaves

The tensor sheaf is the sheafification of the ordinary sectionwise
module tensor product. Multiplication of rational functions defines a
natural map to the fractional sheaf with multiplied local generators.
On a common trivializing open, this map is the usual rank-one tensor
isomorphism. Consequently the presheaf map is locally bijective, so its
sheafification is an actual sheaf isomorphism. No tensor-product or
section-space identification is inserted into the Cartier definitions.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open MonoidalCategory
open scoped TensorProduct

variable {X : Scheme.{u}}

/-- The ordinary sectionwise tensor presheaf over the structure sheaf. -/
def tensorPresheaf (F G : X.Modules) : PresheafOfModules X.ringCatSheaf.obj :=
  PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) F.val G.val

/-- The usual tensor product of sheaves of modules, defined by the
standard sheafification construction. -/
def tensorSheaf (F G : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (tensorPresheaf F G)

/-- The canonical map of the sectionwise tensor presheaf into its sheaf. -/
def tensorSheafUnit (F G : X.Modules) :
    tensorPresheaf F G ⟶ (tensorSheaf F G).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app _

/-- Actual sheaf isomorphisms induce the usual tensor-sheaf isomorphism. -/
def tensorSheafIso {F F' G G' : X.Modules} (e : F ≅ F') (f : G ≅ G') :
    tensorSheaf F G ≅ tensorSheaf F' G' := by
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing X.presheaf))
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (MonoidalCategory.tensorIso ((SheafOfModules.forget _).mapIso e)
      ((SheafOfModules.forget _).mapIso f))

variable [IsIntegral X]

namespace RationalCartierCocycle

variable (C D : RationalCartierCocycle X)

/-- In genuine local frames, rational multiplication is ordinary
multiplication of the two regular coefficients. -/
theorem localCoordinates_sectionProduct (i : C.index) (j : D.index)
    (U : X.Opens) (hU : U≤C.openSet i⊓D.openSet j)
    (s : Γ(C.sheaf,U)) (t : Γ(D.sheaf,U)) :
    (C.mul D).localCoordinates (i,j) U hU (C.sectionProduct D U s t) =
      C.localCoordinates i U (hU.trans inf_le_left) s *
        D.localCoordinates j U (hU.trans inf_le_right) t := by
  classical
  by_cases hnonempty : Nonempty U
  · letI := hnonempty
    apply X.germToFunctionField_injective U
    calc
      X.germToFunctionField U
          ((C.mul D).localCoordinates (i,j) U hU (C.sectionProduct D U s t)) =
          rationalValue X U (C.sectionProduct D U s t).val /
            ((C.mul D).generator (i,j) : X.functionField) :=
        (C.mul D).localCoordinates_value (i,j) U hU (C.sectionProduct D U s t)
      _ = (rationalValue X U s.val / (C.generator i : X.functionField)) *
          (rationalValue X U t.val / (D.generator j : X.functionField)) := by
        change rationalValue X U (rationalMul U s.val t.val) /
          ((C.generator i : X.functionField)*(D.generator j : X.functionField)) = _
        rw [rationalValue_mul, div_mul_div_comm]
      _ = X.germToFunctionField U
          (C.localCoordinates i U (hU.trans inf_le_left) s) *
          X.germToFunctionField U
            (D.localCoordinates j U (hU.trans inf_le_right) t) :=
        congrArg₂ (· * ·)
          (C.localCoordinates_value i U (hU.trans inf_le_left) s).symm
          (D.localCoordinates_value j U (hU.trans inf_le_right) t).symm
      _ = X.germToFunctionField U
          (C.localCoordinates i U (hU.trans inf_le_left) s *
            D.localCoordinates j U (hU.trans inf_le_right) t) :=
        (map_mul (X.germToFunctionField U).hom _ _).symm
  · have hbot : U=⊥ := by
      apply le_antisymm
      · intro x hx
        exact False.elim (hnonempty ⟨⟨x,hx⟩⟩)
      · exact bot_le
    letI := regularSections_subsingleton_of_empty X U hbot
    exact Subsingleton.elim _ _

/-- The explicit rank-one tensor isomorphism on a common trivializing
open, obtained from the independently constructed local frames. -/
def localTensorEquiv (i : C.index) (j : D.index)
    (U : X.Opens) (hU : U≤C.openSet i⊓D.openSet j) :
    Γ(C.sheaf,U) ⊗[Γ(X,U)] Γ(D.sheaf,U) ≃ₗ[Γ(X,U)] Γ((C.mul D).sheaf,U) :=
  ((TensorProduct.congr
    (C.localCoordinates i U (hU.trans inf_le_left))
    (D.localCoordinates j U (hU.trans inf_le_right))).trans
      (TensorProduct.lid Γ(X,U) Γ(X,U))).trans
        ((C.mul D).localCoordinates (i,j) U hU).symm

theorem sectionMultiplication_eq_localTensorEquiv (i : C.index) (j : D.index)
    (U : X.Opens) (hU : U≤C.openSet i⊓D.openSet j) :
    C.sectionMultiplication D U = (C.localTensorEquiv D i j U hU).toLinearMap := by
  apply TensorProduct.ext'
  intro s t
  apply ((C.mul D).localCoordinates (i,j) U hU).injective
  simp only [sectionMultiplication_tmul, localCoordinates_sectionProduct,
    localTensorEquiv, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, TensorProduct.lid_tmul,
    LinearEquiv.apply_symm_apply, smul_eq_mul]

theorem sectionMultiplication_bijective_on (i : C.index) (j : D.index)
    (U : X.Opens) (hU : U≤C.openSet i⊓D.openSet j) :
    Function.Bijective (C.sectionMultiplication D U) := by
  rw [C.sectionMultiplication_eq_localTensorEquiv D i j U hU]
  exact (C.localTensorEquiv D i j U hU).bijective

/-- Rational multiplication is a morphism of the actual sectionwise
tensor presheaf, since it commutes with actual restrictions. -/
def tensorPresheafMultiplication :
    tensorPresheaf C.sheaf D.sheaf ⟶ (C.mul D).sheaf.val :=
  PresheafOfModulesOfCommRing.homMk (R := X.presheaf)
    (M₁ := tensorPresheaf C.sheaf D.sheaf) (M₂ := (C.mul D).sheaf.val)
    (fun U => ModuleCat.ofHom
      (X := (tensorPresheaf C.sheaf D.sheaf).obj U)
      (Y := ((C.mul D).sheaf.val).obj U)
      (C.sectionMultiplication D U.unop))
    (by
      intro U V f
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro s t
      change C.sectionMultiplication D V.unop
          ((tensorPresheaf C.sheaf D.sheaf).map f (s ⊗ₜ[Γ(X,U.unop)] t)) =
        (C.mul D).sheaf.presheaf.map f (C.sectionMultiplication D U.unop
          (s ⊗ₜ[Γ(X,U.unop)] t))
      have hm : (tensorPresheaf C.sheaf D.sheaf).map f
          (s ⊗ₜ[Γ(X,U.unop)] t) =
          C.sheaf.val.map f s ⊗ₜ[Γ(X,V.unop)] D.sheaf.val.map f t :=
        PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul
          (R := X.presheaf) (M₁ := C.sheaf.val) (M₂ := D.sheaf.val) f s t
      exact (congrArg (C.sectionMultiplication D V.unop) hm).trans
        (C.sectionProduct_restrict D f.unop s t).symm)

@[simp] theorem tensorPresheafMultiplication_app (U : X.Opens)
    (z : Γ(C.sheaf,U) ⊗[Γ(X,U)] Γ(D.sheaf,U)) :
    (C.tensorPresheafMultiplication D).app (op U) z =
      C.sectionMultiplication D U z := rfl

/-- Local frames prove local injectivity of the presheaf multiplication. -/
instance tensorPresheafMultiplication_locallyInjective :
    CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (C.tensorPresheafMultiplication D)) where
  equalizerSieve_mem {U} s t h := by
    intro x hx
    obtain ⟨i,hi⟩ := C.covers x
    obtain ⟨j,hj⟩ := D.covers x
    let V : X.Opens := U.unop ⊓ (C.openSet i ⊓ D.openSet j)
    let f : V ⟶ U.unop := homOfLE inf_le_left
    refine ⟨V,f,?_,⟨hx,hi,hj⟩⟩
    change (tensorPresheaf C.sheaf D.sheaf).presheaf.map f.op s =
      (tensorPresheaf C.sheaf D.sheaf).presheaf.map f.op t
    apply (C.sectionMultiplication_bijective_on D i j V inf_le_right).injective
    change (C.tensorPresheafMultiplication D).app (op V)
        ((tensorPresheaf C.sheaf D.sheaf).map f.op s) =
      (C.tensorPresheafMultiplication D).app (op V)
        ((tensorPresheaf C.sheaf D.sheaf).map f.op t)
    rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply]
    exact congrArg ((C.mul D).sheaf.presheaf.map f.op) h

/-- Local frames prove local surjectivity of the presheaf multiplication. -/
instance tensorPresheafMultiplication_locallySurjective :
    CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (C.tensorPresheafMultiplication D)) where
  imageSieve_mem {U} s := by
    intro x hx
    obtain ⟨i,hi⟩ := C.covers x
    obtain ⟨j,hj⟩ := D.covers x
    let V : X.Opens := U ⊓ (C.openSet i ⊓ D.openSet j)
    let f : V ⟶ U := homOfLE inf_le_left
    obtain ⟨t,ht⟩ := (C.sectionMultiplication_bijective_on D i j V inf_le_right).surjective
      ((C.mul D).sheaf.presheaf.map f.op s)
    exact ⟨V,f,⟨t,ht⟩,⟨hx,hi,hj⟩⟩

instance tensorPresheafMultiplication_sheafification_isIso :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (C.tensorPresheafMultiplication D)) := by
  have hW := (Opens.grothendieckTopology X).W_of_isLocallyBijective
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
      (C.tensorPresheafMultiplication D))
  change ((Opens.grothendieckTopology X).W.inverseImage
    (PresheafOfModules.toPresheaf X.ringCatSheaf.obj))
      (C.tensorPresheafMultiplication D) at hW
  rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (𝟙 X.ringCatSheaf.obj)] at hW
  exact hW

/-- The genuine sheaf tensor product is canonically isomorphic to the
fractional sheaf obtained by multiplying the actual local equations. -/
def tensorSheafMulIso : tensorSheaf C.sheaf D.sheaf ≅ (C.mul D).sheaf := by
  letI := C.tensorPresheafMultiplication_sheafification_isIso D
  exact asIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (C.tensorPresheafMultiplication D)) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit).app (C.mul D).sheaf

/-- The tensor isomorphism is the sheafification of the original
multiplication map, so its map on pure section tensors is the prescribed
actual rational multiplication. -/
theorem tensorSheafMulIso_unit :
    tensorSheafUnit C.sheaf D.sheaf ≫ (C.tensorSheafMulIso D).hom.val =
      C.tensorPresheafMultiplication D := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  have h : (adj.homEquiv (tensorPresheaf C.sheaf D.sheaf) (C.mul D).sheaf).symm
      (C.tensorPresheafMultiplication D) = (C.tensorSheafMulIso D).hom := by
    rw [Adjunction.homEquiv_counit]
    rfl
  have he := congrArg
    (adj.homEquiv (tensorPresheaf C.sheaf D.sheaf) (C.mul D).sheaf) h
  ext U s
  have he' := congrArg (fun φ => φ.app U s) he
  simp only [Equiv.apply_symm_apply,Adjunction.homEquiv_unit,
    PresheafOfModules.comp_app,ConcreteCategory.comp_apply] at he'
  dsimp only [Functor.comp_obj,Functor.comp_map,SheafOfModules.forget,
    PresheafOfModules.restrictScalars,PresheafOfModules.restrictScalarsObj,
    ModuleCat.restrictScalars,ModuleCat.RestrictScalars.obj',
    ModuleCat.RestrictScalars.map'] at he'
  exact he'.symm

@[simp] theorem tensorSheafMulIso_pure_sections (U : X.Opens)
    (s : Γ(C.sheaf,U)) (t : Γ(D.sheaf,U)) :
    (C.tensorSheafMulIso D).hom.app U
      ((tensorSheafUnit C.sheaf D.sheaf).app (op U) (s ⊗ₜ[Γ(X,U)] t)) =
        C.sectionProduct D U s t := by
  have h := congrArg (fun f => f.app (op U) (s ⊗ₜ[Γ(X,U)] t))
    (C.tensorSheafMulIso_unit D)
  simp only [PresheafOfModules.comp_app,ConcreteCategory.comp_apply,
    tensorPresheafMultiplication_app] at h
  change (C.tensorSheafMulIso D).hom.app U
    ((tensorSheafUnit C.sheaf D.sheaf).app (op U) (s ⊗ₜ[Γ(X,U)] t)) =
      C.sectionMultiplication D U (s ⊗ₜ[Γ(X,U)] t) at h
  exact h.trans (C.sectionMultiplication_tmul D U s t)

end RationalCartierCocycle

namespace CartierData

variable (D E : CartierData X)

/-- The addition of arbitrary actual fractional Cartier presentations
agrees with the ordinary tensor product of their actual sheaves. -/
def tensorSheafAddIso : tensorSheaf D.sheaf E.sheaf ≅ (D.add E).sheaf :=
  tensorSheafIso D.presentationIso E.presentationIso ≪≫
    D.localCocycle.tensorSheafMulIso E.localCocycle

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.tensorSheafMulIso
#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.tensorSheafMulIso_pure_sections
#print axioms PaperVerification.ToricSchemes.CartierData.tensorSheafAddIso
