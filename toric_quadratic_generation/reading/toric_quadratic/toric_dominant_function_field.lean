module

public import PaperVerification.ToricFunctionFieldBridge
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

@[expose] public section

/-! # Actual function-field pullback along a dominant morphism -/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory TopologicalSpace

/-- A nonempty actual open subscheme of a preirreducible scheme is
dominant. This is a topological consequence of the open immersion, not
an additional density assumption on a chart. -/
instance (priority := 80) openImmersion_isDominant_of_preirreducible
    {U X : Scheme.{u}} [Nonempty U] [PreirreducibleSpace X]
    (j : U ⟶ X) [IsOpenImmersion j] : IsDominant j :=
  ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace j
    j.isOpenEmbedding.isOpenMap⟩

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsDominant f]
    [IrreducibleSpace X] [IrreducibleSpace Y]

theorem genericPoint_eq_of_isDominant :
    f (genericPoint X)=genericPoint Y := by
  apply ((genericPoint_spec Y).eq _).symm
  simpa only [Set.image_univ,f.denseRange.closure_range] using
    (genericPoint_spec X).image f.continuous

/-- This is the genuine map on generic stalks, with generic points
identified by dominance. No fraction-field embedding is postulated. -/
def dominantFunctionFieldMap : Y.functionField →+* X.functionField :=
  ((Y.presheaf.stalkCongr
      (.of_eq (genericPoint_eq_of_isDominant f).symm)).hom ≫
    f.stalkMap (genericPoint X)).hom

theorem dominant_preimage_nonempty (U : Y.Opens) [Nonempty U] :
    Nonempty (f ⁻¹ᵁ U) := by
  refine ⟨⟨genericPoint X,?_⟩⟩
  change f (genericPoint X)∈U
  rw [genericPoint_eq_of_isDominant]
  exact ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr
    (by simpa using (show Nonempty U from inferInstance))

set_option backward.isDefEq.respectTransparency.types false in
theorem dominantFunctionFieldMap_germ_hom (U : Y.Opens) [Nonempty U]
    [Nonempty (f ⁻¹ᵁ U)] :
    Y.germToFunctionField U ≫ CommRingCat.ofHom (dominantFunctionFieldMap f) =
      f.app U ≫ X.germToFunctionField (f ⁻¹ᵁ U) := by
  change Y.germToFunctionField U ≫
    ((Y.presheaf.stalkCongr
      (.of_eq (genericPoint_eq_of_isDominant f).symm)).hom ≫
      f.stalkMap (genericPoint X)) = _
  simp only [Scheme.germToFunctionField,TopCat.Presheaf.stalkCongr_hom,
    ← Category.assoc]
  rw [TopCat.Presheaf.germ_stalkSpecializes]
  exact f.germ_stalkMap U (genericPoint X) _

@[simp] theorem dominantFunctionFieldMap_germ (U : Y.Opens) [Nonempty U]
    [Nonempty (f ⁻¹ᵁ U)] (a : Γ(Y,U)) :
    dominantFunctionFieldMap f (Y.germToFunctionField U a) =
      X.germToFunctionField (f ⁻¹ᵁ U) (f.app U a) :=
  congrArg (fun g=>g a) (dominantFunctionFieldMap_germ_hom f U)

set_option backward.isDefEq.respectTransparency.types false in
theorem dominantFunctionFieldMap_comp {Z : Scheme.{u}} [IrreducibleSpace Z]
    (g : Y ⟶ Z) [IsDominant g] :
    dominantFunctionFieldMap (f ≫ g) =
      (dominantFunctionFieldMap f).comp (dominantFunctionFieldMap g) := by
  apply CommRingCat.hom_ext_iff.mp
  apply Z.presheaf.stalk_hom_ext
  intro U hU
  letI : Nonempty U := ⟨⟨genericPoint Z,hU⟩⟩
  letI : Nonempty (g ⁻¹ᵁ U) := dominant_preimage_nonempty g U
  letI : Nonempty (f ⁻¹ᵁ (g ⁻¹ᵁ U)) :=
    dominant_preimage_nonempty f (g ⁻¹ᵁ U)
  letI : Nonempty ((f ≫ g) ⁻¹ᵁ U) := dominant_preimage_nonempty (f ≫ g) U
  change Z.germToFunctionField U ≫ CommRingCat.ofHom (dominantFunctionFieldMap (f≫g)) =
    Z.germToFunctionField U ≫
      (CommRingCat.ofHom (dominantFunctionFieldMap g) ≫
        CommRingCat.ofHom (dominantFunctionFieldMap f))
  calc
    _ = (g.app U ≫ f.app (g ⁻¹ᵁ U)) ≫
        X.germToFunctionField (f ⁻¹ᵁ (g ⁻¹ᵁ U)) :=
      dominantFunctionFieldMap_germ_hom (f ≫ g) U
    _ = g.app U ≫ (f.app (g ⁻¹ᵁ U) ≫
        X.germToFunctionField (f ⁻¹ᵁ (g ⁻¹ᵁ U))) := Category.assoc _ _ _
    _ = g.app U ≫ (Y.germToFunctionField (g ⁻¹ᵁ U) ≫
        CommRingCat.ofHom (dominantFunctionFieldMap f)) :=
      congrArg (fun h : Γ(Y,g ⁻¹ᵁ U) ⟶ X.functionField => g.app U ≫ h)
        (dominantFunctionFieldMap_germ_hom f (g ⁻¹ᵁ U)).symm
    _ = (g.app U ≫ Y.germToFunctionField (g ⁻¹ᵁ U)) ≫
        CommRingCat.ofHom (dominantFunctionFieldMap f) := (Category.assoc _ _ _).symm
    _ = (Z.germToFunctionField U ≫ CommRingCat.ofHom (dominantFunctionFieldMap g)) ≫
        CommRingCat.ofHom (dominantFunctionFieldMap f) :=
      congrArg (fun h : Γ(Z,U) ⟶ Y.functionField =>
        h ≫ CommRingCat.ofHom (dominantFunctionFieldMap f))
        (dominantFunctionFieldMap_germ_hom g U).symm
    _ = _ := Category.assoc _ _ _

theorem dominantFunctionFieldMap_injective [IsIntegral X] [IsIntegral Y] :
    Function.Injective (dominantFunctionFieldMap f) :=
  (dominantFunctionFieldMap f).injective

theorem dominantFunctionFieldMap_eq_openImmersion [IsOpenImmersion f] :
    dominantFunctionFieldMap f=(openImmersionFunctionFieldEquiv f).toRingHom := rfl

/-- Compatibility with every actual local ring, not just global regular
functions. This is the basic regularity input for Cartier pullback. -/
theorem dominantFunctionFieldMap_stalk [IsIntegral X] [IsIntegral Y]
    (x : X) (a : Y.presheaf.stalk (f x)) :
    dominantFunctionFieldMap f
        (algebraMap (Y.presheaf.stalk (f x)) Y.functionField a) =
      algebraMap (X.presheaf.stalk x) X.functionField (f.stalkMap x a) := by
  obtain ⟨U,hx,s,rfl⟩ := Y.presheaf.exists_germ_eq a
  letI : Nonempty U := ⟨⟨f x,hx⟩⟩
  letI : Nonempty (f ⁻¹ᵁ U) := ⟨⟨x,hx⟩⟩
  rw [Y.algebraMap_germ_eq_germToFunctionField hx s,
    dominantFunctionFieldMap_germ,f.germ_stalkMap_apply,
    X.algebraMap_germ_eq_germToFunctionField hx (f.app U s)]

theorem dominantFunctionFieldMap_mem_regularAt [IsIntegral X] [IsIntegral Y]
    (x : X) (a : Y.functionField) (ha : a∈regularAtSubring Y (f x)) :
    dominantFunctionFieldMap f a∈regularAtSubring X x := by
  obtain ⟨s,rfl⟩ := ha
  exact ⟨f.stalkMap x s,(dominantFunctionFieldMap_stalk f x s).symm⟩

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.dominantFunctionFieldMap_stalk
