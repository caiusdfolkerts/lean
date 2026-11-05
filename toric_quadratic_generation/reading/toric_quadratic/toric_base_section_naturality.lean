module

public import PaperVerification.ToricCartierBaseSections
public import PaperVerification.ToricDominantFunctionField
public import Mathlib.AlgebraicGeometry.Group.Affine

@[expose] public section

/-! # Base scalars in actual regular and rational sections -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite

namespace PaperVerification.ToricSchemes.BaseSections

variable (k : Type u) [CommRing k]

theorem scalarMap_top_natural {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k))] (c : k) :
    f.appTop (scalarMap k Y ⊤ c)=scalarMap k X ⊤ c := by
  have h := congrArg
    (fun g : X ⟶ Spec (CommRingCat.of k)=>g.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c))
    (comp_over f (Spec (CommRingCat.of k)))
  simpa only [scalarMap,RingHom.comp_apply,homOfLE_refl,op_id,
    X.presheaf.map_id (op (⊤ : X.Opens)),Y.presheaf.map_id (op (⊤ : Y.Opens)),
    CommRingCat.hom_id,RingHom.id_apply,Scheme.Hom.comp_appTop,
    ConcreteCategory.comp_apply] using h

theorem scalarMap_affine_top (A : Type u) [CommRing A] [Algebra k A] (c : k) :
    scalarMap k (Spec (CommRingCat.of A)) ⊤ c =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv (algebraMap k A c) := by
  have h := congrArg
    (fun f : CommRingCat.of k ⟶ Γ(Spec (CommRingCat.of A),⊤) => f.hom c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k A)))
  simpa only [scalarMap,RingHom.comp_apply,homOfLE_refl,op_id,
    (Spec (CommRingCat.of A)).presheaf.map_id (op (⊤ : (Spec (CommRingCat.of A)).Opens)),
    CommRingCat.hom_id,RingHom.id_apply,specOverSpec_over,
    CommRingCat.hom_comp,CommRingCat.hom_ofHom] using h.symm

theorem scalarMap_restrict {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] {U V : X.Opens} (h : V≤U) (c : k) :
    X.presheaf.map (homOfLE h).op (scalarMap k X U c)=scalarMap k X V c := by
  simp only [scalarMap,RingHom.comp_apply]
  exact congrArg (fun f=>f (((X ↘ Spec (CommRingCat.of k)).appTop).hom
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)))
      (X.presheaf.map_comp (homOfLE le_top).op (homOfLE h).op).symm

open scoped BaseSections

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]

theorem germ_scalarMap (U : X.Opens) [Nonempty U] (c : k) :
    X.germToFunctionField U (scalarMap k X U c)=algebraMap k X.functionField c := by
  have h := scalarMap_restrict k (X:=X) (U:=⊤) (V:=U) le_top c
  rw [← h,germToFunctionField_restrict]
  rfl

/-- The scalar-compatible regular-function embedding in the actual
generic stalk, on every nonempty open. -/
def regularValueAlgHom (U : X.Opens) [Nonempty U] :
    Γ(X,U) →ₐ[k] X.functionField where
  __ := (X.germToFunctionField U).hom
  commutes' := germ_scalarMap k U

/-- Dominant pullback preserves the scalars from the actual structure
morphisms. -/
def dominantFunctionFieldAlgHom (f : X ⟶ Y) [IsDominant f]
    [f.IsOver (Spec (CommRingCat.of k))] : Y.functionField →ₐ[k] X.functionField where
  __ := dominantFunctionFieldMap f
  commutes' c := by
    letI : Nonempty (f ⁻¹ᵁ (⊤ : Y.Opens)) := dominant_preimage_nonempty f ⊤
    change dominantFunctionFieldMap f
      (Y.germToFunctionField ⊤ (scalarMap k Y ⊤ c)) = _
    rw [dominantFunctionFieldMap_germ]
    change X.germToFunctionField ⊤ (f.appTop (scalarMap k Y ⊤ c)) = _
    rw [scalarMap_top_natural]
    rfl

end PaperVerification.ToricSchemes.BaseSections
