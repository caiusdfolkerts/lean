module

public import PaperVerification.ToricFunctionFieldBridge

@[expose] public section

/-!
# Pulling regular functions through an actual affine chart square

This argument does not require dominance. A function which is regular
on an ambient affine chart pulls back through its actual coordinate-ring
homomorphism. The conclusion is expressed in the function field of the
source only after pulling back the regular section.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (R S : CommRingCat.{u}) [IsDomain R] [IsDomain S]
    (j : Spec R ⟶ X) (l : Spec S ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion l]

/-- The actual regular function on the image of an affine chart. -/
def affineChartSection (r : R) : Γ(X,j ''ᵁ (⊤ : (Spec R).Opens)) :=
  (j.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv r)

theorem affineChartSection_germ
    [Nonempty (j ''ᵁ (⊤ : (Spec R).Opens))] (r : R) :
    X.germToFunctionField (j ''ᵁ (⊤ : (Spec R).Opens))
      (affineChartSection R j r) = affineOpenCoordinateMap R j r :=
  (openImmersionRegularToFunctionField_eq_germ_image j ⊤
    ((Scheme.ΓSpecIso R).inv r)).symm

variable (f : Y ⟶ X) (φ : R ⟶ S)
    (hcomm : l ≫ f = Spec.map φ ≫ j)

include hcomm in
theorem affineChartSquare_image_le :
    l ''ᵁ (⊤ : (Spec S).Opens) ≤ f ⁻¹ᵁ (j ''ᵁ (⊤ : (Spec R).Opens)) := by
  rintro y ⟨q,hq,rfl⟩
  exact ⟨Spec.map φ q,trivial,
    (congrArg (fun g : Spec S ⟶ X=>g q) hcomm).symm⟩

set_option backward.isDefEq.respectTransparency.types false in
theorem affineChartSquare_sections :
    f.appLE (j ''ᵁ (⊤ : (Spec R).Opens)) (l ''ᵁ (⊤ : (Spec S).Opens))
        (affineChartSquare_image_le R S j l f φ hcomm) ≫ (l.appIso ⊤).hom =
      (j.appIso ⊤).hom ≫ (Spec.map φ).appTop := by
  rw [l.appIso_hom',j.appIso_hom']
  change f.appLE _ _ _ ≫ l.appLE _ ⊤ _ =
    j.appLE _ ⊤ _ ≫ (Spec.map φ).appLE ⊤ ⊤ le_top
  rw [Scheme.Hom.appLE_comp_appLE,Scheme.Hom.appLE_comp_appLE]
  have hc {a b : Spec S ⟶ X} (hab : a = b)
      (ha : (⊤ : (Spec S).Opens) ≤ a ⁻¹ᵁ (j ''ᵁ (⊤ : (Spec R).Opens)))
      (hb : (⊤ : (Spec S).Opens) ≤ b ⁻¹ᵁ (j ''ᵁ (⊤ : (Spec R).Opens))) :
      a.appLE (j ''ᵁ (⊤ : (Spec R).Opens)) ⊤ ha =
        b.appLE (j ''ᵁ (⊤ : (Spec R).Opens)) ⊤ hb := by
    cases hab
    rfl
  have ha : (⊤ : (Spec S).Opens) ≤ (l ≫ f) ⁻¹ᵁ (j ''ᵁ (⊤ : (Spec R).Opens)) :=
    (l.preimage_image_eq ⊤).ge.trans
      (l.preimage_mono (affineChartSquare_image_le R S j l f φ hcomm))
  exact hc hcomm ha (hcomm ▸ ha)

/-- Equality of genuine regular sections on the source chart image. -/
theorem affineChartSection_pullback (r : R) :
    f.appLE (j ''ᵁ (⊤ : (Spec R).Opens)) (l ''ᵁ (⊤ : (Spec S).Opens))
      (affineChartSquare_image_le R S j l f φ hcomm)
      (affineChartSection R j r) = affineChartSection S l (φ r) := by
  apply (l.appIso ⊤).commRingCatIsoToRingEquiv.injective
  calc
    (l.appIso ⊤).hom
        (f.appLE _ _ (affineChartSquare_image_le R S j l f φ hcomm)
          (affineChartSection R j r)) =
      (Spec.map φ).appTop ((j.appIso ⊤).hom (affineChartSection R j r)) :=
        congrArg (fun g=>g (affineChartSection R j r))
          (affineChartSquare_sections R S j l f φ hcomm)
    _ = (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r) := by
      simp only [affineChartSection,Iso.inv_hom_id_apply]
    _ = (Scheme.ΓSpecIso S).inv (φ r) :=
      (congrArg (fun g=>g r) (Scheme.ΓSpecIso_inv_naturality φ)).symm
    _ = (l.appIso ⊤).hom (affineChartSection S l (φ r)) := by
      simp only [affineChartSection,Iso.inv_hom_id_apply]

include hcomm in
/-- On any smaller open, a regular function with the specified affine
coordinate value pulls back to the value of the actual affine ring map.
Only the regular section is pulled through `f`; no map `K(X) → K(Y)` is
used or assumed. -/
theorem affineChartSection_pullback_value
    (hpre : f ⁻¹ᵁ (j ''ᵁ (⊤ : (Spec R).Opens)) =
      l ''ᵁ (⊤ : (Spec S).Opens))
    (U : X.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)]
    (hU : U≤j ''ᵁ (⊤ : (Spec R).Opens))
    (r : Γ(X,U)) (a : R)
    (hr : X.germToFunctionField U r=affineOpenCoordinateMap R j a) :
    Y.germToFunctionField (f ⁻¹ᵁ U) (f.app U r) =
      affineOpenCoordinateMap S l (φ a) := by
  let V := j ''ᵁ (⊤ : (Spec R).Opens)
  let W := l ''ᵁ (⊤ : (Spec S).Opens)
  letI : Nonempty V := openImmersion_image_nonempty j ⊤
  letI : Nonempty W := openImmersion_image_nonempty l ⊤
  have hW : f ⁻¹ᵁ U≤W := by
    change f ⁻¹ᵁ U ≤ l ''ᵁ (⊤ : (Spec S).Opens)
    rw [← hpre]
    exact f.preimage_mono hU
  have heq : r = X.presheaf.map (homOfLE hU).op (affineChartSection R j a) := by
    apply X.germToFunctionField_injective U
    rw [germToFunctionField_restrict,affineChartSection_germ,hr]
  rw [heq]
  have hs : f.app U
      (X.presheaf.map (homOfLE hU).op (affineChartSection R j a)) =
      Y.presheaf.map (homOfLE hW).op
        (f.appLE V W (affineChartSquare_image_le R S j l f φ hcomm)
          (affineChartSection R j a)) := by
    have hm : X.presheaf.map (homOfLE hU).op ≫ f.app U =
        f.appLE V W (affineChartSquare_image_le R S j l f φ hcomm) ≫
          Y.presheaf.map (homOfLE hW).op := by
      rw [f.app_eq_appLE,f.map_appLE,f.appLE_map]
    exact congrArg
      (fun g : Γ(X,V) ⟶ Γ(Y,f ⁻¹ᵁ U) => g.hom (affineChartSection R j a)) hm
  rw [hs,affineChartSection_pullback R S j l f φ hcomm,germToFunctionField_restrict,
    affineChartSection_germ]

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.affineChartSection_pullback_value
