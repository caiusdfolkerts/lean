module

public import PaperVerification.ToricActionProductProperties
public import PaperVerification.ToricBaseSectionNaturality
public import PaperVerification.ToricDominantAffineCoordinates
public import PaperVerification.ToricTensorFractions

@[expose] public section

/-!
# The actual affine charts of a torus product

For an actual affine open immersion `Spec R → X`, its inverse image in
the torus product is literally the spectrum of `k[M] ⊗ R`. The two
projection coordinate maps and the regular-function range in the actual
generic stalk are proved from the genuine pullback and sheaf maps.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory
open PaperVerification.ToricCharacters
open scoped TensorProduct BaseSections Classical

section AffineCoordinates

variable (k : Type u) [CommRing k]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of k))]
    (R : Type u) [CommRing R] [IsDomain R] [Algebra k R]
    (j : Spec (CommRingCat.of R)⟶X) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k))]

/-- The exact affine coordinate embedding respects the actual base
field structure, as proved by scalar naturality through the chart. -/
def affineCoordinateValueAlgHom : R →ₐ[k] X.functionField where
  __ := affineOpenCoordinateMap (CommRingCat.of R) j
  commutes' c := by
    apply (affineOpenFunctionFieldEquiv (CommRingCat.of R) j).injective
    change affineOpenFunctionFieldEquiv (CommRingCat.of R) j
      (affineOpenCoordinateMap (CommRingCat.of R) j (algebraMap k R c)) = _
    rw [affineOpenFunctionFieldEquiv_coordinateMap]
    change _=affineOpenFunctionFieldEquiv (CommRingCat.of R) j
      (X.germToFunctionField ⊤ (BaseSections.scalarMap k X ⊤ c))
    rw [affineOpenFunctionFieldEquiv_germ_top,
      BaseSections.scalarMap_top_natural k j c, BaseSections.scalarMap_affine_top k R c]
    simp only [Iso.inv_hom_id_apply]

theorem affineCoordinateValueAlgHom_injective :
    Function.Injective (affineCoordinateValueAlgHom k R j) :=
  (openImmersionGlobalToFunctionField_injective j).comp
    (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.injective

end AffineCoordinates

theorem affineOpenCoordinate_range {X : Scheme.{u}} [IsIntegral X]
    (R : CommRingCat.{u}) [IsDomain R] (j : Spec R⟶X) [IsOpenImmersion j] :
    letI : Nonempty (j ''ᵁ (⊤ : (Spec R).Opens)) := openImmersion_image_nonempty j ⊤
    Set.range (affineOpenCoordinateMap R j)=
      Set.range (X.germToFunctionField (j ''ᵁ (⊤ : (Spec R).Opens))) := by
  letI : Nonempty (j ''ᵁ (⊤ : (Spec R).Opens)) := openImmersion_image_nonempty j ⊤
  ext x
  constructor
  · rintro ⟨r,rfl⟩
    exact ⟨affineChartSection R j r,affineChartSection_germ R j r⟩
  · rintro ⟨r,rfl⟩
    refine ⟨(Scheme.ΓSpecIso R).hom ((j.appIso ⊤).hom r),?_⟩
    rw [← affineChartSection_germ]
    congr 1
    simp only [affineChartSection,Iso.hom_inv_id_apply]

section AffineOpen

variable (k : Type u) [CommRing k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] (U : X.Opens) (hU : IsAffineOpen U)

theorem affineOpen_fromSpec_toBase :
    hU.fromSpec≫(X ↘ Spec (CommRingCat.of k))=
      Spec.map (CommRingCat.ofHom (BaseSections.scalarMap k X U)) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec (X ↘ Spec (CommRingCat.of k))
    (isAffineOpen_top (Spec (CommRingCat.of k))) hU
    (show U ≤ (X ↘ Spec (CommRingCat.of k)) ⁻¹ᵁ ⊤ by simp)
  rw [← h,IsAffineOpen.fromSpec_top,Scheme.isoSpec_Spec_inv,← Spec.map_comp]
  congr 1

theorem affineOpen_fromSpec_isOver :
    hU.fromSpec.IsOver (Spec (CommRingCat.of k)) :=
  ⟨affineOpen_fromSpec_toBase k X U hU⟩

theorem affineOpenCoordinateMap_fromSpec [IsIntegral X] [Nonempty U] (r : Γ(X,U)) :
    affineOpenCoordinateMap Γ(X,U) hU.fromSpec r=X.germToFunctionField U r := by
  letI : Nonempty (hU.fromSpec ⁻¹ᵁ U) := openImmersion_preimage_nonempty hU.fromSpec U
  apply (openImmersionFunctionFieldEquiv hU.fromSpec).injective
  change openImmersionFunctionFieldEquiv hU.fromSpec
    ((openImmersionFunctionFieldEquiv hU.fromSpec).symm
      ((Spec Γ(X,U)).germToFunctionField ⊤ ((Scheme.ΓSpecIso Γ(X,U)).inv r))) = _
  rw [RingEquiv.apply_symm_apply, openImmersionFunctionFieldEquiv_germ,hU.fromSpec_app_self]
  simp only [ConcreteCategory.comp_apply]
  exact (germToFunctionField_restrict (Spec Γ(X,U))
    (eqToHom hU.fromSpec_preimage_self) ((Scheme.ΓSpecIso Γ(X,U)).inv r)).symm

end AffineOpen

section Product

variable (k : Type u) [Field k] (n : ℕ)
    (X : Over (Spec (CommRingCat.of k)))
    (R : Type u) [CommRing R] [Algebra k R]
    (j : Spec (CommRingCat.of R)⟶X.left)
    [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k))]

local notation "A" => AddMonoidAlgebra k (Fin n→ℤ)
local notation "G" => splitTorusOver k (Fin n→ℤ)
local notation "Y" => Functor.obj (Over.forget (Spec (CommRingCat.of k))) (G ⊗ X)

/-- The actual affine inverse image, using the literal tensor coordinate
ring and the genuine base-change map of the open immersion. -/
def torusProductAffineChart : Spec (CommRingCat.of (A ⊗[k] R))⟶Y :=
  (pullbackSpecIso k A R).inv≫
    pullback.map (G).hom (Spec.map (CommRingCat.ofHom (algebraMap k R)))
      (G).hom X.hom (𝟙 (G).left) j (𝟙 (Spec (CommRingCat.of k)))
      (by exact (Category.comp_id (G).hom).trans (Category.id_comp (G).hom).symm)
      (by
        have hj := comp_over j (Spec (CommRingCat.of k))
        change j ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k R)) at hj
        exact (Category.comp_id _).trans hj.symm)

@[reassoc] theorem torusProductAffineChart_fst :
    torusProductAffineChart k n X R j≫(fst G X).left=
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] R).toRingHom) := by
  simp only [torusProductAffineChart,Over.fst_left,Category.assoc,pullback.map,
    pullback.lift_fst,Category.comp_id,pullbackSpecIso_inv_fst]
  erw [Category.assoc, pullback.lift_fst]
  exact pullbackSpecIso_inv_fst k A R

@[reassoc] theorem torusProductAffineChart_snd :
    torusProductAffineChart k n X R j≫(snd G X).left=
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : R →ₐ[k] A ⊗[k] R).toRingHom)≫j := by
  simp only [torusProductAffineChart,Over.snd_left,Category.assoc,pullback.map,
    pullback.lift_snd,pullbackSpecIso_inv_snd_assoc]
  erw [Category.assoc, pullback.lift_snd]
  change (pullbackSpecIso k A R).inv ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A)))
        (Spec.map (CommRingCat.ofHom (algebraMap k R))) ≫ j = _
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun f : Spec (CommRingCat.of (A ⊗[k] R)) ⟶ Spec (CommRingCat.of R) => f ≫ j)
      (pullbackSpecIso_inv_snd k A R))

theorem torusProductAffineChart_isPullback :
    IsPullback (torusProductAffineChart k n X R j)
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : R →ₐ[k] A ⊗[k] R).toRingHom))
      (snd G X).left j := by
  apply IsPullback.of_right (t:=IsPullback.of_hasPullback (G).hom X.hom)
  · have hfst : torusProductAffineChart k n X R j ≫ pullback.fst (G).hom X.hom =
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] R).toRingHom) :=
      torusProductAffineChart_fst k n X R j
    have hj := comp_over j (Spec (CommRingCat.of k))
    change j ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k R)) at hj
    rw [hfst,hj]
    refine IsPullback.of_iso_pullback ⟨?_⟩ (pullbackSpecIso k A R).symm ?_ ?_
    · change Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] R).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k A)) =
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : R →ₐ[k] A ⊗[k] R).toRingHom) ≫
            Spec.map (CommRingCat.ofHom (algebraMap k R))
      rw [← Spec.map_comp,← Spec.map_comp]
      congr 1
      ext c
      simp
    · exact pullbackSpecIso_inv_fst k A R
    · exact pullbackSpecIso_inv_snd k A R
  · exact torusProductAffineChart_snd k n X R j

instance torusProductAffineChart_isOpenImmersion :
    IsOpenImmersion (torusProductAffineChart k n X R j) :=
  MorphismProperty.of_isPullback
    (torusProductAffineChart_isPullback k n X R j).flip inferInstance

theorem torusProductAffineChart_opensRange :
    (torusProductAffineChart k n X R j).opensRange=(snd G X).left ⁻¹ᵁ j.opensRange := by
  apply TopologicalSpace.Opens.ext
  simpa only [Set.preimage_univ,Set.image_univ,Scheme.Hom.coe_opensRange,
    Scheme.Hom.coe_preimage] using
    Scheme.image_preimage_eq_of_isPullback
      (torusProductAffineChart_isPullback k n X R j).flip Set.univ

end Product

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.torusProductAffineChart_isPullback
