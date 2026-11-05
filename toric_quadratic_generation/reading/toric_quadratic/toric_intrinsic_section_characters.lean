module

public import PaperVerification.ToricNormalizedCartierAction
public import PaperVerification.ToricBaseSectionNaturality
public import PaperVerification.ToricCharacterSubrepresentations
public import PaperVerification.ToricCartierRationalSections

@[expose] public section

/-!
# Laurent values of actual intrinsic toric global sections

The dense open torus and the proved torus Picard trivialization give the
Laurent polynomial of a genuine global section. No fan, affine invariant
cover, character basis, or section-coaction hypothesis enters this map.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u

open AlgebraicGeometry CategoryTheory Opposite
open PaperVerification.ToricCharacters
open scoped PaperVerification.ToricSchemes.BaseSections

namespace PaperVerification.ToricSchemes

variable (k : Type u) [Field k] (n : ℕ)
    (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (CommRingCat.of k))]
    (j : splitTorus k (Fin n→ℤ) ⟶ X) [hj : IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k))]

local instance openTorus_coordinate_isDomain : IsDomain (torusCoordinateRing k n) :=
  torusCoordinateRing_isDomain k n

local instance openTorus_coordinate_isOpenImmersion :
    IsOpenImmersion (show Spec (CommRingCat.of (torusCoordinateRing k n)) ⟶ X from j) := hj

local instance openTorus_coordinate_isOver :
    (show Spec (CommRingCat.of (torusCoordinateRing k n)) ⟶ X from j).IsOver
      (Spec (CommRingCat.of k)) :=
  inferInstanceAs (j.IsOver (Spec (CommRingCat.of k)))

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual coordinate-ring embedding from the dense open torus,
with the base scalars supplied by the actual structural morphism. -/
def openTorusRationalAlgHom : AddMonoidAlgebra k (Fin n→ℤ) →ₐ[k] X.functionField where
  __ := affineOpenCoordinateMap (CommRingCat.of (torusCoordinateRing k n)) j
  commutes' c := by
    change affineOpenCoordinateMap (CommRingCat.of (torusCoordinateRing k n)) j
      (algebraMap k (torusCoordinateRing k n) c) = algebraMap k X.functionField c
    apply (torusOpenFunctionFieldEquiv k n X j).injective
    have hs : (Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).hom
        (j.appTop (BaseSections.scalarMap k X ⊤ c)) =
          algebraMap k (torusCoordinateRing k n) c := by
      calc
        _ = (Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).hom
            (BaseSections.scalarMap k
              (Spec (CommRingCat.of (torusCoordinateRing k n))) ⊤ c) :=
          congrArg (Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).hom
            (BaseSections.scalarMap_top_natural k j c)
        _ = (Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).hom
            ((Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).inv
              (algebraMap k (torusCoordinateRing k n) c)) :=
          congrArg (Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).hom
            (BaseSections.scalarMap_affine_top k (torusCoordinateRing k n) c)
        _ = _ := by simp only [Iso.inv_hom_id_apply]
    calc
      _ = algebraMap (torusCoordinateRing k n) (FractionRing (torusCoordinateRing k n))
          (algebraMap k (torusCoordinateRing k n) c) :=
        affineOpenFunctionFieldEquiv_coordinateMap
          (CommRingCat.of (torusCoordinateRing k n)) j _
      _ = algebraMap (torusCoordinateRing k n) (FractionRing (torusCoordinateRing k n))
          ((Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).hom
            (j.appTop (BaseSections.scalarMap k X ⊤ c))) :=
        congrArg (algebraMap (torusCoordinateRing k n)
          (FractionRing (torusCoordinateRing k n))) hs.symm
      _ = torusOpenFunctionFieldEquiv k n X j
          (X.germToFunctionField ⊤ (BaseSections.scalarMap k X ⊤ c)) :=
        (torusOpenFunctionFieldEquiv_germ_top k n X j
          (BaseSections.scalarMap k X ⊤ c)).symm
      _ = _ := congrArg (torusOpenFunctionFieldEquiv k n X j)
        (BaseSections.germ_scalarMap k ⊤ c)

theorem openTorusRationalAlgHom_injective :
    Function.Injective (openTorusRationalAlgHom k n X j) :=
  (openImmersionGlobalToFunctionField_injective j).comp
    (Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).commRingCatIsoToRingEquiv.symm.injective

@[simp] theorem openTorusRationalAlgHom_value (f : AddMonoidAlgebra k (Fin n→ℤ)) :
    openTorusRationalAlgHom k n X j f =
      openImmersionGlobalToFunctionField j
        ((Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).inv f) := rfl

variable (D : CartierData X)

/-- Restriction of a genuine global section to the actual open torus. -/
def normalizedGlobalTorusRestriction
    (s : Γ((torusNormalizedCartier k n X j D).sheaf,⊤)) :
    Γ((torusNormalizedCartier k n X j D).sheaf.restrict j,⊤) :=
  ((torusNormalizedCartier k n X j D).sheaf.restrictAppIso j ⊤).inv
    ((torusNormalizedCartier k n X j D).sheaf.presheaf.map
      (homOfLE (show j ''ᵁ (⊤ : (splitTorus k (Fin n→ℤ)).Opens)≤⊤ from le_top)).op s)

theorem normalizedGlobalTorusRestriction_value
    (s : Γ((torusNormalizedCartier k n X j D).sheaf,⊤)) :
    (torusNormalizedCartier k n X j D).alongSectionValue j ⊤
      (normalizedGlobalTorusRestriction k n X j D s) =
      (torusNormalizedCartier k n X j D).globalSectionValue k s := by
  let E := torusNormalizedCartier k n X j D
  letI : Nonempty (j ''ᵁ (⊤ : (splitTorus k (Fin n→ℤ)).Opens)) :=
    openImmersion_image_nonempty j ⊤
  change E.sectionValue (j ''ᵁ ⊤)
    ((E.sheaf.restrictAppIso j ⊤).hom
      ((E.sheaf.restrictAppIso j ⊤).inv
        (E.sheaf.presheaf.map (homOfLE le_top).op s)))=E.sectionValue ⊤ s
  simp only [Iso.inv_hom_id_apply]
  exact E.sectionValue_restrict (homOfLE le_top) s

/-- The explicit Laurent polynomial of the normalized section. -/
def normalizedSectionLaurent
    (s : Γ((torusNormalizedCartier k n X j D).sheaf,⊤)) :
    AddMonoidAlgebra k (Fin n→ℤ) :=
  (Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).hom
    ((torusNormalizedCartierSheafIso k n X j D).hom.app ⊤
      (normalizedGlobalTorusRestriction k n X j D s))

/-- The Laurent polynomial has exactly the original rational value. -/
theorem normalizedSectionLaurent_value
    (s : Γ((torusNormalizedCartier k n X j D).sheaf,⊤)) :
    openTorusRationalAlgHom k n X j (normalizedSectionLaurent k n X j D s) =
      (torusNormalizedCartier k n X j D).globalSectionValue k s := by
  calc
    _ = openImmersionRegularToFunctionField j ⊤
        ((torusNormalizedCartierSheafIso k n X j D).hom.app ⊤
          (normalizedGlobalTorusRestriction k n X j D s)) := by
      exact congrArg (openImmersionGlobalToFunctionField j)
        (Iso.hom_inv_id_apply
          (Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))) _)
    _ = (torusNormalizedCartier k n X j D).alongSectionValue j ⊤
        (normalizedGlobalTorusRestriction k n X j D s) :=
      (torusNormalizedCartier_value k n X j D ⊤ _).symm
    _ = _ := normalizedGlobalTorusRestriction_value k n X j D s

/-- The Laurent-value map is linear over the true base field, proved
through its actual injective rational-value map. -/
def normalizedSectionLaurentLinear :
    Γ((torusNormalizedCartier k n X j D).sheaf,⊤) →ₗ[k]
      AddMonoidAlgebra k (Fin n→ℤ) where
  toFun := normalizedSectionLaurent k n X j D
  map_add' s t := by
    apply openTorusRationalAlgHom_injective k n X j
    rw [map_add,normalizedSectionLaurent_value,normalizedSectionLaurent_value,
      normalizedSectionLaurent_value,map_add]
  map_smul' c s := by
    apply openTorusRationalAlgHom_injective k n X j
    rw [map_smul,normalizedSectionLaurent_value,normalizedSectionLaurent_value,
      map_smul]
    rfl

theorem normalizedSectionLaurentLinear_injective :
    Function.Injective (normalizedSectionLaurentLinear k n X j D) := by
  intro s t h
  apply (torusNormalizedCartier k n X j D).globalSectionValue_injective k
  rw [← normalizedSectionLaurent_value,← normalizedSectionLaurent_value]
  exact congrArg (openTorusRationalAlgHom k n X j) h

/-- The actual Laurent image of the genuine normalized global-section
space. Coaction stability is proved subsequently, not built into it. -/
def normalizedGlobalCharacters : Submodule k (AddMonoidAlgebra k (Fin n→ℤ)) :=
  (normalizedSectionLaurentLinear k n X j D).range

theorem mem_normalizedGlobalCharacters_iff (f : AddMonoidAlgebra k (Fin n→ℤ)) :
    f∈normalizedGlobalCharacters k n X j D ↔
      openTorusRationalAlgHom k n X j f∈
        ((torusNormalizedCartier k n X j D).globalSectionValue k).range := by
  constructor
  · rintro ⟨s,rfl⟩
    exact ⟨s,(normalizedSectionLaurent_value k n X j D s).symm⟩
  · rintro ⟨s,hs⟩
    refine ⟨s,?_⟩
    apply openTorusRationalAlgHom_injective k n X j
    exact (normalizedSectionLaurent_value k n X j D s).trans hs

def normalizedGlobalSectionCoordinates :
    Γ((torusNormalizedCartier k n X j D).sheaf,⊤) ≃ₗ[k]
      normalizedGlobalCharacters k n X j D :=
  LinearEquiv.ofInjective (normalizedSectionLaurentLinear k n X j D)
    (normalizedSectionLaurentLinear_injective k n X j D)

/-- The literal Laurent part of the actual section image of any Cartier
presentation. No normalization or stability is included in the definition. -/
def torusSectionCharacters (E : CartierData X) :
    Submodule k (AddMonoidAlgebra k (Fin n→ℤ)) :=
  ((E.globalSectionValue k).range).comap (openTorusRationalAlgHom k n X j).toLinearMap

@[simp] theorem mem_torusSectionCharacters (E : CartierData X)
    (f : AddMonoidAlgebra k (Fin n→ℤ)) :
    f∈torusSectionCharacters k n X j E ↔
      openTorusRationalAlgHom k n X j f∈(E.globalSectionValue k).range := Iff.rfl

theorem normalizedGlobalCharacters_eq_torusSectionCharacters :
    normalizedGlobalCharacters k n X j D =
      torusSectionCharacters k n X j (torusNormalizedCartier k n X j D) := by
  ext f
  exact mem_normalizedGlobalCharacters_iff k n X j D f

/-- Actual unit local frames on the torus force every genuine global
section to restrict to a Laurent polynomial. -/
theorem globalSectionValue_in_torusRange_of_unitFrames (E : CartierData X)
    (hE : E.localCocycle.HasUnitFramesOn j.opensRange)
    (z : X.functionField) (hz : z∈(E.globalSectionValue k).range) :
    ∃ f : AddMonoidAlgebra k (Fin n→ℤ),openTorusRationalAlgHom k n X j f=z := by
  let U := j ''ᵁ (⊤ : (splitTorus k (Fin n→ℤ)).Opens)
  letI : Nonempty U := openImmersion_image_nonempty j ⊤
  have hregular : ∀ x∈U,z∈regularAtSubring X x := by
    intro x hx
    obtain ⟨i,hi⟩ := E.localCocycle.covers x
    have hr := (E.mem_sectionValueRange_iff_localStalks ⊤ z).mp hz i x trivial hi
    have hq := hE i x (by simpa only [U,Scheme.Hom.image_top_eq_opensRange] using hx) hi
    have h := (regularAtSubring X x).mul_mem hr hq.1
    simpa only [div_mul_cancel₀ _ (E.localCocycle.generator i).ne_zero] using h
  obtain ⟨a,ha⟩ := exists_regularSection_of_stalkwise X U z hregular
  let f := (Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).hom
    ((j.appIso ⊤).hom a)
  refine ⟨f,?_⟩
  calc
    _ = openImmersionRegularToFunctionField j ⊤ ((j.appIso ⊤).hom a) := by
      exact congrArg (openImmersionGlobalToFunctionField j)
        (Iso.hom_inv_id_apply
          (Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))) _)
    _ = X.germToFunctionField U ((j.appIso ⊤).inv ((j.appIso ⊤).hom a)) :=
      openImmersionRegularToFunctionField_eq_germ_image j ⊤ _
    _ = X.germToFunctionField U a :=
      congrArg (X.germToFunctionField U) (Iso.hom_inv_id_apply (j.appIso ⊤) a)
    _ = z := ha

def torusSectionCharacterValue (E : CartierData X) :
    torusSectionCharacters k n X j E →ₗ[k] X.functionField :=
  (openTorusRationalAlgHom k n X j).toLinearMap.comp
    (torusSectionCharacters k n X j E).subtype

theorem torusSectionCharacterValue_injective (E : CartierData X) :
    Function.Injective (torusSectionCharacterValue k n X j E) :=
  (openTorusRationalAlgHom_injective k n X j).comp Subtype.val_injective

theorem torusSectionCharacterValue_range (E : CartierData X)
    (hE : E.localCocycle.HasUnitFramesOn j.opensRange) :
    (torusSectionCharacterValue k n X j E).range=(E.globalSectionValue k).range := by
  ext z
  constructor
  · rintro ⟨f,rfl⟩
    exact f.property
  · intro hz
    obtain ⟨f,hf⟩ := globalSectionValue_in_torusRange_of_unitFrames k n X j E hE z hz
    refine ⟨⟨f,?_⟩,hf⟩
    change openTorusRationalAlgHom k n X j f∈(E.globalSectionValue k).range
    rwa [hf]

/-- A genuine base-linear coordinate equivalence for every presentation
with proved unit frames on the torus, including actual tensor powers. -/
def torusSectionCoordinates (E : CartierData X)
    (hE : E.localCocycle.HasUnitFramesOn j.opensRange) :
    Γ(E.sheaf,⊤) ≃ₗ[k] torusSectionCharacters k n X j E :=
  (LinearEquiv.ofInjective (E.globalSectionValue k)
    (E.globalSectionValue_injective k)).trans
    ((LinearEquiv.ofEq _ _ (torusSectionCharacterValue_range k n X j E hE).symm).trans
      (LinearEquiv.ofInjective (torusSectionCharacterValue k n X j E)
        (torusSectionCharacterValue_injective k n X j E)).symm)

theorem torusSectionCoordinates_value (E : CartierData X)
    (hE : E.localCocycle.HasUnitFramesOn j.opensRange) (s : Γ(E.sheaf,⊤)) :
    openTorusRationalAlgHom k n X j ((torusSectionCoordinates k n X j E hE s).val)=
      E.globalSectionValue k s := by
  change torusSectionCharacterValue k n X j E (torusSectionCoordinates k n X j E hE s)=_
  simp only [torusSectionCoordinates,LinearEquiv.trans_apply,
    LinearEquiv.ofInjective_symm_apply,LinearEquiv.coe_ofEq_apply,
    LinearEquiv.ofInjective_apply]

end PaperVerification.ToricSchemes
