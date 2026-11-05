module

public import PaperVerification.ToricRegularRational
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

/-!
# Restriction of actual rational functions to a dense open affine scheme

An open immersion between irreducible schemes identifies their generic
stalks.  The map below is the genuine stalk map of that immersion, with
the generic points identified by Mathlib's generic-point theorem.  Its
compatibility with regular sections is proved from stalk-map naturality.
For an affine source its target is identified with the ordinary fraction
field of the coordinate ring by the universal property of localization.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped nonZeroDivisors

variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    [IrreducibleSpace X] [IrreducibleSpace Y]

/-- Restriction to an open subscheme is an isomorphism of the actual
generic stalks.  No identification of rational functions is assumed. -/
def openImmersionFunctionFieldIso : Y.functionField ≅ X.functionField :=
  Y.presheaf.stalkCongr
      (.of_eq (genericPoint_eq_of_isOpenImmersion j).symm) ≪≫
    asIso (j.stalkMap (genericPoint X))

def openImmersionFunctionFieldEquiv : Y.functionField ≃+* X.functionField :=
  (openImmersionFunctionFieldIso j).commRingCatIsoToRingEquiv

/-- Every nonempty open of the target meets the open source.  This proves
the nonemptiness needed for its ordinary germ-to-function-field map. -/
theorem openImmersion_preimage_nonempty (U : Y.Opens) [Nonempty U] :
    Nonempty (j ⁻¹ᵁ U) := by
  refine ⟨⟨genericPoint X, ?_⟩⟩
  change j (genericPoint X) ∈ U
  rw [genericPoint_eq_of_isOpenImmersion j]
  exact ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr
    (by simpa using (show Nonempty U from inferInstance))

set_option backward.isDefEq.respectTransparency.types false in
/-- The generic-stalk isomorphism sends the germ of a regular section to
the germ of its actual sheaf restriction. -/
theorem openImmersionFunctionFieldIso_germ (U : Y.Opens) [Nonempty U]
    [Nonempty (j ⁻¹ᵁ U)] :
    Y.germToFunctionField U ≫ (openImmersionFunctionFieldIso j).hom =
      j.app U ≫ X.germToFunctionField (j ⁻¹ᵁ U) := by
  simp only [openImmersionFunctionFieldIso, Iso.trans_hom, Scheme.germToFunctionField,
    TopCat.Presheaf.stalkCongr_hom, asIso_hom, ← Category.assoc]
  rw [TopCat.Presheaf.germ_stalkSpecializes]
  exact j.germ_stalkMap U (genericPoint X) _

@[simp] theorem openImmersionFunctionFieldEquiv_germ (U : Y.Opens)
    [Nonempty U] [Nonempty (j ⁻¹ᵁ U)] (a : Γ(Y,U)) :
    openImmersionFunctionFieldEquiv j (Y.germToFunctionField U a) =
      X.germToFunctionField (j ⁻¹ᵁ U) (j.app U a) := by
  exact congrArg (fun f => f a) (openImmersionFunctionFieldIso_germ j U)

set_option backward.isDefEq.respectTransparency.types false in
/-- Compatibility with a composite of actual open immersions. -/
theorem openImmersionFunctionFieldIso_comp {Z : Scheme.{u}}
    [IrreducibleSpace Z] (g : Y ⟶ Z) [IsOpenImmersion g] :
    openImmersionFunctionFieldIso (j ≫ g) =
      openImmersionFunctionFieldIso g ≪≫ openImmersionFunctionFieldIso j := by
  apply Iso.ext
  apply Z.presheaf.stalk_hom_ext
  intro U hU
  letI : Nonempty U := ⟨⟨genericPoint Z,hU⟩⟩
  letI : Nonempty (g ⁻¹ᵁ U) := openImmersion_preimage_nonempty g U
  letI : Nonempty (j ⁻¹ᵁ (g ⁻¹ᵁ U)) :=
    openImmersion_preimage_nonempty j (g ⁻¹ᵁ U)
  letI : Nonempty ((j ≫ g) ⁻¹ᵁ U) := openImmersion_preimage_nonempty (j ≫ g) U
  change Z.germToFunctionField U ≫ (openImmersionFunctionFieldIso (j ≫ g)).hom =
    Z.germToFunctionField U ≫
      ((openImmersionFunctionFieldIso g).hom ≫ (openImmersionFunctionFieldIso j).hom)
  rw [openImmersionFunctionFieldIso_germ (j ≫ g) U, ← Category.assoc,
    openImmersionFunctionFieldIso_germ g U, Category.assoc,
    openImmersionFunctionFieldIso_germ j (g ⁻¹ᵁ U)]
  change (g.app U ≫ j.app (g ⁻¹ᵁ U)) ≫
      X.germToFunctionField (j ⁻¹ᵁ (g ⁻¹ᵁ U)) =
    g.app U ≫ (j.app (g ⁻¹ᵁ U) ≫ X.germToFunctionField (j ⁻¹ᵁ (g ⁻¹ᵁ U)))
  exact Category.assoc _ _ _

theorem openImmersionFunctionFieldEquiv_comp {Z : Scheme.{u}}
    [IrreducibleSpace Z] (g : Y ⟶ Z) [IsOpenImmersion g] :
    openImmersionFunctionFieldEquiv (j ≫ g) =
      (openImmersionFunctionFieldEquiv g).trans (openImmersionFunctionFieldEquiv j) := by
  ext r
  exact congrArg (fun e => e.hom r) (openImmersionFunctionFieldIso_comp j g)

/-- A regular function on a genuine nonempty chart open determines a
rational function on the ambient scheme, via the inverse generic-stalk
isomorphism. -/
def openImmersionRegularToFunctionField (U : X.Opens) [Nonempty U] :
    Γ(X,U) →+* Y.functionField :=
  (openImmersionFunctionFieldEquiv j).symm.toRingHom.comp
    (X.germToFunctionField U).hom

abbrev openImmersionGlobalToFunctionField : Γ(X,⊤) →+* Y.functionField :=
  openImmersionRegularToFunctionField j ⊤

theorem openImmersionRegularToFunctionField_injective [IsIntegral X]
    (U : X.Opens) [Nonempty U] :
    Function.Injective (openImmersionRegularToFunctionField j U) :=
  (openImmersionFunctionFieldEquiv j).symm.injective.comp
    (X.germToFunctionField_injective U)

theorem openImmersionGlobalToFunctionField_injective [IsIntegral X] :
    Function.Injective (openImmersionGlobalToFunctionField j) :=
  openImmersionRegularToFunctionField_injective j ⊤

/-- Changing to a smaller open chart leaves its rational value unchanged. -/
theorem openImmersionGlobalToFunctionField_restrict {Z : Scheme.{u}}
    [IrreducibleSpace Z] (g : Y ⟶ Z) [IsOpenImmersion g] (a : Γ(Y,⊤)) :
    openImmersionGlobalToFunctionField (j ≫ g) (j.appTop a) =
      openImmersionGlobalToFunctionField g a := by
  apply (openImmersionFunctionFieldEquiv (j ≫ g)).injective
  change (openImmersionFunctionFieldEquiv (j ≫ g))
      ((openImmersionFunctionFieldEquiv (j ≫ g)).symm
        (X.germToFunctionField ⊤ (j.appTop a))) =
    (openImmersionFunctionFieldEquiv (j ≫ g))
      ((openImmersionFunctionFieldEquiv g).symm (Y.germToFunctionField ⊤ a))
  rw [RingEquiv.apply_symm_apply, openImmersionFunctionFieldEquiv_comp]
  simp only [RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  letI : Nonempty (j ⁻¹ᵁ (⊤ : Y.Opens)) := openImmersion_preimage_nonempty j ⊤
  exact (openImmersionFunctionFieldEquiv_germ j ⊤ a).symm

theorem openImmersionRegularToFunctionField_restrict
    {U V : X.Opens} [Nonempty U] [Nonempty V] (i : V ⟶ U) (a : Γ(X,U)) :
    openImmersionRegularToFunctionField j V (X.presheaf.map i.op a) =
      openImmersionRegularToFunctionField j U a := by
  change (openImmersionFunctionFieldEquiv j).symm
      (X.germToFunctionField V (X.presheaf.map i.op a)) =
    (openImmersionFunctionFieldEquiv j).symm (X.germToFunctionField U a)
  exact congrArg (openImmersionFunctionFieldEquiv j).symm
    (X.presheaf.germ_res_apply i (genericPoint X) _ a)

theorem openImmersion_image_nonempty (U : X.Opens) [Nonempty U] :
    Nonempty (j ''ᵁ U) := by
  let x : U := Classical.choice (show Nonempty U from inferInstance)
  exact ⟨⟨j x,⟨x.val,x.property,rfl⟩⟩⟩

/-- The inverse field map of a chart section agrees with its ordinary
regular section on the open image, under the open-immersion section iso. -/
theorem openImmersionRegularToFunctionField_eq_germ_image
    (U : X.Opens) [Nonempty U] [Nonempty (j ''ᵁ U)] (a : Γ(X,U)) :
    openImmersionRegularToFunctionField j U a =
      Y.germToFunctionField (j ''ᵁ U) ((j.appIso U).inv a) := by
  letI : Nonempty (j ⁻¹ᵁ (j ''ᵁ U)) :=
    openImmersion_preimage_nonempty j (j ''ᵁ U)
  apply (openImmersionFunctionFieldEquiv j).injective
  change (openImmersionFunctionFieldEquiv j)
      ((openImmersionFunctionFieldEquiv j).symm (X.germToFunctionField U a)) =
    openImmersionFunctionFieldEquiv j
      (Y.germToFunctionField (j ''ᵁ U) ((j.appIso U).inv a))
  rw [RingEquiv.apply_symm_apply, openImmersionFunctionFieldEquiv_germ]
  have h := congrArg (fun f => f a) (j.appIso_inv_app U)
  simp only [ConcreteCategory.comp_apply] at h
  change X.germToFunctionField U a =
    X.germToFunctionField (j ⁻¹ᵁ (j ''ᵁ U))
      (j.app (j ''ᵁ U) ((j.appIso U).inv a))
  rw [h]
  exact (X.presheaf.germ_res_apply
    (eqToHom (Scheme.Hom.preimage_image_eq j U))
    (genericPoint X) (((genericPoint_spec X).mem_open_set_iff
      (j ⁻¹ᵁ (j ''ᵁ U)).isOpen).mpr
        (by simpa using (show Nonempty (j ⁻¹ᵁ (j ''ᵁ U)) from inferInstance))) a).symm

/-- A chart-regular function is regular in the ambient local ring at
every point of that chart.  Both local rings and their field embeddings
are the actual scheme stalk constructions. -/
theorem openImmersionRegularToFunctionField_mem_regularAt
    [IsIntegral Y] (U : X.Opens) [Nonempty U] (a : Γ(X,U))
    (x : X) (hx : x∈U) :
    openImmersionRegularToFunctionField j U a ∈ regularAtSubring Y (j x) := by
  letI : Nonempty (j ''ᵁ U) := openImmersion_image_nonempty j U
  rw [openImmersionRegularToFunctionField_eq_germ_image]
  exact regular_germ_mem_regularAt Y (j ''ᵁ U) ((j.appIso U).inv a)
    (j x) ⟨x,hx,rfl⟩

theorem openImmersionGlobalToFunctionField_mem_regularAt
    [IsIntegral Y] (a : Γ(X,⊤)) (x : X) :
    openImmersionGlobalToFunctionField j a ∈ regularAtSubring Y (j x) :=
  openImmersionRegularToFunctionField_mem_regularAt j ⊤ a x trivial

variable (R : CommRingCat.{u}) [IsDomain R]

/-- The actual generic stalk of `Spec R` is its fraction field, by the
uniqueness of localization at the nonzero divisors. -/
def affineFunctionFieldEquiv : (Spec R).functionField ≃ₐ[R] FractionRing R :=
  IsLocalization.algEquiv R⁰ (Spec R).functionField (FractionRing R)

@[simp] theorem affineFunctionFieldEquiv_algebraMap (r : R) :
    affineFunctionFieldEquiv R (algebraMap R (Spec R).functionField r) =
      algebraMap R (FractionRing R) r :=
  (affineFunctionFieldEquiv R).commutes r

/-- The algebra map used for this localization is precisely the germ of
the corresponding global regular function, not an unrelated embedding. -/
theorem affine_germToFunctionField_top :
    (Spec R).germToFunctionField ⊤ =
      (Scheme.ΓSpecIso R).hom ≫
        CommRingCat.ofHom (algebraMap R (Spec R).functionField) := by
  calc
    (Spec R).germToFunctionField ⊤ =
        (Scheme.ΓSpecIso R).hom ≫ ((Scheme.ΓSpecIso R).inv ≫
          (Spec R).germToFunctionField ⊤) := by simp
    _ = _ := rfl

@[simp] theorem affineFunctionFieldEquiv_germ_top (a : Γ(Spec R,⊤)) :
    affineFunctionFieldEquiv R ((Spec R).germToFunctionField ⊤ a) =
      algebraMap R (FractionRing R) ((Scheme.ΓSpecIso R).hom a) := by
  rw [affine_germToFunctionField_top]
  exact (affineFunctionFieldEquiv R).commutes _

/-- The function field of an irreducible scheme with this actual open
affine chart is the fraction field of its actual coordinate ring. -/
def affineOpenFunctionFieldEquiv (j : Spec R ⟶ Y) [IsOpenImmersion j] :
    Y.functionField ≃+* FractionRing R :=
  (openImmersionFunctionFieldEquiv j).trans
    (affineFunctionFieldEquiv R).toRingEquiv

@[simp] theorem affineOpenFunctionFieldEquiv_germ_top
    (j : Spec R ⟶ Y) [IsOpenImmersion j] (a : Γ(Y,⊤)) :
    affineOpenFunctionFieldEquiv R j (Y.germToFunctionField ⊤ a) =
      algebraMap R (FractionRing R) ((Scheme.ΓSpecIso R).hom (j.appTop a)) := by
  change affineFunctionFieldEquiv R
    (openImmersionFunctionFieldEquiv j (Y.germToFunctionField ⊤ a)) = _
  letI : Nonempty (j ⁻¹ᵁ (⊤ : Y.Opens)) := openImmersion_preimage_nonempty j ⊤
  rw [openImmersionFunctionFieldEquiv_germ]
  exact affineFunctionFieldEquiv_germ_top R (j.appTop a)

/-- Surjectivity is part of the constructed ring equivalence; in
particular every fraction arises from an actual rational function. -/
theorem affineOpenFunctionFieldEquiv_surjective
    (j : Spec R ⟶ Y) [IsOpenImmersion j] :
    Function.Surjective (affineOpenFunctionFieldEquiv R j) :=
  (affineOpenFunctionFieldEquiv R j).surjective

/-- The actual coordinate-ring embedding of an open affine chart into
the ambient function field, through regular sections and generic germs. -/
def affineOpenCoordinateMap (j : Spec R ⟶ Y) [IsOpenImmersion j] :
    R →+* Y.functionField :=
  (openImmersionGlobalToFunctionField j).comp (Scheme.ΓSpecIso R).inv.hom

def affineOpenCoordinateAlgebra (j : Spec R ⟶ Y) [IsOpenImmersion j] :
    Algebra R Y.functionField :=
  (affineOpenCoordinateMap R j).toAlgebra

@[simp] theorem affineOpenFunctionFieldEquiv_coordinateMap
    (j : Spec R ⟶ Y) [IsOpenImmersion j] (r : R) :
    affineOpenFunctionFieldEquiv R j (affineOpenCoordinateMap R j r) =
      algebraMap R (FractionRing R) r := by
  change affineFunctionFieldEquiv R
      ((openImmersionFunctionFieldEquiv j)
        ((openImmersionFunctionFieldEquiv j).symm
          ((Spec R).germToFunctionField ⊤ ((Scheme.ΓSpecIso R).inv r)))) = _
  rw [RingEquiv.apply_symm_apply, affineFunctionFieldEquiv_germ_top]
  simp

/-- The function-field equivalence respects the actual chart coordinate
map, hence is an algebra equivalence for that explicit algebra structure. -/
def affineOpenFunctionFieldAlgEquiv (j : Spec R ⟶ Y) [IsOpenImmersion j] :
    letI := affineOpenCoordinateAlgebra R j
    Y.functionField ≃ₐ[R] FractionRing R := by
  letI := affineOpenCoordinateAlgebra R j
  exact
    { affineOpenFunctionFieldEquiv R j with
      commutes' := affineOpenFunctionFieldEquiv_coordinateMap R j }

/-- The ambient function field is a fraction ring of an actual affine
chart, with precisely the regular-section/generic-stalk coordinate map.
This explicit structure can be used directly in Kähler localization. -/
theorem affineOpenCoordinate_isFractionRing
    (j : Spec R ⟶ Y) [IsOpenImmersion j] :
    letI := affineOpenCoordinateAlgebra R j
    IsFractionRing R Y.functionField := by
  letI := affineOpenCoordinateAlgebra R j
  exact IsLocalization.isLocalization_of_algEquiv R⁰
    (affineOpenFunctionFieldAlgEquiv R j).symm

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.openImmersionFunctionFieldIso
#print axioms PaperVerification.ToricSchemes.openImmersionFunctionFieldIso_germ
#print axioms PaperVerification.ToricSchemes.affineOpenFunctionFieldEquiv
