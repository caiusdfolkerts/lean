module

public import ToricPower.CellularFiniteInjectiveResolution
public import ToricPower.LinearDerivedHomComparison
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Bounded finite injective models of incidence diagrams

The model property in this file refers to genuine complexes of injective
diagrams with finite-dimensional coefficients and finite degree support.
It is closed under the actual shifts and distinguished triangles of the
derived category. The finite directed grading supplies models of the
single-object complexes through the explicit injective resolution.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated CochainComplex
open CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace ToricPower.Cellular

universe u w
variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]
  [HasDerivedCategory.{w} (C ⥤ ModuleCat.{u} k)]

theorem diagram_finite_of_isZero (F : C ⥤ ModuleCat.{u} k)
    (zero : IsZero F) (c : C) : FiniteDimensional k (F.obj c) := by
  letI : Subsingleton (F.obj c) := ModuleCat.isZero_iff_subsingleton.mp
    (((evaluation C (ModuleCat.{u} k)).obj c).map_isZero zero)
  infer_instance

theorem diagramBiprod_finite (F G : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (F.obj c)]
    [∀ c, FiniteDimensional k (G.obj c)] (c : C) :
    FiniteDimensional k ((F ⊞ G).obj c) := by
  letI := preservesBinaryBiproducts_of_preservesBinaryProducts
    ((evaluation C (ModuleCat.{u} k)).obj c)
  let e := ((evaluation C (ModuleCat.{u} k)).obj c).mapBiprod F G ≪≫
    ModuleCat.biprodIsoProd (F.obj c) (G.obj c)
  exact FiniteDimensional.of_injective e.hom.hom e.toLinearEquiv.injective

/-- A bounded complex of finite-dimensional injective diagrams representing
the indicated object of the actual unbounded derived category. -/
def finiteInjectiveModels : ObjectProperty (DerivedCategory (C ⥤ ModuleCat.{u} k)) :=
  fun X => ∃ (J : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ) (a b : ℤ),
    (∀ q, Injective (J.X q)) ∧
    (∀ q c, FiniteDimensional k ((J.X q).obj c)) ∧
    J.IsStrictlyGE a ∧ J.IsStrictlyLE b ∧ Nonempty (DerivedCategory.Q.obj J ≅ X)

instance : (finiteInjectiveModels k (C := C)).IsClosedUnderIsomorphisms where
  of_iso e h := by
    obtain ⟨J, a, b, hI, hF, hge, hle, ⟨eJ⟩⟩ := h
    exact ⟨J, a, b, hI, hF, hge, hle, ⟨eJ ≪≫ e⟩⟩

instance : (finiteInjectiveModels k (C := C)).ContainsZero where
  exists_zero := by
    refine ⟨DerivedCategory.Q.obj 0,
      DerivedCategory.Q.map_isZero (isZero_zero _), ?_⟩
    refine ⟨0, 0, 0, ?_, ?_, inferInstance, inferInstance, ⟨Iso.refl _⟩⟩
    · intro q
      exact IsZero.injective
        ((HomologicalComplex.eval _ (.up ℤ) q).map_isZero (isZero_zero _))
    · intro q c
      exact diagram_finite_of_isZero k _
        ((HomologicalComplex.eval _ (.up ℤ) q).map_isZero (isZero_zero _)) c

instance : (finiteInjectiveModels k (C := C)).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    { le_shift := by
        intro X hX
        obtain ⟨J, a, b, hI, hF, hge, hle, ⟨e⟩⟩ := hX
        letI := hge
        letI := hle
        rw [ObjectProperty.prop_shift_iff]
        refine ⟨J⟦n⟧, a - n, b - n, ?_, ?_,
          J.isStrictlyGE_shift a n (a - n) (by omega),
          J.isStrictlyLE_shift b n (b - n) (by omega), ?_⟩
        · intro q
          exact hI (q + n)
        · intro q c
          exact hF (q + n) c
        · exact ⟨(DerivedCategory.Q.commShiftIso n).app J ≪≫
            (CategoryTheory.shiftFunctor _ n).mapIso e⟩ }

theorem derived_Q_map_surjective_of_kInjective
    (J K : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ) [K.IsKInjective] :
    Function.Surjective (DerivedCategory.Q.map :
      (J ⟶ K) → (DerivedCategory.Q.obj J ⟶ DerivedCategory.Q.obj K)) := by
  intro f
  obtain ⟨g, hg⟩ := (homotopyDerivedLinearEquivOfKInjective k J K).surjective f
  obtain ⟨g', rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨g', ?_⟩
  convert hg using 1
  change DerivedCategory.Q.map g' =
    ((DerivedCategory.quotientCompQhIso _).inv.app J ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map g')) ≫
        (DerivedCategory.quotientCompQhIso _).hom.app K
  rw [Category.assoc, DerivedCategory.quotientCompQhIso_hom_naturality,
    Iso.inv_hom_id_app_assoc]

instance : (finiteInjectiveModels k (C := C)).IsTriangulatedClosed₃ :=
  ObjectProperty.IsTriangulatedClosed₃.mk' (fun T hT h₁ h₂ => by
    obtain ⟨J, a, b, hIJ, hFJ, hgeJ, hleJ, ⟨eJ⟩⟩ := h₁
    obtain ⟨K, c, d, hIK, hFK, hgeK, hleK, ⟨eK⟩⟩ := h₂
    letI := hgeJ
    letI := hleJ
    letI := hgeK
    letI := hleK
    letI := hIJ
    letI := hIK
    letI := hFJ
    letI := hFK
    letI : K.IsKInjective := CochainComplex.isKInjective_of_injective K c
    obtain ⟨f, hf⟩ := derived_Q_map_surjective_of_kInjective k J K
      (eJ.hom ≫ T.mor₁ ≫ eK.inv)
    let eCone := Triangle.π₃.mapIso
      (isoTriangleOfIso₁₂
        (DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle f)) T
        (DerivedCategory.mappingCone_triangle_distinguished f) hT eJ eK (by
          dsimp
          rw [hf]
          simp))
    refine ⟨mappingCone f, min (a - 1) c, max (b - 1) d, ?_, ?_,
      isStrictlyGE_mappingCone f a c _ (by simp) (by simp), ?_, ⟨eCone⟩⟩
    · intro q
      exact Injective.of_iso
        (HomologicalComplex.homotopyCofiber.XIsoBiprod f q (q + 1) rfl).symm
        inferInstance
    · intro q x
      letI := diagramBiprod_finite k (J.X (q + 1)) (K.X q) x
      let e := (HomologicalComplex.homotopyCofiber.XIsoBiprod f q (q + 1) rfl).app x
      exact FiniteDimensional.of_injective e.hom.hom e.toLinearEquiv.injective
    · rw [CochainComplex.isStrictlyLE_iff]
      intro q hq
      rw [mappingCone.isZero_X_iff]
      exact ⟨J.isZero_of_isStrictlyLE b (q + 1) (by omega),
        K.isZero_of_isStrictlyLE d q (by omega)⟩)

instance : (finiteInjectiveModels k (C := C)).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

section FiniteGrading

variable [Finite C] [∀ c d : C, Finite (c ⟶ d)]
  [∀ c : C, Subsingleton (c ⟶ c)]
variable (grade : C → ℕ)
  (grade_le : ∀ {c d : C} (_ : c ⟶ d), grade c ≤ grade d)
  (eq_of_grade_eq : ∀ {c d : C} (_ : c ⟶ d), grade c = grade d → c = d)
  (N : ℕ) (bound : ∀ c, grade c ≤ N)

include grade grade_le eq_of_grade_eq N bound

theorem single_zero_finiteInjectiveModel (F : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (F.obj c)] :
    finiteInjectiveModels k ((DerivedCategory.singleFunctor _ 0).obj F) := by
  let R := diagramFiniteInjectiveResolution k F
  refine ⟨R.cochainComplex, 0, N, inferInstance, ?_, inferInstance, ?_, ?_⟩
  · intro q c
    by_cases hq : 0 ≤ q
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
      letI : FiniteDimensional k ((R.cocomplex.X n).obj c) :=
        diagramFiniteInjectiveComplex_finite k F n c
      let e := (R.cochainComplexXIso n n rfl).app c
      exact FiniteDimensional.of_injective e.hom.hom e.toLinearEquiv.injective
    · exact diagram_finite_of_isZero k _
        (R.cochainComplex.isZero_of_isStrictlyGE 0 q (by omega)) c
  · rw [CochainComplex.isStrictlyLE_iff]
    intro q hq
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ q by omega)
    exact (diagramFiniteInjectiveComplex_isZero_above k grade grade_le eq_of_grade_eq
      F N n bound (by omega)).of_iso (R.cochainComplexXIso n n rfl)
  · exact ⟨(asIso (DerivedCategory.Q.map R.ι')).symm⟩

theorem single_finiteInjectiveModel (F : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (F.obj c)] (n : ℤ) :
    finiteInjectiveModels k ((DerivedCategory.singleFunctor _ n).obj F) := by
  let P := finiteInjectiveModels k (C := C)
  have h := P.le_shift (-n) _
    (single_zero_finiteInjectiveModel k grade grade_le eq_of_grade_eq N bound F)
  exact P.prop_of_iso
    (((DerivedCategory.singleFunctors _).shiftIso (-n) n 0 (by omega)).app F) h

end FiniteGrading

end ToricPower.Cellular

end
