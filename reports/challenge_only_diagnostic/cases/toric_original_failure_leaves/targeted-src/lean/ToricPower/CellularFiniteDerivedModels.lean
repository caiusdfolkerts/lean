module

public import ToricPower.CellularFiniteInjectiveModels
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import ToricPower.FiniteDimensionalModuleHomology

/-!
# Finite models from finite cohomology

Every bounded derived incidence diagram with finite-dimensional
cohomology has a bounded finite-dimensional injective complex model.
The induction uses the actual canonical truncation triangles. Finiteness
of their cohomology is proved from the monic and epic maps in the actual
long exact cohomology sequence.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated

namespace ToricPower.Cellular

universe u w
variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]
  [HasDerivedCategory.{w} (C ⥤ ModuleCat.{u} k)]

/-- Finiteness concerns the literal derived homology diagrams in every degree. -/
def pointwiseFiniteDerived (X : DerivedCategory (C ⥤ ModuleCat.{u} k)) : Prop :=
  ∀ (q : ℤ) (c : C),
    FiniteDimensional k (((DerivedCategory.homologyFunctor _ q).obj X).obj c)

theorem pointwiseFiniteDerived_of_iso
    {X Y : DerivedCategory (C ⥤ ModuleCat.{u} k)} (e : X ≅ Y)
    (finite : pointwiseFiniteDerived k X) : pointwiseFiniteDerived k Y := by
  intro q c
  letI := finite q c
  let eH := ((DerivedCategory.homologyFunctor _ q).mapIso e).app c
  exact FiniteDimensional.of_injective eH.inv.hom eH.symm.toLinearEquiv.injective

theorem pointwiseFiniteDerived_Q_of_finite_terms
    (J : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ)
    [∀ q c, FiniteDimensional k ((J.X q).obj c)] :
    pointwiseFiniteDerived k (DerivedCategory.Q.obj J) := by
  intro q c
  let evaluationFunctor := (evaluation C (ModuleCat.{u} k)).obj c
  let S := (J.sc q).map evaluationFunctor
  letI : FiniteDimensional k S.X₂ := by
    change FiniteDimensional k ((J.X q).obj c)
    infer_instance
  letI : FiniteDimensional k S.homology := moduleHomology_finiteDimensional S
  let e := ((DerivedCategory.homologyFunctorFactors _ q).app J).app c ≪≫
    ((J.sc q).mapHomologyIso evaluationFunctor).symm
  exact FiniteDimensional.of_injective e.hom.hom e.toLinearEquiv.injective

theorem finiteInjectiveModel_bounded
    {X : DerivedCategory (C ⥤ ModuleCat.{u} k)} (model : finiteInjectiveModels k X) :
    DerivedCategory.TStructure.t.bounded X := by
  obtain ⟨J, a, b, hI, hF, hge, hle, ⟨e⟩⟩ := model
  letI := hge
  letI := hle
  exact ⟨⟨a, DerivedCategory.TStructure.t.isGE_of_iso e a⟩,
    ⟨b, DerivedCategory.TStructure.t.isLE_of_iso e b⟩⟩

theorem finiteInjectiveModel_finite
    {X : DerivedCategory (C ⥤ ModuleCat.{u} k)} (model : finiteInjectiveModels k X) :
    pointwiseFiniteDerived k X := by
  obtain ⟨J, a, b, hI, hF, hge, hle, ⟨e⟩⟩ := model
  letI := hF
  exact pointwiseFiniteDerived_of_iso k e (pointwiseFiniteDerived_Q_of_finite_terms k J)

theorem pointwiseFiniteDerived_truncLT
    (X : DerivedCategory (C ⥤ ModuleCat.{u} k))
    (finite : pointwiseFiniteDerived k X) (b : ℤ) :
    pointwiseFiniteDerived k ((DerivedCategory.TStructure.t.truncLT b).obj X) := by
  let t := DerivedCategory.TStructure.t (C := C ⥤ ModuleCat.{u} k)
  let T := (t.triangleLTGE b).obj X
  have hT := t.triangleLTGE_distinguished b X
  intro q c
  by_cases hq : q < b
  · have mono : Mono ((DerivedCategory.homologyFunctor _ q).map T.mor₁) :=
      (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
        T hT (q - 1) q (by omega)).mpr
        ((DerivedCategory.isZero_of_isGE T.obj₃ b (q - 1) (by omega)).eq_of_src _ _)
    letI := mono
    letI : FiniteDimensional k
        (((DerivedCategory.homologyFunctor _ q).obj T.obj₂).obj c) := finite q c
    exact FiniteDimensional.of_injective
      (((DerivedCategory.homologyFunctor _ q).map T.mor₁).app c).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  · exact diagram_finite_of_isZero k _
      (DerivedCategory.isZero_of_isLE ((t.truncLT b).obj X) (b - 1) q (by omega)) c

theorem pointwiseFiniteDerived_truncGE
    (X : DerivedCategory (C ⥤ ModuleCat.{u} k))
    (finite : pointwiseFiniteDerived k X) (b : ℤ) :
    pointwiseFiniteDerived k ((DerivedCategory.TStructure.t.truncGE b).obj X) := by
  let t := DerivedCategory.TStructure.t (C := C ⥤ ModuleCat.{u} k)
  let T := (t.triangleLTGE b).obj X
  have hT := t.triangleLTGE_distinguished b X
  intro q c
  by_cases hq : b ≤ q
  · have epi : Epi ((DerivedCategory.homologyFunctor _ q).map T.mor₂) :=
      (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff
        T hT q (q + 1) rfl).mpr
        ((DerivedCategory.isZero_of_isLE T.obj₁ (b - 1) (q + 1) (by omega)).eq_of_tgt _ _)
    letI := epi
    letI : FiniteDimensional k
        (((DerivedCategory.homologyFunctor _ q).obj T.obj₂).obj c) := finite q c
    exact Module.Finite.of_surjective
      (((DerivedCategory.homologyFunctor _ q).map T.mor₂).app c).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  · exact diagram_finite_of_isZero k _
      (DerivedCategory.isZero_of_isGE ((t.truncGE b).obj X) b q (by omega)) c

variable [Finite C] [∀ c d : C, Finite (c ⟶ d)]
  [∀ c : C, Subsingleton (c ⟶ c)]
variable (grade : C → ℕ)
  (grade_le : ∀ {c d : C} (_ : c ⟶ d), grade c ≤ grade d)
  (eq_of_grade_eq : ∀ {c d : C} (_ : c ⟶ d), grade c = grade d → c = d)
  (N : ℕ) (bound : ∀ c, grade c ≤ N)

include grade grade_le eq_of_grade_eq N bound

theorem concentrated_finiteInjectiveModel
    (X : DerivedCategory (C ⥤ ModuleCat.{u} k))
    (finite : pointwiseFiniteDerived k X)
    (n : ℤ) [X.IsGE n] [X.IsLE n] : finiteInjectiveModels k X := by
  obtain ⟨F, ⟨e⟩⟩ := X.exists_iso_singleFunctor_obj_of_isGE_of_isLE n
  let eH := (DerivedCategory.homologyFunctor _ n).mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ n).app F
  letI (c : C) : FiniteDimensional k (F.obj c) := by
    letI := finite n c
    exact FiniteDimensional.of_injective (eH.app c).inv.hom
      (eH.app c).symm.toLinearEquiv.injective
  exact (finiteInjectiveModels k).prop_of_iso e.symm
    (single_finiteInjectiveModel k grade grade_le eq_of_grade_eq N bound F n)

/-- The finite model is constructed; it is not supplied as an extra hypothesis. -/
theorem bounded_finiteInjectiveModel
    (X : DerivedCategory (C ⥤ ModuleCat.{u} k))
    (bounded : DerivedCategory.TStructure.t.bounded X)
    (finite : pointwiseFiniteDerived k X) : finiteInjectiveModels k X := by
  let t := DerivedCategory.TStructure.t (C := C ⥤ ModuleCat.{u} k)
  let P := finiteInjectiveModels k (C := C)
  have interval : ∀ n : ℕ, ∀ (K : DerivedCategory (C ⥤ ModuleCat.{u} k)) (a : ℤ),
      K.IsGE a → K.IsLE (a + n) → pointwiseFiniteDerived k K → P K := by
    intro n
    induction n with
    | zero =>
        intro K a hge hle hfinite
        letI := hge
        letI : K.IsLE a := by simpa using hle
        exact concentrated_finiteInjectiveModel k grade grade_le eq_of_grade_eq
          N bound K hfinite a
    | succ n ih =>
        intro K a hge hle hfinite
        letI := hge
        letI := hle
        let b : ℤ := a + (n + 1 : ℕ)
        have hb : b - 1 = a + n := by dsimp [b]; omega
        have leftLE : ((t.truncLT b).obj K).IsLE (a + n) := by
          have h : ((t.truncLT b).obj K).IsLE (b - 1) := inferInstance
          simpa only [hb] using h
        have left : P ((t.truncLT b).obj K) :=
          ih _ a inferInstance leftLE (pointwiseFiniteDerived_truncLT k K hfinite b)
        have right : P ((t.truncGE b).obj K) := by
          letI : ((t.truncGE b).obj K).IsLE b := by
            change ((t.truncGE b).obj K).IsLE (a + (n + 1 : ℕ))
            infer_instance
          exact concentrated_finiteInjectiveModel k grade grade_le eq_of_grade_eq N bound
            _ (pointwiseFiniteDerived_truncGE k K hfinite b) b
        exact P.ext_of_isTriangulatedClosed₂ _ (t.triangleLTGE_distinguished b K) left right
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := bounded
  letI := ha
  letI := hb
  exact interval (b - a).toNat X a ha
    (t.isLE_of_le X b _ (by omega)) finite

theorem finiteInjectiveModel_iff_bounded_finite
    (X : DerivedCategory (C ⥤ ModuleCat.{u} k)) :
    finiteInjectiveModels k X ↔
      DerivedCategory.TStructure.t.bounded X ∧ pointwiseFiniteDerived k X :=
  ⟨fun h => ⟨finiteInjectiveModel_bounded k h, finiteInjectiveModel_finite k h⟩,
    fun h => bounded_finiteInjectiveModel k grade grade_le eq_of_grade_eq N bound X h.1 h.2⟩

end ToricPower.Cellular

end
