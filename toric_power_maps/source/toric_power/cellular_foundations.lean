module

public import ToricPower.CategoricalFoundations
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Yoneda

/-!
# Projective representables and unbounded cellular derived detection

This module collects the actual linearized representables, their projectivity,
and detection of arbitrary nonzero objects in the derived category of actual
module diagrams.  The direct construction preserves all higher coherence by
forming complexes before derived localization.

-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

section ProjectiveHomologySource
/-!
# A projective test for nonzero derived homology

A map from a projective object to a homology object lifts through cycles.
The resulting map from a single complex has exactly the prescribed homology
class.  If that class is nonzero, the map remains nonzero after localization
at quasi-isomorphisms.  Neither boundedness nor injectivity is required.

This is a direct construction in Mathlib's actual category of complexes and
its actual derived localization.  It is intended for cellular representable
modules, which are projective in the abelian category of module diagrams.

-/


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe w v u

section Complexes

variable {C : Type u} [Category.{v} C] [Abelian C]
  {I : Type*} [DecidableEq I] {c : ComplexShape I}

/-- Lift a prescribed homology class through the epimorphism from cycles,
then include those cycles into the complex. -/
def projectiveHomologyRepresentative (K : HomologicalComplex C c) (n : I)
    (P : C) [Projective P] (η : P ⟶ K.homology n) :
    ((HomologicalComplex.single C c n).obj P) ⟶ K :=
  HomologicalComplex.mkHomFromSingle
    (Projective.factorThru η (K.homologyπ n) ≫ K.iCycles n)
    (fun j _ => by
      simp only [Category.assoc, HomologicalComplex.iCycles_d, comp_zero])

/-- The chosen representative induces the original homology class, under
the canonical identification of the single complex's homology with `P`. -/
theorem projectiveHomologyRepresentative_homology
    (K : HomologicalComplex C c) (n : I) (P : C) [Projective P]
    (η : P ⟶ K.homology n) :
    (HomologicalComplex.singleObjHomologySelfIso c n P).inv ≫
      HomologicalComplex.homologyMap (projectiveHomologyRepresentative K n P η) n = η := by
  let α := projectiveHomologyRepresentative K n P η
  have hα : α.f n = (HomologicalComplex.singleObjXSelf c n P).hom ≫
      (Projective.factorThru η (K.homologyπ n) ≫ K.iCycles n) := by
    simp only [α, projectiveHomologyRepresentative, HomologicalComplex.mkHomFromSingle_f]
  have hcycles :
      (HomologicalComplex.singleObjCyclesSelfIso c n P).inv ≫
        HomologicalComplex.cyclesMap α n = Projective.factorThru η (K.homologyπ n) := by
    rw [← cancel_mono (K.iCycles n)]
    simp only [Category.assoc, HomologicalComplex.cyclesMap_i, hα,
      HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles_assoc,
      Iso.inv_hom_id_assoc]
  change (HomologicalComplex.singleObjHomologySelfIso c n P).inv ≫
    HomologicalComplex.homologyMap α n = η
  calc
    _ = ((HomologicalComplex.singleObjCyclesSelfIso c n P).inv ≫
        ((HomologicalComplex.single C c n).obj P).homologyπ n) ≫
          HomologicalComplex.homologyMap α n := by
      rw [HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ]
    _ = ((HomologicalComplex.singleObjCyclesSelfIso c n P).inv ≫
        HomologicalComplex.cyclesMap α n) ≫ K.homologyπ n := by
      simp only [Category.assoc, HomologicalComplex.homologyπ_naturality]
    _ = η := by rw [hcycles, Projective.factorThru_comp]

end Complexes

section Derived

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- A nonzero prescribed homology class gives a nonzero map in the genuine
unbounded derived category. -/
theorem projectiveHomologyRepresentative_nonzero_Q
    (K : CochainComplex C ℤ) (n : ℤ) (P : C) [Projective P]
    (η : P ⟶ K.homology n) (hη : η ≠ 0) :
    DerivedCategory.Q.map (projectiveHomologyRepresentative K n P η) ≠ 0 := by
  intro hzero
  have hhomology :
      HomologicalComplex.homologyMap (projectiveHomologyRepresentative K n P η) n = 0 := by
    rw [← cancel_epi ((DerivedCategory.homologyFunctorFactors C n).hom.app
      ((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj P)),
      ← DerivedCategory.homologyFunctorFactors_hom_naturality,
      hzero, Functor.map_zero, zero_comp, comp_zero]
  have h := projectiveHomologyRepresentative_homology K n P η
  rw [hhomology, comp_zero] at h
  exact hη h.symm

end Derived

end ToricPower
end ProjectiveHomologySource

section CellularRepresentableSource
/-!
# The actual representables of cellular module diagrams

For a face category `C`, `representable R s` is the free module on each
actual hom-set `s ⟶ t`.  In a poset this is exactly the diagram with value
`R` on the open star of `s` and zero elsewhere.  Its maps are the literal
postcomposition maps.  The free-module Yoneda equivalence below identifies
morphisms from this diagram with values at `s`, proves projectivity, and
shows that these representables detect zero diagrams.

The category here is the actual abelian functor category.  A subsequent
derived construction must use complexes in this category, so no ordinary
diagram category in a derived category is substituted for derived diagrams.

-/


open CategoryTheory CategoryTheory.Limits Opposite

namespace ToricPower.Cellular

universe u

variable {C : Type u} [Category.{u} C] (R : Type u) [Ring R]

/-- The literal linearization of a covariant representable. -/
def representable (s : C) : C ⥤ ModuleCat.{u} R :=
  coyoneda.obj (op s) ⋙ ModuleCat.free R

@[simp]
theorem representable_map_freeMk (s : C) {t t' : C} (f : t ⟶ t') (g : s ⟶ t) :
    (representable R s).map f (ModuleCat.freeMk g) = ModuleCat.freeMk (g ≫ f) :=
  ModuleCat.free_map_apply (↾fun h : s ⟶ t => h ≫ f) g

/-- A value determines a natural transformation by transport along the
actual incidence morphisms. -/
def fromValue (F : C ⥤ ModuleCat.{u} R) (s : C) (v : F.obj s) :
    representable R s ⟶ F where
  app t := ModuleCat.freeDesc (↾fun g : s ⟶ t => F.map g v)
  naturality {t t'} f := by
    apply ModuleCat.free_hom_ext
    intro g
    change ModuleCat.freeDesc (↾fun h : s ⟶ t' => F.map h v)
      ((representable R s).map f (ModuleCat.freeMk g)) =
      F.map f (ModuleCat.freeDesc (↾fun h : s ⟶ t => F.map h v)
        (ModuleCat.freeMk g))
    rw [representable_map_freeMk, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    change F.map (g ≫ f) v = F.map f (F.map g v)
    rw [CategoryTheory.Functor.map_comp]
    rfl

@[simp]
theorem fromValue_app_freeMk (F : C ⥤ ModuleCat.{u} R) (s t : C)
    (v : F.obj s) (f : s ⟶ t) :
    (fromValue R F s v).app t (ModuleCat.freeMk f) = F.map f v := by
  change ModuleCat.freeDesc (↾fun g : s ⟶ t => F.map g v) (ModuleCat.freeMk f) = _
  rw [ModuleCat.freeDesc_apply]
  rfl

/-- Evaluation at the identity generator. -/
def evaluate (F : C ⥤ ModuleCat.{u} R) (s : C) (φ : representable R s ⟶ F) : F.obj s :=
  φ.app s (ModuleCat.freeMk (𝟙 s))

@[simp]
theorem evaluate_fromValue (F : C ⥤ ModuleCat.{u} R) (s : C) (v : F.obj s) :
    evaluate R F s (fromValue R F s v) = v := by
  change (fromValue R F s v).app s (ModuleCat.freeMk (𝟙 s)) = v
  rw [fromValue_app_freeMk, CategoryTheory.Functor.map_id]
  rfl

@[simp]
theorem fromValue_evaluate (F : C ⥤ ModuleCat.{u} R) (s : C)
    (φ : representable R s ⟶ F) :
    fromValue R F s (evaluate R F s φ) = φ := by
  apply NatTrans.ext
  funext t
  apply ModuleCat.free_hom_ext
  intro g
  have h := ConcreteCategory.congr_hom (φ.naturality g) (ModuleCat.freeMk (𝟙 s))
  simp only [ModuleCat.comp_apply, representable_map_freeMk, Category.id_comp] at h
  exact (fromValue_app_freeMk R F s t (evaluate R F s φ) g).trans h.symm

/-- The exact free-module Yoneda equivalence, with no finiteness assumption
on the coefficient module. -/
def representableHomEquiv (F : C ⥤ ModuleCat.{u} R) (s : C) :
    (representable R s ⟶ F) ≃ F.obj s where
  toFun := evaluate R F s
  invFun := fromValue R F s
  left_inv := fromValue_evaluate R F s
  right_inv := evaluate_fromValue R F s

@[simp]
theorem evaluate_comp {F G : C ⥤ ModuleCat.{u} R} (s : C)
    (φ : representable R s ⟶ F) (η : F ⟶ G) :
    evaluate R G s (φ ≫ η) = η.app s (evaluate R F s φ) := rfl

@[simp]
theorem evaluate_zero (F : C ⥤ ModuleCat.{u} R) (s : C) :
    evaluate R F s 0 = 0 := rfl

/-- Actual cellular representables are projective in the abelian diagram
category: an epimorphism lifts the chosen value at the representing cell. -/
instance representable_projective (s : C) : Projective (representable R s) where
  factors {F G} φ η hη := by
    haveI : Epi (η.app s) := inferInstance
    obtain ⟨v, hv⟩ := (ModuleCat.epi_iff_surjective (η.app s)).mp
      (by infer_instance) (evaluate R G s φ)
    refine ⟨fromValue R F s v, ?_⟩
    apply (representableHomEquiv R G s).injective
    change evaluate R G s (fromValue R F s v ≫ η) = evaluate R G s φ
    simpa only [evaluate_comp, evaluate_fromValue] using hv

/-- All representables together detect zero in the actual diagram category. -/
theorem isZero_iff_representable_maps_zero (F : C ⥤ ModuleCat.{u} R) :
    IsZero F ↔ ∀ s : C, ∀ φ : representable R s ⟶ F, φ = 0 := by
  constructor
  · intro h s φ
    exact h.eq_of_tgt φ 0
  · intro h
    apply (IsZero.iff_id_eq_zero F).2
    apply NatTrans.ext
    funext s
    apply ModuleCat.hom_ext
    ext v
    have hv := congrArg (evaluate R F s) (h s (fromValue R F s v))
    simp only [evaluate_fromValue, evaluate_zero] at hv
    exact hv

end ToricPower.Cellular
end CellularRepresentableSource

section DerivedDetection

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.Cellular

universe w u

variable {C : Type u} [Category.{u} C] (R : Type u) [Ring R]
  [HasDerivedCategory.{w} (C ⥤ ModuleCat.{u} R)]

/-- A nonzero complex of actual cellular module diagrams receives a nonzero
derived map from a representable placed in a single degree. -/
theorem exists_nonzero_derived_representable_map_Q
    (K : CochainComplex (C ⥤ ModuleCat.{u} R) ℤ)
    (hK : ¬ IsZero (DerivedCategory.Q.obj K)) :
    ∃ (s : C) (n : ℤ), ∃ φ :
      (DerivedCategory.singleFunctor (C ⥤ ModuleCat.{u} R) n).obj (representable R s) ⟶
        DerivedCategory.Q.obj K, φ ≠ 0 := by
  obtain ⟨n, hn⟩ := ToricPower.exists_nonzero_homology_of_nonzero_Q K hK
  have hex : ∃ s : C, ∃ η : representable R s ⟶ K.homology n, η ≠ 0 := by
    by_contra! h
    exact hn ((isZero_iff_representable_maps_zero R (K.homology n)).mpr h)
  obtain ⟨s, η, hη⟩ := hex
  exact ⟨s, n, DerivedCategory.Q.map
    (ToricPower.projectiveHomologyRepresentative K n (representable R s) η),
      ToricPower.projectiveHomologyRepresentative_nonzero_Q K n (representable R s) η hη⟩

/-- The same detection theorem for every object of the genuine unbounded
derived category, independent of its chosen complex representative. -/
theorem exists_nonzero_derived_representable_map
    (E : DerivedCategory (C ⥤ ModuleCat.{u} R)) (hE : ¬ IsZero E) :
    ∃ (s : C) (n : ℤ), ∃ φ :
      (DerivedCategory.singleFunctor (C ⥤ ModuleCat.{u} R) n).obj (representable R s) ⟶ E,
      φ ≠ 0 := by
  let K := DerivedCategory.Q.objPreimage E
  let e : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  have hK : ¬ IsZero (DerivedCategory.Q.obj K) := fun h => hE (e.isZero_iff.mp h)
  obtain ⟨s, n, φ, hφ⟩ := exists_nonzero_derived_representable_map_Q R K hK
  refine ⟨s, n, φ ≫ e.hom, ?_⟩
  intro hz
  apply hφ
  rw [← cancel_mono e.hom, zero_comp]
  exact hz

/-- Actual degree-zero representables, with all integer shifts, detect every
nonzero unbounded derived cellular diagram. -/
theorem exists_nonzero_shifted_representable_map
    (E : DerivedCategory (C ⥤ ModuleCat.{u} R)) (hE : ¬ IsZero E) :
    ∃ (s : C) (d : ℤ), ∃ φ :
      ((DerivedCategory.singleFunctor (C ⥤ ModuleCat.{u} R) 0).obj
        (representable R s))⟦d⟧ ⟶ E, φ ≠ 0 := by
  obtain ⟨s, n, φ, hφ⟩ := exists_nonzero_derived_representable_map R E hE
  let e := ((DerivedCategory.singleFunctors (C ⥤ ModuleCat.{u} R)).shiftIso
    (-n) n 0 (by omega)).app (representable R s)
  refine ⟨s, -n, e.hom ≫ φ, ?_⟩
  intro hz
  apply hφ
  rw [← cancel_epi e.hom, comp_zero]
  exact hz

/-- Vanishing of all shifted representable tests is equivalent to vanishing
of the actual derived cellular diagram. -/
theorem isZero_iff_shifted_representable_maps_zero
    (E : DerivedCategory (C ⥤ ModuleCat.{u} R)) :
    IsZero E ↔ ∀ (s : C) (d : ℤ), ∀ φ :
      ((DerivedCategory.singleFunctor (C ⥤ ModuleCat.{u} R) 0).obj
        (representable R s))⟦d⟧ ⟶ E, φ = 0 := by
  constructor
  · intro h s d φ
    exact h.eq_of_tgt φ 0
  · intro h
    by_contra hE
    obtain ⟨s, d, φ, hφ⟩ := exists_nonzero_shifted_representable_map R E hE
    exact hφ (h s d φ)

end ToricPower.Cellular

end DerivedDetection
