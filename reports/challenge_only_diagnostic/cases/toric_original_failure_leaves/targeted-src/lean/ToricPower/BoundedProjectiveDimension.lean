module

public import Mathlib.CategoryTheory.Abelian.Projective.Ext
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# A bounded actual projective resolution bounds projective dimension

The bound is proved using Mathlib's genuine Ext groups: every Ext class
is represented by a cocycle on the chosen projective resolution. Above
the stated bound that resolution term is zero, so its cocycle is zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace ToricPower

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A projective resolution that is zero above degree n gives actual
projective dimension at most n. The supplied complex is an actual
resolution, including its proved quasi-isomorphism to the target. -/
theorem projectiveResolution_hasProjectiveDimensionLE {X : C}
    (resolution : ProjectiveResolution X) (n : ℕ)
    (bounded : ∀ degree, n < degree → IsZero (resolution.complex.X degree)) :
    HasProjectiveDimensionLE X n := by
  letI := HasExt.standard C
  apply HasProjectiveDimensionLT.mk
  intro degree above Y extension
  obtain ⟨cocycle, closed, rfl⟩ :=
    resolution.extMk_surjective extension (degree + 1) rfl
  have zero : cocycle = 0 :=
    (bounded degree (Nat.lt_of_succ_le above)).eq_of_src _ _
  subst cocycle
  exact resolution.extMk_zero (degree + 1) rfl

/-- A resolution of a projective object is already a homotopy equivalence.
Consequently every additive functor preserves its augmentation as a
quasi-isomorphism; the functor need not be exact or preserve projectives. -/
theorem additive_map_projectiveResolution_quasiIso
    {D : Type*} [Category D] [Abelian D] (F : C ⥤ D) [F.Additive]
    {X : C} [Projective X] (resolution : ProjectiveResolution X) :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map resolution.π) := by
  let e := ProjectiveResolution.homotopyEquiv resolution (ProjectiveResolution.self X)
  have augmentation : e.hom = resolution.π :=
    (Category.comp_id e.hom).symm.trans
      (ProjectiveResolution.homotopyEquiv_hom_π resolution (ProjectiveResolution.self X))
  rw [← augmentation]
  exact (F.mapHomotopyEquiv e).quasiIso_hom

/-- Exact functors send an actual projective resolution to a resolution
whenever the particular terms remain projective. No assertion about all
projectives in the source category is required. -/
def mapProjectiveResolutionOfProjectiveTerms
    {D : Type*} [Category D] [Abelian D] (F : C ⥤ D)
    [F.Additive] [F.PreservesHomology] {X : C}
    (resolution : ProjectiveResolution X)
    (projectiveTerms : ∀ degree, Projective (F.obj (resolution.complex.X degree))) :
    ProjectiveResolution (F.obj X) where
  complex := (F.mapHomologicalComplex _).obj resolution.complex
  projective := projectiveTerms
  π := (F.mapHomologicalComplex _).map resolution.π ≫
    (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _
  quasiIso := inferInstance

/-- Once an exact image of a resolution has projective terms and target,
every further additive functor preserves its original augmentation as a
quasi-isomorphism. This is the splitting step of the diagonal argument. -/
theorem additive_map_resolution_of_projective_exact_image
    {D E : Type*} [Category D] [Abelian D] [Category E] [Abelian E]
    (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    (G : D ⥤ E) [G.Additive] {X : C}
    (resolution : ProjectiveResolution X)
    (projectiveTerms : ∀ degree, Projective (F.obj (resolution.complex.X degree)))
    [Projective (F.obj X)] :
    QuasiIso ((G.mapHomologicalComplex (ComplexShape.down ℕ)).map
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map resolution.π)) := by
  let mapped := mapProjectiveResolutionOfProjectiveTerms F resolution projectiveTerms
  have mappedQuasi := additive_map_projectiveResolution_quasiIso G mapped
  change QuasiIso ((G.mapHomologicalComplex (ComplexShape.down ℕ)).map
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map resolution.π ≫
      (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _)) at mappedQuasi
  rw [CategoryTheory.Functor.map_comp] at mappedQuasi
  exact (quasiIso_iff_comp_right _ _).mp mappedQuasi

/-- Naturally isomorphic additive functors have the same
quasi-isomorphism property on each chain map. -/
theorem map_quasiIso_iff_of_natIso
    {D : Type*} [Category D] [Abelian D]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (comparison : F ≅ G)
    {ι : Type*} {shape : ComplexShape ι} {K L : HomologicalComplex C shape}
    (f : K ⟶ L) :
    QuasiIso ((F.mapHomologicalComplex shape).map f) ↔
      QuasiIso ((G.mapHomologicalComplex shape).map f) := by
  let e := NatIso.mapHomologicalComplex comparison shape
  rw [← quasiIso_iff_comp_right _ (e.hom.app L),
    e.hom.naturality, quasiIso_iff_comp_left]


end ToricPower

end
