module

public import Mathlib.Algebra.Homology.Embedding.HomEquiv
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Additive functors commute with extending a complex by zero

The isomorphism uses the actual extension and restriction constructions in
Mathlib. Outside the image of the embedding, its components identify two
zero objects. Inside the image, they are the functor applied to the
canonical extension isomorphism.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace PaperVerification.DerivedConcentration

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (G : C ⥤ D) [G.Additive] (e : c.Embedding c') [e.IsRelIff]
  (K : HomologicalComplex C c)

/-- The canonical map on the restriction of an extended, mapped complex. -/
def mapExtendedRestriction :
    ((G.mapHomologicalComplex _).obj (K.extend e)).restriction e ⟶
      (G.mapHomologicalComplex _).obj K :=
  (G.mapHomologicalComplex _).map (e.homRestrict (𝟙 (K.extend e)))

lemma mapExtendedRestriction_hasLift : e.HasLift (mapExtendedRestriction G e K) := by
  intro j hj i' hij
  change G.map ((K.extend e).d i' (e.f j)) ≫
    G.map ((e.homRestrict (𝟙 (K.extend e))).f j) = 0
  rw [← G.map_comp, e.homRestrict_hasLift (𝟙 (K.extend e)) j hj i' hij, G.map_zero]

/-- The comparison from mapping an extension to extending the mapped
complex. Its construction is independent of choices of preimages. -/
def mapExtendHom :
    (G.mapHomologicalComplex _).obj (K.extend e) ⟶
      ((G.mapHomologicalComplex _).obj K).extend e :=
  e.liftExtend (mapExtendedRestriction G e K) (mapExtendedRestriction_hasLift G e K)

lemma mapExtendedRestriction_f (i : ι) :
    (mapExtendedRestriction G e K).f i = G.map ((K.extendXIso e (i := i) rfl).hom) := by
  simp only [mapExtendedRestriction, Functor.mapHomologicalComplex_map_f,
    e.homRestrict_f _ rfl, restrictionXIso, eqToIso_refl, Iso.refl_hom,
    HomologicalComplex.id_f, Category.id_comp]

instance mapExtendHom_isIso : IsIso (mapExtendHom G e K) := by
  haveI : ∀ i', IsIso ((mapExtendHom G e K).f i') := by
    intro i'
    by_cases hi' : ∃ i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi'
      change IsIso
        ((e.liftExtend (mapExtendedRestriction G e K)
          (mapExtendedRestriction_hasLift G e K)).f i')
      rw [e.isIso_liftExtend_f_iff _ _ hi, mapExtendedRestriction_f]
      exact (G.mapIso (K.extendXIso e (i := i) rfl)).isIso_hom
    · exact (G.map_isZero (isZero_extend_X K e i' (by simpa using hi'))).isIso
        (isZero_extend_X ((G.mapHomologicalComplex _).obj K) e i'
          (by simpa using hi')) _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- Additive functors commute with extension by zero along any embedding
of complex shapes preserving and reflecting the differential relation. -/
def mapExtendIso :
    (G.mapHomologicalComplex _).obj (K.extend e) ≅
      ((G.mapHomologicalComplex _).obj K).extend e :=
  asIso (mapExtendHom G e K)

end PaperVerification.DerivedConcentration
