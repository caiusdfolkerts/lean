module

public import ToricPower.ArrangementMorseNamedCoresolution

/-! # The same single-object Morse predicate in canonical scalar presentations

The comparison is proved while the coefficient diagram is abstract.
It changes no scalar action, coefficient or differential.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ToricPower.IntegralArrangement

section Canonical

attribute [local instance 2000] CommRing.toRing
attribute [local instance 2100] Complex.instRing
attribute [local instance 2000] Ring.toAddCommGroup
attribute [local instance 2000] Ring.toSemiring
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

abbrev canonicalSingleMorseAcyclic {n s : ℕ} (A : Fin s → Fin n → ℤ)
    (c : UniversalIncidenceObject A) (region : Set (Fin n → ℝ))
    (E : UniversalIncidenceObject A ⥤ ModuleCat ℂ) : Prop :=
  ((universalLocalMorse A ℂ c region).obj
    ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat ℂ) 0).obj E)).Acyclic

/-- Seal the presentation change while the coefficient diagram is abstract.
The actual geometric coefficient is substituted only after this proof has
been checked. -/
theorem canonicalSingleMorseAcyclic_of_raw {n s : ℕ} (A : Fin s → Fin n → ℤ)
    (c : UniversalIncidenceObject A) (region : Set (Fin n → ℝ))
    (E : UniversalIncidenceObject A ⥤ ModuleCat ℂ)
    (acyclic : ((universalLocalMorse A ℂ c region).obj
      ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat ℂ) 0).obj E)).Acyclic) :
    canonicalSingleMorseAcyclic A c region E := acyclic

/-- The entire coefficient family is transported before any particular
geometric object is evaluated. -/
theorem canonicalSingleMorseAcyclic_all_of_raw {n s : ℕ} (A : Fin s → Fin n → ℤ)
    (c : UniversalIncidenceObject A) (region : Set (Fin n → ℝ))
    {C : Type*} (family : C → UniversalIncidenceObject A ⥤ ModuleCat ℂ)
    (acyclic : ∀ X : C, ((universalLocalMorse A ℂ c region).obj
      ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat ℂ) 0).obj
        (family X))).Acyclic) :
    ∀ X : C, canonicalSingleMorseAcyclic A c region (family X) :=
  fun X => canonicalSingleMorseAcyclic_of_raw A c region (family X) (acyclic X)

end Canonical

section Standard

attribute [local instance 2000] Abelian.toPreadditive
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

theorem canonicalSingleMorseAcyclic_iff {n s : ℕ} (A : Fin s → Fin n → ℤ)
    (c : UniversalIncidenceObject A) (region : Set (Fin n → ℝ))
    (E : UniversalIncidenceObject A ⥤ ModuleCat ℂ) :
    canonicalSingleMorseAcyclic A c region E ↔
      ((universalLocalMorse A ℂ c region).obj
        ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat ℂ) 0).obj E)).Acyclic :=
  Iff.rfl

theorem canonicalSingleMorseAcyclic_all_iff {n s : ℕ} (A : Fin s → Fin n → ℤ)
    (c : UniversalIncidenceObject A) (region : Set (Fin n → ℝ))
    {C : Type*} (family : C → UniversalIncidenceObject A ⥤ ModuleCat ℂ) :
    (∀ X : C, canonicalSingleMorseAcyclic A c region (family X)) ↔
      ∀ X : C, ((universalLocalMorse A ℂ c region).obj
        ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat ℂ) 0).obj
          (family X))).Acyclic :=
  forall_congr' (fun X => canonicalSingleMorseAcyclic_iff A c region (family X))

end Standard

end ToricPower.IntegralArrangement

end
