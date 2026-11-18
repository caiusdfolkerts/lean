module

public import ToricPower.ArrangementMorseComplexIsoTransport

/-! # Morse vanishing under an actual coefficient functor

All domains and functors remain abstract until the full functor
identity is supplied. This avoids normalizing a geometric presentation
at a chosen coefficient object.
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance 2000] CommRing.toRing
attribute [local instance 2100] Complex.instRing
attribute [local instance 2000] Ring.toAddCommGroup
attribute [local instance 2000] Ring.toSemiring
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (c : UniversalIncidenceObject A) (region : Set (Fin n → ℝ))
  {C D : Type*} [Category* C] [Category* D]

theorem universalLocalMorse_single_acyclic_of_precomposition_complex
    (F : C ⥤ D) (G : D ⥤ UniversalIncidenceObject A ⥤ ModuleCat ℂ)
    (K : C ⥤ UniversalIncidenceObject A ⥤ ModuleCat ℂ) (same : K = F ⋙ G)
    (every : ∀ Y : D, ((universalLocalMorse A ℂ c region).obj
      ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat ℂ) 0).obj
        (G.obj Y))).Acyclic) (X : C) :
    ((universalLocalMorse A ℂ c region).obj
      ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat ℂ) 0).obj
        (K.obj X))).Acyclic := by
  subst K
  exact every (F.obj X)

end ToricPower.IntegralArrangement

end
