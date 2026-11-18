module

public import ToricPower.ArrangementMorseRankOneComparison

/-! # Complex-linear coefficient presentation of the rank-one Morse calculation

This generic comparison keeps evaluation of a large geometric
coefficient functor separate from the homological argument. The supplied
isomorphism is an actual isomorphism of complete incidence diagrams.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex

attribute [local instance 2000] CommRing.toRing
attribute [local instance 2100] Complex.instRing
attribute [local instance 2000] Ring.toAddCommGroup
attribute [local instance 2000] Ring.toSemiring
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (c : UniversalIncidenceObject A) (region : Set (Fin n → ℝ))

/-- An exact coefficient functor with unrestricted coproducts can be
tested on any specified full diagram isomorphic to its rank-one value. -/
theorem universalLocalMorse_affineModules_acyclic_of_rankOneIso_complex
    (R : Type) [CommRing R]
    (H : ModuleCat.{0} R ⥤ UniversalIncidenceObject A ⥤ ModuleCat ℂ)
    [H.PreservesZeroMorphisms]
    (exact : ∀ S : ShortComplex (ModuleCat.{0} R),
      S.ShortExact → (S.map H).ShortExact)
    (preserves : ∀ I : Type,
      PreservesColimit (Discrete.functor (fun _ : I => ModuleCat.of R R)) H)
    (T : UniversalIncidenceObject A ⥤ ModuleCat ℂ)
    (e : H.obj (ModuleCat.of R R) ≅ T)
    (rankOne : ((universalLocalMorse A ℂ c region).obj
      ((singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat ℂ) 0).obj T)).Acyclic)
    (M : ModuleCat.{0} R) :
    ((universalLocalMorse A ℂ c region).obj
      ((singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat ℂ) 0).obj (H.obj M))).Acyclic :=
  universalLocalMorse_affineModules_acyclic_of_rankOneIso A ℂ c region R H
    exact preserves T e rankOne M

end ToricPower.IntegralArrangement

end
