module

public import ToricPower.ArrangementMorseFreeCoefficients

/-! # Transporting the rank-one Morse calculation

This generic comparison keeps evaluation of a large geometric
coefficient functor separate from the homological argument. The supplied
isomorphism is an actual isomorphism of complete incidence diagrams.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [Field k]
  (c : UniversalIncidenceObject A) (region : Set (Fin n → ℝ))

/-- An exact coefficient functor with unrestricted coproducts can be
tested on any specified full diagram isomorphic to its rank-one value. -/
theorem universalLocalMorse_affineModules_acyclic_of_rankOneIso
    (R : Type) [CommRing R]
    (H : ModuleCat.{0} R ⥤ UniversalIncidenceObject A ⥤ ModuleCat k)
    [H.PreservesZeroMorphisms]
    (exact : ∀ S : ShortComplex (ModuleCat.{0} R),
      S.ShortExact → (S.map H).ShortExact)
    (preserves : ∀ I : Type,
      PreservesColimit (Discrete.functor (fun _ : I => ModuleCat.of R R)) H)
    (T : UniversalIncidenceObject A ⥤ ModuleCat k)
    (e : H.obj (ModuleCat.of R R) ≅ T)
    (rankOne : ((universalLocalMorse A k c region).obj
      ((singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat k) 0).obj T)).Acyclic)
    (M : ModuleCat.{0} R) :
    ((universalLocalMorse A k c region).obj
      ((singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat k) 0).obj (H.obj M))).Acyclic := by
  apply universalLocalMorse_affineModules_acyclic_of_rankOne A k c region R H exact preserves
  let comparison := (universalLocalMorse A k c region).mapIso
    ((singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat k) 0).mapIso e)
  intro q
  exact (exactAt_iff_of_quasiIsoAt comparison.hom q).mpr (rankOne q)

end ToricPower.IntegralArrangement

end
