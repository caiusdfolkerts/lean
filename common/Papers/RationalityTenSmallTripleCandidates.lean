module
public import Papers.RationalityTenSmallTripleDefinitions

@[expose] public section

namespace Papers.RationalityTen.SmallTripleCores
attribute [local instance 2000] Finset.decidableDforallFinset
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem seven_candidates_complete : ∀ T : Triple,
    T.card = 3 → T ⊆ neighbors →
    ¬({1, 2} : Triple) ⊆ T → ¬({3, 4} : Triple) ⊆ T →
    ¬({5, 6} : Triple) ⊆ T → T ∈ sevenCandidates := by
  decide +kernel

theorem eight_candidates_complete : ∀ T : Triple,
    T.card = 3 → 0 ∉ T →
    ¬({1, 2} : Triple) ⊆ T → ¬({3, 4} : Triple) ⊆ T →
    ¬({5, 6} : Triple) ⊆ T → T ∈ eightCandidates := by
  decide +kernel

theorem seven_models_exhaustive :
    (sevenCandidates.powersetCard 4).filter goodSeven =
      (Finset.univ : Finset (Fin 2)).image sevenModels := by
  decide +kernel


end Papers.RationalityTen.SmallTripleCores
