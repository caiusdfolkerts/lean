module
public import Papers.RationalityTenSmallTripleCandidates
@[expose] public section
namespace Papers.RationalityTen.SmallTripleCores
attribute [local instance 2000] Finset.decidableDforallFinset
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem eight_models_batch_31 :
    ∀ S ∈ ({{1,5,7},{1,6,7},{2,3,5},{2,3,6},{2,3,7},{2,4,5},{2,4,6},{2,4,7},{2,5,7},{2,6,7},{3,5,7},{3,6,7},{4,5,7},{4,6,7}} : Family).powersetCard 3,
      goodEight (insert {1,3,7} (insert {1,4,5} (S))) → (insert {1,3,7} (insert {1,4,5} (S))) ∈ (Finset.univ : Finset (Fin 8)).image eightModels := by
  decide


end Papers.RationalityTen.SmallTripleCores
