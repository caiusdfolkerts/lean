module
public import Papers.RationalityTenSmallTripleCandidates
@[expose] public section
namespace Papers.RationalityTen.SmallTripleCores
attribute [local instance 2000] Finset.decidableDforallFinset
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def quadRootStar : Family := {{0, 1, 2, 3}, {0, 4, 5}, {0, 6, 7}}
def quadFirstGroup : Finset (Fin 8) := {1, 2, 3}
def quadCandidates : Family := {{1, 4, 6}, {1, 4, 7}, {1, 5, 6}, {1, 5, 7}, {2, 4, 6}, {2, 4, 7}, {2, 5, 6}, {2, 5, 7}, {3, 4, 6}, {3, 4, 7}, {3, 5, 6}, {3, 5, 7}}

def goodQuad (S : Family) : Prop :=
  (∀ v ∈ quadFirstGroup, 2 ≤ degree S v) ∧ pairSeparated S

instance (S : Family) : Decidable (goodQuad S) := by
  unfold goodQuad
  infer_instance

theorem quad_candidates_complete : ∀ T : Triple,
    3 ≤ T.card → T ∉ quadRootStar →
    (∀ R ∈ quadRootStar, (T ∩ R).card ≤ 1) → T ∈ quadCandidates := by
  decide +kernel

theorem quad_models_empty :
    quadCandidates.powerset.filter goodQuad = ∅ := by
  decide +kernel

theorem eight_candidates_from_root : ∀ T : Triple,
    T.card = 3 → T ∉ rootStar →
    (∀ R ∈ rootStar, (T ∩ R).card ≤ 1) → T ∈ eightCandidates := by
  decide +kernel

theorem seven_candidates_from_root : ∀ T : Triple,
    T.card = 3 → 7 ∉ T → T ∉ rootStar →
    (∀ R ∈ rootStar, (T ∩ R).card ≤ 1) → T ∈ sevenCandidates := by
  decide +kernel


end Papers.RationalityTen.SmallTripleCores
