module
prelude
public import RootedSmallCacheBadChecked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedSmallCache
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness

theorem bad_exact (c : Fin cellCount) :
    badMasks c.val = RawSharedCache.justifiedBad data facts c := by
  have h := of_decide_eq_true (badTest_complete c.val (Nat.zero_le _) c.isLt)
  simpa only [badTest,Fin.ofNat_val_eq_self] using h
def cache := RawSharedCache.cache data facts bad_exact
theorem well_formed (c : Fin cellCount) :
    RawFacetEmbedding.wellFormedCheck (FacetUniverses.Small.cells c) = true :=
  facts.wellFormed c
#print axioms cache

end Papers.RationalityTen.RootedSmallCache
