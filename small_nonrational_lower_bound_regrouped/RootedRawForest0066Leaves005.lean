module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public import RootedRawForest0066Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0066
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def leafTestAt160 (i : Nat) := leafTest (i+160)
cert_leafTestAt_block 160 0 1
cert_leafTestAt_block 160 1 2
theorem leafTestAt160_complete : Interval leafTestAt160 0 2 :=
  (interval_append leafTestAt160 0 1 2
  leafTestAt160_block_0
  leafTestAt160_block_1)
theorem leafInterval160 : Interval leafTest 160 162 := by
  intro i hlo hhi
  have h := leafTestAt160_complete (i-160) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt160, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedRawForest0066
