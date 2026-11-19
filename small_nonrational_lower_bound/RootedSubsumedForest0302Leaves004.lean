module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0302Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 128
cert_leafTestAt_block_2 128 0 1
cert_leafTestAt_block_2 128 1 2
cert_leafTestAt_block_2 128 2 3
cert_leafTestAt_block_2 128 3 4
cert_leafTestAt_block_2 128 4 5
theorem leafTestAt128_complete : Interval leafTestAt128 0 5 :=
  (interval_append leafTestAt128 0 2 5
  (interval_append leafTestAt128 0 1 2
  leafTestAt128_block_0
  leafTestAt128_block_1)
  (interval_append leafTestAt128 2 3 5
  leafTestAt128_block_2
  (interval_append leafTestAt128 3 4 5
  leafTestAt128_block_3
  leafTestAt128_block_4)))
cert_leafInterval 128 133
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
