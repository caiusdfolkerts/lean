module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest08Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest08
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt_2 256
cert_leafTestAt_block_3 256 0 1
theorem leafTestAt256_complete : Interval leafTestAt256 0 1 :=
  leafTestAt256_block_0
cert_leafInterval_2 256 257
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest08
