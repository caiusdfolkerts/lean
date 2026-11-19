module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0301Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0301
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 23040
cert_test_block_3 23040 0 0 16 16
cert_test_block_3 23040 1 16 32 16
cert_test_block_3 23040 2 32 48 16
cert_test_block_3 23040 3 48 52 4
theorem test23040_complete : Interval test23040 0 52 :=
  (interval_append test23040 0 32 52
  (interval_append test23040 0 16 32
  test23040_block_0
  test23040_block_1)
  (interval_append test23040 32 48 52
  test23040_block_2
  test23040_block_3))
cert_nodeInterval_3 23040 23092
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0301
