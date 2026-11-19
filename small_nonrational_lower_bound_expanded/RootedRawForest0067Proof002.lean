module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public import RootedRawForest0067Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0067
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_5 1280
cert_test_block_2 1280 0 0 32 32
cert_test_block_2 1280 1 32 64 32
cert_test_block_2 1280 2 64 96 32
cert_test_block_2 1280 3 96 128 32
cert_test_block_2 1280 4 128 160 32
cert_test_block_2 1280 5 160 192 32
cert_test_block_2 1280 6 192 224 32
cert_test_block_2 1280 7 224 254 30
cert_test_complete_2 1280 254
cert_nodeInterval_2 1280 1534
end Papers.RationalityTen.RootedForests.RootedRawForest0067
