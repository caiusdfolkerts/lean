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
cert_test_5 3200
cert_test_block_2 3200 0 0 32 32
cert_test_block_2 3200 1 32 64 32
cert_test_block_2 3200 2 64 96 32
cert_test_block_2 3200 3 96 128 32
cert_test_block_2 3200 4 128 160 32
cert_test_block_2 3200 5 160 192 32
cert_test_block_2 3200 6 192 224 32
cert_test_block_2 3200 7 224 256 32
cert_test_block_2 3200 8 256 288 32
cert_test_block_2 3200 9 288 320 32
cert_test_block_2 3200 10 320 352 32
cert_test_block_2 3200 11 352 384 32
cert_test_block_2 3200 12 384 416 32
cert_test_block_2 3200 13 416 448 32
cert_test_block_2 3200 14 448 480 32
cert_test_block_2 3200 15 480 512 32
cert_test_block_2 3200 16 512 544 32
cert_test_block_2 3200 17 544 576 32
cert_test_block_2 3200 18 576 608 32
cert_test_block_2 3200 19 608 640 32
cert_test_complete 3200
cert_nodeInterval_2 3200 3840
end Papers.RationalityTen.RootedForests.RootedRawForest0066
