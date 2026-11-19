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
cert_test_5 2560
cert_test_block_2 2560 0 0 32 32
cert_test_block_2 2560 1 32 64 32
cert_test_block_2 2560 2 64 96 32
cert_test_block_2 2560 3 96 128 32
cert_test_block_2 2560 4 128 160 32
cert_test_block_2 2560 5 160 192 32
cert_test_block_2 2560 6 192 224 32
cert_test_block_2 2560 7 224 256 32
cert_test_block_2 2560 8 256 288 32
cert_test_block_2 2560 9 288 320 32
cert_test_block_2 2560 10 320 352 32
cert_test_block_2 2560 11 352 384 32
cert_test_block_2 2560 12 384 416 32
cert_test_block_2 2560 13 416 448 32
cert_test_block_2 2560 14 448 480 32
cert_test_block_2 2560 15 480 512 32
cert_test_block_2 2560 16 512 544 32
cert_test_block_2 2560 17 544 576 32
cert_test_block_2 2560 18 576 608 32
cert_test_block_2 2560 19 608 640 32
cert_test_complete 2560
cert_nodeInterval_2 2560 3200
end Papers.RationalityTen.RootedForests.RootedRawForest0066
