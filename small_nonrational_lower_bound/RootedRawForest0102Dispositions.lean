module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public import RootedRawForest0102Data
public import RawLeafCertificate

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0102
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

cert_dispositionTable 1
cert_disposition_2
cert_dispositionTest_2 068
cert_dispositionTest_block 0 1
cert_dispositionTest_block 1 2
cert_dispositionTest_block 2 3
cert_dispositionTest_block 3 4
cert_dispositionTest_block 4 5
cert_dispositionTest_block 5 6
theorem dispositionTest_complete : Interval dispositionTest 0 6 :=
  (interval_append dispositionTest 0 3 6
  (interval_append dispositionTest 0 1 3
  dispositionTest_block_0
  (interval_append dispositionTest 1 2 3
  dispositionTest_block_1
  dispositionTest_block_2))
  (interval_append dispositionTest 3 4 6
  dispositionTest_block_3
  (interval_append dispositionTest 4 5 6
  dispositionTest_block_4
  dispositionTest_block_5)))
cert_disposition_checked_2 068
end Papers.RationalityTen.RootedForests.RootedRawForest0102
