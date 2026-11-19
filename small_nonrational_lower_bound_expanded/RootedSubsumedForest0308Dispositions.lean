module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0308Data
public import RawLeafCertificate

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0308
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

cert_dispositionTable_2 2
cert_disposition_3
cert_dispositionTest_5 00
cert_dispositionTest_block_2 0 1
cert_dispositionTest_block_2 1 2
cert_dispositionTest_block_2 2 3
cert_dispositionTest_block_2 3 4
theorem dispositionTest_complete : Interval dispositionTest 0 4 :=
  (interval_append dispositionTest 0 2 4
  (interval_append dispositionTest 0 1 2
  dispositionTest_block_0
  dispositionTest_block_1)
  (interval_append dispositionTest 2 3 4
  dispositionTest_block_2
  dispositionTest_block_3))
cert_disposition_checked_5 00
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0308
