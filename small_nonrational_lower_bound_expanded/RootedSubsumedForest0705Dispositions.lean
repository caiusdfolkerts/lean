module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0705Data
public import RawLeafCertificate

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0705
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

cert_dispositionTable_2 2
cert_disposition_3
cert_dispositionTest_5 04
cert_dispositionTest_block_2 0 1
cert_dispositionTest_block_2 1 2
cert_dispositionTest_block_2 2 3
theorem dispositionTest_complete : Interval dispositionTest 0 3 :=
  (interval_append dispositionTest 0 1 3
  dispositionTest_block_0
  (interval_append dispositionTest 1 2 3
  dispositionTest_block_1
  dispositionTest_block_2))
cert_disposition_checked_5 04
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0705
