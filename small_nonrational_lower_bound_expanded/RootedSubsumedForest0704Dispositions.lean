module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0704Data
public import RawLeafCertificate

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0704
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 5
 (.branch 2
 (.leaf (RawLeafCertificate.Certificate.quota 9))
 (.branch 3
 (.leaf (RawLeafCertificate.Certificate.quota 9))
 (.branch 4
 (.leaf (RawLeafCertificate.Certificate.quota 9))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))
cert_disposition_3
cert_dispositionTest_5 03
cert_dispositionTest_block_2 0 1
cert_dispositionTest_block_2 1 2
cert_dispositionTest_block_2 2 3
cert_dispositionTest_block_2 3 4
cert_dispositionTest_block_2 4 5
cert_dispositionTest_block_2 5 6
cert_dispositionTest_block_2 6 7
cert_dispositionTest_block_2 7 8
cert_dispositionTest_block_2 8 9
cert_dispositionTest_block_2 9 10
theorem dispositionTest_complete : Interval dispositionTest 0 10 :=
  (interval_append dispositionTest 0 5 10
  (interval_append dispositionTest 0 2 5
  (interval_append dispositionTest 0 1 2
  dispositionTest_block_0
  dispositionTest_block_1)
  (interval_append dispositionTest 2 3 5
  dispositionTest_block_2
  (interval_append dispositionTest 3 4 5
  dispositionTest_block_3
  dispositionTest_block_4)))
  (interval_append dispositionTest 5 7 10
  (interval_append dispositionTest 5 6 7
  dispositionTest_block_5
  dispositionTest_block_6)
  (interval_append dispositionTest 7 8 10
  dispositionTest_block_7
  (interval_append dispositionTest 8 9 10
  dispositionTest_block_8
  dispositionTest_block_9))))
cert_disposition_checked_5 03
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0704
