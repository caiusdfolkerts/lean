module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0707Data
public import RawLeafCertificate

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0707
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 9
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 13
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 15
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 16
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 17
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 1)))))))
cert_disposition_3
cert_dispositionTest_5 04
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
cert_dispositionTest_block_2 10 11
cert_dispositionTest_block_2 11 12
cert_dispositionTest_block_2 12 13
cert_dispositionTest_block_2 13 14
cert_dispositionTest_block_2 14 15
cert_dispositionTest_block_2 15 16
cert_dispositionTest_block_2 16 17
cert_dispositionTest_block_2 17 18
theorem dispositionTest_complete : Interval dispositionTest 0 18 :=
  (interval_append dispositionTest 0 9 18
  (interval_append dispositionTest 0 4 9
  (interval_append dispositionTest 0 2 4
  (interval_append dispositionTest 0 1 2
  dispositionTest_block_0
  dispositionTest_block_1)
  (interval_append dispositionTest 2 3 4
  dispositionTest_block_2
  dispositionTest_block_3))
  (interval_append dispositionTest 4 6 9
  (interval_append dispositionTest 4 5 6
  dispositionTest_block_4
  dispositionTest_block_5)
  (interval_append dispositionTest 6 7 9
  dispositionTest_block_6
  (interval_append dispositionTest 7 8 9
  dispositionTest_block_7
  dispositionTest_block_8))))
  (interval_append dispositionTest 9 13 18
  (interval_append dispositionTest 9 11 13
  (interval_append dispositionTest 9 10 11
  dispositionTest_block_9
  dispositionTest_block_10)
  (interval_append dispositionTest 11 12 13
  dispositionTest_block_11
  dispositionTest_block_12))
  (interval_append dispositionTest 13 15 18
  (interval_append dispositionTest 13 14 15
  dispositionTest_block_13
  dispositionTest_block_14)
  (interval_append dispositionTest 15 16 18
  dispositionTest_block_15
  (interval_append dispositionTest 16 17 18
  dispositionTest_block_16
  dispositionTest_block_17)))))
cert_disposition_checked_5 04
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0707
