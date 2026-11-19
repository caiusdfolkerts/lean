module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0696Data
public import RawLeafCertificate

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0696
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 2
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 8))))
 (.branch 5
 (.leaf (RawLeafCertificate.Certificate.quota 8))
 (.branch 6
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 8)))))
 (.branch 11
 (.branch 9
 (.leaf (RawLeafCertificate.Certificate.quota 8))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))
 (.branch 13
 (.branch 12
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 8)))
 (.branch 14
 (.leaf (RawLeafCertificate.Certificate.quota 8))
 (.leaf (RawLeafCertificate.Certificate.quota 2))))))
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
cert_dispositionTest_block_2 10 11
cert_dispositionTest_block_2 11 12
cert_dispositionTest_block_2 12 13
cert_dispositionTest_block_2 13 14
cert_dispositionTest_block_2 14 15
theorem dispositionTest_complete : Interval dispositionTest 0 15 :=
  (interval_append dispositionTest 0 7 15
  (interval_append dispositionTest 0 3 7
  (interval_append dispositionTest 0 1 3
  dispositionTest_block_0
  (interval_append dispositionTest 1 2 3
  dispositionTest_block_1
  dispositionTest_block_2))
  (interval_append dispositionTest 3 5 7
  (interval_append dispositionTest 3 4 5
  dispositionTest_block_3
  dispositionTest_block_4)
  (interval_append dispositionTest 5 6 7
  dispositionTest_block_5
  dispositionTest_block_6)))
  (interval_append dispositionTest 7 11 15
  (interval_append dispositionTest 7 9 11
  (interval_append dispositionTest 7 8 9
  dispositionTest_block_7
  dispositionTest_block_8)
  (interval_append dispositionTest 9 10 11
  dispositionTest_block_9
  dispositionTest_block_10))
  (interval_append dispositionTest 11 13 15
  (interval_append dispositionTest 11 12 13
  dispositionTest_block_11
  dispositionTest_block_12)
  (interval_append dispositionTest 13 14 15
  dispositionTest_block_13
  dispositionTest_block_14))))
cert_disposition_checked_5 03
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0696
