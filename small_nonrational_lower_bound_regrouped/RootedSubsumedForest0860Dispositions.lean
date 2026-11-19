module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0860Data
public import RawLeafCertificate

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0860
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 1)))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))
 (.branch 12
 (.branch 10
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.branch 11
 (.leaf (RawLeafCertificate.Certificate.quota 2))
 (.leaf (RawLeafCertificate.Certificate.quota 3))))
 (.branch 14
 (.branch 13
 (.leaf (RawLeafCertificate.Certificate.quota 3))
 (.leaf (RawLeafCertificate.Certificate.quota 1)))
 (.branch 15
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.leaf (RawLeafCertificate.Certificate.quota 2))))))
cert_disposition_3
cert_dispositionTest_4 05
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
theorem dispositionTest_complete : Interval dispositionTest 0 17 :=
  (interval_append dispositionTest 0 8 17
  (interval_append dispositionTest 0 4 8
  (interval_append dispositionTest 0 2 4
  (interval_append dispositionTest 0 1 2
  dispositionTest_block_0
  dispositionTest_block_1)
  (interval_append dispositionTest 2 3 4
  dispositionTest_block_2
  dispositionTest_block_3))
  (interval_append dispositionTest 4 6 8
  (interval_append dispositionTest 4 5 6
  dispositionTest_block_4
  dispositionTest_block_5)
  (interval_append dispositionTest 6 7 8
  dispositionTest_block_6
  dispositionTest_block_7)))
  (interval_append dispositionTest 8 12 17
  (interval_append dispositionTest 8 10 12
  (interval_append dispositionTest 8 9 10
  dispositionTest_block_8
  dispositionTest_block_9)
  (interval_append dispositionTest 10 11 12
  dispositionTest_block_10
  dispositionTest_block_11))
  (interval_append dispositionTest 12 14 17
  (interval_append dispositionTest 12 13 14
  dispositionTest_block_12
  dispositionTest_block_13)
  (interval_append dispositionTest 14 15 17
  dispositionTest_block_14
  (interval_append dispositionTest 15 16 17
  dispositionTest_block_15
  dispositionTest_block_16)))))
cert_disposition_checked_4 05
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0860
