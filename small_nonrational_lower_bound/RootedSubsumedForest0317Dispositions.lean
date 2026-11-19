module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0317Data
public import RawLeafCertificate

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 6
 (.branch 3
 (.leaf (RawLeafCertificate.Certificate.quota 9))
 (.branch 4
 (.leaf (RawLeafCertificate.Certificate.quota 9))
 (.leaf (RawLeafCertificate.Certificate.quota 3))))
 (.branch 9
 (.branch 7
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.branch 8
 (.leaf (RawLeafCertificate.Certificate.quota 3))
 (.leaf (RawLeafCertificate.Certificate.quota 1))))
 (.branch 10
 (.leaf (RawLeafCertificate.Certificate.quota 1))
 (.leaf (RawLeafCertificate.Certificate.quota 2)))))
cert_disposition_3
cert_dispositionTest_5 01
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
theorem dispositionTest_complete : Interval dispositionTest 0 12 :=
  (interval_append dispositionTest 0 6 12
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
  (interval_append dispositionTest 6 9 12
  (interval_append dispositionTest 6 7 9
  dispositionTest_block_6
  (interval_append dispositionTest 7 8 9
  dispositionTest_block_7
  dispositionTest_block_8))
  (interval_append dispositionTest 9 10 12
  dispositionTest_block_9
  (interval_append dispositionTest 10 11 12
  dispositionTest_block_10
  dispositionTest_block_11))))
cert_disposition_checked_5 01
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
