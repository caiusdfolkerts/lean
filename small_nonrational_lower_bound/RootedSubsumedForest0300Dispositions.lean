module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0300Data
public import RawLeafCertificate

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0300
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 3
 (.branch 1
 (.leaf (RawLeafCertificate.Certificate.quota 8))
 (.branch 2
 (.leaf (RawLeafCertificate.Certificate.quota 8))
 (.leaf (RawLeafCertificate.Certificate.quota 3))))
 (.leaf (RawLeafCertificate.Certificate.quota 8)))
cert_disposition_3
cert_dispositionTest_5 00
cert_dispositionTest_block_2 0 1
cert_dispositionTest_block_2 1 2
cert_dispositionTest_block_2 2 3
cert_dispositionTest_block_2 3 4
cert_dispositionTest_block_2 4 5
cert_dispositionTest_block_2 5 6
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
cert_disposition_checked_5 00
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0300
