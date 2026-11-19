module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest22Data
public import RawLeafCertificate

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest22
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.leaf (RawLeafCertificate.Certificate.quota 2))
cert_disposition_4
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map RootedSmallCache.rawCells) (dispositionTable.get i)
cert_dispositionTest_block_3 0 1
cert_dispositionTest_block_3 1 2
cert_dispositionTest_block_3 2 3
cert_dispositionTest_block_3 3 4
cert_dispositionTest_block_3 4 5
cert_dispositionTest_block_3 5 6
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
cert_disposition_checked_6
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest22
