module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest13Data
public import RawLeafCertificate
public import OldTerminalMatches.M000

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest13
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0029))
 (.leaf (.quota 2)))
 (.branch 3
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0030))
 (.branch 4
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0031))
 (.leaf (.quota 2)))))
 (.leaf (.quota 2)))
cert_disposition_4
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map RootedSmallCache.rawCells) (dispositionTable.get i)

cert_disposition_at_10 0 000 0029
cert_disposition_at_13 1
cert_disposition_at_11 2 000 0030
cert_disposition_at_10 3 000 0031
cert_disposition_at_12 4
cert_disposition_at_12 5
cert_disposition_at_12 6
cert_disposition_at_12 7
cert_disposition_at_12 8
cert_disposition_at_12 9
cert_disposition_interval_6 0 1
cert_disposition_interval_6 1 2
cert_disposition_interval_6 2 3
cert_disposition_interval_6 3 4
cert_disposition_interval_6 4 5
cert_disposition_interval_6 5 6
cert_disposition_interval_6 6 7
cert_disposition_interval_6 7 8
cert_disposition_interval_6 8 9
cert_disposition_interval_6 9 10
theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 5 10 (interval_append dispositionTest 0 2 5 (interval_append dispositionTest 0 1 2 disposition_interval_0 disposition_interval_1) (interval_append dispositionTest 2 3 5 disposition_interval_2 (interval_append dispositionTest 3 4 5 disposition_interval_3 disposition_interval_4))) (interval_append dispositionTest 5 7 10 (interval_append dispositionTest 5 6 7 disposition_interval_5 disposition_interval_6) (interval_append dispositionTest 7 8 10 disposition_interval_7 (interval_append dispositionTest 8 9 10 disposition_interval_8 disposition_interval_9))))
cert_disposition_checked_6
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest13
