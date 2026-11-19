module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest21Data
public import RawLeafCertificate
public import OldTerminalMatches.M005

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest21
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (.quota 2))
 (.branch 2
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0326))))
 (.leaf (.quota 2)))
 (.branch 9
 (.branch 7
 (.leaf (.quota 2))
 (.branch 8
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0327))))
 (.branch 10
 (.leaf (.quota 2))
 (.branch 11
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0328))
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0329))))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0330))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))
 (.branch 21
 (.branch 19
 (.leaf (.quota 2))
 (.branch 20
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0331))))
 (.branch 23
 (.branch 22
 (.leaf (.quota 2))
 (.leaf (.quota 1)))
 (.leaf (.quota 2))))))
cert_disposition_4
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map RootedSmallCache.rawCells) (dispositionTable.get i)
cert_disposition_at_12 0
cert_disposition_at_13 1
cert_disposition_at_10 2 005 0326
cert_disposition_at_12 3
cert_disposition_at_12 4
cert_disposition_at_12 5
cert_disposition_at_12 6
cert_disposition_at_13 7
cert_disposition_at_10 8 005 0327
cert_disposition_at_13 9
cert_disposition_at_11 10 005 0328
cert_disposition_at_11 11 005 0329
cert_disposition_at_10 12 005 0330
cert_disposition_at_12 13
cert_disposition_at_12 14
cert_disposition_at_12 15
cert_disposition_at_12 16
cert_disposition_at_12 17
cert_disposition_at_12 18
cert_disposition_at_13 19
cert_disposition_at_10 20 005 0331
cert_disposition_at_12 21
cert_disposition_at_12 22
cert_disposition_at_12 23
cert_disposition_at_12 24
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
cert_disposition_interval_6 10 11
cert_disposition_interval_6 11 12
cert_disposition_interval_6 12 13
cert_disposition_interval_6 13 14
cert_disposition_interval_6 14 15
cert_disposition_interval_6 15 16
cert_disposition_interval_6 16 17
cert_disposition_interval_6 17 18
cert_disposition_interval_6 18 19
cert_disposition_interval_6 19 20
cert_disposition_interval_6 20 21
cert_disposition_interval_6 21 22
cert_disposition_interval_6 22 23
cert_disposition_interval_6 23 24
cert_disposition_interval_6 24 25
theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 12 25 (interval_append dispositionTest 0 6 12 (interval_append dispositionTest 0 3 6 (interval_append dispositionTest 0 1 3 disposition_interval_0 (interval_append dispositionTest 1 2 3 disposition_interval_1 disposition_interval_2)) (interval_append dispositionTest 3 4 6 disposition_interval_3 (interval_append dispositionTest 4 5 6 disposition_interval_4 disposition_interval_5))) (interval_append dispositionTest 6 9 12 (interval_append dispositionTest 6 7 9 disposition_interval_6 (interval_append dispositionTest 7 8 9 disposition_interval_7 disposition_interval_8)) (interval_append dispositionTest 9 10 12 disposition_interval_9 (interval_append dispositionTest 10 11 12 disposition_interval_10 disposition_interval_11)))) (interval_append dispositionTest 12 18 25 (interval_append dispositionTest 12 15 18 (interval_append dispositionTest 12 13 15 disposition_interval_12 (interval_append dispositionTest 13 14 15 disposition_interval_13 disposition_interval_14)) (interval_append dispositionTest 15 16 18 disposition_interval_15 (interval_append dispositionTest 16 17 18 disposition_interval_16 disposition_interval_17))) (interval_append dispositionTest 18 21 25 (interval_append dispositionTest 18 19 21 disposition_interval_18 (interval_append dispositionTest 19 20 21 disposition_interval_19 disposition_interval_20)) (interval_append dispositionTest 21 23 25 (interval_append dispositionTest 21 22 23 disposition_interval_21 disposition_interval_22) (interval_append dispositionTest 23 24 25 disposition_interval_23 disposition_interval_24)))))
cert_disposition_checked_6
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest21
