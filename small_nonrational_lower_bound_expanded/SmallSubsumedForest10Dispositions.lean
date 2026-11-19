module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest10Data
public import RawLeafCertificate
public import OldTerminalMatches.M000

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest10
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.quota 2))
 (.leaf (.incidence 6)))
 (.leaf (.incidence 6)))
 (.branch 6
 (.branch 5
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0020))
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0021)))
 (.branch 7
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0022))
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0023)))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (.incidence 4))
 (.leaf (.quota 2)))
 (.leaf (.incidence 4)))
 (.branch 14
 (.branch 13
 (.leaf (.incidence 4))
 (.leaf (.quota 2)))
 (.leaf (.incidence 7)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0024))
 (.leaf (.incidence 7)))
 (.branch 19
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0025))
 (.leaf (.incidence 7))))
 (.branch 22
 (.branch 21
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0026))
 (.leaf (.incidence 7)))
 (.branch 23
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0027))
 (.leaf (.incidence 7)))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf (.incidence 9))
 (.leaf (.matching Nonrational.OldTerminalMatches.M000.r0028)))
 (.leaf (.incidence 3)))
 (.branch 30
 (.branch 29
 (.leaf (.incidence 3))
 (.leaf (.quota 2)))
 (.branch 31
 (.leaf (.incidence 3))
 (.leaf (.quota 2)))))))
cert_disposition_4
def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map RootedSmallCache.rawCells) (dispositionTable.get i)
cert_disposition_at_12 0
cert_disposition_at_12 1
cert_disposition_at_12 2
cert_disposition_at_13 3
cert_disposition_at_11 4 000 0020
cert_disposition_at_11 5 000 0021
cert_disposition_at_11 6 000 0022
cert_disposition_at_10 7 000 0023
cert_disposition_at_12 8
cert_disposition_at_12 9
cert_disposition_at_12 10
cert_disposition_at_12 11
cert_disposition_at_12 12
cert_disposition_at_12 13
cert_disposition_at_12 14
cert_disposition_at_13 15
cert_disposition_at_10 16 000 0024
cert_disposition_at_13 17
cert_disposition_at_10 18 000 0025
cert_disposition_at_13 19
cert_disposition_at_10 20 000 0026
cert_disposition_at_13 21
cert_disposition_at_10 22 000 0027
cert_disposition_at_12 23
cert_disposition_at_13 24
cert_disposition_at_10 25 000 0028
cert_disposition_at_12 26
cert_disposition_at_12 27
cert_disposition_at_12 28
cert_disposition_at_12 29
cert_disposition_at_12 30
cert_disposition_at_12 31
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
cert_disposition_interval_6 25 26
cert_disposition_interval_6 26 27
cert_disposition_interval_6 27 28
cert_disposition_interval_6 28 29
cert_disposition_interval_6 29 30
cert_disposition_interval_6 30 31
cert_disposition_interval_6 31 32
theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 16 32 (interval_append dispositionTest 0 8 16 (interval_append dispositionTest 0 4 8 (interval_append dispositionTest 0 2 4 (interval_append dispositionTest 0 1 2 disposition_interval_0 disposition_interval_1) (interval_append dispositionTest 2 3 4 disposition_interval_2 disposition_interval_3)) (interval_append dispositionTest 4 6 8 (interval_append dispositionTest 4 5 6 disposition_interval_4 disposition_interval_5) (interval_append dispositionTest 6 7 8 disposition_interval_6 disposition_interval_7))) (interval_append dispositionTest 8 12 16 (interval_append dispositionTest 8 10 12 (interval_append dispositionTest 8 9 10 disposition_interval_8 disposition_interval_9) (interval_append dispositionTest 10 11 12 disposition_interval_10 disposition_interval_11)) (interval_append dispositionTest 12 14 16 (interval_append dispositionTest 12 13 14 disposition_interval_12 disposition_interval_13) (interval_append dispositionTest 14 15 16 disposition_interval_14 disposition_interval_15)))) (interval_append dispositionTest 16 24 32 (interval_append dispositionTest 16 20 24 (interval_append dispositionTest 16 18 20 (interval_append dispositionTest 16 17 18 disposition_interval_16 disposition_interval_17) (interval_append dispositionTest 18 19 20 disposition_interval_18 disposition_interval_19)) (interval_append dispositionTest 20 22 24 (interval_append dispositionTest 20 21 22 disposition_interval_20 disposition_interval_21) (interval_append dispositionTest 22 23 24 disposition_interval_22 disposition_interval_23))) (interval_append dispositionTest 24 28 32 (interval_append dispositionTest 24 26 28 (interval_append dispositionTest 24 25 26 disposition_interval_24 disposition_interval_25) (interval_append dispositionTest 26 27 28 disposition_interval_26 disposition_interval_27)) (interval_append dispositionTest 28 30 32 (interval_append dispositionTest 28 29 30 disposition_interval_28 disposition_interval_29) (interval_append dispositionTest 30 31 32 disposition_interval_30 disposition_interval_31)))))
cert_disposition_checked_6
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest10
