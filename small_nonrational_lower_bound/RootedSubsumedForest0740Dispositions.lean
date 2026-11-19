module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0740Data
public import RawLeafCertificate
public import OldTerminalMatches.M024

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0740
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
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1594))))
 (.branch 4
 (.leaf (.quota 2))
 (.branch 5
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1595)))))
 (.branch 9
 (.branch 7
 (.leaf (.quota 2))
 (.branch 8
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1596))
 (.leaf (.quota 2))))
 (.leaf (.quota 2))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf (.quota 1))
 (.branch 14
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1597))
 (.leaf (.quota 1))))
 (.branch 16
 (.leaf (.quota 2))
 (.branch 17
 (.leaf (.quota 2))
 (.leaf (.quota 1)))))
 (.branch 21
 (.branch 19
 (.leaf (.quota 1))
 (.leaf (.quota 2)))
 (.branch 23
 (.branch 22
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1598))
 (.leaf (.quota 2)))
 (.branch 24
 (.leaf (.quota 1))
 (.leaf (.quota 3)))))))
cert_disposition_3
cert_dispositionTest_5 04
cert_disposition_at_5 0
cert_disposition_at_8 1
cert_disposition_at_6 2 04 024 1594
cert_disposition_at_5 3
cert_disposition_at_8 4
cert_disposition_at_6 5 04 024 1595
cert_disposition_at_8 6
cert_disposition_at_6 7 04 024 1596
cert_disposition_at_5 8
cert_disposition_at_5 9
cert_disposition_at_5 10
cert_disposition_at_5 11
cert_disposition_at_8 12
cert_disposition_at_6 13 04 024 1597
cert_disposition_at_5 14
cert_disposition_at_5 15
cert_disposition_at_5 16
cert_disposition_at_5 17
cert_disposition_at_5 18
cert_disposition_at_5 19
cert_disposition_at_8 20
cert_disposition_at_6 21 04 024 1598
cert_disposition_at_5 22
cert_disposition_at_5 23
cert_disposition_at_5 24
cert_disposition_interval_4 0 1
cert_disposition_interval_4 1 2
cert_disposition_interval_4 2 3
cert_disposition_interval_4 3 4
cert_disposition_interval_4 4 5
cert_disposition_interval_4 5 6
cert_disposition_interval_4 6 7
cert_disposition_interval_4 7 8
cert_disposition_interval_4 8 9
cert_disposition_interval_4 9 10
cert_disposition_interval_4 10 11
cert_disposition_interval_4 11 12
cert_disposition_interval_4 12 13
cert_disposition_interval_4 13 14
cert_disposition_interval_4 14 15
cert_disposition_interval_4 15 16
cert_disposition_interval_4 16 17
cert_disposition_interval_4 17 18
cert_disposition_interval_4 18 19
cert_disposition_interval_4 19 20
cert_disposition_interval_4 20 21
cert_disposition_interval_4 21 22
cert_disposition_interval_4 22 23
cert_disposition_interval_4 23 24
cert_disposition_interval_4 24 25
theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 12 25 (interval_append dispositionTest 0 6 12 (interval_append dispositionTest 0 3 6 (interval_append dispositionTest 0 1 3 disposition_interval_0 (interval_append dispositionTest 1 2 3 disposition_interval_1 disposition_interval_2)) (interval_append dispositionTest 3 4 6 disposition_interval_3 (interval_append dispositionTest 4 5 6 disposition_interval_4 disposition_interval_5))) (interval_append dispositionTest 6 9 12 (interval_append dispositionTest 6 7 9 disposition_interval_6 (interval_append dispositionTest 7 8 9 disposition_interval_7 disposition_interval_8)) (interval_append dispositionTest 9 10 12 disposition_interval_9 (interval_append dispositionTest 10 11 12 disposition_interval_10 disposition_interval_11)))) (interval_append dispositionTest 12 18 25 (interval_append dispositionTest 12 15 18 (interval_append dispositionTest 12 13 15 disposition_interval_12 (interval_append dispositionTest 13 14 15 disposition_interval_13 disposition_interval_14)) (interval_append dispositionTest 15 16 18 disposition_interval_15 (interval_append dispositionTest 16 17 18 disposition_interval_16 disposition_interval_17))) (interval_append dispositionTest 18 21 25 (interval_append dispositionTest 18 19 21 disposition_interval_18 (interval_append dispositionTest 19 20 21 disposition_interval_19 disposition_interval_20)) (interval_append dispositionTest 21 23 25 (interval_append dispositionTest 21 22 23 disposition_interval_21 disposition_interval_22) (interval_append dispositionTest 23 24 25 disposition_interval_23 disposition_interval_24)))))
cert_disposition_checked_5 04
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0740
