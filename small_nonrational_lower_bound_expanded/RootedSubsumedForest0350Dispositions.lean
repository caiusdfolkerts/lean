module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0350Data
public import RawLeafCertificate
public import OldTerminalMatches.M011

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0350
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0735))
 (.leaf (.quota 2)))
 (.branch 3
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0736))))
 (.branch 6
 (.branch 5
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0737))
 (.leaf (.incidence 0)))
 (.branch 7
 (.leaf (.incidence 5))
 (.leaf (.incidence 4)))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (.incidence 4))
 (.leaf (.incidence 8)))
 (.branch 11
 (.leaf .euler)
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0738))))
 (.branch 14
 (.branch 13
 (.leaf (.matching Nonrational.OldTerminalMatches.M011.r0739))
 (.leaf (.quota 2)))
 (.leaf (.quota 2)))))
cert_disposition_3
cert_dispositionTest_3 01
cert_disposition_at_6 0 01 011 0735
cert_disposition_at_5 1
cert_disposition_at_8 2
cert_disposition_at_9 3 01 011 0736
cert_disposition_at_6 4 01 011 0737
cert_disposition_at_5 5
cert_disposition_at_5 6
cert_disposition_at_5 7
cert_disposition_at_5 8
cert_disposition_at_5 9
cert_disposition_at_8 10
cert_disposition_at_9 11 01 011 0738
cert_disposition_at_6 12 01 011 0739
cert_disposition_at_5 13
cert_disposition_at_5 14
cert_disposition_at_5 15
cert_disposition_at_5 16
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
theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 8 17 (interval_append dispositionTest 0 4 8 (interval_append dispositionTest 0 2 4 (interval_append dispositionTest 0 1 2 disposition_interval_0 disposition_interval_1) (interval_append dispositionTest 2 3 4 disposition_interval_2 disposition_interval_3)) (interval_append dispositionTest 4 6 8 (interval_append dispositionTest 4 5 6 disposition_interval_4 disposition_interval_5) (interval_append dispositionTest 6 7 8 disposition_interval_6 disposition_interval_7))) (interval_append dispositionTest 8 12 17 (interval_append dispositionTest 8 10 12 (interval_append dispositionTest 8 9 10 disposition_interval_8 disposition_interval_9) (interval_append dispositionTest 10 11 12 disposition_interval_10 disposition_interval_11)) (interval_append dispositionTest 12 14 17 (interval_append dispositionTest 12 13 14 disposition_interval_12 disposition_interval_13) (interval_append dispositionTest 14 15 17 disposition_interval_14 (interval_append dispositionTest 15 16 17 disposition_interval_15 disposition_interval_16)))))
cert_disposition_checked_5 01
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0350
