module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0718Data
public import RawLeafCertificate
public import OldTerminalMatches.M020

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0718
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 5
 (.branch 2
 (.leaf (.quota 2))
 (.branch 3
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1302))
 (.leaf (.quota 2))))
 (.branch 7
 (.branch 6
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M020.r1303)))
 (.branch 8
 (.leaf (.quota 2))
 (.branch 9
 (.leaf (.quota 2))
 (.leaf (.quota 1))))))
cert_disposition_3
cert_dispositionTest_5 03
cert_disposition_at_5 0
cert_disposition_at_8 1
cert_disposition_at_6 2 03 020 1302
cert_disposition_at_5 3
cert_disposition_at_5 4
cert_disposition_at_8 5
cert_disposition_at_6 6 03 020 1303
cert_disposition_at_5 7
cert_disposition_at_5 8
cert_disposition_at_5 9
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
theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 5 10 (interval_append dispositionTest 0 2 5 (interval_append dispositionTest 0 1 2 disposition_interval_0 disposition_interval_1) (interval_append dispositionTest 2 3 5 disposition_interval_2 (interval_append dispositionTest 3 4 5 disposition_interval_3 disposition_interval_4))) (interval_append dispositionTest 5 7 10 (interval_append dispositionTest 5 6 7 disposition_interval_5 disposition_interval_6) (interval_append dispositionTest 7 8 10 disposition_interval_7 (interval_append dispositionTest 8 9 10 disposition_interval_8 disposition_interval_9))))
cert_disposition_checked_5 03
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0718
