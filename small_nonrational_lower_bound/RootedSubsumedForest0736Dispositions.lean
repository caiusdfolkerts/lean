module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0736Data
public import RawLeafCertificate
public import OldTerminalMatches.M024

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0736
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1589))
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1590)))
 (.branch 3
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1591))
 (.branch 4
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1592))
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1593)))))
cert_disposition_3
cert_dispositionTest_3 04
cert_disposition_at_9 0 04 024 1589
cert_disposition_at_9 1 04 024 1590
cert_disposition_at_9 2 04 024 1591
cert_disposition_at_9 3 04 024 1592
cert_disposition_at_6 4 04 024 1593
cert_disposition_interval_4 0 1
cert_disposition_interval_4 1 2
cert_disposition_interval_4 2 3
cert_disposition_interval_4 3 4
cert_disposition_interval_4 4 5
theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 2 5 (interval_append dispositionTest 0 1 2 disposition_interval_0 disposition_interval_1) (interval_append dispositionTest 2 3 5 disposition_interval_2 (interval_append dispositionTest 3 4 5 disposition_interval_3 disposition_interval_4)))
cert_disposition_checked_5 04
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0736
