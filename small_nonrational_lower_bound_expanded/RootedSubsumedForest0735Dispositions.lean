module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0735Data
public import RawLeafCertificate
public import OldTerminalMatches.M024

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0735
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 2
 (.branch 1
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1587)))
 (.branch 3
 (.leaf (.quota 2))
 (.branch 4
 (.leaf (.matching Nonrational.OldTerminalMatches.M024.r1588))
 (.leaf (.quota 2)))))
cert_disposition_3
cert_dispositionTest_5 04
cert_disposition_at_8 0
cert_disposition_at_6 1 04 024 1587
cert_disposition_at_8 2
cert_disposition_at_6 3 04 024 1588
cert_disposition_at_5 4
cert_disposition_interval_4 0 1
cert_disposition_interval_4 1 2
cert_disposition_interval_4 2 3
cert_disposition_interval_4 3 4
cert_disposition_interval_4 4 5
theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 2 5 (interval_append dispositionTest 0 1 2 disposition_interval_0 disposition_interval_1) (interval_append dispositionTest 2 3 5 disposition_interval_2 (interval_append dispositionTest 3 4 5 disposition_interval_3 disposition_interval_4)))
cert_disposition_checked_5 04
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0735
