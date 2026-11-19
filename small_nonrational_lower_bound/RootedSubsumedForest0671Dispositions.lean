module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0671Data
public import RawLeafCertificate
public import OldTerminalMatches.M018

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0671
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 3
 (.branch 1
 (.leaf (.incidence 4))
 (.branch 2
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1212))
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1213))))
 (.branch 4
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1214))
 (.branch 5
 (.leaf (.incidence 4))
 (.leaf (.matching Nonrational.OldTerminalMatches.M018.r1215)))))
cert_disposition_3
cert_dispositionTest_5 03
cert_disposition_at_8 0
cert_disposition_at_9 1 03 018 1212
cert_disposition_at_9 2 03 018 1213
cert_disposition_at_6 3 03 018 1214
cert_disposition_at_8 4
cert_disposition_at_6 5 03 018 1215
cert_disposition_interval_4 0 1
cert_disposition_interval_4 1 2
cert_disposition_interval_4 2 3
cert_disposition_interval_4 3 4
cert_disposition_interval_4 4 5
cert_disposition_interval_4 5 6
theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 3 6 (interval_append dispositionTest 0 1 3 disposition_interval_0 (interval_append dispositionTest 1 2 3 disposition_interval_1 disposition_interval_2)) (interval_append dispositionTest 3 4 6 disposition_interval_3 (interval_append dispositionTest 4 5 6 disposition_interval_4 disposition_interval_5)))
cert_disposition_checked_5 03
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0671
