module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0264Data
public import RawLeafCertificate
public import OldTerminalMatches.M005

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0264
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 2
 (.leaf (.quota 2))
 (.branch 3
 (.leaf (.quota 2))
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0344))))
cert_disposition_3
cert_dispositionTest_5 02
cert_disposition_at_5 0
cert_disposition_at_5 1
cert_disposition_at_8 2
cert_disposition_at_6 3 02 005 0344
cert_disposition_interval_4 0 1
cert_disposition_interval_4 1 2
cert_disposition_interval_4 2 3
cert_disposition_interval_4 3 4
theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 2 4 (interval_append dispositionTest 0 1 2 disposition_interval_0 disposition_interval_1) (interval_append dispositionTest 2 3 4 disposition_interval_2 disposition_interval_3))
cert_disposition_checked_5 02
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0264
