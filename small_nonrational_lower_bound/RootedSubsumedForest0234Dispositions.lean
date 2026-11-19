module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0234Data
public import RawLeafCertificate
public import OldTerminalMatches.M005

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0234
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 1
 (.leaf (.matching Nonrational.OldTerminalMatches.M005.r0334))
 (.leaf (.quota 2)))
cert_disposition_3
cert_dispositionTest_3 01
cert_disposition_at_6 0 01 005 0334
cert_disposition_at_5 1
cert_disposition_interval_4 0 1
cert_disposition_interval_4 1 2
theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 1 2 disposition_interval_0 disposition_interval_1)
cert_disposition_checked_5 01
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0234
