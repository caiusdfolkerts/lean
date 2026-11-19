module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0182Data
public import RawLeafCertificate
public import OldTerminalMatches.M005

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0182
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.leaf (.matching Nonrational.OldTerminalMatches.M005.r0333))
cert_disposition_3
cert_dispositionTest_3 02
cert_disposition_at_6 0 02 005 0333
cert_disposition_interval_4 0 1
theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := disposition_interval_0
cert_disposition_checked_5 02
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0182
