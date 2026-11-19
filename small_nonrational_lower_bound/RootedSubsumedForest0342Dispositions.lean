module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0342Data
public import RawLeafCertificate

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0342
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.leaf (.incidence 5))
cert_disposition_3
cert_dispositionTest_5 01
cert_disposition_at_5 0
cert_disposition_interval_4 0 1
theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := disposition_interval_0
cert_disposition_checked_5 01
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0342
