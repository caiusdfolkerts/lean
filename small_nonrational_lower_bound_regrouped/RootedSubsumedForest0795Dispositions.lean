module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0795Data
public import RawLeafCertificate

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0795
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.branch 1
 (.leaf (.incidence 2))
 (.leaf (.quota 2)))
cert_disposition_3
cert_dispositionTest_4 05
cert_disposition_at_5 0
cert_disposition_at_5 1
cert_disposition_interval_4 0 1
cert_disposition_interval_4 1 2
theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 1 2 disposition_interval_0 disposition_interval_1)
cert_disposition_checked_4 05
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0795
