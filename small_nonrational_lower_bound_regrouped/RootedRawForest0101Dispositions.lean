module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public import RootedRawForest0101Data
public import RawLeafCertificate

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0101
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

def dispositionTable : Table RawLeafCertificate.Certificate :=
(.leaf (.incidence 0))
cert_disposition_2
cert_dispositionTest_2 067
cert_disposition_at_2 0
cert_disposition_at_2 1
cert_disposition_at_2 2
cert_disposition_at_2 3
cert_disposition_at_2 4
cert_disposition_at_2 5
cert_disposition_interval_2 0 1
cert_disposition_interval_2 1 2
cert_disposition_interval_2 2 3
cert_disposition_interval_2 3 4
cert_disposition_interval_2 4 5
cert_disposition_interval_2 5 6
theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 3 6 (interval_append dispositionTest 0 1 3 disposition_interval_0 (interval_append dispositionTest 1 2 3 disposition_interval_1 disposition_interval_2)) (interval_append dispositionTest 3 4 6 disposition_interval_3 (interval_append dispositionTest 4 5 6 disposition_interval_4 disposition_interval_5)))
cert_disposition_checked_2 067
end Papers.RationalityTen.RootedForests.RootedRawForest0101
