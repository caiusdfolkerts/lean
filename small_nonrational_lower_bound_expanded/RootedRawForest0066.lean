module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public import RootedSevenPure032GrowthCache
public import IdentityRawMaps
public import RawClosedGrowthClassification
public import RootedRawForest0066Leaves
public import RootedRawForest0066Proof000
public import RootedRawForest0066Proof001
public import RootedRawForest0066Proof002
public import RootedRawForest0066Proof003
public import RootedRawForest0066Proof004
public import RootedRawForest0066Proof005
public import RootedRawForest0066Proof006
public import RootedRawForest0066Proof007

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0066
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 2560 4700 (interval_append nodeTest 0 1280 2560 (interval_append nodeTest 0 640 1280 nodeInterval0 nodeInterval640) (interval_append nodeTest 1280 1920 2560 nodeInterval1280 nodeInterval1920)) (interval_append nodeTest 2560 3840 4700 (interval_append nodeTest 2560 3200 3840 nodeInterval2560 nodeInterval3200) (interval_append nodeTest 3840 4480 4700 nodeInterval3840 nodeInterval4480)))
cert_root_2 4699
cert_nodes_2
cert_boundary_classification_3 032

end Papers.RationalityTen.RootedForests.RootedRawForest0066
