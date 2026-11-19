module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSixBase01GrowthCache
public import RootedSixBase01FastWords
public import SubsumedClassification
public import RootedSubsumedForest0317Leaves
public import RootedSubsumedForest0317Proof000
public import RootedSubsumedForest0317Proof001
public import RootedSubsumedForest0317Proof002
public import RootedSubsumedForest0317Proof003
public import RootedSubsumedForest0317Proof004
public import RootedSubsumedForest0317Proof005
public import RootedSubsumedForest0317Proof006
public import RootedSubsumedForest0317Proof007
public import RootedSubsumedForest0317Proof008
public import RootedSubsumedForest0317Proof009
public import RootedSubsumedForest0317Proof010
public import RootedSubsumedForest0317Proof011
public import RootedSubsumedForest0317Proof012
public import RootedSubsumedForest0317Proof013
public import RootedSubsumedForest0317Proof014

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 4480 9003 (interval_append nodeTest 0 1920 4480 (interval_append nodeTest 0 640 1920 nodeInterval0 (interval_append nodeTest 640 1280 1920 nodeInterval640 nodeInterval1280)) (interval_append nodeTest 1920 3200 4480 (interval_append nodeTest 1920 2560 3200 nodeInterval1920 nodeInterval2560) (interval_append nodeTest 3200 3840 4480 nodeInterval3200 nodeInterval3840))) (interval_append nodeTest 4480 7040 9003 (interval_append nodeTest 4480 5760 7040 (interval_append nodeTest 4480 5120 5760 nodeInterval4480 nodeInterval5120) (interval_append nodeTest 5760 6400 7040 nodeInterval5760 nodeInterval6400)) (interval_append nodeTest 7040 8320 9003 (interval_append nodeTest 7040 7680 8320 nodeInterval7040 nodeInterval7680) (interval_append nodeTest 8320 8960 9003 nodeInterval8320 nodeInterval8960))))
cert_root_7 9002
cert_nodes_3 48
cert_boundary_classification_5 48 01
#print axioms boundary_classification

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
