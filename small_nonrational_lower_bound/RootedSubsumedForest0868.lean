module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSixExtra05GrowthCache
public import RootedSixExtra05FastWords
public import SubsumedClassification
public import RootedSubsumedForest0868Leaves
public import RootedSubsumedForest0868Proof000
public import RootedSubsumedForest0868Proof001
public import RootedSubsumedForest0868Proof002
public import RootedSubsumedForest0868Proof003
public import RootedSubsumedForest0868Proof004
public import RootedSubsumedForest0868Proof005
public import RootedSubsumedForest0868Proof006
public import RootedSubsumedForest0868Proof007
public import RootedSubsumedForest0868Proof008
public import RootedSubsumedForest0868Proof009
public import RootedSubsumedForest0868Proof010
public import RootedSubsumedForest0868Proof011
public import RootedSubsumedForest0868Proof012

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0868
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 3840 8057 (interval_append nodeTest 0 1920 3840 (interval_append nodeTest 0 640 1920 nodeInterval0 (interval_append nodeTest 640 1280 1920 nodeInterval640 nodeInterval1280)) (interval_append nodeTest 1920 2560 3840 nodeInterval1920 (interval_append nodeTest 2560 3200 3840 nodeInterval2560 nodeInterval3200))) (interval_append nodeTest 3840 5760 8057 (interval_append nodeTest 3840 4480 5760 nodeInterval3840 (interval_append nodeTest 4480 5120 5760 nodeInterval4480 nodeInterval5120)) (interval_append nodeTest 5760 7040 8057 (interval_append nodeTest 5760 6400 7040 nodeInterval5760 nodeInterval6400) (interval_append nodeTest 7040 7680 8057 nodeInterval7040 nodeInterval7680))))
cert_root_7 8056
cert_nodes_3 288
cert_boundary_classification_4 288 05
#print axioms boundary_classification

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0868
