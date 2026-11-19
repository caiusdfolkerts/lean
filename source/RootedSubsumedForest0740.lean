module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSixBase04GrowthCache
public import RootedSixBase04FastWords
public import SubsumedClassification
public import RootedSubsumedForest0740Leaves
public import RootedSubsumedForest0740ProofGrouped000
public import RootedSubsumedForest0740ProofGrouped001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0740
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 5120 10281 (interval_append nodeTest 0 2560 5120 (interval_append nodeTest 0 1280 2560 (interval_append nodeTest 0 640 1280 nodeInterval0 nodeInterval640) (interval_append nodeTest 1280 1920 2560 nodeInterval1280 nodeInterval1920)) (interval_append nodeTest 2560 3840 5120 (interval_append nodeTest 2560 3200 3840 nodeInterval2560 nodeInterval3200) (interval_append nodeTest 3840 4480 5120 nodeInterval3840 nodeInterval4480))) (interval_append nodeTest 5120 7680 10281 (interval_append nodeTest 5120 6400 7680 (interval_append nodeTest 5120 5760 6400 nodeInterval5120 nodeInterval5760) (interval_append nodeTest 6400 7040 7680 nodeInterval6400 nodeInterval7040)) (interval_append nodeTest 7680 8960 10281 (interval_append nodeTest 7680 8320 8960 nodeInterval7680 nodeInterval8320) (interval_append nodeTest 8960 9600 10281 nodeInterval8960 (interval_append nodeTest 9600 10240 10281 nodeInterval9600 nodeInterval10240)))))
cert_root_7 10280
cert_nodes_3 1152
cert_boundary_classification_5 1152 04
#print axioms boundary_classification

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0740
