module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSixBase04GrowthCache
public import RootedSixBase04FastWords
public import SubsumedClassification
public import RootedSubsumedForest0699Leaves
public import RootedSubsumedForest0699ProofGrouped000

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0699
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 1280 2913 (interval_append nodeTest 0 640 1280 nodeInterval0 nodeInterval640) (interval_append nodeTest 1280 1920 2913 nodeInterval1280 (interval_append nodeTest 1920 2560 2913 nodeInterval1920 nodeInterval2560)))
cert_root_7 2912
cert_nodes_3 1152
cert_boundary_classification_5 1152 04
#print axioms boundary_classification

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0699
