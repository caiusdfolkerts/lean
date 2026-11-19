module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSixExtra05GrowthCache
public import RootedSixExtra05FastWords
public import SubsumedClassification
public import RootedSubsumedForest0864Leaves
public import RootedSubsumedForest0864ProofGrouped000

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0864
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 1920 3294 (interval_append nodeTest 0 640 1920 nodeInterval0 (interval_append nodeTest 640 1280 1920 nodeInterval640 nodeInterval1280)) (interval_append nodeTest 1920 2560 3294 nodeInterval1920 (interval_append nodeTest 2560 3200 3294 nodeInterval2560 nodeInterval3200)))
cert_root_7 3293
cert_nodes_3 288
cert_boundary_classification_4 288 05
#print axioms boundary_classification

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0864
