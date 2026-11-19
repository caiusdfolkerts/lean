module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSixBase01GrowthCache
public import RootedSixBase01FastWords
public import SubsumedClassification
public import RootedSubsumedForest0309Leaves
public import RootedSubsumedForest0309ProofGrouped000

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0309
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 2560 5577 (interval_append nodeTest 0 1280 2560 (interval_append nodeTest 0 640 1280 nodeInterval0 nodeInterval640) (interval_append nodeTest 1280 1920 2560 nodeInterval1280 nodeInterval1920)) (interval_append nodeTest 2560 3840 5577 (interval_append nodeTest 2560 3200 3840 nodeInterval2560 nodeInterval3200) (interval_append nodeTest 3840 4480 5577 nodeInterval3840 (interval_append nodeTest 4480 5120 5577 nodeInterval4480 nodeInterval5120))))
cert_root_7 5576
cert_nodes_3 48
cert_boundary_classification_5 48 01
#print axioms boundary_classification

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0309
