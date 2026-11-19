module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSixBase00GrowthCache
public import RootedSixBase00FastWords
public import SubsumedClassification
public import RootedSubsumedForest0299Leaves
public import RootedSubsumedForest0299ProofGrouped000
public import RootedSubsumedForest0299ProofGrouped001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0299
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 7680 15088 (interval_append nodeTest 0 3840 7680 (interval_append nodeTest 0 1920 3840 (interval_append nodeTest 0 640 1920 nodeInterval0 (interval_append nodeTest 640 1280 1920 nodeInterval640 nodeInterval1280)) (interval_append nodeTest 1920 2560 3840 nodeInterval1920 (interval_append nodeTest 2560 3200 3840 nodeInterval2560 nodeInterval3200))) (interval_append nodeTest 3840 5760 7680 (interval_append nodeTest 3840 4480 5760 nodeInterval3840 (interval_append nodeTest 4480 5120 5760 nodeInterval4480 nodeInterval5120)) (interval_append nodeTest 5760 6400 7680 nodeInterval5760 (interval_append nodeTest 6400 7040 7680 nodeInterval6400 nodeInterval7040)))) (interval_append nodeTest 7680 11520 15088 (interval_append nodeTest 7680 9600 11520 (interval_append nodeTest 7680 8320 9600 nodeInterval7680 (interval_append nodeTest 8320 8960 9600 nodeInterval8320 nodeInterval8960)) (interval_append nodeTest 9600 10240 11520 nodeInterval9600 (interval_append nodeTest 10240 10880 11520 nodeInterval10240 nodeInterval10880))) (interval_append nodeTest 11520 13440 15088 (interval_append nodeTest 11520 12160 13440 nodeInterval11520 (interval_append nodeTest 12160 12800 13440 nodeInterval12160 nodeInterval12800)) (interval_append nodeTest 13440 14080 15088 nodeInterval13440 (interval_append nodeTest 14080 14720 15088 nodeInterval14080 nodeInterval14720)))))
cert_root_7 15087
cert_nodes_3 96
cert_boundary_classification_5 96 00
#print axioms boundary_classification

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0299
