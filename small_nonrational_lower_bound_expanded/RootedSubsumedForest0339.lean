module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSixBase00GrowthCache
public import RootedSixBase00FastWords
public import SubsumedClassification
public import RootedSubsumedForest0339Leaves
public import RootedSubsumedForest0339ProofGrouped000
public import RootedSubsumedForest0339ProofGrouped001
public import RootedSubsumedForest0339ProofGrouped002

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0339
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 7040 14699 (interval_append nodeTest 0 3200 7040 (interval_append nodeTest 0 1280 3200 (interval_append nodeTest 0 640 1280 nodeInterval0 nodeInterval640) (interval_append nodeTest 1280 1920 3200 nodeInterval1280 (interval_append nodeTest 1920 2560 3200 nodeInterval1920 nodeInterval2560))) (interval_append nodeTest 3200 5120 7040 (interval_append nodeTest 3200 3840 5120 nodeInterval3200 (interval_append nodeTest 3840 4480 5120 nodeInterval3840 nodeInterval4480)) (interval_append nodeTest 5120 5760 7040 nodeInterval5120 (interval_append nodeTest 5760 6400 7040 nodeInterval5760 nodeInterval6400)))) (interval_append nodeTest 7040 10880 14699 (interval_append nodeTest 7040 8960 10880 (interval_append nodeTest 7040 7680 8960 nodeInterval7040 (interval_append nodeTest 7680 8320 8960 nodeInterval7680 nodeInterval8320)) (interval_append nodeTest 8960 9600 10880 nodeInterval8960 (interval_append nodeTest 9600 10240 10880 nodeInterval9600 nodeInterval10240))) (interval_append nodeTest 10880 12800 14699 (interval_append nodeTest 10880 11520 12800 nodeInterval10880 (interval_append nodeTest 11520 12160 12800 nodeInterval11520 nodeInterval12160)) (interval_append nodeTest 12800 13440 14699 nodeInterval12800 (interval_append nodeTest 13440 14080 14699 nodeInterval13440 nodeInterval14080)))))
cert_root_7 14698
cert_nodes_3 96
cert_boundary_classification_5 96 00

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0339
