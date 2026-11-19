module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSixBase01GrowthCache
public import RootedSixBase01FastWords
public import SubsumedClassification
public import RootedSubsumedForest0302Leaves
public import RootedSubsumedForest0302ProofGrouped000
public import RootedSubsumedForest0302ProofGrouped001
public import RootedSubsumedForest0302ProofGrouped002

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 9600 19838 (interval_append nodeTest 0 4480 9600 (interval_append nodeTest 0 1920 4480 (interval_append nodeTest 0 640 1920 nodeInterval0 (interval_append nodeTest 640 1280 1920 nodeInterval640 nodeInterval1280)) (interval_append nodeTest 1920 3200 4480 (interval_append nodeTest 1920 2560 3200 nodeInterval1920 nodeInterval2560) (interval_append nodeTest 3200 3840 4480 nodeInterval3200 nodeInterval3840))) (interval_append nodeTest 4480 7040 9600 (interval_append nodeTest 4480 5760 7040 (interval_append nodeTest 4480 5120 5760 nodeInterval4480 nodeInterval5120) (interval_append nodeTest 5760 6400 7040 nodeInterval5760 nodeInterval6400)) (interval_append nodeTest 7040 8320 9600 (interval_append nodeTest 7040 7680 8320 nodeInterval7040 nodeInterval7680) (interval_append nodeTest 8320 8960 9600 nodeInterval8320 nodeInterval8960)))) (interval_append nodeTest 9600 14720 19838 (interval_append nodeTest 9600 12160 14720 (interval_append nodeTest 9600 10880 12160 (interval_append nodeTest 9600 10240 10880 nodeInterval9600 nodeInterval10240) (interval_append nodeTest 10880 11520 12160 nodeInterval10880 nodeInterval11520)) (interval_append nodeTest 12160 13440 14720 (interval_append nodeTest 12160 12800 13440 nodeInterval12160 nodeInterval12800) (interval_append nodeTest 13440 14080 14720 nodeInterval13440 nodeInterval14080))) (interval_append nodeTest 14720 17280 19838 (interval_append nodeTest 14720 16000 17280 (interval_append nodeTest 14720 15360 16000 nodeInterval14720 nodeInterval15360) (interval_append nodeTest 16000 16640 17280 nodeInterval16000 nodeInterval16640)) (interval_append nodeTest 17280 18560 19838 (interval_append nodeTest 17280 17920 18560 nodeInterval17280 nodeInterval17920) (interval_append nodeTest 18560 19200 19838 nodeInterval18560 nodeInterval19200)))))
cert_root_7 19837
cert_nodes_3 48
cert_boundary_classification_5 48 01

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
