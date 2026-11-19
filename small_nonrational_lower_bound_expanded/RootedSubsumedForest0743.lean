module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSixBase04GrowthCache
public import RootedSixBase04FastWords
public import SubsumedClassification
public import RootedSubsumedForest0743Leaves
public import RootedSubsumedForest0743ProofGrouped000
public import RootedSubsumedForest0743ProofGrouped001
public import RootedSubsumedForest0743ProofGrouped002
public import RootedSubsumedForest0743ProofGrouped003
public import RootedSubsumedForest0743ProofGrouped004
public import RootedSubsumedForest0743ProofGrouped005

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 21760 43949 (interval_append nodeTest 0 10880 21760 (interval_append nodeTest 0 5120 10880 (interval_append nodeTest 0 2560 5120 (interval_append nodeTest 0 1280 2560 (interval_append nodeTest 0 640 1280 nodeInterval0 nodeInterval640) (interval_append nodeTest 1280 1920 2560 nodeInterval1280 nodeInterval1920)) (interval_append nodeTest 2560 3840 5120 (interval_append nodeTest 2560 3200 3840 nodeInterval2560 nodeInterval3200) (interval_append nodeTest 3840 4480 5120 nodeInterval3840 nodeInterval4480))) (interval_append nodeTest 5120 7680 10880 (interval_append nodeTest 5120 6400 7680 (interval_append nodeTest 5120 5760 6400 nodeInterval5120 nodeInterval5760) (interval_append nodeTest 6400 7040 7680 nodeInterval6400 nodeInterval7040)) (interval_append nodeTest 7680 8960 10880 (interval_append nodeTest 7680 8320 8960 nodeInterval7680 nodeInterval8320) (interval_append nodeTest 8960 9600 10880 nodeInterval8960 (interval_append nodeTest 9600 10240 10880 nodeInterval9600 nodeInterval10240))))) (interval_append nodeTest 10880 16000 21760 (interval_append nodeTest 10880 13440 16000 (interval_append nodeTest 10880 12160 13440 (interval_append nodeTest 10880 11520 12160 nodeInterval10880 nodeInterval11520) (interval_append nodeTest 12160 12800 13440 nodeInterval12160 nodeInterval12800)) (interval_append nodeTest 13440 14720 16000 (interval_append nodeTest 13440 14080 14720 nodeInterval13440 nodeInterval14080) (interval_append nodeTest 14720 15360 16000 nodeInterval14720 nodeInterval15360))) (interval_append nodeTest 16000 18560 21760 (interval_append nodeTest 16000 17280 18560 (interval_append nodeTest 16000 16640 17280 nodeInterval16000 nodeInterval16640) (interval_append nodeTest 17280 17920 18560 nodeInterval17280 nodeInterval17920)) (interval_append nodeTest 18560 19840 21760 (interval_append nodeTest 18560 19200 19840 nodeInterval18560 nodeInterval19200) (interval_append nodeTest 19840 20480 21760 nodeInterval19840 (interval_append nodeTest 20480 21120 21760 nodeInterval20480 nodeInterval21120)))))) (interval_append nodeTest 21760 32640 43949 (interval_append nodeTest 21760 26880 32640 (interval_append nodeTest 21760 24320 26880 (interval_append nodeTest 21760 23040 24320 (interval_append nodeTest 21760 22400 23040 nodeInterval21760 nodeInterval22400) (interval_append nodeTest 23040 23680 24320 nodeInterval23040 nodeInterval23680)) (interval_append nodeTest 24320 25600 26880 (interval_append nodeTest 24320 24960 25600 nodeInterval24320 nodeInterval24960) (interval_append nodeTest 25600 26240 26880 nodeInterval25600 nodeInterval26240))) (interval_append nodeTest 26880 29440 32640 (interval_append nodeTest 26880 28160 29440 (interval_append nodeTest 26880 27520 28160 nodeInterval26880 nodeInterval27520) (interval_append nodeTest 28160 28800 29440 nodeInterval28160 nodeInterval28800)) (interval_append nodeTest 29440 30720 32640 (interval_append nodeTest 29440 30080 30720 nodeInterval29440 nodeInterval30080) (interval_append nodeTest 30720 31360 32640 nodeInterval30720 (interval_append nodeTest 31360 32000 32640 nodeInterval31360 nodeInterval32000))))) (interval_append nodeTest 32640 38400 43949 (interval_append nodeTest 32640 35200 38400 (interval_append nodeTest 32640 33920 35200 (interval_append nodeTest 32640 33280 33920 nodeInterval32640 nodeInterval33280) (interval_append nodeTest 33920 34560 35200 nodeInterval33920 nodeInterval34560)) (interval_append nodeTest 35200 36480 38400 (interval_append nodeTest 35200 35840 36480 nodeInterval35200 nodeInterval35840) (interval_append nodeTest 36480 37120 38400 nodeInterval36480 (interval_append nodeTest 37120 37760 38400 nodeInterval37120 nodeInterval37760)))) (interval_append nodeTest 38400 40960 43949 (interval_append nodeTest 38400 39680 40960 (interval_append nodeTest 38400 39040 39680 nodeInterval38400 nodeInterval39040) (interval_append nodeTest 39680 40320 40960 nodeInterval39680 nodeInterval40320)) (interval_append nodeTest 40960 42240 43949 (interval_append nodeTest 40960 41600 42240 nodeInterval40960 nodeInterval41600) (interval_append nodeTest 42240 42880 43949 nodeInterval42240 (interval_append nodeTest 42880 43520 43949 nodeInterval42880 nodeInterval43520)))))))
cert_root_7 43948
cert_nodes_3 1152
cert_boundary_classification_5 1152 04

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
