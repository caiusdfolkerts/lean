module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSixBase00GrowthCache
public import RootedSixBase00FastWords
public import SubsumedClassification
public import RootedSubsumedForest0337Leaves
public import RootedSubsumedForest0337ProofGrouped000
public import RootedSubsumedForest0337ProofGrouped001
public import RootedSubsumedForest0337ProofGrouped002
public import RootedSubsumedForest0337ProofGrouped003
public import RootedSubsumedForest0337ProofGrouped004
public import RootedSubsumedForest0337ProofGrouped005
public import RootedSubsumedForest0337ProofGrouped006

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0337
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 21120 41895 (interval_append nodeTest 0 10240 21120 (interval_append nodeTest 0 5120 10240 (interval_append nodeTest 0 2560 5120 (interval_append nodeTest 0 1280 2560 (interval_append nodeTest 0 640 1280 nodeInterval0 nodeInterval640) (interval_append nodeTest 1280 1920 2560 nodeInterval1280 nodeInterval1920)) (interval_append nodeTest 2560 3840 5120 (interval_append nodeTest 2560 3200 3840 nodeInterval2560 nodeInterval3200) (interval_append nodeTest 3840 4480 5120 nodeInterval3840 nodeInterval4480))) (interval_append nodeTest 5120 7680 10240 (interval_append nodeTest 5120 6400 7680 (interval_append nodeTest 5120 5760 6400 nodeInterval5120 nodeInterval5760) (interval_append nodeTest 6400 7040 7680 nodeInterval6400 nodeInterval7040)) (interval_append nodeTest 7680 8960 10240 (interval_append nodeTest 7680 8320 8960 nodeInterval7680 nodeInterval8320) (interval_append nodeTest 8960 9600 10240 nodeInterval8960 nodeInterval9600)))) (interval_append nodeTest 10240 15360 21120 (interval_append nodeTest 10240 12800 15360 (interval_append nodeTest 10240 11520 12800 (interval_append nodeTest 10240 10880 11520 nodeInterval10240 nodeInterval10880) (interval_append nodeTest 11520 12160 12800 nodeInterval11520 nodeInterval12160)) (interval_append nodeTest 12800 14080 15360 (interval_append nodeTest 12800 13440 14080 nodeInterval12800 nodeInterval13440) (interval_append nodeTest 14080 14720 15360 nodeInterval14080 nodeInterval14720))) (interval_append nodeTest 15360 17920 21120 (interval_append nodeTest 15360 16640 17920 (interval_append nodeTest 15360 16000 16640 nodeInterval15360 nodeInterval16000) (interval_append nodeTest 16640 17280 17920 nodeInterval16640 nodeInterval17280)) (interval_append nodeTest 17920 19200 21120 (interval_append nodeTest 17920 18560 19200 nodeInterval17920 nodeInterval18560) (interval_append nodeTest 19200 19840 21120 nodeInterval19200 (interval_append nodeTest 19840 20480 21120 nodeInterval19840 nodeInterval20480)))))) (interval_append nodeTest 21120 31360 41895 (interval_append nodeTest 21120 26240 31360 (interval_append nodeTest 21120 23680 26240 (interval_append nodeTest 21120 22400 23680 (interval_append nodeTest 21120 21760 22400 nodeInterval21120 nodeInterval21760) (interval_append nodeTest 22400 23040 23680 nodeInterval22400 nodeInterval23040)) (interval_append nodeTest 23680 24960 26240 (interval_append nodeTest 23680 24320 24960 nodeInterval23680 nodeInterval24320) (interval_append nodeTest 24960 25600 26240 nodeInterval24960 nodeInterval25600))) (interval_append nodeTest 26240 28800 31360 (interval_append nodeTest 26240 27520 28800 (interval_append nodeTest 26240 26880 27520 nodeInterval26240 nodeInterval26880) (interval_append nodeTest 27520 28160 28800 nodeInterval27520 nodeInterval28160)) (interval_append nodeTest 28800 30080 31360 (interval_append nodeTest 28800 29440 30080 nodeInterval28800 nodeInterval29440) (interval_append nodeTest 30080 30720 31360 nodeInterval30080 nodeInterval30720)))) (interval_append nodeTest 31360 36480 41895 (interval_append nodeTest 31360 33920 36480 (interval_append nodeTest 31360 32640 33920 (interval_append nodeTest 31360 32000 32640 nodeInterval31360 nodeInterval32000) (interval_append nodeTest 32640 33280 33920 nodeInterval32640 nodeInterval33280)) (interval_append nodeTest 33920 35200 36480 (interval_append nodeTest 33920 34560 35200 nodeInterval33920 nodeInterval34560) (interval_append nodeTest 35200 35840 36480 nodeInterval35200 nodeInterval35840))) (interval_append nodeTest 36480 39040 41895 (interval_append nodeTest 36480 37760 39040 (interval_append nodeTest 36480 37120 37760 nodeInterval36480 nodeInterval37120) (interval_append nodeTest 37760 38400 39040 nodeInterval37760 nodeInterval38400)) (interval_append nodeTest 39040 40320 41895 (interval_append nodeTest 39040 39680 40320 nodeInterval39040 nodeInterval39680) (interval_append nodeTest 40320 40960 41895 nodeInterval40320 (interval_append nodeTest 40960 41600 41895 nodeInterval40960 nodeInterval41600)))))))
cert_root_7 41894
cert_nodes_3 96
cert_boundary_classification_5 96 00
#print axioms boundary_classification

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0337
