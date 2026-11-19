module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSixBase01GrowthCache
public import RootedSixBase01FastWords
public import SubsumedClassification
public import RootedSubsumedForest0352Leaves
public import RootedSubsumedForest0352Proof000
public import RootedSubsumedForest0352Proof001
public import RootedSubsumedForest0352Proof002
public import RootedSubsumedForest0352Proof003
public import RootedSubsumedForest0352Proof004
public import RootedSubsumedForest0352Proof005
public import RootedSubsumedForest0352Proof006
public import RootedSubsumedForest0352Proof007
public import RootedSubsumedForest0352Proof008
public import RootedSubsumedForest0352Proof009
public import RootedSubsumedForest0352Proof010
public import RootedSubsumedForest0352Proof011
public import RootedSubsumedForest0352Proof012
public import RootedSubsumedForest0352Proof013
public import RootedSubsumedForest0352Proof014
public import RootedSubsumedForest0352Proof015
public import RootedSubsumedForest0352Proof016
public import RootedSubsumedForest0352Proof017
public import RootedSubsumedForest0352Proof018
public import RootedSubsumedForest0352Proof019
public import RootedSubsumedForest0352Proof020
public import RootedSubsumedForest0352Proof021
public import RootedSubsumedForest0352Proof022
public import RootedSubsumedForest0352Proof023
public import RootedSubsumedForest0352Proof024

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0352
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 7680 15697 (interval_append nodeTest 0 3840 7680 (interval_append nodeTest 0 1920 3840 (interval_append nodeTest 0 640 1920 nodeInterval0 (interval_append nodeTest 640 1280 1920 nodeInterval640 nodeInterval1280)) (interval_append nodeTest 1920 2560 3840 nodeInterval1920 (interval_append nodeTest 2560 3200 3840 nodeInterval2560 nodeInterval3200))) (interval_append nodeTest 3840 5760 7680 (interval_append nodeTest 3840 4480 5760 nodeInterval3840 (interval_append nodeTest 4480 5120 5760 nodeInterval4480 nodeInterval5120)) (interval_append nodeTest 5760 6400 7680 nodeInterval5760 (interval_append nodeTest 6400 7040 7680 nodeInterval6400 nodeInterval7040)))) (interval_append nodeTest 7680 11520 15697 (interval_append nodeTest 7680 9600 11520 (interval_append nodeTest 7680 8320 9600 nodeInterval7680 (interval_append nodeTest 8320 8960 9600 nodeInterval8320 nodeInterval8960)) (interval_append nodeTest 9600 10240 11520 nodeInterval9600 (interval_append nodeTest 10240 10880 11520 nodeInterval10240 nodeInterval10880))) (interval_append nodeTest 11520 13440 15697 (interval_append nodeTest 11520 12160 13440 nodeInterval11520 (interval_append nodeTest 12160 12800 13440 nodeInterval12160 nodeInterval12800)) (interval_append nodeTest 13440 14720 15697 (interval_append nodeTest 13440 14080 14720 nodeInterval13440 nodeInterval14080) (interval_append nodeTest 14720 15360 15697 nodeInterval14720 nodeInterval15360)))))
cert_root_7 15696
cert_nodes_3 48
cert_boundary_classification_5 48 01
#print axioms boundary_classification

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0352
