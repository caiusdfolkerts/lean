module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSixBase03GrowthCache
public import RootedSixBase03FastWords
public import SubsumedClassification
public import RootedSubsumedForest0696Leaves
public import RootedSubsumedForest0696Proof000
public import RootedSubsumedForest0696Proof001
public import RootedSubsumedForest0696Proof002
public import RootedSubsumedForest0696Proof003
public import RootedSubsumedForest0696Proof004
public import RootedSubsumedForest0696Proof005
public import RootedSubsumedForest0696Proof006
public import RootedSubsumedForest0696Proof007
public import RootedSubsumedForest0696Proof008
public import RootedSubsumedForest0696Proof009
public import RootedSubsumedForest0696Proof010
public import RootedSubsumedForest0696Proof011
public import RootedSubsumedForest0696Proof012
public import RootedSubsumedForest0696Proof013
public import RootedSubsumedForest0696Proof014
public import RootedSubsumedForest0696Proof015
public import RootedSubsumedForest0696Proof016
public import RootedSubsumedForest0696Proof017
public import RootedSubsumedForest0696Proof018

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0696
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 5760 12131 (interval_append nodeTest 0 2560 5760 (interval_append nodeTest 0 1280 2560 (interval_append nodeTest 0 640 1280 nodeInterval0 nodeInterval640) (interval_append nodeTest 1280 1920 2560 nodeInterval1280 nodeInterval1920)) (interval_append nodeTest 2560 3840 5760 (interval_append nodeTest 2560 3200 3840 nodeInterval2560 nodeInterval3200) (interval_append nodeTest 3840 4480 5760 nodeInterval3840 (interval_append nodeTest 4480 5120 5760 nodeInterval4480 nodeInterval5120)))) (interval_append nodeTest 5760 8960 12131 (interval_append nodeTest 5760 7040 8960 (interval_append nodeTest 5760 6400 7040 nodeInterval5760 nodeInterval6400) (interval_append nodeTest 7040 7680 8960 nodeInterval7040 (interval_append nodeTest 7680 8320 8960 nodeInterval7680 nodeInterval8320))) (interval_append nodeTest 8960 10240 12131 (interval_append nodeTest 8960 9600 10240 nodeInterval8960 nodeInterval9600) (interval_append nodeTest 10240 10880 12131 nodeInterval10240 (interval_append nodeTest 10880 11520 12131 nodeInterval10880 nodeInterval11520)))))
cert_root_7 12130
cert_nodes_3 96
cert_boundary_classification_5 96 03
#print axioms boundary_classification

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0696
