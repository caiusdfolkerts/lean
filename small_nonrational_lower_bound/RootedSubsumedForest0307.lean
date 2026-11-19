module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSixBase02GrowthCache
public import RootedSixBase02FastWords
public import SubsumedClassification
public import RootedSubsumedForest0307Leaves
public import RootedSubsumedForest0307Proof000
public import RootedSubsumedForest0307Proof001
public import RootedSubsumedForest0307Proof002
public import RootedSubsumedForest0307Proof003
public import RootedSubsumedForest0307Proof004
public import RootedSubsumedForest0307Proof005
public import RootedSubsumedForest0307Proof006
public import RootedSubsumedForest0307Proof007
public import RootedSubsumedForest0307Proof008
public import RootedSubsumedForest0307Proof009
public import RootedSubsumedForest0307Proof010
public import RootedSubsumedForest0307Proof011
public import RootedSubsumedForest0307Proof012
public import RootedSubsumedForest0307Proof013
public import RootedSubsumedForest0307Proof014
public import RootedSubsumedForest0307Proof015
public import RootedSubsumedForest0307Proof016
public import RootedSubsumedForest0307Proof017

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0307
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 5760 11452 (interval_append nodeTest 0 2560 5760 (interval_append nodeTest 0 1280 2560 (interval_append nodeTest 0 640 1280 nodeInterval0 nodeInterval640) (interval_append nodeTest 1280 1920 2560 nodeInterval1280 nodeInterval1920)) (interval_append nodeTest 2560 3840 5760 (interval_append nodeTest 2560 3200 3840 nodeInterval2560 nodeInterval3200) (interval_append nodeTest 3840 4480 5760 nodeInterval3840 (interval_append nodeTest 4480 5120 5760 nodeInterval4480 nodeInterval5120)))) (interval_append nodeTest 5760 8320 11452 (interval_append nodeTest 5760 7040 8320 (interval_append nodeTest 5760 6400 7040 nodeInterval5760 nodeInterval6400) (interval_append nodeTest 7040 7680 8320 nodeInterval7040 nodeInterval7680)) (interval_append nodeTest 8320 9600 11452 (interval_append nodeTest 8320 8960 9600 nodeInterval8320 nodeInterval8960) (interval_append nodeTest 9600 10240 11452 nodeInterval9600 (interval_append nodeTest 10240 10880 11452 nodeInterval10240 nodeInterval10880)))))
cert_root_7 11451
cert_nodes_3 48
cert_boundary_classification_5 48 02
#print axioms boundary_classification

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0307
