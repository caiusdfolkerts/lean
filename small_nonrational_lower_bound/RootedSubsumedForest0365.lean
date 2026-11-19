module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSixBase02GrowthCache
public import RootedSixBase02FastWords
public import SubsumedClassification
public import RootedSubsumedForest0365Leaves
public import RootedSubsumedForest0365Proof000
public import RootedSubsumedForest0365Proof001
public import RootedSubsumedForest0365Proof002
public import RootedSubsumedForest0365Proof003
public import RootedSubsumedForest0365Proof004
public import RootedSubsumedForest0365Proof005
public import RootedSubsumedForest0365Proof006
public import RootedSubsumedForest0365Proof007
public import RootedSubsumedForest0365Proof008
public import RootedSubsumedForest0365Proof009
public import RootedSubsumedForest0365Proof010
public import RootedSubsumedForest0365Proof011
public import RootedSubsumedForest0365Proof012
public import RootedSubsumedForest0365Proof013
public import RootedSubsumedForest0365Proof014
public import RootedSubsumedForest0365Proof015
public import RootedSubsumedForest0365Proof016
public import RootedSubsumedForest0365Proof017
public import RootedSubsumedForest0365Proof018
public import RootedSubsumedForest0365Proof019

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0365
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 6400 12767 (interval_append nodeTest 0 3200 6400 (interval_append nodeTest 0 1280 3200 (interval_append nodeTest 0 640 1280 nodeInterval0 nodeInterval640) (interval_append nodeTest 1280 1920 3200 nodeInterval1280 (interval_append nodeTest 1920 2560 3200 nodeInterval1920 nodeInterval2560))) (interval_append nodeTest 3200 4480 6400 (interval_append nodeTest 3200 3840 4480 nodeInterval3200 nodeInterval3840) (interval_append nodeTest 4480 5120 6400 nodeInterval4480 (interval_append nodeTest 5120 5760 6400 nodeInterval5120 nodeInterval5760)))) (interval_append nodeTest 6400 9600 12767 (interval_append nodeTest 6400 7680 9600 (interval_append nodeTest 6400 7040 7680 nodeInterval6400 nodeInterval7040) (interval_append nodeTest 7680 8320 9600 nodeInterval7680 (interval_append nodeTest 8320 8960 9600 nodeInterval8320 nodeInterval8960))) (interval_append nodeTest 9600 10880 12767 (interval_append nodeTest 9600 10240 10880 nodeInterval9600 nodeInterval10240) (interval_append nodeTest 10880 11520 12767 nodeInterval10880 (interval_append nodeTest 11520 12160 12767 nodeInterval11520 nodeInterval12160)))))
cert_root_7 12766
cert_nodes_3 48
cert_boundary_classification_5 48 02
#print axioms boundary_classification

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0365
