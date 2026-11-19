module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import RootedSmallCache
public import RootedSmallGeneratorWords
public import SubsumedClassification
public import SmallSubsumedForest07Leaves
public import SmallSubsumedForest07Proof000
public import SmallSubsumedForest07Proof001
public import SmallSubsumedForest07Proof002
public import SmallSubsumedForest07Proof003
public import SmallSubsumedForest07Proof004
public import SmallSubsumedForest07Proof005
public import SmallSubsumedForest07Proof006
public import SmallSubsumedForest07Proof007
public import SmallSubsumedForest07Proof008
public import SmallSubsumedForest07Proof009
public import SmallSubsumedForest07Proof010
public import SmallSubsumedForest07Proof011
public import SmallSubsumedForest07Proof012
public import SmallSubsumedForest07Proof013
public import SmallSubsumedForest07Proof014
public import SmallSubsumedForest07Proof015
public import SmallSubsumedForest07Proof016
public import SmallSubsumedForest07Proof017
public import SmallSubsumedForest07Proof018
public import SmallSubsumedForest07Proof019
public import SmallSubsumedForest07Proof020
public import SmallSubsumedForest07Proof021
public import SmallSubsumedForest07Proof022
public import SmallSubsumedForest07Proof023
public import SmallSubsumedForest07Proof024
public import SmallSubsumedForest07Proof025

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest07
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 8320 16021 (interval_append nodeTest 0 3840 8320 (interval_append nodeTest 0 1920 3840 (interval_append nodeTest 0 640 1920 nodeInterval0 (interval_append nodeTest 640 1280 1920 nodeInterval640 nodeInterval1280)) (interval_append nodeTest 1920 2560 3840 nodeInterval1920 (interval_append nodeTest 2560 3200 3840 nodeInterval2560 nodeInterval3200))) (interval_append nodeTest 3840 5760 8320 (interval_append nodeTest 3840 4480 5760 nodeInterval3840 (interval_append nodeTest 4480 5120 5760 nodeInterval4480 nodeInterval5120)) (interval_append nodeTest 5760 7040 8320 (interval_append nodeTest 5760 6400 7040 nodeInterval5760 nodeInterval6400) (interval_append nodeTest 7040 7680 8320 nodeInterval7040 nodeInterval7680)))) (interval_append nodeTest 8320 12160 16021 (interval_append nodeTest 8320 10240 12160 (interval_append nodeTest 8320 8960 10240 nodeInterval8320 (interval_append nodeTest 8960 9600 10240 nodeInterval8960 nodeInterval9600)) (interval_append nodeTest 10240 10880 12160 nodeInterval10240 (interval_append nodeTest 10880 11520 12160 nodeInterval10880 nodeInterval11520))) (interval_append nodeTest 12160 14080 16021 (interval_append nodeTest 12160 12800 14080 nodeInterval12160 (interval_append nodeTest 12800 13440 14080 nodeInterval12800 nodeInterval13440)) (interval_append nodeTest 14080 15360 16021 (interval_append nodeTest 14080 14720 15360 nodeInterval14080 nodeInterval14720) (interval_append nodeTest 15360 16000 16021 nodeInterval15360 nodeInterval16000)))))
cert_root_8 16020
cert_nodes_4
cert_boundary_classification_6
#print axioms boundary_classification

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest07
