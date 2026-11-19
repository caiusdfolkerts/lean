module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import RootedSmallCache
public import RootedSmallGeneratorWords
public import SubsumedClassification
public import SmallSubsumedForest10Leaves
public import SmallSubsumedForest10Proof000
public import SmallSubsumedForest10Proof001
public import SmallSubsumedForest10Proof002
public import SmallSubsumedForest10Proof003
public import SmallSubsumedForest10Proof004
public import SmallSubsumedForest10Proof005
public import SmallSubsumedForest10Proof006
public import SmallSubsumedForest10Proof007
public import SmallSubsumedForest10Proof008
public import SmallSubsumedForest10Proof009
public import SmallSubsumedForest10Proof010
public import SmallSubsumedForest10Proof011
public import SmallSubsumedForest10Proof012
public import SmallSubsumedForest10Proof013
public import SmallSubsumedForest10Proof014
public import SmallSubsumedForest10Proof015
public import SmallSubsumedForest10Proof016

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest10
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 5120 10529 (interval_append nodeTest 0 2560 5120 (interval_append nodeTest 0 1280 2560 (interval_append nodeTest 0 640 1280 nodeInterval0 nodeInterval640) (interval_append nodeTest 1280 1920 2560 nodeInterval1280 nodeInterval1920)) (interval_append nodeTest 2560 3840 5120 (interval_append nodeTest 2560 3200 3840 nodeInterval2560 nodeInterval3200) (interval_append nodeTest 3840 4480 5120 nodeInterval3840 nodeInterval4480))) (interval_append nodeTest 5120 7680 10529 (interval_append nodeTest 5120 6400 7680 (interval_append nodeTest 5120 5760 6400 nodeInterval5120 nodeInterval5760) (interval_append nodeTest 6400 7040 7680 nodeInterval6400 nodeInterval7040)) (interval_append nodeTest 7680 8960 10529 (interval_append nodeTest 7680 8320 8960 nodeInterval7680 nodeInterval8320) (interval_append nodeTest 8960 9600 10529 nodeInterval8960 (interval_append nodeTest 9600 10240 10529 nodeInterval9600 nodeInterval10240)))))
cert_root_8 10528
cert_nodes_4
cert_boundary_classification_6

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest10
