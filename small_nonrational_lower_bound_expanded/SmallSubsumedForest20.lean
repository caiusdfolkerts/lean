module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import RootedSmallCache
public import RootedSmallGeneratorWords
public import SubsumedClassification
public import SmallSubsumedForest20Leaves
public import SmallSubsumedForest20Proof000
public import SmallSubsumedForest20Proof001
public import SmallSubsumedForest20Proof002
public import SmallSubsumedForest20Proof003
public import SmallSubsumedForest20Proof004
public import SmallSubsumedForest20Proof005
public import SmallSubsumedForest20Proof006
public import SmallSubsumedForest20Proof007
public import SmallSubsumedForest20Proof008
public import SmallSubsumedForest20Proof009
public import SmallSubsumedForest20Proof010
public import SmallSubsumedForest20Proof011
public import SmallSubsumedForest20Proof012
public import SmallSubsumedForest20Proof013
public import SmallSubsumedForest20Proof014
public import SmallSubsumedForest20Proof015
public import SmallSubsumedForest20Proof016
public import SmallSubsumedForest20Proof017
public import SmallSubsumedForest20Proof018
public import SmallSubsumedForest20Proof019
public import SmallSubsumedForest20Proof020
public import SmallSubsumedForest20Proof021
public import SmallSubsumedForest20Proof022
public import SmallSubsumedForest20Proof023
public import SmallSubsumedForest20Proof024
public import SmallSubsumedForest20Proof025
public import SmallSubsumedForest20Proof026
public import SmallSubsumedForest20Proof027

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest20
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 8960 17783 (interval_append nodeTest 0 4480 8960 (interval_append nodeTest 0 1920 4480 (interval_append nodeTest 0 640 1920 nodeInterval0 (interval_append nodeTest 640 1280 1920 nodeInterval640 nodeInterval1280)) (interval_append nodeTest 1920 3200 4480 (interval_append nodeTest 1920 2560 3200 nodeInterval1920 nodeInterval2560) (interval_append nodeTest 3200 3840 4480 nodeInterval3200 nodeInterval3840))) (interval_append nodeTest 4480 6400 8960 (interval_append nodeTest 4480 5120 6400 nodeInterval4480 (interval_append nodeTest 5120 5760 6400 nodeInterval5120 nodeInterval5760)) (interval_append nodeTest 6400 7680 8960 (interval_append nodeTest 6400 7040 7680 nodeInterval6400 nodeInterval7040) (interval_append nodeTest 7680 8320 8960 nodeInterval7680 nodeInterval8320)))) (interval_append nodeTest 8960 13440 17783 (interval_append nodeTest 8960 10880 13440 (interval_append nodeTest 8960 9600 10880 nodeInterval8960 (interval_append nodeTest 9600 10240 10880 nodeInterval9600 nodeInterval10240)) (interval_append nodeTest 10880 12160 13440 (interval_append nodeTest 10880 11520 12160 nodeInterval10880 nodeInterval11520) (interval_append nodeTest 12160 12800 13440 nodeInterval12160 nodeInterval12800))) (interval_append nodeTest 13440 15360 17783 (interval_append nodeTest 13440 14080 15360 nodeInterval13440 (interval_append nodeTest 14080 14720 15360 nodeInterval14080 nodeInterval14720)) (interval_append nodeTest 15360 16640 17783 (interval_append nodeTest 15360 16000 16640 nodeInterval15360 nodeInterval16000) (interval_append nodeTest 16640 17280 17783 nodeInterval16640 nodeInterval17280)))))
cert_root_8 17782
cert_nodes_4
cert_boundary_classification_6

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest20
