module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import RootedSmallCache
public import RootedSmallGeneratorWords
public import SubsumedClassification
public import SmallSubsumedForest11Leaves
public import SmallSubsumedForest11Proof000
public import SmallSubsumedForest11Proof001
public import SmallSubsumedForest11Proof002
public import SmallSubsumedForest11Proof003
public import SmallSubsumedForest11Proof004
public import SmallSubsumedForest11Proof005
public import SmallSubsumedForest11Proof006
public import SmallSubsumedForest11Proof007
public import SmallSubsumedForest11Proof008
public import SmallSubsumedForest11Proof009
public import SmallSubsumedForest11Proof010
public import SmallSubsumedForest11Proof011
public import SmallSubsumedForest11Proof012
public import SmallSubsumedForest11Proof013
public import SmallSubsumedForest11Proof014
public import SmallSubsumedForest11Proof015
public import SmallSubsumedForest11Proof016
public import SmallSubsumedForest11Proof017
public import SmallSubsumedForest11Proof018
public import SmallSubsumedForest11Proof019
public import SmallSubsumedForest11Proof020
public import SmallSubsumedForest11Proof021
public import SmallSubsumedForest11Proof022
public import SmallSubsumedForest11Proof023
public import SmallSubsumedForest11Proof024
public import SmallSubsumedForest11Proof025
public import SmallSubsumedForest11Proof026

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest11
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 8320 17200 (interval_append nodeTest 0 3840 8320 (interval_append nodeTest 0 1920 3840 (interval_append nodeTest 0 640 1920 nodeInterval0 (interval_append nodeTest 640 1280 1920 nodeInterval640 nodeInterval1280)) (interval_append nodeTest 1920 2560 3840 nodeInterval1920 (interval_append nodeTest 2560 3200 3840 nodeInterval2560 nodeInterval3200))) (interval_append nodeTest 3840 5760 8320 (interval_append nodeTest 3840 4480 5760 nodeInterval3840 (interval_append nodeTest 4480 5120 5760 nodeInterval4480 nodeInterval5120)) (interval_append nodeTest 5760 7040 8320 (interval_append nodeTest 5760 6400 7040 nodeInterval5760 nodeInterval6400) (interval_append nodeTest 7040 7680 8320 nodeInterval7040 nodeInterval7680)))) (interval_append nodeTest 8320 12800 17200 (interval_append nodeTest 8320 10240 12800 (interval_append nodeTest 8320 8960 10240 nodeInterval8320 (interval_append nodeTest 8960 9600 10240 nodeInterval8960 nodeInterval9600)) (interval_append nodeTest 10240 11520 12800 (interval_append nodeTest 10240 10880 11520 nodeInterval10240 nodeInterval10880) (interval_append nodeTest 11520 12160 12800 nodeInterval11520 nodeInterval12160))) (interval_append nodeTest 12800 14720 17200 (interval_append nodeTest 12800 13440 14720 nodeInterval12800 (interval_append nodeTest 13440 14080 14720 nodeInterval13440 nodeInterval14080)) (interval_append nodeTest 14720 16000 17200 (interval_append nodeTest 14720 15360 16000 nodeInterval14720 nodeInterval15360) (interval_append nodeTest 16000 16640 17200 nodeInterval16000 nodeInterval16640)))))
cert_root_8 17199
cert_nodes_4
cert_boundary_classification_6

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest11
