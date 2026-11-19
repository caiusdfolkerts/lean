module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0707Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0707
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem bulkNodes8320 : Interval nodeTest 8320 8384 :=
  interval_of_check nodeTest 8320 64 (by decide +kernel)
theorem bulkNodes8384 : Interval nodeTest 8384 8448 :=
  interval_of_check nodeTest 8384 64 (by decide +kernel)
theorem bulkNodes8448 : Interval nodeTest 8448 8512 :=
  interval_of_check nodeTest 8448 64 (by decide +kernel)
theorem bulkNodes8512 : Interval nodeTest 8512 8576 :=
  interval_of_check nodeTest 8512 64 (by decide +kernel)
theorem bulkNodes8576 : Interval nodeTest 8576 8640 :=
  interval_of_check nodeTest 8576 64 (by decide +kernel)
theorem bulkNodes8640 : Interval nodeTest 8640 8704 :=
  interval_of_check nodeTest 8640 64 (by decide +kernel)
theorem bulkNodes8704 : Interval nodeTest 8704 8768 :=
  interval_of_check nodeTest 8704 64 (by decide +kernel)
theorem bulkNodes8768 : Interval nodeTest 8768 8832 :=
  interval_of_check nodeTest 8768 64 (by decide +kernel)
theorem bulkNodes8832 : Interval nodeTest 8832 8896 :=
  interval_of_check nodeTest 8832 64 (by decide +kernel)
theorem bulkNodes8896 : Interval nodeTest 8896 8960 :=
  interval_of_check nodeTest 8896 64 (by decide +kernel)
theorem nodeInterval8320 : Interval nodeTest 8320 8960 :=
  (interval_append nodeTest 8320 8640 8960
  (interval_append nodeTest 8320 8448 8640
  (interval_append nodeTest 8320 8384 8448
  bulkNodes8320
  bulkNodes8384)
  (interval_append nodeTest 8448 8512 8640
  bulkNodes8448
  (interval_append nodeTest 8512 8576 8640
  bulkNodes8512
  bulkNodes8576)))
  (interval_append nodeTest 8640 8768 8960
  (interval_append nodeTest 8640 8704 8768
  bulkNodes8640
  bulkNodes8704)
  (interval_append nodeTest 8768 8832 8960
  bulkNodes8768
  (interval_append nodeTest 8832 8896 8960
  bulkNodes8832
  bulkNodes8896))))
theorem bulkNodes8960 : Interval nodeTest 8960 9024 :=
  interval_of_check nodeTest 8960 64 (by decide +kernel)
theorem bulkNodes9024 : Interval nodeTest 9024 9088 :=
  interval_of_check nodeTest 9024 64 (by decide +kernel)
theorem bulkNodes9088 : Interval nodeTest 9088 9152 :=
  interval_of_check nodeTest 9088 64 (by decide +kernel)
theorem bulkNodes9152 : Interval nodeTest 9152 9216 :=
  interval_of_check nodeTest 9152 64 (by decide +kernel)
theorem bulkNodes9216 : Interval nodeTest 9216 9280 :=
  interval_of_check nodeTest 9216 64 (by decide +kernel)
theorem bulkNodes9280 : Interval nodeTest 9280 9344 :=
  interval_of_check nodeTest 9280 64 (by decide +kernel)
theorem bulkNodes9344 : Interval nodeTest 9344 9408 :=
  interval_of_check nodeTest 9344 64 (by decide +kernel)
theorem bulkNodes9408 : Interval nodeTest 9408 9472 :=
  interval_of_check nodeTest 9408 64 (by decide +kernel)
theorem bulkNodes9472 : Interval nodeTest 9472 9536 :=
  interval_of_check nodeTest 9472 64 (by decide +kernel)
theorem bulkNodes9536 : Interval nodeTest 9536 9600 :=
  interval_of_check nodeTest 9536 64 (by decide +kernel)
theorem nodeInterval8960 : Interval nodeTest 8960 9600 :=
  (interval_append nodeTest 8960 9280 9600
  (interval_append nodeTest 8960 9088 9280
  (interval_append nodeTest 8960 9024 9088
  bulkNodes8960
  bulkNodes9024)
  (interval_append nodeTest 9088 9152 9280
  bulkNodes9088
  (interval_append nodeTest 9152 9216 9280
  bulkNodes9152
  bulkNodes9216)))
  (interval_append nodeTest 9280 9408 9600
  (interval_append nodeTest 9280 9344 9408
  bulkNodes9280
  bulkNodes9344)
  (interval_append nodeTest 9408 9472 9600
  bulkNodes9408
  (interval_append nodeTest 9472 9536 9600
  bulkNodes9472
  bulkNodes9536))))
theorem bulkNodes9600 : Interval nodeTest 9600 9664 :=
  interval_of_check nodeTest 9600 64 (by decide +kernel)
theorem bulkNodes9664 : Interval nodeTest 9664 9728 :=
  interval_of_check nodeTest 9664 64 (by decide +kernel)
theorem bulkNodes9728 : Interval nodeTest 9728 9792 :=
  interval_of_check nodeTest 9728 64 (by decide +kernel)
theorem bulkNodes9792 : Interval nodeTest 9792 9856 :=
  interval_of_check nodeTest 9792 64 (by decide +kernel)
theorem bulkNodes9856 : Interval nodeTest 9856 9920 :=
  interval_of_check nodeTest 9856 64 (by decide +kernel)
theorem bulkNodes9920 : Interval nodeTest 9920 9984 :=
  interval_of_check nodeTest 9920 64 (by decide +kernel)
theorem bulkNodes9984 : Interval nodeTest 9984 10048 :=
  interval_of_check nodeTest 9984 64 (by decide +kernel)
theorem bulkNodes10048 : Interval nodeTest 10048 10112 :=
  interval_of_check nodeTest 10048 64 (by decide +kernel)
theorem bulkNodes10112 : Interval nodeTest 10112 10176 :=
  interval_of_check nodeTest 10112 64 (by decide +kernel)
theorem bulkNodes10176 : Interval nodeTest 10176 10223 :=
  interval_of_check nodeTest 10176 47 (by decide +kernel)
theorem nodeInterval9600 : Interval nodeTest 9600 10223 :=
  (interval_append nodeTest 9600 9920 10223
  (interval_append nodeTest 9600 9728 9920
  (interval_append nodeTest 9600 9664 9728
  bulkNodes9600
  bulkNodes9664)
  (interval_append nodeTest 9728 9792 9920
  bulkNodes9728
  (interval_append nodeTest 9792 9856 9920
  bulkNodes9792
  bulkNodes9856)))
  (interval_append nodeTest 9920 10048 10223
  (interval_append nodeTest 9920 9984 10048
  bulkNodes9920
  bulkNodes9984)
  (interval_append nodeTest 10048 10112 10223
  bulkNodes10048
  (interval_append nodeTest 10112 10176 10223
  bulkNodes10112
  bulkNodes10176))))
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0707
