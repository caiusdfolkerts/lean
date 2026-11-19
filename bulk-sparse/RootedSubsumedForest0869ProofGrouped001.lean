module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedBulk
public import RootedSubsumedForest0869Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0869
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem bulkNodes8320 : Interval nodeTest 8320 8384 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    8320 64 (by decide +kernel)
theorem bulkNodes8384 : Interval nodeTest 8384 8448 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    8384 64 (by decide +kernel)
theorem bulkNodes8448 : Interval nodeTest 8448 8512 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    8448 64 (by decide +kernel)
theorem bulkNodes8512 : Interval nodeTest 8512 8576 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    8512 64 (by decide +kernel)
theorem bulkNodes8576 : Interval nodeTest 8576 8640 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    8576 64 (by decide +kernel)
theorem bulkNodes8640 : Interval nodeTest 8640 8704 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    8640 64 (by decide +kernel)
theorem bulkNodes8704 : Interval nodeTest 8704 8768 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    8704 64 (by decide +kernel)
theorem bulkNodes8768 : Interval nodeTest 8768 8832 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    8768 64 (by decide +kernel)
theorem bulkNodes8832 : Interval nodeTest 8832 8896 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    8832 64 (by decide +kernel)
theorem bulkNodes8896 : Interval nodeTest 8896 8960 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    8896 64 (by decide +kernel)
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
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    8960 64 (by decide +kernel)
theorem bulkNodes9024 : Interval nodeTest 9024 9088 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    9024 64 (by decide +kernel)
theorem bulkNodes9088 : Interval nodeTest 9088 9152 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    9088 64 (by decide +kernel)
theorem bulkNodes9152 : Interval nodeTest 9152 9216 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    9152 64 (by decide +kernel)
theorem bulkNodes9216 : Interval nodeTest 9216 9280 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    9216 64 (by decide +kernel)
theorem bulkNodes9280 : Interval nodeTest 9280 9344 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    9280 64 (by decide +kernel)
theorem bulkNodes9344 : Interval nodeTest 9344 9408 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    9344 64 (by decide +kernel)
theorem bulkNodes9408 : Interval nodeTest 9408 9472 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    9408 64 (by decide +kernel)
theorem bulkNodes9472 : Interval nodeTest 9472 9536 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    9472 64 (by decide +kernel)
theorem bulkNodes9536 : Interval nodeTest 9536 9600 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    9536 64 (by decide +kernel)
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
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    9600 64 (by decide +kernel)
theorem bulkNodes9664 : Interval nodeTest 9664 9728 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    9664 64 (by decide +kernel)
theorem bulkNodes9728 : Interval nodeTest 9728 9792 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    9728 64 (by decide +kernel)
theorem bulkNodes9792 : Interval nodeTest 9792 9856 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    9792 64 (by decide +kernel)
theorem bulkNodes9856 : Interval nodeTest 9856 9920 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    9856 64 (by decide +kernel)
theorem bulkNodes9920 : Interval nodeTest 9920 9984 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    9920 64 (by decide +kernel)
theorem bulkNodes9984 : Interval nodeTest 9984 10048 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    9984 64 (by decide +kernel)
theorem bulkNodes10048 : Interval nodeTest 10048 10112 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    10048 64 (by decide +kernel)
theorem bulkNodes10112 : Interval nodeTest 10112 10176 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    10112 64 (by decide +kernel)
theorem bulkNodes10176 : Interval nodeTest 10176 10240 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    10176 64 (by decide +kernel)
theorem nodeInterval9600 : Interval nodeTest 9600 10240 :=
  (interval_append nodeTest 9600 9920 10240
  (interval_append nodeTest 9600 9728 9920
  (interval_append nodeTest 9600 9664 9728
  bulkNodes9600
  bulkNodes9664)
  (interval_append nodeTest 9728 9792 9920
  bulkNodes9728
  (interval_append nodeTest 9792 9856 9920
  bulkNodes9792
  bulkNodes9856)))
  (interval_append nodeTest 9920 10048 10240
  (interval_append nodeTest 9920 9984 10048
  bulkNodes9920
  bulkNodes9984)
  (interval_append nodeTest 10048 10112 10240
  bulkNodes10048
  (interval_append nodeTest 10112 10176 10240
  bulkNodes10112
  bulkNodes10176))))
theorem bulkNodes10240 : Interval nodeTest 10240 10304 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    10240 64 (by decide +kernel)
theorem bulkNodes10304 : Interval nodeTest 10304 10368 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    10304 64 (by decide +kernel)
theorem bulkNodes10368 : Interval nodeTest 10368 10432 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    10368 64 (by decide +kernel)
theorem bulkNodes10432 : Interval nodeTest 10432 10496 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    10432 64 (by decide +kernel)
theorem bulkNodes10496 : Interval nodeTest 10496 10560 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    10496 64 (by decide +kernel)
theorem bulkNodes10560 : Interval nodeTest 10560 10624 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    10560 64 (by decide +kernel)
theorem bulkNodes10624 : Interval nodeTest 10624 10688 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    10624 64 (by decide +kernel)
theorem bulkNodes10688 : Interval nodeTest 10688 10752 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    10688 64 (by decide +kernel)
theorem bulkNodes10752 : Interval nodeTest 10752 10816 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    10752 64 (by decide +kernel)
theorem bulkNodes10816 : Interval nodeTest 10816 10880 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    10816 64 (by decide +kernel)
theorem nodeInterval10240 : Interval nodeTest 10240 10880 :=
  (interval_append nodeTest 10240 10560 10880
  (interval_append nodeTest 10240 10368 10560
  (interval_append nodeTest 10240 10304 10368
  bulkNodes10240
  bulkNodes10304)
  (interval_append nodeTest 10368 10432 10560
  bulkNodes10368
  (interval_append nodeTest 10432 10496 10560
  bulkNodes10432
  bulkNodes10496)))
  (interval_append nodeTest 10560 10688 10880
  (interval_append nodeTest 10560 10624 10688
  bulkNodes10560
  bulkNodes10624)
  (interval_append nodeTest 10688 10752 10880
  bulkNodes10688
  (interval_append nodeTest 10752 10816 10880
  bulkNodes10752
  bulkNodes10816))))
theorem bulkNodes10880 : Interval nodeTest 10880 10944 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    10880 64 (by decide +kernel)
theorem bulkNodes10944 : Interval nodeTest 10944 11008 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    10944 64 (by decide +kernel)
theorem bulkNodes11008 : Interval nodeTest 11008 11072 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    11008 64 (by decide +kernel)
theorem bulkNodes11072 : Interval nodeTest 11072 11136 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    11072 64 (by decide +kernel)
theorem bulkNodes11136 : Interval nodeTest 11136 11200 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    11136 64 (by decide +kernel)
theorem bulkNodes11200 : Interval nodeTest 11200 11264 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    11200 64 (by decide +kernel)
theorem bulkNodes11264 : Interval nodeTest 11264 11328 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    11264 64 (by decide +kernel)
theorem bulkNodes11328 : Interval nodeTest 11328 11392 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    11328 64 (by decide +kernel)
theorem bulkNodes11392 : Interval nodeTest 11392 11456 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    11392 64 (by decide +kernel)
theorem bulkNodes11456 : Interval nodeTest 11456 11520 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    11456 64 (by decide +kernel)
theorem nodeInterval10880 : Interval nodeTest 10880 11520 :=
  (interval_append nodeTest 10880 11200 11520
  (interval_append nodeTest 10880 11008 11200
  (interval_append nodeTest 10880 10944 11008
  bulkNodes10880
  bulkNodes10944)
  (interval_append nodeTest 11008 11072 11200
  bulkNodes11008
  (interval_append nodeTest 11072 11136 11200
  bulkNodes11072
  bulkNodes11136)))
  (interval_append nodeTest 11200 11328 11520
  (interval_append nodeTest 11200 11264 11328
  bulkNodes11200
  bulkNodes11264)
  (interval_append nodeTest 11328 11392 11520
  bulkNodes11328
  (interval_append nodeTest 11392 11456 11520
  bulkNodes11392
  bulkNodes11456))))
theorem bulkNodes11520 : Interval nodeTest 11520 11584 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    11520 64 (by decide +kernel)
theorem bulkNodes11584 : Interval nodeTest 11584 11648 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    11584 64 (by decide +kernel)
theorem bulkNodes11648 : Interval nodeTest 11648 11712 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    11648 64 (by decide +kernel)
theorem bulkNodes11712 : Interval nodeTest 11712 11776 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    11712 64 (by decide +kernel)
theorem bulkNodes11776 : Interval nodeTest 11776 11840 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    11776 64 (by decide +kernel)
theorem bulkNodes11840 : Interval nodeTest 11840 11904 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    11840 64 (by decide +kernel)
theorem bulkNodes11904 : Interval nodeTest 11904 11968 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    11904 64 (by decide +kernel)
theorem bulkNodes11968 : Interval nodeTest 11968 12032 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    11968 64 (by decide +kernel)
theorem bulkNodes12032 : Interval nodeTest 12032 12041 :=
  RootedBulk.interval widths cellCount 1024 288 leafCount nodeCount
    RootedCaches.RootedSixExtra05.candidateMasks RootedCaches.RootedSixExtra05.badMasks RootedCaches.RootedSixExtra05.kindMasks
    RootedCaches.RootedSixExtra05.keys RootedCaches.RootedSixExtra05.fastKind quota FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves codes counters
    12032 9 (by decide +kernel)
theorem nodeInterval11520 : Interval nodeTest 11520 12041 :=
  (interval_append nodeTest 11520 11776 12041
  (interval_append nodeTest 11520 11648 11776
  (interval_append nodeTest 11520 11584 11648
  bulkNodes11520
  bulkNodes11584)
  (interval_append nodeTest 11648 11712 11776
  bulkNodes11648
  bulkNodes11712))
  (interval_append nodeTest 11776 11904 12041
  (interval_append nodeTest 11776 11840 11904
  bulkNodes11776
  bulkNodes11840)
  (interval_append nodeTest 11904 11968 12041
  bulkNodes11904
  (interval_append nodeTest 11968 12032 12041
  bulkNodes11968
  bulkNodes12032))))
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0869
