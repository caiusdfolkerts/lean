module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedBulk
public import RootedSubsumedForest0740Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0740
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem bulkNodes0 : Interval nodeTest 0 64 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    0 64 (by decide +kernel)
theorem bulkNodes64 : Interval nodeTest 64 128 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    64 64 (by decide +kernel)
theorem bulkNodes128 : Interval nodeTest 128 192 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    128 64 (by decide +kernel)
theorem bulkNodes192 : Interval nodeTest 192 256 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    192 64 (by decide +kernel)
theorem bulkNodes256 : Interval nodeTest 256 320 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    256 64 (by decide +kernel)
theorem bulkNodes320 : Interval nodeTest 320 384 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    320 64 (by decide +kernel)
theorem bulkNodes384 : Interval nodeTest 384 448 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    384 64 (by decide +kernel)
theorem bulkNodes448 : Interval nodeTest 448 512 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    448 64 (by decide +kernel)
theorem bulkNodes512 : Interval nodeTest 512 576 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    512 64 (by decide +kernel)
theorem bulkNodes576 : Interval nodeTest 576 640 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    576 64 (by decide +kernel)
theorem nodeInterval0 : Interval nodeTest 0 640 :=
  (interval_append nodeTest 0 320 640
  (interval_append nodeTest 0 128 320
  (interval_append nodeTest 0 64 128
  bulkNodes0
  bulkNodes64)
  (interval_append nodeTest 128 192 320
  bulkNodes128
  (interval_append nodeTest 192 256 320
  bulkNodes192
  bulkNodes256)))
  (interval_append nodeTest 320 448 640
  (interval_append nodeTest 320 384 448
  bulkNodes320
  bulkNodes384)
  (interval_append nodeTest 448 512 640
  bulkNodes448
  (interval_append nodeTest 512 576 640
  bulkNodes512
  bulkNodes576))))
theorem bulkNodes640 : Interval nodeTest 640 704 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    640 64 (by decide +kernel)
theorem bulkNodes704 : Interval nodeTest 704 768 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    704 64 (by decide +kernel)
theorem bulkNodes768 : Interval nodeTest 768 832 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    768 64 (by decide +kernel)
theorem bulkNodes832 : Interval nodeTest 832 896 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    832 64 (by decide +kernel)
theorem bulkNodes896 : Interval nodeTest 896 960 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    896 64 (by decide +kernel)
theorem bulkNodes960 : Interval nodeTest 960 1024 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    960 64 (by decide +kernel)
theorem bulkNodes1024 : Interval nodeTest 1024 1088 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    1024 64 (by decide +kernel)
theorem bulkNodes1088 : Interval nodeTest 1088 1152 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    1088 64 (by decide +kernel)
theorem bulkNodes1152 : Interval nodeTest 1152 1216 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    1152 64 (by decide +kernel)
theorem bulkNodes1216 : Interval nodeTest 1216 1280 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    1216 64 (by decide +kernel)
theorem nodeInterval640 : Interval nodeTest 640 1280 :=
  (interval_append nodeTest 640 960 1280
  (interval_append nodeTest 640 768 960
  (interval_append nodeTest 640 704 768
  bulkNodes640
  bulkNodes704)
  (interval_append nodeTest 768 832 960
  bulkNodes768
  (interval_append nodeTest 832 896 960
  bulkNodes832
  bulkNodes896)))
  (interval_append nodeTest 960 1088 1280
  (interval_append nodeTest 960 1024 1088
  bulkNodes960
  bulkNodes1024)
  (interval_append nodeTest 1088 1152 1280
  bulkNodes1088
  (interval_append nodeTest 1152 1216 1280
  bulkNodes1152
  bulkNodes1216))))
theorem bulkNodes1280 : Interval nodeTest 1280 1344 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    1280 64 (by decide +kernel)
theorem bulkNodes1344 : Interval nodeTest 1344 1408 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    1344 64 (by decide +kernel)
theorem bulkNodes1408 : Interval nodeTest 1408 1472 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    1408 64 (by decide +kernel)
theorem bulkNodes1472 : Interval nodeTest 1472 1536 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    1472 64 (by decide +kernel)
theorem bulkNodes1536 : Interval nodeTest 1536 1600 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    1536 64 (by decide +kernel)
theorem bulkNodes1600 : Interval nodeTest 1600 1664 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    1600 64 (by decide +kernel)
theorem bulkNodes1664 : Interval nodeTest 1664 1728 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    1664 64 (by decide +kernel)
theorem bulkNodes1728 : Interval nodeTest 1728 1792 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    1728 64 (by decide +kernel)
theorem bulkNodes1792 : Interval nodeTest 1792 1856 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    1792 64 (by decide +kernel)
theorem bulkNodes1856 : Interval nodeTest 1856 1920 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    1856 64 (by decide +kernel)
theorem nodeInterval1280 : Interval nodeTest 1280 1920 :=
  (interval_append nodeTest 1280 1600 1920
  (interval_append nodeTest 1280 1408 1600
  (interval_append nodeTest 1280 1344 1408
  bulkNodes1280
  bulkNodes1344)
  (interval_append nodeTest 1408 1472 1600
  bulkNodes1408
  (interval_append nodeTest 1472 1536 1600
  bulkNodes1472
  bulkNodes1536)))
  (interval_append nodeTest 1600 1728 1920
  (interval_append nodeTest 1600 1664 1728
  bulkNodes1600
  bulkNodes1664)
  (interval_append nodeTest 1728 1792 1920
  bulkNodes1728
  (interval_append nodeTest 1792 1856 1920
  bulkNodes1792
  bulkNodes1856))))
theorem bulkNodes1920 : Interval nodeTest 1920 1984 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    1920 64 (by decide +kernel)
theorem bulkNodes1984 : Interval nodeTest 1984 2048 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    1984 64 (by decide +kernel)
theorem bulkNodes2048 : Interval nodeTest 2048 2112 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    2048 64 (by decide +kernel)
theorem bulkNodes2112 : Interval nodeTest 2112 2176 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    2112 64 (by decide +kernel)
theorem bulkNodes2176 : Interval nodeTest 2176 2240 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    2176 64 (by decide +kernel)
theorem bulkNodes2240 : Interval nodeTest 2240 2304 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    2240 64 (by decide +kernel)
theorem bulkNodes2304 : Interval nodeTest 2304 2368 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    2304 64 (by decide +kernel)
theorem bulkNodes2368 : Interval nodeTest 2368 2432 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    2368 64 (by decide +kernel)
theorem bulkNodes2432 : Interval nodeTest 2432 2496 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    2432 64 (by decide +kernel)
theorem bulkNodes2496 : Interval nodeTest 2496 2560 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    2496 64 (by decide +kernel)
theorem nodeInterval1920 : Interval nodeTest 1920 2560 :=
  (interval_append nodeTest 1920 2240 2560
  (interval_append nodeTest 1920 2048 2240
  (interval_append nodeTest 1920 1984 2048
  bulkNodes1920
  bulkNodes1984)
  (interval_append nodeTest 2048 2112 2240
  bulkNodes2048
  (interval_append nodeTest 2112 2176 2240
  bulkNodes2112
  bulkNodes2176)))
  (interval_append nodeTest 2240 2368 2560
  (interval_append nodeTest 2240 2304 2368
  bulkNodes2240
  bulkNodes2304)
  (interval_append nodeTest 2368 2432 2560
  bulkNodes2368
  (interval_append nodeTest 2432 2496 2560
  bulkNodes2432
  bulkNodes2496))))
theorem bulkNodes2560 : Interval nodeTest 2560 2624 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    2560 64 (by decide +kernel)
theorem bulkNodes2624 : Interval nodeTest 2624 2688 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    2624 64 (by decide +kernel)
theorem bulkNodes2688 : Interval nodeTest 2688 2752 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    2688 64 (by decide +kernel)
theorem bulkNodes2752 : Interval nodeTest 2752 2816 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    2752 64 (by decide +kernel)
theorem bulkNodes2816 : Interval nodeTest 2816 2880 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    2816 64 (by decide +kernel)
theorem bulkNodes2880 : Interval nodeTest 2880 2944 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    2880 64 (by decide +kernel)
theorem bulkNodes2944 : Interval nodeTest 2944 3008 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    2944 64 (by decide +kernel)
theorem bulkNodes3008 : Interval nodeTest 3008 3072 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    3008 64 (by decide +kernel)
theorem bulkNodes3072 : Interval nodeTest 3072 3136 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    3072 64 (by decide +kernel)
theorem bulkNodes3136 : Interval nodeTest 3136 3200 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    3136 64 (by decide +kernel)
theorem nodeInterval2560 : Interval nodeTest 2560 3200 :=
  (interval_append nodeTest 2560 2880 3200
  (interval_append nodeTest 2560 2688 2880
  (interval_append nodeTest 2560 2624 2688
  bulkNodes2560
  bulkNodes2624)
  (interval_append nodeTest 2688 2752 2880
  bulkNodes2688
  (interval_append nodeTest 2752 2816 2880
  bulkNodes2752
  bulkNodes2816)))
  (interval_append nodeTest 2880 3008 3200
  (interval_append nodeTest 2880 2944 3008
  bulkNodes2880
  bulkNodes2944)
  (interval_append nodeTest 3008 3072 3200
  bulkNodes3008
  (interval_append nodeTest 3072 3136 3200
  bulkNodes3072
  bulkNodes3136))))
theorem bulkNodes3200 : Interval nodeTest 3200 3264 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    3200 64 (by decide +kernel)
theorem bulkNodes3264 : Interval nodeTest 3264 3328 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    3264 64 (by decide +kernel)
theorem bulkNodes3328 : Interval nodeTest 3328 3392 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    3328 64 (by decide +kernel)
theorem bulkNodes3392 : Interval nodeTest 3392 3456 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    3392 64 (by decide +kernel)
theorem bulkNodes3456 : Interval nodeTest 3456 3520 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    3456 64 (by decide +kernel)
theorem bulkNodes3520 : Interval nodeTest 3520 3584 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    3520 64 (by decide +kernel)
theorem bulkNodes3584 : Interval nodeTest 3584 3648 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    3584 64 (by decide +kernel)
theorem bulkNodes3648 : Interval nodeTest 3648 3712 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    3648 64 (by decide +kernel)
theorem bulkNodes3712 : Interval nodeTest 3712 3776 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    3712 64 (by decide +kernel)
theorem bulkNodes3776 : Interval nodeTest 3776 3840 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    3776 64 (by decide +kernel)
theorem nodeInterval3200 : Interval nodeTest 3200 3840 :=
  (interval_append nodeTest 3200 3520 3840
  (interval_append nodeTest 3200 3328 3520
  (interval_append nodeTest 3200 3264 3328
  bulkNodes3200
  bulkNodes3264)
  (interval_append nodeTest 3328 3392 3520
  bulkNodes3328
  (interval_append nodeTest 3392 3456 3520
  bulkNodes3392
  bulkNodes3456)))
  (interval_append nodeTest 3520 3648 3840
  (interval_append nodeTest 3520 3584 3648
  bulkNodes3520
  bulkNodes3584)
  (interval_append nodeTest 3648 3712 3840
  bulkNodes3648
  (interval_append nodeTest 3712 3776 3840
  bulkNodes3712
  bulkNodes3776))))
theorem bulkNodes3840 : Interval nodeTest 3840 3904 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    3840 64 (by decide +kernel)
theorem bulkNodes3904 : Interval nodeTest 3904 3968 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    3904 64 (by decide +kernel)
theorem bulkNodes3968 : Interval nodeTest 3968 4032 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    3968 64 (by decide +kernel)
theorem bulkNodes4032 : Interval nodeTest 4032 4096 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    4032 64 (by decide +kernel)
theorem bulkNodes4096 : Interval nodeTest 4096 4160 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    4096 64 (by decide +kernel)
theorem bulkNodes4160 : Interval nodeTest 4160 4224 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    4160 64 (by decide +kernel)
theorem bulkNodes4224 : Interval nodeTest 4224 4288 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    4224 64 (by decide +kernel)
theorem bulkNodes4288 : Interval nodeTest 4288 4352 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    4288 64 (by decide +kernel)
theorem bulkNodes4352 : Interval nodeTest 4352 4416 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    4352 64 (by decide +kernel)
theorem bulkNodes4416 : Interval nodeTest 4416 4480 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    4416 64 (by decide +kernel)
theorem nodeInterval3840 : Interval nodeTest 3840 4480 :=
  (interval_append nodeTest 3840 4160 4480
  (interval_append nodeTest 3840 3968 4160
  (interval_append nodeTest 3840 3904 3968
  bulkNodes3840
  bulkNodes3904)
  (interval_append nodeTest 3968 4032 4160
  bulkNodes3968
  (interval_append nodeTest 4032 4096 4160
  bulkNodes4032
  bulkNodes4096)))
  (interval_append nodeTest 4160 4288 4480
  (interval_append nodeTest 4160 4224 4288
  bulkNodes4160
  bulkNodes4224)
  (interval_append nodeTest 4288 4352 4480
  bulkNodes4288
  (interval_append nodeTest 4352 4416 4480
  bulkNodes4352
  bulkNodes4416))))
theorem bulkNodes4480 : Interval nodeTest 4480 4544 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    4480 64 (by decide +kernel)
theorem bulkNodes4544 : Interval nodeTest 4544 4608 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    4544 64 (by decide +kernel)
theorem bulkNodes4608 : Interval nodeTest 4608 4672 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    4608 64 (by decide +kernel)
theorem bulkNodes4672 : Interval nodeTest 4672 4736 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    4672 64 (by decide +kernel)
theorem bulkNodes4736 : Interval nodeTest 4736 4800 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    4736 64 (by decide +kernel)
theorem bulkNodes4800 : Interval nodeTest 4800 4864 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    4800 64 (by decide +kernel)
theorem bulkNodes4864 : Interval nodeTest 4864 4928 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    4864 64 (by decide +kernel)
theorem bulkNodes4928 : Interval nodeTest 4928 4992 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    4928 64 (by decide +kernel)
theorem bulkNodes4992 : Interval nodeTest 4992 5056 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    4992 64 (by decide +kernel)
theorem bulkNodes5056 : Interval nodeTest 5056 5120 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    5056 64 (by decide +kernel)
theorem nodeInterval4480 : Interval nodeTest 4480 5120 :=
  (interval_append nodeTest 4480 4800 5120
  (interval_append nodeTest 4480 4608 4800
  (interval_append nodeTest 4480 4544 4608
  bulkNodes4480
  bulkNodes4544)
  (interval_append nodeTest 4608 4672 4800
  bulkNodes4608
  (interval_append nodeTest 4672 4736 4800
  bulkNodes4672
  bulkNodes4736)))
  (interval_append nodeTest 4800 4928 5120
  (interval_append nodeTest 4800 4864 4928
  bulkNodes4800
  bulkNodes4864)
  (interval_append nodeTest 4928 4992 5120
  bulkNodes4928
  (interval_append nodeTest 4992 5056 5120
  bulkNodes4992
  bulkNodes5056))))
theorem bulkNodes5120 : Interval nodeTest 5120 5184 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    5120 64 (by decide +kernel)
theorem bulkNodes5184 : Interval nodeTest 5184 5248 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    5184 64 (by decide +kernel)
theorem bulkNodes5248 : Interval nodeTest 5248 5312 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    5248 64 (by decide +kernel)
theorem bulkNodes5312 : Interval nodeTest 5312 5376 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    5312 64 (by decide +kernel)
theorem bulkNodes5376 : Interval nodeTest 5376 5440 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    5376 64 (by decide +kernel)
theorem bulkNodes5440 : Interval nodeTest 5440 5504 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    5440 64 (by decide +kernel)
theorem bulkNodes5504 : Interval nodeTest 5504 5568 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    5504 64 (by decide +kernel)
theorem bulkNodes5568 : Interval nodeTest 5568 5632 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    5568 64 (by decide +kernel)
theorem bulkNodes5632 : Interval nodeTest 5632 5696 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    5632 64 (by decide +kernel)
theorem bulkNodes5696 : Interval nodeTest 5696 5760 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    5696 64 (by decide +kernel)
theorem nodeInterval5120 : Interval nodeTest 5120 5760 :=
  (interval_append nodeTest 5120 5440 5760
  (interval_append nodeTest 5120 5248 5440
  (interval_append nodeTest 5120 5184 5248
  bulkNodes5120
  bulkNodes5184)
  (interval_append nodeTest 5248 5312 5440
  bulkNodes5248
  (interval_append nodeTest 5312 5376 5440
  bulkNodes5312
  bulkNodes5376)))
  (interval_append nodeTest 5440 5568 5760
  (interval_append nodeTest 5440 5504 5568
  bulkNodes5440
  bulkNodes5504)
  (interval_append nodeTest 5568 5632 5760
  bulkNodes5568
  (interval_append nodeTest 5632 5696 5760
  bulkNodes5632
  bulkNodes5696))))
theorem bulkNodes5760 : Interval nodeTest 5760 5824 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    5760 64 (by decide +kernel)
theorem bulkNodes5824 : Interval nodeTest 5824 5888 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    5824 64 (by decide +kernel)
theorem bulkNodes5888 : Interval nodeTest 5888 5952 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    5888 64 (by decide +kernel)
theorem bulkNodes5952 : Interval nodeTest 5952 6016 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    5952 64 (by decide +kernel)
theorem bulkNodes6016 : Interval nodeTest 6016 6080 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    6016 64 (by decide +kernel)
theorem bulkNodes6080 : Interval nodeTest 6080 6144 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    6080 64 (by decide +kernel)
theorem bulkNodes6144 : Interval nodeTest 6144 6208 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    6144 64 (by decide +kernel)
theorem bulkNodes6208 : Interval nodeTest 6208 6272 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    6208 64 (by decide +kernel)
theorem bulkNodes6272 : Interval nodeTest 6272 6336 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    6272 64 (by decide +kernel)
theorem bulkNodes6336 : Interval nodeTest 6336 6400 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    6336 64 (by decide +kernel)
theorem nodeInterval5760 : Interval nodeTest 5760 6400 :=
  (interval_append nodeTest 5760 6080 6400
  (interval_append nodeTest 5760 5888 6080
  (interval_append nodeTest 5760 5824 5888
  bulkNodes5760
  bulkNodes5824)
  (interval_append nodeTest 5888 5952 6080
  bulkNodes5888
  (interval_append nodeTest 5952 6016 6080
  bulkNodes5952
  bulkNodes6016)))
  (interval_append nodeTest 6080 6208 6400
  (interval_append nodeTest 6080 6144 6208
  bulkNodes6080
  bulkNodes6144)
  (interval_append nodeTest 6208 6272 6400
  bulkNodes6208
  (interval_append nodeTest 6272 6336 6400
  bulkNodes6272
  bulkNodes6336))))
theorem bulkNodes6400 : Interval nodeTest 6400 6464 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    6400 64 (by decide +kernel)
theorem bulkNodes6464 : Interval nodeTest 6464 6528 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    6464 64 (by decide +kernel)
theorem bulkNodes6528 : Interval nodeTest 6528 6592 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    6528 64 (by decide +kernel)
theorem bulkNodes6592 : Interval nodeTest 6592 6656 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    6592 64 (by decide +kernel)
theorem bulkNodes6656 : Interval nodeTest 6656 6720 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    6656 64 (by decide +kernel)
theorem bulkNodes6720 : Interval nodeTest 6720 6784 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    6720 64 (by decide +kernel)
theorem bulkNodes6784 : Interval nodeTest 6784 6848 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    6784 64 (by decide +kernel)
theorem bulkNodes6848 : Interval nodeTest 6848 6912 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    6848 64 (by decide +kernel)
theorem bulkNodes6912 : Interval nodeTest 6912 6976 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    6912 64 (by decide +kernel)
theorem bulkNodes6976 : Interval nodeTest 6976 7040 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    6976 64 (by decide +kernel)
theorem nodeInterval6400 : Interval nodeTest 6400 7040 :=
  (interval_append nodeTest 6400 6720 7040
  (interval_append nodeTest 6400 6528 6720
  (interval_append nodeTest 6400 6464 6528
  bulkNodes6400
  bulkNodes6464)
  (interval_append nodeTest 6528 6592 6720
  bulkNodes6528
  (interval_append nodeTest 6592 6656 6720
  bulkNodes6592
  bulkNodes6656)))
  (interval_append nodeTest 6720 6848 7040
  (interval_append nodeTest 6720 6784 6848
  bulkNodes6720
  bulkNodes6784)
  (interval_append nodeTest 6848 6912 7040
  bulkNodes6848
  (interval_append nodeTest 6912 6976 7040
  bulkNodes6912
  bulkNodes6976))))
theorem bulkNodes7040 : Interval nodeTest 7040 7104 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    7040 64 (by decide +kernel)
theorem bulkNodes7104 : Interval nodeTest 7104 7168 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    7104 64 (by decide +kernel)
theorem bulkNodes7168 : Interval nodeTest 7168 7232 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    7168 64 (by decide +kernel)
theorem bulkNodes7232 : Interval nodeTest 7232 7296 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    7232 64 (by decide +kernel)
theorem bulkNodes7296 : Interval nodeTest 7296 7360 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    7296 64 (by decide +kernel)
theorem bulkNodes7360 : Interval nodeTest 7360 7424 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    7360 64 (by decide +kernel)
theorem bulkNodes7424 : Interval nodeTest 7424 7488 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    7424 64 (by decide +kernel)
theorem bulkNodes7488 : Interval nodeTest 7488 7552 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    7488 64 (by decide +kernel)
theorem bulkNodes7552 : Interval nodeTest 7552 7616 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    7552 64 (by decide +kernel)
theorem bulkNodes7616 : Interval nodeTest 7616 7680 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    7616 64 (by decide +kernel)
theorem nodeInterval7040 : Interval nodeTest 7040 7680 :=
  (interval_append nodeTest 7040 7360 7680
  (interval_append nodeTest 7040 7168 7360
  (interval_append nodeTest 7040 7104 7168
  bulkNodes7040
  bulkNodes7104)
  (interval_append nodeTest 7168 7232 7360
  bulkNodes7168
  (interval_append nodeTest 7232 7296 7360
  bulkNodes7232
  bulkNodes7296)))
  (interval_append nodeTest 7360 7488 7680
  (interval_append nodeTest 7360 7424 7488
  bulkNodes7360
  bulkNodes7424)
  (interval_append nodeTest 7488 7552 7680
  bulkNodes7488
  (interval_append nodeTest 7552 7616 7680
  bulkNodes7552
  bulkNodes7616))))
theorem bulkNodes7680 : Interval nodeTest 7680 7744 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    7680 64 (by decide +kernel)
theorem bulkNodes7744 : Interval nodeTest 7744 7808 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    7744 64 (by decide +kernel)
theorem bulkNodes7808 : Interval nodeTest 7808 7872 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    7808 64 (by decide +kernel)
theorem bulkNodes7872 : Interval nodeTest 7872 7936 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    7872 64 (by decide +kernel)
theorem bulkNodes7936 : Interval nodeTest 7936 8000 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    7936 64 (by decide +kernel)
theorem bulkNodes8000 : Interval nodeTest 8000 8064 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    8000 64 (by decide +kernel)
theorem bulkNodes8064 : Interval nodeTest 8064 8128 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    8064 64 (by decide +kernel)
theorem bulkNodes8128 : Interval nodeTest 8128 8192 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    8128 64 (by decide +kernel)
theorem bulkNodes8192 : Interval nodeTest 8192 8256 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    8192 64 (by decide +kernel)
theorem bulkNodes8256 : Interval nodeTest 8256 8320 :=
  RootedBulk.interval widths cellCount 1024 1152 leafCount nodeCount
    RootedCaches.RootedSixBase04.candidateMasks RootedCaches.RootedSixBase04.badMasks RootedCaches.RootedSixBase04.kindMasks
    RootedCaches.RootedSixBase04.keys RootedCaches.RootedSixBase04.fastKind quota FacetUniverses.RootedSixBase04.Generators.FastWords.rawMaps rawLeaves codes counters
    8256 64 (by decide +kernel)
theorem nodeInterval7680 : Interval nodeTest 7680 8320 :=
  (interval_append nodeTest 7680 8000 8320
  (interval_append nodeTest 7680 7808 8000
  (interval_append nodeTest 7680 7744 7808
  bulkNodes7680
  bulkNodes7744)
  (interval_append nodeTest 7808 7872 8000
  bulkNodes7808
  (interval_append nodeTest 7872 7936 8000
  bulkNodes7872
  bulkNodes7936)))
  (interval_append nodeTest 8000 8128 8320
  (interval_append nodeTest 8000 8064 8128
  bulkNodes8000
  bulkNodes8064)
  (interval_append nodeTest 8128 8192 8320
  bulkNodes8128
  (interval_append nodeTest 8192 8256 8320
  bulkNodes8192
  bulkNodes8256))))
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0740
