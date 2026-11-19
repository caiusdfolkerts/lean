module
prelude
public import SharedSmallGraphData

@[expose] public section
namespace Papers.RationalityTen.SharedSmallGraph
open Papers.RationalityTen
open ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming GrowthBitsets
open BatchedGrowthPruning GraphGrowthConstraints FiniteChecks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem cells_005_b1280 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1280 1288 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1280 8 (by decide +kernel)

theorem cells_005_b1288 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1288 1296 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1288 8 (by decide +kernel)

theorem cells_005_b1296 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1296 1304 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1296 8 (by decide +kernel)

theorem cells_005_b1304 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1304 1312 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1304 8 (by decide +kernel)

theorem cells_005_b1312 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1312 1320 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1312 8 (by decide +kernel)

theorem cells_005_b1320 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1320 1328 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1320 8 (by decide +kernel)

theorem cells_005_b1328 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1328 1336 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1328 8 (by decide +kernel)

theorem cells_005_b1336 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1336 1344 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1336 8 (by decide +kernel)

theorem cells_005_b1344 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1344 1352 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1344 8 (by decide +kernel)

theorem cells_005_b1352 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1352 1360 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1352 8 (by decide +kernel)

theorem cells_005_b1360 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1360 1368 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1360 8 (by decide +kernel)

theorem cells_005_b1368 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1368 1376 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1368 8 (by decide +kernel)

theorem cells_005_b1376 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1376 1384 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1376 8 (by decide +kernel)

theorem cells_005_b1384 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1384 1392 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1384 8 (by decide +kernel)

theorem cells_005_b1392 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1392 1400 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1392 8 (by decide +kernel)

theorem cells_005_b1400 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1400 1408 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1400 8 (by decide +kernel)

theorem cells_005_b1408 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1408 1416 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1408 8 (by decide +kernel)

theorem cells_005_b1416 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1416 1424 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1416 8 (by decide +kernel)

theorem cells_005_b1424 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1424 1432 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1424 8 (by decide +kernel)

theorem cells_005_b1432 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1432 1440 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1432 8 (by decide +kernel)

theorem cells_005_b1440 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1440 1448 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1440 8 (by decide +kernel)

theorem cells_005_b1448 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1448 1456 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1448 8 (by decide +kernel)

theorem cells_005_b1456 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1456 1464 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1456 8 (by decide +kernel)

theorem cells_005_b1464 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1464 1472 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1464 8 (by decide +kernel)

theorem cells_005_b1472 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1472 1480 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1472 8 (by decide +kernel)

theorem cells_005_b1480 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1480 1488 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1480 8 (by decide +kernel)

theorem cells_005_b1488 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1488 1496 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1488 8 (by decide +kernel)

theorem cells_005_b1496 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1496 1504 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1496 8 (by decide +kernel)

theorem cells_005_b1504 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1504 1512 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1504 8 (by decide +kernel)

theorem cells_005_b1512 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1512 1520 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1512 8 (by decide +kernel)

theorem cells_005_b1520 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1520 1528 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1520 8 (by decide +kernel)

theorem cells_005_b1528 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1528 1536 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1528 8 (by decide +kernel)

theorem cells_005 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1280 1536 :=
  (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1280 1408 1536
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1280 1344 1408
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1280 1312 1344
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1280 1296 1312
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1280 1288 1296
 cells_005_b1280
 cells_005_b1288)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1296 1304 1312
 cells_005_b1296
 cells_005_b1304))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1312 1328 1344
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1312 1320 1328
 cells_005_b1312
 cells_005_b1320)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1328 1336 1344
 cells_005_b1328
 cells_005_b1336)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1344 1376 1408
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1344 1360 1376
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1344 1352 1360
 cells_005_b1344
 cells_005_b1352)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1360 1368 1376
 cells_005_b1360
 cells_005_b1368))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1376 1392 1408
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1376 1384 1392
 cells_005_b1376
 cells_005_b1384)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1392 1400 1408
 cells_005_b1392
 cells_005_b1400))))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1408 1472 1536
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1408 1440 1472
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1408 1424 1440
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1408 1416 1424
 cells_005_b1408
 cells_005_b1416)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1424 1432 1440
 cells_005_b1424
 cells_005_b1432))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1440 1456 1472
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1440 1448 1456
 cells_005_b1440
 cells_005_b1448)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1456 1464 1472
 cells_005_b1456
 cells_005_b1464)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1472 1504 1536
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1472 1488 1504
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1472 1480 1488
 cells_005_b1472
 cells_005_b1480)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1488 1496 1504
 cells_005_b1488
 cells_005_b1496))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1504 1520 1536
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1504 1512 1520
 cells_005_b1504
 cells_005_b1512)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1520 1528 1536
 cells_005_b1520
 cells_005_b1528)))))
end Papers.RationalityTen.SharedSmallGraph
