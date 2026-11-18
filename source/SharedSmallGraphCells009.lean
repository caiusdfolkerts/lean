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
theorem cells_009_b2304 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2304 2312 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2304 8 (by decide +kernel)

theorem cells_009_b2312 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2312 2320 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2312 8 (by decide +kernel)

theorem cells_009_b2320 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2320 2328 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2320 8 (by decide +kernel)

theorem cells_009_b2328 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2328 2336 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2328 8 (by decide +kernel)

theorem cells_009_b2336 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2336 2344 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2336 8 (by decide +kernel)

theorem cells_009_b2344 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2344 2352 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2344 8 (by decide +kernel)

theorem cells_009_b2352 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2352 2360 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2352 8 (by decide +kernel)

theorem cells_009_b2360 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2360 2368 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2360 8 (by decide +kernel)

theorem cells_009_b2368 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2368 2376 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2368 8 (by decide +kernel)

theorem cells_009_b2376 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2376 2384 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2376 8 (by decide +kernel)

theorem cells_009_b2384 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2384 2392 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2384 8 (by decide +kernel)

theorem cells_009_b2392 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2392 2400 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2392 8 (by decide +kernel)

theorem cells_009_b2400 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2400 2408 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2400 8 (by decide +kernel)

theorem cells_009_b2408 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2408 2416 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2408 8 (by decide +kernel)

theorem cells_009_b2416 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2416 2424 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2416 8 (by decide +kernel)

theorem cells_009_b2424 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2424 2432 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2424 8 (by decide +kernel)

theorem cells_009_b2432 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2432 2440 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2432 8 (by decide +kernel)

theorem cells_009_b2440 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2440 2448 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2440 8 (by decide +kernel)

theorem cells_009_b2448 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2448 2456 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2448 8 (by decide +kernel)

theorem cells_009_b2456 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2456 2464 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2456 8 (by decide +kernel)

theorem cells_009_b2464 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2464 2472 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2464 8 (by decide +kernel)

theorem cells_009_b2472 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2472 2480 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2472 8 (by decide +kernel)

theorem cells_009_b2480 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2480 2488 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2480 8 (by decide +kernel)

theorem cells_009_b2488 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2488 2496 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2488 8 (by decide +kernel)

theorem cells_009_b2496 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2496 2504 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2496 8 (by decide +kernel)

theorem cells_009_b2504 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2504 2512 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2504 8 (by decide +kernel)

theorem cells_009_b2512 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2512 2520 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2512 8 (by decide +kernel)

theorem cells_009_b2520 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2520 2528 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2520 8 (by decide +kernel)

theorem cells_009_b2528 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2528 2536 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2528 8 (by decide +kernel)

theorem cells_009_b2536 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2536 2544 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2536 8 (by decide +kernel)

theorem cells_009_b2544 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2544 2552 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2544 8 (by decide +kernel)

theorem cells_009_b2552 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2552 2560 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2552 8 (by decide +kernel)

theorem cells_009 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2304 2560 :=
  (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2304 2432 2560
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2304 2368 2432
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2304 2336 2368
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2304 2320 2336
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2304 2312 2320
 cells_009_b2304
 cells_009_b2312)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2320 2328 2336
 cells_009_b2320
 cells_009_b2328))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2336 2352 2368
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2336 2344 2352
 cells_009_b2336
 cells_009_b2344)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2352 2360 2368
 cells_009_b2352
 cells_009_b2360)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2368 2400 2432
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2368 2384 2400
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2368 2376 2384
 cells_009_b2368
 cells_009_b2376)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2384 2392 2400
 cells_009_b2384
 cells_009_b2392))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2400 2416 2432
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2400 2408 2416
 cells_009_b2400
 cells_009_b2408)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2416 2424 2432
 cells_009_b2416
 cells_009_b2424))))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2432 2496 2560
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2432 2464 2496
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2432 2448 2464
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2432 2440 2448
 cells_009_b2432
 cells_009_b2440)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2448 2456 2464
 cells_009_b2448
 cells_009_b2456))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2464 2480 2496
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2464 2472 2480
 cells_009_b2464
 cells_009_b2472)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2480 2488 2496
 cells_009_b2480
 cells_009_b2488)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2496 2528 2560
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2496 2512 2528
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2496 2504 2512
 cells_009_b2496
 cells_009_b2504)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2512 2520 2528
 cells_009_b2512
 cells_009_b2520))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2528 2544 2560
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2528 2536 2544
 cells_009_b2528
 cells_009_b2536)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2544 2552 2560
 cells_009_b2544
 cells_009_b2552)))))
end Papers.RationalityTen.SharedSmallGraph
