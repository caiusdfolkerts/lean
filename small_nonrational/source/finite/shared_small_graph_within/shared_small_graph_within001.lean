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
theorem within_001_b256 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 256 264 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 256 8 (by decide +kernel)

theorem within_001_b264 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 264 272 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 264 8 (by decide +kernel)

theorem within_001_b272 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 272 280 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 272 8 (by decide +kernel)

theorem within_001_b280 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 280 288 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 280 8 (by decide +kernel)

theorem within_001_b288 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 288 296 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 288 8 (by decide +kernel)

theorem within_001_b296 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 296 304 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 296 8 (by decide +kernel)

theorem within_001_b304 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 304 312 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 304 8 (by decide +kernel)

theorem within_001_b312 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 312 320 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 312 8 (by decide +kernel)

theorem within_001_b320 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 320 328 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 320 8 (by decide +kernel)

theorem within_001_b328 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 328 336 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 328 8 (by decide +kernel)

theorem within_001_b336 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 336 344 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 336 8 (by decide +kernel)

theorem within_001_b344 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 344 352 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 344 8 (by decide +kernel)

theorem within_001_b352 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 352 360 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 352 8 (by decide +kernel)

theorem within_001_b360 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 360 368 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 360 8 (by decide +kernel)

theorem within_001_b368 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 368 376 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 368 8 (by decide +kernel)

theorem within_001_b376 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 376 384 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 376 8 (by decide +kernel)

theorem within_001_b384 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 384 392 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 384 8 (by decide +kernel)

theorem within_001_b392 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 392 400 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 392 8 (by decide +kernel)

theorem within_001_b400 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 400 408 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 400 8 (by decide +kernel)

theorem within_001_b408 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 408 416 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 408 8 (by decide +kernel)

theorem within_001_b416 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 416 424 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 416 8 (by decide +kernel)

theorem within_001_b424 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 424 432 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 424 8 (by decide +kernel)

theorem within_001_b432 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 432 440 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 432 8 (by decide +kernel)

theorem within_001_b440 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 440 448 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 440 8 (by decide +kernel)

theorem within_001_b448 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 448 456 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 448 8 (by decide +kernel)

theorem within_001_b456 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 456 464 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 456 8 (by decide +kernel)

theorem within_001_b464 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 464 472 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 464 8 (by decide +kernel)

theorem within_001_b472 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 472 480 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 472 8 (by decide +kernel)

theorem within_001_b480 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 480 488 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 480 8 (by decide +kernel)

theorem within_001_b488 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 488 496 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 488 8 (by decide +kernel)

theorem within_001_b496 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 496 504 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 496 8 (by decide +kernel)

theorem within_001_b504 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 504 512 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 504 8 (by decide +kernel)

theorem within_001 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 256 512 :=
  (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 256 384 512
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 256 320 384
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 256 288 320
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 256 272 288
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 256 264 272
 within_001_b256
 within_001_b264)
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 272 280 288
 within_001_b272
 within_001_b280))
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 288 304 320
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 288 296 304
 within_001_b288
 within_001_b296)
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 304 312 320
 within_001_b304
 within_001_b312)))
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 320 352 384
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 320 336 352
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 320 328 336
 within_001_b320
 within_001_b328)
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 336 344 352
 within_001_b336
 within_001_b344))
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 352 368 384
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 352 360 368
 within_001_b352
 within_001_b360)
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 368 376 384
 within_001_b368
 within_001_b376))))
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 384 448 512
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 384 416 448
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 384 400 416
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 384 392 400
 within_001_b384
 within_001_b392)
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 400 408 416
 within_001_b400
 within_001_b408))
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 416 432 448
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 416 424 432
 within_001_b416
 within_001_b424)
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 432 440 448
 within_001_b432
 within_001_b440)))
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 448 480 512
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 448 464 480
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 448 456 464
 within_001_b448
 within_001_b456)
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 464 472 480
 within_001_b464
 within_001_b472))
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 480 496 512
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 480 488 496
 within_001_b480
 within_001_b488)
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 496 504 512
 within_001_b496
 within_001_b504)))))
end Papers.RationalityTen.SharedSmallGraph
