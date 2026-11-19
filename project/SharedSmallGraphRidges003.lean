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
theorem ridges_003_b384 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 384 388 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 384 4 (by decide +kernel)

theorem ridges_003_b388 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 388 392 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 388 4 (by decide +kernel)

theorem ridges_003_b392 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 392 396 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 392 4 (by decide +kernel)

theorem ridges_003_b396 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 396 400 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 396 4 (by decide +kernel)

theorem ridges_003_b400 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 400 404 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 400 4 (by decide +kernel)

theorem ridges_003_b404 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 404 408 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 404 4 (by decide +kernel)

theorem ridges_003_b408 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 408 412 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 408 4 (by decide +kernel)

theorem ridges_003_b412 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 412 416 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 412 4 (by decide +kernel)

theorem ridges_003_b416 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 416 420 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 416 4 (by decide +kernel)

theorem ridges_003_b420 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 420 424 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 420 4 (by decide +kernel)

theorem ridges_003_b424 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 424 428 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 424 4 (by decide +kernel)

theorem ridges_003_b428 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 428 432 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 428 4 (by decide +kernel)

theorem ridges_003_b432 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 432 436 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 432 4 (by decide +kernel)

theorem ridges_003_b436 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 436 440 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 436 4 (by decide +kernel)

theorem ridges_003_b440 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 440 444 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 440 4 (by decide +kernel)

theorem ridges_003_b444 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 444 448 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 444 4 (by decide +kernel)

theorem ridges_003_b448 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 448 452 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 448 4 (by decide +kernel)

theorem ridges_003_b452 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 452 456 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 452 4 (by decide +kernel)

theorem ridges_003_b456 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 456 460 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 456 4 (by decide +kernel)

theorem ridges_003_b460 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 460 464 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 460 4 (by decide +kernel)

theorem ridges_003_b464 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 464 468 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 464 4 (by decide +kernel)

theorem ridges_003_b468 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 468 472 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 468 4 (by decide +kernel)

theorem ridges_003_b472 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 472 476 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 472 4 (by decide +kernel)

theorem ridges_003_b476 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 476 480 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 476 4 (by decide +kernel)

theorem ridges_003_b480 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 480 484 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 480 4 (by decide +kernel)

theorem ridges_003_b484 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 484 488 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 484 4 (by decide +kernel)

theorem ridges_003_b488 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 488 492 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 488 4 (by decide +kernel)

theorem ridges_003_b492 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 492 496 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 492 4 (by decide +kernel)

theorem ridges_003_b496 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 496 500 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 496 4 (by decide +kernel)

theorem ridges_003_b500 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 500 504 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 500 4 (by decide +kernel)

theorem ridges_003_b504 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 504 508 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 504 4 (by decide +kernel)

theorem ridges_003_b508 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 508 512 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 508 4 (by decide +kernel)

theorem ridges_003 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 384 512 :=
  (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 384 448 512
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 384 416 448
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 384 400 416
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 384 392 400
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 384 388 392
 ridges_003_b384
 ridges_003_b388)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 392 396 400
 ridges_003_b392
 ridges_003_b396))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 400 408 416
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 400 404 408
 ridges_003_b400
 ridges_003_b404)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 408 412 416
 ridges_003_b408
 ridges_003_b412)))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 416 432 448
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 416 424 432
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 416 420 424
 ridges_003_b416
 ridges_003_b420)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 424 428 432
 ridges_003_b424
 ridges_003_b428))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 432 440 448
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 432 436 440
 ridges_003_b432
 ridges_003_b436)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 440 444 448
 ridges_003_b440
 ridges_003_b444))))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 448 480 512
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 448 464 480
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 448 456 464
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 448 452 456
 ridges_003_b448
 ridges_003_b452)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 456 460 464
 ridges_003_b456
 ridges_003_b460))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 464 472 480
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 464 468 472
 ridges_003_b464
 ridges_003_b468)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 472 476 480
 ridges_003_b472
 ridges_003_b476)))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 480 496 512
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 480 488 496
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 480 484 488
 ridges_003_b480
 ridges_003_b484)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 488 492 496
 ridges_003_b488
 ridges_003_b492))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 496 504 512
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 496 500 504
 ridges_003_b496
 ridges_003_b500)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 504 508 512
 ridges_003_b504
 ridges_003_b508)))))
end Papers.RationalityTen.SharedSmallGraph
