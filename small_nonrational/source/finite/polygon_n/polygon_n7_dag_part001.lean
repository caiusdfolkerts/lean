module
prelude
public import PolygonN7DAGTests

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.PolygonGrowth.N7
open Papers.RationalityTen GrowthDAG SparseGrowthDAG GrowthPruning FiniteChecks

theorem nodes_part001_00256 : FiniteChecks.Interval nodeTest 256 264 :=
  FiniteChecks.interval_of_check nodeTest 256 8 (by decide +kernel)

theorem nodes_part001_00264 : FiniteChecks.Interval nodeTest 264 272 :=
  FiniteChecks.interval_of_check nodeTest 264 8 (by decide +kernel)

theorem nodes_part001_00272 : FiniteChecks.Interval nodeTest 272 280 :=
  FiniteChecks.interval_of_check nodeTest 272 8 (by decide +kernel)

theorem nodes_part001_00280 : FiniteChecks.Interval nodeTest 280 288 :=
  FiniteChecks.interval_of_check nodeTest 280 8 (by decide +kernel)

theorem nodes_part001_00288 : FiniteChecks.Interval nodeTest 288 296 :=
  FiniteChecks.interval_of_check nodeTest 288 8 (by decide +kernel)

theorem nodes_part001_00296 : FiniteChecks.Interval nodeTest 296 304 :=
  FiniteChecks.interval_of_check nodeTest 296 8 (by decide +kernel)

theorem nodes_part001_00304 : FiniteChecks.Interval nodeTest 304 312 :=
  FiniteChecks.interval_of_check nodeTest 304 8 (by decide +kernel)

theorem nodes_part001_00312 : FiniteChecks.Interval nodeTest 312 320 :=
  FiniteChecks.interval_of_check nodeTest 312 8 (by decide +kernel)

theorem nodes_part001_00320 : FiniteChecks.Interval nodeTest 320 328 :=
  FiniteChecks.interval_of_check nodeTest 320 8 (by decide +kernel)

theorem nodes_part001_00328 : FiniteChecks.Interval nodeTest 328 336 :=
  FiniteChecks.interval_of_check nodeTest 328 8 (by decide +kernel)

theorem nodes_part001_00336 : FiniteChecks.Interval nodeTest 336 344 :=
  FiniteChecks.interval_of_check nodeTest 336 8 (by decide +kernel)

theorem nodes_part001_00344 : FiniteChecks.Interval nodeTest 344 352 :=
  FiniteChecks.interval_of_check nodeTest 344 8 (by decide +kernel)

theorem nodes_part001_00352 : FiniteChecks.Interval nodeTest 352 360 :=
  FiniteChecks.interval_of_check nodeTest 352 8 (by decide +kernel)

theorem nodes_part001_00360 : FiniteChecks.Interval nodeTest 360 368 :=
  FiniteChecks.interval_of_check nodeTest 360 8 (by decide +kernel)

theorem nodes_part001_00368 : FiniteChecks.Interval nodeTest 368 376 :=
  FiniteChecks.interval_of_check nodeTest 368 8 (by decide +kernel)

theorem nodes_part001_00376 : FiniteChecks.Interval nodeTest 376 384 :=
  FiniteChecks.interval_of_check nodeTest 376 8 (by decide +kernel)

theorem nodes_part001_00384 : FiniteChecks.Interval nodeTest 384 392 :=
  FiniteChecks.interval_of_check nodeTest 384 8 (by decide +kernel)

theorem nodes_part001_00392 : FiniteChecks.Interval nodeTest 392 400 :=
  FiniteChecks.interval_of_check nodeTest 392 8 (by decide +kernel)

theorem nodes_part001_00400 : FiniteChecks.Interval nodeTest 400 408 :=
  FiniteChecks.interval_of_check nodeTest 400 8 (by decide +kernel)

theorem nodes_part001_00408 : FiniteChecks.Interval nodeTest 408 416 :=
  FiniteChecks.interval_of_check nodeTest 408 8 (by decide +kernel)

theorem nodes_part001_00416 : FiniteChecks.Interval nodeTest 416 424 :=
  FiniteChecks.interval_of_check nodeTest 416 8 (by decide +kernel)

theorem nodes_part001_00424 : FiniteChecks.Interval nodeTest 424 432 :=
  FiniteChecks.interval_of_check nodeTest 424 8 (by decide +kernel)

theorem nodes_part001_00432 : FiniteChecks.Interval nodeTest 432 440 :=
  FiniteChecks.interval_of_check nodeTest 432 8 (by decide +kernel)

theorem nodes_part001_00440 : FiniteChecks.Interval nodeTest 440 448 :=
  FiniteChecks.interval_of_check nodeTest 440 8 (by decide +kernel)

theorem nodes_part001_00448 : FiniteChecks.Interval nodeTest 448 456 :=
  FiniteChecks.interval_of_check nodeTest 448 8 (by decide +kernel)

theorem nodes_part001_00456 : FiniteChecks.Interval nodeTest 456 464 :=
  FiniteChecks.interval_of_check nodeTest 456 8 (by decide +kernel)

theorem nodes_part001_00464 : FiniteChecks.Interval nodeTest 464 472 :=
  FiniteChecks.interval_of_check nodeTest 464 8 (by decide +kernel)

theorem nodes_part001_00472 : FiniteChecks.Interval nodeTest 472 480 :=
  FiniteChecks.interval_of_check nodeTest 472 8 (by decide +kernel)

theorem nodes_part001_00480 : FiniteChecks.Interval nodeTest 480 488 :=
  FiniteChecks.interval_of_check nodeTest 480 8 (by decide +kernel)

theorem nodes_part001_00488 : FiniteChecks.Interval nodeTest 488 496 :=
  FiniteChecks.interval_of_check nodeTest 488 8 (by decide +kernel)

theorem nodes_part001_00496 : FiniteChecks.Interval nodeTest 496 504 :=
  FiniteChecks.interval_of_check nodeTest 496 8 (by decide +kernel)

theorem nodes_part001_00504 : FiniteChecks.Interval nodeTest 504 512 :=
  FiniteChecks.interval_of_check nodeTest 504 8 (by decide +kernel)

theorem nodes_part001_join_00256_00272 : FiniteChecks.Interval nodeTest 256 272 :=
  FiniteChecks.interval_append nodeTest 256 264 272 nodes_part001_00256 nodes_part001_00264

theorem nodes_part001_join_00272_00288 : FiniteChecks.Interval nodeTest 272 288 :=
  FiniteChecks.interval_append nodeTest 272 280 288 nodes_part001_00272 nodes_part001_00280

theorem nodes_part001_join_00256_00288 : FiniteChecks.Interval nodeTest 256 288 :=
  FiniteChecks.interval_append nodeTest 256 272 288 nodes_part001_join_00256_00272 nodes_part001_join_00272_00288

theorem nodes_part001_join_00288_00304 : FiniteChecks.Interval nodeTest 288 304 :=
  FiniteChecks.interval_append nodeTest 288 296 304 nodes_part001_00288 nodes_part001_00296

theorem nodes_part001_join_00304_00320 : FiniteChecks.Interval nodeTest 304 320 :=
  FiniteChecks.interval_append nodeTest 304 312 320 nodes_part001_00304 nodes_part001_00312

theorem nodes_part001_join_00288_00320 : FiniteChecks.Interval nodeTest 288 320 :=
  FiniteChecks.interval_append nodeTest 288 304 320 nodes_part001_join_00288_00304 nodes_part001_join_00304_00320

theorem nodes_part001_join_00256_00320 : FiniteChecks.Interval nodeTest 256 320 :=
  FiniteChecks.interval_append nodeTest 256 288 320 nodes_part001_join_00256_00288 nodes_part001_join_00288_00320

theorem nodes_part001_join_00320_00336 : FiniteChecks.Interval nodeTest 320 336 :=
  FiniteChecks.interval_append nodeTest 320 328 336 nodes_part001_00320 nodes_part001_00328

theorem nodes_part001_join_00336_00352 : FiniteChecks.Interval nodeTest 336 352 :=
  FiniteChecks.interval_append nodeTest 336 344 352 nodes_part001_00336 nodes_part001_00344

theorem nodes_part001_join_00320_00352 : FiniteChecks.Interval nodeTest 320 352 :=
  FiniteChecks.interval_append nodeTest 320 336 352 nodes_part001_join_00320_00336 nodes_part001_join_00336_00352

theorem nodes_part001_join_00352_00368 : FiniteChecks.Interval nodeTest 352 368 :=
  FiniteChecks.interval_append nodeTest 352 360 368 nodes_part001_00352 nodes_part001_00360

theorem nodes_part001_join_00368_00384 : FiniteChecks.Interval nodeTest 368 384 :=
  FiniteChecks.interval_append nodeTest 368 376 384 nodes_part001_00368 nodes_part001_00376

theorem nodes_part001_join_00352_00384 : FiniteChecks.Interval nodeTest 352 384 :=
  FiniteChecks.interval_append nodeTest 352 368 384 nodes_part001_join_00352_00368 nodes_part001_join_00368_00384

theorem nodes_part001_join_00320_00384 : FiniteChecks.Interval nodeTest 320 384 :=
  FiniteChecks.interval_append nodeTest 320 352 384 nodes_part001_join_00320_00352 nodes_part001_join_00352_00384

theorem nodes_part001_join_00256_00384 : FiniteChecks.Interval nodeTest 256 384 :=
  FiniteChecks.interval_append nodeTest 256 320 384 nodes_part001_join_00256_00320 nodes_part001_join_00320_00384

theorem nodes_part001_join_00384_00400 : FiniteChecks.Interval nodeTest 384 400 :=
  FiniteChecks.interval_append nodeTest 384 392 400 nodes_part001_00384 nodes_part001_00392

theorem nodes_part001_join_00400_00416 : FiniteChecks.Interval nodeTest 400 416 :=
  FiniteChecks.interval_append nodeTest 400 408 416 nodes_part001_00400 nodes_part001_00408

theorem nodes_part001_join_00384_00416 : FiniteChecks.Interval nodeTest 384 416 :=
  FiniteChecks.interval_append nodeTest 384 400 416 nodes_part001_join_00384_00400 nodes_part001_join_00400_00416

theorem nodes_part001_join_00416_00432 : FiniteChecks.Interval nodeTest 416 432 :=
  FiniteChecks.interval_append nodeTest 416 424 432 nodes_part001_00416 nodes_part001_00424

theorem nodes_part001_join_00432_00448 : FiniteChecks.Interval nodeTest 432 448 :=
  FiniteChecks.interval_append nodeTest 432 440 448 nodes_part001_00432 nodes_part001_00440

theorem nodes_part001_join_00416_00448 : FiniteChecks.Interval nodeTest 416 448 :=
  FiniteChecks.interval_append nodeTest 416 432 448 nodes_part001_join_00416_00432 nodes_part001_join_00432_00448

theorem nodes_part001_join_00384_00448 : FiniteChecks.Interval nodeTest 384 448 :=
  FiniteChecks.interval_append nodeTest 384 416 448 nodes_part001_join_00384_00416 nodes_part001_join_00416_00448

theorem nodes_part001_join_00448_00464 : FiniteChecks.Interval nodeTest 448 464 :=
  FiniteChecks.interval_append nodeTest 448 456 464 nodes_part001_00448 nodes_part001_00456

theorem nodes_part001_join_00464_00480 : FiniteChecks.Interval nodeTest 464 480 :=
  FiniteChecks.interval_append nodeTest 464 472 480 nodes_part001_00464 nodes_part001_00472

theorem nodes_part001_join_00448_00480 : FiniteChecks.Interval nodeTest 448 480 :=
  FiniteChecks.interval_append nodeTest 448 464 480 nodes_part001_join_00448_00464 nodes_part001_join_00464_00480

theorem nodes_part001_join_00480_00496 : FiniteChecks.Interval nodeTest 480 496 :=
  FiniteChecks.interval_append nodeTest 480 488 496 nodes_part001_00480 nodes_part001_00488

theorem nodes_part001_join_00496_00512 : FiniteChecks.Interval nodeTest 496 512 :=
  FiniteChecks.interval_append nodeTest 496 504 512 nodes_part001_00496 nodes_part001_00504

theorem nodes_part001_join_00480_00512 : FiniteChecks.Interval nodeTest 480 512 :=
  FiniteChecks.interval_append nodeTest 480 496 512 nodes_part001_join_00480_00496 nodes_part001_join_00496_00512

theorem nodes_part001_join_00448_00512 : FiniteChecks.Interval nodeTest 448 512 :=
  FiniteChecks.interval_append nodeTest 448 480 512 nodes_part001_join_00448_00480 nodes_part001_join_00480_00512

theorem nodes_part001_join_00384_00512 : FiniteChecks.Interval nodeTest 384 512 :=
  FiniteChecks.interval_append nodeTest 384 448 512 nodes_part001_join_00384_00448 nodes_part001_join_00448_00512

theorem nodes_part001_join_00256_00512 : FiniteChecks.Interval nodeTest 256 512 :=
  FiniteChecks.interval_append nodeTest 256 384 512 nodes_part001_join_00256_00384 nodes_part001_join_00384_00512

end Papers.RationalityTen.PolygonGrowth.N7
