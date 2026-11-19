module
prelude
public meta import LowerSchemas.FinitePolygonN
public import PolygonN7DAGTests

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.PolygonGrowth.N7
open Papers.RationalityTen GrowthDAG SparseGrowthDAG GrowthPruning FiniteChecks

cert_nodes_part 001 00256 256 264 8
cert_nodes_part 001 00264 264 272 8
cert_nodes_part 001 00272 272 280 8
cert_nodes_part 001 00280 280 288 8
cert_nodes_part 001 00288 288 296 8
cert_nodes_part 001 00296 296 304 8
cert_nodes_part 001 00304 304 312 8
cert_nodes_part 001 00312 312 320 8
cert_nodes_part 001 00320 320 328 8
cert_nodes_part 001 00328 328 336 8
cert_nodes_part 001 00336 336 344 8
cert_nodes_part 001 00344 344 352 8
cert_nodes_part 001 00352 352 360 8
cert_nodes_part 001 00360 360 368 8
cert_nodes_part 001 00368 368 376 8
cert_nodes_part 001 00376 376 384 8
cert_nodes_part 001 00384 384 392 8
cert_nodes_part 001 00392 392 400 8
cert_nodes_part 001 00400 400 408 8
cert_nodes_part 001 00408 408 416 8
cert_nodes_part 001 00416 416 424 8
cert_nodes_part 001 00424 424 432 8
cert_nodes_part 001 00432 432 440 8
cert_nodes_part 001 00440 440 448 8
cert_nodes_part 001 00448 448 456 8
cert_nodes_part 001 00456 456 464 8
cert_nodes_part 001 00464 464 472 8
cert_nodes_part 001 00472 472 480 8
cert_nodes_part 001 00480 480 488 8
cert_nodes_part 001 00488 488 496 8
cert_nodes_part 001 00496 496 504 8
cert_nodes_part 001 00504 504 512 8
cert_nodes_part_join_2 001 00256 00272 256 272 264 00264
cert_nodes_part_join_2 001 00272 00288 272 288 280 00280
cert_nodes_part_join 001 00256 00288 256 288 272 00272
cert_nodes_part_join_2 001 00288 00304 288 304 296 00296
cert_nodes_part_join_2 001 00304 00320 304 320 312 00312
cert_nodes_part_join 001 00288 00320 288 320 304 00304
cert_nodes_part_join 001 00256 00320 256 320 288 00288
cert_nodes_part_join_2 001 00320 00336 320 336 328 00328
cert_nodes_part_join_2 001 00336 00352 336 352 344 00344
cert_nodes_part_join 001 00320 00352 320 352 336 00336
cert_nodes_part_join_2 001 00352 00368 352 368 360 00360
cert_nodes_part_join_2 001 00368 00384 368 384 376 00376
cert_nodes_part_join 001 00352 00384 352 384 368 00368
cert_nodes_part_join 001 00320 00384 320 384 352 00352
cert_nodes_part_join 001 00256 00384 256 384 320 00320
cert_nodes_part_join_2 001 00384 00400 384 400 392 00392
cert_nodes_part_join_2 001 00400 00416 400 416 408 00408
cert_nodes_part_join 001 00384 00416 384 416 400 00400
cert_nodes_part_join_2 001 00416 00432 416 432 424 00424
cert_nodes_part_join_2 001 00432 00448 432 448 440 00440
cert_nodes_part_join 001 00416 00448 416 448 432 00432
cert_nodes_part_join 001 00384 00448 384 448 416 00416
cert_nodes_part_join_2 001 00448 00464 448 464 456 00456
cert_nodes_part_join_2 001 00464 00480 464 480 472 00472
cert_nodes_part_join 001 00448 00480 448 480 464 00464
cert_nodes_part_join_2 001 00480 00496 480 496 488 00488
cert_nodes_part_join_2 001 00496 00512 496 512 504 00504
cert_nodes_part_join 001 00480 00512 480 512 496 00496
cert_nodes_part_join 001 00448 00512 448 512 480 00480
cert_nodes_part_join 001 00384 00512 384 512 448 00448
cert_nodes_part_join 001 00256 00512 256 512 384 00384
end Papers.RationalityTen.PolygonGrowth.N7
