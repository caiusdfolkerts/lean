module

public meta import LowerSchemas.FinitePolygonN
public import PolygonN7ClassificationPart009

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

cert_terminal_data_join_2 00168 00184 168 184 176 00176
cert_terminal_data_join_2 00184 00200 184 200 192 00192
cert_terminal_data_join 00168 00200 168 200 184 00184
cert_terminal_data_join_2 00200 00216 200 216 208 00208
cert_terminal_data_join_2 00216 00232 216 232 224 00224
cert_terminal_data_join 00200 00232 200 232 216 00216
cert_terminal_data_join 00168 00232 168 232 200 00200
cert_terminal_data_join 00112 00232 112 232 168 00168
cert_terminal_data_join 00000 00232 0 232 112 00112
cert_terminal_data_join_2 00240 00256 240 256 248 00248
cert_terminal_data_join_3 00232 00256 232 256 240 00240
cert_terminal_data_join_2 00256 00272 256 272 264 00264
cert_terminal_data_join_2 00272 00288 272 288 280 00280
cert_terminal_data_join 00256 00288 256 288 272 00272
cert_terminal_data_join 00232 00288 232 288 256 00256
cert_terminal_data_join_2 00288 00304 288 304 296 00296
cert_terminal_data_join_2 00304 00320 304 320 312 00312
cert_terminal_data_join 00288 00320 288 320 304 00304
cert_terminal_data_join_2 00320 00336 320 336 328 00328
cert_terminal_data_join_2 00336 00352 336 352 344 00344
cert_terminal_data_join 00320 00352 320 352 336 00336
cert_terminal_data_join 00288 00352 288 352 320 00320
cert_terminal_data_join 00232 00352 232 352 288 00288
cert_terminal_data_join_2 00360 00376 360 376 368 00368
cert_terminal_data_join_3 00352 00376 352 376 360 00360
cert_terminal_data_join_2 00376 00392 376 392 384 00384
cert_terminal_data_join_2 00392 00408 392 408 400 00400
cert_terminal_data_join 00376 00408 376 408 392 00392
cert_terminal_data_join 00352 00408 352 408 376 00376
cert_terminal_data_join_2 00408 00424 408 424 416 00416
cert_terminal_data_join_2 00424 00440 424 440 432 00432
cert_terminal_data_join 00408 00440 408 440 424 00424
cert_terminal_data_join_2 00440 00456 440 456 448 00448
cert_terminal_data_join_2 00456 00472 456 472 464 00464
cert_terminal_data_join 00440 00472 440 472 456 00456
cert_terminal_data_join 00408 00472 408 472 440 00440
cert_terminal_data_join 00352 00472 352 472 408 00408
cert_terminal_data_join 00232 00472 232 472 352 00352
cert_terminal_data_join 00000 00472 0 472 232 00232
cert_terminal_data_join_2 00480 00496 480 496 488 00488
cert_terminal_data_join_3 00472 00496 472 496 480 00480
cert_terminal_data_join_2 00496 00512 496 512 504 00504
cert_terminal_data_join_2 00512 00528 512 528 520 00520
cert_terminal_data_join 00496 00528 496 528 512 00512
cert_terminal_data_join 00472 00528 472 528 496 00496
cert_terminal_data_join_2 00536 00552 536 552 544 00544
cert_terminal_data_join_3 00528 00552 528 552 536 00536
cert_terminal_data_join_2 00552 00568 552 568 560 00560
cert_terminal_data_join_2 00568 00584 568 584 576 00576
cert_terminal_data_join 00552 00584 552 584 568 00568
cert_terminal_data_join 00528 00584 528 584 552 00552
cert_terminal_data_join 00472 00584 472 584 528 00528
cert_terminal_data_join_2 00592 00608 592 608 600 00600
cert_terminal_data_join_3 00584 00608 584 608 592 00592
cert_terminal_data_join_2 00608 00624 608 624 616 00616
cert_terminal_data_join_2 00624 00640 624 640 632 00632
cert_terminal_data_join 00608 00640 608 640 624 00624
cert_terminal_data_join 00584 00640 584 640 608 00608
cert_terminal_data_join_2 00640 00656 640 656 648 00648
cert_terminal_data_join_2 00656 00672 656 672 664 00664
cert_terminal_data_join 00640 00672 640 672 656 00656
cert_terminal_data_join_2 00672 00688 672 688 680 00680
cert_terminal_data_join_2 00688 00704 688 704 696 00696
theorem terminal_data_join_00672_00704 : FiniteChecks.Interval terminalTest 672 704 :=
  FiniteChecks.interval_append terminalTest 672 688 704 terminal_data_join_00672_00688 terminal_data_join_00688_00704


end Papers.RationalityTen.ConcretePolygonClassification.N7
