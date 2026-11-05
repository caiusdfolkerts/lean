module

public import PolygonN7ClassificationPart009

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

theorem terminal_data_join_00168_00184 : FiniteChecks.Interval terminalTest 168 184 :=
  FiniteChecks.interval_append terminalTest 168 176 184 terminal_data_00168 terminal_data_00176

theorem terminal_data_join_00184_00200 : FiniteChecks.Interval terminalTest 184 200 :=
  FiniteChecks.interval_append terminalTest 184 192 200 terminal_data_00184 terminal_data_00192

theorem terminal_data_join_00168_00200 : FiniteChecks.Interval terminalTest 168 200 :=
  FiniteChecks.interval_append terminalTest 168 184 200 terminal_data_join_00168_00184 terminal_data_join_00184_00200

theorem terminal_data_join_00200_00216 : FiniteChecks.Interval terminalTest 200 216 :=
  FiniteChecks.interval_append terminalTest 200 208 216 terminal_data_00200 terminal_data_00208

theorem terminal_data_join_00216_00232 : FiniteChecks.Interval terminalTest 216 232 :=
  FiniteChecks.interval_append terminalTest 216 224 232 terminal_data_00216 terminal_data_00224

theorem terminal_data_join_00200_00232 : FiniteChecks.Interval terminalTest 200 232 :=
  FiniteChecks.interval_append terminalTest 200 216 232 terminal_data_join_00200_00216 terminal_data_join_00216_00232

theorem terminal_data_join_00168_00232 : FiniteChecks.Interval terminalTest 168 232 :=
  FiniteChecks.interval_append terminalTest 168 200 232 terminal_data_join_00168_00200 terminal_data_join_00200_00232

theorem terminal_data_join_00112_00232 : FiniteChecks.Interval terminalTest 112 232 :=
  FiniteChecks.interval_append terminalTest 112 168 232 terminal_data_join_00112_00168 terminal_data_join_00168_00232

theorem terminal_data_join_00000_00232 : FiniteChecks.Interval terminalTest 0 232 :=
  FiniteChecks.interval_append terminalTest 0 112 232 terminal_data_join_00000_00112 terminal_data_join_00112_00232

theorem terminal_data_join_00240_00256 : FiniteChecks.Interval terminalTest 240 256 :=
  FiniteChecks.interval_append terminalTest 240 248 256 terminal_data_00240 terminal_data_00248

theorem terminal_data_join_00232_00256 : FiniteChecks.Interval terminalTest 232 256 :=
  FiniteChecks.interval_append terminalTest 232 240 256 terminal_data_00232 terminal_data_join_00240_00256

theorem terminal_data_join_00256_00272 : FiniteChecks.Interval terminalTest 256 272 :=
  FiniteChecks.interval_append terminalTest 256 264 272 terminal_data_00256 terminal_data_00264

theorem terminal_data_join_00272_00288 : FiniteChecks.Interval terminalTest 272 288 :=
  FiniteChecks.interval_append terminalTest 272 280 288 terminal_data_00272 terminal_data_00280

theorem terminal_data_join_00256_00288 : FiniteChecks.Interval terminalTest 256 288 :=
  FiniteChecks.interval_append terminalTest 256 272 288 terminal_data_join_00256_00272 terminal_data_join_00272_00288

theorem terminal_data_join_00232_00288 : FiniteChecks.Interval terminalTest 232 288 :=
  FiniteChecks.interval_append terminalTest 232 256 288 terminal_data_join_00232_00256 terminal_data_join_00256_00288

theorem terminal_data_join_00288_00304 : FiniteChecks.Interval terminalTest 288 304 :=
  FiniteChecks.interval_append terminalTest 288 296 304 terminal_data_00288 terminal_data_00296

theorem terminal_data_join_00304_00320 : FiniteChecks.Interval terminalTest 304 320 :=
  FiniteChecks.interval_append terminalTest 304 312 320 terminal_data_00304 terminal_data_00312

theorem terminal_data_join_00288_00320 : FiniteChecks.Interval terminalTest 288 320 :=
  FiniteChecks.interval_append terminalTest 288 304 320 terminal_data_join_00288_00304 terminal_data_join_00304_00320

theorem terminal_data_join_00320_00336 : FiniteChecks.Interval terminalTest 320 336 :=
  FiniteChecks.interval_append terminalTest 320 328 336 terminal_data_00320 terminal_data_00328

theorem terminal_data_join_00336_00352 : FiniteChecks.Interval terminalTest 336 352 :=
  FiniteChecks.interval_append terminalTest 336 344 352 terminal_data_00336 terminal_data_00344

theorem terminal_data_join_00320_00352 : FiniteChecks.Interval terminalTest 320 352 :=
  FiniteChecks.interval_append terminalTest 320 336 352 terminal_data_join_00320_00336 terminal_data_join_00336_00352

theorem terminal_data_join_00288_00352 : FiniteChecks.Interval terminalTest 288 352 :=
  FiniteChecks.interval_append terminalTest 288 320 352 terminal_data_join_00288_00320 terminal_data_join_00320_00352

theorem terminal_data_join_00232_00352 : FiniteChecks.Interval terminalTest 232 352 :=
  FiniteChecks.interval_append terminalTest 232 288 352 terminal_data_join_00232_00288 terminal_data_join_00288_00352

theorem terminal_data_join_00360_00376 : FiniteChecks.Interval terminalTest 360 376 :=
  FiniteChecks.interval_append terminalTest 360 368 376 terminal_data_00360 terminal_data_00368

theorem terminal_data_join_00352_00376 : FiniteChecks.Interval terminalTest 352 376 :=
  FiniteChecks.interval_append terminalTest 352 360 376 terminal_data_00352 terminal_data_join_00360_00376

theorem terminal_data_join_00376_00392 : FiniteChecks.Interval terminalTest 376 392 :=
  FiniteChecks.interval_append terminalTest 376 384 392 terminal_data_00376 terminal_data_00384

theorem terminal_data_join_00392_00408 : FiniteChecks.Interval terminalTest 392 408 :=
  FiniteChecks.interval_append terminalTest 392 400 408 terminal_data_00392 terminal_data_00400

theorem terminal_data_join_00376_00408 : FiniteChecks.Interval terminalTest 376 408 :=
  FiniteChecks.interval_append terminalTest 376 392 408 terminal_data_join_00376_00392 terminal_data_join_00392_00408

theorem terminal_data_join_00352_00408 : FiniteChecks.Interval terminalTest 352 408 :=
  FiniteChecks.interval_append terminalTest 352 376 408 terminal_data_join_00352_00376 terminal_data_join_00376_00408

theorem terminal_data_join_00408_00424 : FiniteChecks.Interval terminalTest 408 424 :=
  FiniteChecks.interval_append terminalTest 408 416 424 terminal_data_00408 terminal_data_00416

theorem terminal_data_join_00424_00440 : FiniteChecks.Interval terminalTest 424 440 :=
  FiniteChecks.interval_append terminalTest 424 432 440 terminal_data_00424 terminal_data_00432

theorem terminal_data_join_00408_00440 : FiniteChecks.Interval terminalTest 408 440 :=
  FiniteChecks.interval_append terminalTest 408 424 440 terminal_data_join_00408_00424 terminal_data_join_00424_00440

theorem terminal_data_join_00440_00456 : FiniteChecks.Interval terminalTest 440 456 :=
  FiniteChecks.interval_append terminalTest 440 448 456 terminal_data_00440 terminal_data_00448

theorem terminal_data_join_00456_00472 : FiniteChecks.Interval terminalTest 456 472 :=
  FiniteChecks.interval_append terminalTest 456 464 472 terminal_data_00456 terminal_data_00464

theorem terminal_data_join_00440_00472 : FiniteChecks.Interval terminalTest 440 472 :=
  FiniteChecks.interval_append terminalTest 440 456 472 terminal_data_join_00440_00456 terminal_data_join_00456_00472

theorem terminal_data_join_00408_00472 : FiniteChecks.Interval terminalTest 408 472 :=
  FiniteChecks.interval_append terminalTest 408 440 472 terminal_data_join_00408_00440 terminal_data_join_00440_00472

theorem terminal_data_join_00352_00472 : FiniteChecks.Interval terminalTest 352 472 :=
  FiniteChecks.interval_append terminalTest 352 408 472 terminal_data_join_00352_00408 terminal_data_join_00408_00472

theorem terminal_data_join_00232_00472 : FiniteChecks.Interval terminalTest 232 472 :=
  FiniteChecks.interval_append terminalTest 232 352 472 terminal_data_join_00232_00352 terminal_data_join_00352_00472

theorem terminal_data_join_00000_00472 : FiniteChecks.Interval terminalTest 0 472 :=
  FiniteChecks.interval_append terminalTest 0 232 472 terminal_data_join_00000_00232 terminal_data_join_00232_00472

theorem terminal_data_join_00480_00496 : FiniteChecks.Interval terminalTest 480 496 :=
  FiniteChecks.interval_append terminalTest 480 488 496 terminal_data_00480 terminal_data_00488

theorem terminal_data_join_00472_00496 : FiniteChecks.Interval terminalTest 472 496 :=
  FiniteChecks.interval_append terminalTest 472 480 496 terminal_data_00472 terminal_data_join_00480_00496

theorem terminal_data_join_00496_00512 : FiniteChecks.Interval terminalTest 496 512 :=
  FiniteChecks.interval_append terminalTest 496 504 512 terminal_data_00496 terminal_data_00504

theorem terminal_data_join_00512_00528 : FiniteChecks.Interval terminalTest 512 528 :=
  FiniteChecks.interval_append terminalTest 512 520 528 terminal_data_00512 terminal_data_00520

theorem terminal_data_join_00496_00528 : FiniteChecks.Interval terminalTest 496 528 :=
  FiniteChecks.interval_append terminalTest 496 512 528 terminal_data_join_00496_00512 terminal_data_join_00512_00528

theorem terminal_data_join_00472_00528 : FiniteChecks.Interval terminalTest 472 528 :=
  FiniteChecks.interval_append terminalTest 472 496 528 terminal_data_join_00472_00496 terminal_data_join_00496_00528

theorem terminal_data_join_00536_00552 : FiniteChecks.Interval terminalTest 536 552 :=
  FiniteChecks.interval_append terminalTest 536 544 552 terminal_data_00536 terminal_data_00544

theorem terminal_data_join_00528_00552 : FiniteChecks.Interval terminalTest 528 552 :=
  FiniteChecks.interval_append terminalTest 528 536 552 terminal_data_00528 terminal_data_join_00536_00552

theorem terminal_data_join_00552_00568 : FiniteChecks.Interval terminalTest 552 568 :=
  FiniteChecks.interval_append terminalTest 552 560 568 terminal_data_00552 terminal_data_00560

theorem terminal_data_join_00568_00584 : FiniteChecks.Interval terminalTest 568 584 :=
  FiniteChecks.interval_append terminalTest 568 576 584 terminal_data_00568 terminal_data_00576

theorem terminal_data_join_00552_00584 : FiniteChecks.Interval terminalTest 552 584 :=
  FiniteChecks.interval_append terminalTest 552 568 584 terminal_data_join_00552_00568 terminal_data_join_00568_00584

theorem terminal_data_join_00528_00584 : FiniteChecks.Interval terminalTest 528 584 :=
  FiniteChecks.interval_append terminalTest 528 552 584 terminal_data_join_00528_00552 terminal_data_join_00552_00584

theorem terminal_data_join_00472_00584 : FiniteChecks.Interval terminalTest 472 584 :=
  FiniteChecks.interval_append terminalTest 472 528 584 terminal_data_join_00472_00528 terminal_data_join_00528_00584

theorem terminal_data_join_00592_00608 : FiniteChecks.Interval terminalTest 592 608 :=
  FiniteChecks.interval_append terminalTest 592 600 608 terminal_data_00592 terminal_data_00600

theorem terminal_data_join_00584_00608 : FiniteChecks.Interval terminalTest 584 608 :=
  FiniteChecks.interval_append terminalTest 584 592 608 terminal_data_00584 terminal_data_join_00592_00608

theorem terminal_data_join_00608_00624 : FiniteChecks.Interval terminalTest 608 624 :=
  FiniteChecks.interval_append terminalTest 608 616 624 terminal_data_00608 terminal_data_00616

theorem terminal_data_join_00624_00640 : FiniteChecks.Interval terminalTest 624 640 :=
  FiniteChecks.interval_append terminalTest 624 632 640 terminal_data_00624 terminal_data_00632

theorem terminal_data_join_00608_00640 : FiniteChecks.Interval terminalTest 608 640 :=
  FiniteChecks.interval_append terminalTest 608 624 640 terminal_data_join_00608_00624 terminal_data_join_00624_00640

theorem terminal_data_join_00584_00640 : FiniteChecks.Interval terminalTest 584 640 :=
  FiniteChecks.interval_append terminalTest 584 608 640 terminal_data_join_00584_00608 terminal_data_join_00608_00640

theorem terminal_data_join_00640_00656 : FiniteChecks.Interval terminalTest 640 656 :=
  FiniteChecks.interval_append terminalTest 640 648 656 terminal_data_00640 terminal_data_00648

theorem terminal_data_join_00656_00672 : FiniteChecks.Interval terminalTest 656 672 :=
  FiniteChecks.interval_append terminalTest 656 664 672 terminal_data_00656 terminal_data_00664

theorem terminal_data_join_00640_00672 : FiniteChecks.Interval terminalTest 640 672 :=
  FiniteChecks.interval_append terminalTest 640 656 672 terminal_data_join_00640_00656 terminal_data_join_00656_00672

theorem terminal_data_join_00672_00688 : FiniteChecks.Interval terminalTest 672 688 :=
  FiniteChecks.interval_append terminalTest 672 680 688 terminal_data_00672 terminal_data_00680

theorem terminal_data_join_00688_00704 : FiniteChecks.Interval terminalTest 688 704 :=
  FiniteChecks.interval_append terminalTest 688 696 704 terminal_data_00688 terminal_data_00696

theorem terminal_data_join_00672_00704 : FiniteChecks.Interval terminalTest 672 704 :=
  FiniteChecks.interval_append terminalTest 672 688 704 terminal_data_join_00672_00688 terminal_data_join_00688_00704


end Papers.RationalityTen.ConcretePolygonClassification.N7
