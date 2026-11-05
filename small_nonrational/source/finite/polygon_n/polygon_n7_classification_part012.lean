module

public import PolygonN7ClassificationPart011

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

theorem terminal_data_join_01200_01216 : FiniteChecks.Interval terminalTest 1200 1216 :=
  FiniteChecks.interval_append terminalTest 1200 1208 1216 terminal_data_01200 terminal_data_01208

theorem terminal_data_join_01216_01232 : FiniteChecks.Interval terminalTest 1216 1232 :=
  FiniteChecks.interval_append terminalTest 1216 1224 1232 terminal_data_01216 terminal_data_01224

theorem terminal_data_join_01200_01232 : FiniteChecks.Interval terminalTest 1200 1232 :=
  FiniteChecks.interval_append terminalTest 1200 1216 1232 terminal_data_join_01200_01216 terminal_data_join_01216_01232

theorem terminal_data_join_01176_01232 : FiniteChecks.Interval terminalTest 1176 1232 :=
  FiniteChecks.interval_append terminalTest 1176 1200 1232 terminal_data_join_01176_01200 terminal_data_join_01200_01232

theorem terminal_data_join_01232_01248 : FiniteChecks.Interval terminalTest 1232 1248 :=
  FiniteChecks.interval_append terminalTest 1232 1240 1248 terminal_data_01232 terminal_data_01240

theorem terminal_data_join_01248_01264 : FiniteChecks.Interval terminalTest 1248 1264 :=
  FiniteChecks.interval_append terminalTest 1248 1256 1264 terminal_data_01248 terminal_data_01256

theorem terminal_data_join_01232_01264 : FiniteChecks.Interval terminalTest 1232 1264 :=
  FiniteChecks.interval_append terminalTest 1232 1248 1264 terminal_data_join_01232_01248 terminal_data_join_01248_01264

theorem terminal_data_join_01264_01280 : FiniteChecks.Interval terminalTest 1264 1280 :=
  FiniteChecks.interval_append terminalTest 1264 1272 1280 terminal_data_01264 terminal_data_01272

theorem terminal_data_join_01280_01296 : FiniteChecks.Interval terminalTest 1280 1296 :=
  FiniteChecks.interval_append terminalTest 1280 1288 1296 terminal_data_01280 terminal_data_01288

theorem terminal_data_join_01264_01296 : FiniteChecks.Interval terminalTest 1264 1296 :=
  FiniteChecks.interval_append terminalTest 1264 1280 1296 terminal_data_join_01264_01280 terminal_data_join_01280_01296

theorem terminal_data_join_01232_01296 : FiniteChecks.Interval terminalTest 1232 1296 :=
  FiniteChecks.interval_append terminalTest 1232 1264 1296 terminal_data_join_01232_01264 terminal_data_join_01264_01296

theorem terminal_data_join_01176_01296 : FiniteChecks.Interval terminalTest 1176 1296 :=
  FiniteChecks.interval_append terminalTest 1176 1232 1296 terminal_data_join_01176_01232 terminal_data_join_01232_01296

theorem terminal_data_join_01304_01320 : FiniteChecks.Interval terminalTest 1304 1320 :=
  FiniteChecks.interval_append terminalTest 1304 1312 1320 terminal_data_01304 terminal_data_01312

theorem terminal_data_join_01296_01320 : FiniteChecks.Interval terminalTest 1296 1320 :=
  FiniteChecks.interval_append terminalTest 1296 1304 1320 terminal_data_01296 terminal_data_join_01304_01320

theorem terminal_data_join_01320_01336 : FiniteChecks.Interval terminalTest 1320 1336 :=
  FiniteChecks.interval_append terminalTest 1320 1328 1336 terminal_data_01320 terminal_data_01328

theorem terminal_data_join_01336_01352 : FiniteChecks.Interval terminalTest 1336 1352 :=
  FiniteChecks.interval_append terminalTest 1336 1344 1352 terminal_data_01336 terminal_data_01344

theorem terminal_data_join_01320_01352 : FiniteChecks.Interval terminalTest 1320 1352 :=
  FiniteChecks.interval_append terminalTest 1320 1336 1352 terminal_data_join_01320_01336 terminal_data_join_01336_01352

theorem terminal_data_join_01296_01352 : FiniteChecks.Interval terminalTest 1296 1352 :=
  FiniteChecks.interval_append terminalTest 1296 1320 1352 terminal_data_join_01296_01320 terminal_data_join_01320_01352

theorem terminal_data_join_01352_01368 : FiniteChecks.Interval terminalTest 1352 1368 :=
  FiniteChecks.interval_append terminalTest 1352 1360 1368 terminal_data_01352 terminal_data_01360

theorem terminal_data_join_01368_01384 : FiniteChecks.Interval terminalTest 1368 1384 :=
  FiniteChecks.interval_append terminalTest 1368 1376 1384 terminal_data_01368 terminal_data_01376

theorem terminal_data_join_01352_01384 : FiniteChecks.Interval terminalTest 1352 1384 :=
  FiniteChecks.interval_append terminalTest 1352 1368 1384 terminal_data_join_01352_01368 terminal_data_join_01368_01384

theorem terminal_data_join_01384_01400 : FiniteChecks.Interval terminalTest 1384 1400 :=
  FiniteChecks.interval_append terminalTest 1384 1392 1400 terminal_data_01384 terminal_data_01392

theorem terminal_data_join_01400_01416 : FiniteChecks.Interval terminalTest 1400 1416 :=
  FiniteChecks.interval_append terminalTest 1400 1408 1416 terminal_data_01400 terminal_data_01408

theorem terminal_data_join_01384_01416 : FiniteChecks.Interval terminalTest 1384 1416 :=
  FiniteChecks.interval_append terminalTest 1384 1400 1416 terminal_data_join_01384_01400 terminal_data_join_01400_01416

theorem terminal_data_join_01352_01416 : FiniteChecks.Interval terminalTest 1352 1416 :=
  FiniteChecks.interval_append terminalTest 1352 1384 1416 terminal_data_join_01352_01384 terminal_data_join_01384_01416

theorem terminal_data_join_01296_01416 : FiniteChecks.Interval terminalTest 1296 1416 :=
  FiniteChecks.interval_append terminalTest 1296 1352 1416 terminal_data_join_01296_01352 terminal_data_join_01352_01416

theorem terminal_data_join_01176_01416 : FiniteChecks.Interval terminalTest 1176 1416 :=
  FiniteChecks.interval_append terminalTest 1176 1296 1416 terminal_data_join_01176_01296 terminal_data_join_01296_01416

theorem terminal_data_join_00944_01416 : FiniteChecks.Interval terminalTest 944 1416 :=
  FiniteChecks.interval_append terminalTest 944 1176 1416 terminal_data_join_00944_01176 terminal_data_join_01176_01416

theorem terminal_data_join_01424_01440 : FiniteChecks.Interval terminalTest 1424 1440 :=
  FiniteChecks.interval_append terminalTest 1424 1432 1440 terminal_data_01424 terminal_data_01432

theorem terminal_data_join_01416_01440 : FiniteChecks.Interval terminalTest 1416 1440 :=
  FiniteChecks.interval_append terminalTest 1416 1424 1440 terminal_data_01416 terminal_data_join_01424_01440

theorem terminal_data_join_01440_01456 : FiniteChecks.Interval terminalTest 1440 1456 :=
  FiniteChecks.interval_append terminalTest 1440 1448 1456 terminal_data_01440 terminal_data_01448

theorem terminal_data_join_01456_01472 : FiniteChecks.Interval terminalTest 1456 1472 :=
  FiniteChecks.interval_append terminalTest 1456 1464 1472 terminal_data_01456 terminal_data_01464

theorem terminal_data_join_01440_01472 : FiniteChecks.Interval terminalTest 1440 1472 :=
  FiniteChecks.interval_append terminalTest 1440 1456 1472 terminal_data_join_01440_01456 terminal_data_join_01456_01472

theorem terminal_data_join_01416_01472 : FiniteChecks.Interval terminalTest 1416 1472 :=
  FiniteChecks.interval_append terminalTest 1416 1440 1472 terminal_data_join_01416_01440 terminal_data_join_01440_01472

theorem terminal_data_join_01472_01488 : FiniteChecks.Interval terminalTest 1472 1488 :=
  FiniteChecks.interval_append terminalTest 1472 1480 1488 terminal_data_01472 terminal_data_01480

theorem terminal_data_join_01488_01504 : FiniteChecks.Interval terminalTest 1488 1504 :=
  FiniteChecks.interval_append terminalTest 1488 1496 1504 terminal_data_01488 terminal_data_01496

theorem terminal_data_join_01472_01504 : FiniteChecks.Interval terminalTest 1472 1504 :=
  FiniteChecks.interval_append terminalTest 1472 1488 1504 terminal_data_join_01472_01488 terminal_data_join_01488_01504

theorem terminal_data_join_01504_01520 : FiniteChecks.Interval terminalTest 1504 1520 :=
  FiniteChecks.interval_append terminalTest 1504 1512 1520 terminal_data_01504 terminal_data_01512

theorem terminal_data_join_01520_01536 : FiniteChecks.Interval terminalTest 1520 1536 :=
  FiniteChecks.interval_append terminalTest 1520 1528 1536 terminal_data_01520 terminal_data_01528

theorem terminal_data_join_01504_01536 : FiniteChecks.Interval terminalTest 1504 1536 :=
  FiniteChecks.interval_append terminalTest 1504 1520 1536 terminal_data_join_01504_01520 terminal_data_join_01520_01536

theorem terminal_data_join_01472_01536 : FiniteChecks.Interval terminalTest 1472 1536 :=
  FiniteChecks.interval_append terminalTest 1472 1504 1536 terminal_data_join_01472_01504 terminal_data_join_01504_01536

theorem terminal_data_join_01416_01536 : FiniteChecks.Interval terminalTest 1416 1536 :=
  FiniteChecks.interval_append terminalTest 1416 1472 1536 terminal_data_join_01416_01472 terminal_data_join_01472_01536

theorem terminal_data_join_01544_01560 : FiniteChecks.Interval terminalTest 1544 1560 :=
  FiniteChecks.interval_append terminalTest 1544 1552 1560 terminal_data_01544 terminal_data_01552

theorem terminal_data_join_01536_01560 : FiniteChecks.Interval terminalTest 1536 1560 :=
  FiniteChecks.interval_append terminalTest 1536 1544 1560 terminal_data_01536 terminal_data_join_01544_01560

theorem terminal_data_join_01560_01576 : FiniteChecks.Interval terminalTest 1560 1576 :=
  FiniteChecks.interval_append terminalTest 1560 1568 1576 terminal_data_01560 terminal_data_01568

theorem terminal_data_join_01576_01592 : FiniteChecks.Interval terminalTest 1576 1592 :=
  FiniteChecks.interval_append terminalTest 1576 1584 1592 terminal_data_01576 terminal_data_01584

theorem terminal_data_join_01560_01592 : FiniteChecks.Interval terminalTest 1560 1592 :=
  FiniteChecks.interval_append terminalTest 1560 1576 1592 terminal_data_join_01560_01576 terminal_data_join_01576_01592

theorem terminal_data_join_01536_01592 : FiniteChecks.Interval terminalTest 1536 1592 :=
  FiniteChecks.interval_append terminalTest 1536 1560 1592 terminal_data_join_01536_01560 terminal_data_join_01560_01592

theorem terminal_data_join_01592_01608 : FiniteChecks.Interval terminalTest 1592 1608 :=
  FiniteChecks.interval_append terminalTest 1592 1600 1608 terminal_data_01592 terminal_data_01600

theorem terminal_data_join_01608_01624 : FiniteChecks.Interval terminalTest 1608 1624 :=
  FiniteChecks.interval_append terminalTest 1608 1616 1624 terminal_data_01608 terminal_data_01616

theorem terminal_data_join_01592_01624 : FiniteChecks.Interval terminalTest 1592 1624 :=
  FiniteChecks.interval_append terminalTest 1592 1608 1624 terminal_data_join_01592_01608 terminal_data_join_01608_01624

theorem terminal_data_join_01624_01640 : FiniteChecks.Interval terminalTest 1624 1640 :=
  FiniteChecks.interval_append terminalTest 1624 1632 1640 terminal_data_01624 terminal_data_01632

theorem terminal_data_join_01640_01656 : FiniteChecks.Interval terminalTest 1640 1656 :=
  FiniteChecks.interval_append terminalTest 1640 1648 1656 terminal_data_01640 terminal_data_01648

theorem terminal_data_join_01624_01656 : FiniteChecks.Interval terminalTest 1624 1656 :=
  FiniteChecks.interval_append terminalTest 1624 1640 1656 terminal_data_join_01624_01640 terminal_data_join_01640_01656

theorem terminal_data_join_01592_01656 : FiniteChecks.Interval terminalTest 1592 1656 :=
  FiniteChecks.interval_append terminalTest 1592 1624 1656 terminal_data_join_01592_01624 terminal_data_join_01624_01656

theorem terminal_data_join_01536_01656 : FiniteChecks.Interval terminalTest 1536 1656 :=
  FiniteChecks.interval_append terminalTest 1536 1592 1656 terminal_data_join_01536_01592 terminal_data_join_01592_01656

theorem terminal_data_join_01416_01656 : FiniteChecks.Interval terminalTest 1416 1656 :=
  FiniteChecks.interval_append terminalTest 1416 1536 1656 terminal_data_join_01416_01536 terminal_data_join_01536_01656

theorem terminal_data_join_01664_01680 : FiniteChecks.Interval terminalTest 1664 1680 :=
  FiniteChecks.interval_append terminalTest 1664 1672 1680 terminal_data_01664 terminal_data_01672

theorem terminal_data_join_01656_01680 : FiniteChecks.Interval terminalTest 1656 1680 :=
  FiniteChecks.interval_append terminalTest 1656 1664 1680 terminal_data_01656 terminal_data_join_01664_01680

theorem terminal_data_join_01680_01696 : FiniteChecks.Interval terminalTest 1680 1696 :=
  FiniteChecks.interval_append terminalTest 1680 1688 1696 terminal_data_01680 terminal_data_01688

theorem terminal_data_join_01696_01712 : FiniteChecks.Interval terminalTest 1696 1712 :=
  FiniteChecks.interval_append terminalTest 1696 1704 1712 terminal_data_01696 terminal_data_01704

theorem terminal_data_join_01680_01712 : FiniteChecks.Interval terminalTest 1680 1712 :=
  FiniteChecks.interval_append terminalTest 1680 1696 1712 terminal_data_join_01680_01696 terminal_data_join_01696_01712

theorem terminal_data_join_01656_01712 : FiniteChecks.Interval terminalTest 1656 1712 :=
  FiniteChecks.interval_append terminalTest 1656 1680 1712 terminal_data_join_01656_01680 terminal_data_join_01680_01712

theorem terminal_data_join_01712_01728 : FiniteChecks.Interval terminalTest 1712 1728 :=
  FiniteChecks.interval_append terminalTest 1712 1720 1728 terminal_data_01712 terminal_data_01720


end Papers.RationalityTen.ConcretePolygonClassification.N7
