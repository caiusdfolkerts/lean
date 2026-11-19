module

public meta import LowerSchemas.FinitePolygonN
public import PolygonN7ClassificationPart011

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

cert_terminal_data_join_2 01200 01216 1200 1216 1208 01208
cert_terminal_data_join_2 01216 01232 1216 1232 1224 01224
cert_terminal_data_join 01200 01232 1200 1232 1216 01216
cert_terminal_data_join 01176 01232 1176 1232 1200 01200
cert_terminal_data_join_2 01232 01248 1232 1248 1240 01240
cert_terminal_data_join_2 01248 01264 1248 1264 1256 01256
cert_terminal_data_join 01232 01264 1232 1264 1248 01248
cert_terminal_data_join_2 01264 01280 1264 1280 1272 01272
cert_terminal_data_join_2 01280 01296 1280 1296 1288 01288
cert_terminal_data_join 01264 01296 1264 1296 1280 01280
cert_terminal_data_join 01232 01296 1232 1296 1264 01264
cert_terminal_data_join 01176 01296 1176 1296 1232 01232
cert_terminal_data_join_2 01304 01320 1304 1320 1312 01312
cert_terminal_data_join_3 01296 01320 1296 1320 1304 01304
cert_terminal_data_join_2 01320 01336 1320 1336 1328 01328
cert_terminal_data_join_2 01336 01352 1336 1352 1344 01344
cert_terminal_data_join 01320 01352 1320 1352 1336 01336
cert_terminal_data_join 01296 01352 1296 1352 1320 01320
cert_terminal_data_join_2 01352 01368 1352 1368 1360 01360
cert_terminal_data_join_2 01368 01384 1368 1384 1376 01376
cert_terminal_data_join 01352 01384 1352 1384 1368 01368
cert_terminal_data_join_2 01384 01400 1384 1400 1392 01392
cert_terminal_data_join_2 01400 01416 1400 1416 1408 01408
cert_terminal_data_join 01384 01416 1384 1416 1400 01400
cert_terminal_data_join 01352 01416 1352 1416 1384 01384
cert_terminal_data_join 01296 01416 1296 1416 1352 01352
cert_terminal_data_join 01176 01416 1176 1416 1296 01296
cert_terminal_data_join 00944 01416 944 1416 1176 01176
cert_terminal_data_join_2 01424 01440 1424 1440 1432 01432
cert_terminal_data_join_3 01416 01440 1416 1440 1424 01424
cert_terminal_data_join_2 01440 01456 1440 1456 1448 01448
cert_terminal_data_join_2 01456 01472 1456 1472 1464 01464
cert_terminal_data_join 01440 01472 1440 1472 1456 01456
cert_terminal_data_join 01416 01472 1416 1472 1440 01440
cert_terminal_data_join_2 01472 01488 1472 1488 1480 01480
cert_terminal_data_join_2 01488 01504 1488 1504 1496 01496
cert_terminal_data_join 01472 01504 1472 1504 1488 01488
cert_terminal_data_join_2 01504 01520 1504 1520 1512 01512
cert_terminal_data_join_2 01520 01536 1520 1536 1528 01528
cert_terminal_data_join 01504 01536 1504 1536 1520 01520
cert_terminal_data_join 01472 01536 1472 1536 1504 01504
cert_terminal_data_join 01416 01536 1416 1536 1472 01472
cert_terminal_data_join_2 01544 01560 1544 1560 1552 01552
cert_terminal_data_join_3 01536 01560 1536 1560 1544 01544
cert_terminal_data_join_2 01560 01576 1560 1576 1568 01568
cert_terminal_data_join_2 01576 01592 1576 1592 1584 01584
cert_terminal_data_join 01560 01592 1560 1592 1576 01576
cert_terminal_data_join 01536 01592 1536 1592 1560 01560
cert_terminal_data_join_2 01592 01608 1592 1608 1600 01600
cert_terminal_data_join_2 01608 01624 1608 1624 1616 01616
cert_terminal_data_join 01592 01624 1592 1624 1608 01608
cert_terminal_data_join_2 01624 01640 1624 1640 1632 01632
cert_terminal_data_join_2 01640 01656 1640 1656 1648 01648
cert_terminal_data_join 01624 01656 1624 1656 1640 01640
cert_terminal_data_join 01592 01656 1592 1656 1624 01624
cert_terminal_data_join 01536 01656 1536 1656 1592 01592
cert_terminal_data_join 01416 01656 1416 1656 1536 01536
cert_terminal_data_join_2 01664 01680 1664 1680 1672 01672
cert_terminal_data_join_3 01656 01680 1656 1680 1664 01664
cert_terminal_data_join_2 01680 01696 1680 1696 1688 01688
cert_terminal_data_join_2 01696 01712 1696 1712 1704 01704
cert_terminal_data_join 01680 01712 1680 1712 1696 01696
cert_terminal_data_join 01656 01712 1656 1712 1680 01680
theorem terminal_data_join_01712_01728 : FiniteChecks.Interval terminalTest 1712 1728 :=
  FiniteChecks.interval_append terminalTest 1712 1720 1728 terminal_data_01712 terminal_data_01720


end Papers.RationalityTen.ConcretePolygonClassification.N7
