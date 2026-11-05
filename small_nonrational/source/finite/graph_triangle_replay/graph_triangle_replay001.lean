module
prelude
public import SharedTriangleCountsData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open Papers.RationalityTen FiniteChecks

namespace Papers.RationalityTen.SharedTriangleCounts
theorem Check008.part1024 : Interval test 1024 1032 :=
  interval_of_check _ 1024 8 (by decide +kernel)
theorem Check008.part1032 : Interval test 1032 1040 :=
  interval_of_check _ 1032 8 (by decide +kernel)
theorem Check008.part1040 : Interval test 1040 1048 :=
  interval_of_check _ 1040 8 (by decide +kernel)
theorem Check008.part1048 : Interval test 1048 1056 :=
  interval_of_check _ 1048 8 (by decide +kernel)
theorem Check008.part1056 : Interval test 1056 1064 :=
  interval_of_check _ 1056 8 (by decide +kernel)
theorem Check008.part1064 : Interval test 1064 1072 :=
  interval_of_check _ 1064 8 (by decide +kernel)
theorem Check008.part1072 : Interval test 1072 1080 :=
  interval_of_check _ 1072 8 (by decide +kernel)
theorem Check008.part1080 : Interval test 1080 1088 :=
  interval_of_check _ 1080 8 (by decide +kernel)
theorem Check008.part1088 : Interval test 1088 1096 :=
  interval_of_check _ 1088 8 (by decide +kernel)
theorem Check008.part1096 : Interval test 1096 1104 :=
  interval_of_check _ 1096 8 (by decide +kernel)
theorem Check008.part1104 : Interval test 1104 1112 :=
  interval_of_check _ 1104 8 (by decide +kernel)
theorem Check008.part1112 : Interval test 1112 1120 :=
  interval_of_check _ 1112 8 (by decide +kernel)
theorem Check008.part1120 : Interval test 1120 1128 :=
  interval_of_check _ 1120 8 (by decide +kernel)
theorem Check008.part1128 : Interval test 1128 1136 :=
  interval_of_check _ 1128 8 (by decide +kernel)
theorem Check008.part1136 : Interval test 1136 1144 :=
  interval_of_check _ 1136 8 (by decide +kernel)
theorem Check008.part1144 : Interval test 1144 1152 :=
  interval_of_check _ 1144 8 (by decide +kernel)
theorem Check008.checked : Interval test 1024 1152 :=
  (FiniteChecks.interval_append test 1024 1088 1152
  (FiniteChecks.interval_append test 1024 1056 1088
  (FiniteChecks.interval_append test 1024 1040 1056
  (FiniteChecks.interval_append test 1024 1032 1040
  Check008.part1024
  Check008.part1032)
  (FiniteChecks.interval_append test 1040 1048 1056
  Check008.part1040
  Check008.part1048))
  (FiniteChecks.interval_append test 1056 1072 1088
  (FiniteChecks.interval_append test 1056 1064 1072
  Check008.part1056
  Check008.part1064)
  (FiniteChecks.interval_append test 1072 1080 1088
  Check008.part1072
  Check008.part1080)))
  (FiniteChecks.interval_append test 1088 1120 1152
  (FiniteChecks.interval_append test 1088 1104 1120
  (FiniteChecks.interval_append test 1088 1096 1104
  Check008.part1088
  Check008.part1096)
  (FiniteChecks.interval_append test 1104 1112 1120
  Check008.part1104
  Check008.part1112))
  (FiniteChecks.interval_append test 1120 1136 1152
  (FiniteChecks.interval_append test 1120 1128 1136
  Check008.part1120
  Check008.part1128)
  (FiniteChecks.interval_append test 1136 1144 1152
  Check008.part1136
  Check008.part1144))))
theorem Check009.part1152 : Interval test 1152 1160 :=
  interval_of_check _ 1152 8 (by decide +kernel)
theorem Check009.part1160 : Interval test 1160 1168 :=
  interval_of_check _ 1160 8 (by decide +kernel)
theorem Check009.part1168 : Interval test 1168 1176 :=
  interval_of_check _ 1168 8 (by decide +kernel)
theorem Check009.part1176 : Interval test 1176 1184 :=
  interval_of_check _ 1176 8 (by decide +kernel)
theorem Check009.part1184 : Interval test 1184 1192 :=
  interval_of_check _ 1184 8 (by decide +kernel)
theorem Check009.part1192 : Interval test 1192 1200 :=
  interval_of_check _ 1192 8 (by decide +kernel)
theorem Check009.part1200 : Interval test 1200 1208 :=
  interval_of_check _ 1200 8 (by decide +kernel)
theorem Check009.part1208 : Interval test 1208 1216 :=
  interval_of_check _ 1208 8 (by decide +kernel)
theorem Check009.part1216 : Interval test 1216 1224 :=
  interval_of_check _ 1216 8 (by decide +kernel)
theorem Check009.part1224 : Interval test 1224 1232 :=
  interval_of_check _ 1224 8 (by decide +kernel)
theorem Check009.part1232 : Interval test 1232 1240 :=
  interval_of_check _ 1232 8 (by decide +kernel)
theorem Check009.part1240 : Interval test 1240 1248 :=
  interval_of_check _ 1240 8 (by decide +kernel)
theorem Check009.part1248 : Interval test 1248 1256 :=
  interval_of_check _ 1248 8 (by decide +kernel)
theorem Check009.part1256 : Interval test 1256 1264 :=
  interval_of_check _ 1256 8 (by decide +kernel)
theorem Check009.part1264 : Interval test 1264 1272 :=
  interval_of_check _ 1264 8 (by decide +kernel)
theorem Check009.part1272 : Interval test 1272 1280 :=
  interval_of_check _ 1272 8 (by decide +kernel)
theorem Check009.checked : Interval test 1152 1280 :=
  (FiniteChecks.interval_append test 1152 1216 1280
  (FiniteChecks.interval_append test 1152 1184 1216
  (FiniteChecks.interval_append test 1152 1168 1184
  (FiniteChecks.interval_append test 1152 1160 1168
  Check009.part1152
  Check009.part1160)
  (FiniteChecks.interval_append test 1168 1176 1184
  Check009.part1168
  Check009.part1176))
  (FiniteChecks.interval_append test 1184 1200 1216
  (FiniteChecks.interval_append test 1184 1192 1200
  Check009.part1184
  Check009.part1192)
  (FiniteChecks.interval_append test 1200 1208 1216
  Check009.part1200
  Check009.part1208)))
  (FiniteChecks.interval_append test 1216 1248 1280
  (FiniteChecks.interval_append test 1216 1232 1248
  (FiniteChecks.interval_append test 1216 1224 1232
  Check009.part1216
  Check009.part1224)
  (FiniteChecks.interval_append test 1232 1240 1248
  Check009.part1232
  Check009.part1240))
  (FiniteChecks.interval_append test 1248 1264 1280
  (FiniteChecks.interval_append test 1248 1256 1264
  Check009.part1248
  Check009.part1256)
  (FiniteChecks.interval_append test 1264 1272 1280
  Check009.part1264
  Check009.part1272))))
theorem Check010.part1280 : Interval test 1280 1288 :=
  interval_of_check _ 1280 8 (by decide +kernel)
theorem Check010.part1288 : Interval test 1288 1296 :=
  interval_of_check _ 1288 8 (by decide +kernel)
theorem Check010.part1296 : Interval test 1296 1304 :=
  interval_of_check _ 1296 8 (by decide +kernel)
theorem Check010.part1304 : Interval test 1304 1312 :=
  interval_of_check _ 1304 8 (by decide +kernel)
theorem Check010.part1312 : Interval test 1312 1320 :=
  interval_of_check _ 1312 8 (by decide +kernel)
theorem Check010.part1320 : Interval test 1320 1328 :=
  interval_of_check _ 1320 8 (by decide +kernel)
theorem Check010.part1328 : Interval test 1328 1336 :=
  interval_of_check _ 1328 8 (by decide +kernel)
theorem Check010.part1336 : Interval test 1336 1344 :=
  interval_of_check _ 1336 8 (by decide +kernel)
theorem Check010.part1344 : Interval test 1344 1352 :=
  interval_of_check _ 1344 8 (by decide +kernel)
theorem Check010.part1352 : Interval test 1352 1360 :=
  interval_of_check _ 1352 8 (by decide +kernel)
theorem Check010.part1360 : Interval test 1360 1368 :=
  interval_of_check _ 1360 8 (by decide +kernel)
theorem Check010.part1368 : Interval test 1368 1376 :=
  interval_of_check _ 1368 8 (by decide +kernel)
theorem Check010.part1376 : Interval test 1376 1384 :=
  interval_of_check _ 1376 8 (by decide +kernel)
theorem Check010.part1384 : Interval test 1384 1392 :=
  interval_of_check _ 1384 8 (by decide +kernel)
theorem Check010.part1392 : Interval test 1392 1400 :=
  interval_of_check _ 1392 8 (by decide +kernel)
theorem Check010.part1400 : Interval test 1400 1408 :=
  interval_of_check _ 1400 8 (by decide +kernel)
theorem Check010.checked : Interval test 1280 1408 :=
  (FiniteChecks.interval_append test 1280 1344 1408
  (FiniteChecks.interval_append test 1280 1312 1344
  (FiniteChecks.interval_append test 1280 1296 1312
  (FiniteChecks.interval_append test 1280 1288 1296
  Check010.part1280
  Check010.part1288)
  (FiniteChecks.interval_append test 1296 1304 1312
  Check010.part1296
  Check010.part1304))
  (FiniteChecks.interval_append test 1312 1328 1344
  (FiniteChecks.interval_append test 1312 1320 1328
  Check010.part1312
  Check010.part1320)
  (FiniteChecks.interval_append test 1328 1336 1344
  Check010.part1328
  Check010.part1336)))
  (FiniteChecks.interval_append test 1344 1376 1408
  (FiniteChecks.interval_append test 1344 1360 1376
  (FiniteChecks.interval_append test 1344 1352 1360
  Check010.part1344
  Check010.part1352)
  (FiniteChecks.interval_append test 1360 1368 1376
  Check010.part1360
  Check010.part1368))
  (FiniteChecks.interval_append test 1376 1392 1408
  (FiniteChecks.interval_append test 1376 1384 1392
  Check010.part1376
  Check010.part1384)
  (FiniteChecks.interval_append test 1392 1400 1408
  Check010.part1392
  Check010.part1400))))
theorem Check011.part1408 : Interval test 1408 1416 :=
  interval_of_check _ 1408 8 (by decide +kernel)
theorem Check011.part1416 : Interval test 1416 1424 :=
  interval_of_check _ 1416 8 (by decide +kernel)
theorem Check011.part1424 : Interval test 1424 1432 :=
  interval_of_check _ 1424 8 (by decide +kernel)
theorem Check011.part1432 : Interval test 1432 1440 :=
  interval_of_check _ 1432 8 (by decide +kernel)
theorem Check011.part1440 : Interval test 1440 1448 :=
  interval_of_check _ 1440 8 (by decide +kernel)
theorem Check011.part1448 : Interval test 1448 1456 :=
  interval_of_check _ 1448 8 (by decide +kernel)
theorem Check011.part1456 : Interval test 1456 1464 :=
  interval_of_check _ 1456 8 (by decide +kernel)
theorem Check011.part1464 : Interval test 1464 1472 :=
  interval_of_check _ 1464 8 (by decide +kernel)
theorem Check011.part1472 : Interval test 1472 1480 :=
  interval_of_check _ 1472 8 (by decide +kernel)
theorem Check011.part1480 : Interval test 1480 1488 :=
  interval_of_check _ 1480 8 (by decide +kernel)
theorem Check011.part1488 : Interval test 1488 1496 :=
  interval_of_check _ 1488 8 (by decide +kernel)
theorem Check011.part1496 : Interval test 1496 1504 :=
  interval_of_check _ 1496 8 (by decide +kernel)
theorem Check011.part1504 : Interval test 1504 1512 :=
  interval_of_check _ 1504 8 (by decide +kernel)
theorem Check011.part1512 : Interval test 1512 1520 :=
  interval_of_check _ 1512 8 (by decide +kernel)
theorem Check011.part1520 : Interval test 1520 1528 :=
  interval_of_check _ 1520 8 (by decide +kernel)
theorem Check011.part1528 : Interval test 1528 1536 :=
  interval_of_check _ 1528 8 (by decide +kernel)
theorem Check011.checked : Interval test 1408 1536 :=
  (FiniteChecks.interval_append test 1408 1472 1536
  (FiniteChecks.interval_append test 1408 1440 1472
  (FiniteChecks.interval_append test 1408 1424 1440
  (FiniteChecks.interval_append test 1408 1416 1424
  Check011.part1408
  Check011.part1416)
  (FiniteChecks.interval_append test 1424 1432 1440
  Check011.part1424
  Check011.part1432))
  (FiniteChecks.interval_append test 1440 1456 1472
  (FiniteChecks.interval_append test 1440 1448 1456
  Check011.part1440
  Check011.part1448)
  (FiniteChecks.interval_append test 1456 1464 1472
  Check011.part1456
  Check011.part1464)))
  (FiniteChecks.interval_append test 1472 1504 1536
  (FiniteChecks.interval_append test 1472 1488 1504
  (FiniteChecks.interval_append test 1472 1480 1488
  Check011.part1472
  Check011.part1480)
  (FiniteChecks.interval_append test 1488 1496 1504
  Check011.part1488
  Check011.part1496))
  (FiniteChecks.interval_append test 1504 1520 1536
  (FiniteChecks.interval_append test 1504 1512 1520
  Check011.part1504
  Check011.part1512)
  (FiniteChecks.interval_append test 1520 1528 1536
  Check011.part1520
  Check011.part1528))))
theorem Check012.part1536 : Interval test 1536 1544 :=
  interval_of_check _ 1536 8 (by decide +kernel)
theorem Check012.part1544 : Interval test 1544 1552 :=
  interval_of_check _ 1544 8 (by decide +kernel)
theorem Check012.part1552 : Interval test 1552 1560 :=
  interval_of_check _ 1552 8 (by decide +kernel)
theorem Check012.part1560 : Interval test 1560 1568 :=
  interval_of_check _ 1560 8 (by decide +kernel)
theorem Check012.part1568 : Interval test 1568 1576 :=
  interval_of_check _ 1568 8 (by decide +kernel)
theorem Check012.part1576 : Interval test 1576 1584 :=
  interval_of_check _ 1576 8 (by decide +kernel)
theorem Check012.part1584 : Interval test 1584 1592 :=
  interval_of_check _ 1584 8 (by decide +kernel)
theorem Check012.part1592 : Interval test 1592 1600 :=
  interval_of_check _ 1592 8 (by decide +kernel)
theorem Check012.part1600 : Interval test 1600 1608 :=
  interval_of_check _ 1600 8 (by decide +kernel)
theorem Check012.part1608 : Interval test 1608 1616 :=
  interval_of_check _ 1608 8 (by decide +kernel)
theorem Check012.part1616 : Interval test 1616 1624 :=
  interval_of_check _ 1616 8 (by decide +kernel)
theorem Check012.part1624 : Interval test 1624 1632 :=
  interval_of_check _ 1624 8 (by decide +kernel)
theorem Check012.part1632 : Interval test 1632 1640 :=
  interval_of_check _ 1632 8 (by decide +kernel)
theorem Check012.part1640 : Interval test 1640 1648 :=
  interval_of_check _ 1640 8 (by decide +kernel)
theorem Check012.part1648 : Interval test 1648 1656 :=
  interval_of_check _ 1648 8 (by decide +kernel)
theorem Check012.part1656 : Interval test 1656 1664 :=
  interval_of_check _ 1656 8 (by decide +kernel)
theorem Check012.checked : Interval test 1536 1664 :=
  (FiniteChecks.interval_append test 1536 1600 1664
  (FiniteChecks.interval_append test 1536 1568 1600
  (FiniteChecks.interval_append test 1536 1552 1568
  (FiniteChecks.interval_append test 1536 1544 1552
  Check012.part1536
  Check012.part1544)
  (FiniteChecks.interval_append test 1552 1560 1568
  Check012.part1552
  Check012.part1560))
  (FiniteChecks.interval_append test 1568 1584 1600
  (FiniteChecks.interval_append test 1568 1576 1584
  Check012.part1568
  Check012.part1576)
  (FiniteChecks.interval_append test 1584 1592 1600
  Check012.part1584
  Check012.part1592)))
  (FiniteChecks.interval_append test 1600 1632 1664
  (FiniteChecks.interval_append test 1600 1616 1632
  (FiniteChecks.interval_append test 1600 1608 1616
  Check012.part1600
  Check012.part1608)
  (FiniteChecks.interval_append test 1616 1624 1632
  Check012.part1616
  Check012.part1624))
  (FiniteChecks.interval_append test 1632 1648 1664
  (FiniteChecks.interval_append test 1632 1640 1648
  Check012.part1632
  Check012.part1640)
  (FiniteChecks.interval_append test 1648 1656 1664
  Check012.part1648
  Check012.part1656))))
theorem Check013.part1664 : Interval test 1664 1672 :=
  interval_of_check _ 1664 8 (by decide +kernel)
theorem Check013.part1672 : Interval test 1672 1680 :=
  interval_of_check _ 1672 8 (by decide +kernel)
theorem Check013.part1680 : Interval test 1680 1688 :=
  interval_of_check _ 1680 8 (by decide +kernel)
theorem Check013.part1688 : Interval test 1688 1696 :=
  interval_of_check _ 1688 8 (by decide +kernel)
theorem Check013.part1696 : Interval test 1696 1704 :=
  interval_of_check _ 1696 8 (by decide +kernel)
theorem Check013.part1704 : Interval test 1704 1712 :=
  interval_of_check _ 1704 8 (by decide +kernel)
theorem Check013.part1712 : Interval test 1712 1720 :=
  interval_of_check _ 1712 8 (by decide +kernel)
theorem Check013.part1720 : Interval test 1720 1728 :=
  interval_of_check _ 1720 8 (by decide +kernel)
theorem Check013.part1728 : Interval test 1728 1736 :=
  interval_of_check _ 1728 8 (by decide +kernel)
theorem Check013.part1736 : Interval test 1736 1744 :=
  interval_of_check _ 1736 8 (by decide +kernel)
theorem Check013.part1744 : Interval test 1744 1752 :=
  interval_of_check _ 1744 8 (by decide +kernel)
theorem Check013.part1752 : Interval test 1752 1760 :=
  interval_of_check _ 1752 8 (by decide +kernel)
theorem Check013.part1760 : Interval test 1760 1768 :=
  interval_of_check _ 1760 8 (by decide +kernel)
theorem Check013.part1768 : Interval test 1768 1776 :=
  interval_of_check _ 1768 8 (by decide +kernel)
theorem Check013.part1776 : Interval test 1776 1784 :=
  interval_of_check _ 1776 8 (by decide +kernel)
theorem Check013.part1784 : Interval test 1784 1792 :=
  interval_of_check _ 1784 8 (by decide +kernel)
theorem Check013.checked : Interval test 1664 1792 :=
  (FiniteChecks.interval_append test 1664 1728 1792
  (FiniteChecks.interval_append test 1664 1696 1728
  (FiniteChecks.interval_append test 1664 1680 1696
  (FiniteChecks.interval_append test 1664 1672 1680
  Check013.part1664
  Check013.part1672)
  (FiniteChecks.interval_append test 1680 1688 1696
  Check013.part1680
  Check013.part1688))
  (FiniteChecks.interval_append test 1696 1712 1728
  (FiniteChecks.interval_append test 1696 1704 1712
  Check013.part1696
  Check013.part1704)
  (FiniteChecks.interval_append test 1712 1720 1728
  Check013.part1712
  Check013.part1720)))
  (FiniteChecks.interval_append test 1728 1760 1792
  (FiniteChecks.interval_append test 1728 1744 1760
  (FiniteChecks.interval_append test 1728 1736 1744
  Check013.part1728
  Check013.part1736)
  (FiniteChecks.interval_append test 1744 1752 1760
  Check013.part1744
  Check013.part1752))
  (FiniteChecks.interval_append test 1760 1776 1792
  (FiniteChecks.interval_append test 1760 1768 1776
  Check013.part1760
  Check013.part1768)
  (FiniteChecks.interval_append test 1776 1784 1792
  Check013.part1776
  Check013.part1784))))
theorem Check014.part1792 : Interval test 1792 1800 :=
  interval_of_check _ 1792 8 (by decide +kernel)
theorem Check014.part1800 : Interval test 1800 1808 :=
  interval_of_check _ 1800 8 (by decide +kernel)
theorem Check014.part1808 : Interval test 1808 1816 :=
  interval_of_check _ 1808 8 (by decide +kernel)
theorem Check014.part1816 : Interval test 1816 1824 :=
  interval_of_check _ 1816 8 (by decide +kernel)
theorem Check014.part1824 : Interval test 1824 1832 :=
  interval_of_check _ 1824 8 (by decide +kernel)
theorem Check014.part1832 : Interval test 1832 1840 :=
  interval_of_check _ 1832 8 (by decide +kernel)
theorem Check014.part1840 : Interval test 1840 1848 :=
  interval_of_check _ 1840 8 (by decide +kernel)
theorem Check014.part1848 : Interval test 1848 1856 :=
  interval_of_check _ 1848 8 (by decide +kernel)
theorem Check014.part1856 : Interval test 1856 1864 :=
  interval_of_check _ 1856 8 (by decide +kernel)
theorem Check014.part1864 : Interval test 1864 1872 :=
  interval_of_check _ 1864 8 (by decide +kernel)
theorem Check014.part1872 : Interval test 1872 1880 :=
  interval_of_check _ 1872 8 (by decide +kernel)
theorem Check014.part1880 : Interval test 1880 1888 :=
  interval_of_check _ 1880 8 (by decide +kernel)
theorem Check014.part1888 : Interval test 1888 1896 :=
  interval_of_check _ 1888 8 (by decide +kernel)
theorem Check014.part1896 : Interval test 1896 1904 :=
  interval_of_check _ 1896 8 (by decide +kernel)
theorem Check014.part1904 : Interval test 1904 1912 :=
  interval_of_check _ 1904 8 (by decide +kernel)
theorem Check014.part1912 : Interval test 1912 1920 :=
  interval_of_check _ 1912 8 (by decide +kernel)
theorem Check014.checked : Interval test 1792 1920 :=
  (FiniteChecks.interval_append test 1792 1856 1920
  (FiniteChecks.interval_append test 1792 1824 1856
  (FiniteChecks.interval_append test 1792 1808 1824
  (FiniteChecks.interval_append test 1792 1800 1808
  Check014.part1792
  Check014.part1800)
  (FiniteChecks.interval_append test 1808 1816 1824
  Check014.part1808
  Check014.part1816))
  (FiniteChecks.interval_append test 1824 1840 1856
  (FiniteChecks.interval_append test 1824 1832 1840
  Check014.part1824
  Check014.part1832)
  (FiniteChecks.interval_append test 1840 1848 1856
  Check014.part1840
  Check014.part1848)))
  (FiniteChecks.interval_append test 1856 1888 1920
  (FiniteChecks.interval_append test 1856 1872 1888
  (FiniteChecks.interval_append test 1856 1864 1872
  Check014.part1856
  Check014.part1864)
  (FiniteChecks.interval_append test 1872 1880 1888
  Check014.part1872
  Check014.part1880))
  (FiniteChecks.interval_append test 1888 1904 1920
  (FiniteChecks.interval_append test 1888 1896 1904
  Check014.part1888
  Check014.part1896)
  (FiniteChecks.interval_append test 1904 1912 1920
  Check014.part1904
  Check014.part1912))))
theorem Check015.part1920 : Interval test 1920 1928 :=
  interval_of_check _ 1920 8 (by decide +kernel)
theorem Check015.part1928 : Interval test 1928 1936 :=
  interval_of_check _ 1928 8 (by decide +kernel)
theorem Check015.part1936 : Interval test 1936 1944 :=
  interval_of_check _ 1936 8 (by decide +kernel)
theorem Check015.part1944 : Interval test 1944 1952 :=
  interval_of_check _ 1944 8 (by decide +kernel)
theorem Check015.part1952 : Interval test 1952 1960 :=
  interval_of_check _ 1952 8 (by decide +kernel)
theorem Check015.part1960 : Interval test 1960 1968 :=
  interval_of_check _ 1960 8 (by decide +kernel)
theorem Check015.part1968 : Interval test 1968 1976 :=
  interval_of_check _ 1968 8 (by decide +kernel)
theorem Check015.part1976 : Interval test 1976 1984 :=
  interval_of_check _ 1976 8 (by decide +kernel)
theorem Check015.part1984 : Interval test 1984 1992 :=
  interval_of_check _ 1984 8 (by decide +kernel)
theorem Check015.part1992 : Interval test 1992 2000 :=
  interval_of_check _ 1992 8 (by decide +kernel)
theorem Check015.part2000 : Interval test 2000 2008 :=
  interval_of_check _ 2000 8 (by decide +kernel)
theorem Check015.part2008 : Interval test 2008 2016 :=
  interval_of_check _ 2008 8 (by decide +kernel)
theorem Check015.part2016 : Interval test 2016 2024 :=
  interval_of_check _ 2016 8 (by decide +kernel)
theorem Check015.part2024 : Interval test 2024 2032 :=
  interval_of_check _ 2024 8 (by decide +kernel)
theorem Check015.part2032 : Interval test 2032 2040 :=
  interval_of_check _ 2032 8 (by decide +kernel)
theorem Check015.part2040 : Interval test 2040 2048 :=
  interval_of_check _ 2040 8 (by decide +kernel)
theorem Check015.checked : Interval test 1920 2048 :=
  (FiniteChecks.interval_append test 1920 1984 2048
  (FiniteChecks.interval_append test 1920 1952 1984
  (FiniteChecks.interval_append test 1920 1936 1952
  (FiniteChecks.interval_append test 1920 1928 1936
  Check015.part1920
  Check015.part1928)
  (FiniteChecks.interval_append test 1936 1944 1952
  Check015.part1936
  Check015.part1944))
  (FiniteChecks.interval_append test 1952 1968 1984
  (FiniteChecks.interval_append test 1952 1960 1968
  Check015.part1952
  Check015.part1960)
  (FiniteChecks.interval_append test 1968 1976 1984
  Check015.part1968
  Check015.part1976)))
  (FiniteChecks.interval_append test 1984 2016 2048
  (FiniteChecks.interval_append test 1984 2000 2016
  (FiniteChecks.interval_append test 1984 1992 2000
  Check015.part1984
  Check015.part1992)
  (FiniteChecks.interval_append test 2000 2008 2016
  Check015.part2000
  Check015.part2008))
  (FiniteChecks.interval_append test 2016 2032 2048
  (FiniteChecks.interval_append test 2016 2024 2032
  Check015.part2016
  Check015.part2024)
  (FiniteChecks.interval_append test 2032 2040 2048
  Check015.part2032
  Check015.part2040))))
end Papers.RationalityTen.SharedTriangleCounts
