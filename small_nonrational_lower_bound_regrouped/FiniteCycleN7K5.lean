module

public import FiniteCycleData7
public import FiniteInjectionWitnessChecks

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FiniteCycleCandidates.N7
open MatroidChecked

noncomputable def coverageTable5 : LiteralLookup ℕ := (.node 1637 (.node 1100 (.node 782 (.node 560 (.node 369 (.node 195 (.node 160 (.node 153 (.node 151 (.node 150 (.leaf 0) (.leaf 110)) (.node 152 (.leaf 112) (.leaf 114))) (.node 157 (.node 154 (.leaf 120) (.leaf 0)) (.node 158 (.leaf 111) (.node 159 (.leaf 113) (.leaf 115))))) (.node 167 (.node 164 (.node 161 (.leaf 121) (.leaf 0)) (.node 165 (.leaf 117) (.node 166 (.leaf 119) (.leaf 125)))) (.node 192 (.node 168 (.leaf 127) (.leaf 0)) (.node 193 (.leaf 116) (.node 194 (.leaf 118) (.leaf 124)))))) (.node 208 (.node 201 (.node 199 (.node 196 (.leaf 126) (.leaf 0)) (.node 200 (.leaf 122) (.leaf 128))) (.node 203 (.node 202 (.leaf 130) (.leaf 132)) (.node 206 (.leaf 0) (.node 207 (.leaf 123) (.leaf 129))))) (.node 362 (.node 210 (.node 209 (.leaf 131) (.leaf 133)) (.node 360 (.leaf 0) (.node 361 (.leaf 115) (.leaf 114)))) (.node 364 (.node 363 (.leaf 112) (.leaf 118)) (.node 367 (.leaf 0) (.node 368 (.leaf 113) (.leaf 111))))))) (.node 417 (.node 403 (.node 375 (.node 371 (.node 370 (.leaf 110) (.leaf 116)) (.node 374 (.leaf 0) (.leaf 119))) (.node 377 (.node 376 (.leaf 117) (.leaf 123)) (.node 378 (.leaf 122) (.node 402 (.leaf 0) (.leaf 121))))) (.node 410 (.node 405 (.node 404 (.leaf 120) (.leaf 126)) (.node 406 (.leaf 124) (.node 409 (.leaf 0) (.leaf 127)))) (.node 412 (.node 411 (.leaf 133) (.leaf 132)) (.node 413 (.leaf 130) (.node 416 (.leaf 0) (.leaf 125)))))) (.node 527 (.node 519 (.node 419 (.node 418 (.leaf 131) (.leaf 129)) (.node 420 (.leaf 128) (.node 518 (.leaf 0) (.leaf 115)))) (.node 521 (.node 520 (.leaf 110) (.leaf 134)) (.node 525 (.leaf 0) (.node 526 (.leaf 114) (.leaf 112))))) (.node 535 (.node 532 (.node 528 (.leaf 136) (.leaf 0)) (.node 533 (.leaf 112) (.node 534 (.leaf 114) (.leaf 138)))) (.node 540 (.node 539 (.leaf 0) (.leaf 118)) (.node 541 (.leaf 120) (.node 542 (.leaf 144) (.leaf 0)))))))) (.node 617 (.node 582 (.node 572 (.node 567 (.node 562 (.node 561 (.leaf 113) (.leaf 111)) (.node 563 (.leaf 135) (.leaf 0))) (.node 569 (.node 568 (.leaf 111) (.leaf 113)) (.node 570 (.leaf 137) (.node 571 (.leaf 139) (.leaf 138))))) (.node 577 (.node 574 (.node 573 (.leaf 136) (.leaf 142)) (.node 575 (.leaf 110) (.node 576 (.leaf 115) (.leaf 139)))) (.node 579 (.node 578 (.leaf 137) (.leaf 135)) (.node 580 (.leaf 134) (.node 581 (.leaf 140) (.leaf 116)))))) (.node 604 (.node 586 (.node 584 (.node 583 (.leaf 121) (.leaf 145)) (.node 585 (.leaf 143) (.leaf 141))) (.node 588 (.node 587 (.leaf 147) (.leaf 146)) (.node 602 (.leaf 0) (.node 603 (.leaf 119) (.leaf 117))))) (.node 612 (.node 609 (.node 605 (.leaf 141) (.leaf 0)) (.node 610 (.leaf 117) (.node 611 (.leaf 119) (.leaf 143)))) (.node 614 (.node 613 (.leaf 145) (.leaf 144)) (.node 615 (.leaf 150) (.node 616 (.leaf 148) (.leaf 123))))))) (.node 736 (.node 626 (.node 621 (.node 619 (.node 618 (.leaf 125) (.leaf 149)) (.node 620 (.leaf 151) (.leaf 157))) (.node 623 (.node 622 (.leaf 156) (.leaf 154)) (.node 624 (.leaf 122) (.node 625 (.leaf 127) (.leaf 151))))) (.node 728 (.node 628 (.node 627 (.leaf 149) (.leaf 155)) (.node 629 (.leaf 153) (.node 630 (.leaf 152) (.leaf 0)))) (.node 730 (.node 729 (.leaf 121) (.leaf 116)) (.node 731 (.leaf 140) (.node 735 (.leaf 0) (.leaf 120)))))) (.node 752 (.node 744 (.node 738 (.node 737 (.leaf 118) (.leaf 142)) (.node 742 (.leaf 0) (.node 743 (.leaf 126) (.leaf 124)))) (.node 749 (.node 745 (.leaf 148) (.leaf 0)) (.node 750 (.leaf 124) (.node 751 (.leaf 126) (.leaf 150))))) (.node 777 (.node 771 (.node 770 (.leaf 0) (.leaf 127)) (.node 772 (.leaf 122) (.node 773 (.leaf 146) (.leaf 0)))) (.node 779 (.node 778 (.leaf 133) (.leaf 128)) (.node 780 (.leaf 152) (.node 781 (.leaf 158) (.leaf 164))))))))) (.node 952 (.node 836 (.node 814 (.node 791 (.node 786 (.node 784 (.node 783 (.leaf 168) (.leaf 169)) (.node 785 (.leaf 132) (.leaf 130))) (.node 788 (.node 787 (.leaf 154) (.leaf 160)) (.node 789 (.leaf 166) (.node 790 (.leaf 169) (.leaf 168))))) (.node 796 (.node 793 (.node 792 (.leaf 130) (.leaf 132)) (.node 794 (.leaf 156) (.node 795 (.leaf 162) (.leaf 167)))) (.node 798 (.node 797 (.leaf 165) (.leaf 164)) (.node 812 (.leaf 0) (.node 813 (.leaf 125) (.leaf 123)))))) (.node 826 (.node 821 (.node 819 (.node 815 (.leaf 147) (.leaf 0)) (.node 820 (.leaf 131) (.leaf 129))) (.node 823 (.node 822 (.leaf 153) (.leaf 159)) (.node 824 (.leaf 165) (.node 825 (.leaf 167) (.leaf 166))))) (.node 831 (.node 828 (.node 827 (.leaf 129) (.leaf 131)) (.node 829 (.leaf 155) (.node 830 (.leaf 161) (.leaf 163)))) (.node 833 (.node 832 (.leaf 162) (.leaf 160)) (.node 834 (.leaf 128) (.node 835 (.leaf 133) (.leaf 157))))))) (.node 882 (.node 868 (.node 840 (.node 838 (.node 837 (.leaf 163) (.leaf 161)) (.node 839 (.leaf 159) (.leaf 158))) (.node 865 (.node 864 (.leaf 0) (.leaf 114)) (.node 866 (.leaf 115) (.node 867 (.leaf 113) (.leaf 119))))) (.node 875 (.node 872 (.node 871 (.leaf 0) (.leaf 112)) (.node 873 (.leaf 110) (.node 874 (.leaf 111) (.leaf 117)))) (.node 879 (.node 878 (.leaf 0) (.leaf 118)) (.node 880 (.leaf 116) (.node 881 (.leaf 122) (.leaf 123)))))) (.node 917 (.node 910 (.node 907 (.node 906 (.leaf 0) (.leaf 112)) (.node 908 (.leaf 110) (.node 909 (.leaf 111) (.leaf 117)))) (.node 914 (.node 913 (.leaf 0) (.leaf 114)) (.node 915 (.leaf 115) (.node 916 (.leaf 113) (.leaf 119))))) (.node 924 (.node 921 (.node 920 (.leaf 0) (.leaf 120)) (.node 922 (.leaf 121) (.node 923 (.leaf 127) (.leaf 125)))) (.node 949 (.node 948 (.leaf 0) (.leaf 136)) (.node 950 (.leaf 134) (.node 951 (.leaf 135) (.leaf 141)))))))) (.node 1049 (.node 1000 (.node 965 (.node 958 (.node 956 (.node 955 (.leaf 0) (.leaf 138)) (.node 957 (.leaf 139) (.leaf 137))) (.node 962 (.node 959 (.leaf 143) (.leaf 0)) (.node 963 (.leaf 144) (.node 964 (.leaf 145) (.leaf 151))))) (.node 993 (.node 990 (.node 966 (.leaf 149) (.leaf 0)) (.node 991 (.leaf 134) (.node 992 (.leaf 136) (.leaf 138)))) (.node 997 (.node 994 (.leaf 144) (.leaf 0)) (.node 998 (.leaf 135) (.node 999 (.leaf 137) (.leaf 139)))))) (.node 1035 (.node 1007 (.node 1004 (.node 1001 (.leaf 145) (.leaf 0)) (.node 1005 (.leaf 141) (.node 1006 (.leaf 143) (.leaf 149)))) (.node 1032 (.node 1008 (.leaf 151) (.leaf 0)) (.node 1033 (.leaf 140) (.node 1034 (.leaf 142) (.leaf 148))))) (.node 1042 (.node 1039 (.node 1036 (.leaf 150) (.leaf 0)) (.node 1040 (.leaf 146) (.node 1041 (.leaf 152) (.leaf 154)))) (.node 1046 (.node 1043 (.leaf 156) (.leaf 0)) (.node 1047 (.leaf 147) (.node 1048 (.leaf 153) (.leaf 155))))))) (.node 1076 (.node 1062 (.node 1055 (.node 1053 (.node 1050 (.leaf 157) (.leaf 0)) (.node 1054 (.leaf 113) (.leaf 111))) (.node 1057 (.node 1056 (.leaf 110) (.leaf 116)) (.node 1060 (.leaf 0) (.node 1061 (.leaf 111) (.leaf 113))))) (.node 1069 (.node 1064 (.node 1063 (.leaf 115) (.leaf 121)) (.node 1067 (.leaf 0) (.node 1068 (.leaf 135) (.leaf 137)))) (.node 1071 (.node 1070 (.leaf 139) (.leaf 145)) (.node 1074 (.leaf 0) (.node 1075 (.leaf 138) (.leaf 139)))))) (.node 1090 (.node 1083 (.node 1078 (.node 1077 (.leaf 137) (.leaf 143)) (.node 1081 (.leaf 0) (.node 1082 (.leaf 136) (.leaf 134)))) (.node 1085 (.node 1084 (.leaf 135) (.leaf 141)) (.node 1088 (.leaf 0) (.node 1089 (.leaf 142) (.leaf 140))))) (.node 1095 (.node 1092 (.node 1091 (.leaf 146) (.leaf 147)) (.node 1093 (.leaf 110) (.node 1094 (.leaf 115) (.leaf 139)))) (.node 1097 (.node 1096 (.leaf 137) (.leaf 135)) (.node 1098 (.leaf 134) (.node 1099 (.leaf 140) (.leaf 134)))))))))) (.node 1389 (.node 1228 (.node 1162 (.node 1125 (.node 1111 (.node 1104 (.node 1102 (.node 1101 (.leaf 170) (.leaf 175)) (.node 1103 (.leaf 173) (.leaf 171))) (.node 1106 (.node 1105 (.leaf 170) (.leaf 176)) (.node 1109 (.leaf 0) (.node 1110 (.leaf 171) (.leaf 173))))) (.node 1118 (.node 1113 (.node 1112 (.leaf 175) (.leaf 181)) (.node 1116 (.leaf 0) (.node 1117 (.leaf 174) (.leaf 175)))) (.node 1120 (.node 1119 (.leaf 173) (.leaf 179)) (.node 1123 (.leaf 0) (.node 1124 (.leaf 172) (.leaf 170)))))) (.node 1136 (.node 1131 (.node 1127 (.node 1126 (.leaf 171) (.leaf 177)) (.node 1130 (.leaf 0) (.leaf 178))) (.node 1133 (.node 1132 (.leaf 176) (.leaf 182)) (.node 1134 (.leaf 183) (.node 1135 (.leaf 112) (.leaf 114))))) (.node 1144 (.node 1141 (.node 1137 (.leaf 138) (.leaf 0)) (.node 1142 (.leaf 136) (.node 1143 (.leaf 172) (.leaf 174)))) (.node 1159 (.node 1158 (.leaf 0) (.leaf 172)) (.node 1160 (.leaf 170) (.node 1161 (.leaf 171) (.leaf 177))))))) (.node 1201 (.node 1175 (.node 1168 (.node 1166 (.node 1165 (.leaf 0) (.leaf 174)) (.node 1167 (.leaf 175) (.leaf 173))) (.node 1172 (.node 1169 (.leaf 179) (.leaf 0)) (.node 1173 (.leaf 180) (.node 1174 (.leaf 181) (.leaf 187))))) (.node 1183 (.node 1177 (.node 1176 (.leaf 185) (.leaf 114)) (.node 1178 (.leaf 112) (.node 1179 (.leaf 136) (.leaf 0)))) (.node 1185 (.node 1184 (.leaf 138) (.leaf 174)) (.node 1186 (.leaf 172) (.node 1200 (.leaf 0) (.leaf 170)))))) (.node 1215 (.node 1208 (.node 1203 (.node 1202 (.leaf 172) (.leaf 174)) (.node 1204 (.leaf 180) (.node 1207 (.leaf 0) (.leaf 171)))) (.node 1210 (.node 1209 (.leaf 173) (.leaf 175)) (.node 1211 (.leaf 181) (.node 1214 (.leaf 0) (.leaf 177))))) (.node 1220 (.node 1217 (.node 1216 (.leaf 179) (.leaf 185)) (.node 1218 (.leaf 187) (.node 1219 (.leaf 120) (.leaf 118)))) (.node 1225 (.node 1221 (.leaf 142) (.leaf 0)) (.node 1226 (.leaf 144) (.node 1227 (.leaf 180) (.leaf 178)))))))) (.node 1310 (.node 1266 (.node 1252 (.node 1245 (.node 1243 (.node 1242 (.leaf 0) (.leaf 176)) (.node 1244 (.leaf 178) (.leaf 184))) (.node 1249 (.node 1246 (.leaf 186) (.leaf 0)) (.node 1250 (.leaf 182) (.node 1251 (.leaf 188) (.leaf 190))))) (.node 1259 (.node 1256 (.node 1253 (.leaf 192) (.leaf 0)) (.node 1257 (.leaf 183) (.node 1258 (.leaf 189) (.leaf 191)))) (.node 1263 (.node 1260 (.leaf 193) (.leaf 0)) (.node 1264 (.leaf 115) (.node 1265 (.leaf 114) (.leaf 112)))))) (.node 1280 (.node 1273 (.node 1270 (.node 1267 (.leaf 118) (.leaf 0)) (.node 1271 (.leaf 110) (.node 1272 (.leaf 112) (.leaf 114)))) (.node 1277 (.node 1274 (.leaf 120) (.leaf 0)) (.node 1278 (.leaf 134) (.node 1279 (.leaf 136) (.leaf 138))))) (.node 1305 (.node 1302 (.node 1281 (.leaf 144) (.leaf 0)) (.node 1303 (.leaf 111) (.node 1304 (.leaf 113) (.leaf 137)))) (.node 1307 (.node 1306 (.leaf 139) (.leaf 138)) (.node 1308 (.leaf 136) (.node 1309 (.leaf 142) (.leaf 135))))))) (.node 1354 (.node 1321 (.node 1314 (.node 1312 (.node 1311 (.leaf 171) (.leaf 173)) (.node 1313 (.leaf 175) (.leaf 174))) (.node 1316 (.node 1315 (.leaf 172) (.leaf 178)) (.node 1319 (.leaf 0) (.node 1320 (.leaf 170) (.leaf 172))))) (.node 1346 (.node 1323 (.node 1322 (.leaf 174) (.leaf 180)) (.node 1344 (.leaf 0) (.node 1345 (.leaf 113) (.leaf 111)))) (.node 1351 (.node 1347 (.leaf 135) (.leaf 0)) (.node 1352 (.leaf 137) (.node 1353 (.leaf 173) (.leaf 171)))))) (.node 1373 (.node 1365 (.node 1359 (.node 1358 (.leaf 0) (.leaf 139)) (.node 1360 (.leaf 175) (.node 1361 (.leaf 170) (.leaf 0)))) (.node 1367 (.node 1366 (.leaf 138) (.leaf 174)) (.node 1368 (.leaf 172) (.node 1372 (.leaf 0) (.leaf 136))))) (.node 1381 (.node 1375 (.node 1374 (.leaf 172) (.leaf 174)) (.node 1379 (.leaf 0) (.node 1380 (.leaf 142) (.leaf 178)))) (.node 1386 (.node 1382 (.leaf 180) (.leaf 0)) (.node 1387 (.leaf 115) (.node 1388 (.leaf 110) (.leaf 134))))))))) (.node 1490 (.node 1442 (.node 1417 (.node 1407 (.node 1396 (.node 1394 (.node 1393 (.leaf 0) (.leaf 139)) (.node 1395 (.leaf 175) (.leaf 170))) (.node 1401 (.node 1400 (.leaf 0) (.leaf 137)) (.node 1402 (.leaf 173) (.node 1403 (.leaf 171) (.leaf 0))))) (.node 1412 (.node 1409 (.node 1408 (.leaf 135) (.leaf 171)) (.node 1410 (.leaf 173) (.node 1411 (.leaf 175) (.leaf 174)))) (.node 1414 (.node 1413 (.leaf 172) (.leaf 178)) (.node 1415 (.leaf 134) (.node 1416 (.leaf 170) (.leaf 175)))))) (.node 1426 (.node 1421 (.node 1419 (.node 1418 (.leaf 173) (.leaf 171)) (.node 1420 (.leaf 170) (.leaf 176))) (.node 1423 (.node 1422 (.leaf 140) (.leaf 176)) (.node 1424 (.leaf 181) (.node 1425 (.leaf 179) (.leaf 177))))) (.node 1431 (.node 1428 (.node 1427 (.leaf 183) (.leaf 182)) (.node 1429 (.leaf 121) (.node 1430 (.leaf 116) (.leaf 140)))) (.node 1436 (.node 1435 (.leaf 0) (.leaf 145)) (.node 1437 (.leaf 181) (.node 1438 (.leaf 176) (.leaf 0))))))) (.node 1464 (.node 1454 (.node 1449 (.node 1444 (.node 1443 (.leaf 143) (.leaf 179)) (.node 1445 (.leaf 177) (.leaf 0))) (.node 1451 (.node 1450 (.leaf 141) (.leaf 177)) (.node 1452 (.leaf 179) (.node 1453 (.leaf 181) (.leaf 180))))) (.node 1459 (.node 1456 (.node 1455 (.leaf 186) (.leaf 184)) (.node 1457 (.leaf 147) (.node 1458 (.leaf 183) (.leaf 185)))) (.node 1461 (.node 1460 (.leaf 187) (.leaf 193)) (.node 1462 (.leaf 192) (.node 1463 (.leaf 190) (.leaf 146)))))) (.node 1476 (.node 1469 (.node 1466 (.node 1465 (.leaf 182) (.leaf 187)) (.node 1467 (.leaf 185) (.node 1468 (.leaf 191) (.leaf 189)))) (.node 1473 (.node 1470 (.leaf 188) (.leaf 0)) (.node 1474 (.leaf 121) (.node 1475 (.leaf 120) (.leaf 126))))) (.node 1483 (.node 1480 (.node 1477 (.leaf 124) (.leaf 0)) (.node 1481 (.leaf 116) (.node 1482 (.leaf 118) (.leaf 124)))) (.node 1487 (.node 1484 (.leaf 126) (.leaf 0)) (.node 1488 (.leaf 140) (.node 1489 (.leaf 142) (.leaf 148)))))))) (.node 1583 (.node 1531 (.node 1519 (.node 1514 (.node 1512 (.node 1491 (.leaf 150) (.leaf 0)) (.node 1513 (.leaf 117) (.leaf 119))) (.node 1516 (.node 1515 (.leaf 143) (.leaf 145)) (.node 1517 (.leaf 144) (.node 1518 (.leaf 150) (.leaf 148))))) (.node 1524 (.node 1521 (.node 1520 (.leaf 141) (.leaf 177)) (.node 1522 (.leaf 179) (.node 1523 (.leaf 181) (.leaf 180)))) (.node 1526 (.node 1525 (.leaf 186) (.leaf 184)) (.node 1529 (.leaf 0) (.node 1530 (.leaf 176) (.leaf 178)))))) (.node 1564 (.node 1556 (.node 1533 (.node 1532 (.leaf 184) (.leaf 186)) (.node 1554 (.leaf 0) (.node 1555 (.leaf 119) (.leaf 117)))) (.node 1561 (.node 1557 (.leaf 141) (.leaf 0)) (.node 1562 (.leaf 143) (.node 1563 (.leaf 179) (.leaf 177))))) (.node 1575 (.node 1569 (.node 1568 (.leaf 0) (.leaf 145)) (.node 1570 (.leaf 181) (.node 1571 (.leaf 176) (.leaf 0)))) (.node 1577 (.node 1576 (.leaf 144) (.leaf 180)) (.node 1578 (.leaf 178) (.node 1582 (.leaf 0) (.leaf 150))))))) (.node 1617 (.node 1598 (.node 1590 (.node 1585 (.node 1584 (.leaf 186) (.leaf 184)) (.node 1589 (.leaf 0) (.leaf 148))) (.node 1592 (.node 1591 (.leaf 184) (.leaf 186)) (.node 1596 (.leaf 0) (.node 1597 (.leaf 125) (.leaf 123))))) (.node 1606 (.node 1603 (.node 1599 (.leaf 147) (.leaf 0)) (.node 1604 (.leaf 149) (.node 1605 (.leaf 185) (.leaf 183)))) (.node 1611 (.node 1610 (.leaf 0) (.leaf 151)) (.node 1612 (.leaf 187) (.node 1613 (.leaf 182) (.leaf 0)))))) (.node 1627 (.node 1622 (.node 1619 (.node 1618 (.leaf 157) (.leaf 193)) (.node 1620 (.leaf 188) (.node 1621 (.leaf 194) (.leaf 200)))) (.node 1624 (.node 1623 (.leaf 204) (.leaf 205)) (.node 1625 (.leaf 156) (.node 1626 (.leaf 192) (.leaf 190))))) (.node 1632 (.node 1629 (.node 1628 (.leaf 196) (.leaf 202)) (.node 1630 (.leaf 205) (.node 1631 (.leaf 204) (.leaf 154)))) (.node 1634 (.node 1633 (.leaf 190) (.leaf 192)) (.node 1635 (.leaf 198) (.node 1636 (.leaf 203) (.leaf 201))))))))))) (.node 2190 (.node 1949 (.node 1804 (.node 1707 (.node 1665 (.node 1652 (.node 1641 (.node 1639 (.node 1638 (.leaf 200) (.leaf 127)) (.node 1640 (.leaf 122) (.leaf 146))) (.node 1646 (.node 1645 (.leaf 0) (.leaf 151)) (.node 1647 (.leaf 187) (.node 1648 (.leaf 182) (.leaf 0))))) (.node 1660 (.node 1654 (.node 1653 (.leaf 149) (.leaf 185)) (.node 1655 (.leaf 183) (.node 1659 (.leaf 0) (.leaf 155)))) (.node 1662 (.node 1661 (.leaf 191) (.leaf 189)) (.node 1663 (.leaf 195) (.node 1664 (.leaf 201) (.leaf 203)))))) (.node 1674 (.node 1669 (.node 1667 (.node 1666 (.leaf 202) (.leaf 153)) (.node 1668 (.leaf 189) (.leaf 191))) (.node 1671 (.node 1670 (.leaf 197) (.leaf 199)) (.node 1672 (.leaf 198) (.node 1673 (.leaf 196) (.leaf 152))))) (.node 1679 (.node 1676 (.node 1675 (.leaf 188) (.leaf 193)) (.node 1677 (.leaf 199) (.node 1678 (.leaf 197) (.leaf 195)))) (.node 1704 (.node 1680 (.leaf 194) (.leaf 0)) (.node 1705 (.leaf 120) (.node 1706 (.leaf 121) (.leaf 127))))))) (.node 1755 (.node 1720 (.node 1713 (.node 1711 (.node 1708 (.leaf 125) (.leaf 0)) (.node 1712 (.leaf 126) (.leaf 132))) (.node 1715 (.node 1714 (.leaf 133) (.leaf 131)) (.node 1718 (.leaf 0) (.node 1719 (.leaf 124) (.leaf 130))))) (.node 1748 (.node 1722 (.node 1721 (.leaf 128) (.leaf 129)) (.node 1746 (.leaf 0) (.node 1747 (.leaf 118) (.leaf 116)))) (.node 1750 (.node 1749 (.leaf 122) (.leaf 123)) (.node 1753 (.leaf 0) (.node 1754 (.leaf 124) (.leaf 130)))))) (.node 1790 (.node 1762 (.node 1757 (.node 1756 (.leaf 128) (.leaf 129)) (.node 1760 (.leaf 0) (.node 1761 (.leaf 126) (.leaf 132)))) (.node 1764 (.node 1763 (.leaf 133) (.leaf 131)) (.node 1788 (.leaf 0) (.node 1789 (.leaf 142) (.leaf 140))))) (.node 1797 (.node 1792 (.node 1791 (.leaf 146) (.leaf 147)) (.node 1795 (.leaf 0) (.node 1796 (.leaf 148) (.leaf 154)))) (.node 1799 (.node 1798 (.leaf 152) (.leaf 153)) (.node 1802 (.leaf 0) (.node 1803 (.leaf 150) (.leaf 156)))))))) (.node 1900 (.node 1873 (.node 1838 (.node 1831 (.node 1806 (.node 1805 (.leaf 157) (.leaf 155)) (.node 1830 (.leaf 0) (.leaf 169))) (.node 1833 (.node 1832 (.leaf 168) (.leaf 164)) (.node 1834 (.leaf 165) (.node 1837 (.leaf 0) (.leaf 166))))) (.node 1845 (.node 1840 (.node 1839 (.leaf 160) (.leaf 158)) (.node 1841 (.leaf 159) (.node 1844 (.leaf 0) (.leaf 167)))) (.node 1847 (.node 1846 (.leaf 162) (.leaf 163)) (.node 1848 (.leaf 161) (.node 1872 (.leaf 0) (.leaf 168)))))) (.node 1886 (.node 1879 (.node 1875 (.node 1874 (.leaf 169) (.leaf 166)) (.node 1876 (.leaf 167) (.leaf 0))) (.node 1881 (.node 1880 (.leaf 164) (.leaf 158)) (.node 1882 (.leaf 160) (.node 1883 (.leaf 162) (.leaf 0))))) (.node 1893 (.node 1888 (.node 1887 (.leaf 165) (.leaf 159)) (.node 1889 (.leaf 161) (.node 1890 (.leaf 163) (.leaf 0)))) (.node 1895 (.node 1894 (.leaf 119) (.leaf 117)) (.node 1896 (.leaf 123) (.node 1897 (.leaf 122) (.leaf 0))))))) (.node 1925 (.node 1911 (.node 1904 (.node 1902 (.node 1901 (.leaf 117) (.leaf 119)) (.node 1903 (.leaf 125) (.leaf 127))) (.node 1908 (.node 1907 (.leaf 0) (.leaf 141)) (.node 1909 (.leaf 143) (.node 1910 (.leaf 149) (.leaf 151))))) (.node 1918 (.node 1915 (.node 1914 (.leaf 0) (.leaf 144)) (.node 1916 (.leaf 145) (.node 1917 (.leaf 151) (.leaf 149)))) (.node 1922 (.node 1921 (.leaf 0) (.leaf 150)) (.node 1923 (.leaf 156) (.node 1924 (.leaf 157) (.leaf 155)))))) (.node 1937 (.node 1932 (.node 1929 (.node 1928 (.leaf 0) (.leaf 148)) (.node 1930 (.leaf 154) (.node 1931 (.leaf 152) (.leaf 153)))) (.node 1934 (.node 1933 (.leaf 116) (.leaf 121)) (.node 1935 (.leaf 145) (.node 1936 (.leaf 143) (.leaf 141))))) (.node 1942 (.node 1939 (.node 1938 (.leaf 147) (.leaf 146)) (.node 1940 (.leaf 140) (.node 1941 (.leaf 176) (.leaf 181)))) (.node 1944 (.node 1943 (.leaf 179) (.leaf 177)) (.node 1945 (.leaf 183) (.node 1946 (.leaf 182) (.leaf 0))))))))) (.node 2090 (.node 2013 (.node 1974 (.node 1960 (.node 1953 (.node 1951 (.node 1950 (.leaf 177) (.leaf 179)) (.node 1952 (.leaf 185) (.leaf 187))) (.node 1957 (.node 1956 (.leaf 0) (.leaf 180)) (.node 1958 (.leaf 181) (.node 1959 (.leaf 187) (.leaf 185))))) (.node 1967 (.node 1964 (.node 1963 (.leaf 0) (.leaf 186)) (.node 1965 (.leaf 192) (.node 1966 (.leaf 193) (.leaf 191)))) (.node 1971 (.node 1970 (.leaf 0) (.leaf 184)) (.node 1972 (.leaf 190) (.node 1973 (.leaf 188) (.leaf 189)))))) (.node 1999 (.node 1981 (.node 1976 (.node 1975 (.leaf 118) (.leaf 120)) (.node 1977 (.leaf 144) (.leaf 0))) (.node 1983 (.node 1982 (.leaf 142) (.leaf 178)) (.node 1984 (.leaf 180) (.node 1998 (.leaf 0) (.leaf 178))))) (.node 2006 (.node 2001 (.node 2000 (.leaf 176) (.leaf 182)) (.node 2002 (.leaf 183) (.node 2005 (.leaf 0) (.leaf 184)))) (.node 2008 (.node 2007 (.leaf 190) (.leaf 188)) (.node 2009 (.leaf 189) (.node 2012 (.leaf 0) (.leaf 186))))))) (.node 2050 (.node 2025 (.node 2017 (.node 2015 (.node 2014 (.leaf 192) (.leaf 193)) (.node 2016 (.leaf 191) (.leaf 124))) (.node 2019 (.node 2018 (.leaf 126) (.leaf 150)) (.node 2023 (.leaf 0) (.node 2024 (.leaf 148) (.leaf 184))))) (.node 2043 (.node 2040 (.node 2026 (.leaf 186) (.leaf 0)) (.node 2041 (.leaf 205) (.node 2042 (.leaf 204) (.leaf 200)))) (.node 2047 (.node 2044 (.leaf 201) (.leaf 0)) (.node 2048 (.leaf 202) (.node 2049 (.leaf 196) (.leaf 194)))))) (.node 2065 (.node 2057 (.node 2054 (.node 2051 (.leaf 195) (.leaf 0)) (.node 2055 (.leaf 203) (.node 2056 (.leaf 198) (.leaf 199)))) (.node 2059 (.node 2058 (.leaf 197) (.leaf 126)) (.node 2060 (.leaf 124) (.node 2061 (.leaf 148) (.leaf 0))))) (.node 2083 (.node 2067 (.node 2066 (.leaf 150) (.leaf 186)) (.node 2068 (.leaf 184) (.node 2082 (.leaf 0) (.leaf 204)))) (.node 2085 (.node 2084 (.leaf 205) (.leaf 202)) (.node 2086 (.leaf 203) (.node 2089 (.leaf 0) (.leaf 200)))))))) (.node 2143 (.node 2117 (.node 2103 (.node 2096 (.node 2092 (.node 2091 (.leaf 194) (.leaf 196)) (.node 2093 (.leaf 198) (.leaf 0))) (.node 2098 (.node 2097 (.leaf 201) (.leaf 195)) (.node 2099 (.leaf 197) (.node 2100 (.leaf 199) (.leaf 0))))) (.node 2110 (.node 2105 (.node 2104 (.leaf 125) (.leaf 131)) (.node 2106 (.leaf 129) (.node 2107 (.leaf 128) (.leaf 0)))) (.node 2112 (.node 2111 (.leaf 123) (.leaf 129)) (.node 2113 (.leaf 131) (.node 2114 (.leaf 133) (.leaf 0)))))) (.node 2131 (.node 2124 (.node 2119 (.node 2118 (.leaf 147) (.leaf 153)) (.node 2120 (.leaf 155) (.node 2121 (.leaf 157) (.leaf 0)))) (.node 2126 (.node 2125 (.leaf 165) (.leaf 159)) (.node 2127 (.leaf 161) (.node 2128 (.leaf 163) (.leaf 0))))) (.node 2138 (.node 2133 (.node 2132 (.leaf 167) (.leaf 162)) (.node 2134 (.leaf 163) (.node 2135 (.leaf 161) (.leaf 0)))) (.node 2140 (.node 2139 (.leaf 166) (.leaf 160)) (.node 2141 (.leaf 158) (.node 2142 (.leaf 159) (.leaf 122))))))) (.node 2166 (.node 2152 (.node 2147 (.node 2145 (.node 2144 (.leaf 127) (.leaf 151)) (.node 2146 (.leaf 149) (.leaf 155))) (.node 2149 (.node 2148 (.leaf 153) (.leaf 152)) (.node 2150 (.leaf 146) (.node 2151 (.leaf 182) (.leaf 187))))) (.node 2159 (.node 2154 (.node 2153 (.leaf 185) (.leaf 191)) (.node 2155 (.leaf 189) (.node 2156 (.leaf 188) (.leaf 0)))) (.node 2161 (.node 2160 (.leaf 183) (.leaf 189)) (.node 2162 (.leaf 191) (.node 2163 (.leaf 193) (.leaf 0)))))) (.node 2180 (.node 2173 (.node 2168 (.node 2167 (.leaf 201) (.leaf 195)) (.node 2169 (.leaf 197) (.node 2170 (.leaf 199) (.leaf 0)))) (.node 2175 (.node 2174 (.leaf 203) (.leaf 198)) (.node 2176 (.leaf 199) (.node 2177 (.leaf 197) (.leaf 0))))) (.node 2185 (.node 2182 (.node 2181 (.leaf 202) (.leaf 196)) (.node 2183 (.leaf 194) (.node 2184 (.leaf 195) (.leaf 128)))) (.node 2187 (.node 2186 (.leaf 133) (.leaf 157)) (.node 2188 (.leaf 163) (.node 2189 (.leaf 161) (.leaf 159)))))))))) (.node 2357 (.node 2267 (.node 2228 (.node 2209 (.node 2199 (.node 2194 (.node 2192 (.node 2191 (.leaf 158) (.leaf 152)) (.node 2193 (.leaf 188) (.leaf 193))) (.node 2196 (.node 2195 (.leaf 199) (.leaf 197)) (.node 2197 (.leaf 195) (.node 2198 (.leaf 194) (.leaf 158))))) (.node 2204 (.node 2201 (.node 2200 (.leaf 194) (.leaf 206)) (.node 2202 (.leaf 211) (.node 2203 (.leaf 209) (.leaf 207)))) (.node 2206 (.node 2205 (.leaf 206) (.leaf 164)) (.node 2207 (.leaf 200) (.node 2208 (.leaf 212) (.leaf 213)))))) (.node 2218 (.node 2213 (.node 2211 (.node 2210 (.leaf 207) (.leaf 209)) (.node 2212 (.leaf 211) (.leaf 168))) (.node 2215 (.node 2214 (.leaf 204) (.leaf 216)) (.node 2216 (.leaf 215) (.node 2217 (.leaf 210) (.leaf 211))))) (.node 2223 (.node 2220 (.node 2219 (.leaf 209) (.leaf 169)) (.node 2221 (.leaf 205) (.node 2222 (.leaf 217) (.leaf 214)))) (.node 2225 (.node 2224 (.leaf 208) (.leaf 206)) (.node 2226 (.leaf 207) (.node 2227 (.leaf 130) (.leaf 132))))))) (.node 2247 (.node 2237 (.node 2232 (.node 2230 (.node 2229 (.leaf 156) (.leaf 162)) (.node 2231 (.leaf 167) (.leaf 165))) (.node 2234 (.node 2233 (.leaf 164) (.leaf 154)) (.node 2235 (.leaf 190) (.node 2236 (.leaf 192) (.leaf 198))))) (.node 2242 (.node 2239 (.node 2238 (.leaf 203) (.leaf 201)) (.node 2240 (.leaf 200) (.node 2241 (.leaf 160) (.leaf 196)))) (.node 2244 (.node 2243 (.leaf 208) (.leaf 210)) (.node 2245 (.leaf 215) (.node 2246 (.leaf 213) (.leaf 212)))))) (.node 2257 (.node 2252 (.node 2249 (.node 2248 (.leaf 166) (.leaf 202)) (.node 2250 (.leaf 214) (.node 2251 (.leaf 217) (.leaf 216)))) (.node 2254 (.node 2253 (.leaf 212) (.leaf 213)) (.node 2255 (.leaf 169) (.node 2256 (.leaf 205) (.leaf 217))))) (.node 2262 (.node 2259 (.node 2258 (.leaf 214) (.leaf 208)) (.node 2260 (.leaf 206) (.node 2261 (.leaf 207) (.leaf 168)))) (.node 2264 (.node 2263 (.leaf 204) (.leaf 216)) (.node 2265 (.leaf 215) (.node 2266 (.leaf 210) (.leaf 211)))))))) (.node 2306 (.node 2286 (.node 2276 (.node 2271 (.node 2269 (.node 2268 (.leaf 209) (.leaf 132)) (.node 2270 (.leaf 130) (.leaf 154))) (.node 2273 (.node 2272 (.leaf 160) (.leaf 166)) (.node 2274 (.leaf 169) (.node 2275 (.leaf 168) (.leaf 156))))) (.node 2281 (.node 2278 (.node 2277 (.leaf 192) (.leaf 190)) (.node 2279 (.leaf 196) (.node 2280 (.leaf 202) (.leaf 205)))) (.node 2283 (.node 2282 (.leaf 204) (.leaf 162)) (.node 2284 (.leaf 198) (.node 2285 (.leaf 210) (.leaf 208)))))) (.node 2296 (.node 2291 (.node 2288 (.node 2287 (.leaf 214) (.leaf 217)) (.node 2289 (.leaf 216) (.node 2290 (.leaf 167) (.leaf 203)))) (.node 2293 (.node 2292 (.leaf 215) (.leaf 216)) (.node 2294 (.leaf 217) (.node 2295 (.leaf 214) (.leaf 215))))) (.node 2301 (.node 2298 (.node 2297 (.leaf 165) (.leaf 201)) (.node 2299 (.leaf 213) (.node 2300 (.leaf 212) (.leaf 206)))) (.node 2303 (.node 2302 (.leaf 208) (.leaf 210)) (.node 2304 (.leaf 164) (.node 2305 (.leaf 200) (.leaf 212))))))) (.node 2331 (.node 2317 (.node 2310 (.node 2308 (.node 2307 (.leaf 213) (.leaf 207)) (.node 2309 (.leaf 209) (.leaf 211))) (.node 2314 (.node 2313 (.leaf 0) (.leaf 127)) (.node 2315 (.leaf 133) (.node 2316 (.leaf 132) (.leaf 130))))) (.node 2324 (.node 2321 (.node 2320 (.leaf 0) (.leaf 122)) (.node 2322 (.leaf 128) (.node 2323 (.leaf 130) (.leaf 132)))) (.node 2328 (.node 2327 (.leaf 0) (.leaf 146)) (.node 2329 (.leaf 152) (.node 2330 (.leaf 154) (.leaf 156)))))) (.node 2345 (.node 2338 (.node 2335 (.node 2334 (.leaf 0) (.leaf 164)) (.node 2336 (.leaf 158) (.node 2337 (.leaf 160) (.leaf 162)))) (.node 2342 (.node 2341 (.leaf 0) (.leaf 168)) (.node 2343 (.leaf 169) (.node 2344 (.leaf 166) (.leaf 167))))) (.node 2352 (.node 2349 (.node 2348 (.leaf 0) (.leaf 169)) (.node 2350 (.leaf 168) (.node 2351 (.leaf 164) (.leaf 165)))) (.node 2354 (.node 2353 (.leaf 123) (.leaf 125)) (.node 2355 (.leaf 149) (.node 2356 (.leaf 151) (.leaf 157))))))))) (.node 2442 (.node 2403 (.node 2380 (.node 2366 (.node 2361 (.node 2359 (.node 2358 (.leaf 156) (.leaf 154)) (.node 2360 (.leaf 147) (.leaf 183))) (.node 2363 (.node 2362 (.leaf 185) (.leaf 187)) (.node 2364 (.leaf 193) (.node 2365 (.leaf 192) (.leaf 190))))) (.node 2373 (.node 2370 (.node 2369 (.leaf 0) (.leaf 182)) (.node 2371 (.leaf 188) (.node 2372 (.leaf 190) (.leaf 192)))) (.node 2377 (.node 2376 (.leaf 0) (.leaf 200)) (.node 2378 (.leaf 194) (.node 2379 (.leaf 196) (.leaf 198)))))) (.node 2393 (.node 2386 (.node 2384 (.node 2383 (.leaf 0) (.leaf 204)) (.node 2385 (.leaf 205) (.leaf 202))) (.node 2390 (.node 2387 (.leaf 203) (.leaf 0)) (.node 2391 (.leaf 205) (.node 2392 (.leaf 204) (.leaf 200))))) (.node 2398 (.node 2395 (.node 2394 (.leaf 201) (.leaf 129)) (.node 2396 (.leaf 131) (.node 2397 (.leaf 155) (.leaf 161)))) (.node 2400 (.node 2399 (.leaf 163) (.leaf 162)) (.node 2401 (.leaf 160) (.node 2402 (.leaf 153) (.leaf 189))))))) (.node 2422 (.node 2412 (.node 2407 (.node 2405 (.node 2404 (.leaf 191) (.leaf 197)) (.node 2406 (.leaf 199) (.leaf 198))) (.node 2409 (.node 2408 (.leaf 196) (.leaf 159)) (.node 2410 (.leaf 195) (.node 2411 (.leaf 207) (.leaf 209))))) (.node 2417 (.node 2414 (.node 2413 (.leaf 211) (.leaf 210)) (.node 2415 (.leaf 208) (.node 2416 (.leaf 165) (.leaf 201)))) (.node 2419 (.node 2418 (.leaf 213) (.leaf 212)) (.node 2420 (.leaf 206) (.node 2421 (.leaf 208) (.leaf 210)))))) (.node 2432 (.node 2427 (.node 2424 (.node 2423 (.leaf 167) (.leaf 203)) (.node 2425 (.leaf 215) (.node 2426 (.leaf 216) (.leaf 217)))) (.node 2429 (.node 2428 (.leaf 214) (.leaf 215)) (.node 2430 (.leaf 166) (.node 2431 (.leaf 202) (.leaf 214))))) (.node 2437 (.node 2434 (.node 2433 (.leaf 217) (.leaf 216)) (.node 2435 (.leaf 212) (.node 2436 (.leaf 213) (.leaf 131)))) (.node 2439 (.node 2438 (.leaf 129) (.leaf 153)) (.node 2440 (.leaf 159) (.node 2441 (.leaf 165) (.leaf 167)))))))) (.node 2481 (.node 2461 (.node 2451 (.node 2446 (.node 2444 (.node 2443 (.leaf 166) (.leaf 155)) (.node 2445 (.leaf 191) (.leaf 189))) (.node 2448 (.node 2447 (.leaf 195) (.leaf 201)) (.node 2449 (.leaf 203) (.node 2450 (.leaf 202) (.leaf 161))))) (.node 2456 (.node 2453 (.node 2452 (.leaf 197) (.leaf 209)) (.node 2454 (.leaf 207) (.node 2455 (.leaf 213) (.leaf 215)))) (.node 2458 (.node 2457 (.leaf 214) (.leaf 163)) (.node 2459 (.leaf 199) (.node 2460 (.leaf 211) (.leaf 206)))))) (.node 2471 (.node 2466 (.node 2463 (.node 2462 (.leaf 212) (.leaf 216)) (.node 2464 (.leaf 217) (.node 2465 (.leaf 162) (.leaf 198)))) (.node 2468 (.node 2467 (.leaf 210) (.leaf 208)) (.node 2469 (.leaf 214) (.node 2470 (.leaf 217) (.leaf 216))))) (.node 2476 (.node 2473 (.node 2472 (.leaf 160) (.leaf 196)) (.node 2474 (.leaf 208) (.node 2475 (.leaf 210) (.leaf 215)))) (.node 2478 (.node 2477 (.leaf 213) (.leaf 212)) (.node 2479 (.leaf 133) (.node 2480 (.leaf 128) (.leaf 152))))))) (.node 2500 (.node 2490 (.node 2485 (.node 2483 (.node 2482 (.leaf 158) (.leaf 164)) (.node 2484 (.leaf 168) (.leaf 169))) (.node 2487 (.node 2486 (.leaf 157) (.leaf 193)) (.node 2488 (.leaf 188) (.node 2489 (.leaf 194) (.leaf 200))))) (.node 2495 (.node 2492 (.node 2491 (.leaf 204) (.leaf 205)) (.node 2493 (.leaf 163) (.node 2494 (.leaf 199) (.leaf 211)))) (.node 2497 (.node 2496 (.leaf 206) (.leaf 212)) (.node 2498 (.leaf 216) (.node 2499 (.leaf 217) (.leaf 161)))))) (.node 2510 (.node 2505 (.node 2502 (.node 2501 (.leaf 197) (.leaf 209)) (.node 2503 (.leaf 207) (.node 2504 (.leaf 213) (.leaf 215)))) (.node 2507 (.node 2506 (.leaf 214) (.leaf 159)) (.node 2508 (.leaf 195) (.node 2509 (.leaf 207) (.leaf 209))))) (.node 2515 (.node 2512 (.node 2511 (.leaf 211) (.leaf 210)) (.node 2513 (.leaf 208) (.node 2514 (.leaf 158) (.leaf 194)))) (.node 2517 (.node 2516 (.leaf 206) (.leaf 211)) (.node 2518 (.leaf 209) (.node 2519 (.leaf 207) (.leaf 206))))))))))))
noncomputable def permutationTable5 : LiteralLookup ℕ := (.node 924 (.node 581 (.node 371 (.node 196 (.node 161 (.node 154 (.node 152 (.node 151 (.leaf 0) (.leaf 6)) (.node 153 (.leaf 8) (.leaf 9))) (.node 158 (.node 157 (.leaf 0) (.leaf 2)) (.node 159 (.leaf 12) (.node 160 (.leaf 14) (.leaf 15))))) (.node 168 (.node 165 (.node 164 (.leaf 0) (.leaf 3)) (.node 166 (.leaf 13) (.node 167 (.leaf 16) (.leaf 17)))) (.node 193 (.node 192 (.leaf 0) (.leaf 1)) (.node 194 (.leaf 7) (.node 195 (.leaf 10) (.leaf 11)))))) (.node 210 (.node 203 (.node 200 (.node 199 (.leaf 0) (.leaf 4)) (.node 201 (.leaf 18) (.node 202 (.leaf 20) (.leaf 21)))) (.node 207 (.node 206 (.leaf 0) (.leaf 5)) (.node 208 (.leaf 19) (.node 209 (.leaf 22) (.leaf 23))))) (.node 364 (.node 361 (.node 360 (.leaf 0) (.leaf 14)) (.node 362 (.leaf 8) (.node 363 (.leaf 6) (.leaf 7)))) (.node 368 (.node 367 (.leaf 0) (.leaf 12)) (.node 369 (.leaf 2) (.node 370 (.leaf 0) (.leaf 1))))))) (.node 420 (.node 406 (.node 378 (.node 375 (.node 374 (.leaf 0) (.leaf 13)) (.node 376 (.leaf 3) (.node 377 (.leaf 5) (.leaf 4)))) (.node 403 (.node 402 (.leaf 0) (.leaf 15)) (.node 404 (.leaf 9) (.node 405 (.leaf 11) (.leaf 10))))) (.node 413 (.node 410 (.node 409 (.leaf 0) (.leaf 17)) (.node 411 (.leaf 23) (.node 412 (.leaf 21) (.leaf 20)))) (.node 417 (.node 416 (.leaf 0) (.leaf 16)) (.node 418 (.leaf 22) (.node 419 (.leaf 19) (.leaf 18)))))) (.node 540 (.node 527 (.node 519 (.node 518 (.leaf 0) (.leaf 14)) (.node 525 (.leaf 0) (.node 526 (.leaf 8) (.leaf 6)))) (.node 533 (.node 532 (.leaf 0) (.leaf 6)) (.node 534 (.leaf 8) (.node 539 (.leaf 0) (.leaf 7))))) (.node 567 (.node 560 (.node 541 (.leaf 9) (.leaf 0)) (.node 561 (.leaf 12) (.node 562 (.leaf 2) (.leaf 0)))) (.node 569 (.node 568 (.leaf 2) (.leaf 12)) (.node 575 (.leaf 0) (.node 576 (.leaf 14) (.leaf 0)))))))) (.node 813 (.node 737 (.node 617 (.node 604 (.node 583 (.node 582 (.leaf 1) (.leaf 15)) (.node 602 (.leaf 0) (.node 603 (.leaf 13) (.leaf 3)))) (.node 610 (.node 609 (.leaf 0) (.leaf 3)) (.node 611 (.leaf 13) (.node 616 (.leaf 0) (.leaf 5))))) (.node 728 (.node 623 (.node 618 (.leaf 16) (.leaf 0)) (.node 624 (.leaf 4) (.node 625 (.leaf 17) (.leaf 0)))) (.node 730 (.node 729 (.leaf 15) (.leaf 1)) (.node 735 (.leaf 0) (.node 736 (.leaf 9) (.leaf 7)))))) (.node 777 (.node 750 (.node 743 (.node 742 (.leaf 0) (.leaf 11)) (.node 744 (.leaf 10) (.node 749 (.leaf 0) (.leaf 10)))) (.node 770 (.node 751 (.leaf 11) (.leaf 0)) (.node 771 (.leaf 17) (.node 772 (.leaf 4) (.leaf 0))))) (.node 786 (.node 779 (.node 778 (.leaf 23) (.leaf 18)) (.node 784 (.leaf 0) (.node 785 (.leaf 21) (.leaf 20)))) (.node 792 (.node 791 (.leaf 0) (.leaf 20)) (.node 793 (.leaf 21) (.node 812 (.leaf 0) (.leaf 16))))))) (.node 875 (.node 835 (.node 826 (.node 819 (.node 814 (.leaf 5) (.leaf 0)) (.node 820 (.leaf 22) (.node 821 (.leaf 19) (.leaf 0)))) (.node 828 (.node 827 (.leaf 19) (.leaf 22)) (.node 833 (.leaf 0) (.node 834 (.leaf 18) (.leaf 23))))) (.node 868 (.node 865 (.node 864 (.leaf 0) (.leaf 8)) (.node 866 (.leaf 14) (.node 867 (.leaf 12) (.leaf 13)))) (.node 872 (.node 871 (.leaf 0) (.leaf 6)) (.node 873 (.leaf 0) (.node 874 (.leaf 2) (.leaf 3)))))) (.node 910 (.node 882 (.node 879 (.node 878 (.leaf 0) (.leaf 7)) (.node 880 (.leaf 1) (.node 881 (.leaf 4) (.leaf 5)))) (.node 907 (.node 906 (.leaf 0) (.leaf 6)) (.node 908 (.leaf 0) (.node 909 (.leaf 2) (.leaf 3))))) (.node 917 (.node 914 (.node 913 (.leaf 0) (.leaf 8)) (.node 915 (.leaf 14) (.node 916 (.leaf 12) (.leaf 13)))) (.node 921 (.node 920 (.leaf 0) (.leaf 9)) (.node 922 (.leaf 15) (.node 923 (.leaf 17) (.leaf 16))))))))) (.node 1747 (.node 1429 (.node 1219 (.node 1064 (.node 1057 (.node 1054 (.node 1053 (.leaf 0) (.leaf 12)) (.node 1055 (.leaf 2) (.node 1056 (.leaf 0) (.leaf 1)))) (.node 1061 (.node 1060 (.leaf 0) (.leaf 2)) (.node 1062 (.leaf 12) (.node 1063 (.leaf 14) (.leaf 15))))) (.node 1136 (.node 1094 (.node 1093 (.leaf 0) (.leaf 14)) (.node 1134 (.leaf 0) (.node 1135 (.leaf 6) (.leaf 8)))) (.node 1177 (.node 1176 (.leaf 0) (.leaf 8)) (.node 1178 (.leaf 6) (.node 1218 (.leaf 0) (.leaf 9)))))) (.node 1274 (.node 1266 (.node 1263 (.node 1220 (.leaf 7) (.leaf 0)) (.node 1264 (.leaf 14) (.node 1265 (.leaf 8) (.leaf 6)))) (.node 1271 (.node 1267 (.leaf 7) (.leaf 0)) (.node 1272 (.leaf 6) (.node 1273 (.leaf 8) (.leaf 9))))) (.node 1345 (.node 1303 (.node 1302 (.leaf 0) (.leaf 2)) (.node 1304 (.leaf 12) (.node 1344 (.leaf 0) (.leaf 12)))) (.node 1386 (.node 1346 (.leaf 2) (.leaf 0)) (.node 1387 (.leaf 14) (.node 1428 (.leaf 0) (.leaf 15))))))) (.node 1598 (.node 1483 (.node 1476 (.node 1473 (.node 1430 (.leaf 1) (.leaf 0)) (.node 1474 (.leaf 15) (.node 1475 (.leaf 9) (.leaf 11)))) (.node 1480 (.node 1477 (.leaf 10) (.leaf 0)) (.node 1481 (.leaf 1) (.node 1482 (.leaf 7) (.leaf 10))))) (.node 1554 (.node 1512 (.node 1484 (.leaf 11) (.leaf 0)) (.node 1513 (.leaf 3) (.node 1514 (.leaf 13) (.leaf 0)))) (.node 1556 (.node 1555 (.leaf 13) (.leaf 3)) (.node 1596 (.leaf 0) (.node 1597 (.leaf 16) (.leaf 5)))))) (.node 1712 (.node 1705 (.node 1639 (.node 1638 (.leaf 0) (.leaf 17)) (.node 1640 (.leaf 4) (.node 1704 (.leaf 0) (.leaf 9)))) (.node 1707 (.node 1706 (.leaf 15) (.leaf 17)) (.node 1708 (.leaf 16) (.node 1711 (.leaf 0) (.leaf 11))))) (.node 1719 (.node 1714 (.node 1713 (.leaf 21) (.leaf 23)) (.node 1715 (.leaf 22) (.node 1718 (.leaf 0) (.leaf 10)))) (.node 1721 (.node 1720 (.leaf 20) (.leaf 18)) (.node 1722 (.leaf 19) (.node 1746 (.leaf 0) (.leaf 7)))))))) (.node 2107 (.node 1901 (.node 1761 (.node 1754 (.node 1749 (.node 1748 (.leaf 1) (.leaf 4)) (.node 1750 (.leaf 5) (.node 1753 (.leaf 0) (.leaf 10)))) (.node 1756 (.node 1755 (.leaf 20) (.leaf 18)) (.node 1757 (.leaf 19) (.node 1760 (.leaf 0) (.leaf 11))))) (.node 1894 (.node 1763 (.node 1762 (.leaf 21) (.leaf 23)) (.node 1764 (.leaf 22) (.node 1893 (.leaf 0) (.leaf 13)))) (.node 1896 (.node 1895 (.leaf 3) (.leaf 5)) (.node 1897 (.leaf 4) (.node 1900 (.leaf 0) (.leaf 3)))))) (.node 2016 (.node 1933 (.node 1903 (.node 1902 (.leaf 13) (.leaf 16)) (.node 1904 (.leaf 17) (.node 1932 (.leaf 0) (.leaf 1)))) (.node 1974 (.node 1934 (.leaf 15) (.leaf 0)) (.node 1975 (.leaf 7) (.node 1976 (.leaf 9) (.leaf 0))))) (.node 2060 (.node 2018 (.node 2017 (.leaf 10) (.leaf 11)) (.node 2058 (.leaf 0) (.node 2059 (.leaf 11) (.leaf 10)))) (.node 2104 (.node 2103 (.leaf 0) (.leaf 16)) (.node 2105 (.leaf 22) (.node 2106 (.leaf 19) (.leaf 18))))))) (.node 2315 (.node 2185 (.node 2114 (.node 2111 (.node 2110 (.leaf 0) (.leaf 5)) (.node 2112 (.leaf 19) (.node 2113 (.leaf 22) (.leaf 23)))) (.node 2143 (.node 2142 (.leaf 0) (.leaf 4)) (.node 2144 (.leaf 17) (.node 2184 (.leaf 0) (.leaf 18))))) (.node 2268 (.node 2226 (.node 2186 (.leaf 23) (.leaf 0)) (.node 2227 (.leaf 20) (.node 2228 (.leaf 21) (.leaf 0)))) (.node 2270 (.node 2269 (.leaf 21) (.leaf 20)) (.node 2313 (.leaf 0) (.node 2314 (.leaf 17) (.leaf 23)))))) (.node 2354 (.node 2322 (.node 2317 (.node 2316 (.leaf 21) (.leaf 20)) (.node 2320 (.leaf 0) (.node 2321 (.leaf 4) (.leaf 18)))) (.node 2324 (.node 2323 (.leaf 20) (.leaf 21)) (.node 2352 (.leaf 0) (.node 2353 (.leaf 5) (.leaf 16))))) (.node 2437 (.node 2395 (.node 2394 (.leaf 0) (.leaf 19)) (.node 2396 (.leaf 22) (.node 2436 (.leaf 0) (.leaf 22)))) (.node 2478 (.node 2438 (.leaf 19) (.leaf 0)) (.node 2479 (.leaf 23) (.node 2480 (.leaf 18) (.leaf 0))))))))))
noncomputable def neighborTable5 : LiteralLookup ℕ := (.node 924 (.node 604 (.node 409 (.node 203 (.node 164 (.node 154 (.node 150 (.leaf 0) (.leaf 110)) (.node 157 (.leaf 0) (.node 161 (.leaf 110) (.leaf 0)))) (.node 192 (.node 168 (.leaf 110) (.leaf 0)) (.node 196 (.leaf 110) (.node 199 (.leaf 0) (.leaf 110))))) (.node 367 (.node 210 (.node 206 (.leaf 0) (.leaf 110)) (.node 360 (.leaf 0) (.node 364 (.leaf 110) (.leaf 0)))) (.node 378 (.node 371 (.leaf 110) (.node 374 (.leaf 0) (.leaf 110))) (.node 402 (.leaf 0) (.node 406 (.leaf 110) (.leaf 0)))))) (.node 539 (.node 520 (.node 416 (.node 413 (.leaf 110) (.leaf 0)) (.node 420 (.leaf 110) (.node 518 (.leaf 0) (.leaf 110)))) (.node 527 (.node 525 (.leaf 0) (.leaf 110)) (.node 532 (.leaf 0) (.node 534 (.leaf 110) (.leaf 0))))) (.node 569 (.node 560 (.node 541 (.leaf 110) (.leaf 0)) (.node 562 (.leaf 110) (.node 567 (.leaf 0) (.leaf 110)))) (.node 581 (.node 574 (.leaf 0) (.node 576 (.leaf 110) (.leaf 0))) (.node 583 (.leaf 110) (.node 602 (.leaf 0) (.leaf 110))))))) (.node 791 (.node 737 (.node 623 (.node 611 (.node 609 (.leaf 0) (.leaf 110)) (.node 616 (.leaf 0) (.node 618 (.leaf 110) (.leaf 0)))) (.node 728 (.node 625 (.leaf 110) (.leaf 0)) (.node 730 (.leaf 110) (.node 735 (.leaf 0) (.leaf 110))))) (.node 770 (.node 744 (.node 742 (.leaf 0) (.leaf 110)) (.node 749 (.leaf 0) (.node 751 (.leaf 110) (.leaf 0)))) (.node 779 (.node 772 (.leaf 110) (.node 777 (.leaf 0) (.leaf 110))) (.node 784 (.leaf 0) (.node 786 (.leaf 110) (.leaf 0)))))) (.node 864 (.node 821 (.node 812 (.node 793 (.leaf 110) (.leaf 0)) (.node 814 (.leaf 110) (.node 819 (.leaf 0) (.leaf 110)))) (.node 828 (.node 826 (.leaf 0) (.leaf 110)) (.node 833 (.leaf 0) (.node 835 (.leaf 110) (.leaf 0))))) (.node 882 (.node 871 (.node 868 (.leaf 110) (.leaf 0)) (.node 875 (.leaf 110) (.node 878 (.leaf 0) (.leaf 110)))) (.node 913 (.node 906 (.leaf 0) (.node 910 (.leaf 110) (.leaf 0))) (.node 917 (.leaf 110) (.node 920 (.leaf 0) (.leaf 110)))))))) (.node 1722 (.node 1386 (.node 1178 (.node 1092 (.node 1057 (.node 1053 (.leaf 0) (.leaf 110)) (.node 1060 (.leaf 0) (.node 1064 (.leaf 110) (.leaf 0)))) (.node 1134 (.node 1094 (.leaf 110) (.leaf 0)) (.node 1136 (.leaf 110) (.node 1176 (.leaf 0) (.leaf 110))))) (.node 1270 (.node 1220 (.node 1218 (.leaf 0) (.leaf 110)) (.node 1263 (.leaf 0) (.node 1267 (.leaf 110) (.leaf 0)))) (.node 1304 (.node 1274 (.leaf 110) (.node 1302 (.leaf 0) (.leaf 110))) (.node 1344 (.leaf 0) (.node 1346 (.leaf 110) (.leaf 0)))))) (.node 1554 (.node 1477 (.node 1428 (.node 1388 (.leaf 110) (.leaf 0)) (.node 1430 (.leaf 110) (.node 1473 (.leaf 0) (.leaf 110)))) (.node 1484 (.node 1480 (.leaf 0) (.leaf 110)) (.node 1512 (.leaf 0) (.node 1514 (.leaf 110) (.leaf 0))))) (.node 1640 (.node 1596 (.node 1556 (.leaf 110) (.leaf 0)) (.node 1598 (.leaf 110) (.node 1638 (.leaf 0) (.leaf 110)))) (.node 1711 (.node 1704 (.leaf 0) (.node 1708 (.leaf 110) (.leaf 0))) (.node 1715 (.leaf 110) (.node 1718 (.leaf 0) (.leaf 110))))))) (.node 2110 (.node 1904 (.node 1760 (.node 1750 (.node 1746 (.leaf 0) (.leaf 110)) (.node 1753 (.leaf 0) (.node 1757 (.leaf 110) (.leaf 0)))) (.node 1893 (.node 1764 (.leaf 110) (.leaf 0)) (.node 1897 (.leaf 110) (.node 1900 (.leaf 0) (.leaf 110))))) (.node 2016 (.node 1934 (.node 1932 (.leaf 0) (.leaf 110)) (.node 1974 (.leaf 0) (.node 1976 (.leaf 110) (.leaf 0)))) (.node 2060 (.node 2018 (.leaf 110) (.node 2058 (.leaf 0) (.leaf 110))) (.node 2103 (.leaf 0) (.node 2107 (.leaf 110) (.leaf 0)))))) (.node 2317 (.node 2186 (.node 2142 (.node 2114 (.leaf 110) (.leaf 0)) (.node 2144 (.leaf 110) (.node 2184 (.leaf 0) (.leaf 110)))) (.node 2268 (.node 2226 (.leaf 0) (.node 2228 (.leaf 110) (.leaf 0))) (.node 2270 (.leaf 110) (.node 2313 (.leaf 0) (.leaf 110))))) (.node 2394 (.node 2324 (.node 2320 (.leaf 0) (.leaf 110)) (.node 2352 (.leaf 0) (.node 2354 (.leaf 110) (.leaf 0)))) (.node 2438 (.node 2396 (.leaf 110) (.node 2436 (.leaf 0) (.leaf 110))) (.node 2478 (.leaf 0) (.node 2480 (.leaf 110) (.leaf 0)))))))))

noncomputable def coverageWitness5 (code : ℕ) : Fin 290 :=
  Fin.ofNat 290 (coverageTable5.get code)
noncomputable def permutationWitness5 (code : ℕ) : Fin 24 :=
  Fin.ofNat 24 (permutationTable5.get code)
noncomputable def neighborWitness5 (code : ℕ) : Fin 290 :=
  Fin.ofNat 290 (neighborTable5.get code)

noncomputable def coveredTest5 (code : ℕ) : Bool :=
  coverageAt cells (triangle 7 (by decide)) (decodeInjection 7 5 (by decide) code)
    (coverageWitness5 code)
noncomputable def neighborTest5 (code : ℕ) : Bool :=
  neighborAt cells neighbors (by decide) permMaps (decodeInjection 7 5 (by decide) code)
    (permutationWitness5 code) (neighborWitness5 code)

theorem covered_5_codes_000000 : CodeInterval coveredTest5 0 64 :=
  codeInterval_of_check coveredTest5 0 64 (by decide +kernel)

theorem covered_5_codes_000064 : CodeInterval coveredTest5 64 128 :=
  codeInterval_of_check coveredTest5 64 64 (by decide +kernel)

theorem covered_5_codes_000128 : CodeInterval coveredTest5 128 192 :=
  codeInterval_of_check coveredTest5 128 64 (by decide +kernel)

theorem covered_5_codes_000192 : CodeInterval coveredTest5 192 256 :=
  codeInterval_of_check coveredTest5 192 64 (by decide +kernel)

theorem covered_5_codes_000256 : CodeInterval coveredTest5 256 320 :=
  codeInterval_of_check coveredTest5 256 64 (by decide +kernel)

theorem covered_5_codes_000320 : CodeInterval coveredTest5 320 384 :=
  codeInterval_of_check coveredTest5 320 64 (by decide +kernel)

theorem covered_5_codes_000384 : CodeInterval coveredTest5 384 448 :=
  codeInterval_of_check coveredTest5 384 64 (by decide +kernel)

theorem covered_5_codes_000448 : CodeInterval coveredTest5 448 512 :=
  codeInterval_of_check coveredTest5 448 64 (by decide +kernel)

theorem covered_5_codes_000512 : CodeInterval coveredTest5 512 576 :=
  codeInterval_of_check coveredTest5 512 64 (by decide +kernel)

theorem covered_5_codes_000576 : CodeInterval coveredTest5 576 640 :=
  codeInterval_of_check coveredTest5 576 64 (by decide +kernel)

theorem covered_5_codes_000640 : CodeInterval coveredTest5 640 704 :=
  codeInterval_of_check coveredTest5 640 64 (by decide +kernel)

theorem covered_5_codes_000704 : CodeInterval coveredTest5 704 768 :=
  codeInterval_of_check coveredTest5 704 64 (by decide +kernel)

theorem covered_5_codes_000768 : CodeInterval coveredTest5 768 832 :=
  codeInterval_of_check coveredTest5 768 64 (by decide +kernel)

theorem covered_5_codes_000832 : CodeInterval coveredTest5 832 896 :=
  codeInterval_of_check coveredTest5 832 64 (by decide +kernel)

theorem covered_5_codes_000896 : CodeInterval coveredTest5 896 960 :=
  codeInterval_of_check coveredTest5 896 64 (by decide +kernel)

theorem covered_5_codes_000960 : CodeInterval coveredTest5 960 1024 :=
  codeInterval_of_check coveredTest5 960 64 (by decide +kernel)

theorem covered_5_codes_001024 : CodeInterval coveredTest5 1024 1088 :=
  codeInterval_of_check coveredTest5 1024 64 (by decide +kernel)

theorem covered_5_codes_001088 : CodeInterval coveredTest5 1088 1152 :=
  codeInterval_of_check coveredTest5 1088 64 (by decide +kernel)

theorem covered_5_codes_001152 : CodeInterval coveredTest5 1152 1216 :=
  codeInterval_of_check coveredTest5 1152 64 (by decide +kernel)

theorem covered_5_codes_001216 : CodeInterval coveredTest5 1216 1280 :=
  codeInterval_of_check coveredTest5 1216 64 (by decide +kernel)

theorem covered_5_codes_001280 : CodeInterval coveredTest5 1280 1344 :=
  codeInterval_of_check coveredTest5 1280 64 (by decide +kernel)

theorem covered_5_codes_001344 : CodeInterval coveredTest5 1344 1408 :=
  codeInterval_of_check coveredTest5 1344 64 (by decide +kernel)

theorem covered_5_codes_001408 : CodeInterval coveredTest5 1408 1472 :=
  codeInterval_of_check coveredTest5 1408 64 (by decide +kernel)

theorem covered_5_codes_001472 : CodeInterval coveredTest5 1472 1536 :=
  codeInterval_of_check coveredTest5 1472 64 (by decide +kernel)

theorem covered_5_codes_001536 : CodeInterval coveredTest5 1536 1600 :=
  codeInterval_of_check coveredTest5 1536 64 (by decide +kernel)

theorem covered_5_codes_001600 : CodeInterval coveredTest5 1600 1664 :=
  codeInterval_of_check coveredTest5 1600 64 (by decide +kernel)

theorem covered_5_codes_001664 : CodeInterval coveredTest5 1664 1728 :=
  codeInterval_of_check coveredTest5 1664 64 (by decide +kernel)

theorem covered_5_codes_001728 : CodeInterval coveredTest5 1728 1792 :=
  codeInterval_of_check coveredTest5 1728 64 (by decide +kernel)

theorem covered_5_codes_001792 : CodeInterval coveredTest5 1792 1856 :=
  codeInterval_of_check coveredTest5 1792 64 (by decide +kernel)

theorem covered_5_codes_001856 : CodeInterval coveredTest5 1856 1920 :=
  codeInterval_of_check coveredTest5 1856 64 (by decide +kernel)

theorem covered_5_codes_001920 : CodeInterval coveredTest5 1920 1984 :=
  codeInterval_of_check coveredTest5 1920 64 (by decide +kernel)

theorem covered_5_codes_001984 : CodeInterval coveredTest5 1984 2048 :=
  codeInterval_of_check coveredTest5 1984 64 (by decide +kernel)

theorem covered_5_codes_002048 : CodeInterval coveredTest5 2048 2112 :=
  codeInterval_of_check coveredTest5 2048 64 (by decide +kernel)

theorem covered_5_codes_002112 : CodeInterval coveredTest5 2112 2176 :=
  codeInterval_of_check coveredTest5 2112 64 (by decide +kernel)

theorem covered_5_codes_002176 : CodeInterval coveredTest5 2176 2240 :=
  codeInterval_of_check coveredTest5 2176 64 (by decide +kernel)

theorem covered_5_codes_002240 : CodeInterval coveredTest5 2240 2304 :=
  codeInterval_of_check coveredTest5 2240 64 (by decide +kernel)

theorem covered_5_codes_002304 : CodeInterval coveredTest5 2304 2368 :=
  codeInterval_of_check coveredTest5 2304 64 (by decide +kernel)

theorem covered_5_codes_002368 : CodeInterval coveredTest5 2368 2432 :=
  codeInterval_of_check coveredTest5 2368 64 (by decide +kernel)

theorem covered_5_codes_002432 : CodeInterval coveredTest5 2432 2496 :=
  codeInterval_of_check coveredTest5 2432 64 (by decide +kernel)

theorem covered_5_codes_002496 : CodeInterval coveredTest5 2496 2520 :=
  codeInterval_of_check coveredTest5 2496 24 (by decide +kernel)

theorem covered_5_join_000000_000128 : CodeInterval coveredTest5 0 128 :=
  codeInterval_append coveredTest5 0 64 128 covered_5_codes_000000 covered_5_codes_000064

theorem covered_5_join_000192_000320 : CodeInterval coveredTest5 192 320 :=
  codeInterval_append coveredTest5 192 256 320 covered_5_codes_000192 covered_5_codes_000256

theorem covered_5_join_000128_000320 : CodeInterval coveredTest5 128 320 :=
  codeInterval_append coveredTest5 128 192 320 covered_5_codes_000128 covered_5_join_000192_000320

theorem covered_5_join_000000_000320 : CodeInterval coveredTest5 0 320 :=
  codeInterval_append coveredTest5 0 128 320 covered_5_join_000000_000128 covered_5_join_000128_000320

theorem covered_5_join_000320_000448 : CodeInterval coveredTest5 320 448 :=
  codeInterval_append coveredTest5 320 384 448 covered_5_codes_000320 covered_5_codes_000384

theorem covered_5_join_000512_000640 : CodeInterval coveredTest5 512 640 :=
  codeInterval_append coveredTest5 512 576 640 covered_5_codes_000512 covered_5_codes_000576

theorem covered_5_join_000448_000640 : CodeInterval coveredTest5 448 640 :=
  codeInterval_append coveredTest5 448 512 640 covered_5_codes_000448 covered_5_join_000512_000640

theorem covered_5_join_000320_000640 : CodeInterval coveredTest5 320 640 :=
  codeInterval_append coveredTest5 320 448 640 covered_5_join_000320_000448 covered_5_join_000448_000640

theorem covered_5_join_000000_000640 : CodeInterval coveredTest5 0 640 :=
  codeInterval_append coveredTest5 0 320 640 covered_5_join_000000_000320 covered_5_join_000320_000640

theorem covered_5_join_000640_000768 : CodeInterval coveredTest5 640 768 :=
  codeInterval_append coveredTest5 640 704 768 covered_5_codes_000640 covered_5_codes_000704

theorem covered_5_join_000832_000960 : CodeInterval coveredTest5 832 960 :=
  codeInterval_append coveredTest5 832 896 960 covered_5_codes_000832 covered_5_codes_000896

theorem covered_5_join_000768_000960 : CodeInterval coveredTest5 768 960 :=
  codeInterval_append coveredTest5 768 832 960 covered_5_codes_000768 covered_5_join_000832_000960

theorem covered_5_join_000640_000960 : CodeInterval coveredTest5 640 960 :=
  codeInterval_append coveredTest5 640 768 960 covered_5_join_000640_000768 covered_5_join_000768_000960

theorem covered_5_join_000960_001088 : CodeInterval coveredTest5 960 1088 :=
  codeInterval_append coveredTest5 960 1024 1088 covered_5_codes_000960 covered_5_codes_001024

theorem covered_5_join_001152_001280 : CodeInterval coveredTest5 1152 1280 :=
  codeInterval_append coveredTest5 1152 1216 1280 covered_5_codes_001152 covered_5_codes_001216

theorem covered_5_join_001088_001280 : CodeInterval coveredTest5 1088 1280 :=
  codeInterval_append coveredTest5 1088 1152 1280 covered_5_codes_001088 covered_5_join_001152_001280

theorem covered_5_join_000960_001280 : CodeInterval coveredTest5 960 1280 :=
  codeInterval_append coveredTest5 960 1088 1280 covered_5_join_000960_001088 covered_5_join_001088_001280

theorem covered_5_join_000640_001280 : CodeInterval coveredTest5 640 1280 :=
  codeInterval_append coveredTest5 640 960 1280 covered_5_join_000640_000960 covered_5_join_000960_001280

theorem covered_5_join_000000_001280 : CodeInterval coveredTest5 0 1280 :=
  codeInterval_append coveredTest5 0 640 1280 covered_5_join_000000_000640 covered_5_join_000640_001280

theorem covered_5_join_001280_001408 : CodeInterval coveredTest5 1280 1408 :=
  codeInterval_append coveredTest5 1280 1344 1408 covered_5_codes_001280 covered_5_codes_001344

theorem covered_5_join_001472_001600 : CodeInterval coveredTest5 1472 1600 :=
  codeInterval_append coveredTest5 1472 1536 1600 covered_5_codes_001472 covered_5_codes_001536

theorem covered_5_join_001408_001600 : CodeInterval coveredTest5 1408 1600 :=
  codeInterval_append coveredTest5 1408 1472 1600 covered_5_codes_001408 covered_5_join_001472_001600

theorem covered_5_join_001280_001600 : CodeInterval coveredTest5 1280 1600 :=
  codeInterval_append coveredTest5 1280 1408 1600 covered_5_join_001280_001408 covered_5_join_001408_001600

theorem covered_5_join_001600_001728 : CodeInterval coveredTest5 1600 1728 :=
  codeInterval_append coveredTest5 1600 1664 1728 covered_5_codes_001600 covered_5_codes_001664

theorem covered_5_join_001792_001920 : CodeInterval coveredTest5 1792 1920 :=
  codeInterval_append coveredTest5 1792 1856 1920 covered_5_codes_001792 covered_5_codes_001856

theorem covered_5_join_001728_001920 : CodeInterval coveredTest5 1728 1920 :=
  codeInterval_append coveredTest5 1728 1792 1920 covered_5_codes_001728 covered_5_join_001792_001920

theorem covered_5_join_001600_001920 : CodeInterval coveredTest5 1600 1920 :=
  codeInterval_append coveredTest5 1600 1728 1920 covered_5_join_001600_001728 covered_5_join_001728_001920

theorem covered_5_join_001280_001920 : CodeInterval coveredTest5 1280 1920 :=
  codeInterval_append coveredTest5 1280 1600 1920 covered_5_join_001280_001600 covered_5_join_001600_001920

theorem covered_5_join_001920_002048 : CodeInterval coveredTest5 1920 2048 :=
  codeInterval_append coveredTest5 1920 1984 2048 covered_5_codes_001920 covered_5_codes_001984

theorem covered_5_join_002112_002240 : CodeInterval coveredTest5 2112 2240 :=
  codeInterval_append coveredTest5 2112 2176 2240 covered_5_codes_002112 covered_5_codes_002176

theorem covered_5_join_002048_002240 : CodeInterval coveredTest5 2048 2240 :=
  codeInterval_append coveredTest5 2048 2112 2240 covered_5_codes_002048 covered_5_join_002112_002240

theorem covered_5_join_001920_002240 : CodeInterval coveredTest5 1920 2240 :=
  codeInterval_append coveredTest5 1920 2048 2240 covered_5_join_001920_002048 covered_5_join_002048_002240

theorem covered_5_join_002240_002368 : CodeInterval coveredTest5 2240 2368 :=
  codeInterval_append coveredTest5 2240 2304 2368 covered_5_codes_002240 covered_5_codes_002304

theorem covered_5_join_002432_002520 : CodeInterval coveredTest5 2432 2520 :=
  codeInterval_append coveredTest5 2432 2496 2520 covered_5_codes_002432 covered_5_codes_002496

theorem covered_5_join_002368_002520 : CodeInterval coveredTest5 2368 2520 :=
  codeInterval_append coveredTest5 2368 2432 2520 covered_5_codes_002368 covered_5_join_002432_002520

theorem covered_5_join_002240_002520 : CodeInterval coveredTest5 2240 2520 :=
  codeInterval_append coveredTest5 2240 2368 2520 covered_5_join_002240_002368 covered_5_join_002368_002520

theorem covered_5_join_001920_002520 : CodeInterval coveredTest5 1920 2520 :=
  codeInterval_append coveredTest5 1920 2240 2520 covered_5_join_001920_002240 covered_5_join_002240_002520

theorem covered_5_join_001280_002520 : CodeInterval coveredTest5 1280 2520 :=
  codeInterval_append coveredTest5 1280 1920 2520 covered_5_join_001280_001920 covered_5_join_001920_002520

theorem covered_5_join_000000_002520 : CodeInterval coveredTest5 0 2520 :=
  codeInterval_append coveredTest5 0 1280 2520 covered_5_join_000000_001280 covered_5_join_001280_002520

theorem covered_5 : ∀ f : Fin 5 → Fin 7, Covered cells (triangle 7 (by decide)) f :=
  covered_of_injection_checks (by decide) cells (triangle 7 (by decide)) coverageWitness5 covered_5_join_000000_002520

theorem neighbor_5_codes_000000 : CodeInterval neighborTest5 0 64 :=
  codeInterval_of_check neighborTest5 0 64 (by decide +kernel)

theorem neighbor_5_codes_000064 : CodeInterval neighborTest5 64 128 :=
  codeInterval_of_check neighborTest5 64 64 (by decide +kernel)

theorem neighbor_5_codes_000128 : CodeInterval neighborTest5 128 192 :=
  codeInterval_of_check neighborTest5 128 64 (by decide +kernel)

theorem neighbor_5_codes_000192 : CodeInterval neighborTest5 192 256 :=
  codeInterval_of_check neighborTest5 192 64 (by decide +kernel)

theorem neighbor_5_codes_000256 : CodeInterval neighborTest5 256 320 :=
  codeInterval_of_check neighborTest5 256 64 (by decide +kernel)

theorem neighbor_5_codes_000320 : CodeInterval neighborTest5 320 384 :=
  codeInterval_of_check neighborTest5 320 64 (by decide +kernel)

theorem neighbor_5_codes_000384 : CodeInterval neighborTest5 384 448 :=
  codeInterval_of_check neighborTest5 384 64 (by decide +kernel)

theorem neighbor_5_codes_000448 : CodeInterval neighborTest5 448 512 :=
  codeInterval_of_check neighborTest5 448 64 (by decide +kernel)

theorem neighbor_5_codes_000512 : CodeInterval neighborTest5 512 576 :=
  codeInterval_of_check neighborTest5 512 64 (by decide +kernel)

theorem neighbor_5_codes_000576 : CodeInterval neighborTest5 576 640 :=
  codeInterval_of_check neighborTest5 576 64 (by decide +kernel)

theorem neighbor_5_codes_000640 : CodeInterval neighborTest5 640 704 :=
  codeInterval_of_check neighborTest5 640 64 (by decide +kernel)

theorem neighbor_5_codes_000704 : CodeInterval neighborTest5 704 768 :=
  codeInterval_of_check neighborTest5 704 64 (by decide +kernel)

theorem neighbor_5_codes_000768 : CodeInterval neighborTest5 768 832 :=
  codeInterval_of_check neighborTest5 768 64 (by decide +kernel)

theorem neighbor_5_codes_000832 : CodeInterval neighborTest5 832 896 :=
  codeInterval_of_check neighborTest5 832 64 (by decide +kernel)

theorem neighbor_5_codes_000896 : CodeInterval neighborTest5 896 960 :=
  codeInterval_of_check neighborTest5 896 64 (by decide +kernel)

theorem neighbor_5_codes_000960 : CodeInterval neighborTest5 960 1024 :=
  codeInterval_of_check neighborTest5 960 64 (by decide +kernel)

theorem neighbor_5_codes_001024 : CodeInterval neighborTest5 1024 1088 :=
  codeInterval_of_check neighborTest5 1024 64 (by decide +kernel)

theorem neighbor_5_codes_001088 : CodeInterval neighborTest5 1088 1152 :=
  codeInterval_of_check neighborTest5 1088 64 (by decide +kernel)

theorem neighbor_5_codes_001152 : CodeInterval neighborTest5 1152 1216 :=
  codeInterval_of_check neighborTest5 1152 64 (by decide +kernel)

theorem neighbor_5_codes_001216 : CodeInterval neighborTest5 1216 1280 :=
  codeInterval_of_check neighborTest5 1216 64 (by decide +kernel)

theorem neighbor_5_codes_001280 : CodeInterval neighborTest5 1280 1344 :=
  codeInterval_of_check neighborTest5 1280 64 (by decide +kernel)

theorem neighbor_5_codes_001344 : CodeInterval neighborTest5 1344 1408 :=
  codeInterval_of_check neighborTest5 1344 64 (by decide +kernel)

theorem neighbor_5_codes_001408 : CodeInterval neighborTest5 1408 1472 :=
  codeInterval_of_check neighborTest5 1408 64 (by decide +kernel)

theorem neighbor_5_codes_001472 : CodeInterval neighborTest5 1472 1536 :=
  codeInterval_of_check neighborTest5 1472 64 (by decide +kernel)

theorem neighbor_5_codes_001536 : CodeInterval neighborTest5 1536 1600 :=
  codeInterval_of_check neighborTest5 1536 64 (by decide +kernel)

theorem neighbor_5_codes_001600 : CodeInterval neighborTest5 1600 1664 :=
  codeInterval_of_check neighborTest5 1600 64 (by decide +kernel)

theorem neighbor_5_codes_001664 : CodeInterval neighborTest5 1664 1728 :=
  codeInterval_of_check neighborTest5 1664 64 (by decide +kernel)

theorem neighbor_5_codes_001728 : CodeInterval neighborTest5 1728 1792 :=
  codeInterval_of_check neighborTest5 1728 64 (by decide +kernel)

theorem neighbor_5_codes_001792 : CodeInterval neighborTest5 1792 1856 :=
  codeInterval_of_check neighborTest5 1792 64 (by decide +kernel)

theorem neighbor_5_codes_001856 : CodeInterval neighborTest5 1856 1920 :=
  codeInterval_of_check neighborTest5 1856 64 (by decide +kernel)

theorem neighbor_5_codes_001920 : CodeInterval neighborTest5 1920 1984 :=
  codeInterval_of_check neighborTest5 1920 64 (by decide +kernel)

theorem neighbor_5_codes_001984 : CodeInterval neighborTest5 1984 2048 :=
  codeInterval_of_check neighborTest5 1984 64 (by decide +kernel)

theorem neighbor_5_codes_002048 : CodeInterval neighborTest5 2048 2112 :=
  codeInterval_of_check neighborTest5 2048 64 (by decide +kernel)

theorem neighbor_5_codes_002112 : CodeInterval neighborTest5 2112 2176 :=
  codeInterval_of_check neighborTest5 2112 64 (by decide +kernel)

theorem neighbor_5_codes_002176 : CodeInterval neighborTest5 2176 2240 :=
  codeInterval_of_check neighborTest5 2176 64 (by decide +kernel)

theorem neighbor_5_codes_002240 : CodeInterval neighborTest5 2240 2304 :=
  codeInterval_of_check neighborTest5 2240 64 (by decide +kernel)

theorem neighbor_5_codes_002304 : CodeInterval neighborTest5 2304 2368 :=
  codeInterval_of_check neighborTest5 2304 64 (by decide +kernel)

theorem neighbor_5_codes_002368 : CodeInterval neighborTest5 2368 2432 :=
  codeInterval_of_check neighborTest5 2368 64 (by decide +kernel)

theorem neighbor_5_codes_002432 : CodeInterval neighborTest5 2432 2496 :=
  codeInterval_of_check neighborTest5 2432 64 (by decide +kernel)

theorem neighbor_5_codes_002496 : CodeInterval neighborTest5 2496 2520 :=
  codeInterval_of_check neighborTest5 2496 24 (by decide +kernel)

theorem neighbor_5_join_000000_000128 : CodeInterval neighborTest5 0 128 :=
  codeInterval_append neighborTest5 0 64 128 neighbor_5_codes_000000 neighbor_5_codes_000064

theorem neighbor_5_join_000192_000320 : CodeInterval neighborTest5 192 320 :=
  codeInterval_append neighborTest5 192 256 320 neighbor_5_codes_000192 neighbor_5_codes_000256

theorem neighbor_5_join_000128_000320 : CodeInterval neighborTest5 128 320 :=
  codeInterval_append neighborTest5 128 192 320 neighbor_5_codes_000128 neighbor_5_join_000192_000320

theorem neighbor_5_join_000000_000320 : CodeInterval neighborTest5 0 320 :=
  codeInterval_append neighborTest5 0 128 320 neighbor_5_join_000000_000128 neighbor_5_join_000128_000320

theorem neighbor_5_join_000320_000448 : CodeInterval neighborTest5 320 448 :=
  codeInterval_append neighborTest5 320 384 448 neighbor_5_codes_000320 neighbor_5_codes_000384

theorem neighbor_5_join_000512_000640 : CodeInterval neighborTest5 512 640 :=
  codeInterval_append neighborTest5 512 576 640 neighbor_5_codes_000512 neighbor_5_codes_000576

theorem neighbor_5_join_000448_000640 : CodeInterval neighborTest5 448 640 :=
  codeInterval_append neighborTest5 448 512 640 neighbor_5_codes_000448 neighbor_5_join_000512_000640

theorem neighbor_5_join_000320_000640 : CodeInterval neighborTest5 320 640 :=
  codeInterval_append neighborTest5 320 448 640 neighbor_5_join_000320_000448 neighbor_5_join_000448_000640

theorem neighbor_5_join_000000_000640 : CodeInterval neighborTest5 0 640 :=
  codeInterval_append neighborTest5 0 320 640 neighbor_5_join_000000_000320 neighbor_5_join_000320_000640

theorem neighbor_5_join_000640_000768 : CodeInterval neighborTest5 640 768 :=
  codeInterval_append neighborTest5 640 704 768 neighbor_5_codes_000640 neighbor_5_codes_000704

theorem neighbor_5_join_000832_000960 : CodeInterval neighborTest5 832 960 :=
  codeInterval_append neighborTest5 832 896 960 neighbor_5_codes_000832 neighbor_5_codes_000896

theorem neighbor_5_join_000768_000960 : CodeInterval neighborTest5 768 960 :=
  codeInterval_append neighborTest5 768 832 960 neighbor_5_codes_000768 neighbor_5_join_000832_000960

theorem neighbor_5_join_000640_000960 : CodeInterval neighborTest5 640 960 :=
  codeInterval_append neighborTest5 640 768 960 neighbor_5_join_000640_000768 neighbor_5_join_000768_000960

theorem neighbor_5_join_000960_001088 : CodeInterval neighborTest5 960 1088 :=
  codeInterval_append neighborTest5 960 1024 1088 neighbor_5_codes_000960 neighbor_5_codes_001024

theorem neighbor_5_join_001152_001280 : CodeInterval neighborTest5 1152 1280 :=
  codeInterval_append neighborTest5 1152 1216 1280 neighbor_5_codes_001152 neighbor_5_codes_001216

theorem neighbor_5_join_001088_001280 : CodeInterval neighborTest5 1088 1280 :=
  codeInterval_append neighborTest5 1088 1152 1280 neighbor_5_codes_001088 neighbor_5_join_001152_001280

theorem neighbor_5_join_000960_001280 : CodeInterval neighborTest5 960 1280 :=
  codeInterval_append neighborTest5 960 1088 1280 neighbor_5_join_000960_001088 neighbor_5_join_001088_001280

theorem neighbor_5_join_000640_001280 : CodeInterval neighborTest5 640 1280 :=
  codeInterval_append neighborTest5 640 960 1280 neighbor_5_join_000640_000960 neighbor_5_join_000960_001280

theorem neighbor_5_join_000000_001280 : CodeInterval neighborTest5 0 1280 :=
  codeInterval_append neighborTest5 0 640 1280 neighbor_5_join_000000_000640 neighbor_5_join_000640_001280

theorem neighbor_5_join_001280_001408 : CodeInterval neighborTest5 1280 1408 :=
  codeInterval_append neighborTest5 1280 1344 1408 neighbor_5_codes_001280 neighbor_5_codes_001344

theorem neighbor_5_join_001472_001600 : CodeInterval neighborTest5 1472 1600 :=
  codeInterval_append neighborTest5 1472 1536 1600 neighbor_5_codes_001472 neighbor_5_codes_001536

theorem neighbor_5_join_001408_001600 : CodeInterval neighborTest5 1408 1600 :=
  codeInterval_append neighborTest5 1408 1472 1600 neighbor_5_codes_001408 neighbor_5_join_001472_001600

theorem neighbor_5_join_001280_001600 : CodeInterval neighborTest5 1280 1600 :=
  codeInterval_append neighborTest5 1280 1408 1600 neighbor_5_join_001280_001408 neighbor_5_join_001408_001600

theorem neighbor_5_join_001600_001728 : CodeInterval neighborTest5 1600 1728 :=
  codeInterval_append neighborTest5 1600 1664 1728 neighbor_5_codes_001600 neighbor_5_codes_001664

theorem neighbor_5_join_001792_001920 : CodeInterval neighborTest5 1792 1920 :=
  codeInterval_append neighborTest5 1792 1856 1920 neighbor_5_codes_001792 neighbor_5_codes_001856

theorem neighbor_5_join_001728_001920 : CodeInterval neighborTest5 1728 1920 :=
  codeInterval_append neighborTest5 1728 1792 1920 neighbor_5_codes_001728 neighbor_5_join_001792_001920

theorem neighbor_5_join_001600_001920 : CodeInterval neighborTest5 1600 1920 :=
  codeInterval_append neighborTest5 1600 1728 1920 neighbor_5_join_001600_001728 neighbor_5_join_001728_001920

theorem neighbor_5_join_001280_001920 : CodeInterval neighborTest5 1280 1920 :=
  codeInterval_append neighborTest5 1280 1600 1920 neighbor_5_join_001280_001600 neighbor_5_join_001600_001920

theorem neighbor_5_join_001920_002048 : CodeInterval neighborTest5 1920 2048 :=
  codeInterval_append neighborTest5 1920 1984 2048 neighbor_5_codes_001920 neighbor_5_codes_001984

theorem neighbor_5_join_002112_002240 : CodeInterval neighborTest5 2112 2240 :=
  codeInterval_append neighborTest5 2112 2176 2240 neighbor_5_codes_002112 neighbor_5_codes_002176

theorem neighbor_5_join_002048_002240 : CodeInterval neighborTest5 2048 2240 :=
  codeInterval_append neighborTest5 2048 2112 2240 neighbor_5_codes_002048 neighbor_5_join_002112_002240

theorem neighbor_5_join_001920_002240 : CodeInterval neighborTest5 1920 2240 :=
  codeInterval_append neighborTest5 1920 2048 2240 neighbor_5_join_001920_002048 neighbor_5_join_002048_002240

theorem neighbor_5_join_002240_002368 : CodeInterval neighborTest5 2240 2368 :=
  codeInterval_append neighborTest5 2240 2304 2368 neighbor_5_codes_002240 neighbor_5_codes_002304

theorem neighbor_5_join_002432_002520 : CodeInterval neighborTest5 2432 2520 :=
  codeInterval_append neighborTest5 2432 2496 2520 neighbor_5_codes_002432 neighbor_5_codes_002496

theorem neighbor_5_join_002368_002520 : CodeInterval neighborTest5 2368 2520 :=
  codeInterval_append neighborTest5 2368 2432 2520 neighbor_5_codes_002368 neighbor_5_join_002432_002520

theorem neighbor_5_join_002240_002520 : CodeInterval neighborTest5 2240 2520 :=
  codeInterval_append neighborTest5 2240 2368 2520 neighbor_5_join_002240_002368 neighbor_5_join_002368_002520

theorem neighbor_5_join_001920_002520 : CodeInterval neighborTest5 1920 2520 :=
  codeInterval_append neighborTest5 1920 2240 2520 neighbor_5_join_001920_002240 neighbor_5_join_002240_002520

theorem neighbor_5_join_001280_002520 : CodeInterval neighborTest5 1280 2520 :=
  codeInterval_append neighborTest5 1280 1920 2520 neighbor_5_join_001280_001920 neighbor_5_join_001920_002520

theorem neighbor_5_join_000000_002520 : CodeInterval neighborTest5 0 2520 :=
  codeInterval_append neighborTest5 0 1280 2520 neighbor_5_join_000000_001280 neighbor_5_join_001280_002520

theorem neighbor_5 : ∀ f : Fin 5 → Fin 7, NeighborWitness cells neighbors (by decide) permMaps f :=
  neighbor_of_injection_checks (by decide) (by decide) cells neighbors permMaps
    permutationWitness5 neighborWitness5 neighbor_5_join_000000_002520

end Papers.RationalityTen.FiniteCycleCandidates.N7
