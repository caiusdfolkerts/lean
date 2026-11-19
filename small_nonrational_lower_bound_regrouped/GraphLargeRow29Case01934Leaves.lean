module
prelude
public meta import LowerSchemas.FiniteGraphLargeRow
public import GraphLargeRow29Case01934Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M046
public import InducedTerminalMatches.M047
public import InducedTerminalMatches.M048
public import InducedTerminalMatches.M049
public import InducedTerminalMatches.M050
public import InducedTerminalMatches.M051
public import InducedTerminalMatches.M052

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphLargeRow29Case01934
open Papers.RationalityTen ConcreteGrowth RawLeafCertificate FastRawLeafCertificate

noncomputable def record000_rawLeaves (j : Fin record000.l) : List Cell :=
  (record000.leaf j).map record000.data.cells
theorem record000_raw_exact (j : Fin record000.l) :
    (record000.leaf j).map record000.data.cells = record000_rawLeaves j := rfl
noncomputable def record000_certificateTable : Table Certificate :=
(.branch 92
 (.branch 46
 (.branch 23
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M046.r1489))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M046.r1490)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M046.r1491))
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M046.r1492))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M046.r1493)))))
 (.branch 8
 (.branch 6
 (.leaf (.matching Nonrational.InducedTerminalMatches.M046.r1494))
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M046.r1495))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M046.r1496))))
 (.branch 9
 (.leaf (.matching Nonrational.InducedTerminalMatches.M046.r1497))
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M046.r1498))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M046.r1499))))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf (.matching Nonrational.InducedTerminalMatches.M046.r1500))
 (.branch 13
 (.leaf (.matching Nonrational.InducedTerminalMatches.M046.r1501))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M046.r1502))))
 (.branch 15
 (.leaf (.matching Nonrational.InducedTerminalMatches.M046.r1503))
 (.branch 16
 (.leaf (.matching Nonrational.InducedTerminalMatches.M047.r1504))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M047.r1505)))))
 (.branch 20
 (.branch 18
 (.leaf (.matching Nonrational.InducedTerminalMatches.M047.r1506))
 (.branch 19
 (.leaf (.matching Nonrational.InducedTerminalMatches.M047.r1507))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M047.r1508))))
 (.branch 21
 (.leaf (.matching Nonrational.InducedTerminalMatches.M047.r1509))
 (.branch 22
 (.leaf (.matching Nonrational.InducedTerminalMatches.M047.r1510))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M047.r1511)))))))
 (.branch 34
 (.branch 28
 (.branch 25
 (.branch 24
 (.leaf (.matching Nonrational.InducedTerminalMatches.M047.r1512))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M047.r1513)))
 (.branch 26
 (.leaf (.matching Nonrational.InducedTerminalMatches.M047.r1514))
 (.branch 27
 (.leaf (.matching Nonrational.InducedTerminalMatches.M047.r1515))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M047.r1516)))))
 (.branch 31
 (.branch 29
 (.leaf (.matching Nonrational.InducedTerminalMatches.M047.r1517))
 (.branch 30
 (.leaf (.matching Nonrational.InducedTerminalMatches.M047.r1518))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M047.r1519))))
 (.branch 32
 (.leaf (.matching Nonrational.InducedTerminalMatches.M047.r1520))
 (.branch 33
 (.leaf (.matching Nonrational.InducedTerminalMatches.M047.r1521))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M047.r1522))))))
 (.branch 40
 (.branch 37
 (.branch 35
 (.leaf (.matching Nonrational.InducedTerminalMatches.M047.r1523))
 (.branch 36
 (.leaf (.matching Nonrational.InducedTerminalMatches.M047.r1524))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M047.r1525))))
 (.branch 38
 (.leaf (.matching Nonrational.InducedTerminalMatches.M047.r1526))
 (.branch 39
 (.leaf (.matching Nonrational.InducedTerminalMatches.M047.r1527))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M047.r1528)))))
 (.branch 43
 (.branch 41
 (.leaf (.matching Nonrational.InducedTerminalMatches.M047.r1529))
 (.branch 42
 (.leaf (.matching Nonrational.InducedTerminalMatches.M047.r1530))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M047.r1531))))
 (.branch 44
 (.leaf (.matching Nonrational.InducedTerminalMatches.M047.r1532))
 (.branch 45
 (.leaf (.matching Nonrational.InducedTerminalMatches.M047.r1533))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M047.r1534))))))))
 (.branch 69
 (.branch 57
 (.branch 51
 (.branch 48
 (.branch 47
 (.leaf (.matching Nonrational.InducedTerminalMatches.M047.r1535))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M048.r1536)))
 (.branch 49
 (.leaf (.matching Nonrational.InducedTerminalMatches.M048.r1537))
 (.branch 50
 (.leaf (.matching Nonrational.InducedTerminalMatches.M048.r1538))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M048.r1539)))))
 (.branch 54
 (.branch 52
 (.leaf (.matching Nonrational.InducedTerminalMatches.M048.r1540))
 (.branch 53
 (.leaf (.matching Nonrational.InducedTerminalMatches.M048.r1541))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M048.r1542))))
 (.branch 55
 (.leaf (.matching Nonrational.InducedTerminalMatches.M048.r1543))
 (.branch 56
 (.leaf (.matching Nonrational.InducedTerminalMatches.M048.r1544))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M048.r1545))))))
 (.branch 63
 (.branch 60
 (.branch 58
 (.leaf (.matching Nonrational.InducedTerminalMatches.M048.r1546))
 (.branch 59
 (.leaf (.matching Nonrational.InducedTerminalMatches.M048.r1547))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M048.r1548))))
 (.branch 61
 (.leaf (.matching Nonrational.InducedTerminalMatches.M048.r1549))
 (.branch 62
 (.leaf (.matching Nonrational.InducedTerminalMatches.M048.r1550))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M048.r1551)))))
 (.branch 66
 (.branch 64
 (.leaf (.matching Nonrational.InducedTerminalMatches.M048.r1552))
 (.branch 65
 (.leaf (.matching Nonrational.InducedTerminalMatches.M048.r1553))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M048.r1554))))
 (.branch 67
 (.leaf (.matching Nonrational.InducedTerminalMatches.M048.r1555))
 (.branch 68
 (.leaf (.matching Nonrational.InducedTerminalMatches.M048.r1556))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M048.r1557)))))))
 (.branch 80
 (.branch 74
 (.branch 71
 (.branch 70
 (.leaf (.matching Nonrational.InducedTerminalMatches.M048.r1558))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M048.r1559)))
 (.branch 72
 (.leaf (.matching Nonrational.InducedTerminalMatches.M048.r1560))
 (.branch 73
 (.leaf (.matching Nonrational.InducedTerminalMatches.M048.r1561))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M048.r1562)))))
 (.branch 77
 (.branch 75
 (.leaf (.matching Nonrational.InducedTerminalMatches.M048.r1563))
 (.branch 76
 (.leaf (.matching Nonrational.InducedTerminalMatches.M048.r1564))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M048.r1565))))
 (.branch 78
 (.leaf (.matching Nonrational.InducedTerminalMatches.M048.r1566))
 (.branch 79
 (.leaf (.matching Nonrational.InducedTerminalMatches.M048.r1567))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M049.r1568))))))
 (.branch 86
 (.branch 83
 (.branch 81
 (.leaf (.matching Nonrational.InducedTerminalMatches.M049.r1569))
 (.branch 82
 (.leaf (.matching Nonrational.InducedTerminalMatches.M049.r1570))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M049.r1571))))
 (.branch 84
 (.leaf (.matching Nonrational.InducedTerminalMatches.M049.r1572))
 (.branch 85
 (.leaf (.matching Nonrational.InducedTerminalMatches.M049.r1573))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M049.r1574)))))
 (.branch 89
 (.branch 87
 (.leaf (.matching Nonrational.InducedTerminalMatches.M049.r1575))
 (.branch 88
 (.leaf (.matching Nonrational.InducedTerminalMatches.M049.r1576))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M049.r1577))))
 (.branch 90
 (.leaf (.matching Nonrational.InducedTerminalMatches.M049.r1578))
 (.branch 91
 (.leaf (.matching Nonrational.InducedTerminalMatches.M049.r1579))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M049.r1580)))))))))
 (.branch 138
 (.branch 115
 (.branch 103
 (.branch 97
 (.branch 94
 (.branch 93
 (.leaf (.matching Nonrational.InducedTerminalMatches.M049.r1581))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M049.r1582)))
 (.branch 95
 (.leaf (.matching Nonrational.InducedTerminalMatches.M049.r1583))
 (.branch 96
 (.leaf (.matching Nonrational.InducedTerminalMatches.M049.r1584))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M049.r1585)))))
 (.branch 100
 (.branch 98
 (.leaf (.matching Nonrational.InducedTerminalMatches.M049.r1586))
 (.branch 99
 (.leaf (.matching Nonrational.InducedTerminalMatches.M049.r1587))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M049.r1588))))
 (.branch 101
 (.leaf (.matching Nonrational.InducedTerminalMatches.M049.r1589))
 (.branch 102
 (.leaf (.matching Nonrational.InducedTerminalMatches.M049.r1590))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M049.r1591))))))
 (.branch 109
 (.branch 106
 (.branch 104
 (.leaf (.matching Nonrational.InducedTerminalMatches.M049.r1592))
 (.branch 105
 (.leaf (.matching Nonrational.InducedTerminalMatches.M049.r1593))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M049.r1594))))
 (.branch 107
 (.leaf (.matching Nonrational.InducedTerminalMatches.M049.r1595))
 (.branch 108
 (.leaf (.matching Nonrational.InducedTerminalMatches.M049.r1596))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M049.r1597)))))
 (.branch 112
 (.branch 110
 (.leaf (.matching Nonrational.InducedTerminalMatches.M049.r1598))
 (.branch 111
 (.leaf (.matching Nonrational.InducedTerminalMatches.M049.r1599))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M050.r1600))))
 (.branch 113
 (.leaf (.matching Nonrational.InducedTerminalMatches.M050.r1601))
 (.branch 114
 (.leaf (.matching Nonrational.InducedTerminalMatches.M050.r1602))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M050.r1603)))))))
 (.branch 126
 (.branch 120
 (.branch 117
 (.branch 116
 (.leaf (.matching Nonrational.InducedTerminalMatches.M050.r1604))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M050.r1605)))
 (.branch 118
 (.leaf (.matching Nonrational.InducedTerminalMatches.M050.r1606))
 (.branch 119
 (.leaf (.matching Nonrational.InducedTerminalMatches.M050.r1607))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M050.r1608)))))
 (.branch 123
 (.branch 121
 (.leaf (.matching Nonrational.InducedTerminalMatches.M050.r1609))
 (.branch 122
 (.leaf (.matching Nonrational.InducedTerminalMatches.M050.r1610))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M050.r1611))))
 (.branch 124
 (.leaf (.matching Nonrational.InducedTerminalMatches.M050.r1612))
 (.branch 125
 (.leaf (.matching Nonrational.InducedTerminalMatches.M050.r1613))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M050.r1614))))))
 (.branch 132
 (.branch 129
 (.branch 127
 (.leaf (.matching Nonrational.InducedTerminalMatches.M050.r1615))
 (.branch 128
 (.leaf (.matching Nonrational.InducedTerminalMatches.M050.r1616))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M050.r1617))))
 (.branch 130
 (.leaf (.matching Nonrational.InducedTerminalMatches.M050.r1618))
 (.branch 131
 (.leaf (.matching Nonrational.InducedTerminalMatches.M050.r1619))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M050.r1620)))))
 (.branch 135
 (.branch 133
 (.leaf (.matching Nonrational.InducedTerminalMatches.M050.r1621))
 (.branch 134
 (.leaf (.matching Nonrational.InducedTerminalMatches.M050.r1622))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M050.r1623))))
 (.branch 136
 (.leaf (.matching Nonrational.InducedTerminalMatches.M050.r1624))
 (.branch 137
 (.leaf (.matching Nonrational.InducedTerminalMatches.M050.r1625))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M050.r1626))))))))
 (.branch 161
 (.branch 149
 (.branch 143
 (.branch 140
 (.branch 139
 (.leaf (.matching Nonrational.InducedTerminalMatches.M050.r1627))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M050.r1628)))
 (.branch 141
 (.leaf (.matching Nonrational.InducedTerminalMatches.M050.r1629))
 (.branch 142
 (.leaf (.matching Nonrational.InducedTerminalMatches.M050.r1630))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M050.r1631)))))
 (.branch 146
 (.branch 144
 (.leaf (.matching Nonrational.InducedTerminalMatches.M051.r1632))
 (.branch 145
 (.leaf (.matching Nonrational.InducedTerminalMatches.M051.r1633))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M051.r1634))))
 (.branch 147
 (.leaf (.matching Nonrational.InducedTerminalMatches.M051.r1635))
 (.branch 148
 (.leaf (.matching Nonrational.InducedTerminalMatches.M051.r1636))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M051.r1637))))))
 (.branch 155
 (.branch 152
 (.branch 150
 (.leaf (.matching Nonrational.InducedTerminalMatches.M051.r1638))
 (.branch 151
 (.leaf (.matching Nonrational.InducedTerminalMatches.M051.r1639))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M051.r1640))))
 (.branch 153
 (.leaf (.matching Nonrational.InducedTerminalMatches.M051.r1641))
 (.branch 154
 (.leaf (.matching Nonrational.InducedTerminalMatches.M051.r1642))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M051.r1643)))))
 (.branch 158
 (.branch 156
 (.leaf (.matching Nonrational.InducedTerminalMatches.M051.r1644))
 (.branch 157
 (.leaf (.matching Nonrational.InducedTerminalMatches.M051.r1645))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M051.r1646))))
 (.branch 159
 (.leaf (.matching Nonrational.InducedTerminalMatches.M051.r1647))
 (.branch 160
 (.leaf (.matching Nonrational.InducedTerminalMatches.M051.r1648))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M051.r1649)))))))
 (.branch 172
 (.branch 166
 (.branch 163
 (.branch 162
 (.leaf (.matching Nonrational.InducedTerminalMatches.M051.r1650))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M051.r1651)))
 (.branch 164
 (.leaf (.matching Nonrational.InducedTerminalMatches.M051.r1652))
 (.branch 165
 (.leaf (.matching Nonrational.InducedTerminalMatches.M051.r1653))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M051.r1654)))))
 (.branch 169
 (.branch 167
 (.leaf (.matching Nonrational.InducedTerminalMatches.M051.r1655))
 (.branch 168
 (.leaf (.matching Nonrational.InducedTerminalMatches.M051.r1656))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M051.r1657))))
 (.branch 170
 (.leaf (.matching Nonrational.InducedTerminalMatches.M051.r1658))
 (.branch 171
 (.leaf (.matching Nonrational.InducedTerminalMatches.M051.r1659))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M051.r1660))))))
 (.branch 178
 (.branch 175
 (.branch 173
 (.leaf (.matching Nonrational.InducedTerminalMatches.M051.r1661))
 (.branch 174
 (.leaf (.matching Nonrational.InducedTerminalMatches.M051.r1662))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M051.r1663))))
 (.branch 176
 (.leaf (.matching Nonrational.InducedTerminalMatches.M052.r1664))
 (.branch 177
 (.leaf (.matching Nonrational.InducedTerminalMatches.M052.r1665))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M052.r1666)))))
 (.branch 181
 (.branch 179
 (.leaf (.matching Nonrational.InducedTerminalMatches.M052.r1667))
 (.branch 180
 (.leaf (.matching Nonrational.InducedTerminalMatches.M052.r1668))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M052.r1669))))
 (.branch 182
 (.leaf (.matching Nonrational.InducedTerminalMatches.M052.r1670))
 (.branch 183
 (.leaf (.matching Nonrational.InducedTerminalMatches.M052.r1671))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M052.r1672))))))))))
noncomputable def record000_certificates (j : Fin record000.l) : Certificate :=
  record000_certificateTable.get j.val
cert_graph_leaf_checked 0 046 1489
cert_graph_leaf_checked 1 046 1490
cert_graph_leaf_checked 2 046 1491
cert_graph_leaf_checked 3 046 1492
cert_graph_leaf_checked 4 046 1493
cert_graph_leaf_checked 5 046 1494
cert_graph_leaf_checked 6 046 1495
cert_graph_leaf_checked 7 046 1496
cert_graph_leaf_checked 8 046 1497
cert_graph_leaf_checked 9 046 1498
cert_graph_leaf_checked 10 046 1499
cert_graph_leaf_checked 11 046 1500
cert_graph_leaf_checked 12 046 1501
cert_graph_leaf_checked 13 046 1502
cert_graph_leaf_checked 14 046 1503
cert_graph_leaf_checked 15 047 1504
cert_graph_leaf_checked 16 047 1505
cert_graph_leaf_checked 17 047 1506
cert_graph_leaf_checked 18 047 1507
cert_graph_leaf_checked 19 047 1508
cert_graph_leaf_checked 20 047 1509
cert_graph_leaf_checked 21 047 1510
cert_graph_leaf_checked 22 047 1511
cert_graph_leaf_checked 23 047 1512
cert_graph_leaf_checked 24 047 1513
cert_graph_leaf_checked 25 047 1514
cert_graph_leaf_checked 26 047 1515
cert_graph_leaf_checked 27 047 1516
cert_graph_leaf_checked 28 047 1517
cert_graph_leaf_checked 29 047 1518
cert_graph_leaf_checked 30 047 1519
cert_graph_leaf_checked 31 047 1520
cert_graph_leaf_checked 32 047 1521
cert_graph_leaf_checked 33 047 1522
cert_graph_leaf_checked 34 047 1523
cert_graph_leaf_checked 35 047 1524
cert_graph_leaf_checked 36 047 1525
cert_graph_leaf_checked 37 047 1526
cert_graph_leaf_checked 38 047 1527
cert_graph_leaf_checked 39 047 1528
cert_graph_leaf_checked 40 047 1529
cert_graph_leaf_checked 41 047 1530
cert_graph_leaf_checked 42 047 1531
cert_graph_leaf_checked 43 047 1532
cert_graph_leaf_checked 44 047 1533
cert_graph_leaf_checked 45 047 1534
cert_graph_leaf_checked 46 047 1535
cert_graph_leaf_checked 47 048 1536
cert_graph_leaf_checked 48 048 1537
cert_graph_leaf_checked 49 048 1538
cert_graph_leaf_checked 50 048 1539
cert_graph_leaf_checked 51 048 1540
cert_graph_leaf_checked 52 048 1541
cert_graph_leaf_checked 53 048 1542
cert_graph_leaf_checked 54 048 1543
cert_graph_leaf_checked 55 048 1544
cert_graph_leaf_checked 56 048 1545
cert_graph_leaf_checked 57 048 1546
cert_graph_leaf_checked 58 048 1547
cert_graph_leaf_checked 59 048 1548
cert_graph_leaf_checked 60 048 1549
cert_graph_leaf_checked 61 048 1550
cert_graph_leaf_checked 62 048 1551
cert_graph_leaf_checked 63 048 1552
cert_graph_leaf_checked 64 048 1553
cert_graph_leaf_checked 65 048 1554
cert_graph_leaf_checked 66 048 1555
cert_graph_leaf_checked 67 048 1556
cert_graph_leaf_checked 68 048 1557
cert_graph_leaf_checked 69 048 1558
cert_graph_leaf_checked 70 048 1559
cert_graph_leaf_checked 71 048 1560
cert_graph_leaf_checked 72 048 1561
cert_graph_leaf_checked 73 048 1562
cert_graph_leaf_checked 74 048 1563
cert_graph_leaf_checked 75 048 1564
cert_graph_leaf_checked 76 048 1565
cert_graph_leaf_checked 77 048 1566
cert_graph_leaf_checked 78 048 1567
cert_graph_leaf_checked 79 049 1568
cert_graph_leaf_checked 80 049 1569
cert_graph_leaf_checked 81 049 1570
cert_graph_leaf_checked 82 049 1571
cert_graph_leaf_checked 83 049 1572
cert_graph_leaf_checked 84 049 1573
cert_graph_leaf_checked 85 049 1574
cert_graph_leaf_checked 86 049 1575
cert_graph_leaf_checked 87 049 1576
cert_graph_leaf_checked 88 049 1577
cert_graph_leaf_checked 89 049 1578
cert_graph_leaf_checked 90 049 1579
cert_graph_leaf_checked 91 049 1580
cert_graph_leaf_checked 92 049 1581
cert_graph_leaf_checked 93 049 1582
cert_graph_leaf_checked 94 049 1583
cert_graph_leaf_checked 95 049 1584
cert_graph_leaf_checked 96 049 1585
cert_graph_leaf_checked 97 049 1586
cert_graph_leaf_checked 98 049 1587
cert_graph_leaf_checked 99 049 1588
cert_graph_leaf_checked 100 049 1589
cert_graph_leaf_checked 101 049 1590
cert_graph_leaf_checked 102 049 1591
cert_graph_leaf_checked 103 049 1592
cert_graph_leaf_checked 104 049 1593
cert_graph_leaf_checked 105 049 1594
cert_graph_leaf_checked 106 049 1595
cert_graph_leaf_checked 107 049 1596
cert_graph_leaf_checked 108 049 1597
cert_graph_leaf_checked 109 049 1598
cert_graph_leaf_checked 110 049 1599
cert_graph_leaf_checked 111 050 1600
cert_graph_leaf_checked 112 050 1601
cert_graph_leaf_checked 113 050 1602
cert_graph_leaf_checked 114 050 1603
cert_graph_leaf_checked 115 050 1604
cert_graph_leaf_checked 116 050 1605
cert_graph_leaf_checked 117 050 1606
cert_graph_leaf_checked 118 050 1607
cert_graph_leaf_checked 119 050 1608
cert_graph_leaf_checked 120 050 1609
cert_graph_leaf_checked 121 050 1610
cert_graph_leaf_checked 122 050 1611
cert_graph_leaf_checked 123 050 1612
cert_graph_leaf_checked 124 050 1613
cert_graph_leaf_checked 125 050 1614
cert_graph_leaf_checked 126 050 1615
cert_graph_leaf_checked 127 050 1616
cert_graph_leaf_checked 128 050 1617
cert_graph_leaf_checked 129 050 1618
cert_graph_leaf_checked 130 050 1619
cert_graph_leaf_checked 131 050 1620
cert_graph_leaf_checked 132 050 1621
cert_graph_leaf_checked 133 050 1622
cert_graph_leaf_checked 134 050 1623
cert_graph_leaf_checked 135 050 1624
cert_graph_leaf_checked 136 050 1625
cert_graph_leaf_checked 137 050 1626
cert_graph_leaf_checked 138 050 1627
cert_graph_leaf_checked 139 050 1628
cert_graph_leaf_checked 140 050 1629
cert_graph_leaf_checked 141 050 1630
cert_graph_leaf_checked 142 050 1631
cert_graph_leaf_checked 143 051 1632
cert_graph_leaf_checked 144 051 1633
cert_graph_leaf_checked 145 051 1634
cert_graph_leaf_checked 146 051 1635
cert_graph_leaf_checked 147 051 1636
cert_graph_leaf_checked 148 051 1637
cert_graph_leaf_checked 149 051 1638
cert_graph_leaf_checked 150 051 1639
cert_graph_leaf_checked 151 051 1640
cert_graph_leaf_checked 152 051 1641
cert_graph_leaf_checked 153 051 1642
cert_graph_leaf_checked 154 051 1643
cert_graph_leaf_checked 155 051 1644
cert_graph_leaf_checked 156 051 1645
cert_graph_leaf_checked 157 051 1646
cert_graph_leaf_checked 158 051 1647
cert_graph_leaf_checked 159 051 1648
cert_graph_leaf_checked 160 051 1649
cert_graph_leaf_checked 161 051 1650
cert_graph_leaf_checked 162 051 1651
cert_graph_leaf_checked 163 051 1652
cert_graph_leaf_checked 164 051 1653
cert_graph_leaf_checked 165 051 1654
cert_graph_leaf_checked 166 051 1655
cert_graph_leaf_checked 167 051 1656
cert_graph_leaf_checked 168 051 1657
cert_graph_leaf_checked 169 051 1658
cert_graph_leaf_checked 170 051 1659
cert_graph_leaf_checked 171 051 1660
cert_graph_leaf_checked 172 051 1661
cert_graph_leaf_checked 173 051 1662
cert_graph_leaf_checked 174 051 1663
cert_graph_leaf_checked 175 052 1664
cert_graph_leaf_checked 176 052 1665
cert_graph_leaf_checked 177 052 1666
cert_graph_leaf_checked 178 052 1667
cert_graph_leaf_checked 179 052 1668
cert_graph_leaf_checked 180 052 1669
cert_graph_leaf_checked 181 052 1670
cert_graph_leaf_checked 182 052 1671
cert_graph_leaf_checked 183 052 1672
theorem record000_leaf_certificates_checked : ∀ j : Fin record000.l,
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves j)
      (record000_certificates j) = true :=
  (Fin.cases record000_leaf_checked_0 (Fin.cases record000_leaf_checked_1 (Fin.cases record000_leaf_checked_2 (Fin.cases record000_leaf_checked_3 (Fin.cases record000_leaf_checked_4 (Fin.cases record000_leaf_checked_5 (Fin.cases record000_leaf_checked_6 (Fin.cases record000_leaf_checked_7 (Fin.cases record000_leaf_checked_8 (Fin.cases record000_leaf_checked_9 (Fin.cases record000_leaf_checked_10 (Fin.cases record000_leaf_checked_11 (Fin.cases record000_leaf_checked_12 (Fin.cases record000_leaf_checked_13 (Fin.cases record000_leaf_checked_14 (Fin.cases record000_leaf_checked_15 (Fin.cases record000_leaf_checked_16 (Fin.cases record000_leaf_checked_17 (Fin.cases record000_leaf_checked_18 (Fin.cases record000_leaf_checked_19 (Fin.cases record000_leaf_checked_20 (Fin.cases record000_leaf_checked_21 (Fin.cases record000_leaf_checked_22 (Fin.cases record000_leaf_checked_23 (Fin.cases record000_leaf_checked_24 (Fin.cases record000_leaf_checked_25 (Fin.cases record000_leaf_checked_26 (Fin.cases record000_leaf_checked_27 (Fin.cases record000_leaf_checked_28 (Fin.cases record000_leaf_checked_29 (Fin.cases record000_leaf_checked_30 (Fin.cases record000_leaf_checked_31 (Fin.cases record000_leaf_checked_32 (Fin.cases record000_leaf_checked_33 (Fin.cases record000_leaf_checked_34 (Fin.cases record000_leaf_checked_35 (Fin.cases record000_leaf_checked_36 (Fin.cases record000_leaf_checked_37 (Fin.cases record000_leaf_checked_38 (Fin.cases record000_leaf_checked_39 (Fin.cases record000_leaf_checked_40 (Fin.cases record000_leaf_checked_41 (Fin.cases record000_leaf_checked_42 (Fin.cases record000_leaf_checked_43 (Fin.cases record000_leaf_checked_44 (Fin.cases record000_leaf_checked_45 (Fin.cases record000_leaf_checked_46 (Fin.cases record000_leaf_checked_47 (Fin.cases record000_leaf_checked_48 (Fin.cases record000_leaf_checked_49 (Fin.cases record000_leaf_checked_50 (Fin.cases record000_leaf_checked_51 (Fin.cases record000_leaf_checked_52 (Fin.cases record000_leaf_checked_53 (Fin.cases record000_leaf_checked_54 (Fin.cases record000_leaf_checked_55 (Fin.cases record000_leaf_checked_56 (Fin.cases record000_leaf_checked_57 (Fin.cases record000_leaf_checked_58 (Fin.cases record000_leaf_checked_59 (Fin.cases record000_leaf_checked_60 (Fin.cases record000_leaf_checked_61 (Fin.cases record000_leaf_checked_62 (Fin.cases record000_leaf_checked_63 (Fin.cases record000_leaf_checked_64 (Fin.cases record000_leaf_checked_65 (Fin.cases record000_leaf_checked_66 (Fin.cases record000_leaf_checked_67 (Fin.cases record000_leaf_checked_68 (Fin.cases record000_leaf_checked_69 (Fin.cases record000_leaf_checked_70 (Fin.cases record000_leaf_checked_71 (Fin.cases record000_leaf_checked_72 (Fin.cases record000_leaf_checked_73 (Fin.cases record000_leaf_checked_74 (Fin.cases record000_leaf_checked_75 (Fin.cases record000_leaf_checked_76 (Fin.cases record000_leaf_checked_77 (Fin.cases record000_leaf_checked_78 (Fin.cases record000_leaf_checked_79 (Fin.cases record000_leaf_checked_80 (Fin.cases record000_leaf_checked_81 (Fin.cases record000_leaf_checked_82 (Fin.cases record000_leaf_checked_83 (Fin.cases record000_leaf_checked_84 (Fin.cases record000_leaf_checked_85 (Fin.cases record000_leaf_checked_86 (Fin.cases record000_leaf_checked_87 (Fin.cases record000_leaf_checked_88 (Fin.cases record000_leaf_checked_89 (Fin.cases record000_leaf_checked_90 (Fin.cases record000_leaf_checked_91 (Fin.cases record000_leaf_checked_92 (Fin.cases record000_leaf_checked_93 (Fin.cases record000_leaf_checked_94 (Fin.cases record000_leaf_checked_95 (Fin.cases record000_leaf_checked_96 (Fin.cases record000_leaf_checked_97 (Fin.cases record000_leaf_checked_98 (Fin.cases record000_leaf_checked_99 (Fin.cases record000_leaf_checked_100 (Fin.cases record000_leaf_checked_101 (Fin.cases record000_leaf_checked_102 (Fin.cases record000_leaf_checked_103 (Fin.cases record000_leaf_checked_104 (Fin.cases record000_leaf_checked_105 (Fin.cases record000_leaf_checked_106 (Fin.cases record000_leaf_checked_107 (Fin.cases record000_leaf_checked_108 (Fin.cases record000_leaf_checked_109 (Fin.cases record000_leaf_checked_110 (Fin.cases record000_leaf_checked_111 (Fin.cases record000_leaf_checked_112 (Fin.cases record000_leaf_checked_113 (Fin.cases record000_leaf_checked_114 (Fin.cases record000_leaf_checked_115 (Fin.cases record000_leaf_checked_116 (Fin.cases record000_leaf_checked_117 (Fin.cases record000_leaf_checked_118 (Fin.cases record000_leaf_checked_119 (Fin.cases record000_leaf_checked_120 (Fin.cases record000_leaf_checked_121 (Fin.cases record000_leaf_checked_122 (Fin.cases record000_leaf_checked_123 (Fin.cases record000_leaf_checked_124 (Fin.cases record000_leaf_checked_125 (Fin.cases record000_leaf_checked_126 (Fin.cases record000_leaf_checked_127 (Fin.cases record000_leaf_checked_128 (Fin.cases record000_leaf_checked_129 (Fin.cases record000_leaf_checked_130 (Fin.cases record000_leaf_checked_131 (Fin.cases record000_leaf_checked_132 (Fin.cases record000_leaf_checked_133 (Fin.cases record000_leaf_checked_134 (Fin.cases record000_leaf_checked_135 (Fin.cases record000_leaf_checked_136 (Fin.cases record000_leaf_checked_137 (Fin.cases record000_leaf_checked_138 (Fin.cases record000_leaf_checked_139 (Fin.cases record000_leaf_checked_140 (Fin.cases record000_leaf_checked_141 (Fin.cases record000_leaf_checked_142 (Fin.cases record000_leaf_checked_143 (Fin.cases record000_leaf_checked_144 (Fin.cases record000_leaf_checked_145 (Fin.cases record000_leaf_checked_146 (Fin.cases record000_leaf_checked_147 (Fin.cases record000_leaf_checked_148 (Fin.cases record000_leaf_checked_149 (Fin.cases record000_leaf_checked_150 (Fin.cases record000_leaf_checked_151 (Fin.cases record000_leaf_checked_152 (Fin.cases record000_leaf_checked_153 (Fin.cases record000_leaf_checked_154 (Fin.cases record000_leaf_checked_155 (Fin.cases record000_leaf_checked_156 (Fin.cases record000_leaf_checked_157 (Fin.cases record000_leaf_checked_158 (Fin.cases record000_leaf_checked_159 (Fin.cases record000_leaf_checked_160 (Fin.cases record000_leaf_checked_161 (Fin.cases record000_leaf_checked_162 (Fin.cases record000_leaf_checked_163 (Fin.cases record000_leaf_checked_164 (Fin.cases record000_leaf_checked_165 (Fin.cases record000_leaf_checked_166 (Fin.cases record000_leaf_checked_167 (Fin.cases record000_leaf_checked_168 (Fin.cases record000_leaf_checked_169 (Fin.cases record000_leaf_checked_170 (Fin.cases record000_leaf_checked_171 (Fin.cases record000_leaf_checked_172 (Fin.cases record000_leaf_checked_173 (Fin.cases record000_leaf_checked_174 (Fin.cases record000_leaf_checked_175 (Fin.cases record000_leaf_checked_176 (Fin.cases record000_leaf_checked_177 (Fin.cases record000_leaf_checked_178 (Fin.cases record000_leaf_checked_179 (Fin.cases record000_leaf_checked_180 (Fin.cases record000_leaf_checked_181 (Fin.cases record000_leaf_checked_182 (Fin.cases record000_leaf_checked_183 (fun j => Fin.elim0 j)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
#print axioms record000_leaf_certificates_checked

end Papers.RationalityTen.CompactReplay.GraphLargeRow29Case01934
