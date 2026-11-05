module
prelude
public import InducedTerminalMatches.Basic

@[expose] public section

/-! Exact full-boundary matches, batch 25. Both facet and polygon
families are checked in both directions after the recorded permutation. -/

namespace Nonrational.OldTerminalMatches.M025
open Nonrational.InducedTerminalMatches
set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- six_orbit_dags/type4m13e11q2r0.json.gz, graph 741, terminal 1; projection:R_one_six_1809.
noncomputable def r1600 : Entry :=
  ⟨⟨[63,71,75,149,217,358,453,696,714,810,820,916,962],[7,11,21,25,38,42,52,56,67,69,70,73,74,133,145,148,152,193,200,290,292,322,324,388,448,522,552,560,648,656,706,770,788,800,896]⟩,
   ⟨1944,654820254465,654820254465⟩⟩
theorem r1600_checked : check r1600 = true := by decide +kernel

-- six_orbit_dags/type4m13e11q2r0.json.gz, graph 741, terminal 3; projection:R_one_six_1817.
noncomputable def r1601 : Entry :=
  ⟨⟨[63,75,149,217,263,358,451,618,692,696,868,901,968],[7,11,21,25,38,42,52,56,67,73,74,98,133,145,148,152,193,200,259,261,262,322,356,385,448,548,552,584,608,644,648,688,772,832,896]⟩,
   ⟨1952,590142845520,590139961920⟩⟩
theorem r1601_checked : check r1601 = true := by decide +kernel

-- six_orbit_dags/type4m13e11q2r0.json.gz, graph 741, terminal 5; projection:R_one_six_1818.
noncomputable def r1602 : Entry :=
  ⟨⟨[63,71,149,217,298,331,440,614,709,820,866,916,968],[7,11,21,25,38,42,52,56,67,69,70,73,133,145,148,152,193,200,266,290,296,304,322,328,392,400,548,580,610,644,704,788,800,832,896]⟩,
   ⟨1953,582342685200,521944707600⟩⟩
theorem r1602_checked : check r1602 = true := by decide +kernel

-- six_orbit_dags/type4m13e11q2r0.json.gz, graph 741, terminal 7; projection:R_one_six_1820.
noncomputable def r1603 : Entry :=
  ⟨⟨[63,75,180,217,263,341,422,468,618,696,835,930,968],[7,11,21,25,38,42,52,56,67,73,74,81,148,152,164,176,200,208,259,261,262,321,340,388,418,448,546,552,578,584,648,672,770,832,896]⟩,
   ⟨1955,590395671585,590395621635⟩⟩
theorem r1603_checked : check r1603 = true := by decide +kernel

-- six_orbit_dags/type4m13e11q2r0.json.gz, graph 741, terminal 8; projection:R_one_six_1819.
noncomputable def r1604 : Entry :=
  ⟨⟨[63,75,180,217,263,341,468,618,678,696,835,902,968],[7,11,21,25,38,42,52,56,67,73,74,81,148,152,164,176,200,208,259,261,262,321,340,388,448,546,552,578,584,646,648,672,770,832,896]⟩,
   ⟨1954,590395671585,590395621635⟩⟩
theorem r1604_checked : check r1604 = true := by decide +kernel

-- six_orbit_dags/type4m13e11q2r0.json.gz, graph 741, terminal 9; projection:R_one_six_1821.
noncomputable def r1605 : Entry :=
  ⟨⟨[63,75,180,217,263,341,468,618,696,806,835,932,968],[7,11,21,25,38,42,52,56,67,73,74,81,148,152,164,176,200,208,259,261,262,321,340,388,448,546,552,578,584,648,672,770,804,832,896]⟩,
   ⟨1956,590395671585,590395621635⟩⟩
theorem r1605_checked : check r1605 = true := by decide +kernel

-- six_orbit_dags/type4m13e11q2r0.json.gz, graph 741, terminal 10; projection:R_one_six_1822.
noncomputable def r1606 : Entry :=
  ⟨⟨[63,71,139,213,358,426,451,665,724,820,824,836,968],[7,11,21,25,38,42,52,56,67,69,70,131,137,138,145,193,212,290,292,296,322,324,386,392,448,532,536,580,648,656,704,772,776,816,832]⟩,
   ⟨1957,517163123745,449215348995⟩⟩
theorem r1606_checked : check r1606 = true := by decide +kernel

-- six_orbit_dags/type4m13e11q2r0.json.gz, graph 741, terminal 17; projection:R_one_six_1810.
noncomputable def r1607 : Entry :=
  ⟨⟨[63,71,75,345,405,440,614,692,709,810,842,928,961],[7,11,21,25,38,42,52,56,67,69,70,73,74,133,148,176,273,280,296,321,328,385,400,416,546,548,578,580,644,672,705,778,800,832,896]⟩,
   ⟨1945,517917192720,517917192720⟩⟩
theorem r1607_checked : check r1607 = true := by decide +kernel

-- six_orbit_dags/type4m13e11q2r0.json.gz, graph 741, terminal 23; projection:R_one_six_1812.
noncomputable def r1608 : Entry :=
  ⟨⟨[63,89,135,203,422,450,597,632,810,820,842,901,961],[7,11,21,25,38,42,52,56,73,74,81,88,131,133,134,193,194,290,292,322,386,388,448,517,532,552,560,577,584,592,772,778,800,832,897]⟩,
   ⟨1947,590394557745,590392660995⟩⟩
theorem r1608_checked : check r1608 = true := by decide +kernel

-- six_orbit_dags/type4m13e11q2r0.json.gz, graph 741, terminal 24; projection:R_one_six_1829.
noncomputable def r1609 : Entry :=
  ⟨⟨[63,71,213,230,409,436,449,554,587,824,841,930,962],[7,11,21,25,38,42,52,56,67,69,70,145,148,162,164,193,194,196,265,280,304,321,385,400,416,448,522,546,552,578,585,776,800,832,898]⟩,
   ⟨1964,654819151905,654818230530⟩⟩
theorem r1609_checked : check r1609 = true := by decide +kernel

-- six_orbit_dags/type4m13e11q2r0.json.gz, graph 741, terminal 25; projection:R_one_six_1827.
noncomputable def r1610 : Entry :=
  ⟨⟨[63,71,341,409,436,449,554,651,696,707,806,838,992],[7,11,21,25,38,42,52,56,67,69,70,137,152,176,193,273,276,292,321,324,385,400,416,448,522,546,552,578,643,648,672,704,774,800,832]⟩,
   ⟨1962,448706843940,448708755765⟩⟩
theorem r1610_checked : check r1610 = true := by decide +kernel

-- six_orbit_dags/type4m13e11q2r0.json.gz, graph 741, terminal 26; projection:R_one_six_1825.
noncomputable def r1611 : Entry :=
  ⟨⟨[63,71,203,230,312,372,426,665,705,789,837,920,992],[7,11,21,25,38,42,52,56,67,69,70,100,137,138,162,193,194,224,276,280,296,304,324,352,392,416,529,577,641,664,704,773,784,832,896]⟩,
   ⟨1960,590393659410,590393659410⟩⟩
theorem r1611_checked : check r1611 = true := by decide +kernel

-- six_orbit_dags/type4m13e11q2r0.json.gz, graph 741, terminal 29; projection:R_one_six_1823.
noncomputable def r1612 : Entry :=
  ⟨⟨[63,71,230,281,331,426,628,696,736,789,837,920,962],[7,11,21,25,38,42,52,56,67,69,70,100,162,168,194,224,265,266,273,280,321,322,386,392,532,560,580,608,664,672,704,773,784,832,896]⟩,
   ⟨1958,654818168850,654818168850⟩⟩
theorem r1612_checked : check r1612 = true := by decide +kernel

-- six_orbit_dags/type4m13e11q2r0.json.gz, graph 741, terminal 31; projection:R_one_six_1824.
noncomputable def r1613 : Entry :=
  ⟨⟨[63,85,248,372,422,480,523,665,682,721,775,837,962],[7,11,21,25,38,42,52,56,69,81,84,112,152,162,168,208,224,262,292,324,352,386,416,448,515,521,522,577,642,648,657,704,770,773,832]⟩,
   ⟨1959,582340329810,521940455460⟩⟩
theorem r1613_checked : check r1613 = true := by decide +kernel

-- six_orbit_dags/type4m13e11q2r0.json.gz, graph 741, terminal 32; projection:R_one_six_1826.
noncomputable def r1614 : Entry :=
  ⟨⟨[63,71,203,341,409,436,449,554,696,714,806,838,992],[7,11,21,25,38,42,52,56,67,69,70,137,152,176,193,202,273,276,292,321,324,385,400,416,448,522,546,552,578,648,672,704,774,800,832]⟩,
   ⟨1961,650792620065,650791698690⟩⟩
theorem r1614_checked : check r1614 = true := by decide +kernel

-- six_orbit_dags/type4m13e11q2r0.json.gz, graph 741, terminal 33; projection:R_one_six_1815.
noncomputable def r1615 : Entry :=
  ⟨⟨[63,75,180,327,405,449,601,618,696,721,806,932,962],[7,11,21,25,38,42,52,56,67,73,74,145,148,164,176,193,261,262,321,322,385,388,448,536,546,552,578,584,593,656,672,704,770,804,896]⟩,
   ⟨1950,581584306515,453237736740⟩⟩
theorem r1615_checked : check r1615 = true := by decide +kernel

-- six_orbit_dags/type4m13e11q2r0.json.gz, graph 741, terminal 34; projection:R_one_six_1814.
noncomputable def r1616 : Entry :=
  ⟨⟨[63,106,149,331,358,391,449,632,665,713,820,916,992],[7,11,21,25,38,42,52,56,73,74,98,104,133,145,148,193,259,262,292,321,322,352,385,388,448,536,560,584,608,649,656,704,788,800,896]⟩,
   ⟨1949,582339527955,521941550355⟩⟩
theorem r1616_checked : check r1616 = true := by decide +kernel

-- six_orbit_dags/type4m13e11q2r0.json.gz, graph 741, terminal 35; projection:R_one_six_1828.
noncomputable def r1617 : Entry :=
  ⟨⟨[63,71,213,409,436,449,554,587,678,710,824,841,992],[7,11,21,25,38,42,52,56,67,69,70,145,148,164,193,196,265,280,304,321,385,400,416,448,522,546,552,578,585,646,672,704,776,800,832]⟩,
   ⟨1963,444681356580,444682223955⟩⟩
theorem r1617_checked : check r1617 = true := by decide +kernel

-- six_orbit_dags/type4m13e11q2r0.json.gz, graph 741, terminal 36; projection:R_one_six_1813.
noncomputable def r1618 : Entry :=
  ⟨⟨[63,71,170,203,341,449,614,696,738,793,820,905,964],[7,11,21,25,38,42,52,56,67,69,70,137,138,162,168,193,194,273,276,321,324,385,448,536,548,560,580,610,648,672,704,772,777,784,896]⟩,
   ⟨1948,590140933395,590140933395⟩⟩
theorem r1618_checked : check r1618 = true := by decide +kernel

-- six_orbit_dags/type4m13e11q2r0.json.gz, graph 741, terminal 42; projection:R_one_six_1816.
noncomputable def r1619 : Entry :=
  ⟨⟨[63,71,213,244,358,440,480,587,705,793,810,913,962],[7,11,21,25,38,42,52,56,67,69,70,100,145,176,193,212,224,280,290,296,322,352,400,416,448,521,522,577,578,641,704,770,776,785,896]⟩,
   ⟨1951,650791637250,650791637025⟩⟩
theorem r1619_checked : check r1619 = true := by decide +kernel

-- six_orbit_dags/type4m13e11q2r0.json.gz, graph 741, terminal 43; projection:R_one_six_1830.
noncomputable def r1620 : Entry :=
  ⟨⟨[63,71,331,409,440,449,597,614,692,721,810,928,962],[7,11,21,25,38,42,52,56,67,69,70,145,176,193,265,266,296,321,322,385,408,416,448,532,546,548,578,580,593,656,672,704,770,800,896]⟩,
   ⟨1965,521942618370,582340595745⟩⟩
theorem r1620_checked : check r1620 = true := by decide +kernel

-- six_orbit_dags/type4m14e11q2r0.json.gz, graph 743, terminal 11; projection:R_one_six_1835.
noncomputable def r1621 : Entry :=
  ⟨⟨[63,85,89,135,331,387,426,472,628,678,696,837,901,976],[7,11,21,25,38,42,52,56,69,73,81,84,88,131,133,134,152,162,168,259,266,321,328,385,386,392,464,548,560,580,592,644,656,672,773,832,896]⟩,
   ⟨1547,582342419265,521944507140⟩⟩
theorem r1621_checked : check r1621 = true := by decide +kernel

-- six_orbit_dags/type4m14e11q2r0.json.gz, graph 743, terminal 92; projection:R_one_six_1841.
noncomputable def r1622 : Entry :=
  ⟨⟨[63,71,89,166,203,337,376,426,692,710,789,837,944,968],[7,11,21,25,38,42,52,56,67,69,70,73,81,88,134,138,162,164,194,200,273,296,304,321,328,336,392,416,532,580,644,688,704,773,784,832,896]⟩,
   ⟨1553,582341428050,521940574275⟩⟩
theorem r1622_checked : check r1622 = true := by decide +kernel

-- six_orbit_dags/type4m14e11q2r0.json.gz, graph 743, terminal 119; projection:R_one_six_1837.
noncomputable def r1623 : Entry :=
  ⟨⟨[63,89,135,213,329,376,395,550,682,710,820,852,936,961],[7,11,21,25,38,42,52,56,73,81,84,88,131,133,134,138,193,196,265,296,304,321,328,336,385,392,518,546,548,580,642,680,704,788,800,832,896]⟩,
   ⟨1549,650793587760,650793587760⟩⟩
theorem r1623_checked : check r1623 = true := by decide +kernel

-- six_orbit_dags/type4m14e11q2r0.json.gz, graph 743, terminal 131; projection:R_one_six_1833.
noncomputable def r1624 : Entry :=
  ⟨⟨[63,71,85,139,170,372,440,601,678,707,838,856,905,932],[7,11,21,25,38,42,52,56,67,69,70,81,84,131,137,138,162,168,280,292,304,324,336,392,416,518,521,577,578,600,641,642,676,772,776,832,896]⟩,
   ⟨1545,582341513265,521942668290⟩⟩
theorem r1624_checked : check r1624 = true := by decide +kernel

-- six_orbit_dags/type4m14e11q2r0.json.gz, graph 743, terminal 182; projection:R_one_six_1834.
noncomputable def r1625 : Entry :=
  ⟨⟨[63,85,116,139,327,387,409,422,632,682,740,849,920,964],[7,11,21,25,38,42,52,56,69,81,84,100,112,131,137,138,162,164,259,262,273,321,324,385,386,388,408,536,552,592,608,648,672,708,784,832,896]⟩,
   ⟨1546,517914771795,517913904420⟩⟩
theorem r1625_checked : check r1625 = true := by decide +kernel

-- six_orbit_dags/type4m14e11q2r0.json.gz, graph 743, terminal 184; projection:R_one_six_1831.
noncomputable def r1626 : Entry :=
  ⟨⟨[63,71,75,197,230,345,449,682,692,789,824,842,901,962],[7,11,21,25,38,42,52,56,67,69,70,73,74,133,162,164,193,194,196,273,280,321,328,385,448,522,532,552,560,642,644,672,773,776,784,834,896]⟩,
   ⟨2,590395748865,590395748865⟩⟩
theorem r1626_checked : check r1626 = true := by decide +kernel

-- six_orbit_dags/type4m14e11q2r0.json.gz, graph 743, terminal 185; projection:R_one_six_1832.
noncomputable def r1627 : Entry :=
  ⟨⟨[63,71,75,213,401,436,454,618,713,793,806,824,897,962],[7,11,21,25,38,42,52,56,67,69,70,73,74,145,148,193,196,262,273,292,304,385,388,400,450,521,546,552,578,584,641,704,769,770,792,800,896]⟩,
   ⟨1544,590395748865,590395748865⟩⟩
theorem r1627_checked : check r1627 = true := by decide +kernel

-- six_orbit_dags/type4m14e11q2r0.json.gz, graph 743, terminal 245; projection:R_one_six_1838.
noncomputable def r1628 : Entry :=
  ⟨⟨[63,71,195,230,312,341,436,601,651,705,810,856,930,964],[7,11,21,25,38,42,52,56,67,69,70,81,131,162,164,193,194,196,276,280,296,304,324,336,388,416,521,522,577,600,641,642,704,776,802,832,896]⟩,
   ⟨1550,590395748865,590395748865⟩⟩
theorem r1628_checked : check r1628 = true := by decide +kernel

-- six_orbit_dags/type4m14e11q2r0.json.gz, graph 743, terminal 257; projection:R_one_six_1836.
noncomputable def r1629 : Entry :=
  ⟨⟨[63,71,180,230,323,362,453,537,632,752,779,789,916,968],[7,11,21,25,38,42,52,56,67,69,70,98,104,148,164,176,196,224,259,261,266,321,322,328,388,448,521,529,536,584,624,656,704,769,776,788,896]⟩,
   ⟨1548,582341702145,521943724545⟩⟩
theorem r1629_checked : check r1629 = true := by decide +kernel

-- six_orbit_dags/type4m14e11q2r0.json.gz, graph 743, terminal 279; projection:R_one_six_1842.
noncomputable def r1630 : Entry :=
  ⟨⟨[63,85,139,325,345,391,454,614,628,682,706,824,905,976],[7,11,21,25,38,42,52,56,69,70,81,84,131,137,138,194,261,265,280,321,324,336,385,390,448,546,552,560,578,592,612,642,648,704,776,784,896]⟩,
   ⟨1554,650793468465,650793652740⟩⟩
theorem r1630_checked : check r1630 = true := by decide +kernel

-- six_orbit_dags/type4m14e11q2r0.json.gz, graph 743, terminal 281; projection:R_one_six_1840.
noncomputable def r1631 : Entry :=
  ⟨⟨[63,75,102,195,277,391,409,454,618,696,713,820,868,976],[7,11,21,25,38,42,52,56,67,70,73,74,98,100,131,137,152,193,194,261,273,276,324,385,390,400,448,552,560,584,608,648,656,704,784,804,832]⟩,
   ⟨1552,654820246305,654820253955⟩⟩
theorem r1631_checked : check r1631 = true := by decide +kernel

-- six_orbit_dags/type4m14e11q2r0.json.gz, graph 743, terminal 282; projection:R_one_six_1843.
noncomputable def r1632 : Entry :=
  ⟨⟨[63,85,139,325,391,409,454,614,628,682,706,824,849,968],[7,11,21,25,38,42,52,56,69,70,81,84,131,137,138,194,261,273,280,321,324,385,390,392,448,546,552,560,578,592,612,642,648,704,776,784,832]⟩,
   ⟨1555,650793648705,650793533955⟩⟩
theorem r1632_checked : check r1632 = true := by decide +kernel

-- six_orbit_dags/type4m14e11q2r0.json.gz, graph 743, terminal 285; projection:R_one_six_1839.
noncomputable def r1633 : Entry :=
  ⟨⟨[63,75,102,195,217,277,391,454,618,696,820,868,913,968],[7,11,21,25,38,42,52,56,67,70,73,74,98,100,131,145,152,193,194,200,261,273,276,324,385,390,448,552,560,584,608,648,656,784,804,832,896]⟩,
   ⟨1551,654820246305,654820253955⟩⟩
theorem r1633_checked : check r1633 = true := by decide +kernel

-- six_orbit_dags/type4m14e11q2r0.json.gz, graph 743, terminal 415; projection:R_one_six_1845.
noncomputable def r1634 : Entry :=
  ⟨⟨[63,85,195,217,244,298,395,583,688,740,806,824,920,962],[7,11,21,25,38,42,52,56,67,69,81,84,131,137,152,176,193,194,208,228,266,290,296,386,392,518,548,560,578,580,656,672,704,770,792,800,896]⟩,
   ⟨1557,521944646145,582342623745⟩⟩
theorem r1634_checked : check r1634 = true := by decide +kernel

-- six_orbit_dags/type4m14e11q2r0.json.gz, graph 743, terminal 417; projection:R_one_six_1844.
noncomputable def r1635 : Entry :=
  ⟨⟨[63,85,298,345,395,422,449,583,628,646,707,824,932,976],[7,11,21,25,38,42,52,56,69,81,84,131,134,193,265,266,280,290,296,321,336,385,386,420,448,518,548,560,579,580,592,642,644,704,784,800,896]⟩,
   ⟨1556,577558811940,452986949940⟩⟩
theorem r1635_checked : check r1635 = true := by decide +kernel

-- six_extra_orbit_dags/full_m12e14q9_types5555.json.gz, graph 854, terminal 4; integer:four_prism.
noncomputable def r1636 : Entry :=
  ⟨⟨[63,109,118,201,338,411,709,744,838,880,903,952],[7,27,45,54,56,69,70,73,82,100,104,112,137,193,200,274,322,336,387,408,580,608,645,680,704,774,816,832,896]⟩,
   ⟨1992,516307391520,243040153920⟩⟩
theorem r1636_checked : check r1636 = true := by decide +kernel

-- six_extra_orbit_dags/full_m12e14q9_types5555.json.gz, graph 854, terminal 6; integer:four_prism.
noncomputable def r1637 : Entry :=
  ⟨⟨[63,71,120,411,451,472,694,710,752,813,837,872],[7,27,45,54,56,67,69,70,88,104,112,146,194,208,265,321,328,387,408,448,548,580,608,646,688,704,773,808,832]⟩,
   ⟨1992,503688763425,217273815300⟩⟩
theorem r1637_checked : check r1637 = true := by decide +kernel

-- six_extra_orbit_dags/full_m13e11q3_types5.json.gz, graph 857, terminal 2; projection:R_prism_completion_next_oneprism_m13e11q3_models_0005.
noncomputable def r1638 : Entry :=
  ⟨⟨[63,71,91,201,310,338,454,472,557,709,824,905,932],[7,27,45,54,56,67,69,70,73,82,88,137,193,196,200,262,274,280,292,304,322,336,388,392,448,517,521,548,552,641,644,776,800,896]⟩,
   ⟨1969,519829542450,577978568775⟩⟩
theorem r1638_checked : check r1638 = true := by decide +kernel

-- six_extra_orbit_dags/full_m13e11q3_types5.json.gz, graph 857, terminal 3; projection:R_prism_completion_next_oneprism_m13e11q3_models_0009.
noncomputable def r1639 : Entry :=
  ⟨⟨[63,91,195,210,301,329,453,472,566,647,824,914,932],[7,27,45,54,56,67,73,82,88,131,133,146,193,194,208,261,265,280,292,296,321,328,388,400,448,518,530,548,560,642,644,784,800,896]⟩,
   ⟨1972,521440399395,578063499570⟩⟩
theorem r1639_checked : check r1639 = true := by decide +kernel

-- six_extra_orbit_dags/full_m13e11q3_types5.json.gz, graph 857, terminal 5; projection:R_prism_completion_next_oneprism_m13e11q3_models_0011.
noncomputable def r1640 : Entry :=
  ⟨⟨[63,182,301,391,450,484,539,696,722,736,777,835,872],[7,27,45,54,56,134,146,164,176,194,224,259,261,265,292,296,322,352,386,388,448,515,521,530,536,552,578,608,656,672,704,769,776,832]⟩,
   ⟨1974,581436609345,247083377670⟩⟩
theorem r1640_checked : check r1640 = true := by decide +kernel

-- six_extra_orbit_dags/full_m13e11q3_types5.json.gz, graph 857, terminal 6; projection:R_prism_completion_next_oneprism_m13e11q3_models_0004.
noncomputable def r1641 : Entry :=
  ⟨⟨[63,91,195,310,376,391,466,480,557,585,709,744,932],[7,27,45,54,56,67,73,82,88,104,131,133,193,194,224,262,274,292,304,336,352,386,388,416,448,517,521,548,552,577,584,644,672,704]⟩,
   ⟨1968,637673869410,646146703410⟩⟩
theorem r1641_checked : check r1641 = true := by decide +kernel

-- six_extra_orbit_dags/full_m13e11q3_types5.json.gz, graph 857, terminal 7; projection:R_prism_completion_next_oneprism_m13e11q3_models_0010.
noncomputable def r1642 : Entry :=
  ⟨⟨[63,155,195,301,393,453,472,566,583,722,824,848,868],[7,27,45,54,56,67,69,131,137,146,152,193,194,208,261,265,280,292,296,324,336,385,392,448,518,530,548,560,578,580,592,784,800,832]⟩,
   ⟨1973,315549356130,577426247730⟩⟩
theorem r1642_checked : check r1642 = true := by decide +kernel

-- six_extra_orbit_dags/full_m13e11q3_types5.json.gz, graph 857, terminal 8; projection:R_prism_completion_next_oneprism_m13e11q3_models_0002.
noncomputable def r1643 : Entry :=
  ⟨⟨[63,91,216,310,323,440,466,557,585,744,775,932,961],[7,27,45,54,56,67,73,82,88,152,168,200,208,259,262,274,292,304,321,322,400,416,448,517,521,548,552,577,584,672,704,769,772,896]⟩,
   ⟨1967,589870539795,590095713045⟩⟩
theorem r1643_checked : check r1643 = true := by decide +kernel

-- six_extra_orbit_dags/full_m13e11q3_types5.json.gz, graph 857, terminal 9; projection:R_prism_completion_next_oneprism_m13e11q3_models_0001.
noncomputable def r1644 : Entry :=
  ⟨⟨[63,109,155,201,360,472,566,583,643,824,868,914,961],[7,27,45,54,56,69,73,100,104,131,137,146,152,193,200,280,296,328,352,400,448,515,518,530,548,560,577,580,641,642,784,800,832,896]⟩,
   ⟨1966,573770310675,521394062100⟩⟩
theorem r1644_checked : check r1644 = true := by decide +kernel

-- six_extra_orbit_dags/full_m13e11q3_types5.json.gz, graph 857, terminal 10; projection:R_prism_completion_next_oneprism_m13e11q3_models_0006.
noncomputable def r1645 : Entry :=
  ⟨⟨[63,91,195,216,301,329,453,488,566,647,696,722,932],[7,27,45,54,56,67,73,82,88,131,133,152,168,193,194,200,208,261,265,292,296,321,328,388,416,448,518,530,548,560,642,644,656,672]⟩,
   ⟨1970,100986687570,238439194770⟩⟩
theorem r1645_checked : check r1645 = true := by decide +kernel

-- six_extra_orbit_dags/full_m13e11q3_types5.json.gz, graph 857, terminal 11; projection:R_prism_completion_next_oneprism_m13e11q3_models_0007.
noncomputable def r1646 : Entry :=
  ⟨⟨[63,91,173,201,323,424,453,472,566,775,824,850,932],[7,27,45,54,56,67,73,82,88,133,137,164,168,193,200,259,261,280,296,321,322,336,388,392,416,448,518,530,548,560,770,772,784,800]⟩,
   ⟨1971,36344926785,242503205385⟩⟩
theorem r1646_checked : check r1646 = true := by decide +kernel

-- six_extra_orbit_dags/full_m13e12q1_types66.json.gz, graph 858, terminal 0; projection:R_prism_smaller_next_pentpair_m13e12k2l1p0q1_models_0000.
noncomputable def r1647 : Entry :=
  ⟨⟨[63,71,101,187,372,387,481,590,668,835,852,906,944],[7,14,28,37,52,59,67,69,70,97,100,131,138,152,161,176,259,304,321,340,352,385,386,416,522,524,532,578,580,648,656,770,784,832,896]⟩,
   ⟨1982,646413747570,648945156195⟩⟩
theorem r1647_checked : check r1647 = true := by decide +kernel

-- six_extra_orbit_dags/full_m13e12q1_types66.json.gz, graph 858, terminal 1; projection:R_prism_smaller_next_pentpair_m13e12k2l1p0q1_models_0000.
noncomputable def r1648 : Entry :=
  ⟨⟨[63,187,195,225,263,357,496,668,714,782,820,835,976],[7,14,28,37,52,59,67,97,131,138,152,161,176,193,194,224,259,261,262,292,304,321,352,464,522,524,532,578,648,656,704,770,772,784,832]⟩,
   ⟨1982,645608441970,627475562595⟩⟩
theorem r1648_checked : check r1648 = true := by decide +kernel

-- six_extra_orbit_dags/full_m13e13q7_types555.json.gz, graph 865, terminal 21; projection:R_prism_smaller_next_many_prism_m13e13k3q7_models_0000.
noncomputable def r1649 : Entry :=
  ⟨⟨[63,109,118,201,338,411,519,709,744,838,880,899,952],[7,27,45,54,56,69,70,73,82,100,104,112,137,193,200,274,322,336,387,408,515,517,518,580,608,641,680,704,770,816,832,896]⟩,
   ⟨1981,494058148965,303080572215⟩⟩
theorem r1649_checked : check r1649 = true := by decide +kernel

-- six_extra_orbit_dags/full_m13e13q7_types555.json.gz, graph 865, terminal 24; projection:R_prism_smaller_next_many_prism_m13e13k3q7_models_0000.
noncomputable def r1650 : Entry :=
  ⟨⟨[63,109,118,201,338,391,411,709,744,838,880,900,952],[7,27,45,54,56,69,70,73,82,100,104,112,133,137,193,200,262,274,322,336,387,388,408,580,608,644,680,704,772,816,832,896]⟩,
   ⟨1981,302126798640,301326734640⟩⟩
theorem r1650_checked : check r1650 = true := by decide +kernel

-- six_extra_orbit_dags/full_m13e13q7_types555.json.gz, graph 865, terminal 35; projection:R_prism_smaller_next_many_prism_m13e13k3q7_models_0000.
noncomputable def r1651 : Entry :=
  ⟨⟨[63,71,120,283,393,451,472,685,709,744,822,838,880],[7,27,45,54,56,67,69,70,88,104,112,137,193,200,259,265,274,280,322,336,385,392,448,548,580,608,645,680,704,774,816,832]⟩,
   ⟨1981,168721342725,371565480225⟩⟩
theorem r1651_checked : check r1651 = true := by decide +kernel

-- six_extra_orbit_dags/full_m14e11q3_types5.json.gz, graph 867, terminal 7; projection:R_prism_completion_next_oneprism_m14e11q3_models_0002.
noncomputable def r1652 : Entry :=
  ⟨⟨[63,91,201,301,327,449,452,566,594,710,728,824,905,932],[7,27,45,54,56,67,70,73,82,88,137,193,196,200,261,265,292,296,321,324,385,388,448,518,530,536,548,560,578,592,644,648,704,776,800,896]⟩,
   ⟨1977,579975861795,453156077895⟩⟩
theorem r1652_checked : check r1652 = true := by decide +kernel

-- six_extra_orbit_dags/full_m14e11q3_types5.json.gz, graph 867, terminal 8; projection:R_prism_completion_next_oneprism_m14e11q3_models_0005.
noncomputable def r1653 : Entry :=
  ⟨⟨[63,135,182,197,283,338,451,557,696,722,740,777,837,856],[7,27,45,54,56,69,82,131,133,134,146,164,176,193,194,196,259,265,274,280,321,322,336,517,521,536,548,552,580,592,656,672,704,769,776,832]⟩,
   ⟨1980,646262559285,646258692660⟩⟩
theorem r1653_checked : check r1653 = true := by decide +kernel

-- six_extra_orbit_dags/full_m14e11q3_types5.json.gz, graph 867, terminal 122; projection:R_prism_completion_next_oneprism_m14e11q3_models_0004.
noncomputable def r1654 : Entry :=
  ⟨⟨[63,155,182,195,201,432,454,472,557,583,824,836,841,932],[7,27,45,54,56,67,70,73,131,134,137,146,152,164,176,193,194,200,280,304,324,328,388,400,416,448,517,521,548,552,577,580,772,776,800,832]⟩,
   ⟨1979,32621282595,509039804745⟩⟩
theorem r1654_checked : check r1654 = true := by decide +kernel

-- six_extra_orbit_dags/full_m14e11q3_types5.json.gz, graph 867, terminal 123; projection:R_prism_completion_next_oneprism_m14e11q3_models_0001.
noncomputable def r1655 : Entry :=
  ⟨⟨[63,91,118,195,201,356,368,454,472,557,647,824,905,932],[7,27,45,54,56,67,70,73,82,88,100,112,131,134,137,193,194,200,280,292,304,324,336,352,388,392,448,517,521,548,552,641,644,776,800,896]⟩,
   ⟨1976,508285239315,303205385490⟩⟩
theorem r1655_checked : check r1655 = true := by decide +kernel

-- six_extra_orbit_dags/full_m14e11q3_types5.json.gz, graph 867, terminal 124; projection:R_prism_completion_next_oneprism_m14e11q3_models_0000.
noncomputable def r1656 : Entry :=
  ⟨⟨[63,91,109,195,210,360,472,566,581,647,824,868,914,961],[7,27,45,54,56,67,69,73,82,88,100,104,131,146,193,194,208,280,296,328,352,400,448,517,518,530,548,560,577,580,641,642,784,800,832,896]⟩,
   ⟨1975,551792480835,452938760760⟩⟩
theorem r1656_checked : check r1656 = true := by decide +kernel

-- six_extra_orbit_dags/full_m14e11q3_types5.json.gz, graph 867, terminal 129; projection:R_prism_completion_next_oneprism_m14e11q3_models_0003.
noncomputable def r1657 : Entry :=
  ⟨⟨[63,155,182,195,201,323,432,454,472,557,775,824,841,932],[7,27,45,54,56,67,73,131,134,137,146,152,164,176,193,194,200,259,262,280,304,321,322,328,388,400,416,448,517,521,548,552,769,772,776,800]⟩,
   ⟨1978,40859952165,581213249865⟩⟩
theorem r1657_checked : check r1657 = true := by decide +kernel

-- six_extra_orbit_dags/full_m14e12q5_types55.json.gz, graph 869, terminal 123; gp:C007.
noncomputable def r1658 : Entry :=
  ⟨⟨[63,91,135,184,338,451,472,557,585,709,744,822,902,944],[7,27,45,54,56,67,73,82,88,131,133,134,152,168,176,193,200,274,322,336,386,400,448,517,521,548,552,577,584,644,672,704,774,816,896]⟩,
   ⟨2002,418886406180,375426924930⟩⟩
theorem r1658_checked : check r1658 = true := by decide +kernel

-- six_extra_orbit_dags/full_m14e12q5_types55.json.gz, graph 869, terminal 140; integer:two_prism_0.
noncomputable def r1659 : Entry :=
  ⟨⟨[63,135,184,283,329,451,472,557,585,709,744,822,902,944],[7,27,45,54,56,73,131,133,134,152,168,176,193,200,259,265,274,280,321,328,386,400,448,517,521,548,552,577,584,644,672,704,774,816,896]⟩,
   ⟨1993,435722291460,152362312785⟩⟩
theorem r1659_checked : check r1659 = true := by decide +kernel

-- six_extra_orbit_dags/full_m14e12q5_types55.json.gz, graph 869, terminal 161; integer:two_prism_0.
noncomputable def r1660 : Entry :=
  ⟨⟨[63,199,219,248,452,480,557,566,585,658,837,872,902,944],[7,27,45,54,56,69,73,104,134,146,176,195,196,216,224,324,352,388,416,448,517,518,521,530,548,552,560,577,584,642,656,772,800,832,896]⟩,
   ⟨1993,496142226720,238725529920⟩⟩
theorem r1660_checked : check r1660 = true := by decide +kernel

-- six_extra_orbit_dags/full_m14e12q5_types55.json.gz, graph 869, terminal 162; gp:C007.
noncomputable def r1661 : Entry :=
  ⟨⟨[63,71,411,440,451,480,557,566,649,709,744,786,838,880],[7,27,45,54,56,67,69,70,137,168,193,224,274,304,322,352,387,408,416,448,517,518,521,530,548,552,560,580,608,641,648,704,770,784,832]⟩,
   ⟨2002,572428714290,315235962915⟩⟩
theorem r1661_checked : check r1661 = true := by decide +kernel

-- six_extra_orbit_dags/full_m14e12q5_types55.json.gz, graph 869, terminal 167; integer:two_prism_2.
noncomputable def r1662 : Entry :=
  ⟨⟨[63,71,120,173,182,393,453,488,658,710,752,795,835,856],[7,27,45,54,56,67,69,70,88,104,112,133,134,137,146,164,168,176,196,224,265,321,328,385,392,448,530,578,592,642,656,704,771,792,832]⟩,
   ⟨1994,551745302850,384236073000⟩⟩
theorem r1662_checked : check r1662 = true := by decide +kernel

-- six_extra_orbit_dags/full_m15e11q3_types5.json.gz, graph 870, terminal 80; projection:R_new_prism_0080.
noncomputable def r1663 : Entry :=
  ⟨⟨[63,155,201,310,356,402,454,472,557,647,705,740,824,841,864],[7,27,45,54,56,73,100,131,134,137,146,152,193,196,200,262,274,280,292,304,324,328,352,386,400,448,517,521,548,552,577,608,641,644,704,776,800,832]⟩,
   ⟨1570,654820257825,654820258050⟩⟩
theorem r1663_checked : check r1663 = true := by decide +kernel

#print axioms r1600_checked

end Nonrational.OldTerminalMatches.M025
