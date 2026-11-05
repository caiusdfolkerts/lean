module
prelude
public import InducedTerminalMatches.Basic

@[expose] public section

/-! Exact full-boundary matches, batch 23. Both facet and polygon
families are checked in both directions after the recorded permutation. -/

namespace Nonrational.OldTerminalMatches.M023
open Nonrational.InducedTerminalMatches
set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 20; projection:R_one_six_1702.
noncomputable def r1472 : Entry :=
  ⟨⟨[63,135,197,285,325,372,395,614,632,682,710,848,920,961],[7,11,29,38,42,52,56,69,100,112,131,133,134,138,193,196,261,265,276,280,321,324,336,385,392,536,546,552,582,592,608,642,648,704,784,832,896]⟩,
   ⟨1844,646515524385,650290405635⟩⟩
theorem r1472_checked : check r1472 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 22; projection:R_one_six_1698.
noncomputable def r1473 : Entry :=
  ⟨⟨[63,71,116,197,285,389,395,468,614,682,707,824,880,968],[7,11,29,38,42,52,56,67,69,70,84,100,112,131,133,138,193,196,261,265,276,280,336,385,388,392,448,546,552,578,608,642,648,704,776,816,832]⟩,
   ⟨1840,646263878145,646263878145⟩⟩
theorem r1473_checked : check r1473 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 23; projection:R_one_six_1697.
noncomputable def r1474 : Entry :=
  ⟨⟨[63,71,197,285,372,389,395,452,614,632,682,707,920,976],[7,11,29,38,42,52,56,67,69,70,100,112,131,133,138,193,196,261,265,276,280,324,336,385,388,392,448,536,546,552,578,592,608,642,648,704,912]⟩,
   ⟨1839,646263878145,646263878145⟩⟩
theorem r1474_checked : check r1474 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 26; projection:R_one_six_1699.
noncomputable def r1475 : Entry :=
  ⟨⟨[63,71,197,285,389,395,468,614,628,682,707,824,848,968],[7,11,29,38,42,52,56,67,69,70,84,131,133,138,193,196,261,265,276,280,336,385,388,392,448,546,552,560,578,592,612,642,648,704,776,784,832]⟩,
   ⟨1841,646263866145,646263873795⟩⟩
theorem r1475_checked : check r1475 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 38; projection:R_one_six_1769.
noncomputable def r1476 : Entry :=
  ⟨⟨[63,71,195,197,234,358,376,452,541,651,728,820,901,976],[7,11,29,38,42,52,56,67,69,70,88,98,104,131,133,138,193,194,196,200,292,304,324,336,352,388,448,517,521,532,536,641,648,720,772,784,896]⟩,
   ⟨1909,448712147745,448712155395⟩⟩
theorem r1476_checked : check r1476 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 39; projection:R_one_six_1791.
noncomputable def r1477 : Entry :=
  ⟨⟨[63,71,102,116,197,362,451,496,541,696,724,779,901,936],[7,11,29,38,42,52,56,67,69,70,84,98,100,112,133,176,193,196,208,259,266,296,322,352,385,416,448,517,521,532,536,644,656,680,769,776,896]⟩,
   ⟨1928,444685624080,444685624080⟩⟩
theorem r1477_checked : check r1477 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 44; projection:R_one_six_1792.
noncomputable def r1478 : Entry :=
  ⟨⟨[63,71,102,197,228,248,362,451,541,692,779,856,901,976],[7,11,29,38,42,52,56,67,69,70,88,98,100,104,133,164,176,193,196,208,224,259,266,322,328,385,448,517,521,532,536,644,656,769,776,848,896]⟩,
   ⟨1929,444685624080,444685624080⟩⟩
theorem r1478_checked : check r1478 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 46; projection:R_one_six_1781.
noncomputable def r1479 : Entry :=
  ⟨⟨[63,71,197,230,248,323,362,449,541,692,779,856,901,976],[7,11,29,38,42,52,56,67,69,70,88,98,104,133,164,176,193,196,208,224,259,266,321,322,328,385,448,517,521,532,536,644,656,769,776,848,896]⟩,
   ⟨1918,444685615905,444685623555⟩⟩
theorem r1479_checked : check r1479 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 68; projection:R_one_six_1790.
noncomputable def r1480 : Entry :=
  ⟨⟨[63,71,120,197,198,234,422,496,541,587,820,856,901,961],[7,11,29,38,42,52,56,67,69,70,74,88,104,112,133,134,162,193,194,196,224,292,304,336,388,416,448,517,521,532,536,577,584,772,784,832,897]⟩,
   ⟨1927,444932829780,509105680980⟩⟩
theorem r1480_checked : check r1480 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 69; projection:R_one_six_1776.
noncomputable def r1481 : Entry :=
  ⟨⟨[63,71,197,198,234,422,440,456,541,587,820,856,901,961],[7,11,29,38,42,52,56,67,69,70,74,133,134,162,168,193,194,196,200,280,292,304,328,388,392,416,448,517,521,532,536,577,584,772,784,832,897]⟩,
   ⟨1914,444932829780,509105680980⟩⟩
theorem r1481_checked : check r1481 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 72; projection:R_one_six_1772.
noncomputable def r1482 : Entry :=
  ⟨⟨[63,106,135,197,230,356,376,458,541,651,820,837,920,961],[7,11,29,38,42,52,56,69,74,98,100,104,131,133,134,138,193,194,196,280,292,304,324,328,352,392,448,517,521,532,536,641,648,772,784,833,896]⟩,
   ⟨1911,444682273620,444681168195⟩⟩
theorem r1482_checked : check r1482 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 89; projection:R_one_six_1696.
noncomputable def r1483 : Entry :=
  ⟨⟨[63,75,106,135,248,285,389,457,614,707,752,820,902,920],[7,11,29,38,42,52,56,67,73,74,98,104,131,133,134,152,193,200,240,261,265,276,280,385,388,392,518,548,560,578,608,642,656,704,772,784,896]⟩,
   ⟨1838,646263877665,646263877890⟩⟩
theorem r1483_checked : check r1483 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 560; projection:R_one_six_1684.
noncomputable def r1484 : Entry :=
  ⟨⟨[63,75,93,180,263,362,422,581,696,724,835,856,901,936],[7,11,29,38,42,52,56,67,69,73,74,84,88,148,164,176,259,261,262,290,296,322,328,388,416,517,536,577,580,592,644,656,680,769,776,832,896]⟩,
   ⟨1826,517918163745,517918171395⟩⟩
theorem r1484_checked : check r1484 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 561; projection:R_one_six_1683.
noncomputable def r1485 : Entry :=
  ⟨⟨[63,75,93,197,212,263,362,451,692,728,806,824,901,968],[7,11,29,38,42,52,56,67,69,73,74,84,88,133,148,193,196,208,259,261,262,290,296,322,328,385,448,536,548,560,644,656,712,772,776,800,896]⟩,
   ⟨1825,654820246305,654820253955⟩⟩
theorem r1485_checked : check r1485 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 562; projection:R_one_six_1687.
noncomputable def r1486 : Entry :=
  ⟨⟨[63,75,93,135,166,325,426,451,632,692,842,852,901,936],[7,11,29,38,42,52,56,67,69,73,74,84,88,131,133,134,162,164,261,266,321,322,324,385,386,424,532,552,560,584,592,644,672,772,776,832,896]⟩,
   ⟨1829,654820246305,654820253955⟩⟩
theorem r1486_checked : check r1486 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 565; projection:R_one_six_1729.
noncomputable def r1487 : Entry :=
  ⟨⟨[63,135,166,203,285,325,329,362,692,709,824,852,930,962],[7,11,29,38,42,52,56,69,73,74,131,133,134,162,164,193,194,261,265,276,280,290,296,321,322,324,328,532,560,580,644,672,704,784,800,832,898]⟩,
   ⟨1870,646515524385,650290405635⟩⟩
theorem r1487_checked : check r1487 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 568; projection:R_one_six_1741.
noncomputable def r1488 : Entry :=
  ⟨⟨[63,71,285,331,389,436,449,582,618,678,696,709,856,976],[7,11,29,38,42,52,56,67,69,70,74,133,164,176,193,261,265,276,280,321,328,385,388,400,448,518,536,546,552,578,580,584,644,656,672,704,848]⟩,
   ⟨1882,577561178145,452990349570⟩⟩
theorem r1488_checked : check r1488 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 576; projection:R_one_six_1743.
noncomputable def r1489 : Entry :=
  ⟨⟨[63,135,195,234,308,422,453,541,581,587,696,852,944,968],[7,11,29,38,42,52,56,67,69,74,131,133,134,162,168,193,194,200,276,292,304,324,388,416,448,517,521,532,536,577,580,584,648,688,784,832,896]⟩,
   ⟨1884,449215475745,517163200770⟩⟩
theorem r1489_checked : check r1489 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 577; projection:R_one_six_1742.
noncomputable def r1490 : Entry :=
  ⟨⟨[63,157,197,203,263,323,362,472,692,708,806,824,837,976],[7,11,29,38,42,52,56,67,69,74,133,137,148,152,193,196,200,259,261,262,280,290,296,321,322,328,464,548,560,580,644,656,704,772,784,800,832]⟩,
   ⟨1883,590144090145,590144090370⟩⟩
theorem r1490_checked : check r1490 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 579; projection:R_one_six_1744.
noncomputable def r1491 : Entry :=
  ⟨⟨[63,285,325,372,395,449,519,614,632,643,682,709,920,976],[7,11,29,38,42,52,56,69,100,112,131,138,193,261,265,276,280,321,324,336,385,392,448,515,517,518,536,546,552,580,592,608,641,642,648,704,912]⟩,
   ⟨1885,646515535905,650290409730⟩⟩
theorem r1491_checked : check r1491 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 620; projection:R_one_six_1745.
noncomputable def r1492 : Entry :=
  ⟨⟨[63,71,285,331,389,436,582,618,678,696,709,856,912,961],[7,11,29,38,42,52,56,67,69,70,74,133,164,176,261,265,276,280,321,328,385,388,400,518,536,546,552,578,580,584,644,656,672,705,784,832,896]⟩,
   ⟨1886,577561166625,452990345475⟩⟩
theorem r1492_checked : check r1492 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 643; projection:R_one_six_1690.
noncomputable def r1493 : Entry :=
  ⟨⟨[63,71,93,180,198,267,422,451,632,713,724,810,905,944],[7,11,29,38,42,52,56,67,69,70,73,84,88,134,148,164,176,193,194,196,259,265,266,290,385,386,416,552,560,584,592,649,656,704,776,800,896]⟩,
   ⟨1832,650793726465,650793726465⟩⟩
theorem r1493_checked : check r1493 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 644; projection:R_one_six_1691.
noncomputable def r1494 : Entry :=
  ⟨⟨[63,75,230,263,285,390,451,618,628,708,713,824,905,916],[7,11,29,38,42,52,56,67,73,74,98,100,134,193,194,196,259,261,262,265,276,280,385,386,388,532,552,560,580,584,608,644,649,704,776,784,896]⟩,
   ⟨1833,646515536385,650290409985⟩⟩
theorem r1494_checked : check r1494 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 669; projection:R_one_six_1757.
noncomputable def r1495 : Entry :=
  ⟨⟨[63,71,234,358,440,453,480,541,587,705,728,820,901,912],[7,11,29,38,42,52,56,67,69,70,74,98,152,168,193,200,224,292,304,324,352,389,400,416,448,517,521,532,536,577,584,641,656,704,772,784,896]⟩,
   ⟨1897,444681171540,444681171540⟩⟩
theorem r1495_checked : check r1495 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 670; projection:R_one_six_1768.
noncomputable def r1496 : Entry :=
  ⟨⟨[63,75,180,230,285,327,449,452,618,713,752,824,905,916],[7,11,29,38,42,52,56,67,70,73,74,98,148,164,176,193,196,224,261,265,276,280,321,324,385,388,448,552,560,584,608,649,656,704,776,784,896]⟩,
   ⟨1908,646515536385,650290409985⟩⟩
theorem r1496_checked : check r1496 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 671; projection:R_one_six_1749.
noncomputable def r1497 : Entry :=
  ⟨⟨[63,75,285,327,449,468,550,618,692,710,713,824,905,912],[7,11,29,38,42,52,56,67,70,73,74,148,193,196,261,265,276,280,321,324,385,400,448,518,546,548,552,560,578,584,644,649,656,704,776,784,896]⟩,
   ⟨1889,509105677140,444932825940⟩⟩
theorem r1497_checked : check r1497 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 685; projection:R_one_six_1710.
noncomputable def r1498 : Entry :=
  ⟨⟨[63,120,197,230,240,285,389,436,583,618,728,779,920,961],[7,11,29,38,42,52,56,69,70,88,98,104,112,133,164,176,193,196,208,224,261,265,276,280,385,388,400,515,522,577,578,584,664,704,769,776,896]⟩,
   ⟨1851,646263878160,646263878160⟩⟩
theorem r1498_checked : check r1498 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 686; projection:R_one_six_1734.
noncomputable def r1499 : Entry :=
  ⟨⟨[63,75,195,230,285,340,391,452,618,628,713,824,905,976],[7,11,29,38,42,52,56,67,73,74,84,98,100,131,134,193,194,196,261,265,276,280,324,336,385,388,448,552,560,584,592,608,649,704,776,784,896]⟩,
   ⟨1875,578060038740,521436934740⟩⟩
theorem r1499_checked : check r1499 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 687; projection:R_one_six_1755.
noncomputable def r1500 : Entry :=
  ⟨⟨[63,71,195,234,358,376,453,541,651,728,820,848,901,960],[7,11,29,38,42,52,56,67,69,70,88,98,104,131,138,193,194,200,292,304,324,336,352,389,448,517,521,532,536,592,641,648,704,772,784,832,896]⟩,
   ⟨1895,444932829780,509105680980⟩⟩
theorem r1500_checked : check r1500 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 688; projection:R_one_six_1767.
noncomputable def r1501 : Entry :=
  ⟨⟨[63,116,234,240,331,358,449,468,541,696,713,775,897,916],[7,11,29,38,42,52,56,73,74,84,98,100,112,168,176,193,200,208,224,259,262,321,322,324,385,404,448,517,521,532,536,641,648,656,769,772,896]⟩,
   ⟨1907,444685627920,444685627920⟩⟩
theorem r1501_checked : check r1501 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 766; projection:R_one_six_1719.
noncomputable def r1502 : Entry :=
  ⟨⟨[63,75,166,234,327,390,436,541,581,713,824,852,936,962],[7,11,29,38,42,52,56,67,69,73,74,134,162,164,168,194,200,262,276,304,322,324,386,388,416,517,521,532,536,577,580,648,704,784,808,832,896]⟩,
   ⟨1860,449215464225,517163196675⟩⟩
theorem r1502_checked : check r1502 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 784; projection:R_one_six_1695.
noncomputable def r1503 : Entry :=
  ⟨⟨[63,93,116,135,201,312,395,472,614,709,752,810,902,944],[7,11,29,38,42,52,56,69,73,84,88,100,112,131,133,134,137,193,200,208,266,280,296,304,386,392,400,518,546,580,608,644,688,704,770,800,896]⟩,
   ⟨1837,521941364820,582338229570⟩⟩
theorem r1503_checked : check r1503 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 785; projection:R_one_six_1693.
noncomputable def r1504 : Entry :=
  ⟨⟨[63,71,157,180,201,216,331,376,678,709,810,838,944,976],[7,11,29,38,42,52,56,67,69,70,73,88,133,137,148,152,164,176,193,200,208,266,296,304,322,328,336,518,546,580,644,672,704,770,800,832,912]⟩,
   ⟨1835,517159858260,449211020610⟩⟩
theorem r1504_checked : check r1504 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 786; projection:R_one_six_1686.
noncomputable def r1505 : Entry :=
  ⟨⟨[63,71,157,180,201,331,472,678,709,752,810,824,838,848],[7,11,29,38,42,52,56,67,69,70,73,133,137,148,152,164,176,193,200,208,266,280,322,328,336,518,546,560,580,592,644,672,704,770,784,808,832]⟩,
   ⟨1828,590140736340,590139630915⟩⟩
theorem r1505_checked : check r1505 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 807; projection:R_one_six_1780.
noncomputable def r1506 : Entry :=
  ⟨⟨[63,102,116,199,226,376,387,426,541,724,779,856,901,992],[7,11,29,38,42,52,56,70,84,98,100,112,131,133,162,194,196,224,259,266,296,344,352,385,386,416,517,521,532,536,592,644,704,769,776,832,896]⟩,
   ⟨1917,444685624080,444685624080⟩⟩
theorem r1506_checked : check r1506 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 930; projection:R_one_six_1731.
noncomputable def r1507 : Entry :=
  ⟨⟨[63,106,116,230,331,360,391,541,645,724,824,880,905,962],[7,11,29,38,42,52,56,74,84,98,100,104,112,133,134,194,196,259,265,296,322,328,352,385,386,517,521,532,536,592,641,644,704,776,816,832,896]⟩,
   ⟨1872,448712159745,448712159745⟩⟩
theorem r1507_checked : check r1507 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 931; projection:R_one_six_1738.
noncomputable def r1508 : Entry :=
  ⟨⟨[63,106,116,230,360,391,458,541,645,724,779,824,880,961],[7,11,29,38,42,52,56,74,84,98,100,104,112,133,134,194,196,259,266,296,328,352,385,386,448,517,521,532,536,592,641,644,704,769,776,816,832]⟩,
   ⟨1879,448712159760,448712159760⟩⟩
theorem r1508_checked : check r1508 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 963; projection:R_one_six_1736.
noncomputable def r1509 : Entry :=
  ⟨⟨[63,106,180,230,327,330,488,541,581,724,779,824,944,961],[7,11,29,38,42,52,56,69,70,74,98,104,148,164,176,196,224,259,266,296,321,322,328,416,448,517,521,532,536,577,580,656,704,769,776,816,896]⟩,
   ⟨1877,449215476240,517163201040⟩⟩
theorem r1509_checked : check r1509 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 990; projection:R_one_six_1764.
noncomputable def r1510 : Entry :=
  ⟨⟨[63,102,180,267,362,451,484,541,583,705,724,824,905,944],[7,11,29,38,42,52,56,67,70,98,100,148,164,176,193,196,259,265,266,296,322,352,385,416,448,517,521,532,536,577,580,641,656,704,776,816,896]⟩,
   ⟨1904,453242007585,581587710210⟩⟩
theorem r1510_checked : check r1510 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 994; projection:R_one_six_1752.
noncomputable def r1511 : Entry :=
  ⟨⟨[63,102,180,203,362,456,484,541,583,705,724,824,905,944],[7,11,29,38,42,52,56,67,70,74,98,100,137,148,164,176,193,196,200,296,328,352,392,416,448,517,521,532,536,577,580,641,656,704,776,816,896]⟩,
   ⟨1892,453242007585,581587710210⟩⟩
theorem r1511_checked : check r1511 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 1470; projection:R_one_six_1782.
noncomputable def r1512 : Entry :=
  ⟨⟨[63,71,195,230,248,387,426,449,541,628,779,837,920,976],[7,11,29,38,42,52,56,67,69,70,100,112,131,152,162,168,193,194,208,224,259,266,321,385,386,392,448,517,521,532,536,580,592,769,776,832,912]⟩,
   ⟨1919,444937274145,509110132995⟩⟩
theorem r1512_checked : check r1512 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 1592; projection:R_one_six_1717.
noncomputable def r1513 : Entry :=
  ⟨⟨[63,102,226,244,267,327,426,541,660,709,824,841,944,962],[7,11,29,38,42,52,56,69,70,98,100,148,162,176,194,196,224,259,265,266,296,321,322,386,416,517,521,532,536,577,644,656,704,776,816,832,896]⟩,
   ⟨1858,452987007060,577556723010⟩⟩
theorem r1513_checked : check r1513 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 1661; projection:R_one_six_1677.
noncomputable def r1514 : Entry :=
  ⟨⟨[63,71,93,166,267,376,426,579,692,710,841,852,899,944],[7,11,29,38,42,52,56,67,69,70,73,84,88,134,162,164,259,265,266,296,304,328,336,386,416,515,532,577,578,580,642,644,688,769,784,832,896]⟩,
   ⟨1819,517918163745,517918171395⟩⟩
theorem r1514_checked : check r1514 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 1662; projection:R_one_six_1676.
noncomputable def r1515 : Entry :=
  ⟨⟨[63,71,93,195,198,267,376,457,678,724,810,820,899,976],[7,11,29,38,42,52,56,67,69,70,73,84,88,131,134,193,194,196,259,265,266,296,304,328,336,385,448,532,546,548,642,644,720,770,784,800,896]⟩,
   ⟨1818,654820246305,654820253955⟩⟩
theorem r1515_checked : check r1515 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 1669; projection:R_one_six_1728.
noncomputable def r1516 : Entry :=
  ⟨⟨[63,139,170,326,372,422,451,541,583,596,713,824,936,976],[7,11,29,38,42,52,56,67,70,84,131,137,138,162,168,193,262,292,304,322,324,336,386,416,448,517,521,532,536,577,580,592,648,704,784,808,896]⟩,
   ⟨1869,449212133460,517158745410⟩⟩
theorem r1516_checked : check r1516 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 1672; projection:R_one_six_1788.
noncomputable def r1517 : Entry :=
  ⟨⟨[63,102,116,135,198,362,451,496,541,696,724,779,901,936],[7,11,29,38,42,52,56,70,84,98,100,112,131,133,134,176,194,196,208,259,266,296,322,352,385,416,448,517,521,532,536,644,656,680,769,776,896]⟩,
   ⟨1925,444685624080,444685624080⟩⟩
theorem r1517_checked : check r1517 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 1675; projection:R_one_six_1789.
noncomputable def r1518 : Entry :=
  ⟨⟨[63,71,166,198,228,248,426,451,541,628,779,837,920,976],[7,11,29,38,42,52,56,67,69,70,100,112,134,152,162,164,168,194,196,208,224,259,266,321,386,392,448,517,521,532,536,580,592,769,776,832,912]⟩,
   ⟨1926,444937282320,509110133520⟩⟩
theorem r1518_checked : check r1518 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 1683; projection:R_one_six_1786.
noncomputable def r1519 : Entry :=
  ⟨⟨[63,102,226,228,267,426,436,451,541,583,724,824,841,976],[7,11,29,38,42,52,56,67,70,98,100,148,162,164,194,196,224,259,265,266,296,304,321,386,400,416,448,517,521,532,536,577,580,720,776,784,832]⟩,
   ⟨1923,449215476240,517163201040⟩⟩
theorem r1519_checked : check r1519 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 1685; projection:R_one_six_1787.
noncomputable def r1520 : Entry :=
  ⟨⟨[63,106,226,248,263,422,432,451,541,587,820,837,920,968],[7,11,29,38,42,52,56,67,74,98,104,152,162,176,194,200,224,259,261,262,292,304,321,386,400,416,448,517,521,532,536,577,584,772,784,832,904]⟩,
   ⟨1924,449215472400,517163197200⟩⟩
theorem r1520_checked : check r1520 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 1687; projection:R_one_six_1716.
noncomputable def r1521 : Entry :=
  ⟨⟨[63,102,226,244,267,426,451,541,583,660,824,841,944,964],[7,11,29,38,42,52,56,67,70,98,100,148,162,176,194,196,224,259,265,266,296,321,386,416,448,517,521,532,536,577,580,644,656,776,816,832,896]⟩,
   ⟨1857,452987007060,577556723010⟩⟩
theorem r1521_checked : check r1521 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 1691; projection:R_one_six_1679.
noncomputable def r1522 : Entry :=
  ⟨⟨[63,116,135,157,195,198,331,358,696,724,810,880,905,961],[7,11,29,38,42,52,56,67,70,84,100,112,131,133,134,137,148,152,193,194,196,265,266,290,321,322,352,552,560,592,648,656,704,776,800,832,897]⟩,
   ⟨1821,590144078625,590144086275⟩⟩
theorem r1522_checked : check r1522 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 1700; projection:R_one_six_1688.
noncomputable def r1523 : Entry :=
  ⟨⟨[63,116,135,157,198,358,451,696,713,724,779,810,833,880],[7,11,29,38,42,52,56,70,84,100,112,131,133,134,137,148,152,193,194,196,259,290,321,322,352,521,552,560,577,592,648,656,704,769,778,800,832]⟩,
   ⟨1830,650290397985,646515532035⟩⟩
theorem r1523_checked : check r1523 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 1712; projection:R_one_six_1762.
noncomputable def r1524 : Entry :=
  ⟨⟨[63,116,230,285,391,449,452,651,682,705,752,824,841,852],[7,11,29,38,42,52,56,84,100,112,131,134,162,193,196,224,261,265,276,280,321,324,385,388,448,521,552,560,577,592,641,650,672,704,776,784,832]⟩,
   ⟨1902,646263877665,646263877890⟩⟩
theorem r1524_checked : check r1524 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 1749; projection:R_one_six_1763.
noncomputable def r1525 : Entry :=
  ⟨⟨[63,102,157,199,372,449,452,523,618,696,835,880,905,916],[7,11,29,38,42,52,56,67,70,98,100,133,137,148,152,193,196,276,321,324,368,385,388,448,515,521,522,552,560,578,608,648,656,769,784,832,896]⟩,
   ⟨1903,654568600080,654568600080⟩⟩
theorem r1525_checked : check r1525 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 1751; projection:R_one_six_1761.
noncomputable def r1526 : Entry :=
  ⟨⟨[63,106,157,203,449,472,519,614,692,824,835,872,901,912],[7,11,29,38,42,52,56,67,74,98,104,133,137,148,152,193,200,280,321,328,385,400,448,515,517,518,548,560,578,608,644,656,769,784,808,832,896]⟩,
   ⟨1901,517159858260,449211020610⟩⟩
theorem r1526_checked : check r1526 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 1770; projection:R_one_six_1740.
noncomputable def r1527 : Entry :=
  ⟨⟨[63,75,102,285,362,389,457,582,628,647,707,824,916,992],[7,11,29,38,42,52,56,67,70,73,74,98,100,133,193,261,265,276,280,296,328,352,385,388,448,518,532,560,578,580,608,643,644,704,784,800,896]⟩,
   ⟨1881,577556005665,452989231365⟩⟩
theorem r1527_checked : check r1527 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 1771; projection:R_one_six_1726.
noncomputable def r1528 : Entry :=
  ⟨⟨[63,93,139,234,325,340,457,632,678,736,775,820,899,976],[7,11,29,38,42,52,56,69,73,84,88,104,131,137,138,162,200,224,261,276,321,324,336,385,448,518,548,560,592,608,642,672,704,771,772,784,896]⟩,
   ⟨1867,582338228820,521940251220⟩⟩
theorem r1528_checked : check r1528 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 1900; projection:R_one_six_1682.
noncomputable def r1529 : Entry :=
  ⟨⟨[63,75,93,180,325,391,440,468,618,678,835,856,898,936],[7,11,29,38,42,52,56,67,69,73,74,84,88,134,148,164,176,259,261,280,321,324,336,386,388,400,424,546,552,578,584,642,672,770,776,832,896]⟩,
   ⟨1824,517918171905,517918171905⟩⟩
theorem r1529_checked : check r1529 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 1903; projection:R_one_six_1678.
noncomputable def r1530 : Entry :=
  ⟨⟨[63,75,93,135,166,323,436,453,632,682,842,852,899,944],[7,11,29,38,42,52,56,67,69,73,74,84,88,131,133,134,162,164,259,276,321,322,324,385,388,432,522,552,560,584,592,642,672,770,784,832,896]⟩,
   ⟨1820,650793714465,650793722115⟩⟩
theorem r1530_checked : check r1530 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 1905; projection:R_one_six_1794.
noncomputable def r1531 : Entry :=
  ⟨⟨[63,139,170,230,326,440,451,496,541,628,775,836,856,905],[7,11,29,38,42,52,56,70,100,112,131,137,138,162,168,194,224,259,262,280,322,324,336,385,392,432,448,517,521,532,536,580,592,769,772,776,832]⟩,
   ⟨1931,449211019860,517158744660⟩⟩
theorem r1531_checked : check r1531 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 1920; projection:R_one_six_1793.
noncomputable def r1532 : Entry :=
  ⟨⟨[63,93,202,248,263,294,426,587,706,724,820,837,899,944],[7,11,29,38,42,52,56,69,73,74,84,88,138,168,176,194,200,208,259,261,262,290,292,386,416,515,532,577,578,580,642,656,704,769,772,816,896]⟩,
   ⟨1930,590391288660,590391288660⟩⟩
theorem r1532_checked : check r1532 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 1926; projection:R_one_six_1778.
noncomputable def r1533 : Entry :=
  ⟨⟨[63,102,116,234,327,387,450,496,541,651,824,852,901,936],[7,11,29,38,42,52,56,70,84,98,100,112,131,138,168,194,224,259,261,304,322,324,336,385,386,416,448,517,521,532,536,641,648,772,784,808,896]⟩,
   ⟨1915,448712155920,448712155920⟩⟩
theorem r1533_checked : check r1533 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 1927; projection:R_one_six_1783.
noncomputable def r1534 : Entry :=
  ⟨⟨[63,102,116,195,234,327,449,496,541,651,824,852,901,936],[7,11,29,38,42,52,56,67,70,84,98,100,112,131,138,168,193,194,224,261,304,321,324,336,385,416,448,517,521,532,536,641,648,772,784,808,896]⟩,
   ⟨1920,448712155920,448712155920⟩⟩
theorem r1534_checked : check r1534 = true := by decide +kernel

-- six_orbit_dags/type3m14e11q2r1.json.gz, graph 724, terminal 1954; projection:R_one_six_1694.
noncomputable def r1535 : Entry :=
  ⟨⟨[63,116,199,285,312,389,468,587,614,705,752,810,905,944],[7,11,29,38,42,52,56,67,70,84,100,112,133,193,196,208,261,265,276,280,296,304,385,388,400,521,522,546,577,578,608,641,688,704,776,800,896]⟩,
   ⟨1836,509106783060,444932826435⟩⟩
theorem r1535_checked : check r1535 = true := by decide +kernel

#print axioms r1472_checked

end Nonrational.OldTerminalMatches.M023
