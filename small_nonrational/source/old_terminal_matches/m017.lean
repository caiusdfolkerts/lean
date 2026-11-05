module
prelude
public import InducedTerminalMatches.Basic

@[expose] public section

/-! Exact full-boundary matches, batch 17. Both facet and polygon
families are checked in both directions after the recorded permutation. -/

namespace Nonrational.OldTerminalMatches.M017
open Nonrational.InducedTerminalMatches
set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 3927; projection:R_one_six_1161.
noncomputable def r1088 : Entry :=
  ⟨⟨[63,86,199,210,300,397,484,570,628,658,779,872,899,976],[7,11,13,22,44,52,58,70,82,84,100,131,133,146,194,196,208,265,268,292,296,352,385,388,448,522,530,552,560,592,608,642,656,771,776,832,896]⟩,
   ⟨1410,444684640305,444684636930⟩⟩
theorem r1088_checked : check r1088 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 3983; projection:R_one_six_1176.
noncomputable def r1089 : Entry :=
  ⟨⟨[63,71,86,116,240,333,451,484,570,651,722,812,905,944],[7,11,13,22,44,52,58,67,69,70,82,84,100,112,131,176,194,208,224,265,268,292,321,324,385,416,448,522,530,552,560,642,649,656,776,800,896]⟩,
   ⟨1425,448712147745,448712155395⟩⟩
theorem r1089_checked : check r1089 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 3984; projection:R_one_six_1177.
noncomputable def r1090 : Entry :=
  ⟨⟨[63,71,86,180,212,333,451,484,570,651,722,812,905,944],[7,11,13,22,44,52,58,67,69,70,82,84,131,148,164,176,194,196,208,265,268,292,321,324,385,416,448,522,530,552,560,642,649,656,776,800,896]⟩,
   ⟨1426,448712147745,448712155395⟩⟩
theorem r1090_checked : check r1090 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 3985; projection:R_one_six_1175.
noncomputable def r1091 : Entry :=
  ⟨⟨[63,71,86,205,228,372,451,480,570,684,779,850,905,944],[7,11,13,22,44,52,58,67,69,70,82,84,100,137,140,164,193,196,224,259,304,322,336,352,385,416,448,522,530,552,560,648,672,770,777,784,896]⟩,
   ⟨1424,444685615905,444685623555⟩⟩
theorem r1091_checked : check r1091 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 3986; projection:R_one_six_1174.
noncomputable def r1092 : Entry :=
  ⟨⟨[63,71,86,205,372,420,451,452,570,684,779,850,905,944],[7,11,13,22,44,52,58,67,69,70,82,84,137,140,164,193,196,259,292,304,322,324,336,385,388,416,448,522,530,552,560,648,672,770,777,784,896]⟩,
   ⟨1423,444685615905,444685623555⟩⟩
theorem r1092_checked : check r1092 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 3989; projection:R_one_six_1173.
noncomputable def r1093 : Entry :=
  ⟨⟨[63,135,214,240,314,331,338,368,653,692,707,812,841,992],[7,11,13,22,44,52,58,67,82,112,131,133,134,148,176,194,208,224,266,274,296,304,322,329,336,352,521,524,548,577,641,644,672,704,776,800,832]⟩,
   ⟨1422,578064494625,521441390850⟩⟩
theorem r1093_checked : check r1093 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 3990; projection:R_one_six_1172.
noncomputable def r1094 : Entry :=
  ⟨⟨[63,71,186,240,342,395,402,464,589,628,684,835,905,992],[7,11,13,22,44,52,58,67,69,70,84,112,138,146,168,176,208,224,259,274,322,336,386,393,400,448,521,524,548,577,580,608,648,672,769,832,896]⟩,
   ⟨1421,581587709985,453242007810⟩⟩
theorem r1094_checked : check r1094 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 3991; projection:R_one_six_1171.
noncomputable def r1095 : Entry :=
  ⟨⟨[63,71,186,333,372,428,480,598,651,658,752,835,905,960],[7,11,13,22,44,52,58,67,69,70,84,112,138,146,168,176,224,265,268,292,321,324,352,392,416,448,515,530,578,592,642,649,656,704,769,832,896]⟩,
   ⟨1420,517163200545,449215475970⟩⟩
theorem r1095_checked : check r1095 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 3992; projection:R_one_six_1170.
noncomputable def r1096 : Entry :=
  ⟨⟨[63,135,214,397,436,451,480,570,587,594,752,812,841,864],[7,11,13,22,44,52,58,67,82,131,133,134,148,176,194,208,224,265,268,292,321,352,385,388,416,448,522,530,552,560,578,585,592,608,776,800,832]⟩,
   ⟨1419,449215475745,517163200770⟩⟩
theorem r1096_checked : check r1096 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 4035; projection:R_one_six_1168.
noncomputable def r1097 : Entry :=
  ⟨⟨[63,180,205,214,240,327,449,570,624,684,779,850,905,992],[7,11,13,22,44,52,58,69,70,82,112,137,140,148,164,176,193,196,208,224,259,321,322,385,448,522,530,552,560,592,608,648,672,770,777,832,896]⟩,
   ⟨1417,444685627425,444685627650⟩⟩
theorem r1097_checked : check r1097 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 4038; projection:R_one_six_1169.
noncomputable def r1098 : Entry :=
  ⟨⟨[63,116,314,364,395,432,457,480,589,598,647,705,752,914],[7,11,13,22,44,52,58,73,76,84,100,112,131,176,193,224,266,274,296,304,328,352,386,393,400,416,448,517,518,530,577,580,592,641,642,656,704]⟩,
   ⟨1418,646263878145,646263878145⟩⟩
theorem r1098_checked : check r1098 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 4059; projection:R_one_six_1167.
noncomputable def r1099 : Entry :=
  ⟨⟨[63,205,228,278,327,372,449,464,570,684,752,779,905,914],[7,11,13,22,44,52,58,69,100,112,137,140,164,193,196,208,224,259,262,274,276,321,324,336,385,400,448,522,530,552,560,648,656,672,770,777,896]⟩,
   ⟨1416,444685627425,444685627650⟩⟩
theorem r1099_checked : check r1099 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 4069; projection:R_one_six_1165.
noncomputable def r1100 : Entry :=
  ⟨⟨[63,71,108,198,244,314,368,395,406,589,707,872,905,976],[7,11,13,22,44,52,58,67,69,70,76,100,104,112,131,134,148,194,196,208,266,274,296,304,336,352,386,393,400,521,577,584,641,704,776,832,896]⟩,
   ⟨1414,577561166625,452990345475⟩⟩
theorem r1100_checked : check r1100 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 4071; projection:R_one_six_1166.
noncomputable def r1101 : Entry :=
  ⟨⟨[63,71,108,198,244,333,451,480,570,651,662,872,905,944],[7,11,13,22,44,52,58,67,69,70,76,100,104,131,134,148,176,194,196,224,265,321,328,352,385,416,448,522,530,552,560,642,649,656,776,800,896]⟩,
   ⟨1415,448712147745,448712155395⟩⟩
theorem r1101_checked : check r1101 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 4079; projection:R_one_six_1164.
noncomputable def r1102 : Entry :=
  ⟨⟨[63,205,278,391,436,449,464,570,684,712,752,779,841,850],[7,11,13,22,44,52,58,73,133,140,164,176,193,200,208,259,262,274,276,321,336,385,388,400,448,522,530,552,560,584,592,648,672,704,770,777,832]⟩,
   ⟨1413,444937285665,509110137090⟩⟩
theorem r1102_checked : check r1102 = true := by decide +kernel

-- six_orbit_dags/type2m12e11q2r2.json.gz, graph 360, terminal 0; projection:R_one_six_1213.
noncomputable def r1103 : Entry :=
  ⟨⟨[63,71,118,212,362,496,541,587,709,824,916,968],[7,11,29,42,54,56,67,69,70,74,84,98,112,148,196,208,296,304,328,352,400,448,517,521,532,536,577,584,644,704,776,784,896]⟩,
   ⟨1437,521940370485,582337303635⟩⟩
theorem r1103_checked : check r1103 = true := by decide +kernel

-- six_orbit_dags/type2m12e11q2r2.json.gz, graph 360, terminal 33; projection:R_one_six_1231.
noncomputable def r1104 : Entry :=
  ⟨⟨[63,75,157,201,362,451,472,566,647,824,916,930],[7,11,29,42,54,56,67,73,74,131,133,137,148,152,193,200,280,290,296,322,328,386,400,448,518,532,546,560,642,644,784,800,896]⟩,
   ⟨1438,517163201025,449215476225⟩⟩
theorem r1104_checked : check r1104 = true := by decide +kernel

-- six_orbit_dags/type2m12e11q2r2.json.gz, graph 360, terminal 36; projection:R_one_six_1232.
noncomputable def r1105 : Entry :=
  ⟨⟨[63,93,201,234,310,354,376,651,709,775,852,962],[7,11,29,42,54,56,69,73,84,88,98,104,137,138,193,194,200,262,276,290,304,322,336,352,515,517,580,641,642,704,770,772,832]⟩,
   ⟨1439,578060231685,521436021585⟩⟩
theorem r1105_checked : check r1105 = true := by decide +kernel

-- six_orbit_dags/type2m12e11q2r2.json.gz, graph 360, terminal 37; projection:R_one_six_1233.
noncomputable def r1106 : Entry :=
  ⟨⟨[63,157,201,234,331,450,453,566,696,775,916,930],[7,11,29,42,54,56,73,74,133,137,148,152,162,168,193,194,200,259,261,321,322,386,388,448,518,532,546,560,656,672,770,772,896]⟩,
   ⟨1440,448707896325,448706790225⟩⟩
theorem r1106_checked : check r1106 = true := by decide +kernel

-- six_orbit_dags/type2m12e11q2r2.json.gz, graph 360, terminal 44; projection:R_one_six_1242.
noncomputable def r1107 : Entry :=
  ⟨⟨[63,195,234,310,327,354,376,541,651,709,728,852],[7,11,29,42,54,56,67,69,88,98,104,131,138,193,194,200,262,276,290,304,322,324,336,352,517,521,532,536,580,592,641,648,704]⟩,
   ⟨1441,509357458485,509356414035⟩⟩
theorem r1107_checked : check r1107 = true := by decide +kernel

-- six_orbit_dags/type2m12e11q2r2.json.gz, graph 360, terminal 45; projection:R_one_six_1243.
noncomputable def r1108 : Entry :=
  ⟨⟨[63,71,182,362,418,440,454,541,587,837,856,916],[7,11,29,42,54,56,67,69,70,74,134,148,162,176,280,290,296,322,324,328,386,388,400,416,517,521,532,536,577,584,772,784,832]⟩,
   ⟨1442,517158863925,449210094675⟩⟩
theorem r1108_checked : check r1108 = true := by decide +kernel

-- six_orbit_dags/type2m12e11q2r2.json.gz, graph 360, terminal 46; projection:R_one_six_1245.
noncomputable def r1109 : Entry :=
  ⟨⟨[63,71,120,285,331,453,472,566,618,710,752,916],[7,11,29,42,54,56,67,69,70,74,88,104,112,196,208,261,265,276,280,321,328,388,400,448,518,532,546,560,578,608,644,656,704]⟩,
   ⟨1444,509110136865,444937285890⟩⟩
theorem r1109_checked : check r1109 = true := by decide +kernel

-- six_orbit_dags/type2m12e11q2r2.json.gz, graph 360, terminal 47; projection:R_one_six_1244.
noncomputable def r1110 : Entry :=
  ⟨⟨[63,71,285,331,376,453,464,566,618,710,752,916],[7,11,29,42,54,56,67,69,70,74,104,112,196,208,261,265,276,280,321,328,336,388,400,448,518,532,546,560,578,608,644,656,704]⟩,
   ⟨1443,509110136865,444937285890⟩⟩
theorem r1110_checked : check r1110 = true := by decide +kernel

-- six_orbit_dags/type2m12e11q2r2.json.gz, graph 360, terminal 48; projection:R_one_six_1246.
noncomputable def r1111 : Entry :=
  ⟨⟨[63,310,391,426,452,496,541,651,696,709,720,852],[7,11,29,42,54,56,131,133,138,168,176,196,208,262,276,290,304,324,336,386,388,416,448,517,521,532,536,580,592,641,648,656,704]⟩,
   ⟨1445,509357335605,509356413780⟩⟩
theorem r1111_checked : check r1111 = true := by decide +kernel

-- six_orbit_dags/type2m12e12q3r2.json.gz, graph 362, terminal 1; projection:R_one_six_1247.
noncomputable def r1112 : Entry :=
  ⟨⟨[63,118,157,197,327,362,395,696,724,880,936,961],[7,11,29,42,54,56,69,70,84,98,112,133,137,148,152,193,196,259,266,296,321,322,352,385,392,560,592,656,680,704,800,832,896]⟩,
   ⟨1446,590296204065,590377853190⟩⟩
theorem r1112_checked : check r1112 = true := by decide +kernel

-- six_orbit_dags/type2m12e12q3r2.json.gz, graph 362, terminal 2; projection:R_one_six_1248.
noncomputable def r1113 : Entry :=
  ⟨⟨[63,93,182,197,331,391,696,724,810,856,930,961],[7,11,29,42,54,56,69,73,84,88,133,134,148,162,176,193,196,259,266,321,328,385,386,536,552,592,656,672,704,776,802,832,896]⟩,
   ⟨1447,590395491105,590395678980⟩⟩
theorem r1113_checked : check r1113 = true := by decide +kernel

-- six_orbit_dags/type2m12e12q3r2.json.gz, graph 362, terminal 4; projection:R_one_six_1251.
noncomputable def r1114 : Entry :=
  ⟨⟨[63,157,201,248,331,391,566,618,752,838,916,961],[7,11,29,42,54,56,73,74,104,133,137,148,152,193,200,240,259,262,321,322,385,388,518,532,546,560,578,608,656,704,772,832,896]⟩,
   ⟨1450,448707896325,448706790225⟩⟩
theorem r1114_checked : check r1114 = true := by decide +kernel

-- six_orbit_dags/type2m12e12q3r2.json.gz, graph 362, terminal 5; projection:R_one_six_1250.
noncomputable def r1115 : Entry :=
  ⟨⟨[63,157,201,248,331,453,566,618,752,775,916,962],[7,11,29,42,54,56,73,74,104,133,137,148,152,193,200,240,259,261,321,322,388,448,518,532,546,560,578,608,656,704,770,772,896]⟩,
   ⟨1449,448707896325,448706790225⟩⟩
theorem r1115_checked : check r1115 = true := by decide +kernel

-- six_orbit_dags/type2m12e12q3r2.json.gz, graph 362, terminal 12; projection:R_one_six_1249.
noncomputable def r1116 : Entry :=
  ⟨⟨[63,93,201,234,395,453,566,632,775,852,930,992],[7,11,29,42,54,56,69,73,84,88,104,137,138,162,193,200,224,259,261,324,385,386,448,518,532,546,560,592,608,770,772,832,928]⟩,
   ⟨1448,449211211845,517157765970⟩⟩
theorem r1116_checked : check r1116 = true := by decide +kernel

-- six_orbit_dags/type2m12e12q3r2.json.gz, graph 362, terminal 16; projection:R_one_six_1253.
noncomputable def r1117 : Entry :=
  ⟨⟨[63,118,199,376,426,452,482,541,651,852,901,920],[7,11,29,42,54,56,70,84,98,112,131,133,138,194,196,280,296,324,336,352,388,392,418,448,517,521,532,536,641,648,772,784,896]⟩,
   ⟨1451,517913715765,517912793940⟩⟩
theorem r1117_checked : check r1117 = true := by decide +kernel

-- six_orbit_dags/type2m12e12q3r2.json.gz, graph 362, terminal 18; projection:R_one_six_1254.
noncomputable def r1118 : Entry :=
  ⟨⟨[63,71,310,362,454,496,541,587,696,709,744,916],[7,11,29,42,54,56,67,69,70,74,104,176,196,224,262,276,290,304,322,352,388,400,448,517,521,532,536,577,584,644,656,680,704]⟩,
   ⟨1452,444685627425,444685627650⟩⟩
theorem r1118_checked : check r1118 = true := by decide +kernel

-- six_orbit_dags/type2m12e12q3r2.json.gz, graph 362, terminal 19; projection:R_one_six_1255.
noncomputable def r1119 : Entry :=
  ⟨⟨[63,118,199,234,452,496,541,651,824,852,901,936],[7,11,29,42,54,56,70,84,98,112,131,133,138,168,194,196,224,304,324,336,388,416,448,517,521,532,536,641,648,772,784,808,896]⟩,
   ⟨1453,449215475745,517163200770⟩⟩
theorem r1119_checked : check r1119 = true := by decide +kernel

-- six_orbit_dags/type2m12e13q4r2.json.gz, graph 363, terminal 0; projection:R_one_six_1256.
noncomputable def r1120 : Entry :=
  ⟨⟨[63,182,234,285,331,647,707,752,824,837,872,916],[7,11,29,42,54,56,67,74,104,134,148,162,176,194,224,261,265,276,280,321,328,517,560,577,608,643,644,656,704,772,784,808,832]⟩,
   ⟨1454,36391036230,448557826905⟩⟩
theorem r1120_checked : check r1120 = true := by decide +kernel

-- six_orbit_dags/type2m13e11q2r2.json.gz, graph 364, terminal 3; projection:R_one_six_1260.
noncomputable def r1121 : Entry :=
  ⟨⟨[63,71,118,226,248,285,682,707,724,779,788,837,920],[7,11,29,42,54,56,67,69,70,84,98,112,152,162,168,194,208,224,261,265,276,280,515,522,532,577,580,642,648,656,704,769,772,776,784]⟩,
   ⟨1456,578064483105,521441386755⟩⟩
theorem r1121_checked : check r1121 = true := by decide +kernel

-- six_orbit_dags/type2m13e11q2r2.json.gz, graph 364, terminal 4; projection:R_one_six_1258.
noncomputable def r1122 : Entry :=
  ⟨⟨[63,75,93,197,212,362,451,472,566,647,824,916,930],[7,11,29,42,54,56,67,69,73,74,84,88,131,133,148,193,196,208,280,290,296,322,328,386,400,448,518,532,546,560,642,644,784,800,896]⟩,
   ⟨1455,521944707585,582342685185⟩⟩
theorem r1122_checked : check r1122 = true := by decide +kernel

-- six_orbit_dags/type2m13e11q2r2.json.gz, graph 364, terminal 9; projection:R_one_six_1264.
noncomputable def r1123 : Entry :=
  ⟨⟨[63,71,118,212,285,323,453,618,752,779,824,916,962],[7,11,29,42,54,56,67,69,70,84,98,112,148,196,208,259,261,265,276,280,321,322,388,448,522,552,560,578,608,656,704,770,776,784,896]⟩,
   ⟨1460,650789266485,650788344660⟩⟩
theorem r1123_checked : check r1123 = true := by decide +kernel

-- six_orbit_dags/type2m13e11q2r2.json.gz, graph 364, terminal 10; projection:R_one_six_1269.
noncomputable def r1124 : Entry :=
  ⟨⟨[63,71,118,203,212,362,456,496,541,709,824,905,916],[7,11,29,42,54,56,67,69,70,74,84,98,112,137,148,193,196,200,208,296,304,328,352,392,400,448,517,521,532,536,641,644,776,784,896]⟩,
   ⟨1465,521940370485,582337303635⟩⟩
theorem r1124_checked : check r1124 = true := by decide +kernel

-- six_orbit_dags/type2m13e11q2r2.json.gz, graph 364, terminal 11; projection:R_one_six_1266.
noncomputable def r1125 : Entry :=
  ⟨⟨[63,71,118,212,267,362,451,496,541,709,824,905,916],[7,11,29,42,54,56,67,69,70,84,98,112,148,193,196,208,259,265,266,296,304,322,352,385,400,448,517,521,532,536,641,644,776,784,896]⟩,
   ⟨1462,521940247605,582337303380⟩⟩
theorem r1125_checked : check r1125 = true := by decide +kernel

-- six_orbit_dags/type2m13e11q2r2.json.gz, graph 364, terminal 12; projection:R_one_six_1262.
noncomputable def r1126 : Entry :=
  ⟨⟨[63,135,182,212,285,453,682,707,752,779,824,833,852],[7,11,29,42,54,56,84,131,133,134,148,162,176,193,196,208,261,265,276,280,321,324,515,522,552,560,577,592,642,672,704,769,776,784,832]⟩,
   ⟨1458,650285950005,646510154580⟩⟩
theorem r1126_checked : check r1126 = true := by decide +kernel

-- six_orbit_dags/type2m13e11q2r2.json.gz, graph 364, terminal 13; projection:R_one_six_1277.
noncomputable def r1127 : Entry :=
  ⟨⟨[63,71,118,203,212,226,426,496,541,709,824,905,916],[7,11,29,42,54,56,67,69,70,84,98,112,137,138,148,162,193,194,196,208,224,296,304,392,400,416,517,521,532,536,641,644,776,784,896]⟩,
   ⟨1472,521940370485,582337303635⟩⟩
theorem r1127_checked : check r1127 = true := by decide +kernel

-- six_orbit_dags/type2m13e11q2r2.json.gz, graph 364, terminal 15; projection:R_one_six_1275.
noncomputable def r1128 : Entry :=
  ⟨⟨[63,157,212,248,310,362,368,395,709,775,852,897,968],[7,11,29,42,54,56,84,104,112,133,137,148,152,196,200,208,259,262,266,276,290,304,328,336,352,385,392,517,580,641,704,769,772,832,896]⟩,
   ⟨1470,650290409505,646515536130⟩⟩
theorem r1128_checked : check r1128 = true := by decide +kernel

-- six_orbit_dags/type2m13e11q2r2.json.gz, graph 364, terminal 16; projection:R_one_six_1274.
noncomputable def r1129 : Entry :=
  ⟨⟨[63,182,199,202,212,285,325,331,682,752,824,852,968],[7,11,29,42,54,56,67,69,74,84,134,138,148,162,176,194,196,200,208,261,265,276,280,321,324,328,552,560,592,648,672,704,776,784,832]⟩,
   ⟨1469,650286072885,646510154835⟩⟩
theorem r1129_checked : check r1129 = true := by decide +kernel

-- six_orbit_dags/type2m13e11q2r2.json.gz, graph 364, terminal 17; projection:R_one_six_1265.
noncomputable def r1130 : Entry :=
  ⟨⟨[63,157,195,197,310,327,340,651,696,724,810,880,962],[7,11,29,42,54,56,67,69,84,131,133,137,148,152,193,194,196,262,276,290,304,322,324,336,522,552,560,592,642,648,656,704,770,800,832]⟩,
   ⟨1461,646259418165,646258496340⟩⟩
theorem r1130_checked : check r1130 = true := by decide +kernel

-- six_orbit_dags/type2m13e11q2r2.json.gz, graph 364, terminal 18; projection:R_one_six_1261.
noncomputable def r1131 : Entry :=
  ⟨⟨[63,157,197,203,310,327,340,650,696,724,810,880,962],[7,11,29,42,54,56,67,69,84,133,137,138,148,152,193,194,196,262,276,290,304,322,324,336,522,552,560,592,642,648,656,704,770,800,832]⟩,
   ⟨1457,646259418165,646258496340⟩⟩
theorem r1131_checked : check r1131 = true := by decide +kernel

-- six_orbit_dags/type2m13e11q2r2.json.gz, graph 364, terminal 19; projection:R_one_six_1276.
noncomputable def r1132 : Entry :=
  ⟨⟨[63,157,170,197,310,327,340,395,696,724,880,930,961],[7,11,29,42,54,56,69,84,133,137,138,148,152,162,168,193,196,259,262,276,290,304,321,324,336,385,386,560,592,656,672,704,800,832,896]⟩,
   ⟨1471,646259418165,646258496340⟩⟩
theorem r1132_checked : check r1132 = true := by decide +kernel

-- six_orbit_dags/type2m13e11q2r2.json.gz, graph 364, terminal 20; projection:R_one_six_1271.
noncomputable def r1133 : Entry :=
  ⟨⟨[63,157,197,310,327,340,395,449,696,724,810,880,968],[7,11,29,42,54,56,69,84,133,137,148,152,193,196,259,262,266,276,290,304,321,324,336,385,392,448,552,560,592,648,656,704,776,800,832]⟩,
   ⟨1467,646259541045,646258496595⟩⟩
theorem r1133_checked : check r1133 = true := by decide +kernel

-- six_orbit_dags/type2m13e11q2r2.json.gz, graph 364, terminal 21; projection:R_one_six_1268.
noncomputable def r1134 : Entry :=
  ⟨⟨[63,157,197,310,327,340,395,696,724,810,880,904,961],[7,11,29,42,54,56,69,84,133,137,148,152,193,196,259,262,266,276,290,304,321,324,336,385,392,552,560,592,648,656,704,776,800,832,896]⟩,
   ⟨1464,646259418165,646258496340⟩⟩
theorem r1134_checked : check r1134 = true := by decide +kernel

-- six_orbit_dags/type2m13e11q2r2.json.gz, graph 364, terminal 22; projection:R_one_six_1263.
noncomputable def r1135 : Entry :=
  ⟨⟨[63,182,199,212,285,325,643,682,752,779,824,852,961],[7,11,29,42,54,56,69,84,131,134,148,162,176,193,196,208,261,265,276,280,321,324,515,522,552,560,592,641,642,672,704,769,776,784,832]⟩,
   ⟨1459,650285950005,646510154580⟩⟩
theorem r1135_checked : check r1135 = true := by decide +kernel

-- six_orbit_dags/type2m13e11q2r2.json.gz, graph 364, terminal 25; projection:R_one_six_1267.
noncomputable def r1136 : Entry :=
  ⟨⟨[63,182,198,212,267,426,451,496,541,583,824,841,852],[7,11,29,42,54,56,67,70,84,134,148,162,176,194,196,208,259,265,266,296,304,321,336,386,416,448,517,521,532,536,577,580,776,784,832]⟩,
   ⟨1463,521436931125,578059113300⟩⟩
theorem r1136_checked : check r1136 = true := by decide +kernel

-- six_orbit_dags/type2m13e11q2r2.json.gz, graph 364, terminal 26; projection:R_one_six_1273.
noncomputable def r1137 : Entry :=
  ⟨⟨[63,182,198,203,212,285,327,329,682,752,824,852,968],[7,11,29,42,54,56,67,70,73,84,134,138,148,162,176,194,196,200,208,261,265,276,280,321,324,328,552,560,592,648,672,704,776,784,832]⟩,
   ⟨1468,650286072885,646510154835⟩⟩
theorem r1137_checked : check r1137 = true := by decide +kernel

-- six_orbit_dags/type2m13e11q2r2.json.gz, graph 364, terminal 27; projection:R_one_six_1270.
noncomputable def r1138 : Entry :=
  ⟨⟨[63,182,198,203,212,426,456,496,541,583,824,841,852],[7,11,29,42,54,56,67,70,73,84,134,138,148,162,176,194,196,200,208,296,304,328,336,392,416,448,517,521,532,536,577,580,776,784,832]⟩,
   ⟨1466,521437054005,578059113555⟩⟩
theorem r1138_checked : check r1138 = true := by decide +kernel

-- six_orbit_dags/type2m13e11q2r2.json.gz, graph 364, terminal 61; projection:R_one_six_1310.
noncomputable def r1139 : Entry :=
  ⟨⟨[63,120,157,201,216,331,391,566,618,752,838,916,961],[7,11,29,42,54,56,73,74,88,104,112,133,137,148,152,193,200,208,259,262,321,322,385,388,518,532,546,560,578,608,656,704,772,832,896]⟩,
   ⟨1505,448707896325,448706790225⟩⟩
theorem r1139_checked : check r1139 = true := by decide +kernel

-- six_orbit_dags/type2m13e11q2r2.json.gz, graph 364, terminal 63; projection:R_one_six_1309.
noncomputable def r1140 : Entry :=
  ⟨⟨[63,120,157,201,216,331,453,566,618,752,775,916,962],[7,11,29,42,54,56,73,74,88,104,112,133,137,148,152,193,200,208,259,261,321,322,388,448,518,532,546,560,578,608,656,704,770,772,896]⟩,
   ⟨1504,448707896325,448706790225⟩⟩
theorem r1140_checked : check r1140 = true := by decide +kernel

-- six_orbit_dags/type2m13e11q2r2.json.gz, graph 364, terminal 87; projection:R_one_six_1312.
noncomputable def r1141 : Entry :=
  ⟨⟨[63,71,118,195,226,376,426,541,651,709,852,920,992],[7,11,29,42,54,56,67,69,70,84,98,112,131,138,162,193,194,224,280,296,336,352,392,416,517,521,532,536,580,641,648,704,784,832,896]⟩,
   ⟨1507,449215464225,517163196675⟩⟩
theorem r1141_checked : check r1141 = true := by decide +kernel

-- six_orbit_dags/type2m13e11q2r2.json.gz, graph 364, terminal 89; projection:R_one_six_1311.
noncomputable def r1142 : Entry :=
  ⟨⟨[63,71,118,195,226,426,496,541,651,709,824,852,968],[7,11,29,42,54,56,67,69,70,84,98,112,131,138,162,193,194,224,296,304,336,392,416,448,517,521,532,536,580,641,648,704,776,784,832]⟩,
   ⟨1506,449215464225,517163196675⟩⟩
theorem r1142_checked : check r1142 = true := by decide +kernel

-- six_orbit_dags/type2m13e11q2r2.json.gz, graph 364, terminal 91; projection:R_one_six_1314.
noncomputable def r1143 : Entry :=
  ⟨⟨[63,93,120,197,201,362,395,566,647,724,880,930,968],[7,11,29,42,54,56,69,73,84,88,104,112,131,133,137,193,196,200,266,290,328,352,386,392,518,532,546,560,592,642,644,704,800,832,896]⟩,
   ⟨1509,453237744645,581582340945⟩⟩
theorem r1143_checked : check r1143 = true := by decide +kernel

-- six_orbit_dags/type2m13e11q2r2.json.gz, graph 364, terminal 92; projection:R_one_six_1313.
noncomputable def r1144 : Entry :=
  ⟨⟨[63,71,118,203,226,426,496,541,709,824,852,905,960],[7,11,29,42,54,56,67,69,70,84,98,112,137,138,162,193,194,224,296,304,336,392,416,448,517,521,532,536,580,641,704,776,784,832,896]⟩,
   ⟨1508,449215464225,517163196675⟩⟩
theorem r1144_checked : check r1144 = true := by decide +kernel

-- six_orbit_dags/type2m13e11q2r2.json.gz, graph 364, terminal 93; projection:R_one_six_1316.
noncomputable def r1145 : Entry :=
  ⟨⟨[63,93,120,197,201,395,488,566,647,724,810,880,962],[7,11,29,42,54,56,69,73,84,88,104,112,131,133,137,193,196,200,266,296,352,386,392,448,518,532,546,560,592,642,644,704,770,800,832]⟩,
   ⟨1511,453237744645,581582340945⟩⟩
theorem r1145_checked : check r1145 = true := by decide +kernel

-- six_orbit_dags/type2m13e11q2r2.json.gz, graph 364, terminal 94; projection:R_one_six_1315.
noncomputable def r1146 : Entry :=
  ⟨⟨[63,71,118,226,248,426,451,541,724,779,837,920,960],[7,11,29,42,54,56,67,69,70,84,98,112,152,162,168,194,208,224,259,266,321,386,392,448,517,521,532,536,580,656,704,769,776,832,896]⟩,
   ⟨1510,453241996065,581587706115⟩⟩
theorem r1146_checked : check r1146 = true := by decide +kernel

-- six_orbit_dags/type2m13e11q2r2.json.gz, graph 364, terminal 96; projection:R_one_six_1294.
noncomputable def r1147 : Entry :=
  ⟨⟨[63,75,93,197,310,344,391,468,618,707,824,930,968],[7,11,29,42,54,56,67,69,73,74,84,88,131,133,193,196,262,276,280,290,304,328,336,386,388,448,546,552,578,584,642,704,776,800,896]⟩,
   ⟨1489,646511272965,650285040465⟩⟩
theorem r1147_checked : check r1147 = true := by decide +kernel

-- six_orbit_dags/type2m13e11q2r2.json.gz, graph 364, terminal 97; projection:R_one_six_1295.
noncomputable def r1148 : Entry :=
  ⟨⟨[63,106,195,310,376,391,482,541,587,709,792,916,968],[7,11,29,42,54,56,67,74,98,104,131,133,193,194,262,276,280,290,304,328,352,386,388,448,517,521,532,536,577,584,644,704,776,784,896]⟩,
   ⟨1490,509105872965,444931851090⟩⟩
theorem r1148_checked : check r1148 = true := by decide +kernel

-- six_orbit_dags/type2m13e11q2r2.json.gz, graph 364, terminal 99; projection:R_one_six_1296.
noncomputable def r1149 : Entry :=
  ⟨⟨[63,157,201,248,310,362,368,464,587,709,775,916,962],[7,11,29,42,54,56,73,74,104,112,133,137,148,152,193,200,208,262,276,290,304,322,336,352,400,448,515,517,577,578,644,704,770,772,896]⟩,
   ⟨1491,577556915205,452984980305⟩⟩
theorem r1149_checked : check r1149 = true := by decide +kernel

-- six_orbit_dags/type2m13e11q2r2.json.gz, graph 364, terminal 100; projection:R_one_six_1297.
noncomputable def r1150 : Entry :=
  ⟨⟨[63,157,201,248,310,362,368,464,587,647,838,916,961],[7,11,29,42,54,56,73,74,104,112,133,137,148,152,193,200,208,262,276,290,304,322,336,352,400,448,515,518,577,578,641,644,772,832,896]⟩,
   ⟨1492,577556915205,452984980305⟩⟩
theorem r1150_checked : check r1150 = true := by decide +kernel

-- six_orbit_dags/type2m13e11q2r2.json.gz, graph 364, terminal 101; projection:R_one_six_1279.
noncomputable def r1151 : Entry :=
  ⟨⟨[63,118,199,226,285,325,395,449,632,682,852,920,992],[7,11,29,42,54,56,69,70,84,98,112,131,138,162,193,194,224,261,265,276,280,321,324,385,392,448,536,552,592,608,648,672,784,832,896]⟩,
   ⟨1474,578064483105,521441386755⟩⟩
theorem r1151_checked : check r1151 = true := by decide +kernel

#print axioms r1088_checked

end Nonrational.OldTerminalMatches.M017
