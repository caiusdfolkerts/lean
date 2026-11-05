module
prelude
public import InducedTerminalMatches.Basic

@[expose] public section

/-! Exact full-boundary matches, batch 20. Both facet and polygon
families are checked in both directions after the recorded permutation. -/

namespace Nonrational.OldTerminalMatches.M020
open Nonrational.InducedTerminalMatches
set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- six_orbit_dags/type3m12e11q1r1.json.gz, graph 716, terminal 20; projection:R_one_six_1422.
noncomputable def r1280 : Entry :=
  ⟨⟨[63,102,106,199,376,458,484,541,651,820,901,920],[7,11,29,38,42,52,56,70,74,98,100,104,131,133,138,194,196,280,292,304,328,352,388,392,448,517,521,532,536,641,648,772,784,896]⟩,
   ⟨1628,448712147745,448712155395⟩⟩
theorem r1280_checked : check r1280 = true := by decide +kernel

-- six_orbit_dags/type3m12e11q1r1.json.gz, graph 716, terminal 23; projection:R_one_six_1424.
noncomputable def r1281 : Entry :=
  ⟨⟨[63,199,234,358,376,452,456,541,651,820,901,920],[7,11,29,38,42,52,56,70,98,104,131,133,138,194,196,200,280,292,304,324,328,352,388,392,448,517,521,532,536,641,648,772,784,896]⟩,
   ⟨1630,448712147745,448712155395⟩⟩
theorem r1281_checked : check r1281 = true := by decide +kernel

-- six_orbit_dags/type3m12e11q1r1.json.gz, graph 716, terminal 25; projection:R_one_six_1419.
noncomputable def r1282 : Entry :=
  ⟨⟨[63,93,327,395,422,449,468,632,682,692,713,720],[7,11,29,38,42,52,56,69,73,84,88,137,138,148,162,164,193,208,259,262,321,324,385,386,388,448,552,560,584,592,648,656,672,704]⟩,
   ⟨1625,650793725985,650793726210⟩⟩
theorem r1282_checked : check r1282 = true := by decide +kernel

-- six_orbit_dags/type3m12e11q2r1.json.gz, graph 717, terminal 4; projection:R_one_six_1477.
noncomputable def r1283 : Entry :=
  ⟨⟨[63,75,180,230,285,327,468,618,696,841,920,992],[7,11,29,38,42,52,56,67,70,73,74,98,148,164,176,196,224,261,265,276,280,321,324,400,448,552,584,608,664,672,776,832,896]⟩,
   ⟨1641,578064494625,521441390850⟩⟩
theorem r1283_checked : check r1283 = true := by decide +kernel

-- six_orbit_dags/type3m12e11q2r1.json.gz, graph 717, terminal 5; projection:R_one_six_1442.
noncomputable def r1284 : Entry :=
  ⟨⟨[63,180,199,285,325,331,468,678,696,810,920,962],[7,11,29,38,42,52,56,67,69,134,148,164,176,194,196,261,265,266,276,280,321,322,324,400,448,546,552,642,664,672,770,776,896]⟩,
   ⟨1635,646515536385,650290409985⟩⟩
theorem r1284_checked : check r1284 = true := by decide +kernel

-- six_orbit_dags/type3m12e11q2r1.json.gz, graph 717, terminal 8; projection:R_one_six_1447.
noncomputable def r1285 : Entry :=
  ⟨⟨[63,71,157,195,395,440,614,709,810,820,916,962],[7,11,29,38,42,52,56,67,69,70,131,133,137,148,152,193,194,266,296,304,386,392,400,546,548,578,580,644,704,770,788,800,896]⟩,
   ⟨1637,650290406145,646515532545⟩⟩
theorem r1285_checked : check r1285 = true := by decide +kernel

-- six_orbit_dags/type3m12e11q2r1.json.gz, graph 717, terminal 13; projection:R_one_six_1476.
noncomputable def r1286 : Entry :=
  ⟨⟨[63,71,102,157,203,362,440,628,709,880,916,968],[7,11,29,38,42,52,56,67,69,70,74,98,100,133,137,148,152,193,200,296,304,328,352,392,400,532,580,624,644,704,784,832,896]⟩,
   ⟨1640,590144078625,590144086275⟩⟩
theorem r1286_checked : check r1286 = true := by decide +kernel

-- six_orbit_dags/type3m12e11q2r1.json.gz, graph 717, terminal 14; projection:R_one_six_1475.
noncomputable def r1287 : Entry :=
  ⟨⟨[63,71,102,362,440,484,541,587,692,709,856,976],[7,11,29,38,42,52,56,67,69,70,74,98,100,164,176,196,280,296,328,352,400,416,448,517,521,532,536,577,584,644,656,704,848]⟩,
   ⟨1639,453242007585,581587710210⟩⟩
theorem r1287_checked : check r1287 = true := by decide +kernel

-- six_orbit_dags/type3m12e11q2r1.json.gz, graph 717, terminal 15; projection:R_one_six_1483.
noncomputable def r1288 : Entry :=
  ⟨⟨[63,75,166,234,436,454,488,541,583,824,841,852],[7,11,29,38,42,52,56,67,70,73,74,134,162,164,194,232,276,296,304,324,328,388,416,448,517,521,532,536,577,580,776,784,832]⟩,
   ⟨1646,449215475745,517163200770⟩⟩
theorem r1288_checked : check r1288 = true := by decide +kernel

-- six_orbit_dags/type3m12e11q2r1.json.gz, graph 717, terminal 17; projection:R_one_six_1478.
noncomputable def r1289 : Entry :=
  ⟨⟨[63,71,230,362,440,480,541,587,692,709,856,976],[7,11,29,38,42,52,56,67,69,70,74,98,164,176,196,224,280,296,328,352,400,416,448,517,521,532,536,577,584,644,656,704,848]⟩,
   ⟨1642,453241996065,581587706115⟩⟩
theorem r1289_checked : check r1289 = true := by decide +kernel

-- six_orbit_dags/type3m12e11q2r1.json.gz, graph 717, terminal 18; projection:R_one_six_1479.
noncomputable def r1290 : Entry :=
  ⟨⟨[63,71,230,362,436,480,541,587,709,824,916,968],[7,11,29,38,42,52,56,67,69,70,74,98,164,196,224,296,304,328,352,404,416,448,517,521,532,536,577,584,644,704,776,784,896]⟩,
   ⟨1643,453241996065,581587706115⟩⟩
theorem r1290_checked : check r1290 = true := by decide +kernel

-- six_orbit_dags/type3m12e11q2r1.json.gz, graph 717, terminal 19; projection:R_one_six_1480.
noncomputable def r1291 : Entry :=
  ⟨⟨[63,71,184,234,358,496,541,587,820,837,920,968],[7,11,29,38,42,52,56,67,69,70,74,98,152,168,176,200,224,292,304,324,352,400,448,517,521,532,536,577,584,772,784,832,904]⟩,
   ⟨1644,449215464225,517163196675⟩⟩
theorem r1291_checked : check r1291 = true := by decide +kernel

-- six_orbit_dags/type3m12e11q2r1.json.gz, graph 717, terminal 21; projection:R_one_six_1482.
noncomputable def r1292 : Entry :=
  ⟨⟨[63,75,198,234,285,327,457,678,696,820,920,964],[7,11,29,38,42,52,56,67,70,73,74,134,162,168,194,196,200,261,265,276,280,321,324,392,448,548,560,644,664,672,772,784,896]⟩,
   ⟨1645,646515535905,650290409730⟩⟩
theorem r1292_checked : check r1292 = true := by decide +kernel

-- six_orbit_dags/type3m12e11q2r1.json.gz, graph 717, terminal 26; projection:R_one_six_1441.
noncomputable def r1293 : Entry :=
  ⟨⟨[63,93,212,248,267,327,457,682,692,806,906,964],[7,11,29,38,42,52,56,69,73,84,88,148,168,176,196,200,208,259,262,265,266,321,324,392,448,546,548,644,650,672,770,772,896]⟩,
   ⟨1634,590392406100,590391293250⟩⟩
theorem r1293_checked : check r1293 = true := by decide +kernel

-- six_orbit_dags/type3m12e11q2r1.json.gz, graph 717, terminal 27; projection:R_one_six_1485.
noncomputable def r1294 : Entry :=
  ⟨⟨[63,75,358,426,436,452,458,541,583,696,713,724],[7,11,29,38,42,52,56,67,70,73,74,148,168,176,196,200,290,292,322,324,388,394,416,448,517,521,532,536,577,580,648,656,704]⟩,
   ⟨1647,453242007585,581587710210⟩⟩
theorem r1294_checked : check r1294 = true := by decide +kernel

-- six_orbit_dags/type3m12e11q2r1.json.gz, graph 717, terminal 28; projection:R_one_six_1493.
noncomputable def r1295 : Entry :=
  ⟨⟨[63,75,157,199,390,436,618,713,806,824,920,962],[7,11,29,38,42,52,56,67,73,74,133,134,137,148,152,193,194,262,292,304,386,388,400,546,552,578,584,648,704,770,792,800,896]⟩,
   ⟨1649,581584367700,453237552450⟩⟩
theorem r1295_checked : check r1295 = true := by decide +kernel

-- six_orbit_dags/type3m12e11q2r1.json.gz, graph 717, terminal 34; projection:R_one_six_1443.
noncomputable def r1296 : Entry :=
  ⟨⟨[63,157,199,201,308,422,587,728,810,824,916,962],[7,11,29,38,42,52,56,67,73,133,134,137,148,152,193,194,200,276,290,292,304,386,388,522,536,578,584,656,704,770,784,808,896]⟩,
   ⟨1636,590144086785,590144086785⟩⟩
theorem r1296_checked : check r1296 = true := by decide +kernel

-- six_orbit_dags/type3m12e11q2r1.json.gz, graph 717, terminal 61; projection:R_one_six_1437.
noncomputable def r1297 : Entry :=
  ⟨⟨[63,199,234,285,325,331,632,678,736,820,856,964],[7,11,29,38,42,52,56,67,69,74,104,134,162,194,196,224,261,265,276,280,321,324,328,548,560,600,608,644,672,704,772,784,832]⟩,
   ⟨1631,646515536385,650290409985⟩⟩
theorem r1297_checked : check r1297 = true := by decide +kernel

-- six_orbit_dags/type3m12e11q2r1.json.gz, graph 717, terminal 62; projection:R_one_six_1438.
noncomputable def r1298 : Entry :=
  ⟨⟨[63,93,197,203,344,372,647,682,806,824,964,968],[7,11,29,38,42,52,56,69,73,84,88,131,133,138,193,196,200,280,292,304,324,328,336,518,546,552,642,644,648,772,776,800,960]⟩,
   ⟨1632,590395748865,590395748865⟩⟩
theorem r1298_checked : check r1298 = true := by decide +kernel

-- six_orbit_dags/type3m12e11q2r1.json.gz, graph 717, terminal 63; projection:R_one_six_1439.
noncomputable def r1299 : Entry :=
  ⟨⟨[63,157,197,203,327,362,456,692,806,824,920,964],[7,11,29,38,42,52,56,67,69,74,133,137,148,152,193,196,200,262,290,296,322,324,328,392,448,548,560,644,656,772,792,800,896]⟩,
   ⟨1633,654568600065,654568600065⟩⟩
theorem r1299_checked : check r1299 = true := by decide +kernel

-- six_orbit_dags/type3m12e11q2r1.json.gz, graph 717, terminal 66; projection:R_one_six_1487.
noncomputable def r1300 : Entry :=
  ⟨⟨[63,230,327,362,440,452,480,541,692,779,901,920],[7,11,29,38,42,52,56,70,98,164,176,196,224,259,261,266,296,322,324,352,388,408,416,448,517,521,532,536,644,656,769,776,896]⟩,
   ⟨1648,444685624080,444685624080⟩⟩
theorem r1300_checked : check r1300 = true := by decide +kernel

-- six_orbit_dags/type3m12e11q2r1.json.gz, graph 717, terminal 72; projection:R_one_six_1470.
noncomputable def r1301 : Entry :=
  ⟨⟨[63,157,199,331,358,449,452,696,810,820,905,916],[7,11,29,38,42,52,56,67,70,133,137,148,152,193,196,265,266,290,292,321,322,324,385,388,448,552,560,648,656,776,788,800,896]⟩,
   ⟨1638,654568600080,654568600080⟩⟩
theorem r1301_checked : check r1301 = true := by decide +kernel

-- six_orbit_dags/type3m12e12q2r1.json.gz, graph 718, terminal 2; gp:C001.
noncomputable def r1302 : Entry :=
  ⟨⟨[63,71,358,376,426,451,541,628,651,709,920,976],[7,11,29,38,42,52,56,67,69,70,100,112,131,138,193,280,290,296,322,336,352,386,392,448,517,521,532,536,580,592,641,648,704,912]⟩,
   ⟨1996,452990346000,577561174800⟩⟩
theorem r1302_checked : check r1302 = true := by decide +kernel

-- six_orbit_dags/type3m12e12q2r1.json.gz, graph 718, terminal 6; projection:R_one_six_1496.
noncomputable def r1303 : Entry :=
  ⟨⟨[63,230,248,391,426,452,541,628,779,837,920,976],[7,11,29,38,42,52,56,100,112,134,152,162,168,196,208,224,259,261,266,324,386,388,392,448,517,521,532,536,580,592,769,776,832,912]⟩,
   ⟨1650,444937285665,509110137090⟩⟩
theorem r1303_checked : check r1303 = true := by decide +kernel

-- six_orbit_dags/type3m12e12q3r1.json.gz, graph 719, terminal 0; projection:R_one_six_1499.
noncomputable def r1304 : Entry :=
  ⟨⟨[63,71,230,285,453,587,682,692,824,841,916,962],[7,11,29,38,42,52,56,67,69,70,162,164,194,196,261,265,276,280,321,388,448,522,552,560,578,585,642,660,672,776,784,832,896]⟩,
   ⟨1652,509104694100,444932825925⟩⟩
theorem r1304_checked : check r1304 = true := by decide +kernel

-- six_orbit_dags/type3m12e12q3r1.json.gz, graph 719, terminal 1; projection:R_one_six_1498.
noncomputable def r1305 : Entry :=
  ⟨⟨[63,71,157,203,436,453,618,728,806,824,838,976],[7,11,29,38,42,52,56,67,69,70,74,133,137,148,152,193,200,292,304,324,388,400,448,536,546,552,578,584,720,774,784,800,832]⟩,
   ⟨1651,654568588065,654568595715⟩⟩
theorem r1305_checked : check r1305 = true := by decide +kernel

-- six_orbit_dags/type3m12e12q3r1.json.gz, graph 719, terminal 4; projection:R_one_six_1500.
noncomputable def r1306 : Entry :=
  ⟨⟨[63,199,234,358,440,480,541,651,820,837,920,961],[7,11,29,38,42,52,56,69,70,98,131,138,168,193,194,224,292,304,324,352,408,416,448,517,521,532,536,641,648,772,784,833,896]⟩,
   ⟨1653,444682285140,444681172290⟩⟩
theorem r1306_checked : check r1306 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q1r1.json.gz, graph 721, terminal 77; projection:R_one_six_1501.
noncomputable def r1307 : Entry :=
  ⟨⟨[63,197,230,285,325,372,568,647,682,752,779,856,961],[7,11,29,38,42,52,56,69,100,112,133,134,162,193,196,224,261,265,276,280,321,324,336,515,522,536,552,560,592,641,642,672,704,769,776,832]⟩,
   ⟨1654,32621544225,509041910025⟩⟩
theorem r1307_checked : check r1307 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q1r1.json.gz, graph 721, terminal 78; projection:R_one_six_1505.
noncomputable def r1308 : Entry :=
  ⟨⟨[63,157,212,358,391,452,523,618,628,696,835,905,976],[7,11,29,38,42,52,56,84,98,100,133,137,148,152,196,208,259,262,322,324,385,388,448,515,521,522,552,560,578,592,608,648,656,769,832,896]⟩,
   ⟨1658,40670151525,577421649225⟩⟩
theorem r1308_checked : check r1308 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q1r1.json.gz, graph 721, terminal 79; projection:R_one_six_1508.
noncomputable def r1309 : Entry :=
  ⟨⟨[63,71,230,248,285,372,464,682,707,779,837,920,960],[7,11,29,38,42,52,56,67,69,70,100,112,152,162,168,194,208,224,261,265,276,280,324,336,400,448,515,522,577,642,648,704,769,776,832,896]⟩,
   ⟨1661,646512182100,650285950275⟩⟩
theorem r1309_checked : check r1309 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q1r1.json.gz, graph 721, terminal 80; projection:R_one_six_1510.
noncomputable def r1310 : Entry :=
  ⟨⟨[63,116,331,358,426,449,496,541,583,696,705,724,905],[7,11,29,38,42,52,56,67,70,84,100,112,168,176,193,208,265,266,290,321,322,352,385,392,416,448,517,521,532,536,577,580,641,648,656,704]⟩,
   ⟨1663,453241996065,581587706115⟩⟩
theorem r1310_checked : check r1310 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q1r1.json.gz, graph 721, terminal 151; projection:R_one_six_1502.
noncomputable def r1311 : Entry :=
  ⟨⟨[63,197,230,248,391,426,456,541,581,628,779,856,961],[7,11,29,38,42,52,56,69,88,100,112,133,134,162,168,193,196,200,224,259,266,328,385,386,392,448,517,521,532,536,577,580,592,769,776,832]⟩,
   ⟨1655,453241996065,581587706115⟩⟩
theorem r1311_checked : check r1311 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q1r1.json.gz, graph 721, terminal 152; projection:R_one_six_1506.
noncomputable def r1312 : Entry :=
  ⟨⟨[63,230,248,285,325,436,452,583,618,712,779,920,961],[7,11,29,38,42,52,56,69,70,98,104,152,164,176,196,200,224,261,265,276,280,321,324,388,400,448,515,522,577,578,584,648,704,769,776,896]⟩,
   ⟨1659,578064483105,521441386755⟩⟩
theorem r1312_checked : check r1312 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q1r1.json.gz, graph 721, terminal 153; projection:R_one_six_1509.
noncomputable def r1313 : Entry :=
  ⟨⟨[63,203,230,426,436,452,541,583,705,824,852,905,960],[7,11,29,38,42,52,56,67,70,137,138,162,164,193,194,196,276,296,304,324,388,392,416,448,517,521,532,536,577,580,641,704,776,784,832,896]⟩,
   ⟨1662,453242007585,581587710210⟩⟩
theorem r1313_checked : check r1313 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q1r1.json.gz, graph 721, terminal 154; projection:R_one_six_1511.
noncomputable def r1314 : Entry :=
  ⟨⟨[63,331,358,426,436,449,452,541,583,696,705,724,905],[7,11,29,38,42,52,56,67,70,148,168,176,193,196,265,266,290,292,321,322,324,385,388,392,416,448,517,521,532,536,577,580,641,648,656,704]⟩,
   ⟨1664,453242007585,581587710210⟩⟩
theorem r1314_checked : check r1314 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q1r1.json.gz, graph 721, terminal 157; projection:R_one_six_1504.
noncomputable def r1315 : Entry :=
  ⟨⟨[63,157,197,244,376,464,550,583,651,810,868,920,961],[7,11,29,38,42,52,56,69,100,112,133,137,148,152,193,196,208,280,296,336,352,400,448,515,518,522,546,548,577,580,641,648,776,800,832,896]⟩,
   ⟨1657,590144078625,590144086275⟩⟩
theorem r1315_checked : check r1315 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q1r1.json.gz, graph 721, terminal 159; projection:R_one_six_1503.
noncomputable def r1316 : Entry :=
  ⟨⟨[63,157,197,244,325,358,376,464,651,775,810,920,961],[7,11,29,38,42,52,56,69,100,112,133,137,148,152,193,196,208,261,262,280,290,296,321,324,336,352,400,448,515,522,641,648,769,770,776,896]⟩,
   ⟨1656,654568588065,654568595715⟩⟩
theorem r1316_checked : check r1316 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q1r1.json.gz, graph 721, terminal 162; projection:R_one_six_1507.
noncomputable def r1317 : Entry :=
  ⟨⟨[63,230,248,285,325,372,464,583,682,706,779,920,961],[7,11,29,38,42,52,56,69,70,100,112,152,162,168,194,208,224,261,265,276,280,321,324,336,400,448,515,522,577,578,642,648,704,769,776,896]⟩,
   ⟨1660,578064483105,521441386755⟩⟩
theorem r1317_checked : check r1317 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q2r1.json.gz, graph 722, terminal 8; projection:R_one_six_1521.
noncomputable def r1318 : Entry :=
  ⟨⟨[63,71,139,285,325,440,457,614,682,692,707,852,976],[7,11,29,38,42,52,56,67,69,70,131,137,138,168,176,193,261,265,276,280,321,324,392,400,448,532,546,548,578,580,642,656,672,704,848]⟩,
   ⟨1674,646515524385,650290405635⟩⟩
theorem r1318_checked : check r1318 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q2r1.json.gz, graph 722, terminal 15; projection:R_one_six_1520.
noncomputable def r1319 : Entry :=
  ⟨⟨[63,71,331,358,426,436,456,541,581,696,713,852,976],[7,11,29,38,42,52,56,67,69,70,73,168,176,200,266,276,290,292,322,324,328,392,400,416,448,517,521,532,536,577,580,648,656,704,848]⟩,
   ⟨1673,453241996065,581587706115⟩⟩
theorem r1319_checked : check r1319 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q2r1.json.gz, graph 722, terminal 16; projection:R_one_six_1526.
noncomputable def r1320 : Entry :=
  ⟨⟨[63,71,116,157,197,331,358,696,724,810,880,905,961],[7,11,29,38,42,52,56,67,69,70,84,100,112,133,137,148,152,193,196,265,266,290,321,322,352,552,560,592,648,656,704,776,800,832,897]⟩,
   ⟨1679,590144078625,590144086275⟩⟩
theorem r1320_checked : check r1320 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q2r1.json.gz, graph 722, terminal 17; projection:R_one_six_1527.
noncomputable def r1321 : Entry :=
  ⟨⟨[63,71,203,230,426,436,452,541,581,824,852,905,961],[7,11,29,38,42,52,56,67,69,70,137,138,162,164,193,194,196,276,296,304,324,388,392,416,448,517,521,532,536,577,580,776,784,832,897]⟩,
   ⟨1680,449215475745,517163200770⟩⟩
theorem r1321_checked : check r1321 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q2r1.json.gz, graph 722, terminal 18; projection:R_one_six_1522.
noncomputable def r1322 : Entry :=
  ⟨⟨[63,71,166,203,285,325,426,457,692,710,824,852,992],[7,11,29,38,42,52,56,67,69,70,134,138,162,164,194,201,261,265,276,280,296,321,324,392,416,448,532,560,580,644,672,704,784,800,832]⟩,
   ⟨1675,646515535905,650290409730⟩⟩
theorem r1322_checked : check r1322 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q2r1.json.gz, graph 722, terminal 22; projection:R_one_six_1523.
noncomputable def r1323 : Entry :=
  ⟨⟨[63,71,157,197,358,468,587,696,713,810,820,912,962],[7,11,29,38,42,52,56,67,69,70,133,137,148,152,193,196,276,290,292,322,324,400,448,522,552,560,578,585,648,656,704,770,784,800,896]⟩,
   ⟨1676,590144090145,590144090370⟩⟩
theorem r1323_checked : check r1323 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q2r1.json.gz, graph 722, terminal 25; projection:R_one_six_1512.
noncomputable def r1324 : Entry :=
  ⟨⟨[63,71,157,197,244,395,449,614,632,810,835,920,976],[7,11,29,38,42,52,56,67,69,70,100,112,133,137,148,152,193,196,208,259,266,321,385,392,448,536,546,552,578,592,608,770,776,832,912]⟩,
   ⟨1665,654568600065,654568600065⟩⟩
theorem r1324_checked : check r1324 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q2r1.json.gz, graph 722, terminal 26; projection:R_one_six_1513.
noncomputable def r1325 : Entry :=
  ⟨⟨[63,71,157,197,395,440,449,614,724,810,820,835,976],[7,11,29,38,42,52,56,67,69,70,133,137,148,152,193,196,259,266,296,304,321,385,392,400,448,532,546,548,578,580,720,770,784,800,832]⟩,
   ⟨1666,654568600065,654568600065⟩⟩
theorem r1325_checked : check r1325 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q2r1.json.gz, graph 722, terminal 27; projection:R_one_six_1524.
noncomputable def r1326 : Entry :=
  ⟨⟨[63,71,157,197,244,358,376,464,651,810,835,920,961],[7,11,29,38,42,52,56,67,69,70,100,112,133,137,148,152,193,196,208,280,290,296,322,336,352,400,448,515,522,641,648,770,776,833,896]⟩,
   ⟨1677,654568588065,654568595715⟩⟩
theorem r1326_checked : check r1326 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q2r1.json.gz, graph 722, terminal 28; projection:R_one_six_1525.
noncomputable def r1327 : Entry :=
  ⟨⟨[63,93,135,197,331,376,678,724,810,820,848,899,961],[7,11,29,38,42,52,56,69,73,84,88,131,133,134,193,196,259,266,296,304,321,328,336,532,546,548,592,642,644,704,770,784,800,832,897]⟩,
   ⟨1678,590395748385,590395748610⟩⟩
theorem r1327_checked : check r1327 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q2r1.json.gz, graph 722, terminal 30; projection:R_one_six_1517.
noncomputable def r1328 : Entry :=
  ⟨⟨[63,71,184,234,285,325,395,451,614,692,852,920,992],[7,11,29,38,42,52,56,67,69,70,98,138,152,168,176,194,224,261,265,276,280,321,324,387,392,448,532,548,580,608,656,672,784,832,896]⟩,
   ⟨1670,646515535905,650290409730⟩⟩
theorem r1328_checked : check r1328 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q2r1.json.gz, graph 722, terminal 31; projection:R_one_six_1518.
noncomputable def r1329 : Entry :=
  ⟨⟨[63,71,184,234,285,325,395,451,614,752,820,920,964],[7,11,29,38,42,52,56,67,69,70,98,138,152,168,176,194,224,261,265,276,280,321,324,387,392,448,548,560,580,608,656,704,772,784,896]⟩,
   ⟨1671,646515535905,650290409730⟩⟩
theorem r1329_checked : check r1329 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q2r1.json.gz, graph 722, terminal 33; projection:R_one_six_1519.
noncomputable def r1330 : Entry :=
  ⟨⟨[63,71,234,358,376,456,541,581,651,707,820,920,964],[7,11,29,38,42,52,56,67,69,70,98,104,138,194,200,280,292,304,324,328,352,392,448,517,521,532,536,577,580,643,648,704,772,784,896]⟩,
   ⟨1672,453242007585,581587710210⟩⟩
theorem r1330_checked : check r1330 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q2r1.json.gz, graph 722, terminal 37; projection:R_one_six_1514.
noncomputable def r1331 : Entry :=
  ⟨⟨[63,71,116,157,197,376,468,614,651,707,810,920,992],[7,11,29,38,42,52,56,67,69,70,84,100,112,133,137,148,152,193,196,280,296,336,352,400,448,522,546,578,608,643,648,704,776,800,896]⟩,
   ⟨1667,590144078625,590144086275⟩⟩
theorem r1331_checked : check r1331 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q2r1.json.gz, graph 722, terminal 38; projection:R_one_six_1515.
noncomputable def r1332 : Entry :=
  ⟨⟨[63,71,116,157,197,440,468,614,651,707,810,880,968],[7,11,29,38,42,52,56,67,69,70,84,100,112,133,137,148,152,193,196,296,304,336,392,400,448,522,546,578,608,643,648,704,776,800,832]⟩,
   ⟨1668,590144078625,590144086275⟩⟩
theorem r1332_checked : check r1332 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q2r1.json.gz, graph 722, terminal 40; projection:R_one_six_1516.
noncomputable def r1333 : Entry :=
  ⟨⟨[63,71,358,426,436,452,541,581,696,724,779,835,968],[7,11,29,38,42,52,56,67,69,70,148,168,176,196,266,290,292,322,324,388,392,416,448,517,521,532,536,577,580,648,656,704,771,776,832]⟩,
   ⟨1669,449215475745,517163200770⟩⟩
theorem r1333_checked : check r1333 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q2r1.json.gz, graph 722, terminal 71; projection:R_one_six_1660.
noncomputable def r1334 : Entry :=
  ⟨⟨[63,71,75,180,230,362,457,496,541,709,824,905,916],[7,11,29,38,42,52,56,67,69,70,73,74,98,148,164,176,193,196,224,296,304,328,352,393,400,448,517,521,532,536,641,644,776,784,896]⟩,
   ⟨1802,444681167700,444681167700⟩⟩
theorem r1334_checked : check r1334 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q2r1.json.gz, graph 722, terminal 77; projection:R_one_six_1655.
noncomputable def r1335 : Entry :=
  ⟨⟨[63,75,180,195,230,362,457,496,541,647,824,905,916],[7,11,29,38,42,52,56,67,73,74,98,131,134,148,164,176,193,194,224,296,304,328,352,393,400,448,517,521,532,536,641,644,776,784,896]⟩,
   ⟨1797,444681167700,444681167700⟩⟩
theorem r1335_checked : check r1335 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q2r1.json.gz, graph 722, terminal 79; projection:R_one_six_1640.
noncomputable def r1336 : Entry :=
  ⟨⟨[63,75,195,230,362,372,452,457,541,647,824,905,916],[7,11,29,38,42,52,56,67,73,74,98,100,131,134,193,194,196,276,296,304,324,328,352,388,393,448,517,521,532,536,641,644,776,784,896]⟩,
   ⟨1782,444681167700,444681167700⟩⟩
theorem r1336_checked : check r1336 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q2r1.json.gz, graph 722, terminal 80; projection:R_one_six_1542.
noncomputable def r1337 : Entry :=
  ⟨⟨[63,75,157,362,372,404,440,579,614,647,841,905,964],[7,11,29,38,42,52,56,67,73,74,98,100,133,137,148,152,276,296,304,324,328,352,388,392,400,515,518,577,578,580,641,644,777,832,896]⟩,
   ⟨1695,650284970580,646511080005⟩⟩
theorem r1337_checked : check r1337 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q2r1.json.gz, graph 722, terminal 82; projection:R_one_six_1667.
noncomputable def r1338 : Entry :=
  ⟨⟨[63,75,135,195,362,422,440,541,692,709,841,920,962],[7,11,29,38,42,52,56,67,73,74,131,133,134,164,176,193,194,290,296,322,328,386,408,416,517,521,532,536,577,644,656,704,776,832,896]⟩,
   ⟨1809,448708816980,448707704130⟩⟩
theorem r1338_checked : check r1338 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q2r1.json.gz, graph 722, terminal 84; projection:R_one_six_1668.
noncomputable def r1339 : Entry :=
  ⟨⟨[63,71,75,198,362,422,440,541,692,709,841,920,962],[7,11,29,38,42,52,56,67,69,70,73,74,134,164,176,194,196,290,296,322,328,386,408,416,517,521,532,536,577,644,656,704,776,832,896]⟩,
   ⟨1810,448708816980,448707704130⟩⟩
theorem r1339_checked : check r1339 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q2r1.json.gz, graph 722, terminal 85; projection:R_one_six_1589.
noncomputable def r1340 : Entry :=
  ⟨⟨[63,71,75,230,285,404,453,682,692,714,824,841,976],[7,11,29,38,42,52,56,67,69,70,73,74,148,162,164,194,196,261,265,276,280,321,388,400,448,552,560,584,650,656,672,704,776,784,832]⟩,
   ⟨1742,577556722260,452985893460⟩⟩
theorem r1340_checked : check r1340 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q2r1.json.gz, graph 722, terminal 90; projection:R_one_six_1554.
noncomputable def r1341 : Entry :=
  ⟨⟨[63,75,157,197,327,436,452,618,713,806,824,920,962],[7,11,29,38,42,52,56,67,69,73,74,133,137,148,152,193,196,262,292,304,322,324,388,400,448,546,552,578,584,648,704,770,792,800,896]⟩,
   ⟨1707,654568600065,654568600065⟩⟩
theorem r1341_checked : check r1341 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q2r1.json.gz, graph 722, terminal 91; projection:R_one_six_1556.
noncomputable def r1342 : Entry :=
  ⟨⟨[63,75,180,199,285,325,440,468,618,678,841,936,962],[7,11,29,38,42,52,56,67,69,73,74,134,148,164,176,194,196,261,265,276,280,321,324,400,424,448,546,552,578,584,642,672,776,832,896]⟩,
   ⟨1709,646515536385,650290409985⟩⟩
theorem r1342_checked : check r1342 = true := by decide +kernel

-- six_orbit_dags/type3m13e11q2r1.json.gz, graph 722, terminal 92; projection:R_one_six_1555.
noncomputable def r1343 : Entry :=
  ⟨⟨[63,75,180,199,285,325,468,618,678,696,841,920,962],[7,11,29,38,42,52,56,67,69,73,74,134,148,164,176,194,196,261,265,276,280,321,324,400,448,546,552,578,584,642,664,672,776,832,896]⟩,
   ⟨1708,646515535905,650290409730⟩⟩
theorem r1343_checked : check r1343 = true := by decide +kernel

#print axioms r1280_checked

end Nonrational.OldTerminalMatches.M020
