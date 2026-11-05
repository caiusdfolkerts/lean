module
prelude
public import InducedTerminalMatches.Basic

@[expose] public section

/-! Exact full-boundary matches, batch 0. Both facet and polygon
families are checked in both directions after the recorded permutation. -/

namespace Nonrational.OldTerminalMatches.M000
open Nonrational.InducedTerminalMatches
set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- seven_dags/pure_064.json, graph 98, terminal 2; gp:SevenSurvivor.
noncomputable def r0000 : Entry :=
  ⟨⟨[127,155,277,358,391,696,714,820,872,913,962],[7,21,27,52,56,74,102,104,131,138,145,152,261,262,273,276,292,322,352,385,386,552,560,584,648,656,706,784,800,832,896]⟩,
   ⟨2040,590395748880,590395748880⟩⟩
theorem r0000_checked : check r0000 = true := by decide +kernel

-- seven_dags/pure_064.json, graph 98, terminal 4; gp:SevenSurvivor.
noncomputable def r0001 : Entry :=
  ⟨⟨[127,155,232,358,458,661,696,775,820,899,992],[7,21,27,52,56,74,102,104,131,138,145,152,168,200,224,262,292,322,352,386,448,517,532,560,641,656,672,771,772,800,896]⟩,
   ⟨2040,582241035030,521843057430⟩⟩
theorem r0001_checked : check r0001 = true := by decide +kernel

-- seven_dags/pure_064.json, graph 98, terminal 8; gp:SevenSurvivor.
noncomputable def r0002 : Entry :=
  ⟨⟨[127,155,440,458,533,614,647,820,872,913,962],[7,21,27,52,56,74,102,104,131,138,145,152,296,304,328,392,400,450,517,518,529,532,548,578,608,641,642,784,800,832,896]⟩,
   ⟨2040,654820258320,654820258320⟩⟩
theorem r0002_checked : check r0002 = true := by decide +kernel

-- seven_dags/pure_064.json, graph 98, terminal 10; gp:SevenSurvivor.
noncomputable def r0003 : Entry :=
  ⟨⟨[127,155,232,405,440,614,714,775,820,899,992],[7,21,27,52,56,74,102,104,131,138,145,152,168,200,224,261,276,304,385,400,416,518,548,578,608,642,704,771,772,800,896]⟩,
   ⟨2040,517816525590,517816525590⟩⟩
theorem r0003_checked : check r0003 = true := by decide +kernel

-- seven_dags/pure_064.json, graph 98, terminal 14; gp:SevenSurvivor.
noncomputable def r0004 : Entry :=
  ⟨⟨[127,149,230,283,391,692,744,824,842,913,962],[7,21,27,52,56,74,102,104,133,134,145,148,164,194,224,259,266,273,280,385,386,552,560,584,656,672,704,776,784,834,896]⟩,
   ⟨2040,582342685200,521944707600⟩⟩
theorem r0004_checked : check r0004 = true := by decide +kernel

-- seven_dags/pure_064.json, graph 98, terminal 16; gp:SevenSurvivor.
noncomputable def r0005 : Entry :=
  ⟨⟨[127,230,283,360,458,647,692,789,824,899,992],[7,21,27,52,56,74,102,104,134,164,194,224,259,266,273,280,296,328,352,386,448,517,532,560,643,644,672,769,784,800,896]⟩,
   ⟨2040,590294098710,590294098710⟩⟩
theorem r0005_checked : check r0005 = true := by decide +kernel

-- seven_dags/pure_064.json, graph 98, terminal 18; gp:SevenSurvivor.
noncomputable def r0006 : Entry :=
  ⟨⟨[127,283,360,405,440,614,647,692,842,899,992],[7,21,27,52,56,74,102,104,133,148,176,259,266,273,280,296,328,352,385,400,416,518,548,578,608,643,644,672,770,832,896]⟩,
   ⟨2040,521843057430,582241035030⟩⟩
theorem r0006_checked : check r0006 = true := by decide +kernel

-- seven_dags/pure_064.json, graph 98, terminal 22; gp:SevenSurvivor.
noncomputable def r0007 : Entry :=
  ⟨⟨[127,283,440,458,533,614,692,744,775,913,962],[7,21,27,52,56,74,102,104,168,176,200,259,266,273,280,392,400,450,517,518,529,532,548,578,608,656,672,704,769,770,896]⟩,
   ⟨2040,650793726480,650793726480⟩⟩
theorem r0007_checked : check r0007 = true := by decide +kernel

-- seven_dags/pure_064.json, graph 98, terminal 24; gp:SevenSurvivor.
noncomputable def r0008 : Entry :=
  ⟨⟨[127,230,391,436,539,616,714,789,824,899,992],[7,21,27,52,56,74,102,104,134,164,194,224,261,276,304,387,388,416,515,522,529,536,552,584,608,642,704,769,784,800,896]⟩,
   ⟨2040,654718608150,654718608150⟩⟩
theorem r0008_checked : check r0008 = true := by decide +kernel

-- seven_dags/pure_064.json, graph 98, terminal 28; gp:SevenSurvivor.
noncomputable def r0009 : Entry :=
  ⟨⟨[127,149,230,436,488,539,647,824,842,913,962],[7,21,27,52,56,74,102,104,133,134,145,148,164,194,224,296,304,328,400,416,448,515,522,529,536,641,642,776,784,834,896]⟩,
   ⟨2040,517918175760,517918175760⟩⟩
theorem r0009_checked : check r0009 = true := by decide +kernel

-- seven_dags/pure_064.json, graph 98, terminal 30; gp:SevenSurvivor.
noncomputable def r0010 : Entry :=
  ⟨⟨[127,358,391,436,539,616,661,696,842,899,992],[7,21,27,52,56,74,102,104,133,148,176,262,292,322,352,387,388,416,515,522,529,536,552,584,608,641,656,672,770,832,896]⟩,
   ⟨2040,650692076310,650692076310⟩⟩
theorem r0010_checked : check r0010 = true := by decide +kernel

-- seven_dags/pure_064.json, graph 98, terminal 34; gp:SevenSurvivor.
noncomputable def r0011 : Entry :=
  ⟨⟨[127,277,358,436,488,539,696,714,775,913,962],[7,21,27,52,56,74,102,104,168,176,200,261,262,273,276,292,322,352,400,416,448,515,522,529,536,648,656,706,769,770,896]⟩,
   ⟨2040,521944707600,582342685200⟩⟩
theorem r0011_checked : check r0011 = true := by decide +kernel

-- small_orbit_dags/row07_m12_e10_q0.json.gz, graph 108, terminal 0; projection:P0_000.
noncomputable def r0012 : Entry :=
  ⟨⟨[31,43,83,227,301,426,598,721,782,789,929,962],[11,13,14,19,21,22,35,41,42,67,81,82,161,162,193,194,261,266,268,289,296,386,416,518,529,532,578,592,641,704,769,770,772,896]⟩,
   ⟨0,345797891190,305220707640⟩⟩
theorem r0012_checked : check r0012 = true := by decide +kernel

-- small_orbit_dags/row07_m12_e10_q0.json.gz, graph 108, terminal 24; projection:P0_000.
noncomputable def r0013 : Entry :=
  ⟨⟨[31,43,115,225,302,425,566,597,752,781,932,961],[11,13,14,19,21,22,35,38,41,42,50,81,97,112,161,193,224,265,268,292,296,385,416,517,532,548,560,577,592,672,704,769,772,896]⟩,
   ⟨0,378921033750,448028504850⟩⟩
theorem r0013_checked : check r0013 = true := by decide +kernel

-- small_orbit_dags/row07_m12_e10_q0.json.gz, graph 108, terminal 67; projection:P0_000.
noncomputable def r0014 : Entry :=
  ⟨⟨[31,105,110,171,182,403,417,589,628,789,865,944],[11,13,14,19,21,22,38,41,42,52,73,76,97,100,104,131,146,161,162,176,273,289,385,400,416,517,532,560,577,580,608,769,784,800]⟩,
   ⟨0,558671893830,246157502580⟩⟩
theorem r0014_checked : check r0014 = true := by decide +kernel

-- small_orbit_dags/row08_m12_e10_q1.json.gz, graph 109, terminal 9; projection:P0_045.
noncomputable def r0015 : Entry :=
  ⟨⟨[31,43,51,109,181,334,406,618,690,868,932,962],[11,13,14,19,21,22,35,37,41,42,49,50,74,76,100,104,146,148,164,176,262,322,324,386,388,546,578,608,642,672,804,832,896]⟩,
   ⟨1,152018950020,279833512245⟩⟩
theorem r0015_checked : check r0015 = true := by decide +kernel

-- small_orbit_dags/row08_m12_e10_q1.json.gz, graph 109, terminal 43; projection:P0_045.
noncomputable def r0016 : Entry :=
  ⟨⟨[31,43,99,211,405,558,617,738,781,790,914,961],[11,13,14,19,21,22,35,41,42,67,97,98,145,146,193,194,261,276,385,400,518,521,524,546,552,577,608,642,704,769,772,786,896]⟩,
   ⟨1,495687177480,414852678705⟩⟩
theorem r0016_checked : check r0016 = true := by decide +kernel

-- small_orbit_dags/row08_m12_e10_q1.json.gz, graph 109, terminal 88; projection:P0_045.
noncomputable def r0017 : Entry :=
  ⟨⟨[31,43,105,110,205,307,481,566,740,789,901,944],[11,13,14,19,21,22,35,38,41,42,50,73,76,97,100,104,133,193,196,224,273,289,304,385,416,532,548,560,644,672,773,784,896]⟩,
   ⟨1,216518706960,434450438160⟩⟩
theorem r0017_checked : check r0017 = true := by decide +kernel

-- small_orbit_dags/row08_m12_e10_q1.json.gz, graph 109, terminal 207; projection:P0_045.
noncomputable def r0018 : Entry :=
  ⟨⟨[31,203,225,339,353,590,598,653,744,789,880,929],[11,13,14,19,21,22,67,74,82,97,137,161,193,200,224,273,289,321,336,352,517,524,532,582,584,592,608,641,648,672,769,784,800]⟩,
   ⟨1,519964087080,552242323830⟩⟩
theorem r0018_checked : check r0018 = true := by decide +kernel

-- small_orbit_dags/row08_m12_e10_q1.json.gz, graph 109, terminal 231; projection:P0_045.
noncomputable def r0019 : Entry :=
  ⟨⟨[31,105,110,173,225,405,484,587,598,787,852,961],[11,13,14,19,21,22,41,44,70,73,74,97,100,104,133,161,164,193,224,273,276,324,385,388,448,515,530,577,578,596,769,784,832]⟩,
   ⟨1,165629073240,481708820790⟩⟩
theorem r0019_checked : check r0019 = true := by decide +kernel

-- small_orbit_dags/row10_m12_e11_q1.json.gz, graph 111, terminal 4; projection:R_m12e11q1_0002.
noncomputable def r0020 : Entry :=
  ⟨⟨[31,43,115,173,234,398,466,565,740,790,880,964],[11,13,14,19,21,22,35,37,41,42,49,82,98,112,138,140,164,168,194,224,262,274,336,386,388,448,532,548,560,608,708,772,784,832]⟩,
   ⟨141,233093212545,143217103620⟩⟩
theorem r0020_checked : check r0020 = true := by decide +kernel

-- small_orbit_dags/row10_m12_e11_q1.json.gz, graph 111, terminal 5; projection:R_m12e11q1_0002.
noncomputable def r0021 : Entry :=
  ⟨⟨[31,43,109,179,234,309,496,590,662,868,916,962],[11,13,14,19,21,22,35,37,41,42,49,74,76,100,104,146,162,176,194,224,276,292,304,352,400,448,518,578,580,642,660,772,832,896]⟩,
   ⟨141,233279068530,159324082230⟩⟩
theorem r0021_checked : check r0021 = true := by decide +kernel

-- small_orbit_dags/row10_m12_e11_q1.json.gz, graph 111, terminal 6; projection:R_m12e11q1_0002.
noncomputable def r0022 : Entry :=
  ⟨⟨[31,43,115,213,406,557,618,737,782,850,901,976],[11,13,14,19,21,22,35,41,42,81,82,97,98,133,148,193,208,262,274,388,400,517,522,524,545,552,578,608,641,704,770,772,848,896]⟩,
   ⟨141,633040343160,618865788210⟩⟩
theorem r0022_checked : check r0022 = true := by decide +kernel

-- small_orbit_dags/row10_m12_e11_q1.json.gz, graph 111, terminal 7; projection:R_m12e11q1_0002.
noncomputable def r0023 : Entry :=
  ⟨⟨[31,43,115,213,466,558,617,653,790,866,916,961],[11,13,14,19,21,22,35,41,42,81,82,97,98,133,148,193,208,274,322,400,448,518,521,524,546,552,577,608,641,644,770,788,832,896]⟩,
   ⟨141,632972190840,618865525590⟩⟩
theorem r0023_checked : check r0023 = true := by decide +kernel

-- small_orbit_dags/row10_m12_e11_q1.json.gz, graph 111, terminal 16; projection:R_m12e11q1_0002.
noncomputable def r0024 : Entry :=
  ⟨⟨[31,105,110,173,331,403,481,661,740,790,838,976],[11,13,14,19,21,22,41,44,70,73,74,97,100,104,133,145,161,164,224,259,274,321,322,385,400,448,532,580,644,656,704,774,784,832]⟩,
   ⟨141,227752159560,139125166935⟩⟩
theorem r0024_checked : check r0024 = true := by decide +kernel

-- small_orbit_dags/row10_m12_e11_q1.json.gz, graph 111, terminal 18; projection:R_m12e11q1_0002.
noncomputable def r0025 : Entry :=
  ⟨⟨[31,171,211,225,398,597,617,752,781,790,914,936],[11,13,14,19,21,22,41,81,97,131,138,146,161,168,193,208,224,262,268,386,392,517,521,532,552,577,592,608,656,672,772,776,786,896]⟩,
   ⟨141,633274107480,620389238355⟩⟩
theorem r0025_checked : check r0025 = true := by decide +kernel

-- small_orbit_dags/row10_m12_e11_q1.json.gz, graph 111, terminal 20; projection:R_m12e11q1_0002.
noncomputable def r0026 : Entry :=
  ⟨⟨[31,171,232,403,458,557,661,737,782,790,872,976],[11,13,14,19,21,22,41,104,131,138,145,161,168,200,224,266,274,328,386,400,448,517,524,532,545,552,608,641,656,704,774,776,784,832]⟩,
   ⟨141,637837669200,649414059600⟩⟩
theorem r0026_checked : check r0026 = true := by decide +kernel

-- small_orbit_dags/row10_m12_e11_q1.json.gz, graph 111, terminal 22; projection:R_m12e11q1_0002.
noncomputable def r0027 : Entry :=
  ⟨⟨[31,109,213,232,302,484,659,713,779,790,916,936],[11,13,14,19,21,22,44,69,73,100,104,145,148,168,193,196,200,224,262,266,292,296,388,416,515,521,530,641,648,656,770,776,788,896]⟩,
   ⟨141,362675407200,152229660000⟩⟩
theorem r0027_checked : check r0027 = true := by decide +kernel

-- small_orbit_dags/row10_m12_e11_q1.json.gz, graph 111, terminal 25; projection:R_m12e11q1_0002.
noncomputable def r0028 : Entry :=
  ⟨⟨[31,105,110,203,301,405,481,598,659,868,916,962],[11,13,14,19,21,22,41,44,70,73,74,97,100,104,131,145,193,194,261,289,292,352,385,404,448,530,532,578,580,642,656,772,832,896]⟩,
   ⟨141,430975424775,163367634225⟩⟩
theorem r0028_checked : check r0028 = true := by decide +kernel

-- small_orbit_dags/row13_m12_e12_q2.json.gz, graph 114, terminal 0; gp:C009.
noncomputable def r0029 : Entry :=
  ⟨⟨[31,109,181,334,484,563,617,662,752,779,902,968],[11,13,14,19,21,22,37,49,76,100,105,148,164,176,224,262,266,324,328,388,448,515,521,530,545,560,584,608,646,656,704,770,776,896]⟩,
   ⟨2004,500390241795,376116347745⟩⟩
theorem r0029_checked : check r0029 = true := by decide +kernel

-- small_orbit_dags/row13_m12_e12_q2.json.gz, graph 114, terminal 2; gp:C010.
noncomputable def r0030 : Entry :=
  ⟨⟨[31,174,205,310,341,484,555,595,713,818,936,976],[11,13,14,19,21,22,38,42,69,81,140,164,168,196,201,276,292,306,324,336,416,448,515,521,530,546,552,577,592,648,704,784,800,896]⟩,
   ⟨2005,576938186640,108053025840⟩⟩
theorem r0030_checked : check r0030 = true := by decide +kernel

-- small_orbit_dags/row13_m12_e12_q2.json.gz, graph 114, terminal 3; gp:C009.
noncomputable def r0031 : Entry :=
  ⟨⟨[31,174,205,341,484,555,566,595,713,820,936,976],[11,13,14,19,21,22,38,42,69,81,140,164,168,196,201,276,292,324,336,416,448,515,521,530,546,552,564,577,592,648,704,784,800,896]⟩,
   ⟨2004,504985818690,504969125940⟩⟩
theorem r0031_checked : check r0031 = true := by decide +kernel

-- small_orbit_dags/row15_m13_e10_q0.json.gz, graph 116, terminal 0; projection:P0_002.
noncomputable def r0032 : Entry :=
  ⟨⟨[31,43,83,105,227,341,466,558,589,744,790,930,964],[11,13,14,19,21,22,35,41,42,67,69,73,81,82,97,104,162,194,224,274,276,324,336,386,448,518,524,546,552,580,584,672,704,770,772,896]⟩,
   ⟨4,26176870290,95163859065⟩⟩
theorem r0032_checked : check r0032 = true := by decide +kernel

-- small_orbit_dags/row15_m13_e10_q0.json.gz, graph 116, terminal 4; projection:P0_004.
noncomputable def r0033 : Entry :=
  ⟨⟨[31,43,83,173,309,355,420,426,598,654,849,916,962],[11,13,14,19,21,22,35,37,41,42,67,81,82,138,140,164,168,273,276,289,290,292,321,322,386,388,416,518,532,578,592,642,644,784,832,896]⟩,
   ⟨6,516240445590,105500669490⟩⟩
theorem r0033_checked : check r0033 = true := by decide +kernel

-- small_orbit_dags/row15_m13_e10_q0.json.gz, graph 116, terminal 5; projection:P0_004.
noncomputable def r0034 : Entry :=
  ⟨⟨[31,43,83,174,333,355,396,425,597,662,850,930,964],[11,13,14,19,21,22,35,41,42,67,69,81,82,134,140,162,168,265,268,289,290,321,322,324,388,392,416,530,532,580,592,642,644,770,832,896]⟩,
   ⟨6,481909954710,79728899160⟩⟩
theorem r0034_checked : check r0034 = true := by decide +kernel

-- small_orbit_dags/row15_m13_e10_q0.json.gz, graph 116, terminal 6; projection:P0_005.
noncomputable def r0035 : Entry :=
  ⟨⟨[31,43,83,141,213,302,406,611,713,722,809,908,930],[11,13,14,19,21,22,35,41,42,67,81,82,133,137,140,146,148,193,208,262,268,290,296,386,388,521,545,546,577,578,642,648,704,776,800,896]⟩,
   ⟨7,27936380055,98921760105⟩⟩
theorem r0035_checked : check r0035 = true := by decide +kernel

-- small_orbit_dags/row15_m13_e10_q0.json.gz, graph 116, terminal 8; projection:P0_005.
noncomputable def r0036 : Entry :=
  ⟨⟨[31,43,83,227,309,342,417,465,557,682,782,932,962],[11,13,14,19,21,22,35,37,41,42,67,81,82,161,162,193,194,262,273,276,289,292,322,336,385,416,448,522,524,548,552,642,672,770,772,896]⟩,
   ⟨7,447805989015,103235937090⟩⟩
theorem r0036_checked : check r0036 = true := by decide +kernel

-- small_orbit_dags/row15_m13_e10_q0.json.gz, graph 116, terminal 13; projection:R_m13e10q0_0029.
noncomputable def r0037 : Entry :=
  ⟨⟨[31,43,51,242,406,426,480,557,625,782,789,872,976],[11,13,14,19,21,22,35,41,42,49,50,112,146,162,208,224,262,266,276,296,352,386,400,416,448,517,524,529,545,552,592,608,772,776,784,832]⟩,
   ⟨145,38964573780,568312477305⟩⟩
theorem r0037_checked : check r0037 = true := by decide +kernel

-- small_orbit_dags/row15_m13_e10_q0.json.gz, graph 116, terminal 16; projection:P0_008.
noncomputable def r0038 : Entry :=
  ⟨⟨[31,43,51,242,342,369,480,557,682,782,789,929,962],[11,13,14,19,21,22,35,41,42,49,50,82,112,162,194,224,262,273,276,289,322,336,352,416,448,517,522,524,545,552,642,672,769,770,772,896]⟩,
   ⟨10,34686117525,104455234425⟩⟩
theorem r0038_checked : check r0038 = true := by decide +kernel

-- small_orbit_dags/row15_m13_e10_q0.json.gz, graph 116, terminal 21; projection:P0_007.
noncomputable def r0039 : Entry :=
  ⟨⟨[31,43,51,214,398,434,452,557,597,810,817,844,976],[11,13,14,19,21,22,35,41,42,49,50,84,134,146,196,208,266,268,290,304,324,386,388,400,448,517,524,529,545,552,580,592,776,784,800,832]⟩,
   ⟨9,38961363045,559436609145⟩⟩
theorem r0039_checked : check r0039 = true := by decide +kernel

-- small_orbit_dags/row15_m13_e10_q0.json.gz, graph 116, terminal 24; projection:R_m13e10q0_0028.
noncomputable def r0040 : Entry :=
  ⟨⟨[31,43,51,214,341,370,452,557,654,810,817,901,962],[11,13,14,19,21,22,35,41,42,49,50,82,84,134,194,196,261,273,290,304,322,324,336,388,448,517,522,524,545,552,642,644,769,770,800,896]⟩,
   ⟨144,34684020630,103621616505⟩⟩
theorem r0040_checked : check r0040 = true := by decide +kernel

-- small_orbit_dags/row15_m13_e10_q0.json.gz, graph 116, terminal 29; projection:P0_001.
noncomputable def r0041 : Entry :=
  ⟨⟨[31,43,99,206,211,406,452,557,618,625,789,844,976],[11,13,14,19,21,22,35,41,42,67,74,76,81,97,98,134,146,194,196,208,276,324,388,400,448,517,524,529,545,552,584,592,608,772,784,832]⟩,
   ⟨3,490049910870,423324104820⟩⟩
theorem r0041_checked : check r0041 = true := by decide +kernel

-- small_orbit_dags/row15_m13_e10_q0.json.gz, graph 116, terminal 33; projection:R_m13e10q0_0020.
noncomputable def r0042 : Entry :=
  ⟨⟨[31,51,77,163,203,310,398,597,716,737,817,916,930],[11,13,14,19,21,22,35,49,50,69,73,76,131,138,140,161,162,193,200,262,276,290,304,386,388,529,532,545,577,580,644,672,704,784,800,896]⟩,
   ⟨143,27955239255,167639336505⟩⟩
theorem r0042_checked : check r0042 = true := by decide +kernel

-- small_orbit_dags/row15_m13_e10_q0.json.gz, graph 116, terminal 38; projection:R_m13e10q0_0028.
noncomputable def r0043 : Entry :=
  ⟨⟨[31,43,214,291,309,339,557,654,692,720,810,880,962],[11,13,14,19,21,22,35,37,41,42,52,82,134,148,194,208,259,273,289,290,304,322,336,522,524,548,552,560,592,642,644,656,704,770,800,832]⟩,
   ⟨144,498541797525,88399700850⟩⟩
theorem r0043_checked : check r0043 = true := by decide +kernel

-- small_orbit_dags/row15_m13_e10_q0.json.gz, graph 116, terminal 40; projection:R_m13e10q0_0028.
noncomputable def r0044 : Entry :=
  ⟨⟨[31,43,99,117,173,436,595,618,654,790,880,900,936],[11,13,14,19,21,22,35,37,41,42,52,67,81,97,98,112,140,164,168,276,304,388,416,518,522,530,552,578,592,608,644,648,772,784,800,896]⟩,
   ⟨144,486179620965,354620241540⟩⟩
theorem r0044_checked : check r0044 = true := by decide +kernel

-- small_orbit_dags/row15_m13_e10_q0.json.gz, graph 116, terminal 48; projection:R_m13e10q0_0029.
noncomputable def r0045 : Entry :=
  ⟨⟨[31,51,77,163,203,398,434,597,716,737,790,817,932],[11,13,14,19,21,22,35,49,50,69,73,76,131,138,140,161,162,193,200,262,274,304,386,388,416,529,532,545,577,580,644,672,704,772,784,800]⟩,
   ⟨145,27955239255,167639336505⟩⟩
theorem r0045_checked : check r0045 = true := by decide +kernel

-- small_orbit_dags/row15_m13_e10_q0.json.gz, graph 116, terminal 49; projection:P0_002.
noncomputable def r0046 : Entry :=
  ⟨⟨[31,43,45,78,214,307,405,620,714,805,810,914,964],[11,13,14,19,21,22,35,37,41,42,44,70,74,76,146,148,194,196,261,273,274,289,290,388,400,522,548,552,580,584,642,704,770,772,800,896]⟩,
   ⟨4,482702600580,144272548680⟩⟩
theorem r0046_checked : check r0046 = true := by decide +kernel

-- small_orbit_dags/row15_m13_e10_q0.json.gz, graph 116, terminal 52; projection:P0_011.
noncomputable def r0047 : Entry :=
  ⟨⟨[31,43,85,105,205,339,468,558,611,744,790,908,962],[11,13,14,19,21,22,35,41,42,67,69,73,81,84,97,104,140,196,200,274,276,322,336,388,448,518,524,546,552,578,608,648,704,770,772,896]⟩,
   ⟨13,507229982850,419165454450⟩⟩
theorem r0047_checked : check r0047 = true := by decide +kernel

-- small_orbit_dags/row15_m13_e10_q0.json.gz, graph 116, terminal 55; projection:P0_003.
noncomputable def r0048 : Entry :=
  ⟨⟨[31,43,115,240,269,302,425,434,597,737,790,901,976],[11,13,14,19,21,22,35,41,42,50,81,97,112,161,176,208,224,261,262,265,268,274,290,296,385,400,416,517,532,577,592,641,704,772,784,896]⟩,
   ⟨5,516492907305,36863156580⟩⟩
theorem r0048_checked : check r0048 = true := by decide +kernel

-- small_orbit_dags/row15_m13_e10_q0.json.gz, graph 116, terminal 56; projection:P0_009.
noncomputable def r0049 : Entry :=
  ⟨⟨[31,46,75,109,177,211,362,481,565,662,806,944,962],[11,13,14,19,21,22,37,38,42,44,49,67,73,74,97,104,145,146,161,176,193,194,290,322,352,416,448,518,532,548,560,642,656,770,800,896]⟩,
   ⟨11,487546049430,101203715205⟩⟩
theorem r0049_checked : check r0049 = true := by decide +kernel

-- small_orbit_dags/row15_m13_e10_q0.json.gz, graph 116, terminal 58; projection:P0_010.
noncomputable def r0050 : Entry :=
  ⟨⟨[31,43,86,105,307,341,466,481,558,589,710,744,930],[11,13,14,19,21,22,35,41,42,69,70,73,82,84,97,104,194,224,273,274,289,290,321,336,386,416,448,518,524,546,552,580,584,642,672,704]⟩,
   ⟨12,580094411670,109527114870⟩⟩
theorem r0050_checked : check r0050 = true := by decide +kernel

-- small_orbit_dags/row15_m13_e10_q0.json.gz, graph 116, terminal 59; projection:P0_012.
noncomputable def r0051 : Entry :=
  ⟨⟨[31,53,75,301,334,372,457,480,563,598,707,752,929],[11,13,14,19,21,22,37,49,52,67,70,73,74,84,112,193,224,265,268,289,292,324,328,352,385,416,448,515,530,545,560,578,592,641,672,704]⟩,
   ⟨14,494347233360,423407944560⟩⟩
theorem r0051_checked : check r0051 = true := by decide +kernel

-- small_orbit_dags/row15_m13_e10_q0.json.gz, graph 116, terminal 60; projection:R_m13e10q0_0028.
noncomputable def r0052 : Entry :=
  ⟨⟨[31,43,105,310,355,403,404,558,589,661,872,932,961],[11,13,14,19,21,22,35,38,41,42,73,97,104,145,148,259,274,276,290,292,321,352,385,388,400,517,524,548,552,577,584,641,644,800,832,896]⟩,
   ⟨144,30373271625,10824533625⟩⟩
theorem r0052_checked : check r0052 = true := by decide +kernel

-- small_orbit_dags/row15_m13_e10_q0.json.gz, graph 116, terminal 61; projection:P0_009.
noncomputable def r0053 : Entry :=
  ⟨⟨[31,45,75,110,233,310,418,421,595,738,789,914,961],[11,13,14,19,21,22,37,38,41,44,67,73,74,98,104,161,162,193,224,261,274,276,290,292,385,386,416,529,530,577,578,642,704,769,784,896]⟩,
   ⟨11,515989656585,36862846785⟩⟩
theorem r0053_checked : check r0053 = true := by decide +kernel

-- small_orbit_dags/row15_m13_e10_q0.json.gz, graph 116, terminal 63; projection:P0_012.
noncomputable def r0054 : Entry :=
  ⟨⟨[31,53,75,302,333,418,421,458,566,595,689,738,961],[11,13,14,19,21,22,37,38,49,52,67,73,74,161,162,194,261,266,268,290,292,321,328,385,386,416,448,529,530,546,560,577,578,641,672,704]⟩,
   ⟨14,516560069385,36866302785⟩⟩
theorem r0054_checked : check r0054 = true := by decide +kernel

-- small_orbit_dags/row15_m13_e10_q0.json.gz, graph 116, terminal 80; projection:P0_007.
noncomputable def r0055 : Entry :=
  ⟨⟨[31,43,169,339,340,405,419,558,598,653,866,936,964],[11,13,14,19,21,22,35,41,42,82,84,133,137,161,168,259,273,276,290,322,324,336,385,388,416,518,524,546,552,578,580,644,648,800,832,896]⟩,
   ⟨9,35203926390,172072597065⟩⟩
theorem r0055_checked : check r0055 = true := by decide +kernel

-- small_orbit_dags/row15_m13_e10_q0.json.gz, graph 116, terminal 105; projection:P0_006.
noncomputable def r0056 : Entry :=
  ⟨⟨[31,83,142,171,297,333,355,428,597,662,850,930,964],[11,13,14,19,21,22,35,41,67,69,81,82,134,138,140,162,168,265,268,289,290,296,321,322,324,388,416,530,532,580,592,642,644,770,832,896]⟩,
   ⟨8,516269691030,105498702930⟩⟩
theorem r0056_checked : check r0056 = true := by decide +kernel

-- small_orbit_dags/row15_m13_e10_q0.json.gz, graph 116, terminal 106; projection:P0_003.
noncomputable def r0057 : Entry :=
  ⟨⟨[31,75,142,205,305,341,355,458,563,662,820,930,964],[11,13,14,19,21,22,35,49,67,69,73,74,134,138,140,196,200,273,276,289,290,304,321,322,324,386,448,530,532,546,560,642,644,772,800,896]⟩,
   ⟨5,481876531350,79728768600⟩⟩
theorem r0057_checked : check r0057 = true := by decide +kernel

-- small_orbit_dags/row15_m13_e10_q0.json.gz, graph 116, terminal 110; projection:P0_006.
noncomputable def r0058 : Entry :=
  ⟨⟨[31,45,83,171,309,355,418,428,598,654,849,916,962],[11,13,14,19,21,22,35,37,41,44,67,81,82,138,140,162,168,273,276,289,290,292,321,322,386,388,416,518,532,578,592,642,644,784,832,896]⟩,
   ⟨8,481880709270,79730865720⟩⟩
theorem r0058_checked : check r0058 = true := by decide +kernel

-- small_orbit_dags/row15_m13_e10_q0.json.gz, graph 116, terminal 111; projection:P0_003.
noncomputable def r0059 : Entry :=
  ⟨⟨[31,51,77,182,341,355,418,433,587,654,844,916,962],[11,13,14,19,21,22,35,49,50,67,69,73,76,134,148,162,176,273,276,289,290,321,322,324,386,400,416,522,524,578,584,642,644,772,832,896]⟩,
   ⟨5,516273868950,105500800050⟩⟩
theorem r0059_checked : check r0059 = true := by decide +kernel

-- small_orbit_dags/row15_m13_e10_q0.json.gz, graph 116, terminal 113; projection:P0_008.
noncomputable def r0060 : Entry :=
  ⟨⟨[31,51,99,141,181,370,406,587,654,681,865,944,962],[11,13,14,19,21,22,35,49,50,67,97,98,133,134,137,140,148,161,176,274,304,322,352,386,400,521,522,545,577,578,642,648,672,800,832,896]⟩,
   ⟨10,27956351895,98923980345⟩⟩
theorem r0060_checked : check r0060 = true := by decide +kernel

-- small_orbit_dags/row15_m13_e10_q0.json.gz, graph 116, terminal 114; projection:P0_008.
noncomputable def r0061 : Entry :=
  ⟨⟨[31,43,163,211,309,337,342,481,557,682,782,932,962],[11,13,14,19,21,22,35,37,41,42,81,82,131,161,162,193,194,262,273,276,289,292,321,322,336,416,448,522,524,548,552,642,672,770,772,896]⟩,
   ⟨10,447805989015,103235937090⟩⟩
theorem r0061_checked : check r0061 = true := by decide +kernel

-- small_orbit_dags/row15_m13_e10_q0.json.gz, graph 116, terminal 132; projection:P0_001.
noncomputable def r0062 : Entry :=
  ⟨⟨[31,43,169,338,341,397,403,558,598,675,844,936,962],[11,13,14,19,21,22,35,41,42,82,84,131,137,161,168,261,268,273,274,322,324,336,385,386,392,518,524,546,552,578,580,642,672,776,832,896]⟩,
   ⟨3,516239220885,105545823810⟩⟩
theorem r0062_checked : check r0062 = true := by decide +kernel

-- small_orbit_dags/row15_m13_e10_q0.json.gz, graph 116, terminal 153; projection:P0_001.
noncomputable def r0063 : Entry :=
  ⟨⟨[31,43,45,309,334,406,450,563,618,722,812,944,968],[11,13,14,19,21,22,35,37,41,42,44,49,74,146,194,262,268,276,292,304,322,328,386,400,448,530,546,552,560,578,584,656,704,776,800,896]⟩,
   ⟨3,34920158100,104239998825⟩⟩
theorem r0063_checked : check r0063 = true := by decide +kernel

#print axioms r0000_checked

end Nonrational.OldTerminalMatches.M000
