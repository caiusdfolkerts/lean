module
prelude
public import InducedTerminalMatches.Basic

@[expose] public section

/-! Exact full-boundary matches, batch 7. Both facet and polygon
families are checked in both directions after the recorded permutation. -/

namespace Nonrational.OldTerminalMatches.M007
open Nonrational.InducedTerminalMatches
set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- six_orbit_dags/m12e12k2p0q3_types23.json.gz, graph 306, terminal 2; projection:R_multi_six_0176.
noncomputable def r0448 : Entry :=
  ⟨⟨[63,71,118,212,285,453,618,707,752,824,907,916],[7,11,29,42,54,56,67,69,70,84,98,112,148,193,196,208,261,265,276,280,385,388,522,552,560,578,608,643,656,704,776,784,896]⟩,
   ⟨664,650789266485,650788344660⟩⟩
theorem r0448_checked : check r0448 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types23.json.gz, graph 306, terminal 3; projection:R_multi_six_0177.
noncomputable def r0449 : Entry :=
  ⟨⟨[63,157,212,216,234,395,453,566,632,775,852,994],[7,11,29,42,54,56,84,88,104,133,137,138,148,152,196,200,208,226,259,261,324,385,386,448,518,532,546,560,592,608,770,772,832]⟩,
   ⟨665,521441391105,578064495105⟩⟩
theorem r0449_checked : check r0449 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types23.json.gz, graph 306, terminal 72; projection:R_multi_six_0178.
noncomputable def r0450 : Entry :=
  ⟨⟨[63,195,234,310,327,354,541,651,709,852,952,992],[7,11,29,42,54,56,67,69,98,131,138,168,193,194,224,262,276,290,304,322,324,352,517,521,532,536,580,641,648,704,784,832,928]⟩,
   ⟨666,509357531205,509356360530⟩⟩
theorem r0450_checked : check r0450 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types23.json.gz, graph 306, terminal 82; projection:R_multi_six_0179.
noncomputable def r0451 : Entry :=
  ⟨⟨[63,71,118,197,285,468,618,707,752,779,901,952],[7,11,29,42,54,56,67,69,70,84,98,112,133,193,196,208,261,265,276,280,388,400,515,522,552,578,608,641,688,704,769,776,896]⟩,
   ⟨667,646515278625,650290340100⟩⟩
theorem r0451_checked : check r0451 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types23.json.gz, graph 306, terminal 83; projection:R_multi_six_0180.
noncomputable def r0452 : Entry :=
  ⟨⟨[63,71,182,198,285,468,682,707,752,779,837,888],[7,11,29,42,54,56,67,69,70,134,148,162,176,194,196,208,261,265,276,280,324,336,515,522,552,577,624,642,672,704,769,776,832]⟩,
   ⟨668,646263620385,646263808260⟩⟩
theorem r0452_checked : check r0452 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types23.json.gz, graph 306, terminal 84; projection:R_multi_six_0181.
noncomputable def r0453 : Entry :=
  ⟨⟨[63,195,310,362,391,450,496,541,587,709,760,916],[7,11,29,42,54,56,67,74,104,131,133,193,194,240,262,276,290,304,322,352,386,388,400,448,517,521,532,536,577,584,644,656,704]⟩,
   ⟨669,444685627425,444685627650⟩⟩
theorem r0453_checked : check r0453 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types23.json.gz, graph 306, terminal 85; projection:R_multi_six_0182.
noncomputable def r0454 : Entry :=
  ⟨⟨[63,118,195,234,327,449,496,541,651,852,901,952],[7,11,29,42,54,56,67,70,84,98,112,131,138,168,193,194,224,261,321,324,336,385,432,448,517,521,532,536,641,648,772,784,896]⟩,
   ⟨670,449215475745,517163200770⟩⟩
theorem r0454_checked : check r0454 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types23.json.gz, graph 306, terminal 100; projection:R_multi_six_0185.
noncomputable def r0455 : Entry :=
  ⟨⟨[63,197,203,413,426,452,566,583,738,824,852,992],[7,11,29,42,54,56,67,69,133,137,138,162,193,194,196,276,280,296,324,388,392,416,448,518,532,546,560,578,580,736,784,800,832]⟩,
   ⟨673,444681290805,444680246355⟩⟩
theorem r0455_checked : check r0455 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types23.json.gz, graph 306, terminal 103; projection:R_multi_six_0183.
noncomputable def r0456 : Entry :=
  ⟨⟨[63,93,203,391,426,449,596,696,728,822,837,992],[7,11,29,42,54,56,69,73,84,88,131,138,168,193,200,261,262,290,321,385,386,416,448,532,560,580,592,664,672,704,772,800,832]⟩,
   ⟨671,582342685185,521944707585⟩⟩
theorem r0456_checked : check r0456 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types23.json.gz, graph 306, terminal 105; projection:R_multi_six_0184.
noncomputable def r0457 : Entry :=
  ⟨⟨[63,157,203,216,263,362,451,632,724,822,901,992],[7,11,29,42,54,56,74,88,104,133,137,148,152,195,200,208,259,261,262,290,322,352,385,448,532,560,592,608,644,704,772,800,896]⟩,
   ⟨672,581587709985,453242007810⟩⟩
theorem r0457_checked : check r0457 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types24.json.gz, graph 307, terminal 16; projection:R_multi_six_0175.
noncomputable def r0458 : Entry :=
  ⟨⟨[63,93,197,248,331,449,488,566,724,810,903,944],[7,11,29,42,54,56,69,73,84,88,133,176,193,196,208,232,259,266,296,321,328,385,416,448,518,532,546,560,644,656,770,800,896]⟩,
   ⟨663,521944707585,582342685185⟩⟩
theorem r0458_checked : check r0458 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p1q3_types15.json.gz, graph 309, terminal 5; integer:85.
noncomputable def r0459 : Entry :=
  ⟨⟨[63,86,108,244,327,466,589,744,779,826,944,961],[7,11,13,22,44,52,58,69,70,76,82,84,100,104,176,208,224,259,274,321,322,400,448,521,552,577,584,672,704,769,778,816,896]⟩,
   ⟨1987,509110137360,444937286160⟩⟩
theorem r0459_checked : check r0459 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p1q3_types15.json.gz, graph 309, terminal 6; projection:R_multi_six_0086.
noncomputable def r0460 : Entry :=
  ⟨⟨[63,86,244,333,428,452,583,722,779,826,944,961],[7,11,13,22,44,52,58,69,70,82,84,164,176,196,208,265,268,296,321,324,388,416,448,515,530,577,578,656,704,769,778,816,896]⟩,
   ⟨602,509109149745,444936295170⟩⟩
theorem r0460_checked : check r0460 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p1q3_types15.json.gz, graph 309, terminal 7; projection:R_multi_six_0087.
noncomputable def r0461 : Entry :=
  ⟨⟨[63,86,333,372,393,428,583,651,698,850,944,961],[7,11,13,22,44,52,58,69,70,82,84,137,168,265,268,292,304,321,324,336,385,392,416,515,530,577,578,641,650,688,784,832,896]⟩,
   ⟨603,517162213425,449214485250⟩⟩
theorem r0461_checked : check r0461 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p1q4_types05.json.gz, graph 310, terminal 3; projection:R_multi_six_0001.
noncomputable def r0462 : Entry :=
  ⟨⟨[63,71,331,397,428,449,598,692,709,824,858,992],[7,11,13,22,26,44,52,56,67,69,70,133,164,193,265,296,321,330,385,396,416,448,532,560,580,594,644,672,704,792,800,832]⟩,
   ⟨529,582342685185,521944707585⟩⟩
theorem r0462_checked : check r0462 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p1q4_types05.json.gz, graph 310, terminal 6; projection:R_multi_six_0002.
noncomputable def r0463 : Entry :=
  ⟨⟨[63,86,199,244,387,397,428,602,779,824,962,1008],[7,11,13,22,26,44,52,56,70,82,84,131,133,164,194,196,240,259,265,296,385,386,396,416,522,536,578,592,770,776,816,960]⟩,
   ⟨530,654568600080,654568600080⟩⟩
theorem r0463_checked : check r0463 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p1q4_types05.json.gz, graph 310, terminal 7; projection:R_multi_six_0003.
noncomputable def r0464 : Entry :=
  ⟨⟨[63,86,195,218,327,372,651,696,781,812,961,1008],[7,11,13,22,26,44,52,56,67,70,82,84,131,138,152,193,194,208,261,292,321,324,368,521,552,641,648,688,769,780,800,960]⟩,
   ⟨531,521441387280,578064491280⟩⟩
theorem r0464_checked : check r0464 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p1q4_types05.json.gz, graph 310, terminal 8; projection:R_multi_six_0005.
noncomputable def r0465 : Entry :=
  ⟨⟨[63,197,236,278,327,372,653,696,779,794,961,1008],[7,11,13,22,26,44,52,56,69,100,133,140,168,193,196,224,259,262,274,276,321,324,368,521,536,641,648,688,769,778,784,960]⟩,
   ⟨533,578064495120,521441391120⟩⟩
theorem r0465_checked : check r0465 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p1q4_types05.json.gz, graph 310, terminal 10; projection:R_multi_six_0004.
noncomputable def r0466 : Entry :=
  ⟨⟨[63,86,197,244,327,346,653,684,779,824,961,1008],[7,11,13,22,26,44,52,56,69,70,82,84,133,164,193,196,240,259,266,280,321,322,336,521,552,641,652,672,769,776,816,960]⟩,
   ⟨532,509361791760,509361791760⟩⟩
theorem r0466_checked : check r0466 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p1q4_types05.json.gz, graph 310, terminal 11; projection:R_multi_six_0006.
noncomputable def r0467 : Entry :=
  ⟨⟨[63,199,372,406,452,589,620,651,705,824,922,992],[7,11,13,22,26,44,52,56,69,100,131,134,193,196,276,304,324,352,388,402,448,521,552,577,588,608,641,650,704,792,800,896]⟩,
   ⟨534,590144090625,590144090625⟩⟩
theorem r0467_checked : check r0467 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p1q4_types05.json.gz, graph 310, terminal 12; projection:R_multi_six_0009.
noncomputable def r0468 : Entry :=
  ⟨⟨[63,86,199,333,364,395,449,628,722,824,922,992],[7,11,13,22,26,44,52,56,69,70,82,84,100,131,193,194,265,296,321,332,352,385,394,448,560,592,608,658,704,792,800,896]⟩,
   ⟨535,654820258305,654820258305⟩⟩
theorem r0468_checked : check r0468 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p1q4_types05.json.gz, graph 310, terminal 13; projection:R_multi_six_0010.
noncomputable def r0469 : Entry :=
  ⟨⟨[63,86,141,236,372,440,583,651,709,850,922,992],[7,11,13,22,26,44,52,56,70,82,84,100,133,137,140,168,196,224,304,336,352,408,416,515,578,581,641,650,704,786,832,896]⟩,
   ⟨536,650788287045,650788287045⟩⟩
theorem r0469_checked : check r0469 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p1q4_types15.json.gz, graph 311, terminal 4; projection:R_multi_six_0068.
noncomputable def r0470 : Entry :=
  ⟨⟨[63,186,240,278,372,391,466,651,744,781,876,961],[7,11,13,22,44,52,58,112,131,138,146,168,176,208,224,261,262,274,276,336,356,385,386,448,521,616,641,648,704,769,780,832]⟩,
   ⟨586,517163201040,449215476240⟩⟩
theorem r0470_checked : check r0470 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p1q4_types15.json.gz, graph 311, terminal 20; projection:R_multi_six_0072.
noncomputable def r0471 : Entry :=
  ⟨⟨[63,86,172,199,244,331,397,752,826,850,936,961],[7,11,13,22,44,52,58,67,70,82,84,133,140,164,168,193,196,240,265,266,321,322,385,392,560,592,672,704,786,808,832,896]⟩,
   ⟨589,509361795600,509361795600⟩⟩
theorem r0471_checked : check r0471 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p1q4_types15.json.gz, graph 311, terminal 21; projection:R_multi_six_0071.
noncomputable def r0472 : Entry :=
  ⟨⟨[63,108,150,205,331,391,628,724,826,872,914,961],[7,11,13,22,44,52,58,73,76,100,104,133,134,146,148,193,196,259,266,321,328,385,386,560,596,608,656,704,786,808,832,896]⟩,
   ⟨588,509360804400,509360804400⟩⟩
theorem r0472_checked : check r0472 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p1q4_types15.json.gz, graph 311, terminal 22; projection:R_multi_six_0070.
noncomputable def r0473 : Entry :=
  ⟨⟨[63,108,150,199,333,395,628,724,826,872,914,961],[7,11,13,22,44,52,58,69,76,100,104,131,134,146,148,193,196,265,266,321,328,385,386,560,596,608,656,704,786,808,832,896]⟩,
   ⟨587,509110137360,444937286160⟩⟩
theorem r0473_checked : check r0473 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p1q4_types15.json.gz, graph 311, terminal 23; projection:R_multi_six_0074.
noncomputable def r0474 : Entry :=
  ⟨⟨[63,86,116,205,236,327,395,752,826,850,936,961],[7,11,13,22,44,52,58,69,70,82,84,100,112,137,168,193,204,224,259,266,321,322,385,392,560,592,672,704,786,808,832,896]⟩,
   ⟨591,509109146160,444936294960⟩⟩
theorem r0474_checked : check r0474 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p1q4_types15.json.gz, graph 311, terminal 24; projection:R_multi_six_0073.
noncomputable def r0475 : Entry :=
  ⟨⟨[63,86,244,333,364,480,583,698,722,779,936,961],[7,11,13,22,44,52,58,69,70,82,84,100,176,208,224,265,296,321,332,352,416,448,515,522,577,578,658,680,704,769,776,896]⟩,
   ⟨590,448711168560,448711168560⟩⟩
theorem r0475_checked : check r0475 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p1q4_types15.json.gz, graph 311, terminal 28; projection:R_multi_six_0077.
noncomputable def r0476 : Entry :=
  ⟨⟨[63,116,150,364,391,468,651,698,752,781,872,961],[7,11,13,22,44,52,58,84,100,112,131,134,146,148,208,261,268,324,360,385,388,448,521,552,608,641,650,688,704,769,776,832]⟩,
   ⟨594,452989358640,577560187440⟩⟩
theorem r0476_checked : check r0476 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p1q4_types15.json.gz, graph 311, terminal 29; projection:R_multi_six_0076.
noncomputable def r0477 : Entry :=
  ⟨⟨[63,116,236,342,391,452,653,744,779,826,880,961],[7,11,13,22,44,52,58,84,100,112,133,140,196,232,259,262,274,324,336,385,388,448,521,552,608,641,648,704,769,778,816,832]⟩,
   ⟨593,444936294960,509109146160⟩⟩
theorem r0477_checked : check r0477 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p1q4_types15.json.gz, graph 311, terminal 30; projection:R_multi_six_0075.
noncomputable def r0478 : Entry :=
  ⟨⟨[63,116,195,214,327,364,651,698,752,781,872,961],[7,11,13,22,44,52,58,67,70,84,100,112,131,146,193,194,208,261,268,321,324,360,521,552,608,641,650,688,704,769,776,832]⟩,
   ⟨592,452989358640,577560187440⟩⟩
theorem r0478_checked : check r0478 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p1q4_types15.json.gz, graph 311, terminal 31; projection:R_multi_six_0078.
noncomputable def r0479 : Entry :=
  ⟨⟨[63,86,244,333,364,480,583,722,779,826,944,961],[7,11,13,22,44,52,58,69,70,82,84,100,176,208,224,265,296,321,332,352,416,448,515,530,577,578,656,704,769,778,816,896]⟩,
   ⟨595,444685627905,444685627905⟩⟩
theorem r0479_checked : check r0479 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p1q4_types15.json.gz, graph 311, terminal 32; projection:R_multi_six_0083.
noncomputable def r0480 : Entry :=
  ⟨⟨[63,86,141,372,428,453,583,651,698,850,944,961],[7,11,13,22,44,52,58,69,70,82,84,133,137,140,168,292,304,324,336,388,416,449,515,530,577,578,641,650,688,784,832,896]⟩,
   ⟨600,517162213425,449214485250⟩⟩
theorem r0480_checked : check r0480 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p1q4_types15.json.gz, graph 311, terminal 33; projection:R_multi_six_0079.
noncomputable def r0481 : Entry :=
  ⟨⟨[63,244,327,406,452,589,620,736,779,826,944,961],[7,11,13,22,44,52,58,69,100,148,176,196,224,259,262,274,321,324,388,400,448,521,552,577,588,608,672,704,769,778,816,896]⟩,
   ⟨596,509110137345,444937286145⟩⟩
theorem r0481_checked : check r0481 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p1q4_types15.json.gz, graph 311, terminal 34; projection:R_multi_six_0080.
noncomputable def r0482 : Entry :=
  ⟨⟨[63,199,244,323,342,653,684,736,779,826,880,961],[7,11,13,22,44,52,58,67,70,84,112,133,164,193,196,224,259,274,321,322,336,521,552,608,641,652,672,704,769,778,816,832]⟩,
   ⟨597,509361795585,509361795585⟩⟩
theorem r0482_checked : check r0482 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p1q4_types15.json.gz, graph 311, terminal 35; projection:R_multi_six_0082.
noncomputable def r0483 : Entry :=
  ⟨⟨[63,86,197,244,327,466,653,684,779,826,944,961],[7,11,13,22,44,52,58,69,70,82,84,133,164,176,193,196,208,259,274,321,322,400,448,521,552,641,652,672,769,778,816,896]⟩,
   ⟨599,444684640305,444684636930⟩⟩
theorem r0483_checked : check r0483 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p1q4_types15.json.gz, graph 311, terminal 36; projection:R_multi_six_0081.
noncomputable def r0484 : Entry :=
  ⟨⟨[63,195,214,327,372,464,651,698,781,812,944,961],[7,11,13,22,44,52,58,67,70,84,131,146,193,194,208,261,292,304,321,324,336,400,448,521,552,641,650,688,769,780,800,896]⟩,
   ⟨598,448711172145,448711168770⟩⟩
theorem r0484_checked : check r0484 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p1q4_types15.json.gz, graph 311, terminal 37; projection:R_multi_six_0084.
noncomputable def r0485 : Entry :=
  ⟨⟨[63,86,172,205,372,484,583,651,698,850,944,961],[7,11,13,22,44,52,58,69,70,82,84,137,140,164,168,193,196,304,336,356,416,448,515,530,577,578,641,650,688,784,832,896]⟩,
   ⟨601,448712159760,448712159760⟩⟩
theorem r0485_checked : check r0485 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p1q4_types25.json.gz, graph 312, terminal 11; projection:R_multi_six_0171.
noncomputable def r0486 : Entry :=
  ⟨⟨[63,93,106,197,376,468,587,647,694,866,944,961],[7,11,29,42,54,56,69,73,74,84,88,98,104,133,148,193,196,304,336,352,400,448,515,546,577,578,641,646,688,800,832,896]⟩,
   ⟨659,521944449825,582342615300⟩⟩
theorem r0486_checked : check r0486 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p1q4_types25.json.gz, graph 312, terminal 12; projection:R_multi_six_0174.
noncomputable def r0487 : Entry :=
  ⟨⟨[63,93,331,376,387,426,581,647,694,852,944,961],[7,11,29,42,54,56,69,73,84,88,131,162,259,266,296,304,321,328,336,385,386,416,517,532,577,580,641,646,688,784,832,896]⟩,
   ⟨662,590395736865,590395744515⟩⟩
theorem r0487_checked : check r0487 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p1q4_types25.json.gz, graph 312, terminal 13; projection:R_multi_six_0173.
noncomputable def r0488 : Entry :=
  ⟨⟨[63,93,248,331,426,456,581,724,775,822,944,961],[7,11,29,42,54,56,69,73,84,88,168,176,200,208,259,266,290,321,328,392,416,448,517,532,577,580,656,704,769,774,816,896]⟩,
   ⟨661,582342673185,521944703235⟩⟩
theorem r0488_checked : check r0488 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p1q4_types25.json.gz, graph 312, terminal 14; projection:R_multi_six_0172.
noncomputable def r0489 : Entry :=
  ⟨⟨[63,93,197,331,391,438,449,632,724,810,944,968],[7,11,29,42,54,56,69,73,84,88,133,148,193,196,259,266,290,321,328,385,390,432,448,552,560,584,592,656,704,776,800,896]⟩,
   ⟨660,650793714465,650793722115⟩⟩
theorem r0489_checked : check r0489 = true := by decide +kernel

-- six_orbit_dags/m12e13k2p1q5_types15.json.gz, graph 314, terminal 3; gp:C000.
noncomputable def r0490 : Entry :=
  ⟨⟨[63,116,395,442,496,598,620,647,722,781,872,961],[7,11,13,22,44,52,58,84,100,112,131,146,208,265,296,352,385,394,432,448,517,518,524,580,594,616,641,642,704,769,776,832]⟩,
   ⟨1995,650290410000,646515536400⟩⟩
theorem r0490_checked : check r0490 = true := by decide +kernel

-- six_orbit_dags/m13e12k2p1q4_types05.json.gz, graph 319, terminal 47; projection:R_multi_six_0000.
noncomputable def r0491 : Entry :=
  ⟨⟨[63,86,195,198,244,391,428,587,602,781,824,961,1008],[7,11,13,22,26,44,52,56,67,70,82,84,131,134,164,193,194,196,240,261,268,296,385,388,416,521,536,577,586,592,769,776,816,960]⟩,
   ⟨528,650290410000,646515536400⟩⟩
theorem r0491_checked : check r0491 = true := by decide +kernel

-- six_orbit_dags/m13e12k2p1q4_types15.json.gz, graph 320, terminal 85; projection:R_multi_six_0054.
noncomputable def r0492 : Entry :=
  ⟨⟨[63,228,278,327,372,496,589,684,698,708,779,914,961],[7,11,13,22,44,52,58,69,100,164,176,196,224,259,262,274,276,321,324,368,400,448,521,522,524,577,580,644,658,680,704,769,770,896]⟩,
   ⟨573,448711168560,448711168560⟩⟩
theorem r0492_checked : check r0492 = true := by decide +kernel

-- six_orbit_dags/m13e12k2p1q4_types15.json.gz, graph 320, terminal 106; projection:R_multi_six_0055.
noncomputable def r0493 : Entry :=
  ⟨⟨[63,116,212,327,406,442,452,589,620,752,779,936,961],[7,11,13,22,44,52,58,69,84,100,112,148,176,196,208,259,262,266,321,324,388,402,424,448,521,552,577,588,608,672,704,769,776,896]⟩,
   ⟨574,577561178640,452990349840⟩⟩
theorem r0493_checked : check r0493 = true := by decide +kernel

-- six_orbit_dags/m13e12k2p1q4_types15.json.gz, graph 320, terminal 112; projection:R_multi_six_0056.
noncomputable def r0494 : Entry :=
  ⟨⟨[63,71,108,195,214,333,395,692,740,826,872,914,961],[7,11,13,22,44,52,58,67,69,70,76,100,104,131,146,148,193,194,196,265,266,321,328,385,386,560,608,656,676,704,786,808,832,896]⟩,
   ⟨575,509110137360,444937286160⟩⟩
theorem r0494_checked : check r0494 = true := by decide +kernel

-- six_orbit_dags/m13e12k2p1q4_types15.json.gz, graph 320, terminal 136; projection:R_multi_six_0059.
noncomputable def r0495 : Entry :=
  ⟨⟨[63,116,150,212,236,391,466,653,744,779,826,880,961],[7,11,13,22,44,52,58,84,100,112,133,134,140,146,148,196,208,232,259,274,336,385,386,448,521,552,608,641,648,704,769,778,816,832]⟩,
   ⟨578,444936290865,509109146115⟩⟩
theorem r0495_checked : check r0495 = true := by decide +kernel

-- six_orbit_dags/m13e12k2p1q4_types15.json.gz, graph 320, terminal 137; projection:R_multi_six_0060.
noncomputable def r0496 : Entry :=
  ⟨⟨[63,86,116,198,236,391,466,653,744,779,826,880,961],[7,11,13,22,44,52,58,70,82,84,100,112,133,134,140,194,196,232,259,274,336,385,386,448,521,552,608,641,648,704,769,778,816,832]⟩,
   ⟨579,444936290865,509109146115⟩⟩
theorem r0496_checked : check r0496 = true := by decide +kernel

-- six_orbit_dags/m13e12k2p1q4_types15.json.gz, graph 320, terminal 142; projection:R_multi_six_0058.
noncomputable def r0497 : Entry :=
  ⟨⟨[63,116,342,364,391,402,464,651,698,752,781,872,961],[7,11,13,22,44,52,58,84,100,112,131,146,208,261,262,268,274,324,336,360,385,386,400,448,521,552,608,641,650,688,704,769,776,832]⟩,
   ⟨577,452989358640,577560187440⟩⟩
theorem r0497_checked : check r0497 = true := by decide +kernel

-- six_orbit_dags/m13e12k2p1q4_types15.json.gz, graph 320, terminal 143; projection:R_multi_six_0057.
noncomputable def r0498 : Entry :=
  ⟨⟨[63,116,210,342,364,391,450,651,698,752,781,872,961],[7,11,13,22,44,52,58,82,84,100,112,131,146,194,208,261,262,268,322,324,360,385,386,448,521,552,608,641,650,688,704,769,776,832]⟩,
   ⟨576,452989358640,577560187440⟩⟩
theorem r0498_checked : check r0498 = true := by decide +kernel

-- six_orbit_dags/m13e12k2p1q4_types15.json.gz, graph 320, terminal 153; projection:R_multi_six_0063.
noncomputable def r0499 : Entry :=
  ⟨⟨[63,86,172,244,338,391,454,653,744,779,826,880,961],[7,11,13,22,44,52,58,70,82,84,112,133,140,164,168,196,224,259,274,322,336,385,390,448,521,552,608,641,648,704,769,778,816,832]⟩,
   ⟨582,509361795105,509361795330⟩⟩
theorem r0499_checked : check r0499 = true := by decide +kernel

-- six_orbit_dags/m13e12k2p1q4_types15.json.gz, graph 320, terminal 158; projection:R_multi_six_0064.
noncomputable def r0500 : Entry :=
  ⟨⟨[63,71,108,198,244,333,488,662,707,779,826,944,961],[7,11,13,22,44,52,58,67,69,70,76,100,104,134,148,176,194,196,224,265,296,321,328,416,448,515,530,642,656,705,769,778,816,896]⟩,
   ⟨583,444685627425,444685627650⟩⟩
theorem r0500_checked : check r0500 = true := by decide +kernel

-- six_orbit_dags/m13e12k2p1q4_types15.json.gz, graph 320, terminal 160; projection:R_multi_six_0061.
noncomputable def r0501 : Entry :=
  ⟨⟨[63,86,199,395,442,449,589,628,722,812,841,944,960],[7,11,13,22,44,52,58,69,70,82,84,131,146,193,194,265,296,321,385,394,432,448,524,548,560,580,585,592,656,704,776,800,832,896]⟩,
   ⟨580,577560183345,452989358595⟩⟩
theorem r0501_checked : check r0501 = true := by decide +kernel

-- six_orbit_dags/m13e12k2p1q4_types15.json.gz, graph 320, terminal 161; projection:R_multi_six_0062.
noncomputable def r0502 : Entry :=
  ⟨⟨[63,71,108,195,372,406,454,589,651,698,872,944,961],[7,11,13,22,44,52,58,67,69,70,76,100,104,131,146,193,194,276,304,324,352,390,400,448,521,552,577,584,641,650,688,800,832,896]⟩,
   ⟨581,517163200545,449215475970⟩⟩
theorem r0502_checked : check r0502 = true := by decide +kernel

-- six_orbit_dags/m13e12k2p1q4_types15.json.gz, graph 320, terminal 169; projection:R_multi_six_0065.
noncomputable def r0503 : Entry :=
  ⟨⟨[63,210,300,342,372,391,450,651,698,752,781,872,961],[7,11,13,22,44,52,58,82,112,131,146,194,208,261,262,268,292,296,322,340,352,385,386,448,521,552,608,641,650,688,704,769,776,832]⟩,
   ⟨584,452989358640,577560187440⟩⟩
theorem r0503_checked : check r0503 = true := by decide +kernel

-- six_orbit_dags/m13e12k2p1q4_types15.json.gz, graph 320, terminal 182; projection:R_multi_six_0066.
noncomputable def r0504 : Entry :=
  ⟨⟨[63,75,236,333,372,480,579,698,714,775,790,944,961],[7,11,13,22,44,52,58,67,73,74,76,100,168,200,224,261,276,304,321,324,352,416,448,515,530,577,578,650,688,704,769,774,784,896]⟩,
   ⟨585,452990349345,577561178370⟩⟩
theorem r0504_checked : check r0504 = true := by decide +kernel

-- six_orbit_dags/m13e12k2p1q4_types25.json.gz, graph 321, terminal 84; projection:R_multi_six_0170.
noncomputable def r0505 : Entry :=
  ⟨⟨[63,93,212,248,404,453,587,682,775,822,833,944,968],[7,11,29,42,54,56,69,73,84,88,148,168,176,196,200,208,261,276,321,388,400,448,515,522,546,577,584,648,672,769,774,816,832,896]⟩,
   ⟨658,517918163745,517918171395⟩⟩
theorem r0505_checked : check r0505 = true := by decide +kernel

-- six_orbit_dags/type0m13e11q1r0.json.gz, graph 337, terminal 2; projection:R_one_six_0030.
noncomputable def r0506 : Entry :=
  ⟨⟨[63,75,150,218,263,436,454,696,713,781,812,835,992],[7,11,13,22,26,44,52,56,67,73,74,134,146,148,152,176,194,200,259,261,262,292,322,388,416,448,521,552,577,648,672,704,769,780,800,832]⟩,
   ⟨703,509361783585,509361791235⟩⟩
theorem r0506_checked : check r0506 = true := by decide +kernel

-- six_orbit_dags/type0m13e11q1r0.json.gz, graph 337, terminal 9; projection:R_one_six_0012.
noncomputable def r0507 : Entry :=
  ⟨⟨[63,71,86,172,331,397,410,628,696,722,837,932,962],[7,11,13,22,26,44,52,56,67,69,70,82,84,140,146,152,164,168,261,265,266,321,322,386,388,392,548,560,580,592,656,672,706,772,832,896]⟩,
   ⟨685,582342684705,521944707330⟩⟩
theorem r0507_checked : check r0507 = true := by decide +kernel

-- six_orbit_dags/type0m13e11q1r0.json.gz, graph 337, terminal 11; projection:R_one_six_0013.
noncomputable def r0508 : Entry :=
  ⟨⟨[63,86,116,139,376,410,428,583,653,740,850,899,992],[7,11,13,22,26,44,52,56,70,82,84,100,112,131,137,138,140,164,274,280,296,336,352,386,392,416,515,517,578,580,641,644,736,770,832,896]⟩,
   ⟨686,582338347845,521939264595⟩⟩
theorem r0508_checked : check r0508 = true := by decide +kernel

-- six_orbit_dags/type0m13e11q1r0.json.gz, graph 337, terminal 34; projection:R_one_six_0028.
noncomputable def r0509 : Entry :=
  ⟨⟨[63,116,135,214,267,410,496,620,709,781,824,899,992],[7,11,13,22,26,44,52,56,84,100,112,131,133,134,146,196,208,259,265,266,280,304,386,400,480,517,524,552,580,608,641,704,769,776,800,896]⟩,
   ⟨701,509110125345,444937281795⟩⟩
theorem r0509_checked : check r0509 = true := by decide +kernel

-- six_orbit_dags/type0m13e11q1r0.json.gz, graph 337, terminal 54; projection:R_one_six_0036.
noncomputable def r0510 : Entry :=
  ⟨⟨[63,71,154,214,269,436,453,696,714,779,812,835,992],[7,11,13,22,26,44,52,56,67,69,70,138,146,148,152,176,194,196,261,265,268,292,321,388,416,448,522,552,578,648,672,704,771,776,800,832]⟩,
   ⟨709,517918175265,517918175490⟩⟩
theorem r0510_checked : check r0510 = true := by decide +kernel

-- six_orbit_dags/type0m13e11q1r0.json.gz, graph 337, terminal 56; projection:R_one_six_0022.
noncomputable def r0511 : Entry :=
  ⟨⟨[63,71,205,395,428,449,598,692,708,794,824,835,992],[7,11,13,22,26,44,52,56,67,69,70,137,140,164,193,196,259,266,296,321,385,392,416,448,530,532,560,578,580,644,672,704,770,792,800,832]⟩,
   ⟨695,517918175265,517918175490⟩⟩
theorem r0511_checked : check r0511 = true := by decide +kernel

#print axioms r0448_checked

end Nonrational.OldTerminalMatches.M007
