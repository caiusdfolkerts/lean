module
prelude
public import InducedTerminalMatches.Basic

@[expose] public section

/-! Exact full-boundary matches, batch 5. Both facet and polygon
families are checked in both directions after the recorded permutation. -/

namespace Nonrational.OldTerminalMatches.M005
open Nonrational.InducedTerminalMatches
set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- small_orbit_dags/row20_m13_e12_q2.json.gz, graph 119, terminal 12; gp:C018.
noncomputable def r0320 : Entry :=
  ⟨⟨[31,43,115,173,342,398,618,661,737,842,849,916,936],[11,13,14,19,21,22,35,41,42,81,82,97,98,133,140,161,168,262,266,276,322,336,388,392,529,552,577,586,608,641,660,672,776,784,832,896]⟩,
   ⟨2013,516520300905,36796064805⟩⟩
theorem r0320_checked : check r0320 = true := by decide +kernel

-- small_orbit_dags/row20_m13_e12_q2.json.gz, graph 119, terminal 21; gp:C018.
noncomputable def r0321 : Entry :=
  ⟨⟨[31,99,109,171,339,406,482,597,620,654,880,916,936],[11,13,14,19,21,22,35,41,67,69,81,97,98,108,134,138,162,168,274,322,336,352,386,404,416,524,532,552,580,592,608,644,648,784,800,896]⟩,
   ⟨2013,554678106000,108001507200⟩⟩
theorem r0321_checked : check r0321 = true := by decide +kernel

-- small_orbit_dags/row20_m13_e12_q2.json.gz, graph 119, terminal 26; gp:C018.
noncomputable def r0322 : Entry :=
  ⟨⟨[31,107,214,230,232,339,457,558,692,781,789,936,976],[11,13,14,19,21,22,38,42,67,73,82,98,104,148,164,168,198,200,208,224,265,273,321,336,392,448,524,532,548,552,656,672,773,776,784,896]⟩,
   ⟨2013,280616277810,223983767685⟩⟩
theorem r0322_checked : check r0322 = true := by decide +kernel

-- small_orbit_dags/row20_m13_e12_q2.json.gz, graph 119, terminal 29; gp:C018.
noncomputable def r0323 : Entry :=
  ⟨⟨[31,105,171,211,302,333,341,662,678,737,820,872,976],[11,13,14,19,21,22,38,41,42,73,81,97,104,131,146,161,162,193,208,268,276,292,296,325,328,336,532,548,608,646,656,672,704,784,800,832]⟩,
   ⟨2013,150702917445,361414887795⟩⟩
theorem r0323_checked : check r0323 = true := by decide +kernel

-- small_orbit_dags/row20_m13_e12_q2.json.gz, graph 119, terminal 31; gp:C018.
noncomputable def r0324 : Entry :=
  ⟨⟨[31,107,211,225,405,496,590,653,681,790,850,872,932],[11,13,14,19,21,22,41,67,74,82,97,104,133,145,161,193,208,224,276,336,352,388,400,416,518,524,552,578,584,644,649,672,772,786,800,832]⟩,
   ⟨2013,499709458470,423330591045⟩⟩
theorem r0324_checked : check r0324 = true := by decide +kernel

-- small_orbit_dags/row20_m13_e12_q2.json.gz, graph 119, terminal 37; gp:C018.
noncomputable def r0325 : Entry :=
  ⟨⟨[31,105,115,203,398,488,565,662,722,781,809,880,964],[11,13,14,19,21,22,41,49,67,73,82,97,104,112,134,138,194,200,268,296,352,388,392,448,517,532,545,560,592,644,658,704,772,777,800,832]⟩,
   ⟨2013,494609393685,423373342485⟩⟩
theorem r0325_checked : check r0325 = true := by decide +kernel

-- small_orbit_dags/row21_m13_e12_q3.json.gz, graph 120, terminal 2; projection:R_m13e12q3_0000.
noncomputable def r0326 : Entry :=
  ⟨⟨[31,43,115,309,397,425,496,618,654,744,790,850,964],[11,13,14,19,21,22,35,41,42,49,82,98,112,140,168,224,261,276,289,304,336,388,393,416,448,518,522,578,616,644,648,704,772,786,832]⟩,
   ⟨205,447520708980,172223395380⟩⟩
theorem r0326_checked : check r0326 = true := by decide +kernel

-- small_orbit_dags/row21_m13_e12_q3.json.gz, graph 120, terminal 8; projection:R_m13e12q3_0000.
noncomputable def r0327 : Entry :=
  ⟨⟨[31,43,109,334,406,426,488,563,690,737,789,837,976],[11,13,14,19,21,22,35,41,42,69,76,97,104,146,162,224,262,266,276,324,328,386,400,424,448,529,545,562,577,656,672,704,773,784,832]⟩,
   ⟨205,447634096215,446828868690⟩⟩
theorem r0327_checked : check r0327 = true := by decide +kernel

-- small_orbit_dags/row21_m13_e12_q3.json.gz, graph 120, terminal 10; projection:R_m13e12q3_0000.
noncomputable def r0328 : Entry :=
  ⟨⟨[31,105,115,171,333,341,398,566,678,744,880,916,968],[11,13,14,19,21,22,35,41,50,73,81,97,104,112,134,138,162,168,268,276,325,328,336,388,392,532,550,560,608,644,672,712,784,832,896]⟩,
   ⟨205,425763362820,284964194145⟩⟩
theorem r0328_checked : check r0328 = true := by decide +kernel

-- small_orbit_dags/row21_m13_e12_q3.json.gz, graph 120, terminal 11; projection:R_m13e12q3_0000.
noncomputable def r0329 : Entry :=
  ⟨⟨[31,107,181,225,301,436,488,590,659,707,790,844,976],[11,13,14,19,21,22,37,41,67,74,97,104,145,161,180,193,224,268,276,292,296,328,400,416,448,518,530,578,588,643,656,704,772,784,832]⟩,
   ⟨205,451361835045,560107700595⟩⟩
theorem r0329_checked : check r0329 = true := by decide +kernel

-- small_orbit_dags/row21_m13_e12_q3.json.gz, graph 120, terminal 12; projection:R_m13e12q3_0000.
noncomputable def r0330 : Entry :=
  ⟨⟨[31,299,341,355,397,468,480,595,618,654,662,752,936],[11,13,14,19,21,22,42,67,81,98,140,148,208,224,261,265,291,296,321,340,352,388,392,416,448,522,530,552,578,592,608,646,648,656,672]⟩,
   ⟨205,6262265475,212372620425⟩⟩
theorem r0330_checked : check r0330 = true := by decide +kernel

-- small_orbit_dags/row21_m13_e12_q3.json.gz, graph 120, terminal 20; projection:R_m13e12q3_0000.
noncomputable def r0331 : Entry :=
  ⟨⟨[31,105,171,333,341,488,563,625,654,738,790,908,976],[11,13,14,19,21,22,35,41,73,81,97,104,138,162,168,224,268,276,325,328,336,392,448,518,530,546,561,592,608,642,652,704,772,784,896]⟩,
   ⟨205,558434055825,108219680775⟩⟩
theorem r0331_checked : check r0331 = true := by decide +kernel

-- six_orbit_dags/m10e13k3p0q4_types223.json.gz, graph 180, terminal 1; projection:R_multi_six_0208.
noncomputable def r0332 : Entry :=
  ⟨⟨[63,118,199,376,468,651,797,810,901,994],[7,11,29,42,54,56,70,84,98,112,131,133,194,196,276,280,296,336,352,388,448,521,522,641,642,773,776,802,896]⟩,
   ⟨684,582338421765,521939338065⟩⟩
theorem r0332_checked : check r0332 = true := by decide +kernel

-- six_orbit_dags/m10e13k3p0q4_types233.json.gz, graph 182, terminal 0; projection:R_multi_six_0207.
noncomputable def r0333 : Entry :=
  ⟨⟨[63,93,182,331,426,724,837,888,903,944],[7,11,29,42,54,56,69,73,84,88,134,148,162,176,259,266,296,321,328,386,416,580,592,644,656,773,816,832,896]⟩,
   ⟨683,590395748865,590395748865⟩⟩
theorem r0333_checked : check r0333 = true := by decide +kernel

-- six_orbit_dags/m11e12k2p0q2_types13.json.gz, graph 234, terminal 0; projection:R_multi_six_0169.
noncomputable def r0334 : Entry :=
  ⟨⟨[63,71,205,314,395,598,620,707,820,914,1000],[7,11,13,22,44,52,58,67,69,70,76,131,137,193,200,266,274,296,304,386,392,530,532,548,578,580,616,642,704,784,800,896]⟩,
   ⟨657,646262882865,646262886915⟩⟩
theorem r0334_checked : check r0334 = true := by decide +kernel

-- six_orbit_dags/m11e12k2p0q3_types12.json.gz, graph 244, terminal 2; projection:R_multi_six_0163.
noncomputable def r0335 : Entry :=
  ⟨⟨[63,71,186,342,436,589,651,835,876,914,936],[7,11,13,22,44,52,58,67,69,70,138,146,168,176,274,276,292,322,324,400,416,515,521,577,588,642,648,770,808,832,896]⟩,
   ⟨656,521440395825,578063503875⟩⟩
theorem r0335_checked : check r0335 = true := by decide +kernel

-- six_orbit_dags/m11e12k2p0q3_types13.json.gz, graph 245, terminal 1; projection:R_multi_six_0154.
noncomputable def r0336 : Entry :=
  ⟨⟨[63,86,186,244,395,466,583,620,781,835,1000],[7,11,13,22,44,52,58,70,82,84,100,138,146,168,176,208,224,259,265,322,386,392,448,517,524,579,580,616,769,776,832]⟩,
   ⟨655,581586715185,453241016835⟩⟩
theorem r0336_checked : check r0336 = true := by decide +kernel

-- six_orbit_dags/m11e12k2p0q3_types22.json.gz, graph 247, terminal 4; projection:R_multi_six_0202.
noncomputable def r0337 : Entry :=
  ⟨⟨[63,75,234,310,440,605,707,728,775,916,930],[7,11,29,42,54,56,67,73,74,152,162,168,194,200,262,276,290,304,400,416,515,517,532,577,600,642,656,704,770,772,896]⟩,
   ⟨681,40290760050,571618898025⟩⟩
theorem r0337_checked : check r0337 = true := by decide +kernel

-- six_orbit_dags/m11e12k2p0q3_types22.json.gz, graph 247, terminal 5; projection:R_multi_six_0202.
noncomputable def r0338 : Entry :=
  ⟨⟨[63,71,157,203,362,440,630,709,880,916,968],[7,11,29,42,54,56,67,69,70,74,98,133,137,148,152,193,200,296,304,328,352,392,400,532,580,624,644,704,784,832,896]⟩,
   ⟨681,590144078625,590144086275⟩⟩
theorem r0338_checked : check r0338 = true := by decide +kernel

-- six_orbit_dags/m11e12k2p0q3_types22.json.gz, graph 247, terminal 8; projection:R_multi_six_0204.
noncomputable def r0339 : Entry :=
  ⟨⟨[63,93,199,201,376,468,651,694,810,944,968],[7,11,29,42,54,56,69,73,84,88,131,134,137,148,193,196,200,296,304,328,336,400,448,522,546,642,648,688,776,800,896]⟩,
   ⟨682,94643713320,413258764695⟩⟩
theorem r0339_checked : check r0339 = true := by decide +kernel

-- six_orbit_dags/m11e12k2p0q3_types22.json.gz, graph 247, terminal 9; projection:R_multi_six_0204.
noncomputable def r0340 : Entry :=
  ⟨⟨[63,234,395,438,456,496,541,632,775,841,852],[7,11,29,42,54,56,104,112,138,162,200,224,259,262,265,276,328,336,386,392,432,448,517,521,532,536,584,592,769,772,832]⟩,
   ⟨682,444685615905,444685623555⟩⟩
theorem r0340_checked : check r0340 = true := by decide +kernel

-- six_orbit_dags/m11e12k2p0q3_types23.json.gz, graph 248, terminal 4; projection:R_multi_six_0193.
noncomputable def r0341 : Entry :=
  ⟨⟨[63,157,201,234,331,453,566,696,775,916,994],[7,11,29,42,54,56,73,74,133,137,148,152,168,193,200,226,259,261,321,322,388,448,518,532,546,560,656,672,770,772,896]⟩,
   ⟨678,448707896325,448706790225⟩⟩
theorem r0341_checked : check r0341 = true := by decide +kernel

-- six_orbit_dags/m11e12k2p0q3_types23.json.gz, graph 248, terminal 10; projection:R_multi_six_0198.
noncomputable def r0342 : Entry :=
  ⟨⟨[63,71,310,362,454,496,541,587,709,760,916],[7,11,29,42,54,56,67,69,70,74,104,196,240,262,276,290,304,322,352,388,400,448,517,521,532,536,577,584,644,656,704]⟩,
   ⟨679,444685627425,444685627650⟩⟩
theorem r0342_checked : check r0342 = true := by decide +kernel

-- six_orbit_dags/m11e12k2p0q3_types23.json.gz, graph 248, terminal 11; projection:R_multi_six_0199.
noncomputable def r0343 : Entry :=
  ⟨⟨[63,118,327,362,452,496,541,724,779,901,952],[7,11,29,42,54,56,70,84,98,112,196,208,259,261,266,296,322,324,352,388,432,448,517,521,532,536,644,656,769,776,896]⟩,
   ⟨680,453242007585,581587710210⟩⟩
theorem r0343_checked : check r0343 = true := by decide +kernel

-- six_orbit_dags/m11e13k2p0q4_types22.json.gz, graph 264, terminal 3; projection:R_multi_six_0189.
noncomputable def r0344 : Entry :=
  ⟨⟨[63,118,199,376,468,651,738,797,810,901,992],[7,11,29,42,54,56,70,84,98,112,131,133,194,196,276,280,296,336,352,388,448,521,522,546,641,642,736,773,776,800,896]⟩,
   ⟨677,582338420805,521939272530⟩⟩
theorem r0344_checked : check r0344 = true := by decide +kernel

-- six_orbit_dags/m11e13k2p0q4_types23.json.gz, graph 265, terminal 0; projection:R_multi_six_0188.
noncomputable def r0345 : Entry :=
  ⟨⟨[63,93,182,331,426,647,724,837,888,899,944],[7,11,29,42,54,56,69,73,84,88,134,148,162,176,259,266,296,321,328,386,416,517,580,592,643,644,656,769,816,832,896]⟩,
   ⟨676,590395491105,590395678980⟩⟩
theorem r0345_checked : check r0345 = true := by decide +kernel

-- six_orbit_dags/m11e13k3p1q5_types125.json.gz, graph 279, terminal 5; projection:R_multi_six_0147.
noncomputable def r0346 : Entry :=
  ⟨⟨[63,195,250,331,364,647,662,781,820,961,1008],[7,11,13,22,44,52,58,67,74,104,131,146,193,194,240,265,268,292,321,328,352,517,532,641,646,656,769,772,816,960]⟩,
   ⟨649,654819263025,654819267075⟩⟩
theorem r0346_checked : check r0346 = true := by decide +kernel

-- six_orbit_dags/m11e13k3p1q5_types125.json.gz, graph 279, terminal 9; projection:R_multi_six_0148.
noncomputable def r0347 : Entry :=
  ⟨⟨[63,86,199,244,496,587,653,826,850,940,961],[7,11,13,22,44,52,58,67,70,82,84,133,164,193,196,240,304,336,416,448,521,522,577,578,641,652,786,808,832,896]⟩,
   ⟨650,444937286145,509110137345⟩⟩
theorem r0347_checked : check r0347 = true := by decide +kernel

-- six_orbit_dags/m11e13k3p1q5_types125.json.gz, graph 279, terminal 12; projection:R_multi_six_0149.
noncomputable def r0348 : Entry :=
  ⟨⟨[63,116,205,236,496,583,651,826,854,936,961],[7,11,13,22,44,52,58,69,84,100,112,137,168,193,204,224,304,336,416,448,515,522,577,582,641,648,786,808,832,896]⟩,
   ⟨651,444936290865,509109146115⟩⟩
theorem r0348_checked : check r0348 = true := by decide +kernel

-- six_orbit_dags/m11e13k3p1q5_types125.json.gz, graph 279, terminal 13; projection:R_multi_six_0150.
noncomputable def r0349 : Entry :=
  ⟨⟨[63,86,244,327,466,684,717,779,826,944,961],[7,11,13,22,44,52,58,69,70,82,84,164,176,196,208,259,274,321,322,400,448,521,552,652,672,705,769,778,816,896]⟩,
   ⟨652,444936298545,509109146370⟩⟩
theorem r0349_checked : check r0349 = true := by decide +kernel

-- six_orbit_dags/m11e13k3p1q5_types125.json.gz, graph 279, terminal 14; projection:R_multi_six_0151.
noncomputable def r0350 : Entry :=
  ⟨⟨[63,86,244,327,466,589,748,779,826,944,961],[7,11,13,22,44,52,58,69,70,82,84,176,208,228,259,274,321,322,400,448,521,552,577,588,672,704,769,778,816,896]⟩,
   ⟨653,509110137345,444937286145⟩⟩
theorem r0350_checked : check r0350 = true := by decide +kernel

-- six_orbit_dags/m11e13k3p1q5_types125.json.gz, graph 279, terminal 15; projection:R_multi_six_0152.
noncomputable def r0351 : Entry :=
  ⟨⟨[63,199,244,342,464,653,684,826,843,944,961],[7,11,13,22,44,52,58,67,70,84,133,164,176,193,196,208,274,322,336,400,448,521,552,641,652,672,778,816,833,896]⟩,
   ⟨654,444936299265,509109150465⟩⟩
theorem r0351_checked : check r0351 = true := by decide +kernel

-- six_orbit_dags/m11e13k3p1q5_types135.json.gz, graph 280, terminal 1; projection:R_multi_six_0146.
noncomputable def r0352 : Entry :=
  ⟨⟨[63,116,342,391,466,651,698,752,781,876,961],[7,11,13,22,44,52,58,84,100,112,131,146,208,261,262,324,338,385,386,448,521,552,608,641,650,688,704,769,780,832]⟩,
   ⟨648,452989354545,577560187395⟩⟩
theorem r0352_checked : check r0352 = true := by decide +kernel

-- six_orbit_dags/m11e13k3p2q6_types055.json.gz, graph 288, terminal 0; integer:52.
noncomputable def r0353 : Entry :=
  ⟨⟨[63,199,331,397,428,449,692,726,824,858,992],[7,11,13,22,26,44,52,56,67,133,164,193,198,265,296,321,330,385,396,416,448,560,594,660,672,704,792,800,832]⟩,
   ⟨1984,590395748880,590395748880⟩⟩
theorem r0353_checked : check r0353 = true := by decide +kernel

-- six_orbit_dags/m11e13k3p2q6_types055.json.gz, graph 288, terminal 1; integer:53.
noncomputable def r0354 : Entry :=
  ⟨⟨[63,86,218,327,372,651,696,781,812,963,1008],[7,11,13,22,26,44,52,56,70,82,84,138,152,194,208,261,292,323,324,368,521,552,643,648,688,769,780,800,960]⟩,
   ⟨1985,578064495120,521441391120⟩⟩
theorem r0354_checked : check r0354 = true := by decide +kernel

-- six_orbit_dags/m11e13k3p2q6_types155.json.gz, graph 289, terminal 2; projection:R_multi_six_0145.
noncomputable def r0355 : Entry :=
  ⟨⟨[63,195,214,391,436,587,634,781,812,961,1008],[7,11,13,22,44,52,58,67,82,131,134,148,193,194,208,261,292,385,388,432,521,552,577,586,624,769,780,800,960]⟩,
   ⟨647,449214480945,517162209795⟩⟩
theorem r0355_checked : check r0355 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types01.json.gz, graph 297, terminal 4; projection:R_multi_six_0046.
noncomputable def r0356 : Entry :=
  ⟨⟨[63,116,205,236,395,440,449,598,775,794,837,1008],[7,11,13,22,26,44,52,56,69,84,100,112,137,168,193,204,224,259,266,280,321,385,392,432,448,518,530,580,592,770,773,784,832]⟩,
   ⟨569,517913719365,517912736340⟩⟩
theorem r0356_checked : check r0356 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types01.json.gz, graph 297, terminal 10; projection:R_multi_six_0045.
noncomputable def r0357 : Entry :=
  ⟨⟨[63,75,150,248,333,364,436,647,730,835,901,992],[7,11,13,22,26,44,52,56,67,73,74,104,134,146,148,176,216,224,261,292,321,332,352,388,416,515,578,642,645,704,769,832,896]⟩,
   ⟨568,582342681345,521944703745⟩⟩
theorem r0357_checked : check r0357 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types01.json.gz, graph 297, terminal 11; projection:R_multi_six_0048.
noncomputable def r0358 : Entry :=
  ⟨⟨[63,86,199,346,376,450,653,756,779,812,899,992],[7,11,13,22,26,44,52,56,70,82,84,112,131,133,194,196,266,296,322,344,352,386,448,521,524,548,641,644,736,771,776,800,896]⟩,
   ⟨570,654568599585,654568599810⟩⟩
theorem r0358_checked : check r0358 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types01.json.gz, graph 297, terminal 13; projection:R_multi_six_0049.
noncomputable def r0359 : Entry :=
  ⟨⟨[63,77,150,244,331,364,440,647,709,835,922,992],[7,11,13,22,26,44,52,56,69,73,76,100,134,146,148,176,196,224,266,296,323,328,352,408,416,515,577,642,645,704,770,832,896]⟩,
   ⟨571,654563160645,654563160645⟩⟩
theorem r0359_checked : check r0359 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types01.json.gz, graph 297, terminal 14; projection:R_multi_six_0050.
noncomputable def r0360 : Entry :=
  ⟨⟨[63,203,236,333,449,534,666,696,775,884,899,992],[7,11,13,22,26,44,52,56,73,76,100,131,138,168,193,200,224,261,321,324,385,448,518,530,532,560,642,664,672,771,772,864,896]⟩,
   ⟨572,590144078625,590144086275⟩⟩
theorem r0360_checked : check r0360 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types02.json.gz, graph 298, terminal 2; projection:R_multi_six_0035.
noncomputable def r0361 : Entry :=
  ⟨⟨[63,116,197,214,391,410,589,620,779,824,961,1008],[7,11,13,22,26,44,52,56,69,84,100,112,133,134,146,193,196,208,259,266,280,385,386,400,521,552,577,588,608,769,776,816,960]⟩,
   ⟨561,517913849925,517912736850⟩⟩
theorem r0361_checked : check r0361 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types02.json.gz, graph 298, terminal 3; projection:R_multi_six_0033.
noncomputable def r0362 : Entry :=
  ⟨⟨[63,116,197,214,391,410,589,620,752,779,952,961],[7,11,13,22,26,44,52,56,69,84,100,112,133,134,146,193,196,208,259,266,385,386,408,521,552,577,588,608,688,704,769,776,896]⟩,
   ⟨559,590391423045,590390309970⟩⟩
theorem r0362_checked : check r0362 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types02.json.gz, graph 298, terminal 12; projection:R_multi_six_0034.
noncomputable def r0363 : Entry :=
  ⟨⟨[63,116,195,214,327,364,651,666,781,824,961,1008],[7,11,13,22,26,44,52,56,67,70,84,100,112,131,146,193,194,208,261,268,296,321,324,352,521,536,641,650,656,769,776,816,960]⟩,
   ⟨560,582338359365,521939268690⟩⟩
theorem r0363_checked : check r0363 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types02.json.gz, graph 298, terminal 13; projection:R_multi_six_0029.
noncomputable def r0364 : Entry :=
  ⟨⟨[63,116,139,327,364,397,598,666,707,880,952,961],[7,11,13,22,26,44,52,56,67,70,84,100,112,131,137,138,261,268,296,321,324,352,385,392,530,578,592,642,664,705,816,832,896]⟩,
   ⟨555,521441387280,578064491280⟩⟩
theorem r0364_checked : check r0364 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types02.json.gz, graph 298, terminal 14; projection:R_multi_six_0032.
noncomputable def r0365 : Entry :=
  ⟨⟨[63,71,214,372,410,464,589,620,707,824,907,992],[7,11,13,22,26,44,52,56,67,69,70,84,100,146,194,208,280,304,336,352,394,400,448,521,552,577,588,608,643,704,776,800,896]⟩,
   ⟨558,590395748385,590395748610⟩⟩
theorem r0365_checked : check r0365 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types02.json.gz, graph 298, terminal 19; projection:R_multi_six_0030.
noncomputable def r0366 : Entry :=
  ⟨⟨[63,77,135,372,406,453,587,620,666,707,952,992],[7,11,13,22,26,44,52,56,69,73,76,100,131,133,134,146,193,276,304,324,352,388,400,448,522,552,579,584,608,642,664,704,928]⟩,
   ⟨556,521441390625,578064494850⟩⟩
theorem r0366_checked : check r0366 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types02.json.gz, graph 298, terminal 20; projection:R_multi_six_0027.
noncomputable def r0367 : Entry :=
  ⟨⟨[63,71,139,218,397,428,451,598,760,820,837,992],[7,11,13,22,26,44,52,56,67,69,70,82,131,137,138,168,194,216,261,292,321,385,396,416,448,532,560,580,592,736,772,800,832]⟩,
   ⟨553,650290409505,646515536130⟩⟩
theorem r0367_checked : check r0367 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types02.json.gz, graph 298, terminal 25; projection:R_multi_six_0031.
noncomputable def r0368 : Entry :=
  ⟨⟨[63,77,135,372,406,453,587,620,707,824,922,992],[7,11,13,22,26,44,52,56,69,73,76,100,131,133,134,193,276,304,324,352,388,402,448,522,552,579,584,608,642,704,792,800,896]⟩,
   ⟨557,521441390625,578064494850⟩⟩
theorem r0368_checked : check r0368 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types02.json.gz, graph 298, terminal 26; projection:R_multi_six_0028.
noncomputable def r0369 : Entry :=
  ⟨⟨[63,71,139,397,428,451,598,696,730,820,837,992],[7,11,13,22,26,44,52,56,67,69,70,131,137,138,168,194,261,292,321,385,396,416,448,532,560,580,594,664,672,704,772,800,832]⟩,
   ⟨554,650290406145,646515532545⟩⟩
theorem r0369_checked : check r0369 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types02.json.gz, graph 298, terminal 27; projection:R_multi_six_0024.
noncomputable def r0370 : Entry :=
  ⟨⟨[63,71,141,236,395,453,598,628,794,835,952,992],[7,11,13,22,26,44,52,56,67,69,70,100,133,137,140,168,196,224,259,266,321,385,392,448,530,560,578,596,608,770,792,832,928]⟩,
   ⟨550,517918175265,517918175490⟩⟩
theorem r0370_checked : check r0370 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types02.json.gz, graph 298, terminal 28; projection:R_multi_six_0025.
noncomputable def r0371 : Entry :=
  ⟨⟨[63,71,141,236,395,453,598,628,696,835,922,992],[7,11,13,22,26,44,52,56,67,69,70,100,133,137,140,168,196,224,259,321,385,394,448,530,560,578,596,608,664,672,770,832,896]⟩,
   ⟨551,517918175745,517918175745⟩⟩
theorem r0371_checked : check r0371 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types02.json.gz, graph 298, terminal 29; projection:R_multi_six_0022.
noncomputable def r0372 : Entry :=
  ⟨⟨[63,86,139,372,410,440,583,653,748,850,899,992],[7,11,13,22,26,44,52,56,70,82,84,100,131,137,138,168,274,304,336,352,386,408,416,515,517,578,580,641,652,736,770,832,896]⟩,
   ⟨548,581587709985,453242007810⟩⟩
theorem r0372_checked : check r0372 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types02.json.gz, graph 298, terminal 30; projection:R_multi_six_0026.
noncomputable def r0373 : Entry :=
  ⟨⟨[63,86,139,236,372,410,440,583,717,850,899,992],[7,11,13,22,26,44,52,56,70,82,84,100,131,137,138,168,204,224,274,304,336,352,386,408,416,515,578,581,641,704,770,832,896]⟩,
   ⟨552,581587706640,453242004240⟩⟩
theorem r0373_checked : check r0373 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types02.json.gz, graph 298, terminal 31; projection:R_multi_six_0023.
noncomputable def r0374 : Entry :=
  ⟨⟨[63,71,333,395,428,449,598,666,696,707,884,992],[7,11,13,22,26,44,52,56,67,69,70,131,138,168,193,265,268,292,321,324,385,392,416,448,530,560,578,596,642,664,672,704,864]⟩,
   ⟨549,521944707105,582342684930⟩⟩
theorem r0374_checked : check r0374 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types02.json.gz, graph 298, terminal 32; projection:R_multi_six_0021.
noncomputable def r0375 : Entry :=
  ⟨⟨[63,346,395,440,450,519,598,653,684,707,884,992],[7,11,13,22,26,44,52,56,82,131,137,168,194,266,280,304,322,336,386,392,416,448,515,517,518,548,578,596,641,652,672,704,864]⟩,
   ⟨547,453241996065,581587706115⟩⟩
theorem r0375_checked : check r0375 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types02.json.gz, graph 298, terminal 34; projection:R_multi_six_0036.
noncomputable def r0376 : Entry :=
  ⟨⟨[63,90,150,244,391,466,587,632,781,835,940,992],[7,11,13,22,26,44,52,56,74,82,88,112,134,146,148,164,208,224,259,261,322,386,388,448,521,552,579,584,608,769,780,832,928]⟩,
   ⟨562,646263877665,646263877890⟩⟩
theorem r0376_checked : check r0376 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types02.json.gz, graph 298, terminal 35; projection:R_multi_six_0037.
noncomputable def r0377 : Entry :=
  ⟨⟨[63,90,150,199,436,466,587,632,653,880,940,961],[7,11,13,22,26,44,52,56,67,74,82,88,133,134,146,148,193,194,304,336,400,420,448,521,552,577,584,624,641,652,800,832,896]⟩,
   ⟨563,521944703760,582342681360⟩⟩
theorem r0377_checked : check r0377 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types02.json.gz, graph 298, terminal 36; projection:R_multi_six_0041.
noncomputable def r0378 : Entry :=
  ⟨⟨[63,77,150,364,391,436,587,666,760,837,899,992],[7,11,13,22,26,44,52,56,69,73,76,104,134,146,148,176,261,292,324,352,387,388,416,515,522,577,584,642,664,736,769,832,896]⟩,
   ⟨567,453241996065,581587706115⟩⟩
theorem r0378_checked : check r0378 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types02.json.gz, graph 298, terminal 37; projection:R_multi_six_0039.
noncomputable def r0379 : Entry :=
  ⟨⟨[63,77,150,248,364,391,436,587,730,837,899,992],[7,11,13,22,26,44,52,56,69,73,76,104,134,146,148,176,216,224,261,292,324,352,387,388,416,515,577,586,642,704,769,832,896]⟩,
   ⟨565,650284970565,646510096965⟩⟩
theorem r0379_checked : check r0379 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types02.json.gz, graph 298, terminal 40; projection:R_multi_six_0038.
noncomputable def r0380 : Entry :=
  ⟨⟨[63,77,108,244,331,488,662,709,775,794,952,961],[7,11,13,22,26,44,52,56,69,73,76,100,104,148,176,196,224,259,266,321,328,424,448,517,518,530,644,656,705,769,770,792,896]⟩,
   ⟨564,578064491280,521441387280⟩⟩
theorem r0380_checked : check r0380 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types02.json.gz, graph 298, terminal 41; projection:R_multi_six_0040.
noncomputable def r0381 : Entry :=
  ⟨⟨[63,77,150,331,376,410,620,647,692,837,899,1008],[7,11,13,22,26,44,52,56,69,73,76,104,134,146,148,259,266,280,321,328,368,386,400,517,548,580,608,643,644,688,769,832,896]⟩,
   ⟨566,646515532560,650290406160⟩⟩
theorem r0381_checked : check r0381 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types03.json.gz, graph 299, terminal 1; projection:R_multi_six_0016.
noncomputable def r0382 : Entry :=
  ⟨⟨[63,116,342,395,410,583,620,653,696,835,897,1008],[7,11,13,22,26,44,52,56,70,84,100,112,137,152,259,274,322,336,385,394,400,517,524,552,579,580,608,641,648,688,769,832,896]⟩,
   ⟨542,521939268165,582337245765⟩⟩
theorem r0382_checked : check r0382 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types03.json.gz, graph 299, terminal 2; projection:R_multi_six_0015.
noncomputable def r0383 : Entry :=
  ⟨⟨[63,90,135,331,376,451,628,662,722,812,909,992],[7,11,13,22,26,44,52,56,74,82,88,112,131,133,134,194,265,296,323,328,352,385,448,532,548,592,608,644,658,704,780,800,896]⟩,
   ⟨541,654568599585,654568599810⟩⟩
theorem r0383_checked : check r0383 = true := by decide +kernel

#print axioms r0320_checked

end Nonrational.OldTerminalMatches.M005
