module
prelude
public import InducedTerminalMatches.Basic

@[expose] public section

/-! Exact full-boundary matches, batch 6. Both facet and polygon
families are checked in both directions after the recorded permutation. -/

namespace Nonrational.OldTerminalMatches.M006
open Nonrational.InducedTerminalMatches
set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- six_orbit_dags/m12e12k2p0q3_types03.json.gz, graph 299, terminal 3; projection:R_multi_six_0012.
noncomputable def r0384 : Entry :=
  ⟨⟨[63,71,139,410,440,451,598,684,717,820,850,992],[7,11,13,22,26,44,52,56,67,69,70,131,137,138,168,193,274,304,322,386,408,416,448,532,548,580,594,652,672,704,784,800,832]⟩,
   ⟨538,650290406160,646515532560⟩⟩
theorem r0384_checked : check r0384 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types03.json.gz, graph 299, terminal 4; projection:R_multi_six_0011.
noncomputable def r0385 : Entry :=
  ⟨⟨[63,75,135,346,376,451,620,653,713,820,918,992],[7,11,13,22,26,44,52,56,67,73,74,104,131,133,134,193,274,304,322,344,352,386,448,524,548,584,608,644,649,704,788,800,896]⟩,
   ⟨537,650793722625,650793722625⟩⟩
theorem r0385_checked : check r0385 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types03.json.gz, graph 299, terminal 5; projection:R_multi_six_0013.
noncomputable def r0386 : Entry :=
  ⟨⟨[63,203,236,263,333,666,696,736,790,884,899,961],[7,11,13,22,26,44,52,56,73,76,100,131,138,168,193,200,224,259,261,262,321,324,530,560,608,642,664,672,704,770,788,832,897]⟩,
   ⟨539,509110136865,444937285890⟩⟩
theorem r0386_checked : check r0386 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types03.json.gz, graph 299, terminal 6; projection:R_multi_six_0014.
noncomputable def r0387 : Entry :=
  ⟨⟨[63,71,154,395,440,451,589,692,726,812,841,992],[7,11,13,22,26,44,52,56,67,69,70,138,146,152,176,194,265,296,321,387,392,416,448,524,548,580,585,660,672,704,776,800,832]⟩,
   ⟨540,654820257825,654820258050⟩⟩
theorem r0387_checked : check r0387 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types03.json.gz, graph 299, terminal 8; projection:R_multi_six_0017.
noncomputable def r0388 : Entry :=
  ⟨⟨[63,86,218,395,440,450,583,756,781,812,835,992],[7,11,13,22,26,44,52,56,70,82,84,138,152,176,194,208,259,265,296,322,386,392,416,448,517,548,579,580,736,769,780,800,832]⟩,
   ⟨543,646263866145,646263873795⟩⟩
theorem r0388_checked : check r0388 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types03.json.gz, graph 299, terminal 9; projection:R_multi_six_0020.
noncomputable def r0389 : Entry :=
  ⟨⟨[63,86,327,397,428,449,602,651,696,707,884,992],[7,11,13,22,26,44,52,56,67,70,82,84,137,168,193,261,292,321,324,385,396,416,448,522,536,560,578,592,643,648,672,704,864]⟩,
   ⟨546,582342684705,521944707330⟩⟩
theorem r0389_checked : check r0389 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types03.json.gz, graph 299, terminal 10; projection:R_multi_six_0019.
noncomputable def r0390 : Entry :=
  ⟨⟨[63,86,199,397,428,449,602,692,724,824,843,992],[7,11,13,22,26,44,52,56,67,70,82,84,133,164,193,196,265,296,321,385,396,416,448,536,560,586,592,660,672,704,776,800,832]⟩,
   ⟨545,444681290565,444680184915⟩⟩
theorem r0390_checked : check r0390 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types03.json.gz, graph 299, terminal 11; projection:R_multi_six_0018.
noncomputable def r0391 : Entry :=
  ⟨⟨[63,199,214,346,436,464,653,684,705,824,843,992],[7,11,13,22,26,44,52,56,67,82,133,148,164,193,198,208,280,304,330,336,400,416,448,521,552,577,641,652,672,704,776,800,832]⟩,
   ⟨544,509104694085,444931842885⟩⟩
theorem r0391_checked : check r0391 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types11.json.gz, graph 301, terminal 12; projection:R_multi_six_0124.
noncomputable def r0392 : Entry :=
  ⟨⟨[63,71,108,205,342,451,488,570,651,884,914,936],[7,11,13,22,44,52,58,67,69,70,76,100,104,131,137,193,200,274,322,340,352,386,424,448,522,530,552,560,642,648,784,800,896]⟩,
   ⟨638,452989358640,577560187440⟩⟩
theorem r0392_checked : check r0392 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types11.json.gz, graph 301, terminal 13; projection:R_multi_six_0126.
noncomputable def r0393 : Entry :=
  ⟨⟨[63,71,214,333,364,451,480,570,756,779,914,936],[7,11,13,22,44,52,58,67,69,70,100,146,194,212,224,259,265,296,321,332,352,386,416,448,522,530,552,560,656,672,770,776,896]⟩,
   ⟨640,444936290865,509109146115⟩⟩
theorem r0393_checked : check r0393 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types11.json.gz, graph 301, terminal 28; projection:R_multi_six_0125.
noncomputable def r0394 : Entry :=
  ⟨⟨[63,116,186,214,395,450,583,620,781,835,936,1008],[7,11,13,22,44,52,58,70,84,100,112,138,146,168,176,194,208,259,265,322,386,392,448,517,524,552,579,580,608,769,776,832,928]⟩,
   ⟨639,581586715185,453241016835⟩⟩
theorem r0394_checked : check r0394 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types11.json.gz, graph 301, terminal 40; projection:R_multi_six_0126.
noncomputable def r0395 : Entry :=
  ⟨⟨[63,150,314,368,395,466,647,692,752,781,876,961],[7,11,13,22,44,52,58,112,131,134,146,148,208,265,266,274,296,304,336,352,385,386,448,517,548,608,641,644,688,704,769,780,832]⟩,
   ⟨640,14783370390,87781705065⟩⟩
theorem r0395_checked : check r0395 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types11.json.gz, graph 301, terminal 41; projection:R_multi_six_0124.
noncomputable def r0396 : Entry :=
  ⟨⟨[63,186,240,308,397,492,651,722,775,790,880,961],[7,11,13,22,44,52,58,112,137,138,146,168,176,208,224,261,276,292,304,352,385,396,448,515,530,592,641,642,704,769,774,784,832]⟩,
   ⟨638,486139253910,88318571910⟩⟩
theorem r0396_checked : check r0396 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types11.json.gz, graph 301, terminal 60; projection:R_multi_six_0128.
noncomputable def r0397 : Entry :=
  ⟨⟨[63,116,199,236,397,449,570,598,779,835,936,1008],[7,11,13,22,44,52,58,67,70,84,100,112,133,140,168,193,196,224,265,321,385,392,448,522,530,552,560,578,592,771,776,832,928]⟩,
   ⟨641,444936298545,509109146370⟩⟩
theorem r0397_checked : check r0397 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types11.json.gz, graph 301, terminal 63; projection:R_multi_six_0130.
noncomputable def r0398 : Entry :=
  ⟨⟨[63,86,186,240,327,466,628,651,684,845,899,992],[7,11,13,22,44,52,58,70,82,84,112,138,146,168,176,208,224,259,322,325,386,448,521,524,548,580,608,643,648,672,769,832,896]⟩,
   ⟨643,517162213425,449214485250⟩⟩
theorem r0398_checked : check r0398 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types11.json.gz, graph 301, terminal 64; projection:R_multi_six_0129.
noncomputable def r0399 : Entry :=
  ⟨⟨[63,86,199,372,461,464,570,722,779,812,899,944],[7,11,13,22,44,52,58,70,82,84,131,194,197,208,265,268,292,304,324,336,385,400,448,522,530,552,560,642,656,771,776,800,896]⟩,
   ⟨642,444684640305,444684636930⟩⟩
theorem r0399_checked : check r0399 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types11.json.gz, graph 301, terminal 65; projection:R_multi_six_0125.
noncomputable def r0400 : Entry :=
  ⟨⟨[63,77,150,199,314,364,395,692,740,880,914,969],[7,11,13,22,44,52,58,69,73,76,100,131,134,146,148,193,196,266,274,296,304,328,352,386,393,560,608,656,676,704,784,832,896]⟩,
   ⟨639,69567203685,160004535960⟩⟩
theorem r0400_checked : check r0400 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types11.json.gz, graph 301, terminal 66; projection:R_multi_six_0128.
noncomputable def r0401 : Entry :=
  ⟨⟨[63,71,180,333,428,468,570,598,752,779,936,963],[7,11,13,22,44,52,58,67,69,70,84,148,164,176,208,265,268,321,324,388,424,448,522,530,552,560,578,592,672,704,771,776,896]⟩,
   ⟨641,150600247365,284860451190⟩⟩
theorem r0401_checked : check r0401 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types11.json.gz, graph 301, terminal 77; projection:R_multi_six_0130.
noncomputable def r0402 : Entry :=
  ⟨⟨[63,342,391,436,464,570,594,653,684,752,843,961],[7,11,13,22,44,52,58,82,133,164,176,208,259,262,276,322,336,385,388,400,448,521,522,530,552,560,578,592,641,652,672,704,833]⟩,
   ⟨643,225041782530,297013907505⟩⟩
theorem r0402_checked : check r0402 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types11.json.gz, graph 301, terminal 78; projection:R_multi_six_0129.
noncomputable def r0403 : Entry :=
  ⟨⟨[63,116,186,210,397,428,496,598,715,775,868,961],[7,11,13,22,44,52,58,82,84,100,112,137,138,146,168,176,194,208,261,292,352,385,396,416,448,515,518,578,580,705,769,772,832]⟩,
   ⟨642,301545887490,297030742065⟩⟩
theorem r0403_checked : check r0403 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types11.json.gz, graph 301, terminal 99; projection:R_multi_six_0135.
noncomputable def r0404 : Entry :=
  ⟨⟨[63,203,236,240,323,378,653,692,775,790,961,976],[7,11,13,22,44,52,58,67,74,104,112,137,140,164,176,193,200,208,224,259,274,321,322,336,517,532,641,644,656,769,774,784,960]⟩,
   ⟨644,650793726465,650793726465⟩⟩
theorem r0404_checked : check r0404 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types11.json.gz, graph 301, terminal 100; projection:R_multi_six_0136.
noncomputable def r0405 : Entry :=
  ⟨⟨[63,195,250,391,406,464,587,620,781,820,880,961],[7,11,13,22,44,52,58,67,74,104,112,131,146,193,194,208,261,276,336,385,390,400,448,521,524,548,577,584,608,769,772,816,832]⟩,
   ⟨645,590395748865,590395748865⟩⟩
theorem r0405_checked : check r0405 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types11.json.gz, graph 301, terminal 104; projection:R_multi_six_0136.
noncomputable def r0406 : Entry :=
  ⟨⟨[63,77,135,364,406,453,587,698,707,820,872,976],[7,11,13,22,44,52,58,69,73,76,131,133,134,146,193,276,292,324,360,388,400,448,522,552,560,579,584,642,656,704,784,800,832]⟩,
   ⟨645,172223579655,446715611505⟩⟩
theorem r0406_checked : check r0406 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types11.json.gz, graph 301, terminal 105; projection:R_multi_six_0135.
noncomputable def r0407 : Entry :=
  ⟨⟨[63,108,135,214,333,453,628,698,779,872,899,976],[7,11,13,22,44,52,58,76,84,100,104,131,133,134,146,196,208,265,325,328,385,448,522,552,560,592,608,642,656,771,776,832,896]⟩,
   ⟨644,176501769735,575564630385⟩⟩
theorem r0407_checked : check r0407 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types11.json.gz, graph 301, terminal 106; projection:R_multi_six_0138.
noncomputable def r0408 : Entry :=
  ⟨⟨[63,86,199,333,364,449,628,651,722,826,905,992],[7,11,13,22,44,52,58,69,70,82,84,100,131,193,194,265,296,321,332,352,385,448,522,530,560,592,608,642,649,704,776,800,896]⟩,
   ⟨646,444684632625,444684636675⟩⟩
theorem r0408_checked : check r0408 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types11.json.gz, graph 301, terminal 107; projection:R_multi_six_0138.
noncomputable def r0409 : Entry :=
  ⟨⟨[63,199,244,331,342,368,653,684,705,826,841,992],[7,11,13,22,44,52,58,67,70,84,112,133,164,193,196,224,266,274,304,322,329,336,352,521,552,577,641,652,672,704,776,800,832]⟩,
   ⟨646,79611364935,442419468435⟩⟩
theorem r0409_checked : check r0409 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types12.json.gz, graph 302, terminal 55; projection:R_multi_six_0105.
noncomputable def r0410 : Entry :=
  ⟨⟨[63,186,203,232,278,391,620,752,820,845,914,961],[7,11,13,22,44,52,58,73,104,131,138,146,168,176,193,200,224,261,262,274,276,385,386,548,560,588,608,656,704,772,784,833,896]⟩,
   ⟨621,654568600065,654568600065⟩⟩
theorem r0410_checked : check r0410 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types12.json.gz, graph 302, terminal 56; projection:R_multi_six_0104.
noncomputable def r0411 : Entry :=
  ⟨⟨[63,186,203,232,278,333,391,752,820,876,914,961],[7,11,13,22,44,52,58,73,104,131,138,146,168,176,193,200,224,261,262,274,276,321,332,385,386,560,608,656,704,784,804,832,896]⟩,
   ⟨620,654568600065,654568600065⟩⟩
theorem r0411_checked : check r0411 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types12.json.gz, graph 302, terminal 57; projection:R_multi_six_0106.
noncomputable def r0412 : Entry :=
  ⟨⟨[63,150,199,314,331,338,397,692,722,880,940,961],[7,11,13,22,44,52,58,67,82,133,134,146,148,193,194,265,266,274,296,304,321,322,336,385,396,560,592,656,676,704,800,832,896]⟩,
   ⟨622,646514549505,650289423105⟩⟩
theorem r0412_checked : check r0412 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types12.json.gz, graph 302, terminal 59; projection:R_multi_six_0107.
noncomputable def r0413 : Entry :=
  ⟨⟨[63,150,199,314,331,338,692,722,812,880,909,961],[7,11,13,22,44,52,58,67,82,133,134,146,148,193,194,265,266,274,296,304,321,322,336,548,560,592,644,656,704,780,800,832,897]⟩,
   ⟨623,578063508225,521440404225⟩⟩
theorem r0413_checked : check r0413 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types12.json.gz, graph 302, terminal 63; projection:R_multi_six_0108.
noncomputable def r0414 : Entry :=
  ⟨⟨[63,150,199,314,331,338,653,692,722,812,880,969],[7,11,13,22,44,52,58,67,82,133,134,146,148,193,194,266,274,296,304,322,329,336,524,548,560,592,644,649,656,704,776,800,832]⟩,
   ⟨624,578064483105,521441386755⟩⟩
theorem r0414_checked : check r0414 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types12.json.gz, graph 302, terminal 81; projection:R_multi_six_0109.
noncomputable def r0415 : Entry :=
  ⟨⟨[63,108,150,203,333,372,391,698,744,880,916,961],[7,11,13,22,44,52,58,73,76,100,104,131,134,138,146,148,193,200,261,276,321,324,368,385,388,560,608,656,680,704,784,832,896]⟩,
   ⟨625,521441391120,578064495120⟩⟩
theorem r0415_checked : check r0415 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types12.json.gz, graph 302, terminal 82; projection:R_multi_six_0110.
noncomputable def r0416 : Entry :=
  ⟨⟨[63,116,150,199,333,364,395,698,724,880,936,961],[7,11,13,22,44,52,58,69,84,100,112,131,134,138,146,148,193,196,265,296,321,332,352,385,392,560,592,656,680,704,800,832,896]⟩,
   ⟨626,517163189025,449215471875⟩⟩
theorem r0416_checked : check r0416 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types12.json.gz, graph 302, terminal 112; projection:R_multi_six_0112.
noncomputable def r0417 : Entry :=
  ⟨⟨[63,71,205,244,342,464,651,684,826,835,944,961],[7,11,13,22,44,52,58,67,69,70,84,137,140,164,176,193,196,208,274,322,336,400,448,515,522,552,641,648,672,770,816,833,896]⟩,
   ⟨628,444684632625,444684636675⟩⟩
theorem r0417_checked : check r0417 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types12.json.gz, graph 302, terminal 113; projection:R_multi_six_0111.
noncomputable def r0418 : Entry :=
  ⟨⟨[63,199,214,323,378,653,692,720,779,812,880,961],[7,11,13,22,44,52,58,67,82,133,148,193,198,208,259,266,296,321,322,368,521,524,548,560,592,641,644,656,704,769,776,800,832]⟩,
   ⟨627,578063499825,521440399875⟩⟩
theorem r0418_checked : check r0418 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types12.json.gz, graph 302, terminal 115; projection:R_multi_six_0113.
noncomputable def r0419 : Entry :=
  ⟨⟨[63,214,327,372,464,587,698,706,781,812,944,961],[7,11,13,22,44,52,58,67,70,84,146,194,208,261,292,304,321,324,336,400,448,521,522,552,577,578,642,688,704,769,780,800,896]⟩,
   ⟨629,448711172145,448711168770⟩⟩
theorem r0419_checked : check r0419 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types12.json.gz, graph 302, terminal 116; projection:R_multi_six_0114.
noncomputable def r0420 : Entry :=
  ⟨⟨[63,71,86,244,331,466,684,709,781,826,944,961],[7,11,13,22,44,52,58,67,69,70,82,84,164,176,196,208,265,266,274,321,322,400,448,517,524,552,644,672,705,769,776,816,896]⟩,
   ⟨630,509110125345,444937281795⟩⟩
theorem r0420_checked : check r0420 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types12.json.gz, graph 302, terminal 117; projection:R_multi_six_0115.
noncomputable def r0421 : Entry :=
  ⟨⟨[63,203,236,397,436,480,579,634,775,790,880,961],[7,11,13,22,44,52,58,67,74,104,137,140,164,193,200,224,261,276,304,352,385,388,416,448,515,530,577,578,624,769,774,784,832]⟩,
   ⟨631,517917180465,517917184515⟩⟩
theorem r0421_checked : check r0421 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types12.json.gz, graph 302, terminal 121; projection:R_multi_six_0118.
noncomputable def r0422 : Entry :=
  ⟨⟨[63,214,300,397,436,496,634,647,706,779,872,961],[7,11,13,22,44,52,58,82,112,133,134,148,194,208,265,268,292,296,352,385,388,432,448,515,522,578,616,641,642,704,769,776,832]⟩,
   ⟨634,449215476240,517163201040⟩⟩
theorem r0422_checked : check r0422 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types12.json.gz, graph 302, terminal 122; projection:R_multi_six_0117.
noncomputable def r0423 : Entry :=
  ⟨⟨[63,214,300,391,436,496,634,651,706,781,872,961],[7,11,13,22,44,52,58,82,112,131,134,148,194,208,261,268,292,296,352,385,388,432,448,521,522,578,616,641,642,704,769,776,832]⟩,
   ⟨633,449215476240,517163201040⟩⟩
theorem r0423_checked : check r0423 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types12.json.gz, graph 302, terminal 124; projection:R_multi_six_0116.
noncomputable def r0424 : Entry :=
  ⟨⟨[63,150,199,244,325,364,496,651,781,826,914,961],[7,11,13,22,44,52,58,69,100,131,134,146,148,193,196,240,261,268,296,304,321,324,352,400,448,521,522,641,642,769,776,786,896]⟩,
   ⟨632,444684636720,444684636720⟩⟩
theorem r0424_checked : check r0424 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types12.json.gz, graph 302, terminal 128; projection:R_multi_six_0119.
noncomputable def r0425 : Entry :=
  ⟨⟨[63,116,139,333,342,391,620,698,713,880,914,961],[7,11,13,22,44,52,58,73,76,84,100,112,131,137,138,261,262,274,321,324,336,385,386,552,560,584,608,648,658,705,784,832,896]⟩,
   ⟨635,517162213425,449214485250⟩⟩
theorem r0425_checked : check r0425 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types12.json.gz, graph 302, terminal 131; projection:R_multi_six_0121.
noncomputable def r0426 : Entry :=
  ⟨⟨[63,116,197,214,333,364,496,647,698,779,936,961],[7,11,13,22,44,52,58,69,84,100,112,133,134,146,176,193,196,208,265,296,321,332,352,416,448,515,522,641,642,680,769,776,896]⟩,
   ⟨637,448712159745,448712159745⟩⟩
theorem r0426_checked : check r0426 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types12.json.gz, graph 302, terminal 132; projection:R_multi_six_0120.
noncomputable def r0427 : Entry :=
  ⟨⟨[63,116,214,327,442,450,589,620,752,779,936,961],[7,11,13,22,44,52,58,69,70,84,100,112,146,176,194,208,259,266,321,322,386,424,448,521,552,577,588,608,672,704,769,776,896]⟩,
   ⟨636,577561178625,452990349825⟩⟩
theorem r0427_checked : check r0427 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types13.json.gz, graph 303, terminal 4; projection:R_multi_six_0090.
noncomputable def r0428 : Entry :=
  ⟨⟨[63,86,203,314,394,466,583,628,653,880,940,961],[7,11,13,22,44,52,58,67,70,82,84,137,138,193,194,266,274,296,304,336,386,392,448,517,548,577,580,624,641,652,800,832,896]⟩,
   ⟨606,646262882865,646262886915⟩⟩
theorem r0428_checked : check r0428 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types13.json.gz, graph 303, terminal 5; projection:R_multi_six_0089.
noncomputable def r0429 : Entry :=
  ⟨⟨[63,186,202,308,327,470,587,744,781,812,944,961],[7,11,13,22,44,52,58,67,74,138,146,168,176,194,200,261,276,292,304,321,326,400,448,521,552,577,584,672,704,769,780,800,896]⟩,
   ⟨605,590144090625,590144090625⟩⟩
theorem r0429_checked : check r0429 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types13.json.gz, graph 303, terminal 54; projection:R_multi_six_0091.
noncomputable def r0430 : Entry :=
  ⟨⟨[63,186,203,210,308,496,583,653,812,854,936,961],[7,11,13,22,44,52,58,67,82,137,138,146,168,176,193,194,208,276,292,304,336,416,448,517,524,577,582,641,648,772,808,832,896]⟩,
   ⟨607,590143095345,590143099395⟩⟩
theorem r0430_checked : check r0430 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types13.json.gz, graph 303, terminal 56; projection:R_multi_six_0092.
noncomputable def r0431 : Entry :=
  ⟨⟨[63,180,314,331,338,496,583,662,722,781,940,961],[7,11,13,22,44,52,58,67,82,148,164,176,208,265,266,274,296,304,321,322,336,416,448,517,518,577,578,644,658,704,769,780,896]⟩,
   ⟨608,578063499825,521440399875⟩⟩
theorem r0431_checked : check r0431 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types13.json.gz, graph 303, terminal 68; projection:R_multi_six_0094.
noncomputable def r0432 : Entry :=
  ⟨⟨[63,71,86,186,333,428,651,722,835,884,905,944],[7,11,13,22,44,52,58,67,69,70,82,84,138,146,168,176,265,268,292,321,324,392,416,515,578,592,642,649,656,769,816,832,896]⟩,
   ⟨610,517163189025,449215471875⟩⟩
theorem r0432_checked : check r0432 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types13.json.gz, graph 303, terminal 69; projection:R_multi_six_0093.
noncomputable def r0433 : Entry :=
  ⟨⟨[63,71,214,314,395,402,589,628,707,812,905,1008],[7,11,13,22,44,52,58,67,69,70,84,131,146,194,208,266,274,296,304,386,393,400,521,524,548,577,580,624,641,704,776,800,896]⟩,
   ⟨609,577561166625,452990345475⟩⟩
theorem r0433_checked : check r0433 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types13.json.gz, graph 303, terminal 71; projection:R_multi_six_0096.
noncomputable def r0434 : Entry :=
  ⟨⟨[63,71,86,186,333,428,628,722,835,868,907,944],[7,11,13,22,44,52,58,67,69,70,82,84,138,146,168,176,265,268,292,321,324,392,416,560,578,592,612,642,656,771,800,832,896]⟩,
   ⟨612,581586715185,453241016835⟩⟩
theorem r0434_checked : check r0434 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types13.json.gz, graph 303, terminal 72; projection:R_multi_six_0095.
noncomputable def r0435 : Entry :=
  ⟨⟨[63,71,214,314,402,496,589,628,707,812,907,992],[7,11,13,22,44,52,58,67,69,70,84,112,146,194,208,266,274,296,304,386,400,480,521,524,548,577,580,608,643,704,776,800,896]⟩,
   ⟨611,509109142065,444936294915⟩⟩
theorem r0435_checked : check r0435 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types13.json.gz, graph 303, terminal 82; projection:R_multi_six_0097.
noncomputable def r0436 : Entry :=
  ⟨⟨[63,122,364,397,436,480,594,647,662,752,843,961],[7,11,13,22,44,52,58,74,82,104,112,133,148,176,224,265,268,292,328,352,385,388,416,448,515,530,578,592,641,646,656,704,833]⟩,
   ⟨613,582341689905,521943716355⟩⟩
theorem r0436_checked : check r0436 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types13.json.gz, graph 303, terminal 85; projection:R_multi_six_0098.
noncomputable def r0437 : Entry :=
  ⟨⟨[63,75,135,378,451,620,653,662,713,820,914,992],[7,11,13,22,44,52,58,67,73,74,104,131,133,134,193,274,304,322,352,386,448,524,532,548,584,608,644,649,658,704,784,800,896]⟩,
   ⟨614,582341689905,521943716355⟩⟩
theorem r0437_checked : check r0437 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types13.json.gz, graph 303, terminal 96; projection:R_multi_six_0099.
noncomputable def r0438 : Entry :=
  ⟨⟨[63,250,342,395,450,653,684,736,775,820,880,961],[7,11,13,22,44,52,58,82,112,137,138,168,194,224,259,262,276,322,336,385,386,448,517,548,608,641,652,672,704,769,772,816,832]⟩,
   ⟨615,654567604785,654567608835⟩⟩
theorem r0438_checked : check r0438 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types13.json.gz, graph 303, terminal 97; projection:R_multi_six_0102.
noncomputable def r0439 : Entry :=
  ⟨⟨[63,135,205,244,331,364,662,752,826,864,899,961],[7,11,13,22,44,52,58,73,76,100,131,133,134,148,193,196,240,259,266,296,321,328,352,530,560,608,642,656,704,770,800,832,897]⟩,
   ⟨618,509360800305,509360804355⟩⟩
theorem r0439_checked : check r0439 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types13.json.gz, graph 303, terminal 98; projection:R_multi_six_0101.
noncomputable def r0440 : Entry :=
  ⟨⟨[63,199,214,240,323,378,653,692,779,812,961,992],[7,11,13,22,44,52,58,67,82,112,133,148,176,193,198,208,224,259,266,296,321,322,352,521,524,548,641,644,672,769,776,800,960]⟩,
   ⟨617,578063499825,521440399875⟩⟩
theorem r0440_checked : check r0440 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types13.json.gz, graph 303, terminal 99; projection:R_multi_six_0100.
noncomputable def r0441 : Entry :=
  ⟨⟨[63,195,250,331,364,480,647,662,781,820,944,961],[7,11,13,22,44,52,58,67,74,104,131,146,176,193,194,224,265,268,292,321,328,352,416,448,517,532,641,646,656,769,772,816,896]⟩,
   ⟨616,654819263025,654819267075⟩⟩
theorem r0441_checked : check r0441 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types13.json.gz, graph 303, terminal 100; projection:R_multi_six_0103.
noncomputable def r0442 : Entry :=
  ⟨⟨[63,205,236,240,327,372,449,698,779,790,905,976],[7,11,13,22,44,52,58,69,100,112,137,168,176,193,204,208,224,259,262,276,321,324,336,385,448,522,530,648,656,770,777,784,896]⟩,
   ⟨619,448712159745,448712159745⟩⟩
theorem r0442_checked : check r0442 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types14.json.gz, graph 304, terminal 19; projection:R_multi_six_0088.
noncomputable def r0443 : Entry :=
  ⟨⟨[63,327,342,397,436,449,570,594,684,715,880,992],[7,11,13,22,44,52,58,67,82,137,140,164,193,261,276,304,321,326,336,385,388,416,448,522,530,552,560,578,592,648,672,704,864]⟩,
   ⟨604,452989354545,577560187395⟩⟩
theorem r0443_checked : check r0443 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types22.json.gz, graph 305, terminal 62; projection:R_multi_six_0187.
noncomputable def r0444 : Entry :=
  ⟨⟨[63,157,201,248,329,362,647,724,779,822,880,961],[7,11,29,42,54,56,73,104,112,133,137,148,152,193,200,208,265,266,290,321,328,352,515,518,532,592,641,644,704,769,770,816,832]⟩,
   ⟨675,6814987560,481944686985⟩⟩
theorem r0444_checked : check r0444 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types22.json.gz, graph 305, terminal 63; projection:R_multi_six_0186.
noncomputable def r0445 : Entry :=
  ⟨⟨[63,93,201,376,426,456,583,651,694,852,944,961],[7,11,29,42,54,56,69,73,84,88,137,138,162,193,200,296,304,328,336,392,416,448,515,518,532,577,580,641,642,688,784,832,896]⟩,
   ⟨674,26192672040,413258764665⟩⟩
theorem r0445_checked : check r0445 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types22.json.gz, graph 305, terminal 64; projection:R_multi_six_0187.
noncomputable def r0446 : Entry :=
  ⟨⟨[63,93,199,395,438,449,632,724,810,841,944,960],[7,11,29,42,54,56,69,73,84,88,131,134,148,193,196,265,266,290,321,385,386,432,448,552,560,584,592,656,704,776,800,832,896]⟩,
   ⟨675,654820246305,654820253955⟩⟩
theorem r0446_checked : check r0446 = true := by decide +kernel

-- six_orbit_dags/m12e12k2p0q3_types22.json.gz, graph 305, terminal 65; projection:R_multi_six_0186.
noncomputable def r0447 : Entry :=
  ⟨⟨[63,285,376,391,449,468,618,651,694,705,752,841],[7,11,29,42,54,56,104,112,131,134,148,193,208,261,265,276,280,321,328,336,385,388,448,521,522,546,577,584,608,641,642,688,704]⟩,
   ⟨674,577561166625,452990345475⟩⟩
theorem r0447_checked : check r0447 = true := by decide +kernel

#print axioms r0384_checked

end Nonrational.OldTerminalMatches.M006
