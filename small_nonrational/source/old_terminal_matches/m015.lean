module
prelude
public import InducedTerminalMatches.Basic

@[expose] public section

/-! Exact full-boundary matches, batch 15. Both facet and polygon
families are checked in both directions after the recorded permutation. -/

namespace Nonrational.OldTerminalMatches.M015
open Nonrational.InducedTerminalMatches
set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 227; projection:R_one_six_1179.
noncomputable def r0960 : Entry :=
  ⟨⟨[63,75,180,214,314,329,402,458,583,740,781,812,944,961],[7,11,13,22,44,52,58,67,70,73,74,146,148,164,176,194,196,265,266,274,296,304,321,328,386,400,448,517,548,577,580,672,704,769,780,800,896]⟩,
   ⟨1428,646262890545,646262887170⟩⟩
theorem r0960_checked : check r0960 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 263; projection:R_one_six_1180.
noncomputable def r0961 : Entry :=
  ⟨⟨[63,75,186,236,323,402,458,589,628,736,775,790,944,961],[7,11,13,22,44,52,58,67,73,74,76,100,138,146,168,176,200,224,259,274,321,322,386,400,448,517,532,560,577,580,608,672,704,769,774,784,896]⟩,
   ⟨1429,650289414705,646514545155⟩⟩
theorem r0961_checked : check r0961 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 301; projection:R_one_six_1181.
noncomputable def r0962 : Entry :=
  ⟨⟨[63,75,195,314,360,406,458,589,620,647,692,880,912,961],[7,11,13,22,44,52,58,67,73,74,104,131,134,148,193,194,266,274,296,304,328,352,386,400,448,517,548,560,577,588,608,641,644,656,784,832,896]⟩,
   ⟨1430,646262890545,646262887170⟩⟩
theorem r0962_checked : check r0962 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 480; projection:R_one_six_0979.
noncomputable def r0963 : Entry :=
  ⟨⟨[63,75,122,135,141,323,428,457,628,662,850,872,899,932],[7,11,13,22,44,52,58,67,73,74,82,104,112,131,133,134,137,140,259,296,321,322,328,385,392,420,530,532,548,592,608,642,644,770,800,832,896]⟩,
   ⟨1293,582342685185,521944707585⟩⟩
theorem r0963_checked : check r0963 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 481; projection:R_one_six_0977.
noncomputable def r0964 : Entry :=
  ⟨⟨[63,75,122,195,201,263,397,488,628,722,790,812,899,992],[7,11,13,22,44,52,58,67,73,74,82,104,112,131,137,193,194,200,259,261,262,268,296,385,392,480,530,532,548,592,608,642,704,770,772,800,896]⟩,
   ⟨1291,654819270705,654819267330⟩⟩
theorem r0964_checked : check r0964 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 482; projection:R_one_six_0981.
noncomputable def r0965 : Entry :=
  ⟨⟨[63,75,122,135,150,323,436,466,620,653,841,880,899,932],[7,11,13,22,44,52,58,67,73,74,82,104,112,131,133,134,146,148,259,304,321,322,336,386,400,420,521,524,548,584,608,641,644,769,800,832,896]⟩,
   ⟨1295,582342673185,521944703235⟩⟩
theorem r0965_checked : check r0965 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 483; projection:R_one_six_0980.
noncomputable def r0966 : Entry :=
  ⟨⟨[63,75,122,195,210,263,406,496,620,713,781,820,899,992],[7,11,13,22,44,52,58,67,73,74,82,104,112,131,146,193,194,208,259,261,262,276,304,386,400,480,521,524,548,584,608,641,704,769,772,800,896]⟩,
   ⟨1294,590395748385,590395748610⟩⟩
theorem r0966_checked : check r0966 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 555; projection:R_one_six_0986.
noncomputable def r0967 : Entry :=
  ⟨⟨[63,75,122,135,150,338,397,451,620,692,841,880,908,914],[7,11,13,22,44,52,58,67,73,74,82,104,112,131,133,134,146,148,265,274,321,322,336,385,386,396,524,548,560,584,608,644,656,776,784,832,896]⟩,
   ⟨1300,517917180465,517917184515⟩⟩
theorem r0967_checked : check r0967 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 607; projection:R_one_six_0983.
noncomputable def r0968 : Entry :=
  ⟨⟨[63,75,122,150,180,338,428,496,589,647,835,872,908,914],[7,11,13,22,44,52,58,67,73,74,82,104,112,134,146,148,164,176,274,296,322,336,352,396,400,416,515,517,524,577,584,642,644,770,776,832,896]⟩,
   ⟨1297,517917180465,517917184515⟩⟩
theorem r0968_checked : check r0968 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 608; projection:R_one_six_0982.
noncomputable def r0969 : Entry :=
  ⟨⟨[63,75,122,210,240,278,436,488,589,707,775,812,914,968],[7,11,13,22,44,52,58,67,73,74,82,104,112,146,176,194,208,224,262,274,276,292,296,400,416,456,515,517,524,577,584,642,704,770,772,776,896]⟩,
   ⟨1296,521943712305,582341693955⟩⟩
theorem r0969_checked : check r0969 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 635; projection:R_one_six_0978.
noncomputable def r0970 : Entry :=
  ⟨⟨[63,75,122,195,210,278,391,457,620,752,781,820,914,968],[7,11,13,22,44,52,58,67,73,74,82,104,112,131,146,193,194,208,261,262,265,274,276,385,386,456,524,548,560,584,608,656,704,772,776,784,896]⟩,
   ⟨1292,654820246305,654820253955⟩⟩
theorem r0970_checked : check r0970 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 655; projection:R_one_six_0985.
noncomputable def r0971 : Entry :=
  ⟨⟨[63,75,122,210,240,308,406,451,589,744,775,812,944,961],[7,11,13,22,44,52,58,67,73,74,82,104,112,146,176,194,208,224,259,262,276,292,304,386,400,449,517,524,552,577,584,672,704,769,772,800,896]⟩,
   ⟨1299,521943712305,582341693955⟩⟩
theorem r0971_checked : check r0971 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 663; projection:R_one_six_0984.
noncomputable def r0972 : Entry :=
  ⟨⟨[63,75,122,150,180,368,391,466,589,684,835,872,901,944],[7,11,13,22,44,52,58,67,73,74,82,104,112,134,146,148,164,176,259,304,322,336,352,386,389,400,517,524,552,577,584,644,672,769,800,832,896]⟩,
   ⟨1298,517917180465,517917184515⟩⟩
theorem r0972_checked : check r0972 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 853; projection:R_one_six_0999.
noncomputable def r0973 : Entry :=
  ⟨⟨[63,122,201,202,210,333,364,651,662,752,775,820,864,961],[7,11,13,22,44,52,58,73,74,82,104,112,137,138,146,193,194,200,208,261,292,321,332,352,515,518,532,560,608,641,642,656,704,769,772,800,832]⟩,
   ⟨1305,590394761265,590394757890⟩⟩
theorem r0973_checked : check r0973 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 854; projection:R_one_six_0997.
noncomputable def r0974 : Entry :=
  ⟨⟨[63,186,201,202,210,331,342,653,684,752,775,820,848,961],[7,11,13,22,44,52,58,73,74,82,137,138,146,168,176,193,194,200,208,259,262,276,321,322,336,517,548,560,592,641,652,672,704,769,772,784,832]⟩,
   ⟨1303,654567613185,654567613185⟩⟩
theorem r0974_checked : check r0974 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 855; projection:R_one_six_0998.
noncomputable def r0975 : Entry :=
  ⟨⟨[63,116,186,201,202,210,331,342,653,684,752,775,868,961],[7,11,13,22,44,52,58,73,74,82,84,100,112,137,138,146,168,176,193,194,200,208,259,262,321,322,324,517,548,608,641,652,672,704,769,772,832]⟩,
   ⟨1304,654567613185,654567613185⟩⟩
theorem r0975_checked : check r0975 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 858; projection:R_one_six_1011.
noncomputable def r0976 : Entry :=
  ⟨⟨[63,86,186,202,210,300,331,488,583,724,781,820,944,961],[7,11,13,22,44,52,58,67,70,74,82,84,138,146,168,176,194,200,208,265,268,292,296,321,328,416,448,517,532,577,580,656,704,769,772,816,896]⟩,
   ⟨1311,654568600080,654568600080⟩⟩
theorem r0976_checked : check r0976 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 859; projection:R_one_six_1012.
noncomputable def r0977 : Entry :=
  ⟨⟨[63,86,186,202,210,308,327,468,587,744,781,812,944,961],[7,11,13,22,44,52,58,67,70,74,82,84,138,146,168,176,194,200,208,261,276,292,304,321,324,400,448,521,552,577,584,672,704,769,780,800,896]⟩,
   ⟨1312,590144078625,590144086275⟩⟩
theorem r0977_checked : check r0977 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 860; projection:R_one_six_1009.
noncomputable def r0978 : Entry :=
  ⟨⟨[63,86,122,198,202,300,395,488,647,724,781,820,880,961],[7,11,13,22,44,52,58,70,74,82,84,104,112,131,134,138,194,196,200,265,268,292,296,352,385,392,448,517,532,592,641,644,704,769,772,816,832]⟩,
   ⟨1309,654820258320,654820258320⟩⟩
theorem r0978_checked : check r0978 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 861; projection:R_one_six_1010.
noncomputable def r0979 : Entry :=
  ⟨⟨[63,86,122,198,202,308,391,468,651,744,781,812,880,961],[7,11,13,22,44,52,58,70,74,82,84,104,112,131,134,138,194,196,200,261,276,292,304,336,385,388,448,521,552,608,641,648,704,769,780,800,832]⟩,
   ⟨1310,590395736865,590395744515⟩⟩
theorem r0979_checked : check r0979 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 865; projection:R_one_six_1013.
noncomputable def r0980 : Entry :=
  ⟨⟨[63,205,228,314,330,364,480,534,587,647,692,850,944,961],[7,11,13,22,44,52,58,73,74,76,100,133,164,193,196,224,266,274,296,304,322,328,352,416,448,515,518,530,532,577,578,641,644,688,784,832,896]⟩,
   ⟨1313,578063503920,521440399920⟩⟩
theorem r0980_checked : check r0980 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 867; projection:R_one_six_1014.
noncomputable def r0981 : Entry :=
  ⟨⟨[63,122,202,236,338,395,450,653,692,736,775,790,880,961],[7,11,13,22,44,52,58,74,82,104,112,137,138,140,164,194,200,224,259,274,322,336,385,386,448,517,532,560,608,641,644,672,704,769,774,784,832]⟩,
   ⟨1314,654819263025,654819267075⟩⟩
theorem r0981_checked : check r0981 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 868; projection:R_one_six_1015.
noncomputable def r0982 : Entry :=
  ⟨⟨[63,180,199,212,314,330,342,464,587,653,684,872,944,961],[7,11,13,22,44,52,58,67,70,74,84,133,148,164,176,193,196,208,266,274,296,304,322,328,336,400,448,521,552,577,584,641,652,672,800,832,896]⟩,
   ⟨1315,578064495105,521441391105⟩⟩
theorem r0982_checked : check r0982 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 875; projection:R_one_six_1016.
noncomputable def r0983 : Entry :=
  ⟨⟨[63,122,202,236,356,397,452,534,651,722,775,820,880,961],[7,11,13,22,44,52,58,74,82,100,104,112,137,138,140,194,196,200,261,292,324,352,385,388,448,515,518,530,532,592,641,642,704,769,772,816,832]⟩,
   ⟨1316,590394757680,590394757680⟩⟩
theorem r0983_checked : check r0983 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 876; projection:R_one_six_1017.
noncomputable def r0984 : Entry :=
  ⟨⟨[63,122,180,212,330,342,391,452,653,684,752,779,872,961],[7,11,13,22,44,52,58,74,82,84,104,112,133,148,164,176,196,208,259,262,266,322,324,328,385,388,448,521,552,608,641,652,672,704,769,776,832]⟩,
   ⟨1317,582342685185,521944707585⟩⟩
theorem r0984_checked : check r0984 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 883; projection:R_one_six_1023.
noncomputable def r0985 : Entry :=
  ⟨⟨[63,71,180,197,214,331,397,570,752,778,812,850,932,961],[7,11,13,22,44,52,58,67,69,70,82,133,148,164,176,193,196,208,265,266,268,321,322,385,388,522,530,552,560,592,672,704,770,776,804,832,896]⟩,
   ⟨1323,444936299265,509109150465⟩⟩
theorem r0985_checked : check r0985 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 884; projection:R_one_six_1022.
noncomputable def r0986 : Entry :=
  ⟨⟨[63,71,116,195,214,333,395,570,752,778,812,868,914,961],[7,11,13,22,44,52,58,67,69,70,84,100,112,131,146,193,194,208,265,266,268,321,324,385,386,522,530,552,560,608,656,704,770,776,804,832,896]⟩,
   ⟨1322,444684641025,444684641025⟩⟩
theorem r0986_checked : check r0986 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 885; projection:R_one_six_1021.
noncomputable def r0987 : Entry :=
  ⟨⟨[63,86,116,199,210,333,395,570,752,778,812,868,914,961],[7,11,13,22,44,52,58,69,70,82,84,100,112,131,146,193,194,208,265,266,268,321,324,385,386,522,530,552,560,608,656,704,770,776,804,832,896]⟩,
   ⟨1321,444684636720,444684636720⟩⟩
theorem r0987_checked : check r0987 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 886; projection:R_one_six_1024.
noncomputable def r0988 : Entry :=
  ⟨⟨[63,86,116,199,228,331,397,570,752,778,812,850,932,961],[7,11,13,22,44,52,58,67,70,82,84,100,112,133,164,193,196,224,265,266,268,321,322,385,388,522,530,552,560,592,672,704,770,776,804,832,896]⟩,
   ⟨1324,444936294960,509109146160⟩⟩
theorem r0988_checked : check r0988 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 887; projection:R_one_six_1020.
noncomputable def r0989 : Entry :=
  ⟨⟨[63,86,180,199,212,331,397,570,752,778,812,850,932,961],[7,11,13,22,44,52,58,67,70,82,84,133,148,164,176,193,196,208,265,266,268,321,322,385,388,522,530,552,560,592,672,704,770,776,804,832,896]⟩,
   ⟨1320,444936294960,509109146160⟩⟩
theorem r0989_checked : check r0989 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 888; projection:R_one_six_1018.
noncomputable def r0990 : Entry :=
  ⟨⟨[63,86,186,240,327,372,480,587,650,684,722,781,932,961],[7,11,13,22,44,52,58,67,70,82,84,112,138,146,168,176,208,224,261,292,321,324,352,416,448,521,522,524,577,578,642,648,676,704,769,772,896]⟩,
   ⟨1318,521440399920,578063503920⟩⟩
theorem r0990_checked : check r0990 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 889; projection:R_one_six_1019.
noncomputable def r0991 : Entry :=
  ⟨⟨[63,122,150,368,391,436,464,586,620,651,722,781,868,961],[7,11,13,22,44,52,58,74,82,104,112,131,134,146,148,208,261,292,304,336,352,385,388,400,448,521,522,524,578,584,612,641,642,704,769,772,832]⟩,
   ⟨1319,521943716400,582341694000⟩⟩
theorem r0991_checked : check r0991 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 895; projection:R_one_six_1026.
noncomputable def r0992 : Entry :=
  ⟨⟨[63,71,108,205,323,342,395,570,650,744,820,868,914,961],[7,11,13,22,44,52,58,67,69,70,76,100,104,137,138,193,200,259,274,276,321,322,324,385,386,522,530,552,560,608,642,648,704,784,804,832,896]⟩,
   ⟨1325,448711164465,448711168515⟩⟩
theorem r0992_checked : check r0992 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 912; projection:R_one_six_1027.
noncomputable def r0993 : Entry :=
  ⟨⟨[63,122,202,232,342,395,450,653,684,752,775,820,848,961],[7,11,13,22,44,52,58,74,82,104,112,137,138,168,194,200,224,259,262,276,322,336,385,386,448,517,548,560,592,641,652,672,704,769,772,784,832]⟩,
   ⟨1326,654819271425,654819271425⟩⟩
theorem r0993_checked : check r0993 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 933; projection:R_one_six_1004.
noncomputable def r0994 : Entry :=
  ⟨⟨[63,135,150,203,314,330,333,338,692,722,812,880,901,961],[7,11,13,22,44,52,58,73,74,82,131,133,134,146,148,193,194,261,266,268,274,296,304,321,322,328,336,548,560,592,644,656,704,772,800,832,897]⟩,
   ⟨1306,646514541105,650289418755⟩⟩
theorem r0994_checked : check r0994 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 937; projection:R_one_six_1006.
noncomputable def r0995 : Entry :=
  ⟨⟨[63,86,203,314,368,394,397,466,583,628,705,812,901,992],[7,11,13,22,44,52,58,67,70,82,84,112,137,138,193,194,266,268,274,296,304,336,352,386,389,392,448,517,548,577,580,608,641,704,772,800,896]⟩,
   ⟨1308,646262890545,646262887170⟩⟩
theorem r0995_checked : check r0995 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 938; projection:R_one_six_1005.
noncomputable def r0996 : Entry :=
  ⟨⟨[63,86,203,327,372,449,464,570,650,653,722,812,901,944],[7,11,13,22,44,52,58,67,70,82,84,137,138,193,194,208,261,292,304,321,324,336,385,400,448,522,524,530,552,560,642,645,648,656,772,800,896]⟩,
   ⟨1307,452989362225,577560187650⟩⟩
theorem r0996_checked : check r0996 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 948; projection:R_one_six_1029.
noncomputable def r0997 : Entry :=
  ⟨⟨[63,77,150,199,395,436,449,484,570,620,778,841,880,914],[7,11,13,22,44,52,58,69,73,76,100,131,134,146,148,193,196,265,266,304,321,352,385,386,400,420,448,522,530,552,560,584,608,770,776,784,832]⟩,
   ⟨1328,444684632625,444684636675⟩⟩
theorem r0997_checked : check r0997 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 949; projection:R_one_six_1028.
noncomputable def r0998 : Entry :=
  ⟨⟨[63,141,314,330,338,428,457,587,598,647,692,705,880,992],[7,11,13,22,44,52,58,73,74,82,133,137,140,164,193,266,274,296,304,322,328,336,392,416,448,515,518,532,560,577,578,592,641,644,672,704,864]⟩,
   ⟨1327,578063499825,521440399875⟩⟩
theorem r0998_checked : check r0998 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 950; projection:R_one_six_1030.
noncomputable def r0999 : Entry :=
  ⟨⟨[63,122,141,236,330,338,457,647,692,736,779,790,880,961],[7,11,13,22,44,52,58,74,82,104,112,133,137,140,164,200,224,265,266,274,322,328,336,449,515,518,532,560,608,641,644,672,704,769,770,784,832]⟩,
   ⟨1329,582341697585,521943716610⟩⟩
theorem r0999_checked : check r0999 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 1039; projection:R_one_six_1197.
noncomputable def r1000 : Entry :=
  ⟨⟨[63,71,86,197,244,331,397,420,570,722,812,842,944,961],[7,11,13,22,44,52,58,67,69,70,82,84,133,164,176,193,196,208,265,268,292,321,330,385,388,416,522,530,552,560,578,656,704,776,800,832,896]⟩,
   ⟨1432,444937274145,509110132995⟩⟩
theorem r1000_checked : check r1000 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 1044; projection:R_one_six_1196.
noncomputable def r1001 : Entry :=
  ⟨⟨[63,71,197,214,314,338,496,587,653,692,812,842,928,961],[7,11,13,22,44,52,58,67,69,70,82,133,148,176,193,196,208,266,274,296,304,322,336,416,448,521,524,548,577,586,641,644,672,776,800,832,896]⟩,
   ⟨1431,509361795105,509361795330⟩⟩
theorem r1001_checked : check r1001 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 1077; projection:R_one_six_1198.
noncomputable def r1002 : Entry :=
  ⟨⟨[63,71,195,214,314,402,496,589,628,651,812,864,906,961],[7,11,13,22,44,52,58,67,69,70,84,112,131,146,193,194,208,266,274,296,304,352,386,400,448,521,524,548,577,580,608,641,650,776,800,832,896]⟩,
   ⟨1433,509110136865,444937285890⟩⟩
theorem r1002_checked : check r1002 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 1087; projection:R_one_six_1201.
noncomputable def r1003 : Entry :=
  ⟨⟨[63,86,199,210,314,402,496,589,628,651,812,864,906,961],[7,11,13,22,44,52,58,69,70,82,84,112,131,146,193,194,208,266,274,296,304,352,386,400,448,521,524,548,577,580,608,641,650,776,800,832,896]⟩,
   ⟨1436,577560183345,452989358595⟩⟩
theorem r1003_checked : check r1003 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 1121; projection:R_one_six_1200.
noncomputable def r1004 : Entry :=
  ⟨⟨[63,86,199,244,314,338,464,587,653,676,812,842,944,961],[7,11,13,22,44,52,58,67,70,82,84,133,164,176,193,196,208,266,274,296,304,322,336,400,448,521,524,548,577,586,641,644,672,776,800,832,896]⟩,
   ⟨1435,509361795105,509361795330⟩⟩
theorem r1004_checked : check r1004 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 1122; projection:R_one_six_1199.
noncomputable def r1005 : Entry :=
  ⟨⟨[63,86,199,212,314,338,496,587,653,692,812,842,928,961],[7,11,13,22,44,52,58,67,70,82,84,133,148,176,193,196,208,266,274,296,304,322,336,416,448,521,524,548,577,586,641,644,672,776,800,832,896]⟩,
   ⟨1434,509361795105,509361795330⟩⟩
theorem r1005_checked : check r1005 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 1297; projection:R_one_six_1040.
noncomputable def r1006 : Entry :=
  ⟨⟨[63,135,195,214,236,323,397,449,570,628,779,850,936,992],[7,11,13,22,44,52,58,67,82,84,100,131,133,134,140,168,193,194,196,224,259,265,321,322,385,392,448,522,530,552,560,592,608,770,776,832,928]⟩,
   ⟨1335,444937286145,509110137345⟩⟩
theorem r1006_checked : check r1006 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 1342; projection:R_one_six_1038.
noncomputable def r1007 : Entry :=
  ⟨⟨[63,71,195,314,342,395,424,589,628,684,713,848,944,962],[7,11,13,22,44,52,58,67,69,70,84,131,137,168,193,194,266,274,296,304,322,336,386,392,416,524,548,560,580,585,592,648,672,704,784,832,896]⟩,
   ⟨1333,646263878145,646263878145⟩⟩
theorem r1007_checked : check r1007 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 1343; projection:R_one_six_1039.
noncomputable def r1008 : Entry :=
  ⟨⟨[63,71,195,314,395,424,466,589,598,684,713,820,848,992],[7,11,13,22,44,52,58,67,69,70,82,131,137,168,193,194,266,274,296,304,336,386,392,416,448,524,532,548,580,585,592,648,672,704,784,800,832]⟩,
   ⟨1334,646263878145,646263878145⟩⟩
theorem r1008_checked : check r1008 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 1472; projection:R_one_six_1034.
noncomputable def r1009 : Entry :=
  ⟨⟨[63,71,141,197,198,406,428,457,570,587,722,820,872,976],[7,11,13,22,44,52,58,67,69,70,73,133,134,137,140,146,193,194,196,276,292,296,328,388,392,400,448,522,530,552,560,578,584,720,784,800,832]⟩,
   ⟨1330,453241996065,581587706115⟩⟩
theorem r1009_checked : check r1009 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 1474; projection:R_one_six_1035.
noncomputable def r1010 : Entry :=
  ⟨⟨[63,71,141,197,236,342,356,451,570,651,820,872,914,968],[7,11,13,22,44,52,58,67,69,70,100,104,131,133,137,140,193,196,200,274,276,292,322,324,352,386,448,522,530,552,560,642,648,784,800,840,896]⟩,
   ⟨1331,452989354545,577560187395⟩⟩
theorem r1010_checked : check r1010 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 1476; projection:R_one_six_1036.
noncomputable def r1011 : Entry :=
  ⟨⟨[63,77,135,197,214,314,338,395,620,713,820,852,936,962],[7,11,13,22,44,52,58,69,73,76,82,84,131,133,134,137,193,194,196,266,274,296,304,322,336,386,392,548,552,580,584,648,704,788,800,832,896]⟩,
   ⟨1332,646263878145,646263878145⟩⟩
theorem r1011_checked : check r1011 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 1481; projection:R_one_six_1076.
noncomputable def r1012 : Entry :=
  ⟨⟨[63,180,210,263,333,406,451,570,587,594,752,812,932,968],[7,11,13,22,44,52,58,67,73,82,146,148,164,176,194,208,259,261,262,268,321,328,386,388,448,522,530,552,560,578,584,592,672,704,776,804,896]⟩,
   ⟨1357,449214480945,517162209795⟩⟩
theorem r1012_checked : check r1012 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 1482; projection:R_one_six_1075.
noncomputable def r1013 : Entry :=
  ⟨⟨[63,210,314,331,338,436,464,519,589,662,684,707,872,992],[7,11,13,22,44,52,58,67,73,82,146,148,164,194,208,266,274,296,304,322,328,336,400,416,448,515,517,518,524,552,577,584,642,644,672,704,864]⟩,
   ⟨1356,578063499825,521440399875⟩⟩
theorem r1013_checked : check r1013 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 1483; projection:R_one_six_1077.
noncomputable def r1014 : Entry :=
  ⟨⟨[63,186,203,210,338,496,519,589,684,790,820,835,928,968],[7,11,13,22,44,52,58,67,73,82,138,146,168,176,194,200,208,274,304,322,336,416,448,515,517,518,524,548,577,584,648,672,770,788,800,832,896]⟩,
   ⟨1358,590143095345,590143099395⟩⟩
theorem r1014_checked : check r1014 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 1496; projection:R_one_six_1078.
noncomputable def r1015 : Entry :=
  ⟨⟨[63,71,86,210,212,236,333,451,570,692,779,872,914,992],[7,11,13,22,44,52,58,67,69,70,76,82,84,104,146,148,164,194,196,208,224,259,265,321,328,386,448,522,530,552,560,656,672,770,776,864,896]⟩,
   ⟨1359,444936290865,509109146115⟩⟩
theorem r1015_checked : check r1015 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 1502; projection:R_one_six_1079.
noncomputable def r1016 : Entry :=
  ⟨⟨[63,71,108,214,314,372,464,480,589,707,744,779,914,936],[7,11,13,22,44,52,58,67,69,70,76,84,100,104,146,194,208,224,266,274,296,304,336,352,400,416,448,515,521,577,584,642,680,704,770,776,896]⟩,
   ⟨1360,509360800305,509360804355⟩⟩
theorem r1016_checked : check r1016 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 1508; projection:R_one_six_1081.
noncomputable def r1017 : Entry :=
  ⟨⟨[63,71,108,180,186,342,404,484,589,651,835,872,914,936],[7,11,13,22,44,52,58,67,69,70,76,100,104,138,146,148,164,168,176,274,276,322,324,352,388,400,416,515,521,577,584,642,648,770,808,832,896]⟩,
   ⟨1362,521440395825,578063503875⟩⟩
theorem r1017_checked : check r1017 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 1509; projection:R_one_six_1080.
noncomputable def r1018 : Entry :=
  ⟨⟨[63,116,122,212,228,263,406,428,587,722,781,872,899,992],[7,11,13,22,44,52,58,74,82,84,100,104,112,146,148,164,196,208,224,259,261,262,268,296,386,388,416,515,521,578,584,642,704,769,776,864,896]⟩,
   ⟨1361,517917180465,517917184515⟩⟩
theorem r1018_checked : check r1018 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 1513; projection:R_one_six_1082.
noncomputable def r1019 : Entry :=
  ⟨⟨[63,86,141,198,210,236,391,457,570,628,779,872,914,976],[7,11,13,22,44,52,58,70,82,84,100,104,133,134,137,140,146,194,196,200,208,259,265,328,385,386,448,522,530,552,560,592,608,770,776,832,912]⟩,
   ⟨1363,444685615905,444685623555⟩⟩
theorem r1019_checked : check r1019 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 1552; projection:R_one_six_1067.
noncomputable def r1020 : Entry :=
  ⟨⟨[63,71,186,214,450,496,556,589,651,820,835,852,898,936],[7,11,13,22,44,52,58,67,69,70,84,138,146,168,176,194,208,304,322,336,386,416,448,515,521,524,548,552,577,580,642,648,770,788,800,832,896]⟩,
   ⟨1352,521440395825,578063503875⟩⟩
theorem r1020_checked : check r1020 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 1553; projection:R_one_six_1068.
noncomputable def r1021 : Entry :=
  ⟨⟨[63,116,135,314,406,450,496,620,653,707,724,779,834,872],[7,11,13,22,44,52,58,84,100,112,131,133,134,148,194,208,266,274,296,304,322,352,386,400,448,515,521,524,578,580,616,641,644,704,770,776,832]⟩,
   ⟨1353,509109142065,444936294915⟩⟩
theorem r1021_checked : check r1021 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 1557; projection:R_one_six_1069.
noncomputable def r1022 : Entry :=
  ⟨⟨[63,71,86,116,210,333,451,484,570,684,752,779,908,914],[7,11,13,22,44,52,58,67,69,70,82,84,100,112,146,164,194,208,224,259,265,268,321,324,386,388,448,522,530,552,560,652,656,672,770,776,896]⟩,
   ⟨1354,444936290865,509109146115⟩⟩
theorem r1022_checked : check r1022 = true := by decide +kernel

-- six_orbit_dags/type1m14e11q2r1.json.gz, graph 355, terminal 1595; projection:R_one_six_1087.
noncomputable def r1023 : Entry :=
  ⟨⟨[63,71,214,314,372,464,480,589,620,707,736,779,914,936],[7,11,13,22,44,52,58,67,69,70,84,100,146,194,208,224,266,274,296,304,336,352,400,416,448,515,521,552,577,588,608,642,672,704,770,776,896]⟩,
   ⟨1368,509360800305,509360804355⟩⟩
theorem r1023_checked : check r1023 = true := by decide +kernel

#print axioms r0960_checked

end Nonrational.OldTerminalMatches.M015
