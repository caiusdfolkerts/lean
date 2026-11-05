module

public import PolygonN7ClassificationPart003

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

theorem terminal_data_00880 : FiniteChecks.Interval terminalTest 880 888 :=
  FiniteChecks.interval_of_check terminalTest 880 8 (by decide +kernel)

theorem terminal_data_00888 : FiniteChecks.Interval terminalTest 888 896 :=
  FiniteChecks.interval_of_check terminalTest 888 8 (by decide +kernel)

theorem terminal_data_00896 : FiniteChecks.Interval terminalTest 896 904 :=
  FiniteChecks.interval_of_check terminalTest 896 8 (by decide +kernel)

theorem terminal_data_00904 : FiniteChecks.Interval terminalTest 904 912 :=
  FiniteChecks.interval_of_check terminalTest 904 8 (by decide +kernel)

theorem terminal_data_00912 : FiniteChecks.Interval terminalTest 912 920 :=
  FiniteChecks.interval_of_check terminalTest 912 8 (by decide +kernel)

theorem terminal_data_00920 : FiniteChecks.Interval terminalTest 920 928 :=
  FiniteChecks.interval_of_check terminalTest 920 8 (by decide +kernel)

theorem terminal_data_00928 : FiniteChecks.Interval terminalTest 928 936 :=
  FiniteChecks.interval_of_check terminalTest 928 8 (by decide +kernel)

theorem terminal_data_00936 : FiniteChecks.Interval terminalTest 936 944 :=
  FiniteChecks.interval_of_check terminalTest 936 8 (by decide +kernel)

theorem terminal_data_00944 : FiniteChecks.Interval terminalTest 944 952 :=
  FiniteChecks.interval_of_check terminalTest 944 8 (by decide +kernel)

theorem terminal_data_00952 : FiniteChecks.Interval terminalTest 952 960 :=
  FiniteChecks.interval_of_check terminalTest 952 8 (by decide +kernel)

theorem terminal_data_00960 : FiniteChecks.Interval terminalTest 960 968 :=
  FiniteChecks.interval_of_check terminalTest 960 8 (by decide +kernel)

theorem terminal_data_00968 : FiniteChecks.Interval terminalTest 968 976 :=
  FiniteChecks.interval_of_check terminalTest 968 8 (by decide +kernel)

theorem terminal_data_00976 : FiniteChecks.Interval terminalTest 976 984 :=
  FiniteChecks.interval_of_check terminalTest 976 8 (by decide +kernel)

theorem terminal_data_00984 : FiniteChecks.Interval terminalTest 984 992 :=
  FiniteChecks.interval_of_check terminalTest 984 8 (by decide +kernel)

theorem terminal_data_00992 : FiniteChecks.Interval terminalTest 992 1000 :=
  FiniteChecks.interval_of_check terminalTest 992 8 (by decide +kernel)

theorem terminal_data_01000 : FiniteChecks.Interval terminalTest 1000 1008 :=
  FiniteChecks.interval_of_check terminalTest 1000 8 (by decide +kernel)

theorem terminal_data_01008 : FiniteChecks.Interval terminalTest 1008 1016 :=
  FiniteChecks.interval_of_check terminalTest 1008 8 (by decide +kernel)

theorem terminal_data_01016 : FiniteChecks.Interval terminalTest 1016 1024 :=
  FiniteChecks.interval_of_check terminalTest 1016 8 (by decide +kernel)

theorem terminal_data_01024 : FiniteChecks.Interval terminalTest 1024 1032 :=
  FiniteChecks.interval_of_check terminalTest 1024 8 (by decide +kernel)

theorem terminal_data_01032 : FiniteChecks.Interval terminalTest 1032 1040 :=
  FiniteChecks.interval_of_check terminalTest 1032 8 (by decide +kernel)

theorem terminal_data_01040 : FiniteChecks.Interval terminalTest 1040 1048 :=
  FiniteChecks.interval_of_check terminalTest 1040 8 (by decide +kernel)

theorem terminal_data_01048 : FiniteChecks.Interval terminalTest 1048 1056 :=
  FiniteChecks.interval_of_check terminalTest 1048 8 (by decide +kernel)

theorem terminal_data_01056 : FiniteChecks.Interval terminalTest 1056 1064 :=
  FiniteChecks.interval_of_check terminalTest 1056 8 (by decide +kernel)

theorem terminal_data_01064 : FiniteChecks.Interval terminalTest 1064 1072 :=
  FiniteChecks.interval_of_check terminalTest 1064 8 (by decide +kernel)

theorem terminal_data_01072 : FiniteChecks.Interval terminalTest 1072 1080 :=
  FiniteChecks.interval_of_check terminalTest 1072 8 (by decide +kernel)

theorem terminal_data_01080 : FiniteChecks.Interval terminalTest 1080 1088 :=
  FiniteChecks.interval_of_check terminalTest 1080 8 (by decide +kernel)

theorem terminal_data_01088 : FiniteChecks.Interval terminalTest 1088 1096 :=
  FiniteChecks.interval_of_check terminalTest 1088 8 (by decide +kernel)

theorem terminal_data_01096 : FiniteChecks.Interval terminalTest 1096 1104 :=
  FiniteChecks.interval_of_check terminalTest 1096 8 (by decide +kernel)

theorem terminal_data_01104 : FiniteChecks.Interval terminalTest 1104 1112 :=
  FiniteChecks.interval_of_check terminalTest 1104 8 (by decide +kernel)

theorem terminal_data_01112 : FiniteChecks.Interval terminalTest 1112 1120 :=
  FiniteChecks.interval_of_check terminalTest 1112 8 (by decide +kernel)

theorem terminal_data_01120 : FiniteChecks.Interval terminalTest 1120 1128 :=
  FiniteChecks.interval_of_check terminalTest 1120 8 (by decide +kernel)

theorem terminal_data_01128 : FiniteChecks.Interval terminalTest 1128 1136 :=
  FiniteChecks.interval_of_check terminalTest 1128 8 (by decide +kernel)

theorem terminal_data_01136 : FiniteChecks.Interval terminalTest 1136 1144 :=
  FiniteChecks.interval_of_check terminalTest 1136 8 (by decide +kernel)

theorem terminal_data_01144 : FiniteChecks.Interval terminalTest 1144 1152 :=
  FiniteChecks.interval_of_check terminalTest 1144 8 (by decide +kernel)

theorem terminal_data_01152 : FiniteChecks.Interval terminalTest 1152 1160 :=
  FiniteChecks.interval_of_check terminalTest 1152 8 (by decide +kernel)

theorem terminal_data_01160 : FiniteChecks.Interval terminalTest 1160 1168 :=
  FiniteChecks.interval_of_check terminalTest 1160 8 (by decide +kernel)

theorem terminal_data_01168 : FiniteChecks.Interval terminalTest 1168 1176 :=
  FiniteChecks.interval_of_check terminalTest 1168 8 (by decide +kernel)

theorem terminal_data_01176 : FiniteChecks.Interval terminalTest 1176 1184 :=
  FiniteChecks.interval_of_check terminalTest 1176 8 (by decide +kernel)

theorem terminal_data_01184 : FiniteChecks.Interval terminalTest 1184 1192 :=
  FiniteChecks.interval_of_check terminalTest 1184 8 (by decide +kernel)

theorem terminal_data_01192 : FiniteChecks.Interval terminalTest 1192 1200 :=
  FiniteChecks.interval_of_check terminalTest 1192 8 (by decide +kernel)

theorem terminal_data_01200 : FiniteChecks.Interval terminalTest 1200 1208 :=
  FiniteChecks.interval_of_check terminalTest 1200 8 (by decide +kernel)

theorem terminal_data_01208 : FiniteChecks.Interval terminalTest 1208 1216 :=
  FiniteChecks.interval_of_check terminalTest 1208 8 (by decide +kernel)

theorem terminal_data_01216 : FiniteChecks.Interval terminalTest 1216 1224 :=
  FiniteChecks.interval_of_check terminalTest 1216 8 (by decide +kernel)

theorem terminal_data_01224 : FiniteChecks.Interval terminalTest 1224 1232 :=
  FiniteChecks.interval_of_check terminalTest 1224 8 (by decide +kernel)

theorem terminal_data_01232 : FiniteChecks.Interval terminalTest 1232 1240 :=
  FiniteChecks.interval_of_check terminalTest 1232 8 (by decide +kernel)

theorem terminal_data_01240 : FiniteChecks.Interval terminalTest 1240 1248 :=
  FiniteChecks.interval_of_check terminalTest 1240 8 (by decide +kernel)

theorem terminal_data_01248 : FiniteChecks.Interval terminalTest 1248 1256 :=
  FiniteChecks.interval_of_check terminalTest 1248 8 (by decide +kernel)

theorem terminal_data_01256 : FiniteChecks.Interval terminalTest 1256 1264 :=
  FiniteChecks.interval_of_check terminalTest 1256 8 (by decide +kernel)

theorem terminal_data_01264 : FiniteChecks.Interval terminalTest 1264 1272 :=
  FiniteChecks.interval_of_check terminalTest 1264 8 (by decide +kernel)

theorem terminal_data_01272 : FiniteChecks.Interval terminalTest 1272 1280 :=
  FiniteChecks.interval_of_check terminalTest 1272 8 (by decide +kernel)

theorem terminal_data_01280 : FiniteChecks.Interval terminalTest 1280 1288 :=
  FiniteChecks.interval_of_check terminalTest 1280 8 (by decide +kernel)

theorem terminal_data_01288 : FiniteChecks.Interval terminalTest 1288 1296 :=
  FiniteChecks.interval_of_check terminalTest 1288 8 (by decide +kernel)

theorem terminal_data_01296 : FiniteChecks.Interval terminalTest 1296 1304 :=
  FiniteChecks.interval_of_check terminalTest 1296 8 (by decide +kernel)

theorem terminal_data_01304 : FiniteChecks.Interval terminalTest 1304 1312 :=
  FiniteChecks.interval_of_check terminalTest 1304 8 (by decide +kernel)

theorem terminal_data_01312 : FiniteChecks.Interval terminalTest 1312 1320 :=
  FiniteChecks.interval_of_check terminalTest 1312 8 (by decide +kernel)

theorem terminal_data_01320 : FiniteChecks.Interval terminalTest 1320 1328 :=
  FiniteChecks.interval_of_check terminalTest 1320 8 (by decide +kernel)

theorem terminal_data_01328 : FiniteChecks.Interval terminalTest 1328 1336 :=
  FiniteChecks.interval_of_check terminalTest 1328 8 (by decide +kernel)

theorem terminal_data_01336 : FiniteChecks.Interval terminalTest 1336 1344 :=
  FiniteChecks.interval_of_check terminalTest 1336 8 (by decide +kernel)

theorem terminal_data_01344 : FiniteChecks.Interval terminalTest 1344 1352 :=
  FiniteChecks.interval_of_check terminalTest 1344 8 (by decide +kernel)

theorem terminal_data_01352 : FiniteChecks.Interval terminalTest 1352 1360 :=
  FiniteChecks.interval_of_check terminalTest 1352 8 (by decide +kernel)

theorem terminal_data_01360 : FiniteChecks.Interval terminalTest 1360 1368 :=
  FiniteChecks.interval_of_check terminalTest 1360 8 (by decide +kernel)

theorem terminal_data_01368 : FiniteChecks.Interval terminalTest 1368 1376 :=
  FiniteChecks.interval_of_check terminalTest 1368 8 (by decide +kernel)

theorem terminal_data_01376 : FiniteChecks.Interval terminalTest 1376 1384 :=
  FiniteChecks.interval_of_check terminalTest 1376 8 (by decide +kernel)

theorem terminal_data_01384 : FiniteChecks.Interval terminalTest 1384 1392 :=
  FiniteChecks.interval_of_check terminalTest 1384 8 (by decide +kernel)


end Papers.RationalityTen.ConcretePolygonClassification.N7
