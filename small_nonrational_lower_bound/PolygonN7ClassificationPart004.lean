module

public meta import LowerSchemas.FinitePolygonN
public import PolygonN7ClassificationPart003

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

cert_terminal_data 00880 880 888 8
cert_terminal_data 00888 888 896 8
cert_terminal_data 00896 896 904 8
cert_terminal_data 00904 904 912 8
cert_terminal_data 00912 912 920 8
cert_terminal_data 00920 920 928 8
cert_terminal_data 00928 928 936 8
cert_terminal_data 00936 936 944 8
cert_terminal_data 00944 944 952 8
cert_terminal_data 00952 952 960 8
cert_terminal_data 00960 960 968 8
cert_terminal_data 00968 968 976 8
cert_terminal_data 00976 976 984 8
cert_terminal_data 00984 984 992 8
cert_terminal_data 00992 992 1000 8
cert_terminal_data 01000 1000 1008 8
cert_terminal_data 01008 1008 1016 8
cert_terminal_data 01016 1016 1024 8
cert_terminal_data 01024 1024 1032 8
cert_terminal_data 01032 1032 1040 8
cert_terminal_data 01040 1040 1048 8
cert_terminal_data 01048 1048 1056 8
cert_terminal_data 01056 1056 1064 8
cert_terminal_data 01064 1064 1072 8
cert_terminal_data 01072 1072 1080 8
cert_terminal_data 01080 1080 1088 8
cert_terminal_data 01088 1088 1096 8
cert_terminal_data 01096 1096 1104 8
cert_terminal_data 01104 1104 1112 8
cert_terminal_data 01112 1112 1120 8
cert_terminal_data 01120 1120 1128 8
cert_terminal_data 01128 1128 1136 8
cert_terminal_data 01136 1136 1144 8
cert_terminal_data 01144 1144 1152 8
cert_terminal_data 01152 1152 1160 8
cert_terminal_data 01160 1160 1168 8
cert_terminal_data 01168 1168 1176 8
cert_terminal_data 01176 1176 1184 8
cert_terminal_data 01184 1184 1192 8
cert_terminal_data 01192 1192 1200 8
cert_terminal_data 01200 1200 1208 8
cert_terminal_data 01208 1208 1216 8
cert_terminal_data 01216 1216 1224 8
cert_terminal_data 01224 1224 1232 8
cert_terminal_data 01232 1232 1240 8
cert_terminal_data 01240 1240 1248 8
cert_terminal_data 01248 1248 1256 8
cert_terminal_data 01256 1256 1264 8
cert_terminal_data 01264 1264 1272 8
cert_terminal_data 01272 1272 1280 8
cert_terminal_data 01280 1280 1288 8
cert_terminal_data 01288 1288 1296 8
cert_terminal_data 01296 1296 1304 8
cert_terminal_data 01304 1304 1312 8
cert_terminal_data 01312 1312 1320 8
cert_terminal_data 01320 1320 1328 8
cert_terminal_data 01328 1328 1336 8
cert_terminal_data 01336 1336 1344 8
cert_terminal_data 01344 1344 1352 8
cert_terminal_data 01352 1352 1360 8
cert_terminal_data 01360 1360 1368 8
cert_terminal_data 01368 1368 1376 8
cert_terminal_data 01376 1376 1384 8
theorem terminal_data_01384 : FiniteChecks.Interval terminalTest 1384 1392 :=
  FiniteChecks.interval_of_check terminalTest 1384 8 (by decide +kernel)


end Papers.RationalityTen.ConcretePolygonClassification.N7
