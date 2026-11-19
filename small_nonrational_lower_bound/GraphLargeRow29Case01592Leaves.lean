module
prelude
public meta import LowerSchemas.FiniteGraphLargeRow
public import GraphLargeRow29Case01592Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M042
public import InducedTerminalMatches.M043
public import InducedTerminalMatches.M044

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphLargeRow29Case01592
open Papers.RationalityTen ConcreteGrowth RawLeafCertificate FastRawLeafCertificate

noncomputable def record000_rawLeaves (j : Fin record000.l) : List Cell :=
  (record000.leaf j).map record000.data.cells
theorem record000_raw_exact (j : Fin record000.l) :
    (record000.leaf j).map record000.data.cells = record000_rawLeaves j := rfl
noncomputable def record000_certificateTable : Table Certificate :=
(.branch 37
 (.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M042.r1355))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M042.r1356)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M042.r1357))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M042.r1358))))
 (.branch 6
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M042.r1359))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M042.r1360)))
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M042.r1361))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M042.r1362))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M042.r1363))))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M042.r1364))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M042.r1365)))
 (.branch 12
 (.leaf (.matching Nonrational.InducedTerminalMatches.M042.r1366))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M042.r1367))))
 (.branch 15
 (.branch 14
 (.leaf (.matching Nonrational.InducedTerminalMatches.M042.r1368))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M042.r1369)))
 (.branch 16
 (.leaf (.matching Nonrational.InducedTerminalMatches.M042.r1370))
 (.branch 17
 (.leaf (.matching Nonrational.InducedTerminalMatches.M042.r1371))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M042.r1372)))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf (.matching Nonrational.InducedTerminalMatches.M042.r1373))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M042.r1374)))
 (.branch 21
 (.leaf (.matching Nonrational.InducedTerminalMatches.M042.r1375))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M043.r1376))))
 (.branch 24
 (.branch 23
 (.leaf (.matching Nonrational.InducedTerminalMatches.M043.r1377))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M043.r1378)))
 (.branch 25
 (.leaf (.matching Nonrational.InducedTerminalMatches.M043.r1379))
 (.branch 26
 (.leaf (.matching Nonrational.InducedTerminalMatches.M043.r1380))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M043.r1381))))))
 (.branch 32
 (.branch 29
 (.branch 28
 (.leaf (.matching Nonrational.InducedTerminalMatches.M043.r1382))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M043.r1383)))
 (.branch 30
 (.leaf (.matching Nonrational.InducedTerminalMatches.M043.r1384))
 (.branch 31
 (.leaf (.matching Nonrational.InducedTerminalMatches.M043.r1385))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M043.r1386)))))
 (.branch 34
 (.branch 33
 (.leaf (.matching Nonrational.InducedTerminalMatches.M043.r1387))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M043.r1388)))
 (.branch 35
 (.leaf (.matching Nonrational.InducedTerminalMatches.M043.r1389))
 (.branch 36
 (.leaf (.matching Nonrational.InducedTerminalMatches.M043.r1390))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M043.r1391))))))))
 (.branch 55
 (.branch 46
 (.branch 41
 (.branch 39
 (.branch 38
 (.leaf (.matching Nonrational.InducedTerminalMatches.M043.r1392))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M043.r1393)))
 (.branch 40
 (.leaf (.matching Nonrational.InducedTerminalMatches.M043.r1394))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M043.r1395))))
 (.branch 43
 (.branch 42
 (.leaf (.matching Nonrational.InducedTerminalMatches.M043.r1396))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M043.r1397)))
 (.branch 44
 (.leaf (.matching Nonrational.InducedTerminalMatches.M043.r1398))
 (.branch 45
 (.leaf (.matching Nonrational.InducedTerminalMatches.M043.r1399))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M043.r1400))))))
 (.branch 50
 (.branch 48
 (.branch 47
 (.leaf (.matching Nonrational.InducedTerminalMatches.M043.r1401))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M043.r1402)))
 (.branch 49
 (.leaf (.matching Nonrational.InducedTerminalMatches.M043.r1403))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M043.r1404))))
 (.branch 52
 (.branch 51
 (.leaf (.matching Nonrational.InducedTerminalMatches.M043.r1405))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M043.r1406)))
 (.branch 53
 (.leaf (.matching Nonrational.InducedTerminalMatches.M043.r1407))
 (.branch 54
 (.leaf (.matching Nonrational.InducedTerminalMatches.M044.r1408))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M044.r1409)))))))
 (.branch 64
 (.branch 59
 (.branch 57
 (.branch 56
 (.leaf (.matching Nonrational.InducedTerminalMatches.M044.r1410))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M044.r1411)))
 (.branch 58
 (.leaf (.matching Nonrational.InducedTerminalMatches.M044.r1412))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M044.r1413))))
 (.branch 61
 (.branch 60
 (.leaf (.matching Nonrational.InducedTerminalMatches.M044.r1414))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M044.r1415)))
 (.branch 62
 (.leaf (.matching Nonrational.InducedTerminalMatches.M044.r1416))
 (.branch 63
 (.leaf (.matching Nonrational.InducedTerminalMatches.M044.r1417))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M044.r1418))))))
 (.branch 69
 (.branch 66
 (.branch 65
 (.leaf (.matching Nonrational.InducedTerminalMatches.M044.r1419))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M044.r1420)))
 (.branch 67
 (.leaf (.matching Nonrational.InducedTerminalMatches.M044.r1421))
 (.branch 68
 (.leaf (.matching Nonrational.InducedTerminalMatches.M044.r1422))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M044.r1423)))))
 (.branch 71
 (.branch 70
 (.leaf (.matching Nonrational.InducedTerminalMatches.M044.r1424))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M044.r1425)))
 (.branch 72
 (.leaf (.matching Nonrational.InducedTerminalMatches.M044.r1426))
 (.branch 73
 (.leaf (.matching Nonrational.InducedTerminalMatches.M044.r1427))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M044.r1428)))))))))
noncomputable def record000_certificates (j : Fin record000.l) : Certificate :=
  record000_certificateTable.get j.val
cert_graph_leaf_checked 0 042 1355
cert_graph_leaf_checked 1 042 1356
cert_graph_leaf_checked 2 042 1357
cert_graph_leaf_checked 3 042 1358
cert_graph_leaf_checked 4 042 1359
cert_graph_leaf_checked 5 042 1360
cert_graph_leaf_checked 6 042 1361
cert_graph_leaf_checked 7 042 1362
cert_graph_leaf_checked 8 042 1363
cert_graph_leaf_checked 9 042 1364
cert_graph_leaf_checked 10 042 1365
cert_graph_leaf_checked 11 042 1366
cert_graph_leaf_checked 12 042 1367
cert_graph_leaf_checked 13 042 1368
cert_graph_leaf_checked 14 042 1369
cert_graph_leaf_checked 15 042 1370
cert_graph_leaf_checked 16 042 1371
cert_graph_leaf_checked 17 042 1372
cert_graph_leaf_checked 18 042 1373
cert_graph_leaf_checked 19 042 1374
cert_graph_leaf_checked 20 042 1375
cert_graph_leaf_checked 21 043 1376
cert_graph_leaf_checked 22 043 1377
cert_graph_leaf_checked 23 043 1378
cert_graph_leaf_checked 24 043 1379
cert_graph_leaf_checked 25 043 1380
cert_graph_leaf_checked 26 043 1381
cert_graph_leaf_checked 27 043 1382
cert_graph_leaf_checked 28 043 1383
cert_graph_leaf_checked 29 043 1384
cert_graph_leaf_checked 30 043 1385
cert_graph_leaf_checked 31 043 1386
cert_graph_leaf_checked 32 043 1387
cert_graph_leaf_checked 33 043 1388
cert_graph_leaf_checked 34 043 1389
cert_graph_leaf_checked 35 043 1390
cert_graph_leaf_checked 36 043 1391
cert_graph_leaf_checked 37 043 1392
cert_graph_leaf_checked 38 043 1393
cert_graph_leaf_checked 39 043 1394
cert_graph_leaf_checked 40 043 1395
cert_graph_leaf_checked 41 043 1396
cert_graph_leaf_checked 42 043 1397
cert_graph_leaf_checked 43 043 1398
cert_graph_leaf_checked 44 043 1399
cert_graph_leaf_checked 45 043 1400
cert_graph_leaf_checked 46 043 1401
cert_graph_leaf_checked 47 043 1402
cert_graph_leaf_checked 48 043 1403
cert_graph_leaf_checked 49 043 1404
cert_graph_leaf_checked 50 043 1405
cert_graph_leaf_checked 51 043 1406
cert_graph_leaf_checked 52 043 1407
cert_graph_leaf_checked 53 044 1408
cert_graph_leaf_checked 54 044 1409
cert_graph_leaf_checked 55 044 1410
cert_graph_leaf_checked 56 044 1411
cert_graph_leaf_checked 57 044 1412
cert_graph_leaf_checked 58 044 1413
cert_graph_leaf_checked 59 044 1414
cert_graph_leaf_checked 60 044 1415
cert_graph_leaf_checked 61 044 1416
cert_graph_leaf_checked 62 044 1417
cert_graph_leaf_checked 63 044 1418
cert_graph_leaf_checked 64 044 1419
cert_graph_leaf_checked 65 044 1420
cert_graph_leaf_checked 66 044 1421
cert_graph_leaf_checked 67 044 1422
cert_graph_leaf_checked 68 044 1423
cert_graph_leaf_checked 69 044 1424
cert_graph_leaf_checked 70 044 1425
cert_graph_leaf_checked 71 044 1426
cert_graph_leaf_checked 72 044 1427
cert_graph_leaf_checked 73 044 1428
theorem record000_leaf_certificates_checked : ∀ j : Fin record000.l,
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves j)
      (record000_certificates j) = true :=
  (Fin.cases record000_leaf_checked_0 (Fin.cases record000_leaf_checked_1 (Fin.cases record000_leaf_checked_2 (Fin.cases record000_leaf_checked_3 (Fin.cases record000_leaf_checked_4 (Fin.cases record000_leaf_checked_5 (Fin.cases record000_leaf_checked_6 (Fin.cases record000_leaf_checked_7 (Fin.cases record000_leaf_checked_8 (Fin.cases record000_leaf_checked_9 (Fin.cases record000_leaf_checked_10 (Fin.cases record000_leaf_checked_11 (Fin.cases record000_leaf_checked_12 (Fin.cases record000_leaf_checked_13 (Fin.cases record000_leaf_checked_14 (Fin.cases record000_leaf_checked_15 (Fin.cases record000_leaf_checked_16 (Fin.cases record000_leaf_checked_17 (Fin.cases record000_leaf_checked_18 (Fin.cases record000_leaf_checked_19 (Fin.cases record000_leaf_checked_20 (Fin.cases record000_leaf_checked_21 (Fin.cases record000_leaf_checked_22 (Fin.cases record000_leaf_checked_23 (Fin.cases record000_leaf_checked_24 (Fin.cases record000_leaf_checked_25 (Fin.cases record000_leaf_checked_26 (Fin.cases record000_leaf_checked_27 (Fin.cases record000_leaf_checked_28 (Fin.cases record000_leaf_checked_29 (Fin.cases record000_leaf_checked_30 (Fin.cases record000_leaf_checked_31 (Fin.cases record000_leaf_checked_32 (Fin.cases record000_leaf_checked_33 (Fin.cases record000_leaf_checked_34 (Fin.cases record000_leaf_checked_35 (Fin.cases record000_leaf_checked_36 (Fin.cases record000_leaf_checked_37 (Fin.cases record000_leaf_checked_38 (Fin.cases record000_leaf_checked_39 (Fin.cases record000_leaf_checked_40 (Fin.cases record000_leaf_checked_41 (Fin.cases record000_leaf_checked_42 (Fin.cases record000_leaf_checked_43 (Fin.cases record000_leaf_checked_44 (Fin.cases record000_leaf_checked_45 (Fin.cases record000_leaf_checked_46 (Fin.cases record000_leaf_checked_47 (Fin.cases record000_leaf_checked_48 (Fin.cases record000_leaf_checked_49 (Fin.cases record000_leaf_checked_50 (Fin.cases record000_leaf_checked_51 (Fin.cases record000_leaf_checked_52 (Fin.cases record000_leaf_checked_53 (Fin.cases record000_leaf_checked_54 (Fin.cases record000_leaf_checked_55 (Fin.cases record000_leaf_checked_56 (Fin.cases record000_leaf_checked_57 (Fin.cases record000_leaf_checked_58 (Fin.cases record000_leaf_checked_59 (Fin.cases record000_leaf_checked_60 (Fin.cases record000_leaf_checked_61 (Fin.cases record000_leaf_checked_62 (Fin.cases record000_leaf_checked_63 (Fin.cases record000_leaf_checked_64 (Fin.cases record000_leaf_checked_65 (Fin.cases record000_leaf_checked_66 (Fin.cases record000_leaf_checked_67 (Fin.cases record000_leaf_checked_68 (Fin.cases record000_leaf_checked_69 (Fin.cases record000_leaf_checked_70 (Fin.cases record000_leaf_checked_71 (Fin.cases record000_leaf_checked_72 (Fin.cases record000_leaf_checked_73 (fun j => Fin.elim0 j)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
#print axioms record000_leaf_certificates_checked

end Papers.RationalityTen.CompactReplay.GraphLargeRow29Case01592
