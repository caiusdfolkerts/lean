module
prelude
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
theorem record000_leaf_checked_0 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 0)
      (record000_certificates 0) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M042.r1355) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 0) Nonrational.InducedTerminalMatches.M042.r1355
    Nonrational.InducedTerminalMatches.M042.r1355_checked (by decide +kernel)
theorem record000_leaf_checked_1 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 1)
      (record000_certificates 1) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M042.r1356) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 1) Nonrational.InducedTerminalMatches.M042.r1356
    Nonrational.InducedTerminalMatches.M042.r1356_checked (by decide +kernel)
theorem record000_leaf_checked_2 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 2)
      (record000_certificates 2) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M042.r1357) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 2) Nonrational.InducedTerminalMatches.M042.r1357
    Nonrational.InducedTerminalMatches.M042.r1357_checked (by decide +kernel)
theorem record000_leaf_checked_3 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 3)
      (record000_certificates 3) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M042.r1358) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 3) Nonrational.InducedTerminalMatches.M042.r1358
    Nonrational.InducedTerminalMatches.M042.r1358_checked (by decide +kernel)
theorem record000_leaf_checked_4 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 4)
      (record000_certificates 4) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M042.r1359) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 4) Nonrational.InducedTerminalMatches.M042.r1359
    Nonrational.InducedTerminalMatches.M042.r1359_checked (by decide +kernel)
theorem record000_leaf_checked_5 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 5)
      (record000_certificates 5) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 5)
    (.matching Nonrational.InducedTerminalMatches.M042.r1360) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 5) Nonrational.InducedTerminalMatches.M042.r1360
    Nonrational.InducedTerminalMatches.M042.r1360_checked (by decide +kernel)
theorem record000_leaf_checked_6 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 6)
      (record000_certificates 6) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 6)
    (.matching Nonrational.InducedTerminalMatches.M042.r1361) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 6) Nonrational.InducedTerminalMatches.M042.r1361
    Nonrational.InducedTerminalMatches.M042.r1361_checked (by decide +kernel)
theorem record000_leaf_checked_7 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 7)
      (record000_certificates 7) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 7)
    (.matching Nonrational.InducedTerminalMatches.M042.r1362) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 7) Nonrational.InducedTerminalMatches.M042.r1362
    Nonrational.InducedTerminalMatches.M042.r1362_checked (by decide +kernel)
theorem record000_leaf_checked_8 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 8)
      (record000_certificates 8) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 8)
    (.matching Nonrational.InducedTerminalMatches.M042.r1363) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 8) Nonrational.InducedTerminalMatches.M042.r1363
    Nonrational.InducedTerminalMatches.M042.r1363_checked (by decide +kernel)
theorem record000_leaf_checked_9 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 9)
      (record000_certificates 9) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 9)
    (.matching Nonrational.InducedTerminalMatches.M042.r1364) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 9) Nonrational.InducedTerminalMatches.M042.r1364
    Nonrational.InducedTerminalMatches.M042.r1364_checked (by decide +kernel)
theorem record000_leaf_checked_10 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 10)
      (record000_certificates 10) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 10)
    (.matching Nonrational.InducedTerminalMatches.M042.r1365) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 10) Nonrational.InducedTerminalMatches.M042.r1365
    Nonrational.InducedTerminalMatches.M042.r1365_checked (by decide +kernel)
theorem record000_leaf_checked_11 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 11)
      (record000_certificates 11) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 11)
    (.matching Nonrational.InducedTerminalMatches.M042.r1366) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 11) Nonrational.InducedTerminalMatches.M042.r1366
    Nonrational.InducedTerminalMatches.M042.r1366_checked (by decide +kernel)
theorem record000_leaf_checked_12 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 12)
      (record000_certificates 12) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 12)
    (.matching Nonrational.InducedTerminalMatches.M042.r1367) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 12) Nonrational.InducedTerminalMatches.M042.r1367
    Nonrational.InducedTerminalMatches.M042.r1367_checked (by decide +kernel)
theorem record000_leaf_checked_13 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 13)
      (record000_certificates 13) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 13)
    (.matching Nonrational.InducedTerminalMatches.M042.r1368) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 13) Nonrational.InducedTerminalMatches.M042.r1368
    Nonrational.InducedTerminalMatches.M042.r1368_checked (by decide +kernel)
theorem record000_leaf_checked_14 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 14)
      (record000_certificates 14) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 14)
    (.matching Nonrational.InducedTerminalMatches.M042.r1369) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 14) Nonrational.InducedTerminalMatches.M042.r1369
    Nonrational.InducedTerminalMatches.M042.r1369_checked (by decide +kernel)
theorem record000_leaf_checked_15 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 15)
      (record000_certificates 15) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 15)
    (.matching Nonrational.InducedTerminalMatches.M042.r1370) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 15) Nonrational.InducedTerminalMatches.M042.r1370
    Nonrational.InducedTerminalMatches.M042.r1370_checked (by decide +kernel)
theorem record000_leaf_checked_16 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 16)
      (record000_certificates 16) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 16)
    (.matching Nonrational.InducedTerminalMatches.M042.r1371) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 16) Nonrational.InducedTerminalMatches.M042.r1371
    Nonrational.InducedTerminalMatches.M042.r1371_checked (by decide +kernel)
theorem record000_leaf_checked_17 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 17)
      (record000_certificates 17) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 17)
    (.matching Nonrational.InducedTerminalMatches.M042.r1372) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 17) Nonrational.InducedTerminalMatches.M042.r1372
    Nonrational.InducedTerminalMatches.M042.r1372_checked (by decide +kernel)
theorem record000_leaf_checked_18 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 18)
      (record000_certificates 18) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 18)
    (.matching Nonrational.InducedTerminalMatches.M042.r1373) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 18) Nonrational.InducedTerminalMatches.M042.r1373
    Nonrational.InducedTerminalMatches.M042.r1373_checked (by decide +kernel)
theorem record000_leaf_checked_19 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 19)
      (record000_certificates 19) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 19)
    (.matching Nonrational.InducedTerminalMatches.M042.r1374) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 19) Nonrational.InducedTerminalMatches.M042.r1374
    Nonrational.InducedTerminalMatches.M042.r1374_checked (by decide +kernel)
theorem record000_leaf_checked_20 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 20)
      (record000_certificates 20) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 20)
    (.matching Nonrational.InducedTerminalMatches.M042.r1375) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 20) Nonrational.InducedTerminalMatches.M042.r1375
    Nonrational.InducedTerminalMatches.M042.r1375_checked (by decide +kernel)
theorem record000_leaf_checked_21 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 21)
      (record000_certificates 21) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 21)
    (.matching Nonrational.InducedTerminalMatches.M043.r1376) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 21) Nonrational.InducedTerminalMatches.M043.r1376
    Nonrational.InducedTerminalMatches.M043.r1376_checked (by decide +kernel)
theorem record000_leaf_checked_22 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 22)
      (record000_certificates 22) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 22)
    (.matching Nonrational.InducedTerminalMatches.M043.r1377) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 22) Nonrational.InducedTerminalMatches.M043.r1377
    Nonrational.InducedTerminalMatches.M043.r1377_checked (by decide +kernel)
theorem record000_leaf_checked_23 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 23)
      (record000_certificates 23) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 23)
    (.matching Nonrational.InducedTerminalMatches.M043.r1378) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 23) Nonrational.InducedTerminalMatches.M043.r1378
    Nonrational.InducedTerminalMatches.M043.r1378_checked (by decide +kernel)
theorem record000_leaf_checked_24 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 24)
      (record000_certificates 24) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 24)
    (.matching Nonrational.InducedTerminalMatches.M043.r1379) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 24) Nonrational.InducedTerminalMatches.M043.r1379
    Nonrational.InducedTerminalMatches.M043.r1379_checked (by decide +kernel)
theorem record000_leaf_checked_25 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 25)
      (record000_certificates 25) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 25)
    (.matching Nonrational.InducedTerminalMatches.M043.r1380) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 25) Nonrational.InducedTerminalMatches.M043.r1380
    Nonrational.InducedTerminalMatches.M043.r1380_checked (by decide +kernel)
theorem record000_leaf_checked_26 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 26)
      (record000_certificates 26) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 26)
    (.matching Nonrational.InducedTerminalMatches.M043.r1381) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 26) Nonrational.InducedTerminalMatches.M043.r1381
    Nonrational.InducedTerminalMatches.M043.r1381_checked (by decide +kernel)
theorem record000_leaf_checked_27 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 27)
      (record000_certificates 27) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 27)
    (.matching Nonrational.InducedTerminalMatches.M043.r1382) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 27) Nonrational.InducedTerminalMatches.M043.r1382
    Nonrational.InducedTerminalMatches.M043.r1382_checked (by decide +kernel)
theorem record000_leaf_checked_28 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 28)
      (record000_certificates 28) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 28)
    (.matching Nonrational.InducedTerminalMatches.M043.r1383) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 28) Nonrational.InducedTerminalMatches.M043.r1383
    Nonrational.InducedTerminalMatches.M043.r1383_checked (by decide +kernel)
theorem record000_leaf_checked_29 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 29)
      (record000_certificates 29) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 29)
    (.matching Nonrational.InducedTerminalMatches.M043.r1384) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 29) Nonrational.InducedTerminalMatches.M043.r1384
    Nonrational.InducedTerminalMatches.M043.r1384_checked (by decide +kernel)
theorem record000_leaf_checked_30 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 30)
      (record000_certificates 30) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 30)
    (.matching Nonrational.InducedTerminalMatches.M043.r1385) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 30) Nonrational.InducedTerminalMatches.M043.r1385
    Nonrational.InducedTerminalMatches.M043.r1385_checked (by decide +kernel)
theorem record000_leaf_checked_31 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 31)
      (record000_certificates 31) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 31)
    (.matching Nonrational.InducedTerminalMatches.M043.r1386) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 31) Nonrational.InducedTerminalMatches.M043.r1386
    Nonrational.InducedTerminalMatches.M043.r1386_checked (by decide +kernel)
theorem record000_leaf_checked_32 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 32)
      (record000_certificates 32) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 32)
    (.matching Nonrational.InducedTerminalMatches.M043.r1387) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 32) Nonrational.InducedTerminalMatches.M043.r1387
    Nonrational.InducedTerminalMatches.M043.r1387_checked (by decide +kernel)
theorem record000_leaf_checked_33 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 33)
      (record000_certificates 33) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 33)
    (.matching Nonrational.InducedTerminalMatches.M043.r1388) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 33) Nonrational.InducedTerminalMatches.M043.r1388
    Nonrational.InducedTerminalMatches.M043.r1388_checked (by decide +kernel)
theorem record000_leaf_checked_34 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 34)
      (record000_certificates 34) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 34)
    (.matching Nonrational.InducedTerminalMatches.M043.r1389) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 34) Nonrational.InducedTerminalMatches.M043.r1389
    Nonrational.InducedTerminalMatches.M043.r1389_checked (by decide +kernel)
theorem record000_leaf_checked_35 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 35)
      (record000_certificates 35) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 35)
    (.matching Nonrational.InducedTerminalMatches.M043.r1390) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 35) Nonrational.InducedTerminalMatches.M043.r1390
    Nonrational.InducedTerminalMatches.M043.r1390_checked (by decide +kernel)
theorem record000_leaf_checked_36 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 36)
      (record000_certificates 36) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 36)
    (.matching Nonrational.InducedTerminalMatches.M043.r1391) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 36) Nonrational.InducedTerminalMatches.M043.r1391
    Nonrational.InducedTerminalMatches.M043.r1391_checked (by decide +kernel)
theorem record000_leaf_checked_37 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 37)
      (record000_certificates 37) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 37)
    (.matching Nonrational.InducedTerminalMatches.M043.r1392) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 37) Nonrational.InducedTerminalMatches.M043.r1392
    Nonrational.InducedTerminalMatches.M043.r1392_checked (by decide +kernel)
theorem record000_leaf_checked_38 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 38)
      (record000_certificates 38) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 38)
    (.matching Nonrational.InducedTerminalMatches.M043.r1393) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 38) Nonrational.InducedTerminalMatches.M043.r1393
    Nonrational.InducedTerminalMatches.M043.r1393_checked (by decide +kernel)
theorem record000_leaf_checked_39 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 39)
      (record000_certificates 39) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 39)
    (.matching Nonrational.InducedTerminalMatches.M043.r1394) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 39) Nonrational.InducedTerminalMatches.M043.r1394
    Nonrational.InducedTerminalMatches.M043.r1394_checked (by decide +kernel)
theorem record000_leaf_checked_40 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 40)
      (record000_certificates 40) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 40)
    (.matching Nonrational.InducedTerminalMatches.M043.r1395) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 40) Nonrational.InducedTerminalMatches.M043.r1395
    Nonrational.InducedTerminalMatches.M043.r1395_checked (by decide +kernel)
theorem record000_leaf_checked_41 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 41)
      (record000_certificates 41) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 41)
    (.matching Nonrational.InducedTerminalMatches.M043.r1396) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 41) Nonrational.InducedTerminalMatches.M043.r1396
    Nonrational.InducedTerminalMatches.M043.r1396_checked (by decide +kernel)
theorem record000_leaf_checked_42 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 42)
      (record000_certificates 42) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 42)
    (.matching Nonrational.InducedTerminalMatches.M043.r1397) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 42) Nonrational.InducedTerminalMatches.M043.r1397
    Nonrational.InducedTerminalMatches.M043.r1397_checked (by decide +kernel)
theorem record000_leaf_checked_43 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 43)
      (record000_certificates 43) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 43)
    (.matching Nonrational.InducedTerminalMatches.M043.r1398) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 43) Nonrational.InducedTerminalMatches.M043.r1398
    Nonrational.InducedTerminalMatches.M043.r1398_checked (by decide +kernel)
theorem record000_leaf_checked_44 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 44)
      (record000_certificates 44) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 44)
    (.matching Nonrational.InducedTerminalMatches.M043.r1399) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 44) Nonrational.InducedTerminalMatches.M043.r1399
    Nonrational.InducedTerminalMatches.M043.r1399_checked (by decide +kernel)
theorem record000_leaf_checked_45 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 45)
      (record000_certificates 45) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 45)
    (.matching Nonrational.InducedTerminalMatches.M043.r1400) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 45) Nonrational.InducedTerminalMatches.M043.r1400
    Nonrational.InducedTerminalMatches.M043.r1400_checked (by decide +kernel)
theorem record000_leaf_checked_46 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 46)
      (record000_certificates 46) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 46)
    (.matching Nonrational.InducedTerminalMatches.M043.r1401) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 46) Nonrational.InducedTerminalMatches.M043.r1401
    Nonrational.InducedTerminalMatches.M043.r1401_checked (by decide +kernel)
theorem record000_leaf_checked_47 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 47)
      (record000_certificates 47) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 47)
    (.matching Nonrational.InducedTerminalMatches.M043.r1402) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 47) Nonrational.InducedTerminalMatches.M043.r1402
    Nonrational.InducedTerminalMatches.M043.r1402_checked (by decide +kernel)
theorem record000_leaf_checked_48 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 48)
      (record000_certificates 48) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 48)
    (.matching Nonrational.InducedTerminalMatches.M043.r1403) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 48) Nonrational.InducedTerminalMatches.M043.r1403
    Nonrational.InducedTerminalMatches.M043.r1403_checked (by decide +kernel)
theorem record000_leaf_checked_49 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 49)
      (record000_certificates 49) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 49)
    (.matching Nonrational.InducedTerminalMatches.M043.r1404) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 49) Nonrational.InducedTerminalMatches.M043.r1404
    Nonrational.InducedTerminalMatches.M043.r1404_checked (by decide +kernel)
theorem record000_leaf_checked_50 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 50)
      (record000_certificates 50) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 50)
    (.matching Nonrational.InducedTerminalMatches.M043.r1405) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 50) Nonrational.InducedTerminalMatches.M043.r1405
    Nonrational.InducedTerminalMatches.M043.r1405_checked (by decide +kernel)
theorem record000_leaf_checked_51 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 51)
      (record000_certificates 51) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 51)
    (.matching Nonrational.InducedTerminalMatches.M043.r1406) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 51) Nonrational.InducedTerminalMatches.M043.r1406
    Nonrational.InducedTerminalMatches.M043.r1406_checked (by decide +kernel)
theorem record000_leaf_checked_52 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 52)
      (record000_certificates 52) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 52)
    (.matching Nonrational.InducedTerminalMatches.M043.r1407) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 52) Nonrational.InducedTerminalMatches.M043.r1407
    Nonrational.InducedTerminalMatches.M043.r1407_checked (by decide +kernel)
theorem record000_leaf_checked_53 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 53)
      (record000_certificates 53) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 53)
    (.matching Nonrational.InducedTerminalMatches.M044.r1408) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 53) Nonrational.InducedTerminalMatches.M044.r1408
    Nonrational.InducedTerminalMatches.M044.r1408_checked (by decide +kernel)
theorem record000_leaf_checked_54 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 54)
      (record000_certificates 54) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 54)
    (.matching Nonrational.InducedTerminalMatches.M044.r1409) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 54) Nonrational.InducedTerminalMatches.M044.r1409
    Nonrational.InducedTerminalMatches.M044.r1409_checked (by decide +kernel)
theorem record000_leaf_checked_55 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 55)
      (record000_certificates 55) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 55)
    (.matching Nonrational.InducedTerminalMatches.M044.r1410) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 55) Nonrational.InducedTerminalMatches.M044.r1410
    Nonrational.InducedTerminalMatches.M044.r1410_checked (by decide +kernel)
theorem record000_leaf_checked_56 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 56)
      (record000_certificates 56) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 56)
    (.matching Nonrational.InducedTerminalMatches.M044.r1411) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 56) Nonrational.InducedTerminalMatches.M044.r1411
    Nonrational.InducedTerminalMatches.M044.r1411_checked (by decide +kernel)
theorem record000_leaf_checked_57 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 57)
      (record000_certificates 57) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 57)
    (.matching Nonrational.InducedTerminalMatches.M044.r1412) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 57) Nonrational.InducedTerminalMatches.M044.r1412
    Nonrational.InducedTerminalMatches.M044.r1412_checked (by decide +kernel)
theorem record000_leaf_checked_58 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 58)
      (record000_certificates 58) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 58)
    (.matching Nonrational.InducedTerminalMatches.M044.r1413) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 58) Nonrational.InducedTerminalMatches.M044.r1413
    Nonrational.InducedTerminalMatches.M044.r1413_checked (by decide +kernel)
theorem record000_leaf_checked_59 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 59)
      (record000_certificates 59) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 59)
    (.matching Nonrational.InducedTerminalMatches.M044.r1414) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 59) Nonrational.InducedTerminalMatches.M044.r1414
    Nonrational.InducedTerminalMatches.M044.r1414_checked (by decide +kernel)
theorem record000_leaf_checked_60 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 60)
      (record000_certificates 60) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 60)
    (.matching Nonrational.InducedTerminalMatches.M044.r1415) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 60) Nonrational.InducedTerminalMatches.M044.r1415
    Nonrational.InducedTerminalMatches.M044.r1415_checked (by decide +kernel)
theorem record000_leaf_checked_61 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 61)
      (record000_certificates 61) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 61)
    (.matching Nonrational.InducedTerminalMatches.M044.r1416) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 61) Nonrational.InducedTerminalMatches.M044.r1416
    Nonrational.InducedTerminalMatches.M044.r1416_checked (by decide +kernel)
theorem record000_leaf_checked_62 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 62)
      (record000_certificates 62) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 62)
    (.matching Nonrational.InducedTerminalMatches.M044.r1417) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 62) Nonrational.InducedTerminalMatches.M044.r1417
    Nonrational.InducedTerminalMatches.M044.r1417_checked (by decide +kernel)
theorem record000_leaf_checked_63 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 63)
      (record000_certificates 63) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 63)
    (.matching Nonrational.InducedTerminalMatches.M044.r1418) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 63) Nonrational.InducedTerminalMatches.M044.r1418
    Nonrational.InducedTerminalMatches.M044.r1418_checked (by decide +kernel)
theorem record000_leaf_checked_64 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 64)
      (record000_certificates 64) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 64)
    (.matching Nonrational.InducedTerminalMatches.M044.r1419) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 64) Nonrational.InducedTerminalMatches.M044.r1419
    Nonrational.InducedTerminalMatches.M044.r1419_checked (by decide +kernel)
theorem record000_leaf_checked_65 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 65)
      (record000_certificates 65) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 65)
    (.matching Nonrational.InducedTerminalMatches.M044.r1420) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 65) Nonrational.InducedTerminalMatches.M044.r1420
    Nonrational.InducedTerminalMatches.M044.r1420_checked (by decide +kernel)
theorem record000_leaf_checked_66 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 66)
      (record000_certificates 66) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 66)
    (.matching Nonrational.InducedTerminalMatches.M044.r1421) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 66) Nonrational.InducedTerminalMatches.M044.r1421
    Nonrational.InducedTerminalMatches.M044.r1421_checked (by decide +kernel)
theorem record000_leaf_checked_67 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 67)
      (record000_certificates 67) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 67)
    (.matching Nonrational.InducedTerminalMatches.M044.r1422) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 67) Nonrational.InducedTerminalMatches.M044.r1422
    Nonrational.InducedTerminalMatches.M044.r1422_checked (by decide +kernel)
theorem record000_leaf_checked_68 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 68)
      (record000_certificates 68) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 68)
    (.matching Nonrational.InducedTerminalMatches.M044.r1423) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 68) Nonrational.InducedTerminalMatches.M044.r1423
    Nonrational.InducedTerminalMatches.M044.r1423_checked (by decide +kernel)
theorem record000_leaf_checked_69 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 69)
      (record000_certificates 69) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 69)
    (.matching Nonrational.InducedTerminalMatches.M044.r1424) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 69) Nonrational.InducedTerminalMatches.M044.r1424
    Nonrational.InducedTerminalMatches.M044.r1424_checked (by decide +kernel)
theorem record000_leaf_checked_70 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 70)
      (record000_certificates 70) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 70)
    (.matching Nonrational.InducedTerminalMatches.M044.r1425) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 70) Nonrational.InducedTerminalMatches.M044.r1425
    Nonrational.InducedTerminalMatches.M044.r1425_checked (by decide +kernel)
theorem record000_leaf_checked_71 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 71)
      (record000_certificates 71) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 71)
    (.matching Nonrational.InducedTerminalMatches.M044.r1426) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 71) Nonrational.InducedTerminalMatches.M044.r1426
    Nonrational.InducedTerminalMatches.M044.r1426_checked (by decide +kernel)
theorem record000_leaf_checked_72 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 72)
      (record000_certificates 72) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 72)
    (.matching Nonrational.InducedTerminalMatches.M044.r1427) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 72) Nonrational.InducedTerminalMatches.M044.r1427
    Nonrational.InducedTerminalMatches.M044.r1427_checked (by decide +kernel)
theorem record000_leaf_checked_73 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 73)
      (record000_certificates 73) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves 73)
    (.matching Nonrational.InducedTerminalMatches.M044.r1428) = true
  exact matching_checked record000.data.quota (record000_rawLeaves 73) Nonrational.InducedTerminalMatches.M044.r1428
    Nonrational.InducedTerminalMatches.M044.r1428_checked (by decide +kernel)
theorem record000_leaf_certificates_checked : ∀ j : Fin record000.l,
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves j)
      (record000_certificates j) = true :=
  (Fin.cases record000_leaf_checked_0 (Fin.cases record000_leaf_checked_1 (Fin.cases record000_leaf_checked_2 (Fin.cases record000_leaf_checked_3 (Fin.cases record000_leaf_checked_4 (Fin.cases record000_leaf_checked_5 (Fin.cases record000_leaf_checked_6 (Fin.cases record000_leaf_checked_7 (Fin.cases record000_leaf_checked_8 (Fin.cases record000_leaf_checked_9 (Fin.cases record000_leaf_checked_10 (Fin.cases record000_leaf_checked_11 (Fin.cases record000_leaf_checked_12 (Fin.cases record000_leaf_checked_13 (Fin.cases record000_leaf_checked_14 (Fin.cases record000_leaf_checked_15 (Fin.cases record000_leaf_checked_16 (Fin.cases record000_leaf_checked_17 (Fin.cases record000_leaf_checked_18 (Fin.cases record000_leaf_checked_19 (Fin.cases record000_leaf_checked_20 (Fin.cases record000_leaf_checked_21 (Fin.cases record000_leaf_checked_22 (Fin.cases record000_leaf_checked_23 (Fin.cases record000_leaf_checked_24 (Fin.cases record000_leaf_checked_25 (Fin.cases record000_leaf_checked_26 (Fin.cases record000_leaf_checked_27 (Fin.cases record000_leaf_checked_28 (Fin.cases record000_leaf_checked_29 (Fin.cases record000_leaf_checked_30 (Fin.cases record000_leaf_checked_31 (Fin.cases record000_leaf_checked_32 (Fin.cases record000_leaf_checked_33 (Fin.cases record000_leaf_checked_34 (Fin.cases record000_leaf_checked_35 (Fin.cases record000_leaf_checked_36 (Fin.cases record000_leaf_checked_37 (Fin.cases record000_leaf_checked_38 (Fin.cases record000_leaf_checked_39 (Fin.cases record000_leaf_checked_40 (Fin.cases record000_leaf_checked_41 (Fin.cases record000_leaf_checked_42 (Fin.cases record000_leaf_checked_43 (Fin.cases record000_leaf_checked_44 (Fin.cases record000_leaf_checked_45 (Fin.cases record000_leaf_checked_46 (Fin.cases record000_leaf_checked_47 (Fin.cases record000_leaf_checked_48 (Fin.cases record000_leaf_checked_49 (Fin.cases record000_leaf_checked_50 (Fin.cases record000_leaf_checked_51 (Fin.cases record000_leaf_checked_52 (Fin.cases record000_leaf_checked_53 (Fin.cases record000_leaf_checked_54 (Fin.cases record000_leaf_checked_55 (Fin.cases record000_leaf_checked_56 (Fin.cases record000_leaf_checked_57 (Fin.cases record000_leaf_checked_58 (Fin.cases record000_leaf_checked_59 (Fin.cases record000_leaf_checked_60 (Fin.cases record000_leaf_checked_61 (Fin.cases record000_leaf_checked_62 (Fin.cases record000_leaf_checked_63 (Fin.cases record000_leaf_checked_64 (Fin.cases record000_leaf_checked_65 (Fin.cases record000_leaf_checked_66 (Fin.cases record000_leaf_checked_67 (Fin.cases record000_leaf_checked_68 (Fin.cases record000_leaf_checked_69 (Fin.cases record000_leaf_checked_70 (Fin.cases record000_leaf_checked_71 (Fin.cases record000_leaf_checked_72 (Fin.cases record000_leaf_checked_73 (fun j => Fin.elim0 j)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
#print axioms record000_leaf_certificates_checked

end Papers.RationalityTen.CompactReplay.GraphLargeRow29Case01592
