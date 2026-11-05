module
prelude
public import GraphInputsRow29Part00044Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M040
public import InducedTerminalMatches.M041

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00044
open Papers.RationalityTen ConcreteGrowth RawLeafCertificate FastRawLeafCertificate
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def record000_rawLeaves (j : Fin record000.l) : List Cell :=
  (record000.leaf j).map record000.data.cells
theorem record000_raw_exact (j : Fin record000.l) :
    (record000.leaf j).map record000.data.cells = record000_rawLeaves j := rfl
noncomputable def record000_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record000_certificates (j : Fin record000.l) : Certificate :=
  record000_certificateTable.get j.val
theorem record000_leaf_checked_0 :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves 0)
      (record000_certificates 0) = true := by
  change RawLeafCertificate.check record000.data.quota [] (.quota 1) = true
  exact empty_checked record000.data.quota 1 (by decide +kernel)
theorem record000_leaf_certificates_checked : ∀ j : Fin record000.l,
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves j)
      (record000_certificates j) = true :=
  (Fin.cases record000_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record000_leaf_certificates_checked

noncomputable def record001_rawLeaves (j : Fin record001.l) : List Cell :=
  (record001.leaf j).map record001.data.cells
theorem record001_raw_exact (j : Fin record001.l) :
    (record001.leaf j).map record001.data.cells = record001_rawLeaves j := rfl
noncomputable def record001_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record001_certificates (j : Fin record001.l) : Certificate :=
  record001_certificateTable.get j.val
theorem record001_leaf_checked_0 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 0)
      (record001_certificates 0) = true := by
  change RawLeafCertificate.check record001.data.quota [] (.quota 1) = true
  exact empty_checked record001.data.quota 1 (by decide +kernel)
theorem record001_leaf_certificates_checked : ∀ j : Fin record001.l,
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves j)
      (record001_certificates j) = true :=
  (Fin.cases record001_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record001_leaf_certificates_checked

noncomputable def record002_rawLeaves (j : Fin record002.l) : List Cell :=
  (record002.leaf j).map record002.data.cells
theorem record002_raw_exact (j : Fin record002.l) :
    (record002.leaf j).map record002.data.cells = record002_rawLeaves j := rfl
noncomputable def record002_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record002_certificates (j : Fin record002.l) : Certificate :=
  record002_certificateTable.get j.val
theorem record002_leaf_checked_0 :
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves 0)
      (record002_certificates 0) = true := by
  change RawLeafCertificate.check record002.data.quota [] (.quota 1) = true
  exact empty_checked record002.data.quota 1 (by decide +kernel)
theorem record002_leaf_certificates_checked : ∀ j : Fin record002.l,
    RawLeafCertificate.check record002.data.quota (record002_rawLeaves j)
      (record002_certificates j) = true :=
  (Fin.cases record002_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record002_leaf_certificates_checked

noncomputable def record003_rawLeaves (j : Fin record003.l) : List Cell :=
  (record003.leaf j).map record003.data.cells
theorem record003_raw_exact (j : Fin record003.l) :
    (record003.leaf j).map record003.data.cells = record003_rawLeaves j := rfl
noncomputable def record003_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record003_certificates (j : Fin record003.l) : Certificate :=
  record003_certificateTable.get j.val
theorem record003_leaf_checked_0 :
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves 0)
      (record003_certificates 0) = true := by
  change RawLeafCertificate.check record003.data.quota [] (.quota 1) = true
  exact empty_checked record003.data.quota 1 (by decide +kernel)
theorem record003_leaf_certificates_checked : ∀ j : Fin record003.l,
    RawLeafCertificate.check record003.data.quota (record003_rawLeaves j)
      (record003_certificates j) = true :=
  (Fin.cases record003_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record003_leaf_certificates_checked

noncomputable def record004_rawLeaves (j : Fin record004.l) : List Cell :=
  (record004.leaf j).map record004.data.cells
theorem record004_raw_exact (j : Fin record004.l) :
    (record004.leaf j).map record004.data.cells = record004_rawLeaves j := rfl
noncomputable def record004_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record004_certificates (j : Fin record004.l) : Certificate :=
  record004_certificateTable.get j.val
theorem record004_leaf_checked_0 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 0)
      (record004_certificates 0) = true := by
  change RawLeafCertificate.check record004.data.quota [] (.quota 1) = true
  exact empty_checked record004.data.quota 1 (by decide +kernel)
theorem record004_leaf_certificates_checked : ∀ j : Fin record004.l,
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves j)
      (record004_certificates j) = true :=
  (Fin.cases record004_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record004_leaf_certificates_checked

noncomputable def record005_rawLeaves (j : Fin record005.l) : List Cell :=
  (record005.leaf j).map record005.data.cells
theorem record005_raw_exact (j : Fin record005.l) :
    (record005.leaf j).map record005.data.cells = record005_rawLeaves j := rfl
noncomputable def record005_certificateTable : Table Certificate :=
(.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M040.r1291))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M040.r1292))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M040.r1293))))
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M040.r1294))
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M040.r1295))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M040.r1296)))))
 (.branch 9
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M040.r1297))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M040.r1298))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M040.r1299))))
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M040.r1300))
 (.branch 11
 (.leaf (.matching Nonrational.InducedTerminalMatches.M040.r1301))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M040.r1302))))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf (.matching Nonrational.InducedTerminalMatches.M040.r1303))
 (.branch 14
 (.leaf (.matching Nonrational.InducedTerminalMatches.M040.r1304))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M040.r1305))))
 (.branch 16
 (.leaf (.matching Nonrational.InducedTerminalMatches.M040.r1306))
 (.branch 17
 (.leaf (.matching Nonrational.InducedTerminalMatches.M040.r1307))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M040.r1308)))))
 (.branch 21
 (.branch 19
 (.leaf (.matching Nonrational.InducedTerminalMatches.M040.r1309))
 (.branch 20
 (.leaf (.matching Nonrational.InducedTerminalMatches.M040.r1310))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M040.r1311))))
 (.branch 23
 (.branch 22
 (.leaf (.matching Nonrational.InducedTerminalMatches.M041.r1312))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M041.r1313)))
 (.branch 24
 (.leaf (.matching Nonrational.InducedTerminalMatches.M041.r1314))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M041.r1315)))))))
 (.branch 38
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf (.matching Nonrational.InducedTerminalMatches.M041.r1316))
 (.branch 27
 (.leaf (.matching Nonrational.InducedTerminalMatches.M041.r1317))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M041.r1318))))
 (.branch 29
 (.leaf (.matching Nonrational.InducedTerminalMatches.M041.r1319))
 (.branch 30
 (.leaf (.matching Nonrational.InducedTerminalMatches.M041.r1320))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M041.r1321)))))
 (.branch 34
 (.branch 32
 (.leaf (.matching Nonrational.InducedTerminalMatches.M041.r1322))
 (.branch 33
 (.leaf (.matching Nonrational.InducedTerminalMatches.M041.r1323))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M041.r1324))))
 (.branch 36
 (.branch 35
 (.leaf (.matching Nonrational.InducedTerminalMatches.M041.r1325))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M041.r1326)))
 (.branch 37
 (.leaf (.matching Nonrational.InducedTerminalMatches.M041.r1327))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M041.r1328))))))
 (.branch 44
 (.branch 41
 (.branch 39
 (.leaf (.matching Nonrational.InducedTerminalMatches.M041.r1329))
 (.branch 40
 (.leaf (.matching Nonrational.InducedTerminalMatches.M041.r1330))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M041.r1331))))
 (.branch 42
 (.leaf (.matching Nonrational.InducedTerminalMatches.M041.r1332))
 (.branch 43
 (.leaf (.matching Nonrational.InducedTerminalMatches.M041.r1333))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M041.r1334)))))
 (.branch 47
 (.branch 45
 (.leaf (.matching Nonrational.InducedTerminalMatches.M041.r1335))
 (.branch 46
 (.leaf (.matching Nonrational.InducedTerminalMatches.M041.r1336))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M041.r1337))))
 (.branch 49
 (.branch 48
 (.leaf (.matching Nonrational.InducedTerminalMatches.M041.r1338))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M041.r1339)))
 (.branch 50
 (.leaf (.matching Nonrational.InducedTerminalMatches.M041.r1340))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M041.r1341))))))))
noncomputable def record005_certificates (j : Fin record005.l) : Certificate :=
  record005_certificateTable.get j.val
theorem record005_leaf_checked_0 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 0)
      (record005_certificates 0) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M040.r1291) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 0) Nonrational.InducedTerminalMatches.M040.r1291
    Nonrational.InducedTerminalMatches.M040.r1291_checked (by decide +kernel)
theorem record005_leaf_checked_1 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 1)
      (record005_certificates 1) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M040.r1292) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 1) Nonrational.InducedTerminalMatches.M040.r1292
    Nonrational.InducedTerminalMatches.M040.r1292_checked (by decide +kernel)
theorem record005_leaf_checked_2 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 2)
      (record005_certificates 2) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M040.r1293) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 2) Nonrational.InducedTerminalMatches.M040.r1293
    Nonrational.InducedTerminalMatches.M040.r1293_checked (by decide +kernel)
theorem record005_leaf_checked_3 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 3)
      (record005_certificates 3) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M040.r1294) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 3) Nonrational.InducedTerminalMatches.M040.r1294
    Nonrational.InducedTerminalMatches.M040.r1294_checked (by decide +kernel)
theorem record005_leaf_checked_4 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 4)
      (record005_certificates 4) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M040.r1295) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 4) Nonrational.InducedTerminalMatches.M040.r1295
    Nonrational.InducedTerminalMatches.M040.r1295_checked (by decide +kernel)
theorem record005_leaf_checked_5 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 5)
      (record005_certificates 5) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 5)
    (.matching Nonrational.InducedTerminalMatches.M040.r1296) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 5) Nonrational.InducedTerminalMatches.M040.r1296
    Nonrational.InducedTerminalMatches.M040.r1296_checked (by decide +kernel)
theorem record005_leaf_checked_6 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 6)
      (record005_certificates 6) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 6)
    (.matching Nonrational.InducedTerminalMatches.M040.r1297) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 6) Nonrational.InducedTerminalMatches.M040.r1297
    Nonrational.InducedTerminalMatches.M040.r1297_checked (by decide +kernel)
theorem record005_leaf_checked_7 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 7)
      (record005_certificates 7) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 7)
    (.matching Nonrational.InducedTerminalMatches.M040.r1298) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 7) Nonrational.InducedTerminalMatches.M040.r1298
    Nonrational.InducedTerminalMatches.M040.r1298_checked (by decide +kernel)
theorem record005_leaf_checked_8 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 8)
      (record005_certificates 8) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 8)
    (.matching Nonrational.InducedTerminalMatches.M040.r1299) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 8) Nonrational.InducedTerminalMatches.M040.r1299
    Nonrational.InducedTerminalMatches.M040.r1299_checked (by decide +kernel)
theorem record005_leaf_checked_9 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 9)
      (record005_certificates 9) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 9)
    (.matching Nonrational.InducedTerminalMatches.M040.r1300) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 9) Nonrational.InducedTerminalMatches.M040.r1300
    Nonrational.InducedTerminalMatches.M040.r1300_checked (by decide +kernel)
theorem record005_leaf_checked_10 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 10)
      (record005_certificates 10) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 10)
    (.matching Nonrational.InducedTerminalMatches.M040.r1301) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 10) Nonrational.InducedTerminalMatches.M040.r1301
    Nonrational.InducedTerminalMatches.M040.r1301_checked (by decide +kernel)
theorem record005_leaf_checked_11 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 11)
      (record005_certificates 11) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 11)
    (.matching Nonrational.InducedTerminalMatches.M040.r1302) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 11) Nonrational.InducedTerminalMatches.M040.r1302
    Nonrational.InducedTerminalMatches.M040.r1302_checked (by decide +kernel)
theorem record005_leaf_checked_12 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 12)
      (record005_certificates 12) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 12)
    (.matching Nonrational.InducedTerminalMatches.M040.r1303) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 12) Nonrational.InducedTerminalMatches.M040.r1303
    Nonrational.InducedTerminalMatches.M040.r1303_checked (by decide +kernel)
theorem record005_leaf_checked_13 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 13)
      (record005_certificates 13) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 13)
    (.matching Nonrational.InducedTerminalMatches.M040.r1304) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 13) Nonrational.InducedTerminalMatches.M040.r1304
    Nonrational.InducedTerminalMatches.M040.r1304_checked (by decide +kernel)
theorem record005_leaf_checked_14 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 14)
      (record005_certificates 14) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 14)
    (.matching Nonrational.InducedTerminalMatches.M040.r1305) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 14) Nonrational.InducedTerminalMatches.M040.r1305
    Nonrational.InducedTerminalMatches.M040.r1305_checked (by decide +kernel)
theorem record005_leaf_checked_15 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 15)
      (record005_certificates 15) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 15)
    (.matching Nonrational.InducedTerminalMatches.M040.r1306) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 15) Nonrational.InducedTerminalMatches.M040.r1306
    Nonrational.InducedTerminalMatches.M040.r1306_checked (by decide +kernel)
theorem record005_leaf_checked_16 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 16)
      (record005_certificates 16) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 16)
    (.matching Nonrational.InducedTerminalMatches.M040.r1307) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 16) Nonrational.InducedTerminalMatches.M040.r1307
    Nonrational.InducedTerminalMatches.M040.r1307_checked (by decide +kernel)
theorem record005_leaf_checked_17 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 17)
      (record005_certificates 17) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 17)
    (.matching Nonrational.InducedTerminalMatches.M040.r1308) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 17) Nonrational.InducedTerminalMatches.M040.r1308
    Nonrational.InducedTerminalMatches.M040.r1308_checked (by decide +kernel)
theorem record005_leaf_checked_18 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 18)
      (record005_certificates 18) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 18)
    (.matching Nonrational.InducedTerminalMatches.M040.r1309) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 18) Nonrational.InducedTerminalMatches.M040.r1309
    Nonrational.InducedTerminalMatches.M040.r1309_checked (by decide +kernel)
theorem record005_leaf_checked_19 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 19)
      (record005_certificates 19) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 19)
    (.matching Nonrational.InducedTerminalMatches.M040.r1310) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 19) Nonrational.InducedTerminalMatches.M040.r1310
    Nonrational.InducedTerminalMatches.M040.r1310_checked (by decide +kernel)
theorem record005_leaf_checked_20 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 20)
      (record005_certificates 20) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 20)
    (.matching Nonrational.InducedTerminalMatches.M040.r1311) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 20) Nonrational.InducedTerminalMatches.M040.r1311
    Nonrational.InducedTerminalMatches.M040.r1311_checked (by decide +kernel)
theorem record005_leaf_checked_21 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 21)
      (record005_certificates 21) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 21)
    (.matching Nonrational.InducedTerminalMatches.M041.r1312) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 21) Nonrational.InducedTerminalMatches.M041.r1312
    Nonrational.InducedTerminalMatches.M041.r1312_checked (by decide +kernel)
theorem record005_leaf_checked_22 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 22)
      (record005_certificates 22) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 22)
    (.matching Nonrational.InducedTerminalMatches.M041.r1313) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 22) Nonrational.InducedTerminalMatches.M041.r1313
    Nonrational.InducedTerminalMatches.M041.r1313_checked (by decide +kernel)
theorem record005_leaf_checked_23 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 23)
      (record005_certificates 23) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 23)
    (.matching Nonrational.InducedTerminalMatches.M041.r1314) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 23) Nonrational.InducedTerminalMatches.M041.r1314
    Nonrational.InducedTerminalMatches.M041.r1314_checked (by decide +kernel)
theorem record005_leaf_checked_24 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 24)
      (record005_certificates 24) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 24)
    (.matching Nonrational.InducedTerminalMatches.M041.r1315) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 24) Nonrational.InducedTerminalMatches.M041.r1315
    Nonrational.InducedTerminalMatches.M041.r1315_checked (by decide +kernel)
theorem record005_leaf_checked_25 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 25)
      (record005_certificates 25) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 25)
    (.matching Nonrational.InducedTerminalMatches.M041.r1316) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 25) Nonrational.InducedTerminalMatches.M041.r1316
    Nonrational.InducedTerminalMatches.M041.r1316_checked (by decide +kernel)
theorem record005_leaf_checked_26 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 26)
      (record005_certificates 26) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 26)
    (.matching Nonrational.InducedTerminalMatches.M041.r1317) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 26) Nonrational.InducedTerminalMatches.M041.r1317
    Nonrational.InducedTerminalMatches.M041.r1317_checked (by decide +kernel)
theorem record005_leaf_checked_27 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 27)
      (record005_certificates 27) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 27)
    (.matching Nonrational.InducedTerminalMatches.M041.r1318) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 27) Nonrational.InducedTerminalMatches.M041.r1318
    Nonrational.InducedTerminalMatches.M041.r1318_checked (by decide +kernel)
theorem record005_leaf_checked_28 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 28)
      (record005_certificates 28) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 28)
    (.matching Nonrational.InducedTerminalMatches.M041.r1319) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 28) Nonrational.InducedTerminalMatches.M041.r1319
    Nonrational.InducedTerminalMatches.M041.r1319_checked (by decide +kernel)
theorem record005_leaf_checked_29 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 29)
      (record005_certificates 29) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 29)
    (.matching Nonrational.InducedTerminalMatches.M041.r1320) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 29) Nonrational.InducedTerminalMatches.M041.r1320
    Nonrational.InducedTerminalMatches.M041.r1320_checked (by decide +kernel)
theorem record005_leaf_checked_30 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 30)
      (record005_certificates 30) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 30)
    (.matching Nonrational.InducedTerminalMatches.M041.r1321) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 30) Nonrational.InducedTerminalMatches.M041.r1321
    Nonrational.InducedTerminalMatches.M041.r1321_checked (by decide +kernel)
theorem record005_leaf_checked_31 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 31)
      (record005_certificates 31) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 31)
    (.matching Nonrational.InducedTerminalMatches.M041.r1322) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 31) Nonrational.InducedTerminalMatches.M041.r1322
    Nonrational.InducedTerminalMatches.M041.r1322_checked (by decide +kernel)
theorem record005_leaf_checked_32 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 32)
      (record005_certificates 32) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 32)
    (.matching Nonrational.InducedTerminalMatches.M041.r1323) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 32) Nonrational.InducedTerminalMatches.M041.r1323
    Nonrational.InducedTerminalMatches.M041.r1323_checked (by decide +kernel)
theorem record005_leaf_checked_33 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 33)
      (record005_certificates 33) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 33)
    (.matching Nonrational.InducedTerminalMatches.M041.r1324) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 33) Nonrational.InducedTerminalMatches.M041.r1324
    Nonrational.InducedTerminalMatches.M041.r1324_checked (by decide +kernel)
theorem record005_leaf_checked_34 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 34)
      (record005_certificates 34) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 34)
    (.matching Nonrational.InducedTerminalMatches.M041.r1325) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 34) Nonrational.InducedTerminalMatches.M041.r1325
    Nonrational.InducedTerminalMatches.M041.r1325_checked (by decide +kernel)
theorem record005_leaf_checked_35 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 35)
      (record005_certificates 35) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 35)
    (.matching Nonrational.InducedTerminalMatches.M041.r1326) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 35) Nonrational.InducedTerminalMatches.M041.r1326
    Nonrational.InducedTerminalMatches.M041.r1326_checked (by decide +kernel)
theorem record005_leaf_checked_36 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 36)
      (record005_certificates 36) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 36)
    (.matching Nonrational.InducedTerminalMatches.M041.r1327) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 36) Nonrational.InducedTerminalMatches.M041.r1327
    Nonrational.InducedTerminalMatches.M041.r1327_checked (by decide +kernel)
theorem record005_leaf_checked_37 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 37)
      (record005_certificates 37) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 37)
    (.matching Nonrational.InducedTerminalMatches.M041.r1328) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 37) Nonrational.InducedTerminalMatches.M041.r1328
    Nonrational.InducedTerminalMatches.M041.r1328_checked (by decide +kernel)
theorem record005_leaf_checked_38 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 38)
      (record005_certificates 38) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 38)
    (.matching Nonrational.InducedTerminalMatches.M041.r1329) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 38) Nonrational.InducedTerminalMatches.M041.r1329
    Nonrational.InducedTerminalMatches.M041.r1329_checked (by decide +kernel)
theorem record005_leaf_checked_39 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 39)
      (record005_certificates 39) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 39)
    (.matching Nonrational.InducedTerminalMatches.M041.r1330) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 39) Nonrational.InducedTerminalMatches.M041.r1330
    Nonrational.InducedTerminalMatches.M041.r1330_checked (by decide +kernel)
theorem record005_leaf_checked_40 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 40)
      (record005_certificates 40) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 40)
    (.matching Nonrational.InducedTerminalMatches.M041.r1331) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 40) Nonrational.InducedTerminalMatches.M041.r1331
    Nonrational.InducedTerminalMatches.M041.r1331_checked (by decide +kernel)
theorem record005_leaf_checked_41 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 41)
      (record005_certificates 41) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 41)
    (.matching Nonrational.InducedTerminalMatches.M041.r1332) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 41) Nonrational.InducedTerminalMatches.M041.r1332
    Nonrational.InducedTerminalMatches.M041.r1332_checked (by decide +kernel)
theorem record005_leaf_checked_42 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 42)
      (record005_certificates 42) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 42)
    (.matching Nonrational.InducedTerminalMatches.M041.r1333) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 42) Nonrational.InducedTerminalMatches.M041.r1333
    Nonrational.InducedTerminalMatches.M041.r1333_checked (by decide +kernel)
theorem record005_leaf_checked_43 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 43)
      (record005_certificates 43) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 43)
    (.matching Nonrational.InducedTerminalMatches.M041.r1334) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 43) Nonrational.InducedTerminalMatches.M041.r1334
    Nonrational.InducedTerminalMatches.M041.r1334_checked (by decide +kernel)
theorem record005_leaf_checked_44 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 44)
      (record005_certificates 44) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 44)
    (.matching Nonrational.InducedTerminalMatches.M041.r1335) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 44) Nonrational.InducedTerminalMatches.M041.r1335
    Nonrational.InducedTerminalMatches.M041.r1335_checked (by decide +kernel)
theorem record005_leaf_checked_45 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 45)
      (record005_certificates 45) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 45)
    (.matching Nonrational.InducedTerminalMatches.M041.r1336) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 45) Nonrational.InducedTerminalMatches.M041.r1336
    Nonrational.InducedTerminalMatches.M041.r1336_checked (by decide +kernel)
theorem record005_leaf_checked_46 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 46)
      (record005_certificates 46) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 46)
    (.matching Nonrational.InducedTerminalMatches.M041.r1337) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 46) Nonrational.InducedTerminalMatches.M041.r1337
    Nonrational.InducedTerminalMatches.M041.r1337_checked (by decide +kernel)
theorem record005_leaf_checked_47 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 47)
      (record005_certificates 47) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 47)
    (.matching Nonrational.InducedTerminalMatches.M041.r1338) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 47) Nonrational.InducedTerminalMatches.M041.r1338
    Nonrational.InducedTerminalMatches.M041.r1338_checked (by decide +kernel)
theorem record005_leaf_checked_48 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 48)
      (record005_certificates 48) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 48)
    (.matching Nonrational.InducedTerminalMatches.M041.r1339) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 48) Nonrational.InducedTerminalMatches.M041.r1339
    Nonrational.InducedTerminalMatches.M041.r1339_checked (by decide +kernel)
theorem record005_leaf_checked_49 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 49)
      (record005_certificates 49) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 49)
    (.matching Nonrational.InducedTerminalMatches.M041.r1340) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 49) Nonrational.InducedTerminalMatches.M041.r1340
    Nonrational.InducedTerminalMatches.M041.r1340_checked (by decide +kernel)
theorem record005_leaf_checked_50 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 50)
      (record005_certificates 50) = true := by
  change RawLeafCertificate.check record005.data.quota (record005_rawLeaves 50)
    (.matching Nonrational.InducedTerminalMatches.M041.r1341) = true
  exact matching_checked record005.data.quota (record005_rawLeaves 50) Nonrational.InducedTerminalMatches.M041.r1341
    Nonrational.InducedTerminalMatches.M041.r1341_checked (by decide +kernel)
theorem record005_leaf_certificates_checked : ∀ j : Fin record005.l,
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves j)
      (record005_certificates j) = true :=
  (Fin.cases record005_leaf_checked_0 (Fin.cases record005_leaf_checked_1 (Fin.cases record005_leaf_checked_2 (Fin.cases record005_leaf_checked_3 (Fin.cases record005_leaf_checked_4 (Fin.cases record005_leaf_checked_5 (Fin.cases record005_leaf_checked_6 (Fin.cases record005_leaf_checked_7 (Fin.cases record005_leaf_checked_8 (Fin.cases record005_leaf_checked_9 (Fin.cases record005_leaf_checked_10 (Fin.cases record005_leaf_checked_11 (Fin.cases record005_leaf_checked_12 (Fin.cases record005_leaf_checked_13 (Fin.cases record005_leaf_checked_14 (Fin.cases record005_leaf_checked_15 (Fin.cases record005_leaf_checked_16 (Fin.cases record005_leaf_checked_17 (Fin.cases record005_leaf_checked_18 (Fin.cases record005_leaf_checked_19 (Fin.cases record005_leaf_checked_20 (Fin.cases record005_leaf_checked_21 (Fin.cases record005_leaf_checked_22 (Fin.cases record005_leaf_checked_23 (Fin.cases record005_leaf_checked_24 (Fin.cases record005_leaf_checked_25 (Fin.cases record005_leaf_checked_26 (Fin.cases record005_leaf_checked_27 (Fin.cases record005_leaf_checked_28 (Fin.cases record005_leaf_checked_29 (Fin.cases record005_leaf_checked_30 (Fin.cases record005_leaf_checked_31 (Fin.cases record005_leaf_checked_32 (Fin.cases record005_leaf_checked_33 (Fin.cases record005_leaf_checked_34 (Fin.cases record005_leaf_checked_35 (Fin.cases record005_leaf_checked_36 (Fin.cases record005_leaf_checked_37 (Fin.cases record005_leaf_checked_38 (Fin.cases record005_leaf_checked_39 (Fin.cases record005_leaf_checked_40 (Fin.cases record005_leaf_checked_41 (Fin.cases record005_leaf_checked_42 (Fin.cases record005_leaf_checked_43 (Fin.cases record005_leaf_checked_44 (Fin.cases record005_leaf_checked_45 (Fin.cases record005_leaf_checked_46 (Fin.cases record005_leaf_checked_47 (Fin.cases record005_leaf_checked_48 (Fin.cases record005_leaf_checked_49 (Fin.cases record005_leaf_checked_50 (fun j => Fin.elim0 j))))))))))))))))))))))))))))))))))))))))))))))))))))
#print axioms record005_leaf_certificates_checked
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00044
