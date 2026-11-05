module
prelude
public import GraphInputsRow29Part00180Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M061
public import InducedTerminalMatches.M062
public import InducedTerminalMatches.M063

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00180
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
(.leaf (.quota 1))
noncomputable def record005_certificates (j : Fin record005.l) : Certificate :=
  record005_certificateTable.get j.val
theorem record005_leaf_checked_0 :
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves 0)
      (record005_certificates 0) = true := by
  change RawLeafCertificate.check record005.data.quota [] (.quota 1) = true
  exact empty_checked record005.data.quota 1 (by decide +kernel)
theorem record005_leaf_certificates_checked : ∀ j : Fin record005.l,
    RawLeafCertificate.check record005.data.quota (record005_rawLeaves j)
      (record005_certificates j) = true :=
  (Fin.cases record005_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record005_leaf_certificates_checked

noncomputable def record006_rawLeaves (j : Fin record006.l) : List Cell :=
  (record006.leaf j).map record006.data.cells
theorem record006_raw_exact (j : Fin record006.l) :
    (record006.leaf j).map record006.data.cells = record006_rawLeaves j := rfl
noncomputable def record006_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record006_certificates (j : Fin record006.l) : Certificate :=
  record006_certificateTable.get j.val
theorem record006_leaf_checked_0 :
    RawLeafCertificate.check record006.data.quota (record006_rawLeaves 0)
      (record006_certificates 0) = true := by
  change RawLeafCertificate.check record006.data.quota [] (.quota 1) = true
  exact empty_checked record006.data.quota 1 (by decide +kernel)
theorem record006_leaf_certificates_checked : ∀ j : Fin record006.l,
    RawLeafCertificate.check record006.data.quota (record006_rawLeaves j)
      (record006_certificates j) = true :=
  (Fin.cases record006_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record006_leaf_certificates_checked

noncomputable def record007_rawLeaves (j : Fin record007.l) : List Cell :=
  (record007.leaf j).map record007.data.cells
theorem record007_raw_exact (j : Fin record007.l) :
    (record007.leaf j).map record007.data.cells = record007_rawLeaves j := rfl
noncomputable def record007_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record007_certificates (j : Fin record007.l) : Certificate :=
  record007_certificateTable.get j.val
theorem record007_leaf_checked_0 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 0)
      (record007_certificates 0) = true := by
  change RawLeafCertificate.check record007.data.quota [] (.quota 1) = true
  exact empty_checked record007.data.quota 1 (by decide +kernel)
theorem record007_leaf_certificates_checked : ∀ j : Fin record007.l,
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves j)
      (record007_certificates j) = true :=
  (Fin.cases record007_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record007_leaf_certificates_checked

noncomputable def record008_rawLeaves (j : Fin record008.l) : List Cell :=
  (record008.leaf j).map record008.data.cells
theorem record008_raw_exact (j : Fin record008.l) :
    (record008.leaf j).map record008.data.cells = record008_rawLeaves j := rfl
noncomputable def record008_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record008_certificates (j : Fin record008.l) : Certificate :=
  record008_certificateTable.get j.val
theorem record008_leaf_checked_0 :
    RawLeafCertificate.check record008.data.quota (record008_rawLeaves 0)
      (record008_certificates 0) = true := by
  change RawLeafCertificate.check record008.data.quota [] (.quota 1) = true
  exact empty_checked record008.data.quota 1 (by decide +kernel)
theorem record008_leaf_certificates_checked : ∀ j : Fin record008.l,
    RawLeafCertificate.check record008.data.quota (record008_rawLeaves j)
      (record008_certificates j) = true :=
  (Fin.cases record008_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record008_leaf_certificates_checked

noncomputable def record009_rawLeaves (j : Fin record009.l) : List Cell :=
  (record009.leaf j).map record009.data.cells
theorem record009_raw_exact (j : Fin record009.l) :
    (record009.leaf j).map record009.data.cells = record009_rawLeaves j := rfl
noncomputable def record009_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record009_certificates (j : Fin record009.l) : Certificate :=
  record009_certificateTable.get j.val
theorem record009_leaf_checked_0 :
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves 0)
      (record009_certificates 0) = true := by
  change RawLeafCertificate.check record009.data.quota [] (.quota 1) = true
  exact empty_checked record009.data.quota 1 (by decide +kernel)
theorem record009_leaf_certificates_checked : ∀ j : Fin record009.l,
    RawLeafCertificate.check record009.data.quota (record009_rawLeaves j)
      (record009_certificates j) = true :=
  (Fin.cases record009_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record009_leaf_certificates_checked

noncomputable def record010_rawLeaves (j : Fin record010.l) : List Cell :=
  (record010.leaf j).map record010.data.cells
theorem record010_raw_exact (j : Fin record010.l) :
    (record010.leaf j).map record010.data.cells = record010_rawLeaves j := rfl
noncomputable def record010_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record010_certificates (j : Fin record010.l) : Certificate :=
  record010_certificateTable.get j.val
theorem record010_leaf_checked_0 :
    RawLeafCertificate.check record010.data.quota (record010_rawLeaves 0)
      (record010_certificates 0) = true := by
  change RawLeafCertificate.check record010.data.quota [] (.quota 1) = true
  exact empty_checked record010.data.quota 1 (by decide +kernel)
theorem record010_leaf_certificates_checked : ∀ j : Fin record010.l,
    RawLeafCertificate.check record010.data.quota (record010_rawLeaves j)
      (record010_certificates j) = true :=
  (Fin.cases record010_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record010_leaf_certificates_checked

noncomputable def record011_rawLeaves (j : Fin record011.l) : List Cell :=
  (record011.leaf j).map record011.data.cells
theorem record011_raw_exact (j : Fin record011.l) :
    (record011.leaf j).map record011.data.cells = record011_rawLeaves j := rfl
noncomputable def record011_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record011_certificates (j : Fin record011.l) : Certificate :=
  record011_certificateTable.get j.val
theorem record011_leaf_checked_0 :
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves 0)
      (record011_certificates 0) = true := by
  change RawLeafCertificate.check record011.data.quota [] (.quota 1) = true
  exact empty_checked record011.data.quota 1 (by decide +kernel)
theorem record011_leaf_certificates_checked : ∀ j : Fin record011.l,
    RawLeafCertificate.check record011.data.quota (record011_rawLeaves j)
      (record011_certificates j) = true :=
  (Fin.cases record011_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record011_leaf_certificates_checked

noncomputable def record012_rawLeaves (j : Fin record012.l) : List Cell :=
  (record012.leaf j).map record012.data.cells
theorem record012_raw_exact (j : Fin record012.l) :
    (record012.leaf j).map record012.data.cells = record012_rawLeaves j := rfl
noncomputable def record012_certificateTable : Table Certificate :=
(.branch 26
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M061.r1966))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M061.r1967))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M061.r1968))))
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M061.r1969))
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M061.r1970))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M061.r1971)))))
 (.branch 9
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M061.r1972))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M061.r1973))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M061.r1974))))
 (.branch 11
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M061.r1975))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M061.r1976)))
 (.branch 12
 (.leaf (.matching Nonrational.InducedTerminalMatches.M061.r1977))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M061.r1978))))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf (.matching Nonrational.InducedTerminalMatches.M061.r1979))
 (.branch 15
 (.leaf (.matching Nonrational.InducedTerminalMatches.M061.r1980))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M061.r1981))))
 (.branch 17
 (.leaf (.matching Nonrational.InducedTerminalMatches.M061.r1982))
 (.branch 18
 (.leaf (.matching Nonrational.InducedTerminalMatches.M061.r1983))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M062.r1984)))))
 (.branch 22
 (.branch 20
 (.leaf (.matching Nonrational.InducedTerminalMatches.M062.r1985))
 (.branch 21
 (.leaf (.matching Nonrational.InducedTerminalMatches.M062.r1986))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M062.r1987))))
 (.branch 24
 (.branch 23
 (.leaf (.matching Nonrational.InducedTerminalMatches.M062.r1988))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M062.r1989)))
 (.branch 25
 (.leaf (.matching Nonrational.InducedTerminalMatches.M062.r1990))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M062.r1991)))))))
 (.branch 39
 (.branch 32
 (.branch 29
 (.branch 27
 (.leaf (.matching Nonrational.InducedTerminalMatches.M062.r1992))
 (.branch 28
 (.leaf (.matching Nonrational.InducedTerminalMatches.M062.r1993))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M062.r1994))))
 (.branch 30
 (.leaf (.matching Nonrational.InducedTerminalMatches.M062.r1995))
 (.branch 31
 (.leaf (.matching Nonrational.InducedTerminalMatches.M062.r1996))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M062.r1997)))))
 (.branch 35
 (.branch 33
 (.leaf (.matching Nonrational.InducedTerminalMatches.M062.r1998))
 (.branch 34
 (.leaf (.matching Nonrational.InducedTerminalMatches.M062.r1999))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M062.r2000))))
 (.branch 37
 (.branch 36
 (.leaf (.matching Nonrational.InducedTerminalMatches.M062.r2001))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M062.r2002)))
 (.branch 38
 (.leaf (.matching Nonrational.InducedTerminalMatches.M062.r2003))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M062.r2004))))))
 (.branch 46
 (.branch 42
 (.branch 40
 (.leaf (.matching Nonrational.InducedTerminalMatches.M062.r2005))
 (.branch 41
 (.leaf (.matching Nonrational.InducedTerminalMatches.M062.r2006))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M062.r2007))))
 (.branch 44
 (.branch 43
 (.leaf (.matching Nonrational.InducedTerminalMatches.M062.r2008))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M062.r2009)))
 (.branch 45
 (.leaf (.matching Nonrational.InducedTerminalMatches.M062.r2010))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M062.r2011)))))
 (.branch 49
 (.branch 47
 (.leaf (.matching Nonrational.InducedTerminalMatches.M062.r2012))
 (.branch 48
 (.leaf (.matching Nonrational.InducedTerminalMatches.M062.r2013))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M062.r2014))))
 (.branch 51
 (.branch 50
 (.leaf (.matching Nonrational.InducedTerminalMatches.M062.r2015))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M063.r2016)))
 (.branch 52
 (.leaf (.matching Nonrational.InducedTerminalMatches.M063.r2017))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M063.r2018))))))))
noncomputable def record012_certificates (j : Fin record012.l) : Certificate :=
  record012_certificateTable.get j.val
theorem record012_leaf_checked_0 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 0)
      (record012_certificates 0) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M061.r1966) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 0) Nonrational.InducedTerminalMatches.M061.r1966
    Nonrational.InducedTerminalMatches.M061.r1966_checked (by decide +kernel)
theorem record012_leaf_checked_1 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 1)
      (record012_certificates 1) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M061.r1967) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 1) Nonrational.InducedTerminalMatches.M061.r1967
    Nonrational.InducedTerminalMatches.M061.r1967_checked (by decide +kernel)
theorem record012_leaf_checked_2 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 2)
      (record012_certificates 2) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M061.r1968) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 2) Nonrational.InducedTerminalMatches.M061.r1968
    Nonrational.InducedTerminalMatches.M061.r1968_checked (by decide +kernel)
theorem record012_leaf_checked_3 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 3)
      (record012_certificates 3) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M061.r1969) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 3) Nonrational.InducedTerminalMatches.M061.r1969
    Nonrational.InducedTerminalMatches.M061.r1969_checked (by decide +kernel)
theorem record012_leaf_checked_4 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 4)
      (record012_certificates 4) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M061.r1970) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 4) Nonrational.InducedTerminalMatches.M061.r1970
    Nonrational.InducedTerminalMatches.M061.r1970_checked (by decide +kernel)
theorem record012_leaf_checked_5 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 5)
      (record012_certificates 5) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 5)
    (.matching Nonrational.InducedTerminalMatches.M061.r1971) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 5) Nonrational.InducedTerminalMatches.M061.r1971
    Nonrational.InducedTerminalMatches.M061.r1971_checked (by decide +kernel)
theorem record012_leaf_checked_6 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 6)
      (record012_certificates 6) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 6)
    (.matching Nonrational.InducedTerminalMatches.M061.r1972) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 6) Nonrational.InducedTerminalMatches.M061.r1972
    Nonrational.InducedTerminalMatches.M061.r1972_checked (by decide +kernel)
theorem record012_leaf_checked_7 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 7)
      (record012_certificates 7) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 7)
    (.matching Nonrational.InducedTerminalMatches.M061.r1973) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 7) Nonrational.InducedTerminalMatches.M061.r1973
    Nonrational.InducedTerminalMatches.M061.r1973_checked (by decide +kernel)
theorem record012_leaf_checked_8 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 8)
      (record012_certificates 8) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 8)
    (.matching Nonrational.InducedTerminalMatches.M061.r1974) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 8) Nonrational.InducedTerminalMatches.M061.r1974
    Nonrational.InducedTerminalMatches.M061.r1974_checked (by decide +kernel)
theorem record012_leaf_checked_9 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 9)
      (record012_certificates 9) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 9)
    (.matching Nonrational.InducedTerminalMatches.M061.r1975) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 9) Nonrational.InducedTerminalMatches.M061.r1975
    Nonrational.InducedTerminalMatches.M061.r1975_checked (by decide +kernel)
theorem record012_leaf_checked_10 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 10)
      (record012_certificates 10) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 10)
    (.matching Nonrational.InducedTerminalMatches.M061.r1976) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 10) Nonrational.InducedTerminalMatches.M061.r1976
    Nonrational.InducedTerminalMatches.M061.r1976_checked (by decide +kernel)
theorem record012_leaf_checked_11 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 11)
      (record012_certificates 11) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 11)
    (.matching Nonrational.InducedTerminalMatches.M061.r1977) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 11) Nonrational.InducedTerminalMatches.M061.r1977
    Nonrational.InducedTerminalMatches.M061.r1977_checked (by decide +kernel)
theorem record012_leaf_checked_12 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 12)
      (record012_certificates 12) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 12)
    (.matching Nonrational.InducedTerminalMatches.M061.r1978) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 12) Nonrational.InducedTerminalMatches.M061.r1978
    Nonrational.InducedTerminalMatches.M061.r1978_checked (by decide +kernel)
theorem record012_leaf_checked_13 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 13)
      (record012_certificates 13) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 13)
    (.matching Nonrational.InducedTerminalMatches.M061.r1979) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 13) Nonrational.InducedTerminalMatches.M061.r1979
    Nonrational.InducedTerminalMatches.M061.r1979_checked (by decide +kernel)
theorem record012_leaf_checked_14 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 14)
      (record012_certificates 14) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 14)
    (.matching Nonrational.InducedTerminalMatches.M061.r1980) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 14) Nonrational.InducedTerminalMatches.M061.r1980
    Nonrational.InducedTerminalMatches.M061.r1980_checked (by decide +kernel)
theorem record012_leaf_checked_15 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 15)
      (record012_certificates 15) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 15)
    (.matching Nonrational.InducedTerminalMatches.M061.r1981) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 15) Nonrational.InducedTerminalMatches.M061.r1981
    Nonrational.InducedTerminalMatches.M061.r1981_checked (by decide +kernel)
theorem record012_leaf_checked_16 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 16)
      (record012_certificates 16) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 16)
    (.matching Nonrational.InducedTerminalMatches.M061.r1982) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 16) Nonrational.InducedTerminalMatches.M061.r1982
    Nonrational.InducedTerminalMatches.M061.r1982_checked (by decide +kernel)
theorem record012_leaf_checked_17 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 17)
      (record012_certificates 17) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 17)
    (.matching Nonrational.InducedTerminalMatches.M061.r1983) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 17) Nonrational.InducedTerminalMatches.M061.r1983
    Nonrational.InducedTerminalMatches.M061.r1983_checked (by decide +kernel)
theorem record012_leaf_checked_18 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 18)
      (record012_certificates 18) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 18)
    (.matching Nonrational.InducedTerminalMatches.M062.r1984) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 18) Nonrational.InducedTerminalMatches.M062.r1984
    Nonrational.InducedTerminalMatches.M062.r1984_checked (by decide +kernel)
theorem record012_leaf_checked_19 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 19)
      (record012_certificates 19) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 19)
    (.matching Nonrational.InducedTerminalMatches.M062.r1985) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 19) Nonrational.InducedTerminalMatches.M062.r1985
    Nonrational.InducedTerminalMatches.M062.r1985_checked (by decide +kernel)
theorem record012_leaf_checked_20 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 20)
      (record012_certificates 20) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 20)
    (.matching Nonrational.InducedTerminalMatches.M062.r1986) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 20) Nonrational.InducedTerminalMatches.M062.r1986
    Nonrational.InducedTerminalMatches.M062.r1986_checked (by decide +kernel)
theorem record012_leaf_checked_21 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 21)
      (record012_certificates 21) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 21)
    (.matching Nonrational.InducedTerminalMatches.M062.r1987) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 21) Nonrational.InducedTerminalMatches.M062.r1987
    Nonrational.InducedTerminalMatches.M062.r1987_checked (by decide +kernel)
theorem record012_leaf_checked_22 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 22)
      (record012_certificates 22) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 22)
    (.matching Nonrational.InducedTerminalMatches.M062.r1988) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 22) Nonrational.InducedTerminalMatches.M062.r1988
    Nonrational.InducedTerminalMatches.M062.r1988_checked (by decide +kernel)
theorem record012_leaf_checked_23 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 23)
      (record012_certificates 23) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 23)
    (.matching Nonrational.InducedTerminalMatches.M062.r1989) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 23) Nonrational.InducedTerminalMatches.M062.r1989
    Nonrational.InducedTerminalMatches.M062.r1989_checked (by decide +kernel)
theorem record012_leaf_checked_24 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 24)
      (record012_certificates 24) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 24)
    (.matching Nonrational.InducedTerminalMatches.M062.r1990) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 24) Nonrational.InducedTerminalMatches.M062.r1990
    Nonrational.InducedTerminalMatches.M062.r1990_checked (by decide +kernel)
theorem record012_leaf_checked_25 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 25)
      (record012_certificates 25) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 25)
    (.matching Nonrational.InducedTerminalMatches.M062.r1991) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 25) Nonrational.InducedTerminalMatches.M062.r1991
    Nonrational.InducedTerminalMatches.M062.r1991_checked (by decide +kernel)
theorem record012_leaf_checked_26 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 26)
      (record012_certificates 26) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 26)
    (.matching Nonrational.InducedTerminalMatches.M062.r1992) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 26) Nonrational.InducedTerminalMatches.M062.r1992
    Nonrational.InducedTerminalMatches.M062.r1992_checked (by decide +kernel)
theorem record012_leaf_checked_27 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 27)
      (record012_certificates 27) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 27)
    (.matching Nonrational.InducedTerminalMatches.M062.r1993) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 27) Nonrational.InducedTerminalMatches.M062.r1993
    Nonrational.InducedTerminalMatches.M062.r1993_checked (by decide +kernel)
theorem record012_leaf_checked_28 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 28)
      (record012_certificates 28) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 28)
    (.matching Nonrational.InducedTerminalMatches.M062.r1994) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 28) Nonrational.InducedTerminalMatches.M062.r1994
    Nonrational.InducedTerminalMatches.M062.r1994_checked (by decide +kernel)
theorem record012_leaf_checked_29 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 29)
      (record012_certificates 29) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 29)
    (.matching Nonrational.InducedTerminalMatches.M062.r1995) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 29) Nonrational.InducedTerminalMatches.M062.r1995
    Nonrational.InducedTerminalMatches.M062.r1995_checked (by decide +kernel)
theorem record012_leaf_checked_30 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 30)
      (record012_certificates 30) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 30)
    (.matching Nonrational.InducedTerminalMatches.M062.r1996) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 30) Nonrational.InducedTerminalMatches.M062.r1996
    Nonrational.InducedTerminalMatches.M062.r1996_checked (by decide +kernel)
theorem record012_leaf_checked_31 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 31)
      (record012_certificates 31) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 31)
    (.matching Nonrational.InducedTerminalMatches.M062.r1997) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 31) Nonrational.InducedTerminalMatches.M062.r1997
    Nonrational.InducedTerminalMatches.M062.r1997_checked (by decide +kernel)
theorem record012_leaf_checked_32 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 32)
      (record012_certificates 32) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 32)
    (.matching Nonrational.InducedTerminalMatches.M062.r1998) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 32) Nonrational.InducedTerminalMatches.M062.r1998
    Nonrational.InducedTerminalMatches.M062.r1998_checked (by decide +kernel)
theorem record012_leaf_checked_33 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 33)
      (record012_certificates 33) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 33)
    (.matching Nonrational.InducedTerminalMatches.M062.r1999) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 33) Nonrational.InducedTerminalMatches.M062.r1999
    Nonrational.InducedTerminalMatches.M062.r1999_checked (by decide +kernel)
theorem record012_leaf_checked_34 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 34)
      (record012_certificates 34) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 34)
    (.matching Nonrational.InducedTerminalMatches.M062.r2000) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 34) Nonrational.InducedTerminalMatches.M062.r2000
    Nonrational.InducedTerminalMatches.M062.r2000_checked (by decide +kernel)
theorem record012_leaf_checked_35 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 35)
      (record012_certificates 35) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 35)
    (.matching Nonrational.InducedTerminalMatches.M062.r2001) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 35) Nonrational.InducedTerminalMatches.M062.r2001
    Nonrational.InducedTerminalMatches.M062.r2001_checked (by decide +kernel)
theorem record012_leaf_checked_36 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 36)
      (record012_certificates 36) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 36)
    (.matching Nonrational.InducedTerminalMatches.M062.r2002) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 36) Nonrational.InducedTerminalMatches.M062.r2002
    Nonrational.InducedTerminalMatches.M062.r2002_checked (by decide +kernel)
theorem record012_leaf_checked_37 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 37)
      (record012_certificates 37) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 37)
    (.matching Nonrational.InducedTerminalMatches.M062.r2003) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 37) Nonrational.InducedTerminalMatches.M062.r2003
    Nonrational.InducedTerminalMatches.M062.r2003_checked (by decide +kernel)
theorem record012_leaf_checked_38 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 38)
      (record012_certificates 38) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 38)
    (.matching Nonrational.InducedTerminalMatches.M062.r2004) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 38) Nonrational.InducedTerminalMatches.M062.r2004
    Nonrational.InducedTerminalMatches.M062.r2004_checked (by decide +kernel)
theorem record012_leaf_checked_39 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 39)
      (record012_certificates 39) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 39)
    (.matching Nonrational.InducedTerminalMatches.M062.r2005) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 39) Nonrational.InducedTerminalMatches.M062.r2005
    Nonrational.InducedTerminalMatches.M062.r2005_checked (by decide +kernel)
theorem record012_leaf_checked_40 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 40)
      (record012_certificates 40) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 40)
    (.matching Nonrational.InducedTerminalMatches.M062.r2006) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 40) Nonrational.InducedTerminalMatches.M062.r2006
    Nonrational.InducedTerminalMatches.M062.r2006_checked (by decide +kernel)
theorem record012_leaf_checked_41 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 41)
      (record012_certificates 41) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 41)
    (.matching Nonrational.InducedTerminalMatches.M062.r2007) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 41) Nonrational.InducedTerminalMatches.M062.r2007
    Nonrational.InducedTerminalMatches.M062.r2007_checked (by decide +kernel)
theorem record012_leaf_checked_42 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 42)
      (record012_certificates 42) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 42)
    (.matching Nonrational.InducedTerminalMatches.M062.r2008) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 42) Nonrational.InducedTerminalMatches.M062.r2008
    Nonrational.InducedTerminalMatches.M062.r2008_checked (by decide +kernel)
theorem record012_leaf_checked_43 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 43)
      (record012_certificates 43) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 43)
    (.matching Nonrational.InducedTerminalMatches.M062.r2009) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 43) Nonrational.InducedTerminalMatches.M062.r2009
    Nonrational.InducedTerminalMatches.M062.r2009_checked (by decide +kernel)
theorem record012_leaf_checked_44 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 44)
      (record012_certificates 44) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 44)
    (.matching Nonrational.InducedTerminalMatches.M062.r2010) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 44) Nonrational.InducedTerminalMatches.M062.r2010
    Nonrational.InducedTerminalMatches.M062.r2010_checked (by decide +kernel)
theorem record012_leaf_checked_45 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 45)
      (record012_certificates 45) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 45)
    (.matching Nonrational.InducedTerminalMatches.M062.r2011) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 45) Nonrational.InducedTerminalMatches.M062.r2011
    Nonrational.InducedTerminalMatches.M062.r2011_checked (by decide +kernel)
theorem record012_leaf_checked_46 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 46)
      (record012_certificates 46) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 46)
    (.matching Nonrational.InducedTerminalMatches.M062.r2012) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 46) Nonrational.InducedTerminalMatches.M062.r2012
    Nonrational.InducedTerminalMatches.M062.r2012_checked (by decide +kernel)
theorem record012_leaf_checked_47 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 47)
      (record012_certificates 47) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 47)
    (.matching Nonrational.InducedTerminalMatches.M062.r2013) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 47) Nonrational.InducedTerminalMatches.M062.r2013
    Nonrational.InducedTerminalMatches.M062.r2013_checked (by decide +kernel)
theorem record012_leaf_checked_48 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 48)
      (record012_certificates 48) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 48)
    (.matching Nonrational.InducedTerminalMatches.M062.r2014) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 48) Nonrational.InducedTerminalMatches.M062.r2014
    Nonrational.InducedTerminalMatches.M062.r2014_checked (by decide +kernel)
theorem record012_leaf_checked_49 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 49)
      (record012_certificates 49) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 49)
    (.matching Nonrational.InducedTerminalMatches.M062.r2015) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 49) Nonrational.InducedTerminalMatches.M062.r2015
    Nonrational.InducedTerminalMatches.M062.r2015_checked (by decide +kernel)
theorem record012_leaf_checked_50 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 50)
      (record012_certificates 50) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 50)
    (.matching Nonrational.InducedTerminalMatches.M063.r2016) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 50) Nonrational.InducedTerminalMatches.M063.r2016
    Nonrational.InducedTerminalMatches.M063.r2016_checked (by decide +kernel)
theorem record012_leaf_checked_51 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 51)
      (record012_certificates 51) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 51)
    (.matching Nonrational.InducedTerminalMatches.M063.r2017) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 51) Nonrational.InducedTerminalMatches.M063.r2017
    Nonrational.InducedTerminalMatches.M063.r2017_checked (by decide +kernel)
theorem record012_leaf_checked_52 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 52)
      (record012_certificates 52) = true := by
  change RawLeafCertificate.check record012.data.quota (record012_rawLeaves 52)
    (.matching Nonrational.InducedTerminalMatches.M063.r2018) = true
  exact matching_checked record012.data.quota (record012_rawLeaves 52) Nonrational.InducedTerminalMatches.M063.r2018
    Nonrational.InducedTerminalMatches.M063.r2018_checked (by decide +kernel)
theorem record012_leaf_certificates_checked : ∀ j : Fin record012.l,
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves j)
      (record012_certificates j) = true :=
  (Fin.cases record012_leaf_checked_0 (Fin.cases record012_leaf_checked_1 (Fin.cases record012_leaf_checked_2 (Fin.cases record012_leaf_checked_3 (Fin.cases record012_leaf_checked_4 (Fin.cases record012_leaf_checked_5 (Fin.cases record012_leaf_checked_6 (Fin.cases record012_leaf_checked_7 (Fin.cases record012_leaf_checked_8 (Fin.cases record012_leaf_checked_9 (Fin.cases record012_leaf_checked_10 (Fin.cases record012_leaf_checked_11 (Fin.cases record012_leaf_checked_12 (Fin.cases record012_leaf_checked_13 (Fin.cases record012_leaf_checked_14 (Fin.cases record012_leaf_checked_15 (Fin.cases record012_leaf_checked_16 (Fin.cases record012_leaf_checked_17 (Fin.cases record012_leaf_checked_18 (Fin.cases record012_leaf_checked_19 (Fin.cases record012_leaf_checked_20 (Fin.cases record012_leaf_checked_21 (Fin.cases record012_leaf_checked_22 (Fin.cases record012_leaf_checked_23 (Fin.cases record012_leaf_checked_24 (Fin.cases record012_leaf_checked_25 (Fin.cases record012_leaf_checked_26 (Fin.cases record012_leaf_checked_27 (Fin.cases record012_leaf_checked_28 (Fin.cases record012_leaf_checked_29 (Fin.cases record012_leaf_checked_30 (Fin.cases record012_leaf_checked_31 (Fin.cases record012_leaf_checked_32 (Fin.cases record012_leaf_checked_33 (Fin.cases record012_leaf_checked_34 (Fin.cases record012_leaf_checked_35 (Fin.cases record012_leaf_checked_36 (Fin.cases record012_leaf_checked_37 (Fin.cases record012_leaf_checked_38 (Fin.cases record012_leaf_checked_39 (Fin.cases record012_leaf_checked_40 (Fin.cases record012_leaf_checked_41 (Fin.cases record012_leaf_checked_42 (Fin.cases record012_leaf_checked_43 (Fin.cases record012_leaf_checked_44 (Fin.cases record012_leaf_checked_45 (Fin.cases record012_leaf_checked_46 (Fin.cases record012_leaf_checked_47 (Fin.cases record012_leaf_checked_48 (Fin.cases record012_leaf_checked_49 (Fin.cases record012_leaf_checked_50 (Fin.cases record012_leaf_checked_51 (Fin.cases record012_leaf_checked_52 (fun j => Fin.elim0 j))))))))))))))))))))))))))))))))))))))))))))))))))))))
#print axioms record012_leaf_certificates_checked
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00180
