module
prelude
public import GraphInputsRow29Part00142Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M059

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00142
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
(.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1888))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1889))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1890))))
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1891))
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1892))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1893)))))
 (.branch 9
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1894))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1895))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1896))))
 (.branch 11
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1897))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1898)))
 (.branch 12
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1899))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1900))))))
 (.branch 20
 (.branch 16
 (.branch 14
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1901))
 (.branch 15
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1902))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1903))))
 (.branch 18
 (.branch 17
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1904))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1905)))
 (.branch 19
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1906))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1907)))))
 (.branch 23
 (.branch 21
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1908))
 (.branch 22
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1909))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1910))))
 (.branch 25
 (.branch 24
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1911))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1912)))
 (.branch 26
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1913))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1914)))))))
noncomputable def record001_certificates (j : Fin record001.l) : Certificate :=
  record001_certificateTable.get j.val
theorem record001_leaf_checked_0 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 0)
      (record001_certificates 0) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M059.r1888) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 0) Nonrational.InducedTerminalMatches.M059.r1888
    Nonrational.InducedTerminalMatches.M059.r1888_checked (by decide +kernel)
theorem record001_leaf_checked_1 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 1)
      (record001_certificates 1) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M059.r1889) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 1) Nonrational.InducedTerminalMatches.M059.r1889
    Nonrational.InducedTerminalMatches.M059.r1889_checked (by decide +kernel)
theorem record001_leaf_checked_2 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 2)
      (record001_certificates 2) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M059.r1890) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 2) Nonrational.InducedTerminalMatches.M059.r1890
    Nonrational.InducedTerminalMatches.M059.r1890_checked (by decide +kernel)
theorem record001_leaf_checked_3 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 3)
      (record001_certificates 3) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M059.r1891) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 3) Nonrational.InducedTerminalMatches.M059.r1891
    Nonrational.InducedTerminalMatches.M059.r1891_checked (by decide +kernel)
theorem record001_leaf_checked_4 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 4)
      (record001_certificates 4) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M059.r1892) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 4) Nonrational.InducedTerminalMatches.M059.r1892
    Nonrational.InducedTerminalMatches.M059.r1892_checked (by decide +kernel)
theorem record001_leaf_checked_5 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 5)
      (record001_certificates 5) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 5)
    (.matching Nonrational.InducedTerminalMatches.M059.r1893) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 5) Nonrational.InducedTerminalMatches.M059.r1893
    Nonrational.InducedTerminalMatches.M059.r1893_checked (by decide +kernel)
theorem record001_leaf_checked_6 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 6)
      (record001_certificates 6) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 6)
    (.matching Nonrational.InducedTerminalMatches.M059.r1894) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 6) Nonrational.InducedTerminalMatches.M059.r1894
    Nonrational.InducedTerminalMatches.M059.r1894_checked (by decide +kernel)
theorem record001_leaf_checked_7 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 7)
      (record001_certificates 7) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 7)
    (.matching Nonrational.InducedTerminalMatches.M059.r1895) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 7) Nonrational.InducedTerminalMatches.M059.r1895
    Nonrational.InducedTerminalMatches.M059.r1895_checked (by decide +kernel)
theorem record001_leaf_checked_8 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 8)
      (record001_certificates 8) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 8)
    (.matching Nonrational.InducedTerminalMatches.M059.r1896) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 8) Nonrational.InducedTerminalMatches.M059.r1896
    Nonrational.InducedTerminalMatches.M059.r1896_checked (by decide +kernel)
theorem record001_leaf_checked_9 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 9)
      (record001_certificates 9) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 9)
    (.matching Nonrational.InducedTerminalMatches.M059.r1897) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 9) Nonrational.InducedTerminalMatches.M059.r1897
    Nonrational.InducedTerminalMatches.M059.r1897_checked (by decide +kernel)
theorem record001_leaf_checked_10 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 10)
      (record001_certificates 10) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 10)
    (.matching Nonrational.InducedTerminalMatches.M059.r1898) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 10) Nonrational.InducedTerminalMatches.M059.r1898
    Nonrational.InducedTerminalMatches.M059.r1898_checked (by decide +kernel)
theorem record001_leaf_checked_11 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 11)
      (record001_certificates 11) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 11)
    (.matching Nonrational.InducedTerminalMatches.M059.r1899) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 11) Nonrational.InducedTerminalMatches.M059.r1899
    Nonrational.InducedTerminalMatches.M059.r1899_checked (by decide +kernel)
theorem record001_leaf_checked_12 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 12)
      (record001_certificates 12) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 12)
    (.matching Nonrational.InducedTerminalMatches.M059.r1900) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 12) Nonrational.InducedTerminalMatches.M059.r1900
    Nonrational.InducedTerminalMatches.M059.r1900_checked (by decide +kernel)
theorem record001_leaf_checked_13 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 13)
      (record001_certificates 13) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 13)
    (.matching Nonrational.InducedTerminalMatches.M059.r1901) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 13) Nonrational.InducedTerminalMatches.M059.r1901
    Nonrational.InducedTerminalMatches.M059.r1901_checked (by decide +kernel)
theorem record001_leaf_checked_14 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 14)
      (record001_certificates 14) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 14)
    (.matching Nonrational.InducedTerminalMatches.M059.r1902) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 14) Nonrational.InducedTerminalMatches.M059.r1902
    Nonrational.InducedTerminalMatches.M059.r1902_checked (by decide +kernel)
theorem record001_leaf_checked_15 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 15)
      (record001_certificates 15) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 15)
    (.matching Nonrational.InducedTerminalMatches.M059.r1903) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 15) Nonrational.InducedTerminalMatches.M059.r1903
    Nonrational.InducedTerminalMatches.M059.r1903_checked (by decide +kernel)
theorem record001_leaf_checked_16 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 16)
      (record001_certificates 16) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 16)
    (.matching Nonrational.InducedTerminalMatches.M059.r1904) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 16) Nonrational.InducedTerminalMatches.M059.r1904
    Nonrational.InducedTerminalMatches.M059.r1904_checked (by decide +kernel)
theorem record001_leaf_checked_17 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 17)
      (record001_certificates 17) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 17)
    (.matching Nonrational.InducedTerminalMatches.M059.r1905) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 17) Nonrational.InducedTerminalMatches.M059.r1905
    Nonrational.InducedTerminalMatches.M059.r1905_checked (by decide +kernel)
theorem record001_leaf_checked_18 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 18)
      (record001_certificates 18) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 18)
    (.matching Nonrational.InducedTerminalMatches.M059.r1906) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 18) Nonrational.InducedTerminalMatches.M059.r1906
    Nonrational.InducedTerminalMatches.M059.r1906_checked (by decide +kernel)
theorem record001_leaf_checked_19 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 19)
      (record001_certificates 19) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 19)
    (.matching Nonrational.InducedTerminalMatches.M059.r1907) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 19) Nonrational.InducedTerminalMatches.M059.r1907
    Nonrational.InducedTerminalMatches.M059.r1907_checked (by decide +kernel)
theorem record001_leaf_checked_20 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 20)
      (record001_certificates 20) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 20)
    (.matching Nonrational.InducedTerminalMatches.M059.r1908) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 20) Nonrational.InducedTerminalMatches.M059.r1908
    Nonrational.InducedTerminalMatches.M059.r1908_checked (by decide +kernel)
theorem record001_leaf_checked_21 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 21)
      (record001_certificates 21) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 21)
    (.matching Nonrational.InducedTerminalMatches.M059.r1909) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 21) Nonrational.InducedTerminalMatches.M059.r1909
    Nonrational.InducedTerminalMatches.M059.r1909_checked (by decide +kernel)
theorem record001_leaf_checked_22 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 22)
      (record001_certificates 22) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 22)
    (.matching Nonrational.InducedTerminalMatches.M059.r1910) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 22) Nonrational.InducedTerminalMatches.M059.r1910
    Nonrational.InducedTerminalMatches.M059.r1910_checked (by decide +kernel)
theorem record001_leaf_checked_23 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 23)
      (record001_certificates 23) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 23)
    (.matching Nonrational.InducedTerminalMatches.M059.r1911) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 23) Nonrational.InducedTerminalMatches.M059.r1911
    Nonrational.InducedTerminalMatches.M059.r1911_checked (by decide +kernel)
theorem record001_leaf_checked_24 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 24)
      (record001_certificates 24) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 24)
    (.matching Nonrational.InducedTerminalMatches.M059.r1912) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 24) Nonrational.InducedTerminalMatches.M059.r1912
    Nonrational.InducedTerminalMatches.M059.r1912_checked (by decide +kernel)
theorem record001_leaf_checked_25 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 25)
      (record001_certificates 25) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 25)
    (.matching Nonrational.InducedTerminalMatches.M059.r1913) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 25) Nonrational.InducedTerminalMatches.M059.r1913
    Nonrational.InducedTerminalMatches.M059.r1913_checked (by decide +kernel)
theorem record001_leaf_checked_26 :
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves 26)
      (record001_certificates 26) = true := by
  change RawLeafCertificate.check record001.data.quota (record001_rawLeaves 26)
    (.matching Nonrational.InducedTerminalMatches.M059.r1914) = true
  exact matching_checked record001.data.quota (record001_rawLeaves 26) Nonrational.InducedTerminalMatches.M059.r1914
    Nonrational.InducedTerminalMatches.M059.r1914_checked (by decide +kernel)
theorem record001_leaf_certificates_checked : ∀ j : Fin record001.l,
    RawLeafCertificate.check record001.data.quota (record001_rawLeaves j)
      (record001_certificates j) = true :=
  (Fin.cases record001_leaf_checked_0 (Fin.cases record001_leaf_checked_1 (Fin.cases record001_leaf_checked_2 (Fin.cases record001_leaf_checked_3 (Fin.cases record001_leaf_checked_4 (Fin.cases record001_leaf_checked_5 (Fin.cases record001_leaf_checked_6 (Fin.cases record001_leaf_checked_7 (Fin.cases record001_leaf_checked_8 (Fin.cases record001_leaf_checked_9 (Fin.cases record001_leaf_checked_10 (Fin.cases record001_leaf_checked_11 (Fin.cases record001_leaf_checked_12 (Fin.cases record001_leaf_checked_13 (Fin.cases record001_leaf_checked_14 (Fin.cases record001_leaf_checked_15 (Fin.cases record001_leaf_checked_16 (Fin.cases record001_leaf_checked_17 (Fin.cases record001_leaf_checked_18 (Fin.cases record001_leaf_checked_19 (Fin.cases record001_leaf_checked_20 (Fin.cases record001_leaf_checked_21 (Fin.cases record001_leaf_checked_22 (Fin.cases record001_leaf_checked_23 (Fin.cases record001_leaf_checked_24 (Fin.cases record001_leaf_checked_25 (Fin.cases record001_leaf_checked_26 (fun j => Fin.elim0 j))))))))))))))))))))))))))))
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
(.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1915))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M059.r1916)))
noncomputable def record004_certificates (j : Fin record004.l) : Certificate :=
  record004_certificateTable.get j.val
theorem record004_leaf_checked_0 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 0)
      (record004_certificates 0) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M059.r1915) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 0) Nonrational.InducedTerminalMatches.M059.r1915
    Nonrational.InducedTerminalMatches.M059.r1915_checked (by decide +kernel)
theorem record004_leaf_checked_1 :
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves 1)
      (record004_certificates 1) = true := by
  change RawLeafCertificate.check record004.data.quota (record004_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M059.r1916) = true
  exact matching_checked record004.data.quota (record004_rawLeaves 1) Nonrational.InducedTerminalMatches.M059.r1916
    Nonrational.InducedTerminalMatches.M059.r1916_checked (by decide +kernel)
theorem record004_leaf_certificates_checked : ∀ j : Fin record004.l,
    RawLeafCertificate.check record004.data.quota (record004_rawLeaves j)
      (record004_certificates j) = true :=
  (Fin.cases record004_leaf_checked_0 (Fin.cases record004_leaf_checked_1 (fun j => Fin.elim0 j)))
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
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00142
