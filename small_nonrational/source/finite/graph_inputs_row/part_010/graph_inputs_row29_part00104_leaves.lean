module
prelude
public import GraphInputsRow29Part00104Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M054
public import InducedTerminalMatches.M055

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104
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
(.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M054.r1738))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M054.r1739))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M054.r1740))))
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M054.r1741))
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M054.r1742))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M054.r1743)))))
 (.branch 9
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M054.r1744))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M054.r1745))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M054.r1746))))
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M054.r1747))
 (.branch 11
 (.leaf (.matching Nonrational.InducedTerminalMatches.M054.r1748))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M054.r1749))))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf (.matching Nonrational.InducedTerminalMatches.M054.r1750))
 (.branch 14
 (.leaf (.matching Nonrational.InducedTerminalMatches.M054.r1751))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M054.r1752))))
 (.branch 16
 (.leaf (.matching Nonrational.InducedTerminalMatches.M054.r1753))
 (.branch 17
 (.leaf (.matching Nonrational.InducedTerminalMatches.M054.r1754))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M054.r1755)))))
 (.branch 21
 (.branch 19
 (.leaf (.matching Nonrational.InducedTerminalMatches.M054.r1756))
 (.branch 20
 (.leaf (.matching Nonrational.InducedTerminalMatches.M054.r1757))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M054.r1758))))
 (.branch 23
 (.branch 22
 (.leaf (.matching Nonrational.InducedTerminalMatches.M054.r1759))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M055.r1760)))
 (.branch 24
 (.leaf (.matching Nonrational.InducedTerminalMatches.M055.r1761))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M055.r1762)))))))
 (.branch 38
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf (.matching Nonrational.InducedTerminalMatches.M055.r1763))
 (.branch 27
 (.leaf (.matching Nonrational.InducedTerminalMatches.M055.r1764))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M055.r1765))))
 (.branch 29
 (.leaf (.matching Nonrational.InducedTerminalMatches.M055.r1766))
 (.branch 30
 (.leaf (.matching Nonrational.InducedTerminalMatches.M055.r1767))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M055.r1768)))))
 (.branch 34
 (.branch 32
 (.leaf (.matching Nonrational.InducedTerminalMatches.M055.r1769))
 (.branch 33
 (.leaf (.matching Nonrational.InducedTerminalMatches.M055.r1770))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M055.r1771))))
 (.branch 36
 (.branch 35
 (.leaf (.matching Nonrational.InducedTerminalMatches.M055.r1772))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M055.r1773)))
 (.branch 37
 (.leaf (.matching Nonrational.InducedTerminalMatches.M055.r1774))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M055.r1775))))))
 (.branch 44
 (.branch 41
 (.branch 39
 (.leaf (.matching Nonrational.InducedTerminalMatches.M055.r1776))
 (.branch 40
 (.leaf (.matching Nonrational.InducedTerminalMatches.M055.r1777))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M055.r1778))))
 (.branch 42
 (.leaf (.matching Nonrational.InducedTerminalMatches.M055.r1779))
 (.branch 43
 (.leaf (.matching Nonrational.InducedTerminalMatches.M055.r1780))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M055.r1781)))))
 (.branch 47
 (.branch 45
 (.leaf (.matching Nonrational.InducedTerminalMatches.M055.r1782))
 (.branch 46
 (.leaf (.matching Nonrational.InducedTerminalMatches.M055.r1783))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M055.r1784))))
 (.branch 49
 (.branch 48
 (.leaf (.matching Nonrational.InducedTerminalMatches.M055.r1785))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M055.r1786)))
 (.branch 50
 (.leaf (.matching Nonrational.InducedTerminalMatches.M055.r1787))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M055.r1788))))))))
noncomputable def record007_certificates (j : Fin record007.l) : Certificate :=
  record007_certificateTable.get j.val
theorem record007_leaf_checked_0 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 0)
      (record007_certificates 0) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M054.r1738) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 0) Nonrational.InducedTerminalMatches.M054.r1738
    Nonrational.InducedTerminalMatches.M054.r1738_checked (by decide +kernel)
theorem record007_leaf_checked_1 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 1)
      (record007_certificates 1) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M054.r1739) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 1) Nonrational.InducedTerminalMatches.M054.r1739
    Nonrational.InducedTerminalMatches.M054.r1739_checked (by decide +kernel)
theorem record007_leaf_checked_2 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 2)
      (record007_certificates 2) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M054.r1740) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 2) Nonrational.InducedTerminalMatches.M054.r1740
    Nonrational.InducedTerminalMatches.M054.r1740_checked (by decide +kernel)
theorem record007_leaf_checked_3 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 3)
      (record007_certificates 3) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M054.r1741) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 3) Nonrational.InducedTerminalMatches.M054.r1741
    Nonrational.InducedTerminalMatches.M054.r1741_checked (by decide +kernel)
theorem record007_leaf_checked_4 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 4)
      (record007_certificates 4) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M054.r1742) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 4) Nonrational.InducedTerminalMatches.M054.r1742
    Nonrational.InducedTerminalMatches.M054.r1742_checked (by decide +kernel)
theorem record007_leaf_checked_5 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 5)
      (record007_certificates 5) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 5)
    (.matching Nonrational.InducedTerminalMatches.M054.r1743) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 5) Nonrational.InducedTerminalMatches.M054.r1743
    Nonrational.InducedTerminalMatches.M054.r1743_checked (by decide +kernel)
theorem record007_leaf_checked_6 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 6)
      (record007_certificates 6) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 6)
    (.matching Nonrational.InducedTerminalMatches.M054.r1744) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 6) Nonrational.InducedTerminalMatches.M054.r1744
    Nonrational.InducedTerminalMatches.M054.r1744_checked (by decide +kernel)
theorem record007_leaf_checked_7 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 7)
      (record007_certificates 7) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 7)
    (.matching Nonrational.InducedTerminalMatches.M054.r1745) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 7) Nonrational.InducedTerminalMatches.M054.r1745
    Nonrational.InducedTerminalMatches.M054.r1745_checked (by decide +kernel)
theorem record007_leaf_checked_8 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 8)
      (record007_certificates 8) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 8)
    (.matching Nonrational.InducedTerminalMatches.M054.r1746) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 8) Nonrational.InducedTerminalMatches.M054.r1746
    Nonrational.InducedTerminalMatches.M054.r1746_checked (by decide +kernel)
theorem record007_leaf_checked_9 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 9)
      (record007_certificates 9) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 9)
    (.matching Nonrational.InducedTerminalMatches.M054.r1747) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 9) Nonrational.InducedTerminalMatches.M054.r1747
    Nonrational.InducedTerminalMatches.M054.r1747_checked (by decide +kernel)
theorem record007_leaf_checked_10 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 10)
      (record007_certificates 10) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 10)
    (.matching Nonrational.InducedTerminalMatches.M054.r1748) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 10) Nonrational.InducedTerminalMatches.M054.r1748
    Nonrational.InducedTerminalMatches.M054.r1748_checked (by decide +kernel)
theorem record007_leaf_checked_11 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 11)
      (record007_certificates 11) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 11)
    (.matching Nonrational.InducedTerminalMatches.M054.r1749) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 11) Nonrational.InducedTerminalMatches.M054.r1749
    Nonrational.InducedTerminalMatches.M054.r1749_checked (by decide +kernel)
theorem record007_leaf_checked_12 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 12)
      (record007_certificates 12) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 12)
    (.matching Nonrational.InducedTerminalMatches.M054.r1750) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 12) Nonrational.InducedTerminalMatches.M054.r1750
    Nonrational.InducedTerminalMatches.M054.r1750_checked (by decide +kernel)
theorem record007_leaf_checked_13 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 13)
      (record007_certificates 13) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 13)
    (.matching Nonrational.InducedTerminalMatches.M054.r1751) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 13) Nonrational.InducedTerminalMatches.M054.r1751
    Nonrational.InducedTerminalMatches.M054.r1751_checked (by decide +kernel)
theorem record007_leaf_checked_14 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 14)
      (record007_certificates 14) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 14)
    (.matching Nonrational.InducedTerminalMatches.M054.r1752) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 14) Nonrational.InducedTerminalMatches.M054.r1752
    Nonrational.InducedTerminalMatches.M054.r1752_checked (by decide +kernel)
theorem record007_leaf_checked_15 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 15)
      (record007_certificates 15) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 15)
    (.matching Nonrational.InducedTerminalMatches.M054.r1753) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 15) Nonrational.InducedTerminalMatches.M054.r1753
    Nonrational.InducedTerminalMatches.M054.r1753_checked (by decide +kernel)
theorem record007_leaf_checked_16 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 16)
      (record007_certificates 16) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 16)
    (.matching Nonrational.InducedTerminalMatches.M054.r1754) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 16) Nonrational.InducedTerminalMatches.M054.r1754
    Nonrational.InducedTerminalMatches.M054.r1754_checked (by decide +kernel)
theorem record007_leaf_checked_17 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 17)
      (record007_certificates 17) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 17)
    (.matching Nonrational.InducedTerminalMatches.M054.r1755) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 17) Nonrational.InducedTerminalMatches.M054.r1755
    Nonrational.InducedTerminalMatches.M054.r1755_checked (by decide +kernel)
theorem record007_leaf_checked_18 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 18)
      (record007_certificates 18) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 18)
    (.matching Nonrational.InducedTerminalMatches.M054.r1756) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 18) Nonrational.InducedTerminalMatches.M054.r1756
    Nonrational.InducedTerminalMatches.M054.r1756_checked (by decide +kernel)
theorem record007_leaf_checked_19 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 19)
      (record007_certificates 19) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 19)
    (.matching Nonrational.InducedTerminalMatches.M054.r1757) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 19) Nonrational.InducedTerminalMatches.M054.r1757
    Nonrational.InducedTerminalMatches.M054.r1757_checked (by decide +kernel)
theorem record007_leaf_checked_20 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 20)
      (record007_certificates 20) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 20)
    (.matching Nonrational.InducedTerminalMatches.M054.r1758) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 20) Nonrational.InducedTerminalMatches.M054.r1758
    Nonrational.InducedTerminalMatches.M054.r1758_checked (by decide +kernel)
theorem record007_leaf_checked_21 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 21)
      (record007_certificates 21) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 21)
    (.matching Nonrational.InducedTerminalMatches.M054.r1759) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 21) Nonrational.InducedTerminalMatches.M054.r1759
    Nonrational.InducedTerminalMatches.M054.r1759_checked (by decide +kernel)
theorem record007_leaf_checked_22 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 22)
      (record007_certificates 22) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 22)
    (.matching Nonrational.InducedTerminalMatches.M055.r1760) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 22) Nonrational.InducedTerminalMatches.M055.r1760
    Nonrational.InducedTerminalMatches.M055.r1760_checked (by decide +kernel)
theorem record007_leaf_checked_23 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 23)
      (record007_certificates 23) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 23)
    (.matching Nonrational.InducedTerminalMatches.M055.r1761) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 23) Nonrational.InducedTerminalMatches.M055.r1761
    Nonrational.InducedTerminalMatches.M055.r1761_checked (by decide +kernel)
theorem record007_leaf_checked_24 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 24)
      (record007_certificates 24) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 24)
    (.matching Nonrational.InducedTerminalMatches.M055.r1762) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 24) Nonrational.InducedTerminalMatches.M055.r1762
    Nonrational.InducedTerminalMatches.M055.r1762_checked (by decide +kernel)
theorem record007_leaf_checked_25 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 25)
      (record007_certificates 25) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 25)
    (.matching Nonrational.InducedTerminalMatches.M055.r1763) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 25) Nonrational.InducedTerminalMatches.M055.r1763
    Nonrational.InducedTerminalMatches.M055.r1763_checked (by decide +kernel)
theorem record007_leaf_checked_26 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 26)
      (record007_certificates 26) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 26)
    (.matching Nonrational.InducedTerminalMatches.M055.r1764) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 26) Nonrational.InducedTerminalMatches.M055.r1764
    Nonrational.InducedTerminalMatches.M055.r1764_checked (by decide +kernel)
theorem record007_leaf_checked_27 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 27)
      (record007_certificates 27) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 27)
    (.matching Nonrational.InducedTerminalMatches.M055.r1765) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 27) Nonrational.InducedTerminalMatches.M055.r1765
    Nonrational.InducedTerminalMatches.M055.r1765_checked (by decide +kernel)
theorem record007_leaf_checked_28 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 28)
      (record007_certificates 28) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 28)
    (.matching Nonrational.InducedTerminalMatches.M055.r1766) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 28) Nonrational.InducedTerminalMatches.M055.r1766
    Nonrational.InducedTerminalMatches.M055.r1766_checked (by decide +kernel)
theorem record007_leaf_checked_29 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 29)
      (record007_certificates 29) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 29)
    (.matching Nonrational.InducedTerminalMatches.M055.r1767) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 29) Nonrational.InducedTerminalMatches.M055.r1767
    Nonrational.InducedTerminalMatches.M055.r1767_checked (by decide +kernel)
theorem record007_leaf_checked_30 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 30)
      (record007_certificates 30) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 30)
    (.matching Nonrational.InducedTerminalMatches.M055.r1768) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 30) Nonrational.InducedTerminalMatches.M055.r1768
    Nonrational.InducedTerminalMatches.M055.r1768_checked (by decide +kernel)
theorem record007_leaf_checked_31 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 31)
      (record007_certificates 31) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 31)
    (.matching Nonrational.InducedTerminalMatches.M055.r1769) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 31) Nonrational.InducedTerminalMatches.M055.r1769
    Nonrational.InducedTerminalMatches.M055.r1769_checked (by decide +kernel)
theorem record007_leaf_checked_32 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 32)
      (record007_certificates 32) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 32)
    (.matching Nonrational.InducedTerminalMatches.M055.r1770) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 32) Nonrational.InducedTerminalMatches.M055.r1770
    Nonrational.InducedTerminalMatches.M055.r1770_checked (by decide +kernel)
theorem record007_leaf_checked_33 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 33)
      (record007_certificates 33) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 33)
    (.matching Nonrational.InducedTerminalMatches.M055.r1771) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 33) Nonrational.InducedTerminalMatches.M055.r1771
    Nonrational.InducedTerminalMatches.M055.r1771_checked (by decide +kernel)
theorem record007_leaf_checked_34 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 34)
      (record007_certificates 34) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 34)
    (.matching Nonrational.InducedTerminalMatches.M055.r1772) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 34) Nonrational.InducedTerminalMatches.M055.r1772
    Nonrational.InducedTerminalMatches.M055.r1772_checked (by decide +kernel)
theorem record007_leaf_checked_35 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 35)
      (record007_certificates 35) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 35)
    (.matching Nonrational.InducedTerminalMatches.M055.r1773) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 35) Nonrational.InducedTerminalMatches.M055.r1773
    Nonrational.InducedTerminalMatches.M055.r1773_checked (by decide +kernel)
theorem record007_leaf_checked_36 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 36)
      (record007_certificates 36) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 36)
    (.matching Nonrational.InducedTerminalMatches.M055.r1774) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 36) Nonrational.InducedTerminalMatches.M055.r1774
    Nonrational.InducedTerminalMatches.M055.r1774_checked (by decide +kernel)
theorem record007_leaf_checked_37 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 37)
      (record007_certificates 37) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 37)
    (.matching Nonrational.InducedTerminalMatches.M055.r1775) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 37) Nonrational.InducedTerminalMatches.M055.r1775
    Nonrational.InducedTerminalMatches.M055.r1775_checked (by decide +kernel)
theorem record007_leaf_checked_38 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 38)
      (record007_certificates 38) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 38)
    (.matching Nonrational.InducedTerminalMatches.M055.r1776) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 38) Nonrational.InducedTerminalMatches.M055.r1776
    Nonrational.InducedTerminalMatches.M055.r1776_checked (by decide +kernel)
theorem record007_leaf_checked_39 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 39)
      (record007_certificates 39) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 39)
    (.matching Nonrational.InducedTerminalMatches.M055.r1777) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 39) Nonrational.InducedTerminalMatches.M055.r1777
    Nonrational.InducedTerminalMatches.M055.r1777_checked (by decide +kernel)
theorem record007_leaf_checked_40 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 40)
      (record007_certificates 40) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 40)
    (.matching Nonrational.InducedTerminalMatches.M055.r1778) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 40) Nonrational.InducedTerminalMatches.M055.r1778
    Nonrational.InducedTerminalMatches.M055.r1778_checked (by decide +kernel)
theorem record007_leaf_checked_41 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 41)
      (record007_certificates 41) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 41)
    (.matching Nonrational.InducedTerminalMatches.M055.r1779) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 41) Nonrational.InducedTerminalMatches.M055.r1779
    Nonrational.InducedTerminalMatches.M055.r1779_checked (by decide +kernel)
theorem record007_leaf_checked_42 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 42)
      (record007_certificates 42) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 42)
    (.matching Nonrational.InducedTerminalMatches.M055.r1780) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 42) Nonrational.InducedTerminalMatches.M055.r1780
    Nonrational.InducedTerminalMatches.M055.r1780_checked (by decide +kernel)
theorem record007_leaf_checked_43 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 43)
      (record007_certificates 43) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 43)
    (.matching Nonrational.InducedTerminalMatches.M055.r1781) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 43) Nonrational.InducedTerminalMatches.M055.r1781
    Nonrational.InducedTerminalMatches.M055.r1781_checked (by decide +kernel)
theorem record007_leaf_checked_44 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 44)
      (record007_certificates 44) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 44)
    (.matching Nonrational.InducedTerminalMatches.M055.r1782) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 44) Nonrational.InducedTerminalMatches.M055.r1782
    Nonrational.InducedTerminalMatches.M055.r1782_checked (by decide +kernel)
theorem record007_leaf_checked_45 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 45)
      (record007_certificates 45) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 45)
    (.matching Nonrational.InducedTerminalMatches.M055.r1783) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 45) Nonrational.InducedTerminalMatches.M055.r1783
    Nonrational.InducedTerminalMatches.M055.r1783_checked (by decide +kernel)
theorem record007_leaf_checked_46 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 46)
      (record007_certificates 46) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 46)
    (.matching Nonrational.InducedTerminalMatches.M055.r1784) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 46) Nonrational.InducedTerminalMatches.M055.r1784
    Nonrational.InducedTerminalMatches.M055.r1784_checked (by decide +kernel)
theorem record007_leaf_checked_47 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 47)
      (record007_certificates 47) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 47)
    (.matching Nonrational.InducedTerminalMatches.M055.r1785) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 47) Nonrational.InducedTerminalMatches.M055.r1785
    Nonrational.InducedTerminalMatches.M055.r1785_checked (by decide +kernel)
theorem record007_leaf_checked_48 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 48)
      (record007_certificates 48) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 48)
    (.matching Nonrational.InducedTerminalMatches.M055.r1786) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 48) Nonrational.InducedTerminalMatches.M055.r1786
    Nonrational.InducedTerminalMatches.M055.r1786_checked (by decide +kernel)
theorem record007_leaf_checked_49 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 49)
      (record007_certificates 49) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 49)
    (.matching Nonrational.InducedTerminalMatches.M055.r1787) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 49) Nonrational.InducedTerminalMatches.M055.r1787
    Nonrational.InducedTerminalMatches.M055.r1787_checked (by decide +kernel)
theorem record007_leaf_checked_50 :
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves 50)
      (record007_certificates 50) = true := by
  change RawLeafCertificate.check record007.data.quota (record007_rawLeaves 50)
    (.matching Nonrational.InducedTerminalMatches.M055.r1788) = true
  exact matching_checked record007.data.quota (record007_rawLeaves 50) Nonrational.InducedTerminalMatches.M055.r1788
    Nonrational.InducedTerminalMatches.M055.r1788_checked (by decide +kernel)
theorem record007_leaf_certificates_checked : ∀ j : Fin record007.l,
    RawLeafCertificate.check record007.data.quota (record007_rawLeaves j)
      (record007_certificates j) = true :=
  (Fin.cases record007_leaf_checked_0 (Fin.cases record007_leaf_checked_1 (Fin.cases record007_leaf_checked_2 (Fin.cases record007_leaf_checked_3 (Fin.cases record007_leaf_checked_4 (Fin.cases record007_leaf_checked_5 (Fin.cases record007_leaf_checked_6 (Fin.cases record007_leaf_checked_7 (Fin.cases record007_leaf_checked_8 (Fin.cases record007_leaf_checked_9 (Fin.cases record007_leaf_checked_10 (Fin.cases record007_leaf_checked_11 (Fin.cases record007_leaf_checked_12 (Fin.cases record007_leaf_checked_13 (Fin.cases record007_leaf_checked_14 (Fin.cases record007_leaf_checked_15 (Fin.cases record007_leaf_checked_16 (Fin.cases record007_leaf_checked_17 (Fin.cases record007_leaf_checked_18 (Fin.cases record007_leaf_checked_19 (Fin.cases record007_leaf_checked_20 (Fin.cases record007_leaf_checked_21 (Fin.cases record007_leaf_checked_22 (Fin.cases record007_leaf_checked_23 (Fin.cases record007_leaf_checked_24 (Fin.cases record007_leaf_checked_25 (Fin.cases record007_leaf_checked_26 (Fin.cases record007_leaf_checked_27 (Fin.cases record007_leaf_checked_28 (Fin.cases record007_leaf_checked_29 (Fin.cases record007_leaf_checked_30 (Fin.cases record007_leaf_checked_31 (Fin.cases record007_leaf_checked_32 (Fin.cases record007_leaf_checked_33 (Fin.cases record007_leaf_checked_34 (Fin.cases record007_leaf_checked_35 (Fin.cases record007_leaf_checked_36 (Fin.cases record007_leaf_checked_37 (Fin.cases record007_leaf_checked_38 (Fin.cases record007_leaf_checked_39 (Fin.cases record007_leaf_checked_40 (Fin.cases record007_leaf_checked_41 (Fin.cases record007_leaf_checked_42 (Fin.cases record007_leaf_checked_43 (Fin.cases record007_leaf_checked_44 (Fin.cases record007_leaf_checked_45 (Fin.cases record007_leaf_checked_46 (Fin.cases record007_leaf_checked_47 (Fin.cases record007_leaf_checked_48 (Fin.cases record007_leaf_checked_49 (Fin.cases record007_leaf_checked_50 (fun j => Fin.elim0 j))))))))))))))))))))))))))))))))))))))))))))))))))))
#print axioms record007_leaf_certificates_checked
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104
