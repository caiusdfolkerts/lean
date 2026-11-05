module
prelude
public import GraphInputsRow16Part00029Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M000
public import InducedTerminalMatches.M001

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029
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
(.leaf (.quota 1))
noncomputable def record012_certificates (j : Fin record012.l) : Certificate :=
  record012_certificateTable.get j.val
theorem record012_leaf_checked_0 :
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves 0)
      (record012_certificates 0) = true := by
  change RawLeafCertificate.check record012.data.quota [] (.quota 1) = true
  exact empty_checked record012.data.quota 1 (by decide +kernel)
theorem record012_leaf_certificates_checked : ∀ j : Fin record012.l,
    RawLeafCertificate.check record012.data.quota (record012_rawLeaves j)
      (record012_certificates j) = true :=
  (Fin.cases record012_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record012_leaf_certificates_checked

noncomputable def record013_rawLeaves (j : Fin record013.l) : List Cell :=
  (record013.leaf j).map record013.data.cells
theorem record013_raw_exact (j : Fin record013.l) :
    (record013.leaf j).map record013.data.cells = record013_rawLeaves j := rfl
noncomputable def record013_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record013_certificates (j : Fin record013.l) : Certificate :=
  record013_certificateTable.get j.val
theorem record013_leaf_checked_0 :
    RawLeafCertificate.check record013.data.quota (record013_rawLeaves 0)
      (record013_certificates 0) = true := by
  change RawLeafCertificate.check record013.data.quota [] (.quota 1) = true
  exact empty_checked record013.data.quota 1 (by decide +kernel)
theorem record013_leaf_certificates_checked : ∀ j : Fin record013.l,
    RawLeafCertificate.check record013.data.quota (record013_rawLeaves j)
      (record013_certificates j) = true :=
  (Fin.cases record013_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record013_leaf_certificates_checked

noncomputable def record014_rawLeaves (j : Fin record014.l) : List Cell :=
  (record014.leaf j).map record014.data.cells
theorem record014_raw_exact (j : Fin record014.l) :
    (record014.leaf j).map record014.data.cells = record014_rawLeaves j := rfl
noncomputable def record014_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record014_certificates (j : Fin record014.l) : Certificate :=
  record014_certificateTable.get j.val
theorem record014_leaf_checked_0 :
    RawLeafCertificate.check record014.data.quota (record014_rawLeaves 0)
      (record014_certificates 0) = true := by
  change RawLeafCertificate.check record014.data.quota [] (.quota 1) = true
  exact empty_checked record014.data.quota 1 (by decide +kernel)
theorem record014_leaf_certificates_checked : ∀ j : Fin record014.l,
    RawLeafCertificate.check record014.data.quota (record014_rawLeaves j)
      (record014_certificates j) = true :=
  (Fin.cases record014_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record014_leaf_certificates_checked

noncomputable def record015_rawLeaves (j : Fin record015.l) : List Cell :=
  (record015.leaf j).map record015.data.cells
theorem record015_raw_exact (j : Fin record015.l) :
    (record015.leaf j).map record015.data.cells = record015_rawLeaves j := rfl
noncomputable def record015_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record015_certificates (j : Fin record015.l) : Certificate :=
  record015_certificateTable.get j.val
theorem record015_leaf_checked_0 :
    RawLeafCertificate.check record015.data.quota (record015_rawLeaves 0)
      (record015_certificates 0) = true := by
  change RawLeafCertificate.check record015.data.quota [] (.quota 1) = true
  exact empty_checked record015.data.quota 1 (by decide +kernel)
theorem record015_leaf_certificates_checked : ∀ j : Fin record015.l,
    RawLeafCertificate.check record015.data.quota (record015_rawLeaves j)
      (record015_certificates j) = true :=
  (Fin.cases record015_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record015_leaf_certificates_checked

noncomputable def record016_rawLeaves (j : Fin record016.l) : List Cell :=
  (record016.leaf j).map record016.data.cells
theorem record016_raw_exact (j : Fin record016.l) :
    (record016.leaf j).map record016.data.cells = record016_rawLeaves j := rfl
noncomputable def record016_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record016_certificates (j : Fin record016.l) : Certificate :=
  record016_certificateTable.get j.val
theorem record016_leaf_checked_0 :
    RawLeafCertificate.check record016.data.quota (record016_rawLeaves 0)
      (record016_certificates 0) = true := by
  change RawLeafCertificate.check record016.data.quota [] (.quota 1) = true
  exact empty_checked record016.data.quota 1 (by decide +kernel)
theorem record016_leaf_certificates_checked : ∀ j : Fin record016.l,
    RawLeafCertificate.check record016.data.quota (record016_rawLeaves j)
      (record016_certificates j) = true :=
  (Fin.cases record016_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record016_leaf_certificates_checked

noncomputable def record017_rawLeaves (j : Fin record017.l) : List Cell :=
  (record017.leaf j).map record017.data.cells
theorem record017_raw_exact (j : Fin record017.l) :
    (record017.leaf j).map record017.data.cells = record017_rawLeaves j := rfl
noncomputable def record017_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record017_certificates (j : Fin record017.l) : Certificate :=
  record017_certificateTable.get j.val
theorem record017_leaf_checked_0 :
    RawLeafCertificate.check record017.data.quota (record017_rawLeaves 0)
      (record017_certificates 0) = true := by
  change RawLeafCertificate.check record017.data.quota [] (.quota 1) = true
  exact empty_checked record017.data.quota 1 (by decide +kernel)
theorem record017_leaf_certificates_checked : ∀ j : Fin record017.l,
    RawLeafCertificate.check record017.data.quota (record017_rawLeaves j)
      (record017_certificates j) = true :=
  (Fin.cases record017_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record017_leaf_certificates_checked

noncomputable def record018_rawLeaves (j : Fin record018.l) : List Cell :=
  (record018.leaf j).map record018.data.cells
theorem record018_raw_exact (j : Fin record018.l) :
    (record018.leaf j).map record018.data.cells = record018_rawLeaves j := rfl
noncomputable def record018_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record018_certificates (j : Fin record018.l) : Certificate :=
  record018_certificateTable.get j.val
theorem record018_leaf_checked_0 :
    RawLeafCertificate.check record018.data.quota (record018_rawLeaves 0)
      (record018_certificates 0) = true := by
  change RawLeafCertificate.check record018.data.quota [] (.quota 1) = true
  exact empty_checked record018.data.quota 1 (by decide +kernel)
theorem record018_leaf_certificates_checked : ∀ j : Fin record018.l,
    RawLeafCertificate.check record018.data.quota (record018_rawLeaves j)
      (record018_certificates j) = true :=
  (Fin.cases record018_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record018_leaf_certificates_checked

noncomputable def record019_rawLeaves (j : Fin record019.l) : List Cell :=
  (record019.leaf j).map record019.data.cells
theorem record019_raw_exact (j : Fin record019.l) :
    (record019.leaf j).map record019.data.cells = record019_rawLeaves j := rfl
noncomputable def record019_certificateTable : Table Certificate :=
(.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M000.r0016))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M000.r0017)))
noncomputable def record019_certificates (j : Fin record019.l) : Certificate :=
  record019_certificateTable.get j.val
theorem record019_leaf_checked_0 :
    RawLeafCertificate.check record019.data.quota (record019_rawLeaves 0)
      (record019_certificates 0) = true := by
  change RawLeafCertificate.check record019.data.quota (record019_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M000.r0016) = true
  exact matching_checked record019.data.quota (record019_rawLeaves 0) Nonrational.InducedTerminalMatches.M000.r0016
    Nonrational.InducedTerminalMatches.M000.r0016_checked (by decide +kernel)
theorem record019_leaf_checked_1 :
    RawLeafCertificate.check record019.data.quota (record019_rawLeaves 1)
      (record019_certificates 1) = true := by
  change RawLeafCertificate.check record019.data.quota (record019_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M000.r0017) = true
  exact matching_checked record019.data.quota (record019_rawLeaves 1) Nonrational.InducedTerminalMatches.M000.r0017
    Nonrational.InducedTerminalMatches.M000.r0017_checked (by decide +kernel)
theorem record019_leaf_certificates_checked : ∀ j : Fin record019.l,
    RawLeafCertificate.check record019.data.quota (record019_rawLeaves j)
      (record019_certificates j) = true :=
  (Fin.cases record019_leaf_checked_0 (Fin.cases record019_leaf_checked_1 (fun j => Fin.elim0 j)))
#print axioms record019_leaf_certificates_checked

noncomputable def record020_rawLeaves (j : Fin record020.l) : List Cell :=
  (record020.leaf j).map record020.data.cells
theorem record020_raw_exact (j : Fin record020.l) :
    (record020.leaf j).map record020.data.cells = record020_rawLeaves j := rfl
noncomputable def record020_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record020_certificates (j : Fin record020.l) : Certificate :=
  record020_certificateTable.get j.val
theorem record020_leaf_checked_0 :
    RawLeafCertificate.check record020.data.quota (record020_rawLeaves 0)
      (record020_certificates 0) = true := by
  change RawLeafCertificate.check record020.data.quota [] (.quota 1) = true
  exact empty_checked record020.data.quota 1 (by decide +kernel)
theorem record020_leaf_certificates_checked : ∀ j : Fin record020.l,
    RawLeafCertificate.check record020.data.quota (record020_rawLeaves j)
      (record020_certificates j) = true :=
  (Fin.cases record020_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record020_leaf_certificates_checked

noncomputable def record021_rawLeaves (j : Fin record021.l) : List Cell :=
  (record021.leaf j).map record021.data.cells
theorem record021_raw_exact (j : Fin record021.l) :
    (record021.leaf j).map record021.data.cells = record021_rawLeaves j := rfl
noncomputable def record021_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record021_certificates (j : Fin record021.l) : Certificate :=
  record021_certificateTable.get j.val
theorem record021_leaf_checked_0 :
    RawLeafCertificate.check record021.data.quota (record021_rawLeaves 0)
      (record021_certificates 0) = true := by
  change RawLeafCertificate.check record021.data.quota [] (.quota 1) = true
  exact empty_checked record021.data.quota 1 (by decide +kernel)
theorem record021_leaf_certificates_checked : ∀ j : Fin record021.l,
    RawLeafCertificate.check record021.data.quota (record021_rawLeaves j)
      (record021_certificates j) = true :=
  (Fin.cases record021_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record021_leaf_certificates_checked

noncomputable def record022_rawLeaves (j : Fin record022.l) : List Cell :=
  (record022.leaf j).map record022.data.cells
theorem record022_raw_exact (j : Fin record022.l) :
    (record022.leaf j).map record022.data.cells = record022_rawLeaves j := rfl
noncomputable def record022_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record022_certificates (j : Fin record022.l) : Certificate :=
  record022_certificateTable.get j.val
theorem record022_leaf_checked_0 :
    RawLeafCertificate.check record022.data.quota (record022_rawLeaves 0)
      (record022_certificates 0) = true := by
  change RawLeafCertificate.check record022.data.quota [] (.quota 1) = true
  exact empty_checked record022.data.quota 1 (by decide +kernel)
theorem record022_leaf_certificates_checked : ∀ j : Fin record022.l,
    RawLeafCertificate.check record022.data.quota (record022_rawLeaves j)
      (record022_certificates j) = true :=
  (Fin.cases record022_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record022_leaf_certificates_checked

noncomputable def record023_rawLeaves (j : Fin record023.l) : List Cell :=
  (record023.leaf j).map record023.data.cells
theorem record023_raw_exact (j : Fin record023.l) :
    (record023.leaf j).map record023.data.cells = record023_rawLeaves j := rfl
noncomputable def record023_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record023_certificates (j : Fin record023.l) : Certificate :=
  record023_certificateTable.get j.val
theorem record023_leaf_checked_0 :
    RawLeafCertificate.check record023.data.quota (record023_rawLeaves 0)
      (record023_certificates 0) = true := by
  change RawLeafCertificate.check record023.data.quota [] (.quota 1) = true
  exact empty_checked record023.data.quota 1 (by decide +kernel)
theorem record023_leaf_certificates_checked : ∀ j : Fin record023.l,
    RawLeafCertificate.check record023.data.quota (record023_rawLeaves j)
      (record023_certificates j) = true :=
  (Fin.cases record023_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record023_leaf_certificates_checked

noncomputable def record024_rawLeaves (j : Fin record024.l) : List Cell :=
  (record024.leaf j).map record024.data.cells
theorem record024_raw_exact (j : Fin record024.l) :
    (record024.leaf j).map record024.data.cells = record024_rawLeaves j := rfl
noncomputable def record024_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record024_certificates (j : Fin record024.l) : Certificate :=
  record024_certificateTable.get j.val
theorem record024_leaf_checked_0 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 0)
      (record024_certificates 0) = true := by
  change RawLeafCertificate.check record024.data.quota [] (.quota 1) = true
  exact empty_checked record024.data.quota 1 (by decide +kernel)
theorem record024_leaf_certificates_checked : ∀ j : Fin record024.l,
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves j)
      (record024_certificates j) = true :=
  (Fin.cases record024_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record024_leaf_certificates_checked

noncomputable def record025_rawLeaves (j : Fin record025.l) : List Cell :=
  (record025.leaf j).map record025.data.cells
theorem record025_raw_exact (j : Fin record025.l) :
    (record025.leaf j).map record025.data.cells = record025_rawLeaves j := rfl
noncomputable def record025_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record025_certificates (j : Fin record025.l) : Certificate :=
  record025_certificateTable.get j.val
theorem record025_leaf_checked_0 :
    RawLeafCertificate.check record025.data.quota (record025_rawLeaves 0)
      (record025_certificates 0) = true := by
  change RawLeafCertificate.check record025.data.quota [] (.quota 1) = true
  exact empty_checked record025.data.quota 1 (by decide +kernel)
theorem record025_leaf_certificates_checked : ∀ j : Fin record025.l,
    RawLeafCertificate.check record025.data.quota (record025_rawLeaves j)
      (record025_certificates j) = true :=
  (Fin.cases record025_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record025_leaf_certificates_checked

noncomputable def record026_rawLeaves (j : Fin record026.l) : List Cell :=
  (record026.leaf j).map record026.data.cells
theorem record026_raw_exact (j : Fin record026.l) :
    (record026.leaf j).map record026.data.cells = record026_rawLeaves j := rfl
noncomputable def record026_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record026_certificates (j : Fin record026.l) : Certificate :=
  record026_certificateTable.get j.val
theorem record026_leaf_checked_0 :
    RawLeafCertificate.check record026.data.quota (record026_rawLeaves 0)
      (record026_certificates 0) = true := by
  change RawLeafCertificate.check record026.data.quota [] (.quota 1) = true
  exact empty_checked record026.data.quota 1 (by decide +kernel)
theorem record026_leaf_certificates_checked : ∀ j : Fin record026.l,
    RawLeafCertificate.check record026.data.quota (record026_rawLeaves j)
      (record026_certificates j) = true :=
  (Fin.cases record026_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record026_leaf_certificates_checked

noncomputable def record027_rawLeaves (j : Fin record027.l) : List Cell :=
  (record027.leaf j).map record027.data.cells
theorem record027_raw_exact (j : Fin record027.l) :
    (record027.leaf j).map record027.data.cells = record027_rawLeaves j := rfl
noncomputable def record027_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record027_certificates (j : Fin record027.l) : Certificate :=
  record027_certificateTable.get j.val
theorem record027_leaf_checked_0 :
    RawLeafCertificate.check record027.data.quota (record027_rawLeaves 0)
      (record027_certificates 0) = true := by
  change RawLeafCertificate.check record027.data.quota [] (.quota 1) = true
  exact empty_checked record027.data.quota 1 (by decide +kernel)
theorem record027_leaf_certificates_checked : ∀ j : Fin record027.l,
    RawLeafCertificate.check record027.data.quota (record027_rawLeaves j)
      (record027_certificates j) = true :=
  (Fin.cases record027_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record027_leaf_certificates_checked

noncomputable def record028_rawLeaves (j : Fin record028.l) : List Cell :=
  (record028.leaf j).map record028.data.cells
theorem record028_raw_exact (j : Fin record028.l) :
    (record028.leaf j).map record028.data.cells = record028_rawLeaves j := rfl
noncomputable def record028_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record028_certificates (j : Fin record028.l) : Certificate :=
  record028_certificateTable.get j.val
theorem record028_leaf_checked_0 :
    RawLeafCertificate.check record028.data.quota (record028_rawLeaves 0)
      (record028_certificates 0) = true := by
  change RawLeafCertificate.check record028.data.quota [] (.quota 1) = true
  exact empty_checked record028.data.quota 1 (by decide +kernel)
theorem record028_leaf_certificates_checked : ∀ j : Fin record028.l,
    RawLeafCertificate.check record028.data.quota (record028_rawLeaves j)
      (record028_certificates j) = true :=
  (Fin.cases record028_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record028_leaf_certificates_checked

noncomputable def record029_rawLeaves (j : Fin record029.l) : List Cell :=
  (record029.leaf j).map record029.data.cells
theorem record029_raw_exact (j : Fin record029.l) :
    (record029.leaf j).map record029.data.cells = record029_rawLeaves j := rfl
noncomputable def record029_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record029_certificates (j : Fin record029.l) : Certificate :=
  record029_certificateTable.get j.val
theorem record029_leaf_checked_0 :
    RawLeafCertificate.check record029.data.quota (record029_rawLeaves 0)
      (record029_certificates 0) = true := by
  change RawLeafCertificate.check record029.data.quota [] (.quota 1) = true
  exact empty_checked record029.data.quota 1 (by decide +kernel)
theorem record029_leaf_certificates_checked : ∀ j : Fin record029.l,
    RawLeafCertificate.check record029.data.quota (record029_rawLeaves j)
      (record029_certificates j) = true :=
  (Fin.cases record029_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record029_leaf_certificates_checked

noncomputable def record030_rawLeaves (j : Fin record030.l) : List Cell :=
  (record030.leaf j).map record030.data.cells
theorem record030_raw_exact (j : Fin record030.l) :
    (record030.leaf j).map record030.data.cells = record030_rawLeaves j := rfl
noncomputable def record030_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record030_certificates (j : Fin record030.l) : Certificate :=
  record030_certificateTable.get j.val
theorem record030_leaf_checked_0 :
    RawLeafCertificate.check record030.data.quota (record030_rawLeaves 0)
      (record030_certificates 0) = true := by
  change RawLeafCertificate.check record030.data.quota [] (.quota 1) = true
  exact empty_checked record030.data.quota 1 (by decide +kernel)
theorem record030_leaf_certificates_checked : ∀ j : Fin record030.l,
    RawLeafCertificate.check record030.data.quota (record030_rawLeaves j)
      (record030_certificates j) = true :=
  (Fin.cases record030_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record030_leaf_certificates_checked

noncomputable def record031_rawLeaves (j : Fin record031.l) : List Cell :=
  (record031.leaf j).map record031.data.cells
theorem record031_raw_exact (j : Fin record031.l) :
    (record031.leaf j).map record031.data.cells = record031_rawLeaves j := rfl
noncomputable def record031_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record031_certificates (j : Fin record031.l) : Certificate :=
  record031_certificateTable.get j.val
theorem record031_leaf_checked_0 :
    RawLeafCertificate.check record031.data.quota (record031_rawLeaves 0)
      (record031_certificates 0) = true := by
  change RawLeafCertificate.check record031.data.quota [] (.quota 1) = true
  exact empty_checked record031.data.quota 1 (by decide +kernel)
theorem record031_leaf_certificates_checked : ∀ j : Fin record031.l,
    RawLeafCertificate.check record031.data.quota (record031_rawLeaves j)
      (record031_certificates j) = true :=
  (Fin.cases record031_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record031_leaf_certificates_checked

noncomputable def record032_rawLeaves (j : Fin record032.l) : List Cell :=
  (record032.leaf j).map record032.data.cells
theorem record032_raw_exact (j : Fin record032.l) :
    (record032.leaf j).map record032.data.cells = record032_rawLeaves j := rfl
noncomputable def record032_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record032_certificates (j : Fin record032.l) : Certificate :=
  record032_certificateTable.get j.val
theorem record032_leaf_checked_0 :
    RawLeafCertificate.check record032.data.quota (record032_rawLeaves 0)
      (record032_certificates 0) = true := by
  change RawLeafCertificate.check record032.data.quota [] (.quota 1) = true
  exact empty_checked record032.data.quota 1 (by decide +kernel)
theorem record032_leaf_certificates_checked : ∀ j : Fin record032.l,
    RawLeafCertificate.check record032.data.quota (record032_rawLeaves j)
      (record032_certificates j) = true :=
  (Fin.cases record032_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record032_leaf_certificates_checked

noncomputable def record033_rawLeaves (j : Fin record033.l) : List Cell :=
  (record033.leaf j).map record033.data.cells
theorem record033_raw_exact (j : Fin record033.l) :
    (record033.leaf j).map record033.data.cells = record033_rawLeaves j := rfl
noncomputable def record033_certificateTable : Table Certificate :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M000.r0018))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M000.r0019)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M000.r0020))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M000.r0021))))
 (.branch 6
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M000.r0022))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M000.r0023)))
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M000.r0024))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M000.r0025)))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (.matching Nonrational.InducedTerminalMatches.M000.r0026))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M000.r0027)))
 (.branch 11
 (.leaf (.matching Nonrational.InducedTerminalMatches.M000.r0028))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M000.r0029))))
 (.branch 14
 (.branch 13
 (.leaf (.matching Nonrational.InducedTerminalMatches.M000.r0030))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M000.r0031)))
 (.branch 15
 (.leaf (.matching Nonrational.InducedTerminalMatches.M001.r0032))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M001.r0033))))))
noncomputable def record033_certificates (j : Fin record033.l) : Certificate :=
  record033_certificateTable.get j.val
theorem record033_leaf_checked_0 :
    RawLeafCertificate.check record033.data.quota (record033_rawLeaves 0)
      (record033_certificates 0) = true := by
  change RawLeafCertificate.check record033.data.quota (record033_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M000.r0018) = true
  exact matching_checked record033.data.quota (record033_rawLeaves 0) Nonrational.InducedTerminalMatches.M000.r0018
    Nonrational.InducedTerminalMatches.M000.r0018_checked (by decide +kernel)
theorem record033_leaf_checked_1 :
    RawLeafCertificate.check record033.data.quota (record033_rawLeaves 1)
      (record033_certificates 1) = true := by
  change RawLeafCertificate.check record033.data.quota (record033_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M000.r0019) = true
  exact matching_checked record033.data.quota (record033_rawLeaves 1) Nonrational.InducedTerminalMatches.M000.r0019
    Nonrational.InducedTerminalMatches.M000.r0019_checked (by decide +kernel)
theorem record033_leaf_checked_2 :
    RawLeafCertificate.check record033.data.quota (record033_rawLeaves 2)
      (record033_certificates 2) = true := by
  change RawLeafCertificate.check record033.data.quota (record033_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M000.r0020) = true
  exact matching_checked record033.data.quota (record033_rawLeaves 2) Nonrational.InducedTerminalMatches.M000.r0020
    Nonrational.InducedTerminalMatches.M000.r0020_checked (by decide +kernel)
theorem record033_leaf_checked_3 :
    RawLeafCertificate.check record033.data.quota (record033_rawLeaves 3)
      (record033_certificates 3) = true := by
  change RawLeafCertificate.check record033.data.quota (record033_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M000.r0021) = true
  exact matching_checked record033.data.quota (record033_rawLeaves 3) Nonrational.InducedTerminalMatches.M000.r0021
    Nonrational.InducedTerminalMatches.M000.r0021_checked (by decide +kernel)
theorem record033_leaf_checked_4 :
    RawLeafCertificate.check record033.data.quota (record033_rawLeaves 4)
      (record033_certificates 4) = true := by
  change RawLeafCertificate.check record033.data.quota (record033_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M000.r0022) = true
  exact matching_checked record033.data.quota (record033_rawLeaves 4) Nonrational.InducedTerminalMatches.M000.r0022
    Nonrational.InducedTerminalMatches.M000.r0022_checked (by decide +kernel)
theorem record033_leaf_checked_5 :
    RawLeafCertificate.check record033.data.quota (record033_rawLeaves 5)
      (record033_certificates 5) = true := by
  change RawLeafCertificate.check record033.data.quota (record033_rawLeaves 5)
    (.matching Nonrational.InducedTerminalMatches.M000.r0023) = true
  exact matching_checked record033.data.quota (record033_rawLeaves 5) Nonrational.InducedTerminalMatches.M000.r0023
    Nonrational.InducedTerminalMatches.M000.r0023_checked (by decide +kernel)
theorem record033_leaf_checked_6 :
    RawLeafCertificate.check record033.data.quota (record033_rawLeaves 6)
      (record033_certificates 6) = true := by
  change RawLeafCertificate.check record033.data.quota (record033_rawLeaves 6)
    (.matching Nonrational.InducedTerminalMatches.M000.r0024) = true
  exact matching_checked record033.data.quota (record033_rawLeaves 6) Nonrational.InducedTerminalMatches.M000.r0024
    Nonrational.InducedTerminalMatches.M000.r0024_checked (by decide +kernel)
theorem record033_leaf_checked_7 :
    RawLeafCertificate.check record033.data.quota (record033_rawLeaves 7)
      (record033_certificates 7) = true := by
  change RawLeafCertificate.check record033.data.quota (record033_rawLeaves 7)
    (.matching Nonrational.InducedTerminalMatches.M000.r0025) = true
  exact matching_checked record033.data.quota (record033_rawLeaves 7) Nonrational.InducedTerminalMatches.M000.r0025
    Nonrational.InducedTerminalMatches.M000.r0025_checked (by decide +kernel)
theorem record033_leaf_checked_8 :
    RawLeafCertificate.check record033.data.quota (record033_rawLeaves 8)
      (record033_certificates 8) = true := by
  change RawLeafCertificate.check record033.data.quota (record033_rawLeaves 8)
    (.matching Nonrational.InducedTerminalMatches.M000.r0026) = true
  exact matching_checked record033.data.quota (record033_rawLeaves 8) Nonrational.InducedTerminalMatches.M000.r0026
    Nonrational.InducedTerminalMatches.M000.r0026_checked (by decide +kernel)
theorem record033_leaf_checked_9 :
    RawLeafCertificate.check record033.data.quota (record033_rawLeaves 9)
      (record033_certificates 9) = true := by
  change RawLeafCertificate.check record033.data.quota (record033_rawLeaves 9)
    (.matching Nonrational.InducedTerminalMatches.M000.r0027) = true
  exact matching_checked record033.data.quota (record033_rawLeaves 9) Nonrational.InducedTerminalMatches.M000.r0027
    Nonrational.InducedTerminalMatches.M000.r0027_checked (by decide +kernel)
theorem record033_leaf_checked_10 :
    RawLeafCertificate.check record033.data.quota (record033_rawLeaves 10)
      (record033_certificates 10) = true := by
  change RawLeafCertificate.check record033.data.quota (record033_rawLeaves 10)
    (.matching Nonrational.InducedTerminalMatches.M000.r0028) = true
  exact matching_checked record033.data.quota (record033_rawLeaves 10) Nonrational.InducedTerminalMatches.M000.r0028
    Nonrational.InducedTerminalMatches.M000.r0028_checked (by decide +kernel)
theorem record033_leaf_checked_11 :
    RawLeafCertificate.check record033.data.quota (record033_rawLeaves 11)
      (record033_certificates 11) = true := by
  change RawLeafCertificate.check record033.data.quota (record033_rawLeaves 11)
    (.matching Nonrational.InducedTerminalMatches.M000.r0029) = true
  exact matching_checked record033.data.quota (record033_rawLeaves 11) Nonrational.InducedTerminalMatches.M000.r0029
    Nonrational.InducedTerminalMatches.M000.r0029_checked (by decide +kernel)
theorem record033_leaf_checked_12 :
    RawLeafCertificate.check record033.data.quota (record033_rawLeaves 12)
      (record033_certificates 12) = true := by
  change RawLeafCertificate.check record033.data.quota (record033_rawLeaves 12)
    (.matching Nonrational.InducedTerminalMatches.M000.r0030) = true
  exact matching_checked record033.data.quota (record033_rawLeaves 12) Nonrational.InducedTerminalMatches.M000.r0030
    Nonrational.InducedTerminalMatches.M000.r0030_checked (by decide +kernel)
theorem record033_leaf_checked_13 :
    RawLeafCertificate.check record033.data.quota (record033_rawLeaves 13)
      (record033_certificates 13) = true := by
  change RawLeafCertificate.check record033.data.quota (record033_rawLeaves 13)
    (.matching Nonrational.InducedTerminalMatches.M000.r0031) = true
  exact matching_checked record033.data.quota (record033_rawLeaves 13) Nonrational.InducedTerminalMatches.M000.r0031
    Nonrational.InducedTerminalMatches.M000.r0031_checked (by decide +kernel)
theorem record033_leaf_checked_14 :
    RawLeafCertificate.check record033.data.quota (record033_rawLeaves 14)
      (record033_certificates 14) = true := by
  change RawLeafCertificate.check record033.data.quota (record033_rawLeaves 14)
    (.matching Nonrational.InducedTerminalMatches.M001.r0032) = true
  exact matching_checked record033.data.quota (record033_rawLeaves 14) Nonrational.InducedTerminalMatches.M001.r0032
    Nonrational.InducedTerminalMatches.M001.r0032_checked (by decide +kernel)
theorem record033_leaf_checked_15 :
    RawLeafCertificate.check record033.data.quota (record033_rawLeaves 15)
      (record033_certificates 15) = true := by
  change RawLeafCertificate.check record033.data.quota (record033_rawLeaves 15)
    (.matching Nonrational.InducedTerminalMatches.M001.r0033) = true
  exact matching_checked record033.data.quota (record033_rawLeaves 15) Nonrational.InducedTerminalMatches.M001.r0033
    Nonrational.InducedTerminalMatches.M001.r0033_checked (by decide +kernel)
theorem record033_leaf_certificates_checked : ∀ j : Fin record033.l,
    RawLeafCertificate.check record033.data.quota (record033_rawLeaves j)
      (record033_certificates j) = true :=
  (Fin.cases record033_leaf_checked_0 (Fin.cases record033_leaf_checked_1 (Fin.cases record033_leaf_checked_2 (Fin.cases record033_leaf_checked_3 (Fin.cases record033_leaf_checked_4 (Fin.cases record033_leaf_checked_5 (Fin.cases record033_leaf_checked_6 (Fin.cases record033_leaf_checked_7 (Fin.cases record033_leaf_checked_8 (Fin.cases record033_leaf_checked_9 (Fin.cases record033_leaf_checked_10 (Fin.cases record033_leaf_checked_11 (Fin.cases record033_leaf_checked_12 (Fin.cases record033_leaf_checked_13 (Fin.cases record033_leaf_checked_14 (Fin.cases record033_leaf_checked_15 (fun j => Fin.elim0 j)))))))))))))))))
#print axioms record033_leaf_certificates_checked
end Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029
