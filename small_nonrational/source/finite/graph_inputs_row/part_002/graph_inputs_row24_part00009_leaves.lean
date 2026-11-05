module
prelude
public import GraphInputsRow24Part00009Data
public import FastRawLeafCertificate
public import InducedTerminalMatches.M005
public import InducedTerminalMatches.M006
public import InducedTerminalMatches.M007
public import InducedTerminalMatches.M008

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009
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
(.leaf (.quota 1))
noncomputable def record019_certificates (j : Fin record019.l) : Certificate :=
  record019_certificateTable.get j.val
theorem record019_leaf_checked_0 :
    RawLeafCertificate.check record019.data.quota (record019_rawLeaves 0)
      (record019_certificates 0) = true := by
  change RawLeafCertificate.check record019.data.quota [] (.quota 1) = true
  exact empty_checked record019.data.quota 1 (by decide +kernel)
theorem record019_leaf_certificates_checked : ∀ j : Fin record019.l,
    RawLeafCertificate.check record019.data.quota (record019_rawLeaves j)
      (record019_certificates j) = true :=
  (Fin.cases record019_leaf_checked_0 (fun j => Fin.elim0 j))
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
(.branch 36
 (.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M005.r0187))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M005.r0188)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M005.r0189))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M005.r0190))))
 (.branch 6
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M005.r0191))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M006.r0192)))
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M006.r0193))
 (.branch 8
 (.leaf (.matching Nonrational.InducedTerminalMatches.M006.r0194))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M006.r0195))))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf (.matching Nonrational.InducedTerminalMatches.M006.r0196))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M006.r0197)))
 (.branch 12
 (.leaf (.matching Nonrational.InducedTerminalMatches.M006.r0198))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M006.r0199))))
 (.branch 15
 (.branch 14
 (.leaf (.matching Nonrational.InducedTerminalMatches.M006.r0200))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M006.r0201)))
 (.branch 16
 (.leaf (.matching Nonrational.InducedTerminalMatches.M006.r0202))
 (.branch 17
 (.leaf (.matching Nonrational.InducedTerminalMatches.M006.r0203))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M006.r0204)))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf (.matching Nonrational.InducedTerminalMatches.M006.r0205))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M006.r0206)))
 (.branch 21
 (.leaf (.matching Nonrational.InducedTerminalMatches.M006.r0207))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M006.r0208))))
 (.branch 24
 (.branch 23
 (.leaf (.matching Nonrational.InducedTerminalMatches.M006.r0209))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M006.r0210)))
 (.branch 25
 (.leaf (.matching Nonrational.InducedTerminalMatches.M006.r0211))
 (.branch 26
 (.leaf (.matching Nonrational.InducedTerminalMatches.M006.r0212))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M006.r0213))))))
 (.branch 31
 (.branch 29
 (.branch 28
 (.leaf (.matching Nonrational.InducedTerminalMatches.M006.r0214))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M006.r0215)))
 (.branch 30
 (.leaf (.matching Nonrational.InducedTerminalMatches.M006.r0216))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M006.r0217))))
 (.branch 33
 (.branch 32
 (.leaf (.matching Nonrational.InducedTerminalMatches.M006.r0218))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M006.r0219)))
 (.branch 34
 (.leaf (.matching Nonrational.InducedTerminalMatches.M006.r0220))
 (.branch 35
 (.leaf (.matching Nonrational.InducedTerminalMatches.M006.r0221))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M006.r0222))))))))
 (.branch 54
 (.branch 45
 (.branch 40
 (.branch 38
 (.branch 37
 (.leaf (.matching Nonrational.InducedTerminalMatches.M006.r0223))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M007.r0224)))
 (.branch 39
 (.leaf (.matching Nonrational.InducedTerminalMatches.M007.r0225))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M007.r0226))))
 (.branch 42
 (.branch 41
 (.leaf (.matching Nonrational.InducedTerminalMatches.M007.r0227))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M007.r0228)))
 (.branch 43
 (.leaf (.matching Nonrational.InducedTerminalMatches.M007.r0229))
 (.branch 44
 (.leaf (.matching Nonrational.InducedTerminalMatches.M007.r0230))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M007.r0231))))))
 (.branch 49
 (.branch 47
 (.branch 46
 (.leaf (.matching Nonrational.InducedTerminalMatches.M007.r0232))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M007.r0233)))
 (.branch 48
 (.leaf (.matching Nonrational.InducedTerminalMatches.M007.r0234))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M007.r0235))))
 (.branch 51
 (.branch 50
 (.leaf (.matching Nonrational.InducedTerminalMatches.M007.r0236))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M007.r0237)))
 (.branch 52
 (.leaf (.matching Nonrational.InducedTerminalMatches.M007.r0238))
 (.branch 53
 (.leaf (.matching Nonrational.InducedTerminalMatches.M007.r0239))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M007.r0240)))))))
 (.branch 63
 (.branch 58
 (.branch 56
 (.branch 55
 (.leaf (.matching Nonrational.InducedTerminalMatches.M007.r0241))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M007.r0242)))
 (.branch 57
 (.leaf (.matching Nonrational.InducedTerminalMatches.M007.r0243))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M007.r0244))))
 (.branch 60
 (.branch 59
 (.leaf (.matching Nonrational.InducedTerminalMatches.M007.r0245))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M007.r0246)))
 (.branch 61
 (.leaf (.matching Nonrational.InducedTerminalMatches.M007.r0247))
 (.branch 62
 (.leaf (.matching Nonrational.InducedTerminalMatches.M007.r0248))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M007.r0249))))))
 (.branch 68
 (.branch 65
 (.branch 64
 (.leaf (.matching Nonrational.InducedTerminalMatches.M007.r0250))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M007.r0251)))
 (.branch 66
 (.leaf (.matching Nonrational.InducedTerminalMatches.M007.r0252))
 (.branch 67
 (.leaf (.matching Nonrational.InducedTerminalMatches.M007.r0253))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M007.r0254)))))
 (.branch 70
 (.branch 69
 (.leaf (.matching Nonrational.InducedTerminalMatches.M007.r0255))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M008.r0256)))
 (.branch 71
 (.leaf (.matching Nonrational.InducedTerminalMatches.M008.r0257))
 (.branch 72
 (.leaf (.matching Nonrational.InducedTerminalMatches.M008.r0258))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M008.r0259)))))))))
noncomputable def record024_certificates (j : Fin record024.l) : Certificate :=
  record024_certificateTable.get j.val
theorem record024_leaf_checked_0 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 0)
      (record024_certificates 0) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 0)
    (.matching Nonrational.InducedTerminalMatches.M005.r0187) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 0) Nonrational.InducedTerminalMatches.M005.r0187
    Nonrational.InducedTerminalMatches.M005.r0187_checked (by decide +kernel)
theorem record024_leaf_checked_1 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 1)
      (record024_certificates 1) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 1)
    (.matching Nonrational.InducedTerminalMatches.M005.r0188) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 1) Nonrational.InducedTerminalMatches.M005.r0188
    Nonrational.InducedTerminalMatches.M005.r0188_checked (by decide +kernel)
theorem record024_leaf_checked_2 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 2)
      (record024_certificates 2) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 2)
    (.matching Nonrational.InducedTerminalMatches.M005.r0189) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 2) Nonrational.InducedTerminalMatches.M005.r0189
    Nonrational.InducedTerminalMatches.M005.r0189_checked (by decide +kernel)
theorem record024_leaf_checked_3 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 3)
      (record024_certificates 3) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 3)
    (.matching Nonrational.InducedTerminalMatches.M005.r0190) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 3) Nonrational.InducedTerminalMatches.M005.r0190
    Nonrational.InducedTerminalMatches.M005.r0190_checked (by decide +kernel)
theorem record024_leaf_checked_4 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 4)
      (record024_certificates 4) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 4)
    (.matching Nonrational.InducedTerminalMatches.M005.r0191) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 4) Nonrational.InducedTerminalMatches.M005.r0191
    Nonrational.InducedTerminalMatches.M005.r0191_checked (by decide +kernel)
theorem record024_leaf_checked_5 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 5)
      (record024_certificates 5) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 5)
    (.matching Nonrational.InducedTerminalMatches.M006.r0192) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 5) Nonrational.InducedTerminalMatches.M006.r0192
    Nonrational.InducedTerminalMatches.M006.r0192_checked (by decide +kernel)
theorem record024_leaf_checked_6 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 6)
      (record024_certificates 6) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 6)
    (.matching Nonrational.InducedTerminalMatches.M006.r0193) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 6) Nonrational.InducedTerminalMatches.M006.r0193
    Nonrational.InducedTerminalMatches.M006.r0193_checked (by decide +kernel)
theorem record024_leaf_checked_7 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 7)
      (record024_certificates 7) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 7)
    (.matching Nonrational.InducedTerminalMatches.M006.r0194) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 7) Nonrational.InducedTerminalMatches.M006.r0194
    Nonrational.InducedTerminalMatches.M006.r0194_checked (by decide +kernel)
theorem record024_leaf_checked_8 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 8)
      (record024_certificates 8) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 8)
    (.matching Nonrational.InducedTerminalMatches.M006.r0195) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 8) Nonrational.InducedTerminalMatches.M006.r0195
    Nonrational.InducedTerminalMatches.M006.r0195_checked (by decide +kernel)
theorem record024_leaf_checked_9 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 9)
      (record024_certificates 9) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 9)
    (.matching Nonrational.InducedTerminalMatches.M006.r0196) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 9) Nonrational.InducedTerminalMatches.M006.r0196
    Nonrational.InducedTerminalMatches.M006.r0196_checked (by decide +kernel)
theorem record024_leaf_checked_10 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 10)
      (record024_certificates 10) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 10)
    (.matching Nonrational.InducedTerminalMatches.M006.r0197) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 10) Nonrational.InducedTerminalMatches.M006.r0197
    Nonrational.InducedTerminalMatches.M006.r0197_checked (by decide +kernel)
theorem record024_leaf_checked_11 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 11)
      (record024_certificates 11) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 11)
    (.matching Nonrational.InducedTerminalMatches.M006.r0198) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 11) Nonrational.InducedTerminalMatches.M006.r0198
    Nonrational.InducedTerminalMatches.M006.r0198_checked (by decide +kernel)
theorem record024_leaf_checked_12 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 12)
      (record024_certificates 12) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 12)
    (.matching Nonrational.InducedTerminalMatches.M006.r0199) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 12) Nonrational.InducedTerminalMatches.M006.r0199
    Nonrational.InducedTerminalMatches.M006.r0199_checked (by decide +kernel)
theorem record024_leaf_checked_13 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 13)
      (record024_certificates 13) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 13)
    (.matching Nonrational.InducedTerminalMatches.M006.r0200) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 13) Nonrational.InducedTerminalMatches.M006.r0200
    Nonrational.InducedTerminalMatches.M006.r0200_checked (by decide +kernel)
theorem record024_leaf_checked_14 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 14)
      (record024_certificates 14) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 14)
    (.matching Nonrational.InducedTerminalMatches.M006.r0201) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 14) Nonrational.InducedTerminalMatches.M006.r0201
    Nonrational.InducedTerminalMatches.M006.r0201_checked (by decide +kernel)
theorem record024_leaf_checked_15 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 15)
      (record024_certificates 15) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 15)
    (.matching Nonrational.InducedTerminalMatches.M006.r0202) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 15) Nonrational.InducedTerminalMatches.M006.r0202
    Nonrational.InducedTerminalMatches.M006.r0202_checked (by decide +kernel)
theorem record024_leaf_checked_16 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 16)
      (record024_certificates 16) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 16)
    (.matching Nonrational.InducedTerminalMatches.M006.r0203) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 16) Nonrational.InducedTerminalMatches.M006.r0203
    Nonrational.InducedTerminalMatches.M006.r0203_checked (by decide +kernel)
theorem record024_leaf_checked_17 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 17)
      (record024_certificates 17) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 17)
    (.matching Nonrational.InducedTerminalMatches.M006.r0204) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 17) Nonrational.InducedTerminalMatches.M006.r0204
    Nonrational.InducedTerminalMatches.M006.r0204_checked (by decide +kernel)
theorem record024_leaf_checked_18 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 18)
      (record024_certificates 18) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 18)
    (.matching Nonrational.InducedTerminalMatches.M006.r0205) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 18) Nonrational.InducedTerminalMatches.M006.r0205
    Nonrational.InducedTerminalMatches.M006.r0205_checked (by decide +kernel)
theorem record024_leaf_checked_19 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 19)
      (record024_certificates 19) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 19)
    (.matching Nonrational.InducedTerminalMatches.M006.r0206) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 19) Nonrational.InducedTerminalMatches.M006.r0206
    Nonrational.InducedTerminalMatches.M006.r0206_checked (by decide +kernel)
theorem record024_leaf_checked_20 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 20)
      (record024_certificates 20) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 20)
    (.matching Nonrational.InducedTerminalMatches.M006.r0207) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 20) Nonrational.InducedTerminalMatches.M006.r0207
    Nonrational.InducedTerminalMatches.M006.r0207_checked (by decide +kernel)
theorem record024_leaf_checked_21 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 21)
      (record024_certificates 21) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 21)
    (.matching Nonrational.InducedTerminalMatches.M006.r0208) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 21) Nonrational.InducedTerminalMatches.M006.r0208
    Nonrational.InducedTerminalMatches.M006.r0208_checked (by decide +kernel)
theorem record024_leaf_checked_22 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 22)
      (record024_certificates 22) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 22)
    (.matching Nonrational.InducedTerminalMatches.M006.r0209) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 22) Nonrational.InducedTerminalMatches.M006.r0209
    Nonrational.InducedTerminalMatches.M006.r0209_checked (by decide +kernel)
theorem record024_leaf_checked_23 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 23)
      (record024_certificates 23) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 23)
    (.matching Nonrational.InducedTerminalMatches.M006.r0210) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 23) Nonrational.InducedTerminalMatches.M006.r0210
    Nonrational.InducedTerminalMatches.M006.r0210_checked (by decide +kernel)
theorem record024_leaf_checked_24 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 24)
      (record024_certificates 24) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 24)
    (.matching Nonrational.InducedTerminalMatches.M006.r0211) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 24) Nonrational.InducedTerminalMatches.M006.r0211
    Nonrational.InducedTerminalMatches.M006.r0211_checked (by decide +kernel)
theorem record024_leaf_checked_25 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 25)
      (record024_certificates 25) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 25)
    (.matching Nonrational.InducedTerminalMatches.M006.r0212) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 25) Nonrational.InducedTerminalMatches.M006.r0212
    Nonrational.InducedTerminalMatches.M006.r0212_checked (by decide +kernel)
theorem record024_leaf_checked_26 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 26)
      (record024_certificates 26) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 26)
    (.matching Nonrational.InducedTerminalMatches.M006.r0213) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 26) Nonrational.InducedTerminalMatches.M006.r0213
    Nonrational.InducedTerminalMatches.M006.r0213_checked (by decide +kernel)
theorem record024_leaf_checked_27 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 27)
      (record024_certificates 27) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 27)
    (.matching Nonrational.InducedTerminalMatches.M006.r0214) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 27) Nonrational.InducedTerminalMatches.M006.r0214
    Nonrational.InducedTerminalMatches.M006.r0214_checked (by decide +kernel)
theorem record024_leaf_checked_28 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 28)
      (record024_certificates 28) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 28)
    (.matching Nonrational.InducedTerminalMatches.M006.r0215) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 28) Nonrational.InducedTerminalMatches.M006.r0215
    Nonrational.InducedTerminalMatches.M006.r0215_checked (by decide +kernel)
theorem record024_leaf_checked_29 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 29)
      (record024_certificates 29) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 29)
    (.matching Nonrational.InducedTerminalMatches.M006.r0216) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 29) Nonrational.InducedTerminalMatches.M006.r0216
    Nonrational.InducedTerminalMatches.M006.r0216_checked (by decide +kernel)
theorem record024_leaf_checked_30 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 30)
      (record024_certificates 30) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 30)
    (.matching Nonrational.InducedTerminalMatches.M006.r0217) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 30) Nonrational.InducedTerminalMatches.M006.r0217
    Nonrational.InducedTerminalMatches.M006.r0217_checked (by decide +kernel)
theorem record024_leaf_checked_31 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 31)
      (record024_certificates 31) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 31)
    (.matching Nonrational.InducedTerminalMatches.M006.r0218) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 31) Nonrational.InducedTerminalMatches.M006.r0218
    Nonrational.InducedTerminalMatches.M006.r0218_checked (by decide +kernel)
theorem record024_leaf_checked_32 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 32)
      (record024_certificates 32) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 32)
    (.matching Nonrational.InducedTerminalMatches.M006.r0219) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 32) Nonrational.InducedTerminalMatches.M006.r0219
    Nonrational.InducedTerminalMatches.M006.r0219_checked (by decide +kernel)
theorem record024_leaf_checked_33 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 33)
      (record024_certificates 33) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 33)
    (.matching Nonrational.InducedTerminalMatches.M006.r0220) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 33) Nonrational.InducedTerminalMatches.M006.r0220
    Nonrational.InducedTerminalMatches.M006.r0220_checked (by decide +kernel)
theorem record024_leaf_checked_34 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 34)
      (record024_certificates 34) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 34)
    (.matching Nonrational.InducedTerminalMatches.M006.r0221) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 34) Nonrational.InducedTerminalMatches.M006.r0221
    Nonrational.InducedTerminalMatches.M006.r0221_checked (by decide +kernel)
theorem record024_leaf_checked_35 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 35)
      (record024_certificates 35) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 35)
    (.matching Nonrational.InducedTerminalMatches.M006.r0222) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 35) Nonrational.InducedTerminalMatches.M006.r0222
    Nonrational.InducedTerminalMatches.M006.r0222_checked (by decide +kernel)
theorem record024_leaf_checked_36 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 36)
      (record024_certificates 36) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 36)
    (.matching Nonrational.InducedTerminalMatches.M006.r0223) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 36) Nonrational.InducedTerminalMatches.M006.r0223
    Nonrational.InducedTerminalMatches.M006.r0223_checked (by decide +kernel)
theorem record024_leaf_checked_37 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 37)
      (record024_certificates 37) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 37)
    (.matching Nonrational.InducedTerminalMatches.M007.r0224) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 37) Nonrational.InducedTerminalMatches.M007.r0224
    Nonrational.InducedTerminalMatches.M007.r0224_checked (by decide +kernel)
theorem record024_leaf_checked_38 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 38)
      (record024_certificates 38) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 38)
    (.matching Nonrational.InducedTerminalMatches.M007.r0225) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 38) Nonrational.InducedTerminalMatches.M007.r0225
    Nonrational.InducedTerminalMatches.M007.r0225_checked (by decide +kernel)
theorem record024_leaf_checked_39 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 39)
      (record024_certificates 39) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 39)
    (.matching Nonrational.InducedTerminalMatches.M007.r0226) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 39) Nonrational.InducedTerminalMatches.M007.r0226
    Nonrational.InducedTerminalMatches.M007.r0226_checked (by decide +kernel)
theorem record024_leaf_checked_40 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 40)
      (record024_certificates 40) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 40)
    (.matching Nonrational.InducedTerminalMatches.M007.r0227) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 40) Nonrational.InducedTerminalMatches.M007.r0227
    Nonrational.InducedTerminalMatches.M007.r0227_checked (by decide +kernel)
theorem record024_leaf_checked_41 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 41)
      (record024_certificates 41) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 41)
    (.matching Nonrational.InducedTerminalMatches.M007.r0228) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 41) Nonrational.InducedTerminalMatches.M007.r0228
    Nonrational.InducedTerminalMatches.M007.r0228_checked (by decide +kernel)
theorem record024_leaf_checked_42 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 42)
      (record024_certificates 42) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 42)
    (.matching Nonrational.InducedTerminalMatches.M007.r0229) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 42) Nonrational.InducedTerminalMatches.M007.r0229
    Nonrational.InducedTerminalMatches.M007.r0229_checked (by decide +kernel)
theorem record024_leaf_checked_43 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 43)
      (record024_certificates 43) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 43)
    (.matching Nonrational.InducedTerminalMatches.M007.r0230) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 43) Nonrational.InducedTerminalMatches.M007.r0230
    Nonrational.InducedTerminalMatches.M007.r0230_checked (by decide +kernel)
theorem record024_leaf_checked_44 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 44)
      (record024_certificates 44) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 44)
    (.matching Nonrational.InducedTerminalMatches.M007.r0231) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 44) Nonrational.InducedTerminalMatches.M007.r0231
    Nonrational.InducedTerminalMatches.M007.r0231_checked (by decide +kernel)
theorem record024_leaf_checked_45 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 45)
      (record024_certificates 45) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 45)
    (.matching Nonrational.InducedTerminalMatches.M007.r0232) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 45) Nonrational.InducedTerminalMatches.M007.r0232
    Nonrational.InducedTerminalMatches.M007.r0232_checked (by decide +kernel)
theorem record024_leaf_checked_46 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 46)
      (record024_certificates 46) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 46)
    (.matching Nonrational.InducedTerminalMatches.M007.r0233) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 46) Nonrational.InducedTerminalMatches.M007.r0233
    Nonrational.InducedTerminalMatches.M007.r0233_checked (by decide +kernel)
theorem record024_leaf_checked_47 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 47)
      (record024_certificates 47) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 47)
    (.matching Nonrational.InducedTerminalMatches.M007.r0234) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 47) Nonrational.InducedTerminalMatches.M007.r0234
    Nonrational.InducedTerminalMatches.M007.r0234_checked (by decide +kernel)
theorem record024_leaf_checked_48 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 48)
      (record024_certificates 48) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 48)
    (.matching Nonrational.InducedTerminalMatches.M007.r0235) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 48) Nonrational.InducedTerminalMatches.M007.r0235
    Nonrational.InducedTerminalMatches.M007.r0235_checked (by decide +kernel)
theorem record024_leaf_checked_49 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 49)
      (record024_certificates 49) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 49)
    (.matching Nonrational.InducedTerminalMatches.M007.r0236) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 49) Nonrational.InducedTerminalMatches.M007.r0236
    Nonrational.InducedTerminalMatches.M007.r0236_checked (by decide +kernel)
theorem record024_leaf_checked_50 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 50)
      (record024_certificates 50) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 50)
    (.matching Nonrational.InducedTerminalMatches.M007.r0237) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 50) Nonrational.InducedTerminalMatches.M007.r0237
    Nonrational.InducedTerminalMatches.M007.r0237_checked (by decide +kernel)
theorem record024_leaf_checked_51 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 51)
      (record024_certificates 51) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 51)
    (.matching Nonrational.InducedTerminalMatches.M007.r0238) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 51) Nonrational.InducedTerminalMatches.M007.r0238
    Nonrational.InducedTerminalMatches.M007.r0238_checked (by decide +kernel)
theorem record024_leaf_checked_52 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 52)
      (record024_certificates 52) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 52)
    (.matching Nonrational.InducedTerminalMatches.M007.r0239) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 52) Nonrational.InducedTerminalMatches.M007.r0239
    Nonrational.InducedTerminalMatches.M007.r0239_checked (by decide +kernel)
theorem record024_leaf_checked_53 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 53)
      (record024_certificates 53) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 53)
    (.matching Nonrational.InducedTerminalMatches.M007.r0240) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 53) Nonrational.InducedTerminalMatches.M007.r0240
    Nonrational.InducedTerminalMatches.M007.r0240_checked (by decide +kernel)
theorem record024_leaf_checked_54 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 54)
      (record024_certificates 54) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 54)
    (.matching Nonrational.InducedTerminalMatches.M007.r0241) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 54) Nonrational.InducedTerminalMatches.M007.r0241
    Nonrational.InducedTerminalMatches.M007.r0241_checked (by decide +kernel)
theorem record024_leaf_checked_55 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 55)
      (record024_certificates 55) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 55)
    (.matching Nonrational.InducedTerminalMatches.M007.r0242) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 55) Nonrational.InducedTerminalMatches.M007.r0242
    Nonrational.InducedTerminalMatches.M007.r0242_checked (by decide +kernel)
theorem record024_leaf_checked_56 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 56)
      (record024_certificates 56) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 56)
    (.matching Nonrational.InducedTerminalMatches.M007.r0243) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 56) Nonrational.InducedTerminalMatches.M007.r0243
    Nonrational.InducedTerminalMatches.M007.r0243_checked (by decide +kernel)
theorem record024_leaf_checked_57 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 57)
      (record024_certificates 57) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 57)
    (.matching Nonrational.InducedTerminalMatches.M007.r0244) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 57) Nonrational.InducedTerminalMatches.M007.r0244
    Nonrational.InducedTerminalMatches.M007.r0244_checked (by decide +kernel)
theorem record024_leaf_checked_58 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 58)
      (record024_certificates 58) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 58)
    (.matching Nonrational.InducedTerminalMatches.M007.r0245) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 58) Nonrational.InducedTerminalMatches.M007.r0245
    Nonrational.InducedTerminalMatches.M007.r0245_checked (by decide +kernel)
theorem record024_leaf_checked_59 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 59)
      (record024_certificates 59) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 59)
    (.matching Nonrational.InducedTerminalMatches.M007.r0246) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 59) Nonrational.InducedTerminalMatches.M007.r0246
    Nonrational.InducedTerminalMatches.M007.r0246_checked (by decide +kernel)
theorem record024_leaf_checked_60 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 60)
      (record024_certificates 60) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 60)
    (.matching Nonrational.InducedTerminalMatches.M007.r0247) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 60) Nonrational.InducedTerminalMatches.M007.r0247
    Nonrational.InducedTerminalMatches.M007.r0247_checked (by decide +kernel)
theorem record024_leaf_checked_61 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 61)
      (record024_certificates 61) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 61)
    (.matching Nonrational.InducedTerminalMatches.M007.r0248) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 61) Nonrational.InducedTerminalMatches.M007.r0248
    Nonrational.InducedTerminalMatches.M007.r0248_checked (by decide +kernel)
theorem record024_leaf_checked_62 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 62)
      (record024_certificates 62) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 62)
    (.matching Nonrational.InducedTerminalMatches.M007.r0249) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 62) Nonrational.InducedTerminalMatches.M007.r0249
    Nonrational.InducedTerminalMatches.M007.r0249_checked (by decide +kernel)
theorem record024_leaf_checked_63 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 63)
      (record024_certificates 63) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 63)
    (.matching Nonrational.InducedTerminalMatches.M007.r0250) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 63) Nonrational.InducedTerminalMatches.M007.r0250
    Nonrational.InducedTerminalMatches.M007.r0250_checked (by decide +kernel)
theorem record024_leaf_checked_64 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 64)
      (record024_certificates 64) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 64)
    (.matching Nonrational.InducedTerminalMatches.M007.r0251) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 64) Nonrational.InducedTerminalMatches.M007.r0251
    Nonrational.InducedTerminalMatches.M007.r0251_checked (by decide +kernel)
theorem record024_leaf_checked_65 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 65)
      (record024_certificates 65) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 65)
    (.matching Nonrational.InducedTerminalMatches.M007.r0252) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 65) Nonrational.InducedTerminalMatches.M007.r0252
    Nonrational.InducedTerminalMatches.M007.r0252_checked (by decide +kernel)
theorem record024_leaf_checked_66 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 66)
      (record024_certificates 66) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 66)
    (.matching Nonrational.InducedTerminalMatches.M007.r0253) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 66) Nonrational.InducedTerminalMatches.M007.r0253
    Nonrational.InducedTerminalMatches.M007.r0253_checked (by decide +kernel)
theorem record024_leaf_checked_67 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 67)
      (record024_certificates 67) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 67)
    (.matching Nonrational.InducedTerminalMatches.M007.r0254) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 67) Nonrational.InducedTerminalMatches.M007.r0254
    Nonrational.InducedTerminalMatches.M007.r0254_checked (by decide +kernel)
theorem record024_leaf_checked_68 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 68)
      (record024_certificates 68) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 68)
    (.matching Nonrational.InducedTerminalMatches.M007.r0255) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 68) Nonrational.InducedTerminalMatches.M007.r0255
    Nonrational.InducedTerminalMatches.M007.r0255_checked (by decide +kernel)
theorem record024_leaf_checked_69 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 69)
      (record024_certificates 69) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 69)
    (.matching Nonrational.InducedTerminalMatches.M008.r0256) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 69) Nonrational.InducedTerminalMatches.M008.r0256
    Nonrational.InducedTerminalMatches.M008.r0256_checked (by decide +kernel)
theorem record024_leaf_checked_70 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 70)
      (record024_certificates 70) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 70)
    (.matching Nonrational.InducedTerminalMatches.M008.r0257) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 70) Nonrational.InducedTerminalMatches.M008.r0257
    Nonrational.InducedTerminalMatches.M008.r0257_checked (by decide +kernel)
theorem record024_leaf_checked_71 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 71)
      (record024_certificates 71) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 71)
    (.matching Nonrational.InducedTerminalMatches.M008.r0258) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 71) Nonrational.InducedTerminalMatches.M008.r0258
    Nonrational.InducedTerminalMatches.M008.r0258_checked (by decide +kernel)
theorem record024_leaf_checked_72 :
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves 72)
      (record024_certificates 72) = true := by
  change RawLeafCertificate.check record024.data.quota (record024_rawLeaves 72)
    (.matching Nonrational.InducedTerminalMatches.M008.r0259) = true
  exact matching_checked record024.data.quota (record024_rawLeaves 72) Nonrational.InducedTerminalMatches.M008.r0259
    Nonrational.InducedTerminalMatches.M008.r0259_checked (by decide +kernel)
theorem record024_leaf_certificates_checked : ∀ j : Fin record024.l,
    RawLeafCertificate.check record024.data.quota (record024_rawLeaves j)
      (record024_certificates j) = true :=
  (Fin.cases record024_leaf_checked_0 (Fin.cases record024_leaf_checked_1 (Fin.cases record024_leaf_checked_2 (Fin.cases record024_leaf_checked_3 (Fin.cases record024_leaf_checked_4 (Fin.cases record024_leaf_checked_5 (Fin.cases record024_leaf_checked_6 (Fin.cases record024_leaf_checked_7 (Fin.cases record024_leaf_checked_8 (Fin.cases record024_leaf_checked_9 (Fin.cases record024_leaf_checked_10 (Fin.cases record024_leaf_checked_11 (Fin.cases record024_leaf_checked_12 (Fin.cases record024_leaf_checked_13 (Fin.cases record024_leaf_checked_14 (Fin.cases record024_leaf_checked_15 (Fin.cases record024_leaf_checked_16 (Fin.cases record024_leaf_checked_17 (Fin.cases record024_leaf_checked_18 (Fin.cases record024_leaf_checked_19 (Fin.cases record024_leaf_checked_20 (Fin.cases record024_leaf_checked_21 (Fin.cases record024_leaf_checked_22 (Fin.cases record024_leaf_checked_23 (Fin.cases record024_leaf_checked_24 (Fin.cases record024_leaf_checked_25 (Fin.cases record024_leaf_checked_26 (Fin.cases record024_leaf_checked_27 (Fin.cases record024_leaf_checked_28 (Fin.cases record024_leaf_checked_29 (Fin.cases record024_leaf_checked_30 (Fin.cases record024_leaf_checked_31 (Fin.cases record024_leaf_checked_32 (Fin.cases record024_leaf_checked_33 (Fin.cases record024_leaf_checked_34 (Fin.cases record024_leaf_checked_35 (Fin.cases record024_leaf_checked_36 (Fin.cases record024_leaf_checked_37 (Fin.cases record024_leaf_checked_38 (Fin.cases record024_leaf_checked_39 (Fin.cases record024_leaf_checked_40 (Fin.cases record024_leaf_checked_41 (Fin.cases record024_leaf_checked_42 (Fin.cases record024_leaf_checked_43 (Fin.cases record024_leaf_checked_44 (Fin.cases record024_leaf_checked_45 (Fin.cases record024_leaf_checked_46 (Fin.cases record024_leaf_checked_47 (Fin.cases record024_leaf_checked_48 (Fin.cases record024_leaf_checked_49 (Fin.cases record024_leaf_checked_50 (Fin.cases record024_leaf_checked_51 (Fin.cases record024_leaf_checked_52 (Fin.cases record024_leaf_checked_53 (Fin.cases record024_leaf_checked_54 (Fin.cases record024_leaf_checked_55 (Fin.cases record024_leaf_checked_56 (Fin.cases record024_leaf_checked_57 (Fin.cases record024_leaf_checked_58 (Fin.cases record024_leaf_checked_59 (Fin.cases record024_leaf_checked_60 (Fin.cases record024_leaf_checked_61 (Fin.cases record024_leaf_checked_62 (Fin.cases record024_leaf_checked_63 (Fin.cases record024_leaf_checked_64 (Fin.cases record024_leaf_checked_65 (Fin.cases record024_leaf_checked_66 (Fin.cases record024_leaf_checked_67 (Fin.cases record024_leaf_checked_68 (Fin.cases record024_leaf_checked_69 (Fin.cases record024_leaf_checked_70 (Fin.cases record024_leaf_checked_71 (Fin.cases record024_leaf_checked_72 (fun j => Fin.elim0 j))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
#print axioms record024_leaf_certificates_checked
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009
