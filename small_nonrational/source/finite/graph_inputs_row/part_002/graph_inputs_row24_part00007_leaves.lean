module
prelude
public import GraphInputsRow24Part00007Data
public import FastRawLeafCertificate

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007
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
(.leaf (.quota 1))
noncomputable def record033_certificates (j : Fin record033.l) : Certificate :=
  record033_certificateTable.get j.val
theorem record033_leaf_checked_0 :
    RawLeafCertificate.check record033.data.quota (record033_rawLeaves 0)
      (record033_certificates 0) = true := by
  change RawLeafCertificate.check record033.data.quota [] (.quota 1) = true
  exact empty_checked record033.data.quota 1 (by decide +kernel)
theorem record033_leaf_certificates_checked : ∀ j : Fin record033.l,
    RawLeafCertificate.check record033.data.quota (record033_rawLeaves j)
      (record033_certificates j) = true :=
  (Fin.cases record033_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record033_leaf_certificates_checked

noncomputable def record034_rawLeaves (j : Fin record034.l) : List Cell :=
  (record034.leaf j).map record034.data.cells
theorem record034_raw_exact (j : Fin record034.l) :
    (record034.leaf j).map record034.data.cells = record034_rawLeaves j := rfl
noncomputable def record034_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record034_certificates (j : Fin record034.l) : Certificate :=
  record034_certificateTable.get j.val
theorem record034_leaf_checked_0 :
    RawLeafCertificate.check record034.data.quota (record034_rawLeaves 0)
      (record034_certificates 0) = true := by
  change RawLeafCertificate.check record034.data.quota [] (.quota 1) = true
  exact empty_checked record034.data.quota 1 (by decide +kernel)
theorem record034_leaf_certificates_checked : ∀ j : Fin record034.l,
    RawLeafCertificate.check record034.data.quota (record034_rawLeaves j)
      (record034_certificates j) = true :=
  (Fin.cases record034_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record034_leaf_certificates_checked

noncomputable def record035_rawLeaves (j : Fin record035.l) : List Cell :=
  (record035.leaf j).map record035.data.cells
theorem record035_raw_exact (j : Fin record035.l) :
    (record035.leaf j).map record035.data.cells = record035_rawLeaves j := rfl
noncomputable def record035_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record035_certificates (j : Fin record035.l) : Certificate :=
  record035_certificateTable.get j.val
theorem record035_leaf_checked_0 :
    RawLeafCertificate.check record035.data.quota (record035_rawLeaves 0)
      (record035_certificates 0) = true := by
  change RawLeafCertificate.check record035.data.quota [] (.quota 1) = true
  exact empty_checked record035.data.quota 1 (by decide +kernel)
theorem record035_leaf_certificates_checked : ∀ j : Fin record035.l,
    RawLeafCertificate.check record035.data.quota (record035_rawLeaves j)
      (record035_certificates j) = true :=
  (Fin.cases record035_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record035_leaf_certificates_checked

noncomputable def record036_rawLeaves (j : Fin record036.l) : List Cell :=
  (record036.leaf j).map record036.data.cells
theorem record036_raw_exact (j : Fin record036.l) :
    (record036.leaf j).map record036.data.cells = record036_rawLeaves j := rfl
noncomputable def record036_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record036_certificates (j : Fin record036.l) : Certificate :=
  record036_certificateTable.get j.val
theorem record036_leaf_checked_0 :
    RawLeafCertificate.check record036.data.quota (record036_rawLeaves 0)
      (record036_certificates 0) = true := by
  change RawLeafCertificate.check record036.data.quota [] (.quota 1) = true
  exact empty_checked record036.data.quota 1 (by decide +kernel)
theorem record036_leaf_certificates_checked : ∀ j : Fin record036.l,
    RawLeafCertificate.check record036.data.quota (record036_rawLeaves j)
      (record036_certificates j) = true :=
  (Fin.cases record036_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record036_leaf_certificates_checked

noncomputable def record037_rawLeaves (j : Fin record037.l) : List Cell :=
  (record037.leaf j).map record037.data.cells
theorem record037_raw_exact (j : Fin record037.l) :
    (record037.leaf j).map record037.data.cells = record037_rawLeaves j := rfl
noncomputable def record037_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record037_certificates (j : Fin record037.l) : Certificate :=
  record037_certificateTable.get j.val
theorem record037_leaf_checked_0 :
    RawLeafCertificate.check record037.data.quota (record037_rawLeaves 0)
      (record037_certificates 0) = true := by
  change RawLeafCertificate.check record037.data.quota [] (.quota 1) = true
  exact empty_checked record037.data.quota 1 (by decide +kernel)
theorem record037_leaf_certificates_checked : ∀ j : Fin record037.l,
    RawLeafCertificate.check record037.data.quota (record037_rawLeaves j)
      (record037_certificates j) = true :=
  (Fin.cases record037_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record037_leaf_certificates_checked

noncomputable def record038_rawLeaves (j : Fin record038.l) : List Cell :=
  (record038.leaf j).map record038.data.cells
theorem record038_raw_exact (j : Fin record038.l) :
    (record038.leaf j).map record038.data.cells = record038_rawLeaves j := rfl
noncomputable def record038_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record038_certificates (j : Fin record038.l) : Certificate :=
  record038_certificateTable.get j.val
theorem record038_leaf_checked_0 :
    RawLeafCertificate.check record038.data.quota (record038_rawLeaves 0)
      (record038_certificates 0) = true := by
  change RawLeafCertificate.check record038.data.quota [] (.quota 1) = true
  exact empty_checked record038.data.quota 1 (by decide +kernel)
theorem record038_leaf_certificates_checked : ∀ j : Fin record038.l,
    RawLeafCertificate.check record038.data.quota (record038_rawLeaves j)
      (record038_certificates j) = true :=
  (Fin.cases record038_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record038_leaf_certificates_checked

noncomputable def record039_rawLeaves (j : Fin record039.l) : List Cell :=
  (record039.leaf j).map record039.data.cells
theorem record039_raw_exact (j : Fin record039.l) :
    (record039.leaf j).map record039.data.cells = record039_rawLeaves j := rfl
noncomputable def record039_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record039_certificates (j : Fin record039.l) : Certificate :=
  record039_certificateTable.get j.val
theorem record039_leaf_checked_0 :
    RawLeafCertificate.check record039.data.quota (record039_rawLeaves 0)
      (record039_certificates 0) = true := by
  change RawLeafCertificate.check record039.data.quota [] (.quota 1) = true
  exact empty_checked record039.data.quota 1 (by decide +kernel)
theorem record039_leaf_certificates_checked : ∀ j : Fin record039.l,
    RawLeafCertificate.check record039.data.quota (record039_rawLeaves j)
      (record039_certificates j) = true :=
  (Fin.cases record039_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record039_leaf_certificates_checked

noncomputable def record040_rawLeaves (j : Fin record040.l) : List Cell :=
  (record040.leaf j).map record040.data.cells
theorem record040_raw_exact (j : Fin record040.l) :
    (record040.leaf j).map record040.data.cells = record040_rawLeaves j := rfl
noncomputable def record040_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record040_certificates (j : Fin record040.l) : Certificate :=
  record040_certificateTable.get j.val
theorem record040_leaf_checked_0 :
    RawLeafCertificate.check record040.data.quota (record040_rawLeaves 0)
      (record040_certificates 0) = true := by
  change RawLeafCertificate.check record040.data.quota [] (.quota 1) = true
  exact empty_checked record040.data.quota 1 (by decide +kernel)
theorem record040_leaf_certificates_checked : ∀ j : Fin record040.l,
    RawLeafCertificate.check record040.data.quota (record040_rawLeaves j)
      (record040_certificates j) = true :=
  (Fin.cases record040_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record040_leaf_certificates_checked

noncomputable def record041_rawLeaves (j : Fin record041.l) : List Cell :=
  (record041.leaf j).map record041.data.cells
theorem record041_raw_exact (j : Fin record041.l) :
    (record041.leaf j).map record041.data.cells = record041_rawLeaves j := rfl
noncomputable def record041_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record041_certificates (j : Fin record041.l) : Certificate :=
  record041_certificateTable.get j.val
theorem record041_leaf_checked_0 :
    RawLeafCertificate.check record041.data.quota (record041_rawLeaves 0)
      (record041_certificates 0) = true := by
  change RawLeafCertificate.check record041.data.quota [] (.quota 1) = true
  exact empty_checked record041.data.quota 1 (by decide +kernel)
theorem record041_leaf_certificates_checked : ∀ j : Fin record041.l,
    RawLeafCertificate.check record041.data.quota (record041_rawLeaves j)
      (record041_certificates j) = true :=
  (Fin.cases record041_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record041_leaf_certificates_checked

noncomputable def record042_rawLeaves (j : Fin record042.l) : List Cell :=
  (record042.leaf j).map record042.data.cells
theorem record042_raw_exact (j : Fin record042.l) :
    (record042.leaf j).map record042.data.cells = record042_rawLeaves j := rfl
noncomputable def record042_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record042_certificates (j : Fin record042.l) : Certificate :=
  record042_certificateTable.get j.val
theorem record042_leaf_checked_0 :
    RawLeafCertificate.check record042.data.quota (record042_rawLeaves 0)
      (record042_certificates 0) = true := by
  change RawLeafCertificate.check record042.data.quota [] (.quota 1) = true
  exact empty_checked record042.data.quota 1 (by decide +kernel)
theorem record042_leaf_certificates_checked : ∀ j : Fin record042.l,
    RawLeafCertificate.check record042.data.quota (record042_rawLeaves j)
      (record042_certificates j) = true :=
  (Fin.cases record042_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record042_leaf_certificates_checked

noncomputable def record043_rawLeaves (j : Fin record043.l) : List Cell :=
  (record043.leaf j).map record043.data.cells
theorem record043_raw_exact (j : Fin record043.l) :
    (record043.leaf j).map record043.data.cells = record043_rawLeaves j := rfl
noncomputable def record043_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record043_certificates (j : Fin record043.l) : Certificate :=
  record043_certificateTable.get j.val
theorem record043_leaf_checked_0 :
    RawLeafCertificate.check record043.data.quota (record043_rawLeaves 0)
      (record043_certificates 0) = true := by
  change RawLeafCertificate.check record043.data.quota [] (.quota 1) = true
  exact empty_checked record043.data.quota 1 (by decide +kernel)
theorem record043_leaf_certificates_checked : ∀ j : Fin record043.l,
    RawLeafCertificate.check record043.data.quota (record043_rawLeaves j)
      (record043_certificates j) = true :=
  (Fin.cases record043_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record043_leaf_certificates_checked

noncomputable def record044_rawLeaves (j : Fin record044.l) : List Cell :=
  (record044.leaf j).map record044.data.cells
theorem record044_raw_exact (j : Fin record044.l) :
    (record044.leaf j).map record044.data.cells = record044_rawLeaves j := rfl
noncomputable def record044_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record044_certificates (j : Fin record044.l) : Certificate :=
  record044_certificateTable.get j.val
theorem record044_leaf_checked_0 :
    RawLeafCertificate.check record044.data.quota (record044_rawLeaves 0)
      (record044_certificates 0) = true := by
  change RawLeafCertificate.check record044.data.quota [] (.quota 1) = true
  exact empty_checked record044.data.quota 1 (by decide +kernel)
theorem record044_leaf_certificates_checked : ∀ j : Fin record044.l,
    RawLeafCertificate.check record044.data.quota (record044_rawLeaves j)
      (record044_certificates j) = true :=
  (Fin.cases record044_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record044_leaf_certificates_checked

noncomputable def record045_rawLeaves (j : Fin record045.l) : List Cell :=
  (record045.leaf j).map record045.data.cells
theorem record045_raw_exact (j : Fin record045.l) :
    (record045.leaf j).map record045.data.cells = record045_rawLeaves j := rfl
noncomputable def record045_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record045_certificates (j : Fin record045.l) : Certificate :=
  record045_certificateTable.get j.val
theorem record045_leaf_checked_0 :
    RawLeafCertificate.check record045.data.quota (record045_rawLeaves 0)
      (record045_certificates 0) = true := by
  change RawLeafCertificate.check record045.data.quota [] (.quota 1) = true
  exact empty_checked record045.data.quota 1 (by decide +kernel)
theorem record045_leaf_certificates_checked : ∀ j : Fin record045.l,
    RawLeafCertificate.check record045.data.quota (record045_rawLeaves j)
      (record045_certificates j) = true :=
  (Fin.cases record045_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record045_leaf_certificates_checked

noncomputable def record046_rawLeaves (j : Fin record046.l) : List Cell :=
  (record046.leaf j).map record046.data.cells
theorem record046_raw_exact (j : Fin record046.l) :
    (record046.leaf j).map record046.data.cells = record046_rawLeaves j := rfl
noncomputable def record046_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record046_certificates (j : Fin record046.l) : Certificate :=
  record046_certificateTable.get j.val
theorem record046_leaf_checked_0 :
    RawLeafCertificate.check record046.data.quota (record046_rawLeaves 0)
      (record046_certificates 0) = true := by
  change RawLeafCertificate.check record046.data.quota [] (.quota 1) = true
  exact empty_checked record046.data.quota 1 (by decide +kernel)
theorem record046_leaf_certificates_checked : ∀ j : Fin record046.l,
    RawLeafCertificate.check record046.data.quota (record046_rawLeaves j)
      (record046_certificates j) = true :=
  (Fin.cases record046_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record046_leaf_certificates_checked

noncomputable def record047_rawLeaves (j : Fin record047.l) : List Cell :=
  (record047.leaf j).map record047.data.cells
theorem record047_raw_exact (j : Fin record047.l) :
    (record047.leaf j).map record047.data.cells = record047_rawLeaves j := rfl
noncomputable def record047_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record047_certificates (j : Fin record047.l) : Certificate :=
  record047_certificateTable.get j.val
theorem record047_leaf_checked_0 :
    RawLeafCertificate.check record047.data.quota (record047_rawLeaves 0)
      (record047_certificates 0) = true := by
  change RawLeafCertificate.check record047.data.quota [] (.quota 1) = true
  exact empty_checked record047.data.quota 1 (by decide +kernel)
theorem record047_leaf_certificates_checked : ∀ j : Fin record047.l,
    RawLeafCertificate.check record047.data.quota (record047_rawLeaves j)
      (record047_certificates j) = true :=
  (Fin.cases record047_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record047_leaf_certificates_checked

noncomputable def record048_rawLeaves (j : Fin record048.l) : List Cell :=
  (record048.leaf j).map record048.data.cells
theorem record048_raw_exact (j : Fin record048.l) :
    (record048.leaf j).map record048.data.cells = record048_rawLeaves j := rfl
noncomputable def record048_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record048_certificates (j : Fin record048.l) : Certificate :=
  record048_certificateTable.get j.val
theorem record048_leaf_checked_0 :
    RawLeafCertificate.check record048.data.quota (record048_rawLeaves 0)
      (record048_certificates 0) = true := by
  change RawLeafCertificate.check record048.data.quota [] (.quota 1) = true
  exact empty_checked record048.data.quota 1 (by decide +kernel)
theorem record048_leaf_certificates_checked : ∀ j : Fin record048.l,
    RawLeafCertificate.check record048.data.quota (record048_rawLeaves j)
      (record048_certificates j) = true :=
  (Fin.cases record048_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record048_leaf_certificates_checked

noncomputable def record049_rawLeaves (j : Fin record049.l) : List Cell :=
  (record049.leaf j).map record049.data.cells
theorem record049_raw_exact (j : Fin record049.l) :
    (record049.leaf j).map record049.data.cells = record049_rawLeaves j := rfl
noncomputable def record049_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record049_certificates (j : Fin record049.l) : Certificate :=
  record049_certificateTable.get j.val
theorem record049_leaf_checked_0 :
    RawLeafCertificate.check record049.data.quota (record049_rawLeaves 0)
      (record049_certificates 0) = true := by
  change RawLeafCertificate.check record049.data.quota [] (.quota 1) = true
  exact empty_checked record049.data.quota 1 (by decide +kernel)
theorem record049_leaf_certificates_checked : ∀ j : Fin record049.l,
    RawLeafCertificate.check record049.data.quota (record049_rawLeaves j)
      (record049_certificates j) = true :=
  (Fin.cases record049_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record049_leaf_certificates_checked

noncomputable def record050_rawLeaves (j : Fin record050.l) : List Cell :=
  (record050.leaf j).map record050.data.cells
theorem record050_raw_exact (j : Fin record050.l) :
    (record050.leaf j).map record050.data.cells = record050_rawLeaves j := rfl
noncomputable def record050_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record050_certificates (j : Fin record050.l) : Certificate :=
  record050_certificateTable.get j.val
theorem record050_leaf_checked_0 :
    RawLeafCertificate.check record050.data.quota (record050_rawLeaves 0)
      (record050_certificates 0) = true := by
  change RawLeafCertificate.check record050.data.quota [] (.quota 1) = true
  exact empty_checked record050.data.quota 1 (by decide +kernel)
theorem record050_leaf_certificates_checked : ∀ j : Fin record050.l,
    RawLeafCertificate.check record050.data.quota (record050_rawLeaves j)
      (record050_certificates j) = true :=
  (Fin.cases record050_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record050_leaf_certificates_checked

noncomputable def record051_rawLeaves (j : Fin record051.l) : List Cell :=
  (record051.leaf j).map record051.data.cells
theorem record051_raw_exact (j : Fin record051.l) :
    (record051.leaf j).map record051.data.cells = record051_rawLeaves j := rfl
noncomputable def record051_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record051_certificates (j : Fin record051.l) : Certificate :=
  record051_certificateTable.get j.val
theorem record051_leaf_checked_0 :
    RawLeafCertificate.check record051.data.quota (record051_rawLeaves 0)
      (record051_certificates 0) = true := by
  change RawLeafCertificate.check record051.data.quota [] (.quota 1) = true
  exact empty_checked record051.data.quota 1 (by decide +kernel)
theorem record051_leaf_certificates_checked : ∀ j : Fin record051.l,
    RawLeafCertificate.check record051.data.quota (record051_rawLeaves j)
      (record051_certificates j) = true :=
  (Fin.cases record051_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record051_leaf_certificates_checked

noncomputable def record052_rawLeaves (j : Fin record052.l) : List Cell :=
  (record052.leaf j).map record052.data.cells
theorem record052_raw_exact (j : Fin record052.l) :
    (record052.leaf j).map record052.data.cells = record052_rawLeaves j := rfl
noncomputable def record052_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record052_certificates (j : Fin record052.l) : Certificate :=
  record052_certificateTable.get j.val
theorem record052_leaf_checked_0 :
    RawLeafCertificate.check record052.data.quota (record052_rawLeaves 0)
      (record052_certificates 0) = true := by
  change RawLeafCertificate.check record052.data.quota [] (.quota 1) = true
  exact empty_checked record052.data.quota 1 (by decide +kernel)
theorem record052_leaf_certificates_checked : ∀ j : Fin record052.l,
    RawLeafCertificate.check record052.data.quota (record052_rawLeaves j)
      (record052_certificates j) = true :=
  (Fin.cases record052_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record052_leaf_certificates_checked

noncomputable def record053_rawLeaves (j : Fin record053.l) : List Cell :=
  (record053.leaf j).map record053.data.cells
theorem record053_raw_exact (j : Fin record053.l) :
    (record053.leaf j).map record053.data.cells = record053_rawLeaves j := rfl
noncomputable def record053_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record053_certificates (j : Fin record053.l) : Certificate :=
  record053_certificateTable.get j.val
theorem record053_leaf_checked_0 :
    RawLeafCertificate.check record053.data.quota (record053_rawLeaves 0)
      (record053_certificates 0) = true := by
  change RawLeafCertificate.check record053.data.quota [] (.quota 1) = true
  exact empty_checked record053.data.quota 1 (by decide +kernel)
theorem record053_leaf_certificates_checked : ∀ j : Fin record053.l,
    RawLeafCertificate.check record053.data.quota (record053_rawLeaves j)
      (record053_certificates j) = true :=
  (Fin.cases record053_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record053_leaf_certificates_checked

noncomputable def record054_rawLeaves (j : Fin record054.l) : List Cell :=
  (record054.leaf j).map record054.data.cells
theorem record054_raw_exact (j : Fin record054.l) :
    (record054.leaf j).map record054.data.cells = record054_rawLeaves j := rfl
noncomputable def record054_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record054_certificates (j : Fin record054.l) : Certificate :=
  record054_certificateTable.get j.val
theorem record054_leaf_checked_0 :
    RawLeafCertificate.check record054.data.quota (record054_rawLeaves 0)
      (record054_certificates 0) = true := by
  change RawLeafCertificate.check record054.data.quota [] (.quota 1) = true
  exact empty_checked record054.data.quota 1 (by decide +kernel)
theorem record054_leaf_certificates_checked : ∀ j : Fin record054.l,
    RawLeafCertificate.check record054.data.quota (record054_rawLeaves j)
      (record054_certificates j) = true :=
  (Fin.cases record054_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record054_leaf_certificates_checked

noncomputable def record055_rawLeaves (j : Fin record055.l) : List Cell :=
  (record055.leaf j).map record055.data.cells
theorem record055_raw_exact (j : Fin record055.l) :
    (record055.leaf j).map record055.data.cells = record055_rawLeaves j := rfl
noncomputable def record055_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record055_certificates (j : Fin record055.l) : Certificate :=
  record055_certificateTable.get j.val
theorem record055_leaf_checked_0 :
    RawLeafCertificate.check record055.data.quota (record055_rawLeaves 0)
      (record055_certificates 0) = true := by
  change RawLeafCertificate.check record055.data.quota [] (.quota 1) = true
  exact empty_checked record055.data.quota 1 (by decide +kernel)
theorem record055_leaf_certificates_checked : ∀ j : Fin record055.l,
    RawLeafCertificate.check record055.data.quota (record055_rawLeaves j)
      (record055_certificates j) = true :=
  (Fin.cases record055_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record055_leaf_certificates_checked

noncomputable def record056_rawLeaves (j : Fin record056.l) : List Cell :=
  (record056.leaf j).map record056.data.cells
theorem record056_raw_exact (j : Fin record056.l) :
    (record056.leaf j).map record056.data.cells = record056_rawLeaves j := rfl
noncomputable def record056_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record056_certificates (j : Fin record056.l) : Certificate :=
  record056_certificateTable.get j.val
theorem record056_leaf_checked_0 :
    RawLeafCertificate.check record056.data.quota (record056_rawLeaves 0)
      (record056_certificates 0) = true := by
  change RawLeafCertificate.check record056.data.quota [] (.quota 1) = true
  exact empty_checked record056.data.quota 1 (by decide +kernel)
theorem record056_leaf_certificates_checked : ∀ j : Fin record056.l,
    RawLeafCertificate.check record056.data.quota (record056_rawLeaves j)
      (record056_certificates j) = true :=
  (Fin.cases record056_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record056_leaf_certificates_checked

noncomputable def record057_rawLeaves (j : Fin record057.l) : List Cell :=
  (record057.leaf j).map record057.data.cells
theorem record057_raw_exact (j : Fin record057.l) :
    (record057.leaf j).map record057.data.cells = record057_rawLeaves j := rfl
noncomputable def record057_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record057_certificates (j : Fin record057.l) : Certificate :=
  record057_certificateTable.get j.val
theorem record057_leaf_checked_0 :
    RawLeafCertificate.check record057.data.quota (record057_rawLeaves 0)
      (record057_certificates 0) = true := by
  change RawLeafCertificate.check record057.data.quota [] (.quota 1) = true
  exact empty_checked record057.data.quota 1 (by decide +kernel)
theorem record057_leaf_certificates_checked : ∀ j : Fin record057.l,
    RawLeafCertificate.check record057.data.quota (record057_rawLeaves j)
      (record057_certificates j) = true :=
  (Fin.cases record057_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record057_leaf_certificates_checked

noncomputable def record058_rawLeaves (j : Fin record058.l) : List Cell :=
  (record058.leaf j).map record058.data.cells
theorem record058_raw_exact (j : Fin record058.l) :
    (record058.leaf j).map record058.data.cells = record058_rawLeaves j := rfl
noncomputable def record058_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record058_certificates (j : Fin record058.l) : Certificate :=
  record058_certificateTable.get j.val
theorem record058_leaf_checked_0 :
    RawLeafCertificate.check record058.data.quota (record058_rawLeaves 0)
      (record058_certificates 0) = true := by
  change RawLeafCertificate.check record058.data.quota [] (.quota 1) = true
  exact empty_checked record058.data.quota 1 (by decide +kernel)
theorem record058_leaf_certificates_checked : ∀ j : Fin record058.l,
    RawLeafCertificate.check record058.data.quota (record058_rawLeaves j)
      (record058_certificates j) = true :=
  (Fin.cases record058_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record058_leaf_certificates_checked

noncomputable def record059_rawLeaves (j : Fin record059.l) : List Cell :=
  (record059.leaf j).map record059.data.cells
theorem record059_raw_exact (j : Fin record059.l) :
    (record059.leaf j).map record059.data.cells = record059_rawLeaves j := rfl
noncomputable def record059_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record059_certificates (j : Fin record059.l) : Certificate :=
  record059_certificateTable.get j.val
theorem record059_leaf_checked_0 :
    RawLeafCertificate.check record059.data.quota (record059_rawLeaves 0)
      (record059_certificates 0) = true := by
  change RawLeafCertificate.check record059.data.quota [] (.quota 1) = true
  exact empty_checked record059.data.quota 1 (by decide +kernel)
theorem record059_leaf_certificates_checked : ∀ j : Fin record059.l,
    RawLeafCertificate.check record059.data.quota (record059_rawLeaves j)
      (record059_certificates j) = true :=
  (Fin.cases record059_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record059_leaf_certificates_checked

noncomputable def record060_rawLeaves (j : Fin record060.l) : List Cell :=
  (record060.leaf j).map record060.data.cells
theorem record060_raw_exact (j : Fin record060.l) :
    (record060.leaf j).map record060.data.cells = record060_rawLeaves j := rfl
noncomputable def record060_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record060_certificates (j : Fin record060.l) : Certificate :=
  record060_certificateTable.get j.val
theorem record060_leaf_checked_0 :
    RawLeafCertificate.check record060.data.quota (record060_rawLeaves 0)
      (record060_certificates 0) = true := by
  change RawLeafCertificate.check record060.data.quota [] (.quota 1) = true
  exact empty_checked record060.data.quota 1 (by decide +kernel)
theorem record060_leaf_certificates_checked : ∀ j : Fin record060.l,
    RawLeafCertificate.check record060.data.quota (record060_rawLeaves j)
      (record060_certificates j) = true :=
  (Fin.cases record060_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record060_leaf_certificates_checked

noncomputable def record061_rawLeaves (j : Fin record061.l) : List Cell :=
  (record061.leaf j).map record061.data.cells
theorem record061_raw_exact (j : Fin record061.l) :
    (record061.leaf j).map record061.data.cells = record061_rawLeaves j := rfl
noncomputable def record061_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record061_certificates (j : Fin record061.l) : Certificate :=
  record061_certificateTable.get j.val
theorem record061_leaf_checked_0 :
    RawLeafCertificate.check record061.data.quota (record061_rawLeaves 0)
      (record061_certificates 0) = true := by
  change RawLeafCertificate.check record061.data.quota [] (.quota 1) = true
  exact empty_checked record061.data.quota 1 (by decide +kernel)
theorem record061_leaf_certificates_checked : ∀ j : Fin record061.l,
    RawLeafCertificate.check record061.data.quota (record061_rawLeaves j)
      (record061_certificates j) = true :=
  (Fin.cases record061_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record061_leaf_certificates_checked

noncomputable def record062_rawLeaves (j : Fin record062.l) : List Cell :=
  (record062.leaf j).map record062.data.cells
theorem record062_raw_exact (j : Fin record062.l) :
    (record062.leaf j).map record062.data.cells = record062_rawLeaves j := rfl
noncomputable def record062_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record062_certificates (j : Fin record062.l) : Certificate :=
  record062_certificateTable.get j.val
theorem record062_leaf_checked_0 :
    RawLeafCertificate.check record062.data.quota (record062_rawLeaves 0)
      (record062_certificates 0) = true := by
  change RawLeafCertificate.check record062.data.quota [] (.quota 1) = true
  exact empty_checked record062.data.quota 1 (by decide +kernel)
theorem record062_leaf_certificates_checked : ∀ j : Fin record062.l,
    RawLeafCertificate.check record062.data.quota (record062_rawLeaves j)
      (record062_certificates j) = true :=
  (Fin.cases record062_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record062_leaf_certificates_checked

noncomputable def record063_rawLeaves (j : Fin record063.l) : List Cell :=
  (record063.leaf j).map record063.data.cells
theorem record063_raw_exact (j : Fin record063.l) :
    (record063.leaf j).map record063.data.cells = record063_rawLeaves j := rfl
noncomputable def record063_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record063_certificates (j : Fin record063.l) : Certificate :=
  record063_certificateTable.get j.val
theorem record063_leaf_checked_0 :
    RawLeafCertificate.check record063.data.quota (record063_rawLeaves 0)
      (record063_certificates 0) = true := by
  change RawLeafCertificate.check record063.data.quota [] (.quota 1) = true
  exact empty_checked record063.data.quota 1 (by decide +kernel)
theorem record063_leaf_certificates_checked : ∀ j : Fin record063.l,
    RawLeafCertificate.check record063.data.quota (record063_rawLeaves j)
      (record063_certificates j) = true :=
  (Fin.cases record063_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record063_leaf_certificates_checked

noncomputable def record064_rawLeaves (j : Fin record064.l) : List Cell :=
  (record064.leaf j).map record064.data.cells
theorem record064_raw_exact (j : Fin record064.l) :
    (record064.leaf j).map record064.data.cells = record064_rawLeaves j := rfl
noncomputable def record064_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record064_certificates (j : Fin record064.l) : Certificate :=
  record064_certificateTable.get j.val
theorem record064_leaf_checked_0 :
    RawLeafCertificate.check record064.data.quota (record064_rawLeaves 0)
      (record064_certificates 0) = true := by
  change RawLeafCertificate.check record064.data.quota [] (.quota 1) = true
  exact empty_checked record064.data.quota 1 (by decide +kernel)
theorem record064_leaf_certificates_checked : ∀ j : Fin record064.l,
    RawLeafCertificate.check record064.data.quota (record064_rawLeaves j)
      (record064_certificates j) = true :=
  (Fin.cases record064_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record064_leaf_certificates_checked

noncomputable def record065_rawLeaves (j : Fin record065.l) : List Cell :=
  (record065.leaf j).map record065.data.cells
theorem record065_raw_exact (j : Fin record065.l) :
    (record065.leaf j).map record065.data.cells = record065_rawLeaves j := rfl
noncomputable def record065_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record065_certificates (j : Fin record065.l) : Certificate :=
  record065_certificateTable.get j.val
theorem record065_leaf_checked_0 :
    RawLeafCertificate.check record065.data.quota (record065_rawLeaves 0)
      (record065_certificates 0) = true := by
  change RawLeafCertificate.check record065.data.quota [] (.quota 1) = true
  exact empty_checked record065.data.quota 1 (by decide +kernel)
theorem record065_leaf_certificates_checked : ∀ j : Fin record065.l,
    RawLeafCertificate.check record065.data.quota (record065_rawLeaves j)
      (record065_certificates j) = true :=
  (Fin.cases record065_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record065_leaf_certificates_checked

noncomputable def record066_rawLeaves (j : Fin record066.l) : List Cell :=
  (record066.leaf j).map record066.data.cells
theorem record066_raw_exact (j : Fin record066.l) :
    (record066.leaf j).map record066.data.cells = record066_rawLeaves j := rfl
noncomputable def record066_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record066_certificates (j : Fin record066.l) : Certificate :=
  record066_certificateTable.get j.val
theorem record066_leaf_checked_0 :
    RawLeafCertificate.check record066.data.quota (record066_rawLeaves 0)
      (record066_certificates 0) = true := by
  change RawLeafCertificate.check record066.data.quota [] (.quota 1) = true
  exact empty_checked record066.data.quota 1 (by decide +kernel)
theorem record066_leaf_certificates_checked : ∀ j : Fin record066.l,
    RawLeafCertificate.check record066.data.quota (record066_rawLeaves j)
      (record066_certificates j) = true :=
  (Fin.cases record066_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record066_leaf_certificates_checked

noncomputable def record067_rawLeaves (j : Fin record067.l) : List Cell :=
  (record067.leaf j).map record067.data.cells
theorem record067_raw_exact (j : Fin record067.l) :
    (record067.leaf j).map record067.data.cells = record067_rawLeaves j := rfl
noncomputable def record067_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record067_certificates (j : Fin record067.l) : Certificate :=
  record067_certificateTable.get j.val
theorem record067_leaf_checked_0 :
    RawLeafCertificate.check record067.data.quota (record067_rawLeaves 0)
      (record067_certificates 0) = true := by
  change RawLeafCertificate.check record067.data.quota [] (.quota 1) = true
  exact empty_checked record067.data.quota 1 (by decide +kernel)
theorem record067_leaf_certificates_checked : ∀ j : Fin record067.l,
    RawLeafCertificate.check record067.data.quota (record067_rawLeaves j)
      (record067_certificates j) = true :=
  (Fin.cases record067_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record067_leaf_certificates_checked

noncomputable def record068_rawLeaves (j : Fin record068.l) : List Cell :=
  (record068.leaf j).map record068.data.cells
theorem record068_raw_exact (j : Fin record068.l) :
    (record068.leaf j).map record068.data.cells = record068_rawLeaves j := rfl
noncomputable def record068_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record068_certificates (j : Fin record068.l) : Certificate :=
  record068_certificateTable.get j.val
theorem record068_leaf_checked_0 :
    RawLeafCertificate.check record068.data.quota (record068_rawLeaves 0)
      (record068_certificates 0) = true := by
  change RawLeafCertificate.check record068.data.quota [] (.quota 1) = true
  exact empty_checked record068.data.quota 1 (by decide +kernel)
theorem record068_leaf_certificates_checked : ∀ j : Fin record068.l,
    RawLeafCertificate.check record068.data.quota (record068_rawLeaves j)
      (record068_certificates j) = true :=
  (Fin.cases record068_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record068_leaf_certificates_checked

noncomputable def record069_rawLeaves (j : Fin record069.l) : List Cell :=
  (record069.leaf j).map record069.data.cells
theorem record069_raw_exact (j : Fin record069.l) :
    (record069.leaf j).map record069.data.cells = record069_rawLeaves j := rfl
noncomputable def record069_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record069_certificates (j : Fin record069.l) : Certificate :=
  record069_certificateTable.get j.val
theorem record069_leaf_checked_0 :
    RawLeafCertificate.check record069.data.quota (record069_rawLeaves 0)
      (record069_certificates 0) = true := by
  change RawLeafCertificate.check record069.data.quota [] (.quota 1) = true
  exact empty_checked record069.data.quota 1 (by decide +kernel)
theorem record069_leaf_certificates_checked : ∀ j : Fin record069.l,
    RawLeafCertificate.check record069.data.quota (record069_rawLeaves j)
      (record069_certificates j) = true :=
  (Fin.cases record069_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record069_leaf_certificates_checked

noncomputable def record070_rawLeaves (j : Fin record070.l) : List Cell :=
  (record070.leaf j).map record070.data.cells
theorem record070_raw_exact (j : Fin record070.l) :
    (record070.leaf j).map record070.data.cells = record070_rawLeaves j := rfl
noncomputable def record070_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record070_certificates (j : Fin record070.l) : Certificate :=
  record070_certificateTable.get j.val
theorem record070_leaf_checked_0 :
    RawLeafCertificate.check record070.data.quota (record070_rawLeaves 0)
      (record070_certificates 0) = true := by
  change RawLeafCertificate.check record070.data.quota [] (.quota 1) = true
  exact empty_checked record070.data.quota 1 (by decide +kernel)
theorem record070_leaf_certificates_checked : ∀ j : Fin record070.l,
    RawLeafCertificate.check record070.data.quota (record070_rawLeaves j)
      (record070_certificates j) = true :=
  (Fin.cases record070_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record070_leaf_certificates_checked

noncomputable def record071_rawLeaves (j : Fin record071.l) : List Cell :=
  (record071.leaf j).map record071.data.cells
theorem record071_raw_exact (j : Fin record071.l) :
    (record071.leaf j).map record071.data.cells = record071_rawLeaves j := rfl
noncomputable def record071_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record071_certificates (j : Fin record071.l) : Certificate :=
  record071_certificateTable.get j.val
theorem record071_leaf_checked_0 :
    RawLeafCertificate.check record071.data.quota (record071_rawLeaves 0)
      (record071_certificates 0) = true := by
  change RawLeafCertificate.check record071.data.quota [] (.quota 1) = true
  exact empty_checked record071.data.quota 1 (by decide +kernel)
theorem record071_leaf_certificates_checked : ∀ j : Fin record071.l,
    RawLeafCertificate.check record071.data.quota (record071_rawLeaves j)
      (record071_certificates j) = true :=
  (Fin.cases record071_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record071_leaf_certificates_checked

noncomputable def record072_rawLeaves (j : Fin record072.l) : List Cell :=
  (record072.leaf j).map record072.data.cells
theorem record072_raw_exact (j : Fin record072.l) :
    (record072.leaf j).map record072.data.cells = record072_rawLeaves j := rfl
noncomputable def record072_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record072_certificates (j : Fin record072.l) : Certificate :=
  record072_certificateTable.get j.val
theorem record072_leaf_checked_0 :
    RawLeafCertificate.check record072.data.quota (record072_rawLeaves 0)
      (record072_certificates 0) = true := by
  change RawLeafCertificate.check record072.data.quota [] (.quota 1) = true
  exact empty_checked record072.data.quota 1 (by decide +kernel)
theorem record072_leaf_certificates_checked : ∀ j : Fin record072.l,
    RawLeafCertificate.check record072.data.quota (record072_rawLeaves j)
      (record072_certificates j) = true :=
  (Fin.cases record072_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record072_leaf_certificates_checked

noncomputable def record073_rawLeaves (j : Fin record073.l) : List Cell :=
  (record073.leaf j).map record073.data.cells
theorem record073_raw_exact (j : Fin record073.l) :
    (record073.leaf j).map record073.data.cells = record073_rawLeaves j := rfl
noncomputable def record073_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record073_certificates (j : Fin record073.l) : Certificate :=
  record073_certificateTable.get j.val
theorem record073_leaf_checked_0 :
    RawLeafCertificate.check record073.data.quota (record073_rawLeaves 0)
      (record073_certificates 0) = true := by
  change RawLeafCertificate.check record073.data.quota [] (.quota 1) = true
  exact empty_checked record073.data.quota 1 (by decide +kernel)
theorem record073_leaf_certificates_checked : ∀ j : Fin record073.l,
    RawLeafCertificate.check record073.data.quota (record073_rawLeaves j)
      (record073_certificates j) = true :=
  (Fin.cases record073_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record073_leaf_certificates_checked

noncomputable def record074_rawLeaves (j : Fin record074.l) : List Cell :=
  (record074.leaf j).map record074.data.cells
theorem record074_raw_exact (j : Fin record074.l) :
    (record074.leaf j).map record074.data.cells = record074_rawLeaves j := rfl
noncomputable def record074_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record074_certificates (j : Fin record074.l) : Certificate :=
  record074_certificateTable.get j.val
theorem record074_leaf_checked_0 :
    RawLeafCertificate.check record074.data.quota (record074_rawLeaves 0)
      (record074_certificates 0) = true := by
  change RawLeafCertificate.check record074.data.quota [] (.quota 1) = true
  exact empty_checked record074.data.quota 1 (by decide +kernel)
theorem record074_leaf_certificates_checked : ∀ j : Fin record074.l,
    RawLeafCertificate.check record074.data.quota (record074_rawLeaves j)
      (record074_certificates j) = true :=
  (Fin.cases record074_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record074_leaf_certificates_checked

noncomputable def record075_rawLeaves (j : Fin record075.l) : List Cell :=
  (record075.leaf j).map record075.data.cells
theorem record075_raw_exact (j : Fin record075.l) :
    (record075.leaf j).map record075.data.cells = record075_rawLeaves j := rfl
noncomputable def record075_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record075_certificates (j : Fin record075.l) : Certificate :=
  record075_certificateTable.get j.val
theorem record075_leaf_checked_0 :
    RawLeafCertificate.check record075.data.quota (record075_rawLeaves 0)
      (record075_certificates 0) = true := by
  change RawLeafCertificate.check record075.data.quota [] (.quota 1) = true
  exact empty_checked record075.data.quota 1 (by decide +kernel)
theorem record075_leaf_certificates_checked : ∀ j : Fin record075.l,
    RawLeafCertificate.check record075.data.quota (record075_rawLeaves j)
      (record075_certificates j) = true :=
  (Fin.cases record075_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record075_leaf_certificates_checked

noncomputable def record076_rawLeaves (j : Fin record076.l) : List Cell :=
  (record076.leaf j).map record076.data.cells
theorem record076_raw_exact (j : Fin record076.l) :
    (record076.leaf j).map record076.data.cells = record076_rawLeaves j := rfl
noncomputable def record076_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record076_certificates (j : Fin record076.l) : Certificate :=
  record076_certificateTable.get j.val
theorem record076_leaf_checked_0 :
    RawLeafCertificate.check record076.data.quota (record076_rawLeaves 0)
      (record076_certificates 0) = true := by
  change RawLeafCertificate.check record076.data.quota [] (.quota 1) = true
  exact empty_checked record076.data.quota 1 (by decide +kernel)
theorem record076_leaf_certificates_checked : ∀ j : Fin record076.l,
    RawLeafCertificate.check record076.data.quota (record076_rawLeaves j)
      (record076_certificates j) = true :=
  (Fin.cases record076_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record076_leaf_certificates_checked

noncomputable def record077_rawLeaves (j : Fin record077.l) : List Cell :=
  (record077.leaf j).map record077.data.cells
theorem record077_raw_exact (j : Fin record077.l) :
    (record077.leaf j).map record077.data.cells = record077_rawLeaves j := rfl
noncomputable def record077_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record077_certificates (j : Fin record077.l) : Certificate :=
  record077_certificateTable.get j.val
theorem record077_leaf_checked_0 :
    RawLeafCertificate.check record077.data.quota (record077_rawLeaves 0)
      (record077_certificates 0) = true := by
  change RawLeafCertificate.check record077.data.quota [] (.quota 1) = true
  exact empty_checked record077.data.quota 1 (by decide +kernel)
theorem record077_leaf_certificates_checked : ∀ j : Fin record077.l,
    RawLeafCertificate.check record077.data.quota (record077_rawLeaves j)
      (record077_certificates j) = true :=
  (Fin.cases record077_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record077_leaf_certificates_checked

noncomputable def record078_rawLeaves (j : Fin record078.l) : List Cell :=
  (record078.leaf j).map record078.data.cells
theorem record078_raw_exact (j : Fin record078.l) :
    (record078.leaf j).map record078.data.cells = record078_rawLeaves j := rfl
noncomputable def record078_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record078_certificates (j : Fin record078.l) : Certificate :=
  record078_certificateTable.get j.val
theorem record078_leaf_checked_0 :
    RawLeafCertificate.check record078.data.quota (record078_rawLeaves 0)
      (record078_certificates 0) = true := by
  change RawLeafCertificate.check record078.data.quota [] (.quota 1) = true
  exact empty_checked record078.data.quota 1 (by decide +kernel)
theorem record078_leaf_certificates_checked : ∀ j : Fin record078.l,
    RawLeafCertificate.check record078.data.quota (record078_rawLeaves j)
      (record078_certificates j) = true :=
  (Fin.cases record078_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record078_leaf_certificates_checked

noncomputable def record079_rawLeaves (j : Fin record079.l) : List Cell :=
  (record079.leaf j).map record079.data.cells
theorem record079_raw_exact (j : Fin record079.l) :
    (record079.leaf j).map record079.data.cells = record079_rawLeaves j := rfl
noncomputable def record079_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record079_certificates (j : Fin record079.l) : Certificate :=
  record079_certificateTable.get j.val
theorem record079_leaf_checked_0 :
    RawLeafCertificate.check record079.data.quota (record079_rawLeaves 0)
      (record079_certificates 0) = true := by
  change RawLeafCertificate.check record079.data.quota [] (.quota 1) = true
  exact empty_checked record079.data.quota 1 (by decide +kernel)
theorem record079_leaf_certificates_checked : ∀ j : Fin record079.l,
    RawLeafCertificate.check record079.data.quota (record079_rawLeaves j)
      (record079_certificates j) = true :=
  (Fin.cases record079_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record079_leaf_certificates_checked

noncomputable def record080_rawLeaves (j : Fin record080.l) : List Cell :=
  (record080.leaf j).map record080.data.cells
theorem record080_raw_exact (j : Fin record080.l) :
    (record080.leaf j).map record080.data.cells = record080_rawLeaves j := rfl
noncomputable def record080_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record080_certificates (j : Fin record080.l) : Certificate :=
  record080_certificateTable.get j.val
theorem record080_leaf_checked_0 :
    RawLeafCertificate.check record080.data.quota (record080_rawLeaves 0)
      (record080_certificates 0) = true := by
  change RawLeafCertificate.check record080.data.quota [] (.quota 1) = true
  exact empty_checked record080.data.quota 1 (by decide +kernel)
theorem record080_leaf_certificates_checked : ∀ j : Fin record080.l,
    RawLeafCertificate.check record080.data.quota (record080_rawLeaves j)
      (record080_certificates j) = true :=
  (Fin.cases record080_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record080_leaf_certificates_checked

noncomputable def record081_rawLeaves (j : Fin record081.l) : List Cell :=
  (record081.leaf j).map record081.data.cells
theorem record081_raw_exact (j : Fin record081.l) :
    (record081.leaf j).map record081.data.cells = record081_rawLeaves j := rfl
noncomputable def record081_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record081_certificates (j : Fin record081.l) : Certificate :=
  record081_certificateTable.get j.val
theorem record081_leaf_checked_0 :
    RawLeafCertificate.check record081.data.quota (record081_rawLeaves 0)
      (record081_certificates 0) = true := by
  change RawLeafCertificate.check record081.data.quota [] (.quota 1) = true
  exact empty_checked record081.data.quota 1 (by decide +kernel)
theorem record081_leaf_certificates_checked : ∀ j : Fin record081.l,
    RawLeafCertificate.check record081.data.quota (record081_rawLeaves j)
      (record081_certificates j) = true :=
  (Fin.cases record081_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record081_leaf_certificates_checked

noncomputable def record082_rawLeaves (j : Fin record082.l) : List Cell :=
  (record082.leaf j).map record082.data.cells
theorem record082_raw_exact (j : Fin record082.l) :
    (record082.leaf j).map record082.data.cells = record082_rawLeaves j := rfl
noncomputable def record082_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record082_certificates (j : Fin record082.l) : Certificate :=
  record082_certificateTable.get j.val
theorem record082_leaf_checked_0 :
    RawLeafCertificate.check record082.data.quota (record082_rawLeaves 0)
      (record082_certificates 0) = true := by
  change RawLeafCertificate.check record082.data.quota [] (.quota 1) = true
  exact empty_checked record082.data.quota 1 (by decide +kernel)
theorem record082_leaf_certificates_checked : ∀ j : Fin record082.l,
    RawLeafCertificate.check record082.data.quota (record082_rawLeaves j)
      (record082_certificates j) = true :=
  (Fin.cases record082_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record082_leaf_certificates_checked

noncomputable def record083_rawLeaves (j : Fin record083.l) : List Cell :=
  (record083.leaf j).map record083.data.cells
theorem record083_raw_exact (j : Fin record083.l) :
    (record083.leaf j).map record083.data.cells = record083_rawLeaves j := rfl
noncomputable def record083_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record083_certificates (j : Fin record083.l) : Certificate :=
  record083_certificateTable.get j.val
theorem record083_leaf_checked_0 :
    RawLeafCertificate.check record083.data.quota (record083_rawLeaves 0)
      (record083_certificates 0) = true := by
  change RawLeafCertificate.check record083.data.quota [] (.quota 1) = true
  exact empty_checked record083.data.quota 1 (by decide +kernel)
theorem record083_leaf_certificates_checked : ∀ j : Fin record083.l,
    RawLeafCertificate.check record083.data.quota (record083_rawLeaves j)
      (record083_certificates j) = true :=
  (Fin.cases record083_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record083_leaf_certificates_checked

noncomputable def record084_rawLeaves (j : Fin record084.l) : List Cell :=
  (record084.leaf j).map record084.data.cells
theorem record084_raw_exact (j : Fin record084.l) :
    (record084.leaf j).map record084.data.cells = record084_rawLeaves j := rfl
noncomputable def record084_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record084_certificates (j : Fin record084.l) : Certificate :=
  record084_certificateTable.get j.val
theorem record084_leaf_checked_0 :
    RawLeafCertificate.check record084.data.quota (record084_rawLeaves 0)
      (record084_certificates 0) = true := by
  change RawLeafCertificate.check record084.data.quota [] (.quota 1) = true
  exact empty_checked record084.data.quota 1 (by decide +kernel)
theorem record084_leaf_certificates_checked : ∀ j : Fin record084.l,
    RawLeafCertificate.check record084.data.quota (record084_rawLeaves j)
      (record084_certificates j) = true :=
  (Fin.cases record084_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record084_leaf_certificates_checked

noncomputable def record085_rawLeaves (j : Fin record085.l) : List Cell :=
  (record085.leaf j).map record085.data.cells
theorem record085_raw_exact (j : Fin record085.l) :
    (record085.leaf j).map record085.data.cells = record085_rawLeaves j := rfl
noncomputable def record085_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record085_certificates (j : Fin record085.l) : Certificate :=
  record085_certificateTable.get j.val
theorem record085_leaf_checked_0 :
    RawLeafCertificate.check record085.data.quota (record085_rawLeaves 0)
      (record085_certificates 0) = true := by
  change RawLeafCertificate.check record085.data.quota [] (.quota 1) = true
  exact empty_checked record085.data.quota 1 (by decide +kernel)
theorem record085_leaf_certificates_checked : ∀ j : Fin record085.l,
    RawLeafCertificate.check record085.data.quota (record085_rawLeaves j)
      (record085_certificates j) = true :=
  (Fin.cases record085_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record085_leaf_certificates_checked

noncomputable def record086_rawLeaves (j : Fin record086.l) : List Cell :=
  (record086.leaf j).map record086.data.cells
theorem record086_raw_exact (j : Fin record086.l) :
    (record086.leaf j).map record086.data.cells = record086_rawLeaves j := rfl
noncomputable def record086_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record086_certificates (j : Fin record086.l) : Certificate :=
  record086_certificateTable.get j.val
theorem record086_leaf_checked_0 :
    RawLeafCertificate.check record086.data.quota (record086_rawLeaves 0)
      (record086_certificates 0) = true := by
  change RawLeafCertificate.check record086.data.quota [] (.quota 1) = true
  exact empty_checked record086.data.quota 1 (by decide +kernel)
theorem record086_leaf_certificates_checked : ∀ j : Fin record086.l,
    RawLeafCertificate.check record086.data.quota (record086_rawLeaves j)
      (record086_certificates j) = true :=
  (Fin.cases record086_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record086_leaf_certificates_checked

noncomputable def record087_rawLeaves (j : Fin record087.l) : List Cell :=
  (record087.leaf j).map record087.data.cells
theorem record087_raw_exact (j : Fin record087.l) :
    (record087.leaf j).map record087.data.cells = record087_rawLeaves j := rfl
noncomputable def record087_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record087_certificates (j : Fin record087.l) : Certificate :=
  record087_certificateTable.get j.val
theorem record087_leaf_checked_0 :
    RawLeafCertificate.check record087.data.quota (record087_rawLeaves 0)
      (record087_certificates 0) = true := by
  change RawLeafCertificate.check record087.data.quota [] (.quota 1) = true
  exact empty_checked record087.data.quota 1 (by decide +kernel)
theorem record087_leaf_certificates_checked : ∀ j : Fin record087.l,
    RawLeafCertificate.check record087.data.quota (record087_rawLeaves j)
      (record087_certificates j) = true :=
  (Fin.cases record087_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record087_leaf_certificates_checked

noncomputable def record088_rawLeaves (j : Fin record088.l) : List Cell :=
  (record088.leaf j).map record088.data.cells
theorem record088_raw_exact (j : Fin record088.l) :
    (record088.leaf j).map record088.data.cells = record088_rawLeaves j := rfl
noncomputable def record088_certificateTable : Table Certificate :=
(.leaf (.quota 1))
noncomputable def record088_certificates (j : Fin record088.l) : Certificate :=
  record088_certificateTable.get j.val
theorem record088_leaf_checked_0 :
    RawLeafCertificate.check record088.data.quota (record088_rawLeaves 0)
      (record088_certificates 0) = true := by
  change RawLeafCertificate.check record088.data.quota [] (.quota 1) = true
  exact empty_checked record088.data.quota 1 (by decide +kernel)
theorem record088_leaf_certificates_checked : ∀ j : Fin record088.l,
    RawLeafCertificate.check record088.data.quota (record088_rawLeaves j)
      (record088_certificates j) = true :=
  (Fin.cases record088_leaf_checked_0 (fun j => Fin.elim0 j))
#print axioms record088_leaf_certificates_checked
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00007
