module
prelude
public import GraphInputsRow24Part00046Data
public import FastRawLeafCertificate

@[expose] public section
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00046
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
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00046
