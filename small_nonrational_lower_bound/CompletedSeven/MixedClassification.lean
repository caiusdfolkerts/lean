module

public import CompletedRooted.Case0000
public import CompletedRooted.Case0022
public import CompletedSeven.Certificates
public import CompletedSeven.MixedCoverage
public import IdentityGrowthRenaming
public import PackedSevenMixed001Classification
public import PackedSevenMixed001Dispositions
public import PackedSevenMixed002Classification
public import PackedSevenMixed002Dispositions
public import PackedSevenMixed003Classification
public import PackedSevenMixed003Dispositions
public import PackedSevenMixed004Classification
public import PackedSevenMixed004Dispositions
public import PackedSevenMixed005Classification
public import PackedSevenMixed005Dispositions
public import PackedSevenMixed006Classification
public import PackedSevenMixed006Dispositions
public import PackedSevenMixed007Classification
public import PackedSevenMixed007Dispositions
public import PackedSevenMixed008Classification
public import PackedSevenMixed008Dispositions
public import PackedSevenMixed009Classification
public import PackedSevenMixed009Dispositions
public import PackedSevenMixed010Classification
public import PackedSevenMixed010Dispositions
public import PackedSevenMixed011Classification
public import PackedSevenMixed011Dispositions
public import PackedSevenMixed012Classification
public import PackedSevenMixed012Dispositions
public import PackedSevenMixed013Classification
public import PackedSevenMixed013Dispositions
public import PackedSevenMixed014Classification
public import PackedSevenMixed014Dispositions
public import PackedSevenMixed015Classification
public import PackedSevenMixed015Dispositions
public import PackedSevenMixed016Classification
public import PackedSevenMixed016Dispositions
public import PackedSevenMixed017Classification
public import PackedSevenMixed017Dispositions
public import PackedSevenMixed018Classification
public import PackedSevenMixed018Dispositions
public import PackedSevenMixed019Classification
public import PackedSevenMixed019Dispositions
public import PackedSevenMixed020Classification
public import PackedSevenMixed020Dispositions
public import PackedSevenMixed021Classification
public import PackedSevenMixed021Dispositions
public import RootedFamilyClosure
public import RootedRawForest0023
public import RootedRawForest0023Dispositions
public import RootedRawForest0024
public import RootedRawForest0024Dispositions
public import RootedRawForest0025
public import RootedRawForest0025Dispositions
public import RootedRawForest0026
public import RootedRawForest0026Dispositions
public import RootedRawForest0027
public import RootedRawForest0027Dispositions
public import RootedRawForest0028
public import RootedRawForest0028Dispositions
public import RootedRawForest0029
public import RootedRawForest0029Dispositions
public import RootedRawForest0030
public import RootedRawForest0030Dispositions
public import RootedRawForest0031
public import RootedRawForest0031Dispositions
public import RootedRawForest0032
public import RootedRawForest0032Dispositions
public import RootedRawForest0033
public import RootedRawForest0033Dispositions
public import RootedSevenMixed001WellFormed
public import RootedSevenMixed002WellFormed
public import RootedSevenMixed003WellFormed
public import RootedSevenMixed004WellFormed
public import RootedSevenMixed005WellFormed
public import RootedSevenMixed006WellFormed
public import RootedSevenMixed007WellFormed
public import RootedSevenMixed008WellFormed
public import RootedSevenMixed009WellFormed
public import RootedSevenMixed010WellFormed
public import RootedSevenMixed011WellFormed
public import RootedSevenMixed012WellFormed
public import RootedSevenMixed013WellFormed
public import RootedSevenMixed014WellFormed
public import RootedSevenMixed015WellFormed
public import RootedSevenMixed016WellFormed
public import RootedSevenMixed017WellFormed
public import RootedSevenMixed018WellFormed
public import RootedSevenMixed019WellFormed
public import RootedSevenMixed020WellFormed
public import RootedSevenMixed021WellFormed


/-! Complete placement, finite classification, and row certificates.
Each source section below retains its original mathematical declarations. -/

/- Source module: CompletedRooted.Case0001 -/
@[expose] public section

/-! Exact finite classification for rooted case 1.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0001

open PackedReplay.PackedSevenMixed001
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenMixed001.cells =
      (rawLeaves j.val).map PackedReplay.PackedSevenMixed001.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed001.cells =
        ((leaves j).map Fin.val).map PackedReplay.PackedSevenMixed001.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map PackedReplay.PackedSevenMixed001.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed001.cells quota (0 : Fin 646) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed001.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed001.well_formed i))
    leaves (fun j => (rawLeaves j.val).map PackedReplay.PackedSevenMixed001.rawCells)
    raw_leaves_exact disposition disposition_checked boundary_classification_nodup

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0001

end
end

/- Source module: CompletedRooted.Case0002 -/
@[expose] public section

/-! Exact finite classification for rooted case 2.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0002

open PackedReplay.PackedSevenMixed002
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenMixed002.cells =
      (rawLeaves j.val).map PackedReplay.PackedSevenMixed002.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed002.cells =
        ((leaves j).map Fin.val).map PackedReplay.PackedSevenMixed002.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map PackedReplay.PackedSevenMixed002.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed002.cells quota (0 : Fin 646) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed002.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed002.well_formed i))
    leaves (fun j => (rawLeaves j.val).map PackedReplay.PackedSevenMixed002.rawCells)
    raw_leaves_exact disposition disposition_checked boundary_classification_nodup

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0002

end
end

/- Source module: CompletedRooted.Case0003 -/
@[expose] public section

/-! Exact finite classification for rooted case 3.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0003

open PackedReplay.PackedSevenMixed003
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenMixed003.cells =
      (rawLeaves j.val).map PackedReplay.PackedSevenMixed003.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed003.cells =
        ((leaves j).map Fin.val).map PackedReplay.PackedSevenMixed003.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map PackedReplay.PackedSevenMixed003.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed003.cells quota (0 : Fin 646) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed003.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed003.well_formed i))
    leaves (fun j => (rawLeaves j.val).map PackedReplay.PackedSevenMixed003.rawCells)
    raw_leaves_exact disposition disposition_checked boundary_classification_nodup

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0003

end
end

/- Source module: CompletedRooted.Case0004 -/
@[expose] public section

/-! Exact finite classification for rooted case 4.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0004

open PackedReplay.PackedSevenMixed004
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenMixed004.cells =
      (rawLeaves j.val).map PackedReplay.PackedSevenMixed004.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed004.cells =
        ((leaves j).map Fin.val).map PackedReplay.PackedSevenMixed004.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map PackedReplay.PackedSevenMixed004.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed004.cells quota (0 : Fin 646) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed004.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed004.well_formed i))
    leaves (fun j => (rawLeaves j.val).map PackedReplay.PackedSevenMixed004.rawCells)
    raw_leaves_exact disposition disposition_checked boundary_classification_nodup

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0004

end
end

/- Source module: CompletedRooted.Case0005 -/
@[expose] public section

/-! Exact finite classification for rooted case 5.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0005

open PackedReplay.PackedSevenMixed005
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenMixed005.cells =
      (rawLeaves j.val).map PackedReplay.PackedSevenMixed005.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed005.cells =
        ((leaves j).map Fin.val).map PackedReplay.PackedSevenMixed005.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map PackedReplay.PackedSevenMixed005.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed005.cells quota (0 : Fin 646) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed005.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed005.well_formed i))
    leaves (fun j => (rawLeaves j.val).map PackedReplay.PackedSevenMixed005.rawCells)
    raw_leaves_exact disposition disposition_checked boundary_classification_nodup

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0005

end
end

/- Source module: CompletedRooted.Case0006 -/
@[expose] public section

/-! Exact finite classification for rooted case 6.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0006

open PackedReplay.PackedSevenMixed006
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenMixed006.cells =
      (rawLeaves j.val).map PackedReplay.PackedSevenMixed006.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed006.cells =
        ((leaves j).map Fin.val).map PackedReplay.PackedSevenMixed006.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map PackedReplay.PackedSevenMixed006.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed006.cells quota (0 : Fin 556) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed006.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed006.well_formed i))
    leaves (fun j => (rawLeaves j.val).map PackedReplay.PackedSevenMixed006.rawCells)
    raw_leaves_exact disposition disposition_checked boundary_classification_nodup

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0006

end
end

/- Source module: CompletedRooted.Case0007 -/
@[expose] public section

/-! Exact finite classification for rooted case 7.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0007

open PackedReplay.PackedSevenMixed007
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenMixed007.cells =
      (rawLeaves j.val).map PackedReplay.PackedSevenMixed007.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed007.cells =
        ((leaves j).map Fin.val).map PackedReplay.PackedSevenMixed007.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map PackedReplay.PackedSevenMixed007.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed007.cells quota (0 : Fin 556) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed007.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed007.well_formed i))
    leaves (fun j => (rawLeaves j.val).map PackedReplay.PackedSevenMixed007.rawCells)
    raw_leaves_exact disposition disposition_checked boundary_classification_nodup

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0007

end
end

/- Source module: CompletedRooted.Case0008 -/
@[expose] public section

/-! Exact finite classification for rooted case 8.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0008

open PackedReplay.PackedSevenMixed008
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenMixed008.cells =
      (rawLeaves j.val).map PackedReplay.PackedSevenMixed008.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed008.cells =
        ((leaves j).map Fin.val).map PackedReplay.PackedSevenMixed008.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map PackedReplay.PackedSevenMixed008.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed008.cells quota (0 : Fin 694) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed008.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed008.well_formed i))
    leaves (fun j => (rawLeaves j.val).map PackedReplay.PackedSevenMixed008.rawCells)
    raw_leaves_exact disposition disposition_checked boundary_classification_nodup

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0008

end
end

/- Source module: CompletedRooted.Case0009 -/
@[expose] public section

/-! Exact finite classification for rooted case 9.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0009

open PackedReplay.PackedSevenMixed009
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenMixed009.cells =
      (rawLeaves j.val).map PackedReplay.PackedSevenMixed009.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed009.cells =
        ((leaves j).map Fin.val).map PackedReplay.PackedSevenMixed009.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map PackedReplay.PackedSevenMixed009.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed009.cells quota (0 : Fin 910) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed009.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed009.well_formed i))
    leaves (fun j => (rawLeaves j.val).map PackedReplay.PackedSevenMixed009.rawCells)
    raw_leaves_exact disposition disposition_checked boundary_classification_nodup

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0009

end
end

/- Source module: CompletedRooted.Case0010 -/
@[expose] public section

/-! Exact finite classification for rooted case 10.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0010

open PackedReplay.PackedSevenMixed010
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenMixed010.cells =
      (rawLeaves j.val).map PackedReplay.PackedSevenMixed010.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed010.cells =
        ((leaves j).map Fin.val).map PackedReplay.PackedSevenMixed010.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map PackedReplay.PackedSevenMixed010.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed010.cells quota (0 : Fin 430) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed010.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed010.well_formed i))
    leaves (fun j => (rawLeaves j.val).map PackedReplay.PackedSevenMixed010.rawCells)
    raw_leaves_exact disposition disposition_checked boundary_classification_nodup

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0010

end
end

/- Source module: CompletedRooted.Case0011 -/
@[expose] public section

/-! Exact finite classification for rooted case 11.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0011

open PackedReplay.PackedSevenMixed011
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenMixed011.cells =
      (rawLeaves j.val).map PackedReplay.PackedSevenMixed011.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed011.cells =
        ((leaves j).map Fin.val).map PackedReplay.PackedSevenMixed011.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map PackedReplay.PackedSevenMixed011.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed011.cells quota (0 : Fin 658) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed011.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed011.well_formed i))
    leaves (fun j => (rawLeaves j.val).map PackedReplay.PackedSevenMixed011.rawCells)
    raw_leaves_exact disposition disposition_checked boundary_classification_nodup

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0011

end
end

/- Source module: CompletedRooted.Case0012 -/
@[expose] public section

/-! Exact finite classification for rooted case 12.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0012

open PackedReplay.PackedSevenMixed012
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenMixed012.cells =
      (rawLeaves j.val).map PackedReplay.PackedSevenMixed012.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed012.cells =
        ((leaves j).map Fin.val).map PackedReplay.PackedSevenMixed012.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map PackedReplay.PackedSevenMixed012.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed012.cells quota (0 : Fin 838) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed012.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed012.well_formed i))
    leaves (fun j => (rawLeaves j.val).map PackedReplay.PackedSevenMixed012.rawCells)
    raw_leaves_exact disposition disposition_checked boundary_classification_nodup

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0012

end
end

/- Source module: CompletedRooted.Case0013 -/
@[expose] public section

/-! Exact finite classification for rooted case 13.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0013

open PackedReplay.PackedSevenMixed013
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenMixed013.cells =
      (rawLeaves j.val).map PackedReplay.PackedSevenMixed013.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed013.cells =
        ((leaves j).map Fin.val).map PackedReplay.PackedSevenMixed013.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map PackedReplay.PackedSevenMixed013.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed013.cells quota (0 : Fin 466) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed013.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed013.well_formed i))
    leaves (fun j => (rawLeaves j.val).map PackedReplay.PackedSevenMixed013.rawCells)
    raw_leaves_exact disposition disposition_checked boundary_classification_nodup

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0013

end
end

/- Source module: CompletedRooted.Case0014 -/
@[expose] public section

/-! Exact finite classification for rooted case 14.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0014

open PackedReplay.PackedSevenMixed014
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenMixed014.cells =
      (rawLeaves j.val).map PackedReplay.PackedSevenMixed014.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed014.cells =
        ((leaves j).map Fin.val).map PackedReplay.PackedSevenMixed014.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map PackedReplay.PackedSevenMixed014.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed014.cells quota (0 : Fin 466) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed014.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed014.well_formed i))
    leaves (fun j => (rawLeaves j.val).map PackedReplay.PackedSevenMixed014.rawCells)
    raw_leaves_exact disposition disposition_checked boundary_classification_nodup

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0014

end
end

/- Source module: CompletedRooted.Case0015 -/
@[expose] public section

/-! Exact finite classification for rooted case 15.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0015

open PackedReplay.PackedSevenMixed015
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 18) :
    (leaves j).map FacetUniverses.RootedSevenMixed015.cells =
      (rawLeaves j.val).map PackedReplay.PackedSevenMixed015.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed015.cells =
        ((leaves j).map Fin.val).map PackedReplay.PackedSevenMixed015.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map PackedReplay.PackedSevenMixed015.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed015.cells quota (0 : Fin 521) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed015.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed015.well_formed i))
    leaves (fun j => (rawLeaves j.val).map PackedReplay.PackedSevenMixed015.rawCells)
    raw_leaves_exact disposition disposition_checked boundary_classification_nodup

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0015

end
end

/- Source module: CompletedRooted.Case0016 -/
@[expose] public section

/-! Exact finite classification for rooted case 16.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0016

open PackedReplay.PackedSevenMixed016
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenMixed016.cells =
      (rawLeaves j.val).map PackedReplay.PackedSevenMixed016.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed016.cells =
        ((leaves j).map Fin.val).map PackedReplay.PackedSevenMixed016.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map PackedReplay.PackedSevenMixed016.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed016.cells quota (0 : Fin 646) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed016.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed016.well_formed i))
    leaves (fun j => (rawLeaves j.val).map PackedReplay.PackedSevenMixed016.rawCells)
    raw_leaves_exact disposition disposition_checked boundary_classification_nodup

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0016

end
end

/- Source module: CompletedRooted.Case0017 -/
@[expose] public section

/-! Exact finite classification for rooted case 17.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0017

open PackedReplay.PackedSevenMixed017
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenMixed017.cells =
      (rawLeaves j.val).map PackedReplay.PackedSevenMixed017.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed017.cells =
        ((leaves j).map Fin.val).map PackedReplay.PackedSevenMixed017.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map PackedReplay.PackedSevenMixed017.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed017.cells quota (0 : Fin 646) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed017.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed017.well_formed i))
    leaves (fun j => (rawLeaves j.val).map PackedReplay.PackedSevenMixed017.rawCells)
    raw_leaves_exact disposition disposition_checked boundary_classification_nodup

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0017

end
end

/- Source module: CompletedRooted.Case0018 -/
@[expose] public section

/-! Exact finite classification for rooted case 18.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0018

open PackedReplay.PackedSevenMixed018
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenMixed018.cells =
      (rawLeaves j.val).map PackedReplay.PackedSevenMixed018.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed018.cells =
        ((leaves j).map Fin.val).map PackedReplay.PackedSevenMixed018.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map PackedReplay.PackedSevenMixed018.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed018.cells quota (0 : Fin 556) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed018.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed018.well_formed i))
    leaves (fun j => (rawLeaves j.val).map PackedReplay.PackedSevenMixed018.rawCells)
    raw_leaves_exact disposition disposition_checked boundary_classification_nodup

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0018

end
end

/- Source module: CompletedRooted.Case0019 -/
@[expose] public section

/-! Exact finite classification for rooted case 19.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0019

open PackedReplay.PackedSevenMixed019
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenMixed019.cells =
      (rawLeaves j.val).map PackedReplay.PackedSevenMixed019.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed019.cells =
        ((leaves j).map Fin.val).map PackedReplay.PackedSevenMixed019.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map PackedReplay.PackedSevenMixed019.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed019.cells quota (0 : Fin 556) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed019.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed019.well_formed i))
    leaves (fun j => (rawLeaves j.val).map PackedReplay.PackedSevenMixed019.rawCells)
    raw_leaves_exact disposition disposition_checked boundary_classification_nodup

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0019

end
end

/- Source module: CompletedRooted.Case0020 -/
@[expose] public section

/-! Exact finite classification for rooted case 20.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0020

open PackedReplay.PackedSevenMixed020
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenMixed020.cells =
      (rawLeaves j.val).map PackedReplay.PackedSevenMixed020.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed020.cells =
        ((leaves j).map Fin.val).map PackedReplay.PackedSevenMixed020.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map PackedReplay.PackedSevenMixed020.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed020.cells quota (0 : Fin 556) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed020.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed020.well_formed i))
    leaves (fun j => (rawLeaves j.val).map PackedReplay.PackedSevenMixed020.rawCells)
    raw_leaves_exact disposition disposition_checked boundary_classification_nodup

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0020

end
end

/- Source module: CompletedRooted.Case0021 -/
@[expose] public section

/-! Exact finite classification for rooted case 21.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0021

open PackedReplay.PackedSevenMixed021
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenMixed021.cells =
      (rawLeaves j.val).map PackedReplay.PackedSevenMixed021.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed021.cells =
        ((leaves j).map Fin.val).map PackedReplay.PackedSevenMixed021.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map PackedReplay.PackedSevenMixed021.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed021.cells quota (0 : Fin 556) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed021.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed021.well_formed i))
    leaves (fun j => (rawLeaves j.val).map PackedReplay.PackedSevenMixed021.rawCells)
    raw_leaves_exact disposition disposition_checked boundary_classification_nodup

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0021

end
end

/- Source module: CompletedRooted.Case0023 -/
@[expose] public section

/-! Exact finite classification for rooted case 23.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0023

open RootedForests.RootedRawForest0023
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenMixed023.cells =
      (rawLeaves j.val).map RootedCaches.RootedSevenMixed023.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed023.cells =
        ((leaves j).map Fin.val).map RootedCaches.RootedSevenMixed023.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedCaches.RootedSevenMixed023.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed023.cells quota (0 : Fin 556) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed023.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed023.well_formed i))
    leaves (fun j => (rawLeaves j.val).map RootedCaches.RootedSevenMixed023.rawCells)
    raw_leaves_exact disposition disposition_checked (by
      intro B hB hroot
      obtain ⟨j, word, hnodup, hsame⟩ := boundary_classification
        (fun _ => GrowthRenaming.Renaming.identity
          (fun c => SparseGrowthDAG.has (FacetUniverses.RootedSevenMixed023.ridgeList c))
          FacetUniverses.RootedSevenMixed023.literalCompatible FacetUniverses.RootedSevenMixed023.kind)
        (fun _ _ => rfl) B hB hroot
      refine ⟨j, hnodup, ?_⟩
      simpa only [GrowthRenaming.applyWord_identity] using hsame)

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0023

end
end

/- Source module: CompletedRooted.Case0024 -/
@[expose] public section

/-! Exact finite classification for rooted case 24.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0024

open RootedForests.RootedRawForest0024
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenMixed024.cells =
      (rawLeaves j.val).map RootedCaches.RootedSevenMixed024.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed024.cells =
        ((leaves j).map Fin.val).map RootedCaches.RootedSevenMixed024.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedCaches.RootedSevenMixed024.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed024.cells quota (0 : Fin 466) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed024.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed024.well_formed i))
    leaves (fun j => (rawLeaves j.val).map RootedCaches.RootedSevenMixed024.rawCells)
    raw_leaves_exact disposition disposition_checked (by
      intro B hB hroot
      obtain ⟨j, word, hnodup, hsame⟩ := boundary_classification
        (fun _ => GrowthRenaming.Renaming.identity
          (fun c => SparseGrowthDAG.has (FacetUniverses.RootedSevenMixed024.ridgeList c))
          FacetUniverses.RootedSevenMixed024.literalCompatible FacetUniverses.RootedSevenMixed024.kind)
        (fun _ _ => rfl) B hB hroot
      refine ⟨j, hnodup, ?_⟩
      simpa only [GrowthRenaming.applyWord_identity] using hsame)

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0024

end
end

/- Source module: CompletedRooted.Case0025 -/
@[expose] public section

/-! Exact finite classification for rooted case 25.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0025

open RootedForests.RootedRawForest0025
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenMixed025.cells =
      (rawLeaves j.val).map RootedCaches.RootedSevenMixed025.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed025.cells =
        ((leaves j).map Fin.val).map RootedCaches.RootedSevenMixed025.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedCaches.RootedSevenMixed025.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed025.cells quota (0 : Fin 466) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed025.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed025.well_formed i))
    leaves (fun j => (rawLeaves j.val).map RootedCaches.RootedSevenMixed025.rawCells)
    raw_leaves_exact disposition disposition_checked (by
      intro B hB hroot
      obtain ⟨j, word, hnodup, hsame⟩ := boundary_classification
        (fun _ => GrowthRenaming.Renaming.identity
          (fun c => SparseGrowthDAG.has (FacetUniverses.RootedSevenMixed025.ridgeList c))
          FacetUniverses.RootedSevenMixed025.literalCompatible FacetUniverses.RootedSevenMixed025.kind)
        (fun _ _ => rfl) B hB hroot
      refine ⟨j, hnodup, ?_⟩
      simpa only [GrowthRenaming.applyWord_identity] using hsame)

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0025

end
end

/- Source module: CompletedRooted.Case0026 -/
@[expose] public section

/-! Exact finite classification for rooted case 26.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0026

open RootedForests.RootedRawForest0026
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenMixed026.cells =
      (rawLeaves j.val).map RootedCaches.RootedSevenMixed026.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed026.cells =
        ((leaves j).map Fin.val).map RootedCaches.RootedSevenMixed026.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedCaches.RootedSevenMixed026.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed026.cells quota (0 : Fin 556) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed026.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed026.well_formed i))
    leaves (fun j => (rawLeaves j.val).map RootedCaches.RootedSevenMixed026.rawCells)
    raw_leaves_exact disposition disposition_checked (by
      intro B hB hroot
      obtain ⟨j, word, hnodup, hsame⟩ := boundary_classification
        (fun _ => GrowthRenaming.Renaming.identity
          (fun c => SparseGrowthDAG.has (FacetUniverses.RootedSevenMixed026.ridgeList c))
          FacetUniverses.RootedSevenMixed026.literalCompatible FacetUniverses.RootedSevenMixed026.kind)
        (fun _ _ => rfl) B hB hroot
      refine ⟨j, hnodup, ?_⟩
      simpa only [GrowthRenaming.applyWord_identity] using hsame)

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0026

end
end

/- Source module: CompletedRooted.Case0027 -/
@[expose] public section

/-! Exact finite classification for rooted case 27.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0027

open RootedForests.RootedRawForest0027
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenMixed027.cells =
      (rawLeaves j.val).map RootedCaches.RootedSevenMixed027.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed027.cells =
        ((leaves j).map Fin.val).map RootedCaches.RootedSevenMixed027.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedCaches.RootedSevenMixed027.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed027.cells quota (0 : Fin 466) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed027.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed027.well_formed i))
    leaves (fun j => (rawLeaves j.val).map RootedCaches.RootedSevenMixed027.rawCells)
    raw_leaves_exact disposition disposition_checked (by
      intro B hB hroot
      obtain ⟨j, word, hnodup, hsame⟩ := boundary_classification
        (fun _ => GrowthRenaming.Renaming.identity
          (fun c => SparseGrowthDAG.has (FacetUniverses.RootedSevenMixed027.ridgeList c))
          FacetUniverses.RootedSevenMixed027.literalCompatible FacetUniverses.RootedSevenMixed027.kind)
        (fun _ _ => rfl) B hB hroot
      refine ⟨j, hnodup, ?_⟩
      simpa only [GrowthRenaming.applyWord_identity] using hsame)

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0027

end
end

/- Source module: CompletedRooted.Case0028 -/
@[expose] public section

/-! Exact finite classification for rooted case 28.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0028

open RootedForests.RootedRawForest0028
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenMixed028.cells =
      (rawLeaves j.val).map RootedCaches.RootedSevenMixed028.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed028.cells =
        ((leaves j).map Fin.val).map RootedCaches.RootedSevenMixed028.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedCaches.RootedSevenMixed028.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed028.cells quota (0 : Fin 466) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed028.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed028.well_formed i))
    leaves (fun j => (rawLeaves j.val).map RootedCaches.RootedSevenMixed028.rawCells)
    raw_leaves_exact disposition disposition_checked (by
      intro B hB hroot
      obtain ⟨j, word, hnodup, hsame⟩ := boundary_classification
        (fun _ => GrowthRenaming.Renaming.identity
          (fun c => SparseGrowthDAG.has (FacetUniverses.RootedSevenMixed028.ridgeList c))
          FacetUniverses.RootedSevenMixed028.literalCompatible FacetUniverses.RootedSevenMixed028.kind)
        (fun _ _ => rfl) B hB hroot
      refine ⟨j, hnodup, ?_⟩
      simpa only [GrowthRenaming.applyWord_identity] using hsame)

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0028

end
end

/- Source module: CompletedRooted.Case0029 -/
@[expose] public section

/-! Exact finite classification for rooted case 29.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0029

open RootedForests.RootedRawForest0029
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenMixed029.cells =
      (rawLeaves j.val).map RootedCaches.RootedSevenMixed029.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed029.cells =
        ((leaves j).map Fin.val).map RootedCaches.RootedSevenMixed029.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedCaches.RootedSevenMixed029.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed029.cells quota (0 : Fin 376) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed029.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed029.well_formed i))
    leaves (fun j => (rawLeaves j.val).map RootedCaches.RootedSevenMixed029.rawCells)
    raw_leaves_exact disposition disposition_checked (by
      intro B hB hroot
      obtain ⟨j, word, hnodup, hsame⟩ := boundary_classification
        (fun _ => GrowthRenaming.Renaming.identity
          (fun c => SparseGrowthDAG.has (FacetUniverses.RootedSevenMixed029.ridgeList c))
          FacetUniverses.RootedSevenMixed029.literalCompatible FacetUniverses.RootedSevenMixed029.kind)
        (fun _ _ => rfl) B hB hroot
      refine ⟨j, hnodup, ?_⟩
      simpa only [GrowthRenaming.applyWord_identity] using hsame)

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0029

end
end

/- Source module: CompletedRooted.Case0030 -/
@[expose] public section

/-! Exact finite classification for rooted case 30.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0030

open RootedForests.RootedRawForest0030
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenMixed030.cells =
      (rawLeaves j.val).map RootedCaches.RootedSevenMixed030.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed030.cells =
        ((leaves j).map Fin.val).map RootedCaches.RootedSevenMixed030.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedCaches.RootedSevenMixed030.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed030.cells quota (0 : Fin 655) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed030.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed030.well_formed i))
    leaves (fun j => (rawLeaves j.val).map RootedCaches.RootedSevenMixed030.rawCells)
    raw_leaves_exact disposition disposition_checked (by
      intro B hB hroot
      obtain ⟨j, word, hnodup, hsame⟩ := boundary_classification
        (fun _ => GrowthRenaming.Renaming.identity
          (fun c => SparseGrowthDAG.has (FacetUniverses.RootedSevenMixed030.ridgeList c))
          FacetUniverses.RootedSevenMixed030.literalCompatible FacetUniverses.RootedSevenMixed030.kind)
        (fun _ _ => rfl) B hB hroot
      refine ⟨j, hnodup, ?_⟩
      simpa only [GrowthRenaming.applyWord_identity] using hsame)

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0030

end
end

/- Source module: CompletedRooted.Case0031 -/
@[expose] public section

/-! Exact finite classification for rooted case 31.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0031

open RootedForests.RootedRawForest0031
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenMixed031.cells =
      (rawLeaves j.val).map RootedCaches.RootedSevenMixed031.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed031.cells =
        ((leaves j).map Fin.val).map RootedCaches.RootedSevenMixed031.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedCaches.RootedSevenMixed031.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed031.cells quota (0 : Fin 655) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed031.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed031.well_formed i))
    leaves (fun j => (rawLeaves j.val).map RootedCaches.RootedSevenMixed031.rawCells)
    raw_leaves_exact disposition disposition_checked (by
      intro B hB hroot
      obtain ⟨j, word, hnodup, hsame⟩ := boundary_classification
        (fun _ => GrowthRenaming.Renaming.identity
          (fun c => SparseGrowthDAG.has (FacetUniverses.RootedSevenMixed031.ridgeList c))
          FacetUniverses.RootedSevenMixed031.literalCompatible FacetUniverses.RootedSevenMixed031.kind)
        (fun _ _ => rfl) B hB hroot
      refine ⟨j, hnodup, ?_⟩
      simpa only [GrowthRenaming.applyWord_identity] using hsame)

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0031

end
end

/- Source module: CompletedRooted.Case0032 -/
@[expose] public section

/-! Exact finite classification for rooted case 32.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0032

open RootedForests.RootedRawForest0032
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenMixed032.cells =
      (rawLeaves j.val).map RootedCaches.RootedSevenMixed032.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed032.cells =
        ((leaves j).map Fin.val).map RootedCaches.RootedSevenMixed032.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedCaches.RootedSevenMixed032.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed032.cells quota (0 : Fin 529) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed032.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed032.well_formed i))
    leaves (fun j => (rawLeaves j.val).map RootedCaches.RootedSevenMixed032.rawCells)
    raw_leaves_exact disposition disposition_checked (by
      intro B hB hroot
      obtain ⟨j, word, hnodup, hsame⟩ := boundary_classification
        (fun _ => GrowthRenaming.Renaming.identity
          (fun c => SparseGrowthDAG.has (FacetUniverses.RootedSevenMixed032.ridgeList c))
          FacetUniverses.RootedSevenMixed032.literalCompatible FacetUniverses.RootedSevenMixed032.kind)
        (fun _ _ => rfl) B hB hroot
      refine ⟨j, hnodup, ?_⟩
      simpa only [GrowthRenaming.applyWord_identity] using hsame)

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0032

end
end

/- Source module: CompletedRooted.Case0033 -/
@[expose] public section

/-! Exact finite classification for rooted case 33.
The quota and the full cell universe are those of the exhaustive numerical
partition. Every leaf is interpreted as the same complete literal boundary. -/

noncomputable section
namespace Papers.RationalityTen.CompletedRooted.Case0033

open RootedForests.RootedRawForest0033
open RawNatGrowthCompleteness RawNatGrowthSoundness

theorem raw_leaves_exact (j : Fin 1) :
    (leaves j).map FacetUniverses.RootedSevenMixed033.cells =
      (rawLeaves j.val).map RootedCaches.RootedSevenMixed033.rawCells := by
  have hb := (Bool.and_eq_true_iff.mp
    (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  have hval : (leaves j).map Fin.val = rawLeaves j.val := val_decode_list _ hb
  calc
    (leaves j).map FacetUniverses.RootedSevenMixed033.cells =
        ((leaves j).map Fin.val).map RootedCaches.RootedSevenMixed033.rawCells := by
      rw [List.map_map]
      rfl
    _ = (rawLeaves j.val).map RootedCaches.RootedSevenMixed033.rawCells := by rw [hval]

def classification : RootedFamilyClosure.FiniteClassification
    FacetUniverses.RootedSevenMixed033.cells quota (0 : Fin 529) :=
  RootedFamilyClosure.FiniteClassification.of_identity
    FacetUniverses.RootedSevenMixed033.cells quota 0
    (fun i => RawFacetEmbeddingSemantics.wellFormed_of_check _ (RootedCaches.RootedSevenMixed033.well_formed i))
    leaves (fun j => (rawLeaves j.val).map RootedCaches.RootedSevenMixed033.rawCells)
    raw_leaves_exact disposition disposition_checked (by
      intro B hB hroot
      obtain ⟨j, word, hnodup, hsame⟩ := boundary_classification
        (fun _ => GrowthRenaming.Renaming.identity
          (fun c => SparseGrowthDAG.has (FacetUniverses.RootedSevenMixed033.ridgeList c))
          FacetUniverses.RootedSevenMixed033.literalCompatible FacetUniverses.RootedSevenMixed033.kind)
        (fun _ _ => rfl) B hB hroot
      refine ⟨j, hnodup, ?_⟩
      simpa only [GrowthRenaming.applyWord_identity] using hsame)

#print axioms classification
end Papers.RationalityTen.CompletedRooted.Case0033

end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0000
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.PackedReplay.PackedSevenMixed000.quota = rowQuota 0 2 6 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 0. -/
def certificate : MixedRowCertificate ⟨2,(some 6),10,13,5,6,2,0,0⟩ where
  cellCount := FacetUniverses.RootedSevenMixed000.cellCount
  cells := FacetUniverses.RootedSevenMixed000.cells
  root := 0
  template := 2
  template_eq := rfl
  sixTemplate := 6
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0000.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed000.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0000
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0001
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.PackedReplay.PackedSevenMixed001.quota = rowQuota 0 2 6 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 1. -/
def certificate : MixedRowCertificate ⟨3,(some 6),10,13,5,6,2,0,0⟩ where
  cellCount := FacetUniverses.RootedSevenMixed001.cellCount
  cells := FacetUniverses.RootedSevenMixed001.cells
  root := 0
  template := 3
  template_eq := rfl
  sixTemplate := 6
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0001.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed001.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0001
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0002
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.PackedReplay.PackedSevenMixed002.quota = rowQuota 0 2 6 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 2. -/
def certificate : MixedRowCertificate ⟨6,(some 6),10,13,5,6,2,0,0⟩ where
  cellCount := FacetUniverses.RootedSevenMixed002.cellCount
  cells := FacetUniverses.RootedSevenMixed002.cells
  root := 0
  template := 6
  template_eq := rfl
  sixTemplate := 6
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0002.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed002.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0002
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0003
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.PackedReplay.PackedSevenMixed003.quota = rowQuota 0 2 6 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 3. -/
def certificate : MixedRowCertificate ⟨7,(some 6),10,13,5,6,2,0,0⟩ where
  cellCount := FacetUniverses.RootedSevenMixed003.cellCount
  cells := FacetUniverses.RootedSevenMixed003.cells
  root := 0
  template := 7
  template_eq := rfl
  sixTemplate := 6
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0003.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed003.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0003
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0004
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.PackedReplay.PackedSevenMixed004.quota = rowQuota 0 2 6 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 4. -/
def certificate : MixedRowCertificate ⟨8,(some 6),10,13,5,6,2,0,0⟩ where
  cellCount := FacetUniverses.RootedSevenMixed004.cellCount
  cells := FacetUniverses.RootedSevenMixed004.cells
  root := 0
  template := 8
  template_eq := rfl
  sixTemplate := 6
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0004.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed004.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0004
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0005
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.PackedReplay.PackedSevenMixed005.quota = rowQuota 0 2 6 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 5. -/
def certificate : MixedRowCertificate ⟨9,(some 6),10,13,5,6,2,0,0⟩ where
  cellCount := FacetUniverses.RootedSevenMixed005.cellCount
  cells := FacetUniverses.RootedSevenMixed005.cells
  root := 0
  template := 9
  template_eq := rfl
  sixTemplate := 6
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0005.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed005.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0005
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0006
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.PackedReplay.PackedSevenMixed006.quota = rowQuota 0 3 5 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 6. -/
def certificate : MixedRowCertificate ⟨11,(some 6),10,13,5,5,3,0,0⟩ where
  cellCount := FacetUniverses.RootedSevenMixed006.cellCount
  cells := FacetUniverses.RootedSevenMixed006.cells
  root := 0
  template := 11
  template_eq := rfl
  sixTemplate := 6
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0006.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed006.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0006
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0007
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.PackedReplay.PackedSevenMixed007.quota = rowQuota 0 3 5 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 7. -/
def certificate : MixedRowCertificate ⟨12,(some 6),10,13,5,5,3,0,0⟩ where
  cellCount := FacetUniverses.RootedSevenMixed007.cellCount
  cells := FacetUniverses.RootedSevenMixed007.cells
  root := 0
  template := 12
  template_eq := rfl
  sixTemplate := 6
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0007.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed007.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0007
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0008
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.PackedReplay.PackedSevenMixed008.quota = rowQuota 0 1 7 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 8. -/
def certificate : MixedRowCertificate ⟨13,(some 0),10,13,5,7,1,0,0⟩ where
  cellCount := FacetUniverses.RootedSevenMixed008.cellCount
  cells := FacetUniverses.RootedSevenMixed008.cells
  root := 0
  template := 13
  template_eq := rfl
  sixTemplate := 0
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0008.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed008.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0008
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0009
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.PackedReplay.PackedSevenMixed009.quota = rowQuota 0 2 6 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 9. -/
def certificate : MixedRowCertificate ⟨13,(some 1),10,13,5,6,2,0,0⟩ where
  cellCount := FacetUniverses.RootedSevenMixed009.cellCount
  cells := FacetUniverses.RootedSevenMixed009.cells
  root := 0
  template := 13
  template_eq := rfl
  sixTemplate := 1
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0009.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed009.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0009
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0010
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.PackedReplay.PackedSevenMixed010.quota = rowQuota 0 1 7 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 10. -/
def certificate : MixedRowCertificate ⟨13,(some 2),10,13,5,7,1,0,0⟩ where
  cellCount := FacetUniverses.RootedSevenMixed010.cellCount
  cells := FacetUniverses.RootedSevenMixed010.cells
  root := 0
  template := 13
  template_eq := rfl
  sixTemplate := 2
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0010.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed010.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0010
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0011
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.PackedReplay.PackedSevenMixed011.quota = rowQuota 0 2 6 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 11. -/
def certificate : MixedRowCertificate ⟨13,(some 3),10,13,5,6,2,0,0⟩ where
  cellCount := FacetUniverses.RootedSevenMixed011.cellCount
  cells := FacetUniverses.RootedSevenMixed011.cells
  root := 0
  template := 13
  template_eq := rfl
  sixTemplate := 3
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0011.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed011.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0011
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0012
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.PackedReplay.PackedSevenMixed012.quota = rowQuota 0 3 5 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 12. -/
def certificate : MixedRowCertificate ⟨13,(some 5),10,13,5,5,3,0,0⟩ where
  cellCount := FacetUniverses.RootedSevenMixed012.cellCount
  cells := FacetUniverses.RootedSevenMixed012.cells
  root := 0
  template := 13
  template_eq := rfl
  sixTemplate := 5
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0012.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed012.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0012
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0013
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.PackedReplay.PackedSevenMixed013.quota = rowQuota 0 4 4 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 13. -/
def certificate : MixedRowCertificate ⟨13,(some 6),10,13,5,4,4,0,0⟩ where
  cellCount := FacetUniverses.RootedSevenMixed013.cellCount
  cells := FacetUniverses.RootedSevenMixed013.cells
  root := 0
  template := 13
  template_eq := rfl
  sixTemplate := 6
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0013.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed013.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0013
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0014
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.PackedReplay.PackedSevenMixed014.quota = rowQuota 0 2 6 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 14. -/
def certificate : MixedRowCertificate ⟨13,(some 6),10,13,6,6,2,0,0⟩ where
  cellCount := FacetUniverses.RootedSevenMixed014.cellCount
  cells := FacetUniverses.RootedSevenMixed014.cells
  root := 0
  template := 13
  template_eq := rfl
  sixTemplate := 6
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0014.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed014.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0014
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0015
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.PackedReplay.PackedSevenMixed015.quota = rowQuota 1 2 6 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 15. -/
def certificate : MixedRowCertificate ⟨13,(some 6),11,13,6,6,2,1,0⟩ where
  cellCount := FacetUniverses.RootedSevenMixed015.cellCount
  cells := FacetUniverses.RootedSevenMixed015.cells
  root := 0
  template := 13
  template_eq := rfl
  sixTemplate := 6
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0015.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed015.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0015
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0016
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.PackedReplay.PackedSevenMixed016.quota = rowQuota 0 2 6 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 16. -/
def certificate : MixedRowCertificate ⟨15,(some 6),10,13,5,6,2,0,0⟩ where
  cellCount := FacetUniverses.RootedSevenMixed016.cellCount
  cells := FacetUniverses.RootedSevenMixed016.cells
  root := 0
  template := 15
  template_eq := rfl
  sixTemplate := 6
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0016.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed016.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0016
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0017
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.PackedReplay.PackedSevenMixed017.quota = rowQuota 0 2 6 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 17. -/
def certificate : MixedRowCertificate ⟨16,(some 6),10,13,5,6,2,0,0⟩ where
  cellCount := FacetUniverses.RootedSevenMixed017.cellCount
  cells := FacetUniverses.RootedSevenMixed017.cells
  root := 0
  template := 16
  template_eq := rfl
  sixTemplate := 6
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0017.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed017.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0017
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0018
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.PackedReplay.PackedSevenMixed018.quota = rowQuota 0 3 5 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 18. -/
def certificate : MixedRowCertificate ⟨18,(some 6),10,13,5,5,3,0,0⟩ where
  cellCount := FacetUniverses.RootedSevenMixed018.cellCount
  cells := FacetUniverses.RootedSevenMixed018.cells
  root := 0
  template := 18
  template_eq := rfl
  sixTemplate := 6
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0018.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed018.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0018
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0019
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.PackedReplay.PackedSevenMixed019.quota = rowQuota 0 3 5 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 19. -/
def certificate : MixedRowCertificate ⟨19,(some 6),10,13,5,5,3,0,0⟩ where
  cellCount := FacetUniverses.RootedSevenMixed019.cellCount
  cells := FacetUniverses.RootedSevenMixed019.cells
  root := 0
  template := 19
  template_eq := rfl
  sixTemplate := 6
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0019.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed019.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0019
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0020
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.PackedReplay.PackedSevenMixed020.quota = rowQuota 0 3 5 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 20. -/
def certificate : MixedRowCertificate ⟨20,(some 6),10,13,5,5,3,0,0⟩ where
  cellCount := FacetUniverses.RootedSevenMixed020.cellCount
  cells := FacetUniverses.RootedSevenMixed020.cells
  root := 0
  template := 20
  template_eq := rfl
  sixTemplate := 6
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0020.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed020.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0020
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0021
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.PackedReplay.PackedSevenMixed021.quota = rowQuota 0 3 5 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 21. -/
def certificate : MixedRowCertificate ⟨21,(some 6),10,13,5,5,3,0,0⟩ where
  cellCount := FacetUniverses.RootedSevenMixed021.cellCount
  cells := FacetUniverses.RootedSevenMixed021.cells
  root := 0
  template := 21
  template_eq := rfl
  sixTemplate := 6
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0021.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed021.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0021
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0022
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.RootedForests.RootedRawForest0022.quota = rowQuota 0 3 5 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 22. -/
def certificate : MixedRowCertificate ⟨23,(some 6),10,13,5,5,3,0,0⟩ where
  cellCount := FacetUniverses.RootedSevenMixed022.cellCount
  cells := FacetUniverses.RootedSevenMixed022.cells
  root := 0
  template := 23
  template_eq := rfl
  sixTemplate := 6
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0022.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed022.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0022
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0023
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.RootedForests.RootedRawForest0023.quota = rowQuota 0 3 5 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 23. -/
def certificate : MixedRowCertificate ⟨24,(some 6),10,13,5,5,3,0,0⟩ where
  cellCount := FacetUniverses.RootedSevenMixed023.cellCount
  cells := FacetUniverses.RootedSevenMixed023.cells
  root := 0
  template := 24
  template_eq := rfl
  sixTemplate := 6
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0023.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed023.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0023
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0024
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.RootedForests.RootedRawForest0024.quota = rowQuota 0 4 4 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 24. -/
def certificate : MixedRowCertificate ⟨25,(some 6),10,13,5,4,4,0,0⟩ where
  cellCount := FacetUniverses.RootedSevenMixed024.cellCount
  cells := FacetUniverses.RootedSevenMixed024.cells
  root := 0
  template := 25
  template_eq := rfl
  sixTemplate := 6
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0024.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed024.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0024
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0025
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.RootedForests.RootedRawForest0025.quota = rowQuota 0 4 4 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 25. -/
def certificate : MixedRowCertificate ⟨27,(some 6),10,13,5,4,4,0,0⟩ where
  cellCount := FacetUniverses.RootedSevenMixed025.cellCount
  cells := FacetUniverses.RootedSevenMixed025.cells
  root := 0
  template := 27
  template_eq := rfl
  sixTemplate := 6
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0025.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed025.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0025
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0026
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.RootedForests.RootedRawForest0026.quota = rowQuota 0 3 5 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 26. -/
def certificate : MixedRowCertificate ⟨28,(some 6),10,13,5,5,3,0,0⟩ where
  cellCount := FacetUniverses.RootedSevenMixed026.cellCount
  cells := FacetUniverses.RootedSevenMixed026.cells
  root := 0
  template := 28
  template_eq := rfl
  sixTemplate := 6
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0026.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed026.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0026
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0027
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.RootedForests.RootedRawForest0027.quota = rowQuota 0 4 4 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 27. -/
def certificate : MixedRowCertificate ⟨29,(some 6),10,13,5,4,4,0,0⟩ where
  cellCount := FacetUniverses.RootedSevenMixed027.cellCount
  cells := FacetUniverses.RootedSevenMixed027.cells
  root := 0
  template := 29
  template_eq := rfl
  sixTemplate := 6
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0027.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed027.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0027
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0028
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.RootedForests.RootedRawForest0028.quota = rowQuota 0 4 4 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 28. -/
def certificate : MixedRowCertificate ⟨31,(some 6),10,13,5,4,4,0,0⟩ where
  cellCount := FacetUniverses.RootedSevenMixed028.cellCount
  cells := FacetUniverses.RootedSevenMixed028.cells
  root := 0
  template := 31
  template_eq := rfl
  sixTemplate := 6
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0028.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed028.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0028
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0029
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.RootedForests.RootedRawForest0029.quota = rowQuota 0 5 3 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 29. -/
def certificate : MixedRowCertificate ⟨33,(some 6),10,13,5,3,5,0,0⟩ where
  cellCount := FacetUniverses.RootedSevenMixed029.cellCount
  cells := FacetUniverses.RootedSevenMixed029.cells
  root := 0
  template := 33
  template_eq := rfl
  sixTemplate := 6
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0029.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed029.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0029
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0030
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.RootedForests.RootedRawForest0030.quota = rowQuota 0 4 4 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 30. -/
def certificate : MixedRowCertificate ⟨10,(some 4),10,13,2,4,4,0,1⟩ where
  cellCount := FacetUniverses.RootedSevenMixed030.cellCount
  cells := FacetUniverses.RootedSevenMixed030.cells
  root := 0
  template := 10
  template_eq := rfl
  sixTemplate := 4
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0030.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed030.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0030
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0031
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.RootedForests.RootedRawForest0031.quota = rowQuota 0 4 4 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 31. -/
def certificate : MixedRowCertificate ⟨17,(some 4),10,13,2,4,4,0,1⟩ where
  cellCount := FacetUniverses.RootedSevenMixed031.cellCount
  cells := FacetUniverses.RootedSevenMixed031.cells
  root := 0
  template := 17
  template_eq := rfl
  sixTemplate := 4
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0031.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed031.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0031
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0032
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.RootedForests.RootedRawForest0032.quota = rowQuota 0 5 3 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 32. -/
def certificate : MixedRowCertificate ⟨26,(some 4),10,13,2,3,5,0,1⟩ where
  cellCount := FacetUniverses.RootedSevenMixed032.cellCount
  cells := FacetUniverses.RootedSevenMixed032.cells
  root := 0
  template := 26
  template_eq := rfl
  sixTemplate := 4
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0032.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed032.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0032
end
end

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSeven.Case0033
open SevenFamilyActualEncoding MatroidChecked.SevenBudgetCoverage

theorem quota_eq : Papers.RationalityTen.RootedForests.RootedRawForest0033.quota = rowQuota 0 5 3 1 := by
  funext k
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k
  · rfl
  rcases k with _ | k <;> rfl

/-- Complete finite and geometric certificate for case 33. -/
def certificate : MixedRowCertificate ⟨30,(some 4),10,13,2,3,5,0,1⟩ where
  cellCount := FacetUniverses.RootedSevenMixed033.cellCount
  cells := FacetUniverses.RootedSevenMixed033.cells
  root := 0
  template := 30
  template_eq := rfl
  sixTemplate := 4
  six_eq := rfl
  classification := by
    rw [← quota_eq]
    exact Papers.RationalityTen.CompletedRooted.Case0033.classification
  coverage := Papers.RationalityTen.RootedCoverage.RootedSevenMixed033.rowCoverage

#print axioms certificate
end Papers.RationalityTen.CompletedSeven.Case0033
end
end

