module

public import Projection.CoordinateExtrusion
public import Mathlib.Topology.Algebra.Module.Equiv.Pi
public import Mathlib.Logic.Equiv.Set

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace RankThreeProjection
open VolumePolynomials

section Relabel
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A coordinate permutation or relabeling, with the ordinary product measure. -/
def relabelCoordinates (e : ι ≃ κ) : (ι → ℝ) ≃L[ℝ] (κ → ℝ) :=
  ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : κ => ℝ) e

@[simp] theorem relabelCoordinates_apply (e : ι ≃ κ) (x : ι → ℝ) (j : κ) :
    relabelCoordinates e x j = x (e.symm j) := by
  change Equiv.piCongrLeft (fun _ : κ => ℝ) e x j = x (e.symm j)
  simpa only [Equiv.apply_symm_apply] using
    (Equiv.piCongrLeft_apply_apply (P := fun _ : κ => ℝ) (e := e) x (e.symm j))

@[simp] theorem relabelCoordinates_symm_apply (e : ι ≃ κ) (x : κ → ℝ) (j : ι) :
    (relabelCoordinates e).symm x j = x (e j) := rfl

theorem relabelCoordinates_measurePreserving (e : ι ≃ κ) :
    MeasurePreserving (relabelCoordinates e) volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ : κ => ℝ) e

theorem relabelCoordinates_basis (e : ι ≃ κ) (i : ι) :
    relabelCoordinates e (Pi.single i 1) = Pi.single (e i) 1 := by
  ext j
  by_cases hj : j = e i
  · subst j
    simp
  · have he : e.symm j ≠ i := by
      intro h
      exact hj ((e.apply_symm_apply j).symm.trans (congrArg e h))
    simp [Pi.single_apply, hj, Ne.symm hj, he, Ne.symm he]

end Relabel

def retainedCoordinateEquiv {n k : ℕ} (I : Deleted n k) :
    Fin (n - k) ≃ Retained I.val :=
  Fintype.equivOfCardEq (by
    simp only [Retained, Fintype.card_subtype_compl, Fintype.card_coe,
      Fintype.card_fin, I.property])

/-- Deleted coordinates are placed first, in their increasing order; retained
coordinates are placed last. The choice of order on the retained coordinates
does not change their Lebesgue volume. -/
def deletedCoordinateEquiv {n k : ℕ} (I : Deleted n k) : Fin (n - k + k) ≃ Fin n :=
  (((finCongr (Nat.add_comm (n - k) k)).trans finSumFinEquiv.symm).trans
    (Equiv.sumCongr (I.val.orderIsoOfFin I.property).toEquiv (retainedCoordinateEquiv I))).trans
      (Equiv.sumCompl (fun i : Fin n => i ∈ I.val))

def headIndex (d : ℕ) {k : ℕ} (i : Fin k) : Fin (d + k) :=
  (finCongr (Nat.add_comm d k)).symm (Fin.castAdd d i)

def tailIndex (k : ℕ) {d : ℕ} (i : Fin d) : Fin (d + k) :=
  ⟨i.val + k, Nat.add_lt_add_right i.isLt k⟩

@[simp] theorem headIndex_val (d : ℕ) {k : ℕ} (i : Fin k) :
    (headIndex d i).val = i.val := rfl

@[simp] theorem tailIndex_val (k : ℕ) {d : ℕ} (i : Fin d) :
    (tailIndex k i).val = i.val + k := rfl

@[simp] theorem deletedCoordinateEquiv_head {n k : ℕ} (I : Deleted n k) (i : Fin k) :
    deletedCoordinateEquiv I (headIndex (n - k) i) = I.val.orderEmbOfFin I.property i := by
  simp [deletedCoordinateEquiv, headIndex, Finset.coe_orderIsoOfFin_apply]

@[simp] theorem deletedCoordinateEquiv_tail {n k : ℕ} (I : Deleted n k) (i : Fin (n - k)) :
    deletedCoordinateEquiv I (tailIndex k i) = (retainedCoordinateEquiv I i).val := by
  have hi : tailIndex k i =
      (finCongr (Nat.add_comm (n - k) k)).symm (Fin.natAdd k i) := by
    apply Fin.ext
    exact Nat.add_comm _ _
  simp [hi, deletedCoordinateEquiv]

/-- Rotate the argument list from body-first to segment-first order. -/
def rotateMarkedIndices (d k : ℕ) : Equiv.Perm (Fin (d + k)) :=
  finAddFlip.trans (finCongr (Nat.add_comm k d))

@[simp] theorem rotateMarkedIndices_body (d k : ℕ) (i : Fin d) :
    rotateMarkedIndices d k (Fin.castAdd k i) = tailIndex k i := by
  simp only [rotateMarkedIndices, Equiv.trans_apply, finAddFlip_apply_castAdd]
  apply Fin.ext
  exact Nat.add_comm _ _

@[simp] theorem rotateMarkedIndices_segment (d k : ℕ) (i : Fin k) :
    rotateMarkedIndices d k (Fin.natAdd d i) = headIndex d i := by
  simp only [rotateMarkedIndices, Equiv.trans_apply, finAddFlip_apply_natAdd]
  rfl

theorem map_relabel_inverse_body {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (K : ConvexBody (κ → ℝ)) :
    mapBody (relabelCoordinates e).toContinuousLinearMap
      (mapBody (relabelCoordinates e).symm.toContinuousLinearMap K) = K := by
  rw [mapBody_comp]
  apply ConvexBody.ext
  change (fun x => relabelCoordinates e ((relabelCoordinates e).symm x)) '' (K : Set _) = _
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  exact Set.image_id _

theorem mapped_coordinateTuple_eq_markedTuple {n k : ℕ} (I : Deleted n k) (K : Body n) :
    (fun i => mapBody (relabelCoordinates (deletedCoordinateEquiv I)).toContinuousLinearMap
      (coordinateTuple (d := n - k) (k := k)
        (mapBody (relabelCoordinates (deletedCoordinateEquiv I)).symm.toContinuousLinearMap K)
        (rotateMarkedIndices (n - k) k i))) =
      markedTuple K (fun j => Pi.single j 1) I := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [rotateMarkedIndices_body, coordinateTuple, tailIndex_val,
      show ¬j.val + k < k by omega, if_false, map_relabel_inverse_body,
      markedTuple, Fin.append_left]
  · intro j
    simp only [rotateMarkedIndices_segment, coordinateTuple, headIndex_val,
      j.isLt, if_true, map_centeredSegment, ContinuousLinearEquiv.coe_coe,
      relabelCoordinates_basis,
      deletedCoordinateEquiv_head, markedTuple, Fin.append_right]

theorem markedTuple_eq_coordinateTuple_volume {n k : ℕ} (I : Deleted n k) (K : Body n) :
    mixedVolume volume (markedTuple K (fun j => Pi.single j 1) I) =
      mixedVolume volume (coordinateTuple (d := n - k) (k := k)
        (mapBody (relabelCoordinates (deletedCoordinateEquiv I)).symm.toContinuousLinearMap K)) := by
  rw [← mapped_coordinateTuple_eq_markedTuple]
  rw [mixedVolume_map_measurePreserving volume volume
    (relabelCoordinates (deletedCoordinateEquiv I))
    (relabelCoordinates_measurePreserving (deletedCoordinateEquiv I))]
  exact mixedVolume_reindex volume _ (rotateMarkedIndices (n - k) k)

theorem projectedBody_relabel_drop {n k : ℕ} (I : Deleted n k) (K : Body n) :
    mapBody (relabelCoordinates (retainedCoordinateEquiv I)).toContinuousLinearMap
      (mapBody (dropCoordinates (n - k) k)
        (mapBody (relabelCoordinates (deletedCoordinateEquiv I)).symm.toContinuousLinearMap K)) =
      projectedBody I.val K := by
  rw [mapBody_comp, mapBody_comp]
  congr 1
  ext x j
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    relabelCoordinates_apply, relabelCoordinates_symm_apply, dropCoordinates_apply,
    deleteCoordinates_apply]
  change x (deletedCoordinateEquiv I (tailIndex k ((retainedCoordinateEquiv I).symm j))) = x j.val
  rw [deletedCoordinateEquiv_tail, Equiv.apply_symm_apply]

/-- The actual coordinate projection volume is exactly the marked
mixed-volume coefficient with standard basis marks. -/
theorem coordinateVolume_eq_standardMarked {n k : ℕ} (I : Deleted n k) (K : Body n) :
    coordinateVolume I.val K = allMarkedArray K (fun i => Pi.single i 1) I := by
  have hkn : k ≤ n := by
    have h := I.val.card_le_univ
    simpa only [I.property, Fintype.card_fin] using h
  let K' : Body (n - k + k) :=
    mapBody (relabelCoordinates (deletedCoordinateEquiv I)).symm.toContinuousLinearMap K
  have hvol : coordinateVolume I.val K =
      volume.real ((mapBody (dropCoordinates (n - k) k) K' : Body (n - k)) :
        Set (Space (n - k))) := by
    rw [coordinateVolume, ← projectedBody_relabel_drop I K]
    change volume.real ((relabelCoordinates (retainedCoordinateEquiv I)) ''
      ((mapBody (dropCoordinates (n - k) k) K' : Body (n - k)) : Set (Space (n - k)))) = _
    exact measureReal_image_measurePreserving volume volume
      (relabelCoordinates (retainedCoordinateEquiv I))
      (relabelCoordinates_measurePreserving (retainedCoordinateEquiv I)) _
  rw [hvol, allMarkedArray, markedTuple_eq_coordinateTuple_volume]
  simpa only [Nat.sub_add_cancel hkn] using
    (coordinateTuple_extrusion (n - k) k K').symm

/-- Statement-level identification required in Theorem 3.1. Both sides are
defined independently from actual bodies, projections, and mixed volume. -/
theorem allProjectionArray_eq_standardMarked {n k : ℕ} (K : Body n) :
    allProjectionArray (k := k) K = allMarkedArray K (fun i => Pi.single i 1) := by
  funext I
  exact coordinateVolume_eq_standardMarked I K

end RankThreeProjection
