module

public import Projection.Hyperplane
public import Projection.SegmentDeterminant

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace RankThreeProjection
open VolumePolynomials

def splitFirst (n : ℕ) : Space (n + 1) ≃L[ℝ] (ℝ × Space n) where
  toFun x := (x 0, fun i => x i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv x := by ext i; exact Fin.cases rfl (fun _ => rfl) i
  right_inv p := by cases p; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply continuous_pi
    intro i
    refine Fin.cases continuous_fst (fun j => ?_) i
    exact (continuous_apply j).comp continuous_snd

theorem splitFirst_measurePreserving (n : ℕ) :
    MeasurePreserving (splitFirst n) volume volume := by
  exact volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0

def tailCoordinates (n : ℕ) : Space (n + 1) →L[ℝ] Space n :=
  (ContinuousLinearMap.snd ℝ ℝ (Space n)).comp (splitFirst n).toContinuousLinearMap

@[simp] theorem tailCoordinates_apply (n : ℕ) (x : Space (n + 1)) (i : Fin n) :
    tailCoordinates n x i = x i.succ := rfl

@[simp] theorem splitFirst_basis_zero (n : ℕ) :
    splitFirst n (Pi.single 0 1) = (1, (0 : Space n)) := by
  ext i <;> simp [splitFirst]

@[simp] theorem tailCoordinates_basis_succ (n : ℕ) (j : Fin n) :
    tailCoordinates n (Pi.single j.succ 1) = Pi.single j 1 := by
  ext i
  simp [tailCoordinates_apply, Pi.single_apply, Fin.succ_inj]

/-- One coordinate deletion, with its exact mixed-volume normalization. -/
theorem mixedVolume_coordinate_head {n : ℕ} (K : Fin n → Body (n + 1)) :
    (n + 1 : ℝ) * mixedVolume volume
      (Fin.cons (centeredSegment (Pi.single 0 1)) K) =
      mixedVolume volume (fun i => mapBody (tailCoordinates n) (K i)) := by
  have h := mixedVolume_map_measurePreserving volume volume (splitFirst n)
    (splitFirst_measurePreserving n)
    (Fin.cons (centeredSegment (Pi.single 0 1)) K)
  have he : (fun i => mapBody (splitFirst n).toContinuousLinearMap
      ((Fin.cons (centeredSegment (Pi.single 0 1)) K :
        Fin (n + 1) → Body (n + 1)) i)) =
      Fin.cons (centeredSegment (1, (0 : Space n)))
        (fun i => mapBody (splitFirst n).toContinuousLinearMap (K i)) := by
    funext i
    refine Fin.cases ?_ (fun _ => rfl) i
    simp only [Fin.cons_zero, map_centeredSegment]
    exact congrArg centeredSegment (splitFirst_basis_zero n)
  rw [← h, he, mixedVolume_centered_axis]
  congr 1
  funext i
  exact mapBody_comp _ _ _

/-- Delete the first `k` coordinates, keeping the last `d`. -/
def dropCoordinates (d k : ℕ) : Space (d + k) →L[ℝ] Space d :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj
    (⟨j.val + k, Nat.add_lt_add_right j.isLt k⟩ : Fin (d + k)))

@[simp] theorem dropCoordinates_apply (d k : ℕ) (x : Space (d + k)) (j : Fin d) :
    dropCoordinates d k x j = x ⟨j.val + k, Nat.add_lt_add_right j.isLt k⟩ := rfl

@[simp] theorem dropCoordinates_zero (d : ℕ) :
    dropCoordinates d 0 = ContinuousLinearMap.id ℝ (Space d) := by ext; rfl

theorem dropCoordinates_succ (d k : ℕ) :
    (dropCoordinates d k).comp (tailCoordinates (d + k)) = dropCoordinates d (k + 1) := by
  ext x j
  rfl

/-- Standard segments in the first `k` slots and copies of `K` elsewhere. -/
def coordinateTuple {d k : ℕ} (K : Body (d + k)) : Fin (d + k) → Body (d + k) :=
  fun i => if i.val < k then centeredSegment (Pi.single i 1) else K

theorem coordinateTuple_zero (d : ℕ) (K : Body d) :
    coordinateTuple (d := d) (k := 0) K = fun _ => K := by
  funext i
  simp [coordinateTuple]

theorem coordinateTuple_succ {d k : ℕ} (K : Body (d + (k + 1))) :
    coordinateTuple (d := d) (k := k + 1) K =
      Fin.cons (centeredSegment (Pi.single 0 1))
        (fun j : Fin (d + k) => coordinateTuple (d := d) (k := k + 1) K j.succ) := by
  funext i
  refine Fin.cases ?_ (fun _ => rfl) i
  simp [coordinateTuple]

theorem coordinateTuple_tail {d k : ℕ} (K : Body (d + (k + 1))) :
    (fun j : Fin (d + k) => mapBody (tailCoordinates (d + k))
      (coordinateTuple (d := d) (k := k + 1) K j.succ)) =
      coordinateTuple (d := d) (k := k) (mapBody (tailCoordinates (d + k)) K) := by
  funext j
  by_cases hj : j.val < k
  · have hj' : j.succ.val < k + 1 := Nat.succ_lt_succ hj
    simp only [coordinateTuple, if_pos hj, if_pos hj',
      map_centeredSegment, tailCoordinates_basis_succ]
  · have hj' : ¬j.succ.val < k + 1 := fun h => hj (Nat.lt_of_succ_lt_succ h)
    simp only [coordinateTuple, if_neg hj, if_neg hj']

/-- Iterated actual interval extrusion. This includes zero-dimensional
projections and every lower-dimensional input body. -/
theorem coordinateTuple_factorial (d k : ℕ) (K : Body (d + k)) :
    ((d + k).factorial : ℝ) * mixedVolume volume (coordinateTuple (d := d) (k := k) K) =
      (d.factorial : ℝ) * volume.real
        ((mapBody (dropCoordinates d k) K : Body d) : Set (Space d)) := by
  induction k with
  | zero =>
      rw [coordinateTuple_zero, dropCoordinates_zero]
      have hm : mapBody (ContinuousLinearMap.id ℝ (Space d)) K = K := by
        apply ConvexBody.ext
        exact Set.image_id _
      rw [hm, mixedVolume_diagonal volume (by simp [Space])]
      simp only [Nat.add_zero]
  | succ k ih =>
      have hex : (d + k + 1 : ℝ) *
          mixedVolume volume (coordinateTuple (d := d) (k := k + 1) K) =
          mixedVolume volume (coordinateTuple (d := d) (k := k)
            (mapBody (tailCoordinates (d + k)) K)) := by
        rw [coordinateTuple_succ]
        simpa only [Nat.cast_add, Nat.cast_one, coordinateTuple_tail] using
          mixedVolume_coordinate_head
            (fun j : Fin (d + k) => coordinateTuple (d := d) (k := k + 1) K j.succ)
      calc
        _ = ((d + k).factorial : ℝ) * ((d + k + 1 : ℝ) *
            mixedVolume volume (coordinateTuple (d := d) (k := k + 1) K)) := by
              have hf : ((d + (k + 1)).factorial : ℝ) =
                  ((d + k).factorial : ℝ) * (d + k + 1 : ℝ) := by
                rw [Nat.add_succ, Nat.factorial_succ]
                push_cast
                ring
              rw [hf, mul_assoc]
        _ = ((d + k).factorial : ℝ) * mixedVolume volume
            (coordinateTuple (d := d) (k := k) (mapBody (tailCoordinates (d + k)) K)) := by rw [hex]
        _ = (d.factorial : ℝ) * volume.real
            ((mapBody (dropCoordinates d k) (mapBody (tailCoordinates (d + k)) K) : Body d) :
              Set (Space d)) := ih _
        _ = _ := by rw [mapBody_comp, dropCoordinates_succ]

theorem coordinateTuple_extrusion (d k : ℕ) (K : Body (d + k)) :
    ((d + k).factorial : ℝ) / (d.factorial : ℝ) *
        mixedVolume volume (coordinateTuple (d := d) (k := k) K) =
      volume.real ((mapBody (dropCoordinates d k) K : Body d) : Set (Space d)) := by
  have h := coordinateTuple_factorial d k K
  have hd : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  rw [div_mul_eq_mul_div₀, div_eq_iff hd]
  exact h.trans (mul_comm _ _)

end RankThreeProjection
