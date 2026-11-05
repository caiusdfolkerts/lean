module

public import Projection.Normalization.Theorem31
public import Projection.HyperplaneObstruction

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Module
open scoped Pointwise BigOperators Topology

namespace RankThreeProjection
open VolumePolynomials

def firstDeleted {n : ℕ} (I : Deleted n 2) : Fin n :=
  I.val.orderEmbOfFin I.property 0

def secondDeleted {n : ℕ} (I : Deleted n 2) : Fin n :=
  I.val.orderEmbOfFin I.property 1

theorem firstDeleted_ne_secondDeleted {n : ℕ} (I : Deleted n 2) :
    firstDeleted I ≠ secondDeleted I := by
  intro h
  have he := (I.val.orderEmbOfFin I.property).injective h
  exact (by decide : (0 : Fin 2) ≠ 1) he

theorem deleted_pair {n : ℕ} (I : Deleted n 2) :
    I.val = {firstDeleted I, secondDeleted I} := by
  apply Finset.coe_injective
  rw [← I.val.range_orderEmbOfFin I.property]
  ext i
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases j <;> simp [firstDeleted, secondDeleted]
  · intro hi
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-- Extract the two-coordinate-deletion tuple from a symmetric hollow array. -/
def tupleOfArray {n : ℕ} (P : Array n) : Deleted n 2 → ℝ :=
  fun I => P (firstDeleted I) (secondDeleted I)

/-- Fill both symmetric entries from each two-element deletion set. -/
def arrayOfTuple {n : ℕ} (p : Deleted n 2 → ℝ) : Array n := fun i j =>
  if h : i = j then 0 else p ⟨{i, j}, by simp [h]⟩

theorem arrayOfTuple_tupleOfArray {n : ℕ} (P : Array n)
    (hdiag : ∀ i, P i i = 0) (hsym : ∀ i j, P i j = P j i) :
    arrayOfTuple (tupleOfArray P) = P := by
  funext i j
  by_cases hij : i = j
  · subst j
    simp [arrayOfTuple, hdiag]
  let I : Deleted n 2 := ⟨{i, j}, by simp [hij]⟩
  have ha : firstDeleted I = i ∨ firstDeleted I = j := by
    simpa only [firstDeleted, I, Finset.mem_insert, Finset.mem_singleton] using
      I.val.orderEmbOfFin_mem I.property (0 : Fin 2)
  have hb : secondDeleted I = i ∨ secondDeleted I = j := by
    simpa only [secondDeleted, I, Finset.mem_insert, Finset.mem_singleton] using
      I.val.orderEmbOfFin_mem I.property (1 : Fin 2)
  have hab := firstDeleted_ne_secondDeleted I
  change (if h : i = j then 0 else
    P (firstDeleted ⟨{i, j}, by simp [h]⟩)
      (secondDeleted ⟨{i, j}, by simp [h]⟩)) = P i j
  rw [dif_neg hij]
  change P (firstDeleted I) (secondDeleted I) = P i j
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact (hab (ha.trans hb.symm)).elim
  · rw [ha, hb]
  · rw [ha, hb, hsym j i]
  · exact (hab (ha.trans hb.symm)).elim

theorem tupleOfArray_projectionArray {n : ℕ} (K : Body n) :
    tupleOfArray (projectionArray K) = allProjectionArray (k := 2) K := by
  funext I
  simp only [tupleOfArray, projectionArray,
    if_neg (firstDeleted_ne_secondDeleted I), allProjectionArray]
  rw [← deleted_pair I]

theorem arrayOfTuple_allProjectionArray {n : ℕ} (K : Body n) :
    arrayOfTuple (allProjectionArray (k := 2) K) = projectionArray K := by
  rw [← tupleOfArray_projectionArray]
  exact arrayOfTuple_tupleOfArray _ (projectionArray_diagonal K) (projectionArray_symmetric K)

theorem continuous_tupleOfArray {n : ℕ} : Continuous (tupleOfArray (n := n)) := by
  apply continuous_pi
  intro I
  exact (continuous_apply (secondDeleted I)).comp (continuous_apply (firstDeleted I))

theorem continuous_arrayOfTuple {n : ℕ} : Continuous (arrayOfTuple (n := n)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases hij : i = j
  · simpa only [arrayOfTuple, dif_pos hij] using
      (continuous_const : Continuous (fun _ : Deleted n 2 → ℝ => (0 : ℝ)))
  · simpa only [arrayOfTuple, dif_neg hij] using
      (continuous_apply (⟨{i, j}, by simp [hij]⟩ : Deleted n 2))

theorem factorial_ratio_two {n : ℕ} (hn : 2 ≤ n) :
    (n.factorial : ℝ) / ((n - 2).factorial : ℝ) =
      (n - 2 + 2 : ℕ) * (n - 2 + 1 : ℕ) := by
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 2 := ⟨n - 2, by omega⟩
  simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  have hd : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  field_simp
  ring

theorem markedTuple_pair_volume {n : ℕ} (K : Body n) (U : Fin n → Space n)
    (I : Deleted n 2) :
    mixedVolume volume (markedTuple K U I) =
      mixedVolume volume
        (Fin.cons (centeredSegment (U (firstDeleted I)))
          (Fin.cons (centeredSegment (U (secondDeleted I)))
            (fun _ : Fin (n - 2) => K))) := by
  let T : Fin (n - 2 + 2) → Body n :=
    Fin.cons (centeredSegment (U (firstDeleted I)))
      (Fin.cons (centeredSegment (U (secondDeleted I))) (fun _ : Fin (n - 2) => K))
  have he : (fun i => T (rotateMarkedIndices (n - 2) 2 i)) = markedTuple K U I := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      rw [rotateMarkedIndices_body]
      have hj : tailIndex 2 j = j.succ.succ := by apply Fin.ext; simp
      simp only [hj, T, Fin.cons_succ, markedTuple, Fin.append_left]
    · intro j
      rw [rotateMarkedIndices_segment]
      fin_cases j
      · simp only [markedTuple, Fin.append_right]
        change T (headIndex (n - 2) (0 : Fin 2)) =
          centeredSegment (U (firstDeleted I))
        have hj : headIndex (n - 2) (0 : Fin 2) = 0 := by apply Fin.ext; rfl
        rw [hj]
        exact Fin.cons_zero _ _
      · simp only [markedTuple, Fin.append_right]
        change T (headIndex (n - 2) (1 : Fin 2)) =
          centeredSegment (U (secondDeleted I))
        have hj : headIndex (n - 2) (1 : Fin 2) = 1 := by apply Fin.ext; rfl
        rw [hj]
        simp only [T, Fin.cons_one, Fin.cons_zero]
  rw [← he]
  exact mixedVolume_reindex volume T (rotateMarkedIndices (n - 2) 2)

theorem tupleOfArray_complementaryMixedMatrix {n : ℕ} (hn : 2 ≤ n)
    (K : Body n) (U : Fin n → Space n) :
    tupleOfArray (complementaryMixedMatrix (d := n - 2) K U) =
      allMarkedArray (k := 2) K U := by
  funext I
  simp only [tupleOfArray, complementaryMixedMatrix, allMarkedArray,
    markedTuple_pair_volume, factorial_ratio_two hn, Nat.cast_add, Nat.cast_ofNat,
    Nat.cast_one]

theorem arrayOfTuple_allMarkedArray {n : ℕ} (hn : 2 ≤ n)
    (K : Body n) (U : Fin n → Space n) :
    arrayOfTuple (allMarkedArray (k := 2) K U) =
      complementaryMixedMatrix (d := n - 2) K U := by
  rw [← tupleOfArray_complementaryMixedMatrix hn]
  exact arrayOfTuple_tupleOfArray _
    (complementaryMixedMatrix_diagonal K U) (complementaryMixedMatrix_symmetric K U)

theorem closedProjectionLocus_hollow_symmetric {n : ℕ} {P : Array n}
    (hP : P ∈ closedProjectionLocus n) :
    (∀ i, P i i = 0) ∧ (∀ i j, P i j = P j i) := by
  constructor
  · intro i
    have hclosed : IsClosed {Q : Array n | Q i i = 0} :=
      isClosed_eq ((continuous_apply i).comp (continuous_apply i)) continuous_const
    apply (hclosed.closure_subset_iff (s := projectionLocus n)).mpr ?_ hP
    rintro Q ⟨K, rfl⟩
    exact projectionArray_diagonal K i
  · intro i j
    have hclosed : IsClosed {Q : Array n | Q i j = Q j i} :=
      isClosed_eq ((continuous_apply j).comp (continuous_apply i))
        ((continuous_apply i).comp (continuous_apply j))
    apply (hclosed.closure_subset_iff (s := projectionLocus n)).mpr ?_ hP
    rintro Q ⟨K, rfl⟩
    exact projectionArray_symmetric K i j

/-- The exact matrix form of Theorem 3.1 for complementary projections.
The matrix on the right is defined by actual mixed volumes even on its
diagonal; its hollowness was proved by repeated-segment extrusion. -/
theorem complementary_compactification {n : ℕ} (hn : 3 ≤ n) (P : Array n) :
    P ∈ closedProjectionLocus n ↔
      ∃ (K : Body n) (U : Fin n → Space n),
        n - 1 ≤ bodyDimension K ∧ complementaryMixedMatrix (d := n - 2) K U = P := by
  constructor
  · intro hP
    have ht : tupleOfArray P ∈ closure (allProjectionLocus n 2) := by
      have h := mem_closure_image continuous_tupleOfArray.continuousAt hP
      apply closure_mono (t := allProjectionLocus n 2) ?_ h
      rintro _ ⟨Q, ⟨K, rfl⟩, rfl⟩
      exact ⟨K, (tupleOfArray_projectionArray K).symm⟩
    obtain ⟨K, U, hdim, he⟩ :=
      (theorem31_with_dimension (by omega) (by omega) (tupleOfArray P)).mp ht
    obtain ⟨hdiag, hsym⟩ := closedProjectionLocus_hollow_symmetric hP
    refine ⟨K, U, ?_, ?_⟩
    · simpa only [show n - 2 + 1 = n - 1 by omega] using hdim
    · have hh := congrArg arrayOfTuple he
      rw [arrayOfTuple_allMarkedArray (by omega),
        arrayOfTuple_tupleOfArray P hdiag hsym] at hh
      exact hh
  · rintro ⟨K, U, _hdim, rfl⟩
    have ht : allMarkedArray (k := 2) K U ∈ closure (allProjectionLocus n 2) :=
      (theorem31 (by omega) (by omega) _).mpr ⟨K, U, rfl⟩
    have h := mem_closure_image continuous_arrayOfTuple.continuousAt ht
    rw [arrayOfTuple_allMarkedArray (by omega)] at h
    apply closure_mono (t := projectionLocus n) ?_ h
    rintro _ ⟨p, ⟨L, rfl⟩, rfl⟩
    exact ⟨L, (arrayOfTuple_allProjectionArray L).symm⟩

end RankThreeProjection
