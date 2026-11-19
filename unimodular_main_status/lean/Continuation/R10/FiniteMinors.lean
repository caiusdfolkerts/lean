module

public import Continuation.R10.Data
public import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
public import Mathlib.Data.Finset.Sort

@[expose] public section

open Matrix
open scoped BigOperators

namespace Unimodular.FiniteMatrixCertificates

def orderedMinor {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (s : Finset (Fin m)) (t : Finset (Fin n)) (h : s.card = t.card) :
    Matrix (Fin s.card) (Fin s.card) ℤ :=
  A.submatrix (s.orderEmbOfFin rfl) (t.orderEmbOfFin h.symm)

theorem totallyUnimodular_of_orderedMinors {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : ∀ s t h, |(orderedMinor A s t h).det| ≤ 1) : A.IsTotallyUnimodular := by
  classical
  intro k f g hf hg
  let s : Finset (Fin m) := Finset.univ.image f
  let t : Finset (Fin n) := Finset.univ.image g
  have hs : s.card = k := by simp [s, Finset.card_image_of_injective _ hf]
  have ht : t.card = k := by simp [t, Finset.card_image_of_injective _ hg]
  have h : s.card = t.card := hs.trans ht.symm
  let ef : Fin k ≃ s := Equiv.ofBijective
    (fun i => ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
    ⟨fun i j hij => hf (congrArg Subtype.val hij), by
      intro i
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp i.property
      exact ⟨j, Subtype.ext hj⟩⟩
  let eg : Fin k ≃ t := Equiv.ofBijective
    (fun i => ⟨g i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
    ⟨fun i j hij => hg (congrArg Subtype.val hij), by
      intro i
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp i.property
      exact ⟨j, Subtype.ext hj⟩⟩
  let er : Fin k ≃ Fin s.card := ef.trans (s.orderIsoOfFin rfl).symm.toEquiv
  let ec : Fin k ≃ Fin s.card := eg.trans (t.orderIsoOfFin h.symm).symm.toEquiv
  have hr : ∀ i, s.orderEmbOfFin rfl (er i) = f i := by
    intro i
    change ((s.orderIsoOfFin rfl) ((s.orderIsoOfFin rfl).symm (ef i))).val = f i
    rw [OrderIso.apply_symm_apply]
    rfl
  have hc : ∀ i, t.orderEmbOfFin h.symm (ec i) = g i := by
    intro i
    change ((t.orderIsoOfFin h.symm) ((t.orderIsoOfFin h.symm).symm (eg i))).val = g i
    rw [OrderIso.apply_symm_apply]
    rfl
  have heq : A.submatrix f g = (orderedMinor A s t h).submatrix er ec := by
    ext i j
    simp only [orderedMinor, Matrix.submatrix_apply, hr, hc]
  have hb : |(A.submatrix f g).det| ≤ 1 := by
    rw [heq, Matrix.abs_det_submatrix_equiv_equiv]
    exact hA s t h
  have hh := abs_le.mp hb
  have hd : (A.submatrix f g).det = -1 ∨ (A.submatrix f g).det = 0 ∨
      (A.submatrix f g).det = 1 := by omega
  rcases hd with hd | hd | hd
  · exact ⟨-1, by simpa using hd.symm⟩
  · exact ⟨0, by simpa using hd.symm⟩
  · exact ⟨1, by simpa using hd.symm⟩

def sortedMinor {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (s : Finset (Fin m)) (t : Finset (Fin n)) (h : s.card = t.card) :
    Matrix (Fin s.card) (Fin s.card) ℤ := fun i j =>
  A ((s.sort (· ≤ ·))[i.val]'(by rw [Finset.length_sort]; exact i.isLt))
    ((t.sort (· ≤ ·))[j.val]'(by rw [Finset.length_sort, ← h]; exact j.isLt))

theorem sortedMinor_eq_orderedMinor {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (s : Finset (Fin m)) (t : Finset (Fin n)) (h : s.card = t.card) :
    sortedMinor A s t h = orderedMinor A s t h := by
  ext i j
  simp only [sortedMinor, orderedMinor, Matrix.submatrix_apply,
    Finset.orderEmbOfFin_apply, Fin.getElem_fin]

/-- Filtering a finite range gives the increasing enumeration without evaluating merge-sort. -/
theorem filterFinRange_eq_sort {n : ℕ} (s : Finset (Fin n)) :
    (List.finRange n).filter (· ∈ s) = s.sort (· ≤ ·) := by
  let l := (List.finRange n).filter (· ∈ s)
  have hn : l.Nodup := (List.nodup_finRange n).filter _
  have hp : (List.finRange n).Pairwise (· ≤ ·) := by
    rw [← Fin.sort_univ n]
    exact Finset.pairwise_sort _ _
  have hl : l.Pairwise (· ≤ ·) := hp.filter _
  have he : l.toFinset = s := by ext i; simp [l]
  have hh := (List.toFinset_sort (r := (· ≤ ·)) hn).2 hl
  simpa only [he] using hh.symm

theorem filterFinRange_length {n : ℕ} (s : Finset (Fin n)) :
    ((List.finRange n).filter (· ∈ s)).length = s.card := by
  rw [filterFinRange_eq_sort, Finset.length_sort]

def filteredMinor {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (s : Finset (Fin m)) (t : Finset (Fin n)) (h : s.card = t.card) :
    Matrix (Fin s.card) (Fin s.card) ℤ := fun i j =>
  A (((List.finRange m).filter (· ∈ s))[i.val]'
      (by rw [filterFinRange_length]; exact i.isLt))
    (((List.finRange n).filter (· ∈ t))[j.val]'
      (by rw [filterFinRange_length, ← h]; exact j.isLt))

theorem filteredMinor_eq_sortedMinor {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (s : Finset (Fin m)) (t : Finset (Fin n)) (h : s.card = t.card) :
    filteredMinor A s t h = sortedMinor A s t h := by
  ext i j
  simp only [filteredMinor, sortedMinor, filterFinRange_eq_sort]

def laplaceDet : (n : ℕ) → Matrix (Fin n) (Fin n) ℤ → ℤ
  | 0, _ => 1
  | n + 1, A => ∑ j : Fin (n + 1), (-1) ^ j.val * A 0 j *
      laplaceDet n (A.submatrix Fin.succ j.succAbove)

theorem laplaceDet_eq_det : ∀ n A, laplaceDet n A = A.det := by
  intro n
  induction n with
  | zero => intro A; simp [laplaceDet]
  | succ n ih =>
      intro A
      rw [laplaceDet, Matrix.det_succ_row_zero]
      apply Finset.sum_congr rfl
      intro j _
      rw [ih]

def r10Small : Matrix (Fin 5) (Fin 5) ℤ :=
  ![![0,0,1,1,1], ![-1,1,0,0,1], ![1,0,-1,0,-1],
    ![0,-1,0,-1,-1], ![-1,1,1,1,1]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r10Small_certificate : ∀ s t h,
    |laplaceDet s.card (filteredMinor r10Small s t h)| ≤ 1 := by decide +kernel

theorem r10Small_totallyUnimodular : r10Small.IsTotallyUnimodular := by
  apply totallyUnimodular_of_orderedMinors
  intro s t h
  rw [← sortedMinor_eq_orderedMinor, ← filteredMinor_eq_sortedMinor, ← laplaceDet_eq_det]
  exact r10Small_certificate s t h

end Unimodular.FiniteMatrixCertificates

namespace Unimodular.ExplicitR10
open Unimodular.FiniteMatrixCertificates

def extraColumns : Matrix (Fin 3) (Fin 5) ℤ :=
  fun i => Pi.single (Fin.castLE (by decide : 3 ≤ 5) i) (-1)

def seedColumn : Fin 8 → Fin 5 ⊕ Fin 3 :=
  ![Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4]

def seed : Matrix (Fin 5) (Fin 8) ℤ :=
  (r10Small.transpose.fromRows extraColumns).transpose.submatrix id seedColumn

def rowSelection : Fin 13 → Fin 5 ⊕ Fin 8 :=
  ![Sum.inl 0, Sum.inr 0, Sum.inl 1, Sum.inr 1, Sum.inl 2, Sum.inr 2,
    Sum.inl 3, Sum.inl 4, Sum.inr 3, Sum.inr 4, Sum.inr 5, Sum.inr 6, Sum.inr 7]

theorem rays_eq_extended_seed :
    rays = (seed.fromRows (1 : Matrix (Fin 8) (Fin 8) ℤ)).submatrix rowSelection id := by decide

theorem rays_totallyUnimodular : rays.IsTotallyUnimodular := by
  have he : (r10Small.transpose.fromRows extraColumns).IsTotallyUnimodular := by
    apply Matrix.IsTotallyUnimodular.fromRows_unitlike r10Small_totallyUnimodular.transpose
    intro _ i
    exact ⟨Fin.castLE (by decide : 3 ≤ 5) i, -1, rfl⟩
  have hs : seed.IsTotallyUnimodular :=
    Matrix.IsTotallyUnimodular.submatrix id seedColumn he.transpose
  have hf : (seed.fromRows (1 : Matrix (Fin 8) (Fin 8) ℤ)).IsTotallyUnimodular :=
    (Matrix.fromRows_one_isTotallyUnimodular_iff seed).2 hs
  rw [rays_eq_extended_seed]
  exact Matrix.IsTotallyUnimodular.submatrix rowSelection id hf

theorem all_ray_determinants (f : Fin 8 → Fin 13) :
    |(rays.submatrix f id).det| ≤ 1 := by
  obtain ⟨s, hs⟩ := (Matrix.isTotallyUnimodular_iff rays).1 rays_totallyUnimodular 8 f id
  rw [← hs]
  cases s <;> norm_num

#print axioms all_ray_determinants
end Unimodular.ExplicitR10
