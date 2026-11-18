module

public import Unimodular.SeriesParallelMatrixReduction

@[expose] public section

open scoped BigOperators
open Set

namespace Unimodular.SeriesParallel

noncomputable section

universe u v

/-- A rooted vertex represented in an actual integral lattice basis. -/
def basisVertex {I N : Type*} [AddCommGroup N] [Module ℤ N]
    (b : Module.Basis I ℤ N) : Option I → N
  | none => 0
  | some i => b i

/-- The integer columns of the full normalized configuration `[1 | A]`. -/
def matrixIntColumns {I J : Type*} [DecidableEq I] (A : I → J → ℤ) : I ⊕ J → I → ℤ
  | .inl i => Pi.single i 1
  | .inr j => fun i => A i j

/-- A literal integral incidence representation. The quantified basis is a
basis of the whole original lattice; no finite-index sublattice or real change
of coordinates is substituted for an integral isomorphism. -/
def IntegralGraphic {I J : Type*} [Fintype I] [DecidableEq I] (A : I → J → ℤ) : Prop :=
  ∃ b : Module.Basis I ℤ (I → ℤ), ∀ a : I ⊕ J,
    ∃ p q : Option I, matrixIntColumns A a = basisVertex b p - basisVertex b q

variable {I : Type u} {J : Type v} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]

/-- Extend an integer vector by zero in one distinguished row. -/
def rowLift (i : I) : ({k : I // k ≠ i} → ℤ) →ₗ[ℤ] (I → ℤ) where
  toFun := fun x k => if h : k = i then 0 else x ⟨k, h⟩
  map_add' := by intros; funext k; split_ifs <;> simp_all
  map_smul' := by intros; funext k; split_ifs <;> simp_all

@[simp] theorem rowLift_self (i : I) (x : {k : I // k ≠ i} → ℤ) : rowLift i x i = 0 := by
  simp [rowLift]

@[simp] theorem rowLift_other (i : I) (x : {k : I // k ≠ i} → ℤ)
    (k : {k : I // k ≠ i}) : rowLift i x k.val = x k := by
  simp [rowLift, k.property]

/-- The old basis-coordinate equivalence acts on the surviving coordinates and
fixes the distinguished coordinate. Its explicit inverse is integral. -/
def extendCoordinateEquiv (i : I)
    (b : Module.Basis {k : I // k ≠ i} ℤ ({k : I // k ≠ i} → ℤ)) :
    (I → ℤ) ≃ₗ[ℤ] (I → ℤ) where
  toFun := fun x k => if h : k = i then x i else b.equivFun (fun r => x r.val) ⟨k, h⟩
  invFun := fun x k => if h : k = i then x i else b.equivFun.symm (fun r => x r.val) ⟨k, h⟩
  left_inv := by
    intro x
    have ht : (fun r : {k : I // k ≠ i} =>
        (if h : r.val = i then x i else b.equivFun (fun t => x t.val) ⟨r.val, h⟩)) =
        b.equivFun (fun t => x t.val) := by
      funext r
      simp [r.property]
    funext k
    dsimp only
    by_cases hk : k = i
    · subst k
      simp
    · rw [dif_neg hk, ht, b.equivFun.symm_apply_apply]
  right_inv := by
    intro x
    have ht : (fun r : {k : I // k ≠ i} =>
        (if h : r.val = i then x i else b.equivFun.symm (fun t => x t.val) ⟨r.val, h⟩)) =
        b.equivFun.symm (fun t => x t.val) := by
      funext r
      simp [r.property]
    funext k
    dsimp only
    by_cases hk : k = i
    · subst k
      simp
    · rw [dif_neg hk, ht, b.equivFun.apply_symm_apply]
  map_add' := by
    intro x y
    funext k
    simp only [Pi.add_apply]
    by_cases hk : k = i
    · simp [hk]
    · simp only [dif_neg hk]
      exact congrFun (map_add b.equivFun (fun r => x r.val) (fun r => y r.val)) ⟨k, hk⟩
  map_smul' := by
    intro c x
    funext k
    simp only [RingHom.id_apply, Pi.smul_apply]
    by_cases hk : k = i
    · simp [hk]
    · simp only [dif_neg hk]
      exact congrFun (map_smul b.equivFun c (fun r => x r.val)) ⟨k, hk⟩

@[simp] theorem extendCoordinateEquiv_apply (i : I)
    (b : Module.Basis {k : I // k ≠ i} ℤ ({k : I // k ≠ i} → ℤ))
    (x : I → ℤ) (k : I) : extendCoordinateEquiv i b x k =
      if h : k = i then x i else b.equivFun (fun r => x r.val) ⟨k,h⟩ := rfl

/-- Adjoin the distinguished unit vector to a basis of the surviving-coordinate
lattice. This is an actual integral basis of all coordinates. -/
def extendBasis (i : I)
    (b : Module.Basis {k : I // k ≠ i} ℤ ({k : I // k ≠ i} → ℤ)) :
    Module.Basis I ℤ (I → ℤ) := Module.Basis.ofEquivFun (extendCoordinateEquiv i b)

@[simp] theorem extendBasis_repr_self (i : I)
    (b : Module.Basis {k : I // k ≠ i} ℤ ({k : I // k ≠ i} → ℤ)) (x : I → ℤ) :
    (extendBasis i b).repr x i = x i := by
  simp [extendBasis, Module.Basis.ofEquivFun_repr_apply, extendCoordinateEquiv]

@[simp] theorem extendBasis_self (i : I)
    (b : Module.Basis {k : I // k ≠ i} ℤ ({k : I // k ≠ i} → ℤ)) :
    extendBasis i b i = Pi.single i 1 := by
  apply (extendBasis i b).repr.injective
  ext k
  rw [Module.Basis.repr_self_apply]
  by_cases hk : k = i
  · simp [hk]
  · have ht : (fun r : {k : I // k ≠ i} => (Pi.single i (1 : ℤ) : I → ℤ) r.val) = 0 := by
      funext r
      simp [Pi.single_apply, r.property, (Ne.symm r.property)]
    simp only [extendBasis, Module.Basis.ofEquivFun_repr_apply, extendCoordinateEquiv_apply]
    rw [dif_neg hk, ht, map_zero]
    simp [Ne.symm hk]

@[simp] theorem extendBasis_other (i : I)
    (b : Module.Basis {k : I // k ≠ i} ℤ ({k : I // k ≠ i} → ℤ))
    (k : {k : I // k ≠ i}) : extendBasis i b k.val = rowLift i (b k) := by
  apply (extendBasis i b).repr.injective
  ext r
  rw [Module.Basis.repr_self_apply]
  by_cases hr : r = i
  · subst r
    simp [k.property, (Ne.symm k.property)]
  · have ht : (fun r : {k : I // k ≠ i} => rowLift i (b k) r.val) = b k := by
      funext r
      simp
    simp only [extendBasis, Module.Basis.ofEquivFun_repr_apply, extendCoordinateEquiv_apply]
    rw [dif_neg hr, ht]
    simp [Module.Basis.equivFun_apply, Module.Basis.repr_self_apply,
      Finsupp.single_apply, Subtype.ext_iff, eq_comm]

/-- Lifted old vertices retain exactly their represented lattice vectors. -/
theorem extendBasis_vertex (i : I)
    (b : Module.Basis {k : I // k ≠ i} ℤ ({k : I // k ≠ i} → ℤ))
    (p : Option {k : I // k ≠ i}) :
    basisVertex (extendBasis i b) (p.map Subtype.val) = rowLift i (basisVertex b p) := by
  cases p <;> simp [basisVertex]

/-- Subdividing a selected old edge adjoins a new vertex equal to the new unit
direction plus its old source vertex. The corresponding basis change is the
previously proved integral pivot. -/
def seriesBasis (i : I)
    (b : Module.Basis {k : I // k ≠ i} ℤ ({k : I // k ≠ i} → ℤ))
    (p : Option {k : I // k ≠ i}) (e : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)) :
    Module.Basis I ℤ (I → ℤ) :=
  (pivotBasis (extendBasis i b) (Pi.single i 1 + rowLift i (basisVertex b p)) i
    (Or.inl (by simp))).map e

@[simp] theorem seriesBasis_self (i : I)
    (b : Module.Basis {k : I // k ≠ i} ℤ ({k : I // k ≠ i} → ℤ))
    (p : Option {k : I // k ≠ i}) (e : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)) :
    seriesBasis i b p e i = e (Pi.single i 1) + e (rowLift i (basisVertex b p)) := by
  simp [seriesBasis]

@[simp] theorem seriesBasis_other (i : I)
    (b : Module.Basis {k : I // k ≠ i} ℤ ({k : I // k ≠ i} → ℤ))
    (p : Option {k : I // k ≠ i}) (e : (I → ℤ) ≃ₗ[ℤ] (I → ℤ))
    (k : {k : I // k ≠ i}) : seriesBasis i b p e k.val = e (rowLift i (b k)) := by
  simp [seriesBasis, pivotBasis_other, k.property]

theorem seriesBasis_vertex (i : I)
    (b : Module.Basis {k : I // k ≠ i} ℤ ({k : I // k ≠ i} → ℤ))
    (p q : Option {k : I // k ≠ i}) (e : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)) :
    basisVertex (seriesBasis i b p e) (q.map Subtype.val) =
      e (rowLift i (basisVertex b q)) := by
  cases q <;> simp [basisVertex]

/-- Diagonal multiplication of one integral coordinate by a unit sign. -/
def scaleRow (i : I) (s : ℤ) (hs : s = 1 ∨ s = -1) :
    (I → ℤ) ≃ₗ[ℤ] (I → ℤ) where
  toFun := fun x k => if k = i then s * x k else x k
  invFun := fun x k => if k = i then s * x k else x k
  left_inv := by intro x; funext k; rcases hs with rfl | rfl <;> by_cases hk : k = i <;> simp [hk]
  right_inv := by intro x; funext k; rcases hs with rfl | rfl <;> by_cases hk : k = i <;> simp [hk]
  map_add' := by intro x y; funext k; by_cases hk : k = i <;> simp [hk, mul_add]
  map_smul' := by intro a x; funext k; by_cases hk : k = i <;> simp [hk, mul_left_comm]

/-- An integral elementary row shear. The distinctness hypothesis is precisely
what makes subtraction of the same multiple its inverse. -/
def shearRow (i k : I) (hik : i ≠ k) (s : ℤ) :
    (I → ℤ) ≃ₗ[ℤ] (I → ℤ) where
  toFun := fun x r => if r = i then x r + s * x k else x r
  invFun := fun x r => if r = i then x r - s * x k else x r
  left_inv := by intro x; funext r; by_cases hr : r = i <;> simp [hr, hik, hik.symm]
  right_inv := by intro x; funext r; by_cases hr : r = i <;> simp [hr, hik, hik.symm]
  map_add' := by intro x y; funext r; by_cases hr : r = i <;> simp [hr, mul_add] <;> ring
  map_smul' := by intro a x; funext r; by_cases hr : r = i <;> simp [hr, mul_add] <;> ring

private theorem integralGraphic_column_extension (A : I → J → ℤ) (j : J)
    (b : Module.Basis I ℤ (I → ℤ))
    (hold : ∀ a : I ⊕ {k : J // k ≠ j}, ∃ p q : Option I,
      matrixIntColumns (fun (i : I) (k : {k : J // k ≠ j}) => A i k.val) a =
        basisVertex b p - basisVertex b q)
    (p q : Option I) (hnew : matrixIntColumns A (.inr j) = basisVertex b p - basisVertex b q) :
    IntegralGraphic A := by
  refine ⟨b, ?_⟩
  intro a
  by_cases ha : a = .inr j
  · exact ha ▸ ⟨p, q, hnew⟩
  have hm : a ∈ Set.range (eraseColumnLabels (I := I) j) := by
    rw [range_eraseColumnLabels]
    simpa using ha
  obtain ⟨a, rfl⟩ := hm
  obtain ⟨p, q, hpq⟩ := hold a
  refine ⟨p, q, ?_⟩
  cases a <;> exact hpq

/-- Adjoining a loop column preserves a literal integral incidence representation. -/
theorem IntegralGraphic.addZeroColumn {A : I → J → ℤ} (j : J)
    (h : IntegralGraphic (fun (i : I) (k : {k : J // k ≠ j}) => A i k.val))
    (hz : ∀ i, A i j = 0) : IntegralGraphic A := by
  obtain ⟨b, hb⟩ := h
  apply integralGraphic_column_extension A j b hb none none
  ext i
  simp [matrixIntColumns, basisVertex, hz i]

/-- Adding either orientation of an existing edge preserves the actual integer
incidence representation. -/
theorem IntegralGraphic.addSignedColumn {A : I → J → ℤ} (j : J)
    (h : IntegralGraphic (fun (i : I) (k : {k : J // k ≠ j}) => A i k.val))
    (a : I ⊕ {k : J // k ≠ j}) (s : ℤ) (hs : s = 1 ∨ s = -1)
    (heq : matrixIntColumns A (.inr j) =
      s • matrixIntColumns (fun (i : I) (k : {k : J // k ≠ j}) => A i k.val) a) :
    IntegralGraphic A := by
  obtain ⟨b, hb⟩ := h
  obtain ⟨p, q, hpq⟩ := hb a
  rcases hs with rfl | rfl
  · apply integralGraphic_column_extension A j b hb p q
    simpa [hpq] using heq
  · apply integralGraphic_column_extension A j b hb q p
    simpa [hpq, neg_sub] using heq

/-- A zero row adjoins an independent bridge direction. All other actual
vectors lift by zero, and the enlarged vertex basis is integral. -/
theorem IntegralGraphic.addZeroRow {A : I → J → ℤ} (i : I)
    (h : IntegralGraphic (fun k : {k : I // k ≠ i} => A k.val))
    (hz : ∀ j, A i j = 0) : IntegralGraphic A := by
  obtain ⟨b, hb⟩ := h
  let d := extendBasis i b
  have hold : ∀ a : {k : I // k ≠ i} ⊕ J,
      matrixIntColumns A (eraseRowLabels i a) =
        rowLift i (matrixIntColumns (fun k : {k : I // k ≠ i} => A k.val) a) := by
    intro a
    cases a with
    | inl k =>
      ext r
      by_cases hr : r = i
      · simp [matrixIntColumns, eraseRowLabels_inl, eraseRowLabels_inr, rowLift, hr, Pi.single_apply,
          k.property, (Ne.symm k.property)]
      · simp [matrixIntColumns, eraseRowLabels_inl, eraseRowLabels_inr, rowLift, hr, (Ne.symm hr), Pi.single_apply,
          Subtype.ext_iff, eq_comm]
    | inr j =>
      ext r
      by_cases hr : r = i <;> simp [matrixIntColumns, eraseRowLabels_inl, eraseRowLabels_inr, rowLift, hr, hz]
  refine ⟨d, ?_⟩
  intro a
  by_cases ha : a = .inl i
  · subst a
    exact ⟨some i, none, by simp [d, basisVertex, matrixIntColumns]⟩
  have hm : a ∈ Set.range (eraseRowLabels (J := J) i) := by
    rw [range_eraseRowLabels]
    simpa using ha
  obtain ⟨a, rfl⟩ := hm
  obtain ⟨p, q, hpq⟩ := hb a
  refine ⟨p.map Subtype.val, q.map Subtype.val, ?_⟩
  rw [hold, hpq, map_sub]
  simp only [d, extendBasis_vertex]

/-- The exact vector-level series operation. A primitive new direction and a
lift of the old selected edge are split into two incidence vectors through one
new vertex. The linear equivalence is integral on the whole lattice. -/
theorem IntegralGraphic.seriesRow {A : I → J → ℤ} (i : I)
    (h : IntegralGraphic (fun k : {k : I // k ≠ i} => A k.val))
    (selected : {k : I // k ≠ i} ⊕ J)
    (e : (I → ℤ) ≃ₗ[ℤ] (I → ℤ))
    (hunit : Pi.single i (1 : ℤ) = e (Pi.single i 1) ∨
      Pi.single i (1 : ℤ) = -e (Pi.single i 1))
    (hselected : matrixIntColumns A (eraseRowLabels i selected) = e (Pi.single i 1) +
      e (rowLift i (matrixIntColumns (fun k : {k : I // k ≠ i} => A k.val) selected)))
    (hothers : ∀ a, a ≠ selected → matrixIntColumns A (eraseRowLabels i a) =
      e (rowLift i (matrixIntColumns (fun k : {k : I // k ≠ i} => A k.val) a))) :
    IntegralGraphic A := by
  obtain ⟨b, hb⟩ := h
  obtain ⟨p, q, hpq⟩ := hb selected
  let d := seriesBasis i b p e
  have hvi : basisVertex d (some i) = e (Pi.single i 1) +
      e (rowLift i (basisVertex b p)) := seriesBasis_self i b p e
  have hvertex (q : Option {k : I // k ≠ i}) :
      basisVertex d (q.map Subtype.val) = e (rowLift i (basisVertex b q)) :=
    seriesBasis_vertex i b p q e
  have hnew : ∃ s t : Option I, Pi.single i (1 : ℤ) = basisVertex d s - basisVertex d t := by
    rcases hunit with hunit | hunit
    · refine ⟨some i, p.map Subtype.val, ?_⟩
      calc
        Pi.single i (1 : ℤ) = e (Pi.single i 1) := hunit
        _ = basisVertex d (some i) - basisVertex d (p.map Subtype.val) := by
          rw [hvi, hvertex]
          abel
    · refine ⟨p.map Subtype.val, some i, ?_⟩
      calc
        Pi.single i (1 : ℤ) = -e (Pi.single i 1) := hunit
        _ = basisVertex d (p.map Subtype.val) - basisVertex d (some i) := by
          rw [hvi, hvertex]
          abel
  have hold : ∀ a : {k : I // k ≠ i} ⊕ J,
      ∃ s t : Option I, matrixIntColumns A (eraseRowLabels i a) =
        basisVertex d s - basisVertex d t := by
    intro a
    by_cases ha : a = selected
    · subst a
      refine ⟨some i, q.map Subtype.val, ?_⟩
      rw [hselected, hpq, map_sub, map_sub, hvi, hvertex]
      abel
    · obtain ⟨s, t, hst⟩ := hb a
      refine ⟨s.map Subtype.val, t.map Subtype.val, ?_⟩
      rw [hothers a ha, hst, map_sub, map_sub]
      rw [hvertex, hvertex]
  refine ⟨d, ?_⟩
  intro a
  by_cases ha : a = .inl i
  · subst a
    exact hnew
  have hm : a ∈ Set.range (eraseRowLabels (J := J) i) := by
    rw [range_eraseRowLabels]
    simpa using ha
  obtain ⟨a, rfl⟩ := hm
  exact hold a

/-- The literal incidence operation for a pendant row, including its unit sign. -/
theorem IntegralGraphic.pendantRow {A : I → J → ℤ} (hA : SmallMinors A) (i : I) (j : J)
    (h : IntegralGraphic (fun k : {k : I // k ≠ i} => A k.val))
    (hi : ∀ l, A i l ≠ 0 ↔ l = j) : IntegralGraphic A := by
  have hs : A i j = 1 ∨ A i j = -1 := by
    have hn := (hi j).mpr rfl
    have hb := abs_le.mp (hA.entry i j)
    omega
  apply h.seriesRow i (.inr j) (scaleRow i (A i j) hs)
  · rcases hs with hs | hs
    · left
      ext k
      by_cases hk : k = i <;> simp [scaleRow, hs, hk]
    · right
      ext k
      by_cases hk : k = i <;> simp [scaleRow, hs, hk, Pi.single_apply]
  · ext k
    by_cases hk : k = i <;>
      simp [matrixIntColumns, eraseRowLabels_inl, eraseRowLabels_inr, scaleRow, rowLift, hk, Pi.single_apply]
  · intro a ha
    cases a with
    | inl r =>
      ext k
      by_cases hk : k = i
      · simp [matrixIntColumns, eraseRowLabels_inl, eraseRowLabels_inr, scaleRow, rowLift, hk,
          Pi.single_apply, r.property, (Ne.symm r.property), Subtype.ext_iff, eq_comm]
      · simp [matrixIntColumns, eraseRowLabels_inl, eraseRowLabels_inr, scaleRow, rowLift, hk,
          (Ne.symm hk), Pi.single_apply, r.property, (Ne.symm r.property), Subtype.ext_iff, eq_comm]
    | inr l =>
      have hlj : l ≠ j := by simpa using ha
      have hz : A i l = 0 := by
        by_contra hn
        exact hlj ((hi l).mp hn)
      ext k
      by_cases hk : k = i <;>
        simp [matrixIntColumns, eraseRowLabels_inl, eraseRowLabels_inr, scaleRow, rowLift, hk, hz]

/-- The unit diagonal change followed by the row shear needed for actual twin
rows. Its determinant is a unit because both displayed maps are integral
linear equivalences. -/
def twinRowEquiv (i k : I) (hik : i ≠ k) (s : ℤ) (hs : s = 1 ∨ s = -1) :
    (I → ℤ) ≃ₗ[ℤ] (I → ℤ) :=
  (scaleRow i (-s) (by rcases hs with rfl | rfl <;> simp)).trans (shearRow i k hik s)

theorem twinRowEquiv_apply (i k : I) (hik : i ≠ k) (s : ℤ) (hs : s = 1 ∨ s = -1)
    (x : I → ℤ) (r : I) :
    twinRowEquiv i k hik s hs x r = if r = i then -s * x i + s * x k else x r := by
  by_cases hr : r = i
  · subst r
    simp [twinRowEquiv, scaleRow, shearRow, hik, hik.symm]
  · simp [twinRowEquiv, scaleRow, shearRow, hr]

/-- The vector-level series operation for twin rows. The required shear is
constructed explicitly, so equality of underlying matroids is never substituted
for equality of the signed primitive vectors. -/
theorem IntegralGraphic.twinRows {A : I → J → ℤ} (hA : SmallMinors A)
    (i k : I) (hik : i ≠ k)
    (h : IntegralGraphic (fun r : {r : I // r ≠ i} => A r.val))
    (hsupport : ∀ j, A i j ≠ 0 ↔ A k j ≠ 0) : IntegralGraphic A := by
  obtain ⟨s, hs, hsign⟩ := hA.row_sign i k hsupport
  apply h.seriesRow i (.inl ⟨k, hik.symm⟩) (twinRowEquiv i k hik s hs)
  · rcases hs with hs | hs
    · right
      ext r
      by_cases hr : r = i <;>
        simp [twinRowEquiv_apply, hs, hr, Pi.single_apply, hik, hik.symm]
    · left
      ext r
      by_cases hr : r = i <;>
        simp [twinRowEquiv_apply, hs, hr, Pi.single_apply, hik, hik.symm]
  · ext r
    by_cases hr : r = i
    · simp [matrixIntColumns, eraseRowLabels_inl, eraseRowLabels_inr, twinRowEquiv_apply, rowLift, hr,
        Pi.single_apply, hik, hik.symm, Subtype.ext_iff]
    · simp [matrixIntColumns, eraseRowLabels_inl, eraseRowLabels_inr, twinRowEquiv_apply, rowLift, hr, (Ne.symm hr),
        Pi.single_apply, Subtype.ext_iff, eq_comm]
  · intro a ha
    cases a with
    | inl r =>
      have hrk : r.val ≠ k := by
        intro hval
        apply ha
        exact congrArg Sum.inl (Subtype.ext hval)
      ext t
      by_cases ht : t = i
      · simp [matrixIntColumns, eraseRowLabels_inl, eraseRowLabels_inr, twinRowEquiv_apply, rowLift, ht,
          Pi.single_apply, r.property, (Ne.symm r.property), hik, hik.symm,
          hrk, hrk.symm, Subtype.ext_iff]
      · simp [matrixIntColumns, eraseRowLabels_inl, eraseRowLabels_inr, twinRowEquiv_apply, rowLift, ht, (Ne.symm ht),
          Pi.single_apply, Subtype.ext_iff, eq_comm]
    | inr j =>
      ext r
      by_cases hr : r = i
      · simp [matrixIntColumns, eraseRowLabels_inl, eraseRowLabels_inr, twinRowEquiv_apply, rowLift, hr,
          hik.symm, hsign j]
      · simp [matrixIntColumns, eraseRowLabels_inl, eraseRowLabels_inr, twinRowEquiv_apply, rowLift, hr]

/-- The full integral reconstruction by arbitrary-size matrix elimination. -/
theorem matrix_integralGraphic_aux :
    ∀ n : ℕ, ∀ (I : Type u) (J : Type v) [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J], Fintype.card I + Fintype.card J = n →
      ∀ A : I → J → ℤ, SmallMinors A → MatrixForbidden A → IntegralGraphic A := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro I J _ _ _ _ hcard A hA hforbid
    have row (i : I) : IntegralGraphic (fun k : {k : I // k ≠ i} => A k.val) := by
      apply ih (Fintype.card {k : I // k ≠ i} + Fintype.card J) ?_
        {k : I // k ≠ i} J rfl _ (hA.eraseRow i) (hforbid.eraseRow i)
      have hh : Fintype.card {k : I // k ≠ i} < Fintype.card I :=
        Fintype.card_subtype_lt (x := i) (by simp)
      omega
    have column (j : J) :
        IntegralGraphic (fun (i : I) (k : {k : J // k ≠ j}) => A i k.val) := by
      apply ih (Fintype.card I + Fintype.card {k : J // k ≠ j}) ?_
        I {k : J // k ≠ j} rfl _ (hA.eraseColumn j) (hforbid.eraseColumn j)
      have hh : Fintype.card {k : J // k ≠ j} < Fintype.card J :=
        Fintype.card_subtype_lt (x := j) (by simp)
      omega
    rcases isEmpty_or_nonempty (I ⊕ J) with he | hne
    · letI := he
      exact ⟨Pi.basisFun ℤ I, fun a => isEmptyElim a⟩
    · letI := hne
      cases matrix_has_reduction A hforbid with
      | zeroRow i hi => exact (row i).addZeroRow i hi
      | zeroColumn j hj => exact (column j).addZeroColumn j hj
      | pendantRow i j hi => exact IntegralGraphic.pendantRow hA i j (row i) hi
      | pendantColumn j i hj =>
        have hs : A i j = 1 ∨ A i j = -1 := by
          have hn := (hj i).mpr rfl
          have hb := abs_le.mp (hA.entry i j)
          omega
        apply (column j).addSignedColumn j (.inl i) (A i j) hs
        ext k
        by_cases hk : k = i
        · simp [matrixIntColumns, hk, Pi.single_apply]
        · have hz : A k j = 0 := by
            by_contra hn
            exact hk ((hj k).mp hn)
          simp [matrixIntColumns, hz, hk, (Ne.symm hk), Pi.single_apply]
      | twinRows i k hik hs => exact IntegralGraphic.twinRows hA i k hik (row i) hs
      | twinColumns j l hjl hs =>
        obtain ⟨s, hsunit, hsign⟩ := hA.column_sign j l hs
        apply (column j).addSignedColumn j (.inr ⟨l, hjl.symm⟩) s hsunit
        ext i
        simpa only [matrixIntColumns, Pi.smul_apply, smul_eq_mul] using hsign i

/-- Every normalized matrix meeting the proved fundamental-graph conditions
has an actual integral incidence realization, in all ranks and with arbitrary
signs, repeated labels, antipodal vectors, and zero columns. -/
theorem matrix_integralGraphic (A : I → J → ℤ) (hA : SmallMinors A)
    (hforbid : MatrixForbidden A) : IntegralGraphic A :=
  matrix_integralGraphic_aux (Fintype.card I + Fintype.card J) I J rfl A hA hforbid

#print axioms Unimodular.SeriesParallel.matrix_integralGraphic

end
end Unimodular.SeriesParallel
