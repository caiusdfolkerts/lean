module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import paper_verification.literal015
public import paper_verification.literal005
public import paper_verification.literal000
public import paper_verification.literal013
public import Mathlib.Data.Fin.Rev
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import paper_verification.literal007
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import paper_verification.literal014
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.Tactic
public import Mathlib.RingTheory.Nilpotent.Exp
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Data.Finset.Max
public import paper_verification.literal004
public import paper_verification.literal008
public import paper_verification.literal010
public import paper_verification.literal011
public import paper_verification.literal012

set_option Elab.async false

section TAF_LiteralSource_0648
/- Original module: TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Complete -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The Schur polynomial of a one-row shape

A Young diagram with at most one row has one cell in each of its columns, and a semistandard
tableau of that shape is exactly a weakly increasing list of letters, one per column: the entries
of a row increase weakly rightwards, and there is no column condition to satisfy.  So a bounded
tableau of a one-row shape is nothing but the **multiset** of the letters it uses, and its weight
is the multiplicity function of that multiset.  Summing over the tableaux therefore sums the
monomial `∏ᵢ xᵢ ^ (multiplicity of i)` over every multiset of letters of the right size, which is
`MvPolynomial.hsymm`:

`TauCeti.diagramSchurPoly N R μ = MvPolynomial.hsymm (Fin N) R μ.card` for `μ.colLen 0 ≤ 1`.

For partitions this reads `s_{(n)} = h_n`, `TauCeti.schurPoly_indiscrete`, the shape `(n)` being
Mathlib's `Nat.Partition.indiscrete` at the top of the dominance order: a single row of `n` cells
for `n > 0`, and the empty diagram for `n = 0`.  It is the `1 × 1` instance of the Jacobi--Trudi
identity, whose general form expresses `s_μ` as a determinant of complete homogeneous symmetric
polynomials, and the character-level shadow of `𝕊^{(n)}(V) = Symⁿ V`.  It is dual to
`TauCeti.schurPoly_ones`, the one-column identity `s_{(1ⁿ)} = e_n`.

The identification runs through `TauCeti.BoundedSSYT.rowMultisetEquiv`, the bijection between the
bounded tableaux of a one-row shape and the multisets of letters of size the number of columns.
Both directions are explicit: a tableau is sent to the multiset
`TauCeti.BoundedSSYT.rowMultiset` of the entries of its row, and a multiset is sent back to the
tableau `TauCeti.BoundedSSYT.ofRowMultiset` that lists it in increasing order, along the sorted
word `Multiset.sort` produces.

Unlike the one-column case, where the letters of a tableau are pairwise distinct and form a
`Finset`, a row may repeat a letter, so the enumeration `Finset.orderEmbOfFin` is unavailable and
the sorted word is what carries the construction.  Its two characterising properties, that it is
weakly increasing and that it has the right multiset of letters, determine it
(`List.Perm.eq_of_pairwise'`), which is how the round trip from a tableau back to itself is
proved.

Stability is another corollary: setting the last of `n + 1` variables to `0` sends `h_d` in
`n + 1` variables to `h_d` in `n` variables (`TauCeti.aeval_snoc_zero_hsymm`), because it does so
for every Schur polynomial (`TauCeti.aeval_snoc_zero_diagramSchurPoly`).  The same holds for the
integer-indexed `TauCeti.hsymmInt` (`TauCeti.aeval_snoc_zero_hsymmInt`).

Symmetry is a corollary rather than an input: the one-row case falls out of
`TauCeti.schurPoly_indiscrete` and the symmetry of the complete homogeneous symmetric polynomials,
without the Bender--Knuth involution that `TauCeti.schurPoly_isSymmetric` needs in general.

## Main definitions

* `TauCeti.BoundedSSYT.rowEntry`: the letter a bounded tableau puts in a given column of its first
  row.
* `TauCeti.BoundedSSYT.rowMultiset`: the multiset of letters used by the first row of a bounded
  tableau.
* `TauCeti.BoundedSSYT.ofRowMultiset`: the one-row tableau listing a given multiset of letters in
  increasing order.
* `TauCeti.BoundedSSYT.rowMultisetEquiv`: the bijection between the bounded tableaux of a one-row
  shape and the multisets of letters of size the number of columns.

## Main results

* `TauCeti.BoundedSSYT.weight_eq_toFinsupp`: the weight of a one-row tableau is the multiplicity
  function of the multiset of letters it uses.
* `TauCeti.diagramSchurPoly_eq_hsymm_of_colLen_le_one`: the Schur polynomial of a one-row shape is
  a complete homogeneous symmetric polynomial.
* `TauCeti.schurPoly_indiscrete`: `s_{(n)} = h_n`.
* `TauCeti.aeval_snoc_zero_hsymm`, `TauCeti.aeval_snoc_zero_hsymmInt`: stability of the complete
  homogeneous symmetric polynomials under setting the last variable to `0`.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 2.2.
* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 3, where `s_{(n)} = h_n` sits beside `s_{(1ⁿ)} = e_n` as the first examples of a Schur
  function.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 7.
-/

public section

namespace TauCeti

open Finset MvPolynomial

namespace BoundedSSYT

variable {N : ℕ} {μ : YoungDiagram}

/-! ### The first row of a bounded tableau -/

/-- The letter a bounded tableau puts in column `j` of its first row.  The shape enters only
through the length `μ.rowLen 0` of its first row, so this reads the first row of any bounded
tableau; for a one-row shape it reads the whole tableau. -/
def rowEntry (T : BoundedSSYT N μ) (j : Fin (μ.rowLen 0)) : Fin N :=
  ⟨T.1 0 j, entry_lt T (YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt)⟩

@[simp]
theorem rowEntry_val (T : BoundedSSYT N μ) (j : Fin (μ.rowLen 0)) :
    (rowEntry T j : ℕ) = T.1 0 j :=
  (rfl)

/-- **The first row of a bounded tableau increases weakly**, entries increasing weakly rightwards
along every row of a semistandard tableau. -/
theorem rowEntry_monotone (T : BoundedSSYT N μ) : Monotone (rowEntry T) := by
  intro j₁ j₂ hj
  rw [Fin.le_def, rowEntry_val, rowEntry_val]
  rcases Nat.eq_or_lt_of_le (Fin.le_def.mp hj) with h | h
  · exact le_of_eq (congrArg (T.1 0) h)
  · exact T.1.row_weak h (YoungDiagram.mem_iff_lt_rowLen.mpr j₂.isLt)

/-- The multiset of letters the first row of a bounded tableau uses, with multiplicity. -/
def rowMultiset (T : BoundedSSYT N μ) : Multiset (Fin N) :=
  Finset.univ.val.map (rowEntry T)

/-- A letter is used by the first row of a bounded tableau exactly when some column carries it. -/
@[simp]
theorem mem_rowMultiset {T : BoundedSSYT N μ} {x : Fin N} :
    x ∈ rowMultiset T ↔ ∃ j, rowEntry T j = x := by
  simp [rowMultiset]

/-- **The first row of a bounded tableau uses one letter per column**, counted with
multiplicity. -/
@[simp]
theorem card_rowMultiset (T : BoundedSSYT N μ) :
    Multiset.card (rowMultiset T) = μ.rowLen 0 := by
  simp [rowMultiset]

/-! ### The weight of a one-row tableau -/

/-- The cells of a one-row shape carrying a given letter, read off the columns that carry it. -/
private theorem filter_cells_eq_image (h : μ.colLen 0 ≤ 1) (T : BoundedSSYT N μ) (y : Fin N) :
    (μ.cells.filter fun c => T.1 c.1 c.2 = (y : ℕ))
      = (Finset.univ.filter fun j : Fin (μ.rowLen 0) => rowEntry T j = y).image
          fun j : Fin (μ.rowLen 0) => (0, (j : ℕ)) := by
  ext c
  obtain ⟨i, j⟩ := c
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
    YoungDiagram.mem_cells, YoungDiagram.mem_iff_of_colLen_le_one h, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨rfl, hj⟩, hT⟩
    exact ⟨⟨j, hj⟩, Fin.ext hT, rfl, rfl⟩
  · rintro ⟨k, hk, rfl, rfl⟩
    exact ⟨⟨rfl, k.isLt⟩, congrArg Fin.val hk⟩

/-- **The weight of a one-row tableau counts the letters of its row**: a letter is used as often
as it occurs in the row. -/
theorem weight_apply_eq_count (h : μ.colLen 0 ≤ 1) (T : BoundedSSYT N μ) (y : Fin N) :
    weight T y = Multiset.count y (rowMultiset T) := by
  rw [weight_apply, SemistandardYoungTableau.content_apply, filter_cells_eq_image h T y,
    Finset.card_image_of_injective _ fun a b hab => Fin.val_injective (congrArg Prod.snd hab),
    rowMultiset, Multiset.count_map]
  simp [Finset.card, Finset.filter_val, eq_comm]

/-- **The weight of a one-row tableau is the multiplicity function of the letters of its row.** -/
theorem weight_eq_toFinsupp (h : μ.colLen 0 ≤ 1) (T : BoundedSSYT N μ) :
    weight T = (rowMultiset T).toFinsupp := by
  ext y
  rw [weight_apply_eq_count h T y, Multiset.toFinsupp_apply]

/-! ### Recovering a one-row tableau from its letters -/

/-- A multiset of letters, listed in increasing order and read as natural numbers: the first row
of the tableau `TauCeti.BoundedSSYT.ofRowMultiset`.  Unlike the one-column case, a row may repeat
a letter, so this is a genuine sorted word rather than the monotone enumeration of a set.  It is
an implementation detail: the tableau it builds is characterised, representation-independently, by
the round trips `TauCeti.BoundedSSYT.rowMultiset_ofRowMultiset` and
`TauCeti.BoundedSSYT.ofRowMultiset_rowMultiset`. -/
private def rowList (s : Multiset (Fin N)) : List ℕ :=
  (s.map Fin.val).sort (· ≤ ·)

@[simp]
private theorem coe_rowList (s : Multiset (Fin N)) :
    ((rowList s : List ℕ) : Multiset ℕ) = s.map Fin.val :=
  Multiset.sort_eq _ _

@[simp]
private theorem length_rowList (s : Multiset (Fin N)) :
    (rowList s).length = Multiset.card s := by
  rw [rowList, Multiset.length_sort, Multiset.card_map]

private theorem pairwise_rowList (s : Multiset (Fin N)) : (rowList s).Pairwise (· ≤ ·) :=
  Multiset.pairwise_sort _ _

private theorem rowList_lt {s : Multiset (Fin N)} {x : ℕ} (hx : x ∈ rowList s) : x < N := by
  obtain ⟨y, -, rfl⟩ := Multiset.mem_map.mp ((Multiset.mem_sort _).mp hx)
  exact y.isLt

/-- **The one-row tableau listing a given multiset of letters in increasing order.**  The multiset
must have one letter per column of the shape; that is the hypothesis `hs`.  There is no column
condition to check, a one-row shape having at most one cell per column. -/
private def rowTableau (h : μ.colLen 0 ≤ 1) (s : Multiset (Fin N))
    (hs : Multiset.card s = μ.rowLen 0) : _root_.SemistandardYoungTableau μ where
  entry i j := if i = 0 then (rowList s).getD j 0 else 0
  row_weak' := by
    intro i j₁ j₂ hj hcell
    obtain ⟨rfl, hj₂⟩ := (YoungDiagram.mem_iff_of_colLen_le_one h).mp hcell
    have hlen : (rowList s).length = μ.rowLen 0 := (length_rowList s).trans hs
    rw [ite_eq_left rfl, ite_eq_left rfl, List.getD_eq_getElem _ _ (by omega),
      List.getD_eq_getElem _ _ (by omega)]
    exact List.pairwise_iff_getElem.mp (pairwise_rowList s) _ _ _ _ hj
  col_strict' := by
    intro i₁ i₂ j hi hcell
    obtain ⟨rfl, -⟩ := (YoungDiagram.mem_iff_of_colLen_le_one h).mp hcell
    exact absurd hi (Nat.not_lt_zero i₁)
  zeros' := by
    intro i j hcell
    by_cases hi : i = 0
    · subst hi
      have hlen : (rowList s).length = μ.rowLen 0 := (length_rowList s).trans hs
      have hj : ¬ j < μ.rowLen 0 := fun hj =>
        hcell ((YoungDiagram.mem_iff_of_colLen_le_one h).mpr ⟨rfl, hj⟩)
      rw [ite_eq_left rfl]
      exact List.getD_eq_default _ _ (by omega)
    · exact ite_eq_right hi

private theorem rowTableau_apply (h : μ.colLen 0 ≤ 1) (s : Multiset (Fin N))
    (hs : Multiset.card s = μ.rowLen 0) (i j : ℕ) :
    rowTableau h s hs i j = if i = 0 then (rowList s).getD j 0 else 0 :=
  (rfl)

/-- **The one-row tableau listing a given multiset of letters in increasing order**, as a bounded
tableau: the letters it uses come from the alphabet because they are letters of the alphabet. -/
def ofRowMultiset (h : μ.colLen 0 ≤ 1) (s : Multiset (Fin N))
    (hs : Multiset.card s = μ.rowLen 0) : BoundedSSYT N μ :=
  ⟨rowTableau h s hs, by
    intro i c hic
    obtain ⟨rfl, hc⟩ := (YoungDiagram.mem_iff_of_colLen_le_one h).mp hic
    have hlen : (rowList s).length = μ.rowLen 0 := (length_rowList s).trans hs
    rw [rowTableau_apply, ite_eq_left rfl, List.getD_eq_getElem _ _ (by omega)]
    exact rowList_lt (List.getElem_mem _)⟩

private theorem ofRowMultiset_apply (h : μ.colLen 0 ≤ 1) (s : Multiset (Fin N))
    (hs : Multiset.card s = μ.rowLen 0) (i j : ℕ) :
    (ofRowMultiset h s hs).1 i j = if i = 0 then (rowList s).getD j 0 else 0 :=
  rowTableau_apply h s hs i j

/-- The first row of `TauCeti.BoundedSSYT.ofRowMultiset` reads off the sorted word. -/
private theorem rowEntry_ofRowMultiset (h : μ.colLen 0 ≤ 1) (s : Multiset (Fin N))
    (hs : Multiset.card s = μ.rowLen 0) (j : Fin (μ.rowLen 0)) :
    (rowEntry (ofRowMultiset h s hs) j : ℕ) = (rowList s).getD (j : ℕ) 0 := by
  rw [rowEntry_val, ofRowMultiset_apply, ite_eq_left rfl]

/-- Reading a sorted word off column by column recovers it. -/
private theorem ofFn_getD_rowList (s : Multiset (Fin N)) (hs : Multiset.card s = μ.rowLen 0) :
    (List.ofFn fun j : Fin (μ.rowLen 0) => (rowList s).getD (j : ℕ) 0) = rowList s := by
  have hlen : (rowList s).length = μ.rowLen 0 := (length_rowList s).trans hs
  refine List.ext_getElem (by simp [hlen]) fun k hk hk' => ?_
  rw [List.getElem_ofFn, List.getD_eq_getElem _ _ hk']

/-- **Listing a multiset of letters along a row uses exactly those letters**: the multiset of
letters of `TauCeti.BoundedSSYT.ofRowMultiset h s hs` is `s` again. -/
@[simp]
theorem rowMultiset_ofRowMultiset (h : μ.colLen 0 ≤ 1) (s : Multiset (Fin N))
    (hs : Multiset.card s = μ.rowLen 0) : rowMultiset (ofRowMultiset h s hs) = s := by
  -- `rowEntry_ofRowMultiset` reads the entries one at a time, so it has to be bundled into a
  -- function equality before it can rewrite under `Multiset.map`.
  have hentries : Fin.val ∘ rowEntry (ofRowMultiset h s hs)
      = fun j : Fin (μ.rowLen 0) => (rowList s).getD (j : ℕ) 0 :=
    funext fun j => rowEntry_ofRowMultiset h s hs j
  refine Multiset.map_injective (Fin.val_injective (n := N)) ?_
  rw [rowMultiset, Multiset.map_map, hentries, Fin.univ_val_map, ofFn_getD_rowList s hs,
    coe_rowList]

/-- **The row of a one-row tableau is already sorted**, so it is the sorted word of its own
multiset of letters. -/
private theorem rowList_rowMultiset (T : BoundedSSYT N μ) :
    rowList (rowMultiset T) = List.ofFn fun j : Fin (μ.rowLen 0) => (T.1 0 j : ℕ) := by
  refine List.Perm.eq_of_pairwise' (pairwise_rowList _) ?_ ?_
  · rw [List.pairwise_ofFn]
    intro i j hij
    exact T.1.row_weak (Fin.lt_def.mp hij) (YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt)
  · rw [← Multiset.coe_eq_coe, coe_rowList, rowMultiset, Multiset.map_map, Fin.univ_val_map]
    rfl

/-- **A one-row tableau is determined by the letters it uses**: relisting the multiset of letters
of the row of `T` in increasing order recovers `T`. -/
@[simp]
theorem ofRowMultiset_rowMultiset (h : μ.colLen 0 ≤ 1) (T : BoundedSSYT N μ) :
    ofRowMultiset h (rowMultiset T) (card_rowMultiset T) = T := by
  refine Subtype.ext (_root_.SemistandardYoungTableau.ext fun i j => ?_)
  rw [ofRowMultiset_apply, rowList_rowMultiset]
  by_cases hij : (i, j) ∈ μ
  · obtain ⟨rfl, hj⟩ := (YoungDiagram.mem_iff_of_colLen_le_one h).mp hij
    rw [ite_eq_left rfl, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn]
  · rw [T.1.zeros hij]
    by_cases hi : i = 0
    · subst hi
      rw [ite_eq_left rfl, List.getD_eq_default]
      simp only [List.length_ofFn]
      exact Nat.le_of_not_lt fun hj =>
        hij ((YoungDiagram.mem_iff_of_colLen_le_one h).mpr ⟨rfl, hj⟩)
    · rw [ite_eq_right hi]

/-- **The bounded tableaux of a one-row shape are the multisets of letters of the right size**: a
tableau is the multiset of the letters of its row, and a multiset of letters is listed along the
row in increasing order. -/
def rowMultisetEquiv (h : μ.colLen 0 ≤ 1) : BoundedSSYT N μ ≃ Sym (Fin N) μ.card where
  toFun T := ⟨rowMultiset T,
    (card_rowMultiset T).trans (YoungDiagram.card_eq_rowLen_of_colLen_le_one h).symm⟩
  invFun s := ofRowMultiset h s.1 (s.2.trans (YoungDiagram.card_eq_rowLen_of_colLen_le_one h))
  left_inv T := ofRowMultiset_rowMultiset h T
  right_inv s := Sym.ext (rowMultiset_ofRowMultiset h s.1 _)

@[simp]
theorem rowMultisetEquiv_apply_coe (h : μ.colLen 0 ≤ 1) (T : BoundedSSYT N μ) :
    (rowMultisetEquiv h T : Multiset (Fin N)) = rowMultiset T :=
  (rfl)

/-- The inverse of `rowMultisetEquiv` lists a multiset of letters along the row in increasing
order. -/
@[simp]
theorem rowMultisetEquiv_symm_apply (h : μ.colLen 0 ≤ 1) (s : Sym (Fin N) μ.card) :
    (rowMultisetEquiv h).symm s
      = ofRowMultiset h s.1 (s.2.trans (YoungDiagram.card_eq_rowLen_of_colLen_le_one h)) :=
  (rfl)

end BoundedSSYT

/-! ### The Schur polynomial of a one-row shape -/

variable {N : ℕ} {R : Type*} [CommSemiring R] {μ : YoungDiagram}

/-- **The Schur polynomial of a one-row shape is a complete homogeneous symmetric polynomial**:
the tableaux of that shape are the multisets of letters of size the number of columns, each
contributing the monomial on the letters it uses. -/
theorem diagramSchurPoly_eq_hsymm_of_colLen_le_one (h : μ.colLen 0 ≤ 1) :
    diagramSchurPoly N R μ = hsymm (Fin N) R μ.card := by
  rw [diagramSchurPoly_eq_sum, hsymm]
  refine Fintype.sum_equiv (BoundedSSYT.rowMultisetEquiv h) _ _ fun T => ?_
  rw [prod_map_X_eq_monomial]
  exact congrArg (fun d => monomial d (1 : R)) (BoundedSSYT.weight_eq_toFinsupp h T)

section Partition

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- **The Schur polynomial of the partition `(n)` is the `n`-th complete homogeneous symmetric
polynomial**, `s_{(n)} = h_n`.  The diagram of `(n)` has at most one row: it is a single row of
`n` cells for `n > 0`, and empty for `n = 0`. -/
@[simp]
theorem schurPoly_indiscrete (n : ℕ) :
    schurPoly σ R (Nat.Partition.indiscrete n) = hsymm σ R n := by
  rw [schurPoly_eq_rename,
    diagramSchurPoly_eq_hsymm_of_colLen_le_one
      (YoungDiagram.colLen_ofPartition_indiscrete_le_one n),
    YoungDiagram.card_ofPartition, rename_hsymm]

end Partition

/-! ### Stability -/

/-- **Stability of the complete homogeneous symmetric polynomials**: setting the last of `n + 1`
variables to `0` turns `h_d` in `n + 1` variables into `h_d` in `n` variables.

Not a `simp` lemma, for the reason recorded at `TauCeti.aeval_snoc_zero_diagramSchurPoly`. -/
theorem aeval_snoc_zero_hsymm (n d : ℕ) :
    aeval (Fin.snoc (X : Fin n → MvPolynomial (Fin n) R) 0) (hsymm (Fin (n + 1)) R d) =
      hsymm (Fin n) R d := by
  have h : ∀ N, hsymm (Fin N) R d =
      diagramSchurPoly N R (YoungDiagram.ofPartition (Nat.Partition.indiscrete d)) := fun N => by
    rw [diagramSchurPoly_eq_hsymm_of_colLen_le_one
        (YoungDiagram.colLen_ofPartition_indiscrete_le_one d),
      YoungDiagram.card_ofPartition]
  rw [h, h, aeval_snoc_zero_diagramSchurPoly]

/-- **Stability of the integer-indexed complete homogeneous symmetric polynomials**: setting the
last of `n + 1` variables to `0` turns `h_m` in `n + 1` variables into `h_m` in `n` variables, for
every integer `m`. -/
theorem aeval_snoc_zero_hsymmInt (n : ℕ) (m : ℤ) :
    aeval (Fin.snoc (X : Fin n → MvPolynomial (Fin n) R) 0) (hsymmInt (Fin (n + 1)) R m) =
      hsymmInt (Fin n) R m := by
  rcases le_or_gt 0 m with hm | hm
  · rw [hsymmInt_of_nonneg hm, hsymmInt_of_nonneg hm, aeval_snoc_zero_hsymm]
  · rw [hsymmInt_of_neg hm, hsymmInt_of_neg hm, map_zero]

end TauCeti
end
end TAF_LiteralSource_0648

section TAF_LiteralSource_0649
/- Original module: PaperVerification.AlternatingFormsChernAnnihilation -/


/-!
# The polynomial annihilator calculation in Lemma 4.2

The bialternant formula puts `Δ * h_l` in the coordinate-power ideal as
soon as its distinguished column has exponent at least `N`.  Logarithmic
partial differentiation preserves that ideal, giving the odd annihilators
without rational functions.  Substitution of squares and coefficient
extraction then prove the actual polynomial coefficient identity used by
the integration formula.  Identifying this coefficient functional with
geometric integration is a separate theorem, not an assumption hidden here.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial
open scoped BigOperators

section Alternants

variable {R : Type*} [CommRing R]

/-- The descending staircase alternant; its square is the squared
Vandermonde product appearing in the paper's integration formula. -/
noncomputable def chernVandermonde (s : ℕ) : MvPolynomial (Fin s) R :=
  TauCeti.alternant (Fin s) R fun j => s - 1 - j.val

theorem chernVandermonde_sq (s : ℕ) :
    chernVandermonde (R := R) s ^ 2 =
      ∏ i : Fin s, ∏ j ∈ Finset.Ioi i, (X i - X j : MvPolynomial (Fin s) R) ^ 2 := by
  have hmat : (Matrix.of fun i j : Fin s => (X i : MvPolynomial (Fin s) R) ^
      (s - 1 - j.val)) =
      (Matrix.vandermonde (X : Fin s → MvPolynomial (Fin s) R)).submatrix id Fin.revPerm := by
    ext i j
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.vandermonde_apply,
      id_eq, Fin.revPerm_apply, Fin.val_rev]
    simp only [Nat.sub_sub, Nat.add_comm]
  have hsign : (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s)) : ℤ) :
      MvPolynomial (Fin s) R) ^ 2) = 1 := by
    have h := congrArg (fun z : ℤ => (z : MvPolynomial (Fin s) R))
      (Int.isUnit_sq (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s))).isUnit)
    simpa only [Int.cast_pow, Int.cast_one] using h
  rw [chernVandermonde, TauCeti.alternant_def, hmat, Matrix.det_permute',
    mul_pow, hsign, one_mul, Matrix.det_vandermonde]
  simp only [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  exact sub_sq_comm _ _

/-- One exponent at least `N` puts every determinant term in the actual
ideal generated by the `N`th coordinate powers. -/
theorem alternant_mem_coordinatePowerIdeal {s N : ℕ} (a : Fin s → ℕ)
    (j : Fin s) (hN : N ≤ a j) :
    TauCeti.alternant (Fin s) R a ∈
      coordinatePowerIdeal (fun _ : Fin s => N) := by
  rw [TauCeti.alternant_eq_sum]
  apply Ideal.sum_mem
  intro τ _
  have hpow : (X (τ j) : MvPolynomial (Fin s) R) ^ a j ∈
      coordinatePowerIdeal (fun _ : Fin s => N) :=
    (coordinatePowerIdeal (fun _ : Fin s => N)).mem_of_dvd (pow_dvd_pow _ hN)
      (coordinatePowerIdeal_generator _ (τ j))
  have hprod : (∏ i : Fin s, (X (τ i) : MvPolynomial (Fin s) R) ^ a i) ∈
      coordinatePowerIdeal (fun _ : Fin s => N) :=
    (coordinatePowerIdeal (fun _ : Fin s => N)).mem_of_dvd
      (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)) hpow
  simpa only [Units.smul_def, zsmul_eq_mul] using
    (coordinatePowerIdeal (fun _ : Fin s => N)).mul_mem_left
      (((Equiv.Perm.sign τ : ℤ) : MvPolynomial (Fin s) R)) hprod

/-- The single-alternant annihilator, obtained from the genuine Schur
polynomial bialternant formula for the one-row Young diagram. -/
theorem vandermonde_hsymm_mem_coordinatePowerIdeal {s N l : ℕ}
    (hs : 0 < s) (hN : N ≤ l + s - 1) :
    chernVandermonde (R := R) s * hsymm (Fin s) R l ∈
      coordinatePowerIdeal (fun _ : Fin s => N) := by
  let μ := YoungDiagram.ofPartition (Nat.Partition.indiscrete l)
  have hrow : μ.colLen 0 ≤ 1 :=
    YoungDiagram.colLen_ofPartition_indiscrete_le_one l
  have hcard : μ.card = l := YoungDiagram.card_ofPartition _
  have hrowzero : μ.rowLen 0 = l :=
    (YoungDiagram.card_eq_rowLen_of_colLen_le_one hrow).symm.trans hcard
  have hbialt := TauCeti.diagramSchurPoly_mul_alternant (R := R) s μ
    (hrow.trans (Nat.succ_le_iff.mpr hs))
  rw [TauCeti.diagramSchurPoly_eq_hsymm_of_colLen_le_one hrow, hcard] at hbialt
  rw [mul_comm, chernVandermonde, hbialt]
  apply alternant_mem_coordinatePowerIdeal _ ⟨0, hs⟩
  rw [YoungDiagram.betaNumber_def]
  change N ≤ μ.rowLen 0 + (s - 1 - 0)
  rw [hrowzero]
  omega

theorem vandermonde_sq_hsymm_mem_coordinatePowerIdeal {s N l : ℕ}
    (hs : 0 < s) (hN : N ≤ l + s - 1) :
    chernVandermonde (R := R) s ^ 2 * hsymm (Fin s) R l ∈
      coordinatePowerIdeal (fun _ : Fin s => N) := by
  have h := (coordinatePowerIdeal (fun _ : Fin s => N)).mul_mem_left
    (chernVandermonde (R := R) s) (vandermonde_hsymm_mem_coordinatePowerIdeal hs hN)
  simpa only [pow_two, mul_assoc] using h

/-- The odd first variations satisfy the corresponding ideal annihilator. -/
theorem vandermonde_sq_logarithmic_hsymm_mem {s N l : ℕ}
    (hs : 0 < s) (hN : N ≤ l + s - 1) (j : Fin s) :
    chernVandermonde (R := R) s ^ 2 * X j * pderiv j (hsymm (Fin s) R l) ∈
      coordinatePowerIdeal (fun _ : Fin s => N) :=
  squared_factor_logarithmic_derivative_mem _ _ _
    (vandermonde_hsymm_mem_coordinatePowerIdeal hs hN) j

end Alternants

section Coefficients

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}

theorem squareSubstitution_eq_expand :
    squareSubstitution (K := K) (σ := Fin s) = expand 2 := by
  ext i
  simp [squareSubstitution]

/-- The exponent extracted in the Grassmannian/Euler coefficient formula. -/
noncomputable def chernTopExponent (s N : ℕ) : Fin s →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun _ => 2 * N - 2

@[simp] theorem chernTopExponent_apply (s N : ℕ) (i : Fin s) :
    chernTopExponent s N i = 2 * N - 2 := rfl

/-- The unnormalized, actual coefficient functional in Section 4.2. -/
noncomputable def chernIntegrationCoefficient (N : ℕ)
    (P : MvPolynomial (Fin s) K) : K :=
  (P * expand 2 (chernVandermonde s) ^ 2).coeff (chernTopExponent s N)

/-- The defining functional is exactly the paper's squared-difference
coefficient expression, including its exponent in every variable. -/
theorem chernIntegrationCoefficient_formula (N : ℕ)
    (P : MvPolynomial (Fin s) K) :
    chernIntegrationCoefficient N P =
      (P * ∏ i : Fin s, ∏ j ∈ Finset.Ioi i,
        (X i ^ 2 - X j ^ 2 : MvPolynomial (Fin s) K) ^ 2).coeff
          (chernTopExponent s N) := by
  have hD : expand 2 (chernVandermonde (R := K) s) ^ 2 =
      ∏ i : Fin s, ∏ j ∈ Finset.Ioi i,
        (X i ^ 2 - X j ^ 2 : MvPolynomial (Fin s) K) ^ 2 := by
    rw [← map_pow, chernVandermonde_sq]
    simp only [map_prod, map_pow, map_sub, expand_X]
  exact congrArg (fun Q : MvPolynomial (Fin s) K =>
    (P * Q).coeff (chernTopExponent s N)) hD

theorem even_relation_coefficient_zero {N l : ℕ} (hs : 0 < s) (hpos : 0 < N)
    (hl : N ≤ l + s - 1) (P : MvPolynomial (Fin s) K) :
    chernIntegrationCoefficient N (P * squareSubstitution (hsymm (Fin s) K l)) = 0 := by
  have h := expand_mem_coordinatePowerIdeal (fun _ : Fin s => N) 2
    (vandermonde_sq_hsymm_mem_coordinatePowerIdeal (R := K) hs hl)
  have hP := (coordinatePowerIdeal (fun _ : Fin s => 2 * N)).mul_mem_left P h
  have hz := coefficient_zero_of_mem_coordinatePowerIdeal _ hP (chernTopExponent s N)
    (by intro i; simp only [chernTopExponent_apply]; omega)
  unfold chernIntegrationCoefficient
  rw [squareSubstitution_eq_expand]
  have hpoly : (P * expand 2 (hsymm (Fin s) K l)) * expand 2 (chernVandermonde s) ^ 2 =
      P * expand 2 (chernVandermonde s ^ 2 * hsymm (Fin s) K l) := by
    simp only [map_mul, map_pow]
    ring
  rw [hpoly]
  exact hz

/-- Multiplication by one extra `X j` makes the odd summand an expanded
logarithmic derivative.  The shifted top exponent is still below `2N`. -/
theorem odd_variation_coefficient_zero {N l : ℕ} (hs : 0 < s) (hpos : 0 < N)
    (hl : N ≤ l + s - 1) (P : MvPolynomial (Fin s) K) (j : Fin s) :
    chernIntegrationCoefficient N
      (P * (X j * squareSubstitution (pderiv j (hsymm (Fin s) K l)))) = 0 := by
  have h := expand_mem_coordinatePowerIdeal (fun _ : Fin s => N) 2
    (vandermonde_sq_logarithmic_hsymm_mem (R := K) hs hl j)
  have hP := (coordinatePowerIdeal (fun _ : Fin s => 2 * N)).mul_mem_left P h
  let Q := (P * (X j * squareSubstitution (pderiv j (hsymm (Fin s) K l)))) *
    expand 2 (chernVandermonde s) ^ 2
  have hQ : X j * Q ∈ coordinatePowerIdeal (fun _ : Fin s => 2 * N) := by
    have hpoly : X j * Q = P * expand 2
        (chernVandermonde s ^ 2 * X j * pderiv j (hsymm (Fin s) K l)) := by
      simp only [Q, squareSubstitution_eq_expand, map_mul, map_pow, expand_X]
      ring
    rw [hpoly]
    exact hP
  have hz := coefficient_zero_of_variable_mul_mem _ j hQ (chernTopExponent s N)
    (by
      intro i
      simp only [Finsupp.add_apply, chernTopExponent_apply]
      by_cases hij : i = j
      · subst i
        simp only [Finsupp.single_eq_same]
        omega
      · simp only [Finsupp.single_eq_of_ne hij, zero_add]
        omega)
  exact hz

/-- The polynomial content of Lemma 4.2, for the paper's full parameter
range and every polynomial multiplier.  No cohomology ring is substituted
for the genuine polynomial ring in this statement. -/
theorem chern_relation_annihilates_coefficient {N n : ℕ}
    (hs : 0 < s) (hsN : s ≤ N) (hn : 2 * (N - s) + 1 ≤ n)
    (P : MvPolynomial (Fin s) K) :
    chernIntegrationCoefficient N
      (P * chernRootRelationPolynomial (K := K) (σ := Fin s) n) = 0 := by
  have hpos : 0 < N := hs.trans_le hsN
  unfold chernRootRelationPolynomial
  split_ifs with heven
  · apply even_relation_coefficient_zero hs hpos
    obtain ⟨m, hm⟩ := heven
    omega
  · unfold chernIntegrationCoefficient
    rw [Finset.mul_sum, Finset.sum_mul, coeff_sum]
    apply Finset.sum_eq_zero
    intro j _
    exact odd_variation_coefficient_zero hs hpos (by omega) P j

/-- The same vanishing with the paper's normalization. -/
theorem chern_relation_annihilates_normalized_coefficient {N n : ℕ}
    (hs : 0 < s) (hsN : s ≤ N) (hn : 2 * (N - s) + 1 ≤ n)
    (P : MvPolynomial (Fin s) K) :
    ((-1 : K) ^ s.choose 2 / (s.factorial : K)) *
      chernIntegrationCoefficient N
        (P * chernRootRelationPolynomial (K := K) (σ := Fin s) n) = 0 := by
  rw [chern_relation_annihilates_coefficient hs hsN hn, mul_zero]

/-- The normalized coefficient functional on the actual independent Chern
coordinates.  Elementary substitution is the proved root/coordinate map. -/
noncomputable def chernCoefficientIntegration (N : ℕ)
    (P : MvPolynomial (Fin s) K) : K :=
  ((-1 : K) ^ s.choose 2 / (s.factorial : K)) *
    chernIntegrationCoefficient N
      (MvPolynomial.aeval (fun i : Fin s =>
        MvPolynomial.esymm (Fin s) K (i.val + 1)) P)

/-- Lemma 4.2's polynomial annihilation statement in the independent
coefficient ring, using the actual descended Chern relations. -/
theorem chernCoefficientRelation_annihilates {N n : ℕ}
    (hs : 0 < s) (hsN : s ≤ N) (hn : 2 * (N - s) + 1 ≤ n)
    (P : MvPolynomial (Fin s) K) :
    chernCoefficientIntegration N
      (P * chernCoefficientRelation (K := K) s n) = 0 := by
  unfold chernCoefficientIntegration
  rw [map_mul, chernCoefficientRelation_substitution]
  exact chern_relation_annihilates_normalized_coefficient hs hsN hn _

end Coefficients

end PaperVerification.AlternatingForms
end
end TAF_LiteralSource_0649

section TAF_LiteralSource_0650
/- Original module: PaperVerification.AlternatingFormsChernPairingNonzero -/


/-!
# A nonzero top value of the actual Chern coefficient pairing

The central coefficient of the squared staircase alternant is the sign of
reversal times `s!`.  Consequently the formal integration functional is
nonzero on the top power of the last Chern coordinate.  This supplies the
nonzero functional needed by the complete-intersection pairing argument
without invoking geometric positivity.  The geometric integration comparison
and the perfect-pairing theorem for the complete intersection remain separate.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial
open scoped BigOperators

section AlternantCoefficient

variable {R : Type*} [CommRing R]

private theorem cast_intUnit_sq (u : ℤˣ) : ((u : ℤ) : R) ^ 2 = 1 := by
  have h := congrArg (fun z : ℤ => (z : R)) (Int.isUnit_sq u.isUnit)
  simpa only [Int.cast_pow, Int.cast_one] using h

/-- The exponent with the same value in every variable. -/
noncomputable def constantExponent (s d : ℕ) : Fin s →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun _ => d

@[simp] theorem constantExponent_apply (s d : ℕ) (i : Fin s) :
    constantExponent s d i = d := rfl

/-- The constant rectangular exponent in the squared Vandermonde has one
contribution of the same sign from each permutation. -/
theorem chernVandermonde_sq_central_coefficient (s : ℕ) :
    (chernVandermonde (R := R) s ^ 2).coeff (constantExponent s (s - 1)) =
      (s.factorial : R) * ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s)) : ℤ) : R) := by
  let a : Fin s → ℕ := fun i => s - 1 - i.val
  let D : MvPolynomial (Fin s) R := chernVandermonde s
  let m := constantExponent s (s - 1)
  have hexpand : D * D =
      ∑ τ : Equiv.Perm (Fin s), Equiv.Perm.sign τ •
        (D * ∏ i : Fin s, (X (τ i) : MvPolynomial (Fin s) R) ^ a i) := by
    calc
      _ = D * ∑ τ : Equiv.Perm (Fin s), Equiv.Perm.sign τ •
          ∏ i : Fin s, (X (τ i) : MvPolynomial (Fin s) R) ^ a i :=
        congrArg (fun q : MvPolynomial (Fin s) R => D * q)
          (TauCeti.alternant_eq_sum a)
      _ = _ := by simp only [Finset.mul_sum, mul_smul_comm]
  have hterm (τ : Equiv.Perm (Fin s)) :
      (Equiv.Perm.sign τ •
        (D * ∏ i : Fin s, (X (τ i) : MvPolynomial (Fin s) R) ^ a i)).coeff m =
          ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s)) : ℤ) : R) := by
    let d : Fin s →₀ ℕ := Finsupp.equivFunOnFinite.symm (a ∘ τ.symm)
    have hprod : (∏ i : Fin s, (X (τ i) : MvPolynomial (Fin s) R) ^ a i) =
        monomial d 1 := by
      have hp : (∏ i : Fin s, (X (τ i) : MvPolynomial (Fin s) R) ^ a i) =
          ∏ i : Fin s, (X i : MvPolynomial (Fin s) R) ^ a (τ.symm i) := by
        rw [← Equiv.prod_comp τ (fun i => (X i : MvPolynomial (Fin s) R) ^ a (τ.symm i))]
        simp
      rw [hp, prod_X_pow]
      apply congrArg (fun e : Fin s →₀ ℕ => monomial e (1 : R))
      ext i
      simp [d, Function.comp_def]
    have hle : d ≤ m := by
      intro i
      change s - 1 - (τ.symm i).val ≤ s - 1
      exact Nat.sub_le _ _
    have hcomp : m - d =
        Finsupp.equivFunOnFinite.symm (a ∘ (τ.symm.trans Fin.revPerm)) := by
      ext i
      change (s - 1) - (s - 1 - (τ.symm i).val) =
        s - 1 - ((τ.symm i).rev).val
      rw [Fin.val_rev]
      have hi := (τ.symm i).isLt
      omega
    rw [coeff_smul, hprod, coeff_mul_monomial', if_pos hle, mul_one, hcomp]
    change Equiv.Perm.sign τ •
      (TauCeti.alternant (Fin s) R a).coeff
        (Finsupp.equivFunOnFinite.symm (a ∘ (τ.symm.trans Fin.revPerm))) = _
    rw [TauCeti.coeff_alternant_of_injective (TauCeti.injective_staircase s),
      Equiv.Perm.sign_trans, Equiv.Perm.sign_symm]
    simp only [Units.smul_def, zsmul_eq_mul, Units.val_mul, Int.cast_mul]
    have hsquare := cast_intUnit_sq (R := R) (Equiv.Perm.sign τ)
    calc
      _ = (((Equiv.Perm.sign Fin.revPerm : ℤ) : R)) *
          (((Equiv.Perm.sign τ : ℤ) : R) ^ 2) := by ring
      _ = _ := by rw [hsquare, mul_one]
  change (D ^ 2).coeff m = _
  rw [pow_two, hexpand, coeff_sum]
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul]

end AlternantCoefficient

section NonzeroValue

variable {K : Type*} [Field K] [CharZero K] {s N : ℕ}

theorem esymm_fin_card :
    esymm (Fin s) K s = ∏ i : Fin s, (X i : MvPolynomial (Fin s) K) := by
  have hpow : (Finset.univ : Finset (Fin s)).powersetCard s = {Finset.univ} := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.powersetCard_self (Finset.univ : Finset (Fin s))
  rw [esymm, hpow, Finset.sum_singleton]

/-- The last Chern coordinate raised to its top-degree exponent. -/
noncomputable def chernTopTestPolynomial (hs : 0 < s) (N : ℕ) : MvPolynomial (Fin s) K :=
  X ⟨s - 1, by omega⟩ ^ (2 * (N - s))

/-- This is a top-degree element for the paper's actual Chern grading. -/
theorem chernTopTestPolynomial_isWeightedHomogeneous (hs : 0 < s) (N : ℕ) :
    (chernTopTestPolynomial (K := K) hs N).IsWeightedHomogeneous
      chernCoefficientWeight (s * (2 * (N - s))) := by
  have h := (MvPolynomial.isWeightedHomogeneous_X K chernCoefficientWeight
    (⟨s - 1, by omega⟩ : Fin s)).pow (2 * (N - s))
  have hlast : s - 1 + 1 = s := by omega
  simpa only [chernTopTestPolynomial, chernCoefficientWeight, hlast,
    smul_eq_mul, mul_comm] using h

theorem chernTopTestPolynomial_substitution (hs : 0 < s) (N : ℕ) :
    MvPolynomial.aeval (fun i : Fin s => esymm (Fin s) K (i.val + 1))
      (chernTopTestPolynomial (K := K) hs N) =
        monomial (constantExponent s (2 * (N - s))) 1 := by
  rw [chernTopTestPolynomial, map_pow, aeval_X]
  have hlast : s - 1 + 1 = s := by omega
  rw [hlast, esymm_fin_card, ← Finset.prod_pow, prod_X_pow]
  apply congrArg (fun e : Fin s →₀ ℕ => monomial e (1 : K))
  ext i
  simp [constantExponent]

/-- The nonzero top value is derived by a coefficient computation for the
actual functional, rather than assumed as a pairing hypothesis. -/
theorem chernCoefficientIntegration_top_ne_zero (hs : 0 < s) (hsN : s ≤ N) :
    chernCoefficientIntegration N (chernTopTestPolynomial (K := K) hs N) ≠ 0 := by
  have hindex : constantExponent s (2 * (N - s)) +
      2 • constantExponent s (s - 1) = chernTopExponent s N := by
    ext i
    simp only [Finsupp.add_apply, Finsupp.smul_apply, constantExponent_apply,
      chernTopExponent_apply, smul_eq_mul]
    omega
  unfold chernCoefficientIntegration
  rw [chernTopTestPolynomial_substitution]
  unfold chernIntegrationCoefficient
  rw [← map_pow, ← hindex, coeff_monomial_mul, one_mul,
    coeff_expand_smul 2 (by decide), chernVandermonde_sq_central_coefficient]
  apply mul_ne_zero
  · exact div_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero s))
  · apply mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero s))
    exact Int.cast_ne_zero.mpr (Units.ne_zero (Equiv.Perm.sign Fin.revPerm))

end NonzeroValue

end PaperVerification.AlternatingForms
end
end TAF_LiteralSource_0650

section TAF_LiteralSource_0651
/- Original module: PaperVerification.AlternatingFormsChernQuotientPairing -/


/-!
# The actual coefficient functional on the Chern relation quotient

The coefficient calculation annihilates the entire ideal generated by the
paper's finite window, including arbitrary polynomial multiples.  It therefore
descends to the literal quotient by those relations and is nonzero there.
This is the algebraic factorization used in Section 4.3.  No geometric
integration comparison or perfect-pairing assertion is built into the quotient.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K] {s N : ℕ}

/-- The previously defined actual coefficient functional is linear. -/
noncomputable def chernCoefficientIntegrationLinear (s N : ℕ) :
    MvPolynomial (Fin s) K →ₗ[K] K :=
  ((-1 : K) ^ s.choose 2 / (s.factorial : K)) •
    (lcoeff K (chernTopExponent s N)).comp
      ((LinearMap.mulRight K (expand 2 (chernVandermonde s) ^ 2)).comp
        (elementarySubstitution s).toLinearMap)

@[simp] theorem chernCoefficientIntegrationLinear_apply
    (P : MvPolynomial (Fin s) K) :
    chernCoefficientIntegrationLinear s N P = chernCoefficientIntegration N P :=
  rfl

/-- The exact finite relation ideal of Theorem 4.1. -/
noncomputable def chernRelationIdeal (s N : ℕ) : Ideal (MvPolynomial (Fin s) K) :=
  Ideal.ofList (chernRelationSequence K s (2 * (N - s) + 1))

/-- Vanishing on the generators and every multiplier gives vanishing on the
whole genuine polynomial ideal, not just on their linear span. -/
theorem chernCoefficientIntegration_ideal_zero (hs : 0 < s) (hsN : s ≤ N)
    (P : MvPolynomial (Fin s) K) (hP : P ∈ chernRelationIdeal (K := K) s N) :
    chernCoefficientIntegration N P = 0 := by
  have hall : ∀ p : MvPolynomial (Fin s) K,
      p ∈ chernRelationIdeal (K := K) s N →
      ∀ q : MvPolynomial (Fin s) K,
        chernCoefficientIntegrationLinear s N (q * p) = 0 := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
      intro q
      exact chernCoefficientRelation_annihilates (n := 2*(N-s)+1+i.val) hs hsN (by omega) q
    | zero => intro q; simp only [mul_zero, map_zero]
    | add p r hp hr ihp ihr =>
      intro q
      rw [mul_add, map_add, ihp q, ihr q, add_zero]
    | smul a p hp ih =>
      intro q
      change chernCoefficientIntegrationLinear s N (q * (a * p)) = 0
      rw [← mul_assoc]
      exact ih (q * a)
  simpa only [one_mul, chernCoefficientIntegrationLinear_apply] using hall P hP 1

/-- The vector-space presentation of the actual polynomial quotient. -/
abbrev ChernRelationQuotient (K : Type*) [Field K] [CharZero K] (s N : ℕ) :=
  MvPolynomial (Fin s) K ⧸ (chernRelationIdeal (K := K) s N).restrictScalars K

/-- The normalized coefficient functional descends through the finite window
of relations by a proved kernel containment. -/
noncomputable def chernQuotientIntegration (hs : 0 < s) (hsN : s ≤ N) :
    ChernRelationQuotient K s N →ₗ[K] K :=
  ((chernRelationIdeal (K := K) s N).restrictScalars K).liftQ
    (chernCoefficientIntegrationLinear s N) (by
      intro P hP
      change chernCoefficientIntegration N P = 0
      exact chernCoefficientIntegration_ideal_zero hs hsN P hP)

@[simp] theorem chernQuotientIntegration_mk (hs : 0 < s) (hsN : s ≤ N)
    (P : MvPolynomial (Fin s) K) :
    chernQuotientIntegration hs hsN
        (((chernRelationIdeal (K := K) s N).restrictScalars K).mkQ P) =
      chernCoefficientIntegration N P :=
  rfl

/-- The top test class remains nonzero in the literal quotient by all the
relations.  This follows from the computed top coefficient. -/
theorem chernTopTestPolynomial_not_mem_relationIdeal (hs : 0 < s) (hsN : s ≤ N) :
    chernTopTestPolynomial (K := K) hs N ∉ chernRelationIdeal (K := K) s N := by
  intro hmem
  exact chernCoefficientIntegration_top_ne_zero hs hsN
    (chernCoefficientIntegration_ideal_zero hs hsN _ hmem)

theorem chernQuotientIntegration_ne_zero (hs : 0 < s) (hsN : s ≤ N) :
    chernQuotientIntegration (K := K) hs hsN ≠ 0 := by
  intro hz
  have h := LinearMap.congr_fun hz
    (((chernRelationIdeal (K := K) s N).restrictScalars K).mkQ
      (chernTopTestPolynomial hs N))
  rw [chernQuotientIntegration_mk, LinearMap.zero_apply] at h
  exact chernCoefficientIntegration_top_ne_zero hs hsN h

end PaperVerification.AlternatingForms
end
end TAF_LiteralSource_0651

section TAF_LiteralSource_0652
/- Original module: PaperVerification.ChernPairingReflection -/


/-!
# Rectangular nondegeneracy of the actual Chern coefficient pairing

The coefficient integral is nondegenerate on symmetric polynomials whose
degree in each root is at most `2 * (N-s)`.  Reversing these root exponents
turns the product with the Vandermonde into its coefficient dual.  Its top
coefficient is therefore a nonzero sum of rational squares.

This is a statement about the independently defined polynomial integral.
It does not identify that integral with a geometric pushforward or define
the singular cohomology or Chow ring by the desired presentation.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial Finset
open RectangularReflection
open scoped BigOperators

variable {R σ : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]

theorem permutedPowerProduct_eq_monomial (a : σ → ℕ) (τ : Equiv.Perm σ) :
    (∏ i, (X (τ i) : MvPolynomial σ R)^a i) =
      monomial (Finsupp.equivFunOnFinite.symm (a ∘ τ.symm)) 1 := by
  have hp : (∏ i, (X (τ i) : MvPolynomial σ R)^a i) =
      ∏ i, (X i : MvPolynomial σ R)^a (τ.symm i) := by
    rw [← Equiv.prod_comp τ (fun i => (X i : MvPolynomial σ R)^a (τ.symm i))]
    simp
  rw [hp, prod_X_pow]
  apply congrArg (fun e : σ →₀ ℕ => monomial e (1 : R))
  ext i
  simp [Function.comp_def]

/-- Reflection reverses every exponent of an alternant, before any
regularity or nonvanishing statement is used. -/
theorem reflect_alternant (d : ℕ) (a : σ → ℕ) :
    reflect (uniformExponent d) (TauCeti.alternant σ R a) =
      TauCeti.alternant σ R (fun i => d-a i) := by
  rw [TauCeti.alternant_eq_sum, TauCeti.alternant_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro τ _
  rw [map_zsmul_unit]
  apply congrArg (fun p : MvPolynomial σ R => Equiv.Perm.sign τ • p)
  rw [permutedPowerProduct_eq_monomial, permutedPowerProduct_eq_monomial,
    reflect_monomial]
  apply congrArg (fun e : σ →₀ ℕ => monomial e (1 : R))
  ext i
  rfl

theorem boundedBy_alternant (d : ℕ) (a : σ → ℕ) (ha : ∀ i, a i ≤ d) :
    BoundedBy (uniformExponent d) (TauCeti.alternant σ R a) := by
  intro b hb
  have hcoeff := mem_support_iff.mp hb
  rw [TauCeti.coeff_alternant] at hcoeff
  obtain ⟨τ,hτ,_⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcoeff
  have heq := (Finset.mem_filter.mp hτ).2
  intro i
  obtain ⟨j,rfl⟩ := τ.surjective i
  have hj : b (τ j) = a j := congrFun heq j
  change b (τ j) ≤ d
  rw [hj]
  exact ha j

theorem expand_alternant (d : ℕ) (a : σ → ℕ) :
    expand d (TauCeti.alternant σ R a) =
      TauCeti.alternant σ R (fun i => d*a i) := by
  rw [TauCeti.alternant_def, TauCeti.alternant_def, AlgHom.map_det]
  congr 1
  ext i j
  simp [pow_mul]

theorem expandedVandermonde_bounded (s : ℕ) :
    BoundedBy (uniformExponent (2*(s-1)))
      (expand 2 (chernVandermonde (R := R) s)) := by
  rw [chernVandermonde, expand_alternant]
  apply boundedBy_alternant
  intro i
  exact Nat.mul_le_mul_left 2 (Nat.sub_le _ _)

/-- The reversal sign is an actual permutation sign; its nonvanishing
does not require a separate sign-convention calculation. -/
theorem reflect_expandedVandermonde (s : ℕ) :
    reflect (uniformExponent (2*(s-1)))
        (expand 2 (chernVandermonde (R := R) s)) =
      Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s)) •
        expand 2 (chernVandermonde (R := R) s) := by
  rw [chernVandermonde, expand_alternant, reflect_alternant]
  have hexp : (fun i : Fin s => 2*(s-1)-2*(s-1-i.val)) =
      (fun i : Fin s => 2*(s-1-i.val)) ∘ Fin.revPerm := by
    funext i
    simp only [Function.comp_apply, Fin.revPerm_apply, Fin.val_rev]
    have hi := i.isLt
    omega
  rw [hexp, TauCeti.alternant_comp_perm]

theorem expandedVandermonde_ne_zero [Nontrivial R] (s : ℕ) :
    expand 2 (chernVandermonde (R := R) s) ≠ 0 := by
  rw [← map_zero (expand (R := R) (σ := Fin s) 2)]
  apply (expand_injective (R := R) (σ := Fin s) (by decide : 0<2)).ne
  exact TauCeti.alternant_ne_zero_of_injective (TauCeti.injective_staircase s)

section CoefficientNondegeneracy

variable {s N : ℕ}

/-- A nonzero symmetric polynomial in the rectangle has a nonzero
partner for the actual root-coordinate integration functional. -/
theorem chernIntegrationCoefficient_reflection_ne_zero
    (hs : 0<s) (hsN : s≤N) (p : MvPolynomial (Fin s) ℚ)
    (hbound : BoundedBy (uniformExponent (2*(N-s))) p) (hne : p≠0) :
    chernIntegrationCoefficient N
      (p * reflect (uniformExponent (2*(N-s))) p) ≠ 0 := by
  let v : MvPolynomial (Fin s) ℚ := expand 2 (chernVandermonde s)
  let ε : ℤˣ := Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s))
  have ht : uniformExponent (σ := Fin s) (2*(N-s)) +
      uniformExponent (2*(s-1)) = chernTopExponent s N := by
    ext i
    simp only [Finsupp.add_apply, uniformExponent_apply, chernTopExponent_apply]
    omega
  have hb : BoundedBy (chernTopExponent s N) (p*v) := by
    rw [← ht]
    exact boundedBy_mul hbound (expandedVandermonde_bounded s)
  have hn : p*v≠0 := mul_ne_zero hne (expandedVandermonde_ne_zero s)
  have hpositive := coeff_self_mul_reflect_pos hb hn
  have hreflect : reflect (chernTopExponent s N) (p*v) =
      ε • (reflect (uniformExponent (2*(N-s))) p * v) := by
    rw [← ht, reflect_mul hbound (expandedVandermonde_bounded s),
      reflect_expandedVandermonde]
    simp only [mul_smul_comm]
    rfl
  rw [hreflect, mul_smul_comm, coeff_smul] at hpositive
  have hprod : p*v*(reflect (uniformExponent (2*(N-s))) p*v) =
      (p*reflect (uniformExponent (2*(N-s))) p)*v^2 := by ring
  rw [hprod] at hpositive
  intro hz
  change ((p*reflect (uniformExponent (2*(N-s))) p)*v^2).coeff
      (chernTopExponent s N) = 0 at hz
  rw [hz, smul_zero] at hpositive
  exact (lt_irrefl 0) hpositive


/-- Elementary substitution has its image in the actual symmetric subalgebra. -/
theorem elementarySubstitution_isSymmetric (P : MvPolynomial (Fin s) ℚ) :
    (elementarySubstitution s P).IsSymmetric := by
  apply (MvPolynomial.mem_symmetricSubalgebra _).mp
  simpa only [MvPolynomial.esymmAlgHom_apply, elementarySubstitution] using
    (MvPolynomial.esymmAlgHom (Fin s) ℚ s P).property

/-- The root reflection expressed back in independent Chern coordinates by
Mathlib's proved fundamental theorem of symmetric polynomials. -/
noncomputable def chernCoefficientReflection (s N : ℕ)
    (P : MvPolynomial (Fin s) ℚ) : MvPolynomial (Fin s) ℚ :=
  (MvPolynomial.esymmAlgEquiv (Fin s) ℚ (Fintype.card_fin s)).symm
    ⟨reflect (uniformExponent (2*(N-s))) (elementarySubstitution s P),
      reflect_isSymmetric (elementarySubstitution_isSymmetric P) _⟩

theorem chernCoefficientReflection_substitution (P : MvPolynomial (Fin s) ℚ) :
    elementarySubstitution s (chernCoefficientReflection s N P) =
      reflect (uniformExponent (2*(N-s))) (elementarySubstitution s P) := by
  have h := (MvPolynomial.esymmAlgEquiv (Fin s) ℚ (Fintype.card_fin s)).apply_symm_apply
    ⟨reflect (uniformExponent (2*(N-s))) (elementarySubstitution s P),
      reflect_isSymmetric (elementarySubstitution_isSymmetric P) _⟩
  have hv := congrArg Subtype.val h
  change (MvPolynomial.esymmAlgHom (Fin s) ℚ s
    (chernCoefficientReflection s N P)).val = _ at hv
  simpa only [MvPolynomial.esymmAlgHom_apply, elementarySubstitution] using hv

/-- Reflection supplies a partner with nonzero normalized coefficient pairing
for every nonzero Chern polynomial with rectangular root support. -/
theorem chernCoefficientIntegration_reflection_ne_zero
    (hs : 0<s) (hsN : s≤N) (P : MvPolynomial (Fin s) ℚ)
    (hbound : BoundedBy (uniformExponent (2*(N-s))) (elementarySubstitution s P))
    (hne : P≠0) :
    chernCoefficientIntegration N (P * chernCoefficientReflection s N P) ≠ 0 := by
  unfold chernCoefficientIntegration
  change ((-1 : ℚ)^s.choose 2 / (s.factorial : ℚ)) *
    chernIntegrationCoefficient N
      (elementarySubstitution s (P * chernCoefficientReflection s N P)) ≠ 0
  rw [map_mul, chernCoefficientReflection_substitution]
  apply mul_ne_zero
  · exact div_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero s))
  · apply chernIntegrationCoefficient_reflection_ne_zero hs hsN _ hbound
    exact fun h => hne ((elementarySubstitution_injective s)
      (h.trans (map_zero (elementarySubstitution s)).symm))

/-- No nonzero Chern polynomial supported in the root rectangle belongs to
the actual relation ideal. This is a proved injection into the quotient. -/
theorem chernRectangular_not_mem_relationIdeal
    (hs : 0<s) (hsN : s≤N) (P : MvPolynomial (Fin s) ℚ)
    (hbound : BoundedBy (uniformExponent (2*(N-s))) (elementarySubstitution s P))
    (hne : P≠0) : P ∉ chernRelationIdeal (K := ℚ) s N := by
  intro hP
  exact chernCoefficientIntegration_reflection_ne_zero hs hsN P hbound hne
    (chernCoefficientIntegration_ideal_zero hs hsN _
      ((chernRelationIdeal (K := ℚ) s N).mul_mem_right
        (chernCoefficientReflection s N P) hP))

end CoefficientNondegeneracy

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0652

section TAF_LiteralSource_0653
/- Original module: PaperVerification.ChernRectangleBounds -/


/-!
# The finite-dimensional rectangle used for the Chern pairing

A coefficient polynomial of ordinary total degree at most `c` becomes, under
elementary substitution, a symmetric root polynomial whose degree in every
individual root is at most `c`. Its source has dimension `choose (c+s) s`.
This uses the actual monomial basis, with the usual slack-coordinate bijection
between degree-at-most-`c` monomials in `s` variables and degree-`c` monomials
in `s+1` variables.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification

open MvPolynomial Finset
open RectangularReflection
open scoped BigOperators

/-- Substitution of polynomials having degree at most one in a chosen root
turns ordinary total degree into an upper bound for that root degree. -/
theorem degreeOf_aeval_le_totalDegree
    {R σ τ : Type*} [CommSemiring R]
    (f : σ → MvPolynomial τ R) (j : τ) (hf : ∀ i, (f i).degreeOf j ≤ 1)
    (P : MvPolynomial σ R) : (aeval f P).degreeOf j ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum, map_sum]
  refine (degreeOf_sum_le j _ _).trans (Finset.sup_le fun d hd => ?_)
  rw [aeval_monomial, algebraMap_eq]
  refine (degreeOf_C_mul_le _ j _).trans ((degreeOf_prod_le j _ _).trans ?_)
  calc
    ∑ i ∈ d.support, ((f i)^d i).degreeOf j ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i _
      exact (degreeOf_pow_le j (f i) (d i)).trans
        (by simpa only [mul_one] using Nat.mul_le_mul_left (d i) (hf i))
    _ ≤ P.totalDegree := le_totalDegree hd

namespace AlternatingForms

variable {s c : ℕ}

/-- Every elementary symmetric coordinate is multiaffine in the root variables. -/
theorem degreeOf_elementary_coordinate (i j : Fin s) :
    (esymm (Fin s) ℚ (i.val+1)).degreeOf j = 1 := by
  rw [degreeOf_def, degrees_esymm (σ := Fin s) (R := ℚ) (by omega) (by simpa using i.isLt)]
  simp

/-- A low ordinary degree in Chern coordinates gives the required root box. -/
theorem elementarySubstitution_bounded_of_totalDegree
    (P : MvPolynomial (Fin s) ℚ) (hP : P.totalDegree ≤ c) :
    BoundedBy (uniformExponent c) (elementarySubstitution s P) := by
  intro d hd j
  change d j ≤ c
  refine (le_degreeOf_of_mem_support j hd).trans ((degreeOf_aeval_le_totalDegree
    (fun i : Fin s => esymm (Fin s) ℚ (i.val+1)) j ?_ P).trans hP)
  intro i
  rw [degreeOf_elementary_coordinate]

end AlternatingForms

/-- Adding the slack exponent turns a bounded-degree monomial into an
exact-degree monomial in one extra variable. -/
def degreeAtMostEquivDegree (s c : ℕ) :
    {d : Fin s →₀ ℕ // d.degree ≤ c} ≃
      {d : Fin (s+1) →₀ ℕ // d.degree = c} where
  toFun d := ⟨Finsupp.equivFunOnFinite.symm (Fin.cons (c-d.1.degree) d.1), by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_succ]
    change c-d.1.degree + ∑ i : Fin s, d.1 i = c
    rw [← Finsupp.degree_eq_sum]
    exact Nat.sub_add_cancel d.2⟩
  invFun d := ⟨Finsupp.equivFunOnFinite.symm (fun i : Fin s => d.1 i.succ), by
    have h := d.2
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_succ] at h
    rw [Finsupp.degree_eq_sum]
    change (∑ i : Fin s, d.1 i.succ) ≤ c
    omega⟩
  left_inv d := by
    apply Subtype.ext
    ext i
    rfl
  right_inv d := by
    apply Subtype.ext
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · have h := d.2
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_succ] at h
      change c - (Finsupp.equivFunOnFinite.symm
        (fun j : Fin s => d.1 j.succ)).degree = d.1 0
      rw [Finsupp.degree_eq_sum]
      change c - (∑ j : Fin s, d.1 j.succ) = d.1 0
      omega
    · rfl

/-- Count actual exponent vectors of one fixed total degree. -/
theorem card_degree_eq_multichoose (s c : ℕ) :
    Nat.card {d : Fin s →₀ ℕ // d.degree = c} = s.multichoose c := by
  classical
  let e : {d : Fin s →₀ ℕ // d.degree = c} ≃
      (Finset.univ.finsuppAntidiag c : Finset (Fin s →₀ ℕ)) :=
    Equiv.subtypeEquiv (Equiv.refl _) fun d => by
      simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_finsuppAntidiag_nat_eq_multichoose]
  simp

/-- Dimension of the genuine ordinary-total-degree submodule. -/
theorem finrank_restrictTotalDegree (s c : ℕ) :
    Module.finrank ℚ (restrictTotalDegree (Fin s) ℚ c) = (c+s).choose s := by
  rw [Module.finrank_eq_nat_card_basis (basisRestrictTotalDegree (Fin s) ℚ c),
    Nat.card_congr (degreeAtMostEquivDegree s c), card_degree_eq_multichoose,
    Nat.multichoose_eq]
  have h : s+1+c-1=c+s := by omega
  rw [h, Nat.choose_symm_add]

end PaperVerification
end
end
end TAF_LiteralSource_0653

section TAF_LiteralSource_0654
/- Original module: PaperVerification.ChernPerfectPairingBridge -/


/-!
# From the rectangle to the actual Chern quotient pairing

The root-exponent reflection proves injectivity of the low-degree coefficient
subspace into the literal quotient. Once the independent complete-intersection
dimension calculation is supplied, that injection is an isomorphism and the
coefficient integral gives a nondegenerate bilinear form on the quotient.

The dimension premise in the bridge theorem is explicit: this file does not
assume or redefine any cohomology, Chow group, or geometric integration map.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial
open RectangularReflection

/-- The actual commutative ring quotient by the Section 4 relation ideal. -/
abbrev ChernQuotientRing (s N : ℕ) :=
  MvPolynomial (Fin s) ℚ ⧸ chernRelationIdeal (K := ℚ) s N

instance chernQuotientRing_finite (s N : ℕ) :
    Module.Finite ℚ (ChernQuotientRing s N) :=
  chern_relation_quotient_finite s (2*(N-s)+1) (by omega)

/-- Ordinary total degree bounds define an actual linear subspace of Chern
polynomials; this is its natural map to the actual ring quotient. -/
def chernLowDegreeToQuotient (s N : ℕ) :
    restrictTotalDegree (Fin s) ℚ (2*(N-s)) →ₗ[ℚ] ChernQuotientRing s N :=
  (Ideal.Quotient.mkₐ ℚ (chernRelationIdeal (K := ℚ) s N)).toLinearMap.comp
    (restrictTotalDegree (Fin s) ℚ (2*(N-s))).subtype

@[simp] theorem chernLowDegreeToQuotient_apply {s N : ℕ}
    (P : restrictTotalDegree (Fin s) ℚ (2*(N-s))) :
    chernLowDegreeToQuotient s N P =
      Ideal.Quotient.mk (chernRelationIdeal (K := ℚ) s N) P := rfl

/-- The rectangle injects into the quotient by the nonzero coefficient pairing,
without using any dimension calculation. -/
theorem chernLowDegreeToQuotient_injective {s N : ℕ} (hs : 0<s) (hsN : s≤N) :
    Function.Injective (chernLowDegreeToQuotient s N) := by
  intro P Q hPQ
  simp only [chernLowDegreeToQuotient_apply] at hPQ
  apply Subtype.ext
  by_contra hne
  have hdiffne : (P : MvPolynomial (Fin s) ℚ) - (Q : MvPolynomial (Fin s) ℚ) ≠ 0 :=
    sub_ne_zero.mpr hne
  have hmem : (P : MvPolynomial (Fin s) ℚ) - (Q : MvPolynomial (Fin s) ℚ) ∈
      chernRelationIdeal (K := ℚ) s N := by
    apply Ideal.Quotient.eq.mp
    exact hPQ
  have hdegree : ((P : MvPolynomial (Fin s) ℚ) - (Q : MvPolynomial (Fin s) ℚ)).totalDegree
      ≤ 2*(N-s) :=
    (mem_restrictTotalDegree (Fin s) (2*(N-s))
      ((P : MvPolynomial (Fin s) ℚ) - (Q : MvPolynomial (Fin s) ℚ))).mp
        ((restrictTotalDegree (Fin s) ℚ (2*(N-s))).sub_mem P.property Q.property)
  have hbound : BoundedBy (uniformExponent (2*(N-s)))
      (elementarySubstitution s
        ((P : MvPolynomial (Fin s) ℚ) - (Q : MvPolynomial (Fin s) ℚ))) :=
    elementarySubstitution_bounded_of_totalDegree
      (s := s) (c := 2*(N-s)) _ hdegree
  exact chernRectangular_not_mem_relationIdeal (s := s) (N := N)
    hs hsN _ hbound hdiffne hmem

/-- The normalized polynomial coefficient functional on the actual ring quotient. -/
def chernRingIntegration {s N : ℕ} (hs : 0<s) (hsN : s≤N) :
    ChernQuotientRing s N →ₗ[ℚ] ℚ :=
  (chernQuotientIntegration (K := ℚ) hs hsN).comp
    (Submodule.Quotient.restrictScalarsEquiv ℚ
      (chernRelationIdeal (K := ℚ) s N)).symm.toLinearMap

@[simp] theorem chernRingIntegration_mk {s N : ℕ} (hs : 0<s) (hsN : s≤N)
    (P : MvPolynomial (Fin s) ℚ) :
    chernRingIntegration hs hsN
      (Ideal.Quotient.mk (chernRelationIdeal (K := ℚ) s N) P) =
        chernCoefficientIntegration N P := rfl

/-- Multiplication followed by the descended coefficient functional. -/
def chernRingPairing {s N : ℕ} (hs : 0<s) (hsN : s≤N) :
    LinearMap.BilinForm ℚ (ChernQuotientRing s N) :=
  (LinearMap.mul ℚ (ChernQuotientRing s N)).compr₂ (chernRingIntegration hs hsN)

@[simp] theorem chernRingPairing_apply {s N : ℕ} (hs : 0<s) (hsN : s≤N)
    (x y : ChernQuotientRing s N) :
    chernRingPairing hs hsN x y = chernRingIntegration hs hsN (x*y) := rfl

@[simp] theorem chernRingPairing_mk {s N : ℕ} (hs : 0<s) (hsN : s≤N)
    (P Q : MvPolynomial (Fin s) ℚ) :
    chernRingPairing hs hsN
      (Ideal.Quotient.mk (chernRelationIdeal (K := ℚ) s N) P)
      (Ideal.Quotient.mk (chernRelationIdeal (K := ℚ) s N) Q) =
        chernCoefficientIntegration N (P*Q) := by
  rw [chernRingPairing_apply, ← map_mul, chernRingIntegration_mk]

/-- Equal dimensions turn the independently proved rectangle injection into
surjectivity. The premise is the separate complete-intersection calculation. -/
theorem chernLowDegreeToQuotient_surjective_of_finrank {s N : ℕ}
    (hs : 0<s) (hsN : s≤N)
    (hdim : Module.finrank ℚ (ChernQuotientRing s N) = (2*(N-s)+s).choose s) :
    Function.Surjective (chernLowDegreeToQuotient s N) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := chernLowDegreeToQuotient s N) ?_).mp
    (chernLowDegreeToQuotient_injective hs hsN)
  rw [PaperVerification.finrank_restrictTotalDegree, hdim]

/-- The actual quotient coefficient pairing is nondegenerate once the
independent finite-dimensional quotient calculation has been established. -/
theorem chernRingPairing_nondegenerate_of_finrank {s N : ℕ}
    (hs : 0<s) (hsN : s≤N)
    (hdim : Module.finrank ℚ (ChernQuotientRing s N) = (2*(N-s)+s).choose s) :
    (chernRingPairing hs hsN).Nondegenerate := by
  have hsym : (chernRingPairing hs hsN).IsSymm := ⟨fun x y => by
    simp only [chernRingPairing_apply, mul_comm]⟩
  apply hsym.isRefl.nondegenerate_iff_separatingLeft.mpr
  intro x hx
  obtain ⟨P,rfl⟩ := chernLowDegreeToQuotient_surjective_of_finrank hs hsN hdim x
  by_contra hne
  have hpne : (P : MvPolynomial (Fin s) ℚ) ≠ 0 := by
    intro hz
    apply hne
    simp only [chernLowDegreeToQuotient_apply, hz, map_zero]
  have hpbound : BoundedBy (uniformExponent (2*(N-s)))
      (elementarySubstitution s (P : MvPolynomial (Fin s) ℚ)) :=
    elementarySubstitution_bounded_of_totalDegree
      (c := 2*(N-s)) (P : MvPolynomial (Fin s) ℚ)
      ((mem_restrictTotalDegree (Fin s) (2*(N-s))
        (P : MvPolynomial (Fin s) ℚ)).mp P.property)
  have hpair := hx (Ideal.Quotient.mk (chernRelationIdeal (K := ℚ) s N)
    (chernCoefficientReflection s N P))
  rw [chernLowDegreeToQuotient_apply, chernRingPairing_mk] at hpair
  exact chernCoefficientIntegration_reflection_ne_zero hs hsN P hpbound hpne hpair

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0654

section TAF_LiteralSource_0655
/- Original module: PaperVerification.ChernQuotientDuality -/


/-!
# Perfect duality for the actual Chern-relation quotient

The polynomial quotient and coefficient functional were defined independently.
The common-zero calculation, regular sequence theorem and graded dimension
calculation now close the dimension premise in the reflection argument.
Consequently the descended multiplication pairing is perfect over `ℚ`, for
all parameters `0 < s ≤ N` of Section 4.

The annihilator theorem characterizes the literal relation ideal by the actual
coefficient integral. No cohomology or Chow group is defined in this file.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial

/-- The dimension of the literal quotient in the odd-pencil range. -/
theorem chernQuotientRing_finrank (s N : ℕ) :
    Module.finrank ℚ (ChernQuotientRing s N) = (2*(N-s)+s).choose s :=
  odd_chern_relation_quotient_finrank (K := ℚ) s N

/-- Every quotient class has a unique representative of ordinary total degree
at most `2*(N-s)` in the independent Chern variables. -/
theorem chernLowDegreeToQuotient_bijective {s N : ℕ} (hs : 0<s) (hsN : s≤N) :
    Function.Bijective (chernLowDegreeToQuotient s N) :=
  ⟨chernLowDegreeToQuotient_injective hs hsN,
    chernLowDegreeToQuotient_surjective_of_finrank hs hsN
      (chernQuotientRing_finrank s N)⟩

/-- The actual low-degree representative space is linearly equivalent to the
actual quotient; this does not identify either space with geometric cohomology. -/
def chernLowDegreeEquiv {s N : ℕ} (hs : 0<s) (hsN : s≤N) :
    restrictTotalDegree (Fin s) ℚ (2*(N-s)) ≃ₗ[ℚ] ChernQuotientRing s N :=
  LinearEquiv.ofBijective (chernLowDegreeToQuotient s N)
    (chernLowDegreeToQuotient_bijective hs hsN)

/-- Multiplication followed by the actual coefficient integral is nondegenerate. -/
theorem chernRingPairing_nondegenerate {s N : ℕ} (hs : 0<s) (hsN : s≤N) :
    (chernRingPairing hs hsN).Nondegenerate :=
  chernRingPairing_nondegenerate_of_finrank hs hsN (chernQuotientRing_finrank s N)

/-- Perfect duality, as an actual equivalence with the vector-space dual. -/
def chernRingPerfectPairing {s N : ℕ} (hs : 0<s) (hsN : s≤N) :
    ChernQuotientRing s N ≃ₗ[ℚ] Module.Dual ℚ (ChernQuotientRing s N) :=
  (chernRingPairing hs hsN).toDual (chernRingPairing_nondegenerate hs hsN)

@[simp] theorem chernRingPerfectPairing_apply {s N : ℕ} (hs : 0<s) (hsN : s≤N)
    (x y : ChernQuotientRing s N) :
    chernRingPerfectPairing hs hsN x y = chernRingIntegration hs hsN (x*y) := rfl

/-- A Chern polynomial belongs to the relation ideal exactly when every
product with it has zero coefficient integral. -/
theorem mem_chernRelationIdeal_iff_integration_mul_eq_zero
    {s N : ℕ} (hs : 0<s) (hsN : s≤N) (P : MvPolynomial (Fin s) ℚ) :
    P ∈ chernRelationIdeal (K := ℚ) s N ↔
      ∀ Q : MvPolynomial (Fin s) ℚ, chernCoefficientIntegration N (P*Q) = 0 := by
  constructor
  · intro hP Q
    exact chernCoefficientIntegration_ideal_zero hs hsN (P*Q)
      (Ideal.mul_mem_right _ _ hP)
  · intro hP
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (chernRingPairing_nondegenerate hs hsN).1
    intro q
    obtain ⟨Q, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [chernRingPairing_mk]
    exact hP Q

/-- Every later root relation also belongs to the same finite-window ideal. -/
theorem chernCoefficientRelation_mem_chernRelationIdeal
    {s N n : ℕ} (hs : 0<s) (hsN : s≤N) (hn : 2*(N-s)+1≤n) :
    chernCoefficientRelation (K := ℚ) s n ∈ chernRelationIdeal (K := ℚ) s N := by
  rw [mem_chernRelationIdeal_iff_integration_mul_eq_zero hs hsN]
  intro Q
  rw [mul_comm]
  exact chernCoefficientRelation_annihilates hs hsN hn Q

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0655

section TAF_LiteralSource_0656
/- Original module: PaperVerification.ChernPresentationCriterion -/


/-!
# A precise presentation criterion for the Chern algebra

This is an algebraic comparison theorem. Its target is an independently given
commutative rational algebra, its evaluation map is independently given, and
both its dimension and its trace identity are explicit hypotheses. Applying it
to the actual cohomology or Chow ring requires constructing that ring and proving
those geometric hypotheses; this theorem does not assume that application.

The criterion derives generation and all relations at once. It does not require
Poincaré duality of the target as an additional hypothesis.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial

/-- An independent finite-dimensional algebra with the correct tautological
integration identity is the actual Chern-relation quotient. The equivalence
agrees with the given evaluation map on every polynomial, not only on dimensions. -/
theorem chernPresentationCriterion
    {s N : ℕ} (hs : 0<s) (hsN : s≤N)
    {H : Type*} [CommRing H] [Algebra ℚ H] [Module.Finite ℚ H]
    (τ : MvPolynomial (Fin s) ℚ →ₐ[ℚ] H) (trace : H →ₗ[ℚ] ℚ)
    (hdim : Module.finrank ℚ H = (2*(N-s)+s).choose s)
    (htrace : ∀ P : MvPolynomial (Fin s) ℚ,
      trace (τ P) = chernCoefficientIntegration N P) :
    ∃ e : ChernQuotientRing s N ≃ₐ[ℚ] H,
      ∀ P : MvPolynomial (Fin s) ℚ,
        e (Ideal.Quotient.mk (chernRelationIdeal (K := ℚ) s N) P) = τ P := by
  let T : restrictTotalDegree (Fin s) ℚ (2*(N-s)) →ₗ[ℚ] H :=
    τ.toLinearMap.comp (restrictTotalDegree (Fin s) ℚ (2*(N-s))).subtype
  have hker₁ : RingHom.ker τ.toRingHom ≤ chernRelationIdeal (K := ℚ) s N := by
    intro P hP
    change τ P = 0 at hP
    rw [mem_chernRelationIdeal_iff_integration_mul_eq_zero hs hsN]
    intro Q
    rw [← htrace, map_mul, hP, zero_mul, map_zero]
  have hinj : Function.Injective T := by
    intro P Q hPQ
    change τ (P : MvPolynomial (Fin s) ℚ) =
      τ (Q : MvPolynomial (Fin s) ℚ) at hPQ
    apply chernLowDegreeToQuotient_injective hs hsN
    apply Ideal.Quotient.eq.mpr
    apply hker₁
    change τ ((P : MvPolynomial (Fin s) ℚ) - (Q : MvPolynomial (Fin s) ℚ)) = 0
    rw [map_sub,hPQ,sub_self]
  have hsurj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := T)
      (by rw [PaperVerification.finrank_restrictTotalDegree, hdim])).mp hinj
  have hker₂ : chernRelationIdeal (K := ℚ) s N ≤ RingHom.ker τ.toRingHom := by
    intro P hP
    change τ P = 0
    obtain ⟨Q,hQ⟩ := hsurj (τ P)
    change τ (Q : MvPolynomial (Fin s) ℚ) = τ P at hQ
    have hQmem : (Q : MvPolynomial (Fin s) ℚ) ∈
        chernRelationIdeal (K := ℚ) s N := by
      rw [mem_chernRelationIdeal_iff_integration_mul_eq_zero hs hsN]
      intro R
      have heq : τ ((Q : MvPolynomial (Fin s) ℚ)*R) = τ (P*R) := by
        rw [map_mul, map_mul, hQ]
      rw [← htrace, heq, htrace]
      exact chernCoefficientIntegration_ideal_zero hs hsN (P*R)
        (Ideal.mul_mem_right _ _ hP)
    have hQzero : Q = 0 := by
      apply chernLowDegreeToQuotient_injective hs hsN
      rw [map_zero, chernLowDegreeToQuotient_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hQmem
    rw [← hQ, hQzero]
    exact map_zero τ
  let f : ChernQuotientRing s N →ₐ[ℚ] H :=
    Ideal.Quotient.liftₐ (chernRelationIdeal (K := ℚ) s N) τ hker₂
  have hf_inj : Function.Injective f :=
    RingHom.lift_injective_of_ker_le_ideal
      (chernRelationIdeal (K := ℚ) s N) hker₂ hker₁
  have hf_surj : Function.Surjective f := by
    intro x
    obtain ⟨P,hP⟩ := hsurj x
    exact ⟨Ideal.Quotient.mk (chernRelationIdeal (K := ℚ) s N) P, hP⟩
  exact ⟨AlgEquiv.ofBijective f ⟨hf_inj,hf_surj⟩, fun _ => rfl⟩

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0656

section TAF_LiteralSource_0657
/- Original module: PaperVerification.RegularNilpotentFlag -/


/-!
# Invariant subspaces of a single nilpotent Jordan chain

The dimension argument is independent of a choice of Jordan normal form.
A nilpotent endomorphism annihilates an invariant subspace after at most its
own dimension many powers. If the ambient kernels have the dimensions of a
single Jordan block, that invariant subspace must equal the corresponding
kernel. The concrete weighted shift below verifies those kernel dimensions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.RegularNilpotentFlag

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Nilpotence on a finite-dimensional space is detected at its dimension. -/
theorem nilpotent_pow_finrank_eq_zero [Module.Finite K V]
    (T : Module.End K V) (hT : IsNilpotent T) : T ^ Module.finrank K V = 0 := by
  obtain ⟨m,hm⟩ := hT
  apply LinearMap.ker_eq_top.mp
  apply top_unique
  have h := Module.End.ker_pow_le_ker_pow_finrank T m
  simpa only [hm, LinearMap.ker_zero] using h

/-- Restricting a nilpotent map to an invariant subspace preserves nilpotence. -/
theorem nilpotent_restrict (T : Module.End K V) (hT : IsNilpotent T)
    (U : Submodule K V) (hU : ∀ x ∈ U, T x ∈ U) :
    IsNilpotent (T.restrict hU) := by
  obtain ⟨m,hm⟩ := hT
  refine ⟨m,?_⟩
  rw [Module.End.pow_restrict m hU]
  ext x
  change (T^m) x = 0
  rw [hm, LinearMap.zero_apply]

/-- Any invariant `s`-plane of a nilpotent map lies in its `s`th kernel. -/
theorem invariant_le_ker_pow_finrank [Module.Finite K V]
    (T : Module.End K V) (hT : IsNilpotent T)
    (U : Submodule K V) (hU : ∀ x ∈ U, T x ∈ U) :
    U  ≤  LinearMap.ker (T ^ Module.finrank K U) := by
  have hz := nilpotent_pow_finrank_eq_zero (T.restrict hU)
    (nilpotent_restrict T hT U hU)
  intro x hx
  change (T ^ Module.finrank K U) x = 0
  have h := congrArg (fun f : Module.End K U => (f ⟨x,hx⟩ : V)) hz
  rw [Module.End.pow_restrict (Module.finrank K U) hU] at h
  simpa only [LinearMap.coe_restrict_apply,
    LinearMap.zero_apply, ZeroMemClass.coe_zero] using h

/-- The usual single-Jordan-block uniqueness statement, proved by dimensions. -/
theorem invariant_eq_ker_pow [Module.Finite K V]
    (T : Module.End K V) (hT : IsNilpotent T) (s : ℕ)
    (hker : Module.finrank K (LinearMap.ker (T^s)) = s)
    (U : Submodule K V) (hU : ∀ x ∈ U, T x ∈ U)
    (hdim : Module.finrank K U = s) : U = LinearMap.ker (T^s) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · simpa only [hdim] using invariant_le_ker_pow_finrank T hT U hU
  · exact hdim.trans hker.symm

section WeightedShift

variable {n : ℕ}

/-- In coordinates ordered along a Jordan chain, nonzero coefficients may
rescale the arrows without changing the invariant subspaces. -/
def weightedShift (a : Fin n → K) : Module.End K (Fin n → K) where
  toFun v i := if h : i.val+1 < n then a i * v ⟨i.val+1,h⟩ else 0
  map_add' u v := by
    funext i
    by_cases h : i.val+1 < n <;> simp [h,mul_add]
  map_smul' r v := by
    funext i
    by_cases h : i.val+1 < n <;> simp [h,mul_left_comm]

@[simp] theorem weightedShift_apply (a : Fin n → K) (v : Fin n → K) (i : Fin n) :
    weightedShift a v i = if h : i.val+1 < n then a i * v ⟨i.val+1,h⟩ else 0 := rfl

@[simp] theorem weightedShift_single_zero {n : ℕ} (a : Fin (n+1) → K) :
    weightedShift a (Pi.single 0 1)=0 := by
  funext i
  rw [weightedShift_apply]
  split_ifs with h
  · have hz : (0 : Fin (n+1)) ≠ ⟨i.val+1,h⟩ := by
      intro he
      have he' := congrArg Fin.val he
      simp only [Fin.val_zero,Fin.val_mk] at he'
      omega
    simp only [Pi.single_apply,if_neg hz.symm,mul_zero,Pi.zero_apply]
  · rfl

@[simp] theorem weightedShift_single_succ {n : ℕ} (a : Fin (n+1) → K) (i : Fin n) :
    weightedShift a (Pi.single i.succ 1)=a i.castSucc • Pi.single i.castSucc 1 := by
  ext j
  by_cases h : j=i.castSucc
  · subst j
    simp [weightedShift_apply,Pi.single_apply,Fin.ext_iff,show i.val+1 < n+1 by omega]
  · have hv : j.val≠i.val := fun he => h (Fin.ext he)
    rw [weightedShift_apply]
    split_ifs <;> simp [Pi.single_apply,Fin.ext_iff,hv,Ne.symm hv]

/-- Once a power passes the end of the chain, its coordinate is zero. -/
theorem weightedShift_pow_apply_of_le (a : Fin n → K) (m : ℕ)
    (v : Fin n → K) (i : Fin n) (hi : n ≤ i.val+m) :
    ((weightedShift a)^m) v i = 0 := by
  induction m generalizing i with
  | zero => have := i.isLt; omega
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, weightedShift_apply]
    split_ifs with h
    · rw [ih ⟨i.val+1,h⟩ (by dsimp; omega), mul_zero]
    · rfl

/-- Before the end of the chain, every coefficient is a product of nonzero
arrow coefficients, so a coordinate vanishes exactly when its source does. -/
theorem weightedShift_pow_apply_eq_zero_iff (a : Fin n → K)
    (ha : ∀ i : Fin n, i.val+1 < n → a i ≠ 0) (m : ℕ)
    (v : Fin n → K) (i : Fin n) (hi : i.val+m < n) :
    ((weightedShift a)^m) v i = 0 ↔ v ⟨i.val+m,hi⟩ = 0 := by
  induction m generalizing i with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, weightedShift_apply,
      dif_pos (show i.val+1 < n by omega), mul_eq_zero]
    simp only [ha i (by omega), false_or]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      ih ⟨i.val+1,by omega⟩ (by dsimp; omega)

/-- The kernel of each power is exactly the space supported on the initial
segment; this identifies actual vectors and actual linear kernels. -/
theorem weightedShift_pow_eq_zero_iff (a : Fin n → K)
    (ha : ∀ i : Fin n, i.val+1 < n → a i ≠ 0) (m : ℕ) (v : Fin n → K) :
    ((weightedShift a)^m) v = 0 ↔ ∀ j : Fin n, m ≤ j.val → v j = 0 := by
  constructor
  · intro h j hj
    let i : Fin n := ⟨j.val-m, by omega⟩
    have hi : i.val+m < n := by dsimp [i]; omega
    have hz : ((weightedShift a)^m) v i = 0 := congrFun h i
    have hsource := (weightedShift_pow_apply_eq_zero_iff a ha m v i hi).mp hz
    convert hsource using 1
    apply congrArg v
    apply Fin.ext
    dsimp [i]
    omega
  · intro h
    funext i
    by_cases hi : i.val+m < n
    · exact (weightedShift_pow_apply_eq_zero_iff a ha m v i hi).mpr
        (h ⟨i.val+m,hi⟩ (by dsimp; omega))
    · exact weightedShift_pow_apply_of_le a m v i (by omega)

theorem weightedShift_ker_pow (a : Fin n → K)
    (ha : ∀ i : Fin n, i.val+1 < n → a i ≠ 0) (m : ℕ) :
    LinearMap.ker ((weightedShift a)^m) =
      Pi.spanSubset K {i : Fin n | i.val < m} := by
  ext v
  rw [LinearMap.mem_ker, weightedShift_pow_eq_zero_iff a ha,
    Pi.mem_spanSubset_iff]
  simp only [Set.mem_setOf_eq, not_lt]

theorem weightedShift_nilpotent (a : Fin n → K) : IsNilpotent (weightedShift a) := by
  refine ⟨n,?_⟩
  apply LinearMap.ext
  intro v
  funext i
  change ((weightedShift a)^n) v i = 0
  exact weightedShift_pow_apply_of_le a n v i (by omega)

/-- The initial coordinate segment has its actual expected dimension. -/
theorem finrank_prefix (m : ℕ) (hm : m ≤ n) :
    Module.finrank K (Pi.spanSubset K {i : Fin n | i.val < m}) = m := by
  rw [Pi.dim_spanSubset, ← Nat.card_coe_set_eq]
  let e : {i : Fin n // i.val < m} ≃ Fin m :=
    { toFun := fun i => ⟨i.val.val,i.property⟩
      invFun := fun i => ⟨⟨i.val,lt_of_lt_of_le i.isLt hm⟩,i.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (Nat.card_fin m)

/-- Initial coordinate spaces are invariant under every weighted lowering map. -/
theorem weightedShift_prefix_invariant (a : Fin n → K) (m : ℕ)
    (v : Fin n → K) (hv : v ∈ Pi.spanSubset K {i : Fin n | i.val < m}) :
    weightedShift a v ∈ Pi.spanSubset K {i : Fin n | i.val < m} := by
  rw [Pi.mem_spanSubset_iff] at hv ⊢
  intro i hi
  rw [weightedShift_apply]
  split_ifs with h
  · have hige : m ≤ i.val := by simpa only [Set.mem_setOf_eq,not_lt] using hi
    rw [hv ⟨i.val+1,h⟩ (by simp only [Set.mem_setOf_eq,not_lt]; omega),mul_zero]
  · rfl

/-- Every invariant subspace of a weighted single Jordan chain is the initial
coordinate subspace of the same dimension. -/
theorem weightedShift_invariant_subspace_unique (a : Fin n → K)
    (ha : ∀ i : Fin n, i.val+1 < n → a i ≠ 0) (m : ℕ) (hm : m ≤ n)
    (U : Submodule K (Fin n → K))
    (hU : ∀ x ∈ U, weightedShift a x ∈ U)
    (hdim : Module.finrank K U = m) :
    U = Pi.spanSubset K {i : Fin n | i.val < m} := by
  rw [← weightedShift_ker_pow a ha]
  apply invariant_eq_ker_pow _ (weightedShift_nilpotent a) m _ U hU hdim
  rw [weightedShift_ker_pow a ha, finrank_prefix m hm]

end WeightedShift

end PaperVerification.RegularNilpotentFlag
end
end
end TAF_LiteralSource_0657

section TAF_LiteralSource_0658
/- Original module: PaperVerification.NilpotentExponentialInvariant -/


/-!
# Invariant subspaces of the genuine finite exponential action

For a nilpotent linear map over a characteristic-zero field, invariance under
all finite exponentials is equivalent to invariance under the linear map.
The reverse implication extracts the coefficient of the parameter from an
actual scalar polynomial. No differentiability or Lie-theoretic assertion is
assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace PaperVerification.NilpotentExponentialInvariant

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
  [Module ℚ V] [IsScalarTower ℚ K V] [SMulCommClass ℚ K V]

/-- A scalar coordinate of the finite exponential orbit is an actual polynomial. -/
def scalarOrbitPolynomial (T : Module.End K V) (v : V) (ℓ : V →ₗ[K] K)
    (n : ℕ) : Polynomial K :=
  ∑ i ∈ Finset.range n,
    Polynomial.C ((i.factorial : K)⁻¹ * ℓ ((T^i) v)) * Polynomial.X^i

/-- The polynomial has precisely the scalar values of the finite exponential. -/
theorem scalarOrbitPolynomial_eval (T : Module.End K V) (v : V)
    (ℓ : V →ₗ[K] K) (n : ℕ) (hn : T^n=0) (u : K) :
    (scalarOrbitPolynomial T v ℓ n).eval u = ℓ (IsNilpotent.exp (u • T) v) := by
  have hu : (u • T)^n=0 := by rw [smul_pow,hn,smul_zero]
  rw [IsNilpotent.exp_eq_sum hu]
  simp only [scalarOrbitPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_rat_smul,
    smul_pow, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [LinearMap.smul_apply, Algebra.smul_def, map_inv₀, map_natCast,Algebra.algebraMap_self,RingHom.id_apply]
  ring

/-- Stability under the infinitesimal map implies stability under every genuine
finite exponential, by the finite sum defining the exponential. -/
theorem exponential_invariant_of_invariant
    (T : Module.End K V) (hT : IsNilpotent T) (U : Submodule K V)
    (hU : ∀ v ∈ U, T v ∈ U) :
    ∀ u : K, ∀ v ∈ U, IsNilpotent.exp (u • T) v ∈ U := by
  obtain ⟨n,hn⟩ := hT
  intro u v hv
  have hu : (u • T)^n=0 := by rw [smul_pow,hn,smul_zero]
  rw [IsNilpotent.exp_eq_sum hu, LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro i hi
  rw [LinearMap.smul_apply]
  apply (U.restrictScalars ℚ).smul_mem
  change ((u • T)^i) v ∈ U
  apply Module.End.pow_apply_mem_of_forall_mem
  · intro x hx
    exact U.smul_mem u (hU x hx)
  · exact hv

/-- If an entire exponential orbit stays in a linear subspace, its linear
coefficient does too. A separating functional would give an identically zero
polynomial with nonzero linear coefficient. -/
theorem invariant_of_exponential_invariant
    (T : Module.End K V) (hT : IsNilpotent T) (U : Submodule K V)
    (hU : ∀ u : K, ∀ v ∈ U, IsNilpotent.exp (u • T) v ∈ U) :
    ∀ v ∈ U, T v ∈ U := by
  intro v hv
  by_contra hnot
  obtain ⟨ℓ,hℓne,hℓ⟩ := Submodule.exists_le_ker_of_notMem hnot
  obtain ⟨n,hn⟩ := hT
  have hn' : T^(n+2)=0 := pow_eq_zero_of_le (by omega) hn
  have hp : scalarOrbitPolynomial T v ℓ (n+2) = 0 := by
    apply Polynomial.zero_of_eval_zero
    intro u
    rw [scalarOrbitPolynomial_eval T v ℓ (n+2) hn' u]
    exact hℓ (hU u v hv)
  have hc := congrArg (fun p : Polynomial K => p.coeff 1) hp
  have h1 : 1 < n+2 := by omega
  have hcoeff : (scalarOrbitPolynomial T v ℓ (n+2)).coeff 1 = ℓ (T v) := by
    simp only [scalarOrbitPolynomial, Polynomial.finsetSum_coeff,
      Polynomial.coeff_C_mul_X_pow]
    simp [h1]
  rw [hcoeff, Polynomial.coeff_zero] at hc
  exact hℓne hc

/-- Invariant subspaces of the additive one-parameter action are exactly the
invariant subspaces of its nilpotent generator. -/
theorem exponential_invariant_iff
    (T : Module.End K V) (hT : IsNilpotent T) (U : Submodule K V) :
    (∀ u : K, ∀ v ∈ U, IsNilpotent.exp (u • T) v ∈ U) ↔
      (∀ v ∈ U, T v ∈ U) :=
  ⟨invariant_of_exponential_invariant T hT U,
    exponential_invariant_of_invariant T hT U⟩

/-- Equality under the actual linear-map action on subspaces is equivalent to
stability under the entire exponential family; inverse parameters supply the
reverse inclusion. -/
theorem exponential_map_eq_iff
    (T : Module.End K V) (hT : IsNilpotent T) (U : Submodule K V) :
    (∀ u : K, U.map (IsNilpotent.exp (u • T)) = U) ↔
      (∀ u : K, ∀ v ∈ U, IsNilpotent.exp (u • T) v ∈ U) := by
  constructor
  · intro h u v hv
    have hm : IsNilpotent.exp (u • T) v ∈ U.map (IsNilpotent.exp (u • T)) :=
      Submodule.mem_map.mpr ⟨v,hv,rfl⟩
    rwa [h u] at hm
  · intro h u
    apply le_antisymm
    · rintro x ⟨v,hv,rfl⟩
      exact h u v hv
    · intro v hv
      apply Submodule.mem_map.mpr
      refine ⟨IsNilpotent.exp ((-u) • T) v,h (-u) v hv,?_⟩
      change (IsNilpotent.exp (u • T)*IsNilpotent.exp ((-u) • T)) v = v
      rw [neg_smul,IsNilpotent.exp_mul_exp_neg_self (hT.smul u),Module.End.one_apply]

/-- The finite exponentials satisfy the additive group law. -/
theorem exponential_add
    (T : Module.End K V) (hT : IsNilpotent T) (u v : K) :
    IsNilpotent.exp ((u+v) • T) =
      IsNilpotent.exp (u • T) * IsNilpotent.exp (v • T) := by
  rw [add_smul]
  apply IsNilpotent.exp_add_of_commute
  · change (u • T)*(v • T)=(v • T)*(u • T)
    simp [smul_mul_assoc,mul_smul_comm,smul_smul,mul_comm]
  · exact hT.smul u
  · exact hT.smul v

end PaperVerification.NilpotentExponentialInvariant
end
end
end TAF_LiteralSource_0658

section TAF_LiteralSource_0659
/- Original module: PaperVerification.AlternatingFormsCanonicalUnipotent -/


/-!
# The canonical odd pencil and its unique unipotent fixed plane

Coordinates are ordered along the chain
`b₀,b₁,...,bₖ,aₖ,aₖ₋₁,...,a₁`. In these coordinates the nilpotent operator of
Section 4.1 is a weighted lowering shift. Its coefficient at the single bridge
from `aₖ` to `bₖ` is one; every other coefficient is the coordinate index minus
`k`. This includes `k=0` without an exceptional definition.

The two forms below are actual bilinear forms and their mixed basis values
are precisely the two incidence pairings from the paper. The unique-fixed-plane
statement concerns actual subspaces, their dimensions, and the genuine finite
exponential linear action.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace PaperVerification.AlternatingForms.CanonicalUnipotent

open RegularNilpotentFlag NilpotentExponentialInvariant

variable {K : Type*} [Field K] [CharZero K]

abbrev ChainSpace (K : Type*) (k : ℕ) := Fin (2*k+1) → K

/-- Nonzero arrow coefficients in the paper's single Jordan chain. -/
def chainCoefficient (k : ℕ) (i : Fin (2*k+1)) : K :=
  if i.val=k then 1 else (i.val : K)-(k : K)

theorem chainCoefficient_ne_zero (k : ℕ) (i : Fin (2*k+1)) :
    chainCoefficient (K := K) k i ≠ 0 := by
  unfold chainCoefficient
  split_ifs with h
  · exact one_ne_zero
  · apply sub_ne_zero.mpr
    exact_mod_cast h

/-- The actual nilpotent endomorphism in chain coordinates. -/
def generator (k : ℕ) : Module.End K (ChainSpace K k) :=
  weightedShift (chainCoefficient k)

theorem generator_nilpotent (k : ℕ) : IsNilpotent (generator (K := K) k) :=
  weightedShift_nilpotent _

/-- The actual additive one-parameter family, using Mathlib's finite exponential. -/
def gaMap (k : ℕ) (u : K) : Module.End K (ChainSpace K k) :=
  IsNilpotent.exp (u • generator k)

@[simp] theorem gaMap_zero (k : ℕ) : gaMap (K := K) k 0 = 1 := by
  simp [gaMap]

theorem gaMap_add (k : ℕ) (u v : K) : gaMap k (u+v) = gaMap k u * gaMap k v :=
  exponential_add _ (generator_nilpotent k) u v

theorem gaMap_isUnit (k : ℕ) (u : K) : IsUnit (gaMap k u) :=
  IsNilpotent.isUnit_exp ((generator_nilpotent k).smul u)

/-- The actual span of the first `s` vectors of the Jordan chain. -/
abbrev fixedPlane (k s : ℕ) : Submodule K (ChainSpace K k) :=
  Pi.spanSubset K {i : Fin (2*k+1) | i.val < s}

theorem fixedPlane_finrank (k s : ℕ) (hs : s ≤ 2*k+1) :
    Module.finrank K (fixedPlane (K := K) k s) = s := finrank_prefix s hs

theorem fixedPlane_invariant (k s : ℕ) :
    ∀ u : K, (fixedPlane (K := K) k s).map (gaMap k u) = fixedPlane k s := by
  unfold gaMap
  apply (exponential_map_eq_iff (K:=K) (V:=ChainSpace K k)
    (generator k) (generator_nilpotent k) _).mpr
  apply exponential_invariant_of_invariant (K:=K) _ (generator_nilpotent k)
  exact weightedShift_prefix_invariant (chainCoefficient k) s

/-- The exponential subgroup fixes exactly one plane of each dimension. -/
theorem fixedPlane_unique (k s : ℕ) (hs : s ≤ 2*k+1)
    (U : Submodule K (ChainSpace K k)) (hdim : Module.finrank K U=s)
    (hfixed : ∀ u : K, U.map (gaMap k u)=U) : U=fixedPlane k s := by
  unfold gaMap at hfixed
  have hstable := (exponential_map_eq_iff (K:=K) (V:=ChainSpace K k)
    (generator k) (generator_nilpotent k) U).mp hfixed
  have hgen := invariant_of_exponential_invariant (K:=K)
    (generator k) (generator_nilpotent k) U hstable
  exact weightedShift_invariant_subspace_unique (chainCoefficient k)
    (fun i _ => chainCoefficient_ne_zero k i) s hs U hgen hdim

/-- A skew anti-diagonal matrix, with the orientation of `aᵢ∧bⱼ`. -/
def skewAntiDiagonal (k r : ℕ) : Matrix (Fin (2*k+1)) (Fin (2*k+1)) K :=
  fun i j => if i.val+j.val=r then
    (if i.val < j.val then -1 else if j.val < i.val then 1 else 0) else 0

theorem skewAntiDiagonal_swap (k r : ℕ) (i j : Fin (2*k+1)) :
    skewAntiDiagonal (K := K) k r i j = -skewAntiDiagonal k r j i := by
  unfold skewAntiDiagonal
  by_cases h : i.val+j.val=r
  · have h' : j.val+i.val=r := by omega
    simp only [if_pos h,if_pos h']
    rcases lt_trichotomy i.val j.val with hij|hij|hij
    · simp [hij,show ¬ j.val < i.val by omega]
    · simp [hij]
    · simp [hij,show ¬ i.val < j.val by omega]
  · have h' : ¬ j.val+i.val=r := by omega
    simp only [if_neg h,if_neg h',neg_zero]

theorem skewAntiDiagonal_isAlt (k r : ℕ) :
    ((skewAntiDiagonal (K := K) k r).toBilin').IsAlt := by
  apply LinearMap.isAlt_iff_eq_neg_flip.mpr
  apply (Pi.basisFun K (Fin (2*k+1))).ext
  intro i
  apply (Pi.basisFun K (Fin (2*k+1))).ext
  intro j
  simp only [Pi.basisFun_apply,LinearMap.neg_apply,LinearMap.flip_apply,
    Matrix.toBilin'_single]
  exact skewAntiDiagonal_swap k r i j

/-- The two canonical pairings in chain coordinates. -/
def firstForm (k : ℕ) : LinearMap.BilinForm K (ChainSpace K k) :=
  (skewAntiDiagonal k (2*k+1)).toBilin'

def secondForm (k : ℕ) : LinearMap.BilinForm K (ChainSpace K k) :=
  (skewAntiDiagonal k (2*k)).toBilin'

theorem firstForm_isAlt (k : ℕ) : (firstForm (K:=K) k).IsAlt :=
  skewAntiDiagonal_isAlt k (2*k+1)

theorem secondForm_isAlt (k : ℕ) : (secondForm (K:=K) k).IsAlt :=
  skewAntiDiagonal_isAlt k (2*k)

/-- Position of `aᵢ₊₁` in the chain basis. -/
def aIndex (k : ℕ) (i : Fin k) : Fin (2*k+1) := ⟨2*k-i.val,by omega⟩

/-- Position of `bⱼ` in the chain basis. -/
def bIndex (k : ℕ) (j : Fin (k+1)) : Fin (2*k+1) := ⟨j.val,by omega⟩

/-- This is exactly the first incidence pairing of Section 4. -/
theorem firstForm_a_b (k : ℕ) (i : Fin k) (j : Fin (k+1)) :
    firstForm (K := K) k (Pi.single (aIndex k i) 1) (Pi.single (bIndex k j) 1) =
      if j.val=i.val+1 then 1 else 0 := by
  rw [firstForm,Matrix.toBilin'_single]
  change (if 2*k-i.val+j.val=2*k+1 then
    (if 2*k-i.val < j.val then -1 else if j.val < 2*k-i.val then 1 else 0) else 0) = _
  have hi := i.isLt
  have hj := j.isLt
  have hlt : j.val < 2*k-i.val := by omega
  have he : (2*k-i.val+j.val=2*k+1) ↔ j.val=i.val+1 := by omega
  simp only [not_lt_of_gt hlt,if_false,if_pos hlt,he]

/-- This is exactly the second incidence pairing of Section 4. -/
theorem secondForm_a_b (k : ℕ) (i : Fin k) (j : Fin (k+1)) :
    secondForm (K := K) k (Pi.single (aIndex k i) 1) (Pi.single (bIndex k j) 1) =
      if j.val=i.val then 1 else 0 := by
  rw [secondForm,Matrix.toBilin'_single]
  change (if 2*k-i.val+j.val=2*k then
    (if 2*k-i.val < j.val then -1 else if j.val < 2*k-i.val then 1 else 0) else 0) = _
  have hi := i.isLt
  have hj := j.isLt
  have hlt : j.val < 2*k-i.val := by omega
  have he : (2*k-i.val+j.val=2*k) ↔ j.val=i.val := by omega
  simp only [not_lt_of_gt hlt,if_false,if_pos hlt,he]

theorem skewAntiDiagonal_low_zero (k r : ℕ) (hr : r=2*k ∨ r=2*k+1)
    (i j : Fin (2*k+1)) (hi : i.val ≤ k) (hj : j.val ≤ k) :
    skewAntiDiagonal (K := K) k r i j = 0 := by
  unfold skewAntiDiagonal
  rcases hr with rfl|rfl <;> split_ifs <;> (first | rfl | omega)

/-- Common isotropy refers to the actual two bilinear forms. -/
def IsCommonIsotropic (k : ℕ) (U : Submodule K (ChainSpace K k)) : Prop :=
  ∀ u ∈ U, ∀ v ∈ U, firstForm k u v=0 ∧ secondForm k u v=0

/-- The unique invariant plane lies in the common isotropic locus throughout
exactly the range used in Section 4. -/
theorem fixedPlane_common_isotropic (k s : ℕ) (hs : s ≤ k+1) :
    IsCommonIsotropic k (fixedPlane (K := K) k s) := by
  intro u hu v hv
  rw [Pi.mem_spanSubset_iff] at hu hv
  have hform (r : ℕ) (hr : r=2*k ∨ r=2*k+1) :
      (skewAntiDiagonal (K := K) k r).toBilin' u v=0 := by
    rw [Matrix.toBilin'_apply]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    by_cases hi : i.val < s
    · by_cases hj : j.val < s
      · rw [skewAntiDiagonal_low_zero k r hr i j (by omega) (by omega)]
        simp
      · rw [hv j hj,mul_zero]
    · rw [hu i hi,zero_mul,zero_mul]
  exact ⟨hform _ (Or.inr rfl),hform _ (Or.inl rfl)⟩

/-- The canonical common isotropic locus has a unique unipotent-fixed `s`-plane.
This is a statement about all actual subspaces, not a selected coordinate list. -/
theorem existsUnique_fixed_common_isotropic_plane (k s : ℕ) (hs : s ≤ k+1) :
    ∃! U : Submodule K (ChainSpace K k),
      Module.finrank K U=s ∧ IsCommonIsotropic k U ∧
        ∀ u : K, U.map (gaMap k u)=U := by
  refine ⟨fixedPlane k s,⟨fixedPlane_finrank k s (by omega),
    fixedPlane_common_isotropic k s hs,fixedPlane_invariant k s⟩,?_⟩
  intro U hU
  exact fixedPlane_unique k s (by omega) U hU.1 hU.2.2

end PaperVerification.AlternatingForms.CanonicalUnipotent
end
end
end TAF_LiteralSource_0659

section TAF_LiteralSource_0660
/- Original module: PaperVerification.AlternatingFormsBorelWeights -/


/-!
# The finite weight identities in Section 4.1

The two triangular families of normal weights are matched with an actual
rectangle by an explicit weight-preserving bijection. Repeated weights are
retained by the indexing equivalence; this is stronger than equality of the
underlying sets. The telescoping formula uses products in an arbitrary
commutative monoid and therefore introduces no division by a potentially zero
specialization.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace PaperVerification.AlternatingForms.BorelWeights

/-- Strictly ordered pairs of basis indices. -/
abbrev UpperPair (s : ℕ) := {p : Fin s × Fin s // p.1.val < p.2.val}

/-- The two normal-weight families have precisely the multiplicities of the
`s` by `s-1` rectangle. -/
def triangleRectangleEquiv (s : ℕ) :
    UpperPair s ⊕ UpperPair s ≃ Fin s × Fin (s-1) where
  toFun
    | Sum.inl p => (p.val.2, ⟨p.val.1.val, by have := p.property; have := p.val.2.isLt; omega⟩)
    | Sum.inr p => (p.val.1, ⟨p.val.2.val-1, by have := p.property; have := p.val.2.isLt; omega⟩)
  invFun p := if h : p.1.val ≤ p.2.val then
    Sum.inr ⟨(p.1, ⟨p.2.val+1, by have := p.2.isLt; omega⟩), by dsimp; omega⟩
    else
    Sum.inl ⟨(⟨p.2.val, by have := p.2.isLt; omega⟩,p.1), by dsimp; omega⟩
  left_inv := by
    rintro (⟨⟨i,j⟩,hij⟩|⟨⟨i,j⟩,hij⟩)
    · dsimp at hij
      dsimp
      rw [dif_neg (show ¬ j.val ≤ i.val by omega)]
    · dsimp at hij
      dsimp
      rw [dif_pos (show i.val ≤ j.val-1 by omega)]
      apply congrArg Sum.inr
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega
  right_inv := by
    rintro ⟨i,h⟩
    dsimp
    split_ifs with hih
    · apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega
    · rfl

/-- The triangular weights as written after reflection in Section 4.1. -/
def triangleWeight {s : ℕ} : UpperPair s ⊕ UpperPair s → ℕ
  | Sum.inl p => p.val.1.val+p.val.2.val
  | Sum.inr p => p.val.1.val+p.val.2.val-1

/-- The explicit bijection preserves the weight, including its multiplicity. -/
theorem triangleRectangleEquiv_weight {s : ℕ} (p : UpperPair s ⊕ UpperPair s) :
    (triangleRectangleEquiv s p).1.val+(triangleRectangleEquiv s p).2.val =
      triangleWeight p := by
  cases p with
  | inl p => simp only [triangleRectangleEquiv, Equiv.coe_fn_mk, triangleWeight]; omega
  | inr p =>
    simp only [triangleRectangleEquiv, Equiv.coe_fn_mk, triangleWeight]
    have := p.property
    omega

/-- Any multiplicative statistic of the normal weights agrees with the
rectangle statistic, in every size. -/
theorem triangular_weight_product {M : Type*} [CommMonoid M]
    (s : ℕ) (f : ℕ → M) :
    (∏ p : UpperPair s, f (p.val.1.val+p.val.2.val)) *
      (∏ p : UpperPair s, f (p.val.1.val+p.val.2.val-1)) =
      ∏ i : Fin s, ∏ h : Fin (s-1), f (i.val+h.val) := by
  have h := Equiv.prod_comp (triangleRectangleEquiv s)
    (fun p : Fin s × Fin (s-1) => f (p.1.val+p.2.val))
  simp only [triangleRectangleEquiv_weight, Fintype.prod_sum_type, triangleWeight,
    Fintype.prod_prod_type] at h
  exact h

/-- A denominator-free telescope for one row of tangent weights. -/
theorem telescope_row {M : Type*} [CommMonoid M] (f : ℕ → M) (a c : ℕ) :
    (∏ j ∈ Finset.range c, f (a+j+1))*f a =
      (∏ j ∈ Finset.range c, f (a+j))*f (a+c) := by
  induction c with
  | zero => simp
  | succ c ih =>
    simpa only [Finset.prod_range_succ, Nat.add_zero, Nat.add_assoc,
      Nat.succ_eq_add_one, mul_assoc, mul_comm, mul_left_comm] using
      congrArg (fun x => x*f (a+c+1)) ih

end PaperVerification.AlternatingForms.BorelWeights
end
end
end TAF_LiteralSource_0660

section TAF_LiteralSource_0661
/- Original module: PaperVerification.PolynomialOrbitFixedPoint -/


/-!
# Leading terms of polynomial additive-group orbits

The projective fixed-point argument for a one-parameter unipotent group has an
elementary polynomial core. The highest nonzero coefficient of a polynomial
orbit is fixed by every group element. Every homogeneous equation vanishing
on the orbit also vanishes on this coefficient. These statements concern
actual matrices, polynomial evaluation and homogeneous equations; no
fixed-point or smoothness theorem is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.PolynomialOrbitFixedPoint

open scoped BigOperators Matrix
open Polynomial

variable {K ι : Type*} [Field K]

/-- The coefficient at the sum of upper degree bounds is multiplicative. -/
theorem coeff_prod_sum_bounds {α : Type*} (s : Finset α)
    (p : α → Polynomial K) (d : α → ℕ)
    (hd : ∀ i ∈ s, (p i).natDegree  ≤  d i) :
    (∏ i ∈ s, p i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (p i).coeff (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi,
      Polynomial.coeff_mul_add_eq_of_natDegree_le (hd i (Finset.mem_insert_self _ _))]
    · rw [ih (fun j hj => hd j (Finset.mem_insert_of_mem hj))]
    · exact (Polynomial.natDegree_prod_le s p).trans
        (Finset.sum_le_sum fun j hj => hd j (Finset.mem_insert_of_mem hj))

/-- A homogeneous polynomial evaluated on polynomial coordinates has its
top possible coefficient obtained by evaluating on the top coefficients. -/
theorem homogeneous_substitution_top_coefficient
    (p : ι → Polynomial K) (d : ℕ) (hd : ∀ i, (p i).natDegree  ≤  d)
    (f : MvPolynomial ι K) (e : ℕ) (hf : f.IsHomogeneous e) :
    (MvPolynomial.aeval p f).coeff (d*e) =
      MvPolynomial.aeval (fun i => (p i).coeff d) f := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, Polynomial.finsetSum_coeff, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hdegree : a.degree = e := by
    rw [Finsupp.degree_eq_weight_one]
    exact hf (MvPolynomial.mem_support_iff.mp ha)
  simp only [MvPolynomial.aeval_monomial,
    Polynomial.algebraMap_eq, Algebra.algebraMap_self, RingHom.id_apply,
    Polynomial.coeff_C_mul]
  congr 1
  have hsum : (∑ i ∈ a.support, a i*d) = d*e := by
    rw [← Finset.sum_mul, ← Finsupp.degree_apply, hdegree, Nat.mul_comm]
  rw [Finsupp.prod, ← hsum, coeff_prod_sum_bounds]
  · apply Finset.prod_congr rfl
    intro i hi
    exact Polynomial.coeff_pow_of_natDegree_le (hd i)
  · intro i hi
    exact Polynomial.natDegree_pow_le_of_le _ (hd i)

/-- Substituting into a multivariate polynomial commutes with evaluation of
the orbit parameter. -/
theorem eval_substitution (p : ι → Polynomial K) (f : MvPolynomial ι K) (u : K) :
    (MvPolynomial.aeval p f).eval u =
      MvPolynomial.aeval (fun i => (p i).eval u) f := by
  have h : (Polynomial.aeval u).comp (MvPolynomial.aeval p) =
      MvPolynomial.aeval (fun i => (p i).eval u) := by
    ext i
    simp
  exact DFunLike.congr_fun h f

/-- Homogeneous equations persist at the leading point of a polynomial
orbit. Infinitude is used only to turn vanishing at all parameters into a
polynomial identity. -/
theorem homogeneous_vanishes_on_top_coefficient [Infinite K]
    (p : ι → Polynomial K) (d : ℕ) (hd : ∀ i, (p i).natDegree  ≤  d)
    (f : MvPolynomial ι K) (e : ℕ) (hf : f.IsHomogeneous e)
    (hvanish : ∀ u : K, MvPolynomial.aeval (fun i => (p i).eval u) f = 0) :
    MvPolynomial.aeval (fun i => (p i).coeff d) f = 0 := by
  have hz : MvPolynomial.aeval p f = 0 :=
    Polynomial.zero_of_eval_zero _ (fun u => by rw [eval_substitution]; exact hvanish u)
  rw [← homogeneous_substitution_top_coefficient p d hd f e hf, hz]
  simp

/-- Translation preserves the coefficient at any common upper degree
bound, including the case when that coefficient is zero. -/
theorem coeff_taylor_of_degree_le (p : Polynomial K) (u : K) (d : ℕ)
    (hd : p.natDegree  ≤  d) : (Polynomial.taylor u p).coeff d = p.coeff d := by
  obtain h | h := lt_or_eq_of_le hd
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (by simpa only [Polynomial.natDegree_taylor] using h),
      Polynomial.coeff_eq_zero_of_natDegree_lt h]
  · subst d
    exact Polynomial.coeff_taylor_natDegree u p

/-- Every matrix fixing the polynomial orbit by translation fixes its
leading coefficient vector. -/
theorem top_coefficient_fixed [Fintype ι] [Infinite K]
    (A : K → Matrix ι ι K) (p : ι → Polynomial K) (d : ℕ)
    (hd : ∀ i, (p i).natDegree  ≤  d)
    (horbit : ∀ u t : K, A u *ᵥ (fun i => (p i).eval t) =
      fun i => (p i).eval (u+t)) (u : K) :
    A u *ᵥ (fun i => (p i).coeff d) = fun i => (p i).coeff d := by
  classical
  funext i
  have hpoly : (∑ j, Polynomial.C (A u i j) * p j) = Polynomial.taylor u (p i) := by
    apply Polynomial.funext
    intro t
    simpa only [Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.taylor_apply, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
      add_comm t u, Matrix.mulVec, dotProduct] using congrFun (horbit u t) i
  have hcoeff := congrArg (fun q : Polynomial K => q.coeff d) hpoly
  simpa only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    coeff_taylor_of_degree_le (p i) u d (hd i), Matrix.mulVec, dotProduct] using hcoeff

/-- A nonzero polynomial vector has a common degree bound with a nonzero
coefficient vector at that bound. -/
theorem exists_nonzero_top_coefficient [Fintype ι]
    (p : ι → Polynomial K) (hp : ∃ i, p i ≠ 0) :
    ∃ d : ℕ, (∀ i, (p i).natDegree  ≤  d) ∧ (fun i => (p i).coeff d) ≠ 0 := by
  classical
  let s : Finset ι := Finset.univ.filter (fun i => p i ≠ 0)
  have hs : s.Nonempty := by
    obtain ⟨i,hi⟩ := hp
    exact ⟨i,by simp [s,hi]⟩
  obtain ⟨i,hi,hmax⟩ := Finset.exists_mem_eq_sup s hs (fun i => (p i).natDegree)
  refine ⟨s.sup (fun i => (p i).natDegree), ?_, ?_⟩
  · intro j
    by_cases hj : p j = 0
    · simp [hj]
    · exact Finset.le_sup (f := fun i => (p i).natDegree) (by simp [s,hj])
  · intro hzero
    have hpi : p i ≠ 0 := (Finset.mem_filter.mp hi).2
    have hcoeff := congrFun hzero i
    rw [hmax, Polynomial.coeff_natDegree] at hcoeff
    exact (Polynomial.leadingCoeff_ne_zero.mpr hpi) hcoeff

/-- The algebraic fixed-point conclusion needed for a homogeneous closed
subset of projective space containing a nonempty polynomial orbit. -/
theorem exists_nonzero_fixed_common_zero [Fintype ι] [Infinite K]
    (A : K → Matrix ι ι K) (p : ι → Polynomial K) (hp : ∃ i, p i ≠ 0)
    (horbit : ∀ u t : K, A u *ᵥ (fun i => (p i).eval t) =
      fun i => (p i).eval (u+t))
    (equations : Set (MvPolynomial ι K))
    (hhom : ∀ f ∈ equations, ∃ e, f.IsHomogeneous e)
    (hvanish : ∀ u : K, ∀ f ∈ equations,
      MvPolynomial.aeval (fun i => (p i).eval u) f = 0) :
    ∃ v : ι → K, v ≠ 0 ∧ (∀ u : K, A u *ᵥ v = v) ∧
      ∀ f ∈ equations, MvPolynomial.aeval v f = 0 := by
  obtain ⟨d,hd,hne⟩ := exists_nonzero_top_coefficient p hp
  refine ⟨fun i => (p i).coeff d, hne, ?_, ?_⟩
  · exact top_coefficient_fixed A p d hd horbit
  · intro f hf
    obtain ⟨e,he⟩ := hhom f hf
    exact homogeneous_vanishes_on_top_coefficient p d hd f e he
      (fun u => hvanish u f hf)

end PaperVerification.PolynomialOrbitFixedPoint
end
end
end TAF_LiteralSource_0661

section TAF_LiteralSource_0662
/- Original module: PaperVerification.BorelLinearAlgebraBatch -/


end TAF_LiteralSource_0662

section TAF_LiteralSource_0663
/- Original module: PaperVerification.FiniteTriangularDecomposition -/


/-!
# A finite direct-sum decomposition detected by triangular tests

This elementary lemma packages the linear algebra in the projective-bundle
formula. The summands may have different types and need not be finite
dimensional. A triangular family of tests proves that their sum is direct.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.FiniteTriangularDecomposition

variable {K ι V : Type*} [Field K] [Fintype ι] [LinearOrder ι]
    [AddCommGroup V] [Module K V]
    {A : ι → Type*} [∀ i, AddCommGroup (A i)] [∀ i, Module K (A i)]

/-- Add the images of a finite family of genuine module homomorphisms. -/
def sumMap (f : ∀ i, A i →ₗ[K] V) : (∀ i, A i) →ₗ[K] V :=
  ∑ i, (f i).comp (LinearMap.proj i)

@[simp] theorem sumMap_apply (f : ∀ i, A i →ₗ[K] V) (x : ∀ i, A i) :
    sumMap f x = ∑ i, f i (x i) := by
  simp [sumMap]

@[simp] theorem sumMap_single (f : ∀ i, A i →ₗ[K] V) (i : ι) (x : A i) :
    sumMap f (Pi.single i x) = f i x := by
  classical
  rw [sumMap_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

/-- A triangular family of coefficient tests makes the sum map injective. -/
theorem sumMap_injective (f : ∀ i, A i →ₗ[K] V) (g : ∀ i, V →ₗ[K] A i)
    (c : ι → K) (hc : ∀ i, c i ≠ 0)
    (hdiag : ∀ i x, g i (f i x) = c i • x)
    (hlower : ∀ i j, j < i → ∀ x, g i (f j x) = 0) :
    Function.Injective (sumMap f) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  by_contra hne
  have hs : (Finset.univ.filter fun i => x i ≠ 0).Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    exact ⟨i, by simpa using hi⟩
  let S := Finset.univ.filter fun i => x i ≠ 0
  let i := S.max' hs
  have hi : x i ≠ 0 := (Finset.mem_filter.mp (Finset.max'_mem S hs)).2
  have he : g i (sumMap f x) = c i • x i := by
    rw [sumMap_apply, map_sum, Finset.sum_eq_single i]
    · exact hdiag i (x i)
    · intro j _ hji
      rcases lt_or_gt_of_ne hji with hlt | hgt
      · exact hlower i j hlt (x j)
      · have hj : x j = 0 := by
          by_contra hj
          have hjS : j ∈ S := by simp [S, hj]
          exact (not_lt_of_ge (Finset.le_max' S j hjS)) hgt
        simp [hj]
    · simp
  rw [hx, map_zero] at he
  exact hi ((smul_eq_zero.mp he.symm).resolve_left (hc i))

/-- Generation of the target by the images makes the sum map surjective. -/
theorem sumMap_surjective (f : ∀ i, A i →ₗ[K] V)
    (hspan : ∀ v : V, v ∈ Submodule.span K (⋃ i, Set.range (f i))) :
    Function.Surjective (sumMap f) := by
  classical
  intro v
  have hle : Submodule.span K (⋃ i, Set.range (f i)) ≤ LinearMap.range (sumMap f) := by
    apply Submodule.span_le.mpr
    intro y hy
    obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.mp hy
    exact ⟨Pi.single i x, sumMap_single f i x⟩
  exact hle (hspan v)

/-- The actual direct-sum equivalence, with no finite-dimensional hypothesis. -/
def equivalence (f : ∀ i, A i →ₗ[K] V) (g : ∀ i, V →ₗ[K] A i)
    (c : ι → K) (hc : ∀ i, c i ≠ 0)
    (hdiag : ∀ i x, g i (f i x) = c i • x)
    (hlower : ∀ i j, j < i → ∀ x, g i (f j x) = 0)
    (hspan : ∀ v : V, v ∈ Submodule.span K (⋃ i, Set.range (f i))) :
    (∀ i, A i) ≃ₗ[K] V :=
  LinearEquiv.ofBijective (sumMap f)
    ⟨sumMap_injective f g c hc hdiag hlower, sumMap_surjective f hspan⟩

@[simp] theorem equivalence_apply (f : ∀ i, A i →ₗ[K] V) (g : ∀ i, V →ₗ[K] A i)
    (c : ι → K) (hc : ∀ i, c i ≠ 0)
    (hdiag : ∀ i x, g i (f i x) = c i • x)
    (hlower : ∀ i j, j < i → ∀ x, g i (f j x) = 0)
    (hspan : ∀ v : V, v ∈ Submodule.span K (⋃ i, Set.range (f i))) (x : ∀ i, A i) :
    equivalence f g c hc hdiag hlower hspan x = ∑ i, f i (x i) :=
  sumMap_apply f x

end PaperVerification.FiniteTriangularDecomposition
end
end
end TAF_LiteralSource_0663

section TAF_LiteralSource_0664
/- Original module: Verified -/


/-! Verified principal results recovered from the exact accepted closures.
Further geometric statements are tracked separately. -/
end TAF_LiteralSource_0664

