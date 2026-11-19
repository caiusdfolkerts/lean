/-
Definitions adapted verbatim from this project's retained Tau Ceti sources.
Copyright (c) 2026 The Tau Ceti contributors. Apache-2.0.
Original source paths and mathematical endpoints are recorded in map.json.
-/
module
public import Mathlib.Combinatorics.Young.YoungDiagram
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.FunLike.Fintype
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
public import Mathlib.Data.Fintype.Fin
public import Mathlib.GroupTheory.GroupAction.DomAct.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Subrepresentation

/-! # Irreducibility of the fixed higher Specht spans -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace YoungDiagram
/-- A cell `c` is **addable** to `μ` if it is not a cell of `μ` while every cell strictly below
it in the product order is. These are exactly the cells outside `μ` whose addition on its own to
`μ` gives a Young diagram (`YoungDiagram.isAddable_iff_isLowerSet`). -/
def IsAddable (μ : YoungDiagram) (c : ℕ × ℕ) : Prop :=
  c ∉ μ ∧ ∀ d < c, d ∈ μ

/-- The defining conjunction of the addable-cell predicate. -/
theorem isAddable_def (μ : YoungDiagram) (c : ℕ × ℕ) :
    IsAddable μ c ↔ c ∉ μ ∧ ∀ d < c, d ∈ μ := by sorry

/-- The original finite test is equivalent to the actual addable-cell predicate. -/
theorem palomarIsAddable_decision_iff (μ : YoungDiagram) (c : ℕ × ℕ) :
    (c ∉ μ ∧ ∀ d ∈ Finset.Iio c, d ∈ μ) ↔ IsAddable μ c := by sorry

/-- The source's finite decision procedure for an addable cell. -/
instance instDecidableIsAddable (μ : YoungDiagram) (c : ℕ × ℕ) : Decidable (IsAddable μ c) :=
  decidable_of_iff (c ∉ μ ∧ ∀ d ∈ Finset.Iio c, d ∈ μ) (palomarIsAddable_decision_iff μ c)

/-- The literal cells used by addCell form a lower set, by the original calculation. -/
theorem palomarAddCell_isLowerSet (μ : YoungDiagram) (c : ℕ × ℕ) :
    IsLowerSet (↑(μ.cells ∪ Finset.range (c.1 + 1) ×ˢ Finset.range (c.2 + 1)) : Set (ℕ × ℕ)) := by
  sorry

/-- The Young diagram obtained from `μ` by adding the cell `c` together with every cell below it in
the product order. It is defined without a hypothesis on `c`, dually to `YoungDiagram.erase`; at
an addable cell exactly the cell `c` is added (`YoungDiagram.IsAddable.cells_addCell_eq_insert`). -/
def addCell (μ : YoungDiagram) (c : ℕ × ℕ) : YoungDiagram where
  cells := μ.cells ∪ Finset.range (c.1 + 1) ×ˢ Finset.range (c.2 + 1)
  isLowerSet := palomarAddCell_isLowerSet μ c

end YoungDiagram

namespace TauCeti
/-- A `μ`-tableau: a bijective filling of the cells of the Young diagram `μ` by the labels
`Fin μ.card`. -/
abbrev YoungTableau (μ : YoungDiagram) : Type := ↥μ.cells ≃ Fin μ.card

namespace YoungTableau
variable {μ : YoungDiagram}
/-- The row of the cell of `μ` carrying the label `k` in the tableau `t`. -/
def rowIndex (t : YoungTableau μ) (k : Fin μ.card) : ℕ := (t.symm k : ℕ × ℕ).1

/-- The column of the cell of `μ` carrying the label `k` in the tableau `t`. -/
def colIndex (t : YoungTableau μ) (k : Fin μ.card) : ℕ := (t.symm k : ℕ × ℕ).2

end YoungTableau

/-- A standard Young tableau of shape `μ` is a bijective labeling of its cells by
`Fin μ.card`, strictly increasing along rows and columns. -/
structure StandardYoungTableau (μ : YoungDiagram) where
  /-- The underlying Young tableau. -/
  toTableau : YoungTableau μ
  /-- Labels increase strictly from left to right. -/
  row_strict' : ∀ {i j₁ j₂ : ℕ} (h : j₁ < j₂) (hcell : (i, j₂) ∈ μ),
    toTableau ⟨(i, j₁), μ.up_left_mem (by rfl) h.le hcell⟩ < toTableau ⟨(i, j₂), hcell⟩
  /-- Labels increase strictly from top to bottom. -/
  col_strict' : ∀ {i₁ i₂ j : ℕ} (h : i₁ < i₂) (hcell : (i₂, j) ∈ μ),
    toTableau ⟨(i₁, j), μ.up_left_mem h.le (by rfl) hcell⟩ < toTableau ⟨(i₂, j), hcell⟩

namespace StandardYoungTableau
/-- Function evaluation is the tableau's underlying bijective labeling. -/
instance instFunLike {μ : YoungDiagram} :
    FunLike (StandardYoungTableau μ) ↥μ.cells (Fin μ.card) where
  coe T := T.toTableau
  coe_injective T U h := by
    cases T with
    | mk e _ _ =>
      cases U with
      | mk e' _ _ =>
        congr
        exact Equiv.ext fun c => congrFun h c

/-- Standard-tableau monotonicity used only to type the literal prefix tableau. -/
theorem row_strict {μ : YoungDiagram} (T : StandardYoungTableau μ)
    {i j₁ j₂ : ℕ} (h : j₁ < j₂) (hcell : (i, j₂) ∈ μ) :
    T ⟨(i, j₁), μ.up_left_mem (by rfl) h.le hcell⟩ < T ⟨(i, j₂), hcell⟩ := by sorry

/-- Standard-tableau monotonicity used only to type the literal prefix tableau. -/
theorem col_strict {μ : YoungDiagram} (T : StandardYoungTableau μ)
    {i₁ i₂ j : ℕ} (h : i₁ < i₂) (hcell : (i₂, j) ∈ μ) :
    T ⟨(i₁, j), μ.up_left_mem h.le (by rfl) hcell⟩ < T ⟨(i₂, j), hcell⟩ := by sorry


end StandardYoungTableau

variable {α ι : Type*}
/-- Original multiplication closure of the unchanged fiber-preserving predicate. -/
theorem palomarFiber_mul (f : α → ι) {σ τ : Equiv.Perm α}
    (hσ : ∀ a, f (σ a) = f a) (hτ : ∀ a, f (τ a) = f a) :
    ∀ a, f ((σ * τ) a) = f a := by sorry
/-- Original identity closure of the unchanged fiber-preserving predicate. -/
theorem palomarFiber_one (f : α → ι) : ∀ a, f ((1 : Equiv.Perm α) a) = f a := by sorry
/-- Original inverse closure of the unchanged fiber-preserving predicate. -/
theorem palomarFiber_inv (f : α → ι) {σ : Equiv.Perm α}
    (hσ : ∀ a, f (σ a) = f a) : ∀ a, f (σ⁻¹ a) = f a := by
  sorry

/-- The subgroup of permutations of `α` that preserve every fiber of `f : α → ι`, that is, those
moving each point within its own fiber. -/
def fiberSubgroup (f : α → ι) : Subgroup (Equiv.Perm α) where
  carrier := {σ | ∀ a, f (σ a) = f a}
  mul_mem' := palomarFiber_mul f
  one_mem' := palomarFiber_one f
  inv_mem' := palomarFiber_inv f

namespace YoungTableau
variable {μ : YoungDiagram}
/-- The **row group** of a `μ`-tableau: the permutations of the labels that keep every label in
its own row of `t`. -/
abbrev rowSubgroup (t : YoungTableau μ) : Subgroup (Equiv.Perm (Fin μ.card)) :=
  fiberSubgroup (rowIndex t)

/-- The **column group** of a `μ`-tableau: the permutations of the labels that keep every label in
its own column of `t`. -/
abbrev colSubgroup (t : YoungTableau μ) : Subgroup (Equiv.Perm (Fin μ.card)) :=
  fiberSubgroup (colIndex t)

end YoungTableau
end TauCeti

namespace TauCeti
open Equiv

theorem youngSortOrder_isTrans : IsTrans ℕ (fun a b : ℕ => a ≥ b) := by
  infer_instance

abbrev youngSortedParts {n : ℕ} (p : n.Partition) : List ℕ :=
  letI : IsTrans ℕ (fun a b : ℕ => a ≥ b) := youngSortOrder_isTrans
  p.parts.sort (· ≥ ·)

def shapePartition (μ : YoungDiagram) : μ.card.Partition :=
  μ.toPartition rfl

theorem shapePartition_parts_sort (μ : YoungDiagram) :
    youngSortedParts (shapePartition μ) = μ.rowLens := by sorry

noncomputable def youngBlocksEquiv {n : ℕ} (μ : n.Partition) :
    (Σ i : Fin (youngSortedParts μ).length,
      Fin ((youngSortedParts μ).get i)) ≃ Fin n :=
  finSigmaFinEquiv.trans <| finCongr <| by
    simp_rw [List.get_eq_getElem]
    rw [Fin.sum_univ_getElem, ← Multiset.sum_coe, Multiset.sort_eq, μ.parts_sum]

noncomputable def youngBlock {n : ℕ} (μ : n.Partition) (j : Fin n) :
    Fin (youngSortedParts μ).length :=
  ((youngBlocksEquiv μ).symm j).1

noncomputable def youngSubgroup {n : ℕ} (μ : n.Partition) :
    Subgroup (Equiv.Perm (Fin n)) :=
  (MulAction.stabilizer (Equiv.Perm (Fin n))ᵈᵐᵃ (youngBlock μ)).unop

namespace YoungTableau

abbrev rowBlocks (l : List ℕ) : Type :=
  Σ i : Fin l.length, Fin (l.get i)

noncomputable def rowCellsEquiv (μ : YoungDiagram) :
    rowBlocks μ.rowLens ≃ ↥μ.cells where
  toFun x := ⟨(x.1, x.2), by
    rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen, ← YoungDiagram.get_rowLens]
    exact x.2.2⟩
  invFun c :=
    ⟨⟨c.1.1, by
      rw [YoungDiagram.length_rowLens]
      exact (_root_.YoungDiagram.mem_iff_lt_colLen.mp c.2).trans_le
        (μ.colLen_anti 0 c.1.2 c.1.2.zero_le)⟩,
      ⟨c.1.2, by
        have hj := _root_.YoungDiagram.mem_iff_lt_rowLen.mp c.2
        rw [← YoungDiagram.get_rowLens] at hj
        exact hj⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def sortedBlocksEquivRows (μ : YoungDiagram) :
    rowBlocks (youngSortedParts (shapePartition μ)) ≃ rowBlocks μ.rowLens :=
  Equiv.cast (congrArg rowBlocks (shapePartition_parts_sort μ))

noncomputable def rowYoungConjugator {μ : YoungDiagram} (t : YoungTableau μ) :
    Equiv.Perm (Fin μ.card) :=
  (youngBlocksEquiv (shapePartition μ)).symm |>.trans <|
    (sortedBlocksEquivRows μ).trans ((rowCellsEquiv μ).trans t)

variable {μ : YoungDiagram}

noncomputable def tabloid (t : YoungTableau μ) :
    Equiv.Perm (Fin μ.card) ⧸ youngSubgroup (shapePartition μ) :=
  QuotientGroup.mk (rowYoungConjugator t)

end YoungTableau
end TauCeti

universe palomarRepU

namespace HigherSpecht
open TauCeti TauCeti.YoungTableau Finset MvPolynomial Module

/-- Count the strict rises of a row-index sequence before position `j`. -/
def ascentCount (r : ℕ → ℕ) (j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range j, if r i < r (i + 1) then 1 else 0

/-- Extend the label-to-row function by zero outside the finite label range.
Only indices strictly below `μ.card` enter cocharge labels. -/
abbrev tableauRows {μ : YoungDiagram} (S : StandardYoungTableau μ) (i : ℕ) : ℕ :=
  if h : i < μ.card then rowIndex S.toTableau ⟨i, h⟩ else 0

/-- The cocharge label of a printed entry (with the printed entry shifted by one). -/
abbrev cochargeLabel {μ : YoungDiagram} (S : StandardYoungTableau μ)
    (i : Fin μ.card) : ℕ := ascentCount (tableauRows S) i.val

/-- The cocharge filling on the cells, before assigning variable labels through T. -/
abbrev cochargeFilling {μ : YoungDiagram} (S : StandardYoungTableau μ)
    (c : ↥μ.cells) : ℕ := cochargeLabel S (S c)

/-- Literal source definition of cochargeDegree. -/
def cochargeDegree {μ : YoungDiagram} (S : StandardYoungTableau μ) : ℕ :=
  ∑ i : Fin μ.card, cochargeLabel S i

/-- Literal source definition of descentNumber. -/
abbrev descentNumber {μ : YoungDiagram} (S : StandardYoungTableau μ) : ℕ :=
  ascentCount (tableauRows S) (μ.card - 1)

/-- Top-to-bottom, left-to-right row reading in the paper's French convention.
The row coordinate itself is still the standard zero-based Young-diagram
coordinate, so larger row coordinates are read first. -/
def rowReadingCells (μ : YoungDiagram) : List ↥μ.cells :=
  μ.cells.attach.toList.mergeSort fun c d =>
    decide (d.val.1 < c.val.1 ∨ (c.val.1 = d.val.1 ∧ c.val.2 ≤ d.val.2))

/-- Literal source definition of cochargeWord. -/
abbrev cochargeWord {μ : YoungDiagram} (S : StandardYoungTableau μ) : List ℕ :=
  (rowReadingCells μ).map (cochargeFilling S)

/-- Literal source definition of CatState. -/
structure CatState where
  word : List ℕ
  shape : YoungDiagram

/-- Literal source definition of catStep. -/
def catStep (s : CatState) : CatState :=
  match s.word.reverse with
  | [] => s
  | a :: rest =>
    if YoungDiagram.IsAddable s.shape (a, s.shape.rowLen a) then
      ⟨rest.reverse, s.shape.addCell (a, s.shape.rowLen a)⟩
    else
      ⟨(a + 1) :: rest.reverse, s.shape⟩

/-- Literal source definition of catRun. -/
def catRun (steps : ℕ) (s : CatState) : CatState := catStep^[steps] s

/-- A genuine terminating output of cyclic insertion. -/
def CatWordOutput (word : List ℕ) (μ : YoungDiagram) : Prop :=
  ∃ N, catRun N ⟨word, ⊥⟩ = ⟨[], μ⟩

/-- Literal source definition of CatTableauOutput. -/
def CatTableauOutput {μ : YoungDiagram} (S : StandardYoungTableau μ)
    (ν : YoungDiagram) : Prop := CatWordOutput (cochargeWord S) ν

/-- Dominance of row-prefix sums, allowing the two diagrams to have different
sizes as in the manuscript's simultaneous-ideal statements. -/
def Dominates (ν μ : YoungDiagram) : Prop :=
  ∀ r : ℕ, (∑ i ∈ Finset.range r, μ.rowLen i) ≤ ∑ i ∈ Finset.range r, ν.rowLen i

/-- The eligibility relation stated directly in terms of the actual terminating
insertion algorithm.  Its comparison with the recursive catabolism definition
is kept separate from all basis assertions. -/
def CatDominates {μ : YoungDiagram} (S : StandardYoungTableau μ)
    (lam : YoungDiagram) : Prop :=
  ∃ ν, CatTableauOutput S ν ∧ Dominates ν lam

/-- Literal source definition of PolynomialRing. -/
abbrev PolynomialRing (n : ℕ) (R : Type*) [CommRing R] := MvPolynomial (Fin n) R

/-- The natural coefficient action commutes with polynomial multiplication. -/
theorem polynomialRing_scalarTower (R : Type*) [CommRing R] (n : ℕ) :
    IsScalarTower R (PolynomialRing n R) (PolynomialRing n R) :=
  IsScalarTower.right

attribute [instance 20000] polynomialRing_scalarTower

section PolynomialDefinitions
attribute [local instance] Classical.propDecidable
variable {R : Type*} [CommRing R]

/-- The elementary symmetric polynomial in precisely the variables in Y. -/
def elementaryOn {n : ℕ} (Y : Finset (Fin n)) (d : ℕ) : PolynomialRing n R :=
  ∑ A ∈ Y.powersetCard d, ∏ i ∈ A, X i

/-- Conjugate tail, using zero-based column indices.  The interval
`[n-m,n)` is the printed interval `n-m+1,…,n`. -/
def conjugateTail (n : ℕ) (μ : YoungDiagram) (m : ℕ) : ℕ :=
  ∑ j ∈ Finset.Ico (n - m) n, μ.colLen j

/-- A generator of the untruncated Griffin ideal.  The comparison is made in
the integers so that no natural subtraction can change its mathematical content. -/
def IsElementaryGenerator (n : ℕ) (μ : YoungDiagram)
    (p : PolynomialRing n R) : Prop :=
  ∃ (Y : Finset (Fin n)) (d : ℕ), 0 < d ∧ d ≤ Y.card ∧
    (Y.card : ℤ) - (conjugateTail n μ Y.card : ℤ) < (d : ℤ) ∧
    p = elementaryOn Y d

/-- Literal source definition of untruncatedIdeal. -/
def untruncatedIdeal (R : Type*) [CommRing R] (n : ℕ) (μ : YoungDiagram) :
    Ideal (PolynomialRing n R) := Ideal.span {p | IsElementaryGenerator n μ p}

/-- Literal source definition of powerIdeal. -/
def powerIdeal (R : Type*) [CommRing R] (n s : ℕ) :
    Ideal (PolynomialRing n R) := Ideal.span (Set.range fun i : Fin n => (X i) ^ s)

/-- Literal source definition of griffinIdeal. -/
def griffinIdeal (R : Type*) [CommRing R] (n : ℕ) (μ : YoungDiagram) (s : ℕ) :
    Ideal (PolynomialRing n R) := untruncatedIdeal R n μ ⊔ powerIdeal R n s

theorem griffinIdeal_isTwoSided (R : Type*) [CommRing R] (n : ℕ)
    (lam : YoungDiagram) (s : ℕ) : (griffinIdeal R n lam s).IsTwoSided :=
  Ideal.instIsTwoSided_1 (griffinIdeal R n lam s)

attribute [instance 1200] griffinIdeal_isTwoSided

/-- Literal source definition of springerIdeal. -/
def springerIdeal (R : Type*) [CommRing R] (μ : YoungDiagram) :
    Ideal (PolynomialRing μ.card R) := untruncatedIdeal R μ.card μ

theorem springerIdeal_isTwoSided (R : Type*) [CommRing R]
    (lam : YoungDiagram) : (springerIdeal R lam).IsTwoSided :=
  Ideal.instIsTwoSided_1 (springerIdeal R lam)

attribute [instance 1200] springerIdeal_isTwoSided

/-- Literal source definition of UntruncatedRing. -/
abbrev UntruncatedRing (R : Type*) [CommRing R] (n : ℕ) (μ : YoungDiagram) :=
  PolynomialRing n R ⧸ untruncatedIdeal R n μ

/-- Literal source definition of GriffinRing. -/
abbrev GriffinRing (R : Type*) [CommRing R] (n : ℕ) (μ : YoungDiagram) (s : ℕ) :=
  PolynomialRing n R ⧸ griffinIdeal R n μ s

/-- Literal source definition of SpringerRing. -/
abbrev SpringerRing (R : Type*) [CommRing R] (μ : YoungDiagram) :=
  PolynomialRing μ.card R ⧸ springerIdeal R μ

/-- The literal row symmetrizer on polynomials. -/
def rowSymmetrize {n : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (p : PolynomialRing n R) : PolynomialRing n R :=
  ∑ ρ : G, MvPolynomial.rename (ρ : Equiv.Perm (Fin n)) p

/-- The literal column antisymmetrizer; its sign is transported from the integers. -/
def columnAlternate {n : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (p : PolynomialRing n R) : PolynomialRing n R :=
  ∑ σ : G, (((Equiv.Perm.sign (σ : Equiv.Perm (Fin n)) : ℤ) : R)) •
    MvPolynomial.rename (σ : Equiv.Perm (Fin n)) p

/-- Literal source definition of youngApply. -/
def youngApply {μ : YoungDiagram} (T : YoungTableau μ)
    (p : PolynomialRing μ.card R) : PolynomialRing μ.card R :=
  columnAlternate (colSubgroup T) (rowSymmetrize (rowSubgroup T) p)

/-- Literal source definition of transportedCocharge. -/
abbrev transportedCocharge {μ : YoungDiagram} (S : StandardYoungTableau μ)
    (T : YoungTableau μ) : Fin μ.card →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => cochargeFilling S (T.symm i)

/-- The manuscript's unnormalized polynomial, with column alternation applied
after row symmetrization. -/
def higherSpechtPolynomial {μ : YoungDiagram} (S T : StandardYoungTableau μ) :
    PolynomialRing μ.card R :=
  youngApply T.toTableau (MvPolynomial.monomial (transportedCocharge S T.toTableau) 1)

/-- The symmetric factor is indexed by its partition itself, padded by zeros.
Its argument is a finite weakly decreasing sequence in the final basis theorem. -/
def elementaryMultiplier (n m : ℕ) (eta : ℕ → ℕ) : PolynomialRing n R :=
  ∏ j ∈ Finset.range m,
    MvPolynomial.esymm (Fin n) R (j + 1) ^ (eta j - eta (j + 1))

end PolynomialDefinitions

/-- Entrywise monotonicity used to certify the explicit prefix cell set is a diagram. -/
theorem standardTableau_monotoneCells {μ : YoungDiagram} (S : StandardYoungTableau μ)
    {a b : ↥μ.cells} (hab : a.val ≤ b.val) : S a ≤ S b := by sorry

/-- The Young diagram of the entries less than k in the given standard tableau. -/
def prefixShape {μ : YoungDiagram} (S : StandardYoungTableau μ) (k : ℕ) : YoungDiagram where
  cells := μ.cells.filter fun c => if hc : c ∈ μ.cells then (S ⟨c, hc⟩).val < k else False
  isLowerSet := by
    intro b a hab hb
    obtain ⟨hbμ, hbk⟩ := Finset.mem_filter.mp hb
    have haμ : a ∈ μ.cells := μ.isLowerSet hab hbμ
    refine Finset.mem_filter.mpr ⟨haμ, ?_⟩
    have hbk' : (S ⟨b, hbμ⟩).val < k := by
      simpa only [dif_pos hbμ] using hbk
    change (if hc : a ∈ μ.cells then (S ⟨a, hc⟩).val < k else False)
    rw [dif_pos haμ]
    exact lt_of_le_of_lt
      (standardTableau_monotoneCells S (a := ⟨a, haμ⟩) (b := ⟨b, hbμ⟩) hab) hbk'

/-- Exact membership criterion for the prefix Young diagram. -/
theorem mem_prefixShape {μ : YoungDiagram} (S : StandardYoungTableau μ) (k : ℕ)
    (c : ℕ × ℕ) :
    c ∈ prefixShape S k ↔ ∃ hc : c ∈ μ.cells, (S ⟨c, hc⟩).val < k := by sorry
/-- Prefix diagrams retain their original cells. -/
theorem prefixShape_le {μ : YoungDiagram} (S : StandardYoungTableau μ) (k : ℕ) :
    prefixShape S k ≤ μ := by sorry

/-- Literal source definition of prefixCellEquiv. -/
def prefixCellEquiv {μ : YoungDiagram} (S : StandardYoungTableau μ) (k : ℕ) :
    ↥(prefixShape S k).cells ≃ {c : ↥μ.cells // (S c).val < k} where
  toFun c := ⟨⟨c.val, prefixShape_le S k c.property⟩,
    ((mem_prefixShape S k c.val).mp c.property).choose_spec⟩
  invFun c := ⟨c.val.val, (mem_prefixShape S k c.val.val).mpr ⟨c.val.property, c.property⟩⟩
  left_inv c := rfl
  right_inv c := rfl

/-- Literal source definition of initialLabelsEquiv. -/
def initialLabelsEquiv {n k : ℕ} (hk : k ≤ n) :
    {i : Fin n // i.val < k} ≃ Fin k where
  toFun i := ⟨i.val.val, i.property⟩
  invFun i := ⟨⟨i.val, lt_of_lt_of_le i.isLt hk⟩, i.isLt⟩
  left_inv i := rfl
  right_inv i := rfl

/-- Literal source definition of prefixLabelEquiv. -/
def prefixLabelEquiv {μ : YoungDiagram} (S : StandardYoungTableau μ)
    (k : ℕ) (hk : k ≤ μ.card) : ↥(prefixShape S k).cells ≃ Fin k :=
  (prefixCellEquiv S k).trans
    ((S.toTableau.subtypeEquiv (fun c => Iff.rfl)).trans (initialLabelsEquiv hk))

/-- Evaluation of the literal prefix-label equivalence on cell labels. -/
@[simp] theorem prefixLabelEquiv_apply_val {μ : YoungDiagram}
    (S : StandardYoungTableau μ) (k : ℕ) (hk : k ≤ μ.card)
    (c : ↥(prefixShape S k).cells) :
    (prefixLabelEquiv S k hk c).val = (S ⟨c.val, prefixShape_le S k c.property⟩).val := by sorry

/-- Every allowed prefix has exactly the prescribed number of cells. -/
theorem prefixShape_card {μ : YoungDiagram} (S : StandardYoungTableau μ)
    (k : ℕ) (hk : k ≤ μ.card) : (prefixShape S k).card = k := by sorry

/-- The literal standard prefix tableau with its original zero-based labels. -/
def prefixTableau {μ : YoungDiagram} (S : StandardYoungTableau μ)
    (k : ℕ) (hk : k ≤ μ.card) : StandardYoungTableau (prefixShape S k) where
  toTableau := (prefixLabelEquiv S k hk).trans (finCongr (prefixShape_card S k hk).symm)
  row_strict' h hcell := by
    change (prefixLabelEquiv S k hk _).val < (prefixLabelEquiv S k hk _).val
    simp only [prefixLabelEquiv_apply_val]
    exact S.row_strict h (prefixShape_le S k hcell)
  col_strict' h hcell := by
    change (prefixLabelEquiv S k hk _).val < (prefixLabelEquiv S k hk _).val
    simp only [prefixLabelEquiv_apply_val]
    exact S.col_strict h (prefixShape_le S k hcell)

/-- Literal source definition of StandardPair. -/
structure StandardPair (n : ℕ) where
  shape : YoungDiagram
  card_eq : shape.card = n
  left : StandardYoungTableau shape
  right : StandardYoungTableau shape

/-- Literal source definition of pairPolynomial. -/
def pairPolynomial {R : Type*} [CommRing R] {n : ℕ} (P : StandardPair n) :
    PolynomialRing n R :=
  MvPolynomial.rename (finCongr P.card_eq)
    (higherSpechtPolynomial P.left P.right)

/-- Literal source definition of prefixEligible. -/
def prefixEligible {n : ℕ} (lam : YoungDiagram) (hk : lam.card ≤ n)
    (P : StandardPair n) : Prop :=
  CatDominates (prefixTableau P.left lam.card (by simpa only [P.card_eq] using hk)) lam

/-- Literal source definition of SpringerIndex. -/
abbrev SpringerIndex (lam : YoungDiagram) :=
  {P : StandardPair lam.card // CatDominates P.left lam}

/-- Literal source definition of springerFamily. -/
def springerFamily (R : Type*) [CommRing R] (lam : YoungDiagram) :
    SpringerIndex lam → SpringerRing R lam :=
  fun i => Ideal.Quotient.mk (springerIdeal R lam) (pairPolynomial i.val)

/-- Literal source definition of GriffinIndex. -/
structure GriffinIndex (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ) where
  pair : StandardPair n
  multiplier : YoungDiagram
  eligible : prefixEligible lam hk pair
  descents_lt : descentNumber pair.left < s
  multiplier_length : multiplier.colLen 0 ≤ n - lam.card
  multiplier_width : multiplier.rowLen 0 ≤ s - descentNumber pair.left - 1

/-- Literal source definition of griffinPolynomial. -/
def griffinPolynomial {R : Type*} [CommRing R] {n : ℕ} {lam : YoungDiagram}
    {hk : lam.card ≤ n} {s : ℕ} (i : GriffinIndex n lam hk s) : PolynomialRing n R :=
  pairPolynomial i.pair * elementaryMultiplier n (n - lam.card) i.multiplier.rowLen

/-- Literal source definition of griffinFamily. -/
def griffinFamily (R : Type*) [CommRing R] (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) :
    GriffinIndex n lam hk s → GriffinRing R n lam s :=
  fun i => Ideal.Quotient.mk (griffinIdeal R n lam s) (griffinPolynomial i)

section PermutationActions
variable {R : Type*} [CommRing R] {n : ℕ}

def PermutationStable (I : Ideal (PolynomialRing n R)) : Prop :=
  ∀ (e : Equiv.Perm (Fin n)) (p : PolynomialRing n R),
    p ∈ I → MvPolynomial.rename e p ∈ I

theorem permutationStable_untruncatedIdeal (μ : YoungDiagram) :
    PermutationStable (untruncatedIdeal R n μ) := by sorry

theorem permutationStable_griffinIdeal (μ : YoungDiagram) (s : ℕ) :
    PermutationStable (griffinIdeal R n μ s) := by sorry

theorem polynomialRename_one (R : Type palomarRepU) [CommRing R] (n : ℕ) :
    (MvPolynomial.rename (1 : Equiv.Perm (Fin n))).toLinearMap =
      (1 : Module.End R (PolynomialRing n R)) := by
  apply LinearMap.ext
  intro p
  exact MvPolynomial.rename_id_apply p

theorem polynomialRename_mul (R : Type palomarRepU) [CommRing R] (n : ℕ)
    (e f : Equiv.Perm (Fin n)) :
    (MvPolynomial.rename (e * f)).toLinearMap =
      ((MvPolynomial.rename e).toLinearMap : Module.End R (PolynomialRing n R)) *
        (MvPolynomial.rename f).toLinearMap := by
  apply LinearMap.ext
  intro p
  exact (MvPolynomial.rename_rename f e p).symm

def polynomialRepresentation (R : Type palomarRepU) [CommRing R] (n : ℕ) :
    Representation R (Equiv.Perm (Fin n)) (PolynomialRing n R) where
  toFun e := (MvPolynomial.rename e).toLinearMap
  map_one' := polynomialRename_one R n
  map_mul' e f := polynomialRename_mul R n e f

def idealSubrepresentation (I : Ideal (PolynomialRing n R)) (hI : PermutationStable I) :
    Subrepresentation (polynomialRepresentation R n) where
  toSubmodule := I.restrictScalars R
  apply_mem_toSubmodule e p hp := hI e p hp

def quotientRepresentation (I : Ideal (PolynomialRing n R)) (hI : PermutationStable I) :
    Representation R (Equiv.Perm (Fin n)) (PolynomialRing n R ⧸ I) :=
  (idealSubrepresentation I hI).quotient

theorem springerIdeal_permutationStable (R : Type palomarRepU) [CommRing R]
    (lam : YoungDiagram) : PermutationStable (springerIdeal R lam) :=
  permutationStable_untruncatedIdeal lam

def springerRepresentation (R : Type palomarRepU) [CommRing R] (μ : YoungDiagram) :
    Representation R (Equiv.Perm (Fin μ.card)) (SpringerRing R μ) :=
  quotientRepresentation (springerIdeal R μ) (springerIdeal_permutationStable R μ)

def griffinRepresentation (R : Type palomarRepU) [CommRing R] (n : ℕ) (μ : YoungDiagram) (s : ℕ) :
    Representation R (Equiv.Perm (Fin n)) (GriffinRing R n μ s) :=
  quotientRepresentation (griffinIdeal R n μ s) (permutationStable_griffinIdeal μ s)

end PermutationActions

structure FixedGriffinIndex (μ lam : YoungDiagram) (hk : lam.card ≤ μ.card) (s : ℕ) where
  left : StandardYoungTableau μ
  multiplier : YoungDiagram
  eligible : CatDominates (prefixTableau left lam.card hk) lam
  descents_lt : descentNumber left < s
  multiplier_length : multiplier.colLen 0 ≤ μ.card - lam.card
  multiplier_width : multiplier.rowLen 0 ≤ s - descentNumber left - 1

abbrev PartitionGriffinCopies (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (part : n.Partition) :=
  FixedGriffinIndex (YoungDiagram.ofPartition part) lam
    (by simpa only [YoungDiagram.card_ofPartition] using hk) s

/-- Cardinal identification used to transport a standard tableau's variable labels. -/
theorem fixedSpan_shapeCard {n : ℕ} (part : n.Partition) :
    (YoungDiagram.ofPartition part).card = n :=
  YoungDiagram.card_ofPartition part

def springerFixedCopySpanOver (K : Type*) [Field K]
    (lam : YoungDiagram) (part : lam.card.Partition)
    (S : StandardYoungTableau (YoungDiagram.ofPartition part)) :
    Submodule K (SpringerRing K lam) :=
  Submodule.span K (Set.range (fun T : StandardYoungTableau (YoungDiagram.ofPartition part) =>
    Ideal.Quotient.mk (springerIdeal K lam)
      (rename (finCongr (fixedSpan_shapeCard part))
        (higherSpechtPolynomial S T))))

def griffinFixedCopySpanOver (K : Type*) [Field K]
    {n : ℕ} (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ)
    (part : n.Partition) (i : PartitionGriffinCopies n lam hk s part) :
    Submodule K (GriffinRing K n lam s) :=
  Submodule.span K (Set.range (fun T : StandardYoungTableau (YoungDiagram.ofPartition part) =>
    Ideal.Quotient.mk (griffinIdeal K n lam s)
      (rename (finCongr (fixedSpan_shapeCard part))
        (higherSpechtPolynomial i.left T) *
        elementaryMultiplier n (n - lam.card) i.multiplier.rowLen)))

section SpechtModel
open scoped Classical

abbrev TableauTabloid (mu : YoungDiagram) :=
  Equiv.Perm (Fin mu.card) ⧸ youngSubgroup (shapePartition mu)

abbrev TabloidSpaceOver (R : Type*) (mu : YoungDiagram) := TableauTabloid mu → R

def tabloidRepresentationOver (R : Type*) [CommRing R] (mu : YoungDiagram) :
    Representation R (Equiv.Perm (Fin mu.card)) (TabloidSpaceOver R mu) where
  toFun g :=
    { toFun f := fun q => f (g⁻¹ • q)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_one' := by ext f q; simp
  map_mul' g h := by ext f q; simp [mul_smul]

def polytabloidOver (R : Type*) [CommRing R] {mu : YoungDiagram}
    (T : YoungTableau mu) : TabloidSpaceOver R mu :=
  ∑ g : colSubgroup T, ((Equiv.Perm.sign g.val : ℤ) : R) •
    Pi.single (g.val • tabloid T) 1

theorem polytabloidSpan_stable (R : Type*) [CommRing R] (mu : YoungDiagram)
    (g : Equiv.Perm (Fin mu.card)) (v : TabloidSpaceOver R mu)
    (hv : v ∈ Submodule.span R (Set.range (polytabloidOver R (mu := mu)))) :
    tabloidRepresentationOver R mu g v ∈
      Submodule.span R (Set.range (polytabloidOver R (mu := mu))) := by sorry

def spechtSubrepresentationOver (R : Type*) [CommRing R] (mu : YoungDiagram) :
    Subrepresentation (tabloidRepresentationOver R mu) where
  toSubmodule := Submodule.span R (Set.range (polytabloidOver R (mu := mu)))
  apply_mem_toSubmodule := polytabloidSpan_stable R mu

abbrev partitionSpechtRepresentationOver (R : Type*) [CommRing R] {n : ℕ}
    (part : n.Partition) :=
  (spechtSubrepresentationOver R (YoungDiagram.ofPartition part)).toRepresentation.comp
    (finCongr (YoungDiagram.card_ofPartition part).symm).permCongrHom.toMonoidHom

end SpechtModel

theorem springer_fixedSpan_specht
    {K : Type*} [Field K] (lam : YoungDiagram) (part : lam.card.Partition)
    (S : StandardYoungTableau (YoungDiagram.ofPartition part)) (hS : CatDominates S lam)
    (hchar : ringChar K = 0 ∨ lam.card < ringChar K) :
    ∃ W : Subrepresentation (springerRepresentation K lam),
      W.toSubmodule = springerFixedCopySpanOver K lam part S ∧
      W.toRepresentation.IsIrreducible ∧
      Nonempty (Representation.Equiv (partitionSpechtRepresentationOver K part)
        W.toRepresentation) := by sorry

theorem griffin_fixedSpan_specht
    {K : Type*} [Field K] {n : ℕ} (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) (part : n.Partition)
    (i : PartitionGriffinCopies n lam hk s part)
    (hchar : ringChar K = 0 ∨ n < ringChar K) (hheight : lam.colLen 0 ≤ s) :
    ∃ W : Subrepresentation (griffinRepresentation K n lam s),
      W.toSubmodule = griffinFixedCopySpanOver K lam hk s part i ∧
      W.toRepresentation.IsIrreducible ∧
      Nonempty (Representation.Equiv (partitionSpechtRepresentationOver K part)
        W.toRepresentation) := by sorry

end HigherSpecht
