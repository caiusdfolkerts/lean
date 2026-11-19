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
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Literal polynomial witnesses for simultaneous harmonic decompositions -/

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
open MvPolynomial
variable (σ : Type*) [Fintype σ] [DecidableEq σ] (R : Type*) [CommRing R]

noncomputable def alternant (α : σ → ℕ) : MvPolynomial σ R :=
  (Matrix.of fun i j => (X i : MvPolynomial σ R) ^ α j).det

end TauCeti

namespace YoungDiagram

@[simp]
theorem rowLen_bot (i : ℕ) : (⊥ : YoungDiagram).rowLen i = 0 := by
  simp [_root_.YoungDiagram.rowLen]

/-- The empty Young diagram has no cells, so every column of it is empty. -/
@[simp]
theorem colLen_bot (j : ℕ) : (⊥ : YoungDiagram).colLen j = 0 :=
  Nat.eq_zero_of_not_pos fun h =>
    _root_.YoungDiagram.notMem_bot _ (_root_.YoungDiagram.mem_iff_lt_colLen.mpr h)

end YoungDiagram

universe palomarYoungU

namespace TauCeti.YoungTableau

variable {μ : YoungDiagram}

local instance (t : YoungTableau μ) : DecidablePred (· ∈ rowSubgroup t) :=
  Classical.decPred _

/-- Classical decidability of membership in the column group, used to form its finite sum. -/
local instance decidablePredMemColSubgroup (t : YoungTableau μ) :
    DecidablePred (· ∈ colSubgroup t) :=
  Classical.decPred _

/-- The **row symmetrizer** `a_t`, the sum of the permutations preserving the rows of `t`. -/
noncomputable def rowSymmetrizer (t : YoungTableau μ) :
    MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card)) :=
  ∑ p : rowSubgroup t, MonoidAlgebra.of ℚ (Equiv.Perm (Fin μ.card)) p

/-- The **column antisymmetrizer** `b_t`, the signed sum of the permutations preserving the
columns of `t`. -/
noncomputable def columnAntisymmetrizer (t : YoungTableau μ) :
    MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card)) :=
  ∑ q : colSubgroup t,
    ((Equiv.Perm.sign (q : Equiv.Perm (Fin μ.card)) : ℤ) : ℚ) •
      MonoidAlgebra.of ℚ (Equiv.Perm (Fin μ.card)) q

/-- The **Young symmetrizer** of `t`, with the convention `c_t = a_t b_t`. On a left module it
acts by column-antisymmetrization followed by row-symmetrization. -/
noncomputable def youngSymmetrizer (t : YoungTableau μ) :
    MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card)) :=
  rowSymmetrizer t * columnAntisymmetrizer t

noncomputable abbrev youngSymmetrizerOver (k : Type palomarYoungU) [Semiring k] [Algebra ℚ k] (t : YoungTableau μ) :
    MonoidAlgebra k (Equiv.Perm (Fin μ.card)) :=
  MonoidAlgebra.mapAlgHom _ (Algebra.ofId ℚ k) (youngSymmetrizer t)

end TauCeti.YoungTableau

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

/-- Literal source definition of springerIdeal. -/
def springerIdeal (R : Type*) [CommRing R] (μ : YoungDiagram) :
    Ideal (PolynomialRing μ.card R) := untruncatedIdeal R μ.card μ

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

structure UnboundedHarmonicIndex (n : ℕ) where
  part : n.Partition
  left : StandardYoungTableau (YoungDiagram.ofPartition part)
  multiplier : YoungDiagram
  multiplier_length : multiplier.colLen 0 ≤ n

structure FiniteHarmonicIndex (n s : ℕ) extends UnboundedHarmonicIndex n where
  descents_lt : descentNumber left < s
  multiplier_width : multiplier.rowLen 0 ≤ s - descentNumber left - 1

def UnboundedHarmonicIndex.degree {n : ℕ} (i : UnboundedHarmonicIndex n) : ℕ :=
  cochargeDegree i.left + i.multiplier.card

def UnboundedHarmonicIndex.eligible {n : ℕ} (i : UnboundedHarmonicIndex n)
    (lam : YoungDiagram) (hk : lam.card ≤ n) : Prop :=
  i.multiplier.colLen 0 ≤ n - lam.card ∧
    CatDominates (prefixTableau i.left lam.card
      (by simpa only [YoungDiagram.card_ofPartition] using hk)) lam

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

/-- The Specht representation of this shape, presented as the left ideal
generated by the row symmetrizer times the column antisymmetrizer. -/
abbrev paperYoungIdealRepresentation {n : ℕ} (part : n.Partition)
    (T : YoungTableau (YoungDiagram.ofPartition part)) :=
  Representation.ofModule' (k := ℂ) (G := Equiv.Perm (Fin n))
    (Ideal.span {(MonoidAlgebra.domCongr ℂ ℂ
        (finCongr (YoungDiagram.card_ofPartition part)).permCongrHom
        (TauCeti.YoungTableau.youngSymmetrizerOver ℂ T))} :
      Ideal (MonoidAlgebra ℂ (Equiv.Perm (Fin n))))

/-- The ordinary apolar pairing written in monomial coefficients. -/
def apolarCoefficientPairing {n : ℕ} (f p : PolynomialRing n ℂ) : ℂ :=
  ∑ a ∈ f.support, f.coeff a * (p.coeff a * ((∏ j, (a j).factorial : ℕ) : ℂ))

open Function

def CatAdmissible (s : CatState) : Prop :=
  ∀ a ∈ s.word, 0 < a → 0 < s.shape.rowLen (a - 1) ∨
    [a, a - 1].Sublist s.word

theorem catRun_eventually_empty {s : CatState} (hs : CatAdmissible s) :
    ∃ N : ℕ, (catRun N s).word = [] := by sorry

structure CyclingToken (n : ℕ) where
  position : Fin n
  round : ℕ
  deriving DecidableEq

namespace CyclingToken
variable {n : ℕ}
def bump (t : CyclingToken n) : CyclingToken n := ⟨t.position, t.round + 1⟩

end CyclingToken

def initialCyclingQueue (n : ℕ) : List (CyclingToken n) := List.ofFn fun i => ⟨i, 0⟩

inductive CyclingExecution {n : ℕ} (initial : List (CyclingToken n)) :
    List (CyclingToken n) → List (CyclingToken n) → Prop
  | start : CyclingExecution initial [] initial
  | accept {accepted pending} (t : CyclingToken n)
      (h : CyclingExecution initial accepted (t :: pending)) :
      CyclingExecution initial (accepted ++ [t]) pending
  | reject {accepted pending} (t : CyclingToken n)
      (h : CyclingExecution initial accepted (t :: pending)) :
      CyclingExecution initial accepted (pending ++ [t.bump])

section LabeledRun
variable {n : ℕ}

abbrev AcceptedToken (n : ℕ) := CyclingToken n × (ℕ × ℕ)

structure LabeledCatState (n : ℕ) where
  pending : List (CyclingToken n)
  shape : YoungDiagram
  accepted : List (AcceptedToken n)

def tokenValue (a : Fin n → ℕ) (t : CyclingToken n) : ℕ := a t.position + t.round

def labeledInitial (n : ℕ) : LabeledCatState n :=
  ⟨initialCyclingQueue n, ⊥, []⟩

def labeledCatStep (a : Fin n → ℕ) (s : LabeledCatState n) : LabeledCatState n :=
  match s.pending with
  | [] => s
  | t :: q =>
    let c := (tokenValue a t, s.shape.rowLen (tokenValue a t))
    if YoungDiagram.IsAddable s.shape c then
      ⟨q, s.shape.addCell c, s.accepted ++ [(t, c)]⟩
    else
      ⟨q ++ [t.bump], s.shape, s.accepted⟩

def labeledCatRun (a : Fin n → ℕ) (N : ℕ) (s : LabeledCatState n) : LabeledCatState n :=
  (labeledCatStep a)^[N] s

structure LabeledInvariant (a : Fin n → ℕ) (s : LabeledCatState n) : Prop where
  execution : CyclingExecution (initialCyclingQueue n) (s.accepted.map Prod.fst) s.pending
  cells : (s.accepted.map Prod.snd).toFinset = s.shape.cells
  distinctCells : (s.accepted.map Prod.snd).Nodup
  rowValue : ∀ z ∈ s.accepted, z.2.1 = tokenValue a z.1
  columnOrder : s.accepted.Pairwise (fun z w => z.2.2 = w.2.2 → z.2.1 < w.2.1)

theorem labeledInvariant_run (a : Fin n → ℕ) (N : ℕ) :
    LabeledInvariant a (labeledCatRun a N (labeledInitial n)) := by sorry

structure CompleteInsertion (a : Fin n → ℕ) where
  state : LabeledCatState n
  invariant : LabeledInvariant a state
  pending_nil : state.pending = []

namespace CompleteInsertion

variable {a : Fin n → ℕ} (C : CompleteInsertion a)

abbrev Index := Fin C.state.accepted.length

def token (i : C.Index) : CyclingToken n := (C.state.accepted.get i).1

def cell (i : C.Index) : ↥C.state.shape.cells :=
  ⟨(C.state.accepted.get i).2, by
    rw [← C.invariant.cells]
    exact List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨C.state.accepted.get i, List.get_mem _ _, rfl⟩)⟩

theorem position_bijective : Function.Bijective (fun i : C.Index => (C.token i).position) := by sorry

theorem cell_bijective : Function.Bijective C.cell := by sorry

def positionEquiv : C.Index ≃ Fin n := Equiv.ofBijective _ C.position_bijective

def cellEquiv : C.Index ≃ ↥C.state.shape.cells := Equiv.ofBijective _ C.cell_bijective

/-- The actual accepted cell is filled by its original scan position. -/
def filling : ↥C.state.shape.cells ≃ Fin n := C.cellEquiv.symm.trans C.positionEquiv

def rejection (j : Fin n) : ℕ := (C.token (C.positionEquiv.symm j)).round

def row (j : Fin n) : ℕ := (C.filling.symm j).val.1

def column (j : Fin n) : ℕ := (C.filling.symm j).val.2

end CompleteInsertion
end LabeledRun

def columnReadingCells (μ : YoungDiagram) : List ↥μ.cells :=
  μ.cells.attach.toList.mergeSort fun c d =>
    decide (c.val.2 < d.val.2 ∨ (c.val.2 = d.val.2 ∧ d.val.1 ≤ c.val.1))

def columnScanCells (μ : YoungDiagram) : List ↥μ.cells := (columnReadingCells μ).reverse

theorem mem_columnScanCells {μ : YoungDiagram} (c : ↥μ.cells) :
    c ∈ columnScanCells μ := by sorry

theorem length_columnScanCells (μ : YoungDiagram) :
    (columnScanCells μ).length = μ.card := by sorry

theorem nodup_columnScanCells (μ : YoungDiagram) : (columnScanCells μ).Nodup := by sorry

def columnScanEquiv (μ : YoungDiagram) : Fin μ.card ≃ ↥μ.cells :=
  (finCongr (length_columnScanCells μ).symm).trans
    (List.Nodup.getEquivOfForallMemList (columnScanCells μ)
      (nodup_columnScanCells μ) (fun c => mem_columnScanCells c))

def columnScanCocharge {μ : YoungDiagram} (S : StandardYoungTableau μ)
    (i : Fin μ.card) : ℕ := cochargeFilling S (columnScanEquiv μ i)

theorem columnScanCocharge_admissible {μ : YoungDiagram} (S : StandardYoungTableau μ) :
    CatAdmissible ⟨(List.ofFn (columnScanCocharge S)).reverse, ⊥⟩ := by sorry

def columnInsertionSteps {μ : YoungDiagram} (S : StandardYoungTableau μ) : ℕ := by
  classical
  exact Nat.find (catRun_eventually_empty (columnScanCocharge_admissible S))

theorem columnInsertion_pending_nil {μ : YoungDiagram} (S : StandardYoungTableau μ) :
    (labeledCatRun (columnScanCocharge S) (columnInsertionSteps S)
      (labeledInitial μ.card)).pending = [] := by sorry

def columnInsertion {μ : YoungDiagram} (S : StandardYoungTableau μ) :
    CompleteInsertion (columnScanCocharge S) where
  state := labeledCatRun (columnScanCocharge S) (columnInsertionSteps S)
    (labeledInitial μ.card)
  invariant := labeledInvariant_run (columnScanCocharge S) (columnInsertionSteps S)
  pending_nil := columnInsertion_pending_nil S

section PrefixWitness
variable {μ : YoungDiagram}

def scanLabelEquiv (T : YoungTableau μ) : Equiv.Perm (Fin μ.card) :=
  (columnScanEquiv μ).trans T

def insertionFilling (S : StandardYoungTableau μ) (T : YoungTableau μ) :
    ↥(columnInsertion S).state.shape.cells ≃ Fin μ.card :=
  (columnInsertion S).filling.trans (scanLabelEquiv T)

def insertionRow (S : StandardYoungTableau μ) (T : YoungTableau μ) (i : Fin μ.card) : ℕ :=
  (columnInsertion S).row ((scanLabelEquiv T).symm i)

theorem witnessFinFinite (n : ℕ) : Finite (Fin n) := inferInstance
abbrev witnessFinFinsupp (n : ℕ) : (Fin n →₀ ℕ) ≃ (Fin n → ℕ) :=
  @Finsupp.equivFunOnFinite (Fin n) ℕ _ (witnessFinFinite n)

def insertionAlpha (S : StandardYoungTableau μ) (T : YoungTableau μ) : Fin μ.card →₀ ℕ :=
  (witnessFinFinsupp μ.card).symm (insertionRow S T)

def insertionRejections (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (i : Fin μ.card) : ℕ :=
  (columnInsertion S).rejection ((scanLabelEquiv T).symm i)

def insertionRejectionExponent (S : StandardYoungTableau μ) (T : YoungTableau μ) :
    Fin μ.card →₀ ℕ := (witnessFinFinsupp μ.card).symm (insertionRejections S T)
theorem witnessPrefixCellMem (S : StandardYoungTableau μ) (k : ℕ)
    (c : ↥(prefixShape S k).cells) : c.val ∈ μ :=
  prefixShape_le S k c.property
theorem witnessPrefixCellInjective (S : StandardYoungTableau μ) (k : ℕ) :
    Function.Injective (fun c : ↥(prefixShape S k).cells =>
      (⟨c.val, witnessPrefixCellMem S k c⟩ : ↥μ.cells)) :=
  fun _ _ h => Subtype.ext (congrArg (fun z : ↥μ.cells => z.val) h)

def prefixCellsEmbedding (S : StandardYoungTableau μ) (k : ℕ) :
    ↥(prefixShape S k).cells ↪ ↥μ.cells where
  toFun c := ⟨c.val, witnessPrefixCellMem S k c⟩
  inj' := witnessPrefixCellInjective S k

def prefixAmbientEmbedding (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (k : ℕ) (hk : k ≤ μ.card) : Fin (prefixShape S k).card ↪ Fin μ.card :=
  (prefixTableau S k hk).toTableau.symm.toEmbedding.trans
    ((prefixCellsEmbedding S k).trans T.toEmbedding)

def boostLabel (eta : YoungDiagram) (n : ℕ) (i : Fin n) : ℕ :=
  eta.rowLen (n - 1 - i.val)

def boostedLabel (S : StandardYoungTableau μ) (eta : YoungDiagram) (i : Fin μ.card) : ℕ :=
  cochargeLabel S i + boostLabel eta μ.card i

def boostedFilling (S : StandardYoungTableau μ) (eta : YoungDiagram) (c : ↥μ.cells) : ℕ :=
  boostedLabel S eta (S c)

def transportedBoosted (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (eta : YoungDiagram) : Fin μ.card →₀ ℕ :=
  (witnessFinFinsupp μ.card).symm fun i => boostedFilling S eta (T.symm i)

end PrefixWitness

section ColumnProduct
variable {R : Type*} [CommRing R] {n : ℕ} {μ : YoungDiagram}
theorem witnessColumnMem (mu : YoungDiagram) (j : ℕ) (i : Fin (mu.colLen j)) :
    (i.val, j) ∈ mu := YoungDiagram.mem_iff_lt_colLen.mpr i.isLt

def columnEmbedding (U : ↥μ.cells ↪ Fin n) (j : ℕ) : Fin (μ.colLen j) ↪ Fin n where
  toFun i := U ⟨(i.val, j), witnessColumnMem μ j i⟩
  inj' i l h := by
    have hi := congrArg (fun c : ↥μ.cells => c.val.1) (U.injective h)
    exact Fin.ext hi

abbrev columnAlternant (U : ↥μ.cells ↪ Fin n) (j : ℕ) : PolynomialRing n R :=
  MvPolynomial.rename (columnEmbedding U j)
    (TauCeti.alternant (Fin (μ.colLen j)) R fun i => i.val)

def fillingLabels (U : ↥μ.cells ↪ Fin n) : Finset (Fin n) := Finset.univ.map U

def outsidePower (U : ↥μ.cells ↪ Fin n) (s : ℕ) : PolynomialRing n R :=
  ∏ i ∈ (fillingLabels U)ᶜ, (MvPolynomial.X i) ^ (s - 1)

/-- The manuscript's column product with its outside exponents.  The use of
n padded columns is harmless because zero-height alternants are 1. -/
abbrev columnWitness (U : ↥μ.cells ↪ Fin n) (s : ℕ) : PolynomialRing n R :=
  (∏ j ∈ Finset.range n, columnAlternant U j) * outsidePower U s

end ColumnProduct

section Exterior
variable {k n : ℕ}

def exteriorExponent (e : Fin k ↪ Fin n) (s : ℕ) : Fin n →₀ ℕ :=
  (witnessFinFinsupp n).symm fun i => if i ∈ Set.range e then 0 else s - 1

def embeddedWitnessAlpha (e : Fin k ↪ Fin n) (a : Fin k →₀ ℕ) (s : ℕ) : Fin n →₀ ℕ :=
  a.mapDomain e + exteriorExponent e s

end Exterior

section GriffinWitness
variable {μ : YoungDiagram}

def griffinWitnessAlpha (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (k : ℕ) (hk : k ≤ μ.card) (s : ℕ) : Fin μ.card →₀ ℕ :=
  embeddedWitnessAlpha (prefixAmbientEmbedding S T k hk)
    (insertionAlpha (prefixTableau S k hk) (prefixTableau S k hk).toTableau) s

def griffinWitnessRejection (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (eta : YoungDiagram) (k : ℕ) (hk : k ≤ μ.card) (s : ℕ) : Fin μ.card →₀ ℕ :=
  griffinWitnessAlpha S T k hk s - transportedBoosted S T eta

variable {R : Type*} [CommRing R]

abbrev griffinApolarWitness (S : StandardYoungTableau μ) (T : YoungTableau μ)
    (k : ℕ) (hk : k ≤ μ.card) (s : ℕ) : PolynomialRing μ.card R :=
  columnWitness (((insertionFilling (prefixTableau S k hk)
    (prefixTableau S k hk).toTableau).toEmbedding).trans (prefixAmbientEmbedding S T k hk)) s

end GriffinWitness

def exteriorPart {k n : ℕ} (e : Fin k ↪ Fin n) (b : Fin n →₀ ℕ) : Fin n →₀ ℕ :=
  (witnessFinFinsupp n).symm fun i => if i ∈ Set.range e then 0 else b i

section UntruncatedWitness
variable {mu : YoungDiagram}

def untruncatedWitnessAlpha (S : StandardYoungTableau mu) (T : YoungTableau mu)
    (eta : YoungDiagram) (k : ℕ) (hk : k ≤ mu.card) : Fin mu.card →₀ ℕ :=
  (insertionAlpha (prefixTableau S k hk) (prefixTableau S k hk).toTableau).mapDomain
    (prefixAmbientEmbedding S T k hk) +
      exteriorPart (prefixAmbientEmbedding S T k hk) (transportedBoosted S T eta)

def untruncatedWitnessRejection (S : StandardYoungTableau mu) (T : YoungTableau mu)
    (eta : YoungDiagram) (k : ℕ) (hk : k ≤ mu.card) : Fin mu.card →₀ ℕ :=
  untruncatedWitnessAlpha S T eta k hk - transportedBoosted S T eta

end UntruncatedWitness

section DividedAction
variable {σ R : Type*} [CommRing R]

def contractMonomial (d : σ →₀ ℕ) :
    MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  (MvPolynomial.basisMonomials σ R).constr R fun a =>
    if d ≤ a then MvPolynomial.monomial (a - d) 1 else 0

theorem contractMonomial_zero :
    contractMonomial (σ := σ) (R := R) 0 = LinearMap.id := by sorry

theorem contractMonomial_add (a b : σ →₀ ℕ) :
    contractMonomial (R := R) (a + b) =
      (contractMonomial a).comp (contractMonomial b) := by sorry

def contractionMonoidHom : Multiplicative (σ →₀ ℕ) →*
    Module.End R (MvPolynomial σ R) where
  toFun a := contractMonomial a.toAdd
  map_one' := contractMonomial_zero
  map_mul' a b := contractMonomial_add a.toAdd b.toAdd

/-- The acting polynomial algebra, represented by divided-power contractions. -/
def dividedAction : MvPolynomial σ R →ₐ[R] Module.End R (MvPolynomial σ R) :=
  AddMonoidAlgebra.lift R (Module.End R (MvPolynomial σ R)) (σ →₀ ℕ)
    contractionMonoidHom

end DividedAction

section OrdinaryAction
variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K] [CharZero K]

def exponentFactorial (a : σ →₀ ℕ) : ℕ := ∏ i, (a i).factorial

def factorialNormalize : MvPolynomial σ K →ₗ[K] MvPolynomial σ K :=
  (MvPolynomial.basisMonomials σ K).constr K fun a =>
    MvPolynomial.monomial a (exponentFactorial a : K)⁻¹

def factorialDenormalize : MvPolynomial σ K →ₗ[K] MvPolynomial σ K :=
  (MvPolynomial.basisMonomials σ K).constr K fun a =>
    MvPolynomial.monomial a (exponentFactorial a : K)

theorem exponentFactorial_ne_zero (a : σ →₀ ℕ) :
    (exponentFactorial a : K) ≠ 0 := by sorry

theorem coeff_factorialNormalize (p : MvPolynomial σ K) (a : σ →₀ ℕ) :
    (factorialNormalize p).coeff a = p.coeff a / exponentFactorial a := by sorry

theorem coeff_factorialDenormalize (p : MvPolynomial σ K) (a : σ →₀ ℕ) :
    (factorialDenormalize p).coeff a = p.coeff a * exponentFactorial a := by sorry

def factorialTransport : MvPolynomial σ K ≃ₗ[K] MvPolynomial σ K where
  toLinearMap := factorialNormalize
  invFun := factorialDenormalize
  left_inv p := by
    change factorialDenormalize (factorialNormalize p) = p
    apply MvPolynomial.ext
    intro a
    rw [coeff_factorialDenormalize, coeff_factorialNormalize]
    exact div_mul_cancel₀ _ (exponentFactorial_ne_zero (K := K) a)
  right_inv p := by
    change factorialNormalize (factorialDenormalize p) = p
    apply MvPolynomial.ext
    intro a
    rw [coeff_factorialNormalize, coeff_factorialDenormalize]
    exact mul_div_cancel_right₀ _ (exponentFactorial_ne_zero (K := K) a)

def ordinaryAction : MvPolynomial σ K →ₐ[K] Module.End K (MvPolynomial σ K) :=
  ((factorialTransport (σ := σ) (K := K)).conjAlgEquiv K).toAlgHom.comp dividedAction

end OrdinaryAction
theorem witnessDerivativeSMulComm (n : ℕ) :
    SMulCommClass ℂ ℂ (AddMonoidAlgebra ℂ (Fin n →₀ ℕ)) := inferInstance
theorem witnessDerivativeScalarTower (n : ℕ) :
    IsScalarTower ℂ ℂ (AddMonoidAlgebra ℂ (Fin n →₀ ℕ)) := inferInstance
abbrev witnessDerivativeEndAlgebra (n : ℕ) : Algebra ℂ (Module.End ℂ (PolynomialRing n ℂ)) :=
  @Module.End.instAlgebra ℂ ℂ (PolynomialRing n ℂ) _ _ _ _ _
    (witnessDerivativeSMulComm n) _ (witnessDerivativeScalarTower n)

def normalizedOrdinaryDerivative {n : ℕ} (r : Fin n →₀ ℕ) (g : PolynomialRing n ℂ) :
    PolynomialRing n ℂ :=
  (exponentFactorial r : ℂ)⁻¹ •
    (@AlgHom.toLinearMap ℂ (PolynomialRing n ℂ) (Module.End ℂ (PolynomialRing n ℂ))
      _ _ _ _ (witnessDerivativeEndAlgebra n) ordinaryAction)
      (MvPolynomial.monomial r (1 : ℂ)) g

def adjointYoungApply {mu : YoungDiagram} (T : YoungTableau mu)
    (f : PolynomialRing mu.card ℂ) : PolynomialRing mu.card ℂ :=
  rowSymmetrize (rowSubgroup T) (columnAlternate (colSubgroup T) f)

def cyclicPolynomialCopy {n : ℕ} (h : PolynomialRing n ℂ) :
    Submodule ℂ (PolynomialRing n ℂ) :=
  Submodule.span ℂ (Set.range fun sigma : Equiv.Perm (Fin n) => MvPolynomial.rename sigma h)

def maximalFinitePrefix {n s : ℕ} (i : FiniteHarmonicIndex n s) : ℕ :=
  min (n - i.multiplier.colLen 0)
    (∑ r ∈ Finset.range s, (columnInsertion i.left).state.shape.rowLen r)

theorem maximalFinitePrefix_le {n s : ℕ} (i : FiniteHarmonicIndex n s) :
    maximalFinitePrefix i ≤ (YoungDiagram.ofPartition i.part).card := by
  rw [YoungDiagram.card_ofPartition]
  exact (min_le_left _ _).trans (Nat.sub_le _ _)

def maximalUntruncatedPrefix {n : ℕ} (i : UnboundedHarmonicIndex n) : ℕ :=
  n - i.multiplier.colLen 0

theorem maximalUntruncatedPrefix_le {n : ℕ} (i : UnboundedHarmonicIndex n) :
    maximalUntruncatedPrefix i ≤ (YoungDiagram.ofPartition i.part).card := by
  rw [YoungDiagram.card_ofPartition]
  exact Nat.sub_le _ _
theorem witnessPartitionCard {n : ℕ} (p : n.Partition) :
    (YoungDiagram.ofPartition p).card = n := YoungDiagram.card_ofPartition p

def finiteCommonHarmonicVectorWithTableau {n s : ℕ} (i : FiniteHarmonicIndex n s)
    (T : YoungTableau (YoungDiagram.ofPartition i.part)) : PolynomialRing n ℂ :=
  MvPolynomial.rename (finCongr (witnessPartitionCard i.part))
    (adjointYoungApply T (normalizedOrdinaryDerivative
      (griffinWitnessRejection i.left T i.multiplier (maximalFinitePrefix i)
        (maximalFinitePrefix_le i) s)
      (griffinApolarWitness i.left T (maximalFinitePrefix i) (maximalFinitePrefix_le i) s)))

/-- The untruncated witness is the actual Vandermonde column product times
the exterior cocharge monomial, with exactly the prescribed rejection and
factorial. -/
def literalUntruncatedHarmonicVector {n : ℕ} (i : UnboundedHarmonicIndex n)
    (T : YoungTableau (YoungDiagram.ofPartition i.part)) : PolynomialRing n ℂ :=
  let k := maximalUntruncatedPrefix i
  let hk := maximalUntruncatedPrefix_le i
  let e := prefixAmbientEmbedding i.left T k hk
  let U := (insertionFilling (prefixTableau i.left k hk)
    (prefixTableau i.left k hk).toTableau).toEmbedding.trans e
  let G : PolynomialRing (YoungDiagram.ofPartition i.part).card ℂ :=
    (∏ j ∈ Finset.range (YoungDiagram.ofPartition i.part).card, columnAlternant U j) *
      MvPolynomial.monomial (exteriorPart e (transportedBoosted i.left T i.multiplier)) 1
  MvPolynomial.rename (finCongr (YoungDiagram.card_ofPartition i.part))
    (adjointYoungApply T (normalizedOrdinaryDerivative
      (untruncatedWitnessRejection i.left T i.multiplier k hk) G))

theorem adjoinOnes_isLowerSet (μ : YoungDiagram) (m : ℕ) :
    IsLowerSet (↑(μ.cells ∪ (Finset.range (μ.colLen 0 + m) ×ˢ {0})) : Set (ℕ × ℕ)) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨hac, hbd⟩ h
    rcases Finset.mem_union.mp h with h | h
    · exact Finset.mem_union_left _ (μ.isLowerSet ⟨hac, hbd⟩ h)
    · apply Finset.mem_union_right
      simp only [Finset.mem_product, Finset.mem_range, Finset.mem_singleton] at h ⊢
      exact ⟨hac.trans_lt h.1, by omega⟩

def adjoinOnes (μ : YoungDiagram) (m : ℕ) : YoungDiagram where
  cells := μ.cells ∪ (Finset.range (μ.colLen 0 + m) ×ˢ {0})
  isLowerSet := adjoinOnes_isLowerSet μ m

/-- The coinvariant case, whose Young diagram is one column of height n. -/
def columnPartition (k : ℕ) : YoungDiagram := adjoinOnes ⊥ k

abbrev SpringerCommonIndex (n : ℕ) :=
  Σ part : n.Partition, StandardYoungTableau (YoungDiagram.ofPartition part)

theorem descentNumber_lt_card {mu : YoungDiagram}
    (S : StandardYoungTableau mu) (hmu : 0 < mu.card) : descentNumber S < mu.card := by sorry

def springerCommonFiniteIndex {n : ℕ} (hn : 0 < n) (z : SpringerCommonIndex n) :
    FiniteHarmonicIndex n n where
  part := z.1
  left := z.2
  multiplier := ⊥
  multiplier_length := by simp
  descents_lt := by
    simpa only [YoungDiagram.card_ofPartition] using
      descentNumber_lt_card z.2 (by simpa only [YoungDiagram.card_ofPartition] using hn)
  multiplier_width := by simp

def springerCommonHarmonicVectorWithTableau {n : ℕ} (hn : 0 < n)
    (z : SpringerCommonIndex n) (T : YoungTableau (YoungDiagram.ofPartition z.1)) :
    PolynomialRing n ℂ :=
  finiteCommonHarmonicVectorWithTableau (springerCommonFiniteIndex hn z) T

/-- The same irreducible Springer witnesses decompose the entire coinvariant
harmonic space and give each Springer harmonic space by its admissible indices. -/
theorem springer_harmonics_full_decomposition (n : ℕ) (hn : 0 < n)
    (T : (part : n.Partition) → YoungTableau (YoungDiagram.ofPartition part)) :
    ∃ W : SpringerCommonIndex n → Subrepresentation (polynomialRepresentation ℂ n),
      (∀ z, (W z).toSubmodule =
          cyclicPolynomialCopy (springerCommonHarmonicVectorWithTableau hn z (T z.1)) ∧
        Nonempty (Representation.Equiv (paperYoungIdealRepresentation z.1 (T z.1))
          (W z).toRepresentation) ∧
        (W z).toRepresentation.IsIrreducible ∧
        (W z).toSubmodule ≤ homogeneousSubmodule (Fin n) ℂ (cochargeDegree z.2)) ∧
      iSupIndep (fun z => (W z).toSubmodule) ∧
      (∀ p : PolynomialRing n ℂ,
        (∀ f ∈ untruncatedIdeal ℂ n (columnPartition n), apolarCoefficientPairing f p = 0) ↔
        p ∈ ⨆ z : SpringerCommonIndex n, (W z).toSubmodule) ∧
      ∀ (mu : YoungDiagram) (hmu : mu.card = n) (p : PolynomialRing n ℂ),
        (∀ f ∈ untruncatedIdeal ℂ n mu, apolarCoefficientPairing f p = 0) ↔
        p ∈ ⨆ z : {z : SpringerCommonIndex n // CatDominates z.2 mu}, (W z.val).toSubmodule := by sorry

end HigherSpecht
