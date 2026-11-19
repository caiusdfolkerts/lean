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
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Actual graded characters and Specht multiplicities -/

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
noncomputable abbrev rowSymmetrizer (t : YoungTableau μ) :
    MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card)) :=
  ∑ p : rowSubgroup t, MonoidAlgebra.of ℚ (Equiv.Perm (Fin μ.card)) p

/-- The **column antisymmetrizer** `b_t`, the signed sum of the permutations preserving the
columns of `t`. -/
noncomputable abbrev columnAntisymmetrizer (t : YoungTableau μ) :
    MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card)) :=
  ∑ q : colSubgroup t,
    ((Equiv.Perm.sign (q : Equiv.Perm (Fin μ.card)) : ℤ) : ℚ) •
      MonoidAlgebra.of ℚ (Equiv.Perm (Fin μ.card)) q

/-- The **Young symmetrizer** of `t`, with the convention `c_t = a_t b_t`. On a left module it
acts by column-antisymmetrization followed by row-symmetrization. -/
noncomputable abbrev youngSymmetrizer (t : YoungTableau μ) :
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

/-- A basis assertion retaining the prescribed vector at every actual index. -/
def IsSpecifiedBasis {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (v : ι → V) : Prop :=
  ∃ b : Basis ι R V, ∀ i, b i = v i

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

def finiteMasterPolynomial {R : Type*} [CommRing R] {n s : ℕ}
    (i : FiniteHarmonicIndex n s)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)) : PolynomialRing n R :=
  rename (finCongr (YoungDiagram.card_ofPartition i.part)) (higherSpechtPolynomial i.left T) *
    elementaryMultiplier n n i.multiplier.rowLen

def unboundedMasterPolynomial {R : Type*} [CommRing R] {n : ℕ}
    (i : UnboundedHarmonicIndex n)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)) : PolynomialRing n R :=
  rename (finCongr (YoungDiagram.card_ofPartition i.part)) (higherSpechtPolynomial i.left T) *
    elementaryMultiplier n n i.multiplier.rowLen

structure BoundedGriffinShape (n s : ℕ) where
  diagram : YoungDiagram
  card_le : diagram.card ≤ n
  height_le : diagram.colLen 0 ≤ s

inductive GriffinIdealExpression (n s : ℕ) where
  | atom : BoundedGriffinShape n s → GriffinIdealExpression n s
  | sum : GriffinIdealExpression n s → GriffinIdealExpression n s → GriffinIdealExpression n s
  | intersection : GriffinIdealExpression n s → GriffinIdealExpression n s → GriffinIdealExpression n s

namespace GriffinIdealExpression

variable {n s : ℕ}

def ideal (R : Type*) [CommRing R] : GriffinIdealExpression n s → Ideal (PolynomialRing n R)
  | .atom a => griffinIdeal R n a.diagram s
  | .sum e f => ideal R e ⊔ ideal R f
  | .intersection e f => ideal R e ⊓ ideal R f

def eligible : GriffinIdealExpression n s → Set (FiniteHarmonicIndex n s)
  | .atom a => {i | i.toUnboundedHarmonicIndex.eligible a.diagram a.card_le}
  | .sum e f => eligible e ∩ eligible f
  | .intersection e f => eligible e ∪ eligible f

variable (e : GriffinIdealExpression n s)

abbrev VectorIndex (e : GriffinIdealExpression n s) :=
  Σ i : {i // i ∈ e.eligible}, StandardYoungTableau (YoungDiagram.ofPartition i.val.part)

def polynomial (R : Type*) [CommRing R] (z : e.VectorIndex) : PolynomialRing n R :=
  finiteMasterPolynomial z.1.val z.2

def family (R : Type*) [CommRing R] (z : e.VectorIndex) : PolynomialRing n R ⧸ e.ideal R :=
  Ideal.Quotient.mk (e.ideal R) (e.polynomial R z)

end GriffinIdealExpression

def generatedGriffinIdealLattice (n s : ℕ) : Set (Ideal (PolynomialRing n ℂ)) :=
  Set.range (GriffinIdealExpression.ideal ℂ (n := n) (s := s))

structure BoundedUntruncatedShape (n : ℕ) where
  diagram : YoungDiagram
  card_le : diagram.card ≤ n

inductive UntruncatedIdealExpression (n : ℕ) where
  | atom : BoundedUntruncatedShape n → UntruncatedIdealExpression n
  | sum : UntruncatedIdealExpression n → UntruncatedIdealExpression n →
      UntruncatedIdealExpression n
  | intersection : UntruncatedIdealExpression n → UntruncatedIdealExpression n →
      UntruncatedIdealExpression n

namespace UntruncatedIdealExpression

variable {n : ℕ}

def ideal (R : Type*) [CommRing R] : UntruncatedIdealExpression n →
    Ideal (PolynomialRing n R)
  | .atom a => untruncatedIdeal R n a.diagram
  | .sum e f => e.ideal R ⊔ f.ideal R
  | .intersection e f => e.ideal R ⊓ f.ideal R

def eligible : UntruncatedIdealExpression n → Set (UnboundedHarmonicIndex n)
  | .atom a => {i | i.eligible a.diagram a.card_le}
  | .sum e f => e.eligible ∩ f.eligible
  | .intersection e f => e.eligible ∪ f.eligible

variable (e : UntruncatedIdealExpression n)

abbrev VectorIndex :=
  Σ i : {i : UnboundedHarmonicIndex n // i ∈ e.eligible},
    StandardYoungTableau (YoungDiagram.ofPartition i.val.part)

def polynomial (R : Type*) [CommRing R] (z : e.VectorIndex) : PolynomialRing n R :=
  unboundedMasterPolynomial z.1.val z.2

def family (R : Type*) [CommRing R] (z : e.VectorIndex) : PolynomialRing n R ⧸ e.ideal R :=
  Ideal.Quotient.mk (e.ideal R) (e.polynomial R z)

end UntruncatedIdealExpression

def generatedUntruncatedIdealLattice (n : ℕ) : Set (Ideal (PolynomialRing n ℂ)) :=
  Set.range (UntruncatedIdealExpression.ideal ℂ (n := n))

abbrev SpringerCommonIndex (n : ℕ) :=
  Σ part : n.Partition, StandardYoungTableau (YoungDiagram.ofPartition part)

def springerIntersectionIdeal (R : Type*) [CommRing R] {n : ℕ}
    (A : Finset n.Partition) : Ideal (PolynomialRing n R) :=
  ⨅ part ∈ A, untruncatedIdeal R n (YoungDiagram.ofPartition part)

abbrev SpringerIntersectionLeftIndex {n : ℕ} (A : Finset n.Partition) :=
  {z : SpringerCommonIndex n // ∃ part ∈ A, CatDominates z.2 (YoungDiagram.ofPartition part)}

abbrev SpringerIntersectionVectorIndex {n : ℕ} (A : Finset n.Partition) :=
  Σ z : SpringerIntersectionLeftIndex A,
    StandardYoungTableau (YoungDiagram.ofPartition z.val.1)

def springerIntersectionPolynomial {R : Type*} [CommRing R] {n : ℕ}
    (A : Finset n.Partition) (z : SpringerIntersectionVectorIndex A) : PolynomialRing n R :=
  rename (finCongr (YoungDiagram.card_ofPartition z.1.val.1))
    (higherSpechtPolynomial z.1.val.2 z.2)

def springerIntersectionFamily (R : Type*) [CommRing R] {n : ℕ}
    (A : Finset n.Partition) (z : SpringerIntersectionVectorIndex A) :
    PolynomialRing n R ⧸ springerIntersectionIdeal R A :=
  Ideal.Quotient.mk _ (springerIntersectionPolynomial A z)

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

end PermutationActions

/-- The Specht representation of this shape, presented as the left ideal
generated by the row symmetrizer times the column antisymmetrizer. -/
abbrev paperYoungIdealRepresentation {n : ℕ} (part : n.Partition)
    (T : YoungTableau (YoungDiagram.ofPartition part)) :=
  Representation.ofModule' (k := ℂ) (G := Equiv.Perm (Fin n))
    (Ideal.span {(MonoidAlgebra.domCongr ℂ ℂ
        (finCongr (YoungDiagram.card_ofPartition part)).permCongrHom
        (TauCeti.YoungTableau.youngSymmetrizerOver ℂ T))} :
      Ideal (MonoidAlgebra ℂ (Equiv.Perm (Fin n))))

section GradedPieces
variable {R : Type*} [CommRing R] {n : ℕ}

def homogeneousQuotientPiece (I : Ideal (PolynomialRing n R)) (d : ℕ) :
    Submodule R (PolynomialRing n R ⧸ I) :=
  (homogeneousSubmodule (Fin n) R d).map (Ideal.Quotient.mkₐ R I).toLinearMap

def homogeneousQuotientSubrepresentation (I : Ideal (PolynomialRing n R))
    (hperm : PermutationStable I) (d : ℕ) : Subrepresentation (quotientRepresentation I hperm) where
  toSubmodule := homogeneousQuotientPiece I d
  apply_mem_toSubmodule g x hx := by
    obtain ⟨p, hp, rfl⟩ := hx
    exact ⟨rename g p, hp.rename_isHomogeneous, rfl⟩

end GradedPieces

namespace GriffinIdealExpression

variable {n s : ℕ}

theorem permutationStable (R : Type*) [CommRing R] (e : GriffinIdealExpression n s) :
    PermutationStable (e.ideal R) := by sorry

end GriffinIdealExpression

theorem griffin_graded_specht_character {n s : ℕ} (e : GriffinIdealExpression n s)
    (hs : 0 < s) (d : ℕ) :
    ∃ T : (part : n.Partition) → YoungTableau (YoungDiagram.ofPartition part),
    ∃ f : Fintype {i : FiniteHarmonicIndex n s // i ∈ e.eligible ∧ i.toUnboundedHarmonicIndex.degree = d},
    ∀ g : Equiv.Perm (Fin n),
      letI := f
      (homogeneousQuotientSubrepresentation (e.ideal ℂ)
        (e.permutationStable ℂ) d).toRepresentation.character g =
        ∑ i : {i : FiniteHarmonicIndex n s // i ∈ e.eligible ∧ i.toUnboundedHarmonicIndex.degree = d},
          (paperYoungIdealRepresentation i.val.part (T i.val.part)).character g := by sorry

namespace UntruncatedIdealExpression

variable {n : ℕ}

theorem permutationStable (R : Type*) [CommRing R]
    (e : UntruncatedIdealExpression n) : PermutationStable (e.ideal R) := by sorry

end UntruncatedIdealExpression

theorem untruncated_graded_specht_character {n : ℕ} (e : UntruncatedIdealExpression n)
    (d : ℕ) :
    ∃ T : (part : n.Partition) → YoungTableau (YoungDiagram.ofPartition part),
    ∃ f : Fintype {i : UnboundedHarmonicIndex n // i ∈ e.eligible ∧ i.degree = d},
    ∀ g : Equiv.Perm (Fin n),
      letI := f
      (homogeneousQuotientSubrepresentation (e.ideal ℂ)
        (e.permutationStable ℂ) d).toRepresentation.character g =
        ∑ i : {i : UnboundedHarmonicIndex n // i ∈ e.eligible ∧ i.degree = d},
          (paperYoungIdealRepresentation i.val.part (T i.val.part)).character g := by sorry

/-- The full Springer intersection character in each degree. The real ideal
and its defining eligibility condition are both specified. -/
theorem springer_intersection_graded_specht_character {n : ℕ} (hn : 0 < n)
    (A : Finset n.Partition) (hA : A.Nonempty) (d : ℕ) :
    ∃ e : GriffinIdealExpression n n,
      e.ideal ℂ = springerIntersectionIdeal ℂ A ∧
      (∀ i : FiniteHarmonicIndex n n, i ∈ e.eligible ↔
        i.multiplier = ⊥ ∧ ∃ part ∈ A, CatDominates i.left (YoungDiagram.ofPartition part)) ∧
      ∃ T : (part : n.Partition) → YoungTableau (YoungDiagram.ofPartition part),
      ∃ f : Fintype {z : SpringerIntersectionLeftIndex A // cochargeDegree z.val.2 = d},
      ∀ g : Equiv.Perm (Fin n),
        letI := f
        (homogeneousQuotientSubrepresentation (e.ideal ℂ)
          (e.permutationStable ℂ) d).toRepresentation.character g =
          ∑ z : {z : SpringerIntersectionLeftIndex A // cochargeDegree z.val.2 = d},
            (paperYoungIdealRepresentation z.val.val.1 (T z.val.val.1)).character g := by sorry

abbrev UntruncatedLeftTableauIndex (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) :=
  {z : (Σ part : n.Partition, StandardYoungTableau (YoungDiagram.ofPartition part)) //
    CatDominates (prefixTableau z.2 lam.card
      (by simpa only [YoungDiagram.card_ofPartition] using hk)) lam}

/-- The exact elementary-parameter denominator, in character-valued form.
The numerator retains one Specht character per eligible left tableau. -/
theorem untruncated_graded_character_rational
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    let e : UntruncatedIdealExpression n := .atom ⟨lam, hk⟩
    ∃ T : (part : n.Partition) → YoungTableau (YoungDiagram.ofPartition part),
    ∃ f : Fintype (UntruncatedLeftTableauIndex n lam hk),
    ∀ g : Equiv.Perm (Fin n),
      letI := f
      (PowerSeries.mk fun d =>
        (homogeneousQuotientSubrepresentation (e.ideal ℂ)
          (e.permutationStable ℂ) d).toRepresentation.character g) *
        (∏ i : Fin (n - lam.card), (1 - (PowerSeries.X : PowerSeries ℂ) ^ (i.val + 1))) =
        ∑ b : UntruncatedLeftTableauIndex n lam hk,
          PowerSeries.C ((paperYoungIdealRepresentation b.val.1 (T b.val.1)).character g) *
            PowerSeries.X ^ cochargeDegree b.val.2 := by sorry

end HigherSpecht
