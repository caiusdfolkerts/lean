module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Interval
public import Mathlib.Topology.LocallyFinite
public import Lean.Elab.Tactic.Omega
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Data.Nat.Find
public import TauCeti.Geometry.Toric.Algebraic.Fan.Basic
public import Mathlib.Topology.Baire.CompleteMetrizable
public import TauCeti.Geometry.Convex.Cone.Alternative
public import Mathlib.Data.Fintype.BigOperators
public import ToricPower.LocalMorseGeometry
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Polyhedral strata, finite fan covers, and the local Morse chain calculation

This consolidated module keeps the elementary geometric dependencies in one
compiler unit. Every carrier, cone, face, direction space, and inclusion is
the actual mathematical object. No constructible-sheaf equivalence, local
acyclicity theorem, or fan detector is introduced as a hypothesis.

Candidate source until ordinary compilation succeeds.
-/

@[expose] public noncomputable section

section ArrangementCellsBundleSource
attribute [local instance] Classical.propDecidable

/-! Literal cells, integral labels, closure relations, and direction spaces
of the periodic integral hyperplane arrangement.  These are the recovered
ArrangementCore source sections 0 and 1, separated to keep the elementary
geometry independent of the CW chart and cellular homology development. -/

section ArrangementSource0









/-! # The literal cells of the integral hyperplane arrangement

For linear forms `fᵢ`, a cell records their integral ceilings and the
forms which are integral on the cell. This is the actual arrangement
`fᵢ(x) ∈ ℤ` used in the HHL resolution. Adding the coordinate forms gives
bounded closed cells without requiring the original rays to span.

The weight region is the actual convex set `fᵢ(x) ≤ lᵢ`. Its membership
is equivalent to the nonnegative monomial-exponent condition
`lᵢ - ceil(fᵢ(x)) ≥ 0`; this is the weight-by-weight identification used
in the affine HHL exactness proof, not a definition of exactness.
-/

@[expose] public noncomputable section

open Set Filter Topology

namespace ToricPower.IntegralArrangement

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E]

/-- A relatively open cell of the actual integral arrangement. -/
def cell (f : ι → E →ₗ[ℝ] ℝ) (e : ι → ℤ) (I : Set ι) : Set E :=
  {x | ∀ i, if i ∈ I then f i x = (e i : ℝ)
    else (e i : ℝ) - 1 < f i x ∧ f i x < (e i : ℝ)}

/-- The closed polyhedron underlying a nonempty cell. -/
def closedCell (f : ι → E →ₗ[ℝ] ℝ) (e : ι → ℤ) (I : Set ι) : Set E :=
  {x | ∀ i, if i ∈ I then f i x = (e i : ℝ)
    else (e i : ℝ) - 1 ≤ f i x ∧ f i x ≤ (e i : ℝ)}

def ceilingVector (f : ι → E →ₗ[ℝ] ℝ) (x : E) : ι → ℤ := fun i => ⌈f i x⌉

def integralIndices (f : ι → E →ₗ[ℝ] ℝ) (x : E) : Set ι :=
  {i | f i x = (⌈f i x⌉ : ℝ)}

theorem mem_cell_self (f : ι → E →ₗ[ℝ] ℝ) (x : E) :
    x ∈ cell f (ceilingVector f x) (integralIndices f x) := by
  intro i
  by_cases h : f i x = (⌈f i x⌉ : ℝ)
  · change (if f i x = (⌈f i x⌉ : ℝ) then
      f i x = (⌈f i x⌉ : ℝ) else
      (⌈f i x⌉ : ℝ) - 1 < f i x ∧ f i x < (⌈f i x⌉ : ℝ))
    rw [ite_eq_left h]
    exact h
  · change (if f i x = (⌈f i x⌉ : ℝ) then
      f i x = (⌈f i x⌉ : ℝ) else
      (⌈f i x⌉ : ℝ) - 1 < f i x ∧ f i x < (⌈f i x⌉ : ℝ))
    rw [ite_eq_right h]
    exact ⟨by linarith [Int.ceil_lt_add_one (f i x)],
      lt_of_le_of_ne (Int.le_ceil (f i x)) h⟩

theorem ceil_eq_of_mem_cell (f : ι → E →ₗ[ℝ] ℝ) (e : ι → ℤ) (I : Set ι)
    {x : E} (hx : x ∈ cell f e I) (i : ι) : ⌈f i x⌉ = e i := by
  by_cases hi : i ∈ I
  · have h := hx i
    simp only [ite_eq_left hi] at h
    rw [h, Int.ceil_intCast]
  · have h := hx i
    simp only [ite_eq_right hi] at h
    exact Int.ceil_eq_iff.mpr ⟨h.1, h.2.le⟩

theorem integralIndices_eq_of_mem_cell (f : ι → E →ₗ[ℝ] ℝ)
    (e : ι → ℤ) (I : Set ι) {x : E} (hx : x ∈ cell f e I) :
    integralIndices f x = I := by
  ext i
  change f i x = (⌈f i x⌉ : ℝ) ↔ i ∈ I
  rw [ceil_eq_of_mem_cell f e I hx i]
  by_cases hi : i ∈ I
  · have h := hx i
    rw [ite_eq_left hi] at h
    exact iff_of_true h hi
  · have h := hx i
    simp only [ite_eq_right hi] at h
    exact ⟨fun h' => (h.2.ne h').elim, fun h' => (hi h').elim⟩

/-- Every point lies in exactly one of the displayed cells. -/
theorem cell_indices_unique (f : ι → E →ₗ[ℝ] ℝ)
    {e e' : ι → ℤ} {I I' : Set ι} {x : E}
    (hx : x ∈ cell f e I) (hx' : x ∈ cell f e' I') : e = e' ∧ I = I' := by
  constructor
  · funext i
    exact (ceil_eq_of_mem_cell f e I hx i).symm.trans
      (ceil_eq_of_mem_cell f e' I' hx' i)
  · exact (integralIndices_eq_of_mem_cell f e I hx).symm.trans
      (integralIndices_eq_of_mem_cell f e' I' hx')

theorem cell_subset_closedCell (f : ι → E →ₗ[ℝ] ℝ) (e : ι → ℤ) (I : Set ι) :
    cell f e I ⊆ closedCell f e I := by
  intro x hx i
  by_cases hi : i ∈ I
  · simpa only [ite_eq_left hi] using hx i
  · have h := hx i
    simp only [ite_eq_right hi] at h ⊢
    exact ⟨h.1.le, h.2.le⟩

theorem closedCell_convex (f : ι → E →ₗ[ℝ] ℝ) (e : ι → ℤ) (I : Set ι) :
    Convex ℝ (closedCell f e I) := by
  intro x hx y hy a b ha hb hab i
  simp only [map_add, map_smul, smul_eq_mul]
  by_cases hi : i ∈ I
  · have hx' := hx i
    have hy' := hy i
    simp only [ite_eq_left hi] at hx' hy' ⊢
    rw [hx', hy', ← add_mul, hab, one_mul]
  · have hx' := hx i
    have hy' := hy i
    simp only [ite_eq_right hi] at hx' hy' ⊢
    exact (convex_Icc ((e i : ℝ) - 1) (e i : ℝ)) hx' hy' ha hb hab

theorem segment_mem_cell (f : ι → E →ₗ[ℝ] ℝ) (e : ι → ℤ) (I : Set ι)
    {x y : E} (hx : x ∈ cell f e I) (hy : y ∈ closedCell f e I)
    {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) : (1-r) • x + r • y ∈ cell f e I := by
  intro i
  simp only [map_add, map_smul, smul_eq_mul]
  by_cases hi : i ∈ I
  · have hx' := hx i
    have hy' := hy i
    simp only [ite_eq_left hi] at hx' hy' ⊢
    rw [hx', hy']
    ring
  · have hx' := hx i
    have hy' := hy i
    simp only [ite_eq_right hi] at hx' hy' ⊢
    have hpos : 0 < 1-r := sub_pos.mpr hr.2
    constructor
    · nlinarith [mul_pos hpos (sub_pos.mpr hx'.1),
        mul_nonneg hr.1 (sub_nonneg.mpr hy'.1)]
    · nlinarith [mul_pos hpos (sub_pos.mpr hx'.2),
        mul_nonneg hr.1 (sub_nonneg.mpr hy'.2)]

section Topology

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

theorem closedCell_isClosed (f : ι → E →ₗ[ℝ] ℝ)
    (hf : ∀ i, Continuous (f i)) (e : ι → ℤ) (I : Set ι) :
    IsClosed (closedCell f e I) := by
  simp only [closedCell, Set.setOf_forall]
  apply isClosed_iInter
  intro i
  by_cases hi : i ∈ I
  · simp only [ite_eq_left hi]
    exact isClosed_eq (hf i) continuous_const
  · simp only [ite_eq_right hi]
    exact (isClosed_le continuous_const (hf i)).inter
      (isClosed_le (hf i) continuous_const)

/-- The weak inequalities give exactly the closure, including all lower
dimensional cells; nonemptiness is the only geometric assumption. -/
theorem closure_cell (f : ι → E →ₗ[ℝ] ℝ) (hf : ∀ i, Continuous (f i))
    (e : ι → ℤ) (I : Set ι) (h : (cell f e I).Nonempty) :
    closure (cell f e I) = closedCell f e I := by
  apply Subset.antisymm
  · exact closure_minimal (cell_subset_closedCell f e I) (closedCell_isClosed f hf e I)
  · intro y hy
    obtain ⟨x, hx⟩ := h
    have hmem : ∀ᶠ r : ℝ in 𝓝[<] 1, (1-r) • x + r • y ∈ cell f e I := by
      filter_upwards [Ico_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with r hr
      exact segment_mem_cell f e I hx hy hr
    apply mem_closure_of_tendsto _ hmem
    have hcont : Continuous (fun r : ℝ => (1-r) • x + r • y) := by fun_prop
    have ht := (hcont.tendsto (1 : ℝ)).mono_left
      (nhdsWithin_le_nhds (a := (1 : ℝ)) (s := Iio 1))
    simpa only [sub_self, zero_smul, one_smul, zero_add] using ht

end Topology

/-- The actual convex polyhedron occurring in a monomial weight piece. -/
def weightRegion (f : ι → E →ₗ[ℝ] ℝ) (l : ι → ℤ) : Set E :=
  {x | ∀ i, f i x ≤ (l i : ℝ)}

theorem mem_weightRegion_iff (f : ι → E →ₗ[ℝ] ℝ) (l : ι → ℤ) (x : E) :
    x ∈ weightRegion f l ↔ ∀ i, 0 ≤ l i - ⌈f i x⌉ := by
  simp only [weightRegion, mem_ofPred_eq, sub_nonneg, Int.ceil_le]

theorem cell_weightRegion_iff (f : ι → E →ₗ[ℝ] ℝ) (l e : ι → ℤ)
    (I : Set ι) {x : E} (hx : x ∈ cell f e I) :
    x ∈ weightRegion f l ↔ ∀ i, 0 ≤ l i - e i := by
  rw [mem_weightRegion_iff]
  simp only [ceil_eq_of_mem_cell f e I hx]

/-- An allowed monomial cell has its entire closed cell in the weight
polyhedron. Thus the literal weight pieces are subcomplexes. -/
theorem closedCell_subset_weightRegion (f : ι → E →ₗ[ℝ] ℝ)
    (l e : ι → ℤ) (I : Set ι) (he : ∀ i, e i ≤ l i) :
    closedCell f e I ⊆ weightRegion f l := by
  intro x hx i
  have hi : f i x ≤ (e i : ℝ) := by
    by_cases hI : i ∈ I
    · have h := hx i
      simp only [ite_eq_left hI] at h
      exact h.le
    · have h := hx i
      simp only [ite_eq_right hI] at h
      exact h.2
  exact hi.trans (by exact_mod_cast he i)

/-- Integral translation acts on the actual arrangement cells by translating
their ceiling vectors. This is the periodicity used in the torus quotient. -/
theorem add_mem_cell_iff (f : ι → E →ₗ[ℝ] ℝ) (e k : ι → ℤ) (I : Set ι)
    (z : E) (hz : ∀ i, f i z = (k i : ℝ)) (x : E) :
    x + z ∈ cell f (e + k) I ↔ x ∈ cell f e I := by
  constructor <;> intro hx i
  all_goals
    have h := hx i
    simp only [map_add, hz, Pi.add_apply, Int.cast_add] at h ⊢
    by_cases hi : i ∈ I
    · simp only [ite_eq_left hi] at h ⊢
      linarith
    · simp only [ite_eq_right hi] at h ⊢
      constructor <;> linarith [h.1, h.2]

section Coordinates

open scoped BigOperators

variable {n s : ℕ}

/-- An integral row acts by its literal real dot product. -/
def integralRowForm (A : Fin s → Fin n → ℤ) (i : Fin s) :
    (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ j, (A i j : ℝ) * x j
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- Coordinate hyperplanes refine the arrangement and make its closed cells
bounded. They do not change the monomial inequalities in `weightRegion`. -/
def augmentedForms (A : Fin s → Fin n → ℤ) :
    Fin s ⊕ Fin n → (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  Sum.elim (integralRowForm A) LinearMap.proj

theorem closedCell_coordinate_bounds (A : Fin s → Fin n → ℤ)
    (e : Fin s ⊕ Fin n → ℤ) (I : Set (Fin s ⊕ Fin n))
    {x : Fin n → ℝ} (hx : x ∈ closedCell (augmentedForms A) e I) (j : Fin n) :
    (e (.inr j) : ℝ)-1 ≤ x j ∧ x j ≤ (e (.inr j) : ℝ) := by
  have h := hx (.inr j)
  by_cases hi : Sum.inr j ∈ I
  · simp only [ite_eq_left hi, augmentedForms, Sum.elim_inr, LinearMap.proj_apply] at h
    constructor <;> linarith
  · simpa only [ite_eq_right hi, augmentedForms, Sum.elim_inr, LinearMap.proj_apply] using h

/-- Every closed cell in the refined arrangement is an actual compact
convex polyhedron, also in rank zero and for lower dimensional cells. -/
theorem closedCell_isCompact (A : Fin s → Fin n → ℤ)
    (e : Fin s ⊕ Fin n → ℤ) (I : Set (Fin s ⊕ Fin n)) :
    IsCompact (closedCell (augmentedForms A) e I) := by
  apply (isCompact_Icc (a := fun j : Fin n => (e (.inr j) : ℝ)-1)
    (b := fun j : Fin n => (e (.inr j) : ℝ))).of_isClosed_subset
  · exact closedCell_isClosed _ (fun i => (augmentedForms A i).continuous_of_finiteDimensional) _ _
  · intro x hx
    exact ⟨fun j => (closedCell_coordinate_bounds A e I hx j).1,
      fun j => (closedCell_coordinate_bounds A e I hx j).2⟩

end Coordinates

end ToricPower.IntegralArrangement

end
end ArrangementSource0

section ArrangementSource1







/-! # Actual faces of the integral arrangement

The lower-dimensional boundary cells below are the literal cells containing
the boundary points. Their dimensions are the dimensions of the intersections
of the active kernels. In particular, the boundary dimension drop is proved
from a new independent equation; it is not assumed as cell-complex data.

This source is a candidate until its ordinary compiler record succeeds.
-/

@[expose] public noncomputable section

open Set

namespace ToricPower.IntegralArrangement

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E]

/-- The actual direction space of a nonempty cell. -/
def cellDirection (f : ι → E →ₗ[ℝ] ℝ) (I : Set ι) : Submodule ℝ E :=
  ⨅ i ∈ I, LinearMap.ker (f i)

theorem mem_cellDirection (f : ι → E →ₗ[ℝ] ℝ) (I : Set ι) (v : E) :
    v ∈ cellDirection f I ↔ ∀ i ∈ I, f i v = 0 := by
  simp [cellDirection]

theorem sub_mem_cellDirection (f : ι → E →ₗ[ℝ] ℝ) (e : ι → ℤ)
    (I : Set ι) {x y : E} (hx : x ∈ closedCell f e I)
    (hy : y ∈ closedCell f e I) : y - x ∈ cellDirection f I := by
  rw [mem_cellDirection]
  intro i hi
  have hx' := hx i
  have hy' := hy i
  simp only [ite_eq_left hi] at hx' hy'
  rw [map_sub, hx', hy', sub_self]

theorem active_subset_of_mem_closedCell (f : ι → E →ₗ[ℝ] ℝ)
    (e : ι → ℤ) (I : Set ι) {y : E} (hy : y ∈ closedCell f e I) :
    I ⊆ integralIndices f y := by
  intro i hi
  have h := hy i
  simp only [ite_eq_left hi] at h
  change f i y = (⌈f i y⌉ : ℝ)
  rw [h, Int.ceil_intCast]

theorem ceiling_bounds_of_mem_closedCell (f : ι → E →ₗ[ℝ] ℝ)
    (e : ι → ℤ) (I : Set ι) {y : E} (hy : y ∈ closedCell f e I) (i : ι) :
    e i - 1 ≤ ceilingVector f y i ∧ ceilingVector f y i ≤ e i := by
  by_cases hi : i ∈ I
  · have h := hy i
    simp only [ite_eq_left hi] at h
    simp [ceilingVector, h]
  · have h := hy i
    simp only [ite_eq_right hi] at h
    constructor
    · apply (Int.cast_le (R := ℝ)).mp
      simp only [Int.cast_sub, Int.cast_one]
      exact h.1.trans (Int.le_ceil (f i y))
    · exact Int.ceil_le.mpr h.2

/-- Every cell met by the closure is itself contained in that closure. -/
theorem closedCell_of_point_subset (f : ι → E →ₗ[ℝ] ℝ)
    (e : ι → ℤ) (I : Set ι) {y : E} (hy : y ∈ closedCell f e I) :
    closedCell f (ceilingVector f y) (integralIndices f y) ⊆ closedCell f e I := by
  intro z hz i
  have hzy := hz i
  have hyi := hy i
  have hb := ceiling_bounds_of_mem_closedCell f e I hy i
  by_cases hi : i ∈ I
  · have hIy := active_subset_of_mem_closedCell f e I hy hi
    simp only [ite_eq_left hi] at hyi ⊢
    simp only [ite_eq_left hIy, ceilingVector] at hzy
    rw [hyi, Int.ceil_intCast] at hzy
    exact hzy
  · simp only [ite_eq_right hi] at hyi ⊢
    by_cases hyint : i ∈ integralIndices f y
    · simp only [ite_eq_left hyint] at hzy
      rw [hzy]
      constructor
      · exact_mod_cast hb.1
      · exact_mod_cast hb.2
    · simp only [ite_eq_right hyint] at hzy
      have he : ceilingVector f y i = e i := by
        by_contra hne
        have hlow : ceilingVector f y i = e i - 1 := by omega
        have hval : f i y = ((e i - 1 : ℤ) : ℝ) := by
          have hu := Int.le_ceil (f i y)
          change f i y ≤ (ceilingVector f y i : ℝ) at hu
          rw [hlow] at hu
          have hl : ((e i - 1 : ℤ) : ℝ) ≤ f i y := by
            simpa only [Int.cast_sub, Int.cast_one] using hyi.1
          exact le_antisymm hu hl
        apply hyint
        change f i y = (⌈f i y⌉ : ℝ)
        rw [hval, Int.ceil_intCast]
      rw [he] at hzy
      exact hzy

/-- A proper boundary point imposes a genuinely new equation on the
direction space; redundant equations cannot cause a spurious dimension drop. -/
theorem boundary_direction_lt (f : ι → E →ₗ[ℝ] ℝ)
    (e : ι → ℤ) (I : Set ι) {x y : E}
    (hx : x ∈ cell f e I) (hy : y ∈ closedCell f e I)
    (hyn : y ∉ cell f e I) :
    cellDirection f (integralIndices f y) < cellDirection f I := by
  have hI := active_subset_of_mem_closedCell f e I hy
  have hle : cellDirection f (integralIndices f y) ≤ cellDirection f I := by
    intro v hv
    rw [mem_cellDirection] at hv ⊢
    exact fun i hi => hv i (hI hi)
  apply lt_of_le_of_ne hle
  intro heq
  have hv : y - x ∈ cellDirection f (integralIndices f y) := by
    rw [heq]
    exact sub_mem_cellDirection f e I (cell_subset_closedCell f e I hx) hy
  rw [mem_cellDirection] at hv
  apply hyn
  intro i
  by_cases hi : i ∈ I
  · simpa only [ite_eq_left hi] using hy i
  · have hx' := hx i
    have hy' := hy i
    simp only [ite_eq_right hi] at hx' hy' ⊢
    have hlow : f i y ≠ (e i : ℝ) - 1 := by
      intro hylo
      have hIy : i ∈ integralIndices f y := by
        change f i y = (⌈f i y⌉ : ℝ)
        have hcast : (e i : ℝ) - 1 = ((e i - 1 : ℤ) : ℝ) := by simp only [Int.cast_sub, Int.cast_one]
        rw [hylo, hcast, Int.ceil_intCast]
      have hzero := hv i hIy
      rw [map_sub, hylo] at hzero
      linarith [hx'.1]
    have hupp : f i y ≠ (e i : ℝ) := by
      intro hyhi
      have hIy : i ∈ integralIndices f y := by
        change f i y = (⌈f i y⌉ : ℝ)
        rw [hyhi, Int.ceil_intCast]
      have hzero := hv i hIy
      rw [map_sub, hyhi] at hzero
      linarith [hx'.2]
    exact ⟨lt_of_le_of_ne hy'.1 hlow.symm, lt_of_le_of_ne hy'.2 hupp⟩

theorem boundary_finrank_lt [FiniteDimensional ℝ E]
    (f : ι → E →ₗ[ℝ] ℝ) (e : ι → ℤ) (I : Set ι) {x y : E}
    (hx : x ∈ cell f e I) (hy : y ∈ closedCell f e I)
    (hyn : y ∉ cell f e I) :
    Module.finrank ℝ (cellDirection f (integralIndices f y)) <
      Module.finrank ℝ (cellDirection f I) :=
  Submodule.finrank_lt_finrank_of_lt (boundary_direction_lt f e I hx hy hyn)

/-- Only finitely many actual cell labels meet the closure of one cell. -/
theorem finite_labels_meeting_closedCell [Finite ι]
    (f : ι → E →ₗ[ℝ] ℝ) (e : ι → ℤ) (I : Set ι) :
    Set.Finite {p : (ι → ℤ) × Set ι |
      ∃ y ∈ closedCell f e I, y ∈ cell f p.1 p.2} := by
  have hf : Set.Finite {d : ι → ℤ | ∀ i, d i ∈ Icc (e i - 1) (e i)} :=
    Set.Finite.pi' (fun i => Set.finite_Icc (e i - 1) (e i))
  apply (hf.prod (Set.finite_univ : Set.Finite (univ : Set (Set ι)))).subset
  rintro ⟨d, J⟩ ⟨y, hy, hyd⟩
  refine ⟨?_, mem_univ _⟩
  intro i
  have hb := ceiling_bounds_of_mem_closedCell f e I hy i
  have he := ceil_eq_of_mem_cell f d J hyd i
  simpa only [ceilingVector, he, mem_Icc] using hb

section LocalFiniteness

variable [Finite ι] [TopologicalSpace E]

/-- The periodic hyperplane cells are locally finite in the actual topology.
This is a finite-label bound in a neighborhood, not a compactness assumption. -/
theorem closedCells_locallyFinite (f : ι → E →ₗ[ℝ] ℝ)
    (hf : ∀ i, Continuous (f i)) :
    LocallyFinite (fun p : (ι → ℤ) × Set ι => closedCell f p.1 p.2) := by
  intro x
  let U : Set E := {y | ∀ i, f i x - 1 < f i y ∧ f i y < f i x + 1}
  have hU : IsOpen U := by
    simp only [U, Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i =>
      (isOpen_lt continuous_const (hf i)).inter (isOpen_lt (hf i) continuous_const)
  have hxU : x ∈ U := fun i => by constructor <;> linarith
  refine ⟨U, hU.mem_nhds hxU, ?_⟩
  have hbox : Set.Finite {e : ι → ℤ | ∀ i,
      e i ∈ Icc (⌈f i x⌉ - 2) (⌈f i x⌉ + 2)} :=
    Set.Finite.pi' fun i => Set.finite_Icc (⌈f i x⌉ - 2) (⌈f i x⌉ + 2)
  apply (hbox.prod (Set.finite_univ : Set.Finite (univ : Set (Set ι)))).subset
  rintro ⟨e, I⟩ ⟨y, hy, hyU⟩
  refine ⟨?_, mem_univ _⟩
  intro i
  have hnear := hyU i
  have hcell := hy i
  have hbounds : (e i : ℝ)-1 ≤ f i y ∧ f i y ≤ (e i : ℝ) := by
    by_cases hi : i ∈ I
    · simp only [ite_eq_left hi] at hcell
      rw [hcell]
      constructor <;> linarith
    · simpa only [ite_eq_right hi] using hcell
  have hceil := Int.le_ceil (f i x)
  have hceil' := Int.ceil_lt_add_one (f i x)
  constructor
  · apply (Int.cast_le (R := ℝ)).mp
    simp only [Int.cast_sub, Int.cast_add, Int.cast_ofNat]
    linarith
  · apply (Int.cast_le (R := ℝ)).mp
    simp only [Int.cast_sub, Int.cast_add, Int.cast_ofNat]
    linarith

/-- The actual closed cells detect closed sets, the weak-topology axiom of
the CW structure. Local finiteness is proved above from the forms. -/
theorem isClosed_of_closedCell_intersections (f : ι → E →ₗ[ℝ] ℝ)
    (hf : ∀ i, Continuous (f i)) (A : Set E)
    (hA : ∀ e I, IsClosed (A ∩ closedCell f e I)) : IsClosed A := by
  have heq : (⋃ p : (ι → ℤ) × Set ι, A ∩ closedCell f p.1 p.2) = A := by
    apply Subset.antisymm
    · exact iUnion_subset fun _ => inter_subset_left
    · intro x hx
      exact mem_iUnion.mpr ⟨(ceilingVector f x, integralIndices f x), hx,
        cell_subset_closedCell f _ _ (mem_cell_self f x)⟩
  rw [← heq]
  apply ((closedCells_locallyFinite f hf).subset
    (fun _ => inter_subset_right)).isClosed_iUnion
  exact fun p => hA p.1 p.2

end LocalFiniteness

end ToricPower.IntegralArrangement

end
end ArrangementSource1
end ArrangementCellsBundleSource

section ArrangementNormalsBundleSource
/-!
# Normal spaces of the literal arrangement strata

The normal space is the linear span of the active forms.  The tangent
space is its annihilator, and in finite dimension the normal space is
exactly the annihilator of the tangent space.  These identities justify
the normal-space interpretation used in the maximal-stratum argument.

Candidate source until ordinary compilation succeeds.
-/


namespace ToricPower.IntegralArrangement

open Set Module

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E]

/-- The actual span of the equations active along a cell. -/
def cellNormal (f : ι → E →ₗ[ℝ] ℝ) (I : Set ι) : Submodule ℝ (Module.Dual ℝ E) :=
  Submodule.span ℝ (f '' I)

/-- A direction belongs to the stratum exactly when every active normal
form annihilates it. -/
theorem cellDirection_eq_dualCoannihilator (f : ι → E →ₗ[ℝ] ℝ) (I : Set ι) :
    cellDirection f I = (cellNormal f I).dualCoannihilator := by
  apply SetLike.coe_injective
  rw [cellNormal, Submodule.coe_dualCoannihilator_span]
  ext v
  simp only [SetLike.mem_coe, mem_cellDirection, Set.mem_ofPred_eq,
    Set.forall_mem_image]

/-- No further normal directions appear in finite dimension. -/
theorem cellDirection_dualAnnihilator [FiniteDimensional ℝ E]
    (f : ι → E →ₗ[ℝ] ℝ) (I : Set ι) :
    (cellDirection f I).dualAnnihilator = cellNormal f I := by
  rw [cellDirection_eq_dualCoannihilator]
  exact Subspace.dualCoannihilator_dualAnnihilator_eq

/-- The normal dimension is the actual codimension of the stratum. -/
theorem finrank_cellDirection_add_cellNormal [FiniteDimensional ℝ E]
    (f : ι → E →ₗ[ℝ] ℝ) (I : Set ι) :
    Module.finrank ℝ (cellDirection f I) + Module.finrank ℝ (cellNormal f I) =
      Module.finrank ℝ E := by
  rw [← cellDirection_dualAnnihilator]
  exact Subspace.finrank_add_finrank_dualAnnihilator_eq _

/-- Every cone generated by active forms lies in the actual normal space.
This is the containment used before the finite fan-cover argument. -/
theorem hull_le_cellNormal (f : ι → E →ₗ[ℝ] ℝ) {I J : Set ι} (hJI : J ⊆ I) :
    PointedCone.hull ℝ (f '' J) ≤ (cellNormal f I : PointedCone ℝ (Module.Dual ℝ E)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, hi, rfl⟩
  exact Submodule.subset_span ⟨i, hJI hi, rfl⟩

end ToricPower.IntegralArrangement
end ArrangementNormalsBundleSource

section LocalStrataBundleSource
/-!
# The local slice at a maximal support stratum

This file proves the arrangement-geometric part of Lemma 3.1.  The cells
are the literal integral hyperplane cells from `IntegralArrangement.cell`.
Around a point `x` we construct an open neighborhood meeting only cells
whose closures contain `x`.  The original cell in this neighborhood is
exactly the affine translate of its direction space.  Consequently data
supported in strata of at most its dimension vanish off that affine slice.

The last assertion concerns support of cellwise data; it does not assert
the microlocal support condition or replace the sheaf-model equivalence.
-/


attribute [local instance] Classical.propDecidable

open Set

namespace ToricPower.IntegralArrangement

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E]

/-- The open star cut out by the two nearest integral hyperplanes, with
both adjacent intervals retained when `x` lies on an integral hyperplane. -/
def localStar (f : ι → E →ₗ[ℝ] ℝ) (x : E) : Set E :=
  {y | ∀ i,
    (⌈f i x⌉ : ℝ) - 1 < f i y ∧
      f i y < (⌈f i x⌉ : ℝ) +
        (if f i x = (⌈f i x⌉ : ℝ) then 1 else 0)}

theorem mem_localStar_self (f : ι → E →ₗ[ℝ] ℝ) (x : E) :
    x ∈ localStar f x := by
  intro i
  constructor
  · linarith [Int.ceil_lt_add_one (f i x)]
  · by_cases hi : f i x = (⌈f i x⌉ : ℝ)
    · simp only [ite_eq_left hi]
      linarith
    · simp only [ite_eq_right hi, add_zero]
      exact lt_of_le_of_ne (Int.le_ceil (f i x)) hi

/-- The literal open star is convex, not merely locally contractible. -/
theorem localStar_convex (f : ι → E →ₗ[ℝ] ℝ) (x : E) :
    Convex ℝ (localStar f x) := by
  simp only [localStar, Set.setOf_forall]
  exact convex_iInter fun i =>
    ((convex_Ioi ((⌈f i x⌉ : ℝ) - 1)).linear_preimage (f i)).inter
      ((convex_Iio ((⌈f i x⌉ : ℝ) +
        (if f i x = (⌈f i x⌉ : ℝ) then 1 else 0))).linear_preimage (f i))

/-- The neighborhood is open for any finite collection of continuous forms. -/
theorem localStar_isOpen [TopologicalSpace E] [Finite ι]
    (f : ι → E →ₗ[ℝ] ℝ) (hf : ∀ i, Continuous (f i)) (x : E) :
    IsOpen (localStar f x) := by
  simp only [localStar, Set.setOf_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact (isOpen_lt continuous_const (hf i)).inter
    (isOpen_lt (hf i) continuous_const)

/-- If `x` is not on the `i`th hyperplane, its integral interval cannot
change inside the local star. -/
theorem localStar_ceil_eq_of_not_integral
    (f : ι → E →ₗ[ℝ] ℝ) (x : E) {y : E}
    (hy : y ∈ localStar f x) {i : ι}
    (hi : i ∉ integralIndices f x) : ⌈f i y⌉ = ⌈f i x⌉ := by
  have hi' : f i x ≠ (⌈f i x⌉ : ℝ) := hi
  have h := hy i
  simp only [ite_eq_right hi', add_zero] at h
  exact Int.ceil_eq_iff.mpr ⟨h.1, h.2.le⟩

/-- Every cell meeting the local star has `x` in its closure.  This is
proved from the integral inequalities, without an abstract frontier axiom. -/
theorem localStar_point_mem_closedCell
    (f : ι → E →ₗ[ℝ] ℝ) (x : E) {y : E}
    (hy : y ∈ localStar f x) :
    x ∈ closedCell f (ceilingVector f y) (integralIndices f y) := by
  intro i
  have h := hy i
  by_cases hxi : f i x = (⌈f i x⌉ : ℝ)
  · simp only [ite_eq_left hxi] at h
    have hceil : ⌈f i x⌉ ≤ ⌈f i y⌉ ∧ ⌈f i y⌉ ≤ ⌈f i x⌉ + 1 := by
      constructor
      · exact Int.le_ceil_iff.mpr h.1
      · apply Int.ceil_le.mpr
        simpa only [Int.cast_add, Int.cast_one] using h.2.le
    by_cases hyi : i ∈ integralIndices f y
    · simp only [ite_eq_left hyi, ceilingVector]
      have hyi' : f i y = (⌈f i y⌉ : ℝ) := hyi
      have he : ⌈f i y⌉ = ⌈f i x⌉ := by
        have hu : ⌈f i y⌉ < ⌈f i x⌉ + 1 := by
          exact_mod_cast (hyi' ▸ h.2)
        omega
      rw [he, ← hxi]
    · simp only [ite_eq_right hyi, ceilingVector]
      constructor
      · have hc : (⌈f i y⌉ : ℝ) ≤ (⌈f i x⌉ : ℝ) + 1 := by
          exact_mod_cast hceil.2
        linarith
      · have hc : (⌈f i x⌉ : ℝ) ≤ (⌈f i y⌉ : ℝ) := by
          exact_mod_cast hceil.1
        exact hxi.le.trans hc
  · have hni : i ∉ integralIndices f x := hxi
    have he := localStar_ceil_eq_of_not_integral f x hy hni
    have hny : i ∉ integralIndices f y := by
      intro hiy
      have hiy' : f i y = (⌈f i y⌉ : ℝ) := hiy
      simp only [ite_eq_right hxi, add_zero] at h
      rw [he] at hiy'
      linarith
    simp only [ite_eq_right hny, ceilingVector, he]
    exact ⟨by linarith [Int.ceil_lt_add_one (f i x)], Int.le_ceil (f i x)⟩

/-- In this neighborhood the stratum is precisely the affine tangent
slice, with no additional open inequalities left to impose. -/
theorem localStar_mem_cell_iff
    (f : ι → E →ₗ[ℝ] ℝ) (x : E) {y : E}
    (hy : y ∈ localStar f x) :
    y ∈ cell f (ceilingVector f x) (integralIndices f x) ↔
      y - x ∈ cellDirection f (integralIndices f x) := by
  constructor
  · intro hcell
    exact sub_mem_cellDirection f _ _
      (cell_subset_closedCell f _ _ (mem_cell_self f x))
      (cell_subset_closedCell f _ _ hcell)
  · intro hv i
    rw [mem_cellDirection] at hv
    by_cases hi : i ∈ integralIndices f x
    · simp only [ite_eq_left hi, ceilingVector]
      have hx : f i x = (⌈f i x⌉ : ℝ) := hi
      have hz := hv i hi
      rw [map_sub] at hz
      linarith
    · simp only [ite_eq_right hi, ceilingVector]
      have hi' : f i x ≠ (⌈f i x⌉ : ℝ) := hi
      simpa only [ite_eq_right hi', add_zero] using hy i

/-- Every distinct incident stratum has strictly larger dimension. -/
theorem localStar_dimension_lt [FiniteDimensional ℝ E]
    (f : ι → E →ₗ[ℝ] ℝ) (x : E) {y : E}
    (hy : y ∈ localStar f x)
    (hne : y ∉ cell f (ceilingVector f x) (integralIndices f x)) :
    Module.finrank ℝ (cellDirection f (integralIndices f x)) <
      Module.finrank ℝ (cellDirection f (integralIndices f y)) := by
  have hxcl := localStar_point_mem_closedCell f x hy
  have hxn : x ∉ cell f (ceilingVector f y) (integralIndices f y) := by
    intro hxc
    obtain ⟨he, hI⟩ := cell_indices_unique f (mem_cell_self f x) hxc
    exact hne (by simpa only [he, hI] using mem_cell_self f y)
  exact boundary_finrank_lt f _ _ (mem_cell_self f y) hxcl hxn

/-- The bounded range of cell dimensions produces a maximal nonzero
stratum; no finiteness condition on the possible values of `F` is needed. -/
theorem exists_maximal_support_point [FiniteDimensional ℝ E]
    {C : Type*} [Zero C] (f : ι → E →ₗ[ℝ] ℝ) (F : E → C)
    (hne : ∃ x, F x ≠ 0) :
    ∃ x, F x ≠ 0 ∧ ∀ y, F y ≠ 0 →
      Module.finrank ℝ (cellDirection f (integralIndices f y)) ≤
        Module.finrank ℝ (cellDirection f (integralIndices f x)) := by
  classical
  let P : ℕ → Prop := fun d => ∃ x, F x ≠ 0 ∧
    Module.finrank ℝ (cellDirection f (integralIndices f x)) = d
  obtain ⟨x₀, hx₀⟩ := hne
  have hmax : P (Nat.findGreatest P (Module.finrank ℝ E)) :=
    Nat.findGreatest_spec (Submodule.finrank_le _) ⟨x₀, hx₀, rfl⟩
  obtain ⟨x, hx, hdim⟩ := hmax
  refine ⟨x, hx, fun y hy => ?_⟩
  rw [hdim]
  exact Nat.le_findGreatest (Submodule.finrank_le _) ⟨y, hy, rfl⟩

/-- For data whose nonzero strata have dimension no larger than the
stratum of `x`, the local support lies on the actual affine tangent slice. -/
theorem maximal_support_vanishes_off_slice [FiniteDimensional ℝ E]
    {C : Type*} [Zero C] (f : ι → E →ₗ[ℝ] ℝ) (F : E → C) (x : E)
    (hmax : ∀ y, F y ≠ 0 →
      Module.finrank ℝ (cellDirection f (integralIndices f y)) ≤
        Module.finrank ℝ (cellDirection f (integralIndices f x)))
    {y : E} (hy : y ∈ localStar f x)
    (hoff : y - x ∉ cellDirection f (integralIndices f x)) : F y = 0 := by
  by_contra hnonzero
  have hne : y ∉ cell f (ceilingVector f x) (integralIndices f x) := by
    intro hmem
    exact hoff ((localStar_mem_cell_iff f x hy).mp hmem)
  exact (not_lt_of_ge (hmax y hnonzero)) (localStar_dimension_lt f x hy hne)

end ToricPower.IntegralArrangement
end LocalStrataBundleSource

section NormalFanBundleSource
/-!
# A normal-space cover forces a linear subfan

This proves the fan-theoretic implication in Lemma 3.1.  The hypothesis
is an actual covering of a vector subspace by cones of the given fan
contained in that subspace.  The conclusion uses actual intersections
of cones, rather than a newly introduced predicate asserting a detector.

The proof uses a finite-sum argument for faces.  It therefore needs no
choice of a relative-interior point and no dimension assumption.
-/


open Set

namespace ToricPower

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A subcone covered by finitely many faces of one cone is contained
in one of those faces.  A sum of one counterexample for each face would
otherwise belong to none of them. -/
theorem subcone_le_of_finite_face_cover {ι : Type*} [Finite ι]
    (C S : PointedCone ℝ V) (F : ι → PointedCone ℝ V)
    (hSC : S ≤ C) (hface : ∀ i, (F i).IsFaceOf C)
    (hcover : ∀ x ∈ S, ∃ i, x ∈ F i) : ∃ i, S ≤ F i := by
  classical
  letI := Fintype.ofFinite ι
  by_contra hnone
  have hw : ∀ i, ∃ x, x ∈ S ∧ x ∉ F i := by
    intro i
    by_contra! h
    exact hnone ⟨i, h⟩
  choose x hxS hxF using hw
  have hs : (∑ i, x i) ∈ S := S.sum_mem (fun i _ => hxS i)
  obtain ⟨i, hi⟩ := hcover _ hs
  exact hxF i ((hface i).mem_of_sum_mem (fun j => hSC (hxS j)) hi i)

namespace NormalFan

open TauCeti.Toric

variable {N : Type*} [AddCommGroup N] {i : N →+ V}

/-- The literal linearity condition from the paper: intersection with
the subspace must already be a cone of the original fan. -/
def IsLinearSubspace (Φ : Fan i) (W : Submodule ℝ V) : Prop :=
  ∀ σ ∈ Φ.cones, σ ⊓ (W : PointedCone ℝ V) ∈ Φ.cones

/-- The intersection with `W` is the intersection with a single cone
contained in `W`, hence a face of `σ`. -/
theorem intersection_eq_of_cone_cover (Φ : Fan i) (W : Submodule ℝ V)
    (hcover : ∀ x ∈ W,
      ∃ η ∈ Φ.cones, η ≤ (W : PointedCone ℝ V) ∧ x ∈ η)
    {σ : PointedCone ℝ V} (hσ : σ ∈ Φ.cones) :
    ∃ η ∈ Φ.cones, η ≤ (W : PointedCone ℝ V) ∧
      σ ⊓ (W : PointedCone ℝ V) = σ ⊓ η := by
  classical
  letI : Fintype Φ.cones := Φ.finite_cones.fintype
  let I := {η : Φ.cones // η.val ≤ (W : PointedCone ℝ V)}
  let F : I → PointedCone ℝ V := fun η => σ ⊓ η.val.val
  have hf : ∀ η : I, (F η).IsFaceOf σ :=
    fun η => Φ.inf_isFaceOf_left hσ η.val.property
  have hc : ∀ x ∈ σ ⊓ (W : PointedCone ℝ V), ∃ η : I, x ∈ F η := by
    intro x hx
    obtain ⟨η, hη, hηW, hxη⟩ := hcover x hx.2
    exact ⟨⟨⟨η, hη⟩, hηW⟩, hx.1, hxη⟩
  obtain ⟨η, hle⟩ := subcone_le_of_finite_face_cover σ
    (σ ⊓ (W : PointedCone ℝ V)) F inf_le_left hf hc
  exact ⟨η.val.val, η.val.property, η.property,
    le_antisymm hle (inf_le_inf_left σ η.property)⟩

/-- The complete normal-space cover in Lemma 3.1 gives the required
linear subspace, for every finite fan and in every ambient dimension. -/
theorem isLinearSubspace_of_cone_cover (Φ : Fan i) (W : Submodule ℝ V)
    (hcover : ∀ x ∈ W,
      ∃ η ∈ Φ.cones, η ≤ (W : PointedCone ℝ V) ∧ x ∈ η) :
    IsLinearSubspace Φ W := by
  intro σ hσ
  obtain ⟨η, hη, _, heq⟩ := intersection_eq_of_cone_cover Φ W hcover hσ
  rw [heq]
  exact Φ.inf_mem hσ hη

end NormalFan

end ToricPower
end NormalFanBundleSource

section NormalFanSpanBundleSource
/-!
# A cone of full normal span

The last step of Lemma 3.1 uses that finitely many proper real linear
subspaces cannot cover a vector space.  This file derives that fact from
the existing Baire theorem for finite-dimensional normed spaces, then
applies it to the actual linear spans of a finite cone cover.
-/


open Set

namespace ToricPower

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Finite ι]

theorem exists_eq_top_of_finite_submodule_cover
    (S : ι → Submodule ℝ V) (hcover : ∀ x : V, ∃ i, x ∈ S i) :
    ∃ i, S i = ⊤ := by
  classical
  by_contra! hproper
  have hi : ∀ i, interior (S i : Set V) = ∅ := by
    intro i
    apply Set.not_nonempty_iff_eq_empty.mp
    intro hne
    exact hproper i ((S i).eq_top_of_nonempty_interior' hne)
  have hd : Dense (⋂ i, (S i : Set V)ᶜ) :=
    dense_iInter_of_isOpen (fun i => (S i).closed_of_finiteDimensional.isOpen_compl)
      (fun i => interior_eq_empty_iff_dense_compl.mp (hi i))
  obtain ⟨x, hx⟩ := hd.nonempty
  obtain ⟨i, hxi⟩ := hcover x
  exact Set.mem_iInter.mp hx i hxi

/-- One of finitely many cones covering a subspace has that full span.
No condition about dimensions is included in the hypotheses. -/
theorem exists_cone_span_eq_of_finite_cover
    (W : Submodule ℝ V) (C : ι → PointedCone ℝ V)
    (hle : ∀ i, C i ≤ (W : PointedCone ℝ V))
    (hcover : ∀ x ∈ W, ∃ i, x ∈ C i) :
    ∃ i, Submodule.span ℝ (C i : Set V) = W := by
  classical
  let S : ι → Submodule ℝ W := fun i =>
    (Submodule.span ℝ (C i : Set V)).comap W.subtype
  have hcov : ∀ x : W, ∃ i, x ∈ S i := by
    intro x
    obtain ⟨i, hi⟩ := hcover x.val x.property
    exact ⟨i, Submodule.subset_span hi⟩
  obtain ⟨i, hi⟩ := exists_eq_top_of_finite_submodule_cover S hcov
  refine ⟨i, le_antisymm (Submodule.span_le.mpr (hle i)) ?_⟩
  intro x hx
  have hmem : (⟨x, hx⟩ : W) ∈ S i := by rw [hi]; trivial
  exact hmem

namespace NormalFan

open TauCeti.Toric

variable {N : Type*} [AddCommGroup N] {i : N →+ V}

/-- A fan cover of the normal space contains a cone of its full span.
This specifies an actual cone of the given fan. -/
theorem exists_full_span_cone_of_cover (Φ : Fan i) (W : Submodule ℝ V)
    (hcover : ∀ x ∈ W,
      ∃ σ ∈ Φ.cones, σ ≤ (W : PointedCone ℝ V) ∧ x ∈ σ) :
    ∃ σ ∈ Φ.cones, σ ≤ (W : PointedCone ℝ V) ∧
      Submodule.span ℝ (σ : Set V) = W := by
  classical
  let J := {σ : Φ.cones // σ.val ≤ (W : PointedCone ℝ V)}
  let F : J → PointedCone ℝ V := fun σ => σ.val.val
  have hc : ∀ x ∈ W, ∃ σ : J, x ∈ F σ := by
    intro x hx
    obtain ⟨σ, hσ, hσW, hxσ⟩ := hcover x hx
    exact ⟨⟨⟨σ, hσ⟩, hσW⟩, hxσ⟩
  obtain ⟨σ, hspan⟩ := exists_cone_span_eq_of_finite_cover W F
    (fun σ => σ.property) hc
  exact ⟨σ.val.val, σ.val.property, σ.property, hspan⟩

/-- The same cover proves rationality by exhibiting finitely many actual
lattice vectors spanning the normal space. -/
theorem exists_finite_lattice_span_of_cover (Φ : Fan i) (W : Submodule ℝ V)
    (hcover : ∀ x ∈ W,
      ∃ σ ∈ Φ.cones, σ ≤ (W : PointedCone ℝ V) ∧ x ∈ σ) :
    ∃ s : Finset N, W = Submodule.span ℝ (i '' (s : Set N)) := by
  obtain ⟨σ, hσ, _, hspan⟩ := exists_full_span_cone_of_cover Φ W hcover
  obtain ⟨s, hs⟩ := (isLatticeRational_iff).mp (Φ.isToricCone hσ).rational
  refine ⟨s, ?_⟩
  rw [← hspan, hs]
  apply le_antisymm
  · exact Submodule.span_le.mpr (PointedCone.hull_le_span ℝ (i '' (s : Set N)))
  · exact Submodule.span_mono PointedCone.subset_hull

end NormalFan

end ToricPower
end NormalFanSpanBundleSource

section NormalSeparationBundleSource
/-!
# Strict separation from a polyhedral normal cone

The local Morse calculation needs one vector satisfying all the strict
interior inequalities as well as a prescribed positive covector inequality.
This is proved from the finite Gordan alternative, with no analytic
separation theorem or unverified acyclicity hypothesis.
-/


namespace ToricPower.LocalMorse

open Module Set

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]

/-- Outside the negative cone of the active forms there is a direction
strictly positive for the proposed covector and every active form.
The given strict interior point is exactly the nonemptiness condition
for the corresponding open polyhedron near a face. -/
theorem exists_common_positive_direction
    (f : ι → Module.Dual ℝ E) (ξ : Module.Dual ℝ E)
    (hint : ∃ w : E, ∀ i, 0 < f i w)
    (hout : -ξ ∉ PointedCone.hull ℝ (Set.range f)) :
    ∃ v : E, (∀ i, 0 < f i v) ∧ 0 < ξ v := by
  classical
  obtain ⟨w, hw⟩ := hint
  let a : Option ι → Module.Dual ℝ E := Option.elim' ξ f
  have hfrel : ∀ c : ι → ℝ, 0 ≤ c → ∑ i, c i • f i = 0 → c = 0 :=
    (TauCeti.exists_forall_dual_pos_iff f).mp ⟨Module.Dual.eval ℝ E w, hw⟩
  have hrel : ∀ c : Option ι → ℝ,
      0 ≤ c → ∑ j, c j • a j = 0 → c = 0 := by
    intro c hc hsum
    have hs : c none • ξ + ∑ i, c (some i) • f i = 0 := by
      simpa only [Fintype.sum_option, a, Option.elim'_none, Option.elim'_some] using hsum
    have hnone : c none = 0 := by
      by_contra hn
      have hp : 0 < c none := lt_of_le_of_ne (hc none) (Ne.symm hn)
      let C : PointedCone ℝ (Module.Dual ℝ E) := PointedCone.hull ℝ (Set.range f)
      have hmem : (∑ i, c (some i) • f i) ∈ C :=
        C.sum_mem fun i _ => C.smul_mem (hc (some i)) (PointedCone.subset_hull ⟨i, rfl⟩)
      have he : (∑ i, c (some i) • f i) = -(c none • ξ) := by
        exact eq_neg_of_add_eq_zero_right hs
      have hscaled := C.smul_mem (inv_nonneg.mpr (hc none)) hmem
      rw [he, smul_neg, smul_smul, inv_mul_cancel₀ hp.ne', one_smul] at hscaled
      exact hout hscaled
    have hrest : (fun i => c (some i)) = 0 := by
      apply hfrel _ (fun i => hc (some i))
      simpa only [hnone, zero_smul, zero_add] using hs
    funext j
    cases j with
    | none => exact hnone
    | some i => exact congrFun hrest i
  obtain ⟨y, hy⟩ := (TauCeti.exists_forall_dual_pos_iff a).mpr hrel
  refine ⟨(Module.evalEquiv ℝ E).symm y, ?_, ?_⟩
  · intro i
    simpa only [Module.apply_evalEquiv_symm_apply, a, Option.elim'_some] using hy (some i)
  · simpa only [Module.apply_evalEquiv_symm_apply, a, Option.elim'_none] using hy none

end ToricPower.LocalMorse
end NormalSeparationBundleSource

section LocalMorseConeBundleSource
/-!
# The excluded-region inclusion outside a polyhedral normal cone

This is the complete elementary topological calculation used for an affine
costandard cone in Appendix A.2.  The hypotheses concern only the actual
linear inequalities, their strict feasibility, the covector, and an open
convex neighborhood.  Strict separation supplies a common star center in
that neighborhood, and the explicit radial homotopies identify the literal
inclusion with a homotopy equivalence.

The later comparison with local sheaf cochains is a separate obligation;
this file does not define local acyclicity by assumption.
-/


namespace ToricPower.LocalMorse

open Set

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every vector has a sufficiently small negative multiple in any open
neighborhood of the origin.  The scalar is strictly positive. -/
theorem exists_negative_smul_mem {B : Set E} (hB : IsOpen B) (hzero : (0 : E) ∈ B)
    (v : E) : ∃ t : ℝ, 0 < t ∧ (-t) • v ∈ B := by
  have hc : Continuous (fun t : ℝ => (-t) • v) := by fun_prop
  have hopen : IsOpen ((fun t : ℝ => (-t) • v) ⁻¹' B) := hB.preimage hc
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 (by simpa using hzero)
  refine ⟨ε / 2, half_pos hε, hball ?_⟩
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    using half_lt_self hε

/-- Every nonzero real linear form is positive in some direction. -/
theorem exists_positive_direction (ξ : Module.Dual ℝ E) (hξ : ξ ≠ 0) :
    ∃ v : E, 0 < ξ v := by
  classical
  have hx : ∃ x : E, ξ x ≠ 0 := by
    by_contra! h
    apply hξ
    ext x
    exact h x
  obtain ⟨x, hx⟩ := hx
  obtain hneg | hpos := lt_or_gt_of_ne hx
  · exact ⟨-x, by simpa only [map_neg] using neg_pos.mpr hneg⟩
  · exact ⟨x, hpos⟩

/-- In the interior case, the negative half-neighborhood itself is
contractible for every nonzero covector.  This is the separate geometric
input for the locally constant sheaf calculation. -/
theorem negativeHalf_contractible_of_ne_zero
    {B : Set E} (hconv : Convex ℝ B) (hB : IsOpen B) (hzero : (0 : E) ∈ B)
    (ξ : Module.Dual ℝ E) (hξ : ξ ≠ 0) : ContractibleSpace (negativeHalf B ξ) := by
  obtain ⟨v, hv⟩ := exists_positive_direction ξ hξ
  obtain ⟨t, ht, htp⟩ := exists_negative_smul_mem hB hzero v
  apply negativeHalf_contractible hconv ξ htp
  rw [map_smul, smul_eq_mul]
  exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr ht) hv

/-- Outside the negative normal cone, the actual excluded-region inclusion
is a homotopy equivalence.  The equality on underlying points specifies
that this is the inclusion map, not merely an unrelated equivalence of
contractible spaces. -/
theorem exists_excludedRegion_inclusion_homotopyEquiv
    [FiniteDimensional ℝ E] [Fintype ι] [Nonempty ι]
    {B : Set E} (hconv : Convex ℝ B) (hB : IsOpen B) (hzero : (0 : E) ∈ B)
    (f : ι → Module.Dual ℝ E) (ξ : Module.Dual ℝ E)
    (hint : ∃ w : E, ∀ i, 0 < f i w)
    (hout : -ξ ∉ PointedCone.hull ℝ (Set.range f)) :
    ∃ e : ContinuousMap.HomotopyEquiv (excludedRegion B ξ f) (negativeHalf B ξ),
      ∀ x, (e x).val = x.val := by
  obtain ⟨v, hv, hξv⟩ := exists_common_positive_direction f ξ hint hout
  obtain ⟨t, ht, htp⟩ := exists_negative_smul_mem hB hzero v
  have hpξ : ξ ((-t) • v) < 0 := by
    rw [map_smul, smul_eq_mul]
    exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr ht) hξv
  have hpf : ∀ i, f i ((-t) • v) ≤ 0 := by
    intro i
    rw [map_smul, smul_eq_mul]
    exact (mul_neg_of_neg_of_pos (neg_lt_zero.mpr ht) (hv i)).le
  exact ⟨excludedRegionInclusionHomotopyEquiv hconv ξ f htp hpξ hpf, fun _ => rfl⟩

end ToricPower.LocalMorse
end LocalMorseConeBundleSource

section LocalMorseChainsBundleSource
/-!
# The actual singular-chain calculation for the local Morse region

The excluded-region inclusion is carried by the singular-chain functor to
an explicit chain homotopy equivalence.  Thus this file proves more than
equality of homology dimensions: the particular inclusion has an actual
chain inverse up to homotopy.  This is the coefficient-independent
topological input to the local cochain calculation.

The comparison from cellular sheaf sections to this relative-chain model
is a separate mathematical obligation; it is not assumed here.

Candidate source until ordinary compilation succeeds.
-/


open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace ToricPower.LocalMorse

universe w v u

section SingularChains

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  {X Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]

/-- A literal topological homotopy equivalence induces a chain homotopy
equivalence on the actual singular chains with arbitrary coefficients. -/
def singularChainHomotopyEquiv (e : ContinuousMap.HomotopyEquiv X Y) (M : C) :
    _root_.HomotopyEquiv
      (((singularChainComplexFunctor C).obj M).obj (TopCat.of X))
      (((singularChainComplexFunctor C).obj M).obj (TopCat.of Y)) where
  hom := ((singularChainComplexFunctor C).obj M).map (TopCat.ofHom e.toFun)
  inv := ((singularChainComplexFunctor C).obj M).map (TopCat.ofHom e.invFun)
  homotopyHomInvId := by
    let H : TopCat.Homotopy
        (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun) (𝟙 (TopCat.of X)) :=
      e.left_inv.some
    have h := H.singularChainComplexFunctorObjMap M
    rw [Functor.map_comp] at h
    exact h.trans (Homotopy.ofEq (((singularChainComplexFunctor C).obj M).map_id _))
  homotopyInvHomId := by
    let H : TopCat.Homotopy
        (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun) (𝟙 (TopCat.of Y)) :=
      e.right_inv.some
    have h := H.singularChainComplexFunctorObjMap M
    rw [Functor.map_comp] at h
    exact h.trans (Homotopy.ofEq (((singularChainComplexFunctor C).obj M).map_id _))

end SingularChains

section ExcludedRegion

variable {E : Type w} {ι : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
  {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

/-- The actual continuous inclusion used by the relative local model. -/
def excludedRegionInclusion (B : Set E) (ξ : E →ₗ[ℝ] ℝ)
    (f : ι → E →ₗ[ℝ] ℝ) : C(excludedRegion B ξ f, negativeHalf B ξ) :=
  ⟨fun x => ⟨x.val, x.property.1⟩, by fun_prop⟩

/-- The explicit common-center contraction gives a chain inverse to the
particular excluded-region inclusion, with arbitrary coefficient objects. -/
def excludedRegionSingularChainHomotopyEquiv [Nonempty ι]
    {B : Set E} (hB : Convex ℝ B) (ξ : E →ₗ[ℝ] ℝ)
    (f : ι → E →ₗ[ℝ] ℝ) {p : E}
    (hpB : p ∈ B) (hpξ : ξ p < 0) (hpf : ∀ i, f i p ≤ 0) (M : C) :
    _root_.HomotopyEquiv
      (((singularChainComplexFunctor C).obj M).obj
        (TopCat.of (excludedRegion B ξ f)))
      (((singularChainComplexFunctor C).obj M).obj
        (TopCat.of (negativeHalf B ξ))) :=
  singularChainHomotopyEquiv
    (excludedRegionInclusionHomotopyEquiv hB ξ f hpB hpξ hpf) M

/-- The forward map of the chain equivalence is the singular-chain map of
the inclusion itself. -/
@[simp]
theorem excludedRegionSingularChainHomotopyEquiv_hom [Nonempty ι]
    {B : Set E} (hB : Convex ℝ B) (ξ : E →ₗ[ℝ] ℝ)
    (f : ι → E →ₗ[ℝ] ℝ) {p : E}
    (hpB : p ∈ B) (hpξ : ξ p < 0) (hpf : ∀ i, f i p ≤ 0) (M : C) :
    (excludedRegionSingularChainHomotopyEquiv hB ξ f hpB hpξ hpf M).hom =
      ((singularChainComplexFunctor C).obj M).map
        (TopCat.ofHom (excludedRegionInclusion B ξ f)) := rfl

/-- In a category with homology, the particular inclusion induces a
quasi-isomorphism of singular chains. -/
theorem excludedRegionInclusion_singularChain_quasiIso
    [CategoryWithHomology C] [Nonempty ι]
    {B : Set E} (hB : Convex ℝ B) (ξ : E →ₗ[ℝ] ℝ)
    (f : ι → E →ₗ[ℝ] ℝ) {p : E}
    (hpB : p ∈ B) (hpξ : ξ p < 0) (hpf : ∀ i, f i p ≤ 0) (M : C) :
    QuasiIso (((singularChainComplexFunctor C).obj M).map
      (TopCat.ofHom (excludedRegionInclusion B ξ f))) := by
  change QuasiIso
    (excludedRegionSingularChainHomotopyEquiv hB ξ f hpB hpξ hpf M).hom
  infer_instance

end ExcludedRegion

end ToricPower.LocalMorse
end LocalMorseChainsBundleSource
