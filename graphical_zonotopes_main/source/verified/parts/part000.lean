module

public import Aesop
public import Lean.Elab.Command
public import Lean.Elab.Tactic.Omega
public import Lean.Meta.Basic
public import Lean.PrettyPrinter
public import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.Graph.Delete
public import Mathlib.Combinatorics.Graph.Maps
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.Graph.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Sigma.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Order.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Order.Sum.Order
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Tauto
public import Mathlib.Topology.Algebra.Affine
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.UnitInterval

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section BundlePart0
/- Source: Papers/GraphicalZonotopes/SetFunction.lean -/
















@[expose] public section

/-! Real set functions, elemental differences, and their genuine lower base polytopes. -/

noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev SetFunction (V : Type*) := Finset V → ℝ

def Supermodular (z : SetFunction V) : Prop :=
  ∀ A B, z A + z B ≤ z (A ∪ B) + z (A ∩ B)

def Normalized (z : SetFunction V) : Prop := z ∅ = 0

def TranslationNormalized (z : SetFunction V) : Prop :=
  Normalized z ∧ ∀ v, z {v} = 0

def delta (z : SetFunction V) (u v : V) (S : Finset V) : ℝ :=
  z (insert u (insert v S)) - z (insert u S) - z (insert v S) + z S

def ElementallyNonnegative (z : SetFunction V) : Prop :=
  ∀ u v, u ≠ v → ∀ S, u ∉ S → v ∉ S → 0 ≤ delta z u v S

def subsetSum (x : V → ℝ) (S : Finset V) : ℝ := ∑ v ∈ S, x v

def basePolytope (z : SetFunction V) : Set (V → ℝ) :=
  {x | subsetSum x univ = z univ ∧ ∀ S, z S ≤ subsetSum x S}

@[simp] theorem subsetSum_empty (x : V → ℝ) : subsetSum x ∅ = 0 := by
  simp [subsetSum]

@[simp] theorem subsetSum_insert {x : V → ℝ} {v : V} {S : Finset V} (hv : v ∉ S) :
    subsetSum x (insert v S) = x v + subsetSum x S := by simp [subsetSum, hv]

@[simp] theorem subsetSum_add (x y : V → ℝ) (S : Finset V) :
    subsetSum (x + y) S = subsetSum x S + subsetSum y S := by
  simp [subsetSum, sum_add_distrib]

@[simp] theorem subsetSum_smul (a : ℝ) (x : V → ℝ) (S : Finset V) :
    subsetSum (a • x) S = a * subsetSum x S := by simp [subsetSum, mul_sum]

theorem Supermodular.marginal {z : SetFunction V} (hz : Supermodular z)
    {A B : Finset V} (hAB : A ⊆ B) {v : V} (hv : v ∉ B) :
    z (insert v A) - z A ≤ z (insert v B) - z B := by
  have hu : insert v A ∪ B = insert v B := by ext x; simp; aesop
  have hi : insert v A ∩ B = A := by ext x; simp; aesop
  have h := hz (insert v A) B
  rw [hu, hi] at h
  linarith

theorem Supermodular.elemental {z : SetFunction V} (hz : Supermodular z) :
    ElementallyNonnegative z := by
  intro u v huv S hu hv
  have h := hz.marginal (subset_insert v S) (show u ∉ insert v S by simp [huv, hu])
  dsimp [delta]
  linarith

theorem ElementallyNonnegative.marginal {z : SetFunction V}
    (hz : ElementallyNonnegative z) {A B : Finset V} (hAB : A ⊆ B)
    {v : V} (hv : v ∉ B) :
    z (insert v A) - z A ≤ z (insert v B) - z B := by
  classical
  have aux : ∀ D : Finset V, v ∉ A ∪ D →
      z (insert v A) - z A ≤ z (insert v (A ∪ D)) - z (A ∪ D) := by
    intro D
    induction D using Finset.induction_on with
    | empty => simp
    | @insert b D hb ih =>
      intro hvAD
      rw [union_insert] at hvAD ⊢
      have hvD : v ∉ A ∪ D := fun h => hvAD (mem_insert_of_mem h)
      have hvb : v ≠ b := by intro h; subst v; exact hvAD (mem_insert_self _ _)
      by_cases hbAD : b ∈ A ∪ D
      · simpa [insert_eq_of_mem hbAD] using ih hvD
      · have h1 := ih hvD
        have h2 := hz v b hvb (A ∪ D) hvD hbAD
        dsimp [delta] at h2
        linarith
  have he : A ∪ (B \ A) = B := union_sdiff_of_subset hAB
  simpa [he] using aux (B \ A) (by simpa [he] using hv)

theorem basePolytope_convex (z : SetFunction V) : Convex ℝ (basePolytope z) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_⟩
  · rw [subsetSum_add, subsetSum_smul, subsetSum_smul, hx.1, hy.1,
      ← add_mul, hab, one_mul]
  · intro S
    rw [subsetSum_add, subsetSum_smul, subsetSum_smul]
    have h1 := mul_le_mul_of_nonneg_left (hx.2 S) ha
    have h2 := mul_le_mul_of_nonneg_left (hy.2 S) hb
    have he : a * z S + b * z S = z S := by rw [← add_mul, hab, one_mul]
    linarith

def orderPrefix {n : ℕ} (e : Fin n ≃ V) (j : ℕ) : Finset V :=
  univ.filter (fun v => (e.symm v).val < j)

@[simp] theorem orderPrefix_zero {n : ℕ} (e : Fin n ≃ V) : orderPrefix e 0 = ∅ := by
  ext v; simp [orderPrefix]

@[simp] theorem orderPrefix_full {n : ℕ} (e : Fin n ≃ V) : orderPrefix e n = univ := by
  ext v; simp [orderPrefix, (e.symm v).isLt]

theorem orderPrefix_mono {n : ℕ} (e : Fin n ≃ V) : Monotone (orderPrefix e) := by
  intro j k hjk v hv
  exact mem_filter.mpr ⟨mem_univ _, lt_of_lt_of_le (mem_filter.mp hv).2 hjk⟩

@[simp] theorem not_mem_orderPrefix {n : ℕ} (e : Fin n ≃ V) (j : Fin n) :
    e j ∉ orderPrefix e j.val := by simp [orderPrefix]

theorem orderPrefix_succ {n : ℕ} (e : Fin n ≃ V) (j : Fin n) :
    orderPrefix e (j.val + 1) = insert (e j) (orderPrefix e j.val) := by
  ext v
  simp only [orderPrefix, mem_filter, mem_univ, true_and, mem_insert]
  constructor
  · intro h
    by_cases he : (e.symm v).val = j.val
    · left
      have hfin : e.symm v = j := Fin.ext he
      simpa using congrArg e hfin
    · right; omega
  · rintro (rfl | h)
    · simp
    · omega

def greedyPoint {n : ℕ} (z : SetFunction V) (e : Fin n ≃ V) (v : V) : ℝ :=
  z (orderPrefix e ((e.symm v).val + 1)) - z (orderPrefix e (e.symm v).val)

@[simp] theorem greedyPoint_apply {n : ℕ} (z : SetFunction V) (e : Fin n ≃ V)
    (j : Fin n) :
    greedyPoint z e (e j) = z (insert (e j) (orderPrefix e j.val)) -
      z (orderPrefix e j.val) := by simp [greedyPoint, orderPrefix_succ]

theorem greedyPoint_prefix {n : ℕ} (z : SetFunction V) (hz : Normalized z)
    (e : Fin n ≃ V) (j : ℕ) (hj : j ≤ n) :
    subsetSum (greedyPoint z e) (orderPrefix e j) = z (orderPrefix e j) := by
  induction j with
  | zero => simpa [Normalized] using hz.symm
  | succ j ih =>
    have hjn : j < n := by omega
    rw [orderPrefix_succ e ⟨j, hjn⟩, subsetSum_insert (not_mem_orderPrefix e _),
      greedyPoint_apply, ih (by omega)]
    ring

theorem greedyPoint_subset_prefix {n : ℕ} {z : SetFunction V} (hz : Normalized z)
    (hs : Supermodular z) (e : Fin n ≃ V) (S : Finset V) (j : ℕ) (hj : j ≤ n) :
    z (S ∩ orderPrefix e j) ≤ subsetSum (greedyPoint z e) (S ∩ orderPrefix e j) := by
  induction j with
  | zero => simp [Normalized] at hz; simpa using le_of_eq hz
  | succ j ih =>
    have hjn : j < n := by omega
    let v := e ⟨j, hjn⟩
    have hvP : v ∉ orderPrefix e j := not_mem_orderPrefix e _
    rw [orderPrefix_succ e ⟨j, hjn⟩]
    by_cases hvS : v ∈ S
    · have he : S ∩ insert v (orderPrefix e j) = insert v (S ∩ orderPrefix e j) := by
        ext x; simp; aesop
      rw [he, subsetSum_insert (by simp [hvP])]
      have h1 := hs.marginal (inter_subset_right : S ∩ orderPrefix e j ⊆ _) hvP
      have h2 := ih (by omega)
      have h3 : greedyPoint z e v = z (insert v (orderPrefix e j)) - z (orderPrefix e j) :=
        greedyPoint_apply z e ⟨j, hjn⟩
      linarith
    · have he : S ∩ insert v (orderPrefix e j) = S ∩ orderPrefix e j := by
        ext x; simp; aesop
      rw [he]
      exact ih (by omega)

theorem greedyPoint_mem_basePolytope {n : ℕ} {z : SetFunction V}
    (hz : Normalized z) (hs : Supermodular z) (e : Fin n ≃ V) :
    greedyPoint z e ∈ basePolytope z := by
  refine ⟨?_, ?_⟩
  · simpa using greedyPoint_prefix z hz e n le_rfl
  · intro S
    simpa using greedyPoint_subset_prefix hz hs e S n le_rfl

theorem basePolytope_nonempty {z : SetFunction V} (hz : Normalized z)
    (hs : Supermodular z) : (basePolytope z).Nonempty :=
  ⟨_, greedyPoint_mem_basePolytope hz hs (Fintype.equivFin V).symm⟩

end GraphicalZonotopes

end
end
end BundlePart0

section BundlePart1
/- Source: Papers/GraphicalZonotopes/BasePolytope.lean -/








@[expose] public section

noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

def orderedSequence {n : ℕ} (e : Fin n ≃ V) (x : V → ℝ) (j : ℕ) : ℝ :=
  if h : j < n then x (e ⟨j, h⟩) else 0

theorem sum_orderPrefix {n : ℕ} (e : Fin n ≃ V) (x : V → ℝ) (j : ℕ) (hj : j ≤ n) :
    subsetSum x (orderPrefix e j) = ∑ i ∈ range j, orderedSequence e x i := by
  classical
  apply sum_bij (fun v _ => (e.symm v).val)
  · intro v hv
    exact mem_range.mpr (mem_filter.mp hv).2
  · intro v hv w hw he
    exact e.symm.injective (Fin.ext he)
  · intro i hi
    have hin : i < n := (mem_range.mp hi).trans_le hj
    refine ⟨e ⟨i, hin⟩, ?_, ?_⟩
    · simp [orderPrefix, mem_range.mp hi]
    · simp
  · intro v hv
    simp [orderedSequence, (e.symm v).isLt]

theorem sum_ordered_product {n : ℕ} (e : Fin n ≃ V) (x w : V → ℝ) :
    (∑ i ∈ range n, orderedSequence e x i * orderedSequence e w i) =
      ∑ v, x v * w v := by
  have he : ∀ i, orderedSequence e x i * orderedSequence e w i =
      orderedSequence e (fun v => x v * w v) i := by
    intro i
    by_cases hi : i < n <;> simp [orderedSequence, hi]
  simp_rw [he]
  rw [← sum_orderPrefix e _ n le_rfl, orderPrefix_full]
  rfl

theorem weighted_le_of_prefix {n : ℕ} (e : Fin n ≃ V) (x y w : V → ℝ)
    (hw : Antitone (fun i => w (e i)))
    (hp : ∀ j ≤ n, subsetSum x (orderPrefix e j) ≤ subsetSum y (orderPrefix e j))
    (ht : subsetSum x univ = subsetSum y univ) :
    (∑ v, x v * w v) ≤ ∑ v, y v * w v := by
  let f : ℕ → ℝ := fun i => orderedSequence e y i - orderedSequence e x i
  let g : ℕ → ℝ := orderedSequence e w
  have hsum : ∀ j ≤ n, 0 ≤ ∑ i ∈ range j, f i := by
    intro j hj
    have h := hp j hj
    rw [sum_orderPrefix e x j hj, sum_orderPrefix e y j hj] at h
    simpa only [f, sum_sub_distrib, sub_nonneg] using h
  have htotal : ∑ i ∈ range n, f i = 0 := by
    rw [show f = (fun i => orderedSequence e y i - orderedSequence e x i) from rfl,
      sum_sub_distrib, ← sum_orderPrefix e y n le_rfl,
      ← sum_orderPrefix e x n le_rfl, orderPrefix_full, ht, sub_self]
  have hnonneg : 0 ≤ ∑ i ∈ range n, f i * g i := by
    simp_rw [← smul_eq_mul]
    rw [sum_range_by_parts', smul_eq_mul, htotal, zero_mul, zero_sub]
    apply neg_nonneg.mpr
    apply sum_nonpos
    intro i hi
    have hin : i < n - 1 := mem_range.mp hi
    have h1 := hsum (i + 1) (by omega)
    have h2 : g (i + 1) - g i ≤ 0 := by
      have hi0 : i < n := by omega
      have hi1 : i + 1 < n := by omega
      have hw' := hw (show (⟨i, hi0⟩ : Fin n) ≤ ⟨i+1, hi1⟩ by
        change i ≤ i + 1
        omega)
      simpa [g, orderedSequence, hi0, hi1, sub_nonpos] using hw'
    simpa only [smul_eq_mul] using mul_nonpos_of_nonneg_of_nonpos h1 h2
  simp only [f, g, sub_mul, sum_sub_distrib, sub_nonneg] at hnonneg
  rwa [sum_ordered_product, sum_ordered_product] at hnonneg

theorem exists_antitone_enumeration (w : V → ℝ) :
    ∃ e : Fin (Fintype.card V) ≃ V, Antitone (fun i => w (e i)) := by
  let f : Fin (Fintype.card V) → OrderDual ℝ := fun i => w ((Fintype.equivFin V).symm i)
  let e := (Tuple.sort f).trans (Fintype.equivFin V).symm
  exact ⟨e, Tuple.monotone_sort f⟩

theorem linearFunctional_eq_weighted_sum (f : (V → ℝ) →L[ℝ] ℝ) (x : V → ℝ) :
    f x = ∑ v, x v * f (Pi.single v 1) := by
  classical
  have he : x = ∑ v, x v • Pi.single v (1 : ℝ) := by
    funext v
    simp [Pi.single_apply]
  conv_lhs => rw [he]
  simp


theorem greedyPoint_minimizes {z : SetFunction V} (hz : Normalized z)
    (w : V → ℝ) : ∃ e : Fin (Fintype.card V) ≃ V,
    ∀ x ∈ basePolytope z,
      (∑ v, greedyPoint z e v * w v) ≤ ∑ v, x v * w v := by
  obtain ⟨e, he⟩ := exists_antitone_enumeration w
  refine ⟨e, ?_⟩
  intro x hx
  apply weighted_le_of_prefix e (greedyPoint z e) x w he
  · intro j hj
    rw [greedyPoint_prefix z hz e j hj]
    exact hx.2 _
  · have h := greedyPoint_prefix z hz e (Fintype.card V) le_rfl
    simpa [hx.1] using h

def greedyPoints (z : SetFunction V) : Set (V → ℝ) :=
  Set.range (fun e : Fin (Fintype.card V) ≃ V => greedyPoint z e)

theorem greedyPoints_finite (z : SetFunction V) : (greedyPoints z).Finite :=
  Set.finite_range _

theorem basePolytope_eq_convexHull {z : SetFunction V} (hz : Normalized z)
    (hs : Supermodular z) : basePolytope z = convexHull ℝ (greedyPoints z) := by
  symm
  apply Set.Subset.antisymm
  · apply convexHull_min ?_ (basePolytope_convex z)
    rintro x ⟨e, rfl⟩
    exact greedyPoint_mem_basePolytope hz hs e
  · intro x hx
    by_contra hout
    obtain ⟨f, c, hxc, hcf⟩ := geometric_hahn_banach_point_closed
      (convex_convexHull ℝ _) ((greedyPoints_finite z).isClosed_convexHull ℝ) hout
    obtain ⟨e, he⟩ := greedyPoint_minimizes hz (fun v => f (Pi.single v 1))
    have hm := he x hx
    rw [← linearFunctional_eq_weighted_sum, ← linearFunctional_eq_weighted_sum] at hm
    have hc := hcf (greedyPoint z e) (subset_convexHull ℝ _ ⟨e, rfl⟩)
    linarith

theorem basePolytope_compact {z : SetFunction V} (hz : Normalized z)
    (hs : Supermodular z) : IsCompact (basePolytope z) := by
  rw [basePolytope_eq_convexHull hz hs]
  exact (greedyPoints_finite z).isCompact_convexHull ℝ

@[simp] theorem greedyPoint_add {n : ℕ} (z w : SetFunction V) (e : Fin n ≃ V) :
    greedyPoint (z + w) e = greedyPoint z e + greedyPoint w e := by
  funext v
  simp only [greedyPoint, Pi.add_apply]
  ring

@[simp] theorem greedyPoint_smul {n : ℕ} (a : ℝ) (z : SetFunction V) (e : Fin n ≃ V) :
    greedyPoint (a • z) e = a • greedyPoint z e := by
  funext v
  simp only [greedyPoint, Pi.smul_apply, smul_eq_mul]
  ring

theorem Supermodular.add {z w : SetFunction V} (hz : Supermodular z)
    (hw : Supermodular w) : Supermodular (z + w) := by
  intro A B
  have h1 := hz A B
  have h2 := hw A B
  simp only [Pi.add_apply]
  linarith

theorem Supermodular.smul {z : SetFunction V} (hz : Supermodular z)
    {a : ℝ} (ha : 0 ≤ a) : Supermodular (a • z) := by
  intro A B
  simpa [mul_add] using mul_le_mul_of_nonneg_left (hz A B) ha

theorem basePolytope_add {z w : SetFunction V} (hz : Normalized z)
    (hw : Normalized w) (hsz : Supermodular z) (hsw : Supermodular w) :
    basePolytope (z + w) = basePolytope z + basePolytope w := by
  apply Set.Subset.antisymm
  · rw [basePolytope_eq_convexHull (show Normalized (z + w) by
      change z ∅ + w ∅ = 0; rw [hz, hw, add_zero])
      (hsz.add hsw)]
    apply convexHull_min ?_ ((basePolytope_convex z).add (basePolytope_convex w))
    rintro x ⟨e, rfl⟩
    dsimp only
    rw [greedyPoint_add]
    exact Set.add_mem_add (greedyPoint_mem_basePolytope hz hsz e)
      (greedyPoint_mem_basePolytope hw hsw e)
  · rintro x ⟨a, ha, b, hb, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [subsetSum_add, ha.1, hb.1]; rfl
    · intro S
      rw [subsetSum_add]
      exact add_le_add (ha.2 S) (hb.2 S)

theorem basePolytope_smul {z : SetFunction V} (hz : Normalized z)
    (hs : Supermodular z) {a : ℝ} (ha : 0 ≤ a) :
    basePolytope (a • z) = a • basePolytope z := by
  rw [basePolytope_eq_convexHull (show Normalized (a • z) by
    change a * z ∅ = 0; rw [hz, mul_zero])
    (hs.smul ha), basePolytope_eq_convexHull hz hs]
  rw [← convexHull_smul]
  congr 1
  ext x
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨greedyPoint z e, ⟨e, rfl⟩, (greedyPoint_smul a z e).symm⟩
  · rintro ⟨y, ⟨e, rfl⟩, rfl⟩
    exact ⟨e, greedyPoint_smul a z e⟩

end GraphicalZonotopes

end
end
end BundlePart1

section BundlePart2
/- Source: Papers/GraphicalZonotopes/Ordering.lean -/




@[expose] public section

noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every set occurs as a prefix of a linear ordering. -/
theorem exists_prefix_enumeration (S : Finset V) :
    ∃ (e : Fin (Fintype.card V) ≃ V) (j : ℕ), j ≤ Fintype.card V ∧
      orderPrefix e j = S := by
  classical
  let w : V → ℝ := fun v => if v ∈ S then 1 else 0
  obtain ⟨e, he⟩ := exists_antitone_enumeration w
  let j := (univ.filter (fun i : Fin (Fintype.card V) => (1 : ℝ) ≤ w (e i))).card
  refine ⟨e, j, ?_, ?_⟩
  · exact (card_filter_le _ _).trans (by simp)
  · ext v
    simp only [orderPrefix, mem_filter, mem_univ, true_and]
    have h := Tuple.lt_card_ge_iff_apply_ge_of_antitone (j := e.symm v) (a := (1 : ℝ)) he
    by_cases hv : v ∈ S <;> norm_num [j, w, hv] at h ⊢ <;> exact h

/-- An arbitrary conditioning set can be followed by either specified ordered pair. -/
theorem exists_pair_enumeration (S : Finset V) {u v : V} (huv : u ≠ v)
    (hu : u ∉ S) (hv : v ∉ S) :
    ∃ e : Fin (Fintype.card V) ≃ V,
      orderPrefix e (e.symm u).val = S ∧
      orderPrefix e (e.symm v).val = insert u S := by
  classical
  let w : V → ℝ := fun x => if x ∈ S then 3 else if x = u then 2 else if x = v then 1 else 0
  obtain ⟨e, he⟩ := exists_antitone_enumeration w
  have wu : w u = 2 := by simp [w, hu]
  have wv : w v = 1 := by simp [w, hv, Ne.symm huv]
  have hmono : ∀ x y, e.symm x ≤ e.symm y → w y ≤ w x := by
    intro x y hxy
    simpa using he hxy
  refine ⟨e, ?_, ?_⟩
  · ext x
    simp only [orderPrefix, mem_filter, mem_univ, true_and]
    constructor
    · intro hx
      by_contra hxS
      have hxu : x ≠ u := by intro h; subst x; omega
      have hwx : w x ≤ 1 := by simp only [w, if_neg hxS, if_neg hxu]; split <;> norm_num
      have h := hmono x u (by exact le_of_lt hx)
      rw [wu] at h
      linarith
    · intro hxS
      have hwx : w x = 3 := by simp [w, hxS]
      by_contra hx
      have h := hmono u x (by omega)
      rw [wu, hwx] at h
      norm_num at h
  · ext x
    simp only [orderPrefix, mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · intro hx
      by_contra hnot
      push_neg at hnot
      have hxv : x ≠ v := by intro h; subst x; omega
      have hwx : w x = 0 := by simp [w, hnot.1, hnot.2, hxv]
      have h := hmono x v (by exact le_of_lt hx)
      rw [wv, hwx] at h
      norm_num at h
    · intro hx
      have hwx : 2 ≤ w x := by
        rcases hx with rfl | hxS
        · rw [wu]
        · norm_num [w, hxS]
      by_contra hnot
      have h := hmono v x (by omega)
      rw [wv] at h
      linarith

end GraphicalZonotopes

end
end
end BundlePart2

section BundlePart3
/- Source: Papers/GraphicalZonotopes/Elemental.lean -/




@[expose] public section

noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem ElementallyNonnegative.difference_mono {z : SetFunction V}
    (hz : ElementallyNonnegative z) {A B : Finset V} (hAB : A ⊆ B)
    (D : Finset V) (hDB : Disjoint D B) :
    z (A ∪ D) - z A ≤ z (B ∪ D) - z B := by
  induction D using Finset.induction_on with
  | empty => simp
  | @insert d D hd ih =>
    have hDB' : Disjoint D B := hDB.mono_left (subset_insert d D)
    have hdB : d ∉ B := fun h => Finset.disjoint_left.mp hDB (mem_insert_self _ _) h
    have hdBD : d ∉ B ∪ D := by simp [hd, hdB]
    have h1 := ih hDB'
    have h2 := hz.marginal (show A ∪ D ⊆ B ∪ D from union_subset_union hAB (subset_refl D)) hdBD
    rw [union_insert, union_insert]
    linarith

theorem ElementallyNonnegative.supermodular {z : SetFunction V}
    (hz : ElementallyNonnegative z) : Supermodular z := by
  classical
  intro A B
  have h := hz.difference_mono (inter_subset_left : A ∩ B ⊆ A)
    (B \ A) Finset.disjoint_sdiff.symm
  have he : (A ∩ B) ∪ (B \ A) = B := by
    ext x
    simp only [mem_union,mem_inter,mem_sdiff]
    tauto
  have he' : A ∪ (B \ A) = A ∪ B := union_sdiff_self_eq_union
  rw [he, he'] at h
  linarith

theorem supermodular_iff_elemental (z : SetFunction V) :
    Supermodular z ↔ ElementallyNonnegative z :=
  ⟨Supermodular.elemental, ElementallyNonnegative.supermodular⟩

@[simp] theorem delta_add (z w : SetFunction V) (u v : V) (S : Finset V) :
    delta (z + w) u v S = delta z u v S + delta w u v S := by
  simp only [delta, Pi.add_apply]; ring

@[simp] theorem delta_sub (z w : SetFunction V) (u v : V) (S : Finset V) :
    delta (z - w) u v S = delta z u v S - delta w u v S := by
  simp only [delta, Pi.sub_apply]; ring

@[simp] theorem delta_smul (a : ℝ) (z : SetFunction V) (u v : V) (S : Finset V) :
    delta (a • z) u v S = a * delta z u v S := by
  simp only [delta, Pi.smul_apply, smul_eq_mul]; ring

def deltaLinear (u v : V) (S : Finset V) : SetFunction V →ₗ[ℝ] ℝ where
  toFun z := delta z u v S
  map_add' z w := delta_add z w u v S
  map_smul' a z := delta_smul a z u v S

@[simp] theorem delta_sum {I : Type*} (t : Finset I) (z : I → SetFunction V)
    (u v : V) (S : Finset V) :
    delta (∑ i ∈ t, z i) u v S = ∑ i ∈ t, delta (z i) u v S :=
  map_sum (deltaLinear u v S) z t

def modular (x : V → ℝ) : SetFunction V := subsetSum x

theorem delta_modular (x : V → ℝ) {u v : V} (huv : u ≠ v)
    {S : Finset V} (hu : u ∉ S) (hv : v ∉ S) : delta (modular x) u v S = 0 := by
  simp only [delta, modular]
  rw [subsetSum_insert (by simp [huv, hu]), subsetSum_insert hu, subsetSum_insert hv]
  ring

theorem modular_supermodular (x : V → ℝ) : Supermodular (modular x) := by
  apply ElementallyNonnegative.supermodular
  intro u v huv S hu hv
  rw [delta_modular x huv hu hv]

theorem zero_elemental_modular {z : SetFunction V} (hzero : Normalized z)
    (hz : ∀ u v, u ≠ v → ∀ S, u ∉ S → v ∉ S → delta z u v S = 0) :
    z = modular (fun v => z {v}) := by
  have hmarg : ∀ S : Finset V, ∀ v, v ∉ S → z (insert v S) = z {v} + z S := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro v hv; simp [Normalized] at hzero; simp [hzero]
    | @insert u S hu ih =>
      intro v hv
      have hvS : v ∉ S := fun h => hv (mem_insert_of_mem h)
      have hvu : v ≠ u := by intro h; subst v; exact hv (mem_insert_self _ _)
      have h := hz v u hvu S hvS hu
      dsimp [delta] at h
      rw [ih v hvS] at h
      linarith
  funext S
  induction S using Finset.induction_on with
  | empty => simpa [modular, Normalized] using hzero
  | @insert v S hv ih =>
    rw [hmarg S v hv]
    change _ = subsetSum (fun w => z {w}) (insert v S)
    rw [subsetSum_insert hv]
    exact congrArg (z {v} + ·) ih

theorem normalized_zero_elemental_eq_zero {z : SetFunction V}
    (hn : TranslationNormalized z)
    (hz : ∀ u v, u ≠ v → ∀ S, u ∉ S → v ∉ S → delta z u v S = 0) : z = 0 := by
  rw [zero_elemental_modular hn.1 hz]
  funext S
  simp [modular, subsetSum, hn.2]

end GraphicalZonotopes

end
end
end BundlePart3

section BundlePart4
/- Source: Papers/GraphicalZonotopes/Minkowski.lean -/





@[expose] public section

/-!
The geometric bridge from arbitrary compact convex Minkowski summands to
supermodular set functions. No deformation-cone characterization is assumed.
-/
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

def lowerSupport (P : Set (V → ℝ)) (S : Finset V) : ℝ :=
  sInf ((fun x => subsetSum x S) '' P)

theorem continuous_subsetSum (S : Finset V) :
    Continuous (fun x : V → ℝ => subsetSum x S) := by
  unfold subsetSum
  exact continuous_finsetSum _ (fun v _ => continuous_apply v)

theorem lowerSupport_minimum {P : Set (V → ℝ)} (hc : IsCompact P)
    (hne : P.Nonempty) (S : Finset V) :
    ∃ x ∈ P, subsetSum x S = lowerSupport P S ∧
      ∀ y ∈ P, lowerSupport P S ≤ subsetSum y S := by
  obtain ⟨x, hx, hmin⟩ := hc.exists_isMinOn hne (continuous_subsetSum S).continuousOn
  have hi : IsLeast ((fun y => subsetSum y S) '' P) (subsetSum x S) := by
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmin hy
  have he : lowerSupport P S = subsetSum x S := hi.csInf_eq
  exact ⟨x, hx, he.symm, fun y hy => by rw [he]; exact hmin hy⟩

theorem lowerSupport_le {P : Set (V → ℝ)} (hc : IsCompact P)
    {x : V → ℝ} (hx : x ∈ P) (S : Finset V) :
    lowerSupport P S ≤ subsetSum x S := by
  obtain ⟨_, _, _, h⟩ := lowerSupport_minimum hc ⟨x, hx⟩ S
  exact h x hx

theorem lowerSupport_normalized {P : Set (V → ℝ)} (hc : IsCompact P)
    (hne : P.Nonempty) : Normalized (lowerSupport P) := by
  obtain ⟨x, hx, he, _⟩ := lowerSupport_minimum hc hne ∅
  simpa [Normalized] using he.symm

theorem lowerSupport_add {P R : Set (V → ℝ)}
    (hP : IsCompact P) (hR : IsCompact R) (hnP : P.Nonempty) (hnR : R.Nonempty) :
    lowerSupport (P + R) = lowerSupport P + lowerSupport R := by
  funext S
  obtain ⟨p, hp, hpmin, hpbound⟩ := lowerSupport_minimum hP hnP S
  obtain ⟨r, hr, hrmin, hrbound⟩ := lowerSupport_minimum hR hnR S
  have hi : IsLeast ((fun y => subsetSum y S) '' (P + R))
      (lowerSupport P S + lowerSupport R S) := by
    refine ⟨⟨p + r, Set.add_mem_add hp hr, ?_⟩, ?_⟩
    · change subsetSum (p+r) S = lowerSupport P S + lowerSupport R S
      rw [subsetSum_add, hpmin, hrmin]
    · rintro _ ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
      change lowerSupport P S + lowerSupport R S ≤ subsetSum (x+y) S
      rw [subsetSum_add]
      exact add_le_add (hpbound x hx) (hrbound y hy)
  exact hi.csInf_eq

theorem lowerSupport_basePolytope {z : SetFunction V} (hz : Normalized z)
    (hs : Supermodular z) : lowerSupport (basePolytope z) = z := by
  funext S
  obtain ⟨e, j, hj, hp⟩ := exists_prefix_enumeration S
  have hg := greedyPoint_mem_basePolytope hz hs e
  have he : subsetSum (greedyPoint z e) S = z S := by
    rw [← hp]
    exact greedyPoint_prefix z hz e j hj
  have hi : IsLeast ((fun y => subsetSum y S) '' basePolytope z) (z S) := by
    refine ⟨⟨greedyPoint z e, hg, he⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hy.2 S
  exact hi.csInf_eq

/-- A decomposition of a greedy point simultaneously minimizes every prefix
in both summands. -/
theorem summand_prefix_minima {z : SetFunction V} (hz : Normalized z)
    (hs : Supermodular z) {P R : Set (V → ℝ)}
    (hP : IsCompact P) (hR : IsCompact R) (hnP : P.Nonempty) (hnR : R.Nonempty)
    (heq : P + R = basePolytope z)
    (e : Fin (Fintype.card V) ≃ V) :
    ∃ p ∈ P, ∀ j ≤ Fintype.card V,
      subsetSum p (orderPrefix e j) = lowerSupport P (orderPrefix e j) := by
  have hg := greedyPoint_mem_basePolytope hz hs e
  rw [← heq] at hg
  obtain ⟨p, hp, r, hr, hpr⟩ := hg
  change p+r = greedyPoint z e at hpr
  refine ⟨p, hp, ?_⟩
  intro j hj
  have hadd : lowerSupport P (orderPrefix e j) + lowerSupport R (orderPrefix e j) =
      z (orderPrefix e j) := by
    have h := congrFun (lowerSupport_add hP hR hnP hnR) (orderPrefix e j)
    rw [heq, lowerSupport_basePolytope hz hs] at h
    exact h.symm
  have hsum : subsetSum p (orderPrefix e j) + subsetSum r (orderPrefix e j) =
      z (orderPrefix e j) := by
    rw [← subsetSum_add, hpr]
    exact greedyPoint_prefix z hz e j hj
  have hpbound := lowerSupport_le hP hp (orderPrefix e j)
  have hrbound := lowerSupport_le hR hr (orderPrefix e j)
  linarith

/-- Supermodularity is derived for arbitrary compact-convex summands, rather
than being imposed on them as an extra assumption. -/
theorem summand_lowerSupport_supermodular {z : SetFunction V} (hz : Normalized z)
    (hs : Supermodular z) {P R : Set (V → ℝ)}
    (hP : IsCompact P) (hR : IsCompact R) (hnP : P.Nonempty) (hnR : R.Nonempty)
    (heq : P + R = basePolytope z) : Supermodular (lowerSupport P) := by
  apply ElementallyNonnegative.supermodular
  intro u v huv S hu hv
  obtain ⟨e, heS, heSu⟩ := exists_pair_enumeration S huv hu hv
  obtain ⟨p, hp, hpref⟩ := summand_prefix_minima hz hs hP hR hnP hnR heq e
  have hS : subsetSum p S = lowerSupport P S := by
    rw [← heS]
    exact hpref _ (e.symm u).isLt.le
  have hSu : subsetSum p (insert u S) = lowerSupport P (insert u S) := by
    rw [← heSu]
    exact hpref _ (e.symm v).isLt.le
  have hSuv : subsetSum p (insert v (insert u S)) = lowerSupport P (insert v (insert u S)) := by
    have h := hpref ((e.symm v).val + 1) (by omega)
    rw [orderPrefix_succ, e.apply_symm_apply, heSu] at h
    exact h
  have hSv := lowerSupport_le hP hp (insert v S)
  rw [subsetSum_insert (by simp [Ne.symm huv, hv]), hSu] at hSuv
  rw [subsetSum_insert hv, hS] at hSv
  simp only [delta, insert_comm u v]
  linarith

theorem summand_greedyPoint_mem {z : SetFunction V} (hz : Normalized z)
    (hs : Supermodular z) {P R : Set (V → ℝ)}
    (hP : IsCompact P) (hR : IsCompact R) (hnP : P.Nonempty) (hnR : R.Nonempty)
    (heq : P + R = basePolytope z)
    (e : Fin (Fintype.card V) ≃ V) : greedyPoint (lowerSupport P) e ∈ P := by
  obtain ⟨p, hp, hpref⟩ := summand_prefix_minima hz hs hP hR hnP hnR heq e
  have he : greedyPoint (lowerSupport P) e = p := by
    funext v
    have h0 := hpref (e.symm v).val (e.symm v).isLt.le
    have h1 := hpref ((e.symm v).val + 1) (by omega)
    rw [orderPrefix_succ, e.apply_symm_apply,
      subsetSum_insert (by simpa using not_mem_orderPrefix e (e.symm v))] at h1
    simp only [greedyPoint]
    rw [orderPrefix_succ,e.apply_symm_apply]
    linarith
  rwa [he]

/-- The full geometric summand theorem for lower base polytopes. -/
theorem summand_eq_basePolytope {z : SetFunction V} (hz : Normalized z)
    (hs : Supermodular z) {P R : Set (V → ℝ)}
    (hP : IsCompact P) (hR : IsCompact R) (hconv : Convex ℝ P)
    (hnP : P.Nonempty) (hnR : R.Nonempty)
    (heq : P + R = basePolytope z) : P = basePolytope (lowerSupport P) := by
  apply Set.Subset.antisymm
  · intro p hp
    refine ⟨?_, fun S => lowerSupport_le hP hp S⟩
    obtain ⟨q, hq, hqmin, _⟩ := lowerSupport_minimum hP hnP univ
    obtain ⟨r, hr⟩ := hnR
    have hpr : p + r ∈ basePolytope z := by rw [← heq]; exact Set.add_mem_add hp hr
    have hqr : q + r ∈ basePolytope z := by rw [← heq]; exact Set.add_mem_add hq hr
    have ht1 := hpr.1
    have ht2 := hqr.1
    rw [subsetSum_add] at ht1 ht2
    linarith
  · rw [basePolytope_eq_convexHull (lowerSupport_normalized hP hnP)
      (summand_lowerSupport_supermodular hz hs hP hR hnP hnR heq)]
    apply convexHull_min ?_ hconv
    rintro _ ⟨e, rfl⟩
    exact summand_greedyPoint_mem hz hs hP hR hnP hnR heq e

end GraphicalZonotopes

end
end
end BundlePart4

section BundlePart5
/- Source: Papers/GraphicalZonotopes/Indecomposable.lean -/




@[expose] public section

/-! Normalization, translations, and genuine geometric Minkowski indecomposability. -/
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem subsetSum_sub (x y : V → ℝ) (S : Finset V) :
    subsetSum (x - y) S = subsetSum x S - subsetSum y S := by
  simp [subsetSum, sum_sub_distrib]

def normalize (z : SetFunction V) : SetFunction V := z - modular (fun v => z {v})

theorem normalize_translationNormalized {z : SetFunction V} (hz : Normalized z) :
    TranslationNormalized (normalize z) := by
  constructor
  · simpa [Normalized, normalize, modular] using hz
  · intro v
    simp [normalize, modular, subsetSum]

theorem delta_normalize (z : SetFunction V) {u v : V} (huv : u ≠ v)
    {S : Finset V} (hu : u ∉ S) (hv : v ∉ S) :
    delta (normalize z) u v S = delta z u v S := by
  rw [normalize, delta_sub, delta_modular _ huv hu hv, sub_zero]

theorem Supermodular.normalize {z : SetFunction V} (hz : Supermodular z) :
    Supermodular (normalize z) := by
  apply ElementallyNonnegative.supermodular
  intro u v huv S hu hv
  rw [delta_normalize z huv hu hv]
  exact hz.elemental u v huv S hu hv

theorem normalize_add (z w : SetFunction V) : normalize (z + w) = normalize z + normalize w := by
  funext S
  simp only [normalize, Pi.sub_apply, Pi.add_apply, modular, subsetSum, sum_add_distrib]
  ring

theorem normalize_eq_self {z : SetFunction V} (hz : TranslationNormalized z) :
    normalize z = z := by
  funext S
  simp [normalize, modular, subsetSum, hz.2]

theorem recover_normalize (z : SetFunction V) :
    z = normalize z + modular (fun v => z {v}) := by
  rw [normalize, sub_add_cancel]

theorem basePolytope_translate (z : SetFunction V) (t : V → ℝ) :
    basePolytope (z + modular t) = ({t} : Set (V → ℝ)) + basePolytope z := by
  ext x
  constructor
  · intro hx
    refine ⟨t, rfl, x - t, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · rw [subsetSum_sub]
        have h := hx.1
        change subsetSum x univ = z univ + subsetSum t univ at h
        linarith
      · intro S
        rw [subsetSum_sub]
        have h := hx.2 S
        change z S + subsetSum t S ≤ subsetSum x S at h
        linarith
    · abel
  · rintro ⟨t', ht, y, hy, rfl⟩
    have ht' : t' = t := Set.mem_singleton_iff.mp ht
    subst t'
    refine ⟨?_, ?_⟩
    · rw [subsetSum_add, hy.1]
      change _ = z univ + subsetSum t univ
      ring
    · intro S
      rw [subsetSum_add]
      change z S + subsetSum t S ≤ _
      linarith [hy.2 S]

/-- Extremality in the normalized supermodular cone, expressed by its actual
additive decomposition property. -/
def ExtremeSupermodular (z : SetFunction V) : Prop :=
  TranslationNormalized z ∧ Supermodular z ∧ z ≠ 0 ∧
    ∀ f g : SetFunction V,
      TranslationNormalized f → TranslationNormalized g →
      Supermodular f → Supermodular g → f + g = z →
      ∃ a : ℝ, 0 ≤ a ∧ f = a • z

/-- Every compact convex Minkowski summand is a nonnegative homothetic copy.
This quantifies over actual subsets of real coordinate space. -/
def MinkowskiIndecomposable (Q : Set (V → ℝ)) : Prop :=
  Q.Nonempty ∧ ∀ P R : Set (V → ℝ),
    IsCompact P → IsCompact R → Convex ℝ P → Convex ℝ R →
    P + R = Q → ∃ (a : ℝ) (t : V → ℝ), 0 ≤ a ∧ P = ({t} : Set (V → ℝ)) + a • Q

/-- Cone extremality implies geometric indecomposability with no assumption
that the summands are already generalized permutahedra. -/
theorem ExtremeSupermodular.minkowskiIndecomposable {z : SetFunction V}
    (hz : ExtremeSupermodular z) : MinkowskiIndecomposable (basePolytope z) := by
  have hne := basePolytope_nonempty hz.1.1 hz.2.1
  refine ⟨hne, ?_⟩
  intro P R hP hR hPc hRc heq
  obtain ⟨x, hx⟩ := hne
  rw [← heq] at hx
  obtain ⟨p, hp, r, hr, hpr⟩ := hx
  have hnP : P.Nonempty := ⟨p, hp⟩
  have hnR : R.Nonempty := ⟨r, hr⟩
  have hnP' := lowerSupport_normalized hP hnP
  have hnR' := lowerSupport_normalized hR hnR
  have hsP := summand_lowerSupport_supermodular hz.1.1 hz.2.1 hP hR hnP hnR heq
  have heq' : R + P = basePolytope z := by rw [add_comm]; exact heq
  have hsR := summand_lowerSupport_supermodular hz.1.1 hz.2.1 hR hP hnR hnP heq'
  have hsum : lowerSupport P + lowerSupport R = z := by
    rw [← lowerSupport_add hP hR hnP hnR, heq, lowerSupport_basePolytope hz.1.1 hz.2.1]
  have hnormsum : normalize (lowerSupport P) + normalize (lowerSupport R) = z := by
    rw [← normalize_add, hsum, normalize_eq_self hz.1]
  obtain ⟨a, ha, hscale⟩ := hz.2.2.2 _ _ (normalize_translationNormalized hnP')
    (normalize_translationNormalized hnR') hsP.normalize hsR.normalize hnormsum
  refine ⟨a, (fun v => lowerSupport P {v}), ha, ?_⟩
  conv_lhs => rw [summand_eq_basePolytope hz.1.1 hz.2.1 hP hR hPc hnP hnR heq]
  conv_lhs => rw [recover_normalize (lowerSupport P)]
  rw [basePolytope_translate, hscale, basePolytope_smul hz.1.1 hz.2.1 ha]

end GraphicalZonotopes

end
end
end BundlePart5

section BundlePart6
/- Source: Papers/GraphicalZonotopes/Mobius.lean -/





@[expose] public section

noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

def zeta (y : SetFunction V) (S : Finset V) : ℝ := ∑ C ∈ S.powerset, y C

def zetaLinear : SetFunction V →ₗ[ℝ] SetFunction V where
  toFun := zeta
  map_add' y z := by funext S; simp [zeta, sum_add_distrib]
  map_smul' a y := by funext S; simp [zeta, mul_sum]

theorem zeta_eq_zero_iff (y : SetFunction V) : zeta y = 0 ↔ y = 0 := by
  constructor
  · intro h
    funext S
    refine Finset.strongInductionOn S ?_
    intro S ih
    have he := congrFun h S
    change ∑ C ∈ S.powerset, y C = 0 at he
    rw [Finset.sum_eq_single S] at he
    · exact he
    · intro C hC hCS
      exact ih C (Finset.ssubset_iff_subset_ne.mpr ⟨mem_powerset.mp hC, hCS⟩)
    · simp
  · rintro rfl
    funext S
    simp [zeta]

theorem zeta_injective : Function.Injective (zeta : SetFunction V → SetFunction V) := by
  intro y z he
  have h : zeta (y - z) = 0 := by
    change zetaLinear (y - z) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr he
  exact sub_eq_zero.mp ((zeta_eq_zero_iff _).mp h)

def zetaEquiv : SetFunction V ≃ₗ[ℝ] SetFunction V :=
  LinearEquiv.ofInjectiveEndo zetaLinear zeta_injective

def mobius (z : SetFunction V) : SetFunction V := zetaEquiv.symm z

@[simp] theorem zeta_mobius (z : SetFunction V) : zeta (mobius z) = z :=
  zetaEquiv.apply_symm_apply z

@[simp] theorem mobius_zeta (y : SetFunction V) : mobius (zeta y) = y :=
  zetaEquiv.symm_apply_apply y

def setMonomial (C : Finset V) (S : Finset V) : ℝ := if C ⊆ S then 1 else 0

theorem zeta_eq_sum_monomials (y : SetFunction V) :
    zeta y = ∑ C : Finset V, y C • setMonomial C := by
  funext S
  unfold zeta
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, setMonomial]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext C
  simp

theorem delta_setMonomial {u v : V} (huv : u ≠ v) {S : Finset V}
    (hu : u ∉ S) (hv : v ∉ S) (C : Finset V) :
    delta (setMonomial C) u v S =
      if u ∈ C ∧ v ∈ C ∧ C ⊆ insert u (insert v S) then 1 else 0 := by
  have h1 : C ⊆ insert u S ↔ C ⊆ insert u (insert v S) ∧ v ∉ C := by
    constructor
    · intro h
      refine ⟨h.trans (insert_subset_insert _ (subset_insert _ _)), ?_⟩
      intro hvC
      have hm := h hvC
      simp [Ne.symm huv, hv] at hm
    · rintro ⟨h, hn⟩ x hx
      have hm := h hx
      simp only [mem_insert] at hm ⊢
      rcases hm with hxu | hxv | hxS
      · exact Or.inl hxu
      · exact False.elim (hn (hxv ▸ hx))
      · exact Or.inr hxS
  have h2 : C ⊆ insert v S ↔ C ⊆ insert u (insert v S) ∧ u ∉ C := by
    constructor
    · intro h
      refine ⟨h.trans (subset_insert _ _), ?_⟩
      intro huC
      have hm := h huC
      simp [huv, hu] at hm
    · rintro ⟨h, hn⟩ x hx
      have hm := h hx
      rcases mem_insert.mp hm with hxu | hm
      · exact False.elim (hn (hxu ▸ hx))
      · exact hm
  have h3 : C ⊆ S ↔ C ⊆ insert u (insert v S) ∧ u ∉ C ∧ v ∉ C := by
    constructor
    · intro h
      refine ⟨h.trans ((subset_insert _ _).trans (subset_insert _ _)), ?_, ?_⟩
      · exact fun hm => hu (h hm)
      · exact fun hm => hv (h hm)
    · rintro ⟨h, hnu, hnv⟩ x hx
      have hm := h hx
      simp only [mem_insert] at hm
      rcases hm with hxu | hxv | hxS
      · exact False.elim (hnu (hxu ▸ hx))
      · exact False.elim (hnv (hxv ▸ hx))
      · exact hxS
  simp only [delta, setMonomial, h1, h2, h3]
  by_cases hC : C ⊆ insert u (insert v S) <;>
    by_cases huC : u ∈ C <;> by_cases hvC : v ∈ C <;> simp [hC, huC, hvC]

theorem delta_zeta {u v : V} (huv : u ≠ v) {S : Finset V}
    (hu : u ∉ S) (hv : v ∉ S) (y : SetFunction V) :
    delta (zeta y) u v S =
      ∑ C ∈ (insert u (insert v S)).powerset.filter (fun C => u ∈ C ∧ v ∈ C), y C := by
  rw [zeta_eq_sum_monomials, delta_sum]
  simp_rw [delta_smul, delta_setMonomial huv hu hv]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← sum_filter]
  congr 1
  ext C
  simp only [mem_filter, mem_univ, true_and, mem_powerset]
  tauto

@[simp] theorem zeta_empty (y : SetFunction V) : zeta y ∅ = y ∅ := by simp [zeta]

theorem zeta_singleton (y : SetFunction V) (v : V) : zeta y {v} = y ∅ + y {v} := by
  have hp : ({v} : Finset V).powerset = {∅,{v}} := by
    ext C
    simp only [mem_powerset,mem_insert,mem_singleton,subset_singleton_iff]
  simp [zeta,hp]

theorem zeta_normalized_iff (y : SetFunction V) :
    TranslationNormalized (zeta y) ↔ y ∅ = 0 ∧ ∀ v, y {v} = 0 := by
  simp only [TranslationNormalized, Normalized, zeta_empty, zeta_singleton]
  constructor
  · rintro ⟨h, hv⟩
    exact ⟨h, fun v => by simpa [h] using hv v⟩
  · rintro ⟨h, hv⟩
    exact ⟨h, fun v => by simp [h, hv v]⟩

theorem nonedge_coefficients_zero_iff (y : SetFunction V) {u v : V} (huv : u ≠ v) :
    (∀ S, u ∉ S → v ∉ S → delta (zeta y) u v S = 0) ↔
      ∀ C, u ∈ C → v ∈ C → y C = 0 := by
  constructor
  · intro hz C
    refine Finset.strongInductionOn C ?_
    intro C ih huC hvC
    let S := (C.erase u).erase v
    have huS : u ∉ S := by simp [S]
    have hvS : v ∉ S := by simp [S]
    have he : insert u (insert v S) = C := by
      ext w
      by_cases hwu : w = u
      · subst w
        simp [S,huC]
      · by_cases hwv : w = v
        · subst w
          simp [S,hvC]
        · simp [S,hwu,hwv]
    have h := hz S huS hvS
    rw [delta_zeta huv huS hvS, he] at h
    rw [sum_eq_single C] at h
    · exact h
    · intro D hD hDC
      rcases mem_filter.mp hD with ⟨hsub, huD, hvD⟩
      exact ih D (Finset.ssubset_iff_subset_ne.mpr ⟨mem_powerset.mp hsub, hDC⟩) huD hvD
    · simp [huC, hvC]
  · intro hz S hu hv
    rw [delta_zeta huv hu hv]
    apply sum_eq_zero
    intro C hC
    exact hz C (mem_filter.mp hC).2.1 (mem_filter.mp hC).2.2

end GraphicalZonotopes

end
end
end BundlePart6

section BundlePart7
/- Source: Papers/GraphicalZonotopes/GraphicalCone.lean -/






@[expose] public section

noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Vanishing of every elemental difference on the graph's nonedges. -/
def Graphical (G : SimpleGraph V) (z : SetFunction V) : Prop :=
  ∀ u v, u ≠ v → ¬G.Adj u v → ∀ S, u ∉ S → v ∉ S → delta z u v S = 0

/-- Möbius support on cliques of cardinality at least two. -/
def CliqueSupported (G : SimpleGraph V) (y : SetFunction V) : Prop :=
  y ∅ = 0 ∧ (∀ v, y {v} = 0) ∧
    ∀ C u v, u ∈ C → v ∈ C → u ≠ v → ¬G.Adj u v → y C = 0

theorem cliqueSupported_iff (G : SimpleGraph V) (y : SetFunction V) :
    CliqueSupported G y ↔ TranslationNormalized (zeta y) ∧ Graphical G (zeta y) := by
  constructor
  · rintro ⟨he, hs, hn⟩
    refine ⟨(zeta_normalized_iff y).mpr ⟨he, hs⟩, ?_⟩
    intro u v huv hG
    exact (nonedge_coefficients_zero_iff y huv).mpr (fun C hu hv => hn C u v hu hv huv hG)
  · rintro ⟨hz, hG⟩
    obtain ⟨he, hs⟩ := (zeta_normalized_iff y).mp hz
    refine ⟨he, hs, ?_⟩
    intro C u v hu hv huv hnon
    exact (nonedge_coefficients_zero_iff y huv).mp (hG u v huv hnon) C hu hv

theorem mobius_cliqueSupported_iff (G : SimpleGraph V) (z : SetFunction V) :
    CliqueSupported G (mobius z) ↔ TranslationNormalized z ∧ Graphical G z := by
  simpa using cliqueSupported_iff G (mobius z)

/-- No graphical-support hypothesis on the summands is needed: nonnegativity
and a vanishing sum force it automatically. -/
theorem Graphical.summands {G : SimpleGraph V} {z f g : SetFunction V}
    (hG : Graphical G z) (hf : Supermodular f) (hg : Supermodular g)
    (he : f + g = z) : Graphical G f ∧ Graphical G g := by
  have hall : ∀ u v, u ≠ v → ¬G.Adj u v → ∀ S, u ∉ S → v ∉ S →
      delta f u v S = 0 ∧ delta g u v S = 0 := by
    intro u v huv hnon S hu hv
    have h1 := hf.elemental u v huv S hu hv
    have h2 := hg.elemental u v huv S hu hv
    have h3 := hG u v huv hnon S hu hv
    rw [← he, delta_add] at h3
    constructor <;> linarith
  exact ⟨fun u v huv hnon S hu hv => (hall u v huv hnon S hu hv).1,
    fun u v huv hnon S hu hv => (hall u v huv hnon S hu hv).2⟩

/-- An actual nonzero normalized supermodular function has a positive slack. -/
theorem exists_positive_delta {z : SetFunction V} (hn : TranslationNormalized z)
    (hs : Supermodular z) (hne : z ≠ 0) :
    ∃ u v, u ≠ v ∧ ∃ S, u ∉ S ∧ v ∉ S ∧ 0 < delta z u v S := by
  by_contra h
  push_neg at h
  apply hne
  apply normalized_zero_elemental_eq_zero hn
  intro u v huv S hu hv
  exact le_antisymm (h u v huv S hu hv) (hs.elemental u v huv S hu hv)

/-- The common-tight-equation criterion is sufficient for extremality, without
assuming a positive coefficient for the putative scalar in advance. -/
theorem extremeSupermodular_of_tightEquations {z : SetFunction V}
    (hn : TranslationNormalized z) (hs : Supermodular z) (hne : z ≠ 0)
    (hker : ∀ f : SetFunction V, TranslationNormalized f →
      (∀ u v, u ≠ v → ∀ S, u ∉ S → v ∉ S →
        delta z u v S = 0 → delta f u v S = 0) →
      ∃ a : ℝ, f = a • z) : ExtremeSupermodular z := by
  refine ⟨hn, hs, hne, ?_⟩
  intro f g hnf hng hsf hsg he
  have hzeros : ∀ u v, u ≠ v → ∀ S, u ∉ S → v ∉ S →
      delta z u v S = 0 → delta f u v S = 0 := by
    intro u v huv S hu hv hz
    have h1 := hsf.elemental u v huv S hu hv
    have h2 := hsg.elemental u v huv S hu hv
    rw [← he, delta_add] at hz
    linarith
  obtain ⟨a, ha⟩ := hker f hnf hzeros
  refine ⟨a, ?_, ha⟩
  obtain ⟨u, v, huv, S, hu, hv, hpos⟩ := exists_positive_delta hn hs hne
  have h := hsf.elemental u v huv S hu hv
  rw [ha, delta_smul] at h
  exact nonneg_of_mul_nonneg_left h hpos

end GraphicalZonotopes

end
end
end BundlePart7

section BundlePart8
/- Source: Papers/GraphicalZonotopes/GraphModels.lean -/








@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def edgeFamily (G : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact univ.filter (fun C => C.card = 2 ∧ ∀ u ∈ C, ∀ v ∈ C, u ≠ v → G.Adj u v)

@[simp] theorem mem_edgeFamily (G : SimpleGraph V) (C : Finset V) :
    C ∈ edgeFamily G ↔ C.card = 2 ∧ ∀ u ∈ C, ∀ v ∈ C, u ≠ v → G.Adj u v := by
  classical
  simp [edgeFamily]

@[simp] theorem pair_mem_edgeFamily (G : SimpleGraph V) {u v : V} (huv : u ≠ v) :
    ({u, v} : Finset V) ∈ edgeFamily G ↔ G.Adj u v := by
  classical
  rw [mem_edgeFamily]
  simp only [card_pair huv, true_and, mem_insert, mem_singleton]
  constructor
  · intro h
    exact h u (Or.inl rfl) v (Or.inr rfl) huv
  · intro h i hi j hj hij
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact False.elim (hij rfl)
    · exact h
    · exact G.adj_symm h
    · exact False.elim (hij rfl)

def cliqueGraph (C : Finset V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ u ∈ C ∧ v ∈ C
  symm := ⟨by intros; tauto⟩
  loopless := ⟨by intro v; simp⟩

def attachmentStar (u : V) (T : Finset V) : SimpleGraph V where
  Adj v w := v ≠ w ∧ ((v = u ∧ w ∈ T) ∨ (w = u ∧ v ∈ T))
  symm := ⟨by intros; tauto⟩
  loopless := ⟨by intro v; simp⟩

/-- The ordinary recursive definition of a 3-tree, on its complete active
vertex set. Vertices outside `S` are isolated throughout the construction. -/
inductive ThreeTreeOn : Finset V → SimpleGraph V → Prop
  | tetrahedron (C : Finset V) (hC : C.card = 4) : ThreeTreeOn C (cliqueGraph C)
  | attach {S : Finset V} {G : SimpleGraph V} (h : ThreeTreeOn S G)
      (u : V) (hu : u ∉ S) (T : Finset V) (hT : T.card = 3)
      (hTS : T ⊆ S) (hcl : G.IsClique T) :
      ThreeTreeOn (insert u S) (G ⊔ attachmentStar u T)

def IsThreeTree (G : SimpleGraph V) : Prop := ThreeTreeOn univ G

def tetrahedra (G : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact univ.filter (fun C => C.card = 4 ∧ G.IsClique C)

def triangleMultiplicity (G : SimpleGraph V) (T : Finset V) : ℕ := by
  classical
  exact ((tetrahedra G).filter (fun C => T ⊆ C)).card

def Admissible (G : SimpleGraph V) : Prop :=
  ∀ T : Finset V, T.card = 3 → G.IsClique T → triangleMultiplicity G T ≤ 3

def HasAdmissibleSpanningThreeTree (G : SimpleGraph V) : Prop :=
  ∃ H : SimpleGraph V, H ≤ G ∧ IsThreeTree H ∧ Admissible H


def cliqueBook (s k : ℕ) : SimpleGraph (Fin s ⊕ Fin k) where
  Adj u v := u ≠ v ∧ (u.isLeft ∨ v.isLeft)
  symm := ⟨by intros; tauto⟩
  loopless := ⟨by intro v; simp⟩

def cliqueCapacity (s : ℕ) : ℕ :=
  s.choose 2 * 2^(s-2) - (2^s-s-1) + 1

def saturatedHubNeighbors (s : ℕ) : ℕ :=
  if s = 2 then 1 else cliqueCapacity s - cliqueCapacity (s-1) + 1

def fourPartite (a : Fin 4 → ℕ) : SimpleGraph (Σ i : Fin 4, Fin (a i)) :=
  SimpleGraph.completeMultipartiteGraph (fun i => Fin (a i))

def twoSingletonGraph (p b : ℕ) := fourPartite ![1,1,p,b]

def doubledPartGraph (r : ℕ) : SimpleGraph (Fin r × Fin 2) where
  Adj u v := u.1 ≠ v.1
  symm := ⟨fun _ _ => Ne.symm⟩
  loopless := ⟨fun _ h => h rfl⟩


end GraphicalZonotopes

end
end
end BundlePart8

section BundlePart9
/- Source: Papers/GraphicalZonotopes/Zonotope.lean -/





@[expose] public section

/-! Graphical zonotopes as genuine Minkowski sums of standard-basis segments. -/
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

def basisVector (v : V) : V → ℝ := Pi.single v 1

@[simp] theorem subsetSum_basisVector (v : V) (S : Finset V) :
    subsetSum (basisVector v) S = if v ∈ S then 1 else 0 := by
  simp [subsetSum, basisVector, Pi.single_apply, eq_comm]

theorem setMonomial_supermodular (C : Finset V) : Supermodular (setMonomial C) := by
  apply ElementallyNonnegative.supermodular
  intro u v huv S hu hv
  rw [delta_setMonomial huv hu hv]
  split <;> norm_num

theorem setMonomial_normalized {C : Finset V} (hC : C.Nonempty) :
    Normalized (setMonomial C) := by
  simp [Normalized, setMonomial, hC.ne_empty]

theorem basisVector_mem_basePair {u v : V} (huv : u ≠ v) :
    basisVector u ∈ basePolytope (setMonomial ({u, v} : Finset V)) := by
  refine ⟨by simp [setMonomial], ?_⟩
  intro S
  rw [subsetSum_basisVector]
  unfold setMonomial
  by_cases h : ({u, v} : Finset V) ⊆ S
  · have hu : u ∈ S := h (by simp)
    simp [h, hu]
  · simp only [if_neg h]
    split_ifs <;> norm_num

theorem basePair_eq_segment {u v : V} (huv : u ≠ v) :
    basePolytope (setMonomial ({u, v} : Finset V)) =
      segment ℝ (basisVector u) (basisVector v) := by
  apply Set.Subset.antisymm
  · intro x hx
    have htotal : subsetSum x univ = 1 := by simpa [setMonomial] using hx.1
    have hnonneg : ∀ j, 0 ≤ x j := by
      intro j
      have hpair : ¬({u, v} : Finset V) ⊆ {j} := by
        simp only [insert_subset_iff, singleton_subset_iff, mem_singleton]
        rintro ⟨rfl, rfl⟩
        exact huv rfl
      simpa [setMonomial, hpair, subsetSum] using hx.2 {j}
    have hzero : ∀ j, j ≠ u → j ≠ v → x j = 0 := by
      intro j hju hjv
      have hpair : ({u, v} : Finset V) ⊆ univ.erase j := by
        simp [insert_subset_iff, singleton_subset_iff, Ne.symm hju, Ne.symm hjv]
      have hmin : 1 ≤ subsetSum x (univ.erase j) := by
        simpa [setMonomial, hpair] using hx.2 (univ.erase j)
      have hsum : subsetSum x (univ.erase j) + x j = 1 := by
        rw [subsetSum, sum_erase_add _ _ (mem_univ j)]
        exact htotal
      linarith [hnonneg j]
    have hsupport : subsetSum x ({u, v} : Finset V) = subsetSum x univ := by
      apply sum_subset (subset_univ _)
      intro j hj hnot
      exact hzero j (fun h => hnot (by simp [h])) (fun h => hnot (by simp [h]))
    have hsum : x u + x v = 1 := by
      simpa [subsetSum, huv] using hsupport.trans htotal
    refine ⟨x u, x v, hnonneg u, hnonneg v, hsum, ?_⟩
    funext j
    by_cases hju : j = u
    · subst j
      simp [basisVector, Ne.symm huv]
    · by_cases hjv : j = v
      · subst j
        simp [basisVector, huv]
      · simp [basisVector, Pi.single_apply, hju, hjv, hzero j hju hjv,
          Ne.symm hju, Ne.symm hjv]
  · apply (basePolytope_convex _).segment_subset (basisVector_mem_basePair huv)
    simpa [pair_comm u v] using basisVector_mem_basePair (Ne.symm huv)

/-- Convex hull of the standard basis vectors indexed by a finite set. On a
two-element set this is precisely the standard-basis segment. -/
def coordinateSimplex (C : Finset V) : Set (V → ℝ) :=
  convexHull ℝ (basisVector '' (C : Set V))

theorem coordinateSimplex_pair (u v : V) :
    coordinateSimplex ({u, v} : Finset V) = segment ℝ (basisVector u) (basisVector v) := by
  simp [coordinateSimplex, convexHull_pair]

theorem baseMonomial_eq_coordinateSimplex {C : Finset V} (hC : C.card = 2) :
    basePolytope (setMonomial C) = coordinateSimplex C := by
  obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp hC
  rw [coordinateSimplex_pair, basePair_eq_segment huv]

@[simp] theorem basePolytope_zero : basePolytope (0 : SetFunction V) = {0} := by
  have hn : Normalized (0 : SetFunction V) := rfl
  have hs : Supermodular (0 : SetFunction V) := by intro A B; simp
  rw [basePolytope_eq_convexHull hn hs]
  have he : greedyPoints (0 : SetFunction V) = {0} := by
    ext x
    constructor
    · rintro ⟨e, rfl⟩
      change greedyPoint (0 : SetFunction V) e = 0
      funext v
      simp [greedyPoint]
    · rintro rfl
      exact ⟨(Fintype.equivFin V).symm, by ext v; simp [greedyPoint]⟩
  rw [he, convexHull_singleton]

theorem Supermodular.finset_sum {I : Type*} (s : Finset I) (f : I → SetFunction V)
    (hs : ∀ i ∈ s, Supermodular (f i)) : Supermodular (∑ i ∈ s, f i) := by
  intro A B
  simp only [Finset.sum_apply]
  have h := sum_le_sum (fun i hi => hs i hi A B)
  simpa [sum_add_distrib] using h

theorem basePolytope_sum {I : Type*} (s : Finset I) (f : I → SetFunction V)
    (hn : ∀ i ∈ s, Normalized (f i)) (hs : ∀ i ∈ s, Supermodular (f i)) :
    basePolytope (∑ i ∈ s, f i) = ∑ i ∈ s, basePolytope (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty,basePolytope_zero]; rfl
  | @insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi]
    have hn' : Normalized (∑ j ∈ s, f j) := by
      simp only [Normalized, Finset.sum_apply]
      exact sum_eq_zero (fun j hj => hn j (mem_insert_of_mem hj))
    rw [basePolytope_add (hn i (mem_insert_self _ _)) hn'
      (hs i (mem_insert_self _ _)) (Supermodular.finset_sum s f (fun j hj => hs j (mem_insert_of_mem hj))),
      ih (fun j hj => hn j (mem_insert_of_mem hj)) (fun j hj => hs j (mem_insert_of_mem hj))]

/-- The lower set function counts edges in the induced subgraph. -/
def graphFunction (G : SimpleGraph V) : SetFunction V :=
  ∑ C ∈ edgeFamily G, setMonomial C

/-- The actual graphical zonotope, built by Minkowski summation of edge segments. -/
def graphicalZonotope (G : SimpleGraph V) : Set (V → ℝ) :=
  ∑ C ∈ edgeFamily G, coordinateSimplex C

theorem graphFunction_normalized (G : SimpleGraph V) : Normalized (graphFunction G) := by
  simp only [Normalized, graphFunction, Finset.sum_apply]
  apply sum_eq_zero
  intro C hC
  have hc := (mem_edgeFamily G C).mp hC
  exact setMonomial_normalized (card_pos.mp (by omega))

theorem graphFunction_supermodular (G : SimpleGraph V) : Supermodular (graphFunction G) :=
  Supermodular.finset_sum _ _ (fun C hC => setMonomial_supermodular C)

theorem baseGraphFunction_eq_graphicalZonotope (G : SimpleGraph V) :
    basePolytope (graphFunction G) = graphicalZonotope G := by
  rw [graphFunction, basePolytope_sum]
  · apply sum_congr rfl
    intro C hC
    exact baseMonomial_eq_coordinateSimplex ((mem_edgeFamily G C).mp hC).1
  · intro C hC
    have hc := ((mem_edgeFamily G C).mp hC).1
    exact setMonomial_normalized (card_pos.mp (by omega))
  · exact fun C hC => setMonomial_supermodular C

/-- The graphical zonotope has unit elemental slack on each graph edge, and
zero elemental slack on every nonedge, in every conditioning context. -/
theorem graphFunction_delta (G : SimpleGraph V) {u v : V} (huv : u ≠ v)
    {S : Finset V} (hu : u ∉ S) (hv : v ∉ S) :
    delta (graphFunction G) u v S = if G.Adj u v then 1 else 0 := by
  classical
  rw [graphFunction, delta_sum]
  have hrow : ∀ C ∈ edgeFamily G,
      delta (setMonomial C) u v S = if C = {u,v} then 1 else 0 := by
    intro C hC
    rw [delta_setMonomial huv hu hv]
    by_cases he : C = {u,v}
    · subst C
      simp
    · have hpair : ¬(u ∈ C ∧ v ∈ C) := by
        rintro ⟨huC,hvC⟩
        apply he
        apply Eq.symm
        apply Finset.eq_of_subset_of_card_le
        · intro w hw
          simp only [mem_insert, mem_singleton] at hw
          rcases hw with rfl | rfl <;> assumption
        · rw [(mem_edgeFamily G C).mp hC |>.1, card_pair huv]
      have hzero : ¬(u∈C ∧ v∈C ∧ C⊆insert u (insert v S)) := by tauto
      simp only [if_neg he,if_neg hzero]
  rw [sum_congr rfl hrow]
  simp [pair_mem_edgeFamily G huv]

theorem graphFunction_translationNormalized (G : SimpleGraph V) :
    TranslationNormalized (graphFunction G) := by
  refine ⟨graphFunction_normalized G, ?_⟩
  intro v
  simp only [graphFunction, Finset.sum_apply]
  apply sum_eq_zero
  intro C hC
  have hc := (mem_edgeFamily G C).mp hC |>.1
  have hnot : ¬C ⊆ {v} := by
    intro h
    have hcard := card_le_card h
    simp [hc] at hcard
  simp [setMonomial, hnot]

/-- Bounded genuine elemental slacks give an actual complementary base
polytope in the indicated dilation of the graphical zonotope. -/
theorem graphical_complement_supermodular {G : SimpleGraph V} {z : SetFunction V}
    (hG : Graphical G z) {a : ℝ} (ha : 0 ≤ a)
    (hub : ∀ u v, u ≠ v → G.Adj u v → ∀ S, u ∉ S → v ∉ S →
      delta z u v S ≤ a) : Supermodular (a • graphFunction G - z) := by
  apply ElementallyNonnegative.supermodular
  intro u v huv S hu hv
  rw [delta_sub, delta_smul, graphFunction_delta G huv hu hv]
  by_cases hedge : G.Adj u v
  · simp only [if_pos hedge, mul_one]
    exact sub_nonneg.mpr (hub u v huv hedge S hu hv)
  · rw [if_neg hedge, hG u v huv hedge S hu hv]
    simp

theorem basePolytope_add_graphical_complement {G : SimpleGraph V} {z : SetFunction V}
    (hn : Normalized z) (hs : Supermodular z) (hG : Graphical G z)
    {a : ℝ} (ha : 0 ≤ a)
    (hub : ∀ u v, u ≠ v → G.Adj u v → ∀ S, u ∉ S → v ∉ S →
      delta z u v S ≤ a) :
    basePolytope z + basePolytope (a • graphFunction G - z) = a • graphicalZonotope G := by
  have hcn : Normalized (a • graphFunction G - z) := by
    change a*graphFunction G ∅-z ∅=0
    rw [graphFunction_normalized G,hn]
    ring
  have hcs := graphical_complement_supermodular hG ha hub
  rw [← basePolytope_add hn hcn hs hcs]
  have he : z + (a • graphFunction G - z) = a • graphFunction G := by module
  rw [he, basePolytope_smul (graphFunction_normalized G) (graphFunction_supermodular G) ha,
    baseGraphFunction_eq_graphicalZonotope]

end GraphicalZonotopes

end
end
end BundlePart9

section BundlePart10
/- Source: Papers/GraphicalZonotopes/ConeCorrespondence.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Geometric indecomposability also implies extremality of the correctly
normalized function cone. Both directions of the dictionary are proved. -/
theorem MinkowskiIndecomposable.extremeSupermodular {z : SetFunction V}
    (hn : TranslationNormalized z) (hs : Supermodular z) (hne : z ≠ 0)
    (hi : MinkowskiIndecomposable (basePolytope z)) : ExtremeSupermodular z := by
  refine ⟨hn,hs,hne,?_⟩
  intro f g hfn hgn hfs hgs hfg
  have hsum : basePolytope f + basePolytope g = basePolytope z := by
    rw [← basePolytope_add hfn.1 hgn.1 hfs hgs,hfg]
  obtain ⟨a,t,ha,he⟩ := hi.2 (basePolytope f) (basePolytope g)
    (basePolytope_compact hfn.1 hfs) (basePolytope_compact hgn.1 hgs)
    (basePolytope_convex f) (basePolytope_convex g) hsum
  rw [← basePolytope_smul hn.1 hs ha,← basePolytope_translate] at he
  have hzn : Normalized (a • z+modular t) := by
    change a*z ∅+subsetSum t ∅=0
    rw [hn.1]
    simp [subsetSum]
  have hzs : Supermodular (a • z+modular t) := (hs.smul ha).add (modular_supermodular t)
  have hfun := congrArg lowerSupport he
  rw [lowerSupport_basePolytope hfn.1 hfs,lowerSupport_basePolytope hzn hzs] at hfun
  have ht : t = 0 := by
    funext v
    have h := congrFun hfun {v}
    simpa [hfn.2 v,hn.2 v,modular,subsetSum] using h.symm
  refine ⟨a,ha,?_⟩
  have htmod : modular t = 0 := by
    rw [ht]
    funext S
    simp [modular,subsetSum]
  rw [htmod,add_zero] at hfun
  exact hfun

theorem extremeSupermodular_iff_minkowskiIndecomposable {z : SetFunction V}
    (hn : TranslationNormalized z) (hs : Supermodular z) (hne : z ≠ 0) :
    ExtremeSupermodular z ↔ MinkowskiIndecomposable (basePolytope z) :=
  ⟨ExtremeSupermodular.minkowskiIndecomposable,
    MinkowskiIndecomposable.extremeSupermodular hn hs hne⟩

/-- Restricting the ambient cone to graphical functions introduces no spurious
extreme rays: every supermodular summand inherits the nonedge zero equations. -/
theorem extremeSupermodular_iff_graphical_decompositions {G : SimpleGraph V}
    {z : SetFunction V} (hn : TranslationNormalized z) (hs : Supermodular z)
    (hne : z ≠ 0) (hG : Graphical G z) :
    ExtremeSupermodular z ↔
      ∀ f g : SetFunction V, TranslationNormalized f → TranslationNormalized g →
        Supermodular f → Supermodular g → Graphical G f → Graphical G g →
        f+g=z → ∃ a : ℝ, 0 ≤ a ∧ f=a • z := by
  constructor
  · intro he f g hfn hgn hfs hgs _ _ hfg
    exact he.2.2.2 f g hfn hgn hfs hgs hfg
  · intro he
    refine ⟨hn,hs,hne,?_⟩
    intro f g hfn hgn hfs hgs hfg
    obtain ⟨hfG,hgG⟩ := hG.summands hfs hgs hfg
    exact he f g hfn hgn hfs hgs hfG hgG hfg

theorem basePolytope_is_singleton_iff {z : SetFunction V}
    (hn : TranslationNormalized z) (hs : Supermodular z) :
    (∃ p,basePolytope z={p}) ↔ z=0 := by
  constructor
  · rintro ⟨p,hp⟩
    have hmem : p ∈ basePolytope z := by rw [hp]; simp
    have hz : ∀ S,z S=subsetSum p S := by
      intro S
      obtain ⟨e,j,hj,he⟩ := exists_prefix_enumeration S
      have hg := greedyPoint_mem_basePolytope hn.1 hs e
      have hgp : greedyPoint z e=p := by simpa [hp] using hg
      have h := greedyPoint_prefix z hn.1 e j hj
      simpa [hgp,he] using h.symm
    have hp0 : p=0 := by
      funext v
      have h := hz {v}
      simpa [hn.2 v,subsetSum] using h.symm
    funext S
    simp [hz S,hp0,subsetSum]
  · rintro rfl
    exact ⟨0,basePolytope_zero⟩

end GraphicalZonotopes

end
end
end BundlePart10

section BundlePart11
/- Source: Papers/GraphicalZonotopes/CliqueCoordinates.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

def IsCliqueCoordinate (G : SimpleGraph V) (C : Finset V) : Prop :=
  2 ≤ C.card ∧ G.IsClique C

abbrev CliqueIndex (G : SimpleGraph V) := {C : Finset V // IsCliqueCoordinate G C}

noncomputable instance cliqueIndexFintype (G : SimpleGraph V) : Fintype (CliqueIndex G) := by
  classical
  infer_instance

def coefficientSpace (G : SimpleGraph V) : Submodule ℝ (SetFunction V) where
  carrier := {y | CliqueSupported G y}
  zero_mem' := by refine ⟨rfl,fun _ => rfl,?_⟩; intros; rfl
  add_mem' := by
    intro y y' hy hy'
    refine ⟨by simp [hy.1,hy'.1],fun v => by simp [hy.2.1 v,hy'.2.1 v],?_⟩
    intro C u v hu hv huv hnon
    simp [hy.2.2 C u v hu hv huv hnon,hy'.2.2 C u v hu hv huv hnon]
  smul_mem' := by
    intro a y hy
    refine ⟨by simp [hy.1],fun v => by simp [hy.2.1 v],?_⟩
    intro C u v hu hv huv hnon
    simp [hy.2.2 C u v hu hv huv hnon]

theorem coefficient_zero_of_not_clique {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y) (C : Finset V) (hC : ¬IsCliqueCoordinate G C) : y C=0 := by
  classical
  by_cases hc : 2 ≤ C.card
  · by_contra hn
    apply hC
    refine ⟨hc,?_⟩
    intro u hu v hv huv
    by_contra hnon
    exact hn (hy.2.2 C u v hu hv huv hnon)
  · have hc' : C.card=0 ∨ C.card=1 := by omega
    rcases hc' with he | he
    · rw [card_eq_zero.mp he,hy.1]
    · obtain ⟨v,rfl⟩ := card_eq_one.mp he
      exact hy.2.1 v

def coefficientsFromCoordinates (G : SimpleGraph V) (c : CliqueIndex G → ℝ) : SetFunction V := by
  classical
  exact fun C => if h : IsCliqueCoordinate G C then c ⟨C,h⟩ else 0

theorem coefficientsFromCoordinates_supported (G : SimpleGraph V) (c : CliqueIndex G → ℝ) :
    CliqueSupported G (coefficientsFromCoordinates G c) := by
  classical
  refine ⟨?_,?_,?_⟩
  · simp [coefficientsFromCoordinates,IsCliqueCoordinate]
  · intro v
    simp [coefficientsFromCoordinates,IsCliqueCoordinate]
  · intro C u v hu hv huv hnon
    have hC : ¬IsCliqueCoordinate G C := by
      intro hc
      exact hnon (hc.2 hu hv huv)
    simp [coefficientsFromCoordinates,hC]

/-- Exactly all normalized clique coefficients, with no missing zero slots. -/
def cliqueCoefficientEquiv (G : SimpleGraph V) :
    (CliqueIndex G → ℝ) ≃ₗ[ℝ] coefficientSpace G where
  toFun c := ⟨coefficientsFromCoordinates G c,coefficientsFromCoordinates_supported G c⟩
  invFun y C := y.1 C.1
  left_inv c := by
    funext C
    simp [coefficientsFromCoordinates,C.2]
  right_inv y := by
    apply Subtype.ext
    funext C
    by_cases hC : IsCliqueCoordinate G C
    · simp [coefficientsFromCoordinates,hC]
    · simp [coefficientsFromCoordinates,hC,coefficient_zero_of_not_clique y.2 C hC]
  map_add' c d := by
    apply Subtype.ext
    funext C
    by_cases hC : IsCliqueCoordinate G C <;> simp [coefficientsFromCoordinates,hC]
  map_smul' a c := by
    apply Subtype.ext
    funext C
    by_cases hC : IsCliqueCoordinate G C <;> simp [coefficientsFromCoordinates,hC]

def graphicalFunctionSpace (G : SimpleGraph V) : Submodule ℝ (SetFunction V) where
  carrier := {z | TranslationNormalized z ∧ Graphical G z}
  zero_mem' := by
    refine ⟨⟨rfl,fun _ => rfl⟩,?_⟩
    intro u v huv hnon S hu hv
    simp [delta]
  add_mem' := by
    intro f g hf hg
    refine ⟨⟨?_,?_⟩,?_⟩
    · change f ∅+g ∅=0
      rw [hf.1.1,hg.1.1,add_zero]
    · intro v
      change f {v}+g {v}=0
      rw [hf.1.2 v,hg.1.2 v,add_zero]
    · intro u v huv hnon S hu hv
      rw [delta_add,hf.2 u v huv hnon S hu hv,hg.2 u v huv hnon S hu hv,add_zero]
  smul_mem' := by
    intro a f hf
    refine ⟨⟨?_,?_⟩,?_⟩
    · change a*f ∅=0
      rw [hf.1.1,mul_zero]
    · intro v
      change a*f {v}=0
      rw [hf.1.2 v,mul_zero]
    · intro u v huv hnon S hu hv
      rw [delta_smul,hf.2 u v huv hnon S hu hv,mul_zero]

/-- Möbius inversion restricted to the exact normalized graphical function
space. Its inverse is the actual finite lower-set sum. -/
def graphicalZetaEquiv (G : SimpleGraph V) :
    coefficientSpace G ≃ₗ[ℝ] graphicalFunctionSpace G where
  toFun y := ⟨zeta y.1,(cliqueSupported_iff G y.1).mp y.2⟩
  invFun z := ⟨mobius z.1,(mobius_cliqueSupported_iff G z.1).mpr z.2⟩
  left_inv y := Subtype.ext (mobius_zeta y.1)
  right_inv z := Subtype.ext (zeta_mobius z.1)
  map_add' y y' := Subtype.ext (zetaLinear.map_add y.1 y'.1)
  map_smul' a y := Subtype.ext (zetaLinear.map_smul a y.1)

def graphicalCoordinatesEquiv (G : SimpleGraph V) :
    (CliqueIndex G → ℝ) ≃ₗ[ℝ] graphicalFunctionSpace G :=
  (cliqueCoefficientEquiv G).trans (graphicalZetaEquiv G)

theorem graphicalFunctionSpace_finrank (G : SimpleGraph V) :
    Module.finrank ℝ (graphicalFunctionSpace G) = Fintype.card (CliqueIndex G) := by
  rw [← (graphicalCoordinatesEquiv G).finrank_eq,Module.finrank_fintype_fun_eq_card]

/-- The elemental-row map is injective on the normalized graphical space.
This also proves that its nonnegative cone is pointed. -/
theorem graphical_function_eq_zero_of_elemental_zero (G : SimpleGraph V)
    (z : graphicalFunctionSpace G)
    (hz : ∀ u v, u ≠ v → ∀ S, u ∉ S → v ∉ S → delta z.1 u v S=0) : z=0 := by
  apply Subtype.ext
  exact normalized_zero_elemental_eq_zero z.2.1 hz

end GraphicalZonotopes

end
end
end BundlePart11

section BundlePart12
/- Source: Papers/GraphicalZonotopes/FiniteMonomialCoordinates.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace FiniteMonomial
open Finset
open scoped BigOperators
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

/-- A displayed finite list of genuine squarefree Boolean monomials. -/
def polynomial (C : I → Finset V) (x : I → ℝ) : SetFunction V :=
  ∑ i, x i • setMonomial (C i)

theorem polynomial_smul (C : I → Finset V) (x : I → ℝ) (a : ℝ) :
    polynomial C (a • x) = a • polynomial C x := by
  simp only [polynomial,smul_sum,Pi.smul_apply,smul_smul,smul_eq_mul]

theorem delta_polynomial (C : I → Finset V) (x : I → ℝ)
    {u v : V} (huv : u≠ v) {S : Finset V} (hu : u∉S) (hv : v∉S) :
    delta (polynomial C x) u v S =
      ∑ i, if u∈C i ∧ v∈C i ∧ C i⊆insert u (insert v S) then x i else 0 := by
  rw [polynomial,delta_sum]
  apply sum_congr rfl
  intro i hi
  rw [delta_smul,delta_setMonomial huv hu hv]
  split_ifs <;> simp

/-- A complete injective clique enumeration recovers every actual normalized
graphical set function from its Möbius coordinates. -/
theorem graphical_eq_polynomial {G : SimpleGraph V} (C : I → Finset V)
    (hinj : Function.Injective C)
    (hcover : ∀ D : Finset V, IsCliqueCoordinate G D → ∃ i,C i=D)
    {f : SetFunction V} (hn : TranslationNormalized f) (hG : Graphical G f) :
    f=polynomial C (fun i => mobius f (C i)) := by
  have hy := (mobius_cliqueSupported_iff G f).mpr ⟨hn,hG⟩
  conv_lhs => rw [← zeta_mobius f,zeta_eq_sum_monomials]
  change (∑ D : Finset V,mobius f D • setMonomial D)=
    ∑ i : I,mobius f (C i) • setMonomial (C i)
  rw [← sum_image (f := fun D => mobius f D • setMonomial D)
    (fun i _ j _ hij => hinj hij)]
  symm
  apply sum_subset (subset_univ _)
  intro D hD hnot
  have hncl : ¬IsCliqueCoordinate G D := by
    intro hd
    obtain ⟨i,rfl⟩ := hcover D hd
    exact hnot (mem_image.mpr ⟨i,mem_univ _,rfl⟩)
  rw [coefficient_zero_of_not_clique hy D hncl,zero_smul]

theorem polynomial_normalized (C : I → Finset V)
    (hcard : ∀ i,2≤(C i).card) (x : I → ℝ) :
    TranslationNormalized (polynomial C x) := by
  constructor
  · change (∑ i,x i • setMonomial (C i)) ∅=0
    rw [Finset.sum_apply]
    apply sum_eq_zero
    intro i hi
    have hne : ¬C i⊆∅ := by
      intro he
      have := card_le_card he
      have := hcard i
      simp only [card_empty] at *
      omega
    simp [setMonomial,hne]
  · intro v
    change (∑ i,x i • setMonomial (C i)) {v}=0
    rw [Finset.sum_apply]
    apply sum_eq_zero
    intro i hi
    have hne : ¬C i⊆{v} := by
      intro he
      have := card_le_card he
      have := hcard i
      simp only [card_singleton] at *
      omega
    simp [setMonomial,hne]

theorem polynomial_graphical {G : SimpleGraph V} (C : I → Finset V)
    (hclique : ∀ i,G.IsClique (C i)) (x : I → ℝ) :
    Graphical G (polynomial C x) := by
  intro u v huv hnon S hu hv
  rw [delta_polynomial C x huv hu hv]
  apply sum_eq_zero
  intro i hi
  have hfalse : ¬(u∈C i ∧ v∈C i ∧ C i⊆insert u (insert v S)) := by
    rintro ⟨huC,hvC,hsub⟩
    exact hnon (hclique i huC hvC huv)
  rw [if_neg hfalse]

end FiniteMonomial
end GraphicalZonotopes

end
end
end BundlePart12

section BundlePart13
/- Source: Papers/GraphicalZonotopes/DiamondGenerated.lean -/










/-! UNCOMPILED auxiliary linear certificate. Actual row correspondence,
geometric wrappers, and all unbounded theorems still require Lean checking. -/

@[expose] public section

namespace GraphicalZonotopes.DiamondGenerated

set_option maxRecDepth 100000

def cliqueMasks : Fin 57 → ℕ :=
  ![3, 5, 6, 7, 9, 10, 11, 17, 18, 19, 24, 25, 26, 27, 33, 34, 35, 40, 41, 42, 43, 65, 66, 67, 68, 69, 70, 71, 129, 130, 131, 132, 133, 134, 135, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523]

def coefficients : Fin 57 → ℝ :=
  ![1, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, -1, 0, 0, 2, 0, 0, 2, -2, 0, 0, 1, 0, 1, 0, -1, 0, 1, 0, 0, 1, 0, -1, 0, 1, 0, 1, 0, -1, 1, 0, 1, 0, -1, 1, 1, -1, 1, 0, -1, 1, 1, -1, 0, 1]

theorem kernel_line (x : Fin 57 → ℝ)
    -- h0: tight row 33.
    (h0 : x 0 + x 3 + x 30 + x 34 = 0)
    -- h1: tight row 37.
    (h1 : x 0 + x 3 + x 9 + x 30 + x 34 = 0)
    -- h2: tight row 39.
    (h2 : x 0 + x 3 + x 6 + x 9 + x 13 + x 30 + x 34 = 0)
    -- h3: tight row 47.
    (h3 : x 0 + x 3 + x 6 + x 9 + x 13 + x 16 + x 20 + x 30 + x 34 = 0)
    -- h4: tight row 49.
    (h4 : x 0 + x 3 + x 23 + x 27 + x 30 + x 34 = 0)
    -- h5: tight row 70.
    (h5 : x 0 + x 6 + x 9 + x 13 + x 37 + x 45 = 0)
    -- h6: tight row 102.
    (h6 : x 0 + x 6 + x 9 + x 13 + x 30 + x 37 + x 45 = 0)
    -- h7: tight row 103.
    (h7 : x 0 + x 3 + x 6 + x 9 + x 13 + x 30 + x 34 + x 37 + x 41 + x 45 = 0)
    -- h8: tight row 128.
    (h8 : x 0 + x 48 = 0)
    -- h9: tight row 161.
    (h9 : x 0 + x 3 + x 30 + x 34 + x 48 + x 52 = 0)
    -- h10: tight row 192.
    (h10 : x 0 + x 37 + x 48 = 0)
    -- h11: tight row 198.
    (h11 : x 0 + x 6 + x 9 + x 13 + x 37 + x 45 + x 48 + x 56 = 0)
    -- h12: tight row 256.
    (h12 : x 1 = 0)
    -- h13: tight row 257.
    (h13 : x 1 + x 3 = 0)
    -- h14: tight row 259.
    (h14 : x 1 + x 3 + x 25 + x 27 = 0)
    -- h15: tight row 261.
    (h15 : x 1 + x 3 + x 32 + x 34 = 0)
    -- h16: tight row 264.
    (h16 : x 1 + x 39 = 0)
    -- h17: tight row 272.
    (h17 : x 1 + x 50 = 0)
    -- h18: tight row 295.
    (h18 : x 2 + x 3 + x 26 + x 27 + x 33 + x 34 = 0)
    -- h19: tight row 303.
    (h19 : x 2 + x 3 + x 26 + x 27 + x 33 + x 34 + x 40 + x 41 = 0)
    -- h20: tight row 311.
    (h20 : x 2 + x 3 + x 26 + x 27 + x 33 + x 34 + x 51 + x 52 = 0)
    -- h21: tight row 312.
    (h21 : x 2 + x 40 + x 51 = 0)
    -- h22: tight row 314.
    (h22 : x 2 + x 26 + x 40 + x 51 = 0)
    -- h23: tight row 316.
    (h23 : x 2 + x 33 + x 40 + x 51 = 0)
    -- h24: tight row 325.
    (h24 : x 4 + x 6 + x 18 + x 20 = 0)
    -- h25: tight row 327.
    (h25 : x 4 + x 6 + x 11 + x 13 + x 18 + x 20 = 0)
    -- h26: tight row 333.
    (h26 : x 4 + x 6 + x 18 + x 20 + x 43 + x 45 = 0)
    -- h27: tight row 336.
    (h27 : x 4 + x 54 = 0)
    -- h28: tight row 340.
    (h28 : x 4 + x 18 + x 54 = 0)
    -- h29: tight row 341.
    (h29 : x 4 + x 6 + x 18 + x 20 + x 54 + x 56 = 0)
    -- h30: tight row 352.
    (h30 : x 5 = 0)
    -- h31: tight row 360.
    (h31 : x 5 + x 44 = 0)
    -- h32: tight row 361.
    (h32 : x 5 + x 6 + x 44 + x 45 = 0)
    -- h33: tight row 363.
    (h33 : x 5 + x 6 + x 12 + x 13 + x 44 + x 45 = 0)
    -- h34: tight row 365.
    (h34 : x 5 + x 6 + x 19 + x 20 + x 44 + x 45 = 0)
    -- h35: tight row 368.
    (h35 : x 5 + x 55 = 0)
    -- h36: tight row 384.
    (h36 : x 7 = 0)
    -- h37: tight row 388.
    (h37 : x 8 = 0)
    -- h38: tight row 392.
    (h38 : x 14 = 0)
    -- h39: tight row 396.
    (h39 : x 15 = 0)
    -- h40: tight row 400.
    (h40 : x 21 = 0)
    -- h41: tight row 404.
    (h41 : x 22 = 0)
    -- h42: tight row 408.
    (h42 : x 28 = 0)
    -- h43: tight row 415.
    (h43 : x 29 + x 30 + x 33 + x 34 = 0)
    -- h44: tight row 416.
    (h44 : x 35 = 0)
    -- h45: tight row 426.
    (h45 : x 36 + x 40 = 0)
    -- h46: tight row 433.
    (h46 : x 46 + x 48 = 0)
    -- h47: tight row 441.
    (h47 : x 47 + x 48 = 0)
    -- h48: tight row 448.
    (h48 : x 10 = 0)
    -- h49: tight row 452.
    (h49 : x 17 = 0)
    -- h50: tight row 456.
    (h50 : x 24 = 0)
    -- h51: tight row 460.
    (h51 : x 31 = 0)
    -- h52: tight row 466.
    (h52 : x 38 + x 40 = 0)
    -- h53: tight row 468.
    (h53 : x 42 = 0)
    -- h54: tight row 474.
    (h54 : x 49 + x 51 = 0)
    -- h55: tight row 477.
    (h55 : x 53 + x 54 = 0)
    : ∀ i : Fin 57, x i = coefficients i * x 0 := by
  intro i
  fin_cases i
  · norm_num [coefficients]
  · norm_num [coefficients]
    linear_combination h12
  · norm_num [coefficients]
    linear_combination -2 * h0 - h5 + h7 - h8 + h9 + 2 * h18 - h19 - h20 + h21
  · norm_num [coefficients]
    linear_combination -h12 + h13
  · norm_num [coefficients]
    linear_combination -h5 - h8 + h11 + h24 + h27 - h29
  · norm_num [coefficients]
    linear_combination h30
  · norm_num [coefficients]
    linear_combination -h0 + h2 - h5 - h8 + h10 - h31 + h32
  · norm_num [coefficients]
    linear_combination h36
  · norm_num [coefficients]
    linear_combination h37
  · norm_num [coefficients]
    linear_combination -h0 + h1
  · norm_num [coefficients]
    linear_combination h48
  · norm_num [coefficients]
    linear_combination -h0 + h1 - h5 - h8 + h10 - h24 + h25 - h31 + h32
  · norm_num [coefficients]
    linear_combination -h0 + h1 - h5 - h8 + h10 - h31 + h33
  · norm_num [coefficients]
    linear_combination h0 - h1 + h5 + h8 - h10 + h31 - h32
  · norm_num [coefficients]
    linear_combination h38
  · norm_num [coefficients]
    linear_combination h39
  · norm_num [coefficients]
    linear_combination -h0 + h3 - 2 * h5 - 2 * h8 + h10 + h11 + h28 - h29 - h31 + h32
  · norm_num [coefficients]
    linear_combination h49
  · norm_num [coefficients]
    linear_combination -h27 + h28
  · norm_num [coefficients]
    linear_combination -h0 + h2 - 2 * h5 - 2 * h8 + h10 + h11 + h28 - h29 - h31 + h34
  · norm_num [coefficients]
    linear_combination h0 - h2 + 2 * h5 + 2 * h8 - h10 - h11 - h28 + h29 + h31 - h32
  · norm_num [coefficients]
    linear_combination h40
  · norm_num [coefficients]
    linear_combination h41
  · norm_num [coefficients]
    linear_combination -2 * h0 + h4 - h6 + h7 - h8 + h9 + h18 - h19 - h20 - h21 + h22 + h23
  · norm_num [coefficients]
    linear_combination h50
  · norm_num [coefficients]
    linear_combination -h0 - h6 + h7 - h8 + h9 - h13 + h14 + h18 - h19 - h20 - h21 + h22 + h23
  · norm_num [coefficients]
    linear_combination -h21 + h22
  · norm_num [coefficients]
    linear_combination h0 + h6 - h7 + h8 - h9 - h18 + h19 + h20 + h21 - h22 - h23
  · norm_num [coefficients]
    linear_combination h42
  · norm_num [coefficients]
    linear_combination -h0 - h12 + h13 + h21 - h23 + h43
  · norm_num [coefficients]
    linear_combination -h5 + h6
  · norm_num [coefficients]
    linear_combination h51
  · norm_num [coefficients]
    linear_combination -h0 - h5 + h6 - h12 + h15
  · norm_num [coefficients]
    linear_combination -h21 + h23
  · norm_num [coefficients]
    linear_combination h0 + h5 - h6 + h12 - h13
  · norm_num [coefficients]
    linear_combination h44
  · norm_num [coefficients]
    linear_combination -h0 - h5 + h7 + h18 - h19 + h45
  · norm_num [coefficients]
    linear_combination -h8 + h10
  · norm_num [coefficients]
    linear_combination -h0 - h5 + h7 + h18 - h19 + h52
  · norm_num [coefficients]
    linear_combination -h12 + h16
  · norm_num [coefficients]
    linear_combination h0 + h5 - h7 - h18 + h19
  · norm_num [coefficients]
    linear_combination -h0 - h5 + h7
  · norm_num [coefficients]
    linear_combination h53
  · norm_num [coefficients]
    linear_combination -h0 + h2 - h5 - h8 + h10 - h24 + h26
  · norm_num [coefficients]
    linear_combination -h30 + h31
  · norm_num [coefficients]
    linear_combination h0 - h2 + h5 + h8 - h10
  · norm_num [coefficients]
    linear_combination -h8 + h46
  · norm_num [coefficients]
    linear_combination -h8 + h47
  · norm_num [coefficients]
    linear_combination h8
  · norm_num [coefficients]
    linear_combination -h0 - h8 + h9 + h18 - h20 + h54
  · norm_num [coefficients]
    linear_combination -h12 + h17
  · norm_num [coefficients]
    linear_combination h0 + h8 - h9 - h18 + h20
  · norm_num [coefficients]
    linear_combination -h0 - h8 + h9
  · norm_num [coefficients]
    linear_combination -h5 - h8 + h11 + h24 - h29 + h55
  · norm_num [coefficients]
    linear_combination h5 + h8 - h11 - h24 + h29
  · norm_num [coefficients]
    linear_combination -h30 + h35
  · norm_num [coefficients]
    linear_combination -h5 - h8 + h11

#print axioms kernel_line

end GraphicalZonotopes.DiamondGenerated


end
end BundlePart13

section BundlePart14
/- Source: Papers/GraphicalZonotopes/Lattice.lean -/




@[expose] public section

noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Integer-valued lower-support data in the fixed standard lattice. -/
def IntegerValued (z : SetFunction V) : Prop := ∀ S, ∃ a : ℤ, z S = (a : ℝ)

/-- Convex hull of finitely many standard integer coordinate vectors. -/
def LatticePolytope (Q : Set (V → ℝ)) : Prop :=
  ∃ P : Finset (V → ℤ), Q = convexHull ℝ ((fun x : V → ℤ => fun v => (x v : ℝ)) '' (P : Set (V → ℤ)))

def integerValue {z : SetFunction V} (hz : IntegerValued z) (S : Finset V) : ℤ :=
  Classical.choose (hz S)

@[simp] theorem cast_integerValue {z : SetFunction V} (hz : IntegerValued z) (S : Finset V) :
    (integerValue hz S : ℝ) = z S := (Classical.choose_spec (hz S)).symm

def integerGreedyPoint {z : SetFunction V} (hz : IntegerValued z)
    (e : Fin (Fintype.card V) ≃ V) (v : V) : ℤ :=
  integerValue hz (orderPrefix e ((e.symm v).val + 1)) -
    integerValue hz (orderPrefix e (e.symm v).val)

@[simp] theorem cast_integerGreedyPoint {z : SetFunction V} (hz : IntegerValued z)
    (e : Fin (Fintype.card V) ≃ V) :
    (fun v => (integerGreedyPoint hz e v : ℝ)) = greedyPoint z e := by
  funext v
  simp [integerGreedyPoint, greedyPoint]

theorem IntegerValued.basePolytope {z : SetFunction V} (hz : IntegerValued z)
    (hn : Normalized z) (hs : Supermodular z) : LatticePolytope (basePolytope z) := by
  classical
  let P : Finset (V → ℤ) := univ.image (integerGreedyPoint hz)
  refine ⟨P, ?_⟩
  rw [basePolytope_eq_convexHull hn hs]
  congr 1
  ext x
  constructor
  · rintro ⟨e, rfl⟩
    refine ⟨integerGreedyPoint hz e, ?_, cast_integerGreedyPoint hz e⟩
    simp [P]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨e, he, rfl⟩ := mem_image.mp hy
    exact ⟨e, (cast_integerGreedyPoint hz e).symm⟩

theorem IntegerValued.add {z w : SetFunction V} (hz : IntegerValued z)
    (hw : IntegerValued w) : IntegerValued (z + w) := by
  intro S
  obtain ⟨a, ha⟩ := hz S
  obtain ⟨b, hb⟩ := hw S
  exact ⟨a + b, by simp [ha, hb]⟩

theorem IntegerValued.sub {z w : SetFunction V} (hz : IntegerValued z)
    (hw : IntegerValued w) : IntegerValued (z - w) := by
  intro S
  obtain ⟨a, ha⟩ := hz S
  obtain ⟨b, hb⟩ := hw S
  exact ⟨a - b, by simp [ha, hb]⟩

theorem IntegerValued.int_smul {z : SetFunction V} (hz : IntegerValued z)
    (m : ℤ) : IntegerValued ((m : ℝ) • z) := by
  intro S
  obtain ⟨a, ha⟩ := hz S
  exact ⟨m * a, by simp [ha]⟩

theorem IntegerValued.finset_sum {I : Type*} (t : Finset I) (f : I → SetFunction V)
    (hf : ∀ i ∈ t, IntegerValued (f i)) : IntegerValued (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => intro S; exact ⟨0, by simp⟩
  | @insert i t hi ih =>
    rw [sum_insert hi]
    exact (hf i (mem_insert_self _ _)).add (ih (fun j hj => hf j (mem_insert_of_mem hj)))

theorem setMonomial_integerValued (C : Finset V) : IntegerValued (setMonomial C) := by
  intro S
  by_cases h : C ⊆ S
  · exact ⟨1, by simp [setMonomial, h]⟩
  · exact ⟨0, by simp [setMonomial, h]⟩

theorem zeta_integerValued {y : SetFunction V} (hy : IntegerValued y) :
    IntegerValued (zeta y) := by
  intro S
  refine ⟨∑ C ∈ S.powerset, integerValue hy C, ?_⟩
  simp [zeta]

theorem graphFunction_integerValued (G : SimpleGraph V) : IntegerValued (graphFunction G) :=
  IntegerValued.finset_sum _ _ (fun C hC => setMonomial_integerValued C)

end GraphicalZonotopes

end
end
end BundlePart14

section BundlePart15
/- Source: Papers/GraphicalZonotopes/Directions.lean -/





@[expose] public section

noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mem_orderPrefix_iff {n : ℕ} (e : Fin n ≃ V) (j : ℕ) (x : V) :
    x∈orderPrefix e j ↔ (e.symm x).val< j := by simp only [orderPrefix,mem_filter,mem_univ,true_and]

theorem card_orderPrefix {n : ℕ} (e : Fin n ≃ V) (j : ℕ) (hj : j ≤ n) :
    (orderPrefix e j).card = j := by
  have hm : orderPrefix e j = (univ.filter (fun i : Fin n => i.val < j)).map e.toEmbedding := by
    ext v
    simp [orderPrefix, Equiv.eq_symm_apply]
  rw [hm, card_map, Fin.card_filter_val_lt, Nat.min_eq_right hj]

theorem pair_enumeration_adjacent {n : ℕ} (e : Fin n ≃ V)
    (S : Finset V) {u v : V} (hu : u ∉ S)
    (h0 : orderPrefix e (e.symm u).val = S)
    (h1 : orderPrefix e (e.symm v).val = insert u S) :
    (e.symm v).val = (e.symm u).val + 1 := by
  have hc0 := congrArg Finset.card h0
  have hc1 := congrArg Finset.card h1
  rw [card_orderPrefix e _ (e.symm u).isLt.le] at hc0
  rw [card_orderPrefix e _ (e.symm v).isLt.le, card_insert_of_notMem hu] at hc1
  omega

/-- Swapping two adjacent coordinates leaves every other prefix unchanged. -/
theorem orderPrefix_swap_of_ne {n : ℕ} (e : Fin n ≃ V) {u v : V} (huv : u ≠ v)
    (hadj : (e.symm v).val = (e.symm u).val + 1) {j : ℕ}
    (hj : j ≠ (e.symm v).val) :
    orderPrefix (e.trans (Equiv.swap u v)) j = orderPrefix e j := by
  ext x
  rw [mem_orderPrefix_iff,mem_orderPrefix_iff]
  change (e.symm (Equiv.swap u v x)).val< j ↔ (e.symm x).val< j
  by_cases hxu : x = u
  · subst x
    simp only [Equiv.swap_apply_left]
    omega
  · by_cases hxv : x = v
    · subst x
      simp only [Equiv.swap_apply_right]
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne hxu hxv]

theorem orderPrefix_swap_middle {n : ℕ} (e : Fin n ≃ V) (S : Finset V)
    {u v : V} (huv : u ≠ v) (hu : u ∉ S) (hv : v ∉ S)
    (h0 : orderPrefix e (e.symm u).val = S)
    (h1 : orderPrefix e (e.symm v).val = insert u S) :
    orderPrefix (e.trans (Equiv.swap u v)) (e.symm v).val = insert v S := by
  have hadj := pair_enumeration_adjacent e S hu h0 h1
  ext x
  rw [mem_orderPrefix_iff,mem_insert]
  change (e.symm (Equiv.swap u v x)).val<(e.symm v).val ↔ x=v ∨ x∈S
  by_cases hxu : x = u
  · subst x
    simp [huv, hu]
  · by_cases hxv : x = v
    · subst x
      simp [hadj]
    · rw [Equiv.swap_apply_of_ne_of_ne hxu hxv]
      have hx0 : x ∈ S ↔ (e.symm x).val < (e.symm u).val := by
        rw [← h0]
        simp [orderPrefix]
      have hne : (e.symm x).val ≠ (e.symm u).val := by
        intro h
        exact hxu (e.symm.injective (Fin.ext h))
      simp only [hxv, false_or, hx0]
      omega

/-- The actual difference of the two neighboring greedy points is the elemental
slack times the corresponding standard root. -/
theorem greedyPoint_swap_difference {n : ℕ} (z : SetFunction V)
    (e : Fin n ≃ V) (S : Finset V) {u v : V} (huv : u ≠ v) (hu : u ∉ S) (hv : v ∉ S)
    (h0 : orderPrefix e (e.symm u).val = S)
    (h1 : orderPrefix e (e.symm v).val = insert u S) :
    greedyPoint z (e.trans (Equiv.swap u v)) - greedyPoint z e =
      delta z u v S • (basisVector u - basisVector v) := by
  let e' := e.trans (Equiv.swap u v)
  have hadj := pair_enumeration_adjacent e S hu h0 h1
  have h2 : orderPrefix e ((e.symm v).val + 1) = insert v (insert u S) := by
    rw [orderPrefix_succ, e.apply_symm_apply, h1]
  have hu0 : orderPrefix e' (e.symm u).val = S := by
    rw [orderPrefix_swap_of_ne e huv hadj (by omega), h0]
  have hv0 : orderPrefix e' (e.symm v).val = insert v S :=
    orderPrefix_swap_middle e S huv hu hv h0 h1
  have hv1 : orderPrefix e' ((e.symm v).val + 1) = insert v (insert u S) := by
    rw [orderPrefix_swap_of_ne e huv hadj (by omega), h2]
  have hu1 : orderPrefix e ((e.symm u).val + 1) = insert u S := by rw [← hadj, h1]
  have hu' : e'.symm u = e.symm v := by simp [e']
  have hv' : e'.symm v = e.symm u := by simp [e']
  change greedyPoint z e'-greedyPoint z e=delta z u v S • (basisVector u-basisVector v)
  funext x
  by_cases hxu : x = u
  · subst x
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,greedyPoint,hu',hv1,hv0,hu1,h0]
    simp [basisVector,Pi.single_apply,huv,Ne.symm huv,delta,insert_comm u v]
    <;> ring
  · by_cases hxv : x = v
    · subst x
      simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,greedyPoint,hv',h2,h1,h0,
        ← hadj,hv0,hu0]
      simp [basisVector,Pi.single_apply,huv,Ne.symm huv,delta,insert_comm u v]
      <;> ring
    · have hx' : e'.symm x = e.symm x := by simp [e', Equiv.swap_apply_of_ne_of_ne hxu hxv]
      have hru : (e.symm x).val ≠ (e.symm u).val := by
        intro h
        exact hxu (e.symm.injective (Fin.ext h))
      have hrv : (e.symm x).val ≠ (e.symm v).val := by
        intro h
        exact hxv (e.symm.injective (Fin.ext h))
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, greedyPoint, hx']
      rw [orderPrefix_swap_of_ne e huv hadj (by omega), orderPrefix_swap_of_ne e huv hadj hrv]
      simp [basisVector, Pi.single_apply, hxu, hxv, Ne.symm hxu, Ne.symm hxv]

/-- Every nonzero elemental difference places the genuine root direction in the
affine variation space of the genuine base polytope. -/
theorem root_mem_vectorSpan_of_delta_ne_zero {z : SetFunction V}
    (hn : Normalized z) (hs : Supermodular z) {u v : V} (huv : u ≠ v)
    {S : Finset V} (hu : u ∉ S) (hv : v ∉ S) (hδ : delta z u v S ≠ 0) :
    basisVector u - basisVector v ∈ vectorSpan ℝ (basePolytope z) := by
  obtain ⟨e, h0, h1⟩ := exists_pair_enumeration S huv hu hv
  have hmem := vsub_mem_vectorSpan ℝ
    (greedyPoint_mem_basePolytope hn hs (e.trans (Equiv.swap u v)))
    (greedyPoint_mem_basePolytope hn hs e)
  change greedyPoint z (e.trans (Equiv.swap u v)) - greedyPoint z e ∈ _ at hmem
  rw [greedyPoint_swap_difference z e S huv hu hv h0 h1] at hmem
  have h := (vectorSpan ℝ (basePolytope z)).smul_mem (delta z u v S)⁻¹ hmem
  simpa [smul_smul, inv_mul_cancel₀ hδ] using h

end GraphicalZonotopes

end
end
end BundlePart15

section BundlePart16
/- Source: Papers/GraphicalZonotopes/AffineDimension.lean -/






@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

def totalLinear : (V → ℝ) →ₗ[ℝ] ℝ where
  toFun x := subsetSum x univ
  map_add' x y := subsetSum_add x y univ
  map_smul' a x := subsetSum_smul a x univ

theorem vectorSpan_basePolytope_le_total_ker {z : SetFunction V}
    (hne : (basePolytope z).Nonempty) :
    vectorSpan ℝ (basePolytope z) ≤ (totalLinear (V := V)).ker := by
  obtain ⟨q,hq⟩ := hne
  rw [vectorSpan_eq_span_vsub_set_right ℝ hq]
  apply Submodule.span_le.mpr
  rintro x ⟨p,hp,rfl⟩
  change subsetSum (p-q) univ = 0
  rw [subsetSum_sub, hp.1, hq.1, sub_self]

theorem finrank_total_ker {n : ℕ} (hn : 0 < n) :
    Module.finrank ℝ (totalLinear (V := Fin n)).ker = n-1 := by
  let e : Fin n := ⟨0, hn⟩
  have hsurj : Function.Surjective (totalLinear (V := Fin n)) := by
    intro a
    refine ⟨a • basisVector e, ?_⟩
    change subsetSum (a • basisVector e) univ = a
    simp
  have hrange : (totalLinear (V := Fin n)).range = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have h := (totalLinear (V := Fin n)).ker.finrank_quotient_add_finrank
  rw [(totalLinear (V := Fin n)).quotKerEquivRange.finrank_eq, hrange] at h
  simp only [finrank_top, Module.finrank_self, Module.finrank_pi, Fintype.card_fin] at h
  omega

def zeroRoot {n : ℕ} (hn : 0 < n) (i : Fin (n-1)) : Fin n → ℝ :=
  basisVector ⟨i.val+1, by omega⟩ - basisVector ⟨0, hn⟩

theorem zeroRoot_evaluation {n : ℕ} (hn : 0 < n) (i j : Fin (n-1)) :
    zeroRoot hn i ⟨j.val+1, by omega⟩ = if i = j then 1 else 0 := by
  simp [zeroRoot, basisVector, Pi.single_apply, Fin.ext_iff, eq_comm]

theorem zeroRoot_linearIndependent {n : ℕ} (hn : 0 < n) :
    LinearIndependent ℝ (zeroRoot hn) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have h := congrFun hc (⟨j.val+1, by omega⟩ : Fin n)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, zeroRoot_evaluation] at h
  simpa using h

theorem all_zeroRoots_mem_of_consecutive {n : ℕ} (hn : 0 < n)
    (W : Submodule ℝ (Fin n → ℝ))
    (hW : ∀ i : Fin (n-1),
      basisVector (⟨i.val, by omega⟩ : Fin n) - basisVector ⟨i.val+1, by omega⟩ ∈ W) :
    ∀ i : Fin (n-1), zeroRoot hn i ∈ W := by
  have hroot : ∀ k : ℕ, ∀ hk : k< n,
      basisVector (⟨k,hk⟩ : Fin n) - basisVector ⟨0,hn⟩ ∈ W := by
    intro k
    induction k with
    | zero => intro hk; simp
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have hstep := hW ⟨k,by omega⟩
      have hh := W.sub_mem hprev hstep
      convert hh using 1 <;> module
  intro i
  exact hroot (i.val+1) (by omega)

theorem finrank_vectorSpan_eq_of_consecutive_roots {n : ℕ} {z : SetFunction (Fin n)}
    (hn : 0 < n) (hne : (basePolytope z).Nonempty)
    (hroots : ∀ i : Fin (n-1),
      basisVector (⟨i.val, by omega⟩ : Fin n) - basisVector ⟨i.val+1, by omega⟩ ∈
        vectorSpan ℝ (basePolytope z)) :
    Module.finrank ℝ (vectorSpan ℝ (basePolytope z)) = n-1 := by
  have hupper := Submodule.finrank_mono (vectorSpan_basePolytope_le_total_ker hne)
  rw [finrank_total_ker hn] at hupper
  have hspan : Submodule.span ℝ (Set.range (zeroRoot hn)) ≤ vectorSpan ℝ (basePolytope z) := by
    apply Submodule.span_le.mpr
    rintro x ⟨i,rfl⟩
    exact all_zeroRoots_mem_of_consecutive hn _ hroots i
  have hlower := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card (zeroRoot_linearIndependent hn), Fintype.card_fin] at hlower
  exact le_antisymm hupper hlower

end GraphicalZonotopes

end
end
end BundlePart16

section BundlePart17
/- Source: Papers/GraphicalZonotopes/ConnectedDimension.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The ambient zero-sum hyperplane has the expected dimension for every
finite nonempty vertex type, independently of a chosen enumeration. -/
theorem finrank_total_ker_fintype (v₀ : V) :
    Module.finrank ℝ (totalLinear (V := V)).ker=Fintype.card V-1 := by
  have hsurj : Function.Surjective (totalLinear (V := V)) := by
    intro a
    refine ⟨a • basisVector v₀,?_⟩
    change subsetSum (a • basisVector v₀) univ=a
    simp
  have hrange : (totalLinear (V := V)).range=⊤ := LinearMap.range_eq_top.mpr hsurj
  have h := (totalLinear (V := V)).ker.finrank_quotient_add_finrank
  rw [(totalLinear (V := V)).quotKerEquivRange.finrank_eq,hrange] at h
  simp only [finrank_top,Module.finrank_self,Module.finrank_pi] at h
  omega

def pointedRoot (v₀ : V) (v : {v : V // v≠ v₀}) : V → ℝ :=
  basisVector v.1-basisVector v₀

theorem pointedRoot_evaluation (v₀ : V) (v w : {v : V // v≠ v₀}) :
    pointedRoot v₀ v w.1=if v=w then 1 else 0 := by
  have hne : w.1≠ v₀ := w.2
  simp [pointedRoot,basisVector,Pi.single_apply,hne,Ne.symm hne,Subtype.ext_iff,eq_comm]

theorem pointedRoot_linearIndependent (v₀ : V) :
    LinearIndependent ℝ (pointedRoot v₀) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc w
  have h := congrFun hc w.1
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,pointedRoot_evaluation] at h
  simpa using h

theorem card_ne_subtype (v₀ : V) : Fintype.card {v : V // v≠ v₀}=Fintype.card V-1 := by
  simpa using Fintype.card_subtype_compl (fun v : V => v=v₀)

/-- Paths in an ordinary graph add their genuine root vectors. -/
theorem root_mem_of_reachable {G : SimpleGraph V} (W : Submodule ℝ (V → ℝ))
    (hW : ∀ u v,G.Adj u v → basisVector u-basisVector v∈W)
    {u v : V} (hpath : G.Reachable u v) : basisVector u-basisVector v∈W := by
  rw [SimpleGraph.reachable_eq_reflTransGen] at hpath
  induction hpath with
  | refl => simp
  | @tail v w hpath hstep ih =>
    have h := W.add_mem ih (hW v w hstep)
    convert h using 1 <;> module

/-- A connected set of actual root directions spans the entire zero-sum
hyperplane. This is an unbounded statement for arbitrary finite graphs. -/
theorem finrank_vectorSpan_eq_of_connected_roots {z : SetFunction V}
    (hne : (basePolytope z).Nonempty) {G : SimpleGraph V} (hG : G.Connected)
    (hroots : ∀ u v,G.Adj u v →
      basisVector u-basisVector v∈vectorSpan ℝ (basePolytope z)) :
    Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=Fintype.card V-1 := by
  obtain ⟨v₀⟩ := hG.nonempty
  have hu := Submodule.finrank_mono (vectorSpan_basePolytope_le_total_ker hne)
  rw [finrank_total_ker_fintype v₀] at hu
  have hspan : Submodule.span ℝ (Set.range (pointedRoot v₀))≤
      vectorSpan ℝ (basePolytope z) := by
    apply Submodule.span_le.mpr
    rintro x ⟨v,rfl⟩
    exact root_mem_of_reachable _ hroots (hG.preconnected v.1 v₀)
  have hl := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card (pointedRoot_linearIndependent v₀),card_ne_subtype v₀] at hl
  exact le_antisymm hu hl

theorem finrank_vectorSpan_eq_of_connected_slacks {z : SetFunction V}
    (hn : Normalized z) (hs : Supermodular z) {G : SimpleGraph V} (hG : G.Connected)
    (hslack : ∀ u v,G.Adj u v → ∃ S : Finset V,
      u∉S ∧ v∉S ∧ delta z u v S≠0) :
    Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=Fintype.card V-1 := by
  apply finrank_vectorSpan_eq_of_connected_roots (basePolytope_nonempty hn hs) hG
  intro u v huv
  obtain ⟨S,hu,hv,hd⟩ := hslack u v huv
  exact root_mem_vectorSpan_of_delta_ne_zero hn hs (G.ne_of_adj huv) hu hv hd

end GraphicalZonotopes

end
end
end BundlePart17
