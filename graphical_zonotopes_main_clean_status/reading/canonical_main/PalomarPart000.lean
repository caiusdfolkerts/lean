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

section BundlePart18
/- Source: Papers/GraphicalZonotopes/LatticeSupport.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem LatticePolytope.compact {Q : Set (V → ℝ)} (hQ : LatticePolytope Q) : IsCompact Q := by
  obtain ⟨P,rfl⟩ := hQ
  exact (P.finite_toSet.image _).isCompact_convexHull ℝ

theorem LatticePolytope.convex {Q : Set (V → ℝ)} (hQ : LatticePolytope Q) : Convex ℝ Q := by
  obtain ⟨P,rfl⟩ := hQ
  exact convex_convexHull ℝ _

/-- Integer lower-support values follow from a genuine lattice convex-hull
presentation; the converse direction of the lattice correspondence is explicit. -/
theorem LatticePolytope.lowerSupport_integerValued {Q : Set (V → ℝ)}
    (hQ : LatticePolytope Q) (hne : Q.Nonempty) : IntegerValued (lowerSupport Q) := by
  classical
  obtain ⟨P,rfl⟩ := hQ
  have hP : P.Nonempty := by
    by_contra h
    have hE : P = ∅ := not_nonempty_iff_eq_empty.mp h
    simp [hE] at hne
  intro S
  let vals : Finset ℤ := P.image (fun x => ∑ v ∈ S, x v)
  have hvals : vals.Nonempty := hP.image _
  let a : ℤ := vals.min' hvals
  have hamem : a ∈ vals := min'_mem _ _
  obtain ⟨p,hp,hpa⟩ := mem_image.mp hamem
  have hmin : ∀ q ∈ P, a ≤ ∑ v ∈ S, q v := by
    intro q hq
    exact min'_le vals _ (mem_image.mpr ⟨q,hq,rfl⟩)
  have hconv : Convex ℝ {x : V → ℝ | (a : ℝ) ≤ subsetSum x S} := by
    intro x hx y hy r s hr hs hrs
    change (a : ℝ) ≤ subsetSum (r • x+s • y) S
    rw [subsetSum_add,subsetSum_smul,subsetSum_smul]
    have h1 := mul_le_mul_of_nonneg_left hx hr
    have h2 := mul_le_mul_of_nonneg_left hy hs
    calc
      (a : ℝ) = r*(a : ℝ)+s*(a : ℝ) := by rw [← add_mul,hrs,one_mul]
      _ ≤ r*subsetSum x S+s*subsetSum y S := add_le_add h1 h2
  have hbound : convexHull ℝ
      ((fun x : V → ℤ => fun v => (x v : ℝ)) '' (P : Set (V → ℤ))) ⊆
      {x : V → ℝ | (a : ℝ) ≤ subsetSum x S} := by
    apply convexHull_min _ hconv
    rintro x ⟨q,hq,rfl⟩
    change (a : ℝ) ≤ ∑ v ∈ S, (q v : ℝ)
    exact_mod_cast hmin q hq
  have hpQ : (fun v => (p v : ℝ)) ∈ convexHull ℝ
      ((fun x : V → ℤ => fun v => (x v : ℝ)) '' (P : Set (V → ℤ))) :=
    subset_convexHull ℝ _ ⟨p,hp,rfl⟩
  have hsum : subsetSum (fun v => (p v : ℝ)) S = (a : ℝ) := by
    change (∑ v ∈ S, (p v : ℝ)) = (a : ℝ)
    exact_mod_cast hpa
  have hleast : IsLeast ((fun x => subsetSum x S) '' convexHull ℝ
      ((fun x : V → ℤ => fun v => (x v : ℝ)) '' (P : Set (V → ℤ)))) (a : ℝ) := by
    refine ⟨⟨_,hpQ,hsum⟩,?_⟩
    rintro y ⟨x,hx,rfl⟩
    exact hbound hx
  exact ⟨a,hleast.csInf_eq⟩

theorem IntegerValued.delta {z : SetFunction V} (hz : IntegerValued z)
    (u v : V) (S : Finset V) : ∃ a : ℤ, GraphicalZonotopes.delta z u v S = (a : ℝ) := by
  obtain ⟨a,ha⟩ := hz (insert u (insert v S))
  obtain ⟨b,hb⟩ := hz (insert u S)
  obtain ⟨c,hc⟩ := hz (insert v S)
  obtain ⟨d,hd⟩ := hz S
  exact ⟨a-b-c+d,by simp [GraphicalZonotopes.delta,ha,hb,hc,hd]⟩

theorem IntegerValued.positive_delta_ge_one {z : SetFunction V} (hz : IntegerValued z)
    (u v : V) (S : Finset V) (hp : 0 < GraphicalZonotopes.delta z u v S) : 1 ≤ GraphicalZonotopes.delta z u v S := by
  obtain ⟨a,ha⟩ := hz.delta u v S
  rw [ha] at hp ⊢
  have hi : 0 < a := by exact_mod_cast hp
  exact_mod_cast (show 1 ≤ a by omega)

theorem IntegerValued.modular (t : V → ℝ) (ht : ∀ v, ∃ a : ℤ, t v = (a : ℝ)) :
    IntegerValued (GraphicalZonotopes.modular t) := by
  classical
  choose a ha using ht
  intro S
  refine ⟨∑ v ∈ S, a v,?_⟩
  simp [GraphicalZonotopes.modular,subsetSum,ha]

theorem IntegerValued.normalize {z : SetFunction V} (hz : IntegerValued z) :
    IntegerValued (GraphicalZonotopes.normalize z) :=
  hz.sub (IntegerValued.modular (fun v => z {v}) (fun v => hz {v}))

end GraphicalZonotopes

end
end
end BundlePart18

section BundlePart19
/- Source: Papers/GraphicalZonotopes/Dilation.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Actual Minkowski summation of compact convex sets in the standard real
coordinate space. -/
def IsMinkowskiSummand (Q Z : Set (V → ℝ)) : Prop :=
  ∃ R : Set (V → ℝ), IsCompact R ∧ Convex ℝ R ∧ R.Nonempty ∧ Q+R=Z

def IsWeakMinkowskiSummand (Q Z : Set (V → ℝ)) : Prop :=
  ∃ a : ℝ, 0< a ∧ IsMinkowskiSummand Q (a • Z)

/-- The exact fixed-dilation deformation criterion. The forward direction
quantifies over arbitrary genuine compact convex summands. -/
theorem isMinkowskiSummand_graphical_iff {G : SimpleGraph V} {z : SetFunction V}
    (hn : Normalized z) (hs : Supermodular z) {a : ℝ} (ha : 0 ≤ a) :
    IsMinkowskiSummand (basePolytope z) (a • graphicalZonotope G) ↔
      Graphical G z ∧
      ∀ u v, u ≠ v → G.Adj u v → ∀ S, u ∉ S → v ∉ S → delta z u v S ≤ a := by
  classical
  have hTn : Normalized (a • graphFunction G) := by
    change a*graphFunction G ∅=0
    rw [graphFunction_normalized,mul_zero]
  have hTs : Supermodular (a • graphFunction G) := (graphFunction_supermodular G).smul ha
  constructor
  · rintro ⟨R,hR,hRc,hnR,hQR⟩
    have hbase : basePolytope z+R=basePolytope (a • graphFunction G) := by
      rw [basePolytope_smul (graphFunction_normalized G) (graphFunction_supermodular G) ha,
        baseGraphFunction_eq_graphicalZonotope]
      exact hQR
    have hQ := basePolytope_compact hn hs
    have hnQ := basePolytope_nonempty hn hs
    have hswap : R+basePolytope z=basePolytope (a • graphFunction G) := by
      rw [add_comm]
      exact hbase
    have hRs := summand_lowerSupport_supermodular hTn hTs hR hQ hnR hnQ hswap
    have hsum : z+lowerSupport R=a • graphFunction G := by
      rw [← lowerSupport_basePolytope hn hs,← lowerSupport_add hQ hR hnQ hnR,
        hbase,lowerSupport_basePolytope hTn hTs]
    have hrows : ∀ u v, u ≠ v → ∀ S, u ∉ S → v ∉ S →
        delta z u v S+delta (lowerSupport R) u v S =
          a*(if G.Adj u v then 1 else 0) := by
      intro u v huv S hu hv
      have h := congrArg (fun f => delta f u v S) hsum
      simpa only [delta_add,delta_smul,graphFunction_delta G huv hu hv] using h
    refine ⟨?_,?_⟩
    · intro u v huv hnon S hu hv
      have h := hrows u v huv S hu hv
      rw [if_neg hnon,mul_zero] at h
      have h1 := hs.elemental u v huv S hu hv
      have h2 := hRs.elemental u v huv S hu hv
      linarith
    · intro u v huv hedge S hu hv
      have h := hrows u v huv S hu hv
      rw [if_pos hedge,mul_one] at h
      have h2 := hRs.elemental u v huv S hu hv
      linarith
  · rintro ⟨hG,hub⟩
    let w := a • graphFunction G-z
    have hwn : Normalized w := by
      change a*graphFunction G ∅-z ∅=0
      rw [graphFunction_normalized,hn]
      ring
    have hws : Supermodular w := graphical_complement_supermodular hG ha hub
    exact ⟨basePolytope w,basePolytope_compact hwn hws,basePolytope_convex w,
      basePolytope_nonempty hwn hws,basePolytope_add_graphical_complement hn hs hG ha hub⟩

/-- The full graphical deformation cone agrees with genuine weak Minkowski
summands, with no bound imposed on the finite graph or its clique sizes. -/
theorem isWeakMinkowskiSummand_graphical_iff {G : SimpleGraph V} {z : SetFunction V}
    (hn : Normalized z) (hs : Supermodular z) :
    IsWeakMinkowskiSummand (basePolytope z) (graphicalZonotope G) ↔ Graphical G z := by
  classical
  constructor
  · rintro ⟨a,ha,h⟩
    exact ((isMinkowskiSummand_graphical_iff hn hs ha.le).mp h).1
  · intro hG
    let A : ℝ := ∑ r : V × V × Finset V, |delta z r.1 r.2.1 r.2.2|
    have hA : 0 ≤ A := sum_nonneg (fun r _ => abs_nonneg _)
    refine ⟨A+1,by linarith,?_⟩
    apply (isMinkowskiSummand_graphical_iff hn hs (by linarith)).mpr
    refine ⟨hG,?_⟩
    intro u v huv hedge S hu hv
    have hbound : |delta z u v S| ≤ A := by
      exact single_le_sum (s := (univ : Finset (V × V × Finset V)))
        (f := fun r => |delta z r.1 r.2.1 r.2.2|)
        (fun r _ => abs_nonneg _) (mem_univ (u,v,S))
    exact (le_abs_self _).trans (hbound.trans (by linarith))

/-- A nonpoint lattice summand of an unweighted graphical zonotope cannot
occur below unit dilation. -/
theorem lattice_nonpoint_dilation_ge_one {G : SimpleGraph V}
    {Q R : Set (V → ℝ)} (hQ : LatticePolytope Q) (hnQ : Q.Nonempty)
    (hR : IsCompact R) (hnR : R.Nonempty)
    (hnpoint : ¬∃ p,Q={p}) {a : ℝ} (ha : 0< a)
    (he : Q+R=a • graphicalZonotope G) : 1 ≤ a := by
  let f := lowerSupport Q
  have hQcomp := hQ.compact
  have hTn : Normalized (a • graphFunction G) := by
    change a*graphFunction G ∅=0
    rw [graphFunction_normalized,mul_zero]
  have hTs := (graphFunction_supermodular G).smul ha.le
  have hbase : Q+R=basePolytope (a • graphFunction G) := by
    rw [basePolytope_smul (graphFunction_normalized G) (graphFunction_supermodular G) ha.le,
      baseGraphFunction_eq_graphicalZonotope]
    exact he
  have hfn : Normalized f := lowerSupport_normalized hQcomp hnQ
  have hfs : Supermodular f :=
    summand_lowerSupport_supermodular hTn hTs hQcomp hR hnQ hnR hbase
  have hQbase : Q=basePolytope f :=
    summand_eq_basePolytope hTn hTs hQcomp hR hQ.convex hnQ hnR hbase
  have hfnormne : normalize f ≠ 0 := by
    intro hz
    apply hnpoint
    refine ⟨fun v => f {v},?_⟩
    rw [hQbase]
    conv_lhs => rw [recover_normalize f]
    rw [hz,basePolytope_translate,basePolytope_zero]
    simp
  obtain ⟨u,v,huv,S,hu,hv,hpos⟩ := exists_positive_delta
    (normalize_translationNormalized hfn) hfs.normalize hfnormne
  rw [delta_normalize f huv hu hv] at hpos
  have hone := IntegerValued.positive_delta_ge_one
    (hQ.lowerSupport_integerValued hnQ) u v S hpos
  have hswap : R+Q=basePolytope (a • graphFunction G) := by rw [add_comm]; exact hbase
  have hRs := summand_lowerSupport_supermodular hTn hTs hR hQcomp hnR hnQ hswap
  have hsum : f+lowerSupport R=a • graphFunction G := by
    rw [← lowerSupport_add hQcomp hR hnQ hnR,hbase,lowerSupport_basePolytope hTn hTs]
  have hrow := congrArg (fun z => delta z u v S) hsum
  rw [delta_add,delta_smul,graphFunction_delta G huv hu hv] at hrow
  have hRδ := hRs.elemental u v huv S hu hv
  by_cases hedge : G.Adj u v
  · rw [if_pos hedge,mul_one] at hrow
    linarith
  · rw [if_neg hedge,mul_zero] at hrow
    linarith

end GraphicalZonotopes

end
end
end BundlePart19

section BundlePart20
/- Source: Papers/GraphicalZonotopes/ExposedSegments.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A nondegenerate exposed one-dimensional face, defined by an actual
supporting linear functional and equality with a genuine closed segment. -/
def IsExposedSegment (Q : Set (V → ℝ)) (p q : V → ℝ) : Prop :=
  p ≠ q ∧ ∃ ℓ : (V → ℝ) →ₗ[ℝ] ℝ, ∃ a : ℝ,
    (∀ x ∈ Q, a ≤ ℓ x) ∧ {x ∈ Q | ℓ x = a} = segment ℝ p q

/-- The paper's actual direction graph: its edges are precisely standard-root
parallel directions realized by nondegenerate exposed edges. -/
def ActualRootEdge (Q : Set (V → ℝ)) (u v : V) : Prop :=
  u ≠ v ∧ ∃ p q, IsExposedSegment Q p q ∧
    ∃ a : ℝ, a ≠ 0 ∧ q-p = a • (basisVector u-basisVector v)

def subsetSumLinear (S : Finset V) : (V → ℝ) →ₗ[ℝ] ℝ where
  toFun x := subsetSum x S
  map_add' x y := subsetSum_add x y S
  map_smul' a x := subsetSum_smul a x S

def prefixFaceFunctional {n : ℕ} (e : Fin n ≃ V) (m : ℕ) :
    (V → ℝ) →ₗ[ℝ] ℝ :=
  ∑ j ∈ (univ : Finset (Fin (n+1))).filter (fun j => j.val ≠ m),
    subsetSumLinear (orderPrefix e j.val)

def prefixFaceLevel {n : ℕ} (z : SetFunction V) (e : Fin n ≃ V) (m : ℕ) : ℝ :=
  ∑ j ∈ (univ : Finset (Fin (n+1))).filter (fun j => j.val ≠ m), z (orderPrefix e j.val)

theorem prefixFace_lower_bound {n : ℕ} (z : SetFunction V) (e : Fin n ≃ V)
    (m : ℕ) {x : V → ℝ} (hx : x ∈ basePolytope z) :
    prefixFaceLevel z e m ≤ prefixFaceFunctional e m x := by
  unfold prefixFaceLevel prefixFaceFunctional
  simp only [LinearMap.sum_apply, subsetSumLinear, LinearMap.coe_mk, AddHom.coe_mk]
  exact sum_le_sum (fun j hj => hx.2 _)

theorem prefixFace_eq_iff {n : ℕ} (z : SetFunction V) (e : Fin n ≃ V)
    (m : ℕ) {x : V → ℝ} (hx : x ∈ basePolytope z) :
    prefixFaceFunctional e m x = prefixFaceLevel z e m ↔
      ∀ j : Fin (n+1), j.val ≠ m → subsetSum x (orderPrefix e j.val) = z (orderPrefix e j.val) := by
  unfold prefixFaceFunctional prefixFaceLevel
  simp only [LinearMap.sum_apply, subsetSumLinear, LinearMap.coe_mk, AddHom.coe_mk]
  have hnn : ∀ j ∈ (univ : Finset (Fin (n+1))).filter (fun j => j.val ≠ m),
      0 ≤ subsetSum x (orderPrefix e j.val) - z (orderPrefix e j.val) :=
    fun j _ => sub_nonneg.mpr (hx.2 _)
  rw [← sub_eq_zero, ← sum_sub_distrib, sum_eq_zero_iff_of_nonneg hnn]
  simp only [mem_filter, mem_univ, true_and, sub_eq_zero]

theorem coordinate_of_prefix_equalities {n : ℕ} (z : SetFunction V) (e : Fin n ≃ V)
    (x : V → ℝ) (j : Fin n)
    (h0 : subsetSum x (orderPrefix e j.val) = z (orderPrefix e j.val))
    (h1 : subsetSum x (orderPrefix e (j.val+1)) = z (orderPrefix e (j.val+1))) :
    x (e j) = greedyPoint z e (e j) := by
  rw [orderPrefix_succ, subsetSum_insert (not_mem_orderPrefix e j), h0] at h1
  rw [greedyPoint_apply]
  linarith

/-- The neighboring greedy segment is an exposed edge whenever its elemental
slack is positive. The proof fixes every other prefix, reconstructs every
coordinate, and identifies the remaining interval exactly. -/
theorem exposedSegment_of_positive_delta {z : SetFunction V}
    (hn : Normalized z) (hs : Supermodular z)
    {u v : V} (huv : u ≠ v) {S : Finset V} (hu : u ∉ S) (hv : v ∉ S)
    (hδ : 0 < delta z u v S) : ActualRootEdge (basePolytope z) u v := by
  obtain ⟨e,h0,h1⟩ := exists_pair_enumeration S huv hu hv
  let p := greedyPoint z e
  let q := greedyPoint z (e.trans (Equiv.swap u v))
  let d := delta z u v S
  let m := (e.symm v).val
  have hd0 : d ≠ 0 := ne_of_gt hδ
  have hadj := pair_enumeration_adjacent e S hu h0 h1
  have hp : p ∈ basePolytope z := greedyPoint_mem_basePolytope hn hs e
  have hq : q ∈ basePolytope z := greedyPoint_mem_basePolytope hn hs _
  have hdiff : q-p = d • (basisVector u-basisVector v) :=
    greedyPoint_swap_difference z e S huv hu hv h0 h1
  have hqu : q u-p u = d := by
    have h := congrFun hdiff u
    simpa [basisVector, Pi.single_apply, huv, Ne.symm huv] using h
  have hqv : q v-p v = -d := by
    have h := congrFun hdiff v
    simpa [basisVector, Pi.single_apply, huv, Ne.symm huv] using h
  have hpq : p ≠ q := by
    intro he
    rw [he,sub_self] at hqu
    exact (ne_of_gt hδ) hqu.symm
  refine ⟨huv,p,q,⟨hpq,?_,?_,?_,?_⟩,d,ne_of_gt hδ,hdiff⟩
  · exact prefixFaceFunctional e m
  · exact prefixFaceLevel z e m
  · intro x hx
    exact prefixFace_lower_bound z e m hx
  · apply Set.Subset.antisymm
    · rintro x ⟨hx,hlevel⟩
      have hprefix := (prefixFace_eq_iff z e m hx).mp hlevel
      have hpref (j : Fin ((Fintype.card V)+1)) :=
        greedyPoint_prefix z hn e j.val (by omega)
      have hxS : subsetSum x S = z S := by
        have h := hprefix ⟨(e.symm u).val,by omega⟩ (by dsimp [m]; omega)
        simpa [h0] using h
      have hpS : subsetSum p S = z S := by
        simpa [p,h0] using hpref ⟨(e.symm u).val,by omega⟩
      have hafter : orderPrefix e ((e.symm v).val+1) = insert v (insert u S) := by
        rw [orderPrefix_succ, e.apply_symm_apply,h1]
      have hxTot : x u+x v = p u+p v := by
        have hx' := hprefix ⟨(e.symm v).val+1,by omega⟩ (by dsimp [m]; omega)
        have hp' := hpref ⟨(e.symm v).val+1,by omega⟩
        rw [hafter,subsetSum_insert (by simp [huv,Ne.symm huv,hv]),subsetSum_insert hu,hxS] at hx'
        rw [hafter,subsetSum_insert (by simp [huv,Ne.symm huv,hv]),subsetSum_insert hu,hpS] at hp'
        linarith
      have hpu : p u = z (insert u S)-z S := by
        have h := greedyPoint_apply z e (e.symm u)
        simpa [p,h0] using h
      have hlow : p u ≤ x u := by
        have h := hx.2 (insert u S)
        rw [subsetSum_insert hu,hxS] at h
        linarith
      have hupp : x u ≤ p u+d := by
        have h := hx.2 (insert v S)
        rw [subsetSum_insert hv,hxS] at h
        have hpuv : p u+p v = z (insert v (insert u S))-z S := by
          have hp' := hpref ⟨(e.symm v).val+1,by omega⟩
          rw [hafter,subsetSum_insert (by simp [huv,Ne.symm huv,hv]),subsetSum_insert hu,hpS] at hp'
          linarith
        dsimp [d,delta]
        rw [insert_comm u v]
        linarith
      have houtside : ∀ w, w ≠ u → w ≠ v → x w = p w := by
        intro w hwu hwv
        have hwu' : (e.symm w).val ≠ (e.symm u).val := by
          intro h
          exact hwu (e.symm.injective (Fin.ext h))
        have hwv' : (e.symm w).val ≠ (e.symm v).val := by
          intro h
          exact hwv (e.symm.injective (Fin.ext h))
        have hbefore := hprefix ⟨(e.symm w).val,by omega⟩ (by exact hwv')
        have hafter := hprefix ⟨(e.symm w).val+1,by omega⟩ (by dsimp [m]; omega)
        simpa [p] using coordinate_of_prefix_equalities z e x (e.symm w) hbefore hafter
      let a : ℝ := (p u+d-x u)/d
      let b : ℝ := (x u-p u)/d
      have ha : 0 ≤ a := div_nonneg (by linarith) hδ.le
      have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hlow) hδ.le
      have hab : a+b = 1 := by dsimp [a,b]; field_simp [hd0]; ring
      refine ⟨a,b,ha,hb,hab,?_⟩
      have hbδ : b*d = x u-p u := by
        dsimp [b]
        field_simp [hd0]
      funext w
      change a * p w + b * q w = x w
      by_cases hwu : w = u
      · subst w
        have hqe : q u = p u+d := by linarith
        calc
          a * p u + b * q u = (a+b) * p u + b*d := by rw [hqe]; ring
          _ = x u := by rw [hab,one_mul,hbδ]; ring
      · by_cases hwv : w = v
        · subst w
          have hqe : q v = p v-d := by linarith
          calc
            a * p v + b * q v = (a+b) * p v - b*d := by rw [hqe]; ring
            _ = x v := by rw [hab,one_mul,hbδ]; linarith [hxTot]
        · have hqeq : q w = p w := by
            have h := congrFun hdiff w
            simp [basisVector,Pi.single_apply,hwu,hwv,Ne.symm hwu,Ne.symm hwv] at h
            exact sub_eq_zero.mp h
          rw [hqeq,houtside w hwu hwv,← add_mul,hab,one_mul]
    · have hpref : prefixFaceFunctional e m p = prefixFaceLevel z e m := by
        apply (prefixFace_eq_iff z e m hp).mpr
        intro j hj
        exact greedyPoint_prefix z hn e j.val (by omega)
      have hqref : prefixFaceFunctional e m q = prefixFaceLevel z e m := by
        apply (prefixFace_eq_iff z e m hq).mpr
        intro j hj
        have heq := orderPrefix_swap_of_ne e huv hadj hj
        rw [← heq]
        exact greedyPoint_prefix z hn (e.trans (Equiv.swap u v)) j.val (by omega)
      have hconv : Convex ℝ {x ∈ basePolytope z |
          prefixFaceFunctional e m x = prefixFaceLevel z e m} := by
        intro x hx y hy a b ha hb hab
        refine ⟨basePolytope_convex z hx.1 hy.1 ha hb hab, ?_⟩
        rw [map_add,map_smul,map_smul,hx.2,hy.2]
        change a * prefixFaceLevel z e m + b * prefixFaceLevel z e m = prefixFaceLevel z e m
        rw [← add_mul,hab,one_mul]
      exact hconv.segment_subset ⟨hp,hpref⟩ ⟨hq,hqref⟩

end GraphicalZonotopes

end
end
end BundlePart20

section BundlePart21
/- Source: Papers/GraphicalZonotopes/GraphDefinitions.lean -/






@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A polytope is a finite convex hull in the actual coordinate space. -/
def IsFinitePolytope (Q : Set (V → ℝ)) : Prop :=
  ∃ s : Finset (V → ℝ), convexHull ℝ (s : Set (V → ℝ)) = Q

/-- The standard lower-base-polytope presentation of a generalized
permutahedron, including arbitrary translations. -/
def IsGeneralizedPermutahedron (Q : Set (V → ℝ)) : Prop :=
  ∃ z : SetFunction V, Normalized z ∧ Supermodular z ∧ Q = basePolytope z

theorem IsFinitePolytope.compact {Q : Set (V → ℝ)} (hQ : IsFinitePolytope Q) :
    IsCompact Q := by
  obtain ⟨s,rfl⟩ := hQ
  exact s.finite_toSet.isCompact_convexHull ℝ

theorem IsFinitePolytope.convex {Q : Set (V → ℝ)} (hQ : IsFinitePolytope Q) :
    Convex ℝ Q := by
  obtain ⟨s,rfl⟩ := hQ
  exact convex_convexHull ℝ _

theorem IsGeneralizedPermutahedron.finitePolytope {Q : Set (V → ℝ)}
    (hQ : IsGeneralizedPermutahedron Q) : IsFinitePolytope Q := by
  classical
  obtain ⟨z,hn,hs,rfl⟩ := hQ
  refine ⟨(greedyPoints_finite z).toFinset,?_⟩
  simpa only [Set.Finite.coe_toFinset] using (basePolytope_eq_convexHull hn hs).symm

/-- The traditional definition quantifies over polytope summands. The
compact-convex definition used by the geometric proof is equivalent on the
generalized permutahedra at issue here, as proved below. -/
def PolytopalMinkowskiIndecomposable (Q : Set (V → ℝ)) : Prop :=
  Q.Nonempty ∧ ∀ P R : Set (V → ℝ),IsFinitePolytope P → IsFinitePolytope R →
    P+R=Q → ∃ (a : ℝ) (t : V → ℝ),0≤ a ∧ P=({t} : Set (V → ℝ))+a • Q

theorem minkowskiIndecomposable_iff_polytopal {Q : Set (V → ℝ)}
    (hQ : IsGeneralizedPermutahedron Q) :
    MinkowskiIndecomposable Q ↔ PolytopalMinkowskiIndecomposable Q := by
  constructor
  · intro h
    refine ⟨h.1,fun P R hP hR he => ?_⟩
    exact h.2 P R hP.compact hR.compact hP.convex hR.convex he
  · intro h
    obtain ⟨z,hn,hs,rfl⟩ := hQ
    refine ⟨h.1,?_⟩
    intro P R hP hR hcP hcR he
    obtain ⟨x,hx⟩ := h.1
    rw [← he] at hx
    obtain ⟨p,hp,r,hr,hpr⟩ := hx
    have hnP : P.Nonempty := ⟨p,hp⟩
    have hnR : R.Nonempty := ⟨r,hr⟩
    have hsgP := summand_lowerSupport_supermodular hn hs hP hR hnP hnR he
    have heR : R+P=basePolytope z := by rw [add_comm]; exact he
    have hsgR := summand_lowerSupport_supermodular hn hs hR hP hnR hnP heR
    have hgpP : IsGeneralizedPermutahedron P :=
      ⟨lowerSupport P,lowerSupport_normalized hP hnP,hsgP,
        summand_eq_basePolytope hn hs hP hR hcP hnP hnR he⟩
    have hgpR : IsGeneralizedPermutahedron R :=
      ⟨lowerSupport R,lowerSupport_normalized hR hnR,hsgR,
        summand_eq_basePolytope hn hs hR hP hcR hnR hnP heR⟩
    exact h.2 P R hgpP.finitePolytope hgpR.finitePolytope he

/-- The base-polytope presentation agrees with genuine weak Minkowski
summands of the ordinary permutahedral zonotope. This checks the geometric
meaning of the generalized-permutahedron predicate used in the targets. -/
theorem generalizedPermutahedron_iff_weak_complete {Q : Set (V → ℝ)}
    (hQ : IsFinitePolytope Q) :
    IsGeneralizedPermutahedron Q ↔
      IsWeakMinkowskiSummand Q (graphicalZonotope (⊤ : SimpleGraph V)) := by
  constructor
  · rintro ⟨z,hn,hs,rfl⟩
    apply (isWeakMinkowskiSummand_graphical_iff hn hs).mpr
    intro u v huv hnon
    exact False.elim (hnon huv)
  · rintro ⟨a,ha,R,hR,hRc,hnR,he⟩
    let z : SetFunction V := a • graphFunction (⊤ : SimpleGraph V)
    have hzn : Normalized z := by
      change a * graphFunction (⊤ : SimpleGraph V) ∅ = 0
      rw [graphFunction_normalized,mul_zero]
    have hzs : Supermodular z := (graphFunction_supermodular _).smul ha.le
    have hbody : Q+R = basePolytope z := by
      rw [show basePolytope z = a • graphicalZonotope (⊤ : SimpleGraph V) by
        rw [basePolytope_smul (graphFunction_normalized _)
          (graphFunction_supermodular _) ha.le,baseGraphFunction_eq_graphicalZonotope]]
      exact he
    obtain ⟨x,hx⟩ := basePolytope_nonempty hzn hzs
    rw [← hbody] at hx
    obtain ⟨p,hp,r,hr,hpr⟩ := hx
    have hnQ : Q.Nonempty := ⟨p,hp⟩
    refine ⟨lowerSupport Q,lowerSupport_normalized hQ.compact hnQ,?_,?_⟩
    · exact summand_lowerSupport_supermodular hzn hzs hQ.compact hR hnQ hnR hbody
    · exact summand_eq_basePolytope hzn hzs hQ.compact hR hQ.convex hnQ hnR hbody

theorem actualRootEdge_symm {Q : Set (V → ℝ)} {u v : V}
    (h : ActualRootEdge Q u v) : ActualRootEdge Q v u := by
  obtain ⟨huv,p,q,hface,a,ha,he⟩ := h
  refine ⟨Ne.symm huv,p,q,hface,-a,neg_ne_zero.mpr ha,?_⟩
  rw [he,neg_smul,smul_sub,smul_sub]
  abel

def actualDirectionGraph (Q : Set (V → ℝ)) : SimpleGraph V where
  Adj := ActualRootEdge Q
  symm := ⟨fun _ _ => actualRootEdge_symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def directionCount (Q : Set (V → ℝ)) : ℕ := (edgeFamily (actualDirectionGraph Q)).card

def maximumDirectionDegree (Q : Set (V → ℝ)) : ℕ := by
  classical
  exact (actualDirectionGraph Q).maxDegree

def FullDimension (Q : Set (V → ℝ)) : Prop :=
  Module.finrank ℝ (vectorSpan ℝ Q) = Fintype.card V - 1

def SupportsFullIndecomposable (G : SimpleGraph V) : Prop :=
  ∃ Q : Set (V → ℝ), IsFinitePolytope Q ∧ MinkowskiIndecomposable Q ∧
    FullDimension Q ∧ IsWeakMinkowskiSummand Q (graphicalZonotope G)

/-- The dimension invariant in the paper. Points do not change its value;
on an edgeless graph this supremum is zero. -/
def maximumIndecomposableDimension (G : SimpleGraph V) : ℕ :=
  sSup {d : ℕ | ∃ Q : Set (V → ℝ), IsFinitePolytope Q ∧
    MinkowskiIndecomposable Q ∧ IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
    Module.finrank ℝ (vectorSpan ℝ Q) = d}

def maximumThreeTreeSupportDimension (G : SimpleGraph V) : ℕ :=
  sSup {d : ℕ | ∃ Q : Set (V → ℝ), IsFinitePolytope Q ∧
    MinkowskiIndecomposable Q ∧ IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
    (∃ S : Finset V, ThreeTreeOn S (actualDirectionGraph Q)) ∧
    Module.finrank ℝ (vectorSpan ℝ Q) = d}

def EdgeMinimalSupporting (G : SimpleGraph V) : Prop :=
  SupportsFullIndecomposable G ∧
    ∀ H : SimpleGraph V, H < G → ¬SupportsFullIndecomposable H

def BooleanElemental (Q : Set (V → ℝ)) : Prop :=
  ∀ u v, u ≠ v → ∀ S : Finset V, u ∉ S → v ∉ S →
    delta (lowerSupport Q) u v S = 0 ∨ delta (lowerSupport Q) u v S = 1

def CentrallySymmetricUpToTranslation (Q : Set (V → ℝ)) : Prop :=
  ∃ t : V → ℝ, Q = ({t} : Set (V → ℝ)) + (-1 : ℝ) • Q

def FullLatticeSummandAt (G : SimpleGraph V) (a : ℝ) : Prop :=
  ∃ Q : Set (V → ℝ), LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
    FullDimension Q ∧ IsMinkowskiSummand Q (a • graphicalZonotope G)

def LeastFullLatticeDilation (G : SimpleGraph V) (a : ℝ) : Prop :=
  0 < a ∧ FullLatticeSummandAt G a ∧
    ∀ b : ℝ, 0 < b → FullLatticeSummandAt G b → a ≤ b


end GraphicalZonotopes

end
end
end BundlePart21

section BundlePart22
/- Source: Papers/GraphicalZonotopes/PolyhedralCone.lean -/














@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! A finite system of homogeneous linear inequalities and its exact extreme-ray criterion. -/
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Polyhedral
variable {E I : Type*} [AddCommGroup E] [Module ℝ E] [Fintype I]

def Nonnegative (A : I → E →ₗ[ℝ] ℝ) (y : E) : Prop := ∀ i, 0 ≤ A i y

def Pointed (A : I → E →ₗ[ℝ] ℝ) : Prop :=
  ∀ y, (∀ i, A i y = 0) → y = 0

def ExtremeRay (A : I → E →ₗ[ℝ] ℝ) (y : E) : Prop :=
  Nonnegative A y ∧ y ≠ 0 ∧
  ∀ u v, Nonnegative A u → Nonnegative A v → u + v = y →
    ∃ a : ℝ, 0 ≤ a ∧ u = a • y

def tightKernel (A : I → E →ₗ[ℝ] ℝ) (y : E) : Submodule ℝ E where
  carrier := {v | ∀ i, A i y = 0 → A i v = 0}
  zero_mem' := by simp
  add_mem' := by intro u v hu hv i hi; simp [hu i hi, hv i hi]
  smul_mem' := by intro a v hv i hi; simp [hv i hi]

@[simp] theorem mem_tightKernel (A : I → E →ₗ[ℝ] ℝ) (y v : E) :
    v ∈ tightKernel A y ↔ ∀ i, A i y = 0 → A i v = 0 := Iff.rfl

theorem self_mem_tightKernel (A : I → E →ₗ[ℝ] ℝ) (y : E) : y ∈ tightKernel A y :=
  fun _ h => h

theorem Pointed.exists_positive {A : I → E →ₗ[ℝ] ℝ} (hA : Pointed A)
    {y : E} (hy : Nonnegative A y) (hne : y ≠ 0) : ∃ i, 0 < A i y := by
  by_contra h
  push_neg at h
  exact hne (hA y (fun i => le_antisymm (h i) (hy i)))

theorem summand_mem_tightKernel {A : I → E →ₗ[ℝ] ℝ} {y u v : E}
    (hu : Nonnegative A u) (hv : Nonnegative A v) (he : u + v = y) :
    u ∈ tightKernel A y := by
  intro i hi
  have hsum : A i u + A i v = 0 := by rw [← map_add, he, hi]
  have h1 := hu i
  have h2 := hv i
  linarith

theorem extremeRay_of_tightKernel {A : I → E →ₗ[ℝ] ℝ} (hA : Pointed A)
    {y : E} (hy : Nonnegative A y) (hne : y ≠ 0)
    (hk : tightKernel A y = Submodule.span ℝ {y}) : ExtremeRay A y := by
  refine ⟨hy, hne, ?_⟩
  intro u v hu hv he
  have huK := summand_mem_tightKernel hu hv he
  rw [hk, Submodule.mem_span_singleton] at huK
  obtain ⟨a, ha⟩ := huK
  refine ⟨a, ?_, ha.symm⟩
  obtain ⟨i, hi⟩ := hA.exists_positive hy hne
  have h := hu i
  rw [← ha, map_smul, smul_eq_mul] at h
  exact nonneg_of_mul_nonneg_left h hi

theorem exists_two_sided_perturbation {A : I → E →ₗ[ℝ] ℝ} {y v : E}
    (hy : Nonnegative A y) (hv : v ∈ tightKernel A y) :
    ∃ ε : ℝ, 0 < ε ∧ Nonnegative A ((1 / 2 : ℝ) • y + ε • v) ∧
      Nonnegative A ((1 / 2 : ℝ) • y - ε • v) := by
  classical
  have aux : ∀ s : Finset I, ∃ ε : ℝ, 0 < ε ∧
      ∀ i ∈ s, ε * |A i v| ≤ A i y / 2 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨ε, hε, hbound⟩ := ih
      by_cases hyi : A i y = 0
      · refine ⟨ε, hε, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with hji | hj
        · subst j
          simp [hyi, hv i hyi]
        · exact hbound j hj
      · have hyi' : 0 < A i y := lt_of_le_of_ne (hy i) (Ne.symm hyi)
        let δ := min ε (A i y / (2 * (|A i v| + 1)))
        have hδ : 0 < δ := lt_min hε (div_pos hyi' (by positivity))
        refine ⟨δ, hδ, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with hji | hj
        · subst j
          have hle : δ ≤ A i y / (2 * (|A i v| + 1)) := min_le_right _ _
          have hm := (le_div_iff₀ (show 0 < 2 * (|A i v| + 1) by positivity)).mp hle
          nlinarith
        · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (abs_nonneg _)).trans
            (hbound j hj)
  obtain ⟨ε, hε, hbound⟩ := aux Finset.univ
  refine ⟨ε, hε, ?_, ?_⟩
  · intro i
    simp only [map_add, map_smul, smul_eq_mul]
    have h1 := hbound i (Finset.mem_univ i)
    have h2 := neg_abs_le (A i v)
    nlinarith
  · intro i
    simp only [map_sub, map_smul, smul_eq_mul]
    have h1 := hbound i (Finset.mem_univ i)
    have h2 := le_abs_self (A i v)
    nlinarith

theorem ExtremeRay.tightKernel_eq_span {A : I → E →ₗ[ℝ] ℝ} {y : E}
    (hy : ExtremeRay A y) : tightKernel A y = Submodule.span ℝ {y} := by
  apply le_antisymm
  · intro v hv
    obtain ⟨ε, hε, hp, hm⟩ := exists_two_sided_perturbation hy.1 hv
    have he : ((1 / 2 : ℝ) • y + ε • v) + ((1 / 2 : ℝ) • y - ε • v) = y := by module
    obtain ⟨a, ha, hae⟩ := hy.2.2 _ _ hp hm he
    apply Submodule.mem_span_singleton.mpr
    refine ⟨(a - 1 / 2) / ε, ?_⟩
    have hvε : ε • v = (a - 1 / 2) • y := by
      rw [sub_smul]
      exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hae)
    calc
      ((a - 1 / 2) / ε) • y = ε⁻¹ • ((a - 1 / 2) • y) := by
        rw [smul_smul]; congr 1; ring
      _ = ε⁻¹ • (ε • v) := by rw [hvε]
      _ = v := by rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hε), one_smul]
  · exact Submodule.span_le.mpr (by
      intro v hv
      have hvy : v = y := Set.mem_singleton_iff.mp hv
      subst v
      exact self_mem_tightKernel A y)

theorem extremeRay_iff_tightKernel {A : I → E →ₗ[ℝ] ℝ} (hA : Pointed A)
    {y : E} (hy : Nonnegative A y) (hne : y ≠ 0) :
    ExtremeRay A y ↔ tightKernel A y = Submodule.span ℝ {y} :=
  ⟨ExtremeRay.tightKernel_eq_span, extremeRay_of_tightKernel hA hy hne⟩

end Polyhedral
end GraphicalZonotopes

end
end
end BundlePart22

section BundlePart23
/- Source: Papers/GraphicalZonotopes/BoundaryContexts.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
section Unordered
variable {V : Type*} [Fintype V] [DecidableEq V]

def commonNeighbors (G : SimpleGraph V) (u v : V) : Finset V := by
  classical
  exact univ.filter (fun w => G.Adj u w ∧ G.Adj v w)

@[simp] theorem mem_commonNeighbors (G : SimpleGraph V) (u v w : V) :
    w ∈ commonNeighbors G u v ↔ G.Adj u w ∧ G.Adj v w := by
  classical
  simp [commonNeighbors]

@[simp] theorem not_mem_commonNeighbors_left (G : SimpleGraph V) (u v : V) :
    u ∉ commonNeighbors G u v := by simp

@[simp] theorem not_mem_commonNeighbors_right (G : SimpleGraph V) (u v : V) :
    v ∉ commonNeighbors G u v := by simp

theorem commonNeighbors_comm (G : SimpleGraph V) (u v : V) :
    commonNeighbors G u v=commonNeighbors G v u := by
  ext w
  simp [and_comm]

theorem clique_pair_subset_iff {G : SimpleGraph V} {C S : Finset V}
    (hcl : G.IsClique C) {u v : V} (huC : u ∈ C) (hvC : v ∈ C) :
    C ⊆ insert u (insert v S) ↔ C ⊆ insert u (insert v (S ∩ commonNeighbors G u v)) := by
  constructor
  · intro h w hw
    have hm := h hw
    simp only [mem_insert] at hm ⊢
    rcases hm with hwu | hwv | hwS
    · exact Or.inl hwu
    · exact Or.inr (Or.inl hwv)
    · by_cases hwu : w=u
      · exact Or.inl hwu
      · by_cases hwv : w=v
        · exact Or.inr (Or.inl hwv)
        · exact Or.inr (Or.inr (mem_inter.mpr ⟨hwS,(mem_commonNeighbors G u v w).mpr
            ⟨hcl huC hw (Ne.symm hwu),hcl hvC hw (Ne.symm hwv)⟩⟩))
  · intro h
    exact h.trans (insert_subset_insert _ (insert_subset_insert _ inter_subset_left))

/-- Elemental differences of a graphical function depend only on the
conditioning bits of common neighbors. This is proved from all Möbius slots. -/
theorem delta_zeta_commonNeighbors {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y) {u v : V} (huv : u ≠ v) {S : Finset V}
    (hu : u ∉ S) (hv : v ∉ S) :
    delta (zeta y) u v S=delta (zeta y) u v (S ∩ commonNeighbors G u v) := by
  classical
  have hu' : u ∉ S ∩ commonNeighbors G u v := by simp
  have hv' : v ∉ S ∩ commonNeighbors G u v := by simp
  rw [zeta_eq_sum_monomials,delta_sum,delta_sum]
  apply sum_congr rfl
  intro C hC
  rw [delta_smul,delta_smul,delta_setMonomial huv hu hv,
    delta_setMonomial huv hu' hv']
  by_cases hyC : y C=0
  · simp [hyC]
  · have hcl : G.IsClique C := by
      by_contra hn
      exact hyC (coefficient_zero_of_not_clique hy C (by rintro ⟨_,h⟩; exact hn h))
    by_cases huC : u ∈ C
    · by_cases hvC : v ∈ C
      · have he := clique_pair_subset_iff (S := S) hcl huC hvC
        simp only [he]
      · simp [hvC]
    · simp [huC]

theorem delta_commonNeighbors {G : SimpleGraph V} {z : SetFunction V}
    (hn : TranslationNormalized z) (hG : Graphical G z)
    {u v : V} (huv : u ≠ v) {S : Finset V} (hu : u ∉ S) (hv : v ∉ S) :
    delta z u v S=delta z u v (S ∩ commonNeighbors G u v) := by
  have h := delta_zeta_commonNeighbors ((mobius_cliqueSupported_iff G z).mpr ⟨hn,hG⟩) huv hu hv
  simpa using h

theorem delta_comm {z : SetFunction V} (u v : V) (S : Finset V) :
    delta z u v S=delta z v u S := by
  unfold delta
  rw [insert_comm]
  ring

end Unordered

section Ordered
variable {V : Type*} [Fintype V] [LinearOrder V]

abbrev OrientedEdge (G : SimpleGraph V) := {e : V × V // e.1< e.2 ∧ G.Adj e.1 e.2}

noncomputable instance orientedEdgeFintype (G : SimpleGraph V) : Fintype (OrientedEdge G) := by
  classical
  infer_instance

abbrev BoundaryContext (G : SimpleGraph V) :=
  Σ e : OrientedEdge G, ↥(commonNeighbors G e.1.1 e.1.2).powerset

noncomputable instance boundaryContextFintype (G : SimpleGraph V) : Fintype (BoundaryContext G) := by
  classical
  infer_instance

/-- The exact boundary slack map, using each unordered graph edge once and all
common-neighbor contexts once. -/
def boundarySlackMap (G : SimpleGraph V) :
    graphicalFunctionSpace G →ₗ[ℝ] (BoundaryContext G → ℝ) where
  toFun z r := delta z.1 r.1.1.1 r.1.1.2 r.2.1
  map_add' z w := by ext r; exact delta_add z.1 w.1 _ _ _
  map_smul' a z := by ext r; exact delta_smul a z.1 _ _ _

theorem boundarySlackMap_eq_zero (G : SimpleGraph V) (z : graphicalFunctionSpace G)
    (hz : boundarySlackMap G z=0) : z=0 := by
  apply graphical_function_eq_zero_of_elemental_zero G z
  intro u v huv S hu hv
  by_cases hedge : G.Adj u v
  · rcases lt_or_gt_of_ne huv with hlt | hgt
    · let e : OrientedEdge G := ⟨(u,v),hlt,hedge⟩
      let T := S ∩ commonNeighbors G u v
      let r : BoundaryContext G := ⟨e,⟨T,mem_powerset.mpr inter_subset_right⟩⟩
      have h := congrFun hz r
      rw [delta_commonNeighbors z.2.1 z.2.2 huv hu hv]
      exact h
    · let e : OrientedEdge G := ⟨(v,u),hgt,G.adj_symm hedge⟩
      let T := S ∩ commonNeighbors G v u
      let r : BoundaryContext G := ⟨e,⟨T,mem_powerset.mpr inter_subset_right⟩⟩
      have h := congrFun hz r
      rw [delta_comm u v,delta_commonNeighbors z.2.1 z.2.2 (Ne.symm huv) hv hu]
      exact h
  · exact z.2.2 u v huv hedge S hu hv

theorem boundarySlackMap_injective (G : SimpleGraph V) :
    Function.Injective (boundarySlackMap G) := by
  intro z w he
  have hz : boundarySlackMap G (z-w)=0 := by rw [map_sub,he,sub_self]
  exact sub_eq_zero.mp (boundarySlackMap_eq_zero G (z-w) hz)

theorem supermodular_iff_boundarySlacks_nonnegative (G : SimpleGraph V)
    (z : graphicalFunctionSpace G) :
    Supermodular z.1 ↔ ∀ r,0 ≤ boundarySlackMap G z r := by
  constructor
  · intro hs r
    have hu : r.1.1.1 ∉ r.2.1 := by
      intro hm
      exact not_mem_commonNeighbors_left G _ _ ((mem_powerset.mp r.2.2) hm)
    have hv : r.1.1.2 ∉ r.2.1 := by
      intro hm
      exact not_mem_commonNeighbors_right G _ _ ((mem_powerset.mp r.2.2) hm)
    exact hs.elemental _ _ (ne_of_lt r.1.2.1) _ hu hv
  · intro hrows
    apply ElementallyNonnegative.supermodular
    intro u v huv S hu hv
    by_cases hedge : G.Adj u v
    · rcases lt_or_gt_of_ne huv with hlt | hgt
      · let e : OrientedEdge G := ⟨(u,v),hlt,hedge⟩
        let r : BoundaryContext G := ⟨e,⟨S ∩ commonNeighbors G u v,mem_powerset.mpr inter_subset_right⟩⟩
        rw [delta_commonNeighbors z.2.1 z.2.2 huv hu hv]
        exact hrows r
      · let e : OrientedEdge G := ⟨(v,u),hgt,G.adj_symm hedge⟩
        let r : BoundaryContext G := ⟨e,⟨S ∩ commonNeighbors G v u,mem_powerset.mpr inter_subset_right⟩⟩
        rw [delta_comm u v,delta_commonNeighbors z.2.1 z.2.2 (Ne.symm huv) hv hu]
        exact hrows r
    · rw [z.2.2 u v huv hedge S hu hv]

theorem boundaryContext_card (G : SimpleGraph V) :
    Fintype.card (BoundaryContext G)=
      ∑ e : OrientedEdge G,2 ^ (commonNeighbors G e.1.1 e.1.2).card := by
  simp only [BoundaryContext,Fintype.card_sigma,Fintype.card_coe,card_powerset]

theorem clique_count_le_boundary_context_count (G : SimpleGraph V) :
    Fintype.card (CliqueIndex G) ≤ Fintype.card (BoundaryContext G) := by
  have h := LinearMap.finrank_le_finrank_of_injective (boundarySlackMap_injective G)
  simpa [graphicalFunctionSpace_finrank,Module.finrank_fintype_fun_eq_card] using h

/-- The row family used by the finite homogeneous inequality cone. -/
def contextRow (G : SimpleGraph V) (r : BoundaryContext G) :
    graphicalFunctionSpace G →ₗ[ℝ] ℝ where
  toFun z := boundarySlackMap G z r
  map_add' z w := congrFun ((boundarySlackMap G).map_add z w) r
  map_smul' a z := congrFun ((boundarySlackMap G).map_smul a z) r

theorem contextRows_pointed (G : SimpleGraph V) : Polyhedral.Pointed (contextRow G) := by
  intro z hz
  apply boundarySlackMap_eq_zero G z
  funext r
  exact hz r

/-- The normalized graphical finite-inequality model and the genuine
supermodular-function cone have exactly the same extreme rays. -/
theorem extremeSupermodular_iff_contextRows (G : SimpleGraph V)
    (z : graphicalFunctionSpace G) :
    ExtremeSupermodular z.1 ↔ Polyhedral.ExtremeRay (contextRow G) z := by
  constructor
  · intro hz
    refine ⟨(supermodular_iff_boundarySlacks_nonnegative G z).mp hz.2.1,?_,?_⟩
    · intro he
      exact hz.2.2.1 (congrArg Subtype.val he)
    · intro f g hf hg he
      have hfs := (supermodular_iff_boundarySlacks_nonnegative G f).mpr hf
      have hgs := (supermodular_iff_boundarySlacks_nonnegative G g).mpr hg
      have hsum : f.1+g.1=z.1 := congrArg Subtype.val he
      obtain ⟨a,ha,hscale⟩ := hz.2.2.2 f.1 g.1 f.2.1 g.2.1 hfs hgs hsum
      exact ⟨a,ha,Subtype.ext hscale⟩
  · intro hz
    have hzs := (supermodular_iff_boundarySlacks_nonnegative G z).mpr hz.1
    refine ⟨z.2.1,hzs,?_,?_⟩
    · intro he
      exact hz.2.1 (Subtype.ext he)
    · intro f g hfn hgn hfs hgs he
      obtain ⟨hfG,hgG⟩ := z.2.2.summands hfs hgs he
      let f' : graphicalFunctionSpace G := ⟨f,hfn,hfG⟩
      let g' : graphicalFunctionSpace G := ⟨g,hgn,hgG⟩
      have hf' : Polyhedral.Nonnegative (contextRow G) f' :=
        (supermodular_iff_boundarySlacks_nonnegative G f').mp hfs
      have hg' : Polyhedral.Nonnegative (contextRow G) g' :=
        (supermodular_iff_boundarySlacks_nonnegative G g').mp hgs
      have he' : f'+g'=z := Subtype.ext he
      obtain ⟨a,ha,hscale⟩ := hz.2.2 f' g' hf' hg' he'
      exact ⟨a,ha,congrArg Subtype.val hscale⟩


end Ordered
end GraphicalZonotopes

end
end
end BundlePart23

section BundlePart24
/- Source: Papers/GraphicalZonotopes/DiamondData.lean -/








@[expose] public section
namespace GraphicalZonotopes.DiamondGeometry
open Finset
open scoped BigOperators Pointwise
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

def edges : Finset (Finset (Fin 10)) :=
  {{0,1}, {0,2}, {1,2}, {0,3}, {1,3}, {0,4}, {1,4}, {0,5}, {1,5}, {0,6}, {1,6}, {0,7}, {1,7}, {0,8}, {1,8}, {0,9}, {1,9}, {3,4}, {3,5}, {2,6}, {2,7}, {2,8}, {3,8}, {2,9}, {3,9}}

def graph : SimpleGraph (Fin 10) where
  Adj u v := u≠ v ∧ {u,v}∈edges
  symm := ⟨by intro u v h; exact ⟨Ne.symm h.1,by simpa only [pair_comm] using h.2⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

instance graphDecidable : DecidableRel graph.Adj :=
  fun u v => inferInstanceAs (Decidable (u≠ v ∧ ({u,v} : Finset (Fin 10))∈edges))

def cliques : Fin 57 → Finset (Fin 10) :=
  ![{0,1}, {0,2}, {1,2}, {0,1,2}, {0,3}, {1,3}, {0,1,3}, {0,4}, {1,4}, {0,1,4}, {3,4}, {0,3,4}, {1,3,4}, {0,1,3,4}, {0,5}, {1,5}, {0,1,5}, {3,5}, {0,3,5}, {1,3,5}, {0,1,3,5}, {0,6}, {1,6}, {0,1,6}, {2,6}, {0,2,6}, {1,2,6}, {0,1,2,6}, {0,7}, {1,7}, {0,1,7}, {2,7}, {0,2,7}, {1,2,7}, {0,1,2,7}, {0,8}, {1,8}, {0,1,8}, {2,8}, {0,2,8}, {1,2,8}, {0,1,2,8}, {3,8}, {0,3,8}, {1,3,8}, {0,1,3,8}, {0,9}, {1,9}, {0,1,9}, {2,9}, {0,2,9}, {1,2,9}, {0,1,2,9}, {3,9}, {0,3,9}, {1,3,9}, {0,1,3,9}]

def coefficientsZ : Fin 57 → ℤ :=
  ![1, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, -1, 0, 0, 2, 0, 0, 2, -2, 0, 0, 1, 0, 1, 0, -1, 0, 1, 0, 0, 1, 0, -1, 0, 1, 0, 1, 0, -1, 1, 0, 1, 0, -1, 1, 1, -1, 1, 0, -1, 1, 1, -1, 0, 1]

theorem cliques_injective : Function.Injective cliques := by decide +kernel

theorem cliques_valid : ∀ i,2≤(cliques i).card ∧ graph.IsClique (cliques i) := by
  decide +kernel

theorem cliques_complete : ∀ C : Finset (Fin 10),
    IsCliqueCoordinate graph C → ∃ i,cliques i=C := by
  change ∀ C : Finset (Fin 10),(2≤ C.card ∧ ∀ u∈C,∀ v∈C,u≠ v → graph.Adj u v) → ∃ i,cliques i=C
  decide +kernel

noncomputable def function : SetFunction (Fin 10) :=
  FiniteMonomial.polynomial cliques DiamondGenerated.coefficients

theorem coefficients_cast : ∀ i,(coefficientsZ i : ℝ)=DiamondGenerated.coefficients i := by
  intro i
  fin_cases i <;> norm_num [coefficientsZ,DiamondGenerated.coefficients]

theorem normalized : TranslationNormalized function :=
  FiniteMonomial.polynomial_normalized cliques (fun i => (cliques_valid i).1) _

theorem graphical : Graphical graph function :=
  FiniteMonomial.polynomial_graphical cliques (fun i => (cliques_valid i).2) _

def slackZ (u v : Fin 10) (S : Finset (Fin 10)) : ℤ :=
  ∑ i : Fin 57,if u∈cliques i ∧ v∈cliques i ∧
    cliques i⊆insert u (insert v S) then coefficientsZ i else 0

theorem delta_eq_slackZ {u v : Fin 10} (huv : u≠ v) {S : Finset (Fin 10)}
    (hu : u∉S) (hv : v∉S) : delta function u v S=(slackZ u v S : ℝ) := by
  change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) u v S=_
  rw [FiniteMonomial.delta_polynomial cliques DiamondGenerated.coefficients huv hu hv]
  simp only [slackZ,Int.cast_sum,apply_ite,Int.cast_zero,coefficients_cast]

def neighbors (u v : Fin 10) : Finset (Fin 10) :=
  univ.filter (fun w => graph.Adj u w ∧ graph.Adj v w)

theorem neighbors_eq (u v : Fin 10) : neighbors u v=commonNeighbors graph u v := by
  ext w
  simp [neighbors]

theorem neighbors_literal_0 : neighbors 0 1={2,3,4,5,6,7,8,9} := by decide +kernel

theorem bounded_edge_0 (S : Finset (Fin 10)) (hS : S∈({2,3,4,5,6,7,8,9} : Finset (Fin 10)).powerset) :
    0≤ slackZ 0 1 S ∧ slackZ 0 1 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h2 : (2 : Fin 10) ∈ S <;>
    by_cases h3 : (3 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_1 : neighbors 0 2={1,6,7,8,9} := by decide +kernel

theorem bounded_edge_1 (S : Finset (Fin 10)) (hS : S∈({1,6,7,8,9} : Finset (Fin 10)).powerset) :
    0≤ slackZ 0 2 S ∧ slackZ 0 2 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h1 : (1 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_2 : neighbors 1 2={0,6,7,8,9} := by decide +kernel

theorem bounded_edge_2 (S : Finset (Fin 10)) (hS : S∈({0,6,7,8,9} : Finset (Fin 10)).powerset) :
    0≤ slackZ 1 2 S ∧ slackZ 1 2 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h0 : (0 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_3 : neighbors 0 3={1,4,5,8,9} := by decide +kernel

theorem bounded_edge_3 (S : Finset (Fin 10)) (hS : S∈({1,4,5,8,9} : Finset (Fin 10)).powerset) :
    0≤ slackZ 0 3 S ∧ slackZ 0 3 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h1 : (1 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_4 : neighbors 1 3={0,4,5,8,9} := by decide +kernel

theorem bounded_edge_4 (S : Finset (Fin 10)) (hS : S∈({0,4,5,8,9} : Finset (Fin 10)).powerset) :
    0≤ slackZ 1 3 S ∧ slackZ 1 3 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h0 : (0 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_5 : neighbors 0 4={1,3} := by decide +kernel

theorem bounded_edge_5 (S : Finset (Fin 10)) (hS : S∈({1,3} : Finset (Fin 10)).powerset) :
    0≤ slackZ 0 4 S ∧ slackZ 0 4 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h1 : (1 : Fin 10) ∈ S <;>
    by_cases h3 : (3 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_6 : neighbors 1 4={0,3} := by decide +kernel

theorem bounded_edge_6 (S : Finset (Fin 10)) (hS : S∈({0,3} : Finset (Fin 10)).powerset) :
    0≤ slackZ 1 4 S ∧ slackZ 1 4 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h0 : (0 : Fin 10) ∈ S <;>
    by_cases h3 : (3 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_7 : neighbors 0 5={1,3} := by decide +kernel

theorem bounded_edge_7 (S : Finset (Fin 10)) (hS : S∈({1,3} : Finset (Fin 10)).powerset) :
    0≤ slackZ 0 5 S ∧ slackZ 0 5 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h1 : (1 : Fin 10) ∈ S <;>
    by_cases h3 : (3 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_8 : neighbors 1 5={0,3} := by decide +kernel

theorem bounded_edge_8 (S : Finset (Fin 10)) (hS : S∈({0,3} : Finset (Fin 10)).powerset) :
    0≤ slackZ 1 5 S ∧ slackZ 1 5 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h0 : (0 : Fin 10) ∈ S <;>
    by_cases h3 : (3 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_9 : neighbors 0 6={1,2} := by decide +kernel

theorem bounded_edge_9 (S : Finset (Fin 10)) (hS : S∈({1,2} : Finset (Fin 10)).powerset) :
    0≤ slackZ 0 6 S ∧ slackZ 0 6 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h1 : (1 : Fin 10) ∈ S <;>
    by_cases h2 : (2 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_10 : neighbors 1 6={0,2} := by decide +kernel

theorem bounded_edge_10 (S : Finset (Fin 10)) (hS : S∈({0,2} : Finset (Fin 10)).powerset) :
    0≤ slackZ 1 6 S ∧ slackZ 1 6 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h0 : (0 : Fin 10) ∈ S <;>
    by_cases h2 : (2 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_11 : neighbors 0 7={1,2} := by decide +kernel

theorem bounded_edge_11 (S : Finset (Fin 10)) (hS : S∈({1,2} : Finset (Fin 10)).powerset) :
    0≤ slackZ 0 7 S ∧ slackZ 0 7 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h1 : (1 : Fin 10) ∈ S <;>
    by_cases h2 : (2 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_12 : neighbors 1 7={0,2} := by decide +kernel

theorem bounded_edge_12 (S : Finset (Fin 10)) (hS : S∈({0,2} : Finset (Fin 10)).powerset) :
    0≤ slackZ 1 7 S ∧ slackZ 1 7 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h0 : (0 : Fin 10) ∈ S <;>
    by_cases h2 : (2 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_13 : neighbors 0 8={1,2,3} := by decide +kernel

theorem bounded_edge_13 (S : Finset (Fin 10)) (hS : S∈({1,2,3} : Finset (Fin 10)).powerset) :
    0≤ slackZ 0 8 S ∧ slackZ 0 8 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h1 : (1 : Fin 10) ∈ S <;>
    by_cases h2 : (2 : Fin 10) ∈ S <;>
    by_cases h3 : (3 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_14 : neighbors 1 8={0,2,3} := by decide +kernel

theorem bounded_edge_14 (S : Finset (Fin 10)) (hS : S∈({0,2,3} : Finset (Fin 10)).powerset) :
    0≤ slackZ 1 8 S ∧ slackZ 1 8 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h0 : (0 : Fin 10) ∈ S <;>
    by_cases h2 : (2 : Fin 10) ∈ S <;>
    by_cases h3 : (3 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_15 : neighbors 0 9={1,2,3} := by decide +kernel

theorem bounded_edge_15 (S : Finset (Fin 10)) (hS : S∈({1,2,3} : Finset (Fin 10)).powerset) :
    0≤ slackZ 0 9 S ∧ slackZ 0 9 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h1 : (1 : Fin 10) ∈ S <;>
    by_cases h2 : (2 : Fin 10) ∈ S <;>
    by_cases h3 : (3 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_16 : neighbors 1 9={0,2,3} := by decide +kernel

theorem bounded_edge_16 (S : Finset (Fin 10)) (hS : S∈({0,2,3} : Finset (Fin 10)).powerset) :
    0≤ slackZ 1 9 S ∧ slackZ 1 9 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h0 : (0 : Fin 10) ∈ S <;>
    by_cases h2 : (2 : Fin 10) ∈ S <;>
    by_cases h3 : (3 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_17 : neighbors 3 4={0,1} := by decide +kernel

theorem bounded_edge_17 (S : Finset (Fin 10)) (hS : S∈({0,1} : Finset (Fin 10)).powerset) :
    0≤ slackZ 3 4 S ∧ slackZ 3 4 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h0 : (0 : Fin 10) ∈ S <;>
    by_cases h1 : (1 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_18 : neighbors 3 5={0,1} := by decide +kernel

theorem bounded_edge_18 (S : Finset (Fin 10)) (hS : S∈({0,1} : Finset (Fin 10)).powerset) :
    0≤ slackZ 3 5 S ∧ slackZ 3 5 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h0 : (0 : Fin 10) ∈ S <;>
    by_cases h1 : (1 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_19 : neighbors 2 6={0,1} := by decide +kernel

theorem bounded_edge_19 (S : Finset (Fin 10)) (hS : S∈({0,1} : Finset (Fin 10)).powerset) :
    0≤ slackZ 2 6 S ∧ slackZ 2 6 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h0 : (0 : Fin 10) ∈ S <;>
    by_cases h1 : (1 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_20 : neighbors 2 7={0,1} := by decide +kernel

theorem bounded_edge_20 (S : Finset (Fin 10)) (hS : S∈({0,1} : Finset (Fin 10)).powerset) :
    0≤ slackZ 2 7 S ∧ slackZ 2 7 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h0 : (0 : Fin 10) ∈ S <;>
    by_cases h1 : (1 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_21 : neighbors 2 8={0,1} := by decide +kernel

theorem bounded_edge_21 (S : Finset (Fin 10)) (hS : S∈({0,1} : Finset (Fin 10)).powerset) :
    0≤ slackZ 2 8 S ∧ slackZ 2 8 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h0 : (0 : Fin 10) ∈ S <;>
    by_cases h1 : (1 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_22 : neighbors 3 8={0,1} := by decide +kernel

theorem bounded_edge_22 (S : Finset (Fin 10)) (hS : S∈({0,1} : Finset (Fin 10)).powerset) :
    0≤ slackZ 3 8 S ∧ slackZ 3 8 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h0 : (0 : Fin 10) ∈ S <;>
    by_cases h1 : (1 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_23 : neighbors 2 9={0,1} := by decide +kernel

theorem bounded_edge_23 (S : Finset (Fin 10)) (hS : S∈({0,1} : Finset (Fin 10)).powerset) :
    0≤ slackZ 2 9 S ∧ slackZ 2 9 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h0 : (0 : Fin 10) ∈ S <;>
    by_cases h1 : (1 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem neighbors_literal_24 : neighbors 3 9={0,1} := by decide +kernel

theorem bounded_edge_24 (S : Finset (Fin 10)) (hS : S∈({0,1} : Finset (Fin 10)).powerset) :
    0≤ slackZ 3 9 S ∧ slackZ 3 9 S≤4 := by
  norm_num [slackZ, cliques, coefficientsZ, Fin.sum_univ_succ, Finset.insert_subset_iff]
  all_goals
    by_cases h0 : (0 : Fin 10) ∈ S <;>
    by_cases h1 : (1 : Fin 10) ∈ S <;>
    simp_all only [and_true, and_false, true_and, false_and, ite_true, ite_false]
  all_goals (try split_ifs) <;> norm_num

theorem edge_orientation_certificate : ∀ u v : Fin 10,u< v → graph.Adj u v →
  (u=0 ∧ v=1) ∨ (u=0 ∧ v=2) ∨ (u=1 ∧ v=2) ∨ (u=0 ∧ v=3) ∨ (u=1 ∧ v=3) ∨ (u=0 ∧ v=4) ∨ (u=1 ∧ v=4) ∨ (u=0 ∧ v=5) ∨ (u=1 ∧ v=5) ∨ (u=0 ∧ v=6) ∨ (u=1 ∧ v=6) ∨ (u=0 ∧ v=7) ∨ (u=1 ∧ v=7) ∨ (u=0 ∧ v=8) ∨ (u=1 ∧ v=8) ∨ (u=0 ∧ v=9) ∨ (u=1 ∧ v=9) ∨ (u=3 ∧ v=4) ∨ (u=3 ∧ v=5) ∨ (u=2 ∧ v=6) ∨ (u=2 ∧ v=7) ∨ (u=2 ∧ v=8) ∨ (u=3 ∧ v=8) ∨ (u=2 ∧ v=9) ∨ (u=3 ∧ v=9) := by decide +kernel

theorem bounded_slack_certificate : ∀ u v : Fin 10,u< v → graph.Adj u v →
    ∀ S : Finset (Fin 10),S∈(neighbors u v).powerset →
      0≤ slackZ u v S ∧ slackZ u v S≤4 := by
  intro u v hlt he S hS
  rcases edge_orientation_certificate u v hlt he with
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rw [neighbors_literal_0] at hS
    exact bounded_edge_0 S hS
  · rw [neighbors_literal_1] at hS
    exact bounded_edge_1 S hS
  · rw [neighbors_literal_2] at hS
    exact bounded_edge_2 S hS
  · rw [neighbors_literal_3] at hS
    exact bounded_edge_3 S hS
  · rw [neighbors_literal_4] at hS
    exact bounded_edge_4 S hS
  · rw [neighbors_literal_5] at hS
    exact bounded_edge_5 S hS
  · rw [neighbors_literal_6] at hS
    exact bounded_edge_6 S hS
  · rw [neighbors_literal_7] at hS
    exact bounded_edge_7 S hS
  · rw [neighbors_literal_8] at hS
    exact bounded_edge_8 S hS
  · rw [neighbors_literal_9] at hS
    exact bounded_edge_9 S hS
  · rw [neighbors_literal_10] at hS
    exact bounded_edge_10 S hS
  · rw [neighbors_literal_11] at hS
    exact bounded_edge_11 S hS
  · rw [neighbors_literal_12] at hS
    exact bounded_edge_12 S hS
  · rw [neighbors_literal_13] at hS
    exact bounded_edge_13 S hS
  · rw [neighbors_literal_14] at hS
    exact bounded_edge_14 S hS
  · rw [neighbors_literal_15] at hS
    exact bounded_edge_15 S hS
  · rw [neighbors_literal_16] at hS
    exact bounded_edge_16 S hS
  · rw [neighbors_literal_17] at hS
    exact bounded_edge_17 S hS
  · rw [neighbors_literal_18] at hS
    exact bounded_edge_18 S hS
  · rw [neighbors_literal_19] at hS
    exact bounded_edge_19 S hS
  · rw [neighbors_literal_20] at hS
    exact bounded_edge_20 S hS
  · rw [neighbors_literal_21] at hS
    exact bounded_edge_21 S hS
  · rw [neighbors_literal_22] at hS
    exact bounded_edge_22 S hS
  · rw [neighbors_literal_23] at hS
    exact bounded_edge_23 S hS
  · rw [neighbors_literal_24] at hS
    exact bounded_edge_24 S hS

end GraphicalZonotopes.DiamondGeometry

end
end BundlePart24

section BundlePart25
/- Source: Papers/GraphicalZonotopes/ZonotopeEdges.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise

section FiniteSums
variable {E I : Type*} [AddCommGroup E] [Module ℝ E]

theorem sum_update_difference [DecidableEq I] (s : Finset I) (f : I → E)
    {i : I} (hi : i ∈ s) (x : E) :
    (∑ j ∈ s, Function.update f i x j) - ∑ j ∈ s, f j = x-f i := by
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [Function.update_of_ne hji]
  · exact fun hn => False.elim (hn hi)

theorem mixed_sum_mem [DecidableEq I] (s : Finset I) (K : I → Set E)
    (f : I → E) (hf : ∀ i ∈ s, f i ∈ K i) {i : I}
    (x : E) (hx : x ∈ K i) :
    (∑ j ∈ s, Function.update f i x j) ∈ ∑ j ∈ s, K j := by
  apply Set.finsetSum_mem_finsetSum
  intro j hj
  by_cases hji : j = i
  · subst j
    simpa using hx
  · simpa [Function.update_of_ne hji] using hf j hj

/-- A nondegenerate exposed edge of a finite Minkowski sum of segments is
parallel to one of the summand segments. All faces here are actual exposed
subsets of the Minkowski sum, not abstract cone coordinates. -/
theorem exposed_edge_of_sum_segments (s : Finset I) (a b : I → E)
    {p q : E} (hpq : p ≠ q) (l : E →ₗ[ℝ] ℝ) (c : ℝ)
    (hbound : ∀ x ∈ (∑ i ∈ s, segment ℝ (a i) (b i)), c ≤ l x)
    (hface : {x ∈ (∑ i ∈ s, segment ℝ (a i) (b i)) | l x = c} =
      segment ℝ p q) :
    ∃ i ∈ s, ∃ t : ℝ, t ≠ 0 ∧ q-p = t • (b i-a i) := by
  classical
  have hp : p ∈ (∑ i ∈ s, segment ℝ (a i) (b i)) ∧ l p = c := by
    exact hface.symm.subset (left_mem_segment ℝ p q)
  have hq : q ∈ (∑ i ∈ s, segment ℝ (a i) (b i)) ∧ l q = c := by
    exact hface.symm.subset (right_mem_segment ℝ p q)
  obtain ⟨f,hf,hfp⟩ := (Set.mem_finsetSum s (fun i => segment ℝ (a i) (b i)) p).mp hp.1
  obtain ⟨g,hg,hgq⟩ := (Set.mem_finsetSum s (fun i => segment ℝ (a i) (b i)) q).mp hq.1
  have hdiff : ∃ i ∈ s, f i ≠ g i := by
    by_contra hn
    push_neg at hn
    apply hpq
    rw [← hfp,← hgq]
    exact sum_congr rfl hn
  obtain ⟨i,hi,hine⟩ := hdiff
  let r := ∑ j ∈ s, Function.update f i (g i) j
  let u := ∑ j ∈ s, Function.update g i (f i) j
  have hr : r ∈ (∑ j ∈ s, segment ℝ (a j) (b j)) :=
    mixed_sum_mem s _ f (fun j hj => hf hj) (g i) (hg hi)
  have hu : u ∈ (∑ j ∈ s, segment ℝ (a j) (b j)) :=
    mixed_sum_mem s _ g (fun j hj => hg hj) (f i) (hf hi)
  have hrsub : r-p = g i-f i := by
    dsimp [r]
    rw [← hfp]
    exact sum_update_difference s f hi (g i)
  have husub : u-q = f i-g i := by
    dsimp [u]
    rw [← hgq]
    exact sum_update_difference s g hi (f i)
  have hrl : l r = c := by
    have h₁ := hbound r hr
    have h₂ := hbound u hu
    have h₃ := congrArg l hrsub
    have h₄ := congrArg l husub
    simp only [map_sub,hp.2,hq.2] at h₃ h₄
    linarith
  have hrseg : r ∈ segment ℝ p q := by
    rw [← hface]
    exact ⟨hr,hrl⟩
  have hspan : g i-f i ∈ Submodule.span ℝ {q-p} := by
    have h := vsub_mem_vectorSpan ℝ hrseg (left_mem_segment ℝ p q)
    rw [vectorSpan_segment] at h
    simpa only [vsub_eq_sub,hrsub] using h
  have hgen : g i-f i ∈ Submodule.span ℝ {b i-a i} := by
    have h := vsub_mem_vectorSpan ℝ (hg hi) (hf hi)
    rw [vectorSpan_segment] at h
    exact h
  obtain ⟨α,hα⟩ := Submodule.mem_span_singleton.mp hspan
  obtain ⟨β,hβ⟩ := Submodule.mem_span_singleton.mp hgen
  have hα0 : α ≠ 0 := by
    intro h
    rw [h,zero_smul] at hα
    exact hine (sub_eq_zero.mp hα.symm).symm
  have hβ0 : β ≠ 0 := by
    intro h
    rw [h,zero_smul] at hβ
    exact hine (sub_eq_zero.mp hβ.symm).symm
  refine ⟨i,hi,α⁻¹*β,mul_ne_zero (inv_ne_zero hα0) hβ0,?_⟩
  calc
    q-p = α⁻¹ • (α • (q-p)) := by simp [smul_smul,hα0]
    _ = α⁻¹ • (β • (b i-a i)) := by rw [hα,hβ]
    _ = (α⁻¹*β) • (b i-a i) := by rw [smul_smul]

end FiniteSums

section Graphs
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem smul_segment_eq (k : ℝ) (p q : V → ℝ) :
    k • segment ℝ p q = segment ℝ (k • p) (k • q) := by
  change (fun x : V → ℝ => k • x) '' segment ℝ p q = _
  exact image_segment ℝ ((k • (LinearMap.id : (V → ℝ) →ₗ[ℝ] (V → ℝ))).toAffineMap) p q

/-- Every exposed edge of a dilated graphical zonotope has one of the graph's
actual standard-root directions. This holds even for disconnected graphs. -/
theorem graphical_zonotope_exposed_edge (G : SimpleGraph V) (k : ℝ)
    {p q : V → ℝ} (hex : IsExposedSegment (k • graphicalZonotope G) p q) :
    ∃ u v, G.Adj u v ∧ ∃ t : ℝ, t ≠ 0 ∧
      q-p = t • (basisVector v-basisVector u) := by
  classical
  let Edge := {C : Finset V // C ∈ edgeFamily G}
  have hpairs : ∀ C : Edge, ∃ u v : V, u ≠ v ∧ C.1 = {u,v} := by
    intro C
    exact card_eq_two.mp ((mem_edgeFamily G C.1).mp C.2).1
  choose u v huv hC using hpairs
  have hsum : k • graphicalZonotope G =
      ∑ C : Edge, segment ℝ (k • basisVector (u C)) (k • basisVector (v C)) := by
    have hs : graphicalZonotope G = ∑ C : Edge, coordinateSimplex C.1 := by
      exact (Finset.sum_coe_sort (edgeFamily G) coordinateSimplex).symm
    rw [hs,Finset.smul_sum]
    apply sum_congr rfl
    intro C hmem
    rw [hC C,coordinateSimplex_pair,smul_segment_eq]
  obtain ⟨hpq,l,c,hbound,hface⟩ := hex
  rw [hsum] at hbound hface
  obtain ⟨C,hmem,t,ht,hdir⟩ := exposed_edge_of_sum_segments (univ : Finset Edge)
    (fun C => k • basisVector (u C)) (fun C => k • basisVector (v C))
    hpq l c hbound hface
  have hadj : G.Adj (u C) (v C) := by
    have hh := C.2
    rw [hC C] at hh
    exact (pair_mem_edgeFamily G (huv C)).mp hh
  have he : q-p = (t*k) • (basisVector (v C)-basisVector (u C)) := by
    simpa only [← smul_sub,smul_smul] using hdir
  have htk : t*k ≠ 0 := by
    intro hz
    rw [hz,zero_smul,sub_eq_zero] at he
    exact hpq he.symm
  exact ⟨u C,v C,hadj,t*k,htk,he⟩

/-- A nonzero standard root cannot be parallel to a root supported on a
different unordered pair. -/
theorem adjacency_of_root_parallel (G : SimpleGraph V) {u v a b : V}
    (huv : u ≠ v) (hab : G.Adj a b) {c d : ℝ} (hc : c ≠ 0)
    (h : c • (basisVector u-basisVector v) = d • (basisVector a-basisVector b)) :
    G.Adj u v := by
  have hu : u = a ∨ u = b := by
    by_contra hn
    push_neg at hn
    have he := congrFun h u
    simp [basisVector,Pi.single_apply,huv,Ne.symm huv,hn.1,hn.2,
      Ne.symm hn.1,Ne.symm hn.2] at he
    exact hc he
  have hv : v = a ∨ v = b := by
    by_contra hn
    push_neg at hn
    have he := congrFun h v
    simp [basisVector,Pi.single_apply,huv,Ne.symm huv,hn.1,hn.2,
      Ne.symm hn.1,Ne.symm hn.2] at he
    exact hc he
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact False.elim (huv rfl)
  · exact hab
  · exact G.adj_symm hab
  · exact False.elim (huv rfl)

theorem graphical_zonotope_actualRootEdge (G : SimpleGraph V) (k : ℝ)
    {u v : V} (h : ActualRootEdge (k • graphicalZonotope G) u v) : G.Adj u v := by
  obtain ⟨huv,p,q,hex,c,hc,hpq⟩ := h
  obtain ⟨a,b,hab,d,hd,he⟩ := graphical_zonotope_exposed_edge G k hex
  exact adjacency_of_root_parallel G huv (G.adj_symm hab) hc (hpq.symm.trans he)

end Graphs

end GraphicalZonotopes

end
end
end BundlePart25

section BundlePart26
/- Source: Papers/GraphicalZonotopes/FiniteLinearAvoidance.lean -/








@[expose] public section
noncomputable section
namespace Papers.Geometry
open Finset Set
variable {V ι : Type*} [AddCommGroup V] [Module ℝ V] [Fintype ι]

/-- A direct finite induction for the exact linear-form avoidance needed by
the exposed-edge perturbation. Every excluded value is an explicit root of
an affine function of one real scalar. -/
theorem exists_forall_linear_forms_ne_zero (forms : ι → V →ₗ[ℝ] ℝ)
    (hforms : ∀ i,∃ x,forms i x≠0) : ∃ x,∀ i,forms i x≠0 := by
  classical
  have aux : ∀ s : Finset ι,∃ x,∀ i∈s,forms i x≠0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0,by simp⟩
    | @insert i s hi ih =>
      obtain ⟨x,hx⟩ := ih
      by_cases hix : forms i x≠0
      · refine ⟨x,?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hix
        · exact hx j hj
      · have hix0 : forms i x=0 := not_not.mp hix
        obtain ⟨y,hy⟩ := hforms i
        let bad : Finset ℝ := s.image fun j => -forms j x/forms j y
        obtain ⟨t,ht,hnotbad⟩ := (Set.Ioo_infinite (show (0 : ℝ)<1 by norm_num)).exists_notMem_finset bad
        refine ⟨x+t • y,?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · rw [map_add,map_smul,smul_eq_mul,hix0,zero_add]
          exact mul_ne_zero (ne_of_gt ht.1) hy
        · by_cases hjy : forms j y=0
          · simpa only [map_add,map_smul,smul_eq_mul,hjy,mul_zero,add_zero] using hx j hj
          · intro hz
            have htroot : -forms j x/forms j y=t := by
              apply (div_eq_iff hjy).mpr
              simp only [map_add,map_smul,smul_eq_mul] at hz
              linarith only [hz]
            exact hnotbad (Finset.mem_image.mpr ⟨j,hj,htroot⟩)
  obtain ⟨x,hx⟩ := aux Finset.univ
  exact ⟨x,fun i => hx i (Finset.mem_univ i)⟩

end Papers.Geometry

end
end
end BundlePart26

section BundlePart27
/- Source: Papers/FiniteAvoidance.lean -/








@[expose] public section

/-!
# Perturbing a functional away from finitely many hyperplanes

The statements apply to any real normed vector space, including a subspace
of a dual space. They are used to select exposing functionals while retaining
the strict inequalities that define an exposed face.
-/

noncomputable section

namespace Papers.Geometry

open Set

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

theorem exists_near_forall_ne_zero (forms : ι → V →L[ℝ] ℝ)
    (hforms : ∀ i, ∃ x, forms i x ≠ 0) (v : V) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : V, dist w v < ε ∧ ∀ i, forms i w ≠ 0 := by
  classical
  obtain ⟨direction, hdirection⟩ :=
    exists_forall_linear_forms_ne_zero
      (fun i => (forms i).toLinearMap) hforms
  let δ := ε / (‖direction‖ + 1)
  have hden : 0 < ‖direction‖ + 1 := by linarith [norm_nonneg direction]
  have hδ : 0 < δ := div_pos hε hden
  let bad : Finset ℝ := Finset.univ.image (fun i => -forms i v / forms i direction)
  obtain ⟨t, ht, hnotbad⟩ := (Set.Ioo_infinite hδ).exists_notMem_finset bad
  refine ⟨v + t • direction, ?_, ?_⟩
  · have hprod : t * (‖direction‖ + 1) < ε := (lt_div_iff₀ hden).mp ht.2
    have hdist : dist (v + t • direction) v = t * ‖direction‖ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
    rw [hdist]
    nlinarith [ht.1]
  · intro i hzero
    apply hnotbad
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    symm
    apply (eq_div_iff (hdirection i)).mpr
    change t * (forms i) direction = -(forms i) v
    simp only [map_add, map_smul, smul_eq_mul] at hzero
    linarith only [hzero]

/-- A nonempty open set cannot be covered by finitely many proper linear
hyperplanes. The point can be chosen inside the original open set. -/
theorem exists_in_open_forall_ne_zero (forms : ι → V →L[ℝ] ℝ)
    (hforms : ∀ i, ∃ x, forms i x ≠ 0) {U : Set V}
    (hopen : IsOpen U) (hne : U.Nonempty) :
    ∃ w ∈ U, ∀ i, forms i w ≠ 0 := by
  obtain ⟨v, hv⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen v hv
  obtain ⟨w, hw, hall⟩ := exists_near_forall_ne_zero forms hforms v hε
  exact ⟨w, hball hw, hall⟩

end Papers.Geometry

end
end
end BundlePart27

section BundlePart28
/- Source: Papers/FiniteConvexGeometry.lean -/










@[expose] public section

/-!
# Finite convex hulls and one-dimensional exposed faces

The argument for `mem_hull_of_maximizers` is adapted from Daniele Cappello's
Apache-2.0-licensed `FacciaArgmax` module; see THIRD_PARTY.md. Its proof needs
only a normed vector space, so the stronger inner-product hypothesis in that
source is omitted here.
-/

noncomputable section
namespace Papers.Geometry
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mem_hull_of_maximizers (s : Finset E) (l : E →L[ℝ] ℝ) {y : E}
    (hy : y ∈ convexHull ℝ (s : Set E))
    (hmax : ∀ w ∈ convexHull ℝ (s : Set E), l w ≤ l y) :
    y ∈ convexHull ℝ {x ∈ (s : Set E) | l x = l y} := by
  classical
  rw [Finset.convexHull_eq] at hy
  obtain ⟨w, hw0, hw1, hwy⟩ := hy
  have hM : ∀ x ∈ s, l x ≤ l y := fun x hx =>
    hmax x (subset_convexHull ℝ _ hx)
  have hyrep : y = ∑ x ∈ s, w x • x := by
    rw [← hwy, Finset.centerMass_eq_of_sum_1 _ _ hw1]
    rfl
  have hly : l y = ∑ x ∈ s, w x * l x := by
    rw [hyrep, map_sum]
    congr 1
    funext x
    rw [map_smul]
    rfl
  have hactive : ∀ x ∈ s, 0 < w x → l x = l y := by
    intro x hx hwx
    by_contra hne
    have hlt : l x < l y := lt_of_le_of_ne (hM x hx) hne
    have hsum : ∑ z ∈ s, w z * l z < ∑ z ∈ s, w z * l y := by
      apply Finset.sum_lt_sum
      · intro z hz
        exact mul_le_mul_of_nonneg_left (hM z hz) (hw0 z hz)
      · exact ⟨x, hx, mul_lt_mul_of_pos_left hlt hwx⟩
    rw [← Finset.sum_mul, hw1, one_mul] at hsum
    rw [hly] at hsum
    exact lt_irrefl _ hsum
  have hzero : ∀ x ∈ s, ¬l x = l y → w x = 0 := by
    intro x hx hne
    by_contra hw
    exact hne (hactive x hx (lt_of_le_of_ne (hw0 x hx) (Ne.symm hw)))
  let sf : Finset E := s.filter (fun x => l x = l y)
  have hsub : sf ⊆ s := Finset.filter_subset _ _
  have hw1' : ∑ x ∈ sf, w x = 1 := by
    rw [← hw1]
    symm
    apply (Finset.sum_subset hsub ?_).symm
    intro x hx hnx
    apply hzero x hx
    intro heq
    exact hnx (Finset.mem_filter.mpr ⟨hx, heq⟩)
  have hyrep' : y = ∑ x ∈ sf, w x • x := by
    rw [hyrep]
    symm
    apply Finset.sum_subset hsub
    intro x hx hnx
    have : w x = 0 := by
      apply hzero x hx
      intro heq
      exact hnx (Finset.mem_filter.mpr ⟨hx, heq⟩)
    rw [this, zero_smul]
  have hmem : y ∈ convexHull ℝ (sf : Set E) := by
    rw [Finset.convexHull_eq]
    refine ⟨w, fun z hz => hw0 z (hsub hz), hw1', ?_⟩
    rw [Finset.centerMass_eq_of_sum_1 _ _ hw1']
    exact hyrep'.symm
  have hset : (sf : Set E) = {x ∈ (s : Set E) | l x = l y} := by
    ext x
    simp [sf]
  rw [← hset]
  exact hmem

theorem mem_hull_of_minimizers (s : Finset E) (l : E →L[ℝ] ℝ) {y : E}
    (hy : y ∈ convexHull ℝ (s : Set E))
    (hmin : ∀ w ∈ convexHull ℝ (s : Set E), l y ≤ l w) :
    y ∈ convexHull ℝ {x ∈ (s : Set E) | l x = l y} := by
  simpa only [ContinuousLinearMap.neg_apply, neg_inj] using
    mem_hull_of_maximizers s (-l) hy (by
      simpa only [ContinuousLinearMap.neg_apply, neg_le_neg_iff] using hmin)

theorem linear_lower_bound_on_convexHull (s : Set E) (l : E →L[ℝ] ℝ)
    (a : ℝ) (ha : ∀ x ∈ s, a ≤ l x) :
    ∀ x ∈ convexHull ℝ s, a ≤ l x :=
  convexHull_min ha (convex_halfSpace_ge (LinearMap.isLinear l.toLinearMap) a)

/-- A finite convex hull contained in an affine line is a genuine closed
segment with endpoints among its generators. Degenerate segments are allowed. -/
theorem finite_hull_parallel_eq_segment (s : Finset E) (hs : s.Nonempty)
    (δ : E) (hδ : δ ≠ 0)
    (hparallel : ∀ x ∈ s, ∀ y ∈ s, x - y ∈ Submodule.span ℝ {δ}) :
    ∃ x ∈ s, ∃ y ∈ s, convexHull ℝ (s : Set E) = segment ℝ x y := by
  classical
  have hnot : δ ∉ (⊥ : Submodule ℝ E) := by simpa using hδ
  obtain ⟨g, hg, _⟩ := Submodule.exists_le_ker_of_notMem hnot
  let l : E →ₗ[ℝ] ℝ := (g δ)⁻¹ • g
  have hl : l δ = 1 := by simp [l, hg]
  obtain ⟨x, hx, hxmin⟩ := s.exists_min_image l hs
  obtain ⟨y, hy, hymax⟩ := s.exists_max_image l hs
  have hform (z : E) (hz : z ∈ s) : z - x = (l z - l x) • δ := by
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hparallel z hz x hx)
    have he : a = l z - l x := by
      have h := congrArg l ha
      simpa only [map_smul, map_sub, smul_eq_mul, hl, mul_one] using h
    exact (he ▸ ha).symm
  have hgen : (s : Set E) ⊆ segment ℝ x y := by
    intro z hz
    have hlow := hxmin z hz
    have hupp := hymax z hz
    have hxy := hxmin y hy
    by_cases hb : l y - l x = 0
    · have hzval : l z - l x = 0 := by linarith
      have hzx : z = x := by
        have h := hform z hz
        rw [hzval, zero_smul, sub_eq_zero] at h
        exact h
      rw [hzx]
      exact left_mem_segment ℝ x y
    · have hbpos : 0 < l y - l x := lt_of_le_of_ne (sub_nonneg.mpr hxy) (Ne.symm hb)
      rw [segment_eq_image']
      refine ⟨(l z - l x) / (l y - l x), ⟨div_nonneg (sub_nonneg.mpr hlow) hbpos.le,
        (div_le_one hbpos).mpr (by linarith)⟩, ?_⟩
      change x + ((l z - l x) / (l y - l x)) • (y - x) = z
      rw [hform y hy, smul_smul, div_mul_cancel₀ _ hb, ← hform z hz]
      module
  refine ⟨x, hx, y, hy, Set.Subset.antisymm
    (convexHull_min hgen (convex_segment x y)) ?_⟩
  exact (convex_convexHull ℝ (s : Set E)).segment_subset
    (subset_convexHull ℝ _ hx) (subset_convexHull ℝ _ hy)

end Papers.Geometry

end
end
end BundlePart28

section BundlePart29
/- Source: Papers/MinkowskiEdges.lean -/









@[expose] public section

/-!
# Exposed edges of Minkowski summands

All sets in the theorem are actual finite convex hulls. The exposing
functional is perturbed in the annihilator of the given edge direction.
This preserves that edge and eliminates all additional independent
directions among the minimizing generators of the sum.
-/

noncomputable section
namespace Papers.Geometry
open Set
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def ExposesSegment (Q : Set E) (l : E →L[ℝ] ℝ) (a : ℝ) (p q : E) : Prop :=
  (∀ x ∈ Q, a ≤ l x) ∧ {x ∈ Q | l x = a} = segment ℝ p q

theorem ExposesSegment.left_mem {Q : Set E} {l : E →L[ℝ] ℝ} {a : ℝ} {p q : E}
    (h : ExposesSegment Q l a p q) : p ∈ Q ∧ l p = a := by
  change p ∈ {x ∈ Q | l x = a}
  rw [h.2]
  exact left_mem_segment ℝ p q

theorem ExposesSegment.right_mem {Q : Set E} {l : E →L[ℝ] ℝ} {a : ℝ} {p q : E}
    (h : ExposesSegment Q l a p q) : q ∈ Q ∧ l q = a := by
  change q ∈ {x ∈ Q | l x = a}
  rw [h.2]
  exact right_mem_segment ℝ p q

theorem minimizers_eq_hull (s : Finset E) (l : E →L[ℝ] ℝ) (a : ℝ)
    (hbound : ∀ v ∈ s, a ≤ l v) :
    {x ∈ convexHull ℝ (s : Set E) | l x = a} =
      convexHull ℝ {v ∈ (s : Set E) | l v = a} := by
  have hglobal := linear_lower_bound_on_convexHull (s : Set E) l a hbound
  apply Set.Subset.antisymm
  · rintro x ⟨hx, hxa⟩
    have h := mem_hull_of_minimizers s l hx (by simpa [hxa] using hglobal)
    simpa [hxa] using h
  · intro x hx
    refine ⟨convexHull_mono (by intro y hy; exact hy.1) hx, ?_⟩
    apply le_antisymm
    · have h := linear_lower_bound_on_convexHull
        {v ∈ (s : Set E) | l v = a} (-l) (-a)
        (by intro v hv; simp [hv.2]) x hx
      simpa only [ContinuousLinearMap.neg_apply, neg_le_neg_iff] using h
    · exact linear_lower_bound_on_convexHull
        {v ∈ (s : Set E) | l v = a} l a (by intro v hv; exact hv.2.ge) x hx

theorem constant_on_segment (l : E →L[ℝ] ℝ) {p q : E} (heq : l p = l q)
    {x : E} (hx : x ∈ segment ℝ p q) : l x = l p := by
  obtain ⟨a, b, _, _, hab, rfl⟩ := hx
  simp only [map_add, map_smul, smul_eq_mul, ← heq, ← add_mul, hab, one_mul]

section Perturbation

variable [FiniteDimensional ℝ E]

/-- Preserve an exposed segment of one finite hull while separating every
pair of generators of another hull whose difference is not its direction. -/
theorem perturb_exposing_segment (s t : Finset E) {p q : E}
    (l₀ : E →L[ℝ] ℝ) (a : ℝ)
    (hex : ExposesSegment (convexHull ℝ (s : Set E)) l₀ a p q) :
    ∃ l : E →L[ℝ] ℝ,
      ExposesSegment (convexHull ℝ (s : Set E)) l (l p) p q ∧
      ∀ x ∈ t, ∀ y ∈ t,
        x - y ∉ Submodule.span ℝ {q - p} → l x ≠ l y := by
  classical
  let δ := q - p
  let A : Submodule ℝ (E →L[ℝ] ℝ) :=
    (ContinuousLinearMap.apply ℝ ℝ δ).ker
  have hp := hex.left_mem
  have hq := hex.right_mem
  have hl₀ : l₀ ∈ A := by
    change l₀ (q - p) = 0
    rw [map_sub, hp.2, hq.2, sub_self]
  let I := {v : s // (v : E) ∉ segment ℝ p q}
  let U : Set A := {l | ∀ v : I, l.val p < l.val v.val.val}
  have hopen : IsOpen U := by
    have hUeq : U = ⋂ v : I, {l : A | l.val p < l.val v.val.val} := by
      ext l
      simp only [U, Set.mem_setOf_eq, Set.mem_iInter]
    rw [hUeq]
    apply isOpen_iInter_of_finite
    intro v
    exact isOpen_lt
      ((ContinuousLinearMap.apply ℝ ℝ p).continuous.comp continuous_subtype_val)
      ((ContinuousLinearMap.apply ℝ ℝ v.val.val).continuous.comp continuous_subtype_val)
  have hU : U.Nonempty := by
    refine ⟨⟨l₀, hl₀⟩, ?_⟩
    intro v
    have hv := hex.1 v.val.val (subset_convexHull ℝ _ v.val.property)
    change l₀ p < l₀ v.val.val
    rw [hp.2]
    apply lt_of_le_of_ne hv
    intro heq
    apply v.property
    exact hex.2.subset ⟨subset_convexHull ℝ _ v.val.property, heq.symm⟩
  let J := {z : t × t // (z.1 : E) - z.2 ∉ Submodule.span ℝ {δ}}
  let forms : J → A →L[ℝ] ℝ := fun z =>
    (ContinuousLinearMap.apply ℝ ℝ ((z.val.1 : E) - z.val.2)).comp A.subtypeL
  have hforms : ∀ z : J, ∃ l : A, forms z l ≠ 0 := by
    intro z
    obtain ⟨g, hgz, hgA⟩ := Submodule.exists_le_ker_of_notMem z.property
    let gc : E →L[ℝ] ℝ := g.toContinuousLinearMap
    have hgc : gc ∈ A := by
      change g δ = 0
      exact hgA (Submodule.subset_span (Set.mem_singleton δ))
    exact ⟨⟨gc, hgc⟩, hgz⟩
  obtain ⟨l, hlU, hlavoid⟩ := exists_in_open_forall_ne_zero forms hforms hopen hU
  have hlpq : l.val p = l.val q := by
    have h : (l : E →L[ℝ] ℝ) (q - p) = 0 := l.property
    rw [map_sub, sub_eq_zero] at h
    exact h.symm
  have hlgen : ∀ v ∈ s, l.val p ≤ l.val v := by
    intro v hv
    by_cases hvs : v ∈ segment ℝ p q
    · exact (constant_on_segment l.val hlpq hvs).ge
    · exact (hlU ⟨⟨v, hv⟩, hvs⟩).le
  have hlbound := linear_lower_bound_on_convexHull (s : Set E) l.val (l.val p) hlgen
  refine ⟨l.val, ⟨hlbound, ?_⟩, ?_⟩
  · rw [minimizers_eq_hull s l.val (l.val p) hlgen]
    apply Set.Subset.antisymm
    · apply convexHull_min _ (convex_segment p q)
      rintro v ⟨hv, hveq⟩
      by_contra hvs
      exact (ne_of_lt (hlU ⟨⟨v, hv⟩, hvs⟩)) hveq.symm
    · intro v hv
      have hbody : v ∈ convexHull ℝ (s : Set E) := by
        have h := hv
        rw [← hex.2] at h
        exact h.1
      have heq : l.val v = l.val p := constant_on_segment l.val hlpq hv
      rw [← minimizers_eq_hull s l.val (l.val p) hlgen]
      exact ⟨hbody, heq⟩
  · intro x hx y hy hxy heq
    let z : J := ⟨(⟨x, hx⟩, ⟨y, hy⟩), hxy⟩
    apply hlavoid z
    change (l : E →L[ℝ] ℝ) (x - y) = 0
    rw [map_sub, heq, sub_self]

end Perturbation

/-- Every nondegenerate exposed edge of a finite-hull Minkowski summand has
the direction of a nondegenerate exposed edge of the sum. The other summand
is arbitrary: its compactness or a prescribed vertex representation is not
assumed. -/
theorem minkowski_summand_exposed_edge_direction [FiniteDimensional ℝ E]
    (s t : Finset E) (ht : t.Nonempty) (R : Set E)
    (hsum : convexHull ℝ (t : Set E) = convexHull ℝ (s : Set E) + R)
    {p q : E} (hpq : p ≠ q) (l₀ : E →L[ℝ] ℝ) (a : ℝ)
    (hex : ExposesSegment (convexHull ℝ (s : Set E)) l₀ a p q) :
    ∃ x y : E, x ≠ y ∧
      (∃ l : E →L[ℝ] ℝ, ∃ b : ℝ,
        ExposesSegment (convexHull ℝ (t : Set E)) l b x y) ∧
      ∃ c : ℝ, c ≠ 0 ∧ y - x = c • (q - p) := by
  classical
  obtain ⟨l, hlex, hlavoid⟩ := perturb_exposing_segment s t l₀ a hex
  have hp := hlex.left_mem
  have hq := hlex.right_mem
  obtain ⟨w, hw, hwmin⟩ := t.exists_min_image l ht
  have hmin := linear_lower_bound_on_convexHull (t : Set E) l (l w) hwmin
  have hwbody : w ∈ convexHull ℝ (s : Set E) + R := by
    rw [← hsum]
    exact subset_convexHull ℝ _ hw
  obtain ⟨u, hu, r, hr, hur⟩ := Set.mem_add.mp hwbody
  have hprbody : p + r ∈ convexHull ℝ (t : Set E) := by
    rw [hsum]
    exact Set.mem_add.mpr ⟨p, hp.1, r, hr, rfl⟩
  have hqrbody : q + r ∈ convexHull ℝ (t : Set E) := by
    rw [hsum]
    exact Set.mem_add.mpr ⟨q, hq.1, r, hr, rfl⟩
  have hurval : l w = l u + l r := by rw [← hur, map_add]
  have huval : l u = l p := by
    have h₁ := hlex.1 u hu
    have h₂ := hmin (p + r) hprbody
    rw [map_add, hurval] at h₂
    linarith
  have hprval : l (p + r) = l w := by rw [map_add, hurval, huval]
  have hqrval : l (q + r) = l w := by rw [map_add, hq.2, hurval, huval]
  let sf : Finset E := t.filter (fun z => l z = l w)
  have hsf : sf.Nonempty := ⟨w, Finset.mem_filter.mpr ⟨hw, rfl⟩⟩
  have hface : {z ∈ convexHull ℝ (t : Set E) | l z = l w} =
      convexHull ℝ (sf : Set E) := by
    rw [minimizers_eq_hull t l (l w) hwmin]
    congr 1
    ext z
    simp [sf]
  have hparallel : ∀ x ∈ sf, ∀ y ∈ sf,
      x - y ∈ Submodule.span ℝ {q - p} := by
    intro x hx y hy
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    by_contra hxy
    exact hlavoid x hx'.1 y hy'.1 hxy (hx'.2.trans hy'.2.symm)
  have hδ : q - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq)
  obtain ⟨x, hx, y, hy, hsegment⟩ :=
    finite_hull_parallel_eq_segment sf hsf (q - p) hδ hparallel
  have hpr : p + r ∈ segment ℝ x y := by
    rw [← hsegment, ← hface]
    exact ⟨hprbody, hprval⟩
  have hqr : q + r ∈ segment ℝ x y := by
    rw [← hsegment, ← hface]
    exact ⟨hqrbody, hqrval⟩
  have hxy : x ≠ y := by
    intro heq
    have hp' : p + r = y := by simpa [heq] using hpr
    have hq' : q + r = y := by simpa [heq] using hqr
    exact hpq (add_right_cancel (hp'.trans hq'.symm))
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hparallel y hy x hx)
  refine ⟨x, y, hxy, ⟨l, l w, hmin, hface.trans hsegment⟩, c, ?_, hc.symm⟩
  intro hc0
  have heq : y = x := by
    rw [hc0, zero_smul, eq_comm, sub_eq_zero] at hc
    exact hc
  exact hxy heq.symm

end Papers.Geometry

end
end
end BundlePart29

section BundlePart30
/- Source: Papers/GraphicalZonotopes/SummandEdges.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An actual exposed edge of a graphical-zonotope summand has one of the
graph's standard-root directions. The complementary summand is an arbitrary
set, and the finite-hull representation of the base polytope is proved earlier. -/
theorem basePolytope_summand_exposed_edge {z : SetFunction V}
    (hn : Normalized z) (hs : Supermodular z) (G : SimpleGraph V)
    {k : ℝ} (hk : 0 ≤ k) (R : Set (V → ℝ))
    (hsum : basePolytope z + R = k • graphicalZonotope G)
    {p q : V → ℝ} (hex : IsExposedSegment (basePolytope z) p q) :
    ∃ u v, G.Adj u v ∧ ∃ t : ℝ, t ≠ 0 ∧
      q-p = t • (basisVector v-basisVector u) := by
  classical
  let f : SetFunction V := k • graphFunction G
  have hfn : Normalized f := by
    change k * graphFunction G ∅ = 0
    rw [graphFunction_normalized,mul_zero]
  have hfs : Supermodular f := (graphFunction_supermodular G).smul hk
  let s : Finset (V → ℝ) := (greedyPoints_finite z).toFinset
  let t : Finset (V → ℝ) := (greedyPoints_finite f).toFinset
  have hsbody : convexHull ℝ (s : Set (V → ℝ)) = basePolytope z := by
    simpa only [s,Set.Finite.coe_toFinset] using (basePolytope_eq_convexHull hn hs).symm
  have htbody : convexHull ℝ (t : Set (V → ℝ)) = k • graphicalZonotope G := by
    calc
      convexHull ℝ (t : Set (V → ℝ)) = basePolytope f := by
        simpa only [t,Set.Finite.coe_toFinset] using (basePolytope_eq_convexHull hfn hfs).symm
      _ = k • graphicalZonotope G := by
        change basePolytope (k • graphFunction G) = _
        rw [basePolytope_smul (graphFunction_normalized G)
          (graphFunction_supermodular G) hk,baseGraphFunction_eq_graphicalZonotope]
  have ht : t.Nonempty := by
    refine ⟨greedyPoint f (Fintype.equivFin V).symm,?_⟩
    change _ ∈ (greedyPoints_finite f).toFinset
    rw [Set.Finite.mem_toFinset]
    exact ⟨(Fintype.equivFin V).symm,rfl⟩
  obtain ⟨hpq,l,a,hbound,hface⟩ := hex
  let L : (V → ℝ) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap l
  have hsum' : convexHull ℝ (t : Set (V → ℝ)) =
      convexHull ℝ (s : Set (V → ℝ)) + R := by
    rw [hsbody,htbody]
    exact hsum.symm
  have hex' : Papers.Geometry.ExposesSegment (convexHull ℝ (s : Set (V → ℝ))) L a p q := by
    rw [hsbody]
    exact ⟨hbound,hface⟩
  obtain ⟨x,y,hxy,⟨L',b,hxyface⟩,c,hc,hxyparallel⟩ :=
    Papers.Geometry.minkowski_summand_exposed_edge_direction s t ht R hsum' hpq L a hex'
  have hxy' : IsExposedSegment (k • graphicalZonotope G) x y := by
    refine ⟨hxy,L'.toLinearMap,b,?_⟩
    simpa only [Papers.Geometry.ExposesSegment,htbody,ContinuousLinearMap.coe_coe] using hxyface
  obtain ⟨u,v,huv,d,hd,he⟩ := graphical_zonotope_exposed_edge G k hxy'
  refine ⟨u,v,huv,c⁻¹*d,mul_ne_zero (inv_ne_zero hc) hd,?_⟩
  calc
    q-p = c⁻¹ • (c • (q-p)) := by simp [smul_smul,hc]
    _ = c⁻¹ • (y-x) := by rw [hxyparallel]
    _ = c⁻¹ • (d • (basisVector v-basisVector u)) := by rw [he]
    _ = (c⁻¹*d) • (basisVector v-basisVector u) := by rw [smul_smul]

theorem basePolytope_summand_actualRootEdge {z : SetFunction V}
    (hn : Normalized z) (hs : Supermodular z) (G : SimpleGraph V)
    {k : ℝ} (hk : 0 ≤ k) (R : Set (V → ℝ))
    (hsum : basePolytope z + R = k • graphicalZonotope G)
    {u v : V} (h : ActualRootEdge (basePolytope z) u v) : G.Adj u v := by
  obtain ⟨huv,p,q,hex,c,hc,hpq⟩ := h
  obtain ⟨a,b,hab,d,hd,he⟩ := basePolytope_summand_exposed_edge hn hs G hk R hsum hex
  exact adjacency_of_root_parallel G huv (G.adj_symm hab) hc (hpq.symm.trans he)

end GraphicalZonotopes

end
end
end BundlePart30

section BundlePart31
/- Source: Papers/GraphicalZonotopes/DiamondGeometry.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes.DiamondGeometry
open Finset
open scoped BigOperators Pointwise
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

theorem elemental_bounds {u v : Fin 10} (huv : u≠ v)
    {S : Finset (Fin 10)} (hu : u∉S) (hv : v∉S) :
    0≤ delta function u v S ∧ delta function u v S≤4 := by
  have ordered : ∀ u v : Fin 10,u< v → ∀ S : Finset (Fin 10),u∉S → v∉S →
      0≤ delta function u v S ∧ delta function u v S≤4 := by
    intro a b hab T ha hb
    by_cases he : graph.Adj a b
    · let U:=T∩commonNeighbors graph a b
      have hU : U∈(neighbors a b).powerset := by
        rw [neighbors_eq,mem_powerset]
        exact inter_subset_right
      have hUa : a∉U:=fun h => ha (mem_inter.mp h).1
      have hUb : b∉U:=fun h => hb (mem_inter.mp h).1
      rw [delta_commonNeighbors normalized graphical (ne_of_lt hab) ha hb,
        delta_eq_slackZ (ne_of_lt hab) hUa hUb]
      exact_mod_cast bounded_slack_certificate a b hab he U hU
    · rw [graphical a b (ne_of_lt hab) he T ha hb]
      norm_num
  rcases lt_or_gt_of_ne huv with hlt | hgt
  · exact ordered u v hlt S hu hv
  · rw [delta_comm u v]
    exact ordered v u hgt S hv hu

theorem supermodular : Supermodular function :=
  ElementallyNonnegative.supermodular (fun _ _ huv _ hu hv => (elemental_bounds huv hu hv).1)

theorem actual_summand : IsMinkowskiSummand (basePolytope function)
    ((4 : ℝ) • graphicalZonotope graph) := by
  apply (isMinkowskiSummand_graphical_iff normalized.1 supermodular (by norm_num : (0 : ℝ)≤4)).mpr
  exact ⟨graphical,fun _ _ huv _ _ hu hv => (elemental_bounds huv hu hv).2⟩

theorem integerValued : IntegerValued function := by
  change IntegerValued (∑ i : Fin 57,DiamondGenerated.coefficients i • setMonomial (cliques i))
  apply IntegerValued.finset_sum
  intro i hi
  rw [← coefficients_cast i]
  exact (setMonomial_integerValued (cliques i)).int_smul (coefficientsZ i)

theorem tight_row_0 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 1 {2,7} = x 0 + x 3 + x 30 + x 34 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (1 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 1 ({2,7} : Finset (Fin 10)))) = {0,3,30,34} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_1 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 1 {2,4,7} = x 0 + x 3 + x 9 + x 30 + x 34 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (1 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 1 ({2,4,7} : Finset (Fin 10)))) = {0,3,9,30,34} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_2 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 1 {2,3,4,7} = x 0 + x 3 + x 6 + x 9 + x 13 + x 30 + x 34 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (1 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 1 ({2,3,4,7} : Finset (Fin 10)))) = {0,3,6,9,13,30,34} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_3 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 1 {2,3,4,5,7} = x 0 + x 3 + x 6 + x 9 + x 13 + x 16 + x 20 + x 30 + x 34 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (1 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 1 ({2,3,4,5,7} : Finset (Fin 10)))) = {0,3,6,9,13,16,20,30,34} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_4 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 1 {2,6,7} = x 0 + x 3 + x 23 + x 27 + x 30 + x 34 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (1 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 1 ({2,6,7} : Finset (Fin 10)))) = {0,3,23,27,30,34} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_5 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 1 {3,4,8} = x 0 + x 6 + x 9 + x 13 + x 37 + x 45 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (1 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 1 ({3,4,8} : Finset (Fin 10)))) = {0,6,9,13,37,45} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_6 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 1 {3,4,7,8} = x 0 + x 6 + x 9 + x 13 + x 30 + x 37 + x 45 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (1 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 1 ({3,4,7,8} : Finset (Fin 10)))) = {0,6,9,13,30,37,45} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_7 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 1 {2,3,4,7,8} = x 0 + x 3 + x 6 + x 9 + x 13 + x 30 + x 34 + x 37 + x 41 + x 45 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (1 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 1 ({2,3,4,7,8} : Finset (Fin 10)))) = {0,3,6,9,13,30,34,37,41,45} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_8 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 1 {9} = x 0 + x 48 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (1 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 1 ({9} : Finset (Fin 10)))) = {0,48} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_9 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 1 {2,7,9} = x 0 + x 3 + x 30 + x 34 + x 48 + x 52 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (1 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 1 ({2,7,9} : Finset (Fin 10)))) = {0,3,30,34,48,52} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_10 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 1 {8,9} = x 0 + x 37 + x 48 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (1 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 1 ({8,9} : Finset (Fin 10)))) = {0,37,48} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_11 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 1 {3,4,8,9} = x 0 + x 6 + x 9 + x 13 + x 37 + x 45 + x 48 + x 56 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (1 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 1 ({3,4,8,9} : Finset (Fin 10)))) = {0,6,9,13,37,45,48,56} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_12 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 2 ∅ = x 1 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (2 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 2 (∅ : Finset (Fin 10)))) = {1} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_13 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 2 {1} = x 1 + x 3 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (2 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 2 ({1} : Finset (Fin 10)))) = {1,3} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_14 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 2 {1,6} = x 1 + x 3 + x 25 + x 27 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (2 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 2 ({1,6} : Finset (Fin 10)))) = {1,3,25,27} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_15 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 2 {1,7} = x 1 + x 3 + x 32 + x 34 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (2 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 2 ({1,7} : Finset (Fin 10)))) = {1,3,32,34} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_16 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 2 {8} = x 1 + x 39 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (2 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 2 ({8} : Finset (Fin 10)))) = {1,39} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_17 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 2 {9} = x 1 + x 50 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (2 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 2 ({9} : Finset (Fin 10)))) = {1,50} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_18 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 2 {0,6,7} = x 2 + x 3 + x 26 + x 27 + x 33 + x 34 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (2 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 2 ({0,6,7} : Finset (Fin 10)))) = {2,3,26,27,33,34} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_19 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 2 {0,6,7,8} = x 2 + x 3 + x 26 + x 27 + x 33 + x 34 + x 40 + x 41 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (2 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 2 ({0,6,7,8} : Finset (Fin 10)))) = {2,3,26,27,33,34,40,41} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_20 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 2 {0,6,7,9} = x 2 + x 3 + x 26 + x 27 + x 33 + x 34 + x 51 + x 52 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (2 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 2 ({0,6,7,9} : Finset (Fin 10)))) = {2,3,26,27,33,34,51,52} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_21 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 2 {8,9} = x 2 + x 40 + x 51 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (2 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 2 ({8,9} : Finset (Fin 10)))) = {2,40,51} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_22 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 2 {6,8,9} = x 2 + x 26 + x 40 + x 51 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (2 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 2 ({6,8,9} : Finset (Fin 10)))) = {2,26,40,51} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_23 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 2 {7,8,9} = x 2 + x 33 + x 40 + x 51 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (2 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 2 ({7,8,9} : Finset (Fin 10)))) = {2,33,40,51} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_24 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 3 {1,5} = x 4 + x 6 + x 18 + x 20 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (3 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 3 ({1,5} : Finset (Fin 10)))) = {4,6,18,20} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_25 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 3 {1,4,5} = x 4 + x 6 + x 11 + x 13 + x 18 + x 20 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (3 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 3 ({1,4,5} : Finset (Fin 10)))) = {4,6,11,13,18,20} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_26 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 3 {1,5,8} = x 4 + x 6 + x 18 + x 20 + x 43 + x 45 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (3 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 3 ({1,5,8} : Finset (Fin 10)))) = {4,6,18,20,43,45} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_27 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 3 {9} = x 4 + x 54 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (3 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 3 ({9} : Finset (Fin 10)))) = {4,54} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_28 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 3 {5,9} = x 4 + x 18 + x 54 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (3 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 3 ({5,9} : Finset (Fin 10)))) = {4,18,54} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_29 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 3 {1,5,9} = x 4 + x 6 + x 18 + x 20 + x 54 + x 56 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (3 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 3 ({1,5,9} : Finset (Fin 10)))) = {4,6,18,20,54,56} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_30 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 3 ∅ = x 5 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (3 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 3 (∅ : Finset (Fin 10)))) = {5} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_31 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 3 {8} = x 5 + x 44 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (3 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 3 ({8} : Finset (Fin 10)))) = {5,44} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_32 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 3 {0,8} = x 5 + x 6 + x 44 + x 45 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (3 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 3 ({0,8} : Finset (Fin 10)))) = {5,6,44,45} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_33 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 3 {0,4,8} = x 5 + x 6 + x 12 + x 13 + x 44 + x 45 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (3 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 3 ({0,4,8} : Finset (Fin 10)))) = {5,6,12,13,44,45} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_34 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 3 {0,5,8} = x 5 + x 6 + x 19 + x 20 + x 44 + x 45 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (3 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 3 ({0,5,8} : Finset (Fin 10)))) = {5,6,19,20,44,45} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_35 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 3 {9} = x 5 + x 55 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (3 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 3 ({9} : Finset (Fin 10)))) = {5,55} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_36 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 4 ∅ = x 7 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (4 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 4 (∅ : Finset (Fin 10)))) = {7} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_37 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 4 ∅ = x 8 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (4 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 4 (∅ : Finset (Fin 10)))) = {8} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_38 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 5 ∅ = x 14 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (5 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 5 (∅ : Finset (Fin 10)))) = {14} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_39 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 5 ∅ = x 15 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (5 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 5 (∅ : Finset (Fin 10)))) = {15} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_40 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 6 ∅ = x 21 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (6 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 6 (∅ : Finset (Fin 10)))) = {21} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_41 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 6 ∅ = x 22 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (6 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 6 (∅ : Finset (Fin 10)))) = {22} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_42 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 7 ∅ = x 28 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (7 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 7 (∅ : Finset (Fin 10)))) = {28} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_43 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 7 {0,2} = x 29 + x 30 + x 33 + x 34 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (7 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 7 ({0,2} : Finset (Fin 10)))) = {29,30,33,34} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_44 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 8 ∅ = x 35 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (8 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 8 (∅ : Finset (Fin 10)))) = {35} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_45 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 8 {2} = x 36 + x 40 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (8 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 8 ({2} : Finset (Fin 10)))) = {36,40} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_46 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 0 9 {1} = x 46 + x 48 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (0 : Fin 10) ∈ cliques i ∧ (9 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 0 (insert 9 ({1} : Finset (Fin 10)))) = {46,48} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_47 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 1 9 {0} = x 47 + x 48 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (1 : Fin 10) ∈ cliques i ∧ (9 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 1 (insert 9 ({0} : Finset (Fin 10)))) = {47,48} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_48 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 3 4 ∅ = x 10 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (3 : Fin 10) ∈ cliques i ∧ (4 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 3 (insert 4 (∅ : Finset (Fin 10)))) = {10} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_49 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 3 5 ∅ = x 17 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (3 : Fin 10) ∈ cliques i ∧ (5 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 3 (insert 5 (∅ : Finset (Fin 10)))) = {17} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_50 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 2 6 ∅ = x 24 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (2 : Fin 10) ∈ cliques i ∧ (6 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 2 (insert 6 (∅ : Finset (Fin 10)))) = {24} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_51 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 2 7 ∅ = x 31 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (2 : Fin 10) ∈ cliques i ∧ (7 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 2 (insert 7 (∅ : Finset (Fin 10)))) = {31} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_52 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 2 8 {1} = x 38 + x 40 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (2 : Fin 10) ∈ cliques i ∧ (8 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 2 (insert 8 ({1} : Finset (Fin 10)))) = {38,40} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_53 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 3 8 ∅ = x 42 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (3 : Fin 10) ∈ cliques i ∧ (8 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 3 (insert 8 (∅ : Finset (Fin 10)))) = {42} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_54 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 2 9 {1} = x 49 + x 51 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (2 : Fin 10) ∈ cliques i ∧ (9 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 2 (insert 9 ({1} : Finset (Fin 10)))) = {49,51} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem tight_row_55 (x : Fin 57 → ℝ) :
    delta (FiniteMonomial.polynomial cliques x) 3 9 {0} = x 53 + x 54 := by
  rw [FiniteMonomial.delta_polynomial cliques x (by decide) (by decide) (by decide)]
  have hrow : univ.filter (fun i : Fin 57 =>
      (3 : Fin 10) ∈ cliques i ∧ (9 : Fin 10) ∈ cliques i ∧ cliques i ⊆ insert 3 (insert 9 ({0} : Finset (Fin 10)))) = {53,54} := by decide +kernel
  rw [← Finset.sum_filter,hrow]
  norm_num [Finset.sum_insert,Finset.sum_singleton] <;> ring

theorem actual_tight_kernel (f : SetFunction (Fin 10)) (hn : TranslationNormalized f)
    (hz : ∀ u v,u≠ v → ∀ S : Finset (Fin 10),u∉S → v∉S →
      delta function u v S=0 → delta f u v S=0) :
    ∃ a : ℝ,f=a • function := by
  have hG : Graphical graph f := fun u v huv hnon S hu hv =>
    hz u v huv S hu hv (graphical u v huv hnon S hu hv)
  let x : Fin 57 → ℝ := fun i => mobius f (cliques i)
  have he : f=FiniteMonomial.polynomial cliques x :=
    FiniteMonomial.graphical_eq_polynomial cliques cliques_injective cliques_complete hn hG
  have h0 : x 0 + x 3 + x 30 + x 34=0 := by
    have h := hz 0 1 (by decide) {2,7} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 1 {2,7}=0
      rw [tight_row_0]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_0] at h
    exact h
  have h1 : x 0 + x 3 + x 9 + x 30 + x 34=0 := by
    have h := hz 0 1 (by decide) {2,4,7} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 1 {2,4,7}=0
      rw [tight_row_1]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_1] at h
    exact h
  have h2 : x 0 + x 3 + x 6 + x 9 + x 13 + x 30 + x 34=0 := by
    have h := hz 0 1 (by decide) {2,3,4,7} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 1 {2,3,4,7}=0
      rw [tight_row_2]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_2] at h
    exact h
  have h3 : x 0 + x 3 + x 6 + x 9 + x 13 + x 16 + x 20 + x 30 + x 34=0 := by
    have h := hz 0 1 (by decide) {2,3,4,5,7} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 1 {2,3,4,5,7}=0
      rw [tight_row_3]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_3] at h
    exact h
  have h4 : x 0 + x 3 + x 23 + x 27 + x 30 + x 34=0 := by
    have h := hz 0 1 (by decide) {2,6,7} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 1 {2,6,7}=0
      rw [tight_row_4]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_4] at h
    exact h
  have h5 : x 0 + x 6 + x 9 + x 13 + x 37 + x 45=0 := by
    have h := hz 0 1 (by decide) {3,4,8} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 1 {3,4,8}=0
      rw [tight_row_5]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_5] at h
    exact h
  have h6 : x 0 + x 6 + x 9 + x 13 + x 30 + x 37 + x 45=0 := by
    have h := hz 0 1 (by decide) {3,4,7,8} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 1 {3,4,7,8}=0
      rw [tight_row_6]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_6] at h
    exact h
  have h7 : x 0 + x 3 + x 6 + x 9 + x 13 + x 30 + x 34 + x 37 + x 41 + x 45=0 := by
    have h := hz 0 1 (by decide) {2,3,4,7,8} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 1 {2,3,4,7,8}=0
      rw [tight_row_7]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_7] at h
    exact h
  have h8 : x 0 + x 48=0 := by
    have h := hz 0 1 (by decide) {9} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 1 {9}=0
      rw [tight_row_8]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_8] at h
    exact h
  have h9 : x 0 + x 3 + x 30 + x 34 + x 48 + x 52=0 := by
    have h := hz 0 1 (by decide) {2,7,9} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 1 {2,7,9}=0
      rw [tight_row_9]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_9] at h
    exact h
  have h10 : x 0 + x 37 + x 48=0 := by
    have h := hz 0 1 (by decide) {8,9} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 1 {8,9}=0
      rw [tight_row_10]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_10] at h
    exact h
  have h11 : x 0 + x 6 + x 9 + x 13 + x 37 + x 45 + x 48 + x 56=0 := by
    have h := hz 0 1 (by decide) {3,4,8,9} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 1 {3,4,8,9}=0
      rw [tight_row_11]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_11] at h
    exact h
  have h12 : x 1=0 := by
    have h := hz 0 2 (by decide) ∅ (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 2 ∅=0
      rw [tight_row_12]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_12] at h
    exact h
  have h13 : x 1 + x 3=0 := by
    have h := hz 0 2 (by decide) {1} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 2 {1}=0
      rw [tight_row_13]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_13] at h
    exact h
  have h14 : x 1 + x 3 + x 25 + x 27=0 := by
    have h := hz 0 2 (by decide) {1,6} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 2 {1,6}=0
      rw [tight_row_14]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_14] at h
    exact h
  have h15 : x 1 + x 3 + x 32 + x 34=0 := by
    have h := hz 0 2 (by decide) {1,7} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 2 {1,7}=0
      rw [tight_row_15]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_15] at h
    exact h
  have h16 : x 1 + x 39=0 := by
    have h := hz 0 2 (by decide) {8} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 2 {8}=0
      rw [tight_row_16]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_16] at h
    exact h
  have h17 : x 1 + x 50=0 := by
    have h := hz 0 2 (by decide) {9} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 2 {9}=0
      rw [tight_row_17]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_17] at h
    exact h
  have h18 : x 2 + x 3 + x 26 + x 27 + x 33 + x 34=0 := by
    have h := hz 1 2 (by decide) {0,6,7} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 2 {0,6,7}=0
      rw [tight_row_18]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_18] at h
    exact h
  have h19 : x 2 + x 3 + x 26 + x 27 + x 33 + x 34 + x 40 + x 41=0 := by
    have h := hz 1 2 (by decide) {0,6,7,8} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 2 {0,6,7,8}=0
      rw [tight_row_19]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_19] at h
    exact h
  have h20 : x 2 + x 3 + x 26 + x 27 + x 33 + x 34 + x 51 + x 52=0 := by
    have h := hz 1 2 (by decide) {0,6,7,9} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 2 {0,6,7,9}=0
      rw [tight_row_20]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_20] at h
    exact h
  have h21 : x 2 + x 40 + x 51=0 := by
    have h := hz 1 2 (by decide) {8,9} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 2 {8,9}=0
      rw [tight_row_21]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_21] at h
    exact h
  have h22 : x 2 + x 26 + x 40 + x 51=0 := by
    have h := hz 1 2 (by decide) {6,8,9} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 2 {6,8,9}=0
      rw [tight_row_22]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_22] at h
    exact h
  have h23 : x 2 + x 33 + x 40 + x 51=0 := by
    have h := hz 1 2 (by decide) {7,8,9} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 2 {7,8,9}=0
      rw [tight_row_23]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_23] at h
    exact h
  have h24 : x 4 + x 6 + x 18 + x 20=0 := by
    have h := hz 0 3 (by decide) {1,5} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 3 {1,5}=0
      rw [tight_row_24]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_24] at h
    exact h
  have h25 : x 4 + x 6 + x 11 + x 13 + x 18 + x 20=0 := by
    have h := hz 0 3 (by decide) {1,4,5} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 3 {1,4,5}=0
      rw [tight_row_25]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_25] at h
    exact h
  have h26 : x 4 + x 6 + x 18 + x 20 + x 43 + x 45=0 := by
    have h := hz 0 3 (by decide) {1,5,8} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 3 {1,5,8}=0
      rw [tight_row_26]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_26] at h
    exact h
  have h27 : x 4 + x 54=0 := by
    have h := hz 0 3 (by decide) {9} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 3 {9}=0
      rw [tight_row_27]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_27] at h
    exact h
  have h28 : x 4 + x 18 + x 54=0 := by
    have h := hz 0 3 (by decide) {5,9} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 3 {5,9}=0
      rw [tight_row_28]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_28] at h
    exact h
  have h29 : x 4 + x 6 + x 18 + x 20 + x 54 + x 56=0 := by
    have h := hz 0 3 (by decide) {1,5,9} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 3 {1,5,9}=0
      rw [tight_row_29]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_29] at h
    exact h
  have h30 : x 5=0 := by
    have h := hz 1 3 (by decide) ∅ (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 3 ∅=0
      rw [tight_row_30]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_30] at h
    exact h
  have h31 : x 5 + x 44=0 := by
    have h := hz 1 3 (by decide) {8} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 3 {8}=0
      rw [tight_row_31]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_31] at h
    exact h
  have h32 : x 5 + x 6 + x 44 + x 45=0 := by
    have h := hz 1 3 (by decide) {0,8} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 3 {0,8}=0
      rw [tight_row_32]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_32] at h
    exact h
  have h33 : x 5 + x 6 + x 12 + x 13 + x 44 + x 45=0 := by
    have h := hz 1 3 (by decide) {0,4,8} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 3 {0,4,8}=0
      rw [tight_row_33]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_33] at h
    exact h
  have h34 : x 5 + x 6 + x 19 + x 20 + x 44 + x 45=0 := by
    have h := hz 1 3 (by decide) {0,5,8} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 3 {0,5,8}=0
      rw [tight_row_34]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_34] at h
    exact h
  have h35 : x 5 + x 55=0 := by
    have h := hz 1 3 (by decide) {9} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 3 {9}=0
      rw [tight_row_35]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_35] at h
    exact h
  have h36 : x 7=0 := by
    have h := hz 0 4 (by decide) ∅ (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 4 ∅=0
      rw [tight_row_36]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_36] at h
    exact h
  have h37 : x 8=0 := by
    have h := hz 1 4 (by decide) ∅ (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 4 ∅=0
      rw [tight_row_37]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_37] at h
    exact h
  have h38 : x 14=0 := by
    have h := hz 0 5 (by decide) ∅ (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 5 ∅=0
      rw [tight_row_38]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_38] at h
    exact h
  have h39 : x 15=0 := by
    have h := hz 1 5 (by decide) ∅ (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 5 ∅=0
      rw [tight_row_39]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_39] at h
    exact h
  have h40 : x 21=0 := by
    have h := hz 0 6 (by decide) ∅ (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 6 ∅=0
      rw [tight_row_40]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_40] at h
    exact h
  have h41 : x 22=0 := by
    have h := hz 1 6 (by decide) ∅ (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 6 ∅=0
      rw [tight_row_41]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_41] at h
    exact h
  have h42 : x 28=0 := by
    have h := hz 0 7 (by decide) ∅ (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 7 ∅=0
      rw [tight_row_42]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_42] at h
    exact h
  have h43 : x 29 + x 30 + x 33 + x 34=0 := by
    have h := hz 1 7 (by decide) {0,2} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 7 {0,2}=0
      rw [tight_row_43]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_43] at h
    exact h
  have h44 : x 35=0 := by
    have h := hz 0 8 (by decide) ∅ (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 8 ∅=0
      rw [tight_row_44]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_44] at h
    exact h
  have h45 : x 36 + x 40=0 := by
    have h := hz 1 8 (by decide) {2} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 8 {2}=0
      rw [tight_row_45]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_45] at h
    exact h
  have h46 : x 46 + x 48=0 := by
    have h := hz 0 9 (by decide) {1} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 0 9 {1}=0
      rw [tight_row_46]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_46] at h
    exact h
  have h47 : x 47 + x 48=0 := by
    have h := hz 1 9 (by decide) {0} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 1 9 {0}=0
      rw [tight_row_47]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_47] at h
    exact h
  have h48 : x 10=0 := by
    have h := hz 3 4 (by decide) ∅ (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 3 4 ∅=0
      rw [tight_row_48]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_48] at h
    exact h
  have h49 : x 17=0 := by
    have h := hz 3 5 (by decide) ∅ (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 3 5 ∅=0
      rw [tight_row_49]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_49] at h
    exact h
  have h50 : x 24=0 := by
    have h := hz 2 6 (by decide) ∅ (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 2 6 ∅=0
      rw [tight_row_50]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_50] at h
    exact h
  have h51 : x 31=0 := by
    have h := hz 2 7 (by decide) ∅ (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 2 7 ∅=0
      rw [tight_row_51]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_51] at h
    exact h
  have h52 : x 38 + x 40=0 := by
    have h := hz 2 8 (by decide) {1} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 2 8 {1}=0
      rw [tight_row_52]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_52] at h
    exact h
  have h53 : x 42=0 := by
    have h := hz 3 8 (by decide) ∅ (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 3 8 ∅=0
      rw [tight_row_53]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_53] at h
    exact h
  have h54 : x 49 + x 51=0 := by
    have h := hz 2 9 (by decide) {1} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 2 9 {1}=0
      rw [tight_row_54]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_54] at h
    exact h
  have h55 : x 53 + x 54=0 := by
    have h := hz 3 9 (by decide) {0} (by decide) (by decide) (by
      change delta (FiniteMonomial.polynomial cliques DiamondGenerated.coefficients) 3 9 {0}=0
      rw [tight_row_55]
      norm_num [DiamondGenerated.coefficients])
    rw [he,tight_row_55] at h
    exact h
  have hx := DiamondGenerated.kernel_line x h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40 h41 h42 h43 h44 h45 h46 h47 h48 h49 h50 h51 h52 h53 h54 h55
  refine ⟨x 0,?_⟩
  have hs : x=(x 0) • DiamondGenerated.coefficients := by
    funext i
    simpa only [Pi.smul_apply,smul_eq_mul,mul_comm] using hx i
  calc
    f=FiniteMonomial.polynomial cliques x := he
    _=FiniteMonomial.polynomial cliques ((x 0) • DiamondGenerated.coefficients) :=
      congrArg (FiniteMonomial.polynomial cliques) hs
    _=(x 0) • function :=
      FiniteMonomial.polynomial_smul cliques DiamondGenerated.coefficients (x 0)

theorem function_ne_zero : function≠0 := by
  intro h
  have he:=congrFun h ({0,1} : Finset (Fin 10))
  norm_num [function,FiniteMonomial.polynomial,cliques,DiamondGenerated.coefficients,
    Fin.sum_univ_succ,setMonomial,Finset.subset_iff] at he

theorem extreme : ExtremeSupermodular function :=
  extremeSupermodular_of_tightEquations normalized supermodular function_ne_zero actual_tight_kernel

theorem lattice : LatticePolytope (basePolytope function) :=
  integerValued.basePolytope normalized.1 supermodular

theorem indecomposable : MinkowskiIndecomposable (basePolytope function) :=
  extreme.minkowskiIndecomposable


def orientedEdges : Fin 25 → Fin 10 × Fin 10 :=
  ![(0,1), (0,2), (1,2), (0,3), (1,3), (0,4), (1,4), (0,5), (1,5), (0,6), (1,6), (0,7), (1,7), (0,8), (1,8), (0,9), (1,9), (3,4), (3,5), (2,6), (2,7), (2,8), (3,8), (2,9), (3,9)]

def positiveContexts : Fin 25 → Finset (Fin 10) :=
  ![∅, {6}, ∅, ∅, {0}, {3}, {3}, {1}, {0}, {1}, {0}, {2}, ∅, {1,2}, ∅, ∅, ∅, {0}, {1}, {0}, {0}, ∅, {0}, ∅, ∅]

theorem oriented_edges_complete : ∀ u v : Fin 10,u< v → graph.Adj u v →
    ∃ i,orientedEdges i=(u,v) := by decide +kernel

theorem positive_contexts_certificate : ∀ i : Fin 25,
    (orientedEdges i).1∉positiveContexts i ∧
    (orientedEdges i).2∉positiveContexts i ∧
    0< slackZ (orientedEdges i).1 (orientedEdges i).2 (positiveContexts i) := by decide +kernel

theorem positive_slack {u v : Fin 10} (he : graph.Adj u v) :
    ∃ S : Finset (Fin 10),u∉S ∧ v∉S ∧ 0< delta function u v S := by
  have ordered : ∀ u v : Fin 10,u< v → graph.Adj u v →
      ∃ S : Finset (Fin 10),u∉S ∧ v∉S ∧ 0< delta function u v S := by
    intro a b hab he
    obtain ⟨i,hi⟩:=oriented_edges_complete a b hab he
    have hc:=positive_contexts_certificate i
    rw [hi] at hc
    refine ⟨positiveContexts i,hc.1,hc.2.1,?_⟩
    rw [delta_eq_slackZ (ne_of_lt hab) hc.1 hc.2.1]
    exact_mod_cast hc.2.2
  rcases lt_or_gt_of_ne (graph.ne_of_adj he) with hlt | hgt
  · exact ordered u v hlt he
  · obtain ⟨S,hv,hu,hs⟩:=ordered v u hgt (graph.adj_symm he)
    exact ⟨S,hu,hv,by rw [delta_comm u v]; exact hs⟩

theorem graph_connected : graph.Connected := by
  apply graph.connected_iff_exists_forall_reachable.mpr
  refine ⟨0,fun v => ?_⟩
  by_cases hv : v=0
  · subst v
    exact SimpleGraph.Reachable.refl _
  · have ha : ∀ w : Fin 10,w≠0 → graph.Adj 0 w := by decide +kernel
    exact (ha v hv).reachable

theorem full_dimension : FullDimension (basePolytope function) := by
  exact finrank_vectorSpan_eq_of_connected_slacks normalized.1 supermodular graph_connected
    (fun _ _ he => by
      obtain ⟨S,hu,hv,hd⟩:=positive_slack he
      exact ⟨S,hu,hv,ne_of_gt hd⟩)

theorem actual_direction_graph : actualDirectionGraph (basePolytope function)=graph := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  constructor
  · intro h
    obtain ⟨R,hR,hRc,hnR,hsum⟩:=actual_summand
    exact basePolytope_summand_actualRootEdge normalized.1 supermodular graph
      (by norm_num : (0 : ℝ)≤4) R hsum h
  · intro he
    obtain ⟨S,hu,hv,hd⟩:=positive_slack he
    exact exposedSegment_of_positive_delta normalized.1 supermodular (graph.ne_of_adj he) hu hv hd

theorem edge_family_eq : edgeFamily graph=edges := by
  ext C
  by_cases hc : C.card=2
  · obtain ⟨u,v,huv,rfl⟩:=card_eq_two.mp hc
    rw [pair_mem_edgeFamily graph huv]
    change (u≠ v ∧ ({u,v} : Finset (Fin 10))∈edges) ↔ _
    exact ⟨fun h => h.2,fun h => ⟨huv,h⟩⟩
  · have hnot : C∉edgeFamily graph := fun h => hc ((mem_edgeFamily graph C).mp h).1
    have hcard : ∀ D∈edges,D.card=2 := by decide +kernel
    have hnot' : C∉edges := fun h => hc (hcard C h)
    simp only [hnot,hnot']

theorem direction_count : directionCount (basePolytope function)=25 := by
  rw [directionCount,actual_direction_graph,edge_family_eq]
  decide

/-- The actual ten-vertex diamond polytope, with its full real tight kernel,
integer lattice, genuine Minkowski complement, full dimension, and exactly
25 actual exposed-edge directions. This is the finite witness used in8.1;
the unbounded classification is a separate theorem. -/
theorem diamond_polytope : LatticePolytope (basePolytope function) ∧
    MinkowskiIndecomposable (basePolytope function) ∧
    FullDimension (basePolytope function) ∧
    IsMinkowskiSummand (basePolytope function) ((4 : ℝ) • graphicalZonotope graph) ∧
    directionCount (basePolytope function)=25 :=
  ⟨lattice,indecomposable,full_dimension,actual_summand,direction_count⟩

end GraphicalZonotopes.DiamondGeometry

end
end
end BundlePart31

section BundlePart32
/- Source: Papers/GraphicalZonotopes/FiniteTightCertificates.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace FiniteTight
open Finset
open scoped BigOperators Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A row is either an actual value coordinate or an actual elemental
difference. It cannot contain an arbitrary unverified linear assertion. -/
inductive Row (V : Type*) where
  | value (S : Finset V)
  | elemental (u v : V) (S : Finset V)
  deriving DecidableEq

def Row.coefficient (r : Row V) (C : Finset V) : ℚ :=
  match r with
  | .value S => if C=S then 1 else 0
  | .elemental u v S =>
      (if C=insert u (insert v S) then 1 else 0)-
      (if C=insert u S then 1 else 0)-
      (if C=insert v S then 1 else 0)+(if C=S then 1 else 0)

def Row.eval (r : Row V) (f : SetFunction V) : ℝ :=
  match r with
  | .value S => f S
  | .elemental u v S => delta f u v S

def integerDelta (z : Finset V → ℤ) (u v : V) (S : Finset V) : ℤ :=
  z (insert u (insert v S))-z (insert u S)-z (insert v S)+z S

def realFunction (z : Finset V → ℤ) : SetFunction V := fun S => (z S : ℝ)

theorem delta_realFunction (z : Finset V → ℤ) (u v : V) (S : Finset V) :
    delta (realFunction z) u v S=(integerDelta z u v S : ℝ) := by
  simp only [delta,realFunction,integerDelta,Int.cast_sub,Int.cast_add]

theorem Row.eval_eq_sum (r : Row V) (f : SetFunction V) :
    r.eval f=∑ C : Finset V,(r.coefficient C : ℝ)*f C := by
  cases r with
  | value S => simp [Row.eval,Row.coefficient,apply_ite,ite_mul]
  | elemental u v S =>
    have hcast (p : Prop) [Decidable p] :
        ((↑(if p then (1 : ℚ) else 0)) : ℝ) = if p then 1 else 0 := by
      split_ifs <;> norm_num
    simp only [Row.eval,Row.coefficient,delta,Rat.cast_add,Rat.cast_sub,hcast,
      sub_mul,add_mul,sum_sub_distrib,sum_add_distrib,ite_mul,one_mul,zero_mul]
    simp <;> ring

@[simp] theorem Row.eval_sub (r : Row V) (f g : SetFunction V) :
    r.eval (f-g)=r.eval f-r.eval g := by cases r <;> simp [Row.eval]

@[simp] theorem Row.eval_smul (r : Row V) (c : ℝ) (f : SetFunction V) :
    r.eval (c • f)=c*r.eval f := by cases r <;> simp [Row.eval]

/-- Each nonpivot certificate row is justified by translation normalization
or by one of the literal tight elemental equations of the proposed function. -/
def Row.valid (z : Finset V → ℤ) (r : Row V) : Prop :=
  match r with
  | .value S => S=∅ ∨ ∃ v : V,S={v}
  | .elemental u v S => u≠ v ∧ u∉S ∧ v∉S ∧ integerDelta z u v S=0

instance (z : Finset V → ℤ) (r : Row V) : Decidable (r.valid z) := by
  cases r <;> unfold Row.valid <;> infer_instance

theorem Row.eval_zero_of_valid {z : Finset V → ℤ} {r : Row V}
    (hr : r.valid z) (f : SetFunction V) (hfn : TranslationNormalized f)
    (hzero : ∀ u v,u≠ v → ∀ S : Finset V,u∉S → v∉S →
      delta (realFunction z) u v S=0 → delta f u v S=0) : r.eval f=0 := by
  cases r with
  | value S =>
    rcases hr with rfl | ⟨v,rfl⟩
    · exact hfn.1
    · exact hfn.2 v
  | elemental u v S =>
    exact hzero u v hr.1 S hr.2.1 hr.2.2.1 (by
      rw [delta_realFunction,hr.2.2.2]
      norm_num)

theorem realFunction_normalized {z : Finset V → ℤ}
    (h0 : z ∅=0) (h1 : ∀ v,z {v}=0) : TranslationNormalized (realFunction z) := by
  exact ⟨by simp [Normalized,realFunction,h0],fun v => by simp [realFunction,h1 v]⟩

theorem realFunction_supermodular {z : Finset V → ℤ}
    (hz : ∀ u v,u≠ v → ∀ S : Finset V,u∉S → v∉S →
      integerDelta z u v S=0 ∨ integerDelta z u v S=1) : Supermodular (realFunction z) := by
  apply ElementallyNonnegative.supermodular
  intro u v huv S hu hv
  rw [delta_realFunction]
  rcases hz u v huv S hu hv with he | he <;> rw [he] <;> norm_num

theorem realFunction_integerValued (z : Finset V → ℤ) : IntegerValued (realFunction z) :=
  fun S => ⟨z S,rfl⟩

theorem pair_sum_of_integer_differences (G : SimpleGraph V) [DecidableRel G.Adj]
    (z w : Finset V → ℤ) (hz0 : z ∅=0) (hz1 : ∀ v,z {v}=0)
    (hw0 : w ∅=0) (hw1 : ∀ v,w {v}=0)
    (hdelta : ∀ u v,u≠ v → ∀ S : Finset V,u∉S → v∉S →
      integerDelta z u v S+integerDelta w u v S=if G.Adj u v then 1 else 0) :
    realFunction z+realFunction w=graphFunction G := by
  have hzn := realFunction_normalized hz0 hz1
  have hwn := realFunction_normalized hw0 hw1
  have hgn := graphFunction_translationNormalized G
  apply sub_eq_zero.mp
  apply normalized_zero_elemental_eq_zero
  · refine ⟨?_,?_⟩
    · change realFunction z ∅+realFunction w ∅-graphFunction G ∅=0
      rw [hzn.1,hwn.1,hgn.1]
      ring
    · intro v
      change realFunction z {v}+realFunction w {v}-graphFunction G {v}=0
      rw [hzn.2 v,hwn.2 v,hgn.2 v]
      ring
  · intro u v huv S hu hv
    rw [delta_sub,delta_add,delta_realFunction,delta_realFunction,
      graphFunction_delta G huv hu hv]
    have h : (integerDelta z u v S : ℝ)+(integerDelta w u v S : ℝ)=
        if G.Adj u v then 1 else 0 := by exact_mod_cast hdelta u v huv S hu hv
    by_cases he : G.Adj u v
    · simpa only [if_pos he] using sub_eq_zero.mpr h
    · simpa only [if_neg he] using sub_eq_zero.mpr h

def matrix {k : ℕ} (rows : Fin (k+1) → Row V) : Matrix (Fin (k+1)) (Finset V) ℚ :=
  fun i C => (rows i).coefficient C

/-- An exact rational left inverse proves the full real tight kernel is a
line. The certificate entries are checked identities; all variables of the
kernel theorem remain arbitrary real set functions. -/
theorem tight_kernel_of_left_inverse {k : ℕ} (z : Finset V → ℤ)
    (rows : Fin (k+1) → Row V) (B : Matrix (Finset V) (Fin (k+1)) ℚ)
    (pivot : Finset V) (hpivot : z pivot=1) (hrow0 : rows 0=.value pivot)
    (hvalid : ∀ i : Fin (k+1),i≠0 → (rows i).valid z)
    (hinverse : B*matrix rows=1) (hn : TranslationNormalized (realFunction z))
    (f : SetFunction V) (hfn : TranslationNormalized f)
    (hzero : ∀ u v,u≠ v → ∀ S : Finset V,u∉S → v∉S →
      delta (realFunction z) u v S=0 → delta f u v S=0) :
    ∃ t : ℝ,f=t • realFunction z := by
  let A' : Matrix (Fin (k+1)) (Finset V) ℝ := fun i C => (matrix rows i C : ℝ)
  let B' : Matrix (Finset V) (Fin (k+1)) ℝ := fun C i => (B C i : ℝ)
  have hBA : B'*A'=1 := by
    ext C D
    have h : (∑ i : Fin (k+1),B C i*matrix rows i D)=if C=D then 1 else 0 := by
      simpa only [Matrix.mul_apply,Matrix.one_apply] using congrFun (congrFun hinverse C) D
    have hc := congrArg (fun q : ℚ => (q : ℝ)) h
    simp only [Rat.cast_sum, Rat.cast_mul, apply_ite, Rat.cast_one, Rat.cast_zero] at hc
    change (∑ i : Fin (k+1),(B C i : ℝ)*(matrix rows i D : ℝ)) = if C=D then 1 else 0
    by_cases he : C=D
    · simpa only [if_pos he] using hc
    · simpa only [if_neg he] using hc

  let w : SetFunction V := f-f pivot • realFunction z
  have hw : A' *ᵥ w=0 := by
    funext i
    change (∑ C : Finset V,(matrix rows i C : ℝ)*w C)=0
    rw [show (∑ C : Finset V,(matrix rows i C : ℝ)*w C)=(rows i).eval w from
      (Row.eval_eq_sum (rows i) w).symm]
    by_cases hi : i=0
    · subst i
      rw [hrow0]
      change f pivot-f pivot*(z pivot : ℝ)=0
      rw [hpivot]
      norm_num
    · rw [show w=f-f pivot • realFunction z from rfl,Row.eval_sub,Row.eval_smul,
        Row.eval_zero_of_valid (hvalid i hi) f hfn hzero,
        Row.eval_zero_of_valid (hvalid i hi) (realFunction z) hn
          (fun _ _ _ _ _ _ he => he)]
      ring
  have h := congrArg (fun v => B' *ᵥ v) hw
  rw [Matrix.mulVec_mulVec,hBA,Matrix.one_mulVec,Matrix.mulVec_zero] at h
  exact ⟨f pivot,sub_eq_zero.mp h⟩

theorem extreme_of_left_inverse {k : ℕ} (z : Finset V → ℤ)
    (rows : Fin (k+1) → Row V) (B : Matrix (Finset V) (Fin (k+1)) ℚ)
    (pivot : Finset V) (hpivot : z pivot=1) (hrow0 : rows 0=.value pivot)
    (hvalid : ∀ i : Fin (k+1),i≠0 → (rows i).valid z)
    (hinverse : B*matrix rows=1) (h0 : z ∅=0) (h1 : ∀ v,z {v}=0)
    (hbool : ∀ u v,u≠ v → ∀ S : Finset V,u∉S → v∉S →
      integerDelta z u v S=0 ∨ integerDelta z u v S=1) :
    ExtremeSupermodular (realFunction z) := by
  have hn := realFunction_normalized h0 h1
  apply extremeSupermodular_of_tightEquations hn (realFunction_supermodular hbool)
  · intro he
    have h := congrFun he pivot
    simp [realFunction,hpivot] at h
  · exact tight_kernel_of_left_inverse z rows B pivot hpivot hrow0 hvalid hinverse hn


/-- A checked real kernel certificate for the literal normalized/tight rows
is sufficient; no matrix computation or floating-point rank oracle is used. -/
theorem tight_kernel_of_row_kernel {k : ℕ} (z : Finset V → ℤ)
    (rows : Fin (k+1) → Row V) (pivot : Finset V)
    (hpivot : z pivot=1) (hrow0 : rows 0=.value pivot)
    (hvalid : ∀ i : Fin (k+1),i≠0 → (rows i).valid z)
    (hkernel : ∀ w : SetFunction V,(∀ i,(rows i).eval w=0) → w=0)
    (hn : TranslationNormalized (realFunction z))
    (f : SetFunction V) (hfn : TranslationNormalized f)
    (hzero : ∀ u v,u≠ v → ∀ S : Finset V,u∉S → v∉S →
      delta (realFunction z) u v S=0 → delta f u v S=0) :
    ∃ t : ℝ,f=t • realFunction z := by
  let w : SetFunction V := f-f pivot • realFunction z
  have hw : ∀ i,(rows i).eval w=0 := by
    intro i
    by_cases hi : i=0
    · subst i
      rw [hrow0]
      change f pivot-f pivot*(z pivot : ℝ)=0
      rw [hpivot]
      norm_num
    · rw [show w=f-f pivot • realFunction z from rfl,Row.eval_sub,Row.eval_smul,
        Row.eval_zero_of_valid (hvalid i hi) f hfn hzero,
        Row.eval_zero_of_valid (hvalid i hi) (realFunction z) hn
          (fun _ _ _ _ _ _ he => he)]
      ring
  exact ⟨f pivot,sub_eq_zero.mp (hkernel w hw)⟩

theorem extreme_of_row_kernel {k : ℕ} (z : Finset V → ℤ)
    (rows : Fin (k+1) → Row V) (pivot : Finset V)
    (hpivot : z pivot=1) (hrow0 : rows 0=.value pivot)
    (hvalid : ∀ i : Fin (k+1),i≠0 → (rows i).valid z)
    (hkernel : ∀ w : SetFunction V,(∀ i,(rows i).eval w=0) → w=0)
    (h0 : z ∅=0) (h1 : ∀ v,z {v}=0)
    (hbool : ∀ u v,u≠ v → ∀ S : Finset V,u∉S → v∉S →
      integerDelta z u v S=0 ∨ integerDelta z u v S=1) :
    ExtremeSupermodular (realFunction z) := by
  have hn := realFunction_normalized h0 h1
  apply extremeSupermodular_of_tightEquations hn (realFunction_supermodular hbool)
  · intro he
    have h := congrFun he pivot
    simp [realFunction,hpivot] at h
  · exact tight_kernel_of_row_kernel z rows pivot hpivot hrow0 hvalid hkernel hn

end FiniteTight
end GraphicalZonotopes

end
end
end BundlePart32

section BundlePart33
/- Source: Papers/GraphicalZonotopes/SmallBooleanCertificates.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace SmallBoolean
open Finset FiniteTight
open scoped BigOperators Matrix

/-- Binary encoding of an actual finite subset; only used to read exact integer certificates. -/
def subsetMask {n : ℕ} (S : Finset (Fin n)) : ℕ := ∑ i∈S,2^i.val

namespace K4

def integerFunction (S : Finset (Fin 4)) : ℤ :=
  (match subsetMask S with
  | 3 => 1
  | 7 => 1
  | 11 => 1
  | 13 => 1
  | 14 => 1
  | 15 => 2
  | _ => 0)

def rows : Fin 16 → Row (Fin 4) :=
  ![.value {0,1},.value ∅,.value {0},.value {1},.value {2},.value {3},.elemental 0 1 {2,3},.elemental 0 2 ∅,.elemental 0 2 {1},.elemental 0 2 {1,3},.elemental 0 3 ∅,.elemental 0 3 {1},.elemental 1 2 ∅,.elemental 1 2 {0,3},.elemental 1 3 ∅,.elemental 2 3 ∅]

def pivot : Finset (Fin 4) := {0,1}

theorem pivot_one : integerFunction pivot=1 := by decide

theorem row_zero : rows 0=.value pivot := by decide

theorem valid_rows : ∀ i : Fin 16,i≠0 → (rows i).valid integerFunction := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 4096 in
theorem row_kernel_zero (f : SetFunction (Fin 4))
    (hf : ∀ i : Fin 16,(rows i).eval f=0) : f=0 := by
  have h0 : f {0,1}=0 := hf 0
  have h1 : f ∅=0 := hf 1
  have h2 : f {0}=0 := hf 2
  have h3 : f {1}=0 := hf 3
  have h4 : f {2}=0 := hf 4
  have h5 : f {3}=0 := hf 5
  have h6 : f {0,1,2,3}-f {0,2,3}-f {1,2,3}+f {2,3}=0 := by
    have h := hf 6
    change f (insert 0 (insert 1 ({2,3} : Finset (Fin 4))))-
      f (insert 0 ({2,3} : Finset (Fin 4)))-f (insert 1 ({2,3} : Finset (Fin 4)))+f {2,3}=0 at h
    have hAB : insert 0 (insert 1 ({2,3} : Finset (Fin 4)))={0,1,2,3} := by decide
    have hA : insert 0 ({2,3} : Finset (Fin 4))={0,2,3} := by decide
    have hB : insert 1 ({2,3} : Finset (Fin 4))={1,2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h7 : f {0,2}-f {0}-f {2}+f ∅=0 := by
    have h := hf 7
    change f (insert 0 (insert 2 (∅ : Finset (Fin 4))))-
      f (insert 0 (∅ : Finset (Fin 4)))-f (insert 2 (∅ : Finset (Fin 4)))+f ∅=0 at h
    have hAB : insert 0 (insert 2 (∅ : Finset (Fin 4)))={0,2} := by decide
    have hA : insert 0 (∅ : Finset (Fin 4))={0} := by decide
    have hB : insert 2 (∅ : Finset (Fin 4))={2} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h8 : f {0,1,2}-f {0,1}-f {1,2}+f {1}=0 := by
    have h := hf 8
    change f (insert 0 (insert 2 ({1} : Finset (Fin 4))))-
      f (insert 0 ({1} : Finset (Fin 4)))-f (insert 2 ({1} : Finset (Fin 4)))+f {1}=0 at h
    have hAB : insert 0 (insert 2 ({1} : Finset (Fin 4)))={0,1,2} := by decide
    have hA : insert 0 ({1} : Finset (Fin 4))={0,1} := by decide
    have hB : insert 2 ({1} : Finset (Fin 4))={1,2} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h9 : f {0,1,2,3}-f {0,1,3}-f {1,2,3}+f {1,3}=0 := by
    have h := hf 9
    change f (insert 0 (insert 2 ({1,3} : Finset (Fin 4))))-
      f (insert 0 ({1,3} : Finset (Fin 4)))-f (insert 2 ({1,3} : Finset (Fin 4)))+f {1,3}=0 at h
    have hAB : insert 0 (insert 2 ({1,3} : Finset (Fin 4)))={0,1,2,3} := by decide
    have hA : insert 0 ({1,3} : Finset (Fin 4))={0,1,3} := by decide
    have hB : insert 2 ({1,3} : Finset (Fin 4))={1,2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h10 : f {0,3}-f {0}-f {3}+f ∅=0 := by
    have h := hf 10
    change f (insert 0 (insert 3 (∅ : Finset (Fin 4))))-
      f (insert 0 (∅ : Finset (Fin 4)))-f (insert 3 (∅ : Finset (Fin 4)))+f ∅=0 at h
    have hAB : insert 0 (insert 3 (∅ : Finset (Fin 4)))={0,3} := by decide
    have hA : insert 0 (∅ : Finset (Fin 4))={0} := by decide
    have hB : insert 3 (∅ : Finset (Fin 4))={3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h11 : f {0,1,3}-f {0,1}-f {1,3}+f {1}=0 := by
    have h := hf 11
    change f (insert 0 (insert 3 ({1} : Finset (Fin 4))))-
      f (insert 0 ({1} : Finset (Fin 4)))-f (insert 3 ({1} : Finset (Fin 4)))+f {1}=0 at h
    have hAB : insert 0 (insert 3 ({1} : Finset (Fin 4)))={0,1,3} := by decide
    have hA : insert 0 ({1} : Finset (Fin 4))={0,1} := by decide
    have hB : insert 3 ({1} : Finset (Fin 4))={1,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h12 : f {1,2}-f {1}-f {2}+f ∅=0 := by
    have h := hf 12
    change f (insert 1 (insert 2 (∅ : Finset (Fin 4))))-
      f (insert 1 (∅ : Finset (Fin 4)))-f (insert 2 (∅ : Finset (Fin 4)))+f ∅=0 at h
    have hAB : insert 1 (insert 2 (∅ : Finset (Fin 4)))={1,2} := by decide
    have hA : insert 1 (∅ : Finset (Fin 4))={1} := by decide
    have hB : insert 2 (∅ : Finset (Fin 4))={2} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h13 : f {0,1,2,3}-f {0,1,3}-f {0,2,3}+f {0,3}=0 := by
    have h := hf 13
    change f (insert 1 (insert 2 ({0,3} : Finset (Fin 4))))-
      f (insert 1 ({0,3} : Finset (Fin 4)))-f (insert 2 ({0,3} : Finset (Fin 4)))+f {0,3}=0 at h
    have hAB : insert 1 (insert 2 ({0,3} : Finset (Fin 4)))={0,1,2,3} := by decide
    have hA : insert 1 ({0,3} : Finset (Fin 4))={0,1,3} := by decide
    have hB : insert 2 ({0,3} : Finset (Fin 4))={0,2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h14 : f {1,3}-f {1}-f {3}+f ∅=0 := by
    have h := hf 14
    change f (insert 1 (insert 3 (∅ : Finset (Fin 4))))-
      f (insert 1 (∅ : Finset (Fin 4)))-f (insert 3 (∅ : Finset (Fin 4)))+f ∅=0 at h
    have hAB : insert 1 (insert 3 (∅ : Finset (Fin 4)))={1,3} := by decide
    have hA : insert 1 (∅ : Finset (Fin 4))={1} := by decide
    have hB : insert 3 (∅ : Finset (Fin 4))={3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h15 : f {2,3}-f {2}-f {3}+f ∅=0 := by
    have h := hf 15
    change f (insert 2 (insert 3 (∅ : Finset (Fin 4))))-
      f (insert 2 (∅ : Finset (Fin 4)))-f (insert 3 (∅ : Finset (Fin 4)))+f ∅=0 at h
    have hAB : insert 2 (insert 3 (∅ : Finset (Fin 4)))={2,3} := by decide
    have hA : insert 2 (∅ : Finset (Fin 4))={2} := by decide
    have hB : insert 3 (∅ : Finset (Fin 4))={3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have v0 : f ∅=0 := by
    linear_combination h1
  have v1 : f {0}=0 := by
    linear_combination h2
  have v2 : f {1}=0 := by
    linear_combination h3
  have v3 : f {0,1}=0 := by
    linear_combination h0
  have v4 : f {2}=0 := by
    linear_combination h4
  have v5 : f {0,2}=0 := by
    linear_combination (-1) * h1 + h2 + h4 + h7
  have v6 : f {1,2}=0 := by
    linear_combination (-1) * h1 + h3 + h4 + h12
  have v7 : f {0,1,2}=0 := by
    linear_combination h0 + (-1) * h1 + h4 + h8 + h12
  have v8 : f {3}=0 := by
    linear_combination h5
  have v9 : f {0,3}=0 := by
    linear_combination (-1) * h1 + h2 + h5 + h10
  have v10 : f {1,3}=0 := by
    linear_combination (-1) * h1 + h3 + h5 + h14
  have v11 : f {0,1,3}=0 := by
    linear_combination h0 + (-1) * h1 + h5 + h11 + h14
  have v12 : f {2,3}=0 := by
    linear_combination (-1) * h1 + h4 + h5 + h15
  have v13 : f {0,2,3}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h3 + h4 + h5 + (-1) * h6 + h9 + h11 + h15
  have v14 : f {1,2,3}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h2 + h4 + h5 + (-1) * h6 + (-1) * h10 + h11 + h13 + h14 + h15
  have v15 : f {0,1,2,3}=0 := by
    linear_combination (2) * h0 + (-1) * h1 + (-1) * h2 + (-1) * h3 + h4 + h5 + (-1) * h6 + h9 + (-1) * h10 + (2) * h11 + h13 + h14 + h15
  funext S
  change f S=0
  have casesS : ∀ S : Finset (Fin 4), S=∅ ∨ S={0} ∨ S={1} ∨ S={0,1} ∨ S={2} ∨ S={0,2} ∨ S={1,2} ∨ S={0,1,2} ∨ S={3} ∨ S={0,3} ∨ S={1,3} ∨ S={0,1,3} ∨ S={2,3} ∨ S={0,2,3} ∨ S={1,2,3} ∨ S={0,1,2,3} := by decide
  rcases casesS S with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem empty_zero : integerFunction ∅=0 := by decide

theorem singleton_zero : ∀ v : Fin 4,integerFunction {v}=0 := by decide

theorem boolean_differences : ∀ u v : Fin 4,u≠ v → ∀ S : Finset (Fin 4),
    u∉S → v∉S → integerDelta integerFunction u v S=0 ∨
      integerDelta integerFunction u v S=1 := by decide

theorem extreme : ExtremeSupermodular (realFunction integerFunction) :=
  extreme_of_row_kernel integerFunction rows pivot pivot_one row_zero valid_rows
    row_kernel_zero empty_zero singleton_zero boolean_differences

end K4

namespace K4Complement

def integerFunction (S : Finset (Fin 4)) : ℤ :=
  (match subsetMask S with
  | 5 => 1
  | 6 => 1
  | 7 => 2
  | 9 => 1
  | 10 => 1
  | 11 => 2
  | 12 => 1
  | 13 => 2
  | 14 => 2
  | 15 => 4
  | _ => 0)

def rows : Fin 16 → Row (Fin 4) :=
  ![.value {0,2},.value ∅,.value {0},.value {1},.value {2},.value {3},.elemental 0 1 ∅,.elemental 0 1 {2},.elemental 0 1 {3},.elemental 0 2 {3},.elemental 0 3 {2},.elemental 1 2 {3},.elemental 1 3 {2},.elemental 2 3 {0},.elemental 2 3 {1},.elemental 2 3 {0,1}]

def pivot : Finset (Fin 4) := {0,2}

theorem pivot_one : integerFunction pivot=1 := by decide

theorem row_zero : rows 0=.value pivot := by decide

theorem valid_rows : ∀ i : Fin 16,i≠0 → (rows i).valid integerFunction := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 4096 in
theorem row_kernel_zero (f : SetFunction (Fin 4))
    (hf : ∀ i : Fin 16,(rows i).eval f=0) : f=0 := by
  have h0 : f {0,2}=0 := hf 0
  have h1 : f ∅=0 := hf 1
  have h2 : f {0}=0 := hf 2
  have h3 : f {1}=0 := hf 3
  have h4 : f {2}=0 := hf 4
  have h5 : f {3}=0 := hf 5
  have h6 : f {0,1}-f {0}-f {1}+f ∅=0 := by
    have h := hf 6
    change f (insert 0 (insert 1 (∅ : Finset (Fin 4))))-
      f (insert 0 (∅ : Finset (Fin 4)))-f (insert 1 (∅ : Finset (Fin 4)))+f ∅=0 at h
    have hAB : insert 0 (insert 1 (∅ : Finset (Fin 4)))={0,1} := by decide
    have hA : insert 0 (∅ : Finset (Fin 4))={0} := by decide
    have hB : insert 1 (∅ : Finset (Fin 4))={1} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h7 : f {0,1,2}-f {0,2}-f {1,2}+f {2}=0 := by
    have h := hf 7
    change f (insert 0 (insert 1 ({2} : Finset (Fin 4))))-
      f (insert 0 ({2} : Finset (Fin 4)))-f (insert 1 ({2} : Finset (Fin 4)))+f {2}=0 at h
    have hAB : insert 0 (insert 1 ({2} : Finset (Fin 4)))={0,1,2} := by decide
    have hA : insert 0 ({2} : Finset (Fin 4))={0,2} := by decide
    have hB : insert 1 ({2} : Finset (Fin 4))={1,2} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h8 : f {0,1,3}-f {0,3}-f {1,3}+f {3}=0 := by
    have h := hf 8
    change f (insert 0 (insert 1 ({3} : Finset (Fin 4))))-
      f (insert 0 ({3} : Finset (Fin 4)))-f (insert 1 ({3} : Finset (Fin 4)))+f {3}=0 at h
    have hAB : insert 0 (insert 1 ({3} : Finset (Fin 4)))={0,1,3} := by decide
    have hA : insert 0 ({3} : Finset (Fin 4))={0,3} := by decide
    have hB : insert 1 ({3} : Finset (Fin 4))={1,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h9 : f {0,2,3}-f {0,3}-f {2,3}+f {3}=0 := by
    have h := hf 9
    change f (insert 0 (insert 2 ({3} : Finset (Fin 4))))-
      f (insert 0 ({3} : Finset (Fin 4)))-f (insert 2 ({3} : Finset (Fin 4)))+f {3}=0 at h
    have hAB : insert 0 (insert 2 ({3} : Finset (Fin 4)))={0,2,3} := by decide
    have hA : insert 0 ({3} : Finset (Fin 4))={0,3} := by decide
    have hB : insert 2 ({3} : Finset (Fin 4))={2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h10 : f {0,2,3}-f {0,2}-f {2,3}+f {2}=0 := by
    have h := hf 10
    change f (insert 0 (insert 3 ({2} : Finset (Fin 4))))-
      f (insert 0 ({2} : Finset (Fin 4)))-f (insert 3 ({2} : Finset (Fin 4)))+f {2}=0 at h
    have hAB : insert 0 (insert 3 ({2} : Finset (Fin 4)))={0,2,3} := by decide
    have hA : insert 0 ({2} : Finset (Fin 4))={0,2} := by decide
    have hB : insert 3 ({2} : Finset (Fin 4))={2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h11 : f {1,2,3}-f {1,3}-f {2,3}+f {3}=0 := by
    have h := hf 11
    change f (insert 1 (insert 2 ({3} : Finset (Fin 4))))-
      f (insert 1 ({3} : Finset (Fin 4)))-f (insert 2 ({3} : Finset (Fin 4)))+f {3}=0 at h
    have hAB : insert 1 (insert 2 ({3} : Finset (Fin 4)))={1,2,3} := by decide
    have hA : insert 1 ({3} : Finset (Fin 4))={1,3} := by decide
    have hB : insert 2 ({3} : Finset (Fin 4))={2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h12 : f {1,2,3}-f {1,2}-f {2,3}+f {2}=0 := by
    have h := hf 12
    change f (insert 1 (insert 3 ({2} : Finset (Fin 4))))-
      f (insert 1 ({2} : Finset (Fin 4)))-f (insert 3 ({2} : Finset (Fin 4)))+f {2}=0 at h
    have hAB : insert 1 (insert 3 ({2} : Finset (Fin 4)))={1,2,3} := by decide
    have hA : insert 1 ({2} : Finset (Fin 4))={1,2} := by decide
    have hB : insert 3 ({2} : Finset (Fin 4))={2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h13 : f {0,2,3}-f {0,2}-f {0,3}+f {0}=0 := by
    have h := hf 13
    change f (insert 2 (insert 3 ({0} : Finset (Fin 4))))-
      f (insert 2 ({0} : Finset (Fin 4)))-f (insert 3 ({0} : Finset (Fin 4)))+f {0}=0 at h
    have hAB : insert 2 (insert 3 ({0} : Finset (Fin 4)))={0,2,3} := by decide
    have hA : insert 2 ({0} : Finset (Fin 4))={0,2} := by decide
    have hB : insert 3 ({0} : Finset (Fin 4))={0,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h14 : f {1,2,3}-f {1,2}-f {1,3}+f {1}=0 := by
    have h := hf 14
    change f (insert 2 (insert 3 ({1} : Finset (Fin 4))))-
      f (insert 2 ({1} : Finset (Fin 4)))-f (insert 3 ({1} : Finset (Fin 4)))+f {1}=0 at h
    have hAB : insert 2 (insert 3 ({1} : Finset (Fin 4)))={1,2,3} := by decide
    have hA : insert 2 ({1} : Finset (Fin 4))={1,2} := by decide
    have hB : insert 3 ({1} : Finset (Fin 4))={1,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h15 : f {0,1,2,3}-f {0,1,2}-f {0,1,3}+f {0,1}=0 := by
    have h := hf 15
    change f (insert 2 (insert 3 ({0,1} : Finset (Fin 4))))-
      f (insert 2 ({0,1} : Finset (Fin 4)))-f (insert 3 ({0,1} : Finset (Fin 4)))+f {0,1}=0 at h
    have hAB : insert 2 (insert 3 ({0,1} : Finset (Fin 4)))={0,1,2,3} := by decide
    have hA : insert 2 ({0,1} : Finset (Fin 4))={0,1,2} := by decide
    have hB : insert 3 ({0,1} : Finset (Fin 4))={0,1,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have v0 : f ∅=0 := by
    linear_combination h1
  have v1 : f {0}=0 := by
    linear_combination h2
  have v2 : f {1}=0 := by
    linear_combination h3
  have v3 : f {0,1}=0 := by
    linear_combination (-1) * h1 + h2 + h3 + h6
  have v4 : f {2}=0 := by
    linear_combination h4
  have v5 : f {0,2}=0 := by
    linear_combination h0
  have v6 : f {1,2}=0 := by
    linear_combination h0 + (-1) * h2 + h3 + (-1) * h9 + h11 + h13 + (-1) * h14
  have v7 : f {0,1,2}=0 := by
    linear_combination (2) * h0 + (-1) * h2 + h3 + (-1) * h4 + h7 + (-1) * h9 + h11 + h13 + (-1) * h14
  have v8 : f {3}=0 := by
    linear_combination h5
  have v9 : f {0,3}=0 := by
    linear_combination h0 + (-1) * h4 + h5 + (-1) * h9 + h10
  have v10 : f {1,3}=0 := by
    linear_combination h0 + (-1) * h2 + h3 + (-1) * h4 + h5 + (-1) * h9 + h12 + h13 + (-1) * h14
  have v11 : f {0,1,3}=0 := by
    linear_combination (2) * h0 + (-1) * h2 + h3 + (-2) * h4 + h5 + h8 + (-2) * h9 + h10 + h12 + h13 + (-1) * h14
  have v12 : f {2,3}=0 := by
    linear_combination h0 + (-1) * h2 + h5 + (-1) * h9 + h13
  have v13 : f {0,2,3}=0 := by
    linear_combination (2) * h0 + (-1) * h2 + (-1) * h4 + h5 + (-1) * h9 + h10 + h13
  have v14 : f {1,2,3}=0 := by
    linear_combination (2) * h0 + (-2) * h2 + h3 + (-1) * h4 + h5 + (-2) * h9 + h11 + h12 + (2) * h13 + (-1) * h14
  have v15 : f {0,1,2,3}=0 := by
    linear_combination (4) * h0 + h1 + (-3) * h2 + h3 + (-3) * h4 + h5 + (-1) * h6 + h7 + h8 + (-3) * h9 + h10 + h11 + h12 + (2) * h13 + (-2) * h14 + h15
  funext S
  change f S=0
  have casesS : ∀ S : Finset (Fin 4), S=∅ ∨ S={0} ∨ S={1} ∨ S={0,1} ∨ S={2} ∨ S={0,2} ∨ S={1,2} ∨ S={0,1,2} ∨ S={3} ∨ S={0,3} ∨ S={1,3} ∨ S={0,1,3} ∨ S={2,3} ∨ S={0,2,3} ∨ S={1,2,3} ∨ S={0,1,2,3} := by decide
  rcases casesS S with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem empty_zero : integerFunction ∅=0 := by decide

theorem singleton_zero : ∀ v : Fin 4,integerFunction {v}=0 := by decide

theorem boolean_differences : ∀ u v : Fin 4,u≠ v → ∀ S : Finset (Fin 4),
    u∉S → v∉S → integerDelta integerFunction u v S=0 ∨
      integerDelta integerFunction u v S=1 := by decide

theorem extreme : ExtremeSupermodular (realFunction integerFunction) :=
  extreme_of_row_kernel integerFunction rows pivot pivot_one row_zero valid_rows
    row_kernel_zero empty_zero singleton_zero boolean_differences

end K4Complement

namespace K1112

def integerFunction (S : Finset (Fin 5)) : ℤ :=
  (match subsetMask S with
  | 3 => 1
  | 7 => 1
  | 9 => 1
  | 10 => 1
  | 11 => 2
  | 13 => 1
  | 14 => 1
  | 15 => 3
  | 19 => 1
  | 21 => 1
  | 22 => 1
  | 23 => 2
  | 25 => 1
  | 26 => 1
  | 27 => 2
  | 29 => 2
  | 30 => 2
  | 31 => 4
  | _ => 0)

def rows : Fin 32 → Row (Fin 5) :=
  ![.value {0,1},.value ∅,.value {0},.value {1},.value {2},.value {3},.value {4},.elemental 0 1 {3},.elemental 0 1 {2,4},.elemental 0 1 {3,4},.elemental 0 1 {2,3,4},.elemental 0 2 ∅,.elemental 0 2 {1},.elemental 0 2 {3},.elemental 0 2 {1,4},.elemental 0 3 {1},.elemental 0 3 {1,4},.elemental 0 4 ∅,.elemental 0 4 {1},.elemental 0 4 {1,2,3},.elemental 1 2 ∅,.elemental 1 2 {3},.elemental 1 2 {0,4},.elemental 1 3 {0},.elemental 1 3 {0,4},.elemental 1 4 ∅,.elemental 1 4 {0,2,3},.elemental 2 3 ∅,.elemental 2 3 {4},.elemental 2 3 {0,4},.elemental 2 4 ∅,.elemental 3 4 ∅]

def pivot : Finset (Fin 5) := {0,1}

theorem pivot_one : integerFunction pivot=1 := by decide

theorem row_zero : rows 0=.value pivot := by decide

theorem valid_rows : ∀ i : Fin 32,i≠0 → (rows i).valid integerFunction := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 4096 in
theorem row_kernel_zero (f : SetFunction (Fin 5))
    (hf : ∀ i : Fin 32,(rows i).eval f=0) : f=0 := by
  have h0 : f {0,1}=0 := hf 0
  have h1 : f ∅=0 := hf 1
  have h2 : f {0}=0 := hf 2
  have h3 : f {1}=0 := hf 3
  have h4 : f {2}=0 := hf 4
  have h5 : f {3}=0 := hf 5
  have h6 : f {4}=0 := hf 6
  have h7 : f {0,1,3}-f {0,3}-f {1,3}+f {3}=0 := by
    have h := hf 7
    change f (insert 0 (insert 1 ({3} : Finset (Fin 5))))-
      f (insert 0 ({3} : Finset (Fin 5)))-f (insert 1 ({3} : Finset (Fin 5)))+f {3}=0 at h
    have hAB : insert 0 (insert 1 ({3} : Finset (Fin 5)))={0,1,3} := by decide
    have hA : insert 0 ({3} : Finset (Fin 5))={0,3} := by decide
    have hB : insert 1 ({3} : Finset (Fin 5))={1,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h8 : f {0,1,2,4}-f {0,2,4}-f {1,2,4}+f {2,4}=0 := by
    have h := hf 8
    change f (insert 0 (insert 1 ({2,4} : Finset (Fin 5))))-
      f (insert 0 ({2,4} : Finset (Fin 5)))-f (insert 1 ({2,4} : Finset (Fin 5)))+f {2,4}=0 at h
    have hAB : insert 0 (insert 1 ({2,4} : Finset (Fin 5)))={0,1,2,4} := by decide
    have hA : insert 0 ({2,4} : Finset (Fin 5))={0,2,4} := by decide
    have hB : insert 1 ({2,4} : Finset (Fin 5))={1,2,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h9 : f {0,1,3,4}-f {0,3,4}-f {1,3,4}+f {3,4}=0 := by
    have h := hf 9
    change f (insert 0 (insert 1 ({3,4} : Finset (Fin 5))))-
      f (insert 0 ({3,4} : Finset (Fin 5)))-f (insert 1 ({3,4} : Finset (Fin 5)))+f {3,4}=0 at h
    have hAB : insert 0 (insert 1 ({3,4} : Finset (Fin 5)))={0,1,3,4} := by decide
    have hA : insert 0 ({3,4} : Finset (Fin 5))={0,3,4} := by decide
    have hB : insert 1 ({3,4} : Finset (Fin 5))={1,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h10 : f {0,1,2,3,4}-f {0,2,3,4}-f {1,2,3,4}+f {2,3,4}=0 := by
    have h := hf 10
    change f (insert 0 (insert 1 ({2,3,4} : Finset (Fin 5))))-
      f (insert 0 ({2,3,4} : Finset (Fin 5)))-f (insert 1 ({2,3,4} : Finset (Fin 5)))+f {2,3,4}=0 at h
    have hAB : insert 0 (insert 1 ({2,3,4} : Finset (Fin 5)))={0,1,2,3,4} := by decide
    have hA : insert 0 ({2,3,4} : Finset (Fin 5))={0,2,3,4} := by decide
    have hB : insert 1 ({2,3,4} : Finset (Fin 5))={1,2,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h11 : f {0,2}-f {0}-f {2}+f ∅=0 := by
    have h := hf 11
    change f (insert 0 (insert 2 (∅ : Finset (Fin 5))))-
      f (insert 0 (∅ : Finset (Fin 5)))-f (insert 2 (∅ : Finset (Fin 5)))+f ∅=0 at h
    have hAB : insert 0 (insert 2 (∅ : Finset (Fin 5)))={0,2} := by decide
    have hA : insert 0 (∅ : Finset (Fin 5))={0} := by decide
    have hB : insert 2 (∅ : Finset (Fin 5))={2} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h12 : f {0,1,2}-f {0,1}-f {1,2}+f {1}=0 := by
    have h := hf 12
    change f (insert 0 (insert 2 ({1} : Finset (Fin 5))))-
      f (insert 0 ({1} : Finset (Fin 5)))-f (insert 2 ({1} : Finset (Fin 5)))+f {1}=0 at h
    have hAB : insert 0 (insert 2 ({1} : Finset (Fin 5)))={0,1,2} := by decide
    have hA : insert 0 ({1} : Finset (Fin 5))={0,1} := by decide
    have hB : insert 2 ({1} : Finset (Fin 5))={1,2} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h13 : f {0,2,3}-f {0,3}-f {2,3}+f {3}=0 := by
    have h := hf 13
    change f (insert 0 (insert 2 ({3} : Finset (Fin 5))))-
      f (insert 0 ({3} : Finset (Fin 5)))-f (insert 2 ({3} : Finset (Fin 5)))+f {3}=0 at h
    have hAB : insert 0 (insert 2 ({3} : Finset (Fin 5)))={0,2,3} := by decide
    have hA : insert 0 ({3} : Finset (Fin 5))={0,3} := by decide
    have hB : insert 2 ({3} : Finset (Fin 5))={2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h14 : f {0,1,2,4}-f {0,1,4}-f {1,2,4}+f {1,4}=0 := by
    have h := hf 14
    change f (insert 0 (insert 2 ({1,4} : Finset (Fin 5))))-
      f (insert 0 ({1,4} : Finset (Fin 5)))-f (insert 2 ({1,4} : Finset (Fin 5)))+f {1,4}=0 at h
    have hAB : insert 0 (insert 2 ({1,4} : Finset (Fin 5)))={0,1,2,4} := by decide
    have hA : insert 0 ({1,4} : Finset (Fin 5))={0,1,4} := by decide
    have hB : insert 2 ({1,4} : Finset (Fin 5))={1,2,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h15 : f {0,1,3}-f {0,1}-f {1,3}+f {1}=0 := by
    have h := hf 15
    change f (insert 0 (insert 3 ({1} : Finset (Fin 5))))-
      f (insert 0 ({1} : Finset (Fin 5)))-f (insert 3 ({1} : Finset (Fin 5)))+f {1}=0 at h
    have hAB : insert 0 (insert 3 ({1} : Finset (Fin 5)))={0,1,3} := by decide
    have hA : insert 0 ({1} : Finset (Fin 5))={0,1} := by decide
    have hB : insert 3 ({1} : Finset (Fin 5))={1,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h16 : f {0,1,3,4}-f {0,1,4}-f {1,3,4}+f {1,4}=0 := by
    have h := hf 16
    change f (insert 0 (insert 3 ({1,4} : Finset (Fin 5))))-
      f (insert 0 ({1,4} : Finset (Fin 5)))-f (insert 3 ({1,4} : Finset (Fin 5)))+f {1,4}=0 at h
    have hAB : insert 0 (insert 3 ({1,4} : Finset (Fin 5)))={0,1,3,4} := by decide
    have hA : insert 0 ({1,4} : Finset (Fin 5))={0,1,4} := by decide
    have hB : insert 3 ({1,4} : Finset (Fin 5))={1,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h17 : f {0,4}-f {0}-f {4}+f ∅=0 := by
    have h := hf 17
    change f (insert 0 (insert 4 (∅ : Finset (Fin 5))))-
      f (insert 0 (∅ : Finset (Fin 5)))-f (insert 4 (∅ : Finset (Fin 5)))+f ∅=0 at h
    have hAB : insert 0 (insert 4 (∅ : Finset (Fin 5)))={0,4} := by decide
    have hA : insert 0 (∅ : Finset (Fin 5))={0} := by decide
    have hB : insert 4 (∅ : Finset (Fin 5))={4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h18 : f {0,1,4}-f {0,1}-f {1,4}+f {1}=0 := by
    have h := hf 18
    change f (insert 0 (insert 4 ({1} : Finset (Fin 5))))-
      f (insert 0 ({1} : Finset (Fin 5)))-f (insert 4 ({1} : Finset (Fin 5)))+f {1}=0 at h
    have hAB : insert 0 (insert 4 ({1} : Finset (Fin 5)))={0,1,4} := by decide
    have hA : insert 0 ({1} : Finset (Fin 5))={0,1} := by decide
    have hB : insert 4 ({1} : Finset (Fin 5))={1,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h19 : f {0,1,2,3,4}-f {0,1,2,3}-f {1,2,3,4}+f {1,2,3}=0 := by
    have h := hf 19
    change f (insert 0 (insert 4 ({1,2,3} : Finset (Fin 5))))-
      f (insert 0 ({1,2,3} : Finset (Fin 5)))-f (insert 4 ({1,2,3} : Finset (Fin 5)))+f {1,2,3}=0 at h
    have hAB : insert 0 (insert 4 ({1,2,3} : Finset (Fin 5)))={0,1,2,3,4} := by decide
    have hA : insert 0 ({1,2,3} : Finset (Fin 5))={0,1,2,3} := by decide
    have hB : insert 4 ({1,2,3} : Finset (Fin 5))={1,2,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h20 : f {1,2}-f {1}-f {2}+f ∅=0 := by
    have h := hf 20
    change f (insert 1 (insert 2 (∅ : Finset (Fin 5))))-
      f (insert 1 (∅ : Finset (Fin 5)))-f (insert 2 (∅ : Finset (Fin 5)))+f ∅=0 at h
    have hAB : insert 1 (insert 2 (∅ : Finset (Fin 5)))={1,2} := by decide
    have hA : insert 1 (∅ : Finset (Fin 5))={1} := by decide
    have hB : insert 2 (∅ : Finset (Fin 5))={2} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h21 : f {1,2,3}-f {1,3}-f {2,3}+f {3}=0 := by
    have h := hf 21
    change f (insert 1 (insert 2 ({3} : Finset (Fin 5))))-
      f (insert 1 ({3} : Finset (Fin 5)))-f (insert 2 ({3} : Finset (Fin 5)))+f {3}=0 at h
    have hAB : insert 1 (insert 2 ({3} : Finset (Fin 5)))={1,2,3} := by decide
    have hA : insert 1 ({3} : Finset (Fin 5))={1,3} := by decide
    have hB : insert 2 ({3} : Finset (Fin 5))={2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h22 : f {0,1,2,4}-f {0,1,4}-f {0,2,4}+f {0,4}=0 := by
    have h := hf 22
    change f (insert 1 (insert 2 ({0,4} : Finset (Fin 5))))-
      f (insert 1 ({0,4} : Finset (Fin 5)))-f (insert 2 ({0,4} : Finset (Fin 5)))+f {0,4}=0 at h
    have hAB : insert 1 (insert 2 ({0,4} : Finset (Fin 5)))={0,1,2,4} := by decide
    have hA : insert 1 ({0,4} : Finset (Fin 5))={0,1,4} := by decide
    have hB : insert 2 ({0,4} : Finset (Fin 5))={0,2,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h23 : f {0,1,3}-f {0,1}-f {0,3}+f {0}=0 := by
    have h := hf 23
    change f (insert 1 (insert 3 ({0} : Finset (Fin 5))))-
      f (insert 1 ({0} : Finset (Fin 5)))-f (insert 3 ({0} : Finset (Fin 5)))+f {0}=0 at h
    have hAB : insert 1 (insert 3 ({0} : Finset (Fin 5)))={0,1,3} := by decide
    have hA : insert 1 ({0} : Finset (Fin 5))={0,1} := by decide
    have hB : insert 3 ({0} : Finset (Fin 5))={0,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h24 : f {0,1,3,4}-f {0,1,4}-f {0,3,4}+f {0,4}=0 := by
    have h := hf 24
    change f (insert 1 (insert 3 ({0,4} : Finset (Fin 5))))-
      f (insert 1 ({0,4} : Finset (Fin 5)))-f (insert 3 ({0,4} : Finset (Fin 5)))+f {0,4}=0 at h
    have hAB : insert 1 (insert 3 ({0,4} : Finset (Fin 5)))={0,1,3,4} := by decide
    have hA : insert 1 ({0,4} : Finset (Fin 5))={0,1,4} := by decide
    have hB : insert 3 ({0,4} : Finset (Fin 5))={0,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h25 : f {1,4}-f {1}-f {4}+f ∅=0 := by
    have h := hf 25
    change f (insert 1 (insert 4 (∅ : Finset (Fin 5))))-
      f (insert 1 (∅ : Finset (Fin 5)))-f (insert 4 (∅ : Finset (Fin 5)))+f ∅=0 at h
    have hAB : insert 1 (insert 4 (∅ : Finset (Fin 5)))={1,4} := by decide
    have hA : insert 1 (∅ : Finset (Fin 5))={1} := by decide
    have hB : insert 4 (∅ : Finset (Fin 5))={4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h26 : f {0,1,2,3,4}-f {0,1,2,3}-f {0,2,3,4}+f {0,2,3}=0 := by
    have h := hf 26
    change f (insert 1 (insert 4 ({0,2,3} : Finset (Fin 5))))-
      f (insert 1 ({0,2,3} : Finset (Fin 5)))-f (insert 4 ({0,2,3} : Finset (Fin 5)))+f {0,2,3}=0 at h
    have hAB : insert 1 (insert 4 ({0,2,3} : Finset (Fin 5)))={0,1,2,3,4} := by decide
    have hA : insert 1 ({0,2,3} : Finset (Fin 5))={0,1,2,3} := by decide
    have hB : insert 4 ({0,2,3} : Finset (Fin 5))={0,2,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h27 : f {2,3}-f {2}-f {3}+f ∅=0 := by
    have h := hf 27
    change f (insert 2 (insert 3 (∅ : Finset (Fin 5))))-
      f (insert 2 (∅ : Finset (Fin 5)))-f (insert 3 (∅ : Finset (Fin 5)))+f ∅=0 at h
    have hAB : insert 2 (insert 3 (∅ : Finset (Fin 5)))={2,3} := by decide
    have hA : insert 2 (∅ : Finset (Fin 5))={2} := by decide
    have hB : insert 3 (∅ : Finset (Fin 5))={3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h28 : f {2,3,4}-f {2,4}-f {3,4}+f {4}=0 := by
    have h := hf 28
    change f (insert 2 (insert 3 ({4} : Finset (Fin 5))))-
      f (insert 2 ({4} : Finset (Fin 5)))-f (insert 3 ({4} : Finset (Fin 5)))+f {4}=0 at h
    have hAB : insert 2 (insert 3 ({4} : Finset (Fin 5)))={2,3,4} := by decide
    have hA : insert 2 ({4} : Finset (Fin 5))={2,4} := by decide
    have hB : insert 3 ({4} : Finset (Fin 5))={3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h29 : f {0,2,3,4}-f {0,2,4}-f {0,3,4}+f {0,4}=0 := by
    have h := hf 29
    change f (insert 2 (insert 3 ({0,4} : Finset (Fin 5))))-
      f (insert 2 ({0,4} : Finset (Fin 5)))-f (insert 3 ({0,4} : Finset (Fin 5)))+f {0,4}=0 at h
    have hAB : insert 2 (insert 3 ({0,4} : Finset (Fin 5)))={0,2,3,4} := by decide
    have hA : insert 2 ({0,4} : Finset (Fin 5))={0,2,4} := by decide
    have hB : insert 3 ({0,4} : Finset (Fin 5))={0,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h30 : f {2,4}-f {2}-f {4}+f ∅=0 := by
    have h := hf 30
    change f (insert 2 (insert 4 (∅ : Finset (Fin 5))))-
      f (insert 2 (∅ : Finset (Fin 5)))-f (insert 4 (∅ : Finset (Fin 5)))+f ∅=0 at h
    have hAB : insert 2 (insert 4 (∅ : Finset (Fin 5)))={2,4} := by decide
    have hA : insert 2 (∅ : Finset (Fin 5))={2} := by decide
    have hB : insert 4 (∅ : Finset (Fin 5))={4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h31 : f {3,4}-f {3}-f {4}+f ∅=0 := by
    have h := hf 31
    change f (insert 3 (insert 4 (∅ : Finset (Fin 5))))-
      f (insert 3 (∅ : Finset (Fin 5)))-f (insert 4 (∅ : Finset (Fin 5)))+f ∅=0 at h
    have hAB : insert 3 (insert 4 (∅ : Finset (Fin 5)))={3,4} := by decide
    have hA : insert 3 (∅ : Finset (Fin 5))={3} := by decide
    have hB : insert 4 (∅ : Finset (Fin 5))={4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have v0 : f ∅=0 := by
    linear_combination h1
  have v1 : f {0}=0 := by
    linear_combination h2
  have v2 : f {1}=0 := by
    linear_combination h3
  have v3 : f {0,1}=0 := by
    linear_combination h0
  have v4 : f {2}=0 := by
    linear_combination h4
  have v5 : f {0,2}=0 := by
    linear_combination (-1) * h1 + h2 + h4 + h11
  have v6 : f {1,2}=0 := by
    linear_combination (-1) * h1 + h3 + h4 + h20
  have v7 : f {0,1,2}=0 := by
    linear_combination h0 + (-1) * h1 + h4 + h12 + h20
  have v8 : f {3}=0 := by
    linear_combination h5
  have v9 : f {0,3}=0 := by
    linear_combination h0 + (-1) * h3 + h5 + (-1) * h7 + h15
  have v10 : f {1,3}=0 := by
    linear_combination h0 + (-1) * h2 + h5 + (-1) * h7 + h23
  have v11 : f {0,1,3}=0 := by
    linear_combination (2) * h0 + (-1) * h2 + (-1) * h3 + h5 + (-1) * h7 + h15 + h23
  have v12 : f {2,3}=0 := by
    linear_combination (-1) * h1 + h4 + h5 + h27
  have v13 : f {0,2,3}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h3 + h4 + h5 + (-1) * h7 + h13 + h15 + h27
  have v14 : f {1,2,3}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h2 + h4 + h5 + (-1) * h7 + h21 + h23 + h27
  have v15 : f {0,1,2,3}=0 := by
    linear_combination (3) * h0 + (-2) * h2 + (-2) * h3 + h4 + h5 + (-1) * h7 + (-1) * h8 + (-1) * h9 + h10 + h14 + h16 + (-1) * h17 + (2) * h18 + (-1) * h19 + h21 + h23 + h27 + (-1) * h28 + h29
  have v16 : f {4}=0 := by
    linear_combination h6
  have v17 : f {0,4}=0 := by
    linear_combination (-1) * h1 + h2 + h6 + h17
  have v18 : f {1,4}=0 := by
    linear_combination (-1) * h1 + h3 + h6 + h25
  have v19 : f {0,1,4}=0 := by
    linear_combination h0 + (-1) * h1 + h6 + h18 + h25
  have v20 : f {2,4}=0 := by
    linear_combination (-1) * h1 + h4 + h6 + h30
  have v21 : f {0,2,4}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h3 + h4 + h6 + (-1) * h8 + h14 + h18 + h30
  have v22 : f {1,2,4}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h2 + h4 + h6 + (-1) * h8 + (-1) * h17 + h18 + h22 + h25 + h30
  have v23 : f {0,1,2,4}=0 := by
    linear_combination (2) * h0 + (-1) * h1 + (-1) * h2 + (-1) * h3 + h4 + h6 + (-1) * h8 + h14 + (-1) * h17 + (2) * h18 + h22 + h25 + h30
  have v24 : f {3,4}=0 := by
    linear_combination (-1) * h1 + h5 + h6 + h31
  have v25 : f {0,3,4}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h3 + h5 + h6 + (-1) * h9 + h16 + h18 + h31
  have v26 : f {1,3,4}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h2 + h5 + h6 + (-1) * h9 + (-1) * h17 + h18 + h24 + h25 + h31
  have v27 : f {0,1,3,4}=0 := by
    linear_combination (2) * h0 + (-1) * h1 + (-1) * h2 + (-1) * h3 + h5 + h6 + (-1) * h9 + h16 + (-1) * h17 + (2) * h18 + h24 + h25 + h31
  have v28 : f {2,3,4}=0 := by
    linear_combination (-2) * h1 + h4 + h5 + h6 + h28 + h30 + h31
  have v29 : f {0,2,3,4}=0 := by
    linear_combination (2) * h0 + (-1) * h1 + (-1) * h2 + (-2) * h3 + h4 + h5 + h6 + (-1) * h8 + (-1) * h9 + h14 + h16 + (-1) * h17 + (2) * h18 + h29 + h30 + h31
  have v30 : f {1,2,3,4}=0 := by
    linear_combination (2) * h0 + (-1) * h1 + (-2) * h2 + (-1) * h3 + h4 + h5 + h6 + (-1) * h8 + (-1) * h9 + (-1) * h13 + h14 + (-1) * h15 + h16 + (-1) * h17 + (2) * h18 + (-1) * h19 + h21 + h23 + h26 + h29 + h30 + h31
  have v31 : f {0,1,2,3,4}=0 := by
    linear_combination (4) * h0 + (-3) * h2 + (-3) * h3 + h4 + h5 + h6 + (-2) * h8 + (-2) * h9 + h10 + (-1) * h13 + (2) * h14 + (-1) * h15 + (2) * h16 + (-2) * h17 + (4) * h18 + (-1) * h19 + h21 + h23 + h26 + (-1) * h28 + (2) * h29 + h30 + h31
  funext S
  change f S=0
  have casesS : ∀ S : Finset (Fin 5), S=∅ ∨ S={0} ∨ S={1} ∨ S={0,1} ∨ S={2} ∨ S={0,2} ∨ S={1,2} ∨ S={0,1,2} ∨ S={3} ∨ S={0,3} ∨ S={1,3} ∨ S={0,1,3} ∨ S={2,3} ∨ S={0,2,3} ∨ S={1,2,3} ∨ S={0,1,2,3} ∨ S={4} ∨ S={0,4} ∨ S={1,4} ∨ S={0,1,4} ∨ S={2,4} ∨ S={0,2,4} ∨ S={1,2,4} ∨ S={0,1,2,4} ∨ S={3,4} ∨ S={0,3,4} ∨ S={1,3,4} ∨ S={0,1,3,4} ∨ S={2,3,4} ∨ S={0,2,3,4} ∨ S={1,2,3,4} ∨ S={0,1,2,3,4} := by decide
  rcases casesS S with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem empty_zero : integerFunction ∅=0 := by decide

theorem singleton_zero : ∀ v : Fin 5,integerFunction {v}=0 := by decide

theorem boolean_differences : ∀ u v : Fin 5,u≠ v → ∀ S : Finset (Fin 5),
    u∉S → v∉S → integerDelta integerFunction u v S=0 ∨
      integerDelta integerFunction u v S=1 := by decide

theorem extreme : ExtremeSupermodular (realFunction integerFunction) :=
  extreme_of_row_kernel integerFunction rows pivot pivot_one row_zero valid_rows
    row_kernel_zero empty_zero singleton_zero boolean_differences

end K1112

namespace K1112Complement

def integerFunction (S : Finset (Fin 5)) : ℤ :=
  (match subsetMask S with
  | 5 => 1
  | 6 => 1
  | 7 => 2
  | 11 => 1
  | 12 => 1
  | 13 => 2
  | 14 => 2
  | 15 => 3
  | 17 => 1
  | 18 => 1
  | 19 => 2
  | 20 => 1
  | 21 => 2
  | 22 => 2
  | 23 => 4
  | 25 => 1
  | 26 => 1
  | 27 => 3
  | 28 => 2
  | 29 => 3
  | 30 => 3
  | 31 => 5
  | _ => 0)

def rows : Fin 32 → Row (Fin 5) :=
  ![.value {0,2},.value ∅,.value {0},.value {1},.value {2},.value {3},.value {4},.elemental 0 1 ∅,.elemental 0 1 {2},.elemental 0 1 {2,3},.elemental 0 1 {4},.elemental 0 2 {1,3},.elemental 0 2 {4},.elemental 0 2 {3,4},.elemental 0 2 {1,3,4},.elemental 0 3 ∅,.elemental 0 3 {2},.elemental 0 3 {4},.elemental 0 3 {1,2,4},.elemental 0 4 {2},.elemental 1 2 {0,3},.elemental 1 2 {4},.elemental 1 2 {3,4},.elemental 1 3 ∅,.elemental 1 3 {2},.elemental 1 3 {4},.elemental 1 4 {2},.elemental 2 3 {0,1},.elemental 2 3 {0,1,4},.elemental 2 4 {0},.elemental 2 4 {0,1},.elemental 3 4 ∅]

def pivot : Finset (Fin 5) := {0,2}

theorem pivot_one : integerFunction pivot=1 := by decide

theorem row_zero : rows 0=.value pivot := by decide

theorem valid_rows : ∀ i : Fin 32,i≠0 → (rows i).valid integerFunction := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 4096 in
theorem row_kernel_zero (f : SetFunction (Fin 5))
    (hf : ∀ i : Fin 32,(rows i).eval f=0) : f=0 := by
  have h0 : f {0,2}=0 := hf 0
  have h1 : f ∅=0 := hf 1
  have h2 : f {0}=0 := hf 2
  have h3 : f {1}=0 := hf 3
  have h4 : f {2}=0 := hf 4
  have h5 : f {3}=0 := hf 5
  have h6 : f {4}=0 := hf 6
  have h7 : f {0,1}-f {0}-f {1}+f ∅=0 := by
    have h := hf 7
    change f (insert 0 (insert 1 (∅ : Finset (Fin 5))))-
      f (insert 0 (∅ : Finset (Fin 5)))-f (insert 1 (∅ : Finset (Fin 5)))+f ∅=0 at h
    have hAB : insert 0 (insert 1 (∅ : Finset (Fin 5)))={0,1} := by decide
    have hA : insert 0 (∅ : Finset (Fin 5))={0} := by decide
    have hB : insert 1 (∅ : Finset (Fin 5))={1} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h8 : f {0,1,2}-f {0,2}-f {1,2}+f {2}=0 := by
    have h := hf 8
    change f (insert 0 (insert 1 ({2} : Finset (Fin 5))))-
      f (insert 0 ({2} : Finset (Fin 5)))-f (insert 1 ({2} : Finset (Fin 5)))+f {2}=0 at h
    have hAB : insert 0 (insert 1 ({2} : Finset (Fin 5)))={0,1,2} := by decide
    have hA : insert 0 ({2} : Finset (Fin 5))={0,2} := by decide
    have hB : insert 1 ({2} : Finset (Fin 5))={1,2} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h9 : f {0,1,2,3}-f {0,2,3}-f {1,2,3}+f {2,3}=0 := by
    have h := hf 9
    change f (insert 0 (insert 1 ({2,3} : Finset (Fin 5))))-
      f (insert 0 ({2,3} : Finset (Fin 5)))-f (insert 1 ({2,3} : Finset (Fin 5)))+f {2,3}=0 at h
    have hAB : insert 0 (insert 1 ({2,3} : Finset (Fin 5)))={0,1,2,3} := by decide
    have hA : insert 0 ({2,3} : Finset (Fin 5))={0,2,3} := by decide
    have hB : insert 1 ({2,3} : Finset (Fin 5))={1,2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h10 : f {0,1,4}-f {0,4}-f {1,4}+f {4}=0 := by
    have h := hf 10
    change f (insert 0 (insert 1 ({4} : Finset (Fin 5))))-
      f (insert 0 ({4} : Finset (Fin 5)))-f (insert 1 ({4} : Finset (Fin 5)))+f {4}=0 at h
    have hAB : insert 0 (insert 1 ({4} : Finset (Fin 5)))={0,1,4} := by decide
    have hA : insert 0 ({4} : Finset (Fin 5))={0,4} := by decide
    have hB : insert 1 ({4} : Finset (Fin 5))={1,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h11 : f {0,1,2,3}-f {0,1,3}-f {1,2,3}+f {1,3}=0 := by
    have h := hf 11
    change f (insert 0 (insert 2 ({1,3} : Finset (Fin 5))))-
      f (insert 0 ({1,3} : Finset (Fin 5)))-f (insert 2 ({1,3} : Finset (Fin 5)))+f {1,3}=0 at h
    have hAB : insert 0 (insert 2 ({1,3} : Finset (Fin 5)))={0,1,2,3} := by decide
    have hA : insert 0 ({1,3} : Finset (Fin 5))={0,1,3} := by decide
    have hB : insert 2 ({1,3} : Finset (Fin 5))={1,2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h12 : f {0,2,4}-f {0,4}-f {2,4}+f {4}=0 := by
    have h := hf 12
    change f (insert 0 (insert 2 ({4} : Finset (Fin 5))))-
      f (insert 0 ({4} : Finset (Fin 5)))-f (insert 2 ({4} : Finset (Fin 5)))+f {4}=0 at h
    have hAB : insert 0 (insert 2 ({4} : Finset (Fin 5)))={0,2,4} := by decide
    have hA : insert 0 ({4} : Finset (Fin 5))={0,4} := by decide
    have hB : insert 2 ({4} : Finset (Fin 5))={2,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h13 : f {0,2,3,4}-f {0,3,4}-f {2,3,4}+f {3,4}=0 := by
    have h := hf 13
    change f (insert 0 (insert 2 ({3,4} : Finset (Fin 5))))-
      f (insert 0 ({3,4} : Finset (Fin 5)))-f (insert 2 ({3,4} : Finset (Fin 5)))+f {3,4}=0 at h
    have hAB : insert 0 (insert 2 ({3,4} : Finset (Fin 5)))={0,2,3,4} := by decide
    have hA : insert 0 ({3,4} : Finset (Fin 5))={0,3,4} := by decide
    have hB : insert 2 ({3,4} : Finset (Fin 5))={2,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h14 : f {0,1,2,3,4}-f {0,1,3,4}-f {1,2,3,4}+f {1,3,4}=0 := by
    have h := hf 14
    change f (insert 0 (insert 2 ({1,3,4} : Finset (Fin 5))))-
      f (insert 0 ({1,3,4} : Finset (Fin 5)))-f (insert 2 ({1,3,4} : Finset (Fin 5)))+f {1,3,4}=0 at h
    have hAB : insert 0 (insert 2 ({1,3,4} : Finset (Fin 5)))={0,1,2,3,4} := by decide
    have hA : insert 0 ({1,3,4} : Finset (Fin 5))={0,1,3,4} := by decide
    have hB : insert 2 ({1,3,4} : Finset (Fin 5))={1,2,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h15 : f {0,3}-f {0}-f {3}+f ∅=0 := by
    have h := hf 15
    change f (insert 0 (insert 3 (∅ : Finset (Fin 5))))-
      f (insert 0 (∅ : Finset (Fin 5)))-f (insert 3 (∅ : Finset (Fin 5)))+f ∅=0 at h
    have hAB : insert 0 (insert 3 (∅ : Finset (Fin 5)))={0,3} := by decide
    have hA : insert 0 (∅ : Finset (Fin 5))={0} := by decide
    have hB : insert 3 (∅ : Finset (Fin 5))={3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h16 : f {0,2,3}-f {0,2}-f {2,3}+f {2}=0 := by
    have h := hf 16
    change f (insert 0 (insert 3 ({2} : Finset (Fin 5))))-
      f (insert 0 ({2} : Finset (Fin 5)))-f (insert 3 ({2} : Finset (Fin 5)))+f {2}=0 at h
    have hAB : insert 0 (insert 3 ({2} : Finset (Fin 5)))={0,2,3} := by decide
    have hA : insert 0 ({2} : Finset (Fin 5))={0,2} := by decide
    have hB : insert 3 ({2} : Finset (Fin 5))={2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h17 : f {0,3,4}-f {0,4}-f {3,4}+f {4}=0 := by
    have h := hf 17
    change f (insert 0 (insert 3 ({4} : Finset (Fin 5))))-
      f (insert 0 ({4} : Finset (Fin 5)))-f (insert 3 ({4} : Finset (Fin 5)))+f {4}=0 at h
    have hAB : insert 0 (insert 3 ({4} : Finset (Fin 5)))={0,3,4} := by decide
    have hA : insert 0 ({4} : Finset (Fin 5))={0,4} := by decide
    have hB : insert 3 ({4} : Finset (Fin 5))={3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h18 : f {0,1,2,3,4}-f {0,1,2,4}-f {1,2,3,4}+f {1,2,4}=0 := by
    have h := hf 18
    change f (insert 0 (insert 3 ({1,2,4} : Finset (Fin 5))))-
      f (insert 0 ({1,2,4} : Finset (Fin 5)))-f (insert 3 ({1,2,4} : Finset (Fin 5)))+f {1,2,4}=0 at h
    have hAB : insert 0 (insert 3 ({1,2,4} : Finset (Fin 5)))={0,1,2,3,4} := by decide
    have hA : insert 0 ({1,2,4} : Finset (Fin 5))={0,1,2,4} := by decide
    have hB : insert 3 ({1,2,4} : Finset (Fin 5))={1,2,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h19 : f {0,2,4}-f {0,2}-f {2,4}+f {2}=0 := by
    have h := hf 19
    change f (insert 0 (insert 4 ({2} : Finset (Fin 5))))-
      f (insert 0 ({2} : Finset (Fin 5)))-f (insert 4 ({2} : Finset (Fin 5)))+f {2}=0 at h
    have hAB : insert 0 (insert 4 ({2} : Finset (Fin 5)))={0,2,4} := by decide
    have hA : insert 0 ({2} : Finset (Fin 5))={0,2} := by decide
    have hB : insert 4 ({2} : Finset (Fin 5))={2,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h20 : f {0,1,2,3}-f {0,1,3}-f {0,2,3}+f {0,3}=0 := by
    have h := hf 20
    change f (insert 1 (insert 2 ({0,3} : Finset (Fin 5))))-
      f (insert 1 ({0,3} : Finset (Fin 5)))-f (insert 2 ({0,3} : Finset (Fin 5)))+f {0,3}=0 at h
    have hAB : insert 1 (insert 2 ({0,3} : Finset (Fin 5)))={0,1,2,3} := by decide
    have hA : insert 1 ({0,3} : Finset (Fin 5))={0,1,3} := by decide
    have hB : insert 2 ({0,3} : Finset (Fin 5))={0,2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h21 : f {1,2,4}-f {1,4}-f {2,4}+f {4}=0 := by
    have h := hf 21
    change f (insert 1 (insert 2 ({4} : Finset (Fin 5))))-
      f (insert 1 ({4} : Finset (Fin 5)))-f (insert 2 ({4} : Finset (Fin 5)))+f {4}=0 at h
    have hAB : insert 1 (insert 2 ({4} : Finset (Fin 5)))={1,2,4} := by decide
    have hA : insert 1 ({4} : Finset (Fin 5))={1,4} := by decide
    have hB : insert 2 ({4} : Finset (Fin 5))={2,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h22 : f {1,2,3,4}-f {1,3,4}-f {2,3,4}+f {3,4}=0 := by
    have h := hf 22
    change f (insert 1 (insert 2 ({3,4} : Finset (Fin 5))))-
      f (insert 1 ({3,4} : Finset (Fin 5)))-f (insert 2 ({3,4} : Finset (Fin 5)))+f {3,4}=0 at h
    have hAB : insert 1 (insert 2 ({3,4} : Finset (Fin 5)))={1,2,3,4} := by decide
    have hA : insert 1 ({3,4} : Finset (Fin 5))={1,3,4} := by decide
    have hB : insert 2 ({3,4} : Finset (Fin 5))={2,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h23 : f {1,3}-f {1}-f {3}+f ∅=0 := by
    have h := hf 23
    change f (insert 1 (insert 3 (∅ : Finset (Fin 5))))-
      f (insert 1 (∅ : Finset (Fin 5)))-f (insert 3 (∅ : Finset (Fin 5)))+f ∅=0 at h
    have hAB : insert 1 (insert 3 (∅ : Finset (Fin 5)))={1,3} := by decide
    have hA : insert 1 (∅ : Finset (Fin 5))={1} := by decide
    have hB : insert 3 (∅ : Finset (Fin 5))={3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h24 : f {1,2,3}-f {1,2}-f {2,3}+f {2}=0 := by
    have h := hf 24
    change f (insert 1 (insert 3 ({2} : Finset (Fin 5))))-
      f (insert 1 ({2} : Finset (Fin 5)))-f (insert 3 ({2} : Finset (Fin 5)))+f {2}=0 at h
    have hAB : insert 1 (insert 3 ({2} : Finset (Fin 5)))={1,2,3} := by decide
    have hA : insert 1 ({2} : Finset (Fin 5))={1,2} := by decide
    have hB : insert 3 ({2} : Finset (Fin 5))={2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h25 : f {1,3,4}-f {1,4}-f {3,4}+f {4}=0 := by
    have h := hf 25
    change f (insert 1 (insert 3 ({4} : Finset (Fin 5))))-
      f (insert 1 ({4} : Finset (Fin 5)))-f (insert 3 ({4} : Finset (Fin 5)))+f {4}=0 at h
    have hAB : insert 1 (insert 3 ({4} : Finset (Fin 5)))={1,3,4} := by decide
    have hA : insert 1 ({4} : Finset (Fin 5))={1,4} := by decide
    have hB : insert 3 ({4} : Finset (Fin 5))={3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h26 : f {1,2,4}-f {1,2}-f {2,4}+f {2}=0 := by
    have h := hf 26
    change f (insert 1 (insert 4 ({2} : Finset (Fin 5))))-
      f (insert 1 ({2} : Finset (Fin 5)))-f (insert 4 ({2} : Finset (Fin 5)))+f {2}=0 at h
    have hAB : insert 1 (insert 4 ({2} : Finset (Fin 5)))={1,2,4} := by decide
    have hA : insert 1 ({2} : Finset (Fin 5))={1,2} := by decide
    have hB : insert 4 ({2} : Finset (Fin 5))={2,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h27 : f {0,1,2,3}-f {0,1,2}-f {0,1,3}+f {0,1}=0 := by
    have h := hf 27
    change f (insert 2 (insert 3 ({0,1} : Finset (Fin 5))))-
      f (insert 2 ({0,1} : Finset (Fin 5)))-f (insert 3 ({0,1} : Finset (Fin 5)))+f {0,1}=0 at h
    have hAB : insert 2 (insert 3 ({0,1} : Finset (Fin 5)))={0,1,2,3} := by decide
    have hA : insert 2 ({0,1} : Finset (Fin 5))={0,1,2} := by decide
    have hB : insert 3 ({0,1} : Finset (Fin 5))={0,1,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h28 : f {0,1,2,3,4}-f {0,1,2,4}-f {0,1,3,4}+f {0,1,4}=0 := by
    have h := hf 28
    change f (insert 2 (insert 3 ({0,1,4} : Finset (Fin 5))))-
      f (insert 2 ({0,1,4} : Finset (Fin 5)))-f (insert 3 ({0,1,4} : Finset (Fin 5)))+f {0,1,4}=0 at h
    have hAB : insert 2 (insert 3 ({0,1,4} : Finset (Fin 5)))={0,1,2,3,4} := by decide
    have hA : insert 2 ({0,1,4} : Finset (Fin 5))={0,1,2,4} := by decide
    have hB : insert 3 ({0,1,4} : Finset (Fin 5))={0,1,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h29 : f {0,2,4}-f {0,2}-f {0,4}+f {0}=0 := by
    have h := hf 29
    change f (insert 2 (insert 4 ({0} : Finset (Fin 5))))-
      f (insert 2 ({0} : Finset (Fin 5)))-f (insert 4 ({0} : Finset (Fin 5)))+f {0}=0 at h
    have hAB : insert 2 (insert 4 ({0} : Finset (Fin 5)))={0,2,4} := by decide
    have hA : insert 2 ({0} : Finset (Fin 5))={0,2} := by decide
    have hB : insert 4 ({0} : Finset (Fin 5))={0,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h30 : f {0,1,2,4}-f {0,1,2}-f {0,1,4}+f {0,1}=0 := by
    have h := hf 30
    change f (insert 2 (insert 4 ({0,1} : Finset (Fin 5))))-
      f (insert 2 ({0,1} : Finset (Fin 5)))-f (insert 4 ({0,1} : Finset (Fin 5)))+f {0,1}=0 at h
    have hAB : insert 2 (insert 4 ({0,1} : Finset (Fin 5)))={0,1,2,4} := by decide
    have hA : insert 2 ({0,1} : Finset (Fin 5))={0,1,2} := by decide
    have hB : insert 4 ({0,1} : Finset (Fin 5))={0,1,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h31 : f {3,4}-f {3}-f {4}+f ∅=0 := by
    have h := hf 31
    change f (insert 3 (insert 4 (∅ : Finset (Fin 5))))-
      f (insert 3 (∅ : Finset (Fin 5)))-f (insert 4 (∅ : Finset (Fin 5)))+f ∅=0 at h
    have hAB : insert 3 (insert 4 (∅ : Finset (Fin 5)))={3,4} := by decide
    have hA : insert 3 (∅ : Finset (Fin 5))={3} := by decide
    have hB : insert 4 (∅ : Finset (Fin 5))={4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have v0 : f ∅=0 := by
    linear_combination h1
  have v1 : f {0}=0 := by
    linear_combination h2
  have v2 : f {1}=0 := by
    linear_combination h3
  have v3 : f {0,1}=0 := by
    linear_combination (-1) * h1 + h2 + h3 + h7
  have v4 : f {2}=0 := by
    linear_combination h4
  have v5 : f {0,2}=0 := by
    linear_combination h0
  have v6 : f {1,2}=0 := by
    linear_combination h0 + (-1) * h2 + h3 + (-1) * h11 + (-1) * h15 + h16 + h20 + h23 + (-1) * h24
  have v7 : f {0,1,2}=0 := by
    linear_combination (2) * h0 + (-1) * h2 + h3 + (-1) * h4 + h8 + (-1) * h11 + (-1) * h15 + h16 + h20 + h23 + (-1) * h24
  have v8 : f {3}=0 := by
    linear_combination h5
  have v9 : f {0,3}=0 := by
    linear_combination (-1) * h1 + h2 + h5 + h15
  have v10 : f {1,3}=0 := by
    linear_combination (-1) * h1 + h3 + h5 + h23
  have v11 : f {0,1,3}=0 := by
    linear_combination h0 + (-1) * h1 + h3 + (-1) * h4 + h5 + h9 + (-1) * h11 + h16 + h23
  have v12 : f {2,3}=0 := by
    linear_combination h0 + (-1) * h2 + h5 + (-1) * h7 + h8 + (-1) * h11 + h23 + (-1) * h24 + h27
  have v13 : f {0,2,3}=0 := by
    linear_combination (2) * h0 + (-1) * h2 + (-1) * h4 + h5 + (-1) * h7 + h8 + (-1) * h11 + h16 + h23 + (-1) * h24 + h27
  have v14 : f {1,2,3}=0 := by
    linear_combination (2) * h0 + (-2) * h2 + h3 + (-1) * h4 + h5 + (-1) * h7 + h8 + (-2) * h11 + (-1) * h15 + h16 + h20 + (2) * h23 + (-1) * h24 + h27
  have v15 : f {0,1,2,3}=0 := by
    linear_combination (3) * h0 + (-2) * h2 + h3 + (-2) * h4 + h5 + (-1) * h7 + h8 + h9 + (-2) * h11 + (-1) * h15 + (2) * h16 + h20 + (2) * h23 + (-1) * h24 + h27
  have v16 : f {4}=0 := by
    linear_combination h6
  have v17 : f {0,4}=0 := by
    linear_combination h0 + (-1) * h4 + h6 + (-1) * h12 + h19
  have v18 : f {1,4}=0 := by
    linear_combination h0 + (-1) * h2 + h3 + (-1) * h4 + h6 + (-1) * h11 + (-1) * h15 + h16 + h20 + (-1) * h21 + h23 + (-1) * h24 + h26
  have v19 : f {0,1,4}=0 := by
    linear_combination (2) * h0 + (-1) * h2 + h3 + (-2) * h4 + h6 + h10 + (-1) * h11 + (-1) * h12 + (-1) * h15 + h16 + h19 + h20 + (-1) * h21 + h23 + (-1) * h24 + h26
  have v20 : f {2,4}=0 := by
    linear_combination h0 + (-1) * h2 + h6 + (-1) * h12 + h29
  have v21 : f {0,2,4}=0 := by
    linear_combination (2) * h0 + (-1) * h2 + (-1) * h4 + h6 + (-1) * h12 + h19 + h29
  have v22 : f {1,2,4}=0 := by
    linear_combination (2) * h0 + (-2) * h2 + h3 + (-1) * h4 + h6 + (-1) * h11 + (-1) * h12 + (-1) * h15 + h16 + h20 + h23 + (-1) * h24 + h26 + h29
  have v23 : f {0,1,2,4}=0 := by
    linear_combination (4) * h0 + h1 + (-3) * h2 + h3 + (-3) * h4 + h6 + (-1) * h7 + h8 + h10 + (-2) * h11 + (-1) * h12 + (-2) * h15 + (2) * h16 + h19 + (2) * h20 + (-1) * h21 + (2) * h23 + (-2) * h24 + h26 + h30
  have v24 : f {3,4}=0 := by
    linear_combination (-1) * h1 + h5 + h6 + h31
  have v25 : f {0,3,4}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h4 + h5 + h6 + (-1) * h12 + h17 + h19 + h31
  have v26 : f {1,3,4}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h2 + h3 + (-1) * h4 + h5 + h6 + (-1) * h11 + (-1) * h15 + h16 + h20 + (-1) * h21 + h23 + (-1) * h24 + h25 + h26 + h31
  have v27 : f {0,1,3,4}=0 := by
    linear_combination (3) * h0 + (-2) * h2 + h3 + (-3) * h4 + h5 + h6 + (-1) * h7 + h8 + h10 + (-2) * h11 + (-1) * h14 + (-2) * h15 + (2) * h16 + h18 + h19 + (2) * h20 + (-2) * h21 + (2) * h23 + (-2) * h24 + h25 + h26 + (-1) * h29 + h30 + h31
  have v28 : f {2,3,4}=0 := by
    linear_combination (2) * h0 + (-2) * h2 + (-1) * h4 + h5 + h6 + (-1) * h7 + h8 + (-1) * h11 + (-1) * h14 + (-1) * h15 + h16 + h20 + (-1) * h22 + h23 + (-1) * h24 + h28 + h30 + h31
  have v29 : f {0,2,3,4}=0 := by
    linear_combination (3) * h0 + (-2) * h2 + (-2) * h4 + h5 + h6 + (-1) * h7 + h8 + (-1) * h11 + (-1) * h12 + h13 + (-1) * h14 + (-1) * h15 + h16 + h17 + h19 + h20 + (-1) * h22 + h23 + (-1) * h24 + h28 + h30 + h31
  have v30 : f {1,2,3,4}=0 := by
    linear_combination (3) * h0 + (-3) * h2 + h3 + (-2) * h4 + h5 + h6 + (-1) * h7 + h8 + (-2) * h11 + (-1) * h14 + (-2) * h15 + (2) * h16 + (2) * h20 + (-1) * h21 + (2) * h23 + (-2) * h24 + h25 + h26 + h28 + h30 + h31
  have v31 : f {0,1,2,3,4}=0 := by
    linear_combination (5) * h0 + h1 + (-4) * h2 + h3 + (-4) * h4 + h5 + h6 + (-2) * h7 + (2) * h8 + h10 + (-3) * h11 + (-1) * h14 + (-3) * h15 + (3) * h16 + h18 + h19 + (3) * h20 + (-2) * h21 + (3) * h23 + (-3) * h24 + h25 + h26 + h28 + (-1) * h29 + (2) * h30 + h31
  funext S
  change f S=0
  have casesS : ∀ S : Finset (Fin 5), S=∅ ∨ S={0} ∨ S={1} ∨ S={0,1} ∨ S={2} ∨ S={0,2} ∨ S={1,2} ∨ S={0,1,2} ∨ S={3} ∨ S={0,3} ∨ S={1,3} ∨ S={0,1,3} ∨ S={2,3} ∨ S={0,2,3} ∨ S={1,2,3} ∨ S={0,1,2,3} ∨ S={4} ∨ S={0,4} ∨ S={1,4} ∨ S={0,1,4} ∨ S={2,4} ∨ S={0,2,4} ∨ S={1,2,4} ∨ S={0,1,2,4} ∨ S={3,4} ∨ S={0,3,4} ∨ S={1,3,4} ∨ S={0,1,3,4} ∨ S={2,3,4} ∨ S={0,2,3,4} ∨ S={1,2,3,4} ∨ S={0,1,2,3,4} := by decide
  rcases casesS S with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem empty_zero : integerFunction ∅=0 := by decide

theorem singleton_zero : ∀ v : Fin 5,integerFunction {v}=0 := by decide

theorem boolean_differences : ∀ u v : Fin 5,u≠ v → ∀ S : Finset (Fin 5),
    u∉S → v∉S → integerDelta integerFunction u v S=0 ∨
      integerDelta integerFunction u v S=1 := by decide

theorem extreme : ExtremeSupermodular (realFunction integerFunction) :=
  extreme_of_row_kernel integerFunction rows pivot pivot_one row_zero valid_rows
    row_kernel_zero empty_zero singleton_zero boolean_differences

end K1112Complement

namespace K1122

def integerFunction (S : Finset (Fin 6)) : ℤ :=
  (match subsetMask S with
  | 3 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 3
  | 9 => 1
  | 10 => 1
  | 11 => 2
  | 13 => 2
  | 14 => 2
  | 15 => 4
  | 17 => 1
  | 18 => 1
  | 19 => 3
  | 20 => 1
  | 21 => 3
  | 22 => 3
  | 23 => 5
  | 24 => 1
  | 25 => 2
  | 26 => 2
  | 27 => 4
  | 28 => 2
  | 29 => 4
  | 30 => 4
  | 31 => 6
  | 33 => 1
  | 34 => 1
  | 35 => 2
  | 36 => 1
  | 37 => 2
  | 38 => 2
  | 39 => 4
  | 41 => 2
  | 42 => 2
  | 43 => 4
  | 44 => 1
  | 45 => 3
  | 46 => 3
  | 47 => 6
  | 49 => 2
  | 50 => 2
  | 51 => 4
  | 52 => 2
  | 53 => 4
  | 54 => 4
  | 55 => 6
  | 56 => 1
  | 57 => 3
  | 58 => 3
  | 59 => 6
  | 60 => 3
  | 61 => 5
  | 62 => 5
  | 63 => 8
  | _ => 0)

def rows : Fin 64 → Row (Fin 6) :=
  ![.value {0,1},.value ∅,.value {0},.value {1},.value {2},.value {3},.value {4},.value {5},.elemental 0 1 {3},.elemental 0 1 {2,3},.elemental 0 1 {2,4},.elemental 0 1 {2,3,4},.elemental 0 1 {5},.elemental 0 1 {3,5},.elemental 0 1 {4,5},.elemental 0 1 {2,4,5},.elemental 0 2 {1,4},.elemental 0 2 {1,3,4},.elemental 0 2 {5},.elemental 0 2 {3,5},.elemental 0 2 {4,5},.elemental 0 2 {3,4,5},.elemental 0 2 {1,3,4,5},.elemental 0 3 {1},.elemental 0 3 {1,2},.elemental 0 3 {4},.elemental 0 3 {1,4},.elemental 0 3 {4,5},.elemental 0 4 {1,2},.elemental 0 4 {3},.elemental 0 4 {1,2,5},.elemental 0 4 {3,5},.elemental 0 4 {1,2,3,5},.elemental 0 5 {1},.elemental 0 5 {2},.elemental 0 5 {1,2},.elemental 1 2 {0,4},.elemental 1 2 {0,3,4},.elemental 1 2 {5},.elemental 1 2 {3,5},.elemental 1 2 {4,5},.elemental 1 2 {3,4,5},.elemental 1 3 {0},.elemental 1 3 {0,2},.elemental 1 3 {4},.elemental 1 3 {4,5},.elemental 1 4 {0,2},.elemental 1 4 {3},.elemental 1 4 {0,2,5},.elemental 1 4 {3,5},.elemental 1 5 {0},.elemental 2 3 ∅,.elemental 2 3 {0},.elemental 2 3 {4},.elemental 2 3 {5},.elemental 2 3 {0,1,5},.elemental 2 3 {4,5},.elemental 2 4 {0,1},.elemental 2 4 {0,1,5},.elemental 2 5 {0},.elemental 3 4 {0},.elemental 3 4 {0,5},.elemental 3 5 ∅,.elemental 4 5 ∅]

def pivot : Finset (Fin 6) := {0,1}

theorem pivot_one : integerFunction pivot=1 := by decide

theorem row_zero : rows 0=.value pivot := by decide

theorem valid_rows : ∀ i : Fin 64,i≠0 → (rows i).valid integerFunction := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 4096 in
theorem row_kernel_zero (f : SetFunction (Fin 6))
    (hf : ∀ i : Fin 64,(rows i).eval f=0) : f=0 := by
  have h0 : f {0,1}=0 := hf 0
  have h1 : f ∅=0 := hf 1
  have h2 : f {0}=0 := hf 2
  have h3 : f {1}=0 := hf 3
  have h4 : f {2}=0 := hf 4
  have h5 : f {3}=0 := hf 5
  have h6 : f {4}=0 := hf 6
  have h7 : f {5}=0 := hf 7
  have h8 : f {0,1,3}-f {0,3}-f {1,3}+f {3}=0 := by
    have h := hf 8
    change f (insert 0 (insert 1 ({3} : Finset (Fin 6))))-
      f (insert 0 ({3} : Finset (Fin 6)))-f (insert 1 ({3} : Finset (Fin 6)))+f {3}=0 at h
    have hAB : insert 0 (insert 1 ({3} : Finset (Fin 6)))={0,1,3} := by decide
    have hA : insert 0 ({3} : Finset (Fin 6))={0,3} := by decide
    have hB : insert 1 ({3} : Finset (Fin 6))={1,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h9 : f {0,1,2,3}-f {0,2,3}-f {1,2,3}+f {2,3}=0 := by
    have h := hf 9
    change f (insert 0 (insert 1 ({2,3} : Finset (Fin 6))))-
      f (insert 0 ({2,3} : Finset (Fin 6)))-f (insert 1 ({2,3} : Finset (Fin 6)))+f {2,3}=0 at h
    have hAB : insert 0 (insert 1 ({2,3} : Finset (Fin 6)))={0,1,2,3} := by decide
    have hA : insert 0 ({2,3} : Finset (Fin 6))={0,2,3} := by decide
    have hB : insert 1 ({2,3} : Finset (Fin 6))={1,2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h10 : f {0,1,2,4}-f {0,2,4}-f {1,2,4}+f {2,4}=0 := by
    have h := hf 10
    change f (insert 0 (insert 1 ({2,4} : Finset (Fin 6))))-
      f (insert 0 ({2,4} : Finset (Fin 6)))-f (insert 1 ({2,4} : Finset (Fin 6)))+f {2,4}=0 at h
    have hAB : insert 0 (insert 1 ({2,4} : Finset (Fin 6)))={0,1,2,4} := by decide
    have hA : insert 0 ({2,4} : Finset (Fin 6))={0,2,4} := by decide
    have hB : insert 1 ({2,4} : Finset (Fin 6))={1,2,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h11 : f {0,1,2,3,4}-f {0,2,3,4}-f {1,2,3,4}+f {2,3,4}=0 := by
    have h := hf 11
    change f (insert 0 (insert 1 ({2,3,4} : Finset (Fin 6))))-
      f (insert 0 ({2,3,4} : Finset (Fin 6)))-f (insert 1 ({2,3,4} : Finset (Fin 6)))+f {2,3,4}=0 at h
    have hAB : insert 0 (insert 1 ({2,3,4} : Finset (Fin 6)))={0,1,2,3,4} := by decide
    have hA : insert 0 ({2,3,4} : Finset (Fin 6))={0,2,3,4} := by decide
    have hB : insert 1 ({2,3,4} : Finset (Fin 6))={1,2,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h12 : f {0,1,5}-f {0,5}-f {1,5}+f {5}=0 := by
    have h := hf 12
    change f (insert 0 (insert 1 ({5} : Finset (Fin 6))))-
      f (insert 0 ({5} : Finset (Fin 6)))-f (insert 1 ({5} : Finset (Fin 6)))+f {5}=0 at h
    have hAB : insert 0 (insert 1 ({5} : Finset (Fin 6)))={0,1,5} := by decide
    have hA : insert 0 ({5} : Finset (Fin 6))={0,5} := by decide
    have hB : insert 1 ({5} : Finset (Fin 6))={1,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h13 : f {0,1,3,5}-f {0,3,5}-f {1,3,5}+f {3,5}=0 := by
    have h := hf 13
    change f (insert 0 (insert 1 ({3,5} : Finset (Fin 6))))-
      f (insert 0 ({3,5} : Finset (Fin 6)))-f (insert 1 ({3,5} : Finset (Fin 6)))+f {3,5}=0 at h
    have hAB : insert 0 (insert 1 ({3,5} : Finset (Fin 6)))={0,1,3,5} := by decide
    have hA : insert 0 ({3,5} : Finset (Fin 6))={0,3,5} := by decide
    have hB : insert 1 ({3,5} : Finset (Fin 6))={1,3,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h14 : f {0,1,4,5}-f {0,4,5}-f {1,4,5}+f {4,5}=0 := by
    have h := hf 14
    change f (insert 0 (insert 1 ({4,5} : Finset (Fin 6))))-
      f (insert 0 ({4,5} : Finset (Fin 6)))-f (insert 1 ({4,5} : Finset (Fin 6)))+f {4,5}=0 at h
    have hAB : insert 0 (insert 1 ({4,5} : Finset (Fin 6)))={0,1,4,5} := by decide
    have hA : insert 0 ({4,5} : Finset (Fin 6))={0,4,5} := by decide
    have hB : insert 1 ({4,5} : Finset (Fin 6))={1,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h15 : f {0,1,2,4,5}-f {0,2,4,5}-f {1,2,4,5}+f {2,4,5}=0 := by
    have h := hf 15
    change f (insert 0 (insert 1 ({2,4,5} : Finset (Fin 6))))-
      f (insert 0 ({2,4,5} : Finset (Fin 6)))-f (insert 1 ({2,4,5} : Finset (Fin 6)))+f {2,4,5}=0 at h
    have hAB : insert 0 (insert 1 ({2,4,5} : Finset (Fin 6)))={0,1,2,4,5} := by decide
    have hA : insert 0 ({2,4,5} : Finset (Fin 6))={0,2,4,5} := by decide
    have hB : insert 1 ({2,4,5} : Finset (Fin 6))={1,2,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h16 : f {0,1,2,4}-f {0,1,4}-f {1,2,4}+f {1,4}=0 := by
    have h := hf 16
    change f (insert 0 (insert 2 ({1,4} : Finset (Fin 6))))-
      f (insert 0 ({1,4} : Finset (Fin 6)))-f (insert 2 ({1,4} : Finset (Fin 6)))+f {1,4}=0 at h
    have hAB : insert 0 (insert 2 ({1,4} : Finset (Fin 6)))={0,1,2,4} := by decide
    have hA : insert 0 ({1,4} : Finset (Fin 6))={0,1,4} := by decide
    have hB : insert 2 ({1,4} : Finset (Fin 6))={1,2,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h17 : f {0,1,2,3,4}-f {0,1,3,4}-f {1,2,3,4}+f {1,3,4}=0 := by
    have h := hf 17
    change f (insert 0 (insert 2 ({1,3,4} : Finset (Fin 6))))-
      f (insert 0 ({1,3,4} : Finset (Fin 6)))-f (insert 2 ({1,3,4} : Finset (Fin 6)))+f {1,3,4}=0 at h
    have hAB : insert 0 (insert 2 ({1,3,4} : Finset (Fin 6)))={0,1,2,3,4} := by decide
    have hA : insert 0 ({1,3,4} : Finset (Fin 6))={0,1,3,4} := by decide
    have hB : insert 2 ({1,3,4} : Finset (Fin 6))={1,2,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h18 : f {0,2,5}-f {0,5}-f {2,5}+f {5}=0 := by
    have h := hf 18
    change f (insert 0 (insert 2 ({5} : Finset (Fin 6))))-
      f (insert 0 ({5} : Finset (Fin 6)))-f (insert 2 ({5} : Finset (Fin 6)))+f {5}=0 at h
    have hAB : insert 0 (insert 2 ({5} : Finset (Fin 6)))={0,2,5} := by decide
    have hA : insert 0 ({5} : Finset (Fin 6))={0,5} := by decide
    have hB : insert 2 ({5} : Finset (Fin 6))={2,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h19 : f {0,2,3,5}-f {0,3,5}-f {2,3,5}+f {3,5}=0 := by
    have h := hf 19
    change f (insert 0 (insert 2 ({3,5} : Finset (Fin 6))))-
      f (insert 0 ({3,5} : Finset (Fin 6)))-f (insert 2 ({3,5} : Finset (Fin 6)))+f {3,5}=0 at h
    have hAB : insert 0 (insert 2 ({3,5} : Finset (Fin 6)))={0,2,3,5} := by decide
    have hA : insert 0 ({3,5} : Finset (Fin 6))={0,3,5} := by decide
    have hB : insert 2 ({3,5} : Finset (Fin 6))={2,3,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h20 : f {0,2,4,5}-f {0,4,5}-f {2,4,5}+f {4,5}=0 := by
    have h := hf 20
    change f (insert 0 (insert 2 ({4,5} : Finset (Fin 6))))-
      f (insert 0 ({4,5} : Finset (Fin 6)))-f (insert 2 ({4,5} : Finset (Fin 6)))+f {4,5}=0 at h
    have hAB : insert 0 (insert 2 ({4,5} : Finset (Fin 6)))={0,2,4,5} := by decide
    have hA : insert 0 ({4,5} : Finset (Fin 6))={0,4,5} := by decide
    have hB : insert 2 ({4,5} : Finset (Fin 6))={2,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h21 : f {0,2,3,4,5}-f {0,3,4,5}-f {2,3,4,5}+f {3,4,5}=0 := by
    have h := hf 21
    change f (insert 0 (insert 2 ({3,4,5} : Finset (Fin 6))))-
      f (insert 0 ({3,4,5} : Finset (Fin 6)))-f (insert 2 ({3,4,5} : Finset (Fin 6)))+f {3,4,5}=0 at h
    have hAB : insert 0 (insert 2 ({3,4,5} : Finset (Fin 6)))={0,2,3,4,5} := by decide
    have hA : insert 0 ({3,4,5} : Finset (Fin 6))={0,3,4,5} := by decide
    have hB : insert 2 ({3,4,5} : Finset (Fin 6))={2,3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h22 : f {0,1,2,3,4,5}-f {0,1,3,4,5}-f {1,2,3,4,5}+f {1,3,4,5}=0 := by
    have h := hf 22
    change f (insert 0 (insert 2 ({1,3,4,5} : Finset (Fin 6))))-
      f (insert 0 ({1,3,4,5} : Finset (Fin 6)))-f (insert 2 ({1,3,4,5} : Finset (Fin 6)))+f {1,3,4,5}=0 at h
    have hAB : insert 0 (insert 2 ({1,3,4,5} : Finset (Fin 6)))={0,1,2,3,4,5} := by decide
    have hA : insert 0 ({1,3,4,5} : Finset (Fin 6))={0,1,3,4,5} := by decide
    have hB : insert 2 ({1,3,4,5} : Finset (Fin 6))={1,2,3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h23 : f {0,1,3}-f {0,1}-f {1,3}+f {1}=0 := by
    have h := hf 23
    change f (insert 0 (insert 3 ({1} : Finset (Fin 6))))-
      f (insert 0 ({1} : Finset (Fin 6)))-f (insert 3 ({1} : Finset (Fin 6)))+f {1}=0 at h
    have hAB : insert 0 (insert 3 ({1} : Finset (Fin 6)))={0,1,3} := by decide
    have hA : insert 0 ({1} : Finset (Fin 6))={0,1} := by decide
    have hB : insert 3 ({1} : Finset (Fin 6))={1,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h24 : f {0,1,2,3}-f {0,1,2}-f {1,2,3}+f {1,2}=0 := by
    have h := hf 24
    change f (insert 0 (insert 3 ({1,2} : Finset (Fin 6))))-
      f (insert 0 ({1,2} : Finset (Fin 6)))-f (insert 3 ({1,2} : Finset (Fin 6)))+f {1,2}=0 at h
    have hAB : insert 0 (insert 3 ({1,2} : Finset (Fin 6)))={0,1,2,3} := by decide
    have hA : insert 0 ({1,2} : Finset (Fin 6))={0,1,2} := by decide
    have hB : insert 3 ({1,2} : Finset (Fin 6))={1,2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h25 : f {0,3,4}-f {0,4}-f {3,4}+f {4}=0 := by
    have h := hf 25
    change f (insert 0 (insert 3 ({4} : Finset (Fin 6))))-
      f (insert 0 ({4} : Finset (Fin 6)))-f (insert 3 ({4} : Finset (Fin 6)))+f {4}=0 at h
    have hAB : insert 0 (insert 3 ({4} : Finset (Fin 6)))={0,3,4} := by decide
    have hA : insert 0 ({4} : Finset (Fin 6))={0,4} := by decide
    have hB : insert 3 ({4} : Finset (Fin 6))={3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h26 : f {0,1,3,4}-f {0,1,4}-f {1,3,4}+f {1,4}=0 := by
    have h := hf 26
    change f (insert 0 (insert 3 ({1,4} : Finset (Fin 6))))-
      f (insert 0 ({1,4} : Finset (Fin 6)))-f (insert 3 ({1,4} : Finset (Fin 6)))+f {1,4}=0 at h
    have hAB : insert 0 (insert 3 ({1,4} : Finset (Fin 6)))={0,1,3,4} := by decide
    have hA : insert 0 ({1,4} : Finset (Fin 6))={0,1,4} := by decide
    have hB : insert 3 ({1,4} : Finset (Fin 6))={1,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h27 : f {0,3,4,5}-f {0,4,5}-f {3,4,5}+f {4,5}=0 := by
    have h := hf 27
    change f (insert 0 (insert 3 ({4,5} : Finset (Fin 6))))-
      f (insert 0 ({4,5} : Finset (Fin 6)))-f (insert 3 ({4,5} : Finset (Fin 6)))+f {4,5}=0 at h
    have hAB : insert 0 (insert 3 ({4,5} : Finset (Fin 6)))={0,3,4,5} := by decide
    have hA : insert 0 ({4,5} : Finset (Fin 6))={0,4,5} := by decide
    have hB : insert 3 ({4,5} : Finset (Fin 6))={3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h28 : f {0,1,2,4}-f {0,1,2}-f {1,2,4}+f {1,2}=0 := by
    have h := hf 28
    change f (insert 0 (insert 4 ({1,2} : Finset (Fin 6))))-
      f (insert 0 ({1,2} : Finset (Fin 6)))-f (insert 4 ({1,2} : Finset (Fin 6)))+f {1,2}=0 at h
    have hAB : insert 0 (insert 4 ({1,2} : Finset (Fin 6)))={0,1,2,4} := by decide
    have hA : insert 0 ({1,2} : Finset (Fin 6))={0,1,2} := by decide
    have hB : insert 4 ({1,2} : Finset (Fin 6))={1,2,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h29 : f {0,3,4}-f {0,3}-f {3,4}+f {3}=0 := by
    have h := hf 29
    change f (insert 0 (insert 4 ({3} : Finset (Fin 6))))-
      f (insert 0 ({3} : Finset (Fin 6)))-f (insert 4 ({3} : Finset (Fin 6)))+f {3}=0 at h
    have hAB : insert 0 (insert 4 ({3} : Finset (Fin 6)))={0,3,4} := by decide
    have hA : insert 0 ({3} : Finset (Fin 6))={0,3} := by decide
    have hB : insert 4 ({3} : Finset (Fin 6))={3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h30 : f {0,1,2,4,5}-f {0,1,2,5}-f {1,2,4,5}+f {1,2,5}=0 := by
    have h := hf 30
    change f (insert 0 (insert 4 ({1,2,5} : Finset (Fin 6))))-
      f (insert 0 ({1,2,5} : Finset (Fin 6)))-f (insert 4 ({1,2,5} : Finset (Fin 6)))+f {1,2,5}=0 at h
    have hAB : insert 0 (insert 4 ({1,2,5} : Finset (Fin 6)))={0,1,2,4,5} := by decide
    have hA : insert 0 ({1,2,5} : Finset (Fin 6))={0,1,2,5} := by decide
    have hB : insert 4 ({1,2,5} : Finset (Fin 6))={1,2,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h31 : f {0,3,4,5}-f {0,3,5}-f {3,4,5}+f {3,5}=0 := by
    have h := hf 31
    change f (insert 0 (insert 4 ({3,5} : Finset (Fin 6))))-
      f (insert 0 ({3,5} : Finset (Fin 6)))-f (insert 4 ({3,5} : Finset (Fin 6)))+f {3,5}=0 at h
    have hAB : insert 0 (insert 4 ({3,5} : Finset (Fin 6)))={0,3,4,5} := by decide
    have hA : insert 0 ({3,5} : Finset (Fin 6))={0,3,5} := by decide
    have hB : insert 4 ({3,5} : Finset (Fin 6))={3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h32 : f {0,1,2,3,4,5}-f {0,1,2,3,5}-f {1,2,3,4,5}+f {1,2,3,5}=0 := by
    have h := hf 32
    change f (insert 0 (insert 4 ({1,2,3,5} : Finset (Fin 6))))-
      f (insert 0 ({1,2,3,5} : Finset (Fin 6)))-f (insert 4 ({1,2,3,5} : Finset (Fin 6)))+f {1,2,3,5}=0 at h
    have hAB : insert 0 (insert 4 ({1,2,3,5} : Finset (Fin 6)))={0,1,2,3,4,5} := by decide
    have hA : insert 0 ({1,2,3,5} : Finset (Fin 6))={0,1,2,3,5} := by decide
    have hB : insert 4 ({1,2,3,5} : Finset (Fin 6))={1,2,3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h33 : f {0,1,5}-f {0,1}-f {1,5}+f {1}=0 := by
    have h := hf 33
    change f (insert 0 (insert 5 ({1} : Finset (Fin 6))))-
      f (insert 0 ({1} : Finset (Fin 6)))-f (insert 5 ({1} : Finset (Fin 6)))+f {1}=0 at h
    have hAB : insert 0 (insert 5 ({1} : Finset (Fin 6)))={0,1,5} := by decide
    have hA : insert 0 ({1} : Finset (Fin 6))={0,1} := by decide
    have hB : insert 5 ({1} : Finset (Fin 6))={1,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h34 : f {0,2,5}-f {0,2}-f {2,5}+f {2}=0 := by
    have h := hf 34
    change f (insert 0 (insert 5 ({2} : Finset (Fin 6))))-
      f (insert 0 ({2} : Finset (Fin 6)))-f (insert 5 ({2} : Finset (Fin 6)))+f {2}=0 at h
    have hAB : insert 0 (insert 5 ({2} : Finset (Fin 6)))={0,2,5} := by decide
    have hA : insert 0 ({2} : Finset (Fin 6))={0,2} := by decide
    have hB : insert 5 ({2} : Finset (Fin 6))={2,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h35 : f {0,1,2,5}-f {0,1,2}-f {1,2,5}+f {1,2}=0 := by
    have h := hf 35
    change f (insert 0 (insert 5 ({1,2} : Finset (Fin 6))))-
      f (insert 0 ({1,2} : Finset (Fin 6)))-f (insert 5 ({1,2} : Finset (Fin 6)))+f {1,2}=0 at h
    have hAB : insert 0 (insert 5 ({1,2} : Finset (Fin 6)))={0,1,2,5} := by decide
    have hA : insert 0 ({1,2} : Finset (Fin 6))={0,1,2} := by decide
    have hB : insert 5 ({1,2} : Finset (Fin 6))={1,2,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h36 : f {0,1,2,4}-f {0,1,4}-f {0,2,4}+f {0,4}=0 := by
    have h := hf 36
    change f (insert 1 (insert 2 ({0,4} : Finset (Fin 6))))-
      f (insert 1 ({0,4} : Finset (Fin 6)))-f (insert 2 ({0,4} : Finset (Fin 6)))+f {0,4}=0 at h
    have hAB : insert 1 (insert 2 ({0,4} : Finset (Fin 6)))={0,1,2,4} := by decide
    have hA : insert 1 ({0,4} : Finset (Fin 6))={0,1,4} := by decide
    have hB : insert 2 ({0,4} : Finset (Fin 6))={0,2,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h37 : f {0,1,2,3,4}-f {0,1,3,4}-f {0,2,3,4}+f {0,3,4}=0 := by
    have h := hf 37
    change f (insert 1 (insert 2 ({0,3,4} : Finset (Fin 6))))-
      f (insert 1 ({0,3,4} : Finset (Fin 6)))-f (insert 2 ({0,3,4} : Finset (Fin 6)))+f {0,3,4}=0 at h
    have hAB : insert 1 (insert 2 ({0,3,4} : Finset (Fin 6)))={0,1,2,3,4} := by decide
    have hA : insert 1 ({0,3,4} : Finset (Fin 6))={0,1,3,4} := by decide
    have hB : insert 2 ({0,3,4} : Finset (Fin 6))={0,2,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h38 : f {1,2,5}-f {1,5}-f {2,5}+f {5}=0 := by
    have h := hf 38
    change f (insert 1 (insert 2 ({5} : Finset (Fin 6))))-
      f (insert 1 ({5} : Finset (Fin 6)))-f (insert 2 ({5} : Finset (Fin 6)))+f {5}=0 at h
    have hAB : insert 1 (insert 2 ({5} : Finset (Fin 6)))={1,2,5} := by decide
    have hA : insert 1 ({5} : Finset (Fin 6))={1,5} := by decide
    have hB : insert 2 ({5} : Finset (Fin 6))={2,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h39 : f {1,2,3,5}-f {1,3,5}-f {2,3,5}+f {3,5}=0 := by
    have h := hf 39
    change f (insert 1 (insert 2 ({3,5} : Finset (Fin 6))))-
      f (insert 1 ({3,5} : Finset (Fin 6)))-f (insert 2 ({3,5} : Finset (Fin 6)))+f {3,5}=0 at h
    have hAB : insert 1 (insert 2 ({3,5} : Finset (Fin 6)))={1,2,3,5} := by decide
    have hA : insert 1 ({3,5} : Finset (Fin 6))={1,3,5} := by decide
    have hB : insert 2 ({3,5} : Finset (Fin 6))={2,3,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h40 : f {1,2,4,5}-f {1,4,5}-f {2,4,5}+f {4,5}=0 := by
    have h := hf 40
    change f (insert 1 (insert 2 ({4,5} : Finset (Fin 6))))-
      f (insert 1 ({4,5} : Finset (Fin 6)))-f (insert 2 ({4,5} : Finset (Fin 6)))+f {4,5}=0 at h
    have hAB : insert 1 (insert 2 ({4,5} : Finset (Fin 6)))={1,2,4,5} := by decide
    have hA : insert 1 ({4,5} : Finset (Fin 6))={1,4,5} := by decide
    have hB : insert 2 ({4,5} : Finset (Fin 6))={2,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h41 : f {1,2,3,4,5}-f {1,3,4,5}-f {2,3,4,5}+f {3,4,5}=0 := by
    have h := hf 41
    change f (insert 1 (insert 2 ({3,4,5} : Finset (Fin 6))))-
      f (insert 1 ({3,4,5} : Finset (Fin 6)))-f (insert 2 ({3,4,5} : Finset (Fin 6)))+f {3,4,5}=0 at h
    have hAB : insert 1 (insert 2 ({3,4,5} : Finset (Fin 6)))={1,2,3,4,5} := by decide
    have hA : insert 1 ({3,4,5} : Finset (Fin 6))={1,3,4,5} := by decide
    have hB : insert 2 ({3,4,5} : Finset (Fin 6))={2,3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h42 : f {0,1,3}-f {0,1}-f {0,3}+f {0}=0 := by
    have h := hf 42
    change f (insert 1 (insert 3 ({0} : Finset (Fin 6))))-
      f (insert 1 ({0} : Finset (Fin 6)))-f (insert 3 ({0} : Finset (Fin 6)))+f {0}=0 at h
    have hAB : insert 1 (insert 3 ({0} : Finset (Fin 6)))={0,1,3} := by decide
    have hA : insert 1 ({0} : Finset (Fin 6))={0,1} := by decide
    have hB : insert 3 ({0} : Finset (Fin 6))={0,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h43 : f {0,1,2,3}-f {0,1,2}-f {0,2,3}+f {0,2}=0 := by
    have h := hf 43
    change f (insert 1 (insert 3 ({0,2} : Finset (Fin 6))))-
      f (insert 1 ({0,2} : Finset (Fin 6)))-f (insert 3 ({0,2} : Finset (Fin 6)))+f {0,2}=0 at h
    have hAB : insert 1 (insert 3 ({0,2} : Finset (Fin 6)))={0,1,2,3} := by decide
    have hA : insert 1 ({0,2} : Finset (Fin 6))={0,1,2} := by decide
    have hB : insert 3 ({0,2} : Finset (Fin 6))={0,2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h44 : f {1,3,4}-f {1,4}-f {3,4}+f {4}=0 := by
    have h := hf 44
    change f (insert 1 (insert 3 ({4} : Finset (Fin 6))))-
      f (insert 1 ({4} : Finset (Fin 6)))-f (insert 3 ({4} : Finset (Fin 6)))+f {4}=0 at h
    have hAB : insert 1 (insert 3 ({4} : Finset (Fin 6)))={1,3,4} := by decide
    have hA : insert 1 ({4} : Finset (Fin 6))={1,4} := by decide
    have hB : insert 3 ({4} : Finset (Fin 6))={3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h45 : f {1,3,4,5}-f {1,4,5}-f {3,4,5}+f {4,5}=0 := by
    have h := hf 45
    change f (insert 1 (insert 3 ({4,5} : Finset (Fin 6))))-
      f (insert 1 ({4,5} : Finset (Fin 6)))-f (insert 3 ({4,5} : Finset (Fin 6)))+f {4,5}=0 at h
    have hAB : insert 1 (insert 3 ({4,5} : Finset (Fin 6)))={1,3,4,5} := by decide
    have hA : insert 1 ({4,5} : Finset (Fin 6))={1,4,5} := by decide
    have hB : insert 3 ({4,5} : Finset (Fin 6))={3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h46 : f {0,1,2,4}-f {0,1,2}-f {0,2,4}+f {0,2}=0 := by
    have h := hf 46
    change f (insert 1 (insert 4 ({0,2} : Finset (Fin 6))))-
      f (insert 1 ({0,2} : Finset (Fin 6)))-f (insert 4 ({0,2} : Finset (Fin 6)))+f {0,2}=0 at h
    have hAB : insert 1 (insert 4 ({0,2} : Finset (Fin 6)))={0,1,2,4} := by decide
    have hA : insert 1 ({0,2} : Finset (Fin 6))={0,1,2} := by decide
    have hB : insert 4 ({0,2} : Finset (Fin 6))={0,2,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h47 : f {1,3,4}-f {1,3}-f {3,4}+f {3}=0 := by
    have h := hf 47
    change f (insert 1 (insert 4 ({3} : Finset (Fin 6))))-
      f (insert 1 ({3} : Finset (Fin 6)))-f (insert 4 ({3} : Finset (Fin 6)))+f {3}=0 at h
    have hAB : insert 1 (insert 4 ({3} : Finset (Fin 6)))={1,3,4} := by decide
    have hA : insert 1 ({3} : Finset (Fin 6))={1,3} := by decide
    have hB : insert 4 ({3} : Finset (Fin 6))={3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h48 : f {0,1,2,4,5}-f {0,1,2,5}-f {0,2,4,5}+f {0,2,5}=0 := by
    have h := hf 48
    change f (insert 1 (insert 4 ({0,2,5} : Finset (Fin 6))))-
      f (insert 1 ({0,2,5} : Finset (Fin 6)))-f (insert 4 ({0,2,5} : Finset (Fin 6)))+f {0,2,5}=0 at h
    have hAB : insert 1 (insert 4 ({0,2,5} : Finset (Fin 6)))={0,1,2,4,5} := by decide
    have hA : insert 1 ({0,2,5} : Finset (Fin 6))={0,1,2,5} := by decide
    have hB : insert 4 ({0,2,5} : Finset (Fin 6))={0,2,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h49 : f {1,3,4,5}-f {1,3,5}-f {3,4,5}+f {3,5}=0 := by
    have h := hf 49
    change f (insert 1 (insert 4 ({3,5} : Finset (Fin 6))))-
      f (insert 1 ({3,5} : Finset (Fin 6)))-f (insert 4 ({3,5} : Finset (Fin 6)))+f {3,5}=0 at h
    have hAB : insert 1 (insert 4 ({3,5} : Finset (Fin 6)))={1,3,4,5} := by decide
    have hA : insert 1 ({3,5} : Finset (Fin 6))={1,3,5} := by decide
    have hB : insert 4 ({3,5} : Finset (Fin 6))={3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h50 : f {0,1,5}-f {0,1}-f {0,5}+f {0}=0 := by
    have h := hf 50
    change f (insert 1 (insert 5 ({0} : Finset (Fin 6))))-
      f (insert 1 ({0} : Finset (Fin 6)))-f (insert 5 ({0} : Finset (Fin 6)))+f {0}=0 at h
    have hAB : insert 1 (insert 5 ({0} : Finset (Fin 6)))={0,1,5} := by decide
    have hA : insert 1 ({0} : Finset (Fin 6))={0,1} := by decide
    have hB : insert 5 ({0} : Finset (Fin 6))={0,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h51 : f {2,3}-f {2}-f {3}+f ∅=0 := by
    have h := hf 51
    change f (insert 2 (insert 3 (∅ : Finset (Fin 6))))-
      f (insert 2 (∅ : Finset (Fin 6)))-f (insert 3 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 2 (insert 3 (∅ : Finset (Fin 6)))={2,3} := by decide
    have hA : insert 2 (∅ : Finset (Fin 6))={2} := by decide
    have hB : insert 3 (∅ : Finset (Fin 6))={3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h52 : f {0,2,3}-f {0,2}-f {0,3}+f {0}=0 := by
    have h := hf 52
    change f (insert 2 (insert 3 ({0} : Finset (Fin 6))))-
      f (insert 2 ({0} : Finset (Fin 6)))-f (insert 3 ({0} : Finset (Fin 6)))+f {0}=0 at h
    have hAB : insert 2 (insert 3 ({0} : Finset (Fin 6)))={0,2,3} := by decide
    have hA : insert 2 ({0} : Finset (Fin 6))={0,2} := by decide
    have hB : insert 3 ({0} : Finset (Fin 6))={0,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h53 : f {2,3,4}-f {2,4}-f {3,4}+f {4}=0 := by
    have h := hf 53
    change f (insert 2 (insert 3 ({4} : Finset (Fin 6))))-
      f (insert 2 ({4} : Finset (Fin 6)))-f (insert 3 ({4} : Finset (Fin 6)))+f {4}=0 at h
    have hAB : insert 2 (insert 3 ({4} : Finset (Fin 6)))={2,3,4} := by decide
    have hA : insert 2 ({4} : Finset (Fin 6))={2,4} := by decide
    have hB : insert 3 ({4} : Finset (Fin 6))={3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h54 : f {2,3,5}-f {2,5}-f {3,5}+f {5}=0 := by
    have h := hf 54
    change f (insert 2 (insert 3 ({5} : Finset (Fin 6))))-
      f (insert 2 ({5} : Finset (Fin 6)))-f (insert 3 ({5} : Finset (Fin 6)))+f {5}=0 at h
    have hAB : insert 2 (insert 3 ({5} : Finset (Fin 6)))={2,3,5} := by decide
    have hA : insert 2 ({5} : Finset (Fin 6))={2,5} := by decide
    have hB : insert 3 ({5} : Finset (Fin 6))={3,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h55 : f {0,1,2,3,5}-f {0,1,2,5}-f {0,1,3,5}+f {0,1,5}=0 := by
    have h := hf 55
    change f (insert 2 (insert 3 ({0,1,5} : Finset (Fin 6))))-
      f (insert 2 ({0,1,5} : Finset (Fin 6)))-f (insert 3 ({0,1,5} : Finset (Fin 6)))+f {0,1,5}=0 at h
    have hAB : insert 2 (insert 3 ({0,1,5} : Finset (Fin 6)))={0,1,2,3,5} := by decide
    have hA : insert 2 ({0,1,5} : Finset (Fin 6))={0,1,2,5} := by decide
    have hB : insert 3 ({0,1,5} : Finset (Fin 6))={0,1,3,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h56 : f {2,3,4,5}-f {2,4,5}-f {3,4,5}+f {4,5}=0 := by
    have h := hf 56
    change f (insert 2 (insert 3 ({4,5} : Finset (Fin 6))))-
      f (insert 2 ({4,5} : Finset (Fin 6)))-f (insert 3 ({4,5} : Finset (Fin 6)))+f {4,5}=0 at h
    have hAB : insert 2 (insert 3 ({4,5} : Finset (Fin 6)))={2,3,4,5} := by decide
    have hA : insert 2 ({4,5} : Finset (Fin 6))={2,4,5} := by decide
    have hB : insert 3 ({4,5} : Finset (Fin 6))={3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h57 : f {0,1,2,4}-f {0,1,2}-f {0,1,4}+f {0,1}=0 := by
    have h := hf 57
    change f (insert 2 (insert 4 ({0,1} : Finset (Fin 6))))-
      f (insert 2 ({0,1} : Finset (Fin 6)))-f (insert 4 ({0,1} : Finset (Fin 6)))+f {0,1}=0 at h
    have hAB : insert 2 (insert 4 ({0,1} : Finset (Fin 6)))={0,1,2,4} := by decide
    have hA : insert 2 ({0,1} : Finset (Fin 6))={0,1,2} := by decide
    have hB : insert 4 ({0,1} : Finset (Fin 6))={0,1,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h58 : f {0,1,2,4,5}-f {0,1,2,5}-f {0,1,4,5}+f {0,1,5}=0 := by
    have h := hf 58
    change f (insert 2 (insert 4 ({0,1,5} : Finset (Fin 6))))-
      f (insert 2 ({0,1,5} : Finset (Fin 6)))-f (insert 4 ({0,1,5} : Finset (Fin 6)))+f {0,1,5}=0 at h
    have hAB : insert 2 (insert 4 ({0,1,5} : Finset (Fin 6)))={0,1,2,4,5} := by decide
    have hA : insert 2 ({0,1,5} : Finset (Fin 6))={0,1,2,5} := by decide
    have hB : insert 4 ({0,1,5} : Finset (Fin 6))={0,1,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h59 : f {0,2,5}-f {0,2}-f {0,5}+f {0}=0 := by
    have h := hf 59
    change f (insert 2 (insert 5 ({0} : Finset (Fin 6))))-
      f (insert 2 ({0} : Finset (Fin 6)))-f (insert 5 ({0} : Finset (Fin 6)))+f {0}=0 at h
    have hAB : insert 2 (insert 5 ({0} : Finset (Fin 6)))={0,2,5} := by decide
    have hA : insert 2 ({0} : Finset (Fin 6))={0,2} := by decide
    have hB : insert 5 ({0} : Finset (Fin 6))={0,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h60 : f {0,3,4}-f {0,3}-f {0,4}+f {0}=0 := by
    have h := hf 60
    change f (insert 3 (insert 4 ({0} : Finset (Fin 6))))-
      f (insert 3 ({0} : Finset (Fin 6)))-f (insert 4 ({0} : Finset (Fin 6)))+f {0}=0 at h
    have hAB : insert 3 (insert 4 ({0} : Finset (Fin 6)))={0,3,4} := by decide
    have hA : insert 3 ({0} : Finset (Fin 6))={0,3} := by decide
    have hB : insert 4 ({0} : Finset (Fin 6))={0,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h61 : f {0,3,4,5}-f {0,3,5}-f {0,4,5}+f {0,5}=0 := by
    have h := hf 61
    change f (insert 3 (insert 4 ({0,5} : Finset (Fin 6))))-
      f (insert 3 ({0,5} : Finset (Fin 6)))-f (insert 4 ({0,5} : Finset (Fin 6)))+f {0,5}=0 at h
    have hAB : insert 3 (insert 4 ({0,5} : Finset (Fin 6)))={0,3,4,5} := by decide
    have hA : insert 3 ({0,5} : Finset (Fin 6))={0,3,5} := by decide
    have hB : insert 4 ({0,5} : Finset (Fin 6))={0,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h62 : f {3,5}-f {3}-f {5}+f ∅=0 := by
    have h := hf 62
    change f (insert 3 (insert 5 (∅ : Finset (Fin 6))))-
      f (insert 3 (∅ : Finset (Fin 6)))-f (insert 5 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 3 (insert 5 (∅ : Finset (Fin 6)))={3,5} := by decide
    have hA : insert 3 (∅ : Finset (Fin 6))={3} := by decide
    have hB : insert 5 (∅ : Finset (Fin 6))={5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h63 : f {4,5}-f {4}-f {5}+f ∅=0 := by
    have h := hf 63
    change f (insert 4 (insert 5 (∅ : Finset (Fin 6))))-
      f (insert 4 (∅ : Finset (Fin 6)))-f (insert 5 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 4 (insert 5 (∅ : Finset (Fin 6)))={4,5} := by decide
    have hA : insert 4 (∅ : Finset (Fin 6))={4} := by decide
    have hB : insert 5 (∅ : Finset (Fin 6))={5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have v0 : f ∅=0 := by
    linear_combination h1
  have v1 : f {0}=0 := by
    linear_combination h2
  have v2 : f {1}=0 := by
    linear_combination h3
  have v3 : f {0,1}=0 := by
    linear_combination h0
  have v4 : f {2}=0 := by
    linear_combination h4
  have v5 : f {0,2}=0 := by
    linear_combination h0 + (-1) * h3 + h4 + (-1) * h12 + h18 + h33 + (-1) * h34
  have v6 : f {1,2}=0 := by
    linear_combination h0 + (-1) * h2 + h4 + (-1) * h12 + (-1) * h16 + h18 + (-1) * h23 + h25 + h28 + (-1) * h29 + h33 + (-1) * h34 + h36 + h42 + (-1) * h44 + (-1) * h46 + h47
  have v7 : f {0,1,2}=0 := by
    linear_combination (3) * h0 + h1 + (-2) * h2 + (-2) * h3 + h4 + (-1) * h8 + h9 + (-2) * h12 + (-1) * h16 + (2) * h18 + (-1) * h24 + h25 + h28 + (-1) * h29 + (2) * h33 + (-2) * h34 + h36 + h42 + (-1) * h44 + (-1) * h46 + h47 + (-1) * h51 + h52
  have v8 : f {3}=0 := by
    linear_combination h5
  have v9 : f {0,3}=0 := by
    linear_combination h0 + (-1) * h3 + h5 + (-1) * h8 + h23
  have v10 : f {1,3}=0 := by
    linear_combination h0 + (-1) * h2 + h5 + (-1) * h8 + h42
  have v11 : f {0,1,3}=0 := by
    linear_combination (2) * h0 + (-1) * h2 + (-1) * h3 + h5 + (-1) * h8 + h23 + h42
  have v12 : f {2,3}=0 := by
    linear_combination (-1) * h1 + h4 + h5 + h51
  have v13 : f {0,2,3}=0 := by
    linear_combination (2) * h0 + (-1) * h2 + (-2) * h3 + h4 + h5 + (-1) * h8 + (-1) * h12 + h18 + h23 + h33 + (-1) * h34 + h52
  have v14 : f {1,2,3}=0 := by
    linear_combination (2) * h0 + (-2) * h2 + (-1) * h3 + h4 + h5 + (-1) * h8 + (-1) * h12 + (-1) * h16 + h18 + (-1) * h24 + h25 + h28 + (-1) * h29 + h33 + (-1) * h34 + h36 + h42 + h43 + (-1) * h44 + (-1) * h46 + h47 + h52
  have v15 : f {0,1,2,3}=0 := by
    linear_combination (4) * h0 + h1 + (-3) * h2 + (-3) * h3 + h4 + h5 + (-2) * h8 + h9 + (-2) * h12 + (-1) * h16 + (2) * h18 + h23 + (-1) * h24 + h25 + h28 + (-1) * h29 + (2) * h33 + (-2) * h34 + h36 + h42 + h43 + (-1) * h44 + (-1) * h46 + h47 + (-1) * h51 + (2) * h52
  have v16 : f {4}=0 := by
    linear_combination h6
  have v17 : f {0,4}=0 := by
    linear_combination h0 + (-1) * h3 + h6 + (-1) * h8 + h23 + (-1) * h25 + h29
  have v18 : f {1,4}=0 := by
    linear_combination h0 + (-1) * h2 + h6 + (-1) * h8 + h42 + (-1) * h44 + h47
  have v19 : f {0,1,4}=0 := by
    linear_combination (3) * h0 + h1 + (-2) * h2 + (-2) * h3 + h6 + (-2) * h8 + h9 + (-1) * h12 + (-1) * h16 + h18 + h23 + (-1) * h24 + h28 + h33 + (-1) * h34 + h42 + (-1) * h44 + h47 + (-1) * h51 + h52
  have v20 : f {2,4}=0 := by
    linear_combination h0 + (-1) * h2 + (-1) * h3 + h4 + h6 + (-1) * h8 + h10 + (-1) * h12 + (-1) * h16 + h18 + h33 + (-1) * h34 + h42 + (-1) * h44 + (-1) * h46 + h47 + h57
  have v21 : f {0,2,4}=0 := by
    linear_combination (3) * h0 + h1 + (-2) * h2 + (-3) * h3 + h4 + h6 + (-2) * h8 + h9 + (-2) * h12 + (-1) * h16 + (2) * h18 + h23 + (-1) * h24 + h28 + (2) * h33 + (-2) * h34 + h42 + (-1) * h44 + (-1) * h46 + h47 + (-1) * h51 + h52 + h57
  have v22 : f {1,2,4}=0 := by
    linear_combination (3) * h0 + h1 + (-3) * h2 + (-2) * h3 + h4 + h6 + (-2) * h8 + h9 + (-2) * h12 + (-2) * h16 + (2) * h18 + (-1) * h24 + h25 + h28 + (-1) * h29 + (2) * h33 + (-2) * h34 + h36 + (2) * h42 + (-2) * h44 + (-1) * h46 + (2) * h47 + (-1) * h51 + h52 + h57
  have v23 : f {0,1,2,4}=0 := by
    linear_combination (5) * h0 + (2) * h1 + (-4) * h2 + (-4) * h3 + h4 + h6 + (-3) * h8 + (2) * h9 + (-3) * h12 + (-2) * h16 + (3) * h18 + h23 + (-2) * h24 + h25 + (2) * h28 + (-1) * h29 + (3) * h33 + (-3) * h34 + h36 + (2) * h42 + (-2) * h44 + (-1) * h46 + (2) * h47 + (-2) * h51 + (2) * h52 + h57
  have v24 : f {3,4}=0 := by
    linear_combination h0 + (-1) * h2 + (-1) * h3 + h5 + h6 + (-1) * h8 + h23 + (-1) * h25 + h60
  have v25 : f {0,3,4}=0 := by
    linear_combination (2) * h0 + (-1) * h2 + (-2) * h3 + h5 + h6 + (-2) * h8 + (2) * h23 + (-1) * h25 + h29 + h60
  have v26 : f {1,3,4}=0 := by
    linear_combination (2) * h0 + (-2) * h2 + (-1) * h3 + h5 + h6 + (-2) * h8 + h23 + (-1) * h25 + h42 + h47 + h60
  have v27 : f {0,1,3,4}=0 := by
    linear_combination (4) * h0 + h1 + (-3) * h2 + (-3) * h3 + h5 + h6 + (-3) * h8 + h9 + (-1) * h12 + (-1) * h16 + h18 + (2) * h23 + (-1) * h24 + (-1) * h25 + h26 + h28 + h33 + (-1) * h34 + h42 + h47 + (-1) * h51 + h52 + h60
  have v28 : f {2,3,4}=0 := by
    linear_combination (2) * h0 + (-2) * h2 + (-2) * h3 + h4 + h5 + h6 + (-2) * h8 + h10 + (-1) * h12 + (-1) * h16 + h18 + h23 + (-1) * h25 + h33 + (-1) * h34 + h42 + (-1) * h44 + (-1) * h46 + h47 + h53 + h57 + h60
  have v29 : f {0,2,3,4}=0 := by
    linear_combination (4) * h0 + h1 + (-3) * h2 + (-4) * h3 + h4 + h5 + h6 + (-3) * h8 + h9 + h10 + (-1) * h11 + (-2) * h12 + (-2) * h16 + h17 + (2) * h18 + (2) * h23 + (-1) * h24 + (-1) * h25 + h26 + h28 + (2) * h33 + (-2) * h34 + h42 + (-1) * h44 + (-1) * h46 + h47 + (-1) * h51 + h52 + h53 + h57 + h60
  have v30 : f {1,2,3,4}=0 := by
    linear_combination (4) * h0 + h1 + (-4) * h2 + (-3) * h3 + h4 + h5 + h6 + (-3) * h8 + h9 + h10 + (-1) * h11 + (-2) * h12 + (-2) * h16 + (2) * h18 + h23 + (-1) * h24 + (-1) * h25 + h26 + h28 + (-1) * h29 + (2) * h33 + (-2) * h34 + h37 + (2) * h42 + (-1) * h44 + (-1) * h46 + (2) * h47 + (-1) * h51 + h52 + h53 + h57 + h60
  have v31 : f {0,1,2,3,4}=0 := by
    linear_combination (6) * h0 + (2) * h1 + (-5) * h2 + (-5) * h3 + h4 + h5 + h6 + (-4) * h8 + (2) * h9 + h10 + (-1) * h11 + (-3) * h12 + (-3) * h16 + h17 + (3) * h18 + (2) * h23 + (-2) * h24 + (-1) * h25 + (2) * h26 + (2) * h28 + (-1) * h29 + (3) * h33 + (-3) * h34 + h37 + (2) * h42 + (-1) * h44 + (-1) * h46 + (2) * h47 + (-2) * h51 + (2) * h52 + h53 + h57 + h60
  have v32 : f {5}=0 := by
    linear_combination h7
  have v33 : f {0,5}=0 := by
    linear_combination h0 + (-1) * h3 + h7 + (-1) * h12 + h33
  have v34 : f {1,5}=0 := by
    linear_combination h0 + (-1) * h2 + h7 + (-1) * h12 + h50
  have v35 : f {0,1,5}=0 := by
    linear_combination (2) * h0 + (-1) * h2 + (-1) * h3 + h7 + (-1) * h12 + h33 + h50
  have v36 : f {2,5}=0 := by
    linear_combination h0 + (-1) * h2 + (-1) * h3 + h4 + h7 + (-1) * h12 + h33 + (-1) * h34 + h59
  have v37 : f {0,2,5}=0 := by
    linear_combination (2) * h0 + (-1) * h2 + (-2) * h3 + h4 + h7 + (-2) * h12 + h18 + (2) * h33 + (-1) * h34 + h59
  have v38 : f {1,2,5}=0 := by
    linear_combination (2) * h0 + (-2) * h2 + (-1) * h3 + h4 + h7 + (-2) * h12 + h33 + (-1) * h34 + h38 + h50 + h59
  have v39 : f {0,1,2,5}=0 := by
    linear_combination (4) * h0 + h1 + (-3) * h2 + (-3) * h3 + h4 + h7 + (-1) * h8 + h9 + (-3) * h12 + h18 + h23 + (-1) * h24 + (2) * h33 + (-2) * h34 + h35 + h38 + h50 + (-1) * h51 + h52 + h59
  have v40 : f {3,5}=0 := by
    linear_combination (-1) * h1 + h5 + h7 + h62
  have v41 : f {0,3,5}=0 := by
    linear_combination (2) * h0 + (-1) * h2 + (-2) * h3 + h5 + h7 + (-1) * h8 + h9 + (-1) * h12 + (-1) * h15 + h18 + (-1) * h20 + h23 + (-1) * h24 + h27 + h30 + (-1) * h31 + h33 + (-1) * h34 + h35 + (-1) * h51 + h52 + h62
  have v42 : f {1,3,5}=0 := by
    linear_combination (2) * h0 + (-2) * h2 + (-1) * h3 + h5 + h7 + (-1) * h8 + h9 + (-1) * h12 + (-1) * h15 + h23 + (-1) * h24 + (-1) * h34 + h35 + h38 + (-1) * h40 + h45 + h48 + (-1) * h49 + h50 + (-1) * h51 + h52 + h62
  have v43 : f {0,1,3,5}=0 := by
    linear_combination (4) * h0 + h1 + (-3) * h2 + (-3) * h3 + h5 + h7 + (-2) * h8 + (2) * h9 + (-2) * h12 + h13 + (-2) * h15 + h18 + (-1) * h20 + (2) * h23 + (-2) * h24 + h27 + h30 + (-1) * h31 + h33 + (-2) * h34 + (2) * h35 + h38 + (-1) * h40 + h45 + h48 + (-1) * h49 + h50 + (-2) * h51 + (2) * h52 + h62
  have v44 : f {2,3,5}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h2 + (-1) * h3 + h4 + h5 + h7 + (-1) * h12 + h33 + (-1) * h34 + h54 + h59 + h62
  have v45 : f {0,2,3,5}=0 := by
    linear_combination (3) * h0 + (-2) * h2 + (-3) * h3 + h4 + h5 + h7 + (-1) * h8 + h9 + (-2) * h12 + (-1) * h15 + h18 + h19 + (-1) * h20 + h23 + (-1) * h24 + h27 + h30 + (-1) * h31 + (2) * h33 + (-2) * h34 + h35 + (-1) * h51 + h52 + h54 + h59 + h62
  have v46 : f {1,2,3,5}=0 := by
    linear_combination (3) * h0 + (-3) * h2 + (-2) * h3 + h4 + h5 + h7 + (-1) * h8 + h9 + (-2) * h12 + (-1) * h15 + h23 + (-1) * h24 + h33 + (-2) * h34 + h35 + h38 + h39 + (-1) * h40 + h45 + h48 + (-1) * h49 + h50 + (-1) * h51 + h52 + h54 + h59 + h62
  have v47 : f {0,1,2,3,5}=0 := by
    linear_combination (6) * h0 + (2) * h1 + (-5) * h2 + (-5) * h3 + h4 + h5 + h7 + (-3) * h8 + (3) * h9 + (-4) * h12 + h13 + (-2) * h15 + (2) * h18 + (-1) * h20 + (3) * h23 + (-3) * h24 + h27 + h30 + (-1) * h31 + (2) * h33 + (-4) * h34 + (3) * h35 + (2) * h38 + (-1) * h40 + h45 + h48 + (-1) * h49 + h50 + (-3) * h51 + (3) * h52 + h55 + h59 + h62
  have v48 : f {4,5}=0 := by
    linear_combination (-1) * h1 + h6 + h7 + h63
  have v49 : f {0,4,5}=0 := by
    linear_combination (2) * h0 + (-1) * h2 + (-2) * h3 + h6 + h7 + (-1) * h8 + h9 + (-1) * h12 + (-1) * h15 + h18 + (-1) * h20 + h23 + (-1) * h24 + h30 + h33 + (-1) * h34 + h35 + (-1) * h51 + h52 + h63
  have v50 : f {1,4,5}=0 := by
    linear_combination (2) * h0 + (-2) * h2 + (-1) * h3 + h6 + h7 + (-1) * h8 + h9 + (-1) * h12 + (-1) * h15 + h23 + (-1) * h24 + (-1) * h34 + h35 + h38 + (-1) * h40 + h48 + h50 + (-1) * h51 + h52 + h63
  have v51 : f {0,1,4,5}=0 := by
    linear_combination (4) * h0 + h1 + (-3) * h2 + (-3) * h3 + h6 + h7 + (-2) * h8 + (2) * h9 + (-2) * h12 + h14 + (-2) * h15 + h18 + (-1) * h20 + (2) * h23 + (-2) * h24 + h30 + h33 + (-2) * h34 + (2) * h35 + h38 + (-1) * h40 + h48 + h50 + (-2) * h51 + (2) * h52 + h63
  have v52 : f {2,4,5}=0 := by
    linear_combination (2) * h0 + (-2) * h2 + (-2) * h3 + h4 + h6 + h7 + (-1) * h8 + h9 + (-2) * h12 + h14 + (-1) * h15 + h18 + (-1) * h20 + h23 + (-1) * h24 + h33 + (-2) * h34 + h35 + h38 + (-1) * h40 + (-1) * h51 + h52 + h58 + h59 + h63
  have v53 : f {0,2,4,5}=0 := by
    linear_combination (4) * h0 + h1 + (-3) * h2 + (-4) * h3 + h4 + h6 + h7 + (-2) * h8 + (2) * h9 + (-3) * h12 + h14 + (-2) * h15 + (2) * h18 + (-1) * h20 + (2) * h23 + (-2) * h24 + h30 + (2) * h33 + (-3) * h34 + (2) * h35 + h38 + (-1) * h40 + (-2) * h51 + (2) * h52 + h58 + h59 + h63
  have v54 : f {1,2,4,5}=0 := by
    linear_combination (4) * h0 + h1 + (-4) * h2 + (-3) * h3 + h4 + h6 + h7 + (-2) * h8 + (2) * h9 + (-3) * h12 + h14 + (-2) * h15 + h18 + (-1) * h20 + (2) * h23 + (-2) * h24 + h33 + (-3) * h34 + (2) * h35 + (2) * h38 + (-1) * h40 + h48 + h50 + (-2) * h51 + (2) * h52 + h58 + h59 + h63
  have v55 : f {0,1,2,4,5}=0 := by
    linear_combination (6) * h0 + (2) * h1 + (-5) * h2 + (-5) * h3 + h4 + h6 + h7 + (-3) * h8 + (3) * h9 + (-4) * h12 + h14 + (-2) * h15 + (2) * h18 + (-1) * h20 + (3) * h23 + (-3) * h24 + h30 + (2) * h33 + (-4) * h34 + (3) * h35 + (2) * h38 + (-1) * h40 + h48 + h50 + (-3) * h51 + (3) * h52 + h58 + h59 + h63
  have v56 : f {3,4,5}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h2 + (-1) * h3 + h5 + h6 + h7 + (-1) * h8 + h9 + (-1) * h15 + h18 + (-1) * h20 + h23 + (-1) * h24 + h30 + (-1) * h31 + (-1) * h34 + h35 + (-1) * h51 + h52 + h61 + h62 + h63
  have v57 : f {0,3,4,5}=0 := by
    linear_combination (3) * h0 + (-2) * h2 + (-3) * h3 + h5 + h6 + h7 + (-2) * h8 + (2) * h9 + (-1) * h12 + (-2) * h15 + (2) * h18 + (-2) * h20 + (2) * h23 + (-2) * h24 + h27 + (2) * h30 + (-1) * h31 + h33 + (-2) * h34 + (2) * h35 + (-2) * h51 + (2) * h52 + h61 + h62 + h63
  have v58 : f {1,3,4,5}=0 := by
    linear_combination (3) * h0 + (-3) * h2 + (-2) * h3 + h5 + h6 + h7 + (-2) * h8 + (2) * h9 + (-1) * h12 + (-2) * h15 + h18 + (-1) * h20 + (2) * h23 + (-2) * h24 + h30 + (-1) * h31 + (-2) * h34 + (2) * h35 + h38 + (-1) * h40 + h45 + h48 + h50 + (-2) * h51 + (2) * h52 + h61 + h62 + h63
  have v59 : f {0,1,3,4,5}=0 := by
    linear_combination (6) * h0 + (2) * h1 + (-5) * h2 + (-5) * h3 + h5 + h6 + h7 + (-4) * h8 + (4) * h9 + (-3) * h12 + h13 + (-3) * h15 + (3) * h18 + (-2) * h20 + (-1) * h22 + (4) * h23 + (-4) * h24 + h27 + (2) * h30 + (-2) * h31 + h32 + h33 + (-4) * h34 + (4) * h35 + (2) * h38 + (-1) * h39 + (-1) * h40 + h45 + h48 + h50 + (-4) * h51 + (4) * h52 + (-1) * h54 + h55 + h61 + h62 + h63
  have v60 : f {2,3,4,5}=0 := by
    linear_combination (3) * h0 + (-3) * h2 + (-3) * h3 + h4 + h5 + h6 + h7 + (-2) * h8 + (2) * h9 + (-2) * h12 + h14 + (-2) * h15 + (2) * h18 + (-2) * h20 + (2) * h23 + (-2) * h24 + h30 + (-1) * h31 + h33 + (-3) * h34 + (2) * h35 + h38 + (-1) * h40 + (-2) * h51 + (2) * h52 + h56 + h58 + h59 + h61 + h62 + h63
  have v61 : f {0,2,3,4,5}=0 := by
    linear_combination (5) * h0 + h1 + (-4) * h2 + (-5) * h3 + h4 + h5 + h6 + h7 + (-3) * h8 + (3) * h9 + (-3) * h12 + h14 + (-3) * h15 + (3) * h18 + (-3) * h20 + h21 + (3) * h23 + (-3) * h24 + h27 + (2) * h30 + (-1) * h31 + (2) * h33 + (-4) * h34 + (3) * h35 + h38 + (-1) * h40 + (-3) * h51 + (3) * h52 + h56 + h58 + h59 + h61 + h62 + h63
  have v62 : f {1,2,3,4,5}=0 := by
    linear_combination (5) * h0 + h1 + (-5) * h2 + (-4) * h3 + h4 + h5 + h6 + h7 + (-3) * h8 + (3) * h9 + (-3) * h12 + h14 + (-3) * h15 + (2) * h18 + (-2) * h20 + (3) * h23 + (-3) * h24 + h30 + (-1) * h31 + h33 + (-4) * h34 + (3) * h35 + (2) * h38 + (-2) * h40 + h41 + h45 + h48 + h50 + (-3) * h51 + (3) * h52 + h56 + h58 + h59 + h61 + h62 + h63
  have v63 : f {0,1,2,3,4,5}=0 := by
    linear_combination (8) * h0 + (3) * h1 + (-7) * h2 + (-7) * h3 + h4 + h5 + h6 + h7 + (-5) * h8 + (5) * h9 + (-5) * h12 + h13 + h14 + (-4) * h15 + (4) * h18 + (-3) * h20 + (5) * h23 + (-5) * h24 + h27 + (2) * h30 + (-2) * h31 + h32 + (2) * h33 + (-6) * h34 + (5) * h35 + (3) * h38 + (-1) * h39 + (-2) * h40 + h41 + h45 + h48 + h50 + (-5) * h51 + (5) * h52 + (-1) * h54 + h55 + h56 + h58 + h59 + h61 + h62 + h63
  funext S
  change f S=0
  have casesS : ∀ S : Finset (Fin 6), S=∅ ∨ S={0} ∨ S={1} ∨ S={0,1} ∨ S={2} ∨ S={0,2} ∨ S={1,2} ∨ S={0,1,2} ∨ S={3} ∨ S={0,3} ∨ S={1,3} ∨ S={0,1,3} ∨ S={2,3} ∨ S={0,2,3} ∨ S={1,2,3} ∨ S={0,1,2,3} ∨ S={4} ∨ S={0,4} ∨ S={1,4} ∨ S={0,1,4} ∨ S={2,4} ∨ S={0,2,4} ∨ S={1,2,4} ∨ S={0,1,2,4} ∨ S={3,4} ∨ S={0,3,4} ∨ S={1,3,4} ∨ S={0,1,3,4} ∨ S={2,3,4} ∨ S={0,2,3,4} ∨ S={1,2,3,4} ∨ S={0,1,2,3,4} ∨ S={5} ∨ S={0,5} ∨ S={1,5} ∨ S={0,1,5} ∨ S={2,5} ∨ S={0,2,5} ∨ S={1,2,5} ∨ S={0,1,2,5} ∨ S={3,5} ∨ S={0,3,5} ∨ S={1,3,5} ∨ S={0,1,3,5} ∨ S={2,3,5} ∨ S={0,2,3,5} ∨ S={1,2,3,5} ∨ S={0,1,2,3,5} ∨ S={4,5} ∨ S={0,4,5} ∨ S={1,4,5} ∨ S={0,1,4,5} ∨ S={2,4,5} ∨ S={0,2,4,5} ∨ S={1,2,4,5} ∨ S={0,1,2,4,5} ∨ S={3,4,5} ∨ S={0,3,4,5} ∨ S={1,3,4,5} ∨ S={0,1,3,4,5} ∨ S={2,3,4,5} ∨ S={0,2,3,4,5} ∨ S={1,2,3,4,5} ∨ S={0,1,2,3,4,5} := by decide
  rcases casesS S with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem empty_zero : integerFunction ∅=0 := by decide

theorem singleton_zero : ∀ v : Fin 6,integerFunction {v}=0 := by decide

theorem boolean_differences : ∀ u v : Fin 6,u≠ v → ∀ S : Finset (Fin 6),
    u∉S → v∉S → integerDelta integerFunction u v S=0 ∨
      integerDelta integerFunction u v S=1 := by decide

theorem extreme : ExtremeSupermodular (realFunction integerFunction) :=
  extreme_of_row_kernel integerFunction rows pivot pivot_one row_zero valid_rows
    row_kernel_zero empty_zero singleton_zero boolean_differences

end K1122

namespace K1122Complement

def integerFunction (S : Finset (Fin 6)) : ℤ :=
  (match subsetMask S with
  | 11 => 1
  | 15 => 1
  | 23 => 1
  | 25 => 1
  | 26 => 1
  | 27 => 2
  | 29 => 1
  | 30 => 1
  | 31 => 3
  | 35 => 1
  | 37 => 1
  | 38 => 1
  | 39 => 2
  | 40 => 1
  | 41 => 1
  | 42 => 1
  | 43 => 2
  | 44 => 1
  | 45 => 2
  | 46 => 2
  | 47 => 3
  | 51 => 1
  | 53 => 1
  | 54 => 1
  | 55 => 3
  | 56 => 1
  | 57 => 2
  | 58 => 2
  | 59 => 3
  | 60 => 1
  | 61 => 3
  | 62 => 3
  | 63 => 5
  | _ => 0)

def rows : Fin 64 → Row (Fin 6) :=
  ![.value {0,1,3},.value ∅,.value {0},.value {1},.value {2},.value {3},.value {4},.value {5},.elemental 0 1 ∅,.elemental 0 1 {2},.elemental 0 1 {4},.elemental 0 1 {3,4},.elemental 0 1 {2,5},.elemental 0 1 {2,3,5},.elemental 0 1 {3,4,5},.elemental 0 1 {2,3,4,5},.elemental 0 2 ∅,.elemental 0 2 {3},.elemental 0 2 {1,3},.elemental 0 2 {4},.elemental 0 2 {3,4},.elemental 0 2 {1,5},.elemental 0 2 {1,3,5},.elemental 0 3 ∅,.elemental 0 3 {5},.elemental 0 3 {1,5},.elemental 0 3 {1,4,5},.elemental 0 3 {1,2,4,5},.elemental 0 4 ∅,.elemental 0 4 {1,3},.elemental 0 4 {5},.elemental 0 4 {1,5},.elemental 0 4 {2,5},.elemental 0 5 ∅,.elemental 0 5 {1,3},.elemental 0 5 {1,2,3,4},.elemental 1 2 ∅,.elemental 1 2 {3},.elemental 1 2 {4},.elemental 1 2 {3,4},.elemental 1 2 {0,5},.elemental 1 2 {0,3,5},.elemental 1 3 ∅,.elemental 1 3 {5},.elemental 1 3 {0,4,5},.elemental 1 3 {0,2,4,5},.elemental 1 4 ∅,.elemental 1 4 {0,3},.elemental 1 4 {5},.elemental 1 4 {2,5},.elemental 1 5 ∅,.elemental 2 3 ∅,.elemental 2 3 {4},.elemental 2 3 {0,1,4},.elemental 2 3 {5},.elemental 2 3 {4,5},.elemental 2 3 {0,4,5},.elemental 2 4 ∅,.elemental 2 4 {5},.elemental 2 5 ∅,.elemental 3 4 ∅,.elemental 3 4 {5},.elemental 3 5 {0,1},.elemental 4 5 ∅]

def pivot : Finset (Fin 6) := {0,1,3}

theorem pivot_one : integerFunction pivot=1 := by decide

theorem row_zero : rows 0=.value pivot := by decide

theorem valid_rows : ∀ i : Fin 64,i≠0 → (rows i).valid integerFunction := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 4096 in
theorem row_kernel_zero (f : SetFunction (Fin 6))
    (hf : ∀ i : Fin 64,(rows i).eval f=0) : f=0 := by
  have h0 : f {0,1,3}=0 := hf 0
  have h1 : f ∅=0 := hf 1
  have h2 : f {0}=0 := hf 2
  have h3 : f {1}=0 := hf 3
  have h4 : f {2}=0 := hf 4
  have h5 : f {3}=0 := hf 5
  have h6 : f {4}=0 := hf 6
  have h7 : f {5}=0 := hf 7
  have h8 : f {0,1}-f {0}-f {1}+f ∅=0 := by
    have h := hf 8
    change f (insert 0 (insert 1 (∅ : Finset (Fin 6))))-
      f (insert 0 (∅ : Finset (Fin 6)))-f (insert 1 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 0 (insert 1 (∅ : Finset (Fin 6)))={0,1} := by decide
    have hA : insert 0 (∅ : Finset (Fin 6))={0} := by decide
    have hB : insert 1 (∅ : Finset (Fin 6))={1} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h9 : f {0,1,2}-f {0,2}-f {1,2}+f {2}=0 := by
    have h := hf 9
    change f (insert 0 (insert 1 ({2} : Finset (Fin 6))))-
      f (insert 0 ({2} : Finset (Fin 6)))-f (insert 1 ({2} : Finset (Fin 6)))+f {2}=0 at h
    have hAB : insert 0 (insert 1 ({2} : Finset (Fin 6)))={0,1,2} := by decide
    have hA : insert 0 ({2} : Finset (Fin 6))={0,2} := by decide
    have hB : insert 1 ({2} : Finset (Fin 6))={1,2} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h10 : f {0,1,4}-f {0,4}-f {1,4}+f {4}=0 := by
    have h := hf 10
    change f (insert 0 (insert 1 ({4} : Finset (Fin 6))))-
      f (insert 0 ({4} : Finset (Fin 6)))-f (insert 1 ({4} : Finset (Fin 6)))+f {4}=0 at h
    have hAB : insert 0 (insert 1 ({4} : Finset (Fin 6)))={0,1,4} := by decide
    have hA : insert 0 ({4} : Finset (Fin 6))={0,4} := by decide
    have hB : insert 1 ({4} : Finset (Fin 6))={1,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h11 : f {0,1,3,4}-f {0,3,4}-f {1,3,4}+f {3,4}=0 := by
    have h := hf 11
    change f (insert 0 (insert 1 ({3,4} : Finset (Fin 6))))-
      f (insert 0 ({3,4} : Finset (Fin 6)))-f (insert 1 ({3,4} : Finset (Fin 6)))+f {3,4}=0 at h
    have hAB : insert 0 (insert 1 ({3,4} : Finset (Fin 6)))={0,1,3,4} := by decide
    have hA : insert 0 ({3,4} : Finset (Fin 6))={0,3,4} := by decide
    have hB : insert 1 ({3,4} : Finset (Fin 6))={1,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h12 : f {0,1,2,5}-f {0,2,5}-f {1,2,5}+f {2,5}=0 := by
    have h := hf 12
    change f (insert 0 (insert 1 ({2,5} : Finset (Fin 6))))-
      f (insert 0 ({2,5} : Finset (Fin 6)))-f (insert 1 ({2,5} : Finset (Fin 6)))+f {2,5}=0 at h
    have hAB : insert 0 (insert 1 ({2,5} : Finset (Fin 6)))={0,1,2,5} := by decide
    have hA : insert 0 ({2,5} : Finset (Fin 6))={0,2,5} := by decide
    have hB : insert 1 ({2,5} : Finset (Fin 6))={1,2,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h13 : f {0,1,2,3,5}-f {0,2,3,5}-f {1,2,3,5}+f {2,3,5}=0 := by
    have h := hf 13
    change f (insert 0 (insert 1 ({2,3,5} : Finset (Fin 6))))-
      f (insert 0 ({2,3,5} : Finset (Fin 6)))-f (insert 1 ({2,3,5} : Finset (Fin 6)))+f {2,3,5}=0 at h
    have hAB : insert 0 (insert 1 ({2,3,5} : Finset (Fin 6)))={0,1,2,3,5} := by decide
    have hA : insert 0 ({2,3,5} : Finset (Fin 6))={0,2,3,5} := by decide
    have hB : insert 1 ({2,3,5} : Finset (Fin 6))={1,2,3,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h14 : f {0,1,3,4,5}-f {0,3,4,5}-f {1,3,4,5}+f {3,4,5}=0 := by
    have h := hf 14
    change f (insert 0 (insert 1 ({3,4,5} : Finset (Fin 6))))-
      f (insert 0 ({3,4,5} : Finset (Fin 6)))-f (insert 1 ({3,4,5} : Finset (Fin 6)))+f {3,4,5}=0 at h
    have hAB : insert 0 (insert 1 ({3,4,5} : Finset (Fin 6)))={0,1,3,4,5} := by decide
    have hA : insert 0 ({3,4,5} : Finset (Fin 6))={0,3,4,5} := by decide
    have hB : insert 1 ({3,4,5} : Finset (Fin 6))={1,3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h15 : f {0,1,2,3,4,5}-f {0,2,3,4,5}-f {1,2,3,4,5}+f {2,3,4,5}=0 := by
    have h := hf 15
    change f (insert 0 (insert 1 ({2,3,4,5} : Finset (Fin 6))))-
      f (insert 0 ({2,3,4,5} : Finset (Fin 6)))-f (insert 1 ({2,3,4,5} : Finset (Fin 6)))+f {2,3,4,5}=0 at h
    have hAB : insert 0 (insert 1 ({2,3,4,5} : Finset (Fin 6)))={0,1,2,3,4,5} := by decide
    have hA : insert 0 ({2,3,4,5} : Finset (Fin 6))={0,2,3,4,5} := by decide
    have hB : insert 1 ({2,3,4,5} : Finset (Fin 6))={1,2,3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h16 : f {0,2}-f {0}-f {2}+f ∅=0 := by
    have h := hf 16
    change f (insert 0 (insert 2 (∅ : Finset (Fin 6))))-
      f (insert 0 (∅ : Finset (Fin 6)))-f (insert 2 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 0 (insert 2 (∅ : Finset (Fin 6)))={0,2} := by decide
    have hA : insert 0 (∅ : Finset (Fin 6))={0} := by decide
    have hB : insert 2 (∅ : Finset (Fin 6))={2} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h17 : f {0,2,3}-f {0,3}-f {2,3}+f {3}=0 := by
    have h := hf 17
    change f (insert 0 (insert 2 ({3} : Finset (Fin 6))))-
      f (insert 0 ({3} : Finset (Fin 6)))-f (insert 2 ({3} : Finset (Fin 6)))+f {3}=0 at h
    have hAB : insert 0 (insert 2 ({3} : Finset (Fin 6)))={0,2,3} := by decide
    have hA : insert 0 ({3} : Finset (Fin 6))={0,3} := by decide
    have hB : insert 2 ({3} : Finset (Fin 6))={2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h18 : f {0,1,2,3}-f {0,1,3}-f {1,2,3}+f {1,3}=0 := by
    have h := hf 18
    change f (insert 0 (insert 2 ({1,3} : Finset (Fin 6))))-
      f (insert 0 ({1,3} : Finset (Fin 6)))-f (insert 2 ({1,3} : Finset (Fin 6)))+f {1,3}=0 at h
    have hAB : insert 0 (insert 2 ({1,3} : Finset (Fin 6)))={0,1,2,3} := by decide
    have hA : insert 0 ({1,3} : Finset (Fin 6))={0,1,3} := by decide
    have hB : insert 2 ({1,3} : Finset (Fin 6))={1,2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h19 : f {0,2,4}-f {0,4}-f {2,4}+f {4}=0 := by
    have h := hf 19
    change f (insert 0 (insert 2 ({4} : Finset (Fin 6))))-
      f (insert 0 ({4} : Finset (Fin 6)))-f (insert 2 ({4} : Finset (Fin 6)))+f {4}=0 at h
    have hAB : insert 0 (insert 2 ({4} : Finset (Fin 6)))={0,2,4} := by decide
    have hA : insert 0 ({4} : Finset (Fin 6))={0,4} := by decide
    have hB : insert 2 ({4} : Finset (Fin 6))={2,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h20 : f {0,2,3,4}-f {0,3,4}-f {2,3,4}+f {3,4}=0 := by
    have h := hf 20
    change f (insert 0 (insert 2 ({3,4} : Finset (Fin 6))))-
      f (insert 0 ({3,4} : Finset (Fin 6)))-f (insert 2 ({3,4} : Finset (Fin 6)))+f {3,4}=0 at h
    have hAB : insert 0 (insert 2 ({3,4} : Finset (Fin 6)))={0,2,3,4} := by decide
    have hA : insert 0 ({3,4} : Finset (Fin 6))={0,3,4} := by decide
    have hB : insert 2 ({3,4} : Finset (Fin 6))={2,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h21 : f {0,1,2,5}-f {0,1,5}-f {1,2,5}+f {1,5}=0 := by
    have h := hf 21
    change f (insert 0 (insert 2 ({1,5} : Finset (Fin 6))))-
      f (insert 0 ({1,5} : Finset (Fin 6)))-f (insert 2 ({1,5} : Finset (Fin 6)))+f {1,5}=0 at h
    have hAB : insert 0 (insert 2 ({1,5} : Finset (Fin 6)))={0,1,2,5} := by decide
    have hA : insert 0 ({1,5} : Finset (Fin 6))={0,1,5} := by decide
    have hB : insert 2 ({1,5} : Finset (Fin 6))={1,2,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h22 : f {0,1,2,3,5}-f {0,1,3,5}-f {1,2,3,5}+f {1,3,5}=0 := by
    have h := hf 22
    change f (insert 0 (insert 2 ({1,3,5} : Finset (Fin 6))))-
      f (insert 0 ({1,3,5} : Finset (Fin 6)))-f (insert 2 ({1,3,5} : Finset (Fin 6)))+f {1,3,5}=0 at h
    have hAB : insert 0 (insert 2 ({1,3,5} : Finset (Fin 6)))={0,1,2,3,5} := by decide
    have hA : insert 0 ({1,3,5} : Finset (Fin 6))={0,1,3,5} := by decide
    have hB : insert 2 ({1,3,5} : Finset (Fin 6))={1,2,3,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h23 : f {0,3}-f {0}-f {3}+f ∅=0 := by
    have h := hf 23
    change f (insert 0 (insert 3 (∅ : Finset (Fin 6))))-
      f (insert 0 (∅ : Finset (Fin 6)))-f (insert 3 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 0 (insert 3 (∅ : Finset (Fin 6)))={0,3} := by decide
    have hA : insert 0 (∅ : Finset (Fin 6))={0} := by decide
    have hB : insert 3 (∅ : Finset (Fin 6))={3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h24 : f {0,3,5}-f {0,5}-f {3,5}+f {5}=0 := by
    have h := hf 24
    change f (insert 0 (insert 3 ({5} : Finset (Fin 6))))-
      f (insert 0 ({5} : Finset (Fin 6)))-f (insert 3 ({5} : Finset (Fin 6)))+f {5}=0 at h
    have hAB : insert 0 (insert 3 ({5} : Finset (Fin 6)))={0,3,5} := by decide
    have hA : insert 0 ({5} : Finset (Fin 6))={0,5} := by decide
    have hB : insert 3 ({5} : Finset (Fin 6))={3,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h25 : f {0,1,3,5}-f {0,1,5}-f {1,3,5}+f {1,5}=0 := by
    have h := hf 25
    change f (insert 0 (insert 3 ({1,5} : Finset (Fin 6))))-
      f (insert 0 ({1,5} : Finset (Fin 6)))-f (insert 3 ({1,5} : Finset (Fin 6)))+f {1,5}=0 at h
    have hAB : insert 0 (insert 3 ({1,5} : Finset (Fin 6)))={0,1,3,5} := by decide
    have hA : insert 0 ({1,5} : Finset (Fin 6))={0,1,5} := by decide
    have hB : insert 3 ({1,5} : Finset (Fin 6))={1,3,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h26 : f {0,1,3,4,5}-f {0,1,4,5}-f {1,3,4,5}+f {1,4,5}=0 := by
    have h := hf 26
    change f (insert 0 (insert 3 ({1,4,5} : Finset (Fin 6))))-
      f (insert 0 ({1,4,5} : Finset (Fin 6)))-f (insert 3 ({1,4,5} : Finset (Fin 6)))+f {1,4,5}=0 at h
    have hAB : insert 0 (insert 3 ({1,4,5} : Finset (Fin 6)))={0,1,3,4,5} := by decide
    have hA : insert 0 ({1,4,5} : Finset (Fin 6))={0,1,4,5} := by decide
    have hB : insert 3 ({1,4,5} : Finset (Fin 6))={1,3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h27 : f {0,1,2,3,4,5}-f {0,1,2,4,5}-f {1,2,3,4,5}+f {1,2,4,5}=0 := by
    have h := hf 27
    change f (insert 0 (insert 3 ({1,2,4,5} : Finset (Fin 6))))-
      f (insert 0 ({1,2,4,5} : Finset (Fin 6)))-f (insert 3 ({1,2,4,5} : Finset (Fin 6)))+f {1,2,4,5}=0 at h
    have hAB : insert 0 (insert 3 ({1,2,4,5} : Finset (Fin 6)))={0,1,2,3,4,5} := by decide
    have hA : insert 0 ({1,2,4,5} : Finset (Fin 6))={0,1,2,4,5} := by decide
    have hB : insert 3 ({1,2,4,5} : Finset (Fin 6))={1,2,3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h28 : f {0,4}-f {0}-f {4}+f ∅=0 := by
    have h := hf 28
    change f (insert 0 (insert 4 (∅ : Finset (Fin 6))))-
      f (insert 0 (∅ : Finset (Fin 6)))-f (insert 4 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 0 (insert 4 (∅ : Finset (Fin 6)))={0,4} := by decide
    have hA : insert 0 (∅ : Finset (Fin 6))={0} := by decide
    have hB : insert 4 (∅ : Finset (Fin 6))={4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h29 : f {0,1,3,4}-f {0,1,3}-f {1,3,4}+f {1,3}=0 := by
    have h := hf 29
    change f (insert 0 (insert 4 ({1,3} : Finset (Fin 6))))-
      f (insert 0 ({1,3} : Finset (Fin 6)))-f (insert 4 ({1,3} : Finset (Fin 6)))+f {1,3}=0 at h
    have hAB : insert 0 (insert 4 ({1,3} : Finset (Fin 6)))={0,1,3,4} := by decide
    have hA : insert 0 ({1,3} : Finset (Fin 6))={0,1,3} := by decide
    have hB : insert 4 ({1,3} : Finset (Fin 6))={1,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h30 : f {0,4,5}-f {0,5}-f {4,5}+f {5}=0 := by
    have h := hf 30
    change f (insert 0 (insert 4 ({5} : Finset (Fin 6))))-
      f (insert 0 ({5} : Finset (Fin 6)))-f (insert 4 ({5} : Finset (Fin 6)))+f {5}=0 at h
    have hAB : insert 0 (insert 4 ({5} : Finset (Fin 6)))={0,4,5} := by decide
    have hA : insert 0 ({5} : Finset (Fin 6))={0,5} := by decide
    have hB : insert 4 ({5} : Finset (Fin 6))={4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h31 : f {0,1,4,5}-f {0,1,5}-f {1,4,5}+f {1,5}=0 := by
    have h := hf 31
    change f (insert 0 (insert 4 ({1,5} : Finset (Fin 6))))-
      f (insert 0 ({1,5} : Finset (Fin 6)))-f (insert 4 ({1,5} : Finset (Fin 6)))+f {1,5}=0 at h
    have hAB : insert 0 (insert 4 ({1,5} : Finset (Fin 6)))={0,1,4,5} := by decide
    have hA : insert 0 ({1,5} : Finset (Fin 6))={0,1,5} := by decide
    have hB : insert 4 ({1,5} : Finset (Fin 6))={1,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h32 : f {0,2,4,5}-f {0,2,5}-f {2,4,5}+f {2,5}=0 := by
    have h := hf 32
    change f (insert 0 (insert 4 ({2,5} : Finset (Fin 6))))-
      f (insert 0 ({2,5} : Finset (Fin 6)))-f (insert 4 ({2,5} : Finset (Fin 6)))+f {2,5}=0 at h
    have hAB : insert 0 (insert 4 ({2,5} : Finset (Fin 6)))={0,2,4,5} := by decide
    have hA : insert 0 ({2,5} : Finset (Fin 6))={0,2,5} := by decide
    have hB : insert 4 ({2,5} : Finset (Fin 6))={2,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h33 : f {0,5}-f {0}-f {5}+f ∅=0 := by
    have h := hf 33
    change f (insert 0 (insert 5 (∅ : Finset (Fin 6))))-
      f (insert 0 (∅ : Finset (Fin 6)))-f (insert 5 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 0 (insert 5 (∅ : Finset (Fin 6)))={0,5} := by decide
    have hA : insert 0 (∅ : Finset (Fin 6))={0} := by decide
    have hB : insert 5 (∅ : Finset (Fin 6))={5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h34 : f {0,1,3,5}-f {0,1,3}-f {1,3,5}+f {1,3}=0 := by
    have h := hf 34
    change f (insert 0 (insert 5 ({1,3} : Finset (Fin 6))))-
      f (insert 0 ({1,3} : Finset (Fin 6)))-f (insert 5 ({1,3} : Finset (Fin 6)))+f {1,3}=0 at h
    have hAB : insert 0 (insert 5 ({1,3} : Finset (Fin 6)))={0,1,3,5} := by decide
    have hA : insert 0 ({1,3} : Finset (Fin 6))={0,1,3} := by decide
    have hB : insert 5 ({1,3} : Finset (Fin 6))={1,3,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h35 : f {0,1,2,3,4,5}-f {0,1,2,3,4}-f {1,2,3,4,5}+f {1,2,3,4}=0 := by
    have h := hf 35
    change f (insert 0 (insert 5 ({1,2,3,4} : Finset (Fin 6))))-
      f (insert 0 ({1,2,3,4} : Finset (Fin 6)))-f (insert 5 ({1,2,3,4} : Finset (Fin 6)))+f {1,2,3,4}=0 at h
    have hAB : insert 0 (insert 5 ({1,2,3,4} : Finset (Fin 6)))={0,1,2,3,4,5} := by decide
    have hA : insert 0 ({1,2,3,4} : Finset (Fin 6))={0,1,2,3,4} := by decide
    have hB : insert 5 ({1,2,3,4} : Finset (Fin 6))={1,2,3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h36 : f {1,2}-f {1}-f {2}+f ∅=0 := by
    have h := hf 36
    change f (insert 1 (insert 2 (∅ : Finset (Fin 6))))-
      f (insert 1 (∅ : Finset (Fin 6)))-f (insert 2 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 1 (insert 2 (∅ : Finset (Fin 6)))={1,2} := by decide
    have hA : insert 1 (∅ : Finset (Fin 6))={1} := by decide
    have hB : insert 2 (∅ : Finset (Fin 6))={2} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h37 : f {1,2,3}-f {1,3}-f {2,3}+f {3}=0 := by
    have h := hf 37
    change f (insert 1 (insert 2 ({3} : Finset (Fin 6))))-
      f (insert 1 ({3} : Finset (Fin 6)))-f (insert 2 ({3} : Finset (Fin 6)))+f {3}=0 at h
    have hAB : insert 1 (insert 2 ({3} : Finset (Fin 6)))={1,2,3} := by decide
    have hA : insert 1 ({3} : Finset (Fin 6))={1,3} := by decide
    have hB : insert 2 ({3} : Finset (Fin 6))={2,3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h38 : f {1,2,4}-f {1,4}-f {2,4}+f {4}=0 := by
    have h := hf 38
    change f (insert 1 (insert 2 ({4} : Finset (Fin 6))))-
      f (insert 1 ({4} : Finset (Fin 6)))-f (insert 2 ({4} : Finset (Fin 6)))+f {4}=0 at h
    have hAB : insert 1 (insert 2 ({4} : Finset (Fin 6)))={1,2,4} := by decide
    have hA : insert 1 ({4} : Finset (Fin 6))={1,4} := by decide
    have hB : insert 2 ({4} : Finset (Fin 6))={2,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h39 : f {1,2,3,4}-f {1,3,4}-f {2,3,4}+f {3,4}=0 := by
    have h := hf 39
    change f (insert 1 (insert 2 ({3,4} : Finset (Fin 6))))-
      f (insert 1 ({3,4} : Finset (Fin 6)))-f (insert 2 ({3,4} : Finset (Fin 6)))+f {3,4}=0 at h
    have hAB : insert 1 (insert 2 ({3,4} : Finset (Fin 6)))={1,2,3,4} := by decide
    have hA : insert 1 ({3,4} : Finset (Fin 6))={1,3,4} := by decide
    have hB : insert 2 ({3,4} : Finset (Fin 6))={2,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h40 : f {0,1,2,5}-f {0,1,5}-f {0,2,5}+f {0,5}=0 := by
    have h := hf 40
    change f (insert 1 (insert 2 ({0,5} : Finset (Fin 6))))-
      f (insert 1 ({0,5} : Finset (Fin 6)))-f (insert 2 ({0,5} : Finset (Fin 6)))+f {0,5}=0 at h
    have hAB : insert 1 (insert 2 ({0,5} : Finset (Fin 6)))={0,1,2,5} := by decide
    have hA : insert 1 ({0,5} : Finset (Fin 6))={0,1,5} := by decide
    have hB : insert 2 ({0,5} : Finset (Fin 6))={0,2,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h41 : f {0,1,2,3,5}-f {0,1,3,5}-f {0,2,3,5}+f {0,3,5}=0 := by
    have h := hf 41
    change f (insert 1 (insert 2 ({0,3,5} : Finset (Fin 6))))-
      f (insert 1 ({0,3,5} : Finset (Fin 6)))-f (insert 2 ({0,3,5} : Finset (Fin 6)))+f {0,3,5}=0 at h
    have hAB : insert 1 (insert 2 ({0,3,5} : Finset (Fin 6)))={0,1,2,3,5} := by decide
    have hA : insert 1 ({0,3,5} : Finset (Fin 6))={0,1,3,5} := by decide
    have hB : insert 2 ({0,3,5} : Finset (Fin 6))={0,2,3,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h42 : f {1,3}-f {1}-f {3}+f ∅=0 := by
    have h := hf 42
    change f (insert 1 (insert 3 (∅ : Finset (Fin 6))))-
      f (insert 1 (∅ : Finset (Fin 6)))-f (insert 3 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 1 (insert 3 (∅ : Finset (Fin 6)))={1,3} := by decide
    have hA : insert 1 (∅ : Finset (Fin 6))={1} := by decide
    have hB : insert 3 (∅ : Finset (Fin 6))={3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h43 : f {1,3,5}-f {1,5}-f {3,5}+f {5}=0 := by
    have h := hf 43
    change f (insert 1 (insert 3 ({5} : Finset (Fin 6))))-
      f (insert 1 ({5} : Finset (Fin 6)))-f (insert 3 ({5} : Finset (Fin 6)))+f {5}=0 at h
    have hAB : insert 1 (insert 3 ({5} : Finset (Fin 6)))={1,3,5} := by decide
    have hA : insert 1 ({5} : Finset (Fin 6))={1,5} := by decide
    have hB : insert 3 ({5} : Finset (Fin 6))={3,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h44 : f {0,1,3,4,5}-f {0,1,4,5}-f {0,3,4,5}+f {0,4,5}=0 := by
    have h := hf 44
    change f (insert 1 (insert 3 ({0,4,5} : Finset (Fin 6))))-
      f (insert 1 ({0,4,5} : Finset (Fin 6)))-f (insert 3 ({0,4,5} : Finset (Fin 6)))+f {0,4,5}=0 at h
    have hAB : insert 1 (insert 3 ({0,4,5} : Finset (Fin 6)))={0,1,3,4,5} := by decide
    have hA : insert 1 ({0,4,5} : Finset (Fin 6))={0,1,4,5} := by decide
    have hB : insert 3 ({0,4,5} : Finset (Fin 6))={0,3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h45 : f {0,1,2,3,4,5}-f {0,1,2,4,5}-f {0,2,3,4,5}+f {0,2,4,5}=0 := by
    have h := hf 45
    change f (insert 1 (insert 3 ({0,2,4,5} : Finset (Fin 6))))-
      f (insert 1 ({0,2,4,5} : Finset (Fin 6)))-f (insert 3 ({0,2,4,5} : Finset (Fin 6)))+f {0,2,4,5}=0 at h
    have hAB : insert 1 (insert 3 ({0,2,4,5} : Finset (Fin 6)))={0,1,2,3,4,5} := by decide
    have hA : insert 1 ({0,2,4,5} : Finset (Fin 6))={0,1,2,4,5} := by decide
    have hB : insert 3 ({0,2,4,5} : Finset (Fin 6))={0,2,3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h46 : f {1,4}-f {1}-f {4}+f ∅=0 := by
    have h := hf 46
    change f (insert 1 (insert 4 (∅ : Finset (Fin 6))))-
      f (insert 1 (∅ : Finset (Fin 6)))-f (insert 4 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 1 (insert 4 (∅ : Finset (Fin 6)))={1,4} := by decide
    have hA : insert 1 (∅ : Finset (Fin 6))={1} := by decide
    have hB : insert 4 (∅ : Finset (Fin 6))={4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h47 : f {0,1,3,4}-f {0,1,3}-f {0,3,4}+f {0,3}=0 := by
    have h := hf 47
    change f (insert 1 (insert 4 ({0,3} : Finset (Fin 6))))-
      f (insert 1 ({0,3} : Finset (Fin 6)))-f (insert 4 ({0,3} : Finset (Fin 6)))+f {0,3}=0 at h
    have hAB : insert 1 (insert 4 ({0,3} : Finset (Fin 6)))={0,1,3,4} := by decide
    have hA : insert 1 ({0,3} : Finset (Fin 6))={0,1,3} := by decide
    have hB : insert 4 ({0,3} : Finset (Fin 6))={0,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h48 : f {1,4,5}-f {1,5}-f {4,5}+f {5}=0 := by
    have h := hf 48
    change f (insert 1 (insert 4 ({5} : Finset (Fin 6))))-
      f (insert 1 ({5} : Finset (Fin 6)))-f (insert 4 ({5} : Finset (Fin 6)))+f {5}=0 at h
    have hAB : insert 1 (insert 4 ({5} : Finset (Fin 6)))={1,4,5} := by decide
    have hA : insert 1 ({5} : Finset (Fin 6))={1,5} := by decide
    have hB : insert 4 ({5} : Finset (Fin 6))={4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h49 : f {1,2,4,5}-f {1,2,5}-f {2,4,5}+f {2,5}=0 := by
    have h := hf 49
    change f (insert 1 (insert 4 ({2,5} : Finset (Fin 6))))-
      f (insert 1 ({2,5} : Finset (Fin 6)))-f (insert 4 ({2,5} : Finset (Fin 6)))+f {2,5}=0 at h
    have hAB : insert 1 (insert 4 ({2,5} : Finset (Fin 6)))={1,2,4,5} := by decide
    have hA : insert 1 ({2,5} : Finset (Fin 6))={1,2,5} := by decide
    have hB : insert 4 ({2,5} : Finset (Fin 6))={2,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h50 : f {1,5}-f {1}-f {5}+f ∅=0 := by
    have h := hf 50
    change f (insert 1 (insert 5 (∅ : Finset (Fin 6))))-
      f (insert 1 (∅ : Finset (Fin 6)))-f (insert 5 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 1 (insert 5 (∅ : Finset (Fin 6)))={1,5} := by decide
    have hA : insert 1 (∅ : Finset (Fin 6))={1} := by decide
    have hB : insert 5 (∅ : Finset (Fin 6))={5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h51 : f {2,3}-f {2}-f {3}+f ∅=0 := by
    have h := hf 51
    change f (insert 2 (insert 3 (∅ : Finset (Fin 6))))-
      f (insert 2 (∅ : Finset (Fin 6)))-f (insert 3 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 2 (insert 3 (∅ : Finset (Fin 6)))={2,3} := by decide
    have hA : insert 2 (∅ : Finset (Fin 6))={2} := by decide
    have hB : insert 3 (∅ : Finset (Fin 6))={3} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h52 : f {2,3,4}-f {2,4}-f {3,4}+f {4}=0 := by
    have h := hf 52
    change f (insert 2 (insert 3 ({4} : Finset (Fin 6))))-
      f (insert 2 ({4} : Finset (Fin 6)))-f (insert 3 ({4} : Finset (Fin 6)))+f {4}=0 at h
    have hAB : insert 2 (insert 3 ({4} : Finset (Fin 6)))={2,3,4} := by decide
    have hA : insert 2 ({4} : Finset (Fin 6))={2,4} := by decide
    have hB : insert 3 ({4} : Finset (Fin 6))={3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h53 : f {0,1,2,3,4}-f {0,1,2,4}-f {0,1,3,4}+f {0,1,4}=0 := by
    have h := hf 53
    change f (insert 2 (insert 3 ({0,1,4} : Finset (Fin 6))))-
      f (insert 2 ({0,1,4} : Finset (Fin 6)))-f (insert 3 ({0,1,4} : Finset (Fin 6)))+f {0,1,4}=0 at h
    have hAB : insert 2 (insert 3 ({0,1,4} : Finset (Fin 6)))={0,1,2,3,4} := by decide
    have hA : insert 2 ({0,1,4} : Finset (Fin 6))={0,1,2,4} := by decide
    have hB : insert 3 ({0,1,4} : Finset (Fin 6))={0,1,3,4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h54 : f {2,3,5}-f {2,5}-f {3,5}+f {5}=0 := by
    have h := hf 54
    change f (insert 2 (insert 3 ({5} : Finset (Fin 6))))-
      f (insert 2 ({5} : Finset (Fin 6)))-f (insert 3 ({5} : Finset (Fin 6)))+f {5}=0 at h
    have hAB : insert 2 (insert 3 ({5} : Finset (Fin 6)))={2,3,5} := by decide
    have hA : insert 2 ({5} : Finset (Fin 6))={2,5} := by decide
    have hB : insert 3 ({5} : Finset (Fin 6))={3,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h55 : f {2,3,4,5}-f {2,4,5}-f {3,4,5}+f {4,5}=0 := by
    have h := hf 55
    change f (insert 2 (insert 3 ({4,5} : Finset (Fin 6))))-
      f (insert 2 ({4,5} : Finset (Fin 6)))-f (insert 3 ({4,5} : Finset (Fin 6)))+f {4,5}=0 at h
    have hAB : insert 2 (insert 3 ({4,5} : Finset (Fin 6)))={2,3,4,5} := by decide
    have hA : insert 2 ({4,5} : Finset (Fin 6))={2,4,5} := by decide
    have hB : insert 3 ({4,5} : Finset (Fin 6))={3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h56 : f {0,2,3,4,5}-f {0,2,4,5}-f {0,3,4,5}+f {0,4,5}=0 := by
    have h := hf 56
    change f (insert 2 (insert 3 ({0,4,5} : Finset (Fin 6))))-
      f (insert 2 ({0,4,5} : Finset (Fin 6)))-f (insert 3 ({0,4,5} : Finset (Fin 6)))+f {0,4,5}=0 at h
    have hAB : insert 2 (insert 3 ({0,4,5} : Finset (Fin 6)))={0,2,3,4,5} := by decide
    have hA : insert 2 ({0,4,5} : Finset (Fin 6))={0,2,4,5} := by decide
    have hB : insert 3 ({0,4,5} : Finset (Fin 6))={0,3,4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h57 : f {2,4}-f {2}-f {4}+f ∅=0 := by
    have h := hf 57
    change f (insert 2 (insert 4 (∅ : Finset (Fin 6))))-
      f (insert 2 (∅ : Finset (Fin 6)))-f (insert 4 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 2 (insert 4 (∅ : Finset (Fin 6)))={2,4} := by decide
    have hA : insert 2 (∅ : Finset (Fin 6))={2} := by decide
    have hB : insert 4 (∅ : Finset (Fin 6))={4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h58 : f {2,4,5}-f {2,5}-f {4,5}+f {5}=0 := by
    have h := hf 58
    change f (insert 2 (insert 4 ({5} : Finset (Fin 6))))-
      f (insert 2 ({5} : Finset (Fin 6)))-f (insert 4 ({5} : Finset (Fin 6)))+f {5}=0 at h
    have hAB : insert 2 (insert 4 ({5} : Finset (Fin 6)))={2,4,5} := by decide
    have hA : insert 2 ({5} : Finset (Fin 6))={2,5} := by decide
    have hB : insert 4 ({5} : Finset (Fin 6))={4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h59 : f {2,5}-f {2}-f {5}+f ∅=0 := by
    have h := hf 59
    change f (insert 2 (insert 5 (∅ : Finset (Fin 6))))-
      f (insert 2 (∅ : Finset (Fin 6)))-f (insert 5 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 2 (insert 5 (∅ : Finset (Fin 6)))={2,5} := by decide
    have hA : insert 2 (∅ : Finset (Fin 6))={2} := by decide
    have hB : insert 5 (∅ : Finset (Fin 6))={5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h60 : f {3,4}-f {3}-f {4}+f ∅=0 := by
    have h := hf 60
    change f (insert 3 (insert 4 (∅ : Finset (Fin 6))))-
      f (insert 3 (∅ : Finset (Fin 6)))-f (insert 4 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 3 (insert 4 (∅ : Finset (Fin 6)))={3,4} := by decide
    have hA : insert 3 (∅ : Finset (Fin 6))={3} := by decide
    have hB : insert 4 (∅ : Finset (Fin 6))={4} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h61 : f {3,4,5}-f {3,5}-f {4,5}+f {5}=0 := by
    have h := hf 61
    change f (insert 3 (insert 4 ({5} : Finset (Fin 6))))-
      f (insert 3 ({5} : Finset (Fin 6)))-f (insert 4 ({5} : Finset (Fin 6)))+f {5}=0 at h
    have hAB : insert 3 (insert 4 ({5} : Finset (Fin 6)))={3,4,5} := by decide
    have hA : insert 3 ({5} : Finset (Fin 6))={3,5} := by decide
    have hB : insert 4 ({5} : Finset (Fin 6))={4,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h62 : f {0,1,3,5}-f {0,1,3}-f {0,1,5}+f {0,1}=0 := by
    have h := hf 62
    change f (insert 3 (insert 5 ({0,1} : Finset (Fin 6))))-
      f (insert 3 ({0,1} : Finset (Fin 6)))-f (insert 5 ({0,1} : Finset (Fin 6)))+f {0,1}=0 at h
    have hAB : insert 3 (insert 5 ({0,1} : Finset (Fin 6)))={0,1,3,5} := by decide
    have hA : insert 3 ({0,1} : Finset (Fin 6))={0,1,3} := by decide
    have hB : insert 5 ({0,1} : Finset (Fin 6))={0,1,5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have h63 : f {4,5}-f {4}-f {5}+f ∅=0 := by
    have h := hf 63
    change f (insert 4 (insert 5 (∅ : Finset (Fin 6))))-
      f (insert 4 (∅ : Finset (Fin 6)))-f (insert 5 (∅ : Finset (Fin 6)))+f ∅=0 at h
    have hAB : insert 4 (insert 5 (∅ : Finset (Fin 6)))={4,5} := by decide
    have hA : insert 4 (∅ : Finset (Fin 6))={4} := by decide
    have hB : insert 5 (∅ : Finset (Fin 6))={5} := by decide
    rw [hAB,hA,hB] at h
    exact h
  have v0 : f ∅=0 := by
    linear_combination h1
  have v1 : f {0}=0 := by
    linear_combination h2
  have v2 : f {1}=0 := by
    linear_combination h3
  have v3 : f {0,1}=0 := by
    linear_combination (-1) * h1 + h2 + h3 + h8
  have v4 : f {2}=0 := by
    linear_combination h4
  have v5 : f {0,2}=0 := by
    linear_combination (-1) * h1 + h2 + h4 + h16
  have v6 : f {1,2}=0 := by
    linear_combination (-1) * h1 + h3 + h4 + h36
  have v7 : f {0,1,2}=0 := by
    linear_combination (-2) * h1 + h2 + h3 + h4 + h9 + h16 + h36
  have v8 : f {3}=0 := by
    linear_combination h5
  have v9 : f {0,3}=0 := by
    linear_combination (-1) * h1 + h2 + h5 + h23
  have v10 : f {1,3}=0 := by
    linear_combination (-1) * h1 + h3 + h5 + h42
  have v11 : f {0,1,3}=0 := by
    linear_combination h0
  have v12 : f {2,3}=0 := by
    linear_combination (-1) * h1 + h4 + h5 + h51
  have v13 : f {0,2,3}=0 := by
    linear_combination (-2) * h1 + h2 + h4 + h5 + h17 + h23 + h51
  have v14 : f {1,2,3}=0 := by
    linear_combination (-2) * h1 + h3 + h4 + h5 + h37 + h42 + h51
  have v15 : f {0,1,2,3}=0 := by
    linear_combination h0 + (-1) * h1 + h4 + h18 + h37 + h51
  have v16 : f {4}=0 := by
    linear_combination h6
  have v17 : f {0,4}=0 := by
    linear_combination (-1) * h1 + h2 + h6 + h28
  have v18 : f {1,4}=0 := by
    linear_combination (-1) * h1 + h3 + h6 + h46
  have v19 : f {0,1,4}=0 := by
    linear_combination (-2) * h1 + h2 + h3 + h6 + h10 + h28 + h46
  have v20 : f {2,4}=0 := by
    linear_combination (-1) * h1 + h4 + h6 + h57
  have v21 : f {0,2,4}=0 := by
    linear_combination (-2) * h1 + h2 + h4 + h6 + h19 + h28 + h57
  have v22 : f {1,2,4}=0 := by
    linear_combination (-2) * h1 + h3 + h4 + h6 + h38 + h46 + h57
  have v23 : f {0,1,2,4}=0 := by
    linear_combination h0 + (-1) * h1 + h4 + (-1) * h5 + h6 + h10 + (-1) * h12 + (-1) * h14 + h15 + h21 + (-2) * h25 + h26 + h28 + (-1) * h29 + (-1) * h30 + h31 + h32 + (-1) * h33 + (2) * h34 + (-1) * h35 + h39 + (-1) * h42 + h46 + h52 + (-1) * h53 + (-1) * h55 + h56 + h57
  have v24 : f {3,4}=0 := by
    linear_combination (-1) * h1 + h5 + h6 + h60
  have v25 : f {0,3,4}=0 := by
    linear_combination h0 + (-1) * h3 + h6 + (-1) * h11 + h29 + (-1) * h42 + h60
  have v26 : f {1,3,4}=0 := by
    linear_combination h0 + (-1) * h2 + h6 + (-1) * h11 + (-1) * h23 + h47 + h60
  have v27 : f {0,1,3,4}=0 := by
    linear_combination (2) * h0 + h1 + (-1) * h2 + (-1) * h3 + (-1) * h5 + h6 + (-1) * h11 + (-1) * h23 + h29 + (-1) * h42 + h47 + h60
  have v28 : f {2,3,4}=0 := by
    linear_combination (-2) * h1 + h4 + h5 + h6 + h52 + h57 + h60
  have v29 : f {0,2,3,4}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h3 + h4 + h6 + (-1) * h11 + h20 + h29 + (-1) * h42 + h52 + h57 + h60
  have v30 : f {1,2,3,4}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h2 + h4 + h6 + (-1) * h11 + (-1) * h23 + h39 + h47 + h52 + h57 + h60
  have v31 : f {0,1,2,3,4}=0 := by
    linear_combination (3) * h0 + (2) * h1 + (-2) * h2 + (-2) * h3 + h4 + (-2) * h5 + h6 + (-1) * h11 + (-1) * h12 + (-1) * h14 + h15 + h21 + (-1) * h23 + (-2) * h25 + h26 + (-1) * h30 + h31 + h32 + (-1) * h33 + (2) * h34 + (-1) * h35 + h39 + (-2) * h42 + h47 + h52 + (-1) * h55 + h56 + h57 + h60
  have v32 : f {5}=0 := by
    linear_combination h7
  have v33 : f {0,5}=0 := by
    linear_combination (-1) * h1 + h2 + h7 + h33
  have v34 : f {1,5}=0 := by
    linear_combination (-1) * h1 + h3 + h7 + h50
  have v35 : f {0,1,5}=0 := by
    linear_combination h0 + (-1) * h5 + h7 + (-1) * h25 + h34 + (-1) * h42 + h50
  have v36 : f {2,5}=0 := by
    linear_combination (-1) * h1 + h4 + h7 + h59
  have v37 : f {0,2,5}=0 := by
    linear_combination h0 + (-1) * h3 + h4 + (-1) * h5 + h7 + (-1) * h12 + h21 + (-1) * h25 + h34 + (-1) * h42 + h59
  have v38 : f {1,2,5}=0 := by
    linear_combination h0 + (-1) * h2 + h4 + (-1) * h5 + h7 + (-1) * h12 + (-1) * h25 + (-1) * h33 + h34 + h40 + (-1) * h42 + h50 + h59
  have v39 : f {0,1,2,5}=0 := by
    linear_combination (2) * h0 + h1 + (-1) * h2 + (-1) * h3 + h4 + (-2) * h5 + h7 + (-1) * h12 + h21 + (-2) * h25 + (-1) * h33 + (2) * h34 + h40 + (-2) * h42 + h50 + h59
  have v40 : f {3,5}=0 := by
    linear_combination h0 + h1 + (-1) * h2 + (-1) * h3 + h7 + (-1) * h8 + (-1) * h25 + (-1) * h43 + h62
  have v41 : f {0,3,5}=0 := by
    linear_combination h0 + (-1) * h3 + h7 + (-1) * h8 + h24 + (-1) * h25 + h33 + (-1) * h43 + h62
  have v42 : f {1,3,5}=0 := by
    linear_combination h0 + (-1) * h2 + h7 + (-1) * h8 + (-1) * h25 + h50 + h62
  have v43 : f {0,1,3,5}=0 := by
    linear_combination (2) * h0 + h1 + (-1) * h2 + (-1) * h3 + (-1) * h5 + h7 + (-1) * h8 + (-1) * h25 + h34 + (-1) * h42 + h50 + h62
  have v44 : f {2,3,5}=0 := by
    linear_combination h0 + (-1) * h2 + (-1) * h3 + h4 + h7 + (-1) * h8 + (-1) * h25 + (-1) * h43 + h54 + h59 + h62
  have v45 : f {0,2,3,5}=0 := by
    linear_combination (2) * h0 + h1 + (-1) * h2 + (-2) * h3 + h4 + (-1) * h5 + h7 + (-1) * h8 + (-1) * h13 + h22 + (-1) * h25 + h34 + (-1) * h42 + (-1) * h43 + h54 + h59 + h62
  have v46 : f {1,2,3,5}=0 := by
    linear_combination (2) * h0 + h1 + (-2) * h2 + (-1) * h3 + h4 + (-1) * h5 + h7 + (-1) * h8 + (-1) * h13 + (-1) * h24 + (-1) * h25 + (-1) * h33 + h34 + h41 + (-1) * h42 + h50 + h54 + h59 + h62
  have v47 : f {0,1,2,3,5}=0 := by
    linear_combination (3) * h0 + (2) * h1 + (-2) * h2 + (-2) * h3 + h4 + (-2) * h5 + h7 + (-1) * h8 + (-1) * h13 + h22 + (-1) * h24 + (-1) * h25 + (-1) * h33 + (2) * h34 + h41 + (-2) * h42 + h50 + h54 + h59 + h62
  have v48 : f {4,5}=0 := by
    linear_combination (-1) * h1 + h6 + h7 + h63
  have v49 : f {0,4,5}=0 := by
    linear_combination (-2) * h1 + h2 + h6 + h7 + h30 + h33 + h63
  have v50 : f {1,4,5}=0 := by
    linear_combination (-2) * h1 + h3 + h6 + h7 + h48 + h50 + h63
  have v51 : f {0,1,4,5}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h5 + h6 + h7 + (-1) * h25 + h31 + h34 + (-1) * h42 + h48 + h50 + h63
  have v52 : f {2,4,5}=0 := by
    linear_combination (-2) * h1 + h4 + h6 + h7 + h58 + h59 + h63
  have v53 : f {0,2,4,5}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h3 + h4 + (-1) * h5 + h6 + h7 + (-1) * h12 + h21 + (-1) * h25 + h32 + h34 + (-1) * h42 + h58 + h59 + h63
  have v54 : f {1,2,4,5}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h2 + h4 + (-1) * h5 + h6 + h7 + (-1) * h12 + (-1) * h25 + (-1) * h33 + h34 + h40 + (-1) * h42 + h49 + h50 + h58 + h59 + h63
  have v55 : f {0,1,2,4,5}=0 := by
    linear_combination (3) * h0 + (2) * h1 + (-2) * h2 + (-2) * h3 + h4 + (-3) * h5 + h6 + h7 + (-2) * h12 + (-1) * h14 + h15 + h21 + (-3) * h25 + h26 + (-1) * h27 + (-1) * h30 + h31 + h32 + (-2) * h33 + (3) * h34 + h40 + (-3) * h42 + h49 + h50 + (-1) * h55 + h56 + h58 + h59 + h63
  have v56 : f {3,4,5}=0 := by
    linear_combination h0 + (-1) * h2 + (-1) * h3 + h6 + h7 + (-1) * h8 + (-1) * h25 + (-1) * h43 + h61 + h62 + h63
  have v57 : f {0,3,4,5}=0 := by
    linear_combination (2) * h0 + h1 + (-1) * h2 + (-2) * h3 + (-1) * h5 + h6 + h7 + (-1) * h8 + (-1) * h14 + (-2) * h25 + h26 + h31 + h34 + (-1) * h42 + (-1) * h43 + h61 + h62 + h63
  have v58 : f {1,3,4,5}=0 := by
    linear_combination (2) * h0 + h1 + (-2) * h2 + (-1) * h3 + (-1) * h5 + h6 + h7 + (-1) * h8 + (-1) * h14 + (-2) * h25 + (-1) * h30 + h31 + (-1) * h33 + h34 + (-1) * h42 + (-1) * h43 + h44 + h48 + h50 + h61 + h62 + h63
  have v59 : f {0,1,3,4,5}=0 := by
    linear_combination (3) * h0 + (2) * h1 + (-2) * h2 + (-2) * h3 + (-2) * h5 + h6 + h7 + (-1) * h8 + (-1) * h14 + (-3) * h25 + h26 + (-1) * h30 + (2) * h31 + (-1) * h33 + (2) * h34 + (-2) * h42 + (-1) * h43 + h44 + h48 + h50 + h61 + h62 + h63
  have v60 : f {2,3,4,5}=0 := by
    linear_combination h0 + (-1) * h1 + (-1) * h2 + (-1) * h3 + h4 + h6 + h7 + (-1) * h8 + (-1) * h25 + (-1) * h43 + h55 + h58 + h59 + h61 + h62 + h63
  have v61 : f {0,2,3,4,5}=0 := by
    linear_combination (3) * h0 + (2) * h1 + (-2) * h2 + (-3) * h3 + h4 + (-2) * h5 + h6 + h7 + (-1) * h8 + (-1) * h12 + (-1) * h14 + h21 + (-3) * h25 + h26 + (-1) * h30 + h31 + h32 + (-1) * h33 + (2) * h34 + (-2) * h42 + (-1) * h43 + h56 + h58 + h59 + h61 + h62 + h63
  have v62 : f {1,2,3,4,5}=0 := by
    linear_combination (3) * h0 + (2) * h1 + (-3) * h2 + (-2) * h3 + h4 + (-2) * h5 + h6 + h7 + (-1) * h8 + (-1) * h12 + (-1) * h14 + (-3) * h25 + h26 + (-1) * h27 + (-1) * h30 + h31 + (-2) * h33 + (2) * h34 + h40 + (-2) * h42 + (-1) * h43 + h45 + h49 + h50 + h56 + h58 + h59 + h61 + h62 + h63
  have v63 : f {0,1,2,3,4,5}=0 := by
    linear_combination (5) * h0 + (5) * h1 + (-4) * h2 + (-4) * h3 + h4 + (-4) * h5 + h6 + h7 + (-1) * h8 + (-2) * h12 + (-2) * h14 + h15 + h21 + (-5) * h25 + (2) * h26 + (-1) * h27 + (-2) * h30 + (2) * h31 + h32 + (-3) * h33 + (4) * h34 + h40 + (-4) * h42 + (-1) * h43 + h45 + h49 + h50 + (-1) * h55 + (2) * h56 + h58 + h59 + h61 + h62 + h63
  funext S
  change f S=0
  have casesS : ∀ S : Finset (Fin 6), S=∅ ∨ S={0} ∨ S={1} ∨ S={0,1} ∨ S={2} ∨ S={0,2} ∨ S={1,2} ∨ S={0,1,2} ∨ S={3} ∨ S={0,3} ∨ S={1,3} ∨ S={0,1,3} ∨ S={2,3} ∨ S={0,2,3} ∨ S={1,2,3} ∨ S={0,1,2,3} ∨ S={4} ∨ S={0,4} ∨ S={1,4} ∨ S={0,1,4} ∨ S={2,4} ∨ S={0,2,4} ∨ S={1,2,4} ∨ S={0,1,2,4} ∨ S={3,4} ∨ S={0,3,4} ∨ S={1,3,4} ∨ S={0,1,3,4} ∨ S={2,3,4} ∨ S={0,2,3,4} ∨ S={1,2,3,4} ∨ S={0,1,2,3,4} ∨ S={5} ∨ S={0,5} ∨ S={1,5} ∨ S={0,1,5} ∨ S={2,5} ∨ S={0,2,5} ∨ S={1,2,5} ∨ S={0,1,2,5} ∨ S={3,5} ∨ S={0,3,5} ∨ S={1,3,5} ∨ S={0,1,3,5} ∨ S={2,3,5} ∨ S={0,2,3,5} ∨ S={1,2,3,5} ∨ S={0,1,2,3,5} ∨ S={4,5} ∨ S={0,4,5} ∨ S={1,4,5} ∨ S={0,1,4,5} ∨ S={2,4,5} ∨ S={0,2,4,5} ∨ S={1,2,4,5} ∨ S={0,1,2,4,5} ∨ S={3,4,5} ∨ S={0,3,4,5} ∨ S={1,3,4,5} ∨ S={0,1,3,4,5} ∨ S={2,3,4,5} ∨ S={0,2,3,4,5} ∨ S={1,2,3,4,5} ∨ S={0,1,2,3,4,5} := by decide
  rcases casesS S with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem empty_zero : integerFunction ∅=0 := by decide

theorem singleton_zero : ∀ v : Fin 6,integerFunction {v}=0 := by decide

theorem boolean_differences : ∀ u v : Fin 6,u≠ v → ∀ S : Finset (Fin 6),
    u∉S → v∉S → integerDelta integerFunction u v S=0 ∨
      integerDelta integerFunction u v S=1 := by decide

theorem extreme : ExtremeSupermodular (realFunction integerFunction) :=
  extreme_of_row_kernel integerFunction rows pivot pivot_one row_zero valid_rows
    row_kernel_zero empty_zero singleton_zero boolean_differences

end K1122Complement

end SmallBoolean
end GraphicalZonotopes

end
end
end BundlePart33

section BundlePart34
/- Source: Papers/GraphicalZonotopes/SetFunctionEmbedding.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace SetFunctionEmbedding
open Finset
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

def pullSet (e : W ↪ V) (S : Finset V) : Finset W :=
  univ.filter fun w => e w∈S

@[simp] theorem mem_pullSet (e : W ↪ V) (S : Finset V) (w : W) :
    w∈pullSet e S ↔ e w∈S := by simp [pullSet]

@[simp] theorem pullSet_empty (e : W ↪ V) : pullSet e ∅=∅ := by
  ext w
  simp

@[simp] theorem pullSet_map (e : W ↪ V) (S : Finset W) : pullSet e (S.map e)=S := by
  ext w
  simp

@[simp] theorem pullSet_insert_image (e : W ↪ V) (w : W) (S : Finset V) :
    pullSet e (insert (e w) S)=insert w (pullSet e S) := by
  ext x
  simp [e.injective.eq_iff]

theorem pullSet_insert_not_range (e : W ↪ V) (v : V) (hv : v∉Set.range e)
    (S : Finset V) : pullSet e (insert v S)=pullSet e S := by
  ext w
  have h : e w≠ v := fun he => hv ⟨w,he⟩
  simp [h]

@[simp] theorem pullSet_union (e : W ↪ V) (S T : Finset V) :
    pullSet e (S∪T)=pullSet e S∪pullSet e T := by ext w; simp

@[simp] theorem pullSet_inter (e : W ↪ V) (S T : Finset V) :
    pullSet e (S∩T)=pullSet e S∩pullSet e T := by ext w; simp

def restrict (e : W ↪ V) (f : SetFunction V) : SetFunction W := fun S => f (S.map e)
def extend (e : W ↪ V) (f : SetFunction W) : SetFunction V := fun S => f (pullSet e S)

@[simp] theorem restrict_smul (e : W ↪ V) (c : ℝ) (f : SetFunction V) :
    restrict e (c • f)=c • restrict e f := rfl

@[simp] theorem extend_smul (e : W ↪ V) (c : ℝ) (f : SetFunction W) :
    extend e (c • f)=c • extend e f := rfl

@[simp] theorem extend_sub (e : W ↪ V) (f g : SetFunction W) :
    extend e (f-g)=extend e f-extend e g := rfl

@[simp] theorem restrict_extend (e : W ↪ V) (f : SetFunction W) :
    restrict e (extend e f)=f := by funext S; simp [restrict,extend]

theorem extend_injective (e : W ↪ V) : Function.Injective (extend e) := by
  intro f g he
  have h := congrArg (restrict e) he
  simpa using h

theorem restrict_translationNormalized (e : W ↪ V) {f : SetFunction V}
    (hf : TranslationNormalized f) : TranslationNormalized (restrict e f) := by
  exact ⟨by simpa [Normalized,restrict] using hf.1,fun w => by simpa [restrict] using hf.2 (e w)⟩

theorem extend_translationNormalized (e : W ↪ V) {f : SetFunction W}
    (hf : TranslationNormalized f) : TranslationNormalized (extend e f) := by
  refine ⟨by simpa [Normalized,extend] using hf.1,?_⟩
  intro v
  by_cases hv : v∈Set.range e
  · obtain ⟨w,rfl⟩ := hv
    change f (pullSet e (insert (e w) ∅))=0
    rw [pullSet_insert_image,pullSet_empty]
    exact hf.2 w
  · change f (pullSet e (insert v ∅))=0
    rw [pullSet_insert_not_range e v hv,pullSet_empty]
    exact hf.1

theorem delta_restrict (e : W ↪ V) (f : SetFunction V) (u v : W) (S : Finset W) :
    delta (restrict e f) u v S=delta f (e u) (e v) (S.map e) := by
  simp only [delta,restrict,map_insert]

theorem delta_extend (e : W ↪ V) (f : SetFunction W) (u v : W) (S : Finset V) :
    delta (extend e f) (e u) (e v) S=delta f u v (pullSet e S) := by
  simp only [delta,extend,pullSet_insert_image]

theorem delta_extend_not_range (e : W ↪ V) (f : SetFunction W) (u v : V)
    (hu : u∉Set.range e) (S : Finset V) : delta (extend e f) u v S=0 := by
  simp only [delta,extend,pullSet_insert_not_range e u hu]
  ring

theorem restrict_graphical (e : W ↪ V) {G : SimpleGraph V} {f : SetFunction V}
    (hf : Graphical G f) : Graphical (G.comap e) (restrict e f) := by
  intro u v huv hnon S hu hv
  rw [delta_restrict]
  exact hf (e u) (e v) (fun h => huv (e.injective h)) hnon _
    (by simpa using hu) (by simpa using hv)

theorem extend_graphical (e : W ↪ V) {G : SimpleGraph V} {f : SetFunction W}
    (hf : Graphical (G.comap e) f) : Graphical G (extend e f) := by
  intro u v huv hnon S hu hv
  by_cases huR : u∈Set.range e
  · obtain ⟨a,rfl⟩ := huR
    by_cases hvR : v∈Set.range e
    · obtain ⟨b,rfl⟩ := hvR
      rw [delta_extend]
      exact hf a b (fun he => huv (congrArg e he)) hnon _
        (by simpa using hu) (by simpa using hv)
    · rw [delta_comm]
      exact delta_extend_not_range e f v (e a) hvR S
  · exact delta_extend_not_range e f u v huR S

theorem restrict_supermodular (e : W ↪ V) {f : SetFunction V}
    (hf : Supermodular f) : Supermodular (restrict e f) := by
  intro S T
  simpa only [restrict,map_union,map_inter] using hf (S.map e) (T.map e)

theorem extend_supermodular (e : W ↪ V) {f : SetFunction W}
    (hf : Supermodular f) : Supermodular (extend e f) := by
  intro S T
  simpa only [extend,pullSet_union,pullSet_inter] using hf (pullSet e S) (pullSet e T)

theorem extend_insert_absent (e : W ↪ V) (f : SetFunction W) (v : V)
    (hv : v∉Set.range e) (S : Finset V) : extend e f (insert v S)=extend e f S := by
  simp only [extend,pullSet_insert_not_range e v hv]

/-- Restriction preserves exact Möbius coefficients on every retained
subset; no maximal-clique or cardinality assumption is needed. -/
theorem mobius_restrict (e : W ↪ V) (f : SetFunction V) (C : Finset W) :
    mobius (restrict e f) C=mobius f (C.map e) := by
  have hsum (S : Finset W) :
      zeta (fun T => mobius f (T.map e)) S=f (S.map e) := by
    conv_rhs => rw [← zeta_mobius f]
    unfold zeta
    apply sum_bij (fun T _ => T.map e)
    · intro T hT
      exact mem_powerset.mpr ((map_subset_map).mpr (mem_powerset.mp hT))
    · intro T hT U hU he
      exact Finset.map_injective e he
    · intro T hT
      refine ⟨pullSet e T,?_,?_⟩
      · apply mem_powerset.mpr
        intro w hw
        have h := (mem_powerset.mp hT) ((mem_pullSet e T w).mp hw)
        simpa using h
      · ext v
        constructor
        · rintro hv
          obtain ⟨w,hw,rfl⟩ := mem_map.mp hv
          exact (mem_pullSet e T w).mp hw
        · intro hv
          obtain ⟨w,hw,rfl⟩ := mem_map.mp ((mem_powerset.mp hT) hv)
          exact mem_map.mpr ⟨w,(mem_pullSet e T w).mpr hv,rfl⟩
    · intro T hT
      rfl
  have he : zeta (fun T => mobius f (T.map e))=restrict e f := funext hsum
  have h := congrArg mobius he
  rw [mobius_zeta] at h
  exact congrFun h.symm C

end SetFunctionEmbedding
end GraphicalZonotopes

end
end
end BundlePart34

