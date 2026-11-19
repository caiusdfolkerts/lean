module

public import canonical_main.PalomarPart001
import all canonical_main.PalomarPart001
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

section BundlePart90
/- Source: Papers/GraphicalZonotopes/Gluing.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-!
An abstract finite-inequality version of positive response gluing. Internal rows
and all boundary choices are retained. The private hypothesis is the actual kernel
of internal zero rows and differences of minimizing boundary rows.
-/
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Gluing
open Finset
open scoped BigOperators

variable {B J D : Type*} {K I X : J → Type*}
variable [Fintype B] [Fintype J] [Fintype D]
variable [∀ j, Fintype (K j)] [∀ j, Fintype (I j)] [∀ j, Fintype (X j)]
variable [DecidableEq J]

abbrev Global (J : Type*) (K : J → Type*) (D : Type*) := (D → ℝ) × (∀ j, K j → ℝ)
abbrev Row (B J : Type*) (I X : J → Type*) := (Σ j, I j) ⊕ (B × (∀ j, X j))

structure Data (B J : Type*) (K : J → Type*) (D : Type*) (I X : J → Type*) where
  boundary : (D → ℝ) →ₗ[ℝ] (B → ℝ)
  internal : (j : J) → I j → (K j → ℝ) →ₗ[ℝ] ℝ
  response : (j : J) → B → X j → (K j → ℝ) →ₗ[ℝ] ℝ

def Data.row (M : Data B J K D I X) : Row B J I X → Global J K D →ₗ[ℝ] ℝ
  | Sum.inl ⟨j, i⟩ =>
    { toFun := fun y => M.internal j i (y.2 j)
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  | Sum.inr (b, x) =>
    { toFun := fun y => M.boundary y.1 b + ∑ j, M.response j b (x j) (y.2 j)
      map_add' := by intros; simp [Finset.sum_add_distrib]; ring
      map_smul' a y := by
        change M.boundary (a • y.1) b + (∑ j, M.response j b (x j) (a • y.2 j)) =
          a * (M.boundary y.1 b + ∑ j, M.response j b (x j) (y.2 j))
        simp only [map_smul, Pi.smul_apply, smul_eq_mul]
        rw [mul_add, Finset.mul_sum] }

/-- The complete private equations at a branch point. -/
def Data.PrivateKernel (M : Data B J K D I X) (f : ∀ j, K j → ℝ) (m : J → B → ℝ)
    (j : J) (g : K j → ℝ) : Prop :=
  (∀ i, M.internal j i (f j) = 0 → M.internal j i g = 0) ∧
    ∀ b x y, M.response j b x (f j) = m j b → M.response j b y (f j) = m j b →
      M.response j b x g = M.response j b y g

def Data.Closure (M : Data B J K D I X) (m : J → B → ℝ)
    (z : D → ℝ) (c : J → ℝ) : Prop :=
  ∀ b, M.boundary z b + ∑ j, c j * m j b = 0

def assemble (z : D → ℝ) (c : J → ℝ) (f : ∀ j, K j → ℝ) : Global J K D :=
  (z, fun j => c j • f j)

variable (M : Data B J K D I X) (f : ∀ j, K j → ℝ) (m : J → B → ℝ)
variable (hmin : ∀ j b x, m j b ≤ M.response j b x (f j))
variable (hatt : ∀ j b, ∃ x, M.response j b x (f j) = m j b)
variable (hinternal : ∀ j i, 0 ≤ M.internal j i (f j))
variable (z : D → ℝ) (lam : J → ℝ) (hlam : ∀ j, 0 < lam j)
variable (hclose : M.Closure m z lam)

include hclose in
/-- The closing relation turns every boundary row into a sum of nonnegative
excesses above genuine conditional minima. -/
theorem row_boundary_eq_excess (b : B) (x : ∀ j, X j) :
    M.row (Sum.inr (b, x)) (assemble z lam f) =
      ∑ j, lam j * (M.response j b (x j) (f j) - m j b) := by
  have hc := hclose b
  simp only [Data.row, assemble, LinearMap.coe_mk, AddHom.coe_mk,
    map_smul, smul_eq_mul, Pi.smul_apply]
  simp only [mul_sub, sum_sub_distrib]
  linarith

include hmin hinternal hlam hclose in
theorem assembled_nonnegative : Polyhedral.Nonnegative M.row (assemble z lam f) := by
  intro r
  rcases r with ⟨j, i⟩ | ⟨b, x⟩
  · change 0 ≤ M.internal j i (lam j • f j)
    rw [map_smul, smul_eq_mul]
    exact mul_nonneg (hlam j).le (hinternal j i)
  · rw [row_boundary_eq_excess M f m z lam hclose]
    apply sum_nonneg
    intro j hj
    exact mul_nonneg (hlam j).le (sub_nonneg.mpr (hmin j b (x j)))

include hmin hlam hclose in
/-- With strictly positive branch scales, a boundary row is tight exactly when
each branch independently minimizes its contribution. -/
theorem boundary_tight_iff (b : B) (x : ∀ j, X j) :
    M.row (Sum.inr (b, x)) (assemble z lam f) = 0 ↔
      ∀ j, M.response j b (x j) (f j) = m j b := by
  rw [row_boundary_eq_excess M f m z lam hclose]
  have hnn : ∀ j ∈ (univ : Finset J), 0 ≤ lam j * (M.response j b (x j) (f j) - m j b) :=
    fun j _ => mul_nonneg (hlam j).le (sub_nonneg.mpr (hmin j b (x j)))
  rw [sum_eq_zero_iff_of_nonneg hnn]
  constructor
  · intro h j
    have hj := h j (mem_univ j)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hj).resolve_left (ne_of_gt (hlam j)))
  · intro h j hj
    rw [h j, sub_self, mul_zero]

/-- Varying only one branch choice isolates exactly that branch's response
change. This uses every global boundary row, not a selected submatrix. -/
theorem row_boundary_update_difference (g : Global J K D) (b : B) (x : ∀ j, X j)
    (j : J) (a a' : X j) :
    M.row (Sum.inr (b, Function.update x j a)) g -
      M.row (Sum.inr (b, Function.update x j a')) g =
        M.response j b a (g.2 j) - M.response j b a' (g.2 j) := by
  classical
  simp only [Data.row, LinearMap.coe_mk, AddHom.coe_mk]
  rw [show (M.boundary g.1 b + ∑ k, M.response k b (Function.update x j a k) (g.2 k)) -
      (M.boundary g.1 b + ∑ k, M.response k b (Function.update x j a' k) (g.2 k)) =
        ∑ k, (M.response k b (Function.update x j a k) (g.2 k) -
          M.response k b (Function.update x j a' k) (g.2 k)) by rw [sum_sub_distrib]; ring]
  rw [sum_eq_single j]
  · simp
  · intro k hk hkj
    simp [Function.update_of_ne hkj]
  · simp

include hmin hatt hlam hclose in
/-- Every branch's complete private equations are inherited from the complete
global tight kernel. -/
theorem privateKernel_of_global {g : Global J K D}
    (hg : g ∈ Polyhedral.tightKernel M.row (assemble z lam f)) (j : J) :
    M.PrivateKernel f m j (g.2 j) := by
  classical
  refine ⟨?_, ?_⟩
  · intro i hi
    have hrow : M.row (Sum.inl ⟨j, i⟩) (assemble z lam f) = 0 := by
      change M.internal j i (lam j • f j) = 0
      rw [map_smul, hi, smul_zero]
    exact hg _ hrow
  · intro b a a' ha ha'
    choose x hx using fun k : J => hatt k b
    have hx1 : ∀ k, M.response k b (Function.update x j a k) (f k) = m k b := by
      intro k
      by_cases hkj : k = j
      · subst k; simpa using ha
      · simpa [Function.update_of_ne hkj] using hx k
    have hx2 : ∀ k, M.response k b (Function.update x j a' k) (f k) = m k b := by
      intro k
      by_cases hkj : k = j
      · subst k; simpa using ha'
      · simpa [Function.update_of_ne hkj] using hx k
    have h1 := hg _ ((boundary_tight_iff M f m hmin z lam hlam hclose b _).mpr hx1)
    have h2 := hg _ ((boundary_tight_iff M f m hmin z lam hlam hclose b _).mpr hx2)
    have hdiff := row_boundary_update_difference M g b x j a a'
    rw [h1, h2] at hdiff
    linarith

variable (hprivate : ∀ j g, M.PrivateKernel f m j g → ∃ c : ℝ, g = c • f j)

include hmin hatt hlam hclose hprivate in
/-- Exact reconstruction of the complete tight kernel by branch scales and
boundary closure, including all boundary and all unused private coordinates. -/
theorem tightKernel_iff {g : Global J K D} :
    g ∈ Polyhedral.tightKernel M.row (assemble z lam f) ↔
      ∃ c : J → ℝ, (∀ j, g.2 j = c j • f j) ∧ M.Closure m g.1 c := by
  constructor
  · intro hg
    have hsc : ∀ j, ∃ c : ℝ, g.2 j = c • f j :=
      fun j => hprivate j (g.2 j) (privateKernel_of_global M f m hmin hatt z lam hlam hclose hg j)
    choose c hc using hsc
    refine ⟨c, hc, ?_⟩
    intro b
    choose x hx using fun j : J => hatt j b
    have ht := (boundary_tight_iff M f m hmin z lam hlam hclose b x).mpr hx
    have hgzero := hg _ ht
    change M.boundary g.1 b + ∑ j, M.response j b (x j) (g.2 j) = 0 at hgzero
    simpa only [hc, map_smul, smul_eq_mul, hx] using hgzero
  · rintro ⟨c, hc, hcl⟩ r hr
    rcases r with ⟨j, i⟩ | ⟨b, x⟩
    · change M.internal j i (lam j • f j) = 0 at hr
      rw [map_smul, smul_eq_mul] at hr
      have hi := (mul_eq_zero.mp hr).resolve_left (ne_of_gt (hlam j))
      change M.internal j i (g.2 j) = 0
      rw [hc j, map_smul, hi, smul_zero]
    · have hx := (boundary_tight_iff M f m hmin z lam hlam hclose b x).mp hr
      change M.boundary g.1 b + ∑ j, M.response j b (x j) (g.2 j) = 0
      simpa only [hc, map_smul, smul_eq_mul, hx] using hcl b


def responseLinear (m : J → B → ℝ) : (J → ℝ) →ₗ[ℝ] (B → ℝ) where
  toFun c := fun b => ∑ j, c j * m j b
  map_add' c d := by ext b; simp [add_mul, sum_add_distrib]
  map_smul' a c := by ext b; simp [mul_assoc, mul_sum]

def Data.closureLinear (M : Data B J K D I X) (m : J → B → ℝ) :
    ((D → ℝ) × (J → ℝ)) →ₗ[ℝ] (B → ℝ) where
  toFun y := M.boundary y.1 + responseLinear m y.2
  map_add' x y := by simp; abel
  map_smul' a x := by simp [smul_add]

def Data.closedRelations (M : Data B J K D I X) (m : J → B → ℝ) :
    Submodule ℝ ((D → ℝ) × (J → ℝ)) := LinearMap.ker (M.closureLinear m)

@[simp] theorem mem_closedRelations (w : D → ℝ) (c : J → ℝ) :
    (w, c) ∈ M.closedRelations m ↔ M.Closure m w c := by
  simp only [Data.closedRelations, LinearMap.mem_ker, Data.closureLinear,
    LinearMap.coe_mk, AddHom.coe_mk, Data.Closure, responseLinear, Pi.add_apply,
    funext_iff, Pi.zero_apply]

def Data.relationLinear (M : Data B J K D I X) (m : J → B → ℝ) :
    (J → ℝ) →ₗ[ℝ] ((B → ℝ) ⧸ LinearMap.range M.boundary) :=
  (LinearMap.range M.boundary).mkQ ∘ₗ responseLinear m

theorem closure_mem_relationKernel {w : D → ℝ} {c : J → ℝ}
    (hc : M.Closure m w c) : c ∈ LinearMap.ker (M.relationLinear m) := by
  change (LinearMap.range M.boundary).mkQ (responseLinear m c) = 0
  rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
  refine ⟨-w, ?_⟩
  ext b
  have h := hc b
  simp only [map_neg, Pi.neg_apply, responseLinear, LinearMap.coe_mk, AddHom.coe_mk]
  linarith

theorem exists_closure_of_relationKernel {c : J → ℝ}
    (hc : c ∈ LinearMap.ker (M.relationLinear m)) : ∃ w, M.Closure m w c := by
  change (LinearMap.range M.boundary).mkQ (responseLinear m c) = 0 at hc
  rw [← LinearMap.mem_ker, Submodule.ker_mkQ] at hc
  obtain ⟨w, hw⟩ := hc
  refine ⟨-w, ?_⟩
  intro b
  have h := congrFun hw b
  simp only [map_neg, Pi.neg_apply, responseLinear, LinearMap.coe_mk, AddHom.coe_mk] at h ⊢
  linarith

variable (hfinj : ∀ j, f j ≠ 0)

def closedToTight : M.closedRelations m →ₗ[ℝ]
    Polyhedral.tightKernel M.row (assemble z lam f) where
  toFun y := ⟨assemble y.1.1 y.1.2 f,
    (tightKernel_iff M f m hmin hatt z lam hlam hclose hprivate).mpr
      ⟨y.1.2, fun _ => rfl, (mem_closedRelations M m _ _).mp y.2⟩⟩
  map_add' x y := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · ext j k
      simp [assemble, add_smul]
  map_smul' a x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · ext j k
      simp [assemble, smul_smul, mul_assoc]

include hfinj in
theorem closedToTight_injective : Function.Injective
    (closedToTight M f m hmin hatt z lam hlam hclose hprivate) := by
  intro x y hxy
  have he := congrArg Subtype.val hxy
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun w : Global J K D => w.1) he
  · funext j
    have h := congrArg (fun w : Global J K D => w.2 j) he
    change x.1.2 j • f j = y.1.2 j • f j at h
    have hnonzero : ∃ k, f j k ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact hfinj j (funext hn)
    obtain ⟨k, hk⟩ := hnonzero
    have hh := congrFun h k
    simp only [Pi.smul_apply, smul_eq_mul] at hh
    exact mul_right_cancel₀ hk hh

theorem closedToTight_surjective : Function.Surjective
    (closedToTight M f m hmin hatt z lam hlam hclose hprivate) := by
  intro g
  obtain ⟨c, hc, hcl⟩ := (tightKernel_iff M f m hmin hatt z lam hlam hclose hprivate).mp g.2
  refine ⟨⟨(g.1.1, c), (mem_closedRelations M m _ _).mpr hcl⟩, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · funext j
    exact (hc j).symm

def closedTightEquiv : M.closedRelations m ≃ₗ[ℝ]
    Polyhedral.tightKernel M.row (assemble z lam f) :=
  LinearEquiv.ofBijective (closedToTight M f m hmin hatt z lam hlam hclose hprivate)
    ⟨closedToTight_injective M f m hmin hatt z lam hlam hclose hprivate hfinj,
      closedToTight_surjective M f m hmin hatt z lam hlam hclose hprivate⟩

variable (hboundary : Function.Injective M.boundary)

def closedToRelation : M.closedRelations m →ₗ[ℝ] LinearMap.ker (M.relationLinear m) where
  toFun y := ⟨y.1.2, closure_mem_relationKernel M m ((mem_closedRelations M m _ _).mp y.2)⟩
  map_add' x y := rfl
  map_smul' a x := rfl

include hboundary in
theorem closedToRelation_injective : Function.Injective (closedToRelation M m) := by
  intro x y hxy
  have hc : x.1.2 = y.1.2 := congrArg Subtype.val hxy
  apply Subtype.ext
  apply Prod.ext
  · apply hboundary
    ext b
    have hx := ((mem_closedRelations M m _ _).mp x.2) b
    have hy := ((mem_closedRelations M m _ _).mp y.2) b
    rw [hc] at hx
    linarith
  · exact hc

theorem closedToRelation_surjective : Function.Surjective (closedToRelation M m) := by
  intro c
  obtain ⟨w, hw⟩ := exists_closure_of_relationKernel M m c.2
  exact ⟨⟨(w, c.1), (mem_closedRelations M m _ _).mpr hw⟩, rfl⟩

def closedRelationEquiv : M.closedRelations m ≃ₗ[ℝ] LinearMap.ker (M.relationLinear m) :=
  LinearEquiv.ofBijective (closedToRelation M m)
    ⟨closedToRelation_injective M m hboundary, closedToRelation_surjective M m⟩

/-- The exact linear equivalence asserted by response gluing: every global tight
variation corresponds to exactly one relation among branch response classes. -/
def tightRelationEquiv : Polyhedral.tightKernel M.row (assemble z lam f) ≃ₗ[ℝ]
    LinearMap.ker (M.relationLinear m) :=
  (closedTightEquiv M f m hmin hatt z lam hlam hclose hprivate hfinj).symm.trans
    (closedRelationEquiv M m hboundary)

include hmin hatt hlam hclose hprivate hfinj hboundary in
/-- The dimension assertion holds for the complete tight kernel, including all
rows, with the boundary quotient and branch scales explicitly constructed. -/
theorem tightKernel_finrank_eq_relationKernel :
    Module.finrank ℝ (Polyhedral.tightKernel M.row (assemble z lam f)) =
      Module.finrank ℝ (LinearMap.ker (M.relationLinear m)) :=
  (tightRelationEquiv M f m hmin hatt z lam hlam hclose hprivate hfinj hboundary).finrank_eq


include hlam hfinj in
theorem assemble_ne_zero [Nonempty J] : assemble z lam f ≠ 0 := by
  intro he
  obtain ⟨j⟩ := ‹Nonempty J›
  have h := congrArg (fun g : Global J K D => g.2 j) he
  change lam j • f j = 0 at h
  exact hfinj j ((smul_eq_zero.mp h).resolve_left (ne_of_gt (hlam j)))

include hmin hatt hinternal hlam hclose hprivate hfinj hboundary in
/-- The extremality equivalence in the positive response gluing theorem. The
finite inequality cone is required to be pointed, as the normalized graphical
cone is by its proved zero-elemental-difference criterion. -/
theorem extreme_iff_relation_finrank_one
    (hpointed : Polyhedral.Pointed M.row) :
    Polyhedral.ExtremeRay M.row (assemble z lam f) ↔
      Module.finrank ℝ (LinearMap.ker (M.relationLinear m)) = 1 := by
  classical
  by_cases hJ : Nonempty J
  · letI := hJ
    have hn := assemble_ne_zero f z lam hlam hfinj
    have hdim := tightKernel_finrank_eq_relationKernel M f m hmin hatt z lam hlam hclose
      hprivate hfinj hboundary
    constructor
    · intro he
      rw [← hdim, he.tightKernel_eq_span]
      exact finrank_span_singleton hn
    · intro hd
      apply Polyhedral.extremeRay_of_tightKernel hpointed
        (assembled_nonnegative M f m hmin hinternal z lam hlam hclose) hn
      exact eq_span_singleton_of_mem_of_finrank_eq_one (hdim.trans hd)
        (Polyhedral.self_mem_tightKernel M.row (assemble z lam f)) hn
  · haveI : IsEmpty J := not_nonempty_iff.mp hJ
    have hz0 : z = 0 := by
      apply hboundary
      ext b
      have h := hclose b
      simpa using h
    have hp0 : assemble z lam f = 0 := by
      apply Prod.ext
      · exact hz0
      · funext j
        exact isEmptyElim j
    have hk := Submodule.finrank_le (LinearMap.ker (M.relationLinear m))
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_of_isEmpty] at hk
    constructor
    · intro he
      exact False.elim (he.2.1 hp0)
    · intro hd
      omega

include hlam hclose in
/-- In the extreme case the relation line is exactly the line through the
strictly positive vector of the construction. -/
theorem relationKernel_eq_span_scales
    (hd : Module.finrank ℝ (LinearMap.ker (M.relationLinear m)) = 1) :
    LinearMap.ker (M.relationLinear m) = Submodule.span ℝ {lam} := by
  have hmem := closure_mem_relationKernel M m hclose
  have hk := Submodule.finrank_le (LinearMap.ker (M.relationLinear m))
  rw [hd, Module.finrank_fintype_fun_eq_card] at hk
  haveI : Nonempty J := Fintype.card_pos_iff.mp (by omega)
  have hne : lam ≠ 0 := by
    intro h
    obtain ⟨j⟩ := ‹Nonempty J›
    have hp := hlam j
    rw [h] at hp
    simp at hp
  exact eq_span_singleton_of_mem_of_finrank_eq_one hd hmem hne

include hboundary in
/-- The sharp universal branch-count bound follows from the dimension of the
boundary response quotient, with its boundary-coordinate subtraction justified
by injectivity of the boundary slack map. -/
theorem branch_count_le_capacity
    (hd : Module.finrank ℝ (LinearMap.ker (M.relationLinear m)) = 1) :
    Fintype.card J ≤ Fintype.card B - Fintype.card D + 1 := by
  have hrn := (LinearMap.ker (M.relationLinear m)).finrank_quotient_add_finrank
  rw [(M.relationLinear m).quotKerEquivRange.finrank_eq, hd,
    Module.finrank_fintype_fun_eq_card] at hrn
  have hrle := Submodule.finrank_le (LinearMap.range (M.relationLinear m))
  have hquot := (LinearMap.range M.boundary).finrank_quotient_add_finrank
  rw [LinearMap.finrank_range_of_inj hboundary, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card] at hquot
  omega

end Gluing
end GraphicalZonotopes

end
end
end BundlePart90

section BundlePart91
/- Source: Papers/GraphicalZonotopes/SeparatorCoordinates.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Separator
open Finset
open scoped BigOperators
variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

/-- A partition of the private vertices across an induced boundary. These
conditions are precisely disjoint coverage and absence of edges between
private parts; no clique or rigidity assumption is made on the boundary. -/
structure Partition (G : SimpleGraph V) (B : Finset V) (A : J → Finset V) : Prop where
  boundary_disjoint : ∀ j,Disjoint B (A j)
  private_disjoint : Pairwise (fun j k => Disjoint (A j) (A k))
  cover : ∀ v : V,v∈B ∨ ∃ j,v∈A j
  no_cross_edge : ∀ j k u v,u∈A j → v∈A k → G.Adj u v → j=k

variable {G : SimpleGraph V} {B : Finset V} {A : J → Finset V}

/-- Every clique not contained in the boundary has one and only one private
branch. This exhausts all original Möbius coordinates. -/
theorem Partition.clique_unique_branch (h : Partition G B A)
    (C : CliqueIndex G) (hC : ¬C.1⊆B) : ∃! j : J,C.1⊆B∪A j := by
  obtain ⟨u,huC,huB⟩ := Finset.not_subset.mp hC
  obtain ⟨j,huj⟩ := (h.cover u).resolve_left huB
  have hsub : C.1⊆B∪A j := by
    intro v hvC
    by_cases hvB : v∈B
    · exact mem_union_left _ hvB
    · obtain ⟨k,hvk⟩ := (h.cover v).resolve_left hvB
      by_cases hjk : j=k
      · subst k
        exact mem_union_right _ hvk
      · have huv : u≠ v := by
          intro he
          have hdis := Finset.disjoint_left.mp (h.private_disjoint hjk)
          exact hdis (he ▸ huj) hvk
        have hedge := C.2.2 huC hvC huv
        exact False.elim (hjk (h.no_cross_edge j k u v huj hvk hedge))
  refine ⟨j,hsub,?_⟩
  intro k hk
  have huk : u∈A k := (mem_union.mp (hk huC)).resolve_left huB
  by_contra hkj
  exact Finset.disjoint_left.mp (h.private_disjoint hkj) huk huj

abbrev boundaryIndex (G : SimpleGraph V) (B : Finset V) :=
  {C : CliqueIndex G // C.1⊆B}

abbrev privateIndex (G : SimpleGraph V) (B : Finset V) (A : J → Finset V) (j : J) :=
  {C : CliqueIndex G // ¬C.1⊆B ∧ C.1⊆B∪A j}

noncomputable instance boundaryIndexFintype : Fintype (boundaryIndex G B) := by
  classical
  unfold boundaryIndex
  infer_instance

noncomputable instance privateIndexFintype (j : J) : Fintype (privateIndex G B A j) := by
  classical
  unfold privateIndex
  infer_instance

def branchOf (h : Partition G B A) (C : CliqueIndex G) (hC : ¬C.1⊆B) : J :=
  Classical.choose (h.clique_unique_branch C hC)

theorem branchOf_spec (h : Partition G B A) (C : CliqueIndex G) (hC : ¬C.1⊆B) :
    C.1⊆B∪A (branchOf h C hC) :=
  (Classical.choose_spec (h.clique_unique_branch C hC)).1

theorem branchOf_eq (h : Partition G B A) (C : CliqueIndex G) (hC : ¬C.1⊆B)
    {j : J} (hj : C.1⊆B∪A j) : branchOf h C hC=j := by
  exact ((Classical.choose_spec (h.clique_unique_branch C hC)).2 j hj).symm

def classify (h : Partition G B A) (C : CliqueIndex G) :
    boundaryIndex G B ⊕ (Σ j : J,privateIndex G B A j) := by
  classical
  exact if hC : C.1⊆B then Sum.inl ⟨C,hC⟩ else
    Sum.inr ⟨branchOf h C hC,⟨C,hC,branchOf_spec h C hC⟩⟩

def forget : boundaryIndex G B ⊕ (Σ j : J,privateIndex G B A j) → CliqueIndex G
  | Sum.inl C => C.1
  | Sum.inr ⟨_,C⟩ => C.1

@[simp] theorem forget_classify (h : Partition G B A) (C : CliqueIndex G) :
    forget (classify h C)=C := by
  classical
  unfold classify
  split_ifs <;> rfl

@[simp] theorem classify_boundary (h : Partition G B A) (C : boundaryIndex G B) :
    classify h C.1=Sum.inl C := by
  classical
  simp [classify,C.2]

@[simp] theorem classify_private (h : Partition G B A) (j : J)
    (C : privateIndex G B A j) : classify h C.1=Sum.inr ⟨j,C⟩ := by
  classical
  unfold classify
  rw [dif_neg C.2.1]
  have hj := branchOf_eq h C.1 C.2.1 C.2.2
  congr 1
  apply Sigma.ext hj
  change (⟨C.1, _⟩ : {D : CliqueIndex G // ¬D.1⊆B ∧ D.1⊆B∪A (branchOf h C.1 C.2.1)}) ≍ C
  exact (Subtype.heq_iff_coe_eq (by intro D; rw [hj])).mpr rfl

/-- Exact reindexing of every clique coordinate into one boundary coordinate
or one private coordinate. No zero slots or exceptional cliques are omitted. -/
def indexEquiv (h : Partition G B A) :
    CliqueIndex G ≃ boundaryIndex G B ⊕ (Σ j : J,privateIndex G B A j) where
  toFun := classify h
  invFun := forget
  left_inv := forget_classify h
  right_inv c := by
    cases c with
    | inl C => exact classify_boundary h C
    | inr C => rcases C with ⟨j,C⟩; exact classify_private h j C

def joinCoordinates (h : Partition G B A)
    (x : (boundaryIndex G B → ℝ) × (∀ j : J,privateIndex G B A j → ℝ)) :
    CliqueIndex G → ℝ := fun C =>
  match classify h C with
  | Sum.inl D => x.1 D
  | Sum.inr ⟨j,D⟩ => x.2 j D

@[simp] theorem joinCoordinates_boundary (h : Partition G B A)
    (x : (boundaryIndex G B → ℝ) × (∀ j : J,privateIndex G B A j → ℝ))
    (C : boundaryIndex G B) : joinCoordinates h x C.1=x.1 C := by
  simp only [joinCoordinates,classify_boundary]

@[simp] theorem joinCoordinates_private (h : Partition G B A)
    (x : (boundaryIndex G B → ℝ) × (∀ j : J,privateIndex G B A j → ℝ))
    (j : J) (C : privateIndex G B A j) : joinCoordinates h x C.1=x.2 j C := by
  simp only [joinCoordinates,classify_private]

/-- The complete linear coordinate dictionary, before inequalities are
translated. This is an actual equivalence, rather than a dimension assumption. -/
def coordinateEquiv (h : Partition G B A) :
    ((boundaryIndex G B → ℝ) × (∀ j : J,privateIndex G B A j → ℝ)) ≃ₗ[ℝ]
      (CliqueIndex G → ℝ) where
  toFun := joinCoordinates h
  invFun y := (fun C => y C.1,fun _ C => y C.1)
  left_inv x := by
    apply Prod.ext
    · funext C
      exact joinCoordinates_boundary h x C
    · funext j C
      exact joinCoordinates_private h x j C
  right_inv y := by
    funext C
    have hf := forget_classify h C
    unfold joinCoordinates
    cases hc : classify h C with
    | inl D =>
      have he : D.1=C := by simpa only [hc,forget] using hf
      exact congrArg y he
    | inr D =>
      rcases D with ⟨j,D⟩
      have he : D.1=C := by simpa only [hc,forget] using hf
      exact congrArg y he
  map_add' x y := by
    funext C
    cases hc : classify h C <;> simp [joinCoordinates, hc]
  map_smul' a x := by
    funext C
    cases hc : classify h C <;> simp [joinCoordinates, hc]

/-- Composition with the actual graphical Möbius equivalence gives the
original normalized set functions, not an abstract stand-in cone. -/
def functionEquiv (h : Partition G B A) :
    ((boundaryIndex G B → ℝ) × (∀ j : J,privateIndex G B A j → ℝ)) ≃ₗ[ℝ]
      graphicalFunctionSpace G :=
  (coordinateEquiv h).trans (graphicalCoordinatesEquiv G)

/-- The graph after deleting the boundary, with its usual induced adjacency. -/
def outsideGraph (G : SimpleGraph V) (B : Finset V) : SimpleGraph {v : V // v∉B} :=
  G.induce {v : V | v∉B}

def componentPart (G : SimpleGraph V) (B : Finset V)
    (c : (outsideGraph G B).ConnectedComponent) : Finset V := by
  classical
  exact univ.filter (fun v => ∃ hv : v∉B,
    (outsideGraph G B).connectedComponentMk ⟨v,hv⟩=c)

@[simp] theorem mem_componentPart (G : SimpleGraph V) (B : Finset V)
    (c : (outsideGraph G B).ConnectedComponent) (v : V) :
    v∈componentPart G B c ↔ ∃ hv : v∉B,
      (outsideGraph G B).connectedComponentMk ⟨v,hv⟩=c := by
  classical
  simp [componentPart]

noncomputable instance componentFintype (G : SimpleGraph V) (B : Finset V) :
    Fintype ((outsideGraph G B).ConnectedComponent) := Fintype.ofFinite _

/-- Every actual induced separator supplies the partition used by the
coordinate dictionary, including empty boundaries and no private vertices. -/
theorem componentPartition (G : SimpleGraph V) (B : Finset V) :
    Partition G B (componentPart G B) := by
  classical
  constructor
  · intro c
    apply Finset.disjoint_left.mpr
    intro v hvB hvc
    obtain ⟨hv,_⟩ := (mem_componentPart G B c v).mp hvc
    exact hv hvB
  · intro c d hcd
    apply Finset.disjoint_left.mpr
    intro v hvc hvd
    obtain ⟨hv,hc⟩ := (mem_componentPart G B c v).mp hvc
    obtain ⟨hv',hd⟩ := (mem_componentPart G B d v).mp hvd
    exact hcd (hc.symm.trans hd)
  · intro v
    by_cases hv : v∈B
    · exact Or.inl hv
    · refine Or.inr ⟨(outsideGraph G B).connectedComponentMk ⟨v,hv⟩,?_⟩
      exact (mem_componentPart G B _ v).mpr ⟨hv,rfl⟩
  · intro c d u v hu hv hadj
    obtain ⟨huB,huc⟩ := (mem_componentPart G B c u).mp hu
    obtain ⟨hvB,hvd⟩ := (mem_componentPart G B d v).mp hv
    have he : (outsideGraph G B).connectedComponentMk ⟨u,huB⟩=
        (outsideGraph G B).connectedComponentMk ⟨v,hvB⟩ :=
      SimpleGraph.ConnectedComponent.sound (SimpleGraph.Adj.reachable hadj)
    exact huc.symm.trans (he.trans hvd)

end Separator
end GraphicalZonotopes

end
end
end BundlePart91

section BundlePart92
/- Source: Papers/GraphicalZonotopes/CoefficientSupport.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A set of variables containing the support of every nonzero Möbius slot. -/
def CoefficientSupportedOn (T : Finset V) (y : SetFunction V) : Prop :=
  ∀ C : Finset V,¬C⊆T → y C=0

/-- Conditioning outside a coefficient support has no effect on any genuine
elemental difference. The endpoints need not themselves lie in the support. -/
theorem delta_zeta_inter_support {T : Finset V} {y : SetFunction V}
    (hy : CoefficientSupportedOn T y) {u v : V} (huv : u≠ v)
    {S : Finset V} (hu : u∉S) (hv : v∉S) :
    delta (zeta y) u v S=delta (zeta y) u v (S∩T) := by
  classical
  have hu' : u∉S∩T := fun h => hu (mem_inter.mp h).1
  have hv' : v∉S∩T := fun h => hv (mem_inter.mp h).1
  rw [zeta_eq_sum_monomials,delta_sum,delta_sum]
  apply sum_congr rfl
  intro C hC
  rw [delta_smul,delta_smul,delta_setMonomial huv hu hv,
    delta_setMonomial huv hu' hv']
  by_cases hCT : C⊆T
  · have he : C⊆insert u (insert v S) ↔ C⊆insert u (insert v (S∩T)) := by
      constructor
      · intro h w hwC
        have hw := h hwC
        simp only [mem_insert] at hw ⊢
        rcases hw with hwu | hwv | hwS
        · exact Or.inl hwu
        · exact Or.inr (Or.inl hwv)
        · exact Or.inr (Or.inr (mem_inter.mpr ⟨hwS,hCT hwC⟩))
      · exact fun h => h.trans (insert_subset_insert _ (insert_subset_insert _ inter_subset_left))
    simp only [he]
  · rw [hy C hCT]
    simp

/-- A variable outside the coefficient support cannot occur in a nonzero
edge slack. This uses the full Möbius transform, not a selected row family. -/
theorem delta_zeta_zero_of_outside_support {T : Finset V} {y : SetFunction V}
    (hy : CoefficientSupportedOn T y) {u v : V} (huv : u≠ v)
    (huT : u∉T) {S : Finset V} (hu : u∉S) (hv : v∉S) :
    delta (zeta y) u v S=0 := by
  apply (nonedge_coefficients_zero_iff y huv).mpr ?_ S hu hv
  intro C huC hvC
  exact hy C (fun h => huT (h huC))

theorem delta_inter_mobius_support {T : Finset V} {z : SetFunction V}
    (hz : CoefficientSupportedOn T (mobius z)) {u v : V} (huv : u≠ v)
    {S : Finset V} (hu : u∉S) (hv : v∉S) :
    delta z u v S=delta z u v (S∩T) := by
  simpa only [zeta_mobius] using delta_zeta_inter_support hz huv hu hv

theorem delta_zero_of_outside_mobius_support {T : Finset V} {z : SetFunction V}
    (hz : CoefficientSupportedOn T (mobius z)) {u v : V} (huv : u≠ v)
    (huT : u∉T) {S : Finset V} (hu : u∉S) (hv : v∉S) :
    delta z u v S=0 := by
  simpa only [zeta_mobius] using delta_zeta_zero_of_outside_support hz huv huT hu hv

end GraphicalZonotopes

end
end
end BundlePart92

section BundlePart93
/- Source: Papers/GraphicalZonotopes/SeparatorPieces.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Separator
open Finset
open scoped BigOperators
variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
variable {G : SimpleGraph V} {B : Finset V} {A : J → Finset V}

abbrev Coordinates (G : SimpleGraph V) (B : Finset V) (A : J → Finset V) :=
  (boundaryIndex G B → ℝ) × (∀ j : J,privateIndex G B A j → ℝ)

def boundaryEmbed : (boundaryIndex G B → ℝ) →ₗ[ℝ] Coordinates G B A where
  toFun z := (z,0)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

def privateEmbed (j : J) : (privateIndex G B A j → ℝ) →ₗ[ℝ] Coordinates G B A where
  toFun g := (0,LinearMap.single ℝ (fun k => privateIndex G B A k → ℝ) j g)
  map_add' f g := by
    apply Prod.ext
    · simp
    · exact map_add (LinearMap.single ℝ (fun k => privateIndex G B A k → ℝ) j) f g
  map_smul' a f := by
    apply Prod.ext
    · simp
    · exact map_smul (LinearMap.single ℝ (fun k => privateIndex G B A k → ℝ) j) a f

def globalFunctionMap (h : Partition G B A) : Coordinates G B A →ₗ[ℝ] SetFunction V :=
  (graphicalFunctionSpace G).subtype.comp (functionEquiv h).toLinearMap

def boundaryFunctionMap (h : Partition G B A) :
    (boundaryIndex G B → ℝ) →ₗ[ℝ] SetFunction V :=
  (globalFunctionMap h).comp boundaryEmbed

def privateFunctionMap (h : Partition G B A) (j : J) :
    (privateIndex G B A j → ℝ) →ₗ[ℝ] SetFunction V :=
  (globalFunctionMap h).comp (privateEmbed j)

theorem coordinates_decompose (x : Coordinates G B A) :
    x=boundaryEmbed x.1+∑ j : J,privateEmbed j (x.2 j) := by
  classical
  apply Prod.ext
  · simp [boundaryEmbed,privateEmbed, Prod.fst_sum, Prod.snd_sum]
  · funext j C
    simp [boundaryEmbed,privateEmbed,LinearMap.single_apply,Finset.sum_apply, Prod.fst_sum, Prod.snd_sum]

/-- The full original function is the sum of its boundary function and every
private branch function, with no discarded Möbius coordinates. -/
theorem function_decompose (h : Partition G B A) (x : Coordinates G B A) :
    globalFunctionMap h x=boundaryFunctionMap h x.1+
      ∑ j : J,privateFunctionMap h j (x.2 j) := by
  have he := congrArg (globalFunctionMap h) (coordinates_decompose x)
  simpa only [map_add,map_sum,boundaryFunctionMap,privateFunctionMap,
    LinearMap.comp_apply] using he

@[simp] theorem mobius_globalFunctionMap (h : Partition G B A) (x : Coordinates G B A) :
    mobius (globalFunctionMap h x)=coefficientsFromCoordinates G (joinCoordinates h x) := by
  change mobius (zeta (coefficientsFromCoordinates G (joinCoordinates h x)))=_
  exact mobius_zeta _

theorem boundaryFunction_supported (h : Partition G B A) (z : boundaryIndex G B → ℝ) :
    CoefficientSupportedOn B (mobius (boundaryFunctionMap h z)) := by
  classical
  intro C hCB
  change mobius (globalFunctionMap h (z,0)) C=0
  rw [mobius_globalFunctionMap]
  by_cases hcl : IsCliqueCoordinate G C
  · simp [coefficientsFromCoordinates,hcl,joinCoordinates,classify,hCB]
  · simp [coefficientsFromCoordinates,hcl]

theorem privateFunction_supported (h : Partition G B A) (j : J)
    (g : privateIndex G B A j → ℝ) :
    CoefficientSupportedOn (B∪A j) (mobius (privateFunctionMap h j g)) := by
  classical
  intro C hCA
  change mobius (globalFunctionMap h
    (0,LinearMap.single ℝ (fun k => privateIndex G B A k → ℝ) j g)) C=0
  rw [mobius_globalFunctionMap]
  by_cases hcl : IsCliqueCoordinate G C
  · have hCB : ¬C⊆B := fun hc => hCA (hc.trans subset_union_left)
    have hbranch : branchOf h ⟨C,hcl⟩ hCB≠ j := by
      intro he
      have hc := branchOf_spec h ⟨C,hcl⟩ hCB
      rw [he] at hc
      exact hCA hc
    simp [coefficientsFromCoordinates,hcl,joinCoordinates,classify,hCB,
      LinearMap.single_apply,Pi.single_eq_of_ne hbranch]
  · simp [coefficientsFromCoordinates,hcl]

theorem privateFunction_boundary_coefficients_zero (h : Partition G B A) (j : J)
    (g : privateIndex G B A j → ℝ) {C : Finset V} (hCB : C⊆B) :
    mobius (privateFunctionMap h j g) C=0 := by
  classical
  change mobius (globalFunctionMap h
    (0,LinearMap.single ℝ (fun k => privateIndex G B A k → ℝ) j g)) C=0
  rw [mobius_globalFunctionMap]
  by_cases hcl : IsCliqueCoordinate G C <;>
    simp [coefficientsFromCoordinates,hcl,joinCoordinates,classify,hCB]

/-- On a private edge, the boundary contribution and every other branch
contribution vanish for all conditioning sets. -/
theorem delta_private_edge_decompose (h : Partition G B A) (x : Coordinates G B A)
    (j : J) {u v : V} (huA : u∈A j) (huv : u≠ v)
    {S : Finset V} (hu : u∉S) (hv : v∉S) :
    delta (globalFunctionMap h x) u v S=
      delta (privateFunctionMap h j (x.2 j)) u v S := by
  classical
  have huB : u∉B := fun hB => Finset.disjoint_left.mp (h.boundary_disjoint j) hB huA
  rw [function_decompose,delta_add,delta_sum]
  rw [delta_zero_of_outside_mobius_support (boundaryFunction_supported h x.1) huv huB hu hv,
    zero_add]
  apply sum_eq_single j
  · intro k hk hkj
    have huBA : u∉B∪A k := by
      intro hm
      rcases mem_union.mp hm with hB | hkA
      · exact huB hB
      · exact Finset.disjoint_left.mp (h.private_disjoint hkj) hkA huA
    exact delta_zero_of_outside_mobius_support (privateFunction_supported h k (x.2 k))
      huv huBA hu hv
  · simp

/-- Every private response depends only on its actual branch conditioning
bits, as required by the separator row model. -/
theorem delta_private_inter (h : Partition G B A) (j : J)
    (g : privateIndex G B A j → ℝ) {u v : V} (huv : u≠ v)
    {S : Finset V} (hu : u∉S) (hv : v∉S) :
    delta (privateFunctionMap h j g) u v S=
      delta (privateFunctionMap h j g) u v (S∩(B∪A j)) :=
  delta_inter_mobius_support (privateFunction_supported h j g) huv hu hv

end Separator
end GraphicalZonotopes

end
end
end BundlePart93

section BundlePart94
/- Source: Papers/GraphicalZonotopes/SeparatorRows.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Separator
open Finset
open scoped BigOperators
variable {V J : Type*} [Fintype V] [LinearOrder V]
local instance : DecidableEq V := LinearOrder.toDecidableEq
variable [Fintype J] [DecidableEq J]
variable {G : SimpleGraph V} {B : Finset V} {A : J → Finset V}

/-- Boundary types are exactly the original edge/common-neighbor contexts
whose endpoints and conditioning variables lie in the induced boundary. -/
abbrev BoundaryRow (G : SimpleGraph V) (B : Finset V) :=
  {r : BoundaryContext G // r.1.1.1∈B ∧ r.1.1.2∈B ∧ r.2.1⊆B}

abbrev InternalRow (G : SimpleGraph V) (B : Finset V) (A : J → Finset V) (j : J) :=
  {r : BoundaryContext G //
    (r.1.1.1∈A j ∨ r.1.1.2∈A j) ∧ r.2.1⊆B∪A j}

abbrev BranchChoice (A : J → Finset V) (j : J) :=
  {S : Finset V // S⊆A j}

noncomputable instance boundaryRowFintype : Fintype (BoundaryRow G B) := by
  classical
  infer_instance
noncomputable instance internalRowFintype (j : J) : Fintype (InternalRow G B A j) := by
  classical
  infer_instance
noncomputable instance branchChoiceFintype (j : J) : Fintype (BranchChoice A j) := by
  classical
  infer_instance

/-- The actual separator row model obtained from the original set functions. -/
def rowData (h : Partition G B A) :
    Gluing.Data (BoundaryRow G B) J (privateIndex G B A) (boundaryIndex G B)
      (InternalRow G B A) (BranchChoice A) where
  boundary := LinearMap.pi (fun b =>
    (deltaLinear b.1.1.1.1 b.1.1.1.2 b.1.2.1).comp (boundaryFunctionMap h))
  internal j r :=
    (deltaLinear r.1.1.1.1 r.1.1.1.2 r.1.2.1).comp (privateFunctionMap h j)
  response j b X :=
    (deltaLinear b.1.1.1.1 b.1.1.1.2 (b.1.2.1∪X.1)).comp (privateFunctionMap h j)

theorem context_left_not_mem (r : BoundaryContext G) : r.1.1.1∉r.2.1 := by
  intro hm
  exact not_mem_commonNeighbors_left G _ _ ((mem_powerset.mp r.2.2) hm)
theorem context_right_not_mem (r : BoundaryContext G) : r.1.1.2∉r.2.1 := by
  intro hm
  exact not_mem_commonNeighbors_right G _ _ ((mem_powerset.mp r.2.2) hm)

/-- An actual private-edge row of the original cone is exactly its private
model row. No boundary or other-branch coefficient is present in that row. -/
theorem internal_row_eq (h : Partition G B A) (x : Coordinates G B A)
    (j : J) (r : InternalRow G B A j) :
    (rowData h).row (Sum.inl ⟨j,r⟩) x=
      delta (globalFunctionMap h x) r.1.1.1.1 r.1.1.1.2 r.1.2.1 := by
  change delta (privateFunctionMap h j (x.2 j)) _ _ _=_
  rcases r.2.1 with hu | hv
  · exact (delta_private_edge_decompose h x j hu (ne_of_lt r.1.1.2.1)
      (context_left_not_mem r.1) (context_right_not_mem r.1)).symm
  · rw [delta_comm r.1.1.1.1,delta_comm r.1.1.1.1]
    exact (delta_private_edge_decompose h x j hv (ne_of_gt r.1.1.2.1)
      (context_right_not_mem r.1) (context_left_not_mem r.1)).symm

/-- The original slack splits across the exact boundary and private contexts. -/
theorem boundary_formula (h : Partition G B A) (x : Coordinates G B A)
    {u v : V} (huv : u≠ v) {S : Finset V} (hu : u∉S) (hv : v∉S) :
    delta (globalFunctionMap h x) u v S=
      delta (boundaryFunctionMap h x.1) u v (S∩B)+
      ∑ j : J,delta (privateFunctionMap h j (x.2 j)) u v ((S∩B)∪(S∩A j)) := by
  rw [function_decompose,delta_add,delta_sum]
  rw [delta_inter_mobius_support (boundaryFunction_supported h x.1) huv hu hv]
  congr 1
  apply sum_congr rfl
  intro j hj
  rw [delta_private_inter h j (x.2 j) huv hu hv,Finset.inter_union_distrib_left]

def combinedContext (S : Finset V) (X : ∀ j,BranchChoice A j) : Finset V :=
  S∪univ.biUnion (fun j => (X j).1)

theorem combinedContext_inter_boundary (h : Partition G B A)
    {S : Finset V} (hSB : S⊆B) (X : ∀ j,BranchChoice A j) :
    combinedContext S X∩B=S := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨hvU,hvB⟩ := mem_inter.mp hv
    rcases mem_union.mp hvU with hvS | hvX
    · exact hvS
    · obtain ⟨j,_,hvj⟩ := mem_biUnion.mp hvX
      exact False.elim (Finset.disjoint_left.mp (h.boundary_disjoint j) hvB ((X j).2 hvj))
  · intro hv
    exact mem_inter.mpr ⟨mem_union_left _ hv,hSB hv⟩

theorem combinedContext_inter_private (h : Partition G B A)
    {S : Finset V} (hSB : S⊆B) (X : ∀ j,BranchChoice A j) (j : J) :
    combinedContext S X∩A j=(X j).1 := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨hvU,hvA⟩ := mem_inter.mp hv
    rcases mem_union.mp hvU with hvS | hvX
    · exact False.elim (Finset.disjoint_left.mp (h.boundary_disjoint j) (hSB hvS) hvA)
    · obtain ⟨k,_,hvk⟩ := mem_biUnion.mp hvX
      by_cases hkj : k=j
      · subst k
        exact hvk
      · exact False.elim (Finset.disjoint_left.mp (h.private_disjoint hkj) ((X k).2 hvk) hvA)
  · intro hv
    exact mem_inter.mpr ⟨mem_union_right _ (mem_biUnion.mpr ⟨j,mem_univ _,hv⟩),(X j).2 hv⟩

theorem boundary_not_mem_combinedContext (h : Partition G B A)
    (S : Finset V) (X : ∀ j,BranchChoice A j) {u : V} (huB : u∈B) (huS : u∉S) :
    u∉combinedContext S X := by
  intro hu
  rcases mem_union.mp hu with hu | hu
  · exact huS hu
  · obtain ⟨j,_,huj⟩ := mem_biUnion.mp hu
    exact Finset.disjoint_left.mp (h.boundary_disjoint j) huB ((X j).2 huj)

/-- Every model boundary row is a genuine original elemental inequality,
with independently chosen private conditioning subsets. -/
theorem boundary_row_eq (h : Partition G B A) (x : Coordinates G B A)
    (b : BoundaryRow G B) (X : ∀ j,BranchChoice A j) :
    (rowData h).row (Sum.inr (b,X)) x=
      delta (globalFunctionMap h x) b.1.1.1.1 b.1.1.1.2 (combinedContext b.1.2.1 X) := by
  have hu := boundary_not_mem_combinedContext h b.1.2.1 X b.2.1 (context_left_not_mem b.1)
  have hv := boundary_not_mem_combinedContext h b.1.2.1 X b.2.2.1 (context_right_not_mem b.1)
  rw [boundary_formula h x (ne_of_lt b.1.1.2.1) hu hv,
    combinedContext_inter_boundary h b.2.2.2 X]
  simp_rw [combinedContext_inter_private h b.2.2.2 X]
  rfl

/-- Nonnegativity of all model rows follows from the genuine supermodular
inequalities on the original graphical function. -/
theorem rowData_nonnegative_of_supermodular (h : Partition G B A) (x : Coordinates G B A)
    (hs : Supermodular (globalFunctionMap h x)) :
    Polyhedral.Nonnegative (rowData h).row x := by
  intro r
  rcases r with ⟨j,r⟩ | ⟨b,X⟩
  · rw [internal_row_eq]
    exact hs.elemental _ _ (ne_of_lt r.1.1.2.1) _
      (context_left_not_mem r.1) (context_right_not_mem r.1)
  · rw [boundary_row_eq]
    exact hs.elemental _ _ (ne_of_lt b.1.1.2.1) _
      (boundary_not_mem_combinedContext h _ X b.2.1 (context_left_not_mem b.1))
      (boundary_not_mem_combinedContext h _ X b.2.2.1 (context_right_not_mem b.1))

/-- Restricting an original common-neighbor context preserves its validity. -/
def restrictContext (r : BoundaryContext G) (T : Finset V) : BoundaryContext G :=
  ⟨r.1,⟨r.2.1∩T,mem_powerset.mpr (inter_subset_left.trans (mem_powerset.mp r.2.2))⟩⟩

/-- Every original row is recovered from the model, so feasibility is an
actual equivalence rather than an implication in a convenient subsystem. -/
theorem supermodular_of_rowData_nonnegative (h : Partition G B A) (x : Coordinates G B A)
    (hn : Polyhedral.Nonnegative (rowData h).row x) :
    Supermodular (globalFunctionMap h x) := by
  apply (supermodular_iff_boundarySlacks_nonnegative G (functionEquiv h x)).mpr
  intro r
  by_cases hb : r.1.1.1∈B ∧ r.1.1.2∈B
  · let b : BoundaryRow G B := ⟨restrictContext r B,hb.1,hb.2,inter_subset_right⟩
    let X : ∀ j,BranchChoice A j := fun j => ⟨r.2.1∩A j,inter_subset_right⟩
    have hm := hn (Sum.inr (b,X))
    change 0≤ delta (globalFunctionMap h x) r.1.1.1 r.1.1.2 r.2.1
    rw [boundary_formula h x (ne_of_lt r.1.2.1)
      (context_left_not_mem r) (context_right_not_mem r)]
    exact hm
  · have hu_or_hv : (∃ j,r.1.1.1∈A j) ∨ (∃ j,r.1.1.2∈A j) := by
      by_cases huB : r.1.1.1∈B
      · exact Or.inr ((h.cover _).resolve_left (fun hvB => hb ⟨huB,hvB⟩))
      · exact Or.inl ((h.cover _).resolve_left huB)
    rcases hu_or_hv with ⟨j,huj⟩ | ⟨j,hvj⟩
    · let r' : InternalRow G B A j :=
        ⟨restrictContext r (B∪A j),Or.inl huj,inter_subset_right⟩
      have hm := hn (Sum.inl ⟨j,r'⟩)
      change 0≤ delta (globalFunctionMap h x) r.1.1.1 r.1.1.2 r.2.1
      rw [delta_private_edge_decompose h x j huj (ne_of_lt r.1.2.1)
        (context_left_not_mem r) (context_right_not_mem r),
        delta_private_inter h j (x.2 j) (ne_of_lt r.1.2.1)
        (context_left_not_mem r) (context_right_not_mem r)]
      exact hm
    · let r' : InternalRow G B A j :=
        ⟨restrictContext r (B∪A j),Or.inr hvj,inter_subset_right⟩
      have hm := hn (Sum.inl ⟨j,r'⟩)
      change 0≤ delta (globalFunctionMap h x) r.1.1.1 r.1.1.2 r.2.1
      rw [delta_comm r.1.1.1,delta_private_edge_decompose h x j hvj (ne_of_gt r.1.2.1)
        (context_right_not_mem r) (context_left_not_mem r),
        delta_private_inter h j (x.2 j) (ne_of_gt r.1.2.1)
        (context_right_not_mem r) (context_left_not_mem r),delta_comm r.1.1.2]
      exact hm

theorem rowData_nonnegative_iff (h : Partition G B A) (x : Coordinates G B A) :
    Polyhedral.Nonnegative (rowData h).row x ↔ Supermodular (globalFunctionMap h x) :=
  ⟨supermodular_of_rowData_nonnegative h x,rowData_nonnegative_of_supermodular h x⟩

end Separator
end GraphicalZonotopes

end
end
end BundlePart94

section BundlePart95
/- Source: Papers/GraphicalZonotopes/PolyhedralConeEquiv.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Polyhedral
variable {E F I J : Type*} [AddCommGroup E] [Module ℝ E]
variable [AddCommGroup F] [Module ℝ F] [Fintype I] [Fintype J]
variable (A : I → E →ₗ[ℝ] ℝ) (B : J → F →ₗ[ℝ] ℝ) (e : E ≃ₗ[ℝ] F)
variable (hcone : ∀ x,Nonnegative A x ↔ Nonnegative B (e x))
include hcone

/-- A genuine linear equivalence of inequality cones preserves extreme rays,
independently of the chosen or repeated inequality presentations. -/
theorem extremeRay_equiv (x : E) : ExtremeRay A x ↔ ExtremeRay B (e x) := by
  constructor
  · intro hx
    refine ⟨(hcone x).mp hx.1,?_,?_⟩
    · intro he
      exact hx.2.1 (e.injective (he.trans (e.map_zero).symm))
    · intro u v hu hv he
      have hu' : Nonnegative A (e.symm u) := (hcone _).mpr (by simpa using hu)
      have hv' : Nonnegative A (e.symm v) := (hcone _).mpr (by simpa using hv)
      have he' : e.symm u+e.symm v=x := by
        apply e.injective
        simpa only [map_add,LinearEquiv.apply_symm_apply] using he
      obtain ⟨a,ha,heu⟩ := hx.2.2 _ _ hu' hv' he'
      refine ⟨a,ha,?_⟩
      simpa only [LinearEquiv.apply_symm_apply,map_smul] using congrArg e heu
  · intro hx
    refine ⟨(hcone x).mpr hx.1,?_,?_⟩
    · intro he
      exact hx.2.1 (by simp [he])
    · intro u v hu hv he
      obtain ⟨a,ha,heu⟩ := hx.2.2 (e u) (e v) ((hcone u).mp hu)
        ((hcone v).mp hv) (by rw [←map_add,he])
      exact ⟨a,ha,e.injective (by simpa only [map_smul] using heu)⟩

/-- Complete tight kernels are preserved by a cone equivalence. The proof
uses actual small two-sided perturbations, so no row-spanning assumption is
hidden in the equivalence of the inequality descriptions. -/
theorem tightKernel_equiv_mem {x v : E} (hx : Nonnegative A x) :
    v∈tightKernel A x ↔ e v∈tightKernel B (e x) := by
  have forward : ∀ {x v : E},Nonnegative A x → v∈tightKernel A x →
      e v∈tightKernel B (e x) := by
    intro x v hx hv
    obtain ⟨ε,hε,hp,hm⟩ := exists_two_sided_perturbation hx hv
    have hp' := (hcone _).mp hp
    have hm' := (hcone _).mp hm
    intro j hj
    have h1 := hp' j
    have h2 := hm' j
    simp only [map_add,map_sub,map_smul,smul_eq_mul,hj,mul_zero,zero_add,zero_sub] at h1 h2
    have he : ε * B j (e v)=0 := le_antisymm (by linarith) h1
    exact (mul_eq_zero.mp he).resolve_left (ne_of_gt hε)
  constructor
  · exact forward hx
  · intro hv
    obtain ⟨ε,hε,hp,hm⟩ := exists_two_sided_perturbation ((hcone x).mp hx) hv
    have hp' : Nonnegative A ((1/2 : ℝ) • x+ε • v) :=
      (hcone _).mpr (by simpa only [map_add,map_smul] using hp)
    have hm' : Nonnegative A ((1/2 : ℝ) • x-ε • v) :=
      (hcone _).mpr (by simpa only [map_sub,map_smul] using hm)
    intro i hi
    have h1 := hp' i
    have h2 := hm' i
    simp only [map_add,map_sub,map_smul,smul_eq_mul,hi,mul_zero,zero_add,zero_sub] at h1 h2
    have he : ε * A i v=0 := le_antisymm (by linarith) h1
    exact (mul_eq_zero.mp he).resolve_left (ne_of_gt hε)

/-- The exact linear isomorphism between complete tight spaces. -/
def tightKernelEquiv (x : E) (hx : Nonnegative A x) :
    tightKernel A x ≃ₗ[ℝ] tightKernel B (e x) where
  toFun v := ⟨e v,(tightKernel_equiv_mem A B e hcone hx).mp v.2⟩
  invFun w := ⟨e.symm w,(tightKernel_equiv_mem A B e hcone hx).mpr (by simpa using w.2)⟩
  left_inv v := Subtype.ext (e.symm_apply_apply v)
  right_inv w := Subtype.ext (e.apply_symm_apply w)
  map_add' v w := Subtype.ext (e.map_add v w)
  map_smul' a v := Subtype.ext (e.map_smul a v)

end Polyhedral
end GraphicalZonotopes

end
end
end BundlePart95

section BundlePart96
/- Source: Papers/GraphicalZonotopes/SeparatorCapacity.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Gluing
open Finset
open scoped BigOperators
variable {B J D : Type*} {K I X : J → Type*}
variable [Fintype B] [Fintype J] [Fintype D]
variable [∀ j, Fintype (K j)] [∀ j, Fintype (I j)] [∀ j, Fintype (X j)]
variable [DecidableEq J]
variable (M : Data B J K D I X) (f : ∀ j, K j → ℝ) (m : J → B → ℝ)
variable (hmin : ∀ j b x, m j b ≤ M.response j b x (f j))
variable (hatt : ∀ j b, ∃ x, M.response j b x (f j) = m j b)
variable (z : D → ℝ) (lam : J → ℝ) (hlam : ∀ j, 0 < lam j)
variable (hcone : Polyhedral.Nonnegative M.row (assemble z lam f))

include hmin hatt hlam hcone in
/-- At an arbitrary feasible glued point, every tight boundary row uses a
minimizer in every branch. It is not assumed that all boundary types are tight. -/
theorem tight_boundary_uses_minima (b : B) (x : ∀ j, X j)
    (ht : M.row (Sum.inr (b,x)) (assemble z lam f) = 0) :
    ∀ j, M.response j b (x j) (f j) = m j b := by
  classical
  choose xmin hxmin using fun j : J => hatt j b
  have hbase := hcone (Sum.inr (b,xmin))
  change 0 ≤ M.boundary z b + ∑ j, M.response j b (xmin j) (lam j • f j) at hbase
  simp only [map_smul, smul_eq_mul, hxmin] at hbase
  change M.boundary z b + ∑ j, M.response j b (x j) (lam j • f j) = 0 at ht
  simp only [map_smul, smul_eq_mul] at ht
  have hnn : ∀ j ∈ (univ : Finset J),
      0 ≤ lam j * (M.response j b (x j) (f j) - m j b) :=
    fun j _ => mul_nonneg (hlam j).le (sub_nonneg.mpr (hmin j b (x j)))
  have hsum : ∑ j, lam j * (M.response j b (x j) (f j) - m j b) = 0 := by
    have hsum0 := sum_nonneg hnn
    rw [show (∑ j, lam j * (M.response j b (x j) (f j) - m j b)) =
      (∑ j, lam j * M.response j b (x j) (f j)) - ∑ j, lam j * m j b by
        simp [mul_sub, sum_sub_distrib]] at hsum0 ⊢
    linarith
  have hterm := (sum_eq_zero_iff_of_nonneg hnn).mp hsum
  intro j
  exact sub_eq_zero.mp ((mul_eq_zero.mp (hterm j (mem_univ j))).resolve_left (ne_of_gt (hlam j)))

/-- Every solution of all aggregated boundary equations gives a true global
tight variation. Additional aggregated equations on nontight types are harmless;
they are counted in the upper bound exactly once each. -/
def capacityEmbedding : M.closedRelations m →ₗ[ℝ]
    Polyhedral.tightKernel M.row (assemble z lam f) where
  toFun y := ⟨assemble y.1.1 y.1.2 f, by
    intro r hr
    rcases r with ⟨j,i⟩ | ⟨b,x⟩
    · change M.internal j i (lam j • f j) = 0 at hr
      rw [map_smul, smul_eq_mul] at hr
      have hi := (mul_eq_zero.mp hr).resolve_left (ne_of_gt (hlam j))
      change M.internal j i (y.1.2 j • f j) = 0
      rw [map_smul, hi, smul_zero]
    · have hx := tight_boundary_uses_minima M f m hmin hatt z lam hlam hcone b x hr
      have hcl := (mem_closedRelations M m y.1.1 y.1.2).mp y.2 b
      change M.boundary y.1.1 b + ∑ j, M.response j b (x j) (y.1.2 j • f j) = 0
      simpa only [map_smul, smul_eq_mul, hx] using hcl⟩
  map_add' x y := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · ext j k
      simp [assemble, add_smul]
  map_smul' a x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · ext j k
      simp [assemble, smul_smul,mul_assoc]

theorem capacityEmbedding_injective (hfinj : ∀ j, f j ≠ 0) :
    Function.Injective (capacityEmbedding M f m hmin hatt z lam hlam hcone) := by
  intro x y hxy
  have he := congrArg Subtype.val hxy
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun w : Global J K D => w.1) he
  · funext j
    have h := congrArg (fun w : Global J K D => w.2 j) he
    change x.1.2 j • f j = y.1.2 j • f j at h
    have hnonzero : ∃ k, f j k ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact hfinj j (funext hn)
    obtain ⟨k,hk⟩ := hnonzero
    have hh := congrFun h k
    simp only [Pi.smul_apply, smul_eq_mul] at hh
    exact mul_right_cancel₀ hk hh

include hmin hatt hlam in
/-- The general separator-capacity inequality. Unlike positive-response gluing,
no private-kernel rigidity and no simultaneous boundary-closing condition are
assumed. Every nonzero private block is permitted to vary by its own scalar. -/
theorem separator_capacity (hfinj : ∀ j, f j ≠ 0)
    (hext : Polyhedral.ExtremeRay M.row (assemble z lam f)) :
    Fintype.card J ≤ Fintype.card B - Fintype.card D + 1 := by
  have hle := LinearMap.finrank_le_finrank_of_injective
    (capacityEmbedding_injective M f m hmin hatt z lam hlam hext.1 hfinj)
  rw [hext.tightKernel_eq_span, finrank_span_singleton hext.2.1] at hle
  have hnull := (M.closureLinear m).ker.finrank_quotient_add_finrank
  rw [(M.closureLinear m).quotKerEquivRange.finrank_eq,
    Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card] at hnull
  have hrange := Submodule.finrank_le (M.closureLinear m).range
  rw [Module.finrank_fintype_fun_eq_card] at hrange
  change Module.finrank ℝ (M.closureLinear m).ker ≤ 1 at hle
  omega

/-- Adding a boundary lift to each branch changes responses by the boundary
slack image. The quotient response map is literally unchanged. -/
theorem relationLinear_boundary_lift (h : J → D → ℝ) :
    M.relationLinear (fun j b => m j b + M.boundary (h j) b) = M.relationLinear m := by
  apply LinearMap.ext
  intro c
  change (LinearMap.range M.boundary).mkQ
      (responseLinear (fun j b => m j b + M.boundary (h j) b) c) =
    (LinearMap.range M.boundary).mkQ (responseLinear m c)
  have he : responseLinear (fun j b => m j b + M.boundary (h j) b) c =
      responseLinear m c + M.boundary (∑ j, c j • h j) := by
    ext b
    simp [responseLinear, mul_add, sum_add_distrib, map_sum]
  rw [he, map_add]
  have hz : (LinearMap.range M.boundary).mkQ (M.boundary (∑ j, c j • h j)) = 0 := by
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
    exact ⟨_,rfl⟩
  rw [hz, add_zero]

end Gluing
end GraphicalZonotopes

end
end
end BundlePart96

section BundlePart97
/- Source: Papers/GraphicalZonotopes/SeparatorCone.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Separator
open Finset
open scoped BigOperators
variable {V J : Type*} [Fintype V] [LinearOrder V]
local instance : DecidableEq V := LinearOrder.toDecidableEq
variable [Fintype J] [DecidableEq J]
variable {G : SimpleGraph V} {B : Finset V} {A : J → Finset V}

/-- The exact normalized graphical cone and the separated row model agree. -/
theorem rowData_nonnegative_iff_contextRows (h : Partition G B A) (x : Coordinates G B A) :
    Polyhedral.Nonnegative (rowData h).row x ↔
      Polyhedral.Nonnegative (contextRow G) (functionEquiv h x) :=
  (rowData_nonnegative_iff h x).trans
    (supermodular_iff_boundarySlacks_nonnegative G (functionEquiv h x))

theorem rowData_extreme_iff (h : Partition G B A) (x : Coordinates G B A) :
    Polyhedral.ExtremeRay (rowData h).row x ↔
      ExtremeSupermodular (globalFunctionMap h x) := by
  rw [Polyhedral.extremeRay_equiv (rowData h).row (contextRow G) (functionEquiv h)
    (rowData_nonnegative_iff_contextRows h)]
  exact (extremeSupermodular_iff_contextRows G (functionEquiv h x)).symm

theorem rowData_pointed (h : Partition G B A) : Polyhedral.Pointed (rowData h).row := by
  intro x hx
  have hp : Polyhedral.Nonnegative (rowData h).row x := fun r => (hx r).ge
  have hm : Polyhedral.Nonnegative (rowData h).row (-x) := by
    intro r
    rw [map_neg,hx r]
    simp
  have hp' := (rowData_nonnegative_iff_contextRows h x).mp hp
  have hm' := (rowData_nonnegative_iff_contextRows h (-x)).mp hm
  have hz : functionEquiv h x=0 := by
    apply contextRows_pointed G
    intro r
    have hneg := hm' r
    rw [map_neg,map_neg] at hneg
    exact le_antisymm (by linarith) (hp' r)
  exact (functionEquiv h).injective (hz.trans (map_zero _).symm)

/-- The boundary slack map used by the separator model is injective because
its rows determine every boundary coefficient through the original graphical
Möbius isomorphism. -/
theorem rowData_boundary_injective (h : Partition G B A) :
    Function.Injective (rowData h).boundary := by
  suffices hz : ∀ z,(rowData h).boundary z=0 → z=0 by
    intro z w he
    exact sub_eq_zero.mp (hz (z-w) (by rw [map_sub,he,sub_self]))
  intro z hz
  let f : graphicalFunctionSpace G := functionEquiv h (z,0)
  have hf : f=0 := by
    apply boundarySlackMap_eq_zero G
    funext r
    change delta (boundaryFunctionMap h z) r.1.1.1 r.1.1.2 r.2.1=0
    by_cases huB : r.1.1.1∈B
    · by_cases hvB : r.1.1.2∈B
      · let b : BoundaryRow G B := ⟨restrictContext r B,huB,hvB,inter_subset_right⟩
        have hb := congrFun hz b
        rw [delta_inter_mobius_support (boundaryFunction_supported h z)
          (ne_of_lt r.1.2.1) (context_left_not_mem r) (context_right_not_mem r)]
        exact hb
      · rw [delta_comm r.1.1.1]
        exact delta_zero_of_outside_mobius_support (boundaryFunction_supported h z)
          (ne_of_gt r.1.2.1) hvB (context_right_not_mem r) (context_left_not_mem r)
    · exact delta_zero_of_outside_mobius_support (boundaryFunction_supported h z)
        (ne_of_lt r.1.2.1) huB (context_left_not_mem r) (context_right_not_mem r)
  have he : ((z,0) : Coordinates G B A)=0 :=
    (functionEquiv h).injective (hf.trans (map_zero _).symm)
  exact congrArg Prod.fst he

/-- The complete original graphical tight space is isomorphic to the
separated model's full tight space; no row has been removed from either cone. -/
def graphicalTightEquiv (h : Partition G B A) (x : Coordinates G B A)
    (hx : Polyhedral.Nonnegative (rowData h).row x) :
    Polyhedral.tightKernel (rowData h).row x ≃ₗ[ℝ]
      Polyhedral.tightKernel (contextRow G) (functionEquiv h x) :=
  Polyhedral.tightKernelEquiv (rowData h).row (contextRow G) (functionEquiv h)
    (rowData_nonnegative_iff_contextRows h) x hx

end Separator
end GraphicalZonotopes

end
end
end BundlePart97

section BundlePart98
/- Source: Papers/GraphicalZonotopes/SeparatorActiveCapacity.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Gluing
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {B J D : Type*} {K I X : J → Type*}
variable [Fintype B] [Fintype J] [Fintype D]
variable [∀ j,Fintype (K j)] [∀ j,Fintype (I j)] [∀ j,Fintype (X j)]
variable [DecidableEq J]

abbrev ActiveBranch (f : ∀ j,K j → ℝ) := {j : J // f j≠0}
noncomputable instance activeBranchFintype (f : ∀ j,K j → ℝ) : Fintype (ActiveBranch f) := by
  classical
  infer_instance

def extendActiveScales (f : ∀ j,K j → ℝ) : (ActiveBranch f → ℝ) →ₗ[ℝ] (J → ℝ) where
  toFun c j := if hj : f j≠0 then c ⟨j,hj⟩ else 0
  map_add' c d := by
    funext j
    by_cases hj : f j=0 <;> simp [hj]
  map_smul' a c := by
    funext j
    by_cases hj : f j=0 <;> simp [hj]

@[simp] theorem extendActiveScales_active (f : ∀ j,K j → ℝ)
    (c : ActiveBranch f → ℝ) (j : ActiveBranch f) : extendActiveScales f c j=c j := by
  classical
  simp [extendActiveScales,j.2]

theorem sum_extendActiveScales (f : ∀ j,K j → ℝ) (c : ActiveBranch f → ℝ) (m : J → ℝ) :
    (∑ j : J,extendActiveScales f c j*m j)=∑ j : ActiveBranch f,c j*m j := by
  classical
  apply Finset.sum_congr_set {j : J | f j≠0}
  · intro j hj
    change f j ≠ 0 at hj
    simp [extendActiveScales,hj]
  · intro j hj
    change ¬f j ≠ 0 at hj
    simp [extendActiveScales,hj]

variable (M : Data B J K D I X) (f : ∀ j,K j → ℝ) (m : J → B → ℝ)

def activeClosureLinear : ((D → ℝ) × (ActiveBranch f → ℝ)) →ₗ[ℝ] (B → ℝ) where
  toFun y := M.boundary y.1 + responseLinear (fun j : ActiveBranch f => m j) y.2
  map_add' x y := by simp; abel
  map_smul' a x := by simp [smul_add]

variable (hmin : ∀ j b x,m j b≤ M.response j b x (f j))
variable (hatt : ∀ j b,∃ x,M.response j b x (f j)=m j b)
variable (z : D → ℝ) (lam : J → ℝ) (hlam : ∀ j,0< lam j)
variable (hcone : Polyhedral.Nonnegative M.row (assemble z lam f))

/-- Only the nonzero private blocks are allowed independent scalar variations.
All boundary variables remain free, including when no private block is active. -/
def activeCapacityEmbedding : LinearMap.ker (activeClosureLinear M f m) →ₗ[ℝ]
    Polyhedral.tightKernel M.row (assemble z lam f) where
  toFun y := ⟨assemble y.1.1 (extendActiveScales f y.1.2) f,by
    intro r hr
    rcases r with ⟨j,i⟩ | ⟨b,x⟩
    · change M.internal j i (lam j • f j)=0 at hr
      rw [map_smul,smul_eq_mul] at hr
      have hi := (mul_eq_zero.mp hr).resolve_left (ne_of_gt (hlam j))
      change M.internal j i (extendActiveScales f y.1.2 j • f j)=0
      rw [map_smul,hi,smul_zero]
    · have hx := tight_boundary_uses_minima M f m hmin hatt z lam hlam hcone b x hr
      have he := congrFun (LinearMap.mem_ker.mp y.2) b
      change M.boundary y.1.1 b+(∑ j : ActiveBranch f,y.1.2 j*m j b)=0 at he
      rw [←sum_extendActiveScales f y.1.2 (fun j => m j b)] at he
      change M.boundary y.1.1 b+∑ j,M.response j b (x j)
        (extendActiveScales f y.1.2 j • f j)=0
      simpa only [map_smul,smul_eq_mul,hx] using he⟩
  map_add' x y := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · ext j k
      simp [assemble,add_smul]
  map_smul' a x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · ext j k
      simp [assemble,smul_smul,mul_assoc]

theorem activeCapacityEmbedding_injective :
    Function.Injective (activeCapacityEmbedding M f m hmin hatt z lam hlam hcone) := by
  intro x y hxy
  have he := congrArg Subtype.val hxy
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun w : Global J K D => w.1) he
  · funext j
    have h := congrArg (fun w : Global J K D => w.2 j.1) he
    change extendActiveScales f x.1.2 j • f j=extendActiveScales f y.1.2 j • f j at h
    rw [extendActiveScales_active,extendActiveScales_active] at h
    obtain ⟨k,hk⟩ : ∃ k,f j k≠0 := by
      by_contra hn
      push_neg at hn
      exact j.2 (funext hn)
    have hh := congrFun h k
    simp only [Pi.smul_apply,smul_eq_mul] at hh
    exact mul_right_cancel₀ hk hh

include hmin hatt hlam in
/-- Full separator capacity, counting exactly the nonzero private blocks.
There is no hypothesis excluding zero blocks or requiring private rigidity. -/
theorem active_separator_capacity
    (hext : Polyhedral.ExtremeRay M.row (assemble z lam f)) :
    Fintype.card (ActiveBranch f)≤ Fintype.card B-Fintype.card D+1 := by
  have hle := LinearMap.finrank_le_finrank_of_injective
    (activeCapacityEmbedding_injective M f m hmin hatt z lam hlam hext.1)
  rw [hext.tightKernel_eq_span,finrank_span_singleton hext.2.1] at hle
  have hnull := (activeClosureLinear M f m).ker.finrank_quotient_add_finrank
  rw [(activeClosureLinear M f m).quotKerEquivRange.finrank_eq,
    Module.finrank_prod,Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card] at hnull
  have hrange := Submodule.finrank_le (activeClosureLinear M f m).range
  rw [Module.finrank_fintype_fun_eq_card] at hrange
  change Module.finrank ℝ (activeClosureLinear M f m).ker≤1 at hle
  omega

end Gluing
end GraphicalZonotopes

end
end
end BundlePart98

section BundlePart99
/- Source: Papers/GraphicalZonotopes/SeparatorTheorems.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Separator
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V J : Type*} [Fintype V] [LinearOrder V]
local instance : DecidableEq V := LinearOrder.toDecidableEq
variable [Fintype J] [DecidableEq J]
variable {G : SimpleGraph V} {B : Finset V} {A : J → Finset V}

noncomputable instance branchChoiceInhabited (j : J) : Inhabited (BranchChoice A j) :=
  ⟨⟨∅,empty_subset _⟩⟩

/-- The conditional response is the actual minimum over every private subset,
including all variables whose selected coefficient happens to be zero. -/
def conditionalMin (h : Partition G B A) (f : ∀ j,privateIndex G B A j → ℝ)
    (j : J) (b : BoundaryRow G B) : ℝ :=
  univ.inf' univ_nonempty (fun X : BranchChoice A j => (rowData h).response j b X (f j))

theorem conditionalMin_le (h : Partition G B A) (f : ∀ j,privateIndex G B A j → ℝ)
    (j : J) (b : BoundaryRow G B) (X : BranchChoice A j) :
    conditionalMin h f j b≤(rowData h).response j b X (f j) :=
  Finset.inf'_le _ (mem_univ X)

theorem conditionalMin_attained (h : Partition G B A)
    (f : ∀ j,privateIndex G B A j → ℝ) (j : J) (b : BoundaryRow G B) :
    ∃ X : BranchChoice A j,(rowData h).response j b X (f j)=conditionalMin h f j b := by
  obtain ⟨X,_,he⟩ := Finset.exists_mem_eq_inf' (s := univ) univ_nonempty
    (fun X : BranchChoice A j => (rowData h).response j b X (f j))
  exact ⟨X,he.symm⟩

abbrev BoundaryEdge (G : SimpleGraph V) (B : Finset V) :=
  {e : OrientedEdge G // e.1.1∈B ∧ e.1.2∈B}
noncomputable instance boundaryEdgeFintype : Fintype (BoundaryEdge G B) := by
  classical
  infer_instance

def boundaryRowEquiv : BoundaryRow G B ≃
    Σ e : BoundaryEdge G B,{S : Finset V // S⊆commonNeighbors G e.1.1.1 e.1.1.2∩B} where
  toFun r := ⟨⟨r.1.1,r.2.1,r.2.2.1⟩,
    ⟨r.1.2.1,subset_inter (mem_powerset.mp r.1.2.2) r.2.2.2⟩⟩
  invFun r := ⟨⟨r.1.1,⟨r.2.1,mem_powerset.mpr (r.2.2.trans inter_subset_left)⟩⟩,
    r.1.2.1,r.1.2.2,r.2.2.trans inter_subset_right⟩
  left_inv r := rfl
  right_inv r := rfl

def subsetPowersetEquiv (T : Finset V) : {S : Finset V // S⊆T} ≃ ↥T.powerset where
  toFun S := ⟨S.1,mem_powerset.mpr S.2⟩
  invFun S := ⟨S.1,mem_powerset.mp S.2⟩
  left_inv S := rfl
  right_inv S := rfl

/-- Exactly one row for each unordered boundary edge and each subset of its
common neighbors in the induced boundary graph. -/
theorem boundaryRow_card : Fintype.card (BoundaryRow G B)=
    ∑ e : BoundaryEdge G B,2^(commonNeighbors G e.1.1.1 e.1.1.2∩B).card := by
  rw [Fintype.card_congr (boundaryRowEquiv (G := G) (B := B)),Fintype.card_sigma]
  apply sum_congr rfl
  intro e he
  rw [Fintype.card_congr (subsetPowersetEquiv _)]
  simp only [Fintype.card_coe, card_powerset]

def boundaryCliques (G : SimpleGraph V) (B : Finset V) : Finset (Finset V) := by
  classical
  exact B.powerset.filter (IsCliqueCoordinate G)

def boundaryCliqueEquiv : boundaryIndex G B ≃ ↥(boundaryCliques G B) where
  toFun C := ⟨C.1.1,by exact mem_filter.mpr ⟨mem_powerset.mpr C.2,C.1.2⟩⟩
  invFun C := ⟨⟨C.1,by exact (mem_filter.mp C.2).2⟩,
    by exact mem_powerset.mp (mem_filter.mp C.2).1⟩
  left_inv C := rfl
  right_inv C := rfl

/-- The boundary-coordinate dimension is precisely the number of cliques
of size at least two in the induced boundary graph. -/
theorem boundaryIndex_card : Fintype.card (boundaryIndex G B)=(boundaryCliques G B).card := by
  rw [Fintype.card_congr (boundaryCliqueEquiv (G := G) (B := B)),Fintype.card_coe]

/-- Lemma5.1 in original graphical coordinates, including zero private blocks.
The left side counts exactly the branches carrying a nonzero Möbius block. -/
theorem separator_capacity_for_function (h : Partition G B A)
    (z : graphicalFunctionSpace G) (hz : ExtremeSupermodular z.1) :
    Fintype.card (Gluing.ActiveBranch (((functionEquiv h).symm z).2))≤
      (∑ e : BoundaryEdge G B,2^(commonNeighbors G e.1.1.1 e.1.1.2∩B).card)-
        (boundaryCliques G B).card+1 := by
  let x : Coordinates G B A := (functionEquiv h).symm z
  have hxe : globalFunctionMap h x=z.1 := by
    exact congrArg Subtype.val ((functionEquiv h).apply_symm_apply z)
  have hex : Polyhedral.ExtremeRay (rowData h).row x :=
    (rowData_extreme_iff h x).mpr (by rw [hxe]; exact hz)
  have hass : Gluing.assemble x.1 (fun _ : J => (1 : ℝ)) x.2=x := by
    apply Prod.ext
    · rfl
    · funext j
      exact one_smul ℝ (x.2 j)
  have hb := Gluing.active_separator_capacity (rowData h) x.2 (conditionalMin h x.2)
    (conditionalMin_le h x.2) (conditionalMin_attained h x.2) x.1
    (fun _ : J => (1 : ℝ)) (fun _ => zero_lt_one) (hass.symm ▸ hex)
  rw [boundaryRow_card,boundaryIndex_card] at hb
  exact hb

/-- The literal induced-separator instance of Lemma5.1, with the private
parts equal to all connected components of G minus B. -/
theorem induced_separator_capacity (G : SimpleGraph V) (B : Finset V)
    (z : graphicalFunctionSpace G) (hz : ExtremeSupermodular z.1) :
    Fintype.card (Gluing.ActiveBranch
      (((functionEquiv (componentPartition G B)).symm z).2))≤
      (∑ e : BoundaryEdge G B,2^(commonNeighbors G e.1.1.1 e.1.1.2∩B).card)-
        (boundaryCliques G B).card+1 := by
  classical
  exact separator_capacity_for_function (componentPartition G B) z hz

section PositiveGluing
variable (h : Partition G B A)
variable (f : ∀ j,privateIndex G B A j → ℝ)
variable (z : boundaryIndex G B → ℝ) (lam : J → ℝ)
variable (hlam : ∀ j,0< lam j) (hf : ∀ j,f j≠0)
variable (hi : ∀ j r,0≤(rowData h).internal j r (f j))
variable (hprivate : ∀ j g,(rowData h).PrivateKernel f (conditionalMin h f) j g →
  ∃ c : ℝ,g=c • f j)
variable (hclose : (rowData h).Closure (conditionalMin h f) z lam)
include hlam hf hi hprivate hclose

def gluedCoordinates : Coordinates G B A := Gluing.assemble z lam f

theorem glued_supermodular :
    Supermodular (globalFunctionMap h (gluedCoordinates f z lam)) := by
  apply (rowData_nonnegative_iff h _).mp
  exact Gluing.assembled_nonnegative (rowData h) f (conditionalMin h f)
    (conditionalMin_le h f) hi z lam hlam hclose

/-- Theorem5.4's exact isomorphism, now for the complete original graphical
common-zero space rather than an abstract inequality model. -/
def graphicalTightRelationEquiv :
    Polyhedral.tightKernel (contextRow G) (functionEquiv h (gluedCoordinates f z lam)) ≃ₗ[ℝ]
      LinearMap.ker ((rowData h).relationLinear (conditionalMin h f)) :=
  (graphicalTightEquiv h (gluedCoordinates f z lam)
    (Gluing.assembled_nonnegative (rowData h) f (conditionalMin h f)
      (conditionalMin_le h f) hi z lam hlam hclose)).symm.trans
    (Gluing.tightRelationEquiv (rowData h) f (conditionalMin h f)
      (conditionalMin_le h f) (conditionalMin_attained h f) z lam hlam hclose
      hprivate hf (rowData_boundary_injective h))

/-- Exact common-zero-space dimension in Theorem5.4, with genuine conditional
minima and every zero coefficient slot retained in its ambient private space. -/
theorem graphical_tight_finrank_eq_relation_finrank :
    Module.finrank ℝ
      (Polyhedral.tightKernel (contextRow G) (functionEquiv h (gluedCoordinates f z lam)))=
    Module.finrank ℝ (LinearMap.ker ((rowData h).relationLinear (conditionalMin h f))) :=
  (graphicalTightRelationEquiv h f z lam hlam hf hi hprivate hclose).finrank_eq

/-- The complete extremality equivalence in Theorem5.4. -/
theorem graphical_extreme_iff_relation_finrank_one :
    ExtremeSupermodular (globalFunctionMap h (gluedCoordinates f z lam)) ↔
      Module.finrank ℝ (LinearMap.ker ((rowData h).relationLinear (conditionalMin h f)))=1 := by
  rw [←rowData_extreme_iff]
  exact Gluing.extreme_iff_relation_finrank_one (rowData h) f (conditionalMin h f)
    (conditionalMin_le h f) (conditionalMin_attained h f) hi z lam hlam hclose
    hprivate hf (rowData_boundary_injective h) (rowData_pointed h)

/-- The unique relation is precisely the positive construction vector, and
the number of branches satisfies the exact induced-boundary capacity. -/
theorem graphical_positive_relation_and_capacity
    (he : ExtremeSupermodular (globalFunctionMap h (gluedCoordinates f z lam))) :
    LinearMap.ker ((rowData h).relationLinear (conditionalMin h f))=Submodule.span ℝ {lam} ∧
    Fintype.card J≤
      (∑ e : BoundaryEdge G B,2^(commonNeighbors G e.1.1.1 e.1.1.2∩B).card)-
        (boundaryCliques G B).card+1 := by
  have hd := (graphical_extreme_iff_relation_finrank_one h f z lam hlam hf hi hprivate hclose).mp he
  refine ⟨Gluing.relationKernel_eq_span_scales (rowData h) (conditionalMin h f) z lam
    hlam hclose hd,?_⟩
  have hb := Gluing.branch_count_le_capacity (rowData h) (conditionalMin h f)
    (rowData_boundary_injective h) hd
  rw [boundaryRow_card,boundaryIndex_card] at hb
  exact hb

end PositiveGluing
end Separator
end GraphicalZonotopes

end
end
end BundlePart99

section BundlePart100
/- Source: Papers/GraphicalZonotopes/CliqueSeparatorCapacity.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Separator
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [LinearOrder V]
local instance : DecidableEq V := LinearOrder.toDecidableEq
variable {G : SimpleGraph V} {B : Finset V}

/-- A boundary edge is exactly one strictly ordered pair in the boundary clique.
The order is used only to count each unordered edge once. -/
def cliqueBoundaryEdgeEquiv (hB : G.IsClique B) :
    BoundaryEdge G B ≃ ↥((B ×ˢ B).filter (fun p : V × V => p.1 < p.2)) where
  toFun e := ⟨e.1.1,mem_filter.mpr ⟨mem_product.mpr e.2,e.1.2.1⟩⟩
  invFun p := ⟨⟨p.1,(mem_filter.mp p.2).2,
      hB ((mem_product.mp (mem_filter.mp p.2).1).1)
        ((mem_product.mp (mem_filter.mp p.2).1).2)
        (ne_of_lt (mem_filter.mp p.2).2)⟩,
      mem_product.mp (mem_filter.mp p.2).1⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem boundaryEdge_card_of_clique (hB : G.IsClique B) :
    Fintype.card (BoundaryEdge G B)=B.card.choose 2 := by
  rw [Fintype.card_congr (cliqueBoundaryEdgeEquiv hB),Fintype.card_coe]
  convert Finset.card_product_filter_lt (s := B) using 2 <;> congr 1

/-- Within a clique, the common neighbors of an edge are all boundary vertices
except its two endpoints, including every unused conditioning bit. -/
theorem boundary_commonNeighbors_of_clique (hB : G.IsClique B)
    {u v : V} (hu : u∈B) (hv : v∈B) (huv : u≠ v) :
    commonNeighbors G u v∩B=(B.erase u).erase v := by
  ext w
  simp only [mem_inter,mem_commonNeighbors,mem_erase]
  constructor
  · rintro ⟨⟨huw,hvw⟩,hw⟩
    exact ⟨(G.ne_of_adj hvw).symm,(G.ne_of_adj huw).symm,hw⟩
  · rintro ⟨hwv,hwu,hw⟩
    exact ⟨⟨hB hu hw hwu.symm,hB hv hw hwv.symm⟩,hw⟩

theorem boundary_commonNeighbors_card_of_clique (hB : G.IsClique B)
    {u v : V} (hu : u∈B) (hv : v∈B) (huv : u≠ v) :
    (commonNeighbors G u v∩B).card=B.card-2 := by
  rw [boundary_commonNeighbors_of_clique hB hu hv huv,
    card_erase_of_mem (mem_erase.mpr ⟨huv.symm,hv⟩),card_erase_of_mem hu]
  omega

theorem boundaryRow_card_of_clique (hB : G.IsClique B) :
    Fintype.card (BoundaryRow G B)=B.card.choose 2*2^(B.card-2) := by
  rw [boundaryRow_card]
  have he : ∀ e : BoundaryEdge G B,
      (commonNeighbors G e.1.1.1 e.1.1.2∩B).card=B.card-2 := by
    intro e
    exact boundary_commonNeighbors_card_of_clique hB e.2.1 e.2.2
      (ne_of_lt e.1.2.1)
  simp_rw [he]
  simp [boundaryEdge_card_of_clique hB,Nat.mul_comm]

private theorem small_subsets_eq :
    B.powerset.filter (fun C => ¬2≤ C.card)=insert ∅ (B.image singleton) := by
  ext C
  simp only [mem_filter,mem_powerset,mem_insert,mem_image]
  constructor
  · rintro ⟨hCB,hC⟩
    have hc : C.card=0 ∨ C.card=1 := by omega
    rcases hc with hc | hc
    · exact Or.inl (card_eq_zero.mp hc)
    · obtain ⟨v,rfl⟩ := card_eq_one.mp hc
      exact Or.inr ⟨v,hCB (mem_singleton_self v),rfl⟩
  · rintro (rfl | ⟨v,hv,rfl⟩)
    · simp
    · simp [singleton_subset_iff,hv]

private theorem small_subsets_card :
    (B.powerset.filter (fun C => ¬2≤ C.card)).card=B.card+1 := by
  rw [small_subsets_eq,card_insert_of_notMem]
  · rw [card_image_of_injective B singleton_injective]
  · simp

theorem boundaryCliques_card_of_clique (hB : G.IsClique B) :
    (boundaryCliques G B).card=2^B.card-B.card-1 := by
  have he : boundaryCliques G B=B.powerset.filter (fun C => 2≤ C.card) := by
    ext C
    simp only [boundaryCliques,mem_filter,mem_powerset,IsCliqueCoordinate]
    constructor
    · rintro ⟨hCB,hC,_⟩
      exact ⟨hCB,hC⟩
    · rintro ⟨hCB,hC⟩
      exact ⟨hCB,hC,fun u hu v hv huv => hB (hCB hu) (hCB hv) huv⟩
  rw [he]
  have hc := card_filter_add_card_filter_not (s := B.powerset) (p := fun C => 2≤ C.card)
  rw [small_subsets_card,card_powerset] at hc
  omega

/-- Theorem7.2, with exactly the connected components of the actual graph after
removing the clique. All zero coefficient slots remain in their private blocks;
only genuinely nonzero blocks are counted on the left. -/
theorem clique_separator_capacity (hB : G.IsClique B) (hs : 2≤ B.card)
    (z : graphicalFunctionSpace G) (hz : ExtremeSupermodular z.1) :
    Fintype.card (Gluing.ActiveBranch
      (((functionEquiv (componentPartition G B)).symm z).2))≤ cliqueCapacity B.card := by
  have h := induced_separator_capacity G B z hz
  rw [←boundaryRow_card,boundaryRow_card_of_clique hB,
    boundaryCliques_card_of_clique hB] at h
  exact h

@[simp] theorem cliqueCapacity_two : cliqueCapacity 2=1 := by norm_num [cliqueCapacity, Nat.choose]
@[simp] theorem cliqueCapacity_three : cliqueCapacity 3=3 := by norm_num [cliqueCapacity, Nat.choose]
@[simp] theorem cliqueCapacity_four : cliqueCapacity 4=14 := by norm_num [cliqueCapacity, Nat.choose]

end Separator
end GraphicalZonotopes

end
end
end BundlePart100

section BundlePart101
/- Source: Papers/GraphicalZonotopes/SeparatorKernelSemantics.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Gluing

variable {B J D : Type*} {K I X : J → Type*}

/-- The paper's private common kernel, as an actual linear subspace. It
retains every internal zero equation and every minimizer-difference equation. -/
def Data.privateKernelSpace (M : Data B J K D I X)
    (f : ∀ j, K j → ℝ) (m : J → B → ℝ) (j : J) :
    Submodule ℝ (K j → ℝ) where
  carrier := {g | M.PrivateKernel f m j g}
  zero_mem' := by
    constructor
    · intro i hi
      simp
    · intro b x y hx hy
      simp
  add_mem' := by
    intro g h hg hh
    constructor
    · intro i hi
      rw [map_add,hg.1 i hi,hh.1 i hi,add_zero]
    · intro b x y hx hy
      rw [map_add,map_add,hg.2 b x y hx hy,hh.2 b x y hx hy]
  smul_mem' := by
    intro a g hg
    constructor
    · intro i hi
      rw [map_smul,hg.1 i hi,smul_zero]
    · intro b x y hx hy
      rw [map_smul,map_smul,hg.2 b x y hx hy]

@[simp] theorem mem_privateKernelSpace (M : Data B J K D I X)
    (f : ∀ j, K j → ℝ) (m : J → B → ℝ) (j : J) (g : K j → ℝ) :
    g ∈ M.privateKernelSpace f m j ↔ M.PrivateKernel f m j g := Iff.rfl

theorem self_mem_privateKernelSpace (M : Data B J K D I X)
    (f : ∀ j, K j → ℝ) (m : J → B → ℝ) (j : J) :
    f j ∈ M.privateKernelSpace f m j :=
  ⟨fun _ h => h, fun _ _ _ hx hy => hx.trans hy.symm⟩

/-- The containment hypothesis used by the gluing proof is exactly the
paper's assertion that the private kernel is the span of the chosen vector.
The reverse containment follows from the actual equations at that vector. -/
theorem privateKernelSpace_eq_span_iff (M : Data B J K D I X)
    (f : ∀ j, K j → ℝ) (m : J → B → ℝ) (j : J) :
    M.privateKernelSpace f m j=Submodule.span ℝ {f j} ↔
      ∀ g, M.PrivateKernel f m j g → ∃ c : ℝ, g=c • f j := by
  constructor
  · intro he g hg
    have hmem : g ∈ M.privateKernelSpace f m j := hg
    rw [he,Submodule.mem_span_singleton] at hmem
    obtain ⟨c,hc⟩ := hmem
    exact ⟨c,hc.symm⟩
  · intro hline
    apply le_antisymm
    · intro g hg
      obtain ⟨c,hc⟩ := hline g hg
      exact Submodule.mem_span_singleton.mpr ⟨c,hc.symm⟩
    · apply Submodule.span_le.mpr
      intro g hg
      have he : g=f j := Set.mem_singleton_iff.mp hg
      subst g
      exact self_mem_privateKernelSpace M f m j

end Gluing
end GraphicalZonotopes

end
end
end BundlePart101

section BundlePart102
/- Source: Papers/GraphicalZonotopes/SeparatorLifts.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Separator
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V J : Type*} [Fintype V] [LinearOrder V]
local instance : DecidableEq V := LinearOrder.toDecidableEq
variable [Fintype J] [DecidableEq J]
variable {G : SimpleGraph V} {B : Finset V} {A : J → Finset V}

/-- A branch may carry any boundary lift, in addition to its private block. -/
def branchWithLift (h : Partition G B A) (j : J)
    (f : privateIndex G B A j → ℝ) (l : boundaryIndex G B → ℝ) : SetFunction V :=
  boundaryFunctionMap h l+privateFunctionMap h j f

/-- Every graphical branch whose other private blocks vanish has exactly
this form. Thus choosing the zero boundary lift loses no original branch. -/
theorem branch_reconstruction (h : Partition G B A) (j : J)
    (g : graphicalFunctionSpace G)
    (hg : ∀ k,k≠ j → ((functionEquiv h).symm g).2 k=0) :
    g.1=branchWithLift h j (((functionEquiv h).symm g).2 j)
      (((functionEquiv h).symm g).1) := by
  let x : Coordinates G B A := (functionEquiv h).symm g
  have he : globalFunctionMap h x=g.1 :=
    congrArg Subtype.val ((functionEquiv h).apply_symm_apply g)
  rw [←he,function_decompose]
  unfold branchWithLift
  congr 1
  apply sum_eq_single j
  · intro k hk hkj
    rw [hg k hkj,map_zero]
  · simp

@[simp] theorem private_coordinate_eq_mobius (h : Partition G B A)
    (g : graphicalFunctionSpace G) (j : J) (C : privateIndex G B A j) :
    ((functionEquiv h).symm g).2 j C=mobius g.1 C.1.1 := rfl

/-- Ordinary coefficient support on a branch implies the exact zero pattern
needed above; this connects the presentation to the paper's induced branches. -/
theorem other_private_blocks_zero_of_support (h : Partition G B A) (j : J)
    (g : graphicalFunctionSpace G)
    (hg : CoefficientSupportedOn (B∪A j) (mobius g.1)) :
    ∀ k,k≠ j → ((functionEquiv h).symm g).2 k=0 := by
  intro k hkj
  funext C
  rw [private_coordinate_eq_mobius]
  apply hg C.1.1
  intro hCj
  obtain ⟨u,huC,huB⟩ := Finset.not_subset.mp C.2.1
  have huk : u∈A k := (mem_union.mp (C.2.2 huC)).resolve_left huB
  have huj : u∈A j := (mem_union.mp (hCj huC)).resolve_left huB
  exact Finset.disjoint_left.mp (h.private_disjoint hkj) huk huj

theorem branchChoice_union_inter_boundary (h : Partition G B A)
    {S : Finset V} (hS : S⊆B) (j : J) (X : BranchChoice A j) :
    (S∪X.1)∩B=S := by
  ext v
  constructor
  · intro hv
    obtain ⟨hvU,hvB⟩ := mem_inter.mp hv
    rcases mem_union.mp hvU with hvS | hvX
    · exact hvS
    · exact False.elim (Finset.disjoint_left.mp (h.boundary_disjoint j) hvB (X.2 hvX))
  · intro hv
    exact mem_inter.mpr ⟨mem_union_left _ hv,hS hv⟩

theorem boundary_not_mem_branchChoice (h : Partition G B A)
    (j : J) (X : BranchChoice A j) {u : V} (huB : u∈B) : u∉X.1 := by
  intro hu
  exact Finset.disjoint_left.mp (h.boundary_disjoint j) huB (X.2 hu)

/-- Internal rows are independent of the arbitrary boundary lift as well. -/
theorem internal_boundary_lift (h : Partition G B A) (j : J)
    (f : privateIndex G B A j → ℝ) (l : boundaryIndex G B → ℝ)
    (r : InternalRow G B A j) :
    delta (branchWithLift h j f l) r.1.1.1.1 r.1.1.1.2 r.1.2.1=
      (rowData h).internal j r f := by
  rw [branchWithLift,delta_add]
  have hz : delta (boundaryFunctionMap h l) r.1.1.1.1 r.1.1.1.2 r.1.2.1=0 := by
    rcases r.2.1 with hu | hv
    · have huB : r.1.1.1.1∉B := fun hb =>
        Finset.disjoint_left.mp (h.boundary_disjoint j) hb hu
      exact delta_zero_of_outside_mobius_support (boundaryFunction_supported h l)
        (ne_of_lt r.1.1.2.1) huB (context_left_not_mem r.1) (context_right_not_mem r.1)
    · have hvB : r.1.1.1.2∉B := fun hb =>
        Finset.disjoint_left.mp (h.boundary_disjoint j) hb hv
      rw [delta_comm r.1.1.1.1]
      exact delta_zero_of_outside_mobius_support (boundaryFunction_supported h l)
        (ne_of_gt r.1.1.2.1) hvB (context_right_not_mem r.1) (context_left_not_mem r.1)
  rw [hz,zero_add]
  rfl

/-- Every original lifted response is its private response plus the boundary
slack image, evaluated at the actual conditioning set. -/
theorem response_boundary_lift (h : Partition G B A) (j : J)
    (f : privateIndex G B A j → ℝ) (l : boundaryIndex G B → ℝ)
    (b : BoundaryRow G B) (X : BranchChoice A j) :
    delta (branchWithLift h j f l) b.1.1.1.1 b.1.1.1.2 (b.1.2.1∪X.1)=
      (rowData h).boundary l b+(rowData h).response j b X f := by
  have hu : b.1.1.1.1∉b.1.2.1∪X.1 := by
    simp only [mem_union,not_or]
    exact ⟨context_left_not_mem b.1,boundary_not_mem_branchChoice h j X b.2.1⟩
  have hv : b.1.1.1.2∉b.1.2.1∪X.1 := by
    simp only [mem_union,not_or]
    exact ⟨context_right_not_mem b.1,boundary_not_mem_branchChoice h j X b.2.2.1⟩
  rw [branchWithLift,delta_add,
    delta_inter_mobius_support (boundaryFunction_supported h l) (ne_of_lt b.1.1.2.1) hu hv,
    branchChoice_union_inter_boundary h b.2.2.2 j X]
  rfl

def liftedConditionalMin (h : Partition G B A)
    (f : ∀ j,privateIndex G B A j → ℝ) (l : J → boundaryIndex G B → ℝ)
    (j : J) (b : BoundaryRow G B) : ℝ :=
  univ.inf' univ_nonempty (fun X : BranchChoice A j =>
    delta (branchWithLift h j (f j) (l j)) b.1.1.1.1 b.1.1.1.2 (b.1.2.1∪X.1))

/-- Conditional minima transform by precisely the same boundary image. -/
theorem liftedConditionalMin_eq (h : Partition G B A)
    (f : ∀ j,privateIndex G B A j → ℝ) (l : J → boundaryIndex G B → ℝ)
    (j : J) (b : BoundaryRow G B) :
    liftedConditionalMin h f l j b=conditionalMin h f j b+(rowData h).boundary (l j) b := by
  apply le_antisymm
  · obtain ⟨X,hX⟩ := conditionalMin_attained h f j b
    have hle := Finset.inf'_le (s := univ)
      (fun X : BranchChoice A j =>
        delta (branchWithLift h j (f j) (l j)) b.1.1.1.1 b.1.1.1.2 (b.1.2.1∪X.1))
      (mem_univ X)
    rw [response_boundary_lift,hX,add_comm] at hle
    exact hle
  · apply Finset.le_inf'
    intro X hX
    rw [response_boundary_lift]
    have hh := conditionalMin_le h f j b X
    linarith

/-- The minimizing subsets, and hence every private minimizer-difference
row in the paper, are unchanged by arbitrary boundary lifts. -/
theorem lifted_minimizer_iff (h : Partition G B A)
    (f : ∀ j,privateIndex G B A j → ℝ) (l : J → boundaryIndex G B → ℝ)
    (j : J) (b : BoundaryRow G B) (X : BranchChoice A j) :
    delta (branchWithLift h j (f j) (l j)) b.1.1.1.1 b.1.1.1.2 (b.1.2.1∪X.1)=
      liftedConditionalMin h f l j b ↔
      (rowData h).response j b X (f j)=conditionalMin h f j b := by
  rw [response_boundary_lift,liftedConditionalMin_eq]
  constructor <;> intro he <;> linarith

/-- The quotient response map is literally independent of every boundary
lift; this proves the equivalence of the zero-lift presentation in the main
graphical gluing theorem with the paper's arbitrary branch functions. -/
theorem lifted_relationLinear_eq (h : Partition G B A)
    (f : ∀ j,privateIndex G B A j → ℝ) (l : J → boundaryIndex G B → ℝ) :
    (rowData h).relationLinear (liftedConditionalMin h f l)=
      (rowData h).relationLinear (conditionalMin h f) := by
  have he : liftedConditionalMin h f l=
      fun j b => conditionalMin h f j b+(rowData h).boundary (l j) b := by
    funext j b
    exact liftedConditionalMin_eq h f l j b
  rw [he]
  exact Gluing.relationLinear_boundary_lift (rowData h) (conditionalMin h f) l

/-- The closing relation for arbitrary lifted branches is exactly the
private-coordinate closing relation after transferring the same scaled
boundary lifts into the closing function. This uses the actual conditional
minima, not only their classes in the response quotient. -/
theorem lifted_closure_iff (h : Partition G B A)
    (f : ∀ j,privateIndex G B A j → ℝ) (l : J → boundaryIndex G B → ℝ)
    (z : boundaryIndex G B → ℝ) (lam : J → ℝ) :
    (rowData h).Closure (liftedConditionalMin h f l) z lam ↔
      (rowData h).Closure (conditionalMin h f) (z+∑ j,lam j • l j) lam := by
  have he (b : BoundaryRow G B) :
      (rowData h).boundary z b+∑ j,lam j*liftedConditionalMin h f l j b =
        (rowData h).boundary (z+∑ j,lam j • l j) b+
          ∑ j,lam j*conditionalMin h f j b := by
    simp only [liftedConditionalMin_eq,map_add,map_sum,map_smul,
      Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
      mul_add,Finset.sum_add_distrib]
    ring
  unfold Gluing.Data.Closure
  simp only [he]

/-- A prescribed private-coordinate closing function therefore works with
any chosen branch boundary lifts after the compensating subtraction. -/
theorem lifted_closure_transfer (h : Partition G B A)
    (f : ∀ j,privateIndex G B A j → ℝ) (l : J → boundaryIndex G B → ℝ)
    (z : boundaryIndex G B → ℝ) (lam : J → ℝ) :
    (rowData h).Closure (liftedConditionalMin h f l) (z-∑ j,lam j • l j) lam ↔
      (rowData h).Closure (conditionalMin h f) z lam := by
  rw [lifted_closure_iff,sub_add_cancel]

/-- The same assembled original function is obtained by transferring each
branch boundary lift into the closing boundary coordinate. -/
theorem assembled_boundary_lift_eq (h : Partition G B A)
    (f : ∀ j,privateIndex G B A j → ℝ) (l : J → boundaryIndex G B → ℝ)
    (z : boundaryIndex G B → ℝ) (lam : J → ℝ) :
    boundaryFunctionMap h z+∑ j,lam j • branchWithLift h j (f j) (l j)=
      globalFunctionMap h (Gluing.assemble (z+∑ j,lam j • l j) lam f) := by
  rw [function_decompose]
  simp only [branchWithLift,Gluing.assemble,map_add,map_sum,map_smul,smul_add,sum_add_distrib]
  abel

end Separator
end GraphicalZonotopes

end
end
end BundlePart102

section BundlePart103
/- Source: Papers/GraphicalZonotopes/Translation.lean -/






@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem singleton_add_eq_vadd (t : V → ℝ) (Q : Set (V → ℝ)) :
    ({t} : Set (V → ℝ))+Q=t+ᵥQ := by
  rw [Set.singleton_add, ← Set.image_vadd]
  simp only [vadd_eq_add]

theorem basePolytope_eq_vadd_normalize (z : SetFunction V) :
    basePolytope z=(fun v => z {v})+ᵥbasePolytope (normalize z) := by
  conv_lhs => rw [recover_normalize z]
  rw [basePolytope_translate,singleton_add_eq_vadd]

theorem vectorSpan_basePolytope_normalize (z : SetFunction V) :
    vectorSpan ℝ (basePolytope (normalize z))=vectorSpan ℝ (basePolytope z) := by
  rw [basePolytope_eq_vadd_normalize z,vectorSpan_vadd]

theorem IsExposedSegment.vadd {Q : Set (V → ℝ)} {p q : V → ℝ}
    (h : IsExposedSegment Q p q) (t : V → ℝ) :
    IsExposedSegment (t+ᵥQ) (t+p) (t+q) := by
  obtain ⟨hpq,ℓ,a,hbound,hface⟩ := h
  refine ⟨fun he => hpq (add_left_cancel he),ℓ,ℓ t+a,?_,?_⟩
  · rintro x ⟨y,hy,rfl⟩
    change ℓ t+a ≤ ℓ (t+y)
    rw [map_add]
    exact add_le_add (le_refl (ℓ t)) (hbound y hy)
  · have he : {x ∈ t+ᵥQ | ℓ x=ℓ t+a}=t+ᵥ{x ∈ Q | ℓ x=a} := by
      ext x
      constructor
      · rintro ⟨⟨y,hy,rfl⟩,he⟩
        refine ⟨y,⟨hy,?_⟩,rfl⟩
        change ℓ (t+y)=ℓ t+a at he
        rw [map_add] at he
        exact add_left_cancel he
      · rintro ⟨y,⟨hy,he⟩,rfl⟩
        refine ⟨⟨y,hy,rfl⟩,?_⟩
        change ℓ (t+y)=ℓ t+a
        rw [map_add,he]
    rw [he,hface,vadd_segment]
    simp only [vadd_eq_add]

theorem ActualRootEdge.vadd {Q : Set (V → ℝ)} {u v : V}
    (h : ActualRootEdge Q u v) (t : V → ℝ) : ActualRootEdge (t+ᵥQ) u v := by
  obtain ⟨huv,p,q,hface,a,ha,he⟩ := h
  refine ⟨huv,t+p,t+q,hface.vadd t,a,ha,?_⟩
  calc
    (t+q)-(t+p)=q-p := by abel
    _=a • (basisVector u-basisVector v) := he

theorem actualRootEdge_vadd_iff (Q : Set (V → ℝ)) (t : V → ℝ) (u v : V) :
    ActualRootEdge (t+ᵥQ) u v ↔ ActualRootEdge Q u v := by
  constructor
  · intro h
    have he := h.vadd (-t)
    simpa only [vadd_vadd,neg_add_cancel,zero_vadd] using he
  · exact fun h => h.vadd t

theorem actualDirectionGraph_vadd (Q : Set (V → ℝ)) (t : V → ℝ) :
    actualDirectionGraph (t+ᵥQ)=actualDirectionGraph Q := by
  ext u v
  exact actualRootEdge_vadd_iff Q t u v

theorem actualDirectionGraph_normalize (z : SetFunction V) :
    actualDirectionGraph (basePolytope (normalize z))=actualDirectionGraph (basePolytope z) := by
  rw [basePolytope_eq_vadd_normalize z,actualDirectionGraph_vadd]

theorem normalize_smul (z : SetFunction V) (a : ℝ) :
    normalize (a • z)=a • normalize z := by
  funext S
  simp only [normalize,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,modular,subsetSum]
  rw [mul_sub,Finset.mul_sum]

@[simp] theorem normalize_modular (t : V → ℝ) : normalize (modular t)=0 := by
  funext S
  simp [normalize,modular,subsetSum]

/-- Geometric indecomposability passes to the normalized cone directly.
The proof permits the original polytope to have an arbitrary translation. -/
theorem MinkowskiIndecomposable.extremeSupermodular_normalize {z : SetFunction V}
    (hn : Normalized z) (hs : Supermodular z) (hne : normalize z ≠ 0)
    (hi : MinkowskiIndecomposable (basePolytope z)) : ExtremeSupermodular (normalize z) := by
  have h0n := normalize_translationNormalized hn
  have h0s := hs.normalize
  refine ⟨h0n,h0s,hne,?_⟩
  intro f g hfn hgn hfs hgs hfg
  let t : V → ℝ := fun v => z {v}
  have hftn : Normalized (f+modular t) := by
    change f ∅+subsetSum t ∅=0
    simpa only [subsetSum,Finset.sum_empty,add_zero] using (show f ∅=0 from hfn.1)
  have hfts := hfs.add (modular_supermodular t)
  have hsum : basePolytope (f+modular t)+basePolytope g=basePolytope z := by
    rw [← basePolytope_add hftn hgn.1 hfts hgs]
    congr 1
    calc
      f+modular t+g=(f+g)+modular t := by abel
      _=normalize z+modular t := by rw [hfg]
      _=z := (recover_normalize z).symm
  obtain ⟨a,s,ha,he⟩ := hi.2 (basePolytope (f+modular t)) (basePolytope g)
    (basePolytope_compact hftn hfts) (basePolytope_compact hgn.1 hgs)
    (basePolytope_convex _) (basePolytope_convex _) hsum
  rw [← basePolytope_smul hn hs ha,← basePolytope_translate] at he
  have han : Normalized (a • z+modular s) := by
    change a*z ∅+subsetSum s ∅=0
    simp only [show z ∅=0 from hn,mul_zero,subsetSum,Finset.sum_empty,add_zero]
  have has := (hs.smul ha).add (modular_supermodular s)
  have hefun := congrArg lowerSupport he
  rw [lowerSupport_basePolytope hftn hfts,lowerSupport_basePolytope han has] at hefun
  have hnorm := congrArg normalize hefun
  rw [normalize_add,normalize_modular,add_zero,normalize_eq_self hfn,
    normalize_add,normalize_smul,normalize_modular,add_zero] at hnorm
  exact ⟨a,ha,hnorm⟩

end GraphicalZonotopes

end
end
end BundlePart103

section BundlePart104
/- Source: Papers/GraphicalZonotopes/SeparatorFullDimension.lean -/







@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Separator
open Finset
open scoped BigOperators Pointwise
variable {n : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
variable {G : SimpleGraph (Fin n)} {B : Finset (Fin n)} {A : J → Finset (Fin n)}

/-- Full dimension activates every nonempty actual private component.
A zero private block would remove every coefficient containing one of its
vertices, contradicting the genuine affine dimension of the base polytope. -/
theorem private_block_ne_zero_of_fullDimension (hn : 2≤ n) (h : Partition G B A)
    (z : graphicalFunctionSpace G) (hz : Supermodular z.1)
    (hd : FullDimension (basePolytope z.1)) (j : J) (hAj : (A j).Nonempty) :
    ((functionEquiv h).symm z).2 j≠0 := by
  classical
  intro hzero
  obtain ⟨v,hvj⟩:=hAj
  have hvB : v∉B:=fun hvB =>
    disjoint_left.mp (h.boundary_disjoint j) hvB hvj
  have hy:=(mobius_cliqueSupported_iff G z.1).mpr z.2
  have hkill : ∀ C : Finset (Fin n),v∈C → mobius z.1 C=0 := by
    intro C hvC
    by_cases hC : IsCliqueCoordinate G C
    · have hCB : ¬C⊆B:=fun hCB => hvB (hCB hvC)
      obtain ⟨k,hCk,hunique⟩:=h.clique_unique_branch ⟨C,hC⟩ hCB
      have hvk : v∈A k:=(mem_union.mp (hCk hvC)).resolve_left hvB
      have hkj : k=j := by
        by_contra hkj
        exact disjoint_left.mp (h.private_disjoint hkj) hvk hvj
      subst k
      let D : privateIndex G B A j:=⟨⟨C,hC⟩,hCB,hCk⟩
      have he:=congrFun hzero D
      simpa only [private_coordinate_eq_mobius,Pi.zero_apply] using he
    · exact coefficient_zero_of_not_clique hy C hC
  have hdep : DependsOn z.1 (univ.erase v) := by
    rw [← zeta_mobius z.1]
    apply zeta_dependsOn
    intro C hC
    apply hkill C
    by_contra hvC
    apply hC
    intro w hw
    exact mem_erase.mpr ⟨fun he => hvC (he ▸ hw),mem_univ _⟩
  have hdim : Module.finrank ℝ (vectorSpan ℝ (basePolytope z.1))=n-1 := by
    simpa only [FullDimension,Fintype.card_fin] using hd
  have he:=fullDimension_dependsOn_eq_univ hn z.2.1 hz hdim hdep
  have hmem : v∈univ.erase v:=by rw [he]; exact mem_univ _
  exact notMem_erase _ _ hmem

theorem componentPart_nonempty (G : SimpleGraph (Fin n)) (B : Finset (Fin n))
    (c : (outsideGraph G B).ConnectedComponent) : (componentPart G B c).Nonempty := by
  obtain ⟨v,hv⟩:=c.exists_rep
  exact ⟨v.1,(mem_componentPart G B c v.1).mpr ⟨v.2,hv⟩⟩

theorem full_dimension_clique_separator_bound (hn : 2≤ n) (B : Finset (Fin n))
    (hB : G.IsClique B) (hs : 2≤ B.card) (z : graphicalFunctionSpace G)
    (hz : ExtremeSupermodular z.1) (hd : FullDimension (basePolytope z.1)) :
    Nat.card ((outsideGraph G B).ConnectedComponent)≤ cliqueCapacity B.card := by
  classical
  let x:=(functionEquiv (componentPartition G B)).symm z
  have hactive : ∀ j,x.2 j≠0:=fun j =>
    private_block_ne_zero_of_fullDimension hn (componentPartition G B) z hz.2.1 hd j
      (componentPart_nonempty G B j)
  let e : Gluing.ActiveBranch x.2 ≃ (outsideGraph G B).ConnectedComponent := {
    toFun:=Subtype.val
    invFun:=fun j => ⟨j,hactive j⟩
    left_inv:=fun _ => rfl
    right_inv:=fun _ => rfl }
  have hb:=clique_separator_capacity hB hs z hz
  change Fintype.card (Gluing.ActiveBranch x.2)≤ cliqueCapacity B.card at hb
  rw [Fintype.card_congr e] at hb
  simpa only [Nat.card_eq_fintype_card] using hb

/-- Corollary5.3 for the literal normalized graphical cone and genuine
polytope dimension, including all connected components after deletion. -/
theorem full_dimension_triangle_separator_bound (hn : 2≤ n) (T : Finset (Fin n))
    (hT : T.card=3) (hc : G.IsClique T) (z : graphicalFunctionSpace G)
    (hz : ExtremeSupermodular z.1) (hd : FullDimension (basePolytope z.1)) :
    Nat.card ((outsideGraph G T).ConnectedComponent)≤3 := by
  have hb:=full_dimension_clique_separator_bound hn T hc (by omega) z hz hd
  simpa only [hT,cliqueCapacity_three] using hb

end Separator

open scoped Pointwise

/-- Ordinary compact-convex weak summands are converted to their actual
normalized lower-support function. No generalized-permutahedron presentation
or coefficient-support condition is added to the geometric hypothesis. -/
theorem SupportsFullIndecomposable.exists_extreme_function {n : ℕ} (hn : 2≤ n)
    {G : SimpleGraph (Fin n)} (h : SupportsFullIndecomposable G) :
    ∃ z : graphicalFunctionSpace G,ExtremeSupermodular z.1 ∧
      FullDimension (basePolytope z.1) := by
  obtain ⟨Q,hQ,hi,hd,a,ha,R,hR,hRc,hnR,hQR⟩:=h
  have hTn : Normalized (a • graphFunction G) := by
    change a*graphFunction G ∅=0
    rw [graphFunction_normalized,mul_zero]
  have hTs:=(graphFunction_supermodular G).smul ha.le
  have hbase : Q+R=basePolytope (a • graphFunction G) := by
    rw [basePolytope_smul (graphFunction_normalized G) (graphFunction_supermodular G) ha.le,
      baseGraphFunction_eq_graphicalZonotope]
    exact hQR
  let f:=lowerSupport Q
  have hfn : Normalized f:=lowerSupport_normalized hQ.compact hi.1
  have hfs : Supermodular f:=summand_lowerSupport_supermodular hTn hTs
    hQ.compact hR hi.1 hnR hbase
  have hbody : Q=basePolytope f:=summand_eq_basePolytope hTn hTs
    hQ.compact hR hQ.convex hi.1 hnR hbase
  have hgf : Graphical G f := by
    apply ((isMinkowskiSummand_graphical_iff hfn hfs ha.le).mp ?_).1
    rw [← hbody]
    exact ⟨R,hR,hRc,hnR,hQR⟩
  have hgn : Graphical G (normalize f) := by
    intro u v huv hnon A hu hv
    rw [delta_normalize f huv hu hv]
    exact hgf u v huv hnon A hu hv
  have hdim : Module.finrank ℝ (vectorSpan ℝ (basePolytope (normalize f)))=n-1 := by
    rw [vectorSpan_basePolytope_normalize,← hbody]
    simpa only [FullDimension,Fintype.card_fin] using hd
  have hne : normalize f≠0 := by
    intro he
    rw [he,basePolytope_zero] at hdim
    have hspan : vectorSpan ℝ ({0} : Set (Fin n → ℝ)) =
        (⊥ : Submodule ℝ (Fin n → ℝ)) :=
      _root_.vectorSpan_singleton ℝ (0 : Fin n → ℝ)
    rw [hspan, _root_.finrank_bot] at hdim
    omega
  refine ⟨⟨normalize f,normalize_translationNormalized hfn,hgn⟩,?_,?_⟩
  · apply MinkowskiIndecomposable.extremeSupermodular_normalize hfn hfs hne
    rwa [← hbody]
  · simpa only [FullDimension,Fintype.card_fin] using hdim

/-- The geometric form of Corollary5.3, with ordinary induced graph
deletion and no implicit active-branch hypothesis. -/
theorem SupportsFullIndecomposable.triangle_components_le_three {n : ℕ} (hn : 2≤ n)
    {G : SimpleGraph (Fin n)} (h : SupportsFullIndecomposable G)
    (T : Finset (Fin n)) (hT : T.card=3) (hc : G.IsClique T) :
    Nat.card ((G.induce ((T : Set (Fin n))ᶜ)).ConnectedComponent)≤3 := by
  obtain ⟨z,hz,hd⟩:=h.exists_extreme_function hn
  exact Separator.full_dimension_triangle_separator_bound hn T hT hc z hz hd

end GraphicalZonotopes

end
end
end BundlePart104

section BundlePart105
/- Source: Papers/GraphicalZonotopes/TreewidthDefinition.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A standard tree decomposition, with the usual vertex and edge coverage
and connected bag occurrence conditions. The width is maximum bag size minus
one. A natural-number index for the finite tree loses no finite decomposition. -/
def HasTreewidthAtMost (G : SimpleGraph V) (w : ℕ) : Prop :=
  ∃ m : ℕ, ∃ T : SimpleGraph (Fin m), ∃ bag : Fin m → Finset V,
    T.IsTree ∧ (∀ i, (bag i).card ≤ w+1) ∧
    (∀ v, ∃ i, v ∈ bag i) ∧
    (∀ u v, G.Adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i) ∧
    ∀ v, (T.induce {i | v ∈ bag i}).Connected


end GraphicalZonotopes

end
end
end BundlePart105

section BundlePart106
/- Source: Papers/GraphicalZonotopes/PathPropagation.lean -/






@[expose] public section

/-!
The arbitrary-length coefficient propagation in §3.2. This module proves the
complete displayed homogeneous system has exactly one scalar of freedom; it does
not by itself assert the polytope theorem before the slack/coordinate bridge.
-/
noncomputable section
namespace GraphicalZonotopes
namespace Path

@[ext] structure Coordinates (n : ℕ) where
  edge1 : Fin (n - 1) → ℝ
  edge2 : Fin (n - 2) → ℝ
  edge3 : Fin (n - 3) → ℝ
  tri012 : Fin (n - 2) → ℝ
  tri013 : Fin (n - 3) → ℝ
  tri023 : Fin (n - 3) → ℝ
  tetra : Fin (n - 3) → ℝ

def scale (n : ℕ) (a : ℝ) : Coordinates n where
  edge1 := fun _ => 0
  edge2 := fun _ => 0
  edge3 := fun _ => 0
  tri012 := fun _ => a
  tri013 := fun _ => 0
  tri023 := fun _ => a
  tetra := fun _ => -a

def Tight (n : ℕ) (y : Coordinates n) : Prop :=
  (∀ i, y.edge1 i = 0) ∧ (∀ i, y.edge2 i = 0) ∧ (∀ i, y.edge3 i = 0) ∧
  ∀ i : Fin (n - 3),
    y.edge3 i + y.tri013 i = 0 ∧
    y.edge1 ⟨i.val, by omega⟩ + y.tri012 ⟨i.val, by omega⟩ + y.tri013 i + y.tetra i = 0 ∧
    y.edge2 ⟨i.val + 1, by omega⟩ + y.tri013 i + y.tri012 ⟨i.val + 1, by omega⟩ + y.tetra i = 0 ∧
    y.edge3 i + y.tri013 i + y.tri023 i + y.tetra i = 0

theorem scale_tight (n : ℕ) (a : ℝ) : Tight n (scale n a) := by
  refine ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, ?_⟩
  intro i
  simp [scale]

/-- The displayed zero equations in the paper have a one-dimensional solution
space for every allowed path size, including both endpoints. -/
theorem tight_eq_scale {n : ℕ} (hn : 4 ≤ n) {y : Coordinates n} (hy : Tight n y) :
    y = scale n (y.tri012 ⟨0, by omega⟩) := by
  let a := y.tri012 ⟨0, by omega⟩
  have hu : ∀ i, y.tri013 i = 0 := by
    intro i
    have h := (hy.2.2.2 i).1
    rw [hy.2.2.1 i] at h
    linarith
  have htstep : ∀ i : Fin (n - 3),
      y.tri012 ⟨i.val, by omega⟩ = y.tri012 ⟨i.val + 1, by omega⟩ := by
    intro i
    have h1 := (hy.2.2.2 i).2.1
    have h2 := (hy.2.2.2 i).2.2.1
    rw [hy.1, hu] at h1
    rw [hy.2.1, hu] at h2
    linarith
  have ht : ∀ i : Fin (n - 2), y.tri012 i = a := by
    have aux : ∀ k : ℕ, ∀ hk : k < n - 2, y.tri012 ⟨k, hk⟩ = a := by
      intro k
      induction k with
      | zero => intro hk; rfl
      | succ k ih =>
        intro hk
        have hkn : k < n - 3 := by omega
        have hp := htstep ⟨k, hkn⟩
        have hi := ih (by omega)
        exact hp.symm.trans hi
    intro i
    exact aux i.val i.isLt
  have hh : ∀ i, y.tetra i = -a := by
    intro i
    have h := (hy.2.2.2 i).2.1
    rw [hy.1, ht, hu] at h
    linarith
  have hv : ∀ i, y.tri023 i = a := by
    intro i
    have h := (hy.2.2.2 i).2.2.2
    rw [hy.2.2.1, hu, hh] at h
    linarith
  apply Coordinates.ext
  · funext i; exact hy.1 i
  · funext i; exact hy.2.1 i
  · funext i; exact hy.2.2.1 i
  · funext i; exact ht i
  · funext i; exact hu i
  · funext i; exact hv i
  · funext i; exact hh i

theorem tight_iff_exists_scale {n : ℕ} (hn : 4 ≤ n) (y : Coordinates n) :
    Tight n y ↔ ∃ a : ℝ, y = scale n a := by
  constructor
  · intro hy
    exact ⟨_, tight_eq_scale hn hy⟩
  · rintro ⟨a, rfl⟩
    exact scale_tight n a

theorem scale_injective {n : ℕ} (hn : 4 ≤ n) : Function.Injective (scale n) := by
  intro a b hab
  have h := congrArg (fun y => y.tri012 ⟨0, by omega⟩) hab
  exact h

end Path
end GraphicalZonotopes

end
end
end BundlePart106

section BundlePart107
/- Source: Papers/GraphicalZonotopes/PathSupport.lean -/






@[expose] public section

noncomputable section
namespace GraphicalZonotopes
namespace Path
open Finset
open scoped BigOperators

/-- The third power of the path on labels `0,...,n-1`. -/
def graph (n : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ u.val ≤ v.val + 3 ∧ v.val ≤ u.val + 3
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- A translated finite mask, intersected with the actual vertex set. Bounds
are imposed explicitly when full-size cliques are used. -/
def window (n i : ℕ) (T : Finset ℕ) : Finset (Fin n) :=
  univ.filter (fun v => i ≤ v.val ∧ v.val - i ∈ T)

@[simp] theorem mem_window (n i : ℕ) (T : Finset ℕ) (v : Fin n) :
    v ∈ window n i T ↔ i ≤ v.val ∧ v.val - i ∈ T := by simp [window]

def masks : Finset (Finset ℕ) :=
  {{0,1}, {0,2}, {0,3}, {0,1,2}, {0,1,3}, {0,2,3}, {0,1,2,3}}

/-- The seven nonsingleton subsets of a four-position window containing its
least position. The proof has no bound on the path length. -/
theorem mask_classification {T : Finset ℕ} (h0 : 0 ∈ T)
    (hT : T ⊆ {0,1,2,3}) (hc : 2 ≤ T.card) : T ∈ masks := by
  have hmem : ∀ k, k ∈ T → k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
    intro k hk
    simpa only [mem_insert, mem_singleton] using hT hk
  by_cases h1 : 1 ∈ T <;> by_cases h2 : 2 ∈ T <;> by_cases h3 : 3 ∈ T
  · have he : T = {0,1,2,3} := by
      ext k
      have hk := hmem k
      constructor
      · intro h
        rcases hk h with rfl | rfl | rfl | rfl <;> simp_all
      · intro h
        simp only [mem_insert,mem_singleton] at h
        aesop
    simp [he, masks]
  · have he : T = {0,1,2} := by
      ext k
      have hk := hmem k
      constructor
      · intro h
        rcases hk h with rfl | rfl | rfl | rfl <;> simp_all
      · intro h
        simp only [mem_insert,mem_singleton] at h
        aesop
    simp [he, masks]
  · have he : T = {0,1,3} := by
      ext k
      have hk := hmem k
      constructor
      · intro h
        rcases hk h with rfl | rfl | rfl | rfl <;> simp_all
      · intro h
        simp only [mem_insert,mem_singleton] at h
        aesop
    simp [he, masks]
  · have he : T = {0,1} := by
      ext k
      have hk := hmem k
      constructor
      · intro h
        rcases hk h with rfl | rfl | rfl | rfl <;> simp_all
      · intro h
        simp only [mem_insert,mem_singleton] at h
        aesop
    simp [he, masks]
  · have he : T = {0,2,3} := by
      ext k
      have hk := hmem k
      constructor
      · intro h
        rcases hk h with rfl | rfl | rfl | rfl <;> simp_all
      · intro h
        simp only [mem_insert,mem_singleton] at h
        aesop
    simp [he, masks]
  · have he : T = {0,2} := by
      ext k
      have hk := hmem k
      constructor
      · intro h
        rcases hk h with rfl | rfl | rfl | rfl <;> simp_all
      · intro h
        simp only [mem_insert,mem_singleton] at h
        aesop
    simp [he, masks]
  · have he : T = {0,3} := by
      ext k
      have hk := hmem k
      constructor
      · intro h
        rcases hk h with rfl | rfl | rfl | rfl <;> simp_all
      · intro h
        simp only [mem_insert,mem_singleton] at h
        aesop
    simp [he, masks]
  · have he : T = {0} := by
      ext k
      have hk := hmem k
      constructor
      · intro h
        rcases hk h with rfl | rfl | rfl | rfl <;> simp_all
      · intro h
        simp only [mem_insert,mem_singleton] at h
        aesop
    simp [he] at hc

theorem window_card {n i : ℕ} (T : Finset ℕ)
    (hbound : ∀ k ∈ T, i + k < n) : (window n i T).card = T.card := by
  apply card_bij (fun v hv => v.val - i)
  · intro v hv
    exact ((mem_window n i T v).mp hv).2
  · intro v hv w hw he
    have hv' := ((mem_window n i T v).mp hv).1
    have hw' := ((mem_window n i T w).mp hw).1
    apply Fin.ext
    omega
  · intro k hk
    refine ⟨⟨i+k, hbound k hk⟩, ?_, ?_⟩
    · simp [window, hk]
    · simp

/-- Every nonsingleton clique is exactly one of the seven listed local patterns,
with every mask coordinate inside the true finite vertex set. -/
theorem clique_window_classification {n : ℕ} {C : Finset (Fin n)}
    (hc : 2 ≤ C.card)
    (hcl : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → (graph n).Adj u v) :
    ∃ i T, T ∈ masks ∧ (∀ k ∈ T, i + k < n) ∧ C = window n i T := by
  have hne : C.Nonempty := card_pos.mp (by omega)
  let a := C.min' hne
  let i := a.val
  let T := C.image (fun v => v.val - i)
  have ha : a ∈ C := min'_mem C hne
  have hleast : ∀ v ∈ C, i ≤ v.val := by
    intro v hv
    exact min'_le C v hv
  have hupper : ∀ v ∈ C, v.val ≤ i + 3 := by
    intro v hv
    by_cases hva : v = a
    · subst v; omega
    · exact (hcl a ha v hv (Ne.symm hva)).2.2
  have h0 : 0 ∈ T := by
    exact mem_image.mpr ⟨a, ha, by simp [i]⟩
  have hT : T ⊆ {0,1,2,3} := by
    intro k hk
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hk
    have h1 := hleast v hv
    have h2 := hupper v hv
    simp only [mem_insert, mem_singleton]
    omega
  have hinj : Set.InjOn (fun v : Fin n => v.val - i) C := by
    intro v hv w hw he
    change v.val-i=w.val-i at he
    have h1 := hleast v hv
    have h2 := hleast w hw
    apply Fin.ext
    omega
  have hcard : 2 ≤ T.card := by
    rw [show T = C.image (fun v => v.val - i) from rfl, card_image_iff.mpr hinj]
    exact hc
  refine ⟨i, T, mask_classification h0 hT hcard, ?_, ?_⟩
  · intro k hk
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hk
    have h := hleast v hv
    omega
  · ext v
    rw [mem_window]
    constructor
    · intro hv
      exact ⟨hleast v hv, mem_image.mpr ⟨v, hv, rfl⟩⟩
    · rintro ⟨hv, hk⟩
      obtain ⟨w, hw, he⟩ := mem_image.mp hk
      have hw' := hleast w hw
      change w.val-i=v.val-i at he
      have hwe : w = v := Fin.ext (by omega)
      simpa [hwe] using hw

/-- Reading all coefficients, including the zero ones, in the paper's coordinates. -/
def coordinates {n : ℕ} (y : SetFunction (Fin n)) : Coordinates n where
  edge1 := fun i => y (window n i.val {0,1})
  edge2 := fun i => y (window n i.val {0,2})
  edge3 := fun i => y (window n i.val {0,3})
  tri012 := fun i => y (window n i.val {0,1,2})
  tri013 := fun i => y (window n i.val {0,1,3})
  tri023 := fun i => y (window n i.val {0,2,3})
  tetra := fun i => y (window n i.val {0,1,2,3})

/-- The seven coordinate families determine every normalized clique-supported
coefficient: there is no omitted independent coefficient. -/
theorem coordinates_injective_on_supported {n : ℕ} {y y' : SetFunction (Fin n)}
    (hy : CliqueSupported (graph n) y) (hy' : CliqueSupported (graph n) y')
    (he : coordinates y = coordinates y') : y = y' := by
  funext C
  by_cases hc : 2 ≤ C.card
  · by_cases hcl : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → (graph n).Adj u v
    · obtain ⟨i, T, hT, hbound, rfl⟩ := clique_window_classification hc hcl
      simp only [masks, mem_insert, mem_singleton] at hT
      rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · have hi : i < n - 1 := by have h := hbound 1 (by simp); omega
        exact congrFun (congrArg Coordinates.edge1 he) ⟨i, hi⟩
      · have hi : i < n - 2 := by have h := hbound 2 (by simp); omega
        exact congrFun (congrArg Coordinates.edge2 he) ⟨i, hi⟩
      · have hi : i < n - 3 := by have h := hbound 3 (by simp); omega
        exact congrFun (congrArg Coordinates.edge3 he) ⟨i, hi⟩
      · have hi : i < n - 2 := by have h := hbound 2 (by simp); omega
        exact congrFun (congrArg Coordinates.tri012 he) ⟨i, hi⟩
      · have hi : i < n - 3 := by have h := hbound 3 (by simp); omega
        exact congrFun (congrArg Coordinates.tri013 he) ⟨i, hi⟩
      · have hi : i < n - 3 := by have h := hbound 3 (by simp); omega
        exact congrFun (congrArg Coordinates.tri023 he) ⟨i, hi⟩
      · have hi : i < n - 3 := by have h := hbound 3 (by simp); omega
        exact congrFun (congrArg Coordinates.tetra he) ⟨i, hi⟩
    · push_neg at hcl
      obtain ⟨u, hu, v, hv, huv, hnon⟩ := hcl
      rw [hy.2.2 C u v hu hv huv hnon, hy'.2.2 C u v hu hv huv hnon]
  · have hc' : C.card ≤ 1 := by omega
    obtain hC | hC := Nat.le_one_iff_eq_zero_or_eq_one.mp hc'
    · have heC : C = ∅ := card_eq_zero.mp hC
      rw [heC, hy.1, hy'.1]
    · obtain ⟨v, rfl⟩ := card_eq_one.mp hC
      rw [hy.2.1 v, hy'.2.1 v]

end Path
end GraphicalZonotopes

end
end
end BundlePart107

section BundlePart108
/- Source: Papers/GraphicalZonotopes/SmallPartTarget.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Targets
open Finset
open scoped BigOperators Pointwise
attribute [local instance] Classical.propDecidable

/-- The graph-specific statement of Corollary9.11, for all sixteen part-size
patterns. Its additional all-dimensions consequence also uses9.8 and9.10. -/
def FourSmallPartsDecomposition : Prop :=
  ∀ a : Fin 4 → ℕ, (∀ i, a i = 1 ∨ a i = 2) →
    ∃ Q R : Set ((Σ i : Fin 4, Fin (a i)) → ℝ),
      LatticePolytope Q ∧ LatticePolytope R ∧
      MinkowskiIndecomposable Q ∧ MinkowskiIndecomposable R ∧
      FullDimension Q ∧ FullDimension R ∧ Q+R = graphicalZonotope (fourPartite a) ∧
      actualDirectionGraph Q = fourPartite a ∧ actualDirectionGraph R = fourPartite a ∧
      BooleanElemental Q ∧ BooleanElemental R

end Targets
end GraphicalZonotopes

end
end
end BundlePart108

section BundlePart109
/- Source: Papers/GraphicalZonotopes/PrincipalTargets.lean -/







@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Targets
open Finset
open scoped BigOperators Pointwise
attribute [local instance] Classical.propDecidable

/-!
These are explicit proposition-valued targets for the principal results beyond
Theorem 3.1. They are NOT axioms and their presence does not assert their truth.
No theorem is exported merely by defining its intended statement. The final
audit must match each of these targets to a separately kernel-checked proof.
-/

/-- Theorem 4.1. In particular there is no clique-number restriction. -/
def DirectionBounds : Prop :=
  ∀ n : ℕ, 4 ≤ n → ∀ Q : Set (Fin n → ℝ),
    IsGeneralizedPermutahedron Q → MinkowskiIndecomposable Q → FullDimension Q →
    3*n-6 ≤ directionCount Q ∧ min (n-1) 6 ≤ maximumDirectionDegree Q ∧
    (directionCount Q = 3*n-6 → IsThreeTree (actualDirectionGraph Q))

/-- The equivalence and the complete quantitative construction in Theorem6.1.
All tetrahedra of a 3-tree are maximal cliques. -/
def ThreeTreeClassification : Prop :=
  ∀ n : ℕ, 4 ≤ n → ∀ G : SimpleGraph (Fin n), IsThreeTree G →
    (SupportsFullIndecomposable G ↔ Admissible G) ∧
    (Admissible G ↔ ∀ T : Finset (Fin n), T.card = 3 → G.IsClique T →
      Nat.card ((G.induce ((T : Set (Fin n))ᶜ)).ConnectedComponent) ≤ 3) ∧
    (Admissible G → ∃ z : SetFunction (Fin n), ExtremeSupermodular z ∧
      IntegerValued (mobius z) ∧
      (∀ C ∈ tetrahedra G, mobius z C = 1) ∧
      (∀ T : Finset (Fin n), T.card = 3 → G.IsClique T →
        mobius z T = 0 ∨ mobius z T = -1 ∨ mobius z T = -2) ∧
      FullDimension (basePolytope z) ∧ actualDirectionGraph (basePolytope z) = G ∧
      IsMinkowskiSummand (basePolytope z) (((n-3 : ℕ) : ℝ) • graphicalZonotope G))

/-- Theorem7.1, including attainment in the stated lattice dilation. -/
def CliqueBookClassification : Prop :=
  ∀ s k : ℕ, 2 ≤ s → 1 ≤ k →
    maximumIndecomposableDimension (cliqueBook s k) =
      min (s+k-1) (s+cliqueCapacity s-1) ∧
    (SupportsFullIndecomposable (cliqueBook s k) ↔ k ≤ cliqueCapacity s) ∧
    ∃ Q : Set ((Fin s ⊕ Fin k) → ℝ), LatticePolytope Q ∧
      MinkowskiIndecomposable Q ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = min (s+k-1) (s+cliqueCapacity s-1) ∧
      IsMinkowskiSummand Q ((((s-1)*min k (cliqueCapacity s) : ℕ) : ℝ) •
        graphicalZonotope (cliqueBook s k))

/-- Theorem7.12. The quantified lower bound and the lattice equality witness
are stated together, so the word "minimum" conceals no attainment premise. -/
def SaturatedBookDirections : Prop :=
  ∀ s : ℕ, 2 ≤ s →
    (∀ Q : Set ((Fin s ⊕ Fin (cliqueCapacity s)) → ℝ),
      IsFinitePolytope Q → MinkowskiIndecomposable Q → FullDimension Q →
      IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s (cliqueCapacity s))) →
      s.choose 2+s*saturatedHubNeighbors s ≤ directionCount Q ∧
      (3 ≤ s → ∀ i j : Fin s, i ≠ j →
        ActualRootEdge Q (Sum.inl i) (Sum.inl j)) ∧
      ∀ i : Fin s, saturatedHubNeighbors s ≤
        (univ.filter (fun j : Fin (cliqueCapacity s) =>
          ActualRootEdge Q (Sum.inl i) (Sum.inr j))).card) ∧
    ∃ Q : Set ((Fin s ⊕ Fin (cliqueCapacity s)) → ℝ),
      LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s (cliqueCapacity s))) ∧
      directionCount Q = s.choose 2+s*saturatedHubNeighbors s ∧
      ∀ i : Fin s, (univ.filter (fun j : Fin (cliqueCapacity s) =>
        ActualRootEdge Q (Sum.inl i) (Sum.inr j))).card = saturatedHubNeighbors s

/-- Theorem8.1, including its extremal six-branch witness. -/
def DiamondBookClassification : Prop :=
  (∀ k : ℕ, 1 ≤ k →
    maximumIndecomposableDimension (twoSingletonGraph 2 k) = min (k+3) 9) ∧
  ∃ Q : Set ((Σ i : Fin 4, Fin (![1,1,2,6] i)) → ℝ),
    LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧ FullDimension Q ∧
    IsMinkowskiSummand Q ((4 : ℝ) • graphicalZonotope (twoSingletonGraph 2 6)) ∧
    directionCount Q = 25 ∧
    ¬HasAdmissibleSpanningThreeTree (twoSingletonGraph 2 6)

/-- Theorem8.2. "Treewidth four" means width at most four and not at most
three, with the standard tree-decomposition definition above. -/
def SparseTreewidthFourFamily : Prop :=
  ∀ n : ℕ, 10 ≤ n → ∃ G : SimpleGraph (Fin n),
    G.CliqueFree 5 ∧ (edgeFamily G).card = 3*n-5 ∧
    HasTreewidthAtMost G 4 ∧ ¬HasTreewidthAtMost G 3 ∧
    EdgeMinimalSupporting G ∧ FullLatticeSummandAt G (n-6 : ℕ)

/-- Theorem8.7, together with lattice attainment of the exact dimension. -/
def TwoSingletonClassification : Prop :=
  ∀ p b : ℕ, 1 ≤ p → 1 ≤ b →
    maximumIndecomposableDimension (twoSingletonGraph p b) =
      min (p+b+1) (2^(min p b)+2*min p b+1) ∧
    (SupportsFullIndecomposable (twoSingletonGraph p b) ↔
      max p b ≤ 2^(min p b)+min p b) ∧
    ∃ Q : Set ((Σ i : Fin 4, Fin (![1,1,p,b] i)) → ℝ),
      LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (twoSingletonGraph p b)) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = min (p+b+1) (2^(min p b)+2*min p b+1)

/-- Theorem8.9. The second invariant explicitly restricts the actual
direction support to a 3-tree on its active vertices. -/
def FourPartiteSpanningThreeTrees : Prop :=
  ∀ a : Fin 4 → ℕ, (∀ i, 1 ≤ a i) →
    (HasAdmissibleSpanningThreeTree (fourPartite a) ↔
      3*(univ.sup a) ≤ 2*(∑ i, a i)-3) ∧
    maximumThreeTreeSupportDimension (fourPartite a) =
      min ((∑ i, a i)-1) (3*((∑ i, a i)-univ.sup a)-4)

/-- Theorem9.1, including every nonzero integral tetrahedral coefficient and
the complete edgewise integer-ceiling lower bound. -/
def ThreeTreeLatticeDilation : Prop :=
  (∀ n : ℕ, 6 ≤ n → ∀ G : SimpleGraph (Fin n), IsThreeTree G →
    ∀ Q : Set (Fin n → ℝ), LatticePolytope Q → MinkowskiIndecomposable Q →
      FullDimension Q → ∀ a : ℝ, 0 < a →
      IsMinkowskiSummand Q (a • graphicalZonotope G) →
      2 ≤ a ∧
      (∀ C ∈ tetrahedra G, ∃ k : ℤ, k ≠ 0 ∧ mobius (lowerSupport Q) C = k) ∧
      ∀ e ∈ edgeFamily G,
        ((Int.ceil ((1/2 : ℝ) *
          ∑ C ∈ (tetrahedra G).filter (fun C => e ⊆ C),
            |mobius (lowerSupport Q) C|)) : ℝ) ≤ a) ∧
  ∀ n : ℕ, 6 ≤ n → FullLatticeSummandAt (Path.graph n) 2

/-- Theorem9.5, with the ambient graph conclusion and all actual directions. -/
def UnitLatticeClassification : Prop :=
  ∀ n : ℕ, 4 ≤ n → ∀ G : SimpleGraph (Fin n), G.CliqueFree 5 →
    ∀ Q : Set (Fin n → ℝ), LatticePolytope Q → MinkowskiIndecomposable Q →
      FullDimension Q → IsMinkowskiSummand Q (graphicalZonotope G) →
      actualDirectionGraph Q = G ∧ n ≤ 8 ∧
      ∃ a : Fin 4 → ℕ, (∀ i, a i = 1 ∨ a i = 2) ∧ Nonempty (G ≃g fourPartite a)

/-- Theorem9.8, including both indecomposabilities, all dimensions, all
directions, Boolean slacks and the parity-dependent symmetry conclusions. -/
def DoubledPartsBooleanPhases : Prop :=
  ∀ r : ℕ, 4 ≤ r → ∃ Q R : Set ((Fin r × Fin 2) → ℝ),
    LatticePolytope Q ∧ LatticePolytope R ∧
    MinkowskiIndecomposable Q ∧ MinkowskiIndecomposable R ∧
    FullDimension Q ∧ FullDimension R ∧
    Q+R = graphicalZonotope (doubledPartGraph r) ∧
    actualDirectionGraph Q = doubledPartGraph r ∧
    actualDirectionGraph R = doubledPartGraph r ∧
    BooleanElemental Q ∧ BooleanElemental R ∧
    (Even r → CentrallySymmetricUpToTranslation Q ∧ CentrallySymmetricUpToTranslation R) ∧
    (Odd r → ∃ t, R = ({t} : Set ((Fin r × Fin 2) → ℝ)) + (-1 : ℝ) • Q) ∧
    (Odd r → graphicalZonotope (doubledPartGraph r) =
      Q+(-1 : ℝ) • Q+({fun _ : Fin r × Fin 2 => ((r-1 : ℕ) : ℝ)} : Set ((Fin r × Fin 2) → ℝ)))

/-- Corollary9.12, expressed as both attainment and a universal lower bound
over every K5-free graph on exactly n vertices. -/
def OptimalK5FreeDilation : Prop :=
  ∀ n : ℕ, 4 ≤ n →
    (∃ G : SimpleGraph (Fin n), G.CliqueFree 5 ∧
      FullLatticeSummandAt G (if n ≤ 8 then 1 else 2)) ∧
    ∀ G : SimpleGraph (Fin n), G.CliqueFree 5 → ∀ a : ℝ,
      0 < a → FullLatticeSummandAt G a → (if n ≤ 8 then 1 else 2) ≤ a

end Targets
end GraphicalZonotopes

end
end
end BundlePart109

section BundlePart110
/- Source: Papers/GraphicalZonotopes/ThreeTreeClassification.lean -/







@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise

/-- The sufficiency direction is about ordinary real polytopes and actual
Minkowski sums. The coefficient construction supplies the genuine witness. -/
theorem admissible_threeTree_supports {n : ℕ} (hn : 4≤ n)
    {G : SimpleGraph (Fin n)} (hG : IsThreeTree G) (hA : Admissible G) :
    SupportsFullIndecomposable G := by
  obtain ⟨z,hz,hy,hC,hT,hd,hgraph,hsum⟩:=admissible_threeTree_construction hn hG hA
  refine ⟨basePolytope z,?_,hz.minkowskiIndecomposable,hd,
    ((n-3 : ℕ) : ℝ),?_,hsum⟩
  · exact (show IsGeneralizedPermutahedron (basePolytope z) from
      ⟨z,hz.1.1,hz.2.1,rfl⟩).finitePolytope
  · exact_mod_cast (show 0< n-3 by omega)

theorem threeTree_supports_iff_admissible {n : ℕ} (hn : 4≤ n)
    {G : SimpleGraph (Fin n)} (hG : IsThreeTree G) :
    SupportsFullIndecomposable G ↔ Admissible G := by
  constructor
  · intro hs
    exact hG.admissible_iff_triangle_deletion.mpr
      (fun T ht hc => hs.triangle_components_le_three (by omega) T ht hc)
  · exact admissible_threeTree_supports hn hG

/-- The complete equivalence and quantitative conclusion of Theorem6.1,
with its exact global parameter range and no selected-branch hypothesis. -/
theorem threeTree_classification : Targets.ThreeTreeClassification := by
  intro n hn G hG
  exact ⟨threeTree_supports_iff_admissible hn hG,
    hG.admissible_iff_triangle_deletion,
    admissible_threeTree_construction hn hG⟩

/-- The literal finite family of maximal K4's containing a triangle is the
family used by `triangleMultiplicity`; this checks condition(ii) of the
paper against the coefficient indexing convention. -/
theorem maximal_tetrahedra_containing_eq {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : IsThreeTree G) (T : Finset V) :
    (univ.filter (fun C : Finset V => C.card=4 ∧
      Maximal G.IsClique (C : Set V) ∧ T⊆C))=
      (tetrahedra G).filter (fun C => T⊆C) := by
  classical
  ext C
  simp only [mem_filter,mem_univ,true_and,hG.maximalClique_iff C]
  constructor
  · exact fun h => ⟨h.2.1,h.2.2⟩
  · intro h
    exact ⟨(mem_filter.mp h.1).2.1,h.1,h.2⟩

/-- A statement with the paper's literal maximal-clique count, as well as
the actual induced-deletion component count. -/
theorem threeTree_classification_literal {n : ℕ} (hn : 4≤ n)
    {G : SimpleGraph (Fin n)} (hG : IsThreeTree G) :
    (SupportsFullIndecomposable G ↔
      ∀ T : Finset (Fin n),T.card=3 → G.IsClique T →
        (univ.filter (fun C : Finset (Fin n) => C.card=4 ∧
          Maximal G.IsClique (C : Set (Fin n)) ∧ T⊆C)).card≤3) ∧
    (SupportsFullIndecomposable G ↔
      ∀ T : Finset (Fin n),T.card=3 → G.IsClique T →
        Nat.card (G.induce ((T : Set (Fin n))ᶜ)).ConnectedComponent≤3) := by
  have he : (∀ T : Finset (Fin n),T.card=3 → G.IsClique T →
      (univ.filter (fun C : Finset (Fin n) => C.card=4 ∧
        Maximal G.IsClique (C : Set (Fin n)) ∧ T⊆C)).card≤3) ↔ Admissible G := by
    simp only [maximal_tetrahedra_containing_eq hG,Admissible,triangleMultiplicity]
  exact ⟨(threeTree_supports_iff_admissible hn hG).trans he.symm,
    (threeTree_supports_iff_admissible hn hG).trans hG.admissible_iff_triangle_deletion⟩

/-- The same constructed ray has an actual lattice-polytope representative,
with every ordinary maximal-clique coefficient equal to one. -/
theorem admissible_threeTree_lattice_witness {n : ℕ} (hn : 4≤ n)
    {G : SimpleGraph (Fin n)} (hG : IsThreeTree G) (hA : Admissible G) :
    ∃ z : SetFunction (Fin n),ExtremeSupermodular z ∧ IntegerValued (mobius z) ∧
      LatticePolytope (basePolytope z) ∧ MinkowskiIndecomposable (basePolytope z) ∧
      FullDimension (basePolytope z) ∧ actualDirectionGraph (basePolytope z)=G ∧
      (∀ C : Finset (Fin n),Maximal G.IsClique (C : Set (Fin n)) → mobius z C=1) ∧
      (∀ T : Finset (Fin n),T.card=3 → G.IsClique T →
        mobius z T=0 ∨ mobius z T= -1 ∨ mobius z T= -2) ∧
      IsMinkowskiSummand (basePolytope z) (((n-3 : ℕ) : ℝ) • graphicalZonotope G) := by
  obtain ⟨z,hz,hy,hC,hT,hd,hgraph,hsum⟩:=admissible_threeTree_construction hn hG hA
  have hi : IntegerValued z := by
    rw [← zeta_mobius z]
    exact zeta_integerValued hy
  exact ⟨z,hz,hy,hi.basePolytope hz.1.1 hz.2.1,hz.minkowskiIndecomposable,
    hd,hgraph,fun C hc => hC C ((hG.maximalClique_iff C).mp hc),hT,hsum⟩

end GraphicalZonotopes

end
end
end BundlePart110

section BundlePart111
/- Source: Papers/GraphicalZonotopes/TetrahedralCardinality.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A nonempty triangle-connected family of four-element sets covers at most
three more vertices than it has members. The finite maximal-family argument
counts the actual selected sets, rather than a larger ambient clique family. -/
theorem connected_tetrahedra_union_card (F : Finset (Finset V))
    (hne : F.Nonempty) (hfour : ∀ C∈F,C.card=4)
    (hconn : (tetrahedronGraph F).Preconnected) :
    (F.biUnion id).card≤ F.card+3 := by
  classical
  obtain ⟨C₀,hC₀⟩ := hne
  let candidates : Finset (Finset (Finset V)) := univ.filter
    (fun A => C₀∈A ∧ A⊆F ∧ (A.biUnion id).card≤ A.card+3)
  have hbase : {C₀}∈candidates := by
    apply mem_filter.mpr
    refine ⟨mem_univ _,by simp,?_,?_⟩
    · exact singleton_subset_iff.mpr hC₀
    · simp [hfour C₀ hC₀]
  obtain ⟨A,hA,hmax⟩ := candidates.exists_max_image Finset.card ⟨{C₀},hbase⟩
  obtain ⟨hC₀A,hAF,hcard⟩ := (mem_filter.mp hA).2
  have hclosed : ∀ C∈A,∀ D∈F,3≤(C∩D).card → D∈A := by
    intro C hC D hD hover
    by_contra hnot
    have hinter : 3≤(D∩A.biUnion id).card := by
      refine hover.trans (card_le_card ?_)
      intro v hv
      exact mem_inter.mpr ⟨(mem_inter.mp hv).2,
        mem_biUnion.mpr ⟨C,hC,(mem_inter.mp hv).1⟩⟩
    have hsum := card_union_add_card_inter D (A.biUnion id)
    have hDfour := hfour D hD
    have hcand : insert D A∈candidates := by
      apply mem_filter.mpr
      refine ⟨mem_univ _,mem_insert_of_mem hC₀A,insert_subset hD hAF,?_⟩
      rw [biUnion_insert,card_insert_of_notMem hnot]
      dsimp only [id_eq]
      omega
    have hmax' := hmax (insert D A) hcand
    rw [card_insert_of_notMem hnot] at hmax'
    omega
  have hall : ∀ C : {C : Finset V // C∈F},C.1∈A := by
    intro C
    have hp := (SimpleGraph.reachable_iff_reflTransGen
      (G:=tetrahedronGraph F) ⟨C₀,hC₀⟩ C).mp (hconn _ _)
    induction hp with
    | refl => exact hC₀A
    | @tail D E hp hDE ih => exact hclosed D.1 ih E.1 E.2 hDE.2
  have hFA : F⊆A := fun C hC => hall ⟨C,hC⟩
  have he : A=F := subset_antisymm hAF hFA
  simpa only [he] using hcard

end GraphicalZonotopes

end
end
end BundlePart111

section BundlePart112
/- Source: Papers/GraphicalZonotopes/ThreeTreeNonzero.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open RefinedTriangleComponents

/-- Lemma9.2 in coefficient form, with the ambient graph allowed to be any
3-tree containing the actual directions. Full dimension and indecomposability
force every one of its tetrahedral coefficients to be nonzero. -/
theorem threeTree_all_tetrahedra_nonzero {n : ℕ} (hn : 4≤ n)
    {G : SimpleGraph (Fin n)} (hG : IsThreeTree G)
    {z : SetFunction (Fin n)} (hz : ExtremeSupermodular z)
    (hgraph : Graphical G z)
    (hfull : Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=n-1) :
    family (mobius z)=tetrahedra G ∧
      ∀ C∈tetrahedra G,mobius z C≠0 := by
  classical
  obtain ⟨hne,hconn,hcover,hactual⟩ :=
    full_refined_support hn hG.cliqueFree_five hz hgraph hfull
  have hy : CliqueSupported G (mobius z) :=
    (mobius_cliqueSupported_iff G z).mpr ⟨hz.1,hgraph⟩
  have hsub : family (mobius z)⊆tetrahedra G := by
    intro C hC
    obtain ⟨hfour,hnonzero⟩ := (mem_family (mobius z) C).mp hC
    apply mem_filter.mpr
    refine ⟨mem_univ _,hfour,?_⟩
    intro u hu v hv huv
    by_contra hnot
    exact hnonzero (hy.2.2 C u v hu hv huv hnot)
  have hbound := connected_tetrahedra_union_card (family (mobius z)) hne
    (fun C hC => ((mem_family (mobius z) C).mp hC).1) hconn
  rw [hcover,card_univ,Fintype.card_fin] at hbound
  have hcount : (tetrahedra G).card=n-3 := by
    simpa only [card_univ,Fintype.card_fin] using hG.tetrahedra_card
  have he : family (mobius z)=tetrahedra G :=
    eq_of_subset_of_card_le hsub (by omega)
  refine ⟨he,?_⟩
  intro C hC
  exact ((mem_family (mobius z) C).mp (he.symm ▸ hC)).2

end GraphicalZonotopes

end
end
end BundlePart112

section BundlePart113
/- Source: Papers/GraphicalZonotopes/MobiusFour.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem zeta_insert (y : SetFunction V) {a : V} {S : Finset V} (ha : a∉S) :
    zeta y (insert a S)=zeta y S+zeta (fun T => y (insert a T)) S := by
  classical
  have hd : Disjoint S.powerset (S.powerset.image (insert a)) := by
    apply disjoint_left.mpr
    intro T hT hi
    obtain ⟨U,hU,rfl⟩ := mem_image.mp hi
    exact ha ((mem_powerset.mp hT) (mem_insert_self _ _))
  have hi : Set.InjOn (insert a) (S.powerset : Set (Finset V)) := by
    intro T hT U hU he
    have haT : a∉T := notMem_mono (mem_powerset.mp hT) ha
    have haU : a∉U := notMem_mono (mem_powerset.mp hU) ha
    have h := congrArg (fun A : Finset V => A.erase a) he
    simpa [haT,haU] using h
  simp only [zeta,powerset_insert]
  rw [sum_union hd,sum_image hi]

/-- The original fourth Möbius coefficient is the complete second difference
of an elemental row on the other two vertices. -/
theorem mobius_four_eq (f : SetFunction V) {a b c d : V}
    (hab : a≠ b) (hac : a≠ c) (had : a≠ d)
    (hbc : b≠ c) (hbd : b≠ d) (hcd : c≠ d) :
    mobius f {a,b,c,d}=
      delta f a b {c,d}-delta f a b {c}-delta f a b {d}+delta f a b ∅ := by
  have h (y : SetFunction V) : y {a,b,c,d}=
      delta (zeta y) a b {c,d}-delta (zeta y) a b {c}-
      delta (zeta y) a b {d}+delta (zeta y) a b ∅ := by
    simp [delta,zeta_insert,hab,hac,had,hbc,hbd,hcd,zeta_empty,zeta_singleton]
    <;> ring
  simpa only [zeta_mobius] using h (mobius f)

/-- Expanded normalized form, convenient for exact lattice certificates. -/
theorem mobius_four_normalized (f : SetFunction V) (hn : TranslationNormalized f)
    {a b c d : V} (hab : a≠ b) (hac : a≠ c) (had : a≠ d)
    (hbc : b≠ c) (hbd : b≠ d) (hcd : c≠ d) :
    mobius f {a,b,c,d}=
      f {a,b,c,d}-f {a,b,c}-f {a,b,d}-f {a,c,d}-f {b,c,d}+
        f {a,b}+f {a,c}+f {a,d}+f {b,c}+f {b,d}+f {c,d} := by
  rw [mobius_four_eq f hab hac had hbc hbd hcd]
  have h0 : f ∅ = 0 := hn.1
  simp only [delta,insert_empty_eq,h0,hn.2]
  ring

end GraphicalZonotopes

end
end
end BundlePart113

section BundlePart114
/- Source: Papers/GraphicalZonotopes/LatticeCoefficients.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Möbius inversion preserves the full integer lattice of set functions.
The proof uses the triangular inverse equations over all subsets, without a
rationality or denominator assumption on the inverse linear equivalence. -/
theorem IntegerValued.mobius {z : SetFunction V} (hz : IntegerValued z) :
    IntegerValued (GraphicalZonotopes.mobius z) := by
  classical
  intro S
  refine Finset.strongInductionOn S ?_
  intro S ih
  let k : Finset V → ℤ := fun C =>
    if h : C⊂S then Classical.choose (ih C h) else 0
  have hk : ∀ C∈S.powerset.erase S,(k C : ℝ)=GraphicalZonotopes.mobius z C := by
    intro C hC
    have hp : C⊂S := Finset.ssubset_iff_subset_ne.mpr
      ⟨mem_powerset.mp (mem_of_mem_erase hC),ne_of_mem_erase hC⟩
    simpa only [k,dif_pos hp] using (Classical.choose_spec (ih C hp)).symm
  obtain ⟨a,ha⟩ := hz S
  have he := congrFun (zeta_mobius z) S
  change ∑ C∈S.powerset,GraphicalZonotopes.mobius z C=z S at he
  rw [← sum_erase_add _ _ (mem_powerset.mpr Subset.rfl),ha] at he
  refine ⟨a-∑ C∈S.powerset.erase S,k C,?_⟩
  push_cast
  have hs : (∑ C∈S.powerset.erase S,(k C : ℝ))=
      ∑ C∈S.powerset.erase S,GraphicalZonotopes.mobius z C := sum_congr rfl hk
  rw [hs]
  linarith

/-- All tetrahedral coefficients are invariant under an arbitrary real
translation, not merely an integer translation. -/
theorem mobius_four_normalize {z : SetFunction V} {C : Finset V}
    (hC : C.card=4) : mobius (normalize z) C=GraphicalZonotopes.mobius z C := by
  obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,rfl⟩ := card_eq_four.mp hC
  rw [mobius_four_eq _ hab hac had hbc hbd hcd,
    mobius_four_eq _ hab hac had hbc hbd hcd,
    delta_normalize z hab (by simp [hac,had]) (by simp [hbc,hbd]),
    delta_normalize z hab (by simp [hac]) (by simp [hbc]),
    delta_normalize z hab (by simp [had]) (by simp [hbd]),
    delta_normalize z hab (by simp) (by simp)]

end GraphicalZonotopes

end
end
end BundlePart114

section BundlePart115
/- Source: Papers/GraphicalZonotopes/ThreeTreeLatticeCoefficients.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A genuine compact convex summand yields the full lower-support data and
all fixed-dilation inequalities, with no assumed generalized-permutahedron
presentation of the summand. -/
theorem actual_summand_lowerSupport {Q R : Set (V → ℝ)} {G : SimpleGraph V}
    (hQ : IsCompact Q) (hcQ : Convex ℝ Q) (hnQ : Q.Nonempty)
    (hR : IsCompact R) (hcR : Convex ℝ R) (hnR : R.Nonempty)
    {a : ℝ} (ha : 0≤ a) (he : Q+R=a • graphicalZonotope G) :
    Normalized (lowerSupport Q) ∧ Supermodular (lowerSupport Q) ∧
      Q=basePolytope (lowerSupport Q) ∧ Graphical G (lowerSupport Q) ∧
      ∀ u v,u≠ v → G.Adj u v → ∀ S,u∉S → v∉S →
        delta (lowerSupport Q) u v S≤ a := by
  have hTn : Normalized (a • graphFunction G) := by
    change a*graphFunction G ∅=0
    rw [graphFunction_normalized,mul_zero]
  have hTs := (graphFunction_supermodular G).smul ha
  have hbase : Q+R=basePolytope (a • graphFunction G) := by
    rw [basePolytope_smul (graphFunction_normalized G) (graphFunction_supermodular G) ha,
      baseGraphFunction_eq_graphicalZonotope]
    exact he
  have hn := lowerSupport_normalized hQ hnQ
  have hs := summand_lowerSupport_supermodular hTn hTs hQ hR hnQ hnR hbase
  have hbody := summand_eq_basePolytope hTn hTs hQ hR hcQ hnQ hnR hbase
  have hsum : IsMinkowskiSummand (basePolytope (lowerSupport Q))
      (a • graphicalZonotope G) := by
    rw [← hbody]
    exact ⟨R,hR,hcR,hnR,he⟩
  have hrows := (isMinkowskiSummand_graphical_iff hn hs ha).mp hsum
  exact ⟨hn,hs,hbody,hrows⟩

/-- The nonzero integer-coefficient assertion in Theorem9.1, for arbitrary
actual lattice summands and every tetrahedron of the given 3-tree. This is an
intermediate theorem; the sharp edgewise dilation bound is a further obligation. -/
theorem threeTree_lattice_four_coefficients {n : ℕ} (hn : 4≤ n)
    {G : SimpleGraph (Fin n)} (hG : IsThreeTree G)
    {Q : Set (Fin n → ℝ)} (hQ : LatticePolytope Q)
    (hi : MinkowskiIndecomposable Q) (hd : FullDimension Q)
    {a : ℝ} (ha : 0< a) (hsum : IsMinkowskiSummand Q (a • graphicalZonotope G)) :
    ∀ C∈tetrahedra G,∃ k : ℤ,k≠0 ∧ mobius (lowerSupport Q) C=k := by
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  obtain ⟨hfn,hfs,hbody,hgraph,hbound⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hi.1 hR hcR hnR ha.le he
  let f:=lowerSupport Q
  have hdim : Module.finrank ℝ (vectorSpan ℝ (basePolytope (normalize f)))=n-1 := by
    rw [vectorSpan_basePolytope_normalize,← hbody]
    simpa only [FullDimension,Fintype.card_fin] using hd
  have hne : normalize f≠0 := by
    intro he
    rw [he,basePolytope_zero] at hdim
    have hspan : vectorSpan ℝ ({0} : Set (Fin n → ℝ)) =
        (⊥ : Submodule ℝ (Fin n → ℝ)) :=
      _root_.vectorSpan_singleton ℝ (0 : Fin n → ℝ)
    rw [hspan, _root_.finrank_bot] at hdim
    omega
  have hext : ExtremeSupermodular (normalize f) := by
    apply MinkowskiIndecomposable.extremeSupermodular_normalize hfn hfs hne
    rwa [← hbody]
  have hnormgraph : Graphical G (normalize f) := by
    intro u v huv hnon S hu hv
    rw [delta_normalize f huv hu hv]
    exact hgraph u v huv hnon S hu hv
  have hall := (threeTree_all_tetrahedra_nonzero hn hG hext hnormgraph hdim).2
  have hint := (hQ.lowerSupport_integerValued hi.1).mobius
  intro C hC
  obtain ⟨k,hk⟩ := hint C
  refine ⟨k,?_,hk⟩
  intro hzero
  have hc : C.card=4 := (mem_filter.mp hC).2.1
  have hnonzero := hall C hC
  rw [mobius_four_normalize hc] at hnonzero
  exact hnonzero (by simpa [hzero] using hk)

end GraphicalZonotopes

end
end
end BundlePart115

section BundlePart116
/- Source: Papers/GraphicalZonotopes/ThreeTreeActiveGeometry.lean -/








@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators Pointwise

namespace GraphicalZonotopes
open Finset SetFunctionEmbedding RefinedTriangleComponents
variable {V : Type*} [Fintype V] [LinearOrder V]

theorem ActualRootEdge.root_mem_vectorSpan {Q : Set (V → ℝ)} {u v : V}
    (h : ActualRootEdge Q u v) : basisVector u-basisVector v∈vectorSpan ℝ Q := by
  obtain ⟨huv,p,q,⟨hpq,l,a,hl,hface⟩,c,hc,hdir⟩ := h
  have hp : p∈Q := by
    have hm := left_mem_segment ℝ p q
    rw [← hface] at hm
    exact hm.1
  have hq : q∈Q := by
    have hm := right_mem_segment ℝ p q
    rw [← hface] at hm
    exact hm.1
  have hv : q-p∈vectorSpan ℝ Q := vsub_mem_vectorSpan ℝ hq hp
  rw [hdir] at hv
  have hh := (vectorSpan ℝ Q).smul_mem c⁻¹ hv
  simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using hh

theorem actualGraph_graphical {f : SetFunction V}
    (hn : Normalized f) (hs : Supermodular f) :
    Graphical (actualDirectionGraph (basePolytope f)) f := by
  intro u v huv hnon S hu hv
  by_contra hd
  exact hnon ((actualRootEdge_iff_nonzero_delta hn hs u v).mpr ⟨huv,S,hu,hv,hd⟩)

theorem threeTree_actual_nonzero {S : Finset V} {f : SetFunction V}
    (hn : Normalized f) (hs : Supermodular f)
    (h : ThreeTreeOn S (actualDirectionGraph (basePolytope f))) : f≠0 := by
  intro he
  obtain ⟨u,v,huv⟩ := h.exists_edge
  obtain ⟨_,T,_,_,hd⟩ := (actualRootEdge_iff_nonzero_delta hn hs u v).mp huv
  exact hd (by simp [he,delta])

theorem isThreeTree_comap_equiv {W : Type*} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} (h : IsThreeTree G) (e : W ≃ V) :
    IsThreeTree (G.comap e.toEmbedding) := by
  have hh := h.comap e.toEmbedding (fun v _ => ⟨e.symm v,e.apply_symm_apply v⟩)
  change ThreeTreeOn univ _
  simpa only [pullSet_univ] using hh

/-- The checked full-dimensional 3-tree theorem transfers to every finite
vertex type by an actual coordinate equivalence. -/
theorem admissible_of_extreme_full {G : SimpleGraph V} (hG : IsThreeTree G)
    {f : SetFunction V} (hf : ExtremeSupermodular f) (hd : FullDimension (basePolytope f))
    (hg : Graphical G f) : Admissible G := by
  let e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  have htree : IsThreeTree (G.comap e.toEmbedding) := isThreeTree_comap_equiv hG e
  have hn : 4≤ Fintype.card V := by
    simpa only [card_univ] using hG.active_card_ge_four
  have hrange : ∀ u v,G.Adj u v → u∈Set.range e.toEmbedding :=
    fun u _ _ => ⟨e.symm u,e.apply_symm_apply u⟩
  have hrec := reconstruct_of_graphical_supported e.toEmbedding hf.1 hg hrange
  let g := restrict e.toEmbedding f
  have hgext : ExtremeSupermodular g := extreme_restrict_of_reconstruction e.toEmbedding hf hrec
  have hdim : FullDimension (basePolytope g) := by
    have he := finrank_vectorSpan_extend e.toEmbedding (restrict_translationNormalized e.toEmbedding hf.1)
    rw [hrec] at he
    change Module.finrank ℝ (vectorSpan ℝ (basePolytope f))=Fintype.card V-1 at hd
    change Module.finrank ℝ (vectorSpan ℝ (basePolytope g))=Fintype.card (Fin (Fintype.card V))-1
    rw [Fintype.card_fin]
    exact he.symm.trans hd
  have hggraph : Graphical (G.comap e.toEmbedding) g := restrict_graphical e.toEmbedding hg
  have hsupport : SupportsFullIndecomposable (G.comap e.toEmbedding) :=
    ⟨basePolytope g,
      (show IsGeneralizedPermutahedron (basePolytope g) from ⟨g,hgext.1.1,hgext.2.1,rfl⟩).finitePolytope,
      hgext.minkowskiIndecomposable,hdim,
      (isWeakMinkowskiSummand_graphical_iff hgext.1.1 hgext.2.1).mpr hggraph⟩
  have hA := ((threeTree_supports_iff_admissible hn htree).mp hsupport).map e.toEmbedding
  rwa [map_comap_of_supported e.toEmbedding G hrange] at hA

/-- Admissible 3-trees on arbitrary finite coordinate types have integral
extreme witnesses with the exact actual direction graph and full dimension. -/
theorem admissible_threeTree_witness_fintype {G : SimpleGraph V}
    (hG : IsThreeTree G) (hA : Admissible G) :
    ∃ f : SetFunction V,ExtremeSupermodular f ∧ IntegerValued f ∧
      FullDimension (basePolytope f) ∧ actualDirectionGraph (basePolytope f)=G ∧ Graphical G f := by
  let e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  have htree := isThreeTree_comap_equiv hG e
  have hn : 4≤ Fintype.card V := by simpa only [card_univ] using hG.active_card_ge_four
  have hAfin : Admissible (G.comap e.toEmbedding) := by
    have hh := hA.map e.symm.toEmbedding
    rwa [SimpleGraph.map_symm] at hh
  obtain ⟨g,hg,hint,_,_,hd,hactual,_⟩ := admissible_threeTree_construction hn htree hAfin
  have hgi : IntegerValued g := by
    rw [← zeta_mobius g]
    exact zeta_integerValued hint
  have hgg : Graphical (G.comap e.toEmbedding) g := by
    have hh := actualGraph_graphical hg.1.1 hg.2.1
    rwa [hactual] at hh
  have hrange : ∀ u v,G.Adj u v → u∈Set.range e.toEmbedding :=
    fun u _ _ => ⟨e.symm u,e.apply_symm_apply u⟩
  refine ⟨extend e.toEmbedding g,extend_extreme e.toEmbedding hg,extend_integer e.toEmbedding hgi,
    ?_,?_,extend_graphical e.toEmbedding hgg⟩
  · unfold FullDimension at hd ⊢
    rw [finrank_vectorSpan_extend e.toEmbedding hg.1]
    simpa only [Fintype.card_fin] using hd
  · rw [actualDirectionGraph_extend e.toEmbedding hg.1 hg.2.1,hactual,
      map_comap_of_supported e.toEmbedding G hrange]

/-- The active support is proved full-dimensional. Admissibility is then
deduced by applying the genuine full-dimensional theorem on that support. -/
theorem threeTree_actual_dimension_admissible {S : Finset V} {f : SetFunction V}
    (hf : ExtremeSupermodular f)
    (h : ThreeTreeOn S (actualDirectionGraph (basePolytope f))) :
    Module.finrank ℝ (vectorSpan ℝ (basePolytope f))=S.card-1 ∧
      Admissible (actualDirectionGraph (basePolytope f)) := by
  letI : DecidableEq S := (inferInstance : LinearOrder S).toDecidableEq
  let G := actualDirectionGraph (basePolytope f)
  let e : S ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have hrange : ∀ u v,G.Adj u v → u∈Set.range e :=
    fun u v huv => ⟨⟨u,(h.edges_supported huv).1⟩,rfl⟩
  have hrec := reconstruct_of_graphical_supported e hf.1
    (actualGraph_graphical hf.1.1 hf.2.1) hrange
  let g := restrict e f
  have hg : ExtremeSupermodular g := extreme_restrict_of_reconstruction e hf hrec
  have hactual : actualDirectionGraph (basePolytope g)=G.comap e :=
    actualDirectionGraph_restrict e hf.1 hf.2.1 hrec
  have htree : IsThreeTree (actualDirectionGraph (basePolytope g)) := by
    rw [hactual]
    exact h.induce
  have hdim : FullDimension (basePolytope g) :=
    finrank_vectorSpan_eq_of_connected_roots (basePolytope_nonempty hg.1.1 hg.2.1)
      htree.connected (fun u v he =>
        ActualRootEdge.root_mem_vectorSpan (show ActualRootEdge (basePolytope g) u v from he))
  have hAr := admissible_of_extreme_full htree hg hdim
    (actualGraph_graphical hg.1.1 hg.2.1)
  have hA := hAr.map e
  rw [hactual,map_comap_of_supported e G hrange] at hA
  refine ⟨?_,hA⟩
  have he := finrank_vectorSpan_extend e hg.1
  rw [hrec] at he
  have hd : Module.finrank ℝ (vectorSpan ℝ (basePolytope g))=S.card-1 := by
    simpa only [FullDimension,Fintype.card_coe] using hdim
  exact he.trans hd

/-- The converse on an arbitrary active subset, preserving the literal
ambient graph and leaving every outside coordinate zero. -/
theorem admissible_threeTree_active_witness {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (hA : Admissible G) :
    ∃ f : SetFunction V,ExtremeSupermodular f ∧ IntegerValued f ∧
      Module.finrank ℝ (vectorSpan ℝ (basePolytope f))=S.card-1 ∧
      actualDirectionGraph (basePolytope f)=G ∧ Graphical G f := by
  letI : DecidableEq S := (inferInstance : LinearOrder S).toDecidableEq
  let e : S ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have hrange : ∀ u v,G.Adj u v → u∈Set.range e :=
    fun u v huv => ⟨⟨u,(h.edges_supported huv).1⟩,rfl⟩
  have hmap := map_comap_of_supported e G hrange
  have hAr : Admissible (G.comap e) := Admissible.of_map e (by rwa [hmap])
  have htr : IsThreeTree (G.comap e) := h.induce
  obtain ⟨g,hg,hgi,hd,hactual,hgraph⟩ :=
    admissible_threeTree_witness_fintype (V := S) htr hAr
  refine ⟨extend e g,extend_extreme e hg,extend_integer e hgi,?_,?_,extend_graphical e hgraph⟩
  · rw [finrank_vectorSpan_extend e hg.1]
    simpa only [FullDimension,Fintype.card_coe] using hd
  · rw [actualDirectionGraph_extend e hg.1 hg.2.1,hactual,hmap]

end GraphicalZonotopes

end
end
end BundlePart116

section BundlePart117
/- Source: Papers/GraphicalZonotopes/PolytopalWeakSummands.lean -/




/-! # Ordinary polytopal formulations of graphical weak summands

The compact convex complementary summand is automatically a finite polytope.
The indecomposability equivalence then allows the main statements to use
precisely the paper's quantification over polytopal Minkowski decompositions.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem LatticePolytope.finitePolytope {Q : Set (V → ℝ)} (hQ : LatticePolytope Q) :
    IsFinitePolytope Q := by
  classical
  obtain ⟨P,hP⟩ := hQ
  refine ⟨P.image (fun x : V → ℤ => fun v => (x v : ℝ)),?_⟩
  simpa only [Finset.coe_image] using hP.symm

/-- Every actual compact convex complement of a finite graphical-zonotope
summand is itself a finite polytope. Nonemptiness of the first summand is
derived from the sum equality, rather than imposed as an extra hypothesis. -/
theorem finite_complement_of_graphical_sum
    {G : SimpleGraph V} {Q R : Set (V → ℝ)}
    (hQ : IsFinitePolytope Q) (hR : IsCompact R) (hcR : Convex ℝ R)
    (hnR : R.Nonempty) {a : ℝ} (ha : 0 ≤ a)
    (he : Q + R = a • graphicalZonotope G) :
    Q.Nonempty ∧ IsFinitePolytope R := by
  have hzn : Normalized (a • graphFunction G) := by
    change a * graphFunction G ∅ = 0
    rw [graphFunction_normalized,mul_zero]
  have hzs : Supermodular (a • graphFunction G) :=
    (graphFunction_supermodular G).smul ha
  have hsum : Q + R = basePolytope (a • graphFunction G) := by
    rw [basePolytope_smul (graphFunction_normalized G)
      (graphFunction_supermodular G) ha,baseGraphFunction_eq_graphicalZonotope]
    exact he
  obtain ⟨x,hx⟩ := basePolytope_nonempty hzn hzs
  rw [← hsum] at hx
  obtain ⟨q,hq,r,hr,hqr⟩ := hx
  have hnQ : Q.Nonempty := ⟨q,hq⟩
  have hsumR : R + Q = basePolytope (a • graphFunction G) := by
    rw [add_comm]
    exact hsum
  have hsm := summand_lowerSupport_supermodular hzn hzs hR hQ.compact hnR hnQ hsumR
  have hbody := summand_eq_basePolytope hzn hzs hR hQ.compact hcR hnR hnQ hsumR
  have hgp : IsGeneralizedPermutahedron R :=
    ⟨lowerSupport R,lowerSupport_normalized hR hnR,hsm,hbody⟩
  exact ⟨hnQ,hgp.finitePolytope⟩

/-- The fixed-dilation summand predicate is equivalent to the ordinary
finite-polytope complement formulation, including at dilation zero. -/
theorem isMinkowskiSummand_graphical_iff_finite_complement
    {G : SimpleGraph V} {Q : Set (V → ℝ)}
    (hQ : IsFinitePolytope Q) {a : ℝ} (ha : 0 ≤ a) :
    IsMinkowskiSummand Q (a • graphicalZonotope G) ↔
      ∃ R : Set (V → ℝ),IsFinitePolytope R ∧ R.Nonempty ∧
        Q + R = a • graphicalZonotope G := by
  constructor
  · rintro ⟨R,hR,hcR,hnR,he⟩
    exact ⟨R,(finite_complement_of_graphical_sum hQ hR hcR hnR ha he).2,hnR,he⟩
  · rintro ⟨R,hR,hnR,he⟩
    exact ⟨R,hR.compact,hR.convex,hnR,he⟩

/-- A genuine weak summand of a graphical zonotope has a positive
dilation with a finite polytope as its complementary summand. -/
theorem isWeakMinkowskiSummand_graphical_iff_finite_complement
    {G : SimpleGraph V} {Q : Set (V → ℝ)} (hQ : IsFinitePolytope Q) :
    IsWeakMinkowskiSummand Q (graphicalZonotope G) ↔
      ∃ a : ℝ,0 < a ∧ ∃ R : Set (V → ℝ),IsFinitePolytope R ∧ R.Nonempty ∧
        Q + R = a • graphicalZonotope G := by
  constructor
  · rintro ⟨a,ha,h⟩
    exact ⟨a,ha,(isMinkowskiSummand_graphical_iff_finite_complement hQ ha.le).mp h⟩
  · rintro ⟨a,ha,h⟩
    exact ⟨a,ha,(isMinkowskiSummand_graphical_iff_finite_complement hQ ha.le).mpr h⟩

theorem weakSummand_indecomposable_iff_polytopal
    {G : SimpleGraph V} {Q : Set (V → ℝ)}
    (hQ : IsFinitePolytope Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    MinkowskiIndecomposable Q ↔ PolytopalMinkowskiIndecomposable Q := by
  constructor
  · intro hi
    exact ⟨hi.1,fun P R hP hR he =>
      hi.2 P R hP.compact hR.compact hP.convex hR.convex he⟩
  · intro hi
    obtain ⟨a,ha,R,hR,hcR,hnR,he⟩ := hw
    have hzn : Normalized (a • graphFunction G) := by
      change a * graphFunction G ∅ = 0
      rw [graphFunction_normalized,mul_zero]
    have hzs : Supermodular (a • graphFunction G) :=
      (graphFunction_supermodular G).smul ha.le
    have hsum : Q + R = basePolytope (a • graphFunction G) := by
      rw [basePolytope_smul (graphFunction_normalized G)
        (graphFunction_supermodular G) ha.le,baseGraphFunction_eq_graphicalZonotope]
      exact he
    have hn := lowerSupport_normalized hQ.compact hi.1
    have hsm := summand_lowerSupport_supermodular hzn hzs hQ.compact hR hi.1 hnR hsum
    have hbody := summand_eq_basePolytope hzn hzs hQ.compact hR hQ.convex hi.1 hnR hsum
    exact (minkowskiIndecomposable_iff_polytopal
      ⟨lowerSupport Q,hn,hsm,hbody⟩).mpr hi

end GraphicalZonotopes

end
end
end BundlePart117

section BundlePart118
/- Source: Papers/GraphicalZonotopes/HamiltonianThreeTree.lean -/







/-! # Hamiltonian 3-trees

Corollary 6.9's Hamiltonian assertion follows from literal vertex deletion:
a Hamiltonian cycle yields at most three components after deleting any
triangle. The exact 3-tree deletion theorem then gives admissibility, and
the constructive classification produces an integral extreme witness.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset

theorem IsThreeTree.admissible_of_hamiltonian
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : IsThreeTree G) (hH : G.IsHamiltonian) : Admissible G := by
  apply hG.admissible_iff_triangle_deletion.mpr
  intro S hS hcl
  have hn : 2 ≤ Fintype.card V := by
    have h := hG.active_card_ge_four
    simp only [card_univ] at h
    omega
  have hne : S.Nonempty := card_pos.mp (by omega)
  simpa only [hS] using
    HamiltonianDeletion.hamiltonian_component_card_delete_le G hH hn S hne

/-- Corollary 6.9's Hamiltonian conclusion on every finite vertex type.
The coordinate order is chosen internally. The witness is an actual lattice
polytope, has full affine dimension and the exact graph as its edge-direction
graph, and is indecomposable for ordinary finite polytopal decompositions. -/
theorem hamiltonian_threeTree_lattice_polytopal_finite
    {V : Type*} [Fintype V] :
    letI : LinearOrder V :=
      LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective;
    ∀ (G : SimpleGraph V), IsThreeTree G → G.IsHamiltonian →
      ∃ Q : Set (V → ℝ), LatticePolytope Q ∧
        PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
        actualDirectionGraph Q = G := by
  letI : LinearOrder V :=
    LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  intro G hG hH
  obtain ⟨f,hf,hint,hd,ha,hgraph⟩ :=
    admissible_threeTree_witness_fintype hG (hG.admissible_of_hamiltonian hH)
  have hlat := hint.basePolytope hf.1.1 hf.2.1
  have hw : IsWeakMinkowskiSummand (basePolytope f) (graphicalZonotope G) :=
    (isWeakMinkowskiSummand_graphical_iff hf.1.1 hf.2.1).mpr hgraph
  exact ⟨basePolytope f,hlat,
    (weakSummand_indecomposable_iff_polytopal hlat.finitePolytope hw).mp
      hf.minkowskiIndecomposable,hd,hw,ha⟩

end GraphicalZonotopes

end
end
end BundlePart118

section BundlePart119
/- Source: Papers/GraphicalZonotopes/MonotoneBooleanKernel.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The hub function in Section7.1. Every value, including all otherwise
unused private coordinates, remains part of the function space. -/
structure IsMonotoneBoolean (F : SetFunction V) : Prop where
  monotone : Monotone F
  values : ∀ S,F S=0 ∨ F S=1
  empty : F ∅=0
  full : F univ=1

def ZeroCoverKernel (F g : SetFunction V) : Prop :=
  g ∅=0 ∧ ∀ a S,a∉S → F (insert a S)-F S=0 → g (insert a S)-g S=0

/-- If the monotone function is constant at the endpoints of an interval,
the zero-cover equations make a variation constant throughout that interval. -/
theorem flat_interval {F g : SetFunction V} (hF : Monotone F)
    (hg : ZeroCoverKernel F g) {A B : Finset V} (hAB : A⊆B) (he : F A=F B) :
    g A=g B := by
  have hvalue : ∀ C,A⊆C → C⊆B → F C=F A := by
    intro C hAC hCB
    exact le_antisymm (by rw [he]; exact hF hCB) (hF hAC)
  have hstep : ∀ D : Finset V,A∪D⊆B → g (A∪D)=g A := by
    intro D
    induction D using Finset.induction_on with
    | empty => simp
    | @insert b D hb ih =>
      intro hsub
      rw [union_insert] at hsub ⊢
      have hsubD : A∪D⊆B:=fun x hx => hsub (mem_insert_of_mem hx)
      by_cases hbD : b∈A∪D
      · simpa only [insert_eq_of_mem hbD] using ih hsubD
      · have hzero : F (insert b (A∪D))-F (A∪D)=0 := by
          rw [hvalue _ (subset_union_left.trans (subset_insert _ _)) hsub,
            hvalue _ subset_union_left hsubD,sub_self]
        have hflat:=sub_eq_zero.mp (hg.2 b (A∪D) hbD hzero)
        exact hflat.trans (ih hsubD)
  have hu : A∪(B\A)=B:=union_sdiff_of_subset hAB
  have hh:=hstep (B\A) (by rw [hu])
  rw [hu] at hh
  exact hh.symm

/-- The full private spoke kernel is a line. No coefficient support or
nonzero-coordinate premise is imposed on the arbitrary variation `g`. -/
theorem zero_cover_kernel_line {F g : SetFunction V}
    (hF : IsMonotoneBoolean F) (hg : ZeroCoverKernel F g) :
    g=(g univ) • F := by
  funext S
  change g S=g univ*F S
  rcases hF.values S with hzero | hone
  · have he : F ∅=F S:=hF.empty.trans hzero.symm
    have hh:=flat_interval hF.monotone hg (empty_subset S) he
    rw [hg.1] at hh
    rw [hzero,mul_zero]
    exact hh.symm
  · have he : F S=F univ:=hone.trans hF.full.symm
    have hh:=flat_interval hF.monotone hg (subset_univ S) he
    simpa only [hone,mul_one] using hh

def privateKernel (F : SetFunction V) : Submodule ℝ (SetFunction V) where
  carrier := {g | ZeroCoverKernel F g}
  zero_mem' := by simp [ZeroCoverKernel]
  add_mem' := by
    intro g h hg hh
    refine ⟨by simp only [Pi.add_apply,hg.1,hh.1,add_zero],?_⟩
    intro a S ha hz
    have h1:=hg.2 a S ha hz
    have h2:=hh.2 a S ha hz
    change (g (insert a S)+h (insert a S))-(g S+h S)=0
    linarith
  smul_mem' := by
    intro c g hg
    refine ⟨by simp only [Pi.smul_apply,smul_eq_mul,hg.1,mul_zero],?_⟩
    intro a S ha hz
    have he:=hg.2 a S ha hz
    change c*g (insert a S)-c*g S=0
    rw [← mul_sub,he,mul_zero]

theorem self_mem_privateKernel {F : SetFunction V} (hF : IsMonotoneBoolean F) :
    F∈privateKernel F := ⟨hF.empty,fun _ _ _ h => h⟩

theorem privateKernel_eq_span {F : SetFunction V} (hF : IsMonotoneBoolean F) :
    privateKernel F=Submodule.span ℝ {F} := by
  apply le_antisymm
  · intro g hg
    exact Submodule.mem_span_singleton.mpr ⟨g univ,(zero_cover_kernel_line hF hg).symm⟩
  · apply Submodule.span_le.mpr
    intro g hg
    have he : g=F:=Set.mem_singleton_iff.mp hg
    subst g
    exact self_mem_privateKernel hF

theorem IsMonotoneBoolean.ne_zero {F : SetFunction V} (hF : IsMonotoneBoolean F) : F≠0 := by
  intro he
  have hh:=hF.full
  rw [he] at hh
  norm_num at hh

theorem privateKernel_finrank {F : SetFunction V} (hF : IsMonotoneBoolean F) :
    Module.finrank ℝ (privateKernel F)=1 := by
  rw [privateKernel_eq_span hF]
  exact finrank_span_singleton hF.ne_zero

theorem cover_values {F : SetFunction V} (hF : IsMonotoneBoolean F)
    (a : V) (S : Finset V) : F (insert a S)-F S=0 ∨ F (insert a S)-F S=1 := by
  have hm:=hF.monotone (subset_insert a S)
  rcases hF.values S with h0 | h1 <;>
    rcases hF.values (insert a S) with hi0 | hi1 <;> simp_all <;> norm_num at *

theorem delta_values {F : SetFunction V} (hF : IsMonotoneBoolean F)
    (u v : V) (S : Finset V) :
    delta F u v S= -1 ∨ delta F u v S=0 ∨ delta F u v S=1 := by
  have h0:=hF.monotone (subset_insert u S)
  have h1:=hF.monotone (subset_insert v S)
  have h2:=hF.monotone (show insert u S⊆insert u (insert v S) from
    insert_subset_insert u (subset_insert v S))
  have h3:=hF.monotone (subset_insert u (insert v S))
  rcases hF.values S with hS | hS <;>
    rcases hF.values (insert u S) with hu | hu <;>
    rcases hF.values (insert v S) with hv | hv <;>
    rcases hF.values (insert u (insert v S)) with huv | huv <;>
    simp_all [delta] <;> norm_num at *

/-- The negative part of the literal central elemental response. -/
def negativeResponse (F : SetFunction V) (u v : V) (S : Finset V) : ℝ :=
  max 0 (-delta F u v S)

theorem negativeResponse_values {F : SetFunction V} (hF : IsMonotoneBoolean F)
    (u v : V) (S : Finset V) :
    negativeResponse F u v S=0 ∨ negativeResponse F u v S=1 := by
  rcases delta_values hF u v S with h | h | h <;>
    simp [negativeResponse,h]

theorem negativeResponse_eq_one_iff {F : SetFunction V} (hF : IsMonotoneBoolean F)
    (u v : V) (S : Finset V) :
    negativeResponse F u v S=1 ↔
      F S=0 ∧ F (insert u S)=1 ∧ F (insert v S)=1 := by
  have h0:=hF.monotone (subset_insert u S)
  have h1:=hF.monotone (subset_insert v S)
  have h2:=hF.monotone (show insert u S⊆insert u (insert v S) from
    insert_subset_insert u (subset_insert v S))
  have h3:=hF.monotone (subset_insert u (insert v S))
  rcases hF.values S with hS | hS <;>
    rcases hF.values (insert u S) with hu | hu <;>
    rcases hF.values (insert v S) with hv | hv <;>
    rcases hF.values (insert u (insert v S)) with huv | huv <;>
    simp_all [negativeResponse,delta] <;> norm_num at *

/-- Each summand in equation(7.1) is exactly a nonnegative zero-one literal
before multiplication by its positive branch scale. -/
theorem response_factor_values {F : SetFunction V} (hF : IsMonotoneBoolean F)
    (u v : V) (S : Finset V) (x : ℝ) (hx : x=0 ∨ x=1) :
    negativeResponse F u v S+x*delta F u v S=0 ∨
      negativeResponse F u v S+x*delta F u v S=1 := by
  rcases delta_values hF u v S with h | h | h <;>
    rcases hx with rfl | rfl <;> simp [negativeResponse,h]

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart119

section BundlePart120
/- Source: Papers/GraphicalZonotopes/BookBooleanFunctions.lean -/






@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise
variable {H J : Type*} [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]

theorem delta_swap (f : SetFunction (H⊕J)) (u v : H⊕J) (A : Finset (H⊕J)) :
    delta f u v A=delta f v u A := by
  unfold delta
  rw [insert_comm]
  ring

def hubs (A : Finset (H⊕J)) : Finset H:=univ.filter (fun a => Sum.inl a∈A)

@[simp] theorem mem_hubs (A : Finset (H⊕J)) (a : H) :
    a∈hubs A ↔ Sum.inl a∈A := by simp [hubs]

@[simp] theorem hubs_empty : hubs (∅ : Finset (H⊕J))=∅ := by ext a; simp

@[simp] theorem hubs_insert_hub (A : Finset (H⊕J)) (a : H) :
    hubs (insert (Sum.inl a) A)=insert a (hubs A) := by ext b; simp

@[simp] theorem hubs_insert_outer (A : Finset (H⊕J)) (j : J) :
    hubs (insert (Sum.inr j) A)=hubs A := by ext b; simp

def hubSet (A : Finset H) : Finset (H⊕J):=A.map ⟨Sum.inl,Sum.inl_injective⟩

@[simp] theorem mem_hubSet_hub (A : Finset H) (a : H) :
    Sum.inl a∈hubSet (J:=J) A ↔ a∈A := by simp [hubSet]

@[simp] theorem notMem_hubSet_outer (A : Finset H) (j : J) :
    Sum.inr j∉hubSet A := by simp [hubSet]

@[simp] theorem hubs_hubSet (A : Finset H) : hubs (hubSet (J:=J) A)=A := by ext a; simp

@[simp] theorem hubSet_insert (A : Finset H) (a : H) :
    hubSet (J:=J) (insert a A)=insert (Sum.inl a) (hubSet A) := by simp [hubSet]

@[simp] theorem hubSet_empty : hubSet (J:=J) (∅ : Finset H)=∅ := by simp [hubSet]

def boundaryLift (z : SetFunction H) : SetFunction (H⊕J):=fun A => z (hubs A)

def branchLift (j : J) (F : SetFunction H) : SetFunction (H⊕J):=
  fun A => if Sum.inr j∈A then F (hubs A) else 0

theorem boundaryLift_normalized {z : SetFunction H} (hz : TranslationNormalized z) :
    TranslationNormalized (boundaryLift (J:=J) z) := by
  refine ⟨?_,?_⟩
  · simpa only [Normalized,boundaryLift,hubs_empty] using hz.1
  · intro v
    cases v with
    | inl a => simpa only [boundaryLift,← insert_empty_eq,hubs_insert_hub,hubs_empty] using hz.2 a
    | inr j => simpa only [Normalized,boundaryLift,← insert_empty_eq,hubs_insert_outer,hubs_empty] using hz.1

theorem branchLift_normalized (j : J) {F : SetFunction H} (hF : F ∅=0) :
    TranslationNormalized (branchLift j F) := by
  constructor
  · simp [Normalized,branchLift]
  · intro v
    cases v <;> simp [branchLift,hubs,hF]

theorem delta_boundary_hubs (z : SetFunction H) (u v : H) (A : Finset (H⊕J)) :
    delta (boundaryLift z) (Sum.inl u) (Sum.inl v) A=delta z u v (hubs A) := by
  simp only [delta,boundaryLift,hubs_insert_hub]

theorem delta_boundary_spoke (z : SetFunction H) (u : H) (j : J) (A : Finset (H⊕J)) :
    delta (boundaryLift z) (Sum.inl u) (Sum.inr j) A=0 := by
  simp only [delta,boundaryLift,hubs_insert_hub,hubs_insert_outer]
  ring

theorem delta_boundary_outer (z : SetFunction H) (i j : J) (A : Finset (H⊕J)) :
    delta (boundaryLift z) (Sum.inr i) (Sum.inr j) A=0 := by
  simp only [delta,boundaryLift,hubs_insert_outer]
  ring

theorem delta_branch_hubs (j : J) (F : SetFunction H) (u v : H) (A : Finset (H⊕J)) :
    delta (branchLift j F) (Sum.inl u) (Sum.inl v) A=
      if Sum.inr j∈A then delta F u v (hubs A) else 0 := by
  by_cases hj : Sum.inr j∈A <;> simp [delta,branchLift,hj]

theorem delta_branch_spoke (i j : J) (F : SetFunction H) (u : H)
    (A : Finset (H⊕J)) (hj : Sum.inr j∉A) :
    delta (branchLift i F) (Sum.inl u) (Sum.inr j) A=
      if i=j then F (insert u (hubs A))-F (hubs A) else 0 := by
  by_cases hij : i=j
  · subst i
    simp [delta,branchLift,hj]
  · by_cases hi : Sum.inr i∈A <;> simp [delta,branchLift,hij,hi] <;> ring

theorem delta_branch_outer (k : J) (F : SetFunction H) (i j : J) (hij : i≠ j)
    (A : Finset (H⊕J)) (hi : Sum.inr i∉A) (hj : Sum.inr j∉A) :
    delta (branchLift k F) (Sum.inr i) (Sum.inr j) A=0 := by
  by_cases hki : k=i
  · subst k
    simp [delta,branchLift,hij,hi]
  · by_cases hkj : k=j
    · subst k
      simp [delta,branchLift,Ne.symm hij,hj]
    · by_cases hk : Sum.inr k∈A <;> simp [delta,branchLift,hki,hkj,hk] <;> ring

def assembled (z : SetFunction H) (F : J → SetFunction H) (w : J → ℝ) :
    SetFunction (H⊕J) := boundaryLift z+∑ j : J,w j • branchLift j (F j)

theorem assembled_normalized {z : SetFunction H} (hz : TranslationNormalized z)
    (F : J → SetFunction H) (hF : ∀ j,IsMonotoneBoolean (F j)) (w : J → ℝ) :
    TranslationNormalized (assembled z F w) := by
  have hb:=boundaryLift_normalized (J:=J) hz
  have hp:=fun j => branchLift_normalized j (hF j).empty
  constructor
  · change boundaryLift z ∅+(∑ j : J,w j • branchLift j (F j)) ∅=0
    rw [Finset.sum_apply,hb.1,zero_add]
    apply sum_eq_zero
    intro j hj
    change w j*branchLift j (F j) ∅=0
    rw [(hp j).1,mul_zero]
  · intro v
    change boundaryLift z {v}+(∑ j : J,w j • branchLift j (F j)) {v}=0
    rw [Finset.sum_apply,hb.2 v,zero_add]
    apply sum_eq_zero
    intro j hj
    change w j*branchLift j (F j) {v}=0
    rw [(hp j).2 v,mul_zero]

theorem delta_assembled_spoke (z : SetFunction H) (F : J → SetFunction H) (w : J → ℝ)
    (u : H) (j : J) (A : Finset (H⊕J)) (hj : Sum.inr j∉A) :
    delta (assembled z F w) (Sum.inl u) (Sum.inr j) A=
      w j*(F j (insert u (hubs A))-F j (hubs A)) := by
  classical
  rw [assembled,delta_add,delta_boundary_spoke,zero_add,delta_sum]
  simp_rw [delta_smul,delta_branch_spoke _ _ _ _ _ hj]
  simp

theorem delta_assembled_outer (z : SetFunction H) (F : J → SetFunction H) (w : J → ℝ)
    (i j : J) (hij : i≠ j) (A : Finset (H⊕J))
    (hi : Sum.inr i∉A) (hj : Sum.inr j∉A) :
    delta (assembled z F w) (Sum.inr i) (Sum.inr j) A=0 := by
  rw [assembled,delta_add,delta_boundary_outer,zero_add,delta_sum]
  apply sum_eq_zero
  intro k hk
  rw [delta_smul,delta_branch_outer _ _ _ _ hij _ hi hj,mul_zero]

theorem delta_assembled_hubs (z : SetFunction H) (F : J → SetFunction H) (w : J → ℝ)
    (u v : H) (A : Finset (H⊕J)) :
    delta (assembled z F w) (Sum.inl u) (Sum.inl v) A=
      delta z u v (hubs A)+∑ j : J,w j*(if Sum.inr j∈A then delta (F j) u v (hubs A) else 0) := by
  rw [assembled,delta_add,delta_boundary_hubs,delta_sum]
  simp_rw [delta_smul,delta_branch_hubs]

def Compatible (z : SetFunction H) (F : J → SetFunction H) (w : J → ℝ) : Prop :=
  ∀ u v,u≠ v → ∀ S,u∉S → v∉S →
    delta z u v S=∑ j : J,w j*negativeResponse (F j) u v S

/-- Equation(7.1) is a literal equality for the genuine global set function. -/
theorem assembled_factorization (z : SetFunction H) (F : J → SetFunction H)
    (w : J → ℝ) (hc : Compatible z F w) (u v : H) (huv : u≠ v)
    (A : Finset (H⊕J)) (hu : Sum.inl u∉A) (hv : Sum.inl v∉A) :
    delta (assembled z F w) (Sum.inl u) (Sum.inl v) A=
      ∑ j : J,w j*(negativeResponse (F j) u v (hubs A)+
        (if Sum.inr j∈A then 1 else 0)*delta (F j) u v (hubs A)) := by
  rw [delta_assembled_hubs,hc u v huv (hubs A) (by simpa using hu) (by simpa using hv),
    ← sum_add_distrib]
  apply sum_congr rfl
  intro j hj
  by_cases hja : Sum.inr j∈A <;> simp only [hja,ite_true,ite_false,one_mul,zero_mul] <;> ring

theorem assembled_supermodular (z : SetFunction H) (F : J → SetFunction H)
    (hF : ∀ j,IsMonotoneBoolean (F j)) (w : J → ℝ) (hw : ∀ j,0≤ w j)
    (hc : Compatible z F w) : Supermodular (assembled z F w) := by
  apply ElementallyNonnegative.supermodular
  intro a b hab A ha hb
  cases a with
  | inl u =>
    cases b with
    | inl v =>
      rw [assembled_factorization z F w hc u v (fun he => hab (congrArg Sum.inl he)) A ha hb]
      apply sum_nonneg
      intro j hj
      apply mul_nonneg (hw j)
      have hx : (if Sum.inr j∈A then (1 : ℝ) else 0)=0 ∨
          (if Sum.inr j∈A then (1 : ℝ) else 0)=1 := by split_ifs <;> simp
      rcases response_factor_values (hF j) u v (hubs A) _ hx with hval | hval <;> rw [hval] <;> norm_num
    | inr j =>
      rw [delta_assembled_spoke z F w u j A hb]
      exact mul_nonneg (hw j) (sub_nonneg.mpr ((hF j).monotone (subset_insert _ _)))
  | inr i =>
    cases b with
    | inl v =>
      rw [delta_swap,delta_assembled_spoke z F w v i A ha]
      exact mul_nonneg (hw i) (sub_nonneg.mpr ((hF i).monotone (subset_insert _ _)))
    | inr j =>
      rw [delta_assembled_outer z F w i j (fun he => hab (congrArg Sum.inr he)) A ha hb]

theorem assembled_graphical {s k : ℕ} (z : SetFunction (Fin s))
    (F : Fin k → SetFunction (Fin s)) (w : Fin k → ℝ) :
    Graphical (cliqueBook s k) (assembled z F w) := by
  intro a b hab hnon A ha hb
  cases a with
  | inl u => exact False.elim (hnon ⟨hab,Or.inl rfl⟩)
  | inr i =>
    cases b with
    | inl v => exact False.elim (hnon ⟨hab,Or.inr rfl⟩)
    | inr j =>
      exact delta_assembled_outer z F w i j
        (fun he => hab (congrArg Sum.inr he)) A ha hb

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart120

section BundlePart121
/- Source: Papers/GraphicalZonotopes/BookFunctionDecomposition.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise
variable {H J : Type*} [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]

def outers (A : Finset (H⊕J)) : Finset J:=univ.filter (fun j => Sum.inr j∈A)

@[simp] theorem mem_outers (A : Finset (H⊕J)) (j : J) :
    j∈outers A ↔ Sum.inr j∈A := by simp [outers]

def outerSet (Y : Finset J) : Finset (H⊕J):=Y.map ⟨Sum.inr,Sum.inr_injective⟩

@[simp] theorem mem_outerSet_outer (Y : Finset J) (j : J) :
    Sum.inr j∈outerSet (H:=H) Y ↔ j∈Y := by simp [outerSet]

@[simp] theorem notMem_outerSet_hub (Y : Finset J) (u : H) :
    Sum.inl u∉outerSet Y := by simp [outerSet]

@[simp] theorem outerSet_empty : outerSet (H:=H) (∅ : Finset J)=∅ := by simp [outerSet]

@[simp] theorem outerSet_insert (Y : Finset J) (j : J) :
    outerSet (H:=H) (insert j Y)=insert (Sum.inr j) (outerSet Y) := by simp [outerSet]

def context (X : Finset H) (Y : Finset J) : Finset (H⊕J):=hubSet X∪outerSet Y

@[simp] theorem mem_context_hub (X : Finset H) (Y : Finset J) (u : H) :
    Sum.inl u∈context X Y ↔ u∈X := by simp [context]

@[simp] theorem mem_context_outer (X : Finset H) (Y : Finset J) (j : J) :
    Sum.inr j∈context X Y ↔ j∈Y := by simp [context]

@[simp] theorem context_empty (X : Finset H) : context (J:=J) X ∅=hubSet X := by
  simp [context]

@[simp] theorem context_insert (X : Finset H) (Y : Finset J) (j : J) :
    context X (insert j Y)=insert (Sum.inr j) (context X Y) := by
  simp only [context,outerSet_insert,union_insert]

@[simp] theorem hubs_context (X : Finset H) (Y : Finset J) : hubs (context X Y)=X := by
  ext u
  simp

@[simp] theorem outers_context (X : Finset H) (Y : Finset J) : outers (context X Y)=Y := by
  ext j
  simp

theorem context_parts (A : Finset (H⊕J)) : context (hubs A) (outers A)=A := by
  ext v
  cases v <;> simp

def OuterZero (f : SetFunction (H⊕J)) : Prop :=
  ∀ i j,i≠ j → ∀ A,Sum.inr i∉A → Sum.inr j∉A →
    delta f (Sum.inr i) (Sum.inr j) A=0

def boundarySlice (f : SetFunction (H⊕J)) : SetFunction H:=fun X => f (hubSet X)

def privateSlice (f : SetFunction (H⊕J)) (j : J) : SetFunction H:=
  fun X => f (insert (Sum.inr j) (hubSet X))-f (hubSet X)

theorem outer_marginal_constant {f : SetFunction (H⊕J)} (hf : OuterZero f)
    (j : J) (X : Finset H) (Y : Finset J) (hj : j∉Y) :
    f (insert (Sum.inr j) (context X Y))-f (context X Y)=privateSlice f j X := by
  induction Y using Finset.induction_on with
  | empty => simp only [context_empty,privateSlice]
  | @insert i Y hi ih =>
    have hji : j≠ i:=fun he => hj (mem_insert.mpr (Or.inl he))
    have hjY : j∉Y:=fun hm => hj (mem_insert_of_mem hm)
    have hz:=hf j i hji (context X Y) (by simpa using hjY) (by simpa using hi)
    have hh:=ih hjY
    rw [context_insert]
    dsimp only [delta] at hz
    linarith

/-- Vanishing on all outer nonedges is exactly the required additive
decomposition into one actual hub function and one actual private slice per
outer vertex. This retains arbitrary real variations, not merely the chosen
Boolean functions. -/
theorem function_context_decomposition {f : SetFunction (H⊕J)} (hf : OuterZero f)
    (X : Finset H) (Y : Finset J) :
    f (context X Y)=boundarySlice f X+∑ j∈Y,privateSlice f j X := by
  induction Y using Finset.induction_on with
  | empty => simp [boundarySlice]
  | @insert j Y hj ih =>
    have hm:=outer_marginal_constant hf j X Y hj
    rw [context_insert,sum_insert hj]
    linarith

theorem function_decomposition {f : SetFunction (H⊕J)} (hf : OuterZero f)
    (A : Finset (H⊕J)) :
    f A=boundarySlice f (hubs A)+∑ j∈outers A,privateSlice f j (hubs A) := by
  simpa only [context_parts] using function_context_decomposition hf (hubs A) (outers A)

theorem boundarySlice_normalized {f : SetFunction (H⊕J)} (hf : TranslationNormalized f) :
    TranslationNormalized (boundarySlice f) := by
  constructor
  · simpa only [Normalized,boundarySlice,hubSet_empty] using hf.1
  · intro a
    simpa [boundarySlice,hubSet] using hf.2 (Sum.inl a)

theorem privateSlice_empty {f : SetFunction (H⊕J)} (hf : TranslationNormalized f) (j : J) :
    privateSlice f j ∅=0 := by
  have h0 : f ∅=0 := hf.1
  simp only [privateSlice,hubSet_empty,insert_empty_eq,h0,hf.2,sub_self]

theorem privateSlice_cover (f : SetFunction (H⊕J)) (j : J) (a : H) (X : Finset H) :
    privateSlice f j (insert a X)-privateSlice f j X=
      delta f (Sum.inl a) (Sum.inr j) (hubSet X) := by
  simp only [privateSlice,hubSet_insert,delta]
  rw [insert_comm (Sum.inr j) (Sum.inl a)]
  ring

theorem graphical_outerZero {s k : ℕ} {f : SetFunction (Fin s⊕Fin k)}
    (hf : Graphical (cliqueBook s k) f) : OuterZero f := by
  intro i j hij A hi hj
  exact hf (Sum.inr i) (Sum.inr j) (fun he => hij (Sum.inr_injective he))
    (by simp [cliqueBook]) A hi hj

/-- Once the actual private slices have specified scales, the original
function itself has that assembled form. -/
theorem eq_assembled_of_privateSlices {f : SetFunction (H⊕J)} (hf : OuterZero f)
    (F : J → SetFunction H) (w : J → ℝ)
    (hparts : ∀ j,privateSlice f j=w j • F j) :
    f=assembled (boundarySlice f) F w := by
  funext A
  rw [function_decomposition hf A]
  change boundarySlice f (hubs A)+(∑ j∈outers A,privateSlice f j (hubs A))=
    boundarySlice f (hubs A)+(∑ j : J,w j • branchLift j (F j)) A
  congr 1
  rw [Finset.sum_apply]
  unfold outers
  rw [sum_filter]
  apply sum_congr rfl
  intro j hj
  rw [hparts j]
  by_cases hja : Sum.inr j∈A <;> simp [branchLift,hja]

/-- Every private spoke kernel in Lemma7.3 is the full line promised by the
paper. The variation is any normalized set function with the actual spoke
zero equations; it is not assumed to have a particular coefficient support. -/
theorem privateSlice_scalar_of_spokeZeros {z : SetFunction H}
    {F : J → SetFunction H} (hF : ∀ j,IsMonotoneBoolean (F j)) {w : J → ℝ}
    {f : SetFunction (H⊕J)} (hf : TranslationNormalized f)
    (ht : ∀ u v,u≠ v → ∀ A,u∉A → v∉A →
      delta (assembled z F w) u v A=0 → delta f u v A=0) (j : J) :
    privateSlice f j=(privateSlice f j univ) • F j := by
  apply zero_cover_kernel_line (hF j)
  refine ⟨privateSlice_empty hf j,?_⟩
  intro a X ha hzero
  rw [privateSlice_cover]
  apply ht (Sum.inl a) (Sum.inr j) (by simp) (hubSet X)
    (by simpa using ha) (notMem_hubSet_outer X j)
  rw [delta_assembled_spoke _ _ _ _ _ _ (notMem_hubSet_outer X j),hubs_hubSet,hzero,mul_zero]

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart121

section BundlePart122
/- Source: Papers/GraphicalZonotopes/BookPositiveCircuit.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise
variable {H J : Type*} [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]

def minimizingOuters (F : J → SetFunction H) (u v : H) (X : Finset H) : Finset J:=
  univ.filter (fun j => delta (F j) u v X= -1)

@[simp] theorem mem_minimizingOuters (F : J → SetFunction H) (u v : H)
    (X : Finset H) (j : J) : j∈minimizingOuters F u v X ↔ delta (F j) u v X= -1 := by
  simp [minimizingOuters]

theorem minimizing_literal {F : SetFunction H} (hF : IsMonotoneBoolean F)
    (u v : H) (X : Finset H) :
    (if delta F u v X= -1 then delta F u v X else 0)= -negativeResponse F u v X := by
  rcases delta_values hF u v X with hd | hd | hd <;> norm_num [negativeResponse,hd]

theorem assembled_minimizer_zero {z : SetFunction H} {F : J → SetFunction H}
    (hF : ∀ j,IsMonotoneBoolean (F j)) {w : J → ℝ} (hc : Compatible z F w)
    (u v : H) (huv : u≠ v) (X : Finset H) (hu : u∉X) (hv : v∉X) :
    delta (assembled z F w) (Sum.inl u) (Sum.inl v)
      (context X (minimizingOuters F u v X))=0 := by
  rw [delta_assembled_hubs,hubs_context,hc u v huv X hu hv]
  have he : (∑ j : J,w j*(if Sum.inr j∈context X (minimizingOuters F u v X)
        then delta (F j) u v X else 0))= -(∑ j : J,w j*negativeResponse (F j) u v X) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro j hj
    simp only [mem_context_outer,mem_minimizingOuters,minimizing_literal (hF j),mul_neg]
  rw [he,add_neg_cancel]

/-- Compatibility of a variation's central function is recovered from actual
global zero contexts, after the spoke equations have determined its scales. -/
theorem compatible_of_tight_variation {z h : SetFunction H} {F : J → SetFunction H}
    (hF : ∀ j,IsMonotoneBoolean (F j)) {w t : J → ℝ} (hc : Compatible z F w)
    (ht : ∀ u v,u≠ v → ∀ A,u∉A → v∉A →
      delta (assembled z F w) u v A=0 → delta (assembled h F t) u v A=0) :
    Compatible h F t := by
  intro u v huv X hu hv
  have hz:=ht (Sum.inl u) (Sum.inl v) (fun he => huv (Sum.inl_injective he))
    (context X (minimizingOuters F u v X)) (by simpa using hu) (by simpa using hv)
    (assembled_minimizer_zero hF hc u v huv X hu hv)
  rw [delta_assembled_hubs,hubs_context] at hz
  have he : (∑ j : J,t j*(if Sum.inr j∈context X (minimizingOuters F u v X)
        then delta (F j) u v X else 0))= -(∑ j : J,t j*negativeResponse (F j) u v X) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro j hj
    simp only [mem_context_outer,mem_minimizingOuters,minimizing_literal (hF j),mul_neg]
  rw [he] at hz
  linarith

/-- The actual integrability relation space, written without choosing a
quotient basis. A vector belongs to it precisely when its weighted response
has a normalized central set-function lift. -/
def UniqueIntegrableRelation (F : J → SetFunction H) (w : J → ℝ) : Prop :=
  ∀ t : J → ℝ,(∃ h : SetFunction H,TranslationNormalized h ∧ Compatible h F t) →
    ∃ c : ℝ,t=c • w

theorem compatible_central_unique {z h : SetFunction H}
    (hzn : TranslationNormalized z) (hhn : TranslationNormalized h)
    {F : J → SetFunction H} {w t : J → ℝ} (hz : Compatible z F w)
    (hh : Compatible h F t) {c : ℝ} (ht : t=c • w) : h=c • z := by
  have hn : TranslationNormalized (h-c • z) := by
    constructor
    · change h ∅-c*z ∅=0
      rw [hhn.1,hzn.1,mul_zero,sub_self]
    · intro a
      change h {a}-c*z {a}=0
      rw [hhn.2 a,hzn.2 a,mul_zero,sub_self]
  apply sub_eq_zero.mp
  apply normalized_zero_elemental_eq_zero hn
  intro u v huv X hu hv
  have he : delta h u v X=c*delta z u v X := by
    rw [hh u v huv X hu hv,hz u v huv X hu hv,mul_sum]
    apply sum_congr rfl
    intro j hj
    change t j*negativeResponse (F j) u v X=c*(w j*negativeResponse (F j) u v X)
    have htj:=congrFun ht j
    change t j=c*w j at htj
    rw [htj]
    ring
  rw [delta_sub,delta_smul,he,sub_self]

theorem assembled_smul (z : SetFunction H) (F : J → SetFunction H)
    (w : J → ℝ) (c : ℝ) :
    assembled (c • z) F (c • w)=c • assembled z F w := by
  unfold assembled
  rw [smul_add,Finset.smul_sum]
  congr 1
  apply sum_congr rfl
  intro j hj
  change (c*w j) • branchLift j (F j)=c • (w j • branchLift j (F j))
  exact mul_smul _ _ _

/-- The whole normalized tight kernel, including all unused coordinates and
all nongraphical variations, is recovered from the positive response circuit. -/
theorem assembled_tight_kernel {z : SetFunction H} (hz : TranslationNormalized z)
    {F : J → SetFunction H} (hF : ∀ j,IsMonotoneBoolean (F j))
    {w : J → ℝ} (hc : Compatible z F w) (hrel : UniqueIntegrableRelation F w)
    (f : SetFunction (H⊕J)) (hf : TranslationNormalized f)
    (ht : ∀ u v,u≠ v → ∀ A,u∉A → v∉A →
      delta (assembled z F w) u v A=0 → delta f u v A=0) :
    ∃ c : ℝ,f=c • assembled z F w := by
  have houter : OuterZero f := by
    intro i j hij A hi hj
    exact ht (Sum.inr i) (Sum.inr j) (fun he => hij (Sum.inr_injective he)) A hi hj
      (delta_assembled_outer z F w i j hij A hi hj)
  let t : J → ℝ:=fun j => privateSlice f j univ
  have hparts : ∀ j,privateSlice f j=t j • F j :=
    fun j => privateSlice_scalar_of_spokeZeros hF hf ht j
  have hrep:=eq_assembled_of_privateSlices houter F t hparts
  have ht' : Compatible (boundarySlice f) F t :=
    compatible_of_tight_variation hF hc (by
      intro u v huv A hu hv hzero
      rw [← hrep]
      exact ht u v huv A hu hv hzero)
  obtain ⟨c,hct⟩:=hrel t ⟨boundarySlice f,boundarySlice_normalized hf,ht'⟩
  have hb:=compatible_central_unique hz (boundarySlice_normalized hf) hc ht' hct
  exact ⟨c,by rw [hrep,hb,hct,assembled_smul]⟩

theorem assembled_at_hubs (z : SetFunction H) (F : J → SetFunction H)
    (w : J → ℝ) (X : Finset H) : assembled z F w (hubSet X)=z X := by
  simp [assembled,boundaryLift,branchLift,Finset.sum_apply]

theorem assembled_at_one_outer (z : SetFunction H) (F : J → SetFunction H)
    (w : J → ℝ) (j : J) (X : Finset H) :
    assembled z F w (insert (Sum.inr j) (hubSet X))=z X+w j*F j X := by
  simp [assembled,boundaryLift,branchLift,Finset.sum_apply]

theorem privateSlice_assembled (z : SetFunction H) (F : J → SetFunction H)
    (w : J → ℝ) (j : J) (X : Finset H) :
    privateSlice (assembled z F w) j X=w j*F j X := by
  rw [privateSlice,assembled_at_one_outer,assembled_at_hubs]
  ring

theorem assembled_ne_zero (z : SetFunction H) (F : J → SetFunction H)
    (hF : ∀ j,IsMonotoneBoolean (F j)) (w : J → ℝ) (hw : ∃ j,w j≠0) :
    assembled z F w≠0 := by
  obtain ⟨j,hj⟩:=hw
  intro he
  have hh:=privateSlice_assembled z F w j univ
  rw [he,(hF j).full,mul_one] at hh
  exact hj (by simpa only [privateSlice,Pi.zero_apply,sub_self] using hh.symm)

/-- Lemma7.3's extremality conclusion, proved directly from the actual
set-function zero rows and their complete integrability relation space. -/
theorem positive_circuit_extreme {z : SetFunction H} (hz : TranslationNormalized z)
    {F : J → SetFunction H} (hF : ∀ j,IsMonotoneBoolean (F j))
    {w : J → ℝ} (hw : ∀ j,0≤ w j) (hne : ∃ j,w j≠0)
    (hc : Compatible z F w) (hrel : UniqueIntegrableRelation F w) :
    ExtremeSupermodular (assembled z F w) := by
  apply extremeSupermodular_of_tightEquations
    (assembled_normalized hz F hF w) (assembled_supermodular z F hF w hw hc)
    (assembled_ne_zero z F hF w hne)
  exact assembled_tight_kernel hz hF hc hrel

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart122

section BundlePart123
/- Source: Papers/GraphicalZonotopes/BooleanVertexExtension.lean -/






/-! # Attaching a single Boolean private vertex

This operation retains the original set function as its restriction to the
old vertices. A single tight old-edge equation identifies the old and new
scales, giving an economical extension of the ten-vertex ray of Section 8.2.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace BooleanVertexExtension
open Finset BooleanModule
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Vertex (V : Type*) := V ⊕ Fin 1

def append (z F : SetFunction V) : SetFunction (Vertex V) :=
  assembled z (fun _ : Fin 1 => F) (fun _ => 1)

@[simp] theorem append_at_hubs (z F : SetFunction V) (S : Finset V) :
    append z F (hubSet S) = z S := by
  exact assembled_at_hubs z (fun _ : Fin 1 => F) (fun _ => 1) S

@[simp] theorem append_at_new (z F : SetFunction V) (S : Finset V) :
    append z F (insert (Sum.inr 0) (hubSet S)) = z S + F S := by
  simpa only [append,one_mul] using
    assembled_at_one_outer z (fun _ : Fin 1 => F) (fun _ => 1) 0 S

theorem append_normalized {z F : SetFunction V}
    (hz : TranslationNormalized z) (hF : IsMonotoneBoolean F) :
    TranslationNormalized (append z F) :=
  assembled_normalized hz _ (fun _ => hF) _

theorem append_delta_old (z F : SetFunction V) (u v : V) (A : Finset (Vertex V)) :
    delta (append z F) (Sum.inl u) (Sum.inl v) A =
      delta z u v (hubs A) + if Sum.inr 0 ∈ A then delta F u v (hubs A) else 0 := by
  rw [append,delta_assembled_hubs]
  simp

theorem append_delta_new (z F : SetFunction V) (u : V)
    (A : Finset (Vertex V)) (hw : Sum.inr 0 ∉ A) :
    delta (append z F) (Sum.inl u) (Sum.inr 0) A =
      F (insert u (hubs A))-F (hubs A) := by
  rw [append,delta_assembled_spoke _ _ _ _ _ _ hw,one_mul]

/-- The two old-vertex slices and monotonicity of the new marginal are
exactly the elemental supermodularity conditions for a single new vertex. -/
theorem append_supermodular {z F : SetFunction V} (hz : Supermodular z)
    (hF : Monotone F) (hplus : Supermodular (z+F)) :
    Supermodular (append z F) := by
  apply ElementallyNonnegative.supermodular
  intro x y hxy A hx hy
  cases x with
  | inl u =>
    cases y with
    | inl v =>
      have huv : u ≠ v := fun he => hxy (congrArg Sum.inl he)
      have hu : u ∉ hubs A := by simpa using hx
      have hv : v ∉ hubs A := by simpa using hy
      rw [append_delta_old]
      split_ifs with hw
      · simpa only [delta_add] using hplus.elemental u v huv (hubs A) hu hv
      · simpa only [add_zero] using hz.elemental u v huv (hubs A) hu hv
    | inr j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      rw [append_delta_new _ _ _ _ hy]
      exact sub_nonneg.mpr (hF (subset_insert _ _))
  | inr i =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    cases y with
    | inl v =>
      rw [delta_comm,append_delta_new _ _ _ _ hx]
      exact sub_nonneg.mpr (hF (subset_insert _ _))
    | inr j =>
      exact False.elim (hxy (congrArg Sum.inr (Subsingleton.elim _ _)))

theorem boundarySlice_supermodular {f : SetFunction (Vertex V)}
    (hf : Supermodular f) : Supermodular (boundarySlice f) := by
  intro A B
  simpa only [boundarySlice,hubSet,map_union,map_inter] using hf (hubSet A) (hubSet B)

/-- A strict old response canceled by the Boolean marginal fixes the new
private scale. The proof quantifies over every actual cone decomposition. -/
theorem append_extreme {z F : SetFunction V} (hz : ExtremeSupermodular z)
    (hF : IsMonotoneBoolean F) (hplus : Supermodular (z+F))
    (hcontact : ∃ u v : V, u ≠ v ∧ ∃ S : Finset V,
      u ∉ S ∧ v ∉ S ∧ delta z u v S = 1 ∧ delta F u v S = -1) :
    ExtremeSupermodular (append z F) := by
  have hn := append_normalized hz.1 hF
  have hs := append_supermodular hz.2.1 hF.monotone hplus
  have hne : append z F ≠ 0 := by
    intro he
    apply hz.2.2.1
    funext S
    have h := congrFun he (hubSet S)
    simpa only [append_at_hubs,Pi.zero_apply] using h
  refine ⟨hn,hs,hne,?_⟩
  intro f g hfn hgn hfs hgs he
  have hsum : boundarySlice f + boundarySlice g = z := by
    funext S
    have h := congrFun he (hubSet S)
    simpa only [Pi.add_apply,append_at_hubs,boundarySlice] using h
  obtain ⟨a,ha,hfa⟩ := hz.2.2.2 (boundarySlice f) (boundarySlice g)
    (boundarySlice_normalized hfn) (boundarySlice_normalized hgn)
    (boundarySlice_supermodular hfs) (boundarySlice_supermodular hgs) hsum
  have ht : ∀ u v, u ≠ v → ∀ A, u ∉ A → v ∉ A →
      delta (append z F) u v A = 0 → delta f u v A = 0 := by
    intro u v huv A hu hv hzero
    have hf := hfs.elemental u v huv A hu hv
    have hg := hgs.elemental u v huv A hu hv
    rw [← he,delta_add] at hzero
    linarith
  let b : Fin 1 → ℝ := fun j => privateSlice f j univ
  have hparts : ∀ j : Fin 1, privateSlice f j = b j • F :=
    fun j => privateSlice_scalar_of_spokeZeros (fun _ => hF) hfn ht j
  have houter : OuterZero f := by
    intro i j hij
    exact False.elim (hij (Subsingleton.elim _ _))
  have hrep := eq_assembled_of_privateSlices houter (fun _ : Fin 1 => F) b hparts
  obtain ⟨u,v,huv,S,hu,hv,hzrow,hFrow⟩ := hcontact
  let A : Finset (Vertex V) := insert (Sum.inr 0) (hubSet S)
  have huA : Sum.inl u ∉ A := by simpa [A] using hu
  have hvA : Sum.inl v ∉ A := by simpa [A] using hv
  have hzA : delta (append z F) (Sum.inl u) (Sum.inl v) A = 0 := by
    rw [append_delta_old]
    simp only [A,hubs_insert_outer,hubs_hubSet,mem_insert_self,ite_true,hzrow,hFrow]
    norm_num
  have hfA := ht (Sum.inl u) (Sum.inl v)
    (fun h => huv (Sum.inl_injective h)) A huA hvA hzA
  rw [hrep,hfa,delta_assembled_hubs,delta_smul] at hfA
  have hab : b 0 = a := by
    simp only [A,hubs_insert_outer,hubs_hubSet,hzrow,hFrow,mul_one,
      Fin.sum_univ_one,mem_insert_self,ite_true,mul_neg_one] at hfA
    linarith
  refine ⟨a,ha,?_⟩
  have hb : b = a • (fun _ : Fin 1 => (1 : ℝ)) := by
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    simp [hj,hab]
  rw [hrep,hfa,hb,assembled_smul]
  rfl

/-- The old slack bound rises by at most one. This will give the exact
`n-6` dilation after starting with the ten-vertex bound four. -/
theorem append_delta_upper {z F : SetFunction V} (hF : IsMonotoneBoolean F)
    {M : ℝ} (hM : 0 ≤ M)
    (hz : ∀ u v, u ≠ v → ∀ S, u ∉ S → v ∉ S → delta z u v S ≤ M) :
    ∀ u v : Vertex V, u ≠ v → ∀ A, u ∉ A → v ∉ A →
      delta (append z F) u v A ≤ M+1 := by
  intro x y hxy A hx hy
  cases x with
  | inl u =>
    cases y with
    | inl v =>
      have h := hz u v (fun he => hxy (congrArg Sum.inl he)) (hubs A)
        (by simpa using hx) (by simpa using hy)
      rw [append_delta_old]
      split_ifs
      · rcases delta_values hF u v (hubs A) with hh | hh | hh <;> rw [hh] <;> linarith
      · linarith
    | inr j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      rw [append_delta_new _ _ _ _ hy]
      rcases cover_values hF u (hubs A) with hh | hh <;> rw [hh] <;> linarith
  | inr i =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    cases y with
    | inl v =>
      rw [delta_comm,append_delta_new _ _ _ _ hx]
      rcases cover_values hF v (hubs A) with hh | hh <;> rw [hh] <;> linarith
    | inr j =>
      exact False.elim (hxy (congrArg Sum.inr (Subsingleton.elim _ _)))

end BooleanVertexExtension
end GraphicalZonotopes

end
end
end BundlePart123

section BundlePart124
/- Source: Papers/GraphicalZonotopes/TriangularBooleanExtension.lean -/




/-! # The three-neighbor extension used in Theorem 8.2

The new marginal is the literal monotone Boolean function `b ∧ (a ∨ t)`.
Its sole negative elemental response is on `at` when `b` is present.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace BooleanVertexExtension
open Finset BooleanModule
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

def andOr (a b t : V) : SetFunction V :=
  fun S => if b ∈ S ∧ (a ∈ S ∨ t ∈ S) then 1 else 0

theorem andOr_boolean (a b t : V) : IsMonotoneBoolean (andOr a b t) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro A B hAB
    by_cases h : b ∈ A ∧ (a ∈ A ∨ t ∈ A)
    · have hB : b ∈ B ∧ (a ∈ B ∨ t ∈ B) :=
        ⟨hAB h.1,h.2.elim (fun h => Or.inl (hAB h)) (fun h => Or.inr (hAB h))⟩
      simp only [andOr,if_pos h,if_pos hB,le_refl]
    · simp only [andOr,if_neg h]
      split_ifs <;> norm_num
  · intro S
    dsimp only [andOr]
    split_ifs <;> simp
  · simp [andOr]
  · simp [andOr]

theorem andOr_insert_outside {a b t u : V}
    (hua : u ≠ a) (hub : u ≠ b) (hut : u ≠ t) (S : Finset V) :
    andOr a b t (insert u S) = andOr a b t S := by
  simp [andOr,Ne.symm hua,Ne.symm hub,Ne.symm hut]

theorem andOr_delta_outside {a b t u : V}
    (hua : u ≠ a) (hub : u ≠ b) (hut : u ≠ t) (v : V) (S : Finset V) :
    delta (andOr a b t) u v S = 0 := by
  simp only [delta,andOr_insert_outside hua hub hut]
  ring

theorem andOr_delta_at {a b t : V} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    {S : Finset V} (ha : a ∉ S) (ht : t ∉ S) :
    delta (andOr a b t) a t S = if b ∈ S then -1 else 0 := by
  by_cases hb : b ∈ S <;>
    simp [delta,andOr,hab,hat,hbt,Ne.symm hab,Ne.symm hat,Ne.symm hbt,ha,ht,hb]

theorem andOr_delta_ab {a b t : V} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    {S : Finset V} (ha : a ∉ S) (hb : b ∉ S) :
    delta (andOr a b t) a b S = if t ∈ S then 0 else 1 := by
  by_cases ht : t ∈ S <;>
    simp [delta,andOr,hab,hat,hbt,Ne.symm hab,Ne.symm hat,Ne.symm hbt,ha,ht,hb]

theorem andOr_delta_bt {a b t : V} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    {S : Finset V} (hb : b ∉ S) (ht : t ∉ S) :
    delta (andOr a b t) b t S = if a ∈ S then 0 else 1 := by
  by_cases ha : a ∈ S <;>
    simp [delta,andOr,hab,hat,hbt,Ne.symm hab,Ne.symm hat,Ne.symm hbt,ha,ht,hb]

theorem andOr_negative_iff {a b t : V} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    {u v : V} (huv : u ≠ v) {S : Finset V} (hu : u ∉ S) (hv : v ∉ S) :
    delta (andOr a b t) u v S = -1 ↔
      ((u = a ∧ v = t) ∨ (u = t ∧ v = a)) ∧ b ∈ S := by
  by_cases hua : u = a
  · subst u
    by_cases hvb : v = b
    · subst v
      rw [andOr_delta_ab hab hat hbt hu hv]
      split_ifs <;> simp_all <;> norm_num
    · by_cases hvt : v = t
      · subst v
        rw [andOr_delta_at hab hat hbt hu hv]
        split_ifs <;> simp_all <;> norm_num
      · rw [delta_comm,andOr_delta_outside (Ne.symm huv) hvb hvt]
        simp_all
  · by_cases hub : u = b
    · subst u
      by_cases hva : v = a
      · subst v
        rw [delta_comm,andOr_delta_ab hab hat hbt hv hu]
        split_ifs <;> simp_all <;> norm_num
      · by_cases hvt : v = t
        · subst v
          rw [andOr_delta_bt hab hat hbt hu hv]
          split_ifs <;> simp_all <;> norm_num
        · rw [delta_comm,andOr_delta_outside hva (Ne.symm huv) hvt]
          simp_all
    · by_cases hut : u = t
      · subst u
        by_cases hva : v = a
        · subst v
          rw [delta_comm,andOr_delta_at hab hat hbt hv hu]
          split_ifs <;> simp_all <;> norm_num
        · by_cases hvb : v = b
          · subst v
            rw [delta_comm,andOr_delta_bt hab hat hbt hv hu]
            split_ifs <;> simp_all <;> norm_num
          · rw [delta_comm,andOr_delta_outside hva hvb (Ne.symm huv)]
            simp_all
      · rw [andOr_delta_outside hua hub hut]
        simp_all

/-- The boundary condition is literal: every context containing the second
hub gives slack one on the first-hub–tip edge. -/
def UnitBoundary (z : SetFunction V) (a b t : V) : Prop :=
  a ≠ b ∧ a ≠ t ∧ b ≠ t ∧
    ∀ S : Finset V, a ∉ S → t ∉ S → b ∈ S → delta z a t S = 1

theorem andOr_add_supermodular {z : SetFunction V} {a b t : V}
    (hz : Supermodular z) (hb : UnitBoundary z a b t) :
    Supermodular (z + andOr a b t) := by
  apply ElementallyNonnegative.supermodular
  intro u v huv S hu hv
  rw [delta_add]
  have hnn := hz.elemental u v huv S hu hv
  rcases delta_values (andOr_boolean a b t) u v S with hneg | hzero | hone
  · obtain ⟨hpair,hbS⟩ := (andOr_negative_iff hb.1 hb.2.1 hb.2.2.1 huv hu hv).mp hneg
    rcases hpair with ⟨hua,hvt⟩ | ⟨hut,hva⟩
    · subst u
      subst v
      rw [hb.2.2.2 S hu hv hbS,hneg]
      norm_num
    · subst u
      subst v
      rw [delta_comm (z := z) t a S,hb.2.2.2 S hv hu hbS,hneg]
      norm_num
  · rw [hzero]
    linarith
  · rw [hone]
    linarith

theorem triangular_append_extreme {z : SetFunction V} {a b t : V}
    (hz : ExtremeSupermodular z) (hb : UnitBoundary z a b t) :
    ExtremeSupermodular (append z (andOr a b t)) := by
  apply append_extreme hz (andOr_boolean a b t) (andOr_add_supermodular hz.2.1 hb)
  refine ⟨a,t,hb.2.1,{b},?_,?_,?_,?_⟩
  · simpa using hb.1
  · simpa using hb.2.2.1.symm
  · exact hb.2.2.2 _ (by simpa using hb.1) (by simpa using hb.2.2.1.symm) (by simp)
  · rw [andOr_delta_at hb.1 hb.2.1 hb.2.2.1 (by simpa using hb.1)
      (by simpa using hb.2.2.1.symm)]
    simp

/-- Swapping the hubs makes the newly appended vertex a boundary of exactly
the same kind. This is the uniform induction for every requested order. -/
theorem triangular_append_boundary {z : SetFunction V} {a b t : V}
    (hb : UnitBoundary z a b t) :
    UnitBoundary (append z (andOr a b t)) (Sum.inl b) (Sum.inl a) (Sum.inr 0) := by
  refine ⟨by simpa using hb.1.symm,by simp,by simp,?_⟩
  intro A hbA hwA haA
  rw [append_delta_new _ _ _ _ hwA]
  have ha : a ∈ hubs A := by simpa using haA
  have hb' : b ∉ hubs A := by simpa using hbA
  simp [andOr,ha,hb',hb.1,hb.1.symm]

end BooleanVertexExtension
end GraphicalZonotopes

end
end
end BundlePart124

section BundlePart125
/- Source: Papers/GraphicalZonotopes/SingleVertexGraph.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace SingleVertexGraph
open Finset BooleanModule BooleanVertexExtension
variable {V : Type*} [Fintype V] [DecidableEq V]

def old : V ↪ Vertex V := ⟨Sum.inl,Sum.inl_injective⟩

def graph (G : SimpleGraph V) (N : Finset V) : SimpleGraph (Vertex V) where
  Adj x y := match x,y with
    | Sum.inl u,Sum.inl v => G.Adj u v
    | Sum.inl u,Sum.inr _ => u ∈ N
    | Sum.inr _,Sum.inl v => v ∈ N
    | Sum.inr _,Sum.inr _ => False
  symm := ⟨by
    intro x y h
    cases x <;> cases y
    · exact G.adj_symm h
    · exact h
    · exact h
    · exact h⟩
  loopless := ⟨by
    intro x hx
    cases x with
    | inl v => exact G.irrefl hx
    | inr j => exact hx⟩

@[simp] theorem graph_old_adj (G : SimpleGraph V) (N : Finset V) (u v : V) :
    (graph G N).Adj (Sum.inl u) (Sum.inl v) ↔ G.Adj u v := Iff.rfl

@[simp] theorem graph_new_adj (G : SimpleGraph V) (N : Finset V) (u : V) :
    (graph G N).Adj (Sum.inr 0) (Sum.inl u) ↔ u ∈ N := Iff.rfl

@[simp] theorem graph_adj_new (G : SimpleGraph V) (N : Finset V) (u : V) :
    (graph G N).Adj (Sum.inl u) (Sum.inr 0) ↔ u ∈ N := Iff.rfl

theorem old_le (G : SimpleGraph V) (N : Finset V) : G.map old ≤ graph G N := by
  intro x y hxy
  obtain ⟨u,v,huv,rfl,rfl⟩ := (SimpleGraph.map_adj old G x y).mp hxy
  exact huv

theorem old_comap (G : SimpleGraph V) (N : Finset V) : (graph G N).comap old = G := rfl

theorem connected {G : SimpleGraph V} (hG : G.Connected) {N : Finset V}
    (hN : N.Nonempty) : (graph G N).Connected := by
  obtain ⟨v,hv⟩ := hN
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨Sum.inr 0,?_⟩
  intro x
  cases x with
  | inl u =>
    exact (SimpleGraph.Adj.reachable (show (graph G N).Adj (Sum.inr 0) (Sum.inl v) from hv)).trans
      ((hG v u).map ⟨Sum.inl,fun h => h⟩)
  | inr j =>
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact SimpleGraph.Reachable.rfl

theorem card_hubs_of_new_not_mem {C : Finset (Vertex V)} (hC : Sum.inr 0 ∉ C) :
    (hubs C).card = C.card := by
  have he : hubSet (J := Fin 1) (hubs C) = C := by
    ext x
    cases x with
    | inl u => simp
    | inr j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp [hC]
  have hc := congrArg Finset.card he
  simpa only [hubSet,card_map] using hc

theorem card_hubs_of_new_mem {C : Finset (Vertex V)} (hC : Sum.inr 0 ∈ C) :
    (hubs C).card + 1 = C.card := by
  have he : insert (Sum.inr 0) (hubSet (J := Fin 1) (hubs C)) = C := by
    ext x
    cases x with
    | inl u => simp
    | inr j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp [hC]
  have hc := congrArg Finset.card he
  rw [card_insert_of_notMem (notMem_hubSet_outer _ (0 : Fin 1)),hubSet,card_map] at hc
  exact hc

theorem cliqueFree_five {G : SimpleGraph V} (hG : G.CliqueFree 5)
    {N : Finset V} (hN : N.card ≤ 3) : (graph G N).CliqueFree 5 := by
  intro C hC
  obtain ⟨hcl,hcard⟩ := hC
  have hc : G.IsClique (hubs C) := by
    intro u hu v hv huv
    exact hcl ((mem_hubs _ _).mp hu) ((mem_hubs _ _).mp hv) (fun he => huv (Sum.inl_injective he))
  by_cases hw : Sum.inr 0 ∈ C
  · have hs : hubs C ⊆ N := by
      intro u hu
      exact hcl hw ((mem_hubs _ _).mp hu) (by simp)
    have hsz := card_le_card hs
    have hcard' := card_hubs_of_new_mem hw
    omega
  · exact hG _ ⟨hc,(card_hubs_of_new_not_mem hw).trans hcard⟩

def newEdges (N : Finset V) : Finset (Finset (Vertex V)) :=
  N.image (fun v => {Sum.inl v,Sum.inr 0})

theorem newEdge_injective : Function.Injective
    (fun v : V => ({Sum.inl v,Sum.inr 0} : Finset (Vertex V))) := by
  intro u v he
  change ({Sum.inl u,Sum.inr 0} : Finset (Vertex V)) = {Sum.inl v,Sum.inr 0} at he
  have h : Sum.inl u ∈ ({Sum.inl v,Sum.inr 0} : Finset (Vertex V)) := by
    rw [← he]
    simp
  simpa only [mem_insert,mem_singleton,Sum.inl.injEq,Sum.inl_ne_inr,or_false] using h

theorem edgeFamily_eq (G : SimpleGraph V) (N : Finset V) :
    edgeFamily (graph G N) =
      (edgeFamily G).image (fun C => C.map old) ∪ newEdges N := by
  ext C
  constructor
  · intro hC
    obtain ⟨hc,hcl⟩ := (mem_edgeFamily _ C).mp hC
    obtain ⟨x,y,hxy,rfl⟩ := card_eq_two.mp hc
    have hxyG := hcl x (by simp) y (by simp) hxy
    cases x with
    | inl u =>
      cases y with
      | inl v =>
        apply mem_union_left
        refine mem_image.mpr ⟨{u,v},?_,?_⟩
        · exact (pair_mem_edgeFamily G (fun he => hxy (congrArg Sum.inl he))).mpr hxyG
        · simp [old]
      | inr j =>
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        exact mem_union_right _ (mem_image.mpr ⟨u,hxyG,rfl⟩)
    | inr i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      cases y with
      | inl v =>
        exact mem_union_right _ (mem_image.mpr ⟨v,hxyG,pair_comm _ _⟩)
      | inr j => exact False.elim hxyG
  · intro hC
    rcases mem_union.mp hC with hC | hC
    · obtain ⟨D,hD,rfl⟩ := mem_image.mp hC
      obtain ⟨hd,hcl⟩ := (mem_edgeFamily G D).mp hD
      refine (mem_edgeFamily _ _).mpr ⟨by simpa only [card_map] using hd,?_⟩
      intro x hx y hy hxy
      obtain ⟨u,hu,rfl⟩ := mem_map.mp hx
      obtain ⟨v,hv,rfl⟩ := mem_map.mp hy
      exact hcl u hu v hv (fun he => hxy (congrArg old he))
    · obtain ⟨u,hu,rfl⟩ := mem_image.mp hC
      exact (pair_mem_edgeFamily _ (by simp)).mpr hu

theorem edgeFamily_card (G : SimpleGraph V) (N : Finset V) :
    (edgeFamily (graph G N)).card = (edgeFamily G).card + N.card := by
  rw [edgeFamily_eq,card_union_of_disjoint]
  · rw [card_image_of_injective _ (Finset.map_injective old)]
    unfold newEdges
    exact congrArg (_ + ·) (card_image_of_injective N newEdge_injective)
  · apply disjoint_left.mpr
    intro C hC hN
    obtain ⟨D,hD,rfl⟩ := mem_image.mp hC
    obtain ⟨u,hu,he⟩ := mem_image.mp hN
    have hw : Sum.inr 0 ∈ D.map old := by rw [← he]; simp
    obtain ⟨v,hv,hvw⟩ := mem_map.mp hw
    exact Sum.inl_ne_inr hvw

end SingleVertexGraph
end GraphicalZonotopes

end
end
end BundlePart125

section BundlePart126
/- Source: Papers/GraphicalZonotopes/TreeJoinGraph.lean -/







/-! The literal join of a graph with a two-vertex clique. The two new
vertices are added successively, each adjacent to every previous vertex.
No tree or degree condition is incorporated into the graph definition. -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.TreeJoin
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Vertex (V : Type*) := (V ⊕ Fin 1) ⊕ Fin 1

def graph (T : SimpleGraph V) : SimpleGraph (Vertex V) :=
  SingleVertexGraph.graph (SingleVertexGraph.graph T univ) univ

def old : V ↪ Vertex V := ⟨fun v => Sum.inl (Sum.inl v),by
  intro u v h
  exact Sum.inl_injective (Sum.inl_injective h)⟩

def a : Vertex V := Sum.inr 0
def b : Vertex V := Sum.inl (Sum.inr 0)

def core (S : Finset V) : Finset (Vertex V) := insert a (insert b (S.map old))

def outer (C : Finset (Vertex V)) : Finset V := univ.filter (fun v => old v ∈ C)

@[simp] theorem mem_outer (C : Finset (Vertex V)) (v : V) :
    v ∈ outer C ↔ old v ∈ C := by simp [outer]

@[simp] theorem a_mem_core (S : Finset V) : a ∈ core S := by simp [core]
@[simp] theorem b_mem_core (S : Finset V) : b ∈ core S := by simp [core]
@[simp] theorem old_mem_core (S : Finset V) (v : V) : old v ∈ core S ↔ v ∈ S := by
  simp [core,old,a,b]

@[simp] theorem core_card (S : Finset V) : (core S).card = S.card+2 := by
  simp [core,a,b,old]

theorem core_mono {S U : Finset V} (h : S ⊆ U) : core S ⊆ core U :=
  insert_subset_insert _ (insert_subset_insert _ (map_subset_map.mpr h))

theorem vertex_cases (x : Vertex V) : x=a ∨ x=b ∨ ∃ v,x=old v := by
  rcases x with (v|i)|j
  · exact Or.inr (Or.inr ⟨v,rfl⟩)
  · have hi : i=0 := Subsingleton.elim _ _
    subst i
    exact Or.inr (Or.inl rfl)
  · have hj : j=0 := Subsingleton.elim _ _
    subst j
    exact Or.inl rfl

@[simp] theorem core_univ : core (univ : Finset V)=univ := by
  apply eq_univ_iff_forall.mpr
  intro x
  rcases vertex_cases x with rfl|rfl|⟨v,rfl⟩ <;> simp

theorem core_outer {C : Finset (Vertex V)} (ha : a∈C) (hb : b∈C) : core (outer C)=C := by
  ext x
  rcases vertex_cases x with rfl|rfl|⟨v,rfl⟩ <;> simp [ha,hb]

@[simp] theorem graph_old_adj (T : SimpleGraph V) (u v : V) :
    (graph T).Adj (old u) (old v) ↔ T.Adj u v := Iff.rfl

theorem core_clique_iff (T : SimpleGraph V) (S : Finset V) :
    (graph T).IsClique (core S) ↔ T.IsClique S := by
  constructor
  · intro h u hu v hv huv
    exact h ((old_mem_core S u).mpr hu) ((old_mem_core S v).mpr hv)
      (fun he => huv (old.injective he))
  · intro h x hx y hy hxy
    rcases vertex_cases x with rfl|rfl|⟨u,rfl⟩ <;>
      rcases vertex_cases y with rfl|rfl|⟨v,rfl⟩
    all_goals try { simp [a,b,graph,SingleVertexGraph.graph,old] at hxy ⊢ }
    exact h ((old_mem_core S u).mp hx) ((old_mem_core S v).mp hy)
      (fun he => hxy (congrArg old he))

theorem edgeFamily_card (T : SimpleGraph V) :
    (edgeFamily (graph T)).card=(edgeFamily T).card+2*Fintype.card V+1 := by
  rw [graph,SingleVertexGraph.edgeFamily_card,SingleVertexGraph.edgeFamily_card]
  simp only [card_univ,Fintype.card_sum,Fintype.card_fin]
  omega

theorem tree_edgeFamily_card {T : SimpleGraph V} (hT : T.IsTree) :
    (edgeFamily T).card+1=Fintype.card V := by
  rw [edgeFamily_eq_image_edgeFinset,card_image_of_injective _ sym2_toFinset_injective]
  exact hT.card_edgeFinset

/-- Every connected graph with at least two vertices admits a tetrahedral
growth after adjoining the two universal adjacent vertices. -/
theorem connected_growth {T : SimpleGraph V} (hT : T.Connected)
    (hn : 2 ≤ Fintype.card V) : TetrahedralGrowth (graph T) univ := by
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hn
  obtain ⟨u⟩ := hT.nonempty
  obtain ⟨v,huv⟩ := hT.preconnected.exists_adj_of_nontrivial u
  let C := core ({u,v} : Finset V)
  have hCcard : C.card=4 := by simp [C,core_card,T.ne_of_adj huv]
  have hCcl : (graph T).IsClique C := (core_clique_iff T _).mpr
    (by simpa only [coe_pair,SimpleGraph.isClique_pair] using (fun _ : u≠ v => huv))
  let candidates : Finset (Finset (Vertex V)) := univ.filter
    (fun U => C⊆U ∧ TetrahedralGrowth (graph T) U)
  have hbase : C∈candidates := mem_filter.mpr
    ⟨mem_univ _,Subset.rfl,TetrahedralGrowth.base C hCcard hCcl⟩
  obtain ⟨U,hU,hmax⟩ := candidates.exists_max_image Finset.card ⟨C,hbase⟩
  obtain ⟨hCU,hgrowth⟩ := (mem_filter.mp hU).2
  have ha : a∈U := hCU (a_mem_core _)
  have hb : b∈U := hCU (b_mem_core _)
  have hclosed : ∀ x y : V,old x∈U → T.Adj x y → old y∈U := by
    intro x y hx hxy
    let D := core ({x,y} : Finset V)
    have hDcard : D.card=4 := by simp [D,core_card,T.ne_of_adj hxy]
    have hDcl : (graph T).IsClique D := (core_clique_iff T _).mpr
      (by simpa only [coe_pair,SimpleGraph.isClique_pair] using (fun _ : x≠ y => hxy))
    have hsub : core ({x} : Finset V)⊆D∩U := by
      intro z hz
      refine mem_inter.mpr ⟨core_mono (by simp) hz,?_⟩
      rcases vertex_cases z with rfl|rfl|⟨w,rfl⟩
      · exact ha
      · exact hb
      · have he : w=x := by simpa using (old_mem_core _ _).mp hz
        simpa only [he] using hx
    have hover : 3≤(D∩U).card := by
      simpa only [core_card,card_singleton] using card_le_card hsub
    have hg := hgrowth.extend_fourClique D hDcard hDcl hover
    have hcand : U∪D∈candidates := mem_filter.mpr
      ⟨mem_univ _,hCU.trans subset_union_left,hg⟩
    have he : U∪D=U := (eq_of_subset_of_card_le subset_union_left (hmax _ hcand)).symm
    rw [←he]
    exact mem_union_right U ((old_mem_core _ y).mpr (by simp))
  have hu : old u∈U := hCU ((old_mem_core _ u).mpr (by simp))
  have hall : ∀ w : V,old w∈U := by
    intro w
    have hp := (SimpleGraph.reachable_iff_reflTransGen (G := T) u w).mp (hT u w)
    induction hp with
    | refl => exact hu
    | @tail x y hp hxy ih => exact hclosed x y ih hxy
  have hUeq : U=univ := by
    apply eq_univ_iff_forall.mpr
    intro x
    rcases vertex_cases x with rfl|rfl|⟨w,rfl⟩
    · exact ha
    · exact hb
    · exact hall w
  simpa only [hUeq] using hgrowth

/-- The join of a tree having at least two vertices with K₂ is a genuine
3-tree, by tetrahedral growth and the exact edge count. -/
theorem isThreeTree {T : SimpleGraph V} (hT : T.IsTree)
    (hn : 2 ≤ Fintype.card V) : IsThreeTree (graph T) := by
  have hg := connected_growth hT.connected hn
  have hc := hg.edge_bound_and_equality.2
  simp only [inducedOn_univ,card_univ] at hc
  apply hc
  rw [edgeFamily_card]
  have ht := tree_edgeFamily_card hT
  simp only [Vertex,Fintype.card_sum,Fintype.card_fin]
  omega

/-- A finite nonempty forest with n−1 edges is connected. The proof extends
it to an actual spanning tree and uses equality of finite edge sets. -/
theorem forest_isTree_of_card {T : SimpleGraph V} [Nonempty V]
    (hT : T.IsAcyclic) (hc : T.edgeFinset.card+1=Fintype.card V) : T.IsTree := by
  obtain ⟨H,hTH,hHtop,hH⟩ :=
    (SimpleGraph.connected_top (V := V)).exists_isTree_le_of_le_of_isAcyclic
      (show T≤⊤ from le_top) hT
  have he : T.edgeFinset=H.edgeFinset :=
    eq_of_subset_of_card_le (SimpleGraph.edgeFinset_mono hTH) (by
      have hcard := hH.card_edgeFinset
      omega)
  have hEq : T=H := SimpleGraph.edgeFinset_inj.mp he
  rwa [hEq]

end GraphicalZonotopes.TreeJoin

end
end
end BundlePart126

section BundlePart127
/- Source: Papers/GraphicalZonotopes/TreeJoinCliques.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.TreeJoin
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem outer_core (S : Finset V) : outer (core S)=S := by
  ext v
  simp

theorem core_injective : Function.Injective (core : Finset V → Finset (Vertex V)) := by
  intro S U h
  simpa only [outer_core] using congrArg outer h

theorem core_subset_core_iff (S U : Finset V) : core S⊆core U ↔ S⊆U := by
  constructor
  · intro h v hv
    exact (old_mem_core U v).mp (h ((old_mem_core S v).mpr hv))
  · exact core_mono

theorem outer_clique {T : SimpleGraph V} {C : Finset (Vertex V)}
    (hc : (graph T).IsClique C) : T.IsClique (outer C) := by
  intro u hu v hv huv
  exact hc ((mem_outer C u).mp hu) ((mem_outer C v).mp hv)
    (fun he => huv (old.injective he))

theorem forest_clique_card_le_two {T : SimpleGraph V} (hT : T.IsAcyclic)
    {C : Finset V} (hc : T.IsClique C) : C.card≤2 := by
  by_contra h
  obtain ⟨D,hDC,hD⟩ := exists_subset_card_eq (show 3≤ C.card by omega)
  exact hT.cliqueFree_three D ⟨fun u hu v hv huv => hc (hDC hu) (hDC hv) huv,hD⟩

theorem tetrahedron_hubs {T : SimpleGraph V} (hT : T.IsAcyclic)
    {C : Finset (Vertex V)} (hcard : C.card=4) (hcl : (graph T).IsClique C) :
    a∈C ∧ b∈C := by
  have hout := forest_clique_card_le_two hT (outer_clique hcl)
  constructor
  · by_contra ha
    have hs : C⊆insert b ((outer C).map old) := by
      intro x hx
      rcases vertex_cases x with rfl|rfl|⟨v,rfl⟩
      · exact False.elim (ha hx)
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_map.mpr ⟨v,(mem_outer C v).mpr hx,rfl⟩)
    have hn := (card_le_card hs).trans (card_insert_le _ _)
    simp only [card_map] at hn
    omega
  · by_contra hb
    have hs : C⊆insert a ((outer C).map old) := by
      intro x hx
      rcases vertex_cases x with rfl|rfl|⟨v,rfl⟩
      · exact mem_insert_self _ _
      · exact False.elim (hb hx)
      · exact mem_insert_of_mem (mem_map.mpr ⟨v,(mem_outer C v).mpr hx,rfl⟩)
    have hn := (card_le_card hs).trans (card_insert_le _ _)
    simp only [card_map] at hn
    omega

theorem tetrahedra_eq_edges {T : SimpleGraph V} (hT : T.IsAcyclic) :
    tetrahedra (graph T)=(edgeFamily T).image core := by
  ext C
  constructor
  · intro hC
    obtain ⟨hc,hcl⟩ := (mem_filter.mp hC).2
    obtain ⟨ha,hb⟩ := tetrahedron_hubs hT hc hcl
    have he := core_outer ha hb
    refine mem_image.mpr ⟨outer C,?_,he⟩
    apply (mem_edgeFamily T _).mpr
    refine ⟨?_,fun u hu v hv huv => outer_clique hcl hu hv huv⟩
    have hn := core_card (outer C)
    rw [he,hc] at hn
    omega
  · intro hC
    obtain ⟨E,hE,rfl⟩ := mem_image.mp hC
    obtain ⟨hcard,hcl⟩ := (mem_edgeFamily T E).mp hE
    exact mem_filter.mpr ⟨mem_univ _,by simp [hcard],
      (core_clique_iff T E).mpr hcl⟩

theorem pair_core_injective (v : V) :
    Function.Injective (fun w : V => core ({v,w} : Finset V)) := by
  intro w z he
  have h := core_injective he
  have hw : w=v ∨ w=z := by
    have hm : w∈({v,z} : Finset V) := by rw [←h]; simp
    simpa only [mem_insert,mem_singleton] using hm
  rcases hw with hw|hw
  · have hz : z=v := by
      have hm : z∈({v,w} : Finset V) := by rw [h]; simp
      simpa only [hw,mem_insert,mem_singleton,or_self] using hm
    exact hw.trans hz.symm
  · exact hw

theorem tetrahedra_over_vertex {T : SimpleGraph V} (hT : T.IsAcyclic) (v : V) :
    (tetrahedra (graph T)).filter (fun C => core ({v} : Finset V)⊆C)=
      (T.neighborFinset v).image (fun w => core ({v,w} : Finset V)) := by
  ext C
  constructor
  · intro hC
    obtain ⟨hC,hsub⟩ := mem_filter.mp hC
    rw [tetrahedra_eq_edges hT] at hC
    obtain ⟨E,hE,rfl⟩ := mem_image.mp hC
    have hv : v∈E := singleton_subset_iff.mp ((core_subset_core_iff _ _).mp hsub)
    obtain ⟨hcard,hcl⟩ := (mem_edgeFamily T E).mp hE
    obtain ⟨u,w,huw,rfl⟩ := card_eq_two.mp hcard
    rcases mem_insert.mp hv with hv|hv
    · subst u
      have hadj : T.Adj v w := hcl v (by simp) w (by simp) huw
      exact mem_image.mpr ⟨w,(T.mem_neighborFinset v w).mpr hadj,rfl⟩
    · have he : v=w := mem_singleton.mp hv
      subst w
      have hadj : T.Adj v u := hcl v (by simp) u (by simp) huw.symm
      exact mem_image.mpr ⟨u,(T.mem_neighborFinset v u).mpr hadj,by rw [pair_comm]⟩
  · intro hC
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hC
    have hadj := (T.mem_neighborFinset v w).mp hw
    refine mem_filter.mpr ⟨?_,core_mono (by simp)⟩
    rw [tetrahedra_eq_edges hT]
    exact mem_image.mpr ⟨{v,w},(pair_mem_edgeFamily T (T.ne_of_adj hadj)).mpr hadj,rfl⟩

/-- The triangle through the two hubs and v is contained in exactly
degree(v) tetrahedra. This is the literal multiplicity in the ambient join. -/
theorem triangleMultiplicity_core_singleton {T : SimpleGraph V}
    (hT : T.IsAcyclic) (v : V) :
    triangleMultiplicity (graph T) (core {v})=T.degree v := by
  unfold triangleMultiplicity
  rw [tetrahedra_over_vertex hT,card_image_of_injective _ (pair_core_injective v)]
  exact T.card_neighborFinset_eq_degree v

theorem triangleMultiplicity_le_one_of_missing_hub {T : SimpleGraph V}
    (hT : T.IsAcyclic) {S : Finset (Vertex V)} (hS : S.card=3)
    (hmiss : a∉S ∨ b∉S) : triangleMultiplicity (graph T) S≤1 := by
  rcases hmiss with ha|hb
  · have hs : (tetrahedra (graph T)).filter (fun C => S⊆C)⊆{insert a S} := by
      intro C hC
      obtain ⟨hC,hSC⟩ := mem_filter.mp hC
      obtain ⟨hc,hcl⟩ := (mem_filter.mp hC).2
      have hsub : insert a S⊆C := insert_subset_iff.mpr
        ⟨(tetrahedron_hubs hT hc hcl).1,hSC⟩
      apply mem_singleton.mpr
      exact (eq_of_subset_of_card_le hsub (by rw [card_insert_of_notMem ha,hS,hc])).symm
    simpa only [triangleMultiplicity,card_singleton] using card_le_card hs
  · have hs : (tetrahedra (graph T)).filter (fun C => S⊆C)⊆{insert b S} := by
      intro C hC
      obtain ⟨hC,hSC⟩ := mem_filter.mp hC
      obtain ⟨hc,hcl⟩ := (mem_filter.mp hC).2
      have hsub : insert b S⊆C := insert_subset_iff.mpr
        ⟨(tetrahedron_hubs hT hc hcl).2,hSC⟩
      apply mem_singleton.mpr
      exact (eq_of_subset_of_card_le hsub (by rw [card_insert_of_notMem hb,hS,hc])).symm
    simpa only [triangleMultiplicity,card_singleton] using card_le_card hs

/-- For a forest, admissibility of the join is exactly the ordinary
maximum-degree bound three. -/
theorem admissible_iff_maxDegree {T : SimpleGraph V} (hT : T.IsAcyclic) :
    Admissible (graph T) ↔ T.maxDegree≤3 := by
  constructor
  · intro h
    apply T.maxDegree_le_of_forall_degree_le
    intro v
    have hc : (graph T).IsClique (core ({v} : Finset V)) :=
      (core_clique_iff T _).mpr (by simp [SimpleGraph.isClique_singleton])
    have hm := h (core {v}) (by simp) hc
    rwa [triangleMultiplicity_core_singleton hT v] at hm
  · intro h S hS hc
    by_cases ha : a∈S
    · by_cases hb : b∈S
      · have he := core_outer ha hb
        have hs : (outer S).card=1 := by
          have h := core_card (outer S)
          rw [he,hS] at h
          omega
        obtain ⟨v,hv⟩ := card_eq_one.mp hs
        rw [←he,hv,triangleMultiplicity_core_singleton hT v]
        exact (T.degree_le_maxDegree v).trans h
      · exact (triangleMultiplicity_le_one_of_missing_hub hT hS (Or.inr hb)).trans (by decide)
    · exact (triangleMultiplicity_le_one_of_missing_hub hT hS (Or.inl ha)).trans (by decide)

end GraphicalZonotopes.TreeJoin

end
end
end BundlePart127

section BundlePart128
/- Source: Papers/GraphicalZonotopes/PartialThreeTreeGraph.lean -/





@[expose] public section
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A partial 3-tree is a subgraph of a 3-tree on the same vertices. Every
graph on at most three vertices is included, as in the paper's convention. -/
def IsPartialThreeTree (G : SimpleGraph V) : Prop :=
  Fintype.card V ≤ 3 ∨ ∃ H : SimpleGraph V,IsThreeTree H ∧ G ≤ H

theorem edgeFamily_mono {G H : SimpleGraph V} (h : G ≤ H) :
    edgeFamily G ⊆ edgeFamily H := by
  intro C hC
  obtain ⟨hc,hcl⟩ := (mem_edgeFamily G C).mp hC
  exact (mem_edgeFamily H C).mpr ⟨hc,fun u hu v hv huv => h (hcl u hu v hv huv)⟩

theorem graph_eq_of_edgeFamily_eq {G H : SimpleGraph V}
    (h : edgeFamily G = edgeFamily H) : G = H := by
  ext u v
  by_cases huv : u = v
  · subst v
    simp
  · rw [← pair_mem_edgeFamily G huv,← pair_mem_edgeFamily H huv,h]

theorem graph_eq_of_le_card_edges {G H : SimpleGraph V} (h : G ≤ H)
    (hc : (edgeFamily H).card ≤ (edgeFamily G).card) : G = H :=
  graph_eq_of_edgeFamily_eq (eq_of_subset_of_card_le (edgeFamily_mono h) hc)

theorem inducedOn_mono {G H : SimpleGraph V} (h : G ≤ H) (U : Finset V) :
    inducedOn G U ≤ inducedOn H U := by
  intro u v huv
  exact ⟨h huv.1,huv.2⟩

theorem inducedOn_le (G : SimpleGraph V) (U : Finset V) : inducedOn G U ≤ G :=
  fun _ _ h => h.1

theorem edgeFamily_inducedOn_subset (G : SimpleGraph V) (U : Finset V) :
    edgeFamily (inducedOn G U) ⊆ U.powersetCard 2 := by
  intro C hC
  obtain ⟨hc,hcl⟩ := (mem_edgeFamily _ C).mp hC
  apply mem_powersetCard.mpr
  refine ⟨?_,hc⟩
  intro u hu
  obtain ⟨v,hv,hvu⟩ := exists_mem_ne (by omega : 1 < C.card) u
  exact (hcl u hu v hv (Ne.symm hvu)).2.1

theorem induced_edge_count_le_choose (G : SimpleGraph V) (U : Finset V) :
    (edgeFamily (inducedOn G U)).card ≤ U.card.choose 2 := by
  simpa only [card_powersetCard] using card_le_card (edgeFamily_inducedOn_subset G U)

theorem inducedOn_attachment_of_not_mem (G : SimpleGraph V) (u : V)
    (T U : Finset V) (hu : u ∉ U) :
    inducedOn (G ⊔ attachmentStar u T) U = inducedOn G U := by
  ext v w
  constructor
  · rintro ⟨h,hv,hw⟩
    rcases h with h | h
    · exact ⟨h,hv,hw⟩
    · rcases h.2 with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> contradiction
  · rintro ⟨h,hv,hw⟩
    exact ⟨Or.inl h,hv,hw⟩

/-- Every induced subgraph of a 3-tree satisfies the sharp partial-3-tree
edge bound. The proof includes arbitrary subsets, not merely construction
prefixes, which is essential for the support classification. -/
theorem ThreeTreeOn.induced_edge_bound {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (U : Finset V) (hUS : U ⊆ S) (hU : 3 ≤ U.card) :
    (edgeFamily (inducedOn G U)).card ≤ 3*U.card-6 := by
  classical
  induction h generalizing U with
  | tetrahedron C hC =>
    have hcard := card_le_card hUS
    have hb := induced_edge_count_le_choose (cliqueGraph C) U
    have hu : U.card = 3 ∨ U.card = 4 := by omega
    rcases hu with hu | hu <;> rw [hu] at hb ⊢ <;> norm_num at hb ⊢ <;> exact hb
  | @attach S G h u hu T hT hTS hcl ih =>
    by_cases hc : U.card = 3
    · have hb := induced_edge_count_le_choose (G ⊔ attachmentStar u T) U
      rw [hc] at hb ⊢
      norm_num at hb ⊢
      exact hb
    · by_cases huU : u ∈ U
      · have heU : U = insert u (U.erase u) := (insert_erase huU).symm
        have hsmall : U.erase u ⊆ S := by
          intro v hv
          exact (mem_insert.mp (hUS (mem_of_mem_erase hv))).resolve_left (ne_of_mem_erase hv)
        have hcard : (U.erase u).card = U.card-1 := card_erase_of_mem huU
        have hprev := ih (U.erase u) hsmall (by omega)
        have hsub : earlierNeighbors (G ⊔ attachmentStar u T) (U.erase u) u ⊆ T := by
          intro v hv
          exact (attached_vertex_adj_iff h hu hTS v).mp
            ((mem_earlierNeighbors _ _ _ _).mp hv).2
        have hnb := card_le_card hsub
        rw [hT] at hnb
        rw [heU,induced_edge_count_insert _ _ _ (notMem_erase _ _)]
        rw [inducedOn_attachment_of_not_mem _ _ _ _ (notMem_erase _ _)]
        have hIns : (insert u (U.erase u)).card = U.card := by rw [insert_erase huU]
        omega
      · have hsmall : U ⊆ S := by
          intro v hv
          exact (mem_insert.mp (hUS hv)).resolve_left (fun he => huU (he ▸ hv))
        rw [inducedOn_attachment_of_not_mem _ _ _ _ huU]
        exact ih U hsmall hU

theorem IsPartialThreeTree.induced_edge_bound {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) (U : Finset V) (hU : 3 ≤ U.card) :
    (edgeFamily (inducedOn G U)).card ≤ 3*U.card-6 := by
  rcases hG with hsmall | ⟨H,hH,hGH⟩
  · have hc : U.card = 3 := by
      have hcard := card_le_card (subset_univ U)
      simp only [card_univ] at hcard
      omega
    have hb := induced_edge_count_le_choose G U
    rw [hc] at hb ⊢
    norm_num at hb ⊢
    exact hb
  · exact (card_le_card (edgeFamily_mono (inducedOn_mono hGH U))).trans
      (hH.induced_edge_bound U (subset_univ _) hU)

theorem IsPartialThreeTree.cliqueFree_five {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) : G.CliqueFree 5 := by
  intro C hC
  rcases hG with hsmall | ⟨H,hH,hGH⟩
  · have hc := card_le_card (subset_univ C)
    rw [hC.card_eq,card_univ] at hc
    omega
  · exact hH.cliqueFree_five C ⟨fun u hu v hv huv => hGH (hC.isClique hu hv huv),hC.card_eq⟩

/-- A triangle-connected tetrahedral family in a partial 3-tree has no
extra ambient edges on its vertices and is itself an induced 3-tree. -/
theorem IsPartialThreeTree.connected_family_threeTree {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) (F : Finset (Finset V)) (hne : F.Nonempty)
    (hcl : ∀ C ∈ F,C.card = 4 ∧ G.IsClique C)
    (hconn : (tetrahedronGraph F).Preconnected) :
    ThreeTreeOn (F.biUnion id) (inducedOn G (F.biUnion id)) := by
  have hg := tetrahedralGrowth_of_connected_family G F hne hcl hconn
  have hu := hg.card_ge_four
  obtain ⟨hl,he⟩ := hg.edge_bound_and_equality
  apply he
  exact le_antisymm (hG.induced_edge_bound _ (by omega)) hl

end GraphicalZonotopes

end
end
end BundlePart128

section BundlePart129
/- Source: Papers/GraphicalZonotopes/ThreeTreeInducedEquality.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem ThreeTreeOn.induced_self {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : inducedOn G S = G := by
  ext u v
  exact ⟨fun huv => huv.1,fun huv => ⟨huv,h.edges_supported huv⟩⟩

theorem ThreeTreeOn.edgeFamily_card {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : (edgeFamily G).card = 3*S.card-6 := by
  induction h with
  | tetrahedron C hC =>
    rw [edgeFamily_cliqueGraph,card_powersetCard,hC]
    decide
  | @attach S G h u hu T hT hTS hc ih =>
    have hn : earlierNeighbors (G ⊔ attachmentStar u T) S u = T := by
      ext v
      rw [mem_earlierNeighbors]
      constructor
      · exact fun hv => (attached_vertex_adj_iff h hu hTS v).mp hv.2
      · exact fun hv => ⟨hTS hv,(attached_vertex_adj_iff h hu hTS v).mpr hv⟩
    have ha := ThreeTreeOn.attach h u hu T hT hTS hc
    rw [← ha.induced_self,induced_edge_count_insert _ _ _ hu,
      inducedOn_attachment_of_not_mem _ _ _ _ hu,h.induced_self,ih,hn,hT,
      card_insert_of_notMem hu]
    have hs := h.active_card_ge_four
    omega

theorem clique_of_induced_edge_count_eq_choose {G : SimpleGraph V} {U : Finset V}
    (h : (edgeFamily (inducedOn G U)).card = U.card.choose 2) : G.IsClique U := by
  have he : edgeFamily (inducedOn G U) = U.powersetCard 2 := by
    apply eq_of_subset_of_card_le (edgeFamily_inducedOn_subset G U)
    simpa only [card_powersetCard] using h.ge
  intro u hu v hv huv
  change u ∈ U at hu
  change v ∈ U at hv
  have hp : ({u,v} : Finset V) ∈ U.powersetCard 2 :=
    mem_powersetCard.mpr ⟨by simpa only [insert_subset_iff,singleton_subset_iff] using And.intro hu hv,
      card_pair huv⟩
  rw [← he] at hp
  exact ((pair_mem_edgeFamily _ huv).mp hp).1

/-- Every induced subgraph meeting the maximal partial-three-tree edge
count is itself a three-tree. The statement includes arbitrary vertex
subsets, not only initial segments of a chosen construction. -/
theorem ThreeTreeOn.induced_equality {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (U : Finset V) (hUS : U ⊆ S) (hU : 4 ≤ U.card)
    (he : (edgeFamily (inducedOn G U)).card = 3*U.card-6) :
    ThreeTreeOn U (inducedOn G U) := by
  induction h generalizing U with
  | tetrahedron C hC =>
    have hcard := card_le_card hUS
    have hU4 : U.card = 4 := by omega
    have hcl : (cliqueGraph C).IsClique U :=
      clique_of_induced_edge_count_eq_choose (G := cliqueGraph C) (U := U)
        (by norm_num [hU4,Nat.choose] at he ⊢; exact he)
    rw [inducedOn_clique hcl]
    exact ThreeTreeOn.tetrahedron U hU4
  | @attach S G h u hu T hT hTS hc ih =>
    by_cases hU4 : U.card = 4
    · have hcl : (G ⊔ attachmentStar u T).IsClique U :=
        clique_of_induced_edge_count_eq_choose (G := G ⊔ attachmentStar u T) (U := U)
          (by norm_num [hU4,Nat.choose] at he ⊢; exact he)
      rw [inducedOn_clique hcl]
      exact ThreeTreeOn.tetrahedron U hU4
    · by_cases huU : u ∈ U
      · let W := U.erase u
        have huW : u ∉ W := notMem_erase _ _
        have hWsub : W ⊆ S := by
          intro v hv
          exact (mem_insert.mp (hUS (mem_of_mem_erase hv))).resolve_left (ne_of_mem_erase hv)
        have hWcard : W.card = U.card-1 := card_erase_of_mem huU
        have hW4 : 4 ≤ W.card := by omega
        have hWU : insert u W = U := insert_erase huU
        have hbound := h.induced_edge_bound W hWsub (by omega)
        let N := earlierNeighbors (G ⊔ attachmentStar u T) W u
        have hNT : N ⊆ T := by
          intro v hv
          exact (attached_vertex_adj_iff h hu hTS v).mp
            ((mem_earlierNeighbors _ _ _ _).mp hv).2
        have hN3 : N.card ≤ 3 := by simpa only [hT] using card_le_card hNT
        have hsplit : (edgeFamily (inducedOn (G ⊔ attachmentStar u T) U)).card =
            (edgeFamily (inducedOn G W)).card + N.card := by
          rw [← hWU,induced_edge_count_insert _ _ _ huW,
            inducedOn_attachment_of_not_mem _ _ _ _ huW]
        have hEq : (edgeFamily (inducedOn G W)).card = 3*W.card-6 := by omega
        have hNcard : N.card = 3 := by omega
        have hNT' : N = T := eq_of_subset_of_card_le hNT (by omega)
        have hTW : T ⊆ W := by
          rw [← hNT']
          exact fun v hv => ((mem_earlierNeighbors _ _ _ _).mp hv).1
        have hold := ih W hWsub hW4 hEq
        have hnew := ThreeTreeOn.attach hold u huW T hT hTW
          (fun v hv w hw hvw => ⟨hc hv hw hvw,hTW hv,hTW hw⟩)
        have hgraph : inducedOn (G ⊔ attachmentStar u T) U =
            inducedOn G W ⊔ attachmentStar u T := by
          rw [← hWU,inducedOn_insert_eq_attach _ W T u huW hNT',
            inducedOn_attachment_of_not_mem _ _ _ _ huW]
        rw [hgraph,← hWU]
        exact hnew
      · have hsmall : U ⊆ S := by
          intro v hv
          exact (mem_insert.mp (hUS hv)).resolve_left (fun he => huU (he ▸ hv))
        rw [inducedOn_attachment_of_not_mem _ _ _ _ huU] at he ⊢
        exact ih U hsmall hU he

end GraphicalZonotopes

end
end
end BundlePart129

section BundlePart130
/- Source: Papers/GraphicalZonotopes/TreeJoinInduced.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.TreeJoin
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual induced graph on U, with the canonical finite subtype U as
its vertex type. Adjacency is exactly ambient adjacency of the two values. -/
def subtree (T : SimpleGraph V) (U : Finset V) : SimpleGraph U :=
  T.comap (Subtype.val : U → V)

theorem subtree_eq_induce (T : SimpleGraph V) (U : Finset V) :
    subtree T U=T.induce (U : Set V) := rfl

def subtreeUnivIso (T : SimpleGraph V) : subtree T univ ≃g T where
  toFun := Subtype.val
  invFun := fun v => ⟨v,mem_univ v⟩
  left_inv := by intro v; rfl
  right_inv := by intro v; rfl
  map_rel_iff' := by intros; rfl

def inclusion (U : Finset V) : Vertex U ↪ Vertex V :=
  (Function.Embedding.sumMap
    (Function.Embedding.sumMap ⟨Subtype.val,Subtype.val_injective⟩
      (Function.Embedding.refl (Fin 1))) (Function.Embedding.refl (Fin 1)))

@[simp] theorem inclusion_a (U : Finset V) : inclusion U a=a := rfl
@[simp] theorem inclusion_b (U : Finset V) : inclusion U b=b := rfl
@[simp] theorem inclusion_old (U : Finset V) (v : U) : inclusion U (old v)=old v.1 := rfl

theorem inclusion_mem_core (U : Finset V) (x : Vertex U) : inclusion U x∈core U := by
  rcases vertex_cases x with rfl|rfl|⟨v,rfl⟩
  · simp
  · simp
  · simpa using v.property

theorem mem_core_range (U : Finset V) {x : Vertex V} (hx : x∈core U) :
    x∈Set.range (inclusion U) := by
  rcases vertex_cases x with rfl|rfl|⟨v,rfl⟩
  · exact ⟨a,rfl⟩
  · exact ⟨b,rfl⟩
  · exact ⟨old ⟨v,(old_mem_core U v).mp hx⟩,rfl⟩

theorem univ_map_inclusion (U : Finset V) : univ.map (inclusion U)=core U := by
  ext x
  constructor
  · intro hx
    obtain ⟨v,hv,rfl⟩ := mem_map.mp hx
    exact inclusion_mem_core U v
  · intro hx
    obtain ⟨v,rfl⟩ := mem_core_range U hx
    exact mem_map.mpr ⟨v,mem_univ _,rfl⟩

theorem inclusion_adj (T : SimpleGraph V) (U : Finset V) (x y : Vertex U) :
    (graph (subtree T U)).Adj x y ↔
      (graph T).Adj (inclusion U x) (inclusion U y) := by
  rcases vertex_cases x with rfl|rfl|⟨u,rfl⟩ <;>
    rcases vertex_cases y with rfl|rfl|⟨v,rfl⟩ <;>
    simp [graph,SingleVertexGraph.graph,inclusion,old,a,b,subtree]

theorem map_induced (T : SimpleGraph V) (U : Finset V) :
    (graph (subtree T U)).map (inclusion U)=inducedOn (graph T) (core U) := by
  ext x y
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨u,v,huv,rfl,rfl⟩
    exact ⟨(inclusion_adj T U u v).mp huv,inclusion_mem_core U u,inclusion_mem_core U v⟩
  · rintro ⟨hxy,hx,hy⟩
    obtain ⟨u,rfl⟩ := mem_core_range U hx
    obtain ⟨v,rfl⟩ := mem_core_range U hy
    exact ⟨u,v,(inclusion_adj T U u v).mpr hxy,rfl,rfl⟩

theorem comap_induced (T : SimpleGraph V) (U : Finset V) :
    (inducedOn (graph T) (core U)).comap (inclusion U)=graph (subtree T U) := by
  ext x y
  change ((graph T).Adj (inclusion U x) (inclusion U y) ∧
    inclusion U x∈core U ∧ inclusion U y∈core U) ↔ _
  simp only [inclusion_mem_core,and_true]
  exact (inclusion_adj T U x y).symm

theorem forest_tree_of_join_threeTree {T : SimpleGraph V} (hT : T.IsAcyclic)
    (hG : IsThreeTree (graph T)) : T.IsTree := by
  have hn := hG.active_card_ge_four
  simp only [card_univ,Vertex,Fintype.card_sum,Fintype.card_fin] at hn
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  apply forest_isTree_of_card hT
  have he := hG.edgeFamily_card
  rw [edgeFamily_card] at he
  simp only [card_univ,Vertex,Fintype.card_sum,Fintype.card_fin] at he
  have hcount : (edgeFamily T).card=T.edgeFinset.card := by
    rw [edgeFamily_eq_image_edgeFinset,card_image_of_injective _ sym2_toFinset_injective]
  omega

theorem induced_core_threeTree_iff {T : SimpleGraph V} (hT : T.IsAcyclic)
    (U : Finset V) (hn : 2≤ U.card) :
    ThreeTreeOn (core U) (inducedOn (graph T) (core U)) ↔
      (subtree T U).IsTree := by
  constructor
  · intro h
    have hh := h.comap (inclusion U) (fun _ hv => mem_core_range U hv)
    have hset : SetFunctionEmbedding.pullSet (inclusion U) (core U)=univ := by
      ext x
      simp [SetFunctionEmbedding.mem_pullSet,inclusion_mem_core]
    rw [hset,comap_induced] at hh
    exact forest_tree_of_join_threeTree (hT.induce _) hh
  · intro h
    have hg := (isThreeTree h (by simpa only [Fintype.card_coe] using hn)).map (inclusion U)
    rwa [univ_map_inclusion,map_induced] at hg

theorem induced_core_admissible_iff {T : SimpleGraph V} (hT : T.IsAcyclic)
    (U : Finset V) :
    Admissible (inducedOn (graph T) (core U)) ↔
      (subtree T U).maxDegree≤3 := by
  rw [←map_induced]
  constructor
  · intro h
    exact (admissible_iff_maxDegree (hT.induce _)).mp (Admissible.of_map (inclusion U) h)
  · intro h
    exact ((admissible_iff_maxDegree (hT.induce _)).mpr h).map (inclusion U)

/-- Every induced admissible 3-tree in the two-hub join consists of both
hubs together with a genuine connected induced subtree of maximum degree
at most three. The converse is proved by the preceding two equivalences. -/
theorem induced_admissible_subtree {T : SimpleGraph V} (hT : T.IsAcyclic)
    {S : Finset (Vertex V)} (hS : ThreeTreeOn S (inducedOn (graph T) S))
    (hA : Admissible (inducedOn (graph T) S)) :
    ∃ U : Finset V,S=core U ∧ 2≤ U.card ∧
      (subtree T U).IsTree ∧ (subtree T U).maxDegree≤3 := by
  obtain ⟨C,hC⟩ := hS.tetrahedra_nonempty
  obtain ⟨hc,hcl⟩ := (mem_tetrahedra_iff _ C).mp hC
  have hcl' : (graph T).IsClique C := fun u hu v hv huv => (hcl hu hv huv).1
  obtain ⟨ha,hb⟩ := tetrahedron_hubs hT hc hcl'
  have hCS := hS.clique_subset_active (by omega : 2≤ C.card) hcl
  have he := core_outer (hCS ha) (hCS hb)
  have hn : 2≤(outer S).card := by
    have hcard := hS.active_card_ge_four
    have h := core_card (outer S)
    rw [he] at h
    omega
  refine ⟨outer S,he.symm,hn,?_,?_⟩
  · apply (induced_core_threeTree_iff hT (outer S) hn).mp
    simpa only [he] using hS
  · apply (induced_core_admissible_iff hT (outer S)).mp
    simpa only [he] using hA

end GraphicalZonotopes.TreeJoin

end
end
end BundlePart130

section BundlePart131
/- Source: Papers/GraphicalZonotopes/TreeJoinSubtrees.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.TreeJoin
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A connected subgraph of a forest already contains every ambient edge
between its vertices. Thus the word "subtree" does not restrict s₃ to a
smaller class when we represent it as an induced graph. -/
theorem connected_subgraph_eq {W : Type*} {G H : SimpleGraph W}
    (hG : G.IsAcyclic) (hH : H.Connected) (hHG : H≤ G) : H=G := by
  have htree : G.IsTree := ⟨hH.mono hHG,hG⟩
  have hmin := SimpleGraph.isTree_iff_minimal_connected.mp htree
  exact le_antisymm hHG (hmin.2 hH hHG)

theorem induced_subcubic_iff_subtree {T : SimpleGraph V} (hT : T.IsAcyclic)
    (U : Finset V) :
    ((subtree T U).IsTree ∧ (subtree T U).maxDegree≤3) ↔
      ∃ H : SimpleGraph U,H≤ subtree T U ∧ H.IsTree ∧ H.maxDegree≤3 := by
  constructor
  · rintro ⟨ht,hd⟩
    exact ⟨_,le_rfl,ht,hd⟩
  · rintro ⟨H,hH,ht,hd⟩
    have he := connected_subgraph_eq (hT.induce _) ht.connected hH
    subst H
    exact ⟨ht,hd⟩

def subcubicSubtreeSets (T : SimpleGraph V) : Finset (Finset V) :=
  univ.filter (fun U => (subtree T U).IsTree ∧
    (subtree T U).maxDegree≤3)

/-- The largest number of vertices in a nonempty connected subtree with
maximum degree at most three. `induced_subcubic_iff_subtree` proves that on
a forest this is exactly the maximum over all connected subgraphs. -/
def s3 (T : SimpleGraph V) : ℕ := (subcubicSubtreeSets T).sup Finset.card

theorem subtree_card_le_s3 {T : SimpleGraph V} {U : Finset V}
    (ht : (subtree T U).IsTree) (hd : (subtree T U).maxDegree≤3) :
    U.card≤ s3 T := by
  apply le_sup
  exact mem_filter.mpr ⟨mem_univ _,ht,hd⟩

theorem singleton_subtree (T : SimpleGraph V) (v : V) :
    ({v} : Finset V)∈subcubicSubtreeSets T := by
  letI : Nonempty ({v} : Finset V) := ⟨⟨v,by simp⟩⟩
  letI : Subsingleton ({v} : Finset V) := ⟨by
    intro x y
    apply Subtype.ext
    have hx : x.1=v := mem_singleton.mp x.2
    have hy : y.1=v := mem_singleton.mp y.2
    exact hx.trans hy.symm⟩
  exact mem_filter.mpr ⟨mem_univ _,SimpleGraph.IsTree.of_subsingleton,by simp⟩

theorem s3_pos (T : SimpleGraph V) [Nonempty V] : 1≤ s3 T := by
  obtain ⟨v⟩ := (inferInstance : Nonempty V)
  have h := le_sup (s := subcubicSubtreeSets T) (f := Finset.card) (singleton_subtree T v)
  simpa only [card_singleton,s3] using h

theorem s3_le_card (T : SimpleGraph V) : s3 T≤ Fintype.card V := by
  apply Finset.sup_le_iff.mpr
  intro U hU
  exact card_le_univ U

theorem s3_attained (T : SimpleGraph V) [Nonempty V] :
    ∃ U : Finset V,(subtree T U).IsTree ∧
      (subtree T U).maxDegree≤3 ∧ U.card=s3 T := by
  obtain ⟨v⟩ := (inferInstance : Nonempty V)
  obtain ⟨U,hU,hmax⟩ := (subcubicSubtreeSets T).exists_max_image Finset.card
    ⟨{v},singleton_subtree T v⟩
  obtain ⟨ht,hd⟩ := (mem_filter.mp hU).2
  exact ⟨U,ht,hd,le_antisymm (subtree_card_le_s3 ht hd) (Finset.sup_le_iff.mpr hmax)⟩

theorem s3_eq_card_iff {T : SimpleGraph V} (hT : T.IsTree) :
    s3 T=Fintype.card V ↔ T.maxDegree≤3 := by
  letI : Nonempty V := hT.connected.nonempty
  have hdeg : (subtree T univ).maxDegree=T.maxDegree := by
    exact (subtreeUnivIso T).maxDegree_eq
  constructor
  · intro he
    obtain ⟨U,ht,hd,hcard⟩ := s3_attained T
    have hU : U=univ := eq_univ_of_card U (hcard.trans he)
    subst U
    rwa [hdeg] at hd
  · intro hd
    apply le_antisymm (s3_le_card T)
    have ht : (subtree T univ).IsTree := by
      exact (subtreeUnivIso T).isTree_iff.mpr hT
    have h := subtree_card_le_s3 ht (by rwa [hdeg])
    simpa only [card_univ] using h

end GraphicalZonotopes.TreeJoin

end
end
end BundlePart131

section BundlePart132
/- Source: Papers/GraphicalZonotopes/SupportDimensionBound.lean -/







@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Removing inactive coordinates gives the full support-sensitive affine
dimension bound, including the empty support. -/
theorem finrank_vectorSpan_le_support {z : SetFunction V} {S : Finset V}
    (hn : TranslationNormalized z) (hs : Supermodular z) (hdep : DependsOn z S) :
    Module.finrank ℝ (vectorSpan ℝ (basePolytope z))≤ S.card-1 := by
  let W:=vectorSpan ℝ (basePolytope z)
  have hzero : ∀ (x : W) v,v∉S → x.1 v=0 := by
    intro x v hv
    exact vectorSpan_le_evaluation_ker_of_dependsOn hn hs hdep hv x.2
  by_cases hS : S.Nonempty
  · let r : W →ₗ[ℝ] (S → ℝ) := {
      toFun x v:=x.1 v.1
      map_add' _ _:=rfl
      map_smul' _ _:=rfl }
    have hr : ∀ x : W,r x∈(totalLinear (V:=S)).ker := by
      intro x
      change (∑ v : S,x.1 v.1)=0
      rw [Finset.sum_coe_sort]
      have htotal : (∑ v : V,x.1 v)=0 :=
        vectorSpan_basePolytope_le_total_ker (basePolytope_nonempty hn.1 hs) x.2
      rw [← htotal]
      exact sum_subset (subset_univ S) (fun v hv hvS => hzero x v hvS)
    let q:=r.codRestrict (totalLinear (V:=S)).ker hr
    have hq : Function.Injective q := by
      intro x y hxy
      apply Subtype.ext
      funext v
      by_cases hv : v∈S
      · exact congrArg (fun t : (totalLinear (V:=S)).ker => t.1 ⟨v,hv⟩) hxy
      · rw [hzero x v hv,hzero y v hv]
    have hb:=LinearMap.finrank_le_finrank_of_injective hq
    obtain ⟨v,hv⟩:=hS
    rw [finrank_total_ker_fintype (⟨v,hv⟩ : S),Fintype.card_coe] at hb
    exact hb
  · have hW : W=⊥ := by
      apply le_antisymm
      · intro x hx
        change x=0
        funext v
        exact hzero ⟨x,hx⟩ v (fun hv => hS ⟨v,hv⟩)
      · exact bot_le
    change Module.finrank ℝ W≤ _
    rw [hW,finrank_bot]
    exact Nat.zero_le _

namespace Separator
variable {J : Type*} [Fintype J] [DecidableEq J]
variable {G : SimpleGraph V} {B : Finset V} {A : J → Finset V}

/-- The active separator blocks contain the complete Möbius support, even
when some of the original private branches are zero. -/
theorem dependsOn_active_branches (h : Partition G B A) (z : graphicalFunctionSpace G) :
    DependsOn z.1 (B ∪ univ.biUnion (fun j : Gluing.ActiveBranch
      (((functionEquiv h).symm z).2) => A j.1)) := by
  classical
  let f:=((functionEquiv h).symm z).2
  let T:=B ∪ univ.biUnion (fun j : Gluing.ActiveBranch f => A j.1)
  have hy:=(mobius_cliqueSupported_iff G z.1).mpr z.2
  rw [← zeta_mobius z.1]
  apply zeta_dependsOn
  intro C hCT
  by_cases hcl : IsCliqueCoordinate G C
  · have hCB : ¬C⊆B:=fun hc => hCT (hc.trans subset_union_left)
    obtain ⟨j,hCj,huniq⟩:=h.clique_unique_branch ⟨C,hcl⟩ hCB
    let D : privateIndex G B A j:=⟨⟨C,hcl⟩,hCB,hCj⟩
    by_cases hf : f j=0
    · have hh:=congrFun hf D
      exact hh
    · apply False.elim
      apply hCT
      intro v hv
      rcases mem_union.mp (hCj hv) with hvB | hvA
      · exact mem_union_left _ hvB
      · exact mem_union_right _ (mem_biUnion.mpr ⟨⟨j,hf⟩,mem_univ _,hvA⟩)
  · exact coefficient_zero_of_not_clique hy C hcl

/-- For singleton private branches, the number of active branches controls
the genuine affine dimension. This does not assume full ambient dimension. -/
theorem finrank_le_boundary_add_active (h : Partition G B A)
    (hA : ∀ j,(A j).card≤1) (z : graphicalFunctionSpace G) (hz : Supermodular z.1) :
    Module.finrank ℝ (vectorSpan ℝ (basePolytope z.1))≤
      B.card+Fintype.card (Gluing.ActiveBranch (((functionEquiv h).symm z).2))-1 := by
  classical
  let f:=((functionEquiv h).symm z).2
  have hb:=finrank_vectorSpan_le_support z.2.1 hz (dependsOn_active_branches h z)
  have hu : (univ.biUnion (fun j : Gluing.ActiveBranch f => A j.1)).card≤
      Fintype.card (Gluing.ActiveBranch f) := by
    apply card_biUnion_le.trans
    calc
      (∑ j : Gluing.ActiveBranch f,(A j.1).card)≤∑ j : Gluing.ActiveBranch f,1 :=
        sum_le_sum (fun j hj => hA j.1)
      _=Fintype.card (Gluing.ActiveBranch f):=by simp
  have hc:=card_union_le B (univ.biUnion (fun j : Gluing.ActiveBranch f => A j.1))
  exact hb.trans (Nat.sub_le_sub_right (hc.trans (Nat.add_le_add_left hu B.card)) 1)

end Separator
end GraphicalZonotopes

end
end
end BundlePart132

section BundlePart133
/- Source: Papers/GraphicalZonotopes/WeakSummandReduction.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every actual weak summand has its genuine normalized graphical support
function, preserving affine dimension. Points are handled explicitly rather
than excluded by an extra hypothesis. -/
theorem weak_summand_extreme_or_zero {G : SimpleGraph V} {Q : Set (V → ℝ)}
    (hQ : IsFinitePolytope Q) (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    ∃ z : graphicalFunctionSpace G,Supermodular z.1 ∧
      (z.1=0 ∨ ExtremeSupermodular z.1) ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=Module.finrank ℝ (vectorSpan ℝ (basePolytope z.1)) := by
  obtain ⟨c,hc,R,hR,hRc,hnR,hQR⟩:=hw
  have hTn : Normalized (c • graphFunction G) := by
    change c*graphFunction G ∅=0
    rw [graphFunction_normalized,mul_zero]
  have hTs:=(graphFunction_supermodular G).smul hc.le
  have hbase : Q+R=basePolytope (c • graphFunction G) := by
    rw [basePolytope_smul (graphFunction_normalized G) (graphFunction_supermodular G) hc.le,
      baseGraphFunction_eq_graphicalZonotope]
    exact hQR
  let f:=lowerSupport Q
  have hfn : Normalized f:=lowerSupport_normalized hQ.compact hi.1
  have hfs : Supermodular f:=summand_lowerSupport_supermodular hTn hTs
    hQ.compact hR hi.1 hnR hbase
  have hbody : Q=basePolytope f:=summand_eq_basePolytope hTn hTs
    hQ.compact hR hQ.convex hi.1 hnR hbase
  have hgf : Graphical G f := by
    apply ((isMinkowskiSummand_graphical_iff hfn hfs hc.le).mp ?_).1
    rw [← hbody]
    exact ⟨R,hR,hRc,hnR,hQR⟩
  have hgn : Graphical G (normalize f) := by
    intro u v huv hnon S hu hv
    rw [delta_normalize f huv hu hv]
    exact hgf u v huv hnon S hu hv
  refine ⟨⟨normalize f,normalize_translationNormalized hfn,hgn⟩,hfs.normalize,?_,?_⟩
  · by_cases hz:normalize f=0
    · exact Or.inl hz
    · exact Or.inr (MinkowskiIndecomposable.extremeSupermodular_normalize
        hfn hfs hz (hbody ▸ hi))
  · rw [vectorSpan_basePolytope_normalize,← hbody]

theorem weak_summand_dimension_le {G : SimpleGraph V} {Q : Set (V → ℝ)}
    (hQ : IsFinitePolytope Q) (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    Module.finrank ℝ (vectorSpan ℝ Q)≤ Fintype.card V-1 := by
  obtain ⟨z,hz,he,hd⟩:=weak_summand_extreme_or_zero hQ hi hw
  rw [hd]
  simpa only [card_univ] using finrank_vectorSpan_le_support z.2.1 hz
    (show DependsOn z.1 univ from fun T => by rw [inter_univ])

/-- Every actual witness contributes its real affine dimension to the
paper's maximum invariant; boundedness follows from ambient geometry. -/
theorem dimension_le_maximum {G : SimpleGraph V} {Q : Set (V → ℝ)}
    (hQ : IsFinitePolytope Q) (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    Module.finrank ℝ (vectorSpan ℝ Q)≤ maximumIndecomposableDimension G := by
  apply le_csSup
  · refine ⟨Fintype.card V-1,?_⟩
    rintro d ⟨R,hR,hr,hs,hd⟩
    rw [← hd]
    exact weak_summand_dimension_le hR hr hs
  · exact ⟨Q,hQ,hi,hw,rfl⟩

theorem Graphical.mono_graph {G H : SimpleGraph V} {z : SetFunction V}
    (hHG : H≤ G) (hz : Graphical H z) : Graphical G z := by
  intro u v huv hnon S hu hv
  exact hz u v huv (fun h => hnon (hHG h)) S hu hv

end GraphicalZonotopes

end
end
end BundlePart133

section BundlePart134
/- Source: Papers/GraphicalZonotopes/PartialThreeTreeSupport.lean -/







@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators Pointwise
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [LinearOrder V]

namespace RefinedTriangleComponents
open PositiveDecomposition

private theorem adjusted_zero_function' : adjusted (0 : SetFunction V) = 0 := by
  have ha : allocation (0 : SetFunction V) = 0 := by
    funext C
    by_cases hC : C.card = 2
    · obtain ⟨u,v,huv,rfl⟩ := card_eq_two.mp hC
      rw [allocation_pair _ huv]
      have hm : minimumSlack (0 : SetFunction V) u v = 0 :=
        minimumSlack_eq_zero (by intros; simp [delta])
      simp [hm]
    · exact allocation_zero _ hC
  rw [adjusted,ha]
  change 0+zetaLinear 0=0
  simp

/-- Positive decomposition also identifies the unique interacting clique
class without assuming full ambient dimension. The dimension hypothesis
rules out the segment and isolated-triangle pieces. -/
theorem extreme_has_component_of_dimension_ge_three {z : SetFunction V}
    (hz : ExtremeSupermodular z)
    (hdim : 3 ≤ Module.finrank ℝ (vectorSpan ℝ (basePolytope z)))
    (hdegree : ∀ C,mobius z C ≠ 0 → C.card ≤ 4) :
    ∃ a : Component (mobius z),∃ t : ℝ,0 < t ∧
      adjusted (higherClass (mobius z) (classOf (mobius z)) (Sum.inl a)) = t • z ∧
      DependsOn z ((family (mobius z)).biUnion id) := by
  classical
  let y := mobius z
  have hy : y ∅ = 0 ∧ ∀ v,y {v} = 0 :=
    (zeta_normalized_iff y).mp (by simpa [y] using hz.1)
  obtain ⟨hp,he⟩ := pieces_positive hy hdegree (by simpa [y] using hz.2.1)
  have hez : (∑ i,pieces y i) = z := by simpa [y] using he
  have hex : ∃ i,pieces y i ≠ 0 := by
    by_contra h
    push_neg at h
    have hzero : (∑ i,pieces y i) = 0 := sum_eq_zero (fun i _ => h i)
    exact hz.2.2.1 (hez.symm.trans hzero)
  obtain ⟨i,hi⟩ := hex
  obtain ⟨t,ht,hscale⟩ := hz.finite_summand (pieces y)
    (fun i => (hp i).1) (fun i => (hp i).2) hez hi
  have hsupport : ∀ S,DependsOn (pieces y i) S → 4 ≤ S.card := by
    intro S hS
    rw [hscale] at hS
    have hb := finrank_vectorSpan_le_support hz.1 hz.2.1
      (DependsOn.of_smul (ne_of_gt ht) hS)
    omega
  cases i with
  | inr C =>
    have hC : C.card = 2 := by
      by_contra hnot
      have hzC := residual_zero y (higherClass y (classOf y)) hnot
      exact hi (by simp [pieces,hzC])
    have hdep : DependsOn (pieces y (Sum.inr C)) C := (setMonomial_dependsOn C).smul _
    have hc := hsupport C hdep
    omega
  | inl c =>
    cases c with
    | inr T =>
      have hT : T.card = 3 := by
        by_contra hnot
        have hzero := higher_right_zero_of_card_ne_three hdegree hnot
        exact hi (by simp only [y,pieces,Sum.elim_inl,hzero,adjusted_zero_function'])
      have hdep := PositiveDecomposition.DependsOn.adjusted
        (higher_right_dependsOn hdegree T)
      have hc := hsupport T hdep
      omega
    | inl a =>
      have hdep := PositiveDecomposition.DependsOn.adjusted
        (higher_left_dependsOn hdegree a)
      refine ⟨a,t,ht,hscale,?_⟩
      change DependsOn (pieces y (Sum.inl (Sum.inl a))) ((family y).biUnion id) at hdep
      rw [hscale] at hdep
      exact DependsOn.of_smul (ne_of_gt ht) hdep

/-- Corollary 4.4 in its full, possibly lower-dimensional form: the actual
edge directions are precisely the union of the nonzero tetrahedral
coefficients, and that family is connected through triangles. -/
theorem refined_support_of_dimension_ge_three {G : SimpleGraph V}
    (hG : G.CliqueFree 5) {z : SetFunction V} (hz : ExtremeSupermodular z)
    (hgraph : Graphical G z)
    (hdim : 3 ≤ Module.finrank ℝ (vectorSpan ℝ (basePolytope z))) :
    (family (mobius z)).Nonempty ∧
      (tetrahedronGraph (family (mobius z))).Preconnected ∧
      actualDirectionGraph (basePolytope z) = edgeGraph (mobius z) ∧
      DependsOn z ((family (mobius z)).biUnion id) := by
  classical
  let y := mobius z
  have hy : CliqueSupported G y := (mobius_cliqueSupported_iff G z).mpr ⟨hz.1,hgraph⟩
  have hdegree : ∀ C,y C ≠ 0 → C.card ≤ 4 := fun C hC => nonzero_card_le_four hG hy hC
  obtain ⟨a,t,ht,hscale,hdep⟩ := extreme_has_component_of_dimension_ge_three hz hdim hdegree
  have hcomp := same_component_of_positive_piece a (ne_of_gt ht)
    (by simpa only [zeta_mobius] using hscale)
  have hconnected : (tetrahedronGraph (family y)).Preconnected := by
    intro C D
    exact SimpleGraph.ConnectedComponent.exact ((hcomp C).trans (hcomp D).symm)
  have hne : (family y).Nonempty := by
    obtain ⟨C,hC⟩ := a.exists_rep
    exact ⟨C.1,C.2⟩
  refine ⟨hne,hconnected,?_,hdep⟩
  have hpiece : Graphical (edgeGraph y)
      (adjusted (higherClass y (classOf y) (Sum.inl a))) :=
    adjusted_graphical ((cliqueSupported_iff _ _).mp (left_coefficients_supported hdegree a)).2
  have hzedge : Graphical (edgeGraph y) z := by
    intro u v huv hnon S hu hv
    have h := hpiece u v huv hnon S hu hv
    rw [hscale,delta_smul] at h
    exact mul_left_cancel₀ (ne_of_gt ht) (by simpa using h)
  ext u v
  constructor
  · intro h
    exact actualRootEdge_of_graphical hz.1.1 hz.2.1 hzedge h
  · rintro ⟨huv,C,hC,hu,hv⟩
    exact actualRootEdge_of_nonzero_coefficient hz.1.1 hz.2.1
      ((mem_family y C).mp hC).2 huv hu hv

end RefinedTriangleComponents

open RefinedTriangleComponents

/-- Necessity in Corollary 6.6 on the actual active coordinate set. -/
theorem partial_threeTree_extreme_support {G : SimpleGraph V} (hG : IsPartialThreeTree G)
    {z : SetFunction V} (hz : ExtremeSupermodular z) (hg : Graphical G z)
    (hd : 3 ≤ Module.finrank ℝ (vectorSpan ℝ (basePolytope z))) :
    ∃ U : Finset V,4 ≤ U.card ∧
      actualDirectionGraph (basePolytope z) = inducedOn G U ∧
      ThreeTreeOn U (inducedOn G U) ∧ Admissible (inducedOn G U) ∧
      Module.finrank ℝ (vectorSpan ℝ (basePolytope z)) = U.card-1 := by
  classical
  let F := family (mobius z)
  let U := F.biUnion id
  obtain ⟨hne,hconn,hactual,hdep⟩ := refined_support_of_dimension_ge_three
    hG.cliqueFree_five hz hg hd
  have hy : CliqueSupported G (mobius z) := (mobius_cliqueSupported_iff G z).mpr ⟨hz.1,hg⟩
  have hcl : ∀ C ∈ F,C.card = 4 ∧ G.IsClique C := by
    intro C hC
    obtain ⟨hc,hn⟩ := (mem_family _ C).mp hC
    refine ⟨hc,?_⟩
    by_contra hnot
    exact hn (coefficient_zero_of_not_clique hy C (by rintro ⟨_,hh⟩; exact hnot hh))
  have htree := hG.connected_family_threeTree F hne hcl hconn
  have hU : 4 ≤ U.card := htree.active_card_ge_four
  let H := actualDirectionGraph (basePolytope z)
  have hHU : H ≤ inducedOn G U := by
    intro u v huv
    have he : (edgeGraph (mobius z)).Adj u v := by simpa only [H,hactual] using huv
    obtain ⟨_,C,hC,hu,hv⟩ := he
    exact ⟨actualRootEdge_of_graphical hz.1.1 hz.2.1 hg huv,
      mem_biUnion.mpr ⟨C,hC,hu⟩,mem_biUnion.mpr ⟨C,hC,hv⟩⟩
  have hclH : ∀ C ∈ F,C.card = 4 ∧ H.IsClique C := by
    intro C hC
    refine ⟨(mem_family _ C).mp hC |>.1,?_⟩
    rw [show H = edgeGraph (mobius z) from hactual]
    exact family_subset_edgeGraph_clique hC
  have hHg := tetrahedralGrowth_of_connected_family H F hne hclH hconn
  have hiH : inducedOn H U = H := by
    ext u v
    constructor
    · exact fun h => h.1
    · intro h
      exact ⟨h,(hHU h).2⟩
  have hlow := hHg.edge_bound_and_equality.1
  change 3*U.card-6 ≤ (edgeFamily (inducedOn H U)).card at hlow
  rw [hiH] at hlow
  have heq : H = inducedOn G U := graph_eq_of_le_card_edges hHU
    ((hG.induced_edge_bound U (by omega)).trans hlow)
  have htreeH : ThreeTreeOn U (actualDirectionGraph (basePolytope z)) := by
    change ThreeTreeOn U H
    rw [heq]
    exact htree
  obtain ⟨hdim,hA⟩ := threeTree_actual_dimension_admissible hz htreeH
  exact ⟨U,hU,heq,htree,heq ▸ hA,hdim⟩

/-- Actual weak summands have normalized lower-support functions preserving
both affine dimension and the literal graph of exposed edge directions. -/
theorem weak_summand_normalized_function {G : SimpleGraph V} {Q : Set (V → ℝ)}
    (hQ : IsFinitePolytope Q) (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    ∃ z : graphicalFunctionSpace G,Supermodular z.1 ∧
      (z.1 = 0 ∨ ExtremeSupermodular z.1) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = Module.finrank ℝ (vectorSpan ℝ (basePolytope z.1)) ∧
      actualDirectionGraph Q = actualDirectionGraph (basePolytope z.1) := by
  obtain ⟨c,hc,R,hR,hRc,hnR,hQR⟩ := hw
  have hTn : Normalized (c • graphFunction G) := by
    change c*graphFunction G ∅=0
    rw [graphFunction_normalized,mul_zero]
  have hTs := (graphFunction_supermodular G).smul hc.le
  have hbase : Q+R=basePolytope (c • graphFunction G) := by
    rw [basePolytope_smul (graphFunction_normalized G) (graphFunction_supermodular G) hc.le,
      baseGraphFunction_eq_graphicalZonotope]
    exact hQR
  let f := lowerSupport Q
  have hfn : Normalized f := lowerSupport_normalized hQ.compact hi.1
  have hfs : Supermodular f := summand_lowerSupport_supermodular hTn hTs
    hQ.compact hR hi.1 hnR hbase
  have hbody : Q=basePolytope f := summand_eq_basePolytope hTn hTs
    hQ.compact hR hQ.convex hi.1 hnR hbase
  have hgf : Graphical G f := by
    apply ((isMinkowskiSummand_graphical_iff hfn hfs hc.le).mp ?_).1
    rw [← hbody]
    exact ⟨R,hR,hRc,hnR,hQR⟩
  have hgn : Graphical G (normalize f) := by
    intro u v huv hnon S hu hv
    rw [delta_normalize f huv hu hv]
    exact hgf u v huv hnon S hu hv
  refine ⟨⟨normalize f,normalize_translationNormalized hfn,hgn⟩,hfs.normalize,?_,?_,?_⟩
  · by_cases hz : normalize f=0
    · exact Or.inl hz
    · exact Or.inr (MinkowskiIndecomposable.extremeSupermodular_normalize
        hfn hfs hz (hbody ▸ hi))
  · rw [vectorSpan_basePolytope_normalize,← hbody]
  · rw [actualDirectionGraph_normalize,← hbody]

/-- Corollary 6.6, necessity for ordinary polytopes, with no full-dimension
assumption on the ambient coordinate space. -/
theorem partial_threeTree_polytope_support {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) {Q : Set (V → ℝ)} (hQ : IsFinitePolytope Q)
    (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G))
    (hd : 3 ≤ Module.finrank ℝ (vectorSpan ℝ Q)) :
    ∃ U : Finset V,4 ≤ U.card ∧ actualDirectionGraph Q = inducedOn G U ∧
      ThreeTreeOn U (inducedOn G U) ∧ Admissible (inducedOn G U) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = U.card-1 := by
  obtain ⟨z,hz,he,hdim,hgraph⟩ := weak_summand_normalized_function hQ hi hw
  have hdz : 3 ≤ Module.finrank ℝ (vectorSpan ℝ (basePolytope z.1)) := by rwa [hdim] at hd
  have hext : ExtremeSupermodular z.1 := by
    rcases he with he | he
    · rw [he,basePolytope_zero,_root_.vectorSpan_singleton,finrank_bot] at hdz
      omega
    · exact he
  obtain ⟨U,hU,ha,ht,hA,hD⟩ := partial_threeTree_extreme_support hG hext z.2.2 hdz
  exact ⟨U,hU,hgraph.trans ha,ht,hA,hdim.trans hD⟩

/-- The converse in Corollary 6.6 supplies a lattice representative on every
permitted induced support and fixes all coordinates outside that support. -/
theorem induced_admissible_threeTree_witness {G : SimpleGraph V} {U : Finset V}
    (hU : ThreeTreeOn U (inducedOn G U)) (hA : Admissible (inducedOn G U)) :
    ∃ Q : Set (V → ℝ),LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      actualDirectionGraph Q = inducedOn G U ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = U.card-1 := by
  obtain ⟨f,hf,hi,hd,ha,hg⟩ := admissible_threeTree_active_witness hU hA
  refine ⟨basePolytope f,hi.basePolytope hf.1.1 hf.2.1,hf.minkowskiIndecomposable,?_,ha,hd⟩
  exact (isWeakMinkowskiSummand_graphical_iff hf.1.1 hf.2.1).mpr
    (hg.mono_graph (inducedOn_le G U))

/-- The complete actual-direction-support classification of Corollary 6.6.
The graph on the right is induced on its active vertices; vertices outside
it are isolated. Both implications quantify over arbitrary finite graphs. -/
theorem partial_threeTree_support_classification {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) (H : SimpleGraph V) :
    (∃ Q : Set (V → ℝ),IsFinitePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      3 ≤ Module.finrank ℝ (vectorSpan ℝ Q) ∧ actualDirectionGraph Q = H) ↔
    ∃ U : Finset V,H = inducedOn G U ∧ ThreeTreeOn U H ∧ Admissible H := by
  constructor
  · rintro ⟨Q,hQ,hi,hw,hd,rfl⟩
    obtain ⟨U,hU,ha,ht,hA,hD⟩ := partial_threeTree_polytope_support hG hQ hi hw hd
    exact ⟨U,ha,ha.symm ▸ ht,ha.symm ▸ hA⟩
  · rintro ⟨U,rfl,ht,hA⟩
    obtain ⟨Q,hQ,hi,hw,ha,hd⟩ := induced_admissible_threeTree_witness ht hA
    have hU := ht.active_card_ge_four
    refine ⟨Q,?_,hi,hw,?_,ha⟩
    · exact hQ.finitePolytope
    · omega

end GraphicalZonotopes

end
end
end BundlePart134

section BundlePart135
/- Source: Papers/GraphicalZonotopes/PartialThreeTreeSpectrumGraph.lean -/






/-! # Admissible clique collections in partial 3-trees

The collections below consist of actual tetrahedra, connected by shared
triangles. Their multiplicity condition is imposed on the selected collection,
not on all tetrahedra of the ambient graph.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem Admissible.mono {G H : SimpleGraph V} (hH : Admissible H) (hGH : G ≤ H) :
    Admissible G := by
  intro T hT hc
  exact (triangleMultiplicity_mono hGH T).trans
    (hH T hT (fun u hu v hv huv => hGH (hc hu hv huv)))

/-- Construction prefixes can have any requested size, and remain genuine
subgraphs of the final 3-tree. -/
theorem ThreeTreeOn.prefix {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {m : ℕ} (hm : 4 ≤ m) (hmS : m ≤ S.card) :
    ∃ T : Finset V, ∃ H : SimpleGraph V,
      T ⊆ S ∧ T.card = m ∧ H ≤ G ∧ ThreeTreeOn T H := by
  induction h generalizing m with
  | tetrahedron C hC =>
    have he : m = 4 := by omega
    exact ⟨C,cliqueGraph C,Subset.rfl,by omega,le_rfl,ThreeTreeOn.tetrahedron C hC⟩
  | @attach S G h u hu A hA hAS hcA ih =>
    by_cases hmold : m ≤ S.card
    · obtain ⟨T,H,hTS,hT,hHG,hH⟩ := ih hm hmold
      exact ⟨T,H,hTS.trans (subset_insert _ _),hT,hHG.trans le_sup_left,hH⟩
    · have he : (insert u S).card = m := by
        rw [card_insert_of_notMem hu] at hmS ⊢
        omega
      exact ⟨insert u S,G ⊔ attachmentStar u A,Subset.rfl,he,le_rfl,
        ThreeTreeOn.attach h u hu A hA hAS hcA⟩

theorem ThreeTreeOn.tetrahedronGraph_preconnected {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : (tetrahedronGraph (tetrahedra G)).Preconnected := by
  intro C D
  have hp := h.tetrahedra_reachable C.2 D.2
  rw [SimpleGraph.reachable_eq_reflTransGen] at hp
  have hh : ∀ E, Relation.ReflTransGen (TriangleComponents.cliqueGraph G).Adj C.1 E →
      ∃ hE : E ∈ tetrahedra G,
        (tetrahedronGraph (tetrahedra G)).Reachable C ⟨E,hE⟩ := by
    intro E hE
    induction hE with
    | refl => exact ⟨C.2,SimpleGraph.Reachable.rfl⟩
    | @tail E F hE hEF ih =>
      obtain ⟨hEmem,hreach⟩ := ih
      have hFmem : F ∈ tetrahedra G := mem_filter.mpr
        ⟨mem_univ _,hEF.2.1,hEF.2.2.2.1⟩
      refine ⟨hFmem,hreach.trans (SimpleGraph.Adj.reachable ?_)⟩
      exact ⟨fun he => hEF.2.2.2.2.1 (congrArg Subtype.val he),hEF.2.2.2.2.2⟩
  obtain ⟨hD,hreach⟩ := hh _ hp
  exact hreach

structure IsAdmissibleCliqueCollection (G : SimpleGraph V)
    (F : Finset (Finset V)) : Prop where
  nonempty : F.Nonempty
  included : F ⊆ tetrahedra G
  connected : (tetrahedronGraph F).Preconnected
  thin : ∀ T : Finset V, T.card = 3 → (F.filter (fun C => T ⊆ C)).card ≤ 3

theorem admissibleCliqueCollection_singleton {G : SimpleGraph V} {C : Finset V}
    (hC : C ∈ tetrahedra G) : IsAdmissibleCliqueCollection G {C} := by
  refine ⟨singleton_nonempty _,singleton_subset_iff.mpr hC,?_,?_⟩
  · intro A B
    have he : A = B := by
      apply Subtype.ext
      exact (mem_singleton.mp A.2).trans (mem_singleton.mp B.2).symm
    subst B
    exact SimpleGraph.Reachable.rfl
  · intro T hT
    have hc := card_filter_le (s := ({C} : Finset (Finset V))) (p := fun D => T ⊆ D)
    simp only [card_singleton] at hc
    omega

theorem ThreeTreeOn.admissibleCliqueCollection {S : Finset V} {H G : SimpleGraph V}
    (h : ThreeTreeOn S H) (hA : Admissible H) (hHG : H ≤ G) :
    IsAdmissibleCliqueCollection G (tetrahedra H) := by
  refine ⟨h.tetrahedra_nonempty,tetrahedra_mono hHG,h.tetrahedronGraph_preconnected,?_⟩
  intro T hT
  by_cases hc : H.IsClique T
  · exact hA T hT hc
  · have he : (tetrahedra H).filter (fun C => T ⊆ C) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro C hC
      obtain ⟨hC,hTC⟩ := mem_filter.mp hC
      have hcl := (mem_filter.mp hC).2.2
      exact hc (fun u hu v hv huv => hcl (hTC hu) (hTC hv) huv)
    rw [he,card_empty]
    omega

theorem IsAdmissibleCliqueCollection.four {G : SimpleGraph V}
    {F : Finset (Finset V)} (hF : IsAdmissibleCliqueCollection G F) :
    ∀ C ∈ F, C.card = 4 ∧ G.IsClique C := by
  intro C hC
  exact (mem_filter.mp (hF.included hC)).2

/-- In a partial 3-tree a connected collection already contains every
tetrahedron induced on its union. There are no hidden extra clique nodes. -/
theorem IsAdmissibleCliqueCollection.induced_structure {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) {F : Finset (Finset V)}
    (hF : IsAdmissibleCliqueCollection G F) :
    ThreeTreeOn (F.biUnion id) (inducedOn G (F.biUnion id)) ∧
      tetrahedra (inducedOn G (F.biUnion id)) = F ∧
      Admissible (inducedOn G (F.biUnion id)) ∧
      (F.biUnion id).card = F.card + 3 := by
  let U := F.biUnion id
  have ht := hG.connected_family_threeTree F hF.nonempty hF.four hF.connected
  have hsub : F ⊆ tetrahedra (inducedOn G U) := by
    intro C hC
    refine mem_filter.mpr ⟨mem_univ _,(hF.four C hC).1,?_⟩
    intro u hu v hv huv
    exact ⟨(hF.four C hC).2 hu hv huv,
      mem_biUnion.mpr ⟨C,hC,hu⟩,mem_biUnion.mpr ⟨C,hC,hv⟩⟩
  have hu := connected_tetrahedra_union_card F hF.nonempty
    (fun C hC => (hF.four C hC).1) hF.connected
  have hfour : 4 ≤ U.card := ht.active_card_ge_four
  have hcard : (tetrahedra (inducedOn G U)).card = U.card - 3 := ht.tetrahedra_card
  have he : tetrahedra (inducedOn G U) = F := by
    apply (eq_of_subset_of_card_le hsub ?_).symm
    rw [hcard]
    change U.card ≤ F.card + 3 at hu
    omega
  refine ⟨ht,he,?_,?_⟩
  · intro T hT hc
    change ((tetrahedra (inducedOn G U)).filter (fun C => T ⊆ C)).card ≤ 3
    rw [he]
    exact hF.thin T hT
  · rw [he] at hcard
    change U.card = F.card + 3
    omega

def admissibleCliqueCollections (G : SimpleGraph V) : Finset (Finset (Finset V)) := by
  classical
  exact univ.filter (IsAdmissibleCliqueCollection G)

/-- The invariant M(G) of Corollaries 6.7 and 6.8. -/
def maximumAdmissibleCliqueCount (G : SimpleGraph V) : ℕ :=
  (admissibleCliqueCollections G).sup Finset.card

theorem admissibleClique_count_le_maximum {G : SimpleGraph V} {F : Finset (Finset V)}
    (hF : IsAdmissibleCliqueCollection G F) : F.card ≤ maximumAdmissibleCliqueCount G := by
  apply le_sup
  exact mem_filter.mpr ⟨mem_univ _,hF⟩

theorem maximumAdmissibleCliqueCount_attained {G : SimpleGraph V}
    (hG : (tetrahedra G).Nonempty) :
    ∃ F : Finset (Finset V), IsAdmissibleCliqueCollection G F ∧
      F.card = maximumAdmissibleCliqueCount G := by
  obtain ⟨C,hC⟩ := hG
  have hne : (admissibleCliqueCollections G).Nonempty :=
    ⟨{C},mem_filter.mpr ⟨mem_univ _,admissibleCliqueCollection_singleton hC⟩⟩
  obtain ⟨F,hF,hmax⟩ := (admissibleCliqueCollections G).exists_max_image Finset.card hne
  have hf := (mem_filter.mp hF).2
  refine ⟨F,hf,le_antisymm (admissibleClique_count_le_maximum hf) ?_⟩
  exact Finset.sup_le_iff.mpr hmax

end GraphicalZonotopes

end
end
end BundlePart135

section BundlePart136
/- Source: Papers/GraphicalZonotopes/PartialThreeTreeSpectrum.lean -/




/-! # Dimension maxima and all intermediate dimensions in partial 3-trees

These are the mathematical assertions in Corollaries 6.7 and 6.8. The
algorithmic running-time assertion is not encoded by these theorems.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators Pointwise
namespace GraphicalZonotopes
open Finset SetFunctionEmbedding
variable {V : Type*} [Fintype V] [LinearOrder V]

/-- A simplex on any actual clique is a lattice indecomposable weak summand.
The affine dimension is the clique size minus one in the full ambient space. -/
theorem clique_simplex_witness {G : SimpleGraph V} {C : Finset V}
    (hC : 2 ≤ C.card) (hcl : G.IsClique C) :
    ∃ Q : Set (V → ℝ), LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = C.card-1 := by
  let e₀ := (Fintype.equivFin C).symm
  let e : Fin (Fintype.card C) ↪ V := e₀.toEmbedding.trans
    ⟨Subtype.val,Subtype.val_injective⟩
  let f : SetFunction (Fin (Fintype.card C)) := setMonomial univ
  have hcard : 2 ≤ Fintype.card C := by simpa only [Fintype.card_coe] using hC
  have hf : ExtremeSupermodular f := setMonomial_extreme (by simpa only [card_univ,
    Fintype.card_fin] using hcard)
  have hfi : IntegerValued f := by
    intro S
    by_cases hs : (univ : Finset (Fin (Fintype.card C))) ⊆ S
    · exact ⟨1,by simp [f,setMonomial,hs]⟩
    · exact ⟨0,by simp [f,setMonomial,hs]⟩
  have hg : Graphical (G.comap e) f := by
    apply (setMonomial_graphical univ).mono_graph
    intro u v huv
    exact hcl (e₀ u).2 (e₀ v).2 (fun he => huv.1 (e.injective he))
  have hext : ExtremeSupermodular (extend e f) := extend_extreme e hf
  have hdim := complete_simplex_fullDimension hcard
  refine ⟨basePolytope (extend e f),(extend_integer e hfi).basePolytope hext.1.1 hext.2.1,
    hext.minkowskiIndecomposable,?_,?_⟩
  · exact (isWeakMinkowskiSummand_graphical_iff hext.1.1 hext.2.1).mpr (extend_graphical e hg)
  · rw [finrank_vectorSpan_extend e hf.1]
    simpa only [FullDimension,Fintype.card_fin,Fintype.card_coe] using hdim

theorem partial_threeTree_dimension_le_clique_count {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) {Q : Set (V → ℝ)} (hQ : IsFinitePolytope Q)
    (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    Module.finrank ℝ (vectorSpan ℝ Q) ≤ maximumAdmissibleCliqueCount G+2 := by
  by_cases hd : 3 ≤ Module.finrank ℝ (vectorSpan ℝ Q)
  · obtain ⟨U,hU,ha,ht,hA,hD⟩ := partial_threeTree_polytope_support hG hQ hi hw hd
    have hF := ht.admissibleCliqueCollection hA (inducedOn_le G U)
    have hb := admissibleClique_count_le_maximum hF
    rw [ht.tetrahedra_card] at hb
    omega
  · omega

/-- The maximum admissible clique collection gives an actual lattice witness
for the supremum defining the dimension invariant. -/
theorem partial_threeTree_maximum_witness {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) (hK : (tetrahedra G).Nonempty) :
    ∃ Q : Set (V → ℝ), LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = maximumAdmissibleCliqueCount G+2 := by
  obtain ⟨F,hF,hmax⟩ := maximumAdmissibleCliqueCount_attained hK
  obtain ⟨ht,he,hA,hcard⟩ := hF.induced_structure hG
  obtain ⟨Q,hQ,hi,hw,ha,hd⟩ := induced_admissible_threeTree_witness ht hA
  exact ⟨Q,hQ,hi,hw,by omega⟩

theorem partial_threeTree_maximum_dimension {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) (hK : (tetrahedra G).Nonempty) :
    maximumIndecomposableDimension G = maximumAdmissibleCliqueCount G+2 := by
  apply le_antisymm
  · apply csSup_le'
    rintro d ⟨Q,hQ,hi,hw,hd⟩
    rw [← hd]
    exact partial_threeTree_dimension_le_clique_count hG hQ hi hw
  · obtain ⟨Q,hQ,hi,hw,hd⟩ := partial_threeTree_maximum_witness hG hK
    rw [← hd]
    exact dimension_le_maximum hQ.finitePolytope hi hw

/-- Every positive integer through the sharp maximum occurs, with no gap and
with a lattice representative. The construction uses an arbitrary prefix of
a maximizing admissible three-tree and actual clique simplices at dimensions
one and two. -/
theorem partial_threeTree_dimension_spectrum {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) (hK : (tetrahedra G).Nonempty)
    (d : ℕ) (hd : 1 ≤ d) (hdM : d ≤ maximumAdmissibleCliqueCount G+2) :
    ∃ Q : Set (V → ℝ), LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = d := by
  by_cases hd3 : 3 ≤ d
  · obtain ⟨F,hF,hmax⟩ := maximumAdmissibleCliqueCount_attained hK
    obtain ⟨ht,he,hA,hcard⟩ := hF.induced_structure hG
    obtain ⟨U,H,hU,hcardU,hH,htH⟩ := ht.prefix (m := d+1) (by omega) (by omega)
    have hHA : Admissible H := hA.mono hH
    obtain ⟨f,hf,hfi,hfd,hfa,hfg⟩ := admissible_threeTree_active_witness htH hHA
    refine ⟨basePolytope f,hfi.basePolytope hf.1.1 hf.2.1,hf.minkowskiIndecomposable,?_,?_⟩
    · exact (isWeakMinkowskiSummand_graphical_iff hf.1.1 hf.2.1).mpr
        (hfg.mono_graph (hH.trans (inducedOn_le G _)))
    · omega
  · obtain ⟨C,hC⟩ := hK
    obtain ⟨hfour,hcl⟩ := (mem_filter.mp hC).2
    obtain ⟨D,hDC,hD⟩ := exists_subset_card_eq (s := C) (n := d+1) (by omega)
    obtain ⟨Q,hQ,hi,hw,hqdim⟩ := clique_simplex_witness
      (by omega : 2 ≤ D.card) (fun u hu v hv huv => hcl (hDC hu) (hDC hv) huv)
    exact ⟨Q,hQ,hi,hw,by omega⟩

/-- Corollary 6.7's exact dimension and full positive spectrum. Algorithmic
complexity is a separate assertion and is not hidden in this statement. -/
theorem threeTree_dimension_and_spectrum {G : SimpleGraph V} (hG : IsThreeTree G) :
    maximumIndecomposableDimension G = maximumAdmissibleCliqueCount G+2 ∧
      ∀ d : ℕ,1 ≤ d → d ≤ maximumAdmissibleCliqueCount G+2 →
        ∃ Q : Set (V → ℝ), LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
          IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
          Module.finrank ℝ (vectorSpan ℝ Q) = d := by
  have hp : IsPartialThreeTree G := Or.inr ⟨G,hG,le_rfl⟩
  exact ⟨partial_threeTree_maximum_dimension hp hG.tetrahedra_nonempty,
    partial_threeTree_dimension_spectrum hp hG.tetrahedra_nonempty⟩

end GraphicalZonotopes

end
end
end BundlePart136

section BundlePart137
/- Source: Papers/GraphicalZonotopes/PolytopalDimension.lean -/




/-! # Dimension invariants with the paper's polytopal convention -/

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The dimension supremum is unchanged when indecomposability is defined
using only finite polytopal Minkowski decompositions, as in the paper. -/
theorem maximumIndecomposableDimension_eq_polytopal_supremum (G : SimpleGraph V) :
    maximumIndecomposableDimension G =
      sSup {d : ℕ | ∃ Q : Set (V → ℝ),IsFinitePolytope Q ∧
        PolytopalMinkowskiIndecomposable Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
        Module.finrank ℝ (vectorSpan ℝ Q)=d} := by
  unfold maximumIndecomposableDimension
  congr 1
  ext d
  constructor
  · rintro ⟨Q,hQ,hi,hw,hd⟩
    exact ⟨Q,hQ,(weakSummand_indecomposable_iff_polytopal hQ hw).mp hi,hw,hd⟩
  · rintro ⟨Q,hQ,hi,hw,hd⟩
    exact ⟨Q,hQ,(weakSummand_indecomposable_iff_polytopal hQ hw).mpr hi,hw,hd⟩

theorem supportsFullIndecomposable_iff_polytopal_weak (G : SimpleGraph V) :
    SupportsFullIndecomposable G ↔
      ∃ Q : Set (V → ℝ),IsFinitePolytope Q ∧
        PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope G) := by
  constructor
  · rintro ⟨Q,hQ,hi,hd,hw⟩
    exact ⟨Q,hQ,(weakSummand_indecomposable_iff_polytopal hQ hw).mp hi,hd,hw⟩
  · rintro ⟨Q,hQ,hi,hd,hw⟩
    exact ⟨Q,hQ,(weakSummand_indecomposable_iff_polytopal hQ hw).mpr hi,hd,hw⟩

end GraphicalZonotopes

end
end
end BundlePart137

section BundlePart138
/- Source: Papers/GraphicalZonotopes/TreeJoinDimension.lean -/







/-! # Corollary 6.9: the join of K₂ with an arbitrary finite tree

The maximum is over actual finite polytopes in the ambient coordinate space.
Every nonempty tree is covered, including the one-vertex tree. The invariant
s₃ counts vertices in ordinary connected subtrees of maximum degree three;
the equivalence of induced and arbitrary subtree presentations is proved in
TreeJoinSubtrees. The lower bound supplies an actual lattice witness.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.TreeJoin
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def vertexOrder (V : Type*) [Fintype V] [DecidableEq V] : LinearOrder (Vertex V) :=
  let o : LinearOrder (Vertex V) :=
    LinearOrder.lift' (Fintype.equivFin (Vertex V)) (Fintype.equivFin (Vertex V)).injective
  { o with
    toDecidableEq := inferInstance
    compare := fun x y => @compareOfLessAndEq _ x y o.toLT (o.toDecidableLT x y) inferInstance
    compare_eq_compareOfLessAndEq := by intros; rfl }

local instance : LinearOrder (Vertex V) := vertexOrder V
local instance : DecidableEq (Vertex V) := (vertexOrder V).toDecidableEq

theorem isPartialThreeTree {T : SimpleGraph V} (hT : T.IsTree) :
    IsPartialThreeTree (graph T) := by
  by_cases hn : 2≤ Fintype.card V
  · exact Or.inr ⟨graph T,isThreeTree hT hn,le_rfl⟩
  · apply Or.inl
    simp only [Vertex,Fintype.card_sum,Fintype.card_fin]
    omega

theorem summand_dimension_le {T : SimpleGraph V} (hT : T.IsTree)
    {Q : Set (Vertex V → ℝ)} (hQ : IsFinitePolytope Q)
    (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope (graph T))) :
    Module.finrank ℝ (vectorSpan ℝ Q)≤ s3 T+1 := by
  letI : Nonempty V := hT.connected.nonempty
  by_cases hd : 3≤ Module.finrank ℝ (vectorSpan ℝ Q)
  · obtain ⟨S,hcard,hactual,hS,hA,hD⟩ :=
      partial_threeTree_polytope_support (isPartialThreeTree hT) hQ hi hw hd
    obtain ⟨U,hSU,hn,ht,hm⟩ := induced_admissible_subtree hT.isAcyclic hS hA
    have hU := subtree_card_le_s3 ht hm
    rw [hSU,core_card] at hD
    omega
  · have hp := s3_pos T
    omega

theorem lattice_attainment {T : SimpleGraph V} (hT : T.IsTree) :
    ∃ Q : Set (Vertex V → ℝ),LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (graph T)) ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=s3 T+1 := by
  letI : Nonempty V := hT.connected.nonempty
  obtain ⟨U,ht,hm,hU⟩ := s3_attained T
  by_cases hn : 2≤ U.card
  · have htr := (induced_core_threeTree_iff hT.isAcyclic U hn).mpr ht
    have hA := (induced_core_admissible_iff hT.isAcyclic U).mpr hm
    obtain ⟨Q,hQ,hi,hw,ha,hd⟩ := induced_admissible_threeTree_witness htr hA
    refine ⟨Q,hQ,hi,hw,?_⟩
    rw [core_card,hU] at hd
    omega
  · have hpos := s3_pos T
    have hcard : U.card=1 := by omega
    obtain ⟨v,hv⟩ := card_eq_one.mp hcard
    have hc : (graph T).IsClique (core U) := by
      apply (core_clique_iff T U).mpr
      rw [hv]
      simp [SimpleGraph.isClique_singleton]
    obtain ⟨Q,hQ,hi,hw,hd⟩ := clique_simplex_witness
      (by rw [core_card]; omega : 2≤(core U).card) hc
    refine ⟨Q,hQ,hi,hw,?_⟩
    rw [core_card,hU] at hd
    omega

theorem maximum_dimension {T : SimpleGraph V} (hT : T.IsTree) :
    maximumIndecomposableDimension (graph T)=s3 T+1 := by
  apply le_antisymm
  · apply csSup_le'
    rintro d ⟨Q,hQ,hi,hw,hd⟩
    rw [←hd]
    exact summand_dimension_le hT hQ hi hw
  · obtain ⟨Q,hQ,hi,hw,hd⟩ := lattice_attainment hT
    have h := dimension_le_maximum hQ.finitePolytope hi hw
    rwa [hd] at h

theorem supports_full_iff {T : SimpleGraph V} (hT : T.IsTree) :
    SupportsFullIndecomposable (graph T) ↔ T.maxDegree≤3 := by
  constructor
  · rintro ⟨Q,hQ,hi,hd,hw⟩
    have h := summand_dimension_le hT hQ hi hw
    have hbound := s3_le_card T
    change Module.finrank ℝ (vectorSpan ℝ Q)=Fintype.card (Vertex V)-1 at hd
    simp only [Vertex,Fintype.card_sum,Fintype.card_fin] at hd
    have hdim : Module.finrank ℝ (vectorSpan ℝ Q)=Fintype.card V+1 := by
      simpa only [Nat.add_sub_cancel] using hd
    rw [hdim] at h
    exact (s3_eq_card_iff hT).mp
      (le_antisymm hbound (Nat.le_of_add_le_add_right h))
  · intro h
    have he := (s3_eq_card_iff hT).mpr h
    obtain ⟨Q,hQ,hi,hw,hd⟩ := lattice_attainment hT
    refine ⟨Q,hQ.finitePolytope,hi,?_,hw⟩
    change Module.finrank ℝ (vectorSpan ℝ Q)=Fintype.card (Vertex V)-1
    simp only [Vertex,Fintype.card_sum,Fintype.card_fin]
    rw [hd,he]
    omega

/-- The complete K₂*tree portion of Corollary 6.9, with the paper's ordinary
polytopal indecomposability convention and lattice attainment of the maximum. -/
theorem paper_corollary_6_9_tree_join (T : SimpleGraph V) (hT : T.IsTree) :
    (sSup {d : ℕ | ∃ Q : Set (Vertex V → ℝ),IsFinitePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (graph T)) ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=d})=s3 T+1 ∧
    ((∃ Q : Set (Vertex V → ℝ),IsFinitePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (graph T))) ↔ T.maxDegree≤3) ∧
    ∃ Q : Set (Vertex V → ℝ),LatticePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (graph T)) ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=s3 T+1 := by
  refine ⟨?_,?_,?_⟩
  · rw [←maximumIndecomposableDimension_eq_polytopal_supremum]
    exact maximum_dimension hT
  · rw [←supportsFullIndecomposable_iff_polytopal_weak]
    exact supports_full_iff hT
  · obtain ⟨Q,hQ,hi,hw,hd⟩ := lattice_attainment hT
    exact ⟨Q,hQ,(weakSummand_indecomposable_iff_polytopal hQ.finitePolytope hw).mp hi,hw,hd⟩

end GraphicalZonotopes.TreeJoin

end
end
end BundlePart138

section BundlePart139
/- Source: Papers/GraphicalZonotopes/LatticeExtremeEmbedding.lean -/







@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- An actual integral extreme graphical set function with exact dimension
and a uniform integral elemental-slack bound. -/
def LatticeExtremeAt (G : SimpleGraph V) (d M : ℕ) : Prop :=
  ∃ f : SetFunction V,TranslationNormalized f ∧ IntegerValued f ∧
    ExtremeSupermodular f ∧ Graphical G f ∧
    Module.finrank ℝ (vectorSpan ℝ (basePolytope f))=d ∧
    ∀ u v,u≠ v → ∀ S,u∉S → v∉S → delta f u v S≤(M : ℝ)

theorem LatticeExtremeAt.of_lattice_complement {G : SimpleGraph V} {f : SetFunction V}
    (hn : TranslationNormalized f) (hi : IntegerValued f) (he : ExtremeSupermodular f)
    (hG : Graphical G f) {d M : ℕ} (hd : Module.finrank ℝ (vectorSpan ℝ (basePolytope f))=d)
    {R : Set (V → ℝ)} (hR : LatticePolytope R) (hRn : R.Nonempty)
    (hsum : basePolytope f+R=(M : ℝ) • graphicalZonotope G) : LatticeExtremeAt G d M := by
  have hsummand : IsMinkowskiSummand (basePolytope f) ((M : ℝ) • graphicalZonotope G) :=
    ⟨R,hR.compact,hR.convex,hRn,hsum⟩
  have hb := ((isMinkowskiSummand_graphical_iff hn.1 he.2.1 (Nat.cast_nonneg M)).mp hsummand).2
  refine ⟨f,hn,hi,he,hG,hd,?_⟩
  intro u v huv S hu hv
  by_cases hedge : G.Adj u v
  · exact hb u v huv hedge S hu hv
  · rw [hG u v huv hedge S hu hv]
    exact Nat.cast_nonneg M

theorem LatticeExtremeAt.mono_dilation {G : SimpleGraph V} {d M N : ℕ}
    (h : LatticeExtremeAt G d M) (hMN : M≤ N) : LatticeExtremeAt G d N := by
  obtain ⟨f,hn,hi,he,hG,hd,hb⟩ := h
  exact ⟨f,hn,hi,he,hG,hd,fun u v huv S hu hv =>
    (hb u v huv S hu hv).trans (by exact_mod_cast hMN)⟩

theorem LatticeExtremeAt.embed {G : SimpleGraph V} {H : SimpleGraph W}
    {d M : ℕ} (h : LatticeExtremeAt G d M) (e : V ↪ W) (hGH : G≤ H.comap e) :
    LatticeExtremeAt H d M := by
  obtain ⟨f,hn,hi,he,hG,hd,hb⟩ := h
  let g := SetFunctionEmbedding.extend e f
  refine ⟨g,SetFunctionEmbedding.extend_translationNormalized e hn,
    SetFunctionEmbedding.extend_integer e hi,SetFunctionEmbedding.extend_extreme e he,
    SetFunctionEmbedding.extend_graphical e (hG.mono_graph hGH),?_,?_⟩
  · rw [SetFunctionEmbedding.finrank_vectorSpan_extend e hn]
    exact hd
  · intro u v huv S hu hv
    by_cases huR : u∈Set.range e
    · obtain ⟨a,rfl⟩ := huR
      by_cases hvR : v∈Set.range e
      · obtain ⟨b,rfl⟩ := hvR
        rw [SetFunctionEmbedding.delta_extend]
        exact hb a b (fun h => huv (congrArg e h)) _
          (by simpa using hu) (by simpa using hv)
      · rw [delta_comm,SetFunctionEmbedding.delta_extend_not_range e f v (e a) hvR]
        exact Nat.cast_nonneg M
    · rw [SetFunctionEmbedding.delta_extend_not_range e f u v huR]
      exact Nat.cast_nonneg M

theorem LatticeExtremeAt.polytope {G : SimpleGraph V} {d M : ℕ}
    (h : LatticeExtremeAt G d M) :
    ∃ Q : Set (V → ℝ),LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=d ∧
      IsMinkowskiSummand Q ((M : ℝ) • graphicalZonotope G) := by
  obtain ⟨f,hn,hi,he,hG,hd,hb⟩ := h
  exact ⟨basePolytope f,hi.basePolytope hn.1 he.2.1,he.minkowskiIndecomposable,hd,
    (isMinkowskiSummand_graphical_iff hn.1 he.2.1 (Nat.cast_nonneg M)).mpr
      ⟨hG,fun u v huv _ S hu hv => hb u v huv S hu hv⟩⟩

theorem LatticeExtremeAt.dimension_le_maximum {G : SimpleGraph V} {d M : ℕ}
    (h : LatticeExtremeAt G d M) : d≤ maximumIndecomposableDimension G := by
  obtain ⟨f,hn,hi,he,hG,hd,hb⟩ := h
  rw [← hd]
  exact GraphicalZonotopes.dimension_le_maximum (show IsGeneralizedPermutahedron (basePolytope f) from ⟨f,hn.1,he.2.1,rfl⟩).finitePolytope
    he.minkowskiIndecomposable ((isWeakMinkowskiSummand_graphical_iff hn.1 he.2.1).mpr hG)

theorem LatticeExtremeAt.supports_full {G : SimpleGraph V} {M : ℕ}
    (h : LatticeExtremeAt G (Fintype.card V-1) M) : SupportsFullIndecomposable G := by
  obtain ⟨f,hn,hi,he,hG,hd,hb⟩ := h
  exact ⟨basePolytope f,(show IsGeneralizedPermutahedron (basePolytope f) from ⟨f,hn.1,he.2.1,rfl⟩).finitePolytope,
    he.minkowskiIndecomposable,hd,(isWeakMinkowskiSummand_graphical_iff hn.1 he.2.1).mpr hG⟩

end GraphicalZonotopes

end
end
end BundlePart139

section BundlePart140
/- Source: Papers/GraphicalZonotopes/BookEmbeddings.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators

/-- Promoting one outer vertex to a hub preserves all existing edges. -/
def bookPromote (s k : ℕ) : (Fin s⊕Fin (k+1)) ≃ (Fin (s+1)⊕Fin k) where
  toFun
    | .inl i => .inl i.succ
    | .inr j => Fin.cases (.inl 0) (fun i => .inr i) j
  invFun
    | .inl i => Fin.cases (.inr 0) (fun j => .inl j) i
    | .inr j => .inr j.succ
  left_inv x := by
    cases x with
    | inl i => rfl
    | inr j => exact Fin.cases rfl (fun _ => rfl) j
  right_inv x := by
    cases x with
    | inl i => exact Fin.cases rfl (fun _ => rfl) i
    | inr j => rfl

theorem bookPromote_edges (s k : ℕ) :
    cliqueBook s (k+1)≤(cliqueBook (s+1) k).comap (bookPromote s k) := by
  intro u v h
  change u≠ v ∧ (u.isLeft ∨ v.isLeft) at h
  change (bookPromote s k u)≠(bookPromote s k v) ∧
    ((bookPromote s k u).isLeft ∨ (bookPromote s k v).isLeft)
  have hleft : ∀ x : Fin s⊕Fin (k+1),x.isLeft → (bookPromote s k x).isLeft := by
    intro x hx
    cases x with
    | inl i => rfl
    | inr j => exact False.elim (by simpa using hx)
  exact ⟨fun he => h.1 ((bookPromote s k).injective he),h.2.elim
    (fun hu => Or.inl (hleft u hu)) (fun hv => Or.inr (hleft v hv))⟩

def bookOuterEmbedding (s : ℕ) {k l : ℕ} (hkl : k≤ l) : (Fin s⊕Fin k) ↪ (Fin s⊕Fin l) :=
  Function.Embedding.sumMap (Function.Embedding.refl _) (Fin.castLEEmb hkl)

theorem bookOuterEmbedding_edges (s : ℕ) {k l : ℕ} (hkl : k≤ l) :
    cliqueBook s k≤(cliqueBook s l).comap (bookOuterEmbedding s hkl) := by
  intro u v h
  change u≠ v ∧ (u.isLeft ∨ v.isLeft) at h
  change (bookOuterEmbedding s hkl u)≠(bookOuterEmbedding s hkl v) ∧
    ((bookOuterEmbedding s hkl u).isLeft ∨ (bookOuterEmbedding s hkl v).isLeft)
  constructor
  · exact fun he => h.1 ((bookOuterEmbedding s hkl).injective he)
  · cases u <;> cases v <;> simpa [bookOuterEmbedding] using h.2

theorem book_lattice_promote {s k M : ℕ}
    (h : LatticeExtremeAt (cliqueBook s (k+1)) (s+(k+1)-1) M) :
    LatticeExtremeAt (cliqueBook (s+1) k) (s+1+k-1) M := by
  simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
    h.embed (bookPromote s k).toEmbedding (bookPromote_edges s k)

theorem book_lattice_add_outer {s k l M : ℕ} (hkl : k≤ l)
    (h : LatticeExtremeAt (cliqueBook s k) (s+k-1) M) :
    LatticeExtremeAt (cliqueBook s l) (s+k-1) M :=
  h.embed (bookOuterEmbedding s hkl) (bookOuterEmbedding_edges s hkl)

end GraphicalZonotopes

end
end
end BundlePart140

section BundlePart141
/- Source: Papers/GraphicalZonotopes/BooleanResponseQuotient.lean -/






@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H J : Type*} [Fintype H] [LinearOrder H] [Fintype J] [DecidableEq J]

/-- The paper's rows are unordered hub pairs, each with every conditioning
subset of the remaining hubs. `BoundaryContext` uses the increasing ordering
only to select one representative of each unordered pair. -/
abbrev HubResponseRow (H : Type*) [Fintype H] [LinearOrder H] :=
  BoundaryContext (⊤ : SimpleGraph H)

def centralSlack : graphicalFunctionSpace (⊤ : SimpleGraph H) →ₗ[ℝ]
    (HubResponseRow H → ℝ) := boundarySlackMap ⊤

/-- This is literally the elemental map from all central Möbius coefficients,
including every subset of size at least two. -/
def centralCoefficientSlack : (CliqueIndex (⊤ : SimpleGraph H) → ℝ) →ₗ[ℝ]
    (HubResponseRow H → ℝ) :=
  centralSlack ∘ₗ (graphicalCoordinatesEquiv ⊤).toLinearMap

theorem centralSlack_injective : Function.Injective (centralSlack (H:=H)) :=
  boundarySlackMap_injective ⊤

theorem centralCoefficientSlack_injective :
    Function.Injective (centralCoefficientSlack (H:=H)) :=
  centralSlack_injective.comp (graphicalCoordinatesEquiv ⊤).injective

theorem centralCoefficientSlack_range :
    LinearMap.range (centralCoefficientSlack (H:=H))=
      LinearMap.range (centralSlack (H:=H)) := by
  apply le_antisymm
  · rintro x ⟨c,rfl⟩
    exact ⟨graphicalCoordinatesEquiv ⊤ c,rfl⟩
  · rintro x ⟨z,rfl⟩
    exact ⟨(graphicalCoordinatesEquiv ⊤).symm z,by
      simp only [centralCoefficientSlack,LinearMap.comp_apply,
        LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]⟩

def responseVector (F : SetFunction H) : HubResponseRow H → ℝ :=
  fun r => negativeResponse F r.1.1.1 r.1.1.2 r.2.1

def weightedResponse (F : J → SetFunction H) :
    (J → ℝ) →ₗ[ℝ] (HubResponseRow H → ℝ) where
  toFun w r := ∑ j : J,w j*responseVector (F j) r
  map_add' w t := by ext r; simp [add_mul,sum_add_distrib]
  map_smul' c w := by ext r; simp [mul_assoc,mul_sum]

/-- The complete relation map in the actual response quotient. Its kernel
contains all real relations among the classes, not merely positive ones. -/
def quotientRelation (F : J → SetFunction H) :
    (J → ℝ) →ₗ[ℝ]
      ((HubResponseRow H → ℝ) ⧸ LinearMap.range (centralCoefficientSlack (H:=H))) :=
  (LinearMap.range (centralCoefficientSlack (H:=H))).mkQ ∘ₗ weightedResponse F

theorem negativeResponse_comm (F : SetFunction H) (u v : H) (S : Finset H) :
    negativeResponse F u v S=negativeResponse F v u S := by
  simp only [negativeResponse,delta_comm u v]

theorem central_function {z : SetFunction H} (hz : TranslationNormalized z) :
    z∈graphicalFunctionSpace (⊤ : SimpleGraph H) := by
  refine ⟨hz,?_⟩
  intro u v huv hnon S hu hv
  exact False.elim (hnon ((SimpleGraph.top_adj u v).mpr huv))

theorem remaining_subset_commonNeighbors (u v : H) (S : Finset H)
    (hu : u∉S) (hv : v∉S) : S⊆commonNeighbors (⊤ : SimpleGraph H) u v := by
  intro a ha
  apply (mem_commonNeighbors _ _ _ _).mpr
  constructor
  · apply (SimpleGraph.top_adj u a).mpr
    intro he
    exact hu (he.symm ▸ ha)
  · apply (SimpleGraph.top_adj v a).mpr
    intro he
    exact hv (he.symm ▸ ha)

/-- Quantifying over the row type is equivalent to quantifying over every
actual elemental difference, with no context omitted. -/
theorem compatible_iff_rows {z : SetFunction H} (hz : TranslationNormalized z)
    (F : J → SetFunction H) (w : J → ℝ) :
    Compatible z F w ↔
      centralSlack ⟨z,central_function hz⟩=weightedResponse F w := by
  constructor
  · intro hc
    funext r
    have hu : r.1.1.1∉r.2.1 := by
      intro hm
      exact not_mem_commonNeighbors_left ⊤ _ _ ((mem_powerset.mp r.2.2) hm)
    have hv : r.1.1.2∉r.2.1 := by
      intro hm
      exact not_mem_commonNeighbors_right ⊤ _ _ ((mem_powerset.mp r.2.2) hm)
    exact hc _ _ (ne_of_lt r.1.2.1) _ hu hv
  · intro he u v huv S hu hv
    have hordered : ∀ a b,a< b → a∉S → b∉S →
        delta z a b S=∑ j : J,w j*negativeResponse (F j) a b S := by
      intro a b hab ha hb
      let e : OrientedEdge (⊤ : SimpleGraph H):=
        ⟨(a,b),hab,(SimpleGraph.top_adj a b).mpr (ne_of_lt hab)⟩
      let r : HubResponseRow H:=⟨e,⟨S,mem_powerset.mpr
        (remaining_subset_commonNeighbors a b S ha hb)⟩⟩
      exact congrFun he r
    rcases lt_or_gt_of_ne huv with hlt | hgt
    · exact hordered u v hlt hu hv
    · rw [delta_comm u v,hordered v u hgt hv hu]
      apply sum_congr rfl
      intro j hj
      rw [negativeResponse_comm (F j) v u]

theorem mem_quotientRelation_ker_iff (F : J → SetFunction H) (w : J → ℝ) :
    w∈LinearMap.ker (quotientRelation F) ↔
      ∃ z : SetFunction H,TranslationNormalized z ∧ Compatible z F w := by
  change (LinearMap.range (centralCoefficientSlack (H:=H))).mkQ
      (weightedResponse F w)=0 ↔ _
  rw [← LinearMap.mem_ker,Submodule.ker_mkQ,centralCoefficientSlack_range]
  constructor
  · rintro ⟨z,hz⟩
    exact ⟨z.1,z.2.1,(compatible_iff_rows z.2.1 F w).mpr hz⟩
  · rintro ⟨z,hz,hc⟩
    exact ⟨⟨z,central_function hz⟩,(compatible_iff_rows hz F w).mp hc⟩

/-- The basis-free compatibility formulation used in the zero-equation proof
is exactly the paper's one-dimensional quotient relation condition. -/
theorem uniqueIntegrableRelation_iff_ker_eq_span
    (F : J → SetFunction H) (w : J → ℝ)
    (hw : ∃ z : SetFunction H,TranslationNormalized z ∧ Compatible z F w) :
    UniqueIntegrableRelation F w ↔
      LinearMap.ker (quotientRelation F)=Submodule.span ℝ {w} := by
  have hwm : w∈LinearMap.ker (quotientRelation F):=
    (mem_quotientRelation_ker_iff F w).mpr hw
  constructor
  · intro huniq
    apply le_antisymm
    · intro t ht
      obtain ⟨c,hc⟩:=huniq t ((mem_quotientRelation_ker_iff F t).mp ht)
      exact Submodule.mem_span_singleton.mpr ⟨c,hc.symm⟩
    · apply Submodule.span_le.mpr
      intro t ht
      have he : t=w := Set.mem_singleton_iff.mp ht
      subst t
      exact hwm
  · intro hker t ht
    have hm:=(mem_quotientRelation_ker_iff F t).mpr ht
    rw [hker,Submodule.mem_span_singleton] at hm
    obtain ⟨c,hc⟩:=hm
    exact ⟨c,hc.symm⟩

/-- Literal positive-circuit extremality: the relation space is the kernel of
the map to the quotient by the central Möbius image. -/
theorem positive_quotient_circuit_extreme [Nonempty J]
    {z : SetFunction H} (hz : TranslationNormalized z)
    {F : J → SetFunction H} (hF : ∀ j,IsMonotoneBoolean (F j))
    {w : J → ℝ} (hw : ∀ j,0< w j) (hc : Compatible z F w)
    (hd : Module.finrank ℝ (LinearMap.ker (quotientRelation F))=1) :
    ExtremeSupermodular (assembled z F w) := by
  obtain ⟨j₀⟩:=‹Nonempty J›
  have hne : w≠0 := by
    intro he
    have hj:=hw j₀
    rw [he] at hj
    simp at hj
  have hm : w∈LinearMap.ker (quotientRelation F):=
    (mem_quotientRelation_ker_iff F w).mpr ⟨z,hz,hc⟩
  have hker:=eq_span_singleton_of_mem_of_finrank_eq_one hd hm hne
  exact positive_circuit_extreme hz hF (fun j => (hw j).le)
    ⟨j₀,ne_of_gt (hw j₀)⟩ hc
    ((uniqueIntegrableRelation_iff_ker_eq_span F w ⟨z,hz,hc⟩).mpr hker)

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart141

section BundlePart142
/- Source: Papers/GraphicalZonotopes/BookModuleGeometry.lean -/







@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise
variable {H J : Type*} [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]

/-- An essential Boolean variable is witnessed by an actual cover with
increment one. For a monotone zero-one function this is ordinary dependence
on that variable. -/
def Essential (F : SetFunction H) (a : H) : Prop :=
  ∃ X : Finset H,a∉X ∧ F (insert a X)-F X=1

def essentialSpokeGraph (F : J → SetFunction H) : SimpleGraph (H⊕J) where
  Adj
    | Sum.inl a,Sum.inr j => Essential (F j) a
    | Sum.inr j,Sum.inl a => Essential (F j) a
    | _,_ => False
  symm := ⟨by intro a b; cases a <;> cases b <;> exact id⟩
  loopless := ⟨by intro a; cases a <;> exact not_false⟩

theorem essentialSpokeGraph_connected [Nonempty H] [Nonempty J]
    (F : J → SetFunction H) (hF : ∀ j a,Essential (F j) a) :
    (essentialSpokeGraph F).Connected := by
  obtain ⟨a₀⟩:=‹Nonempty H›
  obtain ⟨j₀⟩:=‹Nonempty J›
  have hcross : ∀ a j,(essentialSpokeGraph F).Adj (Sum.inl a) (Sum.inr j):=
    fun a j => hF j a
  refine ⟨?_⟩
  intro x y
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      exact (hcross a j₀).reachable.trans (hcross b j₀).reachable.symm
    | inr j => exact (hcross a j).reachable
  | inr i =>
    cases y with
    | inl a => exact (hcross a i).reachable.symm
    | inr j =>
      exact (hcross a₀ i).reachable.symm.trans (hcross a₀ j).reachable

theorem essential_spoke_slack {z : SetFunction H} {F : J → SetFunction H}
    {w : J → ℝ} (hw : ∀ j,0< w j) {a b : H⊕J}
    (hab : (essentialSpokeGraph F).Adj a b) :
    ∃ A : Finset (H⊕J),a∉A ∧ b∉A ∧ delta (assembled z F w) a b A≠0 := by
  cases a with
  | inl u =>
    cases b with
    | inl v => exact False.elim hab
    | inr j =>
      obtain ⟨X,hu,hX⟩:=hab
      refine ⟨hubSet X,by simpa using hu,by simp,?_⟩
      rw [delta_assembled_spoke _ _ _ _ _ _ (by simp),hubs_hubSet,hX,mul_one]
      exact ne_of_gt (hw j)
  | inr i =>
    cases b with
    | inl v =>
      obtain ⟨X,hv,hX⟩:=hab
      refine ⟨hubSet X,by simp,by simpa using hv,?_⟩
      rw [delta_swap,delta_assembled_spoke _ _ _ _ _ _ (by simp),hubs_hubSet,hX,mul_one]
      exact ne_of_gt (hw i)
    | inr j => exact False.elim hab

/-- The dimension clause of Lemma7.3 uses the genuine connected spanning
essential-spoke graph, so ignored variables remain present in the ambient
coordinate space and cannot disappear silently. -/
theorem assembled_fullDimension {z : SetFunction H} (hz : TranslationNormalized z)
    {F : J → SetFunction H} (hF : ∀ j,IsMonotoneBoolean (F j))
    {w : J → ℝ} (hw : ∀ j,0< w j) (hc : Compatible z F w)
    (hconn : (essentialSpokeGraph F).Connected) :
    FullDimension (basePolytope (assembled z F w)) := by
  apply finrank_vectorSpan_eq_of_connected_slacks (assembled_normalized hz F hF w).1
    (assembled_supermodular z F hF w (fun j => (hw j).le) hc) hconn
  intro a b hab
  exact essential_spoke_slack hw hab

theorem assembled_delta_le_weight_sum {z : SetFunction H}
    {F : J → SetFunction H} (hF : ∀ j,IsMonotoneBoolean (F j))
    {w : J → ℝ} (hw : ∀ j,0≤ w j) (hc : Compatible z F w)
    (a b : H⊕J) (hab : a≠ b) (A : Finset (H⊕J)) (ha : a∉A) (hb : b∉A) :
    delta (assembled z F w) a b A≤∑ j : J,w j := by
  have hsum : 0≤∑ j : J,w j:=sum_nonneg (fun j _ => hw j)
  have hspoke : ∀ u j,Sum.inr j∉A →
      delta (assembled z F w) (Sum.inl u) (Sum.inr j) A≤∑ i : J,w i := by
    intro u j hj
    rw [delta_assembled_spoke _ _ _ _ _ _ hj]
    have hcover : F j (insert u (hubs A))-F j (hubs A)≤1 := by
      rcases cover_values (hF j) u (hubs A) with h | h <;> simp [h]
    exact (mul_le_mul_of_nonneg_left hcover (hw j)).trans
      (by simpa using single_le_sum (fun i _ => hw i) (mem_univ j))
  cases a with
  | inl u =>
    cases b with
    | inl v =>
      rw [assembled_factorization z F w hc u v (fun he => hab (congrArg Sum.inl he)) A ha hb]
      apply sum_le_sum
      intro j hj
      have hx : (if Sum.inr j∈A then (1 : ℝ) else 0)=0 ∨
          (if Sum.inr j∈A then (1 : ℝ) else 0)=1 := by split_ifs <;> simp
      have hle : negativeResponse (F j) u v (hubs A)+
          (if Sum.inr j∈A then 1 else 0)*delta (F j) u v (hubs A)≤1 := by
        rcases response_factor_values (hF j) u v (hubs A) _ hx with h | h <;> rw [h] <;> norm_num
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hle (hw j)
    | inr j => exact hspoke u j hb
  | inr i =>
    cases b with
    | inl v => rw [delta_swap]; exact hspoke v i ha
    | inr j =>
      rw [delta_assembled_outer _ _ _ _ _ (fun he => hab (congrArg Sum.inr he)) _ ha hb]
      exact hsum

theorem IsMonotoneBoolean.integerValued {F : SetFunction H} (hF : IsMonotoneBoolean F) :
    IntegerValued F := by
  intro X
  rcases hF.values X with h | h
  · exact ⟨0,by simpa using h⟩
  · exact ⟨1,by simpa using h⟩

theorem boundaryLift_integerValued {z : SetFunction H} (hz : IntegerValued z) :
    IntegerValued (boundaryLift (J:=J) z) := fun A => hz (hubs A)

theorem branchLift_integerValued (j : J) {F : SetFunction H} (hF : IntegerValued F) :
    IntegerValued (branchLift j F) := by
  intro A
  by_cases hj : Sum.inr j∈A
  · simpa only [branchLift,if_pos hj] using hF (hubs A)
  · exact ⟨0,by simp only [branchLift,if_neg hj,Int.cast_zero]⟩

theorem assembled_integerValued {z : SetFunction H} (hz : IntegerValued z)
    (F : J → SetFunction H) (hF : ∀ j,IsMonotoneBoolean (F j)) (w : J → ℤ) :
    IntegerValued (assembled z F (fun j => (w j : ℝ))) := by
  apply (boundaryLift_integerValued hz).add
  exact IntegerValued.finset_sum univ _ (fun j _ =>
    (branchLift_integerValued j (hF j).integerValued).int_smul (w j))

/-- The exact slack bound gives an actual Minkowski complement in the sum of
the branch weights times the graphical zonotope. -/
theorem assembled_actual_summand {s k : ℕ} {z : SetFunction (Fin s)}
    (hz : TranslationNormalized z) {F : Fin k → SetFunction (Fin s)}
    (hF : ∀ j,IsMonotoneBoolean (F j)) {w : Fin k → ℝ}
    (hw : ∀ j,0≤ w j) (hc : Compatible z F w) :
    IsMinkowskiSummand (basePolytope (assembled z F w))
      ((∑ j : Fin k,w j) • graphicalZonotope (cliqueBook s k)) := by
  apply (isMinkowskiSummand_graphical_iff (assembled_normalized hz F hF w).1
    (assembled_supermodular z F hF w hw hc) (sum_nonneg (fun j _ => hw j))).mpr
  refine ⟨assembled_graphical z F w,?_⟩
  intro a b hab hedge A ha hb
  exact assembled_delta_le_weight_sum hF hw hc a b hab A ha hb

theorem assembled_lattice_complement {s k : ℕ} {z : SetFunction (Fin s)}
    (hz : TranslationNormalized z) (hzi : IntegerValued z)
    {F : Fin k → SetFunction (Fin s)} (hF : ∀ j,IsMonotoneBoolean (F j))
    (w : Fin k → ℤ) (hw : ∀ j,0≤ w j)
    (hc : Compatible z F (fun j => (w j : ℝ))) :
    LatticePolytope (basePolytope (assembled z F (fun j => (w j : ℝ)))) ∧
    ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
      basePolytope (assembled z F (fun j => (w j : ℝ)))+R=
        ((∑ j : Fin k,(w j : ℝ)) • graphicalZonotope (cliqueBook s k)) := by
  let f:=assembled z F (fun j => (w j : ℝ))
  let a : ℝ:=∑ j : Fin k,(w j : ℝ)
  have hw' : ∀ j,0≤(w j : ℝ):=fun j => by exact_mod_cast hw j
  have hn:=assembled_normalized hz F hF (fun j => (w j : ℝ))
  have hs:=assembled_supermodular z F hF (fun j => (w j : ℝ)) hw' hc
  have hi:=assembled_integerValued hzi F hF w
  have hG:=assembled_graphical z F (fun j => (w j : ℝ))
  have ha : 0≤ a:=sum_nonneg (fun j _ => hw' j)
  have hbound : ∀ u v,u≠ v → (cliqueBook s k).Adj u v → ∀ A,u∉A → v∉A →
      delta f u v A≤ a := by
    intro u v huv hedge A hu hv
    exact assembled_delta_le_weight_sum hF hw' hc u v huv A hu hv
  let g : SetFunction (Fin s⊕Fin k):=a • graphFunction (cliqueBook s k)-f
  have hgn : Normalized g := by
    change a*graphFunction (cliqueBook s k) ∅-f ∅=0
    have hf0 : f ∅=0 := hn.1
    rw [graphFunction_normalized,hf0,mul_zero,sub_self]
  have hgs : Supermodular g:=graphical_complement_supermodular hG ha hbound
  have hgi : IntegerValued g := by
    have hg0:=(graphFunction_integerValued (cliqueBook s k)).int_smul (∑ j : Fin k,w j)
    have he : ((∑ j : Fin k,w j : ℤ) : ℝ)=a := by simp only [Int.cast_sum,a]
    rw [he] at hg0
    exact hg0.sub hi
  exact ⟨hi.basePolytope hn.1 hs,basePolytope g,hgi.basePolytope hgn hgs,
    basePolytope_nonempty hgn hgs,basePolytope_add_graphical_complement hn.1 hs hG ha hbound⟩

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart142

section BundlePart143
/- Source: Papers/GraphicalZonotopes/DisjointMintermModules.lean -/




@[expose] public section
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
variable {H : Type*} [Fintype H] [DecidableEq H]

/-- The nonempty, disjoint complements of the minimal winning sets. Their
union may be smaller than `C`; the remaining variables occur in every term. -/
structure ComplementFamily (C : Finset H) (blocks : Finset (Finset H)) : Prop where
  card_two : 2≤ blocks.card
  subsets : ∀ B∈blocks,B⊆C
  nonempty : ∀ B∈blocks,B.Nonempty
  disjoint : ∀ A∈blocks,∀ B∈blocks,A≠ B → Disjoint A B

def complementModule (C : Finset H) (blocks : Finset (Finset H)) : SetFunction H :=
  fun S => if ∃ B∈blocks,C\B⊆S then 1 else 0

theorem complementModule_one_iff (C : Finset H) (blocks : Finset (Finset H)) (S : Finset H) :
    complementModule C blocks S=1 ↔ ∃ B∈blocks,C\B⊆S := by
  classical
  simp [complementModule]

theorem complementModule_zero_iff (C : Finset H) (blocks : Finset (Finset H)) (S : Finset H) :
    complementModule C blocks S=0 ↔ ¬∃ B∈blocks,C\B⊆S := by
  classical
  simp [complementModule]

theorem ComplementFamily.exists_other {C : Finset H} {blocks : Finset (Finset H)}
    (h : ComplementFamily C blocks) (A : Finset H) : ∃ B∈blocks,B≠ A := by
  by_contra hn
  push_neg at hn
  have hc : blocks.card≤1:=card_le_one.mpr (fun B hB D hD =>
    (hn B hB).trans (hn D hD).symm)
  have hh:=h.card_two
  omega

theorem ComplementFamily.shared_mem_eq {C : Finset H} {blocks : Finset (Finset H)}
    (h : ComplementFamily C blocks) {A B : Finset H} (hA : A∈blocks) (hB : B∈blocks)
    {a : H} (ha : a∈A) (hb : a∈B) : A=B := by
  by_contra hne
  exact (disjoint_left.mp (h.disjoint A hA B hB hne)) ha hb

theorem ComplementFamily.module_boolean {C : Finset H} {blocks : Finset (Finset H)}
    (h : ComplementFamily C blocks) : IsMonotoneBoolean (complementModule C blocks) := by
  classical
  refine ⟨?_,?_,?_,?_⟩
  · intro S T hST
    by_cases hs : ∃ B∈blocks,C\B⊆S
    · have ht : ∃ B∈blocks,C\B⊆T := by
        obtain ⟨B,hB,hBS⟩:=hs
        exact ⟨B,hB,hBS.trans hST⟩
      simp only [complementModule,if_pos hs,if_pos ht,le_refl]
    · simp only [complementModule,if_neg hs]
      split_ifs <;> norm_num
  · intro S
    unfold complementModule
    split_ifs <;> simp
  · apply (complementModule_zero_iff _ _ _).mpr
    rintro ⟨B,hB,hBE⟩
    obtain ⟨D,hD,hDB⟩:=h.exists_other B
    obtain ⟨a,ha⟩:=h.nonempty D hD
    have haC:=h.subsets D hD ha
    have haB : a∉B:=fun hb => (disjoint_left.mp (h.disjoint D hD B hB hDB)) ha hb
    exact notMem_empty a (hBE (mem_sdiff.mpr ⟨haC,haB⟩))
  · apply (complementModule_one_iff _ _ _).mpr
    obtain ⟨B,hB,_⟩:=h.exists_other ∅
    exact ⟨B,hB,subset_univ _⟩

/-- The complete multipartite graph on the union of the complement blocks;
vertices of `C` outside that union are isolated in this response graph. -/
def Crosses (blocks : Finset (Finset H)) (u v : H) : Prop :=
  ∃ A∈blocks,∃ B∈blocks,A≠ B ∧ u∈A ∧ v∈B

theorem Crosses.symm {blocks : Finset (Finset H)} {u v : H}
    (h : Crosses blocks u v) : Crosses blocks v u := by
  obtain ⟨A,hA,B,hB,hAB,hu,hv⟩:=h
  exact ⟨B,hB,A,hA,hAB.symm,hv,hu⟩

/-- All negative second differences are literal full-context indicators on
the crossing pairs, even when the function ignores hubs outside `C`. -/
theorem complementModule_negative_one_iff {C : Finset H} {blocks : Finset (Finset H)}
    (h : ComplementFamily C blocks) {u v : H} (huv : u≠ v) {S : Finset H}
    (hu : u∉S) (hv : v∉S) :
    negativeResponse (complementModule C blocks) u v S=1 ↔
      Crosses blocks u v ∧ C⊆insert u (insert v S) := by
  rw [negativeResponse_eq_one_iff h.module_boolean]
  simp only [complementModule_zero_iff,complementModule_one_iff]
  constructor
  · rintro ⟨hn,⟨A,hA,hAu⟩,⟨B,hB,hBv⟩⟩
    have huCA : u∈C\A := by
      by_contra hh
      apply hn
      refine ⟨A,hA,?_⟩
      intro x hx
      rcases mem_insert.mp (hAu hx) with he | he
      · exact False.elim (hh (he ▸ hx))
      · exact he
    have hvCB : v∈C\B := by
      by_contra hh
      apply hn
      refine ⟨B,hB,?_⟩
      intro x hx
      rcases mem_insert.mp (hBv hx) with he | he
      · exact False.elim (hh (he ▸ hx))
      · exact he
    have huC:=(mem_sdiff.mp huCA).1
    have hvC:=(mem_sdiff.mp hvCB).1
    have huA:=(mem_sdiff.mp huCA).2
    have hvB:=(mem_sdiff.mp hvCB).2
    have hvA : v∈A := by
      by_contra hh
      rcases mem_insert.mp (hAu (mem_sdiff.mpr ⟨hvC,hh⟩)) with he | he
      · exact huv he.symm
      · exact hv he
    have huB : u∈B := by
      by_contra hh
      rcases mem_insert.mp (hBv (mem_sdiff.mpr ⟨huC,hh⟩)) with he | he
      · exact huv he
      · exact hu he
    have hBA : B≠ A := fun he => huA (he ▸ huB)
    refine ⟨⟨B,hB,A,hA,hBA,huB,hvA⟩,?_⟩
    intro x hx
    by_cases hxA : x∈A
    · have hxB : x∉B:=fun hxB => (disjoint_left.mp
        (h.disjoint A hA B hB hBA.symm)) hxA hxB
      exact mem_insert_of_mem (hBv (mem_sdiff.mpr ⟨hx,hxB⟩))
    · exact (insert_subset_insert u (subset_insert v S))
        (hAu (mem_sdiff.mpr ⟨hx,hxA⟩))
  · rintro ⟨⟨A,hA,B,hB,hAB,huA,hvB⟩,hCS⟩
    have huC:=h.subsets A hA huA
    have hvC:=h.subsets B hB hvB
    refine ⟨?_,?_,?_⟩
    · rintro ⟨D,hD,hDS⟩
      have huD : u∈D := by
        by_contra hh
        exact hu (hDS (mem_sdiff.mpr ⟨huC,hh⟩))
      have hvD : v∈D := by
        by_contra hh
        exact hv (hDS (mem_sdiff.mpr ⟨hvC,hh⟩))
      exact hAB ((h.shared_mem_eq hA hD huA huD).trans
        (h.shared_mem_eq hD hB hvD hvB))
    · refine ⟨B,hB,?_⟩
      intro x hx
      have hxC:=(mem_sdiff.mp hx).1
      have hxB:=(mem_sdiff.mp hx).2
      rcases mem_insert.mp (hCS hxC) with he | he
      · exact mem_insert.mpr (Or.inl he)
      · rcases mem_insert.mp he with hev | heS
        · exact False.elim (hxB (hev.symm ▸ hvB))
        · exact mem_insert_of_mem heS
    · refine ⟨A,hA,?_⟩
      intro x hx
      have hxC:=(mem_sdiff.mp hx).1
      have hxA:=(mem_sdiff.mp hx).2
      rcases mem_insert.mp (hCS hxC) with he | he
      · exact False.elim (hxA (he.symm ▸ huA))
      · exact he

theorem complementModule_negative {C : Finset H} {blocks : Finset (Finset H)}
    (h : ComplementFamily C blocks) {u v : H} (huv : u≠ v) {S : Finset H}
    (hu : u∉S) (hv : v∉S) :
    negativeResponse (complementModule C blocks) u v S=
      if Crosses blocks u v ∧ C⊆insert u (insert v S) then 1 else 0 := by
  classical
  by_cases hc : Crosses blocks u v ∧ C⊆insert u (insert v S)
  · rw [if_pos hc]
    exact (complementModule_negative_one_iff h huv hu hv).mpr hc
  · rw [if_neg hc]
    rcases negativeResponse_values h.module_boolean u v S with h0 | h1
    · exact h0
    · exact False.elim (hc ((complementModule_negative_one_iff h huv hu hv).mp h1))

theorem ComplementFamily.essential {C : Finset H} {blocks : Finset (Finset H)}
    (h : ComplementFamily C blocks) {a : H} (ha : a∈C) :
    Essential (complementModule C blocks) a := by
  obtain ⟨A,hA,_⟩:=h.exists_other ∅
  obtain ⟨B,hB,haB⟩ : ∃ B∈blocks,a∉B := by
    by_cases haA : a∈A
    · obtain ⟨B,hB,hBA⟩:=h.exists_other A
      exact ⟨B,hB,fun hb => (disjoint_left.mp (h.disjoint B hB A hA hBA)) hb haA⟩
    · exact ⟨A,hA,haA⟩
  let X:=(C\B).erase a
  have hwin : complementModule C blocks (insert a X)=1 := by
    apply (complementModule_one_iff _ _ _).mpr
    refine ⟨B,hB,?_⟩
    rw [insert_erase (mem_sdiff.mpr ⟨ha,haB⟩)]
  have hlose : complementModule C blocks X=0 := by
    apply (complementModule_zero_iff _ _ _).mpr
    rintro ⟨D,hD,hDX⟩
    by_cases hDB : D=B
    · subst D
      exact notMem_erase a (C\B) (hDX (mem_sdiff.mpr ⟨ha,haB⟩))
    · obtain ⟨b,hb⟩:=h.nonempty B hB
      have hbC:=h.subsets B hB hb
      have hbD : b∉D:=fun hd => (disjoint_left.mp (h.disjoint D hD B hB hDB)) hd hb
      have hbad:=mem_of_mem_erase (hDX (mem_sdiff.mpr ⟨hbC,hbD⟩))
      exact (mem_sdiff.mp hbad).2 hb
  exact ⟨X,notMem_erase _ _,by rw [hwin,hlose,sub_zero]⟩

theorem complementModule_ignores_outside (C : Finset H) (blocks : Finset (Finset H))
    {a : H} (ha : a∉C) (S : Finset H) :
    complementModule C blocks (insert a S)=complementModule C blocks S := by
  classical
  have he : (∃ B∈blocks,C\B⊆insert a S) ↔ ∃ B∈blocks,C\B⊆S := by
    constructor
    · rintro ⟨B,hB,hBS⟩
      refine ⟨B,hB,?_⟩
      intro x hx
      rcases mem_insert.mp (hBS hx) with hxa | hxS
      · exact False.elim (ha (hxa ▸ (mem_sdiff.mp hx).1))
      · exact hxS
    · rintro ⟨B,hB,hBS⟩
      exact ⟨B,hB,hBS.trans (subset_insert _ _)⟩
  simp only [complementModule,he]

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart143

section BundlePart144
/- Source: Papers/GraphicalZonotopes/FinitePowersetTransform.lean -/






@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem delta_zeta_reduced {u v : V} (huv : u≠ v) {S : Finset V}
    (hu : u∉S) (hv : v∉S) (y : SetFunction V) :
    delta (zeta y) u v S=∑ T∈S.powerset,y (insert u (insert v T)) := by
  have huvS : u∉insert v S:=by simp only [mem_insert,not_or]; exact ⟨huv,hu⟩
  simp only [delta,zeta,sum_powerset_insert huvS,sum_powerset_insert hu,
    sum_powerset_insert hv]
  ring

namespace PowersetTransform

abbrev SubsetIndex (B : Finset V) := ↥B.powerset

/-- The full lower-set sum on the powerset of a fixed ambient finite set.
The domain is exactly all its subsets; no extension or truncation is used. -/
def lowerSum (B : Finset V) :
    (SubsetIndex B → ℝ) →ₗ[ℝ] (SubsetIndex B → ℝ) where
  toFun y S := ∑ T : SubsetIndex B,if T.1⊆S.1 then y T else 0
  map_add' y z := by
    funext S
    simp only [Pi.add_apply]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro T hT
    split_ifs <;> simp
  map_smul' a y := by
    funext S
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [mul_sum]
    apply sum_congr rfl
    intro T hT
    split_ifs <;> simp

theorem lowerSum_eq_zero_iff (B : Finset V) (y : SubsetIndex B → ℝ) :
    lowerSum B y=0 ↔ y=0 := by
  constructor
  · intro hz
    have hzero : ∀ S : Finset V,∀ hS : S⊆B,y ⟨S,mem_powerset.mpr hS⟩=0 := by
      intro S
      refine Finset.strongInductionOn S ?_
      intro S ih hS
      let s : SubsetIndex B:=⟨S,mem_powerset.mpr hS⟩
      have hs:=congrFun hz s
      change (∑ T : SubsetIndex B,if T.1⊆S then y T else 0)=0 at hs
      rw [sum_eq_single s] at hs
      · simpa only [s,Subset.rfl,ite_true] using hs
      · intro T hT hne
        by_cases hTS : T.1⊆S
        · rw [if_pos hTS]
          have hne' : T.1≠ S := by
            intro he
            apply hne
            exact Subtype.ext he
          exact ih T.1 (Finset.ssubset_iff_subset_ne.mpr ⟨hTS,hne'⟩)
            (mem_powerset.mp T.2)
        · rw [if_neg hTS]
      · simp
    funext S
    exact hzero S.1 (mem_powerset.mp S.2)
  · rintro rfl
    exact (lowerSum B).map_zero

theorem lowerSum_injective (B : Finset V) : Function.Injective (lowerSum B) := by
  intro y z he
  have hz : lowerSum B (y-z)=0 := by rw [map_sub,he,sub_self]
  exact sub_eq_zero.mp ((lowerSum_eq_zero_iff B (y-z)).mp hz)

def lowerEquiv (B : Finset V) :
    (SubsetIndex B → ℝ) ≃ₗ[ℝ] (SubsetIndex B → ℝ) :=
  LinearEquiv.ofInjectiveEndo (lowerSum B) (lowerSum_injective B)

theorem lowerSum_restriction (B : Finset V) (y : SetFunction V) (S : SubsetIndex B) :
    lowerSum B (fun T => y T.1) S=∑ T∈S.1.powerset,y T := by
  change (∑ T : SubsetIndex B,if T.1⊆S.1 then y T.1 else 0)=_
  rw [← sum_filter]
  apply sum_bij (fun T _ => T.1)
  · intro T hT
    exact mem_powerset.mpr (mem_filter.mp hT).2
  · intro T hT U hU he
    exact Subtype.ext he
  · intro T hT
    let t : SubsetIndex B:=⟨T,mem_powerset.mpr
      ((mem_powerset.mp hT).trans (mem_powerset.mp S.2))⟩
    exact ⟨t,mem_filter.mpr ⟨mem_univ t,mem_powerset.mp hT⟩,rfl⟩
  · intro T hT
    rfl

/-- Triangular inversion preserves every coefficient subring, in particular
the integer lattice. This is proved from the inverse equations themselves. -/
theorem lowerEquiv_symm_mem_subring (B : Finset V) (K : Subring ℝ)
    (x : SubsetIndex B → ℝ) (hx : ∀ S,x S∈K) :
    ∀ S,(lowerEquiv B).symm x S∈K := by
  let y:=(lowerEquiv B).symm x
  have he : lowerSum B y=x:=(lowerEquiv B).apply_symm_apply x
  have hmem : ∀ S : Finset V,∀ hS : S⊆B,y ⟨S,mem_powerset.mpr hS⟩∈K := by
    intro S
    refine Finset.strongInductionOn S ?_
    intro S ih hS
    let s : SubsetIndex B:=⟨S,mem_powerset.mpr hS⟩
    have hs:=congrFun he s
    change (∑ T : SubsetIndex B,if T.1⊆S then y T else 0)=x s at hs
    rw [← sum_erase_add _ _ (mem_univ s)] at hs
    have hlast : (if s.1⊆S then y s else 0)=y s:=if_pos Subset.rfl
    rw [hlast] at hs
    have hsum : (∑ T∈(univ : Finset (SubsetIndex B)).erase s,
        if T.1⊆S then y T else 0)∈K := by
      apply K.sum_mem
      intro T hT
      by_cases hTS : T.1⊆S
      · rw [if_pos hTS]
        have hne : T.1≠ S := by
          intro he
          exact (ne_of_mem_erase hT) (Subtype.ext he)
        exact ih T.1 (Finset.ssubset_iff_subset_ne.mpr ⟨hTS,hne⟩) (mem_powerset.mp T.2)
      · rw [if_neg hTS]
        exact K.zero_mem
    have hy : y s=x s-(∑ T∈(univ : Finset (SubsetIndex B)).erase s,
        if T.1⊆S then y T else 0) := by linarith
    rw [hy]
    exact K.sub_mem (hx s) hsum
  intro S
  exact hmem S.1 (mem_powerset.mp S.2)

end PowersetTransform
end GraphicalZonotopes

end
end
end BundlePart144

section BundlePart145
/- Source: Papers/GraphicalZonotopes/BooleanResponseCoordinates.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset PowersetTransform
open scoped BigOperators
variable {H J : Type*} [Fintype H] [LinearOrder H] [Fintype J] [DecidableEq J]

/-- The multilinear expansion is the full powerset zeta transform separately
on each genuine pair row. This is an invertible change of coordinates. -/
def rowLowerEquiv : (HubResponseRow H → ℝ) ≃ₗ[ℝ] (HubResponseRow H → ℝ) where
  toFun y r := lowerEquiv (commonNeighbors (⊤ : SimpleGraph H) r.1.1.1 r.1.1.2)
    (fun T => y ⟨r.1,T⟩) r.2
  invFun y r := (lowerEquiv (commonNeighbors (⊤ : SimpleGraph H) r.1.1.1 r.1.1.2)).symm
    (fun T => y ⟨r.1,T⟩) r.2
  left_inv y := by
    funext r
    rcases r with ⟨e,S⟩
    exact congrFun ((lowerEquiv (commonNeighbors (⊤ : SimpleGraph H) e.1.1 e.1.2)).symm_apply_apply
      (fun T => y ⟨e,T⟩)) S
  right_inv y := by
    funext r
    rcases r with ⟨e,S⟩
    exact congrFun ((lowerEquiv (commonNeighbors (⊤ : SimpleGraph H) e.1.1 e.1.2)).apply_symm_apply
      (fun T => y ⟨e,T⟩)) S
  map_add' y z := by
    funext r
    exact congrFun ((lowerEquiv (commonNeighbors (⊤ : SimpleGraph H) r.1.1.1 r.1.1.2)).map_add
      (fun T => y ⟨r.1,T⟩) (fun T => z ⟨r.1,T⟩)) r.2
  map_smul' c y := by
    funext r
    exact congrFun ((lowerEquiv (commonNeighbors (⊤ : SimpleGraph H) r.1.1.1 r.1.1.2)).map_smul c
      (fun T => y ⟨r.1,T⟩)) r.2

def rowClique (r : HubResponseRow H) : Finset H:=
  insert r.1.1.1 (insert r.1.1.2 r.2.1)

theorem rowClique_card (r : HubResponseRow H) : 2≤(rowClique r).card := by
  have hsub : ({r.1.1.1,r.1.1.2} : Finset H)⊆rowClique r := by
    simp only [rowClique,insert_subset_iff,singleton_subset_iff,mem_insert,true_or,or_true,and_self]
  have hc:=card_le_card hsub
  rwa [card_pair (ne_of_lt r.1.2.1)] at hc

def rowCliqueIndex (r : HubResponseRow H) : CliqueIndex (⊤ : SimpleGraph H) :=
  ⟨rowClique r,rowClique_card r,by
    intro u hu v hv huv
    exact (SimpleGraph.top_adj u v).mpr huv⟩

theorem rowCliqueIndex_surjective : Function.Surjective (rowCliqueIndex (H:=H)) := by
  intro C
  have hpair : ∀ u v,u∈C.1 → v∈C.1 → u< v → ∃ r : HubResponseRow H,rowCliqueIndex r=C := by
    intro u v huC hvC huv
    let T:=(C.1.erase u).erase v
    have hT : T⊆commonNeighbors (⊤ : SimpleGraph H) u v := by
      intro a ha
      have hne:=mem_erase.mp ha
      have hne':=mem_erase.mp hne.2
      exact (mem_commonNeighbors _ _ _ _).mpr
        ⟨(SimpleGraph.top_adj _ _).mpr hne'.1.symm,(SimpleGraph.top_adj _ _).mpr hne.1.symm⟩
    let e : OrientedEdge (⊤ : SimpleGraph H):=
      ⟨(u,v),huv,(SimpleGraph.top_adj u v).mpr (ne_of_lt huv)⟩
    let r : HubResponseRow H:=⟨e,⟨T,mem_powerset.mpr hT⟩⟩
    refine ⟨r,Subtype.ext ?_⟩
    change insert u (insert v ((C.1.erase u).erase v))=C.1
    ext a
    by_cases hau : a=u
    · subst a
      simp [huC]
    · by_cases hav : a=v
      · subst a
        simp [hvC]
      · simp [hau,hav]
  have hcard : 2≤ C.1.card := C.2.1
  obtain ⟨u,hu,v,hv,huv⟩:=one_lt_card.mp (show 1< C.1.card by omega)
  rcases lt_or_gt_of_ne huv with hlt | hgt
  · exact hpair u v hu hv hlt
  · exact hpair v u hv hu hgt

/-- A central Möbius coefficient is repeated once for each pair contained in
its clique. This map includes the pair blocks as well as all higher blocks. -/
def repeatCoefficients : (CliqueIndex (⊤ : SimpleGraph H) → ℝ) →ₗ[ℝ]
    (HubResponseRow H → ℝ) where
  toFun c r := c (rowCliqueIndex r)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coefficient_at_row (c : CliqueIndex (⊤ : SimpleGraph H) → ℝ)
    (r : HubResponseRow H) :
    coefficientsFromCoordinates ⊤ c (rowClique r)=c (rowCliqueIndex r) := by
  unfold coefficientsFromCoordinates
  split_ifs with h
  · rfl
  · exact (h (rowCliqueIndex r).2).elim

/-- This is the actual central elemental map in multilinear response
coordinates, not an independently postulated compatibility condition. -/
theorem rowLower_repeatCoefficients (c : CliqueIndex (⊤ : SimpleGraph H) → ℝ) :
    rowLowerEquiv (repeatCoefficients c)=centralCoefficientSlack c := by
  funext r
  let B:=commonNeighbors (⊤ : SimpleGraph H) r.1.1.1 r.1.1.2
  let y:=coefficientsFromCoordinates (⊤ : SimpleGraph H) c
  have hu : r.1.1.1∉r.2.1 := by
    intro h
    exact not_mem_commonNeighbors_left ⊤ _ _ ((mem_powerset.mp r.2.2) h)
  have hv : r.1.1.2∉r.2.1 := by
    intro h
    exact not_mem_commonNeighbors_right ⊤ _ _ ((mem_powerset.mp r.2.2) h)
  change lowerSum B (fun T => c (rowCliqueIndex ⟨r.1,T⟩)) r.2=
    delta (zeta y) r.1.1.1 r.1.1.2 r.2.1
  calc
    _=lowerSum B (fun T => y (insert r.1.1.1 (insert r.1.1.2 T.1))) r.2 := by
      have he : (fun T : SubsetIndex B => c (rowCliqueIndex ⟨r.1,T⟩))=
          (fun T : SubsetIndex B => y (insert r.1.1.1 (insert r.1.1.2 T.1))) := by
        funext T
        exact (coefficient_at_row c ⟨r.1,T⟩).symm
      rw [he]
    _=∑ T∈r.2.1.powerset,y (insert r.1.1.1 (insert r.1.1.2 T)) :=
      lowerSum_restriction B (fun T => y (insert r.1.1.1 (insert r.1.1.2 T))) r.2
    _=_ := (delta_zeta_reduced (ne_of_lt r.1.2.1) hu hv y).symm

/-- Being in the diagonal line of each clique block means exactly that all
copies of the same central Möbius coefficient agree. -/
def BlockConstant (x : HubResponseRow H → ℝ) : Prop :=
  ∀ r t,rowCliqueIndex r=rowCliqueIndex t → x r=x t

theorem blockConstant_iff_range_repeatCoefficients (x : HubResponseRow H → ℝ) :
    BlockConstant x ↔ x∈LinearMap.range (repeatCoefficients (H:=H)) := by
  constructor
  · intro hx
    choose pick hpick using (rowCliqueIndex_surjective (H:=H))
    refine ⟨fun C => x (pick C),?_⟩
    funext r
    exact hx (pick (rowCliqueIndex r)) r (hpick (rowCliqueIndex r))
  · rintro ⟨c,rfl⟩ r t he
    exact congrArg c he

/-- Integrability is equivalent to independent within-block agreement after
the invertible pairwise Möbius expansion. Consequently there are no hidden
relations between different clique blocks. -/
theorem central_range_iff_blockConstant (x : HubResponseRow H → ℝ) :
    x∈LinearMap.range (centralCoefficientSlack (H:=H)) ↔
      BlockConstant (rowLowerEquiv.symm x) := by
  rw [blockConstant_iff_range_repeatCoefficients]
  constructor
  · rintro ⟨c,rfl⟩
    refine ⟨c,?_⟩
    rw [← rowLower_repeatCoefficients,rowLowerEquiv.symm_apply_apply]
  · rintro ⟨c,hc⟩
    refine ⟨c,?_⟩
    rw [← rowLower_repeatCoefficients,hc,rowLowerEquiv.apply_symm_apply]

theorem integrable_iff_blockConstant (F : J → SetFunction H) (w : J → ℝ) :
    (∃ z : SetFunction H,TranslationNormalized z ∧ Compatible z F w) ↔
      BlockConstant (rowLowerEquiv.symm (weightedResponse F w)) := by
  rw [← mem_quotientRelation_ker_iff]
  change (LinearMap.range (centralCoefficientSlack (H:=H))).mkQ
    (weightedResponse F w)=0 ↔ _
  rw [← LinearMap.mem_ker,Submodule.ker_mkQ,central_range_iff_blockConstant]

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart145

section BundlePart146
/- Source: Papers/GraphicalZonotopes/PureBooleanResponses.lean -/





@[expose] public section
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace BooleanModule
open Finset PowersetTransform
open scoped BigOperators
variable {H : Type*} [Fintype H] [LinearOrder H]

theorem rowLower_raw_coefficients (y : SetFunction H) :
    rowLowerEquiv (fun r => y (rowClique r))=
      (fun r : HubResponseRow H => delta (zeta y) r.1.1.1 r.1.1.2 r.2.1) := by
  funext r
  have hu : r.1.1.1∉r.2.1 := by
    intro hm
    exact not_mem_commonNeighbors_left ⊤ _ _ ((mem_powerset.mp r.2.2) hm)
  have hv : r.1.1.2∉r.2.1 := by
    intro hm
    exact not_mem_commonNeighbors_right ⊤ _ _ ((mem_powerset.mp r.2.2) hm)
  change lowerSum (commonNeighbors (⊤ : SimpleGraph H) r.1.1.1 r.1.1.2)
    (fun T => y (insert r.1.1.1 (insert r.1.1.2 T.1))) r.2=_
  rw [lowerSum_restriction _ (fun T : Finset H => y (insert r.1.1.1 (insert r.1.1.2 T))) r.2]
  exact (delta_zeta_reduced (ne_of_lt r.1.2.1) hu hv y).symm

theorem rowLower_edge_mul (q : OrientedEdge (⊤ : SimpleGraph H) → ℝ)
    (y : HubResponseRow H → ℝ) :
    rowLowerEquiv (fun r => q r.1*y r)=fun r => q r.1*rowLowerEquiv y r := by
  funext r
  exact congrFun ((lowerEquiv (commonNeighbors (⊤ : SimpleGraph H) r.1.1.1 r.1.1.2)).map_smul
    (q r.1) (fun T => y ⟨r.1,T⟩)) r.2

theorem zeta_delta_coordinate (C : Finset H) :
    zeta (fun D : Finset H => if D=C then 1 else 0)=setMonomial C := by
  funext A
  by_cases hC : C⊆A <;> simp [zeta,setMonomial,hC]

/-- The raw response coefficient array of a disjoint-minterm module has one
clique block and the exact complete-multipartite pair indicator in that block. -/
theorem complementModule_response_coefficients {C : Finset H} {blocks : Finset (Finset H)}
    (h : ComplementFamily C blocks) :
    rowLowerEquiv.symm (responseVector (complementModule C blocks))=
      fun r : HubResponseRow H =>
        if rowClique r=C ∧ Crosses blocks r.1.1.1 r.1.1.2 then 1 else 0 := by
  classical
  let q : OrientedEdge (⊤ : SimpleGraph H) → ℝ:=
    fun e => if Crosses blocks e.1.1 e.1.2 then 1 else 0
  let y : HubResponseRow H → ℝ:=fun r => if rowClique r=C then 1 else 0
  have he : (fun r : HubResponseRow H =>
      if rowClique r=C ∧ Crosses blocks r.1.1.1 r.1.1.2 then (1 : ℝ) else 0)=
      fun r => q r.1*y r := by
    funext r
    by_cases hc : rowClique r=C <;>
      by_cases he : Crosses blocks r.1.1.1 r.1.1.2 <;> simp [q,y,hc,he]
  rw [he]
  apply rowLowerEquiv.injective
  rw [rowLowerEquiv.apply_symm_apply,rowLower_edge_mul]
  have hmon : rowLowerEquiv y=
      fun r : HubResponseRow H => delta (setMonomial C) r.1.1.1 r.1.1.2 r.2.1 := by
    simpa only [y,zeta_delta_coordinate] using
      rowLower_raw_coefficients (fun D : Finset H => if D=C then 1 else 0)
  rw [hmon]
  funext r
  have hu : r.1.1.1∉r.2.1 := by
    intro hm
    exact not_mem_commonNeighbors_left ⊤ _ _ ((mem_powerset.mp r.2.2) hm)
  have hv : r.1.1.2∉r.2.1 := by
    intro hm
    exact not_mem_commonNeighbors_right ⊤ _ _ ((mem_powerset.mp r.2.2) hm)
  change negativeResponse (complementModule C blocks) r.1.1.1 r.1.1.2 r.2.1=
    q r.1*delta (setMonomial C) r.1.1.1 r.1.1.2 r.2.1
  rw [complementModule_negative h (ne_of_lt r.1.2.1) hu hv,
    delta_setMonomial (ne_of_lt r.1.2.1) hu hv]
  by_cases he : Crosses blocks r.1.1.1 r.1.1.2
  · obtain ⟨A,hA,B,hB,hAB,ha,hb⟩:=he
    have haC:=h.subsets A hA ha
    have hbC:=h.subsets B hB hb
    have hcross : Crosses blocks r.1.1.1 r.1.1.2 := ⟨A,hA,B,hB,hAB,ha,hb⟩
    simp only [q,hcross,one_mul,haC,hbC,true_and,ite_true]
  · simp only [q,he,zero_mul,false_and,ite_false]

def positivePairBlocks (u v : H) : Finset (Finset H):={{u},{v}}

theorem positivePairBlocks_family (C : Finset H) {u v : H}
    (hu : u∈C) (hv : v∈C) (huv : u≠ v) :
    ComplementFamily C (positivePairBlocks u v) := by
  classical
  refine ⟨?_,?_,?_,?_⟩
  · simp [positivePairBlocks,huv]
  · intro B hB
    simp only [positivePairBlocks,mem_insert,mem_singleton] at hB
    rcases hB with rfl | rfl
    · simpa only [singleton_subset_iff] using hu
    · simpa only [singleton_subset_iff] using hv
  · intro B hB
    simp only [positivePairBlocks,mem_insert,mem_singleton] at hB
    rcases hB with rfl | rfl <;> exact singleton_nonempty _
  · intro A hA B hB hAB
    simp only [positivePairBlocks,mem_insert,mem_singleton] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · exact False.elim (hAB rfl)
    · simp [huv]
    · simp [huv.symm]
    · exact False.elim (hAB rfl)

theorem crosses_positivePairBlocks {u v : H} (huv : u≠ v) (a b : H) :
    Crosses (positivePairBlocks u v) a b ↔
      (a=u ∧ b=v) ∨ (a=v ∧ b=u) := by
  classical
  constructor
  · rintro ⟨A,hA,B,hB,hAB,ha,hb⟩
    simp only [positivePairBlocks,mem_insert,mem_singleton] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · exact False.elim (hAB rfl)
    · exact Or.inl ⟨mem_singleton.mp ha,mem_singleton.mp hb⟩
    · exact Or.inr ⟨mem_singleton.mp ha,mem_singleton.mp hb⟩
    · exact False.elim (hAB rfl)
  · rintro (⟨ha,hb⟩ | ⟨ha,hb⟩)
    · subst a; subst b
      exact ⟨{u},by simp [positivePairBlocks],{v},by simp [positivePairBlocks],
        by simpa using huv,mem_singleton_self _,mem_singleton_self _⟩
    · subst a; subst b
      exact ⟨{v},by simp [positivePairBlocks],{u},by simp [positivePairBlocks],
        by simpa using huv.symm,mem_singleton_self _,mem_singleton_self _⟩

def positivePairModule (C : Finset H) (u v : H) : SetFunction H:=
  complementModule C (positivePairBlocks u v)

/-- The pure positive module of Lemma7.4, with every ambient hub retained. -/
theorem positivePairModule_coefficients (C : Finset H) {u v : H}
    (hu : u∈C) (hv : v∈C) (huv : u< v) :
    rowLowerEquiv.symm (responseVector (positivePairModule C u v))=
      fun r : HubResponseRow H =>
        if rowClique r=C ∧ r.1.1.1=u ∧ r.1.1.2=v then 1 else 0 := by
  rw [positivePairModule,complementModule_response_coefficients
    (positivePairBlocks_family C hu hv (ne_of_lt huv))]
  funext r
  rw [crosses_positivePairBlocks (ne_of_lt huv)]
  have hn : ¬(r.1.1.1=v ∧ r.1.1.2=u) := by
    rintro ⟨ha,hb⟩
    have hh:=r.1.2.1
    rw [ha,hb] at hh
    exact (not_lt_of_ge huv.le) hh
  simp only [or_false,hn,and_assoc]

theorem positivePairModule_essential (C : Finset H) {u v : H}
    (hu : u∈C) (hv : v∈C) (huv : u≠ v) {a : H} (ha : a∈C) :
    Essential (positivePairModule C u v) a :=
  (positivePairBlocks_family C hu hv huv).essential ha

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart146

section BundlePart147
/- Source: Papers/GraphicalZonotopes/NegativePureBooleanResponses.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
variable {H : Type*} [Fintype H] [LinearOrder H]

def negativePairBlocks (C : Finset H) (u v : H) : Finset (Finset H):=
  insert {u,v} ((C\{u,v}).image singleton)

theorem mem_negativePairBlocks (C : Finset H) (u v : H) (B : Finset H) :
    B∈negativePairBlocks C u v ↔
      B={u,v} ∨ ∃ a,a∈C ∧ a≠ u ∧ a≠ v ∧ B={a} := by
  constructor
  · intro hB
    rcases mem_insert.mp hB with he | he
    · exact Or.inl he
    · obtain ⟨a,ha,he⟩:=mem_image.mp he
      have ha':=mem_sdiff.mp ha
      have hn : a≠ u ∧ a≠ v:=by simpa only [mem_insert,mem_singleton,not_or] using ha'.2
      exact Or.inr ⟨a,ha'.1,hn.1,hn.2,he.symm⟩
  · rintro (he | ⟨a,ha,hau,hav,he⟩)
    · exact mem_insert.mpr (Or.inl he)
    · apply mem_insert_of_mem
      exact mem_image.mpr ⟨a,mem_sdiff.mpr ⟨ha,by simp [hau,hav]⟩,he.symm⟩

theorem negativePairBlocks_family (C : Finset H) (hC : 3≤ C.card) {u v : H}
    (hu : u∈C) (hv : v∈C) (huv : u≠ v) :
    ComplementFamily C (negativePairBlocks C u v) := by
  have hpair : ({u,v} : Finset H)⊆C:=by simp [insert_subset_iff,singleton_subset_iff,hu,hv]
  have hdiff : (C\{u,v}).Nonempty := by
    apply card_pos.mp
    rw [card_sdiff_of_subset hpair,card_pair huv]
    omega
  obtain ⟨a,ha⟩:=hdiff
  have ha':=mem_sdiff.mp ha
  have hauv : a≠ u ∧ a≠ v:=by simpa only [mem_insert,mem_singleton,not_or] using ha'.2
  have hpairmem : ({u,v} : Finset H)∈negativePairBlocks C u v:=by
    exact (mem_negativePairBlocks _ _ _ _).mpr (Or.inl rfl)
  have hasingle : ({a} : Finset H)∈negativePairBlocks C u v:=
    (mem_negativePairBlocks _ _ _ _).mpr (Or.inr ⟨a,ha'.1,hauv.1,hauv.2,rfl⟩)
  have hne : ({u,v} : Finset H)≠{a} := by
    intro he
    have hc:=congrArg Finset.card he
    rw [card_pair huv,card_singleton] at hc
    omega
  refine ⟨?_,?_,?_,?_⟩
  · have hh : 1<(negativePairBlocks C u v).card:=
      one_lt_card.mpr ⟨{u,v},hpairmem,{a},hasingle,hne⟩
    omega
  · intro B hB
    rcases (mem_negativePairBlocks _ _ _ _).mp hB with rfl | ⟨b,hb,hbu,hbv,rfl⟩
    · exact hpair
    · exact singleton_subset_iff.mpr hb
  · intro B hB
    rcases (mem_negativePairBlocks _ _ _ _).mp hB with rfl | ⟨b,hb,hbu,hbv,rfl⟩
    · exact ⟨u,by simp⟩
    · exact singleton_nonempty b
  · intro A hA B hB hAB
    rcases (mem_negativePairBlocks _ _ _ _).mp hA with rfl | ⟨a,ha,hau,hav,rfl⟩
    · rcases (mem_negativePairBlocks _ _ _ _).mp hB with rfl | ⟨b,hb,hbu,hbv,rfl⟩
      · exact False.elim (hAB rfl)
      · simp [hbu,hbv,Ne.symm hbu,Ne.symm hbv]
    · rcases (mem_negativePairBlocks _ _ _ _).mp hB with rfl | ⟨b,hb,hbu,hbv,rfl⟩
      · simp [hau,hav,Ne.symm hau,Ne.symm hav]
      · have hab : a≠ b:=fun he => hAB (congrArg singleton he)
        simp [hab]

theorem crosses_negativePairBlocks (C : Finset H) (hC : 3≤ C.card) {u v : H}
    (hu : u∈C) (hv : v∈C) (huv : u≠ v) (a b : H) :
    Crosses (negativePairBlocks C u v) a b ↔
      a∈C ∧ b∈C ∧ a≠ b ∧ ¬(a∈({u,v} : Finset H) ∧ b∈({u,v} : Finset H)) := by
  let hfamily:=negativePairBlocks_family C hC hu hv huv
  have hpairmem : ({u,v} : Finset H)∈negativePairBlocks C u v:=
    (mem_negativePairBlocks _ _ _ _).mpr (Or.inl rfl)
  have hsingle : ∀ x,x∈C → x∉({u,v} : Finset H) →
      ({x} : Finset H)∈negativePairBlocks C u v := by
    intro x hx hxn
    have hn : x≠ u ∧ x≠ v:=by simpa only [mem_insert,mem_singleton,not_or] using hxn
    exact (mem_negativePairBlocks _ _ _ _).mpr (Or.inr ⟨x,hx,hn.1,hn.2,rfl⟩)
  constructor
  · rintro ⟨A,hA,B,hB,hAB,ha,hb⟩
    refine ⟨hfamily.subsets A hA ha,hfamily.subsets B hB hb,?_,?_⟩
    · intro he
      exact hAB (hfamily.shared_mem_eq hA hB ha (he.symm ▸ hb))
    · rintro ⟨hap,hbp⟩
      exact hAB ((hfamily.shared_mem_eq hA hpairmem ha hap).trans
        (hfamily.shared_mem_eq hpairmem hB hbp hb))
  · rintro ⟨ha,hb,hab,hnot⟩
    by_cases hap : a∈({u,v} : Finset H)
    · have hbp : b∉({u,v} : Finset H):=fun hh => hnot ⟨hap,hh⟩
      refine ⟨{u,v},hpairmem,{b},hsingle b hb hbp,?_,hap,mem_singleton_self b⟩
      intro he
      exact hbp (he.symm ▸ mem_singleton_self b)
    · by_cases hbp : b∈({u,v} : Finset H)
      · refine ⟨{a},hsingle a ha hap,{u,v},hpairmem,?_,mem_singleton_self a,hbp⟩
        intro he
        exact hap (he ▸ mem_singleton_self a)
      · exact ⟨{a},hsingle a ha hap,{b},hsingle b hb hbp,
          fun he => hab (singleton_injective he),mem_singleton_self a,mem_singleton_self b⟩

def negativePairModule (C : Finset H) (u v : H) : SetFunction H:=
  complementModule C (negativePairBlocks C u v)

theorem ordered_pair_membership {a b u v : H} (hab : a< b) (huv : u< v) :
    (a∈({u,v} : Finset H) ∧ b∈({u,v} : Finset H)) ↔ a=u ∧ b=v := by
  simp only [mem_insert,mem_singleton]
  constructor
  · rintro ⟨ha,hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact False.elim ((lt_irrefl _) hab)
    · exact ⟨rfl,rfl⟩
    · exact False.elim ((not_lt_of_ge huv.le) hab)
    · exact False.elim ((lt_irrefl _) hab)
  · rintro ⟨rfl,rfl⟩
    exact ⟨Or.inl rfl,Or.inr rfl⟩

/-- The negative pure module has every coordinate in its clique block except
the specified pair. Modulo the diagonal this is the negative pair class. -/
theorem negativePairModule_coefficients (C : Finset H) (hC : 3≤ C.card) {u v : H}
    (hu : u∈C) (hv : v∈C) (huv : u< v) :
    rowLowerEquiv.symm (responseVector (negativePairModule C u v))=
      fun r : HubResponseRow H =>
        if rowClique r=C ∧ ¬(r.1.1.1=u ∧ r.1.1.2=v) then 1 else 0 := by
  rw [negativePairModule,complementModule_response_coefficients
    (negativePairBlocks_family C hC hu hv (ne_of_lt huv))]
  funext r
  rw [crosses_negativePairBlocks C hC hu hv (ne_of_lt huv),
    ordered_pair_membership r.1.2.1 huv]
  by_cases hrow : rowClique r=C
  · have ha : r.1.1.1∈C:=by rw [← hrow]; simp [rowClique]
    have hb : r.1.1.2∈C:=by rw [← hrow]; simp [rowClique]
    have hne : r.1.1.1≠ r.1.1.2 := ne_of_lt r.1.2.1
    simp [hrow,ha,hb,hne]
  · simp only [hrow,false_and,ite_false]

theorem negativePairModule_essential (C : Finset H) (hC : 3≤ C.card) {u v : H}
    (hu : u∈C) (hv : v∈C) (huv : u≠ v) {a : H} (ha : a∈C) :
    Essential (negativePairModule C u v) a :=
  (negativePairBlocks_family C hC hu hv huv).essential ha

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart147

section BundlePart148
/- Source: Papers/GraphicalZonotopes/PureResponseClasses.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
variable {H : Type*} [Fintype H] [LinearOrder H]

abbrev ResponseQuotient (H : Type*) [Fintype H] [LinearOrder H] :=
  (HubResponseRow H → ℝ) ⧸ LinearMap.range (centralCoefficientSlack (H:=H))

def responseClass (F : SetFunction H) : ResponseQuotient H :=
  (LinearMap.range (centralCoefficientSlack (H:=H))).mkQ (responseVector F)

def coefficientClass : (HubResponseRow H → ℝ) →ₗ[ℝ] ResponseQuotient H :=
  (LinearMap.range (centralCoefficientSlack (H:=H))).mkQ ∘ₗ rowLowerEquiv.toLinearMap

def pureCoordinate (C : Finset H) (u v : H) : ResponseQuotient H :=
  coefficientClass (fun r : HubResponseRow H =>
    if rowClique r=C ∧ r.1.1.1=u ∧ r.1.1.2=v then 1 else 0)

theorem responseClass_eq_coefficientClass (F : SetFunction H) :
    responseClass F=coefficientClass (rowLowerEquiv.symm (responseVector F)) := by
  simp only [coefficientClass,LinearMap.comp_apply,LinearEquiv.coe_coe,
    rowLowerEquiv.apply_symm_apply,responseClass]

theorem coefficientClass_eq_zero_iff (x : HubResponseRow H → ℝ) :
    coefficientClass x=0 ↔ BlockConstant x := by
  change (LinearMap.range (centralCoefficientSlack (H:=H))).mkQ (rowLowerEquiv x)=0 ↔ _
  rw [← LinearMap.mem_ker,Submodule.ker_mkQ,central_range_iff_blockConstant,
    rowLowerEquiv.symm_apply_apply]

/-- The common coordinate in a block is exactly a central coefficient and
vanishes in the response quotient, including all pair and higher blocks. -/
theorem coefficientClass_block_zero (C : Finset H) :
    coefficientClass (fun r : HubResponseRow H => if rowClique r=C then 1 else 0)=0 := by
  apply (coefficientClass_eq_zero_iff _).mpr
  intro r t he
  have hv : rowClique r=rowClique t:=congrArg Subtype.val he
  change (if rowClique r=C then (1 : ℝ) else 0)=(if rowClique t=C then 1 else 0)
  rw [hv]

theorem positivePairModule_class (C : Finset H) {u v : H}
    (hu : u∈C) (hv : v∈C) (huv : u< v) :
    responseClass (positivePairModule C u v)=pureCoordinate C u v := by
  rw [responseClass_eq_coefficientClass,positivePairModule_coefficients C hu hv huv]
  rfl

theorem negativePairModule_class (C : Finset H) (hC : 3≤ C.card) {u v : H}
    (hu : u∈C) (hv : v∈C) (huv : u< v) :
    responseClass (negativePairModule C u v)= -pureCoordinate C u v := by
  rw [responseClass_eq_coefficientClass,negativePairModule_coefficients C hC hu hv huv]
  have he : (fun r : HubResponseRow H =>
      if rowClique r=C ∧ ¬(r.1.1.1=u ∧ r.1.1.2=v) then (1 : ℝ) else 0)=
      (fun r : HubResponseRow H => if rowClique r=C then 1 else 0)-
        (fun r : HubResponseRow H =>
          if rowClique r=C ∧ r.1.1.1=u ∧ r.1.1.2=v then 1 else 0) := by
    funext r
    by_cases hr : rowClique r=C <;>
      by_cases hp : r.1.1.1=u ∧ r.1.1.2=v <;> simp [hr,hp,and_assoc]
  rw [he,map_sub,coefficientClass_block_zero,zero_sub]
  rfl

/-- Lemma7.4 with its actual quotient classes, all variables of `C`
essential, and every other ambient variable explicitly ignored. -/
theorem both_signs_of_pure_coordinate (C : Finset H) (hC : 3≤ C.card) {u v : H}
    (hu : u∈C) (hv : v∈C) (huv : u< v) :
    ∃ P R : SetFunction H,
      IsMonotoneBoolean P ∧ IsMonotoneBoolean R ∧
      (∀ a∈C,Essential P a ∧ Essential R a) ∧
      (∀ a,a∉C → ∀ X,P (insert a X)=P X ∧ R (insert a X)=R X) ∧
      responseClass P=pureCoordinate C u v ∧ responseClass R= -pureCoordinate C u v := by
  refine ⟨positivePairModule C u v,negativePairModule C u v,
    (positivePairBlocks_family C hu hv (ne_of_lt huv)).module_boolean,
    (negativePairBlocks_family C hC hu hv (ne_of_lt huv)).module_boolean,?_,?_,
    positivePairModule_class C hu hv huv,negativePairModule_class C hC hu hv huv⟩
  · intro a ha
    exact ⟨positivePairModule_essential C hu hv (ne_of_lt huv) ha,
      negativePairModule_essential C hC hu hv (ne_of_lt huv) ha⟩
  · intro a ha X
    exact ⟨complementModule_ignores_outside C _ ha X,
      complementModule_ignores_outside C _ ha X⟩

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart148

section BundlePart149
/- Source: Papers/GraphicalZonotopes/BlockPairCoordinates.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H J : Type*} [Fintype H] [LinearOrder H] [Fintype J]

/-- All actual unordered pairs of a fixed clique, represented by the ambient
linear order. No pair is omitted from the quotient block. -/
abbrev PairIn (C : Finset H) :=
  {e : OrientedEdge (⊤ : SimpleGraph H) // e.1.1∈C ∧ e.1.2∈C}

def pairRow (C : Finset H) (e : PairIn C) : HubResponseRow H :=
  ⟨e.1,⟨(C.erase e.1.1.1).erase e.1.1.2,mem_powerset.mpr (by
    intro a ha
    obtain ⟨ha₂,ha'⟩:=mem_erase.mp ha
    obtain ⟨ha₁,_⟩:=mem_erase.mp ha'
    exact (mem_commonNeighbors _ _ _ _).mpr
      ⟨(SimpleGraph.top_adj _ _).mpr ha₁.symm,
        (SimpleGraph.top_adj _ _).mpr ha₂.symm⟩)⟩⟩

@[simp] theorem pairRow_edge (C : Finset H) (e : PairIn C) :
    (pairRow C e).1=e.1 := rfl

@[simp] theorem rowClique_pairRow (C : Finset H) (e : PairIn C) :
    rowClique (pairRow C e)=C := by
  change insert e.1.1.1 (insert e.1.1.2 ((C.erase e.1.1.1).erase e.1.1.2))=C
  ext a
  by_cases ha₁ : a=e.1.1.1
  · subst a
    simp [e.2.1]
  · by_cases ha₂ : a=e.1.1.2
    · subst a
      simp [e.2.2]
    · simp [mem_erase,ha₁,ha₂]

def pairAtRow (C : Finset H) (r : HubResponseRow H) (h : rowClique r=C) : PairIn C :=
  ⟨r.1,by
    rw [← h]
    exact ⟨mem_insert_self _ _,mem_insert_of_mem (mem_insert_self _ _)⟩⟩

/-- A vector on the pairs of `C` as an array in the full response-coordinate
space, with all other clique blocks explicitly zero. -/
def blockCoordinates (C : Finset H) : (PairIn C → ℝ) →ₗ[ℝ] (HubResponseRow H → ℝ) where
  toFun x r := if h : rowClique r=C then x (pairAtRow C r h) else 0
  map_add' x y := by
    funext r
    by_cases h : rowClique r=C <;> simp only [h,dite_true,dite_false,Pi.add_apply,add_zero]
  map_smul' c x := by
    funext r
    by_cases h : rowClique r=C <;>
      simp only [h,dite_true,dite_false,Pi.smul_apply,smul_eq_mul,mul_zero,RingHom.id_apply]

@[simp] theorem blockCoordinates_pairRow (C : Finset H) (x : PairIn C → ℝ)
    (e : PairIn C) : blockCoordinates C x (pairRow C e)=x e := by
  change (if h : rowClique (pairRow C e)=C then x (pairAtRow C (pairRow C e) h) else 0)=x e
  rw [dite_eq_left (rowClique_pairRow C e)]
  congr 1

def blockClass (C : Finset H) : (PairIn C → ℝ) →ₗ[ℝ] ResponseQuotient H :=
  coefficientClass ∘ₗ blockCoordinates C

/-- The kernel of the actual response-quotient map on one clique block is
exactly its constant vectors. This includes every pair of that clique. -/
theorem blockClass_eq_zero_iff (C : Finset H) (e₀ : PairIn C) (x : PairIn C → ℝ) :
    blockClass C x=0 ↔ ∃ c : ℝ,∀ e,x e=c := by
  change coefficientClass (blockCoordinates C x)=0 ↔ _
  rw [coefficientClass_eq_zero_iff]
  constructor
  · intro hx
    refine ⟨x e₀,?_⟩
    intro e
    have he : rowCliqueIndex (pairRow C e)=rowCliqueIndex (pairRow C e₀) := by
      apply Subtype.ext
      exact (rowClique_pairRow C e).trans (rowClique_pairRow C e₀).symm
    simpa only [blockCoordinates_pairRow] using hx _ _ he
  · rintro ⟨c,hc⟩ r t hrt
    have he : rowClique r=rowClique t:=congrArg Subtype.val hrt
    by_cases hr : rowClique r=C
    · have ht : rowClique t=C:=he.symm.trans hr
      change (if h : rowClique r=C then x (pairAtRow C r h) else 0)=
        if h : rowClique t=C then x (pairAtRow C t h) else 0
      rw [dite_eq_left hr,dite_eq_left ht,hc,hc]
    · have ht : rowClique t≠ C:=fun h => hr (he.trans h)
      change (if h : rowClique r=C then x (pairAtRow C r h) else 0)=
        if h : rowClique t=C then x (pairAtRow C t h) else 0
      rw [dite_eq_right hr,dite_eq_right ht]

/-- Omitting one reference pair makes ordinary linear independence of pair
vectors equivalent to independence after passage to the actual quotient.
This is the precise reference-pair argument used in Lemma 7.7. -/
theorem blockClass_linearIndependent_of_reference (C : Finset H) (e₀ : PairIn C)
    (x : J → PairIn C → ℝ) (hx : LinearIndependent ℝ x)
    (hzero : ∀ j,x j e₀=0) :
    LinearIndependent ℝ (fun j => blockClass C (x j)) := by
  rw [Fintype.linearIndependent_iff] at hx ⊢
  intro c hc j
  have hmap : blockClass C (∑ i : J,c i • x i)=0 := by
    simpa only [map_sum,map_smul] using hc
  obtain ⟨a,ha⟩:=(blockClass_eq_zero_iff C e₀ _).mp hmap
  have ha0 : a=0 := by
    have hh:=ha e₀
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,hzero,mul_zero,sum_const_zero] at hh
    exact hh.symm
  have hvec : (∑ i : J,c i • x i)=0 := by
    funext e
    exact (ha e).trans ha0
  exact hx c hvec j

theorem blockClass_linearIndependent_iff_reference (C : Finset H) (e₀ : PairIn C)
    (x : J → PairIn C → ℝ) (hzero : ∀ j,x j e₀=0) :
    LinearIndependent ℝ (fun j => blockClass C (x j)) ↔ LinearIndependent ℝ x := by
  constructor
  · intro hx
    exact LinearIndependent.of_comp (blockClass C) hx
  · intro hx
    exact blockClass_linearIndependent_of_reference C e₀ x hx hzero

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart149

