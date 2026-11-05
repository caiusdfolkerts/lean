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

public import verified.parts.part007
import all verified.parts.part007

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

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
