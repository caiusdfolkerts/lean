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

public import verified.parts.part000
import all verified.parts.part000

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

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
