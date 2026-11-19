module

public import canonical_main.PalomarPart000
import all canonical_main.PalomarPart000
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

section BundlePart35
/- Source: Papers/GraphicalZonotopes/GraphFunctionRestriction.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace SetFunctionEmbedding
open Finset
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

@[simp] theorem restrict_add (e : W ↪ V) (f g : SetFunction V) :
    restrict e (f+g)=restrict e f+restrict e g := rfl

@[simp] theorem restrict_sub (e : W ↪ V) (f g : SetFunction V) :
    restrict e (f-g)=restrict e f-restrict e g := rfl

theorem integerValued_restrict (e : W ↪ V) {f : SetFunction V}
    (hf : IntegerValued f) : IntegerValued (restrict e f) := fun S => hf (S.map e)

/-- The induced-edge counting function restricts to the ordinary induced
graph, including all nonedges. -/
theorem graphFunction_restrict (e : W ↪ V) (G : SimpleGraph V) :
    restrict e (graphFunction G)=graphFunction (G.comap e) := by
  have hfn := restrict_translationNormalized e (graphFunction_translationNormalized G)
  have hgn := graphFunction_translationNormalized (G.comap e)
  have hn : TranslationNormalized (restrict e (graphFunction G)-graphFunction (G.comap e)) := by
    refine ⟨?_,?_⟩
    · change restrict e (graphFunction G) ∅-graphFunction (G.comap e) ∅=0
      rw [hfn.1,hgn.1,sub_self]
    · intro w
      change restrict e (graphFunction G) {w}-graphFunction (G.comap e) {w}=0
      rw [hfn.2 w,hgn.2 w,sub_self]
  apply sub_eq_zero.mp
  apply normalized_zero_elemental_eq_zero hn
  intro u v huv S hu hv
  rw [delta_sub,delta_restrict,
    graphFunction_delta G (fun he => huv (e.injective he)) (by simpa using hu) (by simpa using hv),
    graphFunction_delta (G.comap e) huv hu hv]
  exact sub_self _

end SetFunctionEmbedding
end GraphicalZonotopes

end
end
end BundlePart35

section BundlePart36
/- Source: Papers/GraphicalZonotopes/BooleanPair.lean -/








@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped Pointwise
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Actual normalized integer set functions, with their entire real cone
extremality and with every graph direction occurring in each member. -/
structure BooleanPairData (G : SimpleGraph V) where
  left : SetFunction V
  right : SetFunction V
  left_extreme : ExtremeSupermodular left
  right_extreme : ExtremeSupermodular right
  left_integer : IntegerValued left
  right_integer : IntegerValued right
  pair_sum : left+right=graphFunction G
  left_boolean : ∀ u v,u≠ v → ∀ S : Finset V,u∉S → v∉S →
    delta left u v S=0 ∨ delta left u v S=1
  right_boolean : ∀ u v,u≠ v → ∀ S : Finset V,u∉S → v∉S →
    delta right u v S=0 ∨ delta right u v S=1
  left_direction : ∀ u v,G.Adj u v → ∃ S : Finset V,u∉S ∧ v∉S ∧ delta left u v S≠0
  right_direction : ∀ u v,G.Adj u v → ∃ S : Finset V,u∉S ∧ v∉S ∧ delta right u v S≠0

namespace SetFunctionEmbedding

@[simp] theorem restrict_equiv_inverse (e : W ≃ V) (f : SetFunction V) :
    restrict e.symm.toEmbedding (restrict e.toEmbedding f)=f := by
  funext S
  change f ((S.map e.symm.toEmbedding).map e.toEmbedding)=f S
  congr 1
  ext v
  simp

theorem extreme_restrict_equiv (e : W ≃ V) {f : SetFunction V}
    (hf : ExtremeSupermodular f) : ExtremeSupermodular (restrict e.toEmbedding f) := by
  refine ⟨restrict_translationNormalized e.toEmbedding hf.1,
    restrict_supermodular e.toEmbedding hf.2.1,?_,?_⟩
  · intro he
    apply hf.2.2.1
    have h := congrArg (restrict e.symm.toEmbedding) he
    rw [restrict_equiv_inverse] at h
    exact h.trans (by rfl)
  · intro g h hgn hhn hgs hhs he
    have he' : restrict e.symm.toEmbedding g+restrict e.symm.toEmbedding h=f := by
      rw [← restrict_add,he,restrict_equiv_inverse]
    obtain ⟨a,ha,hag⟩ := hf.2.2.2 (restrict e.symm.toEmbedding g)
      (restrict e.symm.toEmbedding h) (restrict_translationNormalized _ hgn)
      (restrict_translationNormalized _ hhn) (restrict_supermodular _ hgs)
      (restrict_supermodular _ hhs) he'
    refine ⟨a,ha,?_⟩
    have h := congrArg (restrict e.toEmbedding) hag
    rw [restrict_smul] at h
    have hi : restrict e.toEmbedding (restrict e.symm.toEmbedding g)=g := by
      simpa only [Equiv.symm_symm] using restrict_equiv_inverse e.symm g
    exact hi.symm.trans h

end SetFunctionEmbedding

namespace BooleanPairData

/-- Relabelling is an equivalence of the full real set-function cones. -/
def relabel {G : SimpleGraph V} (D : BooleanPairData G) (e : W ≃ V) :
    BooleanPairData (G.comap e) where
  left := SetFunctionEmbedding.restrict e.toEmbedding D.left
  right := SetFunctionEmbedding.restrict e.toEmbedding D.right
  left_extreme := SetFunctionEmbedding.extreme_restrict_equiv e D.left_extreme
  right_extreme := SetFunctionEmbedding.extreme_restrict_equiv e D.right_extreme
  left_integer := SetFunctionEmbedding.integerValued_restrict _ D.left_integer
  right_integer := SetFunctionEmbedding.integerValued_restrict _ D.right_integer
  pair_sum := by
    rw [← SetFunctionEmbedding.restrict_add,D.pair_sum]
    exact SetFunctionEmbedding.graphFunction_restrict e.toEmbedding G
  left_boolean := by
    intro u v huv S hu hv
    rw [SetFunctionEmbedding.delta_restrict]
    exact D.left_boolean _ _ (fun he => huv (e.injective he)) _
      (by simpa using hu) (by simpa using hv)
  right_boolean := by
    intro u v huv S hu hv
    rw [SetFunctionEmbedding.delta_restrict]
    exact D.right_boolean _ _ (fun he => huv (e.injective he)) _
      (by simpa using hu) (by simpa using hv)
  left_direction := by
    intro u v huv
    obtain ⟨S,hu,hv,hd⟩ := D.left_direction (e u) (e v) huv
    refine ⟨S.map e.symm.toEmbedding,by simpa using hu,by simpa using hv,?_⟩
    rw [SetFunctionEmbedding.delta_restrict]
    have hS : (S.map e.symm.toEmbedding).map e.toEmbedding=S := by ext x; simp
    rwa [hS]
  right_direction := by
    intro u v huv
    obtain ⟨S,hu,hv,hd⟩ := D.right_direction (e u) (e v) huv
    refine ⟨S.map e.symm.toEmbedding,by simpa using hu,by simpa using hv,?_⟩
    rw [SetFunctionEmbedding.delta_restrict]
    have hS : (S.map e.symm.toEmbedding).map e.toEmbedding=S := by ext x; simp
    rwa [hS]

theorem geometric_pair {G : SimpleGraph V} (D : BooleanPairData G) (hG : G.Connected) :
    LatticePolytope (basePolytope D.left) ∧ LatticePolytope (basePolytope D.right) ∧
    MinkowskiIndecomposable (basePolytope D.left) ∧
    MinkowskiIndecomposable (basePolytope D.right) ∧
    FullDimension (basePolytope D.left) ∧ FullDimension (basePolytope D.right) ∧
    basePolytope D.left+basePolytope D.right=graphicalZonotope G ∧
    actualDirectionGraph (basePolytope D.left)=G ∧
    actualDirectionGraph (basePolytope D.right)=G ∧
    BooleanElemental (basePolytope D.left) ∧ BooleanElemental (basePolytope D.right) := by
  have hln := D.left_extreme.1
  have hrn := D.right_extreme.1
  have hls := D.left_extreme.2.1
  have hrs := D.right_extreme.2.1
  have hsum : basePolytope D.left+basePolytope D.right=graphicalZonotope G := by
    rw [← basePolytope_add hln.1 hrn.1 hls hrs,D.pair_sum,baseGraphFunction_eq_graphicalZonotope]
  refine ⟨D.left_integer.basePolytope hln.1 hls,D.right_integer.basePolytope hrn.1 hrs,
    D.left_extreme.minkowskiIndecomposable,D.right_extreme.minkowskiIndecomposable,
    finrank_vectorSpan_eq_of_connected_slacks hln.1 hls hG D.left_direction,
    finrank_vectorSpan_eq_of_connected_slacks hrn.1 hrs hG D.right_direction,hsum,?_,?_,?_,?_⟩
  · ext u v
    constructor
    · apply basePolytope_summand_actualRootEdge hln.1 hls G
        (by norm_num : (0 : ℝ)≤1) (basePolytope D.right)
      simpa only [one_smul] using hsum
    · intro huv
      obtain ⟨S,hu,hv,hd⟩ := D.left_direction u v huv
      exact exposedSegment_of_positive_delta hln.1 hls (G.ne_of_adj huv) hu hv
        (lt_of_le_of_ne (hls.elemental u v (G.ne_of_adj huv) S hu hv) (Ne.symm hd))
  · ext u v
    constructor
    · apply basePolytope_summand_actualRootEdge hrn.1 hrs G
        (by norm_num : (0 : ℝ)≤1) (basePolytope D.left)
      simpa only [one_smul,add_comm] using hsum
    · intro huv
      obtain ⟨S,hu,hv,hd⟩ := D.right_direction u v huv
      exact exposedSegment_of_positive_delta hrn.1 hrs (G.ne_of_adj huv) hu hv
        (lt_of_le_of_ne (hrs.elemental u v (G.ne_of_adj huv) S hu hv) (Ne.symm hd))
  · intro u v huv S hu hv
    rw [lowerSupport_basePolytope hln.1 hls]
    exact D.left_boolean u v huv S hu hv
  · intro u v huv S hu hv
    rw [lowerSupport_basePolytope hrn.1 hrs]
    exact D.right_boolean u v huv S hu hv

end BooleanPairData
end GraphicalZonotopes

end
end
end BundlePart36

section BundlePart37
/- Source: Papers/GraphicalZonotopes/SmallBooleanGeometry.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace SmallBoolean
open Finset FiniteTight

def partGraph {n : ℕ} (part : Fin n → Fin 4) : SimpleGraph (Fin n) where
  Adj u v := part u≠ part v
  symm := ⟨fun _ _ h => Ne.symm h⟩
  loopless := ⟨fun _ h => h rfl⟩

instance {n : ℕ} (part : Fin n → Fin 4) : DecidableRel (partGraph part).Adj :=
  fun u v => inferInstanceAs (Decidable (part u≠ part v))

namespace K4

def part : Fin 4 → Fin 4 := ![0,1,2,3]

def graph : SimpleGraph (Fin 4) := partGraph part

instance : DecidableRel graph.Adj :=
  fun u v => inferInstanceAs (Decidable (part u≠ part v))

theorem pair_differences : ∀ u v : Fin 4,u≠ v → ∀ S : Finset (Fin 4),
    u∉S → v∉S → integerDelta integerFunction u v S+
      integerDelta K4Complement.integerFunction u v S=if graph.Adj u v then 1 else 0 := by decide

theorem left_occurs : ∀ u v : Fin 4,graph.Adj u v → ∃ S : Finset (Fin 4),
    u∉S ∧ v∉S ∧ integerDelta integerFunction u v S=1 := by decide

theorem right_occurs : ∀ u v : Fin 4,graph.Adj u v → ∃ S : Finset (Fin 4),
    u∉S ∧ v∉S ∧ integerDelta K4Complement.integerFunction u v S=1 := by decide

def pairData : BooleanPairData graph where
  left := realFunction integerFunction
  right := realFunction K4Complement.integerFunction
  left_extreme := extreme
  right_extreme := K4Complement.extreme
  left_integer := realFunction_integerValued _
  right_integer := realFunction_integerValued _
  pair_sum := pair_sum_of_integer_differences graph integerFunction K4Complement.integerFunction
    empty_zero singleton_zero K4Complement.empty_zero K4Complement.singleton_zero pair_differences
  left_boolean := by
    intro u v huv S hu hv
    rw [delta_realFunction]
    rcases boolean_differences u v huv S hu hv with h | h
    · exact Or.inl (by rw [h]; norm_num)
    · exact Or.inr (by rw [h]; norm_num)
  right_boolean := by
    intro u v huv S hu hv
    rw [delta_realFunction]
    rcases K4Complement.boolean_differences u v huv S hu hv with h | h
    · exact Or.inl (by rw [h]; norm_num)
    · exact Or.inr (by rw [h]; norm_num)
  left_direction := by
    intro u v huv
    obtain ⟨S,hu,hv,hd⟩ := left_occurs u v huv
    refine ⟨S,hu,hv,?_⟩
    rw [delta_realFunction,hd]
    norm_num
  right_direction := by
    intro u v huv
    obtain ⟨S,hu,hv,hd⟩ := right_occurs u v huv
    refine ⟨S,hu,hv,?_⟩
    rw [delta_realFunction,hd]
    norm_num

end K4

namespace K1112

def part : Fin 5 → Fin 4 := ![0,1,2,3,3]

def graph : SimpleGraph (Fin 5) := partGraph part

instance : DecidableRel graph.Adj :=
  fun u v => inferInstanceAs (Decidable (part u≠ part v))

theorem pair_differences : ∀ u v : Fin 5,u≠ v → ∀ S : Finset (Fin 5),
    u∉S → v∉S → integerDelta integerFunction u v S+
      integerDelta K1112Complement.integerFunction u v S=if graph.Adj u v then 1 else 0 := by decide

theorem left_occurs : ∀ u v : Fin 5,graph.Adj u v → ∃ S : Finset (Fin 5),
    u∉S ∧ v∉S ∧ integerDelta integerFunction u v S=1 := by decide

theorem right_occurs : ∀ u v : Fin 5,graph.Adj u v → ∃ S : Finset (Fin 5),
    u∉S ∧ v∉S ∧ integerDelta K1112Complement.integerFunction u v S=1 := by decide

def pairData : BooleanPairData graph where
  left := realFunction integerFunction
  right := realFunction K1112Complement.integerFunction
  left_extreme := extreme
  right_extreme := K1112Complement.extreme
  left_integer := realFunction_integerValued _
  right_integer := realFunction_integerValued _
  pair_sum := pair_sum_of_integer_differences graph integerFunction K1112Complement.integerFunction
    empty_zero singleton_zero K1112Complement.empty_zero K1112Complement.singleton_zero pair_differences
  left_boolean := by
    intro u v huv S hu hv
    rw [delta_realFunction]
    rcases boolean_differences u v huv S hu hv with h | h
    · exact Or.inl (by rw [h]; norm_num)
    · exact Or.inr (by rw [h]; norm_num)
  right_boolean := by
    intro u v huv S hu hv
    rw [delta_realFunction]
    rcases K1112Complement.boolean_differences u v huv S hu hv with h | h
    · exact Or.inl (by rw [h]; norm_num)
    · exact Or.inr (by rw [h]; norm_num)
  left_direction := by
    intro u v huv
    obtain ⟨S,hu,hv,hd⟩ := left_occurs u v huv
    refine ⟨S,hu,hv,?_⟩
    rw [delta_realFunction,hd]
    norm_num
  right_direction := by
    intro u v huv
    obtain ⟨S,hu,hv,hd⟩ := right_occurs u v huv
    refine ⟨S,hu,hv,?_⟩
    rw [delta_realFunction,hd]
    norm_num

end K1112

namespace K1122

def part : Fin 6 → Fin 4 := ![0,1,2,2,3,3]

def graph : SimpleGraph (Fin 6) := partGraph part

instance : DecidableRel graph.Adj :=
  fun u v => inferInstanceAs (Decidable (part u≠ part v))

theorem pair_differences : ∀ u v : Fin 6,u≠ v → ∀ S : Finset (Fin 6),
    u∉S → v∉S → integerDelta integerFunction u v S+
      integerDelta K1122Complement.integerFunction u v S=if graph.Adj u v then 1 else 0 := by decide

theorem left_occurs : ∀ u v : Fin 6,graph.Adj u v → ∃ S : Finset (Fin 6),
    u∉S ∧ v∉S ∧ integerDelta integerFunction u v S=1 := by decide

theorem right_occurs : ∀ u v : Fin 6,graph.Adj u v → ∃ S : Finset (Fin 6),
    u∉S ∧ v∉S ∧ integerDelta K1122Complement.integerFunction u v S=1 := by decide

def pairData : BooleanPairData graph where
  left := realFunction integerFunction
  right := realFunction K1122Complement.integerFunction
  left_extreme := extreme
  right_extreme := K1122Complement.extreme
  left_integer := realFunction_integerValued _
  right_integer := realFunction_integerValued _
  pair_sum := pair_sum_of_integer_differences graph integerFunction K1122Complement.integerFunction
    empty_zero singleton_zero K1122Complement.empty_zero K1122Complement.singleton_zero pair_differences
  left_boolean := by
    intro u v huv S hu hv
    rw [delta_realFunction]
    rcases boolean_differences u v huv S hu hv with h | h
    · exact Or.inl (by rw [h]; norm_num)
    · exact Or.inr (by rw [h]; norm_num)
  right_boolean := by
    intro u v huv S hu hv
    rw [delta_realFunction]
    rcases K1122Complement.boolean_differences u v huv S hu hv with h | h
    · exact Or.inl (by rw [h]; norm_num)
    · exact Or.inr (by rw [h]; norm_num)
  left_direction := by
    intro u v huv
    obtain ⟨S,hu,hv,hd⟩ := left_occurs u v huv
    refine ⟨S,hu,hv,?_⟩
    rw [delta_realFunction,hd]
    norm_num
  right_direction := by
    intro u v huv
    obtain ⟨S,hu,hv,hd⟩ := right_occurs u v huv
    refine ⟨S,hu,hv,?_⟩
    rw [delta_realFunction,hd]
    norm_num

end K1122

end SmallBoolean
end GraphicalZonotopes

end
end
end BundlePart37

section BundlePart38
/- Source: Papers/GraphicalZonotopes/RootDirectionLines.lean -/





/-! # Uniqueness of standard root direction lines

This elementary geometric fact is independent of the sharp dimension bounds
and their path-family attainment construction.
-/

@[expose] public section
noncomputable section
namespace GraphicalZonotopes

/-- Distinct unordered pairs represent distinct unoriented root directions.
Together with all-edge coverage, this identifies the graph edge count with
the number of geometric edge directions. -/
theorem root_parallel_pair_eq {V : Type*} [Fintype V] [DecidableEq V]
    {u v a b : V} (huv : u ≠ v) (hab : a ≠ b) {c d : ℝ} (hc : c ≠ 0)
    (h : c • (basisVector u-basisVector v)=d • (basisVector a-basisVector b)) :
    ({u,v} : Finset V)={a,b} := by
  classical
  have hedge : (cliqueGraph ({a,b} : Finset V)).Adj a b :=
    ⟨hab,by simp,by simp⟩
  have he := adjacency_of_root_parallel (cliqueGraph ({a,b} : Finset V)) huv hedge hc h
  apply Finset.eq_of_subset_of_card_le
  · intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact he.2.1
    · have hwv := Finset.mem_singleton.mp hw
      simpa only [hwv] using he.2.2
  · simpa only [Finset.card_pair huv,Finset.card_pair hab] using (Nat.le_refl 2)

end GraphicalZonotopes

end
end
end BundlePart38

section BundlePart39
/- Source: Papers/GraphicalZonotopes/ActualDirectionsFromSlacks.lean -/








/-! # Actual root edges and nonzero elemental slacks

The converse to the exposed-segment construction follows from the genuine
graphical weak-summand criterion, applied to the complete graph with one
pair removed.  No restriction on clique size is needed.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped Pointwise

/-- Every actual exposed edge of an arbitrary finite weak summand has an
ambient standard-root direction. This justifies counting all actual edge
directions by the unordered pairs in `actualDirectionGraph`. -/
theorem weak_summand_exposed_edge_direction {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {Q : Set (V → ℝ)} (hQ : IsFinitePolytope Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G))
    {p q : V → ℝ} (hex : IsExposedSegment Q p q) :
    ∃ u v,G.Adj u v ∧ ∃ t : ℝ,t ≠ 0 ∧
      q - p = t • (basisVector v - basisVector u) := by
  obtain ⟨a,ha,R,hR,hRc,hnR,hQR⟩ := hw
  have hzn : Normalized (a • graphFunction G) := by
    change a * graphFunction G ∅ = 0
    rw [graphFunction_normalized,mul_zero]
  have hzs : Supermodular (a • graphFunction G) :=
    (graphFunction_supermodular G).smul ha.le
  have hbase : Q + R = basePolytope (a • graphFunction G) := by
    rw [basePolytope_smul (graphFunction_normalized G)
      (graphFunction_supermodular G) ha.le,baseGraphFunction_eq_graphicalZonotope]
    exact hQR
  obtain ⟨x,hx⟩ := basePolytope_nonempty hzn hzs
  rw [← hbase] at hx
  obtain ⟨xQ,hxQ,xR,hxR,hxsum⟩ := hx
  have hnQ : Q.Nonempty := ⟨xQ,hxQ⟩
  let f := lowerSupport Q
  have hfn : Normalized f := lowerSupport_normalized hQ.compact hnQ
  have hfs : Supermodular f :=
    summand_lowerSupport_supermodular hzn hzs hQ.compact hR hnQ hnR hbase
  have hbody : Q = basePolytope f :=
    summand_eq_basePolytope hzn hzs hQ.compact hR hQ.convex hnQ hnR hbase
  exact basePolytope_summand_exposed_edge hfn hfs G ha.le R (hbody ▸ hQR) (hbody ▸ hex)

private def deletedPairGraph {V : Type*} (u v : V) : SimpleGraph V where
  Adj a b := a ≠ b ∧ (a ≠ u ∨ b ≠ v) ∧ (a ≠ v ∨ b ≠ u)
  symm := ⟨by intro a b h; tauto⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem actualRootEdge_iff_nonzero_elemental {V : Type*} [Fintype V] [DecidableEq V]
    {f : SetFunction V} (hn : Normalized f) (hs : Supermodular f) (u v : V) :
    ActualRootEdge (basePolytope f) u v ↔ u ≠ v ∧
      ∃ S : Finset V,u ∉ S ∧ v ∉ S ∧ delta f u v S ≠ 0 := by
  constructor
  · intro h
    refine ⟨h.1,?_⟩
    by_contra hnone
    push_neg at hnone
    have hg : Graphical (deletedPairGraph u v) f := by
      intro a b hab hnon S ha hb
      have hp : (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
        change ¬(a ≠ b ∧ (a ≠ u ∨ b ≠ v) ∧ (a ≠ v ∨ b ≠ u)) at hnon
        tauto
      rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hnone S ha hb
      · rw [delta_comm]
        exact hnone S hb ha
    obtain ⟨a,ha,R,hR,hRc,hnR,he⟩ :=
      (isWeakMinkowskiSummand_graphical_iff hn hs).mpr hg
    have hh := basePolytope_summand_actualRootEdge hn hs
      (deletedPairGraph u v) ha.le R he h
    exact hh.2.1.elim (fun hn => hn rfl) (fun hn => hn rfl)
  · rintro ⟨huv,S,hu,hv,hd⟩
    exact exposedSegment_of_positive_delta hn hs huv hu hv
      (lt_of_le_of_ne (hs.elemental u v huv S hu hv) (Ne.symm hd))

end GraphicalZonotopes

end
end
end BundlePart39

section BundlePart40
/- Source: Papers/GraphicalZonotopes/GeometricDirectionCount.lean -/






/-! # Counting actual geometric edge directions

An unoriented direction is the real line spanned by the difference of the
endpoints of an exposed edge. The final theorem identifies the cardinality of
this geometric set with `directionCount`, for every finite weak summand of a
graphical zonotope. Thus no chosen orientation or duplicate parallel edge
changes the count used by the principal theorems.
-/

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def actualEdgeDirectionLines (Q : Set (V → ℝ)) : Set (Submodule ℝ (V → ℝ)) :=
  {L | ∃ p q, IsExposedSegment Q p q ∧
    L = Submodule.span ℝ ({q - p} : Set (V → ℝ))}

abbrev ActualDirectionPair (Q : Set (V → ℝ)) :=
  {C : Finset V // C ∈ edgeFamily (actualDirectionGraph Q)}

def directionPairEndpoints {Q : Set (V → ℝ)} (e : ActualDirectionPair Q) :
    {p : V × V // p.1 ≠ p.2 ∧ e.1 = {p.1,p.2}} := by
  let h := card_eq_two.mp ((mem_edgeFamily _ _).mp e.2).1
  let u := Classical.choose h
  let v := Classical.choose (Classical.choose_spec h)
  exact ⟨(u,v),Classical.choose_spec (Classical.choose_spec h)⟩

def directionPairLine {Q : Set (V → ℝ)} (e : ActualDirectionPair Q) :
    Submodule ℝ (V → ℝ) :=
  Submodule.span ℝ ({(basisVector (directionPairEndpoints e).1.1 -
    basisVector (directionPairEndpoints e).1.2)} : Set (V → ℝ))

private theorem span_root_swap (u v : V) :
    Submodule.span ℝ ({basisVector v-basisVector u} : Set (V → ℝ)) =
      Submodule.span ℝ ({basisVector u-basisVector v} : Set (V → ℝ)) := by
  have he : basisVector v-basisVector u = (-1 : ℝ) •
      (basisVector u-basisVector v) := by module
  rw [he,Submodule.span_singleton_smul_eq
    (isUnit_iff_ne_zero.mpr (by norm_num : (-1 : ℝ) ≠ 0))]

theorem directionPairLine_eq {Q : Set (V → ℝ)} (e : ActualDirectionPair Q)
    (u v : V) (he : e.1 = {u,v}) :
    directionPairLine e =
      Submodule.span ℝ ({basisVector u-basisVector v} : Set (V → ℝ)) := by
  let a := (directionPairEndpoints e).1.1
  let b := (directionPairEndpoints e).1.2
  have hab : a ≠ b := (directionPairEndpoints e).2.1
  have hc : ({a,b} : Finset V) = {u,v} := (directionPairEndpoints e).2.2.symm.trans he
  have ha : a=u ∨ a=v := by
    have hm : a ∈ ({u,v} : Finset V) := hc ▸ mem_insert_self a {b}
    simpa only [mem_insert,mem_singleton] using hm
  have hb : b=u ∨ b=v := by
    have hm : b ∈ ({u,v} : Finset V) := hc ▸ mem_insert_of_mem (mem_singleton_self b)
    simpa only [mem_insert,mem_singleton] using hm
  change Submodule.span ℝ ({basisVector a-basisVector b} : Set (V → ℝ)) = _
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact False.elim (hab (ha.trans hb.symm))
  · rw [ha,hb]
  · rw [ha,hb]
    exact span_root_swap u v
  · exact False.elim (hab (ha.trans hb.symm))

theorem directionPairLine_injective (Q : Set (V → ℝ)) :
    Function.Injective (directionPairLine (Q := Q)) := by
  intro e f h
  let a := (directionPairEndpoints e).1.1
  let b := (directionPairEndpoints e).1.2
  let u := (directionPairEndpoints f).1.1
  let v := (directionPairEndpoints f).1.2
  have hab : a ≠ b := (directionPairEndpoints e).2.1
  have huv : u ≠ v := (directionPairEndpoints f).2.1
  have he : e.1 = {a,b} := (directionPairEndpoints e).2.2
  have hf : f.1 = {u,v} := (directionPairEndpoints f).2.2
  rw [directionPairLine_eq e a b he,directionPairLine_eq f u v hf] at h
  have hm : basisVector a-basisVector b ∈
      Submodule.span ℝ ({basisVector u-basisVector v} : Set (V → ℝ)) :=
    h ▸ Submodule.mem_span_singleton_self _
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hm
  have hp : ({a,b} : Finset V) = {u,v} :=
    root_parallel_pair_eq hab huv (by norm_num : (1 : ℝ) ≠ 0)
      (by simpa only [one_smul] using hc.symm)
  exact Subtype.ext (he.trans (hp.trans hf.symm))

theorem range_directionPairLine {G : SimpleGraph V} {Q : Set (V → ℝ)}
    (hQ : IsFinitePolytope Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    Set.range (directionPairLine (Q := Q)) = actualEdgeDirectionLines Q := by
  ext L
  constructor
  · rintro ⟨e,rfl⟩
    let u := (directionPairEndpoints e).1.1
    let v := (directionPairEndpoints e).1.2
    have huv : u ≠ v := (directionPairEndpoints e).2.1
    have he : e.1 = {u,v} := (directionPairEndpoints e).2.2
    have hm : ({u,v} : Finset V) ∈ edgeFamily (actualDirectionGraph Q) := he ▸ e.2
    have ha : ActualRootEdge Q u v := (pair_mem_edgeFamily _ huv).mp hm
    obtain ⟨_,p,q,hex,c,hc,hpq⟩ := ha
    refine ⟨p,q,hex,?_⟩
    rw [directionPairLine_eq e u v he,hpq,
      Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc)]
  · rintro ⟨p,q,hex,rfl⟩
    obtain ⟨u,v,huv,c,hc,hpq⟩ := weak_summand_exposed_edge_direction hQ hw hex
    have hvu : v ≠ u := (G.ne_of_adj huv).symm
    have ha : ActualRootEdge Q v u := ⟨hvu,p,q,hex,c,hc,hpq⟩
    let e : ActualDirectionPair Q := ⟨{v,u},(pair_mem_edgeFamily _ hvu).mpr ha⟩
    refine ⟨e,?_⟩
    rw [directionPairLine_eq e v u rfl,hpq,
      Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc)]

theorem actualEdgeDirectionLines_finite {G : SimpleGraph V} {Q : Set (V → ℝ)}
    (hQ : IsFinitePolytope Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    (actualEdgeDirectionLines Q).Finite := by
  classical
  rw [←range_directionPairLine hQ hw]
  exact Set.finite_range _

/-- The paper's number of geometric, unoriented edge directions is exactly
the finite root-pair count appearing in the verified numerical theorems. -/
theorem directionCount_eq_geometric_line_count {G : SimpleGraph V}
    {Q : Set (V → ℝ)} (hQ : IsFinitePolytope Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    directionCount Q = (actualEdgeDirectionLines Q).ncard := by
  classical
  rw [←range_directionPairLine hQ hw,
    Set.ncard_range_of_injective (directionPairLine_injective Q),Nat.card_eq_fintype_card]
  simp only [ActualDirectionPair,Fintype.card_coe,directionCount]

end GraphicalZonotopes

end
end
end BundlePart40

section BundlePart41
/- Source: Papers/GraphicalZonotopes/HamiltonianDeletion.lean -/







/-! A Hamiltonian cycle leaves at most |S| components after deletion of a
nonempty vertex set S. The proof counts the components visited by a walk;
it uses the actual graph and its actual induced deletion. -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.HamiltonianDeletion
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev deleted (G : SimpleGraph V) (S : Finset V) :=
  G.induce {v | v ∉ S}

def componentLabel (G : SimpleGraph V) (S : Finset V) (v : V) :
    Option (deleted G S).ConnectedComponent :=
  if h : v ∈ S then none else some ((deleted G S).connectedComponentMk ⟨v,h⟩)

def walkComponents (G : SimpleGraph V) (S : Finset V) {a b : V} (p : G.Walk a b) :
    Finset (deleted G S).ConnectedComponent :=
  (p.support.filterMap (componentLabel G S)).toFinset

theorem start_component_mem (G : SimpleGraph V) (S : Finset V) {a b : V}
    (p : G.Walk a b) (ha : a ∉ S) :
    (deleted G S).connectedComponentMk ⟨a,ha⟩ ∈ walkComponents G S p := by
  simp only [walkComponents,List.mem_toFinset,List.mem_filterMap]
  exact ⟨a,p.start_mem_support,by simp [componentLabel,ha]⟩

/-- Every deleted occurrence can start at most one new surviving component.
If the walk starts outside the deleted set, its initial component contributes
the sole extra term. No simplicity assumption on the walk is needed. -/
theorem walk_component_count_le (G : SimpleGraph V) (S : Finset V) {a b : V}
    (p : G.Walk a b) :
    (walkComponents G S p).card ≤ p.support.countP (fun v => v ∈ S)+
      if a ∈ S then 0 else 1 := by
  induction p with
  | @nil v =>
    by_cases hv : v ∈ S <;> simp [walkComponents,componentLabel,hv]
  | @cons a b c hab p ih =>
    by_cases ha : a ∈ S
    · have hw : walkComponents G S (.cons hab p)=walkComponents G S p := by
        simp [walkComponents,componentLabel,ha]
      rw [hw]
      by_cases hb : b ∈ S <;>
        simp [hb] at ih <;> simp [SimpleGraph.Walk.support_cons,ha] <;> omega
    · have hw : walkComponents G S (.cons hab p)=
          insert ((deleted G S).connectedComponentMk ⟨a,ha⟩) (walkComponents G S p) := by
        simp [walkComponents,componentLabel,ha]
      rw [hw]
      by_cases hb : b ∈ S
      · have hc := card_insert_le ((deleted G S).connectedComponentMk ⟨a,ha⟩)
          (walkComponents G S p)
        simp [hb] at ih
        simp [SimpleGraph.Walk.support_cons,ha]
        omega
      · have he : (deleted G S).connectedComponentMk ⟨a,ha⟩=
            (deleted G S).connectedComponentMk ⟨b,hb⟩ :=
          SimpleGraph.ConnectedComponent.sound
            ((show (deleted G S).Adj ⟨a,ha⟩ ⟨b,hb⟩ from hab).reachable)
        have hm := start_component_mem G S p hb
        rw [←he] at hm
        rw [insert_eq_of_mem hm]
        simpa [SimpleGraph.Walk.support_cons,ha,hb] using ih

theorem hamiltonian_walk_components (G : SimpleGraph V) (S : Finset V) {a b : V}
    {p : G.Walk a b} (hp : p.IsHamiltonian) : walkComponents G S p=univ := by
  apply eq_univ_iff_forall.mpr
  intro C
  induction C using SimpleGraph.ConnectedComponent.ind
  rename_i v
  have hv : v.1 ∉ S := v.2
  simp only [walkComponents,List.mem_toFinset,List.mem_filterMap]
  exact ⟨v.1,hp.mem_support v.1,by simp [componentLabel,hv]⟩

theorem hamiltonian_deleted_count (G : SimpleGraph V) (S : Finset V) {a b : V}
    {p : G.Walk a b} (hp : p.IsHamiltonian) :
    p.support.countP (fun v => v ∈ S)=S.card := by
  have h := hp.isPath.support_nodup.card_eq_countP (P := fun v => v ∈ S)
  rw [hp.toFinset_support] at h
  simpa using h.symm

/-- The usual toughness bound for a Hamiltonian graph, derived directly from
a Hamiltonian cycle and valid for every nonempty deletion set. -/
theorem hamiltonian_component_card_delete_le (G : SimpleGraph V)
    (hG : G.IsHamiltonian) (hn : 2 ≤ Fintype.card V)
    (S : Finset V) (hS : S.Nonempty) :
    Nat.card (G.induce ((S : Set V)ᶜ)).ConnectedComponent ≤ S.card := by
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hn
  obtain ⟨a,ha⟩ := hS
  obtain ⟨p,hp⟩ := hG.exists_isHamiltonianCycle a
  have hpath := hp.isHamiltonian_dropLast
  have h := walk_component_count_le G S p.dropLast
  rw [hamiltonian_walk_components G S hpath,
    hamiltonian_deleted_count G S hpath] at h
  change Nat.card (deleted G S).ConnectedComponent ≤ S.card
  simpa only [ha,ite_true,add_zero,card_univ,Nat.card_eq_fintype_card] using h

end GraphicalZonotopes.HamiltonianDeletion

end
end
end BundlePart41

section BundlePart42
/- Source: Papers/GraphicalZonotopes/ThreeTreeCliques.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem ThreeTreeOn.edges_supported {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u v : V} (huv : G.Adj u v) : u∈S ∧ v∈S := by
  induction h generalizing u v with
  | tetrahedron C hC => exact ⟨huv.2.1,huv.2.2⟩
  | @attach S G h w hw T hT hTS hcl ih =>
    rcases huv with huv | huv
    · have hv:=ih (u:=u) (v:=v) huv
      exact ⟨mem_insert_of_mem hv.1,mem_insert_of_mem hv.2⟩
    · rcases huv.2 with ⟨rfl,hv⟩ | ⟨rfl,hu⟩
      · exact ⟨mem_insert_self _ _,mem_insert_of_mem (hTS hv)⟩
      · exact ⟨mem_insert_of_mem (hTS hu),mem_insert_self _ _⟩

theorem ThreeTreeOn.active_card_ge_four {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : 4≤ S.card := by
  induction h with
  | tetrahedron C hC => omega
  | attach h u hu T hT hTS hcl ih =>
    rw [card_insert_of_notMem hu]
    omega

theorem ThreeTreeOn.clique_subset_active {S C : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (hcard : 2≤ C.card) (hC : G.IsClique C) : C⊆S := by
  intro u hu
  obtain ⟨v,hv,hvu⟩ := exists_mem_ne (by omega : 1< C.card) u
  exact (h.edges_supported (hC hu hv (Ne.symm hvu))).1

theorem clique_before_attachment {G : SimpleGraph V} {u : V} {T C : Finset V}
    (hu : u∉C) (hC : (G⊔attachmentStar u T).IsClique C) : G.IsClique C := by
  intro v hv w hw hvw
  rcases hC hv hw hvw with h | h
  · exact h
  · rcases h.2 with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> contradiction

theorem attached_vertex_adj_iff {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u : V} (hu : u∉S) {T : Finset V} (hTS : T⊆S)
    (v : V) : (G⊔attachmentStar u T).Adj u v ↔ v∈T := by
  constructor
  · intro hadj
    rcases hadj with hadj | hadj
    · exact False.elim (hu (h.edges_supported hadj).1)
    · rcases hadj.2 with ⟨_,hv⟩ | ⟨he,huT⟩
      · exact hv
      · exact False.elim (hu (hTS huT))
  · intro hv
    refine Or.inr ⟨?_,Or.inl ⟨rfl,hv⟩⟩
    intro he
    subst v
    exact hu (hTS hv)

theorem attached_tetrahedron_clique {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u : V} (hu : u∉S) {T : Finset V} (hTS : T⊆S)
    (hT : G.IsClique T) : (G⊔attachmentStar u T).IsClique (insert u T : Finset V) := by
  intro v hv w hw hvw
  change v ∈ (insert u T : Finset V) at hv
  change w ∈ (insert u T : Finset V) at hw
  rcases mem_insert.mp hv with hvu | hv
  · subst v
    have hwT : w∈T := (mem_insert.mp hw).resolve_left (Ne.symm hvw)
    exact (attached_vertex_adj_iff h hu hTS w).mpr hwT
  · rcases mem_insert.mp hw with hwu | hw
    · subst w
      exact (G⊔attachmentStar u T).adj_symm
        ((attached_vertex_adj_iff h hu hTS v).mpr hv)
    · exact Or.inl (hT hv hw hvw)

theorem ThreeTreeOn.clique_card_le_four {S C : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (hC : G.IsClique C) : C.card≤4 := by
  induction h generalizing C with
  | tetrahedron S hS =>
    by_cases hc : 2≤ C.card
    · have hsub := (ThreeTreeOn.tetrahedron S hS).clique_subset_active hc hC
      simpa only [hS] using card_le_card hsub
    · omega
  | @attach S G h u hu T hT hTS hcl ih =>
    by_cases huC : u∈C
    · have herase : C.erase u⊆T := by
        intro v hv
        exact (attached_vertex_adj_iff h hu hTS v).mp
          (hC huC (mem_of_mem_erase hv) (Ne.symm (ne_of_mem_erase hv)))
      have hcard := card_le_card herase
      rw [card_erase_of_mem huC,hT] at hcard
      omega
    · exact ih (C:=C) (clique_before_attachment huC hC)

theorem ThreeTreeOn.cliqueFree_five {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : G.CliqueFree 5 := by
  intro C hc
  have hb:=h.clique_card_le_four hc.isClique
  rw [hc.card_eq] at hb
  omega

theorem tetrahedra_after_attachment {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u : V} (hu : u∉S) {T : Finset V}
    (hT : T.card=3) (hTS : T⊆S) (hcl : G.IsClique T) :
    tetrahedra (G⊔attachmentStar u T)=insert (insert u T) (tetrahedra G) := by
  classical
  have huT : u∉T := fun huT => hu (hTS huT)
  ext C
  simp only [tetrahedra,mem_filter,mem_univ,true_and,mem_insert]
  constructor
  · rintro ⟨hC,hclC⟩
    by_cases huC : u∈C
    · left
      have herase : C.erase u⊆T := by
        intro v hv
        exact (attached_vertex_adj_iff h hu hTS v).mp
          (hclC huC (mem_of_mem_erase hv) (Ne.symm (ne_of_mem_erase hv)))
      have he : C.erase u=T := eq_of_subset_of_card_le herase (by
        rw [card_erase_of_mem huC,hC,hT])
      rw [← he,insert_erase huC]
    · right
      exact ⟨hC,clique_before_attachment huC hclC⟩
  · rintro (rfl | ⟨hC,hclC⟩)
    · exact ⟨by rw [card_insert_of_notMem huT,hT],attached_tetrahedron_clique h hu hTS hcl⟩
    · exact ⟨hC,fun v hv w hw hvw => Or.inl (hclC hv hw hvw)⟩

theorem attached_tetrahedron_not_old {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u : V} (hu : u∉S) {T : Finset V} :
    insert u T∉tetrahedra G := by
  classical
  intro hm
  obtain ⟨hc,hcl⟩ := (mem_filter.mp hm).2
  have hs:=h.clique_subset_active (by omega) hcl
  exact hu (hs (mem_insert_self _ _))

theorem tetrahedra_cliqueGraph {C : Finset V} (hC : C.card=4) :
    tetrahedra (cliqueGraph C)={C} := by
  classical
  ext D
  simp only [tetrahedra,mem_filter,mem_univ,true_and,mem_singleton]
  constructor
  · rintro ⟨hD,hcl⟩
    exact eq_of_subset_of_card_le
      ((ThreeTreeOn.tetrahedron C hC).clique_subset_active (by omega) hcl) (by omega)
  · rintro rfl
    exact ⟨hC,fun u hu v hv huv => ⟨huv,hu,hv⟩⟩

/-- Every 3-tree on its full active vertex set has exactly |S|-3 actual
tetrahedra. The assertion concerns all cliques, independently of a selected
construction sequence. -/
theorem ThreeTreeOn.tetrahedra_card {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : (tetrahedra G).card=S.card-3 := by
  induction h with
  | tetrahedron C hC => rw [tetrahedra_cliqueGraph hC,card_singleton,hC]
  | @attach S G h u hu T hT hTS hcl ih =>
    rw [tetrahedra_after_attachment h hu hT hTS hcl,
      card_insert_of_notMem (attached_tetrahedron_not_old h hu),ih,
      card_insert_of_notMem hu]
    have hs:=h.active_card_ge_four
    omega

theorem ThreeTreeOn.tetrahedra_cover {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : (tetrahedra G).biUnion id=S := by
  classical
  induction h with
  | tetrahedron C hC => simp [tetrahedra_cliqueGraph hC]
  | @attach S G h u hu T hT hTS hcl ih =>
    rw [tetrahedra_after_attachment h hu hT hTS hcl,biUnion_insert,ih]
    change insert u T∪S=insert u S
    rw [insert_union,union_eq_right.mpr hTS]

end GraphicalZonotopes

end
end
end BundlePart42

section BundlePart43
/- Source: Papers/GraphicalZonotopes/LocalDeltas.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The elemental rows on an empty, one-point or two-point conditioning set,
expanded in the complete Möbius coordinates. -/
theorem delta_zeta_empty (y : SetFunction V) {a b : V} (hab : a ≠ b) :
    delta (zeta y) a b ∅ = y {a,b} := by
  rw [delta_zeta hab (by simp) (by simp)]
  have he : (({a,b} : Finset V).powerset.filter (fun C => a ∈ C ∧ b ∈ C)) = {{a,b}} := by
    ext C
    simp only [mem_filter, mem_powerset, mem_singleton]
    constructor
    · rintro ⟨hc, ha, hb⟩
      apply subset_antisymm hc
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    · rintro rfl
      simp
  change (∑ C ∈ ({a,b} : Finset V).powerset.filter (fun C => a∈C ∧ b∈C),y C)=y {a,b}
  rw [he]
  simp

theorem delta_zeta_singleton (y : SetFunction V) {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    delta (zeta y) a b {c} = y {a,b} + y {a,b,c} := by
  rw [delta_zeta hab (by simpa) (by simpa)]
  have he : (({a,b,c} : Finset V).powerset.filter (fun C => a ∈ C ∧ b ∈ C)) =
      {{a,b}, {a,b,c}} := by
    ext C
    simp only [mem_filter, mem_powerset, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hc, ha, hb⟩
      by_cases hcc : c ∈ C
      · right
        apply subset_antisymm hc
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      · left
        apply subset_antisymm
        · intro x hx
          have hm := hc hx
          simp only [mem_insert, mem_singleton] at hm ⊢
          rcases hm with hxa | hxb | hxc
          · exact Or.inl hxa
          · exact Or.inr hxb
          · exact False.elim (hcc (hxc ▸ hx))
        · intro x hx
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
    · rintro (rfl | rfl) <;> simp
  rw [he]
  have hne : ({a,b} : Finset V) ≠ {a,b,c} := by
    intro h
    have hc : c ∈ ({a,b} : Finset V) := by rw [h]; simp
    simp [Ne.symm hac, Ne.symm hbc] at hc
  simp [hne]

theorem delta_zeta_pair (y : SetFunction V) {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    delta (zeta y) a b {c,d} =
      y {a,b} + y {a,b,c} + y {a,b,d} + y {a,b,c,d} := by
  rw [delta_zeta hab (by simp [hac, had]) (by simp [hbc, hbd])]
  have he : (({a,b,c,d} : Finset V).powerset.filter (fun C => a ∈ C ∧ b ∈ C)) =
      {{a,b}, {a,b,c}, {a,b,d}, {a,b,c,d}} := by
    ext C
    simp only [mem_filter, mem_powerset, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hc, ha, hb⟩
      by_cases hcc : c ∈ C <;> by_cases hdc : d ∈ C
      · right; right; right
        apply subset_antisymm hc
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> assumption
      · right; left
        apply subset_antisymm
        · intro x hx
          have hm := hc hx
          simp only [mem_insert, mem_singleton] at hm ⊢
          rcases hm with hxa | hxb | hxc | hxd
          · exact Or.inl hxa
          · exact Or.inr (Or.inl hxb)
          · exact Or.inr (Or.inr hxc)
          · exact False.elim (hdc (hxd ▸ hx))
        · intro x hx
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl | rfl <;> assumption
      · right; right; left
        apply subset_antisymm
        · intro x hx
          have hm := hc hx
          simp only [mem_insert, mem_singleton] at hm ⊢
          rcases hm with hxa | hxb | hxc | hxd
          · exact Or.inl hxa
          · exact Or.inr (Or.inl hxb)
          · exact False.elim (hcc (hxc ▸ hx))
          · exact Or.inr (Or.inr hxd)
        · intro x hx
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl | rfl <;> assumption
      · left
        apply subset_antisymm
        · intro x hx
          have hm := hc hx
          simp only [mem_insert, mem_singleton] at hm ⊢
          rcases hm with hxa | hxb | hxc | hxd
          · exact Or.inl hxa
          · exact Or.inr hxb
          · exact False.elim (hcc (hxc ▸ hx))
          · exact False.elim (hdc (hxd ▸ hx))
        · intro x hx
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
    · rintro (rfl | rfl | rfl | rfl) <;> simp
  rw [he]
  have habc : ({a,b} : Finset V) ≠ {a,b,c} := by
    intro h; have hc : c ∈ ({a,b} : Finset V) := by rw [h]; simp
    simp [Ne.symm hac, Ne.symm hbc] at hc
  have habd : ({a,b} : Finset V) ≠ {a,b,d} := by
    intro h; have hd : d ∈ ({a,b} : Finset V) := by rw [h]; simp
    simp [Ne.symm had, Ne.symm hbd] at hd
  have habcd : ({a,b} : Finset V) ≠ {a,b,c,d} := by
    intro h; have hc : c ∈ ({a,b} : Finset V) := by rw [h]; simp
    simp [Ne.symm hac, Ne.symm hbc] at hc
  have hacd : ({a,b,c} : Finset V) ≠ {a,b,d} := by
    intro h; have hc : c ∈ ({a,b,d} : Finset V) := by rw [← h]; simp
    simp [Ne.symm hac, Ne.symm hbc, hcd] at hc
  have hacd' : ({a,b,c} : Finset V) ≠ {a,b,c,d} := by
    intro h; have hd : d ∈ ({a,b,c} : Finset V) := by rw [h]; simp
    simp [Ne.symm had, Ne.symm hbd, Ne.symm hcd] at hd
  have hadc' : ({a,b,d} : Finset V) ≠ {a,b,c,d} := by
    intro h; have hc : c ∈ ({a,b,d} : Finset V) := by rw [h]; simp
    simp [Ne.symm hac, Ne.symm hbc, hcd] at hc
  simp [habc, habd, habcd, hacd, hacd', hadc', add_assoc]

end GraphicalZonotopes

end
end
end BundlePart43

section BundlePart44
/- Source: Papers/GraphicalZonotopes/PositiveDecomposition.lean -/






@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace PositiveDecomposition
open Finset
open scoped BigOperators

section Minima
variable {X : Type*} [Fintype X] [Nonempty X]

def minimizingArgument (f : X → ℝ) : X :=
  Classical.choose (univ.exists_min_image f univ_nonempty)

def minimumValue (f : X → ℝ) : ℝ := f (minimizingArgument f)

theorem minimumValue_le (f : X → ℝ) (x : X) : minimumValue f ≤ f x :=
  (Classical.choose_spec (univ.exists_min_image f univ_nonempty)).2 x (mem_univ x)

theorem exists_minimumValue (f : X → ℝ) : ∃ x, f x = minimumValue f :=
  ⟨minimizingArgument f,rfl⟩

end Minima

variable {V A : Type*} [Fintype V] [LinearOrder V] [Fintype A]

abbrev Context (u v : V) := {S : Finset V // u ∉ S ∧ v ∉ S}

noncomputable instance contextFintype (u v : V) : Fintype (Context u v) := by
  classical
  infer_instance

instance contextNonempty (u v : V) : Nonempty (Context u v) :=
  ⟨⟨∅,by simp⟩⟩

def minimumSlack (z : SetFunction V) (u v : V) : ℝ :=
  minimumValue (fun S : Context u v => delta z u v S.1)

theorem minimumSlack_le (z : SetFunction V) (u v : V) (S : Finset V)
    (hu : u ∉ S) (hv : v ∉ S) : minimumSlack z u v ≤ delta z u v S :=
  minimumValue_le (fun T : Context u v => delta z u v T.1) ⟨S,hu,hv⟩

theorem exists_minimumSlack (z : SetFunction V) (u v : V) :
    ∃ S : Finset V, u ∉ S ∧ v ∉ S ∧ delta z u v S = minimumSlack z u v := by
  obtain ⟨S,hS⟩ := exists_minimumValue (fun S : Context u v => delta z u v S.1)
  exact ⟨S.1,S.2.1,S.2.2,hS⟩

theorem minimumSlack_comm (z : SetFunction V) (u v : V) :
    minimumSlack z u v = minimumSlack z v u := by
  apply le_antisymm
  · obtain ⟨S,hv,hu,hmin⟩ := exists_minimumSlack z v u
    have h := minimumSlack_le z u v S hu hv
    have he : delta z u v S=delta z v u S := by unfold delta; rw [insert_comm]; ring
    rwa [he,hmin] at h
  · obtain ⟨S,hu,hv,hmin⟩ := exists_minimumSlack z u v
    have h := minimumSlack_le z v u S hv hu
    have he : delta z v u S=delta z u v S := by unfold delta; rw [insert_comm]; ring
    rwa [he,hmin] at h

def pairPart (y : SetFunction V) : SetFunction V :=
  fun C => if C.card = 2 then y C else 0

theorem pairPart_zero {y : SetFunction V} {C : Finset V} (hC : C.card ≠ 2) :
    pairPart y C = 0 := by simp [pairPart,hC]

theorem zeta_pairSupported_delta (y : SetFunction V)
    (hy : ∀ C, C.card ≠ 2 → y C = 0) {u v : V} (huv : u ≠ v)
    {S : Finset V} (hu : u ∉ S) (hv : v ∉ S) :
    delta (zeta y) u v S = y {u,v} := by
  rw [delta_zeta huv hu hv]
  refine Finset.sum_eq_single (s := (insert u (insert v S)).powerset.filter
    (fun C => u ∈ C ∧ v ∈ C)) (f := y) ({u,v} : Finset V) ?_ ?_
  · intro C hC hne
    apply hy C
    intro hcard
    have hmem := (mem_filter.mp hC).2
    have hsub : ({u,v} : Finset V) ⊆ C :=
      insert_subset hmem.1 (singleton_subset_iff.mpr hmem.2)
    have he : ({u,v} : Finset V) = C := eq_of_subset_of_card_le hsub (by
      simpa [huv] using le_of_eq hcard)
    exact hne he.symm
  · intro hnot
    exact False.elim (hnot (by simp))

def allocation (z : SetFunction V) : SetFunction V := fun C =>
  if h : C.card = 2 then
    -minimumSlack z (C.min' (card_pos.mp (by omega))) (C.max' (card_pos.mp (by omega)))
  else 0

theorem allocation_zero (z : SetFunction V) {C : Finset V} (hC : C.card ≠ 2) :
    allocation z C = 0 := by simp [allocation,hC]

theorem allocation_pair (z : SetFunction V) {u v : V} (huv : u ≠ v) :
    allocation z {u,v} = -minimumSlack z u v := by
  simp only [allocation,card_pair huv,↓reduceDIte,min'_pair,max'_pair]
  rcases le_total u v with h | h
  · rw [min_eq_left h,max_eq_right h]
  · rw [min_eq_right h,max_eq_left h,minimumSlack_comm z v u]

theorem allocation_nonnegative (z : SetFunction V)
    (hzero : ∀ u v, u ≠ v → delta z u v ∅ = 0) (C : Finset V) :
    0 ≤ allocation z C := by
  by_cases hC : C.card = 2
  · obtain ⟨u,v,huv,rfl⟩ := card_eq_two.mp hC
    rw [allocation_pair z huv]
    have hm := minimumSlack_le z u v ∅ (by simp) (by simp)
    rw [hzero u v huv] at hm
    linarith
  · simp [allocation_zero z hC]

def adjusted (z : SetFunction V) : SetFunction V := z+zeta (allocation z)

theorem adjusted_supermodular (z : SetFunction V) : Supermodular (adjusted z) := by
  apply ElementallyNonnegative.supermodular
  intro u v huv S hu hv
  rw [adjusted,delta_add,zeta_pairSupported_delta (allocation z)
    (fun C hC => allocation_zero z hC) huv hu hv,allocation_pair z huv]
  have h := minimumSlack_le z u v S hu hv
  linarith

theorem pairSupported_zeta_normalized (y : SetFunction V)
    (hy : ∀ C, C.card ≠ 2 → y C = 0) : TranslationNormalized (zeta y) := by
  apply (zeta_normalized_iff y).mpr
  exact ⟨hy ∅ (by simp),fun v => hy {v} (by simp)⟩

theorem adjusted_normalized {z : SetFunction V} (hz : TranslationNormalized z) :
    TranslationNormalized (adjusted z) := by
  have ha := pairSupported_zeta_normalized (allocation z)
    (fun C hC => allocation_zero z hC)
  exact ⟨by change z ∅+zeta (allocation z) ∅=0; rw [hz.1,ha.1,add_zero],
    fun v => by change z {v}+zeta (allocation z) {v}=0; rw [hz.2 v,ha.2 v,add_zero]⟩

/-- Exact independence of the conditioning variables used by the separate
higher-coefficient blocks. For triangle classes this is proved by partitioning
the common-neighbor variables of each edge. -/
def IndependentSlacks (h : A → SetFunction V) : Prop :=
  ∀ u v, u ≠ v → ∀ S : A → Context u v,
    ∃ T : Context u v, ∀ a, delta (h a) u v T.1 = delta (h a) u v (S a).1

/-- Disjoint conditioning-variable blocks give exact independent
realizability, not just a lower bound on the sum of their minima. -/
theorem independentSlacks_of_disjoint_variables (h : A → SetFunction V)
    (hblocks : ∀ u v, u ≠ v → ∃ I : A → Finset V,
      (∀ a b, a ≠ b → Disjoint (I a) (I b)) ∧
      ∀ a S, u ∉ S → v ∉ S →
        delta (h a) u v S = delta (h a) u v (S ∩ I a)) :
    IndependentSlacks h := by
  classical
  intro u v huv S
  obtain ⟨I,hdisj,hdep⟩ := hblocks u v huv
  let T : Finset V := univ.biUnion (fun a => (S a).1 ∩ I a)
  have huT : u ∉ T := by
    intro hu
    obtain ⟨a,ha,hu⟩ := mem_biUnion.mp hu
    exact (S a).2.1 (mem_inter.mp hu).1
  have hvT : v ∉ T := by
    intro hv
    obtain ⟨a,ha,hv⟩ := mem_biUnion.mp hv
    exact (S a).2.2 (mem_inter.mp hv).1
  refine ⟨⟨T,huT,hvT⟩,?_⟩
  intro a
  have he : T ∩ I a = (S a).1 ∩ I a := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxT,hxa⟩ := mem_inter.mp hx
      obtain ⟨b,hb,hxb⟩ := mem_biUnion.mp hxT
      by_cases hba : b = a
      · subst b
        exact hxb
      · exact False.elim ((Finset.disjoint_left.mp (hdisj b a hba))
          (mem_inter.mp hxb).2 hxa)
    · intro hx
      exact mem_inter.mpr ⟨mem_biUnion.mpr ⟨a,mem_univ a,hx⟩,(mem_inter.mp hx).2⟩
  calc
    delta (h a) u v T = delta (h a) u v (T ∩ I a) := hdep a T huT hvT
    _ = delta (h a) u v ((S a).1 ∩ I a) := by rw [he]
    _ = delta (h a) u v (S a).1 := (hdep a (S a).1 (S a).2.1 (S a).2.2).symm

def residual (y : SetFunction V) (h : A → SetFunction V) : SetFunction V :=
  fun C => if C.card = 2 then y C-∑ a, allocation (h a) C else 0

theorem residual_zero (y : SetFunction V) (h : A → SetFunction V)
    {C : Finset V} (hC : C.card ≠ 2) : residual y h C = 0 := by
  simp [residual,hC]

theorem residual_nonnegative (y z : SetFunction V) (h : A → SetFunction V)
    (hs : Supermodular z) (he : z = zeta (pairPart y)+∑ a, h a)
    (hind : IndependentSlacks h) (C : Finset V) : 0 ≤ residual y h C := by
  classical
  by_cases hC : C.card = 2
  · obtain ⟨u,v,huv,rfl⟩ := card_eq_two.mp hC
    choose S hu hv hmin using fun a : A => exists_minimumSlack (h a) u v
    let choice : A → Context u v := fun a => ⟨S a,hu a,hv a⟩
    obtain ⟨T,hT⟩ := hind u v huv choice
    have hpositive := hs.elemental u v huv T.1 T.2.1 T.2.2
    rw [he,delta_add,zeta_pairSupported_delta (pairPart y)
      (fun C hC => pairPart_zero hC) huv T.2.1 T.2.2,delta_sum] at hpositive
    have hmins : (∑ a, delta (h a) u v T.1) = ∑ a, minimumSlack (h a) u v := by
      apply sum_congr rfl
      intro a ha
      exact (hT a).trans (hmin a)
    rw [hmins] at hpositive
    simp only [pairPart,card_pair huv,if_pos] at hpositive
    simp only [residual,card_pair huv,if_pos,allocation_pair _ huv,sum_neg_distrib]
    linarith
  · simp [residual_zero y h hC]

theorem residual_supermodular (y z : SetFunction V) (h : A → SetFunction V)
    (hs : Supermodular z) (he : z = zeta (pairPart y)+∑ a, h a)
    (hind : IndependentSlacks h) : Supermodular (zeta (residual y h)) := by
  apply ElementallyNonnegative.supermodular
  intro u v huv S hu hv
  rw [zeta_pairSupported_delta (residual y h)
    (fun C hC => residual_zero y h hC) huv hu hv]
  exact residual_nonnegative y z h hs he hind _

theorem allocation_add_residual (y : SetFunction V) (h : A → SetFunction V) :
    (∑ a, allocation (h a))+residual y h = pairPart y := by
  classical
  funext C
  by_cases hC : C.card = 2
  · simp only [Pi.add_apply,Finset.sum_apply,residual,pairPart,if_pos hC]
    ring
  · simp [hC,residual,pairPart,allocation_zero]

theorem adjusted_sum_reconstruct (y z : SetFunction V) (h : A → SetFunction V)
    (he : z = zeta (pairPart y)+∑ a, h a) :
    (∑ a, adjusted (h a))+zeta (residual y h) = z := by
  classical
  have hadd : (∑ a, zeta (allocation (h a)))+zeta (residual y h) = zeta (pairPart y) := by
    change (∑ a, zetaLinear (allocation (h a)))+zetaLinear (residual y h) = _
    rw [← map_sum,← map_add,allocation_add_residual]
    rfl
  simp only [adjusted,sum_add_distrib]
  rw [add_assoc,hadd,he,add_comm]

/-- The positivity and exact reconstruction part of Lemma4.2. Every block
receives precisely minus its edgewise conditional minimum; the leftover pair
coefficients are nonnegative. The independence hypothesis is an explicit
mathematical obligation for the triangle-class dictionary, not an assumed
property of arbitrary coefficient partitions. -/
theorem positive_block_decomposition (y z : SetFunction V) (h : A → SetFunction V)
    (hs : Supermodular z) (he : z = zeta (pairPart y)+∑ a, h a)
    (hn : ∀ a, TranslationNormalized (h a))
    (hzero : ∀ a u v, u ≠ v → delta (h a) u v ∅ = 0)
    (hind : IndependentSlacks h) :
    (∀ a, TranslationNormalized (adjusted (h a)) ∧ Supermodular (adjusted (h a))) ∧
    (∀ a C, 0 ≤ allocation (h a) C) ∧
    (∀ C, 0 ≤ residual y h C) ∧
    TranslationNormalized (zeta (residual y h)) ∧
    Supermodular (zeta (residual y h)) ∧
    (∑ a, adjusted (h a))+zeta (residual y h) = z := by
  refine ⟨fun a => ⟨adjusted_normalized (hn a),adjusted_supermodular (h a)⟩,
    fun a C => allocation_nonnegative (h a) (hzero a) C,
    residual_nonnegative y z h hs he hind,
    pairSupported_zeta_normalized _ (fun C hC => residual_zero y h hC),
    residual_supermodular y z h hs he hind,adjusted_sum_reconstruct y z h he⟩

end PositiveDecomposition
end GraphicalZonotopes

end
end
end BundlePart44

section BundlePart45
/- Source: Papers/GraphicalZonotopes/TriangleClasses.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace PositiveDecomposition
open Finset
open scoped BigOperators
variable {V A : Type*} [Fintype V] [LinearOrder V] [Fintype A]

/-- Compatibility of a coefficient partition with the triangles in every
nonzero higher clique. The coarse and refined triangle-class partitions both
have this property; an arbitrary coefficient partition need not. -/
def ClassCompatible (y : SetFunction V) (classOf : Finset V → A) : Prop :=
  ∀ C, 4 ≤ C.card → y C ≠ 0 → ∀ T, T.card = 3 → T ⊆ C → classOf T = classOf C

def classCoefficients (y : SetFunction V) (classOf : Finset V → A)
    (a : A) : SetFunction V := by
  classical
  exact fun C => if 3 ≤ C.card ∧ classOf C = a then y C else 0

def higherClass (y : SetFunction V) (classOf : Finset V → A) (a : A) : SetFunction V :=
  zeta (classCoefficients y classOf a)

theorem classCoefficients_nonzero {y : SetFunction V} {classOf : Finset V → A}
    {a : A} {C : Finset V} (h : classCoefficients y classOf a C ≠ 0) :
    3 ≤ C.card ∧ classOf C = a ∧ y C ≠ 0 := by
  classical
  by_cases hC : 3 ≤ C.card ∧ classOf C = a
  · simp only [classCoefficients,if_pos hC] at h
    exact ⟨hC.1,hC.2,h⟩
  · simp [classCoefficients,hC] at h

theorem higherClass_normalized (y : SetFunction V) (classOf : Finset V → A) (a : A) :
    TranslationNormalized (higherClass y classOf a) := by
  classical
  apply (zeta_normalized_iff _).mpr
  simp [classCoefficients]

theorem higherClass_delta_empty (y : SetFunction V) (classOf : Finset V → A) (a : A)
    (u v : V) (huv : u ≠ v) : delta (higherClass y classOf a) u v ∅ = 0 := by
  classical
  rw [higherClass,delta_zeta_empty _ huv]
  simp [classCoefficients,card_pair huv]

theorem class_coefficients_reconstruct (y : SetFunction V) (classOf : Finset V → A)
    (hy : y ∅ = 0 ∧ ∀ v, y {v} = 0) :
    pairPart y+∑ a, classCoefficients y classOf a = y := by
  classical
  funext C
  by_cases hC : 3 ≤ C.card
  · have hC2 : C.card ≠ 2 := by omega
    simp [pairPart,classCoefficients,hC,hC2]
  · have hsum : (∑ a, classCoefficients y classOf a C) = 0 := by
      simp [classCoefficients,hC]
    simp only [Pi.add_apply,Finset.sum_apply]
    rw [hsum,add_zero]
    by_cases hC2 : C.card = 2
    · simp [pairPart,hC2]
    · have hsmall : C.card = 0 ∨ C.card = 1 := by omega
      rcases hsmall with he | he
      · rw [card_eq_zero.mp he]
        simp [pairPart,hy.1]
      · obtain ⟨v,rfl⟩ := card_eq_one.mp he
        simp [pairPart,hy.2]

theorem higher_classes_reconstruct (y : SetFunction V) (classOf : Finset V → A)
    (hy : y ∅ = 0 ∧ ∀ v, y {v} = 0) :
    zeta y = zeta (pairPart y)+∑ a, higherClass y classOf a := by
  have he := congrArg zetaLinear (class_coefficients_reconstruct y classOf hy)
  rw [map_add,map_sum] at he
  change zeta (pairPart y)+(∑ a,zeta (classCoefficients y classOf a))=zeta y at he
  exact he.symm

def classVariables (classOf : Finset V → A) (u v : V) (a : A) : Finset V := by
  classical
  exact univ.filter (fun w => w ≠ u ∧ w ≠ v ∧ classOf {u,v,w} = a)

theorem classVariables_disjoint (classOf : Finset V → A) (u v : V)
    (a b : A) (hab : a ≠ b) :
    Disjoint (classVariables classOf u v a) (classVariables classOf u v b) := by
  classical
  rw [Finset.disjoint_left]
  intro w hwa hwb
  have ha := (mem_filter.mp hwa).2.2.2
  have hb := (mem_filter.mp hwb).2.2.2
  exact hab (ha.symm.trans hb)

theorem remaining_vertex_in_classVariables {y : SetFunction V}
    {classOf : Finset V → A} (hcomp : ClassCompatible y classOf)
    {a : A} {C : Finset V} (hC : classCoefficients y classOf a C ≠ 0)
    {u v w : V} (huv : u ≠ v) (hu : u ∈ C) (hv : v ∈ C) (hw : w ∈ C)
    (hwu : w ≠ u) (hwv : w ≠ v) : w ∈ classVariables classOf u v a := by
  classical
  obtain ⟨hcard,hclass,hyC⟩ := classCoefficients_nonzero hC
  have hTcard : ({u,v,w} : Finset V).card = 3 := by
    simp [huv,hwu,hwv,Ne.symm hwu,Ne.symm hwv]
  have hsub : ({u,v,w} : Finset V) ⊆ C := by
    intro x hx
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hclasses : classOf {u,v,w} = classOf C := by
    by_cases hfour : 4 ≤ C.card
    · exact hcomp C hfour hyC _ hTcard hsub
    · have he : ({u,v,w} : Finset V) = C :=
        eq_of_subset_of_card_le hsub (by omega)
      rw [he]
  exact mem_filter.mpr ⟨mem_univ _,hwu,hwv,hclasses.trans hclass⟩

theorem pair_subset_inter_iff {C S I : Finset V} {u v : V}
    (hrem : ∀ w ∈ C, w ≠ u → w ≠ v → w ∈ I) :
    C ⊆ insert u (insert v S) ↔ C ⊆ insert u (insert v (S ∩ I)) := by
  constructor
  · intro h w hw
    have hm := h hw
    simp only [mem_insert] at hm ⊢
    rcases hm with hwu | hwv | hwS
    · exact Or.inl hwu
    · exact Or.inr (Or.inl hwv)
    · by_cases hwu : w = u
      · exact Or.inl hwu
      · by_cases hwv : w = v
        · exact Or.inr (Or.inl hwv)
        · exact Or.inr (Or.inr (mem_inter.mpr ⟨hwS,hrem w hw hwu hwv⟩))
  · intro h
    exact h.trans (insert_subset_insert _ (insert_subset_insert _ inter_subset_left))

theorem higherClass_uses_classVariables {y : SetFunction V} {classOf : Finset V → A}
    (hcomp : ClassCompatible y classOf) (a : A) {u v : V} (huv : u ≠ v)
    {S : Finset V} (hu : u ∉ S) (hv : v ∉ S) :
    delta (higherClass y classOf a) u v S =
      delta (higherClass y classOf a) u v (S ∩ classVariables classOf u v a) := by
  classical
  have hu' : u ∉ S ∩ classVariables classOf u v a := by simp [hu]
  have hv' : v ∉ S ∩ classVariables classOf u v a := by simp [hv]
  rw [higherClass,zeta_eq_sum_monomials,delta_sum,delta_sum]
  apply sum_congr rfl
  intro C hC
  rw [delta_smul,delta_smul,delta_setMonomial huv hu hv,delta_setMonomial huv hu' hv']
  by_cases hzero : classCoefficients y classOf a C = 0
  · simp [hzero]
  · by_cases huC : u ∈ C
    · by_cases hvC : v ∈ C
      · have hi := pair_subset_inter_iff (S := S)
          (fun w hw hwu hwv => remaining_vertex_in_classVariables hcomp hzero huv huC hvC hw hwu hwv)
        simp only [hi]
      · simp [hvC]
    · simp [huC]

theorem higherClasses_independent {y : SetFunction V} {classOf : Finset V → A}
    (hcomp : ClassCompatible y classOf) : IndependentSlacks (higherClass y classOf) := by
  apply independentSlacks_of_disjoint_variables
  intro u v huv
  refine ⟨classVariables classOf u v,classVariables_disjoint classOf u v,?_⟩
  intro a S hu hv
  exact higherClass_uses_classVariables hcomp a huv hu hv

theorem higherClass_graphical {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y) (classOf : Finset V → A) (a : A) :
    Graphical G (higherClass y classOf a) := by
  classical
  apply ((cliqueSupported_iff G _).mp ?_).2
  refine ⟨by simp [classCoefficients],fun v => by simp [classCoefficients],?_⟩
  intro C u v hu hv huv hnon
  have hz := hy.2.2 C u v hu hv huv hnon
  simp [classCoefficients,hz]

theorem minimumSlack_eq_zero {z : SetFunction V} {u v : V}
    (hz : ∀ S, u ∉ S → v ∉ S → delta z u v S = 0) : minimumSlack z u v = 0 := by
  obtain ⟨S,hu,hv,he⟩ := exists_minimumSlack z u v
  exact he.symm.trans (hz S hu hv)

theorem adjusted_graphical {G : SimpleGraph V} {z : SetFunction V}
    (hz : Graphical G z) : Graphical G (adjusted z) := by
  intro u v huv hnon S hu hv
  have hm := minimumSlack_eq_zero (hz u v huv hnon)
  rw [adjusted,delta_add,hz u v huv hnon S hu hv,
    zeta_pairSupported_delta _ (fun C hC => allocation_zero z hC) huv hu hv,
    allocation_pair z huv,hm]
  ring

/-- The actual triangle-class positive decomposition of the supermodular
function, before the separate connected-component construction of its class
index. The coefficients and all elemental rows are unchanged. -/
theorem compatible_class_decomposition {G : SimpleGraph V} (y : SetFunction V)
    (hy : CliqueSupported G y) (hs : Supermodular (zeta y))
    (classOf : Finset V → A) (hcomp : ClassCompatible y classOf) :
    (∀ a, TranslationNormalized (adjusted (higherClass y classOf a)) ∧
      Supermodular (adjusted (higherClass y classOf a)) ∧
      Graphical G (adjusted (higherClass y classOf a))) ∧
    (∀ C, 0 ≤ residual y (higherClass y classOf) C) ∧
    TranslationNormalized (zeta (residual y (higherClass y classOf))) ∧
    Supermodular (zeta (residual y (higherClass y classOf))) ∧
    (∑ a, adjusted (higherClass y classOf a))+
      zeta (residual y (higherClass y classOf)) = zeta y := by
  have he := higher_classes_reconstruct y classOf ⟨hy.1,hy.2.1⟩
  obtain ⟨hp,ha,hr,hn,hsr,hre⟩ := positive_block_decomposition y (zeta y)
    (higherClass y classOf) hs he (higherClass_normalized y classOf)
    (higherClass_delta_empty y classOf) (higherClasses_independent hcomp)
  exact ⟨fun a => ⟨(hp a).1,(hp a).2,
    adjusted_graphical (higherClass_graphical hy classOf a)⟩,hr,hn,hsr,hre⟩

end PositiveDecomposition
end GraphicalZonotopes

end
end
end BundlePart45

section BundlePart46
/- Source: Papers/GraphicalZonotopes/TetrahedralGrowth.lean -/






@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The induced graph, represented on the original vertex type with isolated
vertices outside the displayed set. -/
def inducedOn (G : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ S ∧ v ∈ S
  symm := ⟨fun _ _ h => ⟨G.adj_symm h.1,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

/-- A tetrahedron followed by vertices attached along existing triangles of
the ambient graph. Extra ambient edges are allowed; equality in the eventual
edge count will prove that there are no extras. -/
inductive TetrahedralGrowth (G : SimpleGraph V) : Finset V → Prop
  | base (C : Finset V) (hcard : C.card = 4) (hcl : G.IsClique C) :
      TetrahedralGrowth G C
  | attach {S : Finset V} (h : TetrahedralGrowth G S) (u : V) (hu : u ∉ S)
      (T : Finset V) (hcard : T.card = 3) (hsub : T ⊆ S) (hcl : G.IsClique T)
      (hadj : ∀ v ∈ T, G.Adj u v) : TetrahedralGrowth G (insert u S)

theorem TetrahedralGrowth.card_ge_four {G : SimpleGraph V} {S : Finset V}
    (h : TetrahedralGrowth G S) : 4 ≤ S.card := by
  induction h with
  | base C hc hcl => omega
  | attach h u hu T hT hsub hcl hadj ih =>
    rw [card_insert_of_notMem hu]
    omega

/-- A tetrahedron sharing a triangle with the vertices already present adds
at most one vertex. Steps adding no vertex need no extra assumption. -/
theorem TetrahedralGrowth.extend_fourClique {G : SimpleGraph V} {S : Finset V}
    (h : TetrahedralGrowth G S) (C : Finset V) (hc : C.card = 4)
    (hcl : G.IsClique C) (hover : 3 ≤ (C ∩ S).card) :
    TetrahedralGrowth G (S ∪ C) := by
  have hcard := card_sdiff_add_card_inter C S
  have hsmall : (C \ S).card = 0 ∨ (C \ S).card = 1 := by omega
  rcases hsmall with hz | ho
  · have hsub : C ⊆ S := sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp hz)
    simpa only [union_eq_left.mpr hsub] using h
  · obtain ⟨u,hu⟩ := card_eq_one.mp ho
    have humem : u ∈ C \ S := by rw [hu]; exact mem_singleton_self u
    have huC : u ∈ C := (mem_sdiff.mp humem).1
    have huS : u ∉ S := (mem_sdiff.mp humem).2
    let T := C.erase u
    have hTcard : T.card = 3 := by
      dsimp [T]
      rw [card_erase_of_mem huC,hc]
    have hTS : T ⊆ S := by
      intro v hv
      obtain ⟨hvu,hvC⟩ := mem_erase.mp hv
      by_contra hvS
      have hm : v ∈ C \ S := mem_sdiff.mpr ⟨hvC,hvS⟩
      rw [hu] at hm
      exact hvu (mem_singleton.mp hm)
    have hTcl : G.IsClique T := fun v hv w hw hvw =>
      hcl (mem_of_mem_erase hv) (mem_of_mem_erase hw) hvw
    have hA : ∀ v ∈ T, G.Adj u v := by
      intro v hv
      have hm := mem_erase.mp hv
      exact hcl huC hm.2 (Ne.symm hm.1)
    have hcover : S ∪ C = insert u S := by
      ext v
      simp only [mem_union,mem_insert]
      constructor
      · rintro (hv | hv)
        · exact Or.inr hv
        · by_cases hvu : v = u
          · exact Or.inl hvu
          · exact Or.inr (hTS (mem_erase.mpr ⟨hvu,hv⟩))
      · rintro (rfl | hv)
        · exact Or.inr huC
        · exact Or.inl hv
    rw [hcover]
    exact TetrahedralGrowth.attach h u huS T hTcard hTS hTcl hA

def tetrahedronGraph (F : Finset (Finset V)) : SimpleGraph {C : Finset V // C ∈ F} where
  Adj C D := C ≠ D ∧ 3 ≤ (C.1 ∩ D.1).card
  symm := ⟨fun C D h => ⟨Ne.symm h.1,by simpa only [inter_comm] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Every nonempty triangle-connected family of tetrahedra has a growth
ordering on its entire vertex union. The finite maximum argument closes under
every neighboring tetrahedron, so this includes all members of the component. -/
theorem tetrahedralGrowth_of_connected_family (G : SimpleGraph V)
    (F : Finset (Finset V)) (hne : F.Nonempty)
    (hcl : ∀ C ∈ F, C.card = 4 ∧ G.IsClique C)
    (hconn : (tetrahedronGraph F).Preconnected) :
    TetrahedralGrowth G (F.biUnion id) := by
  classical
  obtain ⟨C₀,hC₀⟩ := hne
  let S := F.biUnion id
  have hCS : ∀ C ∈ F, C ⊆ S := by
    intro C hC v hv
    exact mem_biUnion.mpr ⟨C,hC,hv⟩
  let candidates : Finset (Finset V) := univ.filter
    (fun U => C₀ ⊆ U ∧ U ⊆ S ∧ TetrahedralGrowth G U)
  have hbase : C₀ ∈ candidates := by
    apply mem_filter.mpr
    exact ⟨mem_univ _,Subset.rfl,hCS C₀ hC₀,
      TetrahedralGrowth.base C₀ (hcl C₀ hC₀).1 (hcl C₀ hC₀).2⟩
  obtain ⟨U,hU,hmax⟩ := candidates.exists_max_image Finset.card ⟨C₀,hbase⟩
  obtain ⟨hC₀U,hUS,hgrowth⟩ := (mem_filter.mp hU).2
  have hclosed : ∀ C ∈ F, 3 ≤ (C ∩ U).card → C ⊆ U := by
    intro C hC hover
    have hg := hgrowth.extend_fourClique C (hcl C hC).1 (hcl C hC).2 hover
    have hcand : U ∪ C ∈ candidates := by
      apply mem_filter.mpr
      refine ⟨mem_univ _,hC₀U.trans subset_union_left,?_,hg⟩
      exact union_subset hUS (hCS C hC)
    have he : U ∪ C = U :=
      (eq_of_subset_of_card_le subset_union_left (hmax _ hcand)).symm
    intro v hv
    rw [← he]
    exact mem_union_right U hv
  have hall : ∀ C : {C : Finset V // C ∈ F}, C.1 ⊆ U := by
    intro C
    have hp := (SimpleGraph.reachable_iff_reflTransGen
      (G := tetrahedronGraph F) ⟨C₀,hC₀⟩ C).mp (hconn _ _)
    induction hp with
    | refl => exact hC₀U
    | @tail D E hp hDE ih =>
      apply hclosed E.1 E.2
      refine hDE.2.trans (card_le_card ?_)
      intro v hv
      exact mem_inter.mpr ⟨(mem_inter.mp hv).2,ih (mem_inter.mp hv).1⟩
  have hSU : S ⊆ U := by
    intro v hv
    obtain ⟨C,hC,hvC⟩ := mem_biUnion.mp hv
    exact hall ⟨C,hC⟩ hvC
  have he : U = S := subset_antisymm hUS hSU
  simpa only [he,S] using hgrowth

theorem inducedOn_clique {G : SimpleGraph V} {S : Finset V}
    (hcl : G.IsClique S) : inducedOn G S = cliqueGraph S := by
  ext u v
  constructor
  · intro h
    exact ⟨G.ne_of_adj h.1,h.2⟩
  · rintro ⟨hne,hu,hv⟩
    exact ⟨hcl hu hv hne,hu,hv⟩

theorem edgeFamily_cliqueGraph (S : Finset V) :
    edgeFamily (cliqueGraph S) = S.powersetCard 2 := by
  classical
  ext C
  rw [mem_edgeFamily,mem_powersetCard]
  constructor
  · rintro ⟨hc,hcl⟩
    refine ⟨?_,hc⟩
    obtain ⟨u,v,huv,rfl⟩ := card_eq_two.mp hc
    have h := hcl u (by simp) v (by simp) huv
    exact insert_subset h.2.1 (singleton_subset_iff.mpr h.2.2)
  · rintro ⟨hsub,hc⟩
    exact ⟨hc,fun u hu v hv huv => ⟨huv,hsub hu,hsub hv⟩⟩

def earlierNeighbors (G : SimpleGraph V) (S : Finset V) (u : V) : Finset V := by
  classical
  exact S.filter (G.Adj u)

@[simp] theorem mem_earlierNeighbors (G : SimpleGraph V) (S : Finset V) (u v : V) :
    v ∈ earlierNeighbors G S u ↔ v ∈ S ∧ G.Adj u v := by
  classical
  simp [earlierNeighbors]

def addedPairs (G : SimpleGraph V) (S : Finset V) (u : V) : Finset (Finset V) :=
  (earlierNeighbors G S u).image (fun v => {u,v})

theorem addedPairs_card (G : SimpleGraph V) (S : Finset V) (u : V) :
    (addedPairs G S u).card = (earlierNeighbors G S u).card := by
  apply card_image_of_injOn
  intro v hv w hw he
  have huv := G.ne_of_adj ((mem_earlierNeighbors G S u v).mp hv).2
  change ({u,v} : Finset V)=({u,w} : Finset V) at he
  have hmem : v ∈ ({u,w} : Finset V) := by rw [← he]; simp
  rcases mem_insert.mp hmem with h | h
  · exact False.elim (huv h.symm)
  · exact mem_singleton.mp h

theorem edgeFamily_inducedOn_insert (G : SimpleGraph V) (S : Finset V) (u : V)
    (hu : u ∉ S) :
    edgeFamily (inducedOn G (insert u S)) = edgeFamily (inducedOn G S) ∪ addedPairs G S u := by
  classical
  ext C
  rw [mem_union]
  constructor
  · intro hC
    obtain ⟨hc,hcl⟩ := (mem_edgeFamily _ C).mp hC
    obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hc
    have h := hcl a (by simp) b (by simp) hab
    change G.Adj a b ∧ a ∈ insert u S ∧ b ∈ insert u S at h
    by_cases hau : a = u
    · subst a
      have hbS : b ∈ S := (mem_insert.mp h.2.2).resolve_left (Ne.symm hab)
      exact Or.inr (mem_image.mpr ⟨b,(mem_earlierNeighbors G S u b).mpr ⟨hbS,h.1⟩,rfl⟩)
    · by_cases hbu : b = u
      · subst b
        have haS : a ∈ S := (mem_insert.mp h.2.1).resolve_left hau
        exact Or.inr (mem_image.mpr ⟨a,(mem_earlierNeighbors G S u a).mpr
          ⟨haS,G.adj_symm h.1⟩,pair_comm u a⟩)
      · apply Or.inl
        apply (pair_mem_edgeFamily _ hab).mpr
        exact ⟨h.1,(mem_insert.mp h.2.1).resolve_left hau,
          (mem_insert.mp h.2.2).resolve_left hbu⟩
  · rintro (hC | hC)
    · obtain ⟨hc,hcl⟩ := (mem_edgeFamily _ C).mp hC
      apply (mem_edgeFamily _ C).mpr
      refine ⟨hc,?_⟩
      intro a ha b hb hab
      have h := hcl a ha b hb hab
      exact ⟨h.1,mem_insert_of_mem h.2.1,mem_insert_of_mem h.2.2⟩
    · obtain ⟨v,hv,rfl⟩ := mem_image.mp hC
      obtain ⟨hvS,huv⟩ := (mem_earlierNeighbors G S u v).mp hv
      exact (pair_mem_edgeFamily _ (G.ne_of_adj huv)).mpr
        ⟨huv,mem_insert_self _ _,mem_insert_of_mem hvS⟩

theorem edgeFamily_addedPairs_disjoint (G : SimpleGraph V) (S : Finset V) (u : V)
    (hu : u ∉ S) : Disjoint (edgeFamily (inducedOn G S)) (addedPairs G S u) := by
  classical
  rw [Finset.disjoint_left]
  intro C hC hnew
  obtain ⟨v,hv,rfl⟩ := mem_image.mp hnew
  have huv := G.ne_of_adj ((mem_earlierNeighbors G S u v).mp hv).2
  have h := (pair_mem_edgeFamily _ huv).mp hC
  exact hu h.2.1

theorem induced_edge_count_insert (G : SimpleGraph V) (S : Finset V) (u : V)
    (hu : u ∉ S) :
    (edgeFamily (inducedOn G (insert u S))).card =
      (edgeFamily (inducedOn G S)).card + (earlierNeighbors G S u).card := by
  rw [edgeFamily_inducedOn_insert G S u hu,
    card_union_of_disjoint (edgeFamily_addedPairs_disjoint G S u hu),addedPairs_card]

theorem inducedOn_insert_eq_attach (G : SimpleGraph V) (S T : Finset V) (u : V)
    (hu : u ∉ S) (hT : earlierNeighbors G S u = T) :
    inducedOn G (insert u S) = inducedOn G S ⊔ attachmentStar u T := by
  ext v w
  change (G.Adj v w ∧ v ∈ insert u S ∧ w ∈ insert u S) ↔
    (G.Adj v w ∧ v ∈ S ∧ w ∈ S) ∨
      (v ≠ w ∧ ((v = u ∧ w ∈ T) ∨ (w = u ∧ v ∈ T)))
  rw [← hT]
  simp only [mem_earlierNeighbors,mem_insert]
  constructor
  · rintro ⟨hvw,hv,hw⟩
    have hvwne := G.ne_of_adj hvw
    rcases hv with rfl | hv
    · exact Or.inr ⟨hvwne,Or.inl ⟨rfl,hw.resolve_left (Ne.symm hvwne),hvw⟩⟩
    · rcases hw with rfl | hw
      · exact Or.inr ⟨hvwne,Or.inr ⟨rfl,hv,G.adj_symm hvw⟩⟩
      · exact Or.inl ⟨hvw,hv,hw⟩
  · rintro (⟨hvw,hv,hw⟩ | ⟨hne,(⟨rfl,hw,huw⟩ | ⟨rfl,hv,huv⟩)⟩)
    · exact ⟨hvw,Or.inr hv,Or.inr hw⟩
    · exact ⟨huw,Or.inl rfl,Or.inr hw⟩
    · exact ⟨G.adj_symm huv,Or.inr hv,Or.inl rfl⟩

/-- The complete combinatorial counting step of Theorem4.1, including the
necessary 3-tree equality condition. It applies to arbitrary ambient graphs,
with no K5-free assumption and no bound on the number of vertices. -/
theorem TetrahedralGrowth.edge_bound_and_equality {G : SimpleGraph V} {S : Finset V}
    (h : TetrahedralGrowth G S) :
    3*S.card-6 ≤ (edgeFamily (inducedOn G S)).card ∧
      ((edgeFamily (inducedOn G S)).card = 3*S.card-6 →
        ThreeTreeOn S (inducedOn G S)) := by
  classical
  induction h with
  | base C hc hcl =>
    rw [inducedOn_clique hcl]
    have he : (edgeFamily (cliqueGraph C)).card = 6 := by
      rw [edgeFamily_cliqueGraph,card_powersetCard,hc]
      decide
    refine ⟨?_,?_⟩
    · omega
    · intro _
      exact ThreeTreeOn.tetrahedron C hc
  | @attach S h u hu T hT hsub hcl hadj ih =>
    have hS := h.card_ge_four
    have hTN : T ⊆ earlierNeighbors G S u := by
      intro v hv
      exact (mem_earlierNeighbors G S u v).mpr ⟨hsub hv,hadj v hv⟩
    have hN : 3 ≤ (earlierNeighbors G S u).card := by
      simpa only [hT] using card_le_card hTN
    rw [card_insert_of_notMem hu,induced_edge_count_insert G S u hu]
    refine ⟨by omega,?_⟩
    intro he
    have hprev : (edgeFamily (inducedOn G S)).card = 3*S.card-6 := by omega
    have hNcard : (earlierNeighbors G S u).card = 3 := by omega
    have hNT : earlierNeighbors G S u = T :=
      (eq_of_subset_of_card_le hTN (by omega)).symm
    rw [inducedOn_insert_eq_attach G S T u hu hNT]
    apply ThreeTreeOn.attach (ih.2 hprev) u hu T hT hsub
    intro v hv w hw hvw
    exact ⟨hcl hv hw hvw,hsub hv,hsub hw⟩

@[simp] theorem inducedOn_univ (G : SimpleGraph V) : inducedOn G univ = G := by
  ext u v
  simp [inducedOn]

theorem edge_bound_of_connected_tetrahedra (G : SimpleGraph V)
    (F : Finset (Finset V)) (hne : F.Nonempty)
    (hcl : ∀ C ∈ F, C.card = 4 ∧ G.IsClique C)
    (hconn : (tetrahedronGraph F).Preconnected) (hcover : F.biUnion id = univ) :
    3*Fintype.card V-6 ≤ (edgeFamily G).card ∧
      ((edgeFamily G).card = 3*Fintype.card V-6 → IsThreeTree G) := by
  have hgrowth := tetrahedralGrowth_of_connected_family G F hne hcl hconn
  rw [hcover] at hgrowth
  simpa [IsThreeTree] using hgrowth.edge_bound_and_equality

end GraphicalZonotopes

end
end
end BundlePart46

section BundlePart47
/- Source: Papers/GraphicalZonotopes/CliqueComponents.lean -/






@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
namespace TriangleComponents
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The graph of all tetrahedra of the actual direction graph, with adjacency
exactly across a shared triangle. Non-tetrahedral finite subsets are isolated;
this harmless ambient choice avoids any nonempty-type assumption. -/
def cliqueGraph (G : SimpleGraph V) : SimpleGraph (Finset V) where
  Adj C D := C.card = 4 ∧ D.card = 4 ∧ G.IsClique C ∧ G.IsClique D ∧
    C ≠ D ∧ 3 ≤ (C ∩ D).card
  symm := ⟨fun C D h => ⟨h.2.1,h.1,h.2.2.2.1,h.2.2.1,Ne.symm h.2.2.2.2.1,
    by simpa only [inter_comm] using h.2.2.2.2.2⟩⟩
  loopless := ⟨fun _ h => h.2.2.2.2.1 rfl⟩

theorem reachable_of_shared_triangle {G : SimpleGraph V} {C D T : Finset V}
    (hC : C.card = 4) (hD : D.card = 4) (hcC : G.IsClique C) (hcD : G.IsClique D)
    (hT : T.card = 3) (hTC : T ⊆ C) (hTD : T ⊆ D) :
    (cliqueGraph G).Reachable C D := by
  by_cases he : C = D
  · subst D
    exact SimpleGraph.Reachable.rfl
  · apply SimpleGraph.Adj.reachable
    exact ⟨hC,hD,hcC,hcD,he,by
      have h := card_le_card (subset_inter hTC hTD)
      omega⟩

/-- All four-element subsets of one clique lie in one triangle-connected
component. The proof exchanges one vertex at a time, and decreases the exact
cardinality of the set difference at each step. -/
theorem tetrahedra_in_clique_reachable {G : SimpleGraph V} {C : Finset V}
    (hC : G.IsClique C) {D E : Finset V} (hD : D.card = 4) (hE : E.card = 4)
    (hDC : D ⊆ C) (hEC : E ⊆ C) : (cliqueGraph G).Reachable D E := by
  classical
  suffices h : ∀ n D, (D \ E).card = n → D.card = 4 → D ⊆ C →
      (cliqueGraph G).Reachable D E from h _ D rfl hD hDC
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro D hn hD hDC
    by_cases hDE : D = E
    · subst D
      exact SimpleGraph.Reachable.rfl
    · have hdiff : (D \ E).Nonempty := by
        by_contra he
        have hsub := sdiff_eq_empty_iff_subset.mp (not_nonempty_iff_eq_empty.mp he)
        exact hDE (eq_of_subset_of_card_le hsub (by omega))
      obtain ⟨u,hu⟩ := hdiff
      obtain ⟨huD,huE⟩ := mem_sdiff.mp hu
      have hother : (E \ D).Nonempty := by
        rw [← card_pos]
        have he := card_sdiff_comm (show D.card = E.card by omega)
        have hp : 0<(D \ E).card := card_pos.mpr ⟨u,hu⟩
        omega
      obtain ⟨v,hv⟩ := hother
      obtain ⟨hvE,hvD⟩ := mem_sdiff.mp hv
      let D' := insert v (D.erase u)
      have hvErase : v ∉ D.erase u := fun h => hvD (mem_of_mem_erase h)
      have hD' : D'.card = 4 := by
        simp only [D',card_insert_of_notMem hvErase,card_erase_of_mem huD,hD]
      have hD'C : D' ⊆ C := by
        intro w hw
        rcases mem_insert.mp hw with rfl | hw
        · exact hEC hvE
        · exact hDC (mem_of_mem_erase hw)
      have hdiff' : D' \ E = (D \ E).erase u := by
        ext w
        simp only [D',mem_sdiff,mem_insert,mem_erase]
        constructor
        · rintro ⟨hw,hwE⟩
          rcases hw with rfl | hw
          · exact False.elim (hwE hvE)
          · exact ⟨hw.1,hw.2,hwE⟩
        · rintro ⟨hwu,hwD,hwE⟩
          exact ⟨Or.inr ⟨hwu,hwD⟩,hwE⟩
      have hlt : (D' \ E).card < n := by
        rw [hdiff',card_erase_of_mem hu]
        have hp : 0<(D \ E).card := card_pos.mpr ⟨u,hu⟩
        omega
      have hstep : (cliqueGraph G).Reachable D D' := by
        apply reachable_of_shared_triangle hD hD'
          (fun x hx y hy hxy => hC (hDC hx) (hDC hy) hxy)
          (fun x hx y hy hxy => hC (hD'C hx) (hD'C hy) hxy)
          (T := D.erase u)
        · rw [card_erase_of_mem huD,hD]
        · exact erase_subset _ _
        · exact subset_insert _ _
      exact hstep.trans (ih _ hlt D' rfl hD' hD'C)

abbrev ComponentIndex (G : SimpleGraph V) := (cliqueGraph G).ConnectedComponent ⊕ Finset V

noncomputable instance componentIndexFintype (G : SimpleGraph V) :
    Fintype (ComponentIndex G) := by
  classical
  unfold ComponentIndex
  infer_instance

abbrev IncidentTetrahedron (G : SimpleGraph V) (C : Finset V) : Prop :=
  ∃ D : Finset V, D.card = 4 ∧ G.IsClique D ∧ C ⊆ D

abbrev ContainedTetrahedron (G : SimpleGraph V) (C : Finset V) : Prop :=
  ∃ D : Finset V, D.card = 4 ∧ G.IsClique D ∧ D ⊆ C

def classOf (G : SimpleGraph V) (C : Finset V) : ComponentIndex G := by
  classical
  exact if hC : C.card = 3 then
    if h : IncidentTetrahedron G C then
      Sum.inl ((cliqueGraph G).connectedComponentMk (Classical.choose h))
    else Sum.inr C
  else if h : ContainedTetrahedron G C then
    Sum.inl ((cliqueGraph G).connectedComponentMk (Classical.choose h))
  else Sum.inr C

theorem contained_of_clique {G : SimpleGraph V} {C : Finset V}
    (hC : 4 ≤ C.card) (hc : G.IsClique C) : ContainedTetrahedron G C := by
  obtain ⟨D,hDC,hD⟩ := exists_subset_card_eq hC
  exact ⟨D,hD,fun u hu v hv huv => hc (hDC hu) (hDC hv) huv,hDC⟩

theorem triangle_extends_in_clique {G : SimpleGraph V} {C T : Finset V}
    (hC : 4 ≤ C.card) (hc : G.IsClique C) (hT : T.card = 3) (hTC : T ⊆ C) :
    ∃ D : Finset V, D.card = 4 ∧ G.IsClique D ∧ T ⊆ D ∧ D ⊆ C := by
  have hdiff : (C \ T).Nonempty := by
    rw [← card_pos,card_sdiff_of_subset hTC,hT]
    omega
  obtain ⟨v,hv⟩ := hdiff
  obtain ⟨hvC,hvT⟩ := mem_sdiff.mp hv
  refine ⟨insert v T,by rw [card_insert_of_notMem hvT,hT],?_,subset_insert _ _,?_⟩
  · intro u hu w hw huw
    exact hc (insert_subset hvC hTC hu) (insert_subset hvC hTC hw) huw
  · exact insert_subset hvC hTC

theorem classOf_higher {G : SimpleGraph V} {C D : Finset V}
    (hC : 4 ≤ C.card) (hc : G.IsClique C) (hD : D.card = 4)
    (hDC : D ⊆ C) :
    classOf G C = Sum.inl ((cliqueGraph G).connectedComponentMk D) := by
  classical
  have he := contained_of_clique hC hc
  have hn : C.card ≠ 3 := by omega
  have hcomp : (cliqueGraph G).connectedComponentMk (Classical.choose he)=
      (cliqueGraph G).connectedComponentMk D := by
    apply SimpleGraph.ConnectedComponent.sound
    obtain ⟨hd,hcl,hsub⟩ := Classical.choose_spec he
    exact tetrahedra_in_clique_reachable hc hd hD hsub hDC
  unfold classOf
  rw [dite_eq_right hn, dite_eq_left he]
  exact congrArg Sum.inl hcomp

theorem classOf_triangle {G : SimpleGraph V} {T D : Finset V}
    (hT : T.card = 3) (hD : D.card = 4) (hcD : G.IsClique D) (hTD : T ⊆ D) :
    classOf G T = Sum.inl ((cliqueGraph G).connectedComponentMk D) := by
  classical
  have he : IncidentTetrahedron G T := ⟨D,hD,hcD,hTD⟩
  have hcomp : (cliqueGraph G).connectedComponentMk (Classical.choose he)=
      (cliqueGraph G).connectedComponentMk D := by
    apply SimpleGraph.ConnectedComponent.sound
    obtain ⟨hd,hc,hsub⟩ := Classical.choose_spec he
    exact reachable_of_shared_triangle hd hD hc hcD hT hsub hTD
  unfold classOf
  rw [dite_eq_left hT, dite_eq_left he]
  exact congrArg Sum.inl hcomp

theorem classOf_compatible {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y) : PositiveDecomposition.ClassCompatible y (classOf G) := by
  intro C hC hyC T hT hTC
  have hc : G.IsClique C := by
    intro u hu v hv huv
    by_contra hn
    exact hyC (hy.2.2 C u v hu hv huv hn)
  obtain ⟨D,hD,hcD,hTD,hDC⟩ := triangle_extends_in_clique hC hc hT hTC
  rw [classOf_triangle hT hD hcD hTD,classOf_higher hC hc hD hDC]

def componentFamily (G : SimpleGraph V) (a : (cliqueGraph G).ConnectedComponent) :
    Finset (Finset V) := by
  classical
  exact univ.filter (fun C => C.card = 4 ∧ G.IsClique C ∧
    (cliqueGraph G).connectedComponentMk C = a)

def componentVertices (G : SimpleGraph V) (a : (cliqueGraph G).ConnectedComponent) :
    Finset V := (componentFamily G a).biUnion id

theorem mem_componentFamily {G : SimpleGraph V} {a : (cliqueGraph G).ConnectedComponent}
    {C : Finset V} : C ∈ componentFamily G a ↔
      C.card = 4 ∧ G.IsClique C ∧ (cliqueGraph G).connectedComponentMk C = a := by
  classical
  simp [componentFamily]

theorem higher_subset_component {G : SimpleGraph V} {C : Finset V}
    (hC : 4 ≤ C.card) (hc : G.IsClique C)
    {a : (cliqueGraph G).ConnectedComponent} (ha : classOf G C = Sum.inl a) :
    C ⊆ componentVertices G a := by
  classical
  obtain ⟨D,hD,hcD,hDC⟩ := contained_of_clique hC hc
  have hDa : (cliqueGraph G).connectedComponentMk D = a := by
    rw [classOf_higher hC hc hD hDC] at ha
    exact Sum.inl.inj ha
  intro v hv
  by_cases hvD : v ∈ D
  · exact mem_biUnion.mpr ⟨D,mem_componentFamily.mpr ⟨hD,hcD,hDa⟩,hvD⟩
  · have hne : D.Nonempty := card_pos.mp (by omega)
    obtain ⟨u,hu⟩ := hne
    let E := insert v (D.erase u)
    have hvE : v ∉ D.erase u := fun h => hvD (mem_of_mem_erase h)
    have hE : E.card = 4 := by
      simp only [E,card_insert_of_notMem hvE,card_erase_of_mem hu,hD]
    have hEC : E ⊆ C := insert_subset hv ((erase_subset _ _).trans hDC)
    have hcE : G.IsClique E := fun x hx y hy hxy => hc (hEC hx) (hEC hy) hxy
    have hEa : (cliqueGraph G).connectedComponentMk E = a :=
      (SimpleGraph.ConnectedComponent.sound
        (tetrahedra_in_clique_reachable hc hE hD hEC hDC)).trans hDa
    exact mem_biUnion.mpr ⟨E,mem_componentFamily.mpr ⟨hE,hcE,hEa⟩,mem_insert_self _ _⟩

theorem triangle_subset_component {G : SimpleGraph V} {T : Finset V} (hT : T.card = 3)
    {a : (cliqueGraph G).ConnectedComponent} (ha : classOf G T = Sum.inl a) :
    T ⊆ componentVertices G a := by
  classical
  by_cases hi : IncidentTetrahedron G T
  · obtain ⟨D,hD,hcD,hTD⟩ := hi
    have he := classOf_triangle hT hD hcD hTD
    rw [he] at ha
    intro v hv
    exact mem_biUnion.mpr ⟨D,mem_componentFamily.mpr ⟨hD,hcD,Sum.inl.inj ha⟩,hTD hv⟩
  · simp [classOf,hT,hi] at ha

theorem right_class_is_triangle {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y) {C T : Finset V} (hC : 3 ≤ C.card) (hyC : y C ≠ 0)
    (ha : classOf G C = Sum.inr T) : C.card = 3 ∧ C = T := by
  classical
  have hc : G.IsClique C := by
    intro u hu v hv huv
    by_contra hn
    exact hyC (hy.2.2 C u v hu hv huv hn)
  by_cases h3 : C.card = 3
  · refine ⟨h3,?_⟩
    by_cases hi : IncidentTetrahedron G C
    · simp [classOf,h3,hi] at ha
    · have hclass : classOf G C=Sum.inr C := by
        simp only [classOf, dite_eq_left h3, dite_eq_right hi]
      exact Sum.inr.inj (hclass.symm.trans ha)
  · have h4 : 4 ≤ C.card := by omega
    obtain ⟨D,hD,hcD,hDC⟩ := contained_of_clique h4 hc
    rw [classOf_higher h4 hc hD hDC] at ha
    cases ha

theorem componentFamily_preconnected (G : SimpleGraph V)
    (a : (cliqueGraph G).ConnectedComponent) :
    (tetrahedronGraph (componentFamily G a)).Preconnected := by
  classical
  intro C D
  have hC := mem_componentFamily.mp C.2
  have hD := mem_componentFamily.mp D.2
  have hr : (cliqueGraph G).Reachable C.1 D.1 :=
    SimpleGraph.ConnectedComponent.exact (hC.2.2.trans hD.2.2.symm)
  rw [SimpleGraph.reachable_eq_reflTransGen] at hr
  have hpath : ∀ E, Relation.ReflTransGen (cliqueGraph G).Adj C.1 E →
      ∃ hE : E ∈ componentFamily G a,
        (tetrahedronGraph (componentFamily G a)).Reachable C ⟨E,hE⟩ := by
    intro E hp
    induction hp with
    | refl => exact ⟨C.2,SimpleGraph.Reachable.rfl⟩
    | @tail E F hp hEF ih =>
      obtain ⟨hE,hreach⟩ := ih
      have hcE := mem_componentFamily.mp hE
      have hF : F ∈ componentFamily G a := mem_componentFamily.mpr
        ⟨hEF.2.1,hEF.2.2.2.1,
          (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hEF).symm.trans hcE.2.2⟩
      refine ⟨hF,hreach.trans (SimpleGraph.Adj.reachable ?_)⟩
      exact ⟨fun he => hEF.2.2.2.2.1 (congrArg Subtype.val he),hEF.2.2.2.2.2⟩
  obtain ⟨hD',hreach⟩ := hpath _ hr
  exact hreach

end TriangleComponents
end GraphicalZonotopes

end
end
end BundlePart47

section BundlePart48
/- Source: Papers/GraphicalZonotopes/ThreeTreeIncidence.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def triangles (G : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact univ.filter (fun T => T.card=3 ∧ G.IsClique T)

theorem mem_triangles {G : SimpleGraph V} {T : Finset V} :
    T∈triangles G ↔ T.card=3 ∧ G.IsClique T := by
  classical
  simp [triangles]

/-- Every triangle of an ordinary 3-tree lies in an actual tetrahedron;
the statement includes triangles created at the last attachment. -/
theorem ThreeTreeOn.triangle_extends {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {T : Finset V} (hT : T.card=3) (hcT : G.IsClique T) :
    ∃ C∈tetrahedra G,T⊆C := by
  classical
  induction h generalizing T with
  | tetrahedron C hC =>
    refine ⟨C,?_,?_⟩
    · rw [tetrahedra_cliqueGraph hC]
      exact mem_singleton_self _
    · exact (ThreeTreeOn.tetrahedron C hC).clique_subset_active (by omega) hcT
  | @attach S G h u hu A hA hAS hcA ih =>
    rw [tetrahedra_after_attachment h hu hA hAS hcA]
    by_cases huT : u∈T
    · refine ⟨insert u A,mem_insert_self _ _,?_⟩
      intro v hv
      by_cases hvu : v=u
      · exact mem_insert.mpr (Or.inl hvu)
      · exact mem_insert.mpr (Or.inr
          ((attached_vertex_adj_iff h hu hAS v).mp (hcT huT hv (Ne.symm hvu))))
    · obtain ⟨C,hC,hTC⟩ := ih hT (clique_before_attachment huT hcT)
      exact ⟨C,mem_insert_of_mem hC,hTC⟩

theorem ThreeTreeOn.tetrahedra_nonempty {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : (tetrahedra G).Nonempty := by
  classical
  induction h with
  | tetrahedron C hC => rw [tetrahedra_cliqueGraph hC]; exact singleton_nonempty _
  | @attach S G h u hu T hT hTS hcT ih =>
    rw [tetrahedra_after_attachment h hu hT hTS hcT]
    exact insert_nonempty _ _

theorem tetrahedronAdjacency_mono {G H : SimpleGraph V} (h : G≤ H) :
    TriangleComponents.cliqueGraph G≤ TriangleComponents.cliqueGraph H := by
  intro C D hCD
  exact ⟨hCD.1,hCD.2.1,
    fun u hu v hv huv => h (hCD.2.2.1 hu hv huv),
    fun u hu v hv huv => h (hCD.2.2.2.1 hu hv huv),hCD.2.2.2.2⟩

/-- All actual tetrahedra of a 3-tree are joined by shared triangles. This
is a statement about the graph itself, independent of a chosen coefficient
vector or an extreme-ray assumption. -/
theorem ThreeTreeOn.tetrahedra_reachable {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {C D : Finset V}
    (hC : C∈tetrahedra G) (hD : D∈tetrahedra G) :
    (TriangleComponents.cliqueGraph G).Reachable C D := by
  classical
  induction h generalizing C D with
  | tetrahedron A hA =>
    rw [tetrahedra_cliqueGraph hA,mem_singleton] at hC hD
    subst C
    subst D
    exact SimpleGraph.Reachable.rfl
  | @attach S G h u hu T hT hTS hcT ih =>
    have hm := tetrahedronAdjacency_mono
      (show G≤ G⊔attachmentStar u T from le_sup_left)
    obtain ⟨K,hK,hTK⟩ := h.triangle_extends hT hcT
    have hk := (mem_filter.mp hK).2
    have huT : u∉T := fun huT => hu (hTS huT)
    have hnew : (TriangleComponents.cliqueGraph (G⊔attachmentStar u T)).Reachable
        (insert u T) K :=
      TriangleComponents.reachable_of_shared_triangle
        (by rw [card_insert_of_notMem huT,hT]) hk.1
        (attached_tetrahedron_clique h hu hTS hcT)
        (fun a ha b hb hab => Or.inl (hk.2 ha hb hab)) hT (subset_insert _ _) hTK
    rw [tetrahedra_after_attachment h hu hT hTS hcT] at hC hD
    rcases mem_insert.mp hC with rfl | hC
    · rcases mem_insert.mp hD with rfl | hD
      · exact SimpleGraph.Reachable.rfl
      · exact hnew.trans (SimpleGraph.Reachable.mono hm (ih hK hD))
    · rcases mem_insert.mp hD with rfl | hD
      · exact (hnew.trans (SimpleGraph.Reachable.mono hm (ih hK hC))).symm
      · exact SimpleGraph.Reachable.mono hm (ih hC hD)

abbrev CliqueTriangleNode (G : SimpleGraph V) := ↥(tetrahedra G) ⊕ ↥(triangles G)

/-- The literal bipartite clique-triangle incidence graph used to root the
construction in Section 6. Its nodes are all tetrahedra and all triangles,
and its edges express containment. -/
def cliqueTriangleIncidence (G : SimpleGraph V) : SimpleGraph (CliqueTriangleNode G) where
  Adj x y := match x,y with
    | Sum.inl C,Sum.inr T => T.1⊆C.1
    | Sum.inr T,Sum.inl C => T.1⊆C.1
    | _,_ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> simp⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

instance (G : SimpleGraph V) : DecidableRel (cliqueTriangleIncidence G).Adj := by
  intro x y
  cases x <;> cases y <;> dsimp [cliqueTriangleIncidence] <;> infer_instance

/-- A shared triangle gives the actual length-two incidence path. -/
theorem incidence_reachable_of_shared_triangle {G : SimpleGraph V}
    (C D : ↥(tetrahedra G)) (hCD : (TriangleComponents.cliqueGraph G).Adj C.1 D.1) :
    (cliqueTriangleIncidence G).Reachable (Sum.inl C) (Sum.inl D) := by
  classical
  obtain ⟨T,hTsub,hTcard⟩ := exists_subset_card_eq hCD.2.2.2.2.2
  have hTC : T⊆C.1 := hTsub.trans inter_subset_left
  have hTD : T⊆D.1 := hTsub.trans inter_subset_right
  have hT : T∈triangles G := mem_triangles.mpr
    ⟨hTcard,fun u hu v hv huv => hCD.2.2.1 (hTC hu) (hTC hv) huv⟩
  exact (SimpleGraph.Adj.reachable
    (show (cliqueTriangleIncidence G).Adj (Sum.inl C) (Sum.inr ⟨T,hT⟩) from hTC)).trans
      (SimpleGraph.Adj.reachable
        (show (cliqueTriangleIncidence G).Adj (Sum.inr ⟨T,hT⟩) (Sum.inl D) from hTD))

theorem incidence_reachable_of_tetrahedron_reachable {G : SimpleGraph V}
    (C D : ↥(tetrahedra G))
    (hp : (TriangleComponents.cliqueGraph G).Reachable C.1 D.1) :
    (cliqueTriangleIncidence G).Reachable (Sum.inl C) (Sum.inl D) := by
  classical
  rw [SimpleGraph.reachable_eq_reflTransGen] at hp
  have hpath : ∀ E,Relation.ReflTransGen (TriangleComponents.cliqueGraph G).Adj C.1 E →
      ∃ hE : E∈tetrahedra G,
        (cliqueTriangleIncidence G).Reachable (Sum.inl C) (Sum.inl ⟨E,hE⟩) := by
    intro E hE
    induction hE with
    | refl => exact ⟨C.2,SimpleGraph.Reachable.rfl⟩
    | @tail E F hE hEF ih =>
      obtain ⟨hEmem,hreach⟩ := ih
      have hFmem : F∈tetrahedra G := mem_filter.mpr
        ⟨mem_univ _,hEF.2.1,hEF.2.2.2.1⟩
      exact ⟨hFmem,hreach.trans
        (incidence_reachable_of_shared_triangle ⟨E,hEmem⟩ ⟨F,hFmem⟩ hEF)⟩
  obtain ⟨hD,hreach⟩ := hpath _ hp
  exact hreach

theorem ThreeTreeOn.incidence_connected {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : (cliqueTriangleIncidence G).Connected := by
  classical
  obtain ⟨C,hC⟩ := h.tetrahedra_nonempty
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨Sum.inl ⟨C,hC⟩,?_⟩
  intro N
  cases N with
  | inl D =>
    exact incidence_reachable_of_tetrahedron_reachable ⟨C,hC⟩ D
      (h.tetrahedra_reachable hC D.2)
  | inr T =>
    have ht := mem_triangles.mp T.2
    obtain ⟨D,hD,hTD⟩ := h.triangle_extends ht.1 ht.2
    exact (incidence_reachable_of_tetrahedron_reachable ⟨C,hC⟩ ⟨D,hD⟩
      (h.tetrahedra_reachable hC hD)).trans
        (SimpleGraph.Adj.reachable
          (show (cliqueTriangleIncidence G).Adj (Sum.inl ⟨D,hD⟩) (Sum.inr T) from hTD))

end GraphicalZonotopes

end
end
end BundlePart48

section BundlePart49
/- Source: Papers/GraphicalZonotopes/ThreeTreeEmbedding.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace GraphicalZonotopes
open Finset
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem map_cliqueGraph (e : V ↪ W) (C : Finset V) :
    (cliqueGraph C).map e=cliqueGraph (C.map e) := by
  ext u v
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨a,b,⟨hab,ha,hb⟩,rfl,rfl⟩
    exact ⟨fun he => hab (e.injective he),mem_map.mpr ⟨a,ha,rfl⟩,mem_map.mpr ⟨b,hb,rfl⟩⟩
  · rintro ⟨huv,hu,hv⟩
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hu
    obtain ⟨b,hb,rfl⟩ := mem_map.mp hv
    exact ⟨a,b,⟨fun he => huv (congrArg e he),ha,hb⟩,rfl,rfl⟩

theorem map_attachmentStar (e : V ↪ W) (u : V) (T : Finset V) :
    (attachmentStar u T).map e=attachmentStar (e u) (T.map e) := by
  ext a b
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨v,w,⟨hvw,hstar⟩,rfl,rfl⟩
    refine ⟨fun he => hvw (e.injective he),?_⟩
    rcases hstar with ⟨rfl,hw⟩ | ⟨rfl,hv⟩
    · exact Or.inl ⟨rfl,mem_map.mpr ⟨w,hw,rfl⟩⟩
    · exact Or.inr ⟨rfl,mem_map.mpr ⟨v,hv,rfl⟩⟩
  · rintro ⟨hab,hstar⟩
    rcases hstar with ⟨rfl,hb⟩ | ⟨rfl,ha⟩
    · obtain ⟨w,hw,rfl⟩ := mem_map.mp hb
      exact ⟨u,w,⟨fun he => hab (congrArg e he),Or.inl ⟨rfl,hw⟩⟩,rfl,rfl⟩
    · obtain ⟨v,hv,rfl⟩ := mem_map.mp ha
      exact ⟨v,u,⟨fun he => hab (congrArg e he),Or.inr ⟨rfl,hv⟩⟩,rfl,rfl⟩

theorem map_sup_embedding (e : V ↪ W) (G H : SimpleGraph V) :
    (G⊔H).map e=G.map e⊔H.map e := by
  ext u v
  simp only [SimpleGraph.map_adj,SimpleGraph.sup_adj]
  aesop

theorem ThreeTreeOn.map {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (e : V ↪ W) : ThreeTreeOn (S.map e) (G.map e) := by
  induction h with
  | tetrahedron C hC =>
    rw [map_cliqueGraph]
    exact ThreeTreeOn.tetrahedron _ (by simpa only [card_map] using hC)
  | @attach S G h u hu T hT hTS hcl ih =>
    rw [map_insert,map_sup_embedding,map_attachmentStar]
    exact ThreeTreeOn.attach ih (e u) (by simpa using hu) (T.map e)
      (by simpa only [card_map] using hT) (map_subset_map.mpr hTS) hcl.finsetMap

namespace SetFunctionEmbedding

theorem map_pullSet_of_subset (e : V ↪ W) (S : Finset W)
    (hS : ∀ v∈S,v∈Set.range e) : (pullSet e S).map e=S := by
  ext v
  constructor
  · rintro hv
    obtain ⟨w,hw,rfl⟩ := mem_map.mp hv
    exact (mem_pullSet e S w).mp hw
  · intro hv
    obtain ⟨w,rfl⟩ := hS v hv
    exact mem_map.mpr ⟨w,(mem_pullSet e S w).mpr hv,rfl⟩

theorem card_pullSet_of_subset (e : V ↪ W) (S : Finset W)
    (hS : ∀ v∈S,v∈Set.range e) : (pullSet e S).card=S.card := by
  rw [← card_map e, map_pullSet_of_subset e S hS]

end SetFunctionEmbedding

theorem comap_cliqueGraph (e : V ↪ W) (C : Finset W) :
    (cliqueGraph C).comap e=cliqueGraph (SetFunctionEmbedding.pullSet e C) := by
  ext u v
  change (e u≠ e v ∧ e u∈C ∧ e v∈C) ↔
    (u≠ v ∧ u∈SetFunctionEmbedding.pullSet e C ∧ v∈SetFunctionEmbedding.pullSet e C)
  simp [e.injective.eq_iff]

theorem comap_attachmentStar (e : V ↪ W) (u : V) (T : Finset W) :
    (attachmentStar (e u) T).comap e=
      attachmentStar u (SetFunctionEmbedding.pullSet e T) := by
  ext a b
  change (e a≠ e b ∧ ((e a=e u ∧ e b∈T) ∨ (e b=e u ∧ e a∈T))) ↔ _
  simp [attachmentStar,SetFunctionEmbedding.mem_pullSet,e.injective.eq_iff]

theorem ThreeTreeOn.comap {S : Finset W} {G : SimpleGraph W}
    (h : ThreeTreeOn S G) (e : V ↪ W) (hS : ∀ v∈S,v∈Set.range e) :
    ThreeTreeOn (SetFunctionEmbedding.pullSet e S) (G.comap e) := by
  induction h with
  | tetrahedron C hC =>
    rw [comap_cliqueGraph]
    exact ThreeTreeOn.tetrahedron _
      ((SetFunctionEmbedding.card_pullSet_of_subset e C hS).trans hC)
  | @attach S G h u hu T hT hTS hcl ih =>
    have hS' : ∀ v∈S,v∈Set.range e := fun v hv => hS v (mem_insert_of_mem hv)
    have hT' : ∀ v∈T,v∈Set.range e := fun v hv => hS' v (hTS hv)
    obtain ⟨w,hw⟩ := hS u (mem_insert_self _ _)
    subst u
    rw [SetFunctionEmbedding.pullSet_insert_image]
    have hsup : (G⊔attachmentStar (e w) T).comap e=
        G.comap e⊔(attachmentStar (e w) T).comap e := rfl
    rw [hsup,comap_attachmentStar]
    apply ThreeTreeOn.attach (ih hS') w (by simpa using hu)
      (SetFunctionEmbedding.pullSet e T)
      ((SetFunctionEmbedding.card_pullSet_of_subset e T hT').trans hT)
    · intro v hv
      exact (SetFunctionEmbedding.mem_pullSet e S v).mpr
        (hTS ((SetFunctionEmbedding.mem_pullSet e T v).mp hv))
    · intro a ha b hb hab
      exact hcl ((SetFunctionEmbedding.mem_pullSet e T a).mp ha)
        ((SetFunctionEmbedding.mem_pullSet e T b).mp hb) (fun he => hab (e.injective he))

theorem ThreeTreeOn.induce {S : Finset V} {G : SimpleGraph V}
    [DecidableEq S] (h : ThreeTreeOn S G) : IsThreeTree (G.induce (S : Set V)) := by
  let e : S ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have hh := h.comap e (fun v hv => ⟨⟨v,hv⟩,rfl⟩)
  have hset : SetFunctionEmbedding.pullSet e S=univ := by
    ext v
    simp [SetFunctionEmbedding.mem_pullSet,e,v.property]
  rw [hset] at hh
  exact hh

theorem ThreeTreeOn.reachable_active {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : ∀ u∈S,∀ v∈S,G.Reachable u v := by
  induction h with
  | tetrahedron C hC =>
    intro u hu v hv
    by_cases huv : u=v
    · subst v; exact SimpleGraph.Reachable.rfl
    · exact SimpleGraph.Adj.reachable ⟨huv,hu,hv⟩
  | @attach S G h w hw T hT hTS hcl ih =>
    obtain ⟨a,ha⟩ := card_pos.mp (show 0< T.card by omega)
    have hwa : (G⊔attachmentStar w T).Reachable w a :=
      SimpleGraph.Adj.reachable ((attached_vertex_adj_iff h hw hTS a).mpr ha)
    intro u hu v hv
    rcases mem_insert.mp hu with hue | huS
    · subst u
      rcases mem_insert.mp hv with hve | hvS
      · subst v; exact SimpleGraph.Reachable.rfl
      · exact hwa.trans ((ih a (hTS ha) v hvS).mono le_sup_left)
    · rcases mem_insert.mp hv with hve | hvS
      · subst v
        exact ((ih u huS a (hTS ha)).mono le_sup_left).trans hwa.symm
      · exact (ih u huS v hvS).mono le_sup_left

theorem IsThreeTree.connected {G : SimpleGraph V} (h : IsThreeTree G) : G.Connected := by
  obtain ⟨v,hv⟩ := card_pos.mp (show 0<(univ : Finset V).card from lt_of_lt_of_le (by norm_num) h.active_card_ge_four)
  letI : Nonempty V := ⟨v⟩
  exact ⟨fun u v => h.reachable_active u (mem_univ _) v (mem_univ _)⟩

@[simp] theorem mem_tetrahedra_iff (G : SimpleGraph V) (C : Finset V) :
    C∈tetrahedra G ↔ C.card=4 ∧ G.IsClique C := by
  classical
  simp only [tetrahedra,mem_filter,mem_univ,true_and]

theorem tetrahedra_map (e : V ↪ W) (G : SimpleGraph V) :
    tetrahedra (G.map e)=(tetrahedra G).image (fun C => C.map e) := by
  classical
  ext D
  constructor
  · intro hD
    obtain ⟨hd,hcl⟩ := (mem_tetrahedra_iff (G.map e) D).mp hD
    obtain ⟨C,hC,rfl⟩ := (SimpleGraph.isClique_map_finset_iff_of_nontrivial
      (G := G) (f := e) (show D.Nontrivial from one_lt_card_iff_nontrivial.mp (by omega))).mp hcl
    refine mem_image.mpr ⟨C,(mem_tetrahedra_iff G C).mpr ⟨?_,hC⟩,rfl⟩
    simpa only [card_map] using hd
  · intro hD
    obtain ⟨C,hC,rfl⟩ := mem_image.mp hD
    obtain ⟨hc,hcl⟩ := (mem_tetrahedra_iff G C).mp hC
    exact (mem_tetrahedra_iff (G.map e) (C.map e)).mpr
      ⟨by simpa only [card_map] using hc,hcl.finsetMap⟩

theorem triangleMultiplicity_map (e : V ↪ W) (G : SimpleGraph V) (T : Finset V) :
    triangleMultiplicity (G.map e) (T.map e)=triangleMultiplicity G T := by
  have he : (tetrahedra (G.map e)).filter (fun C => T.map e⊆C)=
      ((tetrahedra G).filter (fun C => T⊆C)).image (fun C => C.map e) := by
    rw [tetrahedra_map]
    ext D
    simp only [mem_filter,mem_image]
    constructor
    · rintro ⟨⟨C,hC,rfl⟩,hTC⟩
      exact ⟨C,⟨hC,map_subset_map.mp hTC⟩,rfl⟩
    · rintro ⟨C,⟨hC,hTC⟩,rfl⟩
      exact ⟨⟨C,hC,rfl⟩,map_subset_map.mpr hTC⟩
  unfold triangleMultiplicity
  rw [he,card_image_of_injective _ (Finset.map_injective e)]

theorem Admissible.map {G : SimpleGraph V} (h : Admissible G) (e : V ↪ W) :
    Admissible (G.map e) := by
  intro T hT hcl
  obtain ⟨S,hS,rfl⟩ := (SimpleGraph.isClique_map_finset_iff_of_nontrivial
    (G := G) (f := e) (show T.Nontrivial from one_lt_card_iff_nontrivial.mp (by omega))).mp hcl
  rw [triangleMultiplicity_map]
  exact h S (by simpa only [card_map] using hT) hS

theorem Admissible.of_map {G : SimpleGraph V} (e : V ↪ W)
    (h : Admissible (G.map e)) : Admissible G := by
  intro T hT hcl
  have hh := h (T.map e) (by simpa only [card_map] using hT) hcl.finsetMap
  rwa [triangleMultiplicity_map] at hh

theorem IsThreeTree.map_equiv {G : SimpleGraph V} (h : IsThreeTree G) (e : V ≃ W) :
    IsThreeTree (G.map e.toEmbedding) := by
  have hh := h.map e.toEmbedding
  change ThreeTreeOn univ _
  simpa only [Finset.map_univ_equiv] using hh

theorem HasAdmissibleSpanningThreeTree.map_equiv {G : SimpleGraph V}
    (h : HasAdmissibleSpanningThreeTree G) (e : V ≃ W) :
    HasAdmissibleSpanningThreeTree (G.map e.toEmbedding) := by
  obtain ⟨H,hHG,hT,hA⟩ := h
  exact ⟨H.map e.toEmbedding,SimpleGraph.map_monotone e hHG,
    hT.map_equiv e,hA.map e.toEmbedding⟩

theorem ThreeTreeOn.exists_edge {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : ∃ u v,G.Adj u v := by
  obtain ⟨C,hC⟩ := h.tetrahedra_nonempty
  obtain ⟨hc,hcl⟩ := (mem_filter.mp hC).2
  obtain ⟨u,hu⟩ := card_pos.mp (show 0< C.card by omega)
  obtain ⟨v,hv,hvu⟩ := exists_mem_ne (show 1< C.card by omega) u
  exact ⟨u,v,hcl hu hv (Ne.symm hvu)⟩

theorem map_comap_of_supported (e : V ↪ W) (G : SimpleGraph W)
    (hs : ∀ u v,G.Adj u v → u∈Set.range e) : (G.comap e).map e=G := by
  ext u v
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨a,b,hab,rfl,rfl⟩
    exact hab
  · intro huv
    obtain ⟨a,rfl⟩ := hs u v huv
    obtain ⟨b,rfl⟩ := hs v (e a) (G.adj_symm huv)
    exact ⟨a,b,huv,rfl,rfl⟩

end GraphicalZonotopes

end
end
end BundlePart49

section BundlePart50
/- Source: Papers/GraphicalZonotopes/SupportGeometry.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
section Unordered
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Dependence on a displayed set of coordinates is an equality of the
original set function, not an informal support convention. -/
def DependsOn (z : SetFunction V) (S : Finset V) : Prop :=
  ∀ T, z T = z (T ∩ S)

theorem DependsOn.add {f g : SetFunction V} {S : Finset V}
    (hf : DependsOn f S) (hg : DependsOn g S) : DependsOn (f+g) S := by
  intro T
  change f T+g T=f (T∩S)+g (T∩S)
  rw [hf T,hg T]

theorem DependsOn.of_smul {z : SetFunction V} {S : Finset V} {a : ℝ}
    (ha : a ≠ 0) (h : DependsOn (a • z) S) : DependsOn z S := by
  intro T
  exact mul_left_cancel₀ ha (h T)

theorem setMonomial_dependsOn (C : Finset V) : DependsOn (setMonomial C) C := by
  intro T
  simp [setMonomial,subset_inter_iff]

theorem DependsOn.smul {z : SetFunction V} {S : Finset V}
    (h : DependsOn z S) (a : ℝ) : DependsOn (a • z) S := by
  intro T
  change a*z T=a*z (T∩S)
  rw [h T]

theorem zeta_dependsOn {y : SetFunction V} {S : Finset V}
    (hy : ∀ C, ¬ C ⊆ S → y C = 0) : DependsOn (zeta y) S := by
  intro T
  rw [zeta_eq_sum_monomials]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply sum_congr rfl
  intro C hC
  by_cases hCS : C ⊆ S
  · simp [setMonomial,subset_inter_iff,hCS]
  · simp [hy C hCS]

theorem DependsOn.delta_eq_zero {z : SetFunction V} {S : Finset V}
    (h : DependsOn z S) {u v : V} (hu : u ∉ S) (T : Finset V) :
    delta z u v T = 0 := by
  have hi : ∀ A : Finset V, insert u A ∩ S = A ∩ S := by
    intro A
    ext x
    simp only [mem_inter,mem_insert]
    constructor
    · rintro ⟨hx,hxS⟩
      rcases hx with rfl | hx
      · exact False.elim (hu hxS)
      · exact ⟨hx,hxS⟩
    · rintro ⟨hx,hxS⟩
      exact ⟨Or.inr hx,hxS⟩
  unfold delta
  rw [h (insert u (insert v T)),h (insert u T),h (insert v T),h T,hi,hi]
  ring

theorem basePolytope_coordinate_zero_of_dependsOn {z : SetFunction V} {S : Finset V}
    (hn : TranslationNormalized z) (hd : DependsOn z S) {u : V} (hu : u ∉ S)
    {x : V → ℝ} (hx : x ∈ basePolytope z) : x u = 0 := by
  have hl : 0 ≤ x u := by simpa [hn.2 u,subsetSum] using hx.2 {u}
  have he : univ.erase u ∩ S = S := by
    ext v
    simp only [mem_inter,mem_erase,mem_univ,true_and,and_true]
    constructor
    · exact fun h => h.2
    · intro hv
      exact ⟨fun hvu => hu (hvu ▸ hv),hv⟩
  have hz : z (univ.erase u) = z univ := by
    rw [hd (univ.erase u),hd univ,he,univ_inter]
  have hh := hx.2 (univ.erase u)
  rw [hz] at hh
  have hsum : subsetSum x (univ.erase u)+x u=z univ := by
    rw [subsetSum,sum_erase_add _ _ (mem_univ u)]
    exact hx.1
  linarith

def evaluationLinear (u : V) : (V → ℝ) →ₗ[ℝ] ℝ where
  toFun x := x u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem vectorSpan_le_evaluation_ker_of_dependsOn {z : SetFunction V} {S : Finset V}
    (hn : TranslationNormalized z) (hs : Supermodular z) (hd : DependsOn z S)
    {u : V} (hu : u ∉ S) : vectorSpan ℝ (basePolytope z) ≤ (evaluationLinear u).ker := by
  obtain ⟨p,hp⟩ := basePolytope_nonempty hn.1 hs
  rw [vectorSpan_eq_span_vsub_set_right ℝ hp]
  apply Submodule.span_le.mpr
  rintro x ⟨q,hq,rfl⟩
  change q u-p u=0
  rw [basePolytope_coordinate_zero_of_dependsOn hn hd hu hq,
    basePolytope_coordinate_zero_of_dependsOn hn hd hu hp,sub_self]

/-- Full affine dimension forces every coordinate to be present in any set
on which the normalized function depends. -/
theorem fullDimension_dependsOn_eq_univ {n : ℕ} (hn : 2 ≤ n)
    {z : SetFunction (Fin n)} (hzn : TranslationNormalized z) (hzs : Supermodular z)
    (hfull : Module.finrank ℝ (vectorSpan ℝ (basePolytope z)) = n-1)
    {S : Finset (Fin n)} (hdep : DependsOn z S) : S = univ := by
  have hne := basePolytope_nonempty hzn.1 hzs
  have hW : vectorSpan ℝ (basePolytope z) = (totalLinear (V := Fin n)).ker :=
    Submodule.eq_of_le_of_finrank_eq (vectorSpan_basePolytope_le_total_ker hne)
      (hfull.trans (finrank_total_ker (by omega)).symm)
  apply eq_univ_of_forall
  intro u
  by_contra hu
  have hex : ∃ v : Fin n, v ≠ u := by
    by_cases hu0 : u = ⟨0,by omega⟩
    · refine ⟨⟨1,by omega⟩,?_⟩
      rw [hu0]
      intro h
      have hv := congrArg Fin.val h
      change (1 : ℕ)=0 at hv
      omega
    · exact ⟨⟨0,by omega⟩,Ne.symm hu0⟩
  obtain ⟨v,hvu⟩ := hex
  have hroot : basisVector u-basisVector v ∈ (totalLinear (V := Fin n)).ker := by
    change subsetSum (basisVector u-basisVector v) univ=0
    simp
  rw [← hW] at hroot
  have hzero := vectorSpan_le_evaluation_ker_of_dependsOn hzn hzs hdep hu hroot
  change (basisVector u-basisVector v) u=0 at hzero
  simp [basisVector,Pi.single_apply,hvu,Ne.symm hvu] at hzero

theorem TranslationNormalized.finset_sum {I : Type*} (s : Finset I)
    (f : I → SetFunction V) (hf : ∀ i ∈ s, TranslationNormalized (f i)) :
    TranslationNormalized (∑ i ∈ s, f i) := by
  constructor
  · change (∑ i ∈ s, f i) ∅=0
    rw [Finset.sum_apply]
    exact sum_eq_zero fun i hi => (hf i hi).1
  · intro v
    change (∑ i ∈ s, f i) {v}=0
    rw [Finset.sum_apply]
    exact sum_eq_zero fun i hi => (hf i hi).2 v

theorem TranslationNormalized.add {f g : SetFunction V}
    (hf : TranslationNormalized f) (hg : TranslationNormalized g) :
    TranslationNormalized (f+g) := by
  exact ⟨by change f ∅+g ∅=0; rw [hf.1,hg.1,add_zero],
    fun v => by change f {v}+g {v}=0; rw [hf.2 v,hg.2 v,add_zero]⟩

/-- Every nonzero member of an arbitrary finite positive decomposition of an
extreme normalized function is a strictly positive multiple of it. -/
theorem ExtremeSupermodular.finite_summand {I : Type*} [Fintype I]
    {z : SetFunction V} (hz : ExtremeSupermodular z) (f : I → SetFunction V)
    (hn : ∀ i, TranslationNormalized (f i)) (hs : ∀ i, Supermodular (f i))
    (he : ∑ i, f i=z) {i : I} (hi : f i ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ f i=a • z := by
  classical
  let g := ∑ j ∈ univ.erase i, f j
  have hgn : TranslationNormalized g := TranslationNormalized.finset_sum _ _ (fun j hj => hn j)
  have hgs : Supermodular g := Supermodular.finset_sum _ _ (fun j hj => hs j)
  have hsum : f i+g=z := by
    rw [add_comm,show g=∑ j ∈ univ.erase i,f j from rfl,
      sum_erase_add _ _ (mem_univ i),he]
  obtain ⟨a,ha,hf⟩ := hz.2.2.2 (f i) g (hn i) hgn (hs i) hgs hsum
  refine ⟨a,lt_of_le_of_ne ha ?_,hf⟩
  intro hzero
  exact hi (by simpa [← hzero] using hf)

end Unordered

namespace PositiveDecomposition
variable {V : Type*} [Fintype V] [LinearOrder V]

theorem DependsOn.adjusted {z : SetFunction V} {S : Finset V}
    (h : GraphicalZonotopes.DependsOn z S) : GraphicalZonotopes.DependsOn (adjusted z) S := by
  apply h.add
  apply zeta_dependsOn
  intro C hC
  by_cases hcard : C.card = 2
  · obtain ⟨u,v,huv,rfl⟩ := card_eq_two.mp hcard
    rw [allocation_pair z huv]
    have hzero : minimumSlack z u v=0 := by
      by_cases hu : u ∈ S
      · have hv : v ∉ S := fun hv => hC (insert_subset hu (singleton_subset_iff.mpr hv))
        have hz : ∀ T, u ∉ T → v ∉ T → delta z u v T=0 := by
          intro T _ _
          have hcomm : delta z u v T=delta z v u T := by
            unfold delta
            rw [insert_comm]
            ring
          rw [hcomm]
          exact h.delta_eq_zero hv T
        obtain ⟨T,hTu,hTv,hmin⟩ := exists_minimumSlack z u v
        exact hmin.symm.trans (hz T hTu hTv)
      · obtain ⟨T,hTu,hTv,hmin⟩ := exists_minimumSlack z u v
        exact hmin.symm.trans (h.delta_eq_zero hu T)
    simp [hzero]
  · exact allocation_zero z hcard

end PositiveDecomposition
end GraphicalZonotopes

end
end
end BundlePart50

section BundlePart51
/- Source: Papers/GraphicalZonotopes/SetFunctionEmbeddingGeometry.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace GraphicalZonotopes.SetFunctionEmbedding
open Finset
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

@[simp] theorem pullSet_univ (e : W ↪ V) : pullSet e univ=univ := by
  ext w; simp

theorem reconstruct_of_insert_absent (e : W ↪ V) (f : SetFunction V)
    (hf : ∀ v,v∉Set.range e → ∀ S,f (insert v S)=f S) :
    extend e (restrict e f)=f := by
  have hall : ∀ S : Finset V,∀ f : SetFunction V,
      (∀ v,v∉Set.range e → ∀ T,f (insert v T)=f T) →
      f S=f ((pullSet e S).map e) := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro f hf; simp
    | @insert v S hv ih =>
      intro f hf
      by_cases hvR : v∈Set.range e
      · obtain ⟨w,rfl⟩ := hvR
        let g : SetFunction V := fun T => f (insert (e w) T)
        have hg : ∀ v,v∉Set.range e → ∀ T,g (insert v T)=g T := by
          intro v hv T
          dsimp only [g]
          rw [insert_comm,hf v hv]
        simpa only [g,pullSet_insert_image,map_insert] using ih g hg
      · rw [hf v hvR,pullSet_insert_not_range e v hvR]
        exact ih f hf
  funext S
  exact (hall S f hf).symm

theorem insert_absent_of_zero_deltas {f : SetFunction V}
    (hn : TranslationNormalized f) (u : V)
    (hz : ∀ v,u≠ v → ∀ S,u∉S → v∉S → delta f u v S=0) :
    ∀ S,f (insert u S)=f S := by
  intro S
  induction S using Finset.induction_on with
  | empty => change f {u}=f ∅; rw [hn.2 u,hn.1]
  | @insert v S hv ih =>
    by_cases huv : u=v
    · subst v; simp
    · by_cases huS : u∈S
      · simp [insert_eq_of_mem huS,insert_eq_of_mem (mem_insert_of_mem huS)]
      · have hh := hz v huv S huS hv
        dsimp only [delta] at hh
        rw [ih] at hh
        linarith

/-- Adding unused coordinates preserves actual extremality in the full
supermodular cone. Summands are proved to ignore every new coordinate. -/
theorem extend_extreme (e : W ↪ V) {f : SetFunction W}
    (hf : ExtremeSupermodular f) : ExtremeSupermodular (extend e f) := by
  refine ⟨extend_translationNormalized e hf.1,extend_supermodular e hf.2.1,?_,?_⟩
  · intro he
    apply hf.2.2.1
    funext S
    have hh := congrFun he (S.map e)
    simpa only [extend,pullSet_map,Pi.zero_apply] using hh
  · intro g h hgn hhn hgs hhs hsum
    have hgzero : ∀ u,u∉Set.range e → ∀ v,u≠ v → ∀ S,u∉S → v∉S →
        delta g u v S=0 := by
      intro u hu v huv S huS hvS
      have h1 := hgs.elemental u v huv S huS hvS
      have h2 := hhs.elemental u v huv S huS hvS
      have he : delta g u v S+delta h u v S=0 := by
        rw [← delta_add,hsum,delta_extend_not_range e f u v hu]
      linarith
    have hgrec : extend e (restrict e g)=g :=
      reconstruct_of_insert_absent e g (fun u hu =>
        insert_absent_of_zero_deltas hgn u (hgzero u hu))
    have hsum' : restrict e g+restrict e h=f := by
      funext S
      have he := congrFun hsum (S.map e)
      simpa only [restrict,extend,pullSet_map,Pi.add_apply] using he
    obtain ⟨a,ha,hscale⟩ := hf.2.2.2 (restrict e g) (restrict e h)
      (restrict_translationNormalized e hgn) (restrict_translationNormalized e hhn)
      (restrict_supermodular e hgs) (restrict_supermodular e hhs) hsum'
    refine ⟨a,ha,?_⟩
    rw [← hgrec,hscale,extend_smul]

theorem extend_integer (e : W ↪ V) {f : SetFunction W}
    (hf : IntegerValued f) : IntegerValued (extend e f) := fun S => hf (pullSet e S)

theorem extend_dependsOn (e : W ↪ V) (f : SetFunction W) :
    DependsOn (extend e f) (univ.map e) := by
  intro S
  change f (pullSet e S)=f (pullSet e (S∩univ.map e))
  congr 1
  ext w
  simp

/-- The literal linear embedding extends vectors by zero outside the image. -/
def pushVector (e : W ↪ V) : (W → ℝ) →ₗ[ℝ] (V → ℝ) :=
  Fintype.linearCombination ℝ (fun w => basisVector (e w))

@[simp] theorem pushVector_image (e : W ↪ V) (x : W → ℝ) (w : W) :
    pushVector e x (e w)=x w := by
  simp [pushVector,Fintype.linearCombination_apply,basisVector,Pi.single_apply,
    e.injective.eq_iff]

theorem pushVector_outside (e : W ↪ V) (x : W → ℝ) (v : V)
    (hv : v∉Set.range e) : pushVector e x v=0 := by
  have hne : ∀ w,e w≠ v := fun w he => hv ⟨w,he⟩
  simp [pushVector,Fintype.linearCombination_apply,basisVector,Pi.single_apply,
    hne,fun w => Ne.symm (hne w)]

theorem pushVector_injective (e : W ↪ V) : Function.Injective (pushVector e) := by
  intro x y he
  funext w
  have hh := congrFun he (e w)
  simpa only [pushVector_image] using hh

theorem subsetSum_pushVector (e : W ↪ V) (x : W → ℝ) (S : Finset V) :
    subsetSum (pushVector e x) S=subsetSum x (pullSet e S) := by
  change subsetSum (∑ w,x w • basisVector (e w)) S=_
  unfold subsetSum
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [sum_comm]
  simp_rw [← mul_sum]
  change (∑ w,x w*subsetSum (basisVector (e w)) S)=_
  simp only [subsetSum_basisVector]
  simp [subsetSum,pullSet,sum_filter]

/-- The extended base polytope is exactly the zero-coordinate linear image
of the original body, including every point and every defining inequality. -/
theorem basePolytope_extend (e : W ↪ V) {f : SetFunction W}
    (hn : TranslationNormalized f) :
    basePolytope (extend e f)=pushVector e '' basePolytope f := by
  ext x
  constructor
  · intro hx
    let p : W → ℝ := fun w => x (e w)
    have hzero : ∀ v,v∉Set.range e → x v=0 := by
      intro v hv
      apply basePolytope_coordinate_zero_of_dependsOn
        (extend_translationNormalized e hn) (extend_dependsOn e f) (x := x) _ hx
      intro hm
      obtain ⟨w,_,he⟩ := mem_map.mp hm
      exact hv ⟨w,he⟩
    have hpush : pushVector e p=x := by
      funext v
      by_cases hv : v∈Set.range e
      · obtain ⟨w,rfl⟩ := hv
        exact pushVector_image e p w
      · rw [pushVector_outside e p v hv,hzero v hv]
    refine ⟨p,?_,hpush⟩
    constructor
    · have ht := hx.1
      rw [← hpush,subsetSum_pushVector,pullSet_univ] at ht
      simpa only [extend,pullSet_univ] using ht
    · intro T
      have ht := hx.2 (T.map e)
      rw [← hpush,subsetSum_pushVector,pullSet_map] at ht
      simpa only [extend,pullSet_map] using ht
  · rintro ⟨p,hp,rfl⟩
    constructor
    · rw [subsetSum_pushVector,pullSet_univ]
      simpa only [extend,pullSet_univ] using hp.1
    · intro S
      rw [subsetSum_pushVector]
      exact hp.2 (pullSet e S)

/-- Affine dimension is unchanged by an injective extension of the vertex
index set. This is a statement about the genuine base polytopes. -/
theorem finrank_vectorSpan_extend (e : W ↪ V) {f : SetFunction W}
    (hn : TranslationNormalized f) :
    Module.finrank ℝ (vectorSpan ℝ (basePolytope (extend e f)))=
      Module.finrank ℝ (vectorSpan ℝ (basePolytope f)) := by
  rw [basePolytope_extend e hn]
  have he := (pushVector e).toAffineMap.map_vectorSpan (s := basePolytope f)
  change Submodule.map (pushVector e) (vectorSpan ℝ (basePolytope f))=
    vectorSpan ℝ (pushVector e '' basePolytope f) at he
  rw [← he]
  exact (Submodule.equivMapOfInjective (pushVector e) (pushVector_injective e)
    (vectorSpan ℝ (basePolytope f))).finrank_eq.symm

end GraphicalZonotopes.SetFunctionEmbedding

end
end
end BundlePart51

section BundlePart52
/- Source: Papers/GraphicalZonotopes/RefinedTriangleComponents.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace RefinedTriangleComponents
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The actual nonzero four-coefficient family, with no ambient tetrahedron
inserted merely because its vertices form a clique. -/
def family (y : SetFunction V) : Finset (Finset V) := by
  classical
  exact univ.filter (fun C => C.card=4 ∧ y C≠0)

@[simp] theorem mem_family (y : SetFunction V) (C : Finset V) :
    C∈family y ↔ C.card=4 ∧ y C≠0 := by
  classical
  simp [family]

abbrev FamilyVertex (y : SetFunction V) := {C : Finset V // C∈family y}
abbrev Component (y : SetFunction V) := (tetrahedronGraph (family y)).ConnectedComponent
abbrev ClassIndex (y : SetFunction V) := Component y ⊕ Finset V

noncomputable instance classIndexFintype (y : SetFunction V) : Fintype (ClassIndex y) := by
  classical
  infer_instance

def Incident (y : SetFunction V) (T : Finset V) : Prop :=
  ∃ C : Finset V,C∈family y ∧ T⊆C

def classOf (y : SetFunction V) (C : Finset V) : ClassIndex y := by
  classical
  exact if h3 : C.card=3 then
    if h : Incident y C then
      Sum.inl ((tetrahedronGraph (family y)).connectedComponentMk
        ⟨Classical.choose h,(Classical.choose_spec h).1⟩)
    else Sum.inr C
  else if h : C∈family y then
    Sum.inl ((tetrahedronGraph (family y)).connectedComponentMk ⟨C,h⟩)
  else Sum.inr C

theorem family_reachable_of_triangle {y : SetFunction V}
    (C D : FamilyVertex y) {T : Finset V} (hT : T.card=3)
    (hTC : T⊆C.val) (hTD : T⊆D.val) :
    (tetrahedronGraph (family y)).Reachable C D := by
  by_cases he : C=D
  · subst D
    exact SimpleGraph.Reachable.rfl
  · apply SimpleGraph.Adj.reachable
    refine ⟨he,?_⟩
    have hcard := card_le_card (subset_inter hTC hTD)
    omega

theorem classOf_family {y : SetFunction V} {C : Finset V} (hC : C∈family y) :
    classOf y C=Sum.inl ((tetrahedronGraph (family y)).connectedComponentMk ⟨C,hC⟩) := by
  classical
  have hc := (mem_family y C).mp hC
  have h3 : C.card≠3 := by omega
  simp [classOf,h3,hC]

theorem classOf_triangle {y : SetFunction V} {T C : Finset V}
    (hT : T.card=3) (hC : C∈family y) (hTC : T⊆C) :
    classOf y T=Sum.inl ((tetrahedronGraph (family y)).connectedComponentMk ⟨C,hC⟩) := by
  classical
  have hI : Incident y T := ⟨C,hC,hTC⟩
  simp only [classOf,dif_pos hT,dif_pos hI]
  apply congrArg Sum.inl
  apply SimpleGraph.ConnectedComponent.sound
  exact family_reachable_of_triangle _ _ hT (Classical.choose_spec hI).2 hTC

theorem nonzero_card_le_four {G : SimpleGraph V} (hG : G.CliqueFree 5)
    {y : SetFunction V} (hy : CliqueSupported G y) {C : Finset V} (hC : y C≠0) :
    C.card≤4 := by
  by_contra hcard
  have h5 : 5≤ C.card := by omega
  obtain ⟨D,hDC,hD⟩ := exists_subset_card_eq h5
  apply hG D
  refine ⟨?_,hD⟩
  intro u hu v hv huv
  by_contra hnon
  exact hC (hy.2.2 C u v (hDC hu) (hDC hv) huv hnon)

/-- The refined partition has the exact compatibility needed by the positive
decomposition, because no nonzero coefficient has size greater than four. -/
theorem classOf_compatible {y : SetFunction V}
    (hdegree : ∀ C,y C≠0 → C.card≤4) :
    PositiveDecomposition.ClassCompatible y (classOf y) := by
  intro C hC hyC T hT hTC
  have hc : C.card=4 := le_antisymm (hdegree C hyC) hC
  have hmem : C∈family y := (mem_family y C).mpr ⟨hc,hyC⟩
  rw [classOf_triangle hT hmem hTC,classOf_family hmem]

theorem right_class_is_triangle {y : SetFunction V}
    (hdegree : ∀ C,y C≠0 → C.card≤4) {C T : Finset V}
    (hC : 3≤ C.card) (hyC : y C≠0) (ha : classOf y C=Sum.inr T) :
    C.card=3 ∧ C=T := by
  classical
  by_cases h3 : C.card=3
  · refine ⟨h3,?_⟩
    by_cases hi : Incident y C
    · simp [classOf,h3,hi] at ha
    · simpa [classOf,h3,hi] using ha
  · have h4 : C.card=4 := by have h:=hdegree C hyC; omega
    have hm : C∈family y := (mem_family y C).mpr ⟨h4,hyC⟩
    rw [classOf_family hm] at ha
    cases ha

theorem triangle_left_incident {y : SetFunction V} {T : Finset V} (hT : T.card=3)
    {a : Component y} (ha : classOf y T=Sum.inl a) : Incident y T := by
  classical
  by_contra hi
  simp [classOf,hT,hi] at ha

/-- The edge union of the actual nonzero four-coefficient family. -/
def edgeGraph (y : SetFunction V) : SimpleGraph V where
  Adj u v := u≠ v ∧ ∃ C∈family y,u∈C ∧ v∈C
  symm := ⟨by
    rintro u v ⟨huv,C,hC,hu,hv⟩
    exact ⟨Ne.symm huv,C,hC,hv,hu⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem family_subset_edgeGraph_clique {y : SetFunction V} {C : Finset V}
    (hC : C∈family y) : (edgeGraph y).IsClique C := by
  intro u hu v hv huv
  exact ⟨huv,C,hC,hu,hv⟩

theorem left_coefficients_supported {y : SetFunction V}
    (hdegree : ∀ C,y C≠0 → C.card≤4) (a : Component y) :
    CliqueSupported (edgeGraph y)
      (PositiveDecomposition.classCoefficients y (classOf y) (Sum.inl a)) := by
  classical
  refine ⟨by simp [PositiveDecomposition.classCoefficients],
    fun v => by simp [PositiveDecomposition.classCoefficients],?_⟩
  intro C u v hu hv huv hnon
  by_contra hz
  obtain ⟨hc,ha,hyC⟩ := PositiveDecomposition.classCoefficients_nonzero hz
  apply hnon
  refine ⟨huv,?_⟩
  by_cases h3 : C.card=3
  · obtain ⟨D,hD,hCD⟩ := triangle_left_incident h3 ha
    exact ⟨D,hD,hCD hu,hCD hv⟩
  · have h4 : C.card=4 := by have h:=hdegree C hyC; omega
    exact ⟨C,(mem_family y C).mpr ⟨h4,hyC⟩,hu,hv⟩

theorem left_coefficients_subset_vertices {y : SetFunction V}
    (hdegree : ∀ C,y C≠0 → C.card≤4) (a : Component y) {C : Finset V}
    (hC : PositiveDecomposition.classCoefficients y (classOf y) (Sum.inl a) C≠0) :
    C⊆(family y).biUnion id := by
  classical
  obtain ⟨hc,ha,hyC⟩ := PositiveDecomposition.classCoefficients_nonzero hC
  by_cases h3 : C.card=3
  · obtain ⟨D,hD,hCD⟩ := triangle_left_incident h3 ha
    intro v hv
    exact mem_biUnion.mpr ⟨D,hD,hCD hv⟩
  · have h4 : C.card=4 := by have h:=hdegree C hyC; omega
    intro v hv
    exact mem_biUnion.mpr ⟨C,(mem_family y C).mpr ⟨h4,hyC⟩,hv⟩

/-- If a nonzero refined positive piece is proportional to the whole
function, every nonzero four-coefficient lies in its one shared-face component. -/
theorem same_component_of_positive_piece {y : SetFunction V} (a : Component y)
    {t : ℝ} (ht : t≠0)
    (he : PositiveDecomposition.adjusted
      (PositiveDecomposition.higherClass y (classOf y) (Sum.inl a))=t • zeta y) :
    ∀ C : FamilyVertex y,
      (tetrahedronGraph (family y)).connectedComponentMk C=a := by
  intro C
  have hC := (mem_family y C.val).mp C.property
  have hcoef := congrArg (fun f : SetFunction V => mobius f C.val) he
  have hmin : PositiveDecomposition.allocation
      (PositiveDecomposition.higherClass y (classOf y) (Sum.inl a)) C.val=0 :=
    PositiveDecomposition.allocation_zero _ (by omega)
  have hleft : mobius (PositiveDecomposition.adjusted
      (PositiveDecomposition.higherClass y (classOf y) (Sum.inl a))) C.val=
      PositiveDecomposition.classCoefficients y (classOf y) (Sum.inl a) C.val := by
    unfold PositiveDecomposition.adjusted PositiveDecomposition.higherClass
    rw [show zeta (PositiveDecomposition.classCoefficients y (classOf y) (Sum.inl a))+
        zeta (PositiveDecomposition.allocation
          (zeta (PositiveDecomposition.classCoefficients y (classOf y) (Sum.inl a))))=
        zeta (PositiveDecomposition.classCoefficients y (classOf y) (Sum.inl a)+
          PositiveDecomposition.allocation
            (zeta (PositiveDecomposition.classCoefficients y (classOf y) (Sum.inl a)))) from
      (zetaLinear.map_add _ _).symm,mobius_zeta]
    change PositiveDecomposition.classCoefficients y (classOf y) (Sum.inl a) C.val +
      PositiveDecomposition.allocation
        (PositiveDecomposition.higherClass y (classOf y) (Sum.inl a)) C.val = _
    rw [hmin,add_zero]
  have hright : mobius (t • zeta y) C.val=t*y C.val := by
    have hmap := (zetaEquiv (V:=V)).symm.map_smul t (zeta y)
    have h := congrFun hmap C.val
    change mobius (t • zeta y) C.val=t*mobius (zeta y) C.val at h
    simpa only [mobius_zeta] using h
  rw [hleft,hright] at hcoef
  have hn : PositiveDecomposition.classCoefficients y (classOf y) (Sum.inl a) C.val≠0 := by
    rw [hcoef]
    exact mul_ne_zero ht hC.2
  have hclass := (PositiveDecomposition.classCoefficients_nonzero hn).2.1
  rw [classOf_family C.property] at hclass
  exact Sum.inl.inj hclass

end RefinedTriangleComponents
end GraphicalZonotopes

end
end
end BundlePart52

section BundlePart53
/- Source: Papers/GraphicalZonotopes/RefinedSupport.lean -/







@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace RefinedTriangleComponents
open Finset PositiveDecomposition
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [LinearOrder V]

private theorem adjusted_zero_function : adjusted (0 : SetFunction V)=0 := by
  have ha : allocation (0 : SetFunction V)=0 := by
    funext C
    by_cases hC : C.card=2
    · obtain ⟨u,v,huv,rfl⟩ := card_eq_two.mp hC
      rw [allocation_pair _ huv]
      have hm : minimumSlack (0 : SetFunction V) u v=0 :=
        minimumSlack_eq_zero (by intros; simp [delta])
      simp [hm]
    · exact allocation_zero _ hC
  rw [adjusted,ha]
  change 0+zetaLinear 0=0
  simp

theorem higher_right_dependsOn {y : SetFunction V}
    (hdegree : ∀ C,y C≠0 → C.card≤4) (T : Finset V) :
    DependsOn (higherClass y (classOf y) (Sum.inr T)) T := by
  apply zeta_dependsOn
  intro C hC
  by_contra he
  obtain ⟨hc,ha,hyC⟩ := classCoefficients_nonzero he
  obtain ⟨h3,rfl⟩ := right_class_is_triangle hdegree hc hyC ha
  exact hC Subset.rfl

theorem higher_right_zero_of_card_ne_three {y : SetFunction V}
    (hdegree : ∀ C,y C≠0 → C.card≤4) {T : Finset V} (hT : T.card≠3) :
    higherClass y (classOf y) (Sum.inr T)=0 := by
  apply (zeta_eq_zero_iff _).mpr
  funext C
  by_contra he
  obtain ⟨hc,ha,hyC⟩ := classCoefficients_nonzero he
  obtain ⟨h3,rfl⟩ := right_class_is_triangle hdegree hc hyC ha
  exact hT h3

theorem higher_left_dependsOn {y : SetFunction V}
    (hdegree : ∀ C,y C≠0 → C.card≤4) (a : Component y) :
    DependsOn (higherClass y (classOf y) (Sum.inl a)) ((family y).biUnion id) := by
  apply zeta_dependsOn
  intro C hC
  by_contra he
  exact hC (left_coefficients_subset_vertices hdegree a he)

def pieces (y : SetFunction V) : (ClassIndex y ⊕ Finset V) → SetFunction V :=
  Sum.elim (fun a => adjusted (higherClass y (classOf y) a))
    (fun C => residual y (higherClass y (classOf y)) C • setMonomial C)

theorem pieces_positive {y : SetFunction V} (hy : y ∅=0 ∧ ∀ v,y {v}=0)
    (hdegree : ∀ C,y C≠0 → C.card≤4) (hs : Supermodular (zeta y)) :
    (∀ i,TranslationNormalized (pieces y i) ∧ Supermodular (pieces y i)) ∧
    (∑ i,pieces y i)=zeta y := by
  classical
  have hytop : CliqueSupported (⊤ : SimpleGraph V) y := by
    refine ⟨hy.1,hy.2,?_⟩
    intro C u v hu hv huv hnon
    exact False.elim (hnon huv)
  obtain ⟨hp,hr,hrn,hrs,he⟩ := compatible_class_decomposition y hytop hs
    (classOf y) (classOf_compatible hdegree)
  constructor
  · intro i
    cases i with
    | inl a => exact ⟨(hp a).1,(hp a).2.1⟩
    | inr C =>
      refine ⟨?_,(setMonomial_supermodular C).smul (hr C)⟩
      by_cases hC : C.card=2
      · have hn : TranslationNormalized (setMonomial C) := by
          refine ⟨setMonomial_normalized (card_pos.mp (by omega)),?_⟩
          intro v
          have hnot : ¬C⊆{v} := by
            intro hsub
            have hcard:=card_le_card hsub
            simp only [card_singleton] at hcard
            omega
          simp [setMonomial,hnot]
        exact ⟨by change _*setMonomial C ∅=0; rw [hn.1,mul_zero],
          fun v => by change _*setMonomial C {v}=0; rw [hn.2 v,mul_zero]⟩
      · have hz := residual_zero y (higherClass y (classOf y)) hC
        simp only [pieces,Sum.elim_inr,hz,zero_smul]
        exact ⟨rfl,fun _ => rfl⟩
  · rw [Fintype.sum_sum_type]
    change (∑ a,adjusted (higherClass y (classOf y) a))+
      (∑ C,residual y (higherClass y (classOf y)) C • setMonomial C)=_
    rw [← zeta_eq_sum_monomials]
    exact he

theorem extreme_has_positive_component {n : ℕ} (hn : 4≤ n)
    {z : SetFunction (Fin n)} (hz : ExtremeSupermodular z)
    (hfull : Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=n-1)
    (hdegree : ∀ C,mobius z C≠0 → C.card≤4) :
    ∃ a : Component (mobius z),∃ t : ℝ,0< t ∧
      adjusted (higherClass (mobius z) (classOf (mobius z)) (Sum.inl a))=t • z ∧
      (family (mobius z)).biUnion id=univ := by
  classical
  let y:=mobius z
  have hy : y ∅=0 ∧ ∀ v,y {v}=0 :=
    (zeta_normalized_iff y).mp (by simpa [y] using hz.1)
  obtain ⟨hp,he⟩ := pieces_positive hy hdegree (by simpa [y] using hz.2.1)
  have hez : (∑ i,pieces y i)=z := by simpa [y] using he
  have hex : ∃ i,pieces y i≠0 := by
    by_contra h
    push_neg at h
    have hzero : (∑ i,pieces y i)=0 := sum_eq_zero (fun i hi => h i)
    exact hz.2.2.1 (hez.symm.trans hzero)
  obtain ⟨i,hi⟩ := hex
  obtain ⟨t,ht,hscale⟩ := hz.finite_summand (pieces y)
    (fun i => (hp i).1) (fun i => (hp i).2) hez hi
  have hsupport : ∀ S,DependsOn (pieces y i) S → S=univ := by
    intro S hS
    rw [hscale] at hS
    exact fullDimension_dependsOn_eq_univ (by omega) hz.1 hz.2.1 hfull
      (DependsOn.of_smul (ne_of_gt ht) hS)
  cases i with
  | inr C =>
    have hC : C.card=2 := by
      by_contra hnot
      have hzC := residual_zero y (higherClass y (classOf y)) hnot
      exact hi (by simp [pieces,hzC])
    have hdep : DependsOn (pieces y (Sum.inr C)) C := (setMonomial_dependsOn C).smul _
    have hcard:=congrArg Finset.card (hsupport C hdep)
    simp only [hC,card_univ,Fintype.card_fin] at hcard
    omega
  | inl c =>
    cases c with
    | inr T =>
      have hT : T.card=3 := by
        by_contra hnot
        have hzero:=higher_right_zero_of_card_ne_three hdegree hnot
        exact hi (by simp only [y,pieces,Sum.elim_inl,hzero,adjusted_zero_function])
      have hdep := PositiveDecomposition.DependsOn.adjusted
        (higher_right_dependsOn hdegree T)
      have hcard:=congrArg Finset.card (hsupport T hdep)
      simp only [hT,card_univ,Fintype.card_fin] at hcard
      omega
    | inl a =>
      have hdep := PositiveDecomposition.DependsOn.adjusted
        (higher_left_dependsOn hdegree a)
      exact ⟨a,t,ht,hscale,hsupport _ hdep⟩

theorem actualRootEdge_of_nonzero_coefficient {z : SetFunction V}
    (hn : Normalized z) (hs : Supermodular z) {C : Finset V}
    (hC : mobius z C≠0) {u v : V} (huv : u≠ v) (hu : u∈C) (hv : v∈C) :
    ActualRootEdge (basePolytope z) u v := by
  by_contra he
  have hzero : ∀ S : Finset V,u∉S → v∉S → delta z u v S=0 := by
    intro S hSu hSv
    apply le_antisymm _ (hs.elemental u v huv S hSu hSv)
    by_contra h
    exact he (exposedSegment_of_positive_delta hn hs huv hSu hSv (lt_of_not_ge h))
  have hcoeff := (nonedge_coefficients_zero_iff (mobius z) huv).mp
    (by simpa only [zeta_mobius] using hzero) C hu hv
  exact hC hcoeff

theorem actualRootEdge_of_graphical {z : SetFunction V} {G : SimpleGraph V}
    (hn : Normalized z) (hs : Supermodular z) (hG : Graphical G z)
    {u v : V} (h : ActualRootEdge (basePolytope z) u v) : G.Adj u v := by
  obtain ⟨a,ha,R,_,_,_,he⟩ := (isWeakMinkowskiSummand_graphical_iff hn hs).mpr hG
  exact basePolytope_summand_actualRootEdge hn hs G ha.le R he h

/-- Corollary4.4: for a full-dimensional extreme function in a K5-free graph,
the complete nonzero four-coefficient family is nonempty and triangle
connected, covers every vertex, and has precisely the actual direction graph
as its edge union. No zero tetrahedron is added to this family. -/
theorem full_refined_support {n : ℕ} (hn : 4≤ n) {G : SimpleGraph (Fin n)}
    (hG : G.CliqueFree 5) {z : SetFunction (Fin n)} (hz : ExtremeSupermodular z)
    (hgraph : Graphical G z)
    (hfull : Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=n-1) :
    (family (mobius z)).Nonempty ∧
      (tetrahedronGraph (family (mobius z))).Preconnected ∧
      (family (mobius z)).biUnion id=univ ∧
      actualDirectionGraph (basePolytope z)=edgeGraph (mobius z) := by
  classical
  let y:=mobius z
  have hy : CliqueSupported G y := (mobius_cliqueSupported_iff G z).mpr ⟨hz.1,hgraph⟩
  have hdegree : ∀ C,y C≠0 → C.card≤4 := fun C hC => nonzero_card_le_four hG hy hC
  obtain ⟨a,t,ht,hscale,hcover⟩ := extreme_has_positive_component hn hz hfull hdegree
  have hcomp := same_component_of_positive_piece a (ne_of_gt ht)
    (by simpa only [zeta_mobius] using hscale)
  have hconnected : (tetrahedronGraph (family y)).Preconnected := by
    intro C D
    exact SimpleGraph.ConnectedComponent.exact ((hcomp C).trans (hcomp D).symm)
  have hne : (family y).Nonempty := by
    have hm : (⟨0,by omega⟩ : Fin n)∈(family y).biUnion id := by
      rw [hcover]
      exact mem_univ _
    obtain ⟨C,hC,hv⟩ := mem_biUnion.mp hm
    exact ⟨C,hC⟩
  refine ⟨hne,hconnected,hcover,?_⟩
  have hpiece : Graphical (edgeGraph y)
      (adjusted (higherClass y (classOf y) (Sum.inl a))) :=
    adjusted_graphical ((cliqueSupported_iff _ _).mp (left_coefficients_supported hdegree a)).2
  have hzedge : Graphical (edgeGraph y) z := by
    intro u v huv hnon S hu hv
    have h:=hpiece u v huv hnon S hu hv
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
end GraphicalZonotopes

end
end
end BundlePart53

section BundlePart54
/- Source: Papers/GraphicalZonotopes/SetFunctionEmbeddingDirections.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace GraphicalZonotopes
open Finset

private def missingPairGraph {V : Type*} (u v : V) : SimpleGraph V where
  Adj a b := a≠ b ∧ (a≠ u ∨ b≠ v) ∧ (a≠ v ∨ b≠ u)
  symm := ⟨by intro a b h; tauto⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Actual exposed root edges are precisely the nonzero elemental rows,
with existence of a genuine conditioning context in both directions. -/
theorem actualRootEdge_iff_nonzero_delta {V : Type*} [Fintype V] [LinearOrder V]
    {f : SetFunction V} (hn : Normalized f) (hs : Supermodular f) (u v : V) :
    ActualRootEdge (basePolytope f) u v ↔ u≠ v ∧
      ∃ S : Finset V,u∉S ∧ v∉S ∧ delta f u v S≠0 := by
  constructor
  · intro h
    refine ⟨h.1,?_⟩
    by_contra hnone
    push_neg at hnone
    have hg : Graphical (missingPairGraph u v) f := by
      intro a b hab hnon S ha hb
      have hp : (a=u ∧ b=v) ∨ (a=v ∧ b=u) := by
        change ¬(a≠ b ∧ (a≠ u ∨ b≠ v) ∧ (a≠ v ∨ b≠ u)) at hnon
        tauto
      rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hnone S ha hb
      · rw [delta_comm]
        exact hnone S hb ha
    have hh := RefinedTriangleComponents.actualRootEdge_of_graphical hn hs hg h
    exact hh.2.1.elim (fun hn => hn rfl) (fun hn => hn rfl)
  · rintro ⟨huv,S,hu,hv,hd⟩
    exact exposedSegment_of_positive_delta hn hs huv hu hv
      (lt_of_le_of_ne (hs.elemental u v huv S hu hv) (Ne.symm hd))

namespace SetFunctionEmbedding
variable {V W : Type*} [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]

theorem reconstruct_of_graphical_supported (e : W ↪ V) {G : SimpleGraph V}
    {f : SetFunction V} (hn : TranslationNormalized f) (hG : Graphical G f)
    (hS : ∀ u v,G.Adj u v → u∈Set.range e) : extend e (restrict e f)=f := by
  apply reconstruct_of_insert_absent e f
  intro u hu
  apply insert_absent_of_zero_deltas hn u
  intro v huv S huS hvS
  exact hG u v huv (fun hadj => hu (hS u v hadj)) S huS hvS

theorem extreme_restrict_of_reconstruction (e : W ↪ V) {f : SetFunction V}
    (hf : ExtremeSupermodular f) (hrec : extend e (restrict e f)=f) :
    ExtremeSupermodular (restrict e f) := by
  refine ⟨restrict_translationNormalized e hf.1,restrict_supermodular e hf.2.1,?_,?_⟩
  · intro he
    apply hf.2.2.1
    rw [← hrec,he]
    funext S
    rfl
  · intro g h hgn hhn hgs hhs he
    have hsum : extend e g+extend e h=f := by
      rw [← hrec,← he]
      rfl
    obtain ⟨a,ha,hscale⟩ := hf.2.2.2 (extend e g) (extend e h)
      (extend_translationNormalized e hgn) (extend_translationNormalized e hhn)
      (extend_supermodular e hgs) (extend_supermodular e hhs) hsum
    refine ⟨a,ha,?_⟩
    have hh := congrArg (restrict e) hscale
    simpa only [restrict_extend,restrict_smul] using hh

/-- The complete actual direction graph is transported by the embedding;
new coordinates have no edges, and every retained edge stays exposed. -/
theorem actualDirectionGraph_extend (e : W ↪ V) {f : SetFunction W}
    (hn : TranslationNormalized f) (hs : Supermodular f) :
    actualDirectionGraph (basePolytope (extend e f))=
      (actualDirectionGraph (basePolytope f)).map e := by
  ext u v
  rw [SimpleGraph.map_adj]
  constructor
  · intro huv
    obtain ⟨hne,S,hu,hv,hd⟩ := (actualRootEdge_iff_nonzero_delta
      (extend_translationNormalized e hn).1 (extend_supermodular e hs) u v).mp huv
    have huR : u∈Set.range e := by
      by_contra h
      exact hd (delta_extend_not_range e f u v h S)
    have hvR : v∈Set.range e := by
      by_contra h
      rw [delta_comm] at hd
      exact hd (delta_extend_not_range e f v u h S)
    obtain ⟨a,rfl⟩ := huR
    obtain ⟨b,rfl⟩ := hvR
    refine ⟨a,b,?_,rfl,rfl⟩
    apply (actualRootEdge_iff_nonzero_delta hn.1 hs a b).mpr
    refine ⟨fun he => hne (congrArg e he),pullSet e S,by simpa using hu,by simpa using hv,?_⟩
    simpa only [delta_extend] using hd
  · rintro ⟨a,b,hab,rfl,rfl⟩
    obtain ⟨hne,S,ha,hb,hd⟩ := (actualRootEdge_iff_nonzero_delta hn.1 hs a b).mp hab
    apply (actualRootEdge_iff_nonzero_delta (extend_translationNormalized e hn).1
      (extend_supermodular e hs) (e a) (e b)).mpr
    refine ⟨fun he => hne (e.injective he),S.map e,by simpa using ha,by simpa using hb,?_⟩
    simpa only [delta_extend,pullSet_map] using hd

theorem actualDirectionGraph_restrict (e : W ↪ V) {f : SetFunction V}
    (hn : TranslationNormalized f) (hs : Supermodular f)
    (hrec : extend e (restrict e f)=f) :
    actualDirectionGraph (basePolytope (restrict e f))=
      (actualDirectionGraph (basePolytope f)).comap e := by
  have he := actualDirectionGraph_extend e (restrict_translationNormalized e hn)
    (restrict_supermodular e hs)
  rw [hrec] at he
  have hh := congrArg (fun G : SimpleGraph V => G.comap e) he
  simpa only [SimpleGraph.comap_map_eq] using hh.symm

theorem edgeFamily_map (e : W ↪ V) (G : SimpleGraph W) :
    edgeFamily (G.map e)=(edgeFamily G).image (fun C => C.map e) := by
  ext D
  constructor
  · intro hD
    obtain ⟨hd,hcl⟩ := (mem_edgeFamily _ _).mp hD
    obtain ⟨C,hC,rfl⟩ := (SimpleGraph.isClique_map_finset_iff_of_nontrivial
      (G := G) (f := e) (show D.Nontrivial from one_lt_card_iff_nontrivial.mp (by omega))).mp hcl
    refine mem_image.mpr ⟨C,(mem_edgeFamily G C).mpr ⟨?_,hC⟩,rfl⟩
    simpa only [card_map] using hd
  · intro hD
    obtain ⟨C,hC,rfl⟩ := mem_image.mp hD
    obtain ⟨hc,hcl⟩ := (mem_edgeFamily _ _).mp hC
    exact (mem_edgeFamily _ _).mpr ⟨by simpa only [card_map] using hc,
      (show G.IsClique C from hcl).finsetMap⟩

/-- The number of genuine root directions is preserved under every
injective coordinate embedding, including arbitrary coordinate relabelings. -/
theorem directionCount_extend (e : W ↪ V) {f : SetFunction W}
    (hn : TranslationNormalized f) (hs : Supermodular f) :
    directionCount (basePolytope (extend e f))=directionCount (basePolytope f) := by
  unfold directionCount
  rw [actualDirectionGraph_extend e hn hs,edgeFamily_map,
    card_image_of_injective _ (Finset.map_injective e)]

end SetFunctionEmbedding
end GraphicalZonotopes

end
end
end BundlePart54

section BundlePart55
/- Source: Papers/GraphicalZonotopes/ThreeTreeIncidenceTree.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem triangles_cliqueGraph {C : Finset V} (hC : C.card=4) :
    triangles (cliqueGraph C)=C.powersetCard 3 := by
  classical
  ext T
  rw [mem_triangles,mem_powersetCard]
  constructor
  · rintro ⟨hT,hcl⟩
    exact ⟨(ThreeTreeOn.tetrahedron C hC).clique_subset_active (by omega) hcl,hT⟩
  · rintro ⟨hTC,hT⟩
    exact ⟨hT,fun u hu v hv huv => ⟨huv,hTC hu,hTC hv⟩⟩

theorem triangles_after_attachment {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u : V} (hu : u∉S) {A : Finset V}
    (hA : A.card=3) (hAS : A⊆S) (hcA : G.IsClique A) :
    triangles (G⊔attachmentStar u A)=triangles G∪
      (A.powersetCard 2).image (insert u) := by
  classical
  ext T
  rw [mem_triangles,mem_union,mem_triangles,mem_image]
  constructor
  · rintro ⟨hT,hcl⟩
    by_cases huT : u∈T
    · right
      refine ⟨T.erase u,mem_powersetCard.mpr ⟨?_,?_⟩,insert_erase huT⟩
      · intro v hv
        exact (attached_vertex_adj_iff h hu hAS v).mp
          (hcl huT (mem_of_mem_erase hv) (Ne.symm (ne_of_mem_erase hv)))
      · rw [card_erase_of_mem huT,hT]
    · exact Or.inl ⟨hT,clique_before_attachment huT hcl⟩
  · rintro (⟨hT,hcl⟩ | ⟨B,hB,rfl⟩)
    · exact ⟨hT,fun v hv w hw hvw => Or.inl (hcl hv hw hvw)⟩
    · obtain ⟨hBA,hB⟩ := mem_powersetCard.mp hB
      have huB : u∉B := fun hum => hu (hAS (hBA hum))
      refine ⟨by rw [card_insert_of_notMem huB,hB],?_⟩
      have hcl := attached_tetrahedron_clique h hu hAS hcA
      exact fun v hv w hw hvw => hcl (insert_subset_insert u hBA hv)
        (insert_subset_insert u hBA hw) hvw

theorem triangles_after_attachment_card {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u : V} (hu : u∉S) {A : Finset V}
    (hA : A.card=3) (hAS : A⊆S) (hcA : G.IsClique A) :
    (triangles (G⊔attachmentStar u A)).card=(triangles G).card+3 := by
  classical
  have hdis : Disjoint (triangles G) ((A.powersetCard 2).image (insert u)) := by
    apply disjoint_left.mpr
    intro T hT hnew
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hnew
    obtain ⟨hT,hcl⟩ := mem_triangles.mp hT
    exact hu ((h.clique_subset_active (by omega) hcl) (mem_insert_self _ _))
  have himage : ((A.powersetCard 2).image (insert u)).card=(A.powersetCard 2).card := by
    apply card_image_of_injOn
    intro B hB C hC he
    have huB : u∉B := fun hum => hu (hAS ((mem_powersetCard.mp hB).1 hum))
    have huC : u∉C := fun hum => hu (hAS ((mem_powersetCard.mp hC).1 hum))
    have herase := congrArg (fun D : Finset V => D.erase u) he
    simpa [huB,huC] using herase
  rw [triangles_after_attachment h hu hA hAS hcA,card_union_of_disjoint hdis,
    himage,card_powersetCard,hA]
  norm_num

/-- The exact count includes all graph triangles, not a chosen set of
construction separators. -/
theorem ThreeTreeOn.triangles_card {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : (triangles G).card=3*(tetrahedra G).card+1 := by
  classical
  induction h with
  | tetrahedron C hC =>
    rw [triangles_cliqueGraph hC,card_powersetCard,hC,
      tetrahedra_cliqueGraph hC,card_singleton]
    norm_num
  | @attach S G h u hu A hA hAS hcA ih =>
    rw [triangles_after_attachment_card h hu hA hAS hcA,
      tetrahedra_after_attachment h hu hA hAS hcA,
      card_insert_of_notMem (attached_tetrahedron_not_old h hu),ih]
    omega

def incidenceCliqueNeighbors (G : SimpleGraph V) (C : ↥(tetrahedra G)) :
    ↥(C.1.powersetCard 3) ≃ (cliqueTriangleIncidence G).neighborSet (Sum.inl C) := by
  classical
  have hc := (mem_filter.mp C.2).2
  let f : ↥(C.1.powersetCard 3) →
      (cliqueTriangleIncidence G).neighborSet (Sum.inl C) := fun T =>
    ⟨Sum.inr ⟨T.1,mem_triangles.mpr
      ⟨(mem_powersetCard.mp T.2).2,fun u hu v hv huv =>
        hc.2 ((mem_powersetCard.mp T.2).1 hu) ((mem_powersetCard.mp T.2).1 hv) huv⟩⟩,
      (mem_powersetCard.mp T.2).1⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro T U he
    apply Subtype.ext
    simpa only [f, Subtype.mk.injEq, Sum.inr.injEq] using he
  · rintro ⟨N,hN⟩
    cases N with
    | inl D => exact False.elim hN
    | inr T =>
      refine ⟨⟨T.1,mem_powersetCard.mpr ⟨hN,(mem_triangles.mp T.2).1⟩⟩,?_⟩
      rfl

theorem incidence_clique_degree (G : SimpleGraph V) (C : ↥(tetrahedra G)) :
    (cliqueTriangleIncidence G).degree (Sum.inl C)=4 := by
  classical
  have hc := (mem_filter.mp C.2).2.1
  rw [← SimpleGraph.card_neighborSet_eq_degree,
    ← Fintype.card_congr (incidenceCliqueNeighbors G C)]
  simp only [Fintype.card_coe,card_powersetCard,hc]
  norm_num

theorem incidence_edge_card (G : SimpleGraph V) :
    (cliqueTriangleIncidence G).edgeFinset.card=4*(tetrahedra G).card := by
  classical
  let L : Finset (CliqueTriangleNode G) := univ.image Sum.inl
  let R : Finset (CliqueTriangleNode G) := univ.image Sum.inr
  have hb : (cliqueTriangleIncidence G).IsBipartiteWith L R := by
    constructor
    · apply Set.disjoint_left.mpr
      intro N hL hR
      obtain ⟨C,hC,hCN⟩ := mem_image.mp hL
      obtain ⟨T,hT,hTN⟩ := mem_image.mp hR
      have he := hCN.trans hTN.symm
      cases he
    · intro N M hNM
      cases N <;> cases M
      · exact False.elim hNM
      · exact Or.inl ⟨by simp [L],by simp [R]⟩
      · exact Or.inr ⟨by simp [R],by simp [L]⟩
      · exact False.elim hNM
  calc
    (cliqueTriangleIncidence G).edgeFinset.card=
        ∑ N∈L,(cliqueTriangleIncidence G).degree N :=
      (SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hb).symm
    _=∑ C : ↥(tetrahedra G),(4:ℕ) := by
      dsimp [L]
      rw [sum_image (fun C hC D hD hCD => Sum.inl.inj hCD)]
      simp only [incidence_clique_degree]
    _=4*(tetrahedra G).card := by simp [Nat.mul_comm]

/-- The complete literal clique–triangle incidence graph of any 3-tree
is a tree. Connectedness and the exact vertex/edge counts are independently
proved for all actual cliques, so no incidence-tree property is assumed. -/
theorem ThreeTreeOn.incidence_isTree {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : (cliqueTriangleIncidence G).IsTree := by
  classical
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨h.incidence_connected,?_⟩
  simp only [Nat.card_eq_fintype_card,CliqueTriangleNode,Fintype.card_sum,Fintype.card_coe]
  rw [← SimpleGraph.edgeFinset_card,incidence_edge_card,h.triangles_card]
  omega

end GraphicalZonotopes

end
end
end BundlePart55

section BundlePart56
/- Source: Papers/GraphicalZonotopes/PrunedIncidence.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def internalTriangles (G : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact (triangles G).filter (fun T => 2≤ triangleMultiplicity G T)

theorem mem_internalTriangles {G : SimpleGraph V} {T : Finset V} :
    T∈internalTriangles G ↔ T∈triangles G ∧ 2≤ triangleMultiplicity G T := by
  classical
  simp [internalTriangles]

abbrev InternalIncidenceNode (G : SimpleGraph V) :=
  ↥(tetrahedra G) ⊕ ↥(internalTriangles G)

def internalIncidenceEmbedding (G : SimpleGraph V) :
    InternalIncidenceNode G ↪ CliqueTriangleNode G :=
  Function.Embedding.sumMap (Function.Embedding.refl _) {
    toFun := fun T => ⟨T.1,(mem_internalTriangles.mp T.2).1⟩
    inj' := by intro T U he; apply Subtype.ext; simpa only [Subtype.mk.injEq] using he }

/-- The incidence tree with leaf triangles removed. Every remaining
edge carries a nonconstant response, so the local matching property applies
in both directions without a distinguished global root. -/
def internalIncidence (G : SimpleGraph V) : SimpleGraph (InternalIncidenceNode G) :=
  (cliqueTriangleIncidence G).comap (internalIncidenceEmbedding G)

@[simp] theorem internalIncidence_adj_left_right (G : SimpleGraph V)
    (C : ↥(tetrahedra G)) (T : ↥(internalTriangles G)) :
    (internalIncidence G).Adj (Sum.inl C) (Sum.inr T) ↔ T.1⊆C.1 := Iff.rfl

theorem internal_triangle_of_shared {G : SimpleGraph V} {C D T : Finset V}
    (hC : C∈tetrahedra G) (hD : D∈tetrahedra G) (hCD : C≠ D)
    (hT : T.card=3) (hTC : T⊆C) (hTD : T⊆D) : T∈internalTriangles G := by
  classical
  have hc := (mem_filter.mp hC).2.2
  apply mem_internalTriangles.mpr
  refine ⟨mem_triangles.mpr ⟨hT,fun u hu v hv huv => hc (hTC hu) (hTC hv) huv⟩,?_⟩
  unfold triangleMultiplicity
  exact Nat.succ_le_of_lt (one_lt_card.mpr
    ⟨C,mem_filter.mpr ⟨hC,hTC⟩,D,mem_filter.mpr ⟨hD,hTD⟩,hCD⟩)

theorem internalIncidence_reachable_of_shared {G : SimpleGraph V}
    (C D : ↥(tetrahedra G))
    (hCD : (TriangleComponents.cliqueGraph G).Adj C.1 D.1) :
    (internalIncidence G).Reachable (Sum.inl C) (Sum.inl D) := by
  classical
  obtain ⟨T,hTsub,hTcard⟩ := exists_subset_card_eq hCD.2.2.2.2.2
  have hTC : T⊆C.1 := hTsub.trans inter_subset_left
  have hTD : T⊆D.1 := hTsub.trans inter_subset_right
  have hT := internal_triangle_of_shared C.2 D.2 hCD.2.2.2.2.1 hTcard hTC hTD
  exact (SimpleGraph.Adj.reachable
    (show (internalIncidence G).Adj (Sum.inl C) (Sum.inr ⟨T,hT⟩) from hTC)).trans
      (SimpleGraph.Adj.reachable
        (show (internalIncidence G).Adj (Sum.inr ⟨T,hT⟩) (Sum.inl D) from hTD))

theorem internalIncidence_reachable_of_tetrahedron_reachable {G : SimpleGraph V}
    (C D : ↥(tetrahedra G))
    (hp : (TriangleComponents.cliqueGraph G).Reachable C.1 D.1) :
    (internalIncidence G).Reachable (Sum.inl C) (Sum.inl D) := by
  classical
  rw [SimpleGraph.reachable_eq_reflTransGen] at hp
  have hpath : ∀ E,Relation.ReflTransGen (TriangleComponents.cliqueGraph G).Adj C.1 E →
      ∃ hE : E∈tetrahedra G,
        (internalIncidence G).Reachable (Sum.inl C) (Sum.inl ⟨E,hE⟩) := by
    intro E hE
    induction hE with
    | refl => exact ⟨C.2,SimpleGraph.Reachable.rfl⟩
    | @tail E F hE hEF ih =>
      obtain ⟨hEmem,hreach⟩ := ih
      have hFmem : F∈tetrahedra G := mem_filter.mpr
        ⟨mem_univ _,hEF.2.1,hEF.2.2.2.1⟩
      exact ⟨hFmem,hreach.trans
        (internalIncidence_reachable_of_shared ⟨E,hEmem⟩ ⟨F,hFmem⟩ hEF)⟩
  obtain ⟨hD,hreach⟩ := hpath _ hp
  exact hreach

theorem ThreeTreeOn.internalIncidence_connected {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : (internalIncidence G).Connected := by
  classical
  obtain ⟨C,hC⟩ := h.tetrahedra_nonempty
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨Sum.inl ⟨C,hC⟩,?_⟩
  intro N
  cases N with
  | inl D =>
    exact internalIncidence_reachable_of_tetrahedron_reachable ⟨C,hC⟩ D
      (h.tetrahedra_reachable hC D.2)
  | inr T =>
    have ht := mem_triangles.mp (mem_internalTriangles.mp T.2).1
    obtain ⟨D,hD,hTD⟩ := h.triangle_extends ht.1 ht.2
    exact (internalIncidence_reachable_of_tetrahedron_reachable ⟨C,hC⟩ ⟨D,hD⟩
      (h.tetrahedra_reachable hC hD)).trans
        (SimpleGraph.Adj.reachable
          (show (internalIncidence G).Adj (Sum.inl ⟨D,hD⟩) (Sum.inr T) from hTD))

theorem ThreeTreeOn.internalIncidence_isTree {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : (internalIncidence G).IsTree := by
  exact ⟨h.internalIncidence_connected,
    h.incidence_isTree.isAcyclic.of_comap (internalIncidenceEmbedding G)⟩

end GraphicalZonotopes

end
end
end BundlePart56

section BundlePart57
/- Source: Papers/GraphicalZonotopes/RootedResponseAlgebra.lean -/












@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace GraphicalZonotopes
namespace RootedResponse

/-! The local construction in Lemma 6.2. These finite identities concern
the first tetrahedron of an arbitrary branch. The subsequent branch induction
must establish their application to the actual private-kernel equations. -/

abbrev Row := Fin 3 → Bool

abbrev Nonconstant (v : Row) : Prop :=
  (∃ i,v i=false) ∧ (∃ i,v i=true)

def third : Fin 3 → Fin 3 → Fin 3 :=
  ![![0,2,1],![2,1,0],![1,0,2]]

theorem third_distinct : ∀ i j : Fin 3,i≠ j → third i j≠ i ∧ third i j≠ j := by
  decide

/-- The diagonal is the boundary-edge coordinate. An off-diagonal entry
represents the common edge of two nonboundary faces. -/
def compatibleRows (occupied : Finset (Fin 3)) (v : Row) (i j : Fin 3) : Bool :=
  if i=j then v i
  else if i∈occupied then
    if j∈occupied then
      if occupied=Finset.univ then v (third i j) else !(v (third i j))
    else v j
  else v i

theorem compatibleRows_diagonal : ∀ occupied v i,
    compatibleRows occupied v i i=v i := by
  decide

theorem unoccupied_row_constant : ∀ occupied v i,i∉occupied →
    ∀ j,compatibleRows occupied v i j=v i := by
  decide

/-- This is exactly the simultaneous row choice in equation (6.1), for all
eight occupation patterns and all six permitted boundary response states. -/
theorem occupied_rows_nonconstant : ∀ occupied v,Nonconstant v →
    ∀ i,i∈occupied → Nonconstant (compatibleRows occupied v i) := by
  decide

theorem occupied_intersections_agree : ∀ occupied v i j,i≠ j →
    (i∈occupied ∨ j∈occupied) →
      compatibleRows occupied v i j=compatibleRows occupied v j i := by
  decide

def integerBit (b : Bool) : ℤ := if b then 1 else 0

/-- Equation (6.4), before embedding its integer values into the reals. -/
def coreSlack (a b x y : Bool) : ℤ :=
  max (integerBit a) (integerBit b)-integerBit a*integerBit y-
    integerBit b*integerBit x+integerBit x*integerBit y

theorem coreSlack_nonnegative : ∀ a b x y,0≤ coreSlack a b x y := by decide

theorem coreSlack_has_zero : ∀ a b,∃ x y,coreSlack a b x y=0 := by decide

theorem coreSlack_has_positive : ∀ a b,∃ x y,0< coreSlack a b x y := by decide

/-- Both values of either third-vertex bit remain visible at a reduced
zero when the two rows agree. -/
theorem coreSlack_equal_bits_zero : ∀ a x,coreSlack a a x a=0 := by decide

def boundarySlack (v x p : Bool) : ℤ :=
  -integerBit v*integerBit p+integerBit x*integerBit p

def boundaryMinimum (v x : Bool) : ℤ := integerBit v*(integerBit x-1)

theorem boundaryMinimum_le : ∀ v x p,boundaryMinimum v x≤ boundarySlack v x p := by
  decide

theorem boundaryMinimum_attained : ∀ v x,∃ p,boundarySlack v x p=boundaryMinimum v x := by
  decide

theorem boundaryStrictExcess : ∀ v,∃ x p,boundaryMinimum v x< boundarySlack v x p := by
  decide

theorem boundary_tie : ∀ v p,boundarySlack v v p=boundaryMinimum v v := by decide

/-- Recovering the effective coefficients from the three reduced zero
rows in the zero-bit case. All variation coefficients remain arbitrary real
numbers. -/
theorem recover_zero_effective_row (c A B h : ℝ)
    (h00 : c=0) (h10 : c-B=0) (h01 : c-A=0) :
    c=0 ∧ A=0 ∧ B=0 := by
  exact ⟨h00,by linarith,by linarith⟩

/-- The corresponding three-row recovery for the one-bit case. -/
theorem recover_one_effective_row (c A B h : ℝ)
    (h10 : c-B=0) (h01 : c-A=0) (h11 : c-A-B+h=0) :
    c=h ∧ A=h ∧ B=h := by
  exact ⟨by linarith,by linarith,by linarith⟩

def realBit (b : Bool) : ℝ := if b then 1 else 0

/-- The one-child completion `r=1-b` determines the child scale, rather
than merely asserting that the resulting boundary response vanishes. -/
theorem recover_one_child (b : Row) (hb : Nonconstant b) (d lam h : ℝ)
    (he : ∀ i,d-lam*(1-realBit (b i))=h*realBit (b i)) :
    d=h ∧ lam=h := by
  obtain ⟨⟨i,hi⟩,⟨j,hj⟩⟩ := hb
  have h0 := he i
  have h1 := he j
  simp only [hi,hj,realBit,Bool.false_eq_true,ite_false,ite_true] at h0 h1
  constructor <;> nlinarith

def unitResponse (i : Fin 3) (x : Fin 3) : ℝ := if x=i then 1 else 0

/-- Two other unit responses complete a unit row, and equation (6.6)
then fixes both child scales and the triangle coefficient. -/
theorem recover_two_unit_children (i j k : Fin 3)
    (hij : i≠ j) (hik : i≠ k) (hjk : j≠ k) (d lam mu h : ℝ)
    (he : ∀ x,d-lam*unitResponse i x-mu*unitResponse j x=h*unitResponse k x) :
    d=h ∧ lam=h ∧ mu=h := by
  have hi := he i
  have hj := he j
  have hk := he k
  simp only [unitResponse,ite_true,ite_false,hij,hik,hjk,
    Ne.symm hij,Ne.symm hik,Ne.symm hjk,mul_one,mul_zero,sub_zero] at hi hj hk
  exact ⟨by linarith,by linarith,by linarith⟩

/-- The complementary-unit completion gives triangle coefficient `2h`
and fixes the same common scale on both children. -/
theorem recover_two_complement_children (i j k : Fin 3)
    (hij : i≠ j) (hik : i≠ k) (hjk : j≠ k) (d lam mu h : ℝ)
    (he : ∀ x,d-lam*(1-unitResponse i x)-mu*(1-unitResponse j x)=
      h*(1-unitResponse k x)) :
    d=2*h ∧ lam=h ∧ mu=h := by
  have hi := he i
  have hj := he j
  have hk := he k
  simp only [unitResponse,ite_true,ite_false,hij,hik,hjk,
    Ne.symm hij,Ne.symm hik,Ne.symm hjk,mul_one,mul_zero,sub_zero,sub_self] at hi hj hk
  exact ⟨by linarith,by linarith,by linarith⟩

end RootedResponse
end GraphicalZonotopes

end
end BundlePart57

section BundlePart58
/- Source: Papers/GraphicalZonotopes/TetrahedronRows.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 100000
set_option maxRecDepth 4096
namespace GraphicalZonotopes
namespace RootedResponse

/-- Face `i` has coordinates indexed by the other three faces. The entry
at `(i,j)` belongs to their actual common edge. Diagonal entries are unused. -/
abbrev FaceRows := Fin 4 → Fin 4 → Bool

abbrev NonconstantFace (f : Fin 4 → Bool) (i : Fin 4) : Prop :=
  (∃ j,j≠ i ∧ f j=false) ∧ (∃ j,j≠ i ∧ f j=true)

abbrev ConstantFace (f : Fin 4 → Bool) (i : Fin 4) : Prop :=
  ∃ b,∀ j,j≠ i → f j=b

def fourRows (occupied : Finset (Fin 3)) (v : Row) : FaceRows :=
  ![![false,compatibleRows occupied v 0 1,compatibleRows occupied v 0 2,v 0],
    ![compatibleRows occupied v 1 0,false,compatibleRows occupied v 1 2,v 1],
    ![compatibleRows occupied v 2 0,compatibleRows occupied v 2 1,false,v 2],
    ![v 0,v 1,v 2,false]]

abbrev internalFace (occupied : Finset (Fin 3)) (i : Fin 4) : Prop :=
  i=3 ∨ ∃ j : Fin 3,j∈occupied ∧ i=j.castSucc

theorem fourRows_root : ∀ occupied v (i : Fin 3),
    fourRows occupied v 3 i.castSucc=v i := by decide

theorem fourRows_nonconstant : ∀ occupied v,Nonconstant v →
    ∀ i,internalFace occupied i → NonconstantFace (fourRows occupied v i) i := by
  unfold Nonconstant NonconstantFace internalFace
  decide

theorem fourRows_constant : ∀ occupied v i,¬internalFace occupied i →
    ConstantFace (fourRows occupied v i) i := by decide

theorem fourRows_agree : ∀ occupied v i j,i≠ j →
    (internalFace occupied i ∨ internalFace occupied j) →
      fourRows occupied v i j=fourRows occupied v j i := by decide

/-- Relabel the root face by a literal permutation. This construction
works for each of the four possible incoming faces; no preferred vertex is
part of the final local-state predicate. -/
def relabelledRows (internal : Finset (Fin 4)) (r : Fin 4)
    (v : Fin 4 → Bool) : FaceRows :=
  let p := Equiv.swap (3 : Fin 4) r
  let occupied := Finset.univ.filter (fun i : Fin 3 => p i.castSucc∈internal)
  let input : Row := fun i => v (p i.castSucc)
  fun i j => fourRows occupied input (p.symm i) (p.symm j)

/-- The finite local extension theorem for one actual tetrahedron. Every
prescribed nonconstant row on any internal face extends to rows on all four
faces. Internal rows remain nonconstant, leaf rows are constant, and every
edge incident with an internal face has matching rows on its two faces. -/
theorem relabelledRows_spec : ∀ internal r v,r∈internal → NonconstantFace v r →
    (∀ j,j≠ r → relabelledRows internal r v r j=v j) ∧
    (∀ i,i∈internal → NonconstantFace (relabelledRows internal r v i) i) ∧
    (∀ i,i∉internal → ConstantFace (relabelledRows internal r v i) i) ∧
    (∀ i j,i≠ j → (i∈internal ∨ j∈internal) →
      relabelledRows internal r v i j=relabelledRows internal r v j i) := by
  unfold NonconstantFace ConstantFace
  decide

theorem exists_nonconstantFace : ∀ r : Fin 4,∃ v : Fin 4 → Bool,NonconstantFace v r := by decide

end RootedResponse
end GraphicalZonotopes

end
end BundlePart58

section BundlePart59
/- Source: Papers/GraphicalZonotopes/FourState.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace RootedResponse
variable {W : Type*} [Fintype W]

abbrev NonconstantAt (v : W → Bool) (r : W) : Prop :=
  (∃ j,j≠ r ∧ v j=false) ∧ (∃ j,j≠ r ∧ v j=true)

/-- Intrinsic local states on the four vertices of a tetrahedron. A face
is indexed by its missing vertex, and a coordinate on that face is indexed
by the third vertex opposite the corresponding edge. -/
structure FourState (internal : W → Prop) where
  row : W → W → Bool
  nonconstant : ∀ i,internal i → NonconstantAt (row i) i
  constant : ∀ i,¬internal i → ∃ b,∀ j,j≠ i → row i j=b
  agree : ∀ i j,i≠ j → (internal i ∨ internal j) → row i j=row j i

theorem fourState_extend (hcard : Fintype.card W=4) (internal : W → Prop)
    (r : W) (hr : internal r) (v : W → Bool) (hv : NonconstantAt v r) :
    ∃ s : FourState internal,∀ j,j≠ r → s.row r j=v j := by
  classical
  let e := Fintype.equivFinOfCardEq hcard
  let I : Finset (Fin 4) := Finset.univ.filter (fun i => internal (e.symm i))
  let input : Fin 4 → Bool := fun i => v (e.symm i)
  have hroot : e r∈I := by simp [I,hr]
  have hin : NonconstantFace input (e r) := by
    obtain ⟨⟨j,hjr,hj⟩,⟨k,hkr,hk⟩⟩ := hv
    exact ⟨⟨e j,(fun he => hjr (e.injective he)),by simpa [input] using hj⟩,
      ⟨e k,(fun he => hkr (e.injective he)),by simpa [input] using hk⟩⟩
  obtain ⟨hport,hnon,hconst,hagree⟩ := relabelledRows_spec I (e r) input hroot hin
  let rows : W → W → Bool := fun i j => relabelledRows I (e r) input (e i) (e j)
  have hnon' : ∀ i,internal i → NonconstantAt (rows i) i := by
    intro i hi
    obtain ⟨⟨j,hji,hj⟩,⟨k,hki,hk⟩⟩ := hnon (e i) (by simp [I,hi])
    refine ⟨⟨e.symm j,?_,?_⟩,⟨e.symm k,?_,?_⟩⟩
    · intro he
      exact hji (by simpa only [Equiv.apply_symm_apply] using congrArg e he)
    · simpa only [rows,Equiv.apply_symm_apply] using hj
    · intro he
      exact hki (by simpa only [Equiv.apply_symm_apply] using congrArg e he)
    · simpa only [rows,Equiv.apply_symm_apply] using hk
  have hconst' : ∀ i,¬internal i → ∃ b,∀ j,j≠ i → rows i j=b := by
    intro i hi
    obtain ⟨b,hb⟩ := hconst (e i) (by simp [I,hi])
    exact ⟨b,fun j hji => hb (e j) (fun he => hji (e.injective he))⟩
  have hagree' : ∀ i j,i≠ j → (internal i ∨ internal j) → rows i j=rows j i := by
    intro i j hij hi
    apply hagree (e i) (e j) (fun he => hij (e.injective he))
    simpa only [I,Finset.mem_filter,Finset.mem_univ,true_and,
      Equiv.symm_apply_apply] using hi
  refine ⟨⟨rows,hnon',hconst',hagree'⟩,?_⟩
  intro j hjr
  simpa only [rows,input,Equiv.symm_apply_apply] using
    hport (e j) (fun he => hjr (e.injective he))

theorem exists_nonconstantAt (hcard : Fintype.card W=4) (r : W) :
    ∃ v : W → Bool,NonconstantAt v r := by
  classical
  have h := exists_nonconstantFace
  let e := Fintype.equivFinOfCardEq hcard
  obtain ⟨v,⟨⟨j,hjr,hj⟩,⟨k,hkr,hk⟩⟩⟩ := h (e r)
  refine ⟨fun x => v (e x),⟨e.symm j,?_,?_⟩,⟨e.symm k,?_,?_⟩⟩
  · intro he
    exact hjr (by simpa only [Equiv.apply_symm_apply] using congrArg e he)
  · simpa only [Equiv.apply_symm_apply] using hj
  · intro he
    exact hkr (by simpa only [Equiv.apply_symm_apply] using congrArg e he)
  · simpa only [Equiv.apply_symm_apply] using hk

theorem fourState_nonempty (hcard : Fintype.card W=4) (internal : W → Prop) :
    Nonempty (FourState internal) := by
  classical
  by_cases hi : ∃ r,internal r
  · obtain ⟨r,hr⟩ := hi
    obtain ⟨v,hv⟩ := exists_nonconstantAt hcard r
    obtain ⟨s,hs⟩ := fourState_extend hcard internal r hr v hv
    exact ⟨s⟩
  · exact ⟨{
      row := fun _ _ => false
      nonconstant := fun i hi' => False.elim (hi ⟨i,hi'⟩)
      constant := fun _ _ => ⟨false,fun _ _ => rfl⟩
      agree := fun _ _ _ _ => rfl }⟩

end RootedResponse
end GraphicalZonotopes

end
end
end BundlePart59

section BundlePart60
/- Source: Papers/GraphicalZonotopes/TriangleRows.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace GraphicalZonotopes
namespace RootedResponse
open Finset
open scoped BigOperators

def unitBit (i : Fin 3) (x : Fin 3) : Bool := decide (x=i)

def exceptionalCoordinate (v : Row) : Fin 3 :=
  if v 0=v 1 then 2 else if v 0=v 2 then 1 else 0

/-- Each nonconstant three-bit vector is a unit vector or a complementary
unit vector. The exceptional coordinate is selected by a fixed formula. -/
theorem exceptionalCoordinate_spec : ∀ v,Nonconstant v →
    ∀ x,v x=if v (exceptionalCoordinate v) then
      unitBit (exceptionalCoordinate v) x else !(unitBit (exceptionalCoordinate v) x) := by
  decide

def threeRows (complement : Bool) (p : Equiv.Perm (Fin 3)) (j : Fin 3) : Row :=
  fun x => if complement then !(unitBit (p j) x) else unitBit (p j) x

theorem threeRows_nonconstant (complement : Bool) (p : Equiv.Perm (Fin 3))
    (j : Fin 3) : Nonconstant (threeRows complement p j) := by
  have h : ∀ (complement : Bool) (i : Fin 3),Nonconstant
      (fun x => if complement then !(unitBit i x) else unitBit i x) := by decide
  exact h complement (p j)

/-- Any prescribed nonconstant incoming row can occupy any of the three
branch positions. The other rows have the same unit/complement type. -/
theorem threeRows_extend (j : Fin 3) (v : Row) (hv : Nonconstant v) :
    ∃ complement p,threeRows complement p j=v := by
  let i := exceptionalCoordinate v
  refine ⟨!(v i),Equiv.swap j i,?_⟩
  funext x
  rw [exceptionalCoordinate_spec v hv x]
  simp only [threeRows,Equiv.swap_apply_left]
  change (if !(v i) then !(unitBit i x) else unitBit i x)=
    (if v i then unitBit i x else !(unitBit i x))
  cases v i <;> rfl

theorem weighted_unit_row (p : Equiv.Perm (Fin 3)) (lam : Fin 3 → ℝ) (j : Fin 3) :
    (∑ i,lam i*realBit (unitBit (p i) (p j)))=lam j := by
  rw [sum_eq_single j]
  · simp [unitBit,realBit]
  · intro i hi hij
    have he : p j≠ p i := fun he => hij (p.injective he.symm)
    simp [unitBit,realBit,he]
  · intro hj
    exact False.elim (hj (mem_univ j))

theorem realBit_not (b : Bool) : realBit (!b)=1-realBit b := by
  cases b <;> norm_num [realBit]

theorem weighted_threeRows_at (complement : Bool) (p : Equiv.Perm (Fin 3))
    (lam : Fin 3 → ℝ) (j : Fin 3) :
    (∑ i,lam i*realBit (threeRows complement p i (p j)))=
      if complement then (∑ i,lam i)-lam j else lam j := by
  cases complement
  · simpa only [threeRows,Bool.false_eq_true,ite_false] using weighted_unit_row p lam j
  · simp only [threeRows,ite_true,realBit_not,mul_sub,mul_one]
    rw [sum_sub_distrib,weighted_unit_row]

/-- The quotient response relation is exactly one-dimensional. No
positivity or prior common-scale hypothesis is used to recover the scales. -/
theorem threeRows_relation_kernel (complement : Bool) (p : Equiv.Perm (Fin 3))
    (lam : Fin 3 → ℝ) (d : ℝ)
    (h : ∀ x,(∑ i,lam i*realBit (threeRows complement p i x))=d) :
    (∀ i,lam i=lam 0) ∧ d=(if complement then 2 else 1)*lam 0 := by
  have he : ∀ j,(if complement then (∑ i,lam i)-lam j else lam j)=d := by
    intro j
    rw [← weighted_threeRows_at]
    exact h (p j)
  have hs : ∀ j,lam j=lam 0 := by
    intro j
    have h0 := he 0
    have hj := he j
    cases complement <;> simp only [Bool.false_eq_true,ite_false,ite_true] at h0 hj <;>
      linarith
  refine ⟨hs,?_⟩
  have h0 := he 0
  have hsum : (∑ i,lam i)=3*lam 0 := by
    simp only [hs,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    norm_num
  rw [hsum] at h0
  cases complement <;> simp only [Bool.false_eq_true,ite_false,ite_true] at h0 ⊢ <;>
    linarith

theorem threeRows_sum (complement : Bool) (p : Equiv.Perm (Fin 3)) (x : Fin 3) :
    (∑ i,realBit (threeRows complement p i x))=if complement then 2 else 1 := by
  have h := weighted_threeRows_at complement p (fun _ => 1) (p.symm x)
  have hsum : (∑ _ : Fin 3,(1:ℝ))=3 := by norm_num
  rw [hsum] at h
  simpa only [Equiv.apply_symm_apply,one_mul,show (3:ℝ)-1=2 by norm_num] using h

def twoRows (v : Row) : Fin 2 → Row := ![v,fun x => !(v x)]

theorem twoRows_nonconstant : ∀ v,Nonconstant v → ∀ j,Nonconstant (twoRows v j) := by
  decide

theorem twoRows_sum (v : Row) (x : Fin 3) :
    (∑ i,realBit (twoRows v i x))=1 := by
  rw [Fin.sum_univ_two]
  change realBit (v x) + realBit (!(v x)) = 1
  cases v x <;> norm_num [realBit]

theorem twoRows_relation_kernel (v : Row) (hv : Nonconstant v)
    (lam : Fin 2 → ℝ) (d : ℝ)
    (h : ∀ x,(∑ i,lam i*realBit (twoRows v i x))=d) :
    lam 0=lam 1 ∧ d=lam 0 := by
  obtain ⟨⟨i,hi⟩,⟨j,hj⟩⟩ := hv
  have h0 := h i
  have h1 := h j
  simp [twoRows,Fin.sum_univ_two,hi,hj,realBit] at h0 h1
  exact ⟨by linarith,by linarith⟩

end RootedResponse
end GraphicalZonotopes

end
end BundlePart60

section BundlePart61
/- Source: Papers/GraphicalZonotopes/TriangleState.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace RootedResponse
open Finset
open scoped BigOperators
variable {J T J' T' : Type*} [Fintype J] [Fintype T] [Fintype J'] [Fintype T']

abbrev NonconstantBits (v : T → Bool) : Prop := (∃ x,v x=false) ∧ (∃ x,v x=true)

theorem nonconstantBits_comp (e : T' ≃ T) (v : T → Bool) :
    NonconstantBits (fun x => v (e x)) ↔ NonconstantBits v := by
  constructor
  · rintro ⟨⟨x,hx⟩,⟨y,hy⟩⟩
    exact ⟨⟨e x,hx⟩,⟨e y,hy⟩⟩
  · rintro ⟨⟨x,hx⟩,⟨y,hy⟩⟩
    exact ⟨⟨e.symm x,by simpa using hx⟩,⟨e.symm y,by simpa using hy⟩⟩

/-- Complete local data at an internal triangle: nonconstant incident
rows, constant column sum one or two, and the full real response-kernel
condition forcing all incident clique scales to agree. -/
structure TriangleState (J T : Type*) [Fintype J] where
  row : J → T → Bool
  degree : ℕ
  degree_mem : degree=1 ∨ degree=2
  nonconstant : ∀ j,NonconstantBits (row j)
  sum_row : ∀ x,(∑ j,realBit (row j x))=(degree : ℝ)
  kernel : ∀ (lam : J → ℝ) (d : ℝ),
    (∀ x,(∑ j,lam j*realBit (row j x))=d) → ∀ i j,lam i=lam j

def TriangleState.relabel (s : TriangleState J T) (e : J' ≃ J) (f : T' ≃ T) :
    TriangleState J' T' where
  row j x := s.row (e j) (f x)
  degree := s.degree
  degree_mem := s.degree_mem
  nonconstant j := (nonconstantBits_comp f _).mpr (s.nonconstant (e j))
  sum_row x := by
    rw [Equiv.sum_comp e (fun j => realBit (s.row j (f x)))]
    exact s.sum_row (f x)
  kernel lam d h i j := by
    let μ : J → ℝ := fun k => lam (e.symm k)
    have hμ : ∀ x,(∑ k,μ k*realBit (s.row k x))=d := by
      intro x
      have hx := h (f.symm x)
      simp only [Equiv.apply_symm_apply] at hx
      rw [← Equiv.sum_comp e (fun k => μ k*realBit (s.row k x))]
      simpa only [μ,Equiv.symm_apply_apply] using hx
    simpa only [μ,Equiv.symm_apply_apply] using s.kernel μ d hμ (e i) (e j)

def threeState (complement : Bool) (p : Equiv.Perm (Fin 3)) :
    TriangleState (Fin 3) (Fin 3) where
  row := threeRows complement p
  degree := if complement then 2 else 1
  degree_mem := by cases complement <;> simp
  nonconstant := threeRows_nonconstant complement p
  sum_row x := by
    cases complement
    · simpa only [Bool.false_eq_true, ite_false, Nat.cast_one] using threeRows_sum false p x
    · simpa only [ite_true, Nat.cast_ofNat] using threeRows_sum true p x
  kernel lam d h i j :=
    (threeRows_relation_kernel complement p lam d h).1 i |>.trans
      ((threeRows_relation_kernel complement p lam d h).1 j).symm

def twoState (v : Row) (hv : Nonconstant v) : TriangleState (Fin 2) (Fin 3) where
  row := twoRows v
  degree := 1
  degree_mem := Or.inl rfl
  nonconstant := twoRows_nonconstant v hv
  sum_row x := by simpa only [Nat.cast_one] using twoRows_sum v x
  kernel lam d h i j := by
    have he := (twoRows_relation_kernel v hv lam d h).1
    fin_cases i <;> fin_cases j
    · rfl
    · exact he
    · exact he.symm
    · rfl

def twoInput (j : Fin 2) (v : Row) : Row := if j=0 then v else fun x => !(v x)

theorem twoInput_nonconstant : ∀ j v,Nonconstant v → Nonconstant (twoInput j v) := by
  decide

theorem twoInput_port : ∀ j v,twoRows (twoInput j v) j=v := by decide

theorem triangleState_extend (hT : Fintype.card T=3)
    (hJ : Fintype.card J=2 ∨ Fintype.card J=3) (j : J)
    (v : T → Bool) (hv : NonconstantBits v) :
    ∃ s : TriangleState J T,s.row j=v := by
  classical
  let f := Fintype.equivFinOfCardEq hT
  let input : Row := fun x => v (f.symm x)
  have hin : Nonconstant input := (nonconstantBits_comp f.symm v).mpr hv
  rcases hJ with hJ | hJ
  · let e := Fintype.equivFinOfCardEq hJ
    let s := twoState (twoInput (e j) input) (twoInput_nonconstant _ _ hin)
    refine ⟨s.relabel e f,?_⟩
    funext x
    change twoRows (twoInput (e j) input) (e j) (f x)=v x
    rw [twoInput_port]
    exact congrArg v (f.symm_apply_apply x)
  · let e := Fintype.equivFinOfCardEq hJ
    obtain ⟨complement,p,hport⟩ := threeRows_extend (e j) input hin
    refine ⟨(threeState complement p).relabel e f,?_⟩
    funext x
    change threeRows complement p (e j) (f x)=v x
    rw [hport]
    exact congrArg v (f.symm_apply_apply x)

theorem triangleState_nonempty (hT : Fintype.card T=3)
    (hJ : Fintype.card J=2 ∨ Fintype.card J=3) :
    Nonempty (TriangleState J T) := by
  classical
  have hpos : 0< Fintype.card J := by rcases hJ with hJ | hJ <;> omega
  letI : Nonempty J := Fintype.card_pos_iff.mp hpos
  let f := Fintype.equivFinOfCardEq hT
  let input : T → Bool := fun x => unitBit 0 (f x)
  have hv : NonconstantBits input := (nonconstantBits_comp f (unitBit 0)).mpr ⟨⟨1, rfl⟩, ⟨0, rfl⟩⟩
  obtain ⟨s,hs⟩ := triangleState_extend hT hJ (Classical.arbitrary J) input hv
  exact ⟨s⟩

end RootedResponse
end GraphicalZonotopes

end
end
end BundlePart61

section BundlePart62
/- Source: Papers/GraphicalZonotopes/TreeCompatibility.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
universe u v w

/-- A finite tree of nonempty local state spaces has compatible states if
every state at one end of an edge can be matched at the other end. There
are no compatibility conditions on nonedges and no chosen-root hypothesis.
This is the exact finite constraint-tree gluing step needed for the bit-row
construction, independent of its geometric application. -/
theorem tree_compatible_states {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsTree) (State : V → Type v)
    (hne : ∀ v,Nonempty (State v)) (Color : Type w)
    (port : ∀ u v,State u → Color)
    (hextend : ∀ u v,G.Adj u v → ∀ t : State v,
      ∃ s : State u,port u v s=port v u t) :
    ∃ s : ∀ v,State v,∀ u v,G.Adj u v → port u v (s u)=port v u (s v) := by
  classical
  suffices h : ∀ n,∀ (W : Type u) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W),Fintype.card W=n → H.IsTree →
      ∀ (S : W → Type v),(∀ v,Nonempty (S v)) →
      ∀ (p : ∀ u v,S u → Color),
      (∀ u v,H.Adj u v → ∀ t : S v,∃ s : S u,p u v s=p v u t) →
      ∃ s : ∀ v,S v,∀ u v,H.Adj u v → p u v (s u)=p v u (s v) from
    h _ V G rfl hG State hne port hextend
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ _ H hcard htree S hne p hextend
    by_cases hsub : Subsingleton W
    · letI : Subsingleton W := hsub
      refine ⟨fun v => Classical.choice (hne v),?_⟩
      intro u v huv
      exact False.elim (huv.ne (Subsingleton.elim u v))
    · letI : Nontrivial W := not_subsingleton_iff_nontrivial.mp hsub
      obtain ⟨r,hdeg⟩ := htree.exists_vert_degree_one_of_nontrivial
      obtain ⟨q,hrq,hunique⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg
      let W' := {x : W // x≠ r}
      let H' : SimpleGraph W' := H.induce {r}ᶜ
      have htree' : H'.IsTree :=
        ⟨htree.connected.induce_compl_singleton_of_degree_eq_one hdeg,
          htree.isAcyclic.induce _⟩
      have hlt : Fintype.card W'< n := by
        rw [← hcard]
        exact Fintype.card_subtype_lt (x:=r) (by simp)
      obtain ⟨s,hs⟩ := ih (Fintype.card W') hlt W' H' rfl htree'
        (fun v => S v.1) (fun v => hne v.1) (fun u v => p u.1 v.1)
        (fun u v huv t => hextend u.1 v.1 huv t)
      have hqr : q≠ r := hrq.ne.symm
      obtain ⟨sr,hsr⟩ := hextend r q hrq (s ⟨q,hqr⟩)
      let t : ∀ x,S x := fun x =>
        if hx : x=r then hx.symm ▸ sr else s ⟨x,hx⟩
      have htroot : t r=sr := by simp only [t,dif_pos rfl]
      have htoff : ∀ x (hx : x≠ r),t x=s ⟨x,hx⟩ := by
        intro x hx
        simp only [t,dif_neg hx]
      refine ⟨t,?_⟩
      intro u v huv
      by_cases hur : u=r
      · subst u
        have hvq : v=q := hunique v huv
        subst v
        rw [htroot,htoff q hqr]
        exact hsr
      · by_cases hvr : v=r
        · subst v
          have huq : u=q := hunique u huv.symm
          subst u
          rw [htroot,htoff q hqr]
          exact hsr.symm
        · rw [htoff u hur,htoff v hvr]
          exact hs ⟨u,hur⟩ ⟨v,hvr⟩ huv

end GraphicalZonotopes

end
end
end BundlePart62

section BundlePart63
/- Source: Papers/GraphicalZonotopes/ThreeTreeStates.lean -/








@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ThreeTreeStates
open Finset
open RootedResponse
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_opposite {C T : Finset V} (hC : C.card=4) (hT : T.card=3)
    (hTC : T⊆C) : ∃ r : ↥C,C.erase r.1=T := by
  have hcard : (C\T).card=1 := by rw [card_sdiff_of_subset hTC,hC,hT]
  obtain ⟨r,hr⟩ := card_eq_one.mp hcard
  have hrmem : r∈C\T := by rw [hr]; simp
  obtain ⟨hrC,hrT⟩ := mem_sdiff.mp hrmem
  refine ⟨⟨r,hrC⟩,?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨hxr,hxC⟩ := mem_erase.mp hx
    by_contra hxT
    have hxs : x∈C\T := mem_sdiff.mpr ⟨hxC,hxT⟩
    rw [hr,mem_singleton] at hxs
    exact hxr hxs
  · intro hxT
    exact mem_erase.mpr ⟨fun hxr => hrT (by simpa only [hxr] using hxT),hTC hxT⟩

def opposite (G : SimpleGraph V) (C : ↥(tetrahedra G)) (T : ↥(internalTriangles G))
    (hTC : T.1⊆C.1) : ↥C.1 :=
  Classical.choose (exists_opposite (mem_filter.mp C.2).2.1
    (mem_triangles.mp (mem_internalTriangles.mp T.2).1).1 hTC)

theorem opposite_spec (G : SimpleGraph V) (C : ↥(tetrahedra G))
    (T : ↥(internalTriangles G)) (hTC : T.1⊆C.1) :
    C.1.erase (opposite G C T hTC).1=T.1 :=
  Classical.choose_spec (exists_opposite (mem_filter.mp C.2).2.1
    (mem_triangles.mp (mem_internalTriangles.mp T.2).1).1 hTC)

theorem opposite_notMem (G : SimpleGraph V) (C : ↥(tetrahedra G))
    (T : ↥(internalTriangles G)) (hTC : T.1⊆C.1) :
    (opposite G C T hTC).1∉T.1 := by
  rw [← opposite_spec G C T hTC]
  exact notMem_erase _ _

abbrev CliqueState (G : SimpleGraph V) (C : ↥(tetrahedra G)) :=
  FourState (fun p : ↥C.1 => C.1.erase p.1∈internalTriangles G)

abbrev IncidentClique (G : SimpleGraph V) (T : ↥(internalTriangles G)) :=
  {C : ↥(tetrahedra G) // T.1⊆C.1}

abbrev TriangleLocalState (G : SimpleGraph V) (T : ↥(internalTriangles G)) :=
  TriangleState (IncidentClique G T) ↥T.1

def cliquePort (G : SimpleGraph V) (C : ↥(tetrahedra G))
    (T : ↥(internalTriangles G)) (hTC : T.1⊆C.1) (s : CliqueState G C) : ↥T.1 → Bool :=
  fun j => s.row (opposite G C T hTC) ⟨j.1,hTC j.2⟩

theorem cliquePort_nonconstant (G : SimpleGraph V) (C : ↥(tetrahedra G))
    (T : ↥(internalTriangles G)) (hTC : T.1⊆C.1) (s : CliqueState G C) :
    NonconstantBits (cliquePort G C T hTC s) := by
  let p := opposite G C T hTC
  have hp : C.1.erase p.1∈internalTriangles G := by
    rw [opposite_spec G C T hTC]
    exact T.2
  obtain ⟨⟨j,hjp,hj⟩,⟨k,hkp,hk⟩⟩ := s.nonconstant p hp
  have hjT : j.1∈T.1 := by
    rw [← opposite_spec G C T hTC]
    exact mem_erase.mpr ⟨fun he => hjp (Subtype.ext he),j.2⟩
  have hkT : k.1∈T.1 := by
    rw [← opposite_spec G C T hTC]
    exact mem_erase.mpr ⟨fun he => hkp (Subtype.ext he),k.2⟩
  exact ⟨⟨⟨j.1,hjT⟩,hj⟩,⟨⟨k.1,hkT⟩,hk⟩⟩

theorem cliqueState_extend (G : SimpleGraph V) (C : ↥(tetrahedra G))
    (T : ↥(internalTriangles G)) (hTC : T.1⊆C.1)
    (v : ↥T.1 → Bool) (hv : NonconstantBits v) :
    ∃ s : CliqueState G C,cliquePort G C T hTC s=v := by
  classical
  let p := opposite G C T hTC
  let input : ↥C.1 → Bool := fun j => if hj : j.1∈T.1 then v ⟨j.1,hj⟩ else false
  have hp : C.1.erase p.1∈internalTriangles G := by
    rw [opposite_spec G C T hTC]
    exact T.2
  have hnot := opposite_notMem G C T hTC
  have hin : NonconstantAt input p := by
    obtain ⟨⟨j,hj⟩,⟨k,hk⟩⟩ := hv
    refine ⟨⟨⟨j.1,hTC j.2⟩,?_,?_⟩,⟨⟨k.1,hTC k.2⟩,?_,?_⟩⟩
    · intro he
      exact hnot ((congrArg Subtype.val he) ▸ j.2)
    · simpa only [input,dif_pos j.2] using hj
    · intro he
      exact hnot ((congrArg Subtype.val he) ▸ k.2)
    · simpa only [input,dif_pos k.2] using hk
  have hc : Fintype.card ↥C.1=4 := by
    rw [Fintype.card_coe]
    exact (mem_filter.mp C.2).2.1
  obtain ⟨s,hs⟩ := fourState_extend hc
    (fun q : ↥C.1 => C.1.erase q.1∈internalTriangles G) p hp input hin
  refine ⟨s,?_⟩
  funext j
  have hjp : (⟨j.1,hTC j.2⟩ : ↥C.1)≠ p := by
    intro he
    exact hnot ((congrArg Subtype.val he) ▸ j.2)
  change s.row p ⟨j.1,hTC j.2⟩=v j
  rw [hs _ hjp]
  simp only [input,dif_pos j.2]

def incidentCliqueEquiv (G : SimpleGraph V) (T : ↥(internalTriangles G)) :
    IncidentClique G T ≃ ↥((tetrahedra G).filter (fun C => T.1⊆C)) where
  toFun C := ⟨C.1.1,mem_filter.mpr ⟨C.1.2,C.2⟩⟩
  invFun C := ⟨⟨C.1,(mem_filter.mp C.2).1⟩,(mem_filter.mp C.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem incidentClique_card (G : SimpleGraph V) (T : ↥(internalTriangles G)) :
    Fintype.card (IncidentClique G T)=triangleMultiplicity G T.1 := by
  classical
  rw [Fintype.card_congr (incidentCliqueEquiv G T),Fintype.card_coe]
  rfl

theorem incidentClique_card_two_or_three (G : SimpleGraph V) (hG : Admissible G)
    (T : ↥(internalTriangles G)) :
    Fintype.card (IncidentClique G T)=2 ∨ Fintype.card (IncidentClique G T)=3 := by
  obtain ⟨hT,hlo⟩ := mem_internalTriangles.mp T.2
  obtain ⟨hc,hcl⟩ := mem_triangles.mp hT
  have hhi := hG T.1 hc hcl
  rw [incidentClique_card]
  omega

def LocalState (G : SimpleGraph V) : InternalIncidenceNode G → Type _
  | Sum.inl C => CliqueState G C
  | Sum.inr T => TriangleLocalState G T

abbrev PortColor (G : SimpleGraph V) := Option (Σ T : ↥(internalTriangles G),↥T.1 → Bool)

def localPort (G : SimpleGraph V) (x y : InternalIncidenceNode G) :
    LocalState G x → PortColor G :=
  match x,y with
  | Sum.inl C,Sum.inr T => fun s =>
      if hTC : T.1⊆C.1 then some ⟨T,cliquePort G C T hTC s⟩ else none
  | Sum.inr T,Sum.inl C => fun s =>
      if hTC : T.1⊆C.1 then some ⟨T,s.row ⟨C,hTC⟩⟩ else none
  | _,_ => fun _ => none

theorem localState_nonempty (G : SimpleGraph V) (hG : Admissible G)
    (N : InternalIncidenceNode G) : Nonempty (LocalState G N) := by
  classical
  cases N with
  | inl C =>
    exact fourState_nonempty (by
      rw [Fintype.card_coe]
      exact (mem_filter.mp C.2).2.1) _
  | inr T =>
    exact triangleState_nonempty (by
      rw [Fintype.card_coe]
      exact (mem_triangles.mp (mem_internalTriangles.mp T.2).1).1)
      (incidentClique_card_two_or_three G hG T)

theorem localState_matching (G : SimpleGraph V) (hG : Admissible G)
    (x y : InternalIncidenceNode G) (hxy : (internalIncidence G).Adj x y)
    (t : LocalState G y) :
    ∃ s : LocalState G x,localPort G x y s=localPort G y x t := by
  classical
  cases x with
  | inl C =>
    cases y with
    | inl D => exact False.elim hxy
    | inr T =>
      have hTC : T.1⊆C.1 := hxy
      obtain ⟨s,hs⟩ := cliqueState_extend G C T hTC (t.row ⟨C,hTC⟩)
        (t.nonconstant ⟨C,hTC⟩)
      exact ⟨s,by simp only [localPort,dif_pos hTC,hs]⟩
  | inr T =>
    cases y with
    | inr U => exact False.elim hxy
    | inl C =>
      have hTC : T.1⊆C.1 := hxy
      obtain ⟨s,hs⟩ := triangleState_extend (by
        rw [Fintype.card_coe]
        exact (mem_triangles.mp (mem_internalTriangles.mp T.2).1).1)
        (incidentClique_card_two_or_three G hG T) (⟨C,hTC⟩ : IncidentClique G T)
        (cliquePort G C T hTC t) (cliquePort_nonconstant G C T hTC t)
      exact ⟨s,by simp only [localPort,dif_pos hTC,hs]⟩

/-- Actual compatible rows on every clique and every internal triangle,
including the one-dimensional real relation at each triangle. -/
structure CompatibleRows (G : SimpleGraph V) where
  clique : ∀ C : ↥(tetrahedra G),CliqueState G C
  triangle : ∀ T : ↥(internalTriangles G),TriangleLocalState G T
  port_eq : ∀ (C : ↥(tetrahedra G)) (T : ↥(internalTriangles G)) (hTC : T.1⊆C.1),
    cliquePort G C T hTC (clique C)=(triangle T).row ⟨C,hTC⟩

theorem compatibleRows_exists {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (hG : Admissible G) : Nonempty (CompatibleRows G) := by
  classical
  obtain ⟨s,hs⟩ := tree_compatible_states (internalIncidence G) h.internalIncidence_isTree
    (LocalState G) (localState_nonempty G hG) (PortColor G) (localPort G)
    (localState_matching G hG)
  refine ⟨{
    clique := fun C => s (Sum.inl C)
    triangle := fun T => s (Sum.inr T)
    port_eq := ?_ }⟩
  intro C T hTC
  have he := hs (Sum.inl C) (Sum.inr T) hTC
  simp only [localPort,dif_pos hTC] at he
  exact sigma_mk_injective (Option.some.inj he)

end ThreeTreeStates
end GraphicalZonotopes

end
end
end BundlePart63

section BundlePart64
/- Source: Papers/GraphicalZonotopes/ThreeTreeColumns.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ThreeTreeStates
open Finset
open RootedResponse
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev AllIncidentClique (G : SimpleGraph V) (T : ↥(triangles G)) :=
  {C : ↥(tetrahedra G) // T.1⊆C.1}

def faceMissing (G : SimpleGraph V) (C : ↥(tetrahedra G)) (T : ↥(triangles G))
    (hTC : T.1⊆C.1) : ↥C.1 :=
  Classical.choose (exists_opposite (mem_filter.mp C.2).2.1 (mem_triangles.mp T.2).1 hTC)

theorem faceMissing_spec (G : SimpleGraph V) (C : ↥(tetrahedra G))
    (T : ↥(triangles G)) (hTC : T.1⊆C.1) :
    C.1.erase (faceMissing G C T hTC).1=T.1 :=
  Classical.choose_spec (exists_opposite (mem_filter.mp C.2).2.1
    (mem_triangles.mp T.2).1 hTC)

theorem faceMissing_notMem (G : SimpleGraph V) (C : ↥(tetrahedra G))
    (T : ↥(triangles G)) (hTC : T.1⊆C.1) :
    (faceMissing G C T hTC).1∉T.1 := by
  rw [← faceMissing_spec G C T hTC]
  exact notMem_erase _ _

def faceRow (G : SimpleGraph V) (s : CompatibleRows G)
    (T : ↥(triangles G)) (C : AllIncidentClique G T) (j : ↥T.1) : Bool :=
  (s.clique C.1).row (faceMissing G C.1 T C.2) ⟨j.1,C.2 j.2⟩

def columnValue (G : SimpleGraph V) (s : CompatibleRows G)
    (T : ↥(triangles G)) (j : ↥T.1) : ℝ :=
  ∑ C : AllIncidentClique G T,realBit (faceRow G s T C j)

def allIncidentCliqueEquiv (G : SimpleGraph V) (T : ↥(triangles G)) :
    AllIncidentClique G T ≃ ↥((tetrahedra G).filter (fun C => T.1⊆C)) where
  toFun C := ⟨C.1.1,mem_filter.mpr ⟨C.1.2,C.2⟩⟩
  invFun C := ⟨⟨C.1,(mem_filter.mp C.2).1⟩,(mem_filter.mp C.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem allIncidentClique_card (G : SimpleGraph V) (T : ↥(triangles G)) :
    Fintype.card (AllIncidentClique G T)=triangleMultiplicity G T.1 := by
  classical
  rw [Fintype.card_congr (allIncidentCliqueEquiv G T),Fintype.card_coe]
  rfl

theorem internal_column (G : SimpleGraph V) (s : CompatibleRows G)
    (T : ↥(triangles G)) (hT : T.1∈internalTriangles G) (j : ↥T.1) :
    columnValue G s T j=((s.triangle ⟨T.1,hT⟩).degree : ℝ) := by
  let T' : ↥(internalTriangles G) := ⟨T.1,hT⟩
  have he : ∀ C : AllIncidentClique G T,
      faceRow G s T C j=(s.triangle T').row C j := by
    intro C
    exact congrArg (fun f : ↥T.1 → Bool => f j) (s.port_eq C.1 T' C.2)
  unfold columnValue
  simp_rw [he]
  exact (s.triangle T').sum_row j

/-- The column sums on every actual triangle, including the leaf
triangles, are constants in {0,1,2}. The leaf case is proved from its actual
single incident tetrahedron, rather than assigned an unproved response. -/
theorem column_constant {S : Finset V} {G : SimpleGraph V} (h : ThreeTreeOn S G)
    (s : CompatibleRows G) (T : ↥(triangles G)) :
    ∃ d : ℕ,(d=0 ∨ d=1 ∨ d=2) ∧ ∀ j : ↥T.1,columnValue G s T j=(d : ℝ) := by
  classical
  by_cases hT : T.1∈internalTriangles G
  · refine ⟨(s.triangle ⟨T.1,hT⟩).degree,?_,internal_column G s T hT⟩
    exact Or.inr (s.triangle ⟨T.1,hT⟩).degree_mem
  · have htri := mem_triangles.mp T.2
    obtain ⟨C,hC,hTC⟩ := h.triangle_extends htri.1 htri.2
    have hpos : 0< triangleMultiplicity G T.1 := by
      apply card_pos.mpr
      exact ⟨C,mem_filter.mpr ⟨hC,hTC⟩⟩
    have hsmall : ¬2≤ triangleMultiplicity G T.1 := fun hcount =>
      hT (mem_internalTriangles.mpr ⟨T.2,hcount⟩)
    have hone : Fintype.card (AllIncidentClique G T)=1 := by
      rw [allIncidentClique_card]
      omega
    obtain ⟨C₀,hunique⟩ := Fintype.card_eq_one_iff.mp hone
    let p := faceMissing G C₀.1 T C₀.2
    have hleaf : C₀.1.1.erase p.1∉internalTriangles G := by
      rw [faceMissing_spec G C₀.1 T C₀.2]
      exact hT
    obtain ⟨b,hb⟩ := (s.clique C₀.1).constant p hleaf
    have hcol : ∀ j : ↥T.1,columnValue G s T j=realBit b := by
      intro j
      unfold columnValue
      rw [sum_eq_single C₀]
      · apply congrArg realBit
        apply hb
        intro he
        exact faceMissing_notMem G C₀.1 T C₀.2
          ((congrArg Subtype.val he) ▸ j.2)
      · intro D hD hne
        exact False.elim (hne (hunique D))
      · intro hn
        exact False.elim (hn (mem_univ C₀))
    cases hbval : b
    · exact ⟨0,Or.inl rfl,fun j => by simpa [hbval,realBit] using hcol j⟩
    · exact ⟨1,Or.inr (Or.inl rfl),fun j => by simpa [hbval,realBit] using hcol j⟩

def triangleWeight {S : Finset V} {G : SimpleGraph V} (h : ThreeTreeOn S G)
    (s : CompatibleRows G) (T : ↥(triangles G)) : ℕ :=
  Classical.choose (column_constant h s T)

theorem triangleWeight_mem {S : Finset V} {G : SimpleGraph V} (h : ThreeTreeOn S G)
    (s : CompatibleRows G) (T : ↥(triangles G)) :
    triangleWeight h s T=0 ∨ triangleWeight h s T=1 ∨ triangleWeight h s T=2 :=
  (Classical.choose_spec (column_constant h s T)).1

theorem column_eq_triangleWeight {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) (T : ↥(triangles G)) (j : ↥T.1) :
    columnValue G s T j=(triangleWeight h s T : ℝ) :=
  (Classical.choose_spec (column_constant h s T)).2 j

end ThreeTreeStates
end GraphicalZonotopes

end
end
end BundlePart64

section BundlePart65
/- Source: Papers/GraphicalZonotopes/EdgeCoordinates.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Unordered graph edges and two-element clique sets are exactly equivalent
coordinate systems, including their finite sums. -/
theorem sym2_toFinset_injective : Function.Injective (Sym2.toFinset : Sym2 V → Finset V) := by
  intro e f he
  apply Sym2.ext
  intro v
  apply Iff.of_eq
  simpa only [Sym2.mem_toFinset] using congrArg (fun C : Finset V => v∈C) he

theorem edgeFamily_eq_image_edgeFinset (G : SimpleGraph V) :
    edgeFamily G=G.edgeFinset.image Sym2.toFinset := by
  classical
  ext C
  constructor
  · intro hC
    obtain ⟨hc,hcl⟩ := (mem_edgeFamily G C).mp hC
    obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hc
    have hadj := (pair_mem_edgeFamily G hab).mp hC
    exact mem_image.mpr ⟨s(a,b),G.mem_edgeFinset.mpr hadj,Sym2.toFinset_mk_eq⟩
  · rintro hC
    obtain ⟨e,he,rfl⟩ := mem_image.mp hC
    obtain ⟨a,b⟩ := e
    rw [Sym2.toFinset_mk_eq]
    have hadj := G.mem_edgeFinset.mp he
    exact (pair_mem_edgeFamily G (G.ne_of_adj hadj)).mpr hadj

theorem sum_edgeFamily_eq (G : SimpleGraph V) (f : Finset V → ℝ) :
    (∑ C∈edgeFamily G,f C)=∑ e∈G.edgeFinset,f e.toFinset := by
  rw [edgeFamily_eq_image_edgeFinset,sum_image]
  exact fun e he d hd h => sym2_toFinset_injective h

end GraphicalZonotopes

end
end
end BundlePart65

section BundlePart66
/- Source: Papers/GraphicalZonotopes/TetrahedronPairWeights.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ThreeTreeStates
open Finset
open RootedResponse
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

structure ComplementPair (C E : Finset V) where
  first : ↥C
  second : ↥C
  ne : first≠ second
  erase_eq : (C.erase first.1).erase second.1=E

theorem complementPair_nonempty {C E : Finset V} (hC : C.card=4) (hE : E.card=2)
    (hEC : E⊆C) : Nonempty (ComplementPair C E) := by
  have hc : (C\E).card=2 := by rw [card_sdiff_of_subset hEC,hC,hE]
  obtain ⟨a,b,hab,he⟩ := card_eq_two.mp hc
  have ha : a∈C\E := by rw [he]; simp
  have hb : b∈C\E := by rw [he]; simp
  refine ⟨⟨⟨a,(mem_sdiff.mp ha).1⟩,⟨b,(mem_sdiff.mp hb).1⟩,
    (fun h => hab (congrArg Subtype.val h)),?_⟩⟩
  ext x
  constructor
  · intro hx
    obtain ⟨hxb,hx'⟩ := mem_erase.mp hx
    obtain ⟨hxa,hxC⟩ := mem_erase.mp hx'
    by_contra hxE
    have hm : x∈C\E := mem_sdiff.mpr ⟨hxC,hxE⟩
    rw [he,mem_insert,mem_singleton] at hm
    exact hm.elim hxa hxb
  · intro hxE
    refine mem_erase.mpr ⟨?_,mem_erase.mpr ⟨?_,hEC hxE⟩⟩
    · intro hxb
      exact (mem_sdiff.mp hb).2 (by simpa only [hxb] using hxE)
    · intro hxa
      exact (mem_sdiff.mp ha).2 (by simpa only [hxa] using hxE)

def complementPair (G : SimpleGraph V) (C : ↥(tetrahedra G)) (E : Finset V)
    (hE : E.card=2) (hEC : E⊆C.1) : ComplementPair C.1 E :=
  Classical.choice (complementPair_nonempty (mem_filter.mp C.2).2.1 hE hEC)

theorem ComplementPair.pair_eq_complement {C E : Finset V} (p : ComplementPair C E) :
    ({p.first.1,p.second.1} : Finset V)=C\E := by
  conv_rhs => rw [← p.erase_eq]
  ext x
  by_cases hxa : x=p.first.1 <;> by_cases hxb : x=p.second.1 <;>
    simp [hxa,hxb,p.first.2,p.second.2]

theorem ComplementPair.unordered_eq {C E : Finset V} (p q : ComplementPair C E) :
    s(p.first.1,p.second.1)=s(q.first.1,q.second.1) := by
  apply sym2_toFinset_injective
  simp only [Sym2.toFinset_mk_eq,p.pair_eq_complement,q.pair_eq_complement]

def ComplementPair.maximum {C E : Finset V} (p : ComplementPair C E)
    (row : ↥C → ↥C → Bool) : ℤ :=
  max (RootedResponse.integerBit (row p.first p.second)) (RootedResponse.integerBit (row p.second p.first))

theorem ComplementPair.maximum_eq {C E : Finset V} (p q : ComplementPair C E)
    (row : ↥C → ↥C → Bool) : p.maximum row=q.maximum row := by
  rcases Sym2.eq_iff.mp (p.unordered_eq q) with h | h
  · obtain ⟨ha,hb⟩ := h
    have ha' : p.first=q.first := Subtype.ext ha
    have hb' : p.second=q.second := Subtype.ext hb
    simp only [ComplementPair.maximum,ha',hb']
  · obtain ⟨ha,hb⟩ := h
    have ha' : p.first=q.second := Subtype.ext ha
    have hb' : p.second=q.first := Subtype.ext hb
    simp only [ComplementPair.maximum,ha',hb',max_comm]

theorem ComplementPair.maximum_zero_or_one {C E : Finset V}
    (p : ComplementPair C E) (row : ↥C → ↥C → Bool) :
    p.maximum row=0 ∨ p.maximum row=1 := by
  unfold ComplementPair.maximum
  cases row p.first p.second <;> cases row p.second p.first <;> norm_num [RootedResponse.integerBit]

abbrev IncidentPairClique (G : SimpleGraph V) (E : Finset V) :=
  {C : ↥(tetrahedra G) // E⊆C.1}

def pairWeight (G : SimpleGraph V) (s : CompatibleRows G) (E : Finset V)
    (hE : E.card=2) : ℤ :=
  ∑ C : IncidentPairClique G E,
    (complementPair G C.1 E hE C.2).maximum (s.clique C.1).row

theorem pairWeight_nonneg (G : SimpleGraph V) (s : CompatibleRows G)
    (E : Finset V) (hE : E.card=2) : 0≤ pairWeight G s E hE := by
  apply sum_nonneg
  intro C hC
  rcases (complementPair G C.1 E hE C.2).maximum_zero_or_one (s.clique C.1).row with h | h <;>
    simp [h]

theorem pairWeight_le_incident (G : SimpleGraph V) (s : CompatibleRows G)
    (E : Finset V) (hE : E.card=2) :
    pairWeight G s E hE≤(Fintype.card (IncidentPairClique G E) : ℤ) := by
  calc
    pairWeight G s E hE≤∑ _ : IncidentPairClique G E,(1:ℤ) := by
      apply sum_le_sum
      intro C hC
      rcases (complementPair G C.1 E hE C.2).maximum_zero_or_one (s.clique C.1).row with h | h <;>
        simp [h]
    _=(Fintype.card (IncidentPairClique G E) : ℤ) := by simp

end ThreeTreeStates
end GraphicalZonotopes

end
end
end BundlePart66

section BundlePart67
/- Source: Papers/GraphicalZonotopes/ThreeTreeCoefficients.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ThreeTreeStates
open Finset
open RootedResponse
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual integral Möbius vector of the construction: every
tetrahedron has coefficient one, a triangle has the negative common column
sum, and an edge has the sum of its local maxima. All other coordinates
vanish, including the translation coordinates. -/
def coefficients {S : Finset V} {G : SimpleGraph V} (h : ThreeTreeOn S G)
    (s : CompatibleRows G) : SetFunction V := fun C =>
  if hC : C∈tetrahedra G then 1
  else if hT : C∈triangles G then -(triangleWeight h s ⟨C,hT⟩ : ℝ)
  else if hE : C∈edgeFamily G then (pairWeight G s C ((mem_edgeFamily G C).mp hE).1 : ℝ)
  else 0

theorem coefficients_tetrahedron {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {C : Finset V}
    (hC : C∈tetrahedra G) : coefficients h s C=1 := by
  simp only [coefficients,dif_pos hC]

theorem coefficients_triangle {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {T : Finset V}
    (hT : T∈triangles G) : coefficients h s T= -(triangleWeight h s ⟨T,hT⟩ : ℝ) := by
  have hnot : T∉tetrahedra G := by
    intro hm
    have h4 := (mem_filter.mp hm).2.1
    have h3 := (mem_triangles.mp hT).1
    omega
  simp only [coefficients,dif_neg hnot,dif_pos hT]

theorem coefficients_pair {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {E : Finset V}
    (hE : E∈edgeFamily G) :
    coefficients h s E=(pairWeight G s E ((mem_edgeFamily G E).mp hE).1 : ℝ) := by
  have h2 := ((mem_edgeFamily G E).mp hE).1
  have hnot4 : E∉tetrahedra G := by
    intro hm
    have h4 := (mem_filter.mp hm).2.1
    omega
  have hnot3 : E∉triangles G := by
    intro hm
    have h3 := (mem_triangles.mp hm).1
    omega
  simp only [coefficients,dif_neg hnot4,dif_neg hnot3,dif_pos hE]

theorem coefficients_triangle_values {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {T : Finset V}
    (hT : T∈triangles G) :
    coefficients h s T=0 ∨ coefficients h s T= -1 ∨ coefficients h s T= -2 := by
  rw [coefficients_triangle h s hT]
  rcases triangleWeight_mem h s ⟨T,hT⟩ with hd | hd | hd <;> rw [hd] <;> norm_num

theorem coefficients_cliqueSupported {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) : CliqueSupported G (coefficients h s) := by
  classical
  refine ⟨?_,?_,?_⟩
  · simp [coefficients,tetrahedra,triangles,edgeFamily]
  · intro v
    simp [coefficients,tetrahedra,triangles,edgeFamily]
  · intro C u v hu hv huv hnon
    have h4 : C∉tetrahedra G := by
      intro hm
      exact hnon ((mem_filter.mp hm).2.2 hu hv huv)
    have h3 : C∉triangles G := by
      intro hm
      exact hnon ((mem_triangles.mp hm).2 hu hv huv)
    have h2 : C∉edgeFamily G := by
      intro hm
      exact hnon (((mem_edgeFamily G C).mp hm).2 u hu v hv huv)
    simp only [coefficients,dif_neg h4,dif_neg h3,dif_neg h2]

theorem coefficients_integerValued {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) : IntegerValued (coefficients h s) := by
  classical
  intro C
  unfold coefficients
  split
  · exact ⟨1,by norm_num⟩
  · split
    · rename_i hT
      exact ⟨-(triangleWeight h s ⟨C,hT⟩ : ℤ),by simp⟩
    · split
      · rename_i hE
        exact ⟨pairWeight G s C ((mem_edgeFamily G C).mp hE).1,rfl⟩
      · exact ⟨0,by norm_num⟩

def setFunction {S : Finset V} {G : SimpleGraph V} (h : ThreeTreeOn S G)
    (s : CompatibleRows G) : SetFunction V := zeta (coefficients h s)

theorem setFunction_normalized_graphical {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) :
    TranslationNormalized (setFunction h s) ∧ Graphical G (setFunction h s) :=
  (cliqueSupported_iff G _).mp (coefficients_cliqueSupported h s)

theorem setFunction_integerValued {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) : IntegerValued (setFunction h s) :=
  zeta_integerValued (coefficients_integerValued h s)

theorem setFunction_mobius {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) :
    mobius (setFunction h s)=coefficients h s := mobius_zeta _

theorem setFunction_ne_zero {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) : setFunction h s≠0 := by
  intro hz
  have hy : coefficients h s=0 := by
    apply zeta_injective
    rw [show zeta (coefficients h s)=0 from hz]
    ext C
    simp [zeta]
  obtain ⟨C,hC⟩ := h.tetrahedra_nonempty
  have he := coefficients_tetrahedron h s hC
  rw [hy] at he
  norm_num at he

end ThreeTreeStates
end GraphicalZonotopes

end
end
end BundlePart67

section BundlePart68
/- Source: Papers/GraphicalZonotopes/ThreeTreeLink.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The graph induced on the common neighbors of an edge, with all other
ambient vertices isolated. This ambient form avoids deleting any zero weights
when the link is used as a Boolean interaction graph. -/
def edgeLink (G : SimpleGraph V) (u v : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ G.Adj u a ∧ G.Adj v a ∧ G.Adj u b ∧ G.Adj v b
  symm := ⟨fun a b h => ⟨G.adj_symm h.1,h.2.2.2.1,h.2.2.2.2,h.2.1,h.2.2.1⟩⟩
  loopless := ⟨fun a h => G.irrefl h.1⟩

@[simp] theorem edgeLink_comm (G : SimpleGraph V) (u v : V) :
    edgeLink G u v=edgeLink G v u := by
  ext a b
  simp only [edgeLink]
  tauto

theorem isAcyclic_cliqueGraph_of_card_le_two {C : Finset V} (hC : C.card≤2) :
    (cliqueGraph C).IsAcyclic := by
  by_cases htwo : C.card=2
  · obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp htwo
    have he : cliqueGraph ({a,b} : Finset V)=SimpleGraph.edge a b := by
      ext x y
      simp only [cliqueGraph,mem_insert,mem_singleton,SimpleGraph.edge_adj]
      constructor
      · rintro ⟨hxy,hx,hy⟩
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact False.elim (hxy rfl)
        · exact ⟨Or.inl ⟨rfl,rfl⟩,hxy⟩
        · exact ⟨Or.inr ⟨rfl,rfl⟩,hxy⟩
        · exact False.elim (hxy rfl)
      · rintro ⟨hxy,hne⟩
        rcases hxy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [hab,Ne.symm hab]
    rw [he]
    have h := SimpleGraph.IsAcyclic.sup_edge_of_not_reachable
      (G:=(⊥ : SimpleGraph V)) (u:=a) (v:=b)
      (by simpa only [SimpleGraph.reachable_bot] using hab) SimpleGraph.isAcyclic_bot
    simpa only [bot_sup_eq] using h
  · have hone : C.card≤1 := by omega
    have he : cliqueGraph C=(⊥ : SimpleGraph V) := by
      ext a b
      simp only [SimpleGraph.bot_adj,iff_false]
      intro h
      exact h.1 ((card_le_one.mp hone) a h.2.1 b h.2.2)
    rw [he]
    exact SimpleGraph.isAcyclic_bot

theorem adj_before_attachment {G : SimpleGraph V} {w a b : V} {T : Finset V}
    (ha : a≠ w) (hb : b≠ w) (hab : (G⊔attachmentStar w T).Adj a b) : G.Adj a b := by
  rcases hab with h | h
  · exact h
  · rcases h.2 with ⟨he,_⟩ | ⟨he,_⟩
    · exact False.elim (ha he)
    · exact False.elim (hb he)

theorem edgeLink_new_le_clique {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {w : V} (hw : w∉S) {T : Finset V} (hTS : T⊆S)
    (v : V) : edgeLink (G⊔attachmentStar w T) w v≤ cliqueGraph (T.erase v) := by
  intro a b hab
  have ha := (attached_vertex_adj_iff h hw hTS a).mp hab.2.1
  have hb := (attached_vertex_adj_iff h hw hTS b).mp hab.2.2.2.1
  exact ⟨(G⊔attachmentStar w T).ne_of_adj hab.1,
    mem_erase.mpr ⟨Ne.symm ((G⊔attachmentStar w T).ne_of_adj hab.2.2.1),ha⟩,
    mem_erase.mpr ⟨Ne.symm ((G⊔attachmentStar w T).ne_of_adj hab.2.2.2.2),hb⟩⟩

theorem ThreeTreeOn.edgeLink_acyclic {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u v : V} (huv : G.Adj u v) :
    (edgeLink G u v).IsAcyclic := by
  induction h generalizing u v with
  | tetrahedron C hC =>
    have hu := huv.2.1
    have hv := huv.2.2
    have hne := huv.1
    have hcard : ((C.erase u).erase v).card≤2 := by
      rw [card_erase_of_mem (mem_erase.mpr ⟨Ne.symm hne,hv⟩),card_erase_of_mem hu,hC]
    apply (isAcyclic_cliqueGraph_of_card_le_two hcard).anti
    intro a b hab
    refine ⟨hab.1.1,?_,?_⟩
    · exact mem_erase.mpr ⟨Ne.symm hab.2.2.1.1,
        mem_erase.mpr ⟨Ne.symm hab.2.1.1,hab.1.2.1⟩⟩
    · exact mem_erase.mpr ⟨Ne.symm hab.2.2.2.2.1,
        mem_erase.mpr ⟨Ne.symm hab.2.2.2.1.1,hab.1.2.2⟩⟩
  | @attach S G h w hw T hT hTS hcl ih =>
    by_cases huw : u=w
    · subst u
      have hv := (attached_vertex_adj_iff h hw hTS v).mp huv
      apply (isAcyclic_cliqueGraph_of_card_le_two (C:=T.erase v) (by
        rw [card_erase_of_mem hv,hT])).anti
      exact edgeLink_new_le_clique h hw hTS v
    by_cases hvw : v=w
    · subst v
      rw [edgeLink_comm]
      have hu := (attached_vertex_adj_iff h hw hTS u).mp
        ((G⊔attachmentStar w T).adj_symm huv)
      apply (isAcyclic_cliqueGraph_of_card_le_two (C:=T.erase u) (by
        rw [card_erase_of_mem hu,hT])).anti
      exact edgeLink_new_le_clique h hw hTS u
    have hold := adj_before_attachment huw hvw huv
    have hi := ih (u:=u) (v:=v) hold
    by_cases hboth : u∈T ∧ v∈T
    · have hne : u≠ v := G.ne_of_adj hold
      have hcard : ((T.erase u).erase v).card=1 := by
        rw [card_erase_of_mem (mem_erase.mpr ⟨Ne.symm hne,hboth.2⟩),
          card_erase_of_mem hboth.1,hT]
      obtain ⟨r,hr⟩ := card_eq_one.mp hcard
      have hrmem : r∈(T.erase u).erase v := by rw [hr]; simp
      have hrT := mem_of_mem_erase (mem_of_mem_erase hrmem)
      have hrw : r≠ w := by intro he; subst r; exact hw (hTS hrT)
      have hnotreach : ¬(edgeLink G u v).Reachable w r := by
        intro hreach
        obtain ⟨x,hx⟩ := hreach.nonempty_neighborSet_left (Ne.symm hrw)
        exact hw (h.edges_supported hx.1).1
      have hforest := hi.sup_edge_of_not_reachable hnotreach
      apply hforest.anti
      intro a b hab
      by_cases haw : a=w
      · subst a
        right
        have hbT := (attached_vertex_adj_iff h hw hTS b).mp hab.1
        have hbu := Ne.symm ((G⊔attachmentStar w T).ne_of_adj hab.2.2.2.1)
        have hbv := Ne.symm ((G⊔attachmentStar w T).ne_of_adj hab.2.2.2.2)
        have hb : b∈(T.erase u).erase v := mem_erase.mpr ⟨hbv,mem_erase.mpr ⟨hbu,hbT⟩⟩
        rw [hr,mem_singleton] at hb
        subst b
        exact (SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,Ne.symm hrw⟩
      by_cases hbw : b=w
      · subst b
        right
        have haT := (attached_vertex_adj_iff h hw hTS a).mp
          ((G⊔attachmentStar w T).adj_symm hab.1)
        have hau := Ne.symm ((G⊔attachmentStar w T).ne_of_adj hab.2.1)
        have hav := Ne.symm ((G⊔attachmentStar w T).ne_of_adj hab.2.2.1)
        have ha : a∈(T.erase u).erase v := mem_erase.mpr ⟨hav,mem_erase.mpr ⟨hau,haT⟩⟩
        rw [hr,mem_singleton] at ha
        subst a
        exact (SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inr ⟨rfl,rfl⟩,hrw⟩
      exact Or.inl ⟨adj_before_attachment haw hbw hab.1,
        adj_before_attachment huw haw hab.2.1,
        adj_before_attachment hvw haw hab.2.2.1,
        adj_before_attachment huw hbw hab.2.2.2.1,
        adj_before_attachment hvw hbw hab.2.2.2.2⟩
    · apply hi.anti
      intro a b hab
      have haw : a≠ w := by
        intro he
        subst a
        exact hboth ⟨(attached_vertex_adj_iff h hw hTS u).mp
          ((G⊔attachmentStar w T).adj_symm hab.2.1),
          (attached_vertex_adj_iff h hw hTS v).mp
          ((G⊔attachmentStar w T).adj_symm hab.2.2.1)⟩
      have hbw : b≠ w := by
        intro he
        subst b
        exact hboth ⟨(attached_vertex_adj_iff h hw hTS u).mp
          ((G⊔attachmentStar w T).adj_symm hab.2.2.2.1),
          (attached_vertex_adj_iff h hw hTS v).mp
          ((G⊔attachmentStar w T).adj_symm hab.2.2.2.2)⟩
      exact ⟨adj_before_attachment haw hbw hab.1,
        adj_before_attachment huw haw hab.2.1,
        adj_before_attachment hvw haw hab.2.2.1,
        adj_before_attachment huw hbw hab.2.2.2.1,
        adj_before_attachment hvw hbw hab.2.2.2.2⟩

end GraphicalZonotopes

end
end
end BundlePart68

section BundlePart69
/- Source: Papers/GraphicalZonotopes/ForestSigns.lean -/








@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ForestSigns
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

def IsSign (x : ℝ) : Prop := x=1 ∨ x=-1

theorem IsSign.mul {x y : ℝ} (hx : IsSign x) (hy : IsSign y) : IsSign (x*y) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num [IsSign]

theorem IsSign.sq {x : ℝ} (hx : IsSign x) : x^2=1 := by
  rcases hx with rfl | rfl <;> norm_num

/-- Every assignment of signs to the edges of a finite forest is realized
as products of vertex signs. The proof deletes one bridge and flips precisely
one of its two components; it includes disconnected and empty forests. -/
theorem exists_vertex_signs (G : SimpleGraph V) (hG : G.IsAcyclic)
    (ρ : V → V → ℝ) (hρ : ∀ u v,G.Adj u v → IsSign (ρ u v))
    (hρsym : ∀ u v,G.Adj u v → ρ u v=ρ v u) :
    ∃ σ : V → ℝ,(∀ v,IsSign (σ v)) ∧ ∀ u v,G.Adj u v → σ u*σ v=ρ u v := by
  classical
  suffices h : ∀ n (H : SimpleGraph V),H.edgeFinset.card=n → H.IsAcyclic →
      (∀ u v,H.Adj u v → IsSign (ρ u v)) →
      (∀ u v,H.Adj u v → ρ u v=ρ v u) →
      ∃ σ : V → ℝ,(∀ v,IsSign (σ v)) ∧ ∀ u v,H.Adj u v → σ u*σ v=ρ u v from
    h _ G rfl hG hρ hρsym
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro H hcard hH hρ hρsym
    by_cases hbot : H=⊥
    · subst H
      exact ⟨fun _ => 1,fun _ => Or.inl rfl,by simp⟩
    · obtain ⟨e,he⟩ := H.edgeFinset_nonempty.mpr hbot
      obtain ⟨u,v⟩ := e
      have huv : H.Adj u v := (H.mem_edgeFinset.mp he)
      let H' := H.deleteEdges ({s(u,v)} : Finset (Sym2 V))
      have hle : H' ≤ H := H.deleteEdges_le _
      have hlt : H'.edgeFinset.card< n := by
        change (H.deleteEdges ({s(u,v)} : Finset (Sym2 V))).edgeFinset.card< n
        rw [SimpleGraph.edgeFinset_deleteEdges,sdiff_singleton_eq_erase]
        have hh : (H.edgeFinset.erase s(u,v)).card < H.edgeFinset.card :=
          card_erase_lt_of_mem (show s(u,v) ∈ H.edgeFinset from he)
        exact hh.trans_eq (by simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using hcard)
      obtain ⟨σ,hσ,hσedge⟩ := ih _ hlt H' (by simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]) (hH.anti hle)
        (fun x y hxy => hρ x y (hle hxy)) (fun x y hxy => hρsym x y (hle hxy))
      have hbridge := (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hH) huv
      have hnotuv : ¬H'.Reachable u v := by
        simpa only [H', Finset.coe_singleton] using SimpleGraph.isBridge_iff.mp hbridge
      have hnotvu : ¬H'.Reachable v u := fun h => hnotuv h.symm
      let a : ℝ := ρ u v*σ u*σ v
      have ha : IsSign a := ((hρ u v huv).mul (hσ u)).mul (hσ v)
      let τ : V → ℝ := fun w => if H'.Reachable v w then a*σ w else σ w
      have hτ : ∀ w,IsSign (τ w) := by
        intro w
        dsimp [τ]
        split
        · exact ha.mul (hσ w)
        · exact hσ w
      have huvτ : τ u*τ v=ρ u v := by
        simp only [τ,if_neg hnotvu,SimpleGraph.Reachable.rfl,if_pos]
        dsimp [a]
        calc
          σ u*((ρ u v*σ u*σ v)*σ v)=ρ u v*(σ u)^2*(σ v)^2 := by ring
          _=ρ u v := by rw [(hσ u).sq,(hσ v).sq]; ring
      refine ⟨τ,hτ,?_⟩
      intro x y hxy
      by_cases heq : s(x,y)=s(u,v)
      · rcases Sym2.eq_iff.mp heq with heq | heq
        · obtain ⟨rfl,rfl⟩ := heq
          exact huvτ
        · obtain ⟨rfl,rfl⟩ := heq
          simpa only [mul_comm, hρsym _ _ hxy] using huvτ
      · have hxy' : H'.Adj x y := by
          refine ⟨hxy, ?_⟩
          intro he
          have hm := he.1
          change s(x,y) ∈ ({s(u,v)} : Finset (Sym2 V)) at hm
          exact heq (Finset.mem_singleton.mp hm)
        have hr : H'.Reachable v x ↔ H'.Reachable v y :=
          ⟨fun h => h.trans hxy'.reachable,fun h => h.trans hxy'.symm.reachable⟩
        by_cases hx : H'.Reachable v x
        · have hy := hr.mp hx
          simp only [τ,if_pos hx,if_pos hy]
          calc
            (a*σ x)*(a*σ y)=a^2*(σ x*σ y) := by ring
            _=ρ x y := by rw [ha.sq,hσedge x y hxy',one_mul]
        · have hy : ¬H'.Reachable v y := fun h => hx (hr.mpr h)
          simp only [τ,if_neg hx,if_neg hy]
          exact hσedge x y hxy'

end ForestSigns
end GraphicalZonotopes

end
end
end BundlePart69

section BundlePart70
/- Source: Papers/GraphicalZonotopes/ForestOscillation.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ForestSigns
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

def edgeProduct (x : V → ℝ) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v => x u*x v,fun _ _ => mul_comm _ _⟩

@[simp] theorem edgeProduct_pair (x : V → ℝ) (u v : V) :
    edgeProduct x s(u,v)=x u*x v := rfl

def spinToBit (σ : V → ℝ) (v : V) : ℝ := (1+σ v)/2

theorem spinToBit_boolean {σ : V → ℝ} (hσ : ∀ v,IsSign (σ v)) :
    ∀ v,spinToBit σ v=0 ∨ spinToBit σ v=1 := by
  intro v
  rcases hσ v with h | h <;> simp [spinToBit,h]

theorem neg_signs {σ : V → ℝ} (hσ : ∀ v,IsSign (σ v)) :
    ∀ v,IsSign ((-σ) v) := by
  intro v
  rcases hσ v with h | h <;> simp [IsSign,h]

theorem edgeProduct_spin_complement (σ : V → ℝ) (e : Sym2 V) :
    edgeProduct (spinToBit σ) e+edgeProduct (spinToBit (-σ)) e=
      (1+edgeProduct σ e)/2 := by
  obtain ⟨u,v⟩ := e
  simp only [edgeProduct_pair,spinToBit,Pi.neg_apply]
  ring

def quadratic (G : SimpleGraph V) (c : ℝ) (l : V → ℝ) (w : Sym2 V → ℝ)
    (x : V → ℝ) : ℝ :=
  c+(∑ v,l v*x v)+∑ e ∈ G.edgeFinset,w e*edgeProduct x e

theorem quadratic_spin_complement (G : SimpleGraph V) (c : ℝ)
    (l : V → ℝ) (w : Sym2 V → ℝ) (σ : V → ℝ) :
    quadratic G c l w (spinToBit σ)+quadratic G c l w (spinToBit (-σ))=
      2*c+(∑ v,l v)+(1/2 : ℝ)*(∑ e ∈ G.edgeFinset,w e)+
      (1/2 : ℝ)*(∑ e ∈ G.edgeFinset,w e*edgeProduct σ e) := by
  have hlin : (∑ v,l v*spinToBit σ v)+(∑ v,l v*spinToBit (-σ) v)=∑ v,l v := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro v hv
    simp only [spinToBit,Pi.neg_apply]
    ring
  have hquad : (∑ e ∈ G.edgeFinset,w e*edgeProduct (spinToBit σ) e)+
      (∑ e ∈ G.edgeFinset,w e*edgeProduct (spinToBit (-σ)) e)=
      (1/2 : ℝ)*(∑ e ∈ G.edgeFinset,w e)+
      (1/2 : ℝ)*(∑ e ∈ G.edgeFinset,w e*edgeProduct σ e) := by
    rw [← sum_add_distrib,mul_sum,mul_sum,← sum_add_distrib]
    apply sum_congr rfl
    intro e he
    rw [← mul_add,edgeProduct_spin_complement]
    ring
  unfold quadratic
  linarith

def coefficientSign (w : Sym2 V → ℝ) (u v : V) : ℝ :=
  if 0 ≤ w s(u,v) then 1 else -1

theorem coefficientSign_isSign (w : Sym2 V → ℝ) (u v : V) :
    IsSign (coefficientSign w u v) := by
  unfold coefficientSign
  split <;> simp [IsSign]

theorem coefficientSign_symm (w : Sym2 V → ℝ) (u v : V) :
    coefficientSign w u v=coefficientSign w v u := by
  simp only [coefficientSign,Sym2.eq_swap]

theorem weight_mul_coefficientSign (w : Sym2 V → ℝ) (u v : V) :
    w s(u,v)*coefficientSign w u v=|w s(u,v)| := by
  by_cases h : 0 ≤ w s(u,v)
  · simp [coefficientSign,h,abs_of_nonneg h]
  · simp [coefficientSign,h,abs_of_neg (lt_of_not_ge h)]

theorem exists_energy_extrema (G : SimpleGraph V) (hG : G.IsAcyclic)
    (w : Sym2 V → ℝ) :
    ∃ σ τ : V → ℝ,(∀ v,IsSign (σ v)) ∧ (∀ v,IsSign (τ v)) ∧
      (∑ e ∈ G.edgeFinset,w e*edgeProduct σ e)=∑ e ∈ G.edgeFinset,|w e| ∧
      (∑ e ∈ G.edgeFinset,w e*edgeProduct τ e)=-(∑ e ∈ G.edgeFinset,|w e|) := by
  obtain ⟨σ,hσ,hσe⟩ := exists_vertex_signs G hG (coefficientSign w)
    (fun u v _ => coefficientSign_isSign w u v)
    (fun u v _ => coefficientSign_symm w u v)
  obtain ⟨τ,hτ,hτe⟩ := exists_vertex_signs G hG (fun u v => -coefficientSign w u v)
    (fun u v _ => by
      rcases coefficientSign_isSign w u v with h | h <;> simp [IsSign,h])
    (fun u v _ => by rw [coefficientSign_symm w u v])
  refine ⟨σ,τ,hσ,hτ,?_,?_⟩
  · apply sum_congr rfl
    intro e he
    obtain ⟨u,v⟩ := e
    rw [edgeProduct_pair,hσe u v (G.mem_edgeFinset.mp he),weight_mul_coefficientSign]
  · rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro e he
    obtain ⟨u,v⟩ := e
    rw [edgeProduct_pair,hτe u v (G.mem_edgeFinset.mp he),mul_neg,
      weight_mul_coefficientSign]

/-- Lemma9.3 in its full real-coefficient form: a quadratic Boolean
polynomial whose interaction graph is a forest has oscillation at least half
the total absolute interaction weight. Arbitrary linear and constant terms
are retained. -/
theorem quadratic_oscillation_lower (G : SimpleGraph V) (hG : G.IsAcyclic)
    (c : ℝ) (l : V → ℝ) (w : Sym2 V → ℝ) (lo hi : ℝ)
    (hbound : ∀ x : V → ℝ,(∀ v,x v=0 ∨ x v=1) →
      lo ≤ quadratic G c l w x ∧ quadratic G c l w x ≤ hi) :
    (1/2 : ℝ)*(∑ e ∈ G.edgeFinset,|w e|) ≤ hi-lo := by
  obtain ⟨σ,τ,hσ,hτ,hmax,hmin⟩ := exists_energy_extrema G hG w
  have hσplus := hbound (spinToBit σ) (spinToBit_boolean hσ)
  have hσminus := hbound (spinToBit (-σ)) (spinToBit_boolean (neg_signs hσ))
  have hτplus := hbound (spinToBit τ) (spinToBit_boolean hτ)
  have hτminus := hbound (spinToBit (-τ)) (spinToBit_boolean (neg_signs hτ))
  have hfirst := quadratic_spin_complement G c l w σ
  have hsecond := quadratic_spin_complement G c l w τ
  rw [hmax] at hfirst
  rw [hmin] at hsecond
  linarith

end ForestSigns
end GraphicalZonotopes

end
end
end BundlePart70

section BundlePart71
/- Source: Papers/GraphicalZonotopes/QuadraticSetFunctions.lean -/







@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The complete degree-two expansion, retaining arbitrary constant and
linear coefficients. This is a finite identity, valid on every ground set. -/
theorem zeta_degree_two (g : SetFunction V)
    (hdegree : ∀ C : Finset V,2< C.card → g C=0) (S : Finset V) :
    zeta g S=g ∅+(∑ v∈S,g {v})+∑ C∈S.powersetCard 2,g C := by
  let N:=max (S.card+1) 3
  let F : ℕ → ℝ := fun j => ∑ C∈S.powersetCard j,g C
  have hlarge : ∑ j∈range (S.card+1),F j=∑ j∈range N,F j := by
    apply sum_subset (range_mono (le_max_left _ _))
    intro j hj hsmall
    have hcard : S.card< j := by
      have hn : ¬j< S.card+1 := by simpa only [mem_range] using hsmall
      omega
    simp only [F,(powersetCard_eq_empty.mpr hcard),sum_empty]
  have hshort : ∑ j∈range 3,F j=∑ j∈range N,F j := by
    apply sum_subset (range_mono (le_max_right _ _))
    intro j hj hsmall
    have hthree : 3≤ j := by simpa only [mem_range,not_lt] using hsmall
    apply sum_eq_zero
    intro C hC
    exact hdegree C (by have hc:=(mem_powersetCard.mp hC).2; omega)
  unfold zeta
  rw [sum_powerset,hlarge,← hshort]
  simp only [F,sum_range_succ,sum_range_zero,zero_add,powersetCard_zero,
    sum_singleton,powersetCard_one,sum_map] <;> rfl

/-- The actual interaction graph can omit every pair whose coefficient is
zero; no additional equality is imposed on the linear or constant terms. -/
theorem zeta_degree_two_on_graph (G : SimpleGraph V) (g : SetFunction V)
    (hdegree : ∀ C : Finset V,2< C.card → g C=0)
    (hgraph : ∀ C : Finset V,C.card=2 → C∉edgeFamily G → g C=0)
    (S : Finset V) :
    zeta g S=g ∅+(∑ v∈S,g {v})+
      ∑ e∈G.edgeFinset,if e.toFinset⊆S then g e.toFinset else 0 := by
  rw [zeta_degree_two g hdegree S]
  congr 1
  have hp : (edgeFamily G).filter (fun C => C⊆S)⊆S.powersetCard 2 := by
    intro C hC
    obtain ⟨hC,hCS⟩ := mem_filter.mp hC
    exact mem_powersetCard.mpr ⟨hCS,((mem_edgeFamily G C).mp hC).1⟩
  have he : (∑ C∈(edgeFamily G).filter (fun C => C⊆S),g C)=
      ∑ C∈S.powersetCard 2,g C := by
    apply sum_subset hp
    intro C hC hnot
    have hCS := (mem_powersetCard.mp hC).1
    apply hgraph C (mem_powersetCard.mp hC).2
    intro hedge
    exact hnot (mem_filter.mpr ⟨hedge,hCS⟩)
  rw [← he,sum_filter,sum_edgeFamily_eq]

def booleanSupport (x : V → ℝ) : Finset V := by
  classical
  exact univ.filter (fun v => x v=1)

@[simp] theorem mem_booleanSupport (x : V → ℝ) (v : V) :
    v∈booleanSupport x ↔ x v=1 := by
  classical
  simp [booleanSupport]

theorem zeta_eq_boolean_quadratic (G : SimpleGraph V) (g : SetFunction V)
    (hdegree : ∀ C : Finset V,2< C.card → g C=0)
    (hgraph : ∀ C : Finset V,C.card=2 → C∉edgeFamily G → g C=0)
    (x : V → ℝ) (hx : ∀ v,x v=0 ∨ x v=1) :
    zeta g (booleanSupport x)=ForestSigns.quadratic G (g ∅)
      (fun v => g {v}) (fun e => g e.toFinset) x := by
  classical
  rw [zeta_degree_two_on_graph G g hdegree hgraph]
  unfold ForestSigns.quadratic
  have hlinear : (∑ v∈booleanSupport x,g {v})=∑ v,g {v}*x v := by
    rw [booleanSupport,sum_filter]
    apply sum_congr rfl
    intro v hv
    rcases hx v with he | he <;> simp [he]
  have hquad : (∑ e∈G.edgeFinset,if e.toFinset⊆booleanSupport x then g e.toFinset else 0)=
      ∑ e∈G.edgeFinset,g e.toFinset*ForestSigns.edgeProduct x e := by
    apply sum_congr rfl
    intro e he
    obtain ⟨a,b⟩ := e
    rw [Sym2.toFinset_mk_eq,ForestSigns.edgeProduct_pair]
    rcases hx a with ha | ha <;> rcases hx b with hb | hb <;>
      simp [Finset.insert_subset_iff,Finset.singleton_subset_iff,ha,hb]
  rw [hlinear,hquad]

end GraphicalZonotopes

end
end
end BundlePart71

section BundlePart72
/- Source: Papers/GraphicalZonotopes/ConditionalQuadratic.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem CliqueSupported.clique_of_nonzero {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y) {C : Finset V} (hC : y C≠0) : G.IsClique C := by
  intro u hu v hv huv
  by_contra hnot
  exact hC (hy.2.2 C u v hu hv huv hnot)

/-- Möbius coefficients of an elemental row, with its two endpoint variables
removed. The discarded coordinates are explicitly zero, not quotiented out. -/
def edgeCoefficients (y : SetFunction V) (u v : V) : SetFunction V := fun C =>
  if u∉C ∧ v∉C then y (insert u (insert v C)) else 0

theorem edgeCoefficients_degree_two {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y)
    (hfour : ∀ C : Finset V,G.IsClique C → C.card≤4)
    {u v : V} (huv : u≠ v) (C : Finset V) (hC : 2< C.card) :
    edgeCoefficients y u v C=0 := by
  classical
  by_cases he : u∉C ∧ v∉C
  · rw [edgeCoefficients,if_pos he]
    by_contra hnonzero
    have hbound := hfour _ (hy.clique_of_nonzero hnonzero)
    rw [card_insert_of_notMem (by simp [huv,he.1]),card_insert_of_notMem he.2] at hbound
    omega
  · simp [edgeCoefficients,he]

theorem edgeCoefficients_graph {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y) {u v : V} (huv : u≠ v)
    (C : Finset V) (hC : C.card=2) (hnot : C∉edgeFamily (edgeLink G u v)) :
    edgeCoefficients y u v C=0 := by
  classical
  by_cases he : u∉C ∧ v∉C
  · rw [edgeCoefficients,if_pos he]
    by_contra hn
    have hcl := hy.clique_of_nonzero hn
    obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hC
    have hua : u≠ a := fun h => he.1 (by simp [h])
    have hub : u≠ b := fun h => he.1 (by simp [h])
    have hva : v≠ a := fun h => he.2 (by simp [h])
    have hvb : v≠ b := fun h => he.2 (by simp [h])
    apply hnot
    apply (pair_mem_edgeFamily (edgeLink G u v) hab).mpr
    exact ⟨hcl (by simp) (by simp) hab,
      hcl (by simp) (by simp) hua,hcl (by simp) (by simp) hva,
      hcl (by simp) (by simp) hub,hcl (by simp) (by simp) hvb⟩
  · simp [edgeCoefficients,he]

theorem zeta_erase_of_containing_zero (g : SetFunction V) (u : V)
    (hz : ∀ C : Finset V,u∈C → g C=0) (S : Finset V) :
    zeta g S=zeta g (S.erase u) := by
  classical
  symm
  apply sum_subset (powerset_mono.mpr (erase_subset _ _))
  intro C hC hnot
  apply hz C
  by_contra hu
  apply hnot
  apply mem_powerset.mpr
  intro v hv
  exact mem_erase.mpr ⟨fun he => hu (he ▸ hv),(mem_powerset.mp hC) hv⟩

theorem edgeCoefficients_zeta {y : SetFunction V} {u v : V} (huv : u≠ v)
    {S : Finset V} (hu : u∉S) (hv : v∉S) :
    zeta (edgeCoefficients y u v) S=delta (zeta y) u v S := by
  classical
  rw [delta_zeta huv hu hv]
  apply sum_bij (fun C _ => insert u (insert v C))
  · intro C hC
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr (insert_subset_insert _
      (insert_subset_insert _ (mem_powerset.mp hC))),by simp⟩
  · intro C hC D hD he
    have huC : u∉C := notMem_mono (mem_powerset.mp hC) hu
    have hvC : v∉C := notMem_mono (mem_powerset.mp hC) hv
    have huD : u∉D := notMem_mono (mem_powerset.mp hD) hu
    have hvD : v∉D := notMem_mono (mem_powerset.mp hD) hv
    have hh:=congrArg (fun A : Finset V => (A.erase u).erase v) he
    simpa [huv,huC,hvC,huD,hvD] using hh
  · intro D hD
    obtain ⟨hsub,huD,hvD⟩ := mem_filter.mp hD
    refine ⟨(D.erase u).erase v,?_,?_⟩
    · apply mem_powerset.mpr
      intro w hw
      have hwD := mem_of_mem_erase (mem_of_mem_erase hw)
      have hwu := ne_of_mem_erase (mem_of_mem_erase hw)
      have hwv := ne_of_mem_erase hw
      have hm := (mem_powerset.mp hsub) hwD
      simpa only [mem_insert,hwu,hwv,false_or] using hm
    · ext w
      by_cases hwu : w=u <;> by_cases hwv : w=v <;> simp [hwu,hwv,huD,hvD]
  · intro C hC
    have huC : u∉C := notMem_mono (mem_powerset.mp hC) hu
    have hvC : v∉C := notMem_mono (mem_powerset.mp hC) hv
    simp [edgeCoefficients,huC,hvC]

/-- Every elemental row of four-clique-supported data is the literal
quadratic Boolean polynomial on the common-neighbor graph. -/
theorem edgeCoefficients_boolean_quadratic {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y)
    (hfour : ∀ C : Finset V,G.IsClique C → C.card≤4)
    {u v : V} (huv : u≠ v) (x : V → ℝ) (hx : ∀ w,x w=0 ∨ x w=1) :
    ForestSigns.quadratic (edgeLink G u v) (edgeCoefficients y u v ∅)
      (fun w => edgeCoefficients y u v {w})
      (fun e => edgeCoefficients y u v e.toFinset) x=
      delta (zeta y) u v (((booleanSupport x).erase u).erase v) := by
  rw [← zeta_eq_boolean_quadratic (edgeLink G u v) (edgeCoefficients y u v)
    (edgeCoefficients_degree_two hy hfour huv) (edgeCoefficients_graph hy huv) x hx]
  rw [zeta_erase_of_containing_zero _ u (by
    intro C hC; simp [edgeCoefficients,hC])]
  rw [zeta_erase_of_containing_zero _ v (by
    intro C hC; simp [edgeCoefficients,hC])]
  exact edgeCoefficients_zeta huv (by simp) (by simp)

end GraphicalZonotopes

end
end
end BundlePart72

section BundlePart73
/- Source: Papers/GraphicalZonotopes/CliqueLinkEquivalence.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem linkPair_excludes_endpoints {G : SimpleGraph V} {u v : V} {E : Finset V}
    (hE : E∈edgeFamily (edgeLink G u v)) : u∉E ∧ v∉E := by
  obtain ⟨hc,hcl⟩ := (mem_edgeFamily _ _).mp hE
  obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hc
  have he := hcl a (by simp) b (by simp) hab
  exact ⟨by simp [G.ne_of_adj he.2.1,G.ne_of_adj he.2.2.2.1],
    by simp [G.ne_of_adj he.2.2.1,G.ne_of_adj he.2.2.2.2]⟩

theorem tetrahedron_of_linkPair {G : SimpleGraph V} {u v : V} (huv : G.Adj u v)
    {E : Finset V} (hE : E∈edgeFamily (edgeLink G u v)) :
    insert u (insert v E)∈tetrahedra G := by
  classical
  obtain ⟨hc,hcl⟩ := (mem_edgeFamily _ _).mp hE
  obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hc
  have he := hcl a (by simp) b (by simp) hab
  have hua := G.ne_of_adj he.2.1
  have hub := G.ne_of_adj he.2.2.2.1
  have hva := G.ne_of_adj he.2.2.1
  have hvb := G.ne_of_adj he.2.2.2.2
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_,?_⟩
  · simp [huv.ne,hua,hub,hva,hvb,hab]
  · intro x hx y hy hxy
    change x ∈ (insert u (insert v {a,b}) : Finset V) at hx
    change y ∈ (insert u (insert v {a,b}) : Finset V) at hy
    simp only [mem_insert,mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl <;>
      first | exact False.elim (hxy rfl) | exact huv | exact huv.symm |
        exact he.1 | exact he.1.symm | exact he.2.1 | exact he.2.1.symm |
        exact he.2.2.1 | exact he.2.2.1.symm | exact he.2.2.2.1 |
        exact he.2.2.2.1.symm | exact he.2.2.2.2 | exact he.2.2.2.2.symm

theorem linkPair_of_tetrahedron {G : SimpleGraph V} {u v : V} (huv : u≠ v)
    {C : Finset V} (hC : C∈tetrahedra G) (huC : u∈C) (hvC : v∈C) :
    (C.erase u).erase v∈edgeFamily (edgeLink G u v) := by
  obtain ⟨hc,hcl⟩ := (mem_filter.mp hC).2
  apply (mem_edgeFamily _ _).mpr
  refine ⟨?_,?_⟩
  · rw [card_erase_of_mem (mem_erase.mpr ⟨huv.symm,hvC⟩),
      card_erase_of_mem huC,hc]
  · intro a ha b hb hab
    obtain ⟨hav,ha'⟩ := mem_erase.mp ha
    obtain ⟨hau,haC⟩ := mem_erase.mp ha'
    obtain ⟨hbv,hb'⟩ := mem_erase.mp hb
    obtain ⟨hbu,hbC⟩ := mem_erase.mp hb'
    exact ⟨hcl haC hbC hab,hcl huC haC hau.symm,hcl hvC haC hav.symm,
      hcl huC hbC hbu.symm,hcl hvC hbC hbv.symm⟩

def tetrahedraContaining (G : SimpleGraph V) (u v : V) : Finset (Finset V) := by
  classical
  exact (tetrahedra G).filter (fun C => u∈C ∧ v∈C)

/-- Every tetrahedron through an actual edge corresponds to exactly one
edge of its common-neighbor graph, with no omitted interaction or duplicate
coefficient. This is the coordinate dictionary used by the Boolean kernel
and lattice-oscillation arguments. -/
def tetrahedronLinkEquiv (G : SimpleGraph V) {u v : V} (huv : G.Adj u v) :
    ↥(tetrahedraContaining G u v) ≃ ↥(edgeFamily (edgeLink G u v)) where
  toFun C := ⟨(C.1.erase u).erase v,linkPair_of_tetrahedron huv.ne
    (mem_filter.mp C.2).1 (mem_filter.mp C.2).2.1 (mem_filter.mp C.2).2.2⟩
  invFun E := ⟨insert u (insert v E.1),mem_filter.mpr
    ⟨tetrahedron_of_linkPair huv E.2,by simp,by simp⟩⟩
  left_inv C := by
    apply Subtype.ext
    have huC := (mem_filter.mp C.2).2.1
    have hvC := (mem_filter.mp C.2).2.2
    ext x
    by_cases hxu : x=u <;> by_cases hxv : x=v <;> simp [hxu,hxv,huC,hvC]
  right_inv E := by
    apply Subtype.ext
    obtain ⟨huE,hvE⟩ := linkPair_excludes_endpoints E.2
    simp [huv.ne,huE,hvE]

theorem tetrahedronLink_card (G : SimpleGraph V) {u v : V} (huv : G.Adj u v) :
    (tetrahedraContaining G u v).card=(edgeLink G u v).edgeFinset.card := by
  have he := Fintype.card_congr (tetrahedronLinkEquiv G huv)
  simp only [Fintype.card_coe] at he
  rw [he,edgeFamily_eq_image_edgeFinset,card_image_of_injective _ sym2_toFinset_injective]

end GraphicalZonotopes

end
end
end BundlePart73

section BundlePart74
/- Source: Papers/GraphicalZonotopes/ThreeTreeEdgeCoordinates.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ThreeTreeStates
open Finset
open RootedResponse
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem ComplementPair.ne_val {C E : Finset V} (p : ComplementPair C E) :
    p.first.1≠ p.second.1 := fun he => p.ne (Subtype.ext he)

theorem ComplementPair.first_notMem {C E : Finset V} (p : ComplementPair C E) :
    p.first.1∉E := by
  simpa only [p.erase_eq] using
    (show p.first.1 ∉ (C.erase p.first.1).erase p.second.1 from by simp)

theorem ComplementPair.second_notMem {C E : Finset V} (p : ComplementPair C E) :
    p.second.1∉E := by
  simpa only [p.erase_eq] using
    (show p.second.1 ∉ (C.erase p.first.1).erase p.second.1 from notMem_erase _ _)

theorem ComplementPair.mem_complement_iff {C E : Finset V}
    (p : ComplementPair C E) (w : V) :
    w∈C ∧ w∉E ↔ w=p.first.1 ∨ w=p.second.1 := by
  rw [← mem_sdiff,← p.pair_eq_complement]
  simp only [mem_insert,mem_singleton]

theorem ComplementPair.erase_first {C E : Finset V} (p : ComplementPair C E) :
    C.erase p.first.1=insert p.second.1 E := by
  simpa only [p.erase_eq] using
    (insert_erase (mem_erase.mpr ⟨p.ne_val.symm,p.second.2⟩)).symm

theorem ComplementPair.erase_second {C E : Finset V} (p : ComplementPair C E) :
    C.erase p.second.1=insert p.first.1 E := by
  have he : (C.erase p.second.1).erase p.first.1 = E := by
    rw [erase_right_comm]
    exact p.erase_eq
  simpa only [he] using (insert_erase (mem_erase.mpr ⟨p.ne_val,p.first.2⟩)).symm

/-- The linear coefficient contributed by one tetrahedron to the
elemental row at its complementary pair. This is expressed on every
ambient vertex, with exact zeros off the two remaining vertices. -/
def pairLinear (G : SimpleGraph V) (s : CompatibleRows G)
    (E : Finset V) (hE : E.card=2) (C : IncidentPairClique G E) (w : V) : ℝ :=
  let p:=complementPair G C.1 E hE C.2
  if w=p.first.1 then realBit ((s.clique C.1).row p.second p.first)
  else if w=p.second.1 then realBit ((s.clique C.1).row p.first p.second)
  else 0

theorem pairLinear_eq_zero_of_notMem (G : SimpleGraph V) (s : CompatibleRows G)
    (E : Finset V) (hE : E.card=2) (C : IncidentPairClique G E) (w : V)
    (hw : w∉C.1.1) : pairLinear G s E hE C w=0 := by
  let p:=complementPair G C.1 E hE C.2
  have ha : w≠ p.first.1 := fun he => hw (he.symm ▸ p.first.2)
  have hb : w≠ p.second.1 := fun he => hw (he.symm ▸ p.second.2)
  dsimp only [p] at ha hb
  simp only [pairLinear,ha,hb,ite_false]

theorem pairLinear_eq_zero_of_mem (G : SimpleGraph V) (s : CompatibleRows G)
    (E : Finset V) (hE : E.card=2) (C : IncidentPairClique G E) (w : V)
    (hw : w∈E) : pairLinear G s E hE C w=0 := by
  let p:=complementPair G C.1 E hE C.2
  have ha : w≠ p.first.1 := fun he => p.first_notMem (he ▸ hw)
  have hb : w≠ p.second.1 := fun he => p.second_notMem (he ▸ hw)
  dsimp only [p] at ha hb
  simp only [pairLinear,ha,hb,ite_false]

def pairTriangleIncidenceEquiv (G : SimpleGraph V) (E : Finset V) (w : V)
    (hT : insert w E∈triangles G) :
    AllIncidentClique G ⟨insert w E,hT⟩ ≃
      {C : IncidentPairClique G E // w∈C.1.1} where
  toFun C:=⟨⟨C.1,(subset_insert w E).trans C.2⟩,C.2 (mem_insert_self _ _)⟩
  invFun C:=⟨C.1.1,insert_subset_iff.mpr ⟨C.2,C.1.2⟩⟩
  left_inv _:=rfl
  right_inv _:=rfl

theorem faceRow_eq_pairLinear (G : SimpleGraph V) (s : CompatibleRows G)
    (E : Finset V) (hE : E.card=2) (w : V) (hw : w∉E)
    (hT : insert w E∈triangles G)
    (D : AllIncidentClique G ⟨insert w E,hT⟩) :
    realBit (faceRow G s ⟨insert w E,hT⟩ D ⟨w,mem_insert_self _ _⟩)=
      pairLinear G s E hE ((pairTriangleIncidenceEquiv G E w hT) D).1 w := by
  let C:=((pairTriangleIncidenceEquiv G E w hT) D).1
  let p:=complementPair G C.1 E hE C.2
  have hwC : w∈C.1.1:=D.2 (mem_insert_self _ _)
  change realBit ((s.clique C.1).row (faceMissing G C.1 ⟨insert w E,hT⟩ D.2) ⟨w,hwC⟩) =
    if w=p.first.1 then realBit ((s.clique C.1).row p.second p.first)
    else if w=p.second.1 then realBit ((s.clique C.1).row p.first p.second) else 0
  rcases (p.mem_complement_iff w).mp ⟨hwC,hw⟩ with ha | hb
  · have hm : faceMissing G C.1 ⟨insert w E,hT⟩ D.2=p.second := by
      apply Subtype.ext
      apply (erase_inj C.1.1 (faceMissing G C.1 ⟨insert w E,hT⟩ D.2).2).mp
      rw [faceMissing_spec]
      change insert w E = C.1.1.erase p.second.1
      rw [p.erase_second,ha]
    have hwv : (⟨w,hwC⟩ : ↥C.1.1)=p.first:=Subtype.ext ha
    rw [hm, if_pos ha]
    exact congrArg (fun j => realBit ((s.clique C.1).row p.second j)) hwv
  · have hm : faceMissing G C.1 ⟨insert w E,hT⟩ D.2=p.first := by
      apply Subtype.ext
      apply (erase_inj C.1.1 (faceMissing G C.1 ⟨insert w E,hT⟩ D.2).2).mp
      rw [faceMissing_spec]
      change insert w E = C.1.1.erase p.first.1
      rw [p.erase_first,hb]
    have hna : w≠ p.first.1 := by rw [hb]; exact p.ne_val.symm
    have hwv : (⟨w,hwC⟩ : ↥C.1.1)=p.second:=Subtype.ext hb
    rw [hm, if_neg hna, if_pos hb]
    exact congrArg (fun j => realBit ((s.clique C.1).row p.first j)) hwv

/-- Every actual triangle column is exactly the sum of its contributions
from tetrahedra incident with a fixed edge of that triangle. -/
theorem column_eq_sum_pairLinear (G : SimpleGraph V) (s : CompatibleRows G)
    (E : Finset V) (hE : E.card=2) (w : V) (hw : w∉E)
    (hT : insert w E∈triangles G) :
    columnValue G s ⟨insert w E,hT⟩ ⟨w,mem_insert_self _ _⟩=
      ∑ C : IncidentPairClique G E,pairLinear G s E hE C w := by
  classical
  unfold columnValue
  calc
    _=∑ C : {C : IncidentPairClique G E // w∈C.1.1},
        pairLinear G s E hE C.1 w :=
      Fintype.sum_equiv (pairTriangleIncidenceEquiv G E w hT) _ _
        (faceRow_eq_pairLinear G s E hE w hw hT)
    _=∑ C∈(univ : Finset (IncidentPairClique G E)).filter (fun C => w∈C.1.1),
        pairLinear G s E hE C w :=
      (sum_subtype ((univ : Finset (IncidentPairClique G E)).filter (fun C => w∈C.1.1))
        (by intro C; simp) (fun C => pairLinear G s E hE C w)).symm
    _=∑ C : IncidentPairClique G E,pairLinear G s E hE C w := by
      apply sum_subset (filter_subset _ _)
      intro C hC hnot
      exact pairLinear_eq_zero_of_notMem G s E hE C w
        (fun hwC => hnot (mem_filter.mpr ⟨hC,hwC⟩))

theorem coefficients_insert_pair {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) (E : Finset V) (hE : E.card=2)
    (w : V) (hw : w∉E) :
    coefficients h s (insert w E)=
      -(∑ C : IncidentPairClique G E,pairLinear G s E hE C w) := by
  classical
  by_cases hT : insert w E∈triangles G
  · rw [coefficients_triangle h s hT,
      ← column_eq_triangleWeight h s ⟨insert w E,hT⟩ ⟨w,mem_insert_self _ _⟩,
      column_eq_sum_pairLinear G s E hE w hw hT]
  · have hzero : coefficients h s (insert w E)=0 := by
      by_contra hn
      have hcl:=(coefficients_cliqueSupported h s).clique_of_nonzero hn
      exact hT (mem_triangles.mpr ⟨by rw [card_insert_of_notMem hw,hE],hcl⟩)
    rw [hzero]
    symm
    rw [neg_eq_zero]
    apply sum_eq_zero
    intro C hC
    apply pairLinear_eq_zero_of_notMem G s E hE C w
    intro hwC
    apply hT
    refine mem_triangles.mpr ⟨by rw [card_insert_of_notMem hw,hE],?_⟩
    have hs : insert w E ⊆ C.1.1 := insert_subset_iff.mpr ⟨hwC,C.2⟩
    intro a ha b hb hab
    exact (mem_filter.mp C.1.2).2.2 (hs ha) (hs hb) hab

theorem pairLinear_sum (G : SimpleGraph V) (s : CompatibleRows G)
    (E : Finset V) (hE : E.card=2) (C : IncidentPairClique G E) (x : V → ℝ) :
    (∑ w,pairLinear G s E hE C w*x w)=
      let p:=complementPair G C.1 E hE C.2
      realBit ((s.clique C.1).row p.second p.first)*x p.first.1+
      realBit ((s.clique C.1).row p.first p.second)*x p.second.1 := by
  let p:=complementPair G C.1 E hE C.2
  calc
    _=pairLinear G s E hE C p.first.1*x p.first.1+
        pairLinear G s E hE C p.second.1*x p.second.1 := by
      apply sum_eq_add_of_mem p.first.1 p.second.1 (mem_univ _) (mem_univ _) p.ne_val
      intro w hw hne
      dsimp only [p] at hne
      simp only [pairLinear,hne.1,hne.2,ite_false,zero_mul]
    _=_ := by
      have hp := p.ne_val.symm
      dsimp only [p] at hp ⊢
      simp only [pairLinear,ite_true,hp,ite_false]

end ThreeTreeStates
end GraphicalZonotopes

end
end
end BundlePart74

section BundlePart75
/- Source: Papers/GraphicalZonotopes/ThreeTreeFactorization.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ThreeTreeStates
open Finset
open RootedResponse
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

def edgeFinsetFamilyEquiv (G : SimpleGraph V) : ↥G.edgeFinset ≃ ↥(edgeFamily G) :=
  Equiv.ofBijective (fun e => ⟨e.1.toFinset,by
    rw [edgeFamily_eq_image_edgeFinset]
    exact mem_image.mpr ⟨e.1,e.2,rfl⟩⟩) (by
    constructor
    · intro e f hef
      exact Subtype.ext (sym2_toFinset_injective (congrArg Subtype.val hef))
    · intro E
      have hE:=E.2
      simp only [edgeFamily_eq_image_edgeFinset] at hE
      obtain ⟨e,he,heE⟩:=mem_image.mp hE
      exact ⟨⟨e,he⟩,Subtype.ext heE⟩)

def incidentPairContainingEquiv (G : SimpleGraph V) (u v : V) :
    IncidentPairClique G {u,v} ≃ ↥(tetrahedraContaining G u v) where
  toFun C:=⟨C.1.1,mem_filter.mpr ⟨C.1.2,C.2 (by simp),C.2 (by simp)⟩⟩
  invFun C:=⟨⟨C.1,(mem_filter.mp C.2).1⟩,by
    simpa only [insert_subset_iff,singleton_subset_iff] using (mem_filter.mp C.2).2⟩
  left_inv _:=rfl
  right_inv _:=rfl

/-- The summation over actual incident tetrahedra is exactly the summation
over actual edges of the common-neighbor graph. -/
def pairLinkEquiv (G : SimpleGraph V) {u v : V} (huv : G.Adj u v) :
    IncidentPairClique G {u,v} ≃ ↥(edgeLink G u v).edgeFinset :=
  ((incidentPairContainingEquiv G u v).trans (tetrahedronLinkEquiv G huv)).trans
    (edgeFinsetFamilyEquiv (edgeLink G u v)).symm

theorem pairLinkEquiv_toFinset (G : SimpleGraph V) {u v : V} (huv : G.Adj u v)
    (C : IncidentPairClique G {u,v}) :
    ((pairLinkEquiv G huv C).1).toFinset=(C.1.1.erase u).erase v := by
  exact congrArg Subtype.val
    ((edgeFinsetFamilyEquiv (edgeLink G u v)).apply_symm_apply
      ((tetrahedronLinkEquiv G huv) ((incidentPairContainingEquiv G u v) C)))

theorem pairLinkEquiv_eq (G : SimpleGraph V) {u v : V} (huv : G.Adj u v)
    (C : IncidentPairClique G {u,v}) :
    (pairLinkEquiv G huv C).1=
      let p:=complementPair G C.1 {u,v} (by simp [huv.ne]) C.2
      s(p.first.1,p.second.1) := by
  let p:=complementPair G C.1 {u,v} (by simp [huv.ne]) C.2
  apply sym2_toFinset_injective
  rw [pairLinkEquiv_toFinset,Sym2.toFinset_mk_eq,p.pair_eq_complement]
  ext w
  simp only [mem_erase,mem_sdiff,mem_insert,mem_singleton,not_or]
  tauto

theorem edgeCoefficients_constant {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v) :
    edgeCoefficients (coefficients h s) u v ∅=
      ∑ C : IncidentPairClique G {u,v},
        ((complementPair G C.1 {u,v} (by simp [huv.ne]) C.2).maximum
          (s.clique C.1).row : ℝ) := by
  rw [edgeCoefficients,if_pos (by simp)]
  simp only [insert_empty_eq]
  rw [coefficients_pair h s ((pair_mem_edgeFamily G huv.ne).mpr huv)]
  simp only [pairWeight,Int.cast_sum]

theorem edgeCoefficients_linear {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v)
    (w : V) :
    edgeCoefficients (coefficients h s) u v {w}=
      -(∑ C : IncidentPairClique G {u,v},
        pairLinear G s {u,v} (by simp [huv.ne]) C w) := by
  classical
  by_cases hw : w∈({u,v} : Finset V)
  · have hs : ∑ C : IncidentPairClique G {u,v},
        pairLinear G s {u,v} (by simp [huv.ne]) C w=0 := by
      exact sum_eq_zero (fun C _ => pairLinear_eq_zero_of_mem G s _ _ C w hw)
    rw [hs,neg_zero]
    simp only [mem_insert,mem_singleton] at hw
    rcases hw with rfl | rfl <;> simp [edgeCoefficients]
  · have hwu : w≠ u := fun he => hw (by simp [he])
    have hwv : w≠ v := fun he => hw (by simp [he])
    rw [edgeCoefficients,if_pos (by simp [hwu.symm,hwv.symm])]
    have he : insert u (insert v ({w} : Finset V))=insert w {u,v} := by
      ext a
      simp only [mem_insert,mem_singleton]
      tauto
    rw [he]
    exact coefficients_insert_pair h s _ (by simp [huv.ne]) w hw

theorem edgeCoefficients_quadratic {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v)
    (e : ↥(edgeLink G u v).edgeFinset) :
    edgeCoefficients (coefficients h s) u v e.1.toFinset=1 := by
  have hE : e.1.toFinset∈edgeFamily (edgeLink G u v):=
    ((edgeFinsetFamilyEquiv (edgeLink G u v)) e).2
  obtain ⟨hu,hv⟩:=linkPair_excludes_endpoints hE
  rw [edgeCoefficients,if_pos ⟨hu,hv⟩]
  exact coefficients_tetrahedron h s (tetrahedron_of_linkPair huv hE)

def pairFactor (G : SimpleGraph V) (s : CompatibleRows G)
    (E : Finset V) (hE : E.card=2) (C : IncidentPairClique G E) (x : V → ℝ) : ℝ :=
  let p:=complementPair G C.1 E hE C.2
  (p.maximum (s.clique C.1).row : ℝ)-
    realBit ((s.clique C.1).row p.first p.second)*x p.second.1-
    realBit ((s.clique C.1).row p.second p.first)*x p.first.1+
    x p.first.1*x p.second.1

/-- The exact polynomial identity, before restricting coordinates to the
Boolean cube. Its constant, every ambient linear coefficient, and every
quadratic interaction are proved from the actual Möbius vector. -/
theorem quadratic_eq_sum_pairFactor {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v)
    (x : V → ℝ) :
    ForestSigns.quadratic (edgeLink G u v)
      (edgeCoefficients (coefficients h s) u v ∅)
      (fun w => edgeCoefficients (coefficients h s) u v {w})
      (fun e => edgeCoefficients (coefficients h s) u v e.toFinset) x=
      ∑ C : IncidentPairClique G {u,v},pairFactor G s {u,v} (by simp [huv.ne]) C x := by
  classical
  let pc : (C : IncidentPairClique G {u,v}) → ComplementPair C.1.1 {u,v}:=
    fun C => complementPair G C.1 {u,v} (by simp [huv.ne]) C.2
  have hlin : (∑ w,edgeCoefficients (coefficients h s) u v {w}*x w)=
      -(∑ C : IncidentPairClique G {u,v},
        (realBit ((s.clique C.1).row (pc C).second (pc C).first)*x (pc C).first.1+
        realBit ((s.clique C.1).row (pc C).first (pc C).second)*x (pc C).second.1)) := by
    simp_rw [edgeCoefficients_linear h s huv,neg_mul,sum_mul]
    rw [sum_neg_distrib,sum_comm]
    simp_rw [pairLinear_sum]
    rfl
  have hquad :
      (∑ e∈(edgeLink G u v).edgeFinset,
        edgeCoefficients (coefficients h s) u v e.toFinset*ForestSigns.edgeProduct x e)=
      ∑ C : IncidentPairClique G {u,v},x (pc C).first.1*x (pc C).second.1 := by
    rw [← sum_coe_sort]
    have hw : ∀ e : ↥(edgeLink G u v).edgeFinset,
        edgeCoefficients (coefficients h s) u v e.1.toFinset=1:=
      edgeCoefficients_quadratic h s huv
    simp_rw [hw,one_mul]
    symm
    apply Fintype.sum_equiv (pairLinkEquiv G huv)
    intro C
    rw [pairLinkEquiv_eq,ForestSigns.edgeProduct_pair]
  unfold ForestSigns.quadratic
  rw [edgeCoefficients_constant h s huv,hlin,hquad]
  simp only [pairFactor]
  rw [← sub_eq_add_neg,← sum_sub_distrib,← sum_add_distrib]
  apply sum_congr rfl
  intro C hC
  dsimp only [pc]
  ring

theorem pairFactor_zero_or_one (G : SimpleGraph V) (s : CompatibleRows G)
    (E : Finset V) (hE : E.card=2) (C : IncidentPairClique G E) (x : V → Bool) :
    pairFactor G s E hE C (fun w => realBit (x w))=0 ∨
      pairFactor G s E hE C (fun w => realBit (x w))=1 := by
  let p:=complementPair G C.1 E hE C.2
  change ((p.maximum (s.clique C.1).row : ℝ)-
    realBit ((s.clique C.1).row p.first p.second)*realBit (x p.second.1)-
    realBit ((s.clique C.1).row p.second p.first)*realBit (x p.first.1)+
    realBit (x p.first.1)*realBit (x p.second.1)=0) ∨
    ((p.maximum (s.clique C.1).row : ℝ)-
    realBit ((s.clique C.1).row p.first p.second)*realBit (x p.second.1)-
    realBit ((s.clique C.1).row p.second p.first)*realBit (x p.first.1)+
    realBit (x p.first.1)*realBit (x p.second.1)=1)
  unfold ComplementPair.maximum
  cases (s.clique C.1).row p.first p.second <;>
    cases (s.clique C.1).row p.second p.first <;>
    cases x p.first.1 <;> cases x p.second.1 <;>
    norm_num [realBit,RootedResponse.integerBit]

/-- Every elemental slack is the literal sum of the Boolean local factors.
Endpoint erasure only expresses that a conditioning set omits those endpoints. -/
theorem elemental_factorization {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v)
    (x : V → Bool) :
    delta (setFunction h s) u v
      (((booleanSupport (fun w => realBit (x w))).erase u).erase v)=
      ∑ C : IncidentPairClique G {u,v},
        pairFactor G s {u,v} (by simp [huv.ne]) C (fun w => realBit (x w)) := by
  unfold setFunction
  rw [← edgeCoefficients_boolean_quadratic (coefficients_cliqueSupported h s)
    (fun C hC => h.clique_card_le_four hC) huv.ne _
      (fun w => by cases x w <;> simp [realBit])]
  exact quadratic_eq_sum_pairFactor h s huv _

end ThreeTreeStates
end GraphicalZonotopes

end
end
end BundlePart75

section BundlePart76
/- Source: Papers/GraphicalZonotopes/ThreeTreeSharedEdges.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem tetrahedra_mono {G H : SimpleGraph V} (h : G≤ H) :
    tetrahedra G⊆tetrahedra H := by
  classical
  intro C hC
  obtain ⟨hc,hcl⟩ := (mem_filter.mp hC).2
  exact mem_filter.mpr ⟨mem_univ _,hc,fun u hu v hv huv => h (hcl hu hv huv)⟩

theorem triangleMultiplicity_mono {G H : SimpleGraph V} (h : G≤ H) (T : Finset V) :
    triangleMultiplicity G T≤ triangleMultiplicity H T := by
  classical
  apply card_le_card
  intro C hC
  obtain ⟨hC,hTC⟩ := mem_filter.mp hC
  exact mem_filter.mpr ⟨tetrahedra_mono h hC,hTC⟩

theorem internalTriangles_mono {G H : SimpleGraph V} (h : G≤ H) :
    internalTriangles G⊆internalTriangles H := by
  intro T hT
  obtain ⟨hT,hcount⟩ := mem_internalTriangles.mp hT
  obtain ⟨hc,hcl⟩ := mem_triangles.mp hT
  exact mem_internalTriangles.mpr
    ⟨mem_triangles.mpr ⟨hc,fun u hu v hv huv => h (hcl hu hv huv)⟩,
      hcount.trans (triangleMultiplicity_mono h T)⟩

/-- A running-intersection consequence for all actual tetrahedra: if two
distinct cliques contain a set E, the first clique has a shared triangular
face containing E. In particular, an edge contained in several tetrahedra
meets an internal face at every tetrahedron containing it. -/
theorem ThreeTreeOn.shared_face_containing {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {C D E : Finset V}
    (hC : C∈tetrahedra G) (hD : D∈tetrahedra G) (hCD : C≠ D)
    (hEC : E⊆C) (hED : E⊆D) :
    ∃ T∈internalTriangles G,E⊆T ∧ T⊆C := by
  classical
  induction h generalizing C D E with
  | tetrahedron A hA =>
    rw [tetrahedra_cliqueGraph hA,mem_singleton] at hC hD
    exact False.elim (hCD (hC.trans hD.symm))
  | @attach S G h u hu A hA hAS hcA ih =>
    let H := G⊔attachmentStar u A
    have hmono : G≤ H := le_sup_left
    obtain ⟨K,hK,hAK⟩ := h.triangle_extends hA hcA
    have hnew : insert u A∈tetrahedra H := by
      rw [tetrahedra_after_attachment h hu hA hAS hcA]
      exact mem_insert_self _ _
    have hnewK : insert u A≠ K := by
      intro he
      apply attached_tetrahedron_not_old h hu (T := A)
      simpa only [he] using hK
    have hshared : A∈internalTriangles H := internal_triangle_of_shared hnew
      (tetrahedra_mono hmono hK) hnewK hA (subset_insert _ _) hAK
    have hav : ∀ L∈tetrahedra G,u∉L := by
      intro L hL hum
      have hc := (mem_filter.mp hL).2
      exact hu (h.clique_subset_active (by omega) hc.2 hum)
    have hsubsetA : ∀ L∈tetrahedra G,E⊆L → E⊆insert u A → E⊆A := by
      intro L hL hEL hEN v hv
      rcases mem_insert.mp (hEN hv) with he | hvA
      · exact False.elim (hav L hL (he ▸ hEL hv))
      · exact hvA
    rw [tetrahedra_after_attachment h hu hA hAS hcA] at hC hD
    rcases mem_insert.mp hC with hC | hC
    · subst C
      rcases mem_insert.mp hD with hD | hD
      · exact False.elim (hCD hD.symm)
      · exact ⟨A,hshared,hsubsetA D hD hED hEC,subset_insert _ _⟩
    · rcases mem_insert.mp hD with hD | hD
      · subst D
        have hEA : E⊆A := hsubsetA C hC hEC hED
        by_cases hCK : C=K
        · exact ⟨A,hshared,hEA,by simpa only [hCK] using hAK⟩
        · obtain ⟨T,hT,hET,hTC⟩ := ih hC hK hCK hEC (hEA.trans hAK)
          exact ⟨T,internalTriangles_mono hmono hT,hET,hTC⟩
      · obtain ⟨T,hT,hET,hTC⟩ := ih hC hD hCD hEC hED
        exact ⟨T,internalTriangles_mono hmono hT,hET,hTC⟩

end GraphicalZonotopes

end
end
end BundlePart76

section BundlePart77
/- Source: Papers/GraphicalZonotopes/ForestZeroKernel.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace ForestZeros
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A zero of the sum of the nonnegative factors `xy` and
`(1-x)(1-y)`: every edge has an endpoint equal to its specified bit. -/
def CoversLabels (G : SimpleGraph V) (b : Sym2 V → Bool) (x : V → Bool) : Prop :=
  ∀ u v,G.Adj u v → x u=b s(u,v) ∨ x v=b s(u,v)

def bitSign (b : Bool) : ℝ := if b then 1 else -1

def signBit (s : ℝ) : Bool := decide (s=1)

theorem bitSign_isSign (b : Bool) : ForestSigns.IsSign (bitSign b) := by
  cases b <;> simp [bitSign,ForestSigns.IsSign]

@[simp] theorem signBit_bitSign (b : Bool) : signBit (bitSign b)=b := by
  cases b <;> norm_num [signBit,bitSign]

theorem signBit_covers_of_neg_product {s t : ℝ}
    (hs : ForestSigns.IsSign s) (ht : ForestSigns.IsSign t)
    (hst : s*t=-1) (b : Bool) : signBit s=b ∨ signBit t=b := by
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    cases b
  all_goals try (norm_num [signBit] at hst)
  all_goals norm_num [signBit]

/-- Opposite signs on every forest edge give a zero independently of the
choice of edge labels. Empty and disconnected forests are included. -/
theorem exists_cover (G : SimpleGraph V) (hG : G.IsAcyclic)
    (b : Sym2 V → Bool) : ∃ x,CoversLabels G b x := by
  obtain ⟨σ,hσ,hσe⟩ := ForestSigns.exists_vertex_signs G hG (fun _ _ => -1)
    (by intro u v huv; exact Or.inr rfl) (by intro u v huv; rfl)
  refine ⟨fun v => signBit (σ v),?_⟩
  intro u v huv
  exact signBit_covers_of_neg_product (hσ u) (hσ v) (hσe u v huv) _

/-- For every vertex of a forest, the common zero locus contains two
points differing at that vertex alone. In particular the zero locus spans
the full affine Boolean coordinate space; this does not follow merely from
the existence of a single zero. -/
theorem exists_flippable_cover (G : SimpleGraph V) (hG : G.IsAcyclic)
    (b : Sym2 V → Bool) (r : V) :
    ∃ x : V → Bool,∀ a : Bool,CoversLabels G b (Function.update x r a) := by
  let ρ : V → V → ℝ := fun u v =>
    if u=r ∨ v=r then bitSign (b s(u,v)) else -1
  have hρ : ∀ u v,G.Adj u v → ForestSigns.IsSign (ρ u v) := by
    intro u v huv
    dsimp [ρ]
    split
    · exact bitSign_isSign _
    · exact Or.inr rfl
  have hρsym : ∀ u v,G.Adj u v → ρ u v=ρ v u := by
    intro u v huv
    simp only [ρ,or_comm,Sym2.eq_swap]
  obtain ⟨σ,hσ,hσe⟩ := ForestSigns.exists_vertex_signs G hG ρ hρ hρsym
  let τ : V → ℝ := fun v => σ r*σ v
  have hτ : ∀ v,ForestSigns.IsSign (τ v) := fun v => (hσ r).mul (hσ v)
  have hneighbor : ∀ v,G.Adj r v → signBit (τ v)=b s(r,v) := by
    intro v hrv
    have he := hσe r v hrv
    have he' : τ v=bitSign (b s(r,v)) := by
      dsimp only [ρ] at he
      rw [if_pos (Or.inl rfl)] at he
      simpa only [τ] using he
    rw [he',signBit_bitSign]
  have hoff : ∀ u v,G.Adj u v → u≠ r → v≠ r →
      signBit (τ u)=b s(u,v) ∨ signBit (τ v)=b s(u,v) := by
    intro u v huv hur hvr
    have hprod : τ u*τ v=-1 := by
      calc
        τ u*τ v=(σ r)^2*(σ u*σ v) := by dsimp [τ]; ring
        _=-1 := by rw [(hσ r).sq,hσe u v huv]; simp [ρ,hur,hvr]
    exact signBit_covers_of_neg_product (hτ u) (hτ v) hprod _
  refine ⟨fun v => signBit (τ v),?_⟩
  intro a u v huv
  by_cases hur : u=r
  · subst u
    have hvr : v≠ r := huv.ne.symm
    exact Or.inr (by simpa only [Function.update_of_ne hvr] using hneighbor v huv)
  · by_cases hvr : v=r
    · subst v
      exact Or.inl (by
        simpa only [Function.update_of_ne hur,Sym2.eq_swap] using hneighbor u huv.symm)
    · simpa only [Function.update_of_ne hur,Function.update_of_ne hvr] using
        hoff u v huv hur hvr

def affineValue (c : ℝ) (l : V → ℝ) (x : V → Bool) : ℝ :=
  c+∑ v,l v*RootedResponse.realBit (x v)

theorem affineValue_update_difference (c : ℝ) (l : V → ℝ)
    (x : V → Bool) (r : V) :
    affineValue c l (Function.update x r true)-
      affineValue c l (Function.update x r false)=l r := by
  calc
    affineValue c l (Function.update x r true)-
        affineValue c l (Function.update x r false)=
        ∑ v,(l v*RootedResponse.realBit ((Function.update x r true) v)-
          l v*RootedResponse.realBit ((Function.update x r false) v)) := by
      rw [sum_sub_distrib]
      unfold affineValue
      ring
    _=l r := by
      rw [sum_eq_single r]
      · simp [RootedResponse.realBit]
      · intro v hv hvr
        simp only [Function.update_of_ne hvr,sub_self]
      · intro hr
        exact False.elim (hr (mem_univ r))

/-- No nonzero affine functional vanishes on the entire zero locus of a
sum of labelled-edge factors on a finite forest. Together with subtraction
of the known quadratic coefficients, this identifies the full quadratic
tight kernel, rather than only a selected set of zero rows. -/
theorem affine_vanishing_iff (G : SimpleGraph V) (hG : G.IsAcyclic)
    (b : Sym2 V → Bool) (c : ℝ) (l : V → ℝ) :
    (∀ x,CoversLabels G b x → affineValue c l x=0) ↔
      c=0 ∧ ∀ v,l v=0 := by
  constructor
  · intro hzero
    have hl : ∀ r,l r=0 := by
      intro r
      obtain ⟨x,hx⟩ := exists_flippable_cover G hG b r
      have hfalse := hzero _ (hx false)
      have htrue := hzero _ (hx true)
      have hd := affineValue_update_difference c l x r
      rw [hfalse,htrue] at hd
      linarith
    obtain ⟨x,hx⟩ := exists_cover G hG b
    have hc := hzero x hx
    simp only [affineValue,hl,zero_mul,sum_const_zero,add_zero] at hc
    exact ⟨hc,hl⟩
  · rintro ⟨rfl,hl⟩ x hx
    simp only [affineValue,hl,zero_mul,sum_const_zero,add_zero]

end ForestZeros
end GraphicalZonotopes

end
end
end BundlePart77

section BundlePart78
/- Source: Papers/GraphicalZonotopes/ForestFactorKernel.lean -/







@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ForestZeros
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Each edge has quadratic coefficient one. Its lower coefficients are
fixed by its bit: `xy` for zero, `(1-x)(1-y)` for one. -/
def edgeFactor (b : Sym2 V → Bool) (x : V → Bool) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v =>
    if b s(u,v) then
      (1-RootedResponse.realBit (x u))*(1-RootedResponse.realBit (x v))
    else RootedResponse.realBit (x u)*RootedResponse.realBit (x v),by
      intro u v
      simp only [Sym2.eq_swap,mul_comm]⟩

@[simp] theorem edgeFactor_pair (b : Sym2 V → Bool) (x : V → Bool) (u v : V) :
    edgeFactor b x s(u,v)=
      if b s(u,v) then
        (1-RootedResponse.realBit (x u))*(1-RootedResponse.realBit (x v))
      else RootedResponse.realBit (x u)*RootedResponse.realBit (x v) := rfl

theorem edgeFactor_zero_or_one (b : Sym2 V → Bool) (x : V → Bool) (e : Sym2 V) :
    edgeFactor b x e=0 ∨ edgeFactor b x e=1 := by
  obtain ⟨u,v⟩ := e
  rw [edgeFactor_pair]
  cases b s(u,v) <;> cases x u <;> cases x v <;>
    norm_num [RootedResponse.realBit]

theorem edgeFactor_nonneg (b : Sym2 V → Bool) (x : V → Bool) (e : Sym2 V) :
    0≤ edgeFactor b x e := by
  rcases edgeFactor_zero_or_one b x e with h | h <;> simp [h]

theorem edgeFactor_le_one (b : Sym2 V → Bool) (x : V → Bool) (e : Sym2 V) :
    edgeFactor b x e≤1 := by
  rcases edgeFactor_zero_or_one b x e with h | h <;> simp [h]

theorem edgeFactor_pair_eq_zero (b : Sym2 V → Bool) (x : V → Bool) (u v : V) :
    edgeFactor b x s(u,v)=0 ↔ x u=b s(u,v) ∨ x v=b s(u,v) := by
  rw [edgeFactor_pair]
  cases b s(u,v) <;> cases x u <;> cases x v <;>
    norm_num [RootedResponse.realBit]

def totalFactor (G : SimpleGraph V) (b : Sym2 V → Bool) (x : V → Bool) : ℝ :=
  ∑ e∈G.edgeFinset,edgeFactor b x e

theorem totalFactor_nonneg (G : SimpleGraph V) (b : Sym2 V → Bool) (x : V → Bool) :
    0≤ totalFactor G b x := by
  exact sum_nonneg (fun e he => edgeFactor_nonneg b x e)

theorem totalFactor_le_card (G : SimpleGraph V) (b : Sym2 V → Bool) (x : V → Bool) :
    totalFactor G b x≤(G.edgeFinset.card : ℝ) := by
  calc
    totalFactor G b x≤∑ e∈G.edgeFinset,(1:ℝ) :=
      sum_le_sum (fun e he => edgeFactor_le_one b x e)
    _=(G.edgeFinset.card : ℝ) := by simp

theorem totalFactor_eq_zero_iff (G : SimpleGraph V) (b : Sym2 V → Bool)
    (x : V → Bool) : totalFactor G b x=0 ↔ CoversLabels G b x := by
  rw [totalFactor,sum_eq_zero_iff_of_nonneg (fun e he => edgeFactor_nonneg b x e)]
  constructor
  · intro h u v huv
    exact (edgeFactor_pair_eq_zero b x u v).mp (h _ (G.mem_edgeFinset.mpr huv))
  · intro h e he
    obtain ⟨u,v⟩ := e
    exact (edgeFactor_pair_eq_zero b x u v).mpr (h u v (G.mem_edgeFinset.mp he))

theorem totalFactor_has_zero (G : SimpleGraph V) (hG : G.IsAcyclic)
    (b : Sym2 V → Bool) : ∃ x,totalFactor G b x=0 := by
  obtain ⟨x,hx⟩ := exists_cover G hG b
  exact ⟨x,(totalFactor_eq_zero_iff G b x).mpr hx⟩

/-- An actual nonempty interaction graph has a strictly positive slack.
There is no cancellation argument here: one selected factor is one and all
other factors are nonnegative. -/
theorem totalFactor_has_positive (G : SimpleGraph V) (hG : G≠⊥)
    (b : Sym2 V → Bool) : ∃ x,0< totalFactor G b x := by
  obtain ⟨e,he⟩ := G.edgeFinset_nonempty.mpr hG
  let x : V → Bool := fun _ => !(b e)
  have hone : edgeFactor b x e=1 := by
    obtain ⟨u,v⟩ := e
    rw [edgeFactor_pair]
    dsimp [x]
    cases b s(u,v) <;> norm_num [RootedResponse.realBit]
  have hle : edgeFactor b x e≤ totalFactor G b x :=
    single_le_sum (fun f hf => edgeFactor_nonneg b x f) he
  refine ⟨x,?_⟩
  rw [hone] at hle
  linarith

/-- These are unrestricted real quadratic variations written in the
edge-factor basis plus their affine remainder. The coefficients on distinct
edges remain completely independent. -/
def factorCoordinates (G : SimpleGraph V) (b : Sym2 V → Bool)
    (c : ℝ) (l : V → ℝ) (w : Sym2 V → ℝ) (x : V → Bool) : ℝ :=
  affineValue c l x+∑ e∈G.edgeFinset,w e*edgeFactor b x e

theorem weightedFactors_zero (G : SimpleGraph V) (b : Sym2 V → Bool)
    (w : Sym2 V → ℝ) (x : V → Bool) (hx : CoversLabels G b x) :
    (∑ e∈G.edgeFinset,w e*edgeFactor b x e)=0 := by
  apply sum_eq_zero
  intro e he
  obtain ⟨u,v⟩ := e
  rw [(edgeFactor_pair_eq_zero b x u v).mpr (hx u v (G.mem_edgeFinset.mp he)),mul_zero]

/-- The entire tight kernel of the positive unit-weight forest polynomial:
the arbitrary quadratic edge coefficients survive, and every affine
remainder vanishes. The equivalence uses every zero row of the actual
polynomial and has no rank or private-kernel assumption. -/
theorem factor_tight_kernel (G : SimpleGraph V) (hG : G.IsAcyclic)
    (b : Sym2 V → Bool) (c : ℝ) (l : V → ℝ) (w : Sym2 V → ℝ) :
    (∀ x,totalFactor G b x=0 → factorCoordinates G b c l w x=0) ↔
      c=0 ∧ ∀ v,l v=0 := by
  rw [← affine_vanishing_iff G hG b c l]
  constructor
  · intro h x hx
    have hz := h x ((totalFactor_eq_zero_iff G b x).mpr hx)
    simpa only [factorCoordinates,weightedFactors_zero G b w x hx,add_zero] using hz
  · intro h x hx
    have hx' := (totalFactor_eq_zero_iff G b x).mp hx
    simp only [factorCoordinates,h x hx',weightedFactors_zero G b w x hx',add_zero]

def endpointSum (x : V → ℝ) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v => x u+x v,fun _ _ => add_comm _ _⟩

@[simp] theorem endpointSum_pair (x : V → ℝ) (u v : V) :
    endpointSum x s(u,v)=x u+x v := rfl

def constantWeight (G : SimpleGraph V) (b : Sym2 V → Bool) (w : Sym2 V → ℝ) : ℝ :=
  ∑ e∈G.edgeFinset,if b e then w e else 0

def incidentWeight (G : SimpleGraph V) (b : Sym2 V → Bool)
    (w : Sym2 V → ℝ) (v : V) : ℝ :=
  ∑ e∈G.edgeFinset,if b e ∧ v∈e.toFinset then w e else 0

theorem incidentWeight_sum (G : SimpleGraph V) (b : Sym2 V → Bool)
    (w : Sym2 V → ℝ) (x : V → ℝ) :
    (∑ v,incidentWeight G b w v*x v)=
      ∑ e∈G.edgeFinset,if b e then w e*endpointSum x e else 0 := by
  simp_rw [incidentWeight,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  obtain ⟨u,v⟩ := e
  have huv : u≠ v := (G.mem_edgeFinset.mp he).ne
  cases hb : b s(u,v)
  · simp [hb]
  · simp only [hb,Bool.coe_true,true_and,ite_true,ite_mul,zero_mul]
    rw [sum_ite_mem_eq]
    simp [Sym2.toFinset_mk_eq, huv, endpointSum_pair, mul_add]

theorem weightedFactors_expansion (G : SimpleGraph V) (b : Sym2 V → Bool)
    (w : Sym2 V → ℝ) (x : V → Bool) :
    (∑ e∈G.edgeFinset,w e*edgeFactor b x e)=
      (∑ e∈G.edgeFinset,w e*ForestSigns.edgeProduct
        (fun v => RootedResponse.realBit (x v)) e)+constantWeight G b w-
        ∑ v,incidentWeight G b w v*RootedResponse.realBit (x v) := by
  rw [incidentWeight_sum]
  unfold constantWeight
  rw [← sum_add_distrib,← sum_sub_distrib]
  apply sum_congr rfl
  intro e he
  obtain ⟨u,v⟩ := e
  rw [edgeFactor_pair,ForestSigns.edgeProduct_pair,endpointSum_pair]
  cases b s(u,v) <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> ring

/-- Every ordinary quadratic polynomial on this graph has an exact
factor-coordinate representation. Thus the preceding kernel theorem loses
no constant, linear, or quadratic variations. -/
theorem quadratic_eq_factorCoordinates (G : SimpleGraph V) (b : Sym2 V → Bool)
    (c : ℝ) (l : V → ℝ) (w : Sym2 V → ℝ) (x : V → Bool) :
    ForestSigns.quadratic G c l w (fun v => RootedResponse.realBit (x v))=
      factorCoordinates G b (c-constantWeight G b w)
        (fun v => l v+incidentWeight G b w v) w x := by
  unfold factorCoordinates affineValue ForestSigns.quadratic
  rw [weightedFactors_expansion]
  simp_rw [add_mul]
  rw [sum_add_distrib]
  ring

/-- Full ordinary-coefficient form of the forest tight-kernel theorem.
All coefficients are arbitrary real numbers, and all Boolean zero rows of
the actual unit-weight polynomial are retained. -/
theorem ordinary_quadratic_tight_kernel (G : SimpleGraph V) (hG : G.IsAcyclic)
    (b : Sym2 V → Bool) (c : ℝ) (l : V → ℝ) (w : Sym2 V → ℝ) :
    (∀ x,totalFactor G b x=0 →
      ForestSigns.quadratic G c l w (fun v => RootedResponse.realBit (x v))=0) ↔
      c=constantWeight G b w ∧ ∀ v,l v= -incidentWeight G b w v := by
  simp_rw [quadratic_eq_factorCoordinates G b c l w]
  rw [factor_tight_kernel G hG b]
  constructor
  · rintro ⟨hc,hl⟩
    exact ⟨by linarith,fun v => by have hv := hl v; linarith⟩
  · rintro ⟨hc,hl⟩
    exact ⟨by linarith,fun v => by rw [hl v]; ring⟩

end ForestZeros
end GraphicalZonotopes

end
end
end BundlePart78

section BundlePart79
/- Source: Papers/GraphicalZonotopes/ThreeTreeGoodEdges.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ThreeTreeStates
open Finset
open RootedResponse
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A good edge is one contained in at least two actual tetrahedra. -/
def GoodPair (G : SimpleGraph V) (E : Finset V) : Prop :=
  2≤ Fintype.card (IncidentPairClique G E)

theorem goodPair_faces_agree {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) (E : Finset V) (hE : E.card=2)
    (hg : GoodPair G E) (C : IncidentPairClique G E) :
    let p:=complementPair G C.1 E hE C.2
    (s.clique C.1).row p.first p.second=(s.clique C.1).row p.second p.first := by
  classical
  let p:=complementPair G C.1 E hE C.2
  have hc : 1<(univ : Finset (IncidentPairClique G E)).card := by
    simpa only [card_univ] using (show 1< Fintype.card (IncidentPairClique G E) by
      exact lt_of_lt_of_le (by decide : 1<2) hg)
  obtain ⟨D,hD,hDC⟩:=exists_mem_ne hc C
  have hCD : C.1.1≠ D.1.1 := by
    intro he
    exact hDC (Subtype.ext (Subtype.ext he.symm))
  obtain ⟨T,hT,hET,hTC⟩:=h.shared_face_containing C.1.2 D.1.2 hCD C.2 D.2
  have ht3:=(mem_triangles.mp (mem_internalTriangles.mp hT).1).1
  obtain ⟨r,hr⟩:=exists_opposite (mem_filter.mp C.1.2).2.1 ht3 hTC
  have hrT : r.1∉T := by rw [← hr]; exact notMem_erase _ _
  have hrE : r.1∉E:=fun he => hrT (hET he)
  have hi : C.1.1.erase p.first.1∈internalTriangles G ∨
      C.1.1.erase p.second.1∈internalTriangles G := by
    rcases (p.mem_complement_iff r.1).mp ⟨r.2,hrE⟩ with he | he
    · left
      rw [← he,hr]
      exact hT
    · right
      rw [← he,hr]
      exact hT
  exact (s.clique C.1).agree p.first p.second p.ne hi

def linkBit (G : SimpleGraph V) (s : CompatibleRows G) {u v : V}
    (huv : G.Adj u v) (e : Sym2 V) : Bool :=
  if he : e∈(edgeLink G u v).edgeFinset then
    let C:=(pairLinkEquiv G huv).symm ⟨e,he⟩
    let p:=complementPair G C.1 {u,v} (by simp [huv.ne]) C.2
    (s.clique C.1).row p.first p.second
  else false

theorem linkBit_at_clique (G : SimpleGraph V) (s : CompatibleRows G) {u v : V}
    (huv : G.Adj u v) (C : IncidentPairClique G {u,v}) :
    linkBit G s huv (pairLinkEquiv G huv C).1=
      let p:=complementPair G C.1 {u,v} (by simp [huv.ne]) C.2
      (s.clique C.1).row p.first p.second := by
  simp only [linkBit,dif_pos (pairLinkEquiv G huv C).2]
  let F : IncidentPairClique G {u,v} → Bool := fun D =>
    let p:=complementPair G D.1 {u,v} (by simp [huv.ne]) D.2
    (s.clique D.1).row p.first p.second
  change F ((pairLinkEquiv G huv).symm ((pairLinkEquiv G huv) C)) = F C
  rw [Equiv.symm_apply_apply]

theorem pairFactor_eq_edgeFactor {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v)
    (hg : GoodPair G {u,v}) (C : IncidentPairClique G {u,v}) (x : V → Bool) :
    pairFactor G s {u,v} (by simp [huv.ne]) C (fun w => realBit (x w))=
      ForestZeros.edgeFactor (linkBit G s huv) x (pairLinkEquiv G huv C).1 := by
  let p:=complementPair G C.1 {u,v} (by simp [huv.ne]) C.2
  have he:=goodPair_faces_agree h s {u,v} (by simp [huv.ne]) hg C
  have hb:=linkBit_at_clique G s huv C
  rw [pairLinkEquiv_eq] at hb ⊢
  rw [ForestZeros.edgeFactor_pair,hb]
  change ((p.maximum (s.clique C.1).row : ℤ) : ℝ)-
      realBit ((s.clique C.1).row p.first p.second)*realBit (x p.second.1)-
      realBit ((s.clique C.1).row p.second p.first)*realBit (x p.first.1)+
      realBit (x p.first.1)*realBit (x p.second.1)=
      if (s.clique C.1).row p.first p.second then
        (1-realBit (x p.first.1))*(1-realBit (x p.second.1))
      else realBit (x p.first.1)*realBit (x p.second.1)
  unfold ComplementPair.maximum
  rw [← he]
  cases (s.clique C.1).row p.first p.second <;>
    cases x p.first.1 <;> cases x p.second.1 <;> norm_num [realBit,RootedResponse.integerBit]

/-- For a good edge the constructed elemental row is exactly the
positive unit-weight forest polynomial. This identifies its entire zero
locus, including every ambient Boolean coordinate. -/
theorem elemental_good_factorization {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v)
    (hg : GoodPair G {u,v}) (x : V → Bool) :
    delta (setFunction h s) u v
      (((booleanSupport (fun w => realBit (x w))).erase u).erase v)=
      ForestZeros.totalFactor (edgeLink G u v) (linkBit G s huv) x := by
  rw [elemental_factorization h s huv x]
  simp_rw [pairFactor_eq_edgeFactor h s huv hg]
  unfold ForestZeros.totalFactor
  conv_rhs => rw [← sum_coe_sort]
  exact (pairLinkEquiv G huv).sum_comp
    (fun e => ForestZeros.edgeFactor (linkBit G s huv) x e.1)

def TightVariation (z f : SetFunction V) : Prop :=
  ∀ u v,u≠ v → ∀ A,u∉A → v∉A → delta z u v A=0 → delta f u v A=0

theorem tightVariation_cliqueSupported {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {f : SetFunction V}
    (hn : TranslationNormalized f) (hf : TightVariation (setFunction h s) f) :
    CliqueSupported G (mobius f) := by
  apply (mobius_cliqueSupported_iff G f).mpr
  refine ⟨hn,?_⟩
  intro u v huv hnon A hu hv
  exact hf u v huv A hu hv ((setFunction_normalized_graphical h s).2 u v huv hnon A hu hv)

/-- A complete ordinary-coefficient kernel equation for each good edge.
No scalar relation is assumed for the tetrahedral coefficients of the
variation; they remain arbitrary real numbers in the displayed sums. -/
theorem good_edge_tight_kernel {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {f : SetFunction V}
    (hn : TranslationNormalized f) (hf : TightVariation (setFunction h s) f)
    {u v : V} (huv : G.Adj u v) (hg : GoodPair G {u,v}) :
    edgeCoefficients (mobius f) u v ∅=
      ForestZeros.constantWeight (edgeLink G u v) (linkBit G s huv)
        (fun e => edgeCoefficients (mobius f) u v e.toFinset) ∧
    ∀ w,edgeCoefficients (mobius f) u v {w}=
      -ForestZeros.incidentWeight (edgeLink G u v) (linkBit G s huv)
        (fun e => edgeCoefficients (mobius f) u v e.toFinset) w := by
  apply (ForestZeros.ordinary_quadratic_tight_kernel (edgeLink G u v)
    (h.edgeLink_acyclic huv) (linkBit G s huv) _ _ _).mp
  intro x hx
  rw [edgeCoefficients_boolean_quadratic (tightVariation_cliqueSupported h s hn hf)
    (fun C hC => h.clique_card_le_four hC) huv.ne _
      (fun w => by cases x w <;> simp [realBit]),zeta_mobius]
  apply hf u v huv.ne _ (by simp) (by simp)
  rw [elemental_good_factorization h s huv hg x]
  exact hx

end ThreeTreeStates
end GraphicalZonotopes

end
end
end BundlePart79

section BundlePart80
/- Source: Papers/GraphicalZonotopes/ThreeTreeKernelColumns.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ThreeTreeStates
open Finset
open RootedResponse
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem weighted_column_eq_sum_pairLinear (G : SimpleGraph V) (s : CompatibleRows G)
    (lam : ↥(tetrahedra G) → ℝ) (E : Finset V) (hE : E.card=2)
    (w : V) (hw : w∉E) (T : Finset V) (hT : T∈triangles G)
    (he : T=insert w E) (hwT : w∈T) :
    (∑ C : AllIncidentClique G ⟨T,hT⟩,
      lam C.1*realBit (faceRow G s ⟨T,hT⟩ C ⟨w,hwT⟩))=
      ∑ C : IncidentPairClique G E,lam C.1*pairLinear G s E hE C w := by
  classical
  subst T
  calc
    _=∑ C : {C : IncidentPairClique G E // w∈C.1.1},
        lam C.1.1*pairLinear G s E hE C.1 w := by
      apply Fintype.sum_equiv (pairTriangleIncidenceEquiv G E w hT)
      intro C
      rw [faceRow_eq_pairLinear G s E hE w hw hT C]
      rfl
    _=∑ C∈(univ : Finset (IncidentPairClique G E)).filter (fun C => w∈C.1.1),
        lam C.1*pairLinear G s E hE C w :=
      (sum_subtype ((univ : Finset (IncidentPairClique G E)).filter (fun C => w∈C.1.1))
        (by intro C; simp) (fun C => lam C.1*pairLinear G s E hE C w)).symm
    _=_ := by
      apply sum_subset (filter_subset _ _)
      intro C hC hnot
      rw [pairLinear_eq_zero_of_notMem G s E hE C w
        (fun hwC => hnot (mem_filter.mpr ⟨hC,hwC⟩)),mul_zero]

theorem edgeCoefficients_at_clique (G : SimpleGraph V) {u v : V} (huv : G.Adj u v)
    (y : SetFunction V) (C : IncidentPairClique G {u,v}) :
    edgeCoefficients y u v ((pairLinkEquiv G huv C).1).toFinset=y C.1.1 := by
  rw [pairLinkEquiv_toFinset,edgeCoefficients,if_pos (by simp)]
  have hu : u∈C.1.1:=C.2 (by simp)
  have hv : v∈C.1.1:=C.2 (by simp)
  have he : insert u (insert v ((C.1.1.erase u).erase v))=C.1.1 := by
    ext w
    by_cases hwu : w=u <;> by_cases hwv : w=v <;> simp [hwu,hwv,hu,hv]
  rw [he]

/-- The forest-kernel linear coefficient is the actual weighted sum of
the incident tetrahedron face bits, with arbitrary real tetrahedron weights. -/
theorem incidentWeight_eq_pairLinear {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v)
    (hg : GoodPair G {u,v}) (y : SetFunction V) (w : V) :
    ForestZeros.incidentWeight (edgeLink G u v) (linkBit G s huv)
      (fun e => edgeCoefficients y u v e.toFinset) w=
      ∑ C : IncidentPairClique G {u,v},y C.1.1*
        pairLinear G s {u,v} (by simp [huv.ne]) C w := by
  classical
  unfold ForestZeros.incidentWeight
  rw [← sum_coe_sort]
  symm
  apply Fintype.sum_equiv (pairLinkEquiv G huv)
  intro C
  let p:=complementPair G C.1 {u,v} (by simp [huv.ne]) C.2
  have hagree:=goodPair_faces_agree h s {u,v} (by simp [huv.ne]) hg C
  have hbit:=linkBit_at_clique G s huv C
  dsimp only
  rw [edgeCoefficients_at_clique G huv y C,hbit,pairLinkEquiv_eq,Sym2.toFinset_mk_eq]
  change y C.1.1*(if w=p.first.1 then realBit ((s.clique C.1).row p.second p.first)
    else if w=p.second.1 then realBit ((s.clique C.1).row p.first p.second) else 0)=
      if (s.clique C.1).row p.first p.second = true ∧ w ∈ ({p.first.1,p.second.1} : Finset V)
      then y C.1.1 else 0
  change (s.clique C.1).row p.first p.second = (s.clique C.1).row p.second p.first at hagree
  rw [← hagree]
  by_cases hwa : w=p.first.1 <;> by_cases hwb : w=p.second.1 <;>
    cases (s.clique C.1).row p.first p.second <;>
    simp [hwa,hwb,realBit]

theorem good_pair_linear_relation {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {f : SetFunction V}
    (hn : TranslationNormalized f) (hf : TightVariation (setFunction h s) f)
    (E : Finset V) (hE : E∈edgeFamily G) (hg : GoodPair G E)
    (w : V) (hw : w∉E) :
    mobius f (insert w E)=
      -(∑ C : IncidentPairClique G E,mobius f C.1.1*
        pairLinear G s E ((mem_edgeFamily G E).mp hE).1 C w) := by
  obtain ⟨u,v,huv,rfl⟩:=card_eq_two.mp ((mem_edgeFamily G E).mp hE).1
  have hedge:=(pair_mem_edgeFamily G huv).mp hE
  have hlin:=(good_edge_tight_kernel h s hn hf hedge hg).2 w
  rw [incidentWeight_eq_pairLinear h s hedge hg] at hlin
  have hwu : w≠ u:=fun he => hw (by simp [he])
  have hwv : w≠ v:=fun he => hw (by simp [he])
  rw [edgeCoefficients,if_pos (by simp [hwu.symm,hwv.symm])] at hlin
  have he : insert u (insert v ({w} : Finset V))=insert w {u,v} := by
    ext a
    simp only [mem_insert,mem_singleton]
    tauto
  simpa only [he] using hlin

theorem goodPair_of_internalTriangle (G : SimpleGraph V) (T : ↥(internalTriangles G))
    (E : Finset V) (hET : E⊆T.1) : GoodPair G E := by
  have hlow:=(mem_internalTriangles.mp T.2).2
  rw [← incidentClique_card G T] at hlow
  apply hlow.trans
  apply Fintype.card_le_of_injective
    (fun C : IncidentClique G T => (⟨C.1,hET.trans C.2⟩ : IncidentPairClique G E))
  intro C D he
  apply Subtype.ext
  simpa only using congrArg (fun x : IncidentPairClique G E => x.1) he

/-- Each internal triangle sees a constant weighted response across all
three of its edge coordinates. The equation is derived from the complete
zero rows of the actual constructed polytope. -/
theorem internal_triangle_relation {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {f : SetFunction V}
    (hn : TranslationNormalized f) (hf : TightVariation (setFunction h s) f)
    (T : ↥(internalTriangles G)) (j : ↥T.1) :
    (∑ C : IncidentClique G T,mobius f C.1.1*realBit ((s.triangle T).row C j))=
      -mobius f T.1 := by
  classical
  let E:=T.1.erase j.1
  have hEcard : E.card=2 := by
    dsimp only [E]
    rw [card_erase_of_mem j.2,(mem_triangles.mp (mem_internalTriangles.mp T.2).1).1]
  have hE : E∈edgeFamily G:= (mem_edgeFamily G E).mpr ⟨hEcard,
    fun u hu v hv huv => (mem_triangles.mp (mem_internalTriangles.mp T.2).1).2
      (mem_of_mem_erase hu) (mem_of_mem_erase hv) huv⟩
  have hjE : j.1∉E:=notMem_erase _ _
  have hlin:=good_pair_linear_relation h s hn hf E hE
    (goodPair_of_internalTriangle G T E (erase_subset _ _)) j.1 hjE
  have he : T.1=insert j.1 E := (insert_erase j.2).symm
  rw [← he] at hlin
  have hcol:=weighted_column_eq_sum_pairLinear G s (fun C => mobius f C.1)
    E hEcard j.1 hjE T.1 (mem_internalTriangles.mp T.2).1 he j.2
  have hport : ∀ C : IncidentClique G T,
      faceRow G s ⟨T.1,(mem_internalTriangles.mp T.2).1⟩ C j=(s.triangle T).row C j := by
    intro C
    exact congrArg (fun r : ↥T.1 → Bool => r j) (s.port_eq C.1 T C.2)
  simp_rw [hport] at hcol
  rw [← hcol] at hlin
  linarith

theorem incident_clique_scales_equal {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {f : SetFunction V}
    (hn : TranslationNormalized f) (hf : TightVariation (setFunction h s) f)
    (T : ↥(internalTriangles G)) (C D : IncidentClique G T) :
    mobius f C.1.1=mobius f D.1.1 :=
  (s.triangle T).kernel (fun C => mobius f C.1.1) (-mobius f T.1)
    (internal_triangle_relation h s hn hf T) C D

end ThreeTreeStates
end GraphicalZonotopes

end
end
end BundlePart80

section BundlePart81
/- Source: Papers/GraphicalZonotopes/ThreeTreeKernelRigidity.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ThreeTreeStates
open Finset
open RootedResponse
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem adjacent_clique_scales_equal {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {f : SetFunction V}
    (hn : TranslationNormalized f) (hf : TightVariation (setFunction h s) f)
    {C D : Finset V} (hCD : (TriangleComponents.cliqueGraph G).Adj C D) :
    mobius f C=mobius f D := by
  obtain ⟨T,hTsub,hTcard⟩:=exists_subset_card_eq hCD.2.2.2.2.2
  have hTC : T⊆C:=hTsub.trans inter_subset_left
  have hTD : T⊆D:=hTsub.trans inter_subset_right
  have hC : C∈tetrahedra G:=mem_filter.mpr ⟨mem_univ _,hCD.1,hCD.2.2.1⟩
  have hD : D∈tetrahedra G:=mem_filter.mpr ⟨mem_univ _,hCD.2.1,hCD.2.2.2.1⟩
  have hT:=internal_triangle_of_shared hC hD hCD.2.2.2.2.1 hTcard hTC hTD
  exact incident_clique_scales_equal h s hn hf ⟨T,hT⟩ ⟨⟨C,hC⟩,hTC⟩ ⟨⟨D,hD⟩,hTD⟩

/-- Every actual tetrahedral coefficient of a tight variation is a common
real scalar. Propagation uses paths in the graph of all actual tetrahedra,
not a selected subfamily. -/
theorem all_clique_scales_equal {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {f : SetFunction V}
    (hn : TranslationNormalized f) (hf : TightVariation (setFunction h s) f) :
    ∃ a : ℝ,∀ C∈tetrahedra G,mobius f C=a := by
  obtain ⟨C₀,hC₀⟩:=h.tetrahedra_nonempty
  refine ⟨mobius f C₀,?_⟩
  intro C hC
  have hp:=h.tetrahedra_reachable hC hC₀
  rw [SimpleGraph.reachable_eq_reflTransGen] at hp
  induction hp with
  | refl => rfl
  | @tail D E hD hDE ih =>
    have hmD : D ∈ tetrahedra G := mem_filter.mpr ⟨mem_univ _,hDE.1,hDE.2.2.1⟩
    exact (ih hmD).trans (adjacent_clique_scales_equal h s hn hf hDE)

theorem triangle_coefficient_of_good_pair {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {f : SetFunction V}
    (hn : TranslationNormalized f) (hf : TightVariation (setFunction h s) f)
    (a : ℝ) (ha : ∀ C∈tetrahedra G,mobius f C=a)
    (T : ↥(triangles G)) (j : ↥T.1) (hg : GoodPair G (T.1.erase j.1)) :
    mobius f T.1=a*coefficients h s T.1 := by
  classical
  let E:=T.1.erase j.1
  have hEcard : E.card=2 := by
    dsimp only [E]
    rw [card_erase_of_mem j.2,(mem_triangles.mp T.2).1]
  have hE : E∈edgeFamily G:= (mem_edgeFamily G E).mpr ⟨hEcard,
    fun u hu v hv huv => (mem_triangles.mp T.2).2
      (mem_of_mem_erase hu) (mem_of_mem_erase hv) huv⟩
  have hjE : j.1∉E:=notMem_erase _ _
  have he : T.1=insert j.1 E := (insert_erase j.2).symm
  have hlin:=good_pair_linear_relation h s hn hf E hE hg j.1 hjE
  rw [← he] at hlin
  have hcol:=weighted_column_eq_sum_pairLinear G s (fun C => mobius f C.1)
    E hEcard j.1 hjE T.1 T.2 he j.2
  rw [← hcol] at hlin
  have hweights : ∀ C : AllIncidentClique G T,mobius f C.1.1=a:=fun C => ha C.1.1 C.1.2
  simp_rw [hweights] at hlin
  rw [← mul_sum] at hlin
  change mobius f T.1= -(a*columnValue G s T j) at hlin
  rw [column_eq_triangleWeight h s T j] at hlin
  rw [coefficients_triangle h s T.2,hlin]
  ring

/-- If the 3-tree has at least two tetrahedra, every triangle contains a
good edge. For a leaf triangle, use its intersection with an internal face
of its unique incident tetrahedron. -/
theorem triangle_has_good_pair {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (hm : 2≤(tetrahedra G).card) (T : ↥(triangles G)) :
    ∃ j : ↥T.1,GoodPair G (T.1.erase j.1) := by
  classical
  by_cases hT : T.1∈internalTriangles G
  · obtain ⟨w,hw⟩:=card_pos.mp (by rw [(mem_triangles.mp T.2).1]; decide)
    exact ⟨⟨w,hw⟩,goodPair_of_internalTriangle G ⟨T.1,hT⟩ _ (erase_subset _ _)⟩
  · obtain ⟨C,hC,hTC⟩:=h.triangle_extends (mem_triangles.mp T.2).1 (mem_triangles.mp T.2).2
    obtain ⟨D,hD,hDC⟩:=exists_mem_ne (show 1<(tetrahedra G).card by omega) C
    obtain ⟨F,hF,hEF,hFC⟩:=h.shared_face_containing hC hD hDC.symm
      (E:=∅) (empty_subset _) (empty_subset _)
    have hFcard:=(mem_triangles.mp (mem_internalTriangles.mp hF).1).1
    obtain ⟨r,hr⟩:=exists_opposite (mem_filter.mp hC).2.1 hFcard hFC
    have hrT : r.1∈T.1 := by
      by_contra hrT
      have hTF : T.1⊆F := by
        rw [← hr]
        intro w hw
        exact mem_erase.mpr ⟨fun he => hrT (he ▸ hw),hTC hw⟩
      have he : T.1=F:=eq_of_subset_of_card_le hTF (by
        rw [(mem_triangles.mp T.2).1,hFcard])
      exact hT (he.symm ▸ hF)
    refine ⟨⟨r.1,hrT⟩,goodPair_of_internalTriangle G ⟨F,hF⟩ _ ?_⟩
    simpa only [← hr] using erase_subset_erase r.1 hTC

theorem all_triangle_coefficients_scaled {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) (hm : 2≤(tetrahedra G).card)
    {f : SetFunction V} (hn : TranslationNormalized f)
    (hf : TightVariation (setFunction h s) f)
    (a : ℝ) (ha : ∀ C∈tetrahedra G,mobius f C=a) :
    ∀ T∈triangles G,mobius f T=a*coefficients h s T := by
  intro T hT
  obtain ⟨j,hj⟩:=triangle_has_good_pair h hm ⟨T,hT⟩
  exact triangle_coefficient_of_good_pair h s hn hf a ha ⟨T,hT⟩ j hj

end ThreeTreeStates
end GraphicalZonotopes

end
end
end BundlePart81

section BundlePart82
/- Source: Papers/GraphicalZonotopes/ThreeTreeMaximal.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every clique in the active vertex set of a 3-tree extends to an
actual tetrahedron. This includes empty sets, vertices and edges, rather
than only the triangular separators used in the construction. -/
theorem ThreeTreeOn.clique_extends {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {C : Finset V} (hCS : C⊆S) (hC : G.IsClique C) :
    ∃ D∈tetrahedra G,C⊆D := by
  classical
  induction h generalizing C with
  | tetrahedron A hA =>
    exact ⟨A,by rw [tetrahedra_cliqueGraph hA]; simp,hCS⟩
  | @attach S G h u hu A hA hAS hcA ih =>
    by_cases huC : u∈C
    · refine ⟨insert u A,?_,?_⟩
      · rw [tetrahedra_after_attachment h hu hA hAS hcA]
        exact mem_insert_self _ _
      · intro v hv
        by_cases hvu : v=u
        · exact mem_insert.mpr (Or.inl hvu)
        · exact mem_insert.mpr (Or.inr
            ((attached_vertex_adj_iff h hu hAS v).mp (hC huC hv (Ne.symm hvu))))
    · have hCold : C⊆S := by
        intro v hv
        rcases mem_insert.mp (hCS hv) with he | hvS
        · exact False.elim (huC (he ▸ hv))
        · exact hvS
      obtain ⟨D,hD,hCD⟩ := ih hCold (clique_before_attachment huC hC)
      exact ⟨D,by
        rw [tetrahedra_after_attachment h hu hA hAS hcA]
        exact mem_insert_of_mem hD,hCD⟩

/-- In the full 3-tree, the finite tetrahedra used by the coefficient
formalization are exactly the ordinary maximal cliques of the paper. -/
theorem IsThreeTree.maximalClique_iff {G : SimpleGraph V} (h : IsThreeTree G)
    (C : Finset V) : Maximal G.IsClique (C : Set V) ↔ C∈tetrahedra G := by
  classical
  constructor
  · intro hmax
    obtain ⟨D,hD,hCD⟩ := h.clique_extends (subset_univ C) hmax.1
    have hDC : D⊆C := hmax.2 (mem_filter.mp hD).2.2 hCD
    have he : C=D := subset_antisymm hCD hDC
    simpa only [he] using hD
  · intro hC
    obtain ⟨hc,hcl⟩ := (mem_filter.mp hC).2
    apply SimpleGraph.IsMaximumClique.isMaximalClique C
    refine ⟨hcl,?_⟩
    intro D hD
    rw [hc]
    exact h.clique_card_le_four hD

end GraphicalZonotopes

end
end
end BundlePart82

section BundlePart83
/- Source: Papers/GraphicalZonotopes/ThreeTreeConstructionBounds.lean -/







@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace ThreeTreeStates
open Finset
open RootedResponse
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

def contextBits (A : Finset V) (w : V) : Bool := decide (w∈A)

theorem booleanSupport_contextBits (A : Finset V) :
    booleanSupport (fun w => realBit (contextBits A w))=A := by
  ext w
  by_cases hw : w∈A <;> simp [booleanSupport,contextBits,realBit,hw]

theorem elemental_factorization_context {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v)
    (A : Finset V) (hu : u∉A) (hv : v∉A) :
    delta (setFunction h s) u v A=
      ∑ C : IncidentPairClique G {u,v},pairFactor G s {u,v} (by simp [huv.ne]) C
        (fun w => realBit (contextBits A w)) := by
  simpa only [booleanSupport_contextBits,erase_eq_of_notMem hu,erase_eq_of_notMem hv]
    using elemental_factorization h s huv (contextBits A)

theorem elemental_bounds_incident {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v)
    (A : Finset V) (hu : u∉A) (hv : v∉A) :
    0≤ delta (setFunction h s) u v A ∧
      delta (setFunction h s) u v A≤(Fintype.card (IncidentPairClique G {u,v}) : ℝ) := by
  rw [elemental_factorization_context h s huv A hu hv]
  constructor
  · apply sum_nonneg
    intro C hC
    rcases pairFactor_zero_or_one G s {u,v} (by simp [huv.ne]) C (contextBits A)
      with he | he <;> simp only [he] <;> norm_num
  · calc
      _≤∑ _ : IncidentPairClique G {u,v},(1 : ℝ) := by
        apply sum_le_sum
        intro C hC
        rcases pairFactor_zero_or_one G s {u,v} (by simp [huv.ne]) C (contextBits A)
          with he | he <;> simp only [he] <;> norm_num
      _=_ := by simp

theorem incidentPairClique_card_le {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (E : Finset V) :
    Fintype.card (IncidentPairClique G E)≤ S.card-3 := by
  calc
    _≤ Fintype.card ↥(tetrahedra G) :=
      Fintype.card_le_of_injective (fun C => C.1) (fun C D he => Subtype.ext he)
    _=S.card-3 := by rw [Fintype.card_coe,h.tetrahedra_card]

/-- The original unbounded graph, with all of its conditioning sets,
satisfies the full supermodular inequalities. No subset of rows is used. -/
theorem setFunction_supermodular {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) : Supermodular (setFunction h s) := by
  apply ElementallyNonnegative.supermodular
  intro u v huv A hu hv
  by_cases hedge : G.Adj u v
  · exact (elemental_bounds_incident h s hedge A hu hv).1
  · rw [(setFunction_normalized_graphical h s).2 u v huv hedge A hu hv]

theorem elemental_bound {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v)
    (A : Finset V) (hu : u∉A) (hv : v∉A) :
    delta (setFunction h s) u v A≤((S.card-3 : ℕ) : ℝ) := by
  apply (elemental_bounds_incident h s huv A hu hv).2.trans
  exact_mod_cast incidentPairClique_card_le h ({u,v} : Finset V)

theorem setFunction_lattice {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) : LatticePolytope (basePolytope (setFunction h s)) :=
  (setFunction_integerValued h s).basePolytope (setFunction_normalized_graphical h s).1.1
    (setFunction_supermodular h s)

/-- The construction is an actual summand of the stated dilation of the
ordinary graphical zonotope, including its compact convex complement. -/
theorem setFunction_actual_summand {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) :
    IsMinkowskiSummand (basePolytope (setFunction h s))
      (((S.card-3 : ℕ) : ℝ) • graphicalZonotope G) := by
  apply (isMinkowskiSummand_graphical_iff (setFunction_normalized_graphical h s).1.1
    (setFunction_supermodular h s) (Nat.cast_nonneg _)).mpr
  exact ⟨(setFunction_normalized_graphical h s).2,
    fun u v huv hedge A hu hv => elemental_bound h s hedge A hu hv⟩

/-- A coefficient-one tetrahedron forces a nonzero elemental row at each
of its edges. Nonnegativity then makes that row strictly positive. -/
theorem exists_positive_edge_slack {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v) :
    ∃ A : Finset V,u∉A ∧ v∉A ∧ 0< delta (setFunction h s) u v A := by
  classical
  by_contra hn
  push_neg at hn
  have hz : ∀ A : Finset V,u∉A → v∉A → delta (setFunction h s) u v A=0 := by
    intro A hu hv
    exact le_antisymm (hn A hu hv) ((setFunction_supermodular h s).elemental u v huv.ne A hu hv)
  have hy := (nonedge_coefficients_zero_iff (coefficients h s) huv.ne).mp hz
  obtain ⟨C,hC,hEC⟩ := h.clique_extends
    (C:=({u,v} : Finset V)) (by
      simpa only [insert_subset_iff,singleton_subset_iff] using h.edges_supported huv)
    (((mem_edgeFamily G {u,v}).mp ((pair_mem_edgeFamily G huv.ne).mpr huv)).2)
  have hc:=hy C (hEC (by simp)) (hEC (by simp))
  rw [coefficients_tetrahedron h s hC] at hc
  norm_num at hc

theorem setFunction_direction_graph {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) :
    actualDirectionGraph (basePolytope (setFunction h s))=G := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  constructor
  · intro he
    obtain ⟨R,hR,hRc,hnR,hadd⟩:=setFunction_actual_summand h s
    exact basePolytope_summand_actualRootEdge (setFunction_normalized_graphical h s).1.1
      (setFunction_supermodular h s) G (Nat.cast_nonneg _) R hadd he
  · intro huv
    obtain ⟨A,hu,hv,hpos⟩:=exists_positive_edge_slack h s huv
    exact exposedSegment_of_positive_delta (setFunction_normalized_graphical h s).1.1
      (setFunction_supermodular h s) huv.ne hu hv hpos

end ThreeTreeStates
end GraphicalZonotopes

end
end
end BundlePart83

section BundlePart84
/- Source: Papers/GraphicalZonotopes/ThreeTreeTightKernel.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ThreeTreeStates
open Finset
open RootedResponse
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem zeta_pairSupported_delta_unordered (y : SetFunction V)
    (hy : ∀ C, C.card ≠ 2 → y C = 0) {u v : V} (huv : u ≠ v)
    {S : Finset V} (hu : u ∉ S) (hv : v ∉ S) :
    delta (zeta y) u v S = y {u,v} := by
  rw [delta_zeta huv hu hv]
  refine Finset.sum_eq_single (s := (insert u (insert v S)).powerset.filter
    (fun C => u ∈ C ∧ v ∈ C)) (f := y) ({u,v} : Finset V) ?_ ?_
  · intro C hC hne
    apply hy C
    intro hcard
    have hmem := (mem_filter.mp hC).2
    have hsub : ({u,v} : Finset V) ⊆ C :=
      insert_subset hmem.1 (singleton_subset_iff.mpr hmem.2)
    have he : ({u,v} : Finset V) = C := eq_of_subset_of_card_le hsub (by
      simpa [huv] using le_of_eq hcard)
    exact hne he.symm
  · intro hnot
    exact False.elim (hnot (by simp))

theorem pairFactor_has_zero (G : SimpleGraph V) (s : CompatibleRows G)
    (E : Finset V) (hE : E.card=2) (C : IncidentPairClique G E) :
    ∃ x : V → Bool,pairFactor G s E hE C (fun w => realBit (x w))=0 := by
  let p:=complementPair G C.1 E hE C.2
  let a:=(s.clique C.1).row p.first p.second
  let b:=(s.clique C.1).row p.second p.first
  let x : V → Bool:=Function.update (fun _ => a) p.first.1 b
  refine ⟨x,?_⟩
  have hx1 : x p.first.1=b:=by simp [x]
  have hx2 : x p.second.1=a:=Function.update_of_ne p.ne_val.symm _ _
  change ((max (RootedResponse.integerBit a) (RootedResponse.integerBit b) : ℤ) : ℝ)-
    realBit a*realBit (x p.second.1)-realBit b*realBit (x p.first.1)+
    realBit (x p.first.1)*realBit (x p.second.1)=0
  rw [hx1,hx2]
  cases a <;> cases b <;> norm_num [realBit,RootedResponse.integerBit]

theorem edge_has_zero_slack {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v) :
    ∃ A : Finset V,u∉A ∧ v∉A ∧ delta (setFunction h s) u v A=0 := by
  classical
  by_cases hg : GoodPair G {u,v}
  · obtain ⟨x,hx⟩:=ForestZeros.totalFactor_has_zero (edgeLink G u v)
      (h.edgeLink_acyclic huv) (linkBit G s huv)
    refine ⟨((booleanSupport (fun w => realBit (x w))).erase u).erase v,
      by simp,by simp,?_⟩
    rw [elemental_good_factorization h s huv hg x]
    exact hx
  · obtain ⟨D,hD,hED⟩:=h.clique_extends (C:=({u,v} : Finset V))
      (by simpa only [insert_subset_iff,singleton_subset_iff] using h.edges_supported huv)
      (((mem_edgeFamily G {u,v}).mp ((pair_mem_edgeFamily G huv.ne).mpr huv)).2)
    let C : IncidentPairClique G {u,v}:=⟨⟨D,hD⟩,hED⟩
    have hpos : 0< Fintype.card (IncidentPairClique G {u,v}):=
      Fintype.card_pos_iff.mpr ⟨C⟩
    have hone : Fintype.card (IncidentPairClique G {u,v})=1 := by
      unfold GoodPair at hg
      omega
    have hsub : Subsingleton (IncidentPairClique G {u,v}):=
      Fintype.card_le_one_iff_subsingleton.mp hone.le
    obtain ⟨x,hx⟩:=pairFactor_has_zero G s {u,v} (by simp [huv.ne]) C
    refine ⟨((booleanSupport (fun w => realBit (x w))).erase u).erase v,
      by simp,by simp,?_⟩
    rw [elemental_factorization h s huv x]
    rw [sum_eq_single C]
    · exact hx
    · intro D hD hDC
      exact False.elim (hDC (hsub.elim _ _))
    · intro hn
      exact False.elim (hn (mem_univ C))

theorem cliqueSupported_zero_of_not_clique {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y) {C : Finset V} (hc : ¬G.IsClique C) : y C=0 := by
  by_contra hn
  exact hc (hy.clique_of_nonzero hn)

/-- After recovering every actual tetrahedron and triangle coefficient,
the full Möbius residual is supported on pairs. No clique or higher-degree
coordinates are omitted from this assertion. -/
theorem residual_pair_supported {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) (hm : 2≤(tetrahedra G).card)
    {f : SetFunction V} (hn : TranslationNormalized f)
    (hf : TightVariation (setFunction h s) f)
    (a : ℝ) (ha : ∀ C∈tetrahedra G,mobius f C=a) :
    ∀ C,C.card≠2 → (mobius f-a • coefficients h s) C=0 := by
  have hy:=tightVariation_cliqueSupported h s hn hf
  have hz:=coefficients_cliqueSupported h s
  have htri:=all_triangle_coefficients_scaled h s hm hn hf a ha
  intro C hc2
  change mobius f C-a*coefficients h s C=0
  by_cases hcl : G.IsClique C
  · have hcard:=h.clique_card_le_four hcl
    have hc : C.card=0 ∨ C.card=1 ∨ C.card=3 ∨ C.card=4 := by omega
    rcases hc with hc | hc | hc | hc
    · have he : C=∅:=card_eq_zero.mp hc
      rw [he,hy.1,hz.1,mul_zero,sub_zero]
    · obtain ⟨v,rfl⟩:=card_eq_one.mp hc
      rw [hy.2.1 v,hz.2.1 v,mul_zero,sub_zero]
    · rw [htri C (mem_triangles.mpr ⟨hc,hcl⟩),sub_self]
    · have hC : C∈tetrahedra G:=mem_filter.mpr ⟨mem_univ _,hc,hcl⟩
      rw [ha C hC,coefficients_tetrahedron h s hC,mul_one,sub_self]
  · rw [cliqueSupported_zero_of_not_clique hy hcl,
      cliqueSupported_zero_of_not_clique hz hcl,mul_zero,sub_zero]

/-- The complete normalized tight kernel for the constructed ray on any
3-tree with at least two tetrahedra. All real set functions are quantified,
and support is deduced from the original nonedge zero rows. -/
theorem complete_tight_kernel {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) (hm : 2≤(tetrahedra G).card)
    (f : SetFunction V) (hn : TranslationNormalized f)
    (hf : TightVariation (setFunction h s) f) :
    ∃ a : ℝ,f=a • setFunction h s := by
  classical
  obtain ⟨a,ha⟩:=all_clique_scales_equal h s hn hf
  let y:=mobius f-a • coefficients h s
  have hyp : ∀ C,C.card≠2 → y C=0:=residual_pair_supported h s hm hn hf a ha
  have hyf:=tightVariation_cliqueSupported h s hn hf
  have hyz:=coefficients_cliqueSupported h s
  have hzeta : zeta y=f-a • setFunction h s := by
    change zetaLinear (mobius f-a • coefficients h s)=_
    rw [map_sub,map_smul]
    change zeta (mobius f)-a • zeta (coefficients h s)=_
    rw [zeta_mobius]
    rfl
  have hy0 : y=0 := by
    funext C
    by_cases hc2 : C.card=2
    · obtain ⟨u,v,huv,rfl⟩:=card_eq_two.mp hc2
      by_cases hedge : G.Adj u v
      · obtain ⟨A,hu,hv,hA⟩:=edge_has_zero_slack h s hedge
        have hvar:=hf u v huv A hu hv hA
        have hrow:=zeta_pairSupported_delta_unordered y hyp huv hu hv
        rw [hzeta,delta_sub,delta_smul,hvar,hA,mul_zero,sub_zero] at hrow
        exact hrow.symm
      · change mobius f {u,v}-a*coefficients h s {u,v}=0
        rw [hyf.2.2 {u,v} u v (by simp) (by simp) huv hedge,
          hyz.2.2 {u,v} u v (by simp) (by simp) huv hedge,mul_zero,sub_zero]
    · exact hyp C hc2
  refine ⟨a,sub_eq_zero.mp ?_⟩
  rw [← hzeta,hy0]
  exact (zeta_eq_zero_iff _).mpr rfl

theorem setFunction_extreme {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) (hm : 2≤(tetrahedra G).card) :
    ExtremeSupermodular (setFunction h s) :=
  extremeSupermodular_of_tightEquations (setFunction_normalized_graphical h s).1
    (setFunction_supermodular h s) (setFunction_ne_zero h s)
    (complete_tight_kernel h s hm)

end ThreeTreeStates
end GraphicalZonotopes

end
end
end BundlePart84

section BundlePart85
/- Source: Papers/GraphicalZonotopes/SimplexRay.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem setMonomial_translationNormalized {C : Finset V} (hC : 2≤ C.card) :
    TranslationNormalized (setMonomial C) := by
  refine ⟨setMonomial_normalized (card_pos.mp (by omega)),?_⟩
  intro v
  have hnot : ¬C⊆{v} := by
    intro hs
    have hc:=card_le_card hs
    simp only [card_singleton] at hc
    omega
  simp only [setMonomial,if_neg hnot]

theorem setMonomial_graphical (C : Finset V) : Graphical (cliqueGraph C) (setMonomial C) := by
  intro u v huv hnon A hu hv
  rw [delta_setMonomial huv hu hv]
  apply if_neg
  rintro ⟨huC,hvC,hsub⟩
  exact hnon ⟨huv,huC,hvC⟩

theorem zeta_single_coefficient (C : Finset V) (a : ℝ) :
    zeta (fun D : Finset V => if D=C then a else 0)=a • setMonomial C := by
  funext A
  by_cases hCA : C⊆A <;> simp [zeta,setMonomial,hCA]

theorem mobius_setMonomial (C : Finset V) :
    mobius (setMonomial C)=(fun D => if D=C then 1 else 0) := by
  have he:=zeta_single_coefficient C 1
  simp only [one_smul] at he
  rw [← he,mobius_zeta]

/-- The simplex ray has its complete normalized tight kernel in every
ambient dimension. The proof retains every proper-subset equation, including
coordinates outside the simplex's support. -/
theorem setMonomial_tight_kernel {C : Finset V} (hC : 2≤ C.card)
    (f : SetFunction V) (hn : TranslationNormalized f)
    (hf : ThreeTreeStates.TightVariation (setMonomial C) f) :
    ∃ a : ℝ,f=a • setMonomial C := by
  classical
  have hgraph : Graphical (cliqueGraph C) f := by
    intro u v huv hnon A hu hv
    exact hf u v huv A hu hv (setMonomial_graphical C u v huv hnon A hu hv)
  have hy : CliqueSupported (cliqueGraph C) (mobius f):=
    (mobius_cliqueSupported_iff _ f).mpr ⟨hn,hgraph⟩
  have hzero : ∀ D : Finset V,D≠ C → mobius f D=0 := by
    intro D
    refine Finset.strongInductionOn D ?_
    intro D ih
    intro hDC
    by_cases hd0 : D.card=0
    · rw [card_eq_zero.mp hd0]
      exact hy.1
    by_cases hd1 : D.card=1
    · obtain ⟨v,rfl⟩:=card_eq_one.mp hd1
      exact hy.2.1 v
    by_contra hnonzero
    have hd2 : 2≤ D.card:=by omega
    have hcl:=hy.clique_of_nonzero hnonzero
    have hDCsub : D⊆C := by
      intro u hu
      obtain ⟨v,hv,hvu⟩:=exists_mem_ne (show 1< D.card by omega) u
      exact (hcl hu hv hvu.symm).2.1
    have hnot : ¬C⊆D:=fun hCD => hDC (subset_antisymm hDCsub hCD)
    obtain ⟨u,huD,v,hvD,huv⟩:=one_lt_card.mp (show 1< D.card by omega)
    let A:=(D.erase u).erase v
    have huA : u∉A:=by simp [A]
    have hvA : v∉A:=by simp [A]
    have he : insert u (insert v A)=D := by
      ext w
      by_cases hwu : w=u <;> by_cases hwv : w=v <;> simp [A,hwu,hwv,huD,hvD]
    have hrow : delta (setMonomial C) u v A=0 := by
      rw [delta_setMonomial huv huA hvA,he]
      simp only [hnot,and_false,ite_false]
    have hvar:=hf u v huv A huA hvA hrow
    rw [← zeta_mobius f,delta_zeta huv huA hvA,he] at hvar
    rw [sum_eq_single D] at hvar
    · exact hnonzero hvar
    · intro B hB hBD
      have hBDsub:=(mem_powerset.mp (mem_filter.mp hB).1)
      apply ih B (Finset.ssubset_iff_subset_ne.mpr ⟨hBDsub,hBD⟩)
      intro hBC
      exact hnot (hBC ▸ hBDsub)
    · intro hDnot
      exact False.elim (hDnot (by simp [huD,hvD]))
  let a:=mobius f C
  have hyEq : mobius f=(fun D => if D=C then a else 0) := by
    funext D
    by_cases hDC : D=C
    · simp only [hDC,ite_true,a]
    · simp only [if_neg hDC,hzero D hDC]
  refine ⟨a,?_⟩
  rw [← zeta_mobius f,hyEq]
  exact zeta_single_coefficient C a

theorem setMonomial_extreme {C : Finset V} (hC : 2≤ C.card) :
    ExtremeSupermodular (setMonomial C) := by
  apply extremeSupermodular_of_tightEquations (setMonomial_translationNormalized hC)
    (setMonomial_supermodular C)
  · intro he
    have hx:=congrFun he C
    norm_num [setMonomial] at hx
  · exact setMonomial_tight_kernel hC

end GraphicalZonotopes

end
end
end BundlePart85

section BundlePart86
/- Source: Papers/GraphicalZonotopes/ThreeTreeConstruction.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem ThreeTreeOn.roots_mem {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (W : Submodule ℝ (V → ℝ))
    (hW : ∀ u v,G.Adj u v → basisVector u-basisVector v∈W) :
    ∀ u∈S,∀ v∈S,basisVector u-basisVector v∈W := by
  revert hW
  induction h with
  | tetrahedron C hC =>
    intro hW u hu v hv
    by_cases huv : u=v
    · simp [huv]
    · exact hW u v ⟨huv,hu,hv⟩
  | @attach S G h w hw T hT hTS hcl ih =>
    intro hW u hu v hv
    have hi:=ih (fun u v huv => hW u v (Or.inl huv))
    obtain ⟨a,ha⟩:=card_pos.mp (show 0< T.card by omega)
    have hwa:=hW w a ((attached_vertex_adj_iff h hw hTS a).mpr ha)
    rcases mem_insert.mp hu with huw | huS
    · subst u
      rcases mem_insert.mp hv with hvw | hvS
      · subst v
        simp
      · have hp:=W.add_mem hwa (hi a (hTS ha) v hvS)
        convert hp using 1 <;> module
    · rcases mem_insert.mp hv with hvw | hvS
      · subst v
        have hp:=W.sub_mem (hi u huS a (hTS ha)) hwa
        convert hp using 1 <;> module
      · exact hi u huS v hvS

theorem ThreeTreeOn.eq_cliqueGraph_of_card_four {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (hS : S.card=4) : G=cliqueGraph S := by
  induction h with
  | tetrahedron C hC => rfl
  | @attach S G h w hw T hT hTS hcl ih =>
    have hlo:=h.active_card_ge_four
    rw [card_insert_of_notMem hw] at hS
    omega

namespace ThreeTreeStates

theorem setFunction_fullDimension {n : ℕ} {G : SimpleGraph (Fin n)}
    (h : IsThreeTree G) (s : CompatibleRows G) :
    FullDimension (basePolytope (setFunction h s)) := by
  have hn4 : 4≤ n:=by simpa only [card_univ,Fintype.card_fin] using h.active_card_ge_four
  have hn:=(setFunction_normalized_graphical h s).1.1
  have hs:=setFunction_supermodular h s
  unfold FullDimension
  simp only [Fintype.card_fin]
  apply finrank_vectorSpan_eq_of_consecutive_roots (by omega) (basePolytope_nonempty hn hs)
  intro i
  apply h.roots_mem (vectorSpan ℝ (basePolytope (setFunction h s))) _ _ (mem_univ _) _ (mem_univ _)
  intro u v huv
  obtain ⟨A,hu,hv,hpos⟩:=exists_positive_edge_slack h s huv
  exact root_mem_vectorSpan_of_delta_ne_zero hn hs huv.ne hu hv hpos.ne'

end ThreeTreeStates

theorem complete_simplex_fullDimension {n : ℕ} (hn : 2≤ n) :
    FullDimension (basePolytope (setMonomial (univ : Finset (Fin n)))) := by
  have hzn:=(setMonomial_translationNormalized (C:=(univ : Finset (Fin n)))
    (by simpa using hn)).1
  have hzs:=setMonomial_supermodular (univ : Finset (Fin n))
  unfold FullDimension
  simp only [Fintype.card_fin]
  apply finrank_vectorSpan_eq_of_consecutive_roots (by omega) (basePolytope_nonempty hzn hzs)
  intro i
  let u : Fin n:=⟨i.val,by omega⟩
  let v : Fin n:=⟨i.val+1,by omega⟩
  have huv : u≠ v:=by intro he; have he':=congrArg Fin.val he; dsimp [u,v] at he'; omega
  let A:=(univ.erase u).erase v
  have hu : u∉A:=by simp [A]
  have hv : v∉A:=by simp [A]
  have he : insert u (insert v A)=univ := by
    ext w
    by_cases hwu : w=u <;> by_cases hwv : w=v <;> simp [A,hwu,hwv]
  apply root_mem_vectorSpan_of_delta_ne_zero hzn hzs huv hu hv
  rw [delta_setMonomial huv hu hv,he]
  norm_num

theorem complete_simplex_direction_graph {n : ℕ} (hn : 2≤ n) :
    actualDirectionGraph (basePolytope (setMonomial (univ : Finset (Fin n)) ))=
      cliqueGraph (univ : Finset (Fin n)) := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  constructor
  · intro he
    exact ⟨he.1,mem_univ _,mem_univ _⟩
  · intro huv
    let A:=(univ.erase u).erase v
    have hu : u∉A:=by simp [A]
    have hv : v∉A:=by simp [A]
    have he : insert u (insert v A)=univ := by
      ext w
      by_cases hwu : w=u <;> by_cases hwv : w=v <;> simp [A,hwu,hwv]
    apply exposedSegment_of_positive_delta
      (setMonomial_translationNormalized (C:=(univ : Finset (Fin n))) (by simpa using hn)).1
      (setMonomial_supermodular _) huv.1 hu hv
    rw [delta_setMonomial huv.1 hu hv,he]
    norm_num

/-- The complete quantitative existence assertion of Theorem6.1. This is
the actual integral Möbius vector, all graph directions, full affine
dimension, and the literal (n−3)-zonotope summand, for every n≥4. -/
theorem admissible_threeTree_construction {n : ℕ} (hn : 4≤ n)
    {G : SimpleGraph (Fin n)} (hG : IsThreeTree G) (hA : Admissible G) :
    ∃ z : SetFunction (Fin n),ExtremeSupermodular z ∧ IntegerValued (mobius z) ∧
      (∀ C∈tetrahedra G,mobius z C=1) ∧
      (∀ T : Finset (Fin n),T.card=3 → G.IsClique T →
        mobius z T=0 ∨ mobius z T= -1 ∨ mobius z T= -2) ∧
      FullDimension (basePolytope z) ∧ actualDirectionGraph (basePolytope z)=G ∧
      IsMinkowskiSummand (basePolytope z) (((n-3 : ℕ) : ℝ) • graphicalZonotope G) := by
  classical
  by_cases hn4 : n=4
  · have hGraph : G=cliqueGraph (univ : Finset (Fin n)):=
      hG.eq_cliqueGraph_of_card_four (by simpa using hn4)
    let z:=setMonomial (univ : Finset (Fin n))
    refine ⟨z,setMonomial_extreme (by simpa using (show 2≤ n by omega)),?_,?_,?_,
      complete_simplex_fullDimension (by omega),?_,?_⟩
    · rw [mobius_setMonomial]
      intro C
      by_cases hC : C=univ
      · exact ⟨1,by simp [hC]⟩
      · exact ⟨0,by simp [hC]⟩
    · intro C hC
      rw [hGraph,tetrahedra_cliqueGraph (by simpa using hn4),mem_singleton] at hC
      rw [mobius_setMonomial]
      simp [hC]
    · intro T ht hcl
      left
      rw [mobius_setMonomial]
      have hne : T≠ univ := by
        intro he
        have hc:=congrArg Finset.card he
        simp only [ht,card_univ,Fintype.card_fin] at hc
        omega
      simp [hne]
    · rw [hGraph]
      exact complete_simplex_direction_graph (by omega)
    · apply (isMinkowskiSummand_graphical_iff
        (setMonomial_translationNormalized (C:=(univ : Finset (Fin n)))
          (by simpa using (show 2≤ n by omega))).1
        (setMonomial_supermodular _) (Nat.cast_nonneg _)).mpr
      refine ⟨by rw [hGraph]; exact setMonomial_graphical _,?_⟩
      intro u v huv hedge A hu hv
      rw [delta_setMonomial huv hu hv]
      have he : (n-3 : ℕ)=1 := by omega
      rw [he]
      split <;> norm_num
  · obtain ⟨s⟩:=ThreeTreeStates.compatibleRows_exists hG hA
    have hm : 2≤(tetrahedra G).card := by
      rw [hG.tetrahedra_card,card_univ,Fintype.card_fin]
      omega
    refine ⟨ThreeTreeStates.setFunction hG s,
      ThreeTreeStates.setFunction_extreme hG s hm,?_,?_,?_,
      ThreeTreeStates.setFunction_fullDimension hG s,
      ThreeTreeStates.setFunction_direction_graph hG s,?_⟩
    · rw [ThreeTreeStates.setFunction_mobius]
      exact ThreeTreeStates.coefficients_integerValued hG s
    · intro C hC
      rw [ThreeTreeStates.setFunction_mobius]
      exact ThreeTreeStates.coefficients_tetrahedron hG s hC
    · intro T ht hcl
      rw [ThreeTreeStates.setFunction_mobius]
      exact ThreeTreeStates.coefficients_triangle_values hG s (mem_triangles.mpr ⟨ht,hcl⟩)
    · simpa only [card_univ,Fintype.card_fin] using ThreeTreeStates.setFunction_actual_summand hG s

end GraphicalZonotopes

end
end
end BundlePart86

section BundlePart87
/- Source: Papers/GraphicalZonotopes/GraphComponentExtension.lean -/







@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace VertexExtension
variable {V : Type*} {W : Type*}

/-- Add one vertex, with exactly the specified neighbors. The old vertex
type is retained as `some`, and the new vertex is `none`. -/
def graph (G : SimpleGraph V) (N : Set V) : SimpleGraph (Option V) where
  Adj a b := match a,b with
    | none,some v => v∈N
    | some v,none => v∈N
    | some v,some w => G.Adj v w
    | none,none => False
  symm := ⟨by intro a b; cases a <;> cases b <;> simp [G.adj_comm]⟩
  loopless := ⟨by intro a; cases a <;> simp [G.irrefl]⟩

def someHom (G : SimpleGraph V) (N : Set V) : G →g graph G N where
  toFun := Option.some
  map_rel' := fun h => h

/-- A label constant on each edge descends to the actual connected-component
quotient. In particular, this does not assert that the labels define a graph
homomorphism, which would fail when an edge is collapsed to one vertex. -/
def componentLift (G : SimpleGraph V) (f : V → W)
    (hf : ∀ u v,G.Adj u v → f u=f v) : G.ConnectedComponent → W :=
  Quot.lift f (by
    intro u v hp
    rw [SimpleGraph.reachable_eq_reflTransGen] at hp
    induction hp with
    | refl => rfl
    | @tail v w hp hvw ih => exact ih.trans (hf v w hvw))

@[simp] theorem componentLift_mk (G : SimpleGraph V) (f : V → W)
    (hf : ∀ u v,G.Adj u v → f u=f v) (u : V) :
    componentLift G f hf (G.connectedComponentMk u)=f u := rfl

def oldLabel (G : SimpleGraph V) (v₀ : V) : Option V → G.ConnectedComponent
  | none => G.connectedComponentMk v₀
  | some v => G.connectedComponentMk v

theorem oldLabel_adj (G : SimpleGraph V) (N : Set V) (v₀ : V)
    (hv₀ : v₀∈N) (hN : G.IsClique N) :
    ∀ a b,(graph G N).Adj a b → oldLabel G v₀ a=oldLabel G v₀ b := by
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => exact False.elim hab
    | some v =>
      by_cases he : v₀=v
      · simp [oldLabel,he]
      · exact SimpleGraph.ConnectedComponent.sound (hN hv₀ hab he).reachable
  | some u =>
    cases b with
    | none =>
      by_cases he : u=v₀
      · simp [oldLabel,he]
      · exact SimpleGraph.ConnectedComponent.sound (hN hab hv₀ he).reachable
    | some v =>
        change G.Adj u v at hab
        exact SimpleGraph.ConnectedComponent.sound hab.reachable

/-- Attaching a vertex to a nonempty clique preserves all actual connected
components, including any other disconnected components of the old graph. -/
def componentEquiv (G : SimpleGraph V) (N : Set V) (v₀ : V)
    (hv₀ : v₀∈N) (hN : G.IsClique N) :
    (graph G N).ConnectedComponent ≃ G.ConnectedComponent where
  toFun := componentLift (graph G N) (oldLabel G v₀) (oldLabel_adj G N v₀ hv₀ hN)
  invFun := SimpleGraph.ConnectedComponent.map (someHom G N)
  left_inv := by
    intro c
    refine c.ind ?_
    intro v
    cases v with
    | none =>
      exact SimpleGraph.ConnectedComponent.sound
        (show (graph G N).Reachable (some v₀) none from
          (SimpleGraph.Adj.reachable (show (graph G N).Adj (some v₀) none from hv₀)))
    | some v => rfl
  right_inv := by
    intro c
    exact c.ind (fun _ => rfl)

theorem component_card (G : SimpleGraph V) (N : Set V)
    (hne : N.Nonempty) (hN : G.IsClique N) :
    Nat.card (graph G N).ConnectedComponent=Nat.card G.ConnectedComponent := by
  obtain ⟨v₀,hv₀⟩:=hne
  exact Nat.card_congr (componentEquiv G N v₀ hv₀ hN)

def isolatedLabel (G : SimpleGraph V) : Option V → Option G.ConnectedComponent
  | none => none
  | some v => some (G.connectedComponentMk v)

theorem isolatedLabel_adj (G : SimpleGraph V) :
    ∀ a b,(graph G ∅).Adj a b → isolatedLabel G a=isolatedLabel G b := by
  intro a b hab
  cases a <;> cases b
  · exact False.elim hab
  · exact False.elim hab
  · exact False.elim hab
  · rename_i u v
    change G.Adj u v at hab
    exact congrArg Option.some (SimpleGraph.ConnectedComponent.sound hab.reachable)

/-- Adding an isolated vertex adds exactly one new connected component. -/
def isolatedComponentEquiv (G : SimpleGraph V) :
    (graph G ∅).ConnectedComponent ≃ Option G.ConnectedComponent where
  toFun := componentLift (graph G ∅) (isolatedLabel G) (isolatedLabel_adj G)
  invFun := fun c => match c with
    | none => (graph G ∅).connectedComponentMk none
    | some c => c.map (someHom G ∅)
  left_inv := by
    intro c
    refine c.ind ?_
    intro v
    cases v <;> rfl
  right_inv := by
    intro c
    cases c with
    | none => rfl
    | some c => exact c.ind (fun _ => rfl)

theorem isolated_component_card (G : SimpleGraph V) [Finite V] :
    Nat.card (graph G ∅).ConnectedComponent=Nat.card G.ConnectedComponent+1 := by
  classical
  letI : Fintype G.ConnectedComponent:=Fintype.ofFinite _
  rw [Nat.card_congr (isolatedComponentEquiv G),Nat.card_eq_fintype_card,
    Fintype.card_option,Nat.card_eq_fintype_card]

theorem connected (G : SimpleGraph V) (N : Set V)
    (hG : G.Connected) (hne : N.Nonempty) : (graph G N).Connected := by
  obtain ⟨v₀,hv₀⟩:=hne
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨none,?_⟩
  intro v
  cases v with
  | none => exact SimpleGraph.Reachable.rfl
  | some v =>
    exact (SimpleGraph.Adj.reachable (show (graph G N).Adj none (some v₀) from hv₀)).trans
      ((hG v₀ v).map (someHom G N))

theorem connected_component_card_one {G : SimpleGraph V} (hG : G.Connected) :
    Nat.card G.ConnectedComponent=1 := by
  letI : Nonempty V:=hG.nonempty
  letI : Subsingleton G.ConnectedComponent:=hG.preconnected.subsingleton_connectedComponent
  exact Nat.card_unique

end VertexExtension
end GraphicalZonotopes

end
end
end BundlePart87

section BundlePart88
/- Source: Papers/GraphicalZonotopes/ActiveDeletion.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Delete vertices from the actual active graph. Ambient isolated vertices
outside `S` are not included in this graph's vertex type. -/
def activeDelete (G : SimpleGraph V) (S D : Finset V) :
    SimpleGraph {v : V // v∈S ∧ v∉D} := G.induce {v | v∈S ∧ v∉D}

def activeAttachEquiv {S : Finset V} {u : V} (hu : u∉S)
    (D : Finset V) (huD : u∉D) :
    Option {v : V // v∈S ∧ v∉D} ≃ {v : V // v∈insert u S ∧ v∉D} where
  toFun x := match x with
    | none => ⟨u,mem_insert_self _ _,huD⟩
    | some v => ⟨v.1,mem_insert_of_mem v.2.1,v.2.2⟩
  invFun v := if hv : v.1=u then none else
    some ⟨v.1,(mem_insert.mp v.2.1).resolve_left hv,v.2.2⟩
  left_inv := by
    intro x
    cases x with
    | none => simp
    | some v =>
      have hv : v.1≠ u:=fun he => hu (he ▸ v.2.1)
      simp [hv]
  right_inv := by
    intro v
    by_cases hv : v.1=u
    · simp only [dif_pos hv]
      exact Subtype.ext hv.symm
    · simp only [dif_neg hv]

/-- The exact graph after a new vertex survives deletion: it is the old
deleted graph with one vertex attached to the surviving attachment clique. -/
def activeAttachIso {S : Finset V} {G : SimpleGraph V} (h : ThreeTreeOn S G)
    {u : V} (hu : u∉S) (A : Finset V) (hAS : A⊆S)
    (D : Finset V) (huD : u∉D) :
    VertexExtension.graph (activeDelete G S D) {v | v.1∈A} ≃g
      activeDelete (G⊔attachmentStar u A) (insert u S) D where
  toEquiv := activeAttachEquiv hu D huD
  map_rel_iff' := by
    intro x y
    cases x with
    | none =>
      cases y with
      | none =>
        change (G⊔attachmentStar u A).Adj u u ↔ False
        simp
      | some v =>
        change (G⊔attachmentStar u A).Adj u v.1 ↔ v.1∈A
        exact attached_vertex_adj_iff h hu hAS v.1
    | some v =>
      cases y with
      | none =>
        change (G⊔attachmentStar u A).Adj v.1 u ↔ v.1∈A
        rw [SimpleGraph.adj_comm]
        exact attached_vertex_adj_iff h hu hAS v.1
      | some w =>
        change (G⊔attachmentStar u A).Adj v.1 w.1 ↔ G.Adj v.1 w.1
        constructor
        · exact adj_before_attachment (fun he => hu (he ▸ v.2.1))
            (fun he => hu (he ▸ w.2.1))
        · exact Or.inl

def activeRemovedEquiv {S : Finset V} {u : V} (hu : u∉S)
    (D : Finset V) (huD : u∈D) :
    {v : V // v∈S ∧ v∉D.erase u} ≃ {v : V // v∈insert u S ∧ v∉D} where
  toFun v := ⟨v.1,mem_insert_of_mem v.2.1,by
    intro hvD
    exact v.2.2 (mem_erase.mpr ⟨fun he => hu (he ▸ v.2.1),hvD⟩)⟩
  invFun v := ⟨v.1,(mem_insert.mp v.2.1).resolve_left
    (fun he => v.2.2 (he.symm ▸ huD)),fun hv => v.2.2 (mem_of_mem_erase hv)⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- If the newly attached vertex is deleted, no new edge survives. Removing
that vertex from the deletion set gives precisely the old induced graph. -/
def activeRemovedIso {S : Finset V} {G : SimpleGraph V} {u : V} (hu : u∉S)
    (A D : Finset V) (huD : u∈D) :
    activeDelete G S (D.erase u) ≃g
      activeDelete (G⊔attachmentStar u A) (insert u S) D where
  toEquiv := activeRemovedEquiv hu D huD
  map_rel_iff' := by
    intro v w
    change (G⊔attachmentStar u A).Adj v.1 w.1 ↔ G.Adj v.1 w.1
    exact ⟨adj_before_attachment (fun he => hu (he ▸ v.2.1))
      (fun he => hu (he ▸ w.2.1)),Or.inl⟩

theorem active_neighbors_nonempty {S A D : Finset V} (hAS : A⊆S)
    (hcard : D.card< A.card) :
    ({v : {v : V // v∈S ∧ v∉D} | v.1∈A} : Set _).Nonempty := by
  have hnot : ¬A⊆D:=fun h => Nat.not_lt_of_ge (card_le_card h) hcard
  obtain ⟨v,hvA,hvD⟩:=not_subset.mp hnot
  exact ⟨⟨v,hAS hvA,hvD⟩,hvA⟩

theorem active_neighbors_clique {G : SimpleGraph V} {S A D : Finset V}
    (hA : G.IsClique A) :
    (activeDelete G S D).IsClique {v | v.1∈A} := by
  intro v hv w hw hvw
  exact hA hv hw (fun he => hvw (Subtype.ext he))

theorem cliqueGraph_activeDelete_connected (C D : Finset V) (hcard : D.card< C.card) :
    (activeDelete (cliqueGraph C) C D).Connected := by
  have hn : ¬C⊆D:=fun hs => Nat.not_lt_of_ge (card_le_card hs) hcard
  obtain ⟨v,hvC,hvD⟩:=not_subset.mp hn
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨⟨v,hvC,hvD⟩,?_⟩
  intro w
  by_cases he : v=w.1
  · have he' : (⟨v,hvC,hvD⟩ : {v : V // v∈C ∧ v∉D})=w:=Subtype.ext he
    rw [he']
  · exact SimpleGraph.Adj.reachable ⟨he,hvC,w.2.1⟩

/-- Deleting at most two vertices from a 3-tree leaves its active graph
connected. The deletion set is arbitrary; it need not lie inside `S`. -/
theorem ThreeTreeOn.delete_at_most_two_connected {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (D : Finset V) (hD : D.card≤2) :
    (activeDelete G S D).Connected := by
  induction h generalizing D with
  | tetrahedron C hC =>
    exact cliqueGraph_activeDelete_connected C D (by omega)
  | @attach S G h u hu A hA hAS hcA ih =>
    by_cases huD : u∈D
    · exact (activeRemovedIso (G:=G) hu A D huD).connected_iff.mp
        (ih (D.erase u) ((card_erase_le (s:=D) (a:=u)).trans hD))
    · exact (activeAttachIso h hu A hAS D huD).connected_iff.mp
        (VertexExtension.connected _ _ (ih D hD)
          (active_neighbors_nonempty hAS (by omega)))

theorem activeDelete_univ_components (G : SimpleGraph V) (D : Finset V) :
    Nat.card (activeDelete G univ D).ConnectedComponent=
      Nat.card (G.induce ((D : Set V)ᶜ)).ConnectedComponent := by
  let e : {v : V // v∈(univ : Finset V) ∧ v∉D} ≃ {v : V // v∉D} :=
    { toFun := fun v => ⟨v.1,v.2.2⟩
      invFun := fun v => ⟨v.1,mem_univ _,v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let iso : activeDelete G univ D ≃g G.induce ((D : Set V)ᶜ) :=
    { toEquiv := e
      map_rel_iff' := by intro v w; rfl }
  exact Nat.card_congr iso.connectedComponentEquiv

end GraphicalZonotopes

end
end
end BundlePart88

section BundlePart89
/- Source: Papers/GraphicalZonotopes/ThreeTreeDeletion.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem triangleMultiplicity_after_attachment {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u : V} (hu : u∉S) {A : Finset V}
    (hA : A.card=3) (hAS : A⊆S) (hcA : G.IsClique A) (T : Finset V) :
    triangleMultiplicity (G⊔attachmentStar u A) T=
      triangleMultiplicity G T+if T⊆insert u A then 1 else 0 := by
  classical
  simp only [triangleMultiplicity,tetrahedra_after_attachment h hu hA hAS hcA,
    filter_insert]
  split_ifs with ht
  · rw [card_insert_of_notMem (by
      intro hm
      exact attached_tetrahedron_not_old h hu (mem_filter.mp hm).1)]
  · simp

theorem ThreeTreeOn.triangleMultiplicity_eq_zero_of_outside
    {S : Finset V} {G : SimpleGraph V} (h : ThreeTreeOn S G)
    {u : V} (hu : u∉S) {T : Finset V} (huT : u∈T) :
    triangleMultiplicity G T=0 := by
  classical
  unfold triangleMultiplicity
  apply card_eq_zero.mpr
  apply filter_eq_empty_iff.mpr
  intro C hC hTC
  obtain ⟨hc,hcl⟩:=(mem_filter.mp hC).2
  exact hu (h.clique_subset_active (by omega) hcl (hTC huT))

/-- The exact separator dictionary for every triangle of a 3-tree, proved
on the actual active vertex type. Thus unused ambient vertices cannot create
spurious components in the induction. -/
theorem ThreeTreeOn.triangle_components_eq_multiplicity
    {S : Finset V} {G : SimpleGraph V} (h : ThreeTreeOn S G)
    (T : Finset V) (hT : T.card=3) (hcT : G.IsClique T) :
    Nat.card (activeDelete G S T).ConnectedComponent=triangleMultiplicity G T := by
  classical
  induction h generalizing T with
  | tetrahedron C hC =>
    have hTC:=(ThreeTreeOn.tetrahedron C hC).clique_subset_active (by omega) hcT
    rw [VertexExtension.connected_component_card_one
      (cliqueGraph_activeDelete_connected C T (by omega))]
    simp only [triangleMultiplicity,tetrahedra_cliqueGraph hC]
    rw [Finset.filter_singleton]
    simp only [if_pos hTC, Finset.card_singleton]
  | @attach S G h u hu A hA hAS hcA ih =>
    by_cases huT : u∈T
    · have hTsub : T⊆insert u A := by
        intro v hv
        by_cases he : v=u
        · exact mem_insert.mpr (Or.inl he)
        · exact mem_insert.mpr (Or.inr
            ((attached_vertex_adj_iff h hu hAS v).mp (hcT huT hv (Ne.symm he))))
      have hconn : (activeDelete (G⊔attachmentStar u A) (insert u S) T).Connected :=
        (activeRemovedIso (G:=G) hu A T huT).connected_iff.mp
          (h.delete_at_most_two_connected (T.erase u) (by
            rw [card_erase_of_mem huT,hT]))
      rw [VertexExtension.connected_component_card_one hconn,
        triangleMultiplicity_after_attachment h hu hA hAS hcA,
        h.triangleMultiplicity_eq_zero_of_outside hu huT,if_pos hTsub]
    · have hcOld : G.IsClique T:=clique_before_attachment huT hcT
      have hnewcard := Nat.card_congr
        (activeAttachIso h hu A hAS T huT).connectedComponentEquiv
      rw [← hnewcard,triangleMultiplicity_after_attachment h hu hA hAS hcA]
      by_cases hTA : T=A
      · subst T
        have hN : ({v : {v : V // v∈S ∧ v∉A} | v.1∈A} : Set _)=∅ := by
          ext v
          exact ⟨fun hv => v.2.2 hv,False.elim⟩
        rw [hN,VertexExtension.isolated_component_card,
          ih A hA hcA,if_pos (subset_insert _ _)]
      · have hnot : ¬A⊆T := by
          intro hAT
          exact hTA (eq_of_subset_of_card_le hAT (by omega)).symm
        obtain ⟨v,hvA,hvT⟩:=not_subset.mp hnot
        have hN : ({v : {v : V // v∈S ∧ v∉T} | v.1∈A} : Set _).Nonempty :=
          ⟨⟨v,hAS hvA,hvT⟩,hvA⟩
        have hnotSub : ¬T⊆insert u A := by
          intro ht
          have htA : T⊆A := by
            intro w hw
            exact (mem_insert.mp (ht hw)).resolve_left (fun he => huT (he ▸ hw))
          exact hTA (eq_of_subset_of_card_le htA (by omega))
        rw [VertexExtension.component_card _ _ hN (active_neighbors_clique hcA),
          ih T hT hcOld,if_neg hnotSub,Nat.add_zero]

/-- Literal vertex deletion on a full 3-tree has exactly one component per
maximal tetrahedron containing the deleted triangle. -/
theorem IsThreeTree.triangle_components_eq_multiplicity {G : SimpleGraph V}
    (hG : IsThreeTree G) (T : Finset V) (hT : T.card=3) (hcT : G.IsClique T) :
    Nat.card (G.induce ((T : Set V)ᶜ)).ConnectedComponent=triangleMultiplicity G T := by
  rw [← activeDelete_univ_components]
  exact ThreeTreeOn.triangle_components_eq_multiplicity hG T hT hcT

theorem IsThreeTree.admissible_iff_triangle_deletion {G : SimpleGraph V}
    (hG : IsThreeTree G) :
    Admissible G ↔ ∀ T : Finset V,T.card=3 → G.IsClique T →
      Nat.card (G.induce ((T : Set V)ᶜ)).ConnectedComponent≤3 := by
  constructor
  · intro h T ht hc
    rw [hG.triangle_components_eq_multiplicity T ht hc]
    exact h T ht hc
  · intro h T ht hc
    rw [← hG.triangle_components_eq_multiplicity T ht hc]
    exact h T ht hc

end GraphicalZonotopes

end
end
end BundlePart89

