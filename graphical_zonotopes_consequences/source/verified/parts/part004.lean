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

public import verified.parts.part003
import all verified.parts.part003

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

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
