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

public import verified.parts.part008
import all verified.parts.part008

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

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
