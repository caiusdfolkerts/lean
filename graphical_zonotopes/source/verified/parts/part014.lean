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

public import verified.parts.part013
import all verified.parts.part013

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section BundlePart194
/- Source: Papers/GraphicalZonotopes/MultipartiteRealization.lean -/








@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
namespace SmallCount
open Finset
open scoped BigOperators

namespace SizeModel
variable {I : Type*} [Fintype I] [DecidableEq I] (p : I → ℕ)
abbrev Vertex:=Σ i : I,Fin (p i)

def embedding {s : ℕ} (hsize : (∑ i,p i)≤ s) : Vertex p ↪ Fin s :=
  (Fintype.equivFin (Vertex p)).toEmbedding.trans (Fin.castLEEmb (by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using hsize))

def block {s : ℕ} (hsize : (∑ i,p i)≤ s) (i : I) : Finset (Fin s):=
  univ.map ((Function.Embedding.sigmaMk i).trans (embedding p hsize))

@[simp] theorem block_card {s : ℕ} (hsize : (∑ i,p i)≤ s) (i : I) :
    (block p hsize i).card=p i := by simp only [block,card_map,card_univ,Fintype.card_fin]

theorem block_disjoint {s : ℕ} (hsize : (∑ i,p i)≤ s) {i j : I} (hij : i≠ j) :
    Disjoint (block p hsize i) (block p hsize j) := by
  apply disjoint_left.mpr
  intro x hi hj
  obtain ⟨a,_,ha⟩:=mem_map.mp hi
  obtain ⟨b,_,hb⟩:=mem_map.mp hj
  have he : (⟨i,a⟩ : Vertex p)=⟨j,b⟩:=
    (embedding p hsize).injective (ha.trans hb.symm)
  exact hij (congrArg Sigma.fst he)

theorem block_nonempty {s : ℕ} (hsize : (∑ i,p i)≤ s)
    (hpos : ∀ i,0< p i) (i : I) : (block p hsize i).Nonempty := by
  rw [← card_pos,block_card]
  exact hpos i

theorem block_injective {s : ℕ} (hsize : (∑ i,p i)≤ s) (hpos : ∀ i,0< p i) :
    Function.Injective (block p hsize) := by
  intro i j he
  by_contra hij
  obtain ⟨x,hx⟩:=block_nonempty p hsize hpos i
  exact (disjoint_left.mp (block_disjoint p hsize hij)) hx (he ▸ hx)

def blocks {s : ℕ} (hsize : (∑ i,p i)≤ s) : Finset (Finset (Fin s)):=
  univ.image (block p hsize)

theorem blocks_nonempty {s : ℕ} (hsize : (∑ i,p i)≤ s) (hpos : ∀ i,0< p i) :
    ∀ B∈blocks p hsize,B.Nonempty := by
  intro B hB
  obtain ⟨i,_,rfl⟩:=mem_image.mp hB
  exact block_nonempty p hsize hpos i

theorem blocks_disjoint {s : ℕ} (hsize : (∑ i,p i)≤ s) :
    ∀ A∈blocks p hsize,∀ B∈blocks p hsize,A≠ B → Disjoint A B := by
  intro A hA B hB hAB
  obtain ⟨i,_,rfl⟩:=mem_image.mp hA
  obtain ⟨j,_,rfl⟩:=mem_image.mp hB
  exact block_disjoint p hsize (fun h => hAB (congrArg (block p hsize) h))

theorem blockUnion_card {s : ℕ} (hsize : (∑ i,p i)≤ s) :
    (blockUnion (blocks p hsize)).card=∑ i,p i := by
  have he : blockUnion (blocks p hsize)=univ.biUnion (block p hsize) := by
    ext x
    simp only [blockUnion,blocks,mem_biUnion,mem_image,mem_univ,true_and]
    constructor
    · rintro ⟨B,⟨i,rfl⟩,hx⟩
      exact ⟨i,hx⟩
    · rintro ⟨i,hx⟩
      exact ⟨block p hsize i,⟨i,rfl⟩,hx⟩
  rw [he,card_biUnion]
  · simp only [block_card]
  · intro i hi j hj hij
    exact block_disjoint p hsize hij

theorem within_count {s : ℕ} (hsize : (∑ i,p i)≤ s) (hpos : ∀ i,0< p i) :
    (∑ B∈blocks p hsize,B.card.choose 2)=∑ i,(p i).choose 2 := by
  rw [blocks,sum_image]
  · simp only [block_card]
  · intro i hi j hj he
    exact block_injective p hsize hpos he

theorem crossing_count {s : ℕ} (hsize : (∑ i,p i)≤ s) (hpos : ∀ i,0< p i) :
    (crossingPairs (blocks p hsize)).card=(∑ i,p i).choose 2-∑ i,(p i).choose 2 := by
  rw [crossingPairs_card_formula _ (blocks_disjoint p hsize),
    blockUnion_card,within_count p hsize hpos]

end SizeModel

/-- The finite blocks in the Boolean construction exist for every positive
proper pair count, including counts whose pattern uses fewer than all hubs. -/
theorem exists_complement_family_count (s m : ℕ) (hm : 0< m) (hmax : m< s.choose 2) :
    ∃ blocks : Finset (Finset (Fin s)),
      ComplementFamily (univ : Finset (Fin s)) blocks ∧
      (crossingPairs blocks).card=m ∧
      ∃ e : OrientedEdge (⊤ : SimpleGraph (Fin s)),e∉crossingPairs blocks := by
  obtain ⟨sizes,hpos,hsize,hcount⟩:=exists_multipartite_sizes s m hmax.le
  let p : Fin sizes.length → ℕ:=sizes.get
  have hsum : (∑ i,p i)=sizes.sum := by
    rw [← List.sum_ofFn]
    exact congrArg List.sum (List.ofFn_get sizes)
  have hinside : (∑ i,(p i).choose 2)=(sizes.map (fun n => n.choose 2)).sum := by
    rw [← List.sum_ofFn]
    change (List.ofFn ((fun n : ℕ => n.choose 2) ∘ sizes.get)).sum=_
    rw [← List.map_ofFn,List.ofFn_get]
  have hp : ∀ i,0< p i:=fun i => hpos (sizes.get i) (List.get_mem sizes i)
  have hsize' : (∑ i,p i)≤ s:=by rw [hsum]; exact hsize
  let blocks:=SizeModel.blocks p hsize'
  have hc : (crossingPairs blocks).card=m := by
    rw [SizeModel.crossing_count p hsize' hp,hsum,hinside]
    exact hcount
  have hnon : (crossingPairs blocks).Nonempty:=card_pos.mp (hc.symm ▸ hm)
  refine ⟨blocks,⟨crossingPairs_nonempty_gives_two blocks hnon,
    fun B hB => subset_univ _,SizeModel.blocks_nonempty p hsize' hp,
    SizeModel.blocks_disjoint p hsize'⟩,hc,?_⟩
  have hlt : (crossingPairs blocks).card<
      (univ : Finset (OrientedEdge (⊤ : SimpleGraph (Fin s)))).card := by
    rw [hc,card_univ,completePair_card,Fintype.card_fin]
    exact hmax
  obtain ⟨e,_,he⟩:=exists_mem_notMem_of_card_lt_card hlt
  exact ⟨e,he⟩

end SmallCount
end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart194

section BundlePart195
/- Source: Papers/GraphicalZonotopes/SmallCountPrincipal.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise

theorem conjunction_boolean {H : Type*} [Fintype H] [DecidableEq H] [Nonempty H] :
    IsMonotoneBoolean (setMonomial (univ : Finset H)) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro A B hAB
    by_cases hA : (univ : Finset H)⊆A
    · simp only [setMonomial,if_pos hA,if_pos (hA.trans hAB),le_refl]
    · simp only [setMonomial,if_neg hA]
      split_ifs <;> norm_num
  · intro A
    by_cases hA : (univ : Finset H)⊆A <;> simp [setMonomial,hA]
  · have hn : ¬(univ : Finset H)⊆∅ := by
      obtain ⟨a⟩:=‹Nonempty H›
      intro h
      exact notMem_empty a (h (mem_univ a))
    simp only [setMonomial,if_neg hn]
  · simp only [setMonomial,subset_refl,ite_true]

theorem conjunction_essential {H : Type*} [Fintype H] [DecidableEq H] (a : H) :
    Essential (setMonomial (univ : Finset H)) a := by
  refine ⟨univ.erase a,notMem_erase a univ,?_⟩
  have hins : insert a (univ.erase a)=(univ : Finset H):=insert_erase (mem_univ a)
  have hn : ¬(univ : Finset H)⊆univ.erase a:=
    fun h => notMem_erase a univ (h (mem_univ a))
  rw [hins]
  simp only [setMonomial,subset_refl,ite_true,if_neg hn,sub_zero]

theorem one_outer_lattice_book (s : ℕ) (hs : 0< s) :
    ∃ f : SetFunction (Fin s⊕Fin 1),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s 1) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin 1) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(1 : ℝ) • graphicalZonotope (cliqueBook s 1) := by
  letI : Nonempty (Fin s):=⟨⟨0,hs⟩⟩
  let F : Fin 1 → SetFunction (Fin s):=fun _ => setMonomial univ
  have hrel : ∃ z : SetFunction (Fin s),TranslationNormalized z ∧
      Compatible z F (fun _ => 1) := by
    refine ⟨0,⟨rfl,fun _ => rfl⟩,?_⟩
    intro u v huv S hu hv
    have hn : negativeResponse (setMonomial (univ : Finset (Fin s))) u v S=0 := by
      exact max_eq_left (neg_nonpos.mpr ((setMonomial_supermodular univ).elemental u v huv S hu hv))
    simpa only [F,hn,mul_zero,sum_const_zero] using
      (show delta (0 : SetFunction (Fin s)) u v S=0 by simp [delta])
  have huniq : UniqueIntegrableRelation F (fun _ => 1) := by
    intro t ht
    refine ⟨t 0,?_⟩
    funext i
    have hi : i=0:=Subsingleton.elim _ _
    subst i
    simp only [Pi.smul_apply,smul_eq_mul,mul_one]
  simpa only [Nat.cast_one] using lattice_book_of_unit_modules hs (by decide) F
    (fun _ => conjunction_boolean) (fun _ a => conjunction_essential a) hrel huniq

/-- The complete parameter range in Theorem7.5, with actual lattice
complements in `k` times the graphical zonotope. The proof includes the
one-column simplex case and constructs the multipartite pair pattern for
every remaining integer count. -/
theorem small_count_lattice_books (s k : ℕ) (hs : 2≤ s) (hk : 1≤ k)
    (hmax : k≤ s.choose 2) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(k : ℝ) • graphicalZonotope (cliqueBook s k) := by
  by_cases hk1 : k=1
  · subst k
    simpa only [Nat.cast_one] using one_outer_lattice_book s (by omega)
  · have hs3 : 3≤ s := by
      by_contra hn
      have hs2 : s=2:=by omega
      subst s
      norm_num at hmax
      omega
    have hm : 0< k-1:=by omega
    have hlt : k-1< s.choose 2:=by omega
    obtain ⟨blocks,hb,hcard,hproper⟩:=SmallCount.exists_complement_family_count s (k-1) hm hlt
    exact SmallCount.lattice_book_of_complement_family hs3 blocks hb hproper (by omega)


/-- Literal geometric formulation of Theorem 7.5, obtained from the complete
integral construction above. The actual complement already exists when k=1. -/
theorem small_count_lattice_books_literal (s k : ℕ) (hs : 2≤ s) (hk : 1≤ k)
    (hmax : k≤ s.choose 2) :
    ∃ Q : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope Q ∧
      MinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s k)) ∧
      (2≤ k → IsMinkowskiSummand Q ((k : ℝ) • graphicalZonotope (cliqueBook s k))) := by
  obtain ⟨f,hn,hi,he,hg,hd,hm,hl,R,hR,hnR,hsum⟩ :=
    small_count_lattice_books s k hs hk hmax
  have hactual : IsMinkowskiSummand (basePolytope f)
      ((k : ℝ) • graphicalZonotope (cliqueBook s k)) :=
    ⟨R,hR.compact,hR.convex,hnR,hsum⟩
  refine ⟨basePolytope f,hl,hm,hd,⟨(k : ℝ),?_,hactual⟩,fun _ => hactual⟩
  exact_mod_cast (show 0< k by omega)

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart195

section BundlePart196
/- Source: Papers/GraphicalZonotopes/BookLatticeAttainment.lean -/








@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
open BooleanModule

private theorem book_lattice_of_full_complement {s k M : ℕ}
    (h : ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(M : ℝ) • graphicalZonotope (cliqueBook s k)) :
    LatticeExtremeAt (cliqueBook s k) (s+k-1) M := by
  obtain ⟨f,hn,hi,he,hG,hd,hm,hl,R,hR,hRn,hQR⟩ := h
  apply LatticeExtremeAt.of_lattice_complement hn hi he hG _ hR hRn hQR
  simpa only [FullDimension,Fintype.card_sum,Fintype.card_fin] using hd

theorem book_lattice_small {s k : ℕ} (hs : 2≤ s) (hk : 1≤ k) (hcap : k≤ s.choose 2) :
    LatticeExtremeAt (cliqueBook s k) (s+k-1) ((s-1)*k) := by
  have h := book_lattice_of_full_complement (small_count_lattice_books s k hs hk hcap)
  apply h.mono_dilation
  simpa only [one_mul] using Nat.mul_le_mul_right k (show 1≤ s-1 by omega)

theorem book_lattice_threshold {s k : ℕ} (hs : 3≤ s)
    (hklo : 2^(s-1)-s+1≤ k) (hkhi : k≤ cliqueCapacity s-cliqueCapacity (s-1)+1) :
    LatticeExtremeAt (cliqueBook s k) (s+k-1) ((s-1)*k) := by
  have h := book_lattice_of_full_complement (threshold_book_interval hs hklo hkhi)
  apply h.mono_dilation
  simpa only [one_mul] using Nat.mul_le_mul_right k (show 1≤ s-1 by omega)

theorem book_lattice_upper {s k : ℕ} (hs : 5≤ s)
    (hklo : bookUpperIntervalStart s≤ k) (hkhi : k≤ cliqueCapacity s) :
    LatticeExtremeAt (cliqueBook s k) (s+k-1) ((s-1)*k) :=
  book_lattice_of_full_complement (book_upper_interval hs hklo hkhi)

theorem book_lattice_four_bridge {k : ℕ} (hklo : 12≤ k) (hkhi : k≤14) :
    LatticeExtremeAt (cliqueBook 4 k) (4+k-1) ((4-1)*k) := by
  have h := book_lattice_of_full_complement (two_threshold_four_bridge hklo hkhi)
  exact h.mono_dilation (Nat.mul_le_mul_right k (by decide : 2≤4-1))

theorem book_lattice_five_bridge {k : ℕ} (hklo : 39≤ k) (hkhi : k≤53) :
    LatticeExtremeAt (cliqueBook 5 k) (5+k-1) ((5-1)*k) := by
  have h := book_lattice_of_full_complement (two_threshold_five_bridge hklo hkhi)
  exact h.mono_dilation (Nat.mul_le_mul_right k (by decide : 2≤5-1))

/-- Full dimensional integral attainment for every book below its exact
capacity. The induction uses actual graph embeddings and the proved overlap
inequalities, including the four- and five-hub bridges. -/
theorem book_lattice_full (s : ℕ) : ∀ k : ℕ,2≤ s → 1≤ k → k≤ cliqueCapacity s →
    LatticeExtremeAt (cliqueBook s k) (s+k-1) ((s-1)*k) := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro k hs hk hcap
    by_cases hsmall : k≤ s.choose 2
    · exact book_lattice_small hs hk hsmall
    have hs4 : 4≤ s := by
      by_contra hn
      have hcases : s=2 ∨ s=3 := by omega
      rcases hcases with rfl | rfl <;> norm_num [cliqueCapacity,Nat.choose] at hcap hsmall <;> omega
    by_cases hsEq4 : s=4
    · subst s
      have hcap' : k≤14 := by simpa [cliqueCapacity,Nat.choose] using hcap
      by_cases h12 : k≤12
      · apply book_lattice_threshold (by decide)
        · norm_num [Nat.choose] at hsmall
          norm_num
          omega
        · norm_num [cliqueCapacity,Nat.choose]
          exact h12
      · exact book_lattice_four_bridge (by omega) hcap'
    by_cases hsEq5 : s=5
    · subst s
      have hcap' : k≤55 := by simpa [cliqueCapacity,Nat.choose] using hcap
      have hk11 : 11≤ k := by norm_num [Nat.choose] at hsmall; omega
      by_cases hkEq11 : k=11
      · subst k
        have hprev := ih 4 (by decide) 12 (by decide) (by decide)
          (by norm_num [cliqueCapacity,Nat.choose])
        have hp := book_lattice_promote hprev
        exact hp.mono_dilation (by decide)
      by_cases h42 : k≤42
      · apply book_lattice_threshold (by decide)
        · norm_num
          omega
        · norm_num [cliqueCapacity,Nat.choose]
          exact h42
      by_cases h53 : k≤53
      · exact book_lattice_five_bridge (by omega) h53
      · apply book_lattice_upper (by decide)
        · norm_num [bookUpperIntervalStart,Nat.choose]
          omega
        · exact hcap
    have hs6 : 6≤ s := by omega
    by_cases hprev : k+1≤ cliqueCapacity (s-1)
    · have hp := ih (s-1) (by omega) (k+1) (by omega) (by omega) hprev
      have hpromote := book_lattice_promote hp
      have he : s-1+1=s := by omega
      rw [he] at hpromote
      apply hpromote.mono_dilation
      have hchoose := two_mul_le_choose_two (show 5≤ s by omega)
      have hkbig : s-2≤ k := by omega
      have he' : s-1-1=s-2 := by omega
      have he'' : s-1=(s-2)+1 := by omega
      rw [he',he'']
      nlinarith
    · have hkstart : 2^(s-1)-s+1≤ k :=
        (threshold_start_le_previous_capacity hs6).trans (by omega)
      by_cases hthreshold : k≤ cliqueCapacity s-cliqueCapacity (s-1)+1
      · exact book_lattice_threshold (by omega) hkstart hthreshold
      · exact book_lattice_upper (by omega)
          ((upper_start_le_threshold_end hs6).trans (by omega)) hcap

/-- Exact lattice attainment of the dimension formula for all branch counts,
including counts above capacity. The extra vertices are genuine unused
coordinates, introduced by an injective extension of the actual set function. -/
theorem book_lattice_attainment (s k : ℕ) (hs : 2≤ s) (hk : 1≤ k) :
    LatticeExtremeAt (cliqueBook s k)
      (min (s+k-1) (s+cliqueCapacity s-1)) ((s-1)*min k (cliqueCapacity s)) := by
  have hcapPos : 1≤ cliqueCapacity s := by unfold cliqueCapacity; omega
  let m := min k (cliqueCapacity s)
  have hm : 1≤ m := le_min hk hcapPos
  have h := book_lattice_full s m hs hm (min_le_right _ _)
  have he := book_lattice_add_outer (min_le_left k (cliqueCapacity s)) h
  have hd : s+m-1=min (s+k-1) (s+cliqueCapacity s-1) := by
    dsimp only [m]
    by_cases hkc : k≤ cliqueCapacity s
    · rw [min_eq_left hkc,min_eq_left (by omega)]
    · rw [min_eq_right (by omega),min_eq_right (by omega)]
  rw [hd] at he
  exact he

end GraphicalZonotopes

end
end
end BundlePart196

section BundlePart197
/- Source: Papers/GraphicalZonotopes/SeparatorPaperStatements.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Separator
open Finset
open scoped BigOperators

/-- An order used only to select one orientation of every unordered edge.
It is supplied for every finite vertex type, rather than assumed as extra
mathematical structure on the graph. -/
def finiteVertexOrder (V : Type*) [Fintype V] : LinearOrder V :=
  LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective

/-- Lemma 5.1 on an arbitrary finite vertex type, with its orientation
convention chosen internally. There is no order hypothesis. -/
theorem induced_separator_capacity_finite {V : Type*} [Fintype V] :
    letI : LinearOrder V := finiteVertexOrder V;
    ∀ (G : SimpleGraph V) (B : Finset V) (z : graphicalFunctionSpace G),
      ExtremeSupermodular z.1 →
      Fintype.card (Gluing.ActiveBranch
        (((functionEquiv (componentPartition G B)).symm z).2)) ≤
        (∑ e : BoundaryEdge G B,
          2^(commonNeighbors G e.1.1.1 e.1.1.2 ∩ B).card) -
          (boundaryCliques G B).card + 1 := by
  letI : LinearOrder V := finiteVertexOrder V
  exact fun G B z hz => induced_separator_capacity G B z hz

/-- Theorem 7.2 for an arbitrary finite vertex type; an ordering used to
orient unordered edges is supplied internally. -/
theorem clique_separator_capacity_finite {V : Type*} [Fintype V] :
    letI : LinearOrder V := finiteVertexOrder V;
    ∀ (G : SimpleGraph V) (B : Finset V),G.IsClique B → 2≤ B.card →
      ∀ z : graphicalFunctionSpace G,ExtremeSupermodular z.1 →
        Fintype.card (Gluing.ActiveBranch
          (((functionEquiv (componentPartition G B)).symm z).2))≤ cliqueCapacity B.card := by
  letI : LinearOrder V := finiteVertexOrder V
  exact fun G B hB hs z hz => clique_separator_capacity hB hs z hz

section Ordered
variable {V J : Type*} [Fintype V] [LinearOrder V]
local instance : DecidableEq V := LinearOrder.toDecidableEq
variable [Fintype J] [DecidableEq J]
variable {G : SimpleGraph V} {B : Finset V} {A : J → Finset V}

/-- The literal closing-function transformation in the paper: adding a
boundary lift to each branch is compensated by subtracting the scaled sum
of those lifts from the closing function. The original function is equal. -/
theorem assembled_boundary_lift_transfer (h : Partition G B A)
    (f : ∀ j, privateIndex G B A j → ℝ)
    (l : J → boundaryIndex G B → ℝ)
    (z : boundaryIndex G B → ℝ) (lam : J → ℝ) :
    boundaryFunctionMap h (z - ∑ j, lam j • l j) +
      ∑ j, lam j • branchWithLift h j (f j) (l j) =
      globalFunctionMap h (Gluing.assemble z lam f) := by
  rw [assembled_boundary_lift_eq]
  simp only [sub_add_cancel]

/-- Every conclusion of Theorem 5.4, including membership in the original
normalized graphical cone, the exact dimension, the equivalence, the unique
positive relation, and the branch count. -/
def PositiveResponseGluingConclusion (h : Partition G B A)
    (f : ∀ j, privateIndex G B A j → ℝ)
    (z : boundaryIndex G B → ℝ) (lam : J → ℝ) : Prop :=
  let p := globalFunctionMap h (gluedCoordinates f z lam)
  let R := LinearMap.ker ((rowData h).relationLinear (conditionalMin h f))
  TranslationNormalized p ∧ Graphical G p ∧ Supermodular p ∧
    Module.finrank ℝ
      (Polyhedral.tightKernel (contextRow G)
        (functionEquiv h (gluedCoordinates f z lam))) = Module.finrank ℝ R ∧
    (ExtremeSupermodular p ↔ Module.finrank ℝ R = 1) ∧
    (ExtremeSupermodular p →
      R = Submodule.span ℝ {lam} ∧
      Fintype.card J ≤
        (∑ e : BoundaryEdge G B,
          2^(commonNeighbors G e.1.1.1 e.1.1.2 ∩ B).card) -
          (boundaryCliques G B).card + 1)

/-- Theorem 5.4 as one endpoint, using the literal equality of private
kernels with their one-dimensional spans. Boundary lifts are justified by
`lifted_relationLinear_eq` and `assembled_boundary_lift_eq`. -/
theorem positive_response_gluing (h : Partition G B A)
    (f : ∀ j, privateIndex G B A j → ℝ)
    (z : boundaryIndex G B → ℝ) (lam : J → ℝ)
    (hlam : ∀ j, 0 < lam j) (hf : ∀ j, f j ≠ 0)
    (hi : ∀ j r, 0 ≤ (rowData h).internal j r (f j))
    (hprivate : ∀ j, (rowData h).privateKernelSpace f (conditionalMin h f) j =
      Submodule.span ℝ {f j})
    (hclose : (rowData h).Closure (conditionalMin h f) z lam) :
    PositiveResponseGluingConclusion h f z lam := by
  have hline : ∀ j g, (rowData h).PrivateKernel f (conditionalMin h f) j g →
      ∃ c : ℝ, g = c • f j :=
    fun j => (Gluing.privateKernelSpace_eq_span_iff
      (rowData h) f (conditionalMin h f) j).mp (hprivate j)
  have hn := (functionEquiv h (gluedCoordinates f z lam)).2
  exact ⟨hn.1, hn.2, glued_supermodular h f z lam hlam hf hi hline hclose,
    graphical_tight_finrank_eq_relation_finrank h f z lam hlam hf hi hline hclose,
    graphical_extreme_iff_relation_finrank_one h f z lam hlam hf hi hline hclose,
    graphical_positive_relation_and_capacity h f z lam hlam hf hi hline hclose⟩

end Ordered

/-- The same complete gluing theorem for every finite vertex type. The
orientation order is constructed internally and is not an additional
hypothesis on the graph, its separator, or any branch function. -/
theorem positive_response_gluing_finite {V : Type*} [Fintype V] :
    letI : LinearOrder V := finiteVertexOrder V;
    ∀ {J : Type*} [Fintype J] [DecidableEq J]
      {G : SimpleGraph V} {B : Finset V} {A : J → Finset V}
      (h : Partition G B A)
      (f : ∀ j, privateIndex G B A j → ℝ)
      (z : boundaryIndex G B → ℝ) (lam : J → ℝ),
      (∀ j, 0 < lam j) → (∀ j, f j ≠ 0) →
      (∀ j r, 0 ≤ (rowData h).internal j r (f j)) →
      (∀ j, (rowData h).privateKernelSpace f (conditionalMin h f) j =
        Submodule.span ℝ {f j}) →
      (rowData h).Closure (conditionalMin h f) z lam →
      PositiveResponseGluingConclusion h f z lam := by
  letI : LinearOrder V := finiteVertexOrder V
  intro J _ _ G B A h f z lam hlam hf hi hprivate hclose
  exact positive_response_gluing h f z lam hlam hf hi hprivate hclose

end Separator
end GraphicalZonotopes

end
end
end BundlePart197

section BundlePart198
/- Source: Papers/GraphicalZonotopes/BookDimensionUpper.lean -/







/-! # The full upper bound and necessity in Theorem 7.1 -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.BookDimension
open Finset
attribute [local instance] Classical.propDecidable

abbrev Vertex (s k : ℕ) := Fin s ⊕ Fin k

local instance vertexOrder (s k : ℕ) : LinearOrder (Vertex s k) :=
  inferInstanceAs (LinearOrder (Fin s ⊕ₗ Fin k))

local instance vertexDecidableEq (s k : ℕ) : DecidableEq (Vertex s k) :=
  (vertexOrder s k).toDecidableEq

def boundary (s k : ℕ) : Finset (Vertex s k) :=
  univ.image (Sum.inl : Fin s → Vertex s k)

def privatePart (s k : ℕ) (j : Fin k) : Finset (Vertex s k) := {Sum.inr j}

@[simp] theorem boundary_card (s k : ℕ) : (boundary s k).card=s := by
  rw [boundary,card_image_of_injective _ Sum.inl_injective]
  simp

theorem boundary_clique (s k : ℕ) : (cliqueBook s k).IsClique (boundary s k) := by
  intro u hu v hv huv
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hu
  exact ⟨huv,Or.inl rfl⟩

theorem partition (s k : ℕ) :
    Separator.Partition (cliqueBook s k) (boundary s k) (privatePart s k) where
  boundary_disjoint j := by
    apply disjoint_left.mpr
    intro v hv hp
    have he : v=Sum.inr j := mem_singleton.mp hp
    obtain ⟨i,hi,hei⟩ := mem_image.mp hv
    exact Sum.inl_ne_inr (hei.trans he)
  private_disjoint := by
    intro i j hij
    exact disjoint_singleton.mpr (fun he => hij (Sum.inr_injective he))
  cover v := by
    cases v with
    | inl i => exact Or.inl (mem_image.mpr ⟨i,mem_univ _,rfl⟩)
    | inr j => exact Or.inr ⟨j,mem_singleton_self _⟩
  no_cross_edge := by
    intro i j u v hu hv huv
    have hu' : u=Sum.inr i := mem_singleton.mp hu
    have hv' : v=Sum.inr j := mem_singleton.mp hv
    subst u
    subst v
    have hf : False := by
      simpa only [cliqueBook,Sum.isLeft_inr,Bool.false_eq_true,or_self,and_false] using huv
    exact hf.elim

theorem extreme_dimension_bound (s k : ℕ) (hs : 2≤ s)
    (z : graphicalFunctionSpace (cliqueBook s k)) (hz : ExtremeSupermodular z.1) :
    Module.finrank ℝ (vectorSpan ℝ (basePolytope z.1))≤ s+cliqueCapacity s-1 := by
  have hb := Separator.finrank_le_boundary_add_active (partition s k)
    (fun j => by simp [privatePart]) z hz.2.1
  have hc := Separator.separator_capacity_for_function (partition s k) z hz
  rw [←Separator.boundaryRow_card,Separator.boundaryRow_card_of_clique (boundary_clique s k),
    Separator.boundaryCliques_card_of_clique (boundary_clique s k),boundary_card] at hc
  change _≤ cliqueCapacity s at hc
  rw [boundary_card] at hb
  omega

/-- Every actual weak indecomposable polytope summand satisfies the sharp
upper bound. Lower-dimensional summands and points are included. -/
theorem actual_summand_dimension_bound (s k : ℕ) (hs : 2≤ s)
    {Q : Set (Vertex s k → ℝ)} (hQ : IsFinitePolytope Q)
    (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s k))) :
    Module.finrank ℝ (vectorSpan ℝ Q)≤ min (s+k-1) (s+cliqueCapacity s-1) := by
  apply le_min
  · simpa only [Fintype.card_sum,Fintype.card_fin] using weak_summand_dimension_le hQ hi hw
  · obtain ⟨z,hz,hzero|hext,hd⟩ := weak_summand_extreme_or_zero hQ hi hw
    · rw [hd,hzero,basePolytope_zero,vectorSpan_singleton,finrank_bot]
      exact Nat.zero_le _
    · rw [hd]
      exact extreme_dimension_bound s k hs z hext

theorem maximum_dimension_upper (s k : ℕ) (hs : 2≤ s) :
    maximumIndecomposableDimension (cliqueBook s k)≤ min (s+k-1) (s+cliqueCapacity s-1) := by
  apply csSup_le'
  rintro d ⟨Q,hQ,hi,hw,hd⟩
  rw [←hd]
  exact actual_summand_dimension_bound s k hs hQ hi hw

theorem capacity_necessary (s k : ℕ) (hs : 2≤ s)
    (h : SupportsFullIndecomposable (cliqueBook s k)) : k≤ cliqueCapacity s := by
  obtain ⟨Q,hQ,hi,hd,hw⟩ := h
  have hb := actual_summand_dimension_bound s k hs hQ hi hw
  simp only [FullDimension,Fintype.card_sum,Fintype.card_fin] at hd
  rw [hd] at hb
  omega

end GraphicalZonotopes.BookDimension

end
end
end BundlePart198

section BundlePart199
/- Source: Papers/GraphicalZonotopes/BookPrincipal.lean -/







/-! # Exact clique-book classification, with lattice attainment -/

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open scoped Pointwise

/-- Theorem 7.1, preserving every hub count, every branch count, the full
polytope maximum, the capacity equivalence, and the stated integral dilation. -/
theorem clique_book_classification : Targets.CliqueBookClassification := by
  intro s k hs hk
  have hatt := book_lattice_attainment s k hs hk
  refine ⟨le_antisymm (BookDimension.maximum_dimension_upper s k hs)
    hatt.dimension_le_maximum,?_,hatt.polytope⟩
  constructor
  · exact BookDimension.capacity_necessary s k hs
  · intro hcap
    have hfull := book_lattice_full s k hs hk hcap
    apply LatticeExtremeAt.supports_full
    simpa only [Fintype.card_sum,Fintype.card_fin] using hfull

/-- The literal polytopal version of Theorem 7.1. The equivalence of the
dimension invariant and the supporting predicate is proved, not assumed. -/
theorem clique_book_classification_polytopal (s k : ℕ) (hs : 2≤ s) (hk : 1≤ k) :
    (sSup {d : ℕ | ∃ Q : Set ((Fin s⊕Fin k) → ℝ),IsFinitePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s k)) ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=d}) =
        min (s+k-1) (s+cliqueCapacity s-1) ∧
    ((∃ Q : Set ((Fin s⊕Fin k) → ℝ),IsFinitePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s k))) ↔
        k≤ cliqueCapacity s) ∧
    ∃ Q : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=min (s+k-1) (s+cliqueCapacity s-1) ∧
      IsMinkowskiSummand Q ((((s-1)*min k (cliqueCapacity s) : ℕ) : ℝ) •
        graphicalZonotope (cliqueBook s k)) := by
  obtain ⟨hd,hfull,Q,hQ,hi,hDim,hSum⟩ := clique_book_classification s k hs hk
  refine ⟨?_,?_,Q,hQ,?_,hDim,hSum⟩
  · rw [←maximumIndecomposableDimension_eq_polytopal_supremum]
    exact hd
  · rw [←supportsFullIndecomposable_iff_polytopal_weak]
    exact hfull
  · exact ⟨hi.1,fun P R hP hR he =>
      hi.2 P R hP.compact hR.compact hP.convex hR.convex he⟩

end GraphicalZonotopes

end
end
end BundlePart199

section BundlePart200
/- Source: Papers/GraphicalZonotopes/Corollary69.lean -/






/-! # Corollary 6.9

The three clauses are `three_hub_book_maximum`,
`TreeJoin.paper_corollary_6_9_tree_join`, and
`hamiltonian_threeTree_lattice_polytopal_finite`. The latter two include
lattice attainment and ordinary polytopal Minkowski indecomposability.
-/

@[expose] public section
noncomputable section
namespace GraphicalZonotopes

theorem three_hub_book_maximum (k : ℕ) (hk : 1≤ k) :
    maximumIndecomposableDimension (cliqueBook 3 k)=min (k+2) 5 := by
  have h := (clique_book_classification 3 k (by decide) hk).1
  have hc : cliqueCapacity 3=3 := by decide
  rw [hc] at h
  have hn : 3+k-1=k+2 := by omega
  simpa only [hn] using h

end GraphicalZonotopes

end
end
end BundlePart200

section BundlePart201
/- Source: Papers/GraphicalZonotopes/CubeCells.lean -/








@[expose] public section
noncomputable section
namespace GraphicalZonotopes.TwoHub
open Finset

/-- A Boolean cube cell fixes a set of coordinates and assigns one to a
subset of those coordinates. The other coordinates are free. -/
structure Cell (I : Type*) where
  fixed : Finset I
  ones : Finset I
  ones_subset : ones⊆fixed
  deriving DecidableEq

variable {I : Type*} [Fintype I] [DecidableEq I]

def Cell.assignment (C : Cell I) : Finset C.fixed :=
  univ.filter (fun i => i.1∈C.ones)

def Cell.pull (C : Cell I) (Y : Finset I) : Finset C.fixed :=
  univ.filter (fun i => i.1∈Y)

def Cell.Matches (C : Cell I) (Y : Finset I) : Prop := C.pull Y=C.assignment

instance (C : Cell I) (Y : Finset I) : Decidable (C.Matches Y) :=
  inferInstanceAs (Decidable (C.pull Y=C.assignment))
@[simp] theorem Cell.mem_assignment (C : Cell I) (i : C.fixed) :
    i∈C.assignment ↔ i.1∈C.ones := by simp [Cell.assignment]
@[simp] theorem Cell.mem_pull (C : Cell I) (Y : Finset I) (i : C.fixed) :
    i∈C.pull Y ↔ i.1∈Y := by simp [Cell.pull]

theorem Cell.matches_iff (C : Cell I) {Y : Finset I} :
    C.Matches Y ↔ ∀ i∈C.fixed,(i∈Y ↔ i∈C.ones) := by
  constructor
  · intro h i hi
    have hh:=Finset.ext_iff.mp h (⟨i,hi⟩ : C.fixed)
    simpa using hh
  · intro h
    apply Finset.ext
    intro i
    simpa using h i.1 i.2

theorem Cell.matches_ones (C : Cell I) : C.Matches C.ones := by
  apply C.matches_iff.mpr
  intro i hi
  rfl


/-- Splitting a cell on a previously free coordinate preserves its cube
and gives two disjoint nonempty subcells. -/
def Cell.splitZero (C : Cell I) (i : I) : Cell I where
  fixed:=insert i C.fixed
  ones:=C.ones
  ones_subset:=C.ones_subset.trans (subset_insert i C.fixed)

def Cell.splitOne (C : Cell I) (i : I) : Cell I where
  fixed:=insert i C.fixed
  ones:=insert i C.ones
  ones_subset:=insert_subset_insert i C.ones_subset

theorem Cell.matches_splitZero (C : Cell I) (i : I) (hi : i∉C.fixed) (Y : Finset I) :
    (C.splitZero i).Matches Y ↔ C.Matches Y ∧ i∉Y := by
  have hio : i∉C.ones:=fun h => hi (C.ones_subset h)
  constructor
  · intro h
    have hh:=(C.splitZero i).matches_iff.mp h
    refine ⟨C.matches_iff.mpr (fun j hj => hh j (mem_insert_of_mem hj)),?_⟩
    have he:=hh i (mem_insert_self i C.fixed)
    exact fun hy => hio (he.mp hy)
  · rintro ⟨h,hY⟩
    apply (C.splitZero i).matches_iff.mpr
    intro j hj
    rcases mem_insert.mp hj with rfl|hj
    · simp [Cell.splitZero,hY,hio]
    · exact C.matches_iff.mp h j hj

theorem Cell.matches_splitOne (C : Cell I) (i : I) (hi : i∉C.fixed) (Y : Finset I) :
    (C.splitOne i).Matches Y ↔ C.Matches Y ∧ i∈Y := by
  constructor
  · intro h
    have hh:=(C.splitOne i).matches_iff.mp h
    refine ⟨C.matches_iff.mpr ?_,?_⟩
    · intro j hj
      have hji : j≠ i:=fun he => hi (he ▸ hj)
      simpa [Cell.splitOne,hji] using hh j (mem_insert_of_mem hj)
    · exact (hh i (mem_insert_self i C.fixed)).mpr (mem_insert_self i C.ones)
  · rintro ⟨h,hY⟩
    apply (C.splitOne i).matches_iff.mpr
    intro j hj
    rcases mem_insert.mp hj with rfl|hj
    · simp [Cell.splitOne,hY]
    · have hji : j≠ i:=fun he => hi (he ▸ hj)
      simpa [Cell.splitOne,hji] using C.matches_iff.mp h j hj

theorem Cell.splitZero_ne (C : Cell I) (i : I) (hi : i∉C.fixed) : C.splitZero i≠ C := by
  intro h
  have he:=congrArg Cell.fixed h
  exact hi (he ▸ mem_insert_self i C.fixed)

theorem Cell.splitOne_ne (C : Cell I) (i : I) (hi : i∉C.fixed) : C.splitOne i≠ C := by
  intro h
  have he:=congrArg Cell.fixed h
  exact hi (he ▸ mem_insert_self i C.fixed)

theorem Cell.split_ne (C : Cell I) (i : I) (hi : i∉C.fixed) : C.splitZero i≠ C.splitOne i := by
  intro h
  have he:=congrArg Cell.ones h
  have hm : i∈C.ones := he.symm ▸ mem_insert_self i C.ones
  exact hi (C.ones_subset hm)

def Cell.root : Cell I where
  fixed:=∅
  ones:=∅
  ones_subset:=Subset.rfl

@[simp] theorem Cell.root_matches (Y : Finset I) : (Cell.root (I:=I)).Matches Y := by
  apply (Cell.matches_iff Cell.root).mpr
  simp [Cell.root]

namespace CubePartition

def Valid (F : Finset (Cell I)) : Prop := ∀ Y : Finset I,∃! C,C∈F ∧ C.Matches Y

def UsesZero (F : Finset (Cell I)) (A : Finset I) : Prop :=
  ∀ i∈A,∃ C∈F,i∈C.fixed ∧ i∉C.ones

theorem Valid.unique {F : Finset (Cell I)} (hF : Valid F) {Y : Finset I}
    {C D : Cell I} (hC : C∈F) (hD : D∈F) (hCY : C.Matches Y) (hDY : D.Matches Y) : C=D := by
  obtain ⟨E,hE,hu⟩:=hF Y
  exact (hu C ⟨hC,hCY⟩).trans (hu D ⟨hD,hDY⟩).symm

theorem root_valid : Valid ({Cell.root} : Finset (Cell I)) := by
  intro Y
  refine ⟨Cell.root,⟨mem_singleton_self _,Cell.root_matches Y⟩,?_⟩
  intro C hC
  exact mem_singleton.mp hC.1

def refine (F : Finset (Cell I)) (C : Cell I) (i : I) : Finset (Cell I) :=
  insert (C.splitZero i) (insert (C.splitOne i) (F.erase C))

theorem Valid.splitZero_not_mem {F : Finset (Cell I)} (hF : Valid F)
    {C : Cell I} (hC : C∈F) (i : I) (hi : i∉C.fixed) : C.splitZero i∉F := by
  intro hz
  have hm:=(C.matches_splitZero i hi (C.splitZero i).ones).mp (C.splitZero i).matches_ones
  exact C.splitZero_ne i hi (hF.unique hz hC (C.splitZero i).matches_ones hm.1)

theorem Valid.splitOne_not_mem {F : Finset (Cell I)} (hF : Valid F)
    {C : Cell I} (hC : C∈F) (i : I) (hi : i∉C.fixed) : C.splitOne i∉F := by
  intro hz
  have hm:=(C.matches_splitOne i hi (C.splitOne i).ones).mp (C.splitOne i).matches_ones
  exact C.splitOne_ne i hi (hF.unique hz hC (C.splitOne i).matches_ones hm.1)

theorem Valid.refine_card {F : Finset (Cell I)} (hF : Valid F)
    {C : Cell I} (hC : C∈F) (i : I) (hi : i∉C.fixed) :
    (refine F C i).card=F.card+1 := by
  have h0:=hF.splitZero_not_mem hC i hi
  have h1:=hF.splitOne_not_mem hC i hi
  have h01:=C.split_ne i hi
  have h0e : C.splitZero i∉F.erase C := fun h => h0 (mem_of_mem_erase h)
  have h1e : C.splitOne i∉F.erase C := fun h => h1 (mem_of_mem_erase h)
  have h0i : C.splitZero i∉insert (C.splitOne i) (F.erase C) := by simp [h01,h0e]
  rw [refine,card_insert_of_notMem h0i,card_insert_of_notMem h1e,card_erase_of_mem hC]
  have hp:=card_pos.mpr ⟨C,hC⟩
  omega

theorem Valid.refine_valid {F : Finset (Cell I)} (hF : Valid F)
    {C : Cell I} (hC : C∈F) (i : I) (hi : i∉C.fixed) : Valid (refine F C i) := by
  intro Y
  have hparent {D : Cell I} (hD : D∈refine F C i) (hDY : D.Matches Y) :
      D=C.splitZero i ∨ D=C.splitOne i ∨ (D∈F ∧ D≠ C) := by
    simp only [refine,mem_insert,mem_erase] at hD
    rcases hD with h|h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h.2,h.1⟩)
  obtain ⟨D,hD,huniq⟩:=hF Y
  by_cases hDC : D=C
  · subst D
    by_cases hY : i∈Y
    · refine ⟨C.splitOne i,⟨by simp [refine],(C.matches_splitOne i hi Y).mpr ⟨hD.2,hY⟩⟩,?_⟩
      intro E hE
      rcases hparent hE.1 hE.2 with h|h|h
      · subst E
        exact False.elim (((C.matches_splitZero i hi Y).mp hE.2).2 hY)
      · exact h
      · exact False.elim (h.2 (huniq E ⟨h.1,hE.2⟩))
    · refine ⟨C.splitZero i,⟨by simp [refine],(C.matches_splitZero i hi Y).mpr ⟨hD.2,hY⟩⟩,?_⟩
      intro E hE
      rcases hparent hE.1 hE.2 with h|h|h
      · exact h
      · subst E
        exact False.elim (hY ((C.matches_splitOne i hi Y).mp hE.2).2)
      · exact False.elim (h.2 (huniq E ⟨h.1,hE.2⟩))
  · refine ⟨D,⟨by simp [refine,hDC,hD.1],hD.2⟩,?_⟩
    intro E hE
    rcases hparent hE.1 hE.2 with h|h|h
    · subst E
      have hm:=(C.matches_splitZero i hi Y).mp hE.2
      exact False.elim (hDC (huniq C ⟨hC,hm.1⟩).symm)
    · subst E
      have hm:=(C.matches_splitOne i hi Y).mp hE.2
      exact False.elim (hDC (huniq C ⟨hC,hm.1⟩).symm)
    · exact huniq E ⟨h.1,hE.2⟩

theorem UsesZero.refine {F : Finset (Cell I)} {A : Finset I} (hF : UsesZero F A)
    {C : Cell I} (hC : C∈F) (i : I) (hi : i∉C.fixed) : UsesZero (refine F C i) (insert i A) := by
  intro j hj
  rcases mem_insert.mp hj with hji|hj
  · subst j
    refine ⟨C.splitZero i,by simp [CubePartition.refine],by simp [Cell.splitZero],?_⟩
    exact fun h => hi (C.ones_subset h)
  · obtain ⟨D,hD,hjD,hj0⟩:=hF j hj
    by_cases hDC : D=C
    · subst D
      exact ⟨C.splitZero i,by simp [CubePartition.refine],mem_insert_of_mem hjD,hj0⟩
    · exact ⟨D,by simp [CubePartition.refine,hDC,hD],hjD,hj0⟩


/-- Distinct cells of a partition have distinct canonical vertices. -/
theorem Valid.ones_injective {F : Finset (Cell I)} (hF : Valid F) :
    Set.InjOn Cell.ones (F : Set (Cell I)) := by
  intro C hC D hD hCD
  apply hF.unique hC hD C.matches_ones
  simpa only [hCD] using D.matches_ones

theorem Valid.card_le {F : Finset (Cell I)} (hF : Valid F) :
    F.card≤2^Fintype.card I := by
  have hh:=card_le_card (subset_univ (F.image Cell.ones))
  rw [card_image_of_injOn hF.ones_injective] at hh
  simpa using hh

/-- Unless every cell is a point, some cell can still be split. -/
theorem Valid.exists_free {F : Finset (Cell I)} (hF : Valid F)
    (hlt : F.card<2^Fintype.card I) : ∃ C∈F,∃ i : I,i∉C.fixed := by
  by_contra h
  have hfixed : ∀ C∈F,∀ i : I,i∈C.fixed := by
    intro C hC i
    by_contra hi
    exact h ⟨C,hC,i,hi⟩
  have hcover : (univ : Finset (Finset I))⊆F.image Cell.ones := by
    intro Y hY
    obtain ⟨C,hC,hunique⟩:=hF Y
    have he : C.ones=Y := by
      ext i
      exact (C.matches_iff.mp hC.2 i (hfixed C hC.1 i)).symm
    exact mem_image.mpr ⟨C,hC.1,he⟩
  have hh:=(card_le_card hcover).trans (card_image_le)
  have hh' : 2^Fintype.card I≤ F.card := by simpa using hh
  exact (Nat.not_le_of_lt hlt) hh'

theorem Valid.fixed_nonempty {F : Finset (Cell I)} (hF : Valid F)
    (hcard : 2≤ F.card) {C : Cell I} (hC : C∈F) : C.fixed.Nonempty := by
  by_contra h
  have hf : C.fixed=∅:=not_nonempty_iff_eq_empty.mp h
  have hsub : F⊆{C} := by
    intro D hD
    apply mem_singleton.mpr
    apply hF.unique hD hC D.matches_ones
    apply C.matches_iff.mpr
    simp [hf]
  have hh:=card_le_card hsub
  simp only [card_singleton] at hh
  omega

/-- A chain of coordinate splits supplies a partition with one more cell
than coordinates split. It uses a zero assignment in every such coordinate. -/
theorem exists_chain (A : Finset I) :
    ∃ F : Finset (Cell I),Valid F ∧ F.card=A.card+1 ∧ UsesZero F A ∧
      ∀ C∈F,C.fixed⊆A := by
  induction A using Finset.induction_on with
  | empty =>
      refine ⟨{Cell.root},root_valid,by simp,?_,?_⟩
      · intro i hi
        simp at hi
      · intro C hC
        have he:=mem_singleton.mp hC
        subst C
        exact Subset.rfl
  | @insert i A hi ih =>
      obtain ⟨F,hF,hcard,huses,hfixed⟩:=ih
      obtain ⟨C,hC,huniq⟩:=hF ∅
      have hif : i∉C.fixed:=fun hh => hi (hfixed C hC.1 hh)
      refine ⟨refine F C i,hF.refine_valid hC.1 i hif,?_,huses.refine hC.1 i hif,?_⟩
      · rw [hF.refine_card hC.1 i hif,hcard,card_insert_of_notMem hi]
      · intro D hD
        simp only [refine,mem_insert,mem_erase] at hD
        rcases hD with rfl|rfl|hD
        · exact insert_subset_insert i (hfixed C hC.1)
        · exact insert_subset_insert i (hfixed C hC.1)
        · exact (hfixed D hD.2).trans (subset_insert i A)

/-- Every cardinality between the coordinate chain and the point partition
is attained by successive splits. The zero-assignment condition survives. -/
theorem exists_card (k : ℕ) (hlo : Fintype.card I+1≤ k)
    (hhi : k≤2^Fintype.card I) :
    ∃ F : Finset (Cell I),Valid F ∧ F.card=k ∧ UsesZero F univ := by
  have hstep : ∀ n,Fintype.card I+1≤ n → n≤2^Fintype.card I →
      ∃ F : Finset (Cell I),Valid F ∧ F.card=n ∧ UsesZero F univ := by
    intro n hn
    induction n,hn using Nat.le_induction with
    | base =>
        intro htop
        obtain ⟨F,hF,hcard,huses,hfixed⟩:=exists_chain (univ : Finset I)
        exact ⟨F,hF,by simpa using hcard,huses⟩
    | succ n hn ih =>
        intro htop
        obtain ⟨F,hF,hcard,huses⟩:=ih (by omega)
        have hlt : F.card<2^Fintype.card I:=by omega
        obtain ⟨C,hC,i,hi⟩:=hF.exists_free hlt
        refine ⟨refine F C i,hF.refine_valid hC i hi,?_,?_⟩
        · rw [hF.refine_card hC i hi,hcard]
        · simpa only [insert_eq_of_mem (mem_univ i)] using huses.refine hC i hi
  exact hstep k hlo hhi

/-- The partition required for the intermediate range of Theorem 8.7. -/
theorem exists_proper_card [Nonempty I] (k : ℕ) (hlo : Fintype.card I+1≤ k)
    (hhi : k≤2^Fintype.card I) :
    ∃ F : Finset (Cell I),Valid F ∧ F.card=k ∧ UsesZero F univ ∧
      ∀ C∈F,C.fixed.Nonempty := by
  obtain ⟨F,hF,hcard,huses⟩:=exists_card k hlo hhi
  have hpos:=Fintype.card_pos (α:=I)
  refine ⟨F,hF,hcard,huses,?_⟩
  intro C hC
  exact hF.fixed_nonempty (by omega) hC

end CubePartition

end GraphicalZonotopes.TwoHub

end
end
end BundlePart201

section BundlePart202
/- Source: Papers/GraphicalZonotopes/CubeDecisionTree.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes.TwoHub
open Finset
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A full binary coordinate decision tree rooted at a cube cell. The `fresh`
condition expresses exactly that a coordinate is never tested twice along one
root-to-leaf path. -/
inductive CellDecisionTree : Cell I → Type _ where
  | leaf (C : Cell I) : CellDecisionTree C
  | node (C : Cell I) (i : I) (fresh : i∉C.fixed)
      (zero : CellDecisionTree (C.splitZero i))
      (one : CellDecisionTree (C.splitOne i)) : CellDecisionTree C

namespace CellDecisionTree

def leaves {C : Cell I} : CellDecisionTree C → Finset (Cell I)
  | .leaf C => {C}
  | .node _ _ _ zero one => zero.leaves∪one.leaves

def tested {C : Cell I} : CellDecisionTree C → Finset I
  | .leaf _ => ∅
  | .node _ i _ zero one => insert i (zero.tested∪one.tested)

def leafCount {C : Cell I} : CellDecisionTree C → ℕ
  | .leaf _ => 1
  | .node _ _ _ zero one => zero.leafCount+one.leafCount

theorem leaves_nonempty {C : Cell I} (T : CellDecisionTree C) : T.leaves.Nonempty := by
  induction T with
  | leaf C => exact singleton_nonempty C
  | node C i hi zero one ihz iho => exact ihz.mono subset_union_left

theorem fixed_subset {C : Cell I} (T : CellDecisionTree C) {D : Cell I}
    (hD : D∈T.leaves) : C.fixed⊆D.fixed := by
  induction T with
  | leaf C =>
      have he : D=C := mem_singleton.mp hD
      subst D
      exact Subset.rfl
  | node C i hi zero one ihz iho =>
      rcases mem_union.mp hD with hz|ho
      · exact (subset_insert i C.fixed).trans (ihz hz)
      · exact (subset_insert i C.fixed).trans (iho ho)

theorem matches_parent {C : Cell I} (T : CellDecisionTree C) {D : Cell I}
    (hD : D∈T.leaves) {Y : Finset I} (hY : D.Matches Y) : C.Matches Y := by
  induction T with
  | leaf C =>
      have he : D=C := mem_singleton.mp hD
      exact he ▸ hY
  | node C i hi zero one ihz iho =>
      rcases mem_union.mp hD with hz|ho
      · exact ((C.matches_splitZero i hi Y).mp (ihz hz)).1
      · exact ((C.matches_splitOne i hi Y).mp (iho ho)).1

theorem children_disjoint (C : Cell I) (i : I) (hi : i∉C.fixed)
    (zero : CellDecisionTree (C.splitZero i))
    (one : CellDecisionTree (C.splitOne i)) : Disjoint zero.leaves one.leaves := by
  apply disjoint_left.mpr
  intro D hz ho
  have h0 := (C.matches_splitZero i hi D.ones).mp (zero.matches_parent hz D.matches_ones)
  have h1 := (C.matches_splitOne i hi D.ones).mp (one.matches_parent ho D.matches_ones)
  exact h0.2 h1.2

theorem leaves_card {C : Cell I} (T : CellDecisionTree C) : T.leaves.card=T.leafCount := by
  induction T with
  | leaf C => simp [leaves,leafCount]
  | node C i hi zero one ihz iho =>
      rw [leaves,card_union_of_disjoint (children_disjoint C i hi zero one),ihz,iho]
      rfl

theorem exists_unique_match {C : Cell I} (T : CellDecisionTree C) {Y : Finset I}
    (hY : C.Matches Y) : ∃! D,D∈T.leaves ∧ D.Matches Y := by
  induction T with
  | leaf C =>
      refine ⟨C,⟨mem_singleton_self _,hY⟩,?_⟩
      intro D hD
      exact mem_singleton.mp hD.1
  | node C i hi zero one ihz iho =>
      by_cases hy : i∈Y
      · obtain ⟨D,hD,hu⟩ := iho ((C.matches_splitOne i hi Y).mpr ⟨hY,hy⟩)
        refine ⟨D,⟨mem_union_right _ hD.1,hD.2⟩,?_⟩
        intro E hE
        rcases mem_union.mp hE.1 with hz|ho
        · exact False.elim (((C.matches_splitZero i hi Y).mp
            (zero.matches_parent hz hE.2)).2 hy)
        · exact hu E ⟨ho,hE.2⟩
      · obtain ⟨D,hD,hu⟩ := ihz ((C.matches_splitZero i hi Y).mpr ⟨hY,hy⟩)
        refine ⟨D,⟨mem_union_left _ hD.1,hD.2⟩,?_⟩
        intro E hE
        rcases mem_union.mp hE.1 with hz|ho
        · exact hu E ⟨hz,hE.2⟩
        · exact False.elim (hy ((C.matches_splitOne i hi Y).mp
            (one.matches_parent ho hE.2)).2)

theorem uses_zero {C : Cell I} (T : CellDecisionTree C) :
    CubePartition.UsesZero T.leaves T.tested := by
  induction T with
  | leaf C => intro i hi; simp [tested] at hi
  | node C i hi zero one ihz iho =>
      intro j hj
      rcases mem_insert.mp hj with hji|hj
      · subst j
        obtain ⟨D,hD⟩ := zero.leaves_nonempty
        have hm := (C.matches_splitZero i hi D.ones).mp
          (zero.matches_parent hD D.matches_ones)
        exact ⟨D,mem_union_left _ hD,
          zero.fixed_subset hD (mem_insert_self i C.fixed),hm.2⟩
      · rcases mem_union.mp hj with hz|ho
        · obtain ⟨D,hD,hf,hn⟩ := ihz j hz
          exact ⟨D,mem_union_left _ hD,hf,hn⟩
        · obtain ⟨D,hD,hf,hn⟩ := iho j ho
          exact ⟨D,mem_union_right _ hD,hf,hn⟩

theorem root_valid (T : CellDecisionTree (Cell.root (I:=I))) :
    CubePartition.Valid T.leaves := by
  intro Y
  exact T.exists_unique_match (Cell.root_matches Y)

theorem root_proper [Nonempty I] (T : CellDecisionTree (Cell.root (I:=I)))
    (h : T.tested=univ) : ∀ C∈T.leaves,C.fixed.Nonempty := by
  have ht : T.tested.Nonempty := by rw [h]; exact univ_nonempty
  have hc : 2≤ T.leaves.card := by
    cases T with
    | leaf C => simp [tested] at ht
    | node C i hi zero one =>
        rw [leaves,card_union_of_disjoint (children_disjoint Cell.root i hi zero one)]
        have hz := card_pos.mpr zero.leaves_nonempty
        have ho := card_pos.mpr one.leaves_nonempty
        omega
  exact fun C hC => T.root_valid.fixed_nonempty hc hC

end CellDecisionTree
end GraphicalZonotopes.TwoHub

end
end
end BundlePart202

section BundlePart203
/- Source: Papers/GraphicalZonotopes/GeneralBranchAssembly.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise
variable {H J : Type*} [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]

/-- Arbitrary monotone branch functions are allowed. Booleanity is needed
only in the earlier convenient sufficient criterion for private rigidity. -/
theorem assembled_normalized_general {z : SetFunction H} (hz : TranslationNormalized z)
    (F : J → SetFunction H) (hF : ∀ j,F j ∅=0) (w : J → ℝ) :
    TranslationNormalized (assembled z F w) := by
  have hb:=boundaryLift_normalized (J:=J) hz
  have hp:=fun j => branchLift_normalized j (hF j)
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

theorem response_factor_nonnegative (F : SetFunction H) (u v : H)
    (X : Finset H) (x : ℝ) (hx : x=0 ∨ x=1) :
    0≤ negativeResponse F u v X+x*delta F u v X := by
  rcases hx with rfl | rfl
  · simp only [zero_mul,add_zero,negativeResponse]
    exact le_max_left _ _
  · simp only [one_mul,negativeResponse]
    have h:=le_max_right (0 : ℝ) (-delta F u v X)
    linarith

theorem assembled_supermodular_general (z : SetFunction H) (F : J → SetFunction H)
    (hF : ∀ j a X,0≤ F j (insert a X)-F j X) (w : J → ℝ)
    (hw : ∀ j,0≤ w j) (hc : Compatible z F w) :
    Supermodular (assembled z F w) := by
  apply ElementallyNonnegative.supermodular
  intro a b hab A ha hb
  cases a with
  | inl u =>
    cases b with
    | inl v =>
      rw [assembled_factorization z F w hc u v
        (fun he => hab (congrArg Sum.inl he)) A ha hb]
      apply sum_nonneg
      intro j hj
      apply mul_nonneg (hw j)
      apply response_factor_nonnegative
      split_ifs <;> simp
    | inr j =>
      rw [delta_assembled_spoke z F w u j A hb]
      exact mul_nonneg (hw j) (hF j u (hubs A))
  | inr i =>
    cases b with
    | inl v =>
      rw [delta_swap,delta_assembled_spoke z F w v i A ha]
      exact mul_nonneg (hw i) (hF i v (hubs A))
    | inr j =>
      rw [delta_assembled_outer z F w i j
        (fun he => hab (congrArg Sum.inr he)) A ha hb]

def minimizingOutersGeneral (F : J → SetFunction H) (u v : H)
    (X : Finset H) : Finset J := univ.filter (fun j => delta (F j) u v X<0)

@[simp] theorem mem_minimizingOutersGeneral (F : J → SetFunction H)
    (u v : H) (X : Finset H) (j : J) :
    j∈minimizingOutersGeneral F u v X ↔ delta (F j) u v X<0 := by
  simp [minimizingOutersGeneral]

theorem minimizing_general_literal (F : SetFunction H) (u v : H) (X : Finset H) :
    (if delta F u v X<0 then delta F u v X else 0)=
      -negativeResponse F u v X := by
  unfold negativeResponse
  by_cases h : delta F u v X<0
  · rw [if_pos h,max_eq_right (by linarith)]
    ring
  · rw [if_neg h,max_eq_left (by linarith),neg_zero]

theorem assembled_minimizer_zero_general {z : SetFunction H}
    {F : J → SetFunction H} {w : J → ℝ} (hc : Compatible z F w)
    (u v : H) (huv : u≠ v) (X : Finset H) (hu : u∉X) (hv : v∉X) :
    delta (assembled z F w) (Sum.inl u) (Sum.inl v)
      (context X (minimizingOutersGeneral F u v X))=0 := by
  rw [delta_assembled_hubs,hubs_context,hc u v huv X hu hv]
  have he : (∑ j : J,w j*(if Sum.inr j∈context X (minimizingOutersGeneral F u v X)
        then delta (F j) u v X else 0))= -(∑ j : J,w j*negativeResponse (F j) u v X) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro j hj
    simp only [mem_context_outer,mem_minimizingOutersGeneral,minimizing_general_literal,mul_neg]
  rw [he,add_neg_cancel]

theorem compatible_of_tight_variation_general {z h : SetFunction H}
    {F : J → SetFunction H} {w t : J → ℝ} (hc : Compatible z F w)
    (ht : ∀ u v,u≠ v → ∀ A,u∉A → v∉A →
      delta (assembled z F w) u v A=0 → delta (assembled h F t) u v A=0) :
    Compatible h F t := by
  intro u v huv X hu hv
  have hz:=ht (Sum.inl u) (Sum.inl v) (fun he => huv (Sum.inl_injective he))
    (context X (minimizingOutersGeneral F u v X)) (by simpa using hu) (by simpa using hv)
    (assembled_minimizer_zero_general hc u v huv X hu hv)
  rw [delta_assembled_hubs,hubs_context] at hz
  have he : (∑ j : J,t j*(if Sum.inr j∈context X (minimizingOutersGeneral F u v X)
        then delta (F j) u v X else 0))= -(∑ j : J,t j*negativeResponse (F j) u v X) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro j hj
    simp only [mem_context_outer,mem_minimizingOutersGeneral,minimizing_general_literal,mul_neg]
  rw [he] at hz
  linarith

theorem function_eq_private_assembly {f : SetFunction (H⊕J)} (hf : OuterZero f) :
    f=assembled (boundarySlice f) (privateSlice f) (fun _ => 1) := by
  apply eq_assembled_of_privateSlices hf
  intro j
  exact (one_smul ℝ _).symm

theorem delta_assembled_insert_outer (z : SetFunction H)
    (F : J → SetFunction H) (w : J → ℝ) (u v : H) (X : Finset H)
    (Y : Finset J) (j : J) (hj : j∉Y) :
    delta (assembled z F w) (Sum.inl u) (Sum.inl v) (context X (insert j Y))-
      delta (assembled z F w) (Sum.inl u) (Sum.inl v) (context X Y)=
        w j*delta (F j) u v X := by
  simp only [delta_assembled_hubs,hubs_context,mem_context_outer]
  have hsum : (∑ i : J,w i*(if i∈insert j Y then delta (F i) u v X else 0))=
      w j*delta (F j) u v X+∑ i : J,w i*(if i∈Y then delta (F i) u v X else 0) := by
    simp only [mul_ite,mul_zero]
    rw [← sum_filter,← sum_filter]
    have hY : (univ.filter (fun i => i∈Y))=Y := by ext i; simp
    have hI : (univ.filter (fun i => i∈insert j Y))=insert j Y := by ext i; simp
    rw [hI,hY,sum_insert hj]
  rw [hsum]
  ring

/-- These are precisely the local spoke equations and the differences of
minimizing boundary equations used by the non-Boolean modules of Section 8. -/
def PrivateRigid (F : SetFunction H) : Prop :=
  ∀ f : SetFunction H,f ∅=0 →
    (∀ a X,a∉X → F (insert a X)-F X=0 → f (insert a X)-f X=0) →
    (∀ u v,u≠ v → ∀ X,u∉X → v∉X → delta F u v X=0 → delta f u v X=0) →
    ∃ c : ℝ,f=c • F

theorem privateSlice_scalar_general {z : SetFunction H}
    {F : J → SetFunction H} {w : J → ℝ} (hc : Compatible z F w)
    (hF : ∀ j,PrivateRigid (F j))
    {f : SetFunction (H⊕J)} (hf : TranslationNormalized f)
    (ht : ∀ u v,u≠ v → ∀ A,u∉A → v∉A →
      delta (assembled z F w) u v A=0 → delta f u v A=0) (j : J) :
    ∃ c : ℝ,privateSlice f j=c • F j := by
  have hout : OuterZero f := by
    intro i k hik A hi hk
    exact ht (Sum.inr i) (Sum.inr k) (fun he => hik (Sum.inr_injective he)) A hi hk
      (delta_assembled_outer z F w i k hik A hi hk)
  apply hF j (privateSlice f j) (privateSlice_empty hf j)
  · intro a X ha hz
    rw [privateSlice_cover]
    apply ht (Sum.inl a) (Sum.inr j) (by simp) (hubSet X)
      (by simpa using ha) (notMem_hubSet_outer X j)
    rw [delta_assembled_spoke _ _ _ _ _ _ (notMem_hubSet_outer X j),hubs_hubSet,hz,mul_zero]
  · intro u v huv X hu hv hz
    let Y:=minimizingOutersGeneral F u v X
    have hj : j∉Y := by simp [Y,hz]
    have hz0 := assembled_minimizer_zero_general hc u v huv X hu hv
    have hz1 : delta (assembled z F w) (Sum.inl u) (Sum.inl v)
        (context X (insert j Y))=0 := by
      have hdiff := delta_assembled_insert_outer z F w u v X Y j hj
      rw [hz,mul_zero] at hdiff
      change delta (assembled z F w) (Sum.inl u) (Sum.inl v) (context X Y)=0 at hz0
      linarith
    have hf0 := ht (Sum.inl u) (Sum.inl v)
      (fun he => huv (Sum.inl_injective he)) (context X Y)
      (by simpa using hu) (by simpa using hv) hz0
    have hf1 := ht (Sum.inl u) (Sum.inl v)
      (fun he => huv (Sum.inl_injective he)) (context X (insert j Y))
      (by simpa using hu) (by simpa using hv) hz1
    have hdiff := delta_assembled_insert_outer (boundarySlice f) (privateSlice f)
      (fun _ => 1) u v X Y j hj
    rw [←function_eq_private_assembly hout,hf0,hf1,sub_self,one_mul] at hdiff
    exact hdiff.symm

theorem assembled_tight_kernel_general {z : SetFunction H} (hz : TranslationNormalized z)
    {F : J → SetFunction H} {w : J → ℝ} (hc : Compatible z F w)
    (hF : ∀ j,PrivateRigid (F j)) (hrel : UniqueIntegrableRelation F w)
    (f : SetFunction (H⊕J)) (hf : TranslationNormalized f)
    (ht : ∀ u v,u≠ v → ∀ A,u∉A → v∉A →
      delta (assembled z F w) u v A=0 → delta f u v A=0) :
    ∃ c : ℝ,f=c • assembled z F w := by
  have houter : OuterZero f := by
    intro i j hij A hi hj
    exact ht (Sum.inr i) (Sum.inr j) (fun he => hij (Sum.inr_injective he)) A hi hj
      (delta_assembled_outer z F w i j hij A hi hj)
  choose t htparts using privateSlice_scalar_general hc hF hf ht
  have hrep:=eq_assembled_of_privateSlices houter F t htparts
  have ht' : Compatible (boundarySlice f) F t :=
    compatible_of_tight_variation_general hc (by
      intro u v huv A hu hv hzero
      rw [← hrep]
      exact ht u v huv A hu hv hzero)
  obtain ⟨c,hct⟩:=hrel t ⟨boundarySlice f,boundarySlice_normalized hf,ht'⟩
  have hb:=compatible_central_unique hz (boundarySlice_normalized hf) hc ht' hct
  exact ⟨c,by rw [hrep,hb,hct,assembled_smul]⟩

theorem assembled_ne_zero_general (z : SetFunction H) (F : J → SetFunction H)
    (w : J → ℝ) (hne : ∃ j X,w j*F j X≠0) : assembled z F w≠0 := by
  obtain ⟨j,X,hj⟩:=hne
  intro he
  have hh:=privateSlice_assembled z F w j X
  rw [he] at hh
  exact hj (by simpa only [privateSlice,Pi.zero_apply,sub_self] using hh.symm)

theorem positive_circuit_extreme_general {z : SetFunction H} (hz : TranslationNormalized z)
    {F : J → SetFunction H} (hzero : ∀ j,F j ∅=0)
    (hmono : ∀ j a X,0≤ F j (insert a X)-F j X)
    (hrigid : ∀ j,PrivateRigid (F j))
    {w : J → ℝ} (hw : ∀ j,0≤ w j) (hne : ∃ j X,w j*F j X≠0)
    (hc : Compatible z F w) (hrel : UniqueIntegrableRelation F w) :
    ExtremeSupermodular (assembled z F w) := by
  apply extremeSupermodular_of_tightEquations
    (assembled_normalized_general hz F hzero w)
    (assembled_supermodular_general z F hmono w hw hc)
    (assembled_ne_zero_general z F w hne)
  exact assembled_tight_kernel_general hz hc hrigid hrel

theorem IsMonotoneBoolean.privateRigid {F : SetFunction H} (hF : IsMonotoneBoolean F) :
    PrivateRigid F := by
  intro f hf hcover hdelta
  exact ⟨f univ,zero_cover_kernel_line hF ⟨hf,hcover⟩⟩

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart203

section BundlePart204
/- Source: Papers/GraphicalZonotopes/TwoHubFunctions.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise
variable {H J : Type*} [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]

theorem assembled_context (z : SetFunction H) (F : J → SetFunction H)
    (w : J → ℝ) (X : Finset H) (Y : Finset J) :
    assembled z F w (context X Y)=z X+∑ j∈Y,w j*F j X := by
  simp only [assembled,Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
    boundaryLift,hubs_context,branchLift,mem_context_outer]
  simp only [mul_ite,mul_zero]
  rw [← sum_filter]
  have hY : (univ.filter (fun j => j∈Y))=Y := by ext j; simp
  rw [hY]

theorem privateSlice_context (z : SetFunction H) (F : J → SetFunction H)
    (w : J → ℝ) (X : Finset H) (Y : Finset J) (j : J) (hj : j∉Y) :
    assembled z F w (context X (insert j Y))-assembled z F w (context X Y)=
      w j*F j X := by
  rw [assembled_context,assembled_context,sum_insert hj]
  ring

end BooleanModule

namespace TwoHub
open Finset BooleanModule
open scoped BigOperators Pointwise
variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev Hub (I : Type*) := Bool⊕I
def a : Hub I := .inl false
def b : Hub I := .inl true
def u (i : I) : Hub I := .inr i

/-- The four corner values are (1,1,0,1) when e=false and (0,1,1,1)
when e=true, in the order 00,10,01,11. -/
def corner (e : Bool) : SetFunction Bool := fun S =>
  if false∈S then 1 else if true∈S then (if e then 1 else 0) else (if e then 0 else 1)

def pair (A B C : ℝ) : SetFunction Bool := fun S =>
  (if false∈S then A else 0)+(if true∈S then B else 0)+
    (if false∈S ∧ true∈S then C else 0)

@[simp] theorem pair_empty (A B C : ℝ) : pair A B C ∅=0 := by simp [pair]
@[simp] theorem pair_false (A B C : ℝ) : pair A B C {false}=A := by simp [pair]
@[simp] theorem pair_true (A B C : ℝ) : pair A B C {true}=B := by simp [pair]
@[simp] theorem pair_full (A B C : ℝ) : pair A B C univ=A+B+C := by simp [pair]

theorem bool_set_ext {f g : SetFunction Bool}
    (h0 : f ∅=g ∅) (ha : f {false}=g {false}) (hb : f {true}=g {true})
    (h1 : f univ=g univ) : f=g := by
  funext X
  have hx : X∈(univ : Finset Bool).powerset := mem_powerset.mpr (subset_univ X)
  fin_cases hx <;> simpa using (by first | exact h0 | exact ha | exact hb | exact h1)

theorem eq_pair (f : SetFunction Bool) (h0 : f ∅=0) :
    f=pair (f {false}) (f {true}) (f univ-f {false}-f {true}) := by
  apply bool_set_ext
  · simp [h0]
  · simp
  · simp
  · simp only [pair_full]
    ring

@[simp] theorem corner_empty (e : Bool) : corner e ∅=if e then 0 else 1 := by simp [corner]
@[simp] theorem corner_false (e : Bool) : corner e {false}=1 := by simp [corner]
@[simp] theorem corner_true (e : Bool) : corner e {true}=if e then 1 else 0 := by simp [corner]
@[simp] theorem corner_full (e : Bool) : corner e univ=1 := by simp [corner]

theorem corner_values (e : Bool) (X : Finset Bool) : corner e X=0 ∨ corner e X=1 := by
  unfold corner
  split_ifs <;> simp

theorem corner_nonneg (e : Bool) (X : Finset Bool) : 0≤ corner e X := by
  rcases corner_values e X with h | h <;> rw [h] <;> norm_num

theorem corner_private_line (e : Bool) (f : SetFunction Bool)
    (hzero : f (if e then ∅ else {true})=0)
    (ha : f (if e then univ else {false})=f (if e then {true} else ∅))
    (hb : f univ=f {false}) : ∃ c : ℝ,f=c • corner e := by
  cases e with
  | false =>
    refine ⟨f ∅,?_⟩
    apply bool_set_ext <;> simp only [Pi.smul_apply,smul_eq_mul,corner_empty,
      corner_false,corner_true,corner_full,Bool.false_eq_true,ite_false,mul_zero,mul_one]
    · exact ha
    · exact hzero
    · exact hb.trans ha
  | true =>
    refine ⟨f {true},?_⟩
    apply bool_set_ext <;> simp only [Pi.smul_apply,smul_eq_mul,corner_empty,
      corner_false,corner_true,corner_full,ite_true,mul_zero,mul_one]
    · exact hzero
    · exact hb.symm.trans ha
    · exact ha

def eta (ε : Finset I) : ℝ := if ε=∅ then 1 else 0

def central (ε : Finset I) : SetFunction Bool :=
  pair (eta ε) ((Fintype.card I : ℝ)-(ε.card : ℝ)) ((ε.card : ℝ)-1)

def moduleFunction (ε : Finset I) : SetFunction (Hub I) :=
  assembled (central ε) (fun i => corner (decide (i∈ε))) (fun _ => 1)

@[simp] theorem module_empty (ε : Finset I) : moduleFunction ε ∅=0 := by
  simp [moduleFunction,assembled,boundaryLift,branchLift,central]

theorem module_context (ε : Finset I) (X : Finset Bool) (Y : Finset I) :
    moduleFunction ε (context X Y)=central ε X+∑ i∈Y,corner (decide (i∈ε)) X := by
  simp only [moduleFunction,assembled_context,one_mul]

theorem module_outer_zero (ε : Finset I) : OuterZero (moduleFunction ε) := by
  intro i j hij X hi hj
  exact delta_assembled_outer _ _ _ i j hij X hi hj

theorem module_spoke (ε : Finset I) (i : I) (X : Finset Bool) :
    moduleFunction ε (insert (u i) (hubSet X))-moduleFunction ε (hubSet X)=
      corner (decide (i∈ε)) X := by
  simpa only [moduleFunction,u,one_mul,privateSlice] using
    privateSlice_assembled (central ε) (fun i => corner (decide (i∈ε))) (fun _ => 1) i X

theorem module_hub_spoke (ε : Finset I) (i : I) (v : Bool) (X : Finset Bool) :
    delta (moduleFunction ε) (Sum.inl v) (u i) (hubSet X)=
      corner (decide (i∈ε)) (insert v X)-corner (decide (i∈ε)) X := by
  simp only [moduleFunction,u,delta_assembled_spoke _ _ _ _ _ _ (notMem_hubSet_outer X i),
    hubs_hubSet,one_mul]

theorem delta_pair (A B C : ℝ) : delta (pair A B C) false true ∅=C := by
  simp [delta,pair]
  ring

theorem delta_corner (e : Bool) : delta (corner e) false true ∅=if e then -1 else 1 := by
  cases e <;> norm_num [delta,corner]

theorem module_ab (ε Y : Finset I) :
    delta (moduleFunction ε) a b (outerSet Y)=
      ((ε.card : ℝ)-1)+∑ i∈Y,if i∈ε then (-1 : ℝ) else 1 := by
  change delta (assembled (central ε) _ _) (.inl false) (.inl true) (outerSet Y)=_
  rw [delta_assembled_hubs]
  have hh : hubs (outerSet (H:=Bool) Y)=∅ := by ext v; simp
  rw [hh]
  simp only [central,delta_pair,one_mul,mem_outerSet_outer,delta_corner,ite_mul]
  simp only [Bool.decide_iff]
  rw [← sum_filter]
  have hY : (univ.filter (fun i => i∈Y))=Y := by ext i; simp
  rw [hY]

def neighbor (ε : Finset I) (i : I) : Finset I :=
  if i∈ε then ε.erase i else insert i ε

theorem signed_sum_epsilon (ε : Finset I) (γ : I → ℝ) :
    (∑ i∈ε,if i∈ε then -γ i else γ i)= -∑ i∈ε,γ i := by
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro i hi
  rw [if_pos hi]

theorem signed_sum_neighbor (ε : Finset I) (γ : I → ℝ) (j : I) :
    (∑ i∈neighbor ε j,if i∈ε then -γ i else γ i)= -(∑ i∈ε,γ i)+γ j := by
  unfold neighbor
  by_cases hj : j∈ε
  · rw [if_pos hj]
    have he := sum_erase_add (s:=ε) (f:=fun i => if i∈ε then -γ i else γ i) hj
    rw [signed_sum_epsilon,if_pos hj] at he
    linarith
  · rw [if_neg hj,sum_insert hj,if_neg hj,signed_sum_epsilon]
    ring

theorem module_ab_neighbor (ε : Finset I) (j : I) :
    delta (moduleFunction ε) a b (outerSet (neighbor ε j))=0 := by
  rw [module_ab]
  have hs:=signed_sum_neighbor ε (fun _ => (1 : ℝ)) j
  rw [hs]
  simp

end TwoHub
end GraphicalZonotopes

end
end
end BundlePart204

section BundlePart205
/- Source: Papers/GraphicalZonotopes/TwoHubPrivate.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H J : Type*} [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]

theorem assembled_hub_cover (z : SetFunction H) (F : J → SetFunction H)
    (w : J → ℝ) (v : H) (X : Finset H) (Y : Finset J) :
    assembled z F w (context (insert v X) Y)-assembled z F w (context X Y)=
      z (insert v X)-z X+∑ j∈Y,w j*(F j (insert v X)-F j X) := by
  rw [assembled_context,assembled_context]
  simp only [mul_sub,Finset.sum_sub_distrib]
  ring

theorem context_insert_hub (X : Finset H) (Y : Finset J) (v : H) :
    context (insert v X) Y=insert (Sum.inl v) (context X Y) := by
  ext x
  cases x <;> simp

end BooleanModule

namespace TwoHub
open Finset BooleanModule
open scoped BigOperators Pointwise
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem module_a_zero_cover (ε Y : Finset I) :
    moduleFunction ε (context {false} Y)-moduleFunction ε (context ∅ Y)=
      eta ε+∑ i∈Y,if i∈ε then (1 : ℝ) else 0 := by
  have hh := assembled_hub_cover (central ε) (fun i => corner (decide (i∈ε)))
    (fun _ => 1) false ∅ Y
  simp only [insert_empty_eq] at hh
  simp only [moduleFunction]
  rw [hh]
  simp only [central,pair_false,pair_empty,sub_zero,corner_false,corner_empty,one_mul]
  congr 1
  apply sum_congr rfl
  intro i hi
  by_cases he : i∈ε <;> simp [he]

theorem module_a_one_cover (ε Y : Finset I) :
    moduleFunction ε (context univ Y)-moduleFunction ε (context {true} Y)=
      eta ε+(ε.card : ℝ)-1+∑ i∈Y,if i∈ε then (0 : ℝ) else 1 := by
  have hb : insert false ({true} : Finset Bool)=univ := by decide
  have hh := assembled_hub_cover (central ε) (fun i => corner (decide (i∈ε)))
      (fun _ => 1) false {true} Y
  rw [hb] at hh
  simp only [moduleFunction]
  rw [hh]
  simp only [central,pair_full,pair_true,corner_full,corner_true,one_mul]
  have hs : (∑ i∈Y,(1-(if decide (i∈ε) then (1 : ℝ) else 0)))=
      ∑ i∈Y,if i∈ε then (0 : ℝ) else 1 := by
    apply sum_congr rfl
    intro i hi
    by_cases he : i∈ε <;> simp [he]
  rw [hs]
  ring

theorem module_b_zero_cover (ε Y : Finset I) :
    moduleFunction ε (context {true} Y)-moduleFunction ε (context ∅ Y)=
      (Fintype.card I : ℝ)-(ε.card : ℝ)+∑ i∈Y,if i∈ε then (1 : ℝ) else -1 := by
  have hh := assembled_hub_cover (central ε) (fun i => corner (decide (i∈ε)))
      (fun _ => 1) true ∅ Y
  simp only [insert_empty_eq] at hh
  simp only [moduleFunction]
  rw [hh]
  simp only [central,pair_true,pair_empty,sub_zero,corner_true,corner_empty,one_mul]
  congr 1
  apply sum_congr rfl
  intro i hi
  by_cases he : i∈ε <;> simp [he]

theorem module_b_one_cover (ε Y : Finset I) :
    moduleFunction ε (context univ Y)-moduleFunction ε (context {false} Y)=
      (Fintype.card I : ℝ)-1 := by
  have hb : insert true ({false} : Finset Bool)=univ := by decide
  have hh := assembled_hub_cover (central ε) (fun i => corner (decide (i∈ε)))
      (fun _ => 1) true {false} Y
  rw [hb] at hh
  simp only [moduleFunction]
  rw [hh]
  simp only [central,pair_full,pair_false,corner_full,corner_false,sub_self,mul_zero,sum_const_zero,add_zero]
  ring

theorem module_b_complement_zero (ε : Finset I) :
    moduleFunction ε (context {true} (univ\ε))-
      moduleFunction ε (context ∅ (univ\ε))=0 := by
  rw [module_b_zero_cover]
  have hs : (∑ i∈univ\ε,if i∈ε then (1 : ℝ) else -1)=
      -(Fintype.card I : ℝ)+(ε.card : ℝ) := by
    calc
      _ = ∑ _i∈univ\ε,(-1 : ℝ) := by
        apply sum_congr rfl
        intro i hi
        rw [if_neg (mem_sdiff.mp hi).2]
      _ = -((Fintype.card I-ε.card : ℕ) : ℝ) := by
        simp [card_sdiff_of_subset (subset_univ ε)]
      _ = _ := by rw [Nat.cast_sub (card_le_univ ε)]; ring
  rw [hs]
  ring

theorem private_corner_of_tight (ε : Finset I) (f : SetFunction (Hub I))
    (hcover : ∀ v X,v∉X → moduleFunction ε (insert v X)-moduleFunction ε X=0 →
      f (insert v X)-f X=0)
    (hdelta : ∀ v w,v≠ w → ∀ X,v∉X → w∉X →
      delta (moduleFunction ε) v w X=0 → delta f v w X=0)
    (i : I) : ∃ c : ℝ,privateSlice f i=c • corner (decide (i∈ε)) := by
  apply corner_private_line
  · have hh:=hcover (u i) (hubSet (if decide (i∈ε) then ∅ else {true}))
      (notMem_hubSet_outer _ i)
    have hz : moduleFunction ε (insert (u i) (hubSet (if decide (i∈ε) then ∅ else {true})))-
        moduleFunction ε (hubSet (if decide (i∈ε) then ∅ else {true}))=0 := by
      rw [module_spoke]
      by_cases hi : i∈ε <;> simp [hi,corner]
    exact hh hz
  · have hh := hdelta a (u i) (by simp [a,u])
      (hubSet (if decide (i∈ε) then {true} else ∅))
      (by by_cases hi : i∈ε <;> simp [a,hi])
      (notMem_hubSet_outer _ i)
    have hz : delta (moduleFunction ε) a (u i)
        (hubSet (if decide (i∈ε) then {true} else ∅))=0 := by
      rw [a,module_hub_spoke]
      by_cases hi : i∈ε <;> simp [hi,corner]
    have h:=hh hz
    rw [a,u,← privateSlice_cover] at h
    by_cases hi : i∈ε
    · have hu : insert false ({true} : Finset Bool)=univ := by decide
      simpa [hi,hu] using sub_eq_zero.mp h
    · simpa [hi] using sub_eq_zero.mp h
  · have hh := hdelta b (u i) (by simp [b,u]) (hubSet {false})
      (by simp [b]) (notMem_hubSet_outer _ i)
    have hz : delta (moduleFunction ε) b (u i) (hubSet {false})=0 := by
      rw [b,module_hub_spoke]
      simp [corner]
    have h:=hh hz
    rw [b,u,← privateSlice_cover] at h
    have hu : insert true ({false} : Finset Bool)=univ := by decide
    rw [hu] at h
    exact sub_eq_zero.mp h

theorem delta_weighted_corners (h : SetFunction Bool) (ε Y : Finset I) (γ : I → ℝ) :
    delta (assembled h (fun i => corner (decide (i∈ε))) γ) a b (outerSet Y)=
      delta h false true ∅+∑ i∈Y,if i∈ε then -γ i else γ i := by
  rw [a,b,delta_assembled_hubs]
  have hh : hubs (outerSet (H:=Bool) Y)=∅ := by ext v; simp
  rw [hh]
  simp only [mem_outerSet_outer,delta_corner]
  have hs : (∑ i : I,γ i*(if i∈Y then (if decide (i∈ε) then (-1 : ℝ) else 1) else 0))=
      ∑ i∈Y,if i∈ε then -γ i else γ i := by
    simp only [mul_ite,mul_zero,mul_neg,mul_one]
    rw [←sum_filter]
    have hY : (univ.filter (fun i => i∈Y))=Y := by ext i; simp
    rw [hY]
    apply sum_congr rfl
    intro i hi
    simp
  rw [hs]

theorem module_private_rigid [Nonempty I] (ε : Finset I) : PrivateRigid (moduleFunction ε) := by
  intro f hf hcover hdelta
  have hout : OuterZero f := by
    intro i j hij X hi hj
    exact hdelta (Sum.inr i) (Sum.inr j) (by simpa using hij) X hi hj
      (module_outer_zero ε i j hij X hi hj)
  choose γ hγ using private_corner_of_tight ε f hcover hdelta
  have hrep := eq_assembled_of_privateSlices hout
    (fun i => corner (decide (i∈ε))) γ hγ
  let h:=boundarySlice f
  have hh0 : h ∅=0 := by simpa [h,boundarySlice] using hf
  have hscale (j : I) : delta h false true ∅-(∑ i∈ε,γ i)+γ j=0 := by
    have hz := hdelta a b (by simp [a,b]) (outerSet (neighbor ε j))
      (by simp [a]) (by simp [b]) (module_ab_neighbor ε j)
    rw [hrep,delta_weighted_corners,signed_sum_neighbor] at hz
    dsimp [h]
    linarith
  let j₀ : I:=Classical.choice ‹Nonempty I›
  let c:=γ j₀
  have hγc (j : I) : γ j=c := by
    have h1:=hscale j
    have h2:=hscale j₀
    dsimp [c]
    linarith
  have hC : delta h false true ∅=((ε.card : ℝ)-1)*c := by
    have he:=hscale j₀
    simp_rw [hγc] at he
    simp only [sum_const,nsmul_eq_mul] at he
    linarith
  have hB : h {true}=((Fintype.card I : ℝ)-(ε.card : ℝ))*c := by
    have hz := hcover b (context ∅ (univ\ε)) (by simp [b]) (by
      rw [b,←context_insert_hub,insert_empty_eq]
      exact module_b_complement_zero ε)
    rw [hrep,b,←context_insert_hub,assembled_hub_cover] at hz
    have hS : (∑ i∈univ\ε,γ i*(corner (decide (i∈ε)) (insert true ∅)-
        corner (decide (i∈ε)) ∅))= -((Fintype.card I : ℝ)-(ε.card : ℝ))*c := by
      calc
        _ = ∑ _i∈univ\ε,-c := by
          apply sum_congr rfl
          intro i hi
          simp [(mem_sdiff.mp hi).2,hγc i,corner]
        _ = _ := by
          simp [card_sdiff_of_subset (subset_univ ε),Nat.cast_sub (card_le_univ ε)] <;> ring
    rw [hS] at hz
    change h {true}-h ∅+ -((Fintype.card I : ℝ)-(ε.card : ℝ))*c=0 at hz
    rw [hh0] at hz
    linarith
  have hA : h {false}=eta ε*c := by
    by_cases he : ε=∅
    · have hz := hcover a (context {true} (∅ : Finset I)) (by simp [a]) (by
        rw [a,←context_insert_hub]
        have hu : insert false ({true} : Finset Bool)=univ := by decide
        rw [hu,module_a_one_cover]
        simp [he,eta])
      rw [hrep,a,←context_insert_hub,assembled_hub_cover] at hz
      have hu : insert false ({true} : Finset Bool)=univ := by decide
      simp only [hu,sum_empty,add_zero] at hz
      change h univ-h {true}=0 at hz
      have hCab : delta h false true ∅=h univ-h {false}-h {true}+h ∅ := by
        simp only [delta,insert_empty_eq,hu]
      rw [hCab,hh0,he,card_empty,Nat.cast_zero] at hC
      simp only [eta,he,ite_true,one_mul]
      linarith
    · have hz := hcover a (context ∅ (∅ : Finset I)) (by simp [a]) (by
        rw [a,←context_insert_hub]
        simpa [eta,he] using module_a_zero_cover ε (∅ : Finset I))
      rw [hrep,a,←context_insert_hub,assembled_hub_cover] at hz
      change h {false}-h ∅+0=0 at hz
      rw [hh0] at hz
      simp only [eta,if_neg he,zero_mul]
      linarith
  have hcentral : h=c • central ε := by
    rw [eq_pair h hh0]
    apply bool_set_ext
    · simp [central]
    · simp [central,hA,mul_comm]
    · simp [central,hB,mul_comm]
    · have hCab : delta h false true ∅=h univ-h {false}-h {true}+h ∅ := by
        have hu : insert false ({true} : Finset Bool)=univ := by decide
        simp only [delta,insert_empty_eq,hu]
      rw [hCab,hh0] at hC
      simp only [pair_full,Pi.smul_apply,smul_eq_mul,central]
      nlinarith [hA,hB]
  refine ⟨c,?_⟩
  rw [hrep]
  change assembled h _ γ=c • moduleFunction ε
  have hg : γ=c • (fun _ : I => (1 : ℝ)) := by
    funext i
    simp [hγc i]
  rw [hcentral,hg,assembled_smul]
  rfl

end TwoHub
end GraphicalZonotopes

end
end
end BundlePart205

section BundlePart206
/- Source: Papers/GraphicalZonotopes/TwoHubResponses.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace TwoHub
open Finset BooleanModule
open scoped BigOperators Pointwise
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem bool_set_without_false {X : Finset Bool} (h : false∉X) :
    X=∅ ∨ X={true} := by
  by_cases ht : true∈X
  · right
    ext v
    cases v <;> simp [h,ht]
  · left
    ext v
    cases v <;> simp [h,ht]

theorem bool_set_without_true {X : Finset Bool} (h : true∉X) :
    X=∅ ∨ X={false} := by
  by_cases ht : false∈X
  · right
    ext v
    cases v <;> simp [h,ht]
  · left
    ext v
    cases v <;> simp [h,ht]

theorem signed_sum_card (ε Y : Finset I) :
    (∑ i∈Y,if i∈ε then (-1 : ℝ) else 1)=
      ((Y\ε).card : ℝ)-((Y∩ε).card : ℝ) := by
  have hp : Y.filter (fun i => i∈ε)=Y∩ε := by ext i; simp
  have hn : Y.filter (fun i => i∉ε)=Y\ε := by ext i; simp
  rw [sum_ite,hp,hn]
  simp
  <;> ring

theorem reverse_signed_sum_card (ε Y : Finset I) :
    (∑ i∈Y,if i∈ε then (1 : ℝ) else -1)=
      ((Y∩ε).card : ℝ)-((Y\ε).card : ℝ) := by
  have hp : Y.filter (fun i => i∈ε)=Y∩ε := by ext i; simp
  have hn : Y.filter (fun i => i∉ε)=Y\ε := by ext i; simp
  rw [sum_ite,hp,hn]
  simp
  <;> ring

@[simp] theorem eta_nonneg (ε : Finset I) : 0≤ eta ε := by
  unfold eta
  split_ifs <;> norm_num

theorem eta_card_sub_one_nonneg (ε : Finset I) : 0≤ eta ε+(ε.card : ℝ)-1 := by
  by_cases h : ε=∅
  · simp [h,eta]
  · have hc : 1≤ ε.card := card_pos.mpr (nonempty_iff_ne_empty.mpr h)
    have hc' : (1 : ℝ)≤(ε.card : ℝ) := by exact_mod_cast hc
    simp only [eta,if_neg h,zero_add]
    linarith

/-- Nonnegative first differences of the integer-valued module (8.1),
including the endpoint p=1 and all conditioning sets. -/
theorem module_cover_nonnegative [Nonempty I] (ε : Finset I) (v : Hub I)
    (S : Finset (Hub I)) :
    0 ≤ moduleFunction ε (insert v S)-moduleFunction ε S := by
  by_cases hv : v∈S
  · simp [insert_eq_of_mem hv]
  let X:=hubs S
  let Y:=outers S
  have hS : context X Y=S := context_parts S
  rw [←hS] at hv ⊢
  cases v with
  | inr i =>
    have hi : i∉Y := by simpa using hv
    rw [moduleFunction,←context_insert,privateSlice_context _ _ _ _ _ _ hi,one_mul]
    exact corner_nonneg _ _
  | inl v =>
    have hX : v∉X := by simpa using hv
    rw [←context_insert_hub]
    cases v with
    | false =>
      rcases bool_set_without_false hX with hX0 | hX1
      · rw [hX0,insert_empty_eq,module_a_zero_cover]
        exact add_nonneg (eta_nonneg ε) (sum_nonneg (by intro i hi; split_ifs <;> norm_num))
      · have hb : insert false ({true} : Finset Bool)=univ := by decide
        rw [hX1,hb,module_a_one_cover]
        exact add_nonneg (eta_card_sub_one_nonneg ε)
          (sum_nonneg (by intro i hi; split_ifs <;> norm_num))
    | true =>
      rcases bool_set_without_true hX with hX0 | hX1
      · rw [hX0,insert_empty_eq,module_b_zero_cover,reverse_signed_sum_card]
        have hsub : Y\ε ⊆ univ\ε := sdiff_subset_sdiff (subset_univ Y) Subset.rfl
        have hc := card_le_card hsub
        have hc' : ((Y\ε).card : ℝ)≤(Fintype.card I : ℝ)-(ε.card : ℝ) := by
          have hh : ((Y\ε).card : ℝ)≤((univ\ε).card : ℝ) := by exact_mod_cast hc
          simpa only [card_sdiff_of_subset (subset_univ ε),card_univ,Nat.cast_sub (card_le_univ ε)] using hh
        linarith [(Nat.cast_nonneg ((Y∩ε).card) : (0 : ℝ)≤((Y∩ε).card : ℝ))]
      · have hb : insert true ({false} : Finset Bool)=univ := by decide
        rw [hX1,hb,module_b_one_cover]
        have hp : (1 : ℝ)≤(Fintype.card I : ℝ) := by
          exact_mod_cast (Fintype.card_pos : 0< Fintype.card I)
        linarith

def distance (ε Y : Finset I) : ℕ := (ε\Y).card+(Y\ε).card

theorem distance_zero_iff (ε Y : Finset I) : distance ε Y=0 ↔ ε=Y := by
  simp only [distance,Nat.add_eq_zero,card_eq_zero,sdiff_eq_empty_iff_subset]
  exact ⟨fun h => Subset.antisymm h.1 h.2,fun h => by simp [h]⟩

theorem module_ab_distance (ε Y : Finset I) :
    delta (moduleFunction ε) a b (outerSet Y)=(distance ε Y : ℝ)-1 := by
  rw [module_ab,signed_sum_card]
  have hc : ((ε\Y).card : ℝ)+((Y∩ε).card : ℝ)=(ε.card : ℝ) := by
    exact_mod_cast (by simpa only [inter_comm] using card_sdiff_add_card_inter ε Y)
  simp only [distance,Nat.cast_add]
  linarith

theorem module_ab_negativeResponse (ε Y : Finset I) :
    negativeResponse (moduleFunction ε) a b (outerSet Y)=if Y=ε then 1 else 0 := by
  rw [negativeResponse,module_ab_distance]
  by_cases he : Y=ε
  · subst Y
    simp [distance]
  · have hd : 1≤ distance ε Y := Nat.one_le_iff_ne_zero.mpr
      (fun hh => he ((distance_zero_iff ε Y).mp hh).symm)
    have hd' : (1 : ℝ)≤(distance ε Y : ℝ) := by exact_mod_cast hd
    rw [if_neg he,max_eq_left (by linarith)]

theorem module_ai_delta (ε : Finset I) (i : I) (S : Finset (Hub I))
    (ha : a∉S) (hi : u i∉S) :
    delta (moduleFunction ε) a (u i) S=
      if i∈ε then (if b∈S then 0 else 1) else (if b∈S then 1 else 0) := by
  have hx : false∉hubs S := by simpa [a] using ha
  simp only [moduleFunction,a,u,delta_assembled_spoke _ _ _ _ _ _ hi,one_mul]
  by_cases hb : b∈S <;> by_cases he : i∈ε <;>
    simp [corner,hx,he,show (true∈hubs S ↔ b∈S) from by simp [b],hb]

theorem module_bi_delta (ε : Finset I) (i : I) (S : Finset (Hub I))
    (hb : b∉S) (hi : u i∉S) :
    delta (moduleFunction ε) b (u i) S=
      if a∈S then 0 else (if i∈ε then 1 else -1) := by
  have hx : true∉hubs S := by simpa [b] using hb
  simp only [moduleFunction,b,u,delta_assembled_spoke _ _ _ _ _ _ hi,one_mul]
  by_cases ha : a∈S <;> by_cases he : i∈ε <;>
    simp [corner,hx,he,show (false∈hubs S ↔ a∈S) from by simp [a],ha]

theorem module_ai_response (ε : Finset I) (i : I) (S : Finset (Hub I))
    (ha : a∉S) (hi : u i∉S) : negativeResponse (moduleFunction ε) a (u i) S=0 := by
  rw [negativeResponse,module_ai_delta ε i S ha hi]
  split_ifs <;> norm_num

theorem module_bi_response (ε : Finset I) (i : I) (S : Finset (Hub I))
    (hb : b∉S) (hi : u i∉S) :
    negativeResponse (moduleFunction ε) b (u i) S=
      if i∈ε then 0 else (if a∈S then 0 else 1) := by
  rw [negativeResponse,module_bi_delta ε i S hb hi]
  split_ifs <;> norm_num

/-- The balancing Boolean module r_i = a(b ∨ u_i). -/
def balancing (i : I) : SetFunction (Hub I) :=
  fun S => if a∈S ∧ (b∈S ∨ u i∈S) then 1 else 0

theorem balancing_boolean (i : I) : IsMonotoneBoolean (balancing i) where
  monotone := by
    intro X Y hXY
    unfold balancing
    split_ifs with hX hY hY
    · exact le_refl _
    · exact False.elim (hY ⟨hXY hX.1,hX.2.imp (fun h => hXY h) (fun h => hXY h)⟩)
    · norm_num
    · norm_num
  values := by intro X; unfold balancing; split_ifs <;> simp
  empty := by simp [balancing]
  full := by simp [balancing]

theorem balancing_ab_delta (i : I) (S : Finset (Hub I))
    (ha : a∉S) (hb : b∉S) :
    delta (balancing i) a b S=if u i∈S then 0 else 1 := by
  by_cases hi : u i∈S <;> simp_all [delta,balancing,a,b,u] <;> ring

theorem balancing_ai_delta (i j : I) (S : Finset (Hub I))
    (ha : a∉S) (hj : u j∉S) :
    delta (balancing i) a (u j) S=if i=j then (if b∈S then 0 else 1) else 0 := by
  by_cases he : i=j
  · subst j
    by_cases hb : b∈S <;> simp_all [delta,balancing,a,b,u] <;> ring
  · by_cases hb : b∈S <;> by_cases hi : u i∈S <;>
      simp_all [delta,balancing,a,b,u,Ne.symm he] <;> ring

theorem balancing_bi_delta (i j : I) (S : Finset (Hub I))
    (hb : b∉S) (hj : u j∉S) :
    delta (balancing i) b (u j) S=if i=j then (if a∈S then -1 else 0) else 0 := by
  by_cases he : i=j
  · subst j
    by_cases ha : a∈S <;> simp_all [delta,balancing,a,b,u] <;> ring
  · by_cases ha : a∈S <;> by_cases hi : u i∈S <;>
      simp_all [delta,balancing,a,b,u,Ne.symm he] <;> ring

theorem balancing_outer_zero (i : I) : OuterZero (balancing i) := by
  intro j k hjk S hj hk
  by_cases hij : i=j <;> by_cases hik : i=k <;>
    by_cases ha : a∈S <;> by_cases hb : b∈S <;> by_cases hi : u i∈S <;>
    simp_all [delta,balancing,a,b,u]

end TwoHub
end GraphicalZonotopes

end
end
end BundlePart206

section BundlePart207
/- Source: Papers/GraphicalZonotopes/TwoHubCircuit.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace TwoHub
open Finset BooleanModule
open scoped BigOperators Pointwise
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The response identity is independent of the ordering of the three
variables. It is the discrete equality of mixed third derivatives. -/
theorem delta_insert_difference (f : SetFunction (Hub I)) (x y z : Hub I)
    (S : Finset (Hub I)) :
    delta f x y (insert z S)-delta f x y S=
      delta f x z (insert y S)-delta f x z S := by
  simp only [delta]
  simp only [insert_comm y z]
  ring

theorem outer_context_of_hubs_absent (S : Finset (Hub I)) (ha : a∉S) (hb : b∉S) :
    S=outerSet (outers S) := by
  have hX : hubs S=∅ := by
    ext v
    cases v <;> simp_all [a,b]
  have h:=context_parts S
  rw [hX] at h
  simpa [context] using h.symm

theorem module_ab_response_all (ε : Finset I) (S : Finset (Hub I))
    (ha : a∉S) (hb : b∉S) :
    negativeResponse (moduleFunction ε) a b S=if outers S=ε then 1 else 0 := by
  conv_lhs => rw [outer_context_of_hubs_absent S ha hb]
  exact module_ab_negativeResponse ε (outers S)

theorem balancing_ab_response (i : I) (S : Finset (Hub I))
    (ha : a∉S) (hb : b∉S) : negativeResponse (balancing i) a b S=0 := by
  rw [negativeResponse,balancing_ab_delta i S ha hb]
  split_ifs <;> norm_num

theorem balancing_ai_response (i j : I) (S : Finset (Hub I))
    (ha : a∉S) (hj : u j∉S) : negativeResponse (balancing i) a (u j) S=0 := by
  rw [negativeResponse,balancing_ai_delta i j S ha hj]
  split_ifs <;> norm_num

theorem balancing_bi_response (i j : I) (S : Finset (Hub I))
    (hb : b∉S) (hj : u j∉S) :
    negativeResponse (balancing i) b (u j) S=if i=j then (if a∈S then 1 else 0) else 0 := by
  rw [negativeResponse,balancing_bi_delta i j S hb hj]
  split_ifs <;> norm_num

abbrev Index (I : Type*) := Finset I⊕I

def family : Index I → SetFunction (Hub I)
  | .inl ε => moduleFunction ε
  | .inr i => balancing i

def missCount (i : I) : ℕ := (univ.filter (fun ε : Finset I => i∉ε)).card

theorem missCount_eq (i : I) : missCount i=2^(Fintype.card I-1) := by
  have he : (univ.filter (fun ε : Finset I => i∉ε))=(univ.erase i).powerset := by
    ext ε
    simp only [mem_filter,mem_univ,true_and,mem_powerset,subset_erase,subset_univ,and_true]
  rw [missCount,he,card_powerset,card_erase_of_mem (mem_univ i),card_univ]

theorem missCount_pos (i : I) : 0 < missCount i := by
  rw [missCount_eq]
  positivity

def weights : Index I → ℝ
  | .inl _ => 1
  | .inr i => (missCount i : ℝ)

def boundaryCentral : SetFunction (Hub I) :=
  assembled (pair 0 0 1) (fun i X => if true∈X then (missCount i : ℝ) else 0) (fun _ => 1)

def construction : SetFunction (Hub I⊕Index I) := assembled boundaryCentral family weights

theorem weights_pos (j : Index I) : 0 < weights j := by
  cases j with
  | inl ε => norm_num [weights]
  | inr i => simpa [weights] using (Nat.cast_pos.mpr (missCount_pos i) : (0 : ℝ)<(missCount i : ℝ))

theorem family_empty (j : Index I) : family j ∅=0 := by
  cases j with
  | inl ε => exact module_empty ε
  | inr i => exact (balancing_boolean i).empty

theorem family_monotone [Nonempty I] (j : Index I) (v : Hub I) (S : Finset (Hub I)) :
    0≤ family j (insert v S)-family j S := by
  cases j with
  | inl ε => exact module_cover_nonnegative ε v S
  | inr i => exact sub_nonneg.mpr ((balancing_boolean i).monotone (subset_insert v S))

theorem family_privateRigid [Nonempty I] (j : Index I) : PrivateRigid (family j) := by
  cases j with
  | inl ε => exact module_private_rigid ε
  | inr i => exact (balancing_boolean i).privateRigid

theorem family_ai_response (j : Index I) (i : I) (S : Finset (Hub I))
    (ha : a∉S) (hi : u i∉S) : negativeResponse (family j) a (u i) S=0 := by
  cases j with
  | inl ε => exact module_ai_response ε i S ha hi
  | inr k => exact balancing_ai_response k i S ha hi

theorem response_sum_ab (t : Index I → ℝ) (S : Finset (Hub I))
    (ha : a∉S) (hb : b∉S) :
    (∑ j : Index I,t j*negativeResponse (family j) a b S)=t (.inl (outers S)) := by
  rw [Fintype.sum_sum_type]
  simp only [family,module_ab_response_all _ _ ha hb,balancing_ab_response _ _ ha hb,
    mul_zero,sum_const_zero,add_zero,mul_ite,mul_one]
  simp

theorem response_sum_ai (t : Index I → ℝ) (i : I) (S : Finset (Hub I))
    (ha : a∉S) (hi : u i∉S) :
    (∑ j : Index I,t j*negativeResponse (family j) a (u i) S)=0 := by
  simp only [family_ai_response _ _ _ ha hi,mul_zero,sum_const_zero]

theorem response_sum_bi (t : Index I → ℝ) (i : I) (S : Finset (Hub I))
    (hb : b∉S) (hi : u i∉S) :
    (∑ j : Index I,t j*negativeResponse (family j) b (u i) S)=
      if a∈S then t (.inr i) else ∑ ε : Finset I,if i∈ε then 0 else t (.inl ε) := by
  rw [Fintype.sum_sum_type]
  simp only [family,module_bi_response _ _ _ hb hi,balancing_bi_response _ _ _ hb hi]
  by_cases ha : a∈S
  · simp [ha]
  · simp [ha,mul_ite]

theorem family_outer_response (j : Index I) (i k : I) (hik : i≠ k)
    (S : Finset (Hub I)) (hi : u i∉S) (hk : u k∉S) :
    negativeResponse (family j) (u i) (u k) S=0 := by
  cases j with
  | inl ε =>
    rw [family,negativeResponse]
    change max 0 (-delta (moduleFunction ε) (.inr i) (.inr k) S)=0
    rw [module_outer_zero ε i k hik S hi hk,neg_zero,max_self]
  | inr v =>
    rw [family,negativeResponse]
    change max 0 (-delta (balancing v) (.inr i) (.inr k) S)=0
    rw [balancing_outer_zero v i k hik S hi hk,neg_zero,max_self]

theorem compatible_ai_zero {h : SetFunction (Hub I)} {t : Index I → ℝ}
    (hc : Compatible h family t) (i : I) (S : Finset (Hub I))
    (ha : a∉S) (hi : u i∉S) : delta h a (u i) S=0 := by
  rw [hc a (u i) (by simp [a,u]) S ha hi,response_sum_ai _ _ _ ha hi]

theorem compatible_ab_constant {h : SetFunction (Hub I)} {t : Index I → ℝ}
    (hc : Compatible h family t) (Y : Finset I) :
    delta h a b (outerSet Y)=delta h a b ∅ := by
  induction Y using Finset.induction_on with
  | empty => simp
  | @insert i Y hi ih =>
    rw [outerSet_insert]
    have hh:=delta_insert_difference h a b (u i) (outerSet Y)
    have hz0:=compatible_ai_zero hc i (outerSet Y) (by simp [a]) (by simpa [u] using hi)
    have hz1:=compatible_ai_zero hc i (insert b (outerSet Y))
      (by simp [a,b]) (by simpa [u,b] using hi)
    rw [hz0,hz1] at hh
    change delta h a b (insert (u i) (outerSet Y))=delta h a b ∅
    rw [←ih]
    linarith

/-- Exact one-dimensionality of the integrability relation space. The
central function is arbitrary; no coefficient ansatz is imposed. -/
theorem unique_relation : UniqueIntegrableRelation (family (I:=I)) weights := by
  intro t ht
  obtain ⟨h,hn,hc⟩:=ht
  let c:=delta h a b ∅
  have hm (ε : Finset I) : t (.inl ε)=c := by
    have he:=hc a b (by simp [a,b]) (outerSet ε) (by simp [a]) (by simp [b])
    rw [response_sum_ab _ _ (by simp [a]) (by simp [b])] at he
    have hε : outers (outerSet (H:=Bool) ε)=ε := by ext i; simp
    rw [hε] at he
    exact he.symm.trans (compatible_ab_constant hc ε)
  have hb (i : I) : t (.inr i)=(missCount i : ℝ)*c := by
    have hz0:=compatible_ai_zero hc i (∅ : Finset (Hub I)) (by simp) (by simp)
    have hz1:=compatible_ai_zero hc i {b} (by simp [a,b]) (by simp [b,u])
    have hd:=delta_insert_difference h (u i) b a ∅
    rw [delta_comm (u i) b,delta_comm (u i) b,delta_comm (u i) a,delta_comm (u i) a] at hd
    simp only [insert_empty_eq] at hd
    rw [hz0,hz1] at hd
    have h0:=hc b (u i) (by simp [b,u]) ∅ (by simp) (by simp)
    have h1:=hc b (u i) (by simp [b,u]) {a} (by simp [a,b]) (by simp [a,u])
    rw [response_sum_bi _ _ _ (by simp) (by simp)] at h0
    rw [response_sum_bi _ _ _ (by simp [a,b]) (by simp [a,u])] at h1
    simp only [notMem_empty,not_false_eq_true,if_false,mem_singleton,ite_true] at h0 h1
    have hs : (∑ ε : Finset I,if i∈ε then (0 : ℝ) else t (.inl ε))=(missCount i : ℝ)*c := by
      simp_rw [hm]
      have he : (∑ ε : Finset I,if i∈ε then (0 : ℝ) else c)=
          ∑ ε∈univ.filter (fun ε : Finset I => i∉ε),c := by
        rw [sum_filter]
        apply sum_congr rfl
        intro ε hε
        by_cases hi : i∈ε <;> simp [hi]
      rw [he]
      simp only [sum_const,nsmul_eq_mul,missCount]
    rw [hs] at h0
    linarith
  refine ⟨c,?_⟩
  funext j
  cases j with
  | inl ε => simpa [weights] using hm ε
  | inr i => simpa [weights,mul_comm] using hb i

end TwoHub
end GraphicalZonotopes

end
end
end BundlePart207

section BundlePart208
/- Source: Papers/GraphicalZonotopes/GraphIsomorphismDimension.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open SetFunctionEmbedding
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Adding unused coordinates and then edges cannot lower the maximum
indecomposable-summand dimension. Every input is an actual real polytope. -/
theorem maximumIndecomposableDimension_le_of_embedding (e : V ↪ W)
    {G : SimpleGraph V} {H : SimpleGraph W} (hGH : G.map e≤ H) :
    maximumIndecomposableDimension G≤ maximumIndecomposableDimension H := by
  unfold maximumIndecomposableDimension
  apply csSup_le'
  rintro d ⟨Q,hQ,hi,hw,hd⟩
  obtain ⟨z,hz,he,hzd⟩ := weak_summand_extreme_or_zero hQ hi hw
  rw [← hd,hzd]
  rcases he with he | he
  · rw [he,basePolytope_zero]
    have hs : vectorSpan ℝ ({0} : Set (V → ℝ))=(⊥ : Submodule ℝ (V → ℝ)) :=
      _root_.vectorSpan_singleton ℝ (0 : V → ℝ)
    rw [hs,_root_.finrank_bot]
    exact Nat.zero_le _
  · have hfe := extend_extreme e he
    have hsub : G≤ H.comap e := by
      intro u v huv
      exact hGH ((SimpleGraph.map_adj e G (e u) (e v)).mpr ⟨u,v,huv,rfl,rfl⟩)
    have hgg : Graphical H (extend e z.1) :=
      extend_graphical e (Graphical.mono_graph hsub z.2.2)
    have hgp : IsGeneralizedPermutahedron (basePolytope (extend e z.1)) :=
      ⟨extend e z.1,hfe.1.1,hfe.2.1,rfl⟩
    have hm := dimension_le_maximum hgp.finitePolytope hfe.minkowskiIndecomposable
      ((isWeakMinkowskiSummand_graphical_iff hfe.1.1 hfe.2.1).mpr hgg)
    rw [finrank_vectorSpan_extend e z.2.1] at hm
    exact hm

theorem graph_map_of_iso {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    G.map e.toEquiv.toEmbedding=H := by
  ext u v
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨x,y,hxy,rfl,rfl⟩
    exact e.map_adj_iff.mpr hxy
  · intro huv
    refine ⟨e.symm u,e.symm v,e.symm.map_adj_iff.mpr huv,?_,?_⟩ <;> simp

/-- The paper's dimension invariant is unchanged by an arbitrary graph
isomorphism, including a change of the finite coordinate type. -/
theorem maximumIndecomposableDimension_iso {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : maximumIndecomposableDimension G=maximumIndecomposableDimension H := by
  apply le_antisymm
  · exact maximumIndecomposableDimension_le_of_embedding e.toEquiv.toEmbedding
      (le_of_eq (graph_map_of_iso e))
  · exact maximumIndecomposableDimension_le_of_embedding e.symm.toEquiv.toEmbedding
      (le_of_eq (graph_map_of_iso e.symm))

end GraphicalZonotopes

end
end
end BundlePart208

section BundlePart209
/- Source: Papers/GraphicalZonotopes/TwoHubGraph.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace TwoHub
open Finset
open scoped BigOperators Pointwise
variable {I : Type*} [Fintype I] [DecidableEq I]

variable {J : Type*} [Fintype J] [DecidableEq J]

def color : (Bool⊕I)⊕J → Fin 4
  | .inl (.inl false) => 0
  | .inl (.inl true) => 1
  | .inl (.inr _) => 2
  | .inr _ => 3

def graph : SimpleGraph ((Bool⊕I)⊕J) where
  Adj x y := color x≠ color y
  symm := ⟨fun _ _ => Ne.symm⟩
  loopless := ⟨fun _ h => h rfl⟩

instance graphDecidable : DecidableRel (graph (I:=I) (J:=J)).Adj :=
  fun x y => inferInstanceAs (Decidable (color x≠ color y))


end TwoHub
end GraphicalZonotopes

end
end
end BundlePart209
