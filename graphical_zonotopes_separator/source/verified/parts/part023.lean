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

public import verified.parts.part022
import all verified.parts.part022

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section BundlePart331
/- Source: Papers/GraphicalZonotopes/CliqueDegreeObstruction.lean -/








@[expose] public section
namespace GraphicalZonotopes
namespace CliqueDegree

open Finset

/-- Every graph on six named vertices containing the two tetrahedra
`0123` and `0124` has exactly these six optional edges.  The parameter
records `34, 05, 15, 25, 35, 45`; all remaining non-loop edges are forced. -/
def sixGraph (b : Fin 6 → Bool) : SimpleGraph (Fin 6) where
  Adj i j := i ≠ j ∧
    (if i = 5 then b (j+1) = true
     else if j = 5 then b (i+1) = true
     else i.val < 3 ∨ j.val < 3 ∨ b 0 = true)
  symm := ⟨by
    intro i j
    by_cases hi : i = 5 <;> by_cases hj : j = 5 <;>
      simp [hi,hj,ne_comm,or_comm,or_left_comm]⟩
  loopless := ⟨by intro i; simp⟩

instance (b : Fin 6 → Bool) : DecidableRel (sixGraph b).Adj :=
  fun i j => inferInstanceAs (Decidable (i ≠ j ∧
    (if i = 5 then b (j+1) = true
     else if j = 5 then b (i+1) = true
     else i.val < 3 ∨ j.val < 3 ∨ b 0 = true)))

def HasSixthAttachment (G : SimpleGraph (Fin 6)) : Prop :=
  ∃ T : Finset (Fin 6), T.card = 3 ∧ 5 ∉ T ∧ G.IsClique T ∧
    ∀ i ∈ T, G.Adj i 5

def EveryTriangleSaturated (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj] : Prop :=
  ∀ T : Finset (Fin 6), T.card = 3 → G.IsClique T → ∃ i ∈ T, 5 ≤ G.degree i

instance (b : Fin 6 → Bool) : Decidable (HasSixthAttachment (sixGraph b)) := by
  unfold HasSixthAttachment
  infer_instance

instance (b : Fin 6 → Bool) : Decidable (EveryTriangleSaturated (sixGraph b)) := by
  unfold EveryTriangleSaturated
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The finite local obstruction in Lemma 4.5.  This checks exactly the
64 possible supergraphs of the two initial tetrahedra, with every possible
attachment triangle.  It is used as a local lemma in the arbitrary-graph
argument, not as a bounded version of the paper's theorem.  `decide` builds
a proof checked by reduction in the Lean kernel; no native evaluator is used. -/
theorem six_vertex_obstruction :
    ∀ b : Fin 6 → Bool, HasSixthAttachment (sixGraph b) →
      EveryTriangleSaturated (sixGraph b) := by
  decide

def optionalEdges (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj] : Fin 6 → Bool :=
  ![decide (G.Adj 3 4),decide (G.Adj 0 5),decide (G.Adj 1 5),
    decide (G.Adj 2 5),decide (G.Adj 3 5),decide (G.Adj 4 5)]

/-- The finite certificate represents every supergraph of the two indicated
tetrahedra, rather than a selected collection of examples. -/
theorem eq_sixGraph (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj]
    (h₃ : G.IsClique ({0,1,2,3} : Finset (Fin 6)))
    (h₄ : G.IsClique ({0,1,2,4} : Finset (Fin 6))) :
    G = sixGraph (optionalEdges G) := by
  have h01 : G.Adj 0 1 := h₃ (by decide) (by decide) (by decide)
  have h02 : G.Adj 0 2 := h₃ (by decide) (by decide) (by decide)
  have h03 : G.Adj 0 3 := h₃ (by decide) (by decide) (by decide)
  have h04 : G.Adj 0 4 := h₄ (by decide) (by decide) (by decide)
  have h12 : G.Adj 1 2 := h₃ (by decide) (by decide) (by decide)
  have h13 : G.Adj 1 3 := h₃ (by decide) (by decide) (by decide)
  have h14 : G.Adj 1 4 := h₄ (by decide) (by decide) (by decide)
  have h23 : G.Adj 2 3 := h₃ (by decide) (by decide) (by decide)
  have h24 : G.Adj 2 4 := h₄ (by decide) (by decide) (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sixGraph,optionalEdges,h01,h02,h03,h04,h12,h13,h14,h23,h24,
      SimpleGraph.adj_comm] <;> first | exact G.adj_symm h01 | assumption

theorem six_vertex_obstruction_graph (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj]
    (h₃ : G.IsClique ({0,1,2,3} : Finset (Fin 6)))
    (h₄ : G.IsClique ({0,1,2,4} : Finset (Fin 6)))
    (ha : HasSixthAttachment G) : EveryTriangleSaturated G := by
  have he := eq_sixGraph G h₃ h₄
  have ha' : HasSixthAttachment (sixGraph (optionalEdges G)) := by simpa only [he] using ha
  have hs := six_vertex_obstruction (optionalEdges G) ha'
  simpa only [← he] using hs

section Ambient
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- An extra neighbor outside an embedded finite graph raises the ambient
degree by one. This is the arbitrary-size bridge for the six-vertex local
certificate. -/
theorem degree_ge_of_extra_neighbor (f : Fin 6 ↪ V) (i : Fin 6) (w : V)
    (hw : w ∉ Set.range f) (hadj : G.Adj (f i) w) :
    (G.comap f).degree i+1 ≤ G.degree (f i) := by
  classical
  let S := ((G.comap f).neighborFinset i).map f
  have hwS : w ∉ S := by
    intro h
    obtain ⟨j,hj,he⟩ := mem_map.mp h
    exact hw ⟨j,he⟩
  have hsub : insert w S ⊆ G.neighborFinset (f i) := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact (G.mem_neighborFinset _ _).mpr hadj
    · obtain ⟨j,hj,rfl⟩ := mem_map.mp hv
      exact (G.mem_neighborFinset _ _).mpr ((G.comap f).mem_neighborFinset _ _ |>.mp hj)
  calc
    (G.comap f).degree i+1 = (insert w S).card := by
      rw [card_insert_of_notMem hwS]
      simp only [S,card_map,SimpleGraph.card_neighborFinset_eq_degree]
    _ ≤ (G.neighborFinset (f i)).card := card_le_card hsub
    _ = G.degree (f i) := rfl

/-- Once the first six vertices of a triangle-connected tetrahedron family
have appeared, a graph of maximum degree five cannot attach a seventh vertex
to any triangle on those six vertices. The ambient vertex type is unrestricted. -/
theorem no_seventh_triangle_attachment (f : Fin 6 ↪ V)
    (hdeg : ∀ v, G.degree v ≤ 5)
    (h₃ : (G.comap f).IsClique ({0,1,2,3} : Finset (Fin 6)))
    (h₄ : (G.comap f).IsClique ({0,1,2,4} : Finset (Fin 6)))
    (ha : HasSixthAttachment (G.comap f))
    (w : V) (hw : w ∉ Set.range f) (T : Finset (Fin 6))
    (hT : T.card = 3) (hcl : (G.comap f).IsClique T)
    (hneigh : ∀ i ∈ T, G.Adj (f i) w) : False := by
  classical
  obtain ⟨i,hi,hfive⟩ := six_vertex_obstruction_graph (G.comap f) h₃ h₄ ha T hT hcl
  have hsix := degree_ge_of_extra_neighbor G f i w hw (hneigh i hi)
  have hup := hdeg (f i)
  omega

end Ambient

end CliqueDegree
end GraphicalZonotopes

end
end BundlePart331

section BundlePart332
/- Source: Papers/GraphicalZonotopes/GrowthDegree.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem TetrahedralGrowth.four_isClique {G : SimpleGraph V} {S : Finset V}
    (h : TetrahedralGrowth G S) (hS : S.card=4) : G.IsClique S := by
  cases h with
  | base C hc hcl => exact hcl
  | @attach R h u hu T hT hTR hcl ha =>
    have hr := h.card_ge_four
    rw [card_insert_of_notMem hu] at hS
    omega

theorem TetrahedralGrowth.five_structure {G : SimpleGraph V} {S : Finset V}
    (h : TetrahedralGrowth G S) (hS : S.card=5) :
    ∃ C T : Finset V, ∃ e : V, C.card=4 ∧ G.IsClique C ∧
      T.card=3 ∧ T ⊆ C ∧ e ∉ C ∧ (∀ v ∈ T,G.Adj e v) ∧ S=insert e C := by
  cases h with
  | base C hc hcl => omega
  | @attach R h u hu T hT hTR hcl ha =>
    have hr : R.card=4 := by rw [card_insert_of_notMem hu] at hS; omega
    exact ⟨R,T,u,hr,h.four_isClique hr,hT,hTR,hu,ha,rfl⟩

def sixPreimage (f : Fin 6 ↪ V) (T : Finset V) : Finset (Fin 6) :=
  univ.filter (fun i => f i ∈ T)

theorem sixPreimage_image (f : Fin 6 ↪ V) (T : Finset V)
    (hT : ∀ v ∈ T,v ∈ Set.range f) : (sixPreimage f T).map f=T := by
  ext v
  constructor
  · intro hv
    obtain ⟨i,hi,rfl⟩ := mem_map.mp hv
    exact (mem_filter.mp hi).2
  · intro hv
    obtain ⟨i,rfl⟩ := hT v hv
    exact mem_map.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hv⟩,rfl⟩

theorem sixPreimage_card (f : Fin 6 ↪ V) (T : Finset V)
    (hT : ∀ v ∈ T,v ∈ Set.range f) : (sixPreimage f T).card=T.card := by
  have h := congrArg Finset.card (sixPreimage_image f T hT)
  simpa using h

/-- Every six-vertex growth stage is exactly an embedded instance of the
local six-vertex obstruction. No graph edges are discarded by the pullback. -/
theorem TetrahedralGrowth.six_model {G : SimpleGraph V} {S : Finset V}
    (h : TetrahedralGrowth G S) (hS : S.card=6) :
    ∃ f : Fin 6 ↪ V, Set.range f=(S : Set V) ∧
      (G.comap f).IsClique ({0,1,2,3} : Finset (Fin 6)) ∧
      (G.comap f).IsClique ({0,1,2,4} : Finset (Fin 6)) ∧
      CliqueDegree.HasSixthAttachment (G.comap f) := by
  classical
  cases h with
  | base C hc hcl => omega
  | @attach R h f hf U hU hUR hclU hadj =>
    have hR : R.card=5 := by rw [card_insert_of_notMem hf] at hS; omega
    obtain ⟨C,T,e,hC,hclC,hT,hTC,he,heAdj,hRC⟩ := h.five_structure hR
    have hdiff : (C \ T).card=1 := by rw [card_sdiff_of_subset hTC,hC,hT]
    obtain ⟨d,hd⟩ := card_eq_one.mp hdiff
    have hdmem : d ∈ C \ T := by rw [hd]; simp
    have hdC := (mem_sdiff.mp hdmem).1
    have hdT := (mem_sdiff.mp hdmem).2
    have hCT : C=insert d T := by
      have hu := union_sdiff_of_subset hTC
      rw [hd] at hu
      simpa [union_comm] using hu.symm
    obtain ⟨a,b,c,hab,hac,hbc,hTabc⟩ := card_eq_three.mp hT
    have haC : a ∈ C := hTC (by simp [hTabc])
    have hbC : b ∈ C := hTC (by simp [hTabc])
    have hcC : c ∈ C := hTC (by simp [hTabc])
    have hda : d ≠ a := by intro hda; exact hdT (by simp [hda,hTabc])
    have hdb : d ≠ b := by intro hdb; exact hdT (by simp [hdb,hTabc])
    have hdc : d ≠ c := by intro hdc; exact hdT (by simp [hdc,hTabc])
    have hea : e ≠ a := by
      intro heq
      apply he
      simpa only [heq] using haC
    have heb : e ≠ b := by
      intro heq
      apply he
      simpa only [heq] using hbC
    have hec : e ≠ c := by
      intro heq
      apply he
      simpa only [heq] using hcC
    have hed : e ≠ d := by
      intro heq
      apply he
      simpa only [heq] using hdC
    have hCR : C ⊆ R := by rw [hRC]; exact subset_insert _ _
    have heR : e ∈ R := by rw [hRC]; exact mem_insert_self _ _
    have hfa : f ≠ a := by
      intro heq
      apply hf
      simpa only [heq] using hCR haC
    have hfb : f ≠ b := by
      intro heq
      apply hf
      simpa only [heq] using hCR hbC
    have hfc : f ≠ c := by
      intro heq
      apply hf
      simpa only [heq] using hCR hcC
    have hfd : f ≠ d := by
      intro heq
      apply hf
      simpa only [heq] using hCR hdC
    have hfe : f ≠ e := by
      intro heq
      apply hf
      simpa only [heq] using heR
    let names : Fin 6 → V := ![a,b,c,d,e,f]
    have hinj : Function.Injective names := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp only [names,Matrix.cons_val_zero,Matrix.cons_val_succ,
          Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
          Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] at hij ⊢
      all_goals first | rfl | exact False.elim (hab hij) | exact False.elim (hab hij.symm) |
        exact False.elim (hac hij) | exact False.elim (hac hij.symm) |
        exact False.elim (hbc hij) | exact False.elim (hbc hij.symm) |
        exact False.elim (hda hij) | exact False.elim (hda hij.symm) |
        exact False.elim (hdb hij) | exact False.elim (hdb hij.symm) |
        exact False.elim (hdc hij) | exact False.elim (hdc hij.symm) |
        exact False.elim (hea hij) | exact False.elim (hea hij.symm) |
        exact False.elim (heb hij) | exact False.elim (heb hij.symm) |
        exact False.elim (hec hij) | exact False.elim (hec hij.symm) |
        exact False.elim (hed hij) | exact False.elim (hed hij.symm) |
        exact False.elim (hfa hij) | exact False.elim (hfa hij.symm) |
        exact False.elim (hfb hij) | exact False.elim (hfb hij.symm) |
        exact False.elim (hfc hij) | exact False.elim (hfc hij.symm) |
        exact False.elim (hfd hij) | exact False.elim (hfd hij.symm) |
        exact False.elim (hfe hij) | exact False.elim (hfe hij.symm)
    let emb : Fin 6 ↪ V := ⟨names,hinj⟩
    have hnames : ∀ v,v ∈ insert f R ↔ ∃ i : Fin 6,emb i=v := by
      intro v
      rw [hRC,hCT,hTabc]
      simp only [mem_insert,mem_singleton]
      constructor
      · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
        · exact ⟨5,rfl⟩
        · exact ⟨4,rfl⟩
        · exact ⟨3,rfl⟩
        · exact ⟨0,rfl⟩
        · exact ⟨1,rfl⟩
        · exact ⟨2,rfl⟩
      · rintro ⟨i,rfl⟩
        fin_cases i <;> simp [emb,names]
    have hrange : Set.range emb=((insert f R : Finset V) : Set V) := by
      ext v
      exact (hnames v).symm
    have hfirst : ∀ i ∈ ({0,1,2,3} : Finset (Fin 6)),emb i ∈ C := by
      intro i hi
      simp only [mem_insert,mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact haC
      · exact hbC
      · exact hcC
      · exact hdC
    have hsecond : ∀ i ∈ ({0,1,2,4} : Finset (Fin 6)),emb i ∈ insert e T := by
      intro i hi
      simp only [mem_insert,mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> simp [emb,names,hTabc]
    have hclSecond : G.IsClique (insert e T : Finset V) := by
      intro x hx y hy hxy
      rcases mem_insert.mp hx with hxe | hxT
      · rcases mem_insert.mp hy with hye | hyT
        · exact False.elim (hxy (hxe.trans hye.symm))
        · rw [hxe]
          exact heAdj y hyT
      · rcases mem_insert.mp hy with hye | hyT
        · rw [hye]
          exact G.adj_symm (heAdj x hxT)
        · exact hclC (hTC hxT) (hTC hyT) hxy
    refine ⟨emb,hrange,?_,?_,?_⟩
    · intro i hi j hj hij
      exact hclC (hfirst i hi) (hfirst j hj) (fun he => hij (emb.injective he))
    · intro i hi j hj hij
      exact hclSecond (hsecond i hi) (hsecond j hj) (fun he => hij (emb.injective he))
    · have hUrange : ∀ v ∈ U,v ∈ Set.range emb := by
        intro v hv
        rw [hrange]
        exact mem_insert_of_mem (hUR hv)
      refine ⟨sixPreimage emb U,(sixPreimage_card emb U hUrange).trans hU,?_,?_,?_⟩
      · intro h5
        have hmem := (mem_filter.mp h5).2
        change f ∈ U at hmem
        exact hf (hUR hmem)
      · intro i hi j hj hij
        exact hclU (mem_filter.mp hi).2 (mem_filter.mp hj).2
          (fun he => hij (emb.injective he))
      · intro i hi
        exact G.adj_symm (hadj (emb i) (mem_filter.mp hi).2)

theorem degree_comap_le (G : SimpleGraph V) (f : Fin 6 ↪ V) (i : Fin 6) :
    (G.comap f).degree i ≤ G.degree (f i) := by
  classical
  have hsub : ((G.comap f).neighborFinset i).map f ⊆ G.neighborFinset (f i) := by
    intro v hv
    obtain ⟨j,hj,rfl⟩ := mem_map.mp hv
    exact (G.mem_neighborFinset _ _).mpr ((G.comap f).mem_neighborFinset _ _ |>.mp hj)
  have hcard := card_le_card hsub
  simpa only [card_map,SimpleGraph.card_neighborFinset_eq_degree] using hcard

/-- The local certificate applies to every triangle of every six-vertex
growth stage inside an arbitrary finite ambient graph. -/
theorem TetrahedralGrowth.six_triangle_saturated {G : SimpleGraph V} {S : Finset V}
    (h : TetrahedralGrowth G S) (hS : S.card=6) (T : Finset V)
    (hT : T.card=3) (hTS : T ⊆ S) (hcT : G.IsClique T) :
    ∃ v ∈ T,5 ≤ G.degree v := by
  classical
  obtain ⟨f,hrange,h₃,h₄,ha⟩ := h.six_model hS
  have hTrange : ∀ v ∈ T,v ∈ Set.range f := by
    intro v hv
    rw [hrange]
    exact hTS hv
  have hc : (G.comap f).IsClique (sixPreimage f T) := by
    intro i hi j hj hij
    exact hcT (mem_filter.mp hi).2 (mem_filter.mp hj).2
      (fun he => hij (f.injective he))
  obtain ⟨i,hi,hdeg⟩ := CliqueDegree.six_vertex_obstruction_graph (G.comap f)
    h₃ h₄ ha (sixPreimage f T) ((sixPreimage_card f T hTrange).trans hT) hc
  exact ⟨f i,(mem_filter.mp hi).2,hdeg.trans (degree_comap_le G f i)⟩

theorem TetrahedralGrowth.six_cannot_attach_at_degree_five {G : SimpleGraph V}
    {S : Finset V} (h : TetrahedralGrowth G S) (hS : S.card=6)
    (hdeg : ∀ v,G.degree v ≤ 5) (u : V) (hu : u ∉ S) (T : Finset V)
    (hT : T.card=3) (hTS : T ⊆ S) (hcT : G.IsClique T)
    (hadj : ∀ v ∈ T,G.Adj u v) : False := by
  classical
  obtain ⟨f,hrange,h₃,h₄,ha⟩ := h.six_model hS
  have hTrange : ∀ v ∈ T,v ∈ Set.range f := by
    intro v hv
    rw [hrange]
    exact hTS hv
  apply CliqueDegree.no_seventh_triangle_attachment G f hdeg h₃ h₄ ha u
    (by simpa [hrange] using hu) (sixPreimage f T)
    ((sixPreimage_card f T hTrange).trans hT)
  · intro i hi j hj hij
    exact hcT (mem_filter.mp hi).2 (mem_filter.mp hj).2
      (fun he => hij (f.injective he))
  · intro i hi
    exact G.adj_symm (hadj (f i) (mem_filter.mp hi).2)

theorem clique_degree_lower (G : SimpleGraph V) (C : Finset V)
    (hC : G.IsClique C) (v : V) (hv : v ∈ C) : C.card-1 ≤ G.degree v := by
  classical
  have hsub : C.erase v ⊆ G.neighborFinset v := by
    intro w hw
    have hm := mem_erase.mp hw
    exact (G.mem_neighborFinset _ _).mpr (hC hv hm.2 (Ne.symm hm.1))
  have h := card_le_card hsub
  simpa only [card_erase_of_mem hv,SimpleGraph.card_neighborFinset_eq_degree] using h

theorem TetrahedralGrowth.contains_triangle {G : SimpleGraph V} {S : Finset V}
    (h : TetrahedralGrowth G S) :
    ∃ T : Finset V,T.card=3 ∧ T ⊆ S ∧ G.IsClique T := by
  induction h with
  | base C hc hcl =>
    obtain ⟨T,hTC,hT⟩ := exists_subset_card_eq (show 3 ≤ C.card by omega)
    exact ⟨T,hT,hTC,fun u hu v hv huv => hcl (hTC hu) (hTC hv) huv⟩
  | attach h u hu T hT hsub hcl hadj ih =>
    obtain ⟨A,hA,hAS,hclA⟩ := ih
    exact ⟨A,hA,hAS.trans (subset_insert _ _),hclA⟩

theorem TetrahedralGrowth.five_has_degree_four {G : SimpleGraph V} {S : Finset V}
    (h : TetrahedralGrowth G S) (hS : S.card=5) : ∃ v,4 ≤ G.degree v := by
  classical
  obtain ⟨C,T,e,hC,hclC,hT,hTC,he,heAdj,hSC⟩ := h.five_structure hS
  obtain ⟨v,hv⟩ := card_pos.mp (show 0< T.card by omega)
  have hvC := hTC hv
  have heErase : e ∉ C.erase v := fun h => he (mem_of_mem_erase h)
  have hsub : insert e (C.erase v) ⊆ G.neighborFinset v := by
    intro w hw
    rcases mem_insert.mp hw with rfl | hw
    · exact (G.mem_neighborFinset _ _).mpr (G.adj_symm (heAdj v hv))
    · obtain ⟨hwv,hwC⟩ := mem_erase.mp hw
      exact (G.mem_neighborFinset _ _).mpr (hclC hvC hwC (Ne.symm hwv))
  have hcard := card_le_card hsub
  rw [card_insert_of_notMem heErase,card_erase_of_mem hvC,hC] at hcard
  exact ⟨v,hcard⟩

theorem TetrahedralGrowth.seven_has_degree_six {G : SimpleGraph V} {S : Finset V}
    (h : TetrahedralGrowth G S) (hS : 7 ≤ S.card) : ∃ v,6 ≤ G.degree v := by
  classical
  induction h with
  | base C hc hcl => omega
  | @attach R h u hu T hT hTR hcl hadj ih =>
    by_cases hlarge : 7 ≤ R.card
    · exact ih hlarge
    · have hR : R.card=6 := by rw [card_insert_of_notMem hu] at hS; omega
      by_contra hno
      have hdeg : ∀ v,G.degree v ≤ 5 := by
        intro v
        have hv : ¬6 ≤ G.degree v := fun hv => hno ⟨v,hv⟩
        omega
      exact h.six_cannot_attach_at_degree_five hR hdeg u hu T hT hTR hcl hadj

/-- The complete arbitrary-size degree bound, using the finite certificate
only at the six-to-seven transition of a genuine tetrahedral growth. -/
theorem TetrahedralGrowth.degree_lower {G : SimpleGraph V} {S : Finset V}
    (h : TetrahedralGrowth G S) : ∃ v,min (S.card-1) 6 ≤ G.degree v := by
  classical
  have hmin := h.card_ge_four
  by_cases h4 : S.card=4
  · obtain ⟨v,hv⟩ := card_pos.mp (show 0< S.card by omega)
    have hd := clique_degree_lower G S (h.four_isClique h4) v hv
    exact ⟨v,by simpa [h4] using hd⟩
  · by_cases h5 : S.card=5
    · obtain ⟨v,hv⟩ := h.five_has_degree_four h5
      exact ⟨v,by simpa [h5] using hv⟩
    · by_cases h6 : S.card=6
      · obtain ⟨T,hT,hTS,hclT⟩ := h.contains_triangle
        obtain ⟨v,hv,hdeg⟩ := h.six_triangle_saturated h6 T hT hTS hclT
        exact ⟨v,by simpa [h6] using hdeg⟩
      · obtain ⟨v,hv⟩ := h.seven_has_degree_six (by omega)
        exact ⟨v,(min_le_right _ _).trans hv⟩

theorem maximum_degree_bound_of_connected_tetrahedra (G : SimpleGraph V)
    (F : Finset (Finset V)) (hne : F.Nonempty)
    (hcl : ∀ C ∈ F,C.card=4 ∧ G.IsClique C)
    (hconn : (tetrahedronGraph F).Preconnected) (hcover : F.biUnion id=univ) :
    min (Fintype.card V-1) 6 ≤ G.maxDegree := by
  classical
  have hg := tetrahedralGrowth_of_connected_family G F hne hcl hconn
  rw [hcover] at hg
  obtain ⟨v,hv⟩ := hg.degree_lower
  have h := hv.trans (G.degree_le_maxDegree v)
  simpa using h

end GraphicalZonotopes

end
end
end BundlePart332

section BundlePart333
/- Source: Papers/GraphicalZonotopes/SpanningTetrahedra.lean -/








@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
namespace PositiveDecomposition
variable {V : Type*} [Fintype V] [LinearOrder V]

@[simp] theorem allocation_zero_function : allocation (0 : SetFunction V)=0 := by
  funext C
  by_cases hC : C.card = 2
  · obtain ⟨u,v,huv,rfl⟩ := card_eq_two.mp hC
    rw [allocation_pair _ huv]
    have hm : minimumSlack (0 : SetFunction V) u v=0 :=
      minimumSlack_eq_zero (by intros; simp [delta])
    simp [hm]
  · exact allocation_zero _ hC

@[simp] theorem adjusted_zero : adjusted (0 : SetFunction V)=0 := by
  rw [adjusted,allocation_zero_function]
  change 0+zetaLinear 0=0
  simp

theorem higherClass_right_dependsOn {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y) (T : Finset V) :
    GraphicalZonotopes.DependsOn
      (higherClass y (TriangleComponents.classOf G) (Sum.inr T)) T := by
  apply zeta_dependsOn
  intro C hC
  by_contra he
  obtain ⟨hc,ha,hyC⟩ := classCoefficients_nonzero he
  obtain ⟨h3,rfl⟩ := TriangleComponents.right_class_is_triangle hy hc hyC ha
  exact hC Subset.rfl

theorem higherClass_right_zero_of_card_ne_three {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y) {T : Finset V} (hT : T.card ≠ 3) :
    higherClass y (TriangleComponents.classOf G) (Sum.inr T)=0 := by
  apply (zeta_eq_zero_iff _).mpr
  funext C
  by_contra he
  obtain ⟨hc,ha,hyC⟩ := classCoefficients_nonzero he
  obtain ⟨h3,rfl⟩ := TriangleComponents.right_class_is_triangle hy hc hyC ha
  exact hT h3

theorem higherClass_left_dependsOn {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y) (a : (TriangleComponents.cliqueGraph G).ConnectedComponent) :
    GraphicalZonotopes.DependsOn
      (higherClass y (TriangleComponents.classOf G) (Sum.inl a))
      (TriangleComponents.componentVertices G a) := by
  apply zeta_dependsOn
  intro C hC
  by_contra he
  obtain ⟨hc,ha,hyC⟩ := classCoefficients_nonzero he
  apply hC
  by_cases h3 : C.card = 3
  · exact TriangleComponents.triangle_subset_component h3 ha
  · have h4 : 4 ≤ C.card := by omega
    have hcl : G.IsClique C := by
      intro u hu v hv huv
      by_contra hn
      exact hyC (hy.2.2 C u v hu hv huv hn)
    exact TriangleComponents.higher_subset_component h4 hcl ha

def allPieces (G : SimpleGraph V) (y : SetFunction V) :
    (TriangleComponents.ComponentIndex G ⊕ Finset V) → SetFunction V :=
  Sum.elim (fun a => adjusted (higherClass y (TriangleComponents.classOf G) a))
    (fun C => residual y (higherClass y (TriangleComponents.classOf G)) C • setMonomial C)

theorem allPieces_positive {G : SimpleGraph V} (y : SetFunction V)
    (hy : CliqueSupported G y) (hs : Supermodular (zeta y)) :
    (∀ i, TranslationNormalized (allPieces G y i) ∧ Supermodular (allPieces G y i)) ∧
    (∑ i, allPieces G y i)=zeta y := by
  classical
  obtain ⟨hp,hr,hrn,hrs,he⟩ := compatible_class_decomposition y hy hs
    (TriangleComponents.classOf G) (TriangleComponents.classOf_compatible hy)
  constructor
  · intro i
    cases i with
    | inl a => exact ⟨(hp a).1,(hp a).2.1⟩
    | inr C =>
      have hnonneg := hr C
      refine ⟨?_,(setMonomial_supermodular C).smul hnonneg⟩
      by_cases hC : C.card = 2
      · have hn : TranslationNormalized (setMonomial C) := by
          refine ⟨setMonomial_normalized (card_pos.mp (by omega)),?_⟩
          intro v
          have hnot : ¬ C ⊆ {v} := by
            intro hsub
            have hcard := card_le_card hsub
            simp only [card_singleton] at hcard
            omega
          simp [setMonomial,hnot]
        exact ⟨by change _*setMonomial C ∅=0; rw [hn.1,mul_zero],
          fun v => by change _*setMonomial C {v}=0; rw [hn.2 v,mul_zero]⟩
      · have hz := residual_zero y (higherClass y (TriangleComponents.classOf G)) hC
        simp only [allPieces,Sum.elim_inr,hz,zero_smul]
        exact ⟨rfl,fun _ => rfl⟩
  · rw [Fintype.sum_sum_type]
    change (∑ a,adjusted (higherClass y (TriangleComponents.classOf G) a))+
      (∑ C,residual y (higherClass y (TriangleComponents.classOf G)) C • setMonomial C)=_
    rw [← zeta_eq_sum_monomials]
    exact he

end PositiveDecomposition

theorem graphical_actualDirectionGraph {V : Type*} [Fintype V] [DecidableEq V]
    {z : SetFunction V} (hn : Normalized z) (hs : Supermodular z) :
    Graphical (actualDirectionGraph (basePolytope z)) z := by
  intro u v huv hnon S hu hv
  have hnonneg := hs.elemental u v huv S hu hv
  apply le_antisymm _ hnonneg
  by_contra h
  have hpos : 0 < delta z u v S := lt_of_not_ge h
  exact hnon (exposedSegment_of_positive_delta hn hs huv hu hv hpos)

/-- Lemma4.3: the tetrahedral component is constructed from the actual
positive decomposition. No connectivity or coefficient-sign hypothesis has
been added to the indecomposable polytope. -/
theorem ExtremeSupermodular.spanning_tetrahedra {n : ℕ} (hn : 4 ≤ n)
    {z : SetFunction (Fin n)} (hz : ExtremeSupermodular z)
    (hfull : Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=n-1)
    {G : SimpleGraph (Fin n)} (hG : Graphical G z) :
    ∃ F : Finset (Finset (Fin n)), F.Nonempty ∧
      (∀ C ∈ F,C.card=4 ∧ G.IsClique C) ∧
      (tetrahedronGraph F).Preconnected ∧ F.biUnion id=univ := by
  classical
  let y := mobius z
  have hy : CliqueSupported G y := (mobius_cliqueSupported_iff G z).mpr ⟨hz.1,hG⟩
  have hys : Supermodular (zeta y) := by simpa [y] using hz.2.1
  obtain ⟨hp,he⟩ := PositiveDecomposition.allPieces_positive y hy hys
  have hez : (∑ i,PositiveDecomposition.allPieces G y i)=z := by simpa [y] using he
  have hex : ∃ i,PositiveDecomposition.allPieces G y i ≠ 0 := by
    by_contra h
    push_neg at h
    have hzero : (∑ i,PositiveDecomposition.allPieces G y i)=0 :=
      sum_eq_zero (fun i hi => h i)
    exact hz.2.2.1 (hez.symm.trans hzero)
  obtain ⟨i,hi⟩ := hex
  obtain ⟨a,ha,hscale⟩ := hz.finite_summand (PositiveDecomposition.allPieces G y)
    (fun i => (hp i).1) (fun i => (hp i).2) hez hi
  have hsupport : ∀ S, DependsOn (PositiveDecomposition.allPieces G y i) S → S=univ := by
    intro S hS
    rw [hscale] at hS
    exact fullDimension_dependsOn_eq_univ (by omega) hz.1 hz.2.1 hfull
      (DependsOn.of_smul (ne_of_gt ha) hS)
  cases i with
  | inr C =>
    have hC : C.card=2 := by
      by_contra hnot
      have hzC := PositiveDecomposition.residual_zero y
        (PositiveDecomposition.higherClass y (TriangleComponents.classOf G)) hnot
      exact hi (by simp [PositiveDecomposition.allPieces,hzC])
    have hdep : DependsOn (PositiveDecomposition.allPieces G y (Sum.inr C)) C :=
      (setMonomial_dependsOn C).smul _
    have hcard := congrArg Finset.card (hsupport C hdep)
    simp only [hC,card_univ,Fintype.card_fin] at hcard
    omega
  | inl c =>
    cases c with
    | inr T =>
      have hT : T.card=3 := by
        by_contra hnot
        have hzero := PositiveDecomposition.higherClass_right_zero_of_card_ne_three hy hnot
        apply hi
        change PositiveDecomposition.adjusted
          (PositiveDecomposition.higherClass y (TriangleComponents.classOf G)
            (Sum.inr T)) = 0
        exact (congrArg PositiveDecomposition.adjusted hzero).trans
          PositiveDecomposition.adjusted_zero
      have hdep := PositiveDecomposition.DependsOn.adjusted
        (PositiveDecomposition.higherClass_right_dependsOn hy T)
      have hcard := congrArg Finset.card (hsupport T hdep)
      simp only [hT,card_univ,Fintype.card_fin] at hcard
      omega
    | inl c =>
      have hdep := PositiveDecomposition.DependsOn.adjusted
        (PositiveDecomposition.higherClass_left_dependsOn hy c)
      have hcover := hsupport (TriangleComponents.componentVertices G c) hdep
      refine ⟨TriangleComponents.componentFamily G c,?_,?_,
        TriangleComponents.componentFamily_preconnected G c,hcover⟩
      · have hm : (⟨0,by omega⟩ : Fin n) ∈ TriangleComponents.componentVertices G c := by
          rw [hcover]
          exact mem_univ _
        obtain ⟨C,hC,hv⟩ := mem_biUnion.mp hm
        exact ⟨C,hC⟩
      · intro C hC
        have hc := TriangleComponents.mem_componentFamily.mp hC
        exact ⟨hc.1,hc.2.1⟩

theorem ExtremeSupermodular.direction_count_bound {n : ℕ} (hn : 4 ≤ n)
    {z : SetFunction (Fin n)} (hz : ExtremeSupermodular z)
    (hfull : Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=n-1) :
    3*n-6 ≤ directionCount (basePolytope z) ∧
      (directionCount (basePolytope z)=3*n-6 →
        IsThreeTree (actualDirectionGraph (basePolytope z))) := by
  obtain ⟨F,hne,hcl,hconn,hcover⟩ := hz.spanning_tetrahedra hn hfull
    (graphical_actualDirectionGraph hz.1.1 hz.2.1)
  simpa [directionCount] using edge_bound_of_connected_tetrahedra _ F hne hcl hconn hcover

theorem ExtremeSupermodular.maximum_degree_bound {n : ℕ} (hn : 4 ≤ n)
    {z : SetFunction (Fin n)} (hz : ExtremeSupermodular z)
    (hfull : Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=n-1) :
    min (n-1) 6 ≤ maximumDirectionDegree (basePolytope z) := by
  classical
  obtain ⟨F,hne,hcl,hconn,hcover⟩ := hz.spanning_tetrahedra hn hfull
    (graphical_actualDirectionGraph hz.1.1 hz.2.1)
  simpa [maximumDirectionDegree] using
    maximum_degree_bound_of_connected_tetrahedra _ F hne hcl hconn hcover

end GraphicalZonotopes

end
end
end BundlePart333

section BundlePart334
/- Source: Papers/GraphicalZonotopes/DirectionBounds.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes

/-- Theorem4.1, with all translations and no clique-number restriction.
The matching path-cube attainment is the separate principal family theorem. -/
theorem direction_bounds (n : ℕ) (hn : 4 ≤ n) (Q : Set (Fin n → ℝ))
    (hQ : IsGeneralizedPermutahedron Q) (hi : MinkowskiIndecomposable Q)
    (hd : FullDimension Q) :
    3*n-6 ≤ directionCount Q ∧ min (n-1) 6 ≤ maximumDirectionDegree Q ∧
    (directionCount Q=3*n-6 → IsThreeTree (actualDirectionGraph Q)) := by
  obtain ⟨z,hzn,hzs,rfl⟩ := hQ
  have hdim : Module.finrank ℝ (vectorSpan ℝ (basePolytope (normalize z)))=n-1 := by
    rw [vectorSpan_basePolytope_normalize]
    simpa [FullDimension] using hd
  have hne : normalize z ≠ 0 := by
    intro hz0
    rw [hz0,basePolytope_zero] at hdim
    have hspan : vectorSpan ℝ ({0} : Set (Fin n → ℝ)) =
        (⊥ : Submodule ℝ (Fin n → ℝ)) :=
      _root_.vectorSpan_singleton ℝ (0 : Fin n → ℝ)
    rw [hspan, _root_.finrank_bot] at hdim
    omega
  have hext := hi.extremeSupermodular_normalize hzn hzs hne
  obtain ⟨hedges,heq⟩ := hext.direction_count_bound hn hdim
  have hdegree := hext.maximum_degree_bound hn hdim
  have hgraph := actualDirectionGraph_normalize z
  have hecount : directionCount (basePolytope (normalize z))=directionCount (basePolytope z) := by
    unfold directionCount
    rw [hgraph]
  have hedegree : maximumDirectionDegree (basePolytope (normalize z))=
      maximumDirectionDegree (basePolytope z) := by
    unfold maximumDirectionDegree
    rw [hgraph]
  rw [hecount] at hedges heq
  rw [hedegree] at hdegree
  exact ⟨hedges,hdegree,fun h => by simpa only [hgraph] using heq h⟩

/-- The same theorem with the traditional polytope-summand definition in
its hypothesis. This prevents the stronger-looking compact-convex wording
from concealing a restriction on the paper's class of indecomposable polytopes. -/
theorem direction_bounds_polytopal (n : ℕ) (hn : 4≤ n) (Q : Set (Fin n → ℝ))
    (hQ : IsGeneralizedPermutahedron Q) (hi : PolytopalMinkowskiIndecomposable Q)
    (hd : FullDimension Q) :
    3*n-6≤ directionCount Q ∧ min (n-1) 6≤ maximumDirectionDegree Q ∧
    (directionCount Q=3*n-6 → IsThreeTree (actualDirectionGraph Q)) :=
  direction_bounds n hn Q hQ ((minkowskiIndecomposable_iff_polytopal hQ).mpr hi) hd

end GraphicalZonotopes

end
end
end BundlePart334

section BundlePart335
/- Source: Papers/GraphicalZonotopes/SharpDirectionBounds.lean -/






@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open scoped Pointwise

/-- The root-direction graph counts every geometric edge direction of an
actual generalized permutahedron. This includes arbitrary translations. -/
theorem generalizedPermutahedron_exposed_edge_is_root
    {V : Type*} [Fintype V] [DecidableEq V] {Q : Set (V → ℝ)}
    (hQ : IsGeneralizedPermutahedron Q) {p q : V → ℝ}
    (hex : IsExposedSegment Q p q) :
    ∃ u v : V,u≠ v ∧ ∃ t : ℝ,t≠0 ∧
      q-p=t • (basisVector v-basisVector u) := by
  obtain ⟨z,hn,hs,rfl⟩ := hQ
  have hweak : IsWeakMinkowskiSummand (basePolytope z)
      (graphicalZonotope (⊤ : SimpleGraph V)) := by
    apply (isWeakMinkowskiSummand_graphical_iff hn hs).mpr
    intro u v huv hnon
    exact False.elim (hnon huv)
  obtain ⟨a,ha,R,_,_,_,he⟩ := hweak
  obtain ⟨u,v,huv,t,ht,heq⟩ :=
    basePolytope_summand_exposed_edge hn hs (⊤ : SimpleGraph V) ha.le R he hex
  exact ⟨u,v,huv,t,ht,heq⟩

namespace Path

theorem actualDirectionGraph_eq {n : ℕ} (hn : 4≤ n) :
    actualDirectionGraph (polytope n)=graph n := by
  apply SimpleGraph.ext
  funext u v
  exact propext (actual_direction_graph hn u v)

theorem polytope_generalizedPermutahedron (n : ℕ) :
    IsGeneralizedPermutahedron (polytope n) :=
  ⟨setFunction n,(setFunction_normalized n).1,setFunction_supermodular n,rfl⟩

theorem polytope_polytopalIndecomposable {n : ℕ} (hn : 4≤ n) :
    PolytopalMinkowskiIndecomposable (polytope n) :=
  (minkowskiIndecomposable_iff_polytopal (polytope_generalizedPermutahedron n)).mp
    (polytope_indecomposable hn)

theorem polytope_fullDimension {n : ℕ} (hn : 4≤ n) :
    FullDimension (polytope n) := by
  simpa only [FullDimension,Fintype.card_fin] using polytope_dimension hn

theorem directionCount_eq {n : ℕ} (hn : 4≤ n) :
    directionCount (polytope n)=3*n-6 := by
  rw [directionCount,actualDirectionGraph_eq hn]
  exact graph_edge_count hn

theorem maximumDirectionDegree_eq {n : ℕ} (hn : 4≤ n) :
    maximumDirectionDegree (polytope n)=min (n-1) 6 := by
  classical
  letI : DecidableRel (graph n).Adj := graph_decidableAdj n
  change (actualDirectionGraph (polytope n)).maxDegree=min (n-1) 6
  let e : actualDirectionGraph (polytope n) ≃g graph n :=
    { toEquiv := Equiv.refl _
      map_rel_iff' := by
        intro u v
        exact (actual_direction_graph hn u v).symm }
  exact e.maxDegree_eq.trans (graph_maxDegree hn)

end Path

/-- The full content of Theorem4.1: both universal sharp bounds, the equality
classification, and simultaneous attainment by the paper's explicit Q_n for
every n≥4. The definition uses ordinary polytopal indecomposability. -/
def SharpDirectionBounds : Prop :=
  (∀ n : ℕ,4≤ n → ∀ Q : Set (Fin n → ℝ),
    IsGeneralizedPermutahedron Q → PolytopalMinkowskiIndecomposable Q →
    FullDimension Q →
    3*n-6≤ directionCount Q ∧ min (n-1) 6≤ maximumDirectionDegree Q ∧
    (directionCount Q=3*n-6 → IsThreeTree (actualDirectionGraph Q))) ∧
  ∀ n : ℕ,4≤ n →
    IsGeneralizedPermutahedron (Path.polytope n) ∧
    PolytopalMinkowskiIndecomposable (Path.polytope n) ∧
    FullDimension (Path.polytope n) ∧
    directionCount (Path.polytope n)=3*n-6 ∧
    maximumDirectionDegree (Path.polytope n)=min (n-1) 6

/-- A single audited endpoint is required for the entire sharp theorem,
including the explicit equality witnesses in its final sentence. -/
theorem sharp_direction_bounds : SharpDirectionBounds := by
  refine ⟨direction_bounds_polytopal,?_⟩
  intro n hn
  exact ⟨Path.polytope_generalizedPermutahedron n,
    Path.polytope_polytopalIndecomposable hn,Path.polytope_fullDimension hn,
    Path.directionCount_eq hn,Path.maximumDirectionDegree_eq hn⟩

end GraphicalZonotopes

end
end
end BundlePart335

section BundlePart336
/- Source: Papers/GraphicalZonotopes/TriangularExtensionGeometry.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace BooleanVertexExtension
open Finset BooleanModule
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem andOr_graphical {G : SimpleGraph V} {a b t : V}
    (hT : G.IsClique ({a,b,t} : Finset V)) : Graphical G (andOr a b t) := by
  intro u v huv hnon S hu hv
  by_cases huT : u ∈ ({a,b,t} : Finset V)
  · by_cases hvT : v ∈ ({a,b,t} : Finset V)
    · exact False.elim (hnon (hT huT hvT huv))
    · have hva : v ≠ a := fun he => hvT (by simp [he])
      have hvb : v ≠ b := fun he => hvT (by simp [he])
      have hvt : v ≠ t := fun he => hvT (by simp [he])
      rw [delta_comm]
      exact andOr_delta_outside hva hvb hvt u S
  · have hua : u ≠ a := fun he => huT (by simp [he])
    have hub : u ≠ b := fun he => huT (by simp [he])
    have hut : u ≠ t := fun he => huT (by simp [he])
    exact andOr_delta_outside hua hub hut v S

theorem triangular_append_graphical {G : SimpleGraph V} {z : SetFunction V} {a b t : V}
    (hz : Graphical G z) (hT : G.IsClique ({a,b,t} : Finset V)) :
    Graphical (SingleVertexGraph.graph G {a,b,t}) (append z (andOr a b t)) := by
  intro x y hxy hnon A hx hy
  have hF := andOr_graphical hT
  cases x with
  | inl u =>
    cases y with
    | inl v =>
      have huv : u ≠ v := fun he => hxy (congrArg Sum.inl he)
      have hu : u ∉ hubs A := by simpa using hx
      have hv : v ∉ hubs A := by simpa using hy
      rw [append_delta_old,hz u v huv hnon _ hu hv,hF u v huv hnon _ hu hv]
      split_ifs <;> simp
    | inr j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      change u ∉ ({a,b,t} : Finset V) at hnon
      have hua : u ≠ a := fun he => hnon (by simp [he])
      have hub : u ≠ b := fun he => hnon (by simp [he])
      have hut : u ≠ t := fun he => hnon (by simp [he])
      rw [append_delta_new _ _ _ _ hy,andOr_insert_outside hua hub hut,sub_self]
  | inr i =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    cases y with
    | inl v =>
      change v ∉ ({a,b,t} : Finset V) at hnon
      have hva : v ≠ a := fun he => hnon (by simp [he])
      have hvb : v ≠ b := fun he => hnon (by simp [he])
      have hvt : v ≠ t := fun he => hnon (by simp [he])
      rw [delta_comm,append_delta_new _ _ _ _ hx,andOr_insert_outside hva hvb hvt,sub_self]
    | inr j => exact False.elim (hxy (congrArg Sum.inr (Subsingleton.elim _ _)))

theorem triangular_append_old_positive {z : SetFunction V} {a b t u v : V}
    {S : Finset V} (hu : u ∉ S) (hv : v ∉ S) (hp : 0 < delta z u v S) :
    Sum.inl u ∉ (hubSet (J := Fin 1) S) ∧ Sum.inl v ∉ (hubSet (J := Fin 1) S) ∧
      0 < delta (append z (andOr a b t)) (Sum.inl u) (Sum.inl v) (hubSet S) := by
  refine ⟨by simpa using hu,by simpa using hv,?_⟩
  rw [append_delta_old]
  simpa using hp

theorem triangular_append_spoke_positive {z : SetFunction V} {a b t : V}
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) {u : V}
    (hu : u ∈ ({a,b,t} : Finset V)) :
    ∃ A : Finset (Vertex V), Sum.inl u ∉ A ∧ Sum.inr 0 ∉ A ∧
      0 < delta (append z (andOr a b t)) (Sum.inl u) (Sum.inr 0) A := by
  simp only [mem_insert,mem_singleton] at hu
  rcases hu with rfl | rfl | rfl
  · refine ⟨hubSet {b},by simpa using hab,by simp,?_⟩
    rw [append_delta_new _ _ _ _ (by simp)]
    simp [andOr,hab,hat,hbt,Ne.symm hab,Ne.symm hat,Ne.symm hbt]
  · refine ⟨hubSet {a},by simpa using hab.symm,by simp,?_⟩
    rw [append_delta_new _ _ _ _ (by simp)]
    simp [andOr,hab,hat,hbt,Ne.symm hab,Ne.symm hat,Ne.symm hbt]
  · refine ⟨hubSet {b},by simpa using hbt.symm,by simp,?_⟩
    rw [append_delta_new _ _ _ _ (by simp)]
    simp [andOr,hab,hat,hbt,Ne.symm hab,Ne.symm hat,Ne.symm hbt]

theorem triangular_append_positive {G : SimpleGraph V} {z : SetFunction V} {a b t : V}
    (hb : UnitBoundary z a b t)
    (hz : ∀ u v, G.Adj u v → ∃ S : Finset V, u ∉ S ∧ v ∉ S ∧ 0 < delta z u v S) :
    ∀ x y, (SingleVertexGraph.graph G {a,b,t}).Adj x y →
      ∃ A : Finset (Vertex V), x ∉ A ∧ y ∉ A ∧
        0 < delta (append z (andOr a b t)) x y A := by
  intro x y hxy
  cases x with
  | inl u =>
    cases y with
    | inl v =>
      obtain ⟨S,hu,hv,hp⟩ := hz u v hxy
      exact ⟨hubSet S,triangular_append_old_positive hu hv hp⟩
    | inr j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact triangular_append_spoke_positive hb.1 hb.2.1 hb.2.2.1 hxy
  | inr i =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    cases y with
    | inl v =>
      obtain ⟨A,hv,hw,hp⟩ := triangular_append_spoke_positive
        (z := z) hb.1 hb.2.1 hb.2.2.1 hxy
      exact ⟨A,hw,hv,by simpa only [delta_comm] using hp⟩
    | inr j => exact False.elim hxy

theorem append_integerValued {z F : SetFunction V} (hz : IntegerValued z)
    (hF : IsMonotoneBoolean F) : IntegerValued (append z F) := by
  intro A
  obtain ⟨k,hk⟩ := hz (hubs A)
  have he : append z F A = z (hubs A) + if Sum.inr 0 ∈ A then F (hubs A) else 0 := by
    simp [append,assembled,boundaryLift,branchLift,Finset.sum_apply]
  rw [he,hk]
  by_cases hw : Sum.inr 0 ∈ A
  · rw [if_pos hw]
    rcases hF.values (hubs A) with hzero | hone
    · exact ⟨k,by rw [hzero,add_zero]⟩
    · exact ⟨k+1,by rw [hone]; norm_num⟩
  · exact ⟨k,by rw [if_neg hw,add_zero]⟩

theorem triangular_append_triangle {G : SimpleGraph V} {a b t : V}
    (hab : a ≠ b) (hT : G.IsClique ({a,b,t} : Finset V)) :
    (SingleVertexGraph.graph G {a,b,t}).IsClique
      ({Sum.inl b,Sum.inl a,Sum.inr 0} : Finset (Vertex V)) := by
  intro x hx y hy hxy
  change x ∈ ({Sum.inl b,Sum.inl a,Sum.inr 0} : Finset (Vertex V)) at hx
  change y ∈ ({Sum.inl b,Sum.inl a,Sum.inr 0} : Finset (Vertex V)) at hy
  simp only [mem_insert,mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  · exact False.elim (hxy rfl)
  · exact hT (by simp) (by simp) hab.symm
  · exact mem_insert_of_mem (mem_insert_self _ _)
  · exact hT (by simp) (by simp) hab
  · exact False.elim (hxy rfl)
  · exact mem_insert_self _ _
  · exact mem_insert_of_mem (mem_insert_self _ _)
  · exact mem_insert_self _ _
  · exact False.elim (hxy rfl)

end BooleanVertexExtension
end GraphicalZonotopes

end
end
end BundlePart336

section BundlePart337
/- Source: Papers/GraphicalZonotopes/SparseFamilyGeometry.lean -/





/-! # An unbounded family with one edge above the sharp direction bound

The graphs are precisely the graphs `L_(10+m)` in Section 8.2. The polynomial
is an alternative uniform construction: at each step append the Boolean
marginal `b ∧ (a ∨ t)`, then exchange the names of the two hubs. This retains
all old directions and raises the maximum elemental slack by at most one.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace SparseFamily
open Finset BooleanModule BooleanVertexExtension
open scoped BigOperators Pointwise

def Vertex : ℕ → Type
  | 0 => Fin 10
  | m+1 => BooleanVertexExtension.Vertex (Vertex m)

instance vertexFintype (m : ℕ) : Fintype (Vertex m) := by
  induction m with
  | zero => exact inferInstanceAs (Fintype (Fin 10))
  | succ m ih =>
    letI : Fintype (Vertex m) := ih
    exact inferInstanceAs (Fintype (Vertex m ⊕ Fin 1))

instance vertexDecidableEq (m : ℕ) : DecidableEq (Vertex m) := by
  induction m with
  | zero => exact inferInstanceAs (DecidableEq (Fin 10))
  | succ m ih =>
    letI : DecidableEq (Vertex m) := ih
    exact inferInstanceAs (DecidableEq (Vertex m ⊕ Fin 1))

def frame : (m : ℕ) → Vertex m × Vertex m × Vertex m
  | 0 => ((0 : Fin 10),(1 : Fin 10),(6 : Fin 10))
  | m+1 => (Sum.inl (frame m).2.1,Sum.inl (frame m).1,Sum.inr 0)

abbrev first (m : ℕ) : Vertex m := (frame m).1
abbrev second (m : ℕ) : Vertex m := (frame m).2.1
abbrev tip (m : ℕ) : Vertex m := (frame m).2.2

def graph : (m : ℕ) → SimpleGraph (Vertex m)
  | 0 => DiamondGeometry.graph
  | m+1 => SingleVertexGraph.graph (graph m) {first m,second m,tip m}

/-- The distinguished triangle has three different vertices at every step;
this fact depends only on the recursive graph presentation. -/
theorem frame_distinct (m : ℕ) :
    first m ≠ second m ∧ first m ≠ tip m ∧ second m ≠ tip m := by
  induction m with
  | zero =>
    change (0 : Fin 10) ≠ 1 ∧ (0 : Fin 10) ≠ 6 ∧ (1 : Fin 10) ≠ 6
    decide
  | succ m ih =>
    change (Sum.inl (second m) : Vertex m ⊕ Fin 1) ≠ Sum.inl (first m) ∧
      (Sum.inl (second m) : Vertex m ⊕ Fin 1) ≠ Sum.inr 0 ∧
      (Sum.inl (first m) : Vertex m ⊕ Fin 1) ≠ Sum.inr 0
    exact ⟨fun h => ih.1 (Sum.inl_injective h).symm,Sum.inl_ne_inr,Sum.inl_ne_inr⟩

def function : (m : ℕ) → SetFunction (Vertex m)
  | 0 => DiamondGeometry.function
  | m+1 => append (function m) (andOr (first m) (second m) (tip m))

theorem vertex_card (m : ℕ) : Fintype.card (Vertex m) = 10+m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change Fintype.card (Vertex m ⊕ Fin 1) = _
    rw [Fintype.card_sum,Fintype.card_fin,ih]
    omega

/-- The seed boundary is verified from the literal 57-clique polynomial,
using no private-kernel or rigidity premise. -/
theorem base_unit_boundary : UnitBoundary DiamondGeometry.function (0 : Fin 10) 1 6 := by
  refine ⟨by decide,by decide,by decide,?_⟩
  intro S h0 h6 h1
  rw [DiamondGeometry.delta_eq_slackZ (by decide) h0 h6]
  by_cases h2 : (2 : Fin 10) ∈ S <;>
    norm_num [DiamondGeometry.slackZ,DiamondGeometry.cliques,DiamondGeometry.coefficientsZ,
      Fin.sum_univ_succ,Finset.subset_iff,h0,h6,h1,h2]

theorem extreme_and_boundary (m : ℕ) :
    ExtremeSupermodular (function m) ∧ UnitBoundary (function m) (first m) (second m) (tip m) := by
  induction m with
  | zero => exact ⟨DiamondGeometry.extreme,base_unit_boundary⟩
  | succ m ih =>
    exact ⟨triangular_append_extreme ih.1 ih.2,triangular_append_boundary ih.2⟩

theorem extreme (m : ℕ) : ExtremeSupermodular (function m) := (extreme_and_boundary m).1
theorem unit_boundary (m : ℕ) : UnitBoundary (function m) (first m) (second m) (tip m) :=
  (extreme_and_boundary m).2

theorem frame_card (m : ℕ) : ({first m,second m,tip m} : Finset (Vertex m)).card = 3 := by
  have h := frame_distinct m
  simp [h.1,h.2.1,h.2.2]

theorem frame_clique (m : ℕ) : (graph m).IsClique ({first m,second m,tip m} : Finset (Vertex m)) := by
  induction m with
  | zero =>
    change DiamondGeometry.graph.IsClique ({0,1,6} : Finset (Fin 10))
    decide +kernel
  | succ m ih => exact triangular_append_triangle (unit_boundary m).1 ih

theorem graphical (m : ℕ) : Graphical (graph m) (function m) := by
  induction m with
  | zero => exact DiamondGeometry.graphical
  | succ m ih => exact triangular_append_graphical ih (frame_clique m)

theorem integerValued (m : ℕ) : IntegerValued (function m) := by
  induction m with
  | zero => exact DiamondGeometry.integerValued
  | succ m ih => exact append_integerValued ih (andOr_boolean _ _ _)

theorem elemental_upper (m : ℕ) :
    ∀ u v : Vertex m, u ≠ v → ∀ S, u ∉ S → v ∉ S →
      delta (function m) u v S ≤ (m+4 : ℕ) := by
  induction m with
  | zero =>
    intro u v huv S hu hv
    exact (DiamondGeometry.elemental_bounds huv hu hv).2
  | succ m ih =>
    have h := append_delta_upper (andOr_boolean (first m) (second m) (tip m))
      (Nat.cast_nonneg (m+4)) ih
    intro u v huv S hu hv
    have he : ((m+4 : ℕ) : ℝ)+1 = ((m+1+4 : ℕ) : ℝ) := by
      norm_num [Nat.cast_add] <;> ring
    simpa only [function,he] using h u v huv S hu hv

theorem positive_slack (m : ℕ) :
    ∀ u v : Vertex m, (graph m).Adj u v → ∃ S : Finset (Vertex m),
      u ∉ S ∧ v ∉ S ∧ 0 < delta (function m) u v S := by
  induction m with
  | zero => exact fun _ _ h => DiamondGeometry.positive_slack h
  | succ m ih => exact triangular_append_positive (unit_boundary m) ih

theorem connected (m : ℕ) : (graph m).Connected := by
  induction m with
  | zero => exact DiamondGeometry.graph_connected
  | succ m ih => exact SingleVertexGraph.connected ih ⟨first m,by simp⟩

theorem cliqueFree_five (m : ℕ) : (graph m).CliqueFree 5 := by
  induction m with
  | zero =>
    change DiamondGeometry.graph.CliqueFree 5
    intro C hC
    have hc : C.card = 5 := hC.card_eq
    obtain ⟨i,hi⟩ := DiamondGeometry.cliques_complete C ⟨by omega,hC.isClique⟩
    have hfour : ∀ i : Fin 57, (DiamondGeometry.cliques i).card ≤ 4 := by decide +kernel
    have hle := hfour i
    rw [hi] at hle
    omega
  | succ m ih =>
    exact SingleVertexGraph.cliqueFree_five ih
      (by simpa only [frame_card] using (show 3 ≤ 3 from le_rfl))

theorem edge_count (m : ℕ) : (edgeFamily (graph m)).card = 25+3*m := by
  induction m with
  | zero =>
    rw [graph,DiamondGeometry.edge_family_eq]
    decide +kernel
  | succ m ih =>
    rw [graph,SingleVertexGraph.edgeFamily_card,ih,frame_card]
    omega

theorem actual_summand (m : ℕ) : IsMinkowskiSummand (basePolytope (function m))
    (((m+4 : ℕ) : ℝ) • graphicalZonotope (graph m)) := by
  apply (isMinkowskiSummand_graphical_iff (extreme m).1.1 (extreme m).2.1
    (Nat.cast_nonneg (m+4))).mpr
  exact ⟨graphical m,fun u v huv _ S hu hv => elemental_upper m u v huv S hu hv⟩

theorem full_dimension (m : ℕ) : FullDimension (basePolytope (function m)) := by
  exact finrank_vectorSpan_eq_of_connected_slacks (extreme m).1.1 (extreme m).2.1
    (connected m) (fun u v huv => by
      obtain ⟨S,hu,hv,hp⟩ := positive_slack m u v huv
      exact ⟨S,hu,hv,ne_of_gt hp⟩)

theorem actual_direction_graph (m : ℕ) :
    actualDirectionGraph (basePolytope (function m)) = graph m := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  constructor
  · intro he
    obtain ⟨R,hR,hRc,hnR,hQR⟩ := actual_summand m
    exact basePolytope_summand_actualRootEdge (extreme m).1.1 (extreme m).2.1 (graph m)
      (Nat.cast_nonneg (m+4)) R hQR he
  · intro he
    obtain ⟨S,hu,hv,hp⟩ := positive_slack m u v he
    exact exposedSegment_of_positive_delta (extreme m).1.1 (extreme m).2.1 he.ne hu hv hp

theorem lattice (m : ℕ) : LatticePolytope (basePolytope (function m)) :=
  (integerValued m).basePolytope (extreme m).1.1 (extreme m).2.1

end SparseFamily
end GraphicalZonotopes

end
end
end BundlePart337

section BundlePart338
/- Source: Papers/GraphicalZonotopes/TreewidthLowDegree.lean -/




/-! # A degree consequence of an ordinary tree decomposition

The proof prunes redundant leaf bags. A vertex exclusive to a leaf bag has
all its neighbors in that bag. This is the standard degeneracy consequence
of bounded treewidth, with the full connected-occurrence condition used.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem tree_bags_have_low_degree [Nonempty V] (G : SimpleGraph V) (w : ℕ)
    {I : Type} [Fintype I] [DecidableEq I] (T : SimpleGraph I) (bag : I → Finset V)
    (hT : T.IsTree) (hsize : ∀ i, (bag i).card ≤ w+1)
    (hcover : ∀ v, ∃ i, v ∈ bag i)
    (hedge : ∀ u v, G.Adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i)
    (hconn : ∀ v, (T.induce {i | v ∈ bag i}).Connected) :
    ∃ v : V, G.degree v ≤ w := by
  classical
  have single (I : Type) [Fintype I] [DecidableEq I] (bag : I → Finset V)
      (hs : ∀ i, (bag i).card ≤ w+1)
      (he : ∀ u v, G.Adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i)
      (r : I) (v : V) (hv : v ∈ bag r)
      (honly : ∀ i, v ∈ bag i → i = r) : ∃ v : V, G.degree v ≤ w := by
    refine ⟨v,?_⟩
    have hsub : G.neighborFinset v ⊆ (bag r).erase v := by
      intro u hu
      have hAdj := (G.mem_neighborFinset v u).mp hu
      obtain ⟨i,hvi,hui⟩ := he v u hAdj
      have hir := honly i hvi
      subst i
      exact mem_erase.mpr ⟨hAdj.ne.symm,hui⟩
    have hc := card_le_card hsub
    rw [SimpleGraph.card_neighborFinset_eq_degree,card_erase_of_mem hv] at hc
    have hb := hs r
    omega
  suffices aux : ∀ n : ℕ, ∀ (J : Type) [Fintype J] [DecidableEq J],
      Fintype.card J = n → ∀ (H : SimpleGraph J) (b : J → Finset V),
      H.IsTree → (∀ i, (b i).card ≤ w+1) →
      (∀ v, ∃ i, v ∈ b i) →
      (∀ u v, G.Adj u v → ∃ i, u ∈ b i ∧ v ∈ b i) →
      (∀ v, (H.induce {i | v ∈ b i}).Connected) → ∃ v : V, G.degree v ≤ w from
    aux _ I rfl T bag hT hsize hcover hedge hconn
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro J _ _ hcard H b htree hs hc he hcon
    by_cases hsub : Subsingleton J
    · letI : Subsingleton J := hsub
      obtain ⟨r⟩ := htree.connected.nonempty
      let v : V := Classical.choice inferInstance
      have hv : v ∈ b r := by
        obtain ⟨i,hi⟩ := hc v
        simpa only [Subsingleton.elim i r] using hi
      exact single J b hs he r v hv (fun i _ => Subsingleton.elim _ _)
    · letI : Nontrivial J := not_subsingleton_iff_nontrivial.mp hsub
      obtain ⟨r,hrdeg⟩ := htree.exists_vert_degree_one_of_nontrivial
      obtain ⟨q,hrq,hqonly⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hrdeg
      have hqr : q ≠ r := hrq.ne.symm
      by_cases hleaf : b r ⊆ b q
      · let J' := {i : J // i ≠ r}
        let H' : SimpleGraph J' := H.induce {r}ᶜ
        let b' : J' → Finset V := fun i => b i.1
        have htree' : H'.IsTree :=
          ⟨htree.connected.induce_compl_singleton_of_degree_eq_one hrdeg,
            htree.isAcyclic.induce _⟩
        have hc' : ∀ v, ∃ i : J', v ∈ b' i := by
          intro v
          obtain ⟨i,hi⟩ := hc v
          by_cases hir : i = r
          · subst i
            exact ⟨⟨q,hqr⟩,hleaf hi⟩
          · exact ⟨⟨i,hir⟩,hi⟩
        have he' : ∀ u v, G.Adj u v → ∃ i : J', u ∈ b' i ∧ v ∈ b' i := by
          intro u v huv
          obtain ⟨i,hu,hv⟩ := he u v huv
          by_cases hir : i = r
          · subst i
            exact ⟨⟨q,hqr⟩,hleaf hu,hleaf hv⟩
          · exact ⟨⟨i,hir⟩,hu,hv⟩
        have hcon' : ∀ v, (H'.induce {i | v ∈ b' i}).Connected := by
          intro v
          let K := H.induce {i | v ∈ b i}
          let S : Set {i : J // v ∈ b i} := {i | i.1 ≠ r}
          have hpre : (K.induce S).Preconnected := by
            apply (hcon v).preconnected.induce_of_degree_eq_one
            intro i hi
            have hir : i.1 = r := by
              by_contra hne
              exact hi hne
            intro j hj k hk
            apply Subtype.ext
            have hj' : H.Adj i.1 j.1 := hj
            have hk' : H.Adj i.1 k.1 := hk
            have hjq : j.1 = q := hqonly j.1 (by simpa only [hir] using hj')
            have hkq : k.1 = q := hqonly k.1 (by simpa only [hir] using hk')
            exact hjq.trans hkq.symm
          let e : (H'.induce {i | v ∈ b' i}) ≃g (K.induce S) :=
            { toFun := fun i => ⟨⟨i.1.1,i.2⟩,i.1.2⟩
              invFun := fun i => ⟨⟨i.1.1,i.2⟩,i.1.2⟩
              left_inv := by intro i; rfl
              right_inv := by intro i; rfl
              map_rel_iff' := by intro i j; rfl }
          have hpre' := e.preconnected_iff.mpr hpre
          obtain ⟨i,hi⟩ := hc' v
          letI : Nonempty ({i : J' | v ∈ b' i} : Set J') := ⟨⟨i,hi⟩⟩
          exact ⟨hpre'⟩
        have hlt : Fintype.card J' < n := by
          rw [← hcard]
          exact Fintype.card_subtype_lt (x := r) (by simp)
        exact ih _ hlt J' rfl H' b' htree' (fun i => hs i.1) hc' he' hcon'
      · obtain ⟨v,hvr,hvq⟩ := not_subset.mp hleaf
        apply single J b hs he r v hvr
        intro i hvi
        by_contra hir
        let r' : {i : J // v ∈ b i} := ⟨r,hvr⟩
        let i' : {i : J // v ∈ b i} := ⟨i,hvi⟩
        have hri : r' ≠ i' := fun hh => hir (congrArg Subtype.val hh).symm
        obtain ⟨j,hj⟩ := ((hcon v) r' i').nonempty_neighborSet_left hri
        have hjq : j.1 = q := hqonly j.1 hj
        exact hvq (hjq ▸ j.2)

theorem HasTreewidthAtMost.exists_degree_le {G : SimpleGraph V} [Nonempty V] {w : ℕ}
    (h : HasTreewidthAtMost G w) : ∃ v : V, G.degree v ≤ w := by
  obtain ⟨m,T,bag,hT,hs,hc,he,hcon⟩ := h
  exact tree_bags_have_low_degree G w T bag hT hs hc he hcon

end GraphicalZonotopes

end
end
end BundlePart338

section BundlePart339
/- Source: Papers/GraphicalZonotopes/TreewidthOperations.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset BooleanModule BooleanVertexExtension
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Relabeling graph vertices preserves the number of unordered edges.
No order on the vertex types is needed. -/
theorem edgeFamily_card_map (e : V ↪ W) (G : SimpleGraph V) :
    (edgeFamily (G.map e)).card = (edgeFamily G).card := by
  classical
  rw [edgeFamily_eq_image_edgeFinset,
    card_image_of_injective _ sym2_toFinset_injective,
    edgeFamily_eq_image_edgeFinset,
    card_image_of_injective _ sym2_toFinset_injective]
  simpa only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] using
    SimpleGraph.card_edgeFinset_map e G

theorem HasTreewidthAtMost.comap {G : SimpleGraph V} {w : ℕ}
    (h : HasTreewidthAtMost G w) (e : W ↪ V) : HasTreewidthAtMost (G.comap e) w := by
  obtain ⟨m,T,bag,hT,hs,hc,he,hcon⟩ := h
  let b : Fin m → Finset W := fun i => SetFunctionEmbedding.pullSet e (bag i)
  refine ⟨m,T,b,hT,?_,?_,?_,?_⟩
  · intro i
    have hsub : (b i).map e ⊆ bag i := by
      intro v hv
      obtain ⟨u,hu,rfl⟩ := mem_map.mp hv
      exact (SetFunctionEmbedding.mem_pullSet e _ _).mp hu
    have hcard := card_le_card hsub
    rw [card_map] at hcard
    exact hcard.trans (hs i)
  · intro v
    obtain ⟨i,hi⟩ := hc (e v)
    exact ⟨i,(SetFunctionEmbedding.mem_pullSet e _ _).mpr hi⟩
  · intro u v huv
    obtain ⟨i,hu,hv⟩ := he (e u) (e v) huv
    exact ⟨i,(SetFunctionEmbedding.mem_pullSet e _ _).mpr hu,
      (SetFunctionEmbedding.mem_pullSet e _ _).mpr hv⟩
  · intro v
    have hsets : {i | v ∈ b i} = {i | e v ∈ bag i} := by
      ext i
      exact SetFunctionEmbedding.mem_pullSet e _ _
    rw [hsets]
    exact hcon (e v)

/-- A finite tree decomposition with one specified bag containing the
displayed boundary. The index type is only presentation data. -/
structure RootedTreeDecomposition (G : SimpleGraph V) (w : ℕ) (B : Finset V) where
  Index : Type
  [indexFintype : Fintype Index]
  [indexDecidableEq : DecidableEq Index]
  tree : SimpleGraph Index
  bag : Index → Finset V
  root : Index
  isTree : tree.IsTree
  size : ∀ i, (bag i).card ≤ w+1
  cover : ∀ v, ∃ i, v ∈ bag i
  edge : ∀ u v, G.Adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i
  occurrence : ∀ v, (tree.induce {i | v ∈ bag i}).Connected
  boundary : B ⊆ bag root

attribute [instance] RootedTreeDecomposition.indexFintype RootedTreeDecomposition.indexDecidableEq

theorem RootedTreeDecomposition.hasTreewidthAtMost {G : SimpleGraph V} {w : ℕ}
    {B : Finset V} (d : RootedTreeDecomposition G w B) : HasTreewidthAtMost G w := by
  let e := Fintype.equivFin d.Index
  let T : SimpleGraph (Fin (Fintype.card d.Index)) := d.tree.comap e.symm
  let bag : Fin (Fintype.card d.Index) → Finset V := fun i => d.bag (e.symm i)
  let iso : T ≃g d.tree := { e.symm with map_rel_iff' := by intros; rfl }
  refine ⟨Fintype.card d.Index,T,bag,iso.isTree_iff.mpr d.isTree,
    fun i => d.size (e.symm i),?_,?_,?_⟩
  · intro v
    obtain ⟨i,hi⟩ := d.cover v
    exact ⟨e i,by simpa only [bag,Equiv.symm_apply_apply] using hi⟩
  · intro u v huv
    obtain ⟨i,hu,hv⟩ := d.edge u v huv
    exact ⟨e i,by simpa only [bag,Equiv.symm_apply_apply] using hu,
      by simpa only [bag,Equiv.symm_apply_apply] using hv⟩
  · intro v
    let e' : (T.induce {i | v ∈ bag i}) ≃g (d.tree.induce {i | v ∈ d.bag i}) :=
      { toFun := fun i => ⟨e.symm i.1,i.2⟩
        invFun := fun i => ⟨e i.1,by
          change v ∈ d.bag (e.symm (e i.1))
          simpa only [Equiv.symm_apply_apply] using (show v ∈ d.bag i.1 from i.2)⟩
        left_inv := by intro i; apply Subtype.ext; simp
        right_inv := by intro i; apply Subtype.ext; simp
        map_rel_iff' := by intros; rfl }
    exact e'.connected_iff.mpr (d.occurrence v)

def RootedTreeDecomposition.restrictBoundary {G : SimpleGraph V} {w : ℕ}
    {B C : Finset V} (d : RootedTreeDecomposition G w B) (h : C ⊆ B) :
    RootedTreeDecomposition G w C := { d with boundary := h.trans d.boundary }

theorem edgeFamily_card_eq_edgeFinset_card (G : SimpleGraph V) :
    (edgeFamily G).card = G.edgeFinset.card := by
  rw [edgeFamily_eq_image_edgeFinset,card_image_of_injective _ sym2_toFinset_injective]

theorem SingleVertexGraph.isTree_singleton {G : SimpleGraph V} (hG : G.IsTree) (r : V) :
    (SingleVertexGraph.graph G {r}).IsTree := by
  apply (SimpleGraph.isTree_iff_connected_and_card).mpr
  refine ⟨SingleVertexGraph.connected hG.connected (singleton_nonempty _),?_⟩
  simp only [Nat.card_eq_fintype_card,Fintype.card_sum,Fintype.card_fin]
  rw [← SimpleGraph.edgeFinset_card,← edgeFamily_card_eq_edgeFinset_card,
    SingleVertexGraph.edgeFamily_card,card_singleton,edgeFamily_card_eq_edgeFinset_card,
    hG.card_edgeFinset]

/-- Appending a leaf bag proves the ordinary width bound after attaching a
new graph vertex to vertices already sharing the specified boundary bag. -/
def RootedTreeDecomposition.append {G : SimpleGraph V} {w : ℕ} {B : Finset V}
    (d : RootedTreeDecomposition G w B) (hB : B.card ≤ w) :
    RootedTreeDecomposition (SingleVertexGraph.graph G B) w
      (insert (Sum.inr 0) (hubSet (J := Fin 1) B)) := by
  let I := d.Index
  let T : SimpleGraph (BooleanVertexExtension.Vertex I) :=
    SingleVertexGraph.graph d.tree {d.root}
  let bag : BooleanVertexExtension.Vertex I → Finset (BooleanVertexExtension.Vertex V)
    | Sum.inl i => hubSet (d.bag i)
    | Sum.inr _ => insert (Sum.inr 0) (hubSet B)
  refine {
    Index := BooleanVertexExtension.Vertex I
    tree := T
    bag := bag
    root := Sum.inr 0
    isTree := SingleVertexGraph.isTree_singleton d.isTree d.root
    size := ?_
    cover := ?_
    edge := ?_
    occurrence := ?_
    boundary := Subset.rfl }
  · intro i
    cases i with
    | inl i => simpa only [bag,hubSet,card_map] using d.size i
    | inr j =>
      change (insert (Sum.inr 0) (hubSet (J := Fin 1) B)).card ≤ w+1
      rw [card_insert_of_notMem (notMem_hubSet_outer B (0 : Fin 1)),hubSet,card_map]
      omega
  · intro v
    cases v with
    | inl v =>
      obtain ⟨i,hi⟩ := d.cover v
      exact ⟨Sum.inl i,by simpa only [bag,mem_hubSet_hub] using hi⟩
    | inr j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact ⟨Sum.inr 0,mem_insert_self _ _⟩
  · intro u v huv
    cases u with
    | inl u =>
      cases v with
      | inl v =>
        obtain ⟨i,hu,hv⟩ := d.edge u v huv
        exact ⟨Sum.inl i,by simpa only [bag,mem_hubSet_hub] using hu,
          by simpa only [bag,mem_hubSet_hub] using hv⟩
      | inr j =>
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        change u ∈ B at huv
        exact ⟨Sum.inr 0,by simpa only [bag,mem_insert,Sum.inl_ne_inr,false_or,
          mem_hubSet_hub] using huv,mem_insert_self _ _⟩
    | inr i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      cases v with
      | inl v =>
        change v ∈ B at huv
        exact ⟨Sum.inr 0,mem_insert_self _ _,by simpa only [bag,mem_insert,
          Sum.inl_ne_inr,false_or,mem_hubSet_hub] using huv⟩
      | inr j => exact False.elim huv
  · intro v
    cases v with
    | inl v =>
      let f : (d.tree.induce {i | v ∈ d.bag i}) →g (T.induce {i | Sum.inl v ∈ bag i}) :=
        { toFun := fun i => ⟨Sum.inl i.1,by
            change Sum.inl v ∈ hubSet (J := Fin 1) (d.bag i.1)
            exact (mem_hubSet_hub _ _).mpr i.2⟩
          map_rel' := by intro i j hij; exact hij }
      obtain ⟨i,hi⟩ := d.cover v
      apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
      refine ⟨f ⟨i,hi⟩,?_⟩
      intro j
      rcases j with ⟨j,hj⟩
      cases j with
      | inl k =>
        have hk : v ∈ d.bag k := by
          change Sum.inl v ∈ hubSet (J := Fin 1) (d.bag k) at hj
          exact (mem_hubSet_hub _ _).mp hj
        exact ((d.occurrence v) ⟨i,hi⟩ ⟨k,hk⟩).map f
      | inr k =>
        have hk : k = 0 := Subsingleton.elim _ _
        subst k
        have hvB : v ∈ B := by
          change Sum.inl v ∈ insert (Sum.inr 0) (hubSet (J := Fin 1) B) at hj
          simpa only [mem_insert,Sum.inl_ne_inr,false_or,mem_hubSet_hub] using hj
        have hvr : v ∈ d.bag d.root := d.boundary hvB
        refine (((d.occurrence v) ⟨i,hi⟩ ⟨d.root,hvr⟩).map f).trans ?_
        apply SimpleGraph.Adj.reachable
        exact mem_singleton_self _
    | inr v =>
      have hv : v = 0 := Subsingleton.elim _ _
      subst v
      apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
      refine ⟨⟨Sum.inr 0,mem_insert_self _ _⟩,?_⟩
      rintro ⟨i,hi⟩
      cases i with
      | inl i =>
        change Sum.inr (0 : Fin 1) ∈ hubSet (d.bag i) at hi
        exact False.elim (notMem_hubSet_outer _ _ hi)
      | inr i =>
        have hi0 : i = 0 := Subsingleton.elim _ _
        subst i
        exact SimpleGraph.Reachable.rfl

end GraphicalZonotopes

end
end
end BundlePart339

section BundlePart340
/- Source: Papers/GraphicalZonotopes/SparseFamilyTreewidth.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.SparseFamily
open Finset BooleanModule

def baseBags : Fin 6 → Finset (Fin 10) :=
  ![{0,1,2,3,4},{0,1,2,3,5},{0,1,2,3,6},
    {0,1,2,3,7},{0,1,2,3,8},{0,1,2,3,9}]

theorem baseBag_occurrence (v : Fin 10) :
    {i : Fin 6 | v ∈ baseBags i} = Set.univ ∨
      ∃ j : Fin 6, {i : Fin 6 | v ∈ baseBags i} = {j} := by
  fin_cases v
  · left; ext i; fin_cases i <;> simp [baseBags]
  · left; ext i; fin_cases i <;> simp [baseBags]
  · left; ext i; fin_cases i <;> simp [baseBags]
  · left; ext i; fin_cases i <;> simp [baseBags]
  · right; refine ⟨0,?_⟩; ext i; fin_cases i <;> simp [baseBags]
  · right; refine ⟨1,?_⟩; ext i; fin_cases i <;> simp [baseBags]
  · right; refine ⟨2,?_⟩; ext i; fin_cases i <;> simp [baseBags]
  · right; refine ⟨3,?_⟩; ext i; fin_cases i <;> simp [baseBags]
  · right; refine ⟨4,?_⟩; ext i; fin_cases i <;> simp [baseBags]
  · right; refine ⟨5,?_⟩; ext i; fin_cases i <;> simp [baseBags]

def base_decomposition : RootedTreeDecomposition DiamondGeometry.graph 4 ({0,1,6} : Finset (Fin 10)) where
  Index := Fin 6
  tree := SimpleGraph.pathGraph 6
  bag := baseBags
  root := 2
  isTree := SimpleGraph.isTree_pathGraph_add_one 5
  size := by decide +kernel
  cover := by decide +kernel
  edge := by decide +kernel
  occurrence := by
    intro v
    rcases baseBag_occurrence v with h | ⟨i,h⟩
    · rw [h]
      exact (SimpleGraph.induceUnivIso _).connected_iff.mpr
        (SimpleGraph.connected_pathGraph_add_one 5)
    · rw [h,SimpleGraph.induce_singleton_eq_top]
      letI : Nonempty ({i} : Set (Fin 6)) := ⟨⟨i,by simp⟩⟩
      exact SimpleGraph.connected_top
  boundary := by decide +kernel

def rooted_decomposition : (m : ℕ) →
    RootedTreeDecomposition (graph m) 4 ({first m,second m,tip m} : Finset (Vertex m))
  | 0 => base_decomposition
  | m+1 =>
    ((rooted_decomposition m).append (by rw [frame_card]; omega)).restrictBoundary (by
      intro x hx
      simp only [frame,first,second,tip,mem_insert,mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> simp)

theorem width_at_most_four (m : ℕ) : HasTreewidthAtMost (graph m) 4 :=
  (rooted_decomposition m).hasTreewidthAtMost

def coreEmbedding : Fin 6 ↪ Fin 10 where
  toFun := ![0,1,2,3,8,9]
  inj' := by decide +kernel

def coreGraph : SimpleGraph (Fin 6) := DiamondGeometry.graph.comap coreEmbedding

instance coreGraphDecidable : DecidableRel coreGraph.Adj := by
  unfold coreGraph
  infer_instance

/-- The induced six-vertex `K₂ * C₄` core has minimum degree four. -/
theorem core_minimum_degree : ∀ v : Fin 6, 4 ≤ coreGraph.degree v := by
  decide +kernel

theorem base_not_width_three : ¬HasTreewidthAtMost DiamondGeometry.graph 3 := by
  intro h
  have hc : HasTreewidthAtMost coreGraph 3 := h.comap coreEmbedding
  obtain ⟨v,hv⟩ := hc.exists_degree_le
  have hm := core_minimum_degree v
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hv hm
  omega

def baseEmbedding : (m : ℕ) → Fin 10 ↪ Vertex m
  | 0 => Function.Embedding.refl _
  | m+1 => (baseEmbedding m).trans SingleVertexGraph.old

theorem graph_comap_base (m : ℕ) : (graph m).comap (baseEmbedding m) = DiamondGeometry.graph := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have he : (graph (m+1)).comap (baseEmbedding (m+1)) = (graph m).comap (baseEmbedding m) := rfl
    exact he.trans ih

theorem not_width_three (m : ℕ) : ¬HasTreewidthAtMost (graph m) 3 := by
  intro h
  have hb := h.comap (baseEmbedding m)
  rw [graph_comap_base] at hb
  exact base_not_width_three hb

end GraphicalZonotopes.SparseFamily

end
end
end BundlePart340

section BundlePart341
/- Source: Papers/GraphicalZonotopes/ThreeTreePruneExtension.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace SingleVertexGraph
open Finset BooleanModule BooleanVertexExtension SetFunctionEmbedding
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem all_vertices_eq_insert :
    (univ : Finset (BooleanVertexExtension.Vertex V)) =
      insert (Sum.inr 0) (hubSet (J := Fin 1) (univ : Finset V)) := by
  ext x
  cases x with
  | inl v => simp
  | inr j =>
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simp

/-- A spanning admissible three-tree survives deleting a newly attached
vertex with at most three available neighbors. The proof uses exact edge
counts on arbitrary induced subsets, so no construction order is assumed. -/
theorem admissible_spanning_prune {G : SimpleGraph V} {N : Finset V}
    (hV : 4 ≤ Fintype.card V) (hN : N.card ≤ 3)
    (h : HasAdmissibleSpanningThreeTree (graph G N)) :
    HasAdmissibleSpanningThreeTree G := by
  obtain ⟨H,hHG,hH,hA⟩ := h
  let C : Finset (BooleanVertexExtension.Vertex V) := hubSet (univ : Finset V)
  have hC : C.card = Fintype.card V := by simp [C,hubSet]
  have hw : Sum.inr 0 ∉ C := notMem_hubSet_outer _ _
  have hsize : (edgeFamily H).card = 3*(Fintype.card V+1)-6 := by
    simpa only [card_univ,Fintype.card_sum,Fintype.card_fin] using hH.edgeFamily_card
  have hnb : earlierNeighbors H C (Sum.inr 0) ⊆ hubSet (J := Fin 1) N := by
    intro x hx
    obtain ⟨hxC,hwx⟩ := (mem_earlierNeighbors _ _ _ _).mp hx
    cases x with
    | inl v =>
      exact (mem_hubSet_hub _ _).mpr (hHG hwx)
    | inr j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact False.elim (hw hxC)
  have hnb3 : (earlierNeighbors H C (Sum.inr 0)).card ≤ 3 := by
    have hh := card_le_card hnb
    simp only [hubSet,card_map] at hh
    exact hh.trans hN
  have hsplit : (edgeFamily H).card = (edgeFamily (inducedOn H C)).card +
      (earlierNeighbors H C (Sum.inr 0)).card := by
    have hh := induced_edge_count_insert H C (Sum.inr 0) hw
    have hu : insert (Sum.inr 0) C = univ := all_vertices_eq_insert.symm
    rw [hu,inducedOn_univ] at hh
    exact hh
  have hbound := hH.induced_edge_bound C (subset_univ C) (by omega)
  have he : (edgeFamily (inducedOn H C)).card = 3*C.card-6 := by omega
  have hp : ThreeTreeOn C (inducedOn H C) :=
    hH.induced_equality C (subset_univ C) (by omega) he
  have hrange : ∀ x ∈ C, x ∈ Set.range (old : V ↪ BooleanVertexExtension.Vertex V) := by
    intro x hx
    obtain ⟨v,hv,hvx⟩ := mem_map.mp hx
    exact ⟨v,hvx⟩
  have hcomap : (inducedOn H C).comap old = H.comap old := by
    ext u v
    change (H.Adj (Sum.inl u) (Sum.inl v) ∧ Sum.inl u ∈ C ∧ Sum.inl v ∈ C) ↔ _
    simp [C,old]
  have hset : pullSet old C = univ := by
    ext v
    simp [C,old]
  have htOld : IsThreeTree (H.comap old) := by
    have ht := hp.comap old hrange
    rw [hcomap,hset] at ht
    exact ht
  have hAP : Admissible (inducedOn H C) := by
    intro T hT hcl
    exact (triangleMultiplicity_mono (inducedOn_le H C) T).trans
      (hA T hT (fun u hu v hv huv => (hcl hu hv huv).1))
  have hmap : ((inducedOn H C).comap old).map old = inducedOn H C :=
    map_comap_of_supported old _ (fun u v huv => hrange u huv.2.1)
  have hAO : Admissible (H.comap old) := by
    have hh := Admissible.of_map old (G := (inducedOn H C).comap old) (by rwa [hmap])
    rwa [hcomap] at hh
  exact ⟨H.comap old,fun u v huv => hHG huv,htOld,hAO⟩

end SingleVertexGraph
end GraphicalZonotopes

end
end
end BundlePart341

section BundlePart342
/- Source: Papers/GraphicalZonotopes/SparseFamilyMinimality.lean -/








@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset

namespace SparseFamily

theorem no_admissible_spanning (m : ℕ) : ¬HasAdmissibleSpanningThreeTree (graph m) := by
  induction m with
  | zero =>
    rintro ⟨H,hHG,hH,hA⟩
    exact DiamondBook.no_admissible_spanning_threeTree 6 (by omega)
      ⟨H,hHG.trans DiamondBook.diamond_support_subgraph,hH,hA⟩
  | succ m ih =>
    intro h
    apply ih
    exact SingleVertexGraph.admissible_spanning_prune
      (by rw [vertex_card]; omega)
      (by simpa only [frame_card] using (show 3 ≤ 3 from le_rfl)) h

end SparseFamily

/-- One edge above the absolute lower bound, the absence of an admissible
spanning three-tree makes every actual supporting edge indispensable. -/
theorem edgeMinimalSupporting_of_one_excess {n : ℕ} (hn : 4 ≤ n)
    {G : SimpleGraph (Fin n)} (hc : (edgeFamily G).card = 3*n-5)
    (hno : ¬HasAdmissibleSpanningThreeTree G) (hs : SupportsFullIndecomposable G) :
    EdgeMinimalSupporting G := by
  refine ⟨hs,?_⟩
  intro H hHG hsupport
  obtain ⟨Q,hQ,hi,hd,hw⟩ := hsupport
  obtain ⟨z,hzs,hze,hzd⟩ := weak_summand_extreme_or_zero hQ hi hw
  have hfull : Module.finrank ℝ (vectorSpan ℝ (basePolytope z.1)) = n-1 := by
    rw [← hzd]
    simpa only [FullDimension,Fintype.card_fin] using hd
  have hz : ExtremeSupermodular z.1 := by
    rcases hze with hzero | he
    · rw [hzero,basePolytope_zero,_root_.vectorSpan_singleton,_root_.finrank_bot] at hfull
      omega
    · exact he
  let A := actualDirectionGraph (basePolytope z.1)
  have hAH : A ≤ H := fun u v huv =>
    RefinedTriangleComponents.actualRootEdge_of_graphical hz.1.1 hz.2.1 z.2.2 huv
  have hstrict : edgeFamily H ⊂ edgeFamily G := by
    apply ssubset_iff_subset_ne.mpr
    refine ⟨edgeFamily_mono hHG.le,?_⟩
    intro he
    exact hHG.ne (graph_eq_of_edgeFamily_eq he)
  have hHcount := card_lt_card hstrict
  have hAcount := card_le_card (edgeFamily_mono hAH)
  obtain ⟨hlower,heq⟩ := hz.direction_count_bound hn hfull
  have he : directionCount (basePolytope z.1) = 3*n-6 := by
    change 3*n-6 ≤ (edgeFamily A).card at hlower
    change (edgeFamily A).card = _
    omega
  have htree : IsThreeTree A := heq he
  have hsA : SupportsFullIndecomposable A := by
    refine ⟨basePolytope z.1,?_,hz.minkowskiIndecomposable,?_,?_⟩
    · exact (show IsGeneralizedPermutahedron (basePolytope z.1) from
        ⟨z.1,hz.1.1,hz.2.1,rfl⟩).finitePolytope
    · simpa only [FullDimension,Fintype.card_fin] using hfull
    · exact (isWeakMinkowskiSummand_graphical_iff hz.1.1 hz.2.1).mpr
        (graphical_actualDirectionGraph hz.1.1 hz.2.1)
  have hA := (threeTree_supports_iff_admissible hn htree).mp hsA
  exact hno ⟨A,hAH.trans hHG.le,htree,hA⟩

end GraphicalZonotopes

end
end
end BundlePart342

section BundlePart343
/- Source: Papers/GraphicalZonotopes/SparseFamilyPrincipal.lean -/







/-! # Theorem 8.2 in its complete geometric form

Every order `n ≥ 10` has a genuine graph of treewidth exactly four and a
full-dimensional lattice indecomposable summand in the asserted dilation.
The actual exposed-root direction graph is proved equal to that graph, and
every proper edge-subgraph is excluded from supporting a full-dimensional ray.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.SparseFamily
open Finset SetFunctionEmbedding
open scoped BigOperators Pointwise

theorem complete_family (n : ℕ) (hn : 10 ≤ n) :
    ∃ G : SimpleGraph (Fin n), ∃ Q : Set (Fin n → ℝ),
      G.CliqueFree 5 ∧ (edgeFamily G).card = 3*n-5 ∧
      HasTreewidthAtMost G 4 ∧ ¬HasTreewidthAtMost G 3 ∧
      EdgeMinimalSupporting G ∧ LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      FullDimension Q ∧ actualDirectionGraph Q = G ∧
      IsMinkowskiSummand Q (((n-6 : ℕ) : ℝ) • graphicalZonotope G) ∧
      ¬∃ H : SimpleGraph (Fin n), H ≤ G ∧ IsThreeTree H ∧ SupportsFullIndecomposable H := by
  let m := n-10
  have hcard : Fintype.card (Vertex m) = n := by rw [vertex_card]; dsimp [m]; omega
  letI : Nonempty (Vertex m) := (connected m).nonempty
  let e : Vertex m ≃ Fin n := Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using hcard)
  let G : SimpleGraph (Fin n) := (graph m).map e.toEmbedding
  let z : SetFunction (Fin n) := extend e.toEmbedding (function m)
  have hz : ExtremeSupermodular z := extend_extreme e.toEmbedding (extreme m)
  have hzi : IntegerValued z := extend_integer e.toEmbedding (integerValued m)
  have hzg : Graphical G z := by
    apply extend_graphical e.toEmbedding
    change Graphical (((graph m).map e.toEmbedding).comap e.toEmbedding) (function m)
    rw [SimpleGraph.comap_map_eq]
    exact graphical m
  have hM : m+4 = n-6 := by dsimp [m]; omega
  have hbound : ∀ u v : Fin n, u ≠ v → ∀ S, u ∉ S → v ∉ S → delta z u v S ≤ (n-6 : ℕ) := by
    intro u v huv S hu hv
    obtain ⟨a,rfl⟩ := e.surjective u
    obtain ⟨b,rfl⟩ := e.surjective v
    change delta (extend e.toEmbedding (function m)) (e.toEmbedding a) (e.toEmbedding b) S ≤ _
    rw [delta_extend e.toEmbedding (function m) a b S]
    simpa only [hM] using elemental_upper m a b (fun he => huv (congrArg e he))
      (pullSet e.toEmbedding S) (by simpa only [mem_pullSet,Equiv.toEmbedding_apply] using hu)
      (by simpa only [mem_pullSet,Equiv.toEmbedding_apply] using hv)
  have hsum : IsMinkowskiSummand (basePolytope z)
      (((n-6 : ℕ) : ℝ) • graphicalZonotope G) := by
    apply (isMinkowskiSummand_graphical_iff hz.1.1 hz.2.1 (Nat.cast_nonneg (n-6))).mpr
    exact ⟨hzg,fun u v huv _ S hu hv => hbound u v huv S hu hv⟩
  have hdim : FullDimension (basePolytope z) := by
    change Module.finrank ℝ (vectorSpan ℝ (basePolytope (extend e.toEmbedding (function m)))) = _
    rw [finrank_vectorSpan_extend e.toEmbedding (extreme m).1]
    have hd := full_dimension m
    change Module.finrank ℝ (vectorSpan ℝ (basePolytope (function m))) =
      Fintype.card (Vertex m)-1 at hd
    simpa only [hcard,Fintype.card_fin] using hd
  have hactual : actualDirectionGraph (basePolytope z) = G := by
    apply SimpleGraph.ext
    funext u v
    apply propext
    constructor
    · intro he
      obtain ⟨R,hR,hRc,hnR,hQR⟩ := hsum
      exact basePolytope_summand_actualRootEdge hz.1.1 hz.2.1 G
        (Nat.cast_nonneg (n-6)) R hQR he
    · intro he
      obtain ⟨a,b,hab,rfl,rfl⟩ := (SimpleGraph.map_adj e.toEmbedding (graph m) u v).mp he
      obtain ⟨S,ha,hb,hp⟩ := positive_slack m a b hab
      apply exposedSegment_of_positive_delta hz.1.1 hz.2.1
        (fun he => hab.ne (e.injective he)) (S := S.map e.toEmbedding)
        (by simpa using ha) (by simpa using hb)
      change 0 < delta (extend e.toEmbedding (function m))
        (e.toEmbedding a) (e.toEmbedding b) (S.map e.toEmbedding)
      rw [delta_extend e.toEmbedding (function m) a b (S.map e.toEmbedding),pullSet_map]
      exact hp
  have hcf : G.CliqueFree 5 := SimpleGraph.cliqueFree_map_iff.mpr (cliqueFree_five m)
  have hedge : (edgeFamily G).card = 3*n-5 := by
    change (edgeFamily ((graph m).map e.toEmbedding)).card = _
    rw [edgeFamily_card_map,edge_count]
    dsimp [m]
    omega
  have hw4 : HasTreewidthAtMost G 4 := by
    have hh := (width_at_most_four m).comap e.symm.toEmbedding
    rwa [SimpleGraph.comap_symm] at hh
  have hnw3 : ¬HasTreewidthAtMost G 3 := by
    intro hh
    have hback := hh.comap e.toEmbedding
    rw [show G = (graph m).map e.toEmbedding from rfl,SimpleGraph.comap_map_eq] at hback
    exact not_width_three m hback
  have hno : ¬HasAdmissibleSpanningThreeTree G := by
    intro hh
    have hback := hh.map_equiv e.symm
    rw [SimpleGraph.map_symm,show G = (graph m).map e.toEmbedding from rfl,
      SimpleGraph.comap_map_eq] at hback
    exact no_admissible_spanning m hback
  have hsupport : SupportsFullIndecomposable G :=
    ⟨basePolytope z,(show IsGeneralizedPermutahedron (basePolytope z) from
      ⟨z,hz.1.1,hz.2.1,rfl⟩).finitePolytope,hz.minkowskiIndecomposable,hdim,
      (n-6 : ℕ),by exact_mod_cast (show 0 < n-6 by omega),hsum⟩
  refine ⟨G,basePolytope z,hcf,hedge,hw4,hnw3,
    edgeMinimalSupporting_of_one_excess (by omega) hedge hno hsupport,
    hzi.basePolytope hz.1.1 hz.2.1,hz.minkowskiIndecomposable,hdim,hactual,hsum,?_⟩
  rintro ⟨H,hHG,hH,hS⟩
  exact hno ⟨H,hHG,hH,(threeTree_supports_iff_admissible (by omega) hH).mp hS⟩

/-- The exact pinned principal target, discharged by the stronger literal
statement above, including all orders and the asserted dilation. -/
theorem paper_theorem_8_2 : Targets.SparseTreewidthFourFamily := by
  intro n hn
  obtain ⟨G,Q,hcf,he,hw4,hnw3,hmin,hQ,hI,hD,hA,hS,hno⟩ := complete_family n hn
  exact ⟨G,hcf,he,hw4,hnw3,hmin,Q,hQ,hI,hD,hS⟩

/-- The same family using only ordinary polytopal indecomposability. The
proper-subgraph conclusion is expanded explicitly so the convention used
inside `EdgeMinimalSupporting` is not an implicit semantic assumption. -/
theorem paper_theorem_8_2_polytopal (n : ℕ) (hn : 10 ≤ n) :
    ∃ G : SimpleGraph (Fin n), ∃ Q : Set (Fin n → ℝ),
      G.CliqueFree 5 ∧ (edgeFamily G).card = 3*n-5 ∧
      HasTreewidthAtMost G 4 ∧ ¬HasTreewidthAtMost G 3 ∧
      LatticePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      actualDirectionGraph Q = G ∧
      IsMinkowskiSummand Q (((n-6 : ℕ) : ℝ) • graphicalZonotope G) ∧
      (∀ H : SimpleGraph (Fin n),H < G →
        ¬∃ R : Set (Fin n → ℝ),IsFinitePolytope R ∧
          PolytopalMinkowskiIndecomposable R ∧ FullDimension R ∧
          IsWeakMinkowskiSummand R (graphicalZonotope H)) ∧
      ¬∃ H : SimpleGraph (Fin n),H ≤ G ∧ IsThreeTree H ∧
        ∃ R : Set (Fin n → ℝ),IsFinitePolytope R ∧
          PolytopalMinkowskiIndecomposable R ∧ FullDimension R ∧
          IsWeakMinkowskiSummand R (graphicalZonotope H) := by
  obtain ⟨G,Q,hcf,he,hw4,hnw3,hmin,hQ,hI,hD,hA,hS,hno⟩ := complete_family n hn
  have hpoly : PolytopalMinkowskiIndecomposable Q :=
    ⟨hI.1,fun P R hP hR hsum => hI.2 P R hP.compact hR.compact hP.convex hR.convex hsum⟩
  refine ⟨G,Q,hcf,he,hw4,hnw3,hQ,hpoly,hD,hA,hS,?_,?_⟩
  · intro H hHG
    rintro ⟨R,hR,hi,hd,hs⟩
    exact hmin.2 H hHG
      ⟨R,hR,(weakSummand_indecomposable_iff_polytopal hR hs).mpr hi,hd,hs⟩
  · rintro ⟨H,hHG,hH,R,hR,hi,hd,hs⟩
    exact hno ⟨H,hHG,hH,
      R,hR,(weakSummand_indecomposable_iff_polytopal hR hs).mpr hi,hd,hs⟩

end GraphicalZonotopes.SparseFamily

end
end
end BundlePart343

section BundlePart344
/- Source: Papers/GraphicalZonotopes/ThreeTreePaperStatements.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped Pointwise

/-- The existence predicate in Theorem 6.1 is unchanged if indecomposability
is quantified over ordinary polytopes instead of all compact convex bodies.
The generalized-permutahedron presentation is derived from the actual sum. -/
theorem supportsFullIndecomposable_iff_polytopal {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    SupportsFullIndecomposable G ↔
      ∃ Q : Set (V → ℝ), IsFinitePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧
        FullDimension Q ∧ IsWeakMinkowskiSummand Q (graphicalZonotope G) := by
  constructor
  · rintro ⟨Q,hQ,hi,hd,hs⟩
    refine ⟨Q,hQ,⟨hi.1,?_⟩,hd,hs⟩
    intro P R hP hR he
    exact hi.2 P R hP.compact hR.compact hP.convex hR.convex he
  · rintro ⟨Q,hQ,hi,hd,a,ha,R,hR,hcR,hnR,he⟩
    obtain ⟨hn,hsm,hbody,_,_⟩ := actual_summand_lowerSupport
      hQ.compact hQ.convex hi.1 hR hcR hnR ha.le he
    have hgp : IsGeneralizedPermutahedron Q := ⟨lowerSupport Q,hn,hsm,hbody⟩
    exact ⟨Q,hQ,(minkowskiIndecomposable_iff_polytopal hgp).mpr hi,hd,
      a,ha,R,hR,hcR,hnR,he⟩

/-- The two equivalences of Theorem 6.1 with the paper's literal maximal-clique
and induced-deletion conditions and its ordinary polytope convention. The
quantitative lattice witness is `admissible_threeTree_lattice_witness`. -/
theorem threeTree_classification_polytopal {n : ℕ} (hn : 4≤ n)
    {G : SimpleGraph (Fin n)} (hG : IsThreeTree G) :
    ((∃ Q : Set (Fin n → ℝ), IsFinitePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G)) ↔
      ∀ T : Finset (Fin n),T.card=3 → G.IsClique T →
        (univ.filter (fun C : Finset (Fin n) => C.card=4 ∧
          Maximal G.IsClique (C : Set (Fin n)) ∧ T⊆C)).card≤3) ∧
    ((∃ Q : Set (Fin n → ℝ), IsFinitePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G)) ↔
      ∀ T : Finset (Fin n),T.card=3 → G.IsClique T →
        Nat.card (G.induce ((T : Set (Fin n))ᶜ)).ConnectedComponent≤3) := by
  have h := threeTree_classification_literal hn hG
  exact ⟨(supportsFullIndecomposable_iff_polytopal G).symm.trans h.1,
    (supportsFullIndecomposable_iff_polytopal G).symm.trans h.2⟩

end GraphicalZonotopes

end
end
end BundlePart344

section BundlePart345
/- Source: Papers/GraphicalZonotopes/TriangleFreeSeparator.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Separator
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} {B : Finset V}

/-- The induced boundary contains no triangle. This is expressed directly in
the ambient graph so the vertices outside the boundary are irrelevant. -/
def TriangleFreeBoundary (G : SimpleGraph V) (B : Finset V) : Prop :=
  ∀ T : Finset V, T ⊆ B → T.card = 3 → ¬G.IsClique T

theorem commonNeighbors_boundary_eq_empty (hB : TriangleFreeBoundary G B)
    (e : BoundaryEdge G B) : commonNeighbors G e.1.1.1 e.1.1.2 ∩ B = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro w hw
  obtain ⟨hwN,hwB⟩ := mem_inter.mp hw
  obtain ⟨huw,hvw⟩ := (mem_commonNeighbors G _ _ w).mp hwN
  have ht := (SimpleGraph.is3Clique_triple_iff (G := G)).mpr ⟨e.1.2.2,huw,hvw⟩
  exact hB {e.1.1.1,e.1.1.2,w}
    (by simp only [insert_subset_iff,singleton_subset_iff]; exact ⟨e.2.1,e.2.2,hwB⟩)
    ht.card_eq ht.isClique

def boundaryEdgeClique (e : BoundaryEdge G B) : ↥(boundaryCliques G B) :=
  ⟨{e.1.1.1,e.1.1.2},by
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr ?_,?_,?_⟩
    · exact insert_subset e.2.1 (singleton_subset_iff.mpr e.2.2)
    · simp [card_pair (ne_of_lt e.1.2.1)]
    · simpa only [Finset.coe_pair] using
        (SimpleGraph.isClique_pair).mpr (fun _ => e.1.2.2)⟩

theorem boundaryEdgeClique_injective :
    Function.Injective (boundaryEdgeClique (G := G) (B := B)) := by
  intro e f hef
  have he : ({e.1.1.1,e.1.1.2} : Finset V) = {f.1.1.1,f.1.1.2} :=
    congrArg Subtype.val hef
  have h₁ : e.1.1.1 = f.1.1.1 ∨ e.1.1.1 = f.1.1.2 := by
    have hh : e.1.1.1 ∈ ({f.1.1.1,f.1.1.2} : Finset V) := by rw [← he]; simp
    simpa only [mem_insert,mem_singleton] using hh
  have h₂ : e.1.1.2 = f.1.1.1 ∨ e.1.1.2 = f.1.1.2 := by
    have hh : e.1.1.2 ∈ ({f.1.1.1,f.1.1.2} : Finset V) := by rw [← he]; simp
    simpa only [mem_insert,mem_singleton] using hh
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · rcases h₁ with h₁ | h₁
    · exact h₁
    · rcases h₂ with h₂ | h₂
      · exact False.elim (lt_asymm e.1.2.1 (by simpa only [h₁,h₂] using f.1.2.1))
      · exact False.elim ((ne_of_lt e.1.2.1) (h₁.trans h₂.symm))
  · rcases h₂ with h₂ | h₂
    · rcases h₁ with h₁ | h₁
      · exact False.elim ((ne_of_lt e.1.2.1) (h₁.trans h₂.symm))
      · exact False.elim (lt_asymm e.1.2.1 (by simpa only [h₁,h₂] using f.1.2.1))
    · exact h₂

/-- A triangle-free boundary has at most one active private block. This is
the exact specialization of Lemma 5.1 used in Corollary 5.2. -/
theorem triangle_free_boundary_capacity (hB : TriangleFreeBoundary G B)
    (z : graphicalFunctionSpace G) (hz : ExtremeSupermodular z.1) :
    Fintype.card (Gluing.ActiveBranch
      (((functionEquiv (componentPartition G B)).symm z).2)) ≤ 1 := by
  have hc := induced_separator_capacity G B z hz
  have hsum : (∑ e : BoundaryEdge G B,
      2^(commonNeighbors G e.1.1.1 e.1.1.2 ∩ B).card) = Fintype.card (BoundaryEdge G B) := by
    simp only [commonNeighbors_boundary_eq_empty hB,card_empty,pow_zero,sum_const,
      card_univ,smul_eq_mul,mul_one]
  have hcard : Fintype.card (BoundaryEdge G B) ≤ (boundaryCliques G B).card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective
      (boundaryEdgeClique (G := G) (B := B)) boundaryEdgeClique_injective
  rw [hsum,Nat.sub_eq_zero_of_le hcard,zero_add] at hc
  exact hc

end Separator

open Finset

/-- Corollary 5.2: deleting a triangle-free boundary leaves at most one
component whenever a full-dimensional indecomposable weak summand exists. -/
theorem SupportsFullIndecomposable.triangle_free_components_le_one {n : ℕ} (hn : 2 ≤ n)
    {G : SimpleGraph (Fin n)} (hG : SupportsFullIndecomposable G)
    (B : Finset (Fin n)) (hB : Separator.TriangleFreeBoundary G B) :
    Nat.card ((G.induce ((B : Set (Fin n))ᶜ)).ConnectedComponent) ≤ 1 := by
  classical
  obtain ⟨z,hz,hd⟩ := hG.exists_extreme_function hn
  let x := (Separator.functionEquiv (Separator.componentPartition G B)).symm z
  have ha : ∀ j,x.2 j ≠ 0 := fun j =>
    Separator.private_block_ne_zero_of_fullDimension hn (Separator.componentPartition G B)
      z hz.2.1 hd j (Separator.componentPart_nonempty G B j)
  let e : Gluing.ActiveBranch x.2 ≃ (Separator.outsideGraph G B).ConnectedComponent := {
    toFun := Subtype.val
    invFun := fun j => ⟨j,ha j⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hc := Separator.triangle_free_boundary_capacity hB z hz
  change Fintype.card (Gluing.ActiveBranch x.2) ≤ 1 at hc
  rw [Fintype.card_congr e] at hc
  change Nat.card ((Separator.outsideGraph G B).ConnectedComponent) ≤ 1
  rw [@Nat.card_eq_fintype_card _ (Separator.componentFintype G B)]
  exact hc

/-- The paper's literal conclusion: every set whose deletion disconnects the
graph contains all three vertices of an actual graph triangle. -/
theorem SupportsFullIndecomposable.separator_contains_triangle {n : ℕ} (hn : 2 ≤ n)
    {G : SimpleGraph (Fin n)} (hG : SupportsFullIndecomposable G)
    (B : Finset (Fin n))
    (hsep : 2 ≤ Nat.card ((G.induce ((B : Set (Fin n))ᶜ)).ConnectedComponent)) :
    ∃ T : Finset (Fin n),T ⊆ B ∧ T.card = 3 ∧ G.IsClique T := by
  by_contra h
  have hB : Separator.TriangleFreeBoundary G B := by
    intro T hTB hT hc
    exact h ⟨T,hTB,hT,hc⟩
  have hb := hG.triangle_free_components_le_one hn B hB
  omega

/-- In particular, deleting fewer than three vertices cannot disconnect a
supporting graph. This quantifies over all such vertex sets. -/
theorem SupportsFullIndecomposable.delete_lt_three_preconnected {n : ℕ} (hn : 4 ≤ n)
    {G : SimpleGraph (Fin n)} (hG : SupportsFullIndecomposable G)
    (B : Finset (Fin n)) (hB : B.card < 3) :
    (G.induce ((B : Set (Fin n))ᶜ)).Preconnected := by
  have ht : Separator.TriangleFreeBoundary G B := by
    intro T hTB hT _
    have hc := card_le_card hTB
    omega
  have hc := hG.triangle_free_components_le_one (by omega) B ht
  letI : Subsingleton ((G.induce ((B : Set (Fin n))ᶜ)).ConnectedComponent) :=
    Fintype.card_le_one_iff_subsingleton.mp
      (by simpa only [Nat.card_eq_fintype_card] using hc)
  intro u v
  exact SimpleGraph.ConnectedComponent.exact (Subsingleton.elim _ _)

end GraphicalZonotopes

end
end
end BundlePart345

section BundlePart346
/- Source: Papers/GraphicalZonotopes/TwoHubGraphMaps.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes.TwoHub
open Finset
variable {I J I' J' : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype I'] [DecidableEq I'] [Fintype J'] [DecidableEq J']

def vertexEmbedding (e : I↪I') (f : J↪J') : ((Bool⊕I)⊕J)↪((Bool⊕I')⊕J') :=
  Function.Embedding.sumMap (Function.Embedding.sumMap (Function.Embedding.refl Bool) e) f

@[simp] theorem vertexEmbedding_color (e : I↪I') (f : J↪J') (x : (Bool⊕I)⊕J) :
    color (vertexEmbedding e f x)=color x := by
  rcases x with (v|i)|j
  · cases v <;> rfl
  · rfl
  · rfl

theorem graph_le_comap (e : I↪I') (f : J↪J') :
    graph (I:=I) (J:=J)≤(graph (I:=I') (J:=J')).comap (vertexEmbedding e f) := by
  intro x y hxy
  change color (vertexEmbedding e f x)≠ color (vertexEmbedding e f y)
  simpa [graph] using hxy

def swapVertex : ((Bool⊕I)⊕J)→((Bool⊕J)⊕I)
  | .inl (.inl v) => .inl (.inl v)
  | .inl (.inr i) => .inr i
  | .inr j => .inl (.inr j)

@[simp] theorem swapVertex_swap (x : (Bool⊕I)⊕J) : swapVertex (swapVertex x)=x := by
  rcases x with (v|i)|j <;> rfl

def swapEquiv : ((Bool⊕I)⊕J)≃((Bool⊕J)⊕I) where
  toFun:=swapVertex
  invFun:=swapVertex
  left_inv:=swapVertex_swap
  right_inv:=swapVertex_swap

def swapGraphIso : graph (I:=I) (J:=J)≃g graph (I:=J) (J:=I) where
  toEquiv:=swapEquiv
  map_rel_iff':=by
    intro x y
    change color (swapVertex x)≠ color (swapVertex y) ↔ color x≠ color y
    rcases x with (v|i)|j <;> rcases y with (w|k)|l
    · cases v <;> cases w <;> simp [swapVertex,color]
    · cases v <;> simp [swapVertex,color]
    · cases v <;> simp [swapVertex,color]
    · cases w <;> simp [swapVertex,color]
    · simp [swapVertex,color]
    · simp [swapVertex,color]
    · cases w <;> simp [swapVertex,color]
    · simp [swapVertex,color]
    · simp [swapVertex,color]

def twoSingletonSwap (p b : ℕ) : twoSingletonGraph p b≃g twoSingletonGraph b p :=
  (finGraphIso p b).symm.trans
    ((swapGraphIso (I:=Fin p) (J:=Fin b)).trans (finGraphIso b p))

theorem maximum_dimension_swap (p b : ℕ) :
    maximumIndecomposableDimension (twoSingletonGraph p b)=
      maximumIndecomposableDimension (twoSingletonGraph b p) :=
  maximumIndecomposableDimension_iso (twoSingletonSwap p b)

end GraphicalZonotopes.TwoHub

end
end
end BundlePart346
