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

public import verified.parts.part017
import all verified.parts.part017

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section BundlePart255
/- Source: Papers/GraphicalZonotopes/DoubledSliceContexts.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset BooleanFourier
variable {I : Type*} [Fintype I] [DecidableEq I]

def slicedPair (a : I) (b : Bool)
    (uv : Cube (DeletedIndex a) × Cube (DeletedIndex a)) : Cube I × Cube I :=
  (extendCube a b uv.1,extendCube a b uv.2)

theorem subsetOfBits_slice_false (a : I)
    (uv : Cube (DeletedIndex a) × Cube (DeletedIndex a)) :
    subsetOfBits (coordinateChange.symm (slicedPair a false uv))=
      (subsetOfBits (coordinateChange.symm uv)).map
        (pairedEmbedding (Function.Embedding.subtype (fun i : I => i≠ a))) := by
  ext w
  rcases w with ⟨i,b⟩
  fin_cases b <;> dsimp only
  · conv_lhs => simp [subsetOfBits]
    constructor
    · intro hi
      have hia : i≠ a := by
        intro he
        subst i
        simpa [coordinateChange,slicedPair] using hi
      refine mem_map.mpr ⟨(⟨i,hia⟩,0),?_,rfl⟩
      simpa [coordinateChange,slicedPair,extendCube,hia] using hi
    · intro hi
      obtain ⟨⟨j,b⟩,hj,he⟩ := mem_map.mp hi
      have hb : b=0 := congrArg Prod.snd he
      subst b
      have hji : j.1=i := congrArg Prod.fst he
      subst i
      simpa [coordinateChange,slicedPair,extendCube,j.2] using hj
  · conv_lhs => simp [subsetOfBits]
    constructor
    · intro hi
      have hia : i≠ a := by
        intro he
        subst i
        simpa [coordinateChange,slicedPair] using hi
      refine mem_map.mpr ⟨(⟨i,hia⟩,1),?_,rfl⟩
      simpa [coordinateChange,slicedPair,extendCube,hia] using hi
    · intro hi
      obtain ⟨⟨j,b⟩,hj,he⟩ := mem_map.mp hi
      have hb : b=1 := congrArg Prod.snd he
      subst b
      have hji : j.1=i := congrArg Prod.fst he
      subst i
      simpa [coordinateChange,slicedPair,extendCube,j.2] using hj

theorem subsetOfBits_slice_true (a : I)
    (uv : Cube (DeletedIndex a) × Cube (DeletedIndex a)) :
    subsetOfBits (coordinateChange.symm (slicedPair a true uv))=
      insert (a,0) (subsetOfBits (coordinateChange.symm (slicedPair a false uv))) := by
  ext w
  rcases w with ⟨i,b⟩
  fin_cases b <;> by_cases hi : i=a
  · subst i
    simp [subsetOfBits,coordinateChange,slicedPair,extendCube]
  · simp [subsetOfBits,coordinateChange,slicedPair,extendCube,hi]
  · subst i
    simp [subsetOfBits,coordinateChange,slicedPair,extendCube]
  · simp [subsetOfBits,coordinateChange,slicedPair,extendCube,hi]

theorem missing_one_not_mem_slice (a : I) (b : Bool)
    (uv : Cube (DeletedIndex a) × Cube (DeletedIndex a)) :
    (a,1)∉subsetOfBits (coordinateChange.symm (slicedPair a b uv)) := by
  cases b <;> simp [subsetOfBits,coordinateChange,slicedPair,extendCube]

theorem edgeContext_slice_true (u v : I×Fin 2) (a : Remaining u v)
    (uv : Cube (DeletedIndex a) × Cube (DeletedIndex a)) :
    edgeContext u v (coordinateChange.symm (slicedPair a true uv))=
      insert (a.1,0) (edgeContext u v (coordinateChange.symm (slicedPair a false uv))) := by
  simp only [edgeContext,subsetOfBits_slice_true,map_insert]
  rfl

theorem missing_one_not_mem_edge_slice (u v : I×Fin 2) (a : Remaining u v) (b : Bool)
    (uv : Cube (DeletedIndex a) × Cube (DeletedIndex a)) :
    (a.1,1)∉edgeContext u v (coordinateChange.symm (slicedPair a b uv)) := by
  intro h
  obtain ⟨w,hw,he⟩ := mem_map.mp h
  have he' : w=(a,1) := (remainingEmbedding u v).injective he
  exact missing_one_not_mem_slice a b uv (he' ▸ hw)

theorem paired_map_pullSet (a : I) (S : Finset (I×Fin 2)) :
    (SetFunctionEmbedding.pullSet
      (pairedEmbedding (Function.Embedding.subtype (fun i : I => i≠ a))) S).map
        (pairedEmbedding (Function.Embedding.subtype (fun i : I => i≠ a)))=
      (S.erase (a,0)).erase (a,1) := by
  ext w
  rcases w with ⟨i,b⟩
  simp only [mem_map,SetFunctionEmbedding.mem_pullSet,mem_erase]
  constructor
  · rintro ⟨⟨j,c⟩,hj,he⟩
    have hia : i≠ a := by
      have hji : j.1=i := congrArg Prod.fst he
      exact hji ▸ j.2
    refine ⟨?_,?_,?_⟩
    · intro h
      exact hia (congrArg Prod.fst h)
    · intro h
      exact hia (congrArg Prod.fst h)
    · simpa only [he] using hj
  · rintro ⟨h1,h0,hw⟩
    have hia : i≠ a := by
      intro hi
      subst i
      fin_cases b
      · exact h0 rfl
      · exact h1 rfl
    exact ⟨(⟨i,hia⟩,b),hw,rfl⟩

/-- Every context, after deleting both vertices of one part, is one of the
zero-bit slices of the remaining-part cube. This is the surjectivity needed
when the slice argument is applied back to the complete elemental kernel. -/
theorem exists_zero_slice_context (u v : I×Fin 2) (a : Remaining u v)
    (S : Finset (I×Fin 2)) :
    ∃ uv : Cube (DeletedIndex a) × Cube (DeletedIndex a),
      edgeContext u v (coordinateChange.symm (slicedPair a false uv))=
        ((S∩commonNeighbors (graph I) u v).erase (a.1,0)).erase (a.1,1) := by
  let T := remainingPart u v S
  let e := pairedEmbedding (Function.Embedding.subtype (fun i : Remaining u v => i≠ a))
  let U := SetFunctionEmbedding.pullSet e T
  let uv := coordinateChange (bitsOfSubset U)
  refine ⟨uv,?_⟩
  rw [edgeContext,subsetOfBits_slice_false]
  have hU : subsetOfBits (coordinateChange.symm uv)=U := by simp [uv]
  rw [hU]
  change (U.map e).map (remainingEmbedding u v)=_
  rw [show U.map e=(T.erase (a,0)).erase (a,1) from paired_map_pullSet a T]
  rw [map_erase,map_erase]
  have hT : T.map (remainingEmbedding u v)=S∩commonNeighbors (graph I) u v := by
    simpa only [edgeContext,subsetOfBits_bitsOfSubset] using edgeContext_remainingPart u v S
  rw [hT]
  rfl

end DoubledParts
end GraphicalZonotopes

end
end
end BundlePart255

section BundlePart256
/- Source: Papers/GraphicalZonotopes/DoubledDeletionKernel.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset BooleanFourier
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The actual complete-quadratic row description, before any vertex is
deleted. Both members of the floor-half complementary pair satisfy it. -/
def CompleteQuadraticRows (z : SetFunction (I×Fin 2)) : Prop :=
  ∀ u v,(graph I).Adj u v → ∃ c : ℝ,∃ L : Finset (Remaining u v),
    (c=1 ∨ c= -1) ∧ ∀ uv,
      delta z u v (edgeContext u v (coordinateChange.symm uv))=
        faceFunction (completePhase c L) uv

theorem setFunction_completeQuadraticRows : CompleteQuadraticRows (setFunction (I := I)) := by
  intro u v huv
  refine ⟨if u.2=1 ∧ v.2=1 then -1 else 1,if u.2=v.2 then univ else ∅,?_,?_⟩
  · split_ifs <;> simp
  · exact setFunction_edgeProfile huv

theorem complementFunction_completeQuadraticRows :
    CompleteQuadraticRows (complementFunction (I := I)) := by
  intro u v huv
  refine ⟨-(if u.2=1 ∧ v.2=1 then -1 else 1),if u.2=v.2 then univ else ∅,?_,?_⟩
  · split_ifs <;> norm_num
  · intro uv
    rw [complementFunction_edgeProfile huv]
    congr 1
    funext x
    simp only [rowPhase,Pi.neg_apply,completePhase]
    ring

theorem remaining_deleted_nonempty (hI : 4≤ Fintype.card I)
    (u v : I×Fin 2) (a : Remaining u v) : Nonempty (DeletedIndex a) := by
  obtain ⟨i,hi,hn⟩ := exists_mem_notMem_of_card_lt_card
    (show ({u.1,v.1,a.1} : Finset I).card<(univ : Finset I).card by
      have h : ({u.1,v.1,a.1} : Finset I).card≤3 := card_le_three
      simpa only [card_univ] using (lt_of_le_of_lt h (by omega : 3< Fintype.card I)))
  have hnot : i≠ u.1 ∧ i≠ v.1 ∧ i≠ a.1 := by simpa using hn
  exact ⟨⟨⟨i,hnot.1,hnot.2.1⟩,fun he => hnot.2.2 (congrArg Subtype.val he)⟩⟩

/-- The complete tight kernel after deleting one of the paired vertices is
still a line. All retained contexts are used, and the proof derives the
missing row equations by the two distinct Boolean slices. -/
theorem one_singleton_tight_kernel (hI : 4≤ Fintype.card I) (a : I)
    {z : SetFunction (I×Fin 2)} (hzn : TranslationNormalized z)
    (hzG : Graphical (graph I) z) (hphase : CompleteQuadraticRows z)
    (hfour : ∀ C : Finset (I×Fin 2),C.card=4 → (graph I).IsClique C → mobius z C≠0)
    (f : SetFunction (VertexDeletion.Retained (a,(1 : Fin 2)))) (hfn : TranslationNormalized f)
    (hzero : ∀ u v : VertexDeletion.Retained (a,(1 : Fin 2)),u≠ v →
      ∀ S : Finset (VertexDeletion.Retained (a,(1 : Fin 2))),u∉S → v∉S →
      delta (SetFunctionEmbedding.restrict (VertexDeletion.embedding (a,1)) z) u v S=0 →
      delta f u v S=0) :
    ∃ t : ℝ,f=t • SetFunctionEmbedding.restrict (VertexDeletion.embedding (a,1)) z := by
  let d : I×Fin 2 := (a,1)
  let s : I×Fin 2 := (a,0)
  let e := VertexDeletion.embedding d
  let F := SetFunctionEmbedding.extend e f
  let Z := SetFunctionEmbedding.extend e (SetFunctionEmbedding.restrict e z)
  have hsd : s≠ d := by simp [s,d]
  have hfG : Graphical ((graph I).comap e) f := by
    intro u v huv hnon S hu hv
    exact hzero u v huv S hu hv
      (SetFunctionEmbedding.restrict_graphical e hzG u v huv hnon S hu hv)
  have hFn : TranslationNormalized F := SetFunctionEmbedding.extend_translationNormalized e hfn
  have hFG : Graphical (graph I) F := SetFunctionEmbedding.extend_graphical e hfG
  have hZn : TranslationNormalized Z := SetFunctionEmbedding.extend_translationNormalized e
    (SetFunctionEmbedding.restrict_translationNormalized e hzn)
  have hZG : Graphical (graph I) Z := SetFunctionEmbedding.extend_graphical e
    (SetFunctionEmbedding.restrict_graphical e hzG)
  have hlocal := deletion_incident_row_line (by omega : 3≤ Fintype.card I) s d hsd rfl
    hzn hzG (fun v => by
      obtain ⟨c,L,hc,hp⟩ := hphase s v.1 v.2
      have hc0 : c≠0 := by rcases hc with rfl | rfl <;> norm_num
      exact ⟨completePhase c L,completePhase_isSign hc L,completePhase_nonseparable hc0 L,hp⟩)
    f hfn hzero
  choose scale hscale using hlocal
  obtain ⟨t,ht⟩ := star_scales_constant hI s z F hfour scale hscale
  let R : SetFunction (I×Fin 2) := F-t • Z
  have hRn : TranslationNormalized R := by
    refine ⟨?_,?_⟩
    · change F ∅-t*Z ∅=0
      rw [hFn.1,hZn.1]
      ring
    · intro v
      change F {v}-t*Z {v}=0
      rw [hFn.2 v,hZn.2 v]
      ring
  have hRG : Graphical (graph I) R := by
    intro u v huv hnon S hu hv
    rw [show R=F-t • Z from rfl,delta_sub,delta_smul,
      hFG u v huv hnon S hu hv,hZG u v huv hnon S hu hv]
    ring
  have hignoreD : ∀ S : Finset (I×Fin 2),R (insert d S)=R S := by
    intro S
    simp only [R,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,F,Z,
      SetFunctionEmbedding.extend_insert_absent e _ d (VertexDeletion.deleted_not_range d)]
  have hrowS : ∀ v,s≠ v → ∀ S : Finset (I×Fin 2),s∉S → v∉S → delta R s v S=0 := by
    intro v hsv S hs hv
    by_cases hadj : (graph I).Adj s v
    · let v' : AtVertex s := ⟨v,hadj⟩
      have hvd : v≠ d := by intro he; exact hadj (by simpa [s,d] using congrArg Prod.fst he.symm)
      have hz : delta Z s v S=delta z s v S := by
        have he : Z=(fun T => z (T.erase d)) := funext (VertexDeletion.extend_restrict d z)
        rw [he]
        exact VertexDeletion.delta_delete_nonNeighbor hzn hzG hsv hsd hvd (by simp [s,d,graph]) hs hv
      rw [show R=F-t • Z from rfl,delta_sub,delta_smul,hscale v' S hs hv,ht v',hz]
      ring
    · exact hRG s v hsv hadj S hs hv
  have hignoreS := insert_eq_of_zero_incident hRn s hrowS
  have hRzero {u v : I×Fin 2} (huv : u≠ v) (hud : u≠ d) (hvd : v≠ d)
      {S : Finset (I×Fin 2)} (hu : u∉S) (hv : v∉S) (hd : d∉S)
      (hz : delta z u v S=0) : delta R u v S=0 := by
    have hF0 : delta F u v S=0 := VertexDeletion.extended_tight_zero d z f hzero huv hud hvd hu hv hd hz
    have hZ0 : delta Z u v S=0 := by
      have he : Z=(fun T => z (T.erase d)) := funext (VertexDeletion.extend_restrict d z)
      rw [he,VertexDeletion.delta_erase_function d u v hud hvd,erase_eq_of_notMem hd]
      exact hz
    rw [show R=F-t • Z from rfl,delta_sub,delta_smul,hF0,hZ0]
    ring
  have hother {u v : I×Fin 2} (hua : u.1≠ a) (hva : v.1≠ a)
      (huv : (graph I).Adj u v) :
      ∀ S : Finset (I×Fin 2),u∉S → v∉S → delta R u v S=0 := by
    let a' : Remaining u v := ⟨a,Ne.symm hua,Ne.symm hva⟩
    letI := remaining_deleted_nonempty hI u v a'
    obtain ⟨c,L,hc,hprofile⟩ := hphase u v huv
    have hc0 : c≠0 := by rcases hc with rfl | rfl <;> norm_num
    let p : (Cube (DeletedIndex a') × Cube (DeletedIndex a')) → ℝ :=
      fun uv => delta R u v (edgeContext u v (coordinateChange.symm (slicedPair a' false uv)))
    have hp : p∈tensorSpace := tensorSpace_slice a' false false
      (graphical_edgeProfile_mem_tensorSpace hRn hRG ((graph I).ne_of_adj huv))
    have hslice (b : Bool) (uv : Cube (DeletedIndex a') × Cube (DeletedIndex a'))
        (hz : faceFunction (slicePhase a' c L b) uv=0) :
        delta R u v (edgeContext u v (coordinateChange.symm (slicedPair a' b uv)))=0 := by
      apply hRzero ((graph I).ne_of_adj huv)
        (fun he => hua (congrArg Prod.fst he)) (fun he => hva (congrArg Prod.fst he))
        (left_not_mem_edgeContext _ _ _) (right_not_mem_edgeContext _ _ _)
        (missing_one_not_mem_edge_slice u v a' b uv)
      rw [hprofile]
      exact (faceFunction_slice a' c L b uv).trans hz
    have hp0 : p=0 := by
      apply boolean_slice_intersection (slicePhase_isSign a' hc L false)
        (slicePhase_isSign a' hc L true) (slicePhase_nonseparable a' hc0 L false)
        (slicePhase_nonseparable a' hc0 L true) (slicePhase_distinct a' hc0 L) p hp
      · exact hslice false
      · intro uv hz
        have h := hslice true uv hz
        rw [edgeContext_slice_true,delta_insert_eq_of_insert_eq hignoreS] at h
        exact h
    intro S hu hv
    obtain ⟨uv,he⟩ := exists_zero_slice_context u v a' S
    have h := congrFun hp0 uv
    change delta R u v (edgeContext u v (coordinateChange.symm (slicedPair a' false uv)))=0 at h
    rw [he] at h
    rw [VertexDeletion.delta_erase_eq_of_insert_eq hignoreD u v
        (fun he => hua (congrArg Prod.fst he)) (fun he => hva (congrArg Prod.fst he)),
      VertexDeletion.delta_erase_eq_of_insert_eq hignoreS u v
        (fun he => hua (congrArg Prod.fst he)) (fun he => hva (congrArg Prod.fst he))] at h
    rw [delta_commonNeighbors hRn hRG ((graph I).ne_of_adj huv) hu hv]
    exact h
  have hR : R=0 := by
    apply normalized_zero_elemental_eq_zero hRn
    intro u v huv S hu hv
    by_cases hua : u.1=a
    · rcases u with ⟨i,b⟩
      change i=a at hua
      subst i
      fin_cases b
      · exact delta_zero_of_insert_eq hignoreS v S
      · exact delta_zero_of_insert_eq hignoreD v S
    · by_cases hva : v.1=a
      · rw [delta_comm]
        rcases v with ⟨i,b⟩
        change i=a at hva
        subst i
        fin_cases b
        · exact delta_zero_of_insert_eq hignoreS u S
        · exact delta_zero_of_insert_eq hignoreD u S
      · by_cases hadj : (graph I).Adj u v
        · exact hother hua hva hadj S hu hv
        · exact hRG u v huv hadj S hu hv
  refine ⟨t,?_⟩
  have he : F=t • Z := sub_eq_zero.mp hR
  have hsmall := congrArg (SetFunctionEmbedding.restrict e) he
  simpa only [F,Z,SetFunctionEmbedding.restrict_smul,SetFunctionEmbedding.restrict_extend] using hsmall

end DoubledParts
end GraphicalZonotopes

end
end
end BundlePart256

section BundlePart257
/- Source: Papers/GraphicalZonotopes/DoubledGeometry.lean -/








@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset
open scoped Pointwise
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem setFunction_ne_zero (hI : 3≤ Fintype.card I) : (setFunction (I := I))≠0 := by
  obtain ⟨e⟩ := slopeEdge_nonempty (by omega : 2≤ Fintype.card I)
  obtain ⟨S,hu,hv,hd⟩ := setFunction_nonzero_slack hI e.2
  intro he
  rw [he] at hd
  exact hd (by simp [delta])

theorem complementFunction_ne_zero (hI : 3≤ Fintype.card I) : (complementFunction (I := I))≠0 := by
  obtain ⟨e⟩ := slopeEdge_nonempty (by omega : 2≤ Fintype.card I)
  obtain ⟨S,hu,hv,hd⟩ := complementFunction_nonzero_slack hI e.2
  intro he
  rw [he] at hd
  exact hd (by simp [delta])

theorem setFunction_extreme (hI : 4≤ Fintype.card I) :
    ExtremeSupermodular (setFunction (I := I)) := by
  apply extremeSupermodular_of_local_row_lines setFunction_translationNormalized
    setFunction_supermodular (setFunction_ne_zero (by omega)) setFunction_graphical
  · exact coefficientEdgeGraph_connected hI (fun C hc hC => mobius_setFunction_four_ne_zero hc hC)
  · exact setFunction_local_row_lines (by omega)

theorem complementFunction_extreme (hI : 4≤ Fintype.card I) :
    ExtremeSupermodular (complementFunction (I := I)) := by
  apply extremeSupermodular_of_local_row_lines complementFunction_translationNormalized
    complementFunction_supermodular (complementFunction_ne_zero (by omega)) complementFunction_graphical
  · exact coefficientEdgeGraph_connected hI (fun C hc hC => mobius_complementFunction_four_ne_zero hc hC)
  · exact complementFunction_local_row_lines (by omega)

theorem polytope_indecomposable (hI : 4≤ Fintype.card I) :
    MinkowskiIndecomposable (polytope (I := I)) :=
  (setFunction_extreme hI).minkowskiIndecomposable

theorem complementPolytope_indecomposable (hI : 4≤ Fintype.card I) :
    MinkowskiIndecomposable (complementPolytope (I := I)) :=
  (complementFunction_extreme hI).minkowskiIndecomposable

theorem polytope_fullDimension (hI : 3≤ Fintype.card I) :
    FullDimension (polytope (I := I)) := by
  apply finrank_vectorSpan_eq_of_connected_slacks setFunction_translationNormalized.1
    setFunction_supermodular (graph_connected (by omega))
  intro u v huv
  exact setFunction_nonzero_slack hI huv

theorem complementPolytope_fullDimension (hI : 3≤ Fintype.card I) :
    FullDimension (complementPolytope (I := I)) := by
  apply finrank_vectorSpan_eq_of_connected_slacks complementFunction_translationNormalized.1
    complementFunction_supermodular (graph_connected (by omega))
  intro u v huv
  exact complementFunction_nonzero_slack hI huv

theorem polytope_actualDirectionGraph (hI : 3≤ Fintype.card I) :
    actualDirectionGraph (polytope (I := I))=graph I := by
  ext u v
  constructor
  · apply basePolytope_summand_actualRootEdge setFunction_translationNormalized.1
      setFunction_supermodular (graph I) (by norm_num : (0 : ℝ)≤1) complementPolytope
    simpa only [one_smul,polytope] using (polytope_add_complement (I := I))
  · intro huv
    obtain ⟨S,hu,hv,hd⟩ := setFunction_nonzero_slack hI huv
    apply exposedSegment_of_positive_delta setFunction_translationNormalized.1
      setFunction_supermodular ((graph I).ne_of_adj huv) hu hv
    have hnon := setFunction_supermodular.elemental u v ((graph I).ne_of_adj huv) S hu hv
    exact lt_of_le_of_ne hnon (Ne.symm hd)

theorem complementPolytope_actualDirectionGraph (hI : 3≤ Fintype.card I) :
    actualDirectionGraph (complementPolytope (I := I))=graph I := by
  ext u v
  constructor
  · apply basePolytope_summand_actualRootEdge complementFunction_translationNormalized.1
      complementFunction_supermodular (graph I) (by norm_num : (0 : ℝ)≤1) polytope
    simpa only [one_smul,add_comm,complementPolytope] using (polytope_add_complement (I := I))
  · intro huv
    obtain ⟨S,hu,hv,hd⟩ := complementFunction_nonzero_slack hI huv
    apply exposedSegment_of_positive_delta complementFunction_translationNormalized.1
      complementFunction_supermodular ((graph I).ne_of_adj huv) hu hv
    have hnon := complementFunction_supermodular.elemental u v ((graph I).ne_of_adj huv) S hu hv
    exact lt_of_le_of_ne hnon (Ne.symm hd)

/-- Every geometric edge is covered by the root-direction graph. -/
theorem every_polytope_edge_is_root {p q : (I×Fin 2) → ℝ}
    (h : IsExposedSegment polytope p q) :
    ∃ u v,(graph I).Adj u v ∧ ∃ t : ℝ,t≠0 ∧
      q-p=t • (basisVector v-basisVector u) := by
  apply basePolytope_summand_exposed_edge setFunction_translationNormalized.1
    setFunction_supermodular (graph I) (by norm_num : (0 : ℝ)≤1) complementPolytope _ h
  simpa only [one_smul,polytope] using (polytope_add_complement (I := I))

theorem every_complementPolytope_edge_is_root {p q : (I×Fin 2) → ℝ}
    (h : IsExposedSegment complementPolytope p q) :
    ∃ u v,(graph I).Adj u v ∧ ∃ t : ℝ,t≠0 ∧
      q-p=t • (basisVector v-basisVector u) := by
  apply basePolytope_summand_exposed_edge complementFunction_translationNormalized.1
    complementFunction_supermodular (graph I) (by norm_num : (0 : ℝ)≤1) polytope _ h
  simpa only [one_smul,add_comm,complementPolytope] using (polytope_add_complement (I := I))

theorem polytope_booleanElemental : BooleanElemental (polytope (I := I)) := by
  intro u v huv S hu hv
  rw [polytope,lowerSupport_basePolytope setFunction_translationNormalized.1 setFunction_supermodular]
  exact setFunction_boolean huv hu hv

theorem complementPolytope_booleanElemental : BooleanElemental (complementPolytope (I := I)) := by
  intro u v huv S hu hv
  rw [complementPolytope,lowerSupport_basePolytope complementFunction_translationNormalized.1
    complementFunction_supermodular]
  by_cases he : (graph I).Adj u v
  · rw [complementFunction,delta_sub,graphFunction_delta _ huv hu hv,if_pos he]
    rcases setFunction_boolean huv hu hv with h | h
    · exact Or.inr (by rw [h]; norm_num)
    · exact Or.inl (by rw [h]; norm_num)
  · exact Or.inl (complementFunction_graphical u v huv he S hu hv)

end DoubledParts
end GraphicalZonotopes

end
end
end BundlePart257

section BundlePart258
/- Source: Papers/GraphicalZonotopes/OneSingleton.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset BooleanFourier
open scoped Pointwise
variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev SingletonVertices (a : I) := VertexDeletion.Retained (a,(1 : Fin 2))

def singletonGraph (a : I) : SimpleGraph (SingletonVertices a) :=
  (graph I).comap (VertexDeletion.embedding (a,(1 : Fin 2)))

abbrev singletonFunction (a : I) (z : SetFunction (I×Fin 2)) : SetFunction (SingletonVertices a) :=
  SetFunctionEmbedding.restrict (VertexDeletion.embedding (a,(1 : Fin 2))) z

theorem singletonGraph_connected (hI : 2≤ Fintype.card I) (a : I) :
    (singletonGraph a).Connected := by
  letI : Nonempty (SingletonVertices a) := ⟨⟨(a,0),by simp⟩⟩
  refine ⟨?_⟩
  intro u v
  by_cases huv : u.1.1≠ v.1.1
  · exact SimpleGraph.Adj.reachable huv
  · have hp : u.1.1=v.1.1 := not_not.mp huv
    obtain ⟨i,hi,hn⟩ := exists_mem_notMem_of_card_lt_card
      (show ({u.1.1} : Finset I).card<(univ : Finset I).card by simp only [card_singleton,card_univ]; omega)
    have hiu : i≠ u.1.1 := by simpa using hn
    let w : SingletonVertices a := ⟨(i,0),by simp⟩
    exact (SimpleGraph.Adj.reachable (show (singletonGraph a).Adj u w from Ne.symm hiu)).trans
      (SimpleGraph.Adj.reachable (show (singletonGraph a).Adj w v from by change i≠ v.1.1; rwa [← hp]))

theorem singletonGraph_has_edge (hI : 2≤ Fintype.card I) (a : I) :
    ∃ u v : SingletonVertices a,(singletonGraph a).Adj u v := by
  obtain ⟨v⟩ := exists_star_vertex hI (a,0)
  have hv : v.1≠(a,1) := by
    intro he
    exact v.2 (congrArg Prod.fst he).symm
  exact ⟨⟨(a,0),by simp⟩,⟨v.1,hv⟩,v.2⟩

theorem singleton_nonzero_slack (hI : 4≤ Fintype.card I) (a : I)
    {z : SetFunction (I×Fin 2)} (hphase : CompleteQuadraticRows z)
    {u v : SingletonVertices a} (huv : (singletonGraph a).Adj u v) :
    ∃ S : Finset (SingletonVertices a),u∉S ∧ v∉S ∧
      delta (singletonFunction a z) u v S≠0 := by
  let d : I×Fin 2 := (a,1)
  let e := VertexDeletion.embedding d
  have hadj : (graph I).Adj u.1 v.1 := huv
  have transfer (S : Finset (I×Fin 2)) (hu : u.1∉S) (hv : v.1∉S) (hd : d∉S)
      (hz : delta z u.1 v.1 S≠0) :
      ∃ T : Finset (SingletonVertices a),u∉T ∧ v∉T ∧
        delta (singletonFunction a z) u v T≠0 := by
    have heu : e u=u.1 := rfl
    have hev : e v=v.1 := rfl
    refine ⟨SetFunctionEmbedding.pullSet e S,?_,?_,?_⟩
    · rw [SetFunctionEmbedding.mem_pullSet,heu]
      exact hu
    · rw [SetFunctionEmbedding.mem_pullSet,hev]
      exact hv
    · rw [singletonFunction,SetFunctionEmbedding.delta_restrict,
        VertexDeletion.map_pullSet,erase_eq_of_notMem hd]
      exact hz
  obtain ⟨c,L,hc,hprofile⟩ := hphase u.1 v.1 hadj
  have hc0 : c≠0 := by rcases hc with rfl | rfl <;> norm_num
  by_cases hparts : u.1.1=a ∨ v.1.1=a
  · letI := remaining_nonempty (by omega : 3≤ Fintype.card I) u.1 v.1
    have hne := faceFunction_ne_zero (completePhase_isSign hc L)
    obtain ⟨uv,huv'⟩ : ∃ uv,faceFunction (completePhase c L) uv≠0 := by
      by_contra! h
      exact hne (funext h)
    apply transfer (edgeContext u.1 v.1 (coordinateChange.symm uv))
      (left_not_mem_edgeContext _ _ _) (right_not_mem_edgeContext _ _ _) _
      (by rwa [hprofile])
    intro hm
    obtain ⟨w,hw,he⟩ := mem_map.mp hm
    have hwa : w.1.1=a := congrArg Prod.fst he
    rcases hparts with hu | hv
    · exact w.1.2.1 (hwa.trans hu.symm)
    · exact w.1.2.2 (hwa.trans hv.symm)
  · have hparts' : u.1.1≠ a ∧ v.1.1≠ a := not_or.mp hparts
    let a' : Remaining u.1 v.1 := ⟨a,Ne.symm hparts'.1,Ne.symm hparts'.2⟩
    letI := remaining_deleted_nonempty hI u.1 v.1 a'
    have hne := faceFunction_ne_zero (slicePhase_isSign a' hc L false)
    obtain ⟨uv,huv'⟩ : ∃ uv,faceFunction (slicePhase a' c L false) uv≠0 := by
      by_contra! h
      exact hne (funext h)
    apply transfer (edgeContext u.1 v.1 (coordinateChange.symm (slicedPair a' false uv)))
      (left_not_mem_edgeContext _ _ _) (right_not_mem_edgeContext _ _ _)
      (missing_one_not_mem_edge_slice _ _ a' false uv)
    rw [hprofile,slicedPair,faceFunction_slice]
    exact huv'

theorem singleton_extreme (hI : 4≤ Fintype.card I) (a : I)
    {z : SetFunction (I×Fin 2)} (hzn : TranslationNormalized z) (hzs : Supermodular z)
    (hzG : Graphical (graph I) z) (hphase : CompleteQuadraticRows z)
    (hfour : ∀ C : Finset (I×Fin 2),C.card=4 → (graph I).IsClique C → mobius z C≠0) :
    ExtremeSupermodular (singletonFunction a z) := by
  have hn := SetFunctionEmbedding.restrict_translationNormalized (VertexDeletion.embedding (a,(1 : Fin 2))) hzn
  have hs := SetFunctionEmbedding.restrict_supermodular (VertexDeletion.embedding (a,(1 : Fin 2))) hzs
  have hne : singletonFunction a z≠0 := by
    obtain ⟨u,v,huv⟩ := singletonGraph_has_edge (by omega : 2≤ Fintype.card I) a
    obtain ⟨S,hu,hv,hd⟩ := singleton_nonzero_slack hI a hphase huv
    intro he
    rw [he] at hd
    exact hd (by simp [delta])
  apply extremeSupermodular_of_tightEquations hn hs hne
  exact one_singleton_tight_kernel hI a hzn hzG hphase hfour

def singletonPolytope (a : I) : Set (SingletonVertices a → ℝ) :=
  basePolytope (singletonFunction a setFunction)

def singletonComplementPolytope (a : I) : Set (SingletonVertices a → ℝ) :=
  basePolytope (singletonFunction a complementFunction)

theorem singleton_pair_sum (a : I) :
    singletonPolytope a+singletonComplementPolytope a=graphicalZonotope (singletonGraph a) := by
  let e := VertexDeletion.embedding (a,(1 : Fin 2))
  have hn := SetFunctionEmbedding.restrict_translationNormalized e setFunction_translationNormalized
  have hn' := SetFunctionEmbedding.restrict_translationNormalized e complementFunction_translationNormalized
  have hs := SetFunctionEmbedding.restrict_supermodular e setFunction_supermodular
  have hs' := SetFunctionEmbedding.restrict_supermodular e complementFunction_supermodular
  rw [singletonPolytope,singletonComplementPolytope,← basePolytope_add hn.1 hn'.1 hs hs']
  have he : singletonFunction a setFunction+singletonFunction a complementFunction=
      graphFunction (singletonGraph a) := by
    rw [singletonFunction,singletonFunction,← SetFunctionEmbedding.restrict_add]
    rw [show setFunction+complementFunction=graphFunction (graph I) by unfold complementFunction; abel]
    exact SetFunctionEmbedding.graphFunction_restrict e (graph I)
  rw [he,baseGraphFunction_eq_graphicalZonotope]

/-- Corollary9.10 for an arbitrary finite part set and a specified singleton
part. The two summands are the actual restricted lower base polytopes. -/
theorem one_singleton_decomposition (hI : 4≤ Fintype.card I) (a : I) :
    LatticePolytope (singletonPolytope a) ∧
    LatticePolytope (singletonComplementPolytope a) ∧
    MinkowskiIndecomposable (singletonPolytope a) ∧
    MinkowskiIndecomposable (singletonComplementPolytope a) ∧
    FullDimension (singletonPolytope a) ∧ FullDimension (singletonComplementPolytope a) ∧
    singletonPolytope a+singletonComplementPolytope a=graphicalZonotope (singletonGraph a) ∧
    actualDirectionGraph (singletonPolytope a)=singletonGraph a ∧
    actualDirectionGraph (singletonComplementPolytope a)=singletonGraph a ∧
    BooleanElemental (singletonPolytope a) ∧ BooleanElemental (singletonComplementPolytope a) := by
  let e := VertexDeletion.embedding (a,(1 : Fin 2))
  have hn := SetFunctionEmbedding.restrict_translationNormalized e setFunction_translationNormalized
  have hn' := SetFunctionEmbedding.restrict_translationNormalized e complementFunction_translationNormalized
  have hs := SetFunctionEmbedding.restrict_supermodular e setFunction_supermodular
  have hs' := SetFunctionEmbedding.restrict_supermodular e complementFunction_supermodular
  have hQ : MinkowskiIndecomposable (singletonPolytope a) :=
    (singleton_extreme hI a setFunction_translationNormalized setFunction_supermodular
      setFunction_graphical setFunction_completeQuadraticRows
      (fun C hc hC => mobius_setFunction_four_ne_zero hc hC)).minkowskiIndecomposable
  have hR : MinkowskiIndecomposable (singletonComplementPolytope a) :=
    (singleton_extreme hI a complementFunction_translationNormalized complementFunction_supermodular
      complementFunction_graphical complementFunction_completeQuadraticRows
      (fun C hc hC => mobius_complementFunction_four_ne_zero hc hC)).minkowskiIndecomposable
  have hconn := singletonGraph_connected (by omega : 2≤ Fintype.card I) a
  have hslack {u v : SingletonVertices a} (h : (singletonGraph a).Adj u v) :=
    singleton_nonzero_slack hI a setFunction_completeQuadraticRows h
  have hslack' {u v : SingletonVertices a} (h : (singletonGraph a).Adj u v) :=
    singleton_nonzero_slack hI a complementFunction_completeQuadraticRows h
  have hsum := singleton_pair_sum a
  refine ⟨(SetFunctionEmbedding.integerValued_restrict e setFunction_integerValued).basePolytope hn.1 hs,
    (SetFunctionEmbedding.integerValued_restrict e complementFunction_integerValued).basePolytope hn'.1 hs',
    hQ,hR,finrank_vectorSpan_eq_of_connected_slacks hn.1 hs hconn (fun _ _ h => hslack h),
    finrank_vectorSpan_eq_of_connected_slacks hn'.1 hs' hconn (fun _ _ h => hslack' h),hsum,?_,?_,?_,?_⟩
  · ext u v
    constructor
    · apply basePolytope_summand_actualRootEdge hn.1 hs (singletonGraph a)
        (by norm_num : (0 : ℝ)≤1) (singletonComplementPolytope a)
      simpa only [one_smul,singletonPolytope,singletonFunction,e] using hsum
    · intro huv
      obtain ⟨S,hu,hv,hd⟩ := hslack huv
      apply exposedSegment_of_positive_delta hn.1 hs ((singletonGraph a).ne_of_adj huv) hu hv
      exact lt_of_le_of_ne (hs.elemental u v ((singletonGraph a).ne_of_adj huv) S hu hv) (Ne.symm hd)
  · ext u v
    constructor
    · apply basePolytope_summand_actualRootEdge hn'.1 hs' (singletonGraph a)
        (by norm_num : (0 : ℝ)≤1) (singletonPolytope a)
      have hh : singletonComplementPolytope a+singletonPolytope a=graphicalZonotope (singletonGraph a) := by
        rw [add_comm]
        exact hsum
      simpa only [one_smul,singletonComplementPolytope,singletonFunction,e] using hh
    · intro huv
      obtain ⟨S,hu,hv,hd⟩ := hslack' huv
      apply exposedSegment_of_positive_delta hn'.1 hs' ((singletonGraph a).ne_of_adj huv) hu hv
      exact lt_of_le_of_ne (hs'.elemental u v ((singletonGraph a).ne_of_adj huv) S hu hv) (Ne.symm hd)
  · intro u v huv S hu hv
    rw [singletonPolytope,lowerSupport_basePolytope hn.1 hs,
      SetFunctionEmbedding.delta_restrict]
    exact setFunction_boolean (fun he => huv (Subtype.ext he)) (fun hm => hu ((Finset.mem_map' (VertexDeletion.embedding (a,(1 : Fin 2)))).mp hm)) (fun hm => hv ((Finset.mem_map' (VertexDeletion.embedding (a,(1 : Fin 2)))).mp hm))
  · intro u v huv S hu hv
    rw [singletonComplementPolytope,lowerSupport_basePolytope hn'.1 hs',
      SetFunctionEmbedding.delta_restrict]
    have h : BooleanElemental (complementPolytope (I := I)) := complementPolytope_booleanElemental
    rw [BooleanElemental,complementPolytope,
      lowerSupport_basePolytope complementFunction_translationNormalized.1 complementFunction_supermodular] at h
    exact h (e u) (e v) (fun he => huv (Subtype.ext he)) (S.map e)
      (fun hm => hu ((Finset.mem_map' (VertexDeletion.embedding (a,(1 : Fin 2)))).mp hm)) (fun hm => hv ((Finset.mem_map' (VertexDeletion.embedding (a,(1 : Fin 2)))).mp hm))

theorem singleton_dimension (hI : 4≤ Fintype.card I) (a : I) :
    Module.finrank ℝ (vectorSpan ℝ (singletonPolytope a))=2*Fintype.card I-2 ∧
    Module.finrank ℝ (vectorSpan ℝ (singletonComplementPolytope a))=2*Fintype.card I-2 := by
  have h := one_singleton_decomposition hI a
  have hQ := h.2.2.2.2.1
  have hR := h.2.2.2.2.2.1
  have hc : Fintype.card (SingletonVertices a)=Fintype.card I*2-1 := by
    rw [card_ne_subtype]
    simp
  change Module.finrank ℝ (vectorSpan ℝ (singletonPolytope a))=
    Fintype.card (SingletonVertices a)-1 at hQ
  change Module.finrank ℝ (vectorSpan ℝ (singletonComplementPolytope a))=
    Fintype.card (SingletonVertices a)-1 at hR
  rw [hc] at hQ hR
  constructor <;> omega

end DoubledParts
end GraphicalZonotopes

end
end
end BundlePart258

section BundlePart259
/- Source: Papers/GraphicalZonotopes/DoubledPairData.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem complementFunction_boolean {u v : I×Fin 2} (huv : u≠ v)
    {S : Finset (I×Fin 2)} (hu : u∉S) (hv : v∉S) :
    delta complementFunction u v S=0 ∨ delta complementFunction u v S=1 := by
  have h := complementPolytope_booleanElemental (I := I)
  rw [BooleanElemental,complementPolytope,
    lowerSupport_basePolytope complementFunction_translationNormalized.1 complementFunction_supermodular] at h
  exact h u v huv S hu hv

def doubledPairData (hI : 4≤ Fintype.card I) : BooleanPairData (graph I) where
  left := setFunction
  right := complementFunction
  left_extreme := setFunction_extreme hI
  right_extreme := complementFunction_extreme hI
  left_integer := setFunction_integerValued
  right_integer := complementFunction_integerValued
  pair_sum := by unfold complementFunction; abel
  left_boolean := fun _ _ huv _ hu hv => setFunction_boolean huv hu hv
  right_boolean := fun _ _ huv _ hu hv => complementFunction_boolean huv hu hv
  left_direction := fun _ _ h => setFunction_nonzero_slack (by omega) h
  right_direction := fun _ _ h => complementFunction_nonzero_slack (by omega) h

def singletonPairData (hI : 4≤ Fintype.card I) (a : I) : BooleanPairData (singletonGraph a) where
  left := singletonFunction a setFunction
  right := singletonFunction a complementFunction
  left_extreme := singleton_extreme hI a setFunction_translationNormalized setFunction_supermodular
    setFunction_graphical setFunction_completeQuadraticRows
    (fun _ hc hC => mobius_setFunction_four_ne_zero hc hC)
  right_extreme := singleton_extreme hI a complementFunction_translationNormalized complementFunction_supermodular
    complementFunction_graphical complementFunction_completeQuadraticRows
    (fun _ hc hC => mobius_complementFunction_four_ne_zero hc hC)
  left_integer := SetFunctionEmbedding.integerValued_restrict _ setFunction_integerValued
  right_integer := SetFunctionEmbedding.integerValued_restrict _ complementFunction_integerValued
  pair_sum := by
    rw [singletonFunction,singletonFunction,← SetFunctionEmbedding.restrict_add]
    rw [show setFunction+complementFunction=graphFunction (graph I) by unfold complementFunction; abel]
    exact SetFunctionEmbedding.graphFunction_restrict (VertexDeletion.embedding (a,(1 : Fin 2))) (graph I)
  left_boolean := by
    intro u v huv S hu hv
    rw [singletonFunction,SetFunctionEmbedding.delta_restrict]
    exact setFunction_boolean (fun he => huv (Subtype.ext he)) (fun hm => hu ((Finset.mem_map' (VertexDeletion.embedding (a,(1 : Fin 2)))).mp hm)) (fun hm => hv ((Finset.mem_map' (VertexDeletion.embedding (a,(1 : Fin 2)))).mp hm))
  right_boolean := by
    intro u v huv S hu hv
    rw [singletonFunction,SetFunctionEmbedding.delta_restrict]
    exact complementFunction_boolean (fun he => huv (Subtype.ext he)) (fun hm => hu ((Finset.mem_map' (VertexDeletion.embedding (a,(1 : Fin 2)))).mp hm)) (fun hm => hv ((Finset.mem_map' (VertexDeletion.embedding (a,(1 : Fin 2)))).mp hm))
  left_direction := fun _ _ h => singleton_nonzero_slack hI a setFunction_completeQuadraticRows h
  right_direction := fun _ _ h => singleton_nonzero_slack hI a complementFunction_completeQuadraticRows h

end DoubledParts
end GraphicalZonotopes

end
end
end BundlePart259

section BundlePart260
/- Source: Papers/GraphicalZonotopes/FourSmallParts.lean -/








@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace FourSmallParts
open Finset

/-- There is always the zero-labelled vertex of each part; precisely the
parts in `s` also have their one-labelled vertex. -/
abbrev Vertices (s : Finset (Fin 4)) :=
  {v : Fin 4×Fin 2 // v.2=0 ∨ v.1∈s}

def graph (s : Finset (Fin 4)) : SimpleGraph (Vertices s) :=
  (DoubledParts.graph (Fin 4)).comap Subtype.val

def canonicalParts (d : ℕ) : Finset (Fin 4) := (univ : Finset (Fin 4)).filter (fun i => (4 - d : ℕ) ≤ i.val)

theorem canonicalParts_card {d : ℕ} (hd : d≤4) : (canonicalParts d).card=d := by
  interval_cases d <;> decide

def canonicalZeroEquiv : Vertices (canonicalParts 0) ≃ Fin 4 :=
  Equiv.ofBijective (fun v => v.1.1) (by decide)

def canonicalOneMap (v : Vertices (canonicalParts 1)) : Fin 5 :=
  ⟨if v.1.1=3 then 3+v.1.2.val else v.1.1.val,by
    have hi := v.1.1.isLt
    have hb := v.1.2.isLt
    split <;> omega⟩

def canonicalOneEquiv : Vertices (canonicalParts 1) ≃ Fin 5 :=
  Equiv.ofBijective canonicalOneMap (by decide)

def canonicalTwoMap (v : Vertices (canonicalParts 2)) : Fin 6 :=
  ⟨if v.1.1.val<2 then v.1.1.val else 2*v.1.1.val-2+v.1.2.val,by
    have hi := v.1.1.isLt
    have hb := v.1.2.isLt
    split <;> omega⟩

def canonicalTwoEquiv : Vertices (canonicalParts 2) ≃ Fin 6 :=
  Equiv.ofBijective canonicalTwoMap (by decide)

def canonicalThreeEquiv : Vertices (canonicalParts 3) ≃ DoubledParts.SingletonVertices (0 : Fin 4) :=
  Equiv.subtypeEquivRight (by decide)

def canonicalFourEquiv : Vertices (canonicalParts 4) ≃ Fin 4×Fin 2 :=
  Equiv.subtypeUnivEquiv (by decide)

theorem canonicalZero_graph : SmallBoolean.K4.graph.comap canonicalZeroEquiv=graph (canonicalParts 0) := by
  have h : ∀ u v : Vertices (canonicalParts 0),
      SmallBoolean.K4.part (canonicalZeroEquiv u)≠ SmallBoolean.K4.part (canonicalZeroEquiv v) ↔
        u.1.1≠ v.1.1 := by decide
  ext u v
  exact h u v

theorem canonicalOne_graph : SmallBoolean.K1112.graph.comap canonicalOneEquiv=graph (canonicalParts 1) := by
  have h : ∀ u v : Vertices (canonicalParts 1),
      SmallBoolean.K1112.part (canonicalOneEquiv u)≠ SmallBoolean.K1112.part (canonicalOneEquiv v) ↔
        u.1.1≠ v.1.1 := by decide
  ext u v
  exact h u v

theorem canonicalTwo_graph : SmallBoolean.K1122.graph.comap canonicalTwoEquiv=graph (canonicalParts 2) := by
  have h : ∀ u v : Vertices (canonicalParts 2),
      SmallBoolean.K1122.part (canonicalTwoEquiv u)≠ SmallBoolean.K1122.part (canonicalTwoEquiv v) ↔
        u.1.1≠ v.1.1 := by decide
  ext u v
  exact h u v

theorem canonicalThree_graph : (DoubledParts.singletonGraph (0 : Fin 4)).comap canonicalThreeEquiv=
    graph (canonicalParts 3) := by
  ext u v
  rfl

theorem canonicalFour_graph : (DoubledParts.graph (Fin 4)).comap canonicalFourEquiv=
    graph (canonicalParts 4) := by
  ext u v
  rfl

def canonicalPair (d : ℕ) (hd : d≤4) : BooleanPairData (graph (canonicalParts d)) := by
  interval_cases d
  · simpa only [canonicalZero_graph] using SmallBoolean.K4.pairData.relabel canonicalZeroEquiv
  · simpa only [canonicalOne_graph] using SmallBoolean.K1112.pairData.relabel canonicalOneEquiv
  · simpa only [canonicalTwo_graph] using SmallBoolean.K1122.pairData.relabel canonicalTwoEquiv
  · simpa only [canonicalThree_graph] using
      (DoubledParts.singletonPairData (I := Fin 4) (by decide) 0).relabel canonicalThreeEquiv
  · simpa only [canonicalFour_graph] using
      (DoubledParts.doubledPairData (I := Fin 4) (by decide)).relabel canonicalFourEquiv

def permuteParts {s t : Finset (Fin 4)} (σ : Equiv.Perm (Fin 4))
    (hσ : s.map σ.toEmbedding=t) : Vertices s ≃ Vertices t :=
  (σ.prodCongr (Equiv.refl (Fin 2))).subtypeEquiv (by
    intro v
    rw [← hσ]
    simp)

theorem graph_permuteParts {s t : Finset (Fin 4)} (σ : Equiv.Perm (Fin 4))
    (hσ : s.map σ.toEmbedding=t) : (graph t).comap (permuteParts σ hσ)=graph s := by
  ext u v
  change (σ u.1.1≠ σ v.1.1) ↔ (u.1.1≠ v.1.1)
  exact not_congr σ.injective.eq_iff

/-- Every one of the sixteen part patterns is covered. The reduction uses an
actual permutation of the four parts and an equivalence of all real cones. -/
def pairData (s : Finset (Fin 4)) : BooleanPairData (graph s) := by
  have hd : s.card≤4 := by simpa using card_le_card (subset_univ s)
  have hex := Equiv.Perm.exists_map_finset_eq s (canonicalParts s.card)
    (canonicalParts_card hd).symm
  let σ := Classical.choose hex
  have hσ := Classical.choose_spec hex
  simpa only [graph_permuteParts] using (canonicalPair s.card hd).relabel (permuteParts σ hσ)

def doubledParts (a : Fin 4 → ℕ) : Finset (Fin 4) := univ.filter fun i => a i=2

def partSizeEquiv (a : Fin 4 → ℕ) (ha : ∀ i,a i=1 ∨ a i=2) :
    (Σ i : Fin 4,Fin (a i)) ≃ Vertices (doubledParts a) where
  toFun v := ⟨(v.1,⟨v.2.val,by rcases ha v.1 with h | h <;> have hv := v.2.isLt <;> omega⟩),by
    rcases ha v.1 with h | h
    · left
      apply Fin.ext
      change v.2.val=0
      have hv := v.2.isLt
      omega
    · right
      simp [doubledParts,h]⟩
  invFun v := ⟨v.1.1,⟨v.1.2.val,by
    rcases ha v.1.1 with h | h
    · have hb : v.1.2=0 := by
        rcases v.2 with hb | hm
        · exact hb
        · have hm' : a v.1.1=2 := by simpa [doubledParts] using hm
          omega
      simp [h,hb]
    · have hb := v.1.2.isLt
      omega⟩⟩
  left_inv v := by
    rcases v with ⟨i,b⟩
    congr 1
  right_inv v := by
    apply Subtype.ext
    exact Prod.ext rfl (Fin.ext rfl)

theorem graph_partSizeEquiv (a : Fin 4 → ℕ) (ha : ∀ i,a i=1 ∨ a i=2) :
    (graph (doubledParts a)).comap (partSizeEquiv a ha)=fourPartite a := by
  ext u v
  rfl

theorem fourPartite_connected (a : Fin 4 → ℕ) (ha : ∀ i,0< a i) :
    (fourPartite a).Connected := by
  letI : Nonempty (Σ i : Fin 4,Fin (a i)) := ⟨⟨0,⟨0,ha 0⟩⟩⟩
  refine ⟨?_⟩
  intro u v
  by_cases huv : u.1≠ v.1
  · exact SimpleGraph.Adj.reachable huv
  · have he : u.1=v.1 := not_not.mp huv
    let i : Fin 4 := if u.1=0 then 1 else 0
    have hi : i≠ u.1 := by
      dsimp [i]
      split_ifs with h
      · simp [h]
      · exact Ne.symm h
    let w : Σ i : Fin 4,Fin (a i) := ⟨i,⟨0,ha i⟩⟩
    exact (SimpleGraph.Adj.reachable (show (fourPartite a).Adj u w from Ne.symm hi)).trans
      (SimpleGraph.Adj.reachable (show (fourPartite a).Adj w v from by change i≠ v.1; rwa [← he]))

/-- Corollary9.11, with its original arbitrary four part sizes and actual
Minkowski equality in the standard integer coordinate lattice. -/
theorem four_small_parts_decomposition : Targets.FourSmallPartsDecomposition := by
  intro a ha
  have hconn := fourPartite_connected a (fun i => by rcases ha i with h | h <;> omega)
  let D : BooleanPairData (fourPartite a) := by
    simpa only [graph_partSizeEquiv] using (pairData (doubledParts a)).relabel (partSizeEquiv a ha)
  exact ⟨basePolytope D.left,basePolytope D.right,D.geometric_pair hconn⟩

end FourSmallParts
end GraphicalZonotopes

end
end
end BundlePart260

section BundlePart261
/- Source: Papers/GraphicalZonotopes/BooleanAllDimensions.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped Pointwise

theorem booleanPair_on_fin {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (D : BooleanPairData G) (hG : G.Connected)
    {n : ℕ} (hc : Fintype.card V=n) :
    ∃ H : SimpleGraph (Fin n),H.Connected ∧ Nonempty (BooleanPairData H) := by
  let e : Fin n ≃ V := Fintype.equivOfCardEq (by simpa using hc.symm)
  let E : G.comap e ≃g G := {toEquiv := e,map_rel_iff' := by intros; rfl}
  exact ⟨G.comap e,E.connected_iff.mpr hG,⟨D.relabel e⟩⟩

theorem SmallBoolean.partGraph_connected {n : ℕ} (part : Fin n → Fin 4)
    (z o : Fin n) (hzo : part z≠ part o) : (SmallBoolean.partGraph part).Connected := by
  letI : Nonempty (Fin n) := ⟨z⟩
  refine ⟨?_⟩
  intro u v
  by_cases huv : part u≠ part v
  · exact SimpleGraph.Adj.reachable huv
  · have he : part u=part v := not_not.mp huv
    by_cases huz : part u=part z
    · exact (SimpleGraph.Adj.reachable (show (SmallBoolean.partGraph part).Adj u o from
        by change part u≠ part o; simpa [huz] using hzo)).trans
        (SimpleGraph.Adj.reachable (show (SmallBoolean.partGraph part).Adj o v from
          by change part o≠ part v; simpa [← he,huz] using Ne.symm hzo))
    · exact (SimpleGraph.Adj.reachable (show (SmallBoolean.partGraph part).Adj u z from huz)).trans
        (SimpleGraph.Adj.reachable (show (SmallBoolean.partGraph part).Adj z v from
          by change part z≠ part v; simpa [← he] using Ne.symm huz))

theorem booleanPair_every_vertex_count {n : ℕ} (hn : 4≤ n) :
    ∃ G : SimpleGraph (Fin n),G.Connected ∧ Nonempty (BooleanPairData G) := by
  by_cases hn4 : n=4
  · subst n
    exact ⟨SmallBoolean.K4.graph,
      SmallBoolean.partGraph_connected SmallBoolean.K4.part 0 1 (by decide),
      ⟨SmallBoolean.K4.pairData⟩⟩
  by_cases hn5 : n=5
  · subst n
    exact ⟨SmallBoolean.K1112.graph,
      SmallBoolean.partGraph_connected SmallBoolean.K1112.part 0 1 (by decide),
      ⟨SmallBoolean.K1112.pairData⟩⟩
  by_cases hn6 : n=6
  · subst n
    exact ⟨SmallBoolean.K1122.graph,
      SmallBoolean.partGraph_connected SmallBoolean.K1122.part 0 1 (by decide),
      ⟨SmallBoolean.K1122.pairData⟩⟩
  have hn7 : 7≤ n := by omega
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨r,hr⟩ := he
    have hr4 : 4≤ r := by omega
    exact booleanPair_on_fin (DoubledParts.doubledPairData (I := Fin r) (by simpa using hr4))
      (DoubledParts.graph_connected (by simpa using (show 2≤ r by omega))) (by
        simp only [Fintype.card_prod,Fintype.card_fin]
        omega)
  · obtain ⟨r,hr⟩ := ho
    have hr4 : 4≤ r+1 := by omega
    let a : Fin (r+1) := 0
    apply booleanPair_on_fin
      (DoubledParts.singletonPairData (I := Fin (r+1)) (by simpa using hr4) a)
      (DoubledParts.singletonGraph_connected (by simpa using (show 2≤ r+1 by omega)) a)
    change Fintype.card {v : Fin (r+1)×Fin 2 // v≠(a,1)}=n
    rw [card_ne_subtype]
    simp only [Fintype.card_prod,Fintype.card_fin]
    omega

/-- The unbounded final consequence of Corollary9.11: both summands are
actual lattice polytopes in every dimension at least three. -/
theorem boolean_decomposition_every_dimension {d : ℕ} (hd : 3≤ d) :
    ∃ G : SimpleGraph (Fin (d+1)),∃ Q R : Set (Fin (d+1) → ℝ),
      LatticePolytope Q ∧ LatticePolytope R ∧
      MinkowskiIndecomposable Q ∧ MinkowskiIndecomposable R ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=d ∧ Module.finrank ℝ (vectorSpan ℝ R)=d ∧
      Q+R=graphicalZonotope G ∧ BooleanElemental Q ∧ BooleanElemental R := by
  obtain ⟨G,hG,⟨D⟩⟩ := booleanPair_every_vertex_count (show 4≤ d+1 by omega)
  obtain ⟨hL,hR,hI,hJ,hD,hE,hS,hgraph,hgraph',hB,hB'⟩ := D.geometric_pair hG
  refine ⟨G,basePolytope D.left,basePolytope D.right,hL,hR,hI,hJ,?_,?_,hS,hB,hB'⟩
  · simpa only [FullDimension,Fintype.card_fin,Nat.add_sub_cancel] using hD
  · simpa only [FullDimension,Fintype.card_fin,Nat.add_sub_cancel] using hE

end GraphicalZonotopes

end
end
end BundlePart261

section BundlePart262
/- Source: Papers/GraphicalZonotopes/IntegralForestOscillation.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace ForestSigns
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

def bitVector (b : V → Bool) : V → ℝ := fun v => if b v then 1 else 0

theorem bitVector_boolean (b : V → Bool) : ∀ v,bitVector b v=0 ∨ bitVector b v=1 := by
  intro v
  cases h : b v <;> simp [bitVector,h]

theorem exists_bitVector (x : V → ℝ) (hx : ∀ v,x v=0 ∨ x v=1) :
    ∃ b : V → Bool,bitVector b=x := by
  refine ⟨fun v => decide (x v=1),?_⟩
  funext v
  rcases hx v with h | h <;> simp [bitVector,h]

/-- The integer rounding in Lemma9.3. The bounding interval may have real
endpoints; integrality is required only of the actual Boolean polynomial values. -/
theorem integral_quadratic_oscillation_lower (G : SimpleGraph V) (hG : G.IsAcyclic)
    (c : ℝ) (l : V → ℝ) (w : Sym2 V → ℝ) (lo hi : ℝ)
    (hbound : ∀ x : V → ℝ,(∀ v,x v=0 ∨ x v=1) →
      lo≤ quadratic G c l w x ∧ quadratic G c l w x≤ hi)
    (hint : ∀ x : V → ℝ,(∀ v,x v=0 ∨ x v=1) →
      ∃ k : ℤ,quadratic G c l w x=k) :
    (Int.ceil ((1/2 : ℝ)*(∑ e ∈ G.edgeFinset,|w e|)) : ℝ)≤ hi-lo := by
  let F : (V → Bool) → ℝ := fun b => quadratic G c l w (bitVector b)
  obtain ⟨bmin,hbmin,hmin⟩ := exists_min_image (univ : Finset (V → Bool)) F univ_nonempty
  obtain ⟨bmax,hbmax,hmax⟩ := exists_max_image (univ : Finset (V → Bool)) F univ_nonempty
  obtain ⟨kmin,hkmin⟩ := hint (bitVector bmin) (bitVector_boolean bmin)
  obtain ⟨kmax,hkmax⟩ := hint (bitVector bmax) (bitVector_boolean bmax)
  have hactual : ∀ x : V → ℝ,(∀ v,x v=0 ∨ x v=1) →
      (kmin : ℝ)≤ quadratic G c l w x ∧ quadratic G c l w x≤ kmax := by
    intro x hx
    obtain ⟨b,rfl⟩ := exists_bitVector x hx
    have h₁ := hmin b (mem_univ b)
    have h₂ := hmax b (mem_univ b)
    change quadratic G c l w (bitVector bmin)≤ _ at h₁
    change _≤ quadratic G c l w (bitVector bmax) at h₂
    rw [hkmin] at h₁
    rw [hkmax] at h₂
    exact ⟨h₁,h₂⟩
  have hosc := quadratic_oscillation_lower G hG c l w (kmin : ℝ) (kmax : ℝ) hactual
  have hceil : Int.ceil ((1/2 : ℝ)*(∑ e ∈ G.edgeFinset,|w e|))≤ kmax-kmin := by
    apply Int.ceil_le.mpr
    simpa only [Int.cast_sub] using hosc
  have hcast : (Int.ceil ((1/2 : ℝ)*(∑ e ∈ G.edgeFinset,|w e|)) : ℝ)≤
      (kmax : ℝ)-(kmin : ℝ) := by exact_mod_cast hceil
  have hminbound := (hbound (bitVector bmin) (bitVector_boolean bmin)).1
  have hmaxbound := (hbound (bitVector bmax) (bitVector_boolean bmax)).2
  rw [hkmin] at hminbound
  rw [hkmax] at hmaxbound
  linarith

end ForestSigns
end GraphicalZonotopes

end
end
end BundlePart262

section BundlePart263
/- Source: Papers/GraphicalZonotopes/ThreeTreeSlack.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem edgeLink_pair_vertices {G : SimpleGraph V} {u v : V} {C : Finset V}
    (hC : C∈edgeFamily (edgeLink G u v)) :
    u∉C ∧ v∉C ∧ ∀ a∈C,G.Adj u a ∧ G.Adj v a := by
  obtain ⟨hc,hcl⟩ := (mem_edgeFamily _ C).mp hC
  obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hc
  have h := (pair_mem_edgeFamily (edgeLink G u v) hab).mp hC
  have hall : ∀ w∈({a,b} : Finset V),G.Adj u w ∧ G.Adj v w := by
    intro w hw
    rcases mem_insert.mp hw with rfl | hw
    · exact ⟨h.2.1,h.2.2.1⟩
    · have hw' := mem_singleton.mp hw
      subst w
      exact ⟨h.2.2.2.1,h.2.2.2.2⟩
  exact ⟨fun hu => G.irrefl (hall u hu).1,
    fun hv => G.irrefl (hall v hv).2,hall⟩

/-- Link edges and tetrahedra containing the original edge are in exact
bijection. The equality applies to arbitrary real weights. -/
theorem sum_edgeLink_tetrahedra {G : SimpleGraph V} {u v : V} (huv : G.Adj u v)
    (f : Finset V → ℝ) :
    (∑ e∈(edgeLink G u v).edgeFinset,f (insert u (insert v e.toFinset)))=
      ∑ C∈(tetrahedra G).filter (fun C => ({u,v} : Finset V)⊆C),f C := by
  classical
  rw [← sum_edgeFamily_eq (edgeLink G u v) (fun e => f (insert u (insert v e)))]
  apply sum_bij (fun C _ => insert u (insert v C))
  · intro C hC
    obtain ⟨huC,hvC,hverts⟩ := edgeLink_pair_vertices hC
    obtain ⟨hcard,hcl⟩ := (mem_edgeFamily _ C).mp hC
    apply mem_filter.mpr
    refine ⟨mem_filter.mpr ⟨mem_univ _,?_,?_⟩,by simp⟩
    · rw [card_insert_of_notMem (by simp [G.ne_of_adj huv,huC]),
        card_insert_of_notMem hvC,hcard]
    · have hc : G.IsClique C := fun a ha b hb hab => (hcl a ha b hb hab).1
      have hvcl : G.IsClique (insert v C : Finset V) := by
        simpa only [Finset.coe_insert] using hc.insert (fun a ha _ => (hverts a ha).2)
      simpa only [Finset.coe_insert] using hvcl.insert (by
        intro a ha hna
        rcases mem_insert.mp ha with rfl | ha
        · exact huv
        · exact (hverts a ha).1)
  · intro C hC D hD he
    obtain ⟨huC,hvC,_⟩ := edgeLink_pair_vertices hC
    obtain ⟨huD,hvD,_⟩ := edgeLink_pair_vertices hD
    have hh:=congrArg (fun E : Finset V => (E.erase u).erase v) he
    simpa [G.ne_of_adj huv,huC,hvC,huD,hvD] using hh
  · intro C hC
    obtain ⟨hC,hpair⟩ := mem_filter.mp hC
    obtain ⟨hcard,hcl⟩ := (mem_filter.mp hC).2
    have huC : u∈C := hpair (by simp)
    have hvC : v∈C := hpair (by simp)
    let D:=(C.erase u).erase v
    have hDcard : D.card=2 := by
      rw [card_erase_of_mem (mem_erase.mpr ⟨Ne.symm (G.ne_of_adj huv),hvC⟩),
        card_erase_of_mem huC,hcard]
    have hDcl : (edgeLink G u v).IsClique D := by
      intro a ha b hb hab
      have haC := mem_of_mem_erase (mem_of_mem_erase ha)
      have hbC := mem_of_mem_erase (mem_of_mem_erase hb)
      have hau := ne_of_mem_erase (mem_of_mem_erase ha)
      have hav := ne_of_mem_erase ha
      have hbu := ne_of_mem_erase (mem_of_mem_erase hb)
      have hbv := ne_of_mem_erase hb
      exact ⟨hcl haC hbC hab,hcl huC haC (Ne.symm hau),hcl hvC haC (Ne.symm hav),
        hcl huC hbC (Ne.symm hbu),hcl hvC hbC (Ne.symm hbv)⟩
    refine ⟨D,(mem_edgeFamily _ D).mpr ⟨hDcard,hDcl⟩,?_⟩
    ext a
    by_cases hau : a=u <;> by_cases hav : a=v <;> simp [D,hau,hav,huC,hvC]
  · intro C hC
    rfl

theorem sum_edgeCoefficients_abs {G : SimpleGraph V} {u v : V} (huv : G.Adj u v)
    (y : SetFunction V) :
    (∑ e∈(edgeLink G u v).edgeFinset,|edgeCoefficients y u v e.toFinset|)=
      ∑ C∈(tetrahedra G).filter (fun C => ({u,v} : Finset V)⊆C),|y C| := by
  classical
  rw [← sum_edgeLink_tetrahedra huv (fun C => |y C|)]
  apply sum_congr rfl
  intro e he
  have hmem : e.toFinset∈edgeFamily (edgeLink G u v) := by
    rw [edgeFamily_eq_image_edgeFinset]
    exact mem_image.mpr ⟨e,he,rfl⟩
  obtain ⟨hu,hv,_⟩ := edgeLink_pair_vertices hmem
  simp [edgeCoefficients,hu,hv]

/-- The exact integer-ceiling edge bound in Theorem9.1, with arbitrary
constant and triangle coefficients retained in the actual elemental row. -/
theorem threeTree_integral_slack_bound {S : Finset V} {G : SimpleGraph V}
    (hG : ThreeTreeOn S G) {z : SetFunction V}
    (hz : Supermodular z) (hint : IntegerValued z)
    (hy : CliqueSupported G (mobius z)) {a : ℝ}
    (hbound : ∀ u v,u≠ v → G.Adj u v → ∀ T,u∉T → v∉T → delta z u v T≤ a)
    {u v : V} (huv : G.Adj u v) :
    (Int.ceil ((1/2 : ℝ)*
      ∑ C∈(tetrahedra G).filter (fun C => ({u,v} : Finset V)⊆C),|mobius z C|) : ℝ)≤ a := by
  classical
  have hne := G.ne_of_adj huv
  let g:=edgeCoefficients (mobius z) u v
  have heval (x : V → ℝ) (hx : ∀ w,x w=0 ∨ x w=1) :
      ForestSigns.quadratic (edgeLink G u v) (g ∅)
        (fun w => g {w}) (fun e => g e.toFinset) x=
        delta z u v (((booleanSupport x).erase u).erase v) := by
    simpa only [zeta_mobius] using edgeCoefficients_boolean_quadratic hy
      (fun C hc => hG.clique_card_le_four hc) hne x hx
  have hinterval : ∀ x : V → ℝ,(∀ w,x w=0 ∨ x w=1) →
      0≤ ForestSigns.quadratic (edgeLink G u v) (g ∅)
        (fun w => g {w}) (fun e => g e.toFinset) x ∧
      ForestSigns.quadratic (edgeLink G u v) (g ∅)
        (fun w => g {w}) (fun e => g e.toFinset) x≤ a := by
    intro x hx
    rw [heval x hx]
    exact ⟨hz.elemental u v hne _ (by simp) (by simp),
      hbound u v hne huv _ (by simp) (by simp)⟩
  have hinteger : ∀ x : V → ℝ,(∀ w,x w=0 ∨ x w=1) →
      ∃ k : ℤ,ForestSigns.quadratic (edgeLink G u v) (g ∅)
        (fun w => g {w}) (fun e => g e.toFinset) x=k := by
    intro x hx
    rw [heval x hx]
    exact hint.delta u v _
  have hosc := ForestSigns.integral_quadratic_oscillation_lower (edgeLink G u v)
    (hG.edgeLink_acyclic huv) (g ∅) (fun w => g {w}) (fun e => g e.toFinset)
    0 a hinterval hinteger
  simpa only [g,sum_edgeCoefficients_abs huv (mobius z),sub_zero] using hosc

end GraphicalZonotopes

end
end
end BundlePart263

section BundlePart264
/- Source: Papers/GraphicalZonotopes/TetrahedralTriple.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A connected finite graph with at least three vertices contains a path of
length two with distinct endpoints. No acyclicity is assumed. -/
theorem preconnected_three_path (G : SimpleGraph V) (hG : G.Preconnected)
    (hcard : 3≤ Fintype.card V) : ∃ a b c : V,a≠ c ∧ G.Adj a b ∧ G.Adj b c := by
  classical
  by_contra hnot
  have hthin : ∀ a b c : V,G.Adj a b → G.Adj b c → a=c := by
    intro a b c hab hbc
    by_contra hne
    exact hnot ⟨a,b,c,hne,hab,hbc⟩
  have hne : (univ : Finset V).Nonempty := card_pos.mp (by simpa using (show 0< Fintype.card V by omega))
  obtain ⟨a,ha⟩ := hne
  obtain ⟨c,hc,hca⟩ := exists_mem_ne (s:=(univ : Finset V))
    (by simpa using (show 1< Fintype.card V by omega)) a
  obtain ⟨b,hab⟩ := (hG a c).nonempty_neighborSet_left (Ne.symm hca)
  have hall : ∀ x : V,x=a ∨ x=b := by
    intro x
    have hp := (SimpleGraph.reachable_iff_reflTransGen (G:=G) a x).mp (hG a x)
    induction hp with
    | refl => exact Or.inl rfl
    | @tail y z hp hyz ih =>
      rcases ih with hy | hy
      · subst y
        exact Or.inr (hthin b a z (G.adj_symm hab) hyz).symm
      · subst y
        exact Or.inl (hthin a b z hab hyz).symm
  have hsub : (univ : Finset V)⊆{a,b} := by intro x hx; simpa using hall x
  have hb := card_le_card hsub
  have hpair : ({a,b} : Finset V).card≤2 := card_le_two
  rw [card_univ] at hb
  omega

/-- Three successive tetrahedra contain a common pair: their two shared
triangles intersect inside the middle four-element set. -/
theorem tetrahedra_path_shared_pair {A B C : Finset V} (hB : B.card=4)
    (hAB : 3≤(A∩B).card) (hBC : 3≤(B∩C).card) :
    ∃ e : Finset V,e.card=2 ∧ e⊆A ∧ e⊆B ∧ e⊆C := by
  have hunion : (A∩B)∪(B∩C)⊆B := by
    intro v hv
    rcases mem_union.mp hv with h | h
    · exact (mem_inter.mp h).2
    · exact (mem_inter.mp h).1
  have hub := card_le_card hunion
  have hsum := card_union_add_card_inter (A∩B) (B∩C)
  have hcommon : 2≤((A∩B)∩(B∩C)).card := by omega
  obtain ⟨e,he,hcard⟩ := exists_subset_card_eq hcommon
  refine ⟨e,hcard,?_,?_,?_⟩
  · intro v hv
    exact (mem_inter.mp (mem_inter.mp (he hv)).1).1
  · intro v hv
    exact (mem_inter.mp (mem_inter.mp (he hv)).1).2
  · intro v hv
    exact (mem_inter.mp (mem_inter.mp (he hv)).2).2

/-- The purely combinatorial step yielding the sharp integer dilation2:
a connected family of at least three tetrahedra has a pair contained in at
least three distinct members. -/
theorem connected_tetrahedra_pair_multiplicity (F : Finset (Finset V))
    (hfour : ∀ C∈F,C.card=4) (hconn : (tetrahedronGraph F).Preconnected)
    (hcard : 3≤ F.card) :
    ∃ e : Finset V,e.card=2 ∧ 3≤(F.filter (fun C => e⊆C)).card := by
  classical
  have hc : 3≤ Fintype.card {C : Finset V // C∈F} := by simpa using hcard
  obtain ⟨A,B,C,hAC,hAB,hBC⟩ := preconnected_three_path (tetrahedronGraph F) hconn hc
  obtain ⟨e,he,heA,heB,heC⟩ := tetrahedra_path_shared_pair
    (hfour B.val B.property) hAB.2 hBC.2
  refine ⟨e,he,?_⟩
  have hAB' : A.val≠ B.val := fun he => hAB.1 (Subtype.ext he)
  have hAC' : A.val≠ C.val := fun he => hAC (Subtype.ext he)
  have hBC' : B.val≠ C.val := fun he => hBC.1 (Subtype.ext he)
  have hsub : ({A.val,B.val,C.val} : Finset (Finset V))⊆F.filter (fun D => e⊆D) := by
    intro D hD
    simp only [mem_insert,mem_singleton] at hD
    rcases hD with rfl | rfl | rfl
    · exact mem_filter.mpr ⟨A.property,heA⟩
    · exact mem_filter.mpr ⟨B.property,heB⟩
    · exact mem_filter.mpr ⟨C.property,heC⟩
  have hcount := card_le_card hsub
  simpa [hAB',hAC',hBC'] using hcount

end GraphicalZonotopes

end
end
end BundlePart264

section BundlePart265
/- Source: Papers/GraphicalZonotopes/PathCoefficients.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace Path
open Finset
open scoped BigOperators

theorem window_eq_iff {n i j : ℕ} {T U : Finset ℕ} (hT0 : 0 ∈ T) (hU0 : 0 ∈ U)
    (hT : ∀ k ∈ T, i + k < n) (hU : ∀ k ∈ U, j + k < n) :
    window n i T = window n j U ↔ i = j ∧ T = U := by
  have hi : i < n := by simpa using hT 0 hT0
  have hj : j < n := by simpa using hU 0 hU0
  constructor
  · intro he
    have hiM : (⟨i, hi⟩ : Fin n) ∈ window n i T := by simp [hT0]
    have hjM : (⟨j, hj⟩ : Fin n) ∈ window n j U := by simp [hU0]
    rw [he] at hiM
    rw [← he] at hjM
    have hij : i = j := le_antisymm ((mem_window n i T _).mp hjM).1
      ((mem_window n j U _).mp hiM).1
    refine ⟨hij, ?_⟩
    subst j
    ext k
    constructor
    · intro hk
      have hkM : (⟨i+k, hT k hk⟩ : Fin n) ∈ window n i T := by simp [hk]
      rw [he] at hkM
      simpa using ((mem_window n i U _).mp hkM).2
    · intro hk
      have hkM : (⟨i+k, hU k hk⟩ : Fin n) ∈ window n i U := by simp [hk]
      rw [← he] at hkM
      simpa using ((mem_window n i T _).mp hkM).2
  · rintro ⟨rfl, rfl⟩
    rfl

theorem window_clique {n i : ℕ} {T : Finset ℕ} (hT : T ⊆ {0,1,2,3}) :
    ∀ u ∈ window n i T, ∀ v ∈ window n i T, u ≠ v → (graph n).Adj u v := by
  intro u hu v hv huv
  obtain ⟨hu0, huT⟩ := (mem_window n i T u).mp hu
  obtain ⟨hv0, hvT⟩ := (mem_window n i T v).mp hv
  have h1 := hT huT
  have h2 := hT hvT
  simp only [mem_insert, mem_singleton] at h1 h2
  exact ⟨huv, by omega, by omega⟩

def coefficients (n : ℕ) : SetFunction (Fin n) :=
  (∑ i : Fin (n-2), Pi.single (window n i.val {0,1,2}) 1) +
  (∑ i : Fin (n-3), Pi.single (window n i.val {0,2,3}) 1) -
  (∑ i : Fin (n-3), Pi.single (window n i.val {0,1,2,3}) 1)

def setFunction (n : ℕ) : SetFunction (Fin n) := zeta (coefficients n)

theorem sum_single_window {n N i : ℕ} {T U : Finset ℕ}
    (hT0 : 0 ∈ T) (hU0 : 0 ∈ U)
    (hT : ∀ k ∈ T, i+k < n) (hU : ∀ j : Fin N, ∀ k ∈ U, j.val+k < n) :
    (∑ j : Fin N, (Pi.single (window n j.val U) (1 : ℝ) : SetFunction (Fin n))) (window n i T) =
      if T = U then (if i < N then 1 else 0) else 0 := by
  classical
  simp only [Finset.sum_apply, Pi.single_apply]
  have he : ∀ j : Fin N, window n i T = window n j.val U ↔ i = j.val ∧ T = U :=
    fun j => window_eq_iff hT0 hU0 hT (hU j)
  simp_rw [he]
  by_cases hTU : T = U
  · simp only [hTU, and_true, if_true]
    by_cases hi : i < N
    · rw [if_pos hi]
      rw [sum_eq_single (⟨i, hi⟩ : Fin N)]
      · simp
      · intro j hj hji
        have hval : i ≠ j.val := by intro hv; apply hji; exact Fin.ext hv.symm
        simp [hval]
      · simp
    · rw [if_neg hi]
      apply sum_eq_zero
      intro j hj
      have hval : i ≠ j.val := by intro h; rw [h] at hi; exact hi j.isLt
      simp [hval]
  · simp [hTU]

theorem coefficients_window {n i : ℕ} {T : Finset ℕ} (hT0 : 0 ∈ T)
    (hT : ∀ k ∈ T, i+k < n) :
    coefficients n (window n i T) =
      (if T = {0,1,2} then (if i < n-2 then 1 else 0) else 0) +
      (if T = {0,2,3} then (if i < n-3 then 1 else 0) else 0) -
      (if T = {0,1,2,3} then (if i < n-3 then 1 else 0) else 0) := by
  unfold coefficients
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [sum_single_window hT0 (by simp) hT (by
    intro j k hk; simp only [mem_insert, mem_singleton] at hk; omega)]
  rw [sum_single_window hT0 (by simp) hT (by
    intro j k hk; simp only [mem_insert, mem_singleton] at hk; omega)]
  rw [sum_single_window hT0 (by simp) hT (by
    intro j k hk; simp only [mem_insert, mem_singleton] at hk; omega)]

theorem coordinates_coefficients (n : ℕ) : coordinates (coefficients n) = scale n 1 := by
  have hm01 : ({0,1} : Finset ℕ) ≠ {0,2} := by decide
  have hm10 := Ne.symm hm01
  have hm02 : ({0,1} : Finset ℕ) ≠ {0,3} := by decide
  have hm20 := Ne.symm hm02
  have hm03 : ({0,1} : Finset ℕ) ≠ {0,1,2} := by decide
  have hm30 := Ne.symm hm03
  have hm04 : ({0,1} : Finset ℕ) ≠ {0,1,3} := by decide
  have hm40 := Ne.symm hm04
  have hm05 : ({0,1} : Finset ℕ) ≠ {0,2,3} := by decide
  have hm50 := Ne.symm hm05
  have hm06 : ({0,1} : Finset ℕ) ≠ {0,1,2,3} := by decide
  have hm60 := Ne.symm hm06
  have hm12 : ({0,2} : Finset ℕ) ≠ {0,3} := by decide
  have hm21 := Ne.symm hm12
  have hm13 : ({0,2} : Finset ℕ) ≠ {0,1,2} := by decide
  have hm31 := Ne.symm hm13
  have hm14 : ({0,2} : Finset ℕ) ≠ {0,1,3} := by decide
  have hm41 := Ne.symm hm14
  have hm15 : ({0,2} : Finset ℕ) ≠ {0,2,3} := by decide
  have hm51 := Ne.symm hm15
  have hm16 : ({0,2} : Finset ℕ) ≠ {0,1,2,3} := by decide
  have hm61 := Ne.symm hm16
  have hm23 : ({0,3} : Finset ℕ) ≠ {0,1,2} := by decide
  have hm32 := Ne.symm hm23
  have hm24 : ({0,3} : Finset ℕ) ≠ {0,1,3} := by decide
  have hm42 := Ne.symm hm24
  have hm25 : ({0,3} : Finset ℕ) ≠ {0,2,3} := by decide
  have hm52 := Ne.symm hm25
  have hm26 : ({0,3} : Finset ℕ) ≠ {0,1,2,3} := by decide
  have hm62 := Ne.symm hm26
  have hm34 : ({0,1,2} : Finset ℕ) ≠ {0,1,3} := by decide
  have hm43 := Ne.symm hm34
  have hm35 : ({0,1,2} : Finset ℕ) ≠ {0,2,3} := by decide
  have hm53 := Ne.symm hm35
  have hm36 : ({0,1,2} : Finset ℕ) ≠ {0,1,2,3} := by decide
  have hm63 := Ne.symm hm36
  have hm45 : ({0,1,3} : Finset ℕ) ≠ {0,2,3} := by decide
  have hm54 := Ne.symm hm45
  have hm46 : ({0,1,3} : Finset ℕ) ≠ {0,1,2,3} := by decide
  have hm64 := Ne.symm hm46
  have hm56 : ({0,2,3} : Finset ℕ) ≠ {0,1,2,3} := by decide
  have hm65 := Ne.symm hm56
  apply Coordinates.ext <;> funext i <;> dsimp [coordinates]
  all_goals
    rw [coefficients_window (by simp) (by
      intro k hk; simp only [mem_insert, mem_singleton] at hk; omega)]
    norm_num [scale, i.isLt,hm01,hm10,hm02,hm20,hm03,hm30,hm04,hm40,hm05,hm50,hm06,hm60,hm12,hm21,hm13,hm31,hm14,hm41,hm15,hm51,hm16,hm61,hm23,hm32,hm24,hm42,hm25,hm52,hm26,hm62,hm34,hm43,hm35,hm53,hm36,hm63,hm45,hm54,hm46,hm64,hm56,hm65]

theorem coefficients_supported (n : ℕ) : CliqueSupported (graph n) (coefficients n) := by
  have hzero : ∀ C : Finset (Fin n),
      (∀ i : Fin (n-2), window n i.val {0,1,2} ≠ C) →
      (∀ i : Fin (n-3), window n i.val {0,2,3} ≠ C) →
      (∀ i : Fin (n-3), window n i.val {0,1,2,3} ≠ C) → coefficients n C = 0 := by
    intro C h1 h2 h3
    simp [coefficients, Pi.single_apply, h1, h2, h3]
  have hc012 : ∀ i : Fin (n-2), (window n i.val {0,1,2}).card = 3 := by
    intro i
    rw [window_card _ (by intro k hk; simp only [mem_insert, mem_singleton] at hk; omega)]
    norm_num
  have hc023 : ∀ i : Fin (n-3), (window n i.val {0,2,3}).card = 3 := by
    intro i
    rw [window_card _ (by intro k hk; simp only [mem_insert, mem_singleton] at hk; omega)]
    norm_num
  have hc0123 : ∀ i : Fin (n-3), (window n i.val {0,1,2,3}).card = 4 := by
    intro i
    rw [window_card _ (by intro k hk; simp only [mem_insert, mem_singleton] at hk; omega)]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · apply hzero
    · intro i h; have hh := hc012 i; rw [h] at hh; simp at hh
    · intro i h; have hh := hc023 i; rw [h] at hh; simp at hh
    · intro i h; have hh := hc0123 i; rw [h] at hh; simp at hh
  · intro v
    apply hzero
    · intro i h; have hh := hc012 i; rw [h] at hh; simp at hh
    · intro i h; have hh := hc023 i; rw [h] at hh; simp at hh
    · intro i h; have hh := hc0123 i; rw [h] at hh; simp at hh
  · intro C u v hu hv huv hnon
    apply hzero
    · intro i h
      have hcl := window_clique (n := n) (i := i.val) (T := ({0,1,2} : Finset ℕ)) (by intro k hk; simp only [mem_insert, mem_singleton] at hk ⊢; tauto)
      rw [h] at hcl
      exact hnon (hcl u hu v hv huv)
    · intro i h
      have hcl := window_clique (n := n) (i := i.val) (T := ({0,2,3} : Finset ℕ)) (by intro k hk; simp only [mem_insert, mem_singleton] at hk ⊢; tauto)
      rw [h] at hcl
      exact hnon (hcl u hu v hv huv)
    · intro i h
      have hcl := window_clique (n := n) (i := i.val) (T := ({0,1,2,3} : Finset ℕ)) (subset_refl _)
      rw [h] at hcl
      exact hnon (hcl u hu v hv huv)

theorem setFunction_normalized (n : ℕ) : TranslationNormalized (setFunction n) :=
  ((cliqueSupported_iff (graph n) (coefficients n)).mp (coefficients_supported n)).1

theorem setFunction_graphical (n : ℕ) : Graphical (graph n) (setFunction n) :=
  ((cliqueSupported_iff (graph n) (coefficients n)).mp (coefficients_supported n)).2

theorem zeta_singleCoefficient {V : Type*} [Fintype V] [DecidableEq V] (C : Finset V) :
    zeta (Pi.single C 1) = setMonomial C := by
  classical
  funext S
  simp [zeta, setMonomial, Pi.single_apply, eq_comm]

/-- Exact correspondence with the paper's two triple sums minus the tetrahedron
sum, before changing the labels from `0,...,n-1` to `1,...,n`. -/
theorem setFunction_expansion (n : ℕ) :
    setFunction n =
      (∑ i : Fin (n-2), setMonomial (window n i.val {0,1,2})) +
      (∑ i : Fin (n-3), setMonomial (window n i.val {0,2,3})) -
      (∑ i : Fin (n-3), setMonomial (window n i.val {0,1,2,3})) := by
  change zetaLinear (coefficients n) = _
  rw [coefficients, map_sub, map_add, map_sum, map_sum, map_sum]
  simp only [show ∀ C : Finset (Fin n), zetaLinear (Pi.single C 1) = setMonomial C from
    fun C => zeta_singleCoefficient C]

end Path
end GraphicalZonotopes

end
end
end BundlePart265

section BundlePart266
/- Source: Papers/GraphicalZonotopes/PathTight.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace Path
open Finset
open scoped BigOperators

abbrev vertex (n i k : ℕ) (h : i+k< n) : Fin n := ⟨i+k,h⟩

theorem window_pair_eq {n i a b : ℕ} (ha : i+a< n) (hb : i+b< n) :
    window n i {a,b} = {vertex n i a ha, vertex n i b hb} := by
  ext v
  simp only [mem_window, mem_insert, mem_singleton, vertex, Fin.ext_iff]
  omega

theorem window_triple_eq {n i a b c : ℕ}
    (ha : i+a< n) (hb : i+b< n) (hc : i+c< n) :
    window n i {a,b,c} = {vertex n i a ha, vertex n i b hb, vertex n i c hc} := by
  ext v
  simp only [mem_window, mem_insert, mem_singleton, vertex, Fin.ext_iff]
  omega

theorem window_quad_eq {n i a b c d : ℕ}
    (ha : i+a< n) (hb : i+b< n) (hc : i+c< n) (hd : i+d< n) :
    window n i {a,b,c,d} =
      {vertex n i a ha, vertex n i b hb, vertex n i c hc, vertex n i d hd} := by
  ext v
  simp only [mem_window, mem_insert, mem_singleton, vertex, Fin.ext_iff]
  omega

theorem delta_edge1 (y : SetFunction (Fin n)) (i : Fin (n-1)) :
    delta (zeta y) (vertex n i.val 0 (by omega)) (vertex n i.val 1 (by omega)) ∅ =
      (coordinates y).edge1 i := by
  rw [delta_zeta_empty y (by simp [vertex, Fin.ext_iff])]
  exact congrArg y (window_pair_eq (by omega) (by omega)).symm

theorem delta_edge2 (y : SetFunction (Fin n)) (i : Fin (n-2)) :
    delta (zeta y) (vertex n i.val 0 (by omega)) (vertex n i.val 2 (by omega)) ∅ =
      (coordinates y).edge2 i := by
  rw [delta_zeta_empty y (by simp [vertex, Fin.ext_iff])]
  exact congrArg y (window_pair_eq (by omega) (by omega)).symm

theorem delta_edge3 (y : SetFunction (Fin n)) (i : Fin (n-3)) :
    delta (zeta y) (vertex n i.val 0 (by omega)) (vertex n i.val 3 (by omega)) ∅ =
      (coordinates y).edge3 i := by
  rw [delta_zeta_empty y (by simp [vertex, Fin.ext_iff])]
  exact congrArg y (window_pair_eq (by omega) (by omega)).symm

theorem delta_row013 (y : SetFunction (Fin n)) (i : Fin (n-3)) :
    delta (zeta y) (vertex n i.val 0 (by omega)) (vertex n i.val 3 (by omega))
      {vertex n i.val 1 (by omega)} =
      (coordinates y).edge3 i + (coordinates y).tri013 i := by
  rw [delta_zeta_singleton y (by simp [vertex, Fin.ext_iff])
    (by simp [vertex, Fin.ext_iff]) (by simp [vertex, Fin.ext_iff])]
  dsimp [coordinates]
  rw [window_pair_eq (by omega) (by omega),
    window_triple_eq (by omega) (by omega) (by omega)]
  congr 1
  congr 1
  ext v
  simp [or_comm, or_left_comm, or_assoc]

theorem delta_row01 (y : SetFunction (Fin n)) (i : Fin (n-3)) :
    delta (zeta y) (vertex n i.val 0 (by omega)) (vertex n i.val 1 (by omega))
      {vertex n i.val 2 (by omega), vertex n i.val 3 (by omega)} =
      (coordinates y).edge1 ⟨i.val, by omega⟩ +
      (coordinates y).tri012 ⟨i.val, by omega⟩ +
      (coordinates y).tri013 i + (coordinates y).tetra i := by
  rw [delta_zeta_pair y (by simp [vertex, Fin.ext_iff])
    (by simp [vertex, Fin.ext_iff]) (by simp [vertex, Fin.ext_iff])
    (by simp [vertex, Fin.ext_iff]) (by simp [vertex, Fin.ext_iff])
    (by simp [vertex, Fin.ext_iff])]
  dsimp [coordinates]
  rw [window_pair_eq (by omega) (by omega),
    window_triple_eq (by omega) (by omega) (by omega),
    window_triple_eq (by omega) (by omega) (by omega),
    window_quad_eq (by omega) (by omega) (by omega) (by omega)]

theorem delta_row13 (y : SetFunction (Fin n)) (i : Fin (n-3)) :
    delta (zeta y) (vertex n i.val 1 (by omega)) (vertex n i.val 3 (by omega))
      {vertex n i.val 0 (by omega), vertex n i.val 2 (by omega)} =
      (coordinates y).edge2 ⟨i.val+1, by omega⟩ +
      (coordinates y).tri013 i +
      (coordinates y).tri012 ⟨i.val+1, by omega⟩ + (coordinates y).tetra i := by
  rw [delta_zeta_pair y (by simp [vertex, Fin.ext_iff])
    (by simp [vertex, Fin.ext_iff]) (by simp [vertex, Fin.ext_iff])
    (by simp [vertex, Fin.ext_iff]) (by simp [vertex, Fin.ext_iff])
    (by simp [vertex, Fin.ext_iff])]
  dsimp [coordinates]
  rw [window_pair_eq (by omega) (by omega),
    window_triple_eq (by omega) (by omega) (by omega),
    window_triple_eq (by omega) (by omega) (by omega),
    window_quad_eq (by omega) (by omega) (by omega) (by omega)]
  simp only [vertex, Nat.add_zero, Nat.add_assoc]
  apply congrArg₂ (fun x y : ℝ => x+y)
  · apply congrArg₂ (fun x y : ℝ => x+y)
    · apply congrArg₂ (fun x y : ℝ => x+y)
      · apply congrArg y
        ext v
        simp only [mem_insert,mem_singleton,vertex,Fin.ext_iff] <;> omega
      · apply congrArg y
        ext v
        simp only [mem_insert,mem_singleton,vertex,Fin.ext_iff] <;> omega
    · apply congrArg y
      ext v
      simp only [mem_insert,mem_singleton,vertex,Fin.ext_iff] <;> omega
  · apply congrArg y
    ext v
    simp only [mem_insert,mem_singleton,vertex,Fin.ext_iff] <;> omega

theorem delta_row03 (y : SetFunction (Fin n)) (i : Fin (n-3)) :
    delta (zeta y) (vertex n i.val 0 (by omega)) (vertex n i.val 3 (by omega))
      {vertex n i.val 1 (by omega), vertex n i.val 2 (by omega)} =
      (coordinates y).edge3 i + (coordinates y).tri013 i +
      (coordinates y).tri023 i + (coordinates y).tetra i := by
  rw [delta_zeta_pair y (by simp [vertex, Fin.ext_iff])
    (by simp [vertex, Fin.ext_iff]) (by simp [vertex, Fin.ext_iff])
    (by simp [vertex, Fin.ext_iff]) (by simp [vertex, Fin.ext_iff])
    (by simp [vertex, Fin.ext_iff])]
  dsimp [coordinates]
  rw [window_pair_eq (by omega) (by omega),
    window_triple_eq (by omega) (by omega) (by omega),
    window_triple_eq (by omega) (by omega) (by omega),
    window_quad_eq (by omega) (by omega) (by omega) (by omega)]
  apply congrArg₂ (fun x y : ℝ => x+y)
  · apply congrArg₂ (fun x y : ℝ => x+y)
    · apply congrArg₂ (fun x y : ℝ => x+y)
      · apply congrArg y
        ext v
        simp only [mem_insert,mem_singleton,vertex,Fin.ext_iff] <;> omega
      · apply congrArg y
        ext v
        simp only [mem_insert,mem_singleton,vertex,Fin.ext_iff] <;> omega
    · apply congrArg y
      ext v
      simp only [mem_insert,mem_singleton,vertex,Fin.ext_iff] <;> omega
  · apply congrArg y
    ext v
    simp only [mem_insert,mem_singleton,vertex,Fin.ext_iff] <;> omega

/-- Every zero equation used for propagation is a genuine zero elemental row
of the displayed path function, including the zero pair coordinates. -/
theorem tight_of_preserves_zeros {n : ℕ} (f : SetFunction (Fin n))
    (hz : ∀ u v, u ≠ v → ∀ S, u ∉ S → v ∉ S →
      delta (setFunction n) u v S = 0 → delta f u v S = 0) :
    Tight n (coordinates (mobius f)) := by
  have he := coordinates_coefficients n
  have hedge1 (i : Fin (n-1)) : (coordinates (mobius f)).edge1 i = 0 := by
    rw [← delta_edge1, zeta_mobius]
    apply hz _ _ (by simp [vertex, Fin.ext_iff]) ∅ (by simp) (by simp)
    rw [setFunction, delta_edge1, he]
    rfl
  have hedge2 (i : Fin (n-2)) : (coordinates (mobius f)).edge2 i = 0 := by
    rw [← delta_edge2, zeta_mobius]
    apply hz _ _ (by simp [vertex, Fin.ext_iff]) ∅ (by simp) (by simp)
    rw [setFunction, delta_edge2, he]
    rfl
  have hedge3 (i : Fin (n-3)) : (coordinates (mobius f)).edge3 i = 0 := by
    rw [← delta_edge3, zeta_mobius]
    apply hz _ _ (by simp [vertex, Fin.ext_iff]) ∅ (by simp) (by simp)
    rw [setFunction, delta_edge3, he]
    rfl
  refine ⟨hedge1, hedge2, hedge3, ?_⟩
  intro i
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← delta_row013, zeta_mobius]
    apply hz _ _ (by simp [vertex, Fin.ext_iff]) _
      (by simp [vertex, Fin.ext_iff]) (by simp [vertex, Fin.ext_iff])
    rw [setFunction, delta_row013, he]
    norm_num [scale]
  · rw [← delta_row01, zeta_mobius]
    apply hz _ _ (by simp [vertex, Fin.ext_iff]) _
      (by simp [vertex, Fin.ext_iff]) (by simp [vertex, Fin.ext_iff])
    rw [setFunction, delta_row01, he]
    norm_num [scale]
  · rw [← delta_row13, zeta_mobius]
    apply hz _ _ (by simp [vertex, Fin.ext_iff]) _
      (by simp [vertex, Fin.ext_iff]) (by simp [vertex, Fin.ext_iff])
    rw [setFunction, delta_row13, he]
    norm_num [scale]
  · rw [← delta_row03, zeta_mobius]
    apply hz _ _ (by simp [vertex, Fin.ext_iff]) _
      (by simp [vertex, Fin.ext_iff]) (by simp [vertex, Fin.ext_iff])
    rw [setFunction, delta_row03, he]
    norm_num [scale]

theorem coefficients_smul_supported {n : ℕ} (a : ℝ) :
    CliqueSupported (graph n) (a • coefficients n) := by
  obtain ⟨he, hs, hn⟩ := coefficients_supported n
  refine ⟨by simp [he], fun v => by simp [hs v], ?_⟩
  intro C u v hu hv huv hnon
  simp [hn C u v hu hv huv hnon]

theorem coordinates_smul_coefficients (n : ℕ) (a : ℝ) :
    coordinates (a • coefficients n) = scale n a := by
  have h := coordinates_coefficients n
  apply Coordinates.ext <;> funext i
  · have he := congrFun (congrArg Coordinates.edge1 h) i
    change a * coefficients n _ = 0
    rw [show coefficients n _ = 0 from he]
    simp
  · have he := congrFun (congrArg Coordinates.edge2 h) i
    change a * coefficients n _ = 0
    rw [show coefficients n _ = 0 from he]
    simp
  · have he := congrFun (congrArg Coordinates.edge3 h) i
    change a * coefficients n _ = 0
    rw [show coefficients n _ = 0 from he]
    simp
  · have he := congrFun (congrArg Coordinates.tri012 h) i
    change a * coefficients n _ = a
    rw [show coefficients n _ = 1 from he]
    simp
  · have he := congrFun (congrArg Coordinates.tri013 h) i
    change a * coefficients n _ = 0
    rw [show coefficients n _ = 0 from he]
    simp
  · have he := congrFun (congrArg Coordinates.tri023 h) i
    change a * coefficients n _ = a
    rw [show coefficients n _ = 1 from he]
    simp
  · have he := congrFun (congrArg Coordinates.tetra h) i
    change a * coefficients n _ = -a
    rw [show coefficients n _ = -1 from he]
    ring

/-- The complete normalized common-zero space is a line, not merely the
restriction of that space to the displayed nonzero coordinates. -/
theorem complete_tight_kernel {n : ℕ} (hn : 4 ≤ n) (f : SetFunction (Fin n))
    (hfn : TranslationNormalized f)
    (hz : ∀ u v, u ≠ v → ∀ S, u ∉ S → v ∉ S →
      delta (setFunction n) u v S = 0 → delta f u v S = 0) :
    ∃ a : ℝ, f = a • setFunction n := by
  have hG : Graphical (graph n) f := by
    intro u v huv hnon S hu hv
    exact hz u v huv S hu hv (setFunction_graphical n u v huv hnon S hu hv)
  have hsup : CliqueSupported (graph n) (mobius f) :=
    (mobius_cliqueSupported_iff _ _).mpr ⟨hfn, hG⟩
  obtain ⟨a, ha⟩ := (tight_iff_exists_scale hn _).mp (tight_of_preserves_zeros f hz)
  have hcoeff : mobius f = a • coefficients n :=
    coordinates_injective_on_supported hsup (coefficients_smul_supported a)
      (ha.trans (coordinates_smul_coefficients n a).symm)
  refine ⟨a, ?_⟩
  have hzeta := congrArg zeta hcoeff
  rw [zeta_mobius] at hzeta
  calc
    f = zeta (a • coefficients n) := hzeta
    _ = a • setFunction n := zetaLinear.map_smul a (coefficients n)

end Path
end GraphicalZonotopes

end
end
end BundlePart266

section BundlePart267
/- Source: Papers/GraphicalZonotopes/BooleanSlacks.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators

/-- A literal Boolean coordinate, viewed in the coefficient field. -/
def membershipBit {V : Type*} [DecidableEq V] (S : Finset V) (v : V) : ℝ :=
  if v ∈ S then 1 else 0

@[simp] theorem membershipBit_zero_or_one {V : Type*} [DecidableEq V]
    (S : Finset V) (v : V) : membershipBit S v = 0 ∨ membershipBit S v = 1 := by
  unfold membershipBit
  split <;> simp

/-- Zero extension beyond the endpoints is part of the definition, rather
than a convention left to an informal boundary argument. -/
def integerBit {n : ℕ} (S : Finset (Fin n)) (k : ℤ) : ℝ :=
  if ∃ v : Fin n, (v.val : ℤ) = k ∧ v ∈ S then 1 else 0

@[simp] theorem integerBit_cast {n : ℕ} (S : Finset (Fin n)) (v : Fin n) :
    integerBit S (v.val : ℤ) = membershipBit S v := by
  have he : (∃ w : Fin n, (w.val : ℤ) = (v.val : ℤ) ∧ w ∈ S) ↔ v ∈ S := by
    constructor
    · rintro ⟨w, hw, hS⟩
      have h : w = v := Fin.ext (by exact_mod_cast hw)
      simpa [h] using hS
    · intro h
      exact ⟨v, rfl, h⟩
  unfold integerBit membershipBit
  simp only [he]

theorem integerBit_zero_or_one {n : ℕ} (S : Finset (Fin n)) (k : ℤ) :
    integerBit S k = 0 ∨ integerBit S k = 1 := by
  unfold integerBit
  split <;> simp

theorem integerBit_bounds_of_ne_zero {n : ℕ} {S : Finset (Fin n)} {k : ℤ}
    (h : integerBit S k ≠ 0) : 0 ≤ k ∧ k < n := by
  unfold integerBit at h
  split at h
  · rename_i hm
    obtain ⟨v, rfl, hv⟩ := hm
    exact ⟨by omega, by exact_mod_cast v.isLt⟩
  · exact False.elim (h rfl)

theorem integerBit_eq_zero_of_outside {n : ℕ} (S : Finset (Fin n)) (k : ℤ)
    (h : k < 0 ∨ (n : ℤ) ≤ k) : integerBit S k = 0 := by
  by_contra hn
  have hb := integerBit_bounds_of_ne_zero hn
  omega

/-- Ordered three-point monomials have precisely their three possible pair
rows. This is an identity for every conditioning set. -/
theorem delta_monomial_three {n : ℕ} {a b c u v : Fin n} {S : Finset (Fin n)}
    (hab : a < b) (hbc : b < c) (huv : u < v) (hu : u ∉ S) (hv : v ∉ S) :
    delta (setMonomial {a,b,c}) u v S =
      (if u = a ∧ v = b then membershipBit S c else 0) +
      (if u = a ∧ v = c then membershipBit S b else 0) +
      (if u = b ∧ v = c then membershipBit S a else 0) := by
  rw [delta_setMonomial (ne_of_lt huv) hu hv]
  by_cases huC : u ∈ ({a,b,c} : Finset (Fin n))
  · by_cases hvC : v ∈ ({a,b,c} : Finset (Fin n))
    · simp only [mem_insert, mem_singleton] at huC hvC
      rcases huC with rfl | rfl | rfl <;> rcases hvC with rfl | rfl | rfl
      all_goals first | omega | simp_all [membershipBit, insert_subset_iff, Fin.ext_iff]
      all_goals try { split_ifs <;> simp_all <;> omega }
    · have hvab : v ≠ a ∧ v ≠ b ∧ v ≠ c := by simpa using hvC
      simp [huC, hvC, hvab.1, hvab.2.1, hvab.2.2]
  · have huab : u ≠ a ∧ u ≠ b ∧ u ≠ c := by simpa using huC
    simp [huC, huab.1, huab.2.1, huab.2.2]

/-- The analogous exact six-term identity for a four-point monomial. -/
theorem delta_monomial_four {n : ℕ} {a b c d u v : Fin n} {S : Finset (Fin n)}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (huv : u < v) (hu : u ∉ S) (hv : v ∉ S) :
    delta (setMonomial {a,b,c,d}) u v S =
      (if u = a ∧ v = b then membershipBit S c * membershipBit S d else 0) +
      (if u = a ∧ v = c then membershipBit S b * membershipBit S d else 0) +
      (if u = a ∧ v = d then membershipBit S b * membershipBit S c else 0) +
      (if u = b ∧ v = c then membershipBit S a * membershipBit S d else 0) +
      (if u = b ∧ v = d then membershipBit S a * membershipBit S c else 0) +
      (if u = c ∧ v = d then membershipBit S a * membershipBit S b else 0) := by
  rw [delta_setMonomial (ne_of_lt huv) hu hv]
  by_cases huC : u ∈ ({a,b,c,d} : Finset (Fin n))
  · by_cases hvC : v ∈ ({a,b,c,d} : Finset (Fin n))
    · simp only [mem_insert, mem_singleton] at huC hvC
      rcases huC with rfl | rfl | rfl | rfl <;>
        rcases hvC with rfl | rfl | rfl | rfl
      all_goals first | omega | simp_all [membershipBit, insert_subset_iff, Fin.ext_iff]
      all_goals try { split_ifs <;> simp_all <;> omega }
      all_goals split_ifs <;> simp_all <;> omega
    · have hvab : v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ v ≠ d := by simpa using hvC
      simp [huC, hvC, hvab.1, hvab.2.1, hvab.2.2.1, hvab.2.2.2]
  · have huab : u ≠ a ∧ u ≠ b ∧ u ≠ c ∧ u ≠ d := by simpa using huC
    simp [huC, huab.1, huab.2.1, huab.2.2.1, huab.2.2.2]

/-- Collapse a translated Kronecker row. The support hypothesis is explicitly
proved from the zero-extended Boolean factors in each application. -/
theorem sum_at_integer (N : ℕ) (k : ℤ) (r : ℝ)
    (hr : r ≠ 0 → 0 ≤ k ∧ k < N) :
    (∑ j : Fin N, if (j.val : ℤ) = k then r else 0) = r := by
  by_cases hz : r = 0
  · simp [hz]
  · obtain ⟨hk0, hkN⟩ := hr hz
    let j : Fin N := ⟨k.toNat, by omega⟩
    have hj : (j.val : ℤ) = k := by dsimp [j]; omega
    rw [sum_eq_single j]
    · simp [hj]
    · intro l hl hlj
      have hne : (l.val : ℤ) ≠ k := by
        intro he
        apply hlj
        apply Fin.ext
        dsimp [j]
        omega
      simp [hne]
    · simp

/-- A useful version with a function evaluated at the start of the window. -/
theorem sum_pair_start (N : ℕ) (a b u v : ℤ) (F : ℤ → ℝ)
    (hsupport : v = u + (b-a) → F (u-a) ≠ 0 → 0 ≤ u-a ∧ u-a < N) :
    (∑ j : Fin N, if u = (j.val : ℤ)+a ∧ v = (j.val : ℤ)+b
      then F (j.val : ℤ) else 0) =
      if v = u + (b-a) then F (u-a) else 0 := by
  have hterm (j : Fin N) :
      (if u = (j.val : ℤ)+a ∧ v = (j.val : ℤ)+b then F (j.val : ℤ) else 0) =
      if v = u+(b-a) then (if (j.val : ℤ) = u-a then F (u-a) else 0) else 0 := by
    by_cases h : v = u+(b-a)
    · rw [if_pos h]
      by_cases hj : (j.val : ℤ) = u-a
      · have he : u = (j.val : ℤ)+a ∧ v = (j.val : ℤ)+b := by omega
        rw [if_pos he, if_pos hj, hj]
      · have he : ¬(u = (j.val : ℤ)+a ∧ v = (j.val : ℤ)+b) := by omega
        rw [if_neg he, if_neg hj]
    · have he : ¬(u = (j.val : ℤ)+a ∧ v = (j.val : ℤ)+b) := by omega
      rw [if_neg he, if_neg h]
  simp_rw [hterm]
  by_cases h : v = u+(b-a)
  · simp only [if_pos h]
    exact sum_at_integer N (u-a) (F (u-a)) (hsupport h)
  · simp [h]

/-- The path's three slack polynomials, checked for every Boolean assignment. -/
theorem path_boolean_slack_one {a b c d : ℝ}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1)
    (hc : c = 0 ∨ c = 1) (hd : d = 0 ∨ d = 1) :
    0 ≤ a*(1-b)+b*(1-c)+c*(1-d) ∧ a*(1-b)+b*(1-c)+c*(1-d) ≤ 2 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;> norm_num

theorem path_boolean_slack_two {a b c : ℝ}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1) :
    0 ≤ b*(1-a)+c*(1-b) ∧ b*(1-a)+c*(1-b) ≤ 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> norm_num

theorem path_boolean_slack_three {a b : ℝ}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    0 ≤ b*(1-a) ∧ b*(1-a) ≤ 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

end GraphicalZonotopes

end
end
end BundlePart267
