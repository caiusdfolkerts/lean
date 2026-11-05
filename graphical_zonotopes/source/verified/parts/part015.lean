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

public import verified.parts.part014
import all verified.parts.part014

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section BundlePart210
/- Source: Papers/GraphicalZonotopes/TwoHubAssembly.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace TwoHub
open Finset BooleanModule
open scoped BigOperators Pointwise
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem boundaryCentral_normalized : TranslationNormalized (boundaryCentral (I:=I)) := by
  apply assembled_normalized_general
  · constructor
    · simp [Normalized,pair]
    · intro v
      cases v <;> simp [pair]
  · intro i
    simp

theorem boundaryCentral_ab (S : Finset (Hub I)) (ha : a∉S) (hb : b∉S) :
    delta boundaryCentral a b S=1 := by
  have hh : hubs S=∅ := by
    ext v
    cases v <;> simp_all [a,b]
  rw [boundaryCentral,a,b,delta_assembled_hubs,hh,delta_pair]
  have hd (i : I) : delta (fun X : Finset Bool => if true∈X then (missCount i : ℝ) else 0)
      false true ∅=0 := by simp [delta]
  simp only [hd,ite_self,mul_zero,sum_const_zero,add_zero]

theorem boundaryCentral_ai (i : I) (S : Finset (Hub I)) (hi : u i∉S) :
    delta boundaryCentral a (u i) S=0 := by
  rw [boundaryCentral,a,u,delta_assembled_spoke _ _ _ _ _ _ hi]
  simp

theorem boundaryCentral_bi (i : I) (S : Finset (Hub I)) (hb : b∉S) (hi : u i∉S) :
    delta boundaryCentral b (u i) S=(missCount i : ℝ) := by
  have hx : true∉hubs S := by simpa [b] using hb
  rw [boundaryCentral,b,u,delta_assembled_spoke _ _ _ _ _ _ hi]
  simp [hx]

theorem boundaryCentral_outer : OuterZero (boundaryCentral (I:=I)) := by
  intro i j hij S hi hj
  exact delta_assembled_outer _ _ _ i j hij S hi hj

theorem missing_sum (i : I) :
    (∑ ε : Finset I,if i∈ε then (0 : ℝ) else 1)=(missCount i : ℝ) := by
  have he : (∑ ε : Finset I,if i∈ε then (0 : ℝ) else 1)=
      ∑ ε∈univ.filter (fun ε : Finset I => i∉ε),(1 : ℝ) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro ε hε
    by_cases hi : i∈ε <;> simp [hi]
  rw [he]
  simp [missCount]

theorem family_outer_zero (j : Index I) : OuterZero (family j) := by
  cases j with
  | inl ε => exact module_outer_zero ε
  | inr i => exact balancing_outer_zero i

/-- The central coefficients match the exact negative responses on every
boundary edge and every conditioning set. -/
theorem central_compatible : Compatible (boundaryCentral (I:=I)) family weights := by
  have hab (S : Finset (Hub I)) (ha : a∉S) (hb : b∉S) :
      delta boundaryCentral a b S=
        ∑ j : Index I,weights j*negativeResponse (family j) a b S := by
    rw [boundaryCentral_ab S ha hb,response_sum_ab _ _ ha hb]
    rfl
  have hai (i : I) (S : Finset (Hub I)) (ha : a∉S) (hi : u i∉S) :
      delta boundaryCentral a (u i) S=
        ∑ j : Index I,weights j*negativeResponse (family j) a (u i) S := by
    rw [boundaryCentral_ai i S hi,response_sum_ai _ _ _ ha hi]
  have hbi (i : I) (S : Finset (Hub I)) (hb : b∉S) (hi : u i∉S) :
      delta boundaryCentral b (u i) S=
        ∑ j : Index I,weights j*negativeResponse (family j) b (u i) S := by
    rw [boundaryCentral_bi i S hb hi,response_sum_bi _ _ _ hb hi]
    by_cases ha : a∈S
    · simp [ha,weights]
    · simp only [ha,ite_false,weights,missing_sum]
  have hij (i j : I) (hne : i≠ j) (S : Finset (Hub I)) (hi : u i∉S) (hj : u j∉S) :
      delta boundaryCentral (u i) (u j) S=
        ∑ k : Index I,weights k*negativeResponse (family k) (u i) (u j) S := by
    have hz : delta boundaryCentral (u i) (u j) S=0 := boundaryCentral_outer i j hne S hi hj
    rw [hz]
    simp only [family_outer_response _ _ _ hne S hi hj,mul_zero,sum_const_zero]
  have swap (x y : Hub I) (S : Finset (Hub I))
      (h : delta boundaryCentral x y S=
        ∑ j : Index I,weights j*negativeResponse (family j) x y S) :
      delta boundaryCentral y x S=
        ∑ j : Index I,weights j*negativeResponse (family j) y x S := by
    simpa only [negativeResponse,delta_comm y x] using h
  intro x y hxy S hx hy
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      cases x <;> cases y
      · exact False.elim (hxy rfl)
      · exact hab S hx hy
      · exact swap a b S (hab S hy hx)
      · exact False.elim (hxy rfl)
    | inr i =>
      cases x
      · exact hai i S hx hy
      · exact hbi i S hx hy
  | inr i =>
    cases y with
    | inl y =>
      cases y
      · exact swap a (u i) S (hai i S hy hx)
      · exact swap b (u i) S (hbi i S hy hx)
    | inr j => exact hij i j (fun he => hxy (congrArg Sum.inr he)) S hx hy

theorem construction_normalized : TranslationNormalized (construction (I:=I)) :=
  assembled_normalized_general boundaryCentral_normalized family family_empty weights

theorem construction_supermodular [Nonempty I] : Supermodular (construction (I:=I)) :=
  assembled_supermodular_general boundaryCentral family family_monotone weights
    (fun j => (weights_pos j).le) central_compatible

theorem construction_extreme [Nonempty I] : ExtremeSupermodular (construction (I:=I)) := by
  apply positive_circuit_extreme_general boundaryCentral_normalized family_empty family_monotone
    family_privateRigid (fun j => (weights_pos j).le) _ central_compatible unique_relation
  refine ⟨Sum.inr (Classical.choice ‹Nonempty I›),univ,?_⟩
  simp only [family,weights,(balancing_boolean _).full,mul_one]
  exact ne_of_gt (Nat.cast_pos.mpr (missCount_pos _) : (0 : ℝ)< _)

theorem construction_graphical : Graphical (graph (I:=I) (J:=Index I)) construction := by
  intro x y hxy hnon S hx hy
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      cases x with
      | inl x =>
        cases y with
        | inl y =>
          cases x <;> cases y <;> simp_all [graph,color]
        | inr i => cases x <;> simp_all [graph,color]
      | inr i =>
        cases y with
        | inl y => cases y <;> simp_all [graph,color]
        | inr j =>
          have hij : i≠ j := fun he => hxy (by subst j; rfl)
          have hi : u i∉hubs S := by simpa [u] using hx
          have hj : u j∉hubs S := by simpa [u] using hy
          rw [construction,delta_assembled_hubs,boundaryCentral_outer i j hij _ hi hj]
          simp only [family_outer_zero _ i j hij _ hi hj,ite_self,mul_zero,sum_const_zero,add_zero]
    | inr j =>
      cases x with
      | inl x => cases x <;> simp_all [graph,color]
      | inr i => simp_all [graph,color]
  | inr i =>
    cases y with
    | inl y =>
      cases y with
      | inl y => cases y <;> simp_all [graph,color]
      | inr j => simp_all [graph,color]
    | inr j =>
      exact delta_assembled_outer _ _ _ i j
        (fun he => hxy (congrArg Sum.inr he)) S hx hy

end TwoHub
end GraphicalZonotopes

end
end
end BundlePart210

section BundlePart211
/- Source: Papers/GraphicalZonotopes/TwoHubGraphIso.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace TwoHub
open Finset
open scoped BigOperators
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

abbrev SigmaVertex (I J : Type*) [Fintype I] [Fintype J] :=
  Σ c : Fin 4,Fin (![1,1,Fintype.card I,Fintype.card J] c)

/-- Exact coordinate correspondence with the paper's four independent
parts. Both singleton vertices and every vertex in the other parts are kept. -/
def sigmaTo : (Bool⊕I)⊕J → SigmaVertex I J
  | .inl (.inl false) => ⟨0,⟨0,by simp⟩⟩
  | .inl (.inl true) => ⟨1,⟨0,by simp⟩⟩
  | .inl (.inr i) => ⟨2,Fintype.equivFin I i⟩
  | .inr j => ⟨3,Fintype.equivFin J j⟩

@[simp] theorem sigmaTo_color (x : (Bool⊕I)⊕J) : (sigmaTo x).1=color x := by
  rcases x with (e|i)|j
  · cases e <;> rfl
  · rfl
  · rfl

theorem sigmaTo_injective : Function.Injective (sigmaTo (I:=I) (J:=J)) := by
  intro x y h
  have hc := congrArg Sigma.fst h
  have hv := congrArg (fun x : SigmaVertex I J => x.2.val) h
  rcases x with (e|i)|j <;> rcases y with (f|k)|l
  · cases e <;> cases f <;> simp_all [sigmaTo]
  · cases e <;> simp_all [sigmaTo]
  · cases e <;> simp_all [sigmaTo]
  · cases f <;> simp_all [sigmaTo]
  · apply congrArg (fun i : I => (Sum.inl (Sum.inr i) : (Bool⊕I)⊕J))
    apply (Fintype.equivFin I).injective
    exact Fin.ext hv
  · simp_all [sigmaTo]
  · cases f <;> simp_all [sigmaTo]
  · simp_all [sigmaTo]
  · apply congrArg (Sum.inr : J → (Bool⊕I)⊕J)
    apply (Fintype.equivFin J).injective
    exact Fin.ext hv

def sigmaEquiv : ((Bool⊕I)⊕J) ≃ SigmaVertex I J :=
  Equiv.ofBijective sigmaTo ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨sigmaTo_injective,by
      simp [SigmaVertex,Fintype.card_sigma,Fin.sum_univ_succ,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]⟩)

def graphIso : graph (I:=I) (J:=J) ≃g
    twoSingletonGraph (Fintype.card I) (Fintype.card J) where
  toEquiv := sigmaEquiv
  map_rel_iff' := by
    intro x y
    change ((sigmaTo x).1≠(sigmaTo y).1) ↔ color x≠ color y
    rw [sigmaTo_color,sigmaTo_color]

/-- The natural-parameter specialization has literal part sizes p and b,
so subsequent embeddings need no implicit cardinality casts. -/
def finGraphIso (p b : ℕ) : graph (I:=Fin p) (J:=Fin b)≃g twoSingletonGraph p b := by
  exact cast (by rw [Fintype.card_fin,Fintype.card_fin])
    (graphIso (I:=Fin p) (J:=Fin b))

theorem maximum_dimension_model_eq (p b : ℕ) :
    maximumIndecomposableDimension (graph (I:=Fin p) (J:=Fin b))=
      maximumIndecomposableDimension (twoSingletonGraph p b) := by
  exact maximumIndecomposableDimension_iso (finGraphIso p b)

end TwoHub
end GraphicalZonotopes

end
end
end BundlePart211

section BundlePart212
/- Source: Papers/GraphicalZonotopes/TwoHubGeometry.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace TwoHub
open Finset BooleanModule
open scoped BigOperators Pointwise
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem module_u_essential (ε : Finset I) (i : I) : Essential (moduleFunction ε) (u i) := by
  refine ⟨hubSet {false},by simp [u],?_⟩
  rw [module_spoke,corner_false]

theorem module_a_essential (ε : Finset I) : Essential (moduleFunction ε) a := by
  by_cases he : ε=∅
  · refine ⟨context ∅ (∅ : Finset I),by simp [a],?_⟩
    rw [a,←context_insert_hub,insert_empty_eq,module_a_zero_cover]
    simp [he,eta]
  · obtain ⟨i,hi⟩:=nonempty_iff_ne_empty.mpr he
    refine ⟨context ∅ {i},by simp [a],?_⟩
    rw [a,←context_insert_hub,insert_empty_eq,module_a_zero_cover]
    simp [eta,he,hi]

theorem module_b_essential [Nonempty I] (ε : Finset I) : Essential (moduleFunction ε) b := by
  by_cases he : ε=univ
  · let i : I:=Classical.choice ‹Nonempty I›
    refine ⟨context ∅ {i},by simp [b],?_⟩
    rw [b,←context_insert_hub,insert_empty_eq,module_b_zero_cover]
    simp [he]
  · obtain ⟨i,hi⟩:=nonempty_iff_ne_empty.mpr
      (show univ\ε≠∅ from fun h => he (eq_univ_iff_forall.mpr
        (fun i => (sdiff_eq_empty_iff_subset.mp h) (mem_univ i))))
    let Y:=(univ\ε).erase i
    have hiε : i∉ε := (mem_sdiff.mp hi).2
    have hiY : i∉Y := by simp [Y]
    have hYi : insert i Y=univ\ε := insert_erase hi
    have hb0:=module_b_complement_zero ε
    have hd:=module_bi_delta ε i (context (∅ : Finset Bool) Y) (by simp [b]) (by simpa [u] using hiY)
    simp only [a,b,u,mem_context_hub,notMem_empty,not_false_eq_true,ite_false,hiε] at hd
    refine ⟨context (∅ : Finset Bool) Y,by simp [b],?_⟩
    rw [b,←context_insert_hub,insert_empty_eq]
    have hctx : insert (u i) (context (∅ : Finset Bool) Y)=context (∅ : Finset Bool) (univ\ε) := by
      rw [u,←context_insert,hYi]
    have hctxb : insert b (context (∅ : Finset Bool) (univ\ε))=context {true} (univ\ε) := by
      rw [b,←context_insert_hub,insert_empty_eq]
    have hctxbY : insert b (context (∅ : Finset Bool) Y)=context {true} Y := by
      rw [b,←context_insert_hub,insert_empty_eq]
    change delta (moduleFunction ε) b (u i) (context (∅ : Finset Bool) Y)= -1 at hd
    simp only [delta,hctx,hctxb,hctxbY] at hd
    linarith

theorem module_all_essential [Nonempty I] (ε : Finset I) (v : Hub I) :
    Essential (moduleFunction ε) v := by
  rcases v with e|i
  · cases e
    · exact module_a_essential ε
    · exact module_b_essential ε
  · exact module_u_essential ε i

theorem balancing_a_essential (i : I) : Essential (balancing i) a := by
  refine ⟨{b},by simp [a,b],?_⟩
  simp [balancing,a,b,u]

theorem family_connected [Nonempty I] : (essentialSpokeGraph (family (I:=I))).Connected := by
  let j₀ : Index I:=.inl ∅
  have hhub (v : Hub I) :
      (essentialSpokeGraph family).Adj (.inl v) (.inr j₀) := module_all_essential ∅ v
  have houter (j : Index I) :
      (essentialSpokeGraph family).Adj (.inl (a : Hub I)) (.inr j) := by
    cases j with
    | inl ε => exact module_a_essential ε
    | inr i => exact balancing_a_essential i
  have reach (v : Hub I⊕Index I) :
      (essentialSpokeGraph family).Reachable v (.inl (a : Hub I)) := by
    cases v with
    | inl v => exact (hhub v).reachable.trans (hhub a).reachable.symm
    | inr j => exact (houter j).reachable.symm
  exact ⟨fun x y => (reach x).trans (reach y).symm⟩

theorem construction_fullDimension [Nonempty I] : FullDimension (basePolytope (construction (I:=I))) := by
  apply finrank_vectorSpan_eq_of_connected_slacks construction_normalized.1
    construction_supermodular family_connected
  intro x y hxy
  exact essential_spoke_slack weights_pos hxy

namespace IntegerHelpers
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem conditional (P : Finset V → Prop) [∀ S,Decidable (P S)]
    {f : SetFunction V} (hf : IntegerValued f) :
    IntegerValued (fun S => if P S then f S else 0) := by
  intro S
  by_cases h : P S
  · simpa [h] using hf S
  · exact ⟨0,by simp [h]⟩

theorem constant (n : ℤ) : IntegerValued (fun _ : Finset V => (n : ℝ)) :=
  fun _ => ⟨n,rfl⟩

end IntegerHelpers

theorem pair_integer (A B C : ℤ) : IntegerValued (pair (A : ℝ) (B : ℝ) (C : ℝ)) := by
  exact ((IntegerHelpers.conditional (fun S : Finset Bool => false∈S) (IntegerHelpers.constant A)).add
    (IntegerHelpers.conditional (fun S : Finset Bool => true∈S) (IntegerHelpers.constant B))).add
    (IntegerHelpers.conditional (fun S : Finset Bool => false∈S∧true∈S) (IntegerHelpers.constant C))

theorem corner_integer (e : Bool) : IntegerValued (corner e) := by
  intro S
  rcases corner_values e S with h|h
  · exact ⟨0,by simpa using h⟩
  · exact ⟨1,by simpa using h⟩

theorem central_integer (ε : Finset I) : IntegerValued (central ε) := by
  have he : eta ε=((if ε=∅ then 1 else 0 : ℤ) : ℝ) := by
    unfold eta
    split_ifs <;> norm_num
  simpa only [central,he,Int.cast_sub,Int.cast_natCast,Int.cast_one] using
    pair_integer (if ε=∅ then 1 else 0) ((Fintype.card I : ℤ)-(ε.card : ℤ))
      ((ε.card : ℤ)-1)

theorem module_integer (ε : Finset I) : IntegerValued (moduleFunction ε) := by
  apply (boundaryLift_integerValued (central_integer ε)).add
  apply IntegerValued.finset_sum
  intro i hi
  simpa only [one_smul] using branchLift_integerValued i (corner_integer (decide (i∈ε)))

theorem family_integer (j : Index I) : IntegerValued (family j) := by
  cases j with
  | inl ε => exact module_integer ε
  | inr i => exact (balancing_boolean i).integerValued

theorem boundaryCentral_integer : IntegerValued (boundaryCentral (I:=I)) := by
  unfold boundaryCentral assembled
  have hz : IntegerValued (pair (0 : ℝ) 0 1) := by simpa using pair_integer 0 0 1
  apply (boundaryLift_integerValued hz).add
  apply IntegerValued.finset_sum
  intro i hi
  simpa only [one_smul,Int.cast_natCast] using
    branchLift_integerValued i
      (IntegerHelpers.conditional (fun S : Finset Bool => true∈S)
        (IntegerHelpers.constant (missCount i : ℤ)))

theorem construction_integer : IntegerValued (construction (I:=I)) := by
  unfold construction assembled
  apply (boundaryLift_integerValued boundaryCentral_integer).add
  apply IntegerValued.finset_sum
  intro j hj
  cases j with
  | inl ε => simpa only [weights,family,one_smul] using branchLift_integerValued (Sum.inl ε : Index I) (module_integer ε)
  | inr i => simpa only [weights,family,Int.cast_natCast] using
      (branchLift_integerValued (Sum.inr i : Index I) (balancing_boolean i).integerValued).int_smul (missCount i : ℤ)

/-- The construction is an actual integral, full-dimensional
Minkowski-indecomposable weak summand for arbitrary nonempty finite I. -/
theorem exponential_lattice_witness [Nonempty I] :
    LatticePolytope (basePolytope (construction (I:=I))) ∧
    MinkowskiIndecomposable (basePolytope (construction (I:=I))) ∧
    FullDimension (basePolytope (construction (I:=I))) ∧
    IsWeakMinkowskiSummand (basePolytope (construction (I:=I)))
      (graphicalZonotope (graph (I:=I) (J:=Index I))) := by
  refine ⟨construction_integer.basePolytope construction_normalized.1 construction_supermodular,
    construction_extreme.minkowskiIndecomposable,construction_fullDimension,?_⟩
  exact (isWeakMinkowskiSummand_graphical_iff construction_normalized.1
    construction_supermodular).mpr construction_graphical

end TwoHub
end GraphicalZonotopes

end
end
end BundlePart212

section BundlePart213
/- Source: Papers/GraphicalZonotopes/TwoHubRestriction.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset SetFunctionEmbedding
open scoped BigOperators Pointwise
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Adding genuinely ignored variables preserves private rigidity. Tight
zero covers force every variation to ignore those same variables. -/
theorem PrivateRigid.extend {F : SetFunction W} (hF : PrivateRigid F) (e : W ↪ V) :
    PrivateRigid (SetFunctionEmbedding.extend e F) := by
  intro f hf hcover hdelta
  let g:=SetFunctionEmbedding.restrict e f
  have hg : g ∅=0 := by simpa [g,SetFunctionEmbedding.restrict] using hf
  have hgcover : ∀ w X,w∉X → F (insert w X)-F X=0 → g (insert w X)-g X=0 := by
    intro w X hw hzero
    change f ((insert w X).map e)-f (X.map e)=0
    rw [map_insert]
    apply hcover (e w) (X.map e) (by simpa using hw)
    simpa only [SetFunctionEmbedding.extend,pullSet_insert_image,pullSet_map] using hzero
  have hgdelta : ∀ w v,w≠ v → ∀ X,w∉X → v∉X → delta F w v X=0 → delta g w v X=0 := by
    intro w v hwv X hw hv hz
    rw [show g=SetFunctionEmbedding.restrict e f from rfl,delta_restrict]
    apply hdelta (e w) (e v) (fun he => hwv (e.injective he)) (X.map e)
      (by simpa using hw) (by simpa using hv)
    simpa only [delta_extend,pullSet_map] using hz
  obtain ⟨c,hc⟩:=hF g hg hgcover hgdelta
  have hrec : SetFunctionEmbedding.extend e g=f := by
    apply reconstruct_of_insert_absent
    intro v hv X
    by_cases hx : v∈X
    · simp [insert_eq_of_mem hx]
    · apply sub_eq_zero.mp
      apply hcover v X hx
      rw [extend_insert_absent e F v hv X,sub_self]
  refine ⟨c,?_⟩
  rw [←hrec,hc,extend_smul]

end BooleanModule

namespace TwoHub
open Finset BooleanModule SetFunctionEmbedding
open scoped BigOperators Pointwise
variable {I : Type*} [Fintype I] [DecidableEq I]


def Cell.embedding (C : Cell I) : Hub C.fixed ↪ Hub I :=
  Function.Embedding.sumMap (Function.Embedding.refl Bool)
    ⟨Subtype.val,Subtype.val_injective⟩

def Cell.function (C : Cell I) : SetFunction (Hub I) :=
  extend C.embedding (moduleFunction C.assignment)

@[simp] theorem Cell.embed_a (C : Cell I) : C.embedding a=a := rfl
@[simp] theorem Cell.embed_b (C : Cell I) : C.embedding b=b := rfl
@[simp] theorem Cell.embed_u (C : Cell I) (i : C.fixed) : C.embedding (u i)=u i.1 := rfl

theorem Cell.pullSet_outers (C : Cell I) (S : Finset (Hub I)) :
    outers (pullSet C.embedding S)=C.pull (outers S) := by
  ext i
  simp [Cell.embedding,u]

theorem Cell.pullSet_a (C : Cell I) (S : Finset (Hub I)) :
    a∈pullSet C.embedding S ↔ a∈S := by simp

theorem Cell.pullSet_b (C : Cell I) (S : Finset (Hub I)) :
    b∈pullSet C.embedding S ↔ b∈S := by simp

theorem Cell.range_u (C : Cell I) (i : I) : u i∈Set.range C.embedding ↔ i∈C.fixed := by
  constructor
  · rintro ⟨x,hx⟩
    rcases x with e|j
    · cases e <;> simp [Cell.embedding,a,b,u] at hx
    · have hh : j.1=i := Sum.inr_injective hx
      exact hh ▸ j.2
  · intro hi
    exact ⟨u (⟨i,hi⟩ : C.fixed),rfl⟩

theorem Cell.privateRigid (C : Cell I) (hC : C.fixed.Nonempty) : PrivateRigid C.function := by
  letI : Nonempty C.fixed:=⟨⟨hC.choose,hC.choose_spec⟩⟩
  exact (module_private_rigid C.assignment).extend C.embedding

theorem Cell.empty (C : Cell I) : C.function ∅=0 := by
  simp [Cell.function,extend]

theorem Cell.cover_nonnegative (C : Cell I) (hC : C.fixed.Nonempty)
    (v : Hub I) (S : Finset (Hub I)) : 0≤ C.function (insert v S)-C.function S := by
  letI : Nonempty C.fixed:=⟨⟨hC.choose,hC.choose_spec⟩⟩
  by_cases hv : v∈Set.range C.embedding
  · obtain ⟨w,rfl⟩:=hv
    simpa only [Cell.function,extend,pullSet_insert_image] using
      module_cover_nonnegative C.assignment w (pullSet C.embedding S)
  · simp only [Cell.function,extend_insert_absent C.embedding _ v hv S,sub_self,le_refl]

theorem Cell.ab_response (C : Cell I) (S : Finset (Hub I)) (ha : a∉S) (hb : b∉S) :
    negativeResponse C.function a b S=if C.Matches (outers S) then 1 else 0 := by
  change max 0 (-delta (extend C.embedding (moduleFunction C.assignment))
    (C.embedding a) (C.embedding b) S)=_
  rw [delta_extend]
  change negativeResponse (moduleFunction C.assignment) a b (pullSet C.embedding S)=_
  rw [module_ab_response_all C.assignment _ (by simpa using ha) (by simpa using hb),Cell.pullSet_outers]
  rfl

theorem Cell.ai_response (C : Cell I) (i : I) (S : Finset (Hub I))
    (ha : a∉S) (hi : u i∉S) : negativeResponse C.function a (u i) S=0 := by
  by_cases hc : i∈C.fixed
  · let j : C.fixed:=⟨i,hc⟩
    change max 0 (-delta (extend C.embedding (moduleFunction C.assignment))
      (C.embedding a) (C.embedding (u j)) S)=0
    rw [delta_extend]
    exact module_ai_response C.assignment j _ (by simpa using ha) (by simpa [j] using hi)
  · have hh : u i∉Set.range C.embedding := fun h => hc ((C.range_u i).mp h)
    rw [negativeResponse,delta_comm a (u i)]
    change max 0 (-delta (extend C.embedding _) (u i) a S)=0
    rw [delta_extend_not_range C.embedding _ _ _ hh,neg_zero,max_self]

theorem Cell.bi_response (C : Cell I) (i : I) (S : Finset (Hub I))
    (hb : b∉S) (hi : u i∉S) :
    negativeResponse C.function b (u i) S=
      if i∈C.fixed ∧ i∉C.ones then (if a∈S then 0 else 1) else 0 := by
  by_cases hc : i∈C.fixed
  · let j : C.fixed:=⟨i,hc⟩
    change max 0 (-delta (extend C.embedding (moduleFunction C.assignment))
      (C.embedding b) (C.embedding (u j)) S)=_
    rw [delta_extend]
    change negativeResponse (moduleFunction C.assignment) b (u j) (pullSet C.embedding S)=_
    rw [module_bi_response _ _ _ (by simpa using hb) (by simpa [j] using hi)]
    by_cases ho : i∈C.ones <;> simp [hc,ho,j]
  · have hh : u i∉Set.range C.embedding := fun h => hc ((C.range_u i).mp h)
    rw [negativeResponse,delta_comm b (u i)]
    change max 0 (-delta (extend C.embedding _) (u i) b S)=_
    rw [delta_extend_not_range C.embedding _ _ _ hh]
    simp [hc]

theorem Cell.outer_zero (C : Cell I) : OuterZero C.function := by
  intro i j hij S hi hj
  by_cases hci : i∈C.fixed
  · by_cases hcj : j∈C.fixed
    · let i' : C.fixed:=⟨i,hci⟩
      let j' : C.fixed:=⟨j,hcj⟩
      change delta (extend C.embedding _) (C.embedding (u i')) (C.embedding (u j')) S=0
      rw [delta_extend]
      exact module_outer_zero C.assignment i' j' (fun he => hij (congrArg Subtype.val he))
        _ (by simpa [Cell.embedding,i',u] using hi) (by simpa [Cell.embedding,j',u] using hj)
    · change delta C.function (u i) (u j) S=0
      rw [delta_comm (u i) (u j)]
      exact delta_extend_not_range C.embedding _ _ _
        (fun h => hcj ((C.range_u j).mp h)) S
  · exact delta_extend_not_range C.embedding _ _ _
      (fun h => hci ((C.range_u i).mp h)) S

theorem Cell.integer (C : Cell I) : IntegerValued C.function :=
  extend_integer C.embedding (module_integer C.assignment)

theorem Cell.a_essential (C : Cell I) : Essential C.function a := by
  obtain ⟨X,hX,hval⟩:=module_a_essential C.assignment
  refine ⟨X.map C.embedding,?_,?_⟩
  · change C.embedding a∉X.map C.embedding
    intro hx
    obtain ⟨y,hy,he⟩:=Finset.mem_map.mp hx
    exact hX (C.embedding.injective he ▸ hy)
  · change extend C.embedding (moduleFunction C.assignment)
        (insert (C.embedding a) (X.map C.embedding))-
        extend C.embedding (moduleFunction C.assignment) (X.map C.embedding)=1
    simpa only [extend,pullSet_insert_image,pullSet_map] using hval

theorem Cell.b_essential (C : Cell I) (hC : C.fixed.Nonempty) : Essential C.function b := by
  letI : Nonempty C.fixed:=⟨⟨hC.choose,hC.choose_spec⟩⟩
  obtain ⟨X,hX,hval⟩:=module_b_essential C.assignment
  refine ⟨X.map C.embedding,?_,?_⟩
  · change C.embedding b∉X.map C.embedding
    intro hx
    obtain ⟨y,hy,he⟩:=Finset.mem_map.mp hx
    exact hX (C.embedding.injective he ▸ hy)
  · change extend C.embedding (moduleFunction C.assignment)
        (insert (C.embedding b) (X.map C.embedding))-
        extend C.embedding (moduleFunction C.assignment) (X.map C.embedding)=1
    simpa only [extend,pullSet_insert_image,pullSet_map] using hval

theorem balancing_b_essential (i : I) : Essential (balancing i) b := by
  refine ⟨{a},by simp [a,b],?_⟩
  simp [balancing,a,b,u]

theorem balancing_u_essential (i : I) : Essential (balancing i) (u i) := by
  refine ⟨{a},by simp [a,u],?_⟩
  simp [balancing,a,b,u]

end TwoHub
end GraphicalZonotopes

end
end
end BundlePart213

section BundlePart214
/- Source: Papers/GraphicalZonotopes/TwoHubPartition.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.TwoHub
open Finset BooleanModule
open scoped BigOperators Pointwise
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The cube partition hypotheses are constructed for every needed size in
`CubePartition.exists_proper_card`. They are not assumptions of the final
complete multipartite graph theorem. -/
structure PartitionData (I : Type*) [Fintype I] [DecidableEq I] where
  cells : Finset (Cell I)
  valid : CubePartition.Valid cells
  proper : ∀ C∈cells,C.fixed.Nonempty
  uses : CubePartition.UsesZero cells univ

namespace PartitionData
variable (P : PartitionData I)

abbrev Index := P.cells⊕I

def misses (C : P.cells) (i : I) : Prop := i∈C.1.fixed ∧ i∉C.1.ones
instance (C : P.cells) (i : I) : Decidable (P.misses C i) :=
  inferInstanceAs (Decidable (i∈C.1.fixed ∧ i∉C.1.ones))

def missCount (i : I) : ℕ := (univ.filter (fun C : P.cells => P.misses C i)).card

def family : P.Index → SetFunction (Hub I)
  | .inl C => C.1.function
  | .inr i => balancing i

def weights : P.Index → ℝ
  | .inl _ => 1
  | .inr i => (P.missCount i : ℝ)

def boundary : SetFunction (Hub I) :=
  assembled (pair 0 0 1) (fun i X => if true∈X then (P.missCount i : ℝ) else 0) (fun _ => 1)

def construction : SetFunction (Hub I⊕P.Index) := assembled P.boundary P.family P.weights

theorem missCount_pos (i : I) : 0< P.missCount i := by
  obtain ⟨C,hC,hi,hio⟩:=P.uses i (mem_univ i)
  exact card_pos.mpr ⟨⟨C,hC⟩,mem_filter.mpr ⟨mem_univ _,hi,hio⟩⟩

theorem weights_pos (j : P.Index) : 0< P.weights j := by
  cases j with
  | inl C => norm_num [weights]
  | inr i => simpa [weights] using (Nat.cast_pos.mpr (P.missCount_pos i) : (0 : ℝ)< _)

theorem family_empty (j : P.Index) : P.family j ∅=0 := by
  cases j with
  | inl C => exact C.1.empty
  | inr i => exact (balancing_boolean i).empty

theorem family_monotone (j : P.Index) (v : Hub I) (S : Finset (Hub I)) :
    0≤ P.family j (insert v S)-P.family j S := by
  cases j with
  | inl C => exact C.1.cover_nonnegative (P.proper C.1 C.2) v S
  | inr i => exact sub_nonneg.mpr ((balancing_boolean i).monotone (subset_insert v S))

theorem family_privateRigid (j : P.Index) : PrivateRigid (P.family j) := by
  cases j with
  | inl C => exact C.1.privateRigid (P.proper C.1 C.2)
  | inr i => exact (balancing_boolean i).privateRigid

theorem family_ai_response (j : P.Index) (i : I) (S : Finset (Hub I))
    (ha : a∉S) (hi : u i∉S) : negativeResponse (P.family j) a (u i) S=0 := by
  cases j with
  | inl C => exact C.1.ai_response i S ha hi
  | inr k => exact balancing_ai_response k i S ha hi

theorem response_sum_ab (t : P.Index → ℝ) (S : Finset (Hub I))
    (ha : a∉S) (hb : b∉S) (C : P.cells) (hC : C.1.Matches (outers S)) :
    (∑ j : P.Index,t j*negativeResponse (P.family j) a b S)=t (.inl C) := by
  rw [Fintype.sum_sum_type]
  simp only [family,Cell.ab_response _ _ ha hb,balancing_ab_response _ _ ha hb,
    mul_zero,sum_const_zero,add_zero,mul_ite,mul_one]
  rw [sum_eq_single C]
  · simp [hC]
  · intro D hD hDC
    have hm : ¬D.1.Matches (outers S) := by
      intro hm
      exact hDC (Subtype.ext (P.valid.unique D.2 C.2 hm hC))
    simp [hm]
  · simp

theorem response_sum_ai (t : P.Index → ℝ) (i : I) (S : Finset (Hub I))
    (ha : a∉S) (hi : u i∉S) :
    (∑ j : P.Index,t j*negativeResponse (P.family j) a (u i) S)=0 := by
  simp only [P.family_ai_response _ _ _ ha hi,mul_zero,sum_const_zero]

theorem response_sum_bi (t : P.Index → ℝ) (i : I) (S : Finset (Hub I))
    (hb : b∉S) (hi : u i∉S) :
    (∑ j : P.Index,t j*negativeResponse (P.family j) b (u i) S)=
      if a∈S then t (.inr i) else ∑ C : P.cells,if P.misses C i then t (.inl C) else 0 := by
  rw [Fintype.sum_sum_type]
  simp only [family,Cell.bi_response _ _ _ hb hi,balancing_bi_response _ _ _ hb hi]
  by_cases ha : a∈S
  · simp [ha]
  · simp only [ha,ite_false,ite_self,mul_ite,mul_one,mul_zero,sum_const_zero,add_zero,misses]
    <;> rfl

theorem family_outer_zero (j : P.Index) : OuterZero (P.family j) := by
  cases j with
  | inl C => exact C.1.outer_zero
  | inr i => exact balancing_outer_zero i

theorem family_outer_response (j : P.Index) (i k : I) (hik : i≠ k)
    (S : Finset (Hub I)) (hi : u i∉S) (hk : u k∉S) :
    negativeResponse (P.family j) (u i) (u k) S=0 := by
  rw [negativeResponse]
  have hz : delta (P.family j) (u i) (u k) S=0 := P.family_outer_zero j i k hik S hi hk
  rw [hz,neg_zero,max_self]

theorem compatible_ai_zero {h : SetFunction (Hub I)} {t : P.Index → ℝ}
    (hc : Compatible h P.family t) (i : I) (S : Finset (Hub I))
    (ha : a∉S) (hi : u i∉S) : delta h a (u i) S=0 := by
  rw [hc a (u i) (by simp [a,u]) S ha hi,P.response_sum_ai _ _ _ ha hi]

theorem compatible_ab_constant {h : SetFunction (Hub I)} {t : P.Index → ℝ}
    (hc : Compatible h P.family t) (Y : Finset I) :
    delta h a b (outerSet Y)=delta h a b ∅ := by
  induction Y using Finset.induction_on with
  | empty => simp
  | @insert i Y hi ih =>
    rw [outerSet_insert]
    have hh:=delta_insert_difference h a b (u i) (outerSet Y)
    have hz0:=P.compatible_ai_zero hc i (outerSet Y) (by simp [a]) (by simpa [u] using hi)
    have hz1:=P.compatible_ai_zero hc i (insert b (outerSet Y))
      (by simp [a,b]) (by simpa [u,b] using hi)
    rw [hz0,hz1] at hh
    change delta h a b (insert (u i) (outerSet Y))=delta h a b ∅
    rw [←ih]
    linarith

theorem unique_relation : UniqueIntegrableRelation P.family P.weights := by
  intro t ht
  obtain ⟨h,hn,hc⟩:=ht
  let c:=delta h a b ∅
  have hm (C : P.cells) : t (.inl C)=c := by
    have he:=hc a b (by simp [a,b]) (outerSet C.1.ones) (by simp [a]) (by simp [b])
    rw [P.response_sum_ab _ _ (by simp [a]) (by simp [b]) C
      (by
        have hY : outers (outerSet (H:=Bool) C.1.ones)=C.1.ones := by ext i; simp
        rw [hY]
        exact C.1.matches_ones)] at he
    exact he.symm.trans (P.compatible_ab_constant hc C.1.ones)
  have hb (i : I) : t (.inr i)=(P.missCount i : ℝ)*c := by
    have hz0:=P.compatible_ai_zero hc i (∅ : Finset (Hub I)) (by simp) (by simp)
    have hz1:=P.compatible_ai_zero hc i {b} (by simp [a,b]) (by simp [b,u])
    have hd:=delta_insert_difference h (u i) b a ∅
    rw [delta_comm (u i) b,delta_comm (u i) b,delta_comm (u i) a,delta_comm (u i) a] at hd
    simp only [insert_empty_eq] at hd
    rw [hz0,hz1] at hd
    have h0:=hc b (u i) (by simp [b,u]) ∅ (by simp) (by simp)
    have h1:=hc b (u i) (by simp [b,u]) {a} (by simp [a,b]) (by simp [a,u])
    rw [P.response_sum_bi _ _ _ (by simp) (by simp)] at h0
    rw [P.response_sum_bi _ _ _ (by simp [a,b]) (by simp [a,u])] at h1
    simp only [notMem_empty,not_false_eq_true,if_false,mem_singleton,ite_true] at h0 h1
    have hs : (∑ C : P.cells,if P.misses C i then t (.inl C) else 0)=(P.missCount i : ℝ)*c := by
      simp_rw [hm]
      rw [←sum_filter]
      simp only [sum_const,nsmul_eq_mul,missCount]
    rw [hs] at h0
    linarith
  refine ⟨c,?_⟩
  funext j
  cases j with
  | inl C => simpa [weights] using hm C
  | inr i => simpa [weights,mul_comm] using hb i

theorem boundary_normalized : TranslationNormalized P.boundary := by
  apply assembled_normalized_general
  · constructor
    · simp [Normalized,pair]
    · intro v
      cases v <;> simp [pair]
  · intro i
    simp

theorem boundary_ab (S : Finset (Hub I)) (ha : a∉S) (hb : b∉S) :
    delta P.boundary a b S=1 := by
  have hh : hubs S=∅ := by
    ext v
    cases v <;> simp_all [a,b]
  rw [boundary,a,b,delta_assembled_hubs,hh,delta_pair]
  have hd (i : I) : delta (fun X : Finset Bool => if true∈X then (P.missCount i : ℝ) else 0)
      false true ∅=0 := by simp [delta]
  simp only [hd,ite_self,mul_zero,sum_const_zero,add_zero]

theorem boundary_ai (i : I) (S : Finset (Hub I)) (hi : u i∉S) :
    delta P.boundary a (u i) S=0 := by
  rw [boundary,a,u,delta_assembled_spoke _ _ _ _ _ _ hi]
  simp

theorem boundary_bi (i : I) (S : Finset (Hub I)) (hb : b∉S) (hi : u i∉S) :
    delta P.boundary b (u i) S=(P.missCount i : ℝ) := by
  have hx : true∉hubs S := by simpa [b] using hb
  rw [boundary,b,u,delta_assembled_spoke _ _ _ _ _ _ hi]
  simp [hx]

theorem boundary_outer : OuterZero P.boundary := by
  intro i j hij S hi hj
  exact delta_assembled_outer _ _ _ i j hij S hi hj

theorem missing_sum (i : I) :
    (∑ C : P.cells,if P.misses C i then (1 : ℝ) else 0)=(P.missCount i : ℝ) := by
  rw [←sum_filter]
  simp [missCount]

/-- All conditioning sets are treated, including those outside a cell's
fixed coordinates. -/
theorem central_compatible : Compatible P.boundary P.family P.weights := by
  have hab (S : Finset (Hub I)) (ha : a∉S) (hb : b∉S) :
      delta P.boundary a b S=
        ∑ j : P.Index,P.weights j*negativeResponse (P.family j) a b S := by
    obtain ⟨C,hC,hu⟩:=P.valid (outers S)
    rw [P.boundary_ab S ha hb,P.response_sum_ab _ _ ha hb ⟨C,hC.1⟩ hC.2]
    rfl
  have hai (i : I) (S : Finset (Hub I)) (ha : a∉S) (hi : u i∉S) :
      delta P.boundary a (u i) S=
        ∑ j : P.Index,P.weights j*negativeResponse (P.family j) a (u i) S := by
    rw [P.boundary_ai i S hi,P.response_sum_ai _ _ _ ha hi]
  have hbi (i : I) (S : Finset (Hub I)) (hb : b∉S) (hi : u i∉S) :
      delta P.boundary b (u i) S=
        ∑ j : P.Index,P.weights j*negativeResponse (P.family j) b (u i) S := by
    rw [P.boundary_bi i S hb hi,P.response_sum_bi _ _ _ hb hi]
    by_cases ha : a∈S
    · simp [ha,weights]
    · simp only [ha,ite_false,weights,P.missing_sum]
  have hij (i j : I) (hne : i≠ j) (S : Finset (Hub I)) (hi : u i∉S) (hj : u j∉S) :
      delta P.boundary (u i) (u j) S=
        ∑ k : P.Index,P.weights k*negativeResponse (P.family k) (u i) (u j) S := by
    have hz : delta P.boundary (u i) (u j) S=0 := P.boundary_outer i j hne S hi hj
    rw [hz]
    simp only [P.family_outer_response _ _ _ hne S hi hj,mul_zero,sum_const_zero]
  have swap (x y : Hub I) (S : Finset (Hub I))
      (h : delta P.boundary x y S=
        ∑ j : P.Index,P.weights j*negativeResponse (P.family j) x y S) :
      delta P.boundary y x S=
        ∑ j : P.Index,P.weights j*negativeResponse (P.family j) y x S := by
    simpa only [negativeResponse,delta_comm y x] using h
  intro x y hxy S hx hy
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      cases x <;> cases y
      · exact False.elim (hxy rfl)
      · exact hab S hx hy
      · exact swap a b S (hab S hy hx)
      · exact False.elim (hxy rfl)
    | inr i =>
      cases x
      · exact hai i S hx hy
      · exact hbi i S hx hy
  | inr i =>
    cases y with
    | inl y =>
      cases y
      · exact swap a (u i) S (hai i S hy hx)
      · exact swap b (u i) S (hbi i S hy hx)
    | inr j => exact hij i j (fun he => hxy (congrArg Sum.inr he)) S hx hy

theorem construction_normalized : TranslationNormalized P.construction :=
  assembled_normalized_general P.boundary_normalized P.family P.family_empty P.weights

theorem construction_supermodular : Supermodular P.construction :=
  assembled_supermodular_general P.boundary P.family P.family_monotone P.weights
    (fun j => (P.weights_pos j).le) P.central_compatible

theorem construction_extreme [Nonempty I] : ExtremeSupermodular P.construction := by
  apply positive_circuit_extreme_general P.boundary_normalized P.family_empty P.family_monotone
    P.family_privateRigid (fun j => (P.weights_pos j).le) _ P.central_compatible P.unique_relation
  refine ⟨Sum.inr (Classical.choice ‹Nonempty I›),univ,?_⟩
  simp only [family,weights,(balancing_boolean _).full,mul_one]
  exact ne_of_gt (Nat.cast_pos.mpr (P.missCount_pos _) : (0 : ℝ)< _)

end PartitionData
end GraphicalZonotopes.TwoHub

end
end
end BundlePart214

section BundlePart215
/- Source: Papers/GraphicalZonotopes/TwoHubPartitionGeometry.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.TwoHub.PartitionData
open Finset BooleanModule
open scoped BigOperators Pointwise
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (P : PartitionData I)

theorem construction_graphical : Graphical (graph (I:=I) (J:=P.Index)) P.construction := by
  intro x y hxy hnon S hx hy
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      cases x with
      | inl x =>
        cases y with
        | inl y =>
          cases x <;> cases y <;> simp_all [graph,color]
        | inr i => cases x <;> simp_all [graph,color]
      | inr i =>
        cases y with
        | inl y => cases y <;> simp_all [graph,color]
        | inr j =>
          have hij : i≠ j := fun he => hxy (by subst j; rfl)
          have hi : u i∉hubs S := by simpa [u] using hx
          have hj : u j∉hubs S := by simpa [u] using hy
          rw [construction,delta_assembled_hubs,P.boundary_outer i j hij _ hi hj]
          simp only [P.family_outer_zero _ i j hij _ hi hj,ite_self,mul_zero,sum_const_zero,add_zero]
    | inr j =>
      cases x with
      | inl x => cases x <;> simp_all [graph,color]
      | inr i => simp_all [graph,color]
  | inr i =>
    cases y with
    | inl y =>
      cases y with
      | inl y => cases y <;> simp_all [graph,color]
      | inr j => simp_all [graph,color]
    | inr j =>
      exact delta_assembled_outer _ _ _ i j
        (fun he => hxy (congrArg Sum.inr he)) S hx hy


/-- Positive essential spokes connect every cell vertex and every
coordinate through the two distinguished hubs. -/
theorem family_connected [Nonempty I] : (essentialSpokeGraph P.family).Connected := by
  have ha (j : P.Index) :
      (essentialSpokeGraph P.family).Adj (.inl (a : Hub I)) (.inr j) := by
    cases j with
    | inl C => exact C.1.a_essential
    | inr i => exact balancing_a_essential i
  have hu (i : I) :
      (essentialSpokeGraph P.family).Adj (.inl (u i)) (.inr (.inr i)) :=
    balancing_u_essential i
  let i₀ : I:=Classical.choice ‹Nonempty I›
  have hb : (essentialSpokeGraph P.family).Adj (.inl (b : Hub I)) (.inr (.inr i₀)) :=
    balancing_b_essential i₀
  have reach (v : Hub I⊕P.Index) :
      (essentialSpokeGraph P.family).Reachable v (.inl (a : Hub I)) := by
    cases v with
    | inl v =>
      cases v with
      | inl v =>
        cases v
        · exact SimpleGraph.Reachable.refl _
        · exact hb.reachable.trans (ha (.inr i₀)).reachable.symm
      | inr i => exact (hu i).reachable.trans (ha (.inr i)).reachable.symm
    | inr j => exact (ha j).reachable.symm
  exact ⟨fun x y => (reach x).trans (reach y).symm⟩

theorem construction_fullDimension [Nonempty I] : FullDimension (basePolytope P.construction) := by
  apply finrank_vectorSpan_eq_of_connected_slacks P.construction_normalized.1
    P.construction_supermodular P.family_connected
  intro x y hxy
  exact essential_spoke_slack P.weights_pos hxy

theorem boundary_integer : IntegerValued P.boundary := by
  unfold boundary assembled
  have hz : IntegerValued (pair (0 : ℝ) 0 1) := by simpa using pair_integer 0 0 1
  apply (boundaryLift_integerValued hz).add
  apply IntegerValued.finset_sum
  intro i hi
  simpa only [one_smul,Int.cast_natCast] using
    branchLift_integerValued i
      (IntegerHelpers.conditional (fun S : Finset Bool => true∈S)
        (IntegerHelpers.constant (P.missCount i : ℤ)))

theorem construction_integer : IntegerValued P.construction := by
  unfold construction assembled
  apply (boundaryLift_integerValued P.boundary_integer).add
  apply IntegerValued.finset_sum
  intro j hj
  cases j with
  | inl C => simpa only [weights,family,one_smul] using branchLift_integerValued (Sum.inl C : P.Index) C.1.integer
  | inr i => simpa only [weights,family,Int.cast_natCast] using
      (branchLift_integerValued (Sum.inr i : P.Index) (balancing_boolean i).integerValued).int_smul (P.missCount i : ℤ)

theorem lattice_witness [Nonempty I] :
    LatticePolytope (basePolytope P.construction) ∧
    MinkowskiIndecomposable (basePolytope P.construction) ∧
    FullDimension (basePolytope P.construction) ∧
    IsWeakMinkowskiSummand (basePolytope P.construction)
      (graphicalZonotope (graph (I:=I) (J:=P.Index))) := by
  refine ⟨P.construction_integer.basePolytope P.construction_normalized.1 P.construction_supermodular,
    P.construction_extreme.minkowskiIndecomposable,P.construction_fullDimension,?_⟩
  exact (isWeakMinkowskiSummand_graphical_iff P.construction_normalized.1
    P.construction_supermodular).mpr P.construction_graphical

end GraphicalZonotopes.TwoHub.PartitionData

end
end
end BundlePart215

section BundlePart216
/- Source: Papers/GraphicalZonotopes/TwoHubPartitionCost.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.TwoHub.PartitionData
open Finset
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (P : PartitionData I)

theorem cell_eq_of_fixed_ones {C D : Cell I}
    (hf : C.fixed=D.fixed) (ho : C.ones=D.ones) : C=D := by
  cases C
  cases D
  cases hf
  cases ho
  rfl

def totalDepth : ℕ := ∑ C : P.cells,C.1.fixed.card

/-- The natural-number form of L−k+2, with subtraction performed locally
on the positive depths. `partitionDilation_eq` proves the printed formula. -/
def partitionDilation : ℕ := (∑ C : P.cells,(C.1.fixed.card-1))+2

def fixCount (i : I) : ℕ := (univ.filter (fun C : P.cells => i∈C.1.fixed)).card

theorem depth_positive (C : P.cells) : 1≤ C.1.fixed.card :=
  card_pos.mpr (P.proper C.1 C.2)

theorem sum_pred_depth_add_card :
    (∑ C : P.cells,(C.1.fixed.card-1))+P.cells.card=P.totalDepth := by
  have he : (∑ C : P.cells,((C.1.fixed.card-1)+1))=∑ C : P.cells,C.1.fixed.card := by
    apply sum_congr rfl
    intro C hC
    exact Nat.sub_add_cancel (P.depth_positive C)
  simpa only [sum_add_distrib,sum_const,card_univ,Fintype.card_coe,nsmul_eq_mul,
    mul_one,Nat.cast_id,totalDepth] using he

theorem partitionDilation_eq : P.partitionDilation=P.totalDepth-P.cells.card+2 := by
  have h := P.sum_pred_depth_add_card
  unfold partitionDilation
  omega

theorem partitionDilation_ge_two : 2≤ P.partitionDilation := by
  unfold partitionDilation
  omega

theorem fixed_card_le_partitionDilation (C : P.cells) :
    C.1.fixed.card≤ P.partitionDilation := by
  have hh : C.1.fixed.card-1≤∑ D : P.cells,(D.1.fixed.card-1) :=
    single_le_sum (fun D (_ : D∈(univ : Finset P.cells)) => Nat.zero_le (D.1.fixed.card-1))
      (mem_univ C)
  have hp := P.depth_positive C
  unfold partitionDilation
  omega

/-- There are at most two distinct cube cells with the same singleton
fixed set: the bit fixed there is either zero or one. -/
theorem singleton_fixed_count_le_two (i : I) :
    (univ.filter (fun C : P.cells => C.1.fixed={i})).card≤2 := by
  have hc := card_le_card_of_injOn
    (s := univ.filter (fun C : P.cells => C.1.fixed={i})) (t := (univ : Finset Bool))
    (fun C : P.cells => decide (i∈C.1.ones)) (by intro C hC; exact mem_univ _) (by
      intro C hC D hD he
      have hCf := (mem_filter.mp hC).2
      have hDf := (mem_filter.mp hD).2
      have hbits : i∈C.1.ones ↔ i∈D.1.ones := decide_eq_decide.mp he
      apply Subtype.ext
      apply cell_eq_of_fixed_ones
      · exact hCf.trans hDf.symm
      · ext j
        by_cases hji : j=i
        · subst j
          exact hbits
        · have hCj : j∉C.1.ones := by
            intro hj
            have hf := C.1.ones_subset hj
            rw [hCf] at hf
            exact hji (mem_singleton.mp hf)
          have hDj : j∉D.1.ones := by
            intro hj
            have hf := D.1.ones_subset hj
            rw [hDf] at hf
            exact hji (mem_singleton.mp hf)
          simp only [hCj,hDj,not_false_eq_true])
  simpa only [card_univ,Fintype.card_bool] using hc

theorem fixCount_le_partitionDilation (i : I) : P.fixCount i≤ P.partitionDilation := by
  have hterm (C : P.cells) :
      (if i∈C.1.fixed then 1 else 0)≤ C.1.fixed.card-1+
        (if C.1.fixed={i} then 1 else 0) := by
    by_cases hi : i∈C.1.fixed
    · by_cases hc : C.1.fixed.card=1
      · have he : C.1.fixed={i} :=
          (eq_of_subset_of_card_le (singleton_subset_iff.mpr hi) (by simp [hc])).symm
        simp [hi,he]
      · have hp := P.depth_positive C
        simp only [if_pos hi]
        split_ifs <;> omega
    · simp only [if_neg hi]
      exact Nat.zero_le _
  have hh := sum_le_sum (fun C (_ : C∈(univ : Finset P.cells)) => hterm C)
  simp only [sum_add_distrib,sum_boole,Nat.cast_id] at hh
  have htwo := P.singleton_fixed_count_le_two i
  unfold fixCount partitionDilation
  omega

theorem missCount_le_partitionDilation (i : I) : P.missCount i≤ P.partitionDilation := by
  apply le_trans _ (P.fixCount_le_partitionDilation i)
  apply card_le_card
  intro C hC
  exact mem_filter.mpr ⟨mem_univ _,((mem_filter.mp hC).2).1⟩

end GraphicalZonotopes.TwoHub.PartitionData

end
end
end BundlePart216

section BundlePart217
/- Source: Papers/GraphicalZonotopes/TwoHubModuleBounds.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.TwoHub
open Finset BooleanModule SetFunctionEmbedding
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem present_indicator_sum (ε Y : Finset I) :
    (∑ i∈Y,if i∈ε then (1 : ℝ) else 0)=((Y∩ε).card : ℝ) := by
  have hp : Y.filter (fun i => i∈ε)=Y∩ε := by ext i; simp
  rw [←sum_filter,hp]
  simp

theorem absent_indicator_sum (ε Y : Finset I) :
    (∑ i∈Y,if i∈ε then (0 : ℝ) else 1)=((Y\ε).card : ℝ) := by
  have hn : Y.filter (fun i => i∉ε)=Y\ε := by ext i; simp
  have he : (∑ i∈Y,if i∈ε then (0 : ℝ) else 1)=
      ∑ i∈Y,if i∉ε then (1 : ℝ) else 0 := by
    apply sum_congr rfl
    intro i hi
    by_cases he : i∈ε <;> simp [he]
  rw [he,←sum_filter,hn]
  simp

/-- A single private spoke of module (8.1) is bounded by the number of
coordinates that the module actually uses, including the endpoint one. -/
theorem module_cover_le_card [Nonempty I] (ε : Finset I) (v : Hub I)
    (S : Finset (Hub I)) :
    moduleFunction ε (insert v S)-moduleFunction ε S≤(Fintype.card I : ℝ) := by
  have hp : (1 : ℝ)≤(Fintype.card I : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0< Fintype.card I)
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
    rcases corner_values (decide (i∈ε)) X with h|h <;> rw [h] <;> linarith
  | inl v =>
    have hX : v∉X := by simpa using hv
    rw [←context_insert_hub]
    cases v with
    | false =>
      rcases bool_set_without_false hX with hX0|hX1
      · rw [hX0,insert_empty_eq,module_a_zero_cover,present_indicator_sum]
        by_cases he : ε=∅
        · simp only [he,eta,ite_true,inter_empty,card_empty,Nat.cast_zero,add_zero]
          exact hp
        · have hc : ((Y∩ε).card : ℝ)≤(Fintype.card I : ℝ) := by
            exact_mod_cast card_le_univ (Y∩ε)
          simpa only [eta,if_neg he,zero_add] using hc
      · have hb : insert false ({true} : Finset Bool)=univ := by decide
        rw [hX1,hb,module_a_one_cover,absent_indicator_sum]
        have hs : Y\ε⊆univ\ε := sdiff_subset_sdiff (subset_univ Y) Subset.rfl
        have hc : ((Y\ε).card : ℝ)≤(Fintype.card I : ℝ)-(ε.card : ℝ) := by
          have hh : ((Y\ε).card : ℝ)≤((univ\ε).card : ℝ) := by exact_mod_cast card_le_card hs
          simpa only [card_sdiff_of_subset (subset_univ ε),card_univ,
            Nat.cast_sub (card_le_univ ε)] using hh
        have he : eta ε≤1 := by unfold eta; split_ifs <;> norm_num
        linarith
    | true =>
      rcases bool_set_without_true hX with hX0|hX1
      · rw [hX0,insert_empty_eq,module_b_zero_cover,reverse_signed_sum_card]
        have hc : ((Y∩ε).card : ℝ)≤(ε.card : ℝ) := by
          exact_mod_cast card_le_card (inter_subset_right : Y∩ε⊆ε)
        have hn : (0 : ℝ)≤((Y\ε).card : ℝ) := Nat.cast_nonneg _
        linarith
      · have hb : insert true ({false} : Finset Bool)=univ := by decide
        rw [hX1,hb,module_b_one_cover]
        linarith

theorem Cell.cover_le_fixed_card (C : Cell I) (hC : C.fixed.Nonempty)
    (v : Hub I) (S : Finset (Hub I)) :
    C.function (insert v S)-C.function S≤(C.fixed.card : ℝ) := by
  letI : Nonempty C.fixed := ⟨⟨hC.choose,hC.choose_spec⟩⟩
  by_cases hv : v∈Set.range C.embedding
  · obtain ⟨w,rfl⟩ := hv
    simpa only [Cell.function,extend,pullSet_insert_image,Fintype.card_coe] using
      module_cover_le_card C.assignment w (pullSet C.embedding S)
  · simp only [Cell.function,extend_insert_absent C.embedding _ v hv S,sub_self]
    exact Nat.cast_nonneg _

end GraphicalZonotopes.TwoHub

end
end
end BundlePart217

section BundlePart218
/- Source: Papers/GraphicalZonotopes/TwoHubCellBounds.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.TwoHub
open Finset BooleanModule SetFunctionEmbedding
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem distance_add_missing_le_card (ε Y : Finset I) :
    distance ε Y+((univ\ε)\Y).card≤ Fintype.card I := by
  have h0 := card_sdiff_add_card_inter (univ\ε) Y
  have h1 := card_sdiff_add_card_inter ε Y
  have h2 := card_sdiff_add_card_inter (univ : Finset I) ε
  have he : (univ\ε)∩Y=Y\ε := by ext i; simp [and_comm]
  rw [he] at h0
  simp only [univ_inter,card_univ] at h2
  unfold distance
  omega

theorem Cell.missing_zero_count (C : Cell I) (Y : Finset I) :
    ((univ\C.assignment)\C.pull Y).card=
      (univ.filter (fun i : I => i∈C.fixed ∧ i∉C.ones ∧ i∉Y)).card := by
  let e : C.fixed ↪ I := ⟨Subtype.val,Subtype.val_injective⟩
  have he : (((univ\C.assignment)\C.pull Y).map e)=
      univ.filter (fun i : I => i∈C.fixed ∧ i∉C.ones ∧ i∉Y) := by
    ext i
    constructor
    · intro hi
      obtain ⟨j,hj,rfl⟩ := mem_map.mp hi
      simp only [mem_sdiff,mem_univ,true_and,Cell.mem_assignment,Cell.mem_pull] at hj
      exact mem_filter.mpr ⟨mem_univ _,j.2,hj⟩
    · intro hi
      obtain ⟨hfix,hones,hY⟩ := (mem_filter.mp hi).2
      exact mem_map.mpr ⟨⟨i,hfix⟩,by simp [hones,hY],rfl⟩
  have h := congrArg Finset.card he
  simpa only [card_map] using h

theorem Cell.distance_missing_le_fixed (C : Cell I) (Y : Finset I) :
    (distance C.assignment (C.pull Y) : ℝ)+
      ∑ i : I,(if i∈C.fixed ∧ i∉C.ones then (1 : ℝ) else 0)*
        (if i∈Y then 0 else 1)≤(C.fixed.card : ℝ) := by
  have hs : (∑ i : I,(if i∈C.fixed ∧ i∉C.ones then (1 : ℝ) else 0)*
        (if i∈Y then 0 else 1))=
      ((univ.filter (fun i : I => i∈C.fixed ∧ i∉C.ones ∧ i∉Y)).card : ℝ) := by
    have he : (∑ i : I,(if i∈C.fixed ∧ i∉C.ones then (1 : ℝ) else 0)*
        (if i∈Y then 0 else 1))=
        ∑ i : I,if i∈C.fixed ∧ i∉C.ones ∧ i∉Y then (1 : ℝ) else 0 := by
      apply sum_congr rfl
      intro i hi
      by_cases hf : i∈C.fixed <;> by_cases ho : i∈C.ones <;>
        by_cases hy : i∈Y <;> simp [hf,ho,hy]
    rw [he]
    simp
  rw [hs,←C.missing_zero_count Y]
  have h := distance_add_missing_le_card C.assignment (C.pull Y)
  simpa only [Fintype.card_coe,Nat.cast_add] using (Nat.cast_le.mpr h :
    ((distance C.assignment (C.pull Y)+((univ\C.assignment)\C.pull Y).card : ℕ) : ℝ)≤ _)

theorem Cell.ab_delta_distance (C : Cell I) (S : Finset (Hub I))
    (ha : a∉S) (hb : b∉S) :
    delta C.function a b S=(distance C.assignment (C.pull (outers S)) : ℝ)-1 := by
  change delta (extend C.embedding (moduleFunction C.assignment))
    (C.embedding a) (C.embedding b) S=_
  rw [delta_extend]
  have hd := module_ab_distance C.assignment (C.pull (outers S))
  rw [←C.pullSet_outers S] at hd
  rw [←outer_context_of_hubs_absent (pullSet C.embedding S)
    (by simpa using ha) (by simpa using hb)] at hd
  simpa only [C.pullSet_outers S] using hd

theorem Cell.ai_delta_all (C : Cell I) (i : I) (S : Finset (Hub I))
    (ha : a∉S) (hi : u i∉S) :
    delta C.function a (u i) S=
      if i∈C.fixed then
        (if i∈C.ones then (if b∈S then 0 else 1) else (if b∈S then 1 else 0)) else 0 := by
  by_cases hc : i∈C.fixed
  · let j : C.fixed := ⟨i,hc⟩
    change delta (extend C.embedding (moduleFunction C.assignment))
      (C.embedding a) (C.embedding (u j)) S=_
    rw [delta_extend,module_ai_delta C.assignment j _ (by simpa using ha)
      (by simpa [j] using hi)]
    simp [hc,j,Cell.pullSet_b]
  · have hh : u i∉Set.range C.embedding := fun h => hc ((C.range_u i).mp h)
    rw [delta_comm]
    change delta (extend C.embedding _) (u i) a S=_
    rw [delta_extend_not_range C.embedding _ _ _ hh]
    simp [hc]

theorem Cell.bi_delta_all (C : Cell I) (i : I) (S : Finset (Hub I))
    (hb : b∉S) (hi : u i∉S) :
    delta C.function b (u i) S=
      if i∈C.fixed then (if a∈S then 0 else (if i∈C.ones then 1 else -1)) else 0 := by
  by_cases hc : i∈C.fixed
  · let j : C.fixed := ⟨i,hc⟩
    change delta (extend C.embedding (moduleFunction C.assignment))
      (C.embedding b) (C.embedding (u j)) S=_
    rw [delta_extend,module_bi_delta C.assignment j _ (by simpa using hb)
      (by simpa [j] using hi)]
    simp [hc,j,Cell.pullSet_a]
  · have hh : u i∉Set.range C.embedding := fun h => hc ((C.range_u i).mp h)
    rw [delta_comm]
    change delta (extend C.embedding _) (u i) b S=_
    rw [delta_extend_not_range C.embedding _ _ _ hh]
    simp [hc]

theorem Cell.ai_positive_plus_missing (C : Cell I) (i : I) (S : Finset (Hub I))
    (ha : a∉S) (hi : u i∉S) :
    max 0 (delta C.function a (u i) S)+
      (if i∈C.fixed ∧ i∉C.ones then (1 : ℝ) else 0)*(if b∈S then 0 else 1)≤
      if i∈C.fixed then 1 else 0 := by
  rw [C.ai_delta_all i S ha hi]
  by_cases hf : i∈C.fixed <;> by_cases ho : i∈C.ones <;> by_cases hb : b∈S <;>
    norm_num [hf,ho,hb]

theorem Cell.bi_positive_plus_missing (C : Cell I) (i : I) (S : Finset (Hub I))
    (hb : b∉S) (hi : u i∉S) :
    (if i∈C.fixed ∧ i∉C.ones then (1 : ℝ) else 0)+
      max 0 (delta C.function b (u i) S)≤ if i∈C.fixed then 1 else 0 := by
  rw [C.bi_delta_all i S hb hi]
  by_cases hf : i∈C.fixed <;> by_cases ho : i∈C.ones <;> by_cases ha : a∈S <;>
    norm_num [hf,ho,ha]

end GraphicalZonotopes.TwoHub

end
end
end BundlePart218

section BundlePart219
/- Source: Papers/GraphicalZonotopes/TwoHubDilation.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.TwoHub
open Finset BooleanModule
open scoped BigOperators Pointwise
variable {I : Type*} [Fintype I] [DecidableEq I]

def dilation (p : ℕ) : ℕ := (p-1)*2^p+2

theorem two_mul_missCount (i : I) : 2*missCount i=2^Fintype.card I := by
  have hp : 0< Fintype.card I:=Fintype.card_pos_iff.mpr ⟨i⟩
  rw [missCount_eq,mul_comm,←pow_succ]
  congr 1
  omega

theorem presentCount_eq (i : I) :
    (univ.filter (fun ε : Finset I => i∈ε)).card=missCount i := by
  have hh:=card_filter_add_card_filter_not (s:=(univ : Finset (Finset I))) (fun ε => i∈ε)
  have ht:=two_mul_missCount i
  simp only [card_univ,Fintype.card_finset] at hh
  change (univ.filter (fun ε : Finset I => i∈ε)).card+missCount i=2^Fintype.card I at hh
  omega

theorem present_sum (i : I) :
    (∑ ε : Finset I,if i∈ε then (1 : ℝ) else 0)=(missCount i : ℝ) := by
  rw [←sum_filter]
  simp only [sum_const,nsmul_eq_mul,mul_one,presentCount_eq]

theorem distance_sum (Y : Finset I) :
    (∑ ε : Finset I,(distance ε Y : ℝ))=
      (Fintype.card I : ℝ)*(2^(Fintype.card I-1) : ℝ) := by
  have hdist (ε : Finset I) : (distance ε Y : ℝ)=
      ∑ i : I,if i∈Y then (if i∈ε then 0 else 1) else (if i∈ε then 1 else 0) := by
    have h0 : ε\Y=univ.filter (fun i => i∈ε ∧ i∉Y):=by ext i; simp
    have h1 : Y\ε=univ.filter (fun i => i∈Y ∧ i∉ε):=by ext i; simp
    have hcard (A : Finset I) : (A.card : ℝ)=∑ i∈A,(1 : ℝ):=by simp
    rw [distance,Nat.cast_add,hcard,hcard,h0,h1,sum_filter,sum_filter,←sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    by_cases hε : i∈ε <;> by_cases hY : i∈Y <;> simp [hε,hY]
  simp_rw [hdist]
  rw [sum_comm]
  have hb (i : I) :
      (∑ ε : Finset I,if i∈Y then (if i∈ε then (0 : ℝ) else 1) else (if i∈ε then 1 else 0))=
      (2^(Fintype.card I-1) : ℝ) := by
    by_cases hi : i∈Y
    · simp only [hi,ite_true]
      rw [missing_sum,missCount_eq]
      norm_cast
    · simp only [hi,ite_false]
      rw [present_sum,missCount_eq]
      norm_cast
  simp_rw [hb]
  simp

theorem max_zero_eq_add_negative (x : ℝ) : max 0 x=x+max 0 (-x) := by
  by_cases hx : 0≤ x
  · rw [max_eq_right hx,max_eq_left (neg_nonpos.mpr hx),add_zero]
  · have hx' : x≤0:=le_of_not_ge hx
    rw [max_eq_left hx',max_eq_right (neg_nonneg.mpr hx')]
    ring

theorem positive_ab_sum (S : Finset (Hub I)) (ha : a∉S) (hb : b∉S) :
    (∑ ε : Finset I,max 0 (delta (moduleFunction ε) a b S))=
      (Fintype.card I : ℝ)*(2^(Fintype.card I-1) : ℝ)-(2^Fintype.card I : ℝ)+1 := by
  have he (ε : Finset I) : max 0 (delta (moduleFunction ε) a b S)=
      (distance ε (outers S) : ℝ)-1+(if outers S=ε then 1 else 0) := by
    rw [max_zero_eq_add_negative]
    change delta (moduleFunction ε) a b S+negativeResponse (moduleFunction ε) a b S=_
    rw [module_ab_response_all ε S ha hb]
    have hd:=module_ab_distance ε (outers S)
    rw [←outer_context_of_hubs_absent S ha hb] at hd
    rw [hd]
  simp_rw [he]
  rw [sum_add_distrib,sum_sub_distrib,distance_sum]
  simp

theorem dilation_cast (p : ℕ) (hp : 1≤ p) :
    (dilation p : ℝ)=((p : ℝ)-1)*(2^p : ℝ)+2 := by
  simp only [dilation,Nat.cast_add,Nat.cast_mul,Nat.cast_sub hp,Nat.cast_one,
    Nat.cast_pow,Nat.cast_ofNat]

theorem two_pow_le_dilation (p : ℕ) (hp : 1≤ p) : 2^p≤ dilation p := by
  by_cases he : p=1
  · subst p
    decide
  · have h : 1≤ p-1:=by omega
    have hm:=Nat.mul_le_mul_right (2^p) h
    simp only [one_mul] at hm
    exact hm.trans (Nat.le_add_right _ _)

theorem two_mul_le_dilation (p : ℕ) (hp : 1≤ p) : 2*p≤ dilation p := by
  by_cases he : p=1
  · subst p
    decide
  · have hp2 : 2≤ p:=by omega
    have hpow : 4≤2^p:=by
      have h:=Nat.pow_le_pow_right (by decide : 1≤(2 : ℕ)) hp2
      simpa using h
    have hh:=Nat.mul_le_mul_left (p-1) hpow
    unfold dilation
    nlinarith [Nat.sub_add_cancel hp]

theorem missCount_le_dilation (i : I) : missCount i≤ dilation (Fintype.card I) := by
  have hp : 1≤ Fintype.card I:=Fintype.card_pos_iff.mpr ⟨i⟩
  have hm : missCount i≤2^Fintype.card I:=by have ht:=two_mul_missCount i;omega
  exact hm.trans (two_pow_le_dilation _ hp)

/-- A bound on the total range suffices for every private spoke; it avoids
any implicit restriction on its conditioning set. -/
theorem module_cover_le [Nonempty I] (ε : Finset I) (v : Hub I) (S : Finset (Hub I)) :
    moduleFunction ε (insert v S)-moduleFunction ε S≤2*(Fintype.card I : ℝ) := by
  have hstep (X Z : Finset (Hub I)) : moduleFunction ε X≤ moduleFunction ε (X∪Z) := by
    induction Z using Finset.induction_on with
    | empty => simp
    | @insert v Z hv ih =>
      rw [union_insert]
      exact ih.trans (sub_nonneg.mp (module_cover_nonnegative ε v (X∪Z)))
  have hm : Monotone (moduleFunction ε):=by
    intro X Y hXY
    simpa only [union_eq_right.mpr hXY] using hstep X Y
  have hn : 0 ≤ moduleFunction ε S := by
    simpa using hm (empty_subset S)
  have hu:=hm (subset_univ (insert v S))
  have hc : context (univ : Finset Bool) (univ : Finset I)=univ := by
    ext x
    cases x <;> simp
  have hfull : moduleFunction ε univ=eta ε+2*(Fintype.card I : ℝ)-1 := by
    rw [←hc,module_context]
    simp only [central,pair,mem_univ,and_self,ite_true,corner_full,sum_const,
      card_univ,nsmul_eq_mul,mul_one]
    ring
  have he : eta ε≤1:=by unfold eta;split_ifs <;> norm_num
  rw [hfull] at hu
  linarith

variable {H J : Type*} [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]

theorem assembled_hubs_le (z : SetFunction H) (F : J → SetFunction H) (w : J → ℝ)
    (hw : ∀ j,0≤ w j) (u v : H) (A : Finset (H⊕J)) :
    delta (assembled z F w) (.inl u) (.inl v) A≤
      delta z u v (hubs A)+∑ j,w j*max 0 (delta (F j) u v (hubs A)) := by
  rw [delta_assembled_hubs]
  apply add_le_add (le_refl _)
  apply sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _ (hw j)
  split_ifs
  · exact le_max_right _ _
  · exact le_max_left _ _


theorem positive_ai_main_sum (i : I) (S : Finset (Hub I)) (ha : a∉S) (hi : u i∉S) :
    (∑ ε : Finset I,max 0 (delta (moduleFunction ε) a (u i) S))=(missCount i : ℝ) := by
  have he (ε : Finset I) : max 0 (delta (moduleFunction ε) a (u i) S)=
      if i∈ε then (if b∈S then 0 else 1) else (if b∈S then 1 else 0) := by
    rw [module_ai_delta ε i S ha hi]
    split_ifs <;> norm_num
  simp_rw [he]
  by_cases hb : b∈S
  · simp only [hb,ite_true]
    exact missing_sum i
  · simp only [hb,ite_false]
    exact present_sum i

theorem positive_bi_main_sum_le (i : I) (S : Finset (Hub I)) (hb : b∉S) (hi : u i∉S) :
    (∑ ε : Finset I,max 0 (delta (moduleFunction ε) b (u i) S))≤(missCount i : ℝ) := by
  have he (ε : Finset I) : max 0 (delta (moduleFunction ε) b (u i) S)=
      if a∈S then 0 else (if i∈ε then 1 else 0) := by
    rw [module_bi_delta ε i S hb hi]
    split_ifs <;> norm_num
  simp_rw [he]
  by_cases ha : a∈S
  · simp [ha]
  · simp only [ha,ite_false,present_sum,le_refl]

theorem positive_ai_extra_sum (i : I) (S : Finset (Hub I)) (ha : a∉S) (hi : u i∉S) :
    (∑ j : I,(missCount j : ℝ)*max 0 (delta (balancing j) a (u i) S))=
      if b∈S then 0 else (missCount i : ℝ) := by
  have he (j : I) : max 0 (delta (balancing j) a (u i) S)=
      if j=i then (if b∈S then 0 else 1) else 0 := by
    rw [balancing_ai_delta j i S ha hi]
    split_ifs <;> norm_num
  simp_rw [he]
  by_cases hb : b∈S <;> simp [hb]

theorem positive_bi_extra_sum (i : I) (S : Finset (Hub I)) (hb : b∉S) (hi : u i∉S) :
    (∑ j : I,(missCount j : ℝ)*max 0 (delta (balancing j) b (u i) S))=0 := by
  apply sum_eq_zero
  intro j hj
  rw [balancing_bi_delta j i S hb hi]
  split_ifs <;> norm_num

theorem positive_ab_extra_sum_le (S : Finset (Hub I)) (ha : a∉S) (hb : b∉S) :
    (∑ j : I,(missCount j : ℝ)*max 0 (delta (balancing j) a b S))≤
      (Fintype.card I : ℝ)*(2^(Fintype.card I-1) : ℝ) := by
  calc
    _ ≤ ∑ j : I,(missCount j : ℝ) := by
      apply sum_le_sum
      intro j hj
      rw [balancing_ab_delta j S ha hb]
      split_ifs <;> simp
    _ = _ := by simp only [missCount_eq,Nat.cast_pow,Nat.cast_ofNat,sum_const,
        card_univ,nsmul_eq_mul]

theorem construction_ab_le [Nonempty I] (A : Finset (Hub I⊕Index I))
    (ha : Sum.inl (a : Hub I)∉A) (hb : Sum.inl (b : Hub I)∉A) :
    delta construction (.inl a) (.inl b) A≤(dilation (Fintype.card I) : ℝ) := by
  have ha' : a∉hubs A:=by simpa using ha
  have hb' : b∉hubs A:=by simpa using hb
  have hh:=assembled_hubs_le boundaryCentral family weights (fun j => (weights_pos j).le) a b A
  rw [boundaryCentral_ab _ ha' hb',Fintype.sum_sum_type] at hh
  simp only [family,weights,one_mul] at hh
  rw [positive_ab_sum _ ha' hb'] at hh
  have hbnd:=positive_ab_extra_sum_le (hubs A) ha' hb'
  let i₀ : I:=Classical.choice ‹Nonempty I›
  have ht : (2 : ℝ)*(2^(Fintype.card I-1) : ℝ)=(2^Fintype.card I : ℝ) := by
    have h:=two_mul_missCount i₀
    rw [missCount_eq] at h
    exact_mod_cast h
  have hmul:=congrArg (fun x : ℝ => (Fintype.card I : ℝ)*x) ht
  rw [dilation_cast _ (by have h:=Fintype.card_pos (α:=I);omega)]
  change delta (assembled boundaryCentral family weights) (.inl a) (.inl b) A≤ _
  nlinarith

theorem construction_ai_le (i : I) (A : Finset (Hub I⊕Index I))
    (ha : Sum.inl (a : Hub I)∉A) (hi : Sum.inl (u i)∉A) :
    delta construction (.inl a) (.inl (u i)) A≤(dilation (Fintype.card I) : ℝ) := by
  have ha' : a∉hubs A:=by simpa using ha
  have hi' : u i∉hubs A:=by simpa using hi
  have hh:=assembled_hubs_le boundaryCentral family weights (fun j => (weights_pos j).le) a (u i) A
  rw [boundaryCentral_ai _ _ hi',Fintype.sum_sum_type,zero_add] at hh
  simp only [family,weights,one_mul] at hh
  rw [positive_ai_main_sum _ _ ha' hi',positive_ai_extra_sum _ _ ha' hi'] at hh
  have ht : (2 : ℝ)*(missCount i : ℝ)=(2^Fintype.card I : ℝ):=by exact_mod_cast two_mul_missCount i
  have hm : (2^Fintype.card I : ℝ)≤(dilation (Fintype.card I) : ℝ):=by
    exact_mod_cast two_pow_le_dilation (Fintype.card I) (Fintype.card_pos_iff.mpr ⟨i⟩)
  have hn : 0≤(missCount i : ℝ):=Nat.cast_nonneg _
  change delta (assembled boundaryCentral family weights) (.inl a) (.inl (u i)) A≤ _
  split_ifs at hh <;> linarith

theorem construction_bi_le (i : I) (A : Finset (Hub I⊕Index I))
    (hb : Sum.inl (b : Hub I)∉A) (hi : Sum.inl (u i)∉A) :
    delta construction (.inl b) (.inl (u i)) A≤(dilation (Fintype.card I) : ℝ) := by
  have hb' : b∉hubs A:=by simpa using hb
  have hi' : u i∉hubs A:=by simpa using hi
  have hh:=assembled_hubs_le boundaryCentral family weights (fun j => (weights_pos j).le) b (u i) A
  rw [boundaryCentral_bi _ _ hb' hi',Fintype.sum_sum_type] at hh
  simp only [family,weights,one_mul] at hh
  rw [positive_bi_extra_sum _ _ hb' hi',add_zero] at hh
  have hp:=positive_bi_main_sum_le i (hubs A) hb' hi'
  have ht : (2 : ℝ)*(missCount i : ℝ)=(2^Fintype.card I : ℝ):=by exact_mod_cast two_mul_missCount i
  have hm : (2^Fintype.card I : ℝ)≤(dilation (Fintype.card I) : ℝ):=by
    exact_mod_cast two_pow_le_dilation (Fintype.card I) (Fintype.card_pos_iff.mpr ⟨i⟩)
  change delta (assembled boundaryCentral family weights) (.inl b) (.inl (u i)) A≤ _
  linarith

theorem construction_spoke_le [Nonempty I] (v : Hub I) (j : Index I)
    (A : Finset (Hub I⊕Index I)) (hj : Sum.inr j∉A) :
    delta construction (.inl v) (.inr j) A≤(dilation (Fintype.card I) : ℝ) := by
  rw [construction,delta_assembled_spoke _ _ _ _ _ _ hj]
  cases j with
  | inl ε =>
    simp only [weights,one_mul,family]
    apply (module_cover_le ε v (hubs A)).trans
    exact_mod_cast two_mul_le_dilation (Fintype.card I) (by have h:=Fintype.card_pos (α:=I);omega)
  | inr i =>
    simp only [weights,family]
    have h0:=(balancing_boolean i).values (hubs A)
    have h1:=(balancing_boolean i).values (insert v (hubs A))
    have hb : balancing i (insert v (hubs A))-balancing i (hubs A)≤1:=by
      rcases h0 with h0|h0 <;> rcases h1 with h1|h1 <;> linarith
    calc
      _ ≤ (missCount i : ℝ)*1:=mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
      _ = (missCount i : ℝ):=mul_one _
      _ ≤ _:=by exact_mod_cast missCount_le_dilation i

theorem construction_delta_le [Nonempty I] (x y : Hub I⊕Index I) (hxy : x≠ y)
    (A : Finset (Hub I⊕Index I)) (hx : x∉A) (hy : y∉A) :
    delta construction x y A≤(dilation (Fintype.card I) : ℝ) := by
  have houter (i j : I) (hij : i≠ j)
      (hi : Sum.inl (u i)∉A) (hj : Sum.inl (u j)∉A) :
      delta construction (.inl (u i)) (.inl (u j)) A=0 := by
    apply construction_graphical _ _ (by simpa [u] using hij) ?_ A hi hj
    simp [graph,color,u]
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      cases x with
      | inl x =>
        cases y with
        | inl y =>
          cases x <;> cases y
          · exact False.elim (hxy rfl)
          · exact construction_ab_le A hx hy
          · rw [delta_comm]
            exact construction_ab_le A hy hx
          · exact False.elim (hxy rfl)
        | inr i =>
          cases x
          · exact construction_ai_le i A hx hy
          · exact construction_bi_le i A hx hy
      | inr i =>
        cases y with
        | inl y =>
          rw [delta_comm]
          cases y
          · exact construction_ai_le i A hy hx
          · exact construction_bi_le i A hy hx
        | inr j =>
          change delta construction (.inl (u i)) (.inl (u j)) A≤ _
          rw [houter i j (fun he => hxy (by subst j;rfl)) hx hy]
          exact Nat.cast_nonneg _
    | inr j => exact construction_spoke_le x j A hy
  | inr j =>
    cases y with
    | inl y =>
      rw [delta_comm]
      exact construction_spoke_le y j A hx
    | inr k =>
      rw [construction,delta_assembled_outer _ _ _ j k
        (fun he => hxy (congrArg Sum.inr he)) A hx hy]
      exact Nat.cast_nonneg _

/-- The quantitative part of Theorem8.4: the actual lattice summand uses
precisely the printed dilation, for every positive parameter. -/
theorem exponential_lattice_summand (p : ℕ) (hp : 1≤ p) :
    LatticeExtremeAt (twoSingletonGraph p (2^p+p)) (2^p+2*p+1) ((p-1)*2^p+2) := by
  letI : Nonempty (Fin p):=⟨⟨0,hp⟩⟩
  have hh : LatticeExtremeAt (graph (I:=Fin p) (J:=Index (Fin p)))
      (2^p+2*p+1) (dilation p) := by
    refine ⟨construction,construction_normalized,construction_integer,
      construction_extreme,construction_graphical,?_,?_⟩
    · have hd:=construction_fullDimension (I:=Fin p)
      change Module.finrank ℝ (vectorSpan ℝ (basePolytope (construction (I:=Fin p))))=
        Fintype.card (Hub (Fin p)⊕Index (Fin p))-1 at hd
      rw [hd]
      simp only [Hub,Index,Fintype.card_sum,Fintype.card_bool,Fintype.card_fin,Fintype.card_finset]
      have hpow : 0<(2 : ℕ)^p := by positivity
      omega
    · simpa using construction_delta_le (I:=Fin p)
  let e:=graphIso (I:=Fin p) (J:=Index (Fin p))
  have hm : graph (I:=Fin p) (J:=Index (Fin p))≤
      (twoSingletonGraph (Fintype.card (Fin p)) (Fintype.card (Index (Fin p)))).comap e := by
    intro x y hxy
    exact e.map_adj_iff.mpr hxy
  have he:=hh.embed e.toEquiv.toEmbedding hm
  have hcard : (Fintype.card (Fin p),Fintype.card (Index (Fin p)))=(p,2^p+p) := by
    simp [Index]
  exact Eq.mp (congrArg (fun x : ℕ×ℕ =>
    LatticeExtremeAt (twoSingletonGraph x.1 x.2) (2^p+2*p+1) (dilation p)) hcard) he

end GraphicalZonotopes.TwoHub

end
end
end BundlePart219

section BundlePart220
/- Source: Papers/GraphicalZonotopes/TwoHubPartitionDilation.lean -/







@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace GraphicalZonotopes.TwoHub.PartitionData
open Finset BooleanModule SetFunctionEmbedding
open scoped BigOperators Pointwise
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (P : PartitionData I)

theorem missCount_sum (i : I) :
    (P.missCount i : ℝ)=∑ C : P.cells,if P.misses C i then 1 else 0 := by
  simp [missCount]

theorem partitionDilation_cast :
    (P.partitionDilation : ℝ)=(P.totalDepth : ℝ)-(P.cells.card : ℝ)+2 := by
  have h := congrArg (fun n : ℕ => (n : ℝ)) P.sum_pred_depth_add_card
  simp only [Nat.cast_add] at h
  unfold partitionDilation
  rw [Nat.cast_add]
  norm_num only [Nat.cast_ofNat]
  linarith

theorem positive_ab_sum (S : Finset (Hub I)) (ha : a∉S) (hb : b∉S) :
    (∑ C : P.cells,max 0 (delta C.1.function a b S))=
      (∑ C : P.cells,(distance C.1.assignment (C.1.pull (outers S)) : ℝ))-
        (P.cells.card : ℝ)+1 := by
  have he (C : P.cells) : max 0 (delta C.1.function a b S)=
      (distance C.1.assignment (C.1.pull (outers S)) : ℝ)-1+
        negativeResponse C.1.function a b S := by
    rw [max_zero_eq_add_negative]
    change delta C.1.function a b S+negativeResponse C.1.function a b S=_
    rw [C.1.ab_delta_distance S ha hb]
  obtain ⟨C,hC,hu⟩ := P.valid (outers S)
  have hr := P.response_sum_ab (fun _ => 1) S ha hb ⟨C,hC.1⟩ hC.2
  rw [Fintype.sum_sum_type] at hr
  simp only [family,balancing_ab_response _ _ ha hb,one_mul,sum_const_zero,add_zero] at hr
  simp_rw [he]
  rw [sum_add_distrib,sum_sub_distrib,hr]
  simp

theorem distances_and_balancing_le_depth (Y : Finset I) :
    (∑ C : P.cells,(distance C.1.assignment (C.1.pull Y) : ℝ))+
      ∑ i : I,(P.missCount i : ℝ)*(if i∈Y then 0 else 1)≤(P.totalDepth : ℝ) := by
  have h := sum_le_sum (fun C (_ : C∈(univ : Finset P.cells)) =>
    C.1.distance_missing_le_fixed Y)
  rw [sum_add_distrib] at h
  simp_rw [P.missCount_sum,sum_mul]
  rw [sum_comm]
  simpa only [misses,totalDepth,Nat.cast_sum] using h

theorem positive_balancing_ab_sum (S : Finset (Hub I)) (ha : a∉S) (hb : b∉S) :
    (∑ i : I,(P.missCount i : ℝ)*max 0 (delta (balancing i) a b S))=
      ∑ i : I,(P.missCount i : ℝ)*(if i∈outers S then 0 else 1) := by
  apply sum_congr rfl
  intro i hi
  rw [balancing_ab_delta i S ha hb]
  by_cases hu : u i∈S <;> simp [hu,show (i∈outers S ↔ u i∈S) from by simp [u]]

theorem construction_ab_le (A : Finset (Hub I⊕P.Index))
    (ha : Sum.inl (a : Hub I)∉A) (hb : Sum.inl (b : Hub I)∉A) :
    delta P.construction (.inl a) (.inl b) A≤(P.partitionDilation : ℝ) := by
  have ha' : a∉hubs A := by simpa using ha
  have hb' : b∉hubs A := by simpa using hb
  have h := assembled_hubs_le P.boundary P.family P.weights
    (fun j => (P.weights_pos j).le) a b A
  rw [P.boundary_ab _ ha' hb',Fintype.sum_sum_type] at h
  simp only [family,weights,one_mul] at h
  rw [P.positive_ab_sum _ ha' hb',P.positive_balancing_ab_sum _ ha' hb'] at h
  have hbnd := P.distances_and_balancing_le_depth (outers (hubs A))
  rw [P.partitionDilation_cast]
  change delta (assembled P.boundary P.family P.weights) (.inl a) (.inl b) A≤ _
  linarith

theorem positive_balancing_ai_sum (i : I) (S : Finset (Hub I))
    (ha : a∉S) (hi : u i∉S) :
    (∑ j : I,(P.missCount j : ℝ)*max 0 (delta (balancing j) a (u i) S))=
      (P.missCount i : ℝ)*(if b∈S then 0 else 1) := by
  have he (j : I) : max 0 (delta (balancing j) a (u i) S)=
      if j=i then (if b∈S then 0 else 1) else 0 := by
    rw [balancing_ai_delta j i S ha hi]
    split_ifs <;> norm_num
  simp_rw [he]
  by_cases hb : b∈S <;> simp [hb]

theorem positive_balancing_bi_sum (i : I) (S : Finset (Hub I))
    (hb : b∉S) (hi : u i∉S) :
    (∑ j : I,(P.missCount j : ℝ)*max 0 (delta (balancing j) b (u i) S))=0 := by
  apply sum_eq_zero
  intro j hj
  rw [balancing_bi_delta j i S hb hi]
  split_ifs <;> norm_num

theorem positive_ai_sum_le_fixCount (i : I) (S : Finset (Hub I))
    (ha : a∉S) (hi : u i∉S) :
    (∑ C : P.cells,max 0 (delta C.1.function a (u i) S))+
      (P.missCount i : ℝ)*(if b∈S then 0 else 1)≤(P.fixCount i : ℝ) := by
  rw [P.missCount_sum,sum_mul,←sum_add_distrib]
  have h := sum_le_sum (fun C (_ : C∈(univ : Finset P.cells)) =>
    C.1.ai_positive_plus_missing i S ha hi)
  simpa only [misses,sum_boole,fixCount] using h

theorem positive_bi_sum_le_fixCount (i : I) (S : Finset (Hub I))
    (hb : b∉S) (hi : u i∉S) :
    (P.missCount i : ℝ)+(∑ C : P.cells,max 0 (delta C.1.function b (u i) S))≤
      (P.fixCount i : ℝ) := by
  rw [P.missCount_sum,←sum_add_distrib]
  have h := sum_le_sum (fun C (_ : C∈(univ : Finset P.cells)) =>
    C.1.bi_positive_plus_missing i S hb hi)
  simpa only [misses,sum_boole,fixCount] using h

theorem construction_ai_le (i : I) (A : Finset (Hub I⊕P.Index))
    (ha : Sum.inl (a : Hub I)∉A) (hi : Sum.inl (u i)∉A) :
    delta P.construction (.inl a) (.inl (u i)) A≤(P.partitionDilation : ℝ) := by
  have ha' : a∉hubs A := by simpa using ha
  have hi' : u i∉hubs A := by simpa using hi
  have h := assembled_hubs_le P.boundary P.family P.weights
    (fun j => (P.weights_pos j).le) a (u i) A
  rw [P.boundary_ai _ _ hi',Fintype.sum_sum_type,zero_add] at h
  simp only [family,weights,one_mul] at h
  rw [P.positive_balancing_ai_sum _ _ ha' hi'] at h
  have hmain := P.positive_ai_sum_le_fixCount i (hubs A) ha' hi'
  have hcount : (P.fixCount i : ℝ)≤(P.partitionDilation : ℝ) := by
    exact_mod_cast P.fixCount_le_partitionDilation i
  exact h.trans (hmain.trans hcount)

theorem construction_bi_le (i : I) (A : Finset (Hub I⊕P.Index))
    (hb : Sum.inl (b : Hub I)∉A) (hi : Sum.inl (u i)∉A) :
    delta P.construction (.inl b) (.inl (u i)) A≤(P.partitionDilation : ℝ) := by
  have hb' : b∉hubs A := by simpa using hb
  have hi' : u i∉hubs A := by simpa using hi
  have h := assembled_hubs_le P.boundary P.family P.weights
    (fun j => (P.weights_pos j).le) b (u i) A
  rw [P.boundary_bi _ _ hb' hi',Fintype.sum_sum_type] at h
  simp only [family,weights,one_mul] at h
  rw [P.positive_balancing_bi_sum _ _ hb' hi',add_zero] at h
  have hmain := P.positive_bi_sum_le_fixCount i (hubs A) hb' hi'
  have hcount : (P.fixCount i : ℝ)≤(P.partitionDilation : ℝ) := by
    exact_mod_cast P.fixCount_le_partitionDilation i
  exact h.trans (hmain.trans hcount)

theorem construction_spoke_le (v : Hub I) (j : P.Index)
    (A : Finset (Hub I⊕P.Index)) (hj : Sum.inr j∉A) :
    delta P.construction (.inl v) (.inr j) A≤(P.partitionDilation : ℝ) := by
  rw [construction,delta_assembled_spoke _ _ _ _ _ _ hj]
  cases j with
  | inl C =>
    simp only [weights,one_mul,family]
    apply (C.1.cover_le_fixed_card (P.proper C.1 C.2) v (hubs A)).trans
    exact_mod_cast P.fixed_card_le_partitionDilation C
  | inr i =>
    simp only [weights,family]
    have h0 := (balancing_boolean i).values (hubs A)
    have h1 := (balancing_boolean i).values (insert v (hubs A))
    have hb : balancing i (insert v (hubs A))-balancing i (hubs A)≤1 := by
      rcases h0 with h0|h0 <;> rcases h1 with h1|h1 <;> linarith
    calc
      _ ≤ (P.missCount i : ℝ)*1 := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
      _ = (P.missCount i : ℝ) := mul_one _
      _ ≤ _ := by exact_mod_cast P.missCount_le_partitionDilation i

theorem construction_delta_le (x y : Hub I⊕P.Index) (hxy : x≠ y)
    (A : Finset (Hub I⊕P.Index)) (hx : x∉A) (hy : y∉A) :
    delta P.construction x y A≤(P.partitionDilation : ℝ) := by
  have houter (i j : I) (hij : i≠ j)
      (hi : Sum.inl (u i)∉A) (hj : Sum.inl (u j)∉A) :
      delta P.construction (.inl (u i)) (.inl (u j)) A=0 := by
    apply P.construction_graphical _ _ (by simpa [u] using hij) ?_ A hi hj
    simp [graph,color,u]
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      cases x with
      | inl x =>
        cases y with
        | inl y =>
          cases x <;> cases y
          · exact False.elim (hxy rfl)
          · exact P.construction_ab_le A hx hy
          · rw [delta_comm]
            exact P.construction_ab_le A hy hx
          · exact False.elim (hxy rfl)
        | inr i =>
          cases x
          · exact P.construction_ai_le i A hx hy
          · exact P.construction_bi_le i A hx hy
      | inr i =>
        cases y with
        | inl y =>
          rw [delta_comm]
          cases y
          · exact P.construction_ai_le i A hy hx
          · exact P.construction_bi_le i A hy hx
        | inr j =>
          change delta P.construction (.inl (u i)) (.inl (u j)) A≤ _
          rw [houter i j (fun he => hxy (by subst j; rfl)) hx hy]
          exact Nat.cast_nonneg _
    | inr j => exact P.construction_spoke_le x j A hy
  | inr j =>
    cases y with
    | inl y =>
      rw [delta_comm]
      exact P.construction_spoke_le y j A hx
    | inr k =>
      rw [construction,delta_assembled_outer _ _ _ j k
        (fun he => hxy (congrArg Sum.inr he)) A hx hy]
      exact Nat.cast_nonneg _

theorem lattice_extreme_at [Nonempty I] :
    LatticeExtremeAt (graph (I:=I) (J:=P.Index))
      (P.cells.card+2*Fintype.card I+1) (P.totalDepth-P.cells.card+2) := by
  rw [←P.partitionDilation_eq]
  refine ⟨P.construction,P.construction_normalized,P.construction_integer,
    P.construction_extreme,P.construction_graphical,?_,P.construction_delta_le⟩
  have hd := P.construction_fullDimension
  change Module.finrank ℝ (vectorSpan ℝ (basePolytope P.construction))=
    Fintype.card (Hub I⊕P.Index)-1 at hd
  rw [hd]
  simp only [Hub,Index,Fintype.card_sum,Fintype.card_bool,Fintype.card_coe]
  omega

end GraphicalZonotopes.TwoHub.PartitionData

end
end
end BundlePart220

section BundlePart221
/- Source: Papers/GraphicalZonotopes/CubePartitionLiteral.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.TwoHub
open Finset
open scoped BigOperators Pointwise
variable {I : Type*} [Fintype I] [DecidableEq I]

namespace CellDecisionTree

def totalDepth {C : Cell I} (T : CellDecisionTree C) : ℕ :=
  ∑ D : T.leaves,D.1.fixed.card

/-- The paper's tree hypotheses imply every property required by the
previously checked geometric partition construction. -/
def partitionData [Nonempty I] (T : CellDecisionTree (Cell.root (I:=I)))
    (h : T.tested=univ) : PartitionData I where
  cells:=T.leaves
  valid:=T.root_valid
  proper:=T.root_proper h
  uses:=by simpa only [h] using T.uses_zero

@[simp] theorem partitionData_card [Nonempty I]
    (T : CellDecisionTree (Cell.root (I:=I))) (h : T.tested=univ) :
    (T.partitionData h).cells.card=T.leafCount := T.leaves_card

@[simp] theorem partitionData_totalDepth [Nonempty I]
    (T : CellDecisionTree (Cell.root (I:=I))) (h : T.tested=univ) :
    (T.partitionData h).totalDepth=T.totalDepth := rfl

end CellDecisionTree

/-- The actual integral summand, in exactly the natural-number multipartite
coordinate system used by Lemma8.6. -/
theorem decision_tree_lattice_summand (p : ℕ) (hp : 1≤ p)
    (T : CellDecisionTree (Cell.root (I:=Fin p))) (ht : T.tested=univ) :
    LatticeExtremeAt (twoSingletonGraph p (T.leafCount+p))
      (T.leafCount+2*p+1) (T.totalDepth-T.leafCount+2) := by
  letI : Nonempty (Fin p):=⟨⟨0,hp⟩⟩
  let P:=T.partitionData ht
  have hh:=P.lattice_extreme_at
  let e:=graphIso (I:=Fin p) (J:=P.Index)
  have hm : graph (I:=Fin p) (J:=P.Index)≤
      (twoSingletonGraph (Fintype.card (Fin p)) (Fintype.card P.Index)).comap e := by
    intro x y hxy
    exact e.map_adj_iff.mpr hxy
  have he:=hh.embed e.toEquiv.toEmbedding hm
  have hcard : (Fintype.card (Fin p),Fintype.card P.Index)=(p,T.leafCount+p) := by
    simp [PartitionData.Index,P]
  have he':=Eq.mp (congrArg (fun x : ℕ×ℕ =>
    LatticeExtremeAt (twoSingletonGraph x.1 x.2)
      (P.cells.card+2*Fintype.card (Fin p)+1) (P.totalDepth-P.cells.card+2)) hcard) he
  simpa only [P,CellDecisionTree.partitionData_card,CellDecisionTree.partitionData_totalDepth,
    Fintype.card_fin] using he'

/-- Literal Lemma8.6: every full binary coordinate decision tree testing
all p≥1 coordinates gives a full-dimensional lattice indecomposable weak
summand of K₁,₁,ₚ,ₖ₊ₚ, with a finite polytopal complement at dilation L−k+2.
The two parameters are the actual leaf count and the sum of the sizes of
the leaf fixed-coordinate sets. -/
theorem paper_lemma_8_6 (p : ℕ) (hp : 1≤ p)
    (T : CellDecisionTree (Cell.root (I:=Fin p))) (ht : T.tested=univ) :
    ∃ Q : Set ((Σ i : Fin 4,Fin (![1,1,p,T.leafCount+p] i))→ℝ),
      LatticePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=T.leafCount+2*p+1 ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (twoSingletonGraph p (T.leafCount+p))) ∧
      ∃ R : Set ((Σ i : Fin 4,Fin (![1,1,p,T.leafCount+p] i))→ℝ),
        IsFinitePolytope R ∧ R.Nonempty ∧
        Q+R=(((T.totalDepth-T.leafCount+2 : ℕ) : ℝ) •
          graphicalZonotope (twoSingletonGraph p (T.leafCount+p))) := by
  letI : Nonempty (Fin p):=⟨⟨0,hp⟩⟩
  obtain ⟨Q,hl,hi,hd,hs⟩ := (decision_tree_lattice_summand p hp T ht).polytope
  have hM : (0 : ℝ)<((T.totalDepth-T.leafCount+2 : ℕ) : ℝ) := by positivity
  have hw : IsWeakMinkowskiSummand Q (graphicalZonotope (twoSingletonGraph p (T.leafCount+p))) :=
    ⟨_,hM,hs⟩
  refine ⟨Q,hl,(weakSummand_indecomposable_iff_polytopal hl.finitePolytope hw).mp hi,
    ?_,hd,hw,?_⟩
  · change Module.finrank ℝ (vectorSpan ℝ Q)=
      Fintype.card (Σ i : Fin 4,Fin (![1,1,p,T.leafCount+p] i))-1
    have hc : Fintype.card (Σ i : Fin 4,Fin (![1,1,p,T.leafCount+p] i))=
        p+(T.leafCount+p)+2 := by
      simp [Fintype.card_sigma,Fin.sum_univ_succ]
      omega
    rw [hd,hc]
    omega
  · exact (isMinkowskiSummand_graphical_iff_finite_complement hl.finitePolytope hM.le).mp hs

end GraphicalZonotopes.TwoHub

end
end
end BundlePart221

section BundlePart222
/- Source: Papers/GraphicalZonotopes/DiamondBookGraph.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes.DiamondBook
open Finset
open scoped BigOperators

abbrev Vertex (k : ℕ) := Fin (k+4)
def a (k : ℕ) : Vertex k := ⟨0,by omega⟩
def b (k : ℕ) : Vertex k := ⟨1,by omega⟩
def u (k : ℕ) : Vertex k := ⟨2,by omega⟩
def v (k : ℕ) : Vertex k := ⟨3,by omega⟩

@[simp] theorem a_ne_b (k : ℕ) : a k≠ b k := by
  simp [a,b,Fin.ext_iff]

@[simp] theorem a_ne_u (k : ℕ) : a k≠ u k := by
  simp [a,u,Fin.ext_iff]

@[simp] theorem a_ne_v (k : ℕ) : a k≠ v k := by
  simp [a,v,Fin.ext_iff]

@[simp] theorem b_ne_a (k : ℕ) : b k≠ a k := by
  simp [b,a,Fin.ext_iff]

@[simp] theorem b_ne_u (k : ℕ) : b k≠ u k := by
  simp [b,u,Fin.ext_iff]

@[simp] theorem b_ne_v (k : ℕ) : b k≠ v k := by
  simp [b,v,Fin.ext_iff]

@[simp] theorem u_ne_a (k : ℕ) : u k≠ a k := by
  simp [u,a,Fin.ext_iff]

@[simp] theorem u_ne_b (k : ℕ) : u k≠ b k := by
  simp [u,b,Fin.ext_iff]

@[simp] theorem u_ne_v (k : ℕ) : u k≠ v k := by
  simp [u,v,Fin.ext_iff]

@[simp] theorem v_ne_a (k : ℕ) : v k≠ a k := by
  simp [v,a,Fin.ext_iff]

@[simp] theorem v_ne_b (k : ℕ) : v k≠ b k := by
  simp [v,b,Fin.ext_iff]

@[simp] theorem v_ne_u (k : ℕ) : v k≠ u k := by
  simp [v,u,Fin.ext_iff]

/-- The four actual multipartite classes have sizes1,1,2,k. -/
def part (k : ℕ) (x : Vertex k) : Fin 4 :=
  if x.val=0 then 0 else if x.val=1 then 1 else if x.val<4 then 2 else 3

def graph (k : ℕ) : SimpleGraph (Vertex k) where
  Adj x y:=part k x≠ part k y
  symm:=⟨fun _ _ => Ne.symm⟩
  loopless:=⟨fun _ h => h rfl⟩

instance graphDecidable (k : ℕ) : DecidableRel (graph k).Adj :=
  fun x y => inferInstanceAs (Decidable (part k x≠ part k y))

theorem part_zero_iff (k : ℕ) (x : Vertex k) : part k x=0 ↔ x=a k := by
  constructor
  · intro h
    apply Fin.ext
    change x.val=0
    by_contra hx
    unfold part at h
    rw [if_neg hx] at h
    split_ifs at h <;> norm_num at h
  · intro h
    subst x
    rfl

@[simp] theorem part_a (k : ℕ) : part k (a k)=0 := rfl
@[simp] theorem part_b (k : ℕ) : part k (b k)=1 := rfl
@[simp] theorem part_u (k : ℕ) : part k (u k)=2 := rfl
@[simp] theorem part_v (k : ℕ) : part k (v k)=2 := rfl

theorem part_one_iff (k : ℕ) (x : Vertex k) : part k x=1 ↔ x=b k := by
  simp only [Fin.ext_iff,b]
  unfold part
  split_ifs <;> norm_num <;> omega

theorem part_two_iff (k : ℕ) (x : Vertex k) : part k x=2 ↔ x=u k ∨ x=v k := by
  simp only [Fin.ext_iff,u,v]
  unfold part
  split_ifs <;> norm_num <;> omega

/-- Every tetrahedron uses the two singleton vertices and one vertex from
the two-element part. This is an unrestricted statement for everyk. -/
theorem tetrahedron_contains_boundary (k : ℕ) (C : Finset (Vertex k))
    (hcard : C.card=4) (hc : (graph k).IsClique C) :
    a k∈C ∧ b k∈C ∧ (u k∈C ∨ v k∈C) := by
  have hinj : Set.InjOn (part k) C := by
    intro x hx y hy he
    by_contra hne
    exact hc hx hy hne he
  have himcard : (C.image (part k)).card=4 := (card_image_of_injOn hinj).trans hcard
  have him : C.image (part k)=univ := eq_univ_of_card (C.image (part k)) (by simpa using himcard)
  have hex (i : Fin 4) : ∃ x∈C,part k x=i := by
    apply mem_image.mp
    rw [him]
    exact mem_univ _
  obtain ⟨x,hx,hpx⟩:=hex 0
  obtain ⟨y,hy,hpy⟩:=hex 1
  obtain ⟨z,hz,hpz⟩:=hex 2
  refine ⟨(part_zero_iff k x).mp hpx ▸ hx,(part_one_iff k y).mp hpy ▸ hy,?_⟩
  rcases (part_two_iff k z).mp hpz with he | he
  · exact Or.inl (he ▸ hz)
  · exact Or.inr (he ▸ hz)

theorem admissible_triangle_bound {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} (hH : Admissible H) (T : Finset V) (hT : T.card=3) :
    triangleMultiplicity H T≤3 := by
  classical
  by_cases hc : H.IsClique T
  · exact hH T hT hc
  · have he : (tetrahedra H).filter (fun C => T⊆C)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro C hC
      obtain ⟨hC,hTC⟩:=mem_filter.mp hC
      have hcC : H.IsClique C:=((mem_filter.mp hC).2).2
      exact hc (fun x hx y hy hxy => hcC (hTC hx) (hTC hy) hxy)
    simp [triangleMultiplicity,he]

/-- No member of this unbounded family beyond the capacity threshold has
an admissible spanning3-tree. Counting all actual tetrahedra proves this
without assuming that a chosen construction is a double cone. -/
theorem no_admissible_spanning_threeTree (k : ℕ) (hk : 6≤ k) :
    ¬HasAdmissibleSpanningThreeTree (graph k) := by
  classical
  rintro ⟨H,hsub,hthree,hadm⟩
  let U : Finset (Vertex k):={a k,b k,u k}
  let W : Finset (Vertex k):={a k,b k,v k}
  have hU : U.card=3:=by simp [U,a,b,u,Fin.ext_iff]
  have hW : W.card=3:=by simp [W,a,b,v,Fin.ext_iff]
  have hcapU:=admissible_triangle_bound hadm U hU
  have hcapW:=admissible_triangle_bound hadm W hW
  have hcover : tetrahedra H⊆
      (tetrahedra H).filter (fun C => U⊆C) ∪
      (tetrahedra H).filter (fun C => W⊆C) := by
    intro C hC
    have hc:=((mem_filter.mp hC).2)
    have hcG : (graph k).IsClique C:=fun x hx y hy hxy => hsub (hc.2 hx hy hxy)
    obtain ⟨ha,hb,hu|hv⟩:=tetrahedron_contains_boundary k C hc.1 hcG
    · apply mem_union_left
      exact mem_filter.mpr ⟨hC,by simpa [U,insert_subset_iff,singleton_subset_iff] using And.intro ha (And.intro hb hu)⟩
    · apply mem_union_right
      exact mem_filter.mpr ⟨hC,by simpa [W,insert_subset_iff,singleton_subset_iff] using And.intro ha (And.intro hb hv)⟩
  have hbound:=(card_le_card hcover).trans (card_union_le _ _)
  change (tetrahedra H).card≤ triangleMultiplicity H U+triangleMultiplicity H W at hbound
  have hcount:=ThreeTreeOn.tetrahedra_card hthree
  rw [card_univ,Fintype.card_fin] at hcount
  omega

end GraphicalZonotopes.DiamondBook

end
end
end BundlePart222
