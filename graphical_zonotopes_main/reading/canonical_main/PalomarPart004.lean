module

public import canonical_main.PalomarPart003
import all canonical_main.PalomarPart003
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

section BundlePart223
/- Source: Papers/GraphicalZonotopes/DiamondBookCapacity.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes.DiamondBook
open Finset
open scoped BigOperators
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

def boundary (k : ℕ) : Finset (Vertex k):={a k,b k,u k,v k}
def privateVertex (k : ℕ) (j : Fin k) : Vertex k:=⟨j.val+4,by omega⟩
def privatePart (k : ℕ) (j : Fin k) : Finset (Vertex k):={privateVertex k j}

theorem boundary_card (k : ℕ) : (boundary k).card=4 := by
  simp [boundary,a,b,u,v,Fin.ext_iff]

theorem mem_boundary_iff (k : ℕ) (x : Vertex k) : x∈boundary k ↔ x.val<4 := by
  simp only [boundary,mem_insert,mem_singleton,Fin.ext_iff,a,b,u,v]
  omega

theorem privateVertex_injective (k : ℕ) : Function.Injective (privateVertex k) := by
  intro i j hij
  apply Fin.ext
  have hh:=congrArg Fin.val hij
  change i.val+4=j.val+4 at hh
  omega

theorem private_part_value (k : ℕ) (j : Fin k) : part k (privateVertex k j)=3 := by
  simp [part,privateVertex]

theorem partition (k : ℕ) : Separator.Partition (graph k) (boundary k) (privatePart k) where
  boundary_disjoint j:=by
    apply disjoint_left.mpr
    intro x hx hxp
    have he:x=privateVertex k j:=mem_singleton.mp hxp
    rw [he,mem_boundary_iff] at hx
    change j.val+4<4 at hx
    omega
  private_disjoint:=by
    intro i j hij
    exact disjoint_singleton.mpr (fun he => hij (privateVertex_injective k he))
  cover x:=by
    by_cases hx:x.val<4
    · exact Or.inl ((mem_boundary_iff k x).mpr hx)
    · apply Or.inr
      let j : Fin k:=⟨x.val-4,by have:=x.isLt; omega⟩
      refine ⟨j,?_⟩
      apply mem_singleton.mpr
      apply Fin.ext
      change x.val=(x.val-4)+4
      omega
  no_cross_edge:=by
    intro i j x y hx hy hxy
    have hx':x=privateVertex k i:=mem_singleton.mp hx
    have hy':y=privateVertex k j:=mem_singleton.mp hy
    subst x
    subst y
    change part k (privateVertex k i)≠ part k (privateVertex k j) at hxy
    rw [private_part_value,private_part_value] at hxy
    exact False.elim (hxy rfl)

theorem boundary_cliques_card (k : ℕ) :
    (Separator.boundaryCliques (graph k) (boundary k)).card=7 := by
  classical
  have hp (x : Vertex k) : ({x} : Finset (Vertex k)).powerset={∅,{x}} := by
    ext S
    simp [Finset.subset_singleton_iff]
  norm_num [Separator.boundaryCliques,boundary,IsCliqueCoordinate,
    SimpleGraph.IsClique,Set.Pairwise,graph,part_a,part_b,part_u,part_v,
    Finset.powerset_insert,hp,Finset.filter_insert,Finset.filter_singleton]
  exact of_decide_eq_true rfl

def boundaryEdges (k : ℕ) : Finset (Vertex k × Vertex k):=
  {(a k,b k),(a k,u k),(a k,v k),(b k,u k),(b k,v k)}

theorem boundary_edge_iff (k : ℕ) (x y : Vertex k) :
    (x< y ∧ (graph k).Adj x y ∧ x∈boundary k ∧ y∈boundary k) ↔
      (x,y)∈boundaryEdges k := by
  constructor
  · rintro ⟨hlt,he,hx,hy⟩
    simp only [boundary,mem_insert,mem_singleton] at hx hy
    rcases hx with rfl|rfl|rfl|rfl <;>
      rcases hy with rfl|rfl|rfl|rfl <;>
      norm_num [boundaryEdges,graph,part,a,b,u,v,Fin.lt_def] at *
  · intro he
    simp only [boundaryEdges,mem_insert,mem_singleton,Prod.mk.injEq] at he
    rcases he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
      norm_num [boundary,graph,part,a,b,u,v,Fin.lt_def]

def boundaryEdgeEquiv (k : ℕ) :
    Separator.BoundaryEdge (graph k) (boundary k) ≃ ↥(boundaryEdges k) where
  toFun e:=⟨e.1.1,(boundary_edge_iff k _ _).mp ⟨e.1.2.1,e.1.2.2,e.2⟩⟩
  invFun e:=
    let h:=(boundary_edge_iff k e.1.1 e.1.2).mpr e.2
    ⟨⟨e.1,h.1,h.2.1⟩,h.2.2⟩
  left_inv _:=rfl
  right_inv _:=rfl

theorem common_boundary_ab (k : ℕ) :
    commonNeighbors (graph k) (a k) (b k)∩boundary k={u k,v k} := by
  ext x
  constructor
  · intro hx
    obtain ⟨hn,hB⟩:=mem_inter.mp hx
    simp only [boundary,mem_insert,mem_singleton] at hB
    rcases hB with rfl|rfl|rfl|rfl
    all_goals simp_all [mem_commonNeighbors,graph,part_a,part_b,part_u,part_v]
  · intro hx
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl|rfl
    all_goals apply mem_inter.mpr
    all_goals constructor
    all_goals simp [boundary,mem_commonNeighbors,graph,part_a,part_b,part_u,part_v]

theorem common_boundary_au (k : ℕ) :
    commonNeighbors (graph k) (a k) (u k)∩boundary k={b k} := by
  ext x
  constructor
  · intro hx
    obtain ⟨hn,hB⟩:=mem_inter.mp hx
    simp only [boundary,mem_insert,mem_singleton] at hB
    rcases hB with rfl|rfl|rfl|rfl
    all_goals simp_all [mem_commonNeighbors,graph,part_a,part_b,part_u,part_v]
  · intro hx
    simp only [mem_insert,mem_singleton] at hx
    subst x
    all_goals apply mem_inter.mpr
    all_goals constructor
    all_goals simp [boundary,mem_commonNeighbors,graph,part_a,part_b,part_u,part_v]

theorem common_boundary_av (k : ℕ) :
    commonNeighbors (graph k) (a k) (v k)∩boundary k={b k} := by
  ext x
  constructor
  · intro hx
    obtain ⟨hn,hB⟩:=mem_inter.mp hx
    simp only [boundary,mem_insert,mem_singleton] at hB
    rcases hB with rfl|rfl|rfl|rfl
    all_goals simp_all [mem_commonNeighbors,graph,part_a,part_b,part_u,part_v]
  · intro hx
    simp only [mem_insert,mem_singleton] at hx
    subst x
    all_goals apply mem_inter.mpr
    all_goals constructor
    all_goals simp [boundary,mem_commonNeighbors,graph,part_a,part_b,part_u,part_v]

theorem common_boundary_bu (k : ℕ) :
    commonNeighbors (graph k) (b k) (u k)∩boundary k={a k} := by
  ext x
  constructor
  · intro hx
    obtain ⟨hn,hB⟩:=mem_inter.mp hx
    simp only [boundary,mem_insert,mem_singleton] at hB
    rcases hB with rfl|rfl|rfl|rfl
    all_goals simp_all [mem_commonNeighbors,graph,part_a,part_b,part_u,part_v]
  · intro hx
    simp only [mem_insert,mem_singleton] at hx
    subst x
    all_goals apply mem_inter.mpr
    all_goals constructor
    all_goals simp [boundary,mem_commonNeighbors,graph,part_a,part_b,part_u,part_v]

theorem common_boundary_bv (k : ℕ) :
    commonNeighbors (graph k) (b k) (v k)∩boundary k={a k} := by
  ext x
  constructor
  · intro hx
    obtain ⟨hn,hB⟩:=mem_inter.mp hx
    simp only [boundary,mem_insert,mem_singleton] at hB
    rcases hB with rfl|rfl|rfl|rfl
    all_goals simp_all [mem_commonNeighbors,graph,part_a,part_b,part_u,part_v]
  · intro hx
    simp only [mem_insert,mem_singleton] at hx
    subst x
    all_goals apply mem_inter.mpr
    all_goals constructor
    all_goals simp [boundary,mem_commonNeighbors,graph,part_a,part_b,part_u,part_v]

theorem boundary_rows_count (k : ℕ) :
    (∑ e : Separator.BoundaryEdge (graph k) (boundary k),
      2^(commonNeighbors (graph k) e.1.1.1 e.1.1.2∩boundary k).card)=12 := by
  classical
  have hsum : (∑ e : Separator.BoundaryEdge (graph k) (boundary k),
      2^(commonNeighbors (graph k) e.1.1.1 e.1.1.2∩boundary k).card)=
      ∑ e∈boundaryEdges k,2^(commonNeighbors (graph k) e.1 e.2∩boundary k).card := by
    calc
      _ = ∑ e : ↥(boundaryEdges k),
          (2 : ℕ)^(commonNeighbors (graph k) e.1.1 e.1.2∩boundary k).card :=
        Fintype.sum_equiv (boundaryEdgeEquiv k)
          (fun e : Separator.BoundaryEdge (graph k) (boundary k) =>
            (2 : ℕ)^(commonNeighbors (graph k) e.1.1.1 e.1.1.2∩boundary k).card)
          (fun e : ↥(boundaryEdges k) =>
            (2 : ℕ)^(commonNeighbors (graph k) e.1.1 e.1.2∩boundary k).card)
          (fun _ => rfl)
      _ = _ := sum_coe_sort (boundaryEdges k)
        (fun e : Vertex k × Vertex k =>
          (2 : ℕ)^(commonNeighbors (graph k) e.1 e.2∩boundary k).card)
  rw [hsum]
  simp [boundaryEdges,common_boundary_ab,common_boundary_au,common_boundary_av,
    common_boundary_bu,common_boundary_bv]

/-- The exact diamond separator capacity, independent of the number of
private vertices and allowing every zero private block. -/
theorem active_capacity (k : ℕ) (z : graphicalFunctionSpace (graph k))
    (hz : ExtremeSupermodular z.1) :
    Fintype.card (Gluing.ActiveBranch (((Separator.functionEquiv (partition k)).symm z).2))≤6 := by
  have hb:=Separator.separator_capacity_for_function (partition k) z hz
  rw [boundary_rows_count,boundary_cliques_card] at hb
  exact hb

theorem dimension_le_nine (k : ℕ) (z : graphicalFunctionSpace (graph k))
    (hz : ExtremeSupermodular z.1) :
    Module.finrank ℝ (vectorSpan ℝ (basePolytope z.1))≤9 := by
  have hb:=Separator.finrank_le_boundary_add_active (partition k)
    (fun j => by simp [privatePart]) z hz.2.1
  rw [boundary_card] at hb
  have ha:=active_capacity k z hz
  omega

end GraphicalZonotopes.DiamondBook

end
end
end BundlePart223

section BundlePart224
/- Source: Papers/GraphicalZonotopes/DiamondBookUpperBound.lean -/






@[expose] public section
noncomputable section
namespace GraphicalZonotopes.DiamondBook
open Finset

theorem actual_summand_dimension_bound (k : ℕ) {Q : Set (Vertex k → ℝ)}
    (hQ : IsFinitePolytope Q) (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope (graph k))) :
    Module.finrank ℝ (vectorSpan ℝ Q)≤ min (k+3) 9 := by
  apply le_min
  · have hb:=weak_summand_dimension_le hQ hi hw
    simp only [Fintype.card_fin] at hb
    omega
  · obtain ⟨z,hz,hzero|hext,hd⟩:=weak_summand_extreme_or_zero hQ hi hw
    · rw [hd,hzero,basePolytope_zero,vectorSpan_singleton,finrank_bot]
      norm_num
    · rw [hd]
      exact dimension_le_nine k z hext

/-- The upper half of the paper's complete dimension formula, with its
literal supremum over all actual indecomposable weak polytope summands. -/
theorem maximum_dimension_upper (k : ℕ) :
    maximumIndecomposableDimension (graph k)≤ min (k+3) 9 := by
  apply csSup_le'
  rintro d ⟨Q,hQ,hi,hw,hd⟩
  rw [← hd]
  exact actual_summand_dimension_bound k hQ hi hw

end GraphicalZonotopes.DiamondBook

end
end
end BundlePart224

section BundlePart225
/- Source: Papers/GraphicalZonotopes/DiamondBookSmallTrees.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes.DiamondBook
open Finset
open scoped BigOperators Pointwise
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 8192

instance decidableCliqueGraph {V : Type*} [DecidableEq V] (C : Finset V) :
    DecidableRel (cliqueGraph C).Adj :=
  fun x y => inferInstanceAs (Decidable (x≠ y ∧ x∈C ∧ y∈C))
instance decidableAttachmentStar {V : Type*} [DecidableEq V] (x : V) (T : Finset V) :
    DecidableRel (attachmentStar x T).Adj :=
  fun y z => inferInstanceAs (Decidable (y≠ z ∧ ((y=x ∧ z∈T) ∨ (z=x ∧ y∈T))))

theorem admissible_of_tetrahedron_list {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (F : Finset (Finset V)) (hF : tetrahedra G=F)
    (hcap : ∀ T∈F.biUnion (fun C => C.powerset.filter (fun T => T.card=3)),
      (F.filter (fun C => T⊆C)).card≤3) : Admissible G := by
  classical
  intro T hT hc
  rw [triangleMultiplicity,hF]
  by_cases he : (F.filter (fun C => T⊆C)).Nonempty
  · obtain ⟨C,hC⟩:=he
    obtain ⟨hCF,hTC⟩:=mem_filter.mp hC
    exact hcap T (mem_biUnion.mpr ⟨C,hCF,mem_filter.mpr ⟨mem_powerset.mpr hTC,hT⟩⟩)
  · rw [not_nonempty_iff_eq_empty.mp he,card_empty]
    norm_num

def small1G0 : SimpleGraph (Fin 5) := cliqueGraph {0,1,2,4}
instance small1dec0 : DecidableRel small1G0.Adj := by unfold small1G0; infer_instance
theorem small1tree0 : ThreeTreeOn ({0,1,2,4} : Finset (Fin 5)) small1G0 :=
  ThreeTreeOn.tetrahedron _ (by decide +kernel)
def small1F0 : Finset (Finset (Fin 5)) := {{0,1,2,4}}
theorem small1tetra0 : tetrahedra small1G0=small1F0 :=
  tetrahedra_cliqueGraph (by decide +kernel)

def small1G1 : SimpleGraph (Fin 5) := small1G0 ⊔ attachmentStar 3 {0,1,4}
instance small1dec1 : DecidableRel small1G1.Adj := by unfold small1G1; infer_instance
theorem small1clique1 : small1G0.IsClique ({0,1,4} : Finset (Fin 5)) := by
  unfold small1G0
  decide +kernel
theorem small1tree1 : ThreeTreeOn ({0,1,2,4,3} : Finset (Fin 5)) small1G1 := by
  have h:=ThreeTreeOn.attach small1tree0 (3 : Fin 5) (by decide +kernel)
    ({0,1,4} : Finset (Fin 5)) (by decide +kernel) (by decide +kernel) small1clique1
  simpa only [small1G1,show insert (3 : Fin 5) ({0,1,2,4} : Finset (Fin 5))={0,1,2,4,3} from by decide +kernel] using h
def small1F1 : Finset (Finset (Fin 5)) := insert (insert 3 {0,1,4}) small1F0
theorem small1tetra1 : tetrahedra small1G1=small1F1 := by
  rw [small1G1,tetrahedra_after_attachment small1tree0
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small1clique1,small1tetra0]
  rfl

theorem small1spanning : IsThreeTree small1G1 := by
  change ThreeTreeOn univ small1G1
  have he : ({0,1,2,4,3} : Finset (Fin 5))=univ := by decide +kernel
  simpa only [he] using small1tree1

theorem small1admissible : Admissible small1G1 := by
  apply admissible_of_tetrahedron_list small1G1 small1F1 small1tetra1
  intro T hT
  unfold small1F1 small1F0 at hT ⊢
  fin_cases hT <;> decide +kernel

theorem small1subgraph : small1G1≤ graph 1 := by
  change ∀ x y,small1G1.Adj x y → (graph 1).Adj x y
  unfold small1G1 small1G0
  decide +kernel

def small2G0 : SimpleGraph (Fin 6) := cliqueGraph {0,1,2,4}
instance small2dec0 : DecidableRel small2G0.Adj := by unfold small2G0; infer_instance
theorem small2tree0 : ThreeTreeOn ({0,1,2,4} : Finset (Fin 6)) small2G0 :=
  ThreeTreeOn.tetrahedron _ (by decide +kernel)
def small2F0 : Finset (Finset (Fin 6)) := {{0,1,2,4}}
theorem small2tetra0 : tetrahedra small2G0=small2F0 :=
  tetrahedra_cliqueGraph (by decide +kernel)

def small2G1 : SimpleGraph (Fin 6) := small2G0 ⊔ attachmentStar 3 {0,1,4}
instance small2dec1 : DecidableRel small2G1.Adj := by unfold small2G1; infer_instance
theorem small2clique1 : small2G0.IsClique ({0,1,4} : Finset (Fin 6)) := by
  unfold small2G0
  decide +kernel
theorem small2tree1 : ThreeTreeOn ({0,1,2,4,3} : Finset (Fin 6)) small2G1 := by
  have h:=ThreeTreeOn.attach small2tree0 (3 : Fin 6) (by decide +kernel)
    ({0,1,4} : Finset (Fin 6)) (by decide +kernel) (by decide +kernel) small2clique1
  simpa only [small2G1,show insert (3 : Fin 6) ({0,1,2,4} : Finset (Fin 6))={0,1,2,4,3} from by decide +kernel] using h
def small2F1 : Finset (Finset (Fin 6)) := insert (insert 3 {0,1,4}) small2F0
theorem small2tetra1 : tetrahedra small2G1=small2F1 := by
  rw [small2G1,tetrahedra_after_attachment small2tree0
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small2clique1,small2tetra0]
  rfl

def small2G2 : SimpleGraph (Fin 6) := small2G1 ⊔ attachmentStar 5 {0,1,2}
instance small2dec2 : DecidableRel small2G2.Adj := by unfold small2G2; infer_instance
theorem small2clique2 : small2G1.IsClique ({0,1,2} : Finset (Fin 6)) := by
  unfold small2G1 small2G0
  decide +kernel
theorem small2tree2 : ThreeTreeOn ({0,1,2,4,3,5} : Finset (Fin 6)) small2G2 := by
  have h:=ThreeTreeOn.attach small2tree1 (5 : Fin 6) (by decide +kernel)
    ({0,1,2} : Finset (Fin 6)) (by decide +kernel) (by decide +kernel) small2clique2
  simpa only [small2G2,show insert (5 : Fin 6) ({0,1,2,4,3} : Finset (Fin 6))={0,1,2,4,3,5} from by decide +kernel] using h
def small2F2 : Finset (Finset (Fin 6)) := insert (insert 5 {0,1,2}) small2F1
theorem small2tetra2 : tetrahedra small2G2=small2F2 := by
  rw [small2G2,tetrahedra_after_attachment small2tree1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small2clique2,small2tetra1]
  rfl

theorem small2spanning : IsThreeTree small2G2 := by
  change ThreeTreeOn univ small2G2
  have he : ({0,1,2,4,3,5} : Finset (Fin 6))=univ := by decide +kernel
  simpa only [he] using small2tree2

theorem small2admissible : Admissible small2G2 := by
  apply admissible_of_tetrahedron_list small2G2 small2F2 small2tetra2
  intro T hT
  unfold small2F2 small2F1 small2F0 at hT ⊢
  fin_cases hT <;> decide +kernel

theorem small2subgraph : small2G2≤ graph 2 := by
  change ∀ x y,small2G2.Adj x y → (graph 2).Adj x y
  unfold small2G2 small2G1 small2G0
  decide +kernel

def small3G0 : SimpleGraph (Fin 7) := cliqueGraph {0,1,2,4}
instance small3dec0 : DecidableRel small3G0.Adj := by unfold small3G0; infer_instance
theorem small3tree0 : ThreeTreeOn ({0,1,2,4} : Finset (Fin 7)) small3G0 :=
  ThreeTreeOn.tetrahedron _ (by decide +kernel)
def small3F0 : Finset (Finset (Fin 7)) := {{0,1,2,4}}
theorem small3tetra0 : tetrahedra small3G0=small3F0 :=
  tetrahedra_cliqueGraph (by decide +kernel)

def small3G1 : SimpleGraph (Fin 7) := small3G0 ⊔ attachmentStar 3 {0,1,4}
instance small3dec1 : DecidableRel small3G1.Adj := by unfold small3G1; infer_instance
theorem small3clique1 : small3G0.IsClique ({0,1,4} : Finset (Fin 7)) := by
  unfold small3G0
  decide +kernel
theorem small3tree1 : ThreeTreeOn ({0,1,2,4,3} : Finset (Fin 7)) small3G1 := by
  have h:=ThreeTreeOn.attach small3tree0 (3 : Fin 7) (by decide +kernel)
    ({0,1,4} : Finset (Fin 7)) (by decide +kernel) (by decide +kernel) small3clique1
  simpa only [small3G1,show insert (3 : Fin 7) ({0,1,2,4} : Finset (Fin 7))={0,1,2,4,3} from by decide +kernel] using h
def small3F1 : Finset (Finset (Fin 7)) := insert (insert 3 {0,1,4}) small3F0
theorem small3tetra1 : tetrahedra small3G1=small3F1 := by
  rw [small3G1,tetrahedra_after_attachment small3tree0
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small3clique1,small3tetra0]
  rfl

def small3G2 : SimpleGraph (Fin 7) := small3G1 ⊔ attachmentStar 5 {0,1,2}
instance small3dec2 : DecidableRel small3G2.Adj := by unfold small3G2; infer_instance
theorem small3clique2 : small3G1.IsClique ({0,1,2} : Finset (Fin 7)) := by
  unfold small3G1 small3G0
  decide +kernel
theorem small3tree2 : ThreeTreeOn ({0,1,2,4,3,5} : Finset (Fin 7)) small3G2 := by
  have h:=ThreeTreeOn.attach small3tree1 (5 : Fin 7) (by decide +kernel)
    ({0,1,2} : Finset (Fin 7)) (by decide +kernel) (by decide +kernel) small3clique2
  simpa only [small3G2,show insert (5 : Fin 7) ({0,1,2,4,3} : Finset (Fin 7))={0,1,2,4,3,5} from by decide +kernel] using h
def small3F2 : Finset (Finset (Fin 7)) := insert (insert 5 {0,1,2}) small3F1
theorem small3tetra2 : tetrahedra small3G2=small3F2 := by
  rw [small3G2,tetrahedra_after_attachment small3tree1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small3clique2,small3tetra1]
  rfl

def small3G3 : SimpleGraph (Fin 7) := small3G2 ⊔ attachmentStar 6 {0,1,2}
instance small3dec3 : DecidableRel small3G3.Adj := by unfold small3G3; infer_instance
theorem small3clique3 : small3G2.IsClique ({0,1,2} : Finset (Fin 7)) := by
  unfold small3G2 small3G1 small3G0
  decide +kernel
theorem small3tree3 : ThreeTreeOn ({0,1,2,4,3,5,6} : Finset (Fin 7)) small3G3 := by
  have h:=ThreeTreeOn.attach small3tree2 (6 : Fin 7) (by decide +kernel)
    ({0,1,2} : Finset (Fin 7)) (by decide +kernel) (by decide +kernel) small3clique3
  simpa only [small3G3,show insert (6 : Fin 7) ({0,1,2,4,3,5} : Finset (Fin 7))={0,1,2,4,3,5,6} from by decide +kernel] using h
def small3F3 : Finset (Finset (Fin 7)) := insert (insert 6 {0,1,2}) small3F2
theorem small3tetra3 : tetrahedra small3G3=small3F3 := by
  rw [small3G3,tetrahedra_after_attachment small3tree2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small3clique3,small3tetra2]
  rfl

theorem small3spanning : IsThreeTree small3G3 := by
  change ThreeTreeOn univ small3G3
  have he : ({0,1,2,4,3,5,6} : Finset (Fin 7))=univ := by decide +kernel
  simpa only [he] using small3tree3

theorem small3admissible : Admissible small3G3 := by
  apply admissible_of_tetrahedron_list small3G3 small3F3 small3tetra3
  intro T hT
  unfold small3F3 small3F2 small3F1 small3F0 at hT ⊢
  fin_cases hT <;> decide +kernel

theorem small3subgraph : small3G3≤ graph 3 := by
  change ∀ x y,small3G3.Adj x y → (graph 3).Adj x y
  unfold small3G3 small3G2 small3G1 small3G0
  decide +kernel

def small4G0 : SimpleGraph (Fin 8) := cliqueGraph {0,1,2,4}
instance small4dec0 : DecidableRel small4G0.Adj := by unfold small4G0; infer_instance
theorem small4tree0 : ThreeTreeOn ({0,1,2,4} : Finset (Fin 8)) small4G0 :=
  ThreeTreeOn.tetrahedron _ (by decide +kernel)
def small4F0 : Finset (Finset (Fin 8)) := {{0,1,2,4}}
theorem small4tetra0 : tetrahedra small4G0=small4F0 :=
  tetrahedra_cliqueGraph (by decide +kernel)

def small4G1 : SimpleGraph (Fin 8) := small4G0 ⊔ attachmentStar 3 {0,1,4}
instance small4dec1 : DecidableRel small4G1.Adj := by unfold small4G1; infer_instance
theorem small4clique1 : small4G0.IsClique ({0,1,4} : Finset (Fin 8)) := by
  unfold small4G0
  decide +kernel
theorem small4tree1 : ThreeTreeOn ({0,1,2,4,3} : Finset (Fin 8)) small4G1 := by
  have h:=ThreeTreeOn.attach small4tree0 (3 : Fin 8) (by decide +kernel)
    ({0,1,4} : Finset (Fin 8)) (by decide +kernel) (by decide +kernel) small4clique1
  simpa only [small4G1,show insert (3 : Fin 8) ({0,1,2,4} : Finset (Fin 8))={0,1,2,4,3} from by decide +kernel] using h
def small4F1 : Finset (Finset (Fin 8)) := insert (insert 3 {0,1,4}) small4F0
theorem small4tetra1 : tetrahedra small4G1=small4F1 := by
  rw [small4G1,tetrahedra_after_attachment small4tree0
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small4clique1,small4tetra0]
  rfl

def small4G2 : SimpleGraph (Fin 8) := small4G1 ⊔ attachmentStar 5 {0,1,2}
instance small4dec2 : DecidableRel small4G2.Adj := by unfold small4G2; infer_instance
theorem small4clique2 : small4G1.IsClique ({0,1,2} : Finset (Fin 8)) := by
  unfold small4G1 small4G0
  decide +kernel
theorem small4tree2 : ThreeTreeOn ({0,1,2,4,3,5} : Finset (Fin 8)) small4G2 := by
  have h:=ThreeTreeOn.attach small4tree1 (5 : Fin 8) (by decide +kernel)
    ({0,1,2} : Finset (Fin 8)) (by decide +kernel) (by decide +kernel) small4clique2
  simpa only [small4G2,show insert (5 : Fin 8) ({0,1,2,4,3} : Finset (Fin 8))={0,1,2,4,3,5} from by decide +kernel] using h
def small4F2 : Finset (Finset (Fin 8)) := insert (insert 5 {0,1,2}) small4F1
theorem small4tetra2 : tetrahedra small4G2=small4F2 := by
  rw [small4G2,tetrahedra_after_attachment small4tree1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small4clique2,small4tetra1]
  rfl

def small4G3 : SimpleGraph (Fin 8) := small4G2 ⊔ attachmentStar 6 {0,1,2}
instance small4dec3 : DecidableRel small4G3.Adj := by unfold small4G3; infer_instance
theorem small4clique3 : small4G2.IsClique ({0,1,2} : Finset (Fin 8)) := by
  unfold small4G2 small4G1 small4G0
  decide +kernel
theorem small4tree3 : ThreeTreeOn ({0,1,2,4,3,5,6} : Finset (Fin 8)) small4G3 := by
  have h:=ThreeTreeOn.attach small4tree2 (6 : Fin 8) (by decide +kernel)
    ({0,1,2} : Finset (Fin 8)) (by decide +kernel) (by decide +kernel) small4clique3
  simpa only [small4G3,show insert (6 : Fin 8) ({0,1,2,4,3,5} : Finset (Fin 8))={0,1,2,4,3,5,6} from by decide +kernel] using h
def small4F3 : Finset (Finset (Fin 8)) := insert (insert 6 {0,1,2}) small4F2
theorem small4tetra3 : tetrahedra small4G3=small4F3 := by
  rw [small4G3,tetrahedra_after_attachment small4tree2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small4clique3,small4tetra2]
  rfl

def small4G4 : SimpleGraph (Fin 8) := small4G3 ⊔ attachmentStar 7 {0,1,3}
instance small4dec4 : DecidableRel small4G4.Adj := by unfold small4G4; infer_instance
theorem small4clique4 : small4G3.IsClique ({0,1,3} : Finset (Fin 8)) := by
  unfold small4G3 small4G2 small4G1 small4G0
  decide +kernel
theorem small4tree4 : ThreeTreeOn ({0,1,2,4,3,5,6,7} : Finset (Fin 8)) small4G4 := by
  have h:=ThreeTreeOn.attach small4tree3 (7 : Fin 8) (by decide +kernel)
    ({0,1,3} : Finset (Fin 8)) (by decide +kernel) (by decide +kernel) small4clique4
  simpa only [small4G4,show insert (7 : Fin 8) ({0,1,2,4,3,5,6} : Finset (Fin 8))={0,1,2,4,3,5,6,7} from by decide +kernel] using h
def small4F4 : Finset (Finset (Fin 8)) := insert (insert 7 {0,1,3}) small4F3
theorem small4tetra4 : tetrahedra small4G4=small4F4 := by
  rw [small4G4,tetrahedra_after_attachment small4tree3
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small4clique4,small4tetra3]
  rfl

theorem small4spanning : IsThreeTree small4G4 := by
  change ThreeTreeOn univ small4G4
  have he : ({0,1,2,4,3,5,6,7} : Finset (Fin 8))=univ := by decide +kernel
  simpa only [he] using small4tree4

theorem small4admissible : Admissible small4G4 := by
  apply admissible_of_tetrahedron_list small4G4 small4F4 small4tetra4
  intro T hT
  unfold small4F4 small4F3 small4F2 small4F1 small4F0 at hT ⊢
  fin_cases hT <;> decide +kernel

theorem small4subgraph : small4G4≤ graph 4 := by
  change ∀ x y,small4G4.Adj x y → (graph 4).Adj x y
  unfold small4G4 small4G3 small4G2 small4G1 small4G0
  decide +kernel

def small5G0 : SimpleGraph (Fin 9) := cliqueGraph {0,1,2,4}
instance small5dec0 : DecidableRel small5G0.Adj := by unfold small5G0; infer_instance
theorem small5tree0 : ThreeTreeOn ({0,1,2,4} : Finset (Fin 9)) small5G0 :=
  ThreeTreeOn.tetrahedron _ (by decide +kernel)
def small5F0 : Finset (Finset (Fin 9)) := {{0,1,2,4}}
theorem small5tetra0 : tetrahedra small5G0=small5F0 :=
  tetrahedra_cliqueGraph (by decide +kernel)

def small5G1 : SimpleGraph (Fin 9) := small5G0 ⊔ attachmentStar 3 {0,1,4}
instance small5dec1 : DecidableRel small5G1.Adj := by unfold small5G1; infer_instance
theorem small5clique1 : small5G0.IsClique ({0,1,4} : Finset (Fin 9)) := by
  unfold small5G0
  decide +kernel
theorem small5tree1 : ThreeTreeOn ({0,1,2,4,3} : Finset (Fin 9)) small5G1 := by
  have h:=ThreeTreeOn.attach small5tree0 (3 : Fin 9) (by decide +kernel)
    ({0,1,4} : Finset (Fin 9)) (by decide +kernel) (by decide +kernel) small5clique1
  simpa only [small5G1,show insert (3 : Fin 9) ({0,1,2,4} : Finset (Fin 9))={0,1,2,4,3} from by decide +kernel] using h
def small5F1 : Finset (Finset (Fin 9)) := insert (insert 3 {0,1,4}) small5F0
theorem small5tetra1 : tetrahedra small5G1=small5F1 := by
  rw [small5G1,tetrahedra_after_attachment small5tree0
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small5clique1,small5tetra0]
  rfl

def small5G2 : SimpleGraph (Fin 9) := small5G1 ⊔ attachmentStar 5 {0,1,2}
instance small5dec2 : DecidableRel small5G2.Adj := by unfold small5G2; infer_instance
theorem small5clique2 : small5G1.IsClique ({0,1,2} : Finset (Fin 9)) := by
  unfold small5G1 small5G0
  decide +kernel
theorem small5tree2 : ThreeTreeOn ({0,1,2,4,3,5} : Finset (Fin 9)) small5G2 := by
  have h:=ThreeTreeOn.attach small5tree1 (5 : Fin 9) (by decide +kernel)
    ({0,1,2} : Finset (Fin 9)) (by decide +kernel) (by decide +kernel) small5clique2
  simpa only [small5G2,show insert (5 : Fin 9) ({0,1,2,4,3} : Finset (Fin 9))={0,1,2,4,3,5} from by decide +kernel] using h
def small5F2 : Finset (Finset (Fin 9)) := insert (insert 5 {0,1,2}) small5F1
theorem small5tetra2 : tetrahedra small5G2=small5F2 := by
  rw [small5G2,tetrahedra_after_attachment small5tree1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small5clique2,small5tetra1]
  rfl

def small5G3 : SimpleGraph (Fin 9) := small5G2 ⊔ attachmentStar 6 {0,1,2}
instance small5dec3 : DecidableRel small5G3.Adj := by unfold small5G3; infer_instance
theorem small5clique3 : small5G2.IsClique ({0,1,2} : Finset (Fin 9)) := by
  unfold small5G2 small5G1 small5G0
  decide +kernel
theorem small5tree3 : ThreeTreeOn ({0,1,2,4,3,5,6} : Finset (Fin 9)) small5G3 := by
  have h:=ThreeTreeOn.attach small5tree2 (6 : Fin 9) (by decide +kernel)
    ({0,1,2} : Finset (Fin 9)) (by decide +kernel) (by decide +kernel) small5clique3
  simpa only [small5G3,show insert (6 : Fin 9) ({0,1,2,4,3,5} : Finset (Fin 9))={0,1,2,4,3,5,6} from by decide +kernel] using h
def small5F3 : Finset (Finset (Fin 9)) := insert (insert 6 {0,1,2}) small5F2
theorem small5tetra3 : tetrahedra small5G3=small5F3 := by
  rw [small5G3,tetrahedra_after_attachment small5tree2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small5clique3,small5tetra2]
  rfl

def small5G4 : SimpleGraph (Fin 9) := small5G3 ⊔ attachmentStar 7 {0,1,3}
instance small5dec4 : DecidableRel small5G4.Adj := by unfold small5G4; infer_instance
theorem small5clique4 : small5G3.IsClique ({0,1,3} : Finset (Fin 9)) := by
  unfold small5G3 small5G2 small5G1 small5G0
  decide +kernel
theorem small5tree4 : ThreeTreeOn ({0,1,2,4,3,5,6,7} : Finset (Fin 9)) small5G4 := by
  have h:=ThreeTreeOn.attach small5tree3 (7 : Fin 9) (by decide +kernel)
    ({0,1,3} : Finset (Fin 9)) (by decide +kernel) (by decide +kernel) small5clique4
  simpa only [small5G4,show insert (7 : Fin 9) ({0,1,2,4,3,5,6} : Finset (Fin 9))={0,1,2,4,3,5,6,7} from by decide +kernel] using h
def small5F4 : Finset (Finset (Fin 9)) := insert (insert 7 {0,1,3}) small5F3
theorem small5tetra4 : tetrahedra small5G4=small5F4 := by
  rw [small5G4,tetrahedra_after_attachment small5tree3
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small5clique4,small5tetra3]
  rfl

def small5G5 : SimpleGraph (Fin 9) := small5G4 ⊔ attachmentStar 8 {0,1,3}
instance small5dec5 : DecidableRel small5G5.Adj := by unfold small5G5; infer_instance
theorem small5clique5 : small5G4.IsClique ({0,1,3} : Finset (Fin 9)) := by
  unfold small5G4 small5G3 small5G2 small5G1 small5G0
  decide +kernel
theorem small5tree5 : ThreeTreeOn ({0,1,2,4,3,5,6,7,8} : Finset (Fin 9)) small5G5 := by
  have h:=ThreeTreeOn.attach small5tree4 (8 : Fin 9) (by decide +kernel)
    ({0,1,3} : Finset (Fin 9)) (by decide +kernel) (by decide +kernel) small5clique5
  simpa only [small5G5,show insert (8 : Fin 9) ({0,1,2,4,3,5,6,7} : Finset (Fin 9))={0,1,2,4,3,5,6,7,8} from by decide +kernel] using h
def small5F5 : Finset (Finset (Fin 9)) := insert (insert 8 {0,1,3}) small5F4
theorem small5tetra5 : tetrahedra small5G5=small5F5 := by
  rw [small5G5,tetrahedra_after_attachment small5tree4
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small5clique5,small5tetra4]
  rfl

theorem small5spanning : IsThreeTree small5G5 := by
  change ThreeTreeOn univ small5G5
  have he : ({0,1,2,4,3,5,6,7,8} : Finset (Fin 9))=univ := by decide +kernel
  simpa only [he] using small5tree5

theorem small5admissible : Admissible small5G5 := by
  apply admissible_of_tetrahedron_list small5G5 small5F5 small5tetra5
  intro T hT
  unfold small5F5 small5F4 small5F3 small5F2 small5F1 small5F0 at hT ⊢
  fin_cases hT <;> decide +kernel

theorem small5subgraph : small5G5≤ graph 5 := by
  change ∀ x y,small5G5.Adj x y → (graph 5).Adj x y
  unfold small5G5 small5G4 small5G3 small5G2 small5G1 small5G0
  decide +kernel

/-- Every member below the diamond threshold has an admissible spanning
3-tree. The finite cases exhaust the exact parameter range1≤k≤5. -/
theorem admissible_spanning_small (k : ℕ) (hk : 1≤ k) (hmax : k≤5) :
    HasAdmissibleSpanningThreeTree (graph k) := by
  interval_cases k
  · exact ⟨small1G1,small1subgraph,small1spanning,small1admissible⟩
  · exact ⟨small2G2,small2subgraph,small2spanning,small2admissible⟩
  · exact ⟨small3G3,small3subgraph,small3spanning,small3admissible⟩
  · exact ⟨small4G4,small4subgraph,small4spanning,small4admissible⟩
  · exact ⟨small5G5,small5subgraph,small5spanning,small5admissible⟩

end GraphicalZonotopes.DiamondBook

end
end
end BundlePart225

section BundlePart226
/- Source: Papers/GraphicalZonotopes/DiamondBookSmallDimension.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped Pointwise

/-- The checked3-tree construction yields a full-dimensional extreme
function on every graph containing an admissible spanning3-tree. -/
theorem full_support_of_admissible_spanning_threeTree {n : ℕ} (hn : 4≤ n)
    {G : SimpleGraph (Fin n)} (hG : HasAdmissibleSpanningThreeTree G) :
    ∃ z : SetFunction (Fin n),ExtremeSupermodular z ∧
      FullDimension (basePolytope z) ∧ Graphical G z := by
  obtain ⟨H,hHG,hH,hA⟩:=hG
  obtain ⟨z,hz,hi,hfour,hthree,hd,hdir,hsum⟩:=admissible_threeTree_construction hn hH hA
  have hgraph:=((isMinkowskiSummand_graphical_iff hz.1.1 hz.2.1
    (Nat.cast_nonneg (n-3))).mp hsum).1
  exact ⟨z,hz,hd,hgraph.mono_graph hHG⟩

namespace DiamondBook

theorem small_dimension_lower (k : ℕ) (hk : 1≤ k) (hmax : k≤5) :
    k+3≤ maximumIndecomposableDimension (graph k) := by
  obtain ⟨z,hz,hd,hgraph⟩:=full_support_of_admissible_spanning_threeTree
    (by omega : 4≤ k+4) (admissible_spanning_small k hk hmax)
  have hw:=(isWeakMinkowskiSummand_graphical_iff hz.1.1 hz.2.1).mpr hgraph
  have hfinite : IsFinitePolytope (basePolytope z):=
    (show IsGeneralizedPermutahedron (basePolytope z) from ⟨z,hz.1.1,hz.2.1,rfl⟩).finitePolytope
  have hle:=dimension_le_maximum hfinite hz.minkowskiIndecomposable hw
  change Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=Fintype.card (Fin (k+4))-1 at hd
  rw [hd,Fintype.card_fin] at hle
  omega

end DiamondBook
end GraphicalZonotopes

end
end
end BundlePart226

section BundlePart227
/- Source: Papers/GraphicalZonotopes/DiamondBookLargeDimension.lean -/







@[expose] public section
noncomputable section
namespace GraphicalZonotopes.DiamondBook
open Finset
open scoped Pointwise

def largeEmbedding (k : ℕ) (hk : 6≤ k) : Fin 10 ↪ Vertex k where
  toFun x:=⟨x.val,by have:=x.isLt; omega⟩
  inj' x y h:=Fin.ext (congrArg (fun z : Vertex k => z.val) h)

theorem large_graph_comap (k : ℕ) (hk : 6≤ k) :
    (graph k).comap (largeEmbedding k hk)=graph 6 := by
  apply SimpleGraph.ext
  funext x y
  rfl

theorem diamond_support_subgraph : DiamondGeometry.graph≤ graph 6 := by
  change ∀ x y,DiamondGeometry.graph.Adj x y → (graph 6).Adj x y
  decide +kernel

theorem large_dimension_lower (k : ℕ) (hk : 6≤ k) :
    9≤ maximumIndecomposableDimension (graph k) := by
  let e:=largeEmbedding k hk
  let z:=SetFunctionEmbedding.extend e DiamondGeometry.function
  have hz : ExtremeSupermodular z:=SetFunctionEmbedding.extend_extreme e DiamondGeometry.extreme
  have hgraph0 : Graphical ((graph k).comap e) DiamondGeometry.function := by
    rw [large_graph_comap]
    exact DiamondGeometry.graphical.mono_graph diamond_support_subgraph
  have hgraph : Graphical (graph k) z:=SetFunctionEmbedding.extend_graphical e hgraph0
  have hd : Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=9 := by
    rw [SetFunctionEmbedding.finrank_vectorSpan_extend e DiamondGeometry.normalized]
    exact DiamondGeometry.full_dimension
  have hfinite : IsFinitePolytope (basePolytope z):=
    (show IsGeneralizedPermutahedron (basePolytope z) from ⟨z,hz.1.1,hz.2.1,rfl⟩).finitePolytope
  have hle:=dimension_le_maximum hfinite hz.minkowskiIndecomposable
    ((isWeakMinkowskiSummand_graphical_iff hz.1.1 hz.2.1).mpr hgraph)
  rwa [hd] at hle

theorem diamond_witness :
    ∃ Q : Set (Fin 10 → ℝ),LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      FullDimension Q ∧ IsMinkowskiSummand Q ((4 : ℝ) • graphicalZonotope (graph 6)) ∧
      directionCount Q=25 ∧ ¬HasAdmissibleSpanningThreeTree (graph 6) := by
  refine ⟨basePolytope DiamondGeometry.function,DiamondGeometry.lattice,
    DiamondGeometry.indecomposable,DiamondGeometry.full_dimension,?_,
    DiamondGeometry.direction_count,no_admissible_spanning_threeTree 6 (by norm_num)⟩
  apply (isMinkowskiSummand_graphical_iff DiamondGeometry.normalized.1
    DiamondGeometry.supermodular (by norm_num : (0 : ℝ)≤4)).mpr
  exact ⟨DiamondGeometry.graphical.mono_graph diamond_support_subgraph,
    fun _ _ huv _ _ hu hv => (DiamondGeometry.elemental_bounds huv hu hv).2⟩

end GraphicalZonotopes.DiamondBook

end
end
end BundlePart227

section BundlePart228
/- Source: Papers/GraphicalZonotopes/DiamondPrincipal.lean -/






@[expose] public section
noncomputable section
namespace GraphicalZonotopes.DiamondBook

/-- The unbounded maximum-dimension formula for every positive private-part
size. All lower witnesses and the upper supremum bound refer to actual
indecomposable Minkowski summands. -/
theorem maximum_dimension (k : ℕ) (hk : 1≤ k) :
    maximumIndecomposableDimension (graph k)=min (k+3) 9 := by
  apply le_antisymm (maximum_dimension_upper k)
  by_cases hs:k≤5
  · exact (min_le_left _ _).trans (small_dimension_lower k hk hs)
  · exact (min_le_right _ _).trans (large_dimension_lower k (by omega))

end GraphicalZonotopes.DiamondBook

end
end
end BundlePart228

section BundlePart229
/- Source: Papers/GraphicalZonotopes/DiamondBookIsomorphism.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.DiamondBook
open scoped BigOperators

abbrev MultipartiteVertex (k : ℕ) := Σ i : Fin 4,Fin (![1,1,2,k] i)

/-- The literal coordinate numbering: singleton parts at0,1; the two-element
part at2,3; and the last part at4 throughk+3. -/
def sigmaToVertex (k : ℕ) (x : MultipartiteVertex k) : Vertex k :=
  ⟨if x.1.val=0 then 0 else if x.1.val=1 then 1 else
    if x.1.val=2 then x.2.val+2 else x.2.val+4,by
    rcases x with ⟨i,j⟩
    have hj := j.isLt
    fin_cases i <;> norm_num at hj ⊢ <;> omega⟩

@[simp] theorem part_sigmaToVertex (k : ℕ) (x : MultipartiteVertex k) :
    part k (sigmaToVertex k x)=x.1 := by
  rcases x with ⟨i,j⟩
  have hj := j.isLt
  fin_cases i
  · rfl
  · rfl
  · have hj' : j.val<2 := by simpa using hj
    have h0 : j.val+2≠0 := by omega
    have h1 : j.val+2≠1 := by omega
    have h4 : j.val+2<4 := by omega
    simp [part,sigmaToVertex,h0,h1,h4]
  · have h0 : j.val+4≠0 := by omega
    have h1 : j.val+4≠1 := by omega
    have h4 : ¬j.val+4<4 := by omega
    simp [part,sigmaToVertex,h0,h1,h4]

theorem sigmaToVertex_injective (k : ℕ) : Function.Injective (sigmaToVertex k) := by
  intro x y he
  have hi := congrArg (part k) he
  rw [part_sigmaToVertex,part_sigmaToVertex] at hi
  rcases x with ⟨i,j⟩
  rcases y with ⟨l,m⟩
  change i=l at hi
  subst l
  apply congrArg (Sigma.mk i)
  apply Fin.ext
  have hj := j.isLt
  have hm := m.isLt
  have hv := congrArg Fin.val he
  fin_cases i <;> norm_num [sigmaToVertex] at hj hm hv ⊢ <;> omega

def sigmaEquiv (k : ℕ) : MultipartiteVertex k ≃ Vertex k :=
  Equiv.ofBijective (sigmaToVertex k)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨sigmaToVertex_injective k,by
        simp [MultipartiteVertex,Vertex,Fintype.card_sigma,Fin.sum_univ_succ,
          Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]⟩)

def sigmaGraphIso (k : ℕ) : twoSingletonGraph 2 k ≃g graph k where
  toEquiv := sigmaEquiv k
  map_rel_iff' := by
    intro x y
    change (part k (sigmaToVertex k x)≠ part k (sigmaToVertex k y)) ↔ x.1≠ y.1
    rw [part_sigmaToVertex,part_sigmaToVertex]

/-- The model used for the explicit certificate is exactly the paper's
graph, under an actual bijection of all coordinates for everyk. -/
def graphIso (k : ℕ) : graph k ≃g twoSingletonGraph 2 k := (sigmaGraphIso k).symm

theorem maximum_dimension_model_eq (k : ℕ) :
    maximumIndecomposableDimension (graph k)=
      maximumIndecomposableDimension (twoSingletonGraph 2 k) :=
  maximumIndecomposableDimension_iso (graphIso k)

end GraphicalZonotopes.DiamondBook

end
end
end BundlePart229

section BundlePart230
/- Source: Papers/GraphicalZonotopes/DiamondPaper.lean -/








@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.DiamondBook
open Finset SetFunctionEmbedding
open scoped Pointwise

/-- The obstruction survives the exact bijection to the paper's four-part
coordinate type. The transported object is an actual spanning 3-tree. -/
theorem no_spanning_six_multipartite :
    ¬HasAdmissibleSpanningThreeTree (twoSingletonGraph 2 6) := by
  classical
  rintro ⟨H,hH,hTree,hAdm⟩
  let e := (sigmaGraphIso 6).toEquiv.toEmbedding
  have hsub : H.map e≤ graph 6 := by
    intro x y hxy
    obtain ⟨a,b,hab,rfl,rfl⟩ := (SimpleGraph.map_adj e H x y).mp hxy
    exact (sigmaGraphIso 6).map_adj_iff.mpr (hH hab)
  have htree : IsThreeTree (H.map e) := by
    change ThreeTreeOn univ (H.map e)
    have ht := hTree.map e
    simpa only [e,Finset.map_univ_equiv] using ht
  exact no_admissible_spanning_threeTree 6 (by norm_num)
    ⟨H.map e,hsub,htree,hAdm.map e⟩

/-- Every geometric property of the diamond witness is transported to the
literal multipartite coordinates used in the paper's statement. -/
theorem diamond_witness_multipartite :
    ∃ Q : Set (MultipartiteVertex 6 → ℝ),
      LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsMinkowskiSummand Q ((4 : ℝ) • graphicalZonotope (twoSingletonGraph 2 6)) ∧
      directionCount Q=25 ∧ ¬HasAdmissibleSpanningThreeTree (twoSingletonGraph 2 6) := by
  classical
  let o : LinearOrder (MultipartiteVertex 6) :=
    LinearOrder.lift' (Fintype.equivFin (MultipartiteVertex 6))
      (Fintype.equivFin (MultipartiteVertex 6)).injective
  letI : LinearOrder (MultipartiteVertex 6) :=
    { o with
      toDecidableEq := inferInstance
      compare := fun x y => @compareOfLessAndEq _ x y o.toLT (o.toDecidableLT x y) inferInstance
      compare_eq_compareOfLessAndEq := by intros;rfl }
  let e := (graphIso 6).toEquiv.toEmbedding
  let z := extend e DiamondGeometry.function
  have hz : ExtremeSupermodular z := extend_extreme e DiamondGeometry.extreme
  have hi : IntegerValued z := extend_integer e DiamondGeometry.integerValued
  have hcomap : (twoSingletonGraph 2 6).comap e=graph 6 := by
    ext a b
    exact (graphIso 6).map_adj_iff
  have hg : Graphical (twoSingletonGraph 2 6) z := by
    apply extend_graphical e
    rw [hcomap]
    exact DiamondGeometry.graphical.mono_graph diamond_support_subgraph
  have hd : FullDimension (basePolytope z) := by
    change Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=
      Fintype.card (MultipartiteVertex 6)-1
    change Module.finrank ℝ (vectorSpan ℝ (basePolytope
      (extend e DiamondGeometry.function)))=_
    rw [finrank_vectorSpan_extend e DiamondGeometry.normalized]
    have hh := DiamondGeometry.full_dimension
    change Module.finrank ℝ (vectorSpan ℝ (basePolytope DiamondGeometry.function))=9 at hh
    rw [hh]
    norm_num [MultipartiteVertex,Fintype.card_sigma,Fin.sum_univ_succ]
  have hsum : IsMinkowskiSummand (basePolytope z)
      ((4 : ℝ) • graphicalZonotope (twoSingletonGraph 2 6)) := by
    apply (isMinkowskiSummand_graphical_iff hz.1.1 hz.2.1
      (by norm_num : (0 : ℝ)≤4)).mpr
    refine ⟨hg,?_⟩
    intro u v huv _ S hu hv
    have heval (x : Vertex 6) : e x=(graphIso 6).toEquiv x := rfl
    have hsurj : Function.Surjective e := by
      intro y
      obtain ⟨x,hx⟩ := (graphIso 6).toEquiv.surjective y
      exact ⟨x,(heval x).trans hx⟩
    obtain ⟨a,rfl⟩ := hsurj u
    obtain ⟨b,rfl⟩ := hsurj v
    change delta (extend e DiamondGeometry.function) (e a) (e b) S≤4
    rw [delta_extend]
    exact (DiamondGeometry.elemental_bounds
      (fun he => huv (congrArg e he))
      (by simpa only [mem_pullSet] using hu)
      (by simpa only [mem_pullSet] using hv)).2
  refine ⟨basePolytope z,hi.basePolytope hz.1.1 hz.2.1,
    hz.minkowskiIndecomposable,hd,hsum,?_,no_spanning_six_multipartite⟩
  change directionCount (basePolytope (extend e DiamondGeometry.function))=25
  rw [directionCount_extend e DiamondGeometry.normalized DiamondGeometry.supermodular]
  exact DiamondGeometry.direction_count

/-- Theorem 8.1 in the paper's exact vertex model, with both the unrestricted
dimension formula and every property of the extremal six-branch witness. -/
theorem paper_theorem_8_1 : Targets.DiamondBookClassification := by
  refine ⟨?_,diamond_witness_multipartite⟩
  intro k hk
  rw [← maximum_dimension_model_eq]
  exact maximum_dimension k hk

end GraphicalZonotopes.DiamondBook

end
end
end BundlePart230

section BundlePart231
/- Source: Papers/GraphicalZonotopes/DiamondGeometricObstruction.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset SetFunctionEmbedding
open scoped Pointwise
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Coordinate relabelling preserves the actual full-dimensional weak-summand
existence assertion. No direction graph is assigned by definition. -/
theorem SupportsFullIndecomposable.map_equiv {G : SimpleGraph V}
    (e : V ≃ W) (hn : 2≤ Fintype.card V) (h : SupportsFullIndecomposable G) :
    SupportsFullIndecomposable (G.map e.toEmbedding) := by
  obtain ⟨Q,hQ,hi,hd,hw⟩ := h
  obtain ⟨z,hz,he,hzd⟩ := weak_summand_extreme_or_zero hQ hi hw
  have hdf : Module.finrank ℝ (vectorSpan ℝ (basePolytope z.1))=Fintype.card V-1 := by
    rw [←hzd]
    exact hd
  rcases he with he | he
  · rw [he,basePolytope_zero,_root_.vectorSpan_singleton,_root_.finrank_bot] at hdf
    omega
  · have hfe := extend_extreme e.toEmbedding he
    have hsub : G≤(G.map e.toEmbedding).comap e.toEmbedding := by
      intro u v huv
      exact (SimpleGraph.map_adj e.toEmbedding G (e u) (e v)).mpr ⟨u,v,huv,rfl,rfl⟩
    have hgg : Graphical (G.map e.toEmbedding) (extend e.toEmbedding z.1) :=
      extend_graphical e.toEmbedding (Graphical.mono_graph hsub z.2.2)
    have hp : IsGeneralizedPermutahedron (basePolytope (extend e.toEmbedding z.1)) :=
      ⟨_,hfe.1.1,hfe.2.1,rfl⟩
    refine ⟨_,hp.finitePolytope,hfe.minkowskiIndecomposable,?_,
      (isWeakMinkowskiSummand_graphical_iff hfe.1.1 hfe.2.1).mpr hgg⟩
    change Module.finrank ℝ (vectorSpan ℝ (basePolytope (extend e.toEmbedding z.1)))=
      Fintype.card W-1
    rw [finrank_vectorSpan_extend e.toEmbedding z.2.1,hdf,Fintype.card_congr e]

namespace DiamondBook

/-- The literal geometric obstruction in Theorem 8.1: no spanning 3-tree
contained in the prescribed graph supports a full-dimensional indecomposable
weak Minkowski summand. -/
theorem no_supporting_spanning_threeTree :
    ¬∃ H : SimpleGraph (MultipartiteVertex 6),
      H≤ twoSingletonGraph 2 6 ∧ IsThreeTree H ∧ SupportsFullIndecomposable H := by
  classical
  rintro ⟨H,hsub,htree,hsupport⟩
  let e := (sigmaGraphIso 6).toEquiv
  have hm : IsThreeTree (H.map e.toEmbedding) := by
    change ThreeTreeOn univ (H.map e.toEmbedding)
    simpa only [Finset.map_univ_equiv] using htree.map e.toEmbedding
  have hc : 2≤ Fintype.card (MultipartiteVertex 6) := by
    norm_num [MultipartiteVertex,Fintype.card_sigma,Fin.sum_univ_succ]
  have hs := hsupport.map_equiv e hc
  have ha := (threeTree_supports_iff_admissible (by decide : 4≤10) hm).mp hs
  exact no_spanning_six_multipartite
    ⟨H,hsub,htree,Admissible.of_map e.toEmbedding ha⟩

/-- Both clauses of Theorem 8.1 with the second clause phrased directly in
terms of actual geometric supporting polytopes, in the paper's vertex model. -/
theorem paper_theorem_8_1_literal :
    (∀ k : ℕ,1≤ k → maximumIndecomposableDimension (twoSingletonGraph 2 k)=min (k+3) 9) ∧
    (∃ Q : Set (MultipartiteVertex 6 → ℝ),
      LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsMinkowskiSummand Q ((4 : ℝ) • graphicalZonotope (twoSingletonGraph 2 6)) ∧
      directionCount Q=25) ∧
    ¬∃ H : SimpleGraph (MultipartiteVertex 6),
      H≤ twoSingletonGraph 2 6 ∧ IsThreeTree H ∧ SupportsFullIndecomposable H := by
  obtain ⟨Q,hQ,hi,hd,hs,he,_⟩ := diamond_witness_multipartite
  exact ⟨paper_theorem_8_1.1,⟨Q,hQ,hi,hd,hs,he⟩,no_supporting_spanning_threeTree⟩

end DiamondBook
end GraphicalZonotopes

end
end
end BundlePart231

section BundlePart232
/- Source: Papers/GraphicalZonotopes/DiamondPolytopalCompletion.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- On every actual finite weak summand, ordinary polytopal and compact-convex
indecomposability agree. No full-dimension hypothesis is needed. -/
theorem minkowskiIndecomposable_iff_polytopal_of_weak_summand
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
      change a * graphFunction G ∅=0
      rw [graphFunction_normalized,mul_zero]
    have hzs : Supermodular (a • graphFunction G) :=
      (graphFunction_supermodular G).smul ha.le
    have hsum : Q+R=basePolytope (a • graphFunction G) := by
      rw [basePolytope_smul (graphFunction_normalized G)
        (graphFunction_supermodular G) ha.le,baseGraphFunction_eq_graphicalZonotope]
      exact he
    have hn := lowerSupport_normalized hQ.compact hi.1
    have hsm := summand_lowerSupport_supermodular hzn hzs hQ.compact hR hi.1 hnR hsum
    have hbody := summand_eq_basePolytope hzn hzs hQ.compact hR hQ.convex hi.1 hnR hsum
    exact (minkowskiIndecomposable_iff_polytopal
      ⟨lowerSupport Q,hn,hsm,hbody⟩).mpr hi

/-- The literal dimension supremum with ordinary polytopal decompositions. -/
def maximumPolytopalIndecomposableDimension (G : SimpleGraph V) : ℕ :=
  sSup {d : ℕ | ∃ Q : Set (V → ℝ), IsFinitePolytope Q ∧
    PolytopalMinkowskiIndecomposable Q ∧
    IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
    Module.finrank ℝ (vectorSpan ℝ Q)=d}

/-- Equality of the two dimension invariants, for every finite graph. -/
theorem maximumIndecomposableDimension_eq_polytopal (G : SimpleGraph V) :
    maximumIndecomposableDimension G=maximumPolytopalIndecomposableDimension G := by
  unfold maximumIndecomposableDimension maximumPolytopalIndecomposableDimension
  congr 1
  ext d
  constructor
  · rintro ⟨Q,hQ,hi,hw,hd⟩
    exact ⟨Q,hQ,(minkowskiIndecomposable_iff_polytopal_of_weak_summand hQ hw).mp hi,hw,hd⟩
  · rintro ⟨Q,hQ,hi,hw,hd⟩
    exact ⟨Q,hQ,(minkowskiIndecomposable_iff_polytopal_of_weak_summand hQ hw).mpr hi,hw,hd⟩

/-- Allowing zero as a dilation factor adds no full-dimensional lattice
witness when there are at least two coordinates. -/
theorem not_fullLatticeSummandAt_zero (G : SimpleGraph V)
    (hn : 2≤ Fintype.card V) : ¬FullLatticeSummandAt G 0 := by
  rintro ⟨Q,_,hi,hd,R,_,_,hnR,he⟩
  obtain ⟨r,hr⟩ := hnR
  have hpoint : ∀ q∈Q,q= -r := by
    intro q hq
    have hm : q+r∈(0 : ℝ) • graphicalZonotope G :=
      he ▸ (show q+r∈Q+R from ⟨q,hq,r,hr,rfl⟩)
    obtain ⟨z,_,hz⟩ := hm
    have hqr : q+r=0 := by simpa only [zero_smul] using hz.symm
    calc
      q=q+r-r := by abel
      _= -r := by rw [hqr];simp
  have hQ : Q={-r} := by
    ext q
    constructor
    · intro hq
      exact Set.mem_singleton_iff.mpr (hpoint q hq)
    · intro hq
      have heq := Set.mem_singleton_iff.mp hq
      obtain ⟨q₀,hq₀⟩ := hi.1
      simpa only [heq,hpoint q₀ hq₀] using hq₀
  change Module.finrank ℝ (vectorSpan ℝ Q)=Fintype.card V-1 at hd
  rw [hQ,_root_.vectorSpan_singleton,_root_.finrank_bot] at hd
  omega

namespace DiamondBook

/-- The entire diamond theorem with ordinary polytopal indecomposability
in both its dimension invariant and its literal geometric obstruction. -/
theorem paper_theorem_8_1_polytopal :
    (∀ k : ℕ,1≤ k → maximumPolytopalIndecomposableDimension (twoSingletonGraph 2 k)=
      min (k+3) 9) ∧
    (∃ Q : Set (MultipartiteVertex 6 → ℝ),
      LatticePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsMinkowskiSummand Q ((4 : ℝ) • graphicalZonotope (twoSingletonGraph 2 6)) ∧
      directionCount Q=25) ∧
    ¬∃ H : SimpleGraph (MultipartiteVertex 6),
      H≤ twoSingletonGraph 2 6 ∧ IsThreeTree H ∧
      ∃ Q : Set (MultipartiteVertex 6 → ℝ), IsFinitePolytope Q ∧
        PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope H) := by
  obtain ⟨hm,⟨Q,hQ,hi,hd,hs,he⟩,ho⟩ := paper_theorem_8_1_literal
  refine ⟨?_,⟨Q,hQ,?_,hd,hs,he⟩,?_⟩
  · intro k hk
    rw [←maximumIndecomposableDimension_eq_polytopal]
    exact hm k hk
  · exact ⟨hi.1,fun P R hP hR heq =>
      hi.2 P R hP.compact hR.compact hP.convex hR.convex heq⟩
  · rintro ⟨H,hsub,htree,Q,hfin,hind,hfull,hweak⟩
    apply ho
    exact ⟨H,hsub,htree,Q,hfin,
      (minkowskiIndecomposable_iff_polytopal_of_weak_summand hfin hweak).mpr hind,
      hfull,hweak⟩

end DiamondBook
end GraphicalZonotopes

end
end
end BundlePart232

section BundlePart233
/- Source: Papers/GraphicalZonotopes/GraphFunctionTwins.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Vertices with identical open neighborhoods have identical induced-edge
marginals in every subset avoiding them. -/
theorem graphFunction_insert_twins (G : SimpleGraph V) {u v : V}
    (htwin : ∀ w,G.Adj u w↔G.Adj v w) (S : Finset V) (hu : u∉S) (hv : v∉S) :
    graphFunction G (insert u S)=graphFunction G (insert v S) := by
  classical
  revert hu hv
  induction S using Finset.induction_on with
  | empty =>
    intro hu hv
    simp only [insert_empty_eq,(graphFunction_translationNormalized G).2]
  | @insert w S hw ih =>
    intro hu hv
    have huS : u∉S := fun h => hu (mem_insert_of_mem h)
    have hvS : v∉S := fun h => hv (mem_insert_of_mem h)
    have huw : u≠ w := fun h => hu (by simp [h])
    have hvw : v≠ w := fun h => hv (by simp [h])
    have h1 := graphFunction_delta G huw huS hw
    have h2 := graphFunction_delta G hvw hvS hw
    rw [htwin w] at h1
    have he := ih huS hvS
    unfold delta at h1 h2
    linarith

end GraphicalZonotopes

end
end
end BundlePart233

section BundlePart234
/- Source: Papers/GraphicalZonotopes/FloorHalf.lean -/








@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace GraphicalZonotopes
namespace FloorHalf
open Finset
open scoped BigOperators

/-- The exact carry identity behind every graphical Boolean slack. -/
theorem edge_boolean (m a b : ℤ) :
    (m+a+b+1)/2+m/2-(m+a)/2-(m+b)/2=0 ∨
    (m+a+b+1)/2+m/2-(m+a)/2-(m+b)/2=1 := by omega

theorem edge_boolean_of_mixed (m mu mv muv : ℤ) (h : muv+m-mu-mv=1) :
    muv/2+m/2-mu/2-mv/2=0 ∨ muv/2+m/2-mu/2-mv/2=1 := by omega

/-- Nonadjacent paired vertices have consecutive unrounded marginals, whose
rounding errors cancel exactly. -/
theorem twins_zero (m mu mv muv : ℤ) (hm : muv+m-mu-mv=0)
    (ht : mu+1=mv ∨ mv+1=mu) : muv/2+m/2-mu/2-mv/2=0 := by omega

/-- Four-variable quadratic-phase Möbius coefficient with arbitrary linear
part. This finite identity is later applied through an arbitrary four-clique
restriction; it is not used as a bounded replacement for a graph theorem. -/
def fourPhaseMobius (b : Fin 4 → Bool) : ℤ :=
  ∑ S : Finset (Fin 4),(-1 : ℤ)^(4-S.card)*
    (-1 : ℤ)^(S.card.choose 2+(S.filter (fun i => b i=false)).card)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem fourPhaseMobius_values :
    ∀ b : Fin 4 → Bool,fourPhaseMobius b=4 ∨ fourPhaseMobius b= -4 := by decide

end FloorHalf
end GraphicalZonotopes

end
end BundlePart234

section BundlePart235
/- Source: Papers/GraphicalZonotopes/DoubledPartsBoolean.lean -/







@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset
open scoped BigOperators Pointwise
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The ordinary complete multipartite graph with a pair in each part. -/
def graph (I : Type*) : SimpleGraph (I×Fin 2) where
  Adj u v := u.1≠ v.1
  symm := ⟨fun _ _ => Ne.symm⟩
  loopless := ⟨fun _ h => h rfl⟩

def integerGraphCount (S : Finset (I×Fin 2)) : ℤ :=
  ∑ C∈edgeFamily (graph I),if C⊆S then 1 else 0

def firstWeight (v : I×Fin 2) : ℤ := if v.2=0 then 1 else 0

def integerData (S : Finset (I×Fin 2)) : ℤ :=
  integerGraphCount S+∑ v∈S,firstWeight v

/-- An explicit uniform integral function for all even and odd numbers of
parts: the floor of half the induced-edge count plus first-vertex count. -/
def setFunction (S : Finset (I×Fin 2)) : ℝ := ((integerData S/2 : ℤ) : ℝ)

theorem delta_setFunction (u v : I×Fin 2) (S : Finset (I×Fin 2)) :
    delta setFunction u v S=
      ((integerData (insert u (insert v S))/2+integerData S/2-
        integerData (insert u S)/2-integerData (insert v S)/2 : ℤ) : ℝ) := by
  simp only [delta,setFunction,Int.cast_sub,Int.cast_add]
  ring

theorem cast_integerGraphCount (S : Finset (I×Fin 2)) :
    (integerGraphCount S : ℝ)=graphFunction (graph I) S := by
  simp [integerGraphCount,graphFunction,setMonomial,Finset.sum_apply]

theorem cast_integerData (S : Finset (I×Fin 2)) :
    (integerData S : ℝ)=graphFunction (graph I) S+
      modular (fun v : I×Fin 2 => (firstWeight v : ℝ)) S := by
  simp only [integerData,Int.cast_add,Int.cast_sum,cast_integerGraphCount,modular,subsetSum]

@[simp] theorem integerGraphCount_empty : integerGraphCount (I := I) ∅=0 := by
  apply Int.cast_injective (α := ℝ)
  rw [cast_integerGraphCount,(graphFunction_translationNormalized (graph I)).1]
  norm_num

@[simp] theorem integerGraphCount_singleton (v : I×Fin 2) : integerGraphCount {v}=0 := by
  apply Int.cast_injective (α := ℝ)
  rw [cast_integerGraphCount,(graphFunction_translationNormalized (graph I)).2]
  norm_num

theorem setFunction_translationNormalized : TranslationNormalized (setFunction (I := I)) := by
  constructor
  · change setFunction ∅ = 0
    simp [setFunction, integerData]
  · intro v
    simp only [setFunction, integerData, integerGraphCount_singleton, sum_singleton, zero_add]
    by_cases h : v.2=0 <;> norm_num [firstWeight,h]

theorem integerData_mixed {u v : I×Fin 2} (huv : u≠ v)
    {S : Finset (I×Fin 2)} (hu : u∉S) (hv : v∉S) :
    integerData (insert u (insert v S))+integerData S-
      integerData (insert u S)-integerData (insert v S)=
      if (graph I).Adj u v then 1 else 0 := by
  apply Int.cast_injective (α := ℝ)
  push_cast
  simp only [cast_integerData]
  have hg := graphFunction_delta (graph I) huv hu hv
  have hm := delta_modular (fun v : I×Fin 2 => (firstWeight v : ℝ)) huv hu hv
  unfold delta at hg hm
  split_ifs with h
  · rw [if_pos h] at hg
    linarith
  · rw [if_neg h] at hg
    linarith

theorem integerData_twins_consecutive {u v : I×Fin 2} (huv : u≠ v)
    (hnon : ¬(graph I).Adj u v) {S : Finset (I×Fin 2)} (hu : u∉S) (hv : v∉S) :
    integerData (insert u S)+1=integerData (insert v S) ∨
    integerData (insert v S)+1=integerData (insert u S) := by
  have hp : u.1=v.1 := Classical.not_not.mp hnon
  have ht : ∀ w,(graph I).Adj u w↔(graph I).Adj v w := by
    intro w
    change u.1≠ w.1 ↔ v.1≠ w.1
    rw [hp]
  have hg : integerGraphCount (insert u S)=integerGraphCount (insert v S) := by
    apply Int.cast_injective (α := ℝ)
    rw [cast_integerGraphCount,cast_integerGraphCount]
    exact graphFunction_insert_twins (graph I) ht S hu hv
  have hside : u.2≠ v.2 := fun he => huv (Prod.ext hp he)
  have hw : firstWeight u+1=firstWeight v ∨ firstWeight v+1=firstWeight u := by
    rcases u with ⟨i,a⟩
    rcases v with ⟨j,b⟩
    fin_cases a <;> fin_cases b <;> simp_all [firstWeight]
  simp only [integerData,sum_insert hu,sum_insert hv]
  rcases hw with hw | hw
  · left
    linarith
  · right
    linarith

theorem setFunction_graphical : Graphical (graph I) (setFunction (I := I)) := by
  intro u v huv hnon S hu hv
  have hm := integerData_mixed huv hu hv
  rw [if_neg hnon] at hm
  have ht := integerData_twins_consecutive huv hnon hu hv
  have hh := FloorHalf.twins_zero _ _ _ _ hm ht
  rw [delta_setFunction]
  exact_mod_cast hh

/-- Every original elemental slack is Boolean, uniformly in the number of
parts and in every conditioning subset. -/
theorem setFunction_boolean {u v : I×Fin 2} (huv : u≠ v)
    {S : Finset (I×Fin 2)} (hu : u∉S) (hv : v∉S) :
    delta (setFunction (I := I)) u v S=0 ∨ delta (setFunction (I := I)) u v S=1 := by
  by_cases hadj : (graph I).Adj u v
  · have hm := integerData_mixed huv hu hv
    rw [if_pos hadj] at hm
    have hh := FloorHalf.edge_boolean_of_mixed _ _ _ _ hm
    rcases hh with hh | hh
    · left
      rw [delta_setFunction]
      exact_mod_cast hh
    · right
      rw [delta_setFunction]
      exact_mod_cast hh
  · exact Or.inl (setFunction_graphical u v huv hadj S hu hv)

theorem setFunction_supermodular : Supermodular (setFunction (I := I)) := by
  apply ElementallyNonnegative.supermodular
  intro u v huv S hu hv
  rcases setFunction_boolean huv hu hv with he | he <;> rw [he] <;> norm_num

theorem setFunction_integerValued : IntegerValued (setFunction (I := I)) :=
  fun S => ⟨integerData S/2,rfl⟩

def complementFunction : SetFunction (I×Fin 2) := graphFunction (graph I)-setFunction

theorem complementFunction_translationNormalized :
    TranslationNormalized (complementFunction (I := I)) := by
  constructor
  · change graphFunction (graph I) ∅-setFunction ∅=0
    rw [(graphFunction_translationNormalized _).1,setFunction_translationNormalized.1,sub_self]
  · intro v
    change graphFunction (graph I) {v}-setFunction {v}=0
    rw [(graphFunction_translationNormalized _).2 v,setFunction_translationNormalized.2 v,sub_self]

theorem complementFunction_supermodular : Supermodular (complementFunction (I := I)) := by
  have h := graphical_complement_supermodular (G := graph I) (z := setFunction) setFunction_graphical (show (0 : ℝ)≤1 by norm_num)
    (fun u v huv _ S hu hv => by
      rcases setFunction_boolean huv hu hv with he | he <;> rw [he] <;> norm_num)
  simpa only [complementFunction,one_smul] using h

theorem complementFunction_integerValued : IntegerValued (complementFunction (I := I)) :=
  (graphFunction_integerValued _).sub setFunction_integerValued

def polytope : Set ((I×Fin 2) → ℝ) := basePolytope setFunction
def complementPolytope : Set ((I×Fin 2) → ℝ) := basePolytope complementFunction

theorem polytope_lattice : LatticePolytope (polytope (I := I)) :=
  setFunction_integerValued.basePolytope setFunction_translationNormalized.1 setFunction_supermodular

theorem complementPolytope_lattice : LatticePolytope (complementPolytope (I := I)) :=
  complementFunction_integerValued.basePolytope complementFunction_translationNormalized.1
    complementFunction_supermodular

theorem polytope_add_complement :
    polytope (I := I)+complementPolytope=graphicalZonotope (graph I) := by
  rw [polytope,complementPolytope,←basePolytope_add setFunction_translationNormalized.1
    complementFunction_translationNormalized.1 setFunction_supermodular complementFunction_supermodular]
  rw [show (setFunction (I := I)+complementFunction)=graphFunction (graph I) by
    unfold complementFunction
    abel,baseGraphFunction_eq_graphicalZonotope]

end DoubledParts
end GraphicalZonotopes

end
end
end BundlePart235

section BundlePart236
/- Source: Papers/GraphicalZonotopes/QuadraticSignAlgebra.lean -/














@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace QuadraticSign
open Finset
open scoped symmDiff

/-- The real sign of a parity, written over the natural numbers so that no
representative of an element of `𝔽₂` is chosen implicitly. -/
def parity (n : ℕ) : ℝ := (-1 : ℝ)^n

def triangle (n : ℕ) : ℝ := parity (n.choose 2)

@[simp] theorem parity_zero : parity 0=1 := by simp [parity]
@[simp] theorem parity_one : parity 1=-1 := by simp [parity]
@[simp] theorem parity_add (m n : ℕ) : parity (m+n)=parity m*parity n := by
  simp only [parity,pow_add]
@[simp] theorem parity_square (n : ℕ) : parity n*parity n=1 := by
  simp [parity,← mul_pow]
theorem parity_ne_zero (n : ℕ) : parity n≠0 := pow_ne_zero _ (by norm_num)

theorem parity_mod_two (n : ℕ) : parity n=parity (n%2) :=
  neg_one_pow_eq_pow_mod_two n

theorem parity_mul (m n : ℕ) :
    parity (m*n)=if Even m then 1 else parity n := by
  rw [parity,pow_mul,neg_one_pow_eq_ite]
  split_ifs <;> simp [parity]

@[simp] theorem triangle_zero : triangle 0=1 := by simp [triangle]
@[simp] theorem triangle_one : triangle 1=1 := by simp [triangle]
@[simp] theorem triangle_square (n : ℕ) : triangle n*triangle n=1 := by
  exact parity_square _
theorem triangle_ne_zero (n : ℕ) : triangle n≠0 := parity_ne_zero _

theorem triangle_succ (n : ℕ) : triangle (n+1)=triangle n*parity n := by
  change parity ((n+1).choose (1+1))=triangle n*parity n
  rw [Nat.choose_succ_succ',Nat.choose_one_right,parity_add]
  exact mul_comm _ _

theorem triangle_add (m n : ℕ) :
    triangle (m+n)=triangle m*triangle n*parity (m*n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show m+(n+1)=(m+n)+1 by omega,triangle_succ,ih,
      triangle_succ,parity_add,show m*(n+1)=m*n+m by ring,parity_add]
    ring

theorem triangle_add_two (n : ℕ) : triangle (n+2)= -triangle n := by
  rw [show n+2=(n+1)+1 by omega,triangle_succ,triangle_succ,parity_add]
  simp only [parity_one]
  calc
    triangle n*parity n*(parity n*(-1)) =
        -(triangle n*(parity n*parity n)) := by ring
    _ = -triangle n := by rw [parity_square,mul_one]

theorem triangle_add_twice (n k : ℕ) :
    triangle (n+2*k)=triangle n*parity k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show n+2*(k+1)=(n+2*k)+2 by omega,triangle_add_two,ih,parity_add]
    simp

variable {I : Type*} [DecidableEq I]

theorem card_symmDiff_add_twice_inter (A B : Finset I) :
    (A∆B).card+2*(A∩B).card=A.card+B.card := by
  have hd : Disjoint (A\B) (B\A) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (mem_sdiff.mp hi).2 (mem_sdiff.mp hj).1
  rw [Finset.symmDiff_def,card_union_of_disjoint hd]
  have ha := card_sdiff_add_card_inter A B
  have hb := card_sdiff_add_card_inter B A
  rw [inter_comm B A] at hb
  omega

/-- The complete quadratic form on subsets. Its exponent is precisely the
number of unordered pairs of chosen coordinates. -/
def complete (A : Finset I) : ℝ := triangle A.card

/-- The ordinary Boolean character pairing. -/
def pairing (A B : Finset I) : ℝ := parity (A∩B).card

@[simp] theorem complete_empty : complete (∅ : Finset I)=1 := by simp [complete]
@[simp] theorem complete_square (A : Finset I) : complete A*complete A=1 :=
  triangle_square _
theorem complete_ne_zero (A : Finset I) : complete A≠0 := triangle_ne_zero _
@[simp] theorem pairing_empty_left (A : Finset I) : pairing ∅ A=1 := by simp [pairing]
@[simp] theorem pairing_empty_right (A : Finset I) : pairing A ∅=1 := by simp [pairing]
@[simp] theorem pairing_square (A B : Finset I) : pairing A B*pairing A B=1 :=
  parity_square _
theorem pairing_comm (A B : Finset I) : pairing A B=pairing B A := by
  simp only [pairing,inter_comm]

/-- Polarization of the complete Boolean quadratic form, with every sign
identity proved over the real numbers. -/
theorem complete_symmDiff (A B : Finset I) :
    complete (A∆B)=complete A*complete B*parity (A.card*B.card)*pairing A B := by
  have h := congrArg triangle (card_symmDiff_add_twice_inter A B)
  rw [triangle_add_twice,triangle_add] at h
  calc
    complete (A∆B) =
        (triangle (A∆B).card*parity (A∩B).card)*parity (A∩B).card := by
      rw [mul_assoc,parity_square,mul_one]
      rfl
    _ = (triangle A.card*triangle B.card*parity (A.card*B.card))*
        parity (A∩B).card := by rw [h]
    _ = _ := rfl

/-- The parity of symmetric-difference cardinality is the product of the two
parities; the intersection contributes twice and therefore cancels. -/
theorem parity_card_symmDiff (A B : Finset I) :
    parity (A∆B).card=parity A.card*parity B.card := by
  have h := congrArg parity (card_symmDiff_add_twice_inter A B)
  rw [parity_add,parity_add] at h
  have htwo : parity (2*(A∩B).card)=1 := by
    rw [parity_mul]
    simp
  simpa only [htwo,mul_one] using h

theorem pairing_symmDiff_right (A B C : Finset I) :
    pairing A (B∆C)=pairing A B*pairing A C := by
  have hset : A∩(B∆C)=(A∩B)∆(A∩C) := by
    ext i
    simp only [mem_inter,mem_symmDiff]
    tauto
  change parity (A∩(B∆C)).card=_
  rw [hset,parity_card_symmDiff]
  rfl

theorem pairing_symmDiff_left (A B C : Finset I) :
    pairing (A∆B) C=pairing A C*pairing B C := by
  rw [pairing_comm,pairing_symmDiff_right,pairing_comm C A,pairing_comm C B]

variable [Fintype I]

/-- The bilinear map `I+J` on Boolean subsets. -/
def polar (A : Finset I) : Finset I := if Even A.card then A else Aᶜ

theorem pairing_compl_left (A B : Finset I) :
    pairing Aᶜ B=parity B.card*pairing A B := by
  have hcard : (Aᶜ∩B).card+(A∩B).card=B.card := by
    have hs : Aᶜ∩B=B\A := by ext i; simp [and_comm]
    rw [hs,inter_comm A B]
    exact card_sdiff_add_card_inter B A
  have h := congrArg parity hcard
  rw [parity_add] at h
  calc
    pairing Aᶜ B=(pairing Aᶜ B*pairing A B)*pairing A B := by
      rw [mul_assoc,pairing_square,mul_one]
    _ = parity B.card*pairing A B := by change _ = _; rw [show pairing Aᶜ B * pairing A B = parity B.card from h]

theorem pairing_polar (A B : Finset I) :
    pairing (polar A) B=parity (A.card*B.card)*pairing A B := by
  rw [polar,parity_mul]
  split_ifs with h
  · simp
  · exact pairing_compl_left A B

theorem complete_polarization (A B : Finset I) :
    complete (A∆B)=complete A*complete B*pairing (polar A) B := by
  rw [complete_symmDiff,pairing_polar]
  ring

theorem even_card_compl_iff (hI : Even (Fintype.card I)) (A : Finset I) :
    Even Aᶜ.card ↔ Even A.card := by
  rw [card_compl,Nat.even_iff,Nat.even_iff] 
  have hle := card_le_univ A
  have he := Nat.even_iff.mp hI
  omega

theorem polar_involutive (hI : Even (Fintype.card I)) :
    Function.Involutive (polar (I := I)) := by
  intro A
  by_cases h : Even A.card
  · simp [polar,h]
  · have hc : ¬Even Aᶜ.card := by simpa only [even_card_compl_iff hI A] using h
    simp [polar,h,hc]

theorem polar_eq_empty_iff (hI : Even (Fintype.card I)) (A : Finset I) :
    polar A=∅ ↔ A=∅ := by
  constructor
  · intro h
    have he := congrArg polar h
    rw [polar_involutive hI A] at he
    simpa [polar] using he
  · rintro rfl
    simp [polar]

end QuadraticSign
end GraphicalZonotopes

end
end
end BundlePart236

section BundlePart237
/- Source: Papers/GraphicalZonotopes/PairCounting.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators symmDiff
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The ordinary marginal of the induced-edge count. -/
theorem graphFunction_insert (G : SimpleGraph V) (u : V) (S : Finset V) (hu : u∉S) :
    graphFunction G (insert u S)=graphFunction G S+
      ∑ w∈S,if G.Adj u w then (1 : ℝ) else 0 := by
  revert hu
  induction S using Finset.induction_on with
  | empty =>
    intro hu
    simp only [insert_empty_eq, sum_empty, add_zero, (graphFunction_translationNormalized G).2]
    exact (graphFunction_translationNormalized G).1.symm
  | @insert w S hw ih =>
    intro hu
    have huS : u∉S := fun h => hu (mem_insert_of_mem h)
    have huw : u≠ w := fun h => hu (by simp [h])
    have hd := graphFunction_delta G huw huS hw
    have hm := ih huS
    rw [sum_insert hw]
    unfold delta at hd
    linarith

namespace DoubledParts
variable {I : Type*} [Fintype I] [DecidableEq I]

def firstSet (S : Finset (I×Fin 2)) : Finset I := univ.filter fun i => (i,0)∈S
def secondSet (S : Finset (I×Fin 2)) : Finset I := univ.filter fun i => (i,1)∈S

@[simp] theorem mem_firstSet (S : Finset (I×Fin 2)) (i : I) : i∈firstSet S ↔ (i,0)∈S := by
  simp [firstSet]
@[simp] theorem mem_secondSet (S : Finset (I×Fin 2)) (i : I) : i∈secondSet S ↔ (i,1)∈S := by
  simp [secondSet]

theorem subset_eq_two_images (S : Finset (I×Fin 2)) :
    S=(firstSet S).image (fun i => (i,0)) ∪ (secondSet S).image (fun i => (i,1)) := by
  ext v
  rcases v with ⟨i,b⟩
  fin_cases b <;> simp

theorem card_eq_first_add_second (S : Finset (I×Fin 2)) :
    S.card=(firstSet S).card+(secondSet S).card := by
  have hd : Disjoint ((firstSet S).image (fun i => (i,(0 : Fin 2))))
      ((secondSet S).image (fun i => (i,(1 : Fin 2)))) := by
    apply disjoint_left.mpr
    rintro w hw₀ hw₁
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hw₀
    obtain ⟨j,hj,he⟩ := mem_image.mp hw₁
    have hh := congrArg Prod.snd he
    norm_num at hh
  conv_lhs => rw [subset_eq_two_images S]
  rw [card_union_of_disjoint hd,
    card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h),
    card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)]

/-- Pairs internal to one doubled part. -/
def internalPairFunction : SetFunction (I×Fin 2) :=
  ∑ i : I,setMonomial {(i,0),(i,1)}

theorem internalPairFunction_eq (S : Finset (I×Fin 2)) :
    internalPairFunction S=((firstSet S∩secondSet S).card : ℝ) := by
  simp only [internalPairFunction,Finset.sum_apply,setMonomial,Finset.insert_subset_iff,Finset.singleton_subset_iff]
  rw [← sum_filter]
  simp only [sum_const,nsmul_eq_mul,mul_one]
  congr 1
  apply congrArg Finset.card
  ext i
  simp

def allPairFunction (S : Finset (I×Fin 2)) : ℝ := (S.card.choose 2 : ℝ)

theorem allPairFunction_delta {u v : I×Fin 2} (huv : u≠ v)
    {S : Finset (I×Fin 2)} (hu : u∉S) (hv : v∉S) :
    delta allPairFunction u v S=1 := by
  have huvS : u∉insert v S := by simp [huv,hu]
  simp only [delta,allPairFunction,card_insert_of_notMem hu,card_insert_of_notMem hv,
    card_insert_of_notMem huvS]
  have h1 : (S.card+1).choose 2=S.card.choose 2+S.card := by
    simpa only [Nat.choose_one_right, Nat.add_comm] using Nat.choose_succ_succ' S.card 1
  have h2 : (S.card+1+1).choose 2=(S.card+1).choose 2+(S.card+1) := by
    simpa only [Nat.choose_one_right, Nat.add_comm] using Nat.choose_succ_succ' (S.card+1) 1
  rw [h2,h1]
  push_cast
  ring

theorem internalPairFunction_delta {u v : I×Fin 2} (huv : u≠ v)
    {S : Finset (I×Fin 2)} (hu : u∉S) (hv : v∉S) :
    delta internalPairFunction u v S=if u.1=v.1 then 1 else 0 := by
  rw [internalPairFunction,delta_sum]
  simp_rw [delta_setMonomial huv hu hv]
  by_cases hp : u.1=v.1
  · rw [if_pos hp,sum_eq_single u.1]
    · rcases u with ⟨i,a⟩
      rcases v with ⟨j,b⟩
      dsimp at hp
      subst j
      fin_cases a <;> fin_cases b <;> simp_all [Finset.insert_subset_iff,Finset.singleton_subset_iff]
    · intro i hi hne
      have hn : u∉({(i,0),(i,1)} : Finset (I×Fin 2)) := by
        intro hm
        simp only [mem_insert,mem_singleton] at hm
        rcases hm with he | he <;> exact hne (congrArg Prod.fst he).symm
      simp [hn]
    · simp
  · rw [if_neg hp]
    apply sum_eq_zero
    intro i hi
    have hn : ¬(u∈({(i,0),(i,1)} : Finset (I×Fin 2)) ∧
        v∈({(i,0),(i,1)} : Finset (I×Fin 2))) := by
      rintro ⟨hu',hv'⟩
      simp only [mem_insert,mem_singleton] at hu' hv'
      rcases hu' with hu' | hu' <;> rcases hv' with hv' | hv' <;>
        exact hp ((congrArg Prod.fst hu').trans (congrArg Prod.fst hv').symm)
    simp only [ite_eq_right_iff,one_ne_zero,imp_false,not_and]
    intro hu' hv'
    exact False.elim (hn ⟨hu',hv'⟩)

/-- The exact induced-edge formula in all dimensions. Both sides are
identified by their complete elemental rows and normalization. -/
theorem graphFunction_eq_allPairs_sub_internal :
    graphFunction (graph I)=allPairFunction-internalPairFunction := by
  have hnorm : TranslationNormalized
      (graphFunction (graph I)-(allPairFunction-internalPairFunction)) := by
    constructor
    · change graphFunction (graph I) ∅ - (allPairFunction ∅ - internalPairFunction ∅) = 0
      rw [(graphFunction_translationNormalized (graph I)).1]
      simp [allPairFunction,internalPairFunction,setMonomial]
    · intro v
      have hp : ∀ i : I,¬({(i,0),(i,1)} : Finset (I×Fin 2))⊆{v} := by
        intro i h
        have h0 := h (by simp : (i,0)∈({(i,0),(i,1)} : Finset (I×Fin 2)))
        have h1 := h (by simp : (i,1)∈({(i,0),(i,1)} : Finset (I×Fin 2)))
        simp only [mem_singleton] at h0 h1
        have h01 := congrArg Prod.snd (h0.trans h1.symm)
        norm_num at h01
      simp [allPairFunction,internalPairFunction,setMonomial,hp,
        (graphFunction_translationNormalized _).2]
  apply sub_eq_zero.mp
  apply normalized_zero_elemental_eq_zero hnorm
  intro u v huv S hu hv
  rw [delta_sub,delta_sub,graphFunction_delta _ huv hu hv,
    allPairFunction_delta huv hu hv,internalPairFunction_delta huv hu hv]
  by_cases hp : u.1=v.1 <;> simp [graph,hp]

theorem firstWeight_sum (S : Finset (I×Fin 2)) :
    (∑ v∈S,firstWeight v : ℤ)=((firstSet S).card : ℤ) := by
  rw [show (∑ v∈S,firstWeight v : ℤ)=
      ∑ v∈S.filter (fun v => v.2=0),(1 : ℤ) by simp [firstWeight,sum_filter]]
  simp only [sum_const,nsmul_eq_mul,mul_one]
  congr 1
  apply card_bij (fun v _ => v.1)
  · intro v hv
    rcases mem_filter.mp hv with ⟨hv,hv0⟩
    apply (mem_firstSet S v.1).mpr
    have he : (v.1, (0 : Fin 2)) = v := Prod.ext rfl hv0.symm
    rwa [he]
  · intro v hv w hw h
    apply Prod.ext h
    exact (mem_filter.mp hv).2.trans (mem_filter.mp hw).2.symm
  · intro i hi
    exact ⟨(i,0),by simpa using hi,rfl⟩

theorem integerData_count_identity (S : Finset (I×Fin 2)) :
    integerData S+((firstSet S∩secondSet S).card : ℤ)=
      (S.card.choose 2 : ℤ)+((firstSet S).card : ℤ) := by
  apply Int.cast_injective (α := ℝ)
  push_cast
  rw [cast_integerData,graphFunction_eq_allPairs_sub_internal]
  simp only [modular,subsetSum,← Int.cast_sum]
  change (allPairFunction S-internalPairFunction S)+
    ((∑ v∈S,firstWeight v : ℤ) : ℝ)+((firstSet S∩secondSet S).card : ℝ)=_
  rw [internalPairFunction_eq,firstWeight_sum]
  change (S.card.choose 2 : ℝ)-_+_+_= _
  push_cast
  ring

/-- Exact parity of the defining integer quadratic form: its quadratic part
is the complete form on the symmetric difference of the two selected sets. -/
theorem integerData_phase (S : Finset (I×Fin 2)) :
    (-1 : ℝ)^(integerData S)=
      QuadraticSign.parity (firstSet S).card *
        QuadraticSign.complete (firstSet S ∆ secondSet S) := by
  have hc : S.card=(firstSet S∆secondSet S).card+2*(firstSet S∩secondSet S).card := by
    rw [card_eq_first_add_second]
    exact (QuadraticSign.card_symmDiff_add_twice_inter _ _).symm
  have hi := congrArg (fun n : ℤ => (-1 : ℝ)^n) (integerData_count_identity S)
  rw [zpow_add₀ (by norm_num),zpow_add₀ (by norm_num)] at hi
  simp only [zpow_natCast] at hi
  change (-1 : ℝ)^integerData S*QuadraticSign.parity (firstSet S∩secondSet S).card=
    QuadraticSign.triangle S.card*QuadraticSign.parity (firstSet S).card at hi
  rw [hc,QuadraticSign.triangle_add_twice] at hi
  apply mul_right_cancel₀ (QuadraticSign.parity_ne_zero (firstSet S∩secondSet S).card)
  calc
    (-1 : ℝ)^integerData S*QuadraticSign.parity (firstSet S∩secondSet S).card =
        (QuadraticSign.triangle (firstSet S∆secondSet S).card*
          QuadraticSign.parity (firstSet S∩secondSet S).card)*
          QuadraticSign.parity (firstSet S).card := hi
    _ = _ := by unfold QuadraticSign.complete; ring

end DoubledParts
end GraphicalZonotopes

end
end
end BundlePart237

section BundlePart238
/- Source: Papers/GraphicalZonotopes/BooleanFourier.lean -/











@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace BooleanFourier
open Finset
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev Cube (I : Type*) := I → Bool

def spin (b : Bool) : ℝ := if b then -1 else 1

theorem spin_isSign (b : Bool) : spin b = 1 ∨ spin b = -1 := by
  cases b <;> simp [spin]

@[simp] theorem spin_mul_self (b : Bool) : spin b*spin b=1 := by
  cases b <;> norm_num [spin]

theorem spin_ne_zero (b : Bool) : spin b ≠ 0 := by
  cases b <;> norm_num [spin]

def character (A : Finset I) (u : Cube I) : ℝ :=
  ∏ i, if i∈A then spin (u i) else 1

@[simp] theorem character_empty (u : Cube I) : character ∅ u=1 := by
  simp [character]

@[simp] theorem character_univ (u : Cube I) :
    character univ u=∏ i,spin (u i) := by
  simp [character]

theorem character_ne_zero (A : Finset I) (u : Cube I) : character A u≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  split_ifs <;> simp [spin_ne_zero]

@[simp] theorem character_square (A : Finset I) (u : Cube I) :
    character A u*character A u=1 := by
  simp only [character,← prod_mul_distrib]
  have h : ∀ i : I,(if i∈A then spin (u i) else 1)*
      (if i∈A then spin (u i) else 1)=1 := by
    intro i
    split_ifs <;> simp
  simp only [h,prod_const_one]

theorem character_compl (A : Finset I) (u : Cube I) :
    character univ u*character A u=character Aᶜ u := by
  simp only [character,mem_univ,ite_true,← prod_mul_distrib]
  apply prod_congr rfl
  intro i hi
  by_cases h : i∈A <;> simp [h]

theorem character_orthogonality (A B : Finset I) :
    (∑ u : Cube I,character A u*character B u)=
      if A=B then (2 : ℝ)^Fintype.card I else 0 := by
  simp only [character,← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : I) (b : Bool) =>
    (if i∈A then spin b else 1)*(if i∈B then spin b else 1))]
  have hlocal : ∀ i : I,
      (∑ b : Bool,(if i∈A then spin b else 1)*(if i∈B then spin b else 1))=
      if (i∈A ↔ i∈B) then (2 : ℝ) else 0 := by
    intro i
    by_cases ha : i∈A <;> by_cases hb : i∈B <;> norm_num [ha,hb,spin]
  simp_rw [hlocal]
  by_cases h : A=B
  · subst B
    simp
  · rw [if_neg h]
    obtain ⟨i,hi⟩ : ∃ i : I,¬(i∈A ↔ i∈B) := by
      by_contra! hh
      exact h (Finset.ext hh)
    exact prod_eq_zero (mem_univ i) (if_neg hi)

theorem coefficient_extraction (c : Finset I → ℝ) (B : Finset I) :
    (∑ u : Cube I,character B u*(∑ A : Finset I,c A*character A u))=
      (2 : ℝ)^Fintype.card I*c B := by
  simp_rw [mul_sum]
  rw [sum_comm]
  have hterm : ∀ A : Finset I,
      (∑ u : Cube I,character B u*(c A*character A u))=
      c A*(∑ u : Cube I,character B u*character A u) := by
    intro A
    rw [mul_sum]
    apply sum_congr rfl
    intro u hu
    ring
  simp_rw [hterm,character_orthogonality]
  simp [mul_comm]

theorem character_linearIndependent : LinearIndependent ℝ (character (I := I)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc B
  have hz : ∀ u : Cube I,(∑ A : Finset I,c A*character A u)=0 := by
    intro u
    have h := congrFun hc u
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] using h
  have h := coefficient_extraction c B
  simp only [hz,mul_zero,sum_const_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ (by norm_num))

theorem character_span : Submodule.span ℝ (Set.range (character (I := I)))=⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_span_eq_card character_linearIndependent,Module.finrank_pi,
    Fintype.card_finset,Fintype.card_fun]
  simp

theorem exists_character_expansion (f : Cube I → ℝ) :
    ∃ c : Finset I → ℝ,∀ u,f u=∑ A : Finset I,c A*character A u := by
  have h : f∈Submodule.span ℝ (Set.range (character (I := I))) := by
    rw [character_span]
    trivial
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp h
  refine ⟨c,fun u => ?_⟩
  have hcu := congrFun hc u
  simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using hcu.symm

/-- A function depends on the indicated coordinates, with no representation
or regularity assumption on the remaining coordinates. -/
def DependsOn (A : Finset I) (f : Cube I → ℝ) : Prop :=
  ∀ u v : Cube I,(∀ i∈A,u i=v i) → f u=f v

theorem dependsOn_const (A : Finset I) (c : ℝ) : DependsOn A (fun _ => c) :=
  fun _ _ _ => rfl

theorem dependsOn_univ (f : Cube I → ℝ) : DependsOn univ f := by
  intro u v h
  congr 1
  exact funext fun i => h i (mem_univ i)

theorem dependsOn_character (A : Finset I) : DependsOn A (character A) := by
  intro u v h
  apply prod_congr rfl
  intro i hi
  by_cases hia : i∈A
  · simp [hia,h i hia]
  · simp [hia]

theorem DependsOn.add {A : Finset I} {f g : Cube I → ℝ}
    (hf : DependsOn A f) (hg : DependsOn A g) : DependsOn A (f+g) := by
  intro u v h
  change f u+g u=f v+g v
  rw [hf u v h,hg u v h]

theorem DependsOn.smul {A : Finset I} {f : Cube I → ℝ}
    (hf : DependsOn A f) (c : ℝ) : DependsOn A (c • f) := by
  intro u v h
  change c*f u=c*f v
  rw [hf u v h]

theorem DependsOn.mono {A B : Finset I} {f : Cube I → ℝ}
    (hf : DependsOn A f) (hAB : A⊆B) : DependsOn B f :=
  fun u v h => hf u v fun i hi => h i (hAB hi)

theorem dependsOn_empty_iff (f : Cube I → ℝ) :
    DependsOn ∅ f ↔ ∃ c : ℝ,∀ u,f u=c := by
  constructor
  · intro h
    exact ⟨f (fun _ => false),fun u => h u (fun _ => false) (by simp)⟩
  · rintro ⟨c,hc⟩ u v huv
    rw [hc u,hc v]

def mix (A : Finset I) (u v : Cube I) : Cube I :=
  fun i => if i∈A then u i else v i

theorem DependsOn.mix_left {A : Finset I} {f : Cube I → ℝ}
    (hf : DependsOn A f) (u v : Cube I) : f (mix A u v)=f u := by
  apply hf
  intro i hi
  simp [mix,hi]

theorem DependsOn.mix_right {A : Finset I} {f : Cube I → ℝ}
    (hf : DependsOn Aᶜ f) (u v : Cube I) : f (mix A u v)=f v := by
  apply hf
  intro i hi
  simp only [mem_compl] at hi
  simp [mix,hi]

end BooleanFourier
end GraphicalZonotopes

end
end
end BundlePart238

section BundlePart239
/- Source: Papers/GraphicalZonotopes/BooleanFace.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace BooleanFourier
open Finset
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The three choices in each factor are exactly `1`, `uᵢ`, and `uᵢvᵢ`. -/
def tensorMonomial (a : I → Option Bool) (uv : Cube I × Cube I) : ℝ :=
  ∏ i, match a i with
    | none => 1
    | some false => spin (uv.1 i)
    | some true => spin (uv.1 i)*spin (uv.2 i)

/-- The actual tensor product of the three-dimensional one-part spaces,
realized as a subspace of functions on all independent signs. -/
def tensorSpace : Submodule ℝ ((Cube I × Cube I) → ℝ) :=
  Submodule.span ℝ (Set.range (tensorMonomial (I := I)))

def active (a : I → Option Bool) : Finset I := univ.filter (fun i => (a i).isSome)
def second (a : I → Option Bool) : Finset I := univ.filter (fun i => a i=some true)

theorem second_subset_active (a : I → Option Bool) : second a⊆active a := by
  intro i hi
  simp only [second,mem_filter,mem_univ,true_and] at hi
  simp [active,hi]

theorem tensorMonomial_eq (a : I → Option Bool) (uv : Cube I × Cube I) :
    tensorMonomial a uv=character (active a) uv.1*character (second a) uv.2 := by
  simp only [tensorMonomial,character,← prod_mul_distrib]
  apply prod_congr rfl
  intro i hi
  cases h : a i with
  | none => simp [active,second,h]
  | some b => cases b <;> simp [active,second,h]

def coordinateChange : (Cube I × Cube I) ≃ (Cube I × Cube I) where
  toFun uv := (uv.1,fun i => Bool.xor (uv.1 i) (uv.2 i))
  invFun uv := (uv.1,fun i => Bool.xor (uv.1 i) (uv.2 i))
  left_inv uv := by
    apply Prod.ext
    · rfl
    · funext i
      change Bool.xor (uv.1 i) (Bool.xor (uv.1 i) (uv.2 i)) = uv.2 i
      cases uv.1 i <;> cases uv.2 i <;> rfl
  right_inv uv := by
    apply Prod.ext
    · rfl
    · funext i
      change Bool.xor (uv.1 i) (Bool.xor (uv.1 i) (uv.2 i)) = uv.2 i
      cases uv.1 i <;> cases uv.2 i <;> rfl

theorem spin_xor (a b : Bool) : spin (Bool.xor a b)=spin a*spin b := by
  cases a <;> cases b <;> norm_num [spin]

/-- This identifies the transformed tensor generators with the paper's
original factors `1,sᵢ₀,sᵢ₁`; the independent-coordinate change is an equivalence. -/
theorem tensorMonomial_coordinateChange (a : I → Option Bool) (s : Cube I × Cube I) :
    tensorMonomial a (coordinateChange s)=
      ∏ i,match a i with
        | none => 1
        | some false => spin (s.1 i)
        | some true => spin (s.2 i) := by
  apply prod_congr rfl
  intro i hi
  cases h : a i with
  | none => rfl
  | some b =>
    cases b
    · rfl
    · change spin (s.1 i)*spin (Bool.xor (s.1 i) (s.2 i))=spin (s.2 i)
      rw [spin_xor,← mul_assoc,spin_mul_self,one_mul]

def HasRestrictedExpansion (p : (Cube I × Cube I) → ℝ) : Prop :=
  ∃ P : Finset I → Cube I → ℝ,(∀ A,DependsOn A (P A)) ∧
    ∀ u v,p (u,v)=∑ A : Finset I,character A u*P A v

theorem tensorMonomial_expansion (a : I → Option Bool) :
    HasRestrictedExpansion (tensorMonomial a) := by
  refine ⟨fun A v => if A=active a then character (second a) v else 0,?_,?_⟩
  · intro A
    by_cases h : A=active a
    · subst A
      simpa using (dependsOn_character (second a)).mono (second_subset_active a)
    · simpa [h] using dependsOn_const A (0 : ℝ)
  · intro u v
    simp [tensorMonomial_eq]

theorem restrictedExpansion_of_mem_tensorSpace {p : (Cube I × Cube I) → ℝ}
    (hp : p∈tensorSpace) : HasRestrictedExpansion p := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨a,rfl⟩ := hp
    exact tensorMonomial_expansion a
  | zero =>
    refine ⟨fun _ _ => 0,fun A => dependsOn_const A 0,?_⟩
    simp
  | add p q hp hq ihp ihq =>
    obtain ⟨P,hP,hp⟩ := ihp
    obtain ⟨Q,hQ,hq⟩ := ihq
    refine ⟨fun A => P A+Q A,fun A => (hP A).add (hQ A),?_⟩
    intro u v
    simp only [Pi.add_apply,hp,hq,mul_add,sum_add_distrib]
  | smul c p hp ih =>
    obtain ⟨P,hP,hp⟩ := ih
    refine ⟨fun A => c • P A,fun A => (hP A).smul c,?_⟩
    intro u v
    simp only [Pi.smul_apply,smul_eq_mul,hp,mul_sum]
    apply sum_congr rfl
    intro A hA
    ring

theorem constant_mem_tensorSpace (c : ℝ) : (fun _ : Cube I × Cube I => c)∈tensorSpace := by
  have h : tensorMonomial (fun _ : I => none)∈tensorSpace :=
    Submodule.subset_span ⟨_,rfl⟩
  convert (tensorSpace (I := I)).smul_mem c h using 1
  funext uv
  simp [tensorMonomial]

theorem full_character_product_mem (B : Finset I) :
    (fun uv : Cube I × Cube I => character univ uv.1*character B uv.2)∈tensorSpace := by
  let a : I → Option Bool := fun i => if i∈B then some true else some false
  have h := (Submodule.subset_span (R := ℝ)
    (s := Set.range (tensorMonomial (I := I))) (⟨a,rfl⟩ : tensorMonomial a∈Set.range tensorMonomial))
  have ha : active a=univ := by
    ext i
    by_cases hi : i ∈ B <;> simp [active,a,hi]
  have hb : second a=B := by ext i; simp [second,a]
  have he : tensorMonomial a = (fun uv : Cube I × Cube I => character univ uv.1*character B uv.2) := by
    funext uv
    rw [tensorMonomial_eq,ha,hb]
  rw [he] at h
  exact h

def phase (G : Cube I → ℝ) (uv : Cube I × Cube I) : ℝ := character univ uv.1*G uv.2
def faceFunction (G : Cube I → ℝ) (uv : Cube I × Cube I) : ℝ := (1+phase G uv)/2

theorem phase_mem_tensorSpace (G : Cube I → ℝ) : phase G∈tensorSpace := by
  obtain ⟨c,hc⟩ := exists_character_expansion G
  have h : (∑ B : Finset I,c B •
      (fun uv : Cube I × Cube I => character univ uv.1*character B uv.2))∈tensorSpace :=
    (tensorSpace (I := I)).sum_mem fun B _ =>
      (tensorSpace (I := I)).smul_mem (c B) (full_character_product_mem B)
  convert h using 1
  funext uv
  simp only [phase,hc,mul_sum,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply sum_congr rfl
  intro B hB
  ring

theorem faceFunction_mem_tensorSpace (G : Cube I → ℝ) : faceFunction G∈tensorSpace := by
  have h := (tensorSpace (I := I)).smul_mem (1/2 : ℝ)
    ((tensorSpace (I := I)).add_mem (constant_mem_tensorSpace 1) (phase_mem_tensorSpace G))
  convert h using 1
  funext uv
  simp only [faceFunction,Pi.smul_apply,smul_eq_mul,Pi.add_apply]
  ring

/-- Nonfactorization across every nonempty proper partition. The factors are
arbitrary real functions of their respective variables. For a sign-valued
function, any factorization can equivalently be rescaled to sign factors. -/
def Nonseparable (G : Cube I → ℝ) : Prop :=
  ∀ A : Finset I,A.Nonempty → A≠ univ →
    ¬∃ H K : Cube I → ℝ,DependsOn A H ∧ DependsOn Aᶜ K ∧ ∀ v,G v=H v*K v

theorem factor_of_complementary_equation {G P Q : Cube I → ℝ} {A : Finset I}
    (hG : ∀ v,G v=1 ∨ G v=-1)
    (hP : DependsOn A P) (hQ : DependsOn Aᶜ Q)
    (heq : ∀ v,P v=G v*Q v) (v₀ : Cube I) (hc : P v₀≠0) :
    ∃ H K : Cube I → ℝ,DependsOn A H ∧ DependsOn Aᶜ K ∧ ∀ v,G v=H v*K v := by
  let c := P v₀
  let K : Cube I → ℝ := fun v => G (mix A v₀ v)
  let H : Cube I → ℝ := fun v => P v/c
  have hGsquare : ∀ v,G v*G v=1 := by
    intro v
    rcases hG v with h | h <;> rw [h] <;> norm_num
  have hKsquare : ∀ v,K v*K v=1 := fun v => hGsquare (mix A v₀ v)
  have hQc : ∀ v,Q v=K v*c := by
    intro v
    have h := heq (mix A v₀ v)
    rw [hP.mix_left,hQ.mix_right] at h
    have hh := congrArg (fun x : ℝ => K v*x) h
    change K v*c=K v*(K v*Q v) at hh
    rw [← mul_assoc,hKsquare,one_mul] at hh
    exact hh.symm
  refine ⟨H,K,?_,?_,?_⟩
  · intro u v huv
    change P u/c=P v/c
    rw [hP u v huv]
  · intro u v huv
    apply congrArg G
    funext i
    by_cases hi : i∈A
    · simp [mix,hi]
    · simp [mix,hi,huv i (by simpa using hi)]
  · intro v
    change G v=(P v/c)*K v
    rw [heq v,hQc v]
    have hc' : c≠0 := hc
    calc
      G v=G v*(K v*K v) := by rw [hKsquare,mul_one]
      _=(G v*(K v*c)/c)*K v := by field_simp [hc']

theorem restricted_components_equation {p : (Cube I × Cube I) → ℝ}
    {G : Cube I → ℝ} {P : Finset I → Cube I → ℝ}
    (hp : ∀ u v,p (u,v)=∑ A : Finset I,character A u*P A v)
    (hgp : ∀ u v,phase G (u,v)*p (u,v)=p (u,v)) :
    ∀ A v,P A v=G v*P Aᶜ v := by
  intro A v
  have hcoeff : ∀ B : Finset I,
      (∑ u : Cube I,character B u*p (u,v))=(2 : ℝ)^Fintype.card I*P B v := by
    intro B
    have hs : ∀ u,p (u,v)=∑ C : Finset I,P C v*character C u := by
      intro u
      rw [hp]
      apply sum_congr rfl
      intro C hC
      ring
    simp_rw [hs]
    exact coefficient_extraction (fun C => P C v) B
  have h := congrArg (fun f : Cube I → ℝ => ∑ u,character A u*f u)
    (funext fun u => hgp u v)
  have hleft : (∑ u : Cube I,character A u*(phase G (u,v)*p (u,v)))=
      G v*(∑ u : Cube I,character Aᶜ u*p (u,v)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro u hu
    rw [← character_compl]
    unfold phase
    ring
  change (∑ u : Cube I,character A u*(phase G (u,v)*p (u,v)))=
    ∑ u : Cube I,character A u*p (u,v) at h
  rw [hleft,hcoeff,hcoeff] at h
  have hn : (2 : ℝ)^Fintype.card I≠0 := pow_ne_zero _ (by norm_num)
  apply (mul_left_cancel₀ hn)
  calc
    (2 : ℝ)^Fintype.card I*P A v=G v*((2 : ℝ)^Fintype.card I*P Aᶜ v) := h.symm
    _=(2 : ℝ)^Fintype.card I*(G v*P Aᶜ v) := by ring

theorem phase_square {G : Cube I → ℝ} (hG : ∀ v,G v=1 ∨ G v=-1)
    (uv : Cube I × Cube I) : phase G uv*phase G uv=1 := by
  have hGv : G uv.2*G uv.2=1 := by
    rcases hG uv.2 with h | h <;> rw [h] <;> norm_num
  have hu := character_square (univ : Finset I) uv.1
  calc
    phase G uv*phase G uv=(character univ uv.1*character univ uv.1)*(G uv.2*G uv.2) := by
      unfold phase
      ring
    _=1 := by rw [hu,hGv]; norm_num

theorem vanishes_iff_phase_fixed {G : Cube I → ℝ}
    (hG : ∀ v,G v=1 ∨ G v=-1) (p : (Cube I × Cube I) → ℝ) :
    (∀ uv,faceFunction G uv=0 → p uv=0) ↔
      ∀ u v,phase G (u,v)*p (u,v)=p (u,v) := by
  constructor
  · intro hp u v
    have hs := phase_square hG (u,v)
    have hsign : phase G (u,v)=1 ∨ phase G (u,v)=-1 := by
      have h : (phase G (u,v)-1)*(phase G (u,v)+1)=0 := by nlinarith
      rcases mul_eq_zero.mp h with h | h
      · left; linarith
      · right; linarith
    rcases hsign with h | h
    · simp [h]
    · have hz := hp (u,v) (by simp [faceFunction,h])
      simp [hz]
  · intro hp uv hf
    have h := hp uv.1 uv.2
    have hg : phase G uv=-1 := by unfold faceFunction at hf; linarith
    rw [hg] at h
    linarith

/-- Lemma9.9: the complete vanishing subspace is the one-dimensional line
through the Boolean function, for every nonempty finite index set. -/
theorem boolean_face_line [Nonempty I] {G : Cube I → ℝ}
    (hG : ∀ v,G v=1 ∨ G v=-1) (hsep : Nonseparable G)
    (p : (Cube I × Cube I) → ℝ) (hp : p∈tensorSpace) :
    (∀ uv,faceFunction G uv=0 → p uv=0) ↔
      ∃ c : ℝ,p=c • faceFunction G := by
  constructor
  · intro hzero
    obtain ⟨P,hP,hp⟩ := restrictedExpansion_of_mem_tensorSpace hp
    have hgp := (vanishes_iff_phase_fixed hG p).mp hzero
    have hcomponents := restricted_components_equation hp hgp
    have hproper : ∀ A : Finset I,A≠∅ → A≠ univ → ∀ v,P A v=0 := by
      intro A hA htop v
      by_contra hv
      exact hsep A (nonempty_iff_ne_empty.mpr hA) htop
        (factor_of_complementary_equation hG (hP A) (hP Aᶜ)
          (hcomponents A) v hv)
    obtain ⟨c,hc⟩ := (dependsOn_empty_iff (P ∅)).mp (hP ∅)
    have hfull : ∀ v,P univ v=G v*c := by
      intro v
      simpa only [compl_univ,hc] using hcomponents univ v
    have hne : (∅ : Finset I)≠ univ := by
      exact ne_of_lt (empty_ssubset.mpr univ_nonempty)
    refine ⟨2*c,?_⟩
    funext uv
    rw [hp]
    have hs : (∑ A : Finset I,character A uv.1*P A uv.2)=
        character ∅ uv.1*P ∅ uv.2+character univ uv.1*P univ uv.2 := by
      have hh := sum_subset (f := fun A : Finset I => character A uv.1 * P A uv.2) (subset_univ ({∅,univ} : Finset (Finset I)))
        (fun A hAu hnot => by
          have hA : A≠∅ := by intro h; apply hnot; simp [h]
          have htop : A≠ univ := by intro h; apply hnot; simp [h]
          rw [hproper A hA htop,mul_zero])
      simpa only [sum_pair hne] using hh.symm
    rw [hs,character_empty,one_mul,hc,hfull]
    simp only [Pi.smul_apply,smul_eq_mul,faceFunction,phase]
    ring
  · rintro ⟨c,rfl⟩ uv huv
    simp [huv]

theorem faceFunction_boolean {G : Cube I → ℝ}
    (hG : ∀ v,G v=1 ∨ G v=-1) (uv : Cube I × Cube I) :
    faceFunction G uv=0 ∨ faceFunction G uv=1 := by
  have hs := phase_square hG uv
  have hp : faceFunction G uv*(faceFunction G uv-1)=0 := by
    unfold faceFunction
    nlinarith [hs]
  rcases mul_eq_zero.mp hp with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

theorem faceFunction_ne_zero [Nonempty I] {G : Cube I → ℝ}
    (hG : ∀ v,G v=1 ∨ G v=-1) : faceFunction G≠0 := by
  let v₀ : Cube I := fun _ => false
  obtain ⟨i⟩ := ‹Nonempty I›
  have hvalue : ∃ u : Cube I,faceFunction G (u,v₀)=1 := by
    rcases hG v₀ with h | h
    · refine ⟨fun _ => false,?_⟩
      simp [faceFunction,phase,character,spin,h]
    · let u : Cube I := fun j => if j=i then true else false
      have hu : character univ u=-1 := by
        rw [character_univ,prod_eq_single i]
        · simp [u,spin]
        · intro j hj hji
          simp [u,hji,spin]
        · simp
      exact ⟨u,by simp [faceFunction,phase,hu,h]⟩
  obtain ⟨u,hu⟩ := hvalue
  intro hz
  rw [hz] at hu
  norm_num at hu

/-- All tensor polynomials vanishing on the literal zero set of `f`. -/
def faceKernel (G : Cube I → ℝ) : Submodule ℝ ((Cube I × Cube I) → ℝ) where
  carrier := {p | p∈tensorSpace ∧ ∀ uv,faceFunction G uv=0 → p uv=0}
  zero_mem' := ⟨(tensorSpace (I := I)).zero_mem,by simp⟩
  add_mem' hp hq := ⟨(tensorSpace (I := I)).add_mem hp.1 hq.1,by
    intro uv huv
    simp [hp.2 uv huv,hq.2 uv huv]⟩
  smul_mem' c p hp := ⟨(tensorSpace (I := I)).smul_mem c hp.1,by
    intro uv huv
    simp [hp.2 uv huv]⟩

theorem faceKernel_eq_span [Nonempty I] {G : Cube I → ℝ}
    (hG : ∀ v,G v=1 ∨ G v=-1) (hsep : Nonseparable G) :
    faceKernel G=Submodule.span ℝ {faceFunction G} := by
  ext p
  constructor
  · intro hp
    obtain ⟨c,hc⟩ := (boolean_face_line hG hsep p hp.1).mp hp.2
    exact Submodule.mem_span_singleton.mpr ⟨c,hc.symm⟩
  · intro hp
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hp
    exact ⟨(tensorSpace (I := I)).smul_mem c (faceFunction_mem_tensorSpace G),
      fun uv huv => by simp [huv]⟩

theorem faceKernel_finrank [Nonempty I] {G : Cube I → ℝ}
    (hG : ∀ v,G v=1 ∨ G v=-1) (hsep : Nonseparable G) :
    Module.finrank ℝ (faceKernel G)=1 := by
  rw [faceKernel_eq_span hG hsep]
  exact finrank_span_singleton (faceFunction_ne_zero hG)

theorem Nonseparable.neg {G : Cube I → ℝ} (hG : Nonseparable G) :
    Nonseparable (-G) := by
  intro A hA htop hfactor
  obtain ⟨H,K,hH,hK,h⟩ := hfactor
  apply hG A hA htop
  refine ⟨(-1 : ℝ) • H,K,hH.smul (-1),hK,?_⟩
  intro v
  have hv := h v
  change -G v=H v*K v at hv
  change G v=((-1 : ℝ)*H v)*K v
  linarith

/-- The nonfactorization convention is unchanged if the candidate factors
are required to be sign-valued: every real factorization of a sign function
has such a normalization. -/
theorem normalize_sign_factorization {G H K : Cube I → ℝ} {A : Finset I}
    (hG : ∀ v,G v=1 ∨ G v=-1)
    (hH : DependsOn A H) (hK : DependsOn Aᶜ K)
    (hfactor : ∀ v,G v=H v*K v) :
    ∃ H' K' : Cube I → ℝ,DependsOn A H' ∧ DependsOn Aᶜ K' ∧
      (∀ v,H' v=1 ∨ H' v=-1) ∧ (∀ v,K' v=1 ∨ K' v=-1) ∧
      ∀ v,G v=H' v*K' v := by
  let v₀ : Cube I := fun _ => false
  let H' : Cube I → ℝ := fun v => G (mix A v v₀)*G v₀
  let K' : Cube I → ℝ := fun v => G (mix A v₀ v)
  have hH' : DependsOn A H' := by
    intro u v huv
    change G (mix A u v₀)*G v₀=G (mix A v v₀)*G v₀
    congr 2
    funext i
    by_cases hi : i∈A
    · simp [mix,hi,huv i hi]
    · simp [mix,hi]
  have hK' : DependsOn Aᶜ K' := by
    intro u v huv
    apply congrArg G
    funext i
    by_cases hi : i∈A
    · simp [mix,hi]
    · simp [mix,hi,huv i (by simpa using hi)]
  refine ⟨H',K',hH',hK',?_,fun v => hG (mix A v₀ v),?_⟩
  · intro v
    rcases hG (mix A v v₀) with ha | ha <;>
      rcases hG v₀ with hb | hb <;> simp [H',ha,hb]
  · intro v
    have h₀ : G v₀*G v₀=1 := by
      rcases hG v₀ with h | h <;> rw [h] <;> norm_num
    change G v=(G (mix A v v₀)*G v₀)*G (mix A v₀ v)
    rw [hfactor (mix A v v₀),hfactor (mix A v₀ v),
      hH.mix_left,hH.mix_left,hK.mix_right,hK.mix_right]
    calc
      G v=G v*(G v₀*G v₀) := by rw [h₀,mul_one]
      _=(H v*K v₀*G v₀)*(H v₀*K v) := by rw [hfactor v,hfactor v₀]; ring

end BooleanFourier
end GraphicalZonotopes

end
end
end BundlePart239

section BundlePart240
/- Source: Papers/GraphicalZonotopes/TensorIndicators.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace BooleanFourier
open Finset
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The local factors of the actual three-dimensional space in transformed
coordinates. -/
def tensorFactor (b : Option Bool) (u v : Bool) : ℝ :=
  match b with
  | none => 1
  | some false => spin u
  | some true => spin u*spin v

/-- Products of arbitrary local linear combinations lie in the actual tensor
space. The proof is the finite distributive law over all choices of factors. -/
theorem tensor_product_mem (w : I → Option Bool → ℝ) :
    (fun uv : Cube I × Cube I =>
      ∏ i,∑ b : Option Bool,w i b*tensorFactor b (uv.1 i) (uv.2 i))∈tensorSpace := by
  have h : (∑ a : I → Option Bool,(∏ i,w i (a i)) • tensorMonomial a)∈tensorSpace :=
    (tensorSpace (I := I)).sum_mem fun a _ =>
      (tensorSpace (I := I)).smul_mem _ (Submodule.subset_span ⟨a,rfl⟩)
  convert h using 1
  funext uv
  rw [Fintype.prod_sum]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,tensorMonomial]
  apply sum_congr rfl
  intro a ha
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro i hi
  cases a i <;> rfl

/-- A selected original membership bit in each part, with no bit selected for
`none`. A clique of a graph with doubled parts has exactly this form. -/
def indicatorMonomial (a : I → Option Bool) (s : Cube I × Cube I) : ℝ :=
  ∏ i,match a i with
    | none => 1
    | some false => if s.1 i then 1 else 0
    | some true => if s.2 i then 1 else 0

def indicatorCoefficients (a : Option Bool) (b : Option Bool) : ℝ :=
  match a with
  | none => if b=none then 1 else 0
  | some q => if b=none then 1/2 else if b=some q then -1/2 else 0

theorem indicator_local_expansion (a : Option Bool) (u v : Bool) :
    (∑ b : Option Bool,indicatorCoefficients a b*tensorFactor b u v)=
      match a with
      | none => 1
      | some false => if u then 1 else 0
      | some true => if Bool.xor u v then 1 else 0 := by
  cases a with
  | none => simp [indicatorCoefficients,tensorFactor]
  | some q =>
    cases q <;> cases u <;> cases v <;>
      norm_num [indicatorCoefficients,tensorFactor,spin,Fintype.sum_option,Fintype.sum_bool]

/-- Actual membership monomials become tensor-space elements under the
invertible coordinate substitution `(u,v) ↦ (u,u xor v)`. -/
theorem indicatorMonomial_mem_tensorSpace (a : I → Option Bool) :
    (fun uv => indicatorMonomial a (coordinateChange.symm uv))∈tensorSpace := by
  have h := tensor_product_mem (fun i => indicatorCoefficients (a i))
  convert h using 1
  funext uv
  simp only [indicatorMonomial]
  apply prod_congr rfl
  intro i hi
  rw [indicator_local_expansion]
  cases a i with
  | none => rfl
  | some q => cases q <;> rfl

theorem indicatorMonomial_eq (a : I → Option Bool) (s : Cube I × Cube I) :
    indicatorMonomial a s=
      if (∀ i, a i=some false → s.1 i=true) ∧
        (∀ i,a i=some true → s.2 i=true) then 1 else 0 := by
  classical
  by_cases hall : (∀ i,a i=some false → s.1 i=true) ∧
      (∀ i,a i=some true → s.2 i=true)
  · rw [if_pos hall]
    apply prod_eq_one
    intro i hi
    cases h : a i with
    | none => rfl
    | some q =>
      cases q
      · simp [h,hall.1 i h]
      · simp [h,hall.2 i h]
  · rw [if_neg hall]
    have hn : (∃ i,a i=some false ∧ s.1 i≠ true) ∨
        (∃ i,a i=some true ∧ s.2 i≠ true) := by
      simpa only [not_and_or,not_forall,not_imp,exists_prop] using hall
    rcases hn with ⟨i,ha,hs⟩ | ⟨i,ha,hs⟩
    · apply Finset.prod_eq_zero (mem_univ i)
      simp [ha,hs]
    · apply Finset.prod_eq_zero (mem_univ i)
      simp [ha,hs]

end BooleanFourier
end GraphicalZonotopes

end
end
end BundlePart240

section BundlePart241
/- Source: Papers/GraphicalZonotopes/PairTensor.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset BooleanFourier
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The usual Boolean coordinates of an arbitrary subset of paired vertices. -/
def subsetOfBits (s : Cube I × Cube I) : Finset (I×Fin 2) :=
  univ.filter fun v => if v.2=0 then s.1 v.1=true else s.2 v.1=true

@[simp] theorem mem_subsetOfBits_zero (s : Cube I × Cube I) (i : I) :
    (i,0)∈subsetOfBits s ↔ s.1 i=true := by simp [subsetOfBits]

@[simp] theorem mem_subsetOfBits_one (s : Cube I × Cube I) (i : I) :
    (i,1)∈subsetOfBits s ↔ s.2 i=true := by simp [subsetOfBits]

def bitsOfSubset (S : Finset (I×Fin 2)) : Cube I × Cube I :=
  (fun i => decide ((i,0)∈S),fun i => decide ((i,1)∈S))

@[simp] theorem subsetOfBits_bitsOfSubset (S : Finset (I×Fin 2)) :
    subsetOfBits (bitsOfSubset S)=S := by
  ext v
  rcases v with ⟨i,b⟩
  fin_cases b <;> simp [bitsOfSubset]

@[simp] theorem bitsOfSubset_subsetOfBits (s : Cube I × Cube I) :
    bitsOfSubset (subsetOfBits s)=s := by
  apply Prod.ext
  · funext i
    simp [bitsOfSubset]
  · funext i
    simp [bitsOfSubset]

def selector (C : Finset (I×Fin 2)) (i : I) : Option Bool :=
  if (i,0)∈C then some false else if (i,1)∈C then some true else none

def IsPartialTransversal (C : Finset (I×Fin 2)) : Prop :=
  ∀ i,¬((i,0)∈C ∧ (i,1)∈C)

theorem clique_partialTransversal {C : Finset (I×Fin 2)}
    (hC : (graph I).IsClique C) : IsPartialTransversal C := by
  intro i hi
  exact hC hi.1 hi.2 (by simp) rfl

theorem selector_zero_iff (C : Finset (I×Fin 2)) (i : I) :
    selector C i=some false ↔ (i,0)∈C := by
  by_cases h0 : (i,0)∈C <;> by_cases h1 : (i,1)∈C <;> simp [selector,h0,h1]

theorem selector_one_iff {C : Finset (I×Fin 2)} (hC : IsPartialTransversal C) (i : I) :
    selector C i=some true ↔ (i,1)∈C := by
  by_cases h0 : (i,0)∈C
  · have h1 : (i,1)∉C := fun h => hC i ⟨h0,h⟩
    simp [selector,h0,h1]
  · simp [selector,h0]

theorem subset_subsetOfBits_iff (C : Finset (I×Fin 2)) (s : Cube I × Cube I) :
    C⊆subsetOfBits s ↔
      (∀ i,(i,0)∈C → s.1 i=true) ∧ (∀ i,(i,1)∈C → s.2 i=true) := by
  constructor
  · intro h
    exact ⟨fun i hi => (mem_subsetOfBits_zero s i).mp (h hi),
      fun i hi => (mem_subsetOfBits_one s i).mp (h hi)⟩
  · rintro ⟨h0,h1⟩ ⟨i,b⟩ hi
    fin_cases b
    · exact (mem_subsetOfBits_zero s i).mpr (h0 i hi)
    · exact (mem_subsetOfBits_one s i).mpr (h1 i hi)

theorem setMonomial_subsetOfBits {C : Finset (I×Fin 2)}
    (hC : IsPartialTransversal C) (s : Cube I × Cube I) :
    setMonomial C (subsetOfBits s)=indicatorMonomial (selector C) s := by
  rw [indicatorMonomial_eq]
  simp only [setMonomial,selector_zero_iff,selector_one_iff hC,subset_subsetOfBits_iff]

theorem setMonomial_mem_tensorSpace {C : Finset (I×Fin 2)}
    (hC : IsPartialTransversal C) :
    (fun uv => setMonomial C (subsetOfBits (coordinateChange.symm uv)))∈tensorSpace := by
  simpa only [setMonomial_subsetOfBits hC] using
    indicatorMonomial_mem_tensorSpace (selector C)

abbrev Remaining (u v : I×Fin 2) := {i : I // i≠ u.1 ∧ i≠ v.1}

def remainingEmbedding (u v : I×Fin 2) : Remaining u v × Fin 2 ↪ I×Fin 2 where
  toFun w := (w.1.1,w.2)
  inj' := by
    rintro ⟨i,a⟩ ⟨j,b⟩ h
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst h)
    · exact congrArg (fun z : I × Fin 2 => z.2) h

def edgeContext (u v : I×Fin 2)
    (s : Cube (Remaining u v) × Cube (Remaining u v)) : Finset (I×Fin 2) :=
  (subsetOfBits s).map (remainingEmbedding u v)

@[simp] theorem left_not_mem_edgeContext (u v : I×Fin 2)
    (s : Cube (Remaining u v) × Cube (Remaining u v)) : u∉edgeContext u v s := by
  rintro h
  obtain ⟨w,hw,he⟩ := mem_map.mp h
  exact w.1.2.1 (congrArg Prod.fst he)

@[simp] theorem right_not_mem_edgeContext (u v : I×Fin 2)
    (s : Cube (Remaining u v) × Cube (Remaining u v)) : v∉edgeContext u v s := by
  rintro h
  obtain ⟨w,hw,he⟩ := mem_map.mp h
  exact w.1.2.2 (congrArg Prod.fst he)

def remainingPart (u v : I×Fin 2) (C : Finset (I×Fin 2)) :
    Finset (Remaining u v × Fin 2) :=
  univ.filter fun w => remainingEmbedding u v w∈C

@[simp] theorem mem_remainingPart (u v : I×Fin 2) (C : Finset (I×Fin 2))
    (w : Remaining u v × Fin 2) : w∈remainingPart u v C ↔ remainingEmbedding u v w∈C :=
  by simp [remainingPart]

theorem remainingPart_partialTransversal {u v : I×Fin 2} {C : Finset (I×Fin 2)}
    (hC : IsPartialTransversal C) : IsPartialTransversal (remainingPart u v C) := by
  intro i hi
  exact hC i.1 ⟨(mem_remainingPart _ _ _ _).mp hi.1,(mem_remainingPart _ _ _ _).mp hi.2⟩

theorem clique_edge_subset_iff {u v : I×Fin 2} {C : Finset (I×Fin 2)}
    (hC : (graph I).IsClique C) (hu : u∈C) (hv : v∈C)
    (s : Cube (Remaining u v) × Cube (Remaining u v)) :
    C⊆insert u (insert v (edgeContext u v s)) ↔
      remainingPart u v C⊆subsetOfBits s := by
  constructor
  · intro h w hw
    have he := h ((mem_remainingPart _ _ _ _).mp hw)
    rcases mem_insert.mp he with he | he
    · exact False.elim (w.1.2.1 (congrArg Prod.fst he))
    · rcases mem_insert.mp he with he | he
      · exact False.elim (w.1.2.2 (congrArg Prod.fst he))
      · obtain ⟨w',hw',he⟩ := mem_map.mp he
        have hw'e : w'=w := (remainingEmbedding u v).injective he
        simpa only [hw'e] using hw'
  · intro h w hw
    by_cases hwu : w=u
    · simp [hwu]
    by_cases hwv : w=v
    · simp [hwv]
    have hpu : w.1≠ u.1 := hC hw hu hwu
    have hpv : w.1≠ v.1 := hC hw hv hwv
    let w' : Remaining u v × Fin 2 := (⟨w.1,hpu,hpv⟩,w.2)
    have hw' : w'∈remainingPart u v C := (mem_remainingPart _ _ _ _).mpr hw
    exact mem_insert_of_mem (mem_insert_of_mem (mem_map.mpr ⟨w',h hw',rfl⟩))

theorem delta_setMonomial_tensor {u v : I×Fin 2} (huv : u≠ v)
    {C : Finset (I×Fin 2)} (hC : (graph I).IsClique C) :
    (fun uv => delta (setMonomial C) u v
      (edgeContext u v (coordinateChange.symm uv)))∈tensorSpace := by
  by_cases hu : u∈C
  · by_cases hv : v∈C
    · have h := setMonomial_mem_tensorSpace
        (remainingPart_partialTransversal (u := u) (v := v) (clique_partialTransversal hC))
      convert h using 1
      funext uv
      rw [delta_setMonomial huv (left_not_mem_edgeContext _ _ _) (right_not_mem_edgeContext _ _ _)]
      simp only [hu,hv,true_and,clique_edge_subset_iff hC hu hv,setMonomial]
    · convert (tensorSpace (I := Remaining u v)).zero_mem using 1
      funext uv
      rw [delta_setMonomial huv (left_not_mem_edgeContext _ _ _) (right_not_mem_edgeContext _ _ _)]
      simp [hv]
  · convert (tensorSpace (I := Remaining u v)).zero_mem using 1
    funext uv
    rw [delta_setMonomial huv (left_not_mem_edgeContext _ _ _) (right_not_mem_edgeContext _ _ _)]
    simp [hu]

/-- Every actual elemental row of a normalized graphical function belongs to
the precise tensor space used by the Boolean face argument. No row-space
hypothesis is assumed: it follows from the original clique coefficients. -/
theorem graphical_edgeProfile_mem_tensorSpace {f : SetFunction (I×Fin 2)}
    (hn : TranslationNormalized f) (hG : Graphical (graph I) f)
    {u v : I×Fin 2} (huv : u≠ v) :
    (fun uv => delta f u v (edgeContext u v (coordinateChange.symm uv)))∈tensorSpace := by
  have hsupport := (mobius_cliqueSupported_iff (graph I) f).mpr ⟨hn,hG⟩
  have hsum : (∑ C : Finset (I×Fin 2),mobius f C •
      (fun uv => delta (setMonomial C) u v
        (edgeContext u v (coordinateChange.symm uv))))∈tensorSpace := by
    apply (tensorSpace (I := Remaining u v)).sum_mem
    intro C hC
    by_cases hc : mobius f C=0
    · simp only [hc,zero_smul]
      exact (tensorSpace (I := Remaining u v)).zero_mem
    · have hcl : (graph I).IsClique C := by
        by_contra hnC
        exact hc (coefficient_zero_of_not_clique hsupport C (by
          rintro ⟨_,h⟩
          exact hnC h))
      exact (tensorSpace (I := Remaining u v)).smul_mem _ (delta_setMonomial_tensor huv hcl)
  convert hsum using 1
  funext uv
  conv_lhs => rw [← zeta_mobius f,zeta_eq_sum_monomials]
  simp only [delta_sum,delta_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

end DoubledParts
end GraphicalZonotopes

end
end
end BundlePart241

section BundlePart242
/- Source: Papers/GraphicalZonotopes/PairRelabelling.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset BooleanFourier
open scoped BigOperators symmDiff
attribute [local instance] Classical.propDecidable
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def pairedEmbedding (e : I ↪ J) : I×Fin 2 ↪ J×Fin 2 :=
  e.prodMap (Function.Embedding.refl (Fin 2))

theorem firstSet_map (e : I ↪ J) (S : Finset (I×Fin 2)) :
    firstSet (S.map (pairedEmbedding e))=(firstSet S).map e := by
  ext j
  rw [mem_firstSet,mem_map,mem_map]
  constructor
  · rintro ⟨⟨i,b⟩,hi,h⟩
    have hb : b=0 := congrArg Prod.snd h
    subst b
    exact ⟨i,(mem_firstSet _ _).mpr hi,congrArg Prod.fst h⟩
  · rintro ⟨i,hi,h⟩
    exact ⟨(i,0),(mem_firstSet _ _).mp hi,Prod.ext h rfl⟩

theorem secondSet_map (e : I ↪ J) (S : Finset (I×Fin 2)) :
    secondSet (S.map (pairedEmbedding e))=(secondSet S).map e := by
  ext j
  rw [mem_secondSet,mem_map,mem_map]
  constructor
  · rintro ⟨⟨i,b⟩,hi,h⟩
    have hb : b=1 := congrArg Prod.snd h
    subst b
    exact ⟨i,(mem_secondSet _ _).mpr hi,congrArg Prod.fst h⟩
  · rintro ⟨i,hi,h⟩
    exact ⟨(i,1),(mem_secondSet _ _).mp hi,Prod.ext h rfl⟩

theorem integerData_map (e : I ↪ J) (S : Finset (I×Fin 2)) :
    integerData (S.map (pairedEmbedding e))=integerData S := by
  have h1 := integerData_count_identity (S.map (pairedEmbedding e))
  have h2 := integerData_count_identity S
  rw [firstSet_map,secondSet_map,← map_inter,card_map,card_map,card_map] at h1
  omega

def remainingPartEmbedding (u v : I×Fin 2) : Remaining u v ↪ I :=
  ⟨Subtype.val,Subtype.val_injective⟩

theorem remainingEmbedding_eq (u v : I×Fin 2) :
    remainingEmbedding u v=pairedEmbedding (remainingPartEmbedding u v) := by
  apply Function.Embedding.ext
  intro w
  rfl

theorem integerData_edgeContext (u v : I×Fin 2)
    (s : Cube (Remaining u v) × Cube (Remaining u v)) :
    integerData (edgeContext u v s)=integerData (subsetOfBits s) := by
  rw [edgeContext,remainingEmbedding_eq,integerData_map]

@[simp] theorem edgeContext_card (u v : I×Fin 2)
    (s : Cube (Remaining u v) × Cube (Remaining u v)) :
    (edgeContext u v s).card=(subsetOfBits s).card := by
  simp only [edgeContext,card_map]

theorem edgeContext_remainingPart (u v : I×Fin 2) (S : Finset (I×Fin 2)) :
    edgeContext u v (bitsOfSubset (remainingPart u v S))=
      S∩commonNeighbors (graph I) u v := by
  rw [edgeContext,subsetOfBits_bitsOfSubset]
  ext w
  constructor
  · intro hw
    obtain ⟨w',hw',rfl⟩ := mem_map.mp hw
    refine mem_inter.mpr ⟨(mem_remainingPart _ _ _ _).mp hw',?_⟩
    exact (mem_commonNeighbors _ _ _ _).mpr ⟨Ne.symm w'.1.2.1,Ne.symm w'.1.2.2⟩
  · intro hw
    rcases mem_inter.mp hw with ⟨hw,hn⟩
    rcases (mem_commonNeighbors _ _ _ _).mp hn with ⟨hu,hv⟩
    let w' : Remaining u v × Fin 2 := (⟨w.1,Ne.symm hu,Ne.symm hv⟩,w.2)
    exact mem_map.mpr ⟨w',(mem_remainingPart _ _ _ _).mpr hw,rfl⟩

theorem edgeContext_all_adj (u v : I×Fin 2)
    (s : Cube (Remaining u v) × Cube (Remaining u v)) :
    ∀ w∈edgeContext u v s,(graph I).Adj u w ∧ (graph I).Adj v w := by
  intro w hw
  obtain ⟨w',hw',rfl⟩ := mem_map.mp hw
  exact ⟨Ne.symm w'.1.2.1,Ne.symm w'.1.2.2⟩

theorem integerData_insert_common (u : I×Fin 2) (S : Finset (I×Fin 2))
    (hu : u∉S) (ha : ∀ w∈S,(graph I).Adj u w) :
    integerData (insert u S)=integerData S+(S.card : ℤ)+firstWeight u := by
  apply Int.cast_injective (α := ℝ)
  push_cast
  simp only [cast_integerData]
  rw [graphFunction_insert _ u S hu]
  have he : (∑ w∈S,if (graph I).Adj u w then (1 : ℝ) else 0)=(S.card : ℝ) := by
    simp only [sum_ite_of_true ha,sum_const,nsmul_eq_mul,mul_one]
  rw [he]
  simp only [modular,subsetSum,sum_insert hu]
  ring

theorem firstWeight_isBit (u : I×Fin 2) : firstWeight u=0 ∨ firstWeight u=1 := by
  unfold firstWeight
  split_ifs <;> simp

end DoubledParts
end GraphicalZonotopes

end
end
end BundlePart242

section BundlePart243
/- Source: Papers/GraphicalZonotopes/LocalSlopes.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem mobius_sub (f g : SetFunction V) : mobius (f-g)=mobius f-mobius g := by
  exact (zetaEquiv (V := V)).symm.map_sub f g

@[simp] theorem mobius_smul (a : ℝ) (f : SetFunction V) : mobius (a • f)=a • mobius f := by
  exact (zetaEquiv (V := V)).symm.map_smul a f

/-- Equality of an entire elemental row determines every Möbius coefficient
containing its two endpoints. This is Boolean Möbius inversion, not a test on
selected contexts. -/
theorem mobius_scale_of_delta_scale {f z : SetFunction V} {u v : V}
    (huv : u≠ v) (a : ℝ)
    (h : ∀ S : Finset V,u∉S → v∉S → delta f u v S=a*delta z u v S)
    {C : Finset V} (hu : u∈C) (hv : v∈C) : mobius f C=a*mobius z C := by
  have hzero : ∀ S : Finset V,u∉S → v∉S → delta (f-a • z) u v S=0 := by
    intro S hSu hSv
    rw [delta_sub,delta_smul,h S hSu hSv,sub_self]
  have hcoeff := (nonedge_coefficients_zero_iff (mobius (f-a • z)) huv).mp
    (by simpa only [zeta_mobius] using hzero) C hu hv
  rw [mobius_sub,mobius_smul] at hcoeff
  change mobius f C-a*mobius z C=0 at hcoeff
  exact sub_eq_zero.mp hcoeff

abbrev SlopeEdge (G : SimpleGraph V) := {e : V×V // G.Adj e.1 e.2}

/-- Edge scales interact whenever the same nonzero original Möbius
coefficient contains both edges. -/
def coefficientEdgeGraph (G : SimpleGraph V) (z : SetFunction V) :
    SimpleGraph (SlopeEdge G) where
  Adj e f := e≠ f ∧ ∃ C : Finset V,mobius z C≠0 ∧
    e.1.1∈C ∧ e.1.2∈C ∧ f.1.1∈C ∧ f.1.2∈C
  symm := ⟨by
    rintro e f ⟨hef,C,hC,he₁,he₂,hf₁,hf₂⟩
    exact ⟨Ne.symm hef,C,hC,hf₁,hf₂,he₁,he₂⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- A local-to-global extremality criterion used in the Boolean phase
construction. Each local hypothesis concerns every context of the actual
original elemental row. Connected nonzero coefficients then force all row
scales to agree. -/
theorem extremeSupermodular_of_local_row_lines {G : SimpleGraph V}
    {z : SetFunction V} (hn : TranslationNormalized z) (hs : Supermodular z)
    (hne : z≠0) (hG : Graphical G z)
    (hconn : (coefficientEdgeGraph G z).Connected)
    (hlocal : ∀ f : SetFunction V,TranslationNormalized f →
      (∀ u v,u≠ v → ∀ S : Finset V,u∉S → v∉S →
        delta z u v S=0 → delta f u v S=0) →
      ∀ e : SlopeEdge G,∃ a : ℝ,∀ S : Finset V,
        e.1.1∉S → e.1.2∉S → delta f e.1.1 e.1.2 S=a*delta z e.1.1 e.1.2 S) :
    ExtremeSupermodular z := by
  classical
  apply extremeSupermodular_of_tightEquations hn hs hne
  intro f hfn hzeros
  choose a ha using hlocal f hfn hzeros
  obtain ⟨e₀⟩ := hconn.nonempty
  have hedge : ∀ e d : SlopeEdge G,(coefficientEdgeGraph G z).Adj e d → a e=a d := by
    rintro e d ⟨hed,C,hC,he₁,he₂,hd₁,hd₂⟩
    have he := mobius_scale_of_delta_scale (G.ne_of_adj e.2) (a e) (ha e) he₁ he₂
    have hd := mobius_scale_of_delta_scale (G.ne_of_adj d.2) (a d) (ha d) hd₁ hd₂
    exact mul_right_cancel₀ hC (he.symm.trans hd)
  have hconst : ∀ e : SlopeEdge G,a e=a e₀ := by
    intro e
    have hr := hconn.preconnected e e₀
    rw [SimpleGraph.reachable_eq_reflTransGen] at hr
    induction hr with
    | refl => rfl
    | @tail d e hpath hde ih => exact ih.trans (hedge d e hde)
  have hrow : ∀ u v,u≠ v → ∀ S : Finset V,u∉S → v∉S →
      delta f u v S=a e₀*delta z u v S := by
    intro u v huv S hu hv
    by_cases hadj : G.Adj u v
    · let e : SlopeEdge G := ⟨(u,v),hadj⟩
      have h := ha e S hu hv
      rw [hconst e] at h
      exact h
    · have hz := hG u v huv hadj S hu hv
      rw [hzeros u v huv S hu hv hz,hz,mul_zero]
  have hwn : TranslationNormalized (f-a e₀ • z) := by
    refine ⟨?_,?_⟩
    · change f ∅-a e₀*z ∅=0
      rw [hfn.1,hn.1]
      ring
    · intro v
      change f {v}-a e₀*z {v}=0
      rw [hfn.2 v,hn.2 v]
      ring
  refine ⟨a e₀,sub_eq_zero.mp (normalized_zero_elemental_eq_zero hwn ?_)⟩
  intro u v huv S hu hv
  rw [delta_sub,delta_smul,hrow u v huv S hu hv,sub_self]

end GraphicalZonotopes

end
end
end BundlePart243

section BundlePart244
/- Source: Papers/GraphicalZonotopes/DoubledFourCoefficients.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem integerData_of_clique {C : Finset (I×Fin 2)} (hC : (graph I).IsClique C) :
    integerData C=(C.card.choose 2 : ℤ)+∑ v∈C,firstWeight v := by
  have he : firstSet C∩secondSet C=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro i hi
    rcases mem_inter.mp hi with ⟨h0,h1⟩
    exact hC ((mem_firstSet _ _).mp h0) ((mem_secondSet _ _).mp h1) (by simp) rfl
  have h := integerData_count_identity C
  rw [he,card_empty,Int.natCast_zero,add_zero,← firstWeight_sum] at h
  exact h

def fourRoundedCoefficient (a b c d : ℤ) : ℤ :=
  (6+a+b+c+d)/2-(3+a+b+c)/2-(3+a+b+d)/2-(3+a+c+d)/2-(3+b+c+d)/2+
    (1+a+b)/2+(1+a+c)/2+(1+a+d)/2+(1+b+c)/2+(1+b+d)/2+(1+c+d)/2

/-- The only bounded calculation is a universal four-bit algebra identity;
its application below quantifies over every four-clique in every graph size. -/
theorem fourRoundedCoefficient_sign (a b c d : ℤ)
    (ha : a=0 ∨ a=1) (hb : b=0 ∨ b=1) (hc : c=0 ∨ c=1) (hd : d=0 ∨ d=1) :
    fourRoundedCoefficient a b c d=1 ∨ fourRoundedCoefficient a b c d= -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;>
    norm_num [fourRoundedCoefficient]

theorem mobius_setFunction_four (a b c d : I×Fin 2)
    (hab : a≠ b) (hac : a≠ c) (had : a≠ d)
    (hbc : b≠ c) (hbd : b≠ d) (hcd : c≠ d)
    (hC : (graph I).IsClique ({a,b,c,d} : Finset (I×Fin 2))) :
    mobius setFunction {a,b,c,d}=
      (fourRoundedCoefficient (firstWeight a) (firstWeight b) (firstWeight c) (firstWeight d) : ℝ) := by
  have hform (T : Finset (I×Fin 2)) (hT : T⊆{a,b,c,d}) :
      integerData T=(T.card.choose 2 : ℤ)+∑ v∈T,firstWeight v := by
    apply integerData_of_clique
    intro x hx y hy hxy
    exact hC (hT hx) (hT hy) hxy
  rw [mobius_four_normalized setFunction setFunction_translationNormalized hab hac had hbc hbd hcd]
  norm_num [setFunction,hform,hab,hac,had,hbc,hbd,hcd,fourRoundedCoefficient,
    Finset.insert_subset_iff, Finset.singleton_subset_iff, Nat.choose]
  <;> ring

/-- Every tetrahedral coefficient is nonzero, in every number of doubled
parts, for every choice of the four selected endpoint sides. -/
theorem mobius_setFunction_four_sign {C : Finset (I×Fin 2)}
    (hcard : C.card=4) (hC : (graph I).IsClique C) :
    mobius setFunction C=1 ∨ mobius setFunction C= -1 := by
  obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,rfl⟩ := card_eq_four.mp hcard
  rw [mobius_setFunction_four a b c d hab hac had hbc hbd hcd hC]
  rcases fourRoundedCoefficient_sign (firstWeight a) (firstWeight b) (firstWeight c) (firstWeight d)
      (firstWeight_isBit a) (firstWeight_isBit b) (firstWeight_isBit c) (firstWeight_isBit d) with h | h
  · exact Or.inl (by exact_mod_cast h)
  · exact Or.inr (by exact_mod_cast h)

theorem mobius_setFunction_four_ne_zero {C : Finset (I×Fin 2)}
    (hcard : C.card=4) (hC : (graph I).IsClique C) : mobius setFunction C≠0 := by
  rcases mobius_setFunction_four_sign hcard hC with h | h <;> rw [h] <;> norm_num

theorem mobius_graphFunction_four_zero {C : Finset (I×Fin 2)} (hcard : C.card=4) :
    mobius (graphFunction (graph I)) C=0 := by
  obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,rfl⟩ := card_eq_four.mp hcard
  rw [mobius_four_eq _ hab hac had hbc hbd hcd]
  rw [graphFunction_delta _ hab (by simp [hac,had]) (by simp [hbc,hbd]),
    graphFunction_delta _ hab (by simp [hac]) (by simp [hbc]),
    graphFunction_delta _ hab (by simp [had]) (by simp [hbd]),
    graphFunction_delta _ hab (by simp) (by simp)]
  ring

theorem mobius_complementFunction_four_ne_zero {C : Finset (I×Fin 2)}
    (hcard : C.card=4) (hC : (graph I).IsClique C) : mobius complementFunction C≠0 := by
  rw [complementFunction,mobius_sub]
  change mobius (graphFunction (graph I)) C-mobius setFunction C≠0
  rw [mobius_graphFunction_four_zero hcard,zero_sub]
  exact neg_ne_zero.mpr (mobius_setFunction_four_ne_zero hcard hC)

end DoubledParts
end GraphicalZonotopes

end
end
end BundlePart244

section BundlePart245
/- Source: Papers/GraphicalZonotopes/FloorPhase.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace GraphicalZonotopes
namespace FloorHalf

/-- Exact remainder characterization, including negative integers. -/
theorem even_iff_mod_two (m : ℤ) : Even m ↔ m%2=0 := by
  constructor
  · rintro ⟨k,hk⟩
    omega
  · intro hm
    exact ⟨m/2,by omega⟩

theorem sign_zpow_mod_two (m : ℤ) :
    (-1 : ℝ)^m=if m%2=0 then 1 else -1 := by
  simp only [neg_one_zpow_eq_ite,even_iff_mod_two]

/-- Floor division as its linear part plus the exact parity correction. -/
theorem floor_half_phase (m : ℤ) :
    ((m/2 : ℤ) : ℝ)=(m : ℝ)/2+((-1 : ℝ)^m-1)/4 := by
  rw [sign_zpow_mod_two]
  by_cases hm : m%2=0
  · rw [if_pos hm]
    have he : m=2*(m/2) := by omega
    have hc : (m : ℝ)=2*((m/2 : ℤ) : ℝ) := by exact_mod_cast he
    linarith
  · rw [if_neg hm]
    have he : m=2*(m/2)+1 := by omega
    have hc : (m : ℝ)=2*((m/2 : ℤ) : ℝ)+1 := by exact_mod_cast he
    linarith

def edgePhaseInteger (m t a b : ℤ) : ℤ :=
  if a=b then
    if a=1 then (if (m+t)%2=0 then 1 else -1)
    else -(if (m+t)%2=0 then 1 else -1)
  else if m%2=0 then 1 else -1

theorem rounded_edge_phase_integer (m t a b : ℤ)
    (ha : a=0 ∨ a=1) (hb : b=0 ∨ b=1) :
    2*((m+2*t+a+b+1)/2+m/2-(m+t+a)/2-(m+t+b)/2)=
      1+edgePhaseInteger m t a b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp only [edgePhaseInteger] <;> split_ifs <;> omega

/-- The exact original row profile, with all four endpoint-side choices.
Only the two endpoint bits are split; `m` and the context size are arbitrary. -/
theorem rounded_edge_phase (m t a b : ℤ)
    (ha : a=0 ∨ a=1) (hb : b=0 ∨ b=1) :
    (((m+2*t+a+b+1)/2 : ℤ) : ℝ)+((m/2 : ℤ) : ℝ)-
        (((m+t+a)/2 : ℤ) : ℝ)-(((m+t+b)/2 : ℤ) : ℝ)=
      (1+(if a=b then if a=1 then (-1 : ℝ)^(m+t) else -(-1 : ℝ)^(m+t)
        else (-1 : ℝ)^m))/2 := by
  have h := rounded_edge_phase_integer m t a b ha hb
  have hc : 2*((((m+2*t+a+b+1)/2 : ℤ) : ℝ)+((m/2 : ℤ) : ℝ)-
      (((m+t+a)/2 : ℤ) : ℝ)-(((m+t+b)/2 : ℤ) : ℝ))=
      1+(edgePhaseInteger m t a b : ℝ) := by exact_mod_cast h
  have hp : (edgePhaseInteger m t a b : ℝ)=
      if a=b then if a=1 then (-1 : ℝ)^(m+t) else -(-1 : ℝ)^(m+t)
      else (-1 : ℝ)^m := by
    rw [sign_zpow_mod_two,sign_zpow_mod_two]
    unfold edgePhaseInteger
    split_ifs <;> norm_num
  rw [hp] at hc
  linarith

end FloorHalf
end GraphicalZonotopes

end
end BundlePart245

section BundlePart246
/- Source: Papers/GraphicalZonotopes/CompleteBooleanPhase.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace BooleanFourier
open Finset
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

def vertexOfSet (S : Finset I) : Cube I := fun i => decide (i∈S)
def trueSet (v : Cube I) : Finset I := univ.filter (fun i => v i=true)

@[simp] theorem trueSet_vertexOfSet (S : Finset I) : trueSet (vertexOfSet S)=S := by
  ext i
  simp [trueSet,vertexOfSet]

@[simp] theorem character_vertex_empty (A : Finset I) : character A (vertexOfSet ∅)=1 := by
  simp [character,vertexOfSet,spin]

theorem character_vertex_singleton (A : Finset I) (i : I) :
    character A (vertexOfSet {i})=if i∈A then -1 else 1 := by
  unfold character
  rw [prod_eq_single i]
  · simp [vertexOfSet,spin]
  · intro j hj hji
    simp [vertexOfSet,spin,hji]
  · simp

theorem character_vertex_pair (A : Finset I) {i j : I} (hij : i≠ j) :
    character A (vertexOfSet {i,j})=
      character A (vertexOfSet {i})*character A (vertexOfSet {j}) := by
  simp only [character,← prod_mul_distrib]
  apply prod_congr rfl
  intro k hk
  by_cases hA : k∈A
  · by_cases hi : k=i
    · subst k
      simp [vertexOfSet,spin,hA,hij]
    · by_cases hj : k=j
      · subst k
        simp [vertexOfSet,spin,hA,Ne.symm hij]
      · simp [vertexOfSet,spin,hA,hi,hj]
  · simp [hA]

/-- A quadratic Boolean phase with every mixed pair present, arbitrary linear
part `L`, and an arbitrary nonzero constant multiplier. The exponent is the
number of pairs of true bits, so this is precisely the complete quadratic form. -/
def completePhase (c : ℝ) (L : Finset I) (v : Cube I) : ℝ :=
  c*(-1 : ℝ)^((trueSet v).card.choose 2)*character L v

@[simp] theorem completePhase_empty (c : ℝ) (L : Finset I) :
    completePhase c L (vertexOfSet ∅)=c := by
  simp [completePhase]

theorem completePhase_singleton (c : ℝ) (L : Finset I) (i : I) :
    completePhase c L (vertexOfSet {i})=c*character L (vertexOfSet {i}) := by
  simp [completePhase]

theorem completePhase_pair (c : ℝ) (L : Finset I) {i j : I} (hij : i≠ j) :
    completePhase c L (vertexOfSet {i,j})=
      -c*character L (vertexOfSet {i})*character L (vertexOfSet {j}) := by
  rw [completePhase,trueSet_vertexOfSet,card_pair hij]
  norm_num
  rw [character_vertex_pair L hij]
  ring

theorem completePhase_ne_zero {c : ℝ} (hc : c≠0) (L : Finset I) (v : Cube I) :
    completePhase c L v≠0 := by
  exact mul_ne_zero (mul_ne_zero hc (pow_ne_zero _ (by norm_num)))
    (character_ne_zero L v)

theorem completePhase_isSign {c : ℝ} (hc : c=1 ∨ c=-1) (L : Finset I) (v : Cube I) :
    completePhase c L v=1 ∨ completePhase c L v=-1 := by
  have hp : ∀ n : ℕ,(-1 : ℝ)^n=1 ∨ (-1 : ℝ)^n=-1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rcases ih with h | h <;> simp [pow_succ,h]
  have hchar : character L v=1 ∨ character L v=-1 := by
    have hsq := character_square L v
    have hprod : (character L v-1)*(character L v+1)=0 := by nlinarith [hsq]
    rcases mul_eq_zero.mp hprod with h | h
    · left; linarith
    · right; linarith
  rcases hc with hc | hc <;> rcases hp ((trueSet v).card.choose 2) with hp | hp <;>
    rcases hchar with hchar | hchar <;> simp [completePhase,hc,hp,hchar]

/-- The four-corner identity of a genuine separated function. Only the
defining coordinate dependence of the two factors is used. -/
theorem separated_four_corner {G H K : Cube I → ℝ} {A : Finset I}
    (hH : DependsOn A H) (hK : DependsOn Aᶜ K)
    (hfactor : ∀ v,G v=H v*K v) {i j : I} (hi : i∈A) (hj : j∉A) :
    G (vertexOfSet ∅)*G (vertexOfSet {i,j})=
      G (vertexOfSet {i})*G (vertexOfSet {j}) := by
  have hij : i≠ j := by intro h; exact hj (h ▸ hi)
  have hH₀ : H (vertexOfSet {j})=H (vertexOfSet ∅) := by
    apply hH
    intro k hk
    have hkj : k≠ j := by intro h; exact hj (h ▸ hk)
    simp [vertexOfSet,hkj]
  have hH₁ : H (vertexOfSet {i,j})=H (vertexOfSet {i}) := by
    apply hH
    intro k hk
    have hkj : k≠ j := by intro h; exact hj (h ▸ hk)
    simp [vertexOfSet,hkj]
  have hK₀ : K (vertexOfSet {i})=K (vertexOfSet ∅) := by
    apply hK
    intro k hk
    have hki : k≠ i := by
      intro h
      have hn : k∉A := mem_compl.mp hk
      exact hn (h.symm ▸ hi)
    simp [vertexOfSet,hki]
  have hK₁ : K (vertexOfSet {i,j})=K (vertexOfSet {j}) := by
    apply hK
    intro k hk
    have hki : k≠ i := by
      intro h
      have hn : k∉A := mem_compl.mp hk
      exact hn (h.symm ▸ hi)
    simp [vertexOfSet,hki]
  rw [hfactor,hfactor,hfactor,hfactor,hH₀,hH₁,hK₀,hK₁]
  ring

/-- Every complete quadratic phase is nonseparable across every nonempty
proper partition, in every finite number of variables. This is the exact
nonfactorization property used by Theorem9.8 after the Walsh calculation. -/
theorem completePhase_nonseparable {c : ℝ} (hc : c≠0) (L : Finset I) :
    Nonseparable (completePhase c L) := by
  intro A hA htop hfactor
  obtain ⟨i,hi⟩ := hA
  obtain ⟨j,hj⟩ : ∃ j : I,j∉A := by
    by_contra! hall
    apply htop
    ext j
    simp [hall j]
  obtain ⟨H,K,hH,hK,hsep⟩ := hfactor
  have hij : i≠ j := by intro h; exact hj (h ▸ hi)
  have hs := separated_four_corner hH hK hsep hi hj
  have hm : completePhase c L (vertexOfSet ∅)*completePhase c L (vertexOfSet {i,j})=
      -(completePhase c L (vertexOfSet {i})*completePhase c L (vertexOfSet {j})) := by
    rw [completePhase_empty,completePhase_pair c L hij,
      completePhase_singleton,completePhase_singleton]
    ring
  have hzero : completePhase c L (vertexOfSet {i})*completePhase c L (vertexOfSet {j})=0 := by
    linarith [hs,hm]
  exact (mul_ne_zero (completePhase_ne_zero hc L _) (completePhase_ne_zero hc L _)) hzero

end BooleanFourier
end GraphicalZonotopes

end
end
end BundlePart246

section BundlePart247
/- Source: Papers/GraphicalZonotopes/DoubledPhase.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset BooleanFourier
open scoped BigOperators symmDiff
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem character_univ_parity (s : Cube I) :
    character univ s=QuadraticSign.parity (trueSet s).card := by
  rw [character_univ]
  have hf : ∀ i : I,spin (s i)=if i∈trueSet s then (-1 : ℝ) else 1 := by
    intro i
    cases hs : s i <;> simp [spin,trueSet,hs]
  simp_rw [hf]
  rw [prod_ite_mem_eq]
  simp [QuadraticSign.parity]

theorem trueSet_xor (s t : Cube I) :
    trueSet (fun i => Bool.xor (s i) (t i))=trueSet s∆trueSet t := by
  ext i
  cases hs : s i <;> cases ht : t i <;> simp [trueSet,Finset.mem_symmDiff,hs,ht]

@[simp] theorem firstSet_subsetOfBits (s : Cube I × Cube I) :
    firstSet (subsetOfBits s)=trueSet s.1 := by
  ext i
  simp [trueSet]

@[simp] theorem secondSet_subsetOfBits (s : Cube I × Cube I) :
    secondSet (subsetOfBits s)=trueSet s.2 := by
  ext i
  simp [trueSet]

theorem transformed_firstSet (uv : Cube I × Cube I) :
    firstSet (subsetOfBits (coordinateChange.symm uv))=trueSet uv.1 := by
  rw [firstSet_subsetOfBits]
  rfl

theorem transformed_secondSet (uv : Cube I × Cube I) :
    secondSet (subsetOfBits (coordinateChange.symm uv))=trueSet uv.1∆trueSet uv.2 := by
  rw [secondSet_subsetOfBits]
  exact trueSet_xor uv.1 uv.2

theorem integerData_transformed_phase (uv : Cube I × Cube I) :
    (-1 : ℝ)^integerData (subsetOfBits (coordinateChange.symm uv))=
      phase (completePhase 1 ∅) uv := by
  rw [integerData_phase,transformed_firstSet,transformed_secondSet,
    symmDiff_symmDiff_cancel_left,← character_univ_parity]
  simp [phase,completePhase,QuadraticSign.complete,QuadraticSign.triangle,
    QuadraticSign.parity]

theorem transformed_card_phase (uv : Cube I × Cube I) :
    (-1 : ℝ)^((subsetOfBits (coordinateChange.symm uv)).card)=character univ uv.2 := by
  change QuadraticSign.parity _=_
  rw [card_eq_first_add_second,transformed_firstSet,transformed_secondSet,
    QuadraticSign.parity_add,QuadraticSign.parity_card_symmDiff,
    ← mul_assoc,QuadraticSign.parity_square,one_mul,character_univ_parity]

/-- The complete quadratic phase occurring in an original edge row. Its
linear part depends only on whether the endpoint sides agree. -/
def rowPhase (u v : I×Fin 2) : Cube (Remaining u v) → ℝ :=
  completePhase (if u.2=1 ∧ v.2=1 then -1 else 1)
    (if u.2=v.2 then univ else ∅)

theorem rowPhase_isSign (u v : I×Fin 2) (x : Cube (Remaining u v)) :
    rowPhase u v x=1 ∨ rowPhase u v x= -1 := by
  apply completePhase_isSign
  split_ifs <;> simp

theorem rowPhase_nonseparable (u v : I×Fin 2) : Nonseparable (rowPhase u v) := by
  apply completePhase_nonseparable
  split_ifs <;> norm_num

theorem setFunction_edgeContext_rounded {u v : I×Fin 2} (huv : (graph I).Adj u v)
    (s : Cube (Remaining u v) × Cube (Remaining u v)) :
    delta setFunction u v (edgeContext u v s)=
      (1+(if firstWeight u=firstWeight v then
          if firstWeight u=1 then
            (-1 : ℝ)^(integerData (edgeContext u v s)+(edgeContext u v s).card)
          else -(-1 : ℝ)^(integerData (edgeContext u v s)+(edgeContext u v s).card)
        else (-1 : ℝ)^integerData (edgeContext u v s)))/2 := by
  let S := edgeContext u v s
  have hmu := integerData_insert_common u S (left_not_mem_edgeContext _ _ _)
    (fun w hw => (edgeContext_all_adj u v s w hw).1)
  have hmv := integerData_insert_common v S (right_not_mem_edgeContext _ _ _)
    (fun w hw => (edgeContext_all_adj u v s w hw).2)
  have hd := integerData_mixed ((graph I).ne_of_adj huv)
    (left_not_mem_edgeContext u v s) (right_not_mem_edgeContext u v s)
  rw [if_pos huv] at hd
  have hmuv : integerData (insert u (insert v S))=
      integerData S+2*(S.card : ℤ)+firstWeight u+firstWeight v+1 := by
    change integerData (insert u (insert v S))+integerData S-
      integerData (insert u S)-integerData (insert v S)=1 at hd
    omega
  rw [delta_setFunction]
  change ((integerData (insert u (insert v S))/2+integerData S/2-
    integerData (insert u S)/2-integerData (insert v S)/2 : ℤ) : ℝ)=_
  rw [hmuv,hmu,hmv]
  push_cast
  exact FloorHalf.rounded_edge_phase _ _ _ _ (firstWeight_isBit u) (firstWeight_isBit v)

/-- The original elemental difference is exactly the Boolean tensor face
function after an explicitly invertible change of all remaining bits. -/
theorem setFunction_edgeProfile {u v : I×Fin 2} (huv : (graph I).Adj u v)
    (uv : Cube (Remaining u v) × Cube (Remaining u v)) :
    delta setFunction u v (edgeContext u v (coordinateChange.symm uv))=
      faceFunction (rowPhase u v) uv := by
  rw [setFunction_edgeContext_rounded huv,integerData_edgeContext,edgeContext_card,
    zpow_add₀ (by norm_num),zpow_natCast,integerData_transformed_phase,transformed_card_phase]
  rcases u with ⟨i,a⟩
  rcases v with ⟨j,b⟩
  fin_cases a <;> fin_cases b <;>
    simp [firstWeight,rowPhase,faceFunction,phase,completePhase] <;> ring

theorem complementFunction_edgeProfile {u v : I×Fin 2} (huv : (graph I).Adj u v)
    (uv : Cube (Remaining u v) × Cube (Remaining u v)) :
    delta complementFunction u v (edgeContext u v (coordinateChange.symm uv))=
      faceFunction (-rowPhase u v) uv := by
  rw [complementFunction,delta_sub,graphFunction_delta _ ((graph I).ne_of_adj huv)
    (left_not_mem_edgeContext _ _ _) (right_not_mem_edgeContext _ _ _),if_pos huv,
    setFunction_edgeProfile huv]
  simp only [faceFunction,phase,Pi.neg_apply]
  ring

end DoubledParts
end GraphicalZonotopes

end
end
end BundlePart247

section BundlePart248
/- Source: Papers/GraphicalZonotopes/DoubledLocalLines.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset BooleanFourier
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem remaining_nonempty (hI : 3≤ Fintype.card I) (u v : I×Fin 2) :
    Nonempty (Remaining u v) := by
  have hcard : ({u.1,v.1} : Finset I).card<(univ : Finset I).card := by
    have h : ({u.1,v.1} : Finset I).card≤2 := card_le_two
    simpa only [card_univ] using (lt_of_le_of_lt h (by omega : 2< Fintype.card I))
  obtain ⟨i,hi,hn⟩ := exists_mem_notMem_of_card_lt_card hcard
  have he : i≠ u.1 ∧ i≠ v.1 := by simpa using hn
  exact ⟨⟨i,he⟩⟩

theorem complementFunction_graphical : Graphical (graph I) (complementFunction (I := I)) := by
  intro u v huv hnon S hu hv
  rw [complementFunction,delta_sub,graphFunction_delta _ huv hu hv,
    if_neg hnon,setFunction_graphical u v huv hnon S hu hv,sub_self]

/-- A complete original row is forced to a single scale by its exact Boolean
zero pattern. All nonedge constraints are recovered before the tensor lemma
is used. -/
theorem local_row_line_of_phase {z : SetFunction (I×Fin 2)}
    (hzn : TranslationNormalized z) (hzG : Graphical (graph I) z)
    {u v : I×Fin 2} (huv : (graph I).Adj u v) [Nonempty (Remaining u v)]
    (H : Cube (Remaining u v) → ℝ) (hH : ∀ x,H x=1 ∨ H x= -1)
    (hsep : Nonseparable H)
    (hprofile : ∀ uv,delta z u v (edgeContext u v (coordinateChange.symm uv))=
      faceFunction H uv)
    (f : SetFunction (I×Fin 2)) (hfn : TranslationNormalized f)
    (hzero : ∀ a b,a≠ b → ∀ S : Finset (I×Fin 2),a∉S → b∉S →
      delta z a b S=0 → delta f a b S=0) :
    ∃ c : ℝ,∀ S : Finset (I×Fin 2),u∉S → v∉S → delta f u v S=c*delta z u v S := by
  have hfG : Graphical (graph I) f := by
    intro a b hab hnon S ha hb
    exact hzero a b hab S ha hb (hzG a b hab hnon S ha hb)
  let p : (Cube (Remaining u v) × Cube (Remaining u v)) → ℝ :=
    fun uv => delta f u v (edgeContext u v (coordinateChange.symm uv))
  have hp : p∈tensorSpace :=
    graphical_edgeProfile_mem_tensorSpace hfn hfG ((graph I).ne_of_adj huv)
  have hzeros : ∀ uv,faceFunction H uv=0 → p uv=0 := by
    intro uv he
    apply hzero u v ((graph I).ne_of_adj huv) _
      (left_not_mem_edgeContext _ _ _) (right_not_mem_edgeContext _ _ _)
    rwa [hprofile]
  obtain ⟨c,hc⟩ := (boolean_face_line hH hsep p hp).mp hzeros
  refine ⟨c,?_⟩
  intro S hu hv
  let s := bitsOfSubset (remainingPart u v S)
  let uv := coordinateChange s
  have he := congrFun hc uv
  change delta f u v (edgeContext u v (coordinateChange.symm uv))=
    c*faceFunction H uv at he
  rw [← hprofile uv] at he
  have hcontext : edgeContext u v (coordinateChange.symm uv)=
      S∩commonNeighbors (graph I) u v := by
    rw [show coordinateChange.symm uv=s by simp [uv]]
    exact edgeContext_remainingPart u v S
  rw [hcontext] at he
  rw [delta_commonNeighbors hfn hfG ((graph I).ne_of_adj huv) hu hv,
    delta_commonNeighbors hzn hzG ((graph I).ne_of_adj huv) hu hv]
  exact he

theorem setFunction_local_row_lines (hI : 3≤ Fintype.card I)
    (f : SetFunction (I×Fin 2)) (hfn : TranslationNormalized f)
    (hzero : ∀ a b,a≠ b → ∀ S : Finset (I×Fin 2),a∉S → b∉S →
      delta setFunction a b S=0 → delta f a b S=0)
    (e : SlopeEdge (graph I)) :
    ∃ c : ℝ,∀ S : Finset (I×Fin 2),e.1.1∉S → e.1.2∉S →
      delta f e.1.1 e.1.2 S=c*delta setFunction e.1.1 e.1.2 S := by
  letI := remaining_nonempty hI e.1.1 e.1.2
  exact local_row_line_of_phase setFunction_translationNormalized setFunction_graphical e.2
    (rowPhase e.1.1 e.1.2) (rowPhase_isSign _ _) (rowPhase_nonseparable _ _)
    (setFunction_edgeProfile e.2) f hfn hzero

theorem complementFunction_local_row_lines (hI : 3≤ Fintype.card I)
    (f : SetFunction (I×Fin 2)) (hfn : TranslationNormalized f)
    (hzero : ∀ a b,a≠ b → ∀ S : Finset (I×Fin 2),a∉S → b∉S →
      delta complementFunction a b S=0 → delta f a b S=0)
    (e : SlopeEdge (graph I)) :
    ∃ c : ℝ,∀ S : Finset (I×Fin 2),e.1.1∉S → e.1.2∉S →
      delta f e.1.1 e.1.2 S=c*delta complementFunction e.1.1 e.1.2 S := by
  letI := remaining_nonempty hI e.1.1 e.1.2
  apply local_row_line_of_phase complementFunction_translationNormalized complementFunction_graphical e.2
    (-rowPhase e.1.1 e.1.2) _ (rowPhase_nonseparable _ _).neg
    (complementFunction_edgeProfile e.2) f hfn hzero
  intro x
  rcases rowPhase_isSign e.1.1 e.1.2 x with h | h
  · exact Or.inr (by simpa using congrArg Neg.neg h)
  · exact Or.inl (by simpa using congrArg Neg.neg h)

theorem exists_nonzero_slack_of_phase {z : SetFunction (I×Fin 2)}
    {u v : I×Fin 2} [Nonempty (Remaining u v)]
    (H : Cube (Remaining u v) → ℝ) (hH : ∀ x,H x=1 ∨ H x= -1)
    (hprofile : ∀ uv,delta z u v (edgeContext u v (coordinateChange.symm uv))=
      faceFunction H uv) :
    ∃ S : Finset (I×Fin 2),u∉S ∧ v∉S ∧ delta z u v S≠0 := by
  have hne := faceFunction_ne_zero hH
  have hex : ∃ uv,faceFunction H uv≠0 := by
    by_contra! hall
    apply hne
    funext uv
    exact hall uv
  obtain ⟨uv,huv⟩ := hex
  refine ⟨edgeContext u v (coordinateChange.symm uv),
    left_not_mem_edgeContext _ _ _,right_not_mem_edgeContext _ _ _,?_⟩
  rwa [hprofile]

theorem setFunction_nonzero_slack (hI : 3≤ Fintype.card I) {u v : I×Fin 2}
    (huv : (graph I).Adj u v) :
    ∃ S : Finset (I×Fin 2),u∉S ∧ v∉S ∧ delta setFunction u v S≠0 := by
  letI := remaining_nonempty hI u v
  exact exists_nonzero_slack_of_phase (rowPhase u v) (rowPhase_isSign u v)
    (setFunction_edgeProfile huv)

theorem complementFunction_nonzero_slack (hI : 3≤ Fintype.card I) {u v : I×Fin 2}
    (huv : (graph I).Adj u v) :
    ∃ S : Finset (I×Fin 2),u∉S ∧ v∉S ∧ delta complementFunction u v S≠0 := by
  letI := remaining_nonempty hI u v
  apply exists_nonzero_slack_of_phase (-rowPhase u v) _ (complementFunction_edgeProfile huv)
  intro x
  rcases rowPhase_isSign u v x with h | h
  · exact Or.inr (by simpa using congrArg Neg.neg h)
  · exact Or.inl (by simpa using congrArg Neg.neg h)

end DoubledParts
end GraphicalZonotopes

end
end
end BundlePart248

section BundlePart249
/- Source: Papers/GraphicalZonotopes/DoubledConnectivity.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

def selectedClique (T : Finset I) (b : I → Fin 2) : Finset (I×Fin 2) :=
  T.image fun i => (i,b i)

@[simp] theorem mem_selectedClique (T : Finset I) (b : I → Fin 2) (w : I×Fin 2) :
    w∈selectedClique T b ↔ w.1∈T ∧ b w.1=w.2 := by
  constructor
  · intro hw
    obtain ⟨i,hi,he⟩ := mem_image.mp hw
    have h1 : i=w.1 := congrArg Prod.fst he
    have h2 : b i=w.2 := congrArg Prod.snd he
    simpa [h1] using And.intro hi h2
  · rintro ⟨hi,hb⟩
    exact mem_image.mpr ⟨w.1,hi,Prod.ext rfl hb⟩

@[simp] theorem selectedClique_card (T : Finset I) (b : I → Fin 2) :
    (selectedClique T b).card=T.card :=
  card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)

theorem selectedClique_isClique (T : Finset I) (b : I → Fin 2) :
    (graph I).IsClique (selectedClique T b) := by
  intro u hu v hv huv
  have hu' := (mem_selectedClique T b u).mp hu
  have hv' := (mem_selectedClique T b v).mp hv
  intro he
  apply huv
  apply Prod.ext he
  rw [← hu'.2,← hv'.2,he]

def canonicalEdge (e : SlopeEdge (graph I)) : SlopeEdge (graph I) :=
  ⟨((e.1.1.1,0),(e.1.2.1,0)),e.2⟩

theorem shared_four_reachable {z : SetFunction (I×Fin 2)}
    (hnon : ∀ C : Finset (I×Fin 2),C.card=4 → (graph I).IsClique C → mobius z C≠0)
    (e f : SlopeEdge (graph I)) {C : Finset (I×Fin 2)}
    (hcard : C.card=4) (hC : (graph I).IsClique C)
    (he₁ : e.1.1∈C) (he₂ : e.1.2∈C) (hf₁ : f.1.1∈C) (hf₂ : f.1.2∈C) :
    (coefficientEdgeGraph (graph I) z).Reachable e f := by
  by_cases hef : e=f
  · subst f
    exact SimpleGraph.Reachable.rfl
  · exact SimpleGraph.Adj.reachable ⟨hef,C,hnon C hcard hC,he₁,he₂,hf₁,hf₂⟩

theorem edge_reachable_canonical (hI : 4≤ Fintype.card I)
    {z : SetFunction (I×Fin 2)}
    (hnon : ∀ C : Finset (I×Fin 2),C.card=4 → (graph I).IsClique C → mobius z C≠0)
    (e : SlopeEdge (graph I)) :
    (coefficientEdgeGraph (graph I) z).Reachable e (canonicalEdge e) := by
  let a := e.1.1.1
  let b := e.1.2.1
  have hab : a≠ b := e.2
  obtain ⟨T,hST,hTU,hT⟩ := exists_subsuperset_card_eq
    (subset_univ ({a,b} : Finset I))
    (show ({a,b} : Finset I).card≤4 by simp [card_pair hab])
    (show 4≤(univ : Finset I).card by simpa using hI)
  have hD : (T\{a,b}).card=2 := by rw [card_sdiff_of_subset hST,hT,card_pair hab]
  obtain ⟨i,j,hij,hDij⟩ := card_eq_two.mp hD
  have hi : i∈T ∧ i≠ a ∧ i≠ b := by
    have h : i∈T\{a,b} := by rw [hDij]; simp
    simpa using h
  have hj : j∈T ∧ j≠ a ∧ j≠ b := by
    have h : j∈T\{a,b} := by rw [hDij]; simp
    simpa using h
  have haT : a∈T := hST (by simp)
  have hbT : b∈T := hST (by simp)
  let f : SlopeEdge (graph I) := ⟨((i,0),(j,0)),hij⟩
  let bits : I → Fin 2 := fun k => if k=a then e.1.1.2 else if k=b then e.1.2.2 else 0
  have hfirst : (coefficientEdgeGraph (graph I) z).Reachable e f := by
    apply shared_four_reachable hnon e f (C := selectedClique T bits)
      (by simpa using hT) (selectedClique_isClique T bits)
    · simp [bits,a,haT]
    · simp [bits,b,a,hbT,Ne.symm hab]
    · simp [f,bits,hi.1,hi.2.1,hi.2.2]
    · simp [f,bits,hj.1,hj.2.1,hj.2.2]
  have hsecond : (coefficientEdgeGraph (graph I) z).Reachable f (canonicalEdge e) := by
    apply shared_four_reachable hnon f (canonicalEdge e) (C := selectedClique T (fun _ => 0))
      (by simpa using hT) (selectedClique_isClique T (fun _ => 0))
    · simp [f,hi.1]
    · simp [f,hj.1]
    · simpa [canonicalEdge,a] using haT
    · simpa [canonicalEdge,b] using hbT
  exact hfirst.trans hsecond

theorem canonical_edges_reachable (hI : 4≤ Fintype.card I)
    {z : SetFunction (I×Fin 2)}
    (hnon : ∀ C : Finset (I×Fin 2),C.card=4 → (graph I).IsClique C → mobius z C≠0)
    (e f : SlopeEdge (graph I)) :
    (coefficientEdgeGraph (graph I) z).Reachable (canonicalEdge e) (canonicalEdge f) := by
  let S : Finset I := {e.1.1.1,e.1.2.1,f.1.1.1,f.1.2.1}
  obtain ⟨T,hST,hTU,hT⟩ := exists_subsuperset_card_eq
    (subset_univ S) (show S.card≤4 from card_le_four) (by simpa using hI)
  apply shared_four_reachable hnon (canonicalEdge e) (canonicalEdge f)
    (C := selectedClique T (fun _ => 0)) (by simpa using hT)
    (selectedClique_isClique T (fun _ => 0))
  · simpa [canonicalEdge] using hST (by simp [S] : e.1.1.1∈S)
  · simpa [canonicalEdge] using hST (by simp [S] : e.1.2.1∈S)
  · simpa [canonicalEdge] using hST (by simp [S] : f.1.1.1∈S)
  · simpa [canonicalEdge] using hST (by simp [S] : f.1.2.1∈S)

theorem slopeEdge_nonempty (hI : 2≤ Fintype.card I) : Nonempty (SlopeEdge (graph I)) := by
  obtain ⟨S,hS,hcard⟩ := exists_subset_card_eq
    (show 2≤(univ : Finset I).card by simpa using hI)
  obtain ⟨i,j,hij,rfl⟩ := card_eq_two.mp hcard
  exact ⟨⟨((i,0),(j,0)),hij⟩⟩

/-- Nonzero tetrahedral coefficients connect all actual edge scales, with no
bound on the number of doubled parts. -/
theorem coefficientEdgeGraph_connected (hI : 4≤ Fintype.card I)
    {z : SetFunction (I×Fin 2)}
    (hnon : ∀ C : Finset (I×Fin 2),C.card=4 → (graph I).IsClique C → mobius z C≠0) :
    (coefficientEdgeGraph (graph I) z).Connected := by
  letI := slopeEdge_nonempty (by omega : 2≤ Fintype.card I)
  refine ⟨?_⟩
  intro e f
  exact (edge_reachable_canonical hI hnon e).trans
    ((canonical_edges_reachable hI hnon e f).trans (edge_reachable_canonical hI hnon f).symm)

theorem graph_connected (hI : 2≤ Fintype.card I) : (graph I).Connected := by
  obtain ⟨e⟩ := slopeEdge_nonempty hI
  letI : Nonempty (I×Fin 2) := ⟨e.1.1⟩
  refine ⟨?_⟩
  intro u v
  by_cases huv : u.1≠ v.1
  · exact SimpleGraph.Adj.reachable huv
  · have he : u.1=v.1 := not_not.mp huv
    obtain ⟨i,hi,hn⟩ := exists_mem_notMem_of_card_lt_card
      (show ({u.1} : Finset I).card<(univ : Finset I).card by simpa using (show 1 < Fintype.card I by omega))
    have hiu : i≠ u.1 := by simpa using hn
    have hiv : i≠ v.1 := by simpa only [he] using hiu
    exact (SimpleGraph.Adj.reachable (show (graph I).Adj u (i,0) from Ne.symm hiu)).trans
      (SimpleGraph.Adj.reachable (show (graph I).Adj (i,0) v from hiv))

end DoubledParts
end GraphicalZonotopes

end
end
end BundlePart249

section BundlePart250
/- Source: Papers/GraphicalZonotopes/DoubledStarScales.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem exists_four_clique_containing_three (hI : 4≤ Fintype.card I)
    (a b c : I×Fin 2) (hab : a.1≠ b.1) (hac : a.1≠ c.1) (hbc : b.1≠ c.1) :
    ∃ C : Finset (I×Fin 2),C.card=4 ∧ (graph I).IsClique C ∧ a∈C ∧ b∈C ∧ c∈C := by
  obtain ⟨T,hST,hTU,hT⟩ := exists_subsuperset_card_eq
    (subset_univ ({a.1,b.1,c.1} : Finset I))
    (show ({a.1,b.1,c.1} : Finset I).card≤4 by
      have h : ({a.1,b.1,c.1} : Finset I).card≤3 := card_le_three
      omega)
    (show 4≤(univ : Finset I).card by simpa using hI)
  let bits : I → Fin 2 := fun i => if i=a.1 then a.2 else if i=b.1 then b.2
    else if i=c.1 then c.2 else 0
  refine ⟨selectedClique T bits,by simpa using hT,selectedClique_isClique T bits,?_,?_,?_⟩
  · simp [bits,hST (by simp : a.1∈({a.1,b.1,c.1} : Finset I))]
  · simp [bits,Ne.symm hab,hST (by simp : b.1∈({a.1,b.1,c.1} : Finset I))]
  · simp [bits,Ne.symm hac,Ne.symm hbc,
      hST (by simp : c.1∈({a.1,b.1,c.1} : Finset I))]

abbrev AtVertex (a : I×Fin 2) := {v : I×Fin 2 // (graph I).Adj a v}

theorem exists_star_vertex (hI : 2≤ Fintype.card I) (a : I×Fin 2) : Nonempty (AtVertex a) := by
  obtain ⟨i,hi,hn⟩ := exists_mem_notMem_of_card_lt_card
    (show ({a.1} : Finset I).card<(univ : Finset I).card by simp only [card_singleton,card_univ]; omega)
  have hia : i≠ a.1 := by simpa using hn
  exact ⟨⟨(i,0),Ne.symm hia⟩⟩

/-- Every locally determined scale on an edge at one fixed vertex is the
same, using only nonzero four-clique coefficients and arbitrary r≥4. -/
theorem star_scales_constant (hI : 4≤ Fintype.card I) (a : I×Fin 2)
    (z f : SetFunction (I×Fin 2))
    (hnon : ∀ C : Finset (I×Fin 2),C.card=4 → (graph I).IsClique C → mobius z C≠0)
    (scale : AtVertex a → ℝ)
    (hscale : ∀ v : AtVertex a,∀ S : Finset (I×Fin 2),a∉S → v.1∉S →
      delta f a v.1 S=scale v*delta z a v.1 S) :
    ∃ t : ℝ,∀ v : AtVertex a,scale v=t := by
  letI := exists_star_vertex (by omega : 2≤ Fintype.card I) a
  obtain ⟨v₀⟩ := ‹Nonempty (AtVertex a)›
  have hdiff (v w : AtVertex a) (hvw : v.1.1≠ w.1.1) : scale v=scale w := by
    obtain ⟨C,hcard,hC,ha,hv,hw⟩ :=
      exists_four_clique_containing_three hI a v.1 w.1 v.2 w.2 hvw
    have hv' := mobius_scale_of_delta_scale ((graph I).ne_of_adj v.2)
      (scale v) (hscale v) ha hv
    have hw' := mobius_scale_of_delta_scale ((graph I).ne_of_adj w.2)
      (scale w) (hscale w) ha hw
    exact mul_right_cancel₀ (hnon C hcard hC) (hv'.symm.trans hw')
  refine ⟨scale v₀,?_⟩
  intro v
  by_cases hparts : v.1.1≠ v₀.1.1
  · exact hdiff v v₀ hparts
  · obtain ⟨i,hi,hn⟩ := exists_mem_notMem_of_card_lt_card
      (show ({a.1,v.1.1} : Finset I).card<(univ : Finset I).card by
        have h : ({a.1,v.1.1} : Finset I).card≤2 := card_le_two
        simpa only [card_univ] using (lt_of_le_of_lt h (by omega : 2< Fintype.card I)))
    have hn' : i≠ a.1 ∧ i≠ v.1.1 := by simpa using hn
    let w : AtVertex a := ⟨(i,0),Ne.symm hn'.1⟩
    have hp : v.1.1=v₀.1.1 := not_not.mp hparts
    exact (hdiff v w (Ne.symm hn'.2)).trans (hdiff w v₀ (by simpa [w,← hp] using hn'.2))

end DoubledParts
end GraphicalZonotopes

end
end
end BundlePart250

section BundlePart251
/- Source: Papers/GraphicalZonotopes/IgnoredVertices.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Vanishing of all original elemental rows at a normalized vertex means
the function is independent of that vertex, on every subset. -/
theorem insert_eq_of_zero_incident {f : SetFunction V} (hn : TranslationNormalized f)
    (a : V) (hzero : ∀ v,a≠ v → ∀ S : Finset V,a∉S → v∉S → delta f a v S=0) :
    ∀ S : Finset V,f (insert a S)=f S := by
  intro S
  by_cases ha : a∈S
  · rw [insert_eq_of_mem ha]
  · revert ha
    induction S using Finset.induction_on with
    | empty => simp only [insert_empty_eq,show f ∅=0 from hn.1,hn.2,implies_true]
    | @insert v S hv ih =>
      intro ha
      have hav : a≠ v := fun he => ha (by simp [he])
      have haS : a∉S := fun h => ha (mem_insert_of_mem h)
      have hd := hzero v hav S haS hv
      have hi := ih haS
      unfold delta at hd
      linarith

theorem erase_eq_of_insert_eq {f : SetFunction V} {a : V}
    (hf : ∀ S : Finset V,f (insert a S)=f S) (S : Finset V) : f (S.erase a)=f S := by
  by_cases ha : a∈S
  · have h := hf (S.erase a)
    rw [insert_erase ha] at h
    exact h.symm
  · rw [erase_eq_of_notMem ha]

theorem delta_insert_eq_of_insert_eq {f : SetFunction V} {a : V}
    (hf : ∀ S : Finset V,f (insert a S)=f S) (u v : V) (S : Finset V) :
    delta f u v (insert a S)=delta f u v S := by
  simp only [delta,insert_comm u a,insert_comm v a,hf]

theorem delta_zero_of_insert_eq {f : SetFunction V} {a : V}
    (hf : ∀ S : Finset V,f (insert a S)=f S) (v : V) (S : Finset V) :
    delta f a v S=0 := by
  simp only [delta,hf]
  ring

namespace VertexDeletion

abbrev Retained (d : V) := {v : V // v≠ d}

def embedding (d : V) : Retained d ↪ V := Function.Embedding.subtype _

@[simp] theorem deleted_not_range (d : V) : d∉Set.range (embedding d) := by
  rintro ⟨v,hv⟩
  exact v.2 hv

theorem map_pullSet (d : V) (S : Finset V) :
    (SetFunctionEmbedding.pullSet (embedding d) S).map (embedding d)=S.erase d := by
  ext v
  simp only [mem_map,SetFunctionEmbedding.mem_pullSet,mem_erase]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨w.2,hw⟩
  · rintro ⟨hv,hS⟩
    exact ⟨⟨v,hv⟩,hS,rfl⟩

theorem extend_restrict (d : V) (f : SetFunction V) (S : Finset V) :
    SetFunctionEmbedding.extend (embedding d)
      (SetFunctionEmbedding.restrict (embedding d) f) S=f (S.erase d) := by
  simp only [SetFunctionEmbedding.extend,SetFunctionEmbedding.restrict,map_pullSet]

theorem delta_erase_function {f : SetFunction V} (d u v : V)
    (hu : u≠ d) (hv : v≠ d) (S : Finset V) :
    delta (fun T => f (T.erase d)) u v S=delta f u v (S.erase d) := by
  simp only [delta,erase_insert_of_ne hu,erase_insert_of_ne hv]

theorem delta_erase_eq_of_insert_eq {f : SetFunction V} {a : V}
    (hf : ∀ S : Finset V,f (insert a S)=f S) (u v : V)
    (hu : u≠ a) (hv : v≠ a) (S : Finset V) :
    delta f u v (S.erase a)=delta f u v S := by
  rw [← delta_erase_function a u v hu hv]
  have he : (fun T => f (T.erase a))=f := funext (erase_eq_of_insert_eq hf)
  rw [he]

theorem extended_tight_zero (d : V) (z : SetFunction V)
    (f : SetFunction (Retained d))
    (hzero : ∀ u v : Retained d,u≠ v → ∀ S : Finset (Retained d),u∉S → v∉S →
      delta (SetFunctionEmbedding.restrict (embedding d) z) u v S=0 → delta f u v S=0)
    {u v : V} (huv : u≠ v) (hud : u≠ d) (hvd : v≠ d)
    {S : Finset V} (hu : u∉S) (hv : v∉S) (hd : d∉S) (hz : delta z u v S=0) :
    delta (SetFunctionEmbedding.extend (embedding d) f) u v S=0 := by
  let u' : Retained d := ⟨u,hud⟩
  let v' : Retained d := ⟨v,hvd⟩
  have he := hzero u' v' (fun h => huv (congrArg Subtype.val h))
    (SetFunctionEmbedding.pullSet (embedding d) S) (by simpa [u',embedding] using hu) (by simpa [v',embedding] using hv)
  have hsmall : delta (SetFunctionEmbedding.restrict (embedding d) z) u' v'
      (SetFunctionEmbedding.pullSet (embedding d) S)=0 := by
    rw [SetFunctionEmbedding.delta_restrict,map_pullSet,erase_eq_of_notMem hd]
    exact hz
  have h := he hsmall
  simpa only [← SetFunctionEmbedding.delta_extend,embedding,u',v',Function.Embedding.coe_subtype] using h

/-- A graphical row is insensitive to deleting a nonneighbor of its first
endpoint. This follows from the full clique-coordinate dictionary. -/
theorem delta_delete_nonNeighbor {G : SimpleGraph V} {f : SetFunction V}
    (hn : TranslationNormalized f) (hG : Graphical G f)
    {d u v : V} (huv : u≠ v) (hu : u≠ d) (hv : v≠ d) (hd : ¬G.Adj u d)
    {S : Finset V} (huS : u∉S) (hvS : v∉S) :
    delta (fun T => f (T.erase d)) u v S=delta f u v S := by
  rw [delta_erase_function d u v hu hv]
  rw [delta_commonNeighbors hn hG huv (by simpa [hu] using huS) (by simpa [hv] using hvS),
    delta_commonNeighbors hn hG huv huS hvS]
  have he : S.erase d∩commonNeighbors G u v=S∩commonNeighbors G u v := by
    ext w
    simp only [mem_inter,mem_erase]
    constructor
    · exact fun h => ⟨h.1.2,h.2⟩
    · intro h
      refine ⟨⟨?_,h.1⟩,h.2⟩
      intro hwd
      subst w
      exact hd ((mem_commonNeighbors G u v d).mp h.2).1
  rw [he]

end VertexDeletion
end GraphicalZonotopes

end
end
end BundlePart251

section BundlePart252
/- Source: Papers/GraphicalZonotopes/BooleanSliceIntersection.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace BooleanFourier
open Finset
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem faceFunction_injective : Function.Injective (faceFunction (I := I)) := by
  intro G H he
  funext v
  have hv : (1+G v)/2=(1+H v)/2 := by
    simpa [faceFunction,phase,character,spin] using
      congrFun he ((fun _ => false),v)
  linarith

/-- Two distinct Boolean functions cannot span the same nonzero real ray
or line. This elementary fact is applied to literal elemental-row slices. -/
theorem eq_zero_of_two_boolean_lines {X : Type*} {f g p : X → ℝ}
    (hf : ∀ x,f x=0 ∨ f x=1) (hg : ∀ x,g x=0 ∨ g x=1)
    (hfg : f≠ g) (hp : ∃ c : ℝ,p=c • f) (hq : ∃ d : ℝ,p=d • g) : p=0 := by
  obtain ⟨c,hc⟩ := hp
  obtain ⟨d,hd⟩ := hq
  by_cases hp0 : p=0
  · exact hp0
  have hc0 : c≠0 := by
    intro h
    apply hp0
    simpa [h] using hc
  have hf0 : f≠0 := by
    intro h
    apply hp0
    simpa [h] using hc
  obtain ⟨x,hx⟩ : ∃ x,f x=1 := by
    by_contra! hn
    apply hf0
    funext x
    exact (hf x).resolve_right (hn x)
  have he : c • f=d • g := hc.symm.trans hd
  have hx' := congrFun he x
  simp only [Pi.smul_apply,smul_eq_mul,hx,mul_one] at hx'
  have hcd : c=d := by
    rcases hg x with hgx | hgx
    · rw [hgx,mul_zero] at hx'
      exact False.elim (hc0 hx')
    · simpa only [hgx,mul_one] using hx'
  apply False.elim
  apply hfg
  funext y
  have hy := congrFun he y
  simp only [Pi.smul_apply,smul_eq_mul,← hcd] at hy
  exact mul_left_cancel₀ hc0 hy

/-- The two-slice elimination used in Corollaries9.10 and9.11: the same
tensor polynomial satisfying both complete zero sets must vanish. -/
theorem boolean_slice_intersection [Nonempty I] {G H : Cube I → ℝ}
    (hG : ∀ v,G v=1 ∨ G v= -1) (hH : ∀ v,H v=1 ∨ H v= -1)
    (hsepG : Nonseparable G) (hsepH : Nonseparable H) (hGH : G≠ H)
    (p : (Cube I × Cube I) → ℝ) (hp : p∈tensorSpace)
    (hzeroG : ∀ uv,faceFunction G uv=0 → p uv=0)
    (hzeroH : ∀ uv,faceFunction H uv=0 → p uv=0) : p=0 := by
  exact eq_zero_of_two_boolean_lines (faceFunction_boolean hG) (faceFunction_boolean hH)
    (fun h => hGH (faceFunction_injective h))
    ((boolean_face_line hG hsepG p hp).mp hzeroG)
    ((boolean_face_line hH hsepH p hp).mp hzeroH)

/-- Multiplication by the parity character is nonconstant in every positive
number of variables, even when accompanied by an arbitrary constant sign. -/
theorem ne_parity_multiple [Nonempty I] {G : Cube I → ℝ}
    (hG : ∀ v,G v≠0) (c : ℝ) : G≠ fun v => c*character univ v*G v := by
  intro he
  have h0 := congrFun he (vertexOfSet ∅)
  rw [character_vertex_empty,mul_one] at h0
  have hc : c=1 := by
    apply (mul_right_cancel₀ (hG (vertexOfSet ∅)))
    simpa only [one_mul] using h0.symm
  obtain ⟨i⟩ := ‹Nonempty I›
  have h1 := congrFun he (vertexOfSet {i})
  rw [hc,one_mul,character_vertex_singleton,if_pos (mem_univ i)] at h1
  have hz : G (vertexOfSet {i})=0 := by linarith
  exact hG _ hz

end BooleanFourier
end GraphicalZonotopes

end
end
end BundlePart252

section BundlePart253
/- Source: Papers/GraphicalZonotopes/BooleanSlicing.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace BooleanFourier
open Finset
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev DeletedIndex (a : I) := {i : I // i≠ a}

def extendCube (a : I) (b : Bool) (v : Cube (DeletedIndex a)) : Cube I :=
  fun i => if h : i=a then b else v ⟨i,h⟩

@[simp] theorem extendCube_at (a : I) (b : Bool) (v : Cube (DeletedIndex a)) :
    extendCube a b v a=b := by simp [extendCube]

@[simp] theorem extendCube_other (a : I) (b : Bool) (v : Cube (DeletedIndex a))
    (i : DeletedIndex a) : extendCube a b v i=v i := by simp [extendCube,i.2]

theorem prod_split_deleted (a : I) (f : I → ℝ) :
    (∏ i,f i)=f a*∏ i : DeletedIndex a,f i := by
  rw [← mul_prod_erase univ f (mem_univ a)]
  rw [prod_subtype (p := fun i : I => i≠ a) (univ.erase a) (by simp) f]

def deletedSet (a : I) (L : Finset I) : Finset (DeletedIndex a) :=
  univ.filter fun i => i.1∈L

@[simp] theorem mem_deletedSet (a : I) (L : Finset I) (i : DeletedIndex a) :
    i∈deletedSet a L ↔ i.1∈L := by simp [deletedSet]

@[simp] theorem deletedSet_univ (a : I) : deletedSet a univ=univ := by
  ext i
  simp

theorem character_extendCube (a : I) (b : Bool) (v : Cube (DeletedIndex a)) (L : Finset I) :
    character L (extendCube a b v)=
      (if a∈L then spin b else 1)*character (deletedSet a L) v := by
  unfold character
  rw [prod_split_deleted a]
  simp only [extendCube_at,extendCube_other,mem_deletedSet]

theorem trueSet_extendCube_false (a : I) (v : Cube (DeletedIndex a)) :
    trueSet (extendCube a false v)=(trueSet v).map (Function.Embedding.subtype _) := by
  ext i
  by_cases hi : i=a
  · subst i
    simp [trueSet]
  · simp only [trueSet,mem_filter,mem_univ,true_and,mem_map]
    constructor
    · intro h
      exact ⟨⟨i,hi⟩,by simpa [extendCube,hi] using h,rfl⟩
    · rintro ⟨j,hj,rfl⟩
      simpa using hj

theorem trueSet_extendCube_true (a : I) (v : Cube (DeletedIndex a)) :
    trueSet (extendCube a true v)=insert a ((trueSet v).map (Function.Embedding.subtype _)) := by
  ext i
  by_cases hi : i=a
  · subst i
    simp [trueSet]
  · simp only [trueSet,mem_filter,mem_univ,true_and,mem_insert,hi,false_or,mem_map]
    constructor
    · intro h
      exact ⟨⟨i,hi⟩,by simpa [extendCube,hi] using h,rfl⟩
    · rintro ⟨j,hj,rfl⟩
      simpa using hj

@[simp] theorem trueSet_extendCube_false_card (a : I) (v : Cube (DeletedIndex a)) :
    (trueSet (extendCube a false v)).card=(trueSet v).card := by
  rw [trueSet_extendCube_false,card_map]

@[simp] theorem trueSet_extendCube_true_card (a : I) (v : Cube (DeletedIndex a)) :
    (trueSet (extendCube a true v)).card=(trueSet v).card+1 := by
  rw [trueSet_extendCube_true,card_insert_of_notMem,card_map]
  simp

theorem completePhase_extendCube_false (a : I) (c : ℝ) (L : Finset I)
    (v : Cube (DeletedIndex a)) :
    completePhase c L (extendCube a false v)=completePhase c (deletedSet a L) v := by
  simp [completePhase,character_extendCube,spin]

theorem completePhase_extendCube_true (a : I) (c : ℝ) (L : Finset I)
    (v : Cube (DeletedIndex a)) :
    completePhase c L (extendCube a true v)=
      (if a∈L then -1 else 1)*character univ v*completePhase c (deletedSet a L) v := by
  simp only [completePhase,trueSet_extendCube_true_card,character_extendCube,spin,ite_true]
  have hp : (-1 : ℝ)^((trueSet v).card+1).choose 2=
      (-1 : ℝ)^((trueSet v).card.choose 2)*(-1 : ℝ)^((trueSet v).card) := by
    simpa [QuadraticSign.triangle,QuadraticSign.parity] using
      QuadraticSign.triangle_succ (trueSet v).card
  rw [hp,DoubledParts.character_univ_parity]
  change _=(if a∈L then -1 else 1)*(-1 : ℝ)^((trueSet v).card)*_
  ring

def slicePhase (a : I) (c : ℝ) (L : Finset I) (b : Bool) : Cube (DeletedIndex a) → ℝ :=
  if b then completePhase (-(if a∈L then -1 else 1)*c) (deletedSet a L)ᶜ
  else completePhase c (deletedSet a L)

/-- Fixing the two original signs of a deleted part to `(b, false)` fixes
both transformed bits to `b`; its two actual slices are again Boolean faces. -/
theorem faceFunction_slice (a : I) (c : ℝ) (L : Finset I) (b : Bool)
    (uv : Cube (DeletedIndex a) × Cube (DeletedIndex a)) :
    faceFunction (completePhase c L)
        (extendCube a b uv.1,extendCube a b uv.2)=faceFunction (slicePhase a c L b) uv := by
  cases b
  · simp [faceFunction,phase,character_extendCube,completePhase_extendCube_false,slicePhase,spin]
  · rw [faceFunction,phase,character_extendCube,deletedSet_univ,
      completePhase_extendCube_true]
    simp only [mem_univ,ite_true,spin]
    rw [faceFunction,phase]
    simp only [slicePhase,ite_true]
    simp only [completePhase]
    rw [← character_compl]
    ring

theorem slicePhase_isSign (a : I) {c : ℝ} (hc : c=1 ∨ c= -1) (L : Finset I)
    (b : Bool) (v : Cube (DeletedIndex a)) :
    slicePhase a c L b v=1 ∨ slicePhase a c L b v= -1 := by
  cases b
  · exact completePhase_isSign hc _ _
  · apply completePhase_isSign
    rcases hc with rfl | rfl <;> split_ifs <;> norm_num

theorem slicePhase_nonseparable (a : I) {c : ℝ} (hc : c≠0) (L : Finset I) (b : Bool) :
    Nonseparable (slicePhase a c L b) := by
  cases b
  · exact completePhase_nonseparable hc _
  · apply completePhase_nonseparable
    apply mul_ne_zero _ hc
    split_ifs <;> norm_num

theorem slicePhase_distinct (a : I) [Nonempty (DeletedIndex a)] {c : ℝ}
    (hc : c≠0) (L : Finset I) : slicePhase a c L false≠ slicePhase a c L true := by
  have he : slicePhase a c L true=(fun v =>
      -(if a∈L then -1 else 1)*character univ v*completePhase c (deletedSet a L) v) := by
    funext v
    simp only [slicePhase,ite_true]
    simp only [completePhase]
    rw [← character_compl]
    ring
  rw [he]
  exact ne_parity_multiple (completePhase_ne_zero hc _) _

/-- Evaluation at arbitrary fixed values of the removed transformed bits
preserves the exact tensor space on the remaining coordinates. -/
theorem tensorSpace_slice (a : I) (b c : Bool) {p : (Cube I × Cube I) → ℝ}
    (hp : p∈tensorSpace) :
    (fun uv : Cube (DeletedIndex a) × Cube (DeletedIndex a) =>
      p (extendCube a b uv.1,extendCube a c uv.2))∈tensorSpace := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨s,rfl⟩ := hp
    let k : ℝ := match s a with
      | none => 1
      | some false => spin b
      | some true => spin b*spin c
    have ht : tensorMonomial (fun i : DeletedIndex a => s i)∈tensorSpace :=
      Submodule.subset_span ⟨_,rfl⟩
    convert (tensorSpace (I := DeletedIndex a)).smul_mem k ht using 1
    funext uv
    simp only [tensorMonomial,Pi.smul_apply,smul_eq_mul]
    rw [prod_split_deleted a]
    simp only [extendCube_at,extendCube_other]
    rfl
  | zero =>
    exact (tensorSpace (I := DeletedIndex a)).zero_mem
  | add p q hp hq ihp ihq =>
    exact (tensorSpace (I := DeletedIndex a)).add_mem ihp ihq
  | smul r p hp ih =>
    exact (tensorSpace (I := DeletedIndex a)).smul_mem r ih

end BooleanFourier
end GraphicalZonotopes

end
end
end BundlePart253

section BundlePart254
/- Source: Papers/GraphicalZonotopes/DoubledRestrictedLines.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset BooleanFourier
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Only the contexts in the actual remaining-part cube are needed for one
row-line argument; graphicality itself is an independently proved premise. -/
theorem graphical_row_line_of_profile {z f : SetFunction (I×Fin 2)}
    (hzn : TranslationNormalized z) (hzG : Graphical (graph I) z)
    (hfn : TranslationNormalized f) (hfG : Graphical (graph I) f)
    {u v : I×Fin 2} (huv : (graph I).Adj u v) [Nonempty (Remaining u v)]
    (H : Cube (Remaining u v) → ℝ) (hH : ∀ x,H x=1 ∨ H x= -1)
    (hsep : Nonseparable H)
    (hprofile : ∀ uv,delta z u v (edgeContext u v (coordinateChange.symm uv))=faceFunction H uv)
    (hzero : ∀ uv,faceFunction H uv=0 →
      delta f u v (edgeContext u v (coordinateChange.symm uv))=0) :
    ∃ t : ℝ,∀ S : Finset (I×Fin 2),u∉S → v∉S → delta f u v S=t*delta z u v S := by
  let p : (Cube (Remaining u v) × Cube (Remaining u v)) → ℝ :=
    fun uv => delta f u v (edgeContext u v (coordinateChange.symm uv))
  have hp : p∈tensorSpace :=
    graphical_edgeProfile_mem_tensorSpace hfn hfG ((graph I).ne_of_adj huv)
  obtain ⟨t,ht⟩ := (boolean_face_line hH hsep p hp).mp hzero
  refine ⟨t,?_⟩
  intro S hu hv
  let s := bitsOfSubset (remainingPart u v S)
  let uv := coordinateChange s
  have h := congrFun ht uv
  change delta f u v (edgeContext u v (coordinateChange.symm uv))=t*faceFunction H uv at h
  rw [← hprofile] at h
  have he : edgeContext u v (coordinateChange.symm uv)=S∩commonNeighbors (graph I) u v := by
    rw [show coordinateChange.symm uv=s by simp [uv]]
    exact edgeContext_remainingPart u v S
  rw [he] at h
  rw [delta_commonNeighbors hfn hfG ((graph I).ne_of_adj huv) hu hv,
    delta_commonNeighbors hzn hzG ((graph I).ne_of_adj huv) hu hv]
  exact h

theorem same_part_not_mem_edgeContext {a d v : I×Fin 2} (hd : d.1=a.1)
    (s : Cube (Remaining a v) × Cube (Remaining a v)) : d∉edgeContext a v s := by
  intro hm
  obtain ⟨w,hw,he⟩ := mem_map.mp hm
  have hh : w.1.1=a.1 := (congrArg Prod.fst he).trans hd
  exact w.1.2.1 hh

/-- Every edge at the singleton retains exactly its full Boolean-face line
after the other vertex in that part is deleted. The kernel vector is lifted
from the actual retained coordinate space. -/
theorem deletion_incident_row_line (hI : 3≤ Fintype.card I)
    (a d : I×Fin 2) (had : a≠ d) (hpart : d.1=a.1)
    {z : SetFunction (I×Fin 2)} (hzn : TranslationNormalized z)
    (hzG : Graphical (graph I) z)
    (hlocalPhase : ∀ v : AtVertex a,∃ H : Cube (Remaining a v.1) → ℝ,
      (∀ x,H x=1 ∨ H x= -1) ∧ Nonseparable H ∧
      ∀ uv,delta z a v.1 (edgeContext a v.1 (coordinateChange.symm uv))=faceFunction H uv)
    (f : SetFunction (VertexDeletion.Retained d)) (hfn : TranslationNormalized f)
    (hzero : ∀ u v : VertexDeletion.Retained d,u≠ v →
      ∀ S : Finset (VertexDeletion.Retained d),u∉S → v∉S →
      delta (SetFunctionEmbedding.restrict (VertexDeletion.embedding d) z) u v S=0 →
      delta f u v S=0) :
    ∀ v : AtVertex a,∃ t : ℝ,∀ S : Finset (I×Fin 2),a∉S → v.1∉S →
      delta (SetFunctionEmbedding.extend (VertexDeletion.embedding d) f) a v.1 S=
        t*delta z a v.1 S := by
  let e := VertexDeletion.embedding d
  have hfG : Graphical ((graph I).comap e) f := by
    intro u v huv hnon S hu hv
    exact hzero u v huv S hu hv
      (SetFunctionEmbedding.restrict_graphical e hzG u v huv hnon S hu hv)
  have hFn := SetFunctionEmbedding.extend_translationNormalized e hfn
  have hFG := SetFunctionEmbedding.extend_graphical e hfG
  intro v
  letI := remaining_nonempty hI a v.1
  obtain ⟨H,hH,hsep,hprofile⟩ := hlocalPhase v
  apply graphical_row_line_of_profile hzn hzG hFn hFG v.2 H hH hsep hprofile
  intro uv hz
  let S := edgeContext a v.1 (coordinateChange.symm uv)
  have hdS : d∉S := same_part_not_mem_edgeContext hpart _
  have hvd : v.1≠ d := by
    intro he
    exact v.2 ((congrArg Prod.fst he).trans hpart).symm
  let a' : VertexDeletion.Retained d := ⟨a,had⟩
  let v' : VertexDeletion.Retained d := ⟨v.1,hvd⟩
  have hav' : a'≠ v' := fun he => (graph I).ne_of_adj v.2 (congrArg Subtype.val he)
  have haS : a'∉SetFunctionEmbedding.pullSet e S := by
    simpa only [SetFunctionEmbedding.mem_pullSet,e,S,a',VertexDeletion.embedding,Function.Embedding.coe_subtype] using left_not_mem_edgeContext a v.1 _
  have hvS : v'∉SetFunctionEmbedding.pullSet e S := by
    simpa only [SetFunctionEmbedding.mem_pullSet,e,S,v',VertexDeletion.embedding,Function.Embedding.coe_subtype] using right_not_mem_edgeContext a v.1 _
  have hsmall : delta (SetFunctionEmbedding.restrict e z) a' v'
      (SetFunctionEmbedding.pullSet e S)=0 := by
    rw [SetFunctionEmbedding.delta_restrict]
    change delta z a v.1 ((SetFunctionEmbedding.pullSet e S).map e)=0
    rw [VertexDeletion.map_pullSet,erase_eq_of_notMem hdS]
    exact (hprofile uv).trans hz
  have he := hzero a' v' hav' _ haS hvS hsmall
  simpa only [← SetFunctionEmbedding.delta_extend,e,S,a',v',VertexDeletion.embedding,Function.Embedding.coe_subtype] using he

end DoubledParts
end GraphicalZonotopes

end
end
end BundlePart254

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

