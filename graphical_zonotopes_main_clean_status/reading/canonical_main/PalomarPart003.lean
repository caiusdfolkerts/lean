module

public import canonical_main.PalomarPart002
import all canonical_main.PalomarPart002
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

section BundlePart150
/- Source: Papers/GraphicalZonotopes/PureGraphModules.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
variable {H : Type*} [Fintype H] [LinearOrder H]

def partialStarBlocks (a : H) (B : Finset H) : Finset (Finset H) := {{a},B}

theorem partialStarBlocks_family (C : Finset H) {a : H} {B : Finset H}
    (ha : a∈C) (hB : B⊆C) (hne : B.Nonempty) (haB : a∉B) :
    ComplementFamily C (partialStarBlocks a B) := by
  have hnot : ({a} : Finset H)≠ B := by
    intro he
    exact haB (he ▸ mem_singleton_self a)
  refine ⟨?_,?_,?_,?_⟩
  · simp only [partialStarBlocks,card_pair hnot,le_refl]
  · intro D hD
    simp only [partialStarBlocks,mem_insert,mem_singleton] at hD
    rcases hD with rfl | rfl
    · exact singleton_subset_iff.mpr ha
    · exact hB
  · intro D hD
    simp only [partialStarBlocks,mem_insert,mem_singleton] at hD
    rcases hD with rfl | rfl
    · exact singleton_nonempty a
    · exact hne
  · intro D hD E hE hDE
    simp only [partialStarBlocks,mem_insert,mem_singleton] at hD hE
    rcases hD with rfl | rfl <;> rcases hE with rfl | rfl
    · exact False.elim (hDE rfl)
    · exact disjoint_singleton_left.mpr haB
    · exact disjoint_singleton_right.mpr haB
    · exact False.elim (hDE rfl)

def StarPair (a : H) (B : Finset H) (u v : H) : Prop :=
  (u=a ∧ v∈B) ∨ (v=a ∧ u∈B)

instance (a : H) (B : Finset H) (u v : H) : Decidable (StarPair a B u v) :=
  inferInstanceAs (Decidable ((u=a ∧ v∈B) ∨ (v=a ∧ u∈B)))

theorem crosses_partialStarBlocks {a : H} {B : Finset H} (haB : a∉B)
    (u v : H) : Crosses (partialStarBlocks a B) u v ↔ StarPair a B u v := by
  have hnot : ({a} : Finset H)≠ B := by
    intro he
    exact haB (he ▸ mem_singleton_self a)
  constructor
  · rintro ⟨D,hD,E,hE,hDE,hu,hv⟩
    simp only [partialStarBlocks,mem_insert,mem_singleton] at hD hE
    rcases hD with rfl | rfl <;> rcases hE with rfl | rfl
    · exact False.elim (hDE rfl)
    · exact Or.inl ⟨mem_singleton.mp hu,hv⟩
    · exact Or.inr ⟨mem_singleton.mp hv,hu⟩
    · exact False.elim (hDE rfl)
  · rintro (⟨hu,hv⟩ | ⟨hv,hu⟩)
    · exact ⟨{a},by simp [partialStarBlocks],B,by simp [partialStarBlocks],
        hnot,mem_singleton.mpr hu,hv⟩
    · exact ⟨B,by simp [partialStarBlocks],{a},by simp [partialStarBlocks],
        hnot.symm,hu,mem_singleton.mpr hv⟩

/-- The two-minterm function used for every partial-star column in Lemma7.7. -/
def partialStarModule (C : Finset H) (a : H) (B : Finset H) : SetFunction H :=
  complementModule C (partialStarBlocks a B)

theorem partialStarModule_properties (C : Finset H) {a : H} {B : Finset H}
    (ha : a∈C) (hB : B⊆C) (hne : B.Nonempty) (haB : a∉B) :
    IsMonotoneBoolean (partialStarModule C a B) ∧
    (∀ i∈C,Essential (partialStarModule C a B) i) ∧
    (∀ i,i∉C → ∀ X,partialStarModule C a B (insert i X)=partialStarModule C a B X) ∧
    rowLowerEquiv.symm (responseVector (partialStarModule C a B))=
      fun r : HubResponseRow H =>
        if rowClique r=C ∧ StarPair a B r.1.1.1 r.1.1.2 then 1 else 0 := by
  have hf:=partialStarBlocks_family C ha hB hne haB
  refine ⟨hf.module_boolean,fun i hi => hf.essential hi,?_,?_⟩
  · exact fun i hi X => complementModule_ignores_outside C _ hi X
  · rw [partialStarModule,complementModule_response_coefficients hf]
    funext r
    simp only [crosses_partialStarBlocks haB]

def cliqueBlocks (U : Finset H) : Finset (Finset H) := U.image singleton

theorem cliqueBlocks_family (C U : Finset H) (hU : U⊆C) (hcard : 2≤ U.card) :
    ComplementFamily C (cliqueBlocks U) := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [cliqueBlocks,card_image_of_injective _ singleton_injective] using hcard
  · intro B hB
    obtain ⟨i,hi,rfl⟩:=mem_image.mp hB
    exact singleton_subset_iff.mpr (hU hi)
  · intro B hB
    obtain ⟨i,hi,rfl⟩:=mem_image.mp hB
    exact singleton_nonempty i
  · intro A hA B hB hAB
    obtain ⟨i,hi,rfl⟩:=mem_image.mp hA
    obtain ⟨j,hj,rfl⟩:=mem_image.mp hB
    apply disjoint_singleton_left.mpr
    intro h
    have he : i=j:=mem_singleton.mp h
    exact hAB (congrArg singleton he)

theorem crosses_cliqueBlocks (U : Finset H) (u v : H) :
    Crosses (cliqueBlocks U) u v ↔ u∈U ∧ v∈U ∧ u≠ v := by
  constructor
  · rintro ⟨A,hA,B,hB,hAB,hu,hv⟩
    obtain ⟨i,hi,rfl⟩:=mem_image.mp hA
    obtain ⟨j,hj,rfl⟩:=mem_image.mp hB
    have hui : u=i:=mem_singleton.mp hu
    have hvj : v=j:=mem_singleton.mp hv
    refine ⟨hui.symm ▸ hi,hvj.symm ▸ hj,?_⟩
    intro huv
    exact hAB (congrArg singleton (hui.symm.trans (huv.trans hvj)))
  · rintro ⟨hu,hv,huv⟩
    exact ⟨{u},mem_image.mpr ⟨u,hu,rfl⟩,
      {v},mem_image.mpr ⟨v,hv,rfl⟩,
      fun he => huv (singleton_injective he),mem_singleton_self _,mem_singleton_self _⟩

/-- The disjunction of the complements of the singleton vertices of `U`. -/
def cliqueModule (C U : Finset H) : SetFunction H :=
  complementModule C (cliqueBlocks U)

theorem cliqueModule_properties (C U : Finset H) (hU : U⊆C) (hcard : 2≤ U.card) :
    IsMonotoneBoolean (cliqueModule C U) ∧
    (∀ i∈C,Essential (cliqueModule C U) i) ∧
    (∀ i,i∉C → ∀ X,cliqueModule C U (insert i X)=cliqueModule C U X) ∧
    rowLowerEquiv.symm (responseVector (cliqueModule C U))=
      fun r : HubResponseRow H =>
        if rowClique r=C ∧ r.1.1.1∈U ∧ r.1.1.2∈U then 1 else 0 := by
  have hf:=cliqueBlocks_family C U hU hcard
  refine ⟨hf.module_boolean,fun i hi => hf.essential hi,?_,?_⟩
  · exact fun i hi X => complementModule_ignores_outside C _ hi X
  · rw [cliqueModule,complementModule_response_coefficients hf]
    funext r
    rw [crosses_cliqueBlocks]
    simp [ne_of_lt r.1.2.1]

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart150

section BundlePart151
/- Source: Papers/GraphicalZonotopes/FiniteSplitting.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {E : Type*} [DecidableEq E]

/-- A finite family whose nonsingleton members can be split into two members
admits every intermediate number of disjoint parts. The statement records
actual partitions; the later pure-response argument supplies their columns. -/
theorem partition_every_size_of_splitting (P : Finset E → Prop)
    (hsplit : ∀ A,P A → 2≤ A.card →
      ∃ B D : Finset E,B.Nonempty ∧ D.Nonempty ∧ Disjoint B D ∧
        B∪D=A ∧ P B ∧ P D)
    {A : Finset E} (hA : A.Nonempty) (hPA : P A) :
    ∀ k,1≤ k → k≤ A.card →
      ∃ Q : Finpartition A,Q.parts.card=k ∧ ∀ B∈Q.parts,P B := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
    intro hk hkA
    by_cases hk0 : k=0
    · subst k
      refine ⟨Finpartition.indiscrete hA.ne_empty,?_,?_⟩
      · rfl
      · intro B hB
        have he : B=A:=mem_singleton.mp hB
        exact he.symm ▸ hPA
    · obtain ⟨Q,hQcard,hQP⟩:=ih (by omega) (by omega)
      have hlarge : ∃ B∈Q.parts,2≤ B.card := by
        by_contra hn
        have hsingle : ∀ B∈Q.parts,B.card=1 := by
          intro B hB
          have hlt : B.card<2:=Nat.lt_of_not_ge (fun h => hn ⟨B,hB,h⟩)
          have hpos : 0< B.card:=card_pos.mpr (nonempty_iff_ne_empty.mpr (Q.ne_bot hB))
          omega
        have hsum : (∑ B∈Q.parts,B.card)=Q.parts.card := by
          calc
            _ = ∑ _B∈Q.parts,1 := sum_congr rfl hsingle
            _ = _ := by simp
        rw [Q.sum_card_parts,hQcard] at hsum
        omega
      obtain ⟨B,hB,hBcard⟩:=hlarge
      obtain ⟨D,F,hD,hF,hDF,hunion,hPD,hPF⟩:=hsplit B (hQP B hB) hBcard
      let splitPart : Finpartition B :=
        (Finpartition.indiscrete hD.ne_empty).extend hF.ne_empty hDF hunion
      have hsplitCard : splitPart.parts.card=2 := by
        rw [Finpartition.card_extend]
        rfl
      have hsplitP : ∀ C∈splitPart.parts,P C := by
        intro C hC
        change C∈insert F {D} at hC
        rcases mem_insert.mp hC with he | he
        · exact he.symm ▸ hPF
        · exact (mem_singleton.mp he).symm ▸ hPD
      let pieces : ∀ C∈Q.parts,Finpartition C := fun C hC =>
        if he : C=B then he.symm ▸ splitPart else Finpartition.indiscrete (Q.ne_bot hC)
      have hpieceCard : ∀ C (hC : C∈Q.parts),(pieces C hC).parts.card=
          1+(if C=B then 1 else 0) := by
        intro C hC
        by_cases he : C=B
        · subst C
          simp [pieces,hsplitCard]
        · simp only [pieces,dif_neg he,if_neg he,Finpartition.indiscrete,card_singleton,add_zero]
      have hpieceP : ∀ C (hC : C∈Q.parts),∀ D∈(pieces C hC).parts,P D := by
        intro C hC D hD
        by_cases he : C=B
        · subst C
          simp only [pieces,dif_pos rfl] at hD
          exact hsplitP D hD
        · simp only [pieces,dif_neg he,Finpartition.indiscrete,mem_singleton] at hD
          exact hD.symm ▸ hQP C hC
      refine ⟨Q.bind pieces,?_,?_⟩
      · rw [Finpartition.card_bind]
        simp_rw [hpieceCard]
        rw [sum_add_distrib]
        have hcount : (∑ C∈Q.parts.attach,if C.1=B then (1 : ℕ) else 0)=1 := by
          have he : ∀ C : Q.parts,C.1=B ↔ C=⟨B,hB⟩ :=
            fun C => ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩
          simp_rw [he]
          simp
        rw [hcount]
        simp only [sum_const,card_attach,nsmul_eq_mul,mul_one,hQcard,Nat.succ_eq_add_one]
        rfl
      · intro C hC
        obtain ⟨D,hD,hCD⟩:=Finpartition.mem_bind.mp hC
        exact hpieceP D hD C hCD

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart151

section BundlePart152
/- Source: Papers/GraphicalZonotopes/PureColumnRealization.lean -/






@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H : Type*} [Fintype H] [LinearOrder H]

/-- A column is realized by an actual monotone Boolean function. Its entire
essential-variable set is recorded, as is its class in the full response
quotient. -/
def PureRealizable (C : Finset H) (x : PairIn C → ℝ) : Prop :=
  ∃ F : SetFunction H, IsMonotoneBoolean F ∧
    (∀ a ∈ C, Essential F a) ∧
    (∀ a, a ∉ C → ∀ X, F (insert a X) = F X) ∧
    responseClass F = blockClass C x

def pairIndicator {C : Finset H} (A : Finset (PairIn C)) : PairIn C → ℝ :=
  fun e => if e ∈ A then 1 else 0

def starPairs (C : Finset H) (a : H) (B : Finset H) : Finset (PairIn C) :=
  univ.filter (fun e => StarPair a B e.1.1.1 e.1.1.2)

def cliquePairs (C U : Finset H) : Finset (PairIn C) :=
  univ.filter (fun e => e.1.1.1 ∈ U ∧ e.1.1.2 ∈ U)

@[simp] theorem mem_starPairs {C : Finset H} {a : H} {B : Finset H} {e : PairIn C} :
    e ∈ starPairs C a B ↔ StarPair a B e.1.1.1 e.1.1.2 := by
  simp [starPairs]

@[simp] theorem mem_cliquePairs {C U : Finset H} {e : PairIn C} :
    e ∈ cliquePairs C U ↔ e.1.1.1 ∈ U ∧ e.1.1.2 ∈ U := by
  simp [cliquePairs]

theorem pureRealizable_star (C : Finset H) {a : H} {B : Finset H}
    (ha : a ∈ C) (hB : B ⊆ C) (hne : B.Nonempty) (haB : a ∉ B) :
    PureRealizable C (pairIndicator (starPairs C a B)) := by
  obtain ⟨hf,he,hi,hr⟩ := partialStarModule_properties C ha hB hne haB
  refine ⟨partialStarModule C a B,hf,he,hi,?_⟩
  rw [responseClass_eq_coefficientClass,hr]
  apply congrArg coefficientClass
  funext r
  change (if rowClique r=C ∧ StarPair a B r.1.1.1 r.1.1.2 then 1 else 0) =
    if h : rowClique r=C then pairIndicator (starPairs C a B) (pairAtRow C r h) else 0
  by_cases h : rowClique r=C <;> simp [h,pairIndicator,pairAtRow]

theorem pureRealizable_clique (C U : Finset H) (hU : U ⊆ C) (hcard : 2 ≤ U.card) :
    PureRealizable C (pairIndicator (cliquePairs C U)) := by
  obtain ⟨hf,he,hi,hr⟩ := cliqueModule_properties C U hU hcard
  refine ⟨cliqueModule C U,hf,he,hi,?_⟩
  rw [responseClass_eq_coefficientClass,hr]
  apply congrArg coefficientClass
  funext r
  change (if rowClique r=C ∧ r.1.1.1∈U ∧ r.1.1.2∈U then 1 else 0) =
    if h : rowClique r=C then pairIndicator (cliquePairs C U) (pairAtRow C r h) else 0
  by_cases h : rowClique r=C <;> simp [h,pairIndicator,pairAtRow]

theorem blockClass_singleton (C : Finset H) (e : PairIn C) :
    blockClass C (pairIndicator {e}) = pureCoordinate C e.1.1.1 e.1.1.2 := by
  apply congrArg coefficientClass
  funext r
  change (if h : rowClique r=C then pairIndicator {e} (pairAtRow C r h) else 0) =
    if rowClique r=C ∧ r.1.1.1=e.1.1.1 ∧ r.1.1.2=e.1.1.2 then 1 else 0
  by_cases h : rowClique r=C
  · have he : pairAtRow C r h=e ↔ r.1.1.1=e.1.1.1 ∧ r.1.1.2=e.1.1.2 := by
      constructor
      · intro he
        exact ⟨congrArg (fun t : PairIn C => t.1.1.1) he,
          congrArg (fun t : PairIn C => t.1.1.2) he⟩
      · rintro ⟨hu,hv⟩
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext hu hv
    simp only [h,dite_true,pairIndicator,mem_singleton,he,true_and]
  · simp only [h,dite_false,false_and,ite_false]

theorem pureRealizable_pair (C : Finset H) (e : PairIn C) :
    PureRealizable C (pairIndicator {e}) := by
  refine ⟨positivePairModule C e.1.1.1 e.1.1.2,
    (positivePairBlocks_family C e.2.1 e.2.2 (ne_of_lt e.1.2.1)).module_boolean,?_,?_,?_⟩
  · exact fun a ha => positivePairModule_essential C e.2.1 e.2.2 (ne_of_lt e.1.2.1) ha
  · exact fun a ha X => complementModule_ignores_outside C _ ha X
  · rw [positivePairModule_class C e.2.1 e.2.2 e.1.2.1,blockClass_singleton]

theorem pureRealizable_negative_pair (C : Finset H) (hC : 3 ≤ C.card) (e : PairIn C) :
    PureRealizable C (-pairIndicator {e}) := by
  refine ⟨negativePairModule C e.1.1.1 e.1.1.2,
    (negativePairBlocks_family C hC e.2.1 e.2.2 (ne_of_lt e.1.2.1)).module_boolean,?_,?_,?_⟩
  · exact fun a ha => negativePairModule_essential C hC e.2.1 e.2.2 (ne_of_lt e.1.2.1) ha
  · exact fun a ha X => complementModule_ignores_outside C _ ha X
  · rw [negativePairModule_class C hC e.2.1 e.2.2 e.1.2.1,map_neg,blockClass_singleton]

/-- Indicator columns of the nonempty parts of a genuine finite partition
are independent. This elementary statement is used before quotienting. -/
theorem linearIndependent_partition_indicators {E : Type*} [DecidableEq E]
    {A : Finset E} (Q : Finpartition A) :
    LinearIndependent ℝ (fun B : Q.parts => fun e : E => if e∈B.1 then (1 : ℝ) else 0) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc B
  obtain ⟨e,he⟩ := nonempty_iff_ne_empty.mpr (Q.ne_bot B.2)
  have hmem : ∀ D : Q.parts, e∈D.1 ↔ D=B := by
    intro D
    constructor
    · intro hD
      apply Subtype.ext
      by_contra hDB
      exact Finset.disjoint_left.mp (Q.disjoint D.2 B.2 hDB) hD he
    · intro hD
      exact hD.symm ▸ he
  have hv := congrFun hc e
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hv
  simp_rw [hmem] at hv
  simpa using hv

theorem sum_partition_indicators {E : Type*} [DecidableEq E]
    {A : Finset E} (Q : Finpartition A) (e : E) :
    (∑ B : Q.parts,if e∈B.1 then (1 : ℝ) else 0) = if e∈A then 1 else 0 := by
  classical
  by_cases he : e∈A
  · obtain ⟨B,hB,heB⟩ := Q.exists_mem he
    have hmem : ∀ D : Q.parts, e∈D.1 ↔ D=⟨B,hB⟩ := by
      intro D
      constructor
      · intro hD
        apply Subtype.ext
        by_contra hDB
        exact Finset.disjoint_left.mp (Q.disjoint D.2 hB hDB) hD heB
      · intro hD
        exact hD.symm ▸ heB
    simp_rw [hmem]
    simp [he]
  · have hmem : ∀ D : Q.parts, e∉D.1 := fun D hD => he ((Q.le D.2) hD)
    simp [hmem,he]

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart152

section BundlePart153
/- Source: Papers/GraphicalZonotopes/PureEdgePartitions.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H : Type*} [Fintype H] [LinearOrder H]

def orderedPair (C : Finset H) (a b : H) (hab : a< b) (ha : a∈C) (hb : b∈C) :
    PairIn C := ⟨⟨(a,b),hab,(SimpleGraph.top_adj _ _).mpr (ne_of_lt hab)⟩,ha,hb⟩

def pairOfNe (C : Finset H) (a b : H) (hab : a≠ b) (ha : a∈C) (hb : b∈C) : PairIn C :=
  if h : a< b then orderedPair C a b h ha hb
  else orderedPair C b a (lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hab)) hb ha

theorem pairOfNe_endpoints (C : Finset H) (a b : H) (hab : a≠ b)
    (ha : a∈C) (hb : b∈C) :
    ((pairOfNe C a b hab ha hb).1.1.1=a ∧ (pairOfNe C a b hab ha hb).1.1.2=b) ∨
    ((pairOfNe C a b hab ha hb).1.1.1=b ∧ (pairOfNe C a b hab ha hb).1.1.2=a) := by
  unfold pairOfNe
  split <;> simp [orderedPair]

theorem starPairs_nonempty (C : Finset H) {a : H} {B : Finset H}
    (ha : a∈C) (hB : B⊆C) (haB : a∉B) (hne : B.Nonempty) :
    (starPairs C a B).Nonempty := by
  obtain ⟨b,hb⟩ := hne
  have hab : a≠ b := fun h => haB (h.symm ▸ hb)
  refine ⟨pairOfNe C a b hab ha (hB hb),?_⟩
  rw [mem_starPairs]
  rcases pairOfNe_endpoints C a b hab ha (hB hb) with h | h <;>
    simp [StarPair,h.1,h.2,hb]

def cliquePairsEquiv (C U : Finset H) (hU : U⊆C) :
    ↥(cliquePairs C U) ≃ ↥((U ×ˢ U).filter (fun p : H×H => p.1< p.2)) where
  toFun e := ⟨e.1.1.1,mem_filter.mpr ⟨mem_product.mpr
    (mem_cliquePairs.mp e.2),e.1.1.2.1⟩⟩
  invFun p := ⟨orderedPair C p.1.1 p.1.2 (mem_filter.mp p.2).2
    (hU (mem_product.mp (mem_filter.mp p.2).1).1)
    (hU (mem_product.mp (mem_filter.mp p.2).1).2),
    mem_cliquePairs.mpr (mem_product.mp (mem_filter.mp p.2).1)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem cliquePairs_card (C U : Finset H) (hU : U⊆C) :
    (cliquePairs C U).card=U.card.choose 2 := by
  have h := Fintype.card_congr (cliquePairsEquiv C U hU)
  simpa only [Fintype.card_coe,Finset.card_product_filter_lt] using h

theorem cliquePairs_nonempty (C U : Finset H) (hU : U⊆C) (hc : 2≤ U.card) :
    (cliquePairs C U).Nonempty := by
  apply card_pos.mp
  rw [cliquePairs_card C U hU]
  exact Nat.choose_pos hc

theorem cliquePairs_nonempty_iff (C U : Finset H) (hU : U⊆C) :
    (cliquePairs C U).Nonempty ↔ 2≤ U.card := by
  rw [← card_pos,cliquePairs_card C U hU]
  constructor
  · intro h
    exact Nat.choose_ne_zero_iff.mp (ne_of_gt h)
  · exact Nat.choose_pos

theorem starPairs_union (C : Finset H) (a : H) (B D : Finset H) :
    starPairs C a (B∪D)=starPairs C a B∪starPairs C a D := by
  ext e
  simp only [mem_starPairs,StarPair,mem_union]
  tauto

theorem starPairs_disjoint (C : Finset H) (a : H) {B D : Finset H}
    (hBD : Disjoint B D) (haB : a∉B) (haD : a∉D) :
    Disjoint (starPairs C a B) (starPairs C a D) := by
  apply disjoint_left.mpr
  intro e heB heD
  rw [mem_starPairs] at heB heD
  rcases heB with ⟨hu,hv⟩ | ⟨hv,hu⟩ <;>
    rcases heD with ⟨hu',hv'⟩ | ⟨hv',hu'⟩
  · exact disjoint_left.mp hBD hv hv'
  · exact haD (hu ▸ hu')
  · exact haD (hv ▸ hv')
  · exact disjoint_left.mp hBD hu hu'

theorem starPairs_singleton (C : Finset H) {a b : H} (hab : a≠ b)
    (ha : a∈C) (hb : b∈C) :
    starPairs C a {b}={pairOfNe C a b hab ha hb} := by
  ext e
  rw [mem_starPairs,mem_singleton]
  have hends := pairOfNe_endpoints C a b hab ha hb
  constructor
  · intro he
    apply Subtype.ext
    apply Subtype.ext
    rcases he with ⟨hu,hv⟩ | ⟨hv,hu⟩
    · have hv' : e.1.1.2=b := mem_singleton.mp hv
      rcases hends with h | h
      · exact Prod.ext (hu.trans h.1.symm) (hv'.trans h.2.symm)
      · have h1 : a< b := hu ▸ hv' ▸ e.1.2.1
        have h2 : b< a := by simpa only [h.1,h.2] using (pairOfNe C a b hab ha hb).1.2.1
        exact False.elim ((not_lt_of_ge h1.le) h2)
    · have hu' : e.1.1.1=b := mem_singleton.mp hu
      rcases hends with h | h
      · have h1 : b< a := hu' ▸ hv ▸ e.1.2.1
        have h2 : a< b := by simpa only [h.1,h.2] using (pairOfNe C a b hab ha hb).1.2.1
        exact False.elim ((not_lt_of_ge h1.le) h2)
      · exact Prod.ext (hu'.trans h.1.symm) (hv.trans h.2.symm)
  · rintro rfl
    rcases hends with h | h <;> simp [StarPair,h.1,h.2]

theorem starPairs_card (C : Finset H) {a : H} {B : Finset H}
    (ha : a∈C) (hB : B⊆C) (haB : a∉B) :
    (starPairs C a B).card=B.card := by
  induction B using Finset.induction_on with
  | empty => simp [starPairs,StarPair]
  | @insert b B hb ih =>
    have hbC : b∈C := hB (mem_insert_self _ _)
    have hBC : B⊆C := fun x hx => hB (mem_insert_of_mem hx)
    have haB' : a∉B := fun h => haB (mem_insert_of_mem h)
    have hab : a≠ b := fun h => haB (mem_insert.mpr (Or.inl h))
    rw [← singleton_union,starPairs_union,card_union_of_disjoint
      (starPairs_disjoint C a (disjoint_singleton_left.mpr hb)
        (by simpa only [mem_singleton] using hab) haB'),
      starPairs_singleton C hab ha hbC,card_singleton,ih hBC haB']
    simp [card_insert_of_notMem hb,Nat.add_comm]

theorem cliquePairs_split (C U : Finset H) (a : H) (ha : a∈U) :
    cliquePairs C U=starPairs C a (U.erase a)∪cliquePairs C (U.erase a) := by
  ext e
  simp only [mem_cliquePairs,mem_union,mem_starPairs,StarPair,mem_erase]
  have huv : e.1.1.1≠ e.1.1.2 := ne_of_lt e.1.2.1
  constructor
  · rintro ⟨hu,hv⟩
    by_cases hua : e.1.1.1=a
    · exact Or.inl (Or.inl ⟨hua,fun hvA => huv (hua.trans hvA.symm),hv⟩)
    · by_cases hva : e.1.1.2=a
      · exact Or.inl (Or.inr ⟨hva,hua,hu⟩)
      · exact Or.inr ⟨⟨hua,hu⟩,hva,hv⟩
  · rintro ((⟨hua,hva,hv⟩ | ⟨hva,hua,hu⟩) | ⟨⟨hua,hu⟩,hva,hv⟩)
    · exact ⟨hua.symm ▸ ha,hv⟩
    · exact ⟨hu,hva.symm ▸ ha⟩
    · exact ⟨hu,hv⟩

theorem cliquePairs_split_disjoint (C U : Finset H) (a : H) :
    Disjoint (starPairs C a (U.erase a)) (cliquePairs C (U.erase a)) := by
  apply disjoint_left.mpr
  intro e hs hc
  rw [mem_starPairs] at hs
  obtain ⟨hu,hv⟩ := mem_cliquePairs.mp hc
  rcases hs with ⟨he,_⟩ | ⟨he,_⟩
  · exact (mem_erase.mp hu).1 he
  · exact (mem_erase.mp hv).1 he

/-- The allowed pieces are actual partial stars or cliques of pairs. -/
def PureEdgeChunk (C : Finset H) (A : Finset (PairIn C)) : Prop :=
  (∃ a B, a∈C ∧ B⊆C ∧ a∉B ∧ A=starPairs C a B) ∨
  (∃ U, U⊆C ∧ A=cliquePairs C U)

theorem PureEdgeChunk.realizable {C : Finset H} {A : Finset (PairIn C)}
    (hA : PureEdgeChunk C A) (hne : A.Nonempty) : PureRealizable C (pairIndicator A) := by
  rcases hA with ⟨a,B,ha,hB,haB,rfl⟩ | ⟨U,hU,rfl⟩
  · have hb : B.Nonempty := by
      apply card_pos.mp
      rw [← starPairs_card C ha hB haB]
      exact card_pos.mpr hne
    exact pureRealizable_star C ha hB hb haB
  · exact pureRealizable_clique C U hU ((cliquePairs_nonempty_iff C U hU).mp hne)

theorem PureEdgeChunk.split {C : Finset H} {A : Finset (PairIn C)}
    (hA : PureEdgeChunk C A) (hc : 2≤ A.card) :
    ∃ B D : Finset (PairIn C), B.Nonempty ∧ D.Nonempty ∧ Disjoint B D ∧
      B∪D=A ∧ PureEdgeChunk C B ∧ PureEdgeChunk C D := by
  rcases hA with ⟨a,U,ha,hU,haU,rfl⟩ | ⟨U,hU,rfl⟩
  · have hUc : 2≤ U.card := by rwa [starPairs_card C ha hU haU] at hc
    obtain ⟨b,hb⟩ := card_pos.mp (by omega : 0< U.card)
    have hab : a≠ b := fun h => haU (h.symm ▸ hb)
    have hUe : (U.erase b).Nonempty := by
      apply card_pos.mp
      rw [card_erase_of_mem hb]
      omega
    refine ⟨starPairs C a {b},starPairs C a (U.erase b),
      starPairs_nonempty C ha (singleton_subset_iff.mpr (hU hb))
        (by simpa only [mem_singleton] using hab) (singleton_nonempty b),
      starPairs_nonempty C ha (erase_subset _ _ |>.trans hU)
        (fun h => haU (mem_of_mem_erase h)) hUe,
      starPairs_disjoint C a (disjoint_singleton_left.mpr (notMem_erase b U))
        (by simpa only [mem_singleton] using hab) (fun h => haU (mem_of_mem_erase h)),?_,?_,?_⟩
    · rw [← starPairs_union,singleton_union,insert_erase hb]
    · exact Or.inl ⟨a,{b},ha,singleton_subset_iff.mpr (hU hb),
        by simpa only [mem_singleton] using hab,rfl⟩
    · exact Or.inl ⟨a,U.erase b,ha,(erase_subset _ _).trans hU,
        fun h => haU (mem_of_mem_erase h),rfl⟩
  · have hUc : 3≤ U.card := by
      rw [cliquePairs_card C U hU] at hc
      by_contra hn
      have hcases : U.card=0 ∨ U.card=1 ∨ U.card=2 := by omega
      rcases hcases with h | h | h <;> norm_num [h,Nat.choose] at hc
    obtain ⟨a,ha⟩ := card_pos.mp (by omega : 0< U.card)
    have he : 2≤(U.erase a).card := by rw [card_erase_of_mem ha]; omega
    have hsub : U.erase a⊆C := (erase_subset _ _).trans hU
    refine ⟨starPairs C a (U.erase a),cliquePairs C (U.erase a),
      starPairs_nonempty C (hU ha) hsub (notMem_erase _ _) (card_pos.mp (by omega)),
      cliquePairs_nonempty C (U.erase a) hsub he,
      cliquePairs_split_disjoint C U a,(cliquePairs_split C U a ha).symm,?_,?_⟩
    · exact Or.inl ⟨a,U.erase a,hU ha,hsub,notMem_erase _ _,rfl⟩
    · exact Or.inr ⟨U.erase a,hsub,rfl⟩

/-- Every intermediate number of independent pure Boolean columns is
available for a clique or partial-star indicator. -/
theorem pureEdgeChunk_partition (C : Finset H) {A : Finset (PairIn C)}
    (hA : PureEdgeChunk C A) (hne : A.Nonempty) {k : ℕ} (hk : 1≤ k) (hkA : k≤ A.card) :
    ∃ Q : Finpartition A, Q.parts.card=k ∧
      (∀ B : Q.parts, PureRealizable C (pairIndicator B.1)) ∧
      LinearIndependent ℝ (fun B : Q.parts => pairIndicator B.1) ∧
      (∑ B : Q.parts,pairIndicator B.1)=pairIndicator A := by
  obtain ⟨Q,hQc,hQ⟩ := partition_every_size_of_splitting (PureEdgeChunk C)
    (fun A hA hc => hA.split hc) hne hA k hk hkA
  refine ⟨Q,hQc,fun B => (hQ B.1 B.2).realizable (Q.nonempty_of_mem_parts B.2),
    linearIndependent_partition_indicators Q,?_⟩
  funext e
  simpa only [Finset.sum_apply,pairIndicator] using sum_partition_indicators Q e

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart153

section BundlePart154
/- Source: Papers/GraphicalZonotopes/PairColumnRefinement.lean -/







@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators

section Split
variable {J W : Type*} [Fintype J] [DecidableEq J]
variable [AddCommGroup W] [Module ℝ W]

def splitColumnFamily (v : J → W) (j₀ : J) (u : W) : Option J → W
  | none => u
  | some j => if j=j₀ then v j-u else v j

theorem splitColumnFamily_sum (v : J → W) (j₀ : J) (u : W) (c : Option J → ℝ) :
    (∑ j,c j • splitColumnFamily v j₀ u j)=
      (c none-c (some j₀)) • u+∑ j,c (some j) • v j := by
  rw [Fintype.sum_option]
  simp only [splitColumnFamily]
  have he : ∀ j,(if j=j₀ then v j-u else v j)=v j-(if j=j₀ then u else 0) := by
    intro j
    by_cases h : j=j₀ <;> simp [h]
  simp_rw [he,smul_sub]
  rw [sum_sub_distrib]
  have hs : (∑ j,c (some j) • (if j=j₀ then u else 0))=c (some j₀) • u := by
    simp [smul_ite]
  rw [hs,sub_smul]
  abel

theorem splitColumnFamily_independent (v : J → W) (hv : LinearIndependent ℝ v)
    (j₀ : J) (u : W) (hu : u∉Submodule.span ℝ (Set.range v)) :
    LinearIndependent ℝ (splitColumnFamily v j₀ u) := by
  have hi := hv.option hu
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  rw [splitColumnFamily_sum] at hc
  let d : Option J → ℝ := fun j => match j with
    | none => c none-c (some j₀)
    | some j => c (some j)
  have hd : (∑ j : Option J,d j • Option.casesOn' j u v)=0 := by
    rw [Fintype.sum_option]
    exact hc
  have hz := (Fintype.linearIndependent_iff.mp hi) d hd
  cases j with
  | none =>
    have h0 := hz none
    have hj := hz (some j₀)
    change c none-c (some j₀)=0 at h0
    change c (some j₀)=0 at hj
    linarith
  | some j => exact hz (some j)

theorem splitColumnFamily_preserves_sum (v : J → W) (j₀ : J) (u : W) (w : J → ℝ) :
    (∑ j : Option J,(Option.casesOn' j (w j₀) w) • splitColumnFamily v j₀ u j)=
      ∑ j,w j • v j := by
  rw [splitColumnFamily_sum]
  simp

theorem splitColumnFamily_span_mono (v : J → W) (j₀ : J) (u : W) :
    Submodule.span ℝ (Set.range v) ≤
      Submodule.span ℝ (Set.range (splitColumnFamily v j₀ u)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j,rfl⟩
  change v j∈Submodule.span ℝ (Set.range (splitColumnFamily v j₀ u))
  have hu : u∈Submodule.span ℝ (Set.range (splitColumnFamily v j₀ u)) :=
    Submodule.subset_span ⟨none,rfl⟩
  have hj := Submodule.subset_span (R:=ℝ) (s:=Set.range (splitColumnFamily v j₀ u))
    (show splitColumnFamily v j₀ u (some j)∈Set.range (splitColumnFamily v j₀ u) from ⟨some j,rfl⟩)
  change splitColumnFamily v j₀ u (some j)∈Submodule.span ℝ (Set.range (splitColumnFamily v j₀ u)) at hj
  by_cases h : j=j₀
  · have hh : v j-u∈Submodule.span ℝ (Set.range (splitColumnFamily v j₀ u)) := by
      simpa only [splitColumnFamily,ite_eq_left h] using hj
    simpa only [sub_add_cancel] using (Submodule.add_mem _ hh hu)
  · simpa only [splitColumnFamily,ite_eq_right h] using hj

end Split

section PairBasis
variable {H : Type*} [Fintype H] [LinearOrder H]

theorem pairIn_card (C : Finset H) : Fintype.card (PairIn C)=C.card.choose 2 := by
  have hu : cliquePairs C C=univ := by
    ext e
    simp only [mem_cliquePairs,mem_univ,iff_true]
    exact e.2
  have h := cliquePairs_card C C (Subset.refl _)
  rwa [hu,card_univ] at h

theorem reference_pair_columns_independent (C : Finset H) (e₀ : PairIn C) :
    LinearIndependent ℝ (fun e : ↥((univ : Finset (PairIn C)).erase e₀) =>
      blockClass C (pairIndicator {e.1})) := by
  classical
  apply blockClass_linearIndependent_of_reference C e₀
  · rw [Fintype.linearIndependent_iff]
    intro c hc e
    have hv := congrFun hc e.1
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,pairIndicator,mem_singleton,
      Pi.zero_apply] at hv
    have heq : ∀ f : ↥((univ : Finset (PairIn C)).erase e₀),e.1=f.1 ↔ f=e :=
      fun f => ⟨fun h => Subtype.ext h.symm,fun h => congrArg Subtype.val h.symm⟩
    simp_rw [heq] at hv
    simpa using hv
  · intro e
    exact ite_eq_right (by simpa only [mem_singleton] using Ne.symm (mem_erase.mp e.2).1)

/-- Below the full block dimension, some genuine pair column lies outside
any given independent family. The argument counts a proved reference-pair
basis inside the actual response quotient. -/
theorem exists_pair_outside_span (C : Finset H) (e₀ : PairIn C)
    {J : Type*} [Fintype J] (v : J → ResponseQuotient H) (hv : LinearIndependent ℝ v)
    (hcard : Fintype.card J< C.card.choose 2-1) :
    ∃ e : PairIn C,blockClass C (pairIndicator {e})∉Submodule.span ℝ (Set.range v) := by
  classical
  by_contra hn
  have hall : ∀ e : PairIn C,blockClass C (pairIndicator {e})∈Submodule.span ℝ (Set.range v) := by
    intro e
    exact Classical.byContradiction (fun h => hn ⟨e,h⟩)
  let S := Submodule.span ℝ (Set.range v)
  let b : ↥((univ : Finset (PairIn C)).erase e₀) → S :=
    fun e => ⟨blockClass C (pairIndicator {e.1}),hall e.1⟩
  have hi : LinearIndependent ℝ b :=
    LinearIndependent.of_comp S.subtype (reference_pair_columns_independent C e₀)
  have hc := hi.fintype_card_le_finrank
  rw [finrank_span_eq_card hv] at hc
  simp only [Fintype.card_coe,card_erase_of_mem (mem_univ e₀),card_univ,pairIn_card] at hc
  omega

end PairBasis
end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart154

section BundlePart155
/- Source: Papers/GraphicalZonotopes/WeightedStarRefinement.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H : Type*} [Fintype H] [LinearOrder H]

structure StarPiece (C : Finset H) where
  center : H
  leaves : Finset H
  center_mem : center∈C
  leaves_subset : leaves⊆C
  nonempty : leaves.Nonempty
  center_notMem : center∉leaves

def StarPiece.edges {C : Finset H} (P : StarPiece C) : Finset (PairIn C) :=
  starPairs C P.center P.leaves

def StarPiece.vector {C : Finset H} (P : StarPiece C) : PairIn C → ℝ :=
  pairIndicator P.edges

def StarPiece.response {C : Finset H} (P : StarPiece C) : ResponseQuotient H :=
  blockClass C P.vector

theorem StarPiece.realizable {C : Finset H} (P : StarPiece C) : PureRealizable C P.vector :=
  pureRealizable_star C P.center_mem P.leaves_subset P.nonempty P.center_notMem

private theorem pairIndicator_union {C : Finset H} {A B : Finset (PairIn C)}
    (h : Disjoint A B) : pairIndicator (A∪B)=pairIndicator A+pairIndicator B := by
  funext e
  by_cases ha : e∈A <;> by_cases hb : e∈B
  · exact False.elim (disjoint_left.mp h ha hb)
  all_goals simp [pairIndicator,ha,hb]

/-- Splitting off an actual pair preserves the class sum and every covered
pair. Both child columns are actual nonempty partial-star modules. -/
theorem StarPiece.split_at {C : Finset H} (P : StarPiece C) (e : PairIn C)
    (he : e∈P.edges) (hne : P.response≠ blockClass C (pairIndicator {e})) :
    ∃ L R : StarPiece C,L.response=blockClass C (pairIndicator {e}) ∧
      R.response=P.response-blockClass C (pairIndicator {e}) ∧
      L.edges∪R.edges=P.edges := by
  have he' := mem_starPairs.mp he
  have hex : ∃ b∈P.leaves,starPairs C P.center {b}={e} := by
    rcases he' with ⟨hu,hv⟩ | ⟨hv,hu⟩
    · have hne : P.center≠ e.1.1.2 := fun h => P.center_notMem (h.symm ▸ hv)
      have hem : e∈starPairs C P.center {e.1.1.2} := mem_starPairs.mpr (Or.inl ⟨hu,mem_singleton_self _⟩)
      have heq := mem_singleton.mp (starPairs_singleton C hne P.center_mem e.2.2 ▸ hem)
      exact ⟨e.1.1.2,hv,(starPairs_singleton C hne P.center_mem e.2.2).trans
        (congrArg singleton heq.symm)⟩
    · have hne : P.center≠ e.1.1.1 := fun h => P.center_notMem (h.symm ▸ hu)
      have hem : e∈starPairs C P.center {e.1.1.1} := mem_starPairs.mpr (Or.inr ⟨hv,mem_singleton_self _⟩)
      have heq := mem_singleton.mp (starPairs_singleton C hne P.center_mem e.2.1 ▸ hem)
      exact ⟨e.1.1.1,hu,(starPairs_singleton C hne P.center_mem e.2.1).trans
        (congrArg singleton heq.symm)⟩
  obtain ⟨b,hb,hpair⟩ := hex
  have hcb : P.center≠ b := fun h => P.center_notMem (h.symm ▸ hb)
  have herase : (P.leaves.erase b).Nonempty := by
    by_contra hn
    have he0 : P.leaves.erase b=∅ := not_nonempty_iff_eq_empty.mp hn
    rcases (erase_eq_empty_iff P.leaves b).mp he0 with h | h
    · exact P.nonempty.ne_empty h
    · apply hne
      change blockClass C (pairIndicator (starPairs C P.center P.leaves))=_
      rw [h,hpair]
  let L : StarPiece C := ⟨P.center,{b},P.center_mem,singleton_subset_iff.mpr
    (P.leaves_subset hb),singleton_nonempty _,by simpa only [mem_singleton] using hcb⟩
  let R : StarPiece C := ⟨P.center,P.leaves.erase b,P.center_mem,
    (erase_subset _ _).trans P.leaves_subset,herase,
    fun h => P.center_notMem (mem_of_mem_erase h)⟩
  have hL : L.edges={e} := hpair
  have hdis : Disjoint L.edges R.edges := starPairs_disjoint C P.center
    (B:={b}) (D:=P.leaves.erase b) (disjoint_singleton_left.mpr (notMem_erase b P.leaves))
    (by simpa only [mem_singleton] using hcb) (fun h => P.center_notMem (mem_of_mem_erase h))
  have hcover : L.edges∪R.edges=P.edges := by
    change starPairs C P.center {b}∪starPairs C P.center (P.leaves.erase b)=_
    rw [← starPairs_union,singleton_union,insert_erase hb]
    rfl
  have hsum : L.response+R.response=P.response := by
    change blockClass C (pairIndicator L.edges)+blockClass C (pairIndicator R.edges)=_
    rw [← map_add,← pairIndicator_union hdis,hcover]
    rfl
  have hclass : L.response=blockClass C (pairIndicator {e}) := by
    change blockClass C (pairIndicator L.edges)=_
    rw [hL]
  refine ⟨L,R,hclass,?_,hcover⟩
  rw [← hsum,hclass]
  abel

/-- An independent collection of positive partial stars, with integer scales
bounded by `M`, a prescribed weighted response, and coverage of every pair. -/
structure WeightedStarFamily (C : Finset H) (M : ℤ) (v : ResponseQuotient H) (r : ℕ) where
  piece : Fin r → StarPiece C
  weight : Fin r → ℤ
  positive : ∀ j,0< weight j
  bounded : ∀ j,weight j≤ M
  independent : LinearIndependent ℝ (fun j => (piece j).response)
  weighted_sum : (∑ j,(weight j : ℝ) • (piece j).response)=v
  covers : ∀ e : PairIn C,∃ j,e∈(piece j).edges

theorem weightedStarFamily_of_data {C : Finset H} {M : ℤ} {v : ResponseQuotient H}
    {J : Type*} [Fintype J] (P : J → StarPiece C) (w : J → ℤ)
    (hp : ∀ j,0< w j) (hb : ∀ j,w j≤ M)
    (hi : LinearIndependent ℝ (fun j => (P j).response))
    (hs : (∑ j,(w j : ℝ) • (P j).response)=v)
    (hc : ∀ e : PairIn C,∃ j,e∈(P j).edges) {r : ℕ} (hr : Fintype.card J=r) :
    Nonempty (WeightedStarFamily C M v r) := by
  classical
  let e : Fin r ≃ J := (finCongr hr.symm).trans (Fintype.equivFin J).symm
  refine ⟨⟨fun i => P (e i),fun i => w (e i),fun i => hp (e i),fun i => hb (e i),
    hi.comp e e.injective,?_,?_⟩⟩
  · exact (e.sum_comp _).trans hs
  · intro x
    obtain ⟨j,hj⟩ := hc x
    exact ⟨e.symm j,by simpa only [e.apply_symm_apply] using hj⟩

/-- One independent rank-increasing split. Positivity, the upper weight
bound, the prescribed weighted response, and complete pair coverage persist. -/
theorem WeightedStarFamily.step {C : Finset H} {M : ℤ} {v : ResponseQuotient H}
    {r : ℕ} (P : WeightedStarFamily C M v r) (e₀ : PairIn C)
    (hr : r< C.card.choose 2-1) : Nonempty (WeightedStarFamily C M v (r+1)) := by
  classical
  obtain ⟨e,he⟩ := exists_pair_outside_span C e₀ (fun j => (P.piece j).response)
    P.independent (by simpa only [Fintype.card_fin] using hr)
  obtain ⟨j₀,hj₀⟩ := P.covers e
  have hne : (P.piece j₀).response≠ blockClass C (pairIndicator {e}) := by
    intro h
    exact he (h ▸ Submodule.subset_span ⟨j₀,rfl⟩)
  obtain ⟨L,R,hL,hR,hcov⟩ := (P.piece j₀).split_at e hj₀ hne
  let Q : Option (Fin r) → StarPiece C := fun j => match j with
    | none => L
    | some j => if j=j₀ then R else P.piece j
  let w : Option (Fin r) → ℤ := fun j => Option.casesOn' j (P.weight j₀) P.weight
  have hq : (fun j => (Q j).response)=
      splitColumnFamily (fun j => (P.piece j).response) j₀ (blockClass C (pairIndicator {e})) := by
    funext j
    cases j with
    | none => exact hL
    | some j =>
      by_cases h : j=j₀
      · subst j
        simp only [Q,splitColumnFamily,ite_true,hR]
      · simp only [Q,splitColumnFamily,ite_eq_right h]
  have hi : LinearIndependent ℝ (fun j => (Q j).response) := by
    rw [hq]
    exact splitColumnFamily_independent _ P.independent j₀ _ he
  have hs : (∑ j,(w j : ℝ) • (Q j).response)=v := by
    have hw : (fun j : Option (Fin r) => (w j : ℝ))=
        fun j => Option.casesOn' j (P.weight j₀ : ℝ) (fun i => (P.weight i : ℝ)) := by
      funext j
      cases j <;> rfl
    change (∑ j,(fun i : Option (Fin r) => (w i : ℝ)) j • (fun i => (Q i).response) j)=v
    rw [hw,hq]
    exact (splitColumnFamily_preserves_sum (fun j => (P.piece j).response) j₀
      (blockClass C (pairIndicator {e})) (fun j => (P.weight j : ℝ))).trans P.weighted_sum
  have hc : ∀ f : PairIn C,∃ j,f∈(Q j).edges := by
    intro f
    obtain ⟨j,hj⟩ := P.covers f
    by_cases h : j=j₀
    · subst j
      rw [← hcov,mem_union] at hj
      rcases hj with hj | hj
      · exact ⟨none,hj⟩
      · exact ⟨some j₀,by simpa only [Q,ite_true] using hj⟩
    · exact ⟨some j,by simpa only [Q,ite_eq_right h] using hj⟩
  apply weightedStarFamily_of_data Q w _ _ hi hs hc (by simp)
  · intro j
    cases j with
    | none => exact P.positive j₀
    | some j => exact P.positive j
  · intro j
    cases j with
    | none => exact P.bounded j₀
    | some j => exact P.bounded j

/-- Refinement reaches every intermediate number of columns all the way to
the full quotient dimension. All modules and integer scales are retained. -/
theorem WeightedStarFamily.refine {C : Finset H} {M : ℤ} {v : ResponseQuotient H}
    {r : ℕ} (P : WeightedStarFamily C M v r) (e₀ : PairIn C)
    {k : ℕ} (hlo : r≤ k) (hhi : k≤ C.card.choose 2-1) :
    Nonempty (WeightedStarFamily C M v k) := by
  induction k, hlo using Nat.le_induction with
  | base => exact ⟨P⟩
  | succ k hk ih =>
    obtain ⟨Q⟩ := ih (by omega)
    exact Q.step e₀ (by omega)

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart155

section BundlePart156
/- Source: Papers/GraphicalZonotopes/PurePivotSplitting.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators

section Pivot
variable {E I : Type*} [DecidableEq E] [Fintype I] [DecidableEq I]

def pivotPositive (seed : I → E) (D : Finset E) (owner : D → I) (i : I) : E → ℝ :=
  fun e => (if e=seed i then 1 else 0) +
    if h : e∈D then if owner ⟨e,h⟩=i then 1 else 0 else 0

def pivotColumns (seed : I → E) (D : Finset E) (owner : D → I) : I ⊕ D → E → ℝ
  | Sum.inl i => pivotPositive seed D owner i
  | Sum.inr d => fun e => if e=d.1 then -1 else 0

theorem pivotPositive_at_seed (seed : I → E) (hseed : Function.Injective seed)
    (D : Finset E) (owner : D → I) (hD : ∀ i,seed i∉D) (i j : I) :
    pivotPositive seed D owner i (seed j)=if j=i then 1 else 0 := by
  simp only [pivotPositive,dite_eq_right (hD j),add_zero,hseed.eq_iff]

theorem pivotPositive_at_extra (seed : I → E) (D : Finset E) (owner : D → I)
    (hD : ∀ i,seed i∉D) (i : I) (d : D) :
    pivotPositive seed D owner i d.1=if owner d=i then 1 else 0 := by
  have hne : d.1≠ seed i := fun h => hD i (h ▸ d.2)
  simp only [pivotPositive,ite_eq_right hne,dite_eq_left d.2,zero_add]

theorem pivotColumns_linearIndependent (seed : I → E) (hseed : Function.Injective seed)
    (D : Finset E) (owner : D → I) (hD : ∀ i,seed i∉D) :
    LinearIndependent ℝ (pivotColumns seed D owner) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have hbase : ∀ i,c (Sum.inl i)=0 := by
    intro i
    have hv := congrFun hc (seed i)
    rw [Fintype.sum_sum_type] at hv
    simp only [Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
      pivotColumns,pivotPositive_at_seed seed hseed D owner hD,Pi.zero_apply] at hv
    have hn : ∀ d : D,seed i≠ d.1 := fun d h => hD i (h.symm ▸ d.2)
    simp only [hn,ite_false,mul_zero,sum_const_zero,add_zero] at hv
    simpa using hv
  cases j with
  | inl i => exact hbase i
  | inr d =>
    have hv := congrFun hc d.1
    rw [Fintype.sum_sum_type] at hv
    simp only [Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
      hbase,zero_mul,sum_const_zero,zero_add,pivotColumns,Pi.zero_apply] at hv
    have he : ∀ e : D,d.1=e.1 ↔ e=d := fun e =>
      ⟨fun h => Subtype.ext h.symm,fun h => congrArg Subtype.val h.symm⟩
    simp_rw [he] at hv
    simpa using hv

theorem pivotColumns_sum (seed : I → E) (D : Finset E) (owner : D → I) :
    (∑ j : I ⊕ D,pivotColumns seed D owner j)=
      fun e => ∑ i : I,if e=seed i then (1 : ℝ) else 0 := by
  classical
  funext e
  rw [Fintype.sum_sum_type]
  simp only [Pi.add_apply,Finset.sum_apply,pivotColumns,pivotPositive]
  rw [sum_add_distrib]
  by_cases h : e∈D
  · simp only [dite_eq_left h]
    have he : ∀ d : D,e=d.1 ↔ d=⟨e,h⟩ := fun d =>
      ⟨fun he => Subtype.ext he.symm,fun he => congrArg Subtype.val he.symm⟩
    simp_rw [he]
    simp
  · have he : ∀ d : D,e≠ d.1 := fun d he => h (he.symm ▸ d.2)
    simp only [dite_eq_right h,he,ite_false,sum_const_zero,add_zero]

theorem pivotColumns_zero_at (seed : I → E) (D : Finset E) (owner : D → I)
    (e : E) (heD : e∉D) (hseed : ∀ i,e≠ seed i) (j : I ⊕ D) :
    pivotColumns seed D owner j e=0 := by
  cases j with
  | inl i => simp [pivotColumns,pivotPositive,hseed i,heD]
  | inr d =>
    have he : e≠ d.1 := fun h => heD (h.symm ▸ d.2)
    simp [pivotColumns,he]

end Pivot
end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart156

section BundlePart157
/- Source: Papers/GraphicalZonotopes/PureDecompositions.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H : Type*} [Fintype H] [LinearOrder H]

/-- An actual family of Boolean modules, independent in the complete
response quotient, whose unit-weight sum is the prescribed class. -/
structure PureDecomposition (C : Finset H) (v : ResponseQuotient H) (k : ℕ) where
  functions : Fin k → SetFunction H
  monotone_boolean : ∀ i, IsMonotoneBoolean (functions i)
  essential : ∀ i a, a∈C → Essential (functions i) a
  ignored : ∀ i a, a∉C → ∀ X, functions i (insert a X)=functions i X
  block_supported : ∀ i, ∃ x : PairIn C → ℝ, responseClass (functions i)=blockClass C x
  independent : LinearIndependent ℝ (fun i => responseClass (functions i))
  sum_eq : (∑ i,responseClass (functions i))=v

theorem pureDecomposition_of_vectors {C : Finset H} {J : Type*} [Fintype J]
    (x : J → PairIn C → ℝ) (hx : ∀ j,PureRealizable C (x j))
    (hind : LinearIndependent ℝ (fun j => blockClass C (x j)))
    {v : ResponseQuotient H} (hsum : (∑ j,blockClass C (x j))=v)
    {k : ℕ} (hk : Fintype.card J=k) : Nonempty (PureDecomposition C v k) := by
  classical
  choose F hF he hi hr using hx
  let e : Fin k ≃ J := (finCongr hk.symm).trans (Fintype.equivFin J).symm
  refine ⟨⟨fun i => F (e i),fun i => hF (e i),fun i a => he (e i) a,
    fun i a => hi (e i) a,fun i => ⟨x (e i),hr (e i)⟩,?_,?_⟩⟩
  · have h : LinearIndependent ℝ (fun j => responseClass (F j)) := by
      simpa only [hr] using hind
    exact h.comp e e.injective
  · calc
      _ = ∑ j : J,responseClass (F j) := e.sum_comp _
      _ = v := by simpa only [hr] using hsum

def starVector (C : Finset H) (a : H) : PairIn C → ℝ :=
  pairIndicator (starPairs C a (C.erase a))

theorem starVector_eq (C : Finset H) (a : H) (e : PairIn C) :
    starVector C a e=if a=e.1.1.1 ∨ a=e.1.1.2 then 1 else 0 := by
  have hu := e.2.1
  have hv := e.2.2
  have huv : e.1.1.1≠ e.1.1.2 := ne_of_lt e.1.2.1
  simp only [starVector,pairIndicator,mem_starPairs,StarPair,mem_erase]
  congr 1
  apply propext
  constructor
  · rintro (⟨h,_⟩ | ⟨h,_⟩)
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · rintro (h | h)
    · exact Or.inl ⟨h.symm,fun hh => huv (h.symm.trans hh.symm),hv⟩
    · exact Or.inr ⟨h.symm,fun hh => huv (hh.trans h),hu⟩

theorem clique_without_vertex_class (C : Finset H) (a : H) :
    blockClass C (pairIndicator (cliquePairs C (C.erase a))) =
      -blockClass C (starVector C a) := by
  have he : pairIndicator (cliquePairs C (C.erase a))=
      (fun _ : PairIn C => (1 : ℝ))-starVector C a := by
    funext e
    simp only [Pi.sub_apply]
    rw [starVector_eq]
    simp only [pairIndicator,mem_cliquePairs,mem_erase]
    by_cases hu : a=e.1.1.1 <;> by_cases hv : a=e.1.1.2 <;>
      simp [eq_comm,hu,hv,e.2.1,e.2.2]
  rw [he,map_sub]
  have hz : blockClass C (fun _ : PairIn C => (1 : ℝ))=0 := by
    change coefficientClass (blockCoordinates C (fun _ => 1))=0
    have hco : blockCoordinates C (fun _ : PairIn C => (1 : ℝ))=
        fun r : HubResponseRow H => if rowClique r=C then 1 else 0 := by
      funext r
      change (if _h : rowClique r=C then (1 : ℝ) else 0)=_
      split <;> rfl
    rw [hco]
    exact coefficientClass_block_zero C
  rw [hz,zero_sub]

theorem positive_star_small_interpolation (C : Finset H) (hC : 3≤ C.card)
    (a : H) (ha : a∈C) {k : ℕ} (hk : 1≤ k) (hkC : k≤ C.card-1) :
    Nonempty (PureDecomposition C (blockClass C (starVector C a)) k) := by
  have hcard : (C.erase a).card=C.card-1 := card_erase_of_mem ha
  have hn : (C.erase a).Nonempty := card_pos.mp (by omega)
  have hsub : C.erase a⊆C := erase_subset _ _
  obtain ⟨Q,hQ,hreal,hind,hsum⟩ := pureEdgeChunk_partition C
    (Or.inl ⟨a,C.erase a,ha,hsub,notMem_erase _ _,rfl⟩)
    (starPairs_nonempty C ha hsub (notMem_erase _ _) hn) hk
    (by simpa only [starPairs_card C ha hsub (notMem_erase _ _),hcard] using hkC)
  obtain ⟨e₀,he₀⟩ := cliquePairs_nonempty C (C.erase a) hsub (by omega)
  have hzero : ∀ B : Q.parts,pairIndicator B.1 e₀=0 := by
    intro B
    have hnot : e₀∉B.1 := by
      intro h
      have hs := mem_starPairs.mp ((Q.le B.2) h)
      obtain ⟨hu,hv⟩ := mem_cliquePairs.mp he₀
      rcases hs with ⟨hh,_⟩ | ⟨hh,_⟩
      · exact (mem_erase.mp hu).1 hh
      · exact (mem_erase.mp hv).1 hh
    exact ite_eq_right hnot
  apply pureDecomposition_of_vectors _ hreal
    (blockClass_linearIndependent_of_reference C e₀ _ hind hzero) _
    (by simpa only [Fintype.card_coe] using hQ)
  rw [← map_sum,hsum]
  rfl

theorem negative_star_small_interpolation (C : Finset H) (hC : 3≤ C.card)
    (a : H) (ha : a∈C) {k : ℕ} (hk : 1≤ k) (hkC : k≤(C.card-1).choose 2) :
    Nonempty (PureDecomposition C (-blockClass C (starVector C a)) k) := by
  have hcard : (C.erase a).card=C.card-1 := card_erase_of_mem ha
  have hsub : C.erase a⊆C := erase_subset _ _
  obtain ⟨Q,hQ,hreal,hind,hsum⟩ := pureEdgeChunk_partition C
    (Or.inr ⟨C.erase a,hsub,rfl⟩)
    (cliquePairs_nonempty C (C.erase a) hsub (by omega)) hk
    (by simpa only [cliquePairs_card C (C.erase a) hsub,hcard] using hkC)
  obtain ⟨b,hb⟩ := card_pos.mp (show 0<(C.erase a).card by omega)
  have hab : a≠ b := Ne.symm (mem_erase.mp hb).1
  let e₀ := pairOfNe C a b hab ha (mem_of_mem_erase hb)
  have hzero : ∀ B : Q.parts,pairIndicator B.1 e₀=0 := by
    intro B
    have hnot : e₀∉B.1 := by
      intro h
      obtain ⟨hu,hv⟩ := mem_cliquePairs.mp ((Q.le B.2) h)
      rcases pairOfNe_endpoints C a b hab ha (mem_of_mem_erase hb) with hh | hh
      · exact (mem_erase.mp hu).1 hh.1
      · exact (mem_erase.mp hv).1 hh.2
    exact ite_eq_right hnot
  apply pureDecomposition_of_vectors _ hreal
    (blockClass_linearIndependent_of_reference C e₀ _ hind hzero) _
    (by simpa only [Fintype.card_coe] using hQ)
  rw [← map_sum,hsum]
  exact clique_without_vertex_class C a

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart157

section BundlePart158
/- Source: Papers/GraphicalZonotopes/StarCoordinateAlgebra.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H : Type*} [Fintype H] [LinearOrder H]

def erasedHubWeight (C : Finset H) (m : H) (t : C.erase m → ℝ) (a : H) : ℝ :=
  if h : a∈C.erase m then t ⟨a,h⟩ else 0

@[simp] theorem erasedHubWeight_self (C : Finset H) (m : H) (t : C.erase m → ℝ) :
    erasedHubWeight C m t m=0 := by
  simp [erasedHubWeight]

@[simp] theorem erasedHubWeight_subtype (C : Finset H) (m : H)
    (t : C.erase m → ℝ) (a : C.erase m) : erasedHubWeight C m t a.1=t a := by
  simp only [erasedHubWeight,dite_eq_left a.2]

private theorem sum_erased_indicator (C : Finset H) (m : H)
    (t : C.erase m → ℝ) (a : H) :
    (∑ i : C.erase m,t i*(if i.1=a then (1 : ℝ) else 0))=erasedHubWeight C m t a := by
  classical
  by_cases ha : a∈C.erase m
  · have he : ∀ i : C.erase m,i.1=a ↔ i=⟨a,ha⟩ :=
      fun i => ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩
    simp [he,erasedHubWeight,ha]
  · have hn : ∀ i : C.erase m,i.1≠ a := fun i h => ha (h ▸ i.2)
    simp [hn,erasedHubWeight,ha]

theorem sum_erased_stars_eval (C : Finset H) (m : H)
    (t : C.erase m → ℝ) (e : PairIn C) :
    (∑ i : C.erase m,t i • starVector C i.1) e=
      erasedHubWeight C m t e.1.1.1+erasedHubWeight C m t e.1.1.2 := by
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply,smul_eq_mul,starVector_eq]
  have he : ∀ i : C.erase m,t i*(if i.1=e.1.1.1 ∨ i.1=e.1.1.2 then (1 : ℝ) else 0)=
      t i*(if i.1=e.1.1.1 then 1 else 0)+t i*(if i.1=e.1.1.2 then 1 else 0) := by
    intro i
    by_cases hu : i.1=e.1.1.1 <;> by_cases hv : i.1=e.1.1.2
    · exact False.elim ((ne_of_lt e.1.2.1) (hu.symm.trans hv))
    all_goals simp [hu,hv,ne_of_lt e.1.2.1,Ne.symm (ne_of_lt e.1.2.1)]
  rw [sum_congr rfl (fun i _ => he i),sum_add_distrib,
    sum_erased_indicator,sum_erased_indicator]

theorem sum_erased_stars_at_pair (C : Finset H) (m : H) (t : C.erase m → ℝ)
    (u v : H) (huv : u≠ v) (hu : u∈C) (hv : v∈C) :
    (∑ i : C.erase m,t i • starVector C i.1) (pairOfNe C u v huv hu hv)=
      erasedHubWeight C m t u+erasedHubWeight C m t v := by
  rw [sum_erased_stars_eval]
  rcases pairOfNe_endpoints C u v huv hu hv with h | h <;> simp [h.1,h.2,add_comm]

/-- The stars centered at all but one vertex are independent modulo the
constant pair vector. This is proved from the actual pair quotient. -/
theorem erased_star_columns_independent (C : Finset H) (hC : 3≤ C.card)
    (m : H) (hm : m∈C) :
    LinearIndependent ℝ (fun i : C.erase m => blockClass C (starVector C i.1)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro t ht i
  have hmap : blockClass C (∑ j : C.erase m,t j • starVector C j.1)=0 := by
    simpa only [map_sum,map_smul] using ht
  have herase : 2≤(C.erase m).card := by rw [card_erase_of_mem hm]; omega
  obtain ⟨u,hu,v,hv,huv⟩ := one_lt_card.mp (show 1<(C.erase m).card by omega)
  let e₀ := pairOfNe C u v huv (mem_of_mem_erase hu) (mem_of_mem_erase hv)
  obtain ⟨c,hc⟩ := (blockClass_eq_zero_iff C e₀ _).mp hmap
  have hscale : ∀ j : C.erase m,t j=c := by
    intro j
    have h := hc (pairOfNe C m j.1 (Ne.symm (mem_erase.mp j.2).1) hm (mem_of_mem_erase j.2))
    rw [sum_erased_stars_at_pair,erasedHubWeight_self,erasedHubWeight_subtype,zero_add] at h
    exact h
  have hz := hc e₀
  rw [sum_erased_stars_at_pair] at hz
  have hu' : erasedHubWeight C m t u=t ⟨u,hu⟩ := erasedHubWeight_subtype C m t ⟨u,hu⟩
  have hv' : erasedHubWeight C m t v=t ⟨v,hv⟩ := erasedHubWeight_subtype C m t ⟨v,hv⟩
  rw [hu',hv',hscale,hscale] at hz
  have hc0 : c=0 := by linarith
  exact (hscale i).trans hc0

def fullStarPiece (C : Finset H) (hC : 2≤ C.card) (i : C) : StarPiece C where
  center := i.1
  leaves := C.erase i.1
  center_mem := i.2
  leaves_subset := erase_subset _ _
  nonempty := card_pos.mp (by rw [card_erase_of_mem i.2]; omega)
  center_notMem := notMem_erase _ _

theorem fullStarPiece_response (C : Finset H) (hC : 2≤ C.card) (i : C) :
    (fullStarPiece C hC i).response=blockClass C (starVector C i.1) := rfl

/-- Positive vertex-star scales have independent positive partial-star
refinements at every count between `|C|-1` and the full block dimension. -/
theorem weighted_full_stars_interpolation (C : Finset H) (hC : 3≤ C.card)
    (m : H) (hm : m∈C) (w : C.erase m → ℤ) (M : ℤ)
    (hw : ∀ i,0< w i) (hM : ∀ i,w i≤ M) {k : ℕ}
    (hklo : C.card-1≤ k) (hkhi : k≤ C.card.choose 2-1) :
    Nonempty (WeightedStarFamily C M
      (∑ i : C.erase m,(w i : ℝ) • blockClass C (starVector C i.1)) k) := by
  classical
  let P : C.erase m → StarPiece C := fun i => fullStarPiece C (by omega) ⟨i.1,mem_of_mem_erase i.2⟩
  have hi : LinearIndependent ℝ (fun i => (P i).response) :=
    erased_star_columns_independent C hC m hm
  have hc : ∀ e : PairIn C,∃ j,e∈(P j).edges := by
    intro e
    by_cases hu : e.1.1.1=m
    · have hv : e.1.1.2≠ m := fun h => (ne_of_lt e.1.2.1) (hu.trans h.symm)
      let j : C.erase m := ⟨e.1.1.2,mem_erase.mpr ⟨hv,e.2.2⟩⟩
      refine ⟨j,mem_starPairs.mpr (Or.inr ⟨rfl,?_⟩)⟩
      exact mem_erase.mpr ⟨ne_of_lt e.1.2.1,e.2.1⟩
    · let j : C.erase m := ⟨e.1.1.1,mem_erase.mpr ⟨hu,e.2.1⟩⟩
      refine ⟨j,mem_starPairs.mpr (Or.inl ⟨rfl,?_⟩)⟩
      exact mem_erase.mpr ⟨Ne.symm (ne_of_lt e.1.2.1),e.2.2⟩
  obtain ⟨Q⟩ := weightedStarFamily_of_data P w hw hM hi rfl hc
    (r:=C.card-1) (by simp only [Fintype.card_coe,card_erase_of_mem hm])
  obtain ⟨e₀,he₀⟩ := cliquePairs_nonempty C C (Subset.refl _) (by omega)
  exact Q.refine e₀ hklo hkhi

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart158

section BundlePart159
/- Source: Papers/GraphicalZonotopes/OrdinaryBookBlocks.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators

variable {s : ℕ}

def endpointLabels (C : Finset (Fin s)) : PairIn C → ℝ :=
  fun e => (e.1.1.1.val : ℝ)+(e.1.1.2.val : ℝ)

def ordinaryBookTarget (C : Finset (Fin s)) : ResponseQuotient (Fin s) :=
  -((-1 : ℝ)^(C.card-3) • blockClass C (endpointLabels C))

private theorem numeric_erased_weight (C : Finset (Fin s)) (m a : Fin s)
    (ha : a∈C) :
    erasedHubWeight C m (fun i => (((i.1.val : ℤ)-(m.val : ℤ)) : ℝ)) a=
      (a.val : ℝ)-(m.val : ℝ) := by
  by_cases h : a=m
  · subst a
    simp
  · have hm : a∈C.erase m := mem_erase.mpr ⟨h,ha⟩
    simp only [erasedHubWeight,dite_eq_left hm,Int.cast_sub,Int.cast_natCast]

private theorem numeric_erased_weight_neg (C : Finset (Fin s)) (m a : Fin s)
    (ha : a∈C) :
    erasedHubWeight C m (fun i => (((m.val : ℤ)-(i.1.val : ℤ)) : ℝ)) a=
      (m.val : ℝ)-(a.val : ℝ) := by
  by_cases h : a=m
  · subst a
    simp
  · have hm : a∈C.erase m := mem_erase.mpr ⟨h,ha⟩
    simp only [erasedHubWeight,dite_eq_left hm,Int.cast_sub,Int.cast_natCast]

private theorem endpoint_stars_positive (C : Finset (Fin s)) (m : Fin s)
    (e₀ : PairIn C) :
    (∑ i : C.erase m,((((i.1.val : ℤ)-(m.val : ℤ)) : ℝ)) •
      blockClass C (starVector C i.1))=blockClass C (endpointLabels C) := by
  have he : (∑ i : C.erase m,((((i.1.val : ℤ)-(m.val : ℤ)) : ℝ)) • starVector C i.1)=
      endpointLabels C-(fun _ : PairIn C => 2*(m.val : ℝ)) := by
    funext e
    rw [sum_erased_stars_eval,numeric_erased_weight C m _ e.2.1,numeric_erased_weight C m _ e.2.2]
    change ((e.1.1.1.val : ℝ)-m.val)+((e.1.1.2.val : ℝ)-m.val)=
      (e.1.1.1.val : ℝ)+e.1.1.2.val-2*m.val
    ring
  have hz : blockClass C (fun _ : PairIn C => 2*(m.val : ℝ))=0 :=
    (blockClass_eq_zero_iff C e₀ _).mpr ⟨2*(m.val : ℝ),fun _ => rfl⟩
  calc
    _ = blockClass C (∑ i : C.erase m,
        ((((i.1.val : ℤ)-(m.val : ℤ)) : ℝ)) • starVector C i.1) := by simp only [map_sum,map_smul]
    _ = _ := by rw [he,map_sub,hz,sub_zero]

private theorem endpoint_stars_negative (C : Finset (Fin s)) (m : Fin s)
    (e₀ : PairIn C) :
    (∑ i : C.erase m,((((m.val : ℤ)-(i.1.val : ℤ)) : ℝ)) •
      blockClass C (starVector C i.1))= -blockClass C (endpointLabels C) := by
  have he : (∑ i : C.erase m,((((m.val : ℤ)-(i.1.val : ℤ)) : ℝ)) • starVector C i.1)=
      (fun _ : PairIn C => 2*(m.val : ℝ))-endpointLabels C := by
    funext e
    rw [sum_erased_stars_eval,numeric_erased_weight_neg C m _ e.2.1,numeric_erased_weight_neg C m _ e.2.2]
    change ((m.val : ℝ)-e.1.1.1.val)+((m.val : ℝ)-e.1.1.2.val)=
      2*(m.val : ℝ)-((e.1.1.1.val : ℝ)+e.1.1.2.val)
    ring
  have hz : blockClass C (fun _ : PairIn C => 2*(m.val : ℝ))=0 :=
    (blockClass_eq_zero_iff C e₀ _).mpr ⟨2*(m.val : ℝ),fun _ => rfl⟩
  calc
    _ = blockClass C (∑ i : C.erase m,
        ((((m.val : ℤ)-(i.1.val : ℤ)) : ℝ)) • starVector C i.1) := by simp only [map_sum,map_smul]
    _ = _ := by rw [he,map_sub,hz,zero_sub]

/-- Every ordinary clique block in Theorem 7.10 admits every intermediate
rank with strictly positive integral scales at most `s-1`. The target is the
literal cancellation of all weighted threshold-star responses on the block. -/
theorem ordinary_book_block_interpolation (C : Finset (Fin s)) (hC : 3≤ C.card)
    {k : ℕ} (hklo : C.card-1≤ k) (hkhi : k≤ C.card.choose 2-1) :
    Nonempty (WeightedStarFamily C ((s-1 : ℕ) : ℤ) (ordinaryBookTarget C) k) := by
  classical
  have hne : C.Nonempty := card_pos.mp (by omega)
  obtain ⟨e₀,he₀⟩ := cliquePairs_nonempty C C (Subset.refl _) (by omega)
  rcases neg_one_pow_eq_or ℝ (C.card-3) with hsign | hsign
  · let m := C.max' hne
    have hm : m∈C := max'_mem C hne
    let w : C.erase m → ℤ := fun i => (m.val : ℤ)-(i.1.val : ℤ)
    have hw : ∀ i,0< w i := by
      intro i
      have hle : i.1≤ m := le_max' C i.1 (mem_of_mem_erase i.2)
      have hni : i.1≠ m := (mem_erase.mp i.2).1
      have hlt : i.1< m := lt_of_le_of_ne hle hni
      have hval : i.1.val< m.val := hlt
      dsimp only [w]
      omega
    have hb : ∀ i,w i≤((s-1 : ℕ) : ℤ) := by
      intro i
      have hmval := m.isLt
      dsimp only [w]
      omega
    have hp := weighted_full_stars_interpolation C hC m hm w ((s-1 : ℕ) : ℤ) hw hb hklo hkhi
    have he := endpoint_stars_negative C m e₀
    have he' : (∑ i : C.erase m,(w i : ℝ) • blockClass C (starVector C i.1))=
        -blockClass C (endpointLabels C) := by
      simpa only [w,Int.cast_sub,Int.cast_natCast] using he
    rw [he'] at hp
    simpa only [ordinaryBookTarget,hsign,one_smul] using hp
  · let m := C.min' hne
    have hm : m∈C := min'_mem C hne
    let w : C.erase m → ℤ := fun i => (i.1.val : ℤ)-(m.val : ℤ)
    have hw : ∀ i,0< w i := by
      intro i
      have hle : m ≤ i.1 := min'_le C i.1 (mem_of_mem_erase i.2)
      have hni : m≠ i.1 := Ne.symm (mem_erase.mp i.2).1
      have hlt : m < i.1 := lt_of_le_of_ne hle hni
      have hval : m.val < i.1.val := hlt
      dsimp only [w]
      omega
    have hb : ∀ i,w i≤((s-1 : ℕ) : ℤ) := by
      intro i
      have hival := i.1.isLt
      dsimp only [w]
      omega
    have hp := weighted_full_stars_interpolation C hC m hm w ((s-1 : ℕ) : ℤ) hw hb hklo hkhi
    have he := endpoint_stars_positive C m e₀
    have he' : (∑ i : C.erase m,(w i : ℝ) • blockClass C (starVector C i.1))=
        blockClass C (endpointLabels C) := by
      simpa only [w,Int.cast_sub,Int.cast_natCast] using he
    rw [he'] at hp
    simpa only [ordinaryBookTarget,hsign,neg_one_smul,neg_neg] using hp

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart159

section BundlePart160
/- Source: Papers/GraphicalZonotopes/BookQuadrilateralModules.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators

structure BalancedQuad (s : ℕ) where
  point : Fin 4 → Fin s
  ordered : StrictMono point
  balanced : (point 0).val+(point 3).val=(point 1).val+(point 2).val

namespace BalancedQuad
variable {s : ℕ} (Q : BalancedQuad s)

def clique : Finset (Fin s) := univ.image Q.point

@[simp] theorem point_mem (i : Fin 4) : Q.point i∈Q.clique :=
  mem_image.mpr ⟨i,mem_univ _,rfl⟩

@[simp] theorem card_clique : Q.clique.card=4 := by
  rw [clique,card_image_of_injective _ Q.ordered.injective]
  rfl

def pair (i j : Fin 4) (hij : i< j) : PairIn Q.clique :=
  orderedPair Q.clique (Q.point i) (Q.point j) (Q.ordered hij) (Q.point_mem i) (Q.point_mem j)

@[simp] theorem pair_eq_iff (i j k l : Fin 4) (hij : i< j) (hkl : k< l) :
    Q.pair i j hij=Q.pair k l hkl ↔ i=k ∧ j=l := by
  constructor
  · intro h
    exact ⟨Q.ordered.injective (congrArg (fun e : PairIn Q.clique => e.1.1.1) h),
      Q.ordered.injective (congrArg (fun e : PairIn Q.clique => e.1.1.2) h)⟩
  · rintro ⟨rfl,rfl⟩
    rfl

def reference : PairIn Q.clique := Q.pair 0 3 (by decide)
def opposite : PairIn Q.clique := Q.pair 1 2 (by decide)

def retainedIndices : Fin 4 → Fin 4×Fin 4 := ![(0,1),(0,2),(1,3),(2,3)]
theorem retainedIndices_order (i : Fin 4) : (retainedIndices i).1<(retainedIndices i).2 := by
  fin_cases i <;> decide
theorem retainedIndices_injective : Function.Injective retainedIndices := by decide

def retainedPair (i : Fin 4) : PairIn Q.clique :=
  Q.pair (retainedIndices i).1 (retainedIndices i).2 (retainedIndices_order i)

theorem retainedPair_injective : Function.Injective Q.retainedPair := by
  intro i j h
  apply retainedIndices_injective
  apply Prod.ext
  · exact ((Q.pair_eq_iff _ _ _ _ _ _).mp h).1
  · exact ((Q.pair_eq_iff _ _ _ _ _ _).mp h).2

@[simp] theorem reference_ne_retained (i : Fin 4) : Q.reference≠ Q.retainedPair i := by
  change Q.pair 0 3 _≠ Q.pair _ _ _
  rw [ne_eq,pair_eq_iff]
  fin_cases i <;> decide

@[simp] theorem opposite_ne_retained (i : Fin 4) : Q.opposite≠ Q.retainedPair i := by
  change Q.pair 1 2 _≠ Q.pair _ _ _
  rw [ne_eq,pair_eq_iff]
  fin_cases i <;> decide

def columnSign (i : Fin 4) : ℝ := if i.val<2 then -1 else 1

def column (i : Fin 4) : PairIn Q.clique → ℝ :=
  columnSign i • pairIndicator {Q.retainedPair i}

def label (i : Fin 4) : ℤ := ((Q.point i).val : ℤ)

def weight : Fin 4 → ℤ :=
  ![Q.label 3-Q.label 1,Q.label 3-Q.label 2,Q.label 1-Q.label 0,Q.label 2-Q.label 0]

@[simp] theorem columnSign_ne_zero (i : Fin 4) : columnSign i≠0 := by
  unfold columnSign
  split <;> norm_num

theorem column_realizable (i : Fin 4) : PureRealizable Q.clique (Q.column i) := by
  by_cases h : i.val<2
  · have he : Q.column i= -pairIndicator {Q.retainedPair i} := by
      simp only [column,columnSign,ite_eq_left h,neg_one_smul]
    rw [he]
    exact pureRealizable_negative_pair Q.clique (by rw [Q.card_clique]; omega) (Q.retainedPair i)
  · have he : Q.column i=pairIndicator {Q.retainedPair i} := by
      simp only [column,columnSign,ite_eq_right h,one_smul]
    rw [he]
    exact pureRealizable_pair Q.clique (Q.retainedPair i)

theorem weight_positive (i : Fin 4) : 0< Q.weight i := by
  have h01 : Q.label 0< Q.label 1 := by
    change ((Q.point 0).val : ℤ)<((Q.point 1).val : ℤ)
    exact_mod_cast (show (Q.point 0).val<(Q.point 1).val from Q.ordered (by decide : (0 : Fin 4)<1))
  have h02 : Q.label 0< Q.label 2 := by
    change ((Q.point 0).val : ℤ)<((Q.point 2).val : ℤ)
    exact_mod_cast (show (Q.point 0).val<(Q.point 2).val from Q.ordered (by decide : (0 : Fin 4)<2))
  have h13 : Q.label 1< Q.label 3 := by
    change ((Q.point 1).val : ℤ)<((Q.point 3).val : ℤ)
    exact_mod_cast (show (Q.point 1).val<(Q.point 3).val from Q.ordered (by decide : (1 : Fin 4)<3))
  have h23 : Q.label 2< Q.label 3 := by
    change ((Q.point 2).val : ℤ)<((Q.point 3).val : ℤ)
    exact_mod_cast (show (Q.point 2).val<(Q.point 3).val from Q.ordered (by decide : (2 : Fin 4)<3))
  fin_cases i <;> change 0 < _ - _ <;> omega

theorem weight_bounded (i : Fin 4) : Q.weight i≤((s-1 : ℕ) : ℤ) := by
  have hlo : ∀ j,0≤ Q.label j := fun j => Int.natCast_nonneg _
  have hhi : ∀ j,Q.label j<(s : ℤ) := fun j => by
    change ((Q.point j).val : ℤ)<(s : ℤ)
    exact_mod_cast (Q.point j).isLt
  have h0 := hlo 0
  have h1 := hlo 1
  have h2 := hlo 2
  have h3 := hhi 3
  have h1' := hhi 1
  have h2' := hhi 2
  fin_cases i <;> change _ - _ ≤ ((s-1 : ℕ) : ℤ) <;> omega

theorem columns_independent : LinearIndependent ℝ (fun i => blockClass Q.clique (Q.column i)) := by
  let p : Fin 4 → ↥((univ : Finset (PairIn Q.clique)).erase Q.reference) :=
    fun i => ⟨Q.retainedPair i,mem_erase.mpr ⟨Ne.symm (Q.reference_ne_retained i),mem_univ _⟩⟩
  have hp : Function.Injective p := fun i j h => Q.retainedPair_injective (congrArg Subtype.val h)
  have hi : LinearIndependent ℝ (fun i => blockClass Q.clique (pairIndicator {Q.retainedPair i})) :=
    (reference_pair_columns_independent Q.clique Q.reference).comp p hp
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hz : (∑ j,(c j*columnSign j) • blockClass Q.clique (pairIndicator {Q.retainedPair j}))=0 := by
    simpa only [column,map_smul,mul_smul] using hc
  exact (mul_eq_zero.mp ((Fintype.linearIndependent_iff.mp hi) _ hz i)).resolve_right (columnSign_ne_zero i)

@[simp] theorem column_reference (i : Fin 4) : Q.column i Q.reference=0 := by
  simp [column,pairIndicator]

@[simp] theorem column_opposite (i : Fin 4) : Q.column i Q.opposite=0 := by
  simp [column,pairIndicator]

/-- All six pair coordinates are checked: four retained signed pairs have
positive scales, and the two omitted pairs have the same endpoint sum. -/
theorem weighted_columns_vector :
    (∑ i : Fin 4,(Q.weight i : ℝ) • Q.column i)=
      endpointLabels Q.clique-(fun _ => ((Q.label 0+Q.label 3 : ℤ) : ℝ)) := by
  funext e
  obtain ⟨i,hi,hui⟩ := mem_image.mp e.2.1
  obtain ⟨j,hj,hvj⟩ := mem_image.mp e.2.2
  have hij : i< j := by
    by_contra hn
    have hle := Q.ordered.monotone (le_of_not_gt hn)
    have hlt : Q.point i< Q.point j := by simpa only [hui,hvj] using e.1.2.1
    exact (not_le_of_gt hlt) hle
  have he : e=Q.pair i j hij := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext hui.symm hvj.symm
  rw [he]
  have hb : ((Q.point 0).val : ℝ)+(Q.point 3).val=
      ((Q.point 1).val : ℝ)+(Q.point 2).val := by exact_mod_cast Q.balanced
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals
    simp [Fin.sum_univ_four,Pi.smul_apply,smul_eq_mul,column,columnSign,pairIndicator,
      retainedPair,retainedIndices,pair_eq_iff,weight,
      Int.cast_sub,Int.cast_add,Int.cast_natCast]
    simp only [endpointLabels,pair,orderedPair,label,Pi.sub_apply]
    push_cast
    linarith

theorem weighted_columns_response :
    (∑ i : Fin 4,(Q.weight i : ℝ) • blockClass Q.clique (Q.column i))=
      ordinaryBookTarget Q.clique := by
  have hz : blockClass Q.clique (fun _ : PairIn Q.clique => ((Q.label 0+Q.label 3 : ℤ) : ℝ))=0 :=
    (blockClass_eq_zero_iff Q.clique Q.reference _).mpr ⟨_,fun _ => rfl⟩
  calc
    _ = blockClass Q.clique (∑ i : Fin 4,(Q.weight i : ℝ) • Q.column i) := by simp only [map_sum,map_smul]
    _ = blockClass Q.clique (endpointLabels Q.clique) := by
      rw [Q.weighted_columns_vector,map_sub,hz,sub_zero]
    _ = ordinaryBookTarget Q.clique := by simp [ordinaryBookTarget,Q.card_clique]

end BalancedQuad
end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart160

section BundlePart161
/- Source: Papers/GraphicalZonotopes/WeightedPureBlocks.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators

variable {H : Type*} [Fintype H] [LinearOrder H]

/-- Positive integral pure module data, with the actual quotient classes and
actual monotone Boolean realizations as part of the construction. -/
structure WeightedPureBlock (C : Finset H) (M : ℤ)
    (v : ResponseQuotient H) (r : ℕ) where
  column : Fin r → PairIn C → ℝ
  realizable : ∀ j,PureRealizable C (column j)
  weight : Fin r → ℤ
  positive : ∀ j,0< weight j
  bounded : ∀ j,weight j≤ M
  independent : LinearIndependent ℝ (fun j => blockClass C (column j))
  weighted_sum : (∑ j,(weight j : ℝ) • blockClass C (column j))=v

namespace WeightedStarFamily

def toPureBlock {C : Finset H} {M : ℤ} {v : ResponseQuotient H} {r : ℕ}
    (P : WeightedStarFamily C M v r) : WeightedPureBlock C M v r where
  column := fun j => (P.piece j).vector
  realizable := fun j => (P.piece j).realizable
  weight := P.weight
  positive := P.positive
  bounded := P.bounded
  independent := P.independent
  weighted_sum := P.weighted_sum

end WeightedStarFamily

namespace BalancedQuad
variable {s : ℕ}

def pureBlock (Q : BalancedQuad s) :
    WeightedPureBlock Q.clique ((s-1 : ℕ) : ℤ) (ordinaryBookTarget Q.clique) 4 where
  column := Q.column
  realizable := Q.column_realizable
  weight := Q.weight
  positive := Q.weight_positive
  bounded := Q.weight_bounded
  independent := Q.columns_independent
  weighted_sum := Q.weighted_columns_response

end BalancedQuad

theorem ordinary_book_pure_block {s : ℕ} (C : Finset (Fin s)) (hC : 3≤ C.card)
    {k : ℕ} (hklo : C.card-1≤ k) (hkhi : k≤ C.card.choose 2-1) :
    Nonempty (WeightedPureBlock C ((s-1 : ℕ) : ℤ) (ordinaryBookTarget C) k) := by
  exact ⟨(Classical.choice (ordinary_book_block_interpolation C hC hklo hkhi)).toPureBlock⟩

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart161

section BundlePart162
/- Source: Papers/GraphicalZonotopes/ExactlyOneExpansion.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H : Type*} [Fintype H] [DecidableEq H]

def exactlyOne (S : Finset H) : ℝ:=if S.card=1 then 1 else 0

def exactlyOneCoefficient (n : ℕ) : ℝ:=
  if n=0 then 0 else (n : ℝ)*(-1 : ℝ)^(n-1)

theorem exactlyOneCoefficient_step (n : ℕ) :
    exactlyOneCoefficient n+exactlyOneCoefficient (n+1)=(-1 : ℝ)^n := by
  cases n with
  | zero => norm_num [exactlyOneCoefficient]
  | succ n =>
    simp only [exactlyOneCoefficient,Nat.add_one_ne_zero,Nat.succ_ne_zero,
      ite_false,Nat.add_sub_cancel,Nat.succ_sub_one,Nat.cast_add,Nat.cast_one,
      Nat.cast_succ,pow_succ]
    ring

theorem real_alternating_powerset (S : Finset H) :
    (∑ T∈S.powerset,(-1 : ℝ)^T.card)=if S=∅ then 1 else 0 := by
  have hi:=sum_powerset_neg_one_pow_card (x:=S)
  exact_mod_cast hi

/-- The full finite multilinear expansion of the exactly-one indicator.
It includes the empty coefficient and every subset of the ambient type. -/
theorem zeta_exactlyOneCoefficient :
    zeta (fun S : Finset H => exactlyOneCoefficient S.card)=exactlyOne := by
  funext S
  by_cases hS : S=∅
  · subst S
    simp [zeta,exactlyOneCoefficient,exactlyOne]
  · obtain ⟨a,ha⟩:=nonempty_iff_ne_empty.mpr hS
    let T:=S.erase a
    have haT : a∉T:=notMem_erase a S
    have he : insert a T=S:=insert_erase ha
    rw [← he]
    change (∑ U∈(insert a T).powerset,exactlyOneCoefficient U.card)=_
    rw [sum_powerset_insert haT,← sum_add_distrib]
    have hs : (∑ U∈T.powerset,
        (exactlyOneCoefficient U.card+exactlyOneCoefficient (insert a U).card))=
        ∑ U∈T.powerset,(-1 : ℝ)^U.card := by
      apply sum_congr rfl
      intro U hU
      have haU : a∉U:=fun h => haT ((mem_powerset.mp hU) h)
      rw [card_insert_of_notMem haU,exactlyOneCoefficient_step]
    rw [hs,real_alternating_powerset]
    simp only [exactlyOne,card_insert_of_notMem haT]
    have hn : T.card+1=1 ↔ T=∅:=by rw [← card_eq_zero]; omega
    simp only [hn]

def absentCoefficient (a : H) (y : SetFunction H) : SetFunction H:=
  fun T => if a∈T then -y (T.erase a) else y T

/-- Multiplication by the Boolean factor `(1-x_a)` in actual subset
coordinates, derived by cancelling the two halves of the powerset sum. -/
theorem zeta_absentCoefficient (a : H) (y : SetFunction H) (S : Finset H) :
    zeta (absentCoefficient a y) S=if a∈S then 0 else zeta y S := by
  by_cases ha : a∈S
  · let T:=S.erase a
    have haT : a∉T:=notMem_erase a S
    have he : insert a T=S:=insert_erase ha
    rw [if_pos ha,← he]
    unfold zeta
    rw [sum_powerset_insert haT]
    have hfirst : (∑ U∈T.powerset,absentCoefficient a y U)=∑ U∈T.powerset,y U := by
      apply sum_congr rfl
      intro U hU
      have haU : a∉U:=fun h => haT ((mem_powerset.mp hU) h)
      exact if_neg haU
    have hsecond : (∑ U∈T.powerset,absentCoefficient a y (insert a U))=
        -(∑ U∈T.powerset,y U) := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro U hU
      have haU : a∉U:=fun h => haT ((mem_powerset.mp hU) h)
      simp only [absentCoefficient,mem_insert_self,ite_true,erase_insert haU]
    rw [hfirst,hsecond,add_neg_cancel]
  · rw [if_neg ha]
    apply sum_congr rfl
    intro U hU
    have haU : a∉U:=fun h => ha ((mem_powerset.mp hU) h)
    exact if_neg haU

theorem zeta_absent_exactlyOne (a : H) (S : Finset H) :
    zeta (absentCoefficient a (fun T => exactlyOneCoefficient T.card)) S=
      if a∈S then 0 else exactlyOne S := by
  rw [zeta_absentCoefficient,zeta_exactlyOneCoefficient]

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart162

section BundlePart163
/- Source: Papers/GraphicalZonotopes/ThresholdBoolean.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
variable {H : Type*} [Fintype H] [DecidableEq H]

/-- The threshold module of Lemma 7.6. Counting the whole set in the second
disjunct is equivalent to counting the hubs other than `a`: the first
disjunct already makes the value one whenever `a` is present. -/
def thresholdStar (a : H) : SetFunction H :=
  fun S => if a∈S ∨ 2≤ S.card then 1 else 0

theorem thresholdStar_literal (a : H) (S : Finset H) :
    thresholdStar a S=if a∈S ∨ 2≤(S.erase a).card then 1 else 0 := by
  by_cases ha : a∈S
  · simp only [thresholdStar,ha,true_or,ite_true]
  · simp only [thresholdStar,ha,false_or,erase_eq_of_notMem ha]

theorem thresholdStar_boolean (a : H) : IsMonotoneBoolean (thresholdStar a) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro S T hST
    by_cases hS : a∈S ∨ 2≤ S.card
    · have hT : a∈T ∨ 2≤ T.card := by
        rcases hS with ha | hc
        · exact Or.inl (hST ha)
        · exact Or.inr (hc.trans (card_le_card hST))
      simp only [thresholdStar,if_pos hS,if_pos hT,le_refl]
    · by_cases hT : a∈T ∨ 2≤ T.card <;>
        simp only [thresholdStar,if_neg hS,hT,ite_true,ite_false] <;> norm_num
  · intro S
    by_cases hS : a∈S ∨ 2≤ S.card <;> simp only [thresholdStar,hS,ite_true,ite_false] <;> simp
  · simp [thresholdStar]
  · simp [thresholdStar]

theorem thresholdStar_eq_zero_iff (a : H) (S : Finset H) :
    thresholdStar a S=0 ↔ a∉S ∧ S.card<2 := by
  by_cases ha : a∈S
  · simp [thresholdStar,ha]
  · by_cases hc : 2≤ S.card
    · simp [thresholdStar,ha,hc,Nat.not_lt.mpr hc]
    · have hlt : S.card<2:=Nat.lt_of_not_ge hc
      simp [thresholdStar,ha,hc,hlt]

theorem thresholdStar_eq_one_iff (a : H) (S : Finset H) :
    thresholdStar a S=1 ↔ a∈S ∨ 2≤ S.card := by
  by_cases h : a∈S ∨ 2≤ S.card <;> simp only [thresholdStar,h,ite_true,ite_false] <;> norm_num

/-- Essentiality is witnessed by literal Boolean covers, including all
ambient hubs rather than only the distinguished one. -/
theorem thresholdStar_essential (hs : 3≤ Fintype.card H) (a i : H) :
    Essential (thresholdStar a) i := by
  by_cases hi : i=a
  · subst i
    refine ⟨∅,notMem_empty _,?_⟩
    simp [thresholdStar]
  · have hb : ∃ b : H,b≠ a ∧ b≠ i := by
      by_contra hn
      have hsub : (univ : Finset H)⊆{a,i} := by
        intro b hb
        by_cases hba : b=a
        · simp only [hba,mem_insert_self]
        · by_cases hbi : b=i
          · simp only [hbi,mem_insert,mem_singleton,or_true]
          · exact False.elim (hn ⟨b,hba,hbi⟩)
      have hc:=card_le_card hsub
      rw [card_univ,card_pair (Ne.symm hi)] at hc
      omega
    obtain ⟨b,hba,hbi⟩:=hb
    refine ⟨{b},by simpa only [mem_singleton] using Ne.symm hbi,?_⟩
    have hai : a≠ i:=Ne.symm hi
    have hab : a≠ b:=Ne.symm hba
    simp only [thresholdStar,mem_insert,mem_singleton,hai,hab,false_or,
      card_pair (Ne.symm hbi),card_singleton]
    norm_num

/-- Every actual pair response is the exactly-one indicator on its context,
with the distinguished hub excluded. The formula also covers pairs incident
with `a`, since their legitimate contexts already omit `a`. -/
theorem thresholdStar_negativeResponse (a : H) {u v : H} (huv : u≠ v)
    (S : Finset H) (hu : u∉S) (hv : v∉S) :
    negativeResponse (thresholdStar a) u v S=
      if a∈S then 0 else exactlyOne S := by
  have hone : negativeResponse (thresholdStar a) u v S=1 ↔ a∉S ∧ S.card=1 := by
    rw [negativeResponse_eq_one_iff (thresholdStar_boolean a),
      thresholdStar_eq_zero_iff,thresholdStar_eq_one_iff,thresholdStar_eq_one_iff]
    simp only [mem_insert,card_insert_of_notMem hu,card_insert_of_notMem hv]
    constructor
    · rintro ⟨⟨ha,hc⟩,hu',hv'⟩
      refine ⟨ha,?_⟩
      by_cases hpos : 1≤ S.card
      · omega
      · have hau : a=u := by
          rcases hu' with (hau | haS) | hcard
          · exact hau
          · exact False.elim (ha haS)
          · omega
        have hav : a=v := by
          rcases hv' with (hav | haS) | hcard
          · exact hav
          · exact False.elim (ha haS)
          · omega
        exact False.elim (huv (hau.symm.trans hav))
    · rintro ⟨ha,hc⟩
      exact ⟨⟨ha,by omega⟩,Or.inr (by omega),Or.inr (by omega)⟩
  rcases negativeResponse_values (thresholdStar_boolean a) u v S with hz | ho
  · have hn : ¬(a∉S ∧ S.card=1) := by
      intro h
      have hh:=hone.mpr h
      rw [hz] at hh
      norm_num at hh
    by_cases ha : a∈S
    · simp only [hz,if_pos ha]
    · have hc : S.card≠1:=fun h => hn ⟨ha,h⟩
      simp only [hz,if_neg ha,exactlyOne,if_neg hc]
  · obtain ⟨ha,hc⟩:=hone.mp ho
    simp only [ho,if_neg ha,exactlyOne,if_pos hc]

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart163

section BundlePart164
/- Source: Papers/GraphicalZonotopes/ThresholdResponse.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset PowersetTransform
variable {H : Type*} [Fintype H] [LinearOrder H]

def thresholdCoefficients (a : H) : HubResponseRow H → ℝ :=
  fun r => absentCoefficient a (fun T => exactlyOneCoefficient T.card) r.2.1

/-- The actual inverse of the pairwise response zeta transform, with every
context retained. This is computed from the Boolean function, not stipulated
as a response vector. -/
theorem thresholdStar_coefficients (a : H) :
    rowLowerEquiv.symm (responseVector (thresholdStar a))=thresholdCoefficients a := by
  apply rowLowerEquiv.injective
  rw [rowLowerEquiv.apply_symm_apply]
  funext r
  have hu : r.1.1.1∉r.2.1 := by
    intro h
    exact not_mem_commonNeighbors_left ⊤ _ _ ((mem_powerset.mp r.2.2) h)
  have hv : r.1.1.2∉r.2.1 := by
    intro h
    exact not_mem_commonNeighbors_right ⊤ _ _ ((mem_powerset.mp r.2.2) h)
  change negativeResponse (thresholdStar a) r.1.1.1 r.1.1.2 r.2.1=
    lowerSum (commonNeighbors (⊤ : SimpleGraph H) r.1.1.1 r.1.1.2)
      (fun T => absentCoefficient a (fun U => exactlyOneCoefficient U.card) T.1) r.2
  rw [lowerSum_restriction]
  change negativeResponse (thresholdStar a) r.1.1.1 r.1.1.2 r.2.1=
    zeta (absentCoefficient a (fun U => exactlyOneCoefficient U.card)) r.2.1
  rw [zeta_absent_exactlyOne,
    thresholdStar_negativeResponse a (ne_of_lt r.1.2.1) r.2.1 hu hv]

def thresholdSign (n : ℕ) : ℝ :=
  if n=0 then 0 else (-1 : ℝ)^(n-1)

theorem exactlyOneCoefficient_sub_sign (n : ℕ) (hn : 0< n) :
    exactlyOneCoefficient n-thresholdSign n= -exactlyOneCoefficient (n-1) := by
  have hs:=exactlyOneCoefficient_step (n-1)
  have he : n-1+1=n:=by omega
  rw [he] at hs
  rw [thresholdSign,if_neg (Nat.ne_of_gt hn)]
  linarith

theorem rowClique_card_eq_context_add_two (r : HubResponseRow H) :
    (rowClique r).card=r.2.1.card+2 := by
  have hu : r.1.1.1∉r.2.1 := by
    intro h
    exact not_mem_commonNeighbors_left ⊤ _ _ ((mem_powerset.mp r.2.2) h)
  have hv : r.1.1.2∉r.2.1 := by
    intro h
    exact not_mem_commonNeighbors_right ⊤ _ _ ((mem_powerset.mp r.2.2) h)
  have hu' : r.1.1.1∉insert r.1.1.2 r.2.1 := by
    simpa only [mem_insert,not_or] using And.intro (ne_of_lt r.1.2.1) hu
  simp only [rowClique,card_insert_of_notMem hu',card_insert_of_notMem hv]

def thresholdCommon (a : H) (C : Finset H) : ℝ :=
  exactlyOneCoefficient (C.card-2)-if a∈C then thresholdSign (C.card-2) else 0

/-- The literal signed-star representative appearing in equation (7.2),
including its zero value on blocks not containing the distinguished hub. -/
def thresholdSignedStar (a : H) : HubResponseRow H → ℝ :=
  fun r => if 3≤(rowClique r).card ∧ (a=r.1.1.1 ∨ a=r.1.1.2)
    then (-1 : ℝ)^((rowClique r).card-3) else 0

theorem thresholdSignedStar_eq (a : H) (r : HubResponseRow H) :
    thresholdSignedStar a r=
      if a=r.1.1.1 ∨ a=r.1.1.2 then thresholdSign r.2.1.card else 0 := by
  have hc:=rowClique_card_eq_context_add_two r
  by_cases ha : a=r.1.1.1 ∨ a=r.1.1.2
  · by_cases hn : r.2.1.card=0
    · have hC : ¬3≤(rowClique r).card:=by omega
      simp [thresholdSignedStar,ha,hC,thresholdSign,hn]
    · have hC : 3≤(rowClique r).card:=by omega
      have he : (rowClique r).card-3=r.2.1.card-1:=by omega
      simp [thresholdSignedStar,ha,hC,thresholdSign,hn,he]
  · simp only [thresholdSignedStar,ha,and_false,ite_false]

/-- Before passing to the quotient, the response differs from the signed
star by exactly one common coefficient on each full clique block. -/
theorem thresholdCoefficients_decomposition (a : H) :
    thresholdCoefficients a=
      (fun r : HubResponseRow H => thresholdCommon a (rowClique r))+
        thresholdSignedStar a := by
  funext r
  have hc:=rowClique_card_eq_context_add_two r
  have hsub : (rowClique r).card-2=r.2.1.card:=by omega
  have hu : r.1.1.1∉r.2.1 := by
    intro h
    exact not_mem_commonNeighbors_left ⊤ _ _ ((mem_powerset.mp r.2.2) h)
  have hv : r.1.1.2∉r.2.1 := by
    intro h
    exact not_mem_commonNeighbors_right ⊤ _ _ ((mem_powerset.mp r.2.2) h)
  simp only [Pi.add_apply,thresholdCoefficients,thresholdCommon,hsub,
    thresholdSignedStar_eq,absentCoefficient]
  by_cases hp : a=r.1.1.1 ∨ a=r.1.1.2
  · have ha : a∈rowClique r := by
      rcases hp with ha | ha
      · simp only [rowClique,ha,mem_insert_self]
      · simp [rowClique,ha]
    have haS : a∉r.2.1 := by
      rcases hp with ha | ha
      · simpa only [ha] using hu
      · simpa only [ha] using hv
    rw [if_neg haS,if_pos ha,if_pos hp]
    ring
  · by_cases haS : a∈r.2.1
    · have ha : a∈rowClique r:=mem_insert_of_mem (mem_insert_of_mem haS)
      have hn : 0< r.2.1.card:=card_pos.mpr ⟨a,haS⟩
      rw [if_pos haS,if_pos ha,if_neg hp,add_zero,card_erase_of_mem haS,
        exactlyOneCoefficient_sub_sign _ hn]
    · have ha : a∉rowClique r := by
        simp only [rowClique,mem_insert]
        intro h
        rcases h with h | h | h
        · exact hp (Or.inl h)
        · exact hp (Or.inr h)
        · exact haS h
      rw [if_neg haS,if_neg ha,if_neg hp,sub_zero,add_zero]

/-- Lemma 7.6 in the actual quotient by all central elemental responses.
There are no omitted contexts or unproved block-identification assumptions. -/
theorem thresholdStar_response_class (a : H) :
    responseClass (thresholdStar a)=coefficientClass (thresholdSignedStar a) := by
  rw [responseClass_eq_coefficientClass,thresholdStar_coefficients,
    thresholdCoefficients_decomposition,map_add]
  have hz : coefficientClass
      (fun r : HubResponseRow H => thresholdCommon a (rowClique r))=0 := by
    apply (coefficientClass_eq_zero_iff _).mpr
    intro r t hrt
    exact congrArg (thresholdCommon a) (congrArg Subtype.val hrt)
  rw [hz,zero_add]

theorem thresholdStar_response_lemma (hs : 3≤ Fintype.card H) (a : H) :
    IsMonotoneBoolean (thresholdStar a) ∧
    (∀ i,Essential (thresholdStar a) i) ∧
    responseClass (thresholdStar a)=coefficientClass (thresholdSignedStar a) :=
  ⟨thresholdStar_boolean a,thresholdStar_essential hs a,thresholdStar_response_class a⟩

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart164

section BundlePart165
/- Source: Papers/GraphicalZonotopes/BookCombinatorialCounts.lean -/







@[expose] public section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators

/-- Bounded integral sums attain every value between zero and their total
capacity. This supplies every intermediate branch count, uniformly. -/
theorem bounded_sum_composition {E : Type*} [DecidableEq E] (S : Finset E)
    (d : E → ℕ) {n : ℕ} (hn : n≤∑ i∈S,d i) :
    ∃ f : E → ℕ,(∀ i∈S,f i≤ d i) ∧ (∑ i∈S,f i)=n := by
  classical
  induction S using Finset.induction_on generalizing n with
  | empty =>
    have hn0 : n=0 := by simpa using hn
    exact ⟨fun _ => 0,by simp,by simp [hn0]⟩
  | @insert a S ha ih =>
    rw [sum_insert ha] at hn
    have hr : n-min (d a) n≤∑ i∈S,d i := by
      by_cases h : d a≤ n
      · rw [min_eq_left h]
        omega
      · rw [min_eq_right (by omega)]
        omega
    obtain ⟨f,hf,hfs⟩ := ih hr
    let g := fun i => if i=a then min (d a) n else f i
    refine ⟨g,?_,?_⟩
    · intro i hi
      rcases mem_insert.mp hi with rfl | hi
      · simp only [g,ite_true]
        exact min_le_left _ _
      · have hia : i≠ a := fun h => ha (h ▸ hi)
        simpa only [g,ite_eq_right hia] using hf i hi
    · rw [sum_insert ha]
      have hg : (∑ i∈S,g i)=∑ i∈S,f i := by
        apply sum_congr rfl
        intro i hi
        change (if i=a then min (d a) n else f i)=f i
        exact ite_eq_right (fun (h : i=a) => ha (h ▸ hi))
      rw [hg,hfs]
      simp only [g,ite_true]
      omega

theorem positive_sum_composition {B : Type*} [Fintype B] [DecidableEq B]
    (d : B → ℕ) (hd : ∀ b,1≤ d b) {n : ℕ}
    (hnlo : Fintype.card B≤ n) (hnhi : n≤∑ b,d b) :
    ∃ k : B → ℕ,(∀ b,1≤ k b ∧ k b≤ d b) ∧ (∑ b,k b)=n := by
  classical
  have hsum : (∑ b,(d b-1))+Fintype.card B=∑ b,d b := by
    calc
      _ = ∑ b,((d b-1)+1) := by simp [sum_add_distrib]
      _ = _ := sum_congr rfl (fun b _ => Nat.sub_add_cancel (hd b))
  obtain ⟨f,hf,hfs⟩ := bounded_sum_composition (univ : Finset B) (fun b => d b-1)
    (n:=n-Fintype.card B) (by omega)
  refine ⟨fun b => f b+1,?_,?_⟩
  · intro b
    have h := hf b (mem_univ b)
    have hdb := hd b
    change 1≤ f b+1 ∧ f b+1≤ d b
    constructor <;> omega
  · rw [sum_add_distrib,hfs]
    simp only [sum_const,card_univ,nsmul_eq_mul,mul_one,Nat.cast_id]
    omega

section Powersets
variable {H : Type*} [DecidableEq H]

def blockDimensionSum (S : Finset H) : ℕ :=
  ∑ C∈S.powerset,(C.card.choose 2-1)

def nontrivialSubsets (S : Finset H) : Finset (Finset H) :=
  S.powerset.filter (fun C => 2≤ C.card)

theorem small_subsets_card (S : Finset H) :
    (S.powerset.filter (fun C => ¬2≤ C.card)).card=S.card+1 := by
  have he : S.powerset.filter (fun C => ¬2≤ C.card)=insert ∅ (S.image singleton) := by
    ext C
    simp only [mem_filter,mem_powerset,mem_insert,mem_image]
    constructor
    · rintro ⟨hCS,hC⟩
      have hc : C.card=0 ∨ C.card=1 := by omega
      rcases hc with hc | hc
      · exact Or.inl (card_eq_zero.mp hc)
      · obtain ⟨a,rfl⟩ := card_eq_one.mp hc
        exact Or.inr ⟨a,hCS (mem_singleton_self a),rfl⟩
    · rintro (rfl | ⟨a,ha,rfl⟩)
      · simp
      · simp [singleton_subset_iff,ha]
  rw [he,card_insert_of_notMem]
  · rw [card_image_of_injective _ singleton_injective]
  · simp

theorem nontrivialSubsets_card (S : Finset H) :
    (nontrivialSubsets S).card=2^S.card-S.card-1 := by
  have h := card_filter_add_card_filter_not (s:=S.powerset) (p:=fun C => 2≤ C.card)
  rw [small_subsets_card,card_powerset] at h
  change (S.powerset.filter (fun C => 2≤ C.card)).card=_
  omega

theorem sum_powerset_card (S : Finset H) :
    (∑ C∈S.powerset,C.card)=S.card*2^(S.card-1) := by
  rw [sum_powerset_apply_card (fun n : ℕ => n)]
  simpa only [nsmul_eq_mul,Nat.mul_comm,Nat.cast_id] using Nat.sum_range_mul_choose S.card

theorem sum_powerset_choose_two (S : Finset H) :
    (∑ C∈S.powerset,C.card.choose 2)=S.card.choose 2*2^(S.card-2) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [sum_powerset_insert ha]
    have ht : ∀ T∈S.powerset,(insert a T).card.choose 2=T.card+T.card.choose 2 := by
      intro T hT
      have haT : a∉T := fun h => ha ((mem_powerset.mp hT) h)
      rw [card_insert_of_notMem haT]
      simpa only [Nat.choose_one_right] using Nat.choose_succ_succ T.card 1
    have ht' : (∑ T∈S.powerset,(insert a T).card.choose 2)=
        ∑ T∈S.powerset,(T.card+T.card.choose 2) := sum_congr rfl ht
    rw [ht']
    rw [sum_add_distrib,ih,sum_powerset_card,card_insert_of_notMem ha]
    by_cases h0 : S.card=0
    · norm_num [h0]
    by_cases h1 : S.card=1
    · norm_num [h1]
    have hn : 2≤ S.card := by omega
    have he : S.card+1-2=S.card-1 := by omega
    have he' : S.card-2+1=S.card-1 := by omega
    have hp : 2^(S.card-1)=2^(S.card-2)*2 := by rw [← he',pow_succ]
    have hc : (S.card+1).choose 2=S.card+S.card.choose 2 := by
      simpa only [Nat.choose_one_right] using Nat.choose_succ_succ S.card 1
    rw [hc,he,hp]
    ring

theorem blockDimensionSum_add_cliques (S : Finset H) :
    blockDimensionSum S+(nontrivialSubsets S).card=∑ C∈S.powerset,C.card.choose 2 := by
  have hd : blockDimensionSum S=∑ C∈nontrivialSubsets S,(C.card.choose 2-1) := by
    symm
    unfold blockDimensionSum nontrivialSubsets
    apply sum_subset (filter_subset _ _)
    intro C hC hn
    have hc : ¬2≤ C.card := fun h => hn (mem_filter.mpr ⟨hC,h⟩)
    have hchoose : C.card.choose 2=0 := Nat.choose_eq_zero_of_lt (by omega)
    simp only [hchoose,Nat.zero_sub]
  have hc : (∑ C∈nontrivialSubsets S,C.card.choose 2)=∑ C∈S.powerset,C.card.choose 2 := by
    apply sum_subset (filter_subset _ _)
    intro C hC hn
    exact Nat.choose_eq_zero_of_lt (by
      have h : ¬2≤ C.card := fun h => hn (mem_filter.mpr ⟨hC,h⟩)
      omega)
  rw [hd,← hc]
  calc
    _ = ∑ C∈nontrivialSubsets S,((C.card.choose 2-1)+1) := by simp [sum_add_distrib]
    _ = _ := by
      apply sum_congr rfl
      intro C hC
      exact Nat.sub_add_cancel (Nat.choose_pos (mem_filter.mp hC).2)

theorem blockDimensionSum_eq (S : Finset H) :
    blockDimensionSum S=S.card.choose 2*2^(S.card-2)-(2^S.card-S.card-1) := by
  have h := blockDimensionSum_add_cliques S
  rw [nontrivialSubsets_card,sum_powerset_choose_two] at h
  omega

theorem cliqueCapacity_eq_dimension_sum (S : Finset H) :
    cliqueCapacity S.card=blockDimensionSum S+1 := by
  rw [blockDimensionSum_eq]
  rfl

end Powersets
end BooleanModule
end GraphicalZonotopes

end
end BundlePart165

section BundlePart166
/- Source: Papers/GraphicalZonotopes/BlockFamilies.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H : Type*} [Fintype H] [LinearOrder H]

/-- Independent clique blocks remain independent in the actual quotient by
all central coefficients. This proves the direct-sum assertion, rather than
assuming an identification with a synthetic coordinate space. -/
theorem block_sum_zero_component {B : Type*} [Fintype B] [DecidableEq B]
    (C : B → Finset H) (hC : Function.Injective C)
    (e₀ : ∀ b,PairIn (C b)) (x : ∀ b,PairIn (C b) → ℝ)
    (hz : (∑ b,blockClass (C b) (x b))=0) (b : B) :
    blockClass (C b) (x b)=0 := by
  have hraw : coefficientClass (∑ c,blockCoordinates (C c) (x c))=0 := by
    simpa only [map_sum,blockClass,LinearMap.comp_apply] using hz
  have heval : ∀ e : PairIn (C b),
      (∑ c,blockCoordinates (C c) (x c)) (pairRow (C b) e)=x b e := by
    intro e
    rw [Finset.sum_apply]
    rw [sum_eq_single b]
    · exact blockCoordinates_pairRow (C b) (x b) e
    · intro c hc hcb
      have hne : rowClique (pairRow (C b) e)≠ C c := by
        rw [rowClique_pairRow]
        exact fun h => hcb (hC h.symm)
      change (if h : rowClique (pairRow (C b) e)=C c then
        x c (pairAtRow (C c) (pairRow (C b) e) h) else 0)=0
      exact dite_eq_right hne
    · simp
  apply (blockClass_eq_zero_iff (C b) (e₀ b) (x b)).mpr
  refine ⟨x b (e₀ b),?_⟩
  intro e
  have hrows : rowCliqueIndex (pairRow (C b) e)=rowCliqueIndex (pairRow (C b) (e₀ b)) := by
    apply Subtype.ext
    exact (rowClique_pairRow (C b) e).trans (rowClique_pairRow (C b) (e₀ b)).symm
  have hh := (coefficientClass_eq_zero_iff _).mp hraw _ _ hrows
  simpa only [heval] using hh

theorem block_families_independent {B : Type*} [Fintype B] [DecidableEq B]
    (C : B → Finset H) (hC : Function.Injective C) (e₀ : ∀ b,PairIn (C b))
    {J : B → Type*} [∀ b,Fintype (J b)]
    (x : ∀ b,J b → PairIn (C b) → ℝ)
    (hx : ∀ b,LinearIndependent ℝ (fun j => blockClass (C b) (x b j))) :
    LinearIndependent ℝ (fun j : Sigma J => blockClass (C j.1) (x j.1 j.2)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  let y := fun b => ∑ i : J b,c ⟨b,i⟩ • x b i
  have hy : (∑ b,blockClass (C b) (y b))=0 := by
    rw [Fintype.sum_sigma] at hc
    simpa only [y,map_sum,map_smul] using hc
  have hj := block_sum_zero_component C hC e₀ y hy j.1
  have hji : (∑ i : J j.1,c ⟨j.1,i⟩ • blockClass (C j.1) (x j.1 i))=0 := by
    simpa only [y,map_sum,map_smul] using hj
  exact (Fintype.linearIndependent_iff.mp (hx j.1)) _ hji j.2

theorem pureDecompositions_independent {B : Type*} [Fintype B] [DecidableEq B]
    (C : B → Finset H) (hC : Function.Injective C) (hsize : ∀ b,2≤(C b).card)
    (v : B → ResponseQuotient H) (k : B → ℕ)
    (P : ∀ b,PureDecomposition (C b) (v b) (k b)) :
    LinearIndependent ℝ (fun j : Σ b,Fin (k b) => responseClass ((P j.1).functions j.2)) := by
  classical
  choose x hx using fun b j => (P b).block_supported j
  have hex : ∀ b,∃ e : PairIn (C b),True := by
    intro b
    obtain ⟨e,he⟩ := cliquePairs_nonempty (C b) (C b) (Subset.refl _) (hsize b)
    exact ⟨e,trivial⟩
  choose e₀ he₀ using hex
  have hi : ∀ b,LinearIndependent ℝ (fun j => blockClass (C b) (x b j)) := by
    intro b
    simpa only [← hx] using (P b).independent
  simpa only [hx] using block_families_independent C hC e₀ x hi

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart166

section BundlePart167
/- Source: Papers/GraphicalZonotopes/BookBlockCoordinates.lean -/







@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators

variable {H : Type*} [Fintype H] [LinearOrder H]

def largeBlocks (S : Finset H) : Finset (Finset H) :=
  S.powerset.filter (fun C => 3≤ C.card)

@[simp] theorem mem_largeBlocks {S C : Finset H} :
    C∈largeBlocks S ↔ C⊆S ∧ 3≤ C.card := by
  simp only [largeBlocks,mem_filter,mem_powerset]

abbrev BookBlock (H : Type*) [Fintype H] [LinearOrder H] :=
  ↥(largeBlocks (univ : Finset H))

def endpointCoefficients (C : Finset H) (d : H → ℝ) : PairIn C → ℝ :=
  fun e => d e.1.1.1+d e.1.1.2

theorem sum_full_stars (C : Finset H) (d : H → ℝ) :
    (∑ a,d a • starVector C a)=endpointCoefficients C d := by
  funext e
  have huv : e.1.1.1≠ e.1.1.2 := ne_of_lt e.1.2.1
  have he : ∀ a,starVector C a e=
      (if a=e.1.1.1 then (1 : ℝ) else 0)+(if a=e.1.1.2 then 1 else 0) := by
    intro a
    rw [starVector_eq]
    by_cases hu : a=e.1.1.1
    · have hv : a≠ e.1.1.2 := fun h => huv (hu.symm.trans h)
      simp [hu,hv,huv,Ne.symm huv]
    · by_cases hv : a=e.1.1.2 <;> simp [hu,hv,huv,Ne.symm huv]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,he,mul_add,sum_add_distrib,
    mul_ite,mul_one,mul_zero]
  simp only [sum_ite_eq',mem_univ,ite_true,endpointCoefficients]

/-- A threshold module's full coefficient response over all actual clique
blocks. Blocks that do not contain its distinguished vertex contribute zero. -/
theorem threshold_response_largeBlocks (a : H) :
    responseClass (thresholdStar a)=∑ C : BookBlock H,
      (-1 : ℝ)^(C.1.card-3) • blockClass C.1 (starVector C.1 a) := by
  have hcoord : thresholdSignedStar a=∑ C : BookBlock H,
      (-1 : ℝ)^(C.1.card-3) • blockCoordinates C.1 (starVector C.1 a) := by
    funext r
    rw [Finset.sum_apply]
    by_cases hr : 3≤(rowClique r).card
    · let C₀ : BookBlock H := ⟨rowClique r,mem_largeBlocks.mpr ⟨subset_univ _,hr⟩⟩
      rw [sum_eq_single C₀]
      · change thresholdSignedStar a r=
          (-1 : ℝ)^((rowClique r).card-3)*
            blockCoordinates (rowClique r) (starVector (rowClique r) a) r
        have he : blockCoordinates (rowClique r) (starVector (rowClique r) a) r=
            starVector (rowClique r) a (pairAtRow (rowClique r) r rfl) := by
          change (if h : rowClique r=rowClique r then
            starVector (rowClique r) a (pairAtRow (rowClique r) r h) else 0)=_
          rw [dite_eq_left rfl]
        rw [he,starVector_eq]
        change (if 3≤(rowClique r).card ∧ (a=r.1.1.1 ∨ a=r.1.1.2) then
          (-1 : ℝ)^((rowClique r).card-3) else 0)=
          (-1 : ℝ)^((rowClique r).card-3)*(if a=r.1.1.1 ∨ a=r.1.1.2 then 1 else 0)
        by_cases h : a=r.1.1.1 ∨ a=r.1.1.2 <;> simp [hr,h]
      · intro C hC hne
        have hrow : rowClique r≠ C.1 := fun h => hne (Subtype.ext h.symm)
        change (-1 : ℝ)^(C.1.card-3)*
          (if h : rowClique r=C.1 then starVector C.1 a (pairAtRow C.1 r h) else 0)=0
        rw [dite_eq_right hrow,mul_zero]
      · simp
    · rw [sum_eq_zero]
      · simp only [thresholdSignedStar,hr,false_and,ite_false]
      · intro C hC
        have hrow : rowClique r≠ C.1 := fun h => hr (h ▸ (mem_largeBlocks.mp C.2).2)
        change (-1 : ℝ)^(C.1.card-3)*
          (if h : rowClique r=C.1 then starVector C.1 a (pairAtRow C.1 r h) else 0)=0
        rw [dite_eq_right hrow,mul_zero]
  rw [thresholdStar_response_class,hcoord,map_sum]
  apply sum_congr rfl
  intro C hC
  rw [map_smul]
  rfl

/-- The coefficients of an arbitrary linear combination of threshold modules
are endpoint sums on every clique block, with the exact alternating sign. -/
theorem weighted_threshold_response (d : H → ℝ) :
    (∑ a,d a • responseClass (thresholdStar a))=
      ∑ C : BookBlock H,(-1 : ℝ)^(C.1.card-3) •
        blockClass C.1 (endpointCoefficients C.1 d) := by
  simp_rw [threshold_response_largeBlocks,smul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro C hC
  calc
    _ = (-1 : ℝ)^(C.1.card-3) •
        blockClass C.1 (∑ a,d a • starVector C.1 a) := by
      simp only [map_sum,map_smul,smul_sum]
      apply sum_congr rfl
      intro a ha
      exact smul_comm _ _ _
    _ = _ := by rw [sum_full_stars]

/-- Every actual block in the decomposition has its full constant kernel,
independently of all other blocks. -/
theorem book_block_sum_zero_component
    (x : (C : BookBlock H) → PairIn C.1 → ℝ)
    (hz : (∑ C : BookBlock H,blockClass C.1 (x C))=0) :
    ∀ C,∃ c : ℝ,∀ e,x C e=c := by
  classical
  have hp : ∀ C : BookBlock H,∃ e : PairIn C.1,True := by
    intro C
    obtain ⟨e,he⟩ := cliquePairs_nonempty C.1 C.1 (Subset.refl _)
      (by have h := (mem_largeBlocks.mp C.2).2; omega)
    exact ⟨e,trivial⟩
  let e₀ := fun C => (hp C).choose
  have he := block_sum_zero_component Subtype.val Subtype.val_injective e₀ x hz
  intro C
  exact (blockClass_eq_zero_iff C.1 (e₀ C) (x C)).mp (he C)

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart167

section BundlePart168
/- Source: Papers/GraphicalZonotopes/IntegralBooleanResponse.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset PowersetTransform
open scoped BigOperators
variable {H J : Type*} [Fintype H] [LinearOrder H] [Fintype J] [DecidableEq J]

def integerSubring : Subring ℝ:=(Int.castRingHom ℝ).range

theorem mem_integerSubring_iff (x : ℝ) :
    x∈integerSubring ↔ ∃ a : ℤ,x=(a : ℝ) := by
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a,ha.symm⟩
  · rintro ⟨a,ha⟩
    exact ⟨a,ha.symm⟩

theorem rowLower_symm_mem_subring (K : Subring ℝ) (x : HubResponseRow H → ℝ)
    (hx : ∀ r,x r∈K) : ∀ r,rowLowerEquiv.symm x r∈K := by
  intro r
  exact lowerEquiv_symm_mem_subring
    (commonNeighbors (⊤ : SimpleGraph H) r.1.1.1 r.1.1.2) K
    (fun T => x ⟨r.1,T⟩) (fun T => hx ⟨r.1,T⟩) r.2

theorem weightedResponse_integer (F : J → SetFunction H)
    (hF : ∀ j,IsMonotoneBoolean (F j)) (w : J → ℤ) :
    ∀ r,weightedResponse F (fun j => (w j : ℝ)) r∈integerSubring := by
  intro r
  apply integerSubring.sum_mem
  intro j hj
  apply integerSubring.mul_mem
  · exact (mem_integerSubring_iff _).mpr ⟨w j,rfl⟩
  · rcases negativeResponse_values (hF j) r.1.1.1 r.1.1.2 r.2.1 with h | h
    · change negativeResponse (F j) _ _ _∈integerSubring
      rw [h]
      exact integerSubring.zero_mem
    · change negativeResponse (F j) _ _ _∈integerSubring
      rw [h]
      exact integerSubring.one_mem

/-- Whenever integral pair-response coefficients are integrable over the
reals, their central lift already has integral Möbius coefficients. No
unproved rationality or saturation assertion is used. -/
theorem central_integral_lift (x : HubResponseRow H → ℝ)
    (hx : ∀ r,x r∈integerSubring)
    (hblock : BlockConstant (rowLowerEquiv.symm x)) :
    ∃ c : CliqueIndex (⊤ : SimpleGraph H) → ℝ,
      (∀ C,c C∈integerSubring) ∧ centralCoefficientSlack c=x := by
  obtain ⟨c,hc⟩:=(blockConstant_iff_range_repeatCoefficients _).mp hblock
  have hi:=rowLower_symm_mem_subring integerSubring x hx
  refine ⟨c,?_,?_⟩
  · intro C
    obtain ⟨r,hr⟩:=rowCliqueIndex_surjective C
    have he:=congrFun hc r
    change c (rowCliqueIndex r)=rowLowerEquiv.symm x r at he
    rw [hr] at he
    rw [he]
    exact hi r
  · rw [← rowLower_repeatCoefficients,hc,rowLowerEquiv.apply_symm_apply]

/-- The integral central lift used by every Boolean-module construction in
Section7, stated for arbitrary finite hub and branch sets. -/
theorem integral_compatible_lift (F : J → SetFunction H)
    (hF : ∀ j,IsMonotoneBoolean (F j)) (w : J → ℤ)
    (hrel : (fun j => (w j : ℝ))∈LinearMap.ker (quotientRelation F)) :
    ∃ z : SetFunction H,TranslationNormalized z ∧ IntegerValued z ∧
      Compatible z F (fun j => (w j : ℝ)) := by
  have hi:=weightedResponse_integer F hF w
  have hb : BlockConstant (rowLowerEquiv.symm (weightedResponse F (fun j => (w j : ℝ)))) :=
    (integrable_iff_blockConstant F _).mp ((mem_quotientRelation_ker_iff F _).mp hrel)
  obtain ⟨c,hci,hc⟩:=central_integral_lift _ hi hb
  let y:=coefficientsFromCoordinates (⊤ : SimpleGraph H) c
  let z:=zeta y
  have hn : TranslationNormalized z:=(graphicalCoordinatesEquiv ⊤ c).2.1
  have hyi : IntegerValued y := by
    intro C
    by_cases hC : IsCliqueCoordinate (⊤ : SimpleGraph H) C
    · change (∃ a : ℤ,coefficientsFromCoordinates ⊤ c C=(a : ℝ))
      rw [coefficientsFromCoordinates,dif_pos hC]
      exact (mem_integerSubring_iff _).mp (hci ⟨C,hC⟩)
    · exact ⟨0,by simp only [y,coefficientsFromCoordinates,dif_neg hC,Int.cast_zero]⟩
  refine ⟨z,hn,zeta_integerValued hyi,?_⟩
  apply (compatible_iff_rows hn F _).mpr
  exact hc

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart168

section BundlePart169
/- Source: Papers/GraphicalZonotopes/WeightedBookGeometry.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise

/-- One branch depending on every hub joins all remaining nonconstant
branches. Other branches may ignore arbitrarily many of the hubs. -/
theorem essentialSpokeGraph_connected_of_anchor
    {H J : Type*} [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]
    [Nonempty H] (F : J → SetFunction H) (j₀ : J)
    (hanchor : ∀ a, Essential (F j₀) a)
    (hbranch : ∀ j, ∃ a, Essential (F j) a) :
    (essentialSpokeGraph F).Connected := by
  letI : Nonempty J := ⟨j₀⟩
  have hhub : ∀ a, (essentialSpokeGraph F).Reachable (Sum.inl a) (Sum.inr j₀) :=
    fun a => (show (essentialSpokeGraph F).Adj (Sum.inl a) (Sum.inr j₀)
      from hanchor a).reachable
  have hreach : ∀ x, (essentialSpokeGraph F).Reachable x (Sum.inr j₀) := by
    intro x
    cases x with
    | inl a => exact hhub a
    | inr j =>
      obtain ⟨a,ha⟩ := hbranch j
      exact (show (essentialSpokeGraph F).Adj (Sum.inl a) (Sum.inr j)
        from ha).reachable.symm.trans (hhub a)
  exact ⟨fun x y => (hreach x).trans (hreach y).symm⟩

/-- Integral complementary polytope for any integral dilation at least the
sum of the positive branch scales. The complement is constructed from its
supermodular set function, not merely inferred from numerical containment. -/
theorem assembled_lattice_complement_of_weight_sum_le {s k : ℕ}
    {z : SetFunction (Fin s)} (hz : TranslationNormalized z) (hzi : IntegerValued z)
    {F : Fin k → SetFunction (Fin s)} (hF : ∀ j, IsMonotoneBoolean (F j))
    (w : Fin k → ℤ) (hw : ∀ j, 0 ≤ w j)
    (hc : Compatible z F (fun j => (w j : ℝ)))
    (M : ℤ) (hM : ∑ j, w j ≤ M) :
    LatticePolytope (basePolytope (assembled z F (fun j => (w j : ℝ)))) ∧
    ∃ R : Set ((Fin s ⊕ Fin k) → ℝ), LatticePolytope R ∧ R.Nonempty ∧
      basePolytope (assembled z F (fun j => (w j : ℝ))) + R =
        (M : ℝ) • graphicalZonotope (cliqueBook s k) := by
  let f := assembled z F (fun j => (w j : ℝ))
  have hw' : ∀ j, 0 ≤ (w j : ℝ) := fun j => by exact_mod_cast hw j
  have hn := assembled_normalized hz F hF (fun j => (w j : ℝ))
  have hs := assembled_supermodular z F hF (fun j => (w j : ℝ)) hw' hc
  have hi := assembled_integerValued hzi F hF w
  have hG := assembled_graphical z F (fun j => (w j : ℝ))
  have hsum : (∑ j, (w j : ℝ)) ≤ (M : ℝ) := by exact_mod_cast hM
  have ha : 0 ≤ (M : ℝ) := (sum_nonneg (fun j _ => hw' j)).trans hsum
  have hbound : ∀ u v, u ≠ v → (cliqueBook s k).Adj u v → ∀ A,
      u ∉ A → v ∉ A → delta f u v A ≤ (M : ℝ) := by
    intro u v huv hedge A hu hv
    exact (assembled_delta_le_weight_sum hF hw' hc u v huv A hu hv).trans hsum
  let g : SetFunction (Fin s ⊕ Fin k) := (M : ℝ) • graphFunction (cliqueBook s k) - f
  have hgn : Normalized g := by
    change (M : ℝ) * graphFunction (cliqueBook s k) ∅ - f ∅ = 0
    have hf0 : f ∅ = 0 := hn.1
    rw [graphFunction_normalized, hf0, mul_zero, sub_self]
  have hgs : Supermodular g := graphical_complement_supermodular hG ha hbound
  have hgi : IntegerValued g :=
    ((graphFunction_integerValued (cliqueBook s k)).int_smul M).sub hi
  exact ⟨hi.basePolytope hn.1 hs, basePolytope g, hgi.basePolytope hgn hgs,
    basePolytope_nonempty hgn hgs,
    basePolytope_add_graphical_complement hn.1 hs hG ha hbound⟩

/-- A positive integral circuit in the actual response quotient yields a
full dimensional indecomposable lattice polytope and an integral complement.
Every ambient hub and every branch remains present in the dimension claim. -/
theorem lattice_book_of_weighted_modules {s k : ℕ} (hk : 0 < k)
    (F : Fin k → SetFunction (Fin s)) (hF : ∀ j, IsMonotoneBoolean (F j))
    (w : Fin k → ℤ) (hw : ∀ j, 0 < w j)
    (hconn : (essentialSpokeGraph F).Connected)
    (hrel : (fun j => (w j : ℝ)) ∈ LinearMap.ker (quotientRelation F))
    (huniq : UniqueIntegrableRelation F (fun j => (w j : ℝ)))
    (M : ℤ) (hM : ∑ j, w j ≤ M) :
    ∃ f : SetFunction (Fin s ⊕ Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s ⊕ Fin k) → ℝ), LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f + R = (M : ℝ) • graphicalZonotope (cliqueBook s k) := by
  obtain ⟨z,hzn,hzi,hc⟩ := integral_compatible_lift F hF w hrel
  have hw' : ∀ j, 0 < (w j : ℝ) := fun j => by exact_mod_cast hw j
  let f := assembled z F (fun j => (w j : ℝ))
  have hn : TranslationNormalized f := assembled_normalized hzn F hF _
  have hi : IntegerValued f := assembled_integerValued hzi F hF w
  have he : ExtremeSupermodular f := positive_circuit_extreme hzn hF
    (fun j => (hw' j).le) ⟨⟨0,hk⟩,ne_of_gt (hw' ⟨0,hk⟩)⟩ hc huniq
  have hd : FullDimension (basePolytope f) :=
    assembled_fullDimension hzn hF hw' hc hconn
  obtain ⟨hl,R,hR,hnR,hQR⟩ := assembled_lattice_complement_of_weight_sum_le
    hzn hzi hF w (fun j => (hw j).le) hc M hM
  exact ⟨f,hn,hi,he,assembled_graphical z F _,hd,
    he.minkowskiIndecomposable,hl,R,hR,hnR,hQR⟩

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart169

section BundlePart170
/- Source: Papers/GraphicalZonotopes/ResponseBlockHelpers.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H J : Type*} [Fintype H] [LinearOrder H] [Fintype J]

/-- The genuine row belonging to a hub pair with every other hub present. -/
def fullRow (e : OrientedEdge (⊤ : SimpleGraph H)) : HubResponseRow H :=
  ⟨e,⟨commonNeighbors ⊤ e.1.1 e.1.2,mem_powerset.mpr (subset_refl _)⟩⟩

@[simp] theorem fullRow_edge (e : OrientedEdge (⊤ : SimpleGraph H)) :
    (fullRow e).1=e := rfl

@[simp] theorem rowClique_fullRow (e : OrientedEdge (⊤ : SimpleGraph H)) :
    rowClique (fullRow e)=univ := by
  ext a
  simp only [rowClique,fullRow,mem_insert,mem_commonNeighbors,SimpleGraph.top_adj,mem_univ,iff_true]
  by_cases ha : a=e.1.1
  · exact Or.inl ha
  · by_cases hb : a=e.1.2
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr ⟨Ne.symm ha,Ne.symm hb⟩)

def fullBlock (x : OrientedEdge (⊤ : SimpleGraph H) → ℝ) : HubResponseRow H → ℝ :=
  fun r => if rowClique r=univ then x r.1 else 0

/-- For an array supported on the full hub block, the actual integrability
condition is precisely equality of all pair coordinates of that block. -/
theorem fullBlock_constant_iff (x : OrientedEdge (⊤ : SimpleGraph H) → ℝ)
    [Nonempty (OrientedEdge (⊤ : SimpleGraph H))] :
    BlockConstant (fullBlock x) ↔ ∃ c : ℝ,∀ e,x e=c := by
  constructor
  · intro hx
    obtain ⟨e₀⟩:=‹Nonempty (OrientedEdge (⊤ : SimpleGraph H))›
    refine ⟨x e₀,?_⟩
    intro e
    have he : rowCliqueIndex (fullRow e)=rowCliqueIndex (fullRow e₀) := by
      apply Subtype.ext
      simp only [rowCliqueIndex,rowClique_fullRow]
    simpa only [fullBlock,rowClique_fullRow,ite_true,fullRow_edge] using hx _ _ he
  · rintro ⟨c,hc⟩ r t he
    have hrt : rowClique r=rowClique t:=congrArg Subtype.val he
    simp only [fullBlock,hrt,hc]

theorem rowLower_symm_weightedResponse (F : J → SetFunction H) (w : J → ℝ) :
    rowLowerEquiv.symm (weightedResponse F w)=
      ∑ j : J,w j • rowLowerEquiv.symm (responseVector (F j)) := by
  have he : weightedResponse F w=∑ j : J,w j • responseVector (F j) := by
    funext r
    simp only [weightedResponse,LinearMap.coe_mk,AddHom.coe_mk,
      Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [he,map_sum]
  apply sum_congr rfl
  intro j hj
  exact map_smul rowLowerEquiv.symm (w j) (responseVector (F j))

theorem weightedResponse_reindex {K : Type*} [Fintype K]
    (e : K≃J) (F : J → SetFunction H) (w : K → ℝ) :
    weightedResponse (fun k => F (e k)) w=
      weightedResponse F (fun j => w (e.symm j)) := by
  funext r
  change (∑ k : K,w k*responseVector (F (e k)) r)=
    ∑ j : J,w (e.symm j)*responseVector (F j) r
  simpa only [e.symm_apply_apply] using
    e.sum_comp (fun j => w (e.symm j)*responseVector (F j) r)

theorem compatible_reindex {K : Type*} [Fintype K]
    (e : K≃J) (z : SetFunction H) (F : J → SetFunction H) (w : K → ℝ) :
    Compatible z (fun k => F (e k)) w ↔
      Compatible z F (fun j => w (e.symm j)) := by
  have hs : ∀ u v S,(∑ k : K,w k*negativeResponse (F (e k)) u v S)=
      ∑ j : J,w (e.symm j)*negativeResponse (F j) u v S := by
    intro u v S
    simpa only [e.symm_apply_apply] using
      e.sum_comp (fun j => w (e.symm j)*negativeResponse (F j) u v S)
  unfold Compatible
  simp only [hs]

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart170

section BundlePart171
/- Source: Papers/GraphicalZonotopes/AnchoredBooleanCircuits.lean -/








@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise
variable {H J : Type*} [Fintype H] [LinearOrder H] [Fintype J] [DecidableEq J]

theorem quotientRelation_apply_eq_sum (F : J → SetFunction H) (w : J → ℝ) :
    quotientRelation F w=∑ j,w j • responseClass (F j) := by
  have he : weightedResponse F w=∑ j,w j • responseVector (F j) := by
    funext r
    simp only [weightedResponse,LinearMap.coe_mk,AddHom.coe_mk,
      Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  change (LinearMap.range centralCoefficientSlack).mkQ (weightedResponse F w)=_
  rw [he,map_sum]
  simp only [map_smul,responseClass]

def anchoredFamily (F₀ : SetFunction H) (F : J → SetFunction H) : Option J → SetFunction H
  | none => F₀
  | some j => F j

/-- One distinguished column plus an independent family with vanishing
unit sum has precisely the unit relation line in the full quotient. -/
theorem anchored_unit_relation (F₀ : SetFunction H) (F : J → SetFunction H)
    (hind : LinearIndependent ℝ (fun j => responseClass (F j)))
    (hsum : responseClass F₀+∑ j,responseClass (F j)=0) :
    (fun _ : Option J => (1 : ℝ))∈LinearMap.ker (quotientRelation (anchoredFamily F₀ F)) ∧
      UniqueIntegrableRelation (anchoredFamily F₀ F) (fun _ => 1) := by
  constructor
  · change quotientRelation (anchoredFamily F₀ F) (fun _ => 1)=0
    rw [quotientRelation_apply_eq_sum,Fintype.sum_option]
    simpa only [one_smul,anchoredFamily] using hsum
  · intro t ht
    have ht0 : quotientRelation (anchoredFamily F₀ F) t=0 :=
      (mem_quotientRelation_ker_iff _ _).mpr ht
    rw [quotientRelation_apply_eq_sum,Fintype.sum_option] at ht0
    change t none • responseClass F₀+∑ j,t (some j) • responseClass (F j)=0 at ht0
    have hsub : (∑ j,(t (some j)-t none) • responseClass (F j))=0 := by
      calc
        _ = (t none • responseClass F₀+∑ j,t (some j) • responseClass (F j))-
            t none • (responseClass F₀+∑ j,responseClass (F j)) := by
          simp only [sub_smul,sum_sub_distrib,smul_add,smul_sum]
          abel
        _ = 0 := by rw [ht0,hsum,smul_zero,sub_self]
    have hcoeff := (Fintype.linearIndependent_iff.mp hind) _ hsub
    refine ⟨t none,?_⟩
    funext i
    cases i with
    | none => simp
    | some j =>
      have hj : t (some j)=t none := sub_eq_zero.mp (hcoeff j)
      simpa only [Pi.smul_apply,smul_eq_mul,mul_one] using hj

/-- Relabeling a positive unit circuit with one all-hub anchor produces an
actual full lattice summand in exactly `k` times the graphical zonotope.
The other modules may have any nonempty proper essential hub sets. -/
theorem lattice_book_of_anchored_circuit {s k : ℕ} (hs : 0< s)
    (F₀ : SetFunction (Fin s)) (F : J → SetFunction (Fin s))
    (hF₀ : IsMonotoneBoolean F₀) (hF : ∀ j,IsMonotoneBoolean (F j))
    (hess₀ : ∀ a,Essential F₀ a) (hess : ∀ j,∃ a,Essential (F j) a)
    (hind : LinearIndependent ℝ (fun j => responseClass (F j)))
    (hsum : responseClass F₀+∑ j,responseClass (F j)=0)
    (hcard : Fintype.card J+1=k) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(k : ℝ) • graphicalZonotope (cliqueBook s k) := by
  classical
  letI : Nonempty (Fin s) := ⟨⟨0,hs⟩⟩
  have hk : 0< k := by omega
  have hJ : Fintype.card (Option J)=k := by simpa only [Fintype.card_option] using hcard
  let e : Fin k ≃ Option J := (finCongr hJ.symm).trans (Fintype.equivFin (Option J)).symm
  let G := anchoredFamily F₀ F
  let F' : Fin k → SetFunction (Fin s) := fun i => G (e i)
  have hG : ∀ j,IsMonotoneBoolean (G j) := by
    intro j
    cases j with
    | none => exact hF₀
    | some j => exact hF j
  have hF' : ∀ i,IsMonotoneBoolean (F' i) := fun i => hG (e i)
  have hconn : (essentialSpokeGraph F').Connected := by
    apply essentialSpokeGraph_connected_of_anchor F' (e.symm none)
    · intro a
      simpa only [F',e.apply_symm_apply,G,anchoredFamily] using hess₀ a
    · intro i
      cases he : e i with
      | none => exact ⟨⟨0,hs⟩,by simpa only [F',he,G,anchoredFamily] using hess₀ ⟨0,hs⟩⟩
      | some j => simpa only [F',he,G,anchoredFamily] using hess j
  obtain ⟨hrel,huniq⟩ := anchored_unit_relation F₀ F hind hsum
  obtain ⟨z,hzn,hzc⟩ := (mem_quotientRelation_ker_iff G _).mp hrel
  have hc : Compatible z F' (fun _ => 1) :=
    (compatible_reindex e z G (fun _ => 1)).mpr hzc
  have huniq' : UniqueIntegrableRelation F' (fun _ => 1) := by
    intro t ht
    obtain ⟨u,hun,huc⟩ := ht
    have hold : Compatible u G (fun j => t (e.symm j)) :=
      (compatible_reindex e u G t).mp huc
    obtain ⟨c,hc⟩ := huniq (fun j => t (e.symm j)) ⟨u,hun,hold⟩
    refine ⟨c,?_⟩
    funext i
    simpa only [e.symm_apply_apply,Pi.smul_apply,smul_eq_mul,mul_one] using congrFun hc (e i)
  have hkrel : (fun _ : Fin k => (1 : ℝ))∈LinearMap.ker (quotientRelation F') :=
    (mem_quotientRelation_ker_iff F' _).mpr ⟨z,hzn,hc⟩
  obtain ⟨f,hfn,hfi,hfe,hfg,hfd,hfm,hfl,R,hRl,hRn,hR⟩ :=
    lattice_book_of_weighted_modules hk F' hF' (fun _ => (1 : ℤ)) (fun _ => by norm_num)
      hconn (by simpa only [Int.cast_one] using hkrel)
      (by simpa only [Int.cast_one] using huniq') (k : ℤ) (by simp)
  exact ⟨f,hfn,hfi,hfe,hfg,hfd,hfm,hfl,R,hRl,hRn,by simpa only [Int.cast_natCast] using hR⟩

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart171

section BundlePart172
/- Source: Papers/GraphicalZonotopes/WeightedBooleanCircuits.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise

/-- Transport of a finite positive integral response circuit to the literal
book vertex type, retaining its integral dilation bound. -/
theorem lattice_book_of_finite_weighted_circuit
    {J : Type*} [Fintype J] [DecidableEq J] {s k : ℕ} (hs : 0< s)
    (F : J → SetFunction (Fin s)) (hF : ∀ j,IsMonotoneBoolean (F j))
    (j₀ : J) (hanchor : ∀ a,Essential (F j₀) a)
    (hbranch : ∀ j,∃ a,Essential (F j) a)
    (w : J → ℤ) (hw : ∀ j,0< w j)
    (hrel : (fun j => (w j : ℝ))∈LinearMap.ker (quotientRelation F))
    (huniq : UniqueIntegrableRelation F (fun j => (w j : ℝ)))
    (hcard : Fintype.card J=k) (M : ℤ) (hM : ∑ j,w j≤ M) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(M : ℝ) • graphicalZonotope (cliqueBook s k) := by
  classical
  letI : Nonempty (Fin s) := ⟨⟨0,hs⟩⟩
  letI : Nonempty J := ⟨j₀⟩
  have hk : 0< k := by rw [← hcard]; exact Fintype.card_pos
  let e : Fin k ≃ J := (finCongr hcard.symm).trans (Fintype.equivFin J).symm
  let F' : Fin k → SetFunction (Fin s) := fun i => F (e i)
  let w' : Fin k → ℤ := fun i => w (e i)
  have hc : (essentialSpokeGraph F').Connected := by
    apply essentialSpokeGraph_connected_of_anchor F' (e.symm j₀)
    · intro a
      simpa only [F',e.apply_symm_apply] using hanchor a
    · intro i
      exact hbranch (e i)
  obtain ⟨z,hzn,hzc⟩ := (mem_quotientRelation_ker_iff F _).mp hrel
  have hrel' : (fun i => (w' i : ℝ))∈LinearMap.ker (quotientRelation F') := by
    apply (mem_quotientRelation_ker_iff F' _).mpr
    have hh : Compatible z F (fun j => (w' (e.symm j) : ℝ)) := by
      simpa only [w',e.apply_symm_apply] using hzc
    exact ⟨z,hzn,(compatible_reindex e z F (fun i => (w' i : ℝ))).mpr hh⟩
  have huniq' : UniqueIntegrableRelation F' (fun i => (w' i : ℝ)) := by
    intro t ht
    obtain ⟨u,hun,huc⟩ := ht
    have hold : Compatible u F (fun j => t (e.symm j)) :=
      (compatible_reindex e u F t).mp huc
    obtain ⟨c,hc'⟩ := huniq (fun j => t (e.symm j)) ⟨u,hun,hold⟩
    refine ⟨c,?_⟩
    funext i
    simpa only [e.symm_apply_apply,Pi.smul_apply,w'] using congrFun hc' (e i)
  apply lattice_book_of_weighted_modules hk F' (fun i => hF (e i)) w'
    (fun i => hw (e i)) hc hrel' huniq' M
  change (∑ i : Fin k,w (e i))≤ M
  rw [e.sum_comp]
  exact hM

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart172

section BundlePart173
/- Source: Papers/GraphicalZonotopes/BookCircuitAssembly.lean -/






@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise

variable {s : ℕ} (hs : 3≤ s)

def bookZero : Fin s := ⟨0,by omega⟩
abbrev BookAnchor := ↥((univ : Finset (Fin s)).erase (bookZero hs))

def anchorExtension (t : BookAnchor hs → ℝ) : Fin s → ℝ :=
  erasedHubWeight univ (bookZero hs) t

@[simp] theorem anchorExtension_zero (t : BookAnchor hs → ℝ) :
    anchorExtension hs t (bookZero hs)=0 := erasedHubWeight_self _ _ _

@[simp] theorem anchorExtension_subtype (t : BookAnchor hs → ℝ) (a : BookAnchor hs) :
    anchorExtension hs t a.1=t a := erasedHubWeight_subtype _ _ _ _

theorem anchorExtension_labels :
    anchorExtension hs (fun a => (a.1.val : ℝ))=(fun a : Fin s => (a.val : ℝ)) := by
  funext a
  by_cases h : a=bookZero hs
  · subst a
    rw [anchorExtension_zero]
    norm_num [bookZero]
  · have ha : a∈(univ : Finset (Fin s)).erase (bookZero hs) := mem_erase.mpr ⟨h,mem_univ _⟩
    exact anchorExtension_subtype hs _ ⟨a,ha⟩

theorem sum_anchor_extension {W : Type*} [AddCommMonoid W] [Module ℝ W]
    (t : BookAnchor hs → ℝ) (v : Fin s → W) :
    (∑ a : BookAnchor hs,t a • v a.1)=∑ a,anchorExtension hs t a • v a := by
  have he : (∑ a : BookAnchor hs,t a • v a.1)=
      ∑ a∈(univ : Finset (Fin s)).erase (bookZero hs),anchorExtension hs t a • v a := by
    rw [← sum_coe_sort ((univ : Finset (Fin s)).erase (bookZero hs))
      (fun a : Fin s => anchorExtension hs t a • v a)]
    exact sum_congr rfl (fun a _ => by rw [anchorExtension_subtype])
  rw [he]
  have hz : anchorExtension hs t (bookZero hs) • v (bookZero hs)=0 := by simp
  have hsum := sum_erase_add (s:=(univ : Finset (Fin s)))
    (f:=fun a => anchorExtension hs t a • v a) (mem_univ (bookZero hs))
  simpa only [hz,add_zero] using hsum

theorem weighted_anchor_response (t : BookAnchor hs → ℝ) :
    (∑ a : BookAnchor hs,t a • responseClass (thresholdStar a.1))=
      ∑ C : BookBlock (Fin s),(-1 : ℝ)^(C.1.card-3) •
        blockClass C.1 (endpointCoefficients C.1 (anchorExtension hs t)) := by
  rw [sum_anchor_extension hs t (fun a => responseClass (thresholdStar a)),weighted_threshold_response]

section Family
variable {B : Type*} [Fintype B] [DecidableEq B]
    (e : B ≃ BookBlock (Fin s)) (r : B → ℕ)
    (P : ∀ b,WeightedPureBlock (e b).1 ((s-1 : ℕ) : ℤ)
      (ordinaryBookTarget (e b).1) (r b))

abbrev BookCircuitIndex := BookAnchor hs ⊕ (Σ b,Fin (r b))

def bookCircuitVector : BookCircuitIndex hs r → ResponseQuotient (Fin s)
  | .inl a => responseClass (thresholdStar a.1)
  | .inr j => blockClass (e j.1).1 ((P j.1).column j.2)

def bookCircuitWeight : BookCircuitIndex hs r → ℤ
  | .inl a => (a.1.val : ℤ)
  | .inr j => (P j.1).weight j.2

def bookBlockCombination (t : BookCircuitIndex hs r → ℝ) (b : B) : PairIn (e b).1 → ℝ :=
  (-1 : ℝ)^((e b).1.card-3) • endpointCoefficients (e b).1
    (anchorExtension hs (fun a => t (.inl a)))+
    ∑ j : Fin (r b),t (.inr ⟨b,j⟩) • (P b).column j

theorem bookCircuit_sum_blocks (t : BookCircuitIndex hs r → ℝ) :
    (∑ j,t j • bookCircuitVector hs e r P j)=
      ∑ b,blockClass (e b).1 (bookBlockCombination hs e r P t b) := by
  rw [Fintype.sum_sum_type,Fintype.sum_sigma]
  change (∑ a : BookAnchor hs,t (.inl a) • responseClass (thresholdStar a.1))+
    (∑ b,∑ j : Fin (r b),t (.inr ⟨b,j⟩) • blockClass (e b).1 ((P b).column j))=_
  rw [weighted_anchor_response]
  have heq : (∑ C : BookBlock (Fin s),(-1 : ℝ)^(C.1.card-3) •
      blockClass C.1 (endpointCoefficients C.1 (anchorExtension hs (fun a => t (.inl a)))))=
      ∑ b,(-1 : ℝ)^((e b).1.card-3) • blockClass (e b).1
        (endpointCoefficients (e b).1 (anchorExtension hs (fun a => t (.inl a)))) := by
    exact (e.sum_comp _).symm
  rw [heq,← sum_add_distrib]
  apply sum_congr rfl
  intro b hb
  simp only [bookBlockCombination,map_add,map_smul,map_sum]

theorem bookCircuit_weighted_sum :
    (∑ j,(bookCircuitWeight hs e r P j : ℝ) • bookCircuitVector hs e r P j)=0 := by
  rw [bookCircuit_sum_blocks]
  apply sum_eq_zero
  intro b hb
  have hd : anchorExtension hs (fun a => (bookCircuitWeight hs e r P (.inl a) : ℝ))=
      (fun a : Fin s => (a.val : ℝ)) := by
    simpa only [bookCircuitWeight,Int.cast_natCast] using anchorExtension_labels hs
  simp only [bookBlockCombination,map_add,map_smul,map_sum,bookCircuitWeight,Int.cast_natCast]
  rw [anchorExtension_labels,(P b).weighted_sum]
  change (-1 : ℝ)^((e b).1.card-3) • blockClass (e b).1 (endpointLabels (e b).1)+
    -((-1 : ℝ)^((e b).1.card-3) • blockClass (e b).1 (endpointLabels (e b).1))=0
  exact add_neg_cancel _

theorem bookCircuit_pure_independent :
    LinearIndependent ℝ (fun j : Σ b,Fin (r b) =>
      blockClass (e j.1).1 ((P j.1).column j.2)) := by
  classical
  have hpair : ∀ b,∃ p : PairIn (e b).1,True := by
    intro b
    obtain ⟨p,hp⟩ := cliquePairs_nonempty (e b).1 (e b).1 (Subset.refl _)
      (by have h := (mem_largeBlocks.mp (e b).2).2; omega)
    exact ⟨p,trivial⟩
  apply block_families_independent (fun b => (e b).1)
    (Subtype.val_injective.comp e.injective) (fun b => (hpair b).choose)
    (fun b => (P b).column) (fun b => (P b).independent)

/-- The only nonlocal condition needed from the connectors: their block
constant equations force the prescribed arithmetic progression of hub scales. -/
def BookScaleRigidity : Prop :=
  ∀ (d : Fin s → ℝ) (t : (b : B) → Fin (r b) → ℝ),d (bookZero hs)=0 →
    (∀ b,blockClass (e b).1
      ((-1 : ℝ)^((e b).1.card-3) • endpointCoefficients (e b).1 d+
        ∑ j : Fin (r b),t b j • (P b).column j)=0) →
    ∃ c : ℝ,∀ a,d a=c*(a.val : ℝ)

theorem bookCircuit_unique_relation
    (hscale : BookScaleRigidity hs e r P)
    (t : BookCircuitIndex hs r → ℝ)
    (ht : (∑ j,t j • bookCircuitVector hs e r P j)=0) :
    ∃ c : ℝ,t=c • (fun j => (bookCircuitWeight hs e r P j : ℝ)) := by
  classical
  have hpair : ∀ b,∃ p : PairIn (e b).1,True := by
    intro b
    obtain ⟨p,hp⟩ := cliquePairs_nonempty (e b).1 (e b).1 (Subset.refl _)
      (by have h := (mem_largeBlocks.mp (e b).2).2; omega)
    exact ⟨p,trivial⟩
  rw [bookCircuit_sum_blocks] at ht
  have hblock := block_sum_zero_component (fun b => (e b).1)
    (Subtype.val_injective.comp e.injective) (fun b => (hpair b).choose)
    (bookBlockCombination hs e r P t) ht
  obtain ⟨c,hc⟩ := hscale (anchorExtension hs (fun a => t (.inl a)))
    (fun b j => t (.inr ⟨b,j⟩)) (anchorExtension_zero hs _) hblock
  have hanchor : ∀ a : BookAnchor hs,t (.inl a)=c*(a.1.val : ℝ) := by
    intro a
    simpa only [anchorExtension_subtype] using hc a.1
  have hzero : (∑ j : BookCircuitIndex hs r,
      (t j-c*(bookCircuitWeight hs e r P j : ℝ)) • bookCircuitVector hs e r P j)=0 := by
    simp only [sub_smul,mul_smul,sum_sub_distrib,← smul_sum]
    rw [bookCircuit_sum_blocks,ht,bookCircuit_weighted_sum,smul_zero,sub_self]
  rw [Fintype.sum_sum_type] at hzero
  have haz : (∑ a : BookAnchor hs,
      (t (.inl a)-c*(bookCircuitWeight hs e r P (.inl a) : ℝ)) •
        bookCircuitVector hs e r P (.inl a))=0 := by
    apply sum_eq_zero
    intro a ha
    simp only [bookCircuitWeight,Int.cast_natCast,hanchor,sub_self,zero_smul]
  rw [haz,zero_add] at hzero
  have hpure := Fintype.linearIndependent_iff.mp (bookCircuit_pure_independent e r P)
    (fun j => t (.inr j)-c*(bookCircuitWeight hs e r P (.inr j) : ℝ)) hzero
  refine ⟨c,?_⟩
  funext j
  cases j with
  | inl a => simpa only [Pi.smul_apply,smul_eq_mul,bookCircuitWeight,Int.cast_natCast] using hanchor a
  | inr j => simpa only [Pi.smul_apply,smul_eq_mul] using sub_eq_zero.mp (hpure j)

/-- A complete family of pure blocks and actual connector rigidity yields
an indecomposable full lattice book summand at the paper's stated scale. -/
theorem lattice_book_of_block_circuit (hscale : BookScaleRigidity hs e r P)
    {k : ℕ} (hcard : Fintype.card (BookCircuitIndex hs r)=k) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(((s-1)*k : ℕ) : ℝ) • graphicalZonotope (cliqueBook s k) := by
  classical
  have hF : ∀ b j,∃ F : SetFunction (Fin s),IsMonotoneBoolean F ∧
      (∀ a,a∈(e b).1 → Essential F a) ∧
      (∀ a,a∉(e b).1 → ∀ X,F (insert a X)=F X) ∧
      responseClass F=blockClass (e b).1 ((P b).column j) := fun b j => (P b).realizable j
  choose F hFb hFe hFi hFc using hF
  let G : BookCircuitIndex hs r → SetFunction (Fin s)
    | .inl a => thresholdStar a.1
    | .inr j => F j.1 j.2
  have hG : ∀ j,IsMonotoneBoolean (G j) := by
    intro j
    cases j with
    | inl a => exact thresholdStar_boolean a.1
    | inr j => exact hFb j.1 j.2
  have hGc : ∀ j,responseClass (G j)=bookCircuitVector hs e r P j := by
    intro j
    cases j with
    | inl a => rfl
    | inr j => exact hFc j.1 j.2
  let a₁ : BookAnchor hs := ⟨⟨1,by omega⟩,mem_erase.mpr ⟨by
    intro h
    have h' := congrArg Fin.val h
    simp [bookZero] at h',mem_univ _⟩⟩
  have ha₁ : ∀ a,Essential (G (.inl a₁)) a :=
    thresholdStar_essential (by simpa using hs) a₁.1
  have hbranch : ∀ j,∃ a,Essential (G j) a := by
    intro j
    cases j with
    | inl a => exact ⟨a.1,thresholdStar_essential (by simpa using hs) a.1 a.1⟩
    | inr j =>
      have hne : (e j.1).1.Nonempty := card_pos.mp (by
        have h := (mem_largeBlocks.mp (e j.1).2).2
        omega)
      obtain ⟨a,ha⟩ := hne
      exact ⟨a,hFe j.1 j.2 a ha⟩
  have hw : ∀ j,0< bookCircuitWeight hs e r P j := by
    intro j
    cases j with
    | inl a =>
      change 0<(a.1.val : ℤ)
      have hne : a.1≠ bookZero hs := (mem_erase.mp a.2).1
      have hv : a.1.val≠0 := fun h => hne (Fin.ext h)
      omega
    | inr j => exact (P j.1).positive j.2
  have hb : ∀ j,bookCircuitWeight hs e r P j≤((s-1 : ℕ) : ℤ) := by
    intro j
    cases j with
    | inl a =>
      change (a.1.val : ℤ)≤((s-1 : ℕ) : ℤ)
      have h := a.1.isLt
      omega
    | inr j => exact (P j.1).bounded j.2
  have hrel : (fun j => (bookCircuitWeight hs e r P j : ℝ))∈LinearMap.ker (quotientRelation G) := by
    change quotientRelation G _=0
    rw [quotientRelation_apply_eq_sum]
    simp_rw [hGc]
    exact bookCircuit_weighted_sum hs e r P
  have huniq : UniqueIntegrableRelation G (fun j => (bookCircuitWeight hs e r P j : ℝ)) := by
    intro t ht
    have ht0 : quotientRelation G t=0 := (mem_quotientRelation_ker_iff G t).mpr ht
    rw [quotientRelation_apply_eq_sum] at ht0
    simp_rw [hGc] at ht0
    exact bookCircuit_unique_relation hs e r P hscale t ht0
  have hM : (∑ j,bookCircuitWeight hs e r P j)≤(((s-1)*k : ℕ) : ℤ) := by
    calc
      _ ≤ ∑ _ : BookCircuitIndex hs r,((s-1 : ℕ) : ℤ) := sum_le_sum (fun j _ => hb j)
      _ = _ := by simp [hcard,Nat.cast_mul,mul_comm]
  obtain ⟨f,hfn,hfi,hfe,hfg,hfd,hfm,hfl,R,hRl,hRn,hR⟩ :=
    lattice_book_of_finite_weighted_circuit (by omega) G hG (.inl a₁) ha₁ hbranch
      (bookCircuitWeight hs e r P) hw hrel huniq hcard (((s-1)*k : ℕ) : ℤ) hM
  exact ⟨f,hfn,hfi,hfe,hfg,hfd,hfm,hfl,R,hRl,hRn,by simpa only [Int.cast_natCast] using hR⟩

end Family
end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart173

section BundlePart174
/- Source: Papers/GraphicalZonotopes/BookQuadrilateralPattern.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators

/-- The `s-2` quadrilaterals in the paper's upper-interval construction. -/
def connectorLabels {s : ℕ} (i : Fin (s-2)) : Fin 4 → ℕ :=
  if i.val=0 then ![0,1,2,3]
  else if i.val=1 then ![0,1,3,4]
  else if i.val=2 then ![1,2,3,4]
  else ![0,1,i.val+1,i.val+2]

theorem connectorLabels_lt {s : ℕ} (hs : 5≤ s) (i : Fin (s-2)) (j : Fin 4) :
    connectorLabels i j< s := by
  have hi := i.isLt
  by_cases h0 : i.val=0 <;> by_cases h1 : i.val=1 <;> by_cases h2 : i.val=2 <;>
    fin_cases j <;> simp [connectorLabels,h0,h1,h2] <;> omega

theorem connectorLabels_strictMono {s : ℕ} (i : Fin (s-2)) :
    StrictMono (connectorLabels i) := by
  intro u v huv
  by_cases h0 : i.val=0 <;> by_cases h1 : i.val=1 <;> by_cases h2 : i.val=2 <;>
    fin_cases u <;> fin_cases v <;> norm_num at huv
  all_goals simp [connectorLabels,h0,h1,h2] <;> omega

theorem connectorLabels_balanced {s : ℕ} (i : Fin (s-2)) :
    connectorLabels i 0+connectorLabels i 3=connectorLabels i 1+connectorLabels i 2 := by
  by_cases h0 : i.val=0 <;> by_cases h1 : i.val=1 <;> by_cases h2 : i.val=2 <;>
    simp [connectorLabels,h0,h1,h2] <;> omega

def bookConnector {s : ℕ} (hs : 5≤ s) (i : Fin (s-2)) : BalancedQuad s where
  point j := ⟨connectorLabels i j,connectorLabels_lt hs i j⟩
  ordered := connectorLabels_strictMono i
  balanced := connectorLabels_balanced i

theorem BalancedQuad.point_le_last {s : ℕ} (Q : BalancedQuad s) {a : Fin s}
    (ha : a∈Q.clique) : a≤ Q.point 3 := by
  obtain ⟨j,hj,rfl⟩ := mem_image.mp ha
  exact Q.ordered.monotone (by omega)

theorem connector_zero_mem {s : ℕ} (hs : 5≤ s) (i : Fin (s-2)) :
    (⟨0,by omega⟩ : Fin s)∈(bookConnector hs i).clique ↔ i.val≠2 := by
  have hmem : (⟨0,by omega⟩ : Fin s)∈(bookConnector hs i).clique ↔
      ∃ j : Fin 4,connectorLabels i j=0 := by
    simp only [BalancedQuad.clique,mem_image,mem_univ,true_and]
    constructor
    · rintro ⟨j,hj⟩
      exact ⟨j,congrArg Fin.val hj⟩
    · rintro ⟨j,hj⟩
      exact ⟨j,Fin.ext hj⟩
  rw [hmem]
  by_cases h0 : i.val=0
  · constructor
    · intro h
      omega
    · intro h
      exact ⟨0,by simp [connectorLabels,h0]⟩
  by_cases h1 : i.val=1
  · constructor
    · intro h
      omega
    · intro h
      exact ⟨0,by simp [connectorLabels,h0,h1]⟩
  by_cases h2 : i.val=2
  · simp only [h2,ne_eq,not_true_eq_false,iff_false]
    rintro ⟨j,hj⟩
    fin_cases j <;> norm_num [connectorLabels,h0,h1,h2] at hj
  · refine ⟨fun _ => h2,fun _ => ⟨0,?_⟩⟩
    simp [connectorLabels,h0,h1,h2]

theorem bookConnector_clique_injective {s : ℕ} (hs : 5≤ s) :
    Function.Injective (fun i : Fin (s-2) => (bookConnector hs i).clique) := by
  intro i j h
  change (bookConnector hs i).clique=(bookConnector hs j).clique at h
  have hle : (bookConnector hs i).point 3≤(bookConnector hs j).point 3 := by
    apply BalancedQuad.point_le_last
    rw [← h]
    exact BalancedQuad.point_mem _ _
  have hge : (bookConnector hs j).point 3≤(bookConnector hs i).point 3 := by
    apply BalancedQuad.point_le_last
    rw [h]
    exact BalancedQuad.point_mem _ _
  have hmax : connectorLabels i 3=connectorLabels j 3 := congrArg Fin.val (le_antisymm hle hge)
  have hz : i.val≠2 ↔ j.val≠2 := by
    rw [← connector_zero_mem hs i,← connector_zero_mem hs j,h]
  apply Fin.ext
  by_cases hi0 : i.val=0 <;> by_cases hi1 : i.val=1 <;> by_cases hi2 : i.val=2 <;>
    by_cases hj0 : j.val=0 <;> by_cases hj1 : j.val=1 <;> by_cases hj2 : j.val=2 <;>
    simp [connectorLabels,hi0,hi1,hi2,hj0,hj1,hj2] at hmax <;> omega

/-- The three initial equal-endpoint-sum relations and the subsequent chain
force the complete prescribed hub scale vector for every `s≥5`. -/
theorem quadrilateral_endpoint_rigidity (s : ℕ) (hs : 5≤ s) (d : ℕ → ℝ)
    (h0 : d 0=0) (h03 : d 0+d 3=d 1+d 2)
    (h04 : d 0+d 4=d 1+d 3) (h14 : d 1+d 4=d 2+d 3)
    (hstep : ∀ j,5≤ j → j< s → d 0+d j=d 1+d (j-1)) :
    ∀ j,j< s → d j=(j : ℝ)*d 1 := by
  have h2 : d 2=2*d 1 := by linarith
  have h3 : d 3=3*d 1 := by linarith
  have h4 : d 4=4*d 1 := by linarith
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    by_cases hsmall : j≤4
    · interval_cases j <;> norm_num [h0,h2,h3,h4]
    · have h5 : 5≤ j := by omega
      have hr := hstep j h5 hj
      have hp := ih (j-1) (by omega) (by omega)
      have hc : ((j-1 : ℕ) : ℝ)=(j : ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
      rw [hc] at hp
      linarith

theorem bookConnector_scale_rigidity {s : ℕ} (hs : 5≤ s)
    (d : Fin s → ℝ) (h0 : d ⟨0,by omega⟩=0)
    (hconn : ∀ i : Fin (s-2),
      d ((bookConnector hs i).point 0)+d ((bookConnector hs i).point 3)=
      d ((bookConnector hs i).point 1)+d ((bookConnector hs i).point 2)) :
    ∀ j : Fin s,d j=(j.val : ℝ)*d ⟨1,by omega⟩ := by
  let D : ℕ → ℝ := fun j => if h : j< s then d ⟨j,h⟩ else 0
  have hD : ∀ j : Fin s,D j.val=d j := by
    intro j
    simp only [D,dite_eq_left j.isLt]
  have hb0 := hconn ⟨0,by omega⟩
  have hb1 := hconn ⟨1,by omega⟩
  have hb2 := hconn ⟨2,by omega⟩
  have h03 : D 0+D 3=D 1+D 2 := by simpa [D,bookConnector,connectorLabels,(show 0< s by omega),
    (show 1< s by omega),(show 2< s by omega),(show 3< s by omega)] using hb0
  have h04 : D 0+D 4=D 1+D 3 := by simpa [D,bookConnector,connectorLabels,(show 0< s by omega),
    (show 1< s by omega),(show 3< s by omega),(show 4< s by omega)] using hb1
  have h14 : D 1+D 4=D 2+D 3 := by simpa [D,bookConnector,connectorLabels,(show 1< s by omega),
    (show 2< s by omega),(show 3< s by omega),(show 4< s by omega)] using hb2
  have hstep : ∀ j,5≤ j → j< s → D 0+D j=D 1+D (j-1) := by
    intro j hj hjs
    let i : Fin (s-2) := ⟨j-2,by omega⟩
    have hh := hconn i
    have hia : i.val+1=j-1 := by dsimp [i]; omega
    have hib : i.val+2=j := by dsimp [i]; omega
    have hi0 : i.val≠0 := by dsimp [i]; omega
    have hi1 : i.val≠1 := by dsimp [i]; omega
    have hi2 : i.val≠2 := by dsimp [i]; omega
    simpa [D,bookConnector,connectorLabels,hi0,hi1,hi2,hia,hib,(show 0< s by omega),
      (show 1< s by omega),hjs,(show j-1< s by omega)] using hh
  have h := quadrilateral_endpoint_rigidity s hs D
    (by simpa [D,(show 0< s by omega)] using h0) h03 h04 h14 hstep
  intro j
  have hj := h j.val j.isLt
  rw [hD j] at hj
  simpa [D,(show 1< s by omega)] using hj

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart174

section BundlePart175
/- Source: Papers/GraphicalZonotopes/BookBlockCounts.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators

/-- Every integral vector interval realizes every intermediate total. -/
theorem interval_sum_composition {B : Type*} [Fintype B] [DecidableEq B]
    (l u : B → ℕ) (hlu : ∀ b,l b≤ u b) {n : ℕ}
    (hnlo : (∑ b,l b)≤ n) (hnhi : n≤∑ b,u b) :
    ∃ k : B → ℕ,(∀ b,l b≤ k b ∧ k b≤ u b) ∧ (∑ b,k b)=n := by
  have hsum : (∑ b,(u b-l b))+(∑ b,l b)=∑ b,u b := by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun b _ => Nat.sub_add_cancel (hlu b))
  obtain ⟨f,hf,hfs⟩ := bounded_sum_composition (univ : Finset B) (fun b => u b-l b)
    (n:=n-∑ b,l b) (by omega)
  refine ⟨fun b => f b+l b,?_,?_⟩
  · intro b
    have hfb := hf b (mem_univ b)
    have hb := hlu b
    constructor <;> dsimp only <;> omega
  · rw [sum_add_distrib,hfs]
    omega

variable {H : Type*} [Fintype H] [LinearOrder H]

theorem largeBlocks_dimension_sum (S : Finset H) :
    (∑ C∈largeBlocks S,(C.card.choose 2-1))=blockDimensionSum S := by
  unfold blockDimensionSum
  apply sum_subset (filter_subset _ _)
  intro C hC hn
  have hc : C.card<3 := by
    have h : ¬3≤ C.card := fun h => hn (mem_largeBlocks.mpr ⟨mem_powerset.mp hC,h⟩)
    omega
  interval_cases hcard : C.card <;> norm_num [hcard,Nat.choose]

theorem BookBlock_dimension_sum :
    (∑ C : BookBlock H,(C.1.card.choose 2-1))+1=cliqueCapacity (Fintype.card H) := by
  rw [sum_coe_sort (largeBlocks (univ : Finset H)) (fun C : Finset H => C.card.choose 2-1)]
  rw [largeBlocks_dimension_sum,← cliqueCapacity_eq_dimension_sum,card_univ]

theorem largeBlocks_lower_count (S : Finset H) :
    (∑ C∈largeBlocks S,(C.card-1))+S.card.choose 2+2^S.card=
      S.card*2^(S.card-1)+1 := by
  let E := S.powerset.filter (fun C => C.Nonempty)
  have hEcard : E.card+1=2^S.card := by
    have hpartition := card_filter_add_card_filter_not (s:=S.powerset) (p:=fun C => C.Nonempty)
    have hempty : S.powerset.filter (fun C => ¬C.Nonempty)={∅} := by
      ext C
      simp only [mem_filter,mem_powerset,not_nonempty_iff_eq_empty,mem_singleton]
      constructor
      · exact fun h => h.2
      · rintro rfl
        exact ⟨empty_subset _,rfl⟩
    rw [hempty,card_singleton,card_powerset] at hpartition
    exact hpartition
  have hsumE : (∑ C∈E,(C.card-1))+E.card=∑ C∈S.powerset,C.card := by
    calc
      _ = ∑ C∈E,((C.card-1)+1) := by simp [sum_add_distrib]
      _ = ∑ C∈E,C.card := sum_congr rfl (fun C hC =>
        Nat.sub_add_cancel (show 1≤ C.card from (card_pos.mpr (mem_filter.mp hC).2)))
      _ = _ := by
        apply sum_subset (filter_subset _ _)
        intro C hC hn
        have hz : ¬C.Nonempty := fun h => hn (mem_filter.mpr ⟨hC,h⟩)
        exact card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hz)
  have hsplit : (∑ C∈E,(C.card-1))=
      (∑ C∈largeBlocks S,(C.card-1))+S.card.choose 2 := by
    have hfilter : E.filter (fun C => 3≤ C.card)=largeBlocks S := by
      ext C
      simp only [E,mem_filter,mem_powerset,mem_largeBlocks]
      constructor
      · exact fun h => ⟨h.1.1,h.2⟩
      · exact fun h => ⟨⟨h.1,card_pos.mp (by omega)⟩,h.2⟩
    have hsmall : (∑ C∈E.filter (fun C => ¬3≤ C.card),(C.card-1))=
        (S.powersetCard 2).card := by
      have hp : S.powersetCard 2⊆E.filter (fun C => ¬3≤ C.card) := by
        intro C hC
        obtain ⟨hCS,hcard⟩ := mem_powersetCard.mp hC
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_powerset.mpr hCS,
          card_pos.mp (by omega)⟩,by omega⟩
      calc
        _ = ∑ C∈S.powersetCard 2,(C.card-1) := by
          symm
          apply sum_subset hp
          intro C hC hn
          have hsize := (mem_filter.mp hC).2
          have hCS := mem_powerset.mp (mem_filter.mp (mem_filter.mp hC).1).1
          have hne2 : C.card≠2 := fun h => hn (mem_powersetCard.mpr ⟨hCS,h⟩)
          omega
        _ = _ := by
          have he : ∀ C∈S.powersetCard 2,C.card-1=1 := fun C hC => by
            rw [(mem_powersetCard.mp hC).2]
          simp only [sum_congr rfl he,sum_const,nsmul_eq_mul,mul_one,Nat.cast_id]
    have hpartition := sum_filter_add_sum_filter_not (s:=E) (p:=fun C => 3≤ C.card)
      (f:=fun C => C.card-1)
    rw [hfilter,hsmall,card_powersetCard] at hpartition
    exact hpartition.symm
  rw [hsplit,sum_powerset_card] at hsumE
  omega

theorem BookBlock_lower_sum {s : ℕ} (hs : 2≤ s) :
    (∑ C : BookBlock (Fin s),(C.1.card-1))+s.choose 2=
      (s-2)*2^(s-1)+1 := by
  have h := largeBlocks_lower_count (univ : Finset (Fin s))
  simp only [card_univ,Fintype.card_fin] at h
  rw [← sum_coe_sort (largeBlocks (univ : Finset (Fin s)))
    (fun C : Finset (Fin s) => C.card-1)] at h
  have hspos : 0< s := by omega
  have hp : 2^s=2*2^(s-1) := by
    have he : s-1+1=s := by omega
    calc
      2^s=2^(s-1+1) := congrArg (fun n => 2^n) he.symm
      _ = 2*2^(s-1) := by rw [pow_succ]; ring
  have hm : s*2^(s-1)=(s-2)*2^(s-1)+2*2^(s-1) := by
    calc
      s*2^(s-1)=((s-2)+2)*2^(s-1) := congrArg (fun n => n*2^(s-1)) (Nat.sub_add_cancel hs).symm
      _ = _ := by rw [Nat.add_mul]
  rw [hp,hm] at h
  exact Nat.add_right_cancel (h.trans (by ac_rfl))

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart175

section BundlePart176
/- Source: Papers/GraphicalZonotopes/BookUpperBlocks.lean -/






@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise
variable {s : ℕ} (hs : 5≤ s)

def connectorBlock (i : Fin (s-2)) : BookBlock (Fin s) :=
  ⟨(bookConnector hs i).clique,mem_largeBlocks.mpr
    ⟨subset_univ _,by rw [BalancedQuad.card_clique]; omega⟩⟩

theorem connectorBlock_injective : Function.Injective (connectorBlock hs) := by
  intro i j h
  exact bookConnector_clique_injective hs (congrArg Subtype.val h)

def connectorBlockSet : Finset (BookBlock (Fin s)) := univ.image (connectorBlock hs)

@[simp] theorem connectorBlock_mem (i : Fin (s-2)) :
    connectorBlock hs i∈connectorBlockSet hs := mem_image.mpr ⟨i,mem_univ _,rfl⟩

@[simp] theorem connectorBlockSet_card : (connectorBlockSet hs).card=s-2 := by
  rw [connectorBlockSet,card_image_of_injective _ (connectorBlock_injective hs),card_univ,Fintype.card_fin]

abbrev OrdinaryBookBlock := {C : BookBlock (Fin s) // C∉connectorBlockSet hs}
abbrev UpperBookBlock := Fin (s-2) ⊕ OrdinaryBookBlock hs

def upperBlockMap : UpperBookBlock hs → BookBlock (Fin s)
  | .inl i => connectorBlock hs i
  | .inr C => C.1

theorem upperBlockMap_bijective : Function.Bijective (upperBlockMap hs) := by
  constructor
  · intro b c h
    cases b with
    | inl i =>
      cases c with
      | inl j => exact congrArg Sum.inl (connectorBlock_injective hs h)
      | inr C =>
        change connectorBlock hs i=C.1 at h
        exact False.elim (C.2 (h ▸ connectorBlock_mem hs i))
    | inr C =>
      cases c with
      | inl i =>
        change C.1=connectorBlock hs i at h
        exact False.elim (C.2 (h.symm ▸ connectorBlock_mem hs i))
      | inr D => exact congrArg Sum.inr (Subtype.ext h)
  · intro C
    by_cases h : C∈connectorBlockSet hs
    · obtain ⟨i,hi,he⟩ := mem_image.mp h
      exact ⟨.inl i,he⟩
    · exact ⟨.inr ⟨C,h⟩,rfl⟩

def upperBlockEquiv : UpperBookBlock hs ≃ BookBlock (Fin s) :=
  Equiv.ofBijective (upperBlockMap hs) (upperBlockMap_bijective hs)

@[simp] theorem upperBlockEquiv_inl (i : Fin (s-2)) :
    upperBlockEquiv hs (.inl i)=connectorBlock hs i := rfl

@[simp] theorem upperBlockEquiv_inr (C : OrdinaryBookBlock hs) :
    upperBlockEquiv hs (.inr C)=C.1 := rfl

theorem sum_upperBlock_partition {W : Type*} [AddCommMonoid W]
    (v : BookBlock (Fin s) → W) :
    (∑ C : BookBlock (Fin s),v C)=
      (∑ i : Fin (s-2),v (connectorBlock hs i))+
        ∑ C : OrdinaryBookBlock hs,v C.1 := by
  have h := (upperBlockEquiv hs).sum_comp v
  rw [Fintype.sum_sum_type] at h
  exact h.symm

def upperPureRank (r : OrdinaryBookBlock hs → ℕ) : UpperBookBlock hs → ℕ
  | .inl _ => 4
  | .inr C => r C

def upperPureBlock (r : OrdinaryBookBlock hs → ℕ)
    (P : ∀ C,WeightedPureBlock C.1.1 ((s-1 : ℕ) : ℤ)
      (ordinaryBookTarget C.1.1) (r C)) :
    ∀ b : UpperBookBlock hs,WeightedPureBlock (upperBlockEquiv hs b).1
      ((s-1 : ℕ) : ℤ) (ordinaryBookTarget (upperBlockEquiv hs b).1) (upperPureRank hs r b)
  | .inl i => (bookConnector hs i).pureBlock
  | .inr C => P C

/-- The literal omitted coordinates of the selected quadrilaterals supply
all connector equations, hence force a one-dimensional hub scale space. -/
theorem upper_book_scale_rigidity (r : OrdinaryBookBlock hs → ℕ)
    (P : ∀ C,WeightedPureBlock C.1.1 ((s-1 : ℕ) : ℤ)
      (ordinaryBookTarget C.1.1) (r C)) :
    BookScaleRigidity (show 3≤ s by omega) (upperBlockEquiv hs)
      (upperPureRank hs r) (upperPureBlock hs r P) := by
  intro d t hd hblock
  have hconn : ∀ i : Fin (s-2),
      d ((bookConnector hs i).point 0)+d ((bookConnector hs i).point 3)=
        d ((bookConnector hs i).point 1)+d ((bookConnector hs i).point 2) := by
    intro i
    let Q := bookConnector hs i
    have hi := hblock (.inl i)
    change blockClass Q.clique
      ((-1 : ℝ)^(Q.clique.card-3) • endpointCoefficients Q.clique d+
        ∑ j : Fin 4,t (.inl i) j • Q.column j)=0 at hi
    obtain ⟨c,hc⟩ := (blockClass_eq_zero_iff Q.clique Q.reference _).mp hi
    have hr := hc Q.reference
    have ho := hc Q.opposite
    simp only [Pi.add_apply,Pi.smul_apply,Finset.sum_apply,smul_eq_mul,
      BalancedQuad.column_reference,BalancedQuad.column_opposite,mul_zero,
      sum_const_zero,add_zero] at hr ho
    have he := hr.trans ho.symm
    simp only [Q.card_clique] at he
    have he' : -(d (Q.point 0)+d (Q.point 3))= -(d (Q.point 1)+d (Q.point 2)) := by
      simpa [endpointCoefficients,BalancedQuad.reference,BalancedQuad.opposite,
        BalancedQuad.pair,orderedPair] using he
    exact neg_injective he'
  have h := bookConnector_scale_rigidity hs d hd hconn
  exact ⟨d ⟨1,by omega⟩,fun a => by simpa only [mul_comm] using h a⟩

/-- Exact ordinary-block lower count after removing the `s-2` connectors. -/
theorem ordinary_lower_count :
    3*(s-2)+(∑ C : OrdinaryBookBlock hs,(C.1.1.card-1))+s.choose 2=
      (s-2)*2^(s-1)+1 := by
  have h := BookBlock_lower_sum (show 2≤ s by omega)
  rw [sum_upperBlock_partition hs] at h
  have he : (∑ i : Fin (s-2),((connectorBlock hs i).1.card-1))=3*(s-2) := by
    simp only [connectorBlock,BalancedQuad.card_clique]
    norm_num [Nat.choose]
    ring
  rw [he] at h
  exact h

theorem ordinary_upper_count :
    5*(s-2)+(∑ C : OrdinaryBookBlock hs,(C.1.1.card.choose 2-1))+1=cliqueCapacity s := by
  have h := BookBlock_dimension_sum (H:=Fin s)
  simp only [Fintype.card_fin] at h
  rw [sum_upperBlock_partition hs] at h
  have he : (∑ i : Fin (s-2),((connectorBlock hs i).1.card.choose 2-1))=5*(s-2) := by
    simp only [connectorBlock,BalancedQuad.card_clique]
    norm_num [Nat.choose]
    ring
  rw [he] at h
  exact h

def bookUpperIntervalStart (s : ℕ) : ℕ :=
  (s-2)*2^(s-1)+2*s-2-s.choose 2

theorem bookUpperIntervalStart_eq :
    bookUpperIntervalStart s=(s-1)+4*(s-2)+∑ C : OrdinaryBookBlock hs,(C.1.1.card-1) := by
  have h := ordinary_lower_count hs
  unfold bookUpperIntervalStart
  omega

theorem cliqueCapacity_upper_ordinary :
    cliqueCapacity s=(s-1)+4*(s-2)+∑ C : OrdinaryBookBlock hs,(C.1.1.card.choose 2-1) := by
  have h := ordinary_upper_count hs
  omega

private theorem card_le_choose_two {n : ℕ} (hn : 3≤ n) : n≤ n.choose 2 := by
  rw [Nat.choose_two_right]
  apply (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_left n (show 2≤ n-1 by omega)

/-- The full uniform upper interval of Theorem 7.10, with the paper's exact
integral dilation and an explicit integral Minkowski complement. -/
theorem book_upper_interval (hs : 5≤ s) {k : ℕ} (hklo : bookUpperIntervalStart s≤ k)
    (hkhi : k≤ cliqueCapacity s) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(((s-1)*k : ℕ) : ℝ) • graphicalZonotope (cliqueBook s k) := by
  classical
  let N := (s-1)+4*(s-2)
  let l : OrdinaryBookBlock hs → ℕ := fun C => C.1.1.card-1
  let u : OrdinaryBookBlock hs → ℕ := fun C => C.1.1.card.choose 2-1
  have hlu : ∀ C,l C≤ u C := by
    intro C
    have hsize := (mem_largeBlocks.mp C.1.2).2
    have hchoose := card_le_choose_two hsize
    dsimp only [l,u]
    omega
  have hlo : N+(∑ C,l C)≤ k := by
    rw [bookUpperIntervalStart_eq hs] at hklo
    exact hklo
  have hhi : k≤ N+∑ C,u C := by
    rw [cliqueCapacity_upper_ordinary hs] at hkhi
    exact hkhi
  obtain ⟨r,hr,hrsum⟩ := interval_sum_composition l u hlu (n:=k-N) (by omega) (by omega)
  have hP : ∀ C : OrdinaryBookBlock hs,Nonempty
      (WeightedPureBlock C.1.1 ((s-1 : ℕ) : ℤ) (ordinaryBookTarget C.1.1) (r C)) := by
    intro C
    exact ordinary_book_pure_block C.1.1 (mem_largeBlocks.mp C.1.2).2 (hr C).1 (hr C).2
  let P := fun C => Classical.choice (hP C)
  apply lattice_book_of_block_circuit (show 3≤ s by omega) (upperBlockEquiv hs)
    (upperPureRank hs r) (upperPureBlock hs r P) (upper_book_scale_rigidity hs r P)
  have ha : Fintype.card (BookAnchor (show 3≤ s by omega))=s-1 := by
    simp only [BookAnchor,Fintype.card_coe,card_erase_of_mem (mem_univ _),card_univ,Fintype.card_fin]
  change Fintype.card (BookAnchor (show 3≤ s by omega) ⊕
    (Σ b : UpperBookBlock hs,Fin (upperPureRank hs r b)))=k
  rw [Fintype.card_sum,Fintype.card_sigma]
  simp only [Fintype.card_fin,ha,Fintype.sum_sum_type]
  simp only [upperPureRank,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,hrsum]
  dsimp only [N] at hlo ⊢
  omega

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart176

section BundlePart177
/- Source: Papers/GraphicalZonotopes/AnchorBlockCounts.lean -/




@[expose] public section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H : Type*} [DecidableEq H]

def anchorBlocks (S : Finset H) (a : H) : Finset (Finset H) :=
  S.powerset.filter (fun C => a∈C ∧ 3≤ C.card)

@[simp] theorem mem_anchorBlocks {S C : Finset H} {a : H} :
    C∈anchorBlocks S a ↔ C⊆S ∧ a∈C ∧ 3≤ C.card := by
  simp only [anchorBlocks,mem_filter,mem_powerset]

private theorem nontrivial_erase_notMem (S : Finset H) (a : H)
    {T : Finset H} (hT : T∈nontrivialSubsets (S.erase a)) : a∉T := by
  intro h
  exact (notMem_erase a S) ((mem_powerset.mp (mem_filter.mp hT).1) h)

private theorem insert_anchor_injOn (S : Finset H) (a : H) :
    Set.InjOn (fun T : Finset H => insert a T) (↑(nontrivialSubsets (S.erase a)) : Set (Finset H)) := by
  intro T hT U hU he
  have haT := nontrivial_erase_notMem S a hT
  have haU := nontrivial_erase_notMem S a hU
  have h := congrArg (fun X : Finset H => X.erase a) he
  simpa only [erase_insert haT,erase_insert haU] using h

theorem anchorBlocks_eq_image (S : Finset H) (a : H) (ha : a∈S) :
    anchorBlocks S a=(nontrivialSubsets (S.erase a)).image (insert a) := by
  ext C
  rw [mem_anchorBlocks,mem_image]
  constructor
  · rintro ⟨hCS,haC,hC⟩
    refine ⟨C.erase a,mem_filter.mpr ⟨mem_powerset.mpr ?_,?_⟩,insert_erase haC⟩
    · intro x hx
      exact mem_erase.mpr ⟨(mem_erase.mp hx).1,hCS (mem_of_mem_erase hx)⟩
    · rw [card_erase_of_mem haC]
      omega
  · rintro ⟨T,hT,rfl⟩
    have hTS := mem_powerset.mp (mem_filter.mp hT).1
    have haT := nontrivial_erase_notMem S a hT
    refine ⟨insert_subset_iff.mpr ⟨ha,hTS.trans (erase_subset _ _)⟩,mem_insert_self _ _,?_⟩
    rw [card_insert_of_notMem haT]
    have hc := (mem_filter.mp hT).2
    omega

theorem anchorBlocks_card (S : Finset H) (a : H) (ha : a∈S) :
    (anchorBlocks S a).card=2^(S.card-1)-S.card := by
  rw [anchorBlocks_eq_image S a ha,card_image_of_injOn (insert_anchor_injOn S a),
    nontrivialSubsets_card,card_erase_of_mem ha]
  have hs : 1≤ S.card := card_pos.mpr ⟨a,ha⟩
  omega

theorem blockDimensionSum_erase_add_anchor (S : Finset H) (a : H) (ha : a∈S) :
    blockDimensionSum (S.erase a)+
      (∑ C∈anchorBlocks S a,(C.card.choose 2-1))=blockDimensionSum S := by
  have hsum : (∑ C∈anchorBlocks S a,(C.card.choose 2-1))=
      ∑ T∈(S.erase a).powerset,((insert a T).card.choose 2-1) := by
    rw [anchorBlocks_eq_image S a ha,sum_image (insert_anchor_injOn S a)]
    apply sum_subset (filter_subset _ _)
    intro T hT hn
    have haT : a∉T := fun h => (notMem_erase a S) ((mem_powerset.mp hT) h)
    have hsmall : ¬2≤ T.card := fun h => hn (mem_filter.mpr ⟨hT,h⟩)
    have hcases : T.card=0 ∨ T.card=1 := by omega
    rw [card_insert_of_notMem haT]
    rcases hcases with h | h <;> norm_num [h,Nat.choose]
  rw [hsum]
  conv_rhs => rw [← insert_erase ha]
  unfold blockDimensionSum
  rw [sum_powerset_insert (notMem_erase a S)]

theorem anchorBlocks_dimension_sum (S : Finset H) (a : H) (ha : a∈S) :
    (∑ C∈anchorBlocks S a,(C.card.choose 2-1))=
      cliqueCapacity S.card-cliqueCapacity (S.card-1) := by
  have h := blockDimensionSum_erase_add_anchor S a ha
  have hc := cliqueCapacity_eq_dimension_sum S
  have hd := cliqueCapacity_eq_dimension_sum (S.erase a)
  rw [card_erase_of_mem ha] at hd
  omega

end BooleanModule
end GraphicalZonotopes

end
end BundlePart177

section BundlePart178
/- Source: Papers/GraphicalZonotopes/BookIntervalArithmetic.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators

theorem cliqueCapacity_int_formula (s : ℕ) :
    (cliqueCapacity s : ℤ)=(s.choose 2 : ℤ)*(2 : ℤ)^(s-2)-(2 : ℤ)^s+(s : ℤ)+2 := by
  let S := (univ : Finset (Fin s))
  have hsum := blockDimensionSum_add_cliques S
  rw [sum_powerset_choose_two] at hsum
  have hcount := card_filter_add_card_filter_not (s:=S.powerset) (p:=fun C => 2≤ C.card)
  rw [small_subsets_card,card_powerset] at hcount
  change (nontrivialSubsets S).card+(S.card+1)=2^S.card at hcount
  have hcap := cliqueCapacity_eq_dimension_sum S
  have hScard : S.card=s := by simp [S]
  rw [hScard] at hsum hcount hcap
  have hsum' : (blockDimensionSum S : ℤ)+((nontrivialSubsets S).card : ℤ)=
      (s.choose 2 : ℤ)*(2 : ℤ)^(s-2) := by exact_mod_cast hsum
  have hcount' : ((nontrivialSubsets S).card : ℤ)+(s : ℤ)+1=(2 : ℤ)^s := by exact_mod_cast hcount
  have hcap' : (cliqueCapacity s : ℤ)=(blockDimensionSum S : ℤ)+1 := by exact_mod_cast hcap
  linarith

theorem cliqueCapacity_pred_le {s : ℕ} (hs : 1≤ s) :
    cliqueCapacity (s-1)≤ cliqueCapacity s := by
  let S := (univ : Finset (Fin s))
  let a : Fin s := ⟨0,by omega⟩
  have ha : a∈S := mem_univ _
  have h := blockDimensionSum_erase_add_anchor S a ha
  have hcap := cliqueCapacity_eq_dimension_sum S
  have hprev := cliqueCapacity_eq_dimension_sum (S.erase a)
  rw [card_erase_of_mem ha] at hprev
  have hScard : S.card=s := by simp [S]
  rw [hScard] at hcap hprev
  omega

theorem two_mul_le_choose_two {n : ℕ} (hn : 5≤ n) : 2*n≤ n.choose 2 := by
  rw [Nat.choose_two_right]
  apply (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr
  calc
    (2*n)*2=n*4 := by ring
    _ ≤ n*(n-1) := Nat.mul_le_mul_left n (by omega)

private theorem pow_pred_four {s : ℕ} (hs : 3≤ s) :
    (2 : ℤ)^(s-1)=4*(2 : ℤ)^(s-3) := by
  have he : s-1=(s-3)+2 := by omega
  calc
    (2 : ℤ)^(s-1)=(2 : ℤ)^((s-3)+2) := congrArg (fun n => (2 : ℤ)^n) he
    _ = _ := by rw [pow_add]; norm_num; ring

private theorem pow_pred_two {s : ℕ} (hs : 3≤ s) :
    (2 : ℤ)^(s-2)=2*(2 : ℤ)^(s-3) := by
  have he : s-2=(s-3)+1 := by omega
  calc
    (2 : ℤ)^(s-2)=(2 : ℤ)^((s-3)+1) := congrArg (fun n => (2 : ℤ)^n) he
    _ = _ := by rw [pow_succ]; ring

private theorem pow_eight {s : ℕ} (hs : 3≤ s) :
    (2 : ℤ)^s=8*(2 : ℤ)^(s-3) := by
  have he : s=(s-3)+3 := by omega
  calc
    (2 : ℤ)^s=(2 : ℤ)^((s-3)+3) := congrArg (fun n => (2 : ℤ)^n) he
    _ = _ := by rw [pow_add]; norm_num; ring

theorem threshold_start_le_previous_capacity {s : ℕ} (hs : 6≤ s) :
    2^(s-1)-s+1≤ cliqueCapacity (s-1) := by
  have hpowge : s≤2^(s-1) := by
    have h := Nat.lt_two_pow_self (n := s-1)
    omega
  have hcast : ((2^(s-1)-s+1 : ℕ) : ℤ)=(2 : ℤ)^(s-1)-(s : ℤ)+1 := by
    rw [Nat.cast_add,Nat.cast_sub hpowge,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  have hchoose : (8 : ℤ)≤((s-1).choose 2 : ℤ) := by
    have h := two_mul_le_choose_two (show 5≤ s-1 by omega)
    have h' : (8 : ℕ)≤(s-1).choose 2 := by omega
    exact_mod_cast h'
  have hnonneg : 0≤(((s-1).choose 2 : ℤ)-8)*(2 : ℤ)^(s-3) :=
    mul_nonneg (by omega) (by positivity)
  have hformula := cliqueCapacity_int_formula (s-1)
  have hexp : s-1-2=s-3 := by omega
  rw [hexp,pow_pred_four (by omega),Nat.cast_sub (show 1≤ s by omega),Nat.cast_one] at hformula
  have hbound : ((2^(s-1)-s+1 : ℕ) : ℤ)≤(cliqueCapacity (s-1) : ℤ) := by
    rw [hcast,pow_pred_four (by omega)]
    nlinarith
  exact_mod_cast hbound

theorem bookUpperIntervalStart_int_formula {s : ℕ} (hs : 5≤ s) :
    (bookUpperIntervalStart s : ℤ)=((s : ℤ)-2)*(2 : ℤ)^(s-1)+2*(s : ℤ)-2-(s.choose 2 : ℤ) := by
  have h := BookBlock_lower_sum (show 2≤ s by omega)
  have h2 : 2≤(s-2)*2^(s-1)+2*s := by omega
  have hc : s.choose 2≤(s-2)*2^(s-1)+2*s-2 := by omega
  unfold bookUpperIntervalStart
  rw [Nat.cast_sub hc,Nat.cast_sub h2,Nat.cast_add,Nat.cast_mul,Nat.cast_mul,
    Nat.cast_sub (show 2≤ s by omega),Nat.cast_pow]
  norm_num

theorem upper_start_le_threshold_end {s : ℕ} (hs : 6≤ s) :
    bookUpperIntervalStart s≤ cliqueCapacity s-cliqueCapacity (s-1)+1 := by
  have hmono := cliqueCapacity_pred_le (show 1≤ s by omega)
  have hchoose : (s.choose 2 : ℤ)=((s-1).choose 2 : ℤ)+(s : ℤ)-1 := by
    have h := Nat.choose_succ_succ (s-1) 1
    change (s-1+1).choose 2=(s-1).choose 1+(s-1).choose 2 at h
    have he : s-1+1=s := by omega
    have hc : s.choose 2=(s-1)+(s-1).choose 2 := by
      simpa only [he,Nat.choose_one_right] using h
    rw [hc,Nat.cast_add,Nat.cast_sub (show 1≤ s by omega),Nat.cast_one]
    ring
  have hcpNat := two_mul_le_choose_two (show 5≤ s-1 by omega)
  have hcsNat := two_mul_le_choose_two (show 5≤ s by omega)
  have hcp : 2*((s : ℤ)-1)≤((s-1).choose 2 : ℤ) := by
    have h' : ((2*(s-1) : ℕ) : ℤ)≤((s-1).choose 2 : ℤ) := by exact_mod_cast hcpNat
    simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub (show 1≤ s by omega),Nat.cast_one] using h'
  have hcs : 2*(s : ℤ)≤(s.choose 2 : ℤ) := by exact_mod_cast hcsNat
  have hp : 0≤(((s-1).choose 2 : ℤ)-2*(s : ℤ)+2)*(2 : ℤ)^(s-3) :=
    mul_nonneg (by omega) (by positivity)
  have hgap : ((cliqueCapacity s-cliqueCapacity (s-1)+1 : ℕ) : ℤ)-
      (bookUpperIntervalStart s : ℤ)=
      (((s-1).choose 2 : ℤ)-2*(s : ℤ)+2)*(2 : ℤ)^(s-3)+
        (s.choose 2 : ℤ)-2*(s : ℤ)+4 := by
    rw [Nat.cast_add,Nat.cast_sub hmono,Nat.cast_one,
      bookUpperIntervalStart_int_formula (by omega),cliqueCapacity_int_formula,
      cliqueCapacity_int_formula]
    have hexp : s-1-2=s-3 := by omega
    rw [hexp,pow_pred_two (s:=s) (by omega),pow_eight (s:=s) (by omega),pow_pred_four (s:=s) (by omega),
      Nat.cast_sub (show 1≤ s by omega),Nat.cast_one,hchoose]
    ring
  have hbound : (bookUpperIntervalStart s : ℤ)≤
      ((cliqueCapacity s-cliqueCapacity (s-1)+1 : ℕ) : ℤ) := by linarith
  exact_mod_cast hbound

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart178

section BundlePart179
/- Source: Papers/GraphicalZonotopes/SignedPairBases.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H J : Type*} [Fintype H] [LinearOrder H] [Fintype J] [DecidableEq J]

/-- Finite reindexing of pure module data preserves the exact weighted
relation and all positive integral scale bounds. -/
def weightedPureBlock_of_data (C : Finset H) (M : ℤ) (v : ResponseQuotient H)
    (x : J → PairIn C → ℝ) (hx : ∀ j,PureRealizable C (x j))
    (w : J → ℤ) (hw : ∀ j,0< w j) (hM : ∀ j,w j≤ M)
    (hind : LinearIndependent ℝ (fun j => blockClass C (x j)))
    (hsum : (∑ j,(w j : ℝ) • blockClass C (x j))=v)
    {r : ℕ} (hr : Fintype.card J=r) : WeightedPureBlock C M v r := by
  classical
  let e : Fin r ≃ J := (finCongr hr.symm).trans (Fintype.equivFin J).symm
  exact {
    column := fun j => x (e j)
    realizable := fun j => hx (e j)
    weight := fun j => w (e j)
    positive := fun j => hw (e j)
    bounded := fun j => hM (e j)
    independent := hind.comp e e.injective
    weighted_sum := (e.sum_comp (fun j => (w j : ℝ) • blockClass C (x j))).trans hsum
  }

theorem reference_pair_expansion (C : Finset H) (e₀ : PairIn C)
    (x : PairIn C → ℝ) (hx : x e₀=0) :
    (∑ p : ↥((univ : Finset (PairIn C)).erase e₀),x p.1 • pairIndicator {p.1})=x := by
  classical
  funext e
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,pairIndicator,mem_singleton,mul_ite,mul_one,mul_zero]
  by_cases he : e=e₀
  · subst e
    have hn : ∀ p : ↥((univ : Finset (PairIn C)).erase e₀),e₀≠ p.1 :=
      fun p => Ne.symm (mem_erase.mp p.2).1
    simp only [hn,ite_false,sum_const_zero,hx]
  · let p₀ : ↥((univ : Finset (PairIn C)).erase e₀) := ⟨e,mem_erase.mpr ⟨he,mem_univ _⟩⟩
    have hp : ∀ p : ↥((univ : Finset (PairIn C)).erase e₀),e=p.1 ↔ p=p₀ := by
      intro p
      exact ⟨fun h => Subtype.ext h.symm,fun h => (congrArg Subtype.val h).symm⟩
    simp only [hp,sum_ite_eq',mem_univ,ite_true]
    rfl

/-- The complete signed pair basis excluding one reference coordinate,
realized by genuine positive or negative pure Boolean pair modules. -/
def signed_pair_basis (C : Finset H) (hC : 3≤ C.card) (e₀ : PairIn C)
    (ε : ℝ) (hε : ε=1 ∨ ε= -1) (w : PairIn C → ℤ)
    (hw₀ : w e₀=0) (hw : ∀ e,e≠ e₀ → 0< w e) (M : ℤ)
    (hM : ∀ e,e≠ e₀ → w e≤ M) :
    WeightedPureBlock C M (blockClass C (ε • (fun e => (w e : ℝ)))) (C.card.choose 2-1) := by
  classical
  let J := ↥((univ : Finset (PairIn C)).erase e₀)
  let x : J → PairIn C → ℝ := fun p => ε • pairIndicator {p.1}
  have hx : ∀ p,PureRealizable C (x p) := by
    intro p
    rcases hε with h | h
    · simpa only [x,h,one_smul] using pureRealizable_pair C p.1
    · simpa only [x,h,neg_one_smul] using pureRealizable_negative_pair C hC p.1
  have hε₀ : ε≠0 := by rcases hε with rfl | rfl <;> norm_num
  have hind : LinearIndependent ℝ (fun p : J => blockClass C (x p)) := by
    have hi := reference_pair_columns_independent C e₀
    rw [Fintype.linearIndependent_iff]
    intro t ht p
    have hz : (∑ q : J,(t q*ε) • blockClass C (pairIndicator {q.1}))=0 := by
      simpa only [x,map_smul,mul_smul] using ht
    exact (mul_eq_zero.mp ((Fintype.linearIndependent_iff.mp hi) _ hz p)).resolve_right hε₀
  have hsum : (∑ p : J,(w p.1 : ℝ) • blockClass C (x p))=
      blockClass C (ε • (fun e => (w e : ℝ))) := by
    have he : (∑ p : J,(w p.1 : ℝ) • x p)=ε • (fun e => (w e : ℝ)) := by
      calc
        _ = ε • (∑ p : J,(w p.1 : ℝ) • pairIndicator {p.1}) := by
          simp only [x,smul_sum]
          exact sum_congr rfl (fun p _ => smul_comm _ _ _)
        _ = _ := congrArg (fun y : PairIn C → ℝ => ε • y)
          (reference_pair_expansion C e₀ (fun e => (w e : ℝ)) (by simp [hw₀]))
    simpa only [map_sum,map_smul] using congrArg (blockClass C) he
  apply weightedPureBlock_of_data C M _ x hx (fun p : J => w p.1)
    (fun p => hw p.1 (mem_erase.mp p.2).1)
    (fun p => hM p.1 (mem_erase.mp p.2).1) hind hsum
  simp only [J,Fintype.card_coe,card_erase_of_mem (mem_univ _),card_univ,pairIn_card]

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart179

section BundlePart180
/- Source: Papers/GraphicalZonotopes/PositiveStarInterpolation.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H : Type*} [Fintype H] [LinearOrder H]

private def starSeed (C : Finset H) (a : H) (ha : a∈C) (i : C.erase a) : PairIn C :=
  pairOfNe C a i.1 (Ne.symm (mem_erase.mp i.2).1) ha (mem_of_mem_erase i.2)

private theorem starSeed_eq_iff (C : Finset H) (a : H) (ha : a∈C)
    (i : C.erase a) (e : PairIn C) :
    e=starSeed C a ha i ↔
      (e.1.1.1=a ∧ e.1.1.2=i.1) ∨ (e.1.1.2=a ∧ e.1.1.1=i.1) := by
  have h := congrArg (fun A : Finset (PairIn C) => e∈A)
    (starPairs_singleton C (Ne.symm (mem_erase.mp i.2).1) ha (mem_of_mem_erase i.2))
  simpa only [mem_starPairs,StarPair,mem_singleton,starSeed] using Iff.of_eq h.symm

private theorem starSeed_injective (C : Finset H) (a : H) (ha : a∈C) :
    Function.Injective (starSeed C a ha) := by
  intro i j hij
  have hi := (starSeed_eq_iff C a ha i (starSeed C a ha i)).mp rfl
  have hj := (starSeed_eq_iff C a ha j (starSeed C a ha i)).mp hij
  apply Subtype.ext
  rcases hi with ⟨hia,hi⟩ | ⟨hia,hi⟩ <;> rcases hj with ⟨hja,hj⟩ | ⟨hja,hj⟩
  · exact hi.symm.trans hj
  · exact False.elim ((mem_erase.mp j.2).1 (hj.symm.trans hia))
  · exact False.elim ((mem_erase.mp j.2).1 (hj.symm.trans hia))
  · exact hi.symm.trans hj

private theorem starSeed_range (C : Finset H) (a : H) (ha : a∈C) (e : PairIn C) :
    e∈starPairs C a (C.erase a) ↔ ∃ i : C.erase a,e=starSeed C a ha i := by
  rw [mem_starPairs]
  constructor
  · rintro (⟨hu,hv⟩ | ⟨hv,hu⟩)
    · exact ⟨⟨e.1.1.2,hv⟩,(starSeed_eq_iff C a ha _ e).mpr (Or.inl ⟨hu,rfl⟩)⟩
    · exact ⟨⟨e.1.1.1,hu⟩,(starSeed_eq_iff C a ha _ e).mpr (Or.inr ⟨hv,rfl⟩)⟩
  · rintro ⟨i,hi⟩
    rcases (starSeed_eq_iff C a ha i e).mp hi with ⟨hu,hv⟩ | ⟨hv,hu⟩
    · exact Or.inl ⟨hu,hv.symm ▸ i.2⟩
    · exact Or.inr ⟨hv,hu.symm ▸ i.2⟩

private theorem starSeed_not_extra (C : Finset H) (a : H) (ha : a∈C)
    (D : Finset (PairIn C)) (hD : D⊆cliquePairs C (C.erase a)) :
    ∀ i,starSeed C a ha i∉D := by
  intro i h
  obtain ⟨hu,hv⟩ := mem_cliquePairs.mp (hD h)
  rcases (starSeed_eq_iff C a ha i (starSeed C a ha i)).mp rfl with hh | hh
  · exact (mem_erase.mp hu).1 hh.1
  · exact (mem_erase.mp hv).1 hh.1

private def starOwner (C : Finset H) (a : H) (D : Finset (PairIn C))
    (hD : D⊆cliquePairs C (C.erase a)) (d : D) : C.erase a :=
  ⟨d.1.1.1.1,(mem_cliquePairs.mp (hD d.2)).1⟩

private def starOutNeighbors (C : Finset H) (a : H) (D : Finset (PairIn C))
    (i : C.erase a) : Finset H :=
  insert a ((D.filter (fun e => e.1.1.1=i.1)).image (fun e => e.1.1.2))

private theorem starOutNeighbors_subset (C : Finset H) (a : H) (ha : a∈C)
    (D : Finset (PairIn C)) (i : C.erase a) : starOutNeighbors C a D i⊆C := by
  intro b hb
  rcases mem_insert.mp hb with rfl | hb
  · exact ha
  · obtain ⟨e,he,rfl⟩ := mem_image.mp hb
    exact e.2.2

private theorem starOutNeighbors_ne (C : Finset H) (a : H)
    (D : Finset (PairIn C)) (i : C.erase a) : i.1∉starOutNeighbors C a D i := by
  intro h
  rcases mem_insert.mp h with h | h
  · exact (mem_erase.mp i.2).1 h
  · obtain ⟨e,he,hi⟩ := mem_image.mp h
    have he' := (mem_filter.mp he).2
    exact (ne_of_lt e.1.2.1) (he'.trans hi.symm)

private theorem starOutNeighbors_characterization (C : Finset H) (a : H) (ha : a∈C)
    (D : Finset (PairIn C)) (hD : D⊆cliquePairs C (C.erase a))
    (i : C.erase a) (e : PairIn C) :
    StarPair i.1 (starOutNeighbors C a D i) e.1.1.1 e.1.1.2 ↔
      e=starSeed C a ha i ∨ ∃ h : e∈D,starOwner C a D hD ⟨e,h⟩=i := by
  constructor
  · rintro (⟨hu,hv⟩ | ⟨hv,hu⟩)
    · rcases mem_insert.mp hv with hv | hv
      · exact Or.inl ((starSeed_eq_iff C a ha i e).mpr (Or.inr ⟨hv,hu⟩))
      · obtain ⟨d,hd,hv⟩ := mem_image.mp hv
        have hdu := (mem_filter.mp hd).2
        have he : e=d := by
          apply Subtype.ext
          apply Subtype.ext
          exact Prod.ext (hu.trans hdu.symm) hv.symm
        have heD : e∈D := he.symm ▸ (mem_filter.mp hd).1
        exact Or.inr ⟨heD,Subtype.ext hu⟩
    · rcases mem_insert.mp hu with hu | hu
      · exact Or.inl ((starSeed_eq_iff C a ha i e).mpr (Or.inl ⟨hu,hv⟩))
      · obtain ⟨d,hd,hu⟩ := mem_image.mp hu
        have hdu := (mem_filter.mp hd).2
        have hlt : e.1.1.2< e.1.1.1 := by
          simpa only [hdu,hu,hv] using d.1.2.1
        exact False.elim ((not_lt_of_ge e.1.2.1.le) hlt)
  · rintro (h | ⟨heD,howner⟩)
    · rcases (starSeed_eq_iff C a ha i e).mp h with ⟨hu,hv⟩ | ⟨hv,hu⟩
      · exact Or.inr ⟨hv,hu.symm ▸ mem_insert_self _ _⟩
      · exact Or.inl ⟨hu,hv.symm ▸ mem_insert_self _ _⟩
    · have hu : e.1.1.1=i.1 := congrArg Subtype.val howner
      exact Or.inl ⟨hu,mem_insert_of_mem (mem_image.mpr
        ⟨e,mem_filter.mpr ⟨heD,hu⟩,rfl⟩)⟩

private theorem starPivot_realizable (C : Finset H) (hC : 3≤ C.card)
    (a : H) (ha : a∈C) (D : Finset (PairIn C))
    (hD : D⊆cliquePairs C (C.erase a)) :
    ∀ j : C.erase a ⊕ D, PureRealizable C
      (pivotColumns (starSeed C a ha) D (starOwner C a D hD) j) := by
  intro j
  cases j with
  | inl i =>
    have he : pivotColumns (starSeed C a ha) D (starOwner C a D hD) (Sum.inl i)=
        pairIndicator (starPairs C i.1 (starOutNeighbors C a D i)) := by
      funext e
      change pivotPositive _ _ _ i e=_
      simp only [pairIndicator,mem_starPairs,starOutNeighbors_characterization C a ha D hD i e]
      unfold pivotPositive
      by_cases hs : e=starSeed C a ha i
      · have hn : e∉D := hs.symm ▸ starSeed_not_extra C a ha D hD i
        have hn' := starSeed_not_extra C a ha D hD i
        simp [hs,hn']
      · by_cases heD : e∈D
        · simp only [hs,ite_false,dite_eq_left heD,zero_add,false_or]
          congr 1
          apply propext
          constructor
          · exact fun h => ⟨heD,h⟩
          · exact fun ⟨_,h⟩ => h
        · simp [hs,heD]
    rw [he]
    exact pureRealizable_star C (mem_of_mem_erase i.2)
      (starOutNeighbors_subset C a ha D i) ⟨a,mem_insert_self _ _⟩
      (starOutNeighbors_ne C a D i)
  | inr d =>
    have he : pivotColumns (starSeed C a ha) D (starOwner C a D hD) (Sum.inr d)=
        -pairIndicator {d.1} := by
      funext e
      by_cases h : e=d.1 <;> simp [pivotColumns,pairIndicator,h]
    rw [he]
    exact pureRealizable_negative_pair C hC d.1

private theorem starPivot_sum (C : Finset H) (a : H) (ha : a∈C)
    (D : Finset (PairIn C)) (hD : D⊆cliquePairs C (C.erase a)) :
    (∑ j : C.erase a ⊕ D,pivotColumns (starSeed C a ha) D (starOwner C a D hD) j)=
      starVector C a := by
  rw [pivotColumns_sum]
  funext e
  change (∑ i : C.erase a,if e=starSeed C a ha i then (1 : ℝ) else 0)=
    if e∈starPairs C a (C.erase a) then 1 else 0
  by_cases he : e∈starPairs C a (C.erase a)
  · obtain ⟨i,rfl⟩ := (starSeed_range C a ha e).mp he
    have hinj := starSeed_injective C a ha
    simp only [hinj.eq_iff,ite_eq_left he]
    simp
  · have hn : ∀ i : C.erase a,e≠ starSeed C a ha i :=
      fun i h => he ((starSeed_range C a ha e).mpr ⟨i,h⟩)
    simp [he,hn]

/-- The second range in the positive-star interpolation. New pairs are
inserted into an actual partial-star column and canceled by a negative pure
pair. Unique seed pairs and the omitted reference pair prove independence. -/
theorem positive_star_large_interpolation (C : Finset H) (hC : 3≤ C.card)
    (a : H) (ha : a∈C) {k : ℕ} (hk : C.card-1≤ k) (hkC : k≤ C.card.choose 2-1) :
    Nonempty (PureDecomposition C (blockClass C (starVector C a)) k) := by
  classical
  have hecard : (C.erase a).card=C.card-1 := card_erase_of_mem ha
  have hsub : C.erase a⊆C := erase_subset _ _
  have hchoose : C.card.choose 2=(C.card-1).choose 2+(C.card-1) := by
    have h := Nat.choose_succ_succ (C.card-1) 1
    have hs : C.card-1+1=C.card := by omega
    simpa only [Nat.succ_eq_add_one,hs,Nat.choose_one_right,Nat.add_comm] using h
  obtain ⟨e₀,he₀⟩ := cliquePairs_nonempty C (C.erase a) hsub (by omega)
  have hcapacity : k-(C.card-1)≤((cliquePairs C (C.erase a)).erase e₀).card := by
    rw [card_erase_of_mem he₀,cliquePairs_card C (C.erase a) hsub,hecard]
    omega
  obtain ⟨D,hD,hDc⟩ := exists_subset_card_eq hcapacity
  have hD' : D⊆cliquePairs C (C.erase a) := hD.trans (erase_subset _ _)
  let seed := starSeed C a ha
  let owner := starOwner C a D hD'
  let x := pivotColumns seed D owner
  have hreal : ∀ j,PureRealizable C (x j) := starPivot_realizable C hC a ha D hD'
  have hind : LinearIndependent ℝ x := pivotColumns_linearIndependent seed
    (starSeed_injective C a ha) D owner (starSeed_not_extra C a ha D hD')
  have hzero : ∀ j,x j e₀=0 := by
    apply pivotColumns_zero_at seed D owner e₀
    · exact fun h => (mem_erase.mp (hD h)).1 rfl
    · intro i he
      have hm := he.symm ▸ he₀
      exact starSeed_not_extra C a ha (cliquePairs C (C.erase a)) (Subset.refl _) i hm
  apply pureDecomposition_of_vectors x hreal
    (blockClass_linearIndependent_of_reference C e₀ x hind hzero) _ _
  · rw [← map_sum]
    exact congrArg (blockClass C) (starPivot_sum C a ha D hD')
  · simp only [Fintype.card_sum,Fintype.card_coe,hecard,hDc]
    omega

/-- The positive half of Lemma 7.7, with every intermediate count and the
actual response quotient. -/
theorem positive_star_interpolation (C : Finset H) (hC : 3≤ C.card)
    (a : H) (ha : a∈C) {k : ℕ} (hk : 1≤ k) (hkC : k≤ C.card.choose 2-1) :
    Nonempty (PureDecomposition C (blockClass C (starVector C a)) k) := by
  by_cases h : k≤ C.card-1
  · exact positive_star_small_interpolation C hC a ha hk h
  · exact positive_star_large_interpolation C hC a ha (by omega) hkC

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart180

section BundlePart181
/- Source: Papers/GraphicalZonotopes/NegativeStarInterpolation.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H : Type*} [Fintype H] [LinearOrder H]

private theorem pairIndicator_singleton_eq (C : Finset H) (e : PairIn C) :
    pairIndicator {e}=(fun f => if f=e then (1 : ℝ) else 0) := by
  funext f
  simp only [pairIndicator,mem_singleton]

private theorem pairOfNe_char (C : Finset H) (a b : H) (hab : a≠ b)
    (ha : a∈C) (hb : b∈C) (e : PairIn C) :
    e=pairOfNe C a b hab ha hb ↔
      (e.1.1.1=a ∧ e.1.1.2=b) ∨ (e.1.1.2=a ∧ e.1.1.1=b) := by
  have h := congrArg (fun A : Finset (PairIn C) => e∈A)
    (starPairs_singleton C hab ha hb)
  simpa only [mem_starPairs,StarPair,mem_singleton] using Iff.of_eq h.symm

private theorem pairOfNe_symm (C : Finset H) (a b : H) (hab : a≠ b)
    (ha : a∈C) (hb : b∈C) :
    pairOfNe C a b hab ha hb=pairOfNe C b a (Ne.symm hab) hb ha := by
  apply (pairOfNe_char C b a (Ne.symm hab) hb ha _).mpr
  rcases pairOfNe_endpoints C a b hab ha hb with h | h
  · exact Or.inr ⟨h.2,h.1⟩
  · exact Or.inl h

private theorem pairOfNe_other_eq (C : Finset H) (a b c : H) (hab : a≠ b)
    (hac : a≠ c) (ha : a∈C) (hb : b∈C) (hc : c∈C)
    (h : pairOfNe C a b hab ha hb=pairOfNe C a c hac ha hc) : b=c := by
  have hi := (pairOfNe_char C a b hab ha hb _).mp rfl
  have hj := (pairOfNe_char C a c hac ha hc _).mp h
  rcases hi with ⟨hia,hi⟩ | ⟨hia,hi⟩ <;> rcases hj with ⟨hja,hj⟩ | ⟨hja,hj⟩
  · exact hi.symm.trans hj
  · exact False.elim (hac (hia.symm.trans hj))
  · exact False.elim (hac (hia.symm.trans hj))
  · exact hi.symm.trans hj

private theorem pureRealizable_pair_sum (C : Finset H) (b u v : H)
    (hbu : b≠ u) (hbv : b≠ v) (huv : u≠ v)
    (hb : b∈C) (hu : u∈C) (hv : v∈C) :
    PureRealizable C (pairIndicator {pairOfNe C b u hbu hb hu}+
      pairIndicator {pairOfNe C b v hbv hb hv}) := by
  have he : pairIndicator {pairOfNe C b u hbu hb hu}+
      pairIndicator {pairOfNe C b v hbv hb hv}=
      pairIndicator (starPairs C b {u,v}) := by
    rw [← starPairs_singleton C hbu hb hu,← starPairs_singleton C hbv hb hv]
    have hs : ({u,v} : Finset H)={u}∪{v} := by simp
    rw [hs,starPairs_union]
    have hd := starPairs_disjoint C b (B:={u}) (D:={v}) (disjoint_singleton_left.mpr
      (by simpa only [mem_singleton] using huv))
      (by simpa only [mem_singleton] using hbu)
      (by simpa only [mem_singleton] using hbv)
    funext e
    by_cases he1 : e∈starPairs C b {u} <;> by_cases he2 : e∈starPairs C b {v}
    · exact False.elim (disjoint_left.mp hd he1 he2)
    all_goals simp [pairIndicator,he1,he2]
  rw [he]
  apply pureRealizable_star C (a:=b) (B:={u,v}) hb
  · exact insert_subset_iff.mpr ⟨hu,singleton_subset_iff.mpr hv⟩
  · exact insert_nonempty _ _
  · intro h
    rcases mem_insert.mp h with h | h
    · exact hbu h
    · exact hbv (mem_singleton.mp h)

private theorem pivotPositive_unique_owner {E I : Type*} [DecidableEq E]
    [Fintype I] [DecidableEq I] (seed : I → E) (D : Finset E)
    (owner : D → I) (hinj : Function.Injective owner) (d : D) :
    pivotPositive seed D owner (owner d)=
      (fun e => if e=seed (owner d) then (1 : ℝ) else 0)+
      (fun e => if e=d.1 then (1 : ℝ) else 0) := by
  funext e
  simp only [pivotPositive,Pi.add_apply]
  congr 1
  by_cases he : e∈D
  · rw [dite_eq_left he]
    have hh : owner ⟨e,he⟩=owner d ↔ e=d.1 := by
      rw [hinj.eq_iff]
      exact Subtype.ext_iff
    simp only [hh]
  · have hn : e≠ d.1 := fun h => he (h.symm ▸ d.2)
    simp [he,hn]

private theorem pivotPositive_no_owner {E I : Type*} [DecidableEq E]
    [Fintype I] [DecidableEq I] (seed : I → E) (D : Finset E)
    (owner : D → I) (i : I) (h : ¬∃ d,owner d=i) :
    pivotPositive seed D owner i=fun e => if e=seed i then (1 : ℝ) else 0 := by
  funext e
  unfold pivotPositive
  by_cases he : e∈D
  · have hn : owner ⟨e,he⟩≠ i := fun hh => h ⟨⟨e,he⟩,hh⟩
    simp [he,hn]
  · simp [he]

private theorem extraTip_exists (C : Finset H) (a q : H) (ha : a∈C)
    (D : Finset (PairIn C)) (hD : D⊆starPairs C a ((C.erase a).erase q)) (d : D) :
    ∃ b : (C.erase a).erase q,
      d.1=pairOfNe C a b.1 (Ne.symm (mem_erase.mp (mem_of_mem_erase b.2)).1)
        ha (mem_of_mem_erase (mem_of_mem_erase b.2)) := by
  rcases mem_starPairs.mp (hD d.2) with ⟨hu,hv⟩ | ⟨hv,hu⟩
  · refine ⟨⟨d.1.1.1.2,hv⟩,?_⟩
    exact (pairOfNe_char C _ _ _ _ _ _).mpr (Or.inl ⟨hu,rfl⟩)
  · refine ⟨⟨d.1.1.1.1,hu⟩,?_⟩
    exact (pairOfNe_char C _ _ _ _ _ _).mpr (Or.inr ⟨hv,rfl⟩)

private def extraTip (C : Finset H) (a q : H) (ha : a∈C)
    (D : Finset (PairIn C)) (hD : D⊆starPairs C a ((C.erase a).erase q)) (d : D) :=
  Classical.choose (extraTip_exists C a q ha D hD d)

private theorem extraTip_spec (C : Finset H) (a q : H) (ha : a∈C)
    (D : Finset (PairIn C)) (hD : D⊆starPairs C a ((C.erase a).erase q)) (d : D) :
    d.1=pairOfNe C a (extraTip C a q ha D hD d).1
      (Ne.symm (mem_erase.mp (mem_of_mem_erase (extraTip C a q ha D hD d).2)).1)
      ha (mem_of_mem_erase (mem_of_mem_erase (extraTip C a q ha D hD d).2)) :=
  Classical.choose_spec (extraTip_exists C a q ha D hD d)

private def cliqueOwner (C : Finset H) (a q : H) (ha : a∈C) (hq : q∈C.erase a)
    (D : Finset (PairIn C)) (hD : D⊆starPairs C a ((C.erase a).erase q))
    (d : D) : cliquePairs C (C.erase a) :=
  let b := extraTip C a q ha D hD d
  ⟨pairOfNe C q b.1 (Ne.symm (mem_erase.mp b.2).1)
    (mem_of_mem_erase hq) (mem_of_mem_erase (mem_of_mem_erase b.2)),by
    rw [mem_cliquePairs]
    rcases pairOfNe_endpoints C q b.1 (Ne.symm (mem_erase.mp b.2).1)
      (mem_of_mem_erase hq) (mem_of_mem_erase (mem_of_mem_erase b.2)) with h | h
    · exact ⟨h.1.symm ▸ hq,h.2.symm ▸ mem_of_mem_erase b.2⟩
    · exact ⟨h.1.symm ▸ mem_of_mem_erase b.2,h.2.symm ▸ hq⟩⟩

private theorem cliqueOwner_injective (C : Finset H) (a q : H)
    (ha : a∈C) (hq : q∈C.erase a) (D : Finset (PairIn C))
    (hD : D⊆starPairs C a ((C.erase a).erase q)) :
    Function.Injective (cliqueOwner C a q ha hq D hD) := by
  intro d e h
  let b := extraTip C a q ha D hD d
  let c := extraTip C a q ha D hD e
  have hh := pairOfNe_other_eq C q b.1 c.1
    (Ne.symm (mem_erase.mp b.2).1) (Ne.symm (mem_erase.mp c.2).1)
    (mem_of_mem_erase hq) (mem_of_mem_erase (mem_of_mem_erase b.2))
    (mem_of_mem_erase (mem_of_mem_erase c.2)) (congrArg Subtype.val h)
  have ht : extraTip C a q ha D hD d=extraTip C a q ha D hD e := Subtype.ext hh
  apply Subtype.ext
  rw [extraTip_spec C a q ha D hD d,extraTip_spec C a q ha D hD e,ht]

private theorem cliqueSeed_not_extra (C : Finset H) (a q : H)
    (D : Finset (PairIn C)) (hD : D⊆starPairs C a ((C.erase a).erase q)) :
    ∀ i : cliquePairs C (C.erase a),i.1∉D := by
  intro i hi
  obtain ⟨hu,hv⟩ := mem_cliquePairs.mp i.2
  rcases mem_starPairs.mp (hD hi) with ⟨hh,_⟩ | ⟨hh,_⟩
  · exact (mem_erase.mp hu).1 hh
  · exact (mem_erase.mp hv).1 hh

private theorem cliquePivot_realizable (C : Finset H) (hC : 3≤ C.card)
    (a q : H) (ha : a∈C) (hq : q∈C.erase a) (D : Finset (PairIn C))
    (hD : D⊆starPairs C a ((C.erase a).erase q)) :
    ∀ j : cliquePairs C (C.erase a) ⊕ D,
      PureRealizable C (pivotColumns Subtype.val D (cliqueOwner C a q ha hq D hD) j) := by
  intro j
  cases j with
  | inl i =>
    by_cases hi : ∃ d,cliqueOwner C a q ha hq D hD d=i
    · obtain ⟨d,rfl⟩ := hi
      change PureRealizable C (pivotPositive _ _ _ _)
      rw [pivotPositive_unique_owner Subtype.val D _
        (cliqueOwner_injective C a q ha hq D hD) d]
      let b := extraTip C a q ha D hD d
      have hbq : b.1≠ q := (mem_erase.mp b.2).1
      have hba : b.1≠ a := (mem_erase.mp (mem_of_mem_erase b.2)).1
      have hbC : b.1∈C := mem_of_mem_erase (mem_of_mem_erase b.2)
      have hqC : q∈C := mem_of_mem_erase hq
      have hqa : q≠ a := (mem_erase.mp hq).1
      have he1 : (cliqueOwner C a q ha hq D hD d).1=
          pairOfNe C b.1 q hbq hbC hqC := pairOfNe_symm C q b.1 (Ne.symm hbq) hqC hbC
      have he2 : d.1=pairOfNe C b.1 a hba hbC ha :=
        (extraTip_spec C a q ha D hD d).trans (pairOfNe_symm C a b.1 (Ne.symm hba) ha hbC)
      simp only [he1,he2]
      have hp := pureRealizable_pair_sum C b.1 q a hbq hba hqa hbC hqC ha
      rw [pairIndicator_singleton_eq,pairIndicator_singleton_eq] at hp
      exact hp
    · change PureRealizable C (pivotPositive _ _ _ _)
      rw [pivotPositive_no_owner Subtype.val D _ i hi]
      have hp := pureRealizable_pair C i.1
      rw [pairIndicator_singleton_eq] at hp
      exact hp
  | inr d =>
    have he : pivotColumns (fun i : cliquePairs C (C.erase a) => i.1) D
        (cliqueOwner C a q ha hq D hD) (Sum.inr d)=-pairIndicator {d.1} := by
      funext e
      by_cases h : e=d.1 <;> simp [pivotColumns,pairIndicator,h]
    rw [he]
    exact pureRealizable_negative_pair C hC d.1

private theorem cliquePivot_sum (C : Finset H) (a q : H)
    (ha : a∈C) (hq : q∈C.erase a) (D : Finset (PairIn C))
    (hD : D⊆starPairs C a ((C.erase a).erase q)) :
    (∑ j : cliquePairs C (C.erase a) ⊕ D,
      pivotColumns Subtype.val D (cliqueOwner C a q ha hq D hD) j)=
      pairIndicator (cliquePairs C (C.erase a)) := by
  rw [pivotColumns_sum]
  funext e
  by_cases he : e∈cliquePairs C (C.erase a)
  · have heq : ∀ i : cliquePairs C (C.erase a),e=i.1 ↔ i=⟨e,he⟩ :=
      fun i => ⟨fun h => Subtype.ext h.symm,fun h => congrArg Subtype.val h.symm⟩
    simp [heq,pairIndicator,he]
  · have hn : ∀ i : cliquePairs C (C.erase a),e≠ i.1 := fun i h => he (h.symm ▸ i.2)
    simp [hn,pairIndicator,he]

/-- The upper range of the negative-star interpolation. The initial clique
on the other hubs is extended using distinct seed pairs incident with `q`;
the reference pair `aq` is never activated. -/
theorem negative_star_large_interpolation (C : Finset H) (hC : 3≤ C.card)
    (a : H) (ha : a∈C) {k : ℕ} (hk : (C.card-1).choose 2≤ k)
    (hkC : k≤ C.card.choose 2-1) :
    Nonempty (PureDecomposition C (-blockClass C (starVector C a)) k) := by
  classical
  have hecard : (C.erase a).card=C.card-1 := card_erase_of_mem ha
  have hsub : C.erase a⊆C := erase_subset _ _
  have hchoose : C.card.choose 2=(C.card-1).choose 2+(C.card-1) := by
    have h := Nat.choose_succ_succ (C.card-1) 1
    have hs : C.card-1+1=C.card := by omega
    simpa only [Nat.succ_eq_add_one,hs,Nat.choose_one_right,Nat.add_comm] using h
  obtain ⟨q,hq⟩ := card_pos.mp (show 0<(C.erase a).card by omega)
  have hecard2 : ((C.erase a).erase q).card=C.card-2 := by
    rw [card_erase_of_mem hq,hecard]
    omega
  have hsub2 : (C.erase a).erase q⊆C := (erase_subset _ _).trans hsub
  have hn : a∉(C.erase a).erase q := fun h => (notMem_erase a C) (mem_of_mem_erase h)
  have hcapacity : k-(C.card-1).choose 2≤(starPairs C a ((C.erase a).erase q)).card := by
    rw [starPairs_card C ha hsub2 hn,hecard2]
    omega
  obtain ⟨D,hD,hDc⟩ := exists_subset_card_eq hcapacity
  let owner := cliqueOwner C a q ha hq D hD
  let seed := fun i : cliquePairs C (C.erase a) => i.1
  let x := pivotColumns seed D owner
  let e₀ := pairOfNe C a q (Ne.symm (mem_erase.mp hq).1) ha (mem_of_mem_erase hq)
  have hnotseed : ∀ i : cliquePairs C (C.erase a),e₀≠ seed i := by
    intro i hi
    obtain ⟨hu,hv⟩ := mem_cliquePairs.mp i.2
    have hends := pairOfNe_endpoints C a q (Ne.symm (mem_erase.mp hq).1) ha (mem_of_mem_erase hq)
    rcases hends with hh | hh
    · exact (mem_erase.mp hu).1 ((congrArg (fun e : PairIn C => e.1.1.1) hi).symm.trans hh.1)
    · exact (mem_erase.mp hv).1 ((congrArg (fun e : PairIn C => e.1.1.2) hi).symm.trans hh.2)
  have heD : e₀∉D := by
    intro h
    have hs := mem_starPairs.mp (hD h)
    have hends := (pairOfNe_char C a q (Ne.symm (mem_erase.mp hq).1) ha (mem_of_mem_erase hq) e₀).mp rfl
    rcases hs with ⟨hu,hv⟩ | ⟨hv,hu⟩ <;> rcases hends with hh | hh
    · exact (mem_erase.mp hv).1 hh.2
    · exact (mem_erase.mp hq).1 (hh.2.symm.trans hu)
    · exact (mem_erase.mp hq).1 (hh.2.symm.trans hv)
    · exact (mem_erase.mp hu).1 hh.2
  apply pureDecomposition_of_vectors x (cliquePivot_realizable C hC a q ha hq D hD)
    (blockClass_linearIndependent_of_reference C e₀ x
      (pivotColumns_linearIndependent seed Subtype.val_injective D owner
        (cliqueSeed_not_extra C a q D hD))
      (pivotColumns_zero_at seed D owner e₀ heD hnotseed)) _ _
  · rw [← map_sum,cliquePivot_sum C a q ha hq D hD]
    exact clique_without_vertex_class C a
  · simp only [Fintype.card_sum,Fintype.card_coe,cliquePairs_card C (C.erase a) hsub,
      hecard,hDc]
    omega

/-- The negative half of Lemma 7.7, with every count through the entire
block dimension and actual Boolean realizations. -/
theorem negative_star_interpolation (C : Finset H) (hC : 3≤ C.card)
    (a : H) (ha : a∈C) {k : ℕ} (hk : 1≤ k) (hkC : k≤ C.card.choose 2-1) :
    Nonempty (PureDecomposition C (-blockClass C (starVector C a)) k) := by
  by_cases h : k≤(C.card-1).choose 2
  · exact negative_star_small_interpolation C hC a ha hk h
  · exact negative_star_large_interpolation C hC a ha (by omega) hkC

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart181

section BundlePart182
/- Source: Papers/GraphicalZonotopes/TwoAnchorPureBlocks.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H : Type*} [Fintype H] [LinearOrder H]

theorem starVector_eq_zero_of_notMem (C : Finset H) {a : H} (ha : a∉C) :
    starVector C a=0 := by
  funext e
  have hu : a≠ e.1.1.1 := fun h => ha (h.symm ▸ e.2.1)
  have hv : a≠ e.1.1.2 := fun h => ha (h.symm ▸ e.2.2)
  simp only [starVector_eq,hu,hv,false_or,ite_false,Pi.zero_apply]

def PureDecomposition.toWeightedBlock {C : Finset H} {v : ResponseQuotient H} {r : ℕ}
    (P : PureDecomposition C v r) (M : ℤ) (hM : 1≤ M) : WeightedPureBlock C M v r := by
  classical
  choose x hx using P.block_supported
  exact {
    column := x
    realizable := fun j => ⟨P.functions j,P.monotone_boolean j,P.essential j,P.ignored j,hx j⟩
    weight := fun _ => 1
    positive := fun _ => by norm_num
    bounded := fun _ => hM
    independent := by simpa only [← hx] using P.independent
    weighted_sum := by simpa only [Int.cast_one,one_smul,← hx] using P.sum_eq
  }

def twoAnchorTarget (C : Finset H) (a b : H) : ResponseQuotient H :=
  -((-1 : ℝ)^(C.card-3) • blockClass C (starVector C a+starVector C b))

theorem twoAnchorTarget_symm (C : Finset H) (a b : H) :
    twoAnchorTarget C a b=twoAnchorTarget C b a := by rw [twoAnchorTarget,twoAnchorTarget,add_comm]

theorem one_anchor_pure_block (C : Finset H) (hC : 3≤ C.card)
    {a b : H} (ha : a∈C) (hb : b∉C) {k : ℕ} (hk : 1≤ k)
    (hkC : k≤ C.card.choose 2-1) :
    Nonempty (WeightedPureBlock C 2 (twoAnchorTarget C a b) k) := by
  have hb0 := starVector_eq_zero_of_notMem C hb
  rcases neg_one_pow_eq_or ℝ (C.card-3) with h | h
  · obtain ⟨P⟩ := negative_star_interpolation C hC a ha hk hkC
    refine ⟨?_⟩
    have hp := P.toWeightedBlock 2 (by norm_num)
    simpa only [twoAnchorTarget,hb0,add_zero,h,one_smul] using hp
  · obtain ⟨P⟩ := positive_star_interpolation C hC a ha hk hkC
    refine ⟨?_⟩
    have hp := P.toWeightedBlock 2 (by norm_num)
    simpa only [twoAnchorTarget,hb0,add_zero,h,neg_one_smul,neg_neg] using hp

theorem pair_contains_two_iff (C : Finset H) {a b : H} (hab : a< b)
    (ha : a∈C) (hb : b∈C) (e : PairIn C) :
    ((a=e.1.1.1 ∨ a=e.1.1.2) ∧ (b=e.1.1.1 ∨ b=e.1.1.2)) ↔
      e=orderedPair C a b hab ha hb := by
  constructor
  · rintro ⟨(hae | hae),(hbe | hbe)⟩
    · exact False.elim ((ne_of_lt hab) (hae.trans hbe.symm))
    · apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext hae.symm hbe.symm
    · have hbad : b< a := by simpa only [← hae,← hbe] using e.1.2.1
      exact False.elim ((not_lt_of_ge hab.le) hbad)
    · exact False.elim ((ne_of_lt hab) (hae.trans hbe.symm))
  · rintro rfl
    exact ⟨Or.inl rfl,Or.inr rfl⟩

def twoAnchorPairWeight (C : Finset H) (a b : H) (e : PairIn C) : ℤ :=
  2-((if a=e.1.1.1 ∨ a=e.1.1.2 then 1 else 0)+
    (if b=e.1.1.1 ∨ b=e.1.1.2 then 1 else 0))

theorem twoAnchorPairWeight_zero (C : Finset H) {a b : H} (hab : a< b)
    (ha : a∈C) (hb : b∈C) :
    twoAnchorPairWeight C a b (orderedPair C a b hab ha hb)=0 := by
  simp [twoAnchorPairWeight,orderedPair]

theorem twoAnchorPairWeight_positive (C : Finset H) {a b : H} (hab : a< b)
    (ha : a∈C) (hb : b∈C) (e : PairIn C)
    (he : e≠ orderedPair C a b hab ha hb) : 0< twoAnchorPairWeight C a b e := by
  have hn := mt (pair_contains_two_iff C hab ha hb e).mp he
  by_cases hA : a=e.1.1.1 ∨ a=e.1.1.2 <;>
    by_cases hB : b=e.1.1.1 ∨ b=e.1.1.2 <;> simp_all [twoAnchorPairWeight]

theorem twoAnchorPairWeight_bounded (C : Finset H) (a b : H) (e : PairIn C) :
    twoAnchorPairWeight C a b e≤2 := by
  unfold twoAnchorPairWeight
  split <;> split <;> norm_num

theorem twoAnchorPairWeight_vector (C : Finset H) (a b : H) :
    (fun e => (twoAnchorPairWeight C a b e : ℝ))=
      (fun _ : PairIn C => (2 : ℝ))-(starVector C a+starVector C b) := by
  funext e
  simp only [twoAnchorPairWeight,Int.cast_sub,Int.cast_ofNat,Int.cast_add,
    Pi.sub_apply,Pi.add_apply,starVector_eq]
  by_cases hA : a=e.1.1.1 ∨ a=e.1.1.2 <;>
    by_cases hB : b=e.1.1.1 ∨ b=e.1.1.2 <;> simp [hA,hB]

/-- Every double-anchor block other than the single connector is filled to
its full quotient dimension with positive integral weights one or two. -/
theorem two_anchor_full_pure_block (C : Finset H) (hC : 3≤ C.card)
    {a b : H} (hab : a< b) (ha : a∈C) (hb : b∈C) :
    Nonempty (WeightedPureBlock C 2 (twoAnchorTarget C a b) (C.card.choose 2-1)) := by
  let e₀ := orderedPair C a b hab ha hb
  let ε : ℝ := (-1)^(C.card-3)
  let P := signed_pair_basis C hC e₀ ε (neg_one_pow_eq_or ℝ (C.card-3))
    (twoAnchorPairWeight C a b) (twoAnchorPairWeight_zero C hab ha hb)
    (fun e he => twoAnchorPairWeight_positive C hab ha hb e he) 2
    (fun e _ => twoAnchorPairWeight_bounded C a b e)
  have hz : blockClass C (fun _ : PairIn C => (2 : ℝ))=0 :=
    (blockClass_eq_zero_iff C e₀ _).mpr ⟨2,fun _ => rfl⟩
  have hv : blockClass C (ε • (fun e => (twoAnchorPairWeight C a b e : ℝ)))=
      twoAnchorTarget C a b := by
    rw [twoAnchorPairWeight_vector,map_smul,map_sub,hz,zero_sub,smul_neg]
    rfl
  exact ⟨hv ▸ P⟩

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart182

section BundlePart183
/- Source: Papers/GraphicalZonotopes/TwoAnchorConnector.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators

variable {H : Type*} [Fintype H] [LinearOrder H]

structure OrderedTriple (H : Type*) [LinearOrder H] where
  a : H
  b : H
  c : H
  ab : a< b
  bc : b< c

namespace OrderedTriple
variable (T : OrderedTriple H)

def clique : Finset H := {T.a,T.b,T.c}

theorem ac : T.a< T.c := T.ab.trans T.bc

@[simp] theorem card_clique : T.clique.card=3 := by
  simp [clique,T.ab.ne,T.ac.ne,T.bc.ne]

@[simp] theorem a_mem : T.a∈T.clique := by simp [clique]
@[simp] theorem b_mem : T.b∈T.clique := by simp [clique]
@[simp] theorem c_mem : T.c∈T.clique := by simp [clique]

def abPair : PairIn T.clique := orderedPair T.clique T.a T.b T.ab T.a_mem T.b_mem
def acPair : PairIn T.clique := orderedPair T.clique T.a T.c T.ac T.a_mem T.c_mem
def bcPair : PairIn T.clique := orderedPair T.clique T.b T.c T.bc T.b_mem T.c_mem

@[simp] theorem ac_ne_ab : T.acPair≠ T.abPair := by
  intro h
  exact T.bc.ne (congrArg (fun e : PairIn T.clique => e.1.1.2) h).symm

@[simp] theorem bc_ne_ab : T.bcPair≠ T.abPair := by
  intro h
  exact T.ab.ne (congrArg (fun e : PairIn T.clique => e.1.1.1) h).symm

/-- On a triple, the sum of the two distinguished stars is the distinguished
pair plus the constant pair vector. -/
theorem two_stars_vector :
    starVector T.clique T.a+starVector T.clique T.b=
      pairIndicator {T.abPair}+(fun _ : PairIn T.clique => (1 : ℝ)) := by
  funext e
  have hu : e.1.1.1=T.a ∨ e.1.1.1=T.b ∨ e.1.1.1=T.c := by
    simpa only [clique,mem_insert,mem_singleton] using e.2.1
  have hv : e.1.1.2=T.a ∨ e.1.1.2=T.b ∨ e.1.1.2=T.c := by
    simpa only [clique,mem_insert,mem_singleton] using e.2.2
  have hne : e.1.1.1≠ e.1.1.2 := ne_of_lt e.1.2.1
  have he : e=T.abPair ↔
      (T.a=e.1.1.1 ∨ T.a=e.1.1.2) ∧ (T.b=e.1.1.1 ∨ T.b=e.1.1.2) :=
    (pair_contains_two_iff T.clique T.ab T.a_mem T.b_mem e).symm
  simp only [Pi.add_apply,starVector_eq,pairIndicator,mem_singleton,he]
  rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv <;>
    simp [hu,hv,T.ab.ne,T.ac.ne,T.bc.ne,Ne.symm T.ab.ne,Ne.symm T.ac.ne,Ne.symm T.bc.ne] at hne ⊢

theorem connector_response :
    blockClass T.clique (-pairIndicator {T.abPair})=twoAnchorTarget T.clique T.a T.b := by
  have hz : blockClass T.clique (fun _ : PairIn T.clique => (1 : ℝ))=0 :=
    (blockClass_eq_zero_iff T.clique T.abPair _).mpr ⟨1,fun _ => rfl⟩
  rw [twoAnchorTarget,T.two_stars_vector,map_add,hz,add_zero,map_neg,T.card_clique]
  norm_num

/-- The unique connector column is a genuine negative pure pair module. -/
def pureBlock : WeightedPureBlock T.clique 2 (twoAnchorTarget T.clique T.a T.b) 1 := by
  have hne : blockClass T.clique (-pairIndicator {T.abPair})≠0 := by
    intro hz
    obtain ⟨c,hc⟩ := (blockClass_eq_zero_iff T.clique T.abPair _).mp hz
    have hab := hc T.abPair
    have hac := hc T.acPair
    simp [pairIndicator] at hab hac
    linarith
  exact {
    column := fun _ => -pairIndicator {T.abPair}
    realizable := fun _ => pureRealizable_negative_pair T.clique (by rw [T.card_clique]) T.abPair
    weight := fun _ => 1
    positive := fun _ => by norm_num
    bounded := fun _ => by norm_num
    independent := (linearIndependent_unique_iff).mpr hne
    weighted_sum := by simpa using T.connector_response
  }

def firstRow : HubResponseRow H := pairRow T.clique T.acPair
def secondRow : HubResponseRow H := pairRow T.clique T.bcPair

@[simp] theorem firstRow_clique : rowClique T.firstRow=T.clique := rowClique_pairRow _ _
@[simp] theorem secondRow_clique : rowClique T.secondRow=T.clique := rowClique_pairRow _ _

theorem row_index_eq : rowCliqueIndex T.firstRow=rowCliqueIndex T.secondRow := by
  apply Subtype.ext
  exact T.firstRow_clique.trans T.secondRow_clique.symm

@[simp] theorem threshold_a_first : thresholdSignedStar T.a T.firstRow=1 := by
  rw [thresholdSignedStar,T.firstRow_clique,T.card_clique]
  norm_num [firstRow,acPair,pairRow,orderedPair]

@[simp] theorem threshold_a_second : thresholdSignedStar T.a T.secondRow=0 := by
  simp [thresholdSignedStar,T.secondRow_clique,T.card_clique,secondRow,bcPair,pairRow,orderedPair,
    T.ab.ne,T.ac.ne]

@[simp] theorem threshold_b_first : thresholdSignedStar T.b T.firstRow=0 := by
  simp [thresholdSignedStar,T.firstRow_clique,T.card_clique,firstRow,acPair,pairRow,orderedPair,
    Ne.symm T.ab.ne,T.bc.ne]

@[simp] theorem threshold_b_second : thresholdSignedStar T.b T.secondRow=1 := by
  rw [thresholdSignedStar,T.secondRow_clique,T.card_clique]
  norm_num [secondRow,bcPair,pairRow,orderedPair]

@[simp] theorem pureBlock_first (j : Fin 1) :
    blockCoordinates T.clique (T.pureBlock.column j) T.firstRow=0 := by
  change blockCoordinates T.clique (-pairIndicator {T.abPair}) (pairRow T.clique T.acPair)=0
  rw [blockCoordinates_pairRow]
  simp [pairIndicator]

@[simp] theorem pureBlock_second (j : Fin 1) :
    blockCoordinates T.clique (T.pureBlock.column j) T.secondRow=0 := by
  change blockCoordinates T.clique (-pairIndicator {T.abPair}) (pairRow T.clique T.bcPair)=0
  rw [blockCoordinates_pairRow]
  simp [pairIndicator]

end OrderedTriple
end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart183

section BundlePart184
/- Source: Papers/GraphicalZonotopes/TwoAnchorBlockData.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H : Type*} [Fintype H] [LinearOrder H]

namespace OrderedTriple
variable (T : OrderedTriple H)

def block : BookBlock H := ⟨T.clique,mem_largeBlocks.mpr ⟨subset_univ _,by rw [T.card_clique]⟩⟩

structure OmittedBlock (C : BookBlock H) (r : ℕ)
    extends WeightedPureBlock C.1 2 (twoAnchorTarget C.1 T.a T.b) r where
  first_zero : ∀ j,blockCoordinates C.1 (column j) T.firstRow=0
  second_zero : ∀ j,blockCoordinates C.1 (column j) T.secondRow=0

def ordinaryOmittedBlock (C : BookBlock H) (hne : C.1≠ T.clique) {r : ℕ}
    (P : WeightedPureBlock C.1 2 (twoAnchorTarget C.1 T.a T.b) r) : T.OmittedBlock C r := by
  refine { P with first_zero := ?_,second_zero := ?_ }
  · intro j
    have hr : rowClique T.firstRow≠ C.1 := by rw [T.firstRow_clique]; exact Ne.symm hne
    change (if h : rowClique T.firstRow=C.1 then P.column j (pairAtRow C.1 T.firstRow h) else 0)=0
    exact dite_eq_right hr
  · intro j
    have hr : rowClique T.secondRow≠ C.1 := by rw [T.secondRow_clique]; exact Ne.symm hne
    change (if h : rowClique T.secondRow=C.1 then P.column j (pairAtRow C.1 T.secondRow h) else 0)=0
    exact dite_eq_right hr

def connectorOmittedBlock : T.OmittedBlock T.block 1 where
  toWeightedPureBlock := T.pureBlock
  first_zero := T.pureBlock_first
  second_zero := T.pureBlock_second

def lowerRank (C : BookBlock H) : ℕ :=
  if C.1=T.clique then 1 else
  if T.a∈C.1 ∧ T.b∈C.1 then C.1.card.choose 2-1 else
  if T.a∈C.1 ∨ T.b∈C.1 then 1 else 0

def upperRank (C : BookBlock H) : ℕ :=
  if C.1=T.clique then 1 else
  if T.a∈C.1 ∨ T.b∈C.1 then C.1.card.choose 2-1 else 0

theorem lowerRank_le_upperRank (C : BookBlock H) : T.lowerRank C≤ T.upperRank C := by
  have hsize := (mem_largeBlocks.mp C.2).2
  have hc : 1≤ C.1.card.choose 2-1 := by
    have h := Nat.choose_le_choose 2 hsize
    norm_num [Nat.choose] at h
    omega
  unfold lowerRank upperRank
  by_cases hC : C.1=T.clique <;> by_cases ha : T.a∈C.1 <;> by_cases hb : T.b∈C.1 <;>
    simp [hC,ha,hb,hc]

/-- Each local branch count in the exact interval is realized, with both
connector test coordinates zero for every pure column. -/
theorem omittedBlock_exists (C : BookBlock H) {r : ℕ}
    (hrlo : T.lowerRank C≤ r) (hrhi : r≤ T.upperRank C) :
    Nonempty (T.OmittedBlock C r) := by
  classical
  by_cases hC : C.1=T.clique
  · have hCe : C=T.block := Subtype.ext hC
    subst C
    have hr : r=1 := by
      simp only [lowerRank,upperRank,block,ite_true] at hrlo hrhi
      omega
    subst r
    exact ⟨T.connectorOmittedBlock⟩
  · apply Nonempty.map (T.ordinaryOmittedBlock C hC)
    have hsize := (mem_largeBlocks.mp C.2).2
    by_cases ha : T.a∈C.1
    · by_cases hb : T.b∈C.1
      · have hr : r=C.1.card.choose 2-1 := by
          simp only [lowerRank,upperRank,ite_eq_right hC,ha,hb,true_and,true_or,ite_true] at hrlo hrhi
          omega
        subst r
        exact two_anchor_full_pure_block C.1 hsize T.ab ha hb
      · have hlo : 1≤ r := by simpa only [lowerRank,ite_eq_right hC,ha,hb,
          true_and,false_or,true_or,ite_false,ite_true] using hrlo
        have hhi : r≤ C.1.card.choose 2-1 := by
          simpa only [upperRank,ite_eq_right hC,ha,true_or,ite_true] using hrhi
        exact one_anchor_pure_block C.1 hsize ha hb hlo hhi
    · by_cases hb : T.b∈C.1
      · have hlo : 1≤ r := by simpa only [lowerRank,ite_eq_right hC,ha,hb,
          false_and,false_or,ite_false,ite_true] using hrlo
        have hhi : r≤ C.1.card.choose 2-1 := by
          simpa only [upperRank,ite_eq_right hC,hb,or_true,ite_true] using hrhi
        rw [twoAnchorTarget_symm]
        exact one_anchor_pure_block C.1 hsize hb ha hlo hhi
      · have hr : r=0 := by
          simpa only [upperRank,ite_eq_right hC,ha,hb,false_or,ite_false,Nat.le_zero] using hrhi
        subst r
        have hz : twoAnchorTarget C.1 T.a T.b=0 := by
          simp only [twoAnchorTarget,starVector_eq_zero_of_notMem C.1 ha,
            starVector_eq_zero_of_notMem C.1 hb,add_zero,map_zero,smul_zero,neg_zero]
        exact ⟨{
          column := fun j => Fin.elim0 j
          realizable := fun j => Fin.elim0 j
          weight := fun j => Fin.elim0 j
          positive := fun j => Fin.elim0 j
          bounded := fun j => Fin.elim0 j
          independent := linearIndependent_empty_type
          weighted_sum := by simpa only [Fin.sum_univ_zero] using hz.symm
        }⟩

end OrderedTriple
end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart184

section BundlePart185
/- Source: Papers/GraphicalZonotopes/AnchoredWeightedCircuits.lean -/






@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise
variable {H J : Type*} [Fintype H] [LinearOrder H] [Fintype J] [DecidableEq J]

def anchoredWeights (w : J → ℤ) : Option J → ℤ
  | none => 1
  | some j => w j

theorem anchored_weighted_relation (F₀ : SetFunction H) (F : J → SetFunction H)
    (w : J → ℤ) (hind : LinearIndependent ℝ (fun j => responseClass (F j)))
    (hsum : responseClass F₀+∑ j,(w j : ℝ) • responseClass (F j)=0) :
    (fun j => (anchoredWeights w j : ℝ))∈LinearMap.ker (quotientRelation (anchoredFamily F₀ F)) ∧
      UniqueIntegrableRelation (anchoredFamily F₀ F) (fun j => (anchoredWeights w j : ℝ)) := by
  constructor
  · change quotientRelation (anchoredFamily F₀ F) _=0
    rw [quotientRelation_apply_eq_sum,Fintype.sum_option]
    simpa only [anchoredWeights,Int.cast_one,one_smul,anchoredFamily] using hsum
  · intro t ht
    have ht0 : quotientRelation (anchoredFamily F₀ F) t=0 :=
      (mem_quotientRelation_ker_iff _ _).mpr ht
    rw [quotientRelation_apply_eq_sum,Fintype.sum_option] at ht0
    change t none • responseClass F₀+∑ j,t (some j) • responseClass (F j)=0 at ht0
    have hsub : (∑ j,(t (some j)-t none*(w j : ℝ)) • responseClass (F j))=0 := by
      calc
        _ = (t none • responseClass F₀+∑ j,t (some j) • responseClass (F j))-
            t none • (responseClass F₀+∑ j,(w j : ℝ) • responseClass (F j)) := by
          simp only [sub_smul,sum_sub_distrib,smul_add,smul_sum,mul_smul]
          abel
        _ = 0 := by rw [ht0,hsum,smul_zero,sub_self]
    have hcoeff := (Fintype.linearIndependent_iff.mp hind) _ hsub
    refine ⟨t none,?_⟩
    funext i
    cases i with
    | none => simp [anchoredWeights]
    | some j =>
      simpa only [Pi.smul_apply,smul_eq_mul,anchoredWeights] using sub_eq_zero.mp (hcoeff j)

theorem lattice_book_of_anchored_weighted_circuit {s k : ℕ} (hs : 0< s)
    (F₀ : SetFunction (Fin s)) (F : J → SetFunction (Fin s))
    (hF₀ : IsMonotoneBoolean F₀) (hF : ∀ j,IsMonotoneBoolean (F j))
    (hess₀ : ∀ a,Essential F₀ a) (hess : ∀ j,∃ a,Essential (F j) a)
    (w : J → ℤ) (hw : ∀ j,0< w j) (M : ℤ) (hM₀ : 1≤ M) (hM : ∀ j,w j≤ M)
    (hind : LinearIndependent ℝ (fun j => responseClass (F j)))
    (hsum : responseClass F₀+∑ j,(w j : ℝ) • responseClass (F j)=0)
    (hcard : Fintype.card J+1=k) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=((M*k : ℤ) : ℝ) • graphicalZonotope (cliqueBook s k) := by
  classical
  obtain ⟨hrel,huniq⟩ := anchored_weighted_relation F₀ F w hind hsum
  let G := anchoredFamily F₀ F
  have hG : ∀ j,IsMonotoneBoolean (G j) := by
    intro j
    cases j with
    | none => exact hF₀
    | some j => exact hF j
  have hbranch : ∀ j,∃ a,Essential (G j) a := by
    intro j
    cases j with
    | none => exact ⟨⟨0,hs⟩,hess₀ ⟨0,hs⟩⟩
    | some j => exact hess j
  have hw' : ∀ j,0< anchoredWeights w j := by
    intro j
    cases j with
    | none => norm_num [anchoredWeights]
    | some j => exact hw j
  have hb : ∀ j,anchoredWeights w j≤ M := by
    intro j
    cases j with
    | none => exact hM₀
    | some j => exact hM j
  have hcard' : Fintype.card (Option J)=k := by simpa only [Fintype.card_option] using hcard
  apply lattice_book_of_finite_weighted_circuit hs G hG none hess₀ hbranch
    (anchoredWeights w) hw' hrel huniq hcard' (M*k)
  calc
    _ ≤ ∑ _ : Option J,M := sum_le_sum (fun j _ => hb j)
    _ = _ := by simp [hcard',mul_comm]

/-- Two genuine response coordinates detect the relative scales of two
threshold modules. The statement concerns their full integrability quotient;
no private row equations are omitted. -/
theorem two_threshold_coefficients_equal (a b : H)
    (r t : HubResponseRow H) (hrt : rowCliqueIndex r=rowCliqueIndex t)
    (har : thresholdSignedStar a r=1) (hat : thresholdSignedStar a t=0)
    (hbr : thresholdSignedStar b r=0) (hbt : thresholdSignedStar b t=1)
    (C : J → Finset H) (x : (j : J) → PairIn (C j) → ℝ)
    (hxt : ∀ j,blockCoordinates (C j) (x j) r=blockCoordinates (C j) (x j) t)
    (α β : ℝ) (w : J → ℝ)
    (hz : α • responseClass (thresholdStar a)+β • responseClass (thresholdStar b)+
      ∑ j,w j • blockClass (C j) (x j)=0) : α=β := by
  have hclass : coefficientClass (α • thresholdSignedStar a+β • thresholdSignedStar b+
      ∑ j,w j • blockCoordinates (C j) (x j))=0 := by
    simpa only [map_add,map_smul,map_sum,← thresholdStar_response_class,blockClass,
      LinearMap.comp_apply] using hz
  have he := (coefficientClass_eq_zero_iff _).mp hclass r t hrt
  simp only [Pi.add_apply,Pi.smul_apply,Finset.sum_apply,smul_eq_mul,har,hat,hbr,hbt,
    mul_one,mul_zero,add_zero,zero_add] at he
  have hsum : (∑ j,w j*blockCoordinates (C j) (x j) r)=
      ∑ j,w j*blockCoordinates (C j) (x j) t := sum_congr rfl (fun j _ => by rw [hxt j])
  rw [hsum] at he
  exact add_right_cancel he

theorem second_threshold_and_pure_independent (a b : H)
    (C : J → Finset H) (x : (j : J) → PairIn (C j) → ℝ)
    (F : J → SetFunction H) (hF : ∀ j,responseClass (F j)=blockClass (C j) (x j))
    (hind : LinearIndependent ℝ (fun j => responseClass (F j)))
    (r t : HubResponseRow H) (hrt : rowCliqueIndex r=rowCliqueIndex t)
    (har : thresholdSignedStar a r=1) (hat : thresholdSignedStar a t=0)
    (hbr : thresholdSignedStar b r=0) (hbt : thresholdSignedStar b t=1)
    (hxt : ∀ j,blockCoordinates (C j) (x j) r=blockCoordinates (C j) (x j) t) :
    LinearIndependent ℝ (fun j => responseClass (anchoredFamily (thresholdStar b) F j)) := by
  rw [Fintype.linearIndependent_iff]
  intro w hw j
  rw [Fintype.sum_option] at hw
  change w none • responseClass (thresholdStar b)+∑ i,w (some i) • responseClass (F i)=0 at hw
  have hz : (0 : ℝ) • responseClass (thresholdStar a)+
      w none • responseClass (thresholdStar b)+
      ∑ i,w (some i) • blockClass (C i) (x i)=0 := by
    simpa only [zero_smul,zero_add,← hF] using hw
  have hnone : w none=0 := (two_threshold_coefficients_equal a b r t hrt har hat hbr hbt
    C x hxt 0 (w none) (fun i => w (some i)) hz).symm
  cases j with
  | none => exact hnone
  | some j =>
    rw [hnone,zero_smul,zero_add] at hw
    exact (Fintype.linearIndependent_iff.mp hind) _ hw j

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart185

section BundlePart186
/- Source: Papers/GraphicalZonotopes/TwoAnchorBookCircuits.lean -/






@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise

/-- The complete two-threshold construction, uniformly in the ambient hub
set and every admissible intermediate sum of local block ranks. -/
theorem two_threshold_book_interval {s k : ℕ} (hs : 3≤ s)
    (T : OrderedTriple (Fin s))
    (hklo : (∑ C : BookBlock (Fin s),T.lowerRank C)+2≤ k)
    (hkhi : k≤(∑ C : BookBlock (Fin s),T.upperRank C)+2) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(((2*k : ℕ) : ℝ)) • graphicalZonotope (cliqueBook s k) := by
  classical
  obtain ⟨r,hr,hrsum⟩ := interval_sum_composition T.lowerRank T.upperRank T.lowerRank_le_upperRank
    (n:=k-2) (by omega) (by omega)
  let P := fun C => Classical.choice (T.omittedBlock_exists C (hr C).1 (hr C).2)
  have hF : ∀ C j,∃ F : SetFunction (Fin s),IsMonotoneBoolean F ∧
      (∀ a,a∈C.1 → Essential F a) ∧
      (∀ a,a∉C.1 → ∀ X,F (insert a X)=F X) ∧
      responseClass F=blockClass C.1 ((P C).column j) := fun C j => (P C).realizable j
  choose F hFb hFe hFi hFc using hF
  let J := Σ C : BookBlock (Fin s),Fin (r C)
  let G : J → SetFunction (Fin s) := fun j => F j.1 j.2
  let w : J → ℤ := fun j => (P j.1).weight j.2
  have hG : ∀ j,IsMonotoneBoolean (G j) := fun j => hFb j.1 j.2
  have hGc : ∀ j : J,responseClass (G j)=blockClass j.1.1 ((P j.1).column j.2) :=
    fun j => hFc j.1 j.2
  have hess : ∀ j,∃ a,Essential (G j) a := by
    intro j
    obtain ⟨a,ha⟩ := card_pos.mp (show 0< j.1.1.card by
      have h := (mem_largeBlocks.mp j.1.2).2
      omega)
    exact ⟨a,hFe j.1 j.2 a ha⟩
  have hpair : ∀ C : BookBlock (Fin s),∃ p : PairIn C.1,True := by
    intro C
    obtain ⟨p,hp⟩ := cliquePairs_nonempty C.1 C.1 (Subset.refl _)
      (by have h := (mem_largeBlocks.mp C.2).2; omega)
    exact ⟨p,trivial⟩
  have hind : LinearIndependent ℝ (fun j => responseClass (G j)) := by
    simp_rw [hGc]
    exact block_families_independent Subtype.val Subtype.val_injective
      (fun C => (hpair C).choose) (fun C => (P C).column) (fun C => (P C).independent)
  have hRest : LinearIndependent ℝ
      (fun j => responseClass (anchoredFamily (thresholdStar T.b) G j)) :=
    second_threshold_and_pure_independent T.a T.b (fun j : J => j.1.1)
      (fun j => (P j.1).column j.2) G hGc hind T.firstRow T.secondRow T.row_index_eq
      T.threshold_a_first T.threshold_a_second T.threshold_b_first T.threshold_b_second
      (fun j => ((P j.1).first_zero j.2).trans ((P j.1).second_zero j.2).symm)
  have hanchors : responseClass (thresholdStar T.a)+responseClass (thresholdStar T.b)=
      ∑ C : BookBlock (Fin s),(-1 : ℝ)^(C.1.card-3) •
        blockClass C.1 (starVector C.1 T.a+starVector C.1 T.b) := by
    rw [threshold_response_largeBlocks,threshold_response_largeBlocks,← sum_add_distrib]
    apply sum_congr rfl
    intro C hC
    simp only [map_add,smul_add]
  have hpures : (∑ j : J,(w j : ℝ) • responseClass (G j))=
      ∑ C : BookBlock (Fin s),twoAnchorTarget C.1 T.a T.b := by
    rw [Fintype.sum_sigma]
    apply sum_congr rfl
    intro C hC
    simpa only [w,hGc] using (P C).weighted_sum
  have hsum : responseClass (thresholdStar T.a)+
      ∑ j : Option J,(anchoredWeights w j : ℝ) •
        responseClass (anchoredFamily (thresholdStar T.b) G j)=0 := by
    rw [Fintype.sum_option]
    simp only [anchoredWeights,Int.cast_one,anchoredFamily,one_smul]
    rw [← add_assoc,hpures,hanchors]
    simp only [twoAnchorTarget,sum_neg_distrib,add_neg_cancel]
  have hRestB : ∀ j,IsMonotoneBoolean (anchoredFamily (thresholdStar T.b) G j) := by
    intro j
    cases j with
    | none => exact thresholdStar_boolean T.b
    | some j => exact hG j
  have hRestE : ∀ j,∃ a,Essential (anchoredFamily (thresholdStar T.b) G j) a := by
    intro j
    cases j with
    | none => exact ⟨T.b,thresholdStar_essential (by simpa using hs) T.b T.b⟩
    | some j => exact hess j
  have hw : ∀ j,0< anchoredWeights w j := by
    intro j
    cases j with
    | none => norm_num [anchoredWeights]
    | some j => exact (P j.1).positive j.2
  have hb : ∀ j,anchoredWeights w j≤2 := by
    intro j
    cases j with
    | none => norm_num [anchoredWeights]
    | some j => exact (P j.1).bounded j.2
  have hcard : Fintype.card (Option J)+1=k := by
    rw [Fintype.card_option,Fintype.card_sigma]
    simp only [Fintype.card_fin,hrsum]
    omega
  obtain ⟨f,hfn,hfi,hfe,hfg,hfd,hfm,hfl,R,hRl,hRn,hR⟩ :=
    lattice_book_of_anchored_weighted_circuit (by omega) (thresholdStar T.a)
      (anchoredFamily (thresholdStar T.b) G) (thresholdStar_boolean T.a) hRestB
      (thresholdStar_essential (by simpa using hs) T.a) hRestE
      (anchoredWeights w) hw 2 (by norm_num) hb hRest hsum hcard
  exact ⟨f,hfn,hfi,hfe,hfg,hfd,hfm,hfl,R,hRl,hRn,by simpa only [Int.cast_mul,
    Int.cast_ofNat,Int.cast_natCast,Nat.cast_mul,Nat.cast_ofNat] using hR⟩

def initialTriple {s : ℕ} (hs : 3≤ s) : OrderedTriple (Fin s) where
  a := ⟨0,by omega⟩
  b := ⟨1,by omega⟩
  c := ⟨2,by omega⟩
  ab := by change (0 : ℕ)<1; omega
  bc := by change (1 : ℕ)<2; omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem two_threshold_four_counts :
    (∑ C : BookBlock (Fin 4),(initialTriple (by decide : 3≤4)).lowerRank C)=10 ∧
    (∑ C : BookBlock (Fin 4),(initialTriple (by decide : 3≤4)).upperRank C)=12 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem two_threshold_five_counts :
    (∑ C : BookBlock (Fin 5),(initialTriple (by decide : 3≤5)).lowerRank C)=37 ∧
    (∑ C : BookBlock (Fin 5),(initialTriple (by decide : 3≤5)).upperRank C)=51 := by
  decide

/-- The four-hub overlap bridge of Lemma 7.9, including both endpoint sizes. -/
theorem two_threshold_four_bridge {k : ℕ} (hklo : 12≤ k) (hkhi : k≤14) :
    ∃ f : SetFunction (Fin 4⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook 4 k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin 4⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(((2*k : ℕ) : ℝ)) • graphicalZonotope (cliqueBook 4 k) := by
  apply two_threshold_book_interval (by decide) (initialTriple (by decide))
  · rw [two_threshold_four_counts.1]
    exact hklo
  · rw [two_threshold_four_counts.2]
    exact hkhi

/-- The five-hub overlap bridge of Lemma 7.9, with every count 39 through 53. -/
theorem two_threshold_five_bridge {k : ℕ} (hklo : 39≤ k) (hkhi : k≤53) :
    ∃ f : SetFunction (Fin 5⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook 5 k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin 5⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(((2*k : ℕ) : ℝ)) • graphicalZonotope (cliqueBook 5 k) := by
  apply two_threshold_book_interval (by decide) (initialTriple (by decide))
  · rw [two_threshold_five_counts.1]
    exact hklo
  · rw [two_threshold_five_counts.2]
    exact hkhi

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart186

section BundlePart187
/- Source: Papers/GraphicalZonotopes/ThresholdBookCircuits.lean -/








@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise
variable {H : Type*} [Fintype H] [LinearOrder H]

abbrev AnchorBlock (a : H) := ↥(anchorBlocks (univ : Finset H) a)

def anchorSignedClass (a : H) (C : AnchorBlock a) : ResponseQuotient H :=
  (-1 : ℝ)^(C.1.card-3) • blockClass C.1 (starVector C.1 a)

/-- The threshold response is the sum of its signed stars over every clique
block containing the anchor, with all other actual rows zero. -/
theorem threshold_response_block_sum (a : H) :
    responseClass (thresholdStar a)=∑ C : AnchorBlock a,anchorSignedClass a C := by
  have hcoord : thresholdSignedStar a=
      ∑ C : AnchorBlock a,(-1 : ℝ)^(C.1.card-3) •
        blockCoordinates C.1 (starVector C.1 a) := by
    funext r
    rw [Finset.sum_apply]
    by_cases hr : rowClique r∈anchorBlocks (univ : Finset H) a
    · let C₀ : AnchorBlock a := ⟨rowClique r,hr⟩
      rw [sum_eq_single C₀]
      · change thresholdSignedStar a r=
          (-1 : ℝ)^((rowClique r).card-3)*
            blockCoordinates (rowClique r) (starVector (rowClique r) a) r
        have he : blockCoordinates (rowClique r) (starVector (rowClique r) a) r=
            starVector (rowClique r) a (pairAtRow (rowClique r) r rfl) := by
          change (if h : rowClique r=rowClique r then
            starVector (rowClique r) a (pairAtRow (rowClique r) r h) else 0)=_
          rw [dite_eq_left rfl]
        rw [he,starVector_eq]
        have hsize := (mem_anchorBlocks.mp hr).2.2
        change (if 3≤(rowClique r).card ∧ (a=r.1.1.1 ∨ a=r.1.1.2) then
          (-1 : ℝ)^((rowClique r).card-3) else 0)=
          (-1 : ℝ)^((rowClique r).card-3)*(if a=r.1.1.1 ∨ a=r.1.1.2 then 1 else 0)
        by_cases h : a=r.1.1.1 ∨ a=r.1.1.2 <;> simp [hsize,h]
      · intro C hC hne
        have hrow : rowClique r≠ C.1 := fun h => hne (Subtype.ext h.symm)
        change (-1 : ℝ)^(C.1.card-3)*
          (if h : rowClique r=C.1 then starVector C.1 a (pairAtRow C.1 r h) else 0)=0
        rw [dite_eq_right hrow,mul_zero]
      · simp
    · have hterms : ∀ C : AnchorBlock a,
          ((-1 : ℝ)^(C.1.card-3) • blockCoordinates C.1 (starVector C.1 a)) r=0 := by
        intro C
        have hrow : rowClique r≠ C.1 := fun h => hr (h.symm ▸ C.2)
        change (-1 : ℝ)^(C.1.card-3)*
          (if h : rowClique r=C.1 then starVector C.1 a (pairAtRow C.1 r h) else 0)=0
        rw [dite_eq_right hrow,mul_zero]
      rw [sum_eq_zero (fun C _ => hterms C)]
      have hn : ¬(3≤(rowClique r).card ∧ (a=r.1.1.1 ∨ a=r.1.1.2)) := by
        rintro ⟨hc,ha⟩
        apply hr
        apply mem_anchorBlocks.mpr
        refine ⟨subset_univ _,?_,hc⟩
        rcases ha with h | h <;> simp [rowClique,h]
      exact ite_eq_right hn
  rw [thresholdStar_response_class,hcoord,map_sum]
  apply sum_congr rfl
  intro C hC
  rw [map_smul]
  rfl

theorem anchor_cancellation_decomposition (a : H) (C : AnchorBlock a)
    {k : ℕ} (hk : 1≤ k) (hkC : k≤ C.1.card.choose 2-1) :
    Nonempty (PureDecomposition C.1 (-anchorSignedClass a C) k) := by
  have hsize := (mem_anchorBlocks.mp C.2).2.2
  have ha := (mem_anchorBlocks.mp C.2).2.1
  rcases neg_one_pow_eq_or ℝ (C.1.card-3) with h | h
  · simpa only [anchorSignedClass,h,one_smul] using
      negative_star_interpolation C.1 hsize a ha hk hkC
  · simpa only [anchorSignedClass,h,neg_one_smul,neg_neg] using
      positive_star_interpolation C.1 hsize a ha hk hkC

/-- The whole single-threshold interval of Lemma 7.8. The upper endpoint is
written as the equivalent difference of complete response capacities. Every
ambient parameter is arbitrary, and the witness has an integral complement
in exactly `k` times the original graphical zonotope. -/
theorem threshold_book_interval {s k : ℕ} (hs : 3≤ s)
    (hklo : 2^(s-1)-s+1≤ k)
    (hkhi : k≤ cliqueCapacity s-cliqueCapacity (s-1)+1) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(k : ℝ) • graphicalZonotope (cliqueBook s k) := by
  classical
  let a : Fin s := ⟨0,by omega⟩
  let d : AnchorBlock a → ℕ := fun C => C.1.card.choose 2-1
  have hd : ∀ C,1≤ d C := by
    intro C
    have h := Nat.choose_le_choose 2 (mem_anchorBlocks.mp C.2).2.2
    norm_num [Nat.choose] at h
    change 1≤ C.1.card.choose 2-1
    omega
  have hcard : Fintype.card (AnchorBlock a)=2^(s-1)-s := by
    simpa only [AnchorBlock,Fintype.card_coe,card_univ,Fintype.card_fin] using
      anchorBlocks_card (univ : Finset (Fin s)) a (mem_univ a)
  have hsumd : (∑ C : AnchorBlock a,d C)=cliqueCapacity s-cliqueCapacity (s-1) := by
    change (∑ C : ↥(anchorBlocks (univ : Finset (Fin s)) a),(C.1.card.choose 2-1))=_
    rw [sum_coe_sort (anchorBlocks (univ : Finset (Fin s)) a)
      (fun C : Finset (Fin s) => C.card.choose 2-1)]
    simpa only [card_univ,Fintype.card_fin] using
      anchorBlocks_dimension_sum (univ : Finset (Fin s)) a (mem_univ a)
  have hkpos : 0< k := by omega
  obtain ⟨r,hr,hrsum⟩ := positive_sum_composition d hd (n:=k-1)
    (by rw [hcard]; omega) (by rw [hsumd]; omega)
  have hP : ∀ C : AnchorBlock a,Nonempty
      (PureDecomposition C.1 (-anchorSignedClass a C) (r C)) :=
    fun C => anchor_cancellation_decomposition a C (hr C).1 (hr C).2
  let P := fun C => Classical.choice (hP C)
  let F : (Σ C : AnchorBlock a,Fin (r C)) → SetFunction (Fin s) :=
    fun j => (P j.1).functions j.2
  have hind : LinearIndependent ℝ (fun j => responseClass (F j)) :=
    pureDecompositions_independent Subtype.val Subtype.val_injective
      (fun C => by have h := (mem_anchorBlocks.mp C.2).2.2; omega)
      (fun C => -anchorSignedClass a C) r P
  have hsum : responseClass (thresholdStar a)+∑ j,responseClass (F j)=0 := by
    rw [Fintype.sum_sigma]
    have hp : ∀ C : AnchorBlock a,(∑ j : Fin (r C),responseClass (F ⟨C,j⟩))=
        -anchorSignedClass a C := fun C => (P C).sum_eq
    simp_rw [hp]
    rw [sum_neg_distrib,← threshold_response_block_sum]
    exact add_neg_cancel _
  apply lattice_book_of_anchored_circuit (by omega) (thresholdStar a) F
    (thresholdStar_boolean a) (fun j => (P j.1).monotone_boolean j.2)
    (thresholdStar_essential (by simpa using hs) a)
    (fun j => ⟨a,(P j.1).essential j.2 a (mem_anchorBlocks.mp j.1.2).2.1⟩)
    hind hsum
  simp only [Fintype.card_sigma,Fintype.card_fin,hrsum]
  omega

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart187

section BundlePart188
/- Source: Papers/GraphicalZonotopes/OneBlockCircuit.lean -/










@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
namespace OneBlockCircuit
open Finset
open scoped BigOperators
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The columns used in the small-count construction: the indicator of a
proper set of pairs, followed by the complements of its individual pairs. -/
def column (A : Finset E) : Option ↥A → E → ℝ
  | none,e => if e∈A then 1 else 0
  | some a,e => if e=a.1 then 0 else 1

def response (A : Finset E) (t : Option ↥A → ℝ) (e : E) : ℝ :=
  ∑ j : Option ↥A,t j*column A j e

def tailSum (A : Finset E) (t : Option ↥A → ℝ) : ℝ :=
  ∑ a : ↥A,t (some a)

theorem response_outside (A : Finset E) (t : Option ↥A → ℝ)
    {e : E} (he : e∉A) : response A t e=tailSum A t := by
  rw [response,Fintype.sum_option]
  simp only [column,if_neg he,mul_zero,zero_add]
  apply sum_congr rfl
  intro a ha
  have hea : e≠ a.1:=fun h => he (h.symm ▸ a.2)
  simp only [if_neg hea,mul_one]

theorem response_at (A : Finset E) (t : Option ↥A → ℝ) (a : ↥A) :
    response A t a.1=t none+tailSum A t-t (some a) := by
  rw [response,Fintype.sum_option]
  simp only [column,if_pos a.2,mul_one]
  have hs : (∑ b : ↥A,t (some b)*(if a.1=b.1 then 0 else 1))=
      tailSum A t-t (some a) := by
    calc
      _=∑ b : ↥A,(t (some b)-(if a=b then t (some b) else 0)) := by
        apply sum_congr rfl
        intro b hb
        by_cases hab : a=b
        · subst b
          simp
        · have hv : a.1≠ b.1:=fun h => hab (Subtype.ext h)
          simp only [if_neg hv,if_neg hab,mul_one,sub_zero]
      _=tailSum A t-t (some a) := by
        rw [sum_sub_distrib]
        simp only [sum_ite_eq,mem_univ,ite_true,tailSum]
  rw [hs]
  ring

/-- A missing pair fixes the common block value. Comparing every selected
pair with it then forces every column scale to equal the first one. -/
theorem constant_response_iff (A : Finset E) (hA : ∃ e,e∉A)
    (t : Option ↥A → ℝ) :
    (∃ c : ℝ,∀ e,response A t e=c) ↔ ∃ a : ℝ,∀ j,t j=a := by
  constructor
  · rintro ⟨c,hc⟩
    obtain ⟨e₀,he₀⟩:=hA
    have hc₀ : c=tailSum A t:=(hc e₀).symm.trans (response_outside A t he₀)
    refine ⟨t none,?_⟩
    intro j
    cases j with
    | none => rfl
    | some a =>
      have ha:=hc a.1
      rw [response_at,hc₀] at ha
      linarith
  · rintro ⟨a,ha⟩
    refine ⟨tailSum A t,?_⟩
    intro e
    by_cases he : e∈A
    · have h:=response_at A t ⟨e,he⟩
      rw [ha none,ha (some ⟨e,he⟩)] at h
      linarith
    · exact response_outside A t he

theorem unit_response (A : Finset E) (e : E) :
    response A (fun _ => 1) e=(A.card : ℝ) := by
  have hs : tailSum A (fun _ => 1)=(A.card : ℝ) := by
    simp [tailSum]
  by_cases he : e∈A
  · rw [response_at A (fun _ => 1) ⟨e,he⟩,hs]
    ring
  · rw [response_outside A (fun _ => 1) he,hs]

def relationSpace (A : Finset E) : Submodule ℝ (Option ↥A → ℝ) where
  carrier:={t | ∃ c : ℝ,∀ e,response A t e=c}
  zero_mem':=by refine ⟨0,?_⟩; intro e; simp [response]
  add_mem':=by
    rintro t u ⟨c,hc⟩ ⟨d,hd⟩
    refine ⟨c+d,?_⟩
    intro e
    simp only [response,Pi.add_apply,add_mul,sum_add_distrib]
    exact congrArg₂ (·+·) (hc e) (hd e)
  smul_mem':=by
    rintro a t ⟨c,hc⟩
    refine ⟨a*c,?_⟩
    intro e
    simp only [response,Pi.smul_apply,smul_eq_mul,mul_assoc,← mul_sum]
    exact congrArg (a*·) (hc e)

theorem relationSpace_eq_span (A : Finset E) (hA : ∃ e,e∉A) :
    relationSpace A=Submodule.span ℝ {(fun _ : Option ↥A => (1 : ℝ))} := by
  ext t
  change (∃ c : ℝ,∀ e,response A t e=c) ↔ _
  rw [constant_response_iff A hA,Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c,hc⟩
    refine ⟨c,?_⟩
    funext j
    simp only [Pi.smul_apply,smul_eq_mul,mul_one]
    exact (hc j).symm
  · rintro ⟨c,hc⟩
    refine ⟨c,?_⟩
    intro j
    have h:=congrFun hc j
    simpa only [Pi.smul_apply,smul_eq_mul,mul_one] using h.symm

end OneBlockCircuit
end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart188

section BundlePart189
/- Source: Papers/GraphicalZonotopes/SmallCountModules.lean -/







@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
namespace SmallCount
open Finset
open scoped BigOperators Classical
variable {H : Type*} [Fintype H] [LinearOrder H]

def crossingPairs (blocks : Finset (Finset H)) : Finset (OrientedEdge (⊤ : SimpleGraph H)) :=
  univ.filter (fun e => Crosses blocks e.1.1 e.1.2)

@[simp] theorem mem_crossingPairs (blocks : Finset (Finset H))
    (e : OrientedEdge (⊤ : SimpleGraph H)) :
    e∈crossingPairs blocks ↔ Crosses blocks e.1.1 e.1.2 := by
  simp only [crossingPairs,mem_filter,mem_univ,true_and]

abbrev Branch (blocks : Finset (Finset H)) := Option ↥(crossingPairs blocks)

/-- The first outer vertex carries the complete-multipartite response;
every selected pair has its own negative pure-coordinate outer module. -/
def modules (blocks : Finset (Finset H)) : Branch blocks → SetFunction H
  | none => complementModule univ blocks
  | some e => negativePairModule univ e.1.1.1 e.1.1.2

theorem modules_boolean {blocks : Finset (Finset H)}
    (hb : ComplementFamily (univ : Finset H) blocks) (hs : 3≤ Fintype.card H) :
    ∀ j,IsMonotoneBoolean (modules blocks j) := by
  intro j
  cases j with
  | none => exact hb.module_boolean
  | some e =>
    exact (negativePairBlocks_family univ (by simpa using hs)
      (mem_univ _) (mem_univ _) (ne_of_lt e.1.2.1)).module_boolean

theorem modules_essential {blocks : Finset (Finset H)}
    (hb : ComplementFamily (univ : Finset H) blocks) (hs : 3≤ Fintype.card H) :
    ∀ j a,Essential (modules blocks j) a := by
  intro j a
  cases j with
  | none => exact hb.essential (mem_univ a)
  | some e =>
    exact negativePairModule_essential univ (by simpa using hs)
      (mem_univ _) (mem_univ _) (ne_of_lt e.1.2.1) (mem_univ a)

theorem modules_coefficients {blocks : Finset (Finset H)}
    (hb : ComplementFamily (univ : Finset H) blocks) (hs : 3≤ Fintype.card H)
    (j : Branch blocks) :
    rowLowerEquiv.symm (responseVector (modules blocks j))=
      fullBlock (OneBlockCircuit.column (crossingPairs blocks) j) := by
  cases j with
  | none =>
    rw [modules,complementModule_response_coefficients hb]
    funext r
    by_cases hc : rowClique r=univ <;>
      by_cases he : Crosses blocks r.1.1.1 r.1.1.2 <;>
        simp only [fullBlock,OneBlockCircuit.column,mem_crossingPairs,hc,he,
          and_self,true_and,false_and,ite_true,ite_false]
  | some e =>
    rw [modules,negativePairModule_coefficients univ (by simpa using hs)
      (mem_univ _) (mem_univ _) e.1.2.1]
    funext r
    have he : r.1=e.1 ↔ r.1.1.1=e.1.1.1 ∧ r.1.1.2=e.1.1.2 := by
      constructor
      · intro h
        exact ⟨congrArg (fun q : OrientedEdge (⊤ : SimpleGraph H) => q.1.1) h,
          congrArg (fun q : OrientedEdge (⊤ : SimpleGraph H) => q.1.2) h⟩
      · rintro ⟨h₁,h₂⟩
        exact Subtype.ext (Prod.ext h₁ h₂)
    simp only [← he]
    by_cases hc : rowClique r=univ <;> by_cases hp : r.1=e.1 <;>
      simp only [fullBlock,OneBlockCircuit.column,hc,hp,
        true_and,false_and,ite_true,ite_false,not_true_eq_false,not_false_eq_true]

theorem weighted_coefficients {blocks : Finset (Finset H)}
    (hb : ComplementFamily (univ : Finset H) blocks) (hs : 3≤ Fintype.card H)
    (t : Branch blocks → ℝ) :
    rowLowerEquiv.symm (weightedResponse (modules blocks) t)=
      fullBlock (OneBlockCircuit.response (crossingPairs blocks) t) := by
  rw [rowLower_symm_weightedResponse]
  simp_rw [modules_coefficients hb hs]
  funext r
  rw [Finset.sum_apply]
  by_cases hc : rowClique r=univ
  · simp only [Pi.smul_apply,smul_eq_mul,fullBlock,if_pos hc,
      OneBlockCircuit.response]
  · simp only [Pi.smul_apply,smul_eq_mul,fullBlock,if_neg hc,mul_zero,sum_const_zero]

/-- All real relations, with no positivity assumption, are exactly the
constant vectors. The unused pair is part of the actual full hub block. -/
theorem integrable_iff_constant {blocks : Finset (Finset H)}
    (hb : ComplementFamily (univ : Finset H) blocks) (hs : 3≤ Fintype.card H)
    (hproper : ∃ e : OrientedEdge (⊤ : SimpleGraph H),e∉crossingPairs blocks)
    (t : Branch blocks → ℝ) :
    (∃ z : SetFunction H,TranslationNormalized z ∧ Compatible z (modules blocks) t) ↔
      ∃ c : ℝ,∀ j,t j=c := by
  letI : Nonempty (OrientedEdge (⊤ : SimpleGraph H)):=⟨hproper.choose⟩
  rw [integrable_iff_blockConstant,weighted_coefficients hb hs,
    fullBlock_constant_iff,OneBlockCircuit.constant_response_iff _ hproper]

theorem unit_integrable {blocks : Finset (Finset H)}
    (hb : ComplementFamily (univ : Finset H) blocks) (hs : 3≤ Fintype.card H)
    (hproper : ∃ e : OrientedEdge (⊤ : SimpleGraph H),e∉crossingPairs blocks) :
    ∃ z : SetFunction H,TranslationNormalized z ∧
      Compatible z (modules blocks) (fun _ => 1) :=
  (integrable_iff_constant hb hs hproper _).mpr ⟨1,fun _ => rfl⟩

theorem unit_unique {blocks : Finset (Finset H)}
    (hb : ComplementFamily (univ : Finset H) blocks) (hs : 3≤ Fintype.card H)
    (hproper : ∃ e : OrientedEdge (⊤ : SimpleGraph H),e∉crossingPairs blocks) :
    UniqueIntegrableRelation (modules blocks) (fun _ => 1) := by
  intro t ht
  obtain ⟨c,hc⟩:=(integrable_iff_constant hb hs hproper t).mp ht
  refine ⟨c,?_⟩
  funext j
  simpa only [Pi.smul_apply,smul_eq_mul,mul_one] using hc j

theorem unit_integral_lift {blocks : Finset (Finset H)}
    (hb : ComplementFamily (univ : Finset H) blocks) (hs : 3≤ Fintype.card H)
    (hproper : ∃ e : OrientedEdge (⊤ : SimpleGraph H),e∉crossingPairs blocks) :
    ∃ z : SetFunction H,TranslationNormalized z ∧ IntegerValued z ∧
      Compatible z (modules blocks) (fun _ => 1) := by
  have hrel : (fun _ : Branch blocks => (1 : ℝ))∈
      LinearMap.ker (quotientRelation (modules blocks)) :=
    (mem_quotientRelation_ker_iff _ _).mpr (unit_integrable hb hs hproper)
  simpa only [Int.cast_one] using integral_compatible_lift
    (modules blocks) (modules_boolean hb hs) (fun _ => (1 : ℤ))
    (by simpa only [Int.cast_one] using hrel)

end SmallCount
end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart189

section BundlePart190
/- Source: Papers/GraphicalZonotopes/UnitBookGeometry.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise

/-- Actual finite-dimensional lattice geometry for a circuit of unit-weight
Boolean columns. The normalized central lift is derived integrally from the
actual elemental response equations. -/
theorem lattice_book_of_unit_modules {s k : ℕ} (hs : 0< s) (hk : 0< k)
    (F : Fin k → SetFunction (Fin s)) (hF : ∀ i,IsMonotoneBoolean (F i))
    (hess : ∀ i a,Essential (F i) a)
    (hrel : ∃ z : SetFunction (Fin s),TranslationNormalized z ∧ Compatible z F (fun _ => 1))
    (huniq : UniqueIntegrableRelation F (fun _ => 1)) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(k : ℝ) • graphicalZonotope (cliqueBook s k) := by
  letI : Nonempty (Fin s):=⟨⟨0,hs⟩⟩
  letI : Nonempty (Fin k):=⟨⟨0,hk⟩⟩
  have hkrel : (fun _ : Fin k => (1 : ℝ))∈LinearMap.ker (quotientRelation F):=
    (mem_quotientRelation_ker_iff F _).mpr hrel
  obtain ⟨z,hzn,hzi,hcInt⟩:=integral_compatible_lift F hF (fun _ => (1 : ℤ))
    (by simpa only [Int.cast_one] using hkrel)
  have hc : Compatible z F (fun _ => 1):=by simpa only [Int.cast_one] using hcInt
  let f:=assembled z F (fun _ => 1)
  have hn : TranslationNormalized f:=assembled_normalized hzn F hF (fun _ => 1)
  have hi : IntegerValued f := by
    simpa only [Int.cast_one] using assembled_integerValued hzi F hF (fun _ => (1 : ℤ))
  have he : ExtremeSupermodular f:=positive_circuit_extreme hzn hF
    (fun _ => zero_le_one) ⟨⟨0,hk⟩,one_ne_zero⟩ hc huniq
  have hd : FullDimension (basePolytope f):=assembled_fullDimension hzn hF
    (fun _ => zero_lt_one) hc (essentialSpokeGraph_connected F hess)
  obtain ⟨hl,R,hR,hnR,hQR⟩:=assembled_lattice_complement hzn hzi hF
    (fun _ => (1 : ℤ)) (fun _ => zero_le_one) hcInt
  refine ⟨f,hn,hi,he,assembled_graphical z F (fun _ => 1),hd,
    he.minkowskiIndecomposable,?_,R,hR,hnR,?_⟩
  · simpa only [Int.cast_one] using hl
  · simpa only [Int.cast_one,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using hQR

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart190

section BundlePart191
/- Source: Papers/GraphicalZonotopes/SmallCountGeometry.lean -/






@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
namespace SmallCount
open Finset
open scoped BigOperators Pointwise

/-- The complete geometric construction associated with a proper nonempty
complete-multipartite pair pattern. The finite-type transport labels exactly
one outer vertex per Boolean column; it does not change the ambient graph. -/
theorem lattice_book_of_complement_family {s k : ℕ} (hs : 3≤ s)
    (blocks : Finset (Finset (Fin s)))
    (hb : ComplementFamily (univ : Finset (Fin s)) blocks)
    (hproper : ∃ e : OrientedEdge (⊤ : SimpleGraph (Fin s)),e∉crossingPairs blocks)
    (hcard : (crossingPairs blocks).card+1=k) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(k : ℝ) • graphicalZonotope (cliqueBook s k) := by
  have hsf : 3≤ Fintype.card (Fin s):=by simpa using hs
  have hk : 0< k:=by omega
  letI : Nonempty (Fin s):=⟨⟨0,by omega⟩⟩
  letI : Nonempty (Fin k):=⟨⟨0,hk⟩⟩
  have hJ : Fintype.card (Branch blocks)=k := by
    simpa only [Branch,Fintype.card_option,Fintype.card_coe] using hcard
  let e : Fin k≃Branch blocks:=
    (finCongr hJ.symm).trans (Fintype.equivFin (Branch blocks)).symm
  let F : Fin k → SetFunction (Fin s):=fun i => modules blocks (e i)
  have hF : ∀ i,IsMonotoneBoolean (F i):=fun i => modules_boolean hb hsf (e i)
  have hess : ∀ i a,Essential (F i) a:=fun i a => modules_essential hb hsf (e i) a
  obtain ⟨z,hzn,hzc⟩:=unit_integrable hb hsf hproper
  have hc : Compatible z F (fun _ => 1) := by
    apply (compatible_reindex e z (modules blocks) (fun _ => 1)).mpr
    exact hzc
  have huniq : UniqueIntegrableRelation F (fun _ => 1) := by
    intro t ht
    obtain ⟨u,hun,huc⟩:=ht
    have hold : Compatible u (modules blocks) (fun j => t (e.symm j)) :=
      (compatible_reindex e u (modules blocks) t).mp huc
    obtain ⟨c,hc⟩:=unit_unique hb hsf hproper (fun j => t (e.symm j)) ⟨u,hun,hold⟩
    refine ⟨c,?_⟩
    funext i
    simpa only [e.symm_apply_apply,Pi.smul_apply,smul_eq_mul,mul_one] using congrFun hc (e i)
  exact lattice_book_of_unit_modules (by omega) hk F hF hess ⟨z,hzn,hc⟩ huniq

end SmallCount
end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart191

section BundlePart192
/- Source: Papers/GraphicalZonotopes/MultipartitePairCounting.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
namespace SmallCount
open Finset
open scoped BigOperators Classical
variable {H : Type*} [Fintype H] [LinearOrder H]

def blockUnion (blocks : Finset (Finset H)) : Finset H:=blocks.biUnion id

@[simp] theorem mem_blockUnion (blocks : Finset (Finset H)) (x : H) :
    x∈blockUnion blocks ↔ ∃ B∈blocks,x∈B := by
  simp only [blockUnion,mem_biUnion,id_eq]

def orderedPairs (U : Finset H) : Finset (H×H):=
  (U×ˢU).filter (fun p => p.1< p.2)

@[simp] theorem mem_orderedPairs (U : Finset H) (p : H×H) :
    p∈orderedPairs U ↔ p.1∈U ∧ p.2∈U ∧ p.1< p.2 := by
  simp only [orderedPairs,mem_filter,mem_product,and_assoc]

theorem orderedPairs_card (U : Finset H) :
    (orderedPairs U).card=U.card.choose 2 := card_product_filter_lt

def completePairEquiv : OrientedEdge (⊤ : SimpleGraph H)≃↥(orderedPairs (univ : Finset H)) where
  toFun e:=⟨e.1,(mem_orderedPairs _ _).mpr ⟨mem_univ _,mem_univ _,e.2.1⟩⟩
  invFun p:=⟨p.1,((mem_orderedPairs _ _).mp p.2).2.2,
    (SimpleGraph.top_adj _ _).mpr (ne_of_lt ((mem_orderedPairs _ _).mp p.2).2.2)⟩
  left_inv _:=rfl
  right_inv _:=rfl

theorem completePair_card :
    Fintype.card (OrientedEdge (⊤ : SimpleGraph H))=(Fintype.card H).choose 2 := by
  rw [Fintype.card_congr completePairEquiv,Fintype.card_coe,orderedPairs_card,card_univ]

def crossingPairValues (blocks : Finset (Finset H)) : Finset (H×H):=
  (orderedPairs (blockUnion blocks)).filter (fun p => Crosses blocks p.1 p.2)

@[simp] theorem mem_crossingPairValues (blocks : Finset (Finset H)) (p : H×H) :
    p∈crossingPairValues blocks ↔ p∈orderedPairs (blockUnion blocks) ∧
      Crosses blocks p.1 p.2 := by
  simp only [crossingPairValues,mem_filter]

theorem crossingPairs_card_values (blocks : Finset (Finset H)) :
    (crossingPairs blocks).card=(crossingPairValues blocks).card := by
  apply card_bij (fun e _ => e.1)
  · intro e he
    have hcross:=(mem_crossingPairs blocks e).mp he
    obtain ⟨A,hA,B,hB,hAB,hu,hv⟩:=hcross
    exact (mem_crossingPairValues blocks _).mpr ⟨(mem_orderedPairs _ _).mpr
      ⟨(mem_blockUnion blocks _).mpr ⟨A,hA,hu⟩,
        (mem_blockUnion blocks _).mpr ⟨B,hB,hv⟩,e.2.1⟩,
      ⟨A,hA,B,hB,hAB,hu,hv⟩⟩
  · intro e he f hf hef
    exact Subtype.ext hef
  · intro p hp
    have hp' := (mem_crossingPairValues blocks p).mp hp
    have ht:=(mem_orderedPairs _ _).mp hp'.1
    let e : OrientedEdge (⊤ : SimpleGraph H):=
      ⟨p,ht.2.2,(SimpleGraph.top_adj _ _).mpr (ne_of_lt ht.2.2)⟩
    exact ⟨e,(mem_crossingPairs blocks e).mpr hp'.2,rfl⟩

theorem orderedPairs_partition (blocks : Finset (Finset H)) :
    orderedPairs (blockUnion blocks)=crossingPairValues blocks∪blocks.biUnion orderedPairs := by
  ext p
  constructor
  · intro hp
    obtain ⟨hu,hv,hlt⟩:=(mem_orderedPairs _ _).mp hp
    obtain ⟨A,hA,huA⟩:=(mem_blockUnion blocks _).mp hu
    obtain ⟨B,hB,hvB⟩:=(mem_blockUnion blocks _).mp hv
    by_cases hAB : A=B
    · subst B
      exact mem_union_right _ (mem_biUnion.mpr ⟨A,hA,
        (mem_orderedPairs _ _).mpr ⟨huA,hvB,hlt⟩⟩)
    · exact mem_union_left _ ((mem_crossingPairValues blocks p).mpr ⟨hp,⟨A,hA,B,hB,hAB,huA,hvB⟩⟩)
  · intro hp
    rcases mem_union.mp hp with hc | hi
    · exact ((mem_crossingPairValues blocks p).mp hc).1
    · obtain ⟨A,hA,hpA⟩:=mem_biUnion.mp hi
      obtain ⟨hu,hv,hlt⟩:=(mem_orderedPairs _ _).mp hpA
      exact (mem_orderedPairs _ _).mpr
        ⟨(mem_blockUnion blocks _).mpr ⟨A,hA,hu⟩,
          (mem_blockUnion blocks _).mpr ⟨A,hA,hv⟩,hlt⟩

theorem crossing_internal_disjoint (blocks : Finset (Finset H))
    (hd : ∀ A∈blocks,∀ B∈blocks,A≠ B → Disjoint A B) :
    Disjoint (crossingPairValues blocks) (blocks.biUnion orderedPairs) := by
  apply disjoint_left.mpr
  intro p hc hi
  obtain ⟨A,hA,B,hB,hAB,huA,hvB⟩:=((mem_crossingPairValues blocks p).mp hc).2
  obtain ⟨C,hC,hpC⟩:=mem_biUnion.mp hi
  obtain ⟨huC,hvC,_⟩:=(mem_orderedPairs _ _).mp hpC
  have hAC : A=C := by
    by_contra hn
    exact (disjoint_left.mp (hd A hA C hC hn)) huA huC
  have hBC : B=C := by
    by_contra hn
    exact (disjoint_left.mp (hd B hB C hC hn)) hvB hvC
  exact hAB (hAC.trans hBC.symm)

theorem internalPairs_pairwiseDisjoint (blocks : Finset (Finset H))
    (hd : ∀ A∈blocks,∀ B∈blocks,A≠ B → Disjoint A B) :
    (blocks : Set (Finset H)).PairwiseDisjoint orderedPairs := by
  intro A hA B hB hAB
  apply disjoint_left.mpr
  intro p hpA hpB
  exact (disjoint_left.mp (hd A hA B hB hAB))
    ((mem_orderedPairs A p).mp hpA).1 ((mem_orderedPairs B p).mp hpB).1

/-- This count is for the literal ordered representatives of the unordered
crossing pairs. Every pair of active vertices is either crossing or belongs
to one uniquely determined part. -/
theorem crossingPairs_card_formula (blocks : Finset (Finset H))
    (hd : ∀ A∈blocks,∀ B∈blocks,A≠ B → Disjoint A B) :
    (crossingPairs blocks).card=(blockUnion blocks).card.choose 2-
      ∑ B∈blocks,B.card.choose 2 := by
  have he:=congrArg Finset.card (orderedPairs_partition blocks)
  rw [orderedPairs_card,card_union_of_disjoint (crossing_internal_disjoint blocks hd),
    card_biUnion (internalPairs_pairwiseDisjoint blocks hd)] at he
  simp only [orderedPairs_card] at he
  rw [crossingPairs_card_values]
  omega

theorem crossingPairs_nonempty_gives_two (blocks : Finset (Finset H))
    (hp : (crossingPairs blocks).Nonempty) : 2≤ blocks.card := by
  obtain ⟨e,he⟩:=hp
  obtain ⟨A,hA,B,hB,hAB,_,_⟩:=(mem_crossingPairs blocks e).mp he
  exact (one_lt_card.mpr ⟨A,hA,B,hB,hAB⟩)

end SmallCount
end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart192

section BundlePart193
/- Source: Papers/GraphicalZonotopes/MultipartiteSizes.lean -/







@[expose] public section
namespace GraphicalZonotopes
namespace BooleanModule
namespace SmallCount

def crossCount (sizes : List ℕ) : ℕ :=
  sizes.sum.choose 2-(sizes.map (fun a => a.choose 2)).sum

/-- Every pair count up to `s.choose 2` is realized by positive multipartite
block sizes using at most `s` vertices. The unused vertices are isolated in
the response pattern, but will remain essential in its Boolean module. -/
theorem exists_multipartite_sizes (s m : ℕ) (hm : m≤ s.choose 2) :
    ∃ sizes : List ℕ,(∀ a∈sizes,0< a) ∧ sizes.sum≤ s ∧ crossCount sizes=m := by
  induction s with
  | zero =>
    have hm0 : m=0:=by simpa using hm
    subst m
    exact ⟨[],by simp,by simp,by simp [crossCount]⟩
  | succ s ih =>
    by_cases hsmall : m≤ s.choose 2
    · obtain ⟨sizes,hpos,hsize,hcount⟩:=ih hsmall
      exact ⟨sizes,hpos,hsize.trans (Nat.le_succ s),hcount⟩
    · have hchoose : (s+1).choose 2=s.choose 2+s := by
        calc
          (s+1).choose 2=s.choose 1+s.choose 2 := Nat.choose_succ_succ' s 1
          _=s.choose 2+s := by rw [Nat.choose_one_right,Nat.add_comm]
      let j:=(s+1).choose 2-m
      let q:=j/3
      let r:=j%3
      have hdecomp : j=3*q+r:=by
        dsimp only [q,r]
        exact (Nat.div_add_mod j 3).symm
      have hr : r<3:=Nat.mod_lt _ (by decide)
      have hj : j< s := by
        dsimp only [j]
        rw [hchoose]
        omega
      have hused : 3*q+2*r≤ s+1 := by omega
      let a:=s+1-(3*q+2*r)
      let sizes : List ℕ:=List.replicate q 3++List.replicate r 2++List.replicate a 1
      have hsum : sizes.sum=s+1 := by
        simp only [sizes,List.sum_append,List.sum_replicate,nsmul_eq_mul,Nat.cast_id,Nat.mul_one]
        dsimp only [a]
        omega
      have hinside : (sizes.map (fun n => n.choose 2)).sum=j := by
        simpa only [sizes,List.map_append,List.map_replicate,List.sum_append,
          List.sum_replicate,nsmul_eq_mul,
          show (3 : ℕ).choose 2=3 from by decide,
          show (2 : ℕ).choose 2=1 from by decide,
          show (1 : ℕ).choose 2=0 from by decide,
          Nat.cast_id,Nat.mul_one,Nat.mul_zero,Nat.one_mul,Nat.zero_mul,Nat.add_zero,Nat.mul_comm] using hdecomp.symm
      refine ⟨sizes,?_,by omega,?_⟩
      · intro b hb
        simp only [sizes,List.mem_append,List.mem_replicate] at hb
        rcases hb with (⟨_,rfl⟩ | ⟨_,rfl⟩) | ⟨_,rfl⟩ <;> omega
      · rw [crossCount,hsum,hinside]
        dsimp only [j]
        omega

end SmallCount
end BooleanModule
end GraphicalZonotopes

end
end BundlePart193

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

