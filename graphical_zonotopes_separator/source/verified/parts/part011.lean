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

public import verified.parts.part010
import all verified.parts.part010

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section BundlePart145
/- Source: Papers/GraphicalZonotopes/BooleanResponseCoordinates.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset PowersetTransform
open scoped BigOperators
variable {H J : Type*} [Fintype H] [LinearOrder H] [Fintype J] [DecidableEq J]

/-- The multilinear expansion is the full powerset zeta transform separately
on each genuine pair row. This is an invertible change of coordinates. -/
def rowLowerEquiv : (HubResponseRow H → ℝ) ≃ₗ[ℝ] (HubResponseRow H → ℝ) where
  toFun y r := lowerEquiv (commonNeighbors (⊤ : SimpleGraph H) r.1.1.1 r.1.1.2)
    (fun T => y ⟨r.1,T⟩) r.2
  invFun y r := (lowerEquiv (commonNeighbors (⊤ : SimpleGraph H) r.1.1.1 r.1.1.2)).symm
    (fun T => y ⟨r.1,T⟩) r.2
  left_inv y := by
    funext r
    rcases r with ⟨e,S⟩
    exact congrFun ((lowerEquiv (commonNeighbors (⊤ : SimpleGraph H) e.1.1 e.1.2)).symm_apply_apply
      (fun T => y ⟨e,T⟩)) S
  right_inv y := by
    funext r
    rcases r with ⟨e,S⟩
    exact congrFun ((lowerEquiv (commonNeighbors (⊤ : SimpleGraph H) e.1.1 e.1.2)).apply_symm_apply
      (fun T => y ⟨e,T⟩)) S
  map_add' y z := by
    funext r
    exact congrFun ((lowerEquiv (commonNeighbors (⊤ : SimpleGraph H) r.1.1.1 r.1.1.2)).map_add
      (fun T => y ⟨r.1,T⟩) (fun T => z ⟨r.1,T⟩)) r.2
  map_smul' c y := by
    funext r
    exact congrFun ((lowerEquiv (commonNeighbors (⊤ : SimpleGraph H) r.1.1.1 r.1.1.2)).map_smul c
      (fun T => y ⟨r.1,T⟩)) r.2

def rowClique (r : HubResponseRow H) : Finset H:=
  insert r.1.1.1 (insert r.1.1.2 r.2.1)

theorem rowClique_card (r : HubResponseRow H) : 2≤(rowClique r).card := by
  have hsub : ({r.1.1.1,r.1.1.2} : Finset H)⊆rowClique r := by
    simp only [rowClique,insert_subset_iff,singleton_subset_iff,mem_insert,true_or,or_true,and_self]
  have hc:=card_le_card hsub
  rwa [card_pair (ne_of_lt r.1.2.1)] at hc

def rowCliqueIndex (r : HubResponseRow H) : CliqueIndex (⊤ : SimpleGraph H) :=
  ⟨rowClique r,rowClique_card r,by
    intro u hu v hv huv
    exact (SimpleGraph.top_adj u v).mpr huv⟩

theorem rowCliqueIndex_surjective : Function.Surjective (rowCliqueIndex (H:=H)) := by
  intro C
  have hpair : ∀ u v,u∈C.1 → v∈C.1 → u< v → ∃ r : HubResponseRow H,rowCliqueIndex r=C := by
    intro u v huC hvC huv
    let T:=(C.1.erase u).erase v
    have hT : T⊆commonNeighbors (⊤ : SimpleGraph H) u v := by
      intro a ha
      have hne:=mem_erase.mp ha
      have hne':=mem_erase.mp hne.2
      exact (mem_commonNeighbors _ _ _ _).mpr
        ⟨(SimpleGraph.top_adj _ _).mpr hne'.1.symm,(SimpleGraph.top_adj _ _).mpr hne.1.symm⟩
    let e : OrientedEdge (⊤ : SimpleGraph H):=
      ⟨(u,v),huv,(SimpleGraph.top_adj u v).mpr (ne_of_lt huv)⟩
    let r : HubResponseRow H:=⟨e,⟨T,mem_powerset.mpr hT⟩⟩
    refine ⟨r,Subtype.ext ?_⟩
    change insert u (insert v ((C.1.erase u).erase v))=C.1
    ext a
    by_cases hau : a=u
    · subst a
      simp [huC]
    · by_cases hav : a=v
      · subst a
        simp [hvC]
      · simp [hau,hav]
  have hcard : 2≤ C.1.card := C.2.1
  obtain ⟨u,hu,v,hv,huv⟩:=one_lt_card.mp (show 1< C.1.card by omega)
  rcases lt_or_gt_of_ne huv with hlt | hgt
  · exact hpair u v hu hv hlt
  · exact hpair v u hv hu hgt

/-- A central Möbius coefficient is repeated once for each pair contained in
its clique. This map includes the pair blocks as well as all higher blocks. -/
def repeatCoefficients : (CliqueIndex (⊤ : SimpleGraph H) → ℝ) →ₗ[ℝ]
    (HubResponseRow H → ℝ) where
  toFun c r := c (rowCliqueIndex r)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coefficient_at_row (c : CliqueIndex (⊤ : SimpleGraph H) → ℝ)
    (r : HubResponseRow H) :
    coefficientsFromCoordinates ⊤ c (rowClique r)=c (rowCliqueIndex r) := by
  unfold coefficientsFromCoordinates
  split_ifs with h
  · rfl
  · exact (h (rowCliqueIndex r).2).elim

/-- This is the actual central elemental map in multilinear response
coordinates, not an independently postulated compatibility condition. -/
theorem rowLower_repeatCoefficients (c : CliqueIndex (⊤ : SimpleGraph H) → ℝ) :
    rowLowerEquiv (repeatCoefficients c)=centralCoefficientSlack c := by
  funext r
  let B:=commonNeighbors (⊤ : SimpleGraph H) r.1.1.1 r.1.1.2
  let y:=coefficientsFromCoordinates (⊤ : SimpleGraph H) c
  have hu : r.1.1.1∉r.2.1 := by
    intro h
    exact not_mem_commonNeighbors_left ⊤ _ _ ((mem_powerset.mp r.2.2) h)
  have hv : r.1.1.2∉r.2.1 := by
    intro h
    exact not_mem_commonNeighbors_right ⊤ _ _ ((mem_powerset.mp r.2.2) h)
  change lowerSum B (fun T => c (rowCliqueIndex ⟨r.1,T⟩)) r.2=
    delta (zeta y) r.1.1.1 r.1.1.2 r.2.1
  calc
    _=lowerSum B (fun T => y (insert r.1.1.1 (insert r.1.1.2 T.1))) r.2 := by
      have he : (fun T : SubsetIndex B => c (rowCliqueIndex ⟨r.1,T⟩))=
          (fun T : SubsetIndex B => y (insert r.1.1.1 (insert r.1.1.2 T.1))) := by
        funext T
        exact (coefficient_at_row c ⟨r.1,T⟩).symm
      rw [he]
    _=∑ T∈r.2.1.powerset,y (insert r.1.1.1 (insert r.1.1.2 T)) :=
      lowerSum_restriction B (fun T => y (insert r.1.1.1 (insert r.1.1.2 T))) r.2
    _=_ := (delta_zeta_reduced (ne_of_lt r.1.2.1) hu hv y).symm

/-- Being in the diagonal line of each clique block means exactly that all
copies of the same central Möbius coefficient agree. -/
def BlockConstant (x : HubResponseRow H → ℝ) : Prop :=
  ∀ r t,rowCliqueIndex r=rowCliqueIndex t → x r=x t

theorem blockConstant_iff_range_repeatCoefficients (x : HubResponseRow H → ℝ) :
    BlockConstant x ↔ x∈LinearMap.range (repeatCoefficients (H:=H)) := by
  constructor
  · intro hx
    choose pick hpick using (rowCliqueIndex_surjective (H:=H))
    refine ⟨fun C => x (pick C),?_⟩
    funext r
    exact hx (pick (rowCliqueIndex r)) r (hpick (rowCliqueIndex r))
  · rintro ⟨c,rfl⟩ r t he
    exact congrArg c he

/-- Integrability is equivalent to independent within-block agreement after
the invertible pairwise Möbius expansion. Consequently there are no hidden
relations between different clique blocks. -/
theorem central_range_iff_blockConstant (x : HubResponseRow H → ℝ) :
    x∈LinearMap.range (centralCoefficientSlack (H:=H)) ↔
      BlockConstant (rowLowerEquiv.symm x) := by
  rw [blockConstant_iff_range_repeatCoefficients]
  constructor
  · rintro ⟨c,rfl⟩
    refine ⟨c,?_⟩
    rw [← rowLower_repeatCoefficients,rowLowerEquiv.symm_apply_apply]
  · rintro ⟨c,hc⟩
    refine ⟨c,?_⟩
    rw [← rowLower_repeatCoefficients,hc,rowLowerEquiv.apply_symm_apply]

theorem integrable_iff_blockConstant (F : J → SetFunction H) (w : J → ℝ) :
    (∃ z : SetFunction H,TranslationNormalized z ∧ Compatible z F w) ↔
      BlockConstant (rowLowerEquiv.symm (weightedResponse F w)) := by
  rw [← mem_quotientRelation_ker_iff]
  change (LinearMap.range (centralCoefficientSlack (H:=H))).mkQ
    (weightedResponse F w)=0 ↔ _
  rw [← LinearMap.mem_ker,Submodule.ker_mkQ,central_range_iff_blockConstant]

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart145

section BundlePart146
/- Source: Papers/GraphicalZonotopes/PureBooleanResponses.lean -/





@[expose] public section
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace BooleanModule
open Finset PowersetTransform
open scoped BigOperators
variable {H : Type*} [Fintype H] [LinearOrder H]

theorem rowLower_raw_coefficients (y : SetFunction H) :
    rowLowerEquiv (fun r => y (rowClique r))=
      (fun r : HubResponseRow H => delta (zeta y) r.1.1.1 r.1.1.2 r.2.1) := by
  funext r
  have hu : r.1.1.1∉r.2.1 := by
    intro hm
    exact not_mem_commonNeighbors_left ⊤ _ _ ((mem_powerset.mp r.2.2) hm)
  have hv : r.1.1.2∉r.2.1 := by
    intro hm
    exact not_mem_commonNeighbors_right ⊤ _ _ ((mem_powerset.mp r.2.2) hm)
  change lowerSum (commonNeighbors (⊤ : SimpleGraph H) r.1.1.1 r.1.1.2)
    (fun T => y (insert r.1.1.1 (insert r.1.1.2 T.1))) r.2=_
  rw [lowerSum_restriction _ (fun T : Finset H => y (insert r.1.1.1 (insert r.1.1.2 T))) r.2]
  exact (delta_zeta_reduced (ne_of_lt r.1.2.1) hu hv y).symm

theorem rowLower_edge_mul (q : OrientedEdge (⊤ : SimpleGraph H) → ℝ)
    (y : HubResponseRow H → ℝ) :
    rowLowerEquiv (fun r => q r.1*y r)=fun r => q r.1*rowLowerEquiv y r := by
  funext r
  exact congrFun ((lowerEquiv (commonNeighbors (⊤ : SimpleGraph H) r.1.1.1 r.1.1.2)).map_smul
    (q r.1) (fun T => y ⟨r.1,T⟩)) r.2

theorem zeta_delta_coordinate (C : Finset H) :
    zeta (fun D : Finset H => if D=C then 1 else 0)=setMonomial C := by
  funext A
  by_cases hC : C⊆A <;> simp [zeta,setMonomial,hC]

/-- The raw response coefficient array of a disjoint-minterm module has one
clique block and the exact complete-multipartite pair indicator in that block. -/
theorem complementModule_response_coefficients {C : Finset H} {blocks : Finset (Finset H)}
    (h : ComplementFamily C blocks) :
    rowLowerEquiv.symm (responseVector (complementModule C blocks))=
      fun r : HubResponseRow H =>
        if rowClique r=C ∧ Crosses blocks r.1.1.1 r.1.1.2 then 1 else 0 := by
  classical
  let q : OrientedEdge (⊤ : SimpleGraph H) → ℝ:=
    fun e => if Crosses blocks e.1.1 e.1.2 then 1 else 0
  let y : HubResponseRow H → ℝ:=fun r => if rowClique r=C then 1 else 0
  have he : (fun r : HubResponseRow H =>
      if rowClique r=C ∧ Crosses blocks r.1.1.1 r.1.1.2 then (1 : ℝ) else 0)=
      fun r => q r.1*y r := by
    funext r
    by_cases hc : rowClique r=C <;>
      by_cases he : Crosses blocks r.1.1.1 r.1.1.2 <;> simp [q,y,hc,he]
  rw [he]
  apply rowLowerEquiv.injective
  rw [rowLowerEquiv.apply_symm_apply,rowLower_edge_mul]
  have hmon : rowLowerEquiv y=
      fun r : HubResponseRow H => delta (setMonomial C) r.1.1.1 r.1.1.2 r.2.1 := by
    simpa only [y,zeta_delta_coordinate] using
      rowLower_raw_coefficients (fun D : Finset H => if D=C then 1 else 0)
  rw [hmon]
  funext r
  have hu : r.1.1.1∉r.2.1 := by
    intro hm
    exact not_mem_commonNeighbors_left ⊤ _ _ ((mem_powerset.mp r.2.2) hm)
  have hv : r.1.1.2∉r.2.1 := by
    intro hm
    exact not_mem_commonNeighbors_right ⊤ _ _ ((mem_powerset.mp r.2.2) hm)
  change negativeResponse (complementModule C blocks) r.1.1.1 r.1.1.2 r.2.1=
    q r.1*delta (setMonomial C) r.1.1.1 r.1.1.2 r.2.1
  rw [complementModule_negative h (ne_of_lt r.1.2.1) hu hv,
    delta_setMonomial (ne_of_lt r.1.2.1) hu hv]
  by_cases he : Crosses blocks r.1.1.1 r.1.1.2
  · obtain ⟨A,hA,B,hB,hAB,ha,hb⟩:=he
    have haC:=h.subsets A hA ha
    have hbC:=h.subsets B hB hb
    have hcross : Crosses blocks r.1.1.1 r.1.1.2 := ⟨A,hA,B,hB,hAB,ha,hb⟩
    simp only [q,hcross,one_mul,haC,hbC,true_and,ite_true]
  · simp only [q,he,zero_mul,false_and,ite_false]

def positivePairBlocks (u v : H) : Finset (Finset H):={{u},{v}}

theorem positivePairBlocks_family (C : Finset H) {u v : H}
    (hu : u∈C) (hv : v∈C) (huv : u≠ v) :
    ComplementFamily C (positivePairBlocks u v) := by
  classical
  refine ⟨?_,?_,?_,?_⟩
  · simp [positivePairBlocks,huv]
  · intro B hB
    simp only [positivePairBlocks,mem_insert,mem_singleton] at hB
    rcases hB with rfl | rfl
    · simpa only [singleton_subset_iff] using hu
    · simpa only [singleton_subset_iff] using hv
  · intro B hB
    simp only [positivePairBlocks,mem_insert,mem_singleton] at hB
    rcases hB with rfl | rfl <;> exact singleton_nonempty _
  · intro A hA B hB hAB
    simp only [positivePairBlocks,mem_insert,mem_singleton] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · exact False.elim (hAB rfl)
    · simp [huv]
    · simp [huv.symm]
    · exact False.elim (hAB rfl)

theorem crosses_positivePairBlocks {u v : H} (huv : u≠ v) (a b : H) :
    Crosses (positivePairBlocks u v) a b ↔
      (a=u ∧ b=v) ∨ (a=v ∧ b=u) := by
  classical
  constructor
  · rintro ⟨A,hA,B,hB,hAB,ha,hb⟩
    simp only [positivePairBlocks,mem_insert,mem_singleton] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · exact False.elim (hAB rfl)
    · exact Or.inl ⟨mem_singleton.mp ha,mem_singleton.mp hb⟩
    · exact Or.inr ⟨mem_singleton.mp ha,mem_singleton.mp hb⟩
    · exact False.elim (hAB rfl)
  · rintro (⟨ha,hb⟩ | ⟨ha,hb⟩)
    · subst a; subst b
      exact ⟨{u},by simp [positivePairBlocks],{v},by simp [positivePairBlocks],
        by simpa using huv,mem_singleton_self _,mem_singleton_self _⟩
    · subst a; subst b
      exact ⟨{v},by simp [positivePairBlocks],{u},by simp [positivePairBlocks],
        by simpa using huv.symm,mem_singleton_self _,mem_singleton_self _⟩

def positivePairModule (C : Finset H) (u v : H) : SetFunction H:=
  complementModule C (positivePairBlocks u v)

/-- The pure positive module of Lemma7.4, with every ambient hub retained. -/
theorem positivePairModule_coefficients (C : Finset H) {u v : H}
    (hu : u∈C) (hv : v∈C) (huv : u< v) :
    rowLowerEquiv.symm (responseVector (positivePairModule C u v))=
      fun r : HubResponseRow H =>
        if rowClique r=C ∧ r.1.1.1=u ∧ r.1.1.2=v then 1 else 0 := by
  rw [positivePairModule,complementModule_response_coefficients
    (positivePairBlocks_family C hu hv (ne_of_lt huv))]
  funext r
  rw [crosses_positivePairBlocks (ne_of_lt huv)]
  have hn : ¬(r.1.1.1=v ∧ r.1.1.2=u) := by
    rintro ⟨ha,hb⟩
    have hh:=r.1.2.1
    rw [ha,hb] at hh
    exact (not_lt_of_ge huv.le) hh
  simp only [or_false,hn,and_assoc]

theorem positivePairModule_essential (C : Finset H) {u v : H}
    (hu : u∈C) (hv : v∈C) (huv : u≠ v) {a : H} (ha : a∈C) :
    Essential (positivePairModule C u v) a :=
  (positivePairBlocks_family C hu hv huv).essential ha

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart146

section BundlePart147
/- Source: Papers/GraphicalZonotopes/NegativePureBooleanResponses.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
variable {H : Type*} [Fintype H] [LinearOrder H]

def negativePairBlocks (C : Finset H) (u v : H) : Finset (Finset H):=
  insert {u,v} ((C\{u,v}).image singleton)

theorem mem_negativePairBlocks (C : Finset H) (u v : H) (B : Finset H) :
    B∈negativePairBlocks C u v ↔
      B={u,v} ∨ ∃ a,a∈C ∧ a≠ u ∧ a≠ v ∧ B={a} := by
  constructor
  · intro hB
    rcases mem_insert.mp hB with he | he
    · exact Or.inl he
    · obtain ⟨a,ha,he⟩:=mem_image.mp he
      have ha':=mem_sdiff.mp ha
      have hn : a≠ u ∧ a≠ v:=by simpa only [mem_insert,mem_singleton,not_or] using ha'.2
      exact Or.inr ⟨a,ha'.1,hn.1,hn.2,he.symm⟩
  · rintro (he | ⟨a,ha,hau,hav,he⟩)
    · exact mem_insert.mpr (Or.inl he)
    · apply mem_insert_of_mem
      exact mem_image.mpr ⟨a,mem_sdiff.mpr ⟨ha,by simp [hau,hav]⟩,he.symm⟩

theorem negativePairBlocks_family (C : Finset H) (hC : 3≤ C.card) {u v : H}
    (hu : u∈C) (hv : v∈C) (huv : u≠ v) :
    ComplementFamily C (negativePairBlocks C u v) := by
  have hpair : ({u,v} : Finset H)⊆C:=by simp [insert_subset_iff,singleton_subset_iff,hu,hv]
  have hdiff : (C\{u,v}).Nonempty := by
    apply card_pos.mp
    rw [card_sdiff_of_subset hpair,card_pair huv]
    omega
  obtain ⟨a,ha⟩:=hdiff
  have ha':=mem_sdiff.mp ha
  have hauv : a≠ u ∧ a≠ v:=by simpa only [mem_insert,mem_singleton,not_or] using ha'.2
  have hpairmem : ({u,v} : Finset H)∈negativePairBlocks C u v:=by
    exact (mem_negativePairBlocks _ _ _ _).mpr (Or.inl rfl)
  have hasingle : ({a} : Finset H)∈negativePairBlocks C u v:=
    (mem_negativePairBlocks _ _ _ _).mpr (Or.inr ⟨a,ha'.1,hauv.1,hauv.2,rfl⟩)
  have hne : ({u,v} : Finset H)≠{a} := by
    intro he
    have hc:=congrArg Finset.card he
    rw [card_pair huv,card_singleton] at hc
    omega
  refine ⟨?_,?_,?_,?_⟩
  · have hh : 1<(negativePairBlocks C u v).card:=
      one_lt_card.mpr ⟨{u,v},hpairmem,{a},hasingle,hne⟩
    omega
  · intro B hB
    rcases (mem_negativePairBlocks _ _ _ _).mp hB with rfl | ⟨b,hb,hbu,hbv,rfl⟩
    · exact hpair
    · exact singleton_subset_iff.mpr hb
  · intro B hB
    rcases (mem_negativePairBlocks _ _ _ _).mp hB with rfl | ⟨b,hb,hbu,hbv,rfl⟩
    · exact ⟨u,by simp⟩
    · exact singleton_nonempty b
  · intro A hA B hB hAB
    rcases (mem_negativePairBlocks _ _ _ _).mp hA with rfl | ⟨a,ha,hau,hav,rfl⟩
    · rcases (mem_negativePairBlocks _ _ _ _).mp hB with rfl | ⟨b,hb,hbu,hbv,rfl⟩
      · exact False.elim (hAB rfl)
      · simp [hbu,hbv,Ne.symm hbu,Ne.symm hbv]
    · rcases (mem_negativePairBlocks _ _ _ _).mp hB with rfl | ⟨b,hb,hbu,hbv,rfl⟩
      · simp [hau,hav,Ne.symm hau,Ne.symm hav]
      · have hab : a≠ b:=fun he => hAB (congrArg singleton he)
        simp [hab]

theorem crosses_negativePairBlocks (C : Finset H) (hC : 3≤ C.card) {u v : H}
    (hu : u∈C) (hv : v∈C) (huv : u≠ v) (a b : H) :
    Crosses (negativePairBlocks C u v) a b ↔
      a∈C ∧ b∈C ∧ a≠ b ∧ ¬(a∈({u,v} : Finset H) ∧ b∈({u,v} : Finset H)) := by
  let hfamily:=negativePairBlocks_family C hC hu hv huv
  have hpairmem : ({u,v} : Finset H)∈negativePairBlocks C u v:=
    (mem_negativePairBlocks _ _ _ _).mpr (Or.inl rfl)
  have hsingle : ∀ x,x∈C → x∉({u,v} : Finset H) →
      ({x} : Finset H)∈negativePairBlocks C u v := by
    intro x hx hxn
    have hn : x≠ u ∧ x≠ v:=by simpa only [mem_insert,mem_singleton,not_or] using hxn
    exact (mem_negativePairBlocks _ _ _ _).mpr (Or.inr ⟨x,hx,hn.1,hn.2,rfl⟩)
  constructor
  · rintro ⟨A,hA,B,hB,hAB,ha,hb⟩
    refine ⟨hfamily.subsets A hA ha,hfamily.subsets B hB hb,?_,?_⟩
    · intro he
      exact hAB (hfamily.shared_mem_eq hA hB ha (he.symm ▸ hb))
    · rintro ⟨hap,hbp⟩
      exact hAB ((hfamily.shared_mem_eq hA hpairmem ha hap).trans
        (hfamily.shared_mem_eq hpairmem hB hbp hb))
  · rintro ⟨ha,hb,hab,hnot⟩
    by_cases hap : a∈({u,v} : Finset H)
    · have hbp : b∉({u,v} : Finset H):=fun hh => hnot ⟨hap,hh⟩
      refine ⟨{u,v},hpairmem,{b},hsingle b hb hbp,?_,hap,mem_singleton_self b⟩
      intro he
      exact hbp (he.symm ▸ mem_singleton_self b)
    · by_cases hbp : b∈({u,v} : Finset H)
      · refine ⟨{a},hsingle a ha hap,{u,v},hpairmem,?_,mem_singleton_self a,hbp⟩
        intro he
        exact hap (he ▸ mem_singleton_self a)
      · exact ⟨{a},hsingle a ha hap,{b},hsingle b hb hbp,
          fun he => hab (singleton_injective he),mem_singleton_self a,mem_singleton_self b⟩

def negativePairModule (C : Finset H) (u v : H) : SetFunction H:=
  complementModule C (negativePairBlocks C u v)

theorem ordered_pair_membership {a b u v : H} (hab : a< b) (huv : u< v) :
    (a∈({u,v} : Finset H) ∧ b∈({u,v} : Finset H)) ↔ a=u ∧ b=v := by
  simp only [mem_insert,mem_singleton]
  constructor
  · rintro ⟨ha,hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact False.elim ((lt_irrefl _) hab)
    · exact ⟨rfl,rfl⟩
    · exact False.elim ((not_lt_of_ge huv.le) hab)
    · exact False.elim ((lt_irrefl _) hab)
  · rintro ⟨rfl,rfl⟩
    exact ⟨Or.inl rfl,Or.inr rfl⟩

/-- The negative pure module has every coordinate in its clique block except
the specified pair. Modulo the diagonal this is the negative pair class. -/
theorem negativePairModule_coefficients (C : Finset H) (hC : 3≤ C.card) {u v : H}
    (hu : u∈C) (hv : v∈C) (huv : u< v) :
    rowLowerEquiv.symm (responseVector (negativePairModule C u v))=
      fun r : HubResponseRow H =>
        if rowClique r=C ∧ ¬(r.1.1.1=u ∧ r.1.1.2=v) then 1 else 0 := by
  rw [negativePairModule,complementModule_response_coefficients
    (negativePairBlocks_family C hC hu hv (ne_of_lt huv))]
  funext r
  rw [crosses_negativePairBlocks C hC hu hv (ne_of_lt huv),
    ordered_pair_membership r.1.2.1 huv]
  by_cases hrow : rowClique r=C
  · have ha : r.1.1.1∈C:=by rw [← hrow]; simp [rowClique]
    have hb : r.1.1.2∈C:=by rw [← hrow]; simp [rowClique]
    have hne : r.1.1.1≠ r.1.1.2 := ne_of_lt r.1.2.1
    simp [hrow,ha,hb,hne]
  · simp only [hrow,false_and,ite_false]

theorem negativePairModule_essential (C : Finset H) (hC : 3≤ C.card) {u v : H}
    (hu : u∈C) (hv : v∈C) (huv : u≠ v) {a : H} (ha : a∈C) :
    Essential (negativePairModule C u v) a :=
  (negativePairBlocks_family C hC hu hv huv).essential ha

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart147

section BundlePart148
/- Source: Papers/GraphicalZonotopes/PureResponseClasses.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
variable {H : Type*} [Fintype H] [LinearOrder H]

abbrev ResponseQuotient (H : Type*) [Fintype H] [LinearOrder H] :=
  (HubResponseRow H → ℝ) ⧸ LinearMap.range (centralCoefficientSlack (H:=H))

def responseClass (F : SetFunction H) : ResponseQuotient H :=
  (LinearMap.range (centralCoefficientSlack (H:=H))).mkQ (responseVector F)

def coefficientClass : (HubResponseRow H → ℝ) →ₗ[ℝ] ResponseQuotient H :=
  (LinearMap.range (centralCoefficientSlack (H:=H))).mkQ ∘ₗ rowLowerEquiv.toLinearMap

def pureCoordinate (C : Finset H) (u v : H) : ResponseQuotient H :=
  coefficientClass (fun r : HubResponseRow H =>
    if rowClique r=C ∧ r.1.1.1=u ∧ r.1.1.2=v then 1 else 0)

theorem responseClass_eq_coefficientClass (F : SetFunction H) :
    responseClass F=coefficientClass (rowLowerEquiv.symm (responseVector F)) := by
  simp only [coefficientClass,LinearMap.comp_apply,LinearEquiv.coe_coe,
    rowLowerEquiv.apply_symm_apply,responseClass]

theorem coefficientClass_eq_zero_iff (x : HubResponseRow H → ℝ) :
    coefficientClass x=0 ↔ BlockConstant x := by
  change (LinearMap.range (centralCoefficientSlack (H:=H))).mkQ (rowLowerEquiv x)=0 ↔ _
  rw [← LinearMap.mem_ker,Submodule.ker_mkQ,central_range_iff_blockConstant,
    rowLowerEquiv.symm_apply_apply]

/-- The common coordinate in a block is exactly a central coefficient and
vanishes in the response quotient, including all pair and higher blocks. -/
theorem coefficientClass_block_zero (C : Finset H) :
    coefficientClass (fun r : HubResponseRow H => if rowClique r=C then 1 else 0)=0 := by
  apply (coefficientClass_eq_zero_iff _).mpr
  intro r t he
  have hv : rowClique r=rowClique t:=congrArg Subtype.val he
  change (if rowClique r=C then (1 : ℝ) else 0)=(if rowClique t=C then 1 else 0)
  rw [hv]

theorem positivePairModule_class (C : Finset H) {u v : H}
    (hu : u∈C) (hv : v∈C) (huv : u< v) :
    responseClass (positivePairModule C u v)=pureCoordinate C u v := by
  rw [responseClass_eq_coefficientClass,positivePairModule_coefficients C hu hv huv]
  rfl

theorem negativePairModule_class (C : Finset H) (hC : 3≤ C.card) {u v : H}
    (hu : u∈C) (hv : v∈C) (huv : u< v) :
    responseClass (negativePairModule C u v)= -pureCoordinate C u v := by
  rw [responseClass_eq_coefficientClass,negativePairModule_coefficients C hC hu hv huv]
  have he : (fun r : HubResponseRow H =>
      if rowClique r=C ∧ ¬(r.1.1.1=u ∧ r.1.1.2=v) then (1 : ℝ) else 0)=
      (fun r : HubResponseRow H => if rowClique r=C then 1 else 0)-
        (fun r : HubResponseRow H =>
          if rowClique r=C ∧ r.1.1.1=u ∧ r.1.1.2=v then 1 else 0) := by
    funext r
    by_cases hr : rowClique r=C <;>
      by_cases hp : r.1.1.1=u ∧ r.1.1.2=v <;> simp [hr,hp,and_assoc]
  rw [he,map_sub,coefficientClass_block_zero,zero_sub]
  rfl

/-- Lemma7.4 with its actual quotient classes, all variables of `C`
essential, and every other ambient variable explicitly ignored. -/
theorem both_signs_of_pure_coordinate (C : Finset H) (hC : 3≤ C.card) {u v : H}
    (hu : u∈C) (hv : v∈C) (huv : u< v) :
    ∃ P R : SetFunction H,
      IsMonotoneBoolean P ∧ IsMonotoneBoolean R ∧
      (∀ a∈C,Essential P a ∧ Essential R a) ∧
      (∀ a,a∉C → ∀ X,P (insert a X)=P X ∧ R (insert a X)=R X) ∧
      responseClass P=pureCoordinate C u v ∧ responseClass R= -pureCoordinate C u v := by
  refine ⟨positivePairModule C u v,negativePairModule C u v,
    (positivePairBlocks_family C hu hv (ne_of_lt huv)).module_boolean,
    (negativePairBlocks_family C hC hu hv (ne_of_lt huv)).module_boolean,?_,?_,
    positivePairModule_class C hu hv huv,negativePairModule_class C hC hu hv huv⟩
  · intro a ha
    exact ⟨positivePairModule_essential C hu hv (ne_of_lt huv) ha,
      negativePairModule_essential C hC hu hv (ne_of_lt huv) ha⟩
  · intro a ha X
    exact ⟨complementModule_ignores_outside C _ ha X,
      complementModule_ignores_outside C _ ha X⟩

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart148

section BundlePart149
/- Source: Papers/GraphicalZonotopes/BlockPairCoordinates.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H J : Type*} [Fintype H] [LinearOrder H] [Fintype J]

/-- All actual unordered pairs of a fixed clique, represented by the ambient
linear order. No pair is omitted from the quotient block. -/
abbrev PairIn (C : Finset H) :=
  {e : OrientedEdge (⊤ : SimpleGraph H) // e.1.1∈C ∧ e.1.2∈C}

def pairRow (C : Finset H) (e : PairIn C) : HubResponseRow H :=
  ⟨e.1,⟨(C.erase e.1.1.1).erase e.1.1.2,mem_powerset.mpr (by
    intro a ha
    obtain ⟨ha₂,ha'⟩:=mem_erase.mp ha
    obtain ⟨ha₁,_⟩:=mem_erase.mp ha'
    exact (mem_commonNeighbors _ _ _ _).mpr
      ⟨(SimpleGraph.top_adj _ _).mpr ha₁.symm,
        (SimpleGraph.top_adj _ _).mpr ha₂.symm⟩)⟩⟩

@[simp] theorem pairRow_edge (C : Finset H) (e : PairIn C) :
    (pairRow C e).1=e.1 := rfl

@[simp] theorem rowClique_pairRow (C : Finset H) (e : PairIn C) :
    rowClique (pairRow C e)=C := by
  change insert e.1.1.1 (insert e.1.1.2 ((C.erase e.1.1.1).erase e.1.1.2))=C
  ext a
  by_cases ha₁ : a=e.1.1.1
  · subst a
    simp [e.2.1]
  · by_cases ha₂ : a=e.1.1.2
    · subst a
      simp [e.2.2]
    · simp [mem_erase,ha₁,ha₂]

def pairAtRow (C : Finset H) (r : HubResponseRow H) (h : rowClique r=C) : PairIn C :=
  ⟨r.1,by
    rw [← h]
    exact ⟨mem_insert_self _ _,mem_insert_of_mem (mem_insert_self _ _)⟩⟩

/-- A vector on the pairs of `C` as an array in the full response-coordinate
space, with all other clique blocks explicitly zero. -/
def blockCoordinates (C : Finset H) : (PairIn C → ℝ) →ₗ[ℝ] (HubResponseRow H → ℝ) where
  toFun x r := if h : rowClique r=C then x (pairAtRow C r h) else 0
  map_add' x y := by
    funext r
    by_cases h : rowClique r=C <;> simp only [h,dite_true,dite_false,Pi.add_apply,add_zero]
  map_smul' c x := by
    funext r
    by_cases h : rowClique r=C <;>
      simp only [h,dite_true,dite_false,Pi.smul_apply,smul_eq_mul,mul_zero,RingHom.id_apply]

@[simp] theorem blockCoordinates_pairRow (C : Finset H) (x : PairIn C → ℝ)
    (e : PairIn C) : blockCoordinates C x (pairRow C e)=x e := by
  change (if h : rowClique (pairRow C e)=C then x (pairAtRow C (pairRow C e) h) else 0)=x e
  rw [dite_eq_left (rowClique_pairRow C e)]
  congr 1

def blockClass (C : Finset H) : (PairIn C → ℝ) →ₗ[ℝ] ResponseQuotient H :=
  coefficientClass ∘ₗ blockCoordinates C

/-- The kernel of the actual response-quotient map on one clique block is
exactly its constant vectors. This includes every pair of that clique. -/
theorem blockClass_eq_zero_iff (C : Finset H) (e₀ : PairIn C) (x : PairIn C → ℝ) :
    blockClass C x=0 ↔ ∃ c : ℝ,∀ e,x e=c := by
  change coefficientClass (blockCoordinates C x)=0 ↔ _
  rw [coefficientClass_eq_zero_iff]
  constructor
  · intro hx
    refine ⟨x e₀,?_⟩
    intro e
    have he : rowCliqueIndex (pairRow C e)=rowCliqueIndex (pairRow C e₀) := by
      apply Subtype.ext
      exact (rowClique_pairRow C e).trans (rowClique_pairRow C e₀).symm
    simpa only [blockCoordinates_pairRow] using hx _ _ he
  · rintro ⟨c,hc⟩ r t hrt
    have he : rowClique r=rowClique t:=congrArg Subtype.val hrt
    by_cases hr : rowClique r=C
    · have ht : rowClique t=C:=he.symm.trans hr
      change (if h : rowClique r=C then x (pairAtRow C r h) else 0)=
        if h : rowClique t=C then x (pairAtRow C t h) else 0
      rw [dite_eq_left hr,dite_eq_left ht,hc,hc]
    · have ht : rowClique t≠ C:=fun h => hr (he.trans h)
      change (if h : rowClique r=C then x (pairAtRow C r h) else 0)=
        if h : rowClique t=C then x (pairAtRow C t h) else 0
      rw [dite_eq_right hr,dite_eq_right ht]

/-- Omitting one reference pair makes ordinary linear independence of pair
vectors equivalent to independence after passage to the actual quotient.
This is the precise reference-pair argument used in Lemma 7.7. -/
theorem blockClass_linearIndependent_of_reference (C : Finset H) (e₀ : PairIn C)
    (x : J → PairIn C → ℝ) (hx : LinearIndependent ℝ x)
    (hzero : ∀ j,x j e₀=0) :
    LinearIndependent ℝ (fun j => blockClass C (x j)) := by
  rw [Fintype.linearIndependent_iff] at hx ⊢
  intro c hc j
  have hmap : blockClass C (∑ i : J,c i • x i)=0 := by
    simpa only [map_sum,map_smul] using hc
  obtain ⟨a,ha⟩:=(blockClass_eq_zero_iff C e₀ _).mp hmap
  have ha0 : a=0 := by
    have hh:=ha e₀
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,hzero,mul_zero,sum_const_zero] at hh
    exact hh.symm
  have hvec : (∑ i : J,c i • x i)=0 := by
    funext e
    exact (ha e).trans ha0
  exact hx c hvec j

theorem blockClass_linearIndependent_iff_reference (C : Finset H) (e₀ : PairIn C)
    (x : J → PairIn C → ℝ) (hzero : ∀ j,x j e₀=0) :
    LinearIndependent ℝ (fun j => blockClass C (x j)) ↔ LinearIndependent ℝ x := by
  constructor
  · intro hx
    exact LinearIndependent.of_comp (blockClass C) hx
  · intro hx
    exact blockClass_linearIndependent_of_reference C e₀ x hx hzero

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart149

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
