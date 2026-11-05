module

public import Papers.GraphicalZonotopes.TwoHubPartition

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
          have hij : i≠j := fun he => hxy (by subst j; rfl)
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
