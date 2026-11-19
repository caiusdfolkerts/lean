module

public import Unimodular.SeriesParallelMinorClosure
public import Matroid.Connectivity.Connected
public import Matroid.ForMathlib.Partition.Rep
public import Matroid.Sum

/-!
# Literal connected-component sums of series-parallel network matroids

The components are the actual circuit-connectivity blocks of the original
matroid. The sum is Mathlib's disjointSigma on the unchanged ground type.
Every component network is obtained from the existing proved equivalence
between ordinary series/parallel extensions and explicit eligible networks.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open scoped Classical Matroid
open Set

namespace Unimodular.SeriesParallel.NetworkComponents

variable {α : Type*} (M : Matroid α)

/-- The genuine nonempty circuit-connectivity blocks, with original labels. -/
abbrev Block := {S : Set α // S ∈ M.ConnPartition}

/-- The matroid of a component is the actual ordinary restriction. -/
def matroid (C : Block M) : Matroid α := M ↾ C.val

@[simp] theorem ground (C : Block M) : (matroid M C).E = C.val := rfl

theorem block_subset_ground (C : Block M) : C.val ⊆ M.E := by
  simpa only [Matroid.connPartition_supp] using
    M.ConnPartition.subset_of_mem C.property

theorem pairwise_disjoint :
    Pairwise (fun C D : Block M => Disjoint (matroid M C).E (matroid M D).E) := by
  intro C D hCD
  change Disjoint C.val D.val
  exact M.ConnPartition.disjoint C.property D.property
    (fun h => hCD (Subtype.ext h))

theorem iUnion_ground : (⋃ C : Block M, (matroid M C).E) = M.E := by
  ext x
  constructor
  · intro hx
    obtain ⟨C, hxC⟩ := Set.mem_iUnion.mp hx
    exact block_subset_ground M C hxC
  · intro hx
    have hs : x ∈ M.ConnPartition.supp := by
      simpa only [Matroid.connPartition_supp] using hx
    obtain ⟨S, hS, hxS⟩ := M.ConnPartition.mem_supp_iff.mp hs
    exact Set.mem_iUnion.mpr ⟨⟨S, hS⟩, hxS⟩

/-- The restriction to a circuit-connectivity block really is connected. -/
theorem connected (C : Block M) : (matroid M C).Connected := by
  refine ⟨⟨?_⟩, ?_⟩
  · exact M.ConnPartition.nonempty_of_mem C.property
  · intro e f he hf
    change e ∈ C.val at he
    change f ∈ C.val at hf
    have hef : M.ConnectedTo e f :=
      (Matroid.connPartition_rel M).mp
        (M.ConnPartition.rel_of_mem_of_mem C.property he hf)
    rcases hef with ⟨hef, _⟩ | ⟨S, hS, heS, hfS⟩
    · subst f
      exact Matroid.connectedTo_self he
    · have hSC : S ⊆ C.val :=
        hS.subset_of_mem_connPartition C.property heS he
      have hS' : (matroid M C).IsCircuit S :=
        (Matroid.restrict_isCircuit_iff (block_subset_ground M C)).mpr ⟨hS, hSC⟩
      exact hS'.mem_connectedTo_mem heS hfS

/-- Equality with the literal direct sum of all actual connected components.
The reverse independence implication uses an actual circuit of a dependent
set and the theorem that a circuit lies in one connectivity block. -/
theorem decomposition :
    M = Matroid.disjointSigma (matroid M) (pairwise_disjoint M) := by
  apply Matroid.ext_indep (by
    rw [Matroid.disjointSigma_ground_eq]
    exact (iUnion_ground M).symm)
  intro I _
  rw [Matroid.disjointSigma_indep_iff, iUnion_ground M]
  constructor
  · intro hI
    refine ⟨?_, hI.subset_ground⟩
    intro C
    change (M ↾ C.val).Indep (I ∩ C.val)
    exact Matroid.restrict_indep_iff.mpr
      ⟨hI.subset Set.inter_subset_left, Set.inter_subset_right⟩
  · rintro ⟨hparts, hIE⟩
    by_contra hnot
    obtain ⟨S, hSI, hS⟩ :=
      ((Matroid.not_indep_iff hIE).mp hnot).exists_isCircuit_subset
    obtain ⟨e, heS⟩ := hS.nonempty
    have heE := hS.subset_ground heS
    have hesupp : e ∈ M.ConnPartition.supp := by
      simpa only [Matroid.connPartition_supp] using heE
    obtain ⟨C, hC, heC⟩ := M.ConnPartition.mem_supp_iff.mp hesupp
    have hSC : S ⊆ C := hS.subset_of_mem_connPartition hC heS heC
    have hpart := hparts (⟨C, hC⟩ : Block M)
    change (M ↾ C).Indep (I ∩ C) at hpart
    have hIC : M.Indep (I ∩ C) := (Matroid.restrict_indep_iff.mp hpart).1
    exact hS.not_indep (hIC.subset (fun x hx => ⟨hSI hx, hSC hx⟩))

/-- Finiteness is derived from the actual ground, not assumed for a partition. -/
theorem blocks_finite (hE : M.E.Finite) : Finite (Block M) := by
  have hparts : (M.ConnPartition : Set (Set α)).Finite :=
    M.ConnPartition.finite_of_finite (by
      simpa only [Matroid.connPartition_supp] using hE)
  letI : Fintype (Block M) := hparts.fintype
  infer_instance

/-- The actual component restriction is an ordinary minor. -/
theorem isMinor (C : Block M) : matroid M C ≤m M :=
  M.restrict_isMinor (block_subset_ground M C)

/-- Series-parallel necessity therefore passes to each actual component. -/
theorem seriesParallel (hM : GroundSeriesParallel M) (C : Block M) :
    GroundSeriesParallel (matroid M C) :=
  hM.minor (isMinor M C)

/-- The existing abstract construction theorem supplies a literal eligible
network and an equality of the whole matroid after enumerating its ground. -/
theorem network (hM : GroundSeriesParallel M) :
    ∃ (m : ℕ) (e : Fin m ≃ M.E) (G : RootedNetwork m m),
      G.HasEligibleConstruction ∧
      (M.restrictSubtype M.E).mapEquiv e.symm = G.cycleMatroid := by
  obtain ⟨m, e, he⟩ := hM.finite_onGround
  obtain ⟨G, hG, hEq⟩ := (abstract_construction_iff_seriesParallel _).mp he
  exact ⟨m, e, G, hG, hEq⟩

/-- A finite literal direct sum of connected network matroids, with no
replacement of the original ground by a simplified or representable surrogate. -/
theorem direct_sum_network_components (hM : GroundSeriesParallel M) :
    Finite (Block M) ∧
    M = Matroid.disjointSigma (matroid M) (pairwise_disjoint M) ∧
    ∀ C : Block M, (matroid M C).Connected ∧
      ∃ (m : ℕ) (e : Fin m ≃ (matroid M C).E) (G : RootedNetwork m m),
        G.HasEligibleConstruction ∧
        ((matroid M C).restrictSubtype (matroid M C).E).mapEquiv e.symm =
          G.cycleMatroid := by
  refine ⟨blocks_finite M hM.ground_finite, decomposition M, ?_⟩
  intro C
  exact ⟨connected M C, network (matroid M C) (seriesParallel M hM C)⟩

end Unimodular.SeriesParallel.NetworkComponents

#print axioms Unimodular.SeriesParallel.NetworkComponents.decomposition
#print axioms Unimodular.SeriesParallel.NetworkComponents.direct_sum_network_components
