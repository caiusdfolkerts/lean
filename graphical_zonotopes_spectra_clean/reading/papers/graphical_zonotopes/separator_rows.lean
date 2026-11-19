module

public import Papers.GraphicalZonotopes.SeparatorPieces

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Separator
open Finset
open scoped BigOperators
variable {V J : Type*} [Fintype V] [LinearOrder V]
local instance : DecidableEq V := LinearOrder.toDecidableEq
variable [Fintype J] [DecidableEq J]
variable {G : SimpleGraph V} {B : Finset V} {A : J → Finset V}

/-- Boundary types are exactly the original edge/common-neighbor contexts
whose endpoints and conditioning variables lie in the induced boundary. -/
abbrev BoundaryRow (G : SimpleGraph V) (B : Finset V) :=
  {r : BoundaryContext G // r.1.1.1∈B ∧ r.1.1.2∈B ∧ r.2.1⊆B}

abbrev InternalRow (G : SimpleGraph V) (B : Finset V) (A : J → Finset V) (j : J) :=
  {r : BoundaryContext G //
    (r.1.1.1∈A j ∨ r.1.1.2∈A j) ∧ r.2.1⊆B∪A j}

abbrev BranchChoice (A : J → Finset V) (j : J) :=
  {S : Finset V // S⊆A j}

noncomputable instance boundaryRowFintype : Fintype (BoundaryRow G B) := by
  classical
  infer_instance
noncomputable instance internalRowFintype (j : J) : Fintype (InternalRow G B A j) := by
  classical
  infer_instance
noncomputable instance branchChoiceFintype (j : J) : Fintype (BranchChoice A j) := by
  classical
  infer_instance

/-- The actual separator row model obtained from the original set functions. -/
def rowData (h : Partition G B A) :
    Gluing.Data (BoundaryRow G B) J (privateIndex G B A) (boundaryIndex G B)
      (InternalRow G B A) (BranchChoice A) where
  boundary := LinearMap.pi (fun b =>
    (deltaLinear b.1.1.1.1 b.1.1.1.2 b.1.2.1).comp (boundaryFunctionMap h))
  internal j r :=
    (deltaLinear r.1.1.1.1 r.1.1.1.2 r.1.2.1).comp (privateFunctionMap h j)
  response j b X :=
    (deltaLinear b.1.1.1.1 b.1.1.1.2 (b.1.2.1∪X.1)).comp (privateFunctionMap h j)

theorem context_left_not_mem (r : BoundaryContext G) : r.1.1.1∉r.2.1 := by
  intro hm
  exact not_mem_commonNeighbors_left G _ _ ((mem_powerset.mp r.2.2) hm)
theorem context_right_not_mem (r : BoundaryContext G) : r.1.1.2∉r.2.1 := by
  intro hm
  exact not_mem_commonNeighbors_right G _ _ ((mem_powerset.mp r.2.2) hm)

/-- An actual private-edge row of the original cone is exactly its private
model row. No boundary or other-branch coefficient is present in that row. -/
theorem internal_row_eq (h : Partition G B A) (x : Coordinates G B A)
    (j : J) (r : InternalRow G B A j) :
    (rowData h).row (Sum.inl ⟨j,r⟩) x=
      delta (globalFunctionMap h x) r.1.1.1.1 r.1.1.1.2 r.1.2.1 := by
  change delta (privateFunctionMap h j (x.2 j)) _ _ _=_
  rcases r.2.1 with hu | hv
  · exact (delta_private_edge_decompose h x j hu (ne_of_lt r.1.1.2.1)
      (context_left_not_mem r.1) (context_right_not_mem r.1)).symm
  · rw [delta_comm r.1.1.1.1,delta_comm r.1.1.1.1]
    exact (delta_private_edge_decompose h x j hv (ne_of_gt r.1.1.2.1)
      (context_right_not_mem r.1) (context_left_not_mem r.1)).symm

/-- The original slack splits across the exact boundary and private contexts. -/
theorem boundary_formula (h : Partition G B A) (x : Coordinates G B A)
    {u v : V} (huv : u≠v) {S : Finset V} (hu : u∉S) (hv : v∉S) :
    delta (globalFunctionMap h x) u v S=
      delta (boundaryFunctionMap h x.1) u v (S∩B)+
      ∑ j : J,delta (privateFunctionMap h j (x.2 j)) u v ((S∩B)∪(S∩A j)) := by
  rw [function_decompose,delta_add,delta_sum]
  rw [delta_inter_mobius_support (boundaryFunction_supported h x.1) huv hu hv]
  congr 1
  apply sum_congr rfl
  intro j hj
  rw [delta_private_inter h j (x.2 j) huv hu hv,Finset.inter_union_distrib_left]

def combinedContext (S : Finset V) (X : ∀ j,BranchChoice A j) : Finset V :=
  S∪univ.biUnion (fun j => (X j).1)

theorem combinedContext_inter_boundary (h : Partition G B A)
    {S : Finset V} (hSB : S⊆B) (X : ∀ j,BranchChoice A j) :
    combinedContext S X∩B=S := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨hvU,hvB⟩ := mem_inter.mp hv
    rcases mem_union.mp hvU with hvS | hvX
    · exact hvS
    · obtain ⟨j,_,hvj⟩ := mem_biUnion.mp hvX
      exact False.elim (Finset.disjoint_left.mp (h.boundary_disjoint j) hvB ((X j).2 hvj))
  · intro hv
    exact mem_inter.mpr ⟨mem_union_left _ hv,hSB hv⟩

theorem combinedContext_inter_private (h : Partition G B A)
    {S : Finset V} (hSB : S⊆B) (X : ∀ j,BranchChoice A j) (j : J) :
    combinedContext S X∩A j=(X j).1 := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨hvU,hvA⟩ := mem_inter.mp hv
    rcases mem_union.mp hvU with hvS | hvX
    · exact False.elim (Finset.disjoint_left.mp (h.boundary_disjoint j) (hSB hvS) hvA)
    · obtain ⟨k,_,hvk⟩ := mem_biUnion.mp hvX
      by_cases hkj : k=j
      · subst k
        exact hvk
      · exact False.elim (Finset.disjoint_left.mp (h.private_disjoint hkj) ((X k).2 hvk) hvA)
  · intro hv
    exact mem_inter.mpr ⟨mem_union_right _ (mem_biUnion.mpr ⟨j,mem_univ _,hv⟩),(X j).2 hv⟩

theorem boundary_not_mem_combinedContext (h : Partition G B A)
    (S : Finset V) (X : ∀ j,BranchChoice A j) {u : V} (huB : u∈B) (huS : u∉S) :
    u∉combinedContext S X := by
  intro hu
  rcases mem_union.mp hu with hu | hu
  · exact huS hu
  · obtain ⟨j,_,huj⟩ := mem_biUnion.mp hu
    exact Finset.disjoint_left.mp (h.boundary_disjoint j) huB ((X j).2 huj)

/-- Every model boundary row is a genuine original elemental inequality,
with independently chosen private conditioning subsets. -/
theorem boundary_row_eq (h : Partition G B A) (x : Coordinates G B A)
    (b : BoundaryRow G B) (X : ∀ j,BranchChoice A j) :
    (rowData h).row (Sum.inr (b,X)) x=
      delta (globalFunctionMap h x) b.1.1.1.1 b.1.1.1.2 (combinedContext b.1.2.1 X) := by
  have hu := boundary_not_mem_combinedContext h b.1.2.1 X b.2.1 (context_left_not_mem b.1)
  have hv := boundary_not_mem_combinedContext h b.1.2.1 X b.2.2.1 (context_right_not_mem b.1)
  rw [boundary_formula h x (ne_of_lt b.1.1.2.1) hu hv,
    combinedContext_inter_boundary h b.2.2.2 X]
  simp_rw [combinedContext_inter_private h b.2.2.2 X]
  rfl

/-- Nonnegativity of all model rows follows from the genuine supermodular
inequalities on the original graphical function. -/
theorem rowData_nonnegative_of_supermodular (h : Partition G B A) (x : Coordinates G B A)
    (hs : Supermodular (globalFunctionMap h x)) :
    Polyhedral.Nonnegative (rowData h).row x := by
  intro r
  rcases r with ⟨j,r⟩ | ⟨b,X⟩
  · rw [internal_row_eq]
    exact hs.elemental _ _ (ne_of_lt r.1.1.2.1) _
      (context_left_not_mem r.1) (context_right_not_mem r.1)
  · rw [boundary_row_eq]
    exact hs.elemental _ _ (ne_of_lt b.1.1.2.1) _
      (boundary_not_mem_combinedContext h _ X b.2.1 (context_left_not_mem b.1))
      (boundary_not_mem_combinedContext h _ X b.2.2.1 (context_right_not_mem b.1))

/-- Restricting an original common-neighbor context preserves its validity. -/
def restrictContext (r : BoundaryContext G) (T : Finset V) : BoundaryContext G :=
  ⟨r.1,⟨r.2.1∩T,mem_powerset.mpr (inter_subset_left.trans (mem_powerset.mp r.2.2))⟩⟩

/-- Every original row is recovered from the model, so feasibility is an
actual equivalence rather than an implication in a convenient subsystem. -/
theorem supermodular_of_rowData_nonnegative (h : Partition G B A) (x : Coordinates G B A)
    (hn : Polyhedral.Nonnegative (rowData h).row x) :
    Supermodular (globalFunctionMap h x) := by
  apply (supermodular_iff_boundarySlacks_nonnegative G (functionEquiv h x)).mpr
  intro r
  by_cases hb : r.1.1.1∈B ∧ r.1.1.2∈B
  · let b : BoundaryRow G B := ⟨restrictContext r B,hb.1,hb.2,inter_subset_right⟩
    let X : ∀ j,BranchChoice A j := fun j => ⟨r.2.1∩A j,inter_subset_right⟩
    have hm := hn (Sum.inr (b,X))
    change 0≤delta (globalFunctionMap h x) r.1.1.1 r.1.1.2 r.2.1
    rw [boundary_formula h x (ne_of_lt r.1.2.1)
      (context_left_not_mem r) (context_right_not_mem r)]
    exact hm
  · have hu_or_hv : (∃ j,r.1.1.1∈A j) ∨ (∃ j,r.1.1.2∈A j) := by
      by_cases huB : r.1.1.1∈B
      · exact Or.inr ((h.cover _).resolve_left (fun hvB => hb ⟨huB,hvB⟩))
      · exact Or.inl ((h.cover _).resolve_left huB)
    rcases hu_or_hv with ⟨j,huj⟩ | ⟨j,hvj⟩
    · let r' : InternalRow G B A j :=
        ⟨restrictContext r (B∪A j),Or.inl huj,inter_subset_right⟩
      have hm := hn (Sum.inl ⟨j,r'⟩)
      change 0≤delta (globalFunctionMap h x) r.1.1.1 r.1.1.2 r.2.1
      rw [delta_private_edge_decompose h x j huj (ne_of_lt r.1.2.1)
        (context_left_not_mem r) (context_right_not_mem r),
        delta_private_inter h j (x.2 j) (ne_of_lt r.1.2.1)
        (context_left_not_mem r) (context_right_not_mem r)]
      exact hm
    · let r' : InternalRow G B A j :=
        ⟨restrictContext r (B∪A j),Or.inr hvj,inter_subset_right⟩
      have hm := hn (Sum.inl ⟨j,r'⟩)
      change 0≤delta (globalFunctionMap h x) r.1.1.1 r.1.1.2 r.2.1
      rw [delta_comm r.1.1.1,delta_private_edge_decompose h x j hvj (ne_of_gt r.1.2.1)
        (context_right_not_mem r) (context_left_not_mem r),
        delta_private_inter h j (x.2 j) (ne_of_gt r.1.2.1)
        (context_right_not_mem r) (context_left_not_mem r),delta_comm r.1.1.2]
      exact hm

theorem rowData_nonnegative_iff (h : Partition G B A) (x : Coordinates G B A) :
    Polyhedral.Nonnegative (rowData h).row x ↔ Supermodular (globalFunctionMap h x) :=
  ⟨supermodular_of_rowData_nonnegative h x,rowData_nonnegative_of_supermodular h x⟩

end Separator
end GraphicalZonotopes
