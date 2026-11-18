module

public import Papers.GraphicalZonotopes.SeparatorCone
public import Papers.GraphicalZonotopes.SeparatorActiveCapacity
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Separator
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V J : Type*} [Fintype V] [LinearOrder V]
local instance : DecidableEq V := LinearOrder.toDecidableEq
variable [Fintype J] [DecidableEq J]
variable {G : SimpleGraph V} {B : Finset V} {A : J → Finset V}

noncomputable instance branchChoiceInhabited (j : J) : Inhabited (BranchChoice A j) :=
  ⟨⟨∅,empty_subset _⟩⟩

/-- The conditional response is the actual minimum over every private subset,
including all variables whose selected coefficient happens to be zero. -/
def conditionalMin (h : Partition G B A) (f : ∀ j,privateIndex G B A j → ℝ)
    (j : J) (b : BoundaryRow G B) : ℝ :=
  univ.inf' univ_nonempty (fun X : BranchChoice A j => (rowData h).response j b X (f j))

theorem conditionalMin_le (h : Partition G B A) (f : ∀ j,privateIndex G B A j → ℝ)
    (j : J) (b : BoundaryRow G B) (X : BranchChoice A j) :
    conditionalMin h f j b≤(rowData h).response j b X (f j) :=
  Finset.inf'_le _ (mem_univ X)

theorem conditionalMin_attained (h : Partition G B A)
    (f : ∀ j,privateIndex G B A j → ℝ) (j : J) (b : BoundaryRow G B) :
    ∃ X : BranchChoice A j,(rowData h).response j b X (f j)=conditionalMin h f j b := by
  obtain ⟨X,_,he⟩ := Finset.exists_mem_eq_inf' (s := univ) univ_nonempty
    (fun X : BranchChoice A j => (rowData h).response j b X (f j))
  exact ⟨X,he.symm⟩

abbrev BoundaryEdge (G : SimpleGraph V) (B : Finset V) :=
  {e : OrientedEdge G // e.1.1∈B ∧ e.1.2∈B}
noncomputable instance boundaryEdgeFintype : Fintype (BoundaryEdge G B) := by
  classical
  infer_instance

def boundaryRowEquiv : BoundaryRow G B ≃
    Σ e : BoundaryEdge G B,{S : Finset V // S⊆commonNeighbors G e.1.1.1 e.1.1.2∩B} where
  toFun r := ⟨⟨r.1.1,r.2.1,r.2.2.1⟩,
    ⟨r.1.2.1,subset_inter (mem_powerset.mp r.1.2.2) r.2.2.2⟩⟩
  invFun r := ⟨⟨r.1.1,⟨r.2.1,mem_powerset.mpr (r.2.2.trans inter_subset_left)⟩⟩,
    r.1.2.1,r.1.2.2,r.2.2.trans inter_subset_right⟩
  left_inv r := rfl
  right_inv r := rfl

def subsetPowersetEquiv (T : Finset V) : {S : Finset V // S⊆T} ≃ ↥T.powerset where
  toFun S := ⟨S.1,mem_powerset.mpr S.2⟩
  invFun S := ⟨S.1,mem_powerset.mp S.2⟩
  left_inv S := rfl
  right_inv S := rfl

/-- Exactly one row for each unordered boundary edge and each subset of its
common neighbors in the induced boundary graph. -/
theorem boundaryRow_card : Fintype.card (BoundaryRow G B)=
    ∑ e : BoundaryEdge G B,2^(commonNeighbors G e.1.1.1 e.1.1.2∩B).card := by
  rw [Fintype.card_congr (boundaryRowEquiv (G := G) (B := B)),Fintype.card_sigma]
  apply sum_congr rfl
  intro e he
  rw [Fintype.card_congr (subsetPowersetEquiv _)]
  simp only [Fintype.card_coe, card_powerset]

def boundaryCliques (G : SimpleGraph V) (B : Finset V) : Finset (Finset V) := by
  classical
  exact B.powerset.filter (IsCliqueCoordinate G)

def boundaryCliqueEquiv : boundaryIndex G B ≃ ↥(boundaryCliques G B) where
  toFun C := ⟨C.1.1,by exact mem_filter.mpr ⟨mem_powerset.mpr C.2,C.1.2⟩⟩
  invFun C := ⟨⟨C.1,by exact (mem_filter.mp C.2).2⟩,
    by exact mem_powerset.mp (mem_filter.mp C.2).1⟩
  left_inv C := rfl
  right_inv C := rfl

/-- The boundary-coordinate dimension is precisely the number of cliques
of size at least two in the induced boundary graph. -/
theorem boundaryIndex_card : Fintype.card (boundaryIndex G B)=(boundaryCliques G B).card := by
  rw [Fintype.card_congr (boundaryCliqueEquiv (G := G) (B := B)),Fintype.card_coe]

/-- Lemma5.1 in original graphical coordinates, including zero private blocks.
The left side counts exactly the branches carrying a nonzero Möbius block. -/
theorem separator_capacity_for_function (h : Partition G B A)
    (z : graphicalFunctionSpace G) (hz : ExtremeSupermodular z.1) :
    Fintype.card (Gluing.ActiveBranch (((functionEquiv h).symm z).2))≤
      (∑ e : BoundaryEdge G B,2^(commonNeighbors G e.1.1.1 e.1.1.2∩B).card)-
        (boundaryCliques G B).card+1 := by
  let x : Coordinates G B A := (functionEquiv h).symm z
  have hxe : globalFunctionMap h x=z.1 := by
    exact congrArg Subtype.val ((functionEquiv h).apply_symm_apply z)
  have hex : Polyhedral.ExtremeRay (rowData h).row x :=
    (rowData_extreme_iff h x).mpr (by rw [hxe]; exact hz)
  have hass : Gluing.assemble x.1 (fun _ : J => (1 : ℝ)) x.2=x := by
    apply Prod.ext
    · rfl
    · funext j
      exact one_smul ℝ (x.2 j)
  have hb := Gluing.active_separator_capacity (rowData h) x.2 (conditionalMin h x.2)
    (conditionalMin_le h x.2) (conditionalMin_attained h x.2) x.1
    (fun _ : J => (1 : ℝ)) (fun _ => zero_lt_one) (hass.symm ▸ hex)
  rw [boundaryRow_card,boundaryIndex_card] at hb
  exact hb

/-- The literal induced-separator instance of Lemma5.1, with the private
parts equal to all connected components of G minus B. -/
theorem induced_separator_capacity (G : SimpleGraph V) (B : Finset V)
    (z : graphicalFunctionSpace G) (hz : ExtremeSupermodular z.1) :
    Fintype.card (Gluing.ActiveBranch
      (((functionEquiv (componentPartition G B)).symm z).2))≤
      (∑ e : BoundaryEdge G B,2^(commonNeighbors G e.1.1.1 e.1.1.2∩B).card)-
        (boundaryCliques G B).card+1 := by
  classical
  exact separator_capacity_for_function (componentPartition G B) z hz

section PositiveGluing
variable (h : Partition G B A)
variable (f : ∀ j,privateIndex G B A j → ℝ)
variable (z : boundaryIndex G B → ℝ) (lam : J → ℝ)
variable (hlam : ∀ j,0<lam j) (hf : ∀ j,f j≠0)
variable (hi : ∀ j r,0≤(rowData h).internal j r (f j))
variable (hprivate : ∀ j g,(rowData h).PrivateKernel f (conditionalMin h f) j g →
  ∃ c : ℝ,g=c • f j)
variable (hclose : (rowData h).Closure (conditionalMin h f) z lam)
include hlam hf hi hprivate hclose

def gluedCoordinates : Coordinates G B A := Gluing.assemble z lam f

theorem glued_supermodular :
    Supermodular (globalFunctionMap h (gluedCoordinates f z lam)) := by
  apply (rowData_nonnegative_iff h _).mp
  exact Gluing.assembled_nonnegative (rowData h) f (conditionalMin h f)
    (conditionalMin_le h f) hi z lam hlam hclose

/-- Theorem5.4's exact isomorphism, now for the complete original graphical
common-zero space rather than an abstract inequality model. -/
def graphicalTightRelationEquiv :
    Polyhedral.tightKernel (contextRow G) (functionEquiv h (gluedCoordinates f z lam)) ≃ₗ[ℝ]
      LinearMap.ker ((rowData h).relationLinear (conditionalMin h f)) :=
  (graphicalTightEquiv h (gluedCoordinates f z lam)
    (Gluing.assembled_nonnegative (rowData h) f (conditionalMin h f)
      (conditionalMin_le h f) hi z lam hlam hclose)).symm.trans
    (Gluing.tightRelationEquiv (rowData h) f (conditionalMin h f)
      (conditionalMin_le h f) (conditionalMin_attained h f) z lam hlam hclose
      hprivate hf (rowData_boundary_injective h))

/-- Exact common-zero-space dimension in Theorem5.4, with genuine conditional
minima and every zero coefficient slot retained in its ambient private space. -/
theorem graphical_tight_finrank_eq_relation_finrank :
    Module.finrank ℝ
      (Polyhedral.tightKernel (contextRow G) (functionEquiv h (gluedCoordinates f z lam)))=
    Module.finrank ℝ (LinearMap.ker ((rowData h).relationLinear (conditionalMin h f))) :=
  (graphicalTightRelationEquiv h f z lam hlam hf hi hprivate hclose).finrank_eq

/-- The complete extremality equivalence in Theorem5.4. -/
theorem graphical_extreme_iff_relation_finrank_one :
    ExtremeSupermodular (globalFunctionMap h (gluedCoordinates f z lam)) ↔
      Module.finrank ℝ (LinearMap.ker ((rowData h).relationLinear (conditionalMin h f)))=1 := by
  rw [←rowData_extreme_iff]
  exact Gluing.extreme_iff_relation_finrank_one (rowData h) f (conditionalMin h f)
    (conditionalMin_le h f) (conditionalMin_attained h f) hi z lam hlam hclose
    hprivate hf (rowData_boundary_injective h) (rowData_pointed h)

/-- The unique relation is precisely the positive construction vector, and
the number of branches satisfies the exact induced-boundary capacity. -/
theorem graphical_positive_relation_and_capacity
    (he : ExtremeSupermodular (globalFunctionMap h (gluedCoordinates f z lam))) :
    LinearMap.ker ((rowData h).relationLinear (conditionalMin h f))=Submodule.span ℝ {lam} ∧
    Fintype.card J≤
      (∑ e : BoundaryEdge G B,2^(commonNeighbors G e.1.1.1 e.1.1.2∩B).card)-
        (boundaryCliques G B).card+1 := by
  have hd := (graphical_extreme_iff_relation_finrank_one h f z lam hlam hf hi hprivate hclose).mp he
  refine ⟨Gluing.relationKernel_eq_span_scales (rowData h) (conditionalMin h f) z lam
    hlam hclose hd,?_⟩
  have hb := Gluing.branch_count_le_capacity (rowData h) (conditionalMin h f)
    (rowData_boundary_injective h) hd
  rw [boundaryRow_card,boundaryIndex_card] at hb
  exact hb

end PositiveGluing
end Separator
end GraphicalZonotopes
