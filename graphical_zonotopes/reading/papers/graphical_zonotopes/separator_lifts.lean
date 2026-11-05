module

public import Papers.GraphicalZonotopes.SeparatorTheorems
public import Papers.GraphicalZonotopes.SeparatorKernelSemantics

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

/-- A branch may carry any boundary lift, in addition to its private block. -/
def branchWithLift (h : Partition G B A) (j : J)
    (f : privateIndex G B A j → ℝ) (l : boundaryIndex G B → ℝ) : SetFunction V :=
  boundaryFunctionMap h l+privateFunctionMap h j f

/-- Every graphical branch whose other private blocks vanish has exactly
this form. Thus choosing the zero boundary lift loses no original branch. -/
theorem branch_reconstruction (h : Partition G B A) (j : J)
    (g : graphicalFunctionSpace G)
    (hg : ∀ k,k≠j → ((functionEquiv h).symm g).2 k=0) :
    g.1=branchWithLift h j (((functionEquiv h).symm g).2 j)
      (((functionEquiv h).symm g).1) := by
  let x : Coordinates G B A := (functionEquiv h).symm g
  have he : globalFunctionMap h x=g.1 :=
    congrArg Subtype.val ((functionEquiv h).apply_symm_apply g)
  rw [←he,function_decompose]
  unfold branchWithLift
  congr 1
  apply sum_eq_single j
  · intro k hk hkj
    rw [hg k hkj,map_zero]
  · simp

@[simp] theorem private_coordinate_eq_mobius (h : Partition G B A)
    (g : graphicalFunctionSpace G) (j : J) (C : privateIndex G B A j) :
    ((functionEquiv h).symm g).2 j C=mobius g.1 C.1.1 := rfl

/-- Ordinary coefficient support on a branch implies the exact zero pattern
needed above; this connects the presentation to the paper's induced branches. -/
theorem other_private_blocks_zero_of_support (h : Partition G B A) (j : J)
    (g : graphicalFunctionSpace G)
    (hg : CoefficientSupportedOn (B∪A j) (mobius g.1)) :
    ∀ k,k≠j → ((functionEquiv h).symm g).2 k=0 := by
  intro k hkj
  funext C
  rw [private_coordinate_eq_mobius]
  apply hg C.1.1
  intro hCj
  obtain ⟨u,huC,huB⟩ := Finset.not_subset.mp C.2.1
  have huk : u∈A k := (mem_union.mp (C.2.2 huC)).resolve_left huB
  have huj : u∈A j := (mem_union.mp (hCj huC)).resolve_left huB
  exact Finset.disjoint_left.mp (h.private_disjoint hkj) huk huj

theorem branchChoice_union_inter_boundary (h : Partition G B A)
    {S : Finset V} (hS : S⊆B) (j : J) (X : BranchChoice A j) :
    (S∪X.1)∩B=S := by
  ext v
  constructor
  · intro hv
    obtain ⟨hvU,hvB⟩ := mem_inter.mp hv
    rcases mem_union.mp hvU with hvS | hvX
    · exact hvS
    · exact False.elim (Finset.disjoint_left.mp (h.boundary_disjoint j) hvB (X.2 hvX))
  · intro hv
    exact mem_inter.mpr ⟨mem_union_left _ hv,hS hv⟩

theorem boundary_not_mem_branchChoice (h : Partition G B A)
    (j : J) (X : BranchChoice A j) {u : V} (huB : u∈B) : u∉X.1 := by
  intro hu
  exact Finset.disjoint_left.mp (h.boundary_disjoint j) huB (X.2 hu)

/-- Internal rows are independent of the arbitrary boundary lift as well. -/
theorem internal_boundary_lift (h : Partition G B A) (j : J)
    (f : privateIndex G B A j → ℝ) (l : boundaryIndex G B → ℝ)
    (r : InternalRow G B A j) :
    delta (branchWithLift h j f l) r.1.1.1.1 r.1.1.1.2 r.1.2.1=
      (rowData h).internal j r f := by
  rw [branchWithLift,delta_add]
  have hz : delta (boundaryFunctionMap h l) r.1.1.1.1 r.1.1.1.2 r.1.2.1=0 := by
    rcases r.2.1 with hu | hv
    · have huB : r.1.1.1.1∉B := fun hb =>
        Finset.disjoint_left.mp (h.boundary_disjoint j) hb hu
      exact delta_zero_of_outside_mobius_support (boundaryFunction_supported h l)
        (ne_of_lt r.1.1.2.1) huB (context_left_not_mem r.1) (context_right_not_mem r.1)
    · have hvB : r.1.1.1.2∉B := fun hb =>
        Finset.disjoint_left.mp (h.boundary_disjoint j) hb hv
      rw [delta_comm r.1.1.1.1]
      exact delta_zero_of_outside_mobius_support (boundaryFunction_supported h l)
        (ne_of_gt r.1.1.2.1) hvB (context_right_not_mem r.1) (context_left_not_mem r.1)
  rw [hz,zero_add]
  rfl

/-- Every original lifted response is its private response plus the boundary
slack image, evaluated at the actual conditioning set. -/
theorem response_boundary_lift (h : Partition G B A) (j : J)
    (f : privateIndex G B A j → ℝ) (l : boundaryIndex G B → ℝ)
    (b : BoundaryRow G B) (X : BranchChoice A j) :
    delta (branchWithLift h j f l) b.1.1.1.1 b.1.1.1.2 (b.1.2.1∪X.1)=
      (rowData h).boundary l b+(rowData h).response j b X f := by
  have hu : b.1.1.1.1∉b.1.2.1∪X.1 := by
    simp only [mem_union,not_or]
    exact ⟨context_left_not_mem b.1,boundary_not_mem_branchChoice h j X b.2.1⟩
  have hv : b.1.1.1.2∉b.1.2.1∪X.1 := by
    simp only [mem_union,not_or]
    exact ⟨context_right_not_mem b.1,boundary_not_mem_branchChoice h j X b.2.2.1⟩
  rw [branchWithLift,delta_add,
    delta_inter_mobius_support (boundaryFunction_supported h l) (ne_of_lt b.1.1.2.1) hu hv,
    branchChoice_union_inter_boundary h b.2.2.2 j X]
  rfl

def liftedConditionalMin (h : Partition G B A)
    (f : ∀ j,privateIndex G B A j → ℝ) (l : J → boundaryIndex G B → ℝ)
    (j : J) (b : BoundaryRow G B) : ℝ :=
  univ.inf' univ_nonempty (fun X : BranchChoice A j =>
    delta (branchWithLift h j (f j) (l j)) b.1.1.1.1 b.1.1.1.2 (b.1.2.1∪X.1))

/-- Conditional minima transform by precisely the same boundary image. -/
theorem liftedConditionalMin_eq (h : Partition G B A)
    (f : ∀ j,privateIndex G B A j → ℝ) (l : J → boundaryIndex G B → ℝ)
    (j : J) (b : BoundaryRow G B) :
    liftedConditionalMin h f l j b=conditionalMin h f j b+(rowData h).boundary (l j) b := by
  apply le_antisymm
  · obtain ⟨X,hX⟩ := conditionalMin_attained h f j b
    have hle := Finset.inf'_le (s := univ)
      (fun X : BranchChoice A j =>
        delta (branchWithLift h j (f j) (l j)) b.1.1.1.1 b.1.1.1.2 (b.1.2.1∪X.1))
      (mem_univ X)
    rw [response_boundary_lift,hX,add_comm] at hle
    exact hle
  · apply Finset.le_inf'
    intro X hX
    rw [response_boundary_lift]
    have hh := conditionalMin_le h f j b X
    linarith

/-- The minimizing subsets, and hence every private minimizer-difference
row in the paper, are unchanged by arbitrary boundary lifts. -/
theorem lifted_minimizer_iff (h : Partition G B A)
    (f : ∀ j,privateIndex G B A j → ℝ) (l : J → boundaryIndex G B → ℝ)
    (j : J) (b : BoundaryRow G B) (X : BranchChoice A j) :
    delta (branchWithLift h j (f j) (l j)) b.1.1.1.1 b.1.1.1.2 (b.1.2.1∪X.1)=
      liftedConditionalMin h f l j b ↔
      (rowData h).response j b X (f j)=conditionalMin h f j b := by
  rw [response_boundary_lift,liftedConditionalMin_eq]
  constructor <;> intro he <;> linarith

/-- The quotient response map is literally independent of every boundary
lift; this proves the equivalence of the zero-lift presentation in the main
graphical gluing theorem with the paper's arbitrary branch functions. -/
theorem lifted_relationLinear_eq (h : Partition G B A)
    (f : ∀ j,privateIndex G B A j → ℝ) (l : J → boundaryIndex G B → ℝ) :
    (rowData h).relationLinear (liftedConditionalMin h f l)=
      (rowData h).relationLinear (conditionalMin h f) := by
  have he : liftedConditionalMin h f l=
      fun j b => conditionalMin h f j b+(rowData h).boundary (l j) b := by
    funext j b
    exact liftedConditionalMin_eq h f l j b
  rw [he]
  exact Gluing.relationLinear_boundary_lift (rowData h) (conditionalMin h f) l

/-- The closing relation for arbitrary lifted branches is exactly the
private-coordinate closing relation after transferring the same scaled
boundary lifts into the closing function. This uses the actual conditional
minima, not only their classes in the response quotient. -/
theorem lifted_closure_iff (h : Partition G B A)
    (f : ∀ j,privateIndex G B A j → ℝ) (l : J → boundaryIndex G B → ℝ)
    (z : boundaryIndex G B → ℝ) (lam : J → ℝ) :
    (rowData h).Closure (liftedConditionalMin h f l) z lam ↔
      (rowData h).Closure (conditionalMin h f) (z+∑ j,lam j • l j) lam := by
  have he (b : BoundaryRow G B) :
      (rowData h).boundary z b+∑ j,lam j*liftedConditionalMin h f l j b =
        (rowData h).boundary (z+∑ j,lam j • l j) b+
          ∑ j,lam j*conditionalMin h f j b := by
    simp only [liftedConditionalMin_eq,map_add,map_sum,map_smul,
      Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
      mul_add,Finset.sum_add_distrib]
    ring
  unfold Gluing.Data.Closure
  simp only [he]

/-- A prescribed private-coordinate closing function therefore works with
any chosen branch boundary lifts after the compensating subtraction. -/
theorem lifted_closure_transfer (h : Partition G B A)
    (f : ∀ j,privateIndex G B A j → ℝ) (l : J → boundaryIndex G B → ℝ)
    (z : boundaryIndex G B → ℝ) (lam : J → ℝ) :
    (rowData h).Closure (liftedConditionalMin h f l) (z-∑ j,lam j • l j) lam ↔
      (rowData h).Closure (conditionalMin h f) z lam := by
  rw [lifted_closure_iff,sub_add_cancel]

/-- The same assembled original function is obtained by transferring each
branch boundary lift into the closing boundary coordinate. -/
theorem assembled_boundary_lift_eq (h : Partition G B A)
    (f : ∀ j,privateIndex G B A j → ℝ) (l : J → boundaryIndex G B → ℝ)
    (z : boundaryIndex G B → ℝ) (lam : J → ℝ) :
    boundaryFunctionMap h z+∑ j,lam j • branchWithLift h j (f j) (l j)=
      globalFunctionMap h (Gluing.assemble (z+∑ j,lam j • l j) lam f) := by
  rw [function_decompose]
  simp only [branchWithLift,Gluing.assemble,map_add,map_sum,map_smul,smul_add,sum_add_distrib]
  abel

end Separator
end GraphicalZonotopes
