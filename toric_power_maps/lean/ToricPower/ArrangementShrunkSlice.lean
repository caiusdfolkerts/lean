module

public import ToricPower.AffineLatticeShrinking
public import ToricPower.ArrangementAffineSlice
public import ToricPower.ArrangementHalfStar
public import ToricPower.ArrangementPowerCells
public import ToricPower.CellularClosedExtension

/-!
# The exact slice selected by a small inverse-power branch

Inside the genuine open star of a cell, membership in that cell is
exactly the affine tangent equation. The integral compatibility in the
shrinking construction pulls this equation back to the prescribed
integral translate of the closed slice. The branch also gives a literal
functor from every supported source cell to the finite target face star.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set CategoryTheory

namespace ToricPower

section AffineEquation

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The compatibility equation controls the entire affine slice,
including its boundary; positive scaling does not change its direction. -/
theorem inverseScaling_mem_affineSlice_iff
    (V : Submodule ℝ E) (ell : ℕ) (positive : 0 < ell)
    (u m x v₀ z : E) (center : x-v₀ ∈ V)
    (compatible : u+m-(ell : ℝ) • v₀ ∈ V) :
    (ell : ℝ)⁻¹ • (z+u)-x ∈ V ↔ z-m ∈ V := by
  have nonzero : (ell : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt positive)
  have offset : u+m-(ell : ℝ) • x ∈ V := by
    convert V.sub_mem compatible (V.smul_mem (ell : ℝ) center) using 1
    rw [smul_sub]
    abel
  have equal : (ell : ℝ)⁻¹ • (z+u)-x =
      (ell : ℝ)⁻¹ • ((z-m)+(u+m-(ell : ℝ) • x)) := by
    rw [show (z-m)+(u+m-(ell : ℝ) • x) = (z+u)-(ell : ℝ) • x by abel,
      smul_sub,smul_smul,inv_mul_cancel₀ nonzero,one_smul]
  rw [equal,V.smul_mem_iff (inv_ne_zero nonzero),V.add_mem_iff_left offset]

end AffineEquation

namespace IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)

local notation "U" => UniversalIncidenceObject A

theorem universalIncidenceOfPoint_eq_iff (c : U) (x : Fin n → ℝ) :
    universalIncidenceOfPoint A x = c ↔
      x ∈ cell (augmentedForms A) c.2.val.1 c.2.val.2 := by
  constructor
  · intro equal
    rw [← equal]
    exact mem_cell_self _ x
  · intro inside
    apply universalIncidenceLabels_injective A
    exact Prod.ext (funext (fun j => ceil_eq_of_mem_cell _ _ _ inside j))
      (integralIndices_eq_of_mem_cell _ _ _ inside)

/-- In the actual local star, the inverse branch selects precisely
the original translated closed slice. -/
theorem inverseBranch_eq_cell_iff_affineSlice
    (c d : U) (selected : Set (Fin s ⊕ Fin n))
    (direction : cellDirection (augmentedForms A) c.2.val.2 =
      arrangementZeroSlice (augmentedForms A) selected)
    (ell : ℕ) (positive : 0 < ell) (u m v₀ : Fin n → ℤ)
    (center : cellCenter (augmentedForms A) c.2 - latticeLift v₀ ∈
      arrangementZeroSlice (augmentedForms A) selected)
    (compatible : latticeLift u + latticeLift m - (ell : ℝ) • latticeLift v₀ ∈
      arrangementZeroSlice (augmentedForms A) selected)
    (inside : powerInverseBranchPoint ell u (cellCenter (augmentedForms A) d.2) ∈
      localStar (augmentedForms A) (cellCenter (augmentedForms A) c.2)) :
    powerInverseBranchCell A ell u d = c ↔ universalAffineSliceSupport A selected m d := by
  rw [powerInverseBranchCell,universalIncidenceOfPoint_eq_iff,
    universalAffineSliceSupport_iff_center]
  have starCriterion := localStar_mem_cell_iff (augmentedForms A)
    (cellCenter (augmentedForms A) c.2) inside
  rw [cellCenter_ceilingVector,cellCenter_integralIndices,direction] at starCriterion
  exact starCriterion.trans (inverseScaling_mem_affineSlice_iff
    (arrangementZeroSlice (augmentedForms A) selected) ell positive
    (latticeLift u) (latticeLift m) (cellCenter (augmentedForms A) c.2)
    (latticeLift v₀) (cellCenter (augmentedForms A) d.2) center compatible)

/-- The actual branch on a supported subposet lands in the original
finite upper face star whenever the support has been shrunk into it. -/
def shrunkSupportFaceStar (c : U) (P : U → Prop)
    (ell : ℕ) (positive : 0 < ell) (u : Fin n → ℤ)
    (inside : ∀ d : U, P d →
      powerInverseBranchPoint ell u (cellCenter (augmentedForms A) d.2) ∈
        localStar (augmentedForms A) (cellCenter (augmentedForms A) c.2)) :
    {d : U // P d} ⥤ UniversalFaceStar A c where
  obj d := ⟨powerInverseBranchCell A ell u d.val,
    universalIncidenceOfPoint_mem_faceStar A c (inside d.val d.property)⟩
  map f := homOfLE (powerInverseBranchCell_monotone A ell positive u f.le)

/-- This is a factorization of the original branch functor, retaining
every genuine face incidence. -/
def shrunkSupportFaceStarProjectionIso (c : U) (P : U → Prop)
    (ell : ℕ) (positive : 0 < ell) (u : Fin n → ℤ)
    (inside : ∀ d : U, P d →
      powerInverseBranchPoint ell u (cellCenter (augmentedForms A) d.2) ∈
        localStar (augmentedForms A) (cellCenter (augmentedForms A) c.2)) :
    shrunkSupportFaceStar A c P ell positive u inside ⋙ universalFaceStarInclusion A c ≅
      Cellular.closedFaceInclusion P ⋙ powerInverseBranchFunctor A ell positive u :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; exact Subsingleton.elim _ _)

end IntegralArrangement

end ToricPower

end
