module

public import ToricPower.ArrangementFaceIntersections
public import ToricPower.CeilingPowerArithmetic
public import ToricPower.DivisorWeightAlgebra

/-!
# Actual inverse-power branches on arrangement cells

An inverse branch sends a point `x` to `(x+z)/ell`.  The original
arrangement is not preserved by forward dilation.  Instead, each inverse
branch of a cell lies in one uniquely determined cell of the original
arrangement.  Its active walls are exactly the original active walls
whose translated integral value is divisible by `ell`.

The resulting map is a functor on the actual universal face category.
Negative residue representatives keep inverse branches of normalized
cells normalized, retaining every residue and every Laurent direction.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Set

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)

/-- An actual affine inverse branch of the positive power map. -/
def powerInverseBranchPoint (ell : ℕ) (z : Fin n → ℤ) (x : Fin n → ℝ) : Fin n → ℝ :=
  (ell : ℝ)⁻¹ • (x + latticeLift z)

theorem powerInverseBranchPoint_continuous (ell : ℕ) (z : Fin n → ℤ) :
    Continuous (powerInverseBranchPoint ell z) := by
  unfold powerInverseBranchPoint
  fun_prop

theorem augmentedForms_powerInverseBranchPoint (ell : ℕ) (z : Fin n → ℤ)
    (x : Fin n → ℝ) (j : Fin s ⊕ Fin n) :
    augmentedForms A j (powerInverseBranchPoint ell z x) =
      (augmentedForms A j x + (augmentedLatticePairing A z j : ℝ)) / (ell : ℝ) := by
  simp only [powerInverseBranchPoint, map_smul, map_add, augmentedForms_latticeLift,
    smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem integral_value_iff_exists_integer (x : ℝ) :
    x = (⌈x⌉ : ℝ) ↔ ∃ z : ℤ, x = z := by
  refine ⟨fun h => ⟨⌈x⌉,h⟩, ?_⟩
  rintro ⟨z,rfl⟩
  simp

/-- The exact ceiling labels on an inverse branch of any actual cell. -/
theorem inverseBranch_ceilingVector (ell : ℕ) (positive : 0 < ell)
    (z : Fin n → ℤ) {e : Fin s ⊕ Fin n → ℤ} {I : Set (Fin s ⊕ Fin n)}
    {x : Fin n → ℝ} (hx : x ∈ cell (augmentedForms A) e I) :
    ceilingVector (augmentedForms A) (powerInverseBranchPoint ell z x) =
      fun j => (e j - 1 + augmentedLatticePairing A z j) / (ell : ℤ) + 1 := by
  funext j
  rw [ceilingVector, augmentedForms_powerInverseBranchPoint,
    ToricPower.ceil_scaled_translate _ _ ell positive,
    ceil_eq_of_mem_cell _ _ _ hx]

/-- No equality wall is lost: divisibility determines precisely which
active walls survive an inverse branch. -/
theorem inverseBranch_integralIndices (ell : ℕ) (positive : 0 < ell)
    (z : Fin n → ℤ) {e : Fin s ⊕ Fin n → ℤ} {I : Set (Fin s ⊕ Fin n)}
    {x : Fin n → ℝ} (hx : x ∈ cell (augmentedForms A) e I) :
    integralIndices (augmentedForms A) (powerInverseBranchPoint ell z x) =
      {j | j ∈ I ∧ (ell : ℤ) ∣ e j + augmentedLatticePairing A z j} := by
  ext j
  change _ = (⌈_⌉ : ℝ) ↔ _
  rw [integral_value_iff_exists_integer, augmentedForms_powerInverseBranchPoint,
    ToricPower.scaled_translate_is_integer_iff _ _ ell positive]
  constructor
  · rintro ⟨q,hq,divisible⟩
    have equality : q = e j := by
      simpa only [hq, Int.ceil_intCast] using ceil_eq_of_mem_cell _ _ _ hx j
    subst q
    refine ⟨?_,divisible⟩
    rw [← integralIndices_eq_of_mem_cell _ _ _ hx]
    change augmentedForms A j x = (⌈augmentedForms A j x⌉ : ℝ)
    rw [hq, Int.ceil_intCast]
  · rintro ⟨active,divisible⟩
    exact ⟨e j, by simpa only [if_pos active] using hx j, divisible⟩

/-- The literal original cell containing the inverse branch of a cell. -/
def powerInverseBranchCell (ell : ℕ) (z : Fin n → ℤ)
    (c : UniversalIncidenceObject A) : UniversalIncidenceObject A :=
  universalIncidenceOfPoint A
    (powerInverseBranchPoint ell z (cellCenter (augmentedForms A) c.2))

/-- Every point of the original cell has the same branch-cell labels. -/
theorem powerInverseBranchCell_mem (ell : ℕ) (positive : 0 < ell)
    (z : Fin n → ℤ) (c : UniversalIncidenceObject A)
    {x : Fin n → ℝ} (hx : x ∈ cell (augmentedForms A) c.2.val.1 c.2.val.2) :
    powerInverseBranchPoint ell z x ∈ cell (augmentedForms A)
      (powerInverseBranchCell A ell z c).2.val.1
      (powerInverseBranchCell A ell z c).2.val.2 := by
  change powerInverseBranchPoint ell z x ∈ cell (augmentedForms A)
    (ceilingVector (augmentedForms A)
      (powerInverseBranchPoint ell z (cellCenter (augmentedForms A) c.2)))
    (integralIndices (augmentedForms A)
      (powerInverseBranchPoint ell z (cellCenter (augmentedForms A) c.2)))
  rw [inverseBranch_ceilingVector A ell positive z (cellCenter_mem _ c.2),
    inverseBranch_integralIndices A ell positive z (cellCenter_mem _ c.2),
    ← inverseBranch_ceilingVector A ell positive z hx,
    ← inverseBranch_integralIndices A ell positive z hx]
  exact mem_cell_self _ _

/-- The whole closed polyhedron maps into the closed branch cell. -/
theorem powerInverseBranchCell_closed (ell : ℕ) (positive : 0 < ell)
    (z : Fin n → ℤ) (c : UniversalIncidenceObject A) :
    MapsTo (powerInverseBranchPoint ell z) (universalIncidenceClosedCell A c)
      (universalIncidenceClosedCell A (powerInverseBranchCell A ell z c)) := by
  have contained : cell (augmentedForms A) c.2.val.1 c.2.val.2 ⊆
      powerInverseBranchPoint ell z ⁻¹'
        universalIncidenceClosedCell A (powerInverseBranchCell A ell z c) := by
    intro x hx
    exact cell_subset_closedCell _ _ _ (powerInverseBranchCell_mem A ell positive z c hx)
  have closed : IsClosed (powerInverseBranchPoint ell z ⁻¹'
      universalIncidenceClosedCell A (powerInverseBranchCell A ell z c)) :=
    (closedCell_isClosed _ (fun j => (augmentedForms A j).continuous_of_finiteDimensional)
      _ _).preimage (powerInverseBranchPoint_continuous ell z)
  have h := closure_minimal contained closed
  rw [closure_cell _ (fun j => (augmentedForms A j).continuous_of_finiteDimensional)
    _ _ c.2.property.1] at h
  exact h

/-- True face inclusions remain face inclusions after branch coarsening. -/
theorem powerInverseBranchCell_monotone (ell : ℕ) (positive : 0 < ell)
    (z : Fin n → ℤ) : Monotone (powerInverseBranchCell A ell z) := by
  intro c d contained
  have center : cellCenter (augmentedForms A) c.2 ∈ universalIncidenceClosedCell A d :=
    contained (cell_subset_closedCell _ _ _ (cellCenter_mem _ c.2))
  exact closedCell_of_point_subset _ _ _
    (powerInverseBranchCell_closed A ell positive z d center)

/-- The inverse branch is a genuine functor on all universal arrangement cells. -/
def powerInverseBranchFunctor (ell : ℕ) (positive : 0 < ell) (z : Fin n → ℤ) :
    UniversalIncidenceObject A ⥤ UniversalIncidenceObject A where
  obj := powerInverseBranchCell A ell z
  map f := homOfLE (powerInverseBranchCell_monotone A ell positive z f.le)

/-- Negative representatives of every residue keep the branch inside
the original normalized fundamental cube. -/
theorem negativeResidueBranch_normalized (ell : ℕ) (positive : 0 < ell)
    (r : LatticeResidues (Fin n) ell) (c : IncidenceObject A) :
    coordinateCeilings A
      (powerInverseBranchCell A ell (-latticeResidueRepresentative r)
        ⟨c.1,c.2.val⟩).2 = 0 := by
  funext j
  change ceilingVector (augmentedForms A)
    (powerInverseBranchPoint ell (-latticeResidueRepresentative r)
      (cellCenter (augmentedForms A) c.2.val)) (.inr j) = 0
  rw [inverseBranch_ceilingVector A ell positive _ (cellCenter_mem _ c.2.val)]
  have coordinate : c.2.val.val.1 (.inr j) = 0 := congrFun c.2.property j
  simp only [coordinate, augmentedLatticePairing_neg, Pi.neg_apply,
    augmentedLatticePairing_inr, latticeResidueRepresentative, zero_sub]
  have positiveInt : (0 : ℤ) < ell := by exact_mod_cast positive
  have bound : ((r j).val : ℤ) < ell := by exact_mod_cast (r j).isLt
  have division : (-1 + -((r j).val : ℤ)) / (ell : ℤ) = -1 :=
    (Int.ediv_eq_iff_of_pos positiveInt).mpr ⟨by omega, by omega⟩
  omega

/-- The actual normalized cell of each inverse residue branch. Its
dimension is determined by its actual active walls, and may increase. -/
def normalizedPowerBranch (ell : ℕ) (positive : 0 < ell)
    (r : LatticeResidues (Fin n) ell) (c : IncidenceObject A) : IncidenceObject A :=
  ⟨(powerInverseBranchCell A ell (-latticeResidueRepresentative r) ⟨c.1,c.2.val⟩).1,
    ⟨(powerInverseBranchCell A ell (-latticeResidueRepresentative r) ⟨c.1,c.2.val⟩).2,
      negativeResidueBranch_normalized A ell positive r c⟩⟩

/-- The full ceiling vector of the normalized branch, including the
auxiliary coordinate hyperplanes. -/
theorem normalizedPowerBranch_ceiling (ell : ℕ) (positive : 0 < ell)
    (r : LatticeResidues (Fin n) ell) (c : IncidenceObject A) (j : Fin s ⊕ Fin n) :
    (normalizedPowerBranch A ell positive r c).2.val.val.1 j =
      (c.2.val.val.1 j - 1 - augmentedLatticePairing A (latticeResidueRepresentative r) j) /
        (ell : ℤ) + 1 := by
  simpa only [normalizedPowerBranch, powerInverseBranchCell, universalIncidenceOfPoint,
    augmentedLatticePairing_neg, Pi.neg_apply, sub_eq_add_neg] using
    congrFun (inverseBranch_ceilingVector A ell positive (-latticeResidueRepresentative r)
      (cellCenter_mem (augmentedForms A) c.2.val)) j

end ToricPower.IntegralArrangement

end
