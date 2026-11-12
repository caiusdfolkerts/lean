module

public import ToricPower.ArrangementUniversalCover
public import ToricPower.ArrangementPowerIncidenceCoordinates
public import ToricPower.WeightedIncidenceLift
public import ToricPower.LatticeResidueProjection

/-!
# The exact geometric meaning of every lifted inverse-power branch

The weighted cell `(c,m)` means `c−m`. For an arbitrary integral
translation `u`, Euclidean division of `m−u` supplies the finite residue
and integral quotient. The resulting weighted branch is proved to be
exactly the original arrangement cell containing `(c−m+u)/ell`.
The comparison is natural on the full universal face category.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Functor Set

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (ell : ℕ) (positive : 0 < ell)
  (u : Fin n → ℤ)

local notation "W" => WeightedIncidenceObject A
local notation "B" => powerResidueFunctor A ell positive

/-- Residue covariance retains the literal incidence translation. -/
theorem weightedPowerResidue_map {c d : W} (f : c ⟶ d) :
    latticeResidueTranslate ell positive f.val.val
        (latticeResidueOf ell positive (c.2-u)) =
      latticeResidueOf ell positive (d.2-u) := by
  have equal : d.2-u = (c.2-u)+f.val.val :=
    (congrArg (fun m : Fin n → ℤ => m-u) f.property).trans (by abel)
  exact (latticeResidueOf_add ell positive (c.2-u) f.val.val).symm.trans
    (congrArg (latticeResidueOf ell positive) equal.symm)

/-- The quotient changes by exactly the original power-incidence carry. -/
theorem weightedPowerQuotient_map {c d : W} (f : c ⟶ d) :
    latticeQuotientOf ell positive (d.2-u) = latticeQuotientOf ell positive (c.2-u) +
      latticeResidueCarry ell positive f.val.val (latticeResidueOf ell positive (c.2-u)) := by
  have equal : d.2-u = (c.2-u)+f.val.val :=
    (congrArg (fun m : Fin n → ℤ => m-u) f.property).trans (by abel)
  exact (congrArg (latticeQuotientOf ell positive) equal).trans
    (latticeQuotientOf_add ell positive (c.2-u) f.val.val)

def weightedPowerCoverLift : W ⥤ PowerIncidenceObject A ell positive where
  obj c := (B).elementsMk c.1 (latticeResidueOf ell positive (c.2-u))
  map f := ⟨f.val,weightedPowerResidue_map A ell positive u f⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- All integral carries are retained in the universal branch. -/
def weightedPowerBranchFunctor : W ⥤ W :=
  weightedIncidenceFunctorLift A
    (weightedPowerCoverLift A ell positive u ⋙ powerBranchFunctor A ell positive)
    (fun c => latticeQuotientOf ell positive (c.2-u)) (by
      intro c d f
      dsimp only [Functor.comp_map]
      rw [powerBranchFunctor_map_val]
      exact weightedPowerQuotient_map A ell positive u f)

/-- The quotient cell functor is the original branch functor, including
its actual carry characters. -/
def weightedPowerBranchProjectionIso :
    weightedPowerBranchFunctor A ell positive u ⋙ weightedToElements A ⋙
        Elements.π (universalWeightFunctor A) ≅
      weightedPowerCoverLift A ell positive u ⋙ powerBranchFunctor A ell positive :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intros
    simp only [Iso.refl_hom,Category.id_comp,Category.comp_id]
    rfl)

/-- This is an identity of actual cells, including all equality walls
and the resulting intrinsic dimensions. -/
theorem weightedPowerBranch_actualCell (c : W) :
    weightedIncidenceCellEquiv A ((weightedPowerBranchFunctor A ell positive u).obj c) =
      powerInverseBranchCell A ell u (weightedIncidenceCellEquiv A c) := by
  let r := latticeResidueOf ell positive (c.2-u)
  let t := latticeQuotientOf ell positive (c.2-u)
  let p := cellCenter (augmentedForms A) c.1.2.val
  have division : c.2-u = latticeResidueRepresentative r + (ell : ℤ) • t :=
    latticeResidueOf_reconstruct ell positive (c.2-u)
  have carry : latticeResidueRepresentative r + (-c.2) =
      (-u) + (ell : ℤ) • (-t) := by
    have h : c.2 = (latticeResidueRepresentative r + (ell : ℤ) • t) + u :=
      sub_eq_iff_eq_add.mp division
    rw [h,smul_neg]
    abel
  have identity : powerInverseBranchPoint ell u (p+latticeLift (-c.2)) =
      powerInverseBranchPoint ell (-latticeResidueRepresentative r) p + latticeLift (-t) := by
    simpa only [neg_neg] using powerInverseBranchPoint_carry ell positive
      (latticeResidueRepresentative r) (-u) (-c.2) (-t) carry p
  have source : p+latticeLift (-c.2) ∈ cell (augmentedForms A)
      (weightedIncidenceCellEquiv A c).2.val.1
      (weightedIncidenceCellEquiv A c).2.val.2 :=
    (add_mem_cell_iff _ _ _ _ _ (augmentedForms_latticeLift A (-c.2)) p).mpr
      (cellCenter_mem _ c.1.2.val)
  have left := powerInverseBranchCell_mem A ell positive u
    (weightedIncidenceCellEquiv A c) source
  rw [identity] at left
  have base : powerInverseBranchPoint ell (-latticeResidueRepresentative r) p ∈
      cell (augmentedForms A) (normalizedPowerBranch A ell positive r c.1).2.val.val.1
        (normalizedPowerBranch A ell positive r c.1).2.val.val.2 :=
    powerInverseBranchCell_mem A ell positive (-latticeResidueRepresentative r)
      ⟨c.1.1,c.1.2.val⟩ (cellCenter_mem _ c.1.2.val)
  have right : powerInverseBranchPoint ell (-latticeResidueRepresentative r) p + latticeLift (-t) ∈
      cell (augmentedForms A)
        (weightedIncidenceCellEquiv A ((weightedPowerBranchFunctor A ell positive u).obj c)).2.val.1
        (weightedIncidenceCellEquiv A ((weightedPowerBranchFunctor A ell positive u).obj c)).2.val.2 :=
    (add_mem_cell_iff _ _ _ _ _ (augmentedForms_latticeLift A (-t))
      (powerInverseBranchPoint ell (-latticeResidueRepresentative r) p)).mpr base
  apply universalIncidenceLabels_injective A
  obtain ⟨ceilings,active⟩ := cell_indices_unique (augmentedForms A) right left
  exact Prod.ext ceilings active

/-- The complete categorical comparison with the actual affine inverse
branch on the universal arrangement. -/
def weightedPowerBranchGeometricIso :
    weightedPowerBranchFunctor A ell positive u ⋙ weightedIncidenceToCells A ≅
      weightedIncidenceToCells A ⋙ powerInverseBranchFunctor A ell positive u :=
  NatIso.ofComponents
    (fun c => eqToIso (weightedPowerBranch_actualCell A ell positive u c))
    (by intros; exact Subsingleton.elim _ _)

end ToricPower.IntegralArrangement

end
