module

public import ToricPower.ArrangementPowerCells
public import ToricPower.ArrangementCartierDiagram
public import ToricPower.DivisorWeightPowerNaturality
public import ToricPower.DivisorWeightAdditive

/-!
# The full power decomposition of the normalized dual labels

The paper's normalized line label is `L(x) ⊗ O(boundary)`; its inverse
has ray coefficient `ceil(<x,v>)-1`.  The boundary correction makes its
power summands exactly the inverse-branch labels, including points on
integer walls.  Negative representatives enumerate all lattice residues
while keeping every branch inside the normalized cell domain.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays

/-- The opposite basis enumerates negative representatives of every
character residue; it is still a basis of the entire character lattice. -/
def negativeCharacterBasis : Module.Basis (Fin n) ℤ (N →+ ℤ) :=
  basis.map (LinearEquiv.neg ℤ)

theorem negativeCharacterBasis_character (a : Fin n → ℤ) :
    (negativeCharacterBasis basis).equivFun.symm a = -basis.equivFun.symm a := by
  rw [negativeCharacterBasis, Module.Basis.map_equivFun]
  rfl

/-- Coefficients of the inverse of the actual boundary-normalized line. -/
def normalizedDualCartierCoefficients (c : IncidenceObject A) : fan.Ray → ℤ :=
  fun ρ => -diagonalRightCoefficients fan basis rays c.2 ρ - 1

/-- The coefficients are literally the negative of the original label
plus the boundary divisor, not an independently chosen replacement. -/
theorem normalizedDualCartierCoefficients_eq (c : IncidenceObject A) :
    normalizedDualCartierCoefficients fan basis rays c =
      -(diagonalRightCoefficients fan basis rays c.2 + fun _ => 1) := by
  funext ρ
  simp [normalizedDualCartierCoefficients, sub_eq_add_neg, add_comm]

/-- Exact divisor coefficients for every actual inverse residue branch. -/
theorem normalizedDualCartier_residue (ell : ℕ) (positive : 0 < ell)
    (r : LatticeResidues (Fin n) ell) (c : IncidenceObject A) :
    toricResidueCoefficients fan (normalizedDualCartierCoefficients fan basis rays c) ell
      (-basis.equivFun.symm (latticeResidueRepresentative r)) =
        normalizedDualCartierCoefficients fan basis rays
          (normalizedPowerBranch A ell positive r c) := by
  funext ρ
  have ceiling := normalizedPowerBranch_ceiling A ell positive r c (.inl (rays.symm ρ))
  have pairing : augmentedLatticePairing A (latticeResidueRepresentative r)
      (.inl (rays.symm ρ)) =
      basis.equivFun.symm (latticeResidueRepresentative r) (fanRayPrimitiveGenerator fan ρ) :=
    fanArrangementMatrix_character fan basis rays (latticeResidueRepresentative r) ρ
  simp only [toricResidueCoefficients, normalizedDualCartierCoefficients,
    diagonalRightCoefficients, neg_neg, AddMonoidHom.neg_apply]
  rw [ceiling, pairing]
  simp only [sub_eq_add_neg]
  omega

/-- The actual normalized dual Cartier line. -/
def normalizedDualCartierLine (c : IncidenceObject A) : fan.algebraicRealization.Modules := by
  letI := toricSchemeIntegral fan nonempty
  exact (invariantCartierDivisor fan nonempty regular
    (normalizedDualCartierCoefficients fan basis rays c)).sheaf

/-- The full global sheaf decomposition of every normalized dual label.
All `ell^n` character residues are present, without a wall exception. -/
def normalizedDualCartierPowerSplitting (ell : ℕ) (positive : 0 < ell)
    (c : IncidenceObject A) :
    (Scheme.Modules.pushforward (toricPowerMap fan ell)).obj
      (normalizedDualCartierLine fan nonempty regular basis rays c) ≅
        ⨁ (fun r : LatticeResidues (Fin n) ell =>
          normalizedDualCartierLine fan nonempty regular basis rays
            (normalizedPowerBranch A ell positive r c)) := by
  letI := toricSchemeIntegral fan nonempty
  refine toricPowerInvariantCartierSplitting fan nonempty regular
      (negativeCharacterBasis basis) (normalizedDualCartierCoefficients fan basis rays c)
      ell positive ≪≫ biproduct.mapIso (fun r => eqToIso ?_)
  change (invariantCartierDivisor fan nonempty regular
    (toricResidueCoefficients fan (normalizedDualCartierCoefficients fan basis rays c) ell
      ((negativeCharacterBasis basis).equivFun.symm (latticeResidueRepresentative r)))).sheaf =
    (invariantCartierDivisor fan nonempty regular
      (normalizedDualCartierCoefficients fan basis rays
        (normalizedPowerBranch A ell positive r c))).sheaf
  rw [negativeCharacterBasis_character, normalizedDualCartier_residue]

end ToricPower

end
