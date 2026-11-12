module

public import ToricPower.DualDiagonalFramedResolution
public import ToricPower.DualDiagonalToricWeights
public import ToricPower.DiagonalToricAugmentation

/-!
# The affine boundary frame of the genuine toric dual diagonal

On the intersection cone, a character taking value one on every ray is
a Cartier equation for the boundary divisor. Translating a supported
weight `u` by that character identifies it with an ordinary regular
intersection monomial. The complete module isomorphism retains the actual
product-chart ring map. This is an affine frame, not a claim that the
boundary divisor is globally trivial.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement
open scoped Classical

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {latticeMap : N →+ V}
  (fan : Fan latticeMap) (regular : fan.IsRegular) {n s : ℕ}
  (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ τ : fan.cones)
  (q : N →+ ℤ)
  (hq : ∀ ρ : fan.Ray, ρ.toCone ≤ σ ⊓ τ → q (fanRayPrimitiveGenerator fan ρ) = 1)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "S" => fanConeRaySet fan rays σ
local notation "T" => fanConeRaySet fan rays τ
local notation "R" => DiagonalChartRing ℂ A S T

include regular hq

/-- The actual boundary monomial inequalities become the ordinary
regular inequalities after multiplication by the chosen Cartier equation. -/
theorem fan_dualDiagonalStrip_shifted_iff (u : Fin n → ℤ) :
    (dualDiagonalStrip A S T u).Nonempty ↔
      basis.equivFun.symm (u + basis.equivFun q) ∈
        dualSemigroup fan.lattice (σ.val ⊓ τ.val) := by
  rw [fan_dualDiagonalStrip_nonempty_iff fan regular basis rays σ τ]
  change (∀ ρ : fan.Ray, ρ.toCone ≤ σ ⊓ τ →
    -1 ≤ basis.equivFun.symm u (fanRayPrimitiveGenerator fan ρ)) ↔
    basis.equivFun.symm (u + basis.equivFun q) ∈ dualSemigroup fan.lattice (σ ⊓ τ).val
  rw [← fan_rayCharacterMonoid_iff fan basis rays (σ ⊓ τ)]
  change (∀ ρ : fan.Ray, ρ.toCone ≤ σ ⊓ τ →
    -1 ≤ basis.equivFun.symm u (fanRayPrimitiveGenerator fan ρ)) ↔
    ∀ i ∈ fanConeRaySet fan rays (σ ⊓ τ), 0 ≤ rayPairing A (u+basis.equivFun q) i
  constructor
  · intro allowed i hi
    have bound := allowed (rays i) hi
    have evaluation := fanArrangementMatrix_character fan basis rays u (rays i)
    simp only [Equiv.symm_apply_apply] at evaluation
    rw [rayPairing_add, fanArrangementMatrix_basis_character, evaluation, hq (rays i) hi]
    omega
  · intro allowed ρ hρ
    have member : rays.symm ρ ∈ fanConeRaySet fan rays (σ ⊓ τ) := by
      change (rays (rays.symm ρ)).toCone ≤ σ ⊓ τ
      rw [Equiv.apply_symm_apply]
      exact hρ
    have bound := allowed (rays.symm ρ) member
    rw [rayPairing_add, fanArrangementMatrix_basis_character,
      Equiv.apply_symm_apply, hq ρ hρ,
      fanArrangementMatrix_character fan basis rays u ρ] at bound
    omega

/-- The full actual support, expressed in one boundary Cartier frame. -/
def dualDiagonalBoundaryFrameWeightEquiv :
    DualDiagonalBoundaryWeight A S T ≃ DiagonalSupportedWeight A S T where
  toFun u := ⟨u.val + basis.equivFun q,
    (fan_diagonalStrip_nonempty_iff fan basis rays σ τ _).mpr
      ((fan_dualDiagonalStrip_shifted_iff fan regular basis rays σ τ q hq u.val).mp u.property)⟩
  invFun u := ⟨u.val - basis.equivFun q,
    (fan_dualDiagonalStrip_shifted_iff fan regular basis rays σ τ q hq _).mpr (by
      rw [sub_add_cancel]
      exact (fan_diagonalStrip_nonempty_iff fan basis rays σ τ u.val).mp u.property)⟩
  left_inv u := by apply Subtype.ext; change u.val + basis.equivFun q - basis.equivFun q = u.val; abel
  right_inv u := by apply Subtype.ext; change u.val - basis.equivFun q + basis.equivFun q = u.val; abel

/-- The character-frame shift commutes with the actual monomial action. -/
theorem dualDiagonalBoundaryFrameWeightEquiv_translate
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T)
    (u : DualDiagonalBoundaryWeight A S T) :
    dualDiagonalBoundaryFrameWeightEquiv fan regular basis rays σ τ q hq
        (dualDiagonalBoundaryTranslate A S T p u) =
      diagonalSupportedWeightTranslate A S T p
        (dualDiagonalBoundaryFrameWeightEquiv fan regular basis rays σ τ q hq u) := by
  apply Subtype.ext
  change (u.val+p.1.val+p.2.val)+basis.equivFun q =
    (u.val+basis.equivFun q)+p.1.val+p.2.val
  abel

def dualDiagonalBoundaryFrameCoefficients :
    DualDiagonalBoundaryCoefficients A S T ℂ ≃ₗ[ℂ] DiagonalChartHZero ℂ A S T :=
  Finsupp.domLCongr (dualDiagonalBoundaryFrameWeightEquiv fan regular basis rays σ τ q hq)

@[simp]
theorem dualDiagonalBoundaryFrameCoefficients_single (u : DualDiagonalBoundaryWeight A S T) (r : ℂ) :
    dualDiagonalBoundaryFrameCoefficients fan regular basis rays σ τ q hq (Finsupp.single u r) =
      Finsupp.single (dualDiagonalBoundaryFrameWeightEquiv fan regular basis rays σ τ q hq u) r :=
  Finsupp.equivMapDomain_single _ _ _

/-- Exact module compatibility, proved first on actual monomials and
then on arbitrary finite polynomial coefficients. -/
theorem dualDiagonalBoundaryFrameCoefficients_smul (r : R)
    (v : DualDiagonalBoundaryCoefficients A S T ℂ) :
    dualDiagonalBoundaryFrameCoefficients fan regular basis rays σ τ q hq (r • v) =
      r • dualDiagonalBoundaryFrameCoefficients fan regular basis rays σ τ q hq v := by
  have monomial (p : rayCharacterMonoid A S × rayCharacterMonoid A T) (a : ℂ)
      (v : DualDiagonalBoundaryCoefficients A S T ℂ) :
      dualDiagonalBoundaryFrameCoefficients fan regular basis rays σ τ q hq
        (AddMonoidAlgebra.single p a • v) =
      AddMonoidAlgebra.single p a •
        dualDiagonalBoundaryFrameCoefficients fan regular basis rays σ τ q hq v := by
    induction v using Finsupp.induction with
    | zero => simp
    | single_add u b v _ _ ih =>
        rw [smul_add, map_add, map_add, smul_add, ih]
        congr 1
        rw [dualDiagonalBoundary_single_smul_single, dualDiagonalBoundaryFrameCoefficients_single,
          dualDiagonalBoundaryFrameCoefficients_single, diagonalChartHZero_single_smul,
          Finsupp.mapDomain_single, Finsupp.smul_single]
        simp only [smul_eq_mul]
        exact congrArg (fun w => Finsupp.single w (a*b))
          (dualDiagonalBoundaryFrameWeightEquiv_translate fan regular basis rays σ τ q hq p u)
  induction r using AddMonoidAlgebra.induction with
  | zero => simp
  | single_add p a r _ _ ih =>
      rw [add_smul, map_add, add_smul, monomial, ih]

/-- The actual boundary module in this Cartier frame is the actual
intersection coordinate module, with its original product-chart scalars. -/
def dualDiagonalBoundaryFrameModuleIso :
    dualDiagonalBoundaryModule A S T ℂ ≅ diagonalIntersectionModule fan basis rays σ τ :=
  (show DualDiagonalBoundaryCoefficients A S T ℂ ≃ₗ[R] DiagonalChartHZero ℂ A S T from
    { toAddEquiv := (dualDiagonalBoundaryFrameCoefficients fan regular basis rays σ τ q hq).toAddEquiv
      map_smul' := dualDiagonalBoundaryFrameCoefficients_smul fan regular basis rays σ τ q hq }).toModuleIso ≪≫
    diagonalIntersectionModuleIso fan basis rays σ τ

end ToricPower
