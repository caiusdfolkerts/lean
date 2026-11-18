module

public import ToricPower.DivisorWeightFrameCoordinates

/-!
# The affine residue basis in actual Cartier frames

The actual finite module equivalence sends each standard residue generator to
its prescribed regular monomial. These values identify its sheafification with
the canonical global rational-function residue maps.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric MonoidAlgebra

namespace ToricPower


universe u v

variable {N : Type u} {V : Type v} {κ : Type u}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V] [Fintype κ] {i : N →+ V}

/-- Each standard source generator maps to the normalized regular monomial,
with no restriction on the dimension of the cone. -/
theorem toricFramedResidueModuleIso_single (fan : Fan i) (regular : fan.IsRegular)
    (basis : Module.Basis κ ℤ (N →+ ℤ)) (b : fan.Ray → ℤ)
    (ell : ℕ) (hell : 0 < ell) (cone : fan.cones) (residue : LatticeResidues κ ell) :
    (toricFramedResidueModuleIso fan regular basis b ell hell cone).hom
        (Pi.single residue 1) =
      normalizedToricResidueMonomial fan regular b ell hell
        (basis.equivFun.symm (latticeResidueRepresentative residue)) cone := by
  classical
  let A := characterRayMatrix fan.lattice (fan.isToricCone cone.property) basis
  let B := coneDivisorCoefficients fan b cone
  let C := powerCoefficient A B (ell : ℤ) (latticeResidueRepresentative residue)
  let character := basis.equivFun.symm (latticeResidueRepresentative residue)
  let qD := basis.equivFun (coneDivisorCharacter fan regular b cone)
  let qC := basis.equivFun (coneDivisorCharacter fan regular
    (toricResidueCoefficients fan b ell character) cone)
  let e := affineToricRayChartRingEquiv fan.lattice (fan.isToricCone cone.property) basis
  have hD : B = rayMap A qD := by
    funext ρ
    simp only [A, B, qD, characterRayMatrix_apply, coneDivisorCharacter_ray]
  have hC : C = rayMap A qC := by
    have hc := toricResidueCoefficients_chart fan basis b ell character cone
    simp only [character, LinearEquiv.apply_symm_apply] at hc
    dsimp only [C, A, B]
    rw [← hc]
    funext ρ
    simp only [A, qC, character, characterRayMatrix_apply, coneDivisorCharacter_ray]
  let input := divisorCartierTrivialization ℂ A C qC hC 1
  let output := divisorResidueSummand ℂ A B ell hell residue input
  have evaluated :
      e ((toricFramedResidueModuleIso fan regular basis b ell hell cone).hom
        (Pi.single residue 1)) =
      (divisorCartierTrivialization ℂ A B qD hD).symm ⟨output.1, output.2⟩ := by
    change e (e.symm ((divisorCartierTrivialization ℂ A B qD hD).symm _)) = _
    rw [RingEquiv.apply_symm_apply]
    congr 1
    apply Subtype.ext
    change (divisorResidueSum ℂ A B ell hell _).1 = output.1
    apply congrArg Subtype.val
    change divisorResidueSum ℂ A B ell hell _ =
      divisorResidueSummand ℂ A B ell hell residue input
    rw [← divisorResidueSum_pi_single ℂ A B ell hell residue input]
    apply congrArg (divisorResidueSum ℂ A B ell hell)
    exact toricResidueFrameInput_single fan regular basis b ell cone residue hC

  apply e.injective
  rw [evaluated]
  apply mapDomain_injective (rayChartPowerMonoidHom_one_injective A)
  rw [divisorCartierTrivialization_symm_ambient]
  change rayPowerLaurentValue ℂ A ell output.1 * single (Multiplicative.ofAdd qD) 1 = _
  rw [divisorResidueSummand_cartier_generator]
  dsimp only [e]
  rw [normalizedToricResidueMonomial, affineToricRayChartRingEquiv_single,
    mapDomain_single]
  have exponents := (normalizedToricResidueCharacter_coordinates fan regular basis b ell
    residue cone).symm
  apply congrArg (fun m => single m (1 : ℂ))
  apply Multiplicative.toAdd.injective
  change cartierResidueExponent ell (latticeResidueRepresentative residue) qD qC =
    1 • basis.equivFun (normalizedToricResidueCharacter fan regular b ell character cone)
  simpa only [one_smul] using exponents

end ToricPower
