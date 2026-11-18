module

public import ToricPower.ArrangementToricMinimalCoface
public import ToricPower.ToricMonomialChartIsomorphism
public import ToricPower.DiagonalPulledCellularInclusions
public import ToricPower.DiagonalBoundaryNormalization
public import ToricPower.SchemeTensorFrameSections

/-!
# The original represented top coefficient is a unit on its chart

The top coface chosen at the integral minimal character attains equality
in every chart-ray inequality. Hence its actual inverse-right incidence
map is locally invertible. The original top augmentation generator is
then a composite of genuine isomorphisms on that chart.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "Cells" => IncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "Q" => arrangementDualLeftCartierDiagram fan nonempty regular basis rays
local notation "R" => arrangementDualRightCartierDiagram fan nonempty regular basis rays

local instance topCofaceChartBiproducts : HasFiniteBiproducts (X).Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The specified original negative-character incidence is invertible
on the actual cone chart selected in the minimal-weight construction. -/
theorem arrangementMinimalTopCoface_rightMap_restrict_isIso (σ : fan.cones) (c : Cells) :
    let p := arrangementMinimalTopCoface fan regular basis rays σ c
    IsIso ((Scheme.Modules.restrictFunctor (fan.affineToricChartι σ)).map ((R).map p.val.2)) := by
  letI := toricSchemeIntegral fan nonempty
  let p := arrangementMinimalTopCoface fan regular basis rays σ c
  have valid : ∀ ρ : fan.Ray,
      0 ≤ arrangementDualRightCoefficients fan basis rays ⟨n,p.val.1⟩ ρ -
        arrangementDualRightCoefficients fan basis rays c ρ +
          (-(basis.equivFun.symm p.val.2.val)) (fanRayPrimitiveGenerator fan ρ) := by
    intro ρ
    have h := (diagonalEntryRegular_of_incidence fan basis rays p.val.2).2 ρ
    change 0 ≤ -(diagonalRightCoefficients fan basis rays p.val.1 ρ) -
      -(diagonalRightCoefficients fan basis rays c.2 ρ) +
        (-(basis.equivFun.symm p.val.2.val)) (fanRayPrimitiveGenerator fan ρ)
    change 0 ≤ diagonalRightCoefficients fan basis rays c.2 ρ -
      diagonalRightCoefficients fan basis rays p.val.1 ρ -
        (basis.equivFun.symm p.val.2.val) (fanRayPrimitiveGenerator fan ρ) at h
    simp only [AddMonoidHom.neg_apply]
    omega
  have equal : ∀ ρ : fan.Ray, ρ.toCone ≤ σ →
      arrangementDualRightCoefficients fan basis rays ⟨n,p.val.1⟩ ρ -
        arrangementDualRightCoefficients fan basis rays c ρ +
          (-(basis.equivFun.symm p.val.2.val)) (fanRayPrimitiveGenerator fan ρ) = 0 := by
    intro ρ inside
    have hj : rays.symm ρ ∈ fanConeRaySet fan rays σ := by
      change (rays (rays.symm ρ)).toCone ≤ σ
      simpa only [Equiv.apply_symm_apply] using inside
    have ceiling := arrangementMinimalTopCoface_ceiling fan regular basis rays σ c
      (rays.symm ρ) hj
    change p.val.1.val.val.1 (.inl (rays.symm ρ)) =
      c.2.val.val.1 (.inl (rays.symm ρ)) + rayPairing A p.val.2.val (rays.symm ρ) at ceiling
    have value := fanArrangementMatrix_character fan basis rays p.val.2.val ρ
    simp only [arrangementDualRightCoefficients, Pi.neg_apply, diagonalRightCoefficients,
      neg_neg, AddMonoidHom.neg_apply]
    omega
  exact toricCartierMonomialMap_restrict_isIso fan regular
    (arrangementDualRightCoefficients fan basis rays c)
    (arrangementDualRightCoefficients fan basis rays ⟨n,p.val.1⟩)
    (-(basis.equivFun.symm p.val.2.val)) valid σ equal nonempty

/-- Tensoring the original incidence by the original left label keeps
its chart isomorphism, through the genuine restriction tensorator. -/
theorem arrangementMinimalTopCoface_tensorRightMap_restrict_isIso
    (σ : fan.cones) (c : Cells) :
    let p := arrangementMinimalTopCoface fan regular basis rays σ c
    IsIso ((Scheme.Modules.restrictFunctor (fan.affineToricChartι σ)).map
      (((Q).obj ⟨n,p.val.1⟩) ◁ (R).map p.val.2)) := by
  let p := arrangementMinimalTopCoface fan regular basis rays σ c
  let F := Scheme.Modules.restrictFunctor (fan.affineToricChartι σ)
  haveI := arrangementMinimalTopCoface_rightMap_restrict_isIso
    fan nonempty regular basis rays σ c
  haveI composite : IsIso (Functor.LaxMonoidal.μ F ((Q).obj ⟨n,p.val.1⟩) ((R).obj c) ≫
      F.map (((Q).obj ⟨n,p.val.1⟩) ◁ (R).map p.val.2)) := by
    rw [← Functor.LaxMonoidal.μ_natural_right]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (Functor.LaxMonoidal.μ F ((Q).obj ⟨n,p.val.1⟩) ((R).obj c)) _

/-- The actual original represented top coefficient, including its
original diagonal quotient, is invertible on the chosen chart. -/
theorem arrangementMinimalTopCoface_augmentationCoefficient_restrict_isIso
    (σ : fan.cones) (c : Cells) :
    let p := arrangementMinimalTopCoface fan regular basis rays σ c
    IsIso ((Scheme.Modules.restrictFunctor (fan.affineToricChartι σ)).map
      ((Cellular.vectorCopowerInclusion ℂ ((Q).obj ⟨n,p.val.1⟩)
          ((Cellular.representable ℂ c).obj ⟨n,p.val.1⟩) (ModuleCat.freeMk p.val.2) ≫
        arrangementCellularCochainInclusion A ℂ
          (Cellular.covariantCopowerDiagram ℂ Q (Cellular.representable ℂ c)) n p.val.1) ▷
            ((R).obj c) ≫
        singleAugmentationComponent
          (arrangementRepresentedTopAugmentation fan nonempty regular basis rays c))) := by
  let p := arrangementMinimalTopCoface fan regular basis rays σ c
  dsimp only
  erw [arrangementRepresentedTopAugmentation_generator]
  haveI := arrangementMinimalTopCoface_tensorRightMap_restrict_isIso
    fan nonempty regular basis rays σ c
  haveI := diagonalInverseCellPulledTopQuotient_isIso fan nonempty regular basis rays p.val.1
  simp only [Functor.map_comp]
  infer_instance

end ToricPower

end

