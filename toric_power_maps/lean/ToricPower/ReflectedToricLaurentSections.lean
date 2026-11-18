module

public import ToricPower.ArrangementQuasicoherentLabels
public import ToricPower.ArrangementLaurentLabels
public import ToricPower.ToricCartierSectionsLinear
public import ToricPower.CechToricMonomialSections
public import ToricPower.CechToricCover
public import ToricPower.DiagonalToricWeights

/-!
# The actual reflected Cartier diagram has the full Laurent coordinates

This identifies the genuine complex-linear affine sections of the
covariant Cartier labels with the independently specified Laurent
coefficient functor. Every integral character is retained. Naturality
uses the literal rational monomial map and its full character translation.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement
open scoped Classical

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "C" => IncidenceObject A

theorem reflectedLaurent_allowed_iff (c : C) (σ : fan.cones) (m : Fin n → ℤ) :
    (∀ j ∈ fanConeRaySet fan rays σ,
      0 ≤ rayPairing A m j + reflectedCeiling A c.2.val j) ↔
      toricCharacterAllowed fan (arrangementDualLeftCoefficients fan basis rays c)
        σ (basis.equivFun.symm m) := by
  constructor
  · intro allowed ρ contained
    have h := allowed (rays.symm ρ) (by
      change (rays (rays.symm ρ)).toCone ≤ σ
      simpa only [Equiv.apply_symm_apply] using contained)
    rw [arrangementDualLeftCoefficients_apply]
    have pairing := fanArrangementMatrix_character fan basis rays m ρ
    omega
  · intro allowed j contained
    have h := allowed (rays j) contained
    rw [arrangementDualLeftCoefficients_apply] at h
    rw [← fanArrangementMatrix_character fan basis rays m (rays j),
      Equiv.symm_apply_apply] at h
    omega

/-- Full numerical characters are precisely full intrinsic chart weights. -/
def reflectedToricWeightEquiv (c : C) (σ : fan.cones) :
    ReflectedLaurentWeight A (fanConeRaySet fan rays σ) c ≃
      ToricChartDivisorWeight fan (arrangementDualLeftCoefficients fan basis rays c) σ :=
  (Equiv.subtypeEquiv basis.equivFun.symm.toEquiv
    (fun m => reflectedLaurent_allowed_iff fan basis rays c σ m)).trans
      (toricChartWeightGlobalEquiv fan
        (arrangementDualLeftCoefficients fan basis rays c) σ).symm

@[simp]
theorem reflectedToricWeightEquiv_val (c : C) (σ : fan.cones)
    (m : ReflectedLaurentWeight A (fanConeRaySet fan rays σ) c) :
    (reflectedToricWeightEquiv fan basis rays c σ m).val = basis.equivFun.symm m.val := rfl

/-- The scalar structure on the target is the actual scheme base action. -/
def reflectedToricSectionsLinearEquiv (c : C) (σ : fan.cones) :
    (ReflectedLaurentWeight A (fanConeRaySet fan rays σ) c →₀ ℂ) ≃ₗ[ℂ]
      (FiniteCover.schemeBaseSections ℂ fan.algebraicRealization
        (fan.affineToricChartι σ).opensRange).obj
          (arrangementDualLeftSheaf fan nonempty regular basis rays c) := by
  letI := toricSchemeIntegral fan nonempty
  exact (Finsupp.domLCongr (R := ℂ) (reflectedToricWeightEquiv fan basis rays c σ)).trans
    (toricDivisorSectionCoefficientsLinearEquiv fan nonempty regular
      (arrangementDualLeftCoefficients fan basis rays c) σ)

/-- The actual coefficient diagram on a fixed affine chart. -/
def reflectedToricSectionsDiagram (σ : fan.cones) : C ⥤ ModuleCat ℂ :=
  arrangementDualLeftCartierDiagram fan nonempty regular basis rays ⋙
    FiniteCover.schemeBaseSections ℂ fan.algebraicRealization
      (fan.affineToricChartι σ).opensRange

/-- Every literal incidence character is checked on every monomial. -/
theorem reflectedToricSectionsLinearEquiv_naturality (σ : fan.cones)
    {c d : C} (f : c ⟶ d) :
    (reflectedLaurentDiagram A (fanConeRaySet fan rays σ) ℂ).map f ≫
        (reflectedToricSectionsLinearEquiv fan nonempty regular basis rays d σ).toModuleIso.hom =
      (reflectedToricSectionsLinearEquiv fan nonempty regular basis rays c σ).toModuleIso.hom ≫
        (reflectedToricSectionsDiagram fan nonempty regular basis rays σ).map f := by
  letI := toricSchemeIntegral fan nonempty
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro m a
  change reflectedToricSectionsLinearEquiv fan nonempty regular basis rays d σ
      (Finsupp.mapDomain (reflectedLaurentWeightMap A (fanConeRaySet fan rays σ) f)
        (Finsupp.single m a)) =
    Scheme.Modules.Hom.app ((arrangementDualLeftCartierDiagram fan nonempty regular basis rays).map f)
      (fan.affineToricChartι σ).opensRange
      (reflectedToricSectionsLinearEquiv fan nonempty regular basis rays c σ
        (Finsupp.single m a))
  rw [Finsupp.mapDomain_single]
  simp only [reflectedToricSectionsLinearEquiv, LinearEquiv.trans_apply,
    Finsupp.domLCongr_single]
  change toricDivisorSectionCoefficientsEquiv fan nonempty regular
      (arrangementDualLeftCoefficients fan basis rays d) σ
      (Finsupp.single (reflectedToricWeightEquiv fan basis rays d σ
        (reflectedLaurentWeightMap A (fanConeRaySet fan rays σ) f m)) a) =
    Scheme.Modules.Hom.app ((arrangementDualLeftCartierDiagram fan nonempty regular basis rays).map f)
      (fan.affineToricChartι σ).opensRange
      (toricDivisorSectionCoefficientsEquiv fan nonempty regular
        (arrangementDualLeftCoefficients fan basis rays c) σ
        (Finsupp.single (reflectedToricWeightEquiv fan basis rays c σ m) a))
  let positive : ∀ ρ,
      0 ≤ arrangementDualLeftCoefficients fan basis rays d ρ -
        arrangementDualLeftCoefficients fan basis rays c ρ +
          basis.equivFun.symm f.val (fanRayPrimitiveGenerator fan ρ) := by
    intro ρ
    have h := (diagonalEntryRegular_of_incidence fan basis rays f).1 ρ
    change 0 ≤ -(diagonalLeftCoefficients fan basis rays d.2 ρ) -
      -(diagonalLeftCoefficients fan basis rays c.2 ρ) +
        basis.equivFun.symm f.val (fanRayPrimitiveGenerator fan ρ)
    omega
  refine Eq.trans ?_ (toricDivisorSectionCoefficientsEquiv_monomial fan nonempty regular
    (arrangementDualLeftCoefficients fan basis rays c)
    (arrangementDualLeftCoefficients fan basis rays d) (basis.equivFun.symm f.val)
    positive σ (Finsupp.single (reflectedToricWeightEquiv fan basis rays c σ m) a)).symm
  rw [Finsupp.mapDomain_single]
  congr 2
  apply Subtype.ext
  change basis.equivFun.symm (m.val + f.val) =
    basis.equivFun.symm f.val + basis.equivFun.symm m.val
  rw [map_add, add_comm]

/-- The complete Laurent coefficient functor is naturally the actual
affine section functor of the original covariant Cartier labels. -/
def reflectedToricSectionsDiagramIso (σ : fan.cones) :
    reflectedLaurentDiagram A (fanConeRaySet fan rays σ) ℂ ≅
      reflectedToricSectionsDiagram fan nonempty regular basis rays σ :=
  NatIso.ofComponents
    (fun c => (reflectedToricSectionsLinearEquiv fan nonempty regular basis rays c σ).toModuleIso)
    (fun f => reflectedToricSectionsLinearEquiv_naturality
      fan nonempty regular basis rays σ f)

end ToricPower

end
