module

public import ToricPower.ArrangementDualLeftCartierSources
public import ToricPower.DualLaurentDiagram
public import ToricPower.ToricCartierSectionsLinear
public import ToricPower.CechToricMonomialSections
public import ToricPower.CechToricCover
public import ToricPower.DiagonalToricWeights

/-! # Literal affine sections of the inverse cellular Cartier labels

Every integral character is retained. The original contravariant
incidence map translates a character by the actual positive incidence
character. All scalar structures are the genuine scheme base action.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TauCeti.Toric
open ToricPower.IntegralArrangement
open scoped Classical

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  [nonempty : Nonempty fan.cones] (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local instance closedDualSectionsIntegral : IsIntegral fan.algebraicRealization :=
  toricSchemeIntegral fan nonempty

local notation "A" => fanArrangementMatrix fan basis rays
local notation "C" => IncidenceObject A

theorem dualLaurent_allowed_iff (b : fan.Ray → ℤ) (c : C)
    (σ : fan.cones) (m : Fin n → ℤ) :
    (∀ j ∈ fanConeRaySet fan rays σ,
      reflectedCeiling A c.2.val j ≤ rayPairing A m j+b (rays j)) ↔
      toricCharacterAllowed fan (b-arrangementDualLeftCoefficients fan basis rays c)
        σ (basis.equivFun.symm m) := by
  constructor
  · intro allowed ρ contained
    have h := allowed (rays.symm ρ) (by
      change (rays (rays.symm ρ)).toCone ≤ σ
      simpa only [Equiv.apply_symm_apply] using contained)
    simp only [Pi.sub_apply,arrangementDualLeftCoefficients_apply]
    rw [Equiv.apply_symm_apply] at h
    have pairing := fanArrangementMatrix_character fan basis rays m ρ
    omega
  · intro allowed j contained
    have h := allowed (rays j) contained
    simp only [Pi.sub_apply,arrangementDualLeftCoefficients_apply] at h
    rw [← fanArrangementMatrix_character fan basis rays m (rays j),
      Equiv.symm_apply_apply] at h
    omega

def dualToricWeightEquiv (b : fan.Ray → ℤ) (c : C) (σ : fan.cones) :
    DualLaurentWeight A (fanConeRaySet fan rays σ) (fun j => b (rays j)) c ≃
      ToricChartDivisorWeight fan (b-arrangementDualLeftCoefficients fan basis rays c) σ :=
  (Equiv.subtypeEquiv basis.equivFun.symm.toEquiv
    (fun m => dualLaurent_allowed_iff fan basis rays b c σ m)).trans
      (toricChartWeightGlobalEquiv fan
        (b-arrangementDualLeftCoefficients fan basis rays c) σ).symm

@[simp]
theorem dualToricWeightEquiv_val (b : fan.Ray → ℤ) (c : C) (σ : fan.cones)
    (m : DualLaurentWeight A (fanConeRaySet fan rays σ) (fun j => b (rays j)) c) :
    (dualToricWeightEquiv fan basis rays b c σ m).val = basis.equivFun.symm m.val := rfl

def dualToricSectionsLinearEquiv (b : fan.Ray → ℤ) (c : C) (σ : fan.cones) :
    (DualLaurentWeight A (fanConeRaySet fan rays σ) (fun j => b (rays j)) c →₀ ℂ) ≃ₗ[ℂ]
      (FiniteCover.schemeBaseSections ℂ fan.algebraicRealization
        (fan.affineToricChartι σ).opensRange).obj
          ((invariantCartierDivisor fan nonempty regular
            (b-arrangementDualLeftCoefficients fan basis rays c)).sheaf) :=
  (Finsupp.domLCongr (R := ℂ) (dualToricWeightEquiv fan basis rays b c σ)).trans
    (toricDivisorSectionCoefficientsLinearEquiv fan nonempty regular
      (b-arrangementDualLeftCoefficients fan basis rays c) σ)

def dualToricSectionsDiagram (b : fan.Ray → ℤ) (σ : fan.cones) : Cᵒᵖ ⥤ ModuleCat ℂ :=
  arrangementDualDifferenceCoefficientDiagram fan regular basis rays b ⋙
    FiniteCover.schemeBaseSections ℂ fan.algebraicRealization
      (fan.affineToricChartι σ).opensRange

theorem dualToricSectionsLinearEquiv_naturality (b : fan.Ray → ℤ) (σ : fan.cones)
    {c d : C} (f : c ⟶ d) :
    (dualLaurentDiagram A (fanConeRaySet fan rays σ) (fun j => b (rays j)) ℂ).map f.op ≫
        (dualToricSectionsLinearEquiv fan regular basis rays b c σ).toModuleIso.hom =
      (dualToricSectionsLinearEquiv fan regular basis rays b d σ).toModuleIso.hom ≫
        (dualToricSectionsDiagram fan regular basis rays b σ).map f.op := by
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro m a
  change dualToricSectionsLinearEquiv fan regular basis rays b c σ
      (Finsupp.mapDomain
        (dualLaurentWeightMap A (fanConeRaySet fan rays σ) (fun j => b (rays j)) f)
        (Finsupp.single m a)) =
    Scheme.Modules.Hom.app
      ((arrangementDualDifferenceCoefficientDiagram fan regular basis rays b).map f.op)
      (fan.affineToricChartι σ).opensRange
      (dualToricSectionsLinearEquiv fan regular basis rays b d σ (Finsupp.single m a))
  rw [Finsupp.mapDomain_single]
  simp only [dualToricSectionsLinearEquiv,LinearEquiv.trans_apply,Finsupp.domLCongr_single]
  change toricDivisorSectionCoefficientsEquiv fan nonempty regular
      (b-arrangementDualLeftCoefficients fan basis rays c) σ
      (Finsupp.single (dualToricWeightEquiv fan basis rays b c σ
        (dualLaurentWeightMap A (fanConeRaySet fan rays σ) (fun j => b (rays j)) f m)) a) =
    Scheme.Modules.Hom.app
      ((arrangementDualDifferenceCoefficientDiagram fan regular basis rays b).map f.op)
      (fan.affineToricChartι σ).opensRange
      (toricDivisorSectionCoefficientsEquiv fan nonempty regular
        (b-arrangementDualLeftCoefficients fan basis rays d) σ
        (Finsupp.single (dualToricWeightEquiv fan basis rays b d σ m) a))
  let positive := toricMonomialNonnegative_inverseTwist fan
    (arrangementDualLeftCoefficients fan basis rays c)
    (arrangementDualLeftCoefficients fan basis rays d) b
    (basis.equivFun.symm f.val) (arrangementDualLeftCharacter_regular fan basis rays f)
  refine Eq.trans ?_ (toricDivisorSectionCoefficientsEquiv_monomial fan nonempty regular
    (b-arrangementDualLeftCoefficients fan basis rays d)
    (b-arrangementDualLeftCoefficients fan basis rays c) (basis.equivFun.symm f.val)
    positive σ (Finsupp.single (dualToricWeightEquiv fan basis rays b d σ m) a)).symm
  rw [Finsupp.mapDomain_single]
  congr 2
  apply Subtype.ext
  change basis.equivFun.symm (m.val+f.val) =
    basis.equivFun.symm f.val+basis.equivFun.symm m.val
  rw [map_add,add_comm]

def dualToricSectionsDiagramIso (b : fan.Ray → ℤ) (σ : fan.cones) :
    dualLaurentDiagram A (fanConeRaySet fan rays σ) (fun j => b (rays j)) ℂ ≅
      dualToricSectionsDiagram fan regular basis rays b σ :=
  NatIso.ofComponents
    (fun c => (dualToricSectionsLinearEquiv fan regular basis rays b c.unop σ).toModuleIso)
    (fun f => dualToricSectionsLinearEquiv_naturality fan regular basis rays b σ f.unop)

end ToricPower

end
