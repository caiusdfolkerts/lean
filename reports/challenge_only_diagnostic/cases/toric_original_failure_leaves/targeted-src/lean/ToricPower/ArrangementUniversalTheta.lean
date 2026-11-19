module

public import ToricPower.OpenScalarLaurentSum
public import ToricPower.ArrangementStrictRegion
public import ToricPower.DiagonalFanLabels
public import ToricPower.ToricMonomialCategory
public import ToricPower.CechToricLinearCoefficients
public import ToricPower.CechToricMonomialSections

/-! # The full affine theta diagram on the actual universal cells

The absolute ceiling label of a universal cell defines an actual Cartier
sheaf. Every face arrow is multiplication by the unit character. Its
sections on a toric affine chart form the unrestricted direct sum of the
strict-support scalar diagrams. The comparison is complex-linear and
natural before passage to complexes or derived categories.
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
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "U" => UniversalIncidenceObject A
local notation "J" => Fin s ⊕ Fin n

/-- The absolute dual label has coefficient `ceil(x(v))-1`. -/
def universalDualCoefficients (c : U) : fan.Ray → ℤ :=
  fun ρ => c.2.val.1 (.inl (rays.symm ρ)) - 1

/-- On actual universal cells there is no lattice carry: every face map
of these absolute labels is the unit-character monomial map. -/
def universalDualCoefficientDiagram : U ⥤ ToricMonomial.Object fan where
  obj c := ⟨universalDualCoefficients fan basis rays c⟩
  map {c d} f := ⟨0,by
    intro ρ
    have below := universalIncidence_ceiling_le A f.le (.inl (rays.symm ρ))
    simp only [universalDualCoefficients,AddMonoidHom.zero_apply]
    omega⟩
  map_id c := rfl
  map_comp f g := by
    apply Subtype.ext
    exact (zero_add (0 : N →+ ℤ)).symm

variable (cone : fan.cones)

/-- Exactly the fan rays contained in the chosen affine cone. The
coordinate hyperplanes used to make the arrangement bounded are absent. -/
def universalThetaSelected : Set J :=
  fun j => match j with
    | .inl r => (rays r).toCone ≤ cone
    | .inr _ => False

def universalThetaLower (m : N →+ ℤ) : J → ℤ :=
  Sum.elim (fun r => -m (fanRayPrimitiveGenerator fan (rays r))) (fun _ => 0)

def universalChartAllowed (c : U) (m : N →+ ℤ) : Prop :=
  toricCharacterAllowed fan (universalDualCoefficients fan basis rays c) cone m

/-- The actual chart inequalities are precisely the open strict region,
including the integer boundary convention. -/
theorem universalChartAllowed_iff_strict (c : U) (m : N →+ ℤ) :
    universalChartAllowed fan basis rays cone c m ↔
      universalStrictSupport A (universalThetaLower fan rays m)
        (universalThetaSelected fan rays cone) c := by
  constructor
  · intro h j selected
    cases j with
    | inl r =>
        have bound := h (rays r) selected
        simp only [universalDualCoefficients,Equiv.symm_apply_apply] at bound
        change -m (fanRayPrimitiveGenerator fan (rays r)) < c.2.val.1 (.inl r)
        omega
    | inr r => exact selected.elim
  · intro h ρ included
    have bound := h (.inl (rays.symm ρ)) (by
      change (rays (rays.symm ρ)).toCone ≤ cone
      simpa only [Equiv.apply_symm_apply] using included)
    simp only [universalThetaLower,Sum.elim_inl,Equiv.apply_symm_apply] at bound
    change 0 ≤ c.2.val.1 (.inl (rays.symm ρ)) - 1 +
      m (fanRayPrimitiveGenerator fan ρ)
    omega

theorem universalChartAllowed_upward {c d : U} (below : c ≤ d) (m : N →+ ℤ) :
    universalChartAllowed fan basis rays cone c m →
      universalChartAllowed fan basis rays cone d m := by
  intro allowed ρ included
  have value := allowed ρ included
  have ceiling := universalIncidence_ceiling_le A below (.inl (rays.symm ρ))
  simp only [universalDualCoefficients] at value ⊢
  omega

/-- Every character, with its genuine zero-or-scalar support module. -/
abbrev universalThetaFamily : U ⥤ (Discrete (N →+ ℤ) ⥤ ModuleCat ℂ) :=
  MorseCoefficients.scalarSupportFamily ℂ (universalChartAllowed fan basis rays cone)
    (fun h m => universalChartAllowed_upward fan basis rays cone h m)

abbrev universalChartLaurentDiagram : U ⥤ ModuleCat ℂ :=
  MorseCoefficients.laurentSupportDiagram ℂ (universalChartAllowed fan basis rays cone)
    (fun h m => universalChartAllowed_upward fan basis rays cone h m)

variable [nonempty : Nonempty fan.cones] (regular : fan.IsRegular)
local instance : IsIntegral fan.algebraicRealization := toricSchemeIntegral fan nonempty

/-- Actual sections of the actual absolute Cartier label on the chart. -/
def universalCartierChartSections : U ⥤ ModuleCat ℂ :=
  universalDualCoefficientDiagram fan basis rays ⋙
    ToricMonomial.realization fan nonempty regular ⋙
    FiniteCover.schemeBaseSections ℂ fan.algebraicRealization
      (fan.affineToricChartι cone).opensRange

theorem toricDivisorLaurentLinear_apply (b : fan.Ray → ℤ)
    (z : (FiniteCover.schemeBaseSections ℂ fan.algebraicRealization
      (fan.affineToricChartι cone).opensRange).obj
        (invariantCartierDivisor fan nonempty regular b).sheaf) :
    toricDivisorLaurentCoefficientsLinearEquiv fan nonempty regular b cone z =
      toricDivisorLaurentCoefficientsEquiv fan nonempty regular b cone z :=
  DFunLike.congr_fun
    (toricDivisorLaurentCoefficientsLinearEquiv_toAddEquiv fan nonempty regular b cone) z

/-- The coordinate map intertwines every genuine face map; the full
Laurent polynomial is literally unchanged by a unit-character arrow. -/
def universalCartierChartLaurentIso :
    universalCartierChartSections fan basis rays cone regular ≅
      universalChartLaurentDiagram fan basis rays cone :=
  NatIso.ofComponents (fun c =>
    (toricDivisorLaurentCoefficientsLinearEquiv fan nonempty regular
      (universalDualCoefficients fan basis rays c) cone).toModuleIso) (by
    intro c d f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change (toricDivisorLaurentCoefficientsLinearEquiv fan nonempty regular
      (universalDualCoefficients fan basis rays d) cone
      (Scheme.Modules.Hom.app
        (toricCartierMonomialMap fan nonempty regular
          (universalDualCoefficients fan basis rays c)
          (universalDualCoefficients fan basis rays d) 0
          ((universalDualCoefficientDiagram fan basis rays).map f).property)
        (fan.affineToricChartι cone).opensRange z)).val =
      (toricDivisorLaurentCoefficientsLinearEquiv fan nonempty regular
        (universalDualCoefficients fan basis rays c) cone z).val
    rw [toricDivisorLaurentLinear_apply,toricDivisorLaurentLinear_apply]
    refine (toricDivisorLaurentCoefficientsEquiv_monomial fan nonempty regular
        (universalDualCoefficients fan basis rays c)
        (universalDualCoefficients fan basis rays d) 0
        ((universalDualCoefficientDiagram fan basis rays).map f).property cone z).trans ?_
    rw [show (fun m : N →+ ℤ => (0 : N →+ ℤ) + m) = id from funext zero_add]
    exact Finsupp.mapDomain_id)

/-- Actual affine Cartier sections are the unrestricted character sum
as a complete diagram, not merely as individual vector spaces. -/
def universalThetaSumActualIso :
    universalThetaFamily fan basis rays cone ⋙ ModuleDirectSum.sumFunctor ℂ ≅
      universalCartierChartSections fan basis rays cone regular :=
  MorseCoefficients.scalarSupportSumIso ℂ (universalChartAllowed fan basis rays cone)
    (fun h m => universalChartAllowed_upward fan basis rays cone h m) ≪≫
      (universalCartierChartLaurentIso fan basis rays cone regular).symm

end ToricPower

end
