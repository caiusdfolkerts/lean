module

public import ToricPower.ArrangementInverseRightLabels
public import ToricPower.ToricMonomialDualityFunctor

/-! # Original and inverse-right coefficient functors

The small coefficient categories and their exact realization
comparisons retain all characters. No diagonal complex is required.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TauCeti.Toric ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "C" => IncidenceObject A
local notation "X" => fan.algebraicRealization

/-- The original right labels and all their literal monomial arrows. -/
def arrangementRightCoefficientDiagram : Cᵒᵖ ⥤ ToricMonomial.Object fan where
  obj c := ⟨diagonalRightCoefficients fan basis rays c.unop.2⟩
  map f := ⟨-(basis.equivFun.symm f.unop.val), by
    intro ρ
    simpa only [AddMonoidHom.neg_apply, sub_eq_add_neg] using
      (diagonalEntryRegular_of_incidence fan basis rays f.unop).2 ρ⟩
  map_id c := by
    apply Subtype.ext
    simp only [unop_id, incidence_id_val, map_zero, neg_zero]
    rfl
  map_comp f g := by
    apply Subtype.ext
    simp only [unop_comp, incidence_comp_val, map_add, neg_add, add_comm]
    rfl

/-- Actual inverse coefficients, in the original covariant orientation. -/
def arrangementInverseRightCoefficientDiagram : C ⥤ ToricMonomial.Object fan :=
  (arrangementRightCoefficientDiagram fan basis rays).rightOp ⋙ ToricMonomial.dual fan

/-- Double negation preserves every actual character arrow. -/
def arrangementInverseRightDualCoefficientIso :
    (arrangementInverseRightCoefficientDiagram fan basis rays).op ⋙
        ToricMonomial.dual fan ≅ arrangementRightCoefficientDiagram fan basis rays :=
  NatIso.ofComponents (fun c => ToricMonomial.coefficientIso fan _ _ (by
    change -(-diagonalRightCoefficients fan basis rays c.unop.2) = _
    exact neg_neg _)) (by
      intro c d f
      apply Subtype.ext
      exact (add_zero _).trans (zero_add _).symm)

variable (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)

local notation "R" => arrangementDualRightCartierDiagram fan nonempty regular basis rays
local notation "P₀" => arrangementRightCartierDiagram fan nonempty regular basis rays

/-- The small inverse coefficient functor realizes the original
inverse-right Cartier diagram on objects and every source arrow. -/
def arrangementInverseRightRealizationIso :
    arrangementInverseRightCoefficientDiagram fan basis rays ⋙
        ToricMonomial.realization fan nonempty regular ≅ R := by
  letI := toricSchemeIntegral fan nonempty
  refine NatIso.ofComponents (fun c => ?_) ?_
  · change (invariantCartierDivisor fan nonempty regular
        (-diagonalRightCoefficients fan basis rays c.2)).sheaf ≅
      (invariantCartierDivisor fan nonempty regular
        (-diagonalRightCoefficients fan basis rays c.2)).sheaf
    exact Iso.refl _
  · intro c d f
    change toricCartierMonomialMap fan nonempty regular
        (-diagonalRightCoefficients fan basis rays c.2)
        (-diagonalRightCoefficients fan basis rays d.2)
        (-(basis.equivFun.symm f.val)) _ ≫ 𝟙 _ =
      𝟙 _ ≫ toricCartierMonomialMap fan nonempty regular
        (-diagonalRightCoefficients fan basis rays c.2)
        (-diagonalRightCoefficients fan basis rays d.2)
        (-(basis.equivFun.symm f.val)) _
    rw [Category.comp_id, Category.id_comp]

/-- The corresponding original unreflected realization. -/
def arrangementRightCoefficientRealizationIso :
    arrangementRightCoefficientDiagram fan basis rays ⋙
        ToricMonomial.realization fan nonempty regular ≅ P₀ := by
  letI := toricSchemeIntegral fan nonempty
  refine NatIso.ofComponents (fun c => ?_) ?_
  · change (invariantCartierDivisor fan nonempty regular
        (diagonalRightCoefficients fan basis rays c.unop.2)).sheaf ≅
      (invariantCartierDivisor fan nonempty regular
        (diagonalRightCoefficients fan basis rays c.unop.2)).sheaf
    exact Iso.refl _
  · intro c d f
    change toricCartierMonomialMap fan nonempty regular
        (diagonalRightCoefficients fan basis rays c.unop.2)
        (diagonalRightCoefficients fan basis rays d.unop.2)
        (-(basis.equivFun.symm f.unop.val)) _ ≫ 𝟙 _ =
      𝟙 _ ≫ toricCartierMonomialMap fan nonempty regular
        (diagonalRightCoefficients fan basis rays c.unop.2)
        (diagonalRightCoefficients fan basis rays d.unop.2)
        (-(basis.equivFun.symm f.unop.val)) _
    rw [Category.comp_id, Category.id_comp]

end ToricPower

end
