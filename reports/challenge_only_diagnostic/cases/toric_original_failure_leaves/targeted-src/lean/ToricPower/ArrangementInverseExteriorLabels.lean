module

public import ToricPower.ArrangementInverseRightLabels
public import ToricPower.DiagonalCellularIdentification
public import ToricPower.DiagonalPullbackExteriorIso
public import ToricPower.ToricMonomialDualityFunctor
public import ToricPower.ArrangementCellularCoefficientFunctor
public import ToricPower.SchemeAffineLinear

/-!
# The actual inverse labels on the pulled diagonal complex

The two inverse factors are the genuine invariant Cartier sheaves with
negated coefficients. Their incidence maps retain the characters `a`
and `-a`. The rational inverse-divisor comparisons identify their
exterior product with the actual internal-dual kernel, naturally on
every incidence. Pullback to the diagonal gives the pointwise tensor
diagram used by represented cellular evaluation.

No exactness of diagonal pullback is asserted or used here.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TauCeti.Toric TauCeti.AlgebraicGeometry.Scheme ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "C" => IncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "Y" => toricDiagonalProduct fan
local notation "Q" => arrangementDualLeftCartierDiagram fan nonempty regular basis rays

local notation "R" => arrangementDualRightCartierDiagram fan nonempty regular basis rays

local instance dualLeftQuasicoherent (c : C) : ((Q).obj c).IsQuasicoherent := by
  letI := toricSchemeIntegral fan nonempty
  letI := (invariantCartierDivisor fan nonempty regular
    (arrangementDualLeftCoefficients fan basis rays c)).isInvertible_sheaf
  change (invariantCartierDivisor fan nonempty regular
    (arrangementDualLeftCoefficients fan basis rays c)).sheaf.IsQuasicoherent
  infer_instance

/-- The original inverse-divisor identifications on both exterior
factors form a genuine natural isomorphism, including all character maps. -/
def diagonalExteriorCoefficientIso :
    diagonalExteriorDualDiagram fan nonempty regular basis rays ≅
      exteriorLabelDiagram fan Q R := by
  letI := toricSchemeIntegral fan nonempty
  refine NatIso.ofComponents (fun c =>
    tensorIso
      ((Scheme.Modules.pullback (toricDiagonalFirst fan)).mapIso
        (ToricMonomial.inverseCoefficientIso fan nonempty regular
          (diagonalLeftCoefficients fan basis rays c.2)))
      ((Scheme.Modules.pullback (toricDiagonalSecond fan)).mapIso
        (ToricMonomial.inverseCoefficientIso fan nonempty regular
          (diagonalRightCoefficients fan basis rays c.2)))) ?_
  intro c d f
  rw [diagonalExteriorDualDiagram_map]
  change
    ((Scheme.Modules.pullback (toricDiagonalFirst fan)).map
        (toricCartierMonomialDualMap fan nonempty regular
          (diagonalLeftCoefficients fan basis rays d.2)
          (diagonalLeftCoefficients fan basis rays c.2) (basis.equivFun.symm f.val) _) ⊗ₘ
      (Scheme.Modules.pullback (toricDiagonalSecond fan)).map
        (toricCartierMonomialDualMap fan nonempty regular
          (diagonalRightCoefficients fan basis rays d.2)
          (diagonalRightCoefficients fan basis rays c.2) (-(basis.equivFun.symm f.val)) _)) ≫
      (_ ⊗ₘ _) = (_ ⊗ₘ _) ≫ (_ ⊗ₘ _)
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  congr 1
  · change
      (Scheme.Modules.pullback (toricDiagonalFirst fan)).map
        (toricCartierMonomialDualMap fan nonempty regular
          (diagonalLeftCoefficients fan basis rays d.2)
          (diagonalLeftCoefficients fan basis rays c.2) (basis.equivFun.symm f.val) _) ≫
        (Scheme.Modules.pullback (toricDiagonalFirst fan)).map
          (ToricMonomial.inverseCoefficientIso fan nonempty regular
            (diagonalLeftCoefficients fan basis rays d.2)).hom =
      (Scheme.Modules.pullback (toricDiagonalFirst fan)).map
        (ToricMonomial.inverseCoefficientIso fan nonempty regular
          (diagonalLeftCoefficients fan basis rays c.2)).hom ≫
        (Scheme.Modules.pullback (toricDiagonalFirst fan)).map
          (toricCartierMonomialMap fan nonempty regular
            (-diagonalLeftCoefficients fan basis rays c.2)
            (-diagonalLeftCoefficients fan basis rays d.2) (basis.equivFun.symm f.val) _)
    have compatible := congrArg (Scheme.Modules.pullback (toricDiagonalFirst fan)).map
      (ToricMonomial.dualMap_inverseCoefficientIso fan nonempty regular
        (diagonalLeftCoefficients fan basis rays d.2)
        (diagonalLeftCoefficients fan basis rays c.2) (basis.equivFun.symm f.val)
        (diagonalEntryRegular_of_incidence fan basis rays f).1)
    simpa only [Functor.map_comp] using compatible
  · change
      (Scheme.Modules.pullback (toricDiagonalSecond fan)).map
        (toricCartierMonomialDualMap fan nonempty regular
          (diagonalRightCoefficients fan basis rays d.2)
          (diagonalRightCoefficients fan basis rays c.2) (-(basis.equivFun.symm f.val)) _) ≫
        (Scheme.Modules.pullback (toricDiagonalSecond fan)).map
          (ToricMonomial.inverseCoefficientIso fan nonempty regular
            (diagonalRightCoefficients fan basis rays d.2)).hom =
      (Scheme.Modules.pullback (toricDiagonalSecond fan)).map
        (ToricMonomial.inverseCoefficientIso fan nonempty regular
          (diagonalRightCoefficients fan basis rays c.2)).hom ≫
        (Scheme.Modules.pullback (toricDiagonalSecond fan)).map
          (toricCartierMonomialMap fan nonempty regular
            (-diagonalRightCoefficients fan basis rays c.2)
            (-diagonalRightCoefficients fan basis rays d.2) (-(basis.equivFun.symm f.val)) _)
    have compatible := congrArg (Scheme.Modules.pullback (toricDiagonalSecond fan)).map
      (ToricMonomial.dualMap_inverseCoefficientIso fan nonempty regular
        (diagonalRightCoefficients fan basis rays d.2)
        (diagonalRightCoefficients fan basis rays c.2) (-(basis.equivFun.symm f.val))
        (by intro ρ
            simpa only [AddMonoidHom.neg_apply, sub_eq_add_neg] using
              (diagonalEntryRegular_of_incidence fan basis rays f).2 ρ))
    simpa only [Functor.map_comp] using compatible

/-- The actual diagonal respects the specified complex base field. -/
instance toricDiagonal_isOver : (toricDiagonal fan).IsOver (Spec (.of ℂ)) where
  comp_over := by
    change toricDiagonal fan ≫
      (toricDiagonalFirst fan ≫ fan.algebraicRealizationStructureMap) =
        fan.algebraicRealizationStructureMap
    rw [← Category.assoc]
    change (pullback.diagonal fan.algebraicRealizationStructureMap ≫
      pullback.fst _ _) ≫ fan.algebraicRealizationStructureMap = _
    rw [pullback.diagonal_fst, Category.id_comp]

local instance : HasFiniteBiproducts (X).Modules := HasFiniteBiproducts.of_hasFiniteProducts
local instance : HasFiniteBiproducts (Y).Modules := HasFiniteBiproducts.of_hasFiniteProducts

/-- The complete pulled internal-dual complex has the actual cellular
cochain coefficients `Q(c) ⊗ R(c)`, with every differential compared.
This is a complex isomorphism and does not use derived pullback. -/
def diagonalPulledCellularComplexIso :
    ((Scheme.Modules.pullback (toricDiagonal fan)).mapHomologicalComplex (.up ℕ)).obj
        (internalDualComplex (Y).Modules
          (diagonalGlobalSheafComplex fan nonempty regular basis rays)) ≅
      arrangementCellularCochainComplex A ℂ (Cellular.covariantTensorDiagram Q R) :=
  ((Scheme.Modules.pullback (toricDiagonal fan)).mapHomologicalComplex (.up ℕ)).mapIso
      (diagonalExteriorDualComplexIso fan nonempty regular basis rays) ≪≫
    cellularCoefficientComplexIso A ℂ (Scheme.Modules.pullback (toricDiagonal fan))
      (diagonalExteriorDualDiagram fan nonempty regular basis rays) ≪≫
    (arrangementCellularCochainFunctor A ℂ).mapIso
      (Functor.isoWhiskerRight
          (diagonalExteriorCoefficientIso fan nonempty regular basis rays)
          (Scheme.Modules.pullback (toricDiagonal fan)) ≪≫
        diagonalPullbackExteriorDiagramIso fan Q R (fun _ => inferInstance))

end ToricPower

end
