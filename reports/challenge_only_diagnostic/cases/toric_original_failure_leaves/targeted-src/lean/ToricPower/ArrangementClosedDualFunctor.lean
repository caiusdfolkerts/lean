module

public import ToricPower.ArrangementDualLeftCartierSources
public import ToricPower.ClosedContravariantLabels
public import ToricPower.ArrangementClosedSubtorus
public import ToricPower.ArrangementCellularComplex

/-! # The actual finite dual Cartier chain functor

All coefficients are inverse Cartier tensor functors, restricted to the
literal closed support. The differential is the original cellular
boundary, using the actual adjunction mates of every incidence map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  [nonempty : Nonempty fan.cones] (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local instance closedDualFunctorBiproducts : HasFiniteBiproducts (QCoh fan.algebraicRealization) :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance closedDualFunctorIntegral : IsIntegral fan.algebraicRealization :=
  toricSchemeIntegral fan nonempty

local notation "A" => fanArrangementMatrix fan basis rays
local notation "C" => IncidenceObject A
local notation "X" => fan.algebraicRealization

def arrangementDualInverseTensorFunctor : Cᵒᵖ ⥤ QCoh X ⥤ QCoh X :=
  (arrangementDualLeftCartierSources fan regular basis rays).op ⋙
    cartierSourcesQuasicoherentInverseTensor X

instance arrangementDualInverseTensorFunctor_obj_additive (c : Cᵒᵖ) :
    ((arrangementDualInverseTensorFunctor fan regular basis rays).obj c).Additive :=
  inferInstanceAs (quasicoherentCartierTensorEquivalence
    (-(cartierSourceDivisor fan.algebraicRealization
      ((arrangementDualLeftCartierSources fan regular basis rays).obj c.unop)))).functor.Additive

instance arrangementDualInverseTensorFunctor_obj_isEquivalence (c : Cᵒᵖ) :
    ((arrangementDualInverseTensorFunctor fan regular basis rays).obj c).IsEquivalence :=
  inferInstanceAs (quasicoherentCartierTensorEquivalence
    (-(cartierSourceDivisor fan.algebraicRealization
      ((arrangementDualLeftCartierSources fan regular basis rays).obj c.unop)))).functor.IsEquivalence

instance arrangementDualInverseTensorFunctor_flip_additive :
    (arrangementDualInverseTensorFunctor fan regular basis rays).flip.Additive where
  map_add {M N f g} := by
    apply NatTrans.ext
    funext c
    exact ((arrangementDualInverseTensorFunctor fan regular basis rays).obj c).map_add

variable (selected : Set (Fin s ⊕ Fin n))

def arrangementClosedDualCoefficientFunctor : QCoh X ⥤ Cᵒᵖ ⥤ QCoh X :=
  (arrangementDualInverseTensorFunctor fan regular basis rays).flip ⋙
    Cellular.closedContravariantLabelEndofunctor
      (closedIntegralRowsSupport A selected) (closedIntegralRowsSupport_incidence A selected)

def arrangementClosedDualFunctor : QCoh X ⥤ ChainComplex (QCoh X) ℕ :=
  arrangementClosedDualCoefficientFunctor fan regular basis rays selected ⋙
    arrangementCellularChainFunctor A ℂ

theorem arrangementClosedDualFunctor_isZero_X_above (M : QCoh X) (q : ℕ) (above : n < q) :
    IsZero (((arrangementClosedDualFunctor fan regular basis rays selected).obj M).X q) :=
  arrangementCellularChainComplex_isZero_X_above A ℂ _ q above

end ToricPower

end
