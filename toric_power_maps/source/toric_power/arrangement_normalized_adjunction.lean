module

public import ToricPower.ArrangementToricAdjunction
public import ToricPower.QuasicoherentCartierTensor
public import ToricPower.SignedShiftFunctor

/-!
# The boundary twist and dimension shift in the cellular adjunction

The unshifted coend uses the actual Cartier labels `L(x)`. The paper's
normalized labels tensor these by the divisor with coefficient one on
every ray and shift by minus the lattice rank. Both operations are
genuine equivalences of the full unbounded quasicoherent derived
category. Composing the checked adjunction with this equivalence gives
the normalized adjunction without losing any objects or shifts.

This file does not assert cellular reconstruction or identify a dual
diagonal kernel. Those require the separate geometric comparisons.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}
  (fan : Fan i) [nonempty : Nonempty fan.cones] (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "D" => DerivedQCoh fan.algebraicRealization

local instance normalizedAdjunction_integral : IsIntegral fan.algebraicRealization := toricSchemeIntegral fan nonempty

local instance normalizedAdjunction_derivedQCoh : HasDerivedCategory.{1} (QCoh fan.algebraicRealization) :=
  HasDerivedCategory.standard _

local instance normalizedAdjunction_derivedCells : HasDerivedCategory.{1} (IncidenceObject A ⥤ ModuleCat.{0} ℂ) :=
  HasDerivedCategory.standard _

local instance normalizationShiftCommShift (m : ℤ) : (shiftFunctor D m).CommShift ℤ :=
  signedShiftFunctorCommShift D m

local instance normalizationShiftTriangulated (m : ℤ) :
    (shiftFunctor D m).IsTriangulated := signedShiftFunctor_isTriangulated D m

/-- The literal boundary Cartier divisor, with coefficient one on every ray. -/
def arrangementBoundaryDivisor :
    TauCeti.AlgebraicGeometry.Scheme.CartierDivisor fan.algebraicRealization :=
  invariantCartierDivisor fan nonempty regular (fun _ => 1)

/-- Tensoring by the boundary line followed by the actual dimension shift. -/
def arrangementNormalizationEquivalence : D ≌ D :=
  (quasicoherentCartierDerivedTensorEquivalence
    (arrangementBoundaryDivisor fan regular)).trans (shiftEquiv D (-(n : ℤ)))

/-- The realization with the paper's fixed twist and shift. -/
def arrangementNormalizedDerivedRealization :
    DerivedCategory (IncidenceObject A ⥤ ModuleCat.{0} ℂ) ⥤ D :=
  arrangementToricDerivedRealization fan nonempty regular basis rays ⋙
    (arrangementNormalizationEquivalence fan regular (n := n)).functor

/-- Its actual right adjoint, with the inverse twist and inverse shift. -/
def arrangementNormalizedDerivedHom :
    D ⥤ DerivedCategory (IncidenceObject A ⥤ ModuleCat.{0} ℂ) :=
  (arrangementNormalizationEquivalence fan regular (n := n)).inverse ⋙
    arrangementToricDerivedHom fan nonempty regular basis rays

/-- The normalized adjunction follows by composition of actual adjunctions. -/
def arrangementNormalizedDerivedAdjunction :
    arrangementNormalizedDerivedRealization fan regular basis rays ⊣
      arrangementNormalizedDerivedHom fan regular basis rays :=
  (arrangementToricDerivedAdjunction fan nonempty regular basis rays).comp
    (arrangementNormalizationEquivalence fan regular (n := n)).toAdjunction

/-- The normalization is exact on the whole unbounded category. -/
instance arrangementNormalization_functor_commShift :
    (arrangementNormalizationEquivalence fan regular (n := n)).functor.CommShift ℤ := by
  change ((quasicoherentCartierTensorEquivalence
      (arrangementBoundaryDivisor fan regular)).functor.mapDerivedCategory ⋙
    shiftFunctor D (-(n : ℤ))).CommShift ℤ
  infer_instance

instance arrangementNormalization_functor_isTriangulated :
    (arrangementNormalizationEquivalence fan regular (n := n)).functor.IsTriangulated := by
  change ((quasicoherentCartierTensorEquivalence
      (arrangementBoundaryDivisor fan regular)).functor.mapDerivedCategory ⋙
    shiftFunctor D (-(n : ℤ))).IsTriangulated
  infer_instance

instance arrangementNormalization_inverse_commShift :
    (arrangementNormalizationEquivalence fan regular (n := n)).inverse.CommShift ℤ :=
  (arrangementNormalizationEquivalence fan regular (n := n)).commShiftInverse ℤ

instance arrangementNormalization_commShift :
    (arrangementNormalizationEquivalence fan regular (n := n)).CommShift ℤ :=
  (arrangementNormalizationEquivalence fan regular (n := n)).commShift_of_functor ℤ

instance arrangementNormalization_inverse_isTriangulated :
    (arrangementNormalizationEquivalence fan regular (n := n)).inverse.IsTriangulated :=
  (arrangementNormalizationEquivalence fan regular (n := n)).toAdjunction.isTriangulated_rightAdjoint

instance arrangementNormalizedDerivedRealization_commShift :
    (arrangementNormalizedDerivedRealization fan regular basis rays).CommShift ℤ := by
  unfold arrangementNormalizedDerivedRealization
  infer_instance

instance arrangementNormalizedDerivedHom_commShift :
    (arrangementNormalizedDerivedHom fan regular basis rays).CommShift ℤ := by
  unfold arrangementNormalizedDerivedHom
  infer_instance

instance arrangementNormalizedDerivedAdjunction_commShift :
    (arrangementNormalizedDerivedAdjunction fan regular basis rays).CommShift ℤ := by
  unfold arrangementNormalizedDerivedAdjunction
  infer_instance

instance arrangementNormalizedDerivedRealization_isTriangulated :
    (arrangementNormalizedDerivedRealization fan regular basis rays).IsTriangulated := by
  unfold arrangementNormalizedDerivedRealization
  infer_instance

instance arrangementNormalizedDerivedHom_isTriangulated :
    (arrangementNormalizedDerivedHom fan regular basis rays).IsTriangulated := by
  unfold arrangementNormalizedDerivedHom
  infer_instance

end ToricPower

end
