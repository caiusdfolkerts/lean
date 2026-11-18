module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Representation

/-!
# Actual Cartier representation with a chosen dense trivialization

These are genuine generic proofs for integral schemes. A line bundle is
embedded in its rational-function sheaf using a chosen trivialization on a
dense open, and local basis functions give compatible Cartier equations.
The resulting Cartier-divisor sheaf is isomorphic to the original bundle.
The final lemmas record that this divisor is zero on the chosen open.

Complete supporting source bodies are retained with provenance. The optional
passage to the group of line-bundle isomorphism classes is not needed here.
-/

/-! ## Vanishing on the chosen dense open -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}} [IrreducibleSpace X] (M : X.Modules)
  {U : X.Opens}
  (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
  (hU : Dense (U : Set X))

/-- Reading the basis section in the very same chosen rational
trivialization gives the rational function one. -/
theorem rationalFunction_trivializationGenerator_self [Nonempty U] :
    rationalFunction M e hU U (trivializationGenerator M e) = 1 := by
  have : Nonempty (U ⊓ U : X.Opens) := by
    simpa only [inf_idem] using (inferInstance : Nonempty U)
  rw [rationalFunction_apply]
  have hi : (homOfLE (inf_le_left : U ⊓ U ≤ U)) =
      homOfLE (inf_le_right : U ⊓ U ≤ U) := Subsingleton.elim _ _
  rw [hi, trivializationCoordinate_map_trivializationGenerator, map_one]

@[simp]
theorem trivializationGeneratorRationalUnit_self [Nonempty U] :
    trivializationGeneratorRationalUnit M e hU e = 1 := by
  apply Units.ext
  rw [coe_trivializationGeneratorRationalUnit,
    rationalFunction_trivializationGenerator_self]
  rfl

end AlgebraicGeometry.Scheme.Modules

namespace TauCeti.AlgebraicGeometry.Scheme

universe u

variable (X : _root_.AlgebraicGeometry.Scheme.{u}) [IsIntegral X]

/-- Vanishing of the actual Cartier class on an open subset means that
the rational function comes from an actual regular unit on that open. -/
theorem rationalUnitClass_eq_zero_iff_exists_regularUnit
    (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ) :
    rationalUnitClass X U (Additive.ofMul f) = 0 ↔
      ∃ r : Γ(X, U)ˣ, Units.map (X.germToFunctionField U).hom r = f := by
  have zero_class : rationalUnitClass X U (Additive.ofMul (1 : X.functionFieldˣ)) = 0 :=
    (rationalUnitClass X U).map_zero
  constructor
  · intro h
    obtain ⟨r, hr⟩ := (rationalUnitClass_eq_rationalUnitClass_iff X U f 1).mp
      (h.trans zero_class.symm)
    rw [mul_one] at hr
    exact ⟨r, (regularUnitToFunctionField_apply X U r).symm.trans hr⟩
  · rintro ⟨r, hr⟩
    apply Eq.trans _ zero_class
    apply (rationalUnitClass_eq_rationalUnitClass_iff X U f 1).mpr
    exact ⟨r, (mul_one _).trans ((regularUnitToFunctionField_apply X U r).trans hr)⟩


end TauCeti.AlgebraicGeometry.Scheme

namespace ToricPower

open TauCeti.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}} [IsIntegral X] (M : X.Modules)
  [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M]
  {U : X.Opens}

/-- An actual line bundle trivialized on a specified dense open has an
actual Cartier representative whose restriction to that open is zero.
The sheaf isomorphism is the one induced by the rational trivialization. -/
theorem exists_cartierDivisor_zero_on_trivializing_open
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X)) :
    ∃ D : TauCeti.AlgebraicGeometry.Scheme.CartierDivisor X,
      D |_ U = 0 ∧ Nonempty (M ≅ D.sheaf) := by
  have : Nonempty U := Opens.nonempty_coeSort.mpr hU.nonempty
  obtain ⟨D, hD⟩ := M.exists_cartierDivisor_restrict_eq e hU
  refine ⟨D, ?_, ⟨TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.isoSheafOfRestrictEq hD⟩⟩
  rw [hD U e, trivializationGeneratorRationalUnit_self]
  simp

/-- Convert a trivialization on the ordinary open subscheme to the
equivalent free rank-one trivialization on its slice site. -/
def freeTrivializationOverOfUnitRestrict
    (e : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ M.restrict U.ι) :
    SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U :=
  TauCeti.SheafOfModules.freePUnitIsoUnit (X.ringCatSheaf.over U) ≪≫
    (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimageIso
      (e ≪≫ ((Scheme.Modules.overFunctorEquiv U).app M).symm)

/-- The same Cartier representation theorem accepts the ordinary
restriction isomorphism used by affine triviality results. -/
theorem exists_cartierDivisor_zero_of_restrictIsoUnit
    (e : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ M.restrict U.ι)
    (hU : Dense (U : Set X)) :
    ∃ D : TauCeti.AlgebraicGeometry.Scheme.CartierDivisor X,
      D |_ U = 0 ∧ Nonempty (M ≅ D.sheaf) :=
  exists_cartierDivisor_zero_on_trivializing_open M
    (freeTrivializationOverOfUnitRestrict M e) hU

end ToricPower

end
