module

public import PaperVerification.ChevalleyEilenbergExterior
public import PaperVerification.ExteriorDerivationTransport

/-!
# Pullback of the actual Chevalley--Eilenberg exterior differential

The determinant pairing is natural in every degree. Consequently the
pullback on one-cochains induced by an actual Lie equivalence transports
the intrinsic CE differential, including its negative bracket-dual sign.
Conjugation preserves square-zero and the original exterior degree.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.ChevalleyEilenbergTransport

open ExteriorDerivationTransport

section Pairing

variable {R A B : Type*} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

/-- The original determinant pairing commutes with linear pullback in
all exterior degrees, including degree zero. -/
theorem pairingDual_pullback (F : A →ₗ[R] B) (q : ℕ)
    (ω : ⋀[R]^q (Module.Dual R B)) (v : Fin q → A) :
    exteriorPower.pairingDual R A q (exteriorPower.map q F.dualMap ω)
        (exteriorPower.ιMulti R q v) =
      exteriorPower.pairingDual R B q ω
        (exteriorPower.ιMulti R q (F ∘ v)) := by
  have h :
      (Module.Dual.eval R (⋀[R]^q A) (exteriorPower.ιMulti R q v)).comp
        ((exteriorPower.pairingDual R A q).comp (exteriorPower.map q F.dualMap)) =
      (Module.Dual.eval R (⋀[R]^q B) (exteriorPower.ιMulti R q (F ∘ v))).comp
        (exteriorPower.pairingDual R B q) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro α
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      Module.Dual.eval_apply, exteriorPower.map_apply_ιMulti,
      exteriorPower.pairingDual_ιMulti_ιMulti, Function.comp_apply,
      LinearMap.dualMap_apply]
  exact LinearMap.congr_fun h ω

end Pairing

section Lie

variable {K L L' : Type*} [Field K]
  [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  [LieRing L'] [LieAlgebra K L'] [FiniteDimensional K L']

/-- Pullback of the genuine exterior differential along an actual Lie
equivalence, using its contravariant map on dual one-cochains. -/
def pullback (e : L ≃ₗ⁅K⁆ L')
    (D : Module.End K (ExteriorAlgebra K (Module.Dual K L'))) :
    Module.End K (ExteriorAlgebra K (Module.Dual K L)) :=
  conjugate e.toLinearEquiv.dualMap D

/-- Pullback preserves the intrinsic CE defining equations on every
one-cochain, with the actual Lie brackets on the two original spaces. -/
theorem pullback_isDifferential (e : L ≃ₗ⁅K⁆ L')
    (D : Module.End K (ExteriorAlgebra K (Module.Dual K L')))
    (hD : ChevalleyEilenbergExterior.IsDifferential D) :
    ChevalleyEilenbergExterior.IsDifferential (pullback e D) := by
  refine ⟨conjugate_isOddDerivation _ _ hD.1, ?_⟩
  intro α
  obtain ⟨ω, hω, hωeval⟩ := hD.2 (e.toLinearEquiv.dualMap.symm α)
  refine ⟨exteriorPower.map 2 e.toLinearEquiv.toLinearMap.dualMap ω, ?_, ?_⟩
  · rw [pullback, conjugate_apply, mapEquiv_symm_ι, hω, mapEquiv_apply]
    rw [exteriorPower.coe_map]
    apply congrArg (fun F : Module.Dual K L' →ₗ[K] Module.Dual K L =>
      ExteriorAlgebra.map F (ω : ExteriorAlgebra K (Module.Dual K L')))
    ext β z
    simp only [LinearEquiv.coe_coe, LinearEquiv.dualMap_apply, LinearMap.dualMap_apply]
  · intro x y
    rw [pairingDual_pullback]
    have hv : e.toLinearEquiv.toLinearMap ∘ ![x,y] = ![e x,e y] := by
      ext i
      fin_cases i <;> rfl
    rw [hv, hωeval, ← e.map_lie]
    change -((e.toLinearEquiv.dualMap (e.toLinearEquiv.dualMap.symm α)) ⁅x,y⁆) = -α ⁅x,y⁆
    rw [LinearEquiv.apply_symm_apply]

/-- Actual cochain pullback intertwines the two linear differentials. -/
theorem pullback_map (e : L ≃ₗ⁅K⁆ L')
    (D : Module.End K (ExteriorAlgebra K (Module.Dual K L')))
    (x : ExteriorAlgebra K (Module.Dual K L')) :
    pullback e D (mapEquiv e.toLinearEquiv.dualMap x) =
      mapEquiv e.toLinearEquiv.dualMap (D x) := by
  simp only [pullback, conjugate_apply, AlgEquiv.symm_apply_apply]

/-- Square-zero is retained on the original cochains. -/
theorem pullback_square_zero (e : L ≃ₗ⁅K⁆ L')
    (D : Module.End K (ExteriorAlgebra K (Module.Dual K L')))
    (hD : ∀ x, D (D x) = 0) (x : ExteriorAlgebra K (Module.Dual K L)) :
    pullback e D (pullback e D x) = 0 :=
  conjugate_square_zero _ _ hD x

/-- The ordinary cohomological degree is retained, in every natural
exterior degree and for the original homogeneous submodules. -/
theorem pullback_degree (e : L ≃ₗ⁅K⁆ L')
    (D : Module.End K (ExteriorAlgebra K (Module.Dual K L')))
    (hD : ∀ q x, x ∈ ⋀[K]^q (Module.Dual K L') →
      D x ∈ ⋀[K]^(q+1) (Module.Dual K L'))
    (q : ℕ) (x : ExteriorAlgebra K (Module.Dual K L))
    (hx : x ∈ ⋀[K]^q (Module.Dual K L)) :
    pullback e D x ∈ ⋀[K]^(q+1) (Module.Dual K L) :=
  conjugate_degree _ _ hD q x hx

end Lie
end PaperVerification.ChevalleyEilenbergTransport
