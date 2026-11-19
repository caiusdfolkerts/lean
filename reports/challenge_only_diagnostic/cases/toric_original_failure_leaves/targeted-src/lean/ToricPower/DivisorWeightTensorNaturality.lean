module

public import ToricPower.DivisorWeightAdditive

/-!
# Tensor multiplication intertwines the actual monomial maps

The tensor product of multiplication by `χ^m` and multiplication by
`χ^n` is multiplication by `χ^(m+n)` after the genuine Cartier tensor
isomorphisms. Equality is checked on the sectionwise pure tensors that
generate the sheafified tensor, using the actual rational-function
inclusions. No compatibility of these maps is taken as an assumption.

All comparisons concern the actual tensor products and rational-function maps.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace Opposite
open TauCeti.Toric
open scoped TensorProduct

namespace ToricPower

universe u v

section ActualTensorSections

variable {X : Scheme.{u}}

/-- The sectionwise pure tensor, inserted into the actual tensor sheaf
by the genuine lax tensor map of the forgetful functor. -/
def schemeTensorSection (M N : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) (t : Γ(N, U)) : Γ(M ⊗ N, U) :=
  (Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget X.ringCatSheaf) M N).app
    (op U) (s ⊗ₜ[Γ(X, U)] t)

/-- Tensoring actual sheaf morphisms acts on the actual inserted pure
tensors by applying the two section maps. -/
theorem schemeTensorSection_naturality {M M' N N' : X.Modules}
    (f : M ⟶ M') (g : N ⟶ N') (U : X.Opens) (s : Γ(M, U)) (t : Γ(N, U)) :
    Scheme.Modules.Hom.app (f ⊗ₘ g) U (schemeTensorSection M N U s t) =
      schemeTensorSection M' N' U
        (Scheme.Modules.Hom.app f U s) (Scheme.Modules.Hom.app g U t) := by
  have naturality := Functor.LaxMonoidal.μ_natural
    (_root_.SheafOfModules.forget X.ringCatSheaf) f g
  have component := congrArg (fun map => PresheafOfModules.Hom.app map (op U)) naturality
  have value := congrArg
    (fun map :
        (((_root_.SheafOfModules.forget X.ringCatSheaf).obj M) ⊗
          ((_root_.SheafOfModules.forget X.ringCatSheaf).obj N)).obj (op U) ⟶
        ((_root_.SheafOfModules.forget X.ringCatSheaf).obj (M' ⊗ N')).obj (op U) =>
      map.hom (s ⊗ₜ[Γ(X, U)] t)) component
  exact value.symm

/-- Equality on the genuine sectionwise pure tensors determines a map
out of the actual sheaf tensor product. -/
theorem schemeTensorHom_ext {M N P : X.Modules} {f g : M ⊗ N ⟶ P}
    (same : ∀ (U : X.Opens) (s : Γ(M, U)) (t : Γ(N, U)),
      Scheme.Modules.Hom.app f U (schemeTensorSection M N U s t) =
        Scheme.Modules.Hom.app g U (schemeTensorSection M N U s t)) : f = g := by
  apply TauCeti.SheafOfModules.tensor_hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
    (R := X.sheaf.obj.obj U) (M₁ := M.val.obj U) (M₂ := N.val.obj U) (M₃ := P.val.obj U)
  intro s t
  exact same U.unop s t

/-- The inserted tensor is the genuine presheaf tensor followed by the
sheafification unit and its canonical comparison with the sheaf tensor. -/
theorem schemeTensorSection_eq_sheafification (M N : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) (t : Γ(N, U)) :
    schemeTensorSection M N U s t =
      Scheme.Modules.Hom.app (M.tensorUnderlyingIso N).inv U
        (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (PresheafOfModulesOfCommRing.Monoidal.tensorObj
            (R := X.sheaf.obj) M.val N.val)).app (op U)
          (s ⊗ₜ[X.sheaf.obj.obj (op U)] t)) := by
  unfold schemeTensorSection
  erw [TauCeti.SheafOfModules.forget_μ X.sheaf M N]
  rfl

variable [IsIntegral X]

/-- For a Cartier target it suffices to compare rational values on
nonempty opens. The empty-open case follows from the actual rational
sheaf's subsingleton sections there. -/
theorem cartierTensorHom_ext_nonempty
    (D : TauCeti.AlgebraicGeometry.Scheme.CartierDivisor X)
    {M N : X.Modules} {f g : M ⊗ N ⟶ D.sheaf}
    (same : ∀ (U : X.Opens) [Nonempty U] (s : Γ(M, U)) (t : Γ(N, U)),
      TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv U
        (Scheme.Modules.Hom.app D.sheafι U
          (Scheme.Modules.Hom.app f U (schemeTensorSection M N U s t))) =
      TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv U
        (Scheme.Modules.Hom.app D.sheafι U
          (Scheme.Modules.Hom.app g U (schemeTensorSection M N U s t)))) : f = g := by
  apply schemeTensorHom_ext
  intro U s t
  apply D.sheafι_app_injective U
  rcases isEmpty_or_nonempty U with hU | hU
  · have empty : U = ⊥ := Opens.coe_eq_empty.mp (Set.isEmpty_coe_sort.mp hU)
    letI := TauCeti.AlgebraicGeometry.Scheme.subsingleton_rationalFunctions U empty
    exact Subsingleton.elim _ _
  · letI := hU
    exact (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv U).injective (same U s t)

/-- The actual Cartier tensor isomorphism multiplies rational values
of the inserted pure tensors. -/
theorem cartierTensorSheafIso_value
    (D E : TauCeti.AlgebraicGeometry.Scheme.CartierDivisor X)
    (U : X.Opens) [Nonempty U] (s : Γ(D.sheaf, U)) (t : Γ(E.sheaf, U)) :
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv U
      (Scheme.Modules.Hom.app (D + E).sheafι U
        (Scheme.Modules.Hom.app
          (TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.tensorSheafIso D E).hom U
          (schemeTensorSection D.sheaf E.sheaf U s t))) =
      TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv U
          (Scheme.Modules.Hom.app D.sheafι U s) *
        TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv U
          (Scheme.Modules.Hom.app E.sheafι U t) := by
  rw [schemeTensorSection_eq_sheafification]
  simpa only [schemeHom_comp_apply] using
    TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.tensorSheafIso_hom_tmul_rationalValue
      D E U s t

/-- Transport along equality of actual Cartier divisors preserves their
specified rational-function inclusion. -/
theorem cartierEqToIso_value
    {D E : TauCeti.AlgebraicGeometry.Scheme.CartierDivisor X} (h : D = E)
    (U : X.Opens) (s : Γ(D.sheaf, U)) :
    Scheme.Modules.Hom.app E.sheafι U
      (Scheme.Modules.Hom.app
        (eqToIso (congrArg TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.sheaf h)).hom U s) =
      Scheme.Modules.Hom.app D.sheafι U s := by
  subst E
  rfl

end ActualTensorSections

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- The invariant-coefficient tensor comparison is genuine rational
multiplication, even though the equation character for `b+c` was chosen
independently of the characters for `b` and `c`. -/
theorem invariantCartierTensorIso_value (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b c : fan.Ray → ℤ)
    (U : fan.algebraicRealization.Opens) [Nonempty U]
    (s : letI := toricSchemeIntegral fan nonempty;
      Γ((invariantCartierDivisor fan nonempty regular b).sheaf, U))
    (t : letI := toricSchemeIntegral fan nonempty;
      Γ((invariantCartierDivisor fan nonempty regular c).sheaf, U)) :
    letI := toricSchemeIntegral fan nonempty
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv U
      (Scheme.Modules.Hom.app (invariantCartierDivisor fan nonempty regular (b+c)).sheafι U
        (Scheme.Modules.Hom.app (invariantCartierTensorIso fan nonempty regular b c).hom U
          (schemeTensorSection _ _ U s t))) =
      TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv U
          (Scheme.Modules.Hom.app (invariantCartierDivisor fan nonempty regular b).sheafι U s) *
        TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv U
          (Scheme.Modules.Hom.app (invariantCartierDivisor fan nonempty regular c).sheafι U t) := by
  letI := toricSchemeIntegral fan nonempty
  unfold invariantCartierTensorIso
  rw [Iso.trans_hom, schemeHom_comp_apply,
    cartierEqToIso_value (invariantCartierDivisor_add fan nonempty regular b c).symm]
  exact cartierTensorSheafIso_value _ _ U s t

/-- The ray inequality for the tensor character follows by adding the
two actual regularity inequalities. -/
theorem toricMonomialNonnegative_tensor (fan : Fan i) (b c d e : fan.Ray → ℤ)
    (m n : N →+ ℤ)
    (first : ∀ ρ, 0 ≤ c ρ - b ρ + m (fanRayPrimitiveGenerator fan ρ))
    (second : ∀ ρ, 0 ≤ e ρ - d ρ + n (fanRayPrimitiveGenerator fan ρ)) :
    ∀ ρ, 0 ≤ (c+e) ρ - (b+d) ρ + (m+n) (fanRayPrimitiveGenerator fan ρ) := by
  intro ρ
  have hfirst := first ρ
  have hsecond := second ρ
  simp only [Pi.add_apply, AddMonoidHom.add_apply]
  omega

/-- Tensoring the actual `χ^m` and `χ^n` sheaf maps is the actual
`χ^(m+n)` map after the genuine Cartier multiplication isomorphisms. -/
@[reassoc]
theorem toricCartierMonomialMap_tensor (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b c d e : fan.Ray → ℤ) (m n : N →+ ℤ)
    (first : ∀ ρ, 0 ≤ c ρ - b ρ + m (fanRayPrimitiveGenerator fan ρ))
    (second : ∀ ρ, 0 ≤ e ρ - d ρ + n (fanRayPrimitiveGenerator fan ρ)) :
    letI := toricSchemeIntegral fan nonempty
    (toricCartierMonomialMap fan nonempty regular b c m first ⊗ₘ
      toricCartierMonomialMap fan nonempty regular d e n second) ≫
        (invariantCartierTensorIso fan nonempty regular c e).hom =
    (invariantCartierTensorIso fan nonempty regular b d).hom ≫
      toricCartierMonomialMap fan nonempty regular (b+d) (c+e) (m+n)
        (toricMonomialNonnegative_tensor fan b c d e m n first second) := by
  letI := toricSchemeIntegral fan nonempty
  apply cartierTensorHom_ext_nonempty (invariantCartierDivisor fan nonempty regular (c+e))
  intro U hU s t
  simp only [schemeHom_comp_apply]
  rw [schemeTensorSection_naturality, invariantCartierTensorIso_value,
    toricCartierMonomialMap_value, toricCartierMonomialMap_value,
    toricCartierMonomialMap_value, invariantCartierTensorIso_value,
    rationalCharacterUnit_add, Units.val_mul]
  ring

end ToricPower
