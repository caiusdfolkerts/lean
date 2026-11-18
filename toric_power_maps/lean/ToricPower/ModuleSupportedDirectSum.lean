module

public import ToricPower.ModuleDirectSumComplex
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# An unrestricted sum of actual one-dimensional supported modules

Chosen module isomorphisms on the supported indices, together with proved
zero objects elsewhere, identify the full direct sum with finite-support
coefficients on exactly those indices. The maps retain the literal
inclusions and coefficient-ring linearity.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower.SupportedDirectSum

variable (R : Type) [CommRing R] {U : Type} (M : U → ModuleCat.{0} R)
  (p : U → Prop) (e : ∀ u, p u → (M u ≅ ModuleCat.of R R))
  (zero : ∀ u, ¬p u → IsZero (M u))

def toCoefficients : (Π₀ u : U, M u) →ₗ[R] ({u : U // p u} →₀ R) :=
  DFinsupp.lsum R (fun u => if h : p u then
    (Finsupp.lsingle (R := R) (M := R) ⟨u,h⟩).comp (e u h).hom.hom else 0)

def fromCoefficients : ({u : U // p u} →₀ R) →ₗ[R] (Π₀ u : U, M u) :=
  Finsupp.lsum R (fun u =>
    (DFinsupp.lsingle (R := R) (M := fun v : U => ↑(M v)) u.val).comp (e u.val u.property).inv.hom)

@[simp]
theorem toCoefficients_single (u : U) (h : p u) (v : M u) :
    toCoefficients R M p e (DFinsupp.single u v) =
      Finsupp.single ⟨u,h⟩ ((e u h).hom v) := by
  unfold toCoefficients
  rw [DFinsupp.lsum_single, dif_pos h]
  rfl

@[simp]
theorem toCoefficients_single_of_not (u : U) (h : ¬p u) (v : M u) :
    toCoefficients R M p e (DFinsupp.single u v) = 0 := by
  unfold toCoefficients
  rw [DFinsupp.lsum_single, dif_neg h]
  rfl

@[simp]
theorem fromCoefficients_single (u : {u : U // p u}) (r : R) :
    fromCoefficients R M p e (Finsupp.single u r) =
      DFinsupp.single u.val ((e u.val u.property).inv r) := by
  unfold fromCoefficients
  rw [Finsupp.lsum_single]
  rfl

/-- The maps are mutually inverse on the actual unrestricted sum. -/
def linearEquiv : (Π₀ u : U, M u) ≃ₗ[R] ({u : U // p u} →₀ R) :=
  { toCoefficients R M p e with
    invFun := fromCoefficients R M p e
    left_inv := by
      have inverse : (fromCoefficients R M p e).comp (toCoefficients R M p e) =
          LinearMap.id := by
        apply DFinsupp.lhom_ext
        intro u v
        change fromCoefficients R M p e (toCoefficients R M p e (DFinsupp.single u v)) =
          DFinsupp.single u v
        by_cases h : p u
        · rw [toCoefficients_single R M p e u h, fromCoefficients_single]
          exact congrArg (DFinsupp.single u) (ConcreteCategory.congr_hom (e u h).hom_inv_id v)
        · rw [toCoefficients_single_of_not R M p e u h, map_zero]
          haveI : Subsingleton (M u) := ModuleCat.subsingleton_of_isZero (zero u h)
          rw [Subsingleton.elim v 0, DFinsupp.single_zero]
      exact fun v => DFunLike.congr_fun inverse v
    right_inv := by
      have inverse : (toCoefficients R M p e).comp (fromCoefficients R M p e) =
          LinearMap.id := by
        apply Finsupp.lhom_ext
        intro u r
        change toCoefficients R M p e (fromCoefficients R M p e (Finsupp.single u r)) =
          Finsupp.single u r
        rw [fromCoefficients_single, toCoefficients_single R M p e u.val u.property]
        exact congrArg (Finsupp.single u)
          (ConcreteCategory.congr_hom (e u.val u.property).inv_hom_id r)
      exact fun v => DFunLike.congr_fun inverse v }

/-- The supported decomposition is an actual coefficient-ring module
isomorphism. -/
def iso : ModuleCat.of R (Π₀ u : U, M u) ≅ ModuleCat.of R ({u : U // p u} →₀ R) :=
  (linearEquiv R M p e zero).toModuleIso

@[reassoc]
theorem iso_inclusion (u : U) (h : p u) :
    ModuleCat.ofHom (DFinsupp.lsingle (R := R) (M := fun v : U => ↑(M v)) u) ≫
        (iso R M p e zero).hom =
      (e u h).hom ≫ ModuleCat.ofHom (Finsupp.lsingle (R := R) (M := R) ⟨u,h⟩) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  exact toCoefficients_single R M p e u h v

end ToricPower.SupportedDirectSum
