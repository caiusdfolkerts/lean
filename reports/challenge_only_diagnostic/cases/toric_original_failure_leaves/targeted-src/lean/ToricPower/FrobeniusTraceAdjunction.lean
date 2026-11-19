module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Finite free trace pairings and the actual coextension functor

A perfect multiplication pairing identifies extension of scalars with
coextension of scalars. The resulting adjunction is the ordinary
restriction/coextension adjunction transported through this explicit
natural isomorphism. Its formula is retained on every pure tensor.

The trace-pairing hypothesis in this reusable algebraic result must be
proved for an application; the toric residue calculation supplies it.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Module ModuleCat
open scoped TensorProduct
open scoped ChangeOfRings

namespace ToricPower

section BasisPairing

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Multiplication followed by the actual chosen trace. -/
def multiplicationTracePairing (trace : S →ₗ[R] R) : S →ₗ[R] Module.Dual R S :=
  (LinearMap.mul R S).compr₂ trace

@[simp]
theorem multiplicationTracePairing_apply (trace : S →ₗ[R] R) (s t : S) :
    multiplicationTracePairing trace s t = trace (s*t) := rfl

/-- A permutation pairing on an actual finite basis proves perfectness. -/
def multiplicationTraceEquivOfBasis {I : Type*} [Fintype I] [DecidableEq I]
    (b : Basis I R S) (e : I ≃ I) (trace : S →ₗ[R] R)
    (pairing : ∀ i j, trace (b i * b j) = if e i = j then 1 else 0) :
    S ≃ₗ[R] Module.Dual R S :=
  LinearEquiv.ofBijective (multiplicationTracePairing trace) (by
    have equality : multiplicationTracePairing trace =
        (b.equiv b.dualBasis e).toLinearMap := by
      apply b.ext
      intro i
      apply b.ext
      intro j
      simp only [multiplicationTracePairing_apply, LinearEquiv.coe_coe,
        Basis.equiv_apply, Basis.dualBasis_apply, Basis.coord_apply,
        Basis.repr_self_apply, pairing]
      simp only [eq_comm]
    rw [equality]
    exact (b.equiv b.dualBasis e).bijective)

end BasisPairing

section Coextension

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

local notation "φ" => algebraMap R S

variable [Module.Finite R S] [Module.Projective R S]
  (trace : S →ₗ[R] R) (perfect : Function.Bijective (multiplicationTracePairing trace))

/-- The literal perfect trace pairing as an R-linear equivalence. -/
def multiplicationTraceEquiv : S ≃ₗ[R] Module.Dual R S :=
  LinearEquiv.ofBijective (multiplicationTracePairing trace) perfect

/-- Tensor-Hom comparison using the actual finite projective source. -/
def traceTensorHomEquiv (M : ModuleCat.{u} R) :
    S ⊗[R] M ≃ₗ[R] (S →ₗ[R] M) :=
  (TensorProduct.congr (multiplicationTraceEquiv trace perfect)
    (LinearEquiv.refl R M)).trans (dualTensorHomEquiv R S M)

@[simp]
theorem traceTensorHomEquiv_tmul (M : ModuleCat.{u} R) (s t : S) (m : M) :
    traceTensorHomEquiv trace perfect M (s ⊗ₜ[R] m) t = trace (s*t) • m := rfl

/-- Identity on elements identifies the two specified base-module structures. -/
def algebraRestrictionSelfLinearEquiv :
    (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S) ≃ₗ[R] S where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    let xS : S := x
    change algebraMap R S r * xS = r • xS
    exact (Algebra.smul_def r xS).symm

/-- The scalar adapters retain the literal functor carriers. -/
def traceTensorActualEquiv (M : ModuleCat.{u} R) :
    TensorProduct R ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)) M ≃ₗ[R]
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S) →ₗ[R] M) :=
  (TensorProduct.congr (algebraRestrictionSelfLinearEquiv (R := R) (S := S))
      (LinearEquiv.refl R M)).trans
    ((traceTensorHomEquiv trace perfect M).trans
      ((algebraRestrictionSelfLinearEquiv (R := R) (S := S)).arrowCongr
        (LinearEquiv.refl R M)).symm)

/-- The same map is S-linear for the genuine coextension scalar action. -/
def traceExtendCoextendLinearEquiv (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars φ).obj M ≃ₗ[S] (ModuleCat.coextendScalars φ).obj M :=
  { (traceTensorActualEquiv trace perfect M).toEquiv with
    map_add' x y := (traceTensorActualEquiv trace perfect M).map_add x y
    map_smul' a x := by
      change traceTensorActualEquiv trace perfect M (a • x) =
        a • (traceTensorActualEquiv trace perfect M x :
          (ModuleCat.coextendScalars φ).obj M)
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [smul_add, map_add, hx, hy]
      | tmul s m =>
          apply LinearMap.ext
          intro t
          change trace ((a*(show S from s))*(show S from t)) • m =
            trace ((show S from s)*((show S from t)*a)) • m
          rw [mul_assoc, mul_comm a ((show S from s)*(show S from t)), mul_assoc] }

@[simp]
theorem traceExtendCoextendLinearEquiv_tmul (M : ModuleCat.{u} R)
    (s t : S) (m : M) :
    (traceExtendCoextendLinearEquiv trace perfect M (s ⊗ₜ[R,φ] m)) t =
      trace (s*t) • m := rfl

/-- The finite trace identification is natural in every coefficient module. -/
def traceExtendCoextendIso : ModuleCat.extendScalars φ ≅ ModuleCat.coextendScalars φ :=
  NatIso.ofComponents
    (fun M => (traceExtendCoextendLinearEquiv trace perfect M).toModuleIso)
    (by
      intro M N f
      apply ModuleCat.ExtendScalars.hom_ext
      intro m
      apply LinearMap.ext
      intro s
      change trace (1*(show S from s)) • f m =
        f (trace (1*(show S from s)) • m)
      exact (f.hom.map_smul _ _).symm)

/-- Restriction of scalars is also left adjoint to extension through the
proved trace isomorphism. This is an actual adjunction of module functors. -/
def traceRestrictExtendAdjunction :
    ModuleCat.restrictScalars.{u} φ ⊣ ModuleCat.extendScalars φ :=
  (ModuleCat.restrictCoextendScalarsAdj φ).ofNatIsoRight
    (traceExtendCoextendIso trace perfect).symm

end Coextension

end ToricPower

end
