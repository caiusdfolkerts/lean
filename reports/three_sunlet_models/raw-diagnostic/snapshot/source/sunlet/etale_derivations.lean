module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Etale.Field

/-! Derivations extend uniquely through formally étale algebras.
This is the infinitesimal lifting input for the generic contact argument. The
extension is constructed from the universal module of Kähler differentials.
-/

@[expose] public section
noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 600000

namespace Sunlet.EtaleDerivations

variable {R S T M : Type*}
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable [AddCommGroup M] [Module R M] [Module S M] [Module T M]
variable [IsScalarTower R S M] [IsScalarTower R T M] [IsScalarTower S T M]
variable [Algebra.FormallyEtale S T]

/-- The canonical extension of a derivation through a formally étale algebra. -/
def extend (D : Derivation R S M) : Derivation R T M :=
  ((D.liftKaehlerDifferential.liftBaseChange T).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).symm.toLinearMap).compDer
      (KaehlerDifferential.D R T)

@[simp] theorem extend_algebraMap (D : Derivation R S M) (s : S) :
    extend (T := T) D (algebraMap S T s) = D s := by
  change D.liftKaehlerDifferential.liftBaseChange T
    ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).symm
      (KaehlerDifferential.D R T (algebraMap S T s))) = D s
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
  simp

@[simp] theorem extend_compAlgebraMap (D : Derivation R S M) :
    (extend (T := T) D).compAlgebraMap S = D := by
  apply Derivation.ext
  intro s
  change extend (T := T) D (algebraMap S T s) = D s
  exact extend_algebraMap (T := T) D s

/-- An étale extension is already determined on the base algebra. -/
theorem ext {D E : Derivation R T M}
    (h : ∀ s, D (algebraMap S T s) = E (algebraMap S T s)) : D = E := by
  have hl : D.liftKaehlerDifferential = E.liftKaehlerDifferential := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ :=
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).surjective x
    induction y using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul t y =>
      have hm :
          (D.liftKaehlerDifferential.restrictScalars S).comp (KaehlerDifferential.map R R S T) =
          (E.liftKaehlerDifferential.restrictScalars S).comp (KaehlerDifferential.map R R S T) := by
        apply Derivation.liftKaehlerDifferential_unique
        apply Derivation.ext
        intro s
        change D.liftKaehlerDifferential
          (KaehlerDifferential.map R R S T (KaehlerDifferential.D R S s)) =
          E.liftKaehlerDifferential
          (KaehlerDifferential.map R R S T (KaehlerDifferential.D R S s))
        simpa only [KaehlerDifferential.map_D, Derivation.liftKaehlerDifferential_comp_D] using h s
      have he := LinearMap.congr_fun hm y
      simpa [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
        KaehlerDifferential.mapBaseChange_tmul] using congrArg (fun z : M => t • z) he
  apply Derivation.ext
  intro t
  simpa using LinearMap.congr_fun hl (KaehlerDifferential.D R T t)

theorem extend_unique (D : Derivation R S M) (E : Derivation R T M)
    (h : ∀ s, E (algebraMap S T s) = D s) : E = extend (T := T) D := by
  apply ext (S := S)
  intro s
  rw [extend_algebraMap]
  exact h s

end Sunlet.EtaleDerivations
