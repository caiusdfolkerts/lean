module

public import PaperVerification.EulerReduction
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Euler reduction when the coefficient map has zero kernel

The defect below is the actual quotient of the coefficient image by its hit
relations. Multiplication by the potential gives a canonical equivalence with
the cokernel of the scalar Euler operator. No finite-dimensional truncation,
rank premise, or choice of a complement is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.EulerInjective

open EulerReduction

variable {K U V W : Type*} [Field K]
variable [AddCommGroup U] [Module K U]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

def hit (C : U →ₗ[K] V) (D : U →ₗ[K] W) (L : W →ₗ[K] V) (t : K) :
    Submodule K V := LinearMap.range (perturbed C D L t)

/-- The paper's quotient `J/H`, with the relations pulled back to `J`. -/
abbrev Defect (C : U →ₗ[K] V) (D : U →ₗ[K] W) (L : W →ₗ[K] V) (t : K) :=
  LinearMap.range C ⧸ (hit C D L t).comap (LinearMap.range C).subtype

def defectImage (C : U →ₗ[K] V) (D : U →ₗ[K] W) (L : W →ₗ[K] V) (t : K) :
    Submodule K (V ⧸ hit C D L t) :=
  (LinearMap.range C).map (hit C D L t).mkQ

def defectToQuotient (C : U →ₗ[K] V) (D : U →ₗ[K] W)
    (L : W →ₗ[K] V) (t : K) :
    LinearMap.range C →ₗ[K] (V ⧸ hit C D L t) :=
  (hit C D L t).mkQ.comp (LinearMap.range C).subtype

theorem defectToQuotient_kernel (C : U →ₗ[K] V) (D : U →ₗ[K] W)
    (L : W →ₗ[K] V) (t : K) :
    LinearMap.ker (defectToQuotient C D L t) =
      (hit C D L t).comap (LinearMap.range C).subtype := by
  ext x
  change (hit C D L t).mkQ (x : V) = 0 ↔ _
  simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap, Submodule.subtype_apply]

theorem defectToQuotient_range (C : U →ₗ[K] V) (D : U →ₗ[K] W)
    (L : W →ₗ[K] V) (t : K) :
    LinearMap.range (defectToQuotient C D L t) = defectImage C D L t := by
  rw [defectToQuotient, LinearMap.range_comp, Submodule.range_subtype, defectImage]

def defectEquivImage (C : U →ₗ[K] V) (D : U →ₗ[K] W)
    (L : W →ₗ[K] V) (t : K) : Defect C D L t ≃ₗ[K] defectImage C D L t :=
  (Submodule.quotEquivOfEq _ _ (defectToQuotient_kernel C D L t).symm).trans
    ((defectToQuotient C D L t).quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ (defectToQuotient_range C D L t)))

def potentialMap (C : U →ₗ[K] V) (D : U →ₗ[K] W) (L : W →ₗ[K] V) (t : K) :
    W →ₗ[K] (V ⧸ hit C D L t) := (hit C D L t).mkQ.comp L

theorem hit_le_coefficient (C : U →ₗ[K] V) (D : U →ₗ[K] W)
    (E : W →ₗ[K] U) (L : W →ₗ[K] V) (t : K) (hE : C.comp E = L) :
    hit C D L t ≤ LinearMap.range C := by
  rw [EulerReduction.coefficient_range C D E L t hE]
  exact le_sup_left

theorem potentialMap_range (C : U →ₗ[K] V) (D : U →ₗ[K] W)
    (E : W →ₗ[K] U) (L : W →ₗ[K] V) (t : K) (hE : C.comp E = L) :
    LinearMap.range (potentialMap C D L t) = defectImage C D L t := by
  rw [potentialMap, LinearMap.range_comp, defectImage,
    EulerReduction.coefficient_range C D E L t hE,
    Submodule.map_sup]
  change (LinearMap.range L).map (hit C D L t).mkQ =
    (hit C D L t).map (hit C D L t).mkQ ⊔
      (LinearMap.range L).map (hit C D L t).mkQ
  rw [Submodule.mkQ_map_self, bot_sup_eq]

theorem potentialMap_kernel (C : U →ₗ[K] V) (D : U →ₗ[K] W)
    (E : W →ₗ[K] U) (L : W →ₗ[K] V) (t : K)
    (hE : C.comp E = L) (hC : Function.Injective C) :
    LinearMap.ker (potentialMap C D L t) = LinearMap.range (eulerScalar D E t) := by
  change LinearMap.ker ((LinearMap.range (perturbed C D L t)).mkQ.comp L) = _
  rw [EulerReduction.potential_quotient_kernel C D E L t hE,
    LinearMap.ker_eq_bot.mpr hC, Submodule.map_bot, sup_bot_eq]

/-- The canonical potential map identifies its exact scalar cokernel with
the full coefficient-image defect. -/
def potentialEquiv (C : U →ₗ[K] V) (D : U →ₗ[K] W)
    (E : W →ₗ[K] U) (L : W →ₗ[K] V) (t : K)
    (hE : C.comp E = L) (hC : Function.Injective C) :
    (W ⧸ LinearMap.range (eulerScalar D E t)) ≃ₗ[K] Defect C D L t :=
  (Submodule.quotEquivOfEq _ _ (potentialMap_kernel C D E L t hE hC).symm).trans
    ((potentialMap C D L t).quotKerEquivRange.trans
      ((LinearEquiv.ofEq _ _ (potentialMap_range C D E L t hE)).trans
        (defectEquivImage C D L t).symm))

/-- The equivalence is induced by the displayed potential map, rather than
by an unspecified vector-space isomorphism. -/
theorem potentialEquiv_mk (C : U →ₗ[K] V) (D : U →ₗ[K] W)
    (E : W →ₗ[K] U) (L : W →ₗ[K] V) (t : K)
    (hE : C.comp E = L) (hC : Function.Injective C) (w : W) :
    ((defectEquivImage C D L t)
      (potentialEquiv C D E L t hE hC
        ((LinearMap.range (eulerScalar D E t)).mkQ w)) : V ⧸ hit C D L t) =
      (hit C D L t).mkQ (L w) := by
  simp only [potentialEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

/-- Away from scalar Euler resonance, the hit space equals the full
coefficient image. This statement does not even require injectivity of `C`. -/
theorem hit_eq_coefficient_of_surjective (C : U →ₗ[K] V) (D : U →ₗ[K] W)
    (E : W →ₗ[K] U) (L : W →ₗ[K] V) (t : K)
    (hE : C.comp E = L) (hs : Function.Surjective (eulerScalar D E t)) :
    hit C D L t = LinearMap.range C := by
  have hL : LinearMap.range L ≤ hit C D L t := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨v, hv⟩ := hs w
    refine ⟨E v, ?_⟩
    rw [EulerReduction.perturbed_euler C D E L t hE, hv]
  have he := EulerReduction.coefficient_range C D E L t hE
  change LinearMap.range C = hit C D L t ⊔ LinearMap.range L at he
  rw [sup_eq_left.mpr hL] at he
  exact he.symm

end PaperVerification.EulerInjective
