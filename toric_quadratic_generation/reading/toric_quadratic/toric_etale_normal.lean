module

public import Mathlib.RingTheory.Smooth.IntegralClosure
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

@[expose] public section

/-!
# Normality of an étale domain over a normal domain

Smooth base change commutes with integral closure. For an étale domain,
its generic fibre is a finite-dimensional domain over the fraction field,
and hence is itself a field. Its literal localization presentation then
identifies it as a fraction field of the original domain. This proves
absolute integral closedness without assuming it as an additional local
hypothesis on a smooth scheme.
-/

noncomputable section

namespace PaperVerification.ToricSchemes

open scoped TensorProduct nonZeroDivisors

variable (R S : Type*) [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] [Algebra R S]

/-- Flatness makes the image of every nonzero base element a nonzero
element of the domain upstairs. -/
theorem genericFibre_denominators [Module.Flat R S] :
    Algebra.algebraMapSubmonoid S R⁰ ≤ S⁰ := by
  exact map_le_nonZeroDivisors_of_injective (algebraMap R S)
    (FaithfulSMul.algebraMap_injective R S) le_rfl

/-- Relative normality in the genuine tensor-product generic fibre.
Surjectivity of the proved integral-closure comparison is essential here. -/
theorem integrallyClosedIn_genericFibre [IsIntegrallyClosed R]
    [Algebra.Smooth R S] :
    IsIntegrallyClosedIn S (S ⊗[R] FractionRing R) := by
  let F := FractionRing R
  let A := S ⊗[R] F
  have hM : Algebra.algebraMapSubmonoid S R⁰ ≤ S⁰ :=
    genericFibre_denominators R S
  apply isIntegrallyClosedIn_iff.mpr
  refine ⟨IsLocalization.injective A hM,?_⟩
  intro z hz
  obtain ⟨u,hu⟩ :=
    (TensorProduct.toIntegralClosure_bijective_of_smooth
      (R := R) (S := S) (B := F)).2 ⟨z,hz⟩
  have hφ : ∀ u : S ⊗[R] integralClosure R F,
      ∃ s : S, algebraMap S A s =
        ((TensorProduct.toIntegralClosure R S F) u : A) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => exact ⟨0,by simp⟩
    | add u v hu hv =>
        obtain ⟨s,hs⟩ := hu
        obtain ⟨t,ht⟩ := hv
        refine ⟨s+t,?_⟩
        simpa only [map_add,Subalgebra.coe_add,hs,ht]
    | tmul s c =>
        obtain ⟨r,hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
          (R := R) (K := F) c.2
        refine ⟨s * algebraMap R S r,?_⟩
        simp only [TensorProduct.toIntegralClosure,AlgHom.coe_codRestrict,
          Algebra.TensorProduct.map_tmul,AlgHom.id_apply,
          Algebra.TensorProduct.algebraMap_apply,Algebra.algebraMap_self,
          RingHom.id_apply]
        change (s * algebraMap R S r) ⊗ₜ[R] (1 : F) = s ⊗ₜ[R] (c : F)
        rw [← hr]
        calc
          (s * algebraMap R S r) ⊗ₜ[R] (1 : F) = (r • s) ⊗ₜ[R] (1 : F) := by
            rw [Algebra.smul_def,mul_comm]
          _ = s ⊗ₜ[R] (r • (1 : F)) := TensorProduct.smul_tmul r s (1 : F)
          _ = s ⊗ₜ[R] algebraMap R F r := by rw [Algebra.smul_def,mul_one]
  obtain ⟨s,hs⟩ := hφ u
  exact ⟨s,hs.trans (congrArg Subtype.val hu)⟩

/-- A domain that is étale over an integrally closed domain is integrally
closed. All normality of the upstairs ring is a conclusion. -/
theorem isIntegrallyClosed_of_etale [IsIntegrallyClosed R]
    [Algebra.Etale R S] : IsIntegrallyClosed S := by
  let F := FractionRing R
  let A := F ⊗[R] S
  letI : Algebra S A := Algebra.TensorProduct.rightAlgebra
  have hM : Algebra.algebraMapSubmonoid S R⁰ ≤ S⁰ :=
    genericFibre_denominators R S
  letI : IsLocalization (Algebra.algebraMapSubmonoid S R⁰) A :=
    IsLocalization.tensorRight (R := R) (S := S) F R⁰
  letI : IsDomain A := IsLocalization.isDomain_of_le_nonZeroDivisors A hM
  letI : Module.Finite F A := Algebra.FormallyUnramified.finite_of_free F A
  have hfield : IsField A :=
    isField_of_isIntegral_of_isField' (R := F) (S := A) (Field.toIsField F)
  letI : Field A := hfield.toField
  letI : FaithfulSMul S A := (faithfulSMul_iff_algebraMap_injective S A).mpr
    (IsLocalization.injective A hM)
  letI : IsFractionRing S A := by
    apply IsFractionRing.of_field S A
    intro z
    obtain ⟨s,m,hm⟩ := IsLocalization.exists_mk'_eq
      (Algebra.algebraMapSubmonoid S R⁰) z
    refine ⟨s,m,?_⟩
    rw [← hm]
    exact (eq_div_iff (IsLocalization.map_units A m).ne_zero).mpr
      (IsLocalization.mk'_spec A s m)
  let e : S ⊗[R] F ≃ₐ[S] A := Algebra.TensorProduct.commRight R S F
  have hnormal : IsIntegrallyClosedIn S A :=
    e.isIntegrallyClosedIn.mp (integrallyClosedIn_genericFibre R S)
  exact (isIntegrallyClosed_iff_isIntegrallyClosedIn A).mpr hnormal

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.isIntegrallyClosed_of_etale
