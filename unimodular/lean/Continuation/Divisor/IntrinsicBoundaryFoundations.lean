module

public import Continuation.Divisor.InvariantCurves
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.RingTheory.Smooth.IntegralClosure
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

/-! Exact selected normality and actual boundary-character foundations. Every retained theorem has its original complete proof. The selection avoids duplicate declarations owned by the already checked fan-scheme modules. -/

section Selected_ToricNormalHeightOne
section
-- BEGIN ToricNormalHeightOne



/-!
# A normal Noetherian domain is the intersection of its height-one local rings

The argument uses actual denominator ideals in the fraction field. A prime
denominator ideal has height one: the determinant trick supplies an element
whose principal ideal has that prime as a minimal prime. Associated primes
of the quotient of the fraction field by the ring then detect every rational
function that is not regular. No factoriality assumption is used.
-/

noncomputable section

namespace PaperVerification.ToricSchemes

open scoped nonZeroDivisors

variable (R K : Type*) [CommRing R] [Field K] [Algebra R K]
    [IsDomain R] [IsFractionRing R K]

/-- The actual image of the domain in its fraction field, as an `R`-module. -/
def fractionRingImage : Submodule R K :=
  LinearMap.range (Algebra.linearMap R K)

@[simp] theorem mem_fractionRingImage (z : K) :
    z ∈ fractionRingImage R K ↔ ∃ a : R, algebraMap R K a = z := Iff.rfl

/-- The ideal of denominators that clear the given rational function. -/
def fractionDenominatorIdeal (z : K) : Ideal R :=
  (fractionRingImage R K).colon {z}

@[simp] theorem mem_fractionDenominatorIdeal (z : K) (r : R) :
    r ∈ fractionDenominatorIdeal R K z ↔
      ∃ a : R, algebraMap R K a = algebraMap R K r * z := by
  rw [fractionDenominatorIdeal,Submodule.mem_colon_singleton]
  change (∃ a : R,algebraMap R K a = r • z) ↔ _
  rw [Algebra.smul_def]

theorem fractionDenominatorIdeal_eq_top_iff (z : K) :
    fractionDenominatorIdeal R K z = ⊤ ↔ z ∈ fractionRingImage R K := by
  rw [Ideal.eq_top_iff_one,mem_fractionDenominatorIdeal,mem_fractionRingImage]
  simp only [map_one,one_mul]

theorem fractionDenominatorIdeal_ne_bot (z : K) :
    fractionDenominatorIdeal R K z ≠ ⊥ := by
  obtain ⟨a,b,hb,hab⟩ := IsFractionRing.div_surjective R z
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap R K b ≠ 0 := by
    intro h
    apply hb0
    exact (IsFractionRing.injective R K) (by simpa only [map_zero] using h)
  have hbmem : b ∈ fractionDenominatorIdeal R K z := by
    apply (mem_fractionDenominatorIdeal R K z b).mpr
    refine ⟨a,?_⟩
    rw [← hab]
    field_simp
  intro h
  exact hb0 (by simpa only [h,Submodule.mem_bot] using hbmem)

variable [IsNoetherianRing R] [IsIntegrallyClosed R]

/-- A denominator ideal that is prime is necessarily a height-one prime.
The nontrivial step is the determinant trick on its actual image in `K`. -/
theorem fractionDenominatorIdeal_height_eq_one (z : K)
    (hprime : (fractionDenominatorIdeal R K z).IsPrime) :
    (fractionDenominatorIdeal R K z).height = 1 := by
  let P : Ideal R := fractionDenominatorIdeal R K z
  letI : P.IsPrime := hprime
  have hP0 : P ≠ ⊥ := fractionDenominatorIdeal_ne_bot R K z
  let N : Submodule R K := Submodule.map (Algebra.linearMap R K) (P : Submodule R R)
  have hN0 : N ≠ ⊥ := by
    intro hN
    apply hP0
    apply le_antisymm _ bot_le
    intro a ha
    have haK : algebraMap R K a ∈ N := Submodule.mem_map.mpr ⟨a,ha,rfl⟩
    have ha0 : algebraMap R K a = 0 := by simpa only [hN,Submodule.mem_bot] using haK
    change a = 0
    exact (IsFractionRing.injective R K) (by simpa only [map_zero] using ha0)
  have hNfg : N.FG := (IsNoetherian.noetherian P).map (Algebra.linearMap R K)
  have hnotstable : ¬ ∀ w ∈ N,z • w ∈ N := by
    intro hstable
    have hzint : IsIntegral R z :=
      isIntegral_of_smul_mem_submodule N hN0 hNfg z hstable
    obtain ⟨r,hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hzint
    apply hprime.ne_top
    exact (fractionDenominatorIdeal_eq_top_iff R K z).mpr ⟨r,hr⟩
  push_neg at hnotstable
  obtain ⟨w,hw,hnw⟩ := hnotstable
  obtain ⟨a,ha,rfl⟩ := Submodule.mem_map.mp hw
  obtain ⟨b,hb⟩ := (mem_fractionDenominatorIdeal R K z a).mp ha
  have hbP : b ∉ P := by
    intro hbmem
    apply hnw
    apply Submodule.mem_map.mpr
    refine ⟨b,hbmem,?_⟩
    change algebraMap R K b = z * algebraMap R K a
    simpa only [mul_comm] using hb
  have hminimal : P ∈ (Ideal.span {a}).minimalPrimes := by
    refine ⟨⟨hprime,(Ideal.span_singleton_le_iff_mem P).mpr ha⟩,?_⟩
    intro Q hQ hQP
    intro t ht
    obtain ⟨c,hc⟩ := (mem_fractionDenominatorIdeal R K z t).mp ht
    have hmul : b*t = a*c := by
      apply IsFractionRing.injective R K
      simp only [map_mul]
      rw [hb,hc]
      ring
    have haQ : a ∈ Q := hQ.2 (Ideal.subset_span (Set.mem_singleton a))
    have hbt : b*t ∈ Q := by
      rw [hmul]
      exact Q.mul_mem_right c haQ
    exact (hQ.1.mem_or_mem hbt).resolve_left (fun hbQ => hbP (hQP hbQ))
  apply le_antisymm
  · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
      (Ideal.span {a}) P hminimal
  · simpa only [Ideal.height_bot,zero_add] using
      Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hP0)

/-- The annihilator of a rational function modulo the ring is its actual
denominator ideal. -/
theorem fraction_quotient_annihilator (z : K) :
    (⊥ : Submodule R (K ⧸ fractionRingImage R K)).colon
        {(fractionRingImage R K).mkQ z} = fractionDenominatorIdeal R K z := by
  ext r
  rw [Submodule.mem_colon_singleton,Submodule.mem_bot,← map_smul]
  change ((Submodule.Quotient.mk (r • z) : K ⧸ fractionRingImage R K) = 0) ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  rw [fractionDenominatorIdeal,Submodule.mem_colon_singleton]

/-- If a rational function is not in the ring, a height-one prime contains
every denominator that would clear it. -/
theorem exists_heightOne_containing_denominators (z : K)
    (hz : z ∉ fractionRingImage R K) :
    ∃ P : Ideal R, P.IsPrime ∧ P.height = 1 ∧
      fractionDenominatorIdeal R K z ≤ P := by
  let M := K ⧸ fractionRingImage R K
  have hzQ : (fractionRingImage R K).mkQ z ≠ 0 := by
    intro h
    apply hz
    change (Submodule.Quotient.mk z : K ⧸ fractionRingImage R K) = 0 at h
    exact (Submodule.Quotient.mk_eq_zero (fractionRingImage R K)).mp h
  obtain ⟨P,hP,hzP⟩ :=
    exists_le_isAssociatedPrime_of_isNoetherianRing R
      ((fractionRingImage R K).mkQ z) hzQ
  obtain ⟨hp,y,hy⟩ := isAssociatedPrime_iff.mp hP
  obtain ⟨w,rfl⟩ := (fractionRingImage R K).mkQ_surjective y
  rw [fraction_quotient_annihilator] at hy hzP
  refine ⟨P,hp,?_,hzP⟩
  rw [hy]
  exact fractionDenominatorIdeal_height_eq_one R K w (hy ▸ hp)

/-- The actual localization at a prime, regarded as a subalgebra of the
given fraction field. -/
def heightOneLocalRing (P : Ideal R) [P.IsPrime] : Subalgebra R K :=
  Localization.subalgebra.ofField K P.primeCompl P.primeCompl_le_nonZeroDivisors

theorem mem_heightOneLocalRing_iff (P : Ideal R) [P.IsPrime] (z : K) :
    z ∈ heightOneLocalRing R K P ↔
      ∃ s : R, s ∉ P ∧ s ∈ fractionDenominatorIdeal R K z := by
  change (∃ a s : R, ∃ hs : s ∈ P.primeCompl,
    z = algebraMap R K a * (algebraMap R K s)⁻¹) ↔ _
  constructor
  · rintro ⟨a,s,hs,rfl⟩
    refine ⟨s,hs,(mem_fractionDenominatorIdeal R K _ _).mpr ⟨a,?_⟩⟩
    have hs0 : algebraMap R K s ≠ 0 := by
      intro h
      have hsR : s = 0 := (IsFractionRing.injective R K)
        (by simpa only [map_zero] using h)
      apply hs
      change s ∈ P
      simpa only [hsR] using P.zero_mem
    field_simp
  · rintro ⟨s,hs,hsz⟩
    obtain ⟨a,ha⟩ := (mem_fractionDenominatorIdeal R K z s).mp hsz
    refine ⟨a,s,hs,?_⟩
    have hs0 : algebraMap R K s ≠ 0 := by
      intro h
      have hsR : s = 0 := (IsFractionRing.injective R K)
        (by simpa only [map_zero] using h)
      apply hs
      change s ∈ P
      simpa only [hsR] using P.zero_mem
    rw [ha]
    field_simp

/-- This subalgebra is the range of any actual localization at the same
prime, when its map to the fraction field is the compatible algebra map. -/
theorem mem_heightOneLocalRing_iff_localization_range (P : Ideal R) [P.IsPrime]
    (A : Type*) [CommRing A] [Algebra R A] [IsLocalization.AtPrime A P]
    [Algebra A K] [IsScalarTower R A K] (z : K) :
    z ∈ heightOneLocalRing R K P ↔ z ∈ (algebraMap A K).range := by
  have hmap : Localization.mapToFractionRing K P.primeCompl A
      P.primeCompl_le_nonZeroDivisors = IsScalarTower.toAlgHom R A K := by
    apply IsLocalization.algHom_ext P.primeCompl
    ext r
  change z ∈ heightOneLocalRing R K P ↔ z ∈ (IsScalarTower.toAlgHom R A K).range
  rw [← hmap]
  exact (Localization.subalgebra.mem_range_mapToFractionRing_iff_ofField
    K P.primeCompl P.primeCompl_le_nonZeroDivisors A z).symm

/-- A normal Noetherian domain is exactly the intersection of its actual
localizations at all height-one primes, inside any of its fraction fields. -/
theorem mem_fractionRingImage_iff_heightOne (z : K) :
    z ∈ fractionRingImage R K ↔
      ∀ (P : Ideal R) (hP : P.IsPrime), P.height = 1 →
        z ∈ @heightOneLocalRing R K _ _ _ _ _ P hP := by
  constructor
  · rintro ⟨r,rfl⟩ P hP _
    letI : P.IsPrime := hP
    exact (heightOneLocalRing R K P).algebraMap_mem r
  · intro h
    by_contra hz
    obtain ⟨P,hP,hheight,hden⟩ := exists_heightOne_containing_denominators R K z hz
    letI : P.IsPrime := hP
    obtain ⟨s,hs,hsz⟩ := (mem_heightOneLocalRing_iff R K P z).mp (h P hP hheight)
    exact hs (hden hsz)

end PaperVerification.ToricSchemes
end
-- END ToricNormalHeightOne
end

end Selected_ToricNormalHeightOne

section Selected_ToricNormalOrders
section
-- BEGIN ToricNormalOrders



/-!
# Orders detect regularity in normal local rings of dimension one

These statements use Mathlib's actual local-ring order and the actual
generic stalk of a scheme. In particular, order zero is identified with
an honest unit of the local ring, not stipulated in a divisor definition.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory TopologicalSpace

/-- A normal Noetherian local domain of dimension one is a DVR. -/
theorem discreteValuationRing_of_normal_dimensionOne (A : Type*)
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (hdim : ringKrullDim A = 1) :
    IsDiscreteValuationRing A := by
  have hnf : ¬ IsField A := by
    intro hf
    have hzero := ringKrullDim_eq_zero_of_isField hf
    rw [hdim] at hzero
    exact one_ne_zero hzero
  letI : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr hdim.le
  apply ((IsDiscreteValuationRing.TFAE A hnf).out 1 4).mpr
  refine ⟨inferInstance,IsLocalRing.maximalIdeal A,⟨?_,inferInstance⟩,?_⟩
  · exact (IsLocalRing.isField_iff_maximalIdeal_eq).not.mp hnf
  · intro P hP
    exact IsLocalRing.eq_maximalIdeal (hP.2.isMaximal_of_ne_bot hP.1)

/-- The exact unit criterion for the actual order homomorphism of a DVR. -/
theorem ordFrac_eq_one_iff_unit (A K : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] (z : K) :
    Ring.ordFrac A z = 1 ↔ ∃ u : Aˣ, algebraMap A K (u : A) = z := by
  change z ∈ MonoidHom.mker (Ring.ordFrac A) ↔ _
  rw [Ring.mker_ordFrac_eq_isUnitSubmonoid]
  change (∃ a : A, IsUnit a ∧ algebraMap A K a = z) ↔ _
  constructor
  · rintro ⟨a,⟨u,rfl⟩,ha⟩
    exact ⟨u,ha⟩
  · rintro ⟨u,hu⟩
    exact ⟨u,u.isUnit,hu⟩

/-- Nonnegative additive order is equivalent to actual regularity in a
DVR; in multiplicative notation this is the inequality `1 ≤ ordFrac`. -/
theorem one_le_ordFrac_iff_regular (A K : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (z : K) (hz : z ≠ 0) :
    1 ≤ Ring.ordFrac A z ↔ ∃ a : A, algebraMap A K a = z := by
  constructor
  · intro h
    rw [Ring.ordFrac_eq_valuation_inv] at h
    have hv0 : 0 < (IsDiscreteValuationRing.maximalIdeal A).valuation K z :=
      zero_lt_iff.mpr ((map_ne_zero _).mpr hz)
    exact IsDiscreteValuationRing.exists_lift_of_le_one ((one_le_inv₀ hv0).mp h)
  · rintro ⟨a,rfl⟩
    apply Ring.ordFrac_ge_one_of_ne_zero
    intro ha
    apply hz
    simp [ha]

section Schemes

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

theorem normal_codimensionOne_stalk_isDVR (x : X)
    [IsIntegrallyClosed (X.presheaf.stalk x)]
    (hx : Order.coheight x = 1) : IsDiscreteValuationRing (X.presheaf.stalk x) := by
  apply discreteValuationRing_of_normal_dimensionOne
  rw [ringKrullDim_stalk_eq_coheight,hx]
  rfl

/-- A nonzero rational function has order zero at a normal codimension-one
point exactly when it is the image of an actual unit of the stalk. -/
theorem rationalOrder_zero_iff_stalkUnit (x : X)
    [IsIntegrallyClosed (X.presheaf.stalk x)] (hx : Order.coheight x = 1)
    (z : X.functionField) (hz : z ≠ 0) :
    X.ord z x = 0 ↔
      ∃ u : (X.presheaf.stalk x)ˣ,
        algebraMap (X.presheaf.stalk x) X.functionField (u : X.presheaf.stalk x) = z := by
  letI := normal_codimensionOne_stalk_isDVR x hx
  rw [X.ord_eq_iff hx hz]
  change Ring.ordFrac (X.presheaf.stalk x) z = 1 ↔ _
  exact ordFrac_eq_one_iff_unit _ _ z

/-- The sign of the actual local order detects membership in the actual
local ring, under the proved normality and codimension hypotheses. -/
theorem rationalOrder_nonnegative_iff_regularAt (x : X)
    [IsIntegrallyClosed (X.presheaf.stalk x)] (hx : Order.coheight x = 1)
    (z : X.functionField) (hz : z ≠ 0) :
    0 ≤ X.ord z x ↔ z ∈ regularAtSubring X x := by
  letI := normal_codimensionOne_stalk_isDVR x hx
  rw [X.le_ord_iff hx hz]
  change 1 ≤ Ring.ordFrac (X.presheaf.stalk x) z ↔ _
  exact one_le_ordFrac_iff_regular _ _ z hz

end Schemes

end PaperVerification.ToricSchemes
end
-- END ToricNormalOrders
end

end Selected_ToricNormalOrders

section Selected_ToricEtaleNormal
section
-- BEGIN ToricEtaleNormal



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

end
-- END ToricEtaleNormal
end

end Selected_ToricEtaleNormal

section Selected_ToricSmoothNormal
section
-- BEGIN ToricSmoothNormal



/-!
# Integral closedness derived from ordinary smoothness

The local presentation theorem for smooth algebras gives standard étale
charts over polynomial rings. The preceding étale result proves integral
closedness on these charts. Localization and the actual local criterion
then prove it for the original algebra. On an integral scheme smooth over
a field, this applies to every affine coordinate ring and every actual
stalk. Normality is consequently a conclusion, not an additional input.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory
open scoped nonZeroDivisors

variable (k S : Type*) [Field k] [CommRing S] [IsDomain S]
    [Algebra k S] [Algebra.Smooth k S]

include k

/-- Every prime has a genuine principal neighborhood with integrally
closed coordinate ring. The local algebra structure over a polynomial
ring is supplied by the smooth local presentation theorem. -/
theorem exists_integrallyClosed_away_of_smooth (p : Ideal S) [p.IsPrime] :
    ∃ f : S, f ∉ p ∧ IsIntegrallyClosed (Localization.Away f) := by
  obtain ⟨f,hfp,n,ha,ht,he⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := p)
  letI : Algebra (MvPolynomial (Fin n) k) (Localization.Away f) := ha
  letI : IsScalarTower k (MvPolynomial (Fin n) k) (Localization.Away f) := ht
  letI : Algebra.IsStandardEtale (MvPolynomial (Fin n) k) (Localization.Away f) := he
  have hf : f ≠ 0 := fun h => hfp (h ▸ p.zero_mem)
  letI : IsDomain (Localization.Away f) := Localization.Away.isDomain hf
  exact ⟨f,hfp,isIntegrallyClosed_of_etale
    (MvPolynomial (Fin n) k) (Localization.Away f)⟩

/-- Normality of a smooth affine integral algebra, with no normality or
regularity hypothesis on that algebra. -/
theorem isIntegrallyClosed_of_smooth_field : IsIntegrallyClosed S := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro p hp0 hp
  obtain ⟨f,hfp,hfNormal⟩ := exists_integrallyClosed_away_of_smooth k S p
  have hf : f ≠ 0 := fun h => hfp (h ▸ p.zero_mem)
  let A := Localization.Away f
  letI : IsDomain A := Localization.Away.isDomain hf
  letI : IsIntegrallyClosed A := hfNormal
  have hdis : Disjoint (Submonoid.powers f : Set S) (p : Set S) := by
    exact (Ideal.disjoint_powers_iff_notMem_of_isPrime (I := p) f).mpr hfp
  let q : Ideal A := p.map (algebraMap S A)
  letI : q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) A p
      inferInstance hdis
  have hq : q.comap (algebraMap S A) = p :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f) A
      inferInstance hdis
  letI : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime q)
      q.primeCompl q.primeCompl_le_nonZeroDivisors
  let e := IsLocalization.localizationLocalizationAtPrimeIsoLocalization
    (Submonoid.powers f) q
  have hn : IsIntegrallyClosed (Localization.AtPrime (q.comap (algebraMap S A))) :=
    (inferInstance : IsIntegrallyClosed (Localization.AtPrime q)).of_equiv
      e.symm.toRingEquiv
  let p' : PrimeSpectrum S := ⟨q.comap (algebraMap S A),inferInstance⟩
  let p₀ : PrimeSpectrum S := ⟨p,inferInstance⟩
  have hpEq : p'=p₀ := PrimeSpectrum.ext hq
  exact (congrArg
    (fun z : PrimeSpectrum S => IsIntegrallyClosed (Localization.AtPrime z.asIdeal))
    hpEq).mp hn

omit k

section Schemes

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [Smooth f]

include f

/-- The actual ring of functions on each nonempty affine open of an
integral scheme smooth over a field is integrally closed. -/
theorem smooth_affineOpen_isIntegrallyClosed (U : X.Opens)
    (hU : IsAffineOpen U) [Nonempty U] : IsIntegrallyClosed Γ(X,U) := by
  let R := Γ(Spec (.of k),⊤)
  let e : R ≃+* k := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv
  letI : Field R := (e.isField (Field.toIsField k)).toField
  have hpre : U ≤ f ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) := by simp
  letI : Algebra R Γ(X,U) := (f.appLE ⊤ U hpre).hom.toAlgebra
  letI : Algebra.Smooth R Γ(X,U) :=
    (f.smooth_appLE (isAffineOpen_top _) hU hpre).toAlgebra
  exact isIntegrallyClosed_of_smooth_field R Γ(X,U)

/-- Integral closedness of each literal local ring follows from an actual
affine neighborhood and the stalk localization theorem. -/
theorem smooth_stalk_isIntegrallyClosed (x : X) :
    IsIntegrallyClosed (X.presheaf.stalk x) := by
  obtain ⟨_,⟨U,hU,rfl⟩,hxU,-⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
  letI : Nonempty U := ⟨⟨x,hxU⟩⟩
  letI : IsIntegrallyClosed Γ(X,U) := smooth_affineOpen_isIntegrallyClosed f U hU
  letI : Algebra Γ(X,U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x,hxU⟩
  let p := hU.primeIdealOf ⟨x,hxU⟩
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    hU.isLocalization_stalk ⟨x,hxU⟩
  exact isIntegrallyClosed_of_isLocalization (X.presheaf.stalk x)
    p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors

end Schemes

end PaperVerification.ToricSchemes

end
-- END ToricSmoothNormal
end

end Selected_ToricSmoothNormal

section Selected_ToricNormalCartier
section
-- BEGIN ToricNormalCartier



/-!
# Cartier divisors are detected by their genuine Weil orders on smooth schemes

Normality is derived from ordinary smoothness over the ground field. The
height-one intersection theorem is applied to actual affine coordinate
rings and their actual stalk localizations. Thus the resulting injectivity
statement concerns actual invertible fractional sheaves on the scheme.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace PaperVerification.ToricSchemes

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- On a normal affine open, regularity is detected at the actual points
of codimension one in that open. -/
theorem normalAffine_regular_iff_codimensionOne (U : X.Opens)
    (hU : IsAffineOpen U) [Nonempty U] [IsIntegrallyClosed Γ(X,U)]
    (z : X.functionField) :
    z ∈ (X.germToFunctionField U).hom.range ↔
      ∀ x∈U, Order.coheight x = 1 → z∈regularAtSubring X x := by
  let R := Γ(X,U)
  letI : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U,hU⟩
  letI : IsFractionRing R X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  constructor
  · rintro ⟨s,rfl⟩ x hx _
    exact regular_germ_mem_regularAt X U s x hx
  · intro h
    change z ∈ fractionRingImage R X.functionField
    apply (mem_fractionRingImage_iff_heightOne R X.functionField z).mpr
    intro P hP hheight
    letI : P.IsPrime := hP
    let p : Spec (.of R) := ⟨P,hP⟩
    let x : X := hU.fromSpec p
    have hxU : x∈U := by
      change x ∈ (U : Set X)
      rw [← hU.range_fromSpec]
      exact ⟨p,rfl⟩
    have hxheight : Order.coheight x = 1 := by
      calc
        Order.coheight x = Order.coheight p :=
          coheight_eq_of_isOpenImmersion hU.fromSpec
        _ = P.height := (idealHeight_eq_coheight (.of R) p).symm
        _ = 1 := hheight
    letI : Algebra R (X.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x,hxU⟩
    letI : IsLocalization.AtPrime (X.presheaf.stalk x) P :=
      hU.isLocalization_stalk' p hxU
    letI : IsScalarTower R (X.presheaf.stalk x) X.functionField :=
      functionField_isScalarTower X U ⟨x,hxU⟩
    exact (mem_heightOneLocalRing_iff_localization_range R X.functionField
      P (X.presheaf.stalk x) z).mpr (h x hxU hxheight)

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [Smooth f]

include f

/-- A nonzero rational function on a smooth integral scheme is regular on
an arbitrary open exactly when its orders are nonnegative there. -/
theorem smooth_regular_range_iff_orders (U : X.Opens) [Nonempty U]
    (z : X.functionField) (hz : z ≠ 0) :
    z ∈ (X.germToFunctionField U).hom.range ↔
      ∀ x∈U, 0 ≤ X.ord z x := by
  constructor
  · rintro ⟨s,rfl⟩ x hx
    by_cases hcodim : Order.coheight x=1
    · letI : IsIntegrallyClosed (X.presheaf.stalk x) :=
        smooth_stalk_isIntegrallyClosed f x
      exact (rationalOrder_nonnegative_iff_regularAt x hcodim _ hz).mpr
        (regular_germ_mem_regularAt X U s x hx)
    · simp [Scheme.ord_eq_zero_of_coheight_neq_one hcodim]
  · intro h
    apply (mem_regular_range_iff_stalkwise X U z).mpr
    intro x hx
    obtain ⟨V,hV,hxV,hVU⟩ := exists_isAffineOpen_mem_and_subset (x := x) hx
    letI : Nonempty V := ⟨⟨x,hxV⟩⟩
    letI : IsIntegrallyClosed Γ(X,V) :=
      smooth_affineOpen_isIntegrallyClosed f V hV
    have hzV : z∈(X.germToFunctionField V).hom.range := by
      apply (normalAffine_regular_iff_codimensionOne V hV z).mpr
      intro y hy hcodim
      letI : IsIntegrallyClosed (X.presheaf.stalk y) :=
        smooth_stalk_isIntegrallyClosed f y
      exact (rationalOrder_nonnegative_iff_regularAt y hcodim z hz).mp
        (h y (hVU hy))
    obtain ⟨s,hs⟩ := hzV
    rw [← hs]
    exact regular_germ_mem_regularAt X V s x hxV

/-- Vanishing of every genuine Weil order is equivalent to a genuine
regular unit on the open, including nonaffine opens. -/
theorem smooth_regular_unit_iff_orders_zero (U : X.Opens) [Nonempty U]
    (z : X.functionField) (hz : z ≠ 0) :
    (∃ a : Γ(X,U)ˣ,X.germToFunctionField U (a : Γ(X,U))=z) ↔
      ∀ x∈U,X.ord z x=0 := by
  constructor
  · rintro ⟨a,rfl⟩ x hx
    exact X.ord_of_isUnit a.isUnit hx
  · intro h
    have hpos : z∈(X.germToFunctionField U).hom.range :=
      (smooth_regular_range_iff_orders f U z hz).mpr
        (fun x hx => (h x hx).ge)
    have hneg : z⁻¹∈(X.germToFunctionField U).hom.range := by
      apply (smooth_regular_range_iff_orders f U z⁻¹ (inv_ne_zero hz)).mpr
      intro x hx
      rw [rationalOrder_inv hz,h x hx,neg_zero]
    obtain ⟨a,ha⟩ := hpos
    obtain ⟨b,hb⟩ := hneg
    have hab : a*b=1 := by
      apply X.germToFunctionField_injective U
      rw [map_mul,map_one,ha,hb,mul_inv_cancel₀ hz]
    exact ⟨⟨a,b,hab,by simpa only [mul_comm] using hab⟩,ha⟩

namespace CartierData

/-- Equality of the actual Weil coefficients forces equality of Cartier
divisors as embedded fractional sheaves. Normality is a theorem here,
derived from smoothness, not an additional input about the scheme. -/
theorem equivalent_of_weilCoefficient_eq (D E : CartierData X)
    (hcoeff : D.weilCoefficient = E.weilCoefficient) : D.Equivalent E := by
  let C := D.localCocycle
  let B := E.localCocycle
  have hratios : C.GeneratorRatioRegular B ∧ B.GeneratorRatioRegular C := by
    have hunit : ∀ (i : C.index) (j : B.index)
        (V : X.Opens) [Nonempty V], V≤C.openSet i⊓B.openSet j →
        ∃ a : Γ(X,V)ˣ, X.germToFunctionField V (a : Γ(X,V)) =
          (C.generator i : X.functionField)/(B.generator j : X.functionField) := by
      intro i j V hV hsub
      letI := hV
      letI : Nonempty (invertibleOpen D.locallyFree i) :=
        ⟨⟨i,mem_invertibleOpen D.locallyFree i⟩⟩
      letI : Nonempty (invertibleOpen E.locallyFree j) :=
        ⟨⟨j,mem_invertibleOpen E.locallyFree j⟩⟩
      apply (smooth_regular_unit_iff_orders_zero f V _
        (div_ne_zero (C.generator i).ne_zero (B.generator j).ne_zero)).mpr
      intro x hx
      rw [rationalOrder_div (C.generator i).ne_zero (B.generator j).ne_zero]
      have heq := congrFun hcoeff x
      rw [D.weilCoefficient_eq_neg_frameOrder
          (invertibleFrame D.locallyFree i) (hsub hx).1,
        E.weilCoefficient_eq_neg_frameOrder
          (invertibleFrame E.locallyFree j) (hsub hx).2] at heq
      change -X.ord (C.generator i : X.functionField) x =
        -X.ord (B.generator j : X.functionField) x at heq
      omega
    constructor
    · intro i j x hxi hxj
      let V := C.openSet i⊓B.openSet j
      letI : Nonempty V := ⟨⟨x,hxi,hxj⟩⟩
      obtain ⟨a,ha⟩ := hunit i j V le_rfl
      rw [← ha]
      exact regular_germ_mem_regularAt X V a x ⟨hxi,hxj⟩
    · intro j i x hxj hxi
      let V := C.openSet i⊓B.openSet j
      letI : Nonempty V := ⟨⟨x,hxi,hxj⟩⟩
      obtain ⟨a,ha⟩ := hunit i j V le_rfl
      have hinv : X.germToFunctionField V ((a⁻¹ : Γ(X,V)ˣ) : Γ(X,V)) =
          (B.generator j : X.functionField)/(C.generator i : X.functionField) := by
        have hmul := congrArg (X.germToFunctionField V) a.val_inv
        rw [map_mul,map_one,ha] at hmul
        change (C.generator i : X.functionField) / (B.generator j : X.functionField) *
          X.germToFunctionField V ((a⁻¹ : Γ(X,V)ˣ) : Γ(X,V)) = 1 at hmul
        apply mul_left_cancel₀
          (div_ne_zero (C.generator i).ne_zero (B.generator j).ne_zero)
        rw [hmul]
        field_simp
      rw [← hinv]
      exact regular_germ_mem_regularAt X V (a⁻¹ : Γ(X,V)ˣ) x ⟨hxi,hxj⟩
  exact D.equivalent_trans B.toCartierData E
    (D.equivalent_trans C.toCartierData B.toCartierData
      D.equivalent_localCocycle
      (C.equivalent_of_generatorRatios B hratios.1 hratios.2))
    (E.equivalent_symm B.toCartierData E.equivalent_localCocycle)

end CartierData

end PaperVerification.ToricSchemes
end
-- END ToricNormalCartier
end

end Selected_ToricNormalCartier

section Selected_ActualSplitTorusIntegral
section
-- BEGIN ToricTorusGeometricIntegral



/-!
# Geometric integrality of the actual split torus

The proof uses arbitrary field-valued base changes of schemes.  It makes
no appeal to the density of rational points.  The affine coordinate-ring
calculation is the literal scalar extension of the group algebra.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Limits
open PaperVerification.ToricCharacters
open scoped TensorProduct

variable (k : Type u) [Field k] (n : ℕ)

instance splitTorus_integral : IsIntegral (splitTorus k (Fin n→ℤ)) := by
  letI := torusCoordinateRing_isDomain k n
  change IsIntegral (Spec (CommRingCat.of (torusCoordinateRing k n)))
  infer_instance


instance splitTorusOver_integral : IsIntegral (splitTorusOver k (Fin n → ℤ)).left := by
  change IsIntegral (splitTorus k (Fin n → ℤ))
  infer_instance
end PaperVerification.ToricSchemes
end
end
end Selected_ActualSplitTorusIntegral

section Selected_ActualRegularUnitOrder
section
-- BEGIN ToricCartierBoundaryInvariance



/-!
# Genuine Cartier invariance from fixed boundary components

This file retains the actual rational embedding of each invertible sheaf.
The normalized representative is proved to have unit local frames on the
dense torus. Actual generic-stalk pullback preserves this property. On a
smooth scheme, an automorphism fixing the codimension-one boundary points
therefore preserves the Cartier divisor, by the proved Cartier-to-Weil
injectivity theorem.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace PaperVerification.ToricSchemes

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- Both a rational function and its inverse lie in the actual local ring. -/
def IsRegularUnitAt (X : Scheme.{u}) [IsIntegral X] (x : X) (z : X.functionField) : Prop :=
  z∈regularAtSubring X x ∧ z⁻¹∈regularAtSubring X x

theorem isRegularUnitAt_pullback (f : Y ⟶ X) [IsDominant f]
    (y : Y) (z : X.functionField) (h : IsRegularUnitAt X (f y) z) :
    IsRegularUnitAt Y y (dominantFunctionFieldMap f z) := by
  refine ⟨dominantFunctionFieldMap_mem_regularAt f y z h.1,?_⟩
  simpa only [map_inv₀] using dominantFunctionFieldMap_mem_regularAt f y z⁻¹ h.2

theorem rationalOrder_zero_of_isRegularUnitAt [IsLocallyNoetherian X]
    (x : X) (z : X.functionField) (hz : z≠0) (h : IsRegularUnitAt X x z) :
    X.ord z x=0 := by
  obtain ⟨a,ha⟩ := h.1
  obtain ⟨b,hb⟩ := h.2
  have hab : a*b=1 := by
    apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
    rw [map_mul,map_one,ha,hb,mul_inv_cancel₀ hz]
  let aU : (X.presheaf.stalk x)ˣ := ⟨a,b,hab,by simpa only [mul_comm] using hab⟩
  by_cases hx : Order.coheight x=1
  · letI : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    apply (X.ord_eq_iff hx hz).mpr
    change Ring.ordFrac (X.presheaf.stalk x) z=1
    rw [← ha]
    exact Ring.ordFrac_of_isUnit aU.isUnit
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hx z
end PaperVerification.ToricSchemes
end
end
end Selected_ActualRegularUnitOrder

section Selected_ActualTorusRationalMap
section
-- BEGIN ToricIntrinsicSectionCharacters



/-!
# Laurent values of actual intrinsic toric global sections

The dense open torus and the proved torus Picard trivialization give the
Laurent polynomial of a genuine global section. No fan, affine invariant
cover, character basis, or section-coaction hypothesis enters this map.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u

open AlgebraicGeometry CategoryTheory Opposite
open PaperVerification.ToricCharacters
open scoped PaperVerification.ToricSchemes.BaseSections

namespace PaperVerification.ToricSchemes

variable (k : Type u) [Field k] (n : ℕ)
    (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (CommRingCat.of k))]
    (j : splitTorus k (Fin n→ℤ) ⟶ X) [hj : IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k))]

local instance openTorus_coordinate_isDomain : IsDomain (torusCoordinateRing k n) :=
  torusCoordinateRing_isDomain k n

local instance openTorus_coordinate_isOpenImmersion :
    IsOpenImmersion (show Spec (CommRingCat.of (torusCoordinateRing k n)) ⟶ X from j) := hj

local instance openTorus_coordinate_isOver :
    (show Spec (CommRingCat.of (torusCoordinateRing k n)) ⟶ X from j).IsOver
      (Spec (CommRingCat.of k)) :=
  inferInstanceAs (j.IsOver (Spec (CommRingCat.of k)))

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual coordinate-ring embedding from the dense open torus,
with the base scalars supplied by the actual structural morphism. -/
def openTorusRationalAlgHom : AddMonoidAlgebra k (Fin n→ℤ) →ₐ[k] X.functionField where
  __ := affineOpenCoordinateMap (CommRingCat.of (torusCoordinateRing k n)) j
  commutes' c := by
    change affineOpenCoordinateMap (CommRingCat.of (torusCoordinateRing k n)) j
      (algebraMap k (torusCoordinateRing k n) c) = algebraMap k X.functionField c
    apply (torusOpenFunctionFieldEquiv k n X j).injective
    have hs : (Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).hom
        (j.appTop (BaseSections.scalarMap k X ⊤ c)) =
          algebraMap k (torusCoordinateRing k n) c := by
      calc
        _ = (Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).hom
            (BaseSections.scalarMap k
              (Spec (CommRingCat.of (torusCoordinateRing k n))) ⊤ c) :=
          congrArg (Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).hom
            (BaseSections.scalarMap_top_natural k j c)
        _ = (Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).hom
            ((Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).inv
              (algebraMap k (torusCoordinateRing k n) c)) :=
          congrArg (Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).hom
            (BaseSections.scalarMap_affine_top k (torusCoordinateRing k n) c)
        _ = _ := by simp only [Iso.inv_hom_id_apply]
    calc
      _ = algebraMap (torusCoordinateRing k n) (FractionRing (torusCoordinateRing k n))
          (algebraMap k (torusCoordinateRing k n) c) :=
        affineOpenFunctionFieldEquiv_coordinateMap
          (CommRingCat.of (torusCoordinateRing k n)) j _
      _ = algebraMap (torusCoordinateRing k n) (FractionRing (torusCoordinateRing k n))
          ((Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).hom
            (j.appTop (BaseSections.scalarMap k X ⊤ c))) :=
        congrArg (algebraMap (torusCoordinateRing k n)
          (FractionRing (torusCoordinateRing k n))) hs.symm
      _ = torusOpenFunctionFieldEquiv k n X j
          (X.germToFunctionField ⊤ (BaseSections.scalarMap k X ⊤ c)) :=
        (torusOpenFunctionFieldEquiv_germ_top k n X j
          (BaseSections.scalarMap k X ⊤ c)).symm
      _ = _ := congrArg (torusOpenFunctionFieldEquiv k n X j)
        (BaseSections.germ_scalarMap k ⊤ c)

theorem openTorusRationalAlgHom_injective :
    Function.Injective (openTorusRationalAlgHom k n X j) :=
  (openImmersionGlobalToFunctionField_injective j).comp
    (Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).commRingCatIsoToRingEquiv.symm.injective

@[simp] theorem openTorusRationalAlgHom_value (f : AddMonoidAlgebra k (Fin n→ℤ)) :
    openTorusRationalAlgHom k n X j f =
      openImmersionGlobalToFunctionField j
        ((Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).inv f) := rfl
end PaperVerification.ToricSchemes
end
end
end Selected_ActualTorusRationalMap

section Selected_IntrinsicBoundaryCharacters


/-!
# The intrinsic characters and actual boundary valuations

Source candidate, not yet kernel checked. This is the unique declaration
owner of the original character, order and boundary definitions. They are
independent of curve classification, projectivity, and an auxiliary fan.
The torus-order proof uses actual regularity of a character and its inverse
on the original open torus. No arrangement or fan geometry is imported.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricGeometry PaperVerification.ToricCharacters
open scoped BigOperators

variable {k : Type u} [Field k] {n : ℕ}
    {X Y : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    [ModObj (splitTorusOver k (Fin n → ℤ)) Y]
    [IsIntegral X.left] [IsIntegral Y.left]

variable (T : SplitToricEmbedding k n X)

/-- A character is its actual rational function, obtained from the specified
dense open torus and the genuine generic stalk. -/
def intrinsicCharacter (m : Lattice n) : X.left.functionField :=
  openTorusRationalAlgHom k n X.left T.torus.left
    (AddMonoidAlgebra.single m 1)

theorem intrinsicCharacter_ne_zero (m : Lattice n) :
    T.intrinsicCharacter m ≠ 0 := by
  apply (map_ne_zero_iff _ (openTorusRationalAlgHom_injective
    k n X.left T.torus.left)).mpr
  exact AddMonoidAlgebra.single_ne_zero.mpr (one_ne_zero : (1 : k) ≠ 0)

@[simp] theorem intrinsicCharacter_zero : T.intrinsicCharacter 0 = 1 := by
  change openTorusRationalAlgHom k n X.left T.torus.left
    (AddMonoidAlgebra.single (0 : Lattice n) (1 : k)) = 1
  rw [← AddMonoidAlgebra.one_def, map_one]

@[simp] theorem intrinsicCharacter_add (m q : Lattice n) :
    T.intrinsicCharacter (m + q) = T.intrinsicCharacter m * T.intrinsicCharacter q := by
  rw [intrinsicCharacter, intrinsicCharacter, intrinsicCharacter, ← map_mul]
  simp

variable [IsLocallyNoetherian X.left]

/-- The order homomorphism is derived from actual rational-function orders,
including negative character powers. -/
def characterOrder (x : X.left) : Lattice n →+ ℤ where
  toFun m := X.left.ord (T.intrinsicCharacter m) x
  map_zero' := by rw [intrinsicCharacter_zero, rationalOrder_one]
  map_add' m q := by
    rw [intrinsicCharacter_add,
      X.left.ord_mul (T.intrinsicCharacter_ne_zero m) (T.intrinsicCharacter_ne_zero q)]

/-- Coordinates of the genuine character valuation in the fixed character
lattice. This definition also makes sense away from the boundary. -/
def valuationVector (x : X.left) : Lattice n :=
  fun i => T.characterOrder x (Pi.single i 1)

theorem characterOrder_eq_integerPairing (x : X.left) (m : Lattice n) :
    T.characterOrder x m = integerPairing (T.valuationVector x) m := by
  have hm : (∑ i : Fin n, m i • (Pi.single i 1 : Lattice n)) = m := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  calc
    T.characterOrder x m = T.characterOrder x
        (∑ i : Fin n, m i • (Pi.single i 1 : Lattice n)) := congrArg _ hm.symm
    _ = ∑ i : Fin n, m i * T.characterOrder x (Pi.single i 1) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      calc
        T.characterOrder x ((m i) • (Pi.single i 1 : Lattice n)) =
            (m i) • T.characterOrder x (Pi.single i 1) :=
          (T.characterOrder x).map_zsmul _ _
        _ = m i * T.characterOrder x (Pi.single i 1) := zsmul_eq_mul _ _
    _ = integerPairing (T.valuationVector x) m := by
      simp only [integerPairing, valuationVector, mul_comm]

/-- Every character is an actual unit on the specified open torus, so its
ordinary order vanishes there in every codimension. -/
theorem characterOrder_torus (z : splitTorus k (Fin n → ℤ)) (m : Lattice n) :
    T.characterOrder (T.torus.left z) m = 0 := by
  let R := CommRingCat.of (torusCoordinateRing k n)
  letI : IsDomain R := torusCoordinateRing_isDomain k n
  have hreg (a : Lattice n) :
      T.intrinsicCharacter a ∈ regularAtSubring X.left (T.torus.left z) := by
    change openImmersionGlobalToFunctionField T.torus.left
      ((Scheme.ΓSpecIso R).inv (AddMonoidAlgebra.single a (1 : k))) ∈ _
    exact openImmersionGlobalToFunctionField_mem_regularAt T.torus.left _ z
  have hi : T.intrinsicCharacter (-m) = (T.intrinsicCharacter m)⁻¹ := by
    apply mul_left_cancel₀ (T.intrinsicCharacter_ne_zero m)
    rw [← T.intrinsicCharacter_add, add_neg_cancel, T.intrinsicCharacter_zero,
      mul_inv_cancel₀ (T.intrinsicCharacter_ne_zero m)]
  apply rationalOrder_zero_of_isRegularUnitAt (T.torus.left z)
    (T.intrinsicCharacter m) (T.intrinsicCharacter_ne_zero m)
  refine ⟨hreg m, ?_⟩
  rw [← hi]
  exact hreg (-m)

/-- Actual generic points of the codimension-one components of the torus
boundary, with no chosen enumeration or fan presentation. -/
def BoundaryPrime := {x : X.left // Order.coheight x = 1 ∧ x ∈ T.boundary}

def boundaryValuation (p : T.BoundaryPrime) : Lattice n :=
  T.valuationVector p.val

def boundaryForm (p : T.BoundaryPrime) : Ambient n →ₗ[ℝ] ℝ :=
  dotProductEquiv ℝ (Fin n) (embed n (T.boundaryValuation p))

/-- The unit inequalities attached to the actual boundary valuations.
The anticanonical interpretation is proved separately from this definition. -/
def unitBoundaryPolyhedron : Set (Ambient n) :=
  {x | ∀ p : T.BoundaryPrime, T.boundaryForm p x ≤ 1}


end PaperVerification.ToricSchemes.SplitToricEmbedding

end
end
end Selected_IntrinsicBoundaryCharacters

section Selected_ProperGlobalCharacters


/-!
# Complete toric varieties have no nonconstant global characters

Source candidate, not yet kernel checked. The global regular functions of
an integral proper scheme over a field form a field. The actual restriction
to the dense split torus, followed by the Hopf counit (evaluation at its
identity), gives a retraction to the original ground field. Injectivity of
this field homomorphism proves that all global functions are scalars.

Consequently the only character with nonnegative orders at every boundary
prime is the zero character. Projectivity, a chosen fan, and a pre-existing
finiteness theorem for line-bundle sections are unnecessary.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricGeometry PaperVerification.ToricCharacters
open scoped PaperVerification.ToricSchemes.BaseSections

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    [IsIntegral X.left]
    (T : SplitToricEmbedding k n X)

/-- The literal restriction of a global regular function to the open
torus, in its actual Laurent coordinate ring. -/
def globalLaurentRestriction : Γ(X.left, ⊤) →+* torusCoordinateRing k n :=
  (Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).hom.hom.comp
    T.torus.left.appTop.hom

theorem globalLaurentRestriction_scalar (a : k) :
    T.globalLaurentRestriction (BaseSections.scalarMap k X.left ⊤ a) =
      algebraMap k (torusCoordinateRing k n) a := by
  change (Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).hom
    (T.torus.left.appTop (BaseSections.scalarMap k X.left ⊤ a)) = _
  rw [BaseSections.scalarMap_top_natural k T.torus.left a]
  change (Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).hom
    (BaseSections.scalarMap k (Spec (CommRingCat.of (torusCoordinateRing k n))) ⊤ a) = _
  rw [BaseSections.scalarMap_affine_top k (torusCoordinateRing k n) a]
  exact Iso.inv_hom_id_apply _ _

/-- This algebraic counit is evaluation at the actual torus identity. -/
def globalIdentityEvaluation : Γ(X.left, ⊤) →+* k :=
  (Bialgebra.counitAlgHom k (torusCoordinateRing k n)).toRingHom.comp
    T.globalLaurentRestriction

theorem globalIdentityEvaluation_scalar (a : k) :
    T.globalIdentityEvaluation (BaseSections.scalarMap k X.left ⊤ a) = a := by
  change (Bialgebra.counitAlgHom k (torusCoordinateRing k n))
    (T.globalLaurentRestriction (BaseSections.scalarMap k X.left ⊤ a)) = a
  rw [T.globalLaurentRestriction_scalar]
  exact (Bialgebra.counitAlgHom k (torusCoordinateRing k n)).commutes a

/-- Restriction and rational evaluation agree with the original global
regular function in the actual function field. -/
theorem globalLaurentRestriction_value (s : Γ(X.left, ⊤)) :
    openTorusRationalAlgHom k n X.left T.torus.left (T.globalLaurentRestriction s) =
      X.left.germToFunctionField ⊤ s := by
  let R := CommRingCat.of (torusCoordinateRing k n)
  letI : IsDomain R := torusCoordinateRing_isDomain k n
  apply (torusOpenFunctionFieldEquiv k n X.left T.torus.left).injective
  calc
    _ = algebraMap (torusCoordinateRing k n) (FractionRing (torusCoordinateRing k n))
        (T.globalLaurentRestriction s) :=
      affineOpenFunctionFieldEquiv_coordinateMap R T.torus.left _
    _ = _ := (torusOpenFunctionFieldEquiv_germ_top k n X.left T.torus.left s).symm

variable [IsProper X.hom]

/-- The actual field of global functions is exactly the ground field;
the scalar is its value at the specified torus identity. -/
theorem globalSection_eq_scalar (s : Γ(X.left, ⊤)) :
    s = BaseSections.scalarMap k X.left ⊤ (T.globalIdentityEvaluation s) := by
  letI : Field Γ(X.left, ⊤) := (isField_of_universallyClosed k X.hom).toField
  apply T.globalIdentityEvaluation.injective
  exact (T.globalIdentityEvaluation_scalar (T.globalIdentityEvaluation s)).symm

/-- No nonzero lattice exponent can represent a global regular character
on the actual complete variety. -/
theorem intrinsicCharacter_regular_iff (m : Lattice n) :
    T.intrinsicCharacter m ∈ (X.left.germToFunctionField ⊤).hom.range ↔ m = 0 := by
  constructor
  · rintro ⟨s, hs⟩
    have hchar : AddMonoidAlgebra.single m (1 : k) =
        algebraMap k (torusCoordinateRing k n) (T.globalIdentityEvaluation s) := by
      apply openTorusRationalAlgHom_injective k n X.left T.torus.left
      change T.intrinsicCharacter m = _
      rw [AlgHom.commutes]
      rw [T.globalSection_eq_scalar s, BaseSections.germ_scalarMap] at hs
      exact hs.symm
    by_contra hm
    have hc := congrArg (fun p : AddMonoidAlgebra k (Lattice n) => p.coeff m) hchar
    change (AddMonoidAlgebra.single m (1 : k)).coeff m =
      (AddMonoidAlgebra.single 0 (T.globalIdentityEvaluation s)).coeff m at hc
    exact one_ne_zero (by
      simpa only [AddMonoidAlgebra.coeff_single_apply, if_pos rfl,
        if_neg (Ne.symm hm), ite_true] using hc)
  · rintro rfl
    rw [T.intrinsicCharacter_zero]
    exact ⟨1, map_one _⟩

variable [Smooth X.hom]

local instance completeCharacterLocallyNoetherian : IsLocallyNoetherian X.left :=
  LocallyOfFiniteType.isLocallyNoetherian X.hom

/-- All actual boundary valuations positively span the character dual in
the precise integral form needed for finiteness of graphic section points. -/
theorem nonnegative_boundary_orders_iff_zero (m : Lattice n) :
    (∀ q : T.BoundaryPrime, 0 ≤ T.characterOrder q.val m) ↔ m = 0 := by
  rw [← T.intrinsicCharacter_regular_iff m,
    smooth_regular_range_iff_orders X.hom ⊤ _ (T.intrinsicCharacter_ne_zero m)]
  constructor
  · intro h x hx
    by_cases hc : Order.coheight x = 1
    · by_cases hb : x ∈ T.boundary
      · exact h ⟨x, hc, hb⟩
      · have ht : x ∈ (T.torusOpen : Set X.left) := by
          simpa only [boundary, Set.mem_compl_iff, not_not] using hb
        obtain ⟨z, rfl⟩ := ht
        exact le_of_eq (T.characterOrder_torus z m).symm
    · simp only [Scheme.ord_eq_zero_of_coheight_neq_one hc, le_refl]
  · intro h q
    exact h q.val trivial


end PaperVerification.ToricSchemes.SplitToricEmbedding

end
end
end Selected_ProperGlobalCharacters

#print axioms PaperVerification.ToricSchemes.smooth_regular_range_iff_orders
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.characterOrder_eq_integerPairing
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.characterOrder_torus
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.nonnegative_boundary_orders_iff_zero
