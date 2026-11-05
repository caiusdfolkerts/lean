module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.AsSubring

@[expose] public section

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
