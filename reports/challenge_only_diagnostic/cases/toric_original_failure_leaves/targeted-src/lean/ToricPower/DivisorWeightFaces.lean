module

public import ToricPower.DivisorWeightCartierResidue

set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

/-! ## Source section: DivisorWeightFaces -/

/-!
# Denominator clearing on every exposed face

For an integral character nonnegative on the rays of a chart, the face it
exposes consists of the rays on which it vanishes.  A section regular on that
face becomes regular on the entire chart after multiplication by a sufficiently
large power of the exposing monomial.  This is proved for the literal supported
Laurent section modules and does not require a complete fan.
-/



namespace ToricPower

open MonoidAlgebra
open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

abbrev ZeroFaceRay (A : ι → κ → ℤ) (h : κ → ℤ) :=
  {i : ι // rayMap A h i = 0}

/-- An explicit common bound for the negative ray pairings of one character. -/
def divisorDenominatorExponent (A : ι → κ → ℤ) (b : ι → ℤ) (m : κ → ℤ) : ℕ :=
  ∑ i, (-(b i + rayMap A m i)).toNat

theorem divisorDenominatorExponent_bound (A : ι → κ → ℤ)
    (b : ι → ℤ) (m : κ → ℤ) (i : ι) :
    -(b i + rayMap A m i) ≤ (divisorDenominatorExponent A b m : ℤ) := by
  classical
  have hnat : (-(b i + rayMap A m i)).toNat ≤ divisorDenominatorExponent A b m := by
    unfold divisorDenominatorExponent
    exact Finset.single_le_sum
      (f := fun j => (-(b j + rayMap A m j)).toNat)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hcast : (((-(b i + rayMap A m i)).toNat : ℕ) : ℤ) ≤
      (divisorDenominatorExponent A b m : ℤ) := by exact_mod_cast hnat
  omega

/-- An explicit exponent clears the poles away from the exposed face. -/
theorem divisorWeightAllowed_clear_face_denominators (A : ι → κ → ℤ)
    (b : ι → ℤ) (h m : κ → ℤ) (hh : ∀ i, 0 ≤ rayMap A h i)
    (hm : DivisorWeightAllowed (fun i : ZeroFaceRay A h => A i.1)
      (fun i => b i.1) m) :
    DivisorWeightAllowed A b (m + divisorDenominatorExponent A b m • h) := by
  intro i
  change 0 ≤ b i + rayMap A (m + divisorDenominatorExponent A b m • h) i
  rw [map_add, map_nsmul]
  simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
  by_cases hi : rayMap A h i = 0
  · have hm' := hm ⟨i, hi⟩
    change 0 ≤ b i + rayMap A m i at hm'
    simpa only [hi, mul_zero, add_zero] using hm'
  · have hpos : 1 ≤ rayMap A h i := by have := hh i; omega
    have hN : 0 ≤ (divisorDenominatorExponent A b m : ℤ) := Int.natCast_nonneg _
    have hb := divisorDenominatorExponent_bound A b m i
    nlinarith

/-- Every larger exponent also clears the poles. -/
theorem divisorWeightAllowed_clear_face_denominators_of_le (A : ι → κ → ℤ)
    (b : ι → ℤ) (h m : κ → ℤ) (hh : ∀ i, 0 ≤ rayMap A h i)
    (hm : DivisorWeightAllowed (fun i : ZeroFaceRay A h => A i.1)
      (fun i => b i.1) m)
    (N : ℕ) (hN : divisorDenominatorExponent A b m ≤ N) :
    DivisorWeightAllowed A b (m + N • h) := by
  have hc := divisorWeightAllowed_clear_face_denominators A b h m hh hm
  have hp : ∀ i, 0 ≤ rayMap A ((N - divisorDenominatorExponent A b m) • h) i := by
    intro i
    simpa only [map_nsmul, Pi.smul_apply] using
      nsmul_nonneg (hh i) (N - divisorDenominatorExponent A b m)
  have hsum : m + N • h =
      (N - divisorDenominatorExponent A b m) • h +
        (m + divisorDenominatorExponent A b m • h) := by
    calc
      m + N • h = m + ((N - divisorDenominatorExponent A b m) • h +
          divisorDenominatorExponent A b m • h) := by
        rw [← add_nsmul, Nat.sub_add_cancel hN]
      _ = _ := by abel
  rw [hsum]
  exact divisorWeightAllowed_add_nonnegative A b hc hp

/-- A finite Laurent section has a single common denominator on the whole
chart.  The support may be arbitrarily large and the fan may be incomplete. -/
theorem divisorLaurent_clear_face_denominators (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (b : ι → ℤ) (h : κ → ℤ)
    (hh : ∀ i, 0 ≤ rayMap A h i)
    (x : MonoidAlgebra R (Multiplicative (κ → ℤ)))
    (hx : x ∈ supported R R {m | DivisorWeightAllowed
      (fun i : ZeroFaceRay A h => A i.1) (fun i => b i.1) (Multiplicative.toAdd m)}) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      x * single (Multiplicative.ofAdd (n • h)) 1 ∈
        supported R R {m | DivisorWeightAllowed A b (Multiplicative.toAdd m)} := by
  classical
  let N := ∑ m ∈ x.coeff.support, divisorDenominatorExponent A b (Multiplicative.toAdd m)
  refine ⟨N, fun n hn => ?_⟩
  rw [mem_supported]
  intro g hg
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp
    (support_coeff_mul_single_subset x (1 : R) (Multiplicative.ofAdd (n • h)) hg)
  have hbound : divisorDenominatorExponent A b (Multiplicative.toAdd m) ≤ N :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) hm
  exact divisorWeightAllowed_clear_face_denominators_of_le A b h
    (Multiplicative.toAdd m) hh ((mem_supported.mp hx) hm) n (hbound.trans hn)

/-- On the exposed face, multiplication by its exposing character is an
automorphism, because that character pairs to zero with every face ray. -/
def divisorFaceExposingShift (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (b : ι → ℤ) (h : κ → ℤ) :
    DivisorFaceSectionModule R (fun i : ZeroFaceRay A h => i.1) A b 1 ≃ₗ[RayChartRing R A]
      DivisorFaceSectionModule R (fun i : ZeroFaceRay A h => i.1) A b 1 where
  toFun x := ⟨rayPowerLaurentOfValue R A 1
      (rayPowerLaurentValue R A 1 x.1 * single (Multiplicative.ofAdd h) 1), by
    have hz : rayMap (fun i : ZeroFaceRay A h => A i.1) h = 0 := by
      funext i
      exact i.2
    change rayPowerLaurentValue R A 1 x.1 * single (Multiplicative.ofAdd h) 1 ∈
      supported R R {m | DivisorWeightAllowed (fun i : ZeroFaceRay A h => A i.1)
        (fun i => b i.1) (Multiplicative.toAdd m)}
    simpa only [hz, sub_zero] using
      divisor_support_shift R (fun i : ZeroFaceRay A h => A i.1)
        (fun i => b i.1) h (rayPowerLaurentValue R A 1 x.1) x.2⟩
  invFun x := ⟨rayPowerLaurentOfValue R A 1
      (rayPowerLaurentValue R A 1 x.1 * single (Multiplicative.ofAdd (-h)) 1), by
    have hz : rayMap (fun i : ZeroFaceRay A h => A i.1) (-h) = 0 := by
      rw [map_neg]
      have hz' : rayMap (fun i : ZeroFaceRay A h => A i.1) h = 0 := by
        funext i
        exact i.2
      rw [hz', neg_zero]
    change rayPowerLaurentValue R A 1 x.1 * single (Multiplicative.ofAdd (-h)) 1 ∈
      supported R R {m | DivisorWeightAllowed (fun i : ZeroFaceRay A h => A i.1)
        (fun i => b i.1) (Multiplicative.toAdd m)}
    simpa only [hz, sub_zero] using
      divisor_support_shift R (fun i : ZeroFaceRay A h => A i.1)
        (fun i => b i.1) (-h) (rayPowerLaurentValue R A 1 x.1) x.2⟩
  left_inv x := by
    apply Subtype.ext
    apply rayPowerLaurentValue_injective R A 1
    change (rayPowerLaurentValue R A 1 x.1 * single (Multiplicative.ofAdd h) 1) *
      single (Multiplicative.ofAdd (-h)) 1 = rayPowerLaurentValue R A 1 x.1
    simp [mul_assoc, single_mul_single, ← MonoidAlgebra.one_def]
  right_inv x := by
    apply Subtype.ext
    apply rayPowerLaurentValue_injective R A 1
    change (rayPowerLaurentValue R A 1 x.1 * single (Multiplicative.ofAdd (-h)) 1) *
      single (Multiplicative.ofAdd h) 1 = rayPowerLaurentValue R A 1 x.1
    simp [mul_assoc, single_mul_single, ← MonoidAlgebra.one_def]
  map_add' x y := by
    apply Subtype.ext
    apply rayPowerLaurentValue_injective R A 1
    exact add_mul (rayPowerLaurentValue R A 1 x.1) (rayPowerLaurentValue R A 1 y.1) _
  map_smul' a x := by
    apply Subtype.ext
    apply rayPowerLaurentValue_injective R A 1
    change rayPowerLaurentValue R A 1
        (rayPowerLaurentOfValue R A 1
          (rayPowerLaurentValue R A 1 (a • x.1) * single (Multiplicative.ofAdd h) 1)) =
      rayPowerLaurentValue R A 1 (a • rayPowerLaurentOfValue R A 1
        (rayPowerLaurentValue R A 1 x.1 * single (Multiplicative.ofAdd h) 1))
    simp only [rayPowerLaurentValue_ofValue, rayPowerLaurentValue_smul]
    exact mul_assoc _ _ _

def rayChartExposingMonomial (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (h : κ → ℤ) (hh : ∀ i, 0 ≤ rayMap A h i) : RayChartRing R A :=
  single (Multiplicative.ofAdd (⟨h, hh⟩ : rayWeightMonoid A)) 1

/-- The restriction to an exposed face is the localization of the genuine
divisor-section module at the exposing monomial. -/
theorem divisorFaceRestriction_isLocalizedModule (R : Type*) [CommRing R]
    (A : ι → κ → ℤ) (b : ι → ℤ) (h : κ → ℤ)
    (hh : ∀ i, 0 ≤ rayMap A h i) :
    IsLocalizedModule (Submonoid.powers (rayChartExposingMonomial R A h hh))
      (divisorSectionFaceRestriction R (fun i : ZeroFaceRay A h => i.1) A b 1) := by
  let T := DivisorFaceSectionModule R (fun i : ZeroFaceRay A h => i.1) A b 1
  let a := rayChartExposingMonomial R A h hh
  have ha : IsUnit (algebraMap (RayChartRing R A) (Module.End (RayChartRing R A) T) a) := by
    rw [Module.End.isUnit_iff]
    have heq : (algebraMap (RayChartRing R A) (Module.End (RayChartRing R A) T) a : T → T) =
        divisorFaceExposingShift R A b h := by
      funext x
      apply Subtype.ext
      apply rayPowerLaurentValue_injective R A 1
      change mapDomain (rayChartPowerMonoidHom A 1) a * rayPowerLaurentValue R A 1 x.1 =
        rayPowerLaurentValue R A 1 x.1 * single (Multiplicative.ofAdd h) 1
      simp only [a, rayChartExposingMonomial, mapDomain_single]
      have hp : rayChartPowerMonoidHom A 1
          (Multiplicative.ofAdd (⟨h, hh⟩ : rayWeightMonoid A)) = Multiplicative.ofAdd h := by
        apply Multiplicative.toAdd.injective
        simp only [rayChartPowerMonoidHom_toAdd, one_smul]
        rfl
      rw [hp, mul_comm]
    rw [heq]
    exact (divisorFaceExposingShift R A b h).bijective
  refine ⟨?_, ?_, ?_⟩
  · intro s
    obtain ⟨n, hn⟩ := s.2
    change IsUnit (algebraMap (RayChartRing R A) (Module.End (RayChartRing R A) T) s.1)
    rw [← hn, map_pow]
    exact ha.pow n
  · intro x
    obtain ⟨N, hN⟩ := divisorLaurent_clear_face_denominators R A b h hh
      (rayPowerLaurentValue R A 1 x.1) x.2
    let y : DivisorSectionModule R A b 1 :=
      ⟨rayPowerLaurentOfValue R A 1
        (rayPowerLaurentValue R A 1 x.1 * single (Multiplicative.ofAdd (N • h)) 1), hN N le_rfl⟩
    let s : Submonoid.powers a := ⟨a ^ N, ⟨N, rfl⟩⟩
    refine ⟨(y, s), ?_⟩
    apply Subtype.ext
    apply rayPowerLaurentValue_injective R A 1
    change mapDomain (rayChartPowerMonoidHom A 1) (a ^ N) * rayPowerLaurentValue R A 1 x.1 =
      rayPowerLaurentValue R A 1 x.1 * single (Multiplicative.ofAdd (N • h)) 1
    have hp : rayChartPowerMonoidHom A 1
        (Multiplicative.ofAdd (⟨h, hh⟩ : rayWeightMonoid A)) = Multiplicative.ofAdd h := by
      apply Multiplicative.toAdd.injective
      simp only [rayChartPowerMonoidHom_toAdd, one_smul]
      rfl
    have mappedPower : mapDomain (rayChartPowerMonoidHom A 1) (a ^ N) =
        (mapDomain (rayChartPowerMonoidHom A 1) a) ^ N :=
      map_pow (mapDomainRingHom R (rayChartPowerMonoidHom A 1)) a N
    rw [mappedPower]
    simp only [a, rayChartExposingMonomial, mapDomain_single, hp, single_pow, one_pow]
    exact mul_comm _ _
  · intro x y hxy
    refine ⟨1, ?_⟩
    have h := divisorSectionFaceRestriction_injective R
      (fun i : ZeroFaceRay A h => i.1) A b 1 hxy
    simp only [one_smul, h]

end ToricPower
