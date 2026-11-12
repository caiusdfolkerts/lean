module

public import ToricPower.DivisorWeightRestriction

set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

/-! ## Source section: DivisorWeightCartier -/

/-!
# Cartier trivializations of the actual divisor modules

Multiplication by a Laurent monomial translates the divisor coefficients by a
principal divisor.  In particular, a divisor given by a local Cartier character
has a free rank-one chart module, with generator carrying the correct sign.
-/



namespace ToricPower

open MonoidAlgebra

variable {ι κ : Type*} [Fintype κ]

theorem divisor_support_shift (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (b : ι → ℤ) (q : κ → ℤ)
    (x : MonoidAlgebra R (Multiplicative (κ → ℤ)))
    (hx : x ∈ supported R R {m | DivisorWeightAllowed A b (Multiplicative.toAdd m)}) :
    x * single (Multiplicative.ofAdd q) 1 ∈
      supported R R {m | DivisorWeightAllowed A (b - rayMap A q) (Multiplicative.toAdd m)} := by
  classical
  rw [mem_supported]
  intro g hg
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp
    (support_coeff_mul_single_subset x (1 : R) (Multiplicative.ofAdd q) hg)
  intro i
  change 0 ≤ b i - rayMap A q i + rayMap A (Multiplicative.toAdd m + q) i
  simp only [map_add, Pi.add_apply]
  have hi := (mem_supported.mp hx) hm i
  omega

/-- Multiplication by `χ^q` changes `D` to `D - div(χ^q)`. -/
def divisorSectionShiftLinearEquiv (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ) (q : κ → ℤ) :
    DivisorSectionModule R A b ell ≃ₗ[RayChartRing R A]
      DivisorSectionModule R A (b - rayMap A q) ell where
  toFun x := ⟨rayPowerLaurentOfValue R A ell
      (rayPowerLaurentValue R A ell x.1 * single (Multiplicative.ofAdd q) 1),
    divisor_support_shift R A b q (rayPowerLaurentValue R A ell x.1) x.2⟩
  invFun x := ⟨rayPowerLaurentOfValue R A ell
      (rayPowerLaurentValue R A ell x.1 * single (Multiplicative.ofAdd (-q)) 1), by
    have h := divisor_support_shift R A (b - rayMap A q) (-q)
      (rayPowerLaurentValue R A ell x.1) x.2
    change rayPowerLaurentValue R A ell x.1 * single (Multiplicative.ofAdd (-q)) 1 ∈
      supported R R {m | DivisorWeightAllowed A b (Multiplicative.toAdd m)}
    simpa only [map_neg, sub_neg_eq_add, sub_add_cancel] using h⟩
  left_inv x := by
    apply Subtype.ext
    apply rayPowerLaurentValue_injective R A ell
    change (rayPowerLaurentValue R A ell x.1 * single (Multiplicative.ofAdd q) 1) *
      single (Multiplicative.ofAdd (-q)) 1 = rayPowerLaurentValue R A ell x.1
    simp [mul_assoc, single_mul_single, ← MonoidAlgebra.one_def]
  right_inv x := by
    apply Subtype.ext
    apply rayPowerLaurentValue_injective R A ell
    change (rayPowerLaurentValue R A ell x.1 * single (Multiplicative.ofAdd (-q)) 1) *
      single (Multiplicative.ofAdd q) 1 = rayPowerLaurentValue R A ell x.1
    simp [mul_assoc, single_mul_single, ← MonoidAlgebra.one_def]
  map_add' x y := by
    apply Subtype.ext
    apply rayPowerLaurentValue_injective R A ell
    exact add_mul (rayPowerLaurentValue R A ell x.1) (rayPowerLaurentValue R A ell y.1) _
  map_smul' a x := by
    apply Subtype.ext
    apply rayPowerLaurentValue_injective R A ell
    change rayPowerLaurentValue R A ell
        (rayPowerLaurentOfValue R A ell
          (rayPowerLaurentValue R A ell (a • x.1) * single (Multiplicative.ofAdd q) 1)) =
      rayPowerLaurentValue R A ell (a • rayPowerLaurentOfValue R A ell
        (rayPowerLaurentValue R A ell x.1 * single (Multiplicative.ofAdd q) 1))
    simp only [rayPowerLaurentValue_ofValue, rayPowerLaurentValue_smul]
    exact mul_assoc _ _ _

theorem rayChartPowerMonoidHom_one_injective (A : ι → κ → ℤ) :
    Function.Injective (rayChartPowerMonoidHom A 1) := by
  intro m n h
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  simpa only [rayChartPowerMonoidHom_toAdd, one_smul] using
    congrArg Multiplicative.toAdd h

theorem chart_mapDomain_mem_zero_divisor (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (a : RayChartRing R A) :
    mapDomain (rayChartPowerMonoidHom A 1) a ∈
      supported R R {m | DivisorWeightAllowed A 0 (Multiplicative.toAdd m)} := by
  classical
  rw [mem_supported]
  intro m hm
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hm)
  intro i
  simpa only [rayChartPowerMonoidHom_toAdd, one_smul, Pi.zero_apply, zero_add] using
    (Multiplicative.toAdd s).2 i

theorem zero_divisor_support_in_chart_range (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (x : DivisorSectionModule R A 0 1) :
    ↑(rayPowerLaurentValue R A 1 x.1).coeff.support ⊆
      Set.range (rayChartPowerMonoidHom A 1) := by
  intro m hm
  have hp := (mem_supported.mp x.2) hm
  let s : rayWeightMonoid A := ⟨Multiplicative.toAdd m, by
    intro i
    simpa only [Pi.zero_apply, zero_add] using hp i⟩
  refine ⟨Multiplicative.ofAdd s, ?_⟩
  apply Multiplicative.toAdd.injective
  simp only [rayChartPowerMonoidHom_toAdd, one_smul]
  rfl

/-- The zero-divisor section module is the chart coordinate ring itself. -/
def chartRingZeroDivisorLinearEquiv (R : Type*) [Semiring R] (A : ι → κ → ℤ) :
    RayChartRing R A ≃ₗ[RayChartRing R A] DivisorSectionModule R A 0 1 where
  toFun a := ⟨rayPowerLaurentOfValue R A 1 (mapDomain (rayChartPowerMonoidHom A 1) a),
    chart_mapDomain_mem_zero_divisor R A a⟩
  invFun x := comapDomain (rayChartPowerMonoidHom A 1)
    (rayChartPowerMonoidHom_one_injective A) (rayPowerLaurentValue R A 1 x.1)
  left_inv a := by
    change comapDomain (rayChartPowerMonoidHom A 1)
      (rayChartPowerMonoidHom_one_injective A) (mapDomain (rayChartPowerMonoidHom A 1) a) = a
    induction a using induction_linear with
    | zero => simp
    | add a b ha hb => rw [mapDomain_add, comapDomain_add, ha, hb]
    | single s r => simp
  right_inv x := by
    apply Subtype.ext
    apply rayPowerLaurentValue_injective R A 1
    exact mapDomain_comapDomain (zero_divisor_support_in_chart_range R A x)
      (rayChartPowerMonoidHom_one_injective A)
  map_add' a b := by
    apply Subtype.ext
    apply rayPowerLaurentValue_injective R A 1
    exact mapDomain_add _ _ _
  map_smul' a b := by
    apply Subtype.ext
    apply rayPowerLaurentValue_injective R A 1
    change mapDomain (rayChartPowerMonoidHom A 1) (a * b) =
      mapDomain (rayChartPowerMonoidHom A 1) a * mapDomain (rayChartPowerMonoidHom A 1) b
    exact mapDomain_mul _ _ _

/-- Equality of divisor coefficients identifies their section modules by the
literal identity on Laurent polynomials.  Making this identity explicit keeps
the subsequent Cartier trivializations computational on their underlying
sections, without opaque transports of a linear-equivalence record. -/
def divisorCoefficientEqLinearEquiv (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (ell : ℕ) (b c : ι → ℤ) (hbc : b = c) :
    DivisorSectionModule R A b ell ≃ₗ[RayChartRing R A]
      DivisorSectionModule R A c ell where
  toFun x := ⟨x.1, by simpa only [← hbc] using x.2⟩
  invFun x := ⟨x.1, by simpa only [hbc] using x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A Cartier character `q` with coefficients `b = rayMap A q` trivializes the
divisor module by the generator `χ^(-q)`. -/
def divisorCartierTrivialization (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (b : ι → ℤ) (q : κ → ℤ) (hq : b = rayMap A q) :
    RayChartRing R A ≃ₗ[RayChartRing R A] DivisorSectionModule R A b 1 :=
  (chartRingZeroDivisorLinearEquiv R A).trans
    ((divisorSectionShiftLinearEquiv R A 0 1 (-q)).trans
      (divisorCoefficientEqLinearEquiv R A 1 _ b (by
        rw [map_neg, zero_sub, neg_neg, ← hq])))

/-- The Cartier trivialization is multiplication by its actual Laurent
generator, after the chart coordinate ring is embedded in the Laurent ring. -/
@[simp] theorem divisorCartierTrivialization_val (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (b : ι → ℤ) (q : κ → ℤ) (hq : b = rayMap A q)
    (a : RayChartRing R A) :
    (divisorCartierTrivialization R A b q hq a).1 =
      mapDomain (rayChartPowerMonoidHom A 1) a *
        single (Multiplicative.ofAdd (-q)) 1 := rfl

/-- Principal-divisor translations agree on every chart intersection. -/
theorem divisorSectionShiftLinearEquiv_restrict {ι' : Type*}
    (R : Type*) [Semiring R] (f : ι' → ι)
    (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ) (q : κ → ℤ)
    (x : DivisorSectionModule R A b ell) :
    divisorSectionRestrict R f A (b - rayMap A q) ell
        (divisorSectionShiftLinearEquiv R A b ell q x) =
      divisorSectionShiftLinearEquiv R (fun i => A (f i)) (fun i => b (f i)) ell q
        (divisorSectionRestrict R f A b ell x) := by
  apply Subtype.ext
  rfl

end ToricPower

