module

public import ToricPower.DivisorWeightCartierRestriction

set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

/-! ## Source section: DivisorWeightCartierResidue -/

/-!
# Residue monomials in local Cartier frames

For a divisor with local equation `χ^qD` and a floor-divisor summand with local
equation `χ^qC`, the normalized image of its generator is
`χ^(qD + u - ell*qC)`.  Its ray pairings are precisely the nonnegative Euclidean
remainders of `b + A*u`.  This is the concrete local regularity calculation for
the global rational-function map `s ↦ χ^u F_ell^*s`, including arbitrary
divisors and cones of any dimension.
-/



namespace ToricPower

open MonoidAlgebra

variable {ι κ : Type*} [Fintype κ]

def cartierResidueExponent (ell : ℕ) (u qD qC : κ → ℤ) : κ → ℤ :=
  qD + u - (ell : ℤ) • qC

/-- The normalized residue exponent has the literal Euclidean remainders as
its ray coordinates.  Its other lattice coordinates remain unrestricted. -/
theorem rayMap_cartierResidueExponent (A : ι → κ → ℤ) (b : ι → ℤ)
    (ell : ℕ) (u qD qC : κ → ℤ) (hD : b = rayMap A qD)
    (hC : powerCoefficient A b (ell : ℤ) u = rayMap A qC) :
    rayMap A (cartierResidueExponent ell u qD qC) =
      fun i => (b i + rayMap A u i) % (ell : ℤ) := by
  funext i
  simp only [cartierResidueExponent, map_sub, map_add, map_smul,
    Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← congrFun hD i, ← congrFun hC i]
  change b i + rayMap A u i - (ell : ℤ) *
    ((b i + rayMap A u i) / (ell : ℤ)) = _
  have h := Int.emod_add_mul_ediv (b i + rayMap A u i) (ell : ℤ)
  omega

theorem cartierResidueExponent_nonnegative (A : ι → κ → ℤ) (b : ι → ℤ)
    (ell : ℕ) (hell : 0 < ell) (u qD qC : κ → ℤ) (hD : b = rayMap A qD)
    (hC : powerCoefficient A b (ell : ℤ) u = rayMap A qC) :
    ∀ i, 0 ≤ rayMap A (cartierResidueExponent ell u qD qC) i := by
  intro i
  rw [rayMap_cartierResidueExponent A b ell u qD qC hD hC]
  exact Int.emod_nonneg _ (by exact_mod_cast hell.ne')

theorem cartierResidueExponent_lt (A : ι → κ → ℤ) (b : ι → ℤ)
    (ell : ℕ) (hell : 0 < ell) (u qD qC : κ → ℤ) (hD : b = rayMap A qD)
    (hC : powerCoefficient A b (ell : ℤ) u = rayMap A qC) :
    ∀ i, rayMap A (cartierResidueExponent ell u qD qC) i < (ell : ℤ) := by
  intro i
  rw [rayMap_cartierResidueExponent A b ell u qD qC hD hC]
  exact Int.emod_lt_of_pos _ (by exact_mod_cast hell)

/-- The normalized residue monomial is an actual element of the chart ring. -/
def cartierResidueChartMonomial (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ) (hell : 0 < ell)
    (u qD qC : κ → ℤ) (hD : b = rayMap A qD)
    (hC : powerCoefficient A b (ell : ℤ) u = rayMap A qC) : RayChartRing R A :=
  single (Multiplicative.ofAdd
    (⟨cartierResidueExponent ell u qD qC,
      cartierResidueExponent_nonnegative A b ell hell u qD qC hD hC⟩ : rayWeightMonoid A)) 1

/-- The local Cartier generator is sent to the actual normalized residue
monomial.  Multiplication by `χ^qD` converts a target divisor section to its
ordinary chart-coordinate function. -/
theorem divisorResidueSummand_cartier_generator (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ) (hell : 0 < ell)
    (u : LatticeResidues κ ell) (qD qC : κ → ℤ)
    (hC : powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u) = rayMap A qC) :
    rayPowerLaurentValue R A ell (divisorResidueSummand R A b ell hell u
      (divisorCartierTrivialization R A
        (powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u)) qC hC 1)).1 *
          single (Multiplicative.ofAdd qD) 1 =
      single (Multiplicative.ofAdd
        (cartierResidueExponent ell (latticeResidueRepresentative u) qD qC)) 1 := by
  let m : DivisorWeight A
      (powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u)) := ⟨-qC, by
    intro i
    simp only [map_neg, Pi.neg_apply]
    rw [congrFun hC i]
    omega⟩
  have hone : divisorCartierTrivialization R A
      (powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u)) qC hC 1 =
      divisorSectionSingle R A _ 1 m 1 := by
    apply Subtype.ext
    apply rayPowerLaurentValue_injective R A 1
    simp [divisorCartierTrivialization_val, divisorSectionSingle, m, rayPowerLaurentValue, rayPowerLaurentOfValue]
  rw [hone, divisorResidueSummand_single]
  change single (Multiplicative.ofAdd
      (latticeResidueRepresentative u + (ell : ℤ) • (-qC))) 1 *
      single (Multiplicative.ofAdd qD) 1 = _
  rw [single_mul_single, one_mul]
  congr 1
  apply Multiplicative.toAdd.injective
  change (latticeResidueRepresentative u + (ell : ℤ) • (-qC)) + qD =
    qD + latticeResidueRepresentative u - (ell : ℤ) • qC
  rw [smul_neg, sub_eq_add_neg]
  abel

/-- On every scalar multiple of the Cartier generator, the residue inclusion
is the actual power-map scalar action times its normalized chart monomial. -/
theorem divisorResidueSummand_in_cartier_coordinates (R : Type*) [Semiring R]
    (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℕ) (hell : 0 < ell)
    (u : LatticeResidues κ ell) (qD qC : κ → ℤ)
    (hC : powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u) = rayMap A qC)
    (a : RayChartRing R A) :
    rayPowerLaurentValue R A ell (divisorResidueSummand R A b ell hell u
      (divisorCartierTrivialization R A
        (powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u)) qC hC a)).1 *
          single (Multiplicative.ofAdd qD) 1 =
      mapDomain (rayChartPowerMonoidHom A ell) a *
        single (Multiplicative.ofAdd
          (cartierResidueExponent ell (latticeResidueRepresentative u) qD qC)) 1 := by
  let e := divisorCartierTrivialization R A
    (powerCoefficient A b (ell : ℤ) (latticeResidueRepresentative u)) qC hC
  have ha : e a = a • e 1 := by
    simpa only [smul_eq_mul, mul_one] using e.map_smul a 1
  change rayPowerLaurentValue R A ell (divisorResidueSummand R A b ell hell u (e a)).1 * _ = _
  rw [ha, map_smul]
  change (mapDomain (rayChartPowerMonoidHom A ell) a *
      rayPowerLaurentValue R A ell (divisorResidueSummand R A b ell hell u (e 1)).1) *
        single (Multiplicative.ofAdd qD) 1 = _
  rw [mul_assoc, divisorResidueSummand_cartier_generator]

end ToricPower

