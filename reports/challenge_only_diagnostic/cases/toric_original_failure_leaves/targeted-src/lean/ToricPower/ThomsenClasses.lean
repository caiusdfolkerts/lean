module

public import ToricPower.ThomsenGrid

@[expose] public section
noncomputable section

open Set Matrix
open scoped BigOperators Pointwise

namespace ToricPower

variable {n s : ℕ}

/-- The exact universal grid statement in the integral divisor-class quotient.
All sign patterns, dimensions, and integer ray matrices are allowed. -/
theorem thomsenClasses_eq_frobenius_universal (A : Matrix (Fin s) (Fin n) ℤ)
    (e : Fin s → ℤ) (he : IsSignPattern e) :
    thomsenClasses A e = frobeniusClasses A e (universalDenominator A : ℤ) := by
  classical
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    let m : Fin n → ℤ := fun j => ⌊x j⌋
    let x' : Fin n → ℝ := x - fun j => (m j : ℝ)
    let a' : Fin s → ℤ := patternCoefficient e (realRayMap A x) - rayMap A m
    have hbox : ∀ j, 0 ≤ x' j ∧ x' j ≤ 1 := by
      intro j
      change 0 ≤ Int.fract (x j) ∧ Int.fract (x j) ≤ 1
      exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
    have himage : realRayMap A (fun j => (m j : ℝ)) =
        fun i => (rayMap A m i : ℝ) := by
      ext i
      exact realRayMap_integer A m i
    have hx : patternCoefficient e (realRayMap A x') = a' := by
      dsimp [x', a']
      rw [realRayMap_sub, himage, patternCoefficient_sub_int]
    obtain ⟨z, hz⟩ := rounding_cell_grid A e a' he x' hbox hx
    refine ⟨z, ?_⟩
    change divisorClass A (powerCoefficient A e (universalDenominator A : ℤ) z) =
      divisorClass A (patternCoefficient e (realRayMap A x))
    rw [hz]
    exact divisorClass_sub_rayMap A _ m
  · rintro ⟨z, rfl⟩
    refine ⟨(universalDenominator A : ℝ)⁻¹ • (fun j => (z j : ℝ)), ?_⟩
    change divisorClass A (patternCoefficient e
      (realRayMap A ((universalDenominator A : ℝ)⁻¹ • (fun j => (z j : ℝ))))) =
        divisorClass A (powerCoefficient A e (universalDenominator A : ℤ) z)
    rw [patternCoefficient_on_grid A e he _ (universalDenominator_pos A)]

theorem frobeniusClasses_subset_thomsen (A : Matrix (Fin s) (Fin n) ℤ)
    (e : Fin s → ℤ) (he : IsSignPattern e) (ell : ℤ) (hell : 0 < ell) :
    frobeniusClasses A e ell ⊆ thomsenClasses A e := by
  have hnat : 0 < ell.toNat := by omega
  have heq : (ell.toNat : ℤ) = ell := Int.toNat_of_nonneg hell.le
  rintro a ⟨z, rfl⟩
  refine ⟨(ell.toNat : ℝ)⁻¹ • (fun j => (z j : ℝ)), ?_⟩
  change divisorClass A (patternCoefficient e
    (realRayMap A ((ell.toNat : ℝ)⁻¹ • (fun j => (z j : ℝ))))) =
      divisorClass A (powerCoefficient A e ell z)
  rw [patternCoefficient_on_grid A e he _ hnat, heq]

/-- The union is over all positive integer exponents, not merely multiples of R. -/
theorem thomsenClasses_eq_union_positive (A : Matrix (Fin s) (Fin n) ℤ)
    (e : Fin s → ℤ) (he : IsSignPattern e) :
    thomsenClasses A e =
      ⋃ ell : ℤ, ⋃ (_h : 0 < ell), frobeniusClasses A e ell := by
  ext a
  constructor
  · intro ha
    have hR : (0 : ℤ) < universalDenominator A := by
      exact_mod_cast universalDenominator_pos A
    apply Set.mem_iUnion.mpr
    refine ⟨(universalDenominator A : ℤ), Set.mem_iUnion.mpr ⟨hR, ?_⟩⟩
    rw [← thomsenClasses_eq_frobenius_universal A e he]
    exact ha
  · intro ha
    obtain ⟨ell, ha⟩ := Set.mem_iUnion.mp ha
    obtain ⟨hell, ha⟩ := Set.mem_iUnion.mp ha
    exact frobeniusClasses_subset_thomsen A e he ell hell ha

abbrev RealDivisorClass (A : Matrix (Fin s) (Fin n) ℤ) :=
  (Fin s → ℝ) ⧸ LinearMap.range (A.map (Int.castRingHom ℝ)).mulVecLin

def realDivisorQuotient (A : Matrix (Fin s) (Fin n) ℤ) :
    (Fin s → ℝ) →ₗ[ℝ] RealDivisorClass A :=
  (LinearMap.range (A.map (Int.castRingHom ℝ)).mulVecLin).mkQ

def realDivisorClass (A : Matrix (Fin s) (Fin n) ℤ) (a : Fin s → ℤ) :
    RealDivisorClass A := realDivisorQuotient A (fun i => (a i : ℝ))

/-- The literal projection of the closed cube [-1,0]^s to the real cokernel. -/
def realZonotope (A : Matrix (Fin s) (Fin n) ℤ) : Set (RealDivisorClass A) :=
  realDivisorQuotient A '' Set.Icc (-1 : Fin s → ℝ) 0

lemma realDivisorClass_mem_zonotope_iff (A : Matrix (Fin s) (Fin n) ℤ)
    (a : Fin s → ℤ) :
    realDivisorClass A a ∈ realZonotope A ↔
      ∃ x : Fin n → ℝ, ∀ i,
        -1 ≤ (a i : ℝ) - realRayMap A x i ∧
          (a i : ℝ) - realRayMap A x i ≤ 0 := by
  constructor
  · rintro ⟨y, hy, heq⟩
    have hdiff : (fun i => (a i : ℝ)) - y ∈
        LinearMap.range (A.map (Int.castRingHom ℝ)).mulVecLin := by
      apply (Submodule.Quotient.eq _).mp
      exact heq.symm
    obtain ⟨x, hx⟩ := hdiff
    refine ⟨x, ?_⟩
    intro i
    have hi := congrFun hx i
    change realRayMap A x i = (a i : ℝ) - y i at hi
    have hl := hy.1 i
    have hu := hy.2 i
    change -1 ≤ y i at hl
    change y i ≤ 0 at hu
    constructor <;> linarith
  · rintro ⟨x, hx⟩
    let y : Fin s → ℝ := (fun i => (a i : ℝ)) - realRayMap A x
    refine ⟨y, ⟨fun i => (hx i).1, fun i => (hx i).2⟩, ?_⟩
    symm
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨x, ?_⟩
    change realRayMap A x = (fun i => (a i : ℝ)) - y
    dsimp [y]
    abel

/-- The second grid assertion of Lemma 6.1, stated with an arbitrary integral
representative. The class equality retains the entire integral cokernel,
including torsion; only zonotope membership is tested after realification. -/
theorem paper_lemma_6_1_zonotope_grid (A : Matrix (Fin s) (Fin n) ℤ)
    (a : Fin s → ℤ) (ha : realDivisorClass A a ∈ realZonotope A) :
    ∃ a' : Fin s → ℤ, divisorClass A a' = divisorClass A a ∧
      ∃ z : Fin n → ℤ, ∀ i,
        -1 ≤ (a' i : ℝ) -
          realRayMap A ((universalDenominator A : ℝ)⁻¹ • (fun j => (z j : ℝ))) i ∧
        (a' i : ℝ) -
          realRayMap A ((universalDenominator A : ℝ)⁻¹ • (fun j => (z j : ℝ))) i ≤ 0 := by
  classical
  obtain ⟨r, hr⟩ := (realDivisorClass_mem_zonotope_iff A a).mp ha
  let m : Fin n → ℤ := fun j => ⌊r j⌋
  let x : Fin n → ℝ := r - fun j => (m j : ℝ)
  let a' : Fin s → ℤ := a - rayMap A m
  have hbox : ∀ j, 0 ≤ x j ∧ x j ≤ 1 := by
    intro j
    change 0 ≤ Int.fract (r j) ∧ Int.fract (r j) ≤ 1
    exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have hAx (i : Fin s) : realRayMap A x i =
      realRayMap A r i - (rayMap A m i : ℝ) := by
    dsimp [x]
    rw [realRayMap_sub]
    simp only [Pi.sub_apply, realRayMap_integer]
  have hx : x ∈ slopePolytope A a' := by
    rw [mem_slopePolytope_iff]
    refine ⟨hbox, ?_⟩
    intro i
    have hi := hr i
    rw [hAx]
    dsimp [a']
    push_cast
    constructor <;> linarith
  have hv : (slopeVertices A a' : Set (Fin n → ℝ)).Nonempty := by
    apply (convexHull_nonempty_iff (𝕜 := ℝ)).mp
    rw [← slopePolytope_eq_convexHull]
    exact ⟨x, hx⟩
  obtain ⟨q, hq⟩ := hv
  have hqQ : q ∈ slopePolytope A a' := by
    rw [slopePolytope_eq_convexHull]
    exact subset_convexHull ℝ _ hq
  have hqD := slope_vertex_denominator A a' q hq
  have hqR : (universalDenominator A : ℝ) • q ∈ integerLattice n := by
    have hh := (integerLattice n).nsmul_mem hqD (dimensionDenominator n)
    rw [universalDenominator, Nat.cast_mul, mul_comm, mul_smul]
    simpa only [Nat.cast_smul_eq_nsmul] using hh
  obtain ⟨z, hz⟩ := hqR
  have hzfun : (fun j => (z j : ℝ)) = (universalDenominator A : ℝ) • q := funext hz
  have hR : (universalDenominator A : ℝ) ≠ 0 := by
    exact_mod_cast (universalDenominator_pos A).ne'
  have hqeq : q = (universalDenominator A : ℝ)⁻¹ • (fun j => (z j : ℝ)) := by
    rw [hzfun, smul_smul, inv_mul_cancel₀ hR, one_smul]
  refine ⟨a', divisorClass_sub_rayMap A a m, z, ?_⟩
  intro i
  rw [← hqeq]
  have hi := ((mem_slopePolytope_iff A a' q).mp hqQ).2 i
  constructor <;> linarith

end ToricPower
