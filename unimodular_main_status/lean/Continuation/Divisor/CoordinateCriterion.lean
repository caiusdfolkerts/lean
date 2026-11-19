module

public import Continuation.Divisor.Geometry
public import Continuation.Divisor.FanInterfaces

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.FanPurity
public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.Part08
public import Unimodular.FanBridge

@[expose] public section
noncomputable section

/-! Exact source bodies; see the accompanying sources manifest. -/

section Source_Continuation_Divisor_Rounding

/-!
# Exact ceiling criteria for positive Thomsen coefficients

The results hold for arbitrary finite integral coefficient families.  In a
maximal-cone basis they are precisely the numerical criterion in Proposition
6.3; no fan or divisor criterion is built into their definitions.
-/


open scoped BigOperators

namespace Unimodular.Rounding

variable {ι : Type*} [Fintype ι]

theorem sum_mul_lt_one (a d : ι → ℝ)
    (ha : (∑ i, max (a i) 0) ≤ 1)
    (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i < 1) :
    (∑ i, a i * d i) < 1 := by
  classical
  by_cases hpos : ∃ i, 0 < a i
  · obtain ⟨j, hj⟩ := hpos
    have hle (i : ι) : a i * d i ≤ max (a i) 0 := by
      rcases le_or_gt (a i) 0 with h | h
      · exact (mul_nonpos_of_nonpos_of_nonneg h (hd0 i)).trans (le_max_right _ _)
      · rw [max_eq_left h.le]
        simpa only [mul_one] using (mul_lt_mul_of_pos_left (hd1 i) h).le
    have hlt : a j * d j < max (a j) 0 := by
      rw [max_eq_left hj.le]
      simpa only [mul_one] using mul_lt_mul_of_pos_left (hd1 j) hj
    exact (Finset.sum_lt_sum (fun i _ => hle i) ⟨j, Finset.mem_univ j, hlt⟩).trans_le ha
  · have hnonpos : (∑ i, a i * d i) ≤ 0 := by
      apply Finset.sum_nonpos
      intro i _
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt (fun h => hpos ⟨i, h⟩)) (hd0 i)
    exact hnonpos.trans_lt zero_lt_one

/-- The positive coefficient mass is the exact obstruction to the ceiling
inequality, with every real input quantified. -/
theorem ceil_linear_ge_linear_ceil_iff (a : ι → ℤ) :
    (∀ x : ι → ℝ, (∑ i, a i * Int.ceil (x i)) ≤
      Int.ceil (∑ i, (a i : ℝ) * x i)) ↔
      (∑ i, max (a i) 0) ≤ 1 := by
  classical
  constructor
  · intro h
    let x : ι → ℝ := fun i => if 0 < a i then -(1 / 2 : ℝ) else 0
    have hceil (i : ι) : Int.ceil (x i) = 0 := by
      dsimp [x]
      split_ifs <;> norm_num
    have hn := h x
    simp only [hceil, mul_zero, Finset.sum_const_zero] at hn
    have hreal : (-1 : ℝ) < ∑ i, (a i : ℝ) * x i := by
      simpa using Int.le_ceil_iff.mp hn
    have hterm (i : ι) :
        (a i : ℝ) * x i = -((max (a i) 0 : ℤ) : ℝ) / 2 := by
      dsimp [x]
      by_cases hi : 0 < a i
      · rw [if_pos hi, max_eq_left hi.le]
        ring
      · rw [if_neg hi, max_eq_right (le_of_not_gt hi)]
        norm_num
    have hsum : (∑ i, (a i : ℝ) * x i) =
        -((∑ i, max (a i) 0 : ℤ) : ℝ) / 2 := by
      calc
        (∑ i, (a i : ℝ) * x i) = ∑ i, -((max (a i) 0 : ℤ) : ℝ) / 2 :=
          Finset.sum_congr rfl (fun i _ => hterm i)
        _ = -((∑ i, max (a i) 0 : ℤ) : ℝ) / 2 := by
          rw [← Finset.sum_div, Finset.sum_neg_distrib, Int.cast_sum]
    rw [hsum] at hreal
    have hlt : ((∑ i, max (a i) 0 : ℤ) : ℝ) < 2 := by linarith
    have hltZ : (∑ i, max (a i) 0) < (2 : ℤ) := by exact_mod_cast hlt
    omega
  · intro ha x
    apply Int.le_ceil_iff.mpr
    have haR : (∑ i, max (a i : ℝ) 0) ≤ 1 := by exact_mod_cast ha
    have hd0 (i : ι) : 0 ≤ (Int.ceil (x i) : ℝ) - x i :=
      sub_nonneg.mpr (Int.le_ceil (x i))
    have hd1 (i : ι) : (Int.ceil (x i) : ℝ) - x i < 1 := by
      have h := Int.ceil_lt_add_one (x i)
      linarith
    have herr := sum_mul_lt_one (fun i => (a i : ℝ))
      (fun i => (Int.ceil (x i) : ℝ) - x i) haR hd0 hd1
    simp only [mul_sub, Finset.sum_sub_distrib] at herr
    push_cast
    linarith

/-- A small negative coefficient mass forces every rounded solution of an
integral relation to have nonnegative weighted sum. -/
theorem rounded_relation_nonneg (c : ι → ℤ) (t : ι → ℝ)
    (hc : (∑ i, max (-c i) 0) ≤ 1)
    (ht : (∑ i, (c i : ℝ) * t i) = 0) :
    0 ≤ ∑ i, c i * Int.ceil (t i) := by
  have h := (ceil_linear_ge_linear_ceil_iff (fun i => -c i)).mpr hc t
  have hzero : (∑ i, ((-c i : ℤ) : ℝ) * t i) = 0 := by
    simp [Int.cast_neg, neg_mul, Finset.sum_neg_distrib, ht]
  rw [hzero, Int.ceil_zero] at h
  simpa only [neg_mul, Finset.sum_neg_distrib, neg_nonpos] using h

/-- The converse also holds for a normalized relation: coefficient one lets
the remaining coordinates range freely over its real solution hyperplane. -/
theorem rounded_relation_nonneg_iff {n : ℕ} (c : Fin (n + 1) → ℤ)
    (hc0 : c 0 = 1) :
    (∀ t : Fin (n + 1) → ℝ, (∑ i, (c i : ℝ) * t i) = 0 →
      0 ≤ ∑ i, c i * Int.ceil (t i)) ↔
      (∑ i, max (-c i) 0) ≤ 1 := by
  constructor
  · intro h
    have htail : ∀ x : Fin n → ℝ,
        (∑ i, (-c i.succ) * Int.ceil (x i)) ≤
          Int.ceil (∑ i, ((-c i.succ : ℤ) : ℝ) * x i) := by
      intro x
      let t : Fin (n + 1) → ℝ :=
        Fin.cons (∑ i, ((-c i.succ : ℤ) : ℝ) * x i) x
      have ht : (∑ i, (c i : ℝ) * t i) = 0 := by
        simp only [Fin.sum_univ_succ, t, Fin.cons_zero, Fin.cons_succ, hc0,
          Int.cast_one, one_mul, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
        abel
      have hn := h t ht
      simp only [Fin.sum_univ_succ, t, Fin.cons_zero, Fin.cons_succ, hc0,
        one_mul] at hn
      simp only [neg_mul, Finset.sum_neg_distrib]
      linarith
    have hmass := (ceil_linear_ge_linear_ceil_iff
      (fun i : Fin n => -c i.succ)).mp htail
    simpa [Fin.sum_univ_succ, hc0] using hmass
  · intro h t ht
    exact rounded_relation_nonneg c t h ht

theorem normalized_relation_sum_pos {n : ℕ} (c : Fin (n + 2) → ℤ)
    (hc0 : c 0 = 1) (hc1 : c 1 = 1)
    (hneg : (∑ i, max (-c i) 0) ≤ 1) :
    0 < ∑ i, c i := by
  have htail : 0 ≤ ∑ i : Fin n,
      (c i.succ.succ + max (-c i.succ.succ) 0) := by
    apply Finset.sum_nonneg
    intro i _
    have h := le_max_left (-c i.succ.succ) (0 : ℤ)
    omega
  rw [Finset.sum_add_distrib] at htail
  have hneg' : (∑ i : Fin n, max (-c i.succ.succ) 0) ≤ 1 := by
    simpa [Fin.sum_univ_succ, hc0, hc1] using hneg
  have hpos : 0 < 1 + (1 + ∑ i : Fin n, c i.succ.succ) := by omega
  simpa [Fin.sum_univ_succ, hc0, hc1] using hpos

/-- Intrinsic lattice formulation of the ceiling criterion. -/
theorem rounded_basis_inequality_iff {N : Type*} [AddCommGroup N]
    (b : Module.Basis ι ℤ N) (u : N) :
    (∀ θ : N →ₗ[ℤ] ℝ,
      (∑ i, b.repr u i * Int.ceil (θ (b i))) ≤ Int.ceil (θ u)) ↔
    (∑ i, max (b.repr u i) 0) ≤ 1 := by
  have heval (θ : N →ₗ[ℤ] ℝ) :
      θ u = ∑ i, (b.repr u i : ℝ) * θ (b i) := by
    calc
      θ u = θ (∑ i, b.repr u i • b i) := congrArg θ (b.sum_repr u).symm
      _ = ∑ i, (b.repr u i : ℝ) * θ (b i) := by
        simp only [map_sum, map_smul, ← Int.cast_smul_eq_zsmul ℝ, smul_eq_mul]
  constructor
  · intro h
    apply (ceil_linear_ge_linear_ceil_iff (fun i => b.repr u i)).mp
    intro x
    have hx := h (b.constr ℤ x)
    rw [heval] at hx
    simpa only [Module.Basis.constr_basis] using hx
  · intro h θ
    rw [heval]
    exact (ceil_linear_ge_linear_ceil_iff (fun i => b.repr u i)).mpr h
      (fun i => θ (b i))

end Unimodular.Rounding

#print axioms Unimodular.Rounding.ceil_linear_ge_linear_ceil_iff
#print axioms Unimodular.Rounding.rounded_relation_nonneg_iff
#print axioms Unimodular.Rounding.rounded_basis_inequality_iff

end Source_Continuation_Divisor_Rounding

section Source_Continuation_Divisor_MonomialDifferentials

/-!
# Differential transition functions of Laurent monomial coordinates

These calculations use ordinary derivations and Kähler differentials. They
provide the determinant calculation needed for the canonical sheaf of a
smooth toric variety; identifying a particular glued sheaf still requires
its chart and gluing comparison.
-/


open scoped BigOperators

namespace Unimodular.ToricDifferentials

variable {R K M : Type*} [CommRing R] [Field K] [Algebra R K]
  [AddCommGroup M] [Module K M] [Module R M]

/-- Logarithmic differentiation converts products of units to sums. -/
def logarithmicDerivation (D : Derivation R K M) : Kˣ →* Multiplicative M where
  toFun x := Multiplicative.ofAdd ((x : K)⁻¹ • D (x : K))
  map_one' := by
    change (1 : K)⁻¹ • D (1 : K) = 0
    simp
  map_mul' x y := by
    change (((x * y : Kˣ) : K)⁻¹ • D ((x * y : Kˣ) : K)) =
      (x : K)⁻¹ • D (x : K) + (y : K)⁻¹ • D (y : K)
    simp only [Units.val_mul, D.leibniz, mul_inv, smul_add, smul_smul]
    have h₁ : (x : K)⁻¹ * (y : K)⁻¹ * (x : K) = (y : K)⁻¹ := by field_simp
    have h₂ : (x : K)⁻¹ * (y : K)⁻¹ * (y : K) = (x : K)⁻¹ := by field_simp
    rw [h₁, h₂, add_comm]

@[simp] theorem logarithmicDerivation_apply (D : Derivation R K M) (x : Kˣ) :
    Multiplicative.toAdd (logarithmicDerivation D x) = (x : K)⁻¹ • D (x : K) := rfl

theorem logarithmicDerivation_prod_zpow {ι : Type*} [Fintype ι]
    (D : Derivation R K M) (x : ι → Kˣ) (a : ι → ℤ) :
    (((∏ i, x i ^ a i : Kˣ) : K)⁻¹ • D ((∏ i, x i ^ a i : Kˣ) : K)) =
      ∑ i, a i • ((x i : K)⁻¹ • D (x i : K)) := by
  have h := map_prod (logarithmicDerivation D) (fun i => x i ^ a i) Finset.univ
  simpa only [toAdd_prod, map_zpow, toAdd_zpow, logarithmicDerivation_apply] using
    congrArg Multiplicative.toAdd h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Jacobian determinant of an arbitrary Laurent monomial substitution. -/
theorem determinant_derivative_monomials (D : Derivation R K M)
    (x : ι → Kˣ) (a : Matrix ι ι ℤ) (b : Module.Basis ι K M)
    (hb : ∀ i, D (x i : K) = b i) :
    b.det (fun i => D ((∏ j, x j ^ a j i : Kˣ) : K)) =
      ((∏ i, ((∏ j, x j ^ a j i : Kˣ) : K)) / (∏ j, (x j : K))) *
        (a.det : K) := by
  let y : ι → Kˣ := fun i => ∏ j, x j ^ a j i
  have hcoord : b.toMatrix (fun i => (y i : K)⁻¹ • D (y i : K)) =
      Matrix.of (fun j i => (x j : K)⁻¹ * (a j i : K)) := by
    ext j i
    rw [Module.Basis.toMatrix_apply]
    dsimp [y]
    rw [logarithmicDerivation_prod_zpow]
    simp [map_sum, map_smul, hb, Module.Basis.repr_self, Finsupp.sum_apply,
      Finsupp.smul_apply, Finsupp.single_apply, mul_comm]
  have hdet : b.det (fun i => (y i : K)⁻¹ • D (y i : K)) =
      (∏ j, (x j : K)⁻¹) * (a.det : K) := by
    rw [Module.Basis.det_apply, hcoord]
    have hcol := Matrix.det_mul_column (fun j => (x j : K)⁻¹)
      ((Int.castRingHom K).mapMatrix a)
    rw [← (Int.castRingHom K).map_det] at hcol
    exact hcol
  have hy (i : ι) : D (y i : K) =
      (y i : K) • ((y i : K)⁻¹ • D (y i : K)) := by
    simp [smul_smul]
  change b.det (fun i => D (y i : K)) =
    ((∏ i, (y i : K)) / (∏ j, (x j : K))) * (a.det : K)
  calc
    b.det (fun i => D (y i : K)) =
        b.det (fun i => (y i : K) • ((y i : K)⁻¹ • D (y i : K))) := by
      congr 1
      funext i
      exact hy i
    _ = (∏ i, (y i : K)) * b.det (fun i => (y i : K)⁻¹ • D (y i : K)) := by
      exact b.det.map_smul_univ _ _
    _ = ((∏ i, (y i : K)) / (∏ j, (x j : K))) * (a.det : K) := by
      rw [hdet, Finset.prod_inv_distrib]
      simp only [div_eq_mul_inv, mul_assoc]

/-- Unimodular Laurent coordinate changes preserve differential bases in
every characteristic. -/
theorem basis_derivative_monomials (D : Derivation R K M) (x : ι → Kˣ)
    (a : Matrix ι ι ℤ) (b : Module.Basis ι K M)
    (hb : ∀ i, D (x i : K) = b i) (ha : IsUnit a.det) :
    LinearIndependent K (fun i => D ((∏ j, x j ^ a j i : Kˣ) : K)) ∧
      Submodule.span K (Set.range (fun i => D ((∏ j, x j ^ a j i : Kˣ) : K))) = ⊤ := by
  apply b.is_basis_iff_det.mpr
  rw [determinant_derivative_monomials D x a b hb]
  have hu : IsUnit (((∏ i, ((∏ j, x j ^ a j i : Kˣ) : K))) /
      ∏ j, (x j : K)) := by
    rw [isUnit_iff_ne_zero]
    apply div_ne_zero
    · exact Finset.prod_ne_zero_iff.mpr
        (fun i _ => Units.ne_zero (∏ j, x j ^ a j i))
    · exact Finset.prod_ne_zero_iff.mpr (fun j _ => Units.ne_zero (x j))
  exact hu.mul (ha.map (Int.castRingHom K))

section PolynomialCharts

variable (R : Type*) [CommRing R] (ι : Type*) (A : Type*)
  [CommRing A] [Algebra R A] [Algebra (MvPolynomial ι R) A]
  [IsScalarTower R (MvPolynomial ι R) A]
  (S : Submonoid (MvPolynomial ι R)) [IsLocalization S A]

/-- Actual Kähler differentials of a localized polynomial chart. -/
noncomputable def localizedPolynomialDifferentialBasis : Module.Basis ι A Ω[A⁄R] :=
  (KaehlerDifferential.mvPolynomialBasis R ι).ofIsLocalizedModule A S
    (KaehlerDifferential.map R R (MvPolynomial ι R) A)

@[simp] theorem localizedPolynomialDifferentialBasis_apply (i : ι) :
    localizedPolynomialDifferentialBasis R ι A S i =
      KaehlerDifferential.D R A (algebraMap (MvPolynomial ι R) A (.X i)) := by
  simp [localizedPolynomialDifferentialBasis, KaehlerDifferential.map_D]

end PolynomialCharts
end Unimodular.ToricDifferentials

#print axioms Unimodular.ToricDifferentials.logarithmicDerivation_prod_zpow
#print axioms Unimodular.ToricDifferentials.determinant_derivative_monomials
#print axioms Unimodular.ToricDifferentials.basis_derivative_monomials
#print axioms Unimodular.ToricDifferentials.localizedPolynomialDifferentialBasis_apply

end Source_Continuation_Divisor_MonomialDifferentials


section Source_Continuation_Divisor_ThomsenSupport

/-!
# Positive Thomsen coefficients and genuine global generation

The ceiling criterion is applied to every maximal cone and every actual
ray.  The resulting support condition is then fed to the independently
proved global-section construction.  This file calls that intermediate
condition *convex support*: its equivalence with a curve-degree definition
of nefness is a separate geometric theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Unimodular.Thomsen

open AlgebraicGeometry
open PaperVerification.ToricGeometry PaperVerification.ToricSchemes

variable {n : ℕ} (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)

/-- The ordinary ceiling coefficients of a point in the real character
space.  Quantifying over all points also quantifies over all strata. -/
def positiveCoefficients (θ : Lattice n →ₗ[ℤ] ℝ) : Lattice n → ℤ :=
  fun u => Int.ceil (θ u)

lemma linear_map_embed_basis_expansion (b : Module.Basis (Fin n) ℤ (Lattice n))
    (ℓ : Ambient n →ₗ[ℝ] ℝ) (u : Lattice n) :
    ℓ (PaperVerification.ToricGeometry.embed n u) = ∑ i, (b.repr u i : ℝ) * ℓ (PaperVerification.ToricGeometry.embed n (b i)) := by
  calc
    ℓ (PaperVerification.ToricGeometry.embed n u) = ℓ (∑ i, (integralBasisReal b).repr (PaperVerification.ToricGeometry.embed n u) i •
        integralBasisReal b i) := congrArg ℓ ((integralBasisReal b).sum_repr _).symm
    _ = _ := by simp only [map_sum, map_smul, integralBasisReal_repr,
      integralBasisReal_apply, smul_eq_mul]

/-- Convex support is exactly the full-cone coordinate inequalities.  Purity
is derived from the smooth complete fan axioms, not supplied as a hypothesis. -/
theorem convexSupport_iff_coordinates (a : Lattice n → ℝ) :
    F.IsNef a ↔ ∀ s : F.fullCones, ∀ u ∈ F.rays,
      (∑ i, ((F.fullConeBasis s).repr u i : ℝ) * a (F.fullConeBasis s i)) ≤ a u := by
  constructor
  · intro ha s u hu
    obtain ⟨ℓ, he, hle⟩ := ha s.val (F.fullCones_mem s)
    have hb (i : Fin n) : ℓ (PaperVerification.ToricGeometry.embed n (F.fullConeBasis s i)) = a (F.fullConeBasis s i) := by
      apply he
      rw [F.fullConeBasis_ray_set]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have h := hle u hu
    rw [linear_map_embed_basis_expansion (F.fullConeBasis s) ℓ u] at h
    simpa only [hb] using h
  · intro h s hs
    obtain ⟨t, ht, hst, hcard⟩ := F.isPure s hs
    let t' : F.fullCones := ⟨t, Finset.mem_filter.mpr ⟨ht, hcard⟩⟩
    let b := F.fullConeBasis t'
    let ℓ : Ambient n →ₗ[ℝ] ℝ := (integralBasisReal b).constr ℝ (fun i => a (b i))
    have hb (i : Fin n) : ℓ (PaperVerification.ToricGeometry.embed n (b i)) = a (b i) := by
      rw [← integralBasisReal_apply]
      exact (integralBasisReal b).constr_basis ℝ _ i
    refine ⟨ℓ, ?_, ?_⟩
    · intro u hu
      have hut : u ∈ (t' : Finset (Lattice n)) := hst hu
      rw [F.fullConeBasis_ray_set] at hut
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hut
      exact hb i
    · intro u hu
      rw [linear_map_embed_basis_expansion b ℓ u]
      simp only [hb]
      exact h t' u hu

/-- Exact maximal-cone version of Proposition 6.3's positive-coordinate
criterion, for every real character and every ray. -/
theorem positiveThomsen_convexSupport_iff :
    (∀ θ : Lattice n →ₗ[ℤ] ℝ,
      F.IsNef (fun u => (positiveCoefficients θ u : ℝ))) ↔
    ∀ s : F.fullCones, ∀ u ∈ F.rays,
      (∑ i, max ((F.fullConeBasis s).repr u i) 0) ≤ 1 := by
  constructor
  · intro h s u hu
    apply (Unimodular.Rounding.rounded_basis_inequality_iff (F.fullConeBasis s) u).mp
    intro θ
    have hh := (convexSupport_iff_coordinates F _).mp (h θ) s u hu
    exact_mod_cast hh
  · intro h θ
    apply (convexSupport_iff_coordinates F _).mpr
    intro s u hu
    have hh := (Unimodular.Rounding.rounded_basis_inequality_iff
      (F.fullConeBasis s) u).mpr (h s u hu) θ
    exact_mod_cast hh

/-- Each ceiling divisor is an actual globally generated invertible sheaf
under the positive-coordinate criterion. -/
theorem positiveThomsen_isGloballyGenerated (k : Type*) [Field k]
    (h : ∀ s : F.fullCones, ∀ u ∈ F.rays,
      (∑ i, max ((F.fullConeBasis s).repr u i) 0) ≤ 1)
    (θ : Lattice n →ₗ[ℤ] ℝ) :
    (Unimodular.NefBig.cocycleInvertibleSheaf
      (F.fanCartierCocycle k F.isPure (positiveCoefficients θ))).IsGloballyGenerated :=
  Unimodular.NefBig.fanCartier_isGloballyGenerated F k _
    ((positiveThomsen_convexSupport_iff F).mpr h θ)

/-- The ceiling criterion refers to the same ordinary fan and primitive
lattice rays as the classification theorems. -/
theorem positiveThomsen_convexSupport_iff_intrinsic :
    (∀ θ : Lattice n →ₗ[ℤ] ℝ,
      F.IsNef (fun u => (positiveCoefficients θ u : ℝ))) ↔
      Unimodular.ConeBases.PositiveCriterion
        (Unimodular.FanInterfaces.dictionaryToricFan F) :=
  (positiveThomsen_convexSupport_iff F).trans
    (Unimodular.FanInterfaces.dictionaryPositiveCriterion_iff F).symm

#print axioms positiveThomsen_convexSupport_iff
#print axioms positiveThomsen_isGloballyGenerated

end Unimodular.Thomsen

end Source_Continuation_Divisor_ThomsenSupport

section Source_Continuation_Divisor_FanRelativeDimension

/-!
# The dimension of a smooth complete fan scheme

The dimension parameter is recovered from the actual polynomial chart
algebras.  In particular it is not an extra field of `SmoothCompleteFan`.
The proof includes dimension zero and does not require projectivity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace Unimodular.NefBig

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes PaperVerification.ToricCharacters
open PaperVerification.ToricGeometry

variable {n : ℕ} (F : PaperVerification.ToricGeometry.SmoothCompleteFan n) (k : Type u) [Field k]

/-- A full chart is standard smooth of the precise lattice rank. -/
theorem fullChartAlgebra_smoothOfRelativeDimension (s : F.fullCones) :
    Algebra.IsStandardSmoothOfRelativeDimension n k
      (monoidChartAlgebra k (dualConeMonoid (s : Finset (Lattice n)))) := by
  have hcard : Nat.card (Finset.univ : Finset (Fin n)) = n := by simp
  letI : Algebra.IsStandardSmoothOfRelativeDimension n k
      (MvPolynomial (Finset.univ : Finset (Fin n)) k) := by
    simpa only [hcard] using
      (Algebra.IsStandardSmoothOfRelativeDimension.mvPolynomial k
        (Finset.univ : Finset (Fin n)))
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv n
    (fullChartPolynomialEquivUniv F k s).symm

/-- The full-chart structure map has the expected smooth relative dimension. -/
theorem fullChart_smoothOfRelativeDimensionViaCoordinates (s : F.fullCones) :
    SmoothOfRelativeDimension n
      (coneChart k (s : Finset (Lattice n)) ↘ Spec (CommRingCat.of k)) := by
  letI := fullChartAlgebra_smoothOfRelativeDimension F k s
  change SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom
    (algebraMap k (monoidChartAlgebra k (dualConeMonoid (s : Finset (Lattice n)))))))
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)).mpr
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).mpr inferInstance

/-- Every cone chart is an open subscheme of a full chart, by proved purity. -/
theorem coneChart_smoothOfRelativeDimension (s : Finset (Lattice n))
    (hs : s ∈ F.cones) :
    SmoothOfRelativeDimension n (coneChart k s ↘ Spec (CommRingCat.of k)) := by
  obtain ⟨t, ht, hst, hcard⟩ := F.isPure s hs
  let t' : F.fullCones := ⟨t, Finset.mem_filter.mpr ⟨ht, hcard⟩⟩
  letI := fullChart_smoothOfRelativeDimensionViaCoordinates F k t'
  letI := F.coneChartFaceMap_isOpenImmersion k t s ht hst
  rw [← comp_over (coneChartFaceMap k hst) (Spec (CommRingCat.of k))]
  simpa only [Nat.zero_add] using
    (inferInstance : SmoothOfRelativeDimension (0 + n)
      (coneChartFaceMap k hst ≫
        (coneChart k t ↘ Spec (CommRingCat.of k))))

/-- The actual glued scheme is smooth of relative dimension equal to the
lattice rank, without a projectivity assumption. -/
theorem fanScheme_smoothOfRelativeDimensionViaAllCones :
    SmoothOfRelativeDimension n (F.fanScheme k ↘ Spec (CommRingCat.of k)) := by
  apply IsZariskiLocalAtSource.of_openCover
    (P := @SmoothOfRelativeDimension n) (F.fanSchemeOpenCover k)
  intro s
  change SmoothOfRelativeDimension n
    (F.fanChartMap k s ≫ (F.fanScheme k ↘ Spec (CommRingCat.of k)))
  rw [comp_over]
  exact coneChart_smoothOfRelativeDimension F k s.val s.property

#print axioms fullChartAlgebra_smoothOfRelativeDimension
#print axioms fanScheme_smoothOfRelativeDimensionViaAllCones

end Unimodular.NefBig

end Source_Continuation_Divisor_FanRelativeDimension

#eval "DIVISOR_COORDINATE_CRITERION_END"
