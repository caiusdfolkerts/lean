module

public import PaperVerification.GenericSectionCriticalLocus
public import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic

/-!
# Universal critical equations for a generated vector bundle

The variables are the original section parameters and a normalized projective
relation between their differentials. The quotient below is the literal
critical incidence algebra. A nonzero polynomial in the original parameters
vanishes nilpotently on it.

The differential expansion and minimal-prime strategy adapt the scalar proof
in OpenAI's `CriticalLocus.lean` and `LinearFamilies.lean`, commit
`4eaee87548250b2682affda7d05d947c05554bae` (Apache-2.0). The vector-valued
critical equations and their full parameter statement are developed here.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open KaehlerDifferential MvPolynomial

namespace PaperVerification.GenericSectionDifferentials

section Coordinates
variable {K R A ι κ τ : Type*} [CommRing K] [CommRing R] [CommRing A]
  [Algebra K R] [Algebra K A] [Algebra R A] [IsScalarTower K R A]
  [Fintype ι] [Fintype κ] [Fintype τ]

lemma differential_expansion (b : Module.Basis τ R Ω[R⁄K]) (x : R) :
    D K A (algebraMap R A x) =
      ∑ t, algebraMap R A (b.repr (D K R x) t) •
        KaehlerDifferential.map K K R A (b t) := by
  have h := congrArg (KaehlerDifferential.map K K R A) (b.sum_repr (D K R x))
  simpa only [map_sum,map_smul,IsScalarTower.algebraMap_smul,
    KaehlerDifferential.map_D] using h.symm

lemma critical_of_matrix_coordinates (b : Module.Basis τ R Ω[R⁄K])
    (v : Matrix κ ι R) (a : ι → A) (c : κ → A)
    (h : ∀ t, ∑ j, c j * (∑ i,
      a i * algebraMap R A (b.repr (D K R (v j i)) t))=0) :
    ∑ j, c j • (∑ i, a i • D K A (algebraMap R A (v j i)))=0 := by
  classical
  calc
    _ = ∑ j, ∑ t, ∑ i,
        (c j*a i*algebraMap R A (b.repr (D K R (v j i)) t)) •
          KaehlerDifferential.map K K R A (b t) := by
      simp_rw [differential_expansion b,Finset.smul_sum,← mul_smul,mul_assoc]
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.sum_comm
    _ = ∑ t, (∑ j, c j * (∑ i,
        a i * algebraMap R A (b.repr (D K R (v j i)) t))) •
          KaehlerDifferential.map K K R A (b t) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      simp only [Finset.mul_sum,Finset.sum_smul,mul_assoc]
    _ = 0 := by simp only [h,zero_smul,Finset.sum_const_zero]
end Coordinates

section Universal
variable {K R ι κ τ : Type*} [Field K] [CharZero K] [CommRing R]
  [Algebra K R] [Fintype ι] [Fintype κ] [Fintype τ] [DecidableEq κ]

/-- Universal linear section components, with parameters indexed by `ι`. -/
def universalVectorSection (v : Matrix κ ι R) (j : κ) :
    MvPolynomial (Sum ι κ) R :=
  ∑ i, X (Sum.inl i)*C (v j i)

/-- Coordinates of a universal linear relation between the section gradients. -/
def universalCriticalGradient (b : Module.Basis τ R Ω[R⁄K])
    (v : Matrix κ ι R) (t : τ) : MvPolynomial (Sum ι κ) R :=
  ∑ j, X (Sum.inr j) * (∑ i, X (Sum.inl i)*C (b.repr (D K R (v j i)) t))

/-- The section equations, the critical equations, and one normalization. -/
def universalCriticalEquation (b : Module.Basis τ R Ω[R⁄K])
    (v : Matrix κ ι R) (j₀ : κ) : Sum κ (Sum τ Unit) → MvPolynomial (Sum ι κ) R
  | Sum.inl j => universalVectorSection v j
  | Sum.inr (Sum.inl t) => universalCriticalGradient b v t
  | Sum.inr (Sum.inr _) => X (Sum.inr j₀)-1

def universalCriticalIdeal (b : Module.Basis τ R Ω[R⁄K])
    (v : Matrix κ ι R) (j₀ : κ) : Ideal (MvPolynomial (Sum ι κ) R) :=
  Ideal.span (Set.range (universalCriticalEquation b v j₀))

/-- The entire normalized critical incidence scheme lies over the vanishing
set of a nonzero polynomial in the original section parameters. -/
theorem universal_critical_parameter_polynomial [Algebra.FiniteType K R]
    (b : Module.Basis τ R Ω[R⁄K]) (v : Matrix κ ι R)
    (u : Matrix ι κ R) (hvu : v*u=1) (j₀ : κ) :
    ∃ p : MvPolynomial ι K, p≠0 ∧
      IsNilpotent (MvPolynomial.aeval (fun i =>
        algebraMap (MvPolynomial (Sum ι κ) R)
          (MvPolynomial (Sum ι κ) R ⧸ universalCriticalIdeal b v j₀)
          (X (Sum.inl i))) p) := by
  classical
  let T := MvPolynomial (Sum ι κ) R
  let A := T ⧸ universalCriticalIdeal b v j₀
  let a : ι → A := fun i => algebraMap T A (X (Sum.inl i))
  let c : κ → A := fun j => algebraMap T A (X (Sum.inr j))
  have hC (r : R) : algebraMap T A (C r)=algebraMap R A r := rfl
  have he (z : Sum κ (Sum τ Unit)) :
      algebraMap T A (universalCriticalEquation b v j₀ z)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self z))
  have hc : c j₀=1 := by
    have h := he (Sum.inr (Sum.inr ()))
    simpa only [universalCriticalEquation,map_sub,map_one,sub_eq_zero,c] using h
  have hz : ∀ j, ∑ i, a i*algebraMap R A (v j i)=0 := by
    intro j
    have h := he (Sum.inl j)
    simpa only [universalCriticalEquation,universalVectorSection,
      map_sum,map_mul,hC,a] using h
  have hg : ∀ t, ∑ j, c j * (∑ i,
      a i*algebraMap R A (b.repr (D K R (v j i)) t))=0 := by
    intro t
    have h := he (Sum.inr (Sum.inl t))
    simpa only [universalCriticalEquation,universalCriticalGradient,
      map_sum,map_mul,hC,a,c] using h
  have hvu' : v.map (algebraMap R A) * u.map (algebraMap R A)=1 := by
    simpa only [Matrix.map_mul,Matrix.map_one,map_zero,map_one] using
      congrArg (Matrix.map · (algebraMap R A)) hvu
  exact critical_incidence_polynomial (v.map (algebraMap R A))
    (u.map (algebraMap R A)) hvu' a c j₀ hc hz
    (critical_of_matrix_coordinates b v a c hg)

/-- Any field-valued critical point annihilates the universal parameter
polynomial. This is a consequence of nilpotence, so it applies to arbitrary
(nonreduced) universal incidence algebras as well. -/
theorem critical_specialization_polynomial_zero
    {L : Type*} [Field L] [Algebra K L]
    (b : Module.Basis τ R Ω[R⁄K]) (v : Matrix κ ι R) (j₀ : κ)
    (p : MvPolynomial ι K)
    (hp : IsNilpotent (MvPolynomial.aeval (fun i =>
      algebraMap (MvPolynomial (Sum ι κ) R)
        (MvPolynomial (Sum ι κ) R ⧸ universalCriticalIdeal b v j₀)
        (X (Sum.inl i))) p))
    (χ : R →ₐ[K] L) (a : ι → L) (c : κ → L) (hc : c j₀=1)
    (hz : ∀ j, ∑ i, a i*χ (v j i)=0)
    (hg : ∀ t, ∑ j, c j*(∑ i, a i*χ (b.repr (D K R (v j i)) t))=0) :
    MvPolynomial.aeval a p=0 := by
  classical
  let T := MvPolynomial (Sum ι κ) R
  let A := T ⧸ universalCriticalIdeal b v j₀
  let ψ : T →ₐ[K] L := MvPolynomial.aevalTower χ (Sum.elim a c)
  have hψX (i : Sum ι κ) : ψ (X i) = Sum.elim a c i :=
    MvPolynomial.aevalTower_X χ (Sum.elim a c) i
  have hψC (r : R) : ψ (C r) = χ r :=
    MvPolynomial.aevalTower_C χ (Sum.elim a c) r
  have hkill : universalCriticalIdeal b v j₀ ≤ RingHom.ker ψ.toRingHom := by
    apply Ideal.span_le.mpr
    rintro x ⟨z,rfl⟩
    change ψ (universalCriticalEquation b v j₀ z)=0
    rcases z with j | (t | _)
    · simpa only [universalCriticalEquation,universalVectorSection,
        map_sum,map_mul,hψX,hψC,
        Sum.elim_inl] using hz j
    · simpa only [universalCriticalEquation,universalCriticalGradient,
        map_sum,map_mul,hψX,hψC,
        Sum.elim_inl,Sum.elim_inr] using hg t
    · simp only [universalCriticalEquation,map_sub,map_one,
        hψX,Sum.elim_inr,hc,sub_self]
  let φ : A →ₐ[K] L := Ideal.Quotient.liftₐ _ ψ (fun x hx => hkill hx)
  have hφ (i : ι) : φ (algebraMap T A (X (Sum.inl i)))=a i := by
    change ψ (X (Sum.inl i)) = a i
    exact hψX (Sum.inl i)
  have hnil := hp.map φ.toRingHom
  have he : φ (MvPolynomial.aeval (fun i => algebraMap T A (X (Sum.inl i))) p)=0 :=
    isNilpotent_iff_eq_zero.mp hnil
  rw [MvPolynomial.comp_aeval_apply] at he
  simpa only [hφ] using he

/-- One nonzero polynomial excludes every normalized critical-relation chart. -/
def criticalAvoidancePolynomial [Algebra.FiniteType K R]
    (b : Module.Basis τ R Ω[R⁄K]) (v : Matrix κ ι R)
    (u : Matrix ι κ R) (hvu : v*u=1) : MvPolynomial ι K :=
  ∏ j, Classical.choose (universal_critical_parameter_polynomial b v u hvu j)

theorem criticalAvoidancePolynomial_ne_zero [Algebra.FiniteType K R]
    (b : Module.Basis τ R Ω[R⁄K]) (v : Matrix κ ι R)
    (u : Matrix ι κ R) (hvu : v*u=1) :
    criticalAvoidancePolynomial b v u hvu≠0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact (Classical.choose_spec (universal_critical_parameter_polynomial b v u hvu j)).1

/-- On this principal open, no nonzero relation between the gradient rows can
occur at a common zero over any extension field. -/
theorem specialized_gradient_linearIndependent [Algebra.FiniteType K R]
    {L : Type*} [Field L] [Algebra K L]
    (b : Module.Basis τ R Ω[R⁄K]) (v : Matrix κ ι R)
    (u : Matrix ι κ R) (hvu : v*u=1)
    (χ : R →ₐ[K] L) (a : ι → L)
    (ha : MvPolynomial.aeval a (criticalAvoidancePolynomial b v u hvu)≠0)
    (hz : ∀ j, ∑ i, a i*χ (v j i)=0) :
    LinearIndependent L (fun j t => ∑ i, a i*χ (b.repr (D K R (v j i)) t)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j₀
  by_contra hcn
  let c' : κ → L := fun j => (c j₀)⁻¹*c j
  have hc' : c' j₀=1 := inv_mul_cancel₀ hcn
  have hg : ∀ t, ∑ j, c' j*(∑ i, a i*χ (b.repr (D K R (v j i)) t))=0 := by
    intro t
    have ht := congrFun hc t
    simp only [Finset.sum_apply,Pi.smul_apply,Pi.zero_apply,smul_eq_mul] at ht
    simpa only [c',mul_assoc,← Finset.mul_sum,ht,mul_zero]
  let p := Classical.choose (universal_critical_parameter_polynomial b v u hvu j₀)
  have hp := (Classical.choose_spec
    (universal_critical_parameter_polynomial b v u hvu j₀)).2
  have hpzero : MvPolynomial.aeval a p=0 :=
    critical_specialization_polynomial_zero b v j₀ p hp χ a c' hc' hz hg
  apply ha
  rw [criticalAvoidancePolynomial,map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ j₀) hpzero

end Universal

end PaperVerification.GenericSectionDifferentials
