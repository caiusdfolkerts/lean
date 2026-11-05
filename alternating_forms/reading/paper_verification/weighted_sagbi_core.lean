module

public import PaperVerification.AlternatingFormsWeightAlgebraic
public import PaperVerification.WeightedInitialFiber
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# An exact initial-kernel criterion from actual leading monomials

The criterion uses a spanning family in the literal polynomial image. Its
distinct greatest monomials force every finite normal form to respect the
filtration. The resulting equality is an equality of the full conventional
initial ideal and the actual monomial-evaluation kernel; no flatness, Hilbert
function, or equality of dimensions is assumed.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.WeightedSagbi

open MvPolynomial
open scoped BigOperators
open AlternatingForms WeightedInitialFiber

variable {K σ τ C : Type*} [Field K]

theorem natCast_weight (w : τ → ℕ) (a : τ →₀ ℕ) :
    (Finsupp.weight w a : ℤ)=Finsupp.weight (fun i => (w i : ℤ)) a := by
  simp only [Finsupp.weight_apply,Finsupp.sum,nsmul_eq_mul,Nat.cast_sum,Nat.cast_mul,Nat.cast_id]

theorem weightBound_of_weightMonic (w : τ → ℕ) (p : MvPolynomial τ K)
    (a : τ →₀ ℕ) (hp : IsWeightMonic (fun i => (w i : ℤ)) p a) :
    WeightBound w (Finsupp.weight w a) p := by
  intro b hb
  have h := hp.weight_le hb
  rw [←natCast_weight,←natCast_weight] at h
  exact_mod_cast h

theorem component_of_weightMonic (w : τ → ℕ) (p : MvPolynomial τ K)
    (a : τ →₀ ℕ) (hp : IsWeightMonic (fun i => (w i : ℤ)) p a) :
    weightedHomogeneousComponent w (Finsupp.weight w a) p=monomial a 1 := by
  classical
  ext b
  rw [coeff_weightedHomogeneousComponent,coeff_monomial]
  by_cases hba : b=a
  · subst b
    simp only [hp.1,ite_true]
  · rw [if_neg (Ne.symm hba)]
    by_cases hw : Finsupp.weight w b=Finsupp.weight w a
    · rw [if_pos hw]
      apply hp.2 b hba
      rw [←natCast_weight,←natCast_weight,hw]
    · rw [if_neg hw]

theorem weightBound_smul (w : σ → ℕ) (d : ℕ) (a : K) (p : MvPolynomial σ K)
    (hp : WeightBound w d p) : WeightBound w d (a • p) := by
  intro b hb
  apply hp b
  intro h
  exact hb (by simp only [coeff_smul,h,smul_zero])

theorem weightBound_sub (w : σ → ℕ) (d : ℕ) (p q : MvPolynomial σ K)
    (hp : WeightBound w d p) (hq : WeightBound w d q) : WeightBound w d (p-q) := by
  simpa only [neg_one_smul,sub_eq_add_neg] using
    weightBound_add w d hp (weightBound_smul w d (-1 : K) q hq)

/-- In a finite expansion by distinct leading monomials, vanishing of the
top component forces every nonzero coefficient strictly below that degree. -/
theorem expansion_degree_lt (u : τ → ℕ) (v : C → MvPolynomial τ K)
    (a : C → τ →₀ ℕ) (degree : C → ℕ)
    (ha : Function.Injective a)
    (hv : ∀ c,IsWeightMonic (fun i => (u i : ℤ)) (v c) (a c))
    (hw : ∀ c,Finsupp.weight u (a c)=degree c)
    (coeff : C →₀ K) (d : ℕ)
    (hbound : WeightBound u d (coeff.sum fun c z => z • v c))
    (htop : weightedHomogeneousComponent u d (coeff.sum fun c z => z • v c)=0) :
    ∀ c,coeff c≠0 → degree c<d := by
  classical
  intro c hc
  have hS : coeff.support.Nonempty := ⟨c,Finsupp.mem_support_iff.mpr hc⟩
  obtain ⟨j,hj,hmax⟩ := coeff.support.exists_max_image degree hS
  have hcj : coeff j≠0 := Finsupp.mem_support_iff.mp hj
  have hlead : (coeff.sum fun c z => z • v c).coeff (a j)=coeff j := by
    simp only [Finsupp.sum,coeff_sum]
    rw [Finset.sum_eq_single j]
    · rw [coeff_smul,(hv j).1,smul_eq_mul,mul_one]
    · intro i hi hij
      rw [coeff_smul,(hv i).2 (a j) (fun he => hij (ha he.symm)),smul_zero]
      rw [←natCast_weight,←natCast_weight,hw,hw]
      exact_mod_cast hmax i hi
    · intro h
      exact (h hj).elim
  have hle : degree j≤d := by
    rw [←hw j]
    exact hbound (a j) (by rwa [hlead])
  have hne : degree j≠d := by
    intro he
    have h := congrArg (fun p : MvPolynomial τ K => p.coeff (a j)) htop
    rw [coeff_weightedHomogeneousComponent,hw,he,if_pos rfl,hlead] at h
    exact hcj (by simpa using h)
  exact (hmax c (Finsupp.mem_support_iff.mpr hc)).trans_lt (lt_of_le_of_ne hle hne)

section ExactKernel

variable (w : σ → ℕ) (u : τ → ℕ)
  (f f₀ : MvPolynomial σ K →ₐ[K] MvPolynomial τ K)
  (v : C → MvPolynomial σ K) (degree : C → ℕ) (a : C → τ →₀ ℕ)
  (ha : Function.Injective a)
  (hv : ∀ c,(v c).IsWeightedHomogeneous w (degree c))
  (hlead : ∀ c,IsWeightMonic (fun i => (u i : ℤ)) (f (v c)) (a c))
  (hw : ∀ c,Finsupp.weight u (a c)=degree c)
  (hspan : ∀ p,f p∈Submodule.span K (Set.range (fun c => f (v c))))
  (hbound : ∀ p d,WeightBound w d p → WeightBound u d (f p))
  (htop : ∀ p d,WeightBound w d p →
    weightedHomogeneousComponent u d (f p)=f₀ (weightedHomogeneousComponent w d p))
  (hgraded : ∀ p d,weightedHomogeneousComponent u d (f₀ p)=
    f₀ (weightedHomogeneousComponent w d p))

include ha hv hlead hw hspan hbound htop hgraded

theorem homogeneous_kernel_mem_initial (p : MvPolynomial σ K) (d : ℕ)
    (hp : p.IsWeightedHomogeneous w d) (hp₀ : f₀ p=0) :
    p∈initialIdeal (RingHom.ker f.toRingHom) w := by
  classical
  have hbp : WeightBound w d p := fun b hb => (hp hb).le
  have hfp : weightedHomogeneousComponent u d (f p)=0 := by
    rw [htop p d hbp,weightedHomogeneousComponent_eq_self hp,hp₀]
  obtain ⟨coeff,hcoeff⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (hspan p)
  have hsum : (coeff.sum fun c z => z • f (v c))=f p := by
    simpa only [Finsupp.linearCombination_apply] using hcoeff
  have hdeg : ∀ c,coeff c≠0 → degree c<d :=
    expansion_degree_lt u (fun c => f (v c)) a degree ha hlead hw coeff d
      (by rw [hsum]; exact hbound p d hbp) (by rw [hsum]; exact hfp)
  let q : MvPolynomial σ K := coeff.sum fun c z => z • v c
  have hfq : f q=f p := by
    simpa only [q,Finsupp.sum,map_sum,map_smul] using hsum
  have hbq : WeightBound w d q := by
    apply weightBound_sum
    intro c hc
    apply weightBound_smul
    intro b hb
    exact (hv c hb).le.trans (hdeg c (Finsupp.mem_support_iff.mp hc)).le
  have htq : weightedHomogeneousComponent w d q=0 := by
    simp only [q,Finsupp.sum,map_sum,map_smul]
    apply Finset.sum_eq_zero
    intro c hc
    rw [weightedHomogeneousComponent_of_mem (hv c),if_neg,smul_zero]
    exact (hdeg c (Finsupp.mem_support_iff.mp hc)).ne'
  have hr : p-q∈RingHom.ker f.toRingHom := by
    change f (p-q)=0
    rw [map_sub,hfq,sub_self]
  have h := component_mem_initialIdeal (RingHom.ker f.toRingHom) w (p-q) hr d
    (weightBound_sub w d p q hbp hbq)
  rwa [map_sub,weightedHomogeneousComponent_eq_self hp,htq,sub_zero] at h

/-- The entire initial ideal, with no restriction on polynomial degree or
standard-family cardinality, is the literal monomial-map kernel. -/
theorem initial_kernel_eq :
    initialIdeal (RingHom.ker f.toRingHom) w=RingHom.ker f₀.toRingHom := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨p,hp,rfl⟩
    change f₀ (weightedHomogeneousComponent w (weightedTotalDegree w p) p)=0
    rw [←htop p _ (weightBound_total w p)]
    change weightedHomogeneousComponent u _ (f p)=0
    rw [show f p=0 from hp,map_zero]
  · intro p hp
    rw [←sum_components_of_bound w p (weightedTotalDegree w p) (weightBound_total w p)]
    apply Ideal.sum_mem
    intro d hd
    apply homogeneous_kernel_mem_initial w u f f₀ v degree a ha hv hlead hw hspan
      hbound htop hgraded _ d (weightedHomogeneousComponent_isWeightedHomogeneous d p)
    rw [←hgraded p d,show f₀ p=0 from hp,map_zero]

end ExactKernel
end PaperVerification.WeightedSagbi
