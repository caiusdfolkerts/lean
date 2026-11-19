module

public import PaperVerification.SegreCechMonomials
public import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# Exactness of the full finite Laurent-coefficient Čech complex

The coefficient decomposition includes every Laurent exponent of the given
integer total degree and has finite support, exactly as for localized
polynomial sections. The homotopy chooses a nonnegative coordinate separately
for each exponent; finite support is preserved. The conclusions are literal
kernel/image assertions for the alternating tuple differential, without a
sheaf-cohomology assumption or a restriction to finitely many exponents.
-/

set_option autoImplicit false

@[expose] public section

namespace PaperVerification.Segre.CechMonomials

open scoped BigOperators

variable {I K : Type*} [Fintype I] [CommRing K]

section IndexedMaps

variable {A M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
  [Module K M] [Module K N]

/-- A finite-support map whose linear coefficient map may depend on the index. -/
noncomputable def mapAtIndex (L : A → M →ₗ[K] N) : (A →₀ M) →ₗ[K] (A →₀ N) where
  toFun f := Finsupp.onFinset f.support (fun a => L a (f a)) (by
    intro a ha
    by_contra hn
    have hz : f a=0 := Finsupp.notMem_support_iff.mp hn
    exact ha (by rw [hz,map_zero]))
  map_add' f g := by
    ext a : 1
    exact (L a).map_add _ _
  map_smul' c f := by
    ext a : 1
    exact (L a).map_smul _ _

@[simp] theorem mapAtIndex_apply (L : A → M →ₗ[K] N) (f : A →₀ M) (a : A) :
    mapAtIndex L f a=L a (f a) := rfl

end IndexedMaps

/-- Every integer exponent vector of precisely the prescribed total degree. -/
abbrev DegreeExponent (I : Type*) [Fintype I] (t : ℤ) :=
  {a : I → ℤ // ∑ i, a i=t}

/-- Finitely many Laurent monomials, each with a tuple coefficient. -/
abbrev FiniteCochain (I K : Type*) [Fintype I] [CommRing K] (t : ℤ) (q : ℕ) :=
  DegreeExponent I t →₀ RawCochain I K q

/-- The exact denominator support condition, imposed on every coefficient. -/
def laurentCochains (t : ℤ) (q : ℕ) : Submodule K (FiniteCochain I K t q) where
  carrier := {f | ∀ a, f a ∈ supportedCochains (negativeSupport a.val) q}
  zero_mem' := by
    intro a
    exact (supportedCochains (K := K) (negativeSupport a.val) q).zero_mem
  add_mem' := by
    intro f g hf hg a
    change f a + g a ∈ supportedCochains (K := K) (negativeSupport a.val) q
    exact (supportedCochains (K := K) (negativeSupport a.val) q).add_mem (hf a) (hg a)
  smul_mem' := by
    intro c f hf a
    change c • f a ∈ supportedCochains (K := K) (negativeSupport a.val) q
    exact (supportedCochains (K := K) (negativeSupport a.val) q).smul_mem c (hf a)

noncomputable def laurentDifferential (t : ℤ) (q : ℕ) :
    FiniteCochain I K t q →ₗ[K] FiniteCochain I K t (q+1) :=
  mapAtIndex (fun _ => differential q)

@[simp] theorem laurentDifferential_apply (t : ℤ) (q : ℕ)
    (f : FiniteCochain I K t q) (a : DegreeExponent I t) :
    laurentDifferential (I := I) (K := K) t q f a=differential q (f a) := rfl

theorem laurentDifferential_mem {t : ℤ} {q : ℕ} {f : FiniteCochain I K t q}
    (hf : f ∈ laurentCochains (I := I) (K := K) t q) : laurentDifferential (I := I) (K := K) t q f ∈ laurentCochains (I := I) (K := K) t (q+1) :=
  fun a => differential_mem_supported (hf a)

theorem laurentDifferential_squared (t : ℤ) (q : ℕ) (f : FiniteCochain I K t q) :
    laurentDifferential (I := I) (K := K) t (q+1) (laurentDifferential (I := I) (K := K) t q f)=0 := by
  ext a : 1
  exact differential_squared q (f a)

/-- The insertion map for one exponent; it is zero if all exponents are negative. -/
noncomputable def coefficientContraction (a : I → ℤ) (q : ℕ) :
    RawCochain I K (q+1) →ₗ[K] RawCochain I K q := by
  classical
  exact if h : ∃ i, 0≤a i then contraction (Classical.choose h) q else 0

theorem coefficientContraction_mem (a : I → ℤ) (q : ℕ)
    (f : RawCochain I K (q+1)) (hf : f ∈ supportedCochains (negativeSupport a) (q+1)) :
    coefficientContraction a q f ∈ supportedCochains (negativeSupport a) q := by
  classical
  unfold coefficientContraction
  split_ifs with h
  · apply contraction_mem_supported _ _ hf
    exact not_lt_of_ge (Classical.choose_spec h)
  · exact (supportedCochains _ _).zero_mem

noncomputable def laurentContraction (t : ℤ) (q : ℕ) :
    FiniteCochain I K t (q+1) →ₗ[K] FiniteCochain I K t q :=
  mapAtIndex (fun a => coefficientContraction a.val q)

@[simp] theorem laurentContraction_apply (t : ℤ) (q : ℕ)
    (f : FiniteCochain I K t (q+1)) (a : DegreeExponent I t) :
    laurentContraction (I := I) (K := K) t q f a=coefficientContraction a.val q (f a) := rfl

theorem laurentContraction_mem {t : ℤ} {q : ℕ} {f : FiniteCochain I K t (q+1)}
    (hf : f ∈ laurentCochains (I := I) (K := K) t (q+1)) : laurentContraction (I := I) (K := K) t q f ∈ laurentCochains (I := I) (K := K) t q :=
  fun a => coefficientContraction_mem a.val q (f a) (hf a)

theorem negativeSupport_eq_univ_of_no_nonnegative (a : I → ℤ)
    (ha : ¬ ∃ i, 0≤a i) : negativeSupport a=Set.univ := by
  ext i
  simp only [negativeSupport,Set.mem_setOf_eq,Set.mem_univ,iff_true]
  exact lt_of_not_ge (fun hi => ha ⟨i,hi⟩)

/-- Intermediate projective degrees: every cocycle is an actual finite Laurent boundary. -/
theorem laurent_exact_below_dimension (t : ℤ) (q : ℕ) (hq : q+1<Fintype.card I)
    (f : FiniteCochain I K t (q+1)) (hf : f ∈ laurentCochains (I := I) (K := K) t (q+1))
    (hc : laurentDifferential (I := I) (K := K) t (q+1) f=0) :
    ∃ g : FiniteCochain I K t q, g ∈ laurentCochains (I := I) (K := K) t q ∧
      laurentDifferential (I := I) (K := K) t q g=f := by
  classical
  refine ⟨laurentContraction (I := I) (K := K) t q f,laurentContraction_mem hf,?_⟩
  ext a : 1
  change differential q (coefficientContraction a.val q (f a))=f a
  have hca : differential (q+1) (f a)=0 := congrArg (fun z => z a) hc
  unfold coefficientContraction
  split_ifs with h
  · have hi := contraction_identity (Classical.choose h) q (f a)
    simpa only [hca,map_zero,zero_add] using hi
  · have hz : f a=0 := by
      apply supported_univ_eq_zero (q+1) hq
      simpa only [negativeSupport_eq_univ_of_no_nonnegative a.val h] using hf a
    rw [LinearMap.zero_apply,map_zero,hz]

/-- If the twist is at least `-N` on `P^N`, no all-negative monomial occurs;
the augmented tuple complex is therefore exact in every degree. -/
theorem laurent_exact_of_twist (t : ℤ) (ht : -(Fintype.card I : ℤ)<t) (q : ℕ)
    (f : FiniteCochain I K t (q+1)) (hf : f ∈ laurentCochains (I := I) (K := K) t (q+1))
    (hc : laurentDifferential (I := I) (K := K) t (q+1) f=0) :
    ∃ g : FiniteCochain I K t q, g ∈ laurentCochains (I := I) (K := K) t q ∧
      laurentDifferential (I := I) (K := K) t q g=f := by
  classical
  refine ⟨laurentContraction (I := I) (K := K) t q f,laurentContraction_mem hf,?_⟩
  ext a : 1
  have ha : ∃ i, 0≤a.val i := exists_nonnegative_of_total_gt_neg_card a.val (by rwa [a.property])
  change differential q (coefficientContraction a.val q (f a))=f a
  rw [coefficientContraction,dif_pos ha]
  have hca : differential (q+1) (f a)=0 := congrArg (fun z => z a) hc
  have hi := contraction_identity (Classical.choose ha) q (f a)
  simpa only [hca,map_zero,zero_add] using hi

/-- There are no global sections in a negative degree when projective dimension is positive. -/
theorem laurent_global_cocycle_eq_zero (hI : 1<Fintype.card I) (t : ℤ) (ht : t<0)
    (f : FiniteCochain I K t 1) (hf : f ∈ laurentCochains (I := I) (K := K) t 1)
    (hc : laurentDifferential (I := I) (K := K) t 1 f=0) : f=0 := by
  classical
  ext a : 1
  change f a=0
  have hca : differential 1 (f a)=0 := congrArg (fun z => z a) hc
  by_cases ha : ∃ i, 0≤a.val i
  · obtain ⟨i,hi⟩ := ha
    apply global_cocycle_eq_zero
      (negativeSupport_nonempty_of_total_neg a.val (by rwa [a.property])) i
      (not_lt_of_ge hi) (f a) (hf a) hca
  · apply supported_univ_eq_zero 1 hI
    simpa only [negativeSupport_eq_univ_of_no_nonnegative a.val ha] using hf a

end PaperVerification.Segre.CechMonomials
