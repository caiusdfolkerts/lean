module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Tactic.FinCases
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dual.Basis
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let opts ← getOptions
  if env.header.trustLevel != 0 then
    throwError "Header-cache environment has nonzero kernel trust level"
  if Lean.debug.skipKernelTC.get opts then
    throwError "Header-cache environment disabled kernel type checking"
  if Lean.Elab.inServer.get opts then
    throwError "Header-cache environment unexpectedly uses server mode"
  logInfo "HEADER_CACHE_CHECKING_OPTIONS_VERIFIED"

section ComponentSource_0
/- Original module: PaperVerification.SegreCechMonomials -/


/-!
# The Laurent-monomial contraction in the projective Čech complex

A Laurent monomial occurs on an intersection of coordinate charts exactly
when all its negative exponents belong to the tuple of inverted coordinates.
The usual alternating tuple differential therefore preserves this support
condition. Insertion of a coordinate with nonnegative exponent is an explicit
contracting homotopy. If every exponent is negative, all terms below the
number of coordinates vanish literally.

These are statements about the actual alternating tuple complex, including
its support condition. The comparison with sections of twisting sheaves is
a separate obligation; this file does not call this complex sheaf cohomology.
-/

set_option autoImplicit false

@[expose] public section

namespace PaperVerification.Segre.CechMonomials

open scoped BigOperators

variable {I K : Type*} [CommRing K]

/-- Tuple length is used, so length zero is the augmentation term. -/
abbrev RawCochain (I K : Type*) (q : ℕ) := (Fin q → I) → K

/-- The literal alternating deletion differential. -/
noncomputable def differential (q : ℕ) : RawCochain I K q →ₗ[K] RawCochain I K (q+1) where
  toFun f a := ∑ j : Fin (q+1), (-1 : K) ^ j.val * f (a ∘ j.succAbove)
  map_add' f g := by
    funext a
    simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' c f := by
    funext a
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

@[simp] theorem differential_apply (q : ℕ) (f : RawCochain I K q)
    (a : Fin (q+1) → I) :
    differential q f a=∑ j : Fin (q+1), (-1 : K)^j.val*f (a ∘ j.succAbove) := rfl

private theorem deletion_sign_cancel (q : ℕ) (i : Fin (q+2)) (j : Fin (q+1)) :
    (-1 : K)^i.val * (-1 : K)^j.val +
      (-1 : K)^(i.succAbove j).val * (-1 : K)^(j.predAbove i).val = 0 := by
  by_cases h : j.castSucc < i
  · rw [Fin.succAbove_of_castSucc_lt _ _ h,Fin.predAbove_of_castSucc_lt _ _ h]
    simp only [Fin.val_castSucc,Fin.val_pred]
    have hp : i.val-1+1=i.val := by have hh : j.val < i.val := h; omega
    conv_lhs => lhs; lhs; rw [← hp,pow_succ]
    ring
  · have h' : i ≤ j.castSucc := le_of_not_gt h
    rw [Fin.succAbove_of_le_castSucc _ _ h',Fin.predAbove_of_le_castSucc _ _ h']
    simp only [Fin.val_succ,Fin.coe_castPred,pow_succ]
    ring

/-- The literal alternating deletion differential squares to zero. -/
theorem differential_squared (q : ℕ) (f : RawCochain I K q) :
    differential (q+1) (differential q f)=0 := by
  classical
  funext a
  simp only [differential_apply,Finset.mul_sum,Pi.zero_apply]
  rw [← Finset.sum_product',Finset.univ_product_univ]
  refine Finset.sum_involution
    (fun p _ => (p.1.succAbove p.2,p.2.predAbove p.1)) ?_ ?_ (fun _ _ => Finset.mem_univ _) ?_
  · rintro ⟨i,j⟩ _
    have he : (a ∘ (i.succAbove j).succAbove) ∘ (j.predAbove i).succAbove =
        (a ∘ i.succAbove) ∘ j.succAbove := by
      funext k
      simp only [Function.comp_apply,Fin.succAbove_succAbove_succAbove_predAbove]
    change (-1 : K)^i.val * ((-1 : K)^j.val * f ((a ∘ i.succAbove) ∘ j.succAbove)) +
      (-1 : K)^(i.succAbove j).val * ((-1 : K)^(j.predAbove i).val *
        f ((a ∘ (i.succAbove j).succAbove) ∘ (j.predAbove i).succAbove)) = 0
    rw [he,← mul_assoc,← mul_assoc,← add_mul,deletion_sign_cancel,zero_mul]
  · rintro ⟨i,j⟩ _ _ he
    exact Fin.succAbove_ne i j (congrArg Prod.fst he)
  · rintro ⟨i,j⟩ _
    simp only [Fin.succAbove_succAbove_predAbove,Fin.predAbove_predAbove_succAbove]

/-- Insertion of one coordinate is the Čech homotopy. -/
def contraction (v : I) (q : ℕ) : RawCochain I K (q+1) →ₗ[K] RawCochain I K q where
  toFun f a := f (Fin.cons v a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem contraction_apply (v : I) (q : ℕ) (f : RawCochain I K (q+1))
    (a : Fin q → I) : contraction v q f a=f (Fin.cons v a) := rfl

/-- The contracting identity, over every commutative ring and in every degree. -/
theorem contraction_identity (v : I) (q : ℕ) (f : RawCochain I K (q+1)) :
    contraction v (q+1) (differential (q+1) f) +
      differential q (contraction v q f) = f := by
  funext a
  change (∑ j : Fin (q+2), (-1 : K)^j.val*f (Fin.cons v a ∘ j.succAbove)) +
    (∑ j : Fin (q+1), (-1 : K)^j.val*f (Fin.cons v (a ∘ j.succAbove))) = f a
  rw [Fin.sum_univ_succ]
  have hz : Fin.cons v a ∘ (0 : Fin (q+2)).succAbove = a := by
    funext j
    simp only [Function.comp_apply,Fin.zero_succAbove,Fin.cons_succ]
  rw [hz]
  simp only [Fin.val_zero,pow_zero,one_mul,Fin.val_succ,pow_succ,
    Fin.cons_comp_succ_succAbove]
  change f a + (∑ j : Fin (q+1), ((-1 : K)^j.val*(-1))*
    f (Fin.cons v (a ∘ j.succAbove))) +
      (∑ j : Fin (q+1), (-1 : K)^j.val*f (Fin.cons v (a ∘ j.succAbove))) = f a
  simp only [mul_neg_one,neg_mul,Finset.sum_neg_distrib]
  rw [add_assoc, neg_add_cancel, add_zero]

/-- Coefficients allowed only on tuples containing the negative support. -/
def supportedCochains (S : Set I) (q : ℕ) : Submodule K (RawCochain I K q) where
  carrier := {f | ∀ a, ¬ S ⊆ Set.range a → f a=0}
  zero_mem' := by intro a _; rfl
  add_mem' hf hg := by intro a ha; simp only [Pi.add_apply,hf a ha,hg a ha,add_zero]
  smul_mem' c f hf := by intro a ha; simp only [Pi.smul_apply,hf a ha,smul_zero]

theorem differential_mem_supported {S : Set I} {q : ℕ} {f : RawCochain I K q}
    (hf : f ∈ supportedCochains S q) :
    differential q f ∈ supportedCochains S (q+1) := by
  intro a ha
  rw [differential_apply]
  apply Finset.sum_eq_zero
  intro j _
  rw [hf (a ∘ j.succAbove) (by
    intro h
    apply ha
    intro x hx
    obtain ⟨k,hk⟩ := h hx
    exact ⟨j.succAbove k,hk⟩),mul_zero]

theorem contraction_mem_supported {S : Set I} (v : I) (hv : v ∉ S)
    {q : ℕ} {f : RawCochain I K (q+1)} (hf : f ∈ supportedCochains S (q+1)) :
    contraction v q f ∈ supportedCochains S q := by
  intro a ha
  apply hf
  intro h
  apply ha
  intro x hx
  obtain ⟨j,hj⟩ := h hx
  cases j using Fin.cases with
  | zero =>
    have he : v=x := hj
    exact False.elim (hv (he.symm ▸ hx))
  | succ k => exact ⟨k,hj⟩

/-- Every cocycle with proper negative support is a boundary in the augmented complex. -/
theorem exact_supported (S : Set I) (v : I) (hv : v ∉ S) (q : ℕ)
    (f : RawCochain I K (q+1)) (hf : f ∈ supportedCochains S (q+1))
    (hc : differential (q+1) f=0) :
    ∃ g : RawCochain I K q, g ∈ supportedCochains S q ∧ differential q g=f := by
  refine ⟨contraction v q f,contraction_mem_supported v hv hf,?_⟩
  have h := contraction_identity v q f
  simpa only [hc,map_zero,zero_add] using h

/-- The augmentation coefficient is zero whenever at least one exponent is negative. -/
theorem supported_zero_length {S : Set I} (hS : S.Nonempty)
    (f : RawCochain I K 0) (hf : f ∈ supportedCochains S 0) : f=0 := by
  funext a
  apply hf
  intro h
  obtain ⟨x,hx⟩ := hS
  obtain ⟨j,_⟩ := h hx
  exact Fin.elim0 j

/-- A proper nonempty negative support contributes no global cocycles. -/
theorem global_cocycle_eq_zero {S : Set I} (hS : S.Nonempty)
    (v : I) (hv : v ∉ S) (f : RawCochain I K 1)
    (hf : f ∈ supportedCochains S 1) (hc : differential 1 f=0) : f=0 := by
  obtain ⟨g,hg,hgf⟩ := exact_supported S v hv 0 f hf hc
  rw [supported_zero_length hS g hg,map_zero] at hgf
  exact hgf.symm

/-- A tuple too short to contain every coordinate supports no all-negative monomial. -/
theorem supported_univ_eq_zero [Fintype I] (q : ℕ) (hq : q<Fintype.card I)
    (f : RawCochain I K q) (hf : f ∈ supportedCochains (Set.univ : Set I) q) : f=0 := by
  funext a
  apply hf
  intro h
  have hs : Function.Surjective a := fun i => h (Set.mem_univ i)
  have hc := Fintype.card_le_of_surjective a hs
  simp only [Fintype.card_fin] at hc
  omega

/-- The actual Laurent exponent of a monomial; the total degree is an integer. -/
def negativeSupport (a : I → ℤ) : Set I := {i | a i<0}

theorem negativeSupport_nonempty_of_total_neg [Fintype I] (a : I → ℤ)
    (ha : ∑ i, a i<0) : (negativeSupport a).Nonempty := by
  by_contra h
  have hi : ∀ i, 0≤a i := by
    intro i
    by_contra hn
    exact h ⟨i,by exact lt_of_not_ge hn⟩
  exact (not_lt_of_ge (Finset.sum_nonneg (fun i _ => hi i))) ha

/-- All-negative exponent vectors have total degree at most minus the number of variables. -/
theorem total_le_neg_card_of_all_negative [Fintype I] (a : I → ℤ)
    (ha : ∀ i, a i<0) : ∑ i, a i≤-(Fintype.card I : ℤ) := by
  calc
    ∑ i, a i ≤ ∑ _i : I, (-1 : ℤ) := Finset.sum_le_sum (fun i _ => by have := ha i; omega)
    _ = -(Fintype.card I : ℤ) := by simp

/-- Degree at least `-N` on `P^N` ensures a nonnegative exponent in every monomial. -/
theorem exists_nonnegative_of_total_gt_neg_card [Fintype I] (a : I → ℤ)
    (ha : -(Fintype.card I : ℤ)<∑ i, a i) : ∃ i, 0≤a i := by
  by_contra h
  have hi : ∀ i, a i<0 := by
    intro i
    exact lt_of_not_ge (fun hi => h ⟨i,hi⟩)
  exact (not_lt_of_ge (total_le_neg_card_of_all_negative a hi)) ha

end PaperVerification.Segre.CechMonomials
end
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.SegreCechMonomials"

section ComponentSource_1
/- Original module: PaperVerification.SegreCechVanishing -/


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
end
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.SegreCechVanishing"

section ComponentSource_2
/- Original module: PaperVerification.ProjectiveLineLaurentResidue -/


/-!
# The residue description of the projective-line Čech quotient

This file computes the full degree-one quotient of the Laurent tuple
complex. The residue is the coefficient on the ordered intersection
`(0, 1)` for precisely the exponent vectors with both coordinates negative.
All other coefficients are removed by the existing explicit contraction.
The inverse sends a residue to the alternating edge cocycle. The maps are
linear over an arbitrary commutative coefficient ring.

The comparison with actual twisting-sheaf cohomology is kept separate.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.ProjectiveLineLaurentResidue

open Segre.CechMonomials
open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- Evaluation of the first tuple differential. -/
theorem differential_one_apply (f : RawCochain (Fin 2) R 1)
    (a : Fin 2 → Fin 2) :
    differential 1 f a = f (fun _ ↦ a 1) - f (fun _ ↦ a 0) := by
  have h₀ : a ∘ (0 : Fin 2).succAbove = fun _ : Fin 1 ↦ a 1 := by
    funext i
    fin_cases i
    rfl
  have h₁ : a ∘ (1 : Fin 2).succAbove = fun _ : Fin 1 ↦ a 0 := by
    funext i
    fin_cases i
    rfl
  rw [differential_apply, Fin.sum_univ_two, h₀, h₁]
  simp [sub_eq_add_neg]

/-- A value at vertex `1`, with value zero at vertex `0`. -/
def vertex : R →ₗ[R] RawCochain (Fin 2) R 1 where
  toFun c a := if a 0 = 1 then c else 0
  map_add' c d := by
    funext a
    by_cases h : a 0 = 1 <;> simp [h]
  map_smul' c d := by
    funext a
    by_cases h : a 0 = 1 <;> simp [h]

/-- The alternating edge cocycle with coefficient `c` on `(0, 1)`. -/
def edge : R →ₗ[R] RawCochain (Fin 2) R 2 :=
  (differential 1).comp vertex

theorem edge_apply (c : R) (a : Fin 2 → Fin 2) :
    edge c a = (if a 1 = 1 then c else 0) - (if a 0 = 1 then c else 0) :=
  differential_one_apply (vertex c) a

@[simp] theorem edge_id (c : R) : edge c id = c := by
  simp [edge_apply]

theorem edge_cocycle (c : R) : differential 2 (edge c) = 0 :=
  differential_squared 1 (vertex c)

theorem edge_supported (c : R) :
    edge c ∈ supportedCochains (Set.univ : Set (Fin 2)) 2 := by
  intro a ha
  have he : a 0 = a 1 := by
    by_contra hn
    apply ha
    intro i _
    have h₀ := (a 0).isLt
    have h₁ := (a 1).isLt
    have hi := i.isLt
    have hne : (a 0).val ≠ (a 1).val := fun h ↦ hn (Fin.ext h)
    by_cases h : (a 0).val = i.val
    · exact ⟨0, Fin.ext h⟩
    · exact ⟨1, Fin.ext (by omega)⟩
  rw [edge_apply, he, sub_self]

/-- An all-negative supported cocycle is determined by its value on `(0, 1)`. -/
theorem supported_cocycle_eq_zero (f : RawCochain (Fin 2) R 2)
    (hf : f ∈ supportedCochains (Set.univ : Set (Fin 2)) 2)
    (hc : differential 2 f = 0) (hres : f id = 0) : f = 0 := by
  have h₀ : f (fun _ ↦ 0) = 0 := by
    apply hf
    intro h
    obtain ⟨i, hi⟩ := h (Set.mem_univ (1 : Fin 2))
    exact Fin.zero_ne_one hi
  have hh := contraction_identity (0 : Fin 2) 1 f
  rw [hc, map_zero, zero_add] at hh
  have hv : contraction (0 : Fin 2) 1 f = 0 := by
    funext a
    change f (Fin.cons (0 : Fin 2) a) = 0
    by_cases ha : a 0 = 0
    · have he : Fin.cons (0 : Fin 2) a = (fun _ ↦ (0 : Fin 2)) := by
        funext i
        fin_cases i <;> simp [ha]
      rw [he]
      exact h₀
    · have ha' : a 0 = 1 := Fin.eq_one_of_ne_zero _ ha
      have he : Fin.cons (0 : Fin 2) a = id := by
        funext i
        fin_cases i <;> simp [ha']
      rw [he]
      exact hres
  rw [hv, map_zero] at hh
  exact hh.symm

/-- Both negative exponents, with exactly the prescribed integer degree. -/
def negativeExponents (t : ℤ) : Set (DegreeExponent (Fin 2) t) :=
  {a | ∀ i, a.val i < 0}

/-- The Laurent support submodule carries its ordinary inherited additive group. -/
instance laurentCochains_addCommGroup (t : ℤ) (q : ℕ) :
    AddCommGroup (laurentCochains (I := Fin 2) (K := R) t q) := by
  letI : AddCommGroup (FiniteCochain (Fin 2) R t q) := inferInstance
  exact (laurentCochains (I := Fin 2) (K := R) t q).addCommGroup

/-- The full Laurent tuple differential, restricted to the denominator condition. -/
def tupleDifferential (t : ℤ) (q : ℕ) :
    laurentCochains (I := Fin 2) (K := R) t q →ₗ[R]
      laurentCochains (I := Fin 2) (K := R) t (q + 1) :=
  (laurentDifferential (I := Fin 2) (K := R) t q).restrict
    (fun _ h ↦ laurentDifferential_mem h)

@[simp] theorem tupleDifferential_val (t : ℤ) (q : ℕ)
    (f : laurentCochains (I := Fin 2) (K := R) t q) :
    (tupleDifferential t q f).val =
      laurentDifferential (I := Fin 2) (K := R) t q f.val := rfl

theorem tupleDifferential_squared (t : ℤ) (q : ℕ)
    (f : laurentCochains (I := Fin 2) (K := R) t q) :
    tupleDifferential t (q + 1) (tupleDifferential t q f) = 0 :=
  Subtype.ext (laurentDifferential_squared t q f.val)

/-- The actual kernel of the degree-one tuple differential. -/
abbrev Cycles (R : Type*) [CommRing R] (t : ℤ) :=
  LinearMap.ker (tupleDifferential (R := R) t 2)

/-- The cycle submodule has the inherited additive group used by its quotient. -/
instance cycles_addCommGroup (t : ℤ) : AddCommGroup (Cycles R t) :=
  (Cycles R t).addCommGroup

/-- The actual degree-zero boundaries, with their canonical inclusion into cycles. -/
def toCycles (t : ℤ) :
    laurentCochains (I := Fin 2) (K := R) t 1 →ₗ[R] Cycles R t :=
  (tupleDifferential t 1).codRestrict (Cycles R t)
    (fun f ↦ tupleDifferential_squared t 1 f)

/-- Retain the ordered-intersection coefficient on every all-negative monomial. -/
def residue (t : ℤ) : Cycles R t →ₗ[R] (negativeExponents t →₀ R) :=
  (Finsupp.lsubtypeDomain (negativeExponents t)).comp
    ((mapAtIndex (fun _ ↦ (LinearMap.proj id : RawCochain (Fin 2) R 2 →ₗ[R] R))).comp
      ((laurentCochains (I := Fin 2) (K := R) t 2).subtype.comp
        (Cycles R t).subtype))

@[simp] theorem residue_apply (t : ℤ) (f : Cycles R t) (a : negativeExponents t) :
    residue t f a = f.val.val a.val id := rfl

theorem residue_boundary (t : ℤ)
    (f : laurentCochains (I := Fin 2) (K := R) t 1) :
    residue t (toCycles t f) = 0 := by
  ext a
  change differential 1 (f.val a.val) id = 0
  have ha : negativeSupport a.val.val = Set.univ := by
    ext i
    simp [negativeSupport, a.property i]
  have hz : f.val a.val = 0 :=
    supported_univ_eq_zero 1 (by simp) _ (by simpa [ha] using f.property a.val)
  rw [hz, map_zero]
  rfl

/-- Zero residue is precisely the obstruction-free case of the Laurent contraction. -/
theorem exists_boundary_of_residue_zero (t : ℤ) (f : Cycles R t)
    (hres : residue t f = 0) : ∃ g, toCycles t g = f := by
  classical
  let g : laurentCochains (I := Fin 2) (K := R) t 1 :=
    ⟨laurentContraction (I := Fin 2) (K := R) t 1 f.val.val,
      laurentContraction_mem f.val.property⟩
  refine ⟨g, Subtype.ext (Subtype.ext ?_)⟩
  ext a : 1
  change differential 1 (coefficientContraction a.val 1 (f.val.val a)) = f.val.val a
  have hc : differential 2 (f.val.val a) = 0 := by
    have h := congrArg
      (fun z : laurentCochains (I := Fin 2) (K := R) t 3 ↦ z.val a) f.property
    exact h
  unfold coefficientContraction
  split_ifs with h
  · have hi := contraction_identity (Classical.choose h) 1 (f.val.val a)
    simpa only [hc, map_zero, zero_add] using hi
  · have ha : a ∈ negativeExponents t := fun i ↦
      lt_of_not_ge (fun hi ↦ h ⟨i, hi⟩)
    have hz : f.val.val a = 0 := by
      have hsupport : f.val.val a ∈ supportedCochains (Set.univ : Set (Fin 2)) 2 := by
        simpa only [negativeSupport_eq_univ_of_no_nonnegative a.val h] using f.val.property a
      exact supported_cocycle_eq_zero _ hsupport hc
        (congrArg (fun z ↦ z ⟨a, ha⟩) hres)
    rw [LinearMap.zero_apply, map_zero, hz]

theorem range_toCycles_eq_ker_residue (t : ℤ) :
    LinearMap.range (toCycles (R := R) t) = LinearMap.ker (residue t) := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact residue_boundary t g
  · exact exists_boundary_of_residue_zero t f

/-- Include an arbitrary finite family of all-negative monomials as alternating edge cocycles. -/
def residueLift (t : ℤ) (p : negativeExponents t →₀ R) : Cycles R t := by
  classical
  let v := (Finsupp.supportedEquivFinsupp (R := R) (negativeExponents t)).symm p
  let f : FiniteCochain (Fin 2) R t 2 := mapAtIndex (fun _ ↦ edge) v.val
  have hf : f ∈ laurentCochains (I := Fin 2) (K := R) t 2 := by
    intro a
    change edge (v.val a) ∈ supportedCochains (negativeSupport a.val) 2
    by_cases ha : a ∈ negativeExponents t
    · have hs : negativeSupport a.val = Set.univ := by
        ext i
        simp [negativeSupport, ha i]
      rw [hs]
      exact edge_supported _
    · have hz := (Finsupp.mem_supported' R _).mp v.property a ha
      rw [hz, map_zero]
      exact (supportedCochains _ _).zero_mem
  refine ⟨⟨f, hf⟩, ?_⟩
  apply Subtype.ext
  ext a : 1
  exact edge_cocycle (v.val a)

@[simp] theorem residue_residueLift (t : ℤ) (p : negativeExponents t →₀ R) :
    residue t (residueLift t p) = p := by
  classical
  ext a
  change edge (((Finsupp.supportedEquivFinsupp (R := R) (negativeExponents t)).symm p).val
    a.val) id = p a
  rw [edge_id]
  simp [Finsupp.supportedEquivFinsupp_symm_apply_coe, Finsupp.extendDomain_apply]

/-- The entire degree-one Laurent Čech quotient is the module of negative Laurent residues. -/
def homologyResidueEquiv (t : ℤ) :
    (Cycles R t ⧸ LinearMap.range (toCycles (R := R) t)) ≃ₗ[R]
      (negativeExponents t →₀ R) :=
  (Submodule.quotEquivOfEq _ _ (range_toCycles_eq_ker_residue (R := R) t)).trans
    ((residue (R := R) t).quotKerEquivOfSurjective
      (fun p ↦ ⟨residueLift t p, residue_residueLift t p⟩))

/-- The isomorphism is the literal residue of a representative cocycle. -/
@[simp] theorem homologyResidueEquiv_mk (t : ℤ) (f : Cycles R t) :
    homologyResidueEquiv (R := R) t (Submodule.Quotient.mk f) = residue t f := by
  simp [homologyResidueEquiv]

end PaperVerification.ProjectiveLineLaurentResidue
end
end
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.ProjectiveLineLaurentResidue"

section ComponentSource_3
/- Original module: TauCeti.RingTheory.MvPolynomial.RestrictSupport -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The monomial basis of polynomials with restricted support

Mathlib's `MvPolynomial.basisRestrictSupport R s` is the basis of `MvPolynomial.restrictSupport R s`
indexed by `s`. This file records its coordinates (the coefficients) and its basis vectors (the
monomials with coefficient `1`).
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R] {s : Set (σ →₀ ℕ)}

/-- The coordinates of a polynomial in `basisRestrictSupport` are its coefficients. -/
@[simp]
theorem basisRestrictSupport_repr_apply (p : restrictSupport R s) (c : s) :
    (basisRestrictSupport R s).repr p c = (p : MvPolynomial σ R).coeff c :=
  -- `basisRestrictSupport` is defined through `AddMonoidAlgebra.supportedEquivFinsupp`, which
  -- reads off coefficients.
  rfl

/-- The basis vectors of `basisRestrictSupport` are the monomials with coefficient `1`. -/
@[simp]
theorem basisRestrictSupport_apply_coe (c : s) :
    (basisRestrictSupport R s c : MvPolynomial σ R) = monomial (c : σ →₀ ℕ) 1 := by
  classical
  have hc : monomial (c : σ →₀ ℕ) (1 : R) ∈ restrictSupport R s := by simp
  suffices basisRestrictSupport R s c = ⟨_, hc⟩ from congrArg Subtype.val this
  refine (basisRestrictSupport R s).repr.injective (Finsupp.ext fun d ↦ ?_)
  simp [Finsupp.single_apply, coeff_monomial, Subtype.ext_iff]

end MvPolynomial
end
end ComponentSource_3

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: TauCeti.RingTheory.MvPolynomial.RestrictSupport"

section ComponentSource_4
/- Original module: TauCeti.RingTheory.MvPolynomial.Finrank -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Dimension of homogeneous polynomials

The monomial basis of a homogeneous component is indexed by exponent vectors of its degree.
For two variables this gives dimension `w + 1`, used for the scalar-matrix trace on binary forms.
Changing the coefficients along a ring homomorphism, `TauCeti.mapHomogeneousSubmodule`, is
semilinear and sends this basis to the monomial basis over the new ring.
-/

public section

namespace TauCeti

open MvPolynomial

/-- A homogeneous component in finitely many variables is a finite module. -/
instance homogeneousSubmodule_moduleFinite {σ R : Type*} [CommSemiring R] [Finite σ]
    (n : ℕ) : Module.Finite R (homogeneousSubmodule σ R n) :=
  Module.Finite.of_fg (homogeneousSubmodule_fg σ R n)

/-- A homogeneous component is a free module, with the monomials of its degree as basis. -/
instance homogeneousSubmodule_moduleFree {σ R : Type*} [CommSemiring R]
    (n : ℕ) : Module.Free R (homogeneousSubmodule σ R n) := by
  classical
  rw [homogeneousSubmodule_eq_finsupp_supported]
  exact Module.Free.of_basis (basisRestrictSupport R {d : σ →₀ ℕ | d.degree = n})

/-- The monomial basis of a homogeneous component, indexed by exponent vectors of its degree. -/
noncomputable def homogeneousMonomialBasis {σ R : Type*} [CommSemiring R] (n : ℕ) :
    Module.Basis {s : σ →₀ ℕ // s.degree = n} R (homogeneousSubmodule σ R n) :=
  (basisRestrictSupport R {s : σ →₀ ℕ | s.degree = n}).map
    (LinearEquiv.ofEq _ _ (homogeneousSubmodule_eq_finsupp_supported σ R n).symm)

/-- A homogeneous monomial basis vector is the corresponding monomial. -/
@[simp]
theorem coe_homogeneousMonomialBasis {σ R : Type*} [CommSemiring R] (n : ℕ)
    (s : {s : σ →₀ ℕ // s.degree = n}) :
    ((homogeneousMonomialBasis (R := R) n s : homogeneousSubmodule σ R n) :
      MvPolynomial σ R) = monomial s.1 1 := by
  simp only [homogeneousMonomialBasis, Module.Basis.map_apply]
  exact basisRestrictSupport_apply_coe (s := {d : σ →₀ ℕ | d.degree = n}) s

/-- The coordinate of a homogeneous polynomial in the monomial basis is its corresponding
coefficient. -/
@[simp]
theorem homogeneousMonomialBasis_repr_apply {σ R : Type*} [CommSemiring R] (n : ℕ)
    (p : homogeneousSubmodule σ R n) (s : {s : σ →₀ ℕ // s.degree = n}) :
    (homogeneousMonomialBasis n).repr p s = p.1.coeff s.1 := by
  rfl

/-- Mapping the coefficients of the homogeneous polynomials of degree `n` along a ring
homomorphism `f : R →+* S`, as an `f`-semilinear map. -/
noncomputable def mapHomogeneousSubmodule {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (n : ℕ) : homogeneousSubmodule σ R n →ₛₗ[f] homogeneousSubmodule σ S n where
  toFun p := ⟨map f p, p.2.map f⟩
  map_add' p q := Subtype.ext (map_add (map f) (p : MvPolynomial σ R) q)
  map_smul' a p := Subtype.ext <| by simp [smul_eq_C_mul]

@[simp]
theorem coe_mapHomogeneousSubmodule_apply {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) {n : ℕ} (p : homogeneousSubmodule σ R n) :
    (mapHomogeneousSubmodule f n p : MvPolynomial σ S) = map f p :=
  (rfl)

/-- Changing coefficients sends the monomial basis to the monomial basis. -/
@[simp]
theorem mapHomogeneousSubmodule_homogeneousMonomialBasis {σ R S : Type*} [CommSemiring R]
    [CommSemiring S] (f : R →+* S) (n : ℕ) (s : {s : σ →₀ ℕ // s.degree = n}) :
    mapHomogeneousSubmodule f n (homogeneousMonomialBasis n s) = homogeneousMonomialBasis n s :=
  Subtype.ext <| by simp

/-- Exponent vectors of degree `w` in two variables are determined by their value at `0`. -/
noncomputable def finsuppDegreeFinTwoEquiv (w : ℕ) :
    {s : Fin 2 →₀ ℕ // s.degree = w} ≃ Fin (w + 1) where
  toFun s := ⟨s.1 0, by
    have h := s.2
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at h
    omega⟩
  invFun j := ⟨Finsupp.single (0 : Fin 2) (j : ℕ) + Finsupp.single 1 (w - j), by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
    simp
    omega⟩
  left_inv s := by
    have h := s.2
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at h
    ext i
    fin_cases i
    · simp
    · simp; omega
  right_inv j := by ext; simp

/-- The equivalence sends an exponent vector of degree `w` to its value at `0`. -/
@[simp]
theorem coe_finsuppDegreeFinTwoEquiv_apply (w : ℕ) (s : {s : Fin 2 →₀ ℕ // s.degree = w}) :
    (finsuppDegreeFinTwoEquiv w s : ℕ) = s.1 0 :=
  (rfl)

@[simp]
theorem coe_finsuppDegreeFinTwoEquiv_symm (w : ℕ) (j : Fin (w + 1)) :
    ((finsuppDegreeFinTwoEquiv w).symm j).1 =
      Finsupp.single (0 : Fin 2) (j : ℕ) + Finsupp.single 1 (w - j) :=
  (rfl)

/-- The dimension of a homogeneous component is the number of exponent vectors of its degree. -/
theorem finrank_homogeneousSubmodule (σ R : Type*) [CommSemiring R]
    [StrongRankCondition R] (n : ℕ) :
    Module.finrank R (homogeneousSubmodule σ R n) =
      Nat.card (↥{d : σ →₀ ℕ | d.degree = n}) := by
  classical
  rw [homogeneousSubmodule_eq_finsupp_supported]
  exact Module.finrank_eq_nat_card_basis
    (basisRestrictSupport R {d : σ →₀ ℕ | d.degree = n})

/-- The dimension of a homogeneous component is a multichoose number. -/
@[simp]
theorem finrank_homogeneousSubmodule_eq_multichoose (σ R : Type*) [Fintype σ]
    [CommSemiring R] [StrongRankCondition R] (n : ℕ) :
    Module.finrank R (homogeneousSubmodule σ R n) = (Fintype.card σ).multichoose n := by
  classical
  rw [finrank_homogeneousSubmodule]
  let e : (↥{d : σ →₀ ℕ | d.degree = n}) ≃
      (Finset.univ.finsuppAntidiag n : Finset (σ →₀ ℕ)) :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun d => by
      simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum])
  calc
    Nat.card (↥{d : σ →₀ ℕ | d.degree = n}) =
        Nat.card (Finset.univ.finsuppAntidiag n : Finset (σ →₀ ℕ)) := Nat.card_congr e
    _ = (Fintype.card σ).multichoose n := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe,
        Finset.card_finsuppAntidiag_nat_eq_multichoose]
      simp

/-- The degree-`w` homogeneous polynomials in two variables have dimension `w + 1`. -/
theorem finrank_homogeneousSubmodule_fin_two (R : Type*) [CommSemiring R]
    [StrongRankCondition R] (w : ℕ) :
    Module.finrank R (homogeneousSubmodule (Fin 2) R w) = w + 1 := by
  rw [finrank_homogeneousSubmodule_eq_multichoose, Fintype.card_fin, Nat.multichoose_two]

end TauCeti
end
end ComponentSource_4

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: TauCeti.RingTheory.MvPolynomial.Finrank"

section ComponentSource_5
/- Original module: PaperVerification.ProjectiveLineNegativeResidueDuality -/


/-!
# Binary forms and the projective-line residue pairing

For `a ≥ 0`, the negative Laurent monomial `X₀^(-i-1) X₁^(i-a-1)`
pairs with the degree-`a` monomial `X₀^i X₁^(a-i)`. This identifies the
complete residue module with the linear dual of the homogeneous forms.
The construction is linear over every commutative coefficient ring.

This file fixes the two ordered coordinates. Equivariance under an arbitrary
change of frame, including the determinant factor, is a separate assertion.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.ProjectiveLineResidueDuality

open Segre.CechMonomials ProjectiveLineLaurentResidue
open scoped BigOperators

universe u

/-- A negative exponent pair of total degree `-a-2` is determined by `-e₀-1`. -/
def negativeExponentFinEquiv (a : ℕ) :
    negativeExponents (-(a : ℤ) - 2) ≃ Fin (a + 1) where
  toFun e := ⟨(-e.val.val 0 - 1).toNat, by
    have hs := e.val.property
    rw [Fin.sum_univ_two] at hs
    have h₀ := e.property 0
    have h₁ := e.property 1
    omega⟩
  invFun i := ⟨⟨(fun j ↦ if j = 0 then -(i.val : ℤ) - 1 else
      (i.val : ℤ) - (a : ℤ) - 1), by
      simp [Fin.sum_univ_two]
      ring⟩, by
    intro j
    have hi := i.isLt
    change (if j = 0 then -(i.val : ℤ) - 1 else (i.val : ℤ) - (a : ℤ) - 1) < 0
    split_ifs <;> omega⟩
  left_inv e := by
    have hs := e.val.property
    rw [Fin.sum_univ_two] at hs
    have h₀ := e.property 0
    have h₁ := e.property 1
    apply Subtype.ext
    apply Subtype.ext
    funext j
    fin_cases j <;> simp <;> omega
  right_inv i := by
    apply Fin.ext
    simp

/-- Pair negative Laurent exponents with the complementary binary monomial exponents. -/
def negativeExponentMonomialEquiv (a : ℕ) :
    negativeExponents (-(a : ℤ) - 2) ≃
      {s : Fin 2 →₀ ℕ // s.degree = a} :=
  (negativeExponentFinEquiv a).trans (TauCeti.finsuppDegreeFinTwoEquiv a).symm

theorem finite_binary_exponents (a : ℕ) :
    Finite {s : Fin 2 →₀ ℕ // s.degree = a} :=
  Finite.of_equiv (Fin (a + 1)) (TauCeti.finsuppDegreeFinTwoEquiv a).symm

/-- The monomial residue pairing is perfect over every commutative ring. -/
def residueDualEquiv (R : Type u) [CommRing R] (a : ℕ) :
    (negativeExponents (-(a : ℤ) - 2) →₀ R) ≃ₗ[R]
      Module.Dual R (MvPolynomial.homogeneousSubmodule (Fin 2) R a) := by
  letI := finite_binary_exponents a
  exact (Finsupp.domLCongr (negativeExponentMonomialEquiv a)).trans
    (TauCeti.homogeneousMonomialBasis (R := R) a).dualBasis.repr.symm

/-- The functional reads the complementary negative Laurent coefficient. -/
theorem residueDualEquiv_monomial (R : Type u) [CommRing R] (a : ℕ)
    (p : negativeExponents (-(a : ℤ) - 2) →₀ R)
    (s : {s : Fin 2 →₀ ℕ // s.degree = a}) :
    residueDualEquiv R a p (TauCeti.homogeneousMonomialBasis (R := R) a s) =
      p ((negativeExponentMonomialEquiv a).symm s) := by
  haveI := finite_binary_exponents a
  let b := TauCeti.homogeneousMonomialBasis (σ := Fin 2) (R := R) a
  let e := negativeExponentMonomialEquiv a
  calc
    residueDualEquiv R a p (b s) = b.dualBasis.repr (residueDualEquiv R a p) s :=
      (b.dualBasis_repr _ s).symm
    _ = (Finsupp.domLCongr e p) s := by
      change (b.dualBasis.repr (b.dualBasis.repr.symm (Finsupp.domLCongr e p))) s = _
      rw [LinearEquiv.apply_symm_apply]
    _ = p (e.symm s) := rfl

end PaperVerification.ProjectiveLineResidueDuality
end
end
end ComponentSource_5

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.ProjectiveLineNegativeResidueDuality"

section ComponentSource_6
/- Original module: PaperVerification.PerfectPairingCovariance -/


/-!
# Transporting a determinant factor through a perfect pairing

This elementary comparison records the exponent needed in relative
projective-line duality. A residue pairing of multiplier `δ⁻¹`, compared
with a degree-`d` binary pairing of multiplier `δ^d`, produces the multiplier
`δ^(-(d+1))`. The two pairings and the changes of frame remain explicit.
The geometric residue identity is a separate theorem, not an assumption
hidden in a definition of cohomology.
-/

@[expose] public section
noncomputable section

namespace PaperVerification.PerfectPairingCovariance

variable {R U V : Type*} [CommRing R]
  [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]

/-- Compare two actual perfect pairings with the same target dual. -/
def comparison (B : V ≃ₗ[R] Module.Dual R V)
    (C : U ≃ₗ[R] Module.Dual R V) : U ≃ₗ[R] V :=
  C.trans B.symm

/-- The two covariance laws determine the exact determinant exponent of the
comparison. The statement holds over every commutative coefficient ring. -/
theorem comparison_covariant
    (B : V ≃ₗ[R] Module.Dual R V) (C : U ≃ₗ[R] Module.Dual R V)
    (gV : V ≃ₗ[R] V) (gU : U →ₗ[R] U) (δ : Rˣ) (d : ℕ)
    (hB : ∀ x y, B (gV x) (gV y) = (δ : R)^d * B x y)
    (hC : ∀ x y, C (gU x) (gV y) = (↑(δ⁻¹) : R) * C x y)
    (x : U) :
    comparison B C (gU x) =
      (↑(δ⁻¹) : R)^(d+1) • gV (comparison B C x) := by
  apply B.injective
  apply LinearMap.ext
  intro y
  obtain ⟨z, rfl⟩ := gV.surjective y
  simp only [comparison, LinearEquiv.trans_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul, LinearEquiv.apply_symm_apply]
  rw [hC, hB, LinearEquiv.apply_symm_apply]
  have hscalar : (↑(δ⁻¹) : R)^(d+1) * (δ : R)^d = (↑(δ⁻¹) : R) := by
    rw [pow_succ', mul_assoc, ← mul_pow, Units.inv_mul, one_pow, mul_one]
  rw [← mul_assoc, hscalar]

end PaperVerification.PerfectPairingCovariance
end
end
end ComponentSource_6

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.PerfectPairingCovariance"


set_option pp.explicit false
set_option pp.proofs false
set_option pp.deepTerms false
set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let opts ← getOptions
  if true && env.header.trustLevel != 0 then
    throwError "The final environment has nonzero kernel trust level"
  if Lean.debug.skipKernelTC.get opts then
    throwError "The final environment disabled kernel type checking"
  if Lean.Elab.inServer.get opts then
    throwError "The final environment unexpectedly uses server mode"
  let required : Array (Name × String) := #[
    (`PaperVerification.ProjectiveLineLaurentResidue.differential_one_apply, "theorem"),
    (`PaperVerification.ProjectiveLineLaurentResidue.vertex, "definition"),
    (`PaperVerification.ProjectiveLineLaurentResidue.edge, "definition"),
    (`PaperVerification.ProjectiveLineLaurentResidue.edge_apply, "theorem"),
    (`PaperVerification.ProjectiveLineLaurentResidue.edge_id, "theorem"),
    (`PaperVerification.ProjectiveLineLaurentResidue.edge_cocycle, "theorem"),
    (`PaperVerification.ProjectiveLineLaurentResidue.edge_supported, "theorem"),
    (`PaperVerification.ProjectiveLineLaurentResidue.supported_cocycle_eq_zero, "theorem"),
    (`PaperVerification.ProjectiveLineLaurentResidue.negativeExponents, "definition"),
    (`PaperVerification.ProjectiveLineLaurentResidue.tupleDifferential, "definition"),
    (`PaperVerification.ProjectiveLineLaurentResidue.tupleDifferential_val, "theorem"),
    (`PaperVerification.ProjectiveLineLaurentResidue.tupleDifferential_squared, "theorem"),
    (`PaperVerification.ProjectiveLineLaurentResidue.Cycles, "definition"),
    (`PaperVerification.ProjectiveLineLaurentResidue.toCycles, "definition"),
    (`PaperVerification.ProjectiveLineLaurentResidue.residue, "definition"),
    (`PaperVerification.ProjectiveLineLaurentResidue.residue_apply, "theorem"),
    (`PaperVerification.ProjectiveLineLaurentResidue.residue_boundary, "theorem"),
    (`PaperVerification.ProjectiveLineLaurentResidue.exists_boundary_of_residue_zero, "theorem"),
    (`PaperVerification.ProjectiveLineLaurentResidue.range_toCycles_eq_ker_residue, "theorem"),
    (`PaperVerification.ProjectiveLineLaurentResidue.residueLift, "definition"),
    (`PaperVerification.ProjectiveLineLaurentResidue.residue_residueLift, "theorem"),
    (`PaperVerification.ProjectiveLineLaurentResidue.homologyResidueEquiv, "definition"),
    (`PaperVerification.ProjectiveLineLaurentResidue.homologyResidueEquiv_mk, "theorem"),
    (`MvPolynomial.basisRestrictSupport_repr_apply, "theorem"),
    (`MvPolynomial.basisRestrictSupport_apply_coe, "theorem"),
    (`TauCeti.homogeneousMonomialBasis, "definition"),
    (`TauCeti.coe_homogeneousMonomialBasis, "theorem"),
    (`TauCeti.homogeneousMonomialBasis_repr_apply, "theorem"),
    (`TauCeti.mapHomogeneousSubmodule, "definition"),
    (`TauCeti.coe_mapHomogeneousSubmodule_apply, "theorem"),
    (`TauCeti.mapHomogeneousSubmodule_homogeneousMonomialBasis, "theorem"),
    (`TauCeti.finsuppDegreeFinTwoEquiv, "definition"),
    (`TauCeti.coe_finsuppDegreeFinTwoEquiv_apply, "theorem"),
    (`TauCeti.coe_finsuppDegreeFinTwoEquiv_symm, "theorem"),
    (`TauCeti.finrank_homogeneousSubmodule, "theorem"),
    (`TauCeti.finrank_homogeneousSubmodule_eq_multichoose, "theorem"),
    (`TauCeti.finrank_homogeneousSubmodule_fin_two, "theorem"),
    (`PaperVerification.PerfectPairingCovariance.comparison, "definition"),
    (`PaperVerification.PerfectPairingCovariance.comparison_covariant, "theorem"),
    (`PaperVerification.ProjectiveLineResidueDuality.negativeExponentFinEquiv, "definition"),
    (`PaperVerification.ProjectiveLineResidueDuality.negativeExponentMonomialEquiv, "definition"),
    (`PaperVerification.ProjectiveLineResidueDuality.finite_binary_exponents, "theorem"),
    (`PaperVerification.ProjectiveLineResidueDuality.residueDualEquiv, "definition"),
    (`PaperVerification.ProjectiveLineResidueDuality.residueDualEquiv_monomial, "theorem"),
    (`PaperVerification.Segre.CechMonomials.RawCochain, "definition"),
    (`PaperVerification.Segre.CechMonomials.differential, "definition"),
    (`PaperVerification.Segre.CechMonomials.differential_apply, "theorem"),
    (`PaperVerification.Segre.CechMonomials.differential_squared, "theorem"),
    (`PaperVerification.Segre.CechMonomials.contraction, "definition"),
    (`PaperVerification.Segre.CechMonomials.contraction_apply, "theorem"),
    (`PaperVerification.Segre.CechMonomials.contraction_identity, "theorem"),
    (`PaperVerification.Segre.CechMonomials.supportedCochains, "definition"),
    (`PaperVerification.Segre.CechMonomials.differential_mem_supported, "theorem"),
    (`PaperVerification.Segre.CechMonomials.contraction_mem_supported, "theorem"),
    (`PaperVerification.Segre.CechMonomials.exact_supported, "theorem"),
    (`PaperVerification.Segre.CechMonomials.supported_zero_length, "theorem"),
    (`PaperVerification.Segre.CechMonomials.global_cocycle_eq_zero, "theorem"),
    (`PaperVerification.Segre.CechMonomials.supported_univ_eq_zero, "theorem"),
    (`PaperVerification.Segre.CechMonomials.negativeSupport, "definition"),
    (`PaperVerification.Segre.CechMonomials.negativeSupport_nonempty_of_total_neg, "theorem"),
    (`PaperVerification.Segre.CechMonomials.total_le_neg_card_of_all_negative, "theorem"),
    (`PaperVerification.Segre.CechMonomials.exists_nonnegative_of_total_gt_neg_card, "theorem"),
    (`PaperVerification.Segre.CechMonomials.mapAtIndex, "definition"),
    (`PaperVerification.Segre.CechMonomials.mapAtIndex_apply, "theorem"),
    (`PaperVerification.Segre.CechMonomials.DegreeExponent, "definition"),
    (`PaperVerification.Segre.CechMonomials.FiniteCochain, "definition"),
    (`PaperVerification.Segre.CechMonomials.laurentCochains, "definition"),
    (`PaperVerification.Segre.CechMonomials.laurentDifferential, "definition"),
    (`PaperVerification.Segre.CechMonomials.laurentDifferential_apply, "theorem"),
    (`PaperVerification.Segre.CechMonomials.laurentDifferential_mem, "theorem"),
    (`PaperVerification.Segre.CechMonomials.laurentDifferential_squared, "theorem"),
    (`PaperVerification.Segre.CechMonomials.coefficientContraction, "definition"),
    (`PaperVerification.Segre.CechMonomials.coefficientContraction_mem, "theorem"),
    (`PaperVerification.Segre.CechMonomials.laurentContraction, "definition"),
    (`PaperVerification.Segre.CechMonomials.laurentContraction_apply, "theorem"),
    (`PaperVerification.Segre.CechMonomials.laurentContraction_mem, "theorem"),
    (`PaperVerification.Segre.CechMonomials.negativeSupport_eq_univ_of_no_nonnegative, "theorem"),
    (`PaperVerification.Segre.CechMonomials.laurent_exact_below_dimension, "theorem"),
    (`PaperVerification.Segre.CechMonomials.laurent_exact_of_twist, "theorem"),
    (`PaperVerification.Segre.CechMonomials.laurent_global_cocycle_eq_zero, "theorem")
  ]
  let localNames := env.checked.get.constants.foldStage2 (fun acc name _ => acc.push name) (#[] : Array Name)
  if localNames.isEmpty then throwError "Empty authored declaration audit"
  let mut names := localNames
  for (name, _) in required do
    unless names.contains name do names := names.push name
  let mut rows : Array Json := #[]
  for name in names do
    let some info := env.checked.get.find? name | throwError "Missing checked declaration {name}"
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient primitive"
    if kind == "axiom" then throwError "Authored axiom {name}"
    let value := info.value? (allowOpaque := true)
    if kind == "theorem" || kind == "definition" || kind == "opaque" then
      unless value.isSome do throwError "No actual body {name}"
    for (requiredName, expectedKind) in required do
      if name == requiredName && kind != expectedKind then
        throwError "Endpoint kind mismatch {name}: expected {expectedKind}, got {kind}"
    let axioms ← collectAxioms name
    for ax in axioms do
      if ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound then
        throwError "Unapproved transitive axiom {name}: {ax}"
    let mut fields := [("name", toJson name.toString), ("kind", toJson kind),
      ("actual_body_available", toJson value.isSome),
      ("universe_parameters", toJson (info.levelParams.map Name.toString)),
      ("type_dependencies", toJson (info.type.getUsedConstants.map Name.toString)),
      ("body_dependencies", toJson ((value.map Expr.getUsedConstants).getD #[] |>.map Name.toString)),
      ("transitive_axioms", toJson (axioms.map Name.toString))]
    if required.any (fun e => e.1 == name) then
      let typeText ← liftTermElabM <| return (← Meta.ppExpr info.type).pretty
      fields := fields ++ [("readable_type", toJson typeText)]
    rows := rows.push (Json.mkObj fields)
  IO.FS.createDirAll ".lake/reports"
  let path := ".lake/reports/" ++ (← getEnv).mainModule.toString ++ ".json"
  IO.FS.writeFile path (Json.mkObj [("accepted", toJson true),
    ("nonce", toJson "559350b6f2eccffb4415237dafc68cca"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:559350b6f2eccffb4415237dafc68cca"
