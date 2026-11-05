module

public import higher_specht.verified.remaining04_geometry_complete
public import tau_ceti.ring_theory.koszul_complex.basis
public import Mathlib.Data.Fin.Tuple.Take
public import Mathlib.RingTheory.Regular.Flat
public import tau_ceti.ring_theory.koszul_complex.regular
public import Mathlib.CategoryTheory.Monoidal.Tor
public import tau_ceti.linear_algebra.exterior_power.localization
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import tau_ceti.algebra.category.module_cat.projective.dimension
public import tau_ceti.data.e_nat.basic
public import tau_ceti.linear_algebra.dual.right_action
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import tau_ceti.algebra.category.module_cat.coextend_scalars
public import tau_ceti.algebra.homology.ext.basic
public import tau_ceti.ring_theory.regular_local_ring.projective_dimension
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.Algebra.Category.ModuleCat.InjectiveDimension
public import Mathlib.RingTheory.LocalProperties.InjectiveDimension

/- Generated ordinary source-preserving proof stage. See audit/staged_specht_remaining/Final/manifest.json. -/

@[expose] public section

section CanonicalSource51
/- Source: HigherSpecht/GradedDividedDuality.lean -/



/-!
# Homogeneous pieces of the actual quotient and divided-power dual

Projection onto degree d is self-adjoint for the coefficient pairing.
Consequently the actual quotient homogeneous component and the actual
degree-d inverse-system component have the same dimension.  The proof
compares ranges of conjugate linear projections; it does not infer a
graded dimension identity from a Hilbert-series formula.
-/

noncomputable section
open MvPolynomial Module
open scoped Classical

namespace HigherSpecht

variable {R : Type*} [CommRing R] {n : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra

theorem dividedApolarFunctional_homogeneousComponent
    (d : ℕ) (w f : PolynomialRing n R) :
    dividedApolarFunctional (MvPolynomial.homogeneousComponent d w) f =
      dividedApolarFunctional w (MvPolynomial.homogeneousComponent d f) := by
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => simp only [map_add, hf, hg]
  | monomial a c =>
      rw [MvPolynomial.homogeneousComponent_of_mem
        (MvPolynomial.isHomogeneous_monomial c rfl)]
      rw [dividedApolarFunctional_monomial, MvPolynomial.coeff_homogeneousComponent]
      by_cases ha : a.degree = d
      · simp only [ha, if_pos, eq_self_iff_true, dividedApolarFunctional_monomial]
      · simp only [if_neg ha, if_neg (Ne.symm ha), mul_zero, map_zero]

theorem dividedApolarFunctional_eq_component {D : ℕ} {w : PolynomialRing n R}
    (hw : w.IsHomogeneous D) (f : PolynomialRing n R) :
    dividedApolarFunctional w f =
      dividedApolarFunctional w (MvPolynomial.homogeneousComponent D f) := by
  simpa only [MvPolynomial.homogeneousComponent_eq_self hw] using
    dividedApolarFunctional_homogeneousComponent D w f

theorem dividedApolarFunctional_eq_zero_of_degree_ne {D d : ℕ}
    {w f : PolynomialRing n R} (hw : w.IsHomogeneous D)
    (hf : f.IsHomogeneous d) (hne : D ≠ d) : dividedApolarFunctional w f = 0 := by
  rw [dividedApolarFunctional_eq_component hw,
    MvPolynomial.homogeneousComponent_of_mem hf, if_neg hne, map_zero]

def quotientHomogeneousPiece (I : Ideal (PolynomialRing n R)) (d : ℕ) :
    Submodule R (PolynomialRing n R ⧸ I) :=
  (MvPolynomial.homogeneousSubmodule (Fin n) R d).map (Ideal.Quotient.mkₐ R I).toLinearMap

def quotientHomogeneousProjection (I : Ideal (PolynomialRing n R))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) R)) (d : ℕ) :
    Module.End R (PolynomialRing n R ⧸ I) :=
  (I.restrictScalars R).liftQ
    ((Ideal.Quotient.mkₐ R I).toLinearMap.comp (MvPolynomial.homogeneousComponent d))
    (fun f hf => Ideal.Quotient.eq_zero_iff_mem.mpr
      (MvPolynomial.homogeneousComponent_mem_of_mem hI hf d))

@[simp] theorem quotientHomogeneousProjection_mk
    (I : Ideal (PolynomialRing n R))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) R))
    (d : ℕ) (f : PolynomialRing n R) :
    quotientHomogeneousProjection I hI d (Ideal.Quotient.mk I f) =
      Ideal.Quotient.mk I (MvPolynomial.homogeneousComponent d f) := rfl

theorem quotientHomogeneousProjection_range
    (I : Ideal (PolynomialRing n R))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) R)) (d : ℕ) :
    LinearMap.range (quotientHomogeneousProjection I hI d) = quotientHomogeneousPiece I d := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine Submodule.Quotient.induction_on _ x ?_
    intro f
    exact ⟨MvPolynomial.homogeneousComponent d f,
      MvPolynomial.homogeneousComponent_mem d f, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    refine ⟨Ideal.Quotient.mk I f, ?_⟩
    rw [quotientHomogeneousProjection_mk, MvPolynomial.homogeneousComponent_eq_self hf]
    rfl

theorem quotientHomogeneousProjection_eq_self_of_mem
    (I : Ideal (PolynomialRing n R))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) R))
    (d : ℕ) {z : PolynomialRing n R ⧸ I} (hz : z ∈ quotientHomogeneousPiece I d) :
    quotientHomogeneousProjection I hI d z = z := by
  obtain ⟨f, hf, rfl⟩ := hz
  change quotientHomogeneousProjection I hI d (Ideal.Quotient.mk I f) =
    Ideal.Quotient.mk I f
  rw [quotientHomogeneousProjection_mk, MvPolynomial.homogeneousComponent_eq_self hf]

theorem quotientHomogeneousPiece_disjoint
    (I : Ideal (PolynomialRing n R))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) R))
    {d e : ℕ} (hne : d ≠ e) :
    Disjoint (quotientHomogeneousPiece I d) (quotientHomogeneousPiece I e) := by
  rw [disjoint_iff_inf_le]
  intro z hz
  have hfixed := quotientHomogeneousProjection_eq_self_of_mem I hI d hz.1
  obtain ⟨f, hf, rfl⟩ := hz.2
  change quotientHomogeneousProjection I hI d (Ideal.Quotient.mk I f) =
    Ideal.Quotient.mk I f at hfixed
  rw [quotientHomogeneousProjection_mk, MvPolynomial.homogeneousComponent_of_mem hf,
    if_neg hne, map_zero] at hfixed
  exact hfixed.symm

theorem homogeneousComponent_mem_dividedHarmonics
    (I : Ideal (PolynomialRing n R))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) R))
    {w : PolynomialRing n R} (hw : w ∈ dividedHarmonics I) (d : ℕ) :
    MvPolynomial.homogeneousComponent d w ∈ dividedHarmonics I := by
  apply (mem_dividedHarmonics_iff_apolar I _).mpr
  intro f hf
  rw [dividedApolarFunctional_homogeneousComponent]
  exact (mem_dividedHarmonics_iff_apolar I w).mp hw _
    (MvPolynomial.homogeneousComponent_mem_of_mem hI hf d)

def homogeneousHarmonicSpace (I : Ideal (PolynomialRing n R)) (d : ℕ) :
    Submodule R (dividedHarmonics I) :=
  (MvPolynomial.homogeneousSubmodule (Fin n) R d).comap (dividedHarmonics I).subtype

def dividedHomogeneousProjection (I : Ideal (PolynomialRing n R))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) R)) (d : ℕ) :
    Module.End R (dividedHarmonics I) :=
  ((MvPolynomial.homogeneousComponent d).comp (dividedHarmonics I).subtype).codRestrict
    (dividedHarmonics I) (fun w => homogeneousComponent_mem_dividedHarmonics I hI w.property d)

@[simp] theorem dividedHomogeneousProjection_val
    (I : Ideal (PolynomialRing n R))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) R))
    (d : ℕ) (w : dividedHarmonics I) :
    (dividedHomogeneousProjection I hI d w).val =
      MvPolynomial.homogeneousComponent d w.val := rfl

theorem dividedHomogeneousProjection_range
    (I : Ideal (PolynomialRing n R))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) R)) (d : ℕ) :
    LinearMap.range (dividedHomogeneousProjection I hI d) = homogeneousHarmonicSpace I d := by
  ext w
  constructor
  · rintro ⟨p, rfl⟩
    exact MvPolynomial.homogeneousComponent_mem d p.val
  · intro hw
    refine ⟨w, Subtype.ext ?_⟩
    exact MvPolynomial.homogeneousComponent_eq_self hw

theorem dividedHomogeneousProjection_duality
    (I : Ideal (PolynomialRing n R))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) R)) (d : ℕ)
    (w : dividedHarmonics I) :
    dividedHarmonicQuotientDual I (dividedHomogeneousProjection I hI d w) =
      (quotientHomogeneousProjection I hI d).dualMap (dividedHarmonicQuotientDual I w) := by
  apply LinearMap.ext
  intro z
  refine Submodule.Quotient.induction_on (I.restrictScalars R) z ?_
  intro f
  change dividedApolarFunctional (MvPolynomial.homogeneousComponent d w.val) f =
    dividedApolarFunctional w.val (MvPolynomial.homogeneousComponent d f)
  exact dividedApolarFunctional_homogeneousComponent d w.val f

def rangeEquivOfIntertwining {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (f : Module.End R M) (g : Module.End R N)
    (h : ∀ x, e (f x) = g (e x)) : LinearMap.range f ≃ₗ[R] LinearMap.range g :=
  LinearEquiv.ofBijective
    { toFun x := ⟨e x.val, by
        obtain ⟨y, hy⟩ := x.property
        exact ⟨e y, (h y).symm.trans (congrArg e hy)⟩⟩
      map_add' x y := Subtype.ext (e.map_add _ _)
      map_smul' c x := Subtype.ext (e.map_smul _ _) }
    ⟨fun x y hxy => Subtype.ext (e.injective (congrArg Subtype.val hxy)), by
      rintro ⟨z, y, hy⟩
      refine ⟨⟨f (e.symm y), LinearMap.mem_range.mpr ⟨e.symm y, rfl⟩⟩,
        Subtype.ext ?_⟩
      change e (f (e.symm y)) = z
      rw [h, e.apply_symm_apply, hy]⟩

theorem finrank_homogeneousHarmonicSpace_eq_quotientHomogeneousPiece
    {K : Type*} [Field K] {n s : ℕ} (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (hpower : powerIdeal K n s ≤ I) (d : ℕ) :
    Module.finrank K (homogeneousHarmonicSpace I d) =
      Module.finrank K (quotientHomogeneousPiece I d) := by
  let e := dividedHarmonicQuotientDualEquiv I hpower
  have he := (rangeEquivOfIntertwining e (dividedHomogeneousProjection I hI d)
    (quotientHomogeneousProjection I hI d).dualMap
    (dividedHomogeneousProjection_duality I hI d)).finrank_eq
  rw [dividedHomogeneousProjection_range,
    LinearMap.finrank_range_dualMap_eq_finrank_range,
    quotientHomogeneousProjection_range] at he
  exact he

end HigherSpecht
end
end CanonicalSource51

section CanonicalSource52
/- Source: HigherSpecht/QuotientIntegerGrading.lean -/



/-!
# Homogeneous representatives and regular-element quotient lifting

The integer grading is the actual image of homogeneous polynomials;
negative pieces are zero.  The kernel factorization below projects a
literal ideal relation to its homogeneous degree.  It supplies the
degree-sensitive quotient exactness needed by the Koszul proof.
-/

noncomputable section
open MvPolynomial Module Finset
open scoped Classical

namespace HigherSpecht

variable {K : Type*} [Field K] {n : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra

def quotientIntegerPiece (I : Ideal (PolynomialRing n K)) (a : ℤ) :
    Submodule K (PolynomialRing n K ⧸ I) :=
  if 0 ≤ a then quotientHomogeneousPiece I a.toNat else ⊥

@[simp] theorem quotientIntegerPiece_nat (I : Ideal (PolynomialRing n K)) (a : ℕ) :
    quotientIntegerPiece I (a : ℤ) = quotientHomogeneousPiece I a := by
  simp only [quotientIntegerPiece, Int.natCast_nonneg, if_true, Int.toNat_natCast]

theorem quotientIntegerPiece_eq_bot_of_neg (I : Ideal (PolynomialRing n K))
    {a : ℤ} (ha : a < 0) : quotientIntegerPiece I a = ⊥ := by
  rw [quotientIntegerPiece, if_neg (not_le.mpr ha)]

theorem quotientIntegerPiece_mk (I : Ideal (PolynomialRing n K))
    {d : ℕ} {p : PolynomialRing n K} (hp : p.IsHomogeneous d) :
    Ideal.Quotient.mk I p ∈ quotientIntegerPiece I (d : ℤ) := by
  rw [quotientIntegerPiece_nat]
  exact ⟨p, hp, rfl⟩

theorem quotientIntegerPiece_mul (I : Ideal (PolynomialRing n K))
    {a b : ℤ} {x y : PolynomialRing n K ⧸ I}
    (hx : x ∈ quotientIntegerPiece I a) (hy : y ∈ quotientIntegerPiece I b) :
    x * y ∈ quotientIntegerPiece I (a + b) := by
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · rw [quotientIntegerPiece, if_pos ha] at hx
      rw [quotientIntegerPiece, if_pos hb] at hy
      obtain ⟨p, hp, rfl⟩ := hx
      obtain ⟨q, hq, rfl⟩ := hy
      change Ideal.Quotient.mk I p * Ideal.Quotient.mk I q ∈
        quotientIntegerPiece I (a + b)
      rw [← map_mul, quotientIntegerPiece, if_pos (add_nonneg ha hb)]
      refine ⟨p * q, ?_, rfl⟩
      rw [Int.toNat_add ha hb]
      exact hp.mul hq
    · rw [quotientIntegerPiece, if_neg hb] at hy
      rw [show y = 0 from hy, mul_zero]
      exact Submodule.zero_mem _
  · rw [quotientIntegerPiece, if_neg ha] at hx
    rw [show x = 0 from hx, zero_mul]
    exact Submodule.zero_mem _

theorem quotientIntegerPiece_factor_mem {I J : Ideal (PolynomialRing n K)} (hIJ : I ≤ J)
    {a : ℤ} {x : PolynomialRing n K ⧸ I} (hx : x ∈ quotientIntegerPiece I a) :
    Ideal.Quotient.factorₐ K hIJ x ∈ quotientIntegerPiece J a := by
  by_cases ha : 0 ≤ a
  · rw [quotientIntegerPiece, if_pos ha] at hx ⊢
    obtain ⟨p, hp, rfl⟩ := hx
    exact ⟨p, hp, rfl⟩
  · rw [quotientIntegerPiece, if_neg ha] at hx ⊢
    rw [show x = 0 from hx, map_zero]
    exact Submodule.zero_mem _

theorem quotientIntegerPiece_factor_lift {I J : Ideal (PolynomialRing n K)} (hIJ : I ≤ J)
    {a : ℤ} {x : PolynomialRing n K ⧸ J} (hx : x ∈ quotientIntegerPiece J a) :
    ∃ y ∈ quotientIntegerPiece I a, Ideal.Quotient.factorₐ K hIJ y = x := by
  by_cases ha : 0 ≤ a
  · rw [quotientIntegerPiece, if_pos ha] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    refine ⟨Ideal.Quotient.mk I p, ?_, rfl⟩
    rw [quotientIntegerPiece, if_pos ha]
    exact ⟨p, hp, rfl⟩
  · rw [quotientIntegerPiece, if_neg ha] at hx
    exact ⟨0, Submodule.zero_mem _, (map_zero _).trans (show x = 0 from hx).symm⟩

def adjoinHomogeneousElement (I : Ideal (PolynomialRing n K)) (f : PolynomialRing n K) :
    Ideal (PolynomialRing n K) := I ⊔ Ideal.span {f}

theorem adjoinHomogeneousElement_isHomogeneous
    (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    {d : ℕ} {f : PolynomialRing n K} (hf : f.IsHomogeneous d) :
    (adjoinHomogeneousElement I f).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) K) := by
  apply hI.sup
  apply Ideal.homogeneous_span
  rintro p ⟨rfl⟩
  exact ⟨d, hf⟩

/-- The homogeneous kernel element is divided by the actual newly adjoined
polynomial.  This factorization does not need regularity; cancellation in
the later Koszul argument is the separate use of regularity. -/
theorem quotientIntegerPiece_adjoin_kernel
    (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    {d : ℕ} {f : PolynomialRing n K} (hf : f.IsHomogeneous d)
    {a : ℤ} {x : PolynomialRing n K ⧸ I}
    (hx : x ∈ quotientIntegerPiece I a)
    (hzero : Ideal.Quotient.factorₐ K
      (show I ≤ adjoinHomogeneousElement I f from le_sup_left) x = 0) :
    ∃ y ∈ quotientIntegerPiece I (a - d), Ideal.Quotient.mk I f * y = x := by
  by_cases ha : 0 ≤ a
  · rw [quotientIntegerPiece, if_pos ha] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    change ∃ y ∈ quotientIntegerPiece I (a - d),
      Ideal.Quotient.mk I f * y = Ideal.Quotient.mk I p
    have hpJ : p ∈ I ⊔ Ideal.span {f} := Ideal.Quotient.eq_zero_iff_mem.mp hzero
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hpJ
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hv
    have hrelation : p = u + c * f := by
      rw [mul_comm, ← hc]
      exact huv.symm
    have hproj := congrArg (MvPolynomial.homogeneousComponent a.toNat) hrelation
    rw [MvPolynomial.homogeneousComponent_eq_self hp, map_add,
      homogeneousComponent_mul_homogeneous_right _ _ hf] at hproj
    have hu0 : Ideal.Quotient.mk I (MvPolynomial.homogeneousComponent a.toNat u) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        (MvPolynomial.homogeneousComponent_mem_of_mem hI hu a.toNat)
    by_cases hd : d ≤ a.toNat
    · let q := MvPolynomial.homogeneousComponent (a.toNat - d) c
      have hdeg : (↑(a.toNat - d) : ℤ) = a - d := by
        rw [Int.natCast_sub hd, Int.toNat_of_nonneg ha]
      refine ⟨Ideal.Quotient.mk I q, ?_, ?_⟩
      · rw [← hdeg]
        exact quotientIntegerPiece_mk I (MvPolynomial.homogeneousComponent_isHomogeneous _ c)
      · have h := congrArg (Ideal.Quotient.mk I) hproj
        rw [if_pos hd, map_add, hu0, zero_add, map_mul] at h
        simpa only [q, mul_comm] using h.symm
    · refine ⟨0, Submodule.zero_mem _, ?_⟩
      have h := congrArg (Ideal.Quotient.mk I) hproj
      rw [if_neg hd, map_add, hu0, map_zero, add_zero] at h
      rw [mul_zero, h]
  · rw [quotientIntegerPiece, if_neg ha] at hx
    exact ⟨0, Submodule.zero_mem _, (mul_zero _).trans (show x = 0 from hx).symm⟩

theorem homogeneous_positive_eq_sum_variables
    {d : ℕ} {f : PolynomialRing n K} (hf : f.IsHomogeneous d) (hd : 0 < d) :
    ∃ g : Fin n → PolynomialRing n K,
      (∀ i, (g i).IsHomogeneous (d - 1)) ∧
      (∑ i, MvPolynomial.X i * g i) = f := by
  have hm : f ∈ MvPolynomial.idealOfVars (Fin n) K := by
    rw [← pow_one (MvPolynomial.idealOfVars (Fin n) K),
      MvPolynomial.mem_pow_idealOfVars_iff]
    intro a ha
    have hadeg := hf (MvPolynomial.mem_support_iff.mp ha)
    change Finsupp.weight (fun _ : Fin n => (1 : ℕ)) a = d at hadeg
    rw [← Finsupp.degree_eq_weight_one] at hadeg
    omega
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun (PolynomialRing n K)).mp hm
  have h := congrArg (MvPolynomial.homogeneousComponent d) hg
  simp only [map_sum, smul_eq_mul,
    homogeneousComponent_mul_homogeneous_right _ _ (MvPolynomial.isHomogeneous_X K _),
    if_pos (show 1 ≤ d by omega), MvPolynomial.homogeneousComponent_eq_self hf] at h
  exact ⟨fun i => MvPolynomial.homogeneousComponent (d - 1) (g i),
    fun i => MvPolynomial.homogeneousComponent_isHomogeneous _ _,
    by simpa only [mul_comm] using h⟩

end HigherSpecht
end
end CanonicalSource52

section CanonicalSource53
/- Source: HigherSpecht/GradedNullHomotopyReduction.lean -/



/-!
# Homogeneous cycle lifting across a regular null-homotopic scalar

The first index is homological degree and the second is coefficient
degree.  The differential changes them by (-1,+1).  This is the grading
on a coordinate Koszul complex: total internal degree is their sum.

The theorem below proves the regular-element shift in Koszul homology
support directly.  All quotient lifting and degree facts are stated as
the precise structural interface to be instantiated by an actual
homogeneous polynomial quotient.  This generic lemma alone is not a
regularity theorem for any of the paper's rings.
-/

noncomputable section

namespace HigherSpecht

variable {K M N : Type*} [Field K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

structure DifferentialBigrading (K M : Type*) [Field K]
    [AddCommGroup M] [Module K M] where
  piece : ℤ → ℤ → Submodule K M
  differential : Module.End K M
  square_zero : ∀ x, differential (differential x) = 0
  differential_mem : ∀ {i a x}, x ∈ piece i a →
    differential x ∈ piece (i - 1) (a + 1)

namespace DifferentialBigrading

def HomologyVanishesAbove (C : DifferentialBigrading K M) (r : ℤ) : Prop :=
  ∀ (i a : ℤ) (x : M), x ∈ C.piece i a → r < a → C.differential x = 0 →
    ∃ y ∈ C.piece (i + 1) (a - 1), C.differential y = x

structure RegularHomogeneousQuotient
    (C : DifferentialBigrading K M) (B : DifferentialBigrading K N) (d : ℤ) where
  projection : M →ₗ[K] N
  scalar : Module.End K M
  homotopy : Module.End K M
  scalar_injective : Function.Injective scalar
  projection_scalar : ∀ x, projection (scalar x) = 0
  projection_differential : ∀ x,
    projection (C.differential x) = B.differential (projection x)
  scalar_differential : ∀ x,
    C.differential (scalar x) = scalar (C.differential x)
  homotopy_identity : ∀ x,
    C.differential (homotopy x) + homotopy (C.differential x) = scalar x
  projection_mem : ∀ {i a x}, x ∈ C.piece i a → projection x ∈ B.piece i a
  scalar_mem : ∀ {i a x}, x ∈ C.piece i a → scalar x ∈ C.piece i (a + d)
  homotopy_mem : ∀ {i a x}, x ∈ C.piece i a →
    homotopy x ∈ C.piece (i + 1) (a + d - 1)
  homogeneous_lift : ∀ {i a x}, x ∈ B.piece i a →
    ∃ y ∈ C.piece i a, projection y = x
  homogeneous_kernel : ∀ {i a x}, x ∈ C.piece i a → projection x = 0 →
    ∃ y ∈ C.piece i (a - d), scalar y = x

namespace RegularHomogeneousQuotient

variable {C : DifferentialBigrading K M} {B : DifferentialBigrading K N} {d : ℤ}

theorem homotopy_of_cycle (Q : RegularHomogeneousQuotient C B d)
    {x : M} (hx : C.differential x = 0) :
    C.differential (Q.homotopy x) = Q.scalar x := by
  simpa only [hx, map_zero, add_zero] using Q.homotopy_identity x

/-- Forward bound: lift a cycle, divide its differential by the regular
element, kill that smaller cycle, and then lift a boundary. -/
theorem vanishing_quotient (Q : RegularHomogeneousQuotient C B d)
    (hd : 1 ≤ d) {r : ℤ} (hC : C.HomologyVanishesAbove r) :
    B.HomologyVanishesAbove (r + d - 1) := by
  intro i a x hx ha hcycle
  obtain ⟨u, hu, hux⟩ := Q.homogeneous_lift hx
  have hdu : C.differential u ∈ C.piece (i - 1) (a + 1) := C.differential_mem hu
  have hpdu : Q.projection (C.differential u) = 0 := by
    rw [Q.projection_differential, hux, hcycle]
  obtain ⟨v, hv, hfv⟩ := Q.homogeneous_kernel hdu hpdu
  have hdv : C.differential v = 0 := by
    apply Q.scalar_injective
    rw [← Q.scalar_differential, hfv, C.square_zero, map_zero]
  obtain ⟨w, hw, hdw⟩ := hC (i - 1) (a + 1 - d) v hv (by omega) hdv
  have hw' : w ∈ C.piece i (a - d) := by
    simpa only [show i - 1 + 1 = i by omega,
      show a + 1 - d - 1 = a - d by omega] using hw
  have hfw : Q.scalar w ∈ C.piece i a := by
    simpa only [sub_add_cancel] using Q.scalar_mem hw'
  have hnew : u - Q.scalar w ∈ C.piece i a := (C.piece i a).sub_mem hu hfw
  have hdnew : C.differential (u - Q.scalar w) = 0 := by
    rw [map_sub, Q.scalar_differential, hdw, hfv, sub_self]
  obtain ⟨z, hz, hdz⟩ := hC i a (u - Q.scalar w) hnew (by omega) hdnew
  refine ⟨Q.projection z, Q.projection_mem hz, ?_⟩
  rw [← Q.projection_differential, hdz, map_sub, Q.projection_scalar, sub_zero, hux]

/-- Reverse bound: the explicit null-homotopy makes every old cycle the
connecting image of a quotient cycle. Regularity allows cancellation
after a homogeneous lift of its boundary. -/
theorem vanishing_original (Q : RegularHomogeneousQuotient C B d)
    {r : ℤ} (hB : B.HomologyVanishesAbove (r + d - 1)) :
    C.HomologyVanishesAbove r := by
  intro i a x hx ha hcycle
  have hh : Q.homotopy x ∈ C.piece (i + 1) (a + d - 1) := Q.homotopy_mem hx
  have hph : Q.projection (Q.homotopy x) ∈ B.piece (i + 1) (a + d - 1) :=
    Q.projection_mem hh
  have hcycle' : B.differential (Q.projection (Q.homotopy x)) = 0 := by
    rw [← Q.projection_differential, Q.homotopy_of_cycle hcycle, Q.projection_scalar]
  obtain ⟨v, hv, hdv⟩ := hB (i + 1) (a + d - 1)
    (Q.projection (Q.homotopy x)) hph (by omega) hcycle'
  obtain ⟨u, hu, hpu⟩ := Q.homogeneous_lift hv
  have hdu : C.differential u ∈ C.piece (i + 1) (a + d - 1) := by
    have h := C.differential_mem hu
    simpa only [show i + 1 + 1 - 1 = i + 1 by omega,
      show a + d - 1 - 1 + 1 = a + d - 1 by omega] using h
  have hker : Q.projection (Q.homotopy x - C.differential u) = 0 := by
    rw [map_sub, Q.projection_differential, hpu, hdv, sub_self]
  obtain ⟨z, hz, hfz⟩ := Q.homogeneous_kernel
    ((C.piece (i + 1) (a + d - 1)).sub_mem hh hdu) hker
  refine ⟨z, ?_, ?_⟩
  · simpa only [show a + d - 1 - d = a - 1 by omega] using hz
  · apply Q.scalar_injective
    rw [← Q.scalar_differential, hfz, map_sub, C.square_zero, sub_zero,
      Q.homotopy_of_cycle hcycle]

theorem vanishing_iff (Q : RegularHomogeneousQuotient C B d) (hd : 1 ≤ d) (r : ℤ) :
    B.HomologyVanishesAbove (r + d - 1) ↔ C.HomologyVanishesAbove r :=
  ⟨Q.vanishing_original, Q.vanishing_quotient hd⟩

end RegularHomogeneousQuotient
end DifferentialBigrading
end HigherSpecht
end
end CanonicalSource53

section CanonicalSource54
/- Source: HigherSpecht/CoordinateKoszulGrading.lean -/



/-!
# The actual coordinate Koszul complex and its two gradings

The carrier is the exterior algebra over the actual polynomial quotient.
The differential is Mathlib's contraction by the coordinate functional.
Its exterior degree is the homological degree; its coefficient degree is
the genuine quotient grading. Their sum is internal degree.
-/

noncomputable section
open MvPolynomial Module Finset CliffordAlgebra
open scoped Classical

namespace HigherSpecht

variable {K : Type*} [Field K] {n : ℕ}

abbrev CoordinateKoszulCarrier (I : Ideal (PolynomialRing n K)) :=
  ExteriorAlgebra (PolynomialRing n K ⧸ I) (Fin n → PolynomialRing n K ⧸ I)

def coordinateKoszulBasis (I : Ideal (PolynomialRing n K)) :
    Basis (Finset (Fin n)) (PolynomialRing n K ⧸ I) (CoordinateKoszulCarrier I) :=
  (Pi.basisFun (PolynomialRing n K ⧸ I) (Fin n)).ExteriorAlgebra

def coordinateKoszulFunctional (I : Ideal (PolynomialRing n K)) :
    Module.Dual (PolynomialRing n K ⧸ I) (Fin n → PolynomialRing n K ⧸ I) :=
  ∑ j : Fin n, Ideal.Quotient.mk I (MvPolynomial.X j) •
    (Pi.basisFun (PolynomialRing n K ⧸ I) (Fin n)).coord j

@[simp] theorem coordinateKoszulFunctional_basis
    (I : Ideal (PolynomialRing n K)) (j : Fin n) :
    coordinateKoszulFunctional I (Pi.basisFun (PolynomialRing n K ⧸ I) (Fin n) j) =
      Ideal.Quotient.mk I (MvPolynomial.X j) := by
  simp only [coordinateKoszulFunctional, LinearMap.sum_apply, LinearMap.smul_apply,
    Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  simp

def coordinateKoszulDifferential (I : Ideal (PolynomialRing n K)) :
    Module.End K (CoordinateKoszulCarrier I) :=
  (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm (PolynomialRing n K ⧸ I)
    (Fin n → PolynomialRing n K ⧸ I))) (coordinateKoszulFunctional I)).restrictScalars K

@[simp] theorem coordinateKoszulDifferential_square
    (I : Ideal (PolynomialRing n K)) (z : CoordinateKoszulCarrier I) :
    coordinateKoszulDifferential I (coordinateKoszulDifferential I z) = 0 :=
  CliffordAlgebra.contractLeft_contractLeft (coordinateKoszulFunctional I) z

theorem coordinateKoszulDifferential_smul (I : Ideal (PolynomialRing n K))
    (c : PolynomialRing n K ⧸ I) (z : CoordinateKoszulCarrier I) :
    coordinateKoszulDifferential I (c • z) = c • coordinateKoszulDifferential I z :=
  map_smul (CliffordAlgebra.contractLeft (Q := 0) (coordinateKoszulFunctional I)) c z

theorem coordinateKoszulDifferential_basis (I : Ideal (PolynomialRing n K))
    (s : Finset (Fin n)) :
    coordinateKoszulDifferential I (coordinateKoszulBasis I s) =
      ∑ j : Fin n, if j ∈ s then
        Ideal.Quotient.mk I (MvPolynomial.X j) •
          (TauCeti.ExteriorAlgebra.basisEraseSign j s • coordinateKoszulBasis I (s.erase j))
        else 0 := by
  simp only [coordinateKoszulDifferential, LinearMap.restrictScalars_apply,
    coordinateKoszulFunctional, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, coordinateKoszulBasis,
    TauCeti.ExteriorAlgebra.contractLeft_coord_basis]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> simp only [smul_zero]

def coordinateKoszulPiece (I : Ideal (PolynomialRing n K)) (i a : ℤ) :
    Submodule K (CoordinateKoszulCarrier I) :=
  ⨅ s : Finset (Fin n),
    (if (s.card : ℤ) = i then quotientIntegerPiece I a else ⊥).comap
      (((coordinateKoszulBasis I).coord s).restrictScalars K)

theorem mem_coordinateKoszulPiece (I : Ideal (PolynomialRing n K))
    (i a : ℤ) (z : CoordinateKoszulCarrier I) :
    z ∈ coordinateKoszulPiece I i a ↔
      ∀ s : Finset (Fin n), (coordinateKoszulBasis I).repr z s ∈
        if (s.card : ℤ) = i then quotientIntegerPiece I a else ⊥ := by
  simp only [coordinateKoszulPiece, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Basis.coord_apply]

theorem coordinateKoszulPiece_generator (I : Ideal (PolynomialRing n K))
    {i a : ℤ} (s : Finset (Fin n)) (hs : (s.card : ℤ) = i)
    {c : PolynomialRing n K ⧸ I} (hc : c ∈ quotientIntegerPiece I a) :
    c • coordinateKoszulBasis I s ∈ coordinateKoszulPiece I i a := by
  rw [mem_coordinateKoszulPiece]
  intro t
  simp only [map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
    smul_eq_mul]
  by_cases hts : s = t
  · subst t
    simpa only [hs, if_true, mul_one] using hc
  · simp only [if_neg hts, mul_zero]
    exact Submodule.zero_mem _

theorem coordinateKoszulPiece_le_iff (I : Ideal (PolynomialRing n K))
    (i a : ℤ) (P : Submodule K (CoordinateKoszulCarrier I)) :
    coordinateKoszulPiece I i a ≤ P ↔
      ∀ (s : Finset (Fin n)) (c : PolynomialRing n K ⧸ I),
        (s.card : ℤ) = i → c ∈ quotientIntegerPiece I a →
        c • coordinateKoszulBasis I s ∈ P := by
  constructor
  · intro h s c hs hc
    exact h (coordinateKoszulPiece_generator I s hs hc)
  · intro h z hz
    rw [← (coordinateKoszulBasis I).sum_repr z]
    apply P.sum_mem
    intro s hs
    have hc := (mem_coordinateKoszulPiece I i a z).mp hz s
    by_cases hsi : (s.card : ℤ) = i
    · rw [if_pos hsi] at hc
      exact h s _ hsi hc
    · rw [if_neg hsi] at hc
      rw [show (coordinateKoszulBasis I).repr z s = 0 from hc]
      exact (zero_smul (PolynomialRing n K ⧸ I) (coordinateKoszulBasis I s)).symm ▸
        P.zero_mem

set_option backward.isDefEq.respectTransparency false in
theorem coordinateKoszulDifferential_mem (I : Ideal (PolynomialRing n K))
    {i a : ℤ} {z : CoordinateKoszulCarrier I} (hz : z ∈ coordinateKoszulPiece I i a) :
    coordinateKoszulDifferential I z ∈ coordinateKoszulPiece I (i - 1) (a + 1) := by
  apply ((coordinateKoszulPiece_le_iff I i a
    ((coordinateKoszulPiece I (i - 1) (a + 1)).comap (coordinateKoszulDifferential I))).mpr ?_) hz
  intro s c hsi hc
  change coordinateKoszulDifferential I (c • coordinateKoszulBasis I s) ∈
    coordinateKoszulPiece I (i - 1) (a + 1)
  rw [coordinateKoszulDifferential_smul, coordinateKoszulDifferential_basis]
  rw [Finset.smul_sum (M := PolynomialRing n K ⧸ I)
    (N := CoordinateKoszulCarrier I) (r := c)]
  apply (coordinateKoszulPiece I (i - 1) (a + 1)).sum_mem
  intro j hj
  by_cases hjs : j ∈ s
  · rw [if_pos hjs]
    have hdegree : (↑(s.erase j).card : ℤ) = i - 1 := by
      rw [Finset.card_erase_of_mem hjs]
      have hpos := Finset.card_pos.mpr ⟨j, hjs⟩
      omega
    have hcc : c * Ideal.Quotient.mk I (MvPolynomial.X j) ∈ quotientIntegerPiece I (a + 1) :=
      quotientIntegerPiece_mul I hc (quotientIntegerPiece_mk I (MvPolynomial.isHomogeneous_X K j))
    have hgen := coordinateKoszulPiece_generator I (s.erase j) hdegree hcc
    change c • (Ideal.Quotient.mk I (MvPolynomial.X j) •
        ((TauCeti.ExteriorAlgebra.basisEraseSign j s : ℤ) •
          coordinateKoszulBasis I (s.erase j))) ∈
      coordinateKoszulPiece I (i - 1) (a + 1)
    have heq :=
      (smul_smul c (Ideal.Quotient.mk I (MvPolynomial.X j))
        ((TauCeti.ExteriorAlgebra.basisEraseSign j s : ℤ) •
          coordinateKoszulBasis I (s.erase j))).trans
        (smul_comm (c * Ideal.Quotient.mk I (MvPolynomial.X j))
          (TauCeti.ExteriorAlgebra.basisEraseSign j s : ℤ)
          (coordinateKoszulBasis I (s.erase j)))
    exact heq.symm ▸ (coordinateKoszulPiece I (i - 1) (a + 1)).toAddSubgroup.zsmul_mem hgen _
  · rw [if_neg hjs, smul_zero]
    exact Submodule.zero_mem _

def coordinateKoszulBigrading (I : Ideal (PolynomialRing n K)) :
    DifferentialBigrading K (CoordinateKoszulCarrier I) where
  piece := coordinateKoszulPiece I
  differential := coordinateKoszulDifferential I
  square_zero := coordinateKoszulDifferential_square I
  differential_mem := coordinateKoszulDifferential_mem I

def coordinateKoszulCycles (I : Ideal (PolynomialRing n K)) (i a : ℤ) :
    Submodule K (CoordinateKoszulCarrier I) :=
  coordinateKoszulPiece I i a ⊓ LinearMap.ker (coordinateKoszulDifferential I)

def coordinateKoszulBoundaries (I : Ideal (PolynomialRing n K)) (i a : ℤ) :
    Submodule K (CoordinateKoszulCarrier I) :=
  (coordinateKoszulPiece I (i + 1) (a - 1)).map (coordinateKoszulDifferential I)

theorem coordinateKoszulBoundaries_le_cycles (I : Ideal (PolynomialRing n K)) (i a : ℤ) :
    coordinateKoszulBoundaries I i a ≤ coordinateKoszulCycles I i a := by
  rintro z ⟨y, hy, rfl⟩
  constructor
  · change coordinateKoszulDifferential I y ∈ coordinateKoszulPiece I i a
    have h := coordinateKoszulDifferential_mem I hy
    have hi : (i + 1) - 1 = i := by omega
    have ha : (a - 1) + 1 = a := by omega
    simpa only [hi, ha] using h
  · exact coordinateKoszulDifferential_square I y

/-- The homogeneous component of the actual coordinate Koszul homology.
The exterior degree is i and the internal degree is i+a. -/
abbrev CoordinateKoszulHomology (I : Ideal (PolynomialRing n K)) (i a : ℤ) :=
  coordinateKoszulCycles I i a ⧸
    (coordinateKoszulBoundaries I i a).comap (coordinateKoszulCycles I i a).subtype

theorem coordinateKoszulHomology_subsingleton_iff
    (I : Ideal (PolynomialRing n K)) (i a : ℤ) :
    Subsingleton (CoordinateKoszulHomology I i a) ↔
      ∀ x, x ∈ coordinateKoszulPiece I i a → coordinateKoszulDifferential I x = 0 →
        ∃ y ∈ coordinateKoszulPiece I (i + 1) (a - 1),
          coordinateKoszulDifferential I y = x := by
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  constructor
  · intro h x hx hcycle
    exact h (show (⟨x, hx, hcycle⟩ : coordinateKoszulCycles I i a) ∈ ⊤ from trivial)
  · intro h x hx
    exact h x.val x.property.1 x.property.2

/-- This is the actual Koszul-homology support condition: homological
degree i and internal degree i+a contribute regularity a. -/
def KoszulRegularityLE (I : Ideal (PolynomialRing n K)) (r : ℤ) : Prop :=
  (coordinateKoszulBigrading I).HomologyVanishesAbove r

theorem koszulRegularityLE_iff_homology (I : Ideal (PolynomialRing n K)) (r : ℤ) :
    KoszulRegularityLE I r ↔
      ∀ i a, r < a → Subsingleton (CoordinateKoszulHomology I i a) := by
  constructor
  · intro h i a ha
    rw [coordinateKoszulHomology_subsingleton_iff]
    exact fun x hx hcycle => h i a x hx ha hcycle
  · intro h i a x hx ha hcycle
    exact (coordinateKoszulHomology_subsingleton_iff I i a).mp (h i a ha) x hx hcycle

/-- Exact Castelnuovo–Mumford regularity, expressed through the genuine
coordinate Koszul complex.  Both the bound and its sharpness are retained. -/
def HasKoszulRegularity (I : Ideal (PolynomialRing n K)) (r : ℤ) : Prop :=
  KoszulRegularityLE I r ∧ ¬ KoszulRegularityLE I (r - 1)

end HigherSpecht
end
end CanonicalSource54

section CanonicalSource55
/- Source: HigherSpecht/CoordinateKoszulQuotient.lean -/



/-!
# Actual coefficient change in coordinate Koszul complexes

The map is coefficientwise reduction in the exterior basis. Homogeneous
surjectivity and the homogeneous kernel calculation are proved one
coefficient at a time from actual quotient representatives. Thus the
later regularity comparison does not assume an exact sequence of complexes.
-/

noncomputable section
open MvPolynomial Module Finset CliffordAlgebra
open scoped Classical

namespace HigherSpecht

variable {K : Type*} [Field K] {n : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra

def coordinateKoszulMap {I J : Ideal (PolynomialRing n K)} (hIJ : I ≤ J) :
    CoordinateKoszulCarrier I →ₗ[K] CoordinateKoszulCarrier J :=
  ((coordinateKoszulBasis J).equivFun.symm.toLinearMap.restrictScalars K).comp
    (LinearMap.pi fun s => (Ideal.Quotient.factorₐ K hIJ).toLinearMap.comp
      (((coordinateKoszulBasis I).coord s).restrictScalars K))

@[simp] theorem coordinateKoszulMap_repr {I J : Ideal (PolynomialRing n K)} (hIJ : I ≤ J)
    (z : CoordinateKoszulCarrier I) (s : Finset (Fin n)) :
    (coordinateKoszulBasis J).repr (coordinateKoszulMap hIJ z) s =
      Ideal.Quotient.factorₐ K hIJ ((coordinateKoszulBasis I).repr z s) := by
  change (coordinateKoszulBasis J).equivFun
    ((coordinateKoszulBasis J).equivFun.symm _) s = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem coordinateKoszulMap_smul {I J : Ideal (PolynomialRing n K)} (hIJ : I ≤ J)
    (c : PolynomialRing n K ⧸ I) (z : CoordinateKoszulCarrier I) :
    coordinateKoszulMap hIJ (c • z) =
      Ideal.Quotient.factorₐ K hIJ c • coordinateKoszulMap hIJ z := by
  apply (coordinateKoszulBasis J).repr.injective
  ext s
  simp only [coordinateKoszulMap_repr, map_smul, Finsupp.smul_apply,
    smul_eq_mul, map_mul]

@[simp] theorem coordinateKoszulMap_basis {I J : Ideal (PolynomialRing n K)} (hIJ : I ≤ J)
    (s : Finset (Fin n)) :
    coordinateKoszulMap hIJ (coordinateKoszulBasis I s) = coordinateKoszulBasis J s := by
  apply (coordinateKoszulBasis J).repr.injective
  ext t
  simp only [coordinateKoszulMap_repr, Basis.repr_self, Finsupp.single_apply]
  split_ifs <;> simp only [map_zero, map_one]

theorem coordinateKoszulMap_differential {I J : Ideal (PolynomialRing n K)} (hIJ : I ≤ J)
    (z : CoordinateKoszulCarrier I) :
    coordinateKoszulMap hIJ (coordinateKoszulDifferential I z) =
      coordinateKoszulDifferential J (coordinateKoszulMap hIJ z) := by
  rw [← (coordinateKoszulBasis I).sum_repr z]
  simp only [map_sum, coordinateKoszulDifferential_smul, coordinateKoszulMap_smul]
  apply Finset.sum_congr rfl
  intro s hs
  rw [coordinateKoszulMap_basis]
  apply congrArg (fun v : CoordinateKoszulCarrier J =>
    Ideal.Quotient.factorₐ K hIJ ((coordinateKoszulBasis I).repr z s) • v)
  rw [coordinateKoszulDifferential_basis, coordinateKoszulDifferential_basis, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hjs : j ∈ s
  · simp only [if_pos hjs, coordinateKoszulMap_smul,
      Ideal.Quotient.factorₐ_apply_mk, Units.smul_def, map_zsmul,
      coordinateKoszulMap_basis]
  · simp only [if_neg hjs, smul_zero, map_zero]

theorem coordinateKoszulMap_mem {I J : Ideal (PolynomialRing n K)} (hIJ : I ≤ J)
    {i a : ℤ} {z : CoordinateKoszulCarrier I} (hz : z ∈ coordinateKoszulPiece I i a) :
    coordinateKoszulMap hIJ z ∈ coordinateKoszulPiece J i a := by
  rw [mem_coordinateKoszulPiece]
  intro s
  rw [coordinateKoszulMap_repr]
  have hs := (mem_coordinateKoszulPiece I i a z).mp hz s
  by_cases hsi : (s.card : ℤ) = i
  · rw [if_pos hsi] at hs ⊢
    exact quotientIntegerPiece_factor_mem hIJ hs
  · rw [if_neg hsi] at hs ⊢
    rw [show (coordinateKoszulBasis I).repr z s = 0 from hs, map_zero]
    exact Submodule.zero_mem _

theorem coordinateKoszulMap_homogeneous_lift
    {I J : Ideal (PolynomialRing n K)} (hIJ : I ≤ J)
    {i a : ℤ} {z : CoordinateKoszulCarrier J} (hz : z ∈ coordinateKoszulPiece J i a) :
    ∃ y ∈ coordinateKoszulPiece I i a, coordinateKoszulMap hIJ y = z := by
  have hc : ∀ s : Finset (Fin n),
      ∃ c : PolynomialRing n K ⧸ I,
        c ∈ (if (s.card : ℤ) = i then quotientIntegerPiece I a else ⊥) ∧
        Ideal.Quotient.factorₐ K hIJ c = (coordinateKoszulBasis J).repr z s := by
    intro s
    have hs := (mem_coordinateKoszulPiece J i a z).mp hz s
    by_cases hsi : (s.card : ℤ) = i
    · rw [if_pos hsi] at hs ⊢
      obtain ⟨c, hc, hmap⟩ := quotientIntegerPiece_factor_lift hIJ hs
      exact ⟨c, hc, hmap⟩
    · rw [if_neg hsi] at hs ⊢
      exact ⟨0, Submodule.zero_mem _,
        (map_zero _).trans (show (coordinateKoszulBasis J).repr z s = 0 from hs).symm⟩
  choose c hc hmap using hc
  let y := (coordinateKoszulBasis I).equivFun.symm c
  have hy (s : Finset (Fin n)) : (coordinateKoszulBasis I).repr y s = c s :=
    congrFun ((coordinateKoszulBasis I).equivFun.apply_symm_apply c) s
  refine ⟨y, ?_, ?_⟩
  · rw [mem_coordinateKoszulPiece]
    intro s
    rw [hy]
    exact hc s
  · apply (coordinateKoszulBasis J).repr.injective
    ext s
    rw [coordinateKoszulMap_repr, hy, hmap]

def coordinateKoszulScalar (I : Ideal (PolynomialRing n K)) (f : PolynomialRing n K) :
    Module.End K (CoordinateKoszulCarrier I) :=
  ((Ideal.Quotient.mk I f) •
    (LinearMap.id : Module.End (PolynomialRing n K ⧸ I) (CoordinateKoszulCarrier I))).restrictScalars K

@[simp] theorem coordinateKoszulScalar_apply (I : Ideal (PolynomialRing n K))
    (f : PolynomialRing n K) (z : CoordinateKoszulCarrier I) :
    coordinateKoszulScalar I f z = Ideal.Quotient.mk I f • z := rfl

theorem coordinateKoszulScalar_injective (I : Ideal (PolynomialRing n K))
    (f : PolynomialRing n K)
    (hf : Function.Injective (fun c : PolynomialRing n K ⧸ I => Ideal.Quotient.mk I f * c)) :
    Function.Injective (coordinateKoszulScalar I f) := by
  intro z w hzw
  apply (coordinateKoszulBasis I).repr.injective
  ext s
  apply hf
  have h := congrArg (fun x => (coordinateKoszulBasis I).repr x s) hzw
  simpa only [coordinateKoszulScalar_apply, map_smul, Finsupp.smul_apply, smul_eq_mul] using h

theorem coordinateKoszulScalar_mem (I : Ideal (PolynomialRing n K))
    {d : ℕ} {f : PolynomialRing n K} (hf : f.IsHomogeneous d)
    {i a : ℤ} {z : CoordinateKoszulCarrier I} (hz : z ∈ coordinateKoszulPiece I i a) :
    coordinateKoszulScalar I f z ∈ coordinateKoszulPiece I i (a + d) := by
  rw [mem_coordinateKoszulPiece]
  intro s
  have hs := (mem_coordinateKoszulPiece I i a z).mp hz s
  simp only [coordinateKoszulScalar_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  by_cases hsi : (s.card : ℤ) = i
  · rw [if_pos hsi] at hs ⊢
    simpa only [add_comm] using
      quotientIntegerPiece_mul I (quotientIntegerPiece_mk I hf) hs
  · rw [if_neg hsi] at hs ⊢
    rw [show (coordinateKoszulBasis I).repr z s = 0 from hs, mul_zero]
    exact Submodule.zero_mem _

theorem coordinateKoszulMap_scalar_adjoin (I : Ideal (PolynomialRing n K))
    (f : PolynomialRing n K) (z : CoordinateKoszulCarrier I) :
    coordinateKoszulMap (show I ≤ adjoinHomogeneousElement I f from le_sup_left)
      (coordinateKoszulScalar I f z) = 0 := by
  rw [coordinateKoszulScalar_apply, coordinateKoszulMap_smul,
    Ideal.Quotient.factorₐ_apply_mk]
  have hmem : f ∈ adjoinHomogeneousElement I f := by
    apply (show Ideal.span ({f} : Set (PolynomialRing n K)) ≤
      adjoinHomogeneousElement I f from le_sup_right)
    exact Ideal.subset_span (Set.mem_singleton f)
  have hf : Ideal.Quotient.mk (adjoinHomogeneousElement I f) f = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rw [hf]
  exact zero_smul (PolynomialRing n K ⧸ adjoinHomogeneousElement I f)
    (coordinateKoszulMap (show I ≤ adjoinHomogeneousElement I f from le_sup_left) z)

theorem coordinateKoszulMap_adjoin_homogeneous_kernel
    (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    {d : ℕ} {f : PolynomialRing n K} (hf : f.IsHomogeneous d)
    {i a : ℤ} {z : CoordinateKoszulCarrier I} (hz : z ∈ coordinateKoszulPiece I i a)
    (hzero : coordinateKoszulMap
      (show I ≤ adjoinHomogeneousElement I f from le_sup_left) z = 0) :
    ∃ y ∈ coordinateKoszulPiece I i (a - d), coordinateKoszulScalar I f y = z := by
  have hc : ∀ s : Finset (Fin n), ∃ c : PolynomialRing n K ⧸ I,
      c ∈ (if (s.card : ℤ) = i then quotientIntegerPiece I (a - d) else ⊥) ∧
      Ideal.Quotient.mk I f * c = (coordinateKoszulBasis I).repr z s := by
    intro s
    have hs := (mem_coordinateKoszulPiece I i a z).mp hz s
    by_cases hsi : (s.card : ℤ) = i
    · rw [if_pos hsi] at hs ⊢
      have hmap := congrArg (fun x => (coordinateKoszulBasis
        (adjoinHomogeneousElement I f)).repr x s) hzero
      rw [coordinateKoszulMap_repr, map_zero, Finsupp.zero_apply] at hmap
      exact quotientIntegerPiece_adjoin_kernel I hI hf hs hmap
    · rw [if_neg hsi] at hs ⊢
      exact ⟨0, Submodule.zero_mem _,
        (mul_zero _).trans (show (coordinateKoszulBasis I).repr z s = 0 from hs).symm⟩
  choose c hc hmul using hc
  let y := (coordinateKoszulBasis I).equivFun.symm c
  have hy (s : Finset (Fin n)) : (coordinateKoszulBasis I).repr y s = c s :=
    congrFun ((coordinateKoszulBasis I).equivFun.apply_symm_apply c) s
  refine ⟨y, ?_, ?_⟩
  · rw [mem_coordinateKoszulPiece]
    intro s
    rw [hy]
    exact hc s
  · apply (coordinateKoszulBasis I).repr.injective
    ext s
    simpa only [coordinateKoszulScalar_apply, map_smul, Finsupp.smul_apply,
      smul_eq_mul, hy] using hmul s

end HigherSpecht
end
end CanonicalSource55

section CanonicalSource56
/- Source: HigherSpecht/CoordinateKoszulHomotopy.lean -/



/-!
# The actual homogeneous null-homotopy and regularity shift

Write the positive-degree homogeneous polynomial f literally as
sum X_i g_i, with each g_i homogeneous of degree deg(f)-1.  Exterior
multiplication by the coefficient vector (g_i) supplies the Koszul
null-homotopy.  Its identity and both gradings are proved from the actual
creation and contraction operators before applying cycle lifting.
-/

noncomputable section
open MvPolynomial Module Finset CliffordAlgebra
open scoped Classical

namespace HigherSpecht

variable {K : Type*} [Field K] {n : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra

def coordinateKoszulWedge (I : Ideal (PolynomialRing n K)) (j : Fin n) :
    Module.End (PolynomialRing n K ⧸ I) (CoordinateKoszulCarrier I) where
  toFun z := ExteriorAlgebra.ι (PolynomialRing n K ⧸ I)
    (Pi.basisFun (PolynomialRing n K ⧸ I) (Fin n) j) * z
  map_add' x y := mul_add _ x y
  map_smul' c z := Algebra.mul_smul_comm c _ z

set_option backward.isDefEq.respectTransparency false in
theorem coordinateKoszulWedge_basis (I : Ideal (PolynomialRing n K))
    (j : Fin n) (s : Finset (Fin n)) :
    coordinateKoszulWedge I j (coordinateKoszulBasis I s) =
      if j ∈ s then 0 else
        TauCeti.ExteriorAlgebra.basisEraseSign j (insert j s) •
          coordinateKoszulBasis I (insert j s) := by
  simpa only [coordinateKoszulWedge, coordinateKoszulBasis,
    LinearMap.coe_mk, AddHom.coe_mk] using
    TauCeti.ExteriorAlgebra.ι_mul_basis (Pi.basisFun (PolynomialRing n K ⧸ I) (Fin n)) j s

set_option backward.isDefEq.respectTransparency false in
theorem coordinateKoszulWedge_identity (I : Ideal (PolynomialRing n K))
    (j : Fin n) (z : CoordinateKoszulCarrier I) :
    coordinateKoszulDifferential I (coordinateKoszulWedge I j z) +
      coordinateKoszulWedge I j (coordinateKoszulDifferential I z) =
        Ideal.Quotient.mk I (MvPolynomial.X j) • z := by
  have h := CliffordAlgebra.contractLeft_ι_mul (d := coordinateKoszulFunctional I)
    (Pi.basisFun (PolynomialRing n K ⧸ I) (Fin n) j) z
  rw [coordinateKoszulFunctional_basis] at h
  simpa only [coordinateKoszulDifferential, LinearMap.restrictScalars_apply,
    coordinateKoszulWedge, LinearMap.coe_mk, AddHom.coe_mk] using
      (eq_sub_iff_add_eq.mp h)

def coordinateKoszulHomotopy (I : Ideal (PolynomialRing n K))
    (g : Fin n → PolynomialRing n K) : Module.End K (CoordinateKoszulCarrier I) :=
  (∑ j : Fin n, Ideal.Quotient.mk I (g j) • coordinateKoszulWedge I j).restrictScalars K

@[simp] theorem coordinateKoszulHomotopy_apply (I : Ideal (PolynomialRing n K))
    (g : Fin n → PolynomialRing n K) (z : CoordinateKoszulCarrier I) :
    coordinateKoszulHomotopy I g z =
      ∑ j : Fin n, Ideal.Quotient.mk I (g j) • coordinateKoszulWedge I j z := by
  simp only [coordinateKoszulHomotopy, LinearMap.restrictScalars_apply,
    LinearMap.sum_apply, LinearMap.smul_apply]

set_option backward.isDefEq.respectTransparency false in
theorem coordinateKoszulHomotopy_identity (I : Ideal (PolynomialRing n K))
    {f : PolynomialRing n K} {g : Fin n → PolynomialRing n K}
    (hg : (∑ j, MvPolynomial.X j * g j) = f) (z : CoordinateKoszulCarrier I) :
    coordinateKoszulDifferential I (coordinateKoszulHomotopy I g z) +
      coordinateKoszulHomotopy I g (coordinateKoszulDifferential I z) =
        coordinateKoszulScalar I f z := by
  rw [coordinateKoszulHomotopy_apply, map_sum, coordinateKoszulHomotopy_apply,
    ← Finset.sum_add_distrib]
  calc
    (∑ j, (coordinateKoszulDifferential I
        (Ideal.Quotient.mk I (g j) • coordinateKoszulWedge I j z) +
        Ideal.Quotient.mk I (g j) •
          coordinateKoszulWedge I j (coordinateKoszulDifferential I z))) =
      ∑ j, (Ideal.Quotient.mk I (g j) * Ideal.Quotient.mk I (MvPolynomial.X j)) • z := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [coordinateKoszulDifferential_smul]
        calc
          _ = Ideal.Quotient.mk I (g j) •
              (coordinateKoszulDifferential I (coordinateKoszulWedge I j z) +
                coordinateKoszulWedge I j (coordinateKoszulDifferential I z)) :=
            (smul_add (Ideal.Quotient.mk I (g j))
              (coordinateKoszulDifferential I (coordinateKoszulWedge I j z))
              (coordinateKoszulWedge I j (coordinateKoszulDifferential I z))).symm
          _ = Ideal.Quotient.mk I (g j) •
              (Ideal.Quotient.mk I (MvPolynomial.X j) • z) :=
            congrArg (fun w : CoordinateKoszulCarrier I => Ideal.Quotient.mk I (g j) • w)
              (coordinateKoszulWedge_identity I j z)
          _ = _ := smul_smul (Ideal.Quotient.mk I (g j))
            (Ideal.Quotient.mk I (MvPolynomial.X j)) z
    _ = (∑ j, Ideal.Quotient.mk I (g j) * Ideal.Quotient.mk I (MvPolynomial.X j)) • z :=
      (Finset.sum_smul (R := PolynomialRing n K ⧸ I)
        (M := CoordinateKoszulCarrier I)).symm
    _ = Ideal.Quotient.mk I f • z := by
      congr 1
      calc
        (∑ j, Ideal.Quotient.mk I (g j) * Ideal.Quotient.mk I (MvPolynomial.X j)) =
            Ideal.Quotient.mk I (∑ j, MvPolynomial.X j * g j) := by
          simp only [map_sum, map_mul, mul_comm]
        _ = Ideal.Quotient.mk I f := congrArg (Ideal.Quotient.mk I) hg
    _ = coordinateKoszulScalar I f z := rfl

set_option backward.isDefEq.respectTransparency false in
theorem coordinateKoszulHomotopy_mem (I : Ideal (PolynomialRing n K))
    {d : ℕ} (hd : 0 < d) {g : Fin n → PolynomialRing n K}
    (hg : ∀ j, (g j).IsHomogeneous (d - 1))
    {i a : ℤ} {z : CoordinateKoszulCarrier I} (hz : z ∈ coordinateKoszulPiece I i a) :
    coordinateKoszulHomotopy I g z ∈ coordinateKoszulPiece I (i + 1) (a + d - 1) := by
  apply ((coordinateKoszulPiece_le_iff I i a
    ((coordinateKoszulPiece I (i + 1) (a + d - 1)).comap
      (coordinateKoszulHomotopy I g))).mpr ?_) hz
  intro s c hsi hc
  change coordinateKoszulHomotopy I g (c • coordinateKoszulBasis I s) ∈
    coordinateKoszulPiece I (i + 1) (a + d - 1)
  rw [coordinateKoszulHomotopy_apply]
  apply (coordinateKoszulPiece I (i + 1) (a + d - 1)).sum_mem
  intro j hj
  rw [map_smul, coordinateKoszulWedge_basis]
  by_cases hjs : j ∈ s
  · rw [if_pos hjs, smul_zero, smul_zero]
    exact Submodule.zero_mem _
  · rw [if_neg hjs]
    have hdegree : (↑(insert j s).card : ℤ) = i + 1 := by
      rw [Finset.card_insert_of_notMem hjs]
      omega
    have hcc : Ideal.Quotient.mk I (g j) * c ∈
        quotientIntegerPiece I (a + d - 1) := by
      have h := quotientIntegerPiece_mul I (quotientIntegerPiece_mk I (hg j)) hc
      have hindex : ((d - 1 : ℕ) : ℤ) + a = a + (d : ℤ) - 1 := by omega
      simpa only [hindex] using h
    have hgen := coordinateKoszulPiece_generator I (insert j s) hdegree hcc
    change Ideal.Quotient.mk I (g j) • (c •
        ((TauCeti.ExteriorAlgebra.basisEraseSign j (insert j s) : ℤ) •
          coordinateKoszulBasis I (insert j s))) ∈
      coordinateKoszulPiece I (i + 1) (a + d - 1)
    have heq :=
      (smul_smul (Ideal.Quotient.mk I (g j)) c
        ((TauCeti.ExteriorAlgebra.basisEraseSign j (insert j s) : ℤ) •
          coordinateKoszulBasis I (insert j s))).trans
        (smul_comm (Ideal.Quotient.mk I (g j) * c)
          (TauCeti.ExteriorAlgebra.basisEraseSign j (insert j s) : ℤ)
          (coordinateKoszulBasis I (insert j s)))
    exact heq.symm ▸ (coordinateKoszulPiece I (i + 1) (a + d - 1)).toAddSubgroup.zsmul_mem hgen _

def regularCoordinateKoszulQuotient
    (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    {d : ℕ} {f : PolynomialRing n K} (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hregular : Function.Injective
      (fun c : PolynomialRing n K ⧸ I => Ideal.Quotient.mk I f * c)) :
    DifferentialBigrading.RegularHomogeneousQuotient
      (coordinateKoszulBigrading I)
      (coordinateKoszulBigrading (adjoinHomogeneousElement I f)) (d : ℤ) := by
  let g := Classical.choose (homogeneous_positive_eq_sum_variables hf hd)
  have hdegree := (Classical.choose_spec (homogeneous_positive_eq_sum_variables hf hd)).1
  have hsum := (Classical.choose_spec (homogeneous_positive_eq_sum_variables hf hd)).2
  exact
    { projection := coordinateKoszulMap (show I ≤ adjoinHomogeneousElement I f from le_sup_left)
      scalar := coordinateKoszulScalar I f
      homotopy := coordinateKoszulHomotopy I g
      scalar_injective := coordinateKoszulScalar_injective I f hregular
      projection_scalar := coordinateKoszulMap_scalar_adjoin I f
      projection_differential := coordinateKoszulMap_differential le_sup_left
      scalar_differential := fun z => coordinateKoszulDifferential_smul I _ z
      homotopy_identity := coordinateKoszulHomotopy_identity I hsum
      projection_mem := fun {i a z} hz =>
        coordinateKoszulMap_mem le_sup_left (i := i) (a := a) (z := z) hz
      scalar_mem := fun {i a z} hz =>
        coordinateKoszulScalar_mem I hf (i := i) (a := a) (z := z) hz
      homotopy_mem := fun {i a z} hz =>
        coordinateKoszulHomotopy_mem I hd hdegree (i := i) (a := a) (z := z) hz
      homogeneous_lift := fun {i a z} hz =>
        coordinateKoszulMap_homogeneous_lift le_sup_left (i := i) (a := a) (z := z) hz
      homogeneous_kernel := fun {i a z} hz hzero =>
        coordinateKoszulMap_adjoin_homogeneous_kernel I hI hf
          (i := i) (a := a) (z := z) hz hzero }

/-- The exact regular-element support shift in the actual coordinate
Koszul homology, for arbitrary homogeneous polynomial quotients. -/
theorem koszulRegularityLE_adjoin_iff
    (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    {d : ℕ} {f : PolynomialRing n K} (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hregular : Function.Injective
      (fun c : PolynomialRing n K ⧸ I => Ideal.Quotient.mk I f * c)) (r : ℤ) :
    KoszulRegularityLE (adjoinHomogeneousElement I f) (r + d - 1) ↔
      KoszulRegularityLE I r :=
  (regularCoordinateKoszulQuotient I hI hf hd hregular).vanishing_iff (by omega) r

theorem hasKoszulRegularity_adjoin_iff
    (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    {d : ℕ} {f : PolynomialRing n K} (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hregular : Function.Injective
      (fun c : PolynomialRing n K ⧸ I => Ideal.Quotient.mk I f * c)) (r : ℤ) :
    HasKoszulRegularity (adjoinHomogeneousElement I f) (r + d - 1) ↔
      HasKoszulRegularity I r := by
  unfold HasKoszulRegularity
  rw [koszulRegularityLE_adjoin_iff I hI hf hd hregular r]
  have hindex : (r + (d : ℤ) - 1) - 1 = (r - 1) + (d : ℤ) - 1 := by omega
  rw [hindex, koszulRegularityLE_adjoin_iff I hI hf hd hregular (r - 1)]

end HigherSpecht
end
end CanonicalSource56

section CanonicalSource57
/- Source: HigherSpecht/SpringerTopAlternants.lean -/



/-!
# The genuine top inverse-system component is an ordinary Specht module

A tabloid is encoded by the exponent vector recording the row of each
label.  Distinct tabloids give distinct monomials.  Under this injective
map a polytabloid becomes the actual product of its column Vandermondes.
The integral standard polytabloid basis therefore computes the top
inverse-system dimension in every characteristic.
-/

noncomputable section
open TauCeti TauCeti.YoungTableau MvPolynomial Finset Module
open scoped Classical

namespace HigherSpecht

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type*} [CommRing R]

def tabloidExponent {mu : YoungDiagram} (q : TableauTabloid mu) : Fin mu.card →₀ ℕ :=
  fullFillingExponent (Classical.choose (tabloid_surjective q))

@[simp] theorem tabloidExponent_tabloid {mu : YoungDiagram} (T : YoungTableau mu) :
    tabloidExponent (tabloid T) = fullFillingExponent T := by
  have h := tabloid_eq_iff_rowIndex_eq.mp
    (Classical.choose_spec (tabloid_surjective (tabloid T)))
  ext i
  simpa only [tabloidExponent, fullFillingExponent,
    Finsupp.equivFunOnFinite_symm_apply_apply, fullFillingRow, rowIndex_def] using
    congrFun h i

theorem tabloidExponent_injective (mu : YoungDiagram) :
    Function.Injective (tabloidExponent (mu := mu)) := by
  intro p q hpq
  obtain ⟨T, rfl⟩ := tabloid_surjective p
  obtain ⟨U, rfl⟩ := tabloid_surjective q
  rw [tabloidExponent_tabloid, tabloidExponent_tabloid] at hpq
  apply tabloid_eq_iff_rowIndex_eq.mpr
  funext i
  simpa only [fullFillingExponent, Finsupp.equivFunOnFinite_symm_apply_apply,
    fullFillingRow, rowIndex_def] using DFunLike.congr_fun hpq i

theorem fullFillingExponent_relabel {mu : YoungDiagram}
    (g : Equiv.Perm (Fin mu.card)) (T : YoungTableau mu) :
    fullFillingExponent (relabel g T) = permutedExponent (fullFillingExponent T) g.symm := by
  ext i
  simp only [fullFillingExponent, Finsupp.equivFunOnFinite_symm_apply_apply,
    fullFillingRow, relabel_symm_apply, permutedExponent_apply, Equiv.Perm.inv_def]

def tabloidMonomialMap (R : Type*) [CommRing R] (mu : YoungDiagram) :
    TabloidSpaceOver R mu →ₗ[R] PolynomialRing mu.card R where
  toFun v := ∑ q : TableauTabloid mu, MvPolynomial.monomial (tabloidExponent q) (v q)
  map_add' v w := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, MvPolynomial.smul_monomial, Finset.smul_sum,
      RingHom.id_apply]

@[simp] theorem tabloidMonomialMap_coefficient {mu : YoungDiagram}
    (v : TabloidSpaceOver R mu) (q : TableauTabloid mu) :
    (tabloidMonomialMap R mu v).coeff (tabloidExponent q) = v q := by
  change (∑ p : TableauTabloid mu, MvPolynomial.monomial (tabloidExponent p)
    (v p)).coeff (tabloidExponent q) = v q
  rw [MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single q]
  · simp
  · intro p hp hpq
    rw [MvPolynomial.coeff_monomial, if_neg]
    exact fun h => hpq (tabloidExponent_injective mu h)
  · simp

theorem tabloidMonomialMap_injective (R : Type*) [CommRing R] (mu : YoungDiagram) :
    Function.Injective (tabloidMonomialMap R mu) := by
  intro v w h
  funext q
  have hq := congrArg (fun p : PolynomialRing mu.card R => p.coeff (tabloidExponent q)) h
  simpa only [tabloidMonomialMap_coefficient] using hq

@[simp] theorem tabloidMonomialMap_single {mu : YoungDiagram}
    (q : TableauTabloid mu) (c : R) :
    tabloidMonomialMap R mu (Pi.single q c) = MvPolynomial.monomial (tabloidExponent q) c := by
  change (∑ p : TableauTabloid mu, MvPolynomial.monomial (tabloidExponent p)
    (Pi.single q c p)) = _
  rw [Finset.sum_eq_single q]
  · simp
  · intro p hp hpq
    simp only [Pi.single_apply, if_neg hpq, MvPolynomial.monomial_zero]
  · simp

theorem fullFillingColumn_group {mu : YoungDiagram} (T : YoungTableau mu) :
    colorPermutationGroup (fullFillingColumn T) = colSubgroup T := by
  ext g
  simp only [mem_colorPermutationGroup, mem_colSubgroup, fullFillingColumn, colIndex_def]

theorem tabloidMonomialMap_polytabloid {mu : YoungDiagram} (T : YoungTableau mu) :
    tabloidMonomialMap R mu (polytabloidOver R T) = topColumnAlternant T := by
  rw [polytabloidOver, map_sum]
  simp only [map_smul, tabloidMonomialMap_single, ← tabloid_relabel,
    tabloidExponent_tabloid, fullFillingExponent_relabel]
  rw [topColumnAlternant, ← coefficientWitness_fullFilling_eq_columnWitness T 1,
    coefficientWitness_eq_columnAlternate, fullFillingColumn_group, columnAlternate]
  apply Finset.sum_congr rfl
  intro g hg
  rw [rename_monomial_permuted]

def topAlternantSpace (R : Type*) [CommRing R] (mu : YoungDiagram) :
    Submodule R (PolynomialRing mu.card R) :=
  Submodule.span R (Set.range (topColumnAlternant (R := R) (mu := mu)))

theorem topAlternantSpace_eq_map (R : Type*) [CommRing R] (mu : YoungDiagram) :
    topAlternantSpace R mu =
      (spechtSubrepresentationOver R mu).toSubmodule.map (tabloidMonomialMap R mu) := by
  change Submodule.span R _ = (Submodule.span R _).map _
  rw [Submodule.map_span, ← Set.range_comp]
  simp only [Function.comp_def, tabloidMonomialMap_polytabloid]

def topAlternantSpechtEquiv (R : Type*) [CommRing R] (mu : YoungDiagram) :
    (spechtSubrepresentationOver R mu).toSubmodule ≃ₗ[R] topAlternantSpace R mu :=
  (Submodule.equivMapOfInjective
    (tabloidMonomialMap R mu) (tabloidMonomialMap_injective R mu)
    (spechtSubrepresentationOver R mu).toSubmodule).trans
    (LinearEquiv.ofEq _ _ (topAlternantSpace_eq_map R mu).symm)

def topAlternantBasis (R : Type*) [CommRing R] (mu : YoungDiagram) :
    Basis (StandardYoungTableau mu) R (topAlternantSpace R mu) :=
  (standardPolytabloidBasisOver R mu).map (topAlternantSpechtEquiv R mu)

theorem topAlternantSpace_le_harmonics (R : Type*) [CommRing R] (mu : YoungDiagram) :
    topAlternantSpace R mu ≤ dividedHarmonics (springerIdeal R mu) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨T, rfl⟩
  exact topColumnAlternant_mem_harmonics T

theorem topAlternantSpace_le_homogeneous (R : Type*) [CommRing R] (mu : YoungDiagram) :
    topAlternantSpace R mu ≤
      MvPolynomial.homogeneousSubmodule (Fin mu.card) R (springerTopDegree mu) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨T, rfl⟩
  exact topColumnAlternant_isHomogeneous T

theorem homogeneousComponent_top_contraction {mu : YoungDiagram}
    (T : YoungTableau mu) (a : Fin mu.card →₀ ℕ) :
    MvPolynomial.homogeneousComponent (springerTopDegree mu)
        (contractMonomial a (topColumnAlternant (R := R) T)) =
      if a = 0 then topColumnAlternant T else 0 := by
  by_cases ha : a = 0
  · simp only [ha, contractMonomial_zero, LinearMap.id_apply, if_pos rfl, ite_true,
      MvPolynomial.homogeneousComponent_eq_self (topColumnAlternant_isHomogeneous T)]
  · rw [if_neg ha]
    by_cases hdeg : springerTopDegree mu < a.degree
    · rw [contractMonomial_eq_zero_of_degree_lt (topColumnAlternant_isHomogeneous T) hdeg,
        map_zero]
    · have hpos : 0 < a.degree := Nat.pos_of_ne_zero
        (fun h => ha ((Finsupp.degree_eq_zero_iff a).mp h))
      rw [MvPolynomial.homogeneousComponent_of_mem
        (contractMonomial_isHomogeneous (topColumnAlternant_isHomogeneous T) a), if_neg]
      omega

theorem top_harmonic_iff_topAlternantSpace
    (R : Type*) [CommRing R] [Nontrivial R] (mu : YoungDiagram)
    (w : PolynomialRing mu.card R) :
    w ∈ dividedHarmonics (springerIdeal R mu) ∧ w.IsHomogeneous (springerTopDegree mu) ↔
      w ∈ topAlternantSpace R mu := by
  constructor
  · rintro ⟨hw, hdegree⟩
    have hprojection : MvPolynomial.homogeneousComponent (springerTopDegree mu) w ∈
        topAlternantSpace R mu := by
      clear hdegree
      rw [springerHarmonics_eq_topColumnContractions R mu] at hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
          obtain ⟨T, a, rfl⟩ := hw
          rw [homogeneousComponent_top_contraction]
          split_ifs
          · exact Submodule.subset_span ⟨T, rfl⟩
          · exact Submodule.zero_mem _
      | zero => simpa only [map_zero] using (topAlternantSpace R mu).zero_mem
      | add w v hw hv ihw ihv =>
          simpa only [map_add] using (topAlternantSpace R mu).add_mem ihw ihv
      | smul c w hw ih =>
          simpa only [map_smul] using (topAlternantSpace R mu).smul_mem c ih
    rwa [MvPolynomial.homogeneousComponent_eq_self hdegree] at hprojection
  · intro hw
    exact ⟨topAlternantSpace_le_harmonics R mu hw,
      topAlternantSpace_le_homogeneous R mu hw⟩

def homogeneousHarmonicTopEquiv (R : Type*) [CommRing R] [Nontrivial R]
    (mu : YoungDiagram) :
    homogeneousHarmonicSpace (springerIdeal R mu) (springerTopDegree mu) ≃ₗ[R]
      topAlternantSpace R mu where
  toFun w := ⟨w.val.val, (top_harmonic_iff_topAlternantSpace R mu _).mp
    ⟨w.val.property, w.property⟩⟩
  invFun w := ⟨⟨w.val, topAlternantSpace_le_harmonics R mu w.property⟩,
    topAlternantSpace_le_homogeneous R mu w.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_springer_top_piece (K : Type*) [Field K] (mu : YoungDiagram) :
    Module.finrank K
        (quotientHomogeneousPiece (springerIdeal K mu) (springerTopDegree mu)) =
      Fintype.card (StandardYoungTableau mu) := by
  rw [← finrank_homogeneousHarmonicSpace_eq_quotientHomogeneousPiece
    (springerIdeal K mu) (untruncatedIdeal_isHomogeneous le_rfl)
    (powerIdeal_le_springerIdeal mu) (springerTopDegree mu),
    (homogeneousHarmonicTopEquiv K mu).finrank_eq,
    Module.finrank_eq_card_basis (topAlternantBasis K mu)]

end HigherSpecht
end
end CanonicalSource57

section CanonicalSource58
/- Source: HigherSpecht/SpringerTopProjection.lean -/



/-!
# The coordinate-annihilated part of the Springer ring is its top piece

This proves the two implications using the actual perfect divided-power
pairing.  Nonconstant contractions pair trivially with an element killed
by every coordinate, while multiplication raises the degree beyond that
of every top alternant.  No characteristic-zero differentiation is used.
-/

noncomputable section
open TauCeti TauCeti.YoungTableau MvPolynomial Module
open scoped Classical

namespace HigherSpecht

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K]

theorem quotient_monomial_mul_eq_zero_of_variables
    {n : ℕ} (I : Ideal (PolynomialRing n K)) (z : PolynomialRing n K ⧸ I)
    (hz : ∀ i, Ideal.Quotient.mk I (MvPolynomial.X i) * z = 0)
    {a : Fin n →₀ ℕ} (ha : a ≠ 0) :
    Ideal.Quotient.mk I (MvPolynomial.monomial a 1) * z = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, 0 < a i := by
    by_contra h
    push_neg at h
    exact ha (Finsupp.ext (fun i => Nat.eq_zero_of_le_zero (h i)))
  have hle : Finsupp.single i 1 ≤ a := Finsupp.single_le_iff.mpr hi
  have hm : (MvPolynomial.monomial a 1 : PolynomialRing n K) =
      MvPolynomial.X i * MvPolynomial.monomial (a - Finsupp.single i 1) 1 := by
    rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, add_tsub_cancel_of_le hle]
  rw [hm, map_mul, mul_assoc, mul_left_comm _ _ z, hz i, mul_zero]

theorem dividedApolarFunctional_contract {n : ℕ}
    (w f : PolynomialRing n K) (a : Fin n →₀ ℕ) :
    dividedApolarFunctional (contractMonomial a w) f =
      dividedApolarFunctional w (MvPolynomial.monomial a 1 * f) := by
  rw [dividedApolarFunctional_mul, dividedAction_monomial, one_smul]

theorem springer_eq_zero_of_all_harmonic_pairings (mu : YoungDiagram)
    (z : SpringerRing K mu)
    (hz : ∀ w : dividedHarmonics (springerIdeal K mu),
      dividedHarmonicQuotientDual (springerIdeal K mu) w z = 0) : z = 0 := by
  apply (Module.forall_dual_apply_eq_zero_iff K z).mp
  intro L
  obtain ⟨w, rfl⟩ := (springerDividedDualEquiv K mu).surjective L
  exact hz w

theorem springer_pairing_projection_of_variables_kill
    (mu : YoungDiagram) (f : PolynomialRing mu.card K)
    (hf : ∀ i, Ideal.Quotient.mk (springerIdeal K mu) (MvPolynomial.X i) *
      Ideal.Quotient.mk (springerIdeal K mu) f = 0)
    {w : PolynomialRing mu.card K} (hw : w ∈ dividedHarmonics (springerIdeal K mu)) :
    dividedApolarFunctional w f = dividedApolarFunctional w
      (MvPolynomial.homogeneousComponent (springerTopDegree mu) f) := by
  rw [springerHarmonics_eq_topColumnContractions K mu] at hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨T, a, rfl⟩ := hw
      by_cases ha : a = 0
      · simp only [ha, contractMonomial_zero, LinearMap.id_apply]
        exact dividedApolarFunctional_eq_component (topColumnAlternant_isHomogeneous T) f
      · have hpositive : 0 < a.degree :=
          Nat.pos_of_ne_zero (fun h => ha ((Finsupp.degree_eq_zero_iff a).mp h))
        have hproduct : MvPolynomial.monomial a 1 * f ∈ springerIdeal K mu := by
          apply Ideal.Quotient.eq_zero_iff_mem.mp
          rw [map_mul]
          exact quotient_monomial_mul_eq_zero_of_variables _ _ hf ha
        rw [dividedApolarFunctional_contract, dividedApolarFunctional_contract]
        rw [(mem_dividedHarmonics_iff_apolar _ _).mp
          (topColumnAlternant_mem_harmonics T) _ hproduct]
        symm
        apply dividedApolarFunctional_eq_zero_of_degree_ne
          (topColumnAlternant_isHomogeneous T)
          ((MvPolynomial.isHomogeneous_monomial (1 : K) rfl).mul
            (MvPolynomial.homogeneousComponent_isHomogeneous _ f))
        omega
  | zero => simp only [dividedApolarFunctional, contractionCoefficient_zero, LinearMap.zero_apply]
  | add w v hw hv ihw ihv =>
      simp only [dividedApolarFunctional, contractionCoefficient_add, LinearMap.add_apply] at *
      rw [ihw, ihv]
  | smul c w hw ih =>
      simp only [dividedApolarFunctional, contractionCoefficient_smul, LinearMap.smul_apply] at *
      rw [ih]

theorem springer_top_projection_of_variables_kill (mu : YoungDiagram)
    (z : SpringerRing K mu)
    (hz : ∀ i, Ideal.Quotient.mk (springerIdeal K mu) (MvPolynomial.X i) * z = 0) :
    quotientHomogeneousProjection (springerIdeal K mu)
      (untruncatedIdeal_isHomogeneous le_rfl) (springerTopDegree mu) z = z := by
  refine Submodule.Quotient.induction_on _ z ?_ hz
  intro f hf
  apply sub_eq_zero.mp
  apply springer_eq_zero_of_all_harmonic_pairings mu
  intro w
  rw [map_sub]
  change dividedApolarFunctional w.val
      (MvPolynomial.homogeneousComponent (springerTopDegree mu) f) -
    dividedApolarFunctional w.val f = 0
  exact sub_eq_zero.mpr (springer_pairing_projection_of_variables_kill mu f hf w.property).symm

theorem springer_variables_kill_homogeneous_top (mu : YoungDiagram)
    {f : PolynomialRing mu.card K} (hf : f.IsHomogeneous (springerTopDegree mu))
    (i : Fin mu.card) :
    Ideal.Quotient.mk (springerIdeal K mu) (MvPolynomial.X i) *
      Ideal.Quotient.mk (springerIdeal K mu) f = 0 := by
  rw [← map_mul]
  apply springer_eq_zero_of_all_harmonic_pairings mu
  rintro ⟨w, hw⟩
  change dividedApolarFunctional w (MvPolynomial.X i * f) = 0
  rw [springerHarmonics_eq_topColumnContractions K mu] at hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨T, a, rfl⟩ := hw
      rw [dividedApolarFunctional_contract]
      apply dividedApolarFunctional_eq_zero_of_degree_ne
        (topColumnAlternant_isHomogeneous T)
        ((MvPolynomial.isHomogeneous_monomial (1 : K) rfl).mul
          ((MvPolynomial.isHomogeneous_X K i).mul hf))
      omega
  | zero => simp only [dividedApolarFunctional, contractionCoefficient_zero, LinearMap.zero_apply]
  | add w v hw hv ihw ihv =>
      simp only [dividedApolarFunctional, contractionCoefficient_add,
        LinearMap.add_apply] at ihw ihv ⊢
      rw [ihw, ihv, add_zero]
  | smul c w hw ih =>
      simp only [dividedApolarFunctional, contractionCoefficient_smul,
        LinearMap.smul_apply] at ih ⊢
      rw [ih, smul_zero]

theorem springer_variables_kill_iff_mem_top_piece (mu : YoungDiagram)
    (z : SpringerRing K mu) :
    (∀ i, Ideal.Quotient.mk (springerIdeal K mu) (MvPolynomial.X i) * z = 0) ↔
      z ∈ quotientHomogeneousPiece (springerIdeal K mu) (springerTopDegree mu) := by
  constructor
  · intro hz
    rw [← quotientHomogeneousProjection_range (springerIdeal K mu)
      (untruncatedIdeal_isHomogeneous le_rfl) (springerTopDegree mu)]
    exact ⟨z, springer_top_projection_of_variables_kill mu z hz⟩
  · rintro ⟨f, hf, rfl⟩ i
    exact springer_variables_kill_homogeneous_top mu hf i

theorem springer_homogeneous_eq_zero_of_top_lt (mu : YoungDiagram)
    {d : ℕ} {f : PolynomialRing mu.card K} (hf : f.IsHomogeneous d)
    (hd : springerTopDegree mu < d) :
    Ideal.Quotient.mk (springerIdeal K mu) f = 0 := by
  apply springer_eq_zero_of_all_harmonic_pairings mu
  rintro ⟨w, hw⟩
  change dividedApolarFunctional w f = 0
  rw [springerHarmonics_eq_topColumnContractions K mu] at hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨T, a, rfl⟩ := hw
      rw [dividedApolarFunctional_contract]
      apply dividedApolarFunctional_eq_zero_of_degree_ne
        (topColumnAlternant_isHomogeneous T)
        ((MvPolynomial.isHomogeneous_monomial (1 : K) rfl).mul hf)
      omega
  | zero => simp only [dividedApolarFunctional, contractionCoefficient_zero, LinearMap.zero_apply]
  | add w v hw hv ihw ihv =>
      simp only [dividedApolarFunctional, contractionCoefficient_add,
        LinearMap.add_apply] at ihw ihv ⊢
      rw [ihw, ihv, add_zero]
  | smul c w hw ih =>
      simp only [dividedApolarFunctional, contractionCoefficient_smul,
        LinearMap.smul_apply] at ih ⊢
      rw [ih, smul_zero]

theorem springer_homogeneousPiece_eq_bot_of_top_lt (mu : YoungDiagram)
    {d : ℕ} (hd : springerTopDegree mu < d) :
    quotientHomogeneousPiece (springerIdeal K mu) d = ⊥ := by
  apply le_antisymm
  · rintro z ⟨f, hf, rfl⟩
    exact springer_homogeneous_eq_zero_of_top_lt mu hf hd
  · exact bot_le

end HigherSpecht
end
end CanonicalSource58

section CanonicalSource59
/- Source: HigherSpecht/QuotientSocle.lean -/



/-!
# The actual socle of a quotient with nilpotent coordinates

The socle here is the supremum of all simple submodules.  Nilpotence of
the coordinate classes forces them to annihilate every simple submodule.
Conversely, on a vector killed by the coordinates, every polynomial acts
through its constant term.  The cyclic module generated by a nonzero such
vector is therefore a one-dimensional vector space and is simple.

No homogeneity, finite-dimensionality, characteristic restriction, or
chosen basis is assumed in this bridge.
-/

noncomputable section

open MvPolynomial Module
open scoped Classical

namespace HigherSpecht

variable {K : Type*} [Field K] {n : ℕ}

/-- The submodule literally killed by each variable class. -/
def quotientVariableAnnihilator (I : Ideal (PolynomialRing n K)) :
    Submodule (PolynomialRing n K ⧸ I) (PolynomialRing n K ⧸ I) where
  carrier := {z | ∀ i : Fin n, Ideal.Quotient.mk I (MvPolynomial.X i) * z = 0}
  zero_mem' := fun _ => mul_zero _
  add_mem' hx hy i := by rw [mul_add, hx i, hy i, add_zero]
  smul_mem' a z hz i := by
    change Ideal.Quotient.mk I (MvPolynomial.X i) * (a * z) = 0
    rw [mul_left_comm, hz i, mul_zero]

@[simp] theorem mem_quotientVariableAnnihilator
    (I : Ideal (PolynomialRing n K)) (z : PolynomialRing n K ⧸ I) :
    z ∈ quotientVariableAnnihilator I ↔
      ∀ i : Fin n, Ideal.Quotient.mk I (MvPolynomial.X i) * z = 0 := Iff.rfl

theorem quotient_mul_eq_constant_smul_of_variables_annihilate
    (I : Ideal (PolynomialRing n K)) {z : PolynomialRing n K ⧸ I}
    (hz : z ∈ quotientVariableAnnihilator I) (p : PolynomialRing n K) :
    Ideal.Quotient.mk I p * z = MvPolynomial.constantCoeff p • z := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    simp only [MvPolynomial.constantCoeff_C]
    rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
    exact (Algebra.smul_def c z).symm
  | add p q hp hq =>
    rw [map_add, add_mul, hp, hq, map_add, add_smul]
  | mul_X p i hp =>
    rw [map_mul, mul_assoc, hz i, mul_zero, map_mul,
      MvPolynomial.constantCoeff_X, mul_zero, zero_smul]

theorem quotient_span_eq_scalar_line_of_variables_annihilate
    (I : Ideal (PolynomialRing n K)) {z : PolynomialRing n K ⧸ I}
    (hz : z ∈ quotientVariableAnnihilator I)
    {w : PolynomialRing n K ⧸ I}
    (hw : w ∈ Submodule.span (PolynomialRing n K ⧸ I) {z}) :
    ∃ c : K, c • z = w := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hw
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨MvPolynomial.constantCoeff p,
    (quotient_mul_eq_constant_smul_of_variables_annihilate I hz p).symm.trans ha⟩

theorem quotient_cyclic_isSimple_of_variables_annihilate
    (I : Ideal (PolynomialRing n K)) {z : PolynomialRing n K ⧸ I}
    (hz : z ∈ quotientVariableAnnihilator I) (hz0 : z ≠ 0) :
    IsSimpleModule (PolynomialRing n K ⧸ I)
      (Submodule.span (PolynomialRing n K ⧸ I) {z}) := by
  let Q := PolynomialRing n K ⧸ I
  let N := Submodule.span Q {z}
  letI : Nontrivial N := Submodule.nontrivial_span_singleton hz0
  apply isSimpleModule_iff_toSpanSingleton_surjective.mpr
  refine ⟨inferInstance, ?_⟩
  intro v hv w
  obtain ⟨c, hc⟩ := quotient_span_eq_scalar_line_of_variables_annihilate I hz v.property
  obtain ⟨d, hd⟩ := quotient_span_eq_scalar_line_of_variables_annihilate I hz w.property
  have hc0 : c ≠ 0 := by
    intro h
    apply hv
    apply Subtype.ext
    change v.val = (0 : Q)
    simpa only [h, zero_smul] using hc.symm
  refine ⟨algebraMap K Q (d / c), ?_⟩
  apply Subtype.ext
  change algebraMap K Q (d / c) * v.val = w.val
  calc
    algebraMap K Q (d / c) * v.val = (d / c) • v.val :=
      (Algebra.smul_def (d / c) v.val).symm
    _ = (d / c) • (c • z) := congrArg (fun w : Q => (d / c) • w) hc.symm
    _ = d • z := by rw [smul_smul, div_mul_cancel₀ d hc0]
    _ = w.val := hd

/-- Nilpotence kills the action on the actual semisimple socle; the
reverse inclusion is established by actual simple cyclic submodules. -/
theorem quotient_socle_eq_variableAnnihilator
    (I : Ideal (PolynomialRing n K))
    (hX : ∀ i : Fin n, IsNilpotent (Ideal.Quotient.mk I (MvPolynomial.X i))) :
    TauCeti.socle (PolynomialRing n K ⧸ I) (PolynomialRing n K ⧸ I) =
      quotientVariableAnnihilator I := by
  let Q := PolynomialRing n K ⧸ I
  apply le_antisymm
  · intro z hz i
    obtain ⟨d, hd⟩ := hX i
    have hmem : Ideal.Quotient.mk I (MvPolynomial.X i) ∈
        Module.annihilator Q (TauCeti.socle Q Q) := by
      apply IsSemisimpleModule.annihilator_isRadical (TauCeti.socle Q Q) Q
      exact ⟨d, by rw [hd]; exact Ideal.zero_mem _⟩
    have h := Module.mem_annihilator.mp hmem (⟨z, hz⟩ : TauCeti.socle Q Q)
    exact congrArg Subtype.val h
  · intro z hz
    by_cases hz0 : z = 0
    · exact hz0.symm ▸ Submodule.zero_mem _
    · exact TauCeti.le_socle
        (quotient_cyclic_isSimple_of_variables_annihilate I hz hz0)
          (Submodule.mem_span_singleton_self z)

theorem quotient_socle_restrictScalars_eq_variableAnnihilator
    (I : Ideal (PolynomialRing n K))
    (hX : ∀ i : Fin n, IsNilpotent (Ideal.Quotient.mk I (MvPolynomial.X i))) :
    (TauCeti.socle (PolynomialRing n K ⧸ I) (PolynomialRing n K ⧸ I)).restrictScalars K =
      (quotientVariableAnnihilator I).restrictScalars K := by
  rw [quotient_socle_eq_variableAnnihilator I hX]

end HigherSpecht
end
end CanonicalSource59

section CanonicalSource60
/- Source: HigherSpecht/SpringerSocle.lean -/



/-!
# The actual Springer socle over every coefficient field

The invariant is `TauCeti.socle`, the supremum of simple submodules of
the actual Springer quotient.  It is identified with the actual image
of the homogeneous polynomials of degree n(mu), and its dimension is the
number of standard tableaux of shape mu.  This includes the empty
diagram and uses no restriction on the characteristic.
-/

noncomputable section
open TauCeti Module MvPolynomial
open scoped Classical

namespace HigherSpecht

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K]

abbrev springerSocle (mu : YoungDiagram) : Submodule K (SpringerRing K mu) :=
  (TauCeti.socle (SpringerRing K mu) (SpringerRing K mu)).restrictScalars K

theorem springer_socle_eq_top_piece (mu : YoungDiagram) :
    springerSocle K mu =
      quotientHomogeneousPiece (springerIdeal K mu) (springerTopDegree mu) := by
  rw [springerSocle, quotient_socle_restrictScalars_eq_variableAnnihilator
    (springerIdeal K mu)
    (fun i => ⟨mu.card, springer_coordinate_pow_card_eq_zero mu i⟩)]
  ext z
  exact springer_variables_kill_iff_mem_top_piece mu z

theorem springer_socle_finrank (mu : YoungDiagram) :
    Module.finrank K (springerSocle K mu) =
      Fintype.card (StandardYoungTableau mu) := by
  rw [springer_socle_eq_top_piece, finrank_springer_top_piece]

theorem springer_socle_disjoint_other_degree (mu : YoungDiagram)
    {d : ℕ} (hd : d ≠ springerTopDegree mu) :
    Disjoint (springerSocle K mu) (quotientHomogeneousPiece (springerIdeal K mu) d) := by
  rw [springer_socle_eq_top_piece]
  exact quotientHomogeneousPiece_disjoint (springerIdeal K mu)
    (untruncatedIdeal_isHomogeneous le_rfl) hd.symm

theorem springer_socle_finrank_pos (mu : YoungDiagram) :
    0 < Module.finrank K (springerSocle K mu) := by
  rw [springer_socle_finrank]
  exact Fintype.card_pos

theorem springer_top_piece_ne_bot (mu : YoungDiagram) :
    quotientHomogeneousPiece (springerIdeal K mu) (springerTopDegree mu) ≠ ⊥ := by
  rw [← springer_socle_eq_top_piece]
  intro h
  have hp := springer_socle_finrank_pos K mu
  rw [h, finrank_bot] at hp
  exact (lt_irrefl 0) hp

/-- The exact Artinian socle assertion used in Corollary 7.6. The first
component identifies the actual submodule, and the second gives its type. -/
theorem springer_socle_concentrated_and_type (mu : YoungDiagram) :
    springerSocle K mu =
        quotientHomogeneousPiece (springerIdeal K mu) (springerTopDegree mu) ∧
      Module.finrank K (springerSocle K mu) = Fintype.card (StandardYoungTableau mu) :=
  ⟨springer_socle_eq_top_piece K mu, springer_socle_finrank K mu⟩

end HigherSpecht
end
end CanonicalSource60

section CanonicalSource61
/- Source: HigherSpecht/CoordinateKoszulArtinian.lean -/



/-!
# Artinian regularity from the actual coordinate Koszul complex

The upper bound uses the vanishing of the actual coefficient pieces.  For
sharpness, a nonzero top-degree element is multiplied by the top exterior
basis vector.  It is a cycle because all variables kill it, and it cannot
be a boundary because the next exterior degree is zero.  Thus no Hilbert
series formula is used as a definition of regularity.
-/

noncomputable section
open MvPolynomial Module Finset
open scoped Classical

namespace HigherSpecht

variable {K : Type*} [Field K] {n : ℕ}

theorem coordinateKoszulPiece_eq_bot_of_coefficient_zero
    (I : Ideal (PolynomialRing n K)) (i a : ℤ)
    (hzero : quotientIntegerPiece I a = ⊥) :
    coordinateKoszulPiece I i a = ⊥ := by
  apply le_antisymm
  · intro z hz
    change z = 0
    apply (coordinateKoszulBasis I).repr.injective
    ext s
    have hc := (mem_coordinateKoszulPiece I i a z).mp hz s
    simpa only [hzero, ite_self, Submodule.mem_bot, map_zero, Finsupp.zero_apply] using hc
  · exact bot_le

theorem coordinateKoszulPiece_eq_bot_of_exterior_gt
    (I : Ideal (PolynomialRing n K)) {i : ℤ} (hi : (n : ℤ) < i) (a : ℤ) :
    coordinateKoszulPiece I i a = ⊥ := by
  apply le_antisymm
  · intro z hz
    change z = 0
    apply (coordinateKoszulBasis I).repr.injective
    ext s
    have hs : s.card ≤ n := by simpa only [Fintype.card_fin] using s.card_le_univ
    have hsi : (s.card : ℤ) ≠ i := by omega
    have hc := (mem_coordinateKoszulPiece I i a z).mp hz s
    simpa only [if_neg hsi, Submodule.mem_bot, map_zero, Finsupp.zero_apply] using hc
  · exact bot_le

theorem coordinateKoszul_top_smul_ne_zero
    (I : Ideal (PolynomialRing n K)) {z : PolynomialRing n K ⧸ I} (hz : z ≠ 0) :
    z • coordinateKoszulBasis I Finset.univ ≠ 0 := by
  intro h
  have hc := congrArg (fun x => (coordinateKoszulBasis I).repr x Finset.univ) h
  apply hz
  simpa only [map_smul, Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_eq_same, smul_eq_mul, mul_one, map_zero, Finsupp.zero_apply] using hc

theorem coordinateKoszul_top_smul_cycle
    (I : Ideal (PolynomialRing n K)) {z : PolynomialRing n K ⧸ I}
    (hz : ∀ j : Fin n, Ideal.Quotient.mk I (MvPolynomial.X j) * z = 0) :
    coordinateKoszulDifferential I (z • coordinateKoszulBasis I Finset.univ) = 0 := by
  rw [coordinateKoszulDifferential_smul, coordinateKoszulDifferential_basis]
  refine (Finset.smul_sum (r := z) (s := Finset.univ)
    (f := fun j : Fin n => if j ∈ Finset.univ then
      Ideal.Quotient.mk I (MvPolynomial.X j) •
        (TauCeti.ExteriorAlgebra.basisEraseSign j Finset.univ •
          coordinateKoszulBasis I (Finset.univ.erase j))
      else 0)).trans ?_
  apply Finset.sum_eq_zero
  intro j hj
  rw [if_pos (Finset.mem_univ j)]
  let w : CoordinateKoszulCarrier I :=
    TauCeti.ExteriorAlgebra.basisEraseSign j Finset.univ •
      coordinateKoszulBasis I (Finset.univ.erase j)
  have hm : z * Ideal.Quotient.mk I (MvPolynomial.X j) = 0 :=
    (mul_comm z _).trans (hz j)
  exact (smul_smul z (Ideal.Quotient.mk I (MvPolynomial.X j)) w).trans
    ((congrArg (fun c : PolynomialRing n K ⧸ I => c • w) hm).trans
      (zero_smul (PolynomialRing n K ⧸ I) w))

theorem quotient_top_piece_variables_kill
    (I : Ideal (PolynomialRing n K)) {D : ℕ}
    (hvan : quotientHomogeneousPiece I (D + 1) = ⊥)
    {z : PolynomialRing n K ⧸ I} (hz : z ∈ quotientHomogeneousPiece I D)
    (j : Fin n) : Ideal.Quotient.mk I (MvPolynomial.X j) * z = 0 := by
  have hz' : z ∈ quotientIntegerPiece I (D : ℤ) := by
    simpa only [quotientIntegerPiece_nat] using hz
  have hm := quotientIntegerPiece_mul I
    (quotientIntegerPiece_mk I (MvPolynomial.isHomogeneous_X K j)) hz'
  have hdegree : (1 : ℤ) + D = ((D + 1 : ℕ) : ℤ) := by omega
  rw [Nat.cast_one, hdegree, quotientIntegerPiece_nat, hvan] at hm
  exact hm

/-- A finite graded quotient has regularity equal to its actual last
nonzero coefficient degree.  The statement makes both finiteness and
nonvanishing explicit and derives the Koszul-homology invariant. -/
theorem hasKoszulRegularity_of_top_piece
    (I : Ideal (PolynomialRing n K)) (D : ℕ)
    (hvan : ∀ d : ℕ, D < d → quotientHomogeneousPiece I d = ⊥)
    (htop : quotientHomogeneousPiece I D ≠ ⊥) :
    HasKoszulRegularity I (D : ℤ) := by
  constructor
  · intro i a x hx ha hcycle
    have ha0 : 0 ≤ a := by omega
    have hDa : D < a.toNat := by omega
    have hcoeff : quotientIntegerPiece I a = ⊥ := by
      rw [quotientIntegerPiece, if_pos ha0, hvan a.toNat hDa]
    have hp := coordinateKoszulPiece_eq_bot_of_coefficient_zero I i a hcoeff
    have hx0 : x = 0 := by
      change x ∈ coordinateKoszulPiece I i a at hx
      simpa only [hp, Submodule.mem_bot] using hx
    exact ⟨0, Submodule.zero_mem _, (map_zero _).trans hx0.symm⟩
  · intro hbound
    obtain ⟨z, hz, hzne⟩ := (quotientHomogeneousPiece I D).ne_bot_iff.mp htop
    let x : CoordinateKoszulCarrier I := z • coordinateKoszulBasis I Finset.univ
    have hx : x ∈ coordinateKoszulPiece I (n : ℤ) (D : ℤ) := by
      apply coordinateKoszulPiece_generator I Finset.univ
      · simp only [Finset.card_univ, Fintype.card_fin]
      · simpa only [quotientIntegerPiece_nat] using hz
    have hcycle : coordinateKoszulDifferential I x = 0 :=
      coordinateKoszul_top_smul_cycle I
        (quotient_top_piece_variables_kill I (hvan (D + 1) (Nat.lt_succ_self D)) hz)
    obtain ⟨y, hy, hdy⟩ := hbound (n : ℤ) (D : ℤ) x hx (by omega) hcycle
    have hpiece : coordinateKoszulPiece I ((n : ℤ) + 1) ((D : ℤ) - 1) = ⊥ :=
      coordinateKoszulPiece_eq_bot_of_exterior_gt I (by omega) _
    have hy0 : y = 0 := by
      change y ∈ coordinateKoszulPiece I ((n : ℤ) + 1) ((D : ℤ) - 1) at hy
      simpa only [hpiece, Submodule.mem_bot] using hy
    have hx0 : x = 0 := by simpa only [hy0, map_zero] using hdy.symm
    exact coordinateKoszul_top_smul_ne_zero I hzne hx0

/-- The Springer regularity computation, for every coefficient field. -/
theorem springer_hasKoszulRegularity (K : Type*) [Field K] (mu : YoungDiagram) :
    HasKoszulRegularity (springerIdeal K mu) (springerTopDegree mu : ℤ) :=
  hasKoszulRegularity_of_top_piece (springerIdeal K mu) (springerTopDegree mu)
    (fun d hd => springer_homogeneousPiece_eq_bot_of_top_lt mu hd)
    (springer_top_piece_ne_bot K mu)

end HigherSpecht
end
end CanonicalSource61

section CanonicalSource62
/- Source: HigherSpecht/RegularQuotientSequence.lean -/



/-! Transport of a literal weakly regular sequence in a quotient to
regular multiplication in the original polynomial quotient with the
previous generators adjoined.  The proof uses the actual ideal image;
no quotient tower identification is assumed. -/

noncomputable section

namespace HigherSpecht

open RingTheory.Sequence

variable {R : Type*} [CommRing R]

theorem regular_quotient_sup_of_regular_image
    (I J : Ideal R) (f : R)
    (hregular : IsSMulRegular ((R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I))
      (Ideal.Quotient.mk I f)) :
    Function.Injective (fun x : R ⧸ (I ⊔ J) => Ideal.Quotient.mk (I ⊔ J) f * x) := by
  change IsSMulRegular (R ⧸ (I ⊔ J)) (Ideal.Quotient.mk (I ⊔ J) f)
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro x hx
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hfp : f * p ∈ I ⊔ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_mul, smul_eq_mul] using hx
  have hfp' : Ideal.Quotient.mk I f * Ideal.Quotient.mk I p ∈
      J.map (Ideal.Quotient.mk I) := by
    rw [← map_mul, Ideal.mem_quotient_iff_mem_sup]
    simpa only [sup_comm] using hfp
  have hp' : Ideal.Quotient.mk I p ∈ J.map (Ideal.Quotient.mk I) :=
    mem_of_isSMulRegular_quotient_of_smul_mem hregular hfp'
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  simpa only [Ideal.mem_quotient_iff_mem_sup, sup_comm] using hp'

theorem regular_adjoined_prefix_of_weaklyRegular
    (I : Ideal R) (fs : List R)
    (hregular : IsWeaklyRegular (R ⧸ I) (fs.map (Ideal.Quotient.mk I)))
    (i : ℕ) (hi : i < fs.length) :
    Function.Injective (fun x : R ⧸ (I ⊔ Ideal.ofList (fs.take i)) =>
      Ideal.Quotient.mk (I ⊔ Ideal.ofList (fs.take i)) fs[i] * x) := by
  have h := hregular.regular_mod_prev i (by simpa only [List.length_map] using hi)
  have htop : (Ideal.ofList ((fs.take i).map (Ideal.Quotient.mk I)) •
      (⊤ : Submodule (R ⧸ I) (R ⧸ I))) =
      Ideal.ofList ((fs.take i).map (Ideal.Quotient.mk I)) := by
    change Ideal.ofList ((fs.take i).map (Ideal.Quotient.mk I)) * ⊤ = _
    exact Ideal.mul_top _
  have hprev : (Ideal.ofList ((fs.map (Ideal.Quotient.mk I)).take i) •
      (⊤ : Submodule (R ⧸ I) (R ⧸ I))) =
      (Ideal.ofList (fs.take i)).map (Ideal.Quotient.mk I) := by
    rw [← List.map_take, htop, Ideal.map_ofList]
  rw [hprev] at h
  simp only [List.getElem_map] at h
  exact regular_quotient_sup_of_regular_image I (Ideal.ofList (fs.take i)) fs[i] h

end HigherSpecht
end
end CanonicalSource62

section CanonicalSource63
/- Source: HigherSpecht/KoszulParameterShift.lean -/



/-!
# The elementary-parameter regularity shift

The parameter sequence is literally e_1,...,e_m.  Its contribution to
regularity is the sum 0+1+...+(m-1), derived one regular element at a time
from the actual coordinate Koszul complex.  The final application supplies
regularity of this sequence from the already constructed parameter basis.
-/

noncomputable section
open TauCeti Module MvPolynomial Finset RingTheory.Sequence
open scoped Classical

namespace HigherSpecht

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K] {n : ℕ}

def elementaryParameterSequence (K : Type*) [CommRing K] (n m : ℕ) :
    List (PolynomialRing n K) :=
  List.ofFn (fun i : Fin m => MvPolynomial.esymm (Fin n) K (i.val + 1))

@[simp] theorem elementaryParameterSequence_length (K : Type*) [CommRing K] (n m : ℕ) :
    (elementaryParameterSequence K n m).length = m := List.length_ofFn

theorem elementaryParameterSequence_getElem (m i : ℕ) (hi : i < m) :
    (elementaryParameterSequence K n m)[i]'(by
      simpa only [elementaryParameterSequence_length] using hi) =
      MvPolynomial.esymm (Fin n) K (i + 1) := by
  simp only [elementaryParameterSequence, List.getElem_ofFn]

theorem elementaryParameterSequence_prefix_ideal (m j : ℕ) (hj : j ≤ m) :
    Ideal.ofList ((elementaryParameterSequence K n m).take j) =
      elementaryParameterIdeal K n j := by
  rw [elementaryParameterSequence, ← Fin.ofFn_take_eq_take_ofFn hj]
  unfold Ideal.ofList elementaryParameterIdeal
  congr 1
  ext p
  simp only [List.mem_ofFn, Fin.take_apply, Fin.val_castLE, Set.mem_range,
    Set.mem_setOf_eq]

@[simp] theorem elementaryParameterIdeal_zero : elementaryParameterIdeal K n 0 = ⊥ := by
  simp only [elementaryParameterIdeal, Set.range_eq_empty, Ideal.span_empty]

theorem elementaryParameterIdeal_succ (j : ℕ) :
    elementaryParameterIdeal K n (j + 1) =
      elementaryParameterIdeal K n j ⊔ Ideal.span {MvPolynomial.esymm (Fin n) K (j + 1)} := by
  rw [← elementaryParameterSequence_prefix_ideal (K := K) (n := n) (j + 1) (j + 1) le_rfl,
    List.take_succ_eq_append_getElem (by simp), Ideal.ofList_append,
    Ideal.ofList_singleton,
    elementaryParameterSequence_prefix_ideal (j + 1) j (Nat.le_succ j),
    elementaryParameterSequence_getElem (j + 1) j (Nat.lt_succ_self j)]

theorem elementaryParameterIdeal_isHomogeneous (j : ℕ) :
    (elementaryParameterIdeal K n j).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) K) := by
  apply Ideal.homogeneous_span
  rintro p ⟨i, rfl⟩
  exact ⟨i.val + 1, elementaryOn_isHomogeneous Finset.univ (i.val + 1)⟩

def elementaryKoszulShift (m : ℕ) : ℤ := ∑ i ∈ Finset.range m, (i : ℤ)

@[simp] theorem elementaryKoszulShift_zero : elementaryKoszulShift 0 = 0 := by
  simp only [elementaryKoszulShift, Finset.range_zero, Finset.sum_empty]

theorem elementaryKoszulShift_succ (m : ℕ) :
    elementaryKoszulShift (m + 1) = elementaryKoszulShift m + m := by
  exact Finset.sum_range_succ (fun i : ℕ => (i : ℤ)) m

/-- This intermediate statement has the genuine weak regularity of the
literal quotient classes as a hypothesis.  The final untruncated theorem
below instantiates it from flatness over the actual parameter ring. -/
theorem hasKoszulRegularity_elementary_prefix_iff
    (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (m : ℕ)
    (hregular : IsWeaklyRegular (PolynomialRing n K ⧸ I)
      ((elementaryParameterSequence K n m).map (Ideal.Quotient.mk I)))
    (j : ℕ) (hj : j ≤ m) (r : ℤ) :
    HasKoszulRegularity (I ⊔ elementaryParameterIdeal K n j)
        (r + elementaryKoszulShift j) ↔ HasKoszulRegularity I r := by
  induction j with
  | zero => simp only [elementaryParameterIdeal_zero, sup_bot_eq,
      elementaryKoszulShift_zero, add_zero]
  | succ j ih =>
    have hjm : j < m := by omega
    have hreg := regular_adjoined_prefix_of_weaklyRegular I
      (elementaryParameterSequence K n m) hregular j (by simpa using hjm)
    rw [elementaryParameterSequence_prefix_ideal m j (by omega),
      elementaryParameterSequence_getElem m j hjm] at hreg
    have hstep := hasKoszulRegularity_adjoin_iff
      (I ⊔ elementaryParameterIdeal K n j)
      (hI.sup (elementaryParameterIdeal_isHomogeneous j))
      (elementaryOn_isHomogeneous (R := K) (Finset.univ : Finset (Fin n)) (j + 1))
      (Nat.zero_lt_succ j) hreg (r + elementaryKoszulShift j)
    have hideal : adjoinHomogeneousElement (I ⊔ elementaryParameterIdeal K n j)
        (MvPolynomial.esymm (Fin n) K (j + 1)) =
        I ⊔ elementaryParameterIdeal K n (j + 1) := by
      rw [elementaryParameterIdeal_succ, adjoinHomogeneousElement, sup_assoc]
    rw [elementaryOn_univ, hideal] at hstep
    have hshift : r + elementaryKoszulShift j + (j + 1 : ℕ) - 1 =
        r + elementaryKoszulShift (j + 1) := by
      rw [elementaryKoszulShift_succ]
      omega
    rw [hshift] at hstep
    exact hstep.trans (ih (by omega))

theorem springerTopDegree_adjoinOnes (lam : YoungDiagram) (m : ℕ) :
    (springerTopDegree (adjoinOnes lam m) : ℤ) =
      (springerTopDegree lam : ℤ) + (m : ℤ) * lam.colLen 0 + elementaryKoszulShift m := by
  rw [springerTopDegree_eq_sum_rows, adjoinOnes_colLen_zero, Finset.sum_range_add]
  have hfirst : (∑ r ∈ Finset.range (lam.colLen 0),
      r * (adjoinOnes lam m).rowLen r) = springerTopDegree lam := by
    rw [springerTopDegree_eq_sum_rows]
    apply Finset.sum_congr rfl
    intro r hr
    rw [adjoinOnes_rowLen, if_pos (Finset.mem_range.mp hr)]
  have hlast : (∑ r ∈ Finset.range m,
      (lam.colLen 0 + r) * (adjoinOnes lam m).rowLen (lam.colLen 0 + r)) =
      m * lam.colLen 0 + ∑ r ∈ Finset.range m, r := by
    calc
      _ = ∑ r ∈ Finset.range m, (lam.colLen 0 + r) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [adjoinOnes_rowLen, if_neg (by omega),
          if_pos (by have := Finset.mem_range.mp hr; omega), mul_one]
      _ = _ := by rw [Finset.sum_add_distrib]; simp only [Finset.sum_const,
          Finset.card_range, smul_eq_mul]
  rw [hfirst, hlast]
  push_cast
  simp only [elementaryKoszulShift, add_assoc]

end HigherSpecht
end
end CanonicalSource63

section CanonicalSource64
/- Source: HigherSpecht/PolynomialVariableSequence.lean -/



/-!
# The literal variable sequence of a polynomial ring

The prefix ideal is exactly the ideal generated by the earlier variables.
That ideal is prime over a domain, and the next variable survives evaluation
which kills the prefix. This proves weak regularity of the actual ordered
list, so the finite free parameter algebra can inherit it by flat base change.
-/

noncomputable section

open RingTheory.Sequence

namespace HigherSpecht

variable (R : Type*) [CommRing R]

theorem variablePrefixIdeal {m i : ℕ} (hi : i ≤ m) :
    Ideal.ofList ((List.ofFn (MvPolynomial.X : Fin m → MvPolynomial (Fin m) R)).take i) =
      Ideal.span (MvPolynomial.X '' {j : Fin m | j.val < i}) := by
  classical
  rw [← Fin.ofFn_take_eq_take_ofFn hi, Ideal.ofList_ofFn]
  congr 1
  ext f
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨Fin.castLE hi j, j.isLt, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    refine ⟨⟨j.val, hj⟩, ?_⟩
    change MvPolynomial.X (Fin.castLE hi ⟨j.val, hj⟩) = MvPolynomial.X j
    congr 1

theorem polynomialVariables_isWeaklyRegular [IsDomain R] (m : ℕ) :
    IsWeaklyRegular (MvPolynomial (Fin m) R)
      (List.ofFn (MvPolynomial.X : Fin m → MvPolynomial (Fin m) R)) := by
  classical
  constructor
  intro i hi
  have him : i < m := by simpa only [List.length_ofFn] using hi
  let j : Fin m := ⟨i, him⟩
  let I : Ideal (MvPolynomial (Fin m) R) :=
    Ideal.ofList ((List.ofFn (MvPolynomial.X : Fin m → MvPolynomial (Fin m) R)).take i)
  have hI : I = Ideal.span (MvPolynomial.X '' {t : Fin m | t.val < i}) :=
    variablePrefixIdeal R him.le
  have hprime : I.IsPrime := hI.symm ▸ MvPolynomial.span_X_image_isPrime _
  have hnot : MvPolynomial.X j ∉ I := by
    rw [hI, MvPolynomial.span_X_image_eq_ker_aeval_ite_mem]
    intro hx
    have hz : (MvPolynomial.X j : MvPolynomial (Fin m) R) = 0 := by
      simpa [RingHom.mem_ker, j] using hx
    exact MvPolynomial.X_ne_zero j hz
  have htop : (I • (⊤ : Submodule (MvPolynomial (Fin m) R)
      (MvPolynomial (Fin m) R))) = I := by
    change I * ⊤ = I
    exact Ideal.mul_top I
  rw [List.getElem_ofFn]
  change IsSMulRegular (MvPolynomial (Fin m) R ⧸
    (I • (⊤ : Submodule (MvPolynomial (Fin m) R) (MvPolynomial (Fin m) R))))
      (MvPolynomial.X j : MvPolynomial (Fin m) R)
  rw [htop, isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro f hf
  exact (hprime.mem_or_mem (show MvPolynomial.X j * f ∈ I from hf)).resolve_left hnot

end HigherSpecht
end
end CanonicalSource64

section CanonicalSource65
/- Source: HigherSpecht/UntruncatedRegularity.lean -/



/-!
# Corollary 7.5 over every field

Regularity is computed using actual homogeneous coordinate Koszul
homology.  The elementary parameters are proved regular by flat base
change from the literal variables in their polynomial parameter ring.
The actual zero-parameter fiber is the Springer quotient for the diagram
obtained by adjoining one-box rows.  Its top exterior cycle establishes
the sharp bound, and the explicit regular-element null-homotopies remove
the parameter degree shifts.
-/

noncomputable section
open TauCeti Module MvPolynomial RingTheory.Sequence
open scoped Classical

namespace HigherSpecht

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K]

theorem untruncated_elementarySequence_isWeaklyRegular
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    IsWeaklyRegular (UntruncatedRing K n lam)
      ((elementaryParameterSequence K n (n - lam.card)).map
        (Ideal.Quotient.mk (untruncatedIdeal K n lam))) := by
  letI := untruncated_parameter_flat_allCoefficients K n lam hk
  have h := (polynomialVariables_isWeaklyRegular K (n - lam.card)).of_flat
    (S := UntruncatedRing K n lam)
  have hseq : (List.ofFn (MvPolynomial.X :
      Fin (n - lam.card) → ElementaryParameterRing K n lam)).map
        (algebraMap (ElementaryParameterRing K n lam) (UntruncatedRing K n lam)) =
      (elementaryParameterSequence K n (n - lam.card)).map
        (Ideal.Quotient.mk (untruncatedIdeal K n lam)) := by
    simp only [elementaryParameterSequence, List.map_ofFn]
    apply congrArg (fun F : Fin (n - lam.card) → UntruncatedRing K n lam => List.ofFn F)
    funext i
    simp only [Function.comp_apply, untruncatedParameter_algebraMap, MvPolynomial.aeval_X,
      elementaryParameterClasses]
  exact (congrArg (IsWeaklyRegular (UntruncatedRing K n lam)) hseq).mp h

/-- The manuscript's exact value, with no restriction on characteristic
and with the empty partition and zero-parameter cases included. -/
theorem corollary_7_5_regularity
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    HasKoszulRegularity (untruncatedIdeal K n lam)
      ((springerTopDegree lam : ℤ) + (n - lam.card : ℕ) * (lam.colLen 0 : ℤ)) := by
  let m := n - lam.card
  let mu := adjoinOnes lam m
  have hcard : mu.card = n := by
    simp only [mu, adjoinOnes_card, m, Nat.add_sub_of_le hk]
  have hfiber : untruncatedIdeal K n mu =
      untruncatedIdeal K n lam ⊔ elementaryParameterIdeal K n m := by
    have h := specialFiberIdeal_eq (R := K) lam m
    have hsize : lam.card + m = n := Nat.add_sub_of_le hk
    rwa [hsize] at h
  have hartin : HasKoszulRegularity (untruncatedIdeal K n mu)
      (springerTopDegree mu : ℤ) := by
    have hfull (N : ℕ) (hN : mu.card = N) :
        HasKoszulRegularity (untruncatedIdeal K N mu) (springerTopDegree mu : ℤ) := by
      subst N
      exact springer_hasKoszulRegularity K mu
    exact hfull n hcard
  have hshift := hasKoszulRegularity_elementary_prefix_iff
    (untruncatedIdeal K n lam) (untruncatedIdeal_isHomogeneous hk) m
    (untruncated_elementarySequence_isWeaklyRegular K n lam hk) m le_rfl
    ((springerTopDegree lam : ℤ) + (m : ℤ) * lam.colLen 0)
  apply hshift.mp
  rw [← hfiber]
  convert hartin using 1
  exact (springerTopDegree_adjoinOnes lam m).symm

variable {K}

/-- The sharpness condition in the regularity predicate is equivalent to
an actual nonzero Koszul homology component at the printed degree. -/
theorem hasKoszulRegularity_iff_homology_support
    {n : ℕ} (I : Ideal (PolynomialRing n K)) (r : ℤ) :
    HasKoszulRegularity I r ↔
      (∀ i a, r < a → Subsingleton (CoordinateKoszulHomology I i a)) ∧
        ∃ i, ¬ Subsingleton (CoordinateKoszulHomology I i r) := by
  rw [HasKoszulRegularity, koszulRegularityLE_iff_homology,
    koszulRegularityLE_iff_homology]
  constructor
  · rintro ⟨hupper, hlower⟩
    push_neg at hlower
    obtain ⟨i, a, ha, hnonzero⟩ := hlower
    have hnot : ¬ Subsingleton (CoordinateKoszulHomology I i a) :=
      not_subsingleton_iff_nontrivial.mpr hnonzero
    have har : a ≤ r := by
      by_contra! h
      exact hnot (hupper i a h)
    have heq : a = r := by omega
    exact ⟨hupper, i, heq ▸ hnot⟩
  · rintro ⟨hupper, i, hnonzero⟩
    exact ⟨hupper, fun h => hnonzero (h i r (by omega))⟩

theorem corollary_7_5_koszul_homology
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    let r : ℤ := (springerTopDegree lam : ℤ) +
      (n - lam.card : ℕ) * (lam.colLen 0 : ℤ)
    (∀ i a, r < a →
      Subsingleton (CoordinateKoszulHomology (untruncatedIdeal K n lam) i a)) ∧
      ∃ i, ¬ Subsingleton (CoordinateKoszulHomology (untruncatedIdeal K n lam) i r) :=
  (hasKoszulRegularity_iff_homology_support _ _).mp
    (corollary_7_5_regularity K n lam hk)

end HigherSpecht
end
end CanonicalSource65

section CanonicalSource66
/- Source: HigherSpecht/NullHomotopyHomologySplit.lean -/



/-!
# Homology after quotienting by an injective null-homotopic scalar

This is a direct cycle calculation.  It proves the actual homology
splitting of a short exact sequence whose first map is injective and
null-homotopic.  In the application the maps are multiplication by a
regular polynomial, coefficient reduction, and exterior multiplication
by a vector expressing that polynomial in the coordinate ideal.
-/

noncomputable section

open Module

namespace HigherSpecht

structure DifferentialGrading (K V : Type*) [Field K] [AddCommGroup V] [Module K V] where
  piece : ℤ → Submodule K V
  differential : Module.End K V
  square_zero : ∀ z, differential (differential z) = 0
  differential_mem : ∀ {i z}, z ∈ piece i → differential z ∈ piece (i - 1)

namespace DifferentialGrading

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

def cycles (D : DifferentialGrading K V) (i : ℤ) : Submodule K V :=
  D.piece i ⊓ LinearMap.ker D.differential

def boundaries (D : DifferentialGrading K V) (i : ℤ) : Submodule K V :=
  (D.piece (i + 1)).map D.differential

theorem boundaries_le_cycles (D : DifferentialGrading K V) (i : ℤ) :
    D.boundaries i ≤ D.cycles i := by
  rintro z ⟨y, hy, rfl⟩
  exact ⟨by simpa using D.differential_mem hy, D.square_zero y⟩

abbrev Homology (D : DifferentialGrading K V) (i : ℤ) :=
  D.cycles i ⧸ (D.boundaries i).comap (D.cycles i).subtype

def homologyClass (D : DifferentialGrading K V) (i : ℤ) :
    D.cycles i →ₗ[K] D.Homology i :=
  ((D.boundaries i).comap (D.cycles i).subtype).mkQ

theorem homologyClass_eq_zero_iff (D : DifferentialGrading K V) (i : ℤ)
    (z : D.cycles i) : D.homologyClass i z = 0 ↔ z.val ∈ D.boundaries i :=
  Submodule.Quotient.mk_eq_zero _

structure RegularNullHomotopyQuotient (D : DifferentialGrading K V)
    (E : DifferentialGrading K W) where
  projection : V →ₗ[K] W
  scalar : Module.End K V
  homotopy : Module.End K V
  scalar_injective : Function.Injective scalar
  projection_scalar : ∀ z, projection (scalar z) = 0
  projection_differential : ∀ z, projection (D.differential z) = E.differential (projection z)
  scalar_differential : ∀ z, scalar (D.differential z) = D.differential (scalar z)
  homotopy_identity : ∀ z, D.differential (homotopy z) + homotopy (D.differential z) = scalar z
  projection_mem : ∀ {i z}, z ∈ D.piece i → projection z ∈ E.piece i
  scalar_mem : ∀ {i z}, z ∈ D.piece i → scalar z ∈ D.piece i
  homotopy_mem : ∀ {i z}, z ∈ D.piece i → homotopy z ∈ D.piece (i + 1)
  graded_lift : ∀ {i z}, z ∈ E.piece i → ∃ y ∈ D.piece i, projection y = z
  graded_kernel : ∀ {i z}, z ∈ D.piece i → projection z = 0 →
    ∃ y ∈ D.piece i, scalar y = z

namespace RegularNullHomotopyQuotient

variable {D : DifferentialGrading K V} {E : DifferentialGrading K W}
  (Q : RegularNullHomotopyQuotient D E)

def mapCycles (i : ℤ) : D.cycles i →ₗ[K] E.cycles i :=
  Q.projection.restrict (fun z hz =>
    ⟨Q.projection_mem hz.1, by
      change E.differential (Q.projection z) = 0
      rw [← Q.projection_differential, hz.2, map_zero]⟩)

def shiftedCycles (i : ℤ) : D.cycles (i - 1) →ₗ[K] E.cycles i :=
  (Q.projection.comp Q.homotopy).restrict (fun z hz => by
    refine ⟨?_, ?_⟩
    · simpa using Q.projection_mem (Q.homotopy_mem hz.1)
    · change E.differential (Q.projection (Q.homotopy z)) = 0
      rw [← Q.projection_differential]
      have hid := Q.homotopy_identity z
      rw [hz.2, map_zero, add_zero] at hid
      rw [hid, Q.projection_scalar])

theorem mapCycles_boundary (i : ℤ)
    (z : D.cycles i) (hz : z.val ∈ D.boundaries i) :
    (Q.mapCycles i z).val ∈ E.boundaries i := by
  obtain ⟨y, hy, hdy⟩ := hz
  refine ⟨Q.projection y, Q.projection_mem hy, ?_⟩
  change E.differential (Q.projection y) = Q.projection z.val
  rw [← Q.projection_differential, hdy]

theorem shiftedCycles_boundary (i : ℤ)
    (z : D.cycles (i - 1)) (hz : z.val ∈ D.boundaries (i - 1)) :
    (Q.shiftedCycles i z).val ∈ E.boundaries i := by
  obtain ⟨y, hy, hdy⟩ := hz
  have hy' : y ∈ D.piece i := by simpa using hy
  refine ⟨-Q.projection (Q.homotopy y),
    (E.piece (i + 1)).neg_mem (Q.projection_mem (Q.homotopy_mem hy')), ?_⟩
  change E.differential (-Q.projection (Q.homotopy y)) =
    Q.projection (Q.homotopy z.val)
  have hid := congrArg Q.projection (Q.homotopy_identity y)
  rw [map_add, Q.projection_scalar, hdy] at hid
  rw [map_neg, ← Q.projection_differential]
  rw [eq_neg_of_add_eq_zero_left hid, neg_neg]

def homologyMap (i : ℤ) : D.Homology i →ₗ[K] E.Homology i :=
  ((D.boundaries i).comap (D.cycles i).subtype).liftQ
    ((E.homologyClass i).comp (Q.mapCycles i)) (by
      intro z hz
      exact (E.homologyClass_eq_zero_iff i _).mpr (Q.mapCycles_boundary i z hz))

def shiftedHomologyMap (i : ℤ) : D.Homology (i - 1) →ₗ[K] E.Homology i :=
  ((D.boundaries (i - 1)).comap (D.cycles (i - 1)).subtype).liftQ
    ((E.homologyClass i).comp (Q.shiftedCycles i)) (by
      intro z hz
      exact (E.homologyClass_eq_zero_iff i _).mpr (Q.shiftedCycles_boundary i z hz))

def homologySum (i : ℤ) :
    D.Homology i × D.Homology (i - 1) →ₗ[K] E.Homology i :=
  (Q.homologyMap i).coprod (Q.shiftedHomologyMap i)

@[simp] theorem homologySum_classes (i : ℤ)
    (a : D.cycles i) (b : D.cycles (i - 1)) :
    Q.homologySum i (D.homologyClass i a, D.homologyClass (i - 1) b) =
      E.homologyClass i (Q.mapCycles i a + Q.shiftedCycles i b) := by
  simp only [homologySum, LinearMap.coprod_apply, homologyMap, shiftedHomologyMap,
    homologyClass, Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.comp_apply, map_add]

theorem homologySum_injective (i : ℤ) : Function.Injective (Q.homologySum i) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  rintro ⟨a, b⟩ hab
  obtain ⟨a, rfl⟩ := ((D.boundaries i).comap (D.cycles i).subtype).mkQ_surjective a
  obtain ⟨b, rfl⟩ := ((D.boundaries (i - 1)).comap
    (D.cycles (i - 1)).subtype).mkQ_surjective b
  change Q.homologySum i (D.homologyClass i a, D.homologyClass (i - 1) b) = 0 at hab
  rw [Q.homologySum_classes] at hab
  obtain ⟨w, hw, hdw⟩ := (E.homologyClass_eq_zero_iff i _).mp hab
  obtain ⟨c, hc, hpc⟩ := Q.graded_lift hw
  have hker : Q.projection (a.val + Q.homotopy b.val - D.differential c) = 0 := by
    rw [map_sub, map_add, Q.projection_differential, hpc]
    change Q.projection a.val + Q.projection (Q.homotopy b.val) - E.differential w = 0
    exact sub_eq_zero.mpr hdw.symm
  have hp : a.val + Q.homotopy b.val - D.differential c ∈ D.piece i := by
    exact (D.piece i).sub_mem ((D.piece i).add_mem a.property.1
      (by simpa using Q.homotopy_mem b.property.1))
      (by simpa using D.differential_mem hc)
  obtain ⟨v, hv, hfv⟩ := Q.graded_kernel hp hker
  have hb : b.val = D.differential v := by
    apply Q.scalar_injective
    rw [Q.scalar_differential, hfv, map_sub, map_add,
      a.property.2, D.square_zero c, zero_add, sub_zero]
    have h := Q.homotopy_identity b.val
    rw [b.property.2, map_zero, add_zero] at h
    exact h.symm
  have ha : a.val = D.differential (c + Q.homotopy v) := by
    have h := Q.homotopy_identity v
    rw [← hb] at h
    rw [map_add]
    apply add_right_cancel (b := Q.homotopy b.val)
    calc
      a.val + Q.homotopy b.val = Q.scalar v + D.differential c :=
        (eq_sub_iff_add_eq.mp hfv).symm
      _ = (D.differential (Q.homotopy v) + Q.homotopy b.val) +
          D.differential c := by rw [h]
      _ = (D.differential c + D.differential (Q.homotopy v)) +
          Q.homotopy b.val := by abel
  apply Prod.ext
  · apply (D.homologyClass_eq_zero_iff i a).mpr
    refine ⟨c + Q.homotopy v,
      (D.piece (i + 1)).add_mem hc (Q.homotopy_mem hv), ha.symm⟩
  · apply (D.homologyClass_eq_zero_iff (i - 1) b).mpr
    refine ⟨v, ?_, hb.symm⟩
    simpa using hv

theorem homologySum_surjective (i : ℤ) : Function.Surjective (Q.homologySum i) := by
  intro z
  obtain ⟨z, rfl⟩ := ((E.boundaries i).comap (E.cycles i).subtype).mkQ_surjective z
  obtain ⟨y, hy, hpy⟩ := Q.graded_lift z.property.1
  have hpdy : Q.projection (D.differential y) = 0 := by
    rw [Q.projection_differential, hpy]
    exact z.property.2
  obtain ⟨b, hb, hfb⟩ := Q.graded_kernel (D.differential_mem hy) hpdy
  have hdb : D.differential b = 0 := by
    apply Q.scalar_injective
    rw [Q.scalar_differential, hfb, D.square_zero, map_zero]
  let bc : D.cycles (i - 1) := ⟨b, hb, hdb⟩
  have hda : D.differential (y - Q.homotopy b) = 0 := by
    rw [map_sub]
    have h := Q.homotopy_identity b
    rw [hdb, map_zero, add_zero, hfb] at h
    rw [h, sub_self]
  let ac : D.cycles i := ⟨y - Q.homotopy b,
    (D.piece i).sub_mem hy (by simpa using Q.homotopy_mem hb), hda⟩
  refine ⟨(D.homologyClass i ac, D.homologyClass (i - 1) bc), ?_⟩
  rw [Q.homologySum_classes]
  congr 1
  apply Subtype.ext
  change Q.projection (y - Q.homotopy b) + Q.projection (Q.homotopy b) = z.val
  rw [map_sub, sub_add_cancel, hpy]

/-- The genuine homology splitting.  It is induced by `(a,b) ↦ π(a+h(b))`,
and its inverse exists by the explicit cycle and boundary calculations. -/
def homologyEquiv (i : ℤ) :
    (D.Homology i × D.Homology (i - 1)) ≃ₗ[K] E.Homology i :=
  LinearEquiv.ofBijective (Q.homologySum i)
    ⟨Q.homologySum_injective i, Q.homologySum_surjective i⟩

theorem finrank_homology (Q : RegularNullHomotopyQuotient D E) (i : ℤ)
    [FiniteDimensional K (D.Homology i)] [FiniteDimensional K (D.Homology (i - 1))] :
    Module.finrank K (E.Homology i) =
      Module.finrank K (D.Homology i) + Module.finrank K (D.Homology (i - 1)) := by
  exact (LinearEquiv.finrank_eq (homologyEquiv Q i)).symm.trans
    (Module.finrank_prod (R := K) (M := D.Homology i) (M' := D.Homology (i - 1)))

end RegularNullHomotopyQuotient
end DifferentialGrading
end HigherSpecht
end
end CanonicalSource66

section CanonicalSource67
/- Source: HigherSpecht/CoordinateKoszulHomological.lean -/



/-!
# The ungraded coefficient version of the actual coordinate Koszul complex

Only exterior degree is retained here.  Thus the later complete-intersection
argument permits an arbitrary regular defining sequence; its elements need
not be homogeneous.  The differential and coefficient-reduction maps are
the same literal maps used in the separately graded regularity argument.
-/

noncomputable section

open MvPolynomial Module Finset CliffordAlgebra
open scoped Classical

namespace HigherSpecht

variable {K : Type*} [Field K] {n : ℕ}

def coordinateHomologicalPiece (I : Ideal (PolynomialRing n K)) (i : ℤ) :
    Submodule K (CoordinateKoszulCarrier I) :=
  ⨅ s : Finset (Fin n),
    if (s.card : ℤ) = i then ⊤ else
      LinearMap.ker (((coordinateKoszulBasis I).coord s).restrictScalars K)

theorem mem_coordinateHomologicalPiece (I : Ideal (PolynomialRing n K))
    (i : ℤ) (z : CoordinateKoszulCarrier I) :
    z ∈ coordinateHomologicalPiece I i ↔
      ∀ s : Finset (Fin n), (s.card : ℤ) ≠ i → (coordinateKoszulBasis I).repr z s = 0 := by
  simp only [coordinateHomologicalPiece, Submodule.mem_iInf]
  apply forall_congr'
  intro s
  by_cases hs : (s.card : ℤ) = i
  · simp only [hs, if_true, Submodule.mem_top, ne_eq, not_true_eq_false, false_implies]
  · simp only [if_neg hs, if_false, LinearMap.mem_ker, LinearMap.restrictScalars_apply,
      Basis.coord_apply, ne_eq, hs, not_false_eq_true, true_implies]

theorem coordinateHomologicalPiece_generator (I : Ideal (PolynomialRing n K))
    {i : ℤ} (s : Finset (Fin n)) (hs : (s.card : ℤ) = i)
    (c : PolynomialRing n K ⧸ I) :
    c • coordinateKoszulBasis I s ∈ coordinateHomologicalPiece I i := by
  rw [mem_coordinateHomologicalPiece]
  intro t ht
  have hst : s ≠ t := by rintro rfl; exact ht hs
  simp only [map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
    if_neg hst, smul_eq_mul, mul_zero]

theorem coordinateHomologicalPiece_le_iff (I : Ideal (PolynomialRing n K))
    (i : ℤ) (P : Submodule K (CoordinateKoszulCarrier I)) :
    coordinateHomologicalPiece I i ≤ P ↔
      ∀ (s : Finset (Fin n)) (c : PolynomialRing n K ⧸ I),
        (s.card : ℤ) = i → c • coordinateKoszulBasis I s ∈ P := by
  constructor
  · intro h s c hs
    exact h (coordinateHomologicalPiece_generator I s hs c)
  · intro h z hz
    rw [← (coordinateKoszulBasis I).sum_repr z]
    apply P.sum_mem
    intro s hs
    by_cases hsi : (s.card : ℤ) = i
    · exact h s _ hsi
    · rw [(mem_coordinateHomologicalPiece I i z).mp hz s hsi]
      exact (zero_smul (PolynomialRing n K ⧸ I) (coordinateKoszulBasis I s)).symm ▸
        P.zero_mem

set_option backward.isDefEq.respectTransparency false in
theorem coordinateHomologicalDifferential_mem (I : Ideal (PolynomialRing n K))
    {i : ℤ} {z : CoordinateKoszulCarrier I}
    (hz : z ∈ coordinateHomologicalPiece I i) :
    coordinateKoszulDifferential I z ∈ coordinateHomologicalPiece I (i - 1) := by
  apply ((coordinateHomologicalPiece_le_iff I i
    ((coordinateHomologicalPiece I (i - 1)).comap (coordinateKoszulDifferential I))).mpr ?_) hz
  intro s c hsi
  change coordinateKoszulDifferential I (c • coordinateKoszulBasis I s) ∈
    coordinateHomologicalPiece I (i - 1)
  rw [coordinateKoszulDifferential_smul, coordinateKoszulDifferential_basis]
  rw [Finset.smul_sum (M := PolynomialRing n K ⧸ I)
    (N := CoordinateKoszulCarrier I) (r := c)]
  apply (coordinateHomologicalPiece I (i - 1)).sum_mem
  intro j hj
  by_cases hjs : j ∈ s
  · rw [if_pos hjs]
    have hdegree : (↑(s.erase j).card : ℤ) = i - 1 := by
      rw [Finset.card_erase_of_mem hjs]
      have hpos := Finset.card_pos.mpr ⟨j, hjs⟩
      omega
    have h := coordinateHomologicalPiece_generator I (s.erase j) hdegree
      (c * Ideal.Quotient.mk I (X j))
    change c • (Ideal.Quotient.mk I (X j) •
        ((TauCeti.ExteriorAlgebra.basisEraseSign j s : ℤ) •
          coordinateKoszulBasis I (s.erase j))) ∈ coordinateHomologicalPiece I (i - 1)
    have heq :=
      (smul_smul c (Ideal.Quotient.mk I (X j))
        ((TauCeti.ExteriorAlgebra.basisEraseSign j s : ℤ) •
          coordinateKoszulBasis I (s.erase j))).trans
        (smul_comm (c * Ideal.Quotient.mk I (X j))
          (TauCeti.ExteriorAlgebra.basisEraseSign j s : ℤ)
          (coordinateKoszulBasis I (s.erase j)))
    exact heq.symm ▸ (coordinateHomologicalPiece I (i - 1)).toAddSubgroup.zsmul_mem h _
  · rw [if_neg hjs, smul_zero]
    exact Submodule.zero_mem _

def coordinateDifferentialGrading (I : Ideal (PolynomialRing n K)) :
    DifferentialGrading K (CoordinateKoszulCarrier I) where
  piece := coordinateHomologicalPiece I
  differential := coordinateKoszulDifferential I
  square_zero := coordinateKoszulDifferential_square I
  differential_mem := coordinateHomologicalDifferential_mem I

abbrev TotalCoordinateKoszulHomology (I : Ideal (PolynomialRing n K)) (i : ℤ) :=
  (coordinateDifferentialGrading I).Homology i

theorem coordinateHomologicalScalar_mem (I : Ideal (PolynomialRing n K))
    (f : PolynomialRing n K) {i : ℤ} {z : CoordinateKoszulCarrier I}
    (hz : z ∈ coordinateHomologicalPiece I i) :
    coordinateKoszulScalar I f z ∈ coordinateHomologicalPiece I i := by
  rw [mem_coordinateHomologicalPiece]
  intro s hs
  simp only [coordinateKoszulScalar_apply, map_smul, Finsupp.smul_apply,
    (mem_coordinateHomologicalPiece I i z).mp hz s hs, smul_zero]

theorem coordinateHomologicalMap_mem {I J : Ideal (PolynomialRing n K)}
    (hIJ : I ≤ J) {i : ℤ} {z : CoordinateKoszulCarrier I}
    (hz : z ∈ coordinateHomologicalPiece I i) :
    coordinateKoszulMap hIJ z ∈ coordinateHomologicalPiece J i := by
  rw [mem_coordinateHomologicalPiece]
  intro s hs
  rw [coordinateKoszulMap_repr, (mem_coordinateHomologicalPiece I i z).mp hz s hs, map_zero]

set_option backward.isDefEq.respectTransparency false in
theorem coordinateHomologicalHomotopy_mem (I : Ideal (PolynomialRing n K))
    (g : Fin n → PolynomialRing n K) {i : ℤ} {z : CoordinateKoszulCarrier I}
    (hz : z ∈ coordinateHomologicalPiece I i) :
    coordinateKoszulHomotopy I g z ∈ coordinateHomologicalPiece I (i + 1) := by
  apply ((coordinateHomologicalPiece_le_iff I i
    ((coordinateHomologicalPiece I (i + 1)).comap (coordinateKoszulHomotopy I g))).mpr ?_) hz
  intro s c hsi
  change coordinateKoszulHomotopy I g (c • coordinateKoszulBasis I s) ∈
    coordinateHomologicalPiece I (i + 1)
  rw [coordinateKoszulHomotopy_apply]
  apply (coordinateHomologicalPiece I (i + 1)).sum_mem
  intro j hj
  rw [map_smul, coordinateKoszulWedge_basis]
  by_cases hjs : j ∈ s
  · rw [if_pos hjs, smul_zero, smul_zero]
    exact Submodule.zero_mem _
  · rw [if_neg hjs]
    have hdegree : (↑(insert j s).card : ℤ) = i + 1 := by
      rw [Finset.card_insert_of_notMem hjs]
      omega
    have h := coordinateHomologicalPiece_generator I (insert j s) hdegree
      (Ideal.Quotient.mk I (g j) * c)
    change Ideal.Quotient.mk I (g j) • (c •
        ((TauCeti.ExteriorAlgebra.basisEraseSign j (insert j s) : ℤ) •
          coordinateKoszulBasis I (insert j s))) ∈ coordinateHomologicalPiece I (i + 1)
    have heq :=
      (smul_smul (Ideal.Quotient.mk I (g j)) c
        ((TauCeti.ExteriorAlgebra.basisEraseSign j (insert j s) : ℤ) •
          coordinateKoszulBasis I (insert j s))).trans
        (smul_comm (Ideal.Quotient.mk I (g j) * c)
          (TauCeti.ExteriorAlgebra.basisEraseSign j (insert j s) : ℤ)
          (coordinateKoszulBasis I (insert j s)))
    exact heq.symm ▸ (coordinateHomologicalPiece I (i + 1)).toAddSubgroup.zsmul_mem h _

theorem coordinateHomologicalMap_lift {I J : Ideal (PolynomialRing n K)}
    (hIJ : I ≤ J) {i : ℤ} {z : CoordinateKoszulCarrier J}
    (hz : z ∈ coordinateHomologicalPiece J i) :
    ∃ y ∈ coordinateHomologicalPiece I i, coordinateKoszulMap hIJ y = z := by
  have hc : ∀ s : Finset (Fin n), ∃ c : PolynomialRing n K ⧸ I,
      ((s.card : ℤ) ≠ i → c = 0) ∧
      Ideal.Quotient.factorₐ K hIJ c = (coordinateKoszulBasis J).repr z s := by
    intro s
    by_cases hsi : (s.card : ℤ) = i
    · obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective ((coordinateKoszulBasis J).repr z s)
      refine ⟨Ideal.Quotient.mk I p, fun h => (h hsi).elim, ?_⟩
      simpa only [Ideal.Quotient.factorₐ_apply_mk] using hp
    · exact ⟨0, fun _ => rfl, (map_zero _).trans
        ((mem_coordinateHomologicalPiece J i z).mp hz s hsi).symm⟩
  choose c hc hmap using hc
  let y := (coordinateKoszulBasis I).equivFun.symm c
  have hy (s : Finset (Fin n)) : (coordinateKoszulBasis I).repr y s = c s :=
    congrFun ((coordinateKoszulBasis I).equivFun.apply_symm_apply c) s
  refine ⟨y, ?_, ?_⟩
  · rw [mem_coordinateHomologicalPiece]
    intro s hs
    rw [hy]
    exact hc s hs
  · apply (coordinateKoszulBasis J).repr.injective
    ext s
    rw [coordinateKoszulMap_repr, hy, hmap]

theorem quotient_adjoin_kernel (I : Ideal (PolynomialRing n K))
    (f : PolynomialRing n K) (x : PolynomialRing n K ⧸ I)
    (hx : Ideal.Quotient.factorₐ K (show I ≤ I ⊔ Ideal.span {f} from le_sup_left) x = 0) :
    ∃ y : PolynomialRing n K ⧸ I, Ideal.Quotient.mk I f * y = x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hp : p ∈ I ⊔ Ideal.span {f} := Ideal.Quotient.eq_zero_iff_mem.mp hx
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hp
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hv
  refine ⟨Ideal.Quotient.mk I c, ?_⟩
  have h := congrArg (Ideal.Quotient.mk I) huv
  rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hu, zero_add] at h
  rw [← map_mul, ← hc]
  exact h

theorem coordinateHomologicalMap_kernel (I : Ideal (PolynomialRing n K))
    (f : PolynomialRing n K) {i : ℤ} {z : CoordinateKoszulCarrier I}
    (hz : z ∈ coordinateHomologicalPiece I i)
    (hzero : coordinateKoszulMap (show I ≤ adjoinHomogeneousElement I f from le_sup_left) z = 0) :
    ∃ y ∈ coordinateHomologicalPiece I i, coordinateKoszulScalar I f y = z := by
  have hc : ∀ s : Finset (Fin n), ∃ c : PolynomialRing n K ⧸ I,
      ((s.card : ℤ) ≠ i → c = 0) ∧
      Ideal.Quotient.mk I f * c = (coordinateKoszulBasis I).repr z s := by
    intro s
    by_cases hsi : (s.card : ℤ) = i
    · have hmap := congrArg (fun x => (coordinateKoszulBasis
        (adjoinHomogeneousElement I f)).repr x s) hzero
      rw [coordinateKoszulMap_repr, map_zero, Finsupp.zero_apply] at hmap
      obtain ⟨c, hc⟩ := quotient_adjoin_kernel I f _ hmap
      exact ⟨c, fun h => (h hsi).elim, hc⟩
    · exact ⟨0, fun _ => rfl, (mul_zero _).trans
        ((mem_coordinateHomologicalPiece I i z).mp hz s hsi).symm⟩
  choose c hc hmul using hc
  let y := (coordinateKoszulBasis I).equivFun.symm c
  have hy (s : Finset (Fin n)) : (coordinateKoszulBasis I).repr y s = c s :=
    congrFun ((coordinateKoszulBasis I).equivFun.apply_symm_apply c) s
  refine ⟨y, ?_, ?_⟩
  · rw [mem_coordinateHomologicalPiece]
    intro s hs
    rw [hy]
    exact hc s hs
  · apply (coordinateKoszulBasis I).repr.injective
    ext s
    simpa only [coordinateKoszulScalar_apply, map_smul, Finsupp.smul_apply,
      smul_eq_mul, hy] using hmul s

theorem constantCoeff_zero_eq_sum_variables {f : PolynomialRing n K}
    (hf : constantCoeff f = 0) :
    ∃ g : Fin n → PolynomialRing n K, (∑ j, X j * g j) = f := by
  have hm : f ∈ MvPolynomial.idealOfVars (Fin n) K := by
    rw [MvPolynomial.idealOfVars, ← Set.image_univ,
      MvPolynomial.span_X_image_eq_ker_aeval_ite_mem]
    simpa only [RingHom.mem_ker, Set.compl_univ, Set.mem_empty_iff_false, if_false,
      MvPolynomial.aeval_zero', hf, map_zero]
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun (PolynomialRing n K)).mp hm
  exact ⟨g, by simpa only [smul_eq_mul, mul_comm] using hg⟩

def regularCoordinateHomologicalQuotient (I : Ideal (PolynomialRing n K))
    (f : PolynomialRing n K) (hf : constantCoeff f = 0)
    (hregular : Function.Injective
      (fun c : PolynomialRing n K ⧸ I => Ideal.Quotient.mk I f * c)) :
    DifferentialGrading.RegularNullHomotopyQuotient
      (coordinateDifferentialGrading I)
      (coordinateDifferentialGrading (adjoinHomogeneousElement I f)) := by
  let g := Classical.choose (constantCoeff_zero_eq_sum_variables hf)
  have hsum := Classical.choose_spec (constantCoeff_zero_eq_sum_variables hf)
  exact
    { projection := coordinateKoszulMap (show I ≤ adjoinHomogeneousElement I f from le_sup_left)
      scalar := coordinateKoszulScalar I f
      homotopy := coordinateKoszulHomotopy I g
      scalar_injective := coordinateKoszulScalar_injective I f hregular
      projection_scalar := coordinateKoszulMap_scalar_adjoin I f
      projection_differential := coordinateKoszulMap_differential le_sup_left
      scalar_differential := fun z => (coordinateKoszulDifferential_smul I _ z).symm
      homotopy_identity := coordinateKoszulHomotopy_identity I hsum
      projection_mem := fun {i z} hz =>
        coordinateHomologicalMap_mem le_sup_left (i := i) (z := z) hz
      scalar_mem := fun {i z} hz =>
        coordinateHomologicalScalar_mem I f (i := i) (z := z) hz
      homotopy_mem := fun {i z} hz =>
        coordinateHomologicalHomotopy_mem I g (i := i) (z := z) hz
      graded_lift := fun {i z} hz =>
        coordinateHomologicalMap_lift le_sup_left (i := i) (z := z) hz
      graded_kernel := fun {i z} hz hzero =>
        coordinateHomologicalMap_kernel I f (i := i) (z := z) hz hzero }

end HigherSpecht
end
end CanonicalSource67

section CanonicalSource68
/- Source: HigherSpecht/RegularSequencePresentation.lean -/



/-!
# Complete-intersection presentations and selected polynomial variables

The predicate in this file is the usual presentation by a regular sequence
in the stated polynomial ring.  In particular it refers to the actual
successive multiplication maps in quotient modules; no partition condition
is built into its definition.
-/

noncomputable section

open TauCeti MvPolynomial RingTheory.Sequence
open scoped Classical

namespace HigherSpecht

def IsRegularSequencePresentation {R : Type*} [CommRing R] (I : Ideal R) : Prop :=
  ∃ xs : List R, IsRegular R xs ∧ Ideal.ofList xs = I

theorem selectedVariablePrefixIdeal (R : Type*) [CommRing R]
    {n r i : ℕ} (e : Fin r ↪ Fin n) (hi : i ≤ r) :
    Ideal.ofList ((List.ofFn (fun j => (X (e j) : PolynomialRing n R))).take i) =
      Ideal.span (X '' (e '' {j : Fin r | j.val < i})) := by
  rw [← Fin.ofFn_take_eq_take_ofFn hi, Ideal.ofList_ofFn]
  congr 1
  ext f
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨e (Fin.castLE hi j), ⟨Fin.castLE hi j, j.isLt, rfl⟩, rfl⟩
  · rintro ⟨v, ⟨j, hj, rfl⟩, rfl⟩
    refine ⟨⟨j.val, hj⟩, ?_⟩
    congr 2

theorem selectedPolynomialVariables_isWeaklyRegular
    (R : Type*) [CommRing R] [IsDomain R] {n r : ℕ}
    (e : Fin r ↪ Fin n) :
    IsWeaklyRegular (PolynomialRing n R)
      (List.ofFn (fun j => (X (e j) : PolynomialRing n R))) := by
  constructor
  intro i hi
  have hir : i < r := by simpa only [List.length_ofFn] using hi
  let j : Fin r := ⟨i, hir⟩
  let I : Ideal (PolynomialRing n R) := Ideal.ofList
    ((List.ofFn (fun t => (X (e t) : PolynomialRing n R))).take i)
  have hI : I = Ideal.span (X '' (e '' {t : Fin r | t.val < i})) :=
    selectedVariablePrefixIdeal R e hir.le
  have hprime : I.IsPrime := hI.symm ▸ MvPolynomial.span_X_image_isPrime _
  have hj : e j ∉ e '' {t : Fin r | t.val < i} := by
    rintro ⟨t, ht, hte⟩
    have hti := e.injective hte
    subst t
    exact (Nat.lt_irrefl i) ht
  have hnot : (X (e j) : PolynomialRing n R) ∉ I := by
    rw [hI, MvPolynomial.span_X_image_eq_ker_aeval_ite_mem]
    intro hx
    have hz : (X (e j) : PolynomialRing n R) = 0 := by
      simpa only [RingHom.mem_ker, MvPolynomial.aeval_X,
        Set.mem_compl_iff, if_pos hj] using hx
    exact MvPolynomial.X_ne_zero (e j) hz
  have htop : (I • (⊤ : Submodule (PolynomialRing n R) (PolynomialRing n R))) = I := by
    change I * ⊤ = I
    exact Ideal.mul_top I
  rw [List.getElem_ofFn]
  change IsSMulRegular (PolynomialRing n R ⧸
    (I • (⊤ : Submodule (PolynomialRing n R) (PolynomialRing n R))))
      (X (e j) : PolynomialRing n R)
  rw [htop, isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro f hf
  exact (hprime.mem_or_mem (show X (e j) * f ∈ I from hf)).resolve_left hnot

theorem polynomialSequence_isRegular_of_constantCoeff_zero
    (R : Type*) [CommRing R] [Nontrivial R] {n : ℕ}
    (xs : List (PolynomialRing n R))
    (hreg : IsWeaklyRegular (PolynomialRing n R) xs)
    (hzero : ∀ x ∈ xs, constantCoeff x = 0) :
    IsRegular (PolynomialRing n R) xs := by
  refine ⟨hreg, ?_⟩
  have hker : Ideal.ofList xs ≤ RingHom.ker constantCoeff := by
    apply Ideal.span_le.mpr
    exact hzero
  intro htop
  have heq : (⊤ : Ideal (PolynomialRing n R)) = Ideal.ofList xs := by
    simpa only [smul_eq_mul, Ideal.mul_top] using htop
  have hmem : (1 : PolynomialRing n R) ∈ Ideal.ofList xs := by rw [← heq]; trivial
  exact one_ne_zero (by simpa only [RingHom.mem_ker, map_one] using hker hmem)

theorem selectedPolynomialVariables_isRegular
    (R : Type*) [CommRing R] [IsDomain R] {n r : ℕ}
    (e : Fin r ↪ Fin n) :
    IsRegular (PolynomialRing n R)
      (List.ofFn (fun j => (X (e j) : PolynomialRing n R))) := by
  apply polynomialSequence_isRegular_of_constantCoeff_zero R _
    (selectedPolynomialVariables_isWeaklyRegular R e)
  intro x hx
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
  exact constantCoeff_X R (e j)

theorem isWeaklyRegular_map_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (xs : List R) :
    IsWeaklyRegular R xs ↔ IsWeaklyRegular S (xs.map e) := by
  apply e.toAddEquiv.isWeaklyRegular_congr
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro r hr x
  exact e.map_mul r x

theorem untruncatedIdeal_empty (R : Type*) [CommRing R] (n : ℕ) :
    untruncatedIdeal R n ⊥ = ⊥ := by
  apply le_antisymm _ bot_le
  apply Ideal.span_le.mpr
  rintro p ⟨Y, d, hd, hcard, hthreshold, rfl⟩
  have hz : conjugateTail n ⊥ Y.card = 0 := by simp [conjugateTail]
  rw [hz, Nat.cast_zero, sub_zero] at hthreshold
  omega

def untruncatedEmptyRingEquiv (R : Type*) [CommRing R] (n : ℕ) :
    PolynomialRing n R ≃+* UntruncatedRing R n ⊥ :=
  (RingEquiv.quotientBot (PolynomialRing n R)).symm.trans
    (Ideal.quotEquivOfEq (untruncatedIdeal_empty R n).symm)

@[simp] theorem untruncatedEmptyRingEquiv_apply
    (R : Type*) [CommRing R] (n : ℕ) (p : PolynomialRing n R) :
    untruncatedEmptyRingEquiv R n p =
      Ideal.Quotient.mk (untruncatedIdeal R n ⊥) p := rfl

/-- Any selected elementary symmetric polynomials form a weakly regular
sequence, in any order without repetitions.  The proof transfers the
actual selected variable sequence through the full elementary-parameter
free algebra, then identifies the empty-partition quotient with the
original polynomial ring. -/
theorem selectedElementary_isWeaklyRegular
    (R : Type*) [CommRing R] [IsDomain R] {n r : ℕ}
    (e : Fin r ↪ Fin n) :
    IsWeaklyRegular (PolynomialRing n R)
      (List.ofFn (fun j => MvPolynomial.esymm (Fin n) R ((e j).val + 1))) := by
  let B := ElementaryParameterRing R n ⊥
  let A := UntruncatedRing R n ⊥
  let en : Fin n ≃ Fin (n - (⊥ : YoungDiagram).card) :=
    finCongr (by simp only [YoungDiagram.card, YoungDiagram.cells_bot,
      Finset.card_empty, Nat.sub_zero])
  let e' : Fin r ↪ Fin (n - (⊥ : YoungDiagram).card) := e.trans en.toEmbedding
  letI : Module.Flat B A := untruncated_parameter_flat_allCoefficients R n ⊥
    (by simp only [YoungDiagram.card, YoungDiagram.cells_bot, Finset.card_empty, Nat.zero_le])
  have hvars := selectedPolynomialVariables_isWeaklyRegular R e'
  have hbase := hvars.of_flat (S := A)
  have heq : (List.ofFn (fun j => (X (e' j) : B))).map (algebraMap B A) =
      (List.ofFn (fun j => MvPolynomial.esymm (Fin n) R ((e j).val + 1))).map
        (untruncatedEmptyRingEquiv R n) := by
    simp only [List.map_ofFn]
    congr 1
    funext j
    change algebraMap B A (X (e' j)) =
      untruncatedEmptyRingEquiv R n (MvPolynomial.esymm (Fin n) R ((e j).val + 1))
    rw [untruncatedEmptyRingEquiv_apply]
    change algebraMap (ElementaryParameterRing R n ⊥) (UntruncatedRing R n ⊥)
      (X (e' j)) = _
    rw [untruncatedParameter_algebraMap, MvPolynomial.aeval_X]
    rfl
  rw [heq] at hbase
  exact (isWeaklyRegular_map_ringEquiv (untruncatedEmptyRingEquiv R n) _).mpr hbase

theorem selectedElementary_isRegular
    (R : Type*) [CommRing R] [IsDomain R] {n r : ℕ}
    (e : Fin r ↪ Fin n) :
    IsRegular (PolynomialRing n R)
      (List.ofFn (fun j => MvPolynomial.esymm (Fin n) R ((e j).val + 1))) := by
  apply polynomialSequence_isRegular_of_constantCoeff_zero R _
    (selectedElementary_isWeaklyRegular R e)
  intro x hx
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
  exact constantCoeff_elementaryOn Finset.univ (Nat.zero_lt_succ _)

end HigherSpecht
end
end CanonicalSource68

section CanonicalSource69
/- Source: HigherSpecht/CoordinateKoszulEndpoints.lean -/



/-!
# The bottom, top and initial homology of the coordinate Koszul complex

The zeroth homology is the residue field, the top homology is the literal
coordinate annihilator, and the polynomial-ring complex is exact in
positive degree.  These identifications are proved for the actual
coefficient and exterior-basis maps used in the regular-quotient splitting.
-/

noncomputable section

open TauCeti MvPolynomial Module Finset CliffordAlgebra
open scoped Classical

namespace HigherSpecht

variable {K : Type*} [Field K] {n : ℕ}

theorem coordinateHomologicalPiece_eq_bot (I : Ideal (PolynomialRing n K))
    {i : ℤ} (hi : i < 0 ∨ (n : ℤ) < i) : coordinateHomologicalPiece I i = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro z hz
  apply (coordinateKoszulBasis I).repr.injective
  ext s
  have hs : (s.card : ℤ) ≠ i := by
    have hc : s.card ≤ n := by simpa using s.card_le_univ
    omega
  simpa only [map_zero, Finsupp.zero_apply] using
    (mem_coordinateHomologicalPiece I i z).mp hz s hs

theorem totalCoordinateKoszulHomology_subsingleton_of_outside
    (I : Ideal (PolynomialRing n K)) {i : ℤ} (hi : i < 0 ∨ (n : ℤ) < i) :
    Subsingleton (TotalCoordinateKoszulHomology I i) := by
  have hc : (coordinateDifferentialGrading I).cycles i = ⊥ := by
    unfold DifferentialGrading.cycles
    change coordinateHomologicalPiece I i ⊓ _ = _
    rw [coordinateHomologicalPiece_eq_bot I hi, bot_inf_eq]
  letI : Subsingleton ((coordinateDifferentialGrading I).cycles i) := by
    rw [hc]
    infer_instance
  infer_instance

theorem coordinateHomologicalPiece_eq_exteriorPower
    (I : Ideal (PolynomialRing n K)) (q : ℕ) :
    coordinateHomologicalPiece I (q : ℤ) =
      (ExteriorAlgebra.exteriorPower (PolynomialRing n K ⧸ I) q
        (Fin n → PolynomialRing n K ⧸ I)).restrictScalars K := by
  let A := PolynomialRing n K ⧸ I
  let b := Pi.basisFun A (Fin n)
  apply le_antisymm
  · rw [coordinateHomologicalPiece_le_iff]
    intro s c hs
    have hsq : s.card = q := by exact_mod_cast hs
    let t : Set.powersetCard (Fin n) q := ⟨s, hsq⟩
    have hmem : coordinateKoszulBasis I s ∈ ExteriorAlgebra.exteriorPower A q (Fin n → A) := by
      rw [show coordinateKoszulBasis I s =
        (b.exteriorPower q t : ExteriorAlgebra A (Fin n → A)) from
          ExteriorAlgebra.basis_eq_coe_basis b t]
      exact (b.exteriorPower q t).property
    exact (ExteriorAlgebra.exteriorPower A q (Fin n → A)).smul_mem c hmem
  · intro z hz
    let z' : ⋀[A]^q (Fin n → A) := ⟨z, hz⟩
    have hsum := congrArg Subtype.val ((b.exteriorPower q).sum_repr z')
    change z'.val ∈ coordinateHomologicalPiece I (q : ℤ)
    rw [← hsum]
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
    apply (coordinateHomologicalPiece I (q : ℤ)).sum_mem
    intro s hs
    rw [← ExteriorAlgebra.basis_eq_coe_basis b s]
    exact coordinateHomologicalPiece_generator I s.val (by exact_mod_cast s.property) _

theorem coordinateKoszulFunctional_eq_linearCombination
    (I : Ideal (PolynomialRing n K)) :
    coordinateKoszulFunctional I = Fintype.linearCombination (PolynomialRing n K ⧸ I)
      (fun j => Ideal.Quotient.mk I (X j)) := by
  apply (Pi.basisFun (PolynomialRing n K ⧸ I) (Fin n)).ext
  intro j
  rw [coordinateKoszulFunctional_basis]
  rw [Pi.basisFun_apply, Fintype.linearCombination_apply_single, one_smul]

set_option backward.isDefEq.respectTransparency false in
theorem totalCoordinateKoszulHomology_bot_succ_subsingleton (q : ℕ) :
    Subsingleton (TotalCoordinateKoszulHomology (⊥ : Ideal (PolynomialRing n K))
      ((q + 1 : ℕ) : ℤ)) := by
  let I : Ideal (PolynomialRing n K) := ⊥
  let A := PolynomialRing n K ⧸ I
  let x : Fin n → A := fun j => Ideal.Quotient.mk I (X j)
  have hvars : RingTheory.Sequence.IsWeaklyRegular A (List.ofFn x) := by
    have h := (polynomialVariables_isWeaklyRegular K n)
    have hmap := (isWeaklyRegular_map_ringEquiv
      (RingEquiv.quotientBot (PolynomialRing n K)).symm
        (List.ofFn (MvPolynomial.X : Fin n → PolynomialRing n K))).mp h
    simpa only [List.map_ofFn, Function.comp_def, RingEquiv.quotientBot_symm_mk] using hmap
  have hex := (TauCeti.koszulComplex.exactAt_succ_iff _ q).mp
    (TauCeti.koszulComplex.exactAt_of_isWeaklyRegular x hvars q)
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  intro z hz
  have hzp : z.val ∈ ExteriorAlgebra.exteriorPower A (q + 1) (Fin n → A) := by
    change z.val ∈ (ExteriorAlgebra.exteriorPower A (q + 1) (Fin n → A)).restrictScalars K
    rw [← coordinateHomologicalPiece_eq_exteriorPower I (q + 1)]
    exact z.property.1
  let z' : ⋀[A]^(q + 1) (Fin n → A) := ⟨z.val, hzp⟩
  have hdz : TauCeti.koszulDifferential (Fintype.linearCombination A x) q z' = 0 := by
    apply Subtype.ext
    rw [TauCeti.coe_koszulDifferential_apply,
      ← coordinateKoszulFunctional_eq_linearCombination I]
    exact z.property.2
  obtain ⟨y, hy⟩ := (hex z').mp hdz
  refine ⟨y.val, ?_, ?_⟩
  · change y.val ∈ coordinateHomologicalPiece I ((q + 1 : ℕ) + 1)
    rw [show ((q + 1 : ℕ) : ℤ) + 1 = ((q + 2 : ℕ) : ℤ) by omega,
      coordinateHomologicalPiece_eq_exteriorPower I (q + 2)]
    exact y.property
  · have h := congrArg Subtype.val hy
    rw [TauCeti.coe_koszulDifferential_apply,
      ← coordinateKoszulFunctional_eq_linearCombination I] at h
    exact h

theorem coordinateHomologicalPiece_zero_repr (I : Ideal (PolynomialRing n K))
    {z : CoordinateKoszulCarrier I} (hz : z ∈ coordinateHomologicalPiece I 0) :
    z = (coordinateKoszulBasis I).repr z ∅ • coordinateKoszulBasis I ∅ := by
  calc
    z = ∑ s, (coordinateKoszulBasis I).repr z s • coordinateKoszulBasis I s :=
      ((coordinateKoszulBasis I).sum_repr z).symm
    _ = _ := by
      apply Finset.sum_eq_single ∅
      · intro s hs hne
        rw [(mem_coordinateHomologicalPiece I 0 z).mp hz s (by
          intro h; exact hne (Finset.card_eq_zero.mp (by exact_mod_cast h)))]
        exact zero_smul (PolynomialRing n K ⧸ I) (coordinateKoszulBasis I s)
      · intro h
        exact (h (Finset.mem_univ _)).elim

theorem coordinateHomologicalPiece_top_repr (I : Ideal (PolynomialRing n K))
    {z : CoordinateKoszulCarrier I} (hz : z ∈ coordinateHomologicalPiece I (n : ℤ)) :
    z = (coordinateKoszulBasis I).repr z Finset.univ • coordinateKoszulBasis I Finset.univ := by
  calc
    z = ∑ s, (coordinateKoszulBasis I).repr z s • coordinateKoszulBasis I s :=
      ((coordinateKoszulBasis I).sum_repr z).symm
    _ = _ := by
      apply Finset.sum_eq_single Finset.univ
      · intro s hs hne
        rw [(mem_coordinateHomologicalPiece I (n : ℤ) z).mp hz s (by
          intro h
          exact hne (s.eq_univ_of_card (by
            simpa only [Fintype.card_fin] using (show s.card = n by exact_mod_cast h))))]
        exact zero_smul (PolynomialRing n K ⧸ I) (coordinateKoszulBasis I s)
      · intro h
        exact (h (Finset.mem_univ _)).elim

set_option backward.isDefEq.respectTransparency false in
theorem coordinateKoszul_top_cycle_iff (I : Ideal (PolynomialRing n K))
    (c : PolynomialRing n K ⧸ I) :
    coordinateKoszulDifferential I (c • coordinateKoszulBasis I Finset.univ) = 0 ↔
      c ∈ quotientVariableAnnihilator I := by
  constructor
  · intro hc j
    have h := coordinateKoszulWedge_identity I j (c • coordinateKoszulBasis I Finset.univ)
    have hw : coordinateKoszulWedge I j (c • coordinateKoszulBasis I Finset.univ) = 0 := by
      rw [map_smul, coordinateKoszulWedge_basis,
        if_pos (Finset.mem_univ j), smul_zero]
    rw [hw, hc, map_zero, map_zero, zero_add] at h
    have hh := congrArg (fun z => (coordinateKoszulBasis I).repr z Finset.univ) h
    simpa only [map_zero, Finsupp.zero_apply, map_smul, Finsupp.smul_apply,
      Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one] using hh.symm
  · intro hc
    rw [coordinateKoszulDifferential_smul, coordinateKoszulDifferential_basis]
    rw [Finset.smul_sum (M := PolynomialRing n K ⧸ I)
      (N := CoordinateKoszulCarrier I) (r := c)]
    apply Finset.sum_eq_zero
    intro j hj
    rw [if_pos (Finset.mem_univ j)]
    have hzero : c * Ideal.Quotient.mk I (X j) = 0 :=
      (mul_comm c (Ideal.Quotient.mk I (X j))).trans (hc j)
    calc
      c • (Ideal.Quotient.mk I (X j) •
          (TauCeti.ExteriorAlgebra.basisEraseSign j Finset.univ •
            coordinateKoszulBasis I (Finset.univ.erase j))) =
        (c * Ideal.Quotient.mk I (X j)) •
          (TauCeti.ExteriorAlgebra.basisEraseSign j Finset.univ •
            coordinateKoszulBasis I (Finset.univ.erase j)) :=
          smul_smul c (Ideal.Quotient.mk I (X j))
            (TauCeti.ExteriorAlgebra.basisEraseSign j Finset.univ •
              coordinateKoszulBasis I (Finset.univ.erase j))
      _ = 0 := by
        rw [hzero]
        exact zero_smul (PolynomialRing n K ⧸ I)
          (TauCeti.ExteriorAlgebra.basisEraseSign j Finset.univ •
            coordinateKoszulBasis I (Finset.univ.erase j))

set_option backward.isDefEq.respectTransparency false in
def coordinateTopCyclesEquiv (I : Ideal (PolynomialRing n K)) :
    (quotientVariableAnnihilator I).restrictScalars K ≃ₗ[K]
      (coordinateDifferentialGrading I).cycles (n : ℤ) where
  toFun c := ⟨c.val • coordinateKoszulBasis I Finset.univ,
    coordinateHomologicalPiece_generator I Finset.univ (by simp) c.val,
    (coordinateKoszul_top_cycle_iff I c.val).mpr c.property⟩
  invFun z := ⟨(coordinateKoszulBasis I).repr z.val Finset.univ, by
    apply (coordinateKoszul_top_cycle_iff I _).mp
    rw [← coordinateHomologicalPiece_top_repr I z.property.1]
    exact z.property.2⟩
  left_inv c := by
    apply Subtype.ext
    simp only [map_smul, Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_eq_same, smul_eq_mul, mul_one]
  right_inv z := by
    apply Subtype.ext
    exact (coordinateHomologicalPiece_top_repr I z.property.1).symm
  map_add' a b := by
    apply Subtype.ext
    exact add_smul a.val b.val (coordinateKoszulBasis I Finset.univ)
  map_smul' c a := by
    apply Subtype.ext
    change (c • a.val) • coordinateKoszulBasis I Finset.univ =
      c • (a.val • coordinateKoszulBasis I Finset.univ)
    exact smul_assoc c a.val (coordinateKoszulBasis I Finset.univ)


def totalCoordinateTopHomologyEquiv (I : Ideal (PolynomialRing n K)) :
    TotalCoordinateKoszulHomology I (n : ℤ) ≃ₗ[K]
      (quotientVariableAnnihilator I).restrictScalars K :=
  (Submodule.quotEquivOfEqBot _ (by
    change ((coordinateHomologicalPiece I ((n : ℤ) + 1)).map
      (coordinateKoszulDifferential I)).comap _ = ⊥
    rw [coordinateHomologicalPiece_eq_bot I (Or.inr (by omega)), Submodule.map_bot]
    exact LinearMap.ker_eq_bot.mpr (Submodule.injective_subtype _))).trans
    (coordinateTopCyclesEquiv I).symm

end HigherSpecht
end
end CanonicalSource69

section CanonicalSource70
/- Source: HigherSpecht/KoszulProjectiveResolution.lean -/



/-!
# The actual projective resolution supplied by a regular Koszul complex

The augmentation is the quotient map after the degree-zero exterior-power
identification. Exactness and surjectivity of this map, positive-degree
acyclicity, and freeness of every exterior power give a genuine Mathlib
`ProjectiveResolution`. The last equivalence computes Mathlib's derived
tensor functor from that resolution. No acyclicity assertion is assumed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CliffordAlgebra
open scoped TensorProduct

universe u

namespace HigherSpecht

variable {R : Type u} [CommRing R] {n : ℕ} (x : Fin n → R)

abbrev KoszulResidue := R ⧸ Ideal.span (Set.range x)

def koszulAugmentation :
    ⋀[R]^0 (Fin n → R) →ₗ[R] KoszulResidue x :=
  (Ideal.span (Set.range x)).mkQ.comp
    (exteriorPower.zeroEquiv R (Fin n → R)).toLinearMap

theorem koszulAugmentation_surjective : Function.Surjective (koszulAugmentation x) :=
  (Submodule.mkQ_surjective _).comp
    (exteriorPower.zeroEquiv R (Fin n → R)).surjective

theorem koszulAugmentation_exact :
    Function.Exact (TauCeti.koszulDifferential (Fintype.linearCombination R x) 0)
      (koszulAugmentation x) := by
  intro z
  change Ideal.Quotient.mk (Ideal.span (Set.range x))
      (exteriorPower.zeroEquiv R (Fin n → R) z) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change exteriorPower.zeroEquiv R (Fin n → R) z ∈
    Submodule.span R (Set.range x) ↔ _
  rw [← Fintype.range_linearCombination R x,
    ← TauCeti.map_zeroEquiv_range_koszulDifferential_zero]
  constructor
  · rintro ⟨y, hy, hyz⟩
    exact (exteriorPower.zeroEquiv R (Fin n → R)).injective hyz ▸ hy
  · intro hz
    exact Submodule.mem_map_of_mem hz

theorem koszulAugmentation_comp_d :
    (koszulAugmentation x).comp
      (TauCeti.koszulDifferential (Fintype.linearCombination R x) 0) = 0 := by
  apply LinearMap.ext
  intro z
  exact (koszulAugmentation_exact x _).mpr ⟨z, rfl⟩

def koszulAugmentationShortComplex : ShortComplex (ModuleCat R) :=
  ModuleCat.shortComplexOfCompEqZero
    (TauCeti.koszulDifferential (Fintype.linearCombination R x) 0)
    (koszulAugmentation x) (koszulAugmentation_comp_d x)

theorem koszulAugmentationShortComplex_exact :
    (koszulAugmentationShortComplex x).Exact :=
  ModuleCat.shortComplex_exact _ (koszulAugmentation_exact x)

instance koszulAugmentation_epi : Epi (ModuleCat.ofHom (koszulAugmentation x)) :=
  (ModuleCat.epi_iff_surjective _).mpr (koszulAugmentation_surjective x)

set_option backward.isDefEq.respectTransparency false in
/-- The exterior-power complex itself, with its literal augmentation, is
a projective resolution of the quotient by a weakly regular sequence. -/
def regularKoszulProjectiveResolution
    (hx : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x)) :
    ProjectiveResolution (ModuleCat.of R (KoszulResidue x)) where
  complex := TauCeti.koszulComplex (Fintype.linearCombination R x)
  projective i := by
    change CategoryTheory.Projective (ModuleCat.of R (⋀[R]^i (Fin n → R)))
    infer_instance
  π := (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨ModuleCat.ofHom (koszulAugmentation x), by
      apply ModuleCat.hom_ext
      exact koszulAugmentation_comp_d x⟩
  quasiIso := ⟨fun i => by
    cases i with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · dsimp
        refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
          ⟨koszulAugmentationShortComplex_exact x, by
            change Epi (ModuleCat.ofHom (koszulAugmentation x))
            infer_instance⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by simp [koszulAugmentationShortComplex, TauCeti.koszulComplex_d])
          (by simp [koszulAugmentationShortComplex])
      all_goals rfl
    | succ i =>
      rw [quasiIsoAt_iff_exactAt']
      · exact TauCeti.koszulComplex.exactAt_of_isWeaklyRegular x hx i
      · apply ChainComplex.exactAt_succ_single_obj⟩

/-- Mathlib's derived tensor functor is computed by tensoring the genuine
regular Koszul projective resolution. -/
def torRegularKoszulIso
    (hx : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x))
    (M : ModuleCat R) (i : ℕ) :
    ((CategoryTheory.Tor (ModuleCat R) i).obj M).obj
        (ModuleCat.of R (KoszulResidue x)) ≅
      ((((MonoidalCategory.tensoringLeft (ModuleCat R)).obj M).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj
          (TauCeti.koszulComplex (Fintype.linearCombination R x))).homology i :=
  (regularKoszulProjectiveResolution x hx).isoLeftDerivedObj
    ((MonoidalCategory.tensoringLeft (ModuleCat R)).obj M) i

end HigherSpecht
end
end CanonicalSource70

section CanonicalSource71
/- Source: HigherSpecht/KoszulScalarExtension.lean -/



/-!
# Extension of scalars for the actual finite-coordinate Koszul complex

The degreewise comparison sends a tensor of a wedge to the wedge of the
coefficientwise images. Its compatibility with contraction is proved on
pure wedges. Consequently tensoring the polynomial-variable resolution
really gives the coordinate complex used in the regularity calculation.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CliffordAlgebra
open scoped Classical TensorProduct

universe u

namespace HigherSpecht

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

def koszulCoefficientMap (n : ℕ) : (Fin n → R) →ₗ[R] (Fin n → A) :=
  (Algebra.linearMap R A).compLeft (Fin n)

theorem koszulCoefficientMap_isBaseChange (n : ℕ) :
    IsBaseChange A (koszulCoefficientMap R A n) :=
  (IsBaseChange.linearMap R A).finitePow (Fin n)

def koszulScalarExtensionDegree (n i : ℕ) :
    A ⊗[R] (⋀[R]^i (Fin n → R)) ≃ₗ[A] ⋀[A]^i (Fin n → A) :=
  (koszulCoefficientMap_isBaseChange R A n).exteriorPowerEquiv i

@[simp] theorem koszulScalarExtensionDegree_tmul_wedge
    (n i : ℕ) (a : A) (v : Fin i → Fin n → R) :
    koszulScalarExtensionDegree R A n i
      (a ⊗ₜ[R] exteriorPower.ιMulti R i v) =
      a • exteriorPower.ιMulti A i (fun j => koszulCoefficientMap R A n (v j)) :=
  (koszulCoefficientMap_isBaseChange R A n).exteriorPowerEquiv_tmul_ιMulti i a v

theorem koszulFunctional_coefficientMap {n : ℕ} (x : Fin n → R) (v : Fin n → R) :
    Fintype.linearCombination A (fun j => algebraMap R A (x j))
        (koszulCoefficientMap R A n v) =
      algebraMap R A (Fintype.linearCombination R x v) := by
  simp only [Fintype.linearCombination_apply, koszulCoefficientMap,
    LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply,
    map_sum, map_mul, smul_eq_mul]

theorem koszulScalarExtensionDegree_differential {n : ℕ} (x : Fin n → R) (i : ℕ) :
    (TauCeti.koszulDifferential
      (Fintype.linearCombination A (fun j => algebraMap R A (x j))) i).comp
        (koszulScalarExtensionDegree R A n (i + 1)).toLinearMap =
      (koszulScalarExtensionDegree R A n i).toLinearMap.comp
        ((TauCeti.koszulDifferential (Fintype.linearCombination R x) i).baseChange A) := by
  let extR : Module R (⋀[A]^i (Fin n → A)) := Module.compHom _ (algebraMap R A)
  let extTower : @IsScalarTower R A (⋀[A]^i (Fin n → A)) _
      (⋀[A]^i (Fin n → A)).module.toSMul extR.toSMul :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  apply @TensorProduct.AlgebraTensorModule.ext R A A
    (⋀[R]^(i + 1) (Fin n → R)) (⋀[A]^i (Fin n → A))
    _ _ _ _ _ _ _ _ _ _ extR _ extTower
  intro a z
  have hw :
      (((TauCeti.koszulDifferential
          (Fintype.linearCombination A (fun j => algebraMap R A (x j))) i).comp
          (koszulScalarExtensionDegree R A n (i + 1)).toLinearMap).restrictScalars R).comp
          (TensorProduct.mk R A (⋀[R]^(i + 1) (Fin n → R)) a) =
      (((koszulScalarExtensionDegree R A n i).toLinearMap.comp
          ((TauCeti.koszulDifferential (Fintype.linearCombination R x) i).baseChange A)).restrictScalars R).comp
          (TensorProduct.mk R A (⋀[R]^(i + 1) (Fin n → R)) a) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply, TensorProduct.mk_apply, LinearEquiv.coe_coe,
      koszulScalarExtensionDegree_tmul_wedge, LinearMap.baseChange_tmul,
      TauCeti.koszulDifferential_ιMulti, map_smul, map_sum,
      TensorProduct.tmul_sum, TensorProduct.tmul_smul,
      koszulFunctional_coefficientMap, map_mul, map_pow, map_neg, map_one]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hremove : j.removeNth (fun q => koszulCoefficientMap R A n (v q)) =
        fun q => koszulCoefficientMap R A n (j.removeNth v q) := rfl
    rw [hremove, TensorProduct.smul_tmul', koszulScalarExtensionDegree_tmul_wedge]
    simp only [smul_smul, Algebra.smul_def, map_mul, map_pow, map_neg, map_one]
    congr 1
    ring
  exact LinearMap.congr_fun hw z

set_option backward.isDefEq.respectTransparency false in
def koszulScalarRestrictionEquiv (M : Type u) [AddCommGroup M]
    [Module R M] [Module A M] [IsScalarTower R A M] :
    ((ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A M)) ≃ₗ[R] M where
  toFun z := z
  invFun z := z
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r z := IsScalarTower.algebraMap_smul (M := M) A r (show M from z)

def koszulScalarExtensionDegreeIso (n i : ℕ) :
    ModuleCat.of R (A ⊗[R] (⋀[R]^i (Fin n → R))) ≅
      (ModuleCat.restrictScalars (algebraMap R A)).obj
        (ModuleCat.of A (⋀[A]^i (Fin n → A))) :=
  (koszulScalarRestrictionEquiv R A _).symm.toModuleIso ≪≫
    (ModuleCat.restrictScalars (algebraMap R A)).mapIso
      (koszulScalarExtensionDegree R A n i).toModuleIso

def koszulScalarExtensionIso {n : ℕ} (x : Fin n → R) :
    (((MonoidalCategory.tensoringLeft (ModuleCat R)).obj (ModuleCat.of R A)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
        (TauCeti.koszulComplex (Fintype.linearCombination R x)) ≅
      ((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj
        (TauCeti.koszulComplex
          (Fintype.linearCombination A (fun j => algebraMap R A (x j)))) :=
  HomologicalComplex.Hom.isoOfComponents (koszulScalarExtensionDegreeIso R A n) (by
    rintro _ i rfl
    simp only [Functor.mapHomologicalComplex_obj_d, TauCeti.koszulComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact LinearMap.congr_fun (koszulScalarExtensionDegree_differential R A x i) z)

end HigherSpecht
end
end CanonicalSource71

section CanonicalSource72
/- Source: HigherSpecht/CoordinateKoszulChainComparison.lean -/



/-!
# The coordinate complex is the actual exterior-power Koszul complex

The comparison is the identity on the underlying exterior algebra.  Its
degree restriction is justified by the independently proved exterior-basis
description, and its differential is the same contraction map.  The final
equivalence compares the literal cycles/modulo-boundaries quotient with
Mathlib's homology object, including homological degree zero.
-/

noncomputable section

open CategoryTheory CliffordAlgebra Module MvPolynomial
open scoped Classical

namespace HigherSpecht

variable {K : Type*} [Field K] {n : ℕ}

private theorem coordinateHomologicalPiece_mem_exteriorPower
    (I : Ideal (PolynomialRing n K)) (i : ℕ) (z : CoordinateKoszulCarrier I) :
    z ∈ coordinateHomologicalPiece I (i : ℤ) ↔
      z ∈ ExteriorAlgebra.exteriorPower (PolynomialRing n K ⧸ I) i
        (Fin n → PolynomialRing n K ⧸ I) := by
  exact Iff.of_eq (congrArg
    (fun P : Submodule K (CoordinateKoszulCarrier I) => z ∈ P)
    (coordinateHomologicalPiece_eq_exteriorPower I i))

def coordinateExteriorEquiv (I : Ideal (PolynomialRing n K)) (i : ℕ) :
    coordinateHomologicalPiece I (i : ℤ) ≃ₗ[K]
      ⋀[PolynomialRing n K ⧸ I]^i (Fin n → PolynomialRing n K ⧸ I) where
  toFun z := ⟨z.val, by
    exact (coordinateHomologicalPiece_mem_exteriorPower I i z.val).mp z.property⟩
  invFun z := ⟨z.val, by
    exact (coordinateHomologicalPiece_mem_exteriorPower I i z.val).mpr z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coordinateExteriorEquiv_val
    (I : Ideal (PolynomialRing n K)) (i : ℕ)
    (z : coordinateHomologicalPiece I (i : ℤ)) :
    (coordinateExteriorEquiv I i z).val = z.val := rfl

def coordinateChainDifferential (I : Ideal (PolynomialRing n K)) (i : ℕ) :
    coordinateHomologicalPiece I ((i + 1 : ℕ) : ℤ) →ₗ[K]
      coordinateHomologicalPiece I (i : ℤ) :=
  (coordinateKoszulDifferential I).restrict fun z hz => by
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using
      coordinateHomologicalDifferential_mem I hz

def coordinateChainComplex (I : Ideal (PolynomialRing n K)) :
    ChainComplex (ModuleCat K) ℕ :=
  ChainComplex.of (fun i => ModuleCat.of K (coordinateHomologicalPiece I (i : ℤ)))
    (fun i => ModuleCat.ofHom (coordinateChainDifferential I i)) (fun i => by
      apply ModuleCat.hom_ext
      ext z
      exact coordinateKoszulDifferential_square I z.val)

def exteriorCoordinateComplex (I : Ideal (PolynomialRing n K)) :
    ChainComplex (ModuleCat K) ℕ :=
  ((ModuleCat.restrictScalars (algebraMap K (PolynomialRing n K ⧸ I))).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj
      (TauCeti.koszulComplex (coordinateKoszulFunctional I))

@[simp] theorem coordinateChainComplex_d
    (I : Ideal (PolynomialRing n K)) (i : ℕ) :
    (coordinateChainComplex I).d (i + 1) i =
      ModuleCat.ofHom (coordinateChainDifferential I i) := by
  simp only [coordinateChainComplex, ChainComplex.of_d]

theorem exteriorCoordinateComplex_d
    (I : Ideal (PolynomialRing n K)) (i : ℕ) :
    (exteriorCoordinateComplex I).d (i + 1) i =
      (ModuleCat.restrictScalars (algebraMap K (PolynomialRing n K ⧸ I))).map
        (ModuleCat.ofHom (TauCeti.koszulDifferential (coordinateKoszulFunctional I) i)) := by
  change (ModuleCat.restrictScalars (algebraMap K (PolynomialRing n K ⧸ I))).map
    ((TauCeti.koszulComplex (coordinateKoszulFunctional I)).d (i + 1) i) = _
  rw [TauCeti.koszulComplex_d]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem exteriorCoordinateComplex_d_apply
    (I : Ideal (PolynomialRing n K)) (i : ℕ)
    (z : ⋀[PolynomialRing n K ⧸ I]^(i + 1) (Fin n → PolynomialRing n K ⧸ I)) :
    ((exteriorCoordinateComplex I).d (i + 1) i).hom z =
      TauCeti.koszulDifferential (coordinateKoszulFunctional I) i z := by
  rw [exteriorCoordinateComplex_d]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem exteriorCoordinateComplex_d_coe
    (I : Ideal (PolynomialRing n K)) (i : ℕ)
    (z : ⋀[PolynomialRing n K ⧸ I]^(i + 1) (Fin n → PolynomialRing n K ⧸ I)) :
    (((exteriorCoordinateComplex I).d (i + 1) i).hom z).val =
      coordinateKoszulDifferential I z.val := by
  rw [exteriorCoordinateComplex_d_apply]
  exact TauCeti.coe_koszulDifferential_apply (coordinateKoszulFunctional I) i z

set_option backward.isDefEq.respectTransparency false in
def coordinateChainComplexIso (I : Ideal (PolynomialRing n K)) :
    coordinateChainComplex I ≅ exteriorCoordinateComplex I :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (coordinateExteriorEquiv I i).toModuleIso ≪≫
      (koszulScalarRestrictionEquiv K (PolynomialRing n K ⧸ I) _).symm.toModuleIso)
    (by
      rintro _ i rfl
      rw [coordinateChainComplex_d, exteriorCoordinateComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      change TauCeti.koszulDifferential (coordinateKoszulFunctional I) i
          (coordinateExteriorEquiv I (i + 1) z) =
        coordinateExteriorEquiv I i (coordinateChainDifferential I i z)
      apply Subtype.ext
      exact TauCeti.coe_koszulDifferential_apply (coordinateKoszulFunctional I) i
        (coordinateExteriorEquiv I (i + 1) z))

theorem coordinateDifferential_zero_on_degree_zero
    (I : Ideal (PolynomialRing n K))
    (z : ⋀[PolynomialRing n K ⧸ I]^0 (Fin n → PolynomialRing n K ⧸ I)) :
    coordinateKoszulDifferential I z.val = 0 := by
  have hz : z.val ∈ coordinateHomologicalPiece I 0 :=
    (coordinateHomologicalPiece_mem_exteriorPower I 0 z.val).mpr z.property
  have hd := coordinateHomologicalDifferential_mem I hz
  rw [coordinateHomologicalPiece_eq_bot I (Or.inl (by norm_num : (0 : ℤ) - 1 < 0))]
    at hd
  exact hd

set_option backward.isDefEq.respectTransparency false in
theorem exteriorCoordinateComplex_cycle_iff
    (I : Ideal (PolynomialRing n K)) (i : ℕ)
    (z : ⋀[PolynomialRing n K ⧸ I]^i (Fin n → PolynomialRing n K ⧸ I)) :
    ((exteriorCoordinateComplex I).d i (i - 1)).hom z = 0 ↔
      coordinateKoszulDifferential I z.val = 0 := by
  cases i with
  | zero =>
      have hd : (exteriorCoordinateComplex I).d 0 0 = 0 :=
        (exteriorCoordinateComplex I).shape 0 0 (by simp)
      rw [Nat.zero_sub, hd]
      exact ⟨fun _ => coordinateDifferential_zero_on_degree_zero I z, fun _ => rfl⟩
  | succ i =>
      rw [Nat.add_sub_cancel]
      constructor
      · intro h
        have hzero : (((exteriorCoordinateComplex I).d (i + 1) i).hom z).val = 0 :=
          congrArg Subtype.val h
        exact (exteriorCoordinateComplex_d_coe I i z).symm.trans hzero
      · intro h
        apply Subtype.ext
        change (((exteriorCoordinateComplex I).d (i + 1) i).hom z).val = 0
        exact (exteriorCoordinateComplex_d_coe I i z).trans h

def coordinateHomologyShortComplex (I : Ideal (PolynomialRing n K)) (i : ℕ) :
    ShortComplex (ModuleCat K) := (exteriorCoordinateComplex I).sc' (i + 1) i (i - 1)

set_option backward.isDefEq.respectTransparency false in
def exteriorCoordinateCyclesEquiv (I : Ideal (PolynomialRing n K)) (i : ℕ) :
    LinearMap.ker (coordinateHomologyShortComplex I i).g.hom ≃ₗ[K]
      (coordinateDifferentialGrading I).cycles (i : ℤ) where
  toFun z := ⟨z.val.val, by
    constructor
    · exact (coordinateHomologicalPiece_mem_exteriorPower I i z.val.val).mpr
        z.val.property
    · exact (exteriorCoordinateComplex_cycle_iff I i z.val).mp z.property⟩
  invFun z := ⟨⟨z.val, by
      exact (coordinateHomologicalPiece_mem_exteriorPower I i z.val).mp z.property.1⟩,
    (exteriorCoordinateComplex_cycle_iff I i _).mpr z.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

set_option backward.isDefEq.respectTransparency false in
theorem exteriorCoordinateCyclesEquiv_boundaries
    (I : Ideal (PolynomialRing n K)) (i : ℕ) :
    ((coordinateHomologyShortComplex I i).moduleCatToCycles.range).map
        (exteriorCoordinateCyclesEquiv I i).toLinearMap =
      ((coordinateDifferentialGrading I).boundaries (i : ℤ)).comap
        ((coordinateDifferentialGrading I).cycles (i : ℤ)).subtype := by
  ext z
  constructor
  · rintro ⟨w, ⟨y, rfl⟩, rfl⟩
    refine ⟨y.val, ?_, ?_⟩
    · change y.val ∈ coordinateHomologicalPiece I ((i : ℤ) + 1)
      simpa only [Nat.cast_add, Nat.cast_one] using
        (coordinateHomologicalPiece_mem_exteriorPower I (i + 1) y.val).mpr y.property
    · change coordinateKoszulDifferential I y.val =
        (((exteriorCoordinateComplex I).d (i + 1) i).hom y).val
      exact (exteriorCoordinateComplex_d_coe I i y).symm
  · rintro ⟨y, hy, hdy⟩
    have hyp : y ∈ ExteriorAlgebra.exteriorPower (PolynomialRing n K ⧸ I)
        (i + 1) (Fin n → PolynomialRing n K ⧸ I) := by
      apply (coordinateHomologicalPiece_mem_exteriorPower I (i + 1) y).mp
      change y ∈ coordinateHomologicalPiece I ((i : ℤ) + 1) at hy
      simpa only [Nat.cast_add, Nat.cast_one] using hy
    let y' : ⋀[PolynomialRing n K ⧸ I]^(i + 1)
        (Fin n → PolynomialRing n K ⧸ I) := ⟨y, hyp⟩
    refine ⟨(coordinateHomologyShortComplex I i).moduleCatToCycles y',
      ⟨y', rfl⟩, ?_⟩
    apply Subtype.ext
    change (((exteriorCoordinateComplex I).d (i + 1) i).hom y').val = z.val
    change coordinateKoszulDifferential I y = z.val at hdy
    exact (exteriorCoordinateComplex_d_coe I i y').trans hdy

set_option backward.isDefEq.respectTransparency false in
/-- Mathlib's actual exterior-power Koszul homology is the explicit
coordinate cycles/modulo-boundaries quotient. -/
def exteriorCoordinateHomologyEquiv
    (I : Ideal (PolynomialRing n K)) (i : ℕ) :
    (exteriorCoordinateComplex I).homology i ≃ₗ[K]
      TotalCoordinateKoszulHomology I (i : ℤ) :=
  ((exteriorCoordinateComplex I).homologyIsoSc' (i + 1) i (i - 1)
      (by simp) (by cases i <;> simp)).toLinearEquiv |>.trans
    (coordinateHomologyShortComplex I i).moduleCatHomologyIso.toLinearEquiv |>.trans
      (Submodule.Quotient.equiv _ _ (exteriorCoordinateCyclesEquiv I i)
        (exteriorCoordinateCyclesEquiv_boundaries I i))

end HigherSpecht
end
end CanonicalSource72

section CanonicalSource73
/- Source: HigherSpecht/PolynomialKoszulTor.lean -/



/-!
# The actual derived tensor object over the polynomial ring

The residue module below is the coefficient field with its literal
constant-coefficient action.  The quotient by the variables is explicitly
isomorphic to that module.  Tensoring the proved variable Koszul resolution,
extending coefficients to the actual quotient, and restricting scalars give
the comparison with the coordinate homology used in the regularity proof.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CliffordAlgebra Module MvPolynomial
open scoped Classical TensorProduct

namespace HigherSpecht

variable (K : Type*) [Field K] (n : ℕ)

def polynomialResidueModule : ModuleCat (PolynomialRing n K) := by
  letI : Module (PolynomialRing n K) K := Module.compHom K MvPolynomial.constantCoeff
  exact ModuleCat.of (PolynomialRing n K) K

def polynomialResidueEvaluation :
    KoszulResidue (MvPolynomial.X : Fin n → PolynomialRing n K) →+* K :=
  Ideal.Quotient.lift _ MvPolynomial.constantCoeff (by
    change Ideal.span (Set.range (MvPolynomial.X : Fin n → PolynomialRing n K)) ≤
      RingHom.ker (MvPolynomial.constantCoeff : PolynomialRing n K →+* K)
    apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    exact MvPolynomial.constantCoeff_X K i)

@[simp] theorem polynomialResidueEvaluation_mk (p : PolynomialRing n K) :
    polynomialResidueEvaluation K n (Ideal.Quotient.mk _ p) = constantCoeff p := rfl

theorem polynomial_sub_constant_mem_variables (p : PolynomialRing n K) :
    p - C (constantCoeff p) ∈ Ideal.span
      (Set.range (MvPolynomial.X : Fin n → PolynomialRing n K)) := by
  obtain ⟨g, hg⟩ := constantCoeff_zero_eq_sum_variables
    (f := p - C (constantCoeff p)) (by simp)
  rw [← hg]
  apply Ideal.sum_mem
  intro i hi
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

set_option backward.isDefEq.respectTransparency false in
def polynomialResidueEquiv :
    KoszulResidue (MvPolynomial.X : Fin n → PolynomialRing n K) ≃ₗ[PolynomialRing n K]
      polynomialResidueModule K n where
  toFun := polynomialResidueEvaluation K n
  invFun c := Ideal.Quotient.mk _ (MvPolynomial.C c)
  left_inv z := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    change Ideal.Quotient.mk _ (C (constantCoeff p)) = Ideal.Quotient.mk _ p
    apply Ideal.Quotient.eq.mpr
    simpa only [neg_sub] using
      (Ideal.span (Set.range (MvPolynomial.X : Fin n → PolynomialRing n K))).neg_mem
        (polynomial_sub_constant_mem_variables K n p)
  right_inv c := by simp only [polynomialResidueEvaluation_mk, constantCoeff_C]
  map_add' := map_add _
  map_smul' r z := by
    change polynomialResidueEvaluation K n (Ideal.Quotient.mk _ r * z) =
      constantCoeff r * polynomialResidueEvaluation K n z
    rw [map_mul, polynomialResidueEvaluation_mk]

/-- This is Mathlib's derived tensor functor, with second argument the
actual coefficient field as a polynomial-ring module. -/
def polynomialTorModule (I : Ideal (PolynomialRing n K)) (i : ℕ) : ModuleCat K :=
  (ModuleCat.restrictScalars (algebraMap K (PolynomialRing n K))).obj
    (((CategoryTheory.Tor (ModuleCat (PolynomialRing n K)) i).obj
      (ModuleCat.of (PolynomialRing n K) (PolynomialRing n K ⧸ I))).obj
        (polynomialResidueModule K n))

abbrev PolynomialTor (I : Ideal (PolynomialRing n K)) (i : ℕ) :=
  polynomialTorModule K n I i

set_option backward.isDefEq.respectTransparency false in
def polynomialTorExteriorHomologyIso (I : Ideal (PolynomialRing n K)) (i : ℕ) :
    polynomialTorModule K n I i ≅ (exteriorCoordinateComplex I).homology i := by
  let R := PolynomialRing n K
  let A := R ⧸ I
  let x : Fin n → R := MvPolynomial.X
  let resKR := ModuleCat.restrictScalars (algebraMap K R)
  let resRA := ModuleCat.restrictScalars (algebraMap R A)
  let resKA := ModuleCat.restrictScalars (algebraMap K A)
  let C := TauCeti.koszulComplex (coordinateKoszulFunctional I)
  let F := (CategoryTheory.Tor (ModuleCat R) i).obj (ModuleCat.of R A)
  have hfunctional : Fintype.linearCombination A
      (fun j => algebraMap R A (x j)) = coordinateKoszulFunctional I :=
    (coordinateKoszulFunctional_eq_linearCombination I).symm
  let e₀ := resKR.mapIso (F.mapIso (polynomialResidueEquiv K n).toModuleIso).symm
  let e₁ := resKR.mapIso (torRegularKoszulIso x
    (polynomialVariables_isWeaklyRegular K n) (ModuleCat.of R A) i)
  let eKoszul :
      (((MonoidalCategory.tensoringLeft (ModuleCat R)).obj (ModuleCat.of R A)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (TauCeti.koszulComplex (Fintype.linearCombination R x)) ≅
      (resRA.mapHomologicalComplex (ComplexShape.down ℕ)).obj C := by
    simpa only [hfunctional] using (koszulScalarExtensionIso R A x)
  let e₂ := resKR.mapIso
    ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) i).mapIso
      eKoszul)
  let e₃ := resKR.mapIso ((C.sc i).mapHomologyIso resRA)
  let e₄ := (ModuleCat.restrictScalarsComp'App (algebraMap K R) (algebraMap R A)
    (algebraMap K A) (IsScalarTower.algebraMap_eq K R A) (C.homology i)).symm
  let e₅ := ((C.sc i).mapHomologyIso resKA).symm
  exact e₀ ≪≫ e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅

/-- The actual Tor object is linearly equivalent to the literal total
coordinate Koszul homology; no exactness hypothesis is added. -/
def polynomialTorCoordinateEquiv (I : Ideal (PolynomialRing n K)) (i : ℕ) :
    PolynomialTor K n I i ≃ₗ[K] TotalCoordinateKoszulHomology I (i : ℤ) :=
  (polynomialTorExteriorHomologyIso K n I i).toLinearEquiv.trans
    (exteriorCoordinateHomologyEquiv I i)

end HigherSpecht
end
end CanonicalSource73

section CanonicalSource74
/- Source: HigherSpecht/HomogeneousBasisGrading.lean -/



/-!
# The internal grading supplied by an actual homogeneous basis

The construction assigns degrees to basis vectors and transports the
literal direct-sum decomposition of their finitely supported coordinates.
The comparison theorem identifies its pieces with independently given
homogeneous submodules and projections.  Thus it cannot manufacture a
grading which differs from the polynomial grading used by the paper.
-/

noncomputable section
open Module TauCeti
open scoped Classical

namespace HigherSpecht

variable {K M ι : Type*} [CommRing K] [AddCommGroup M] [Module K M]

def homogeneousBasisGrading (b : Basis ι K M) (degree : ι → ℤ) :
    InternalGrading K M :=
  (InternalGrading.finsupp K degree).map b.repr.symm

theorem mem_homogeneousBasisGrading_iff
    (b : Basis ι K M) (degree : ι → ℤ) (d : ℤ) (x : M) :
    x ∈ (homogeneousBasisGrading b degree).piece d ↔
      ∀ i, b.repr x i ≠ 0 → degree i = d := by
  rw [homogeneousBasisGrading, InternalGrading.mem_map_piece_iff]
  exact InternalGrading.mem_finsupp_piece_iff

theorem basis_mem_homogeneousBasisGrading
    (b : Basis ι K M) (degree : ι → ℤ) (i : ι) :
    b i ∈ (homogeneousBasisGrading b degree).piece (degree i) := by
  rw [mem_homogeneousBasisGrading_iff]
  intro j hj
  by_cases hji : j = i
  · simpa only [hji]
  · simp only [b.repr_self, Finsupp.single_apply, if_neg (Ne.symm hji)] at hj
    exact (hj rfl).elim

theorem homogeneousBasisGrading_piece_le
    (b : Basis ι K M) (degree : ι → ℤ) (H : ℤ → Submodule K M)
    (hb : ∀ i, b i ∈ H (degree i)) (d : ℤ) :
    (homogeneousBasisGrading b degree).piece d ≤ H d := by
  intro x hx
  rw [mem_homogeneousBasisGrading_iff] at hx
  rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
  apply (H d).sum_mem
  intro i hi
  exact (H d).smul_mem _ ((hx i (Finsupp.mem_support_iff.mp hi)) ▸ hb i)

theorem homogeneousBasisGrading_piece_eq
    (b : Basis ι K M) (degree : ι → ℤ) (H : ℤ → Submodule K M)
    (P : ℤ → Module.End K M)
    (hb : ∀ i, b i ∈ H (degree i))
    (hfixed : ∀ d x, x ∈ H d → P d x = x)
    (hbasis : ∀ d i, P d (b i) = if degree i = d then b i else 0) :
    (homogeneousBasisGrading b degree).piece = H := by
  funext d
  apply le_antisymm (homogeneousBasisGrading_piece_le b degree H hb d)
  intro x hx
  rw [mem_homogeneousBasisGrading_iff]
  intro i hi
  by_contra hne
  have hcoord : (b.coord i).comp (P d) = 0 := by
    apply b.ext
    intro j
    rw [LinearMap.comp_apply, hbasis]
    by_cases hj : degree j = d
    · rw [if_pos hj]
      have hji : j ≠ i := fun h => hne (h ▸ hj)
      simp only [Basis.coord_apply, b.repr_self, Finsupp.single_apply,
        if_neg hji, LinearMap.zero_apply]
    · simp only [if_neg hj, map_zero, LinearMap.zero_apply]
  have h := DFunLike.congr_fun hcoord x
  rw [LinearMap.comp_apply, hfixed d x hx, LinearMap.zero_apply,
    Basis.coord_apply] at h
  exact hi h

theorem homogeneousBasisGrading_piece_eq_bot_of_lt
    (b : Basis ι K M) (degree : ι → ℤ) (L : ℤ)
    (hdegree : ∀ i, L ≤ degree i) {d : ℤ} (hd : d < L) :
    (homogeneousBasisGrading b degree).piece d = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  apply b.repr.injective
  ext i
  rw [map_zero, Finsupp.zero_apply]
  by_contra hne
  have heq := (mem_homogeneousBasisGrading_iff b degree d x).mp hx i hne
  have := hdegree i
  omega

end HigherSpecht
end
end CanonicalSource74

section CanonicalSource75
/- Source: HigherSpecht/ParameterHomogeneousBasis.lean -/



/-!
# The actual homogeneous elementary-parameter basis

Parameter X_j has weight j+1.  Multiplying the proved finite parameter
basis by parameter monomials gives a basis over the coefficient field.
Its internal grading is proved to equal the actual quotient polynomial
grading.  In particular its coefficients have the requisite weighted
degrees; graded freeness is a conclusion, not an additional hypothesis.
-/

noncomputable section
open TauCeti Module MvPolynomial Finset
open scoped Classical

namespace HigherSpecht

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K]

def elementaryIntegerWeights (m : ℕ) (i : Fin m) : ℤ := i.val + 1

theorem elementaryWeight_cast {m : ℕ} (a : Fin m →₀ ℕ) :
    (elementaryWeight a : ℤ) = Finsupp.weight (elementaryIntegerWeights m) a := by
  simp only [elementaryWeight, Finsupp.weight_eq_sum, elementaryIntegerWeights,
    nsmul_eq_mul, Nat.cast_sum, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_id]

theorem elementaryWeight_eq_zero_iff {m : ℕ} (a : Fin m →₀ ℕ) :
    elementaryWeight a = 0 ↔ a = 0 := by
  constructor
  · intro h
    ext i
    rw [Finsupp.zero_apply]
    by_contra hi
    have hle := Finsupp.le_weight_of_ne_zero' (fun j : Fin m => j.val + 1) hi
    change i.val + 1 ≤ elementaryWeight a at hle
    omega
  · rintro rfl
    exact map_zero _

def elementaryWeightedPiece (m : ℕ) (d : ℤ) :
    Submodule K (MvPolynomial (Fin m) K) :=
  MvPolynomial.weightedHomogeneousSubmodule K (elementaryIntegerWeights m) d

theorem elementaryWeightedPiece_eq_bot_of_neg (m : ℕ) {d : ℤ} (hd : d < 0) :
    elementaryWeightedPiece K m d = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro p hp
  apply MvPolynomial.ext
  intro a
  rw [MvPolynomial.coeff_zero]
  by_contra ha
  have heq := hp ha
  rw [← elementaryWeight_cast] at heq
  have hnonneg : (0 : ℤ) ≤ elementaryWeight a := Int.natCast_nonneg _
  omega

theorem elementaryWeightedPiece_zero (m : ℕ) {p : MvPolynomial (Fin m) K}
    (hp : p ∈ elementaryWeightedPiece K m 0) : p = MvPolynomial.C p.constantCoeff := by
  apply MvPolynomial.ext
  intro a
  by_cases ha : a = 0
  · subst a
    simp only [MvPolynomial.coeff_C, if_pos rfl, ite_true, MvPolynomial.constantCoeff_eq]
  · have hc : p.coeff a = 0 := by
      by_contra hc
      have heq := hp hc
      rw [← elementaryWeight_cast] at heq
      exact ha ((elementaryWeight_eq_zero_iff a).mp (by exact_mod_cast heq))
    simp only [hc, MvPolynomial.coeff_C, if_neg (Ne.symm ha)]

theorem quotientIntegerPiece_one {n : ℕ} (I : Ideal (PolynomialRing n K)) :
    (1 : PolynomialRing n K ⧸ I) ∈ quotientIntegerPiece I 0 := by
  simpa only [map_one, Nat.cast_zero] using
    quotientIntegerPiece_mk I (MvPolynomial.isHomogeneous_one (σ := Fin n) (R := K))

theorem quotientIntegerPiece_pow {n : ℕ} (I : Ideal (PolynomialRing n K))
    {x : PolynomialRing n K ⧸ I} {d : ℤ}
    (hx : x ∈ quotientIntegerPiece I d) (a : ℕ) :
    x ^ a ∈ quotientIntegerPiece I (a * d) := by
  induction a with
  | zero => simpa only [pow_zero, Nat.cast_zero, zero_mul] using quotientIntegerPiece_one K I
  | succ a ih =>
      simpa only [pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using
        quotientIntegerPiece_mul I ih hx

theorem parameter_monomial_mem_piece (n : ℕ) (lam : YoungDiagram)
    (a : Fin (n - lam.card) →₀ ℕ) :
    algebraMap (ElementaryParameterRing K n lam) (UntruncatedRing K n lam)
      (MvPolynomial.monomial a 1) ∈
      quotientIntegerPiece (untruncatedIdeal K n lam) (elementaryWeight a : ℤ) := by
  rw [untruncatedParameter_algebraMap, MvPolynomial.aeval_monomial]
  simp only [map_one, one_mul]
  have hprod : ∀ s : Finset (Fin (n - lam.card)),
      (∏ i ∈ s, elementaryParameterClasses K n lam i ^ a i) ∈
      quotientIntegerPiece (untruncatedIdeal K n lam)
        (∑ i ∈ s, (a i : ℤ) * (i.val + 1)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using quotientIntegerPiece_one K (untruncatedIdeal K n lam)
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      apply quotientIntegerPiece_mul _ _ ih
      apply quotientIntegerPiece_pow
      simpa only [elementaryParameterClasses, elementaryOn_univ, Nat.cast_add, Nat.cast_one] using
        quotientIntegerPiece_mk (untruncatedIdeal K n lam)
          (elementaryOn_isHomogeneous (Finset.univ : Finset (Fin n)) (i.val + 1))
  convert hprod a.support using 1 <;>
    simp only [elementaryWeight, Finsupp.weight_apply, Finsupp.sum, Finsupp.prod,
    nsmul_eq_mul, Nat.cast_sum, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_id]

def untruncatedCoefficientBasis (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Basis ((Fin (n - lam.card) →₀ ℕ) × SpecialFiberMonomialIndex n lam) K
      (UntruncatedRing K n lam) :=
  (MvPolynomial.basisMonomials (Fin (n - lam.card)) K).smulTower
    (untruncatedMonomialParameterBasis K n lam hk)

def parameterBasisDegree {n : ℕ} {lam : YoungDiagram}
    (i : (Fin (n - lam.card) →₀ ℕ) × SpecialFiberMonomialIndex n lam) : ℤ :=
  elementaryWeight i.1 + i.2.val.degree

theorem untruncatedCoefficientBasis_mem_piece
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (i : (Fin (n - lam.card) →₀ ℕ) × SpecialFiberMonomialIndex n lam) :
    untruncatedCoefficientBasis K n lam hk i ∈
      quotientIntegerPiece (untruncatedIdeal K n lam) (parameterBasisDegree i) := by
  rw [untruncatedCoefficientBasis, Basis.smulTower_apply,
    MvPolynomial.coe_basisMonomials, untruncatedMonomialParameterBasis_apply,
    Algebra.smul_def]
  apply quotientIntegerPiece_mul
    (untruncatedIdeal K n lam) (parameter_monomial_mem_piece K n lam i.1)
  exact quotientIntegerPiece_mk _ (MvPolynomial.isHomogeneous_monomial 1 rfl)

def quotientIntegerProjection {n : ℕ} (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K)) (d : ℤ) :
    Module.End K (PolynomialRing n K ⧸ I) :=
  if 0 ≤ d then quotientHomogeneousProjection I hI d.toNat else 0

theorem quotientIntegerProjection_fixed {n : ℕ} (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (d : ℤ) (x : PolynomialRing n K ⧸ I) (hx : x ∈ quotientIntegerPiece I d) :
    quotientIntegerProjection K I hI d x = x := by
  by_cases hd : 0 ≤ d
  · rw [quotientIntegerProjection, if_pos hd]
    exact quotientHomogeneousProjection_eq_self_of_mem I hI d.toNat
      (by simpa only [quotientIntegerPiece, if_pos hd] using hx)
  · have hx0 : x = 0 := by simpa only [quotientIntegerPiece, if_neg hd,
      Submodule.mem_bot] using hx
    simp only [hx0, map_zero]

theorem quotientIntegerProjection_of_mem {n : ℕ} (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    {e : ℤ} {x : PolynomialRing n K ⧸ I} (hx : x ∈ quotientIntegerPiece I e) (d : ℤ) :
    quotientIntegerProjection K I hI d x = if e = d then x else 0 := by
  by_cases he : 0 ≤ e
  · have hx' : x ∈ quotientHomogeneousPiece I e.toNat := by
      simpa only [quotientIntegerPiece, if_pos he] using hx
    obtain ⟨p, hp, rfl⟩ := hx'
    change quotientIntegerProjection K I hI d (Ideal.Quotient.mk I p) =
      if e = d then Ideal.Quotient.mk I p else 0
    by_cases hd : 0 ≤ d
    · simp only [quotientIntegerProjection, if_pos hd, quotientHomogeneousProjection_mk,
        MvPolynomial.homogeneousComponent_of_mem hp]
      by_cases hed : e = d
      · simp only [hed, if_pos, eq_self_iff_true, ite_true]
      · have hnat : d.toNat ≠ e.toNat := fun h => hed (by omega)
        simp only [if_neg hnat, if_neg hed, map_zero]
    · have hne : e ≠ d := by omega
      simp only [quotientIntegerProjection, if_neg hd, LinearMap.zero_apply, if_neg hne]
  · have hx0 : x = 0 := by simpa only [quotientIntegerPiece, if_neg he,
      Submodule.mem_bot] using hx
    simp only [hx0, map_zero, ite_self]

def untruncatedInternalGrading (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    InternalGrading K (UntruncatedRing K n lam) :=
  homogeneousBasisGrading (untruncatedCoefficientBasis K n lam hk) parameterBasisDegree

set_option maxRecDepth 4096 in
theorem untruncatedInternalGrading_piece
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    (untruncatedInternalGrading K n lam hk).piece =
      quotientIntegerPiece (untruncatedIdeal K n lam) := by
  exact homogeneousBasisGrading_piece_eq
    (untruncatedCoefficientBasis K n lam hk)
    (parameterBasisDegree (n := n) (lam := lam))
    (quotientIntegerPiece (untruncatedIdeal K n lam))
    (quotientIntegerProjection K (untruncatedIdeal K n lam)
      (untruncatedIdeal_isHomogeneous hk))
    (fun i => untruncatedCoefficientBasis_mem_piece K n lam hk i)
    (quotientIntegerProjection_fixed K (untruncatedIdeal K n lam)
      (untruncatedIdeal_isHomogeneous hk))
    (fun d i => quotientIntegerProjection_of_mem K (untruncatedIdeal K n lam)
      (untruncatedIdeal_isHomogeneous hk)
      (untruncatedCoefficientBasis_mem_piece K n lam hk i) d)

theorem parameterBasis_repr_homogeneous
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) {d : ℤ}
    {x : UntruncatedRing K n lam}
    (hx : x ∈ quotientIntegerPiece (untruncatedIdeal K n lam) d)
    (i : SpecialFiberMonomialIndex n lam) :
    (untruncatedMonomialParameterBasis K n lam hk).repr x i ∈
      elementaryWeightedPiece K (n - lam.card) (d - i.val.degree) := by
  intro a ha
  have hx' : x ∈ (untruncatedInternalGrading K n lam hk).piece d := by
    rwa [untruncatedInternalGrading_piece]
  have hcoord : (untruncatedCoefficientBasis K n lam hk).repr x (a, i) =
      ((untruncatedMonomialParameterBasis K n lam hk).repr x i).coeff a := by
    rw [untruncatedCoefficientBasis, Basis.smulTower_repr]
    rfl
  have heq := (mem_homogeneousBasisGrading_iff
    (untruncatedCoefficientBasis K n lam hk) parameterBasisDegree d x).mp hx' (a, i)
      (by rw [hcoord]; exact ha)
  rw [← elementaryWeight_cast]
  change (elementaryWeight a : ℤ) + i.val.degree = d at heq
  omega

end HigherSpecht
end
end CanonicalSource75

section CanonicalSource76
/- Source: HigherSpecht/CoordinateKoszulProjection.lean -/



/-!
# Genuine homogeneous projections on the coordinate Koszul complex

Projection acts on the actual polynomial-quotient coefficients of the
exterior basis.  Contracting increases coefficient degree by one, so the
projection identity below has exactly that shift.  It also proves that a
homogeneous cycle which is an ungraded boundary has a homogeneous primitive.
-/

noncomputable section

open TauCeti Module MvPolynomial CliffordAlgebra
open scoped Classical BigOperators

namespace HigherSpecht

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K] {n : ℕ}

theorem quotientIntegerProjection_mem (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (a : ℤ) (x : PolynomialRing n K ⧸ I) :
    quotientIntegerProjection K I hI a x ∈ quotientIntegerPiece I a := by
  by_cases ha : 0 ≤ a
  · rw [quotientIntegerProjection, if_pos ha, quotientIntegerPiece, if_pos ha]
    rw [← quotientHomogeneousProjection_range I hI a.toNat]
    exact ⟨x, rfl⟩
  · simp only [quotientIntegerProjection, if_neg ha, LinearMap.zero_apply,
      Submodule.zero_mem]

theorem quotientIntegerProjection_mul_variable (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (a : ℤ) (x : PolynomialRing n K ⧸ I) (j : Fin n) :
    quotientIntegerProjection K I hI (a + 1) (x * Ideal.Quotient.mk I (X j)) =
      quotientIntegerProjection K I hI a x * Ideal.Quotient.mk I (X j) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  by_cases ha : 0 ≤ a
  · have ha1 : 0 ≤ a + 1 := by omega
    have hnat : (a + 1).toNat - 1 = a.toNat := by omega
    have hdegree : 1 ≤ (a + 1).toNat := by omega
    simp only [quotientIntegerProjection, if_pos ha, if_pos ha1, ← map_mul,
      quotientHomogeneousProjection_mk, homogeneousComponent_mul_homogeneous_right
        p (X j) (MvPolynomial.isHomogeneous_X K j), if_pos hdegree, hnat]
  · by_cases ha1 : 0 ≤ a + 1
    · have haeq : a = -1 := by omega
      subst a
      simp only [neg_add_cancel, quotientIntegerProjection, show ¬ (0 : ℤ) ≤ -1 by omega,
        if_neg, show (0 : ℤ) ≤ 0 by omega, if_pos, Int.toNat_zero,
        LinearMap.zero_apply, zero_mul, ← map_mul, quotientHomogeneousProjection_mk,
        homogeneousComponent_mul_homogeneous_right p (X j) (MvPolynomial.isHomogeneous_X K j),
        show ¬ (1 : ℕ) ≤ 0 by omega, if_neg, ite_false, map_zero]
    · simp only [quotientIntegerProjection, if_neg ha, if_neg ha1,
        LinearMap.zero_apply, zero_mul]

def coordinateCoefficientProjection (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K)) (a : ℤ) :
    Module.End K (CoordinateKoszulCarrier I) :=
  ((coordinateKoszulBasis I).repr.symm.toLinearMap.restrictScalars K).comp
    ((Finsupp.mapRange.linearMap (quotientIntegerProjection K I hI a)).comp
      ((coordinateKoszulBasis I).repr.toLinearMap.restrictScalars K))

@[simp] theorem coordinateCoefficientProjection_repr
    (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (a : ℤ) (z : CoordinateKoszulCarrier I) (s : Finset (Fin n)) :
    (coordinateKoszulBasis I).repr (coordinateCoefficientProjection I hI a z) s =
      quotientIntegerProjection K I hI a ((coordinateKoszulBasis I).repr z s) := by
  simp only [coordinateCoefficientProjection, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply]

theorem coordinateCoefficientProjection_smul_basis
    (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (a : ℤ) (c : PolynomialRing n K ⧸ I) (s : Finset (Fin n)) :
    coordinateCoefficientProjection I hI a (c • coordinateKoszulBasis I s) =
      quotientIntegerProjection K I hI a c • coordinateKoszulBasis I s := by
  apply (coordinateKoszulBasis I).repr.injective
  ext t
  rw [coordinateCoefficientProjection_repr]
  simp only [map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
    smul_eq_mul]
  by_cases hst : s = t <;>
    simp only [hst, if_pos, if_neg, ite_true, ite_false, mul_one, mul_zero, map_zero]

theorem coordinateCoefficientProjection_mem
    (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (a i : ℤ) {z : CoordinateKoszulCarrier I}
    (hz : z ∈ coordinateHomologicalPiece I i) :
    coordinateCoefficientProjection I hI a z ∈ coordinateKoszulPiece I i a := by
  rw [mem_coordinateKoszulPiece]
  intro s
  rw [coordinateCoefficientProjection_repr]
  by_cases hs : (s.card : ℤ) = i
  · rw [if_pos hs]
    exact quotientIntegerProjection_mem I hI a _
  · rw [if_neg hs, (mem_coordinateHomologicalPiece I i z).mp hz s hs, map_zero]
    exact Submodule.zero_mem _

theorem coordinateKoszulPiece_le_homological
    (I : Ideal (PolynomialRing n K)) (i a : ℤ) :
    coordinateKoszulPiece I i a ≤ coordinateHomologicalPiece I i := by
  intro z hz
  rw [mem_coordinateHomologicalPiece]
  intro s hs
  have h := (mem_coordinateKoszulPiece I i a z).mp hz s
  simpa only [if_neg hs, Submodule.mem_bot] using h

theorem coordinateCoefficientProjection_fixed
    (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (i a : ℤ) {z : CoordinateKoszulCarrier I} (hz : z ∈ coordinateKoszulPiece I i a) :
    coordinateCoefficientProjection I hI a z = z := by
  apply (coordinateKoszulBasis I).repr.injective
  ext s
  rw [coordinateCoefficientProjection_repr]
  have hc := (mem_coordinateKoszulPiece I i a z).mp hz s
  by_cases hs : (s.card : ℤ) = i
  · rw [if_pos hs] at hc
    exact quotientIntegerProjection_fixed K I hI a _ hc
  · rw [if_neg hs] at hc
    simp only [show (coordinateKoszulBasis I).repr z s = 0 from hc, map_zero]

theorem coordinateCoefficientProjection_of_mem
    (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (i a b : ℤ) {z : CoordinateKoszulCarrier I} (hz : z ∈ coordinateKoszulPiece I i a) :
    coordinateCoefficientProjection I hI b z = if a = b then z else 0 := by
  apply (coordinateKoszulBasis I).repr.injective
  ext s
  rw [coordinateCoefficientProjection_repr]
  have hc := (mem_coordinateKoszulPiece I i a z).mp hz s
  by_cases hs : (s.card : ℤ) = i
  · rw [if_pos hs] at hc
    rw [quotientIntegerProjection_of_mem K I hI hc b]
    split_ifs <;> simp only [map_zero, Finsupp.zero_apply]
  · rw [if_neg hs] at hc
    have hzero : (coordinateKoszulBasis I).repr z s = 0 := hc
    by_cases hab : a = b
    · simp only [if_pos hab, hzero, map_zero]
    · simp only [if_neg hab, hzero, map_zero, Finsupp.zero_apply]

set_option backward.isDefEq.respectTransparency false in
theorem coordinateDifferential_smul_basis_signed
    (I : Ideal (PolynomialRing n K)) (c : PolynomialRing n K ⧸ I)
    (s : Finset (Fin n)) :
    coordinateKoszulDifferential I (c • coordinateKoszulBasis I s) =
      ∑ j : Fin n, if j ∈ s then
        (((TauCeti.ExteriorAlgebra.basisEraseSign j s : ℤ) : K)) •
          ((c * Ideal.Quotient.mk I (X j)) • coordinateKoszulBasis I (s.erase j))
        else 0 := by
  rw [coordinateKoszulDifferential_smul, coordinateKoszulDifferential_basis]
  rw [Finset.smul_sum (M := PolynomialRing n K ⧸ I)
    (N := CoordinateKoszulCarrier I) (r := c)]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hjs : j ∈ s
  · simp only [if_pos hjs, Units.smul_def]
    change c • (Ideal.Quotient.mk I (X j) •
        ((TauCeti.ExteriorAlgebra.basisEraseSign j s : ℤ) •
          coordinateKoszulBasis I (s.erase j))) =
      (((TauCeti.ExteriorAlgebra.basisEraseSign j s : ℤ) : K)) •
        ((c * Ideal.Quotient.mk I (X j)) • coordinateKoszulBasis I (s.erase j))
    exact
      (smul_smul c (Ideal.Quotient.mk I (X j))
        ((TauCeti.ExteriorAlgebra.basisEraseSign j s : ℤ) •
          coordinateKoszulBasis I (s.erase j))).trans
        ((smul_comm (c * Ideal.Quotient.mk I (X j))
          (TauCeti.ExteriorAlgebra.basisEraseSign j s : ℤ)
          (coordinateKoszulBasis I (s.erase j))).trans
          (Int.cast_smul_eq_zsmul K
            (TauCeti.ExteriorAlgebra.basisEraseSign j s : ℤ)
            ((c * Ideal.Quotient.mk I (X j)) • coordinateKoszulBasis I (s.erase j))).symm)
  · simpa only [if_neg hjs] using
      (smul_zero c : c • (0 : CoordinateKoszulCarrier I) = 0)


theorem coordinateCoefficientProjection_differential
    (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (a : ℤ) (z : CoordinateKoszulCarrier I) :
    coordinateCoefficientProjection I hI (a + 1) (coordinateKoszulDifferential I z) =
      coordinateKoszulDifferential I (coordinateCoefficientProjection I hI a z) := by
  rw [← (coordinateKoszulBasis I).sum_repr z]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [coordinateCoefficientProjection_smul_basis,
    coordinateDifferential_smul_basis_signed, coordinateDifferential_smul_basis_signed,
    map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs with hjs
  · rw [map_smul, coordinateCoefficientProjection_smul_basis,
      quotientIntegerProjection_mul_variable]
  · exact map_zero _

theorem homogeneous_coordinate_boundary_lift
    (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (i a : ℤ) {z : CoordinateKoszulCarrier I}
    (hz : z ∈ coordinateKoszulPiece I i a)
    (hb : z ∈ (coordinateDifferentialGrading I).boundaries i) :
    z ∈ coordinateKoszulBoundaries I i a := by
  obtain ⟨y, hy, hdy⟩ := hb
  change coordinateKoszulDifferential I y = z at hdy
  refine ⟨coordinateCoefficientProjection I hI (a - 1) y,
    coordinateCoefficientProjection_mem I hI (a - 1) (i + 1) hy, ?_⟩
  rw [← coordinateCoefficientProjection_differential, sub_add_cancel, hdy]
  exact coordinateCoefficientProjection_fixed I hI i a hz

end HigherSpecht
end
end CanonicalSource76

section CanonicalSource77
/- Source: HigherSpecht/CoordinateKoszulInternalGrading.lean -/



/-!
# The actual internal grading of the coefficient-extended Koszul complex

A homogeneous basis of the polynomial quotient gives a basis of each
actual exterior-power term.  Its assigned degree is the polynomial degree
plus the exterior degree.  The pieces are independently identified with
the literal polynomial homogeneous pieces.  Kernel and boundary
homogeneity are then proved using coefficient projections, and the
resulting quotient grading is the grading of the actual homology.
-/

noncomputable section

open Module TauCeti CliffordAlgebra DirectSum
open scoped Classical

namespace HigherSpecht

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K] {n : ℕ} {ι : Type*}

/-- The homogeneous projection belonging to a genuine internal direct sum. -/
def koszulInternalProjection {M : Type*} [AddCommGroup M] [Module K M]
    (G : InternalGrading K M) (j : ℤ) : Module.End K M where
  toFun z := (DirectSum.decompose G.piece z j : M)
  map_add' x y := by
    simp only [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
  map_smul' c z := by
    simp only [DirectSum.decompose_smul, DirectSum.smul_apply, Submodule.coe_smul_of_tower,
      RingHom.id_apply]

def coordinateTermBasis (I : Ideal (PolynomialRing n K))
    (b : Basis ι K (PolynomialRing n K ⧸ I)) (i : ℕ) :
    Basis (ι × Set.powersetCard (Fin n) i) K (coordinateHomologicalPiece I (i : ℤ)) :=
  (b.smulTower ((Pi.basisFun (PolynomialRing n K ⧸ I) (Fin n)).exteriorPower i)).map
    (coordinateExteriorEquiv I i).symm

@[simp] theorem coordinateTermBasis_val (I : Ideal (PolynomialRing n K))
    (b : Basis ι K (PolynomialRing n K ⧸ I)) (i : ℕ)
    (t : ι × Set.powersetCard (Fin n) i) :
    (coordinateTermBasis I b i t).val = b t.1 • coordinateKoszulBasis I t.2.val := by
  simp only [coordinateTermBasis, Basis.map_apply, Basis.smulTower_apply]
  change b t.1 • (((Pi.basisFun (PolynomialRing n K ⧸ I) (Fin n)).exteriorPower i t.2) :
    CoordinateKoszulCarrier I) = _
  rw [← ExteriorAlgebra.basis_eq_coe_basis]
  rfl

def coordinateTermGrading (I : Ideal (PolynomialRing n K))
    (b : Basis ι K (PolynomialRing n K ⧸ I)) (degree : ι → ℤ) (i : ℕ) :
    InternalGrading K (coordinateHomologicalPiece I (i : ℤ)) :=
  homogeneousBasisGrading (coordinateTermBasis I b i) (fun t => degree t.1 + i)

def coordinateTermProjection (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K)) (i : ℕ) (j : ℤ) :
    Module.End K (coordinateHomologicalPiece I (i : ℤ)) :=
  (coordinateCoefficientProjection I hI (j - i)).restrict fun z hz =>
    coordinateKoszulPiece_le_homological I i (j - i)
      (coordinateCoefficientProjection_mem I hI (j - i) i hz)

theorem coordinateTermGrading_piece (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (b : Basis ι K (PolynomialRing n K ⧸ I)) (degree : ι → ℤ)
    (hb : ∀ t, b t ∈ quotientIntegerPiece I (degree t)) (i : ℕ) :
    (coordinateTermGrading I b degree i).piece = fun j =>
      (coordinateKoszulPiece I i (j - i)).comap (coordinateHomologicalPiece I i).subtype := by
  apply homogeneousBasisGrading_piece_eq _ _ _ (coordinateTermProjection I hI i)
  · intro t
    change (coordinateTermBasis I b i t).val ∈
      coordinateKoszulPiece I i ((degree t.1 + i) - i)
    rw [coordinateTermBasis_val]
    have h := coordinateKoszulPiece_generator I t.2.val
      (show (t.2.val.card : ℤ) = i by exact_mod_cast t.2.property) (hb t.1)
    simpa only [add_sub_cancel_right] using h
  · intro j z hz
    apply Subtype.ext
    exact coordinateCoefficientProjection_fixed I hI i (j - i) hz
  · intro j t
    apply Subtype.ext
    change coordinateCoefficientProjection I hI (j - i)
      (coordinateTermBasis I b i t).val = _
    rw [coordinateTermBasis_val]
    have hmem := coordinateKoszulPiece_generator I t.2.val
      (show (t.2.val.card : ℤ) = i by exact_mod_cast t.2.property) (hb t.1)
    rw [coordinateCoefficientProjection_of_mem I hI i (degree t.1) (j - i) hmem]
    by_cases ht : degree t.1 + i = j
    · have heq : degree t.1 = j - i := by omega
      simp only [if_pos ht, if_pos heq, coordinateTermBasis_val]
    · have hne : degree t.1 ≠ j - i := by omega
      simp only [if_neg ht, if_neg hne, Submodule.coe_zero]

theorem mem_coordinateTermGrading (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (b : Basis ι K (PolynomialRing n K ⧸ I)) (degree : ι → ℤ)
    (hb : ∀ t, b t ∈ quotientIntegerPiece I (degree t)) (i : ℕ) (j : ℤ)
    (z : coordinateHomologicalPiece I (i : ℤ)) :
    z ∈ (coordinateTermGrading I b degree i).piece j ↔
      z.val ∈ coordinateKoszulPiece I i (j - i) := by
  rw [coordinateTermGrading_piece I hI b degree hb i]
  rfl

theorem coordinateTerm_decompose (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (b : Basis ι K (PolynomialRing n K ⧸ I)) (degree : ι → ℤ)
    (hb : ∀ t, b t ∈ quotientIntegerPiece I (degree t)) (i : ℕ) (j : ℤ)
    (z : coordinateHomologicalPiece I (i : ℤ)) :
    ((DirectSum.decompose (coordinateTermGrading I b degree i).piece z j :
      coordinateHomologicalPiece I (i : ℤ)) : CoordinateKoszulCarrier I) =
      coordinateCoefficientProjection I hI (j - i) z.val := by
  let G := coordinateTermGrading I b degree i
  have heq : (coordinateHomologicalPiece I i).subtype.comp (koszulInternalProjection G j) =
      (coordinateCoefficientProjection I hI (j - i)).comp
        (coordinateHomologicalPiece I i).subtype := by
    apply G.linearMap_ext
    intro q x hx
    have hpiece := (mem_coordinateTermGrading I hI b degree hb i q x).mp hx
    change ((DirectSum.decompose G.piece x j : coordinateHomologicalPiece I i) :
      CoordinateKoszulCarrier I) = coordinateCoefficientProjection I hI (j - i) x.val
    by_cases hqj : q = j
    · subst q
      rw [DirectSum.decompose_of_mem_same G.piece hx]
      exact (coordinateCoefficientProjection_fixed I hI i (j - i) hpiece).symm
    · rw [DirectSum.decompose_of_mem_ne G.piece hx hqj,
        coordinateCoefficientProjection_of_mem I hI i (q - i) (j - i) hpiece,
        if_neg (by omega : q - (i : ℤ) ≠ j - i)]
      rfl
  exact DFunLike.congr_fun heq z

def coordinateCyclesInTerm (I : Ideal (PolynomialRing n K)) (i : ℕ) :
    Submodule K (coordinateHomologicalPiece I (i : ℤ)) :=
  LinearMap.ker ((coordinateKoszulDifferential I).comp
    (coordinateHomologicalPiece I i).subtype)

def coordinateTermCyclesEquiv (I : Ideal (PolynomialRing n K)) (i : ℕ) :
    coordinateCyclesInTerm I i ≃ₗ[K] (coordinateDifferentialGrading I).cycles (i : ℤ) where
  toFun z := ⟨z.val.val, z.val.property, z.property⟩
  invFun z := ⟨⟨z.val, z.property.1⟩, z.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coordinateCyclesInTerm_homogeneous (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (b : Basis ι K (PolynomialRing n K ⧸ I)) (degree : ι → ℤ)
    (hb : ∀ t, b t ∈ quotientIntegerPiece I (degree t)) (i : ℕ) :
    SetLike.IsHomogeneous (coordinateTermGrading I b degree i).piece
      (coordinateCyclesInTerm I i) := by
  intro j z hz
  change coordinateKoszulDifferential I
    (((DirectSum.decompose (coordinateTermGrading I b degree i).piece z j :
      coordinateHomologicalPiece I i) : CoordinateKoszulCarrier I)) = 0
  rw [coordinateTerm_decompose I hI b degree hb i j z,
    ← coordinateCoefficientProjection_differential]
  change coordinateCoefficientProjection I hI (j - i + 1)
    (coordinateKoszulDifferential I z.val) = 0
  rw [show coordinateKoszulDifferential I z.val = 0 from hz, map_zero]

def coordinateCyclesGrading (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (b : Basis ι K (PolynomialRing n K ⧸ I)) (degree : ι → ℤ)
    (hb : ∀ t, b t ∈ quotientIntegerPiece I (degree t)) (i : ℕ) :
    InternalGrading K ((coordinateDifferentialGrading I).cycles (i : ℤ)) :=
  ((coordinateTermGrading I b degree i).submodule (coordinateCyclesInTerm I i)
    (coordinateCyclesInTerm_homogeneous I hI b degree hb i)).map
      (coordinateTermCyclesEquiv I i)

theorem mem_coordinateCyclesGrading (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (b : Basis ι K (PolynomialRing n K ⧸ I)) (degree : ι → ℤ)
    (hb : ∀ t, b t ∈ quotientIntegerPiece I (degree t)) (i : ℕ) (j : ℤ)
    (z : (coordinateDifferentialGrading I).cycles (i : ℤ)) :
    z ∈ (coordinateCyclesGrading I hI b degree hb i).piece j ↔
      z.val ∈ coordinateKoszulPiece I i (j - i) := by
  rw [coordinateCyclesGrading, InternalGrading.mem_map_piece_iff,
    InternalGrading.mem_submodule_piece]
  exact mem_coordinateTermGrading I hI b degree hb i j _

theorem coordinateCycles_decompose (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (b : Basis ι K (PolynomialRing n K ⧸ I)) (degree : ι → ℤ)
    (hb : ∀ t, b t ∈ quotientIntegerPiece I (degree t)) (i : ℕ) (j : ℤ)
    (z : (coordinateDifferentialGrading I).cycles (i : ℤ)) :
    ((DirectSum.decompose (coordinateCyclesGrading I hI b degree hb i).piece z j :
      (coordinateDifferentialGrading I).cycles (i : ℤ)) : CoordinateKoszulCarrier I) =
      coordinateCoefficientProjection I hI (j - i) z.val := by
  let G := coordinateCyclesGrading I hI b degree hb i
  have heq : ((coordinateDifferentialGrading I).cycles i).subtype.comp
      (koszulInternalProjection G j) =
      (coordinateCoefficientProjection I hI (j - i)).comp
        ((coordinateDifferentialGrading I).cycles i).subtype := by
    apply G.linearMap_ext
    intro q x hx
    have hpiece := (mem_coordinateCyclesGrading I hI b degree hb i q x).mp hx
    change ((DirectSum.decompose G.piece x j : (coordinateDifferentialGrading I).cycles i) :
      CoordinateKoszulCarrier I) = coordinateCoefficientProjection I hI (j - i) x.val
    by_cases hqj : q = j
    · subst q
      rw [DirectSum.decompose_of_mem_same G.piece hx]
      exact (coordinateCoefficientProjection_fixed I hI i (j - i) hpiece).symm
    · rw [DirectSum.decompose_of_mem_ne G.piece hx hqj,
        coordinateCoefficientProjection_of_mem I hI i (q - i) (j - i) hpiece,
        if_neg (by omega : q - (i : ℤ) ≠ j - i)]
      rfl
  exact DFunLike.congr_fun heq z

theorem coordinateTotalBoundaries_homogeneous (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (b : Basis ι K (PolynomialRing n K ⧸ I)) (degree : ι → ℤ)
    (hb : ∀ t, b t ∈ quotientIntegerPiece I (degree t)) (i : ℕ) :
    SetLike.IsHomogeneous (coordinateCyclesGrading I hI b degree hb i).piece
      (((coordinateDifferentialGrading I).boundaries i).comap
        ((coordinateDifferentialGrading I).cycles i).subtype) := by
  intro j z hz
  change ((DirectSum.decompose (coordinateCyclesGrading I hI b degree hb i).piece z j :
    (coordinateDifferentialGrading I).cycles i) : CoordinateKoszulCarrier I) ∈
      (coordinateDifferentialGrading I).boundaries i
  rw [coordinateCycles_decompose I hI b degree hb i j z]
  obtain ⟨y, hy, hdy⟩ := hz
  refine ⟨coordinateCoefficientProjection I hI (j - i - 1) y, ?_, ?_⟩
  · exact coordinateKoszulPiece_le_homological I (i + 1) (j - i - 1)
      (coordinateCoefficientProjection_mem I hI (j - i - 1) (i + 1) hy)
  · change coordinateKoszulDifferential I
        (coordinateCoefficientProjection I hI (j - i - 1) y) =
      coordinateCoefficientProjection I hI (j - i) z.val
    change coordinateKoszulDifferential I y = z.val at hdy
    rw [← coordinateCoefficientProjection_differential, sub_add_cancel, hdy]

def coordinateTotalHomologyGrading (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (b : Basis ι K (PolynomialRing n K ⧸ I)) (degree : ι → ℤ)
    (hb : ∀ t, b t ∈ quotientIntegerPiece I (degree t)) (i : ℕ) :
    InternalGrading K (TotalCoordinateKoszulHomology I (i : ℤ)) :=
  (coordinateCyclesGrading I hI b degree hb i).quotient
    (((coordinateDifferentialGrading I).boundaries i).comap
      ((coordinateDifferentialGrading I).cycles i).subtype)
    (coordinateTotalBoundaries_homogeneous I hI b degree hb i)

/-- The grading on actual homology is represented by polynomial-homogeneous
cycles of coefficient degree `j-i`, exactly as in the tensor resolution. -/
theorem mem_coordinateTotalHomologyGrading (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (b : Basis ι K (PolynomialRing n K ⧸ I)) (degree : ι → ℤ)
    (hb : ∀ t, b t ∈ quotientIntegerPiece I (degree t)) (i : ℕ) (j : ℤ)
    (x : TotalCoordinateKoszulHomology I (i : ℤ)) :
    x ∈ (coordinateTotalHomologyGrading I hI b degree hb i).piece j ↔
      ∃ z : (coordinateDifferentialGrading I).cycles (i : ℤ),
        z.val ∈ coordinateKoszulPiece I i (j - i) ∧
          (coordinateDifferentialGrading I).homologyClass i z = x := by
  rw [coordinateTotalHomologyGrading, InternalGrading.mem_quotient_piece_iff]
  apply exists_congr
  intro z
  rw [mem_coordinateCyclesGrading I hI b degree hb i j z]
  rfl

end HigherSpecht
end
end CanonicalSource77

section CanonicalSource78
/- Source: HigherSpecht/PolynomialTorGrading.lean -/



/-!
# Homogeneous components of the actual polynomial-ring Tor objects

The internal grading is transported from the proved grading of the
coefficient-extended variable Koszul resolution.  The component
comparison is an isomorphism: a homogeneous cycle that is an ungraded
boundary has a homogeneous primitive.  Thus both vanishing and nonvanishing
are transported, in every homological and internal degree.
-/

noncomputable section

open Module TauCeti
open scoped Classical

namespace HigherSpecht

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K] {n : ℕ} {ι : Type*}

def homogeneousCoordinateCyclesInTotal (I : Ideal (PolynomialRing n K)) (i a : ℤ) :
    coordinateKoszulCycles I i a →ₗ[K] (coordinateDifferentialGrading I).cycles i where
  toFun z := ⟨z.val, coordinateKoszulPiece_le_homological I i a z.property.1, z.property.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def homogeneousCoordinateHomologyToTotal (I : Ideal (PolynomialRing n K)) (i a : ℤ) :
    CoordinateKoszulHomology I i a →ₗ[K] TotalCoordinateKoszulHomology I i :=
  ((coordinateKoszulBoundaries I i a).comap (coordinateKoszulCycles I i a).subtype).liftQ
    (((coordinateDifferentialGrading I).homologyClass i).comp
      (homogeneousCoordinateCyclesInTotal I i a)) (by
        intro z hz
        apply ((coordinateDifferentialGrading I).homologyClass_eq_zero_iff i _).mpr
        obtain ⟨y, hy, hdy⟩ := hz
        exact ⟨y, coordinateKoszulPiece_le_homological I (i + 1) (a - 1) hy, hdy⟩)

@[simp] theorem homogeneousCoordinateHomologyToTotal_mk
    (I : Ideal (PolynomialRing n K)) (i a : ℤ) (z : coordinateKoszulCycles I i a) :
    homogeneousCoordinateHomologyToTotal I i a (Submodule.Quotient.mk z) =
      (coordinateDifferentialGrading I).homologyClass i
        (homogeneousCoordinateCyclesInTotal I i a z) := rfl

theorem homogeneousCoordinateHomologyToTotal_injective
    (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K)) (i a : ℤ) :
    Function.Injective (homogeneousCoordinateHomologyToTotal I i a) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  obtain ⟨z, rfl⟩ := ((coordinateKoszulBoundaries I i a).comap
    (coordinateKoszulCycles I i a).subtype).mkQ_surjective x
  change homogeneousCoordinateHomologyToTotal I i a (Submodule.Quotient.mk z) = 0 at hx
  rw [homogeneousCoordinateHomologyToTotal_mk] at hx
  have hb := ((coordinateDifferentialGrading I).homologyClass_eq_zero_iff i _).mp hx
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact homogeneous_coordinate_boundary_lift I hI i a z.property.1 hb

theorem homogeneousCoordinateHomologyToTotal_range
    (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (b : Basis ι K (PolynomialRing n K ⧸ I)) (degree : ι → ℤ)
    (hb : ∀ t, b t ∈ quotientIntegerPiece I (degree t)) (i : ℕ) (j : ℤ) :
    LinearMap.range (homogeneousCoordinateHomologyToTotal I i (j - i)) =
      (coordinateTotalHomologyGrading I hI b degree hb i).piece j := by
  ext x
  rw [mem_coordinateTotalHomologyGrading I hI b degree hb i j x]
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := ((coordinateKoszulBoundaries I i (j - i)).comap
      (coordinateKoszulCycles I i (j - i)).subtype).mkQ_surjective y
    exact ⟨homogeneousCoordinateCyclesInTotal I i (j - i) z, z.property.1, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨Submodule.Quotient.mk (⟨z.val, hz, z.property.2⟩ :
      coordinateKoszulCycles I i (j - i)), rfl⟩

def homogeneousCoordinateTotalComponentEquiv
    (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (b : Basis ι K (PolynomialRing n K ⧸ I)) (degree : ι → ℤ)
    (hb : ∀ t, b t ∈ quotientIntegerPiece I (degree t)) (i : ℕ) (j : ℤ) :
    CoordinateKoszulHomology I i (j - i) ≃ₗ[K]
      (coordinateTotalHomologyGrading I hI b degree hb i).piece j :=
  (LinearEquiv.ofInjective (homogeneousCoordinateHomologyToTotal I i (j - i))
    (homogeneousCoordinateHomologyToTotal_injective I hI i (j - i))).trans
      (LinearEquiv.ofEq _ _
        (homogeneousCoordinateHomologyToTotal_range I hI b degree hb i j))

/-- The actual derived tensor object, graded through the actual graded
variable Koszul resolution.  The ring's polynomial grading is retained. -/
def polynomialTorGrading (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (b : Basis ι K (PolynomialRing n K ⧸ I)) (degree : ι → ℤ)
    (hb : ∀ t, b t ∈ quotientIntegerPiece I (degree t)) (i : ℕ) :
    InternalGrading K (PolynomialTor K n I i) :=
  (coordinateTotalHomologyGrading I hI b degree hb i).map
    (polynomialTorCoordinateEquiv K n I i).symm

theorem mem_polynomialTorGrading (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (b : Basis ι K (PolynomialRing n K ⧸ I)) (degree : ι → ℤ)
    (hb : ∀ t, b t ∈ quotientIntegerPiece I (degree t)) (i : ℕ) (j : ℤ)
    (x : PolynomialTor K n I i) :
    x ∈ (polynomialTorGrading I hI b degree hb i).piece j ↔
      ∃ z : (coordinateDifferentialGrading I).cycles (i : ℤ),
        z.val ∈ coordinateKoszulPiece I i (j - i) ∧
          (coordinateDifferentialGrading I).homologyClass i z =
            polynomialTorCoordinateEquiv K n I i x := by
  rw [polynomialTorGrading, InternalGrading.mem_map_piece_iff]
  exact mem_coordinateTotalHomologyGrading I hI b degree hb i j _

/-- The grading does not depend on the chosen homogeneous basis.  Its
pieces are the images of the intrinsic polynomial-homogeneous cycles. -/
theorem polynomialTorGrading_independent {κ : Type*}
    (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (b : Basis ι K (PolynomialRing n K ⧸ I)) (degree : ι → ℤ)
    (hb : ∀ t, b t ∈ quotientIntegerPiece I (degree t))
    (c : Basis κ K (PolynomialRing n K ⧸ I)) (degree' : κ → ℤ)
    (hc : ∀ t, c t ∈ quotientIntegerPiece I (degree' t)) (i : ℕ) :
    polynomialTorGrading I hI b degree hb i = polynomialTorGrading I hI c degree' hc i := by
  apply InternalGrading.ext
  intro j
  ext x
  rw [mem_polynomialTorGrading I hI b degree hb i j x,
    mem_polynomialTorGrading I hI c degree' hc i j x]

/-- Every homogeneous component is identified, with the exact shift
`internal degree = homological degree + coefficient degree`. -/
def polynomialTorHomogeneousComponentEquiv
    (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (b : Basis ι K (PolynomialRing n K ⧸ I)) (degree : ι → ℤ)
    (hb : ∀ t, b t ∈ quotientIntegerPiece I (degree t)) (i : ℕ) (j : ℤ) :
    CoordinateKoszulHomology I i (j - i) ≃ₗ[K]
      (polynomialTorGrading I hI b degree hb i).piece j :=
  (homogeneousCoordinateTotalComponentEquiv I hI b degree hb i j).trans
    (Submodule.equivMapOfInjective (polynomialTorCoordinateEquiv K n I i).symm.toLinearMap
      (polynomialTorCoordinateEquiv K n I i).symm.injective
      ((coordinateTotalHomologyGrading I hI b degree hb i).piece j))

theorem polynomialTor_piece_subsingleton_iff
    (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (b : Basis ι K (PolynomialRing n K ⧸ I)) (degree : ι → ℤ)
    (hb : ∀ t, b t ∈ quotientIntegerPiece I (degree t)) (i : ℕ) (j : ℤ) :
    Subsingleton ((polynomialTorGrading I hI b degree hb i).piece j) ↔
      Subsingleton (CoordinateKoszulHomology I i (j - i)) := by
  let e := polynomialTorHomogeneousComponentEquiv I hI b degree hb i j
  constructor
  · intro h
    letI := h
    exact ⟨fun x y => e.injective (Subsingleton.elim _ _)⟩
  · intro h
    letI := h
    exact ⟨fun x y => e.symm.injective (Subsingleton.elim _ _)⟩

theorem coordinateKoszulHomology_subsingleton_of_homological_outside
    (I : Ideal (PolynomialRing n K)) {i a : ℤ} (hi : i < 0 ∨ (n : ℤ) < i) :
    Subsingleton (CoordinateKoszulHomology I i a) := by
  have hc : coordinateKoszulCycles I i a = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro z hz
    have hp := coordinateKoszulPiece_le_homological I i a hz.1
    rw [coordinateHomologicalPiece_eq_bot I hi] at hp
    exact hp
  letI : Subsingleton (coordinateKoszulCycles I i a) := by
    rw [hc]
    infer_instance
  infer_instance

theorem coordinateKoszulHomology_subsingleton_of_coefficient_neg
    (I : Ideal (PolynomialRing n K)) {i a : ℤ} (ha : a < 0) :
    Subsingleton (CoordinateKoszulHomology I i a) := by
  have hc : coordinateKoszulCycles I i a = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro z hz
    apply (coordinateKoszulBasis I).repr.injective
    ext s
    rw [map_zero, Finsupp.zero_apply]
    have h := (mem_coordinateKoszulPiece I i a z).mp hz.1 s
    by_cases hs : (s.card : ℤ) = i
    · simpa only [if_pos hs, quotientIntegerPiece, if_neg (by omega : ¬ 0 ≤ a),
        Submodule.mem_bot] using h
    · simpa only [if_neg hs, Submodule.mem_bot] using h
  letI : Subsingleton (coordinateKoszulCycles I i a) := by
    rw [hc]
    infer_instance
  infer_instance

theorem polynomialTor_piece_subsingleton_of_below_diagonal
    (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (b : Basis ι K (PolynomialRing n K ⧸ I)) (degree : ι → ℤ)
    (hb : ∀ t, b t ∈ quotientIntegerPiece I (degree t)) (i : ℕ) (j : ℤ)
    (hji : j < i) : Subsingleton ((polynomialTorGrading I hI b degree hb i).piece j) :=
  (polynomialTor_piece_subsingleton_iff I hI b degree hb i j).mpr
    (coordinateKoszulHomology_subsingleton_of_coefficient_neg I (by omega))

/-- The standard support characterization of regularity in actual Tor.
The upper bound quantifies over every homological and internal degree; the
second clause witnesses its attained, exact value. -/
def HasPolynomialTorRegularity (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (b : Basis ι K (PolynomialRing n K ⧸ I)) (degree : ι → ℤ)
    (hb : ∀ t, b t ∈ quotientIntegerPiece I (degree t)) (r : ℤ) : Prop :=
  (∀ (i : ℕ) (j : ℤ), r < j - i →
    Subsingleton ((polynomialTorGrading I hI b degree hb i).piece j)) ∧
    ∃ i : ℕ, ¬ Subsingleton ((polynomialTorGrading I hI b degree hb i).piece (i + r))

theorem polynomialTor_vanishesAbove_iff
    (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (b : Basis ι K (PolynomialRing n K ⧸ I)) (degree : ι → ℤ)
    (hb : ∀ t, b t ∈ quotientIntegerPiece I (degree t)) (r : ℤ) :
    (∀ (i : ℕ) (j : ℤ), r < j - i →
      Subsingleton ((polynomialTorGrading I hI b degree hb i).piece j)) ↔
        KoszulRegularityLE I r := by
  rw [koszulRegularityLE_iff_homology]
  constructor
  · intro h q a ha
    by_cases hq : 0 ≤ q
    · have hh := (polynomialTor_piece_subsingleton_iff I hI b degree hb
        q.toNat (q + a)).mp (h q.toNat (q + a) (by omega))
      simpa only [Int.toNat_of_nonneg hq, add_sub_cancel_left] using hh
    · exact coordinateKoszulHomology_subsingleton_of_homological_outside I
        (Or.inl (by omega))
  · intro h i j hj
    exact (polynomialTor_piece_subsingleton_iff I hI b degree hb i j).mpr
      (h i (j - i) hj)

/-- Full equivalence with the earlier coordinate formulation, including
all degrees, sharpness, and the zero-variable ring. -/
theorem hasPolynomialTorRegularity_iff
    (I : Ideal (PolynomialRing n K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (b : Basis ι K (PolynomialRing n K ⧸ I)) (degree : ι → ℤ)
    (hb : ∀ t, b t ∈ quotientIntegerPiece I (degree t)) (r : ℤ) :
    HasPolynomialTorRegularity I hI b degree hb r ↔ HasKoszulRegularity I r := by
  rw [HasPolynomialTorRegularity, hasKoszulRegularity_iff_homology_support]
  constructor
  · rintro ⟨hupper, i, hnonzero⟩
    refine ⟨?_, i, ?_⟩
    · intro q a ha
      by_cases hq : 0 ≤ q
      · have h := (polynomialTor_piece_subsingleton_iff I hI b degree hb
          q.toNat (q + a)).mp (hupper q.toNat (q + a) (by omega))
        simpa only [Int.toNat_of_nonneg hq, add_sub_cancel_left] using h
      · exact coordinateKoszulHomology_subsingleton_of_homological_outside I
          (Or.inl (by omega))
    · intro h
      apply hnonzero
      apply (polynomialTor_piece_subsingleton_iff I hI b degree hb i (i + r)).mpr
      simpa only [add_sub_cancel_left] using h
  · rintro ⟨hupper, q, hnonzero⟩
    have hq : 0 ≤ q := by
      by_contra hq
      exact hnonzero (coordinateKoszulHomology_subsingleton_of_homological_outside I
        (Or.inl (by omega)))
    refine ⟨?_, q.toNat, ?_⟩
    · intro i j hj
      exact (polynomialTor_piece_subsingleton_iff I hI b degree hb i j).mpr
        (hupper i (j - i) hj)
    · intro h
      apply hnonzero
      have hh := (polynomialTor_piece_subsingleton_iff I hI b degree hb q.toNat
        ((q.toNat : ℤ) + r)).mp h
      simpa only [Int.toNat_of_nonneg hq, add_sub_cancel_left] using hh

end HigherSpecht
end
end CanonicalSource78

section CanonicalSource79
/- Source: HigherSpecht/UntruncatedTorRegularity.lean -/



/-!
# Corollary 7.5 as a statement about the actual derived Tor functor

The ring is the manuscript's actual untruncated polynomial quotient.
Its Tor objects are Mathlib's derived tensor objects with the genuine
constant-coefficient residue field.  Their internal grading comes from
the graded variable Koszul resolution and has been proved independent of
the homogeneous basis used to construct it.  No characteristic, positive
variable-count, or additional regular-sequence hypothesis is imposed.
-/

noncomputable section

open Module TauCeti
open scoped Classical

namespace HigherSpecht

variable (K : Type*) [Field K]

def untruncatedTorGrading (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (i : ℕ) :
    InternalGrading K (PolynomialTor K n (untruncatedIdeal K n lam) i) :=
  polynomialTorGrading (untruncatedIdeal K n lam) (untruncatedIdeal_isHomogeneous hk)
    (untruncatedCoefficientBasis K n lam hk) parameterBasisDegree
    (untruncatedCoefficientBasis_mem_piece K n lam hk) i

abbrev UntruncatedTorPiece (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (i : ℕ) (j : ℤ) := (untruncatedTorGrading K n lam hk i).piece j

/-- The exact support-based regularity of the actual Tor groups. -/
def HasUntruncatedTorRegularity (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (r : ℤ) : Prop :=
  (∀ (i : ℕ) (j : ℤ), r < j - i → Subsingleton (UntruncatedTorPiece K n lam hk i j)) ∧
    ∃ i : ℕ, ¬ Subsingleton (UntruncatedTorPiece K n lam hk i (i + r))

theorem hasUntruncatedTorRegularity_iff (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (r : ℤ) :
    HasUntruncatedTorRegularity K n lam hk r ↔
      HasKoszulRegularity (untruncatedIdeal K n lam) r :=
  hasPolynomialTorRegularity_iff (untruncatedIdeal K n lam)
    (untruncatedIdeal_isHomogeneous hk) (untruncatedCoefficientBasis K n lam hk)
    parameterBasisDegree (untruncatedCoefficientBasis_mem_piece K n lam hk) r

/-- Corollary 7.5, with the genuine graded Tor interpretation proved. -/
theorem corollary_7_5_tor_regularity (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    HasUntruncatedTorRegularity K n lam hk
      ((springerTopDegree lam : ℤ) + (n - lam.card : ℕ) * (lam.colLen 0 : ℤ)) :=
  (hasUntruncatedTorRegularity_iff K n lam hk _).mpr
    (corollary_7_5_regularity K n lam hk)

/-- All excluded bidegrees vanish: homological degree above `n`, internal
degree below the diagonal, or regularity degree above the printed bound.
The endpoint is attained in a genuine nonzero Tor component. -/
theorem corollary_7_5_tor_support (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    let r : ℤ := (springerTopDegree lam : ℤ) +
      (n - lam.card : ℕ) * (lam.colLen 0 : ℤ)
    (∀ (i : ℕ) (j : ℤ), n < i ∨ j < i ∨ r < j - i →
      Subsingleton (UntruncatedTorPiece K n lam hk i j)) ∧
      ∃ i : ℕ, i ≤ n ∧ ¬ Subsingleton (UntruncatedTorPiece K n lam hk i (i + r)) := by
  dsimp only
  let r : ℤ := (springerTopDegree lam : ℤ) +
    (n - lam.card : ℕ) * (lam.colLen 0 : ℤ)
  have h := corollary_7_5_tor_regularity K n lam hk
  obtain ⟨hupper, i, hnonzero⟩ := h
  have hout (q : ℕ) (j : ℤ) (hq : n < q) :
      Subsingleton (UntruncatedTorPiece K n lam hk q j) := by
    apply (polynomialTor_piece_subsingleton_iff (untruncatedIdeal K n lam)
      (untruncatedIdeal_isHomogeneous hk) (untruncatedCoefficientBasis K n lam hk)
      parameterBasisDegree (untruncatedCoefficientBasis_mem_piece K n lam hk) q j).mpr
    exact coordinateKoszulHomology_subsingleton_of_homological_outside _
      (Or.inr (by exact_mod_cast hq))
  refine ⟨?_, i, ?_, hnonzero⟩
  · intro q j hqj
    rcases hqj with hq | hj | hr
    · exact hout q j hq
    · exact polynomialTor_piece_subsingleton_of_below_diagonal
        (untruncatedIdeal K n lam) (untruncatedIdeal_isHomogeneous hk)
        (untruncatedCoefficientBasis K n lam hk) parameterBasisDegree
        (untruncatedCoefficientBasis_mem_piece K n lam hk) q j hj
    · exact hupper q j hr
  · by_contra hni
    exact hnonzero (hout i (i + r) (by omega))

end HigherSpecht
end
end CanonicalSource79

section CanonicalSource0
/- Source: TauCeti/Algebra/Module/GradedModule/DirectSum.lean -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Direct sums of internally graded modules

This file equips an external direct sum of internally graded modules with its canonical internal
grading.  Its degree-`p` piece is the direct sum of the componentwise degree-`p` pieces, included
in the ambient direct sum, so membership is characterized componentwise. The grading indices
may be any type; no additive structure on them is needed.

## Main definitions

* `TauCeti.InternalGrading.directSumPieceInclusion`: the inclusion of homogeneous summands of one
  fixed degree into the ambient direct sum.
* `TauCeti.InternalGrading.directSumPiece`: the corresponding homogeneous submodule.
* `TauCeti.InternalGrading.directSum`: the canonical internal grading on an external direct sum.

## References

* Mathlib's `DirectSum` API.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.6.
-/


open scoped DirectSum

namespace TauCeti

universe u v w

namespace InternalGrading

variable {R : Type u} {ι : Type v} {M : ι → Type w} {κ : Type} [DecidableEq κ]
variable [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- The canonical inclusion of the direct sum of degree-`p` pieces into the direct sum of the
underlying modules. -/
def directSumPieceInclusion (G : ∀ i, InternalGrading R (M i) κ) (p : κ) :
    (⨁ i, (G i).piece p) →ₗ[R] ⨁ i, M i :=
  TauCeti.DirectSum.piInclusion fun i ↦ (G i).piece p

/-- The componentwise formula for the graded direct-sum inclusion. -/
@[simp]
theorem directSumPieceInclusion_apply (G : ∀ i, InternalGrading R (M i) κ) (p : κ)
    (x : ⨁ i, (G i).piece p) (i : ι) :
    directSumPieceInclusion G p x i = (x i : M i) := by
  simpa only [directSumPieceInclusion] using
    (TauCeti.DirectSum.piInclusion_apply (fun i ↦ (G i).piece p) x i)

/-- The degree-`p` piece in the direct sum of a family of internally graded modules. -/
def directSumPiece (G : ∀ i, InternalGrading R (M i) κ) (p : κ) : Submodule R (⨁ i, M i) :=
  TauCeti.DirectSum.piSubmodule fun i ↦ (G i).piece p

/-- On a homogeneous summand, `directSumPieceInclusion` is the usual external direct-sum
inclusion. -/
@[simp]
theorem directSumPieceInclusion_lof (G : ∀ i, InternalGrading R (M i) κ) (p : κ) (i : ι)
    (x : (G i).piece p) [DecidableEq ι] :
    directSumPieceInclusion G p (DirectSum.lof R ι (fun i ↦ (G i).piece p) i x) =
      DirectSum.lof R ι M i x := by
  exact TauCeti.DirectSum.piInclusion_lof (fun i ↦ (G i).piece p) i x

/-- The linear equivalence from the external direct sum of degree-`p` pieces to its range in the
ambient direct sum. -/
noncomputable def directSumPieceEquiv (G : ∀ i, InternalGrading R (M i) κ) (p : κ) :
    (⨁ i, (G i).piece p) ≃ₗ[R] directSumPiece G p :=
  TauCeti.DirectSum.piSubmoduleEquiv fun i ↦ (G i).piece p

/-- The underlying element of `directSumPieceEquiv` is the canonical inclusion. -/
@[simp]
theorem directSumPieceEquiv_apply (G : ∀ i, InternalGrading R (M i) κ) (p : κ)
    (x : ⨁ i, (G i).piece p) :
    ((directSumPieceEquiv G p x : directSumPiece G p) : ⨁ i, M i) =
      directSumPieceInclusion G p x := by
  exact TauCeti.DirectSum.piSubmoduleEquiv_apply (fun i ↦ (G i).piece p) x

/-- The componentwise formula for the inverse of `directSumPieceEquiv`. -/
@[simp]
theorem directSumPieceEquiv_symm_apply (G : ∀ i, InternalGrading R (M i) κ) (p : κ)
    (y : directSumPiece G p) (i : ι) :
    ((directSumPieceEquiv G p).symm y i : M i) = (y : ⨁ i, M i) i := by
  exact TauCeti.DirectSum.piSubmoduleEquiv_symm_apply (fun i ↦ (G i).piece p) y i

private def sigmaSwap (ι : Type v) : (Σ _ : κ, ι) ≃ (Σ _ : ι, κ) :=
  (Equiv.sigmaEquivProd κ ι).trans <|
    (Equiv.prodComm κ ι).trans (Equiv.sigmaEquivProd ι κ).symm

private def sigmaSwapPieceEquiv (G : ∀ i, InternalGrading R (M i) κ) (z : Σ _ : ι, κ) :
    (G ((sigmaSwap ι).symm z).2).piece ((sigmaSwap ι).symm z).1 ≃ₗ[R] (G z.1).piece z.2 := by
  obtain ⟨i, p⟩ := z
  exact LinearEquiv.refl R _

-- Evaluating the reindexing equivalence on a generator identifies this map with the identity
-- on the corresponding degree-and-summand component.  An API-level rewrite
-- (`DirectSum.coe_congrLinearEquiv` followed by `DirectSum.lmap_lof`) does not typecheck here:
-- the domain family of `sigmaSwapPieceEquiv G z` is
-- `fun z ↦ (G ((sigmaSwap ι).symm z).2).piece ((sigmaSwap ι).symm z).1`, which agrees with the
-- `lof` family `fun z ↦ (G z.1).piece z.2` only up to the semireducible reindexing
-- `(sigmaSwap ι).symm`, and rewrite-step unification does not unfold it.  The `change` below
-- confines that definitional reduction to this private, single-purpose helper.
private theorem sigmaSwapPieceEquiv_lof (G : ∀ i, InternalGrading R (M i) κ) (p : κ) (i : ι)
    (x : (G i).piece p) [DecidableEq ι] :
    DirectSum.congrLinearEquiv (fun z ↦ sigmaSwapPieceEquiv G z)
        (DirectSum.lof R (Σ _ : ι, κ)
          (fun z ↦ (G ((sigmaSwap ι).symm z).2).piece ((sigmaSwap ι).symm z).1) ⟨i, p⟩ x) =
      DirectSum.lof R (Σ _ : ι, κ) (fun z ↦ (G z.1).piece z.2) ⟨i, p⟩ x := by
  change DirectSum.lmap
      (fun z : Σ _ : ι, κ ↦ (LinearEquiv.refl R ((G z.1).piece z.2)).toLinearMap)
      (DirectSum.lof R (Σ _ : ι, κ) (fun z ↦ (G z.1).piece z.2) ⟨i, p⟩ x) = _
  rw [DirectSum.lmap_lof]
  rfl

private noncomputable def directSumRecomposeEquiv (G : ∀ i, InternalGrading R (M i) κ)
    [DecidableEq ι] : (⨁ p, directSumPiece G p) ≃ₗ[R] ⨁ i, M i :=
  (DirectSum.congrLinearEquiv fun p ↦ (directSumPieceEquiv G p).symm).trans <|
    (DirectSum.sigmaLcurryEquiv R (δ := fun p i ↦ (G i).piece p)).symm.trans <|
      (DirectSum.lequivCongrLeft R (sigmaSwap ι)).trans <|
        (DirectSum.congrLinearEquiv fun z ↦ sigmaSwapPieceEquiv G z).trans <|
          (DirectSum.sigmaLcurryEquiv R (δ := fun i p ↦ (G i).piece p)).trans <|
            DirectSum.congrLinearEquiv fun i ↦
              (DirectSum.decomposeLinearEquiv (G i).piece).symm

private theorem directSumRecomposeEquiv_lof_lof (G : ∀ i, InternalGrading R (M i) κ)
    (p : κ) (i : ι) (x : (G i).piece p) [DecidableEq ι] :
    directSumRecomposeEquiv G
        (DirectSum.lof R κ (fun p ↦ directSumPiece G p) p
          (directSumPieceEquiv G p
            (DirectSum.lof R ι (fun i ↦ (G i).piece p) i x))) =
      DirectSum.lof R ι M i x := by
  rw [directSumRecomposeEquiv]
  simp only [LinearEquiv.trans_apply]
  have hpieces :
      (DirectSum.congrLinearEquiv fun p ↦ (directSumPieceEquiv G p).symm)
          (DirectSum.lof R κ (fun p ↦ directSumPiece G p) p
            (directSumPieceEquiv G p
              (DirectSum.lof R ι (fun i ↦ (G i).piece p) i x))) =
        DirectSum.lof R κ (fun p ↦ ⨁ i, (G i).piece p) p
          (DirectSum.lof R ι (fun i ↦ (G i).piece p) i x) := by
    rw [DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof]
    congr 1
    exact (directSumPieceEquiv G p).symm_apply_apply _
  rw [hpieces]
  -- Mathlib packages the inverse as `DFinsupp.sigmaUncurry`, and `lof` as `DFinsupp.single`.
  -- Rewrite matching does not unfold these wrappers, so expose this application first.
  conv_lhs =>
    pattern (DirectSum.sigmaLcurryEquiv R).symm _
    change DFinsupp.sigmaUncurry (δ := fun p i ↦ (G i).piece p)
      (DFinsupp.single p (DFinsupp.single i x))
    rw [DFinsupp.sigmaUncurry_single, DirectSum.single_eq_lof R]
  rw [DirectSum.lequivCongrLeft_lof
    (M := fun z : Σ _ : κ, ι ↦ (G z.2).piece z.1) R (e := sigmaSwap ι)
    (i := Sigma.mk p i) (k := Sigma.mk i p) rfl x x rfl]
  -- After swapping the indices, apply the second curry generator formula.
  rw [sigmaSwapPieceEquiv_lof]
  -- The forward function is the same `DFinsupp.sigmaCurry` packaged by `DirectSum.sigmaCurry`.
  -- Expose that application to use Mathlib's additive generator formula.
  conv_lhs =>
    pattern (DirectSum.sigmaLcurryEquiv R) _
    change DirectSum.sigmaCurry
      (DirectSum.of (fun z : Σ _ : ι, κ ↦ (G z.1).piece z.2) ⟨i, p⟩ x)
    rw [DirectSum.sigmaCurry_of, ← DirectSum.lof_eq_of R ι, ← DirectSum.lof_eq_of R κ]
  -- The last congruence map acts componentwise on the single summand.
  rw [DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof]
  congr 1
  exact DirectSum.decomposeLinearEquiv_symm_lof (G i).piece p x

private theorem directSumRecomposeEquiv_lof (G : ∀ i, InternalGrading R (M i) κ)
    (p : κ) (x : directSumPiece G p) [DecidableEq ι] :
    directSumRecomposeEquiv G
        (DirectSum.lof R κ (fun p ↦ directSumPiece G p) p x) =
      (x : ⨁ i, M i) := by
  obtain ⟨y, rfl⟩ := (directSumPieceEquiv G p).surjective x
  induction y using DirectSum.induction_on with
  | zero => simp
  | of i y =>
    rw [← DirectSum.lof_eq_of R ι (fun i ↦ (G i).piece p), directSumPieceEquiv_apply,
      directSumPieceInclusion_lof]
    exact directSumRecomposeEquiv_lof_lof G p i y
  | add x y hx hy =>
    simpa only [map_add, Submodule.coe_add] using congrArg₂ (· + ·) hx hy

/-- The canonical degreewise ranges in an external direct sum form an internal direct sum. -/
theorem isInternal_directSumPiece (G : ∀ i, InternalGrading R (M i) κ) :
    DirectSum.IsInternal (directSumPiece G) := by
  let _ : DecidableEq ι := Classical.decEq _
  refine TauCeti.DirectSum.isInternal_of_lof
    (e := fun p ↦ LinearEquiv.refl R (directSumPiece G p))
    (E := directSumRecomposeEquiv G) ?_
  intro p x
  simpa only [LinearEquiv.refl_apply] using directSumRecomposeEquiv_lof G p x

/-- The external direct sum of internally graded modules, with degree-`p` piece the image of the
direct sum of the degree-`p` pieces. -/
def directSum (G : ∀ i, InternalGrading R (M i) κ) :
    InternalGrading R (⨁ i, M i) κ where
  piece := directSumPiece G
  isInternal := isInternal_directSumPiece G

/-- Membership in the direct sum of degree-`p` pieces is componentwise. -/
@[simp]
theorem mem_directSumPiece_iff (G : ∀ i, InternalGrading R (M i) κ) (p : κ)
    (x : ⨁ i, M i) :
    x ∈ directSumPiece G p ↔ ∀ i, x i ∈ (G i).piece p := by
  exact TauCeti.DirectSum.mem_piSubmodule_iff (fun i ↦ (G i).piece p) x

/-- The homogeneous pieces of `directSum` are the ranges of the canonical degreewise inclusions. -/
@[simp]
theorem directSum_piece (G : ∀ i, InternalGrading R (M i) κ) (p : κ) :
    (directSum G).piece p = directSumPiece G p :=
  by rw [directSum]

/-- The inclusion of a degree-`p` element from one summand belongs to the degree-`p` piece of the
direct-sum grading. -/
theorem lof_mem_directSumPiece (G : ∀ i, InternalGrading R (M i) κ) (p : κ) (i : ι)
    (x : (G i).piece p) [DecidableEq ι] :
    DirectSum.lof R ι M i x ∈ directSumPiece G p := by
  exact TauCeti.DirectSum.lof_mem_piSubmodule (fun i ↦ (G i).piece p) i x

/-- If each component map sends the degree-`p` piece into `ℬ q`, then so does the direct-sum
universal map on the degree-`p` piece of the direct-sum grading. -/
theorem toModule_mem_of_mem_directSumPiece {S : Type*} [Semiring S] [∀ i, Module S (M i)]
    {N : Type*} [AddCommMonoid N] [Module S N] {σN : Type*} [SetLike σN N]
    [AddSubmonoidClass σN N] [DecidableEq ι] (G : ∀ i, InternalGrading R (M i) κ)
    (ℬ : κ → σN) (φ : ∀ i, M i →ₗ[S] N) {p q : κ}
    (hφ : ∀ i x, x ∈ (G i).piece p → φ i x ∈ ℬ q) {x : ⨁ i, M i}
    (hx : x ∈ directSumPiece G p) : DirectSum.toModule S ι N φ x ∈ ℬ q := by
  classical
  rw [mem_directSumPiece_iff] at hx
  rw [← DFinsupp.sum_single (f := x), DFinsupp.sum, map_sum]
  refine sum_mem fun i _ ↦ ?_
  rw [DirectSum.single_eq_lof S, DirectSum.toModule_lof]
  exact hφ i _ (hx i)

end InternalGrading

end TauCeti
end CanonicalSource0

section CanonicalSource1
/- Source: TauCeti/Algebra/Module/GradedModule/Shift.lean -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Shifting an internal grading

An internal grading may be regraded by a fixed shift `c`, so that the degree-`p` piece of the
shifted grading is the degree-`(p + c)` piece of the original one. The underlying module is
unchanged, and the shifted family is again an internal direct sum: reindexing the homogeneous
pieces along an equivalence of degrees only permutes the summands of `⨁ p, G.piece p`.
The degrees may form any additive group. Simultaneous shifts preserve the degree of a homogeneous
map when the degree group is commutative.

For integer degrees, shifting by one is the suspension `sA` in the `A∞` conventions. The
suspension leaves the underlying module unchanged and reindexes its homogeneous pieces.

## Main definitions

* `TauCeti.InternalGrading.shift`: the shift of an internal grading.

## Main results

* `TauCeti.LinearMap.isHomogeneous_shift_piece_iff`: shifting both gradings preserves degrees.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.6.
-/


namespace TauCeti

universe u v

namespace InternalGrading

variable {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
variable {ι : Type} [DecidableEq ι] [AddGroup ι]

/-- The shift of an internal grading by `c`: its degree-`p` piece is the degree-`(p + c)` piece of
the original grading. The underlying module is unchanged. -/
def shift (G : InternalGrading R M ι) (c : ι) : InternalGrading R M ι where
  piece := fun p ↦ G.piece (Equiv.addRight c p)
  isInternal := by
    refine TauCeti.DirectSum.isInternal_of_lof
      (e := fun p ↦ LinearEquiv.refl R (G.piece (Equiv.addRight c p)))
      (E := (DirectSum.lequivCongrLeft R (Equiv.addRight c).symm).symm.trans
        (DirectSum.decomposeLinearEquiv G.piece).symm) ?_
    intro p x
    -- Express the generator family using the inverse reindexing, so the generator formula
    -- matches without unfolding the semireducible Equiv.addRight permutation.
    change (DirectSum.decomposeLinearEquiv G.piece).symm
      ((DirectSum.lequivCongrLeft R (Equiv.addRight c).symm).symm
        (DirectSum.lof R ι (fun p ↦ G.piece ((Equiv.addRight c).symm.symm p)) p x)) =
          (x : M)
    rw [DirectSum.lequivCongrLeft_symm_lof, DirectSum.decomposeLinearEquiv_symm_lof]

@[simp]
theorem shift_piece (G : InternalGrading R M ι) (c p : ι) :
    (G.shift c).piece p = G.piece (p + c) :=
  (rfl)

@[simp]
theorem shift_zero (G : InternalGrading R M ι) : G.shift 0 = G := by
  ext p
  simp

/-- Shifting twice shifts by the sum of the two amounts. -/
@[simp]
theorem shift_shift (G : InternalGrading R M ι) (c d : ι) :
    (G.shift c).shift d = G.shift (d + c) := by
  ext p
  simp [add_assoc]

/-- A Koszul twist preserves the original degree, expressed in any shifted grading. -/
theorem koszulTwist_mem_shift_piece {R : Type u} {M : Type v}
    [CommRing R] [AddCommMonoid M] [Module R M] (G : InternalGrading R M)
    {x : M} {e : ℤ} (hx : x ∈ G.piece e) (q c : ℤ) :
    G.koszulTwist q x ∈ (G.shift c).piece (e - c) := by
  rw [shift_piece, sub_add_cancel]
  exact G.koszulTwist_mem_piece hx q

/-- The Koszul twist of parameter `q` for a grading shifted by `c` differs from the unshifted
twist by the constant sign `(-1)^(q * c)`: a homogeneous element of degree `p` has degree `p - c`
after the shift. -/
theorem koszulTwist_shift {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M] [Module R M]
    (G : InternalGrading R M) (c q : ℤ) :
    (G.shift c).koszulTwist q = (((q * c).negOnePow : ℤ) : R) • G.koszulTwist q := by
  refine G.linearMap_ext fun p x hx ↦ ?_
  have hshift : x ∈ (G.shift c).piece (p - c) := by rwa [shift_piece, sub_add_cancel]
  rw [koszulTwist_apply_of_mem _ hshift, LinearMap.smul_apply, G.koszulTwist_apply_of_mem hx,
    smul_smul, ← Int.cast_mul, ← Units.val_mul, mul_sub, Int.negOnePow_sub]
  congr 3
  exact mul_comm _ _

/-- The degree-one Koszul twist of the suspended grading is the negative of the unsuspended one. -/
theorem koszulTwist_one_shift_one {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M]
    [Module R M] (G : InternalGrading R M) :
    (G.shift 1).koszulTwist 1 = -G.koszulTwist 1 := by
  rw [koszulTwist_shift]
  simp

end InternalGrading

/-- Shifting the source and the target internal grading by the same amount leaves the degree of a
homogeneous linear map unchanged. -/
theorem LinearMap.isHomogeneous_shift_piece_iff {R : Type u} {M N : Type*} [Semiring R]
    {ι : Type} [DecidableEq ι] [AddCommGroup ι]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] {G : InternalGrading R M ι}
    {H : InternalGrading R N ι} {f : M →ₗ[R] N} {c q : ι} :
    LinearMap.IsHomogeneous f (G.shift c).piece (H.shift c).piece q ↔
      LinearMap.IsHomogeneous f G.piece H.piece q := by
  simp only [LinearMap.isHomogeneous_def, InternalGrading.shift_piece]
  constructor
  · intro hf p x hx
    simpa only [sub_add_cancel, sub_add_eq_add_sub] using hf (p - c) x (by rwa [sub_add_cancel])
  · intro hf p x hx
    rw [add_right_comm]
    exact hf _ x hx

end TauCeti
end CanonicalSource1

section CanonicalSource2
/- Source: TauCeti/Algebra/Module/GradedModule/Generated.lean -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Graded modules generated in one degree

An internally graded module is generated in degree `d` when its degree-`d` homogeneous piece
generates the underlying module.  This is the module-theoretic condition imposed on the `i`th
projective in a linear resolution: after choosing the degree of the resolved module, its `i`th
projective is generated in the correspondingly shifted degree.

The definition is phrased using `Submodule.span`, so it does not depend on a choice of homogeneous
generators, and it allows any index type. The results below give the API needed to use it without
unfolding: generation is invariant under transport by a linear equivalence, its degree changes
predictably when the grading is shifted, and linear maps out of the module are determined by the
indicated homogeneous piece.

For the integer-graded scalar results, a compatible direct-sum decomposition of the scalar
semiring suffices; multiplicative grading laws and a commutative base semiring are not needed.

## Main definitions

* `TauCeti.InternalGrading.IsGeneratedInDegree`: the degree-`d` piece spans the whole module.

## Main results

* `TauCeti.InternalGrading.isGeneratedInDegree_map_iff`: generation in a degree is invariant
  under transport of the grading along a linear equivalence.
* `TauCeti.InternalGrading.isGeneratedInDegree_shift_iff`: shifting a grading indexed by any
  additive group reindexes the generating degree.
* `TauCeti.InternalGrading.isGeneratedInDegree_directSum_iff`: over any grading index type, a
  direct sum is generated in one degree exactly when every summand is generated in that degree.
* `TauCeti.InternalGrading.linearMap_ext_of_isGeneratedInDegree`: two linear maps out of a module
  generated in degree `d` agree when they agree on its degree-`d` piece.
* `TauCeti.InternalGrading.IsGeneratedInDegree.piece_add_eq_smul`: over a graded algebra `𝒜`, a
  graded module generated in degree `d` has degree-`m + d` piece `𝒜 m • M_d`.
* `TauCeti.InternalGrading.IsGeneratedInDegree.piece_eq_bot_of_lt`: over a nonnegatively graded
  algebra, a graded module generated in degree `d` vanishes in every degree below `d`.
* `TauCeti.InternalGrading.IsGeneratedInDegree.piece_le_smul_top`: a graded module generated in
  degree `d` has all of its pieces of degree above `d` inside `A₊ M`, where `A₊` is the sum of the
  pieces of positive degree.
* `TauCeti.InternalGrading.apply_mem_smul_top_of_isGeneratedInDegree`: over a nonnegatively graded
  scalar semiring, a degree-`δ` map from a module generated in degree `d'` to a module generated
  in degree `d < d' + δ` lands in `A₊ M`.

## References

* S. Priddy, "Koszul resolutions", *Transactions of the American Mathematical Society* **152**
  (1970), 39--60, for linear resolutions of graded modules.
* Z. Dancso and A. Licata, "Koszul algebras and flow lattices", *Journal of Combinatorial
  Theory, Series A* **185** (2022), Section 2.2, for the graded-module conventions used by the
  downstream Grothendieck-group constructions.
-/


namespace TauCeti

universe u u' v w

namespace InternalGrading

variable {R : Type u} {A : Type u'} {M : Type v}
variable [Semiring R] [Semiring A]
variable [AddCommMonoid M] [Module R M] [Module A M]
variable {ι : Type} [DecidableEq ι]

/-- An internally graded module is generated in degree `d` if the `A`-span of its degree-`d`
homogeneous piece is the whole module.  The grading pieces are `R`-submodules, while `A` is the
scalar semiring whose span measures generation (typically the graded algebra acting on the
module). The grading may use any index type. -/
def IsGeneratedInDegree (G : InternalGrading R M ι) (A : Type u') [Semiring A] [Module A M]
    (d : ι) : Prop :=
  Submodule.span A (G.piece d : Set M) = ⊤

/-- Generation in degree `d`, restated as membership of every element in the span of the
degree-`d` piece. -/
theorem isGeneratedInDegree_iff (G : InternalGrading R M ι) (d : ι) :
    G.IsGeneratedInDegree A d ↔ ∀ x : M, x ∈ Submodule.span A (G.piece d : Set M) :=
  Submodule.eq_top_iff'

/-- If the degree-`d` piece is the whole module, then the module is generated in degree `d`. -/
theorem isGeneratedInDegree_of_piece_eq_top (G : InternalGrading R M ι) (d : ι)
    (h : G.piece d = ⊤) : G.IsGeneratedInDegree A d := by
  simp [IsGeneratedInDegree, h]

/-- Enlarging the proposed homogeneous generating piece preserves generation. -/
theorem IsGeneratedInDegree.mono {G H : InternalGrading R M ι} {d e : ι}
    (hG : G.IsGeneratedInDegree A d) (h : G.piece d ≤ H.piece e) :
    H.IsGeneratedInDegree A e := by
  rw [IsGeneratedInDegree] at hG ⊢
  apply top_unique
  rw [← hG]
  exact Submodule.span_mono h

variable {N : Type w} [AddCommMonoid N] [Module A N]

section Map

variable {k : Type u} [Semiring k] [SMul k A]
variable [Module k M] [IsScalarTower k A M] [Module k N] [IsScalarTower k A N]

/-- Transporting an internal grading along a linear equivalence preserves generation in every
degree. -/
@[simp]
theorem isGeneratedInDegree_map_iff (G : InternalGrading k M ι) (e : M ≃ₗ[A] N) (d : ι) :
    (G.map (e.restrictScalars k)).IsGeneratedInDegree A d ↔ G.IsGeneratedInDegree A d := by
  rw [IsGeneratedInDegree, IsGeneratedInDegree, map_piece]
  -- Expose the carrier of the mapped `k`-submodule as an image so the `A`-span map lemma applies.
  change Submodule.span A (e '' (G.piece d : Set M)) = ⊤ ↔ _
  rw [Submodule.span_image_linearEquiv, Submodule.map_eq_top_iff]

end Map

/-- A shift by `c` reindexes generation in degree `d` as generation in degree `d + c` for the
original grading. -/
@[simp]
theorem isGeneratedInDegree_shift_iff [AddGroup ι] (G : InternalGrading R M ι) (c d : ι) :
    (G.shift c).IsGeneratedInDegree A d ↔ G.IsGeneratedInDegree A (d + c) := by
  rw [IsGeneratedInDegree, IsGeneratedInDegree, shift_piece]

/-- Two linear maps out of a module generated in degree `d` are equal exactly when they agree on
homogeneous elements of degree `d`. -/
theorem linearMap_eq_iff_of_isGeneratedInDegree (G : InternalGrading R M ι) {d : ι}
    (hG : G.IsGeneratedInDegree A d) (f g : M →ₗ[A] N) :
    f = g ↔ ∀ x : G.piece d, f x = g x :=
  Submodule.linearMap_eq_iff_of_span_eq_top f g hG

/-- Two linear maps out of a module generated in degree `d` agree everywhere if they agree on
homogeneous elements of degree `d`. -/
theorem linearMap_ext_of_isGeneratedInDegree (G : InternalGrading R M ι) {d : ι}
    (hG : G.IsGeneratedInDegree A d) {f g : M →ₗ[A] N}
    (h : ∀ x : G.piece d, f x = g x) : f = g :=
  (G.linearMap_eq_iff_of_isGeneratedInDegree hG f g).2 h

/-- A linear map out of a module generated in degree `d` vanishes exactly when it vanishes on
homogeneous elements of degree `d`. -/
theorem linearMap_eq_zero_iff_of_isGeneratedInDegree (G : InternalGrading R M ι) {d : ι}
    (hG : G.IsGeneratedInDegree A d) (f : M →ₗ[A] N) :
    f = 0 ↔ ∀ x : G.piece d, f x = 0 :=
  Submodule.linearMap_eq_zero_iff_of_span_eq_top f hG

/-- A homogeneous map from a module generated in degree `d` vanishes when the target piece
in degree `d + δ` vanishes. -/
theorem linearMap_eq_zero_of_isGeneratedInDegree [AddMonoid ι] (G : InternalGrading R M ι)
    {d δ : ι} (hG : G.IsGeneratedInDegree A d) [Module R N] {H : InternalGrading R N ι}
    {f : M →ₗ[A] N} (hf : LinearMap.IsHomogeneous f G.piece H.piece δ)
    (hH : H.piece (d + δ) = ⊥) : f = 0 := by
  apply (G.linearMap_eq_zero_iff_of_isGeneratedInDegree hG f).2
  intro x
  exact (Submodule.eq_bot_iff _).1 hH _ (hf.map_mem x.property)

section DirectSum

variable {ι : Type*} {M : ι → Type v} {κ : Type} [DecidableEq κ]
variable [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [∀ i, Module A (M i)]

/-- An external direct sum is generated in degree `d` if every summand is generated in degree
`d`. -/
theorem isGeneratedInDegree_directSum (G : ∀ i, InternalGrading R (M i) κ) (d : κ)
    (hG : ∀ i, (G i).IsGeneratedInDegree A d) :
    (directSum G).IsGeneratedInDegree A d := by
  classical
  rw [isGeneratedInDegree_iff]
  intro x
  induction x using DirectSum.induction_on with
  | zero => exact Submodule.zero_mem _
  | of i x =>
      rw [← DirectSum.lof_eq_of A ι M]
      have hx := ((G i).isGeneratedInDegree_iff d).1 (hG i) x
      refine (Submodule.span_le.mpr ?_ :
        Submodule.span A ((G i).piece d : Set (M i)) ≤
          (Submodule.span A ((directSum G).piece d : Set (DirectSum ι M))).comap
            (DirectSum.lof A ι M i)) hx
      intro y hy
      rw [directSum_piece]
      exact Submodule.subset_span (lof_mem_directSumPiece G d i ⟨y, hy⟩)
  | add x y hx hy => exact Submodule.add_mem _ hx hy

/-- If an external direct sum is generated in degree `d`, then every summand is generated in
degree `d`. -/
theorem IsGeneratedInDegree.of_directSum (G : ∀ i, InternalGrading R (M i) κ) (d : κ)
    (hG : (directSum G).IsGeneratedInDegree A d) (i : ι) :
    (G i).IsGeneratedInDegree A d := by
  classical
  rw [(G i).isGeneratedInDegree_iff]
  intro x
  have hx := ((directSum G).isGeneratedInDegree_iff d).1 hG
    (DirectSum.lof A ι M i x)
  have hmap : Submodule.span A ((directSum G).piece d : Set (DirectSum ι M)) ≤
      (Submodule.span A ((G i).piece d : Set (M i))).comap (DirectSum.component A ι M i) :=
    Submodule.span_le.mpr fun y hy ↦ Submodule.subset_span
      ((mem_directSumPiece_iff G d y).1 (by rwa [← directSum_piece]) i)
  simpa only [Submodule.mem_comap, DirectSum.component.lof_self] using hmap hx

/-- An external direct sum is generated in degree `d` exactly when every summand is generated in
degree `d`. -/
@[simp]
theorem isGeneratedInDegree_directSum_iff (G : ∀ i, InternalGrading R (M i) κ) (d : κ) :
    (directSum G).IsGeneratedInDegree A d ↔ ∀ i, (G i).IsGeneratedInDegree A d :=
  ⟨fun h i ↦ h.of_directSum G d i, isGeneratedInDegree_directSum G d⟩

end DirectSum

end InternalGrading

/-! ### Generation over a graded scalar semiring -/

namespace InternalGrading

variable {k : Type u} {A : Type u'} {M : Type v}
variable [Semiring k] [Semiring A] [Module k A]
variable [AddCommMonoid M] [Module k M] [Module A M] [IsScalarTower k A M]
variable (𝒜 : ℤ → Submodule k A) [DirectSum.Decomposition 𝒜]
variable {G : InternalGrading k M} [SetLike.GradedSMul 𝒜 G.piece] {d : ℤ}

include 𝒜 in
omit [IsScalarTower k A M] in
/-- The span of a homogeneous piece is homogeneous under compatible decompositions of the
scalar semiring and module. -/
theorem isHomogeneous_span_piece (d : ℤ) :
    _root_.DirectSum.SetLike.IsHomogeneous G.piece
      (Submodule.span A (G.piece d : Set M)) := by
  classical
  intro p x hx
  obtain ⟨n, c, g, rfl⟩ := Submodule.mem_span_set'.mp hx
  rw [DirectSum.decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have h := _root_.DirectSum.coe_decompose_smul_add_of_right_mem 𝒜 G.piece (g i).property
    (a := c i) (i := p - d)
  rw [sub_add_cancel] at h
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (g i).property)

/-- Under compatible decompositions of the scalar semiring and module, a module generated in
degree `d` has degree-`m + d` piece `𝒜 m • M_d`: its homogeneous elements of degree `m + d` are
exactly the sums of products of degree-`m` scalars with degree-`d` elements of the module. -/
theorem IsGeneratedInDegree.piece_add_eq_smul (hG : G.IsGeneratedInDegree A d) (m : ℤ) :
    G.piece (m + d) = 𝒜 m • G.piece d := by
  refine le_antisymm (fun x hx ↦ ?_) (Submodule.smul_le.2 fun a ha y hy ↦
    SetLike.GradedSMul.smul_mem ha hy)
  obtain ⟨n, c, g, rfl⟩ := Submodule.mem_span_set'.1 ((G.isGeneratedInDegree_iff d).1 hG x)
  rw [← DirectSum.decompose_of_mem_same G.piece hx, DirectSum.decompose_sum,
    DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rw [_root_.DirectSum.coe_decompose_smul_add_of_right_mem 𝒜 G.piece (g i).2]
  exact Submodule.smul_mem_smul (DirectSum.decompose 𝒜 (c i) m).2 (g i).2

/-- Over a nonnegatively graded scalar semiring, a module generated in degree `d` has no nonzero
homogeneous elements of degree below `d`. -/
theorem IsGeneratedInDegree.piece_eq_bot_of_lt (h𝒜 : ∀ i < 0, 𝒜 i = ⊥)
    (hG : G.IsGeneratedInDegree A d) {p : ℤ} (hp : p < d) : G.piece p = ⊥ := by
  rw [← sub_add_cancel p d, hG.piece_add_eq_smul 𝒜, h𝒜 _ (by omega), Submodule.bot_smul]

/-- A graded module generated in degree `d` has every homogeneous piece of degree above `d`
inside `A₊ M`, the products of elements of positive degree with elements of the module. -/
theorem IsGeneratedInDegree.piece_le_smul_top (hG : G.IsGeneratedInDegree A d) {p : ℤ}
    (hp : d < p) : G.piece p ≤ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • ⊤ := by
  rw [← sub_add_cancel p d, hG.piece_add_eq_smul 𝒜]
  exact Submodule.smul_mono (le_iSup₂_of_le (p - d) (by omega) le_rfl) le_top

/-- Over a nonnegatively graded scalar semiring, a degree-`δ` homogeneous map from a module
generated in degree `d'` to a module generated in degree `d < d' + δ` takes values in `A₊ M`.
The source has no homogeneous elements below degree `d'`, so every nonzero homogeneous image
has degree strictly above `d`. -/
theorem apply_mem_smul_top_of_isGeneratedInDegree (h𝒜 : ∀ i < 0, 𝒜 i = ⊥)
    {M' : Type w} [AddCommMonoid M'] [Module k M'] [Module A M'] [IsScalarTower k A M']
    {G' : InternalGrading k M'} [SetLike.GradedSMul 𝒜 G'.piece] {d' δ : ℤ}
    (hG' : G'.IsGeneratedInDegree A d') (hG : G.IsGeneratedInDegree A d) (hd : d < d' + δ)
    {f : M' →ₗ[A] M} (hf : LinearMap.IsHomogeneous f G'.piece G.piece δ) (x : M') :
    f x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) := by
  classical
  rw [← DirectSum.sum_support_decompose G'.piece x, map_sum]
  refine Submodule.sum_mem _ fun p _ ↦ ?_
  have hx : (DirectSum.decompose G'.piece x p : M') ∈ G'.piece p := (DirectSum.decompose _ x p).2
  rcases lt_or_ge p d' with hp | hp
  · rw [(Submodule.eq_bot_iff _).1 (hG'.piece_eq_bot_of_lt 𝒜 h𝒜 hp) _ hx, map_zero]
    exact Submodule.zero_mem _
  · exact hG.piece_le_smul_top 𝒜 (p := p + δ) (by omega) (hf.map_mem hx)

end InternalGrading

end TauCeti
end CanonicalSource2

section CanonicalSource3
/- Source: TauCeti/Algebra/Module/GradedModule/Nakayama.lean -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Graded Nakayama and detection of generating degrees

For a bounded-below internally graded module, the positive-degree part of the algebra cannot
surject onto the whole module unless the module is zero. More generally, homogeneous generators
modulo the positive-degree action generate the module itself. In particular, over a nonnegatively
graded algebra, a bounded-below module is generated in degree `d` exactly when every homogeneous
piece outside degree `d` lies in `A₊ M`.

The last criterion expresses concentration of `M / A₊ M` in degree `d` without choosing a
presentation of that quotient. It detects the generating degrees of terms of minimal graded
projective resolutions: maps to modules annihilated by `A₊` see precisely this quotient.
Neither projectivity nor semisimplicity is needed for the generation criterion. Boundedness below
is essential; no finite-generation hypothesis is required when a lower bound is supplied.

The positive-degree action `A₊ M` is itself a homogeneous submodule, stable under degree-zero
scalars: its degree-`p` components are sums of products `a • y` with `a` of positive degree `i`
and `y` of degree `p - i`.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of graded rings*, Section 2.3, for graded modules.
* A. Beilinson, V. Ginzburg and W. Soergel, "Koszul duality patterns in representation theory",
  Section 1.2, for detection of linearity via the generating degrees of minimal resolutions.
-/


namespace TauCeti.InternalGrading

open _root_.DirectSum

universe uk uA uM

variable {k : Type uk} [CommSemiring k] {A : Type uA} [Semiring A] [Algebra k A]
  {M : Type uM} [AddCommMonoid M] [Module k M] [Module A M] [IsScalarTower k A M]
  (𝒜 : ℤ → Submodule k A) {G : InternalGrading k M} [SetLike.GradedSMul 𝒜 G.piece]

/-- The degree-`p` component of an element of `A₊ M` is a sum of products `a • y` with `a` of
some positive degree `i` and `y` of degree `p - i`. -/
theorem decompose_mem_span_of_mem_positive_smul_top {x : M}
    (hx : x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)) (p : ℤ) :
    (decompose G.piece x p : M) ∈ Submodule.span k
      {z | ∃ i, 0 < i ∧ ∃ a ∈ 𝒜 i, ∃ y ∈ G.piece (p - i), a • y = z} := by
  classical
  set S := Submodule.span k {z | ∃ i, 0 < i ∧ ∃ a ∈ 𝒜 i, ∃ y ∈ G.piece (p - i), a • y = z}
  refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun x y hx hy => ?_)
  · refine Submodule.iSup_induction _ (motive := fun a =>
      (decompose G.piece (a • y) p : M) ∈ S) ha (fun i a ha => ?_) ?_ ?_
    · refine Submodule.iSup_induction _ (motive := fun a =>
        (decompose G.piece (a • y) p : M) ∈ S) ha (fun hi a ha => ?_) ?_ ?_
      · let f : M →ₗ[k] M := Algebra.lsmul k k M a
        have hf : TauCeti.LinearMap.IsHomogeneous f G.piece G.piece i :=
          TauCeti.LinearMap.isHomogeneous_def.mpr fun q z hz => by
            simpa [f, add_comm] using SetLike.GradedSMul.smul_mem ha hz
        have h := hf.map_decompose (p - i) y
        rw [sub_add_cancel] at h
        simpa only [f, Algebra.lsmul_apply] using h ▸ Submodule.subset_span
          ⟨i, hi, a, ha, _, (decompose G.piece y (p - i)).property, rfl⟩
      · simp
      · intro a b ha hb
        simpa only [add_smul, decompose_add, DirectSum.add_apply, Submodule.coe_add] using
          S.add_mem ha hb
    · simp
    · intro a b ha hb
      simpa only [add_smul, decompose_add, DirectSum.add_apply, Submodule.coe_add] using
        S.add_mem ha hb
  · simpa only [decompose_add, DirectSum.add_apply, Submodule.coe_add] using S.add_mem hx hy

/-- A component of `A₊ M` lies in an `A`-submodule if all lower-degree pieces do. The positive
scalar lowers the degree of the module component needed to compute that component. -/
theorem decompose_mem_of_mem_positive_smul_top (U : Submodule A M) {p : ℤ}
    (hU : ∀ q < p, ∀ x ∈ G.piece q, x ∈ U) {x : M}
    (hx : x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)) :
    (decompose G.piece x p : M) ∈ U := by
  refine (Submodule.span_le (p := U.restrictScalars k)).mpr ?_
    (decompose_mem_span_of_mem_positive_smul_top 𝒜 hx p)
  rintro _ ⟨i, hi, a, -, y, hy, rfl⟩
  exact U.smul_mem a (hU (p - i) (by omega) y hy)

/-- **Graded Nakayama for homogeneous generators.** In a bounded-below graded module, if each
homogeneous piece lies in the sum of a homogeneous `A`-submodule and the positive-degree action
on the module, then that submodule is the whole module. This is generation modulo `A₊`. -/
theorem eq_top_of_piece_le_sup_positive_smul_top (U : Submodule A M)
    (hhom : SetLike.IsHomogeneous G.piece U) (b : ℤ)
    (hbelow : ∀ p < b, G.piece p = ⊥)
    (hU : ∀ p, G.piece p ≤ U.restrictScalars k ⊔
      (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)) : U = ⊤ := by
  have pieces : ∀ n : ℕ, ∀ x ∈ G.piece (b + n), x ∈ U := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (hU _ hx)
      have lower : ∀ q < b + n, ∀ x ∈ G.piece q, x ∈ U := by
        intro q hq x hx
        by_cases hqb : q < b
        · rw [hbelow q hqb] at hx
          have hz : x = 0 := by simpa using hx
          rw [hz]
          exact U.zero_mem
        · have heq : b + (q - b).toNat = q := by omega
          exact ih (q - b).toNat (by omega) x (heq.symm ▸ hx)
      rw [← decompose_of_mem_same G.piece hx, decompose_add,
        DirectSum.add_apply, Submodule.coe_add]
      exact U.add_mem (hhom _ hy)
        (decompose_mem_of_mem_positive_smul_top 𝒜 U lower hz)
  apply top_unique
  intro x _
  classical
  rw [← sum_support_decompose G.piece x]
  refine U.sum_mem fun p _ => ?_
  by_cases hp : p < b
  · have hz := (Submodule.eq_bot_iff _).mp (hbelow p hp) _ (decompose G.piece x p).property
    rw [hz]
    exact U.zero_mem
  · have heq : b + (p - b).toNat = p := by omega
    exact pieces (p - b).toNat _ (heq.symm ▸ (decompose G.piece x p).property)

/-- **Graded Nakayama.** A bounded-below graded module satisfying `A₊ M = M` is zero. -/
theorem subsingleton_of_positive_smul_top_eq_top (b : ℤ)
    (hbelow : ∀ p < b, G.piece p = ⊥)
    (h : (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) = ⊤) :
    Subsingleton M := by
  have hbot : (⊥ : Submodule A M) = ⊤ :=
    eq_top_of_piece_le_sup_positive_smul_top 𝒜 ⊥ (by
      intro p x hx
      have hx : x = 0 := by simpa using hx
      simp [hx]) b hbelow (by simp [h])
  exact subsingleton_of_forall_eq 0 fun x => by
    have hx : x ∈ (⊥ : Submodule A M) := hbot.symm ▸ Submodule.mem_top
    simpa using hx

/-- The positive-degree action `A₊ M` is a homogeneous submodule. -/
theorem isHomogeneous_positive_smul_top :
    SetLike.IsHomogeneous G.piece ((⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)) := by
  intro p x hx
  refine Submodule.span_le.mpr ?_ (decompose_mem_span_of_mem_positive_smul_top 𝒜 hx p)
  rintro _ ⟨i, hi, a, ha, y, -, rfl⟩
  exact Submodule.smul_mem_smul (Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hi ha))
    Submodule.mem_top

variable {𝒜} in
/-- Degree-zero scalars preserve the positive-degree action `A₊ M`. -/
theorem smul_mem_positive_smul_top [SetLike.GradedMul 𝒜] {a : A} (ha : a ∈ 𝒜 0) {x : M}
    (hx : x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)) :
    a • x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) := by
  have hmul : ∀ b ∈ ⨆ (i : ℤ) (_ : 0 < i), 𝒜 i, a * b ∈ ⨆ (i : ℤ) (_ : 0 < i), 𝒜 i := by
    intro b hb
    refine Submodule.iSup_induction _ (motive := fun b => a * b ∈ ⨆ (i : ℤ) (_ : 0 < i), 𝒜 i)
      hb (fun i b hb => ?_) (by simp) (fun b c hb hc => by simpa [mul_add] using add_mem hb hc)
    refine Submodule.iSup_induction _ (motive := fun b => a * b ∈ ⨆ (i : ℤ) (_ : 0 < i), 𝒜 i)
      hb (fun hi b hb => ?_) (by simp) (fun b c hb hc => by simpa [mul_add] using add_mem hb hc)
    exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hi
      (by simpa using SetLike.GradedMul.mul_mem ha hb))
  refine Submodule.smul_induction_on hx (fun b hb y _ => ?_) (fun x y hx hy => ?_)
  · rw [← mul_smul]
    exact Submodule.smul_mem_smul (hmul b hb) Submodule.mem_top
  · simpa only [smul_add] using Submodule.add_mem _ hx hy

variable [GradedAlgebra 𝒜]

/-- A bounded-below module over a nonnegatively graded algebra is generated in degree `d`
exactly when its homogeneous pieces outside degree `d` lie in `A₊ M`. Equivalently, its quotient
by the positive-degree action is concentrated in degree `d`. -/
theorem isGeneratedInDegree_iff_piece_le_positive_smul_top (h𝒜 : ∀ i < 0, 𝒜 i = ⊥)
    (b : ℤ) (hbelow : ∀ p < b, G.piece p = ⊥) (d : ℤ) :
    G.IsGeneratedInDegree A d ↔
      ∀ p, p ≠ d → G.piece p ≤
        (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) := by
  constructor
  · intro hG p hp
    rcases lt_or_gt_of_ne hp with hlt | hgt
    · simp [hG.piece_eq_bot_of_lt 𝒜 h𝒜 hlt]
    · exact hG.piece_le_smul_top 𝒜 hgt
  · intro hG
    have hspan := eq_top_of_piece_le_sup_positive_smul_top 𝒜
      (Submodule.span A (G.piece d : Set M)) (isHomogeneous_span_piece 𝒜 d) b hbelow
      fun p => by
        by_cases hp : p = d
        · subst p
          exact le_sup_of_le_left fun x hx => Submodule.subset_span hx
        · exact le_sup_of_le_right (hG p hp)
    exact (G.isGeneratedInDegree_iff d).mpr fun x => hspan.symm ▸ Submodule.mem_top

/-- The generating-degree criterion for a module finite over the grading's scalar semiring.
Its internal grading has finite support, which supplies the lower bound automatically. -/
theorem isGeneratedInDegree_iff_piece_le_positive_smul_top_of_finite [Module.Finite k M]
    (h𝒜 : ∀ i < 0, 𝒜 i = ⊥) (d : ℤ) :
    G.IsGeneratedInDegree A d ↔
      ∀ p, p ≠ d → G.piece p ≤
        (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) := by
  obtain ⟨b, hb⟩ := G.finite_piece_ne_bot.bddBelow
  apply isGeneratedInDegree_iff_piece_le_positive_smul_top 𝒜 h𝒜 b _ d
  intro p hp
  by_contra hne
  have := hb hne
  omega

end TauCeti.InternalGrading
end CanonicalSource3

section CanonicalSource4
/- Source: TauCeti/RingTheory/LocalRing/Module.lean -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Generators of modules over a local ring

Over a local ring `R`, a free module of rank one is generated by a single element of any
spanning set. For instance, if `Ω[A⁄k]` is free of rank one over a local ring `A`, then it is
generated by a single differential `d a`. This is how a free module of differentials of rank
one at a point of a curve gives a local coordinate whose differential generates it.

More generally, a family of `n` elements of a free module of rank `n` whose coordinates are
linearly independent over the residue field is a basis. Applied to the differentials of a local
ring, this changes coordinates.

A finite module `M` over a local ring `(R, 𝔪, k)` is the quotient of `R ^ μ`, with `μ` the
dimension of `k ⊗ M`, by a submodule of `𝔪 • R ^ μ`: lifting a `k`-basis of `k ⊗ M` gives
generators of `M` (Nakayama) whose relations all have coefficients in `𝔪`. Iterating such minimal
covers is how minimal free resolutions are built.

## Main results

* `TauCeti.IsLocalRing.exists_mem_span_singleton_eq_top_of_finrank_eq_one`: a free module of
  rank one over a local ring is spanned by one element of any spanning set.
* `TauCeti.IsLocalRing.exists_basis_of_linearIndependent_residue_coord`: a family of `n`
  elements of a free module of rank `n` whose coordinates have linearly independent residues is a
  basis.
* `TauCeti.IsLocalRing.exists_surjective_ker_le_maximalIdeal_smul`: a finite module over a local
  ring `(R, 𝔪, k)` is a quotient of `R ^ dim_k (k ⊗ M)` by a submodule of `𝔪 • R ^ dim_k (k ⊗ M)`.

## References

* The Stacks Project, Lemma 10.20.1 (00DV), for Nakayama's lemma in the form used here.
-/


open scoped TensorProduct

namespace TauCeti.IsLocalRing

variable {R M : Type*} [CommRing R] [_root_.IsLocalRing R] [AddCommGroup M] [Module R M]

/-- **A free module of rank one over a local ring is generated by one element of any spanning
set**: if `M` is free of rank one over the local ring `R` and `s` spans `M`, then some `m ∈ s`
spans `M`. -/
theorem exists_mem_span_singleton_eq_top_of_finrank_eq_one [Module.Free R M]
    (h : Module.finrank R M = 1) {s : Set M} (hs : Submodule.span R s = ⊤) :
    ∃ m ∈ s, Submodule.span R {m} = ⊤ := by
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one h
  by_contra! H
  -- Otherwise every element of `s`, hence every element of `M`, has its coordinate in the
  -- maximal ideal; but the coordinate of `e 1` is `1`.
  have hs' : s ⊆ Submodule.comap e.symm.toLinearMap (_root_.IsLocalRing.maximalIdeal R) := by
    intro m hm
    by_contra hu
    rw [SetLike.mem_coe, Submodule.mem_comap, _root_.IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, not_not, LinearEquiv.coe_coe] at hu
    refine H m hm (eq_top_iff.mpr fun v _ ↦ Submodule.mem_span_singleton.mpr
      ⟨e.symm v * Ring.inverse (e.symm m), e.symm.injective ?_⟩)
    rw [map_smul, smul_eq_mul, mul_assoc, Ring.inverse_mul_cancel _ hu, mul_one]
  have h1 := Submodule.span_le.mpr hs' (hs ▸ Submodule.mem_top : e 1 ∈ Submodule.span R s)
  rw [Submodule.mem_comap, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h1
  exact (_root_.IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

/-- **A family with linearly independent residues is a basis.** If `M` has a basis `b` indexed by
`ι`, and `v` is a family of `|ι|` elements whose coordinates in `b`, read in the residue field,
are linearly independent, then `v` is a basis of `M`. -/
theorem exists_basis_of_linearIndependent_residue_coord {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : Module.Basis ι R M) {v : κ → M} (hcard : Fintype.card κ = Fintype.card ι)
    (h : LinearIndependent (_root_.IsLocalRing.ResidueField R)
      fun k i ↦ _root_.IsLocalRing.residue R (b.coord i (v k))) :
    ∃ b' : Module.Basis κ R M, ∀ k, b' k = v k := by
  classical
  let e : κ ≃ ι := Fintype.equivOfCardEq hcard
  -- The matrix of the family `v` in the basis `b`, with columns reindexed by `ι`.
  let A : Matrix ι ι R := Matrix.of fun i j ↦ b.coord i (v (e.symm j))
  have hA : IsUnit A.det := by
    have : IsUnit (A.map (_root_.IsLocalRing.residue R)) := by
      rw [← Matrix.linearIndependent_col_iff_isUnit]
      exact h.comp e.symm e.symm.injective
    rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
    exact isUnit_of_map_unit (_root_.IsLocalRing.residue R) _ this
  refine ⟨(b.map (Matrix.toLinearEquiv b A hA)).reindex e.symm, fun k ↦ ?_⟩
  simp [A, Matrix.toLin_self, Module.Basis.sum_repr]

variable (R M) in
/-- **Minimal generators of a finite module over a local ring.** If `M` is a finite module over a
local ring `(R, 𝔪, k)`, then `M` is the image of a surjection `R ^ μ → M`, with `μ = dim_k (k ⊗ M)`
the minimal number of generators of `M`, whose kernel is contained in `𝔪 • R ^ μ`. -/
theorem exists_surjective_ker_le_maximalIdeal_smul [Module.Finite R M] :
    ∃ f : (Fin (Module.finrank (_root_.IsLocalRing.ResidueField R)
        (_root_.IsLocalRing.ResidueField R ⊗[R] M)) → R) →ₗ[R] M,
      Function.Surjective f ∧ LinearMap.ker f ≤ _root_.IsLocalRing.maximalIdeal R • ⊤ := by
  classical
  let b := Module.finBasis (_root_.IsLocalRing.ResidueField R)
    (_root_.IsLocalRing.ResidueField R ⊗[R] M)
  choose v hv using fun j ↦ TensorProduct.mk_surjective R M (_root_.IsLocalRing.ResidueField R)
    Ideal.Quotient.mk_surjective (b j)
  refine ⟨Fintype.linearCombination R v, ?_, fun x hx ↦ ?_⟩
  · rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact _root_.IsLocalRing.span_eq_top_of_tmul_eq_basis v b hv
  -- A relation among the `v j` maps to a relation among the basis vectors `1 ⊗ v j` of `k ⊗ M`,
  -- whose coefficients are the residues of its coordinates; so these coordinates lie in `𝔪`.
  have hx' : ∑ j, _root_.IsLocalRing.residue R (x j) • b j = 0 := by
    simp_rw [← hv, TensorProduct.mk_apply, ← _root_.IsLocalRing.ResidueField.algebraMap_eq,
      algebraMap_smul, ← TensorProduct.tmul_smul, ← TensorProduct.tmul_sum]
    rw [← Fintype.linearCombination_apply, LinearMap.mem_ker.mp hx, TensorProduct.tmul_zero]
  have hres := Fintype.linearIndependent_iff.mp b.linearIndependent _ hx'
  rw [pi_eq_sum_univ x]
  exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem_smul
    ((_root_.IsLocalRing.residue_eq_zero_iff _).mp (hres j)) Submodule.mem_top

end TauCeti.IsLocalRing
end CanonicalSource4

section CanonicalSource5
/- Source: TauCeti/RingTheory/Depth/AuslanderBuchsbaum.lean -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The Auslander–Buchsbaum formula

Let `M` be a nonzero finite module of finite projective dimension over a Noetherian local ring
`R`. The **Auslander–Buchsbaum formula** states
`projectiveDimension M + depth M = depth R`.

Applied to the residue field `κ = R ⧸ 𝔪`, whose depth is zero, it shows that if `κ` has finite
projective dimension, then that dimension is `depth R`, hence at most `dim R`. This is the
upper bound in Serre's characterization of regular local rings by finite global dimension.

## Main results

* `ModuleCat.projectiveDimension_add_depth_eq_depth`: the Auslander–Buchsbaum formula
  (Stacks, Proposition 10.111.1 (090V)).
* `IsLocalRing.projectiveDimension_quotient_maximalIdeal_eq_depth`: a residue field of finite
  projective dimension has projective dimension `depth R`.
* `IsLocalRing.projectiveDimension_quotient_maximalIdeal_le_ringKrullDim`: a residue field of
  finite projective dimension has projective dimension at most `dim R`
  (Stacks, Lemma 10.110.4 (00OB)).

## Proof

Induction on `p = projectiveDimension M`. If `p = 0`, then `M` is projective, hence free, and a
nonzero finite free module has the depth of `R`. If `p > 0`, choose a minimal free presentation
`0 → K → F → M → 0`, with `K ⊆ 𝔪 F`; then `K` has projective dimension `p - 1`, so
`depth K + (p - 1) = depth R` by induction. The depth inequalities for short exact sequences give
`depth K - 1 ≤ depth M`. For the reverse inequality `depth M + 1 ≤ depth K`:

* if `p ≥ 2`, then `depth K < depth R = depth F`, and the depth inequalities suffice;
* if `p = 1`, then `K` is free, and the inclusion `K → F` has image in `𝔪 F`, so it induces zero
  on `Ext (R ⧸ 𝔪) - n`; the long exact sequence then shows that every connecting map
  `Ext (R ⧸ 𝔪) M n → Ext (R ⧸ 𝔪) K (n + 1)` is surjective.

## References

* [Stacks Project, Proposition 10.111.1](https://stacks.math.columbia.edu/tag/090V).
* [Stacks Project, Lemma 10.110.4](https://stacks.math.columbia.edu/tag/00OB).
* W. Bruns, J. Herzog, *Cohen–Macaulay rings*, Theorem 1.3.3.
-/


universe v u

open CategoryTheory Abelian IsLocalRing
open scoped TensorProduct

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [Small.{v} R]

variable [IsNoetherianRing R]

/-- The Auslander–Buchsbaum formula for a module of projective dimension `p : ℕ`, by induction
on `p`. -/
private theorem depth_add_eq_of_projectiveDimension_eq (p : ℕ) (M : Type v) [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Nontrivial M]
    (hp : projectiveDimension (ModuleCat.of R M) = p) :
    depth (ModuleCat.of R M) + p = depth (ModuleCat.of R R) := by
  induction p generalizing M with
  | zero =>
    have : Projective (ModuleCat.of R M) :=
      ((projectiveDimension_eq_zero_iff _).mp (by exact_mod_cast hp)).1
    have : Module.Projective R M := (IsProjective.iff_projective M).mpr this
    have : Module.Free R M := Module.free_of_flat_of_isLocalRing
    simpa using depth_eq_depth_self_of_free M
  | succ p ih =>
    -- A minimal free presentation, with free module transported to the universe of `M`.
    obtain ⟨n, g, hg, hker⟩ : ∃ (n : ℕ) (g : (Fin n → Shrink.{v} R) →ₗ[R] M),
        Function.Surjective g ∧ LinearMap.ker g ≤ maximalIdeal R • ⊤ := by
      obtain ⟨f, hf, hfker⟩ := TauCeti.IsLocalRing.exists_surjective_ker_le_maximalIdeal_smul R M
      let e : (Fin (Module.finrank (ResidueField R) (ResidueField R ⊗[R] M)) → Shrink.{v} R) ≃ₗ[R]
          (Fin (Module.finrank (ResidueField R) (ResidueField R ⊗[R] M)) → R) :=
        LinearEquiv.piCongrRight fun _ ↦ Shrink.linearEquiv R R
      refine ⟨_, f ∘ₗ e.toLinearMap, hf.comp e.surjective, ?_⟩
      rw [LinearMap.ker_comp, Submodule.comap_equiv_eq_map_symm]
      refine (Submodule.map_mono hfker).trans ?_
      rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
    have hM : ¬ Module.Projective R M := fun h ↦ by
      have := Projective.projectiveDimension_le_zero (ModuleCat.of R M)
      rw [hp] at this
      exact absurd this (by norm_cast)
    have hpK : projectiveDimension (ModuleCat.of R (LinearMap.ker g)) = p := by
      rw [← ENat.WithBot.add_one_cancel, g.projectiveDimension_ker_add_one hg hM, hp]
      norm_cast
    have : Nontrivial (LinearMap.ker g) := by
      by_contra hK
      rw [not_nontrivial_iff_subsingleton] at hK
      have h := (projectiveDimension_eq_bot_iff _).mpr
        (ModuleCat.isZero_of_subsingleton (ModuleCat.of R (LinearMap.ker g)))
      rw [hpK] at h
      exact WithBot.coe_ne_bot h
    have : Module.Finite R (LinearMap.ker g) := Module.IsNoetherian.finite R _
    have : Nontrivial (Fin n → Shrink.{v} R) := hg.nontrivial
    have hK := ih (LinearMap.ker g) hpK
    have hF := depth_eq_depth_self_of_free (R := R) (Fin n → Shrink.{v} R)
    have hKtop : depth (ModuleCat.of R (LinearMap.ker g)) ≠ ⊤ := fun h ↦
      not_subsingleton (LinearMap.ker g) ((depth_eq_top_iff _).mp h)
    have h₁ := depth_min_snd_fst_sub_one_le_trd_of_exact _ g (LinearMap.exact_subtype_ker_map g)
      (LinearMap.ker g).injective_subtype hg
    have h₂ : depth (ModuleCat.of R M) + 1 ≤ depth (ModuleCat.of R (LinearMap.ker g)) := by
      rcases p with _ | q
      · -- `K` is free and lies in `𝔪 F`.
        have : Projective (ModuleCat.of R (LinearMap.ker g)) :=
          ((projectiveDimension_eq_zero_iff _).mp (by exact_mod_cast hpK)).1
        have : Module.Projective R (LinearMap.ker g) := (IsProjective.iff_projective _).mpr this
        have : Module.Free R (LinearMap.ker g) := Module.free_of_flat_of_isLocalRing
        exact depth_add_one_le_depth_ker hg hker
      · -- `depth K < depth R = depth F`.
        have h := depth_min_snd_trd_add_one_le_fst_of_exact _ g
          (LinearMap.exact_subtype_ker_map g) (LinearMap.ker g).injective_subtype hg
        refine (inf_le_iff.mp h).resolve_left fun h' ↦ ?_
        rw [hF, ← hK] at h'
        generalize depth (ModuleCat.of R (LinearMap.ker g)) = b at h' hKtop
        induction b using ENat.recTopCoe with
        | top => exact hKtop rfl
        | coe b => norm_cast at h'; omega
    rw [hF, ← hK] at h₁
    rw [← hK]
    exact ENat.add_succ_eq_of_le_of_le h₁ h₂

end IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R]

/-- **The Auslander–Buchsbaum formula.** For a nonzero finite module `M` of finite projective
dimension over a Noetherian local ring `R`, `projectiveDimension M + depth M = depth R`.
Stacks, Proposition 10.111.1 (090V). -/
@[stacks 090V]
theorem ModuleCat.projectiveDimension_add_depth_eq_depth (M : ModuleCat.{v} R)
    [Module.Finite R M] [Nontrivial M] (hM : projectiveDimension M ≠ ⊤) :
    projectiveDimension M + (IsLocalRing.depth M : WithBot ℕ∞) =
      IsLocalRing.depth (ModuleCat.of R R) := by
  have hbot : projectiveDimension M ≠ ⊥ := by
    rw [ne_eq, projectiveDimension_eq_bot_iff]
    exact fun h ↦ not_subsingleton M (ModuleCat.subsingleton_of_isZero h)
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hbot
  have hdtop : d ≠ ⊤ := fun h ↦ hM (by simp [← hd, h])
  obtain ⟨p, rfl⟩ := ENat.ne_top_iff_exists.mp hdtop
  rw [← hd, ← IsLocalRing.depth_add_eq_of_projectiveDimension_eq p M hd.symm, add_comm]
  norm_cast

namespace IsLocalRing

/-- If the residue field `κ` of a Noetherian local ring `R` has finite projective dimension, that
dimension is `depth R`. -/
theorem projectiveDimension_quotient_maximalIdeal_eq_depth
    (h : projectiveDimension (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) ≠ ⊤) :
    projectiveDimension (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) =
      depth (ModuleCat.of R R) := by
  have : Module.Finite R (Shrink.{v} (R ⧸ maximalIdeal R)) :=
    Module.Finite.equiv (Shrink.linearEquiv R (R ⧸ maximalIdeal R)).symm
  have : Nontrivial (Shrink.{v} (R ⧸ maximalIdeal R)) :=
    (Shrink.linearEquiv R (R ⧸ maximalIdeal R)).nontrivial_congr.mpr inferInstance
  have h0 : depth (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) = 0 :=
    depth_eq_zero_iff_nontrivial_linearMap.mpr
      ⟨(Shrink.linearEquiv R _).symm.toLinearMap, 0, fun h ↦ one_ne_zero
        ((Shrink.linearEquiv R (R ⧸ maximalIdeal R)).symm.map_eq_zero_iff.mp
          (by simpa using congr($h 1)))⟩
  rw [← ModuleCat.projectiveDimension_add_depth_eq_depth _ h, h0]
  simp

/-- If the residue field `κ` of a Noetherian local ring `R` has finite projective dimension, that
dimension is at most the Krull dimension of `R`. Stacks, Lemma 10.110.4 (00OB). -/
@[stacks 00OB]
theorem projectiveDimension_quotient_maximalIdeal_le_ringKrullDim
    (h : projectiveDimension (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) ≠ ⊤) :
    projectiveDimension (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) ≤ ringKrullDim R := by
  rw [projectiveDimension_quotient_maximalIdeal_eq_depth h,
    ← Module.supportDim_self_eq_ringKrullDim]
  exact depth_le_supportDim

end IsLocalRing
end CanonicalSource5

section CanonicalSource6
/- Source: TauCeti/RingTheory/Ideal/GoingUp.lean -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/


/-!
# Lying over along an integral ring homomorphism

An integral ring homomorphism `g : S →+* T` lifts each prime ideal of `S` containing its kernel
to a prime ideal of `T`. This is Mathlib's `Ideal.exists_ideal_over_prime_of_isIntegral` stated
directly for `g`, so callers need not install an algebra structure.

Along an integral algebra, maximal ideals contract to maximal ideals, so the extension of an
ideal contained in the Jacobson radical is again contained in the Jacobson radical.

## Main results

* `Ideal.exists_comap_eq_of_isIntegral`: a prime of `S` containing the kernel of `g` is the
  contraction along `g` of a prime of `T`.
* `Ideal.primesOver_eq_singleton_under_of_primesOver_eq_singleton`: a prime alone above `p` in
  `T` contracts to a prime alone above `p` in any intermediate ring over which `T` is integral.
* `Ideal.comap_eq_maximalIdeal_of_isIntegral`: along an integral algebra over a local ring, every
  maximal ideal contracts to the maximal ideal.
* `Ideal.map_le_jacobson_bot_of_isIntegral`: along an integral algebra, the extension of an ideal
  in the Jacobson radical lies in the Jacobson radical.

## References

* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `a39c3781b9850b9f3d5cbc9920322a3b8e365ef2` (Apache-2.0),
  `lean/Pcf/Stacks/Purity/FiniteAlgebraIdempotents.lean`: `map_le_jacobson_bot_of_isIntegral` is
  the algebra form of its `Pcf.Stacks.map_le_jacobson_bot_of_le_jacobson_of_isIntegral`.
-/


namespace Ideal

variable {S T : Type*} [CommRing S] [CommRing T]

/-- Lying over along an integral ring homomorphism `g : S →+* T`: a prime `P` of `S`
containing the kernel of `g` is the contraction along `g` of a prime of `T`. -/
theorem exists_comap_eq_of_isIntegral (P : Ideal S) [P.IsPrime]
    (g : S →+* T) (hg : g.IsIntegral) (hP : RingHom.ker g ≤ P) :
    ∃ Q : Ideal T, Q.IsPrime ∧ Q.comap g = P := by
  let _ : Algebra S T := g.toAlgebra
  have : Algebra.IsIntegral S T := ⟨hg⟩
  obtain ⟨Q, -, hQ, hQP⟩ := exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal T)
    (by rwa [under_def, RingHom.algebraMap_toAlgebra, ← RingHom.ker_eq_comap_bot])
  exact ⟨Q, hQ, hQP⟩

/-- If `P` is the only prime of `T` above an ideal `p` of `R`, then `P.under S` is the only prime
of `S` above `p`, for any intermediate ring `S` over which `T` is integral and faithful. -/
theorem primesOver_eq_singleton_under_of_primesOver_eq_singleton {R : Type*} [CommRing R]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T] [Algebra.IsIntegral S T]
    [FaithfulSMul S T] {p : Ideal R} {P : Ideal T} (h : p.primesOver T = {P}) :
    p.primesOver S = {P.under S} := by
  obtain ⟨_, _⟩ : P ∈ p.primesOver T := h ▸ rfl
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨inferInstance, inferInstance⟩, ?_⟩
  rintro Q ⟨_, _⟩
  obtain ⟨⟨Q', _, _⟩⟩ := nonempty_primesOver (S := T) Q
  have : Q'.LiesOver p := .trans Q' Q p
  have hmem : Q' ∈ p.primesOver T := ⟨inferInstance, inferInstance⟩
  rw [h] at hmem
  rw [LiesOver.over (P := Q') (p := Q), hmem]

/-- Along an integral algebra, the extension of an ideal in the Jacobson radical lies in the
Jacobson radical, since maximal ideals contract to maximal ideals. -/
theorem map_le_jacobson_bot_of_isIntegral [Algebra S T] [Algebra.IsIntegral S T] {I : Ideal S}
    (hI : I ≤ jacobson ⊥) : I.map (algebraMap S T) ≤ jacobson ⊥ := by
  refine le_sInf fun M ⟨_, hM⟩ ↦ map_le_iff_le_comap.mpr <| hI.trans <| sInf_le
    ⟨bot_le, isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap S T)
      (fun x ↦ Algebra.IsIntegral.isIntegral x) M⟩

/-- Along an integral algebra over a local ring, every maximal ideal contracts to the maximal
ideal. -/
theorem comap_eq_maximalIdeal_of_isIntegral {R : Type*} [CommRing R] [IsLocalRing R]
    [Algebra R S] [Algebra.IsIntegral R S] (P : Ideal S) [P.IsMaximal] :
    P.comap (algebraMap R S) = IsLocalRing.maximalIdeal R :=
  IsLocalRing.eq_maximalIdeal (isMaximal_under_of_isIntegral_of_isMaximal (R := R) P)

end Ideal
end CanonicalSource6

section CanonicalSource7
/- Source: HigherSpecht/FiniteDuality.lean -/



/-!
# The dual module of a finite algebra

`RelativeDual B A` is the actual module `Hom_B(A,B)`, with multiplication
acting by precomposition. Evaluation at one proves its adjunction, and
finite projective double duality identifies its endomorphisms with the
homotheties from `A`. The base-change equivalence is the actual dual
base-change map, with its formula on pure tensors recorded explicitly.

These are the algebraic duality constructions used for the canonical
module. They do not define type or levelness by a desired numerical answer.
-/

noncomputable section

open Module
open scoped Classical TensorProduct

namespace HigherSpecht

variable (B A : Type*) [CommRing B] [CommRing A] [Algebra B A]

def RelativeDual := Module.Dual B A

namespace RelativeDual

instance : AddCommGroup (RelativeDual B A) :=
  inferInstanceAs (AddCommGroup (Module.Dual B A))

instance : Module B (RelativeDual B A) :=
  inferInstanceAs (Module B (Module.Dual B A))

instance : Module A (RelativeDual B A) :=
  show Module A (Module.Dual B A) from
    Module.compHom (Module.Dual B A) (TauCeti.dualRightAction B A)

def toLinearMap (f : RelativeDual B A) : Module.Dual B A := f

def ofLinearMap (f : Module.Dual B A) : RelativeDual B A := f

instance : CoeFun (RelativeDual B A) (fun _ => A → B) :=
  ⟨fun f => toLinearMap B A f⟩

@[simp] theorem ofLinearMap_apply (f : Module.Dual B A) (a : A) :
    ofLinearMap B A f a = f a := rfl

@[ext] theorem ext {f g : RelativeDual B A} (h : ∀ a : A, f a = g a) : f = g :=
  LinearMap.ext h

@[simp] theorem add_apply (f g : RelativeDual B A) (a : A) :
    (f + g) a = f a + g a := rfl

@[simp] theorem zero_apply (a : A) : (0 : RelativeDual B A) a = 0 := rfl

@[simp] theorem base_smul_apply (b : B) (f : RelativeDual B A) (a : A) :
    (b • f) a = b • f a := rfl

@[simp] theorem smul_apply (a : A) (f : RelativeDual B A) (x : A) :
    (a • f) x = f (x * a) := by
  change TauCeti.dualRightAction B A a (toLinearMap B A f) x =
    (toLinearMap B A f) (x * a)
  exact TauCeti.dualRightAction_apply_apply B A a (toLinearMap B A f) x

instance : IsScalarTower B A (RelativeDual B A) :=
  IsScalarTower.of_algebraMap_smul fun b f => by
    ext x
    rw [smul_apply, base_smul_apply, mul_comm x,
      ← Algebra.smul_def]
    exact (toLinearMap B A f).map_smul b x

instance : SMulCommClass B A (RelativeDual B A) where
  smul_comm b a f := by
    ext x
    simp only [smul_apply, base_smul_apply]

def linearEquiv : RelativeDual B A ≃ₗ[B] Module.Dual B A := LinearEquiv.refl B _

@[simp] theorem linearEquiv_apply (f : RelativeDual B A) (a : A) :
    linearEquiv B A f a = f a := rfl

end RelativeDual

variable {B A}

/-- Evaluation at one is the actual restriction--coextension adjunction,
in unbundled linear-map form. -/
def relativeDualHomEquiv (M : Type*) [AddCommGroup M] [Module B M]
    [Module A M] [IsScalarTower B A M] :
    (M →ₗ[A] RelativeDual B A) ≃ₗ[B] (M →ₗ[B] B) where
  toFun f := (Module.Dual.eval B A 1).comp
    ((RelativeDual.linearEquiv B A).toLinearMap.comp (f.restrictScalars B))
  invFun g :=
    { toFun m :=
        RelativeDual.ofLinearMap B A
          { toFun a := g (a • m)
            map_add' a b := by rw [add_smul, map_add]
            map_smul' b a := by simp only [smul_assoc, map_smul, RingHom.id_apply] }
      map_add' m m' := by
        apply RelativeDual.ext
        intro a
        exact (congrArg g (smul_add a m m')).trans (g.map_add _ _)
      map_smul' c m := by
        apply RelativeDual.ext
        intro a
        rw [RingHom.id_apply, RelativeDual.smul_apply]
        change g (a • (c • m)) = g ((a * c) • m)
        rw [mul_smul] }
  left_inv f := by
    ext m a
    change f (a • m) 1 = f m a
    rw [map_smul, RelativeDual.smul_apply, one_mul]
  right_inv g := by
    ext m
    change g ((1 : A) • m) = g m
    rw [one_smul]
  map_add' f g := by ext m; rfl
  map_smul' b f := by ext m; rfl

@[simp] theorem relativeDualHomEquiv_apply
    {M : Type*} [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower B A M]
    (f : M →ₗ[A] RelativeDual B A) (m : M) :
    relativeDualHomEquiv M f m = f m 1 := rfl

@[simp] theorem relativeDualHomEquiv_symm_apply
    {M : Type*} [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower B A M]
    (g : M →ₗ[B] B) (m : M) (a : A) :
    (relativeDualHomEquiv (B := B) (A := A) M).symm g m a = g (a • m) := rfl

/-- Finite free double duality identifies all endomorphisms of the dual
regular module with multiplication by a unique element of the algebra. -/
def relativeDualHomothetyEquiv [Module.Free B A] [Module.Finite B A] :
    A ≃ₗ[B] Module.End A (RelativeDual B A) :=
  (Module.evalEquiv B A).trans
    (relativeDualHomEquiv (B := B) (A := A) (RelativeDual B A)).symm

@[simp] theorem relativeDualHomothetyEquiv_apply
    [Module.Free B A] [Module.Finite B A] (a : A) (f : RelativeDual B A) :
    relativeDualHomothetyEquiv (B := B) (A := A) a f = a • f := by
  apply RelativeDual.ext
  intro x
  change (x • f) a = (a • f) x
  simp only [RelativeDual.smul_apply, mul_comm]

variable (S : Type*) [CommRing S] [Algebra B S]

/-- Actual base change of the dual, valid for the independently proved
finite parameter basis. -/
def relativeDualBaseChangeEquiv [Module.Free B A] [Module.Finite B A] :
    S ⊗[B] RelativeDual B A ≃ₗ[S] Module.Dual S (S ⊗[B] A) :=
  ((RelativeDual.linearEquiv B A).baseChange B S).trans
    (TensorProduct.isBaseChange B A S).toDualBaseChange

@[simp] theorem relativeDualBaseChangeEquiv_tmul
    [Module.Free B A] [Module.Finite B A]
    (s t : S) (f : RelativeDual B A) (a : A) :
    relativeDualBaseChangeEquiv (B := B) (A := A) S (s ⊗ₜ[B] f) (t ⊗ₜ[B] a) =
      s * t * algebraMap B S (f a) := by
  have hunit : (TensorProduct.isBaseChange B A S).toDualBaseChange
      (s ⊗ₜ[B] (RelativeDual.linearEquiv B A) f) ((1 : S) ⊗ₜ[B] a) =
        s * algebraMap B S (f a) := by
    simpa using (TensorProduct.isBaseChange B A S).toDualBaseChange_tmul
      s ((RelativeDual.linearEquiv B A) f) a
  simp only [relativeDualBaseChangeEquiv, LinearEquiv.trans_apply,
    LinearEquiv.baseChange_tmul]
  rw [show t ⊗ₜ[B] a = t • ((1 : S) ⊗ₜ[B] a) from
    (TensorProduct.smul_tmul' t (1 : S) a).trans (by rw [smul_eq_mul, mul_one]) |>.symm,
    map_smul, hunit]
  simp only [smul_eq_mul]
  ring

end HigherSpecht
end
end CanonicalSource7

section CanonicalSource8
/- Source: HigherSpecht/FiniteDualizingModule.lean -/



/-!
# The actual dualizing module of a finite free algebra over a regular ring

The proof uses restriction--coextension adjunction on Ext groups. Coextension
is exact because the algebra is projective over its base. Consequently the
ordinary finite free dual has finite injective dimension when the base has
bounded global dimension, and has no positive self-Ext groups. Together with
its homothety isomorphism these are the usual dualizing-module conditions.
No homological assertion is postulated as a field of the application theorem.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe u w

namespace HigherSpecht

variable (B A : Type u) [CommRing B] [CommRing A] [Algebra B A]

set_option backward.isDefEq.respectTransparency false in
/-- The usual scalar restriction agrees with the already installed algebra
module structure, by its actual action formula. -/
def algebraRestrictionEquiv (M : Type u) [AddCommGroup M] [Module B M]
    [Module A M] [IsScalarTower B A M] :
    ((ModuleCat.restrictScalars (algebraMap B A)).obj (ModuleCat.of A M)) ≃ₗ[B] M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' b x := IsScalarTower.algebraMap_smul (M := M) A b (show M from x)

set_option backward.isDefEq.respectTransparency false in
/-- The explicit dual module is the actual categorical coextension. -/
def relativeDualCoextendEquiv :
    RelativeDual B A ≃ₗ[A]
      (ModuleCat.coextendScalars (algebraMap B A)).obj (ModuleCat.of B B) where
  toFun f := (ModuleCat.CoextendScalars.equiv (algebraMap B A) (ModuleCat.of B B)).symm
    ((RelativeDual.toLinearMap B A f).comp (algebraRestrictionEquiv B A A).toLinearMap)
  invFun g := (ModuleCat.CoextendScalars.equiv (algebraMap B A) (ModuleCat.of B B) g).comp
    (algebraRestrictionEquiv B A A).symm.toLinearMap
  left_inv f := by apply RelativeDual.ext; intro a; rfl
  right_inv g := by apply ModuleCat.CoextendScalars.ext; ext a; rfl
  map_add' f g := by apply ModuleCat.CoextendScalars.ext; ext a; rfl
  map_smul' a f := by
    apply ModuleCat.CoextendScalars.ext
    ext x
    change (a • f) (show A from x) = f ((show A from x) * a)
    exact RelativeDual.smul_apply B A a f (show A from x)

/-- Exactness of actual coextension along a finite free algebra. -/
theorem relativeDual_coextension_preservesFiniteColimits
    [Module.Free B A] :
    PreservesFiniteColimits (ModuleCat.coextendScalars.{u, u, u} (algebraMap B A)) := by
  have hproj : letI := (algebraMap B A).toModule; Module.Projective B A := by
    change Module.Projective B
      ((ModuleCat.restrictScalars (algebraMap B A)).obj (ModuleCat.of A A))
    exact Module.Projective.of_equiv (algebraRestrictionEquiv B A A).symm
  apply (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).mpr
  intro S hS
  have h := ModuleCat.coextendScalars_map_shortExact (algebraMap B A) hproj hS
  exact ⟨h.exact, h.epi_g⟩

section Ext

variable [HasExt.{w} (ModuleCat.{u} B)] [HasExt.{w} (ModuleCat.{u} A)]

/-- The genuine Ext adjunction into the relative dual. -/
def relativeDualExtEquiv [Module.Free B A] (X : ModuleCat.{u} A) (i : ℕ) :
    Ext X (ModuleCat.of A (RelativeDual B A)) i ≃+
      Ext ((ModuleCat.restrictScalars (algebraMap B A)).obj X) (ModuleCat.of B B) i := by
  letI := relativeDual_coextension_preservesFiniteColimits B A
  exact (TauCeti.extAddEquivOfIso (Iso.refl X)
    (relativeDualCoextendEquiv B A).toModuleIso i).trans
      (ModuleCat.restrictCoextendScalarsAdj (algebraMap B A)).extEquiv.symm

/-- Positive self-Ext groups vanish for the actual relative dual. -/
theorem relativeDual_selfExt_eq_zero [Module.Free B A] [Module.Finite B A]
    (i : ℕ) (hi : 0 < i)
    (e : Ext (ModuleCat.of A (RelativeDual B A))
      (ModuleCat.of A (RelativeDual B A)) i) : e = 0 := by
  letI : Module.Free B (RelativeDual B A) :=
    Module.Free.of_equiv (RelativeDual.linearEquiv B A).symm
  letI : Module.Free B
      ((ModuleCat.restrictScalars (algebraMap B A)).obj
        (ModuleCat.of A (RelativeDual B A))) :=
    Module.Free.of_equiv (algebraRestrictionEquiv B A (RelativeDual B A)).symm
  haveI : Projective ((ModuleCat.restrictScalars (algebraMap B A)).obj
      (ModuleCat.of A (RelativeDual B A))) :=
    inferInstance
  apply (relativeDualExtEquiv B A (ModuleCat.of A (RelativeDual B A)) i).injective
  rw [map_zero]
  exact Ext.eq_zero_of_hasProjectiveDimensionLT _ 1 hi

end Ext

/-- Finite injective dimension follows from the actual global-dimension
bound on the regular base, for all modules in the Ext test. -/
theorem relativeDual_hasInjectiveDimensionLE [Module.Free B A]
    [IsRegularRing B] {d : ℕ} (hd : ringKrullDim B ≤ d) :
    HasInjectiveDimensionLE (ModuleCat.of A (RelativeDual B A)) d := by
  letI := HasExt.standard (ModuleCat.{u} A)
  letI := HasExt.standard (ModuleCat.{u} B)
  apply HasInjectiveDimensionLT.mk
  intro i hi X e
  letI := TauCeti.IsRegularRing.hasProjectiveDimensionLE hd
    ((ModuleCat.restrictScalars (algebraMap B A)).obj X)
  apply (relativeDualExtEquiv B A X i).injective
  rw [map_zero]
  exact Ext.eq_zero_of_hasProjectiveDimensionLT _ (d + 1) hi

/-- The algebraic definition of a dualizing module: finite generation,
finite injective dimension, an isomorphism given by homotheties, and vanishing
of the positive self-Ext groups. Each clause refers to the actual module. -/
def IsDualizingModule (M : Type u) [AddCommGroup M] [Module A M] : Prop :=
  IsNoetherianRing A ∧ Module.Finite A M ∧
    (∃ d : ℕ, HasInjectiveDimensionLE (ModuleCat.of A M) d) ∧
    (Function.Bijective (fun a : A => LinearMap.lsmul A M a)) ∧
    (letI := HasExt.standard (ModuleCat.{u} A)
     ∀ i : ℕ, 0 < i → ∀ e : Ext (ModuleCat.of A M) (ModuleCat.of A M) i, e = 0)

/-- The dualizing property is proved from the algebra, not included among
hypotheses on a proposed canonical module. -/
theorem relativeDual_isDualizing [Module.Free B A] [Module.Finite B A]
    [IsRegularRing B] {d : ℕ} (hd : ringKrullDim B ≤ d) :
    IsDualizingModule A (RelativeDual B A) := by
  letI := IsNoetherianRing.of_finite B A
  haveI : Module.Finite B (RelativeDual B A) :=
    Module.Finite.equiv (RelativeDual.linearEquiv B A).symm
  refine ⟨inferInstance, Module.Finite.of_restrictScalars_finite B A _,
    ⟨d, relativeDual_hasInjectiveDimensionLE B A hd⟩, ?_, ?_⟩
  · have hfun : (fun a : A => LinearMap.lsmul A (RelativeDual B A) a) =
        relativeDualHomothetyEquiv (B := B) (A := A) := by
      funext a
      apply LinearMap.ext
      intro f
      exact (relativeDualHomothetyEquiv_apply a f).symm
    rw [hfun]
    exact (relativeDualHomothetyEquiv (B := B) (A := A)).bijective
  · letI := HasExt.standard (ModuleCat.{u} A)
    letI := HasExt.standard (ModuleCat.{u} B)
    exact relativeDual_selfExt_eq_zero B A

end HigherSpecht
end
end CanonicalSource8

section CanonicalSource9
/- Source: HigherSpecht/CyclicDualizingModule.lean -/



/-!
# Cyclic dualizing modules and the usual local Gorenstein condition

Cyclicity here means that one actual element generates the module. Faithful
homotheties make that cyclic generator an isomorphism with the regular module.
Finite injective dimension then transfers to the regular module and to every
local ring. The Gorenstein predicate below is the standard local finite
self-injective-dimension condition, independent of a partition or a basis.
-/

noncomputable section

open CategoryTheory

universe u

namespace HigherSpecht

variable (A : Type u) [CommRing A]

/-- The ordinary local homological definition of a Noetherian Gorenstein ring. -/
def IsGorensteinRing : Prop :=
  IsNoetherianRing A ∧ ∀ p : PrimeSpectrum A,
    ∃ d : ℕ, HasInjectiveDimensionLE
      (ModuleCat.of (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)) d

variable {A}

/-- A cyclic module whose homothety action is faithful is literally the
regular module, via multiplication by the generator. -/
def cyclicFaithfulLinearEquiv {M : Type u} [AddCommGroup M] [Module A M]
    (hfaithful : Function.Injective (fun a : A => LinearMap.lsmul A M a))
    (f : M) (hf : Submodule.span A {f} = ⊤) : A ≃ₗ[A] M := by
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton A M f) :=
    (Submodule.span_singleton_eq_top_iff A f).mp hf
  apply LinearEquiv.ofBijective (LinearMap.toSpanSingleton A M f)
  refine ⟨?_, hsurj⟩
  intro a b hab
  apply hfaithful
  ext g
  obtain ⟨c, rfl⟩ := hsurj g
  change a • (c • f) = b • (c • f)
  rw [smul_comm a c, smul_comm b c]
  exact congrArg (fun x : M => c • x) hab

@[simp] theorem cyclicFaithfulLinearEquiv_apply
    {M : Type u} [AddCommGroup M] [Module A M]
    (hfaithful : Function.Injective (fun a : A => LinearMap.lsmul A M a))
    (f : M) (hf : Submodule.span A {f} = ⊤) (a : A) :
    cyclicFaithfulLinearEquiv hfaithful f hf a = a • f := rfl

/-- Noetherian localization preserves the actual self-injective dimension
bound. This supplies the local condition at every prime. -/
theorem isGorensteinRing_of_hasInjectiveDimensionLE
    [IsNoetherianRing A] {d : ℕ}
    (h : HasInjectiveDimensionLE (ModuleCat.of A A) d) : IsGorensteinRing A := by
  refine ⟨inferInstance, ?_⟩
  intro p
  let S := p.asIdeal.primeCompl
  letI := h
  have hloc := (ModuleCat.of A A).localizedModule_hasInjectiveDimensionLE d S
  letI : IsLocalizedModule S ((ModuleCat.of A A).localizedModuleMkLinearMap S) :=
    ModuleCat.localizedModule_isLocalizedModule (ModuleCat.of A A) S
  let e : (ModuleCat.of A A).localizedModule S ≃ₗ[Localization S] Localization S :=
    LinearEquiv.extendScalarsOfIsLocalization S (Localization S)
      (IsLocalizedModule.linearEquiv S
        ((ModuleCat.of A A).localizedModuleMkLinearMap S)
        (Algebra.linearMap A (Localization S)))
  exact ⟨d, (ModuleCat.hasInjectiveDimensionLE_iff_of_linearEquiv e d).mp hloc⟩

/-- A cyclic dualizing module gives the standard local Gorenstein condition. -/
theorem isGorensteinRing_of_cyclic_dualizing [IsNoetherianRing A]
    {M : Type u} [AddCommGroup M] [Module A M]
    (hM : IsDualizingModule A M) (f : M) (hf : Submodule.span A {f} = ⊤) :
    IsGorensteinRing A := by
  obtain ⟨d, hd⟩ := hM.2.2.1
  let e := cyclicFaithfulLinearEquiv hM.2.2.2.1.injective f hf
  apply isGorensteinRing_of_hasInjectiveDimensionLE
    ((ModuleCat.hasInjectiveDimensionLE_iff_of_linearEquiv
      (M := ModuleCat.of A A) (N := ModuleCat.of A M) e d).mpr hd)

variable (B : Type u) [CommRing B] [Algebra B A]

/-- The relative dual is cyclic exactly when it is actually free of rank
one with a specified regular-module equivalence. -/
theorem relativeDual_cyclic_iff_nonempty_equiv
    [Module.Free B A] [Module.Finite B A] :
    (∃ f : RelativeDual B A, Submodule.span A {f} = ⊤) ↔
      Nonempty (A ≃ₗ[A] RelativeDual B A) := by
  constructor
  · rintro ⟨f, hf⟩
    have hi : Function.Injective (fun a : A => LinearMap.lsmul A (RelativeDual B A) a) := by
      have heq : (fun a : A => LinearMap.lsmul A (RelativeDual B A) a) =
          relativeDualHomothetyEquiv (B := B) (A := A) := by
        funext a
        apply LinearMap.ext
        intro g
        exact (relativeDualHomothetyEquiv_apply a g).symm
      rw [heq]
      exact (relativeDualHomothetyEquiv (B := B) (A := A)).injective
    exact ⟨cyclicFaithfulLinearEquiv hi f hf⟩
  · rintro ⟨e⟩
    refine ⟨e 1, (Submodule.span_singleton_eq_top_iff A _).mpr ?_⟩
    intro g
    refine ⟨e.symm g, ?_⟩
    rw [← e.map_smul, smul_eq_mul, mul_one, e.apply_symm_apply]

/-- Cyclicity of the proven dualizing module establishes Gorensteinness at
all primes, rather than merely a type-one numerical statement. -/
theorem relativeDual_cyclic_isGorenstein
    [Module.Free B A] [Module.Finite B A] [IsRegularRing B]
    {d : ℕ} (hd : ringKrullDim B ≤ d)
    (hcyc : ∃ f : RelativeDual B A, Submodule.span A {f} = ⊤) :
    IsGorensteinRing A := by
  letI := IsNoetherianRing.of_finite B A
  obtain ⟨f, hf⟩ := hcyc
  exact isGorensteinRing_of_cyclic_dualizing
    (relativeDual_isDualizing B A hd) f hf

end HigherSpecht
end
end CanonicalSource9

section CanonicalSource10
/- Source: HigherSpecht/RelativeDualGrading.lean -/



/-!
# The normalized grading of the actual relative dual

The underlying module is Hom_B(A,B), with the actual multiplication action
from FiniteDuality.  Its degree-q piece consists precisely of maps sending
A_t into B_(t+q-W), where W is the sum of the elementary-parameter degrees.
This characterization proves compatibility with the original polynomial
grading and fixes the normalization of the canonical module explicitly.
-/

noncomputable section
open TauCeti Module MvPolynomial Finset
open scoped Classical

namespace HigherSpecht

/-- Restriction of the coefficient action on the actual linear dual. -/
instance (priority := 100) relativeDual_coefficientModule
    {K B A : Type*} [CommRing K] [CommRing B] [CommRing A]
    [Algebra K B] [Algebra B A] : Module K (RelativeDual B A) :=
  inferInstanceAs (Module K (Module.Dual B A))

@[simp] theorem relativeDual_coefficient_smul_apply
    {K B A : Type*} [CommRing K] [CommRing B] [CommRing A]
    [Algebra K B] [Algebra B A]
    (c : K) (f : RelativeDual B A) (x : A) :
    (c • f) x = c • f x := rfl

instance relativeDual_coefficientBaseScalarTower
    {K B A : Type*} [CommRing K] [CommRing B] [CommRing A]
    [Algebra K B] [Algebra B A] : IsScalarTower K B (RelativeDual B A) :=
  inferInstanceAs (IsScalarTower K B (Module.Dual B A))

instance relativeDual_coefficientScalarTower
    {K B A : Type*} [CommRing K] [CommRing B] [CommRing A]
    [Algebra K B] [Algebra B A] [Algebra K A] [IsScalarTower K B A] :
    IsScalarTower K A (RelativeDual B A) :=
  IsScalarTower.of_algebraMap_smul fun c f => by
    apply RelativeDual.ext
    intro x
    rw [RelativeDual.smul_apply, relativeDual_coefficient_smul_apply (K := K)]
    have h := ((RelativeDual.toLinearMap B A f).restrictScalars K).map_smul c x
    simpa only [LinearMap.restrictScalars_apply, Algebra.smul_def,
      mul_comm x (algebraMap K A c)] using h

instance relativeDual_coefficientSMulComm
    {K B A : Type*} [CommRing K] [CommRing B] [CommRing A]
    [Algebra K B] [Algebra B A] [Algebra K A] [IsScalarTower K B A] :
    SMulCommClass K A (RelativeDual B A) where
  smul_comm c a f := by
    apply RelativeDual.ext
    intro x
    simp only [relativeDual_coefficient_smul_apply (K := K), RelativeDual.smul_apply]

variable (K : Type*) [Field K]

def elementaryCanonicalShift (m : ℕ) : ℤ :=
  ∑ j : Fin m, (j.val + 1 : ℤ)

abbrev UntruncatedRelativeDual (n : ℕ) (lam : YoungDiagram) :=
  RelativeDual (ElementaryParameterRing K n lam) (UntruncatedRing K n lam)

def untruncatedRelativeDualBasis
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Basis (SpecialFiberMonomialIndex n lam) (ElementaryParameterRing K n lam)
      (UntruncatedRelativeDual K n lam) := by
  letI := finite_specialFiberMonomialIndex n lam hk
  exact (untruncatedMonomialParameterBasis K n lam hk).dualBasis.map
    (RelativeDual.linearEquiv _ _).symm

def relativeDualCoefficientBasis
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Basis ((Fin (n - lam.card) →₀ ℕ) × SpecialFiberMonomialIndex n lam) K
      (UntruncatedRelativeDual K n lam) :=
  (MvPolynomial.basisMonomials (Fin (n - lam.card)) K).smulTower
    (untruncatedRelativeDualBasis K n lam hk)

theorem relativeDualCoefficientBasis_repr
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (f : UntruncatedRelativeDual K n lam)
    (a : Fin (n - lam.card) →₀ ℕ) (i : SpecialFiberMonomialIndex n lam) :
    (relativeDualCoefficientBasis K n lam hk).repr f (a, i) =
      (f (untruncatedMonomialParameterBasis K n lam hk i)).coeff a := by
  simp only [relativeDualCoefficientBasis, Basis.smulTower_repr,
    untruncatedRelativeDualBasis, Basis.map_repr, Basis.dualBasis_repr,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply, RelativeDual.linearEquiv_apply,
    MvPolynomial.basisMonomials]
  rfl

def relativeDualBasisDegree {n : ℕ} {lam : YoungDiagram}
    (i : (Fin (n - lam.card) →₀ ℕ) × SpecialFiberMonomialIndex n lam) : ℤ :=
  elementaryWeight i.1 + elementaryCanonicalShift (n - lam.card) - i.2.val.degree

def untruncatedRelativeDualGrading
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    InternalGrading K (UntruncatedRelativeDual K n lam) :=
  homogeneousBasisGrading (relativeDualCoefficientBasis K n lam hk) relativeDualBasisDegree

theorem mem_untruncatedRelativeDualGrading_iff_basis
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (q : ℤ) (f : UntruncatedRelativeDual K n lam) :
    f ∈ (untruncatedRelativeDualGrading K n lam hk).piece q ↔
      ∀ i : SpecialFiberMonomialIndex n lam,
        f (untruncatedMonomialParameterBasis K n lam hk i) ∈
          elementaryWeightedPiece K (n - lam.card)
            (q + i.val.degree - elementaryCanonicalShift (n - lam.card)) := by
  rw [untruncatedRelativeDualGrading, mem_homogeneousBasisGrading_iff]
  constructor
  · intro h i a ha
    have heq := h (a, i) (by rwa [relativeDualCoefficientBasis_repr])
    rw [← elementaryWeight_cast]
    change (elementaryWeight a : ℤ) + elementaryCanonicalShift (n - lam.card) -
      i.val.degree = q at heq
    omega
  · intro h i hi
    rw [relativeDualCoefficientBasis_repr] at hi
    have heq := h i.2 hi
    rw [← elementaryWeight_cast] at heq
    change (elementaryWeight i.1 : ℤ) + elementaryCanonicalShift (n - lam.card) -
      i.2.val.degree = q
    omega

/-- Intrinsic characterization of the normalized grading.  Both sides use
the actual polynomial homogeneous pieces, not a profile on a basis index. -/
theorem mem_untruncatedRelativeDualGrading_iff
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (q : ℤ) (f : UntruncatedRelativeDual K n lam) :
    f ∈ (untruncatedRelativeDualGrading K n lam hk).piece q ↔
      ∀ t (x : UntruncatedRing K n lam),
        x ∈ quotientIntegerPiece (untruncatedIdeal K n lam) t →
        f x ∈ elementaryWeightedPiece K (n - lam.card)
          (t + q - elementaryCanonicalShift (n - lam.card)) := by
  rw [mem_untruncatedRelativeDualGrading_iff_basis]
  letI := finite_specialFiberMonomialIndex n lam hk
  letI : Fintype (SpecialFiberMonomialIndex n lam) := Fintype.ofFinite _
  let b := untruncatedMonomialParameterBasis K n lam hk
  constructor
  · intro hf t x hx
    rw [← b.sum_repr x]
    change (RelativeDual.toLinearMap _ _ f) (∑ i, b.repr x i • b i) ∈ _
    rw [map_sum]
    apply Submodule.sum_mem
    intro i hi
    rw [map_smul, smul_eq_mul]
    have hcoeff := parameterBasis_repr_homogeneous K n lam hk hx i
    have hprod := MvPolynomial.IsWeightedHomogeneous.mul hcoeff (hf i)
    change MvPolynomial.IsWeightedHomogeneous (elementaryIntegerWeights (n - lam.card))
      (((untruncatedMonomialParameterBasis K n lam hk).repr x i) *
        f (untruncatedMonomialParameterBasis K n lam hk i))
      (t + q - elementaryCanonicalShift (n - lam.card))
    convert hprod using 1 <;> ring
  · intro hf i
    have hbi : b i ∈ quotientIntegerPiece (untruncatedIdeal K n lam) (i.val.degree : ℤ) := by
      rw [untruncatedMonomialParameterBasis_apply]
      exact quotientIntegerPiece_mk _ (MvPolynomial.isHomogeneous_monomial 1 rfl)
    simpa only [add_comm (i.val.degree : ℤ) q] using hf _ (b i) hbi

theorem relativeDual_smul_mem_piece
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    {d q : ℤ} {a : UntruncatedRing K n lam} {f : UntruncatedRelativeDual K n lam}
    (ha : a ∈ quotientIntegerPiece (untruncatedIdeal K n lam) d)
    (hf : f ∈ (untruncatedRelativeDualGrading K n lam hk).piece q) :
    a • f ∈ (untruncatedRelativeDualGrading K n lam hk).piece (d + q) := by
  rw [mem_untruncatedRelativeDualGrading_iff] at hf ⊢
  intro t x hx
  rw [RelativeDual.smul_apply]
  convert hf (t + d) (x * a) (quotientIntegerPiece_mul _ hx ha) using 1 <;> ring

include K in
theorem specialFiber_basis_degree_le
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (i : SpecialFiberMonomialIndex n lam) :
    i.val.degree ≤ springerTopDegree (adjoinOnes lam (n - lam.card)) := by
  let mu := adjoinOnes lam (n - lam.card)
  have hcard : mu.card = n := by simp only [mu, adjoinOnes_card, Nat.add_sub_of_le hk]
  by_contra! hi
  have hzeroAt (N : ℕ) (hN : mu.card = N) :
      quotientHomogeneousPiece (untruncatedIdeal K N mu) i.val.degree = ⊥ := by
    subst N
    exact springer_homogeneousPiece_eq_bot_of_top_lt (K := K) mu hi
  have hzero := hzeroAt n hcard
  let b := untruncatedStandardMonomialBasis (R := K) (show mu.card ≤ n from hcard.le)
  have hmem : b i ∈ quotientHomogeneousPiece (untruncatedIdeal K n mu) i.val.degree := by
    rw [untruncatedStandardMonomialBasis_apply]
    exact ⟨_, MvPolynomial.isHomogeneous_monomial 1 rfl, rfl⟩
  rw [hzero] at hmem
  exact b.ne_zero i hmem

theorem relativeDual_piece_eq_bot_below
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) {q : ℤ}
    (hq : q < elementaryCanonicalShift (n - lam.card) -
      springerTopDegree (adjoinOnes lam (n - lam.card))) :
    (untruncatedRelativeDualGrading K n lam hk).piece q = ⊥ := by
  apply homogeneousBasisGrading_piece_eq_bot_of_lt
    (relativeDualCoefficientBasis K n lam hk) relativeDualBasisDegree
    (elementaryCanonicalShift (n - lam.card) -
      springerTopDegree (adjoinOnes lam (n - lam.card))) _ hq
  intro i
  have hdegree := specialFiber_basis_degree_le K n lam hk i.2
  have hweight : (0 : ℤ) ≤ elementaryWeight i.1 := Int.natCast_nonneg _
  dsimp only [relativeDualBasisDegree]
  exact_mod_cast (show elementaryCanonicalShift (n - lam.card) -
      (springerTopDegree (adjoinOnes lam (n - lam.card)) : ℤ) ≤
      (elementaryWeight i.1 : ℤ) + elementaryCanonicalShift (n - lam.card) -
        (i.2.val.degree : ℤ) by omega)

end HigherSpecht
end
end CanonicalSource10

section CanonicalSource11
/- Source: HigherSpecht/DualHeadSocle.lean -/



/-!
# The actual dual head and ideal annihilator

For a finite algebra Q over a field, the quotient of Hom_K(Q,K) by the
action of an ideal J is naturally dual to the elements of Q killed by J.
The map is literal restriction of functionals.  Its kernel is proved by
double annihilator duality, so neither the socle nor the generator number
is defined through a desired dimension formula.
-/

noncomputable section
open Module
open scoped Classical

namespace HigherSpecht

variable {K Q : Type*} [Field K] [CommRing Q] [Algebra K Q]

def subspaceKilledSubspace (P : Submodule K Q) : Submodule K Q where
  carrier := {x | ∀ a ∈ P, a * x = 0}
  zero_mem' a ha := mul_zero a
  add_mem' hx hy a ha := by rw [mul_add, hx a ha, hy a ha, add_zero]
  smul_mem' c x hx a ha := by rw [mul_smul_comm, hx a ha, smul_zero]

def dualSubspaceAction (P : Submodule K Q) : Submodule K (Module.Dual K Q) :=
  Submodule.span K {f | ∃ a ∈ P, ∃ g : Module.Dual K Q,
    f = g.comp (LinearMap.mulRight K a)}

theorem dualSubspaceAction_coannihilator (P : Submodule K Q) :
    (dualSubspaceAction P).dualCoannihilator = subspaceKilledSubspace P := by
  ext x
  change x ∈ ((dualSubspaceAction P).dualCoannihilator : Set Q) ↔ _
  rw [dualSubspaceAction, Submodule.coe_dualCoannihilator_span]
  constructor
  · intro hx a ha
    apply (Module.forall_dual_apply_eq_zero_iff K (a * x)).mp
    intro f
    have h := hx (f.comp (LinearMap.mulRight K a)) ⟨a, ha, f, rfl⟩
    simpa only [LinearMap.comp_apply, LinearMap.mulRight_apply, mul_comm x] using h
  · intro hx f hf
    obtain ⟨a, ha, g, rfl⟩ := hf
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply,
      mul_comm x a, hx a ha, map_zero]

theorem dualSubspaceAction_eq_annihilator [Module.Finite K Q] (P : Submodule K Q) :
    dualSubspaceAction P = (subspaceKilledSubspace P).dualAnnihilator := by
  rw [← dualSubspaceAction_coannihilator]
  exact Subspace.dualCoannihilator_dualAnnihilator_eq.symm

theorem mem_dualSubspaceAction_iff [Module.Finite K Q]
    (P : Submodule K Q) (f : Module.Dual K Q) :
    f ∈ dualSubspaceAction P ↔ ∀ x ∈ subspaceKilledSubspace P, f x = 0 := by
  rw [dualSubspaceAction_eq_annihilator, Submodule.mem_dualAnnihilator]

def idealKilledSubspace (J : Ideal Q) : Submodule K Q where
  carrier := {x | ∀ a ∈ J, a * x = 0}
  zero_mem' a ha := mul_zero a
  add_mem' hx hy a ha := by rw [mul_add, hx a ha, hy a ha, add_zero]
  smul_mem' c x hx a ha := by rw [mul_smul_comm, hx a ha, smul_zero]

def dualIdealAction (J : Ideal Q) : Submodule K (Module.Dual K Q) :=
  Submodule.span K {f | ∃ a ∈ J, ∃ g : Module.Dual K Q,
    f = g.comp (LinearMap.mulRight K a)}

theorem dualIdealAction_coannihilator (J : Ideal Q) :
    (dualIdealAction (K := K) J).dualCoannihilator = idealKilledSubspace (K := K) J := by
  ext x
  change x ∈ ((dualIdealAction (K := K) J).dualCoannihilator : Set Q) ↔ _
  rw [dualIdealAction, Submodule.coe_dualCoannihilator_span]
  constructor
  · intro hx a ha
    apply (Module.forall_dual_apply_eq_zero_iff K (a * x)).mp
    intro f
    have h := hx (f.comp (LinearMap.mulRight K a)) ⟨a, ha, f, rfl⟩
    simpa only [LinearMap.comp_apply, LinearMap.mulRight_apply, mul_comm x] using h
  · intro hx f hf
    obtain ⟨a, ha, g, rfl⟩ := hf
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply,
      mul_comm x a, hx a ha, map_zero]

theorem dualIdealAction_eq_annihilator [Module.Finite K Q] (J : Ideal Q) :
    dualIdealAction (K := K) J = (idealKilledSubspace (K := K) J).dualAnnihilator := by
  rw [← dualIdealAction_coannihilator]
  exact Subspace.dualCoannihilator_dualAnnihilator_eq.symm

theorem mem_dualIdealAction_iff [Module.Finite K Q] (J : Ideal Q)
    (f : Module.Dual K Q) :
    f ∈ dualIdealAction (K := K) J ↔ ∀ x ∈ idealKilledSubspace (K := K) J, f x = 0 := by
  rw [dualIdealAction_eq_annihilator, Submodule.mem_dualAnnihilator]

/-- The duality map is restriction to the actual J-annihilator. -/
def dualHeadSocleEquiv [Module.Finite K Q] (J : Ideal Q) :
    (Module.Dual K Q ⧸ dualIdealAction (K := K) J) ≃ₗ[K]
      Module.Dual K (idealKilledSubspace (K := K) J) :=
  (Submodule.quotEquivOfEq _ _ (dualIdealAction_eq_annihilator J)).trans
    (Subspace.quotAnnihilatorEquiv (idealKilledSubspace (K := K) J))

@[simp] theorem dualHeadSocleEquiv_apply [Module.Finite K Q]
    (J : Ideal Q) (f : Module.Dual K Q) (x : idealKilledSubspace (K := K) J) :
    dualHeadSocleEquiv J (Submodule.Quotient.mk f) x = f x := by
  simp only [dualHeadSocleEquiv, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, Subspace.quotAnnihilatorEquiv_apply,
    Submodule.dualRestrict_apply]

theorem finrank_dual_head [Module.Finite K Q] (J : Ideal Q) :
    Module.finrank K (Module.Dual K Q ⧸ dualIdealAction (K := K) J) =
      Module.finrank K (idealKilledSubspace (K := K) J) := by
  rw [(dualHeadSocleEquiv J).finrank_eq, Subspace.dual_finrank_eq]

/-- The span in the definition is exactly the actual ideal action on the
relative dual, transported across its definitional linear equivalence. -/
theorem dualIdealAction_eq_actual_action (J : Ideal Q) :
    dualIdealAction (K := K) J =
      ((J.restrictScalars K) • (⊤ : Submodule K (RelativeDual K Q))).map
        (RelativeDual.linearEquiv K Q).toLinearMap := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨a, ha, g, rfl⟩
    refine ⟨a • (RelativeDual.linearEquiv K Q).symm g,
      Submodule.smul_mem_smul ha Submodule.mem_top, ?_⟩
    ext x
    change (a • (RelativeDual.linearEquiv K Q).symm g) x = g (x * a)
    rw [RelativeDual.smul_apply]
    have h := congrArg (fun l : Module.Dual K Q => l (x * a))
      ((RelativeDual.linearEquiv K Q).apply_symm_apply g)
    simpa only [RelativeDual.linearEquiv_apply] using h
  · rintro f ⟨g, hg, rfl⟩
    refine Submodule.smul_induction_on hg ?_ ?_
    · intro a ha g hg
      apply Submodule.subset_span
      refine ⟨a, ha, RelativeDual.linearEquiv K Q g, ?_⟩
      ext x
      change (a • g) x = g (x * a)
      exact RelativeDual.smul_apply K Q a g x
    · intro x y hx hy
      simpa only [map_add] using (dualIdealAction J).add_mem hx hy

end HigherSpecht
end
end CanonicalSource11

section CanonicalSource12
/- Source: HigherSpecht/RelativeDualReduction.lean -/



/-!
# Specialization of the actual relative dual at the parameter origin

The map evaluates the coefficients of a B-linear functional at zero and
uses the genuine monomial basis of the Springer special fiber.  Its
evaluation and multiplication formulas identify it with base change of
Hom_B(A,B).  A literal constant-coefficient lift proves surjectivity.
-/

noncomputable section
open TauCeti Module MvPolynomial Finset
open scoped Classical

namespace HigherSpecht

variable (K : Type*) [Field K]

theorem untruncatedIdeal_le_specialFiber
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    untruncatedIdeal K n lam ≤
      untruncatedIdeal K n (adjoinOnes lam (n - lam.card)) := by
  have h := specialFiberIdeal_eq (R := K) lam (n - lam.card)
  rw [Nat.add_sub_of_le hk] at h
  rw [h]
  exact le_sup_left

def specialFiberQuotientMap (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    UntruncatedRing K n lam →ₐ[K]
      UntruncatedRing K n (adjoinOnes lam (n - lam.card)) :=
  Ideal.Quotient.factorₐ K (untruncatedIdeal_le_specialFiber K n lam hk)

@[simp] theorem specialFiberQuotientMap_mk
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (p : PolynomialRing n K) :
    specialFiberQuotientMap K n lam hk
      (Ideal.Quotient.mk (untruncatedIdeal K n lam) p) =
      Ideal.Quotient.mk (untruncatedIdeal K n (adjoinOnes lam (n - lam.card))) p := rfl

theorem specialFiberQuotientMap_surjective
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Function.Surjective (specialFiberQuotientMap K n lam hk) := by
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨Ideal.Quotient.mk _ p, rfl⟩

theorem specialFiberQuotientMap_parameter
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (j : Fin (n - lam.card)) :
    specialFiberQuotientMap K n lam hk (elementaryParameterClasses K n lam j) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have h := specialFiberIdeal_eq (R := K) lam (n - lam.card)
  rw [Nat.add_sub_of_le hk] at h
  rw [h]
  exact Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩)

theorem specialFiberQuotientMap_algebraMap
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (p : ElementaryParameterRing K n lam) :
    specialFiberQuotientMap K n lam hk
      (algebraMap (ElementaryParameterRing K n lam) (UntruncatedRing K n lam) p) =
      algebraMap K _ p.constantCoeff := by
  induction p using MvPolynomial.induction_on with
  | C c => simp only [untruncatedParameter_algebraMap, MvPolynomial.aeval_C,
      AlgHom.commutes, MvPolynomial.constantCoeff_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
      simp only [map_mul, hp, MvPolynomial.constantCoeff_X, mul_zero, map_zero,
        untruncatedParameter_algebraMap, MvPolynomial.aeval_X,
        specialFiberQuotientMap_parameter]

theorem specialFiberQuotientMap_smul
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (p : ElementaryParameterRing K n lam) (x : UntruncatedRing K n lam) :
    specialFiberQuotientMap K n lam hk (p • x) =
      p.constantCoeff • specialFiberQuotientMap K n lam hk x := by
  rw [Algebra.smul_def, map_mul, specialFiberQuotientMap_algebraMap]
  exact (Algebra.smul_def p.constantCoeff (specialFiberQuotientMap K n lam hk x)).symm

def specialFiberCoefficientBasis
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Basis (SpecialFiberMonomialIndex n lam) K
      (UntruncatedRing K n (adjoinOnes lam (n - lam.card))) :=
  untruncatedStandardMonomialBasis (R := K)
    (by rw [adjoinOnes_card, Nat.add_sub_of_le hk])

@[simp] theorem specialFiberQuotientMap_basis
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (i : SpecialFiberMonomialIndex n lam) :
    specialFiberQuotientMap K n lam hk
      (untruncatedMonomialParameterBasis K n lam hk i) =
      specialFiberCoefficientBasis K n lam hk i := by
  rw [untruncatedMonomialParameterBasis_apply]
  simp only [parameterMonomialClass, specialFiberQuotientMap_mk,
    specialFiberCoefficientBasis, untruncatedStandardMonomialBasis_apply]

theorem specialFiberQuotientMap_repr
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (x : UntruncatedRing K n lam) (i : SpecialFiberMonomialIndex n lam) :
    (specialFiberCoefficientBasis K n lam hk).repr
      (specialFiberQuotientMap K n lam hk x) i =
      ((untruncatedMonomialParameterBasis K n lam hk).repr x i).constantCoeff := by
  letI := finite_specialFiberMonomialIndex n lam hk
  letI : Fintype (SpecialFiberMonomialIndex n lam) := Fintype.ofFinite _
  conv_lhs => rw [← (untruncatedMonomialParameterBasis K n lam hk).sum_repr x]
  simp only [map_sum, specialFiberQuotientMap_smul, specialFiberQuotientMap_basis,
    map_smul, Basis.repr_self, Finsupp.sum_apply, Finset.sum_apply', Finsupp.smul_apply,
    Finsupp.single_apply]
  simp

def relativeDualReduction
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    UntruncatedRelativeDual K n lam →ₗ[K]
      RelativeDual K (UntruncatedRing K n (adjoinOnes lam (n - lam.card))) where
  toFun f := (specialFiberCoefficientBasis K n lam hk).constr K
    (fun i => (f (untruncatedMonomialParameterBasis K n lam hk i)).constantCoeff)
  map_add' f g := by
    let b := specialFiberCoefficientBasis K n lam hk
    let a := untruncatedMonomialParameterBasis K n lam hk
    change b.constr K (fun i => ((f + g) (a i)).constantCoeff) =
      b.constr K (fun i => (f (a i)).constantCoeff) +
        b.constr K (fun i => (g (a i)).constantCoeff)
    apply b.ext
    intro i
    simp only [Basis.constr_basis, RelativeDual.add_apply, LinearMap.add_apply, map_add]
  map_smul' c f := by
    let b := specialFiberCoefficientBasis K n lam hk
    let a := untruncatedMonomialParameterBasis K n lam hk
    change b.constr K (fun i => ((c • f) (a i)).constantCoeff) =
      c • b.constr K (fun i => (f (a i)).constantCoeff)
    apply b.ext
    intro i
    simp only [Basis.constr_basis, relativeDual_coefficient_smul_apply (K := K),
      LinearMap.smul_apply, MvPolynomial.constantCoeff_smul]

@[simp] theorem relativeDualReduction_basis
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (f : UntruncatedRelativeDual K n lam) (i : SpecialFiberMonomialIndex n lam) :
    relativeDualReduction K n lam hk f (specialFiberCoefficientBasis K n lam hk i) =
      (f (untruncatedMonomialParameterBasis K n lam hk i)).constantCoeff := by
  change ((specialFiberCoefficientBasis K n lam hk).constr K
    (fun j => (f (untruncatedMonomialParameterBasis K n lam hk j)).constantCoeff))
      (specialFiberCoefficientBasis K n lam hk i) = _
  exact Basis.constr_basis _ _ _ _

theorem relativeDualReduction_apply_quotient
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (f : UntruncatedRelativeDual K n lam) (x : UntruncatedRing K n lam) :
    relativeDualReduction K n lam hk f (specialFiberQuotientMap K n lam hk x) =
      (f x).constantCoeff := by
  letI := finite_specialFiberMonomialIndex n lam hk
  letI : Fintype (SpecialFiberMonomialIndex n lam) := Fintype.ofFinite _
  rw [← (untruncatedMonomialParameterBasis K n lam hk).sum_repr x]
  simp only [map_sum, specialFiberQuotientMap_smul, specialFiberQuotientMap_basis,
    map_smul, relativeDualReduction_basis, smul_eq_mul, map_mul]

theorem relativeDualReduction_smul
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (a : UntruncatedRing K n lam) (f : UntruncatedRelativeDual K n lam) :
    relativeDualReduction K n lam hk (a • f) =
      specialFiberQuotientMap K n lam hk a • relativeDualReduction K n lam hk f := by
  apply RelativeDual.ext
  intro z
  obtain ⟨x, rfl⟩ := specialFiberQuotientMap_surjective K n lam hk z
  rw [relativeDualReduction_apply_quotient, RelativeDual.smul_apply,
    RelativeDual.smul_apply, ← map_mul, relativeDualReduction_apply_quotient]

def relativeDualConstantLift
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (g : RelativeDual K (UntruncatedRing K n (adjoinOnes lam (n - lam.card)))) :
    UntruncatedRelativeDual K n lam :=
  RelativeDual.ofLinearMap _ _
    ((untruncatedMonomialParameterBasis K n lam hk).constr
      (ElementaryParameterRing K n lam)
      (fun i => MvPolynomial.C (g (specialFiberCoefficientBasis K n lam hk i))))

@[simp] theorem relativeDualConstantLift_basis
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (g : RelativeDual K (UntruncatedRing K n (adjoinOnes lam (n - lam.card))))
    (i : SpecialFiberMonomialIndex n lam) :
    relativeDualConstantLift K n lam hk g
      (untruncatedMonomialParameterBasis K n lam hk i) =
      MvPolynomial.C (g (specialFiberCoefficientBasis K n lam hk i)) :=
  Basis.constr_basis _ _ _ _

@[simp] theorem relativeDualReduction_constantLift
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (g : RelativeDual K (UntruncatedRing K n (adjoinOnes lam (n - lam.card)))) :
    relativeDualReduction K n lam hk (relativeDualConstantLift K n lam hk g) = g := by
  apply (RelativeDual.linearEquiv K _).injective
  apply (specialFiberCoefficientBasis K n lam hk).ext
  intro i
  change relativeDualReduction K n lam hk (relativeDualConstantLift K n lam hk g)
    (specialFiberCoefficientBasis K n lam hk i) = g (specialFiberCoefficientBasis K n lam hk i)
  rw [relativeDualReduction_basis, relativeDualConstantLift_basis,
    MvPolynomial.constantCoeff_C]

theorem relativeDualReduction_surjective
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Function.Surjective (relativeDualReduction K n lam hk) :=
  fun g => ⟨relativeDualConstantLift K n lam hk g, relativeDualReduction_constantLift K n lam hk g⟩

theorem relativeDualReduction_eq_zero_iff
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (f : UntruncatedRelativeDual K n lam) :
    relativeDualReduction K n lam hk f = 0 ↔
      ∀ i : SpecialFiberMonomialIndex n lam,
        (f (untruncatedMonomialParameterBasis K n lam hk i)).constantCoeff = 0 := by
  constructor
  · intro h i
    simpa only [relativeDualReduction_basis, RelativeDual.zero_apply] using
      congrArg (fun g => g (specialFiberCoefficientBasis K n lam hk i)) h
  · intro h
    apply (RelativeDual.linearEquiv K _).injective
    apply (specialFiberCoefficientBasis K n lam hk).ext
    intro i
    change relativeDualReduction K n lam hk f (specialFiberCoefficientBasis K n lam hk i) =
      (0 : RelativeDual K (UntruncatedRing K n (adjoinOnes lam (n - lam.card))))
        (specialFiberCoefficientBasis K n lam hk i)
    rw [relativeDualReduction_basis, RelativeDual.zero_apply]
    exact h i

end HigherSpecht
end
end CanonicalSource12

section CanonicalSource13
/- Source: HigherSpecht/QuotientPositivePieces.lean -/



/-!
# Positive-degree action and the actual Springer socle

The positive part is the sum of the genuine quotient homogeneous pieces.
Its annihilator is proved to be the subspace killed by the coordinate
classes.  The special-fiber map carries the original positive part onto
the special-fiber positive part.  These statements supply the actual
augmentation action used in graded Nakayama and dual-head duality.
-/

noncomputable section
open TauCeti Module MvPolynomial
open scoped Classical

namespace HigherSpecht

variable {K : Type*} [Field K] {n : ℕ}

def quotientPositivePiece (I : Ideal (PolynomialRing n K)) :
    Submodule K (PolynomialRing n K ⧸ I) :=
  ⨆ (d : ℤ) (_ : 0 < d), quotientIntegerPiece I d

theorem quotient_positive_coordinate (I : Ideal (PolynomialRing n K)) (i : Fin n) :
    Ideal.Quotient.mk I (MvPolynomial.X i) ∈ quotientPositivePiece I := by
  apply Submodule.mem_iSup_of_mem (1 : ℤ)
  apply Submodule.mem_iSup_of_mem (by norm_num : (0 : ℤ) < 1)
  simpa only [Nat.cast_one] using quotientIntegerPiece_mk I (MvPolynomial.isHomogeneous_X K i)

theorem homogeneous_constantCoeff_eq_zero {d : ℕ} {p : PolynomialRing n K}
    (hp : p.IsHomogeneous d) (hd : d ≠ 0) : p.constantCoeff = 0 := by
  by_contra hc
  have heq := hp hc
  simp only [map_zero] at heq
  exact hd heq.symm

theorem quotientPositivePiece_annihilator (I : Ideal (PolynomialRing n K)) :
    subspaceKilledSubspace (quotientPositivePiece I) =
      (quotientVariableAnnihilator I).restrictScalars K := by
  ext z
  constructor
  · intro hz i
    exact hz _ (quotient_positive_coordinate I i)
  · intro hz a ha
    refine Submodule.iSup_induction _ (motive := fun a => a * z = 0) ha
      (fun d a ha => ?_) (zero_mul _) (fun a b ha hb => by rw [add_mul, ha, hb, add_zero])
    refine Submodule.iSup_induction _ (motive := fun a => a * z = 0) ha
      (fun hd a ha => ?_) (zero_mul _) (fun a b ha hb => by rw [add_mul, ha, hb, add_zero])
    have hd0 : 0 ≤ d := le_of_lt hd
    have ha' : a ∈ quotientHomogeneousPiece I d.toNat := by
      simpa only [quotientIntegerPiece, if_pos hd0] using ha
    obtain ⟨p, hp, rfl⟩ := ha'
    change Ideal.Quotient.mk I p * z = 0
    rw [quotient_mul_eq_constant_smul_of_variables_annihilate I hz p,
      homogeneous_constantCoeff_eq_zero hp (by omega), zero_smul]

theorem quotientPositivePiece_factor_image
    {I J : Ideal (PolynomialRing n K)} (hIJ : I ≤ J) :
    (quotientPositivePiece I).map (Ideal.Quotient.factorₐ K hIJ).toLinearMap =
      quotientPositivePiece J := by
  simp only [quotientPositivePiece, Submodule.map_iSup]
  congr 1
  funext d
  congr 1
  funext hd
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact quotientIntegerPiece_factor_mem hIJ hy
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := quotientIntegerPiece_factor_lift hIJ hx
    exact ⟨y, hy, hxy⟩

theorem specialFiber_positive_image
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    (quotientPositivePiece (untruncatedIdeal K n lam)).map
      (specialFiberQuotientMap K n lam hk).toLinearMap =
      quotientPositivePiece (untruncatedIdeal K n (adjoinOnes lam (n - lam.card))) :=
  quotientPositivePiece_factor_image _

theorem specialFiber_positive_annihilator
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    subspaceKilledSubspace
        (quotientPositivePiece (untruncatedIdeal K n (adjoinOnes lam (n - lam.card)))) =
      quotientHomogeneousPiece (untruncatedIdeal K n (adjoinOnes lam (n - lam.card)))
        (springerTopDegree (adjoinOnes lam (n - lam.card))) := by
  rw [quotientPositivePiece_annihilator]
  let mu := adjoinOnes lam (n - lam.card)
  have hcard : mu.card = n := by simp only [mu, adjoinOnes_card, Nat.add_sub_of_le hk]
  have htopAt (N : ℕ) (hN : mu.card = N) :
      (quotientVariableAnnihilator (untruncatedIdeal K N mu)).restrictScalars K =
        quotientHomogeneousPiece (untruncatedIdeal K N mu) (springerTopDegree mu) := by
    subst N
    ext z
    exact springer_variables_kill_iff_mem_top_piece (K := K) mu z
  exact htopAt n hcard

def untruncatedGradedAlgebra (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    GradedAlgebra (untruncatedInternalGrading K n lam hk).piece where
  toDecomposition := inferInstance
  toGradedMonoid :=
    { one_mem := by
        rw [untruncatedInternalGrading_piece]
        exact quotientIntegerPiece_one K _
      mul_mem := fun i j x y hx hy => by
        rw [untruncatedInternalGrading_piece] at hx hy ⊢
        exact quotientIntegerPiece_mul _ hx hy }

def relativeDualGradedSMul (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    SetLike.GradedSMul (untruncatedInternalGrading K n lam hk).piece
      (untruncatedRelativeDualGrading K n lam hk).piece where
  smul_mem := fun i j a f ha hf =>
    relativeDual_smul_mem_piece K n lam hk
      (by simpa only [untruncatedInternalGrading_piece] using ha) hf

end HigherSpecht
end
end CanonicalSource13

section CanonicalSource14
/- Source: HigherSpecht/RelativeDualGeneration.lean -/



/-!
# Generation of the normalized relative dual in its true lowest degree

Reduction at the elementary-parameter origin intertwines the actual
multiplication action.  Its kernel lies in the positive action, and the
positive action on the special-fiber dual lifts.  Dual-head duality and
the proved Springer socle concentration therefore put every other
homogeneous piece in the positive action.  Genuine graded Nakayama gives
generation of the full Hom module; no generation premise is assumed.
-/

noncomputable section
open TauCeti Module MvPolynomial Finset
open scoped Classical

namespace HigherSpecht

variable (K : Type*) [Field K]

def relativeDualPositiveAction (n : ℕ) (lam : YoungDiagram) :
    Submodule K (UntruncatedRelativeDual K n lam) :=
  quotientPositivePiece (untruncatedIdeal K n lam) • ⊤

def relativeDualReducedFunctional
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    UntruncatedRelativeDual K n lam →ₗ[K]
      Module.Dual K (UntruncatedRing K n (adjoinOnes lam (n - lam.card))) :=
  (RelativeDual.linearEquiv K _).toLinearMap.comp (relativeDualReduction K n lam hk)

@[simp] theorem relativeDualReducedFunctional_apply
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (f : UntruncatedRelativeDual K n lam)
    (x : UntruncatedRing K n (adjoinOnes lam (n - lam.card))) :
    relativeDualReducedFunctional K n lam hk f x = relativeDualReduction K n lam hk f x := rfl

theorem relativeDualReduction_ker_le_positive
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    LinearMap.ker (relativeDualReducedFunctional K n lam hk) ≤
      relativeDualPositiveAction K n lam := by
  intro f hf
  have hf0 : relativeDualReduction K n lam hk f = 0 :=
    (RelativeDual.linearEquiv K _).injective hf
  have hconst := (relativeDualReduction_eq_zero_iff K n lam hk f).mp hf0
  let b := relativeDualCoefficientBasis K n lam hk
  rw [← b.linearCombination_repr f, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  have hcoef : b.repr f i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have ha : i.1 ≠ 0 := by
    intro hzero
    rw [relativeDualCoefficientBasis_repr, hzero] at hcoef
    exact hcoef (hconst i.2)
  have hweight : 0 < elementaryWeight i.1 :=
    Nat.pos_of_ne_zero (fun h => ha ((elementaryWeight_eq_zero_iff i.1).mp h))
  change relativeDualCoefficientBasis K n lam hk i ∈ relativeDualPositiveAction K n lam
  rw [relativeDualCoefficientBasis, Basis.smulTower_apply,
    MvPolynomial.coe_basisMonomials, ← IsScalarTower.algebraMap_smul
      (R := ElementaryParameterRing K n lam) (A := UntruncatedRing K n lam)]
  apply Submodule.smul_mem_smul _ Submodule.mem_top
  apply Submodule.mem_iSup_of_mem (elementaryWeight i.1 : ℤ)
  apply Submodule.mem_iSup_of_mem (by exact_mod_cast hweight)
  exact parameter_monomial_mem_piece K n lam i.1

theorem specialFiber_dualPositive_le_image
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    dualSubspaceAction
      (quotientPositivePiece (untruncatedIdeal K n (adjoinOnes lam (n - lam.card)))) ≤
      (relativeDualPositiveAction K n lam).map
        (relativeDualReducedFunctional K n lam hk) := by
  apply Submodule.span_le.mpr
  rintro f ⟨a, ha, g, rfl⟩
  rw [← specialFiber_positive_image n lam hk] at ha
  obtain ⟨x, hx, hxa⟩ := ha
  change specialFiberQuotientMap K n lam hk x = a at hxa
  let g' : RelativeDual K (UntruncatedRing K n (adjoinOnes lam (n - lam.card))) := g
  let f' := relativeDualConstantLift K n lam hk g'
  refine ⟨x • f', Submodule.smul_mem_smul hx Submodule.mem_top, ?_⟩
  apply LinearMap.ext
  intro z
  change relativeDualReduction K n lam hk (x • f') z = _
  rw [relativeDualReduction_smul, relativeDualReduction_constantLift,
    hxa, RelativeDual.smul_apply]
  rfl

theorem relativeDual_mem_positive_of_reduction_mem
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (f : UntruncatedRelativeDual K n lam)
    (hf : relativeDualReducedFunctional K n lam hk f ∈
      dualSubspaceAction
        (quotientPositivePiece (untruncatedIdeal K n (adjoinOnes lam (n - lam.card))))) :
    f ∈ relativeDualPositiveAction K n lam := by
  obtain ⟨g, hg, hgf⟩ := specialFiber_dualPositive_le_image K n lam hk hf
  have hker : f - g ∈ LinearMap.ker (relativeDualReducedFunctional K n lam hk) := by
    rw [LinearMap.mem_ker, map_sub, hgf, sub_self]
  have hfg := relativeDualReduction_ker_le_positive K n lam hk hker
  simpa only [sub_add_cancel] using (relativeDualPositiveAction K n lam).add_mem hfg hg

theorem elementaryWeighted_constantCoeff_zero
    {m : ℕ} {p : MvPolynomial (Fin m) K} {d : ℤ}
    (hp : p ∈ elementaryWeightedPiece K m d) (hd : d ≠ 0) :
    p.constantCoeff = 0 := by
  by_contra hc
  have heq := hp hc
  rw [map_zero] at heq
  exact hd heq.symm

theorem relativeDual_piece_le_positive_of_ne
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (q : ℤ)
    (hq : q ≠ elementaryCanonicalShift (n - lam.card) -
      springerTopDegree (adjoinOnes lam (n - lam.card))) :
    (untruncatedRelativeDualGrading K n lam hk).piece q ≤
      relativeDualPositiveAction K n lam := by
  letI := finite_specialFiberMonomialIndex n lam hk
  letI : Fintype (SpecialFiberMonomialIndex n lam) := Fintype.ofFinite _
  letI : Module.Finite K (UntruncatedRing K n (adjoinOnes lam (n - lam.card))) :=
    Module.Finite.of_basis (specialFiberCoefficientBasis K n lam hk)
  intro f hf
  apply relativeDual_mem_positive_of_reduction_mem K n lam hk f
  rw [mem_dualSubspaceAction_iff]
  intro z hz
  rw [specialFiber_positive_annihilator n lam hk] at hz
  let D := springerTopDegree (adjoinOnes lam (n - lam.card))
  have hz' : z ∈ quotientIntegerPiece
      (untruncatedIdeal K n (adjoinOnes lam (n - lam.card))) (D : ℤ) := by
    simpa only [quotientIntegerPiece_nat, D] using hz
  obtain ⟨x, hx, hzx⟩ := quotientIntegerPiece_factor_lift
    (untruncatedIdeal_le_specialFiber K n lam hk) hz'
  change specialFiberQuotientMap K n lam hk x = z at hzx
  have hfx := (mem_untruncatedRelativeDualGrading_iff K n lam hk q f).mp hf D x hx
  rw [relativeDualReducedFunctional_apply, ← hzx, relativeDualReduction_apply_quotient]
  exact elementaryWeighted_constantCoeff_zero K hfx (by dsimp only [D]; omega)

/-- Actual graded generation, with the canonical normalization W. -/
theorem untruncatedRelativeDual_generated_in_degree
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    (untruncatedRelativeDualGrading K n lam hk).IsGeneratedInDegree
      (UntruncatedRing K n lam)
      (elementaryCanonicalShift (n - lam.card) -
        springerTopDegree (adjoinOnes lam (n - lam.card))) := by
  letI := untruncatedGradedAlgebra (K := K) n lam hk
  letI := relativeDualGradedSMul (K := K) n lam hk
  apply (InternalGrading.isGeneratedInDegree_iff_piece_le_positive_smul_top
    (untruncatedInternalGrading K n lam hk).piece
    (G := untruncatedRelativeDualGrading K n lam hk)
    (fun d hd => by
      rw [untruncatedInternalGrading_piece]
      exact quotientIntegerPiece_eq_bot_of_neg _ hd)
    (elementaryCanonicalShift (n - lam.card) -
      springerTopDegree (adjoinOnes lam (n - lam.card)))
    (fun q hq => relativeDual_piece_eq_bot_below K n lam hk hq) _).mpr
  intro q hq
  simpa only [untruncatedInternalGrading_piece, relativeDualPositiveAction,
    quotientPositivePiece] using relativeDual_piece_le_positive_of_ne K n lam hk q hq

end HigherSpecht
end
end CanonicalSource14

section CanonicalSource15
/- Source: HigherSpecht/RelativeDualLowestPiece.lean -/



/-!
# The true lowest canonical piece and its dimension

Restriction after parameter specialization identifies the lowest piece of
Hom_B(A,B)(-W) with the dual of the actual top piece of the Springer
fiber.  The inverse is the literal top homogeneous projection followed
by the constant-coefficient lift.  The dimension is consequently the
proved number of standard tableaux, in every characteristic.
-/

noncomputable section
open TauCeti Module MvPolynomial
open scoped Classical

namespace HigherSpecht

variable (K : Type*) [Field K]

def relativeDualGeneratingDegree (n : ℕ) (lam : YoungDiagram) : ℤ :=
  elementaryCanonicalShift (n - lam.card) -
    springerTopDegree (adjoinOnes lam (n - lam.card))

def specialFiberTopPiece (n : ℕ) (lam : YoungDiagram) :
    Submodule K (UntruncatedRing K n (adjoinOnes lam (n - lam.card))) :=
  quotientHomogeneousPiece (untruncatedIdeal K n (adjoinOnes lam (n - lam.card)))
    (springerTopDegree (adjoinOnes lam (n - lam.card)))

def relativeDualLowestPiece (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Submodule K (UntruncatedRelativeDual K n lam) :=
  (untruncatedRelativeDualGrading K n lam hk).piece (relativeDualGeneratingDegree n lam)

theorem relativeDualLowest_basis_constant
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    {f : UntruncatedRelativeDual K n lam} (hf : f ∈ relativeDualLowestPiece K n lam hk)
    (i : SpecialFiberMonomialIndex n lam) :
    f (untruncatedMonomialParameterBasis K n lam hk i) =
      MvPolynomial.C
        (f (untruncatedMonomialParameterBasis K n lam hk i)).constantCoeff := by
  have h := (mem_untruncatedRelativeDualGrading_iff_basis K n lam hk _ f).mp hf i
  have hle := specialFiber_basis_degree_le K n lam hk i
  by_cases heq : i.val.degree = springerTopDegree (adjoinOnes lam (n - lam.card))
  · have hd : relativeDualGeneratingDegree n lam + i.val.degree -
        elementaryCanonicalShift (n - lam.card) = 0 := by
      dsimp only [relativeDualGeneratingDegree]
      omega
    rw [hd] at h
    exact elementaryWeightedPiece_zero K (n - lam.card) h
  · have hlt : relativeDualGeneratingDegree n lam + i.val.degree -
      elementaryCanonicalShift (n - lam.card) < 0 := by
      dsimp only [relativeDualGeneratingDegree]
      omega
    rw [elementaryWeightedPiece_eq_bot_of_neg K _ hlt] at h
    rw [show f (untruncatedMonomialParameterBasis K n lam hk i) = 0 from h,
      map_zero, map_zero]

theorem relativeDualLowest_reduction_injective
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    {f : UntruncatedRelativeDual K n lam}
    (hf : f ∈ relativeDualLowestPiece K n lam hk)
    (hred : relativeDualReducedFunctional K n lam hk f = 0) : f = 0 := by
  apply (RelativeDual.linearEquiv _ _).injective
  apply (untruncatedMonomialParameterBasis K n lam hk).ext
  intro i
  change f (untruncatedMonomialParameterBasis K n lam hk i) =
    (0 : UntruncatedRelativeDual K n lam) (untruncatedMonomialParameterBasis K n lam hk i)
  rw [relativeDualLowest_basis_constant K n lam hk hf i]
  have hc := congrArg
    (fun g : Module.Dual K _ => g (specialFiberCoefficientBasis K n lam hk i)) hred
  simp only [relativeDualReducedFunctional_apply, relativeDualReduction_basis,
    LinearMap.zero_apply] at hc
  rw [hc, map_zero]
  rfl

def specialFiberTopProjection
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    UntruncatedRing K n (adjoinOnes lam (n - lam.card)) →ₗ[K]
      specialFiberTopPiece K n lam :=
  (quotientHomogeneousProjection
    (untruncatedIdeal K n (adjoinOnes lam (n - lam.card)))
    (untruncatedIdeal_isHomogeneous (by rw [adjoinOnes_card, Nat.add_sub_of_le hk]))
    (springerTopDegree (adjoinOnes lam (n - lam.card)))).codRestrict _
    (fun z => by
      change _ ∈ quotientHomogeneousPiece
        (untruncatedIdeal K n (adjoinOnes lam (n - lam.card)))
        (springerTopDegree (adjoinOnes lam (n - lam.card)))
      rw [← quotientHomogeneousProjection_range _
        (untruncatedIdeal_isHomogeneous (by rw [adjoinOnes_card, Nat.add_sub_of_le hk])) _]
      exact ⟨z, rfl⟩)

@[simp] theorem specialFiberTopProjection_of_mem
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (z : specialFiberTopPiece K n lam) :
    specialFiberTopProjection K n lam hk z = z := by
  apply Subtype.ext
  exact quotientHomogeneousProjection_eq_self_of_mem _ _ _ z.property

theorem specialFiberTopProjection_basis
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (i : SpecialFiberMonomialIndex n lam)
    (hi : i.val.degree ≠ springerTopDegree (adjoinOnes lam (n - lam.card))) :
    specialFiberTopProjection K n lam hk (specialFiberCoefficientBasis K n lam hk i) = 0 := by
  apply Subtype.ext
  rw [specialFiberCoefficientBasis, untruncatedStandardMonomialBasis_apply]
  change Ideal.Quotient.mk _ (MvPolynomial.homogeneousComponent _
    (MvPolynomial.monomial i.val 1)) = 0
  rw [MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial 1 rfl),
    if_neg hi.symm, map_zero]

def relativeDualLowestRestriction
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    relativeDualLowestPiece K n lam hk →ₗ[K] Module.Dual K (specialFiberTopPiece K n lam) :=
  ((specialFiberTopPiece K n lam).dualRestrict.comp
    (relativeDualReducedFunctional K n lam hk)).comp
      (relativeDualLowestPiece K n lam hk).subtype

@[simp] theorem relativeDualLowestRestriction_apply
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (f : relativeDualLowestPiece K n lam hk) (z : specialFiberTopPiece K n lam) :
    relativeDualLowestRestriction K n lam hk f z =
      relativeDualReduction K n lam hk f.val z.val := rfl

theorem relativeDualLowestRestriction_injective
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Function.Injective (relativeDualLowestRestriction K n lam hk) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  apply Subtype.ext
  apply relativeDualLowest_reduction_injective K n lam hk f.property
  apply (specialFiberCoefficientBasis K n lam hk).ext
  intro i
  by_cases hi : i.val.degree = springerTopDegree (adjoinOnes lam (n - lam.card))
  · have hbi : specialFiberCoefficientBasis K n lam hk i ∈ specialFiberTopPiece K n lam := by
      rw [specialFiberCoefficientBasis, untruncatedStandardMonomialBasis_apply]
      exact ⟨_, MvPolynomial.isHomogeneous_monomial 1 hi, rfl⟩
    have h := congrArg (fun g => g ⟨specialFiberCoefficientBasis K n lam hk i, hbi⟩)
      (show relativeDualLowestRestriction K n lam hk f = 0 from hf)
    exact h
  · have h := (mem_untruncatedRelativeDualGrading_iff_basis K n lam hk _ f.val).mp
      f.property i
    have hle := specialFiber_basis_degree_le K n lam hk i
    have hlt : relativeDualGeneratingDegree n lam + i.val.degree -
        elementaryCanonicalShift (n - lam.card) < 0 := by
      dsimp only [relativeDualGeneratingDegree]
      omega
    rw [elementaryWeightedPiece_eq_bot_of_neg K _ hlt] at h
    rw [relativeDualReducedFunctional_apply, relativeDualReduction_basis,
      show f.val (untruncatedMonomialParameterBasis K n lam hk i) = 0 from h,
      map_zero]
    rfl

theorem relativeDualLowestRestriction_surjective
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Function.Surjective (relativeDualLowestRestriction K n lam hk) := by
  intro ψ
  let g : RelativeDual K (UntruncatedRing K n (adjoinOnes lam (n - lam.card))) :=
    RelativeDual.ofLinearMap _ _ (ψ.comp (specialFiberTopProjection K n lam hk))
  let f := relativeDualConstantLift K n lam hk g
  have hf : f ∈ relativeDualLowestPiece K n lam hk := by
    rw [relativeDualLowestPiece, mem_untruncatedRelativeDualGrading_iff_basis]
    intro i
    rw [relativeDualConstantLift_basis]
    by_cases hi : i.val.degree = springerTopDegree (adjoinOnes lam (n - lam.card))
    · have hd : relativeDualGeneratingDegree n lam + i.val.degree -
          elementaryCanonicalShift (n - lam.card) = 0 := by
        dsimp only [relativeDualGeneratingDegree]
        omega
      rw [hd]
      exact MvPolynomial.isWeightedHomogeneous_C _ _
    · change MvPolynomial.C (ψ (specialFiberTopProjection K n lam hk
        (specialFiberCoefficientBasis K n lam hk i))) ∈ _
      rw [specialFiberTopProjection_basis K n lam hk i hi, map_zero, map_zero]
      exact Submodule.zero_mem _
  refine ⟨⟨f, hf⟩, ?_⟩
  ext z
  rw [relativeDualLowestRestriction_apply, relativeDualReduction_constantLift]
  change ψ (specialFiberTopProjection K n lam hk z) = ψ z
  rw [specialFiberTopProjection_of_mem]

def relativeDualLowestEquiv
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    relativeDualLowestPiece K n lam hk ≃ₗ[K] Module.Dual K (specialFiberTopPiece K n lam) :=
  LinearEquiv.ofBijective (relativeDualLowestRestriction K n lam hk)
    ⟨relativeDualLowestRestriction_injective K n lam hk,
      relativeDualLowestRestriction_surjective K n lam hk⟩

theorem relativeDualLowest_finite
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Module.Finite K (relativeDualLowestPiece K n lam hk) := by
  letI := finite_specialFiberMonomialIndex n lam hk
  letI : Fintype (SpecialFiberMonomialIndex n lam) := Fintype.ofFinite _
  letI : Module.Finite K (UntruncatedRing K n (adjoinOnes lam (n - lam.card))) :=
    Module.Finite.of_basis (specialFiberCoefficientBasis K n lam hk)
  exact (relativeDualLowestEquiv K n lam hk).symm.finiteDimensional

theorem relativeDualLowest_finrank
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Module.finrank K (relativeDualLowestPiece K n lam hk) =
      Fintype.card (StandardYoungTableau (adjoinOnes lam (n - lam.card))) := by
  rw [(relativeDualLowestEquiv K n lam hk).finrank_eq, Subspace.dual_finrank_eq]
  let mu := adjoinOnes lam (n - lam.card)
  have hcard : mu.card = n := by simp only [mu, adjoinOnes_card, Nat.add_sub_of_le hk]
  have hdimAt (N : ℕ) (hN : mu.card = N) :
      Module.finrank K (quotientHomogeneousPiece (untruncatedIdeal K N mu)
        (springerTopDegree mu)) = Fintype.card (StandardYoungTableau mu) := by
    subst N
    exact finrank_springer_top_piece (K := K) mu
  exact hdimAt n hcard

end HigherSpecht
end
end CanonicalSource15

section CanonicalSource16
/- Source: HigherSpecht/GradedMinimalGenerators.lean -/



/-!
# Minimal generator number from the genuine lowest graded piece

For a connected nonnegative graded algebra, every finite generating
family projects to a spanning family of the lowest module piece.  This
proves the lower bound for all generating families, including
nonhomogeneous ones.  A basis of a generating lowest piece gives the
matching upper bound.  No numerical generator invariant is defined by
the conclusion.
-/

noncomputable section
open TauCeti Module DirectSum
open scoped Classical

namespace HigherSpecht

variable {K A M : Type*} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]

def gradingProjection (G : InternalGrading K M) (d : ℤ) : M →ₗ[K] G.piece d :=
  (DirectSum.component K ℤ (fun q => G.piece q) d).comp
    (DirectSum.decomposeLinearEquiv G.piece).toLinearMap

@[simp] theorem gradingProjection_apply (G : InternalGrading K M) (d : ℤ) (x : M) :
    gradingProjection G d x = DirectSum.decompose G.piece x d := rfl

@[simp] theorem gradingProjection_of_mem (G : InternalGrading K M) (d : ℤ)
    (x : G.piece d) : gradingProjection G d x = x := by
  apply Subtype.ext
  exact DirectSum.decompose_of_mem_same G.piece x.property

theorem lowestProjection_span_of_generators
    (GA : InternalGrading K A) (G : InternalGrading K M)
    [SetLike.GradedSMul GA.piece G.piece]
    (hneg : ∀ q < 0, GA.piece q = ⊥)
    (hzero : ∀ a ∈ GA.piece 0, ∃ c : K, algebraMap K A c = a)
    (d : ℤ) (hbelow : ∀ q < d, G.piece q = ⊥)
    {ι : Type*} (v : ι → M)
    (hgen : Submodule.span A (Set.range v) = ⊤) :
    Submodule.span K (Set.range fun i => gradingProjection G d (v i)) = ⊤ := by
  let U := Submodule.span K (Set.range fun i => gradingProjection G d (v i))
  have haction : ∀ a : A, ∀ x : M, gradingProjection G d x ∈ U →
      gradingProjection G d (a • x) ∈ U := by
    intro a x hx
    rw [← DirectSum.sum_support_decompose GA.piece a, Finset.sum_smul, map_sum]
    apply U.sum_mem
    intro q hq
    let aq : A := DirectSum.decompose GA.piece a q
    have haq : aq ∈ GA.piece q := (DirectSum.decompose GA.piece a q).property
    change gradingProjection G d (aq • x) ∈ U
    by_cases hqneg : q < 0
    · have haq0 : aq = 0 := by simpa only [hneg q hqneg, Submodule.mem_bot] using haq
      simp only [haq0, zero_smul, map_zero]
      exact U.zero_mem
    · by_cases hqzero : q = 0
      · obtain ⟨c, hc⟩ := hzero aq (hqzero ▸ haq)
        rw [← hc, IsScalarTower.algebraMap_smul (R := K) (A := A), map_smul]
        exact U.smul_mem c hx
      · have hqpos : 0 < q := by omega
        let f : M →ₗ[K] M := Algebra.lsmul K K M aq
        have hf : TauCeti.LinearMap.IsHomogeneous f G.piece G.piece q := by
          rw [TauCeti.LinearMap.isHomogeneous_def]
          intro r y hy
          simpa only [f, Algebra.lsmul_apply, vadd_eq_add, add_comm r q] using
            SetLike.GradedSMul.smul_mem haq hy
        have hpart : (DirectSum.decompose G.piece x (d - q) : M) = 0 := by
          have h := (DirectSum.decompose G.piece x (d - q)).property
          simpa only [hbelow (d - q) (by omega), Submodule.mem_bot] using h
        have hmap := hf.map_decompose (d - q) x
        rw [hpart, map_zero, sub_add_cancel] at hmap
        have hz : gradingProjection G d (aq • x) = 0 := by
          apply Subtype.ext
          exact hmap.symm
        rw [hz]
        exact U.zero_mem
  have hprojection : ∀ x : M, gradingProjection G d x ∈ U := by
    intro x
    have hx : x ∈ Submodule.span A (Set.range v) := hgen.symm ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simpa only [map_zero] using U.zero_mem
    | add x y hx hy ihx ihy => simpa only [map_add] using U.add_mem ihx ihy
    | smul a x hx ih => exact haction a x ih
  apply top_unique
  intro x hx
  simpa only [gradingProjection_of_mem] using hprojection x.val

theorem lowestPiece_finrank_le_generators
    (GA : InternalGrading K A) (G : InternalGrading K M)
    [SetLike.GradedSMul GA.piece G.piece]
    (hneg : ∀ q < 0, GA.piece q = ⊥)
    (hzero : ∀ a ∈ GA.piece 0, ∃ c : K, algebraMap K A c = a)
    (d : ℤ) (hbelow : ∀ q < d, G.piece q = ⊥)
    {ι : Type*} [Fintype ι] (v : ι → M)
    (hgen : Submodule.span A (Set.range v) = ⊤) :
    Module.finrank K (G.piece d) ≤ Fintype.card ι :=
  finrank_le_of_span_eq_top
    (lowestProjection_span_of_generators GA G hneg hzero d hbelow v hgen)

theorem exists_generators_of_generating_piece
    (G : InternalGrading K M) (d : ℤ) [Module.Finite K (G.piece d)]
    (hgen : G.IsGeneratedInDegree A d) :
    ∃ v : Fin (Module.finrank K (G.piece d)) → M,
      (∀ i, v i ∈ G.piece d) ∧ Submodule.span A (Set.range v) = ⊤ := by
  let b := Module.finBasis K (G.piece d)
  let v := fun i => (b i).val
  refine ⟨v, fun i => (b i).property, ?_⟩
  let U := Submodule.span A (Set.range v)
  have hpiece : (G.piece d : Set M) ⊆ U := by
    intro x hx
    let z : G.piece d := ⟨x, hx⟩
    have hsum := congrArg Subtype.val (b.sum_repr z)
    change z.val ∈ U
    rw [← hsum]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    apply U.sum_mem
    intro i hi
    exact (U.restrictScalars K).smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  apply top_unique
  change Submodule.span A (G.piece d : Set M) = ⊤ at hgen
  rw [← hgen]
  exact Submodule.span_le.mpr hpiece

end HigherSpecht
end
end CanonicalSource16

section CanonicalSource17
/- Source: HigherSpecht/CanonicalModuleGeneration.lean -/



/-!
# Corollary 7.6: the exact canonical generating degree and type

The module is the actual relative dual Hom_B(A,B), with its normalized
intrinsic grading.  It has a homogeneous generating family indexed by
the standard tableaux of the Springer special-fiber shape; every finite
generating family, homogeneous or otherwise, has at least that many
members.  This is the actual minimal number of generators, over every
coefficient field.  The separate dualizing-module theorem identifies
this relative dual as a canonical module.
-/

noncomputable section
open TauCeti Module MvPolynomial
open scoped Classical

namespace HigherSpecht

variable (K : Type*) [Field K]

theorem elementaryCanonicalShift_eq_choose (m : ℕ) :
    elementaryCanonicalShift m = ((m + 1).choose 2 : ℤ) := by
  have hsum : elementaryCanonicalShift m = ∑ j ∈ Finset.range m, (j + 1 : ℤ) := by
    exact Fin.sum_univ_eq_sum_range (fun j : ℕ => (j + 1 : ℤ)) m
  rw [hsum]
  clear hsum
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ' (m + 1) 1,
        Nat.choose_one_right]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

theorem untruncated_degree_zero_scalar
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (a : UntruncatedRing K n lam)
    (ha : a ∈ (untruncatedInternalGrading K n lam hk).piece 0) :
    ∃ c : K, algebraMap K (UntruncatedRing K n lam) c = a := by
  rw [untruncatedInternalGrading_piece, quotientIntegerPiece,
    if_pos (le_refl (0 : ℤ)), Int.toNat_zero] at ha
  obtain ⟨p, hp, rfl⟩ := ha
  refine ⟨p.coeff 0, ?_⟩
  change Ideal.Quotient.mk _ (MvPolynomial.C (p.coeff 0)) = Ideal.Quotient.mk _ p
  rw [← MvPolynomial.homogeneousComponent_zero,
    MvPolynomial.homogeneousComponent_eq_self hp]

/-- Exact source-level assertion of the generating degree in Corollary
7.6; normalization is the usual B(-sum j) normalization. -/
theorem corollary_7_6_canonical_generated_degree
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    (untruncatedRelativeDualGrading K n lam hk).IsGeneratedInDegree
      (UntruncatedRing K n lam)
      (((n - lam.card + 1).choose 2 : ℤ) -
        springerTopDegree (adjoinOnes lam (n - lam.card))) := by
  rw [← elementaryCanonicalShift_eq_choose]
  exact untruncatedRelativeDual_generated_in_degree K n lam hk

/-- An actual homogeneous generating family with precisely f^mu members. -/
theorem exists_canonical_minimal_generators
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    ∃ v : Fin (Fintype.card (StandardYoungTableau (adjoinOnes lam (n - lam.card)))) →
        UntruncatedRelativeDual K n lam,
      (∀ i, v i ∈ (untruncatedRelativeDualGrading K n lam hk).piece
        (relativeDualGeneratingDegree n lam)) ∧
      Submodule.span (UntruncatedRing K n lam) (Set.range v) = ⊤ := by
  letI : Module.Finite K ((untruncatedRelativeDualGrading K n lam hk).piece
      (relativeDualGeneratingDegree n lam)) :=
    relativeDualLowest_finite K n lam hk
  have h := exists_generators_of_generating_piece
    (A := UntruncatedRing K n lam) (untruncatedRelativeDualGrading K n lam hk)
    (relativeDualGeneratingDegree n lam)
    (untruncatedRelativeDual_generated_in_degree K n lam hk)
  have hdim := relativeDualLowest_finrank K n lam hk
  change Module.finrank K ((untruncatedRelativeDualGrading K n lam hk).piece
    (relativeDualGeneratingDegree n lam)) = _ at hdim
  exact Eq.mp (congrArg (fun r : ℕ =>
    ∃ v : Fin r → UntruncatedRelativeDual K n lam,
      (∀ i, v i ∈ (untruncatedRelativeDualGrading K n lam hk).piece
        (relativeDualGeneratingDegree n lam)) ∧
      Submodule.span (UntruncatedRing K n lam) (Set.range v) = ⊤) hdim) h

/-- The lower bound applies to every finite generating family, with no
homogeneity condition on the proposed generators. -/
theorem canonical_generators_card_lower_bound
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (r : ℕ) (v : Fin r → UntruncatedRelativeDual K n lam)
    (hgen : Submodule.span (UntruncatedRing K n lam) (Set.range v) = ⊤) :
    Fintype.card (StandardYoungTableau (adjoinOnes lam (n - lam.card))) ≤ r := by
  letI := relativeDualGradedSMul (K := K) n lam hk
  have h := lowestPiece_finrank_le_generators
    (untruncatedInternalGrading K n lam hk) (untruncatedRelativeDualGrading K n lam hk)
    (fun q hq => by
      rw [untruncatedInternalGrading_piece]
      exact quotientIntegerPiece_eq_bot_of_neg _ hq)
    (untruncated_degree_zero_scalar K n lam hk)
    (relativeDualGeneratingDegree n lam)
    (fun q hq => relativeDual_piece_eq_bot_below K n lam hk hq) v hgen
  have hdim := relativeDualLowest_finrank K n lam hk
  change Module.finrank K ((untruncatedRelativeDualGrading K n lam hk).piece
    (relativeDualGeneratingDegree n lam)) = _ at hdim
  simpa only [hdim, Fintype.card_fin] using h

/-- Level generation and the exact Cohen--Macaulay type, expressed by
actual generating families of the canonical module rather than a
numerical surrogate definition. -/
theorem corollary_7_6_canonical_degree_and_type
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    let d : ℤ := ((n - lam.card + 1).choose 2 : ℤ) -
      springerTopDegree (adjoinOnes lam (n - lam.card))
    let t := Fintype.card (StandardYoungTableau (adjoinOnes lam (n - lam.card)))
    (∃ v : Fin t → UntruncatedRelativeDual K n lam,
      (∀ i, v i ∈ (untruncatedRelativeDualGrading K n lam hk).piece d) ∧
      Submodule.span (UntruncatedRing K n lam) (Set.range v) = ⊤) ∧
    (∀ r (v : Fin r → UntruncatedRelativeDual K n lam),
      Submodule.span (UntruncatedRing K n lam) (Set.range v) = ⊤ → t ≤ r) := by
  constructor
  · simpa only [relativeDualGeneratingDegree, elementaryCanonicalShift_eq_choose] using
      exists_canonical_minimal_generators K n lam hk
  · exact canonical_generators_card_lower_bound K n lam hk

end HigherSpecht
end
end CanonicalSource17

section CanonicalSource18
/- Source: HigherSpecht/UntruncatedCanonicalModule.lean -/



/-!
# The actual canonical module in Corollary 7.6

The module Hom_B(A,B) has its multiplication action and normalized grading.
Its dualizing property is proved using actual Ext adjunction, not assumed.
The independent graded argument supplies its generating degree and the exact
minimum number of generators over every coefficient field.
-/

noncomputable section

open Module TauCeti

universe u

namespace HigherSpecht

variable (K : Type u) [Field K]

/-- The actual relative dual is a dualizing module for the untruncated
quotient, over every field and for every allowed partition. -/
theorem untruncatedRelativeDual_isDualizing
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    IsDualizingModule (UntruncatedRing K n lam) (UntruncatedRelativeDual K n lam) := by
  letI := untruncated_parameter_free_allCoefficients K n lam hk
  letI := untruncated_parameter_finite_allCoefficients K n lam hk
  apply relativeDual_isDualizing (ElementaryParameterRing K n lam)
    (UntruncatedRing K n lam) (d := n - lam.card)
  change ringKrullDim (MvPolynomial (Fin (n - lam.card)) K) ≤ _
  simp [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite]

/-- The canonical module has the manuscript's normalization and its exact
minimal number of homogeneous generators; the lower bound applies to
arbitrary finite generating families. -/
theorem corollary_7_6_canonical_module
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    let d : ℤ := ((n - lam.card + 1).choose 2 : ℤ) -
      springerTopDegree (adjoinOnes lam (n - lam.card))
    let t := Fintype.card (StandardYoungTableau (adjoinOnes lam (n - lam.card)))
    IsDualizingModule (UntruncatedRing K n lam) (UntruncatedRelativeDual K n lam) ∧
    (∃ v : Fin t → UntruncatedRelativeDual K n lam,
      (∀ i, v i ∈ (untruncatedRelativeDualGrading K n lam hk).piece d) ∧
      Submodule.span (UntruncatedRing K n lam) (Set.range v) = ⊤) ∧
    (∀ r (v : Fin r → UntruncatedRelativeDual K n lam),
      Submodule.span (UntruncatedRing K n lam) (Set.range v) = ⊤ → t ≤ r) := by
  exact ⟨untruncatedRelativeDual_isDualizing K n lam hk,
    corollary_7_6_canonical_degree_and_type K n lam hk⟩

/-- Type one supplies an actual cyclic canonical module, hence the
ordinary local finite-self-injective-dimension Gorenstein condition. -/
theorem untruncated_isGorenstein_of_one_standard_tableau
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (ht : Fintype.card (StandardYoungTableau (adjoinOnes lam (n - lam.card))) = 1) :
    IsGorensteinRing (UntruncatedRing K n lam) := by
  letI := untruncated_parameter_free_allCoefficients K n lam hk
  letI := untruncated_parameter_finite_allCoefficients K n lam hk
  obtain ⟨v, hv, hspan⟩ := exists_canonical_minimal_generators K n lam hk
  haveI : Subsingleton
      (Fin (Fintype.card (StandardYoungTableau (adjoinOnes lam (n - lam.card))))) := by
    rw [ht]
    infer_instance
  let i : Fin (Fintype.card (StandardYoungTableau (adjoinOnes lam (n - lam.card)))) :=
    ⟨0, by omega⟩
  have hrange : Set.range v = {v i} := by
    ext x
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, rfl⟩
      exact congrArg v (Subsingleton.elim j i)
    · intro hx
      exact ⟨i, hx.symm⟩
  apply relativeDual_cyclic_isGorenstein (ElementaryParameterRing K n lam)
    (A := UntruncatedRing K n lam) (d := n - lam.card)
  · change ringKrullDim (MvPolynomial (Fin (n - lam.card)) K) ≤ _
    simp [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite]
  · exact ⟨v i, hrange ▸ hspan⟩

end HigherSpecht
end
end CanonicalSource18

section CanonicalSource19
/- Source: HigherSpecht/FiniteLocalFiber.lean -/



/-!
# A finite algebra with a local nilpotent closed fiber

This is a localness criterion for an actual finite algebra.  The hypothesis
on powers is exactly nilpotence in its closed fiber; it is not a hypothesis
that the algebra, or its desired localization, is already local.
-/

noncomputable section

namespace HigherSpecht

variable {R A K : Type*} [CommRing R] [IsLocalRing R]
  [CommRing A] [Algebra R A] [Module.Finite R A] [Field K]

/-- Every maximal ideal of a finite algebra contains the extension of the
maximal ideal of the local base. -/
theorem closedFiberIdeal_le_maximal (P : Ideal A) [P.IsMaximal] :
    (IsLocalRing.maximalIdeal R).map (algebraMap R A) ≤ P := by
  apply Ideal.map_le_iff_le_comap.mpr
  rw [Ideal.comap_eq_maximalIdeal_of_isIntegral (R := R) P]

/-- A finite algebra whose closed fiber has a nilpotent augmentation
kernel has a unique maximal ideal, the actual augmentation kernel. -/
theorem finiteAlgebra_maximal_eq_augmentation
    (eps : A →+* K) (heps : Function.Surjective eps)
    (hnil : ∀ a : A, eps a = 0 →
      ∃ k : ℕ, a ^ k ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R A))
    (P : Ideal A) [P.IsMaximal] : P = RingHom.ker eps := by
  have hker : (RingHom.ker eps).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective eps heps
  apply (hker.eq_of_le (Ideal.IsMaximal.ne_top ‹P.IsMaximal›) ?_).symm
  intro a ha
  obtain ⟨k, hk⟩ := hnil a ha
  exact Ideal.IsPrime.mem_of_pow_mem (inferInstance : P.IsPrime) k
    (closedFiberIdeal_le_maximal (R := R) P hk)

theorem isLocalRing_of_finite_nilpotent_closedFiber
    (eps : A →+* K) (heps : Function.Surjective eps)
    (hnil : ∀ a : A, eps a = 0 →
      ∃ k : ℕ, a ^ k ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) :
    IsLocalRing A := by
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨RingHom.ker eps, RingHom.ker_isMaximal_of_surjective eps heps, ?_⟩
  intro P hP
  letI := hP
  exact finiteAlgebra_maximal_eq_augmentation eps heps hnil P

theorem maximalIdeal_eq_augmentation_of_finite_nilpotent_closedFiber
    [IsLocalRing A] (eps : A →+* K) (heps : Function.Surjective eps)
    (hnil : ∀ a : A, eps a = 0 →
      ∃ k : ℕ, a ^ k ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) :
    IsLocalRing.maximalIdeal A = RingHom.ker eps :=
  finiteAlgebra_maximal_eq_augmentation eps heps hnil _

/-- The resulting unit test is the literal residue-value test. -/
theorem isUnit_iff_augmentation_ne_zero_of_finite_nilpotent_closedFiber
    (eps : A →+* K) (heps : Function.Surjective eps)
    (hnil : ∀ a : A, eps a = 0 →
      ∃ k : ℕ, a ^ k ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R A))
    (a : A) : IsUnit a ↔ eps a ≠ 0 := by
  letI := isLocalRing_of_finite_nilpotent_closedFiber eps heps hnil
  rw [← not_iff_not]
  change a ∈ IsLocalRing.maximalIdeal A ↔ ¬ eps a ≠ 0
  rw [maximalIdeal_eq_augmentation_of_finite_nilpotent_closedFiber eps heps hnil]
  simp only [RingHom.mem_ker, not_not]

end HigherSpecht
end
end CanonicalSource19

section CanonicalSource20
/- Source: HigherSpecht/ParameterOriginLocalization.lean -/



/-!
# The origin of a finite parameter algebra

The local base change is constructed as a tensor product with the
localization of the parameter ring.  Its map to the actual closed fiber
is the localization lift of the original quotient map.  Nilpotence in
that fiber proves localness and identifies this tensor product with the
localization at the original augmentation ideal.
-/

noncomputable section

open scoped TensorProduct
open Module TensorProduct

namespace HigherSpecht

variable {K B A Q : Type*} [Field K] [CommRing B] [CommRing A] [CommRing Q]
  [Algebra K B] [Algebra K A] [Algebra B A] [IsScalarTower K B A] [Algebra K Q]

abbrev parameterOriginBase (eps : B →ₐ[K] K) :=
  Localization.AtPrime (RingHom.ker eps)

abbrev parameterOriginBaseChange (A : Type*) [CommRing A] [Algebra B A]
    (eps : B →ₐ[K] K) := parameterOriginBase eps ⊗[B] A

attribute [local instance] Algebra.TensorProduct.rightAlgebra

def parameterOriginResidue (eps : B →ₐ[K] K) : parameterOriginBase eps →+* K :=
  IsLocalization.lift (M := (RingHom.ker eps).primeCompl)
    (S := parameterOriginBase eps) (g := eps.toRingHom)
    (fun y => isUnit_iff_ne_zero.mpr y.property)

@[simp] theorem parameterOriginResidue_algebraMap (eps : B →ₐ[K] K) (b : B) :
    parameterOriginResidue eps (algebraMap B (parameterOriginBase eps) b) = eps b :=
  IsLocalization.lift_eq _ b

theorem parameterOriginResidue_surjective (eps : B →ₐ[K] K) :
    Function.Surjective (parameterOriginResidue eps) := by
  intro c
  refine ⟨algebraMap B (parameterOriginBase eps) (algebraMap K B c), ?_⟩
  simp only [parameterOriginResidue_algebraMap, eps.commutes,
    Algebra.algebraMap_self, RingHom.id_apply]

variable (eps : B →ₐ[K] K) (q : A →ₐ[K] Q)
  (hparam : ∀ b : B, q (algebraMap B A b) = algebraMap K Q (eps b))

include hparam in
theorem parameterOrigin_denominator_units
    (s : Algebra.algebraMapSubmonoid A (RingHom.ker eps).primeCompl) :
    IsUnit (q s.val) := by
  obtain ⟨b, hb, hbs⟩ := s.property
  rw [← hbs, hparam]
  exact (isUnit_iff_ne_zero.mpr hb).map (algebraMap K Q)

def parameterOriginFiberMap : parameterOriginBaseChange A eps →+* Q :=
  IsLocalization.lift (M := Algebra.algebraMapSubmonoid A (RingHom.ker eps).primeCompl)
    (S := parameterOriginBaseChange A eps) (g := q.toRingHom)
    (parameterOrigin_denominator_units eps q hparam)

@[simp] theorem parameterOriginFiberMap_algebraMap (a : A) :
    parameterOriginFiberMap eps q hparam
      (algebraMap A (parameterOriginBaseChange A eps) a) = q a :=
  IsLocalization.lift_eq _ a

theorem parameterOriginFiberMap_base (r : parameterOriginBase eps) :
    parameterOriginFiberMap eps q hparam
      (algebraMap (parameterOriginBase eps) (parameterOriginBaseChange A eps) r) =
      algebraMap K Q (parameterOriginResidue eps r) := by
  have he : (parameterOriginFiberMap eps q hparam).comp
      (algebraMap (parameterOriginBase eps) (parameterOriginBaseChange A eps)) =
      (algebraMap K Q).comp (parameterOriginResidue eps) := by
    apply IsLocalization.ringHom_ext (RingHom.ker eps).primeCompl
    ext b
    simp only [RingHom.comp_apply, parameterOriginResidue_algebraMap]
    rw [← IsScalarTower.algebraMap_apply B (parameterOriginBase eps)
      (parameterOriginBaseChange A eps),
      IsScalarTower.algebraMap_apply B A (parameterOriginBaseChange A eps),
      parameterOriginFiberMap_algebraMap, hparam]
  exact RingHom.congr_fun he r

theorem parameterOriginFiberMap_surjective (hq : Function.Surjective q) :
    Function.Surjective (parameterOriginFiberMap eps q hparam) := by
  intro z
  obtain ⟨a, rfl⟩ := hq z
  exact ⟨algebraMap A _ a, parameterOriginFiberMap_algebraMap eps q hparam a⟩

theorem parameterOrigin_parameterIdeal_map_le_closedFiber :
    ((RingHom.ker eps).map (algebraMap B A)).map
        (algebraMap A (parameterOriginBaseChange A eps)) ≤
      (IsLocalRing.maximalIdeal (parameterOriginBase eps)).map
        (algebraMap (parameterOriginBase eps) (parameterOriginBaseChange A eps)) := by
  rw [Ideal.map_map]
  apply Ideal.map_le_iff_le_comap.mpr
  intro b hb
  change algebraMap A (parameterOriginBaseChange A eps) (algebraMap B A b) ∈
    (IsLocalRing.maximalIdeal (parameterOriginBase eps)).map
      (algebraMap (parameterOriginBase eps) (parameterOriginBaseChange A eps))
  rw [← IsScalarTower.algebraMap_apply B A (parameterOriginBaseChange A eps),
    IsScalarTower.algebraMap_apply B (parameterOriginBase eps)
      (parameterOriginBaseChange A eps)]
  apply Ideal.mem_map_of_mem
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
    (parameterOriginBase eps) (RingHom.ker eps) b).mpr hb

/-- The kernel of the actual localized quotient lies in the extension of
the local base maximal ideal. -/
theorem parameterOriginFiberMap_ker_le_closedFiber
    (hker : RingHom.ker q ≤ (RingHom.ker eps).map (algebraMap B A)) :
    RingHom.ker (parameterOriginFiberMap eps q hparam) ≤
      (IsLocalRing.maximalIdeal (parameterOriginBase eps)).map
        (algebraMap (parameterOriginBase eps) (parameterOriginBaseChange A eps)) := by
  intro z hz
  change parameterOriginFiberMap eps q hparam z = 0 at hz
  let S := Algebra.algebraMapSubmonoid A (RingHom.ker eps).primeCompl
  let J := (IsLocalRing.maximalIdeal (parameterOriginBase eps)).map
    (algebraMap (parameterOriginBase eps) (parameterOriginBaseChange A eps))
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj S z
  have ha : q a = 0 := by
    have h := congrArg (parameterOriginFiberMap eps q hparam) hs
    simpa only [map_mul, hz, zero_mul,
      parameterOriginFiberMap_algebraMap] using h.symm
  have hma : algebraMap A (parameterOriginBaseChange A eps) a ∈ J :=
    parameterOrigin_parameterIdeal_map_le_closedFiber (A := A) eps
      (Ideal.mem_map_of_mem _ (hker ha))
  obtain ⟨u, hu⟩ := IsLocalization.map_units (parameterOriginBaseChange A eps) s
  have hz' : z = algebraMap A (parameterOriginBaseChange A eps) a * ↑u⁻¹ := by
    rw [← hs, ← hu, mul_assoc]
    simp
  rw [hz']
  exact J.mul_mem_right _ hma

variable (g : Q →ₐ[K] K)

def parameterOriginAugmentation : parameterOriginBaseChange A eps →+* K :=
  g.toRingHom.comp (parameterOriginFiberMap eps q hparam)

@[simp] theorem parameterOriginAugmentation_algebraMap (a : A) :
    parameterOriginAugmentation eps q hparam g
      (algebraMap A (parameterOriginBaseChange A eps) a) = g (q a) := by
  simp only [parameterOriginAugmentation, RingHom.comp_apply,
    parameterOriginFiberMap_algebraMap]
  rfl

theorem parameterOriginAugmentation_surjective (hq : Function.Surjective q) :
    Function.Surjective (parameterOriginAugmentation eps q hparam g) := by
  intro c
  obtain ⟨a, ha⟩ := hq (algebraMap K Q c)
  refine ⟨algebraMap A _ a, ?_⟩
  simp only [parameterOriginAugmentation_algebraMap, ha, g.commutes,
    Algebra.algebraMap_self, RingHom.id_apply]

theorem parameterOriginAugmentation_nilpotent_closedFiber
    (hker : RingHom.ker q ≤ (RingHom.ker eps).map (algebraMap B A))
    (hnil : ∀ x : Q, g x = 0 → IsNilpotent x)
    (z : parameterOriginBaseChange A eps)
    (hz : parameterOriginAugmentation eps q hparam g z = 0) :
    ∃ k : ℕ, z ^ k ∈
      (IsLocalRing.maximalIdeal (parameterOriginBase eps)).map
        (algebraMap (parameterOriginBase eps) (parameterOriginBaseChange A eps)) := by
  obtain ⟨k, hk⟩ := hnil (parameterOriginFiberMap eps q hparam z) hz
  refine ⟨k, parameterOriginFiberMap_ker_le_closedFiber eps q hparam hker ?_⟩
  change parameterOriginFiberMap eps q hparam (z ^ k) = 0
  rw [map_pow, hk]

include hparam in
theorem parameterOriginBaseChange_isLocalRing [Module.Finite B A]
    (hq : Function.Surjective q)
    (hker : RingHom.ker q ≤ (RingHom.ker eps).map (algebraMap B A))
    (hnil : ∀ x : Q, g x = 0 → IsNilpotent x) :
    IsLocalRing (parameterOriginBaseChange A eps) := by
  apply isLocalRing_of_finite_nilpotent_closedFiber
    (R := parameterOriginBase eps)
    (parameterOriginAugmentation eps q hparam g)
    (parameterOriginAugmentation_surjective eps q hparam g hq)
  exact parameterOriginAugmentation_nilpotent_closedFiber eps q hparam g hker hnil

include hparam in
/-- All, and only, the additional denominators at the actual homogeneous
origin have become units in the finite local base change. -/
theorem parameterOriginBaseChange_isLocalization [Module.Finite B A]
    (hq : Function.Surjective q)
    (hker : RingHom.ker q ≤ (RingHom.ker eps).map (algebraMap B A))
    (hnil : ∀ x : Q, g x = 0 → IsNilpotent x) :
    IsLocalization (RingHom.ker (g.comp q)).primeCompl
      (parameterOriginBaseChange A eps) := by
  apply isLocalization_of_enlarged_denominators
    (M := Algebra.algebraMapSubmonoid A (RingHom.ker eps).primeCompl)
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := ha
    change g (q (algebraMap B A b)) ≠ 0
    rw [hparam, g.commutes]
    exact hb
  · intro a
    apply (isUnit_iff_augmentation_ne_zero_of_finite_nilpotent_closedFiber
      (R := parameterOriginBase eps)
      (parameterOriginAugmentation eps q hparam g)
      (parameterOriginAugmentation_surjective eps q hparam g hq)
      (parameterOriginAugmentation_nilpotent_closedFiber eps q hparam g hker hnil)
      _).mpr
    rw [parameterOriginAugmentation_algebraMap]
    exact a.property

def parameterOriginLocalizationEquiv [Module.Finite B A]
    (hq : Function.Surjective q)
    (hker : RingHom.ker q ≤ (RingHom.ker eps).map (algebraMap B A))
    (hnil : ∀ x : Q, g x = 0 → IsNilpotent x) :
    Localization.AtPrime (RingHom.ker (g.comp q)) ≃ₐ[A]
      parameterOriginBaseChange A eps := by
  letI := parameterOriginBaseChange_isLocalization eps q hparam g hq hker hnil
  exact IsLocalization.algEquiv (RingHom.ker (g.comp q)).primeCompl _ _

end HigherSpecht
end
end CanonicalSource20

section CanonicalSource21
/- Source: HigherSpecht/FiniteParameterDuality.lean -/



/-!
# Duality on modules projective over the parameter ring

The dual is the genuine A-linear Hom into Hom_B(A,B). Evaluation at one
identifies it with the B-linear dual. Finite projective B-modules are
reflexive, and a short exact sequence with B-projective quotient remains
short exact after dualization. These facts will be used to compare finite
self-injective dimension with projective dimension of the canonical module.
-/

noncomputable section

open CategoryTheory Module

universe u

namespace HigherSpecht

variable (B A : Type u) [CommRing B] [CommRing A] [Algebra B A]

abbrev ParameterDual (M : Type u) [AddCommGroup M] [Module A M] :=
  M →ₗ[A] RelativeDual B A

variable {B A}

variable {M N P : Type u} [AddCommGroup M] [Module B M] [Module A M]
  [IsScalarTower B A M] [AddCommGroup N] [Module B N] [Module A N]
  [IsScalarTower B A N] [AddCommGroup P] [Module B P] [Module A P]
  [IsScalarTower B A P]

/-- The transpose is actual precomposition. -/
def parameterDualMap (f : M →ₗ[A] N) : ParameterDual B A N →ₗ[A] ParameterDual B A M where
  toFun g := g.comp f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem parameterDualMap_apply (f : M →ₗ[A] N)
    (g : ParameterDual B A N) (m : M) : parameterDualMap f g m = g (f m) := rfl

@[simp] theorem parameterDualMap_comp (f : M →ₗ[A] N) (g : N →ₗ[A] P) :
    parameterDualMap (B := B) (g.comp f) =
      (parameterDualMap (B := B) f).comp (parameterDualMap (B := B) g) := rfl

@[simp] theorem parameterDualMap_zero :
    parameterDualMap (B := B) (0 : M →ₗ[A] N) = 0 := by
  apply LinearMap.ext
  intro g
  apply LinearMap.ext
  intro m
  exact g.map_zero

@[simp] theorem parameterDualMap_id :
    parameterDualMap (B := B) (LinearMap.id : M →ₗ[A] M) = LinearMap.id := rfl

/-- Evaluation at one intertwines the transpose with the ordinary B-dual. -/
theorem parameterDualMap_toBaseDual (f : M →ₗ[A] N) (g : ParameterDual B A N) :
    relativeDualHomEquiv (B := B) (A := A) M (parameterDualMap f g) =
      (relativeDualHomEquiv (B := B) (A := A) N g).comp (f.restrictScalars B) := rfl

/-- Evaluation into the double parameter dual. -/
def parameterBidualEvaluation : M →ₗ[A] ParameterDual B A (ParameterDual B A M) where
  toFun m :=
    { toFun f := f m
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_add' m n := by
    apply LinearMap.ext
    intro f
    exact f.map_add m n
  map_smul' a m := by
    apply LinearMap.ext
    intro f
    exact f.map_smul a m

@[simp] theorem parameterBidualEvaluation_apply (m : M) (f : ParameterDual B A M) :
    parameterBidualEvaluation (B := B) (A := A) m f = f m := rfl

/-- Finite projective reflexivity for the actual parameter dual. -/
def parameterBidualEquiv [Module.Finite B M] [Module.Projective B M] :
    M ≃ₗ[A] ParameterDual B A (ParameterDual B A M) := by
  let e : M ≃ₗ[B] ParameterDual B A (ParameterDual B A M) :=
    ((Module.evalEquiv B M).trans
      (relativeDualHomEquiv (B := B) (A := A) M).dualMap).trans
        (relativeDualHomEquiv (B := B) (A := A) (ParameterDual B A M)).symm
  have he : (e : M → ParameterDual B A (ParameterDual B A M)) =
      parameterBidualEvaluation (B := B) (A := A) := by
    funext m
    ext f a
    change (a • f) m 1 = f m a
    rw [LinearMap.smul_apply, RelativeDual.smul_apply, one_mul]
  exact LinearEquiv.ofBijective (parameterBidualEvaluation (B := B) (A := A))
    (he ▸ e.bijective)

@[simp] theorem parameterBidualEquiv_apply [Module.Finite B M] [Module.Projective B M]
    (m : M) (f : ParameterDual B A M) :
    parameterBidualEquiv (B := B) (A := A) m f = f m := rfl

theorem parameterDual_finite [Module.Finite B M] [Module.Projective B M] :
    Module.Finite B (ParameterDual B A M) :=
  Module.Finite.equiv (relativeDualHomEquiv (B := B) (A := A) M).symm

theorem parameterDual_projective [Module.Finite B M] [Module.Projective B M] :
    Module.Projective B (ParameterDual B A M) :=
  Module.Projective.of_equiv (relativeDualHomEquiv (B := B) (A := A) M).symm

theorem parameterDualMap_injective (f : M →ₗ[A] N) (hf : Function.Surjective f) :
    Function.Injective (parameterDualMap (B := B) f) := by
  intro g h hgh
  apply LinearMap.ext
  intro n
  obtain ⟨m, rfl⟩ := hf n
  exact LinearMap.congr_fun hgh m

/-- Exactness in the middle follows by descending an actual functional
through the surjection, using its kernel. -/
theorem parameterDualMap_exact (f : M →ₗ[A] N) (g : N →ₗ[A] P)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (parameterDualMap (B := B) g) (parameterDualMap (B := B) f) := by
  intro l
  constructor
  · intro hl
    have hmem : relativeDualHomEquiv (B := B) (A := A) N l ∈
        (LinearMap.ker (g.restrictScalars B)).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro n hn
      obtain ⟨m, rfl⟩ := (hfg n).mp hn
      have hzero := LinearMap.congr_fun hl m
      exact congrArg (fun h : RelativeDual B A => h 1) hzero
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective
      (g.restrictScalars B) hg] at hmem
    obtain ⟨l', hl'⟩ := hmem
    refine ⟨(relativeDualHomEquiv (B := B) (A := A) P).symm l', ?_⟩
    apply (relativeDualHomEquiv (B := B) (A := A) N).injective
    rw [parameterDualMap_toBaseDual, LinearEquiv.apply_symm_apply]
    exact hl'
  · rintro ⟨l', rfl⟩
    apply LinearMap.ext
    intro m
    change l' (g (f m)) = 0
    rw [hfg.apply_apply_eq_zero, map_zero]

/-- Projectivity over B splits the original sequence over B. Extending a
functional along that splitting proves surjectivity of the transpose. -/
theorem parameterDualMap_surjective [Module.Projective B P]
    (f : M →ₗ[A] N) (g : N →ₗ[A] P)
    (hfg : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g) :
    Function.Surjective (parameterDualMap (B := B) f) := by
  let S : ShortComplex (ModuleCat.{u} B) :=
    ShortComplex.moduleCatMk (f.restrictScalars B) (g.restrictScalars B)
      (by ext m; exact hfg.apply_apply_eq_zero m)
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S hfg hf hg
  letI : CategoryTheory.Projective S.X₃ := by
    change CategoryTheory.Projective (ModuleCat.of B P)
    infer_instance
  let split := hS.splittingOfProjective
  intro l
  let l' : Module.Dual B N :=
    (relativeDualHomEquiv (B := B) (A := A) M l).comp split.r.hom
  refine ⟨(relativeDualHomEquiv (B := B) (A := A) N).symm l', ?_⟩
  apply (relativeDualHomEquiv (B := B) (A := A) M).injective
  rw [parameterDualMap_toBaseDual, LinearEquiv.apply_symm_apply]
  ext m
  change relativeDualHomEquiv (B := B) (A := A) M l (split.r (f m)) = _
  have hm : split.r (f m) = m := by
    exact congrArg (fun t => t m) split.f_r
  rw [hm]

/-- The reversed short complex is constructed from the actual transpose maps. -/
def parameterDualShortComplex (f : M →ₗ[A] N) (g : N →ₗ[A] P)
    (hfg : g.comp f = 0) : ShortComplex (ModuleCat.{u} A) :=
  ShortComplex.moduleCatMk (parameterDualMap (B := B) g) (parameterDualMap (B := B) f)
    (by rw [← parameterDualMap_comp, hfg, parameterDualMap_zero])

theorem parameterDualShortComplex_shortExact [Module.Projective B P]
    (f : M →ₗ[A] N) (g : N →ₗ[A] P)
    (hfg : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g) :
    (parameterDualShortComplex (B := B) f g hfg.linearMap_comp_eq_zero).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (parameterDualMap_exact f g hfg hg)
    (parameterDualMap_injective g hg) (parameterDualMap_surjective f g hfg hf hg)

end HigherSpecht
end
end CanonicalSource21

section CanonicalSource22
/- Source: HigherSpecht/ParameterExtBound.lean -/



/-!
# Ext on modules projective over the parameter ring

The relative bound tests actual Ext groups against every finite projective
module over the base ring. This is an intermediate property, not a replacement
for finite injective dimension: the latter implies it immediately. The dual
of a finite free algebra-module has vanishing positive relative Ext, and a
short exact sequence shifts the bound by one.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped Classical BigOperators

universe u

namespace HigherSpecht

variable (B A : Type u) [CommRing B] [CommRing A] [Algebra B A]

/-- Vanishing of actual Ext against every finite B-projective A-module. -/
def ParameterExtBound (N : Type u) [AddCommGroup N] [Module A N] (d : ℕ) : Prop :=
  letI := HasExt.standard (ModuleCat.{u} A)
  ∀ (C : Type u) [AddCommGroup C] [Module B C] [Module A C]
    [IsScalarTower B A C] [Module.Finite B C] [Module.Projective B C],
    ∀ i : ℕ, d < i → ∀ e : Ext (ModuleCat.of A C) (ModuleCat.of A N) i, e = 0

/-- An ordinary injective-dimension bound supplies every relative test. -/
theorem parameterExtBound_of_hasInjectiveDimensionLE
    (N : Type u) [AddCommGroup N] [Module A N] (d : ℕ)
    (h : HasInjectiveDimensionLE (ModuleCat.of A N) d) :
    ParameterExtBound B A N d := by
  letI := HasExt.standard (ModuleCat.{u} A)
  letI := h
  intro C _ _ _ _ _ _ i hi e
  exact e.eq_zero_of_hasInjectiveDimensionLT (d + 1) hi

/-- The concrete finite product bicone of modules. -/
abbrev moduleFinitePiBicone (ι : Type) [Fintype ι]
    (M : Type u) [AddCommGroup M] [Module A M] :
    Bicone (fun _ : ι => ModuleCat.of A M) where
  pt := ModuleCat.of A (ι → M)
  π i := ModuleCat.ofHom (LinearMap.proj i)
  ι i := ModuleCat.ofHom (LinearMap.single A (fun _ : ι => M) i)
  ι_π i j := by
    classical
    ext x
    by_cases h : i = j
    · subst j; simp
    · simp [h, Ne.symm h]

/-- The finite product is the actual biproduct, by the coordinate identity. -/
def moduleFinitePiBicone_isBilimit (ι : Type) [Fintype ι]
    (M : Type u) [AddCommGroup M] [Module A M] :
    (moduleFinitePiBicone A ι M).IsBilimit := by
  classical
  apply isBilimitOfTotal
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [moduleFinitePiBicone, ModuleCat.hom_sum, ModuleCat.hom_comp,
    ModuleCat.hom_ofHom, ModuleCat.hom_id, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.id_apply,
    LinearMap.single_apply]
  exact LinearMap.sum_single_apply (fun _ : ι => M) x

/-- Positive relative Ext into the true finite free dual vanishes. -/
theorem parameterExtBound_relativeDual [Module.Free B A]
    : ParameterExtBound B A (RelativeDual B A) 0 := by
  letI := HasExt.standard (ModuleCat.{u} A)
  letI := HasExt.standard (ModuleCat.{u} B)
  intro C _ _ _ _ _ _ i hi e
  letI : Module.Projective B
      ((ModuleCat.restrictScalars (algebraMap B A)).obj (ModuleCat.of A C)) :=
    Module.Projective.of_equiv (algebraRestrictionEquiv B A C).symm
  haveI : Projective
      ((ModuleCat.restrictScalars (algebraMap B A)).obj (ModuleCat.of A C)) :=
    inferInstance
  apply (relativeDualExtEquiv B A (ModuleCat.of A C) i).injective
  rw [map_zero]
  exact Ext.eq_zero_of_hasProjectiveDimensionLT _ 1 hi

/-- Vanishing survives actual finite products. -/
theorem parameterExtBound_pi {N : Type u} [AddCommGroup N] [Module A N]
    {d : ℕ} (h : ParameterExtBound B A N d) (ι : Type) [Fintype ι] :
    ParameterExtBound B A (ι → N) d := by
  letI := HasExt.standard (ModuleCat.{u} A)
  intro C _ _ _ _ _ _ i hi e
  apply (Ext.addEquivBiproduct (ModuleCat.of A C)
    (moduleFinitePiBicone_isBilimit A ι N) i).injective
  rw [map_zero]
  funext j
  exact h C i hi _

/-- Transport along an actual module equivalence. -/
theorem parameterExtBound_equiv {M N : Type u} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] {d : ℕ}
    (e : M ≃ₗ[A] N) (h : ParameterExtBound B A M d) : ParameterExtBound B A N d := by
  letI := HasExt.standard (ModuleCat.{u} A)
  intro C _ _ _ _ _ _ i hi x
  apply (TauCeti.extAddEquivOfIso (Iso.refl (ModuleCat.of A C)) e.symm.toModuleIso i).injective
  rw [map_zero]
  exact h C i hi _

/-- Duals of finite free A-modules are finite products of the actual
relative dual, so their positive relative Ext vanishes. -/
theorem parameterExtBound_dualFiniteFree [Module.Free B A] (r : ℕ) :
    ParameterExtBound B A (ParameterDual B A (Fin r → A)) 0 := by
  let e : ParameterDual B A (Fin r → A) ≃ₗ[A] (Fin r → RelativeDual B A) :=
    LinearEquiv.piRing A (RelativeDual B A) (Fin r) A
  exact parameterExtBound_equiv B A e.symm
    (parameterExtBound_pi B A (parameterExtBound_relativeDual B A) (Fin r))

/-- Exactness of the actual Ext sequence lowers a bound on the left term
when the middle term has zero positive relative Ext. -/
theorem parameterExtBound_cokernel
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) {d : ℕ}
    (hleft : ParameterExtBound B A S.X₁ (d + 1))
    (hmiddle : ParameterExtBound B A S.X₂ 0) : ParameterExtBound B A S.X₃ d := by
  letI := HasExt.standard (ModuleCat.{u} A)
  intro C _ _ _ _ _ _ i hi e
  obtain ⟨e', he'⟩ := Ext.covariant_sequence_exact₃ (ModuleCat.of A C) hS e
    (n₁ := i + 1) rfl (hleft C (i + 1) (by omega) _)
  rw [hmiddle C i (by omega) e', Ext.zero_comp] at he'
  exact he'.symm

end HigherSpecht
end
end CanonicalSource22

section CanonicalSource23
/- Source: HigherSpecht/FiniteDualProjectiveDimension.lean -/



/-!
# Finite injective dimension and the projective dimension of the dual

A finite B-projective A-module admits a finite A-free presentation whose
kernel is again finite B-projective. Its genuine B-dual sequence is exact.
Relative Ext dimension shifting then proves finite projective dimension of
the original module from a relative Ext bound on its dual. Applied to the
regular module's dual, this is the needed implication from finite
self-injective dimension; no duality equivalence is assumed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian Module

universe u

namespace HigherSpecht

variable (B A : Type u) [CommRing B] [CommRing A] [Algebra B A]

/-- The homothety equivalence is linear over A as well as over B. -/
def relativeDualHomothetyLinearEquiv [Module.Free B A] [Module.Finite B A] :
    A ≃ₗ[A] ParameterDual B A (RelativeDual B A) := by
  have h : (fun a : A => LinearMap.lsmul A (RelativeDual B A) a) =
      relativeDualHomothetyEquiv (B := B) (A := A) := by
    funext a
    apply LinearMap.ext
    intro f
    exact (relativeDualHomothetyEquiv_apply a f).symm
  refine LinearEquiv.ofBijective (LinearMap.lsmul A (RelativeDual B A)) ?_
  change Function.Bijective (fun a : A => LinearMap.lsmul A (RelativeDual B A) a)
  rw [h]
  exact (relativeDualHomothetyEquiv (B := B) (A := A)).bijective

/-- A splitting of the transpose gives a splitting of the original map
by actual finite-projective bidual evaluation. -/
theorem exists_section_of_dual_retraction
    {M P : Type u} [AddCommGroup M] [Module B M] [Module A M]
    [IsScalarTower B A M] [Module.Finite B M] [Module.Projective B M]
    [AddCommGroup P] [Module B P] [Module A P] [IsScalarTower B A P]
    [Module.Finite B P] [Module.Projective B P]
    (f : P →ₗ[A] M)
    (r : ParameterDual B A P →ₗ[A] ParameterDual B A M)
    (hr : r.comp (parameterDualMap (B := B) f) = LinearMap.id) :
    ∃ s : M →ₗ[A] P, f.comp s = LinearMap.id := by
  let eM := parameterBidualEquiv (B := B) (A := A) (M := M)
  let eP := parameterBidualEquiv (B := B) (A := A) (M := P)
  let s : M →ₗ[A] P :=
    eP.symm.toLinearMap.comp ((parameterDualMap (B := B) r).comp eM.toLinearMap)
  refine ⟨s, ?_⟩
  ext m
  apply eM.injective
  apply LinearMap.ext
  intro l
  have hs : eP (s m) = parameterDualMap (B := B) r (eM m) :=
    eP.apply_symm_apply _
  have hl := LinearMap.congr_fun hs (parameterDualMap (B := B) f l)
  have hrl := LinearMap.congr_fun hr l
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hrl
  change l (f (s m)) = l m
  simpa only [eP, eM, parameterBidualEquiv_apply, parameterDualMap_apply,
    LinearMap.comp_apply, LinearMap.id_apply, hrl] using hl

/-- The kernel of a surjection onto a B-projective module is B-projective.
The splitting is the actual B-linear splitting of its kernel sequence. -/
theorem kernel_projective_over_base
    {M P : Type u} [AddCommGroup M] [Module B M] [Module A M]
    [IsScalarTower B A M] [Module.Projective B M]
    [AddCommGroup P] [Module B P] [Module A P] [IsScalarTower B A P]
    [Module.Projective B P]
    (f : P →ₗ[A] M) (hf : Function.Surjective f) :
    Module.Projective B (LinearMap.ker f) := by
  let S : ShortComplex (ModuleCat.{u} B) :=
    ShortComplex.moduleCatMk ((LinearMap.ker f).subtype.restrictScalars B)
      (f.restrictScalars B) (by ext x; exact x.property)
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
    (LinearMap.exact_subtype_ker_map f) Subtype.val_injective hf
  haveI : Projective S.X₃ :=
    show Projective (ModuleCat.of B M) from inferInstance
  let split := hS.splittingOfProjective
  exact Module.Projective.of_split ((LinearMap.ker f).subtype.restrictScalars B)
    split.r.hom (ModuleCat.hom_ext_iff.mp split.f_r)

/-- The actual dual exact sequence transfers a finite relative Ext bound
to an ordinary projective-dimension bound. -/
theorem hasProjectiveDimensionLE_of_parameterDual_bound
    [IsNoetherianRing B] [Module.Free B A] [Module.Finite B A]
    (d : ℕ) (M : Type u) [AddCommGroup M] [Module B M] [Module A M]
    [IsScalarTower B A M] [Module.Finite B M] [Module.Projective B M]
    (h : ParameterExtBound B A (ParameterDual B A M) d) :
    HasProjectiveDimensionLE (ModuleCat.of A M) d := by
  induction d generalizing M with
  | zero =>
      letI := HasExt.standard (ModuleCat.{u} A)
      letI : Module.Finite A M := Module.Finite.of_restrictScalars_finite B A M
      obtain ⟨r, f, hf⟩ := Module.Finite.exists_fin' A M
      let K := LinearMap.ker f
      letI : Module.Projective B K := kernel_projective_over_base B A f hf
      letI : Module.Finite B K :=
        Module.Finite.of_injective ((LinearMap.ker f).subtype.restrictScalars B)
          Subtype.val_injective
      letI : Module.Finite B (ParameterDual B A K) := parameterDual_finite
      letI : Module.Projective B (ParameterDual B A K) := parameterDual_projective
      let S := parameterDualShortComplex (B := B) (LinearMap.ker f).subtype f
        (by ext x; exact x.property)
      have hS : S.ShortExact := parameterDualShortComplex_shortExact
        (LinearMap.ker f).subtype f (LinearMap.exact_subtype_ker_map f)
          Subtype.val_injective hf
      obtain ⟨r', hr'⟩ := hS.exists_f_comp_eq_of_ext_eq_zero
        (h (ParameterDual B A K) 1 (by decide)) (𝟙 S.X₁)
      have hr : r'.hom.comp (parameterDualMap (B := B) f) = LinearMap.id := by
        exact ModuleCat.hom_ext_iff.mp hr'
      obtain ⟨s, hs⟩ := exists_section_of_dual_retraction B A f r'.hom hr
      letI : Module.Projective A M := Module.Projective.of_split s f hs
      exact inferInstance
  | succ d ih =>
      letI : Module.Finite A M := Module.Finite.of_restrictScalars_finite B A M
      obtain ⟨r, f, hf⟩ := Module.Finite.exists_fin' A M
      let K := LinearMap.ker f
      letI : Module.Projective B K := kernel_projective_over_base B A f hf
      letI : Module.Finite B K :=
        Module.Finite.of_injective ((LinearMap.ker f).subtype.restrictScalars B)
          Subtype.val_injective
      let T := parameterDualShortComplex (B := B) (LinearMap.ker f).subtype f
        (by ext x; exact x.property)
      have hT : T.ShortExact := parameterDualShortComplex_shortExact
        (LinearMap.ker f).subtype f (LinearMap.exact_subtype_ker_map f)
          Subtype.val_injective hf
      have hK : ParameterExtBound B A (ParameterDual B A K) d :=
        parameterExtBound_cokernel B A hT h (parameterExtBound_dualFiniteFree B A r)
      have hpdK := ih K hK
      let S : ShortComplex (ModuleCat.{u} A) :=
        ShortComplex.moduleCatMk (LinearMap.ker f).subtype f
          (by ext x; exact x.property)
      have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
        (LinearMap.exact_subtype_ker_map f) Subtype.val_injective hf
      haveI : Projective S.X₂ :=
        show Projective (ModuleCat.of A (Fin r → A)) from inferInstance
      exact hS.hasProjectiveDimensionLT_X₃ (d + 1) hpdK
        (hasProjectiveDimensionLT_of_ge S.X₂ 1 (d + 1 + 1) (by omega))

/-- Finite self-injective dimension of the algebra implies finite
projective dimension of its actual finite-free relative dual. -/
theorem relativeDual_hasProjectiveDimensionLE_of_selfInjectiveDimension
    [IsNoetherianRing B] [Module.Free B A] [Module.Finite B A]
    (d : ℕ) (h : HasInjectiveDimensionLE (ModuleCat.of A A) d) :
    HasProjectiveDimensionLE (ModuleCat.of A (RelativeDual B A)) d := by
  letI : Module.Free B (RelativeDual B A) :=
    Module.Free.of_equiv (RelativeDual.linearEquiv B A).symm
  letI : Module.Finite B (RelativeDual B A) :=
    Module.Finite.equiv (RelativeDual.linearEquiv B A).symm
  apply hasProjectiveDimensionLE_of_parameterDual_bound B A d (RelativeDual B A)
  exact parameterExtBound_equiv B A (relativeDualHomothetyLinearEquiv B A)
    (parameterExtBound_of_hasInjectiveDimensionLE B A A d h)

end HigherSpecht
end
end CanonicalSource23

section CanonicalSource24
/- Source: HigherSpecht/FreeHomothetyRankOne.lean -/



/-!
# Free modules with only scalar endomorphisms

The conclusion is an actual cyclic generator. It follows directly from
coordinate projections on a basis: a projection onto one basis vector
cannot be a scalar if another basis vector exists. This avoids relying
on a numerical rank equation or on a Gorenstein characterization.
-/

noncomputable section

open Module
open scoped Classical

universe u

namespace HigherSpecht

variable {A : Type u} [CommRing A] [Nontrivial A]

/-- A nonzero free module whose every endomorphism is scalar has an
actual single generator. No domain or field hypothesis is needed. -/
theorem cyclic_of_free_of_surjective_homothety
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Free A M] [Nontrivial M]
    (h : Function.Surjective (fun a : A => LinearMap.lsmul A M a)) :
    ∃ m : M, Submodule.span A {m} = ⊤ := by
  let b := Module.Free.chooseBasis A M
  obtain ⟨i⟩ := b.index_nonempty
  let p : Module.End A M := b.constr A (fun j => if j = i then b j else 0)
  obtain ⟨a, ha⟩ := h p
  have ha1 : a = 1 := by
    have ht := congrArg (fun f : Module.End A M => b.repr (f (b i)) i) ha
    simpa [p, Basis.constr_basis] using ht
  have hindex (j : Module.Free.ChooseBasisIndex A M) : j = i := by
    by_contra hji
    have ht := congrArg (fun f : Module.End A M => b.repr (f (b j)) j) ha
    have ha0 : a = 0 := by simpa [p, hji, Basis.constr_basis] using ht
    exact one_ne_zero (ha1.symm.trans ha0)
  have hrange : Set.range b = {b i} := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact congrArg b (hindex j)
    · intro hx
      exact ⟨i, hx.symm⟩
  exact ⟨b i, hrange ▸ b.span_eq⟩

/-- The actual relative dual is nonzero because its faithful homotheties
include the distinct actions of zero and one. -/
theorem relativeDual_nontrivial (B : Type u) [CommRing B] [Algebra B A]
    [Module.Free B A] [Module.Finite B A] : Nontrivial (RelativeDual B A) := by
  by_contra h
  haveI : Subsingleton (RelativeDual B A) := not_nontrivial_iff_subsingleton.mp h
  have hh : relativeDualHomothetyLinearEquiv B A (0 : A) =
      relativeDualHomothetyLinearEquiv B A (1 : A) := by
    exact Subsingleton.elim _ _
  exact zero_ne_one ((relativeDualHomothetyLinearEquiv B A).injective hh)

/-- Once the genuine relative dual is free over A, its faithful full
endomorphism ring forces it to be free of rank one, with an actual generator. -/
theorem relativeDual_cyclic_of_free (B : Type u) [CommRing B] [Algebra B A]
    [Module.Free B A] [Module.Finite B A] [Module.Free A (RelativeDual B A)] :
    ∃ f : RelativeDual B A, Submodule.span A {f} = ⊤ := by
  letI := relativeDual_nontrivial (A := A) B
  apply cyclic_of_free_of_surjective_homothety (RelativeDual B A)
  change Function.Surjective (relativeDualHomothetyLinearEquiv B A)
  exact (relativeDualHomothetyLinearEquiv B A).surjective

end HigherSpecht
end
end CanonicalSource24

section CanonicalSource25
/- Source: HigherSpecht/FiniteLocalDualDepth.lean -/



/-!
# Depth and freeness of the actual relative dual at a local finite algebra

The flat local depth formula bounds the depth below by the depth of the
regular local base.  Finite integrality bounds the dimension above by the
same number.  Thus every nonzero module flat over that base has full depth.
The genuine Auslander--Buchsbaum formula then turns a finite projective
dimension of the relative dual into freeness over the local algebra.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian IsLocalRing Module

universe u

namespace HigherSpecht

variable {R A : Type u} [CommRing R] [CommRing A]
  [Algebra R A] [IsLocalRing R] [IsLocalRing A] [Module.Finite R A]

theorem finiteLocalAlgebra_isLocalHom : IsLocalHom (algebraMap R A) := by
  refine ⟨fun r hr => ?_⟩
  by_contra hru
  have hrm : r ∈ IsLocalRing.maximalIdeal R := hru
  have hi : algebraMap R A r ∈ IsLocalRing.maximalIdeal A := by
    change r ∈ (IsLocalRing.maximalIdeal A).comap (algebraMap R A)
    rw [Ideal.comap_eq_maximalIdeal_of_isIntegral (R := R)]
    exact hrm
  exact hi hr

/-- Full depth of a nonzero finite module flat over the regular local
base.  The equality concerns the actual Ext-defined depth. -/
theorem depth_eq_regularBase_of_finite_flat
    [IsRegularLocalRing R]
    (N : Type u) [AddCommGroup N] [Module R N] [Module A N]
    [IsScalarTower R A N] [Module.Finite A N] [Module.Flat R N]
    [Nontrivial N] :
    depth (ModuleCat.of A N) = depth (ModuleCat.of R R) := by
  letI : IsNoetherianRing A := IsNoetherianRing.of_finite R A
  letI : IsLocalHom (algebraMap R A) := finiteLocalAlgebra_isLocalHom
  have hlo : depth (ModuleCat.of R R) ≤ depth (ModuleCat.of A N) := by
    have h := depth_tensorProduct_eq_add_of_flat
      (R := R) (S := A) (N := N) (M := R)
    rw [depth_eq_of_linearEquiv (TensorProduct.AlgebraTensorModule.rid R A N)] at h
    rw [h]
    exact le_add_of_nonneg_right zero_le
  have hhi : (depth (ModuleCat.of A N) : WithBot ℕ∞) ≤
      (depth (ModuleCat.of R R) : WithBot ℕ∞) := by
    calc
      (depth (ModuleCat.of A N) : WithBot ℕ∞) ≤ Module.supportDim A N :=
        depth_le_supportDim
      _ ≤ ringKrullDim A := Module.supportDim_le_ringKrullDim A N
      _ ≤ ringKrullDim R := TauCeti.ringKrullDim_le_of_isIntegral
      _ = (depth (ModuleCat.of R R) : WithBot ℕ∞) :=
        TauCeti.IsRegularLocalRing.depth_eq_ringKrullDim.symm
  exact le_antisymm (WithBot.coe_le_coe.mp hhi) hlo

theorem depth_eq_self_of_finite_flat_regularBase
    [IsRegularLocalRing R] [Module.Flat R A]
    (N : Type u) [AddCommGroup N] [Module R N] [Module A N]
    [IsScalarTower R A N] [Module.Finite A N] [Module.Flat R N]
    [Nontrivial N] :
    depth (ModuleCat.of A N) = depth (ModuleCat.of A A) := by
  rw [depth_eq_regularBase_of_finite_flat (R := R) N,
    depth_eq_regularBase_of_finite_flat (R := R) A]

/-- A nonzero finite module of full depth and finite projective dimension
is free over the actual Noetherian local ring. -/
theorem free_of_finiteProjectiveDimension_of_depth_eq
    [IsNoetherianRing A]
    (N : Type u) [AddCommGroup N] [Module A N] [Module.Finite A N]
    [Nontrivial N] (d : ℕ)
    (hpd : HasProjectiveDimensionLE (ModuleCat.of A N) d)
    (hdepth : depth (ModuleCat.of A N) = depth (ModuleCat.of A A)) :
    Module.Free A N := by
  have hpdle := (projectiveDimension_le_iff (ModuleCat.of A N) d).mpr hpd
  have hpdtop : projectiveDimension (ModuleCat.of A N) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hpdle (by
      have hd : ((d : ℕ∞) : WithBot ℕ∞) < ((⊤ : ℕ∞) : WithBot ℕ∞) :=
        WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top d)
      simpa only [WithBot.coe_natCast, WithBot.coe_top] using hd))
  have hbot : projectiveDimension (ModuleCat.of A N) ≠ ⊥ := by
    rw [ne_eq, projectiveDimension_eq_bot_iff]
    exact fun h => not_subsingleton N (ModuleCat.subsingleton_of_isZero h)
  obtain ⟨p, hp⟩ := WithBot.ne_bot_iff_exists.mp hbot
  have hptop : p ≠ ⊤ := fun h => hpdtop (by simpa only [h, WithBot.coe_top] using hp.symm)
  obtain ⟨k, rfl⟩ := ENat.ne_top_iff_exists.mp hptop
  have hdepthtop : depth (ModuleCat.of A A) ≠ ⊤ :=
    fun h => not_subsingleton A ((depth_eq_top_iff _).mp h)
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp hdepthtop
  have hab := ModuleCat.projectiveDimension_add_depth_eq_depth
    (ModuleCat.of A N) hpdtop
  rw [hdepth, ← hp, ← he] at hab
  have hnat : k + e = e := by exact_mod_cast hab
  have hk : k = 0 := by omega
  have hpdzero : projectiveDimension (ModuleCat.of A N) = 0 := by
    simpa only [hk, ENat.natCast_zero, WithBot.coe_zero] using hp.symm
  letI : Projective (ModuleCat.of A N) :=
    ((projectiveDimension_eq_zero_iff _).mp hpdzero).1
  letI : Module.Projective A N :=
    (IsProjective.iff_projective N).mpr inferInstance
  exact Module.free_of_flat_of_isLocalRing

theorem relativeDual_nontrivial_of_finite_free
    [Module.Free R A] : Nontrivial (RelativeDual R A) := by
  exact relativeDual_nontrivial (A := A) R

/-- The local relative dual is free as soon as the actual local algebra
has finite self-injective dimension. -/
theorem relativeDual_free_of_local_selfInjectiveDimension
    [IsRegularLocalRing R] [Module.Free R A]
    (d : ℕ) (h : HasInjectiveDimensionLE (ModuleCat.of A A) d) :
    Module.Free A (RelativeDual R A) := by
  letI : IsNoetherianRing A := IsNoetherianRing.of_finite R A
  letI : Module.Free R (RelativeDual R A) :=
    Module.Free.of_equiv (RelativeDual.linearEquiv R A).symm
  letI : Module.Finite R (RelativeDual R A) :=
    Module.Finite.equiv (RelativeDual.linearEquiv R A).symm
  letI : Module.Finite A (RelativeDual R A) :=
    Module.Finite.of_restrictScalars_finite R A _
  letI : Nontrivial (RelativeDual R A) :=
    relativeDual_nontrivial_of_finite_free
  apply free_of_finiteProjectiveDimension_of_depth_eq (RelativeDual R A) d
    (relativeDual_hasProjectiveDimensionLE_of_selfInjectiveDimension R A d h)
  exact depth_eq_self_of_finite_flat_regularBase (R := R) (RelativeDual R A)

/-- This is an actual cyclic generator, obtained from freeness and
homothety, rather than a numerical definition of type one. -/
theorem relativeDual_cyclic_of_local_selfInjectiveDimension
    [IsRegularLocalRing R] [Module.Free R A]
    (d : ℕ) (h : HasInjectiveDimensionLE (ModuleCat.of A A) d) :
    ∃ f : RelativeDual R A, Submodule.span A {f} = ⊤ := by
  letI := relativeDual_free_of_local_selfInjectiveDimension (R := R) d h
  exact relativeDual_cyclic_of_free R

end HigherSpecht
end
end CanonicalSource25

section CanonicalSource26
/- Source: HigherSpecht/RingEquivInjectiveDimension.lean -/



/-! # Self-injective dimension under an actual ring equivalence -/

noncomputable section

open CategoryTheory

namespace HigherSpecht

universe u

variable {R S : Type u} [Ring R] [Ring S]

attribute [local instance] RingHomInvPair.of_ringEquiv

local instance ringEquivToRingHomInvPair (e : R ≃+* S) :
    RingHomInvPair e.toRingHom e.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv e

local instance ringEquivSymmToRingHomInvPair (e : R ≃+* S) :
    RingHomInvPair e.symm.toRingHom e.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm e

def ringEquivRegularModule (e : R ≃+* S) :
    ModuleCat.of R R ≃ₛₗ[e.toRingHom] ModuleCat.of S S where
  __ := e.toAddEquiv
  map_smul' r x := e.map_mul r x

theorem selfInjectiveDimensionLE_iff_of_ringEquiv (e : R ≃+* S) (d : ℕ) :
    HasInjectiveDimensionLE (ModuleCat.of R R) d ↔
      HasInjectiveDimensionLE (ModuleCat.of S S) d :=
  ModuleCat.hasInjectiveDimensionLE_iff_of_semiLinearEquiv e
    (ringEquivRegularModule e) d

end HigherSpecht
end
end CanonicalSource26

section CanonicalSource27
/- Source: HigherSpecht/UntruncatedOrigin.lean -/



/-!
# The actual homogeneous-origin localization of the untruncated ring

Both augmentation maps are evaluation at zero.  The special-fiber
kernel is identified using the genuine parameter basis, and its
nilpotence is the already established Springer nilpotence theorem.
These facts instantiate the finite local-fiber construction with no
localness, depth, or cyclicity premise on the quotient.
-/

noncomputable section

open TauCeti Module MvPolynomial
open scoped Classical TensorProduct

namespace HigherSpecht

variable (K : Type*) [Field K]

def untruncatedAugmentation (n : ℕ) (lam : YoungDiagram) :
    UntruncatedRing K n lam →ₐ[K] K :=
  Ideal.Quotient.liftₐ (untruncatedIdeal K n lam)
    (MvPolynomial.aeval fun _ : Fin n => (0 : K)) (by
      intro p hp
      have hz := untruncatedIdeal_le_constantCoeff_ker (R := K) n lam hp
      simpa only [RingHom.mem_ker, MvPolynomial.aeval_zero',
        Algebra.algebraMap_self, RingHom.id_apply] using hz)

@[simp] theorem untruncatedAugmentation_mk
    (n : ℕ) (lam : YoungDiagram) (p : PolynomialRing n K) :
    untruncatedAugmentation K n lam (Ideal.Quotient.mk (untruncatedIdeal K n lam) p) =
      p.constantCoeff := by
  change (MvPolynomial.aeval (fun _ : Fin n => (0 : K))) p = p.constantCoeff
  simp only [MvPolynomial.aeval_zero', Algebra.algebraMap_self, RingHom.id_apply]

def elementaryOriginAugmentation (n : ℕ) (lam : YoungDiagram) :
    ElementaryParameterRing K n lam →ₐ[K] K :=
  MvPolynomial.aeval fun _ : Fin (n - lam.card) => (0 : K)

@[simp] theorem elementaryOriginAugmentation_apply
    (n : ℕ) (lam : YoungDiagram) (p : ElementaryParameterRing K n lam) :
    elementaryOriginAugmentation K n lam p = p.constantCoeff := by
  simp only [elementaryOriginAugmentation, MvPolynomial.aeval_zero',
    Algebra.algebraMap_self, RingHom.id_apply]

abbrev untruncatedOrigin (n : ℕ) (lam : YoungDiagram) :
    Ideal (UntruncatedRing K n lam) := RingHom.ker (untruncatedAugmentation K n lam)

abbrev untruncatedOriginBase (n : ℕ) (lam : YoungDiagram) :=
  parameterOriginBase (elementaryOriginAugmentation K n lam)

abbrev untruncatedOriginAlgebra (n : ℕ) (lam : YoungDiagram) :=
  parameterOriginBaseChange (UntruncatedRing K n lam) (elementaryOriginAugmentation K n lam)

theorem untruncatedAugmentation_comp_specialFiber
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    (untruncatedAugmentation K n (adjoinOnes lam (n - lam.card))).comp
        (specialFiberQuotientMap K n lam hk) = untruncatedAugmentation K n lam := by
  ext x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [AlgHom.comp_apply, specialFiberQuotientMap_mk, untruncatedAugmentation_mk]

theorem specialFiberQuotientMap_ker_le_parameterIdeal
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    RingHom.ker (specialFiberQuotientMap K n lam hk) ≤
      (RingHom.ker (elementaryOriginAugmentation K n lam)).map
        (algebraMap (ElementaryParameterRing K n lam) (UntruncatedRing K n lam)) := by
  letI := finite_specialFiberMonomialIndex n lam hk
  letI : Fintype (SpecialFiberMonomialIndex n lam) := Fintype.ofFinite _
  intro x hx
  let b := untruncatedMonomialParameterBasis K n lam hk
  have hc (i : SpecialFiberMonomialIndex n lam) :
      elementaryOriginAugmentation K n lam (b.repr x i) = 0 := by
    have hi := congrArg (fun z => (specialFiberCoefficientBasis K n lam hk).repr z i)
      (show specialFiberQuotientMap K n lam hk x = 0 from hx)
    simpa only [elementaryOriginAugmentation_apply, b, specialFiberQuotientMap_repr,
      map_zero, Finsupp.zero_apply] using hi
  rw [← b.sum_repr x]
  apply Ideal.sum_mem
  intro i _
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hc i))

theorem untruncatedAugmentation_nilpotent_fullSize
    (n : ℕ) (mu : YoungDiagram) (hcard : mu.card = n)
    (x : UntruncatedRing K n mu) (hx : untruncatedAugmentation K n mu x = 0) :
    IsNilpotent x := by
  subst n
  exact springer_isNilpotent_of_augmentation_eq_zero mu hx

theorem untruncatedOriginAlgebra_isLocalRing
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    IsLocalRing (untruncatedOriginAlgebra K n lam) := by
  letI := untruncated_parameter_finite_allCoefficients K n lam hk
  apply parameterOriginBaseChange_isLocalRing
    (elementaryOriginAugmentation K n lam) (specialFiberQuotientMap K n lam hk)
    (fun p => by simpa only [elementaryOriginAugmentation_apply] using
      specialFiberQuotientMap_algebraMap K n lam hk p)
    (untruncatedAugmentation K n (adjoinOnes lam (n - lam.card)))
    (specialFiberQuotientMap_surjective K n lam hk)
    (specialFiberQuotientMap_ker_le_parameterIdeal K n lam hk)
  exact untruncatedAugmentation_nilpotent_fullSize K n _
    (by rw [adjoinOnes_card, Nat.add_sub_of_le hk])

attribute [local instance] Algebra.TensorProduct.rightAlgebra

def untruncatedOriginLocalizationEquiv
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Localization.AtPrime (untruncatedOrigin K n lam) ≃ₐ[UntruncatedRing K n lam]
      untruncatedOriginAlgebra K n lam := by
  letI := untruncated_parameter_finite_allCoefficients K n lam hk
  have e := parameterOriginLocalizationEquiv
      (elementaryOriginAugmentation K n lam) (specialFiberQuotientMap K n lam hk)
      (fun p => by simpa only [elementaryOriginAugmentation_apply] using
        specialFiberQuotientMap_algebraMap K n lam hk p)
      (untruncatedAugmentation K n (adjoinOnes lam (n - lam.card)))
      (specialFiberQuotientMap_surjective K n lam hk)
      (specialFiberQuotientMap_ker_le_parameterIdeal K n lam hk)
      (untruncatedAugmentation_nilpotent_fullSize K n _
        (by rw [adjoinOnes_card, Nat.add_sub_of_le hk]))
  exact Eq.mp
    (congrArg (fun eps : UntruncatedRing K n lam →ₐ[K] K =>
      Localization.AtPrime (RingHom.ker eps) ≃ₐ[UntruncatedRing K n lam]
        untruncatedOriginAlgebra K n lam)
      (untruncatedAugmentation_comp_specialFiber K n lam hk)) e

theorem untruncatedOriginAlgebra_free
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Module.Free (untruncatedOriginBase K n lam) (untruncatedOriginAlgebra K n lam) := by
  letI := untruncated_parameter_free_allCoefficients K n lam hk
  infer_instance

theorem untruncatedOriginAlgebra_finite
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Module.Finite (untruncatedOriginBase K n lam) (untruncatedOriginAlgebra K n lam) := by
  letI := untruncated_parameter_finite_allCoefficients K n lam hk
  infer_instance

/-- Gorensteinness supplies a genuine cyclic generator of the relative
dual at the homogeneous origin, by the actual local homological proof. -/
theorem untruncatedOrigin_relativeDual_cyclic_of_gorenstein
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hG : IsGorensteinRing (UntruncatedRing K n lam)) :
    ∃ f : RelativeDual (untruncatedOriginBase K n lam) (untruncatedOriginAlgebra K n lam),
      Submodule.span (untruncatedOriginAlgebra K n lam) {f} = ⊤ := by
  letI := untruncatedOriginAlgebra_isLocalRing K n lam hk
  letI := untruncatedOriginAlgebra_free K n lam hk
  letI := untruncatedOriginAlgebra_finite K n lam hk
  obtain ⟨d, hd⟩ := hG.2 ⟨untruncatedOrigin K n lam, inferInstance⟩
  have hC := (selfInjectiveDimensionLE_iff_of_ringEquiv
    (untruncatedOriginLocalizationEquiv K n lam hk).toRingEquiv d).mp hd
  exact relativeDual_cyclic_of_local_selfInjectiveDimension
    (R := untruncatedOriginBase K n lam) d hC

end HigherSpecht
end
end CanonicalSource27

section CanonicalSource28
/- Source: HigherSpecht/FiniteBasisDualSpecialization.lean -/



/-!
# Specialization of a finite free relative dual

The map below evaluates the coefficients of a functional in an actual
finite basis.  Its compatibility with multiplication follows from its
evaluation formula.  Thus an actual cyclic generator specializes to a
cyclic generator of the dual of the closed fiber.  Restriction to the
augmentation annihilator then bounds its genuine vector-space dimension.
-/

noncomputable section

open Module
open scoped Classical

namespace HigherSpecht

section Specialization

variable {R C K Q ι : Type*} [CommRing R] [CommRing C] [Algebra R C]
  [Field K] [CommRing Q] [Algebra K Q] [Fintype ι]
  (b : Basis ι R C) (c : Basis ι K Q) (rho : R →+* K) (q : C →+* Q)
  (hqScalar : ∀ r, q (algebraMap R C r) = algebraMap K Q (rho r))
  (hbc : ∀ i, q (b i) = c i)

def finiteBasisDualSpecialization (f : RelativeDual R C) : RelativeDual K Q :=
  c.constr K (fun i => rho (f (b i)))

@[simp] theorem finiteBasisDualSpecialization_basis (f : RelativeDual R C) (i : ι) :
    finiteBasisDualSpecialization b c rho f (c i) = rho (f (b i)) :=
  Basis.constr_basis _ _ _ _

include hqScalar hbc in
theorem finiteBasisDualSpecialization_eval (f : RelativeDual R C) (z : C) :
    finiteBasisDualSpecialization b c rho f (q z) = rho (f z) := by
  have hsmul (r : R) (x : C) : q (r • x) = rho r • q x := by
    rw [Algebra.smul_def, map_mul, hqScalar, Algebra.smul_def]
  rw [← b.sum_repr z]
  simp only [map_sum, hsmul, hbc, map_smul, finiteBasisDualSpecialization_basis,
    smul_eq_mul, map_mul]

include hqScalar hbc in
theorem finiteBasisDualSpecialization_smul
    (hq : Function.Surjective q) (a : C) (f : RelativeDual R C) :
    finiteBasisDualSpecialization b c rho (a • f) =
      q a • finiteBasisDualSpecialization b c rho f := by
  apply RelativeDual.ext
  intro z
  obtain ⟨x, rfl⟩ := hq z
  rw [finiteBasisDualSpecialization_eval b c rho q hqScalar hbc,
    RelativeDual.smul_apply, RelativeDual.smul_apply, ← map_mul,
    finiteBasisDualSpecialization_eval b c rho q hqScalar hbc]

theorem finiteBasisDualSpecialization_surjective (hrho : Function.Surjective rho) :
    Function.Surjective (finiteBasisDualSpecialization b c rho) := by
  intro g
  choose lift hlift using hrho
  let f : RelativeDual R C :=
    RelativeDual.ofLinearMap R C (b.constr R (fun i => lift (g (c i))))
  refine ⟨f, ?_⟩
  apply (RelativeDual.linearEquiv K Q).injective
  apply c.ext
  intro i
  change finiteBasisDualSpecialization b c rho f (c i) = g (c i)
  rw [finiteBasisDualSpecialization_basis]
  change rho ((b.constr R (fun i => lift (g (c i)))) (b i)) = g (c i)
  rw [Basis.constr_basis, hlift]

include hqScalar hbc in
/-- Cyclicity descends through the genuine finite-free dual specialization. -/
theorem relativeDual_cyclic_specializes
    (hrho : Function.Surjective rho) (hq : Function.Surjective q)
    (hcyc : ∃ f : RelativeDual R C, Submodule.span C {f} = ⊤) :
    ∃ g : RelativeDual K Q, Submodule.span Q {g} = ⊤ := by
  obtain ⟨f, hf⟩ := hcyc
  refine ⟨finiteBasisDualSpecialization b c rho f,
    (Submodule.span_singleton_eq_top_iff Q _).mpr ?_⟩
  intro g
  obtain ⟨f', hf'⟩ := finiteBasisDualSpecialization_surjective b c rho hrho g
  obtain ⟨a, ha⟩ := (Submodule.span_singleton_eq_top_iff C f).mp hf f'
  refine ⟨q a, ?_⟩
  rw [← finiteBasisDualSpecialization_smul b c rho q hqScalar hbc hq,
    show a • f = f' from ha, hf']

end Specialization

section Head

variable {K Q : Type*} [Field K] [CommRing Q] [Algebra K Q]

theorem augmentation_annihilator_mul
    (eps : Q →ₐ[K] K) (x : idealKilledSubspace (K := K) (RingHom.ker eps)) (a : Q) :
    a * x.val = eps a • x.val := by
  have h := x.property (a - algebraMap K Q (eps a)) (by
    change eps (a - algebraMap K Q (eps a)) = 0
    simp only [map_sub, eps.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self])
  rw [sub_mul, sub_eq_zero, ← Algebra.smul_def] at h
  exact h

/-- A cyclic dual has an augmentation-annihilator of dimension at most
one.  The annihilator is an actual subspace of the algebra. -/
theorem finrank_augmentation_annihilator_le_one_of_dual_cyclic
    [Module.Finite K Q]
    (eps : Q →ₐ[K] K)
    (hcyc : ∃ f : RelativeDual K Q, Submodule.span Q {f} = ⊤) :
    Module.finrank K (idealKilledSubspace (K := K) (RingHom.ker eps)) ≤ 1 := by
  let T := idealKilledSubspace (K := K) (RingHom.ker eps)
  obtain ⟨f, hf⟩ := hcyc
  let psi : Module.Dual K T := T.dualRestrict (RelativeDual.linearEquiv K Q f)
  have hspan : Submodule.span K {psi} = ⊤ := by
    apply (Submodule.span_singleton_eq_top_iff K psi).mpr
    intro g
    obtain ⟨g', hg'⟩ := Subspace.dualRestrict_surjective (W := T) g
    obtain ⟨a, ha⟩ := (Submodule.span_singleton_eq_top_iff Q f).mp hf
      ((RelativeDual.linearEquiv K Q).symm g')
    refine ⟨eps a, ?_⟩
    ext x
    have hx := congrArg (fun l : RelativeDual K Q => l x.val) ha
    rw [RelativeDual.smul_apply, mul_comm x.val a,
      augmentation_annihilator_mul eps x a, map_smul] at hx
    have hgx : g' x.val = g x := congrArg (fun l : Module.Dual K T => l x) hg'
    change eps a * f x.val = g x
    exact (show eps a * f x.val = g' x.val from hx).trans hgx
  have hdim : Module.finrank K (Module.Dual K T) ≤ 1 := by
    apply finrank_le_of_span_eq_top (v := fun _ : Fin 1 => psi)
    simpa only [Set.range_const, hspan]
  simpa only [Subspace.dual_finrank_eq] using hdim

end Head

end HigherSpecht
end
end CanonicalSource28

section CanonicalSource29
/- Source: HigherSpecht/OriginDualSpecialization.lean -/



/-!
# From the local canonical module to the actual Springer socle

The local relative dual specializes through the genuine parameter basis.
Its closed-fiber map is proved to be compatible with multiplication.
Consequently a local cyclic generator gives a cyclic dual of the actual
Springer fiber, whose socle has the independently proved tableau dimension.
This supplies the necessary type-one consequence of standard local
Gorensteinness, without assuming a Gorenstein--type characterization.
-/

noncomputable section

open TauCeti Module MvPolynomial
open scoped Classical TensorProduct

namespace HigherSpecht

variable (K : Type*) [Field K]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

def untruncatedOriginFiberMap
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    untruncatedOriginAlgebra K n lam →+*
      UntruncatedRing K n (adjoinOnes lam (n - lam.card)) :=
  parameterOriginFiberMap (elementaryOriginAugmentation K n lam)
    (specialFiberQuotientMap K n lam hk)
    (fun p => by simpa only [elementaryOriginAugmentation_apply] using
      specialFiberQuotientMap_algebraMap K n lam hk p)

@[simp] theorem untruncatedOriginFiberMap_algebraMap
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (x : UntruncatedRing K n lam) :
    untruncatedOriginFiberMap K n lam hk
      (algebraMap (UntruncatedRing K n lam) (untruncatedOriginAlgebra K n lam) x) =
      specialFiberQuotientMap K n lam hk x :=
  parameterOriginFiberMap_algebraMap _ _ _ x

theorem untruncatedOriginFiberMap_surjective
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Function.Surjective (untruncatedOriginFiberMap K n lam hk) :=
  parameterOriginFiberMap_surjective _ _ _
    (specialFiberQuotientMap_surjective K n lam hk)

theorem untruncatedOriginFiberMap_base
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (r : untruncatedOriginBase K n lam) :
    untruncatedOriginFiberMap K n lam hk
      (algebraMap (untruncatedOriginBase K n lam) (untruncatedOriginAlgebra K n lam) r) =
      algebraMap K _ (parameterOriginResidue (elementaryOriginAugmentation K n lam) r) :=
  parameterOriginFiberMap_base _ _ _ r

def untruncatedOriginBasis (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Basis (SpecialFiberMonomialIndex n lam) (untruncatedOriginBase K n lam)
      (untruncatedOriginAlgebra K n lam) :=
  (untruncatedMonomialParameterBasis K n lam hk).baseChange (untruncatedOriginBase K n lam)

@[simp] theorem untruncatedOriginFiberMap_basis
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (i : SpecialFiberMonomialIndex n lam) :
    untruncatedOriginFiberMap K n lam hk (untruncatedOriginBasis K n lam hk i) =
      specialFiberCoefficientBasis K n lam hk i := by
  rw [untruncatedOriginBasis, Basis.baseChange_apply]
  change untruncatedOriginFiberMap K n lam hk
    (algebraMap (UntruncatedRing K n lam) (untruncatedOriginAlgebra K n lam)
      (untruncatedMonomialParameterBasis K n lam hk i)) = _
  rw [untruncatedOriginFiberMap_algebraMap, specialFiberQuotientMap_basis]

theorem specialFiberRelativeDual_cyclic_of_origin_cyclic
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hcyc : ∃ f : RelativeDual (untruncatedOriginBase K n lam)
        (untruncatedOriginAlgebra K n lam),
      Submodule.span (untruncatedOriginAlgebra K n lam) {f} = ⊤) :
    ∃ g : RelativeDual K (UntruncatedRing K n (adjoinOnes lam (n - lam.card))),
      Submodule.span (UntruncatedRing K n (adjoinOnes lam (n - lam.card))) {g} = ⊤ := by
  letI := finite_specialFiberMonomialIndex n lam hk
  letI : Fintype (SpecialFiberMonomialIndex n lam) := Fintype.ofFinite _
  exact relativeDual_cyclic_specializes
    (untruncatedOriginBasis K n lam hk) (specialFiberCoefficientBasis K n lam hk)
    (parameterOriginResidue (elementaryOriginAugmentation K n lam))
    (untruncatedOriginFiberMap K n lam hk)
    (untruncatedOriginFiberMap_base K n lam hk)
    (untruncatedOriginFiberMap_basis K n lam hk)
    (parameterOriginResidue_surjective (elementaryOriginAugmentation K n lam))
    (untruncatedOriginFiberMap_surjective K n lam hk) hcyc

theorem untruncatedAugmentation_annihilator
    (n : ℕ) (lam : YoungDiagram) :
    idealKilledSubspace (K := K) (untruncatedOrigin K n lam) =
      (quotientVariableAnnihilator (untruncatedIdeal K n lam)).restrictScalars K := by
  ext z
  constructor
  · intro hz i
    exact hz (Ideal.Quotient.mk _ (MvPolynomial.X i)) (by
      simp only [RingHom.mem_ker, untruncatedAugmentation_mk, MvPolynomial.constantCoeff_X])
  · intro hz a ha
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    change untruncatedAugmentation K n lam (Ideal.Quotient.mk _ p) = 0 at ha
    rw [untruncatedAugmentation_mk] at ha
    rw [quotient_mul_eq_constant_smul_of_variables_annihilate _ hz p, ha, zero_smul]

theorem fullSize_augmentation_annihilator_finrank
    (n : ℕ) (mu : YoungDiagram) (hcard : mu.card = n) :
    Module.finrank K (idealKilledSubspace (K := K) (untruncatedOrigin K n mu)) =
      Fintype.card (StandardYoungTableau mu) := by
  subst n
  rw [untruncatedAugmentation_annihilator]
  have hs := springer_socle_finrank K mu
  rw [springerSocle, quotient_socle_restrictScalars_eq_variableAnnihilator
    (springerIdeal K mu)
    (fun i => ⟨mu.card, springer_coordinate_pow_card_eq_zero mu i⟩)] at hs
  exact hs

/-- The type-one consequence is deduced from actual localization,
Auslander--Buchsbaum, dual specialization, and the actual socle theorem. -/
theorem untruncated_gorenstein_standardTableau_card_eq_one
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hG : IsGorensteinRing (UntruncatedRing K n lam)) :
    Fintype.card (StandardYoungTableau (adjoinOnes lam (n - lam.card))) = 1 := by
  letI := finite_specialFiberMonomialIndex n lam hk
  letI : Fintype (SpecialFiberMonomialIndex n lam) := Fintype.ofFinite _
  letI : Module.Finite K (UntruncatedRing K n (adjoinOnes lam (n - lam.card))) :=
    Module.Finite.of_basis (specialFiberCoefficientBasis K n lam hk)
  have hcyc := specialFiberRelativeDual_cyclic_of_origin_cyclic K n lam hk
    (untruncatedOrigin_relativeDual_cyclic_of_gorenstein K n lam hk hG)
  have hd := finrank_augmentation_annihilator_le_one_of_dual_cyclic
    (untruncatedAugmentation K n (adjoinOnes lam (n - lam.card))) hcyc
  rw [fullSize_augmentation_annihilator_finrank K n _
    (by rw [adjoinOnes_card, Nat.add_sub_of_le hk])] at hd
  have hp : 0 < Fintype.card
      (StandardYoungTableau (adjoinOnes lam (n - lam.card))) := Fintype.card_pos
  omega

end HigherSpecht
end
end CanonicalSource29

section CanonicalSource30
/- Source: HigherSpecht/CompleteIntersectionCases.lean -/



/-!
# The actual complete-intersection presentations in Corollary 7.6

For a column of size `k`, the defining sequence is literally
`e_(n-k+1),...,e_n`.  For a full-size row it is literally `x_0,...,x_(n-1)`.
The empty partition is included: its displayed sequence is empty and its
ideal is zero.  The converse classification is a separate socle argument.
-/

noncomputable section

open TauCeti MvPolynomial Finset RingTheory.Sequence
open scoped Classical

namespace HigherSpecht

variable {R : Type*} [CommRing R] {n : ℕ} {lam : YoungDiagram}

def elementaryTailEmbedding (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Fin lam.card ↪ Fin n where
  toFun i := ⟨n - lam.card + i.val, by omega⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    have h := congrArg Fin.val hij
    change n - lam.card + i.val = n - lam.card + j.val at h
    omega

def elementaryTailSequence (R : Type*) [CommRing R] (n : ℕ) (lam : YoungDiagram) :
    List (PolynomialRing n R) :=
  List.ofFn (fun i : Fin lam.card => esymm (Fin n) R (n - lam.card + i.val + 1))

theorem conjugateTail_column_of_card_lt (hcolumn : lam.rowLen 0 ≤ 1)
    (hk : lam.card ≤ n) {t : ℕ} (ht : t < n) :
    conjugateTail n lam t = 0 := by
  rw [← columnTail_eq_conjugateTail lam hk]
  exact columnTail_eq_zero_of_width_le lam (by omega)

theorem conjugateTail_univ (hk : lam.card ≤ n) :
    conjugateTail n lam n = lam.card := by
  rw [← columnTail_eq_conjugateTail lam hk, Nat.sub_self, columnTail_zero]

theorem untruncatedIdeal_column_eq_elementaryTail
    (hk : lam.card ≤ n) (hcolumn : lam.rowLen 0 ≤ 1) :
    untruncatedIdeal R n lam = Ideal.ofList (elementaryTailSequence R n lam) := by
  rw [elementaryTailSequence, Ideal.ofList_ofFn]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro p ⟨Y, d, hd, hdY, hthreshold, rfl⟩
    have hYn : Y.card ≤ n := by simpa using Y.card_le_univ
    have hYeq : Y.card = n := by
      by_contra hne
      have hz := conjugateTail_column_of_card_lt hcolumn hk
        (Nat.lt_of_le_of_ne hYn hne)
      rw [hz, Nat.cast_zero, sub_zero] at hthreshold
      omega
    have hY : Y = Finset.univ := Y.eq_univ_of_card (by simpa using hYeq)
    subst Y
    simp only [card_univ, Fintype.card_fin, conjugateTail_univ hk] at hdY hthreshold
    have hsmall : n - lam.card < d := by omega
    let i : Fin lam.card := ⟨d - (n - lam.card) - 1, by omega⟩
    apply Ideal.subset_span
    refine ⟨i, ?_⟩
    have hdegree : n - lam.card + i.val + 1 = d := by
      dsimp only [i]
      omega
    change esymm (Fin n) R (n - lam.card + i.val + 1) =
      elementaryOn (Finset.univ : Finset (Fin n)) d
    rw [elementaryOn_univ, hdegree]
  · apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    apply elementaryOn_mem_untruncatedIdeal Finset.univ
      (Nat.zero_lt_succ _) (by simp only [card_univ, Fintype.card_fin]; omega)
    simp only [card_univ, Fintype.card_fin, conjugateTail_univ hk]
    have hi := i.isLt
    omega

theorem elementaryTailSequence_isRegular [IsDomain R]
    (hk : lam.card ≤ n) :
    IsRegular (PolynomialRing n R) (elementaryTailSequence R n lam) := by
  simpa only [elementaryTailSequence, elementaryTailEmbedding,
    Function.Embedding.coeFn_mk] using
    selectedElementary_isRegular R (elementaryTailEmbedding n lam hk)

/-- The complete-intersection direction for every column, including the
empty shape, in every characteristic. -/
theorem untruncated_regularSequencePresentation_of_column [IsDomain R]
    (hk : lam.card ≤ n) (hcolumn : lam.rowLen 0 ≤ 1) :
    IsRegularSequencePresentation (untruncatedIdeal R n lam) :=
  ⟨elementaryTailSequence R n lam, elementaryTailSequence_isRegular hk,
    (untruncatedIdeal_column_eq_elementaryTail hk hcolumn).symm⟩

theorem untruncatedIdeal_full_row_eq_variableIdeal
    (hcard : lam.card = n) (hrow : lam.colLen 0 ≤ 1) :
    untruncatedIdeal R n lam =
      Ideal.ofList (List.ofFn (MvPolynomial.X : Fin n → PolynomialRing n R)) := by
  rw [← blockSpringerIdeal_univ lam hcard.le,
    blockSpringerIdeal_eq_coordinate_of_one_row Finset.univ
      (by simpa only [card_univ, Fintype.card_fin] using hcard.symm) hrow,
    Ideal.ofList_ofFn]
  unfold coordinateIdeal
  congr 1
  ext p
  simp only [Finset.coe_univ, Set.image_univ, Set.mem_range]

theorem untruncated_regularSequencePresentation_of_full_row [IsDomain R]
    (hcard : lam.card = n) (hrow : lam.colLen 0 ≤ 1) :
    IsRegularSequencePresentation (untruncatedIdeal R n lam) := by
  refine ⟨List.ofFn (MvPolynomial.X : Fin n → PolynomialRing n R), ?_,
    (untruncatedIdeal_full_row_eq_variableIdeal hcard hrow).symm⟩
  exact selectedPolynomialVariables_isRegular R (Function.Embedding.refl (Fin n))

theorem corollary_7_6_completeIntersection_sufficiency [IsDomain R]
    (hk : lam.card ≤ n)
    (hshape : lam.rowLen 0 ≤ 1 ∨ lam.card = n ∧ lam.colLen 0 ≤ 1) :
    IsRegularSequencePresentation (untruncatedIdeal R n lam) := by
  rcases hshape with hcolumn | ⟨hcard, hrow⟩
  · exact untruncated_regularSequencePresentation_of_column hk hcolumn
  · exact untruncated_regularSequencePresentation_of_full_row hcard hrow

end HigherSpecht
end
end CanonicalSource30

section CanonicalSource31
/- Source: HigherSpecht/CoordinateKoszulZero.lean -/



/-! Zeroth coordinate Koszul homology is the literal augmentation field. -/

noncomputable section

open MvPolynomial Module Finset
open scoped Classical

namespace HigherSpecht

variable {K : Type*} [Field K] {n : ℕ}

def quotientConstantAugmentation (I : Ideal (PolynomialRing n K))
    (hI : I ≤ RingHom.ker constantCoeff) : PolynomialRing n K ⧸ I →ₐ[K] K :=
  Ideal.Quotient.liftₐ I (MvPolynomial.aeval fun _ : Fin n => (0 : K)) (by
    intro p hp
    simpa only [RingHom.mem_ker, MvPolynomial.aeval_zero', Algebra.algebraMap_self, RingHom.id_apply]
      using hI hp)

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem quotientConstantAugmentation_mk (I : Ideal (PolynomialRing n K))
    (hI : I ≤ RingHom.ker constantCoeff) (p : PolynomialRing n K) :
    quotientConstantAugmentation I hI (Ideal.Quotient.mk I p) = constantCoeff p := by
  change (MvPolynomial.aeval fun _ : Fin n => (0 : K)) p = constantCoeff p
  simp only [MvPolynomial.aeval_zero', Algebra.algebraMap_self, RingHom.id_apply]

def coordinateAugmentationCoefficient (I : Ideal (PolynomialRing n K))
    (hI : I ≤ RingHom.ker constantCoeff) : CoordinateKoszulCarrier I →ₗ[K] K :=
  (quotientConstantAugmentation I hI).toLinearMap.comp
    (((coordinateKoszulBasis I).coord ∅).restrictScalars K)

@[simp] theorem coordinateAugmentationCoefficient_smul
    (I : Ideal (PolynomialRing n K)) (hI : I ≤ RingHom.ker constantCoeff)
    (c : PolynomialRing n K ⧸ I) (z : CoordinateKoszulCarrier I) :
    coordinateAugmentationCoefficient I hI (c • z) =
      quotientConstantAugmentation I hI c * coordinateAugmentationCoefficient I hI z := by
  simp only [coordinateAugmentationCoefficient, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, Basis.coord_apply, map_smul,
    Finsupp.smul_apply, smul_eq_mul, AlgHom.toLinearMap_apply, map_mul]

@[simp] theorem coordinateAugmentationCoefficient_empty
    (I : Ideal (PolynomialRing n K)) (hI : I ≤ RingHom.ker constantCoeff) :
    coordinateAugmentationCoefficient I hI (coordinateKoszulBasis I ∅) = 1 := by
  simp only [coordinateAugmentationCoefficient, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, Basis.coord_apply, Basis.repr_self,
    Finsupp.single_eq_same, AlgHom.toLinearMap_apply, map_one]

theorem coordinateAugmentationCoefficient_differential
    (I : Ideal (PolynomialRing n K)) (hI : I ≤ RingHom.ker constantCoeff)
    (z : CoordinateKoszulCarrier I) :
    coordinateAugmentationCoefficient I hI (coordinateKoszulDifferential I z) = 0 := by
  rw [← (coordinateKoszulBasis I).sum_repr z]
  simp only [map_sum, coordinateKoszulDifferential_smul,
    coordinateAugmentationCoefficient_smul]
  apply Finset.sum_eq_zero
  intro s hs
  rw [coordinateKoszulDifferential_basis, map_sum]
  have hz : (∑ j : Fin n, coordinateAugmentationCoefficient I hI
      (if j ∈ s then Ideal.Quotient.mk I (X j) •
        (TauCeti.ExteriorAlgebra.basisEraseSign j s • coordinateKoszulBasis I (s.erase j))
      else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    split_ifs <;> simp only [coordinateAugmentationCoefficient_smul,
      quotientConstantAugmentation_mk, constantCoeff_X, zero_mul, map_zero]
  rw [hz, mul_zero]

@[simp] theorem coordinateKoszulDifferential_empty (I : Ideal (PolynomialRing n K)) :
    coordinateKoszulDifferential I (coordinateKoszulBasis I ∅) = 0 := by
  rw [coordinateKoszulDifferential_basis]
  simp only [Finset.notMem_empty, if_false, Finset.sum_const_zero]

set_option backward.isDefEq.respectTransparency false in
def constantCoordinateCycles (I : Ideal (PolynomialRing n K)) :
    K →ₗ[K] (coordinateDifferentialGrading I).cycles 0 :=
  (LinearMap.toSpanSingleton K (CoordinateKoszulCarrier I)
    (coordinateKoszulBasis I ∅)).codRestrict _ (fun c => by
      refine ⟨?_, ?_⟩
      · apply (coordinateHomologicalPiece I 0).smul_mem c
        have hgen := coordinateHomologicalPiece_generator I ∅
          (by simp : (↑(∅ : Finset (Fin n)).card : ℤ) = 0)
          (1 : PolynomialRing n K ⧸ I)
        have hunit : (1 : PolynomialRing n K ⧸ I) • coordinateKoszulBasis I ∅ =
            coordinateKoszulBasis I ∅ :=
          one_smul (PolynomialRing n K ⧸ I) (coordinateKoszulBasis I ∅)
        exact hunit ▸ hgen
      · change coordinateKoszulDifferential I (c • coordinateKoszulBasis I ∅) = 0
        rw [map_smul, coordinateKoszulDifferential_empty, smul_zero])

def constantCoordinateHomology (I : Ideal (PolynomialRing n K)) :
    K →ₗ[K] TotalCoordinateKoszulHomology I 0 :=
  ((coordinateDifferentialGrading I).homologyClass 0).comp (constantCoordinateCycles I)

set_option backward.isDefEq.respectTransparency false in
theorem constantCoordinateHomology_injective (I : Ideal (PolynomialRing n K))
    (hI : I ≤ RingHom.ker constantCoeff) : Function.Injective (constantCoordinateHomology I) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro c hc
  have hc' := ((coordinateDifferentialGrading I).homologyClass_eq_zero_iff 0
    (constantCoordinateCycles I c)).mp hc
  obtain ⟨y, hy, hdy⟩ := hc'
  have h := coordinateAugmentationCoefficient_differential I hI y
  change coordinateKoszulDifferential I y = (constantCoordinateCycles I c).val at hdy
  rw [hdy] at h
  change coordinateAugmentationCoefficient I hI
    (c • coordinateKoszulBasis I ∅) = 0 at h
  rw [map_smul, coordinateAugmentationCoefficient_empty, smul_eq_mul, mul_one] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
theorem constantCoordinateHomology_surjective (I : Ideal (PolynomialRing n K)) :
    Function.Surjective (constantCoordinateHomology I) := by
  intro z
  obtain ⟨z, rfl⟩ := (((coordinateDifferentialGrading I).boundaries 0).comap
    ((coordinateDifferentialGrading I).cycles 0).subtype).mkQ_surjective z
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective ((coordinateKoszulBasis I).repr z.val ∅)
  have hrep : z.val = Ideal.Quotient.mk I p • coordinateKoszulBasis I ∅ := by
    rw [hp]
    exact coordinateHomologicalPiece_zero_repr I z.property.1
  let f := p - MvPolynomial.C (constantCoeff p)
  have hf : constantCoeff f = 0 := by simp only [f, map_sub, constantCoeff_C, sub_self]
  obtain ⟨g, hg⟩ := constantCoeff_zero_eq_sum_variables hf
  let y := coordinateKoszulHomotopy I g (coordinateKoszulBasis I ∅)
  have hy : y ∈ coordinateHomologicalPiece I 1 := by
    have hb : coordinateKoszulBasis I ∅ ∈ coordinateHomologicalPiece I 0 := by
      have hgen := coordinateHomologicalPiece_generator I ∅
        (by simp : (↑(∅ : Finset (Fin n)).card : ℤ) = 0)
        (1 : PolynomialRing n K ⧸ I)
      have hunit : (1 : PolynomialRing n K ⧸ I) • coordinateKoszulBasis I ∅ =
          coordinateKoszulBasis I ∅ :=
        one_smul (PolynomialRing n K ⧸ I) (coordinateKoszulBasis I ∅)
      exact hunit ▸ hgen
    have hy' := coordinateHomologicalHomotopy_mem I g (i := 0)
      (z := coordinateKoszulBasis I ∅) hb
    simpa only [zero_add] using hy' 
  have hdy : coordinateKoszulDifferential I y =
      z.val - (constantCoeff p) • coordinateKoszulBasis I ∅ := by
    have h := coordinateKoszulHomotopy_identity I hg (coordinateKoszulBasis I ∅)
    rw [coordinateKoszulDifferential_empty, map_zero, add_zero,
      coordinateKoszulScalar_apply] at h
    rw [h, hrep]
    simp only [f, map_sub]
    rw [sub_smul (Ideal.Quotient.mk I p)
      (Ideal.Quotient.mk I (MvPolynomial.C (constantCoeff p)))
      (coordinateKoszulBasis I ∅)]
    have hc : Ideal.Quotient.mk I (MvPolynomial.C (constantCoeff p)) =
        algebraMap K (PolynomialRing n K ⧸ I) (constantCoeff p) :=
      (Ideal.Quotient.mkₐ K I).commutes (constantCoeff p)
    have hcsmul : Ideal.Quotient.mk I (MvPolynomial.C (constantCoeff p)) •
        coordinateKoszulBasis I ∅ = (constantCoeff p) • coordinateKoszulBasis I ∅ :=
      (congrArg (fun a : PolynomialRing n K ⧸ I => a • coordinateKoszulBasis I ∅) hc).trans
        (IsScalarTower.algebraMap_smul (PolynomialRing n K ⧸ I)
          (constantCoeff p) (coordinateKoszulBasis I ∅))
    exact congrArg
      (fun w : CoordinateKoszulCarrier I => Ideal.Quotient.mk I p • coordinateKoszulBasis I ∅ - w)
      hcsmul
  refine ⟨constantCoeff p, ?_⟩
  symm
  change (coordinateDifferentialGrading I).homologyClass 0 z =
    (coordinateDifferentialGrading I).homologyClass 0 (constantCoordinateCycles I (constantCoeff p))
  rw [← sub_eq_zero, ← map_sub,
    (coordinateDifferentialGrading I).homologyClass_eq_zero_iff]
  exact ⟨y, hy, hdy⟩

def totalCoordinateZeroHomologyEquiv (I : Ideal (PolynomialRing n K))
    (hI : I ≤ RingHom.ker constantCoeff) :
    K ≃ₗ[K] TotalCoordinateKoszulHomology I 0 :=
  LinearEquiv.ofBijective (constantCoordinateHomology I)
    ⟨constantCoordinateHomology_injective I hI, constantCoordinateHomology_surjective I⟩

end HigherSpecht
end
end CanonicalSource31

section CanonicalSource32
/- Source: HigherSpecht/RegularSequenceKoszulBetti.lean -/



/-!
# The actual coordinate Koszul homology of a regular quotient

Adjoining a regular polynomial with zero constant coefficient doubles
homology by the explicit null-homotopy splitting.  Induction gives the
binomial Betti numbers for every regular list, without a homogeneity
assumption.  Top exterior degree then implies that any such quotient
with nonzero coordinate annihilator has one-dimensional annihilator.
-/

noncomputable section

open Module MvPolynomial RingTheory.Sequence
open scoped Classical

namespace HigherSpecht

variable {K : Type*} [Field K] {n : ℕ}

theorem regularSequence_next_injective
    (xs : List (PolynomialRing n K))
    (hreg : IsWeaklyRegular (PolynomialRing n K) xs)
    (k : ℕ) (hk : k < xs.length) :
    Function.Injective (fun c : PolynomialRing n K ⧸ Ideal.ofList (xs.take k) =>
      Ideal.Quotient.mk (Ideal.ofList (xs.take k)) xs[k] * c) := by
  have h := hreg.regular_mod_prev k hk
  have htop : (Ideal.ofList (xs.take k) •
      (⊤ : Submodule (PolynomialRing n K) (PolynomialRing n K))) =
      Ideal.ofList (xs.take k) := by
    change Ideal.ofList (xs.take k) * ⊤ = _
    exact Ideal.mul_top _
  rw [htop] at h
  exact h

theorem coordinateKoszul_regular_prefix_betti
    (xs : List (PolynomialRing n K))
    (hreg : IsWeaklyRegular (PolynomialRing n K) xs)
    (hzero : ∀ f ∈ xs, constantCoeff f = 0)
    (k : ℕ) (hk : k ≤ xs.length) :
    (∀ i : ℤ, FiniteDimensional K
      (TotalCoordinateKoszulHomology (Ideal.ofList (xs.take k)) i)) ∧
      ∀ q : ℕ, Module.finrank K
        (TotalCoordinateKoszulHomology (Ideal.ofList (xs.take k)) (q : ℤ)) = k.choose q := by
  induction k with
  | zero =>
    let P (I : Ideal (PolynomialRing n K)) : Prop :=
      (∀ i : ℤ, FiniteDimensional K (TotalCoordinateKoszulHomology I i)) ∧
        ∀ q : ℕ, Module.finrank K (TotalCoordinateKoszulHomology I (q : ℤ)) =
          (0 : ℕ).choose q
    have hbot : P ⊥ := by
      have hf : ∀ i : ℤ, FiniteDimensional K
          (TotalCoordinateKoszulHomology (⊥ : Ideal (PolynomialRing n K)) i) := by
        intro i
        by_cases hi : i < 0
        · letI := totalCoordinateKoszulHomology_subsingleton_of_outside
            (⊥ : Ideal (PolynomialRing n K)) (Or.inl hi)
          infer_instance
        · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hi)
          cases q with
          | zero =>
            exact Module.Finite.equiv
              (totalCoordinateZeroHomologyEquiv (⊥ : Ideal (PolynomialRing n K)) bot_le)
          | succ q =>
            letI := totalCoordinateKoszulHomology_bot_succ_subsingleton (K := K) (n := n) q
            infer_instance
      refine ⟨hf, ?_⟩
      intro q
      cases q with
      | zero =>
        let Z (i : ℤ) : Prop := Module.finrank K
          (TotalCoordinateKoszulHomology (⊥ : Ideal (PolynomialRing n K)) i) = 1
        have hz : Z 0 :=
          (totalCoordinateZeroHomologyEquiv
            (⊥ : Ideal (PolynomialRing n K)) bot_le).finrank_eq.symm.trans
              (Module.finrank_self K)
        have hcast : ((0 : ℕ) : ℤ) = 0 := rfl
        have hz' : Z ((0 : ℕ) : ℤ) := (congrArg Z hcast).mpr hz
        simpa only [Nat.choose_zero_right] using hz' 
      | succ q =>
        letI := totalCoordinateKoszulHomology_bot_succ_subsingleton (K := K) (n := n) q
        rw [Module.finrank_zero_of_subsingleton, Nat.choose_eq_zero_of_lt (by omega)]
    have hI : Ideal.ofList (xs.take 0) = (⊥ : Ideal (PolynomialRing n K)) := by
      simp only [List.take_zero, Ideal.ofList_nil]
    exact (congrArg P hI).mpr hbot
  | succ k ih =>
    have hkl : k < xs.length := by omega
    obtain ⟨hfinite, hdim⟩ := ih (by omega)
    let I := Ideal.ofList (xs.take k)
    let f := xs[k]
    let Q := regularCoordinateHomologicalQuotient I f
      (hzero f (List.getElem_mem hkl)) (regularSequence_next_injective xs hreg k hkl)
    have hideal : Ideal.ofList (xs.take (k + 1)) = adjoinHomogeneousElement I f := by
      rw [List.take_succ_eq_append_getElem hkl, Ideal.ofList_append,
        Ideal.ofList_singleton]
      rfl
    let P (J : Ideal (PolynomialRing n K)) : Prop :=
      (∀ i : ℤ, FiniteDimensional K (TotalCoordinateKoszulHomology J i)) ∧
        ∀ q : ℕ, Module.finrank K (TotalCoordinateKoszulHomology J (q : ℤ)) =
          (k + 1).choose q
    change P (Ideal.ofList (xs.take (k + 1)))
    apply (congrArg P hideal).mpr
    have hf : ∀ i : ℤ, FiniteDimensional K
        (TotalCoordinateKoszulHomology (adjoinHomogeneousElement I f) i) := by
      intro i
      letI := hfinite i
      letI := hfinite (i - 1)
      exact Module.Finite.equiv (Q.homologyEquiv i)
    refine ⟨hf, ?_⟩
    intro q
    letI := hfinite (q : ℤ)
    letI := hfinite ((q : ℤ) - 1)
    rw [Q.finrank_homology (q : ℤ)]
    cases q with
    | zero =>
      letI := totalCoordinateKoszulHomology_subsingleton_of_outside I
        (Or.inl (by norm_num : (0 : ℤ) - 1 < 0))
      rw [hdim 0, Module.finrank_zero_of_subsingleton, add_zero,
        Nat.choose_zero_right, Nat.choose_zero_right]
    | succ q =>
      rw [show ((q + 1 : ℕ) : ℤ) - 1 = (q : ℤ) by omega,
        hdim (q + 1), hdim q, Nat.choose_succ_succ', Nat.add_comm]

theorem coordinateKoszul_regularSequence_betti
    (xs : List (PolynomialRing n K))
    (hreg : IsWeaklyRegular (PolynomialRing n K) xs)
    (hzero : ∀ f ∈ xs, constantCoeff f = 0) :
    (∀ i : ℤ, FiniteDimensional K
      (TotalCoordinateKoszulHomology (Ideal.ofList xs) i)) ∧
      ∀ q : ℕ, Module.finrank K
        (TotalCoordinateKoszulHomology (Ideal.ofList xs) (q : ℤ)) = xs.length.choose q := by
  let P (I : Ideal (PolynomialRing n K)) : Prop :=
    (∀ i : ℤ, FiniteDimensional K (TotalCoordinateKoszulHomology I i)) ∧
      ∀ q : ℕ, Module.finrank K (TotalCoordinateKoszulHomology I (q : ℤ)) =
        xs.length.choose q
  have h : P (Ideal.ofList (xs.take xs.length)) :=
    coordinateKoszul_regular_prefix_betti xs hreg hzero xs.length le_rfl
  have hI : Ideal.ofList (xs.take xs.length) = Ideal.ofList xs := by
    rw [List.take_length]
  exact (congrArg P hI).mp h

theorem regularSequence_length_le_number_variables
    (xs : List (PolynomialRing n K))
    (hreg : IsWeaklyRegular (PolynomialRing n K) xs)
    (hzero : ∀ f ∈ xs, constantCoeff f = 0) : xs.length ≤ n := by
  have hdim := (coordinateKoszul_regularSequence_betti xs hreg hzero).2 xs.length
  by_contra h
  letI := totalCoordinateKoszulHomology_subsingleton_of_outside (Ideal.ofList xs)
    (i := (xs.length : ℤ)) (Or.inr (by exact_mod_cast Nat.lt_of_not_ge h))
  rw [Module.finrank_zero_of_subsingleton, Nat.choose_self] at hdim
  exact (Nat.zero_ne_one hdim)

/-- An arbitrary regular defining sequence with a nonzero top Koszul
annihilator has exactly n members, and that actual annihilator has
dimension one.  No homogeneity, chosen basis, or socle-dimension premise
equal to the conclusion is introduced. -/
theorem regularSequence_variableAnnihilator_finrank_one
    (xs : List (PolynomialRing n K))
    (hreg : IsWeaklyRegular (PolynomialRing n K) xs)
    (hzero : ∀ f ∈ xs, constantCoeff f = 0)
    (hpos : 0 < Module.finrank K
      ((quotientVariableAnnihilator (Ideal.ofList xs)).restrictScalars K)) :
    xs.length = n ∧ Module.finrank K
      ((quotientVariableAnnihilator (Ideal.ofList xs)).restrictScalars K) = 1 := by
  obtain ⟨hfinite, hdim⟩ := coordinateKoszul_regularSequence_betti xs hreg hzero
  have htop : Module.finrank K
      ((quotientVariableAnnihilator (Ideal.ofList xs)).restrictScalars K) =
      xs.length.choose n := by
    rw [← (totalCoordinateTopHomologyEquiv (Ideal.ofList xs)).finrank_eq, hdim n]
  have hle := regularSequence_length_le_number_variables xs hreg hzero
  have hge : n ≤ xs.length := by
    by_contra h
    rw [htop, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge h)] at hpos
    exact (Nat.lt_irrefl 0) hpos
  have heq : xs.length = n := Nat.le_antisymm hle hge
  exact ⟨heq, by rw [htop, heq, Nat.choose_self]⟩

theorem regularSequencePresentation_variableAnnihilator_finrank_one
    (I : Ideal (PolynomialRing n K)) (hI : I ≤ RingHom.ker constantCoeff)
    (hci : IsRegularSequencePresentation I)
    (hpos : 0 < Module.finrank K ((quotientVariableAnnihilator I).restrictScalars K)) :
    Module.finrank K ((quotientVariableAnnihilator I).restrictScalars K) = 1 := by
  obtain ⟨xs, hreg, hxs⟩ := hci
  have hzero : ∀ f ∈ xs, constantCoeff f = 0 := by
    intro f hf
    exact hI (hxs ▸ Ideal.subset_span hf)
  rw [← hxs] at hpos ⊢
  exact (regularSequence_variableAnnihilator_finrank_one xs hreg.1 hzero hpos).2

end HigherSpecht
end
end CanonicalSource32

section CanonicalSource33
/- Source: HigherSpecht/CompleteIntersectionClassification.lean -/



/-!
# The complete-intersection classification in Corollary 7.6

The reverse implication starts with an arbitrary actual regular defining
sequence.  The actual regular elementary parameters are appended, giving
the Springer special fiber.  Its coordinate Koszul top homology has
dimension one by the proved regular-quotient splitting, and the separately
proved Springer socle formula forces a row or a column.  No homogeneous
defining-sequence assumption is imposed.
-/

noncomputable section

open TauCeti Module MvPolynomial RingTheory.Sequence
open scoped Classical

namespace HigherSpecht

variable {K : Type*} [Field K] {n : ℕ} {lam : YoungDiagram}

theorem regularSequencePresentation_adjoin
    (I : Ideal (PolynomialRing n K)) (hI : I ≤ RingHom.ker constantCoeff)
    (hci : IsRegularSequencePresentation I) (ys : List (PolynomialRing n K))
    (hy : IsWeaklyRegular (PolynomialRing n K ⧸ I) (ys.map (Ideal.Quotient.mk I)))
    (hzero : ∀ y ∈ ys, constantCoeff y = 0) :
    IsRegularSequencePresentation (I ⊔ Ideal.ofList ys) := by
  obtain ⟨xs, hx, hxs⟩ := hci
  let W (J : Submodule (PolynomialRing n K) (PolynomialRing n K)) : Prop :=
    IsWeaklyRegular (PolynomialRing n K ⧸ J) ys
  have hyR : W I :=
    (isWeaklyRegular_map_algebraMap_iff (PolynomialRing n K ⧸ I)
      (PolynomialRing n K ⧸ I) ys).mp hy
  have htop : (Ideal.ofList xs •
      (⊤ : Submodule (PolynomialRing n K) (PolynomialRing n K))) = I := by
    change Ideal.ofList xs * ⊤ = I
    rw [Ideal.mul_top, hxs]
  have hy' : W (Ideal.ofList xs •
      (⊤ : Submodule (PolynomialRing n K) (PolynomialRing n K))) :=
    (congrArg W htop).mpr hyR
  have hweak : IsWeaklyRegular (PolynomialRing n K) (xs ++ ys) :=
    (isWeaklyRegular_append_iff (PolynomialRing n K) xs ys).mpr ⟨hx.1, hy'⟩
  refine ⟨xs ++ ys, polynomialSequence_isRegular_of_constantCoeff_zero K _ hweak ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hI (hxs ▸ Ideal.subset_span hp)
    · exact hzero p hp
  · rw [Ideal.ofList_append, hxs]

theorem specialFiber_regularSequencePresentation
    (hk : lam.card ≤ n)
    (hci : IsRegularSequencePresentation (untruncatedIdeal K n lam)) :
    IsRegularSequencePresentation (untruncatedIdeal K n (adjoinOnes lam (n - lam.card))) := by
  let m := n - lam.card
  have hideal : untruncatedIdeal K n (adjoinOnes lam m) =
      untruncatedIdeal K n lam ⊔ elementaryParameterIdeal K n m := by
    have h := specialFiberIdeal_eq (R := K) lam m
    have hsize : lam.card + m = n := Nat.add_sub_of_le hk
    rwa [hsize] at h
  rw [hideal]
  have hp : Ideal.ofList (elementaryParameterSequence K n m) =
      elementaryParameterIdeal K n m := by
    have h := elementaryParameterSequence_prefix_ideal (K := K) (n := n) m m le_rfl
    have ht : (elementaryParameterSequence K n m).take m = elementaryParameterSequence K n m :=
      List.take_of_length_le (by simp only [elementaryParameterSequence_length, le_refl])
    rwa [ht] at h
  rw [← hp]
  apply regularSequencePresentation_adjoin _ (untruncatedIdeal_le_constantCoeff_ker n lam)
    hci _ (untruncated_elementarySequence_isWeaklyRegular K n lam hk)
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact constantCoeff_elementaryOn Finset.univ (Nat.zero_lt_succ i.val)

theorem fullSize_variableAnnihilator_finrank (K : Type*) [Field K]
    (n : ℕ) (mu : YoungDiagram) (hcard : mu.card = n) :
    Module.finrank K ((quotientVariableAnnihilator (untruncatedIdeal K n mu)).restrictScalars K) =
      Fintype.card (StandardYoungTableau mu) := by
  subst n
  have hs : springerSocle K mu =
      (quotientVariableAnnihilator (springerIdeal K mu)).restrictScalars K :=
    quotient_socle_restrictScalars_eq_variableAnnihilator (springerIdeal K mu)
      (fun i => ⟨mu.card, springer_coordinate_pow_card_eq_zero mu i⟩)
  rw [show untruncatedIdeal K mu.card mu = springerIdeal K mu from rfl, ← hs]
  exact springer_socle_finrank K mu

theorem standardCount_adjoinOnes_eq_one_of_regularSequencePresentation
    (hk : lam.card ≤ n)
    (hci : IsRegularSequencePresentation (untruncatedIdeal K n lam)) :
    standardCount (adjoinOnes lam (n - lam.card)) = 1 := by
  let mu := adjoinOnes lam (n - lam.card)
  have hcard : mu.card = n := by
    rw [adjoinOnes_card, Nat.add_sub_of_le hk]
  have hdim := fullSize_variableAnnihilator_finrank K n mu hcard
  have hpos : 0 < Module.finrank K
      ((quotientVariableAnnihilator (untruncatedIdeal K n mu)).restrictScalars K) := by
    rw [hdim]
    exact Fintype.card_pos
  have hone := regularSequencePresentation_variableAnnihilator_finrank_one
    (untruncatedIdeal K n mu) (untruncatedIdeal_le_constantCoeff_ker n mu)
    (specialFiber_regularSequencePresentation hk hci) hpos
  rw [hdim] at hone
  simpa only [standardCount_def] using hone

theorem adjoinOnes_extremeShape_iff (hk : lam.card ≤ n) :
    (adjoinOnes lam (n - lam.card)).rowLen 0 ≤ 1 ∨
        (adjoinOnes lam (n - lam.card)).colLen 0 ≤ 1 ↔
      lam.rowLen 0 ≤ 1 ∨ lam.card = n ∧ lam.colLen 0 ≤ 1 := by
  constructor
  · rintro (hcolumn | hrow)
    · exact Or.inl ((YoungDiagram.rowLen_le_of_le (le_adjoinOnes lam (n - lam.card)) 0).trans
        hcolumn)
    · by_cases hcolumn : lam.rowLen 0 ≤ 1
      · exact Or.inl hcolumn
      · have hpos : 0 < lam.colLen 0 := by
          have hcell : (0, 0) ∈ lam := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
          exact YoungDiagram.mem_iff_lt_colLen.mp hcell
        rw [adjoinOnes_colLen_zero] at hrow
        exact Or.inr ⟨by omega, by omega⟩
  · rintro (hcolumn | ⟨hcard, hrow⟩)
    · left
      rw [adjoinOnes_rowLen]
      split_ifs <;> omega
    · right
      rw [adjoinOnes_colLen_zero, hcard, Nat.sub_self, add_zero]
      exact hrow

/-- The exact complete-intersection clause of Corollary 7.6. The left
side is an actual regular-sequence presentation in the original ambient
polynomial ring. Both directions retain all fields and the empty cases. -/
theorem corollary_7_6_completeIntersection_iff (K : Type*) [Field K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    IsRegularSequencePresentation (untruncatedIdeal K n lam) ↔
      lam.rowLen 0 ≤ 1 ∨ lam.card = n ∧ lam.colLen 0 ≤ 1 := by
  constructor
  · intro hci
    apply (adjoinOnes_extremeShape_iff hk).mp
    exact standardCount_eq_one_iff.mp
      (standardCount_adjoinOnes_eq_one_of_regularSequencePresentation hk hci)
  · exact corollary_7_6_completeIntersection_sufficiency hk

theorem corollary_7_6_completeIntersection_iff_enlargedShape
    (K : Type*) [Field K] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    IsRegularSequencePresentation (untruncatedIdeal K n lam) ↔
      (adjoinOnes lam (n - lam.card)).rowLen 0 ≤ 1 ∨
        (adjoinOnes lam (n - lam.card)).colLen 0 ≤ 1 :=
  (corollary_7_6_completeIntersection_iff K n lam hk).trans
    (adjoinOnes_extremeShape_iff hk).symm

end HigherSpecht
end
end CanonicalSource33

section CanonicalSource34
/- Source: HigherSpecht/GorensteinClassification.lean -/



/-!
# The standard Gorenstein classification in Corollary 7.6

The left side is the ordinary Noetherian, local finite
self-injective-dimension condition.  Necessity passes through the
actual origin localization and the actual Springer socle.  Sufficiency
uses a genuine cyclic generator of the proved dualizing module.
-/

noncomputable section

open TauCeti Module

namespace HigherSpecht

variable (K : Type*) [Field K]

theorem untruncated_isGorenstein_iff_one_standard_tableau
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    IsGorensteinRing (UntruncatedRing K n lam) ↔
      Fintype.card (StandardYoungTableau (adjoinOnes lam (n - lam.card))) = 1 :=
  ⟨untruncated_gorenstein_standardTableau_card_eq_one K n lam hk,
    untruncated_isGorenstein_of_one_standard_tableau K n lam hk⟩

/-- The row/column criterion retains all coefficient fields, the empty
diagram, and the case with no elementary parameters. -/
theorem corollary_7_6_gorenstein_iff_enlargedShape
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    IsGorensteinRing (UntruncatedRing K n lam) ↔
      (adjoinOnes lam (n - lam.card)).rowLen 0 ≤ 1 ∨
        (adjoinOnes lam (n - lam.card)).colLen 0 ≤ 1 := by
  rw [untruncated_isGorenstein_iff_one_standard_tableau K n lam hk,
    ← standardCount_def]
  exact standardCount_eq_one_iff

theorem corollary_7_6_gorenstein_iff
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    IsGorensteinRing (UntruncatedRing K n lam) ↔
      lam.rowLen 0 ≤ 1 ∨ lam.card = n ∧ lam.colLen 0 ≤ 1 :=
  (corollary_7_6_gorenstein_iff_enlargedShape K n lam hk).trans
    (adjoinOnes_extremeShape_iff hk)

/-- The two conditions are equivalent for these actual quotient rings;
neither side is defined by the shape criterion. -/
theorem corollary_7_6_gorenstein_iff_completeIntersection
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    IsGorensteinRing (UntruncatedRing K n lam) ↔
      IsRegularSequencePresentation (untruncatedIdeal K n lam) :=
  (corollary_7_6_gorenstein_iff K n lam hk).trans
    (corollary_7_6_completeIntersection_iff K n lam hk).symm

end HigherSpecht
end
end CanonicalSource34

section CanonicalSource1000
/- Source: HigherSpecht/AdmissibleParameterBasis.lean -/



/-!
# The coefficient extension of the prescribed parameter basis

Remark 6.2 concerns the unchanged, unnormalized higher Specht representatives.
The finite prescribed Griffin bases give the full untruncated vector basis by
degreewise stabilization. Expanding the elementary-parameter monomial basis
then proves independence over the actual parameter ring, and the already
proved span transfer proves spanning over that ring.

The final statements have no finite-basis premise. They cover every good-
characteristic field, the exact localization `ℤ[1/n!]`, and, more generally,
every nontrivial commutative ring in which `n!` is a unit. The actual one-row
member proves the necessity of the stated field-characteristic condition.
-/

noncomputable section

open TauCeti Module MvPolynomial

namespace HigherSpecht

theorem untruncatedFamily_linearIndependent_parameters_of_vector_independence
    (R : Type*) [CommRing R] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hv : LinearIndependent R (untruncatedVectorFamily R n lam hk)) :
    LinearIndependent (ElementaryParameterRing R n lam)
      (untruncatedFamily R n lam hk) := by
  apply linearIndependent_scalarRing_of_expansion
    (MvPolynomial.basisMonomials (Fin (n - lam.card)) R)
  have h := hv.comp parameterVectorIndex parameterVectorIndex_injective
  simpa only [MvPolynomial.coe_basisMonomials, parameter_monomial_smul,
    Function.comp_def] using h

/-- The generic stabilization-to-parameter-basis transfer. The following
unconditional endpoints instantiate its finite-basis input with proved bases. -/
def untruncatedParameterBasisFromAnyFiniteBases
    (R : Type*) [CommRing R] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hb : ∀ s : ℕ, 0 < s → lam.colLen 0 ≤ s →
      IsSpecifiedBasis (R := R) (griffinFamily R n lam hk s)) :
    Basis (UntruncatedIndex n lam hk) (ElementaryParameterRing R n lam)
      (UntruncatedRing R n lam) := by
  let B := untruncatedVectorBasisFromAnyFiniteBases R n lam hk hb
  have hB : (B : UntruncatedVectorIndex n lam hk → UntruncatedRing R n lam) =
      untruncatedVectorFamily R n lam hk :=
    funext (untruncatedVectorBasisFromAnyFiniteBases_apply R n lam hk hb)
  apply Basis.mk
  · apply untruncatedFamily_linearIndependent_parameters_of_vector_independence R n lam hk
    simpa only [← hB] using B.linearIndependent
  · exact untruncatedFamily_spans_parameters_of_vector_span R n lam hk
      (untruncatedVectorFamily_spans_of_finite_bases R n lam hk hb)

@[simp] theorem untruncatedParameterBasisFromAnyFiniteBases_apply
    (R : Type*) [CommRing R] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hb : ∀ s : ℕ, 0 < s → lam.colLen 0 ≤ s →
      IsSpecifiedBasis (R := R) (griffinFamily R n lam hk s))
    (i : UntruncatedIndex n lam hk) :
    untruncatedParameterBasisFromAnyFiniteBases R n lam hk hb i =
      untruncatedFamily R n lam hk i := by
  simp only [untruncatedParameterBasisFromAnyFiniteBases, Basis.mk_apply]

/-- The literal higher Specht free basis over every nontrivial commutative
coefficient ring in which `n!` is a unit. -/
theorem untruncated_specified_parameter_basis_of_factorial_isUnit
    (R : Type*) [CommRing R] [Nontrivial R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hfac : IsUnit (n.factorial : R)) :
    IsSpecifiedBasis (R := ElementaryParameterRing R n lam)
      (untruncatedFamily R n lam hk) := by
  let hb := fun s hs hh =>
    griffin_specifiedBasis_of_factorial_isUnit R n lam hk s hs hh hfac
  exact ⟨untruncatedParameterBasisFromAnyFiniteBases R n lam hk hb,
    untruncatedParameterBasisFromAnyFiniteBases_apply R n lam hk hb⟩

/-- Necessity uses an actual index of the prescribed family: the one-row
tableau pair has polynomial `n!`, also for the empty partition. -/
theorem factorial_ne_zero_of_untruncated_specified_parameter_basis
    (R : Type*) [CommRing R] [Nontrivial R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hb : IsSpecifiedBasis (R := ElementaryParameterRing R n lam)
      (untruncatedFamily R n lam hk)) :
    (n.factorial : R) ≠ 0 := by
  intro hzero
  obtain ⟨B, hB⟩ := hb
  let i : UntruncatedIndex n lam hk :=
    (oneRowParameterIndex n lam hk 0).base
  have hi : untruncatedFamily R n lam hk i = 0 := by
    change Ideal.Quotient.mk (untruncatedIdeal R n lam)
      (pairPolynomial (oneRowPair n)) = 0
    rw [pairPolynomial_oneRow, map_natCast]
    simpa only [map_natCast, map_zero] using
      congrArg (algebraMap R (UntruncatedRing R n lam)) hzero
  exact B.ne_zero i ((hB i).trans hi)

/-- Remark 6.2: the unchanged parameter higher Specht family is a basis
exactly in characteristic zero or characteristic greater than `n`.
There is no nonempty-partition or positive-variable-count restriction. -/
theorem remark_6_2_untruncated_characteristic
    (K : Type*) [Field K] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    IsSpecifiedBasis (R := ElementaryParameterRing K n lam)
      (untruncatedFamily K n lam hk) ↔
      ringChar K = 0 ∨ n < ringChar K := by
  constructor
  · intro hb
    exact (factorial_ne_zero_iff_characteristic_range K n).mp
      (factorial_ne_zero_of_untruncated_specified_parameter_basis K n lam hk hb)
  · intro hchar
    let hb := fun s hs hh =>
      (corollary_8_1_griffin_characteristic_all_partitions K n lam hk s hs hh).mpr hchar
    exact ⟨untruncatedParameterBasisFromAnyFiniteBases K n lam hk hb,
      untruncatedParameterBasisFromAnyFiniteBases_apply K n lam hk hb⟩

/-- Remark 6.2 over the exact coefficient ring `Localization.Away (n! : ℤ)`.
The basis indices and polynomial representatives are unchanged. -/
theorem remark_6_2_untruncated_localized
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    IsSpecifiedBasis (R := ElementaryParameterRing (FactorialLocalization n) n lam)
      (untruncatedFamily (FactorialLocalization n) n lam hk) := by
  let hb := fun s hs hh => corollary_8_1_griffin_localized n lam hk s hs hh
  exact ⟨untruncatedParameterBasisFromAnyFiniteBases (FactorialLocalization n) n lam hk hb,
    untruncatedParameterBasisFromAnyFiniteBases_apply (FactorialLocalization n) n lam hk hb⟩

end HigherSpecht
end
end CanonicalSource1000

section CanonicalSource35
/- Source: audit/ExpressionSpechtCopyStatements.lean -/



/-!
# Literal Specht-copy audit for Corollaries 5.3 and 6.7

Pending source only. These statements inspect the actual intertwiner range,
the span of the original quotient polynomials, their genuine permutation
orbits, irreducibility, and equivalence with the ordinary complex Specht
representation. They are not character-equality substitutes.

The finite-family hypotheses match Corollary 5.3's explicit finite nonempty
family and Corollary 6.7's atomic/binary finite-expression operations.
No nullary sum or intersection is asserted.
-/

noncomputable section

open Module MvPolynomial TauCeti TauCeti.YoungTableau HigherSpecht
open scoped Classical

universe u

namespace ExpressionSpechtCopyAudit

theorem finite_expression_copy {n s : ℕ}
    (e : GriffinIdealExpression n s) (hs : 0 < s)
    (i : FiniteHarmonicIndex n s) (hi : i ∈ e.eligible) :
    (e.complexIntertwiner i).range.toSubmodule =
      Submodule.span ℂ (Set.range
        (fun T : StandardYoungTableau (YoungDiagram.ofPartition i.part) =>
          Ideal.Quotient.mk (e.ideal ℂ) (finiteMasterPolynomial i T))) ∧
    (∀ T : StandardYoungTableau (YoungDiagram.ofPartition i.part),
      (e.complexIntertwiner i).range.toSubmodule =
        Submodule.span ℂ (Set.range (fun g : Equiv.Perm (Fin n) =>
          quotientRepresentation (e.ideal ℂ) (e.permutationStable ℂ) g
            (Ideal.Quotient.mk (e.ideal ℂ) (finiteMasterPolynomial i T))))) ∧
    Representation.IsIrreducible (e.complexIntertwiner i).range.toRepresentation ∧
    Nonempty (Representation.Equiv (spechtModuleℂ i.part).ρ
      (e.complexIntertwiner i).range.toRepresentation) :=
  e.corollary_5_3_specht_copy hs i hi

theorem untruncated_expression_copy {n : ℕ}
    (e : UntruncatedIdealExpression n)
    (i : UnboundedHarmonicIndex n) (hi : i ∈ e.eligible) :
    (e.complexIntertwiner i).range.toSubmodule =
      Submodule.span ℂ (Set.range
        (fun T : StandardYoungTableau (YoungDiagram.ofPartition i.part) =>
          Ideal.Quotient.mk (e.ideal ℂ) (unboundedMasterPolynomial i T))) ∧
    (∀ T : StandardYoungTableau (YoungDiagram.ofPartition i.part),
      (e.complexIntertwiner i).range.toSubmodule =
        Submodule.span ℂ (Set.range (fun g : Equiv.Perm (Fin n) =>
          quotientRepresentation (e.ideal ℂ) (e.permutationStable ℂ) g
            (Ideal.Quotient.mk (e.ideal ℂ) (unboundedMasterPolynomial i T))))) ∧
    Representation.IsIrreducible (e.complexIntertwiner i).range.toRepresentation ∧
    Nonempty (Representation.Equiv (spechtModuleℂ i.part).ρ
      (e.complexIntertwiner i).range.toRepresentation) :=
  e.corollary_6_7_specht_copy i hi

theorem finite_nonempty_family_copies
    {ι : Type u} [Finite ι] [Nonempty ι] {n s : ℕ} (hs : 0 < s)
    (A : ι → BoundedGriffinShape n s) :
    (∀ i : FiniteHarmonicIndex n s,
      (∃ j, i.toUnboundedHarmonicIndex.eligible (A j).diagram (A j).card_le) →
      ∃ hJ : PermutationStable (⨅ j, griffinIdeal ℂ n (A j).diagram s),
        ∃ V : Subrepresentation (quotientRepresentation (⨅ j, griffinIdeal ℂ n (A j).diagram s) hJ),
          V.toSubmodule = Submodule.span ℂ
            (Set.range (fun T : StandardYoungTableau (YoungDiagram.ofPartition i.part) =>
              Ideal.Quotient.mk (⨅ j, griffinIdeal ℂ n (A j).diagram s) (finiteMasterPolynomial i T))) ∧
          (∀ T : StandardYoungTableau (YoungDiagram.ofPartition i.part),
            V.toSubmodule = Submodule.span ℂ
              (Set.range (fun g : Equiv.Perm (Fin n) =>
                quotientRepresentation (⨅ j, griffinIdeal ℂ n (A j).diagram s) hJ g
                  (Ideal.Quotient.mk (⨅ j, griffinIdeal ℂ n (A j).diagram s) (finiteMasterPolynomial i T))))) ∧
          Representation.IsIrreducible V.toRepresentation ∧
          Nonempty (Representation.Equiv (spechtModuleℂ i.part).ρ V.toRepresentation)) ∧
    (∀ i : FiniteHarmonicIndex n s,
      (∀ j, i.toUnboundedHarmonicIndex.eligible (A j).diagram (A j).card_le) →
      ∃ hJ : PermutationStable (⨆ j, griffinIdeal ℂ n (A j).diagram s),
        ∃ V : Subrepresentation (quotientRepresentation (⨆ j, griffinIdeal ℂ n (A j).diagram s) hJ),
          V.toSubmodule = Submodule.span ℂ
            (Set.range (fun T : StandardYoungTableau (YoungDiagram.ofPartition i.part) =>
              Ideal.Quotient.mk (⨆ j, griffinIdeal ℂ n (A j).diagram s) (finiteMasterPolynomial i T))) ∧
          (∀ T : StandardYoungTableau (YoungDiagram.ofPartition i.part),
            V.toSubmodule = Submodule.span ℂ
              (Set.range (fun g : Equiv.Perm (Fin n) =>
                quotientRepresentation (⨆ j, griffinIdeal ℂ n (A j).diagram s) hJ g
                  (Ideal.Quotient.mk (⨆ j, griffinIdeal ℂ n (A j).diagram s) (finiteMasterPolynomial i T))))) ∧
          Representation.IsIrreducible V.toRepresentation ∧
          Nonempty (Representation.Equiv (spechtModuleℂ i.part).ρ V.toRepresentation)) := by
  simpa only [IsLiteralQuotientSpechtCopy] using
    corollary_5_3_finite_family_specht_copies hs A

theorem untruncated_finite_nonempty_family_copies
    {ι : Type u} [Finite ι] [Nonempty ι] {n : ℕ}
    (A : ι → BoundedUntruncatedShape n) :
    (∀ i : UnboundedHarmonicIndex n,
      (∃ j, i.eligible (A j).diagram (A j).card_le) →
      ∃ hJ : PermutationStable (⨅ j, untruncatedIdeal ℂ n (A j).diagram),
        ∃ V : Subrepresentation (quotientRepresentation (⨅ j, untruncatedIdeal ℂ n (A j).diagram) hJ),
          V.toSubmodule = Submodule.span ℂ
            (Set.range (fun T : StandardYoungTableau (YoungDiagram.ofPartition i.part) =>
              Ideal.Quotient.mk (⨅ j, untruncatedIdeal ℂ n (A j).diagram) (unboundedMasterPolynomial i T))) ∧
          (∀ T : StandardYoungTableau (YoungDiagram.ofPartition i.part),
            V.toSubmodule = Submodule.span ℂ
              (Set.range (fun g : Equiv.Perm (Fin n) =>
                quotientRepresentation (⨅ j, untruncatedIdeal ℂ n (A j).diagram) hJ g
                  (Ideal.Quotient.mk (⨅ j, untruncatedIdeal ℂ n (A j).diagram) (unboundedMasterPolynomial i T))))) ∧
          Representation.IsIrreducible V.toRepresentation ∧
          Nonempty (Representation.Equiv (spechtModuleℂ i.part).ρ V.toRepresentation)) ∧
    (∀ i : UnboundedHarmonicIndex n,
      (∀ j, i.eligible (A j).diagram (A j).card_le) →
      ∃ hJ : PermutationStable (⨆ j, untruncatedIdeal ℂ n (A j).diagram),
        ∃ V : Subrepresentation (quotientRepresentation (⨆ j, untruncatedIdeal ℂ n (A j).diagram) hJ),
          V.toSubmodule = Submodule.span ℂ
            (Set.range (fun T : StandardYoungTableau (YoungDiagram.ofPartition i.part) =>
              Ideal.Quotient.mk (⨆ j, untruncatedIdeal ℂ n (A j).diagram) (unboundedMasterPolynomial i T))) ∧
          (∀ T : StandardYoungTableau (YoungDiagram.ofPartition i.part),
            V.toSubmodule = Submodule.span ℂ
              (Set.range (fun g : Equiv.Perm (Fin n) =>
                quotientRepresentation (⨆ j, untruncatedIdeal ℂ n (A j).diagram) hJ g
                  (Ideal.Quotient.mk (⨆ j, untruncatedIdeal ℂ n (A j).diagram) (unboundedMasterPolynomial i T))))) ∧
          Representation.IsIrreducible V.toRepresentation ∧
          Nonempty (Representation.Equiv (spechtModuleℂ i.part).ρ V.toRepresentation)) := by
  simpa only [IsLiteralQuotientSpechtCopy] using
    corollary_6_7_finite_family_specht_copies A

end ExpressionSpechtCopyAudit

#print HigherSpecht.GriffinIdealExpression.corollary_5_3_specht_copy
#print axioms HigherSpecht.GriffinIdealExpression.corollary_5_3_specht_copy
#print HigherSpecht.UntruncatedIdealExpression.corollary_6_7_specht_copy
#print axioms HigherSpecht.UntruncatedIdealExpression.corollary_6_7_specht_copy
#print HigherSpecht.corollary_5_3_finite_family_specht_copies
#print axioms HigherSpecht.corollary_5_3_finite_family_specht_copies
#print HigherSpecht.corollary_6_7_finite_family_specht_copies
#print axioms HigherSpecht.corollary_6_7_finite_family_specht_copies
#print axioms ExpressionSpechtCopyAudit.finite_expression_copy
#print axioms ExpressionSpechtCopyAudit.untruncated_expression_copy
#print axioms ExpressionSpechtCopyAudit.finite_nonempty_family_copies
#print axioms ExpressionSpechtCopyAudit.untruncated_finite_nonempty_family_copies
end
end CanonicalSource35

section CanonicalSource36
/- Source: audit/FiniteIdealFamilyStatements.lean -/



/-!
# Literal finite-family correspondence checks

These targets write the actual ideal suprema/infima, prefix-catabolism
conditions, and original higher-Specht products.  They do not define a
finite family by the expression fold whose interpretation is being checked.
The index type is any finite nonempty type, in any universe.

Reconstructed after the runtime outage.  This is pending source, with no
compilation, axiom inspection, or kernel replay asserted.
-/

noncomputable section
open TauCeti TauCeti.YoungTableau Module MvPolynomial HigherSpecht
open scoped Classical

universe u

namespace SpechtFiniteFamilyAudit

/-- The two literal finite-family basis clauses of Corollary 5.3.  Different
partitions may have different sizes; only the ambient `n` and truncation `s`
are shared. -/
def GriffinFiniteFamilyLiteral
    (ι : Type u) [Finite ι] [Nonempty ι]
    (n s : ℕ) (lam : ι → YoungDiagram)
    (hk : ∀ j, (lam j).card ≤ n) : Prop :=
  IsSpecifiedBasis (R := ℂ)
    (fun z : (Σ i : {i : FiniteHarmonicIndex n s //
          ∀ j, i.multiplier.colLen 0 ≤ n - (lam j).card ∧
            CatDominates (prefixTableau i.left (lam j).card
              (by simpa only [YoungDiagram.card_ofPartition] using hk j)) (lam j)},
          StandardYoungTableau (YoungDiagram.ofPartition i.val.part)) =>
      Ideal.Quotient.mk (⨆ j, griffinIdeal ℂ n (lam j) s)
        (rename (finCongr (YoungDiagram.card_ofPartition z.1.val.part))
          (higherSpechtPolynomial z.1.val.left z.2) *
          elementaryMultiplier n n z.1.val.multiplier.rowLen)) ∧
  IsSpecifiedBasis (R := ℂ)
    (fun z : (Σ i : {i : FiniteHarmonicIndex n s //
          ∃ j, i.multiplier.colLen 0 ≤ n - (lam j).card ∧
            CatDominates (prefixTableau i.left (lam j).card
              (by simpa only [YoungDiagram.card_ofPartition] using hk j)) (lam j)},
          StandardYoungTableau (YoungDiagram.ofPartition i.val.part)) =>
      Ideal.Quotient.mk (⨅ j, griffinIdeal ℂ n (lam j) s)
        (rename (finCongr (YoungDiagram.card_ofPartition z.1.val.part))
          (higherSpechtPolynomial z.1.val.left z.2) *
          elementaryMultiplier n n z.1.val.multiplier.rowLen))

theorem corollary_5_3_finiteFamily_literal
    (ι : Type u) [Finite ι] [Nonempty ι]
    (n s : ℕ) (hs : 0 < s) (lam : ι → YoungDiagram)
    (hk : ∀ j, (lam j).card ≤ n)
    (hheight : ∀ j, (lam j).colLen 0 ≤ s) :
    GriffinFiniteFamilyLiteral ι n s lam hk := by
  constructor
  · exact GriffinIdealExpression.corollary_5_3_finiteSum_basis
      (fun j => .atom ⟨lam j, hk j, hheight j⟩) hs
  · exact GriffinIdealExpression.corollary_5_3_finiteIntersection_basis
      (fun j => .atom ⟨lam j, hk j, hheight j⟩) hs

/-- The finite-family vector-space clauses of Corollary 6.7.  There is no
common-size premise for these two basis assertions. -/
def UntruncatedFiniteFamilyLiteral
    (ι : Type u) [Finite ι] [Nonempty ι]
    (n : ℕ) (lam : ι → YoungDiagram)
    (hk : ∀ j, (lam j).card ≤ n) : Prop :=
  IsSpecifiedBasis (R := ℂ)
    (fun z : (Σ i : {i : UnboundedHarmonicIndex n //
          ∀ j, i.multiplier.colLen 0 ≤ n - (lam j).card ∧
            CatDominates (prefixTableau i.left (lam j).card
              (by simpa only [YoungDiagram.card_ofPartition] using hk j)) (lam j)},
          StandardYoungTableau (YoungDiagram.ofPartition i.val.part)) =>
      Ideal.Quotient.mk (⨆ j, untruncatedIdeal ℂ n (lam j))
        (rename (finCongr (YoungDiagram.card_ofPartition z.1.val.part))
          (higherSpechtPolynomial z.1.val.left z.2) *
          elementaryMultiplier n n z.1.val.multiplier.rowLen)) ∧
  IsSpecifiedBasis (R := ℂ)
    (fun z : (Σ i : {i : UnboundedHarmonicIndex n //
          ∃ j, i.multiplier.colLen 0 ≤ n - (lam j).card ∧
            CatDominates (prefixTableau i.left (lam j).card
              (by simpa only [YoungDiagram.card_ofPartition] using hk j)) (lam j)},
          StandardYoungTableau (YoungDiagram.ofPartition i.val.part)) =>
      Ideal.Quotient.mk (⨅ j, untruncatedIdeal ℂ n (lam j))
        (rename (finCongr (YoungDiagram.card_ofPartition z.1.val.part))
          (higherSpechtPolynomial z.1.val.left z.2) *
          elementaryMultiplier n n z.1.val.multiplier.rowLen))

theorem corollary_6_7_finiteFamily_literal
    (ι : Type u) [Finite ι] [Nonempty ι]
    (n : ℕ) (lam : ι → YoungDiagram)
    (hk : ∀ j, (lam j).card ≤ n) :
    UntruncatedFiniteFamilyLiteral ι n lam hk := by
  constructor
  · exact UntruncatedIdealExpression.corollary_6_7_finiteSum_basis
      (fun j => .atom ⟨lam j, hk j⟩)
  · exact UntruncatedIdealExpression.corollary_6_7_finiteIntersection_basis
      (fun j => .atom ⟨lam j, hk j⟩)

end SpechtFiniteFamilyAudit

#print SpechtFiniteFamilyAudit.corollary_5_3_finiteFamily_literal
#print SpechtFiniteFamilyAudit.corollary_6_7_finiteFamily_literal
#print axioms SpechtFiniteFamilyAudit.corollary_5_3_finiteFamily_literal
#print axioms SpechtFiniteFamilyAudit.corollary_6_7_finiteFamily_literal
#print axioms HigherSpecht.UntruncatedIdealExpression.finiteSum_allSize
#print axioms HigherSpecht.UntruncatedIdealExpression.finiteIntersection_allSize
end
end CanonicalSource36

section CanonicalSource37
/- Source: audit/OrderedRootZeroStatements.lean -/



/-!
# Literal zero-parameter identity and coordinate-action check

This gate requires one and the same canonical map to fix every original
Springer class and to intertwine every actual coordinate permutation.  The
last clause exposes its action on an arbitrary polynomial representative.
It is a pending statement check, not a compilation or certification report.
-/

noncomputable section

open TauCeti HigherSpecht
open scoped Classical TensorProduct

namespace SpechtOrderedRootZeroAudit

def NoParameterEquivariantIdentityLiteral
    (R : Type*) [CommRing R] (lam : YoungDiagram) : Prop :=
  (∀ x : PolynomialRing lam.card R ⧸ springerIdeal R lam,
    proposition_7_2_no_parameters R lam
      ((1 : OrderedRootRing R (lam.card - lam.card))
        ⊗ₜ[ElementaryParameterRing R lam.card lam] x) = x) ∧
  (∀ (g : Equiv.Perm (Fin lam.card))
      (z : OrderedRootRing R (lam.card - lam.card)
        ⊗[ElementaryParameterRing R lam.card lam]
          (PolynomialRing lam.card R ⧸ springerIdeal R lam)),
    proposition_7_2_no_parameters R lam
        (elementaryParameterTensorPermutation
          (OrderedRootRing R (lam.card - lam.card)) g z) =
      springerPermutationAlgEquiv lam g
        (proposition_7_2_no_parameters R lam z)) ∧
  (∀ (g : Equiv.Perm (Fin lam.card)) (p : PolynomialRing lam.card R),
    proposition_7_2_no_parameters R lam
        (elementaryParameterTensorPermutation
          (OrderedRootRing R (lam.card - lam.card)) g
          ((1 : OrderedRootRing R (lam.card - lam.card))
            ⊗ₜ[ElementaryParameterRing R lam.card lam]
            Ideal.Quotient.mk (springerIdeal R lam) p)) =
      Ideal.Quotient.mk (springerIdeal R lam) (MvPolynomial.rename g p))

theorem proposition_7_2_no_parameters_equivariant_identity_literal
    (R : Type*) [CommRing R] (lam : YoungDiagram) :
    NoParameterEquivariantIdentityLiteral R lam := by
  refine ⟨proposition_7_2_no_parameters_identity R lam,
    proposition_7_2_no_parameters_permutation R lam, ?_⟩
  intro g p
  exact (proposition_7_2_no_parameters_permutation R lam g
    ((1 : OrderedRootRing R (lam.card - lam.card))
      ⊗ₜ[ElementaryParameterRing R lam.card lam]
        Ideal.Quotient.mk (springerIdeal R lam) p)).trans
    ((congrArg (springerPermutationAlgEquiv (R := R) lam g)
      (proposition_7_2_no_parameters_identity R lam
        (Ideal.Quotient.mk (springerIdeal R lam) p))).trans
      (springerPermutationAlgEquiv_mk (R := R) lam g p))

end SpechtOrderedRootZeroAudit

#print SpechtOrderedRootZeroAudit.proposition_7_2_no_parameters_equivariant_identity_literal
#print axioms SpechtOrderedRootZeroAudit.proposition_7_2_no_parameters_equivariant_identity_literal
end
end CanonicalSource37

section CanonicalSource38
/- Source: audit/SpechtHomologicalStatements.lean -/



/-!
# Literal statement audit for Section 7.1 of the higher Specht manuscript

This file is a pending audit target, not a verification certificate.  It
expands regularity into support and attainment in the actual derived Tor
groups, levelness/type into genuine canonical-module generators, Gorenstein
into local finite self-injective dimension, and complete intersection into
an actual regular sequence generating the stated polynomial ideal.

Every assertion quantifies over all coefficient fields.  The only partition
restriction is its printed size bound.  Zero variables and the empty
partition are included.  The statistic n(lambda) is written as the literal
sum of row index times row length, with row indices starting at zero.
-/

noncomputable section

open CategoryTheory Module TauCeti HigherSpecht
open scoped Classical BigOperators

universe u

namespace SpechtHomologicalAudit

/-- Actual Tor support, including the attained exact regularity value. -/
def RegularityStatement : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n),
    let r : ℤ :=
      ((∑ i ∈ Finset.range (lam.colLen 0), i * lam.rowLen i : ℕ) : ℤ) +
        (n - lam.card : ℕ) * (lam.colLen 0 : ℤ)
    (∀ (i : ℕ) (j : ℤ), n < i ∨ j < i ∨ r < j - i →
      Subsingleton ((untruncatedTorGrading K n lam hk i).piece j)) ∧
      ∃ i : ℕ, i ≤ n ∧
        ¬ Subsingleton ((untruncatedTorGrading K n lam hk i).piece (i + r))

theorem regularity_statement : RegularityStatement := by
  intro K _ n lam hk
  simpa only [springerTopDegree_eq_sum_rows, UntruncatedTorPiece] using
    corollary_7_5_tor_support K n lam hk

/-- The actual Springer socle, rather than a subspace defined by its
expected degree or dimension. -/
def SpringerSocleStatement : Prop :=
  ∀ (K : Type u) [Field K] (mu : YoungDiagram),
    (TauCeti.socle (SpringerRing K mu) (SpringerRing K mu)).restrictScalars K =
      quotientHomogeneousPiece (springerIdeal K mu)
        (∑ i ∈ Finset.range (mu.colLen 0), i * mu.rowLen i) ∧
    Module.finrank K
      ((TauCeti.socle (SpringerRing K mu) (SpringerRing K mu)).restrictScalars K) =
      Fintype.card (StandardYoungTableau mu)

theorem springer_socle_statement : SpringerSocleStatement := by
  intro K _ mu
  simpa only [springerSocle, springerTopDegree_eq_sum_rows] using
    springer_socle_concentrated_and_type K mu

/-- The actual normalized relative dual is dualizing and has precisely
the printed number of generators in precisely the printed degree.
The minimality clause permits arbitrary, not necessarily homogeneous,
finite generating families. -/
def CanonicalModuleStatement : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n),
    let A := UntruncatedRing K n lam
    let omega := UntruncatedRelativeDual K n lam
    let mu := adjoinOnes lam (n - lam.card)
    let degree : ℤ := ((n - lam.card + 1).choose 2 : ℤ) -
      ((∑ i ∈ Finset.range (mu.colLen 0), i * mu.rowLen i : ℕ) : ℤ)
    let count := Fintype.card (StandardYoungTableau mu)
    (∀ (P : Ideal A) [P.IsPrime],
      Module.IsCohenMacaulay (Localization.AtPrime P) (Localization.AtPrime P)) ∧
    (IsNoetherianRing A ∧ Module.Finite A omega ∧
      (∃ d : ℕ, HasInjectiveDimensionLE (ModuleCat.of A omega) d) ∧
      Function.Bijective (fun a : A => LinearMap.lsmul A omega a) ∧
      (letI := HasExt.standard (ModuleCat.{u} A)
       ∀ i : ℕ, 0 < i →
         ∀ e : CategoryTheory.Abelian.Ext (ModuleCat.of A omega) (ModuleCat.of A omega) i, e = 0)) ∧
    (∃ v : Fin count → omega,
      (∀ i, v i ∈ (untruncatedRelativeDualGrading K n lam hk).piece degree) ∧
      Submodule.span A (Set.range v) = ⊤) ∧
    (∀ r (v : Fin r → omega), Submodule.span A (Set.range v) = ⊤ → count ≤ r)

theorem canonical_module_statement : CanonicalModuleStatement := by
  intro K _ n lam hk
  refine ⟨untruncated_isCohenMacaulay_atPrime_allFields K n lam hk, ?_⟩
  simpa only [IsDualizingModule, springerTopDegree_eq_sum_rows] using
    corollary_7_6_canonical_module K n lam hk

/-- The local self-injective-dimension condition is stated explicitly.
The empty partition is included by the column condition. -/
def GorensteinStatement : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n),
    (IsNoetherianRing (UntruncatedRing K n lam) ∧
      ∀ P : PrimeSpectrum (UntruncatedRing K n lam),
        ∃ d : ℕ, HasInjectiveDimensionLE
          (ModuleCat.of (Localization.AtPrime P.asIdeal)
            (Localization.AtPrime P.asIdeal)) d) ↔
      lam.rowLen 0 ≤ 1 ∨ lam.card = n ∧ lam.colLen 0 ≤ 1

theorem gorenstein_statement : GorensteinStatement := by
  intro K _ n lam hk
  simpa only [IsGorensteinRing] using corollary_7_6_gorenstein_iff K n lam hk

/-- The complete-intersection side is an actual regular-sequence
presentation inside the manuscript's polynomial ring. -/
def CompleteIntersectionStatement : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n),
    (∃ xs : List (PolynomialRing n K),
      RingTheory.Sequence.IsRegular (PolynomialRing n K) xs ∧
      Ideal.ofList xs = untruncatedIdeal K n lam) ↔
      lam.rowLen 0 ≤ 1 ∨ lam.card = n ∧ lam.colLen 0 ≤ 1

theorem complete_intersection_statement : CompleteIntersectionStatement := by
  intro K _ n lam hk
  simpa only [IsRegularSequencePresentation] using
    corollary_7_6_completeIntersection_iff K n lam hk

/-- Both standard algebraic conditions hold for exactly the same
actual quotient rings, with no condition defined through the partition. -/
theorem gorenstein_iff_complete_intersection
    (K : Type u) [Field K] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    (IsNoetherianRing (UntruncatedRing K n lam) ∧
      ∀ P : PrimeSpectrum (UntruncatedRing K n lam),
        ∃ d : ℕ, HasInjectiveDimensionLE
          (ModuleCat.of (Localization.AtPrime P.asIdeal)
            (Localization.AtPrime P.asIdeal)) d) ↔
    (∃ xs : List (PolynomialRing n K),
      RingTheory.Sequence.IsRegular (PolynomialRing n K) xs ∧
      Ideal.ofList xs = untruncatedIdeal K n lam) := by
  simpa only [IsGorensteinRing, IsRegularSequencePresentation] using
    corollary_7_6_gorenstein_iff_completeIntersection K n lam hk

end SpechtHomologicalAudit

-- Print the actual mathematical constructions as well as the literal targets.
#print HigherSpecht.polynomialResidueModule
#print HigherSpecht.polynomialTorModule
#print HigherSpecht.polynomialTorGrading
#print HigherSpecht.untruncatedTorGrading
#print HigherSpecht.RelativeDual
#print HigherSpecht.RelativeDual.smul_apply
#print HigherSpecht.untruncatedRelativeDualGrading
#print HigherSpecht.IsDualizingModule
#print HigherSpecht.IsGorensteinRing
#print HigherSpecht.IsRegularSequencePresentation
#print SpechtHomologicalAudit.RegularityStatement
#print SpechtHomologicalAudit.SpringerSocleStatement
#print SpechtHomologicalAudit.CanonicalModuleStatement
#print SpechtHomologicalAudit.GorensteinStatement
#print SpechtHomologicalAudit.CompleteIntersectionStatement
#print axioms SpechtHomologicalAudit.regularity_statement
#print axioms SpechtHomologicalAudit.springer_socle_statement
#print axioms SpechtHomologicalAudit.canonical_module_statement
#print axioms SpechtHomologicalAudit.gorenstein_statement
#print axioms SpechtHomologicalAudit.complete_intersection_statement
#print axioms SpechtHomologicalAudit.gorenstein_iff_complete_intersection
end
end CanonicalSource38

section CanonicalSource39
/- Source: audit/AlternativeMultiplierCopyStatements.lean -/



/-!
# Literal alternative-multiplier copy checks

Every range in these targets is the span of the displayed, unchanged
higher-Specht products.  The multiplier conditions in the theorem gates
refer only to indices used by the actual family.  An actual intertwining
equivalence and irreducibility are both asserted; equality of characters
alone is not the conclusion.

Pending reconstructed source, not a compilation or certification report.
-/

noncomputable section
open TauCeti TauCeti.YoungTableau Module MvPolynomial HigherSpecht
open scoped Classical

namespace SpechtAlternativeMultiplierAudit

def GriffinAlternativeCopyLiteral
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ)
    (f : YoungDiagram → PolynomialRing n ℂ) : Prop :=
  ∀ (part : n.Partition) (i : PartitionGriffinCopies n lam hk s part),
    ∃ W : Subrepresentation (griffinRepresentation ℂ n lam s),
      W.toSubmodule =
        Submodule.span ℂ (Set.range fun T : StandardYoungTableau (YoungDiagram.ofPartition part) =>
          Ideal.Quotient.mk (griffinIdeal ℂ n lam s)
            (rename (finCongr (YoungDiagram.card_ofPartition part))
              (higherSpechtPolynomial i.left T) * f i.multiplier)) ∧
      Representation.IsIrreducible W.toRepresentation ∧
      Nonempty (Representation.Equiv (partitionSpechtRepresentationOver ℂ part) W.toRepresentation)

theorem corollary_4_3_alternativeCopy_literal
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s)
    (f : YoungDiagram → PolynomialRing n ℂ)
    (hf : ∀ z : GriffinIndex n lam hk s,
      IsDominanceTriangularMultiplier n z.multiplier (f z.multiplier)) :
    GriffinAlternativeCopyLiteral n lam hk s f := by
  intro part i
  exact corollary_4_3_copy_on_admissible_multipliers
    n lam hk s hs hheight f hf part i

def ExpressionAlternativeCopyLiteral {n s : ℕ}
    (e : GriffinIdealExpression n s)
    (f : YoungDiagram → PolynomialRing n ℂ) : Prop :=
  ∀ i : {i : FiniteHarmonicIndex n s // i ∈ e.eligible},
    ∃ W : Subrepresentation
        (quotientRepresentation (e.ideal ℂ) (e.permutationStable ℂ)),
      W.toSubmodule =
        Submodule.span ℂ (Set.range fun T :
            StandardYoungTableau (YoungDiagram.ofPartition i.val.part) =>
          Ideal.Quotient.mk (e.ideal ℂ)
            (rename (finCongr (YoungDiagram.card_ofPartition i.val.part))
              (higherSpechtPolynomial i.val.left T) * f i.val.multiplier)) ∧
      Representation.IsIrreducible W.toRepresentation ∧
      Nonempty (Representation.Equiv (partitionSpechtRepresentationOver ℂ i.val.part) W.toRepresentation)

theorem corollary_5_3_alternativeCopy_literal {n s : ℕ}
    (e : GriffinIdealExpression n s) (hs : 0 < s)
    (f : YoungDiagram → PolynomialRing n ℂ)
    (hf : ∀ i : {i : FiniteHarmonicIndex n s // i ∈ e.eligible},
      IsDominanceTriangularMultiplier n i.val.multiplier (f i.val.multiplier)) :
    ExpressionAlternativeCopyLiteral e f := by
  intro i
  have h := e.corollary_5_3_alternative_copy_onEligible f hf hs i
  refine ⟨e.alternativeCopyOnEligible f hf i, ?_, h.2⟩
  exact h.1

end SpechtAlternativeMultiplierAudit

#print SpechtAlternativeMultiplierAudit.corollary_4_3_alternativeCopy_literal
#print SpechtAlternativeMultiplierAudit.corollary_5_3_alternativeCopy_literal
#print axioms SpechtAlternativeMultiplierAudit.corollary_4_3_alternativeCopy_literal
#print axioms SpechtAlternativeMultiplierAudit.corollary_5_3_alternativeCopy_literal
#print axioms HigherSpecht.griffinFixedCopyOver_toSubmodule
#print axioms HigherSpecht.adaptedGriffinCopy_eq_span
end
end CanonicalSource39

section CanonicalSource40
/- Source: audit/Theorem32SelectedFamilyStatements.lean -/



/-!
# Literal selected-family pairing audit

Reconstructed after the outage. This is a pending source gate, not a
compiler or replay certificate. The entries below are the actual
coefficient functionals and the actual column-Vandermonde witnesses.
-/

noncomputable section

open Module MvPolynomial TauCeti TauCeti.YoungTableau HigherSpecht
open scoped Classical

universe u

namespace SpechtSelectedPairingAudit

theorem literal_entry (K : Type u) [Field K] [CharZero K]
    {μ : YoungDiagram} (A : Finset (StandardYoungTableau μ))
    (T : StandardYoungTableau μ) (e : Fin A.card ≃ A) (i j : Fin A.card) :
    higherSpechtApolarFunctional (K := K) (e i).val T.toTableau
      (higherSpechtPolynomial (e j).val T) =
    (ordinaryAction (higherSpechtPolynomial (R := K) (e j).val T)
      (columnWitness (insertionFilling (e i).val T.toTableau).toEmbedding 1)).coeff
        (insertionRejectionExponent (e i).val T.toTableau) :=
  theorem_3_2_selected_entry A T e i j

theorem literal_triangular_matrix (K : Type u) [Field K] [CharZero K]
    {μ : YoungDiagram} (A : Finset (StandardYoungTableau μ))
    (T : StandardYoungTableau μ) :
    ∃ e : Fin A.card ≃ A,
      Monotone (fun i => higherSpechtPrefixKey (e i).val T.toTableau) ∧
      (∀ i j : Fin A.card, i ≤ j →
        higherSpechtPrefixKey (e i).val T.toTableau =
          higherSpechtPrefixKey (e j).val T.toTableau →
        A.equivFin (e i) ≤ A.equivFin (e j)) ∧
      (∀ i j : Fin A.card, j < i →
        higherSpechtApolarFunctional (K := K) (e i).val T.toTableau
          (higherSpechtPolynomial (e j).val T) = 0) ∧
      (∀ i : Fin A.card,
        higherSpechtApolarFunctional (K := K) (e i).val T.toTableau
          (higherSpechtPolynomial (e i).val T) =
          ((rowFillingStabilizers T.toTableau
            (transportedCocharge (e i).val T.toTableau)).card : K) *
          ((insertionFixedPermutations (e i).val T.toTableau).card : K) *
          ((exponentFactorial (insertionAlpha (e i).val T.toTableau) : K) /
            exponentFactorial (insertionRejectionExponent (e i).val T.toTableau))) ∧
      (∀ i : Fin A.card,
        higherSpechtApolarFunctional (K := K) (e i).val T.toTableau
          (higherSpechtPolynomial (e i).val T) ≠ 0) ∧
      (∀ i : Fin A.card,
        0 < higherSpechtApolarFunctional (K := ℚ) (e i).val T.toTableau
          (higherSpechtPolynomial (e i).val T)) :=
  theorem_3_2_selected_family K A T

end SpechtSelectedPairingAudit

#print HigherSpecht.theorem_3_2_selected_entry
#print axioms HigherSpecht.theorem_3_2_selected_entry
#print HigherSpecht.theorem_3_2_selected_family
#print axioms HigherSpecht.theorem_3_2_selected_family
#print axioms SpechtSelectedPairingAudit.literal_entry
#print axioms SpechtSelectedPairingAudit.literal_triangular_matrix
end
end CanonicalSource40

section CanonicalSource41
/- Source: audit/SpechtIntegralHilbertStatements.lean -/



/-!
# Literal degreewise audit of the finite-s integral normal forms

Reconstructed after the outage. Pending source only: no compilation or
certificate is asserted. The graded piece is written as the actual image
of homogeneous polynomials, and field independence has no characteristic
assumption.
-/

noncomputable section

open Module MvPolynomial TauCeti HigherSpecht
open scoped Classical

universe u v

namespace SpechtIntegralHilbertAudit

theorem integral_degree_basis
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) (d : ℕ) :
    ∃ B : Basis {a : GriffinStaircaseExponents n lam s // a.val.degree = d} ℤ
        ((homogeneousSubmodule (Fin n) ℤ d).map
          (Ideal.Quotient.mkₐ ℤ (griffinIdeal ℤ n lam s)).toLinearMap),
      ∀ a, (B a : GriffinRing ℤ n lam s) =
        Ideal.Quotient.mk (griffinIdeal ℤ n lam s)
          (MvPolynomial.monomial a.val.val 1) :=
  lemma_6_4_griffin_degree_integral n lam hk s hs hheight d

theorem degreewise_field_independence
    (K : Type u) (L : Type v) [Field K] [Field L]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) (d : ℕ) :
    Module.finrank K
      ((homogeneousSubmodule (Fin n) K d).map
        (Ideal.Quotient.mkₐ K (griffinIdeal K n lam s)).toLinearMap) =
    Module.finrank L
      ((homogeneousSubmodule (Fin n) L d).map
        (Ideal.Quotient.mkₐ L (griffinIdeal L n lam s)).toLinearMap) :=
  griffinHilbertFunction_independent_field K L n lam hk s hs hheight d

end SpechtIntegralHilbertAudit

#print HigherSpecht.lemma_6_4_griffin_degree_integral
#print axioms HigherSpecht.lemma_6_4_griffin_degree_integral
#print HigherSpecht.griffinHilbertFunction_independent_field
#print axioms HigherSpecht.griffinHilbertFunction_independent_field
#print axioms SpechtIntegralHilbertAudit.integral_degree_basis
#print axioms SpechtIntegralHilbertAudit.degreewise_field_independence
end
end CanonicalSource41

section CanonicalSource42
/- Source: audit/GriffinCharacteristicAllPartitionsStatements.lean -/



noncomputable section
open TauCeti Module

namespace HigherSpechtAudit

/-- A literal basis for the original family, for every partition including
the empty partition, in exactly the admissible field characteristics. -/
theorem griffin_characteristic_all_partitions_statement
    (K : Type*) [Field K] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    (∃ B : Basis (HigherSpecht.GriffinIndex n lam hk s) K
        (HigherSpecht.GriffinRing K n lam s),
      ∀ i, B i = HigherSpecht.griffinFamily K n lam hk s i) ↔
      ringChar K = 0 ∨ n < ringChar K :=
  HigherSpecht.corollary_8_1_griffin_characteristic_all_partitions
    K n lam hk s hs hheight

#print griffin_characteristic_all_partitions_statement
#print axioms griffin_characteristic_all_partitions_statement

end HigherSpechtAudit
end
end CanonicalSource42

section CanonicalSource43
/- Source: audit/ParameterPrincipalStatements.lean -/



/-!
# Literal statement checks for Sections 6–8

These statements expose the actual quotients, prescribed representatives,
coefficient rings, and quantifiers. No `*Target` proposition is assumed.
They are source fixtures until this file is compiled against the final
verified stages. The canonical imports above are temporary integration
headers; the final build may replace only that header with the verified
stages that contain these same canonical declarations.

Theorem 6.1 is asserted over every characteristic-zero field, covering its
printed complex-coefficient statement. Corollary 6.5 retains every allowed
partition (including the empty one) and every coefficient field, with no
characteristic hypothesis. Theorem 7.1 retains arbitrary finite root sets,
positive nonzero-root multiplicities, arbitrary zero-root multiplicity, and
all field characteristics. Corollary 8.1 includes the empty partition and
every positive power bound satisfying the paper's height condition; there
is no characteristic bound involving that power parameter.
-/

noncomputable section

open HigherSpecht TauCeti Module MvPolynomial
open scoped Classical BigOperators Polynomial TensorProduct

namespace ParameterPrincipalStatementAudit

/-- The scalar action used by each parameter-basis statement is the actual
map from formal parameters to elementary symmetric polynomial classes. -/
theorem parameter_action (R : Type*) [CommRing R]
    (n : ℕ) (lam : YoungDiagram) (j : Fin (n - lam.card)) :
    algebraMap (MvPolynomial (Fin (n - lam.card)) R)
        (PolynomialRing n R ⧸ untruncatedIdeal R n lam) (MvPolynomial.X j) =
      Ideal.Quotient.mk (untruncatedIdeal R n lam)
        (MvPolynomial.esymm (Fin n) R (j.val + 1)) := by
  exact MvPolynomial.aeval_X (elementaryParameterClasses R n lam) j

/-- Theorem 6.1: the literal elementary classes, original higher Specht
representatives, finite free parameter basis, and exact numerical rank. -/
theorem theorem61_basis_rank (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    AlgebraicIndependent K
      (fun j : Fin (n - lam.card) =>
        Ideal.Quotient.mk (untruncatedIdeal K n lam)
          (MvPolynomial.esymm (Fin n) K (j.val + 1))) ∧
    (∃ B : Basis (UntruncatedIndex n lam hk)
        (MvPolynomial (Fin (n - lam.card)) K)
        (PolynomialRing n K ⧸ untruncatedIdeal K n lam),
      ∀ i, B i = Ideal.Quotient.mk (untruncatedIdeal K n lam)
        (MvPolynomial.rename (finCongr i.val.card_eq)
          (higherSpechtPolynomial (R := K) i.val.left i.val.right))) ∧
    Module.Finite (MvPolynomial (Fin (n - lam.card)) K)
      (PolynomialRing n K ⧸ untruncatedIdeal K n lam) ∧
    Module.finrank (MvPolynomial (Fin (n - lam.card)) K)
      (PolynomialRing n K ⧸ untruncatedIdeal K n lam) =
        n.factorial / (∏ j ∈ Finset.range (lam.colLen 0), (lam.rowLen j).factorial) := by
  exact theorem_6_1_basis_and_rank K n lam hk

/-- The representatives of the displayed parameter basis have the actual
polynomial grading, not degrees attached to an abstract basis. -/
theorem theorem61_representative_degree {R : Type*} [CommRing R]
    {n : ℕ} {lam : YoungDiagram} {hk : lam.card ≤ n}
    (i : UntruncatedIndex n lam hk) :
    (MvPolynomial.rename (finCongr i.val.card_eq)
      (higherSpechtPolynomial (R := R) i.val.left i.val.right)).IsHomogeneous
        (cochargeDegree i.val.left) :=
  pairPolynomial_isHomogeneous i.val

/-- Theorem 6.1: ordinary Krull dimension and Cohen–Macaulayness at every
prime localization of the actual polynomial quotient. -/
theorem theorem61_dimension_cm (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    ringKrullDim (PolynomialRing n K ⧸ untruncatedIdeal K n lam) =
        (n - lam.card : ℕ) ∧
    IsNoetherianRing (PolynomialRing n K ⧸ untruncatedIdeal K n lam) ∧
    ∀ (P : Ideal (PolynomialRing n K ⧸ untruncatedIdeal K n lam)) [P.IsPrime],
      Module.IsCohenMacaulay (Localization.AtPrime P) (Localization.AtPrime P) := by
  exact theorem_6_1_dimension_and_cohenMacaulay K n lam hk

/-- Corollary 6.5: any integral monomial basis of the specified Springer
special fiber lifts unchanged. The index type has no finiteness premise. -/
theorem corollary65_arbitrary_integral_monomial_lift
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    {ι : Type*} (a : ι → Fin n →₀ ℕ)
    (B : Basis ι ℤ
      (PolynomialRing n ℤ ⧸ untruncatedIdeal ℤ n (adjoinOnes lam (n - lam.card))))
    (hB : ∀ i, B i =
      Ideal.Quotient.mk (untruncatedIdeal ℤ n (adjoinOnes lam (n - lam.card)))
        (MvPolynomial.monomial (a i) 1)) :
    ∃ C : Basis ι (MvPolynomial (Fin (n - lam.card)) ℤ)
        (PolynomialRing n ℤ ⧸ untruncatedIdeal ℤ n lam),
      ∀ i, C i = Ideal.Quotient.mk (untruncatedIdeal ℤ n lam)
        (MvPolynomial.monomial (a i) 1) := by
  refine ⟨integralMonomialParameterBasis_of_basis n lam hk a B hB, ?_⟩
  intro i
  exact integralMonomialParameterBasis_of_basis_apply n lam hk a B hB i

/-- Corollary 6.5: the constructed unchanged staircase monomials give an
actual parameter basis over every commutative coefficient ring. -/
theorem corollary65_monomial_basis_all_rings (R : Type*) [CommRing R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    ∃ B : Basis (UntruncatedStaircaseExponents n (adjoinOnes lam (n - lam.card)))
        (MvPolynomial (Fin (n - lam.card)) R)
        (PolynomialRing n R ⧸ untruncatedIdeal R n lam),
      ∀ a, B a = Ideal.Quotient.mk (untruncatedIdeal R n lam)
        (MvPolynomial.monomial a.val 1) := by
  refine ⟨untruncatedMonomialParameterBasis R n lam hk, ?_⟩
  intro a
  exact untruncatedMonomialParameterBasis_apply R n lam hk a

/-- The all-field algebraic conclusions of Corollary 6.5 use the literal
elementary parameter map, exact factorial quotient, and local depth. -/
theorem corollary65_all_fields (K : Type*) [Field K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    AlgebraicIndependent K
      (fun j : Fin (n - lam.card) =>
        Ideal.Quotient.mk (untruncatedIdeal K n lam)
          (MvPolynomial.esymm (Fin n) K (j.val + 1))) ∧
    Module.Free (MvPolynomial (Fin (n - lam.card)) K)
      (PolynomialRing n K ⧸ untruncatedIdeal K n lam) ∧
    Module.Finite (MvPolynomial (Fin (n - lam.card)) K)
      (PolynomialRing n K ⧸ untruncatedIdeal K n lam) ∧
    Module.finrank (MvPolynomial (Fin (n - lam.card)) K)
      (PolynomialRing n K ⧸ untruncatedIdeal K n lam) =
        n.factorial / (∏ j ∈ Finset.range (lam.colLen 0), (lam.rowLen j).factorial) ∧
    ringKrullDim (PolynomialRing n K ⧸ untruncatedIdeal K n lam) =
        (n - lam.card : ℕ) ∧
    ∀ (P : Ideal (PolynomialRing n K ⧸ untruncatedIdeal K n lam)) [P.IsPrime],
      Module.IsCohenMacaulay (Localization.AtPrime P) (Localization.AtPrime P) := by
  exact corollary_6_5_allFields K n lam hk

theorem corollary65_flat_all_rings (R : Type*) [CommRing R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Module.Flat (MvPolynomial (Fin (n - lam.card)) R)
      (PolynomialRing n R ⧸ untruncatedIdeal R n lam) :=
  untruncated_parameter_flat_allCoefficients R n lam hk

/-- The assignment subtype is independent of the chosen finite-cardinality
instance on each fiber.  This public equality uses `Nat.card` in its literal
predicate, so public algebra-equivalence definitions can transport across it
without exposing a private helper or a chosen subtype `Fintype` instance. -/
theorem rootAssignments_eq_literal {n : ℕ} {ι : Type*} [Fintype ι]
    (lam : YoungDiagram) (r0 : ℕ) (r : ι → ℕ) :
    PrescribedRootAssignments n (splitRootMultiplicities lam r0 r) =
      {f : Fin n → Option ι // ∀ i : Option ι,
        Nat.card {j : Fin n // f j = i} = i.elim (lam.card + r0) r} := by
  apply congrArg (fun p : (Fin n → Option ι) → Prop => {f // p f})
  funext f
  apply propext
  constructor
  · intro hf i
    simpa only [Fintype.card_eq_nat_card, splitRootMultiplicities] using hf i
  · intro hf i
    simpa only [Fintype.card_eq_nat_card, splitRootMultiplicities] using hf i

/-- Theorem 7.1: the left side spells out the original ideal and parameter
equations. The right side uses the actual assignment type and tensor product. -/
def theorem71_parameter_fiber
    (K : Type*) [Field K] {n m : ℕ} {ι : Type*} [Fintype ι]
    (lam : YoungDiagram) (a : Fin m → K) (hsize : lam.card + m = n)
    (r0 : ℕ) (c : ι → K) (hc : Function.Injective c) (hcz : ∀ i, c i ≠ 0)
    (r : ι → ℕ) (hr : ∀ i, 0 < r i)
    (hfactor : parameterPolynomial a =
      Polynomial.X ^ r0 * ∏ i : ι, (Polynomial.X - Polynomial.C (c i)) ^ r i) :
    (PolynomialRing n K ⧸
      (untruncatedIdeal K n lam ⊔ Ideal.span (Set.range fun j : Fin m =>
        elementaryOn (Finset.univ : Finset (Fin n)) (j.val + 1) - MvPolynomial.C (a j)))) ≃ₐ[K]
      ∀ _f : {f : Fin n → Option ι //
          ∀ i : Option ι, Fintype.card {j : Fin n // f j = i} =
            i.elim (lam.card + r0) r},
        ⨂[K] i : Option ι,
          SpringerRing K (i.elim (adjoinOnes lam r0) (fun j => columnPartition (r j))) :=
  by
    have hassign : PrescribedRootAssignments n (splitRootMultiplicities lam r0 r) =
        {f : Fin n → Option ι // ∀ i : Option ι,
          Fintype.card {j : Fin n // f j = i} = i.elim (lam.card + r0) r} := by
      simpa only [Fintype.card_eq_nat_card] using
        (rootAssignments_eq_literal (n := n) lam r0 r)
    exact Eq.mp (congrArg (fun J : Type _ =>
      ParameterFiber K n lam m a ≃ₐ[K]
        (J → ⨂[K] i : Option ι,
          SpringerRing K (i.elim (adjoinOnes lam r0) (fun j => columnPartition (r j))))) hassign)
      (theorem_7_1_parameter_fiber K lam a hsize r0 c hc hcz r hr hfactor)

theorem theorem71_factor_count {n : ℕ} {ι : Type*} [Fintype ι]
    (lam : YoungDiagram) (r0 : ℕ) (r : ι → ℕ)
    (hsize : lam.card + (r0 + ∑ i, r i) = n) :
    Fintype.card {f : Fin n → Option ι //
      ∀ i : Option ι, Fintype.card {j : Fin n // f j = i} =
        i.elim (lam.card + r0) r} =
      n.factorial / ((lam.card + r0).factorial * ∏ i, (r i).factorial) :=
  by
    simpa only [PrescribedRootAssignments, splitRootMultiplicities,
      Fintype.card_eq_nat_card] using
      (theorem_7_1_number_of_factors lam r0 r hsize)

/-- The nonsplit clause is actual scalar extension, along an arbitrary
field extension where the signed parameter polynomial has the factorization. -/
def theorem71_after_field_extension
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    {n m : ℕ} {ι : Type*} [Fintype ι]
    (lam : YoungDiagram) (a : Fin m → K) (hsize : lam.card + m = n)
    (r0 : ℕ) (c : ι → L) (hc : Function.Injective c) (hcz : ∀ i, c i ≠ 0)
    (r : ι → ℕ) (hr : ∀ i, 0 < r i)
    (hfactor : parameterPolynomial (fun i => algebraMap K L (a i)) =
      Polynomial.X ^ r0 * ∏ i : ι, (Polynomial.X - Polynomial.C (c i)) ^ r i) :
    L ⊗[K] (PolynomialRing n K ⧸
      (untruncatedIdeal K n lam ⊔ Ideal.span (Set.range fun j : Fin m =>
        elementaryOn (Finset.univ : Finset (Fin n)) (j.val + 1) - MvPolynomial.C (a j)))) ≃ₐ[L]
      ∀ _f : {f : Fin n → Option ι //
          ∀ i : Option ι, Fintype.card {j : Fin n // f j = i} =
            i.elim (lam.card + r0) r},
        ⨂[L] i : Option ι,
          SpringerRing L (i.elim (adjoinOnes lam r0) (fun j => columnPartition (r j))) :=
  by
    have hassign : PrescribedRootAssignments n (splitRootMultiplicities lam r0 r) =
        {f : Fin n → Option ι // ∀ i : Option ι,
          Fintype.card {j : Fin n // f j = i} = i.elim (lam.card + r0) r} := by
      simpa only [Fintype.card_eq_nat_card] using
        (rootAssignments_eq_literal (n := n) lam r0 r)
    exact Eq.mp (congrArg (fun J : Type _ =>
      L ⊗[K] ParameterFiber K n lam m a ≃ₐ[L]
        (J → ⨂[L] i : Option ι,
          SpringerRing L (i.elim (adjoinOnes lam r0) (fun j => columnPartition (r j))))) hassign)
      (theorem_7_1_after_scalar_extension K L lam a hsize r0 c hc hcz r hr hfactor)

/-- The full all-fiber assertion after algebraic closure has no root-choice
or factorization hypothesis: the roots and their multiplicities are taken
from the actual parameter polynomial's root multiset. -/
def theorem71_algebraic_closure (K : Type*) [Field K] {n m : ℕ}
    (lam : YoungDiagram) (a : Fin m → K) (hsize : lam.card + m = n) :
    let L := AlgebraicClosure K
    let Q := parameterPolynomial (fun i => algebraMap K L (a i))
    L ⊗[K] (PolynomialRing n K ⧸
      (untruncatedIdeal K n lam ⊔ Ideal.span (Set.range fun j : Fin m =>
        elementaryOn (Finset.univ : Finset (Fin n)) (j.val + 1) - MvPolynomial.C (a j)))) ≃ₐ[L]
      ∀ _f : {f : Fin n → Option (nonzeroRootSet Q) //
          ∀ i : Option (nonzeroRootSet Q), Fintype.card {j : Fin n // f j = i} =
            i.elim (lam.card + Q.roots.count 0) (canonicalRootMultiplicity Q)},
        ⨂[L] i : Option (nonzeroRootSet Q),
          SpringerRing L (i.elim (adjoinOnes lam (Q.roots.count 0))
            (fun j => columnPartition (canonicalRootMultiplicity Q j))) :=
  by
    let L := AlgebraicClosure K
    let Q := parameterPolynomial (fun i => algebraMap K L (a i))
    have hassign : PrescribedRootAssignments n
        (splitRootMultiplicities lam (Q.roots.count 0) (canonicalRootMultiplicity Q)) =
        {f : Fin n → Option (nonzeroRootSet Q) // ∀ i : Option (nonzeroRootSet Q),
          Fintype.card {j : Fin n // f j = i} =
            i.elim (lam.card + Q.roots.count 0) (canonicalRootMultiplicity Q)} := by
      simpa only [Fintype.card_eq_nat_card] using
        (rootAssignments_eq_literal (n := n) lam (Q.roots.count 0) (canonicalRootMultiplicity Q))
    exact Eq.mp (congrArg (fun J : Type _ =>
      L ⊗[K] ParameterFiber K n lam m a ≃ₐ[L]
        (J → ⨂[L] i : Option (nonzeroRootSet Q),
          SpringerRing L (i.elim (adjoinOnes lam (Q.roots.count 0))
            (fun j => columnPartition (canonicalRootMultiplicity Q j))))) hassign)
      (theorem_7_1_algebraicClosure K lam a hsize)

/-- Corollary 8.1, including the empty partition, with the literal
unnormalized finite-family representatives and the full multiplier range. -/
theorem corollary81_griffin_iff (K : Type*) [Field K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    (∃ B : Basis (GriffinIndex n lam hk s) K
        (PolynomialRing n K ⧸ griffinIdeal K n lam s),
      ∀ i, B i = Ideal.Quotient.mk (griffinIdeal K n lam s)
        (MvPolynomial.rename (finCongr i.pair.card_eq)
            (higherSpechtPolynomial (R := K) i.pair.left i.pair.right) *
          elementaryMultiplier n (n - lam.card) i.multiplier.rowLen)) ↔
      ringChar K = 0 ∨ n < ringChar K := by
  exact corollary_8_1_griffin_characteristic_all_partitions K n lam hk s hs hheight

theorem corollary81_springer_iff (K : Type*) [Field K] (lam : YoungDiagram) :
    (∃ B : Basis (SpringerIndex lam) K (PolynomialRing lam.card K ⧸ springerIdeal K lam),
      ∀ i, B i = Ideal.Quotient.mk (springerIdeal K lam)
        (MvPolynomial.rename (finCongr i.val.card_eq)
          (higherSpechtPolynomial (R := K) i.val.left i.val.right))) ↔
      ringChar K = 0 ∨ lam.card < ringChar K := by
  exact corollary_8_1_springer_characteristic K lam

/-- The localization is the actual ring obtained by inverting `n!`. -/
theorem corollary81_griffin_localized
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    ∃ B : Basis (GriffinIndex n lam hk s) (Localization.Away (n.factorial : ℤ))
        (PolynomialRing n (Localization.Away (n.factorial : ℤ)) ⧸
          griffinIdeal (Localization.Away (n.factorial : ℤ)) n lam s),
      ∀ i, B i = Ideal.Quotient.mk
        (griffinIdeal (Localization.Away (n.factorial : ℤ)) n lam s)
        (MvPolynomial.rename (finCongr i.pair.card_eq)
            (higherSpechtPolynomial (R := Localization.Away (n.factorial : ℤ))
              i.pair.left i.pair.right) *
          elementaryMultiplier n (n - lam.card) i.multiplier.rowLen) := by
  exact corollary_8_1_griffin_localized n lam hk s hs hheight

theorem corollary81_springer_localized (lam : YoungDiagram) :
    ∃ B : Basis (SpringerIndex lam) (Localization.Away (lam.card.factorial : ℤ))
        (PolynomialRing lam.card (Localization.Away (lam.card.factorial : ℤ)) ⧸
          springerIdeal (Localization.Away (lam.card.factorial : ℤ)) lam),
      ∀ i, B i = Ideal.Quotient.mk
        (springerIdeal (Localization.Away (lam.card.factorial : ℤ)) lam)
        (MvPolynomial.rename (finCongr i.val.card_eq)
          (higherSpechtPolynomial (R := Localization.Away (lam.card.factorial : ℤ))
            i.val.left i.val.right)) := by
  exact corollary_8_1_springer_localized lam

/-- The irreducible finite copy is the span of the actual fixed-left
polynomials, and is equivalent to the ordinary Specht representation. -/
theorem corollary81_griffin_copy {K : Type*} [Field K] {n : ℕ}
    (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ)
    (part : n.Partition) (i : PartitionGriffinCopies n lam hk s part)
    (hchar : ringChar K = 0 ∨ n < ringChar K) (hheight : lam.colLen 0 ≤ s) :
    ∃ V : Subrepresentation (griffinRepresentation K n lam s),
      V.toSubmodule = Submodule.span K
        (Set.range fun T : StandardYoungTableau (YoungDiagram.ofPartition part) =>
          Ideal.Quotient.mk (griffinIdeal K n lam s)
            (MvPolynomial.rename (finCongr (YoungDiagram.card_ofPartition part))
              (higherSpechtPolynomial i.left T) *
                elementaryMultiplier n (n - lam.card) i.multiplier.rowLen)) ∧
      Representation.IsIrreducible V.toRepresentation ∧
      Nonempty (Representation.Equiv (partitionSpechtRepresentationOver K part) V.toRepresentation) := by
  refine ⟨griffinFixedCopyOver K lam hk s part i, ?_, ?_⟩
  · exact griffinFixedCopyOver_toSubmodule K lam hk s part i
  · exact corollary_8_1_griffin_copy_irreducible lam hk s part i hchar hheight

/-- The same literal-span and genuine representation-equivalence check for
every eligible Springer left tableau. -/
theorem corollary81_springer_copy {K : Type*} [Field K]
    (lam : YoungDiagram) (part : lam.card.Partition)
    (S : StandardYoungTableau (YoungDiagram.ofPartition part)) (hS : CatDominates S lam)
    (hchar : ringChar K = 0 ∨ lam.card < ringChar K) :
    ∃ V : Subrepresentation (springerRepresentation K lam),
      V.toSubmodule = Submodule.span K
        (Set.range fun T : StandardYoungTableau (YoungDiagram.ofPartition part) =>
          Ideal.Quotient.mk (springerIdeal K lam)
            (MvPolynomial.rename (finCongr (YoungDiagram.card_ofPartition part))
              (higherSpechtPolynomial S T))) ∧
      Representation.IsIrreducible V.toRepresentation ∧
      Nonempty (Representation.Equiv (partitionSpechtRepresentationOver K part) V.toRepresentation) := by
  refine ⟨springerFixedCopyOver K lam part S, ?_, ?_⟩
  · exact springerFixedCopyOver_toSubmodule K lam part S
  · exact corollary_8_1_springer_copy_irreducible lam part S hS hchar

end ParameterPrincipalStatementAudit
end
end CanonicalSource43

section CanonicalSource44
/- Source: HigherSpecht/FinalStatementAudit.lean -/



/-!
# Literal checks of the principal statements

These independently written statements avoid the `*Target` predicates. They
display the actual quotient representatives, Specht-copy spans, degrees, and
simultaneous decompositions. The index definitions are the original ones in
`Statements` and `SimultaneousStatements`; in particular no count, spanning,
catabolism, or representation assertion is an additional hypothesis here.

This file is a final consumer of the endpoint modules. It must not be imported
by those modules or by an umbrella which it itself imports. A staged build may
replace only the three imports above with its final endpoint-closure import.
The declarations and proof bodies below are unchanged by that header rewrite.
-/

noncomputable section

open TauCeti Module MvPolynomial

namespace HigherSpecht.FinalStatementAudit

/-- Theorem 1.1: every basis vector is the prescribed higher Specht coset. -/
theorem theorem_1_1_basis (lam : YoungDiagram) :
    ∃ b : Basis (SpringerIndex lam) ℂ
        (PolynomialRing lam.card ℂ ⧸ springerIdeal ℂ lam),
      ∀ i, b i = Ideal.Quotient.mk (springerIdeal ℂ lam)
        (rename (finCongr i.val.card_eq)
          (higherSpechtPolynomial (R := ℂ) i.val.left i.val.right)) := by
  simpa only [IsSpecifiedBasis, springerFamily, pairPolynomial] using
    (springer_basis_target ℂ lam)

/-- The grading in Theorem 1.1 is the degree of the actual polynomial. -/
theorem theorem_1_1_degree {mu : YoungDiagram}
    (S T : StandardYoungTableau mu) :
    (higherSpechtPolynomial (R := ℂ) S T).IsHomogeneous (cochargeDegree S) :=
  higherSpechtPolynomial_isHomogeneous S T

/-- The fixed-left-tableau span in Theorem 1.1 is the indicated irreducible
Specht module, with its actual induced permutation action. -/
theorem theorem_1_1_copies (lam : YoungDiagram) (part : lam.card.Partition)
    (S : StandardYoungTableau (YoungDiagram.ofPartition part))
    (hS : CatDominates S lam) :
    (springerFixedCopyOver ℂ lam part S).toSubmodule =
        Submodule.span ℂ (Set.range
          (fun T : StandardYoungTableau (YoungDiagram.ofPartition part) =>
            Ideal.Quotient.mk (springerIdeal ℂ lam)
              (rename (finCongr (YoungDiagram.card_ofPartition part))
                (higherSpechtPolynomial (R := ℂ) S T)))) ∧
      Representation.IsIrreducible (springerFixedCopyOver ℂ lam part S).toRepresentation ∧
      Nonempty (Representation.Equiv (partitionSpechtRepresentationOver ℂ part)
        (springerFixedCopyOver ℂ lam part S).toRepresentation) := by
  refine ⟨?_, ?_⟩
  · simpa only [springerFixedCopySpanOver] using
      (springerFixedCopyOver_toSubmodule ℂ lam part S)
  · exact corollary_8_1_springer_copy_irreducible (K := ℂ) lam part S hS
      (Or.inl (ringChar.eq_zero (R := ℂ)))

/-- Theorem 4.1: all allowed prefixes, descents, and multipliers are retained
by `GriffinIndex`, and the representatives below are exactly `E_eta F_T^S`. -/
theorem theorem_4_1_basis (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hlam : 0 < lam.card) (hheight : lam.colLen 0 ≤ s) :
    ∃ b : Basis (GriffinIndex n lam hk s) ℂ
        (PolynomialRing n ℂ ⧸ griffinIdeal ℂ n lam s),
      ∀ i, b i = Ideal.Quotient.mk (griffinIdeal ℂ n lam s)
        (rename (finCongr i.pair.card_eq)
            (higherSpechtPolynomial (R := ℂ) i.pair.left i.pair.right) *
          elementaryMultiplier n (n - lam.card) i.multiplier.rowLen) := by
  simpa only [IsSpecifiedBasis, griffinFamily, griffinPolynomial, pairPolynomial] using
    (HigherSpecht.theorem_4_1 ℂ n lam hk s hlam hheight)

/-- The multiplier contributes its actual partition size to the degree. -/
theorem theorem_4_1_degree {n : ℕ} {lam : YoungDiagram}
    {hk : lam.card ≤ n} {s : ℕ} (i : GriffinIndex n lam hk s) :
    (rename (finCongr i.pair.card_eq)
        (higherSpechtPolynomial (R := ℂ) i.pair.left i.pair.right) *
      elementaryMultiplier n (n - lam.card) i.multiplier.rowLen).IsHomogeneous
        (cochargeDegree i.pair.left + i.multiplier.card) := by
  simpa only [griffinPolynomial, pairPolynomial] using
    (griffinPolynomial_isHomogeneous (R := ℂ) i)

/-- The irreducible-copy clause of Theorem 4.1 concerns the span of those
same representatives while the right tableau varies. -/
theorem theorem_4_1_copies {n : ℕ} (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (part : n.Partition) (i : PartitionGriffinCopies n lam hk s part)
    (hheight : lam.colLen 0 ≤ s) :
    (griffinFixedCopyOver ℂ lam hk s part i).toSubmodule =
        Submodule.span ℂ (Set.range
          (fun T : StandardYoungTableau (YoungDiagram.ofPartition part) =>
            Ideal.Quotient.mk (griffinIdeal ℂ n lam s)
              (rename (finCongr (YoungDiagram.card_ofPartition part))
                  (higherSpechtPolynomial (R := ℂ) i.left T) *
                elementaryMultiplier n (n - lam.card) i.multiplier.rowLen))) ∧
      Representation.IsIrreducible (griffinFixedCopyOver ℂ lam hk s part i).toRepresentation ∧
      Nonempty (Representation.Equiv (partitionSpechtRepresentationOver ℂ part)
        (griffinFixedCopyOver ℂ lam hk s part i).toRepresentation) := by
  refine ⟨?_, ?_⟩
  · simpa only [griffinFixedCopySpanOver] using
      (griffinFixedCopyOver_toSubmodule ℂ lam hk s part i)
  · exact corollary_8_1_griffin_copy_irreducible (K := ℂ) lam hk s part i
      (Or.inl (ringChar.eq_zero (R := ℂ))) hheight

/-- Theorem 5.2: the canonical common vectors give the correct Specht shape,
degree, directness, and every allowed harmonic-space equality simultaneously.
The eligibility predicate and the Specht-copy predicate are expanded here. -/
theorem theorem_5_2_literal (n s : ℕ) (hn : 0 < n) (hs : 0 < s) :
    (∀ i : FiniteHarmonicIndex n s,
      (∃ phi : Representation.IntertwiningMap (YoungIdealRepresentation (K := ℂ) i.part)
          (polynomialRepresentation ℂ n),
        Function.Injective phi ∧
          LinearMap.range phi.toLinearMap = finiteCommonHarmonicCopy i) ∧
      finiteCommonHarmonicCopy i ≤
        homogeneousSubmodule (Fin n) ℂ (cochargeDegree i.left + i.multiplier.card)) ∧
    iSupIndep (finiteCommonHarmonicCopy (n := n) (s := s)) ∧
    ∀ (lam : YoungDiagram) (hk : lam.card ≤ n), lam.colLen 0 ≤ s →
      ordinaryHarmonics (griffinIdeal ℂ n lam s) =
        ⨆ i : {i : FiniteHarmonicIndex n s //
            i.multiplier.colLen 0 ≤ n - lam.card ∧
              CatDominates (prefixTableau i.left lam.card
                (by simpa only [YoungDiagram.card_ofPartition] using hk)) lam},
          finiteCommonHarmonicCopy i.val := by
  simpa only [IsSpechtPolynomialCopy, UnboundedHarmonicIndex.degree,
    UnboundedHarmonicIndex.eligible] using
    (HigherSpecht.theorem_5_2 n s hn hs)

/-- Theorem 6.6: the actual untruncated common vectors give all partitions,
including the empty partition, with the stated local finiteness by degree. -/
theorem theorem_6_6_literal (n : ℕ) :
    (∀ i : UnboundedHarmonicIndex n,
      (∃ phi : Representation.IntertwiningMap (YoungIdealRepresentation (K := ℂ) i.part)
          (polynomialRepresentation ℂ n),
        Function.Injective phi ∧
          LinearMap.range phi.toLinearMap = untruncatedCommonHarmonicCopy i) ∧
      untruncatedCommonHarmonicCopy i ≤
        homogeneousSubmodule (Fin n) ℂ (cochargeDegree i.left + i.multiplier.card)) ∧
    iSupIndep (untruncatedCommonHarmonicCopy (n := n)) ∧
    (∀ d : ℕ, Set.Finite {i : UnboundedHarmonicIndex n |
      cochargeDegree i.left + i.multiplier.card = d}) ∧
    ∀ (lam : YoungDiagram) (hk : lam.card ≤ n),
      ordinaryHarmonics (untruncatedIdeal ℂ n lam) =
        ⨆ i : {i : UnboundedHarmonicIndex n //
            i.multiplier.colLen 0 ≤ n - lam.card ∧
              CatDominates (prefixTableau i.left lam.card
                (by simpa only [YoungDiagram.card_ofPartition] using hk)) lam},
          untruncatedCommonHarmonicCopy i.val := by
  simpa only [IsSpechtPolynomialCopy, UnboundedHarmonicIndex.degree,
    UnboundedHarmonicIndex.eligible] using
    (HigherSpecht.theorem_6_6 n)

end HigherSpecht.FinalStatementAudit

-- Each command reports the transitive axioms of the corresponding literal
-- statement above, including the imported proof on which it depends.
#print axioms HigherSpecht.FinalStatementAudit.theorem_1_1_basis
#print axioms HigherSpecht.FinalStatementAudit.theorem_1_1_degree
#print axioms HigherSpecht.FinalStatementAudit.theorem_1_1_copies
#print axioms HigherSpecht.FinalStatementAudit.theorem_4_1_basis
#print axioms HigherSpecht.FinalStatementAudit.theorem_4_1_degree
#print axioms HigherSpecht.FinalStatementAudit.theorem_4_1_copies
#print axioms HigherSpecht.FinalStatementAudit.theorem_5_2_literal
#print axioms HigherSpecht.FinalStatementAudit.theorem_6_6_literal
end
end CanonicalSource44

section CanonicalSource45
/- Source: audit/RequiredAxioms.lean -/


/-!
The complete required endpoint inventory. Each command reports Lean's transitive
axiom closure. This is a final consumer; it does not add hypotheses or proof rules.
The companion required_scope.json records mathematical correspondence, not a
verification certificate. Only a successful checked run supplies that evidence.
-/

-- Theorem 1.1
#print axioms HigherSpecht.springer_basis_target
#print axioms HigherSpecht.corollary_8_1_springer_copy_irreducible
#print axioms HigherSpecht.springerFixedCopyOver_toSubmodule
#print axioms HigherSpecht.FinalStatementAudit.theorem_1_1_basis
#print axioms HigherSpecht.FinalStatementAudit.theorem_1_1_degree
#print axioms HigherSpecht.FinalStatementAudit.theorem_1_1_copies

-- Theorem 3.2
#print axioms HigherSpecht.theorem_3_2_prefix_offDiagonal
#print axioms HigherSpecht.theorem_3_2_diagonal
#print axioms HigherSpecht.theorem_3_2_diagonal_pos
#print axioms HigherSpecht.higherSpechtApolarFunctional_apply
#print axioms HigherSpecht.theorem_3_2_selected_entry
#print axioms SpechtSelectedPairingAudit.literal_entry
#print axioms HigherSpecht.theorem_3_2_selected_family
#print axioms SpechtSelectedPairingAudit.literal_triangular_matrix
#print axioms HigherSpecht.columnInsertionSteps
#print axioms HigherSpecht.columnInsertionSteps_empty
#print axioms HigherSpecht.columnInsertion_pending_nil
#print axioms HigherSpecht.columnInsertion
#print axioms HigherSpecht.columnInsertion_state
#print axioms HigherSpecht.labeledCatRun_complete_unique
#print axioms HigherSpecht.columnInsertion_agrees_with_completed_run
#print axioms HigherSpecht.columnInsertion_output
#print axioms HigherSpecht.columnInsertion_rearrangementWitness

-- Theorem 4.1
#print axioms HigherSpecht.theorem_4_1
#print axioms HigherSpecht.griffin_specifiedBasis
#print axioms HigherSpecht.corollary_8_1_griffin_copy_irreducible
#print axioms HigherSpecht.griffinFixedCopyOver_toSubmodule
#print axioms HigherSpecht.FinalStatementAudit.theorem_4_1_basis
#print axioms HigherSpecht.FinalStatementAudit.theorem_4_1_degree
#print axioms HigherSpecht.FinalStatementAudit.theorem_4_1_copies

-- Corollary 4.3
#print axioms HigherSpecht.corollary_4_3_on_admissible_multipliers
#print axioms HigherSpecht.isDominanceTriangularMultiplier_iff_strictExpansion
#print axioms HigherSpecht.corollary_4_3_monomial
#print axioms HigherSpecht.corollary_4_3_schur
#print axioms HigherSpecht.corollary_4_3_copy_on_admissible_multipliers
#print axioms SpechtAlternativeMultiplierAudit.corollary_4_3_alternativeCopy_literal

-- Theorem 5.2
#print axioms HigherSpecht.theorem_5_2
#print axioms HigherSpecht.FinalStatementAudit.theorem_5_2_literal
#print axioms HigherSpecht.finiteCommonHarmonicVectorWithTableau_covariant
#print axioms HigherSpecht.finiteCommonHarmonicCopyWithTableau_eq
#print axioms HigherSpecht.theorem_5_2_any_right_tableaux
#print axioms HigherSpecht.complexSpechtYoungImage_finrank
#print axioms HigherSpecht.complexYoungIdealSpechtEquiv
#print axioms HigherSpecht.complexYoungIdealRepresentation_isIrreducible
#print axioms HigherSpecht.isSpechtPolynomialCopy_iff_complexSpecht
#print axioms HigherSpecht.theorem_5_2_actual_specht

-- Corollary 5.3
#print axioms HigherSpecht.GriffinIdealExpression.harmonic_decomposition
#print axioms HigherSpecht.GriffinIdealExpression.corollary_5_3_basis
#print axioms HigherSpecht.GriffinIdealExpression.corollary_5_3_frobenius
#print axioms HigherSpecht.corollary_5_3_distributive
#print axioms HigherSpecht.GriffinIdealExpression.corollary_5_3_alternative_basis_onEligible
#print axioms HigherSpecht.GriffinIdealExpression.corollary_5_3_finiteSum_basis
#print axioms HigherSpecht.GriffinIdealExpression.corollary_5_3_finiteIntersection_basis
#print axioms SpechtFiniteFamilyAudit.corollary_5_3_finiteFamily_literal
#print axioms HigherSpecht.GriffinIdealExpression.corollary_5_3_alternative_copy_onEligible
#print axioms SpechtAlternativeMultiplierAudit.corollary_5_3_alternativeCopy_literal
#print axioms HigherSpecht.GriffinIdealExpression.corollary_5_3_specht_copy
#print axioms ExpressionSpechtCopyAudit.finite_expression_copy
#print axioms HigherSpecht.corollary_5_3_finite_family_specht_copies
#print axioms ExpressionSpechtCopyAudit.finite_nonempty_family_copies

-- Corollary 5.5
#print axioms HigherSpecht.springerCommonHarmonicCopy_isSpecht
#print axioms HigherSpecht.springerCommonHarmonicCopies_iSupIndep
#print axioms HigherSpecht.corollary_5_5_decomposition
#print axioms HigherSpecht.corollary_5_5_master
#print axioms HigherSpecht.griffinApolarWitness_full
#print axioms HigherSpecht.griffinWitnessAlpha_full
#print axioms HigherSpecht.griffinWitnessRejection_full
#print axioms HigherSpecht.springerCommonHarmonicVector_literal_formula
#print axioms HigherSpecht.springerCommonHarmonicVectorWithTableau_literal_formula
#print axioms HigherSpecht.springerCommonHarmonicCopyWithTableau_eq
#print axioms HigherSpecht.corollary_5_5_any_right_tableaux
#print axioms HigherSpecht.corollary_5_5_actual_specht

-- Corollary 5.6
#print axioms HigherSpecht.corollary_5_6_basis
#print axioms HigherSpecht.corollary_5_6_frobenius
#print axioms HigherSpecht.untruncatedIdeal_weakDominanceJoin
#print axioms HigherSpecht.dominates_weakDominanceJoin_iff
#print axioms HigherSpecht.finiteEligibility_weakDominanceJoin

-- Corollary 5.7
#print axioms HigherSpecht.commonPairingMatrix_inverse_triangular
#print axioms HigherSpecht.adaptedMasterPolynomial
#print axioms HigherSpecht.adaptedMasterPolynomial_isHomogeneous
#print axioms HigherSpecht.corollary_5_7_of_factorial_isUnit
#print axioms HigherSpecht.corollary_5_7_localized
#print axioms HigherSpecht.corollary_5_7_field
#print axioms HigherSpecht.corollary_5_7_localized_copy
#print axioms HigherSpecht.corollary_5_7_field_copy
#print axioms HigherSpecht.adaptedGriffinCopy_eq_span

-- Theorem 6.1
#print axioms HigherSpecht.theorem_6_1_basis_and_rank
#print axioms HigherSpecht.theorem_6_1_dimension_and_cohenMacaulay
#print axioms HigherSpecht.theorem_6_1_frobenius_series
#print axioms HigherSpecht.elementaryFrobeniusDenominator_isUnit
#print axioms HigherSpecht.character_untruncatedGradedPiece
#print axioms ParameterPrincipalStatementAudit.parameter_action
#print axioms ParameterPrincipalStatementAudit.theorem61_basis_rank
#print axioms ParameterPrincipalStatementAudit.theorem61_representative_degree
#print axioms ParameterPrincipalStatementAudit.theorem61_dimension_cm

-- Remark 6.2
#print axioms HigherSpecht.untruncated_specified_parameter_basis_of_factorial_isUnit
#print axioms HigherSpecht.remark_6_2_untruncated_characteristic
#print axioms HigherSpecht.remark_6_2_untruncated_localized

-- Proposition 6.3
#print axioms HigherSpecht.proposition_6_3
#print axioms HigherSpecht.proposition_6_3_eligibility
#print axioms HigherSpecht.proposition_6_3_frobenius
#print axioms HigherSpecht.proposition_6_3_frobenius_target
#print axioms HigherSpecht.proposition_6_3_flat_lifting
#print axioms HigherSpecht.specialFiberPrescribedLiftBasis_apply
#print axioms HigherSpecht.zeroParameterBaseChangeEquiv_one_tmul_mk
#print axioms HigherSpecht.proposition_6_3_frobenius_quotient

-- Corollary 6.5
#print axioms HigherSpecht.integralMonomialParameterBasis_of_basis
#print axioms HigherSpecht.integralMonomialParameterBasis_of_basis_apply
#print axioms HigherSpecht.untruncatedIntegralMonomialParameterBasis
#print axioms HigherSpecht.untruncatedMonomialParameterBasis
#print axioms HigherSpecht.untruncated_parameter_flat_allCoefficients
#print axioms HigherSpecht.corollary_6_5_allFields
#print axioms HigherSpecht.lemma_6_4_griffin_degree_integral
#print axioms SpechtIntegralHilbertAudit.integral_degree_basis
#print axioms HigherSpecht.griffinHilbertFunction_independent_field
#print axioms SpechtIntegralHilbertAudit.degreewise_field_independence
#print axioms HigherSpecht.griffinMonomialDegreeBasis
#print axioms ParameterPrincipalStatementAudit.corollary65_arbitrary_integral_monomial_lift
#print axioms ParameterPrincipalStatementAudit.corollary65_monomial_basis_all_rings
#print axioms ParameterPrincipalStatementAudit.corollary65_all_fields
#print axioms ParameterPrincipalStatementAudit.corollary65_flat_all_rings

-- Theorem 6.6
#print axioms HigherSpecht.theorem_6_6
#print axioms HigherSpecht.FinalStatementAudit.theorem_6_6_literal
#print axioms HigherSpecht.untruncatedCommonHarmonicVectorWithTableau_covariant
#print axioms HigherSpecht.untruncatedCommonHarmonicCopyWithTableau_eq
#print axioms HigherSpecht.theorem_6_6_any_right_tableaux
#print axioms HigherSpecht.theorem_6_6_actual_specht

-- Corollary 6.7
#print axioms HigherSpecht.corollary_6_7_distributive
#print axioms HigherSpecht.UntruncatedIdealExpression.corollary_6_7_basis
#print axioms HigherSpecht.UntruncatedIdealExpression.corollary_6_7_frobenius
#print axioms HigherSpecht.UntruncatedIdealExpression.corollary_6_7_parameters
#print axioms HigherSpecht.UntruncatedIdealExpression.parameter_algebraicIndependent
#print axioms HigherSpecht.UntruncatedIdealExpression.corollary_6_7_finiteSum_basis
#print axioms HigherSpecht.UntruncatedIdealExpression.corollary_6_7_finiteIntersection_basis
#print axioms SpechtFiniteFamilyAudit.corollary_6_7_finiteFamily_literal
#print axioms HigherSpecht.UntruncatedIdealExpression.finiteSum_allSize
#print axioms HigherSpecht.UntruncatedIdealExpression.finiteIntersection_allSize
#print axioms HigherSpecht.UntruncatedIdealExpression.corollary_6_7_specht_copy
#print axioms ExpressionSpechtCopyAudit.untruncated_expression_copy
#print axioms HigherSpecht.corollary_6_7_finite_family_specht_copies
#print axioms ExpressionSpechtCopyAudit.untruncated_finite_nonempty_family_copies

-- Theorem 7.1
#print axioms HigherSpecht.theorem_7_1_parameter_fiber
#print axioms HigherSpecht.theorem_7_1_split_fiber
#print axioms HigherSpecht.theorem_7_1_number_of_factors
#print axioms HigherSpecht.theorem_7_1_after_scalar_extension
#print axioms HigherSpecht.distinctRootTensorEquiv
#print axioms HigherSpecht.theorem_7_1_algebraicClosure
#print axioms HigherSpecht.theorem_7_1_algebraicClosure_number_of_factors
#print axioms ParameterPrincipalStatementAudit.theorem71_parameter_fiber
#print axioms ParameterPrincipalStatementAudit.theorem71_factor_count
#print axioms ParameterPrincipalStatementAudit.theorem71_after_field_extension
#print axioms ParameterPrincipalStatementAudit.theorem71_algebraic_closure

-- Proposition 7.2
#print axioms HigherSpecht.proposition_7_2_integral_trivialization
#print axioms HigherSpecht.proposition_7_2_integral_trivialization_permutation
#print axioms HigherSpecht.proposition_7_2_integral_induced_tensor
#print axioms HigherSpecht.proposition_7_2_after_field_baseChange
#print axioms HigherSpecht.proposition_7_2_after_field_baseChange_permutation
#print axioms HigherSpecht.proposition_7_2_after_field_baseChange_induced
#print axioms HigherSpecht.proposition_7_2_no_parameters_identity
#print axioms HigherSpecht.orderedRootTrivialization_assigned_coordinate
#print axioms HigherSpecht.proposition_7_2_integral_trivialization_coordinate
#print axioms HigherSpecht.proposition_7_2_after_field_baseChange_coordinate
#print axioms HigherSpecht.proposition_7_2_no_parameters_permutation
#print axioms SpechtOrderedRootZeroAudit.proposition_7_2_no_parameters_equivariant_identity_literal

-- Proposition 7.3
#print axioms HigherSpecht.proposition_7_3_primary_decomposition
#print axioms HigherSpecht.coordinateIdeal_incomparable
#print axioms HigherSpecht.untruncatedIdeal_radical_eq_coordinate_intersection
#print axioms HigherSpecht.proposition_7_3_generic_component_length
#print axioms HigherSpecht.proposition_7_3_multiplicities
#print axioms HigherSpecht.proposition_7_3_standard_graded_multiplicity

-- Corollary 7.4
#print axioms HigherSpecht.untruncated_isReduced_iff
#print axioms HigherSpecht.parameterFiber_geometricallyReduced_iff
#print axioms HigherSpecht.parameterFiber_geometricallyReduced_iff_polynomial
#print axioms HigherSpecht.parameterFiber_geometricallyReduced_iff_squarefree
#print axioms HigherSpecht.parameterPolynomial_separable_iff_geometric_squarefree
#print axioms HigherSpecht.parameter_etale_atPrime_iff_polynomial

-- Corollary 7.5
#print axioms HigherSpecht.corollary_7_5_regularity
#print axioms HigherSpecht.hasUntruncatedTorRegularity_iff
#print axioms HigherSpecht.corollary_7_5_tor_regularity
#print axioms HigherSpecht.corollary_7_5_tor_support
#print axioms SpechtHomologicalAudit.regularity_statement

-- Corollary 7.6
#print axioms HigherSpecht.corollary_7_6_canonical_module
#print axioms HigherSpecht.corollary_7_6_canonical_degree_and_type
#print axioms HigherSpecht.corollary_7_6_gorenstein_iff_enlargedShape
#print axioms HigherSpecht.corollary_7_6_gorenstein_iff
#print axioms HigherSpecht.corollary_7_6_completeIntersection_iff
#print axioms HigherSpecht.untruncatedIdeal_column_eq_elementaryTail
#print axioms HigherSpecht.elementaryTailSequence_isRegular
#print axioms HigherSpecht.untruncated_regularSequencePresentation_of_full_row
#print axioms HigherSpecht.corollary_7_6_gorenstein_iff_completeIntersection
#print axioms SpechtHomologicalAudit.springer_socle_statement
#print axioms SpechtHomologicalAudit.canonical_module_statement
#print axioms SpechtHomologicalAudit.gorenstein_statement
#print axioms SpechtHomologicalAudit.complete_intersection_statement
#print axioms SpechtHomologicalAudit.gorenstein_iff_complete_intersection

-- Corollary 8.1
#print axioms HigherSpecht.corollary_8_1_griffin_characteristic
#print axioms HigherSpecht.corollary_8_1_springer_characteristic
#print axioms HigherSpecht.corollary_8_1_griffin_copy_irreducible
#print axioms HigherSpecht.corollary_8_1_springer_copy_irreducible
#print axioms HigherSpecht.corollary_8_1_griffin_localized
#print axioms HigherSpecht.corollary_8_1_springer_localized
#print axioms HigherSpecht.griffinFixedCopyOver_toSubmodule
#print axioms HigherSpecht.corollary_8_1_griffin_characteristic_all_partitions
#print axioms HigherSpechtAudit.griffin_characteristic_all_partitions_statement
#print axioms HigherSpecht.springerFixedCopyOver_toSubmodule
#print axioms ParameterPrincipalStatementAudit.corollary81_griffin_iff
#print axioms ParameterPrincipalStatementAudit.corollary81_springer_iff
#print axioms ParameterPrincipalStatementAudit.corollary81_griffin_localized
#print axioms ParameterPrincipalStatementAudit.corollary81_springer_localized
#print axioms ParameterPrincipalStatementAudit.corollary81_griffin_copy
#print axioms ParameterPrincipalStatementAudit.corollary81_springer_copy
end CanonicalSource45
