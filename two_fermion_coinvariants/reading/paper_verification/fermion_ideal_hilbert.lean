module

public import PaperVerification.FermionPolynomialHilbert
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Algebra.Bilinear

/-!
# Hilbert series of actual successive homogeneous ideal quotients

The maps are multiplication on the original polynomial quotient and the
canonical quotient map after adjoining one generator. Their exactness is
proved by membership in the sum of the old ideal and a principal ideal.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PaperVerification.GradedHilbert

open scoped BigOperators
open MvPolynomial

variable {K : Type*} [Field K] {n m : ℕ}

local notation "P" => MvPolynomial (Fin n) K

attribute [local instance] MvPolynomial.weightedGradedAlgebra

def idealQuotientGrading (w : Fin n → ℕ) (I : Ideal P)
    (hI : DirectSum.SetLike.IsHomogeneous (polynomialGrading (K := K) w).piece I) :
    TauCeti.InternalGrading K (P ⧸ I) ℕ :=
  (polynomialGrading w).quotient I hI

/-- Equality of the actual ideals identifies the Hilbert series, with the
homogeneity proofs transported together with their dependent quotient types. -/
theorem idealQuotient_series_congr (w : Fin n → ℕ) (I J : Ideal P)
    (hI : DirectSum.SetLike.IsHomogeneous (polynomialGrading (K := K) w).piece I)
    (hJ : DirectSum.SetLike.IsHomogeneous (polynomialGrading (K := K) w).piece J)
    (h : I=J) :
    series (idealQuotientGrading w I hI)=series (idealQuotientGrading w J hJ) := by
  subst J
  rfl

@[simp] theorem idealQuotientGrading_piece (w : Fin n → ℕ) (I : Ideal P)
    (hI : DirectSum.SetLike.IsHomogeneous (polynomialGrading (K := K) w).piece I) (e : ℕ) :
    (idealQuotientGrading w I hI).piece e =
      (weightedHomogeneousSubmodule K w e).map (I.mkQ.restrictScalars K) := by
  simp only [idealQuotientGrading, TauCeti.InternalGrading.quotient_piece,
    polynomialGrading_piece]

theorem idealQuotient_piece_finite (w : Fin n → ℕ) (hw : ∀ i, 0 < w i)
    (I : Ideal P)
    (hI : DirectSum.SetLike.IsHomogeneous (polynomialGrading (K := K) w).piece I) (e : ℕ) :
    Module.Finite K ((idealQuotientGrading w I hI).piece e) := by
  letI : Module.Finite K (weightedHomogeneousSubmodule K w e) :=
    Module.Finite.iff_fg.mpr
      (weightedHomogeneousSubmodule_fg K w (fun i ↦ (hw i).ne') e)
  rw [idealQuotientGrading_piece]
  infer_instance

/-- Multiplication by a literal polynomial class on the literal ideal quotient. -/
def quotientMultiplication (I : Ideal P) (a : P) : Module.End K (P ⧸ I) :=
  LinearMap.mul K (P ⧸ I) (Ideal.Quotient.mk I a)

@[simp] theorem quotientMultiplication_mk (I : Ideal P) (a x : P) :
    quotientMultiplication I a (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (a * x) :=
  (map_mul (Ideal.Quotient.mk I) a x).symm

theorem quotientMultiplication_injective (I : Ideal P) (a : P)
    (ha : IsSMulRegular (P ⧸ I) a) : Function.Injective (quotientMultiplication I a) := by
  change Function.Injective (fun z : P ⧸ I ↦ Ideal.Quotient.mk I a * z)
  change Function.Injective (fun z : P ⧸ I ↦ a • z) at ha
  have hsmul (z : P ⧸ I) : a • z=Ideal.Quotient.mk I a*z := by
    obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [←Ideal.Quotient.mk_eq_mk,←Submodule.Quotient.mk_smul]
    change (Submodule.Quotient.mk (a*x) : P ⧸ I)=_
    simp only [Ideal.Quotient.mk_eq_mk,map_mul]
  intro x y h
  apply ha
  change a • x = a • y
  rw [hsmul,hsmul]
  exact h

theorem quotientMultiplication_homogeneous (w : Fin n → ℕ) (I : Ideal P)
    (hI : DirectSum.SetLike.IsHomogeneous (polynomialGrading (K := K) w).piece I)
    (a : P) (d : ℕ) (ha : a.IsWeightedHomogeneous w d) :
    TauCeti.LinearMap.IsHomogeneous (quotientMultiplication I a)
      (idealQuotientGrading w I hI).piece (idealQuotientGrading w I hI).piece d := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro e z hz
  obtain ⟨x, hx, rfl⟩ := ((polynomialGrading w).mem_quotient_piece_iff I hI).mp hz
  rw [Ideal.Quotient.mk_eq_mk,quotientMultiplication_mk]
  apply (polynomialGrading w).mk_mem_quotient_piece I hI
  rw [polynomialGrading_piece, mem_weightedHomogeneousSubmodule]
  rw [polynomialGrading_piece, mem_weightedHomogeneousSubmodule] at hx
  simpa only [Nat.add_comm d e] using ha.mul hx

theorem ideal_factor_homogeneous (w : Fin n → ℕ) (I J : Ideal P)
    (hI : DirectSum.SetLike.IsHomogeneous (polynomialGrading (K := K) w).piece I)
    (hJ : DirectSum.SetLike.IsHomogeneous (polynomialGrading (K := K) w).piece J)
    (hIJ : I ≤ J) :
    TauCeti.LinearMap.IsHomogeneous (Ideal.Quotient.factorₐ K hIJ).toLinearMap
      (idealQuotientGrading w I hI).piece (idealQuotientGrading w J hJ).piece 0 := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro e z hz
  obtain ⟨x, hx, rfl⟩ := ((polynomialGrading w).mem_quotient_piece_iff I hI).mp hz
  rw [add_zero, AlgHom.toLinearMap_apply, Ideal.Quotient.mk_eq_mk,
    Ideal.Quotient.factorₐ_apply_mk, idealQuotientGrading_piece]
  refine ⟨x, ?_, ?_⟩
  · change x ∈ weightedHomogeneousSubmodule K w e
    rw [polynomialGrading_piece] at hx
    exact hx
  · exact Ideal.Quotient.mk_eq_mk x

/-- Exactness is proved on representatives, with no additional colon or
flatness assumption. -/
theorem ideal_factor_kernel_eq_multiplication_range (I J : Ideal P) (a : P)
    (hJ : J = I ⊔ Ideal.span {a}) (hIJ : I ≤ J) :
    LinearMap.ker (Ideal.Quotient.factorₐ K hIJ).toLinearMap =
      LinearMap.range (quotientMultiplication I a) := by
  ext z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  constructor
  · intro hx
    have hxJ : x ∈ J := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      exact hx
    rw [hJ] at hxJ
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hxJ
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hv
    refine ⟨Ideal.Quotient.mk I c, ?_⟩
    rw [quotientMultiplication_mk, ← huv, map_add,
      Ideal.Quotient.eq_zero_iff_mem.mpr hu, zero_add]
  · rintro ⟨y, hy⟩
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [quotientMultiplication_mk] at hy
    rw [← hy]
    change Ideal.Quotient.mk J (a * v) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [hJ]
    exact Ideal.mul_mem_right v _
      ((show Ideal.span {a} ≤ I ⊔ Ideal.span {a} from le_sup_right)
        (Ideal.subset_span rfl))

/-- Adjoining one homogeneous generator regular modulo the preceding ideal
gives the complete Hilbert-series step on actual quotient spaces. -/
theorem ideal_quotient_regular_step (w : Fin n → ℕ) (hw : ∀ i, 0 < w i)
    (I J : Ideal P)
    (hI : DirectSum.SetLike.IsHomogeneous (polynomialGrading (K := K) w).piece I)
    (hJ : DirectSum.SetLike.IsHomogeneous (polynomialGrading (K := K) w).piece J)
    (a : P) (d : ℕ) (ha : a.IsWeightedHomogeneous w d)
    (hregular : IsSMulRegular (P ⧸ I) a) (hadd : J = I ⊔ Ideal.span {a}) :
    series (idealQuotientGrading w J hJ) =
      (1 - PowerSeries.X ^ d) * series (idealQuotientGrading w I hI) := by
  have hIJ : I ≤ J := by rw [hadd]; exact le_sup_left
  exact exact_hilbert_series
    (idealQuotientGrading w I hI) (quotientMultiplication I a) d
    (quotientMultiplication_homogeneous w I hI a d ha)
    (idealQuotientGrading w J hJ) (Ideal.Quotient.factorₐ K hIJ).toLinearMap
    (ideal_factor_homogeneous w I J hI hJ hIJ)
    (idealQuotient_piece_finite w hw I hI)
    (quotientMultiplication_injective I a hregular)
    (Ideal.Quotient.factor_surjective hIJ)
    (ideal_factor_kernel_eq_multiplication_range I J a hadd hIJ)

def prefixIdeal (f : Fin m → P) (k : ℕ) : Ideal P :=
  Ideal.ofList ((List.ofFn f).take k)

@[simp] theorem prefixIdeal_zero (f : Fin m → P) : prefixIdeal f 0 = ⊥ := by
  simp only [prefixIdeal, List.take_zero, Ideal.ofList_nil]

theorem prefixIdeal_succ (f : Fin m → P) (k : ℕ) (hk : k < m) :
    prefixIdeal f (k + 1) = prefixIdeal f k ⊔ Ideal.span {f ⟨k, hk⟩} := by
  have hk' : k < (List.ofFn f).length := by simpa using hk
  simp only [prefixIdeal, List.take_succ_eq_append_getElem hk',
    Ideal.ofList_append, Ideal.ofList_singleton, List.getElem_ofFn]

theorem prefixIdeal_homogeneous (w : Fin n → ℕ) (f : Fin m → P) (degree : Fin m → ℕ)
    (hhom : ∀ i, (f i).IsWeightedHomogeneous w (degree i)) (k : ℕ) :
    DirectSum.SetLike.IsHomogeneous (polynomialGrading (K := K) w).piece (prefixIdeal f k) := by
  change DirectSum.SetLike.IsHomogeneous
    (TauCeti.InternalGrading.ofDecomposition (weightedHomogeneousSubmodule K w)).piece
    ((prefixIdeal f k).restrictScalars K)
  rw [TauCeti.InternalGrading.isHomogeneous_ofDecomposition_piece_iff]
  change (prefixIdeal f k).IsHomogeneous (weightedHomogeneousSubmodule K w)
  apply Ideal.homogeneous_span
  intro a ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_take ha)
  exact ⟨degree i, hhom i⟩

def prefixGrading (w : Fin n → ℕ) (f : Fin m → P) (degree : Fin m → ℕ)
    (hhom : ∀ i, (f i).IsWeightedHomogeneous w (degree i)) (k : ℕ) :
    TauCeti.InternalGrading K (P ⧸ prefixIdeal f k) ℕ :=
  idealQuotientGrading w (prefixIdeal f k) (prefixIdeal_homogeneous w f degree hhom k)

theorem prefix_regular (f : Fin m → P)
    (hregular : RingTheory.Sequence.IsWeaklyRegular P (List.ofFn f))
    (k : ℕ) (hk : k < m) : IsSMulRegular (P ⧸ prefixIdeal f k) (f ⟨k, hk⟩) := by
  have h := hregular.regular_mod_prev k (by simpa using hk)
  have heq : (Ideal.ofList ((List.ofFn f).take k) • (⊤ : Submodule P P)) =
      Ideal.ofList ((List.ofFn f).take k) :=
    (Ideal.smul_eq_mul _ _).trans (Ideal.mul_top _)
  rw [heq, List.getElem_ofFn] at h
  exact h

theorem prefix_series_step (w : Fin n → ℕ) (hw : ∀ i, 0 < w i)
    (f : Fin m → P) (degree : Fin m → ℕ)
    (hhom : ∀ i, (f i).IsWeightedHomogeneous w (degree i))
    (hregular : RingTheory.Sequence.IsWeaklyRegular P (List.ofFn f))
    (k : ℕ) (hk : k < m) :
    series (prefixGrading w f degree hhom (k + 1)) =
      (1 - PowerSeries.X ^ degree ⟨k, hk⟩) * series (prefixGrading w f degree hhom k) :=
  ideal_quotient_regular_step w hw _ _
    (prefixIdeal_homogeneous w f degree hhom k)
    (prefixIdeal_homogeneous w f degree hhom (k + 1))
    (f ⟨k, hk⟩) (degree ⟨k, hk⟩) (hhom ⟨k, hk⟩)
    (prefix_regular f hregular k hk) (prefixIdeal_succ f k hk)

theorem idealQuotient_bot_series (w : Fin n → ℕ) (hw : ∀ i, 0 < w i)
    (hbot : DirectSum.SetLike.IsHomogeneous
      (polynomialGrading (K := K) w).piece (⊥ : Ideal P)) :
    series (idealQuotientGrading w ⊥ hbot) = series (polynomialGrading (K := K) w) := by
  let q : P →ₗ[K] P ⧸ (⊥ : Ideal P) := (⊥ : Ideal P).mkQ.restrictScalars K
  have hq : TauCeti.LinearMap.IsHomogeneous q (polynomialGrading w).piece
      (idealQuotientGrading w ⊥ hbot).piece 0 := by
    apply TauCeti.LinearMap.isHomogeneous_def.mpr
    intro e p hp
    change (Submodule.Quotient.mk p : P ⧸ (⊥ : Ideal P)) ∈
      (idealQuotientGrading w ⊥ hbot).piece (e + 0)
    rw [add_zero, idealQuotientGrading_piece]
    refine ⟨p,?_,rfl⟩
    change p ∈ weightedHomogeneousSubmodule K w e
    rw [polynomialGrading_piece] at hp
    exact hp
  have hsurj : Function.Surjective q := by
    intro z
    obtain ⟨p,hp⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨p, (Ideal.Quotient.mk_eq_mk p).trans hp⟩
  have hker : LinearMap.ker q = ⊥ := by
    simp only [q, LinearMap.ker_restrictScalars, Submodule.ker_mkQ,
      Submodule.restrictScalars_bot]
  ext e
  have h := surjection_piece_dimension_add_kernel_intersection (polynomialGrading w)
    (idealQuotientGrading w ⊥ hbot) q hq (polynomial_piece_finite w hw) hsurj e
  rw [hker, bot_inf_eq, finrank_bot, add_zero] at h
  simp only [coeff_series]
  exact congrArg (fun z : ℕ ↦ (z : ℤ)) h.symm

def prefixNumerator (degree : Fin m → ℕ) (k : ℕ) : PowerSeries ℤ :=
  ((List.ofFn fun i ↦ (1 - PowerSeries.X ^ degree i : PowerSeries ℤ)).take k).prod

@[simp] theorem prefixNumerator_zero (degree : Fin m → ℕ) : prefixNumerator degree 0 = 1 := by
  simp [prefixNumerator]

theorem prefixNumerator_succ (degree : Fin m → ℕ) (k : ℕ) (hk : k < m) :
    prefixNumerator degree (k + 1) =
      prefixNumerator degree k * (1 - PowerSeries.X ^ degree ⟨k, hk⟩) := by
  have hk' : k < (List.ofFn degree).length := by simpa using hk
  simp only [prefixNumerator, List.take_succ_eq_append_getElem
    (show k < (List.ofFn fun i ↦ (1 - PowerSeries.X ^ degree i : PowerSeries ℤ)).length by
      simpa using hk), List.prod_append, List.prod_singleton, List.getElem_ofFn]

theorem prefix_series_formula (w : Fin n → ℕ) (hw : ∀ i, 0 < w i)
    (f : Fin m → P) (degree : Fin m → ℕ)
    (hhom : ∀ i, (f i).IsWeightedHomogeneous w (degree i))
    (hregular : RingTheory.Sequence.IsWeaklyRegular P (List.ofFn f))
    (k : ℕ) (hk : k ≤ m) :
    series (prefixGrading w f degree hhom k) =
      prefixNumerator degree k * series (polynomialGrading (K := K) w) := by
  revert hk
  induction k with
  | zero =>
    intro hk
    rw [prefixNumerator_zero,one_mul]
    have hbot := prefixIdeal_homogeneous w f degree hhom 0
    rw [prefixIdeal_zero] at hbot
    exact (idealQuotient_series_congr w (prefixIdeal f 0) ⊥
      (prefixIdeal_homogeneous w f degree hhom 0) hbot (prefixIdeal_zero f)).trans
        (idealQuotient_bot_series w hw hbot)
  | succ k ih =>
    intro hk
    rw [prefix_series_step w hw f degree hhom hregular k (by omega),
      ih (by omega), prefixNumerator_succ degree k (by omega)]
    rw [mul_assoc, mul_left_comm]

theorem prefixIdeal_full (f : Fin m → P) : prefixIdeal f m = Ideal.span (Set.range f) := by
  have ht : (List.ofFn f).take m = List.ofFn f := List.take_of_length_le (by simp)
  have hs : {p | p ∈ List.ofFn f} = Set.range f := Set.ext fun _ ↦ List.mem_ofFn
  rw [prefixIdeal, ht, Ideal.ofList, hs]

theorem prefixNumerator_full (degree : Fin m → ℕ) :
    prefixNumerator degree m = ∏ i, (1 - PowerSeries.X ^ degree i) := by
  have ht : (List.ofFn fun i ↦ (1 - PowerSeries.X ^ degree i : PowerSeries ℤ)).take m =
      List.ofFn fun i ↦ (1 - PowerSeries.X ^ degree i : PowerSeries ℤ) :=
    List.take_of_length_le (by simp only [List.length_ofFn, le_refl])
  rw [prefixNumerator, ht, List.prod_ofFn]

theorem familyIdeal_homogeneous (w : Fin n → ℕ) (f : Fin m → P) (degree : Fin m → ℕ)
    (hhom : ∀ i, (f i).IsWeightedHomogeneous w (degree i)) :
    DirectSum.SetLike.IsHomogeneous (polynomialGrading (K := K) w).piece
      (Ideal.span (Set.range f)) := by
  rw [← prefixIdeal_full]
  exact prefixIdeal_homogeneous w f degree hhom m

/-- The grading of the literal quotient by the full homogeneous family. -/
def familyGrading (w : Fin n → ℕ) (f : Fin m → P) (degree : Fin m → ℕ)
    (hhom : ∀ i, (f i).IsWeightedHomogeneous w (degree i)) :
    TauCeti.InternalGrading K (P ⧸ Ideal.span (Set.range f)) ℕ :=
  idealQuotientGrading w (Ideal.span (Set.range f)) (familyIdeal_homogeneous w f degree hhom)

/-- The complete regular-sequence factorization, valid for any number of
homogeneous generators. -/
theorem regular_family_series (w : Fin n → ℕ) (hw : ∀ i, 0 < w i)
    (f : Fin m → P) (degree : Fin m → ℕ)
    (hhom : ∀ i, (f i).IsWeightedHomogeneous w (degree i))
    (hregular : RingTheory.Sequence.IsWeaklyRegular P (List.ofFn f)) :
    series (familyGrading w f degree hhom) =
      (∏ i, (1 - PowerSeries.X ^ degree i)) * series (polynomialGrading (K := K) w) := by
  have h := prefix_series_formula w hw f degree hhom hregular m le_rfl
  unfold prefixGrading at h
  have he := idealQuotient_series_congr w (prefixIdeal f m) (Ideal.span (Set.range f))
    (prefixIdeal_homogeneous w f degree hhom m)
    (familyIdeal_homogeneous w f degree hhom) (prefixIdeal_full f)
  rw [he] at h
  simpa only [prefixNumerator_full, familyGrading] using h

/-- Hilbert's complete-intersection identity with actual graded quotient
components and no assumed Hilbert formula. -/
theorem regular_family_hilbert_identity (w : Fin n → ℕ) (hw : ∀ i, 0 < w i)
    (f : Fin m → P) (degree : Fin m → ℕ)
    (hhom : ∀ i, (f i).IsWeightedHomogeneous w (degree i))
    (hregular : RingTheory.Sequence.IsWeaklyRegular P (List.ofFn f)) :
    (∏ i, (1 - PowerSeries.X ^ w i)) * series (familyGrading w f degree hhom) =
      ∏ j, (1 - PowerSeries.X ^ degree j) := by
  rw [regular_family_series w hw f degree hhom hregular, mul_left_comm,
    denominator_mul_polynomial_series w hw, mul_one]

end PaperVerification.GradedHilbert
