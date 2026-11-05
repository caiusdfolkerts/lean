module

public import PaperVerification.HomogeneousRegularSequence
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# A full homogeneous regular sequence cuts out a finite quotient

The origin localization has one dimension per variable. A regular sequence of
that full length cuts its dimension to zero, so every coordinate is nilpotent
in the localized quotient. Homogeneous saturation then descends each actual
coordinate-power relation to the polynomial ring. This avoids claiming that
localization at the origin is globally faithfully flat.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open MvPolynomial RingTheory.Sequence IsLocalRing

namespace PaperVerification.HomogeneousLocalization

variable {K : Type*} [Field K] {n : ℕ}
local notation "P" => MvPolynomial (Fin n) K
local notation "L" => OriginLocalRing (K := K) (ι := Fin n)
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem ofList_ofFn_eq_span_range (f : Fin n → P) :
    Ideal.ofList (List.ofFn f) = Ideal.span (Set.range f) :=
  congrArg Ideal.span (Set.ext fun _ => List.mem_ofFn' f _)

/-- Each coordinate has an actual power in the parameter ideal. The sequence
has full length and is homogeneous of positive degrees for positive weights;
there is no finite-quotient hypothesis. -/
theorem variable_mem_radical_of_homogeneous_regular
    (w : Fin n → ℕ) (hw : ∀ i, 0 < w i)
    (f : Fin n → P) (degree : Fin n → ℕ)
    (hd : ∀ i, 0 < degree i)
    (hf : ∀ i, (f i).IsWeightedHomogeneous w (degree i))
    (hreg : IsWeaklyRegular P (List.ofFn f)) (i : Fin n) :
    X i ∈ (Ideal.span (Set.range f)).radical := by
  classical
  let I : Ideal P := Ideal.span (Set.range f)
  let a : P →+* L := algebraMap P L
  let J : Ideal L := I.map a
  have horigin : ∀ p ∈ List.ofFn f, p ∈ originIdeal (K := K) (ι := Fin n) := by
    intro p hp
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
    change constantCoeff (f j) = 0
    rw [constantCoeff_eq]
    exact (hf j).coeff_eq_zero 0 (by simpa using (hd j).ne)
  have hlocal : IsRegular L ((List.ofFn f).map a) :=
    hreg.isRegular_of_isLocalization_of_mem L
      (originIdeal (K := K) (ι := Fin n)) horigin
  have hJ : Ideal.ofList ((List.ofFn f).map a) = J := by
    rw [← Ideal.map_ofList, ofList_ofFn_eq_span_range]
  have hdim : ringKrullDim (L ⧸ J) + (n : WithBot ℕ∞) = (n : WithBot ℕ∞) := by
    have h := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular _ hlocal
    rw [hJ] at h
    simpa only [List.length_map, List.length_ofFn, originLocalRing_dimension,
      Fintype.card_fin] using h
  have hdim0 : ringKrullDim (L ⧸ J) = 0 := by
    apply (ENat.WithBot.add_natCast_cancel (c := n)).mp
    simpa only [zero_add] using hdim
  have hJle : J ≤ maximalIdeal L := by
    rw [← hJ]
    apply Ideal.span_le.mpr
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L
      (originIdeal (K := K) (ι := Fin n)) q).mpr (horigin q hq)
  have hJne : J ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal L).ne_top hJle
  letI : Nontrivial (L ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJne
  letI : IsLocalRing (L ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  letI : Ring.KrullDimLE 0 (L ⧸ J) :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hdim0
  letI : IsLocalHom (Ideal.Quotient.mk J) :=
    IsLocalHom.of_surjective (R := L) (S := L ⧸ J)
      (Ideal.Quotient.mk J) (Ideal.Quotient.mk_surjective (I := J))
  have hXi : a (X i) ∈ maximalIdeal L := by
    apply (IsLocalization.AtPrime.to_map_mem_maximal_iff L
      (originIdeal (K := K) (ι := Fin n)) (X i)).mpr
    simp only [mem_originIdeal, constantCoeff_X]
  have hquotXi : Ideal.Quotient.mk J (a (X i)) ∈ maximalIdeal (L ⧸ J) :=
    map_nonunit (R := L) (S := L ⧸ J) (Ideal.Quotient.mk J) (a (X i)) hXi
  have hnil : IsNilpotent (Ideal.Quotient.mk J (a (X i))) :=
    Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal.mpr hquotXi
  obtain ⟨e, he⟩ := hnil
  have hloc : a (X i ^ e) ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_pow] using he
  have hI : I.IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    apply Ideal.homogeneous_span
    rintro p ⟨j, rfl⟩
    exact ⟨degree j, hf j⟩
  apply Ideal.mem_radical_iff.mpr
  refine ⟨e, ?_⟩
  exact homogeneous_mem_of_localized w (fun j => (hw j).ne') I hI
    (X i ^ e) (e • w i) ((isWeightedHomogeneous_X K w i).pow e) hloc

/-- Coordinate powers in an ideal make the literal polynomial quotient a
finite module over the coefficient field. -/
theorem quotient_finite_of_variables_mem_radical
    (I : Ideal P) (hrad : ∀ i : Fin n, X i ∈ I.radical) :
    Module.Finite K (P ⧸ I) := by
  let q := Ideal.Quotient.mkₐ K I
  let v : Fin n → P ⧸ I := fun i => q (X i)
  have hv : ∀ i, IsIntegral K (v i) := by
    intro i
    obtain ⟨e, he⟩ := Ideal.mem_radical_iff.mp (hrad i)
    refine ⟨Polynomial.X ^ e, Polynomial.monic_X.pow e, ?_⟩
    change Polynomial.aeval (q (X i)) (Polynomial.X ^ e) = 0
    rw [map_pow, Polynomial.aeval_X, ← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr he
  have heval : MvPolynomial.aeval v = q := by
    ext i
    simp only [v, MvPolynomial.aeval_X]
  have hadjoin : Algebra.adjoin K (Set.range v) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval, heval]
    exact (AlgHom.range_eq_top _).mpr (Ideal.Quotient.mkₐ_surjective K I)
  have hfg := fg_adjoin_of_finite (Set.finite_range v) (fun z hz => by
    obtain ⟨i, rfl⟩ := hz
    exact hv i)
  rw [hadjoin] at hfg
  exact Module.Finite.of_fg_top (by simpa using hfg)

/-- The full homogeneous regular-sequence finiteness theorem, with every
weight and degree positive and no added isolated-zero or finite-length premise. -/
theorem homogeneous_regular_quotient_finite
    (w : Fin n → ℕ) (hw : ∀ i, 0 < w i)
    (f : Fin n → P) (degree : Fin n → ℕ)
    (hd : ∀ i, 0 < degree i)
    (hf : ∀ i, (f i).IsWeightedHomogeneous w (degree i))
    (hreg : IsWeaklyRegular P (List.ofFn f)) :
    Module.Finite K (P ⧸ Ideal.span (Set.range f)) :=
  quotient_finite_of_variables_mem_radical _
    (variable_mem_radical_of_homogeneous_regular w hw f degree hd hf hreg)

end PaperVerification.HomogeneousLocalization
