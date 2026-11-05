module

public import PaperVerification.HomogeneousNullstellensatz
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Descent of homogeneous systems of parameters along field extensions

Polynomial coefficient extension is faithfully flat because its defining square
is an actual algebraic pushout.  Consequently extension followed by contraction
preserves ideals and their radicals.  This allows the common-zero test to be
performed over an algebraic closure while regularity is concluded over the
original field, in particular over the rational numbers used in Theorem 4.1.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial RingTheory.Sequence

variable {K L σ : Type*} [Field K] [Field L] [Algebra K L]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Coefficient extension of polynomial rings is faithfully flat for every
field extension and every variable type. -/
theorem mvPolynomial_coefficientExtension_faithfullyFlat :
    Module.FaithfullyFlat (MvPolynomial σ K) (MvPolynomial σ L) := by
  exact Module.FaithfullyFlat.of_linearEquiv _ _
    (Algebra.IsPushout.equiv K (MvPolynomial σ K) L (MvPolynomial σ L)).symm.toLinearEquiv

/-- Radical membership descends along coefficient extension. -/
theorem radical_comap_map_coefficientExtension (I : Ideal (MvPolynomial σ K)) :
    ((I.map (MvPolynomial.map (algebraMap K L))).radical).comap
        (MvPolynomial.map (algebraMap K L)) = I.radical := by
  letI := mvPolynomial_coefficientExtension_faithfullyFlat (K := K) (L := L) (σ := σ)
  change ((I.map (algebraMap (MvPolynomial σ K) (MvPolynomial σ L))).radical).comap
    (algebraMap (MvPolynomial σ K) (MvPolynomial σ L)) = _
  rw [Ideal.comap_radical, Ideal.comap_map_eq_self_of_faithfullyFlat]

/-- A common-zero test over an algebraically closed extension yields a global
regular sequence in the original positively graded polynomial ring. -/
theorem homogeneous_parameters_regular_of_common_zero_extension
    [Fintype σ] [IsAlgClosed L]
    (w : σ → ℕ) (hw : ∀ i, w i ≠ 0)
    (rs : List (MvPolynomial σ K))
    (hhom : ∀ f ∈ rs, ∃ d, f.IsWeightedHomogeneous w d)
    (horigin : ∀ f ∈ rs, constantCoeff f = 0)
    (hzero : ∀ x : σ → L,
      (∀ f ∈ rs, MvPolynomial.eval₂ (algebraMap K L) x f = 0) → x = 0)
    (hlen : rs.length = Fintype.card σ) :
    IsWeaklyRegular (MvPolynomial σ K) rs := by
  let φ : MvPolynomial σ K →+* MvPolynomial σ L := MvPolynomial.map (algebraMap K L)
  have hradL : HomogeneousLocalization.originIdeal (K := L) (ι := σ) ≤
      (Ideal.map φ (Ideal.ofList rs)).radical := by
    apply HomogeneousLocalization.origin_le_radical_of_zeroLocus
    intro x hx
    apply hzero x
    intro f hf
    have hmem : φ f ∈ Ideal.map φ (Ideal.ofList rs) :=
      Ideal.mem_map_of_mem φ (Ideal.subset_span hf)
    have hz := hx (φ f) hmem
    simpa only [φ, MvPolynomial.aeval_eq_eval, MvPolynomial.eval_map] using hz
  have hradK : HomogeneousLocalization.originIdeal (K := K) (ι := σ) ≤
      (Ideal.ofList rs).radical := by
    intro f hf
    have hfl : φ f ∈ HomogeneousLocalization.originIdeal (K := L) (ι := σ) := by
      change constantCoeff (MvPolynomial.map (algebraMap K L) f) = 0
      rw [MvPolynomial.constantCoeff_map,
        (HomogeneousLocalization.mem_originIdeal f).mp hf, map_zero]
    have hm : f ∈ ((Ideal.map φ (Ideal.ofList rs)).radical).comap φ := hradL hfl
    simpa only [φ, radical_comap_map_coefficientExtension] using hm
  exact HomogeneousLocalization.homogeneous_parameters_regular w hw rs hhom horigin hradK hlen

end PaperVerification.AlternatingForms
