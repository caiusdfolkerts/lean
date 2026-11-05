module

public import Mathlib.RingTheory.ReesAlgebra
import all Mathlib.RingTheory.ReesAlgebra
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import all Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import all Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Polynomial.Laurent
import all Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import all Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.AlgebraicGeometry.AffineScheme
import all Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.RingHom.StandardSmooth
import all Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import all Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.Etale.Kaehler
import all Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.LinearAlgebra.Dimension.Constructions
import all Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.AlgebraicGeometry.FunctionField
import all Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import all Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.FinTrdeg
import all Mathlib.FieldTheory.FinTrdeg
public import Mathlib.RingTheory.Etale.Field
import all Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
import all Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import all Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.RingTheory.Kaehler.Polynomial
import all Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.FieldTheory.SeparablyGenerated
import all Mathlib.FieldTheory.SeparablyGenerated
public import Mathlib.LinearAlgebra.TensorProduct.Basis
import all Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import all Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Dimension.Finite
import all Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.Kaehler.Basic
import all Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
import all Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Algebraic.Integral
import all Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Ideal.Over
import all Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Localization.FractionRing
import all Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Ideal
import all Mathlib.RingTheory.Localization.Ideal
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import all Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
import all Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import Mathlib.AlgebraicGeometry.Noetherian
import all Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import all Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

@[expose] public section ComponentSource_0
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.Cone -/

/-! # Cone -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.Cone.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the affine normal cone in its Rees presentation

For an ideal I of R, the normal-cone algebra is R[It] / I R[It].
The base map and augmentation are induced by constants and evaluation at
degree zero. Their composite is the identity, giving the cone's canonical
closed zero section over Spec(R/I).

This is the affine algebraic construction. The degreewise associated-graded
comparison, gluing over a general closed immersion, deformation space, and
specialization on Chow groups are separate steps still needed for refined Gysin.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

variable {R : Type u} [CommRing R]

/-- Extension of I to its actual Rees algebra. -/
def normalConeIdeal (I : Ideal R) : Ideal (reesAlgebra I) :=
  I.map (algebraMap R (reesAlgebra I))

/-- The standard Rees presentation of the affine normal-cone algebra. -/
abbrev NormalConeRing (I : Ideal R) := (reesAlgebra I) ⧸ normalConeIdeal I

/-- Constants induce the structure map from the closed base R/I. -/
def normalConeBaseMap (I : Ideal R) : R ⧸ I →+* NormalConeRing I :=
  Ideal.Quotient.lift I
    ((Ideal.Quotient.mk (normalConeIdeal I)).comp (algebraMap R (reesAlgebra I)))
    (fun _ hr => Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_map_of_mem (algebraMap R (reesAlgebra I)) hr))

@[simp]
theorem normalConeBaseMap_mk (I : Ideal R) (r : R) :
    normalConeBaseMap I (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk (normalConeIdeal I) (algebraMap R (reesAlgebra I) r) := rfl

/-- Degree-zero evaluation on the Rees subalgebra. -/
def reesAugmentation (I : Ideal R) : reesAlgebra I →+* R :=
  Polynomial.constantCoeff.comp (reesAlgebra I).val.toRingHom

@[simp]
theorem reesAugmentation_algebraMap (I : Ideal R) (r : R) :
    reesAugmentation I (algebraMap R (reesAlgebra I) r) = r := by
  simp [reesAugmentation]

/-- The Rees augmentation carries the extended ideal into I. -/
theorem normalConeIdeal_le_augmentation_ker (I : Ideal R) :
    normalConeIdeal I ≤
      RingHom.ker ((Ideal.Quotient.mk I).comp (reesAugmentation I)) := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro r hr
  change Ideal.Quotient.mk I (reesAugmentation I (algebraMap R (reesAlgebra I) r)) = 0
  rw [reesAugmentation_algebraMap]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hr

/-- Augmentation of the normal-cone algebra to the closed base. -/
def normalConeAugmentation (I : Ideal R) : NormalConeRing I →+* R ⧸ I :=
  Ideal.Quotient.lift (normalConeIdeal I)
    ((Ideal.Quotient.mk I).comp (reesAugmentation I))
    (fun _ hr => normalConeIdeal_le_augmentation_ker I hr)

@[simp]
theorem normalConeAugmentation_mk (I : Ideal R) (a : reesAlgebra I) :
    normalConeAugmentation I (Ideal.Quotient.mk (normalConeIdeal I) a) =
      Ideal.Quotient.mk I (reesAugmentation I a) := rfl

/-- Constants followed by augmentation are the identity on the base ring. -/
theorem normalConeAugmentation_comp_base (I : Ideal R) :
    (normalConeAugmentation I).comp (normalConeBaseMap I) = RingHom.id (R ⧸ I) := by
  apply Ideal.Quotient.ringHom_ext
  ext r
  change Ideal.Quotient.mk I (reesAugmentation I (algebraMap R (reesAlgebra I) r)) =
    Ideal.Quotient.mk I r
  rw [reesAugmentation_algebraMap]

theorem normalConeBaseMap_injective (I : Ideal R) :
    Function.Injective (normalConeBaseMap I) :=
  (show Function.LeftInverse (normalConeAugmentation I) (normalConeBaseMap I) from
    fun r => DFunLike.congr_fun (normalConeAugmentation_comp_base I) r).injective

theorem normalConeAugmentation_surjective (I : Ideal R) :
    Function.Surjective (normalConeAugmentation I) :=
  (show Function.RightInverse (normalConeBaseMap I) (normalConeAugmentation I) from
    fun r => DFunLike.congr_fun (normalConeAugmentation_comp_base I) r).surjective

/-- The actual affine scheme of the normal cone. -/
def affineNormalCone (I : Ideal R) : Scheme := Spec (CommRingCat.of (NormalConeRing I))

/-- The cone's projection to the closed subscheme Spec(R/I). -/
def affineNormalConeProjection (I : Ideal R) :
    affineNormalCone I ⟶ Spec (CommRingCat.of (R ⧸ I)) :=
  Spec.map (CommRingCat.ofHom (normalConeBaseMap I))

/-- The zero section defined by the actual augmentation. -/
def affineNormalConeZeroSection (I : Ideal R) :
    Spec (CommRingCat.of (R ⧸ I)) ⟶ affineNormalCone I :=
  Spec.map (CommRingCat.ofHom (normalConeAugmentation I))

theorem affineNormalConeZeroSection_projection (I : Ideal R) :
    affineNormalConeZeroSection I ≫ affineNormalConeProjection I =
      𝟙 (Spec (CommRingCat.of (R ⧸ I))) := by
  let b : CommRingCat.of (R ⧸ I) ⟶ CommRingCat.of (NormalConeRing I) :=
    CommRingCat.ofHom (normalConeBaseMap I)
  let a : CommRingCat.of (NormalConeRing I) ⟶ CommRingCat.of (R ⧸ I) :=
    CommRingCat.ofHom (normalConeAugmentation I)
  have h : b ≫ a = 𝟙 (CommRingCat.of (R ⧸ I)) := by
    apply CommRingCat.hom_ext
    exact normalConeAugmentation_comp_base I
  exact (Spec.map_comp b a).symm.trans
    ((congrArg Spec.map h).trans (Spec.map_id _))

/-- The canonical zero section is a closed immersion. -/
instance affineNormalConeZeroSection_isClosedImmersion (I : Ideal R) :
    IsClosedImmersion (affineNormalConeZeroSection I) :=
  IsClosedImmersion.spec_of_surjective _ (normalConeAugmentation_surjective I)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.Cone.BundleCycles
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.Cone"

@[expose] public section ComponentSource_1
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Iff -/

/-! # Iff -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Iff.BundleCycles

noncomputable section

/-!
# LineBundleCycles: affine deformation to the normal cone

The extended Rees algebra is the subalgebra R[t,I/t] of R[t,t⁻¹]. Its
coefficient at exponent n lies in I^max(-n,0). This construction retains the
actual ideal and supplies the deformation parameter, rather than postulating
a specialization map on cycles.
-/

open LaurentPolynomial

universe u
variable {R : Type u} [CommRing R]

/-- The extended Rees algebra, with positive parameter t. -/
def deformationAlgebra (I : Ideal R) : Subalgebra R (LaurentPolynomial R) where
  carrier := {p | ∀ n : ℤ, p.coeff n ∈ I ^ (-n).toNat}
  mul_mem' {p q} hp hq n := by
    rw [AddMonoidAlgebra.coeff_mul_apply_left]
    apply Ideal.sum_mem
    intro m hm
    have h := Ideal.mul_mem_mul (hp m) (hq (-m + n))
    rw [← pow_add] at h
    exact Ideal.pow_le_pow_right (by omega) h
  one_mem' n := by
    change (AddMonoidAlgebra.single 0 (1 : R)).coeff n ∈ _
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs with h
    · subst n
      simp
    · exact Ideal.zero_mem _
  add_mem' hp hq n := Ideal.add_mem _ (hp n) (hq n)
  zero_mem' _ := Ideal.zero_mem _
  algebraMap_mem' r n := by
    change (AddMonoidAlgebra.single 0 r).coeff n ∈ _
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs with h
    · subst n
      simp
    · exact Ideal.zero_mem _

theorem mem_deformationAlgebra_iff (I : Ideal R) (p : LaurentPolynomial R) :
    p ∈ deformationAlgebra I ↔ ∀ n : ℤ, p.coeff n ∈ I ^ (-n).toNat := Iff.rfl

/-- Exact coefficient condition for a Laurent monomial. -/
theorem single_mem_deformationAlgebra_iff (I : Ideal R) (n : ℤ) (r : R) :
    AddMonoidAlgebra.single n r ∈ deformationAlgebra I ↔ r ∈ I ^ (-n).toNat := by
  classical
  constructor
  · intro h
    simpa only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] using h n
  · intro h m
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs with hnm
    · simpa [← hnm] using h
    · exact Ideal.zero_mem _

/-- A monomial together with its ideal-power membership. -/
def deformationMonomial (I : Ideal R) (n : ℤ) (r : R)
    (hr : r ∈ I ^ (-n).toNat) : deformationAlgebra I :=
  ⟨AddMonoidAlgebra.single n r,
    (single_mem_deformationAlgebra_iff I n r).mpr hr⟩

/-- The regular parameter t of the deformation. -/
def deformationParameter (I : Ideal R) : deformationAlgebra I :=
  deformationMonomial I 1 1 (by simp)

@[simp]
theorem deformationParameter_val (I : Ideal R) :
    (deformationParameter I : LaurentPolynomial R) = T 1 := rfl

/-- Multiplication by t shifts the Laurent coefficient by one. -/
theorem deformationParameter_mul_coeff (I : Ideal R) (p : deformationAlgebra I) (n : ℤ) :
    ((deformationParameter I * p : deformationAlgebra I) : LaurentPolynomial R).coeff n =
      (p : LaurentPolynomial R).coeff (n - 1) := by
  change (AddMonoidAlgebra.single 1 1 * p.val).coeff n = _
  simp only [AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
  congr 1
  omega

/-- The parameter is a non-zero-divisor, including over rings with zero divisors. -/
theorem deformationParameter_regular (I : Ideal R) :
    deformationParameter I ∈ nonZeroDivisors (deformationAlgebra I) := by
  have hregular : ∀ p : deformationAlgebra I, deformationParameter I * p = 0 → p = 0 := by
    intro p hp
    apply Subtype.ext
    ext n
    have h := congrArg (fun q : deformationAlgebra I => q.val.coeff (n + 1)) hp
    rw [deformationParameter_mul_coeff] at h
    simpa using h
  exact mem_nonZeroDivisors_iff.mpr ⟨hregular, fun p hp => hregular p (by rwa [mul_comm])⟩

/-- The ideal of the special fiber t = 0. -/
def deformationSpecialIdeal (I : Ideal R) : Ideal (deformationAlgebra I) :=
  Ideal.span {deformationParameter I}

/-- Dividing a Laurent polynomial by t increases the required ideal power
by one at every nonpositive exponent. -/
theorem mem_deformationSpecialIdeal_iff (I : Ideal R) (p : deformationAlgebra I) :
    p ∈ deformationSpecialIdeal I ↔
      ∀ n : ℤ, p.val.coeff n ∈ I ^ (1 - n).toNat := by
  rw [deformationSpecialIdeal, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨q, rfl⟩ n
    rw [deformationParameter_mul_coeff]
    convert q.property (n - 1) using 1
    congr 2
    omega
  · intro hp
    let q : deformationAlgebra I := ⟨T (-1) * p.val, fun n => by
      change (AddMonoidAlgebra.single (-1) 1 * p.val).coeff n ∈ _
      rw [AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
      convert hp (-(-1) + n) using 1
      congr 2
      omega⟩
    refine ⟨q, Subtype.ext ?_⟩
    change p.val = T 1 * (T (-1) * p.val)
    rw [← mul_assoc, ← T_add]
    simp only [Int.reduceAdd, T_zero, one_mul]

/-- Coefficients of an ordinary polynomial after Laurent extension. -/
theorem toLaurent_coeff_nat (p : Polynomial R) (n : ℕ) :
    p.toLaurent.coeff (n : ℤ) = p.coeff n := by
  rw [coeff_toLaurent]
  exact Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective _ n

theorem toLaurent_coeff_neg (p : Polynomial R) (n : ℤ) (hn : n < 0) :
    p.toLaurent.coeff n = 0 := by
  rw [coeff_toLaurent]
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨m, hm⟩
  have : (m : ℤ) = n := hm
  omega

/-- The Rees algebra embeds in the deformation by reversing the exponent:
a degree-n coefficient a maps to a/t^n. -/
def reesToDeformation (I : Ideal R) : reesAlgebra I →ₐ[R] deformationAlgebra I :=
  ((invert.toAlgHom.comp Polynomial.toLaurentAlg).comp (reesAlgebra I).val).codRestrict
    (deformationAlgebra I) (fun p n => by
      change (invert p.val.toLaurent).coeff n ∈ _
      rw [invert_apply]
      by_cases hn : 0 ≤ -n
      · have he : ((-n).toNat : ℤ) = -n := Int.toNat_of_nonneg hn
        rw [← he, toLaurent_coeff_nat]
        exact p.property _
      · rw [toLaurent_coeff_neg _ _ (by omega)]
        exact Ideal.zero_mem _)

@[simp]
theorem reesToDeformation_val (I : Ideal R) (p : reesAlgebra I) :
    (reesToDeformation I p).val = invert p.val.toLaurent := rfl

theorem reesToDeformation_coeff (I : Ideal R) (p : reesAlgebra I) (n : ℕ) :
    (reesToDeformation I p).val.coeff (-(n : ℤ)) = p.val.coeff n := by
  rw [reesToDeformation_val, invert_apply, neg_neg, toLaurent_coeff_nat]

theorem reesToDeformation_coeff_pos (I : Ideal R) (p : reesAlgebra I)
    (n : ℤ) (hn : 0 < n) : (reesToDeformation I p).val.coeff n = 0 := by
  rw [reesToDeformation_val, invert_apply, toLaurent_coeff_neg _ _ (by omega)]

theorem reesToDeformation_injective (I : Ideal R) :
    Function.Injective (reesToDeformation I) := by
  intro p q h
  apply Subtype.ext
  exact Polynomial.toLaurent_injective
    (invert.injective (congrArg Subtype.val h))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Iff.BundleCycles
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Iff"

@[expose] public section ComponentSource_2
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFiber -/

/-! # Generic Fiber -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFiber.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the punctured affine deformation

Inverting the deformation parameter identifies R[t,I/t][t⁻¹] with
R[t,t⁻¹]. The proof clears negative exponents of an arbitrary Laurent
polynomial, so the identification applies to every ideal in every base ring.
-/

open LaurentPolynomial

universe u
variable {R : Type u} [CommRing R]

/-- Ordinary polynomials belong to the extended Rees algebra. -/
theorem polynomial_mem_deformationAlgebra (I : Ideal R) (p : Polynomial R) :
    p.toLaurent ∈ Deformation.Iff.BundleCycles.deformationAlgebra I := by
  intro n
  by_cases hn : n < 0
  · rw [Deformation.Iff.BundleCycles.toLaurent_coeff_neg p n hn]
    exact Ideal.zero_mem _
  · have he : (-n).toNat = 0 := by omega
    simp [he]

/-- Inclusion of the parameter polynomial ring into the deformation. -/
def polynomialToDeformation (I : Ideal R) : Polynomial R →ₐ[R] Deformation.Iff.BundleCycles.deformationAlgebra I :=
  Polynomial.toLaurentAlg.codRestrict (Deformation.Iff.BundleCycles.deformationAlgebra I)
    (polynomial_mem_deformationAlgebra I)

@[simp]
theorem polynomialToDeformation_val (I : Ideal R) (p : Polynomial R) :
    (polynomialToDeformation I p).val = p.toLaurent := rfl

@[simp]
theorem polynomialToDeformation_X (I : Ideal R) :
    polynomialToDeformation I Polynomial.X = Deformation.Iff.BundleCycles.deformationParameter I := by
  apply Subtype.ext
  exact Polynomial.toLaurent_X

theorem deformationParameter_pow_val (I : Ideal R) (n : ℕ) :
    ((Deformation.Iff.BundleCycles.deformationParameter I ^ n : Deformation.Iff.BundleCycles.deformationAlgebra I) : LaurentPolynomial R) = T (n : ℤ) := by
  change (T 1 : LaurentPolynomial R) ^ n = _
  rw [T_pow, mul_one]

/-- Laurent polynomials are precisely the localization of the deformation
algebra away from its regular parameter. -/
instance deformation_isLocalization (I : Ideal R) :
    IsLocalization.Away (Deformation.Iff.BundleCycles.deformationParameter I) (LaurentPolynomial R) where
  map_units := by
    rintro ⟨p, ⟨n, rfl⟩⟩
    change IsUnit ((Deformation.Iff.BundleCycles.deformationParameter I ^ n : Deformation.Iff.BundleCycles.deformationAlgebra I) : LaurentPolynomial R)
    rw [deformationParameter_pow_val]
    exact isUnit_T _
  surj p := by
    obtain ⟨n, q, hq⟩ := exists_T_pow p
    refine ⟨(polynomialToDeformation I q,
      ⟨Deformation.Iff.BundleCycles.deformationParameter I ^ n, ⟨n, rfl⟩⟩), ?_⟩
    change p * ((Deformation.Iff.BundleCycles.deformationParameter I ^ n : Deformation.Iff.BundleCycles.deformationAlgebra I) : LaurentPolynomial R) =
      (polynomialToDeformation I q).val
    rw [deformationParameter_pow_val, polynomialToDeformation_val, hq]
  exists_of_eq := by
    intro p q hpq
    have he : p = q := Subtype.ext hpq
    exact ⟨1, by rw [he]⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFiber.BundleCycles
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFiber"

@[expose] public section ComponentSource_3
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.FiniteType -/

/-! # Finite Type -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.FiniteType.BundleCycles

noncomputable section

/-!
# LineBundleCycles: finite type of the deformation algebra

The extended Rees algebra is generated by the reversed ordinary Rees
algebra and the parameter t. Finite generation of I therefore implies
finite type of R[t,I/t], and a Noetherian base gives a Noetherian
deformation ring. This is needed to form finite divisors on the deformation.
-/

open LaurentPolynomial
open scoped BigOperators

universe u
variable {R : Type u} [CommRing R]

/-- Ordinary Rees polynomials with their exponent reversed in the Laurent ring. -/
def reesLaurentMap (I : Ideal R) : reesAlgebra I →ₐ[R] LaurentPolynomial R :=
  (Iff.BundleCycles.deformationAlgebra I).val.comp (Iff.BundleCycles.reesToDeformation I)

/-- The extended Rees algebra is generated by the reversed Rees algebra and t. -/
theorem deformationAlgebra_eq_sup (I : Ideal R) :
    Iff.BundleCycles.deformationAlgebra I = (reesLaurentMap I).range ⊔ Algebra.adjoin R {T 1} := by
  classical
  apply le_antisymm
  · intro p hp
    rw [← AddMonoidAlgebra.sum_coeff_single p]
    apply Subalgebra.sum_mem
    intro n hn
    by_cases hneg : n ≤ 0
    · apply le_sup_left (a := (reesLaurentMap I).range) (b := Algebra.adjoin R {T 1})
      let q : reesAlgebra I :=
        ⟨Polynomial.monomial (-n).toNat (p.coeff n), reesAlgebra.monomial_mem.mpr (hp n)⟩
      refine ⟨q, ?_⟩
      change invert (Polynomial.toLaurent (Polynomial.monomial (-n).toNat (p.coeff n))) = _
      rw [Polynomial.toLaurent_C_mul_T, map_mul, invert_C, invert_T, ← single_eq_C_mul_T]
      congr 1
      omega
    · apply le_sup_right (a := (reesLaurentMap I).range) (b := Algebra.adjoin R {T 1})
      rw [single_eq_C_mul_T]
      apply Subalgebra.mul_mem
      · exact Subalgebra.algebraMap_mem _ _
      · have he : n = (n.toNat : ℤ) := by omega
        rw [he, ← mul_one (n.toNat : ℤ), ← T_pow]
        exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton (T 1))) _
  · apply sup_le
    · rintro _ ⟨p, rfl⟩
      exact (Iff.BundleCycles.reesToDeformation I p).property
    · apply Algebra.adjoin_le
      rintro _ ⟨rfl⟩
      exact (Iff.BundleCycles.deformationParameter I).property

/-- Finite generation of the center ideal suffices for finite generation of
the full deformation algebra. -/
theorem deformationAlgebra_fg (I : Ideal R) (hI : I.FG) : (Iff.BundleCycles.deformationAlgebra I).FG := by
  rw [deformationAlgebra_eq_sup]
  apply Subalgebra.FG.sup
  · have h := Subalgebra.FG.map (reesLaurentMap I) ((reesAlgebra I).fg_top.mpr (reesAlgebra.fg hI))
    simpa only [Algebra.map_top] using h
  · exact Subalgebra.fg_def.mpr ⟨{T 1}, Set.finite_singleton _, rfl⟩

theorem deformationAlgebra_finiteType (I : Ideal R) (hI : I.FG) :
    Algebra.FiniteType R (Iff.BundleCycles.deformationAlgebra I) :=
  (Iff.BundleCycles.deformationAlgebra I).fg_iff_finiteType.mp (deformationAlgebra_fg I hI)

instance deformationAlgebra_noetherian (I : Ideal R) [IsNoetherianRing R] :
    IsNoetherianRing (Iff.BundleCycles.deformationAlgebra I) := by
  have := deformationAlgebra_finiteType I (IsNoetherian.noetherian I)
  exact Algebra.FiniteType.isNoetherianRing R _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.FiniteType.BundleCycles
end ComponentSource_3

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.FiniteType"

@[expose] public section ComponentSource_4
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Transcendence -/

/-! # Transcendence -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Transcendence.BundleCycles

noncomputable section

/-!
# LineBundleCycles: transcendence degree of the deformation algebra

Both the polynomial ring and the extended-Rees algebra localize to the
same Laurent ring. These faithful algebraic extensions show that the
deformation adds exactly one transcendental parameter.
-/

universe u
variable (R : Type u) [CommRing R] [IsDomain R]

/-- Laurent polynomials have exactly one transcendental parameter over their coefficient domain. -/
theorem laurentPolynomial_trdeg : Algebra.trdeg R (LaurentPolynomial R) = 1 := by
  let : IsScalarTower R (Polynomial R) (LaurentPolynomial R) :=
    IsScalarTower.of_algebraMap_eq (fun r => (Polynomial.toLaurent_C r).symm)
  let : FaithfulSMul (Polynomial R) (LaurentPolynomial R) :=
    (faithfulSMul_iff_algebraMap_injective (Polynomial R) (LaurentPolynomial R)).mpr
      Polynomial.toLaurent_injective
  let : Algebra.IsAlgebraic (Polynomial R) (LaurentPolynomial R) :=
    IsLocalization.isAlgebraic (LaurentPolynomial R) (Submonoid.powers (Polynomial.X : Polynomial R))
  have h := trdeg_add_eq R (Polynomial R) (A := LaurentPolynomial R)
  simp only [Polynomial.trdeg_of_isDomain, trdeg_eq_zero, add_zero] at h
  exact h.symm

variable {R} (I : Ideal R)

/-- The extended-Rees algebra adds precisely one transcendental parameter. -/
theorem deformationAlgebra_trdeg : Algebra.trdeg R (Iff.BundleCycles.deformationAlgebra I) = 1 := by
  let : Algebra.IsAlgebraic (Iff.BundleCycles.deformationAlgebra I) (LaurentPolynomial R) :=
    IsLocalization.isAlgebraic (LaurentPolynomial R) (Submonoid.powers (Iff.BundleCycles.deformationParameter I))
  have h := trdeg_add_eq R (Iff.BundleCycles.deformationAlgebra I) (A := LaurentPolynomial R)
  simp only [trdeg_eq_zero, add_zero] at h
  exact h.trans (laurentPolynomial_trdeg R)

variable (k : Type u) [Field k] [Algebra k R]

/-- The coefficient-field action on the deformation is induced by the actual constants map. -/
abbrev deformationScalarAlgebra : Algebra k (Iff.BundleCycles.deformationAlgebra I) :=
  Algebra.compHom (Iff.BundleCycles.deformationAlgebra I) (algebraMap k R)

omit [IsDomain R] in
theorem deformationScalar_isScalarTower :
    letI := deformationScalarAlgebra I k
    IsScalarTower k R (Iff.BundleCycles.deformationAlgebra I) := by
  let := deformationScalarAlgebra I k
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Over the original coefficient field, the actual deformation adds one to transcendence degree. -/
theorem deformationAlgebra_trdeg_base :
    letI := deformationScalarAlgebra I k
    Algebra.trdeg k (Iff.BundleCycles.deformationAlgebra I) = Algebra.trdeg k R + 1 := by
  let := deformationScalarAlgebra I k
  have : IsScalarTower k R (Iff.BundleCycles.deformationAlgebra I) := deformationScalar_isScalarTower I k
  have h := trdeg_add_eq k R (A := Iff.BundleCycles.deformationAlgebra I)
  rw [deformationAlgebra_trdeg I] at h
  exact h.symm

/-- Finite type makes the same formula exact in the natural-number dimension grading. -/
theorem deformationAlgebra_trdeg_toNat [Algebra.FiniteType k R] :
    letI := deformationScalarAlgebra I k
    (Algebra.trdeg k (Iff.BundleCycles.deformationAlgebra I)).toNat = (Algebra.trdeg k R).toNat + 1 := by
  let := deformationScalarAlgebra I k
  have hfin : Algebra.trdeg k R < Cardinal.aleph0 := trdeg_lt_aleph0_of_finiteType
  rw [deformationAlgebra_trdeg_base I k, Cardinal.toNat_add hfin (by simp)]
  simp

omit [IsDomain R] in
/-- Finite-type coefficients and a finitely generated center give a finite-type deformation over the field. -/
theorem deformationAlgebra_finiteType_base [Algebra.FiniteType k R] (hI : I.FG) :
    letI := deformationScalarAlgebra I k
    Algebra.FiniteType k (Iff.BundleCycles.deformationAlgebra I) := by
  let := deformationScalarAlgebra I k
  have : IsScalarTower k R (Iff.BundleCycles.deformationAlgebra I) := deformationScalar_isScalarTower I k
  have : Algebra.FiniteType R (Iff.BundleCycles.deformationAlgebra I) := Deformation.FiniteType.BundleCycles.deformationAlgebra_finiteType I hI
  exact Algebra.FiniteType.trans (S := R) inferInstance inferInstance

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Transcendence.BundleCycles
end ComponentSource_4

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Transcendence"

@[expose] public section ComponentSource_5
/- Original module: OAI.AlgebraicGeometry.Foundations.Scheme.SpecScalarTransport -/

/-! # Spec Scalar Transport -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.SpecScalarTransport

noncomputable section

/-!
# Transport from global functions on Spec to the actual scalar ring

A morphism to `Spec K` induces a map from `Γ(Spec K, ⊤)` on each open's
sections. Composing with the canonical, proved inverse `K → Γ(Spec K, ⊤)`
gives the intended scalar structure. Standard smooth relative dimension is
unchanged, and the resulting affine structure morphism agrees with the
restriction of the original scheme morphism.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [CommRing K] {X : Scheme.{u}}

/-- The actual scalar homomorphism on sections of a scheme over `Spec K`. -/
def specSectionScalarMap (f : X ⟶ Spec (.of K)) (U : X.Opens) : K →+* Γ(X, U) :=
  (f.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom

/-- The `K`-algebra structure induced by the actual structure morphism. -/
abbrev specSectionScalarAlgebra (f : X ⟶ Spec (.of K)) (U : X.Opens) :
    Algebra K Γ(X, U) :=
  (specSectionScalarMap f U).toAlgebra

/-- Replacing `Γ(Spec K, ⊤)` by `K` through its canonical isomorphism preserves
standard smoothness with its exact relative dimension. -/
theorem specSectionScalarMap_standardSmooth_iff (d : ℕ)
    (f : X ⟶ Spec (.of K)) (U : X.Opens) :
    RingHom.IsStandardSmoothOfRelativeDimension d (specSectionScalarMap f U) ↔
      RingHom.IsStandardSmoothOfRelativeDimension d (f.appLE ⊤ U le_top).hom := by
  exact (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := d)).cancel_left_isIso
    (Scheme.ΓSpecIso (.of K)).inv (f.appLE ⊤ U le_top)

/-- The same transport stated directly for the two explicit algebra structures. -/
theorem specSectionScalarAlgebra_standardSmooth_iff (d : ℕ)
    (f : X ⟶ Spec (.of K)) (U : X.Opens) :
    letI := (f.appLE ⊤ U le_top).hom.toAlgebra
    letI := specSectionScalarAlgebra f U
    Algebra.IsStandardSmoothOfRelativeDimension d K Γ(X, U) ↔
      Algebra.IsStandardSmoothOfRelativeDimension d Γ(Spec (.of K), ⊤) Γ(X, U) := by
  exact specSectionScalarMap_standardSmooth_iff d f U

/-- A standard smooth chart over the global functions of `Spec K` is therefore
standard smooth of the same dimension over the intended scalar ring. -/
theorem specSectionScalarAlgebra_standardSmooth (d : ℕ)
    (f : X ⟶ Spec (.of K)) (U : X.Opens)
    (h : RingHom.IsStandardSmoothOfRelativeDimension d (f.appLE ⊤ U le_top).hom) :
    letI := specSectionScalarAlgebra f U
    Algebra.IsStandardSmoothOfRelativeDimension d K Γ(X, U) :=
  (specSectionScalarMap_standardSmooth_iff d f U).mpr h

/-- On an actual affine open, the transported scalar algebra's structural
morphism is exactly the original structural morphism restricted to that open. -/
theorem specSectionScalarMap_fromSpec (f : X ⟶ Spec (.of K))
    (U : X.Opens) (hU : IsAffineOpen U) :
    Spec.map (CommRingCat.ofHom (specSectionScalarMap f U)) = hU.fromSpec ≫ f := by
  simpa only [specSectionScalarMap, CommRingCat.ofHom_comp, Spec.map_comp,
    CommRingCat.ofHom_hom, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] using
      (IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (.of K))) hU le_top)

end

end OAI.AlgebraicGeometry.Foundations.Scheme.SpecScalarTransport
end ComponentSource_5

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Foundations.Scheme.SpecScalarTransport"

@[expose] public section ComponentSource_6
/- Original module: OAI.AlgebraicGeometry.Foundations.Scheme.DifferentialRankLocalization -/

/-! # Differential Rank Localization -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.DifferentialRankLocalization.Algebraic

noncomputable section

/-!
# Presentation dimensions measured in a common localization

The dimension of a submersive presentation can be computed after a nonzero
formally étale extension. In particular, affine charts of an integral scheme
can be compared in their common function field without presupposing their
dimensions are equal.
-/

open scoped TensorProduct

universe u v w t z

variable {R : Type u} {S : Type v} {T : Type w}
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable [Nontrivial S] [Nontrivial T]
variable {ι : Type t} {σ : Type z} [Finite ι] [Finite σ]

/-- The dimension of a submersive presentation is the rank of the differential
module after a nonzero formally étale extension. -/
theorem submersive_dimension_eq_differential_finrank
    [Algebra.FormallyEtale S T] (P : Algebra.SubmersivePresentation R S ι σ) :
    P.dimension = Module.finrank T Ω[T⁄R] := by
  let : Module.Free S Ω[S⁄R] := P.free_kaehlerDifferential
  have hdim : Module.finrank S Ω[S⁄R] = P.dimension :=
    Module.finrank_eq_of_rank_eq P.rank_kaehlerDifferential
  calc
    P.dimension = Module.finrank S Ω[S⁄R] := hdim.symm
    _ = Module.finrank T (T ⊗[S] Ω[S⁄R]) := Module.finrank_baseChange.symm
    _ = Module.finrank T Ω[T⁄R] :=
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).finrank_eq

/-- The preceding computation for any nonzero localization, including the
function field of a domain. -/
theorem submersive_dimension_eq_localized_differential_finrank
    (W : Submonoid S) [IsLocalization W T]
    (P : Algebra.SubmersivePresentation R S ι σ) :
    P.dimension = Module.finrank T Ω[T⁄R] := by
  let : Algebra.FormallyEtale S T := Algebra.FormallyEtale.of_isLocalization W
  exact submersive_dimension_eq_differential_finrank P

/-- Specialization to a common fraction field. -/
theorem submersive_dimension_eq_fraction_differential_finrank
    [IsFractionRing S T]
    (P : Algebra.SubmersivePresentation R S ι σ) :
    P.dimension = Module.finrank T Ω[T⁄R] :=
  submersive_dimension_eq_localized_differential_finrank (nonZeroDivisors S) P

/-- Standard smoothness itself therefore has the relative dimension measured
in any common fraction ring, independently of the chosen presentation. -/
theorem standardSmooth_has_fraction_differential_dimension
    [IsFractionRing S T] [Algebra.IsStandardSmooth R S] :
    Algebra.IsStandardSmoothOfRelativeDimension (Module.finrank T Ω[T⁄R]) R S := by
  obtain ⟨ι', σ', hσ, hι, ⟨P⟩⟩ := Algebra.IsStandardSmooth.out (R := R) (S := S)
  let : Finite σ' := hσ
  let : Finite ι' := hι
  exact P.isStandardSmoothOfRelativeDimension
    (submersive_dimension_eq_fraction_differential_finrank (T := T) P)

end

end OAI.AlgebraicGeometry.Foundations.Scheme.DifferentialRankLocalization.Algebraic
end ComponentSource_6

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Foundations.Scheme.DifferentialRankLocalization"

@[expose] public section ComponentSource_7
/- Original module: OAI.AlgebraicGeometry.Betti.AffineDimension -/

/-! # Affine Dimension -/

namespace OAI.AlgebraicGeometry.Betti.AffineDimension.Realization

noncomputable section

/-!
# One function-field dimension for the affine charts of an integral scheme

The algebra structures are induced by the actual structure morphism, section
restriction, and germ maps. Their compatibility is proved from the sheaf germ
identity. Consequently standard smooth presentations on different nonempty
affine opens have a common dimension: the rank of differentials of the same
function field over the same base ring.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u v w

variable {X Y : Scheme.{u}}

/-- Restriction of the structure morphism on sections to an arbitrary source open. -/
def sectionBaseMap (f : X ⟶ Y) (U : X.Opens) : Γ(Y, ⊤) ⟶ Γ(X, U) :=
  f.appLE ⊤ U le_top

/-- The actual base-ring algebra structure on the sections of a source open. -/
abbrev sectionBaseAlgebra (f : X ⟶ Y) (U : X.Opens) :
    Algebra Γ(Y, ⊤) Γ(X, U) :=
  (sectionBaseMap f U).hom.toAlgebra

variable [IrreducibleSpace X]

/-- The structure morphism followed by the germ at the generic point. -/
def functionFieldBaseMap (f : X ⟶ Y) : Γ(Y, ⊤) ⟶ X.functionField :=
  f.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) (by trivial)

/-- The actual base-ring algebra structure on the function field. -/
abbrev functionFieldBaseAlgebra (f : X ⟶ Y) :
    Algebra Γ(Y, ⊤) X.functionField :=
  (functionFieldBaseMap f).hom.toAlgebra

/-- Restricting to a nonempty open does not change the germ of a base section. -/
theorem sectionBaseMap_germ (f : X ⟶ Y) (U : X.Opens) [Nonempty U] :
    sectionBaseMap f U ≫ X.germToFunctionField U = functionFieldBaseMap f := by
  dsimp only [sectionBaseMap, functionFieldBaseMap, Scheme.Hom.appLE,
    Scheme.germToFunctionField]
  rw [Category.assoc, TopCat.Presheaf.germ_res]
  congr 1

/-- The source-open and function-field algebra structures form the required
scalar tower; this is proved, rather than included as an assumption. -/
theorem functionFieldBase_isScalarTower (f : X ⟶ Y) (U : X.Opens) [Nonempty U] :
    letI := sectionBaseAlgebra f U
    letI := functionFieldBaseAlgebra f
    IsScalarTower Γ(Y, ⊤) Γ(X, U) X.functionField := by
  let := sectionBaseAlgebra f U
  let := functionFieldBaseAlgebra f
  apply IsScalarTower.of_algebraMap_eq'
  change (functionFieldBaseMap f).hom =
    (X.germToFunctionField U).hom.comp (sectionBaseMap f U).hom
  exact congrArg CommRingCat.Hom.hom (sectionBaseMap_germ f U).symm

variable [IsIntegral X]

/-- The common dimension recorded in the differentials of the actual function
field, with its structure-morphism algebra structure. -/
def functionFieldDifferentialDimension (f : X ⟶ Y) : ℕ :=
  letI := functionFieldBaseAlgebra f
  Module.finrank X.functionField Ω[X.functionField⁄Γ(Y, ⊤)]

/-- A genuine standard smooth affine presentation has the dimension of the
same function-field differential space, independently of the chosen open. -/
theorem affinePresentation_dimension (f : X ⟶ Y) (U : X.Opens) [Nonempty U]
    (hU : IsAffineOpen U) (ι : Type v) (σ : Type w) [Finite ι] [Finite σ] :
    letI := sectionBaseAlgebra f U
    ∀ P : Algebra.SubmersivePresentation Γ(Y, ⊤) Γ(X, U) ι σ,
      P.dimension = functionFieldDifferentialDimension f := by
  let := sectionBaseAlgebra f U
  let := functionFieldBaseAlgebra f
  let := functionFieldBase_isScalarTower f U
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  intro P
  exact Foundations.Scheme.DifferentialRankLocalization.Algebraic.submersive_dimension_eq_fraction_differential_finrank
    (T := X.functionField) P

end

end OAI.AlgebraicGeometry.Betti.AffineDimension.Realization
end ComponentSource_7

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Betti.AffineDimension"

@[expose] public section ComponentSource_8
/- Original module: OAI.AlgebraicGeometry.Foundations.Scheme.FunctionFieldScalar -/

/-! # Function Field Scalar -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.FunctionFieldScalar

noncomputable section

/-!
# The canonical scalar structure on a scheme's function field

For an irreducible scheme over `Spec K`, scalar constants enter its function
field through the actual global-sections map and the germ at the generic point.
The compatibility with sections of every nonempty open is proved from the
sheaf restriction/germ identity.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (K : Type u) [CommRing K]

/-- The established identification of scalars with global functions on `Spec K`. -/
def specGlobalScalarEquiv : K ≃+* Γ(Spec (.of K), ⊤) :=
  (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv

@[simp]
theorem specGlobalScalarEquiv_toRingHom :
    (specGlobalScalarEquiv K).toRingHom = (Scheme.ΓSpecIso (.of K)).inv.hom := rfl

/-- The actual scalar algebra structure on global functions of `Spec K`. -/
abbrev specGlobalScalarAlgebra : Algebra K Γ(Spec (.of K), ⊤) :=
  (Scheme.ΓSpecIso (.of K)).inv.hom.toAlgebra

variable {K} {X : Scheme.{u}} [IrreducibleSpace X]

/-- Scalar constants mapped by the structure morphism and then by the generic germ. -/
def functionFieldScalarMap (f : X ⟶ Spec (.of K)) : K →+* X.functionField :=
  (Betti.AffineDimension.Realization.functionFieldBaseMap f).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom

/-- The canonical `K`-algebra structure on the actual function field of `X`. -/
abbrev functionFieldScalarAlgebra (f : X ⟶ Spec (.of K)) : Algebra K X.functionField :=
  (functionFieldScalarMap f).toAlgebra

/-- This map is explicitly the structure-map pullback followed by the generic germ. -/
@[simp]
theorem functionFieldScalarMap_apply (f : X ⟶ Spec (.of K)) (c : K) :
    functionFieldScalarMap f c =
      X.presheaf.germ ⊤ (genericPoint X) (by trivial)
        (f.appTop ((Scheme.ΓSpecIso (.of K)).inv c)) := rfl

/-- Restricting a scalar section to a nonempty open before taking its generic germ
produces the same element of the function field. -/
theorem specSectionScalarMap_germ (f : X ⟶ Spec (.of K))
    (U : X.Opens) [Nonempty U] :
    (X.germToFunctionField U).hom.comp (SpecScalarTransport.specSectionScalarMap f U) =
      functionFieldScalarMap f := by
  exact congrArg
    (fun g : Γ(Spec (.of K), ⊤) ⟶ X.functionField =>
      g.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)
    (Betti.AffineDimension.Realization.sectionBaseMap_germ f U)

/-- Canonical scalar constants, sections, and the function field form a scalar tower. -/
theorem functionFieldScalar_isScalarTower (f : X ⟶ Spec (.of K))
    (U : X.Opens) [Nonempty U] :
    letI := SpecScalarTransport.specSectionScalarAlgebra f U
    letI := functionFieldScalarAlgebra f
    IsScalarTower K Γ(X, U) X.functionField := by
  let := SpecScalarTransport.specSectionScalarAlgebra f U
  let := functionFieldScalarAlgebra f
  apply IsScalarTower.of_algebraMap_eq'
  exact (specSectionScalarMap_germ f U).symm

/-- The scalar algebra is compatible with the original global-sections base algebra
used in the affine common-dimension theorem. -/
theorem functionFieldBaseScalar_isScalarTower (f : X ⟶ Spec (.of K)) :
    letI := specGlobalScalarAlgebra K
    letI := Betti.AffineDimension.Realization.functionFieldBaseAlgebra f
    letI := functionFieldScalarAlgebra f
    IsScalarTower K Γ(Spec (.of K), ⊤) X.functionField := by
  let := specGlobalScalarAlgebra K
  let := Betti.AffineDimension.Realization.functionFieldBaseAlgebra f
  let := functionFieldScalarAlgebra f
  apply IsScalarTower.of_algebraMap_eq'
  rfl

/-- The base map in this tower is a proved ring isomorphism, hence surjective. -/
theorem specGlobalScalarAlgebra_surjective :
    letI := specGlobalScalarAlgebra K
    Function.Surjective (algebraMap K Γ(Spec (.of K), ⊤)) := by
  exact (specGlobalScalarEquiv K).surjective

end

end OAI.AlgebraicGeometry.Foundations.Scheme.FunctionFieldScalar
end ComponentSource_8

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Foundations.Scheme.FunctionFieldScalar"

@[expose] public section ComponentSource_9
/- Original module: OAI.AlgebraicGeometry.Foundations.Scheme.FunctionFieldFiniteType -/

/-! # Function Field Finite Type -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.FunctionFieldFiniteType

noncomputable section

/-!
# Finite generation of the actual function field

The structure morphism supplies the base algebra. A nonempty affine open has
finite-type sections, and the genuine function field is their fraction field.
The proved compatibility of section maps and germs therefore gives essential
finite type, without adding an algebra structure or generation hypothesis.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} [IsIntegral X]

/-- A nonempty affine chart proves essential finite type of the actual
function field over the global sections of an affine base. -/
theorem functionFieldBase_essFiniteType_of_affineOpen
    (f : X ⟶ Y) [IsAffine Y] [LocallyOfFiniteType f]
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U) :
    letI := Betti.AffineDimension.Realization.functionFieldBaseAlgebra f
    Algebra.EssFiniteType Γ(Y, ⊤) X.functionField := by
  let := Betti.AffineDimension.Realization.sectionBaseAlgebra f U
  let := Betti.AffineDimension.Realization.functionFieldBaseAlgebra f
  let := Betti.AffineDimension.Realization.functionFieldBase_isScalarTower f U
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  let : Algebra.FiniteType Γ(Y, ⊤) Γ(X, U) :=
    f.finiteType_appLE (isAffineOpen_top Y) hU le_top
  let : Algebra.EssFiniteType Γ(X, U) X.functionField :=
    Algebra.EssFiniteType.of_isLocalization X.functionField (nonZeroDivisors Γ(X, U))
  exact Algebra.EssFiniteType.comp Γ(Y, ⊤) Γ(X, U) X.functionField

/-- An integral scheme locally of finite type over an affine base has an
essentially finite-type function field for its canonical base-section algebra. -/
theorem functionFieldBase_essFiniteType
    (f : X ⟶ Y) [IsAffine Y] [LocallyOfFiniteType f] :
    letI := Betti.AffineDimension.Realization.functionFieldBaseAlgebra f
    Algebra.EssFiniteType Γ(Y, ⊤) X.functionField := by
  let U : X.Opens :=
    (X.affineCover.f (X.affineCover.idx (genericPoint X))).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.affineCover.f _)
  let : Nonempty U := ⟨⟨genericPoint X, X.affineCover.covers (genericPoint X)⟩⟩
  exact functionFieldBase_essFiniteType_of_affineOpen f U hU

/-- Ring-homomorphism form of the same actual function-field result. -/
theorem functionFieldBaseMap_essFiniteType
    (f : X ⟶ Y) [IsAffine Y] [LocallyOfFiniteType f] :
    (Betti.AffineDimension.Realization.functionFieldBaseMap f).hom.EssFiniteType :=
  functionFieldBase_essFiniteType f

section Scalars

variable {K : Type u} [CommRing K]

/-- Essential finite type descends along the canonical isomorphism from the
actual scalar ring to the global functions on its spectrum. -/
theorem functionFieldScalarMap_essFiniteType
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    (FunctionFieldScalar.functionFieldScalarMap f).EssFiniteType := by
  exact (RingHom.EssFiniteType.respectsIso.cancel_left_isIso
    (Scheme.ΓSpecIso (.of K)).inv (Betti.AffineDimension.Realization.functionFieldBaseMap f)).mpr
      (functionFieldBaseMap_essFiniteType f)

/-- The function field of an integral scheme locally of finite type over
`Spec K` is essentially of finite type over the intended scalar ring `K`. -/
theorem functionFieldScalar_essFiniteType
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    letI := FunctionFieldScalar.functionFieldScalarAlgebra f
    Algebra.EssFiniteType K X.functionField :=
  functionFieldScalarMap_essFiniteType f

end Scalars

variable {K : Type u} [Field K]

/-- The function field of an integral scheme locally of finite type over a
field has finite transcendence degree for its actual structural algebra. -/
theorem functionFieldScalar_finTrdeg
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    letI := FunctionFieldScalar.functionFieldScalarAlgebra f
    FinTrdeg K X.functionField := by
  let := FunctionFieldScalar.functionFieldScalarAlgebra f
  let := functionFieldScalar_essFiniteType f
  infer_instance

/-- In particular, its transcendence degree is a finite cardinal. -/
theorem functionFieldScalar_trdeg_lt_aleph0
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    letI := FunctionFieldScalar.functionFieldScalarAlgebra f
    Algebra.trdeg K X.functionField < Cardinal.aleph0 := by
  let := FunctionFieldScalar.functionFieldScalarAlgebra f
  let := functionFieldScalar_finTrdeg f
  exact trdeg_lt_aleph0 K X.functionField

end

end OAI.AlgebraicGeometry.Foundations.Scheme.FunctionFieldFiniteType
end ComponentSource_9

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Foundations.Scheme.FunctionFieldFiniteType"

@[expose] public section ComponentSource_10
/- Original module: OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceEtale -/

/-! # Transcendence Etale -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceEtale

noncomputable section

/-!
# Formal etaleness over a separating polynomial coordinate algebra

An algebraically independent family identifies its polynomial algebra with
its generated subalgebra. Passing to the generated intermediate field is a
localization, and a separable extension of that field is formally etale.
-/

universe u

/-- The polynomial-algebra structure defined by evaluation at a specified
family of elements. -/
abbrev polynomialEvaluationAlgebra (k : Type*) {K ι : Type*}
    [CommSemiring k] [CommSemiring K] [Algebra k K] (v : ι → K) :
    Algebra (MvPolynomial ι k) K :=
  (MvPolynomial.aeval v).toRingHom.toAlgebra

/-- The evaluation algebra has the expected scalar tower over the original
coefficient semiring. -/
theorem polynomialEvaluation_isScalarTower (k : Type*) {K ι : Type*}
    [CommSemiring k] [CommSemiring K] [Algebra k K] (v : ι → K) :
    letI := polynomialEvaluationAlgebra k v
    IsScalarTower k (MvPolynomial ι k) K := by
  let := polynomialEvaluationAlgebra k v
  apply IsScalarTower.of_algebraMap_eq
  intro c
  exact ((MvPolynomial.aeval v).commutes c).symm

/-- A ring isomorphism is formally etale for its induced algebra structure. -/
theorem formallyEtale_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) : e.toRingHom.FormallyEtale := by
  let : Algebra R S := e.toRingHom.toAlgebra
  change Algebra.FormallyEtale R S
  let e' : R ≃ₐ[R] S := { e with commutes' := fun _ => rfl }
  exact Algebra.FormallyEtale.of_equiv e'

open scoped IntermediateField.algebraAdjoinAdjoin in
/-- A field separable over the field generated by an algebraically independent
family is formally etale over the polynomial algebra evaluated at that family. -/
theorem formallyEtale_polynomialEvaluation
    {k K ι : Type u} [Field k] [Field K] [Algebra k K]
    {v : ι → K} (hv : AlgebraicIndependent k v)
    [Algebra.IsSeparable (IntermediateField.adjoin k (Set.range v)) K] :
    letI := polynomialEvaluationAlgebra k v
    Algebra.FormallyEtale (MvPolynomial ι k) K := by
  change (MvPolynomial.aeval (R := k) v).toRingHom.FormallyEtale
  let A := Algebra.adjoin k (Set.range v)
  let F := IntermediateField.adjoin k (Set.range v)
  have hPA : hv.aevalEquiv.toRingHom.FormallyEtale :=
    formallyEtale_ringEquiv hv.aevalEquiv.toRingEquiv
  have hAF : (algebraMap A F).FormallyEtale :=
    RingHom.formallyEtale_algebraMap.mpr
      (Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A))
  have hFK : (algebraMap F K).FormallyEtale :=
    RingHom.formallyEtale_algebraMap.mpr
      (Algebra.FormallyEtale.of_isSeparable F K)
  have hc := (hPA.comp hAF).comp hFK
  have hcomp : (algebraMap F K).comp
      ((algebraMap A F).comp hv.aevalEquiv.toRingHom) =
        (MvPolynomial.aeval v).toRingHom := by
    apply RingHom.ext
    intro p
    change algebraMap F K (algebraMap A F (hv.aevalEquiv p)) = MvPolynomial.aeval v p
    rw [← IsScalarTower.algebraMap_apply A F K]
    exact hv.algebraMap_aevalEquiv p
  simpa only [hcomp] using hc

end

end OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceEtale
end ComponentSource_10

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceEtale"

@[expose] public section ComponentSource_11
/- Original module: OAI.AlgebraicGeometry.Foundations.Scheme.DifferentialTranscendenceDegree -/

/-! # Differential Transcendence Degree -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.DifferentialTranscendenceDegree

noncomputable section

/-!
# Differential dimension and transcendence bases

This module constructs actual bases of Kähler differential modules by base
change from polynomial rings. The field-theoretic hypotheses are used to
prove formal étaleness, rather than assuming a dimension formula.
-/

set_option autoImplicit false
set_option warningAsError true

open _root_.Module
open scoped TensorProduct

universe u

section EtalePolynomial

variable (k K ι : Type u) [Field k] [Field K] [Algebra k K]
variable [Algebra (MvPolynomial ι k) K] [IsScalarTower k (MvPolynomial ι k) K]
variable [Algebra.FormallyEtale (MvPolynomial ι k) K]

/-- A formally étale algebra over a polynomial ring has the base-changed
coordinate differentials as an actual basis of its differentials over k. -/
def kaehlerPolynomialEtaleBasis : Basis ι K Ω[K⁄k] :=
  ((KaehlerDifferential.mvPolynomialBasis k ι).baseChange K).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k (MvPolynomial ι k) K)

/-- The dimension here follows from a constructed basis, not an assumed
geometric dimension or a surrogate differential object. -/
theorem kaehlerPolynomialEtale_rank : Module.rank K Ω[K⁄k] = Cardinal.mk ι :=
  (kaehlerPolynomialEtaleBasis k K ι).mk_eq_rank''.symm

/-- The basis vectors are the actual universal differentials of the images
of the polynomial coordinates. -/
theorem kaehlerPolynomialEtaleBasis_apply (i : ι) :
    kaehlerPolynomialEtaleBasis k K ι i =
      KaehlerDifferential.D k K (algebraMap (MvPolynomial ι k) K (MvPolynomial.X i)) := by
  simp [kaehlerPolynomialEtaleBasis,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]

/-- For an actual transcendence basis, the constructed differential basis
has cardinality equal to the standard transcendence degree. -/
theorem kaehler_rank_eq_trdeg_of_etale_polynomial {v : ι → K}
    (hv : IsTranscendenceBasis k v) :
    Module.rank K Ω[K⁄k] = Algebra.trdeg k K :=
  (kaehlerPolynomialEtale_rank k K ι).trans hv.cardinalMk_eq_trdeg

end EtalePolynomial

section FinitelyGeneratedFields

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
variable [PerfectField k] [Algebra.EssFiniteType k K]

/-- A finitely generated extension of a perfect field has a finite
transcendence basis whose cardinality also indexes a constructed basis of
its actual Kähler differential module. -/
theorem exists_transcendenceBasis_kaehlerBasis :
    ∃ s : Finset K, IsTranscendenceBasis k ((↑) : s → K) ∧
      Nonempty (Basis s K Ω[K⁄k]) := by
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
  have hset : Set.range ((↑) : s → K) = (s : Set K) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  let : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range ((↑) : s → K))) K := by
    rw [hset]
    exact hsep
  let : Algebra (MvPolynomial s k) K := TranscendenceEtale.polynomialEvaluationAlgebra k ((↑) : s → K)
  let : IsScalarTower k (MvPolynomial s k) K :=
    TranscendenceEtale.polynomialEvaluation_isScalarTower k ((↑) : s → K)
  let : Algebra.FormallyEtale (MvPolynomial s k) K :=
    TranscendenceEtale.formallyEtale_polynomialEvaluation hs.1
  exact ⟨s, hs, ⟨kaehlerPolynomialEtaleBasis k K s⟩⟩

/-- Differential rank equals the standard transcendence degree for a
finitely generated extension of a perfect field. -/
theorem kaehler_rank_eq_trdeg : Module.rank K Ω[K⁄k] = Algebra.trdeg k K := by
  obtain ⟨s, hs, ⟨b⟩⟩ := exists_transcendenceBasis_kaehlerBasis k K
  exact b.mk_eq_rank''.symm.trans hs.cardinalMk_eq_trdeg

/-- The differential module in this theorem is finite-dimensional. -/
theorem kaehler_finite_of_essFiniteType : Module.Finite K Ω[K⁄k] := by
  obtain ⟨s, _, ⟨b⟩⟩ := exists_transcendenceBasis_kaehlerBasis k K
  exact Module.Finite.of_basis b

/-- The same dimension identity in natural-number form. -/
theorem kaehler_finrank_eq_trdeg :
    Module.finrank K Ω[K⁄k] = (Algebra.trdeg k K).toNat := by
  exact congrArg Cardinal.toNat (kaehler_rank_eq_trdeg k K)

end FinitelyGeneratedFields

variable (k K : Type u) [Field k] [CharZero k] [Field K] [Algebra k K]
variable [Algebra.EssFiniteType k K]

/-- In characteristic zero, a finitely generated field extension has
differential dimension equal to its transcendence degree, with no separate
separability or dimension assumption. -/
theorem kaehler_rank_eq_trdeg_charZero :
    Module.rank K Ω[K⁄k] = Algebra.trdeg k K :=
  kaehler_rank_eq_trdeg k K

/-- Natural-number differential dimension in characteristic zero. -/
theorem kaehler_finrank_eq_trdeg_charZero :
    Module.finrank K Ω[K⁄k] = (Algebra.trdeg k K).toNat :=
  kaehler_finrank_eq_trdeg k K

end

end OAI.AlgebraicGeometry.Foundations.Scheme.DifferentialTranscendenceDegree
end ComponentSource_11

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Foundations.Scheme.DifferentialTranscendenceDegree"

@[expose] public section ComponentSource_12
/- Original module: OAI.AlgebraicGeometry.Foundations.Scheme.DifferentialBaseIso -/

/-! # Differential Base Iso -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.DifferentialBaseIso

noncomputable section

/-!
# Kähler differentials under an isomorphism of the base ring

Changing the base ring along a surjective map does not change the module of
differentials of an algebra over the target. In particular, this gives explicit
transport along a base-ring isomorphism, with the induced scalar structure.
-/

section SurjectiveBase

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- The universal `R`-derivation is also `S`-linear when `R → S` is surjective. -/
def kaehlerDerivationOfSurjectiveBase
    (h : Function.Surjective (algebraMap R S)) : Derivation S T Ω[T⁄R] where
  toFun := KaehlerDifferential.D R T
  map_add' := map_add (KaehlerDifferential.D R T)
  map_smul' s x := by
    obtain ⟨r, rfl⟩ := h s
    simpa only [RingHom.id_apply, IsScalarTower.algebraMap_smul] using
      (KaehlerDifferential.D R T).map_smul r x
  map_one_eq_zero' := (KaehlerDifferential.D R T).map_one_eq_zero
  leibniz' := (KaehlerDifferential.D R T).leibniz

@[simp]
theorem kaehlerDerivationOfSurjectiveBase_apply
    (h : Function.Surjective (algebraMap R S)) (x : T) :
    kaehlerDerivationOfSurjectiveBase R S T h x = KaehlerDifferential.D R T x := rfl

/-- A surjective change of base gives an actual linear equivalence between
the two modules of Kähler differentials. -/
def kaehlerDifferentialEquivOfSurjectiveBase
    (h : Function.Surjective (algebraMap R S)) : Ω[T⁄R] ≃ₗ[T] Ω[T⁄S] := by
  let f := KaehlerDifferential.map R S T T
  let g := (kaehlerDerivationOfSurjectiveBase R S T h).liftKaehlerDifferential
  have hgf : g.comp f = LinearMap.id := by
    apply Derivation.liftKaehlerDifferential_unique
    ext x
    simp [f, g]
  have hfg : f.comp g = LinearMap.id := by
    apply Derivation.liftKaehlerDifferential_unique
    ext x
    simp [f, g]
  exact
    { f with
      invFun := g
      left_inv := fun x => LinearMap.congr_fun hgf x
      right_inv := fun x => LinearMap.congr_fun hfg x }

@[simp]
theorem kaehlerDifferentialEquivOfSurjectiveBase_D
    (h : Function.Surjective (algebraMap R S)) (x : T) :
    kaehlerDifferentialEquivOfSurjectiveBase R S T h (KaehlerDifferential.D R T x) =
      KaehlerDifferential.D S T x := by
  change KaehlerDifferential.map R S T T (KaehlerDifferential.D R T x) = _
  simp

@[simp]
theorem kaehlerDifferentialEquivOfSurjectiveBase_symm_D
    (h : Function.Surjective (algebraMap R S)) (x : T) :
    (kaehlerDifferentialEquivOfSurjectiveBase R S T h).symm
        (KaehlerDifferential.D S T x) = KaehlerDifferential.D R T x := by
  apply (kaehlerDifferentialEquivOfSurjectiveBase R S T h).injective
  simp

theorem kaehlerDifferential_rank_eq_of_surjectiveBase
    (h : Function.Surjective (algebraMap R S)) :
    Module.rank T Ω[T⁄R] = Module.rank T Ω[T⁄S] :=
  (kaehlerDifferentialEquivOfSurjectiveBase R S T h).rank_eq

theorem kaehlerDifferential_finrank_eq_of_surjectiveBase
    (h : Function.Surjective (algebraMap R S)) :
    Module.finrank T Ω[T⁄R] = Module.finrank T Ω[T⁄S] :=
  (kaehlerDifferentialEquivOfSurjectiveBase R S T h).finrank_eq

end SurjectiveBase

variable {R S : Type*} (T : Type*) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R T]

/-- The scalar structure obtained by transporting the base along a ring
isomorphism. -/
abbrev differentialBaseIsoAlgebra (e : S ≃+* R) : Algebra S T :=
  ((algebraMap R T).comp e.toRingHom).toAlgebra

/-- Kähler differentials are unchanged by transporting the base ring through
an isomorphism. The new scalar structure is specified by composition. -/
def kaehlerDifferentialBaseIso (e : S ≃+* R) :
    letI := differentialBaseIsoAlgebra T e
    Ω[T⁄R] ≃ₗ[T] Ω[T⁄S] := by
  let := differentialBaseIsoAlgebra T e
  let : Algebra S R := e.toRingHom.toAlgebra
  have : IsScalarTower S R T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact (kaehlerDifferentialEquivOfSurjectiveBase S R T e.surjective).symm

@[simp]
theorem kaehlerDifferentialBaseIso_D (e : S ≃+* R) (x : T) :
    letI := differentialBaseIsoAlgebra T e
    kaehlerDifferentialBaseIso T e (KaehlerDifferential.D R T x) =
      KaehlerDifferential.D S T x := by
  let := differentialBaseIsoAlgebra T e
  let : Algebra S R := e.toRingHom.toAlgebra
  have : IsScalarTower S R T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact kaehlerDifferentialEquivOfSurjectiveBase_symm_D S R T e.surjective x

theorem kaehlerDifferential_rank_eq_of_baseIso (e : S ≃+* R) :
    letI := differentialBaseIsoAlgebra T e
    Module.rank T Ω[T⁄R] = Module.rank T Ω[T⁄S] := by
  let := differentialBaseIsoAlgebra T e
  exact (kaehlerDifferentialBaseIso T e).rank_eq

theorem kaehlerDifferential_finrank_eq_of_baseIso (e : S ≃+* R) :
    letI := differentialBaseIsoAlgebra T e
    Module.finrank T Ω[T⁄R] = Module.finrank T Ω[T⁄S] := by
  let := differentialBaseIsoAlgebra T e
  exact (kaehlerDifferentialBaseIso T e).finrank_eq

end

end OAI.AlgebraicGeometry.Foundations.Scheme.DifferentialBaseIso
end ComponentSource_12

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Foundations.Scheme.DifferentialBaseIso"

@[expose] public section ComponentSource_13
/- Original module: OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceDegreeTransfer -/

/-! # Transcendence Degree Transfer -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceDegreeTransfer

/-!
# Transcendence degree under algebraic extensions

These results use mathlib's cardinal-valued transcendence degree and its
additivity theorem for faithful towers of domains. They apply in particular to
the integral extensions arising in Noether normalization. The prime-quotient
comparison uses the actual map induced on quotients, whose injectivity follows
from taking the inverse image of the prime ideal.
-/

universe u v w

section Towers

variable (k : Type u) (A B : Type v) [Field k]
  [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Algebra k A] [Algebra k B] [Algebra A B]
  [IsScalarTower k A B] [FaithfulSMul A B]

/-- An algebraic faithful extension of domains preserves transcendence degree
over the common base field. -/
theorem trdeg_eq_of_isAlgebraic [Algebra.IsAlgebraic A B] :
    Algebra.trdeg k A = Algebra.trdeg k B := by
  simpa only [trdeg_eq_zero, add_zero] using (trdeg_add_eq k A (A := B))

/-- An integral faithful extension of domains preserves transcendence degree. -/
theorem trdeg_eq_of_isIntegral [Algebra.IsIntegral A B] :
    Algebra.trdeg k A = Algebra.trdeg k B :=
  trdeg_eq_of_isAlgebraic k A B

end Towers

section LiftedTowers

variable (k : Type u) (A : Type v) (B : Type w) [Field k]
  [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Algebra k A] [Algebra k B] [Algebra A B]
  [IsScalarTower k A B] [FaithfulSMul A B]

/-- The universe-polymorphic form of algebraic transcendence-degree invariance. -/
theorem lift_trdeg_eq_of_isAlgebraic [Algebra.IsAlgebraic A B] :
    Cardinal.lift.{w} (Algebra.trdeg k A) =
      Cardinal.lift.{v} (Algebra.trdeg k B) := by
  simpa only [trdeg_eq_zero, Cardinal.lift_zero, add_zero] using
    (lift_trdeg_add_eq k A B)

/-- Integral invariance with the cardinal lifts required by distinct universes. -/
theorem lift_trdeg_eq_of_isIntegral [Algebra.IsIntegral A B] :
    Cardinal.lift.{w} (Algebra.trdeg k A) =
      Cardinal.lift.{v} (Algebra.trdeg k B) :=
  lift_trdeg_eq_of_isAlgebraic k A B

end LiftedTowers

section Fractions

variable (k : Type u) (A K : Type v) [Field k] [CommRing A] [IsDomain A]
  [Field K] [Algebra k A] [Algebra k K] [Algebra A K]
  [IsScalarTower k A K] [IsFractionRing A K]

/-- Passing from a domain to a fraction field does not alter its
transcendence degree over the base field. -/
theorem trdeg_eq_of_isFractionRing : Algebra.trdeg k A = Algebra.trdeg k K := by
  let : Algebra.IsAlgebraic A K :=
    IsLocalization.isAlgebraic K (nonZeroDivisors A)
  exact trdeg_eq_of_isAlgebraic k A K

/-- The standard fraction field has the same transcendence degree as its domain. -/
theorem trdeg_eq_fractionRing (k : Type u) (A : Type v) [Field k]
    [CommRing A] [IsDomain A] [Algebra k A] :
    Algebra.trdeg k A = Algebra.trdeg k (FractionRing A) :=
  trdeg_eq_of_isFractionRing k A (FractionRing A)

end Fractions

variable (k : Type u) {A B : Type v} [Field k]
  [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

/-- A faithful integral algebra homomorphism identifies the transcendence
degrees of its source and target domains. -/
theorem trdeg_eq_of_injective_integral_algHom [IsDomain A] [IsDomain B]
    (f : A →ₐ[k] B) (hf : Function.Injective f) (hint : f.toRingHom.IsIntegral) :
    Algebra.trdeg k A = Algebra.trdeg k B := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let : IsScalarTower k A B := IsScalarTower.of_algHom f
  let : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).mpr hf
  let : Algebra.IsIntegral A B := ⟨hint⟩
  exact trdeg_eq_of_isIntegral k A B

/-- Quotienting an integral algebra map by a prime and its inverse image
preserves transcendence degree. The original map need not be injective:
the induced map on these two quotients is injective by construction. -/
theorem trdeg_quotient_eq_of_integral_algHom (f : A →ₐ[k] B)
    (hint : f.toRingHom.IsIntegral) (P : Ideal B) [P.IsPrime] :
    Algebra.trdeg k (A ⧸ P.comap f) = Algebra.trdeg k (B ⧸ P) := by
  exact trdeg_eq_of_injective_integral_algHom k
    (Ideal.quotientMapₐ P f le_rfl) Ideal.quotientMap_injective hint.quotient

/-- The prime-quotient comparison for an integral tower over a field. -/
theorem trdeg_quotient_eq_of_isIntegral [Algebra A B] [IsScalarTower k A B]
    [Algebra.IsIntegral A B] (P : Ideal B) [P.IsPrime] :
    Algebra.trdeg k (A ⧸ P.comap (algebraMap A B)) =
      Algebra.trdeg k (B ⧸ P) := by
  exact trdeg_quotient_eq_of_integral_algHom k (IsScalarTower.toAlgHom k A B)
    Algebra.IsIntegral.isIntegral P

end OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceDegreeTransfer
end ComponentSource_13

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceDegreeTransfer"

@[expose] public section ComponentSource_14
/- Original module: OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension -/

/-! # Transcendence Dimension -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension

noncomputable section

/-!
# Dimension from the actual function field

For an integral scheme over a field, the structure morphism gives its function
field its canonical scalar algebra. Its transcendence degree therefore defines
a dimension without any choice of an affine presentation. Local finite type
ensures that taking the natural-number value loses no information. On every
nonempty affine open it agrees with the transcendence degree of the actual
ring of sections.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]

/-- The transcendence dimension of an integral scheme over its actual base
field. The finite-type theorem below verifies that the cardinal-to-natural
conversion preserves the full transcendence degree in the intended setting. -/
def schemeTranscendenceDimension (f : X ⟶ Spec (.of K)) : ℕ :=
  letI := FunctionFieldScalar.functionFieldScalarAlgebra f
  (Algebra.trdeg K X.functionField).toNat

/-- The defining expression, with the structure-morphism scalar algebra
made explicit for use in downstream statements. -/
theorem schemeTranscendenceDimension_def (f : X ⟶ Spec (.of K)) :
    letI := FunctionFieldScalar.functionFieldScalarAlgebra f
    schemeTranscendenceDimension f = (Algebra.trdeg K X.functionField).toNat := rfl

/-- For a locally finite-type integral scheme, the natural-number dimension
recovers the complete cardinal-valued transcendence degree. -/
theorem schemeTranscendenceDimension_cast (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] :
    letI := FunctionFieldScalar.functionFieldScalarAlgebra f
    (schemeTranscendenceDimension f : Cardinal) = Algebra.trdeg K X.functionField := by
  let := FunctionFieldScalar.functionFieldScalarAlgebra f
  exact Cardinal.cast_toNat_of_lt_aleph0 (FunctionFieldFiniteType.functionFieldScalar_trdeg_lt_aleph0 f)

/-- Every finite transcendence basis of the actual function field counts
the same dimension. -/
theorem schemeTranscendenceDimension_eq_natCard_basis
    (f : X ⟶ Spec (.of K)) {ι : Type u} [Finite ι] (v : ι → X.functionField) :
    letI := FunctionFieldScalar.functionFieldScalarAlgebra f
    IsTranscendenceBasis K v → schemeTranscendenceDimension f = Nat.card ι := by
  let := FunctionFieldScalar.functionFieldScalarAlgebra f
  intro hv
  exact congrArg Cardinal.toNat hv.cardinalMk_eq_trdeg.symm

/-- The locally finite-type hypothesis supplies an actual finite
transcendence basis of cardinality equal to this dimension. -/
theorem exists_schemeTranscendenceBasis (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] :
    letI := FunctionFieldScalar.functionFieldScalarAlgebra f
    ∃ s : Finset X.functionField, IsTranscendenceBasis K ((↑) : s → X.functionField) ∧
      s.card = schemeTranscendenceDimension f := by
  let := FunctionFieldScalar.functionFieldScalarAlgebra f
  let := FunctionFieldFiniteType.functionFieldScalar_finTrdeg f
  obtain ⟨s, hs⟩ := exists_finset_isTranscendenceBasis K X.functionField
  refine ⟨s, hs, ?_⟩
  have h := schemeTranscendenceDimension_eq_natCard_basis f ((↑) : s → X.functionField) hs
  simpa using h.symm

/-- Over a perfect field the same dimension is computed by the genuine
module of Kähler differentials of the function field. -/
theorem schemeTranscendenceDimension_eq_kaehlerFinrank [PerfectField K]
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    letI := FunctionFieldScalar.functionFieldScalarAlgebra f
    schemeTranscendenceDimension f = Module.finrank X.functionField Ω[X.functionField⁄K] := by
  let := FunctionFieldScalar.functionFieldScalarAlgebra f
  let := FunctionFieldFiniteType.functionFieldScalar_essFiniteType f
  exact (DifferentialTranscendenceDegree.kaehler_finrank_eq_trdeg K X.functionField).symm

/-- The function-field differential module is finite-dimensional in the
perfect-field locally finite-type setting. -/
theorem functionFieldScalar_kaehlerFinite [PerfectField K]
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    letI := FunctionFieldScalar.functionFieldScalarAlgebra f
    Module.Finite X.functionField Ω[X.functionField⁄K] := by
  let := FunctionFieldScalar.functionFieldScalarAlgebra f
  let := FunctionFieldFiniteType.functionFieldScalar_essFiniteType f
  exact DifferentialTranscendenceDegree.kaehler_finite_of_essFiniteType K X.functionField

/-- On any nonempty affine open, the canonical dimension is the
transcendence degree of the actual sections over the actual base field. -/
theorem schemeTranscendenceDimension_eq_affineSections
    (f : X ⟶ Spec (.of K)) (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U) :
    letI := SpecScalarTransport.specSectionScalarAlgebra f U
    schemeTranscendenceDimension f = (Algebra.trdeg K Γ(X, U)).toNat := by
  let := SpecScalarTransport.specSectionScalarAlgebra f U
  let := FunctionFieldScalar.functionFieldScalarAlgebra f
  let := FunctionFieldScalar.functionFieldScalar_isScalarTower f U
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  exact congrArg Cardinal.toNat (TranscendenceDegreeTransfer.trdeg_eq_of_isFractionRing K Γ(X, U) X.functionField).symm

/-- Replacing global functions on the base spectrum by the actual scalar
field leaves the function-field differential dimension unchanged. -/
theorem functionFieldScalar_kaehlerFinrank_eq_base
    (f : X ⟶ Spec (.of K)) :
    letI := FunctionFieldScalar.functionFieldScalarAlgebra f
    Module.finrank X.functionField Ω[X.functionField⁄K] =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension f := by
  let := FunctionFieldScalar.specGlobalScalarAlgebra K
  let := Betti.AffineDimension.Realization.functionFieldBaseAlgebra f
  let := FunctionFieldScalar.functionFieldScalarAlgebra f
  let := FunctionFieldScalar.functionFieldBaseScalar_isScalarTower f
  exact (DifferentialBaseIso.kaehlerDifferentialEquivOfSurjectiveBase K Γ(Spec (.of K), ⊤) X.functionField
    (FunctionFieldScalar.specGlobalScalarAlgebra_surjective (K := K))).finrank_eq

/-- In characteristic zero, the canonical transcendence dimension agrees
with the common differential dimension used by the genuine smooth charts. -/
theorem schemeTranscendenceDimension_eq_functionFieldDifferentialDimension
    [CharZero K] (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    schemeTranscendenceDimension f = Betti.AffineDimension.Realization.functionFieldDifferentialDimension f := by
  let := FunctionFieldScalar.functionFieldScalarAlgebra f
  exact (schemeTranscendenceDimension_eq_kaehlerFinrank f).trans
    (functionFieldScalar_kaehlerFinrank_eq_base f)

end

end OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension
end ComponentSource_14

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension"

@[expose] public section ComponentSource_15
/- Original module: OAI.AlgebraicGeometry.Foundations.Scheme.OpenFunctionField -/

/-! # Open Function Field -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.OpenFunctionField

noncomputable section

/-!
# Function fields and dimensions under nonempty open immersions

The function-field isomorphism is the actual stalk isomorphism of the open
immersion at the generic point, transported along the proved equality of
generic points. Its compatibility with scalar constants is proved from the
germ/stalk-map identity.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {Y X : Scheme.{u}} [IrreducibleSpace Y] [IrreducibleSpace X]

/-- An open immersion identifies the actual generic stalks. -/
def openImmersionFunctionFieldIso (i : Y ⟶ X) [IsOpenImmersion i] :
    X.functionField ≅ Y.functionField :=
  X.presheaf.stalkCongr
      (Inseparable.of_eq (genericPoint_eq_of_isOpenImmersion i).symm) ≪≫
    asIso (i.stalkMap (genericPoint Y))

set_option backward.isDefEq.respectTransparency.types false in
/-- The generic-stalk isomorphism commutes with taking germs of global sections. -/
theorem openImmersionFunctionFieldIso_germ (i : Y ⟶ X) [IsOpenImmersion i] :
    X.presheaf.germ ⊤ (genericPoint X) (by trivial) ≫ (openImmersionFunctionFieldIso i).hom =
      i.appTop ≫ Y.presheaf.germ ⊤ (genericPoint Y) (by trivial) := by
  simp only [openImmersionFunctionFieldIso, Iso.trans_hom,
    TopCat.Presheaf.stalkCongr_hom, asIso_hom, ← Category.assoc]
  rw [TopCat.Presheaf.germ_stalkSpecializes]
  exact i.germ_stalkMap ⊤ (genericPoint Y) (by trivial)

/-- Compatibility with the original global-functions base map is a genuine
consequence of functoriality of pullback and of germs. -/
theorem openImmersionFunctionFieldIso_base {S : Scheme.{u}}
    (i : Y ⟶ X) [IsOpenImmersion i] (f : X ⟶ S) :
    Betti.AffineDimension.Realization.functionFieldBaseMap f ≫ (openImmersionFunctionFieldIso i).hom =
      Betti.AffineDimension.Realization.functionFieldBaseMap (i ≫ f) := by
  simp only [Betti.AffineDimension.Realization.functionFieldBaseMap, Scheme.Hom.comp_appTop, Category.assoc]
  rw [openImmersionFunctionFieldIso_germ]

variable {K : Type u} [Field K]

/-- The generic-stalk isomorphism respects the canonical scalar map. -/
theorem openImmersionFunctionFieldIso_scalar
    (i : Y ⟶ X) [IsOpenImmersion i] (f : X ⟶ Spec (.of K)) :
    (openImmersionFunctionFieldIso i).hom.hom.comp (FunctionFieldScalar.functionFieldScalarMap f) =
      FunctionFieldScalar.functionFieldScalarMap (i ≫ f) := by
  exact congrArg
    (fun g : Γ(Spec (.of K), ⊤) ⟶ Y.functionField =>
      g.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)
    (openImmersionFunctionFieldIso_base i f)

/-- An actual open immersion induces an isomorphism of the canonical scalar algebras. -/
def openImmersionFunctionFieldAlgEquiv
    (i : Y ⟶ X) [IsOpenImmersion i] (f : X ⟶ Spec (.of K)) :
    letI := FunctionFieldScalar.functionFieldScalarAlgebra f
    letI := FunctionFieldScalar.functionFieldScalarAlgebra (i ≫ f)
    X.functionField ≃ₐ[K] Y.functionField := by
  let := FunctionFieldScalar.functionFieldScalarAlgebra f
  let := FunctionFieldScalar.functionFieldScalarAlgebra (i ≫ f)
  refine { (openImmersionFunctionFieldIso i).commRingCatIsoToRingEquiv with
    commutes' := ?_ }
  intro c
  exact DFunLike.congr_fun (openImmersionFunctionFieldIso_scalar i f) c

variable [IsIntegral Y] [IsIntegral X]

/-- Nonempty open immersions preserve the canonical transcendence dimension.
No finite-type assumption is needed for the equality of these cardinal-to-natural values. -/
theorem schemeTranscendenceDimension_openImmersion
    (i : Y ⟶ X) [IsOpenImmersion i] (f : X ⟶ Spec (.of K)) :
    TranscendenceDimension.schemeTranscendenceDimension (i ≫ f) = TranscendenceDimension.schemeTranscendenceDimension f := by
  let := FunctionFieldScalar.functionFieldScalarAlgebra f
  let := FunctionFieldScalar.functionFieldScalarAlgebra (i ≫ f)
  exact congrArg Cardinal.toNat (openImmersionFunctionFieldAlgEquiv i f).trdeg_eq.symm

/-- In particular, restricting to any nonempty actual open subscheme preserves dimension. -/
theorem schemeTranscendenceDimension_open (f : X ⟶ Spec (.of K))
    (U : X.Opens) [Nonempty U] :
    TranscendenceDimension.schemeTranscendenceDimension (U.ι ≫ f) = TranscendenceDimension.schemeTranscendenceDimension f :=
  schemeTranscendenceDimension_openImmersion U.ι f

end

end OAI.AlgebraicGeometry.Foundations.Scheme.OpenFunctionField
end ComponentSource_15

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Foundations.Scheme.OpenFunctionField"

@[expose] public section ComponentSource_16
/- Original module: OAI.AlgebraicGeometry.Foundations.Scheme.AffineSectionFiniteType -/

/-! # Affine Section Finite Type -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.AffineSectionFiniteType

noncomputable section

/-!
# Finite-type affine sections over the actual scalar ring

The structural map to `Spec K` gives an affine open's sections a `K`-algebra
structure. Local finite type makes this algebra finite type, after transport
through the canonical isomorphism between `K` and global sections of `Spec K`.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [CommRing K] {X : Scheme.{u}}

/-- The scalar homomorphism on an affine open is finite type when the
structural morphism is locally of finite type. -/
theorem specSectionScalarMap_finiteType
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (U : X.Opens) (hU : IsAffineOpen U) :
    (SpecScalarTransport.specSectionScalarMap f U).FiniteType := by
  exact (RingHom.finiteType_respectsIso.cancel_left_isIso
    (Scheme.ΓSpecIso (.of K)).inv (f.appLE ⊤ U le_top)).mpr
      (f.finiteType_appLE (isAffineOpen_top (Spec (.of K))) hU le_top)

/-- An actual affine coordinate algebra of a locally finite-type `K`-scheme
is finite type over `K`. -/
theorem specSectionScalarAlgebra_finiteType
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI := SpecScalarTransport.specSectionScalarAlgebra f U
    Algebra.FiniteType K Γ(X, U) :=
  specSectionScalarMap_finiteType f U hU

end

end OAI.AlgebraicGeometry.Foundations.Scheme.AffineSectionFiniteType
end ComponentSource_16

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Foundations.Scheme.AffineSectionFiniteType"

@[expose] public section ComponentSource_17
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.DimensionBridge -/

/-! # Dimension Bridge -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.DimensionBridge.BundleCycles

noncomputable section

/-!
# LineBundleCycles: actual affine scalar maps and transcendence dimension

The canonical spectrum/global-sections isomorphism respects the scalar
action induced by the actual structure morphism. It therefore identifies
the scheme's function-field dimension with the coordinate ring's
transcendence degree, without an assumed scalar compatibility.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u
variable (k A : Type u) [Field k] [CommRing A] [Algebra k A]

/-- The spectrum/global-sections isomorphism over the actual coefficient field. -/
def specGlobalScalarAlgEquiv :
    letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⊤
    Γ(Spec (CommRingCat.of A), ⊤) ≃ₐ[k] A := by
  let a : CommRingCat.of k ⟶ CommRingCat.of A := CommRingCat.ofHom (algebraMap k A)
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra (Spec.map a) ⊤
  refine { (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro r
  have h := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality a)
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r)
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      ((Spec.map a).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r)) =
    a ((Scheme.ΓSpecIso (CommRingCat.of k)).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r)) at h
  have he : (Spec.map a).appLE ⊤ ⊤ le_top = (Spec.map a).appTop :=
    (Spec.map a).app_eq_appLE.symm
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      ((Spec.map a).appLE ⊤ ⊤ le_top ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r)) = algebraMap k A r
  exact (congrArg (fun g => (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      (g ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r))) he).trans
    (h.trans (congrArg a (Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of k)) r)))

/-- The canonical dimension of an integral affine scheme equals its actual ring transcendence degree. -/
theorem schemeTranscendenceDimension_spec_algebra [IsDomain A] :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Spec.map (CommRingCat.ofHom (algebraMap k A))) =
      (Algebra.trdeg k A).toNat := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap k A))
  have : Nonempty (⊤ : (Spec (CommRingCat.of A)).Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of A))), trivial⟩⟩
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f ⊤
  exact (Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_affineSections f ⊤ (isAffineOpen_top _)).trans
    (congrArg Cardinal.toNat (specGlobalScalarAlgEquiv k A).trdeg_eq)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.DimensionBridge.BundleCycles
end ComponentSource_17

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.DimensionBridge"

@[expose] public section ComponentSource_18
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.ReesCoefficients -/

/-! # Rees Coefficients -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ReesCoefficients.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the coefficient ideal of the normal cone

The extension of I to R[It] consists exactly of Rees polynomials whose
degree-n coefficient lies in I^(n+1). This identifies the relations in the
normal-cone presentation without any finite-generation assumption on I.
-/

open _root_.Polynomial
open scoped BigOperators

universe u
variable {R : Type u} [CommRing R]

/-- Rees polynomials with one extra power of I in every coefficient. -/
def reesCoefficientIdeal (I : Ideal R) : Ideal (reesAlgebra I) where
  carrier := {p | ∀ n, p.val.coeff n ∈ I ^ (n + 1)}
  zero_mem' _ := Ideal.zero_mem _
  add_mem' {p q} hp hq n := by
    change (p.val + q.val).coeff n ∈ I ^ (n + 1)
    rw [coeff_add]
    exact Ideal.add_mem _ (hp n) (hq n)
  smul_mem' s p hp n := by
    change (s.val * p.val).coeff n ∈ _
    rw [coeff_mul]
    apply Ideal.sum_mem
    rintro ⟨j, k⟩ hjk
    have h := Ideal.mul_mem_mul (s.property j) (hp k)
    rw [← pow_add] at h
    convert h using 1
    exact congrArg (fun m => I ^ m) (by have := Finset.mem_antidiagonal.mp hjk; omega)

theorem normalConeIdeal_le_reesCoefficientIdeal (I : Ideal R) :
    Normal.Cone.BundleCycles.normalConeIdeal I ≤ reesCoefficientIdeal I := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro r hr n
  change (C r).coeff n ∈ I ^ (n + 1)
  rw [coeff_C]
  split_ifs with hn
  · simpa [hn] using hr
  · exact Ideal.zero_mem _

/-- Each coefficient in I^(n+1) is a finite sum of products of a coefficient
in I with a degree-n Rees monomial. -/
theorem normalConeIdeal_contains_monomial (I : Ideal R) (n : ℕ) (r : R)
    (hr : r ∈ I ^ (n + 1)) :
    ∃ p : reesAlgebra I, p ∈ Normal.Cone.BundleCycles.normalConeIdeal I ∧ p.val = monomial n r := by
  rw [pow_succ'] at hr
  refine Submodule.smul_induction_on hr ?_ ?_
  · intro a ha b hb
    let p : reesAlgebra I := ⟨monomial n b, reesAlgebra.monomial_mem.mpr hb⟩
    refine ⟨algebraMap R (reesAlgebra I) a * p,
      Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha), ?_⟩
    change C a * monomial n b = monomial n (a * b)
    simp only [C_mul_monomial]
  · intro a b ha hb
    obtain ⟨p, hp, ep⟩ := ha
    obtain ⟨q, hq, eq⟩ := hb
    refine ⟨p + q, Ideal.add_mem _ hp hq, ?_⟩
    change p.val + q.val = _
    rw [ep, eq, map_add]

/-- Exact coefficient description of the ideal defining the normal cone. -/
theorem normalConeIdeal_eq_reesCoefficientIdeal (I : Ideal R) :
    Normal.Cone.BundleCycles.normalConeIdeal I = reesCoefficientIdeal I := by
  classical
  apply le_antisymm (normalConeIdeal_le_reesCoefficientIdeal I)
  intro p hp
  have hm (n : ℕ) := normalConeIdeal_contains_monomial I n (p.val.coeff n) (hp n)
  choose q hq eq using hm
  have he : p = ∑ n ∈ p.val.support, q n := by
    apply Subtype.ext
    change p.val = (reesAlgebra I).val (∑ n ∈ p.val.support, q n)
    simp only [map_sum]
    change p.val = ∑ n ∈ p.val.support, (q n).val
    simp only [eq]
    exact p.val.as_sum_support
  rw [he]
  exact Ideal.sum_mem _ fun n hn => hq n

theorem mem_normalConeIdeal_iff (I : Ideal R) (p : reesAlgebra I) :
    p ∈ Normal.Cone.BundleCycles.normalConeIdeal I ↔ ∀ n, p.val.coeff n ∈ I ^ (n + 1) := by
  rw [normalConeIdeal_eq_reesCoefficientIdeal]
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ReesCoefficients.BundleCycles
end ComponentSource_18

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.ReesCoefficients"

@[expose] public section ComponentSource_19
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.SpecialFiber -/

/-! # Special Fiber -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SpecialFiber.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the special fiber of the affine deformation

The map R[It] → R[t,I/t]/(t) sends aT^n to a/t^n. We prove its kernel
is I R[It] and its surjectivity by discarding positive Laurent exponents.
It therefore identifies the special fiber with the actual normal cone.
-/

open LaurentPolynomial

universe u
variable {R : Type u} [CommRing R]

/-- The ring of the closed fiber t = 0. -/
abbrev DeformationSpecialRing (I : Ideal R) :=
  Deformation.Iff.BundleCycles.deformationAlgebra I ⧸ Deformation.Iff.BundleCycles.deformationSpecialIdeal I

/-- The map from the ordinary Rees algebra to the special fiber. -/
def reesToSpecialFiber (I : Ideal R) : reesAlgebra I →+* DeformationSpecialRing I :=
  (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal I)).comp (Deformation.Iff.BundleCycles.reesToDeformation I).toRingHom

/-- The kernel is exactly I R[It], with no regularity hypothesis on I. -/
theorem reesToSpecialFiber_ker (I : Ideal R) :
    RingHom.ker (reesToSpecialFiber I) = Normal.Cone.BundleCycles.normalConeIdeal I := by
  ext p
  change Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal I) (Deformation.Iff.BundleCycles.reesToDeformation I p) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, Deformation.Iff.BundleCycles.mem_deformationSpecialIdeal_iff,
    ReesCoefficients.BundleCycles.mem_normalConeIdeal_iff]
  constructor
  · intro h n
    have hn := h (-(n : ℤ))
    rw [Deformation.Iff.BundleCycles.reesToDeformation_coeff] at hn
    convert hn using 1
    congr 1
    omega
  · intro h n
    by_cases hn : n ≤ 0
    · have he : n = -((-n).toNat : ℤ) := by omega
      rw [he, Deformation.Iff.BundleCycles.reesToDeformation_coeff]
      convert h (-n).toNat using 1
      congr 1
      omega
    · rw [Deformation.Iff.BundleCycles.reesToDeformation_coeff_pos I p n (by omega)]
      exact Ideal.zero_mem _

/-- Truncation reads the nonnegative coefficients without alteration. -/
theorem laurentTrunc_coeff (p : LaurentPolynomial R) (n : ℕ) :
    (trunc p).coeff n = p.coeff (n : ℤ) := rfl

/-- Keep the nonpositive Laurent exponents and reverse them to Rees degrees. -/
def deformationReesTrunc (I : Ideal R) (p : Deformation.Iff.BundleCycles.deformationAlgebra I) : reesAlgebra I :=
  ⟨trunc (invert p.val), fun n => by
    rw [laurentTrunc_coeff, invert_apply]
    simpa only [neg_neg, Int.toNat_natCast] using p.property (-(n : ℤ))⟩

@[simp]
theorem deformationReesTrunc_coeff (I : Ideal R) (p : Deformation.Iff.BundleCycles.deformationAlgebra I) (n : ℕ) :
    (deformationReesTrunc I p).val.coeff n = p.val.coeff (-(n : ℤ)) := by
  change (trunc (invert p.val)).coeff n = _
  rw [laurentTrunc_coeff, invert_apply]

/-- Positive Laurent powers vanish on the special fiber. -/
theorem deformation_sub_reesTrunc_mem (I : Ideal R) (p : Deformation.Iff.BundleCycles.deformationAlgebra I) :
    p - Deformation.Iff.BundleCycles.reesToDeformation I (deformationReesTrunc I p) ∈ Deformation.Iff.BundleCycles.deformationSpecialIdeal I := by
  rw [Deformation.Iff.BundleCycles.mem_deformationSpecialIdeal_iff]
  intro n
  change p.val.coeff n - (Deformation.Iff.BundleCycles.reesToDeformation I (deformationReesTrunc I p)).val.coeff n ∈ _
  by_cases hn : n ≤ 0
  · have he : n = -((-n).toNat : ℤ) := by omega
    rw [he, Deformation.Iff.BundleCycles.reesToDeformation_coeff, deformationReesTrunc_coeff, sub_self]
    exact Ideal.zero_mem _
  · have he : (1 - n).toNat = 0 := by omega
    simp [he]

/-- Every special-fiber element has a representative in the ordinary Rees algebra. -/
theorem reesToSpecialFiber_surjective (I : Ideal R) :
    Function.Surjective (reesToSpecialFiber I) := by
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨deformationReesTrunc I p, ?_⟩
  change Ideal.Quotient.mk _ (Deformation.Iff.BundleCycles.reesToDeformation I (deformationReesTrunc I p)) =
    Ideal.Quotient.mk _ p
  symm
  exact Ideal.Quotient.eq.mpr (deformation_sub_reesTrunc_mem I p)

/-- The affine deformation's special fiber is canonically the normal cone. -/
def normalConeSpecialFiberEquiv (I : Ideal R) :
    Normal.Cone.BundleCycles.NormalConeRing I ≃+* DeformationSpecialRing I :=
  (Ideal.quotEquivOfEq (reesToSpecialFiber_ker I).symm).trans
    (RingHom.quotientKerEquivOfSurjective (reesToSpecialFiber_surjective I))

@[simp]
theorem normalConeSpecialFiberEquiv_mk (I : Ideal R) (p : reesAlgebra I) :
    normalConeSpecialFiberEquiv I (Ideal.Quotient.mk (Normal.Cone.BundleCycles.normalConeIdeal I) p) =
      Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal I) (Deformation.Iff.BundleCycles.reesToDeformation I p) := by
  exact RingHom.quotientKerEquivOfSurjective_apply_mk (reesToSpecialFiber_surjective I) p

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SpecialFiber.BundleCycles
end ComponentSource_19

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.SpecialFiber"

@[expose] public section ComponentSource_20
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Maps -/

/-! # Maps -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Maps.BundleCycles

noncomputable section

/-!
# LineBundleCycles: functoriality of affine deformation and its special fiber

A homomorphism carrying I into J induces the coefficientwise maps on the
Rees and extended Rees algebras. The resulting normal-cone and special-fiber
maps commute with the canonical special-fiber identification.
-/

universe u v w
variable {R : Type u} {S : Type v} {A : Type w}
variable [CommRing R] [CommRing S] [CommRing A]

theorem map_idealPower_mem (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) (n : ℕ) {r : R} (hr : r ∈ I ^ n) : f r ∈ J ^ n := by
  have h := Ideal.mem_map_of_mem f hr
  rw [Ideal.map_pow] at h
  exact pow_le_pow_left' (Ideal.map_le_iff_le_comap.mpr hf) n h

/-- Coefficientwise map of extended Rees algebras. -/
def deformationMap (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) : Iff.BundleCycles.deformationAlgebra I →+* Iff.BundleCycles.deformationAlgebra J where
  toFun p := ⟨AddMonoidAlgebra.mapRingHom ℤ f p.val, fun n => by
    rw [AddMonoidAlgebra.coeff_mapRingHom]
    exact map_idealPower_mem I J f hf _ (p.property n)⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' p q := Subtype.ext (map_add _ p.val q.val)
  map_mul' p q := Subtype.ext (map_mul _ p.val q.val)

@[simp]
theorem deformationMap_coeff (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) (p : Iff.BundleCycles.deformationAlgebra I) (n : ℤ) :
    (deformationMap I J f hf p).val.coeff n = f (p.val.coeff n) :=
  AddMonoidAlgebra.coeff_mapRingHom f p.val n

@[simp]
theorem deformationMap_parameter (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) :
    deformationMap I J f hf (Iff.BundleCycles.deformationParameter I) = Iff.BundleCycles.deformationParameter J := by
  apply Subtype.ext
  change AddMonoidAlgebra.mapRingHom ℤ f (AddMonoidAlgebra.single 1 1) =
    AddMonoidAlgebra.single 1 1
  rw [AddMonoidAlgebra.mapRingHom_single, map_one]

theorem deformationMap_id (I : Ideal R) :
    deformationMap I I (RingHom.id R) (by intro r hr; exact hr) =
      RingHom.id (Iff.BundleCycles.deformationAlgebra I) := by
  ext p n
  exact deformationMap_coeff I I _ _ p n

theorem deformationMap_comp (I : Ideal R) (J : Ideal S) (K : Ideal A)
    (f : R →+* S) (g : S →+* A) (hf : I ≤ J.comap f) (hg : J ≤ K.comap g) :
    (deformationMap J K g hg).comp (deformationMap I J f hf) =
      deformationMap I K (g.comp f) (fun _r hr => hg (hf hr)) := by
  ext p n
  exact ((deformationMap_coeff J K g hg _ n).trans
    (congrArg g (deformationMap_coeff I J f hf p n))).trans
      (deformationMap_coeff I K (g.comp f) (fun _r hr => hg (hf hr)) p n).symm

/-- Coefficientwise map of ordinary Rees algebras. -/
def reesMap (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) : reesAlgebra I →+* reesAlgebra J where
  toFun p := ⟨p.val.map f, fun n => by
    rw [Polynomial.coeff_map]
    exact map_idealPower_mem I J f hf n (p.property n)⟩
  map_zero' := Subtype.ext (map_zero (Polynomial.mapRingHom f))
  map_one' := Subtype.ext (map_one (Polynomial.mapRingHom f))
  map_add' p q := Subtype.ext (map_add (Polynomial.mapRingHom f) p.val q.val)
  map_mul' p q := Subtype.ext (map_mul (Polynomial.mapRingHom f) p.val q.val)

@[simp]
theorem reesMap_coeff (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) (p : reesAlgebra I) (n : ℕ) :
    (reesMap I J f hf p).val.coeff n = f (p.val.coeff n) := Polynomial.coeff_map ..

theorem reesMap_id (I : Ideal R) :
    reesMap I I (RingHom.id R) (by intro r hr; exact hr) = RingHom.id (reesAlgebra I) := by
  ext p n
  exact reesMap_coeff I I _ _ p n

theorem reesMap_comp (I : Ideal R) (J : Ideal S) (K : Ideal A)
    (f : R →+* S) (g : S →+* A) (hf : I ≤ J.comap f) (hg : J ≤ K.comap g) :
    (reesMap J K g hg).comp (reesMap I J f hf) =
      reesMap I K (g.comp f) (fun _r hr => hg (hf hr)) := by
  ext p n
  exact ((reesMap_coeff J K g hg _ n).trans
    (congrArg g (reesMap_coeff I J f hf p n))).trans
      (reesMap_coeff I K (g.comp f) (fun _r hr => hg (hf hr)) p n).symm

/-- Exponent reversal commutes with every coefficient homomorphism. -/
theorem deformationMap_reesToDeformation (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) (p : reesAlgebra I) :
    deformationMap I J f hf (Iff.BundleCycles.reesToDeformation I p) =
      Iff.BundleCycles.reesToDeformation J (reesMap I J f hf p) := by
  apply Subtype.ext
  ext n
  rw [deformationMap_coeff]
  by_cases hn : n ≤ 0
  · have he : n = -((-n).toNat : ℤ) := by omega
    rw [he, Iff.BundleCycles.reesToDeformation_coeff, Iff.BundleCycles.reesToDeformation_coeff, reesMap_coeff]
  · rw [Iff.BundleCycles.reesToDeformation_coeff_pos I p n (by omega), map_zero,
      Iff.BundleCycles.reesToDeformation_coeff_pos J _ n (by omega)]

theorem reesMap_normalConeIdeal (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) : Normal.Cone.BundleCycles.normalConeIdeal I ≤ (Normal.Cone.BundleCycles.normalConeIdeal J).comap (reesMap I J f hf) := by
  intro p hp
  rw [Ideal.mem_comap, ReesCoefficients.BundleCycles.mem_normalConeIdeal_iff]
  intro n
  rw [reesMap_coeff]
  exact map_idealPower_mem I J f hf _ ((ReesCoefficients.BundleCycles.mem_normalConeIdeal_iff I p).mp hp n)

/-- The induced homomorphism of actual normal-cone rings. -/
def normalConeMap (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : I ≤ J.comap f) :
    Normal.Cone.BundleCycles.NormalConeRing I →+* Normal.Cone.BundleCycles.NormalConeRing J :=
  Ideal.quotientMap (Normal.Cone.BundleCycles.normalConeIdeal J) (reesMap I J f hf)
    (reesMap_normalConeIdeal I J f hf)

theorem deformationMap_specialIdeal (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) :
    Iff.BundleCycles.deformationSpecialIdeal I ≤ (Iff.BundleCycles.deformationSpecialIdeal J).comap (deformationMap I J f hf) := by
  intro p hp
  rw [Ideal.mem_comap, Iff.BundleCycles.mem_deformationSpecialIdeal_iff]
  intro n
  rw [deformationMap_coeff]
  exact map_idealPower_mem I J f hf _ ((Iff.BundleCycles.mem_deformationSpecialIdeal_iff I p).mp hp n)

/-- The induced homomorphism of closed deformation fibers. -/
def deformationSpecialMap (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) : SpecialFiber.BundleCycles.DeformationSpecialRing I →+* SpecialFiber.BundleCycles.DeformationSpecialRing J :=
  Ideal.quotientMap (Iff.BundleCycles.deformationSpecialIdeal J) (deformationMap I J f hf)
    (deformationMap_specialIdeal I J f hf)

/-- Naturality of the canonical identification of the special fiber. -/
theorem normalConeSpecialFiberEquiv_natural (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) (x : Normal.Cone.BundleCycles.NormalConeRing I) :
    deformationSpecialMap I J f hf (SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv I x) =
      SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv J (normalConeMap I J f hf x) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv_mk]
  change Ideal.Quotient.mk (Iff.BundleCycles.deformationSpecialIdeal J)
      (deformationMap I J f hf (Iff.BundleCycles.reesToDeformation I p)) =
    SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv J
      (Ideal.Quotient.mk (Normal.Cone.BundleCycles.normalConeIdeal J) (reesMap I J f hf p))
  rw [SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv_mk, deformationMap_reesToDeformation]

@[simp]
theorem deformationMap_algebraMap (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) (r : R) :
    deformationMap I J f hf (algebraMap R (Iff.BundleCycles.deformationAlgebra I) r) =
      algebraMap S (Iff.BundleCycles.deformationAlgebra J) (f r) := by
  apply Subtype.ext
  exact AddMonoidAlgebra.mapRingHom_single f 0 r

@[simp]
theorem deformationMap_monomial (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) (n : ℤ) (r : R) (hr : r ∈ I ^ (-n).toNat) :
    deformationMap I J f hf (Iff.BundleCycles.deformationMonomial I n r hr) =
      Iff.BundleCycles.deformationMonomial J n (f r) (map_idealPower_mem I J f hf _ hr) := by
  apply Subtype.ext
  exact AddMonoidAlgebra.mapRingHom_single f n r

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Maps.BundleCycles
end ComponentSource_20

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Maps"

@[expose] public section ComponentSource_21
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Localization -/

/-! # Localization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Localization.BundleCycles

noncomputable section

/-!
# LineBundleCycles: localization of affine deformation algebras

The deformation algebra commutes with localization of its base ring. The
proof uses localized ideal-power membership for surjectivity and a finite
product of coefficient annihilators for injectivity. It permits zero divisors
and does not require finite generation of the ideal.
-/

open scoped BigOperators

universe u v
variable {R : Type u} [CommRing R]
variable (I : Ideal R) (M : Submonoid R)
variable (S : Type v) [CommRing S] [Algebra R S] [IsLocalization M S]

/-- The ideal after localization of the base. -/
abbrev localizedDeformationIdeal : Ideal S := I.map (algebraMap R S)

/-- Base-ring denominators viewed as constants in the deformation algebra. -/
def deformationDenominators : Submonoid (Iff.BundleCycles.deformationAlgebra I) :=
  M.map (algebraMap R (Iff.BundleCycles.deformationAlgebra I))

/-- Localization of the original deformation by base-ring denominators. -/
abbrev LocalizedDeformation := Localization (deformationDenominators I M)

/-- The coefficient map to the deformation of the localized ideal. -/
def deformationBaseMap : Iff.BundleCycles.deformationAlgebra I →+*
    Iff.BundleCycles.deformationAlgebra (localizedDeformationIdeal I S) :=
  Maps.BundleCycles.deformationMap I _ (algebraMap R S) (fun _ hr => Ideal.mem_map_of_mem _ hr)

theorem deformationBaseMap_units (m : deformationDenominators I M) :
    IsUnit (deformationBaseMap I S m) := by
  obtain ⟨r, hr, he⟩ := m.property
  change algebraMap R (Iff.BundleCycles.deformationAlgebra I) r = m.val at he
  rw [← he]
  change IsUnit (Maps.BundleCycles.deformationMap I _ (algebraMap R S) _ (algebraMap R _ r))
  exact (Maps.BundleCycles.deformationMap_algebraMap I _ (algebraMap R S) _ r).symm ▸
    (IsLocalization.map_units S (⟨r, hr⟩ : M)).map
      (algebraMap S (Iff.BundleCycles.deformationAlgebra (localizedDeformationIdeal I S)))

/-- Canonical map from the localized deformation to the deformation after
localizing its base ring. -/
def deformationLocalizationMap : LocalizedDeformation I M →+*
    Iff.BundleCycles.deformationAlgebra (localizedDeformationIdeal I S) :=
  IsLocalization.lift (deformationBaseMap_units I M S)

@[simp]
theorem deformationLocalizationMap_algebraMap (p : Iff.BundleCycles.deformationAlgebra I) :
    deformationLocalizationMap I M S (algebraMap _ (LocalizedDeformation I M) p) =
      deformationBaseMap I S p := IsLocalization.lift_eq _ p

/-- A Laurent monomial over the localized ideal lifts as a fraction of an
actual monomial over I. -/
theorem deformationLocalizationMap_monomial_mem_range (n : ℤ) (a : S)
    (ha : a ∈ localizedDeformationIdeal I S ^ (-n).toNat) :
    Iff.BundleCycles.deformationMonomial (localizedDeformationIdeal I S) n a ha ∈
      (deformationLocalizationMap I M S).rangeS := by
  have ha' : a ∈ (I ^ (-n).toNat).map (algebraMap R S) := by
    rwa [Ideal.map_pow]
  obtain ⟨⟨b, m⟩, hm⟩ := (IsLocalization.mem_map_algebraMap_iff M S).mp ha'
  let q : Iff.BundleCycles.deformationAlgebra I := Iff.BundleCycles.deformationMonomial I n b.val b.property
  let d : deformationDenominators I M :=
    ⟨algebraMap R _ m.val, Submonoid.mem_map_of_mem _ m.property⟩
  refine ⟨IsLocalization.mk' (LocalizedDeformation I M) q d, ?_⟩
  apply (IsLocalization.lift_mk'_spec (deformationBaseMap_units I M S) q _ d).mpr
  apply Subtype.ext
  change AddMonoidAlgebra.mapRingHom ℤ (algebraMap R S) (AddMonoidAlgebra.single n b.val) =
    AddMonoidAlgebra.mapRingHom ℤ (algebraMap R S) (AddMonoidAlgebra.single 0 m.val) *
      AddMonoidAlgebra.single n a
  rw [AddMonoidAlgebra.mapRingHom_single, AddMonoidAlgebra.mapRingHom_single,
    AddMonoidAlgebra.single_mul_single, zero_add, ← hm, mul_comm a]

/-- Every element of the deformation over the localized base has a preimage. -/
theorem deformationLocalizationMap_surjective :
    Function.Surjective (deformationLocalizationMap I M S) := by
  classical
  intro p
  have he : p = ∑ n ∈ p.val.coeff.support,
      Iff.BundleCycles.deformationMonomial (localizedDeformationIdeal I S) n (p.val.coeff n) (p.property n) := by
    apply Subtype.ext
    change p.val = (Iff.BundleCycles.deformationAlgebra (localizedDeformationIdeal I S)).val
      (∑ n ∈ p.val.coeff.support, Iff.BundleCycles.deformationMonomial _ n _ (p.property n))
    rw [map_sum]
    exact (AddMonoidAlgebra.sum_coeff_single p.val).symm
  have hp : p ∈ (deformationLocalizationMap I M S).rangeS := by
    rw [he]
    exact Subsemiring.sum_mem _ fun n _ =>
      deformationLocalizationMap_monomial_mem_range I M S n _ (p.property n)
  exact hp

/-- A coefficientwise zero after localization is annihilated by one common
base denominator. The product is finite because the Laurent support is finite. -/
theorem deformationBaseMap_zero_denominator (p : Iff.BundleCycles.deformationAlgebra I)
    (hp : deformationBaseMap I S p = 0) :
    ∃ m : M, algebraMap R (Iff.BundleCycles.deformationAlgebra I) m.val * p = 0 := by
  classical
  have hc (n : ℤ) : algebraMap R S (p.val.coeff n) = 0 := by
    have h := congrArg (fun q : Iff.BundleCycles.deformationAlgebra (localizedDeformationIdeal I S) =>
      q.val.coeff n) hp
    exact h
  have hm (n : ℤ) := (IsLocalization.map_eq_zero_iff M S (p.val.coeff n)).mp (hc n)
  choose m hm using hm
  let d : M := ∏ n ∈ p.val.coeff.support, m n
  refine ⟨d, Subtype.ext ?_⟩
  ext n
  change (AddMonoidAlgebra.single 0 d.val * p.val).coeff n = 0
  rw [AddMonoidAlgebra.coeff_single_mul_apply, neg_zero, zero_add]
  by_cases hn : n ∈ p.val.coeff.support
  · obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem m hn
    have hd : d = m n * c := hc
    change d.val * p.val.coeff n = 0
    rw [hd]
    change (m n).val * c.val * p.val.coeff n = 0
    rw [mul_right_comm, hm n, zero_mul]
  · rw [Finsupp.notMem_support_iff.mp hn, mul_zero]

/-- No additional relations appear under the coefficientwise localization. -/
theorem deformationLocalizationMap_injective :
    Function.Injective (deformationLocalizationMap I M S) := by
  apply (IsLocalization.lift_injective_iff (deformationBaseMap_units I M S)).mpr
  intro p q
  constructor
  · intro h
    exact (deformationLocalizationMap_algebraMap I M S p).symm.trans
      ((congrArg (deformationLocalizationMap I M S) h).trans
        (deformationLocalizationMap_algebraMap I M S q))
  · intro h
    have hz : deformationBaseMap I S (p - q) = 0 := by
      rw [map_sub, h, sub_self]
    obtain ⟨m, hm⟩ := deformationBaseMap_zero_denominator I M S (p - q) hz
    apply (IsLocalization.eq_iff_exists (deformationDenominators I M)
      (LocalizedDeformation I M)).mpr
    refine ⟨⟨algebraMap R _ m.val, Submonoid.mem_map_of_mem _ m.property⟩, ?_⟩
    exact sub_eq_zero.mp ((mul_sub _ p q).symm.trans hm)

/-- Formation of the extended Rees algebra commutes with arbitrary base
localization. In particular it commutes with affine basic-open restriction. -/
def deformationLocalizationEquiv : LocalizedDeformation I M ≃+*
    Iff.BundleCycles.deformationAlgebra (localizedDeformationIdeal I S) :=
  RingEquiv.ofBijective (deformationLocalizationMap I M S)
    ⟨deformationLocalizationMap_injective I M S, deformationLocalizationMap_surjective I M S⟩

@[simp]
theorem deformationLocalizationEquiv_algebraMap (p : Iff.BundleCycles.deformationAlgebra I) :
    deformationLocalizationEquiv I M S (algebraMap _ (LocalizedDeformation I M) p) =
      deformationBaseMap I S p := deformationLocalizationMap_algebraMap I M S p

/-- The coefficient map exhibits the localized deformation as a localization,
with its specified algebra structure. -/
theorem deformationBaseMap_isLocalization :
    letI := (deformationBaseMap I S).toAlgebra
    IsLocalization (deformationDenominators I M)
      (Iff.BundleCycles.deformationAlgebra (localizedDeformationIdeal I S)) := by
  let := (deformationBaseMap I S).toAlgebra
  let e : LocalizedDeformation I M ≃ₐ[Iff.BundleCycles.deformationAlgebra I]
      Iff.BundleCycles.deformationAlgebra (localizedDeformationIdeal I S) :=
    { deformationLocalizationEquiv I M S with
      commutes' := deformationLocalizationEquiv_algebraMap I M S }
  exact IsLocalization.isLocalization_of_algEquiv (deformationDenominators I M) e

/-- Localization comparison for an ideal presented by an equality, as occurs
when restricting an ideal sheaf to an affine basic open. -/
theorem deformationMap_isLocalization (J : Ideal S)
    (hJ : I.map (algebraMap R S) = J) (hf : I ≤ J.comap (algebraMap R S)) :
    letI := (Maps.BundleCycles.deformationMap I J (algebraMap R S) hf).toAlgebra
    IsLocalization (deformationDenominators I M) (Iff.BundleCycles.deformationAlgebra J) := by
  subst J
  exact deformationBaseMap_isLocalization I M S

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Localization.BundleCycles
end ComponentSource_21

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Localization"

@[expose] public section ComponentSource_22
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Global.Deformation -/

/-! # Deformation -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.Deformation.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the global deformation scheme of an ideal sheaf

On each affine open U, take Spec(Γ(U)[t,I(U)/t]). The coefficient restriction
maps form a functor, and the proved localization comparison makes its
structure transformation coequifibered. Relative gluing therefore constructs
an actual scheme over X, with the affine deformation charts as its inverse
images. Specialization on cycles is not included in this construction.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

universe u
variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The coefficientwise extended Rees diagram on the affine Zariski site. -/
def deformationDiagram : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat where
  obj U := CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U.unop))
  map {U V} f := CommRingCat.ofHom
    (Deformation.Maps.BundleCycles.deformationMap (I.ideal U.unop) (I.ideal V.unop)
      (X.presheaf.map ((toOpensFunctor X).op.map f)).hom
      (I.ideal_le_comap_ideal (toOpens_mono f.unop.le)))
  map_id U := by
    apply CommRingCat.hom_ext
    ext p n
    have h : (X.presheaf.map ((toOpensFunctor X).op.map (𝟙 U))).hom =
        RingHom.id Γ(X, U.unop.1) :=
      congrArg CommRingCat.Hom.hom (((toOpensFunctor X).op ⋙ X.presheaf).map_id U)
    change (AddMonoidAlgebra.mapRingHom ℤ
      (X.presheaf.map ((toOpensFunctor X).op.map (𝟙 U))).hom p.val).coeff n = p.val.coeff n
    exact (AddMonoidAlgebra.coeff_mapRingHom
      (X.presheaf.map ((toOpensFunctor X).op.map (𝟙 U))).hom p.val n).trans
        (DFunLike.congr_fun h _)
  map_comp {U V W} f g := by
    apply CommRingCat.hom_ext
    ext p n
    have h : (X.presheaf.map ((toOpensFunctor X).op.map (f ≫ g))).hom =
        ((X.presheaf.map ((toOpensFunctor X).op.map g)).hom).comp
          (X.presheaf.map ((toOpensFunctor X).op.map f)).hom :=
      congrArg CommRingCat.Hom.hom (((toOpensFunctor X).op ⋙ X.presheaf).map_comp f g)
    change (AddMonoidAlgebra.mapRingHom ℤ
      (X.presheaf.map ((toOpensFunctor X).op.map (f ≫ g))).hom p.val).coeff n =
      (AddMonoidAlgebra.mapRingHom ℤ (X.presheaf.map ((toOpensFunctor X).op.map g)).hom
        (AddMonoidAlgebra.mapRingHom ℤ (X.presheaf.map ((toOpensFunctor X).op.map f)).hom
          p.val)).coeff n
    simp only [AddMonoidAlgebra.coeff_mapRingHom]
    exact DFunLike.congr_fun h _

/-- Constants provide the map from the structure presheaf to the deformation. -/
def deformationDiagramMap : (toOpensFunctor X).op ⋙ X.presheaf ⟶ deformationDiagram I where
  app U := CommRingCat.ofHom (algebraMap Γ(X, U.unop.1) (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U.unop)))
  naturality {U V} f := by
    apply CommRingCat.hom_ext
    ext r : 1
    exact (Deformation.Maps.BundleCycles.deformationMap_algebraMap (I.ideal U.unop) (I.ideal V.unop)
      (X.presheaf.map ((toOpensFunctor X).op.map f)).hom
      (I.ideal_le_comap_ideal (toOpens_mono f.unop.le)) r).symm

/-- The affine diagram preserves restriction to every principal open. -/
theorem deformationDiagramMap_coequifibered : (deformationDiagramMap I).Coequifibered := by
  apply coequifibered_iff_forall_isLocalizationAway.mpr
  intro U r
  let V : X.AffineZariskiSite := U.basicOpen r
  let f : Γ(X, U.1) →+* Γ(X, V.1) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
  let : Algebra Γ(X, U.1) Γ(X, V.1) := f.toAlgebra
  have : IsLocalization.Away r Γ(X, V.1) := U.2.isLocalization_basicOpen r
  have hI : (I.ideal U).map (algebraMap Γ(X, U.1) Γ(X, V.1)) = I.ideal V :=
    I.map_ideal_basicOpen U r
  have h := Deformation.Localization.BundleCycles.deformationMap_isLocalization (I.ideal U) (Submonoid.powers r) Γ(X, V.1)
    (I.ideal V) hI (I.ideal_le_comap_ideal (X.basicOpen_le r))
  let : Algebra (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U)) (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal V)) :=
    (Deformation.Maps.BundleCycles.deformationMap (I.ideal U) (I.ideal V) f
      (I.ideal_le_comap_ideal (X.basicOpen_le r))).toAlgebra
  change IsLocalization.Away (algebraMap Γ(X, U.1) (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U)) r)
    (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal V))
  simpa only [Deformation.Localization.BundleCycles.deformationDenominators, Submonoid.map_powers] using h

/-- Relative gluing datum whose affine pieces are the actual deformations. -/
def deformationGlueData : (directedCover X).RelativeGluingData :=
  relativeGluingData (deformationDiagramMap_coequifibered I)

instance deformationGlueData_isLocallyDirected :
    ((deformationGlueData I).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- The global deformation to the normal cone of the ideal sheaf I. -/
def globalDeformation : Scheme := (deformationGlueData I).glued

/-- The deformation's structural projection to its original scheme. -/
def globalDeformationProjection : globalDeformation I ⟶ X :=
  (deformationGlueData I).toBase

/-- The affine deformation charts cover the glued scheme. -/
def globalDeformationCover : (globalDeformation I).OpenCover :=
  (deformationGlueData I).cover

/-- The chart over an affine open is its actual extended-Rees spectrum. -/
theorem globalDeformationCover_obj (U : X.AffineZariskiSite) :
    (globalDeformationCover I).X U = Spec (CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U))) := rfl

/-- Each affine deformation chart is exactly the inverse image of the
corresponding affine open in X. -/
theorem globalDeformation_chart_isPullback (U : X.AffineZariskiSite) :
    IsPullback ((deformationGlueData I).natTrans.app U) ((globalDeformationCover I).f U)
      U.1.ι (globalDeformationProjection I) :=
  (deformationGlueData I).isPullback_natTrans_ι_toBase U

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.Deformation.BundleCycles
end ComponentSource_22

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Global.Deformation"

@[expose] public section ComponentSource_23
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.QuotientLocalization -/

/-! # Quotient Localization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.QuotientLocalization.BundleCycles

noncomputable section

/-!
# LineBundleCycles: localization of a quotient ring

Quotienting by an ideal commutes with localization. The proof follows
numerators and denominators explicitly and will be applied to the parameter
ideal of the deformation, in order to glue its normal-cone fibers.
-/

universe u v
variable {R : Type u} [CommRing R] (M : Submonoid R)
variable (S : Type v) [CommRing S] [Algebra R S] [IsLocalization M S]

/-- The actual quotient map induced by localization of coefficients. -/
def quotientLocalizationMap (I : Ideal R) : R ⧸ I →+* S ⧸ I.map (algebraMap R S) :=
  Ideal.quotientMap _ (algebraMap R S) (fun _ hr => Ideal.mem_map_of_mem _ hr)

@[simp]
theorem quotientLocalizationMap_mk (I : Ideal R) (r : R) :
    quotientLocalizationMap S I (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk (I.map (algebraMap R S)) (algebraMap R S r) := rfl

/-- The quotient after localization is a localization of the original quotient. -/
theorem quotientLocalizationMap_isLocalization (I : Ideal R) :
    letI := (quotientLocalizationMap S I).toAlgebra
    IsLocalization (M.map (Ideal.Quotient.mk I)) (S ⧸ I.map (algebraMap R S)) := by
  let := (quotientLocalizationMap S I).toAlgebra
  let J := I.map (algebraMap R S)
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · rintro ⟨q, ⟨m, hm, rfl⟩⟩
    change IsUnit (Ideal.Quotient.mk J (algebraMap R S m))
    exact (IsLocalization.map_units S (⟨m, hm⟩ : M)).map (Ideal.Quotient.mk J)
  · intro q
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨⟨x, m⟩, he⟩ := IsLocalization.surj M y
    refine ⟨(Ideal.Quotient.mk I x,
      ⟨Ideal.Quotient.mk I m.val, Submonoid.mem_map_of_mem _ m.property⟩), ?_⟩
    change Ideal.Quotient.mk J y * Ideal.Quotient.mk J (algebraMap R S m.val) =
      Ideal.Quotient.mk J (algebraMap R S x)
    exact (map_mul (Ideal.Quotient.mk J) y (algebraMap R S m.val)).symm.trans
      (congrArg (Ideal.Quotient.mk J) he)
  · intro p q he
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective p
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    have hxy : algebraMap R S (x - y) ∈ J := by
      rw [map_sub]
      exact Ideal.Quotient.eq.mp he
    obtain ⟨m, hm, hmem⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff M S I (x - y)).mp hxy
    refine ⟨⟨Ideal.Quotient.mk I m, Submonoid.mem_map_of_mem _ hm⟩, ?_⟩
    change Ideal.Quotient.mk I m * Ideal.Quotient.mk I x =
      Ideal.Quotient.mk I m * Ideal.Quotient.mk I y
    rw [← map_mul, ← map_mul]
    apply Ideal.Quotient.eq.mpr
    exact (mul_sub m x y) ▸ hmem

/-- The same localization statement with the target ideal supplied by its
actual image equality, as needed for gluing affine ideal presentations. -/
theorem quotientMap_isLocalization (I : Ideal R) (J : Ideal S)
    (hJ : I.map (algebraMap R S) = J) (hIJ : I ≤ J.comap (algebraMap R S)) :
    letI := (Ideal.quotientMap J (algebraMap R S) hIJ).toAlgebra
    IsLocalization (M.map (Ideal.Quotient.mk I)) (S ⧸ J) := by
  subst J
  exact quotientLocalizationMap_isLocalization M S I

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.QuotientLocalization.BundleCycles
end ComponentSource_23

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.QuotientLocalization"

@[expose] public section ComponentSource_24
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.SpecialFiberLocalization -/

/-! # Special Fiber Localization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SpecialFiberLocalization.BundleCycles

noncomputable section

/-!
# LineBundleCycles: localization of the special fiber

The parameter ideal maps to the parameter ideal under every coefficient
homomorphism. Combining the proved deformation localization with quotient
localization shows that the special-fiber rings also commute with base
localization. This is the remaining affine input for gluing the cone fibers.
-/

universe u v
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The defining equation of the special fiber is preserved, including its ideal. -/
theorem deformationSpecialIdeal_map (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : I ≤ J.comap f) :
    (Deformation.Iff.BundleCycles.deformationSpecialIdeal I).map (Deformation.Maps.BundleCycles.deformationMap I J f hf) = Deformation.Iff.BundleCycles.deformationSpecialIdeal J := by
  unfold Deformation.Iff.BundleCycles.deformationSpecialIdeal
  rw [Ideal.map_span, Set.image_singleton, Deformation.Maps.BundleCycles.deformationMap_parameter]

variable (I : Ideal R) (M : Submonoid R) (S)
variable [Algebra R S] [IsLocalization M S]

/-- The special fiber over a localized base is the localization of the original
special fiber by the same base denominators. -/
theorem deformationSpecialMap_isLocalization (J : Ideal S)
    (hJ : I.map (algebraMap R S) = J) (hIJ : I ≤ J.comap (algebraMap R S)) :
    letI : Algebra (SpecialFiber.BundleCycles.DeformationSpecialRing I) (SpecialFiber.BundleCycles.DeformationSpecialRing J) :=
      @RingHom.toAlgebra (SpecialFiber.BundleCycles.DeformationSpecialRing I) (SpecialFiber.BundleCycles.DeformationSpecialRing J)
        (by infer_instance) (by infer_instance) (Deformation.Maps.BundleCycles.deformationSpecialMap I J (algebraMap R S) hIJ)
    @IsLocalization (SpecialFiber.BundleCycles.DeformationSpecialRing I) (by infer_instance)
      (@Submonoid.map (Deformation.Iff.BundleCycles.deformationAlgebra I) (SpecialFiber.BundleCycles.DeformationSpecialRing I)
        (by infer_instance) (by infer_instance) (Deformation.Iff.BundleCycles.deformationAlgebra I →* SpecialFiber.BundleCycles.DeformationSpecialRing I)
        (by infer_instance) (by infer_instance) (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal I)).toMonoidHom
        (Deformation.Localization.BundleCycles.deformationDenominators I M))
      (SpecialFiber.BundleCycles.DeformationSpecialRing J) (by infer_instance) (by infer_instance) := by
  let : Algebra (Deformation.Iff.BundleCycles.deformationAlgebra I) (Deformation.Iff.BundleCycles.deformationAlgebra J) :=
    (Deformation.Maps.BundleCycles.deformationMap I J (algebraMap R S) hIJ).toAlgebra
  have : IsLocalization (Deformation.Localization.BundleCycles.deformationDenominators I M) (Deformation.Iff.BundleCycles.deformationAlgebra J) :=
    Deformation.Localization.BundleCycles.deformationMap_isLocalization I M S J hJ hIJ
  exact QuotientLocalization.BundleCycles.quotientMap_isLocalization (Deformation.Localization.BundleCycles.deformationDenominators I M) (Deformation.Iff.BundleCycles.deformationAlgebra J)
    (Deformation.Iff.BundleCycles.deformationSpecialIdeal I) (Deformation.Iff.BundleCycles.deformationSpecialIdeal J)
    (deformationSpecialIdeal_map I J (algebraMap R S) hIJ)
    (Deformation.Maps.BundleCycles.deformationMap_specialIdeal I J (algebraMap R S) hIJ)

/-- Constants in the closed fiber provide its map from the original affine base. -/
def specialFiberBaseMap (I : Ideal R) : R →+* SpecialFiber.BundleCycles.DeformationSpecialRing I :=
  (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal I)).comp (algebraMap R (Deformation.Iff.BundleCycles.deformationAlgebra I))

/-- Special-fiber restriction to a principal affine open is localization
at the image of the same regular function. -/
theorem deformationSpecialMap_isLocalization_away (r : R)
    [IsLocalization.Away r S] (J : Ideal S)
    (hJ : I.map (algebraMap R S) = J) (hIJ : I ≤ J.comap (algebraMap R S)) :
    letI : Algebra (SpecialFiber.BundleCycles.DeformationSpecialRing I) (SpecialFiber.BundleCycles.DeformationSpecialRing J) :=
      @RingHom.toAlgebra (SpecialFiber.BundleCycles.DeformationSpecialRing I) (SpecialFiber.BundleCycles.DeformationSpecialRing J)
        (by infer_instance) (by infer_instance) (Deformation.Maps.BundleCycles.deformationSpecialMap I J (algebraMap R S) hIJ)
    IsLocalization.Away (specialFiberBaseMap I r) (SpecialFiber.BundleCycles.DeformationSpecialRing J) := by
  let : Algebra (SpecialFiber.BundleCycles.DeformationSpecialRing I) (SpecialFiber.BundleCycles.DeformationSpecialRing J) :=
    @RingHom.toAlgebra (SpecialFiber.BundleCycles.DeformationSpecialRing I) (SpecialFiber.BundleCycles.DeformationSpecialRing J)
      (by infer_instance) (by infer_instance) (Deformation.Maps.BundleCycles.deformationSpecialMap I J (algebraMap R S) hIJ)
  have h := deformationSpecialMap_isLocalization (I := I) (M := Submonoid.powers r) (S := S) J hJ hIJ
  change IsLocalization.Away
    (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal I) (algebraMap R (Deformation.Iff.BundleCycles.deformationAlgebra I) r))
      (SpecialFiber.BundleCycles.DeformationSpecialRing J)
  simp only [Deformation.Localization.BundleCycles.deformationDenominators, Submonoid.map_powers] at h
  exact h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SpecialFiberLocalization.BundleCycles
end ComponentSource_24

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.SpecialFiberLocalization"

@[expose] public section ComponentSource_25
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SpecialFiber -/

/-! # Special Fiber -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SpecialFiber.BundleCycles

noncomputable section

/-!
# LineBundleCycles: gluing the affine special fibers

The quotients R[t,I/t]/(t) form an actual affine-site diagram. Their base
localization property is proved, so relative gluing assembles a scheme over
X. The quotient maps also glue to a morphism into the global deformation.
Each affine chart is the already identified normal-cone algebra.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

universe u

/-- Closed immersions descend from a target open cover and explicit pullback charts. -/
theorem isClosedImmersion_of_cover_pullbacks {A B : Scheme.{u}} (f : A ⟶ B)
    (C : B.OpenCover) (Z : C.I₀ → Scheme.{u}) (a : ∀ i, Z i ⟶ A)
    (b : ∀ i, Z i ⟶ C.X i)
    (h : ∀ i, IsPullback (b i) (a i) (C.f i) f)
    (hb : ∀ i, IsClosedImmersion (b i)) : IsClosedImmersion f := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) C
  intro i
  let hi := (h i).flip
  let := hb i
  have hc : IsClosedImmersion (hi.isoPullback.inv ≫ b i) :=
    IsClosedImmersion.comp hi.isoPullback.inv (b i)
  exact (congrArg (fun k => IsClosedImmersion k) hi.isoPullback_inv_snd).mp hc

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The actual special-fiber quotient rings and coefficient restriction maps. -/
def specialFiberDiagram : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat where
  obj U := CommRingCat.of (SpecialFiber.BundleCycles.DeformationSpecialRing (I.ideal U.unop))
  map {U V} f := CommRingCat.ofHom
    (Deformation.Maps.BundleCycles.deformationSpecialMap (I.ideal U.unop) (I.ideal V.unop)
      (X.presheaf.map ((toOpensFunctor X).op.map f)).hom
      (I.ideal_le_comap_ideal (toOpens_mono f.unop.le)))
  map_id U := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext p : 1
    change Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (I.ideal U.unop))
        ((Deformation.BundleCycles.deformationDiagram I).map (𝟙 U) p) =
      Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (I.ideal U.unop)) p
    exact congrArg (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (I.ideal U.unop)))
      (ConcreteCategory.congr_hom ((Deformation.BundleCycles.deformationDiagram I).map_id U) p)
  map_comp {U V W} f g := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext p : 1
    change Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (I.ideal W.unop))
        ((Deformation.BundleCycles.deformationDiagram I).map (f ≫ g) p) =
      Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (I.ideal W.unop))
        ((Deformation.BundleCycles.deformationDiagram I).map g ((Deformation.BundleCycles.deformationDiagram I).map f p))
    exact congrArg (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (I.ideal W.unop)))
      (ConcreteCategory.congr_hom ((Deformation.BundleCycles.deformationDiagram I).map_comp f g) p)

/-- The actual quotient maps form a natural transformation of affine diagrams. -/
def deformationToSpecialDiagram : Deformation.BundleCycles.deformationDiagram I ⟶ specialFiberDiagram I where
  app U := CommRingCat.ofHom (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (I.ideal U.unop)))
  naturality {U V} f := by
    apply CommRingCat.hom_ext
    ext p : 1
    rfl

/-- Constants give the structure map of the special-fiber diagram over X. -/
def specialFiberDiagramMap : (toOpensFunctor X).op ⋙ X.presheaf ⟶ specialFiberDiagram I :=
  Deformation.BundleCycles.deformationDiagramMap I ≫ deformationToSpecialDiagram I

/-- The special-fiber diagram is compatible with affine basic-open restriction. -/
theorem specialFiberDiagramMap_coequifibered : (specialFiberDiagramMap I).Coequifibered := by
  apply coequifibered_iff_forall_isLocalizationAway.mpr
  intro U r
  let V : X.AffineZariskiSite := U.basicOpen r
  let f : Γ(X, U.1) →+* Γ(X, V.1) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
  let : Algebra Γ(X, U.1) Γ(X, V.1) := f.toAlgebra
  have : IsLocalization.Away r Γ(X, V.1) := U.2.isLocalization_basicOpen r
  have hI : (I.ideal U).map (algebraMap Γ(X, U.1) Γ(X, V.1)) = I.ideal V :=
    I.map_ideal_basicOpen U r
  exact SpecialFiberLocalization.BundleCycles.deformationSpecialMap_isLocalization_away (I := I.ideal U) (S := Γ(X, V.1)) r
    (I.ideal V) hI (I.ideal_le_comap_ideal (X.basicOpen_le r))

/-- Relative gluing data for the actual t = 0 fibers. -/
def specialFiberGlueData : (directedCover X).RelativeGluingData :=
  relativeGluingData (specialFiberDiagramMap_coequifibered I)

instance specialFiberGlueData_isLocallyDirected :
    ((specialFiberGlueData I).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- The scheme obtained by gluing the actual affine special fibers. -/
def globalSpecialFiber : Scheme := (specialFiberGlueData I).glued

def globalSpecialFiberProjection : globalSpecialFiber I ⟶ X :=
  (specialFiberGlueData I).toBase

def globalSpecialFiberCover : (globalSpecialFiber I).OpenCover :=
  (specialFiberGlueData I).cover

/-- Each glued fiber chart has the canonical affine normal-cone presentation. -/
def globalSpecialFiberNormalConeChart (U : X.AffineZariskiSite) :
    Normal.Cone.BundleCycles.affineNormalCone (I.ideal U) ≅ (globalSpecialFiberCover I).X U :=
  Scheme.Spec.mapIso (SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv (I.ideal U)).toCommRingCatIso.symm.op

/-- Each fiber chart is the inverse image of its affine open in the original base. -/
theorem globalSpecialFiber_chart_isPullback (U : X.AffineZariskiSite) :
    IsPullback ((specialFiberGlueData I).natTrans.app U) ((globalSpecialFiberCover I).f U)
      U.1.ι (globalSpecialFiberProjection I) :=
  (specialFiberGlueData I).isPullback_natTrans_ι_toBase U

/-- Quotient maps followed by the deformation chart inclusions are compatible. -/
def globalSpecialFiberMapCocone : Cocone (specialFiberGlueData I).functor where
  pt := Deformation.BundleCycles.globalDeformation I
  ι := Functor.whiskerRight (deformationToSpecialDiagram I).rightOp Scheme.Spec ≫
    (colimit.cocone (Deformation.BundleCycles.deformationGlueData I).functor).ι

/-- The global morphism induced by all actual affine special-fiber inclusions. -/
def globalSpecialFiberMap : globalSpecialFiber I ⟶ Deformation.BundleCycles.globalDeformation I :=
  colimit.desc _ (globalSpecialFiberMapCocone I)

/-- Its restriction to a fiber chart is the actual quotient spectrum map. -/
theorem globalSpecialFiberMap_on_chart (U : X.AffineZariskiSite) :
    (globalSpecialFiberCover I).f U ≫ globalSpecialFiberMap I =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (I.ideal U)))) ≫
        (Deformation.BundleCycles.globalDeformationCover I).f U :=
  colimit.ι_desc (globalSpecialFiberMapCocone I) U

/-- The affine quotient map commutes with the structure morphisms to the base open. -/
theorem specialFiber_chart_toBase (U : X.AffineZariskiSite) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (I.ideal U)))) ≫
        (Deformation.BundleCycles.deformationGlueData I).natTrans.app U =
      (specialFiberGlueData I).natTrans.app U := by
  change Spec.map ((deformationToSpecialDiagram I).app (.op U)) ≫
      (Spec.map ((Deformation.BundleCycles.deformationDiagramMap I).app (.op U)) ≫
        (restrictIsoSpec X).inv.app U) =
    Spec.map ((specialFiberDiagramMap I).app (.op U)) ≫
      (restrictIsoSpec X).inv.app U
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

/-- The global special-fiber inclusion is a morphism over the original scheme. -/
theorem globalSpecialFiberMap_toBase :
    globalSpecialFiberMap I ≫ Deformation.BundleCycles.globalDeformationProjection I =
      globalSpecialFiberProjection I := by
  apply (globalSpecialFiberCover I).hom_ext
  intro U
  let q : (globalSpecialFiberCover I).X U ⟶ (Deformation.BundleCycles.globalDeformationCover I).X U :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (I.ideal U))))
  have hd : (Deformation.BundleCycles.globalDeformationCover I).f U ≫ Deformation.BundleCycles.globalDeformationProjection I =
      (Deformation.BundleCycles.deformationGlueData I).natTrans.app U ≫ U.1.ι :=
    (Deformation.BundleCycles.deformationGlueData I).ι_toBase U
  have hs : (globalSpecialFiberCover I).f U ≫ globalSpecialFiberProjection I =
      (specialFiberGlueData I).natTrans.app U ≫ U.1.ι :=
    (specialFiberGlueData I).ι_toBase U
  have hq : q ≫ (Deformation.BundleCycles.deformationGlueData I).natTrans.app U =
      (specialFiberGlueData I).natTrans.app U := specialFiber_chart_toBase I U
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ Deformation.BundleCycles.globalDeformationProjection I)
      (globalSpecialFiberMap_on_chart I U)).trans
    ((Category.assoc q _ _).trans
    ((congrArg (fun k => q ≫ k) hd).trans
    ((Category.assoc q _ _).symm.trans
    ((congrArg (fun k => k ≫ U.1.ι) hq).trans hs.symm)))))

/-- Restricting the global inclusion to any deformation chart gives its quotient map. -/
theorem globalSpecialFiberMap_chart_isPullback (U : X.AffineZariskiSite) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (I.ideal U)))))
      ((globalSpecialFiberCover I).f U) ((Deformation.BundleCycles.globalDeformationCover I).f U)
      (globalSpecialFiberMap I) := by
  have h := globalSpecialFiber_chart_isPullback I U
  rw [← specialFiber_chart_toBase I U, ← globalSpecialFiberMap_toBase I] at h
  exact h.of_right (globalSpecialFiberMap_on_chart I U).symm
    (Deformation.BundleCycles.globalDeformation_chart_isPullback I U)

/-- The glued special fiber is a genuine closed subscheme of the deformation. -/
instance globalSpecialFiberMap_isClosedImmersion :
    IsClosedImmersion (globalSpecialFiberMap I) := by
  apply isClosedImmersion_of_cover_pullbacks (globalSpecialFiberMap I)
    (Deformation.BundleCycles.globalDeformationCover I) (globalSpecialFiberCover I).X
    (globalSpecialFiberCover I).f
    (fun U => Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (I.ideal U)))))
    (globalSpecialFiberMap_chart_isPullback I)
  intro U
  have hsurj : Function.Surjective
      (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (I.ideal U))) :=
    Ideal.Quotient.mk_surjective
  exact IsClosedImmersion.spec_of_surjective
    (R := CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U)))
    (S := CommRingCat.of (SpecialFiber.BundleCycles.DeformationSpecialRing (I.ideal U)))
    (CommRingCat.ofHom (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (I.ideal U)))) hsurj

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SpecialFiber.BundleCycles
end ComponentSource_25

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SpecialFiber"

@[expose] public section ComponentSource_26
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.AffineMap -/

/-! # Affine Map -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.AffineMap.BundleCycles

noncomputable section

/-!
# LineBundleCycles: maps between affine schemes glued over a common base

A natural transformation of the actual affine algebras induces a morphism
of the glued schemes. Compatibility with constants proves that this is a
morphism over the base and that its restrictions are pullback charts.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

universe u
variable {X : Scheme.{u}} {F G : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat}
variable {α : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F}
variable {β : (toOpensFunctor X).op ⋙ X.presheaf ⟶ G}
variable (hα : α.Coequifibered) (hβ : β.Coequifibered)

instance relativeAffineGlueData_isLocallyDirected :
    ((relativeGluingData hα).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- Compatible affine spectrum maps into the gluing of the target charts. -/
def relativeAffineMapCocone (η : F ⟶ G) : Cocone (relativeGluingData hβ).functor where
  pt := (relativeGluingData hα).glued
  ι := Functor.whiskerRight η.rightOp Scheme.Spec ≫
    (colimit.cocone (relativeGluingData hα).functor).ι

/-- The morphism induced by a natural transformation of the affine algebras. -/
def relativeAffineMap (η : F ⟶ G) :
    (relativeGluingData hβ).glued ⟶ (relativeGluingData hα).glued :=
  colimit.desc _ (relativeAffineMapCocone hα hβ η)

theorem relativeAffineMap_on_chart (η : F ⟶ G) (U : X.AffineZariskiSite) :
    (relativeGluingData hβ).cover.f U ≫ relativeAffineMap hα hβ η =
      Spec.map (η.app (.op U)) ≫ (relativeGluingData hα).cover.f U :=
  colimit.ι_desc (relativeAffineMapCocone hα hβ η) U

variable (η : F ⟶ G) (hη : α ≫ η = β)
include hη

theorem relativeAffineMap_chart_toBase (U : X.AffineZariskiSite) :
    Spec.map (η.app (.op U)) ≫ (relativeGluingData hα).natTrans.app U =
      (relativeGluingData hβ).natTrans.app U := by
  change Spec.map (η.app (.op U)) ≫
      (Spec.map (α.app (.op U)) ≫ (restrictIsoSpec X).inv.app U) =
    Spec.map (β.app (.op U)) ≫ (restrictIsoSpec X).inv.app U
  rw [← Category.assoc, ← Spec.map_comp]
  exact congrArg (fun a => Spec.map a ≫ (restrictIsoSpec X).inv.app U)
    (congrArg (fun γ => γ.app (.op U)) hη)

/-- The map of gluings respects the specified structure maps to the common base. -/
theorem relativeAffineMap_toBase :
    relativeAffineMap hα hβ η ≫ (relativeGluingData hα).toBase =
      (relativeGluingData hβ).toBase := by
  apply (relativeGluingData hβ).cover.hom_ext
  intro U
  let q : (relativeGluingData hβ).cover.X U ⟶ (relativeGluingData hα).cover.X U :=
    Spec.map (η.app (.op U))
  have hd := (relativeGluingData hα).ι_toBase U
  have hs := (relativeGluingData hβ).ι_toBase U
  have hq : q ≫ (relativeGluingData hα).natTrans.app U =
      (relativeGluingData hβ).natTrans.app U := relativeAffineMap_chart_toBase hα hβ η hη U
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ (relativeGluingData hα).toBase)
      (relativeAffineMap_on_chart hα hβ η U)).trans
    ((Category.assoc q _ _).trans
    ((congrArg (fun k => q ≫ k) hd).trans
    ((Category.assoc q _ _).symm.trans
    ((congrArg (fun k => k ≫ (directedCover X).f U) hq).trans hs.symm)))))

/-- Each affine map is precisely the pullback of the global morphism to that target chart. -/
theorem relativeAffineMap_chart_isPullback (U : X.AffineZariskiSite) :
    IsPullback (Spec.map (η.app (.op U))) ((relativeGluingData hβ).cover.f U)
      ((relativeGluingData hα).cover.f U) (relativeAffineMap hα hβ η) := by
  have h := (relativeGluingData hβ).isPullback_natTrans_ι_toBase U
  rw [← relativeAffineMap_chart_toBase hα hβ η hη U,
    ← relativeAffineMap_toBase hα hβ η hη] at h
  exact h.of_right (relativeAffineMap_on_chart hα hβ η U).symm
    ((relativeGluingData hα).isPullback_natTrans_ι_toBase U)

/-- Surjective affine algebra maps glue to a closed immersion. -/
theorem relativeAffineMap_isClosedImmersion
    (hsurj : ∀ U : X.AffineZariskiSite, Function.Surjective (η.app (.op U))) :
    IsClosedImmersion (relativeAffineMap hα hβ η) := by
  apply Global.SpecialFiber.BundleCycles.isClosedImmersion_of_cover_pullbacks (relativeAffineMap hα hβ η)
    (relativeGluingData hα).cover (relativeGluingData hβ).cover.X
    (relativeGluingData hβ).cover.f (fun U => Spec.map (η.app (.op U)))
    (relativeAffineMap_chart_isPullback hα hβ η hη)
  intro U
  exact IsClosedImmersion.spec_of_surjective _ (hsurj U)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.AffineMap.BundleCycles
end ComponentSource_26

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.AffineMap"

@[expose] public section ComponentSource_27
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.ClosedSupport -/

/-! # Closed Support -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.ClosedSupport.BundleCycles

noncomputable section

/-!
# LineBundleCycles: deformation of closed cycle supports

A surjective base-ring homomorphism induces a surjection on extended Rees
algebras for the image ideal. Its spectrum is therefore an actual closed
immersion. In particular the deformation of a closed integral cycle support
embeds into the ambient deformation, rather than being supplied as abstract
data.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open scoped BigOperators

universe u v
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Surjectivity on base rings gives surjectivity on the actual extended
Rees algebras, with the ideal replaced by its image. -/
theorem deformationMap_surjective (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : Function.Surjective f) (hJ : I.map f = J) (hIJ : I ≤ J.comap f) :
    Function.Surjective (Maps.BundleCycles.deformationMap I J f hIJ) := by
  classical
  intro p
  have hm (n : ℤ) : Iff.BundleCycles.deformationMonomial J n (p.val.coeff n) (p.property n) ∈
      (Maps.BundleCycles.deformationMap I J f hIJ).rangeS := by
    have hc : p.val.coeff n ∈ (I ^ (-n).toNat).map f := by
      rw [Ideal.map_pow, hJ]
      exact p.property n
    obtain ⟨r, hr, he⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp hc
    refine ⟨Iff.BundleCycles.deformationMonomial I n r hr, Subtype.ext ?_⟩
    change AddMonoidAlgebra.mapRingHom ℤ f (AddMonoidAlgebra.single n r) =
      AddMonoidAlgebra.single n (p.val.coeff n)
    rw [AddMonoidAlgebra.mapRingHom_single, he]
  have he : p = ∑ n ∈ p.val.coeff.support, Iff.BundleCycles.deformationMonomial J n (p.val.coeff n) (p.property n) := by
    apply Subtype.ext
    change p.val = (Iff.BundleCycles.deformationAlgebra J).val
      (∑ n ∈ p.val.coeff.support, Iff.BundleCycles.deformationMonomial J n (p.val.coeff n) (p.property n))
    rw [map_sum]
    exact (AddMonoidAlgebra.sum_coeff_single p.val).symm
  have hp : p ∈ (Maps.BundleCycles.deformationMap I J f hIJ).rangeS := by
    rw [he]
    exact Subsemiring.sum_mem _ fun n _ => hm n
  exact hp

/-- The actual spectrum of an affine deformation algebra. -/
def affineDeformation (I : Ideal R) : Scheme := Spec (CommRingCat.of (Iff.BundleCycles.deformationAlgebra I))

/-- Deformation of the closed subscheme cut out by P, along the restricted center. -/
def closedSupportDeformation (I P : Ideal R) : Scheme :=
  affineDeformation (I.map (Ideal.Quotient.mk P))

/-- The quotient on coefficients restricts to the deformation algebra. -/
def closedSupportDeformationRingMap (I P : Ideal R) :
    Iff.BundleCycles.deformationAlgebra I →+* Iff.BundleCycles.deformationAlgebra (I.map (Ideal.Quotient.mk P)) :=
  Maps.BundleCycles.deformationMap I _ (Ideal.Quotient.mk P) (fun _ hr => Ideal.mem_map_of_mem _ hr)

theorem closedSupportDeformationRingMap_surjective (I P : Ideal R) :
    Function.Surjective (closedSupportDeformationRingMap I P) :=
  deformationMap_surjective I _ (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective rfl _

/-- The deformation of a closed support is a closed subscheme of the ambient deformation. -/
def closedSupportDeformationInclusion (I P : Ideal R) :
    closedSupportDeformation I P ⟶ affineDeformation I :=
  Spec.map (CommRingCat.ofHom (closedSupportDeformationRingMap I P))

instance closedSupportDeformationInclusion_isClosedImmersion (I P : Ideal R) :
    IsClosedImmersion (closedSupportDeformationInclusion I P) :=
  IsClosedImmersion.spec_of_surjective _ (closedSupportDeformationRingMap_surjective I P)

/-- Its defining ideal consists exactly of Laurent polynomials with all
coefficients in the original support ideal P. -/
theorem closedSupportDeformationRingMap_eq_zero_iff (I P : Ideal R) (p : Iff.BundleCycles.deformationAlgebra I) :
    closedSupportDeformationRingMap I P p = 0 ↔ ∀ n, p.val.coeff n ∈ P := by
  constructor
  · intro h n
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact congrArg (fun q : Iff.BundleCycles.deformationAlgebra (I.map (Ideal.Quotient.mk P)) => q.val.coeff n) h
  · intro h
    apply Subtype.ext
    ext n
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (h n)

instance affineDeformation_isIntegral (I : Ideal R) [IsDomain R] : IsIntegral (affineDeformation I) := by
  exact inferInstanceAs (IsIntegral (Spec (CommRingCat.of (Iff.BundleCycles.deformationAlgebra I))))

instance affineDeformation_isNoetherian (I : Ideal R) [IsNoetherianRing R] :
    AlgebraicGeometry.IsNoetherian (affineDeformation I) := by
  exact inferInstanceAs (AlgebraicGeometry.IsNoetherian (Spec (CommRingCat.of (Iff.BundleCycles.deformationAlgebra I))))

instance closedSupportDeformation_isIntegral (I P : Ideal R) [P.IsPrime] :
    IsIntegral (closedSupportDeformation I P) := by
  exact affineDeformation_isIntegral (I.map (Ideal.Quotient.mk P))

instance closedSupportDeformation_isNoetherian (I P : Ideal R) [IsNoetherianRing R] :
    AlgebraicGeometry.IsNoetherian (closedSupportDeformation I P) :=
  affineDeformation_isNoetherian (I.map (Ideal.Quotient.mk P))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.ClosedSupport.BundleCycles
end ComponentSource_27

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.ClosedSupport"

@[expose] public section ComponentSource_28
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Support.CoefficientDiagram -/

/-! # Coefficient Diagram -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Support.CoefficientDiagram.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the affine coefficient rings of a closed support

The coefficients are the actual quotients by the support ideal sheaf.
Their transition maps and the images of the center ideals are compatible
with restrictions, with no cohomological condition in the construction.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

universe u

/-- Taking the image of a center ideal commutes with the coefficient quotient map. -/
theorem ideal_image_quotientMap {R S : Type u} [CommRing R] [CommRing S]
    (I P : Ideal R) (J Q : Ideal S) (f : R →+* S)
    (hP : P ≤ Q.comap f) (hI : I.map f = J) :
    (I.map (Ideal.Quotient.mk P)).map (Ideal.quotientMap Q f hP) =
      J.map (Ideal.Quotient.mk Q) := by
  rw [Ideal.map_map, Ideal.quotientMap_comp_mk, ← Ideal.map_map, hI]

variable {X : Scheme.{u}} (P : X.IdealSheafData)

/-- The coefficient rings of the closed support on all affine opens of the ambient scheme. -/
def supportCoefficientDiagram : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat where
  obj U := CommRingCat.of (Γ(X, U.unop.1) ⧸ P.ideal U.unop)
  map {U V} f := CommRingCat.ofHom
    (Ideal.quotientMap (P.ideal V.unop)
      (X.presheaf.map ((toOpensFunctor X).op.map f)).hom
      (P.ideal_le_comap_ideal (toOpens_mono f.unop.le)))
  map_id U := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro r
    change Ideal.Quotient.mk (P.ideal U.unop)
        (((toOpensFunctor X).op ⋙ X.presheaf).map (𝟙 U) r) =
      Ideal.Quotient.mk (P.ideal U.unop) r
    exact congrArg (Ideal.Quotient.mk (P.ideal U.unop))
      (ConcreteCategory.congr_hom (((toOpensFunctor X).op ⋙ X.presheaf).map_id U) r)
  map_comp {U V W} f g := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro r
    change Ideal.Quotient.mk (P.ideal W.unop)
        (((toOpensFunctor X).op ⋙ X.presheaf).map (f ≫ g) r) =
      Ideal.Quotient.mk (P.ideal W.unop)
        (((toOpensFunctor X).op ⋙ X.presheaf).map g
          (((toOpensFunctor X).op ⋙ X.presheaf).map f r))
    exact congrArg (Ideal.Quotient.mk (P.ideal W.unop))
      (ConcreteCategory.congr_hom (((toOpensFunctor X).op ⋙ X.presheaf).map_comp f g) r)

/-- The actual quotient maps form the coefficient natural transformation. -/
def supportCoefficientMap : (toOpensFunctor X).op ⋙ X.presheaf ⟶ supportCoefficientDiagram P where
  app U := CommRingCat.ofHom (Ideal.Quotient.mk (P.ideal U.unop))
  naturality {U V} f := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    rfl

/-- The actual quotient coefficient rings commute with affine basic-open localization. -/
theorem supportCoefficientMap_coequifibered : (supportCoefficientMap P).Coequifibered := by
  apply coequifibered_iff_forall_isLocalizationAway.mpr
  intro U r
  let V : X.AffineZariskiSite := U.basicOpen r
  let f : Γ(X, U.1) →+* Γ(X, V.1) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
  let : Algebra Γ(X, U.1) Γ(X, V.1) := f.toAlgebra
  have : IsLocalization.Away r Γ(X, V.1) := U.2.isLocalization_basicOpen r
  have hP : (P.ideal U).map (algebraMap Γ(X, U.1) Γ(X, V.1)) = P.ideal V :=
    P.map_ideal_basicOpen U r
  have h := QuotientLocalization.BundleCycles.quotientMap_isLocalization (Submonoid.powers r) Γ(X, V.1)
    (P.ideal U) (P.ideal V) hP (P.ideal_le_comap_ideal (X.basicOpen_le r))
  simp only [Submonoid.map_powers] at h
  exact h

variable (I : X.IdealSheafData)

/-- The restricted center ideal in each actual support coefficient ring. -/
def supportCenterIdeal (U : X.AffineZariskiSite) :
    Ideal ((supportCoefficientDiagram P).obj (.op U)) :=
  (I.ideal U).map (Ideal.Quotient.mk (P.ideal U))

theorem supportCenterIdeal_map {U V : X.AffineZariskiSiteᵒᵖ} (f : U ⟶ V) :
    (supportCenterIdeal P I U.unop).map ((supportCoefficientDiagram P).map f).hom =
      supportCenterIdeal P I V.unop :=
  ideal_image_quotientMap (I.ideal U.unop) (P.ideal U.unop)
    (I.ideal V.unop) (P.ideal V.unop)
    (X.presheaf.map ((toOpensFunctor X).op.map f)).hom
    (P.ideal_le_comap_ideal (toOpens_mono f.unop.le))
    (I.map_ideal (toOpens_mono f.unop.le))

theorem supportCenterIdeal_le_comap {U V : X.AffineZariskiSiteᵒᵖ} (f : U ⟶ V) :
    supportCenterIdeal P I U.unop ≤
      (supportCenterIdeal P I V.unop).comap ((supportCoefficientDiagram P).map f).hom :=
  Ideal.map_le_iff_le_comap.mp (supportCenterIdeal_map P I f).le

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Support.CoefficientDiagram.BundleCycles
end ComponentSource_28

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Support.CoefficientDiagram"

@[expose] public section ComponentSource_29
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Support.DeformationDiagram -/

/-! # Deformation Diagram -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Support.DeformationDiagram.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the extended-Rees diagram of a closed support

On each affine open the construction is literally the deformation algebra
over the quotient by the support ideal. Coefficient quotient maps define
the natural morphism from the ambient deformation diagram.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

universe u
variable {X : Scheme.{u}} (I P : X.IdealSheafData)

/-- Actual extended-Rees algebras over the support's quotient coefficient rings. -/
def supportDeformationDiagram : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat where
  obj U := CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U.unop))
  map {U V} f := CommRingCat.ofHom
    (Deformation.Maps.BundleCycles.deformationMap (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U.unop) (CoefficientDiagram.BundleCycles.supportCenterIdeal P I V.unop)
      ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).map f).hom (CoefficientDiagram.BundleCycles.supportCenterIdeal_le_comap P I f))
  map_id U := by
    apply CommRingCat.hom_ext
    ext p n
    have h : ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).map (𝟙 U)).hom =
        RingHom.id ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj U) :=
      congrArg CommRingCat.Hom.hom ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).map_id U)
    change (AddMonoidAlgebra.mapRingHom ℤ
      ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).map (𝟙 U)).hom p.val).coeff n = p.val.coeff n
    exact (AddMonoidAlgebra.coeff_mapRingHom
      ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).map (𝟙 U)).hom p.val n).trans (DFunLike.congr_fun h _)
  map_comp {U V W} f g := by
    apply CommRingCat.hom_ext
    ext p n
    have h : ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).map (f ≫ g)).hom =
        ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).map g).hom.comp ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).map f).hom :=
      congrArg CommRingCat.Hom.hom ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).map_comp f g)
    change (AddMonoidAlgebra.mapRingHom ℤ
      ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).map (f ≫ g)).hom p.val).coeff n =
      (AddMonoidAlgebra.mapRingHom ℤ ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).map g).hom
        (AddMonoidAlgebra.mapRingHom ℤ ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).map f).hom p.val)).coeff n
    simp only [AddMonoidAlgebra.coeff_mapRingHom]
    exact DFunLike.congr_fun h _

/-- Coefficient quotients induce the actual natural maps of deformation algebras. -/
def deformationToSupportDiagram : Global.Deformation.BundleCycles.deformationDiagram I ⟶ supportDeformationDiagram I P where
  app U := CommRingCat.ofHom (Deformation.ClosedSupport.BundleCycles.closedSupportDeformationRingMap (I.ideal U.unop) (P.ideal U.unop))
  naturality {U V} f := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    apply Subtype.ext
    ext n
    let qU := Ideal.Quotient.mk (P.ideal U.unop)
    let qV := Ideal.Quotient.mk (P.ideal V.unop)
    let fR := (X.presheaf.map ((toOpensFunctor X).op.map f)).hom
    let fQ := ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).map f).hom
    exact (AddMonoidAlgebra.coeff_mapRingHom qV (AddMonoidAlgebra.mapRingHom ℤ fR p.val) n).trans
      ((congrArg qV (AddMonoidAlgebra.coeff_mapRingHom fR p.val n)).trans
      ((AddMonoidAlgebra.coeff_mapRingHom fQ (AddMonoidAlgebra.mapRingHom ℤ qU p.val) n).trans
        (congrArg fQ (AddMonoidAlgebra.coeff_mapRingHom qU p.val n))).symm)

theorem deformationToSupportDiagram_surjective (U : X.AffineZariskiSite) :
    Function.Surjective ((deformationToSupportDiagram I P).app (.op U)) :=
  Deformation.ClosedSupport.BundleCycles.closedSupportDeformationRingMap_surjective (I.ideal U) (P.ideal U)

/-- Constants from the ambient scheme give the closed-support deformation's base map. -/
def supportDeformationDiagramMap : (toOpensFunctor X).op ⋙ X.presheaf ⟶ supportDeformationDiagram I P :=
  Global.Deformation.BundleCycles.deformationDiagramMap I ≫ deformationToSupportDiagram I P

theorem supportDeformationDiagramMap_apply (U : X.AffineZariskiSite) (r : Γ(X, U.1)) :
    (supportDeformationDiagramMap I P).app (.op U) r =
      algebraMap ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U))
        (Deformation.Iff.BundleCycles.deformationAlgebra (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U)) (Ideal.Quotient.mk (P.ideal U) r) :=
  Deformation.Maps.BundleCycles.deformationMap_algebraMap (I.ideal U) (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U)
    (Ideal.Quotient.mk (P.ideal U)) (fun _ hr => Ideal.mem_map_of_mem _ hr) r

/-- The actual closed-support deformation rings commute with affine base localization. -/
theorem supportDeformationDiagramMap_coequifibered :
    (supportDeformationDiagramMap I P).Coequifibered := by
  apply coequifibered_iff_forall_isLocalizationAway.mpr
  intro U r
  let V : X.AffineZariskiSite := U.basicOpen r
  let a : (.op U : X.AffineZariskiSiteᵒᵖ) ⟶ .op V :=
    (homOfLE (U.basicOpen_le r)).op
  let A : CommRingCat := (CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)
  let B : CommRingCat := (CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op V)
  let f : A ⟶ B := (CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).map a
  let : Algebra A B := f.hom.toAlgebra
  have : IsLocalization.Away ((CoefficientDiagram.BundleCycles.supportCoefficientMap P).app (.op U) r) B :=
    coequifibered_iff_forall_isLocalizationAway.mp (CoefficientDiagram.BundleCycles.supportCoefficientMap_coequifibered P) U r
  have hI : (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U).map (algebraMap A B) = CoefficientDiagram.BundleCycles.supportCenterIdeal P I V :=
    CoefficientDiagram.BundleCycles.supportCenterIdeal_map P I a
  have hle : CoefficientDiagram.BundleCycles.supportCenterIdeal P I U ≤ (CoefficientDiagram.BundleCycles.supportCenterIdeal P I V).comap (algebraMap A B) :=
    CoefficientDiagram.BundleCycles.supportCenterIdeal_le_comap P I a
  have h := Deformation.Localization.BundleCycles.deformationMap_isLocalization (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U)
    (Submonoid.powers ((CoefficientDiagram.BundleCycles.supportCoefficientMap P).app (.op U) r)) B
    (CoefficientDiagram.BundleCycles.supportCenterIdeal P I V) hI hle
  let : Algebra (Deformation.Iff.BundleCycles.deformationAlgebra (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U))
      (Deformation.Iff.BundleCycles.deformationAlgebra (CoefficientDiagram.BundleCycles.supportCenterIdeal P I V)) :=
    (Deformation.Maps.BundleCycles.deformationMap (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U) (CoefficientDiagram.BundleCycles.supportCenterIdeal P I V) f.hom hle).toAlgebra
  let : Algebra ((supportDeformationDiagram I P).obj (.op U))
      (Deformation.Iff.BundleCycles.deformationAlgebra (CoefficientDiagram.BundleCycles.supportCenterIdeal P I V)) :=
    (Deformation.Maps.BundleCycles.deformationMap (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U) (CoefficientDiagram.BundleCycles.supportCenterIdeal P I V) f.hom hle).toAlgebra
  change IsLocalization.Away ((supportDeformationDiagramMap I P).app (.op U) r)
    (Deformation.Iff.BundleCycles.deformationAlgebra (CoefficientDiagram.BundleCycles.supportCenterIdeal P I V))
  rw [supportDeformationDiagramMap_apply I P U r]
  simp only [Deformation.Localization.BundleCycles.deformationDenominators, Submonoid.map_powers] at h
  exact h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Support.DeformationDiagram.BundleCycles
end ComponentSource_29

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Support.DeformationDiagram"


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
    (`OAI.AlgebraicGeometry.Divisors.LineBundles.Support.DeformationDiagram.BundleCycles.supportDeformationDiagramMap_coequifibered, "theorem")
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
    ("nonce", toJson "ee0ccd0e4329bd1f203b30803e40cb23"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:ee0ccd0e4329bd1f203b30803e40cb23"
