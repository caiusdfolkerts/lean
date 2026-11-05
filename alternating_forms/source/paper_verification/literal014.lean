module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Regular.LinearMap
public import paper_verification.literal013
import paper_verification.literal013
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import paper_verification.literal001
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Ideal.Defs
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Data.Fintype.BigOperators
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Square
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.Fintype.EquivFin
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.Ring.Int.Field
import Mathlib.RingTheory.Ideal.NatInt
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Depth.Basic
public import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Regular.Flat
public import paper_verification.literal001
public import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Lean.Elab.Tactic.Omega
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Finiteness.Quotient
public import paper_verification.literal012
public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Smooth.Field
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Extension.Cotangent.Basis
public import Mathlib.RingTheory.Derivation.ToSquareZero
public import Mathlib.Algebra.MvPolynomial.Funext

set_option Elab.async false

section TAF_LiteralSource_0603
/- Original module: TauCeti.RingTheory.CohenMacaulay.Normal -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Depth of normal local domains

A Noetherian local domain `R` which is integrally closed and has dimension at least two has depth
at least two. This is the local form of the `(S₂)` half of Serre's normality criterion (Stacks,
Lemma 10.157.4 (031S)): a normal Noetherian ring satisfies `(S₂)`. Consequently a Noetherian
integrally closed local domain of dimension at most two is Cohen–Macaulay, which is the
hypothesis miracle flatness asks of a two-dimensional normal local domain finite over a regular
local ring.

## Proof

The depth statement rests on the following property of the maximal ideal `𝔪`: for `b ≠ 0`, it is
not an associated prime of `R ⧸ (b)`, unless `𝔪` is principal. Indeed, let `𝔪 c ⊆ (b)` and put
`t = c / b` in the fraction field, so that `t 𝔪 ⊆ R`. If `t 𝔪 ⊆ 𝔪`, then `t` is integral over `R`
(Mathlib's `isIntegral_of_smul_mem_submodule`), hence lies in `R`, and `c ∈ (b)`. Otherwise
`t u` is a unit for some `u ∈ 𝔪`, and then `𝔪 = (u)`. A principal maximal ideal forces dimension
at most one, so in dimension at least two, any nonzero `x ∈ 𝔪` is followed by an element of `𝔪`
regular on `R ⧸ (x)` (Mathlib's `IsSMulRegular.subsingleton_linearMap_iff`).

## Main results

* `TauCeti.IsIntegrallyClosed.mem_span_singleton_of_forall_mul_mem`: in a Noetherian integrally
  closed local domain whose maximal ideal is not principal, `𝔪 c ⊆ (b)` with `b ≠ 0` forces
  `c ∈ (b)`.
* `TauCeti.IsIntegrallyClosed.isSMulRegular_quotient_span_singleton_of_radical_span_pair`:
  if `(x, y)` has maximal radical, `x ≠ 0` and the maximal ideal is nonprincipal, then `y` is
  regular on `R ⧸ (x)`.
* `IsLocalRing.two_le_depth_of_isIntegrallyClosed`: a Noetherian integrally closed local domain of
  dimension at least two has depth at least two.
* `Module.isCohenMacaulay_self_of_isIntegrallyClosed_of_krullDimLE_two`: a Noetherian integrally
  closed local domain of dimension at most two is Cohen–Macaulay over itself.

## References

* [Stacks Project, Lemma 10.157.4](https://stacks.math.columbia.edu/tag/031S), Serre's criterion
  for normality.
* H. Matsumura, *Commutative Ring Theory*, Theorem 23.8.
-/

public section

open IsLocalRing Ideal Pointwise

namespace TauCeti.IsIntegrallyClosed

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
  [IsIntegrallyClosed R]

/-- In a Noetherian integrally closed local domain whose maximal ideal is not principal, the
maximal ideal is not an associated prime of `R ⧸ (b)` for `b ≠ 0`: if `z c ∈ (b)` for every `z` in
the maximal ideal, then `c ∈ (b)`. -/
theorem mem_span_singleton_of_forall_mul_mem (hm : ¬ (maximalIdeal R).IsPrincipal) {b c : R}
    (hb : b ≠ 0) (hc : ∀ z ∈ maximalIdeal R, z * c ∈ span {b}) : c ∈ span {b} := by
  have hc' : ∀ z ∈ maximalIdeal R, ∃ w, z * c = b * w := fun z hz ↦ by
    obtain ⟨w, hw⟩ := mem_span_singleton'.mp (hc z hz)
    exact ⟨w, by rw [← hw, mul_comm]⟩
  by_cases hall : ∀ z ∈ maximalIdeal R, ∀ w, z * c = b * w → w ∈ maximalIdeal R
  · -- `t = c / b` maps the maximal ideal into itself, so it is integral over `R`.
    let K := FractionRing R
    have hb' : algebraMap R K b ≠ 0 := by simpa using (IsFractionRing.injective R K).ne hb
    let N : Submodule R K := Submodule.map (Algebra.linearMap R K) (maximalIdeal R)
    have hN : N ≠ ⊥ := fun h ↦ hm <| by
      rw [Submodule.map_injective_of_injective (IsFractionRing.injective R K)
        (h.trans (Submodule.map_bot _).symm)]
      exact bot_isPrincipal
    have hint : IsIntegral R (algebraMap R K c / algebraMap R K b) := by
      refine isIntegral_of_smul_mem_submodule N hN
        ((IsNoetherian.noetherian (maximalIdeal R)).map _) _ ?_
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨w, hw⟩ := hc' z hz
      refine ⟨w, hall z hz w hw, ?_⟩
      have hw' := congrArg (algebraMap R K) hw
      simp only [map_mul] at hw'
      simp only [Algebra.linearMap_apply, smul_eq_mul]
      field_simp
      linear_combination -hw'
    obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (K := K)).mp hint
    refine mem_span_singleton'.mpr ⟨a, IsFractionRing.injective R K ?_⟩
    rw [map_mul, ha, div_mul_cancel₀ _ hb']
  · -- Otherwise `u c = b v` with `v` a unit for some `u` in the maximal ideal, which is then `(u)`.
    push Not at hall
    obtain ⟨u, hu, v, huv, hv⟩ := hall
    have hv : IsUnit v := notMem_maximalIdeal.mp hv
    refine absurd ⟨⟨u, le_antisymm (fun z hz ↦ ?_) ((span_singleton_le_iff_mem _).mpr hu)⟩⟩ hm
    obtain ⟨w, hw⟩ := hc' z hz
    have : v * z = u * w := mul_left_cancel₀ hb (by linear_combination u * hw - z * huv)
    rw [Submodule.mem_span_singleton]
    exact ⟨↑hv.unit⁻¹ * w, by
      rw [smul_eq_mul]
      linear_combination -(↑hv.unit⁻¹ : R) * this + z * hv.val_inv_mul⟩

/-- In a Noetherian normal local domain with nonprincipal maximal ideal, if `(x, y)` has maximal
radical and `x ≠ 0`, then `y` is a nonzerodivisor on `R ⧸ (x)`. -/
theorem isSMulRegular_quotient_span_singleton_of_radical_span_pair
    (hm : ¬ (maximalIdeal R).IsPrincipal) {x y : R} (hx : x ≠ 0)
    (hxy : (span {x, y}).radical = maximalIdeal R) :
    IsSMulRegular (R ⧸ span {x}) y := by
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro c hc
  by_contra hcx
  obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R
    (Ideal.Quotient.mk (span {x}) c) (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  have hprime := hP.isPrime
  have hxP : x ∈ P := hle (Ideal.Quotient.mem_colon_singleton_mk.mpr
    (mem_span_singleton'.mpr ⟨c, mul_comm _ _⟩))
  have hyP : y ∈ P := hle (Ideal.Quotient.mem_colon_singleton_mk.mpr hc)
  have hPm : P = maximalIdeal R := by
    refine le_antisymm (le_maximalIdeal hprime.ne_top) ?_
    rw [← hxy]
    exact hprime.radical_le_iff.mpr (span_le.mpr (by rintro z (rfl | rfl) <;> assumption))
  obtain ⟨_, u, hu⟩ := isAssociatedPrime_iff.mp hP
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective u
  have hd : d ∈ span {x} := mem_span_singleton_of_forall_mul_mem hm hx fun z hz ↦
    Ideal.Quotient.mem_colon_singleton_mk.mp (hu ▸ hPm.symm ▸ hz)
  have hone : (1 : R) ∈ P := by
    rw [hu]
    exact Ideal.Quotient.mem_colon_singleton_mk.mpr (by simpa using hd)
  exact hprime.one_notMem hone

end TauCeti.IsIntegrallyClosed

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- **The `(S₂)` property of normal local domains.** A Noetherian integrally closed local domain of
dimension at least two has depth at least two. The local form of the `(S₂)` half of Serre's
criterion, Stacks, Lemma 10.157.4 (031S). -/
@[stacks 031S "the local form of normal implies (S₂)"]
theorem two_le_depth_of_isIntegrallyClosed [IsDomain R] [IsIntegrallyClosed R]
    (hdim : 2 ≤ ringKrullDim R) : 2 ≤ depth (ModuleCat.of R R) := by
  have hm : ¬ (maximalIdeal R).IsPrincipal := fun h ↦
    absurd (hdim.trans (ringKrullDim_le_one_of_isPrincipal_maximalIdeal h)) (by decide)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := maximalIdeal R)
    fun h ↦ hm (h ▸ bot_isPrincipal)
  -- Every linear map `R ⧸ 𝔪 → R ⧸ (x)` vanishes, so some `y ∈ 𝔪` is regular on `R ⧸ (x)`.
  have : Subsingleton (R ⧸ maximalIdeal R →ₗ[R] QuotSMulTop x R) := by
    refine subsingleton_of_forall_eq 0 fun f ↦ ?_
    have hmk (r : R) : Ideal.Quotient.mk (maximalIdeal R) r = r • Ideal.Quotient.mk _ 1 := by
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_one, mul_one]
    have key : f (Ideal.Quotient.mk _ 1) = 0 := by
      -- The maximal ideal kills `f 1`, so a lift `c` of `f 1` has `𝔪 c ⊆ (x)`.
      have hkill (z : R) (hz : z ∈ maximalIdeal R) : z • f (Ideal.Quotient.mk _ 1) = 0 := by
        rw [← map_smul, ← hmk, Ideal.Quotient.eq_zero_iff_mem.mpr hz, map_zero]
      obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (f (Ideal.Quotient.mk _ 1))
      simp only [← hc, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
        ← Submodule.ideal_span_singleton_smul, smul_eq_mul, mul_top] at hkill ⊢
      exact TauCeti.IsIntegrallyClosed.mem_span_singleton_of_forall_mul_mem hm hx0 hkill
    refine LinearMap.ext fun q ↦ ?_
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [hmk, map_smul, key, smul_zero, LinearMap.zero_apply]
  obtain ⟨y, hy, hreg⟩ := IsSMulRegular.subsingleton_linearMap_iff.mp this
  rw [annihilator_quotient] at hy
  rw [← depth_quotSMulTop_succ_eq_depth (IsSMulRegular.of_ne_zero hx0) hx,
    ← depth_quotSMulTop_succ_eq_depth hreg hy, add_assoc]
  exact le_add_self

end IsLocalRing

namespace Module

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
  [IsIntegrallyClosed R]

/-- A Noetherian integrally closed local domain of dimension at most two is Cohen–Macaulay over
itself. -/
theorem isCohenMacaulay_self_of_isIntegrallyClosed_of_krullDimLE_two [Ring.KrullDimLE 2 R] :
    IsCohenMacaulay R R := by
  by_cases hdim : 2 ≤ ringKrullDim R
  · rw [isCohenMacaulay_iff_supportDim_le_depth, supportDim_self_eq_ringKrullDim]
    refine (Ring.krullDimLE_iff.1 ‹_›).trans ?_
    rw [← WithBot.coe_natCast, WithBot.coe_le_coe]
    exact_mod_cast IsLocalRing.two_le_depth_of_isIntegrallyClosed hdim
  -- In dimension at most one, a Noetherian local domain is Cohen–Macaulay.
  have : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr
    (ENat.WithBot.lt_add_one_iff.mp (by simpa [one_add_one_eq_two] using not_le.mp hdim))
  exact isCohenMacaulay_self_of_isDomain_of_krullDimLE_one

end Module
end
end TAF_LiteralSource_0603

section TAF_LiteralSource_0604
/- Original module: TauCeti.RingTheory.LocalRing.Quotient -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The maximal ideal and the cotangent space of a quotient of a local ring

Let `π : Q → A` be a surjective homomorphism of local rings. Then `π` maps `𝔪_Q` onto `𝔪_A`, and
an element of `Q` maps into `𝔪_A²` exactly when it lies in `ker π + 𝔪_Q²`. Consequently
lifts to `Q` of a basis of the cotangent space `𝔪_A / 𝔪_A²` span `𝔪_Q` modulo `ker π + 𝔪_Q²`,
and they are linearly independent modulo it.

For a local homomorphism `R → S` with `S` local and an ideal `J` of `R`, the induced map
`R ⧸ J → S ⧸ J S` is again local. Dividing both sides of a local homomorphism by an ideal of the
base, as in inductions on the dimension of the base, therefore stays among local homomorphisms.

## Main results

* `TauCeti.IsLocalRing.apply_mem_maximalIdeal_sq_iff`: `π a ∈ 𝔪_A²` if and only if
  `a ∈ ker π + 𝔪_Q²`.
* `TauCeti.IsLocalRing.maximalIdeal_quotient_eq_span_range`: if `𝔪_Q = J + (yⱼ)`, then the images
  of the `yⱼ` generate the maximal ideal of `Q ⧸ J`.
* `TauCeti.IsLocalRing.exists_lift_finBasis_cotangentSpace`: lifts to `Q` of a basis of the
  cotangent space of `A`.
* `Ideal.Quotient.isLocalHom_algebraMap_quotient_map_quotient`: `R ⧸ J → S ⧸ J S` is a local
  homomorphism when `R → S` is one and `S` is local.
-/

public section

namespace TauCeti.IsLocalRing

open _root_.IsLocalRing Module

variable {Q A : Type*} [CommRing Q] [IsLocalRing Q] [CommRing A] [IsLocalRing A]

/-- Along a surjective homomorphism of local rings `π : Q → A`, an element `a` maps into `𝔪_A²`
if and only if it lies in `ker π + 𝔪_Q²`. -/
theorem apply_mem_maximalIdeal_sq_iff {π : Q →+* A} (hπ : Function.Surjective π) (a : Q) :
    π a ∈ maximalIdeal A ^ 2 ↔ a ∈ RingHom.ker π ⊔ maximalIdeal Q ^ 2 := by
  rw [← map_maximalIdeal_of_surjective π hπ, ← Ideal.map_pow, ← Ideal.mem_comap,
    Ideal.comap_map_of_surjective' _ hπ, sup_comm]

omit [IsLocalRing A] in
/-- If the maximal ideal of `Q` is `J + (yⱼ)`, then the images of the `yⱼ` generate the maximal
ideal of the local ring `Q ⧸ J`. -/
theorem maximalIdeal_quotient_eq_span_range {κ : Type*} {J : Ideal Q} [IsLocalRing (Q ⧸ J)]
    {y : κ → Q} (h : maximalIdeal Q = J ⊔ Ideal.span (Set.range y)) :
    maximalIdeal (Q ⧸ J) = Ideal.span (Set.range (Ideal.Quotient.mk J ∘ y)) := by
  rw [← map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective, h, Ideal.map_sup,
    Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span, Set.range_comp]

/-- **Lifts of a basis of the cotangent space of a quotient.** Let `π : Q → A` be a surjective
homomorphism of local rings, where `𝔪_Q` is finitely generated. Then there are lifts
`y : Fin e → Q` of a basis of `𝔪_A / 𝔪_A²`, where `e` is its dimension. They lie in `𝔪_Q`, span
`𝔪_Q` modulo `ker π + 𝔪_Q²`, and are linearly independent modulo it: a combination `∑ cⱼ yⱼ` lies
in `ker π + 𝔪_Q²` only if every `cⱼ ∈ 𝔪_Q`. -/
theorem exists_lift_finBasis_cotangentSpace (hfg : (maximalIdeal Q).FG) {π : Q →+* A}
    (hπ : Function.Surjective π) :
    ∃ y : Fin (finrank (ResidueField A) (CotangentSpace A)) → Q,
      (∀ j, y j ∈ maximalIdeal Q) ∧
      maximalIdeal Q ≤ Ideal.span (Set.range y) ⊔ (RingHom.ker π ⊔ maximalIdeal Q ^ 2) ∧
      ∀ c : Fin (finrank (ResidueField A) (CotangentSpace A)) → Q,
        ∑ j, c j * y j ∈ RingHom.ker π ⊔ maximalIdeal Q ^ 2 → ∀ j, c j ∈ maximalIdeal Q := by
  set e := finrank (ResidueField A) (CotangentSpace A)
  have hπ𝔪 : (maximalIdeal Q).map π = maximalIdeal A := map_maximalIdeal_of_surjective π hπ
  have : IsLocalHom π := .of_surjective π hπ
  have : Module.Finite A (maximalIdeal A) := Module.Finite.iff_fg.2 (hπ𝔪 ▸ hfg.map π)
  have : Module.Finite A (CotangentSpace A) :=
    .of_surjective _ (maximalIdeal A).toCotangent_surjective
  have : Module.Finite (ResidueField A) (CotangentSpace A) :=
    .of_restrictScalars_finite A _ _
  let bA := Module.finBasisOfFinrankEq (ResidueField A) (CotangentSpace A) rfl
  choose m hm using fun j ↦ (maximalIdeal A).toCotangent_surjective (bA j)
  choose y hy using fun j ↦ hπ (m j : A)
  have hy𝔪 (j : Fin e) : y j ∈ maximalIdeal Q := by
    rw [← maximalIdeal_comap π, Ideal.mem_comap, hy]
    exact (m j).2
  have hsum𝔪 (c : Fin e → Q) : π (∑ j, c j * y j) ∈ maximalIdeal A :=
    hπ𝔪 ▸ Ideal.mem_map_of_mem π (Ideal.sum_mem _ fun j _ ↦ Ideal.mul_mem_left _ _ (hy𝔪 j))
  have hcot (c : Fin e → Q) : (maximalIdeal A).toCotangent ⟨_, hsum𝔪 c⟩ =
      ∑ j, residue A (π (c j)) • bA j := by
    have : (⟨_, hsum𝔪 c⟩ : maximalIdeal A) = ∑ j, π (c j) • m j := by
      ext
      simp [hy]
    rw [this, map_sum]
    simp [hm, ← ResidueField.algebraMap_eq, algebraMap_smul]
  -- The `yⱼ` together with `ker π` span `𝔪` modulo `𝔪²` ...
  have hcov (a : Q) (ha : a ∈ maximalIdeal Q) :
      a ∈ Ideal.span (Set.range y) ⊔ (RingHom.ker π ⊔ maximalIdeal Q ^ 2) := by
    have haA : π a ∈ maximalIdeal A := hπ𝔪 ▸ Ideal.mem_map_of_mem π ha
    choose c hc using fun j ↦ (residue_surjective.comp hπ) (bA.repr
      ((maximalIdeal A).toCotangent ⟨_, haA⟩) j)
    have hspan : ∑ j, c j * y j ∈ Ideal.span (Set.range y) :=
      Ideal.sum_mem _ fun j _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
    have hrest : a - ∑ j, c j * y j ∈ RingHom.ker π ⊔ maximalIdeal Q ^ 2 := by
      have hmem : π (a - ∑ j, c j * y j) ∈ maximalIdeal A :=
        (map_sub π _ _) ▸ sub_mem haA (hsum𝔪 c)
      rw [← apply_mem_maximalIdeal_sq_iff hπ, ← Ideal.toCotangent_eq_zero _ ⟨_, hmem⟩]
      have : (⟨_, hmem⟩ : maximalIdeal A) = ⟨_, haA⟩ - ⟨_, hsum𝔪 c⟩ :=
        Subtype.ext (map_sub π _ _)
      rw [this, map_sub, hcot]
      simp only [Function.comp_apply] at hc
      simp [hc, Basis.sum_repr]
    simpa using Submodule.add_mem_sup hspan hrest
  -- ... and are linearly independent modulo `ker π + 𝔪²`.
  have hind (c : Fin e → Q) (hc : ∑ j, c j * y j ∈ RingHom.ker π ⊔ maximalIdeal Q ^ 2)
      (j : Fin e) : c j ∈ maximalIdeal Q := by
    rw [← apply_mem_maximalIdeal_sq_iff hπ, ← Ideal.toCotangent_eq_zero _ ⟨_, hsum𝔪 c⟩,
      hcot] at hc
    have := (Fintype.linearIndependent_iff.1 bA.linearIndependent _ hc) j
    rw [residue_eq_zero_iff, ← Ideal.mem_comap, maximalIdeal_comap] at this
    exact this
  exact ⟨y, hy𝔪, fun a ha ↦ hcov a ha, hind⟩

end TauCeti.IsLocalRing

namespace Ideal.Quotient

open _root_.IsLocalRing

variable {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing S] [Algebra R S]
  [IsLocalHom (algebraMap R S)]

/-- For a local homomorphism `R → S` to a local ring and an ideal `J` of `R`, the induced
homomorphism `R ⧸ J → S ⧸ J S` is local. The ring `R` need not be local. -/
instance isLocalHom_algebraMap_quotient_map_quotient (J : Ideal R) :
    IsLocalHom (algebraMap (R ⧸ J) (S ⧸ J.map (algebraMap R S))) := by
  refine ⟨fun a ha ↦ ?_⟩
  obtain ⟨r, rfl⟩ := mk_surjective a
  rw [algebraMap_quotient_map_quotient] at ha
  by_cases hJ : J = ⊤
  · subst hJ
    exact isUnit_of_subsingleton _
  -- A proper `J` consists of nonunits, so `J S` lies in the maximal ideal of `S`.
  have hJS : J.map (algebraMap R S) ≤ maximalIdeal S := map_le_iff_le_comap.mpr fun j hj ↦
    (mem_maximalIdeal _).mpr fun h ↦ hJ (J.eq_top_of_isUnit_mem hj (isUnit_of_map_unit _ j h))
  have : Nontrivial (S ⧸ J.map (algebraMap R S)) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top IsPrime.ne_top' hJS)
  have := IsLocalHom.of_surjective (mk (J.map (algebraMap R S))) mk_surjective
  exact (isUnit_of_map_unit (algebraMap R S) r (isUnit_of_map_unit (mk _) _ ha)).map _

end Ideal.Quotient
end
end TAF_LiteralSource_0604

section TAF_LiteralSource_0605
/- Original module: TauCeti.RingTheory.CohenMacaulay.RegularSequence -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Regular sequences in Cohen–Macaulay modules

Let `M` be a nonzero finite Cohen–Macaulay module over a Noetherian local ring `(R, 𝔪)`. A
sequence `r₁, …, rₙ` of elements of `𝔪` is `M`-regular if and only if it cuts the dimension of
the support down by its length, `dim M ⧸ (r₁, …, rₙ) M + n = dim M` (Stacks, Proposition 10.103.4
(00N6)). One direction holds for every finite module
(`Module.supportDim_add_length_eq_supportDim_of_isRegular`); the content is the converse, for
which the Cohen–Macaulay hypothesis is essential.

The single-element case rests on unmixedness: every associated prime `p` of a Cohen–Macaulay
module satisfies `dim R ⧸ p = dim M`, so if `x` is a zero divisor on `M`, it lies in such a `p`,
which then lies in the support of `M ⧸ x M`, and the dimension does not drop at all.

The main application is to a local homomorphism `R → S` of local rings with `S` Noetherian and
Cohen–Macaulay. If `r₁, …, rₙ` generate the maximal ideal of `R` and
`dim S = dim S ⧸ 𝔪_R S + n`, then the images of the `rᵢ` form an `S`-regular sequence. For a
regular local ring `R` and a regular system of parameters, `n = dim R` and the hypothesis is the
dimension formula `dim S = dim R + dim S ⧸ 𝔪_R S` of miracle flatness (Stacks, Lemma 10.128.1
(00R4)), whose proof starts from exactly this regular sequence.

The same holds one element at a time, which is the form an induction on `dim R` uses. If
`dim S = dim R + dim S ⧸ 𝔪_R S` and `x ∈ R` satisfies `dim R ⧸ (x) + 1 = dim R`, for instance
`x ∈ 𝔪 ∖ 𝔪²` in a regular local ring, then `x` is `S`-regular, `S ⧸ x S` is a Cohen–Macaulay
ring, and `R ⧸ (x) → S ⧸ x S` again satisfies the dimension formula, since its closed fibre is
that of `R → S`. Regularity of `x` comes from the fibre inequality
`dim S ⧸ x S ≤ dim R ⧸ (x) + dim S ⧸ 𝔪_R S`, which forces the dimension of `S` to drop.

For a finite torsion-free algebra `B` over a Noetherian integrally closed local domain `A`, the
localization `B_𝔮` at a maximal ideal need not be finite over `A`, but going down along `A → B`
gives it the dimension of `A`, and its closed fibre `B_𝔮 ⧸ 𝔪_A B_𝔮` is Artinian. So `B_𝔮`
satisfies the dimension formula of miracle flatness, and a Cohen–Macaulay `B_𝔮` receives a
regular sequence from a regular system of parameters of `A`. In dimension two, normality of
`B_𝔮` already implies that it is Cohen–Macaulay (Stacks, Lemma 10.157.4 (031S)). This is the
input to miracle flatness for the localizations of finite normal algebras over a normal local
domain of dimension two, such as a regular local ring of dimension two, as in the proof of purity
for regular local rings (Stacks, Lemma 58.21.3 (0BMA)).

## Main results

* `Module.IsCohenMacaulay.isSMulRegular_of_supportDim_quotSMulTop_lt`: an element `x` with
  `dim M ⧸ x M < dim M` is `M`-regular (Stacks, Lemma 10.103.3 (00N5), part (a)).
* `Module.IsCohenMacaulay.isSMulRegular_iff_supportDim_quotSMulTop_lt`: for `x ∈ 𝔪` and `M ≠ 0`,
  this is a characterization of `M`-regular elements.
* `Module.IsCohenMacaulay.quotSMulTop`: under the same hypothesis `M ⧸ x M` is again
  Cohen–Macaulay (Stacks, Lemma 10.103.3 (00N5), part (b)).
* `Module.IsCohenMacaulay.isRegular_iff_supportDim_add_length_eq_supportDim`: for `M ≠ 0`, a
  sequence in `𝔪` is `M`-regular if and only if it cuts the dimension of the support down by its
  length (Stacks, Proposition 10.103.4 (00N6)).
* `Module.IsCohenMacaulay.isRegular_of_le_radical`: a system of parameters, that is `dim M`
  elements of `𝔪` cutting `M` down to a module supported at the closed point, is `M`-regular.
* `Module.IsCohenMacaulay.isRegular_map_algebraMap`: generators of the maximal ideal of `R` whose
  number is `dim S - dim S ⧸ 𝔪_R S` map to an `S`-regular sequence.
* `Module.IsCohenMacaulay.isRegular_map_algebraMap_localization`: for a finite torsion-free
  algebra `B` over a Noetherian integrally closed local domain `A` and a maximal ideal `𝔮` of `B`
  with `B_𝔮` Cohen–Macaulay, `dim A` generators of the maximal ideal of `A` map to a
  `B_𝔮`-regular sequence.
* `Module.IsCohenMacaulay.isSMulRegular_algebraMap`,
  `Module.IsCohenMacaulay.quotient_map_span_singleton` and
  `Module.IsCohenMacaulay.ringKrullDim_quotient_map_span_singleton_eq`: if `R → S` satisfies the
  dimension formula `dim S = dim R + dim S ⧸ 𝔪_R S` with `S` Cohen–Macaulay, and
  `dim R ⧸ (x) + 1 = dim R`, then `x` is `S`-regular, `S ⧸ x S` is a Cohen–Macaulay ring, and
  `R ⧸ (x) → S ⧸ x S` again satisfies the dimension formula.
* `TauCeti.isRegular_pair_localization_of_isIntegrallyClosed`: when `A` has dimension two and
  `B_𝔮` is a normal domain, `B_𝔮` is automatically Cohen–Macaulay, so every pair generating the
  maximal ideal of `A` maps to a `B_𝔮`-regular sequence.

## References

* [Stacks Project, Section 10.103](https://stacks.math.columbia.edu/tag/00N2),
  Lemma 10.103.3 (00N5) and Proposition 10.103.4 (00N6).
* [Stacks Project, Lemma 10.128.1](https://stacks.math.columbia.edu/tag/00R4), the first step of
  its proof.
* [Stacks Project, Lemma 58.21.3](https://stacks.math.columbia.edu/tag/0BMA), the dimension-two
  case of its proof.
-/

public section

universe u v

open IsLocalRing RingTheory.Sequence Ideal Pointwise

namespace Module.IsCohenMacaulay

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R]
  {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- In a finite Cohen–Macaulay module over a Noetherian local ring, an element `x` with
`dim M ⧸ x M < dim M` is `M`-regular. Stacks, Lemma 10.103.3 (00N5), part (a), where the drop is
assumed to be exactly one. -/
@[stacks 00N5 "(a)"]
theorem isSMulRegular_of_supportDim_quotSMulTop_lt (h : IsCohenMacaulay R M) {x : R}
    (hx : supportDim R (QuotSMulTop x M) < supportDim R M) : IsSMulRegular M x := by
  by_contra hreg
  -- A zero divisor lies in an associated prime `p`.
  have hmem : x ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) := by
    rw [biUnion_associatedPrimes_eq_compl_regular R M]
    exact hreg
  obtain ⟨p, hp, hxp⟩ : ∃ p ∈ associatedPrimes R M, x ∈ p := by simpa using hmem
  have hp : IsAssociatedPrime p M := AssociatedPrimes.mem_iff.1 hp
  -- So `p` lies in the support of `M ⧸ x M`, which therefore has dimension `≥ dim R ⧸ p`.
  have hsupp : (⟨p, hp.isPrime⟩ : PrimeSpectrum R) ∈ support R (QuotSMulTop x M) := by
    rw [support_quotSMulTop]
    refine ⟨mem_support_iff_of_finite.2 ?_, by simpa using hxp⟩
    exact Submodule.annihilator_top (R := R) (M := M) ▸ hp.annihilator_le
  have hle : ringKrullDim (R ⧸ p) ≤ supportDim R (QuotSMulTop x M) := by
    rw [supportDim_eq_ringKrullDim_quotient_annihilator]
    exact ringKrullDim_le_of_surjective _
      (Ideal.Quotient.factor_surjective (mem_support_iff_of_finite.1 hsupp))
  -- By unmixedness `dim R ⧸ p = dim M`, so the dimension does not drop.
  exact (h.ringKrullDim_quotient_eq_supportDim hp ▸ hle).not_gt hx

/-- For `x` in the maximal ideal and a nonzero finite Cohen–Macaulay module `M` over a Noetherian
local ring, `x` is `M`-regular if and only if `dim M ⧸ x M < dim M`; the drop is then exactly one
(`Module.supportDim_quotSMulTop_succ_eq_supportDim`). -/
theorem isSMulRegular_iff_supportDim_quotSMulTop_lt [Nontrivial M] (h : IsCohenMacaulay R M)
    {x : R} (hx : x ∈ maximalIdeal R) :
    IsSMulRegular M x ↔ supportDim R (QuotSMulTop x M) < supportDim R M := by
  refine ⟨fun reg ↦ ?_, h.isSMulRegular_of_supportDim_quotSMulTop_lt⟩
  obtain ⟨k, hk⟩ := exists_supportDim_eq_natCast (R := R) (M := M)
  rw [hk]
  exact ENat.WithBot.lt_natCast_of_add_one_eq
    (hk ▸ supportDim_quotSMulTop_succ_eq_supportDim reg hx)

/-- If `x ∈ 𝔪` satisfies `dim M ⧸ x M < dim M` for a finite Cohen–Macaulay module `M` over a
Noetherian local ring, then `M ⧸ x M` is Cohen–Macaulay. Stacks, Lemma 10.103.3 (00N5),
part (b). -/
@[stacks 00N5 "(b)"]
theorem quotSMulTop (h : IsCohenMacaulay R M) {x : R} (hx : x ∈ maximalIdeal R)
    (hdim : supportDim R (QuotSMulTop x M) < supportDim R M) :
    IsCohenMacaulay R (QuotSMulTop x M) :=
  (isCohenMacaulay_quotSMulTop_iff (h.isSMulRegular_of_supportDim_quotSMulTop_lt hdim) hx).2 h

/-- **Regular sequences in a Cohen–Macaulay module.** For a nonzero finite Cohen–Macaulay module
`M` over a Noetherian local ring, a sequence `r₁, …, rₙ` of elements of the maximal ideal is
`M`-regular if and only if `dim M ⧸ (r₁, …, rₙ) M + n = dim M`. Stacks, Proposition 10.103.4
(00N6). -/
@[stacks 00N6]
theorem isRegular_iff_supportDim_add_length_eq_supportDim [Nontrivial M]
    (h : IsCohenMacaulay R M) (rs : List R) (hrs : ∀ r ∈ rs, r ∈ maximalIdeal R) :
    IsRegular M rs ↔
      supportDim R (M ⧸ ofList rs • (⊤ : Submodule R M)) + rs.length = supportDim R M := by
  refine ⟨supportDim_add_length_eq_supportDim_of_isRegular rs, fun hdim ↦ ?_⟩
  induction rs generalizing M with
  | nil => exact IsRegular.nil R M
  | cons x rs ih =>
    have hx : x ∈ maximalIdeal R := hrs x List.mem_cons_self
    have hrs' : ∀ r ∈ rs, r ∈ maximalIdeal R := fun r hr ↦ hrs r (List.mem_cons_of_mem x hr)
    -- Write `N = M ⧸ x M` and `a = dim N ⧸ (r₂, …, rₙ) N`, so that `a + (n - 1) + 1 = dim M`.
    rw [supportDim_eq_of_equiv (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x rs),
      List.length_cons, Nat.cast_add_one, ← add_assoc] at hdim
    obtain ⟨k, hk⟩ := exists_supportDim_eq_natCast (R := R) (M := M)
    -- Each of `r₂, …, rₙ` drops the dimension by at most one, so `dim N ≤ a + (n - 1) < dim M`.
    have hlt : supportDim R (QuotSMulTop x M) < supportDim R M :=
      (supportDim_le_supportDim_quotient_add_length rs hrs').trans_lt
        (hk ▸ ENat.WithBot.lt_natCast_of_add_one_eq (hdim.trans hk))
    have reg := h.isSMulRegular_of_supportDim_quotSMulTop_lt hlt
    have := nontrivial_quotSMulTop_of_mem_maximalIdeal M hx
    -- Now `dim N + 1 = dim M`, and the induction hypothesis applies to `N`.
    rw [← supportDim_quotSMulTop_succ_eq_supportDim reg hx, ENat.WithBot.add_one_cancel] at hdim
    exact (isRegular_cons_iff M x rs).2 ⟨reg, ih (h.quotSMulTop hx hlt) hrs' hdim⟩

/-- **Systems of parameters are regular sequences.** Let `M` be a nonzero finite Cohen–Macaulay
module over a Noetherian local ring `(R, 𝔪)`. A sequence `r₁, …, rₙ` of `dim M` elements of `𝔪`
such that `(r₁, …, rₙ) + Ann M` has radical `𝔪` is `M`-regular. This is the case of
`isRegular_iff_supportDim_add_length_eq_supportDim` (Stacks, Proposition 10.103.4 (00N6)) in
which `M ⧸ (r₁, …, rₙ) M` is supported at the closed point, hence has dimension zero. -/
theorem isRegular_of_le_radical [Nontrivial M] (h : IsCohenMacaulay R M) {rs : List R}
    (hrs : ∀ r ∈ rs, r ∈ maximalIdeal R)
    (hrad : maximalIdeal R ≤ (ofList rs ⊔ annihilator R M).radical)
    (hlen : (rs.length : WithBot ℕ∞) = supportDim R M) : IsRegular M rs := by
  refine (h.isRegular_iff_supportDim_add_length_eq_supportDim rs hrs).2 ?_
  set N := M ⧸ ofList rs • (⊤ : Submodule R M)
  have hle : ofList rs ≤ maximalIdeal R := span_le.2 hrs
  have : Nontrivial N := Submodule.Quotient.nontrivial_iff.2
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (hle.trans (maximalIdeal_le_jacobson _))).symm
  have : Nontrivial (R ⧸ annihilator R N) :=
    Quotient.nontrivial_iff.2 (annihilator_eq_top_iff.not.2 (not_subsingleton N))
  -- Every prime containing the annihilator of `N` contains `rs` and `Ann M`, hence is `𝔪`.
  have hann : ofList rs ⊔ annihilator R M ≤ annihilator R N := sup_le
    (fun r hr ↦ mem_annihilator.2 fun n ↦ by
      induction n using Submodule.Quotient.induction_on with | H m => ?_
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul hr Submodule.mem_top)
    ((Submodule.mkQ _).annihilator_le_of_surjective (Submodule.mkQ_surjective _))
  have : Ring.KrullDimLE 0 (R ⧸ annihilator R N) :=
    krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.2 fun J hJ ↦ by
      have hJ' : maximalIdeal R ≤ J :=
        hrad.trans ((radical_mono (hann.trans hJ.1.2)).trans_eq hJ.1.1.radical)
      exact (maximalIdeal.isMaximal R).eq_of_le hJ.1.1.ne_top hJ' ▸ maximalIdeal.isMaximal R
  rw [supportDim_eq_ringKrullDim_quotient_annihilator,
    (ringKrullDimZero_iff_ringKrullDim_eq_zero).1 this, zero_add, hlen]

end Module.IsCohenMacaulay

namespace Module.IsCohenMacaulay

variable {R : Type*} {S : Type u} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
  [IsNoetherianRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]

/-- Let `R → S` be a local homomorphism of local rings with `S` Noetherian and Cohen–Macaulay. If
`r₁, …, rₙ` generate the maximal ideal of `R` and `dim S ⧸ 𝔪_R S + n = dim S`, then the images of
the `rᵢ` form an `S`-regular sequence. For a regular system of parameters of a regular local ring
`R`, this hypothesis is the dimension formula of miracle flatness (Stacks, Lemma 10.128.1
(00R4)). -/
theorem isRegular_map_algebraMap (hS : IsCohenMacaulay S S) {rs : List R}
    (hrs : ofList rs = maximalIdeal R)
    (hdim : ringKrullDim (S ⧸ (maximalIdeal R).map (algebraMap R S)) + rs.length =
      ringKrullDim S) :
    IsRegular S (rs.map (algebraMap R S)) := by
  refine (hS.isRegular_iff_supportDim_add_length_eq_supportDim _ fun r hr ↦ ?_).2 ?_
  · obtain ⟨r, hr', rfl⟩ := List.mem_map.1 hr
    exact map_nonunit (algebraMap R S) r (hrs ▸ subset_span hr')
  · rw [← map_ofList, hrs, smul_eq_mul, mul_top, supportDim_quotient_eq_ringKrullDim,
      List.length_map, supportDim_self_eq_ringKrullDim, hdim]

end Module.IsCohenMacaulay

namespace Module.IsCohenMacaulay

variable {R : Type*} {S : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing S]
  [IsLocalRing S] [IsNoetherianRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]

/-- Let `R → S` be a local homomorphism of Noetherian local rings with `S` Cohen–Macaulay and
`dim S = dim R + dim S ⧸ 𝔪_R S`. If `x ∈ R` satisfies `dim R ⧸ (x) + 1 = dim R`, for instance a
nonzero element of the maximal ideal of a regular local ring, then its image in `S` is
`S`-regular. -/
theorem isSMulRegular_algebraMap (hS : IsCohenMacaulay S S) (hdim : ringKrullDim S =
      ringKrullDim R + ringKrullDim (S ⧸ (maximalIdeal R).map (algebraMap R S)))
    {x : R} (hx : ringKrullDim (R ⧸ span {x}) + 1 = ringKrullDim R) :
    IsSMulRegular S (algebraMap R S x) := by
  have hxm := TauCeti.mem_maximalIdeal_of_ringKrullDim_quotient_span_singleton_add_one_eq hx
  have hxS : algebraMap R S x ∈ maximalIdeal S := map_nonunit _ x hxm
  have : Nontrivial (R ⧸ span {x}) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top IsPrime.ne_top' ((span_singleton_le_iff_mem _).mpr hxm))
  have : IsLocalRing (R ⧸ span {x}) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have hJ : (span {x}).map (algebraMap R S) ≤ maximalIdeal S := by
    rw [map_le_iff_le_comap, span_singleton_le_iff_mem]
    exact hxS
  have : Nontrivial (S ⧸ (span {x}).map (algebraMap R S)) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top IsPrime.ne_top' hJ)
  have : IsLocalRing (S ⧸ (span {x}).map (algebraMap R S)) :=
    .of_surjective' _ Ideal.Quotient.mk_surjective
  -- The closed fibre of `R ⧸ (x) → S ⧸ x S` is that of `R → S`, so
  -- `dim S ⧸ x S + 1 ≤ dim R ⧸ (x) + dim S ⧸ 𝔪_R S + 1 = dim S`.
  have hle : ringKrullDim (S ⧸ (span {x}).map (algebraMap R S)) + 1 ≤ ringKrullDim S := by
    have h := TauCeti.ringKrullDim_le_ringKrullDim_add_ringKrullDim_quotient_map_maximalIdeal
      (R := R ⧸ span {x}) (S := S ⧸ (span {x}).map (algebraMap R S))
    rw [TauCeti.ringKrullDim_quotient_map_maximalIdeal_quotient] at h
    rw [hdim, ← hx, add_right_comm]
    gcongr
  have hspan : (span {x}).map (algebraMap R S) = algebraMap R S x • (⊤ : Ideal S) := by
    simp [map_span, ← Submodule.ideal_span_singleton_smul]
  rw [hspan, ← supportDim_quotient_eq_ringKrullDim,
    ← supportDim_self_eq_ringKrullDim] at hle
  -- So the dimension drops by exactly one, and `x` is regular on the Cohen–Macaulay ring `S`.
  obtain ⟨k, hk⟩ := exists_supportDim_eq_natCast (R := S) (M := S)
  refine hS.isSMulRegular_of_supportDim_quotSMulTop_lt
    (hk ▸ ENat.WithBot.lt_natCast_of_add_one_eq ?_)
  exact hk ▸ le_antisymm hle (supportDim_le_supportDim_quotSMulTop_succ hxS)

/-- Under the hypotheses of `Module.IsCohenMacaulay.isSMulRegular_algebraMap`, the quotient
`S ⧸ x S` is a Cohen–Macaulay ring. -/
theorem quotient_map_span_singleton (hS : IsCohenMacaulay S S) (hdim : ringKrullDim S =
      ringKrullDim R + ringKrullDim (S ⧸ (maximalIdeal R).map (algebraMap R S)))
    {x : R} (hx : ringKrullDim (R ⧸ span {x}) + 1 = ringKrullDim R)
    [IsLocalRing (S ⧸ (span {x}).map (algebraMap R S))] :
    IsCohenMacaulay (S ⧸ (span {x}).map (algebraMap R S))
      (S ⧸ (span {x}).map (algebraMap R S)) := by
  have hxS : algebraMap R S x ∈ maximalIdeal S :=
    map_nonunit _ x (TauCeti.mem_maximalIdeal_of_ringKrullDim_quotient_span_singleton_add_one_eq hx)
  have h := (isCohenMacaulay_quotSMulTop_iff (isSMulRegular_algebraMap hS hdim hx) hxS).2 hS
  have hspan : algebraMap R S x • (⊤ : Ideal S) = (span {x}).map (algebraMap R S) := by
    simp [map_span, ← Submodule.ideal_span_singleton_smul]
  rw [(Submodule.quotEquivOfEq _ _ hspan).isCohenMacaulay_iff] at h
  exact (isCohenMacaulay_iff_isCohenMacaulay_self_of_surjective Ideal.Quotient.mk_surjective).1 h

/-- Under the hypotheses of `Module.IsCohenMacaulay.isSMulRegular_algebraMap`, the dimension
formula `dim S = dim R + dim S ⧸ 𝔪_R S` passes to the local homomorphism `R ⧸ (x) → S ⧸ x S`.
Together with `Module.IsCohenMacaulay.quotient_map_span_singleton`, this lets an induction on
`dim R` replace `R → S` by `R ⧸ (x) → S ⧸ x S`, as in the proof of miracle flatness (Stacks,
Lemma 10.128.1 (00R4)). -/
theorem ringKrullDim_quotient_map_span_singleton_eq (hS : IsCohenMacaulay S S)
    (hdim : ringKrullDim S =
      ringKrullDim R + ringKrullDim (S ⧸ (maximalIdeal R).map (algebraMap R S)))
    {x : R} (hx : ringKrullDim (R ⧸ span {x}) + 1 = ringKrullDim R)
    [IsLocalRing (R ⧸ span {x})] :
    ringKrullDim (S ⧸ (span {x}).map (algebraMap R S)) = ringKrullDim (R ⧸ span {x}) +
      ringKrullDim ((S ⧸ (span {x}).map (algebraMap R S)) ⧸
        (maximalIdeal (R ⧸ span {x})).map
          (algebraMap (R ⧸ span {x}) (S ⧸ (span {x}).map (algebraMap R S)))) := by
  have hxS : algebraMap R S x ∈ maximalIdeal S :=
    map_nonunit _ x (TauCeti.mem_maximalIdeal_of_ringKrullDim_quotient_span_singleton_add_one_eq hx)
  have h := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim
    (isSMulRegular_algebraMap hS hdim hx) hxS
  rw [← Set.image_singleton, ← map_span, hdim, ← hx, add_right_comm] at h
  rw [TauCeti.ringKrullDim_quotient_map_maximalIdeal_quotient]
  exact ENat.WithBot.add_one_cancel.1 h

end Module.IsCohenMacaulay

namespace Module.IsCohenMacaulay

variable {A B : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
  [IsIntegrallyClosed A] [CommRing B] [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]

/-- Let `A` be a Noetherian integrally closed local domain, `B` a finite torsion-free `A`-algebra
and `𝔮` a maximal ideal of `B` such that `B_𝔮` is Cohen–Macaulay. If `r₁, …, r_d` generate the
maximal ideal of `A`, where `d = dim A`, then their images form a `B_𝔮`-regular sequence. -/
theorem isRegular_map_algebraMap_localization {𝔮 : Ideal B} [𝔮.IsMaximal]
    (h : IsCohenMacaulay (Localization.AtPrime 𝔮) (Localization.AtPrime 𝔮)) {rs : List A}
    (hrs : ofList rs = maximalIdeal A) (hlen : (rs.length : WithBot ℕ∞) = ringKrullDim A) :
    IsRegular (Localization.AtPrime 𝔮) (rs.map (algebraMap A (Localization.AtPrime 𝔮))) := by
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  have hunder : 𝔮.under A = maximalIdeal A := eq_maximalIdeal inferInstance
  have : 𝔮.LiesOver (maximalIdeal A) := ⟨hunder.symm⟩
  have hmax : (maximalIdeal (Localization.AtPrime 𝔮)).comap
      (algebraMap A (Localization.AtPrime 𝔮)) = maximalIdeal A := by
    rw [← under_def, ← under_under (B := B), Localization.AtPrime.under_maximalIdeal, hunder]
  have : IsLocalHom (algebraMap A (Localization.AtPrime 𝔮)) :=
    ((local_hom_TFAE (algebraMap A (Localization.AtPrime 𝔮))).out 1 5).mpr hmax
  refine h.isRegular_map_algebraMap hrs ?_
  rw [ringKrullDim_localization_atPrime_quotient_map_eq_zero (maximalIdeal A) 𝔮, zero_add, hlen,
    ringKrullDim_localization_atPrime_eq_height_under A, hunder,
    maximalIdeal_height_eq_ringKrullDim]

end Module.IsCohenMacaulay

namespace TauCeti

variable {A B : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
  [IsIntegrallyClosed A] [CommRing B] [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]

/-- Let `A` be a two-dimensional Noetherian integrally closed local domain, `B` a finite
torsion-free `A`-algebra and `𝔮` a maximal ideal of `B` such that `B_𝔮` is a normal domain. Every
pair generating the maximal ideal of `A` maps to a regular sequence on `B_𝔮`. Here `B` need not
be local, and `B_𝔮` need not be finite over `A`. -/
theorem isRegular_pair_localization_of_isIntegrallyClosed (hdim : ringKrullDim A = 2)
    (𝔮 : Ideal B) [𝔮.IsMaximal] [IsDomain (Localization.AtPrime 𝔮)]
    [IsIntegrallyClosed (Localization.AtPrime 𝔮)] {x y : A} (hxy : span {x, y} = maximalIdeal A) :
    IsRegular (Localization.AtPrime 𝔮)
      [algebraMap A (Localization.AtPrime 𝔮) x, algebraMap A (Localization.AtPrime 𝔮) y] := by
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  -- Going down gives `B_𝔮` the dimension two of `A`, so the normal domain `B_𝔮` is
  -- Cohen–Macaulay.
  have : Ring.KrullDimLE 2 (Localization.AtPrime 𝔮) := by
    rw [Ring.krullDimLE_iff, Ideal.ringKrullDim_localization_atPrime_eq_height_under A,
      eq_maximalIdeal (inferInstance : (𝔮.under A).IsMaximal),
      maximalIdeal_height_eq_ringKrullDim, hdim]
    rfl
  exact Module.IsCohenMacaulay.isRegular_map_algebraMap_localization
    Module.isCohenMacaulay_self_of_isIntegrallyClosed_of_krullDimLE_two (rs := [x, y])
    (by rw [ofList_cons, ofList_singleton, ← span_insert, hxy]) (by rw [hdim]; rfl)

end TauCeti
end
end TAF_LiteralSource_0605

section TAF_LiteralSource_0606
/- Original module: TauCeti.LinearAlgebra.Span.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Finite spans and singleton spans

A generator with a unit coefficient in a linear combination can be replaced by that combination
without changing the span. Over a division semiring, a nonzero vector in a singleton span can be
used to recover the generator's membership in any submodule. Acting on a line gives the line
through the image of its generator, so a group element stabilizes the line through a vector
exactly when it sends that vector to a multiple of itself. Finally, a submodule over a
subring that is a direct sum `⊕ i, J i • y i` with nonzero ideal coefficients spans the same
subspace over the larger field as the family `y`.
-/

public section

namespace TauCeti.Submodule

variable {A : Type*} [Ring A] {M : Type*} [AddCommGroup M] [Module A M]

/-- If one coefficient of `x` in a finite span is a unit, then `x` can replace that generator. -/
theorem span_insert_erase_eq_span_of_isUnit [DecidableEq M] {s : Finset M} {i x : M}
    {f : M → A} (hi : i ∈ s) (hf : ∑ a ∈ s, f a • a = x) (hfi : IsUnit (f i)) :
    _root_.Submodule.span A ((insert x (s.erase i)) : Set M) =
      _root_.Submodule.span A (s : Set M) := by
  have hx : x ∈ _root_.Submodule.span A (s : Set M) :=
    hf ▸ sum_mem fun a ha ↦ Submodule.smul_mem _ _ (Submodule.subset_span ha)
  have hi' : i ∈ _root_.Submodule.span A (insert x (s.erase i : Set M)) := by
    refine (Submodule.smul_mem_iff_of_isUnit _ hfi).mp (Submodule.mem_span_insert.mpr
      ⟨1, -∑ a ∈ s.erase i, f a • a,
        neg_mem (sum_mem fun a ha ↦ Submodule.smul_mem _ _ (Submodule.subset_span ha)), ?_⟩)
    rw [one_smul, ← hf, ← Finset.add_sum_erase _ _ hi, add_neg_cancel_right]
  calc _ = _root_.Submodule.span A (insert i (insert x (s.erase i : Set M))) :=
        (Submodule.span_insert_eq_span hi').symm
    _ = _root_.Submodule.span A (insert x (s : Set M)) := by
      rw [Set.insert_comm, ← Finset.coe_insert, Finset.insert_erase hi]
    _ = _ := Submodule.span_insert_eq_span hx

end TauCeti.Submodule

namespace Submodule

variable {K V : Type*} [DivisionSemiring K] [AddCommMonoid V] [Module K V]

/-- If a nonzero member of a submodule lies in the span of `y`, then `y` also belongs to
the submodule. -/
theorem mem_of_mem_span_singleton_of_ne_zero (P : Submodule K V) {x y : V}
    (hx : x ∈ P) (hx0 : x ≠ 0) (hxy : x ∈ K ∙ y) : y ∈ P := by
  obtain ⟨c, rfl⟩ := mem_span_singleton.mp hxy
  exact (P.smul_mem_iff (left_ne_zero_of_smul hx0)).mp hx

section Action

open Pointwise

variable {R M G : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [Monoid G]
  [DistribMulAction G M] [SMulCommClass G R M]

/-- Acting on the line through `v` gives the line through the image of `v`. -/
theorem smul_span_singleton (g : G) (v : M) : g • (R ∙ v) = R ∙ (g • v) := by
  rw [smul_span, Set.smul_set_singleton]

end Action

section GroupAction

open Pointwise

variable {D W G : Type*} [DivisionRing D] [AddCommGroup W] [Module D W] [Group G]
  [DistribMulAction G W] [SMulCommClass G D W]

/-- A group element stabilizes the line through `v` exactly when `g • v` is a multiple of `v`. -/
theorem smul_span_singleton_eq_iff {g : G} {v : W} :
    g • (D ∙ v) = D ∙ v ↔ ∃ c : D, g • v = c • v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  rw [smul_span_singleton, span_singleton_eq_span_singleton]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨((z⁻¹ : Dˣ) : D), by rw [← Units.smul_def]; exact eq_inv_smul_iff.mpr hz⟩
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := left_ne_zero_of_smul (hc ▸ (smul_ne_zero_iff_ne g).mpr hv)
    exact ⟨(Units.mk0 c hc0)⁻¹, by simp [hc, Units.smul_def, smul_smul, hc0]⟩

end GroupAction

section IdealCoefficients

variable {R K V : Type*} [CommRing R] [Field K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V]

/-- If `Λ = ⊕ i, J i • y i` with every `J i` nonzero, then `y` spans the same `K`-subspace as
`Λ`. -/
theorem span_range_eq_span_of_forall_mem_iff [FaithfulSMul R K] {ι : Type*} [Fintype ι]
    {Λ : Submodule R V} {y : ι → V} {J : ι → Ideal R} (hJ : ∀ i, J i ≠ ⊥)
    (hmem : ∀ x, x ∈ Λ ↔ ∃ c : ι → R, (∀ i, c i ∈ J i) ∧ ∑ i, c i • y i = x) :
    span K (Set.range y) = span K (Λ : Set V) := by
  classical
  refine le_antisymm (span_le.2 <| Set.range_subset_iff.2 fun i ↦ ?_) (span_le.2 fun x hx ↦ ?_)
  · obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hJ i)
    have hsum : ∑ k, (Pi.single i b : ι → R) k • y k = b • y i := by
      rw [Fintype.sum_eq_single i fun k hk ↦ by simp [hk]]
      simp
    have hbΛ : b • y i ∈ Λ := hsum ▸ (hmem _).2 ⟨_, fun k ↦ by
      by_cases hk : k = i
      · subst hk
        simpa using hb
      · simp [hk], rfl⟩
    have hb' : algebraMap R K b ≠ 0 :=
      (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R K)).2 hb0
    rw [← inv_smul_smul₀ hb' (y i), algebraMap_smul]
    exact smul_mem _ _ (subset_span hbΛ)
  · obtain ⟨c, -, rfl⟩ := (hmem x).1 hx
    exact sum_mem fun i _ ↦ by
      rw [← algebraMap_smul K]
      exact smul_mem _ _ (subset_span ⟨i, rfl⟩)

end IdealCoefficients

end Submodule
end
end TAF_LiteralSource_0606

section TAF_LiteralSource_0607
/- Original module: TauCeti.RingTheory.LocalRing.MaximalIdeal.Square -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Elements of `𝔪 \ 𝔪²` in a local ring

For a local ring `R` with maximal ideal `𝔪`, elements of `𝔪 \ 𝔪²` are the ones that can be part
of a minimal system of generators of `𝔪`.

## Main declarations

* `TauCeti.IsLocalRing.spanFinrank_map_maximalIdeal_quotient_add_one_le`: for `x ∈ 𝔪 \ 𝔪²`, the
  maximal ideal of `R ⧸ (x)` needs at least one generator fewer than `𝔪`;
* `TauCeti.IsLocalRing.spanFinrank_map_maximalIdeal_quotient_of_le_sq`: dividing out an ideal
  contained in `𝔪²` does not change the number of generators of the maximal ideal;
* `TauCeti.IsLocalRing.exists_mem_maximalIdeal_notMem_sq_forall_notMem`: prime avoidance for
  `𝔪 \ 𝔪²` and finitely many primes other than `𝔪`;
* `TauCeti.IsLocalRing.exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes`: in a Noetherian
  local ring of positive dimension there is `x ∈ 𝔪 \ 𝔪²` outside every minimal prime;
* `TauCeti.IsLocalRing.exists_mem_maximalIdeal_notMem_sq_mem_nonZeroDivisors`: in a Noetherian
  local ring whose maximal ideal is not an associated prime there is a nonzerodivisor in
  `𝔪 \ 𝔪²`;
* `TauCeti.IsLocalRing.exists_comp_eq_id_of_notMem_sq`: for `x ∈ 𝔪 \ 𝔪²`, the residue field of
  `R ⧸ (x)` is a direct summand of `𝔪 ⧸ x 𝔪` as an `R ⧸ (x)`-module.

## References

* H. Matsumura, *Commutative Ring Theory*, Section 19, the proof of Theorem 19.2, for the direct
  summand `𝔪 ⧸ x 𝔪 ≅ κ ⊕ 𝔪 ⧸ (x)`.
-/

public section

namespace TauCeti.IsLocalRing

open _root_.IsLocalRing _root_.Ideal Pointwise

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- If `x ∈ 𝔪 \ 𝔪²`, then the image of `𝔪` in `R ⧸ (x)`, which is the maximal ideal of `R ⧸ (x)`,
needs at least one generator fewer than `𝔪`. -/
theorem spanFinrank_map_maximalIdeal_quotient_add_one_le (hfg : (maximalIdeal R).FG) {x : R}
    (hxm : x ∈ maximalIdeal R) (hx : x ∉ maximalIdeal R ^ 2) :
    ((maximalIdeal R).map (Ideal.Quotient.mk (span {x}))).spanFinrank + 1 ≤
      (maximalIdeal R).spanFinrank := by
  classical
  -- `x` replaces a generator with a unit coefficient in a minimal system of generators of `𝔪`
  obtain ⟨s, hcard, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp (hspan ▸ hxm)
  -- some coefficient of `x` is a unit, since otherwise `x ∈ 𝔪²`
  obtain ⟨i, hi, hfi⟩ : ∃ i ∈ s, IsUnit (f i) := by
    by_contra! h
    refine hx (hf ▸ Ideal.sum_mem _ fun i hi ↦ ?_)
    rw [pow_two, smul_eq_mul]
    exact mul_mem_mul (not_not.mp (mt notMem_maximalIdeal.mp (h i hi)))
      (hspan ▸ Submodule.subset_span hi)
  set q := Ideal.Quotient.mk (span {x})
  have hqx : q x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (mem_span_singleton_self x)
  have hmap : (maximalIdeal R).map q = span ((s.erase i).image q : Set (R ⧸ span {x})) := by
    rw [← hspan]
    rw [← TauCeti.Submodule.span_insert_erase_eq_span_of_isUnit hi hf hfi,
      Ideal.submodule_span_eq, Ideal.map_span,
      Set.image_insert_eq]
    rw [hqx, Ideal.span_insert_zero, Finset.coe_image]
  rw [hmap, ← hcard, ← Finset.card_erase_add_one hi, add_le_add_iff_right]
  refine (Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet _)).trans ?_
  rw [Set.ncard_coe_finset]
  exact Finset.card_image_le

/-- Dividing out an ideal contained in `𝔪²` does not change the number of generators needed for
the maximal ideal: the image of `𝔪` in `R ⧸ I` needs exactly as many generators as `𝔪`. -/
theorem spanFinrank_map_maximalIdeal_quotient_of_le_sq (hfg : (maximalIdeal R).FG) {I : Ideal R}
    (hI : I ≤ maximalIdeal R ^ 2) :
    ((maximalIdeal R).map (Ideal.Quotient.mk I)).spanFinrank = (maximalIdeal R).spanFinrank := by
  classical
  refine le_antisymm (Ideal.spanFinrank_map_le_of_fg _ hfg) ?_
  set q := Ideal.Quotient.mk I
  obtain ⟨s, hcard, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank (hfg.map q)
  -- lift a minimal system of generators of the image of `𝔪` to elements of `𝔪`
  have hlift (y : R ⧸ I) (hy : y ∈ s) : ∃ x ∈ maximalIdeal R, q x = y :=
    (mem_map_iff_of_surjective q Ideal.Quotient.mk_surjective).mp
      (hspan ▸ Submodule.subset_span hy)
  choose! g hgm hgq using hlift
  -- by Nakayama's lemma the lifts generate `𝔪`, since they generate it modulo `I ≤ 𝔪²`
  have hmap : (span (s.image g : Set R)).map q = span (s : Set (R ⧸ I)) := by
    rw [Ideal.map_span, Finset.coe_image, ← Set.image_comp]
    exact congrArg span ((Set.image_congr hgq).trans (Set.image_id _))
  have hle : maximalIdeal R ≤ span (s.image g : Set R) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot hfg
      (jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge fun x hx ↦ ?_
    have hx' : x ∈ ((span (s.image g : Set R)).map q).comap q := by
      rw [mem_comap, hmap, ← Ideal.submodule_span_eq, hspan]
      exact mem_map_of_mem q hx
    rw [comap_map_of_surjective' q Ideal.Quotient.mk_surjective, Ideal.mk_ker] at hx'
    rw [smul_eq_mul, ← pow_two]
    exact sup_le_sup_left hI _ hx'
  have heq : maximalIdeal R = span (s.image g : Set R) :=
    le_antisymm hle (span_le.mpr fun x hx ↦ by
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact hgm y hy)
  rw [← hcard]
  conv_lhs => rw [heq]
  refine (Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet _)).trans ?_
  rw [Set.ncard_coe_finset]
  exact Finset.card_image_le

/-- **Prime avoidance for `𝔪 \ 𝔪²`.** If the maximal ideal is neither contained in its square
nor one of finitely many primes `S`, then some element of `𝔪 \ 𝔪²` lies in no prime of `S`. -/
theorem exists_mem_maximalIdeal_notMem_sq_forall_notMem {S : Set (Ideal R)} (hS : S.Finite)
    (hprime : ∀ p ∈ S, p.IsPrime) (hsq : ¬maximalIdeal R ≤ maximalIdeal R ^ 2)
    (hm : maximalIdeal R ∉ S) :
    ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧ ∀ p ∈ S, x ∉ p := by
  by_contra! H
  have hsub : (maximalIdeal R : Set R) ⊆ ⋃ i ∈ insert (maximalIdeal R ^ 2) S, (i : Set R) := by
    intro x hx
    by_cases hx2 : x ∈ maximalIdeal R ^ 2
    · exact Set.mem_biUnion (Set.mem_insert _ _) hx2
    · obtain ⟨p, hp, hxp⟩ := H x hx hx2
      exact Set.mem_biUnion (Set.mem_insert_of_mem _ hp) hxp
  obtain ⟨i, hi, hmi⟩ := (subset_union_prime_finite (hS.insert _) (f := id)
    (maximalIdeal R ^ 2) (maximalIdeal R ^ 2)
    fun (i : Ideal R) hi hi₁ _ ↦ hprime i ((Set.mem_insert_iff.mp hi).resolve_left hi₁)).mp hsub
  rcases Set.mem_insert_iff.mp hi with rfl | hi
  · exact hsq hmi
  · -- a prime containing `𝔪` is `𝔪`
    exact hm (le_antisymm (le_maximalIdeal (hprime i hi).ne_top) hmi ▸ hi)

/-- In a Noetherian local ring of positive dimension there is an element of the maximal ideal
which lies neither in its square nor in any minimal prime. -/
theorem exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes [IsNoetherianRing R]
    (h : 0 < ringKrullDim R) :
    ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧ ∀ p ∈ minimalPrimes R, x ∉ p := by
  refine exists_mem_maximalIdeal_notMem_sq_forall_notMem
    (minimalPrimes.finite_of_isNoetherianRing R) (fun p hp ↦ hp.isPrime)
    (maximalIdeal_sq_lt_of_ringKrullDim_ne_zero h.ne').not_ge fun hm ↦ ?_
  -- `𝔪` would be a minimal prime, hence of height zero
  rw [← maximalIdeal_height_eq_ringKrullDim, height_eq_zero_iff.mpr hm] at h
  exact h.false

/-- In a Noetherian local ring whose maximal ideal is not an associated prime, that is, of
positive depth, there is a nonzerodivisor in `𝔪 \ 𝔪²`. -/
theorem exists_mem_maximalIdeal_notMem_sq_mem_nonZeroDivisors [IsNoetherianRing R]
    (h : maximalIdeal R ∉ associatedPrimes R R) :
    ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧ x ∈ nonZeroDivisors R := by
  have hsq : ¬maximalIdeal R ≤ maximalIdeal R ^ 2 := fun hle ↦ by
    -- `𝔪 = 𝔪²` forces `𝔪 = 0` by Nakayama's lemma; then every associated prime of `R` is `𝔪`
    have hm : maximalIdeal R = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (maximalIdeal R)
        (maximalIdeal R).fg_of_isNoetherianRing (by rwa [smul_eq_mul, ← pow_two])
        (jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    obtain ⟨p, hp⟩ := associatedPrimes.nonempty R R
    obtain rfl : p = maximalIdeal R := le_antisymm (le_maximalIdeal hp.isPrime.ne_top) (hm ▸ bot_le)
    exact h hp
  -- the zero divisors are the union of the finitely many associated primes
  obtain ⟨x, hxm, hx2, hx⟩ := exists_mem_maximalIdeal_notMem_sq_forall_notMem
    (associatedPrimes.finite R R) (fun p hp ↦ hp.isPrime) hsq h
  have : x ∉ ⋃ p ∈ associatedPrimes R R, (p : Set R) := by simpa using hx
  rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors, Set.notMem_compl_iff] at this
  exact ⟨x, hxm, hx2, this⟩

/-- **The residue field is a direct summand of `𝔪 ⧸ x 𝔪`.** For `x ∈ 𝔪 \ 𝔪²`, the residue field
`(R ⧸ (x)) ⧸ 𝔪 (R ⧸ (x))` of `R ⧸ (x)` is a retract of the `R ⧸ (x)`-module `𝔪 ⧸ x 𝔪`: the
section sends `1` to the class of `x`, and the retraction is a linear form on the cotangent space
`𝔪 ⧸ 𝔪²` taking the value `1` at `x`. -/
theorem exists_comp_eq_id_of_notMem_sq {x : R} (hxm : x ∈ maximalIdeal R)
    (hx : x ∉ maximalIdeal R ^ 2) :
    ∃ (i : (R ⧸ span {x}) ⧸ (maximalIdeal R).map (Ideal.Quotient.mk (span {x})) →ₗ[R ⧸ span {x}]
        maximalIdeal R ⧸ span {x} • (⊤ : Submodule R (maximalIdeal R)))
      (r : maximalIdeal R ⧸ span {x} • (⊤ : Submodule R (maximalIdeal R)) →ₗ[R ⧸ span {x}]
        (R ⧸ span {x}) ⧸ (maximalIdeal R).map (Ideal.Quotient.mk (span {x}))),
      r ∘ₗ i = LinearMap.id := by
  set I := span {x}
  set q := Ideal.Quotient.mk I
  have hN : I • (⊤ : Submodule R (maximalIdeal R)) = x • ⊤ :=
    Submodule.ideal_span_singleton_smul x ⊤
  -- `i` sends `1` to the class of `x`, which `𝔪` kills modulo `x 𝔪`.
  let x' : maximalIdeal R := ⟨x, hxm⟩
  have hi : (maximalIdeal R).map q ≤ LinearMap.ker (LinearMap.toSpanSingleton (R ⧸ I) _
      (Submodule.Quotient.mk (p := I • (⊤ : Submodule R (maximalIdeal R))) x')) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [mem_comap, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply,
      Module.Quotient.mk_smul_mk, Submodule.Quotient.mk_eq_zero, hN]
    convert Submodule.smul_mem_pointwise_smul (⟨a, ha⟩ : maximalIdeal R) x ⊤ trivial using 1
    ext
    simp [x', mul_comm]
  let i := ((maximalIdeal R).map q).liftQ _ hi
  -- `r` is a linear form on the cotangent space `𝔪 ⧸ 𝔪²` taking the value `1` at `x`.
  have hx0 : (maximalIdeal R).toCotangent x' ≠ 0 := by
    rwa [Ne, Ideal.toCotangent_eq_zero]
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one (ResidueField R) hx0
  let ψ : maximalIdeal R →ₗ[R] ResidueField R :=
    φ.restrictScalars R ∘ₗ (maximalIdeal R).toCotangent
  have hψ : I • (⊤ : Submodule R (maximalIdeal R)) ≤ LinearMap.ker ψ := by
    rw [hN]
    rintro _ ⟨m, -, rfl⟩
    rw [LinearMap.mem_ker, DistribSMul.toLinearMap_apply, map_smul, Algebra.smul_def,
      IsLocalRing.ResidueField.algebraMap_eq, (IsLocalRing.residue_eq_zero_iff x).mpr hxm,
      zero_mul]
  let θ : ResidueField R →ₗ[R] (R ⧸ I) ⧸ (maximalIdeal R).map q :=
    (Ideal.quotientMapₐ ((maximalIdeal R).map q) (Ideal.Quotient.mkₐ R I)
      Ideal.le_comap_map).toLinearMap
  let r := (θ ∘ₗ Submodule.liftQ _ ψ hψ).extendScalarsOfSurjective
    (Ideal.Quotient.mk_surjective (I := I))
  refine ⟨i, r, Submodule.linearMap_qext _ (LinearMap.ext_ring ?_)⟩
  have hi1 : i (Submodule.Quotient.mk 1) = Submodule.Quotient.mk x' := by
    rw [Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]
  have hr : r (Submodule.Quotient.mk x') = 1 := by
    rw [LinearMap.extendScalarsOfSurjective_apply, LinearMap.comp_apply, Submodule.liftQ_apply,
      LinearMap.comp_apply, LinearMap.restrictScalars_apply, hφ]
    exact map_one (Ideal.quotientMapₐ ((maximalIdeal R).map q) (Ideal.Quotient.mkₐ R I)
      Ideal.le_comap_map)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply, hi1, hr,
    LinearMap.comp_apply, LinearMap.id_apply, Submodule.mkQ_apply, Ideal.Quotient.mk_eq_mk,
    map_one]

end TauCeti.IsLocalRing
end
end TAF_LiteralSource_0607

section TAF_LiteralSource_0608
/- Original module: TauCeti.RingTheory.RegularLocalRing.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/


/-!
# Regular local rings are domains, and localizations of regular rings

A Noetherian local ring `R` is regular (`IsRegularLocalRing`) when its maximal ideal `𝔪` can be
generated by `dim R` elements. This file proves that a regular local ring is an integral domain.
Consequently the local rings of a regular scheme are domains, which is what makes a connected
regular scheme irreducible, and a regular local ring of dimension one is a discrete valuation
ring, so that the local rings of a regular curve at its codimension-one points are discrete
valuation rings. The file also shows that every localization of a regular ring (`IsRegularRing`)
is a regular ring, so that every `Localization M` of a regular ring, including
`Localization.AtPrime p`, is again a regular ring.

## Main declarations

* `TauCeti.IsRegularLocalRing.isDomain`: a regular local ring is an integral domain;
* `TauCeti.IsRegularLocalRing.quotient_span_singleton`: for `x ∈ 𝔪 \ 𝔪²`, the quotient `R ⧸ (x)`
  is again a regular local ring, and `TauCeti.IsRegularLocalRing.quotient_span_singleton_iff`: for
  a nonzero `x ∈ 𝔪` this happens exactly when `x ∉ 𝔪²`, in which case
  `TauCeti.IsRegularLocalRing.spanFinrank_maximalIdeal_quotient_span_singleton_add_one` shows that
  the maximal ideal of `R ⧸ (x)` needs one generator fewer;
* `Ideal.exists_mem_notMem_maximalIdeal_sq_of_quotient`: a nonzero ideal with regular quotient
  contains an element outside `𝔪²`, also used by the one-element criterion;
* `TauCeti.IsRegularLocalRing.span_singleton_isPrime_of_notMem_sq`: the quotient by such a
  parameter is a domain, so the ideal the parameter generates is prime, the hypothesis the
  statements for an irreducible first equation of `TauCeti.RingTheory.Intersection` take;
* `TauCeti.IsRegularLocalRing.of_maximalIdeal_eq_span_singleton`: a Noetherian local ring whose
  maximal ideal is generated by a nonzerodivisor is a regular local ring;
* `TauCeti.IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one`: a regular local
  ring is a discrete valuation ring exactly when it has dimension one;
* `TauCeti.IsRegularLocalRing.valuationRing_of_ringKrullDim_le_one`: a regular local ring of
  dimension at most one is a valuation ring.
* `TauCeti.IsRegularRing.of_isLocalization`: a localization of a regular ring is a regular ring,
  with the instance `TauCeti.IsRegularRing.isRegularRing_localization` for `Localization M`.
* `TauCeti.IsRegularRing.isReduced`: a regular ring is reduced, since its local rings are domains.

## References

* [The Stacks Project, Lemma 10.106.2](https://stacks.math.columbia.edu/tag/00NP),
  [Lemma 10.106.3](https://stacks.math.columbia.edu/tag/00NQ), and
  [Lemma 10.106.4](https://stacks.math.columbia.edu/tag/00NR).
* M. F. Atiyah and I. G. Macdonald, *Introduction to Commutative Algebra*, Lemma 11.23.
* `TauCeti.IsRegularRing.of_isLocalization` generalizes from localizations at primes to
  all localizations the lemma `Pcf.Stacks.isRegularRing_localization_atPrime` of T. Dupuy,
  T. Tucker and Z. Wang, [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at
  commit `a39c3781b9850b9f3d5cbc9920322a3b8e365ef2` (Apache-2.0),
  `lean/Pcf/Stacks/Common/RegularNormal.lean`.
-/

public section

namespace TauCeti

universe u

open _root_.IsLocalRing _root_.Ideal Pointwise _root_.IsRegularLocalRing

variable {R : Type u} [CommRing R]

open TauCeti.IsLocalRing

namespace IsRegularLocalRing

/-- A Noetherian local ring whose maximal ideal is generated by a nonzerodivisor is a regular local
ring. -/
theorem of_maximalIdeal_eq_span_singleton [_root_.IsLocalRing R] [IsNoetherianRing R] {x : R}
    (hx : x ∈ nonZeroDivisors R) (h : maximalIdeal R = span {x}) : IsRegularLocalRing R := by
  have hdim := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hx
    (h ▸ mem_span_singleton_self x)
  rw [← h, ringKrullDim_eq_zero_of_isField
      ((Quotient.maximal_ideal_iff_isField_quotient _).mp (maximalIdeal.isMaximal R)),
    zero_add] at hdim
  refine of_spanFinrank_maximalIdeal_le R ?_
  -- `R ⧸ (x)` is the residue field, so `R` has dimension one
  rw [← hdim, h]
  exact_mod_cast (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton x)).trans
    (by simp)

variable [IsRegularLocalRing R]

/-- The induction step: for `x ∈ 𝔪 \ 𝔪²` outside every minimal prime, `R ⧸ (x)` is regular. -/
private lemma quotient_aux {x : R} (hxm : x ∈ maximalIdeal R) (hx : x ∉ maximalIdeal R ^ 2)
    (hmin : ∀ p ∈ minimalPrimes R, x ∉ p) :
    IsRegularLocalRing (R ⧸ span {x}) := by
  have : Nontrivial (R ⧸ span {x}) := Ideal.Quotient.nontrivial_iff.mpr fun h ↦
    (maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (h ▸ (span_singleton_le_iff_mem _).mpr hxm))
  have := IsLocalRing.of_surjective' (Ideal.Quotient.mk (span {x})) Ideal.Quotient.mk_surjective
  apply of_spanFinrank_maximalIdeal_le
  have h₁ := spanFinrank_map_maximalIdeal_quotient_add_one_le
    (maximalIdeal R).fg_of_isNoetherianRing hxm hx
  rw [map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective] at h₁
  have h₂ :=
   ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_notMem_minimalPrimes_of_mem_jacobson
      hmin (by rwa [ringJacobson_eq_maximalIdeal R])
  rw [← spanFinrank_maximalIdeal (R := R)] at h₂
  obtain ⟨k, hk⟩ : ∃ k, (maximalIdeal R).spanFinrank = k + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
  rw [hk] at h₁ h₂
  rw [Nat.cast_succ, ENat.WithBot.add_one_cancel] at h₂
  rw [h₂]
  exact_mod_cast (by omega : (maximalIdeal (R ⧸ span {x})).spanFinrank ≤ k)

/-- A regular local ring of dimension `n` is a domain. -/
private theorem isDomain_of_ringKrullDim_eq (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R], ringKrullDim R = n → IsDomain R := by
  -- Induction on `n`: for `n > 0` pick `x ∈ 𝔪 \ 𝔪²` outside every minimal prime; then `R ⧸ (x)`
  -- is regular of dimension `n - 1`, hence a domain, so `(x)` is prime, and a minimal prime
  -- `P ⊆ (x)` satisfies `P = x P`, so `P = 0` by Nakayama's lemma.
  induction n with
  | zero =>
    intro R _ _ h
    have hm : maximalIdeal R = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot (maximalIdeal R).fg_of_isNoetherianRing).mp
        (by exact_mod_cast (spanFinrank_maximalIdeal (R := R)).trans h)
    exact (isField_iff_maximalIdeal_eq.mpr hm).isDomain
  | succ n ih =>
    intro R _ _ h
    obtain ⟨x, hxm, hx, hmin⟩ :=
      exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes (R := R)
        (by rw [h]; exact_mod_cast n.succ_pos)
    have := quotient_aux hxm hx hmin
    have hdim : ringKrullDim (R ⧸ span {x}) = n := by
      have := (
ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_notMem_minimalPrimes_of_mem_jacobson
        hmin (by rwa [ringJacobson_eq_maximalIdeal R]))
      rw [h, Nat.cast_succ, ENat.WithBot.add_one_cancel] at this
      exact this
    have hprime : (span {x}).IsPrime := (Quotient.isDomain_iff_prime (span {x})).mp (ih _ hdim)
    -- a minimal prime `P ⊆ (x)` satisfies `P = x P`, hence vanishes by Nakayama's lemma
    obtain ⟨P, hP, hPx⟩ := exists_minimalPrimes_le (bot_le : ⊥ ≤ span {x})
    have hPprime : P.IsPrime := IsMinimalPrime.isPrime hP
    have hP0 : P = ⊥ := by
      refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (span {x}) P
        P.fg_of_isNoetherianRing (fun y hy ↦ ?_) ?_
      · obtain ⟨z, rfl⟩ := mem_span_singleton'.mp (hPx hy)
        have hz : z ∈ P := (hPprime.mem_or_mem hy).resolve_right (hmin P hP)
        rw [mul_comm, ← smul_eq_mul]
        exact Submodule.smul_mem_smul (mem_span_singleton_self x) hz
      · rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top, span_singleton_le_iff_mem]
        exact hxm
    have : (⊥ : Ideal R).IsPrime := hP0 ▸ hPprime
    exact IsDomain.of_bot_isPrime R

/-- **A regular local ring is an integral domain.** -/
@[stacks 00NP]
instance (priority := 100) isDomain : IsDomain R :=
  isDomain_of_ringKrullDim_eq _ R (spanFinrank_maximalIdeal (R := R)).symm

/-- A nonzero ideal of a regular local ring with regular quotient contains a parameter. -/
theorem _root_.Ideal.exists_mem_notMem_maximalIdeal_sq_of_quotient (I : Ideal R)
    [IsRegularLocalRing (R ⧸ I)] (hne : I ≠ ⊥) :
    ∃ parameter ∈ I, parameter ∉ maximalIdeal R ^ 2 := by
  by_contra! hall
  have hemb := TauCeti.IsLocalRing.spanFinrank_map_maximalIdeal_quotient_of_le_sq
    (maximalIdeal R).fg_of_isNoetherianRing hall
  rw [map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective] at hemb
  obtain ⟨element, hmem, hzero⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hle : span {element} ≤ I := (span_singleton_le_iff_mem _).mpr hmem
  have hdim := ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle)
    (Ideal.Quotient.factor_surjective hle)
  have hdrop := ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    (mem_nonZeroDivisors_of_ne_zero hzero)
  have hbad := (add_le_add hdim (le_refl 1)).trans hdrop
  rw [← spanFinrank_maximalIdeal (R := R ⧸ I),
    ← spanFinrank_maximalIdeal (R := R), hemb] at hbad
  exact absurd hbad (by norm_cast; omega)

/-- If `R` is a regular local ring and `x ∈ 𝔪 \ 𝔪²`, then `R ⧸ (x)` is a regular local ring. -/
@[stacks 00NQ "(2), for one generator"]
theorem quotient_span_singleton {x : R} (hxm : x ∈ maximalIdeal R)
    (hx : x ∉ maximalIdeal R ^ 2) : IsRegularLocalRing (R ⧸ span {x}) := by
  -- the only minimal prime of the domain `R` is `0`, and `x ≠ 0` as `x ∉ 𝔪²`
  refine quotient_aux hxm hx fun p hp hxp ↦ hx ?_
  rw [IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff] at hp
  have hx0 : x = 0 := by simpa [hp] using hxp
  rw [hx0]
  exact zero_mem _

/-- If `R` is a regular local ring and `x ∈ 𝔪` is nonzero, then `R ⧸ (x)` is a regular local ring
exactly when `x ∉ 𝔪²`. -/
theorem quotient_span_singleton_iff {x : R} (hxm : x ∈ maximalIdeal R) (hx0 : x ≠ 0) :
    IsRegularLocalRing (R ⧸ span {x}) ↔ x ∉ maximalIdeal R ^ 2 := by
  refine ⟨fun _ hx ↦ ?_, quotient_span_singleton hxm⟩
  obtain ⟨parameter, hmem, hnot⟩ :=
    _root_.Ideal.exists_mem_notMem_maximalIdeal_sq_of_quotient (span {x})
      (span_singleton_eq_bot.not.mpr hx0)
  exact hnot (((span_singleton_le_iff_mem _).mpr hx) hmem)

/-- If `R` is a regular local ring and `x ∈ 𝔪` is nonzero with `R ⧸ (x)` regular, then the
maximal ideal of `R ⧸ (x)` needs exactly one generator fewer than `𝔪`. -/
theorem spanFinrank_maximalIdeal_quotient_span_singleton_add_one {x : R}
    (hxm : x ∈ maximalIdeal R) (hx0 : x ≠ 0) [IsRegularLocalRing (R ⧸ span {x})] :
    (maximalIdeal (R ⧸ span {x})).spanFinrank + 1 = (maximalIdeal R).spanFinrank := by
  have hdim := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hx0) hxm
  rw [← spanFinrank_maximalIdeal (R := R ⧸ span {x}), ← spanFinrank_maximalIdeal (R := R)] at hdim
  exact_mod_cast hdim

/-- **The curve a parameter cuts out is a domain, so its principal ideal is prime.** Let
`(R, 𝔪)` be a regular local ring and let `f ∈ 𝔪 \ 𝔪²`, so that `f` is a parameter. Then the
quotient `R ⧸ (f)` is a regular local ring by
`TauCeti.IsRegularLocalRing.quotient_span_singleton`, hence a domain by
`TauCeti.IsRegularLocalRing.isDomain`, and `Ideal.Quotient.isDomain_iff_prime` reads that back as
the primality of `(f)`, the hypothesis the statements for an irreducible first equation of
`TauCeti.RingTheory.Intersection` take. A consumer needing the domain instance itself obtains it
from the primality, as `(Ideal.Quotient.isDomain_iff_prime _).mp` of it.

In a ring of Krull dimension two that curve is a discrete valuation ring as well, being a regular
local ring of dimension one by `TauCeti.ringKrullDim_quotient_span_singleton_eq_one` and therefore
by `TauCeti.IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one`. -/
theorem span_singleton_isPrime_of_notMem_sq {f : R} (hfm : f ∈ maximalIdeal R)
    (hf2 : f ∉ maximalIdeal R ^ 2) : (span {f}).IsPrime := by
  let _ : IsRegularLocalRing (R ⧸ span {f}) := quotient_span_singleton hfm hf2
  exact (Quotient.isDomain_iff_prime (span {f})).mp isDomain

/-- A regular local ring is a discrete valuation ring exactly when it has dimension one. -/
theorem isDiscreteValuationRing_iff_ringKrullDim_eq_one :
    IsDiscreteValuationRing R ↔ ringKrullDim R = 1 := by
  refine ⟨fun _ ↦ IsDiscreteValuationRing.ringKrullDim_eq_one R, fun h ↦ ?_⟩
  rw [← finrank_CotangentSpace_eq_one_iff]
  have := (iff_finrank_cotangentSpace R).mp inferInstance
  rw [h] at this
  exact_mod_cast this

/-- A regular local ring of dimension at most one is a valuation ring: a field in dimension zero
and a discrete valuation ring in dimension one. -/
theorem valuationRing_of_ringKrullDim_le_one (h : ringKrullDim R ≤ 1) : ValuationRing R := by
  by_cases h1 : ringKrullDim R = 1
  · have := isDiscreteValuationRing_iff_ringKrullDim_eq_one.mpr h1
    infer_instance
  · have : Ring.KrullDimLE 0 R := by
      rw [Ring.krullDimLE_iff]
      exact Order.le_of_lt_succ (lt_of_le_of_ne h h1)
    let := (Ring.KrullDimLE.isField_of_isDomain (R := R)).toField
    exact ValuationRing.of_field R

end IsRegularLocalRing

namespace IsRegularRing

variable [IsRegularRing R] (M : Submonoid R)

/-- A localization of a regular ring is a regular ring. -/
theorem of_isLocalization (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S] :
    IsRegularRing S := by
  have := IsLocalization.isNoetherianRing M S inferInstance
  refine isRegularRing_iff.mpr fun q _ ↦ ?_
  -- `S_q` is the localization of `R` at the contraction of `q`
  have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
    (Localization.AtPrime q) q
  exact .of_ringEquiv (IsLocalization.algEquiv (q.comap (algebraMap R S)).primeCompl
    (Localization.AtPrime (q.comap (algebraMap R S))) (Localization.AtPrime q)).toRingEquiv

instance isRegularRing_localization : IsRegularRing (Localization M) :=
  of_isLocalization M _

/-- A regular ring is reduced: its localizations at maximal ideals are regular local rings, hence
domains. -/
instance (priority := 100) isReduced : IsReduced R :=
  isReduced_ofLocalizationMaximal _ fun _ _ ↦ inferInstance

end IsRegularRing

end TauCeti
end
end TAF_LiteralSource_0608

section TAF_LiteralSource_0609
/- Original module: TauCeti.Algebra.Module.SpanRank -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li, Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/


/-!
# Generating families and the least number of generators

For a finitely generated submodule, its least number of generators is at most `n` exactly
when it has a generating family indexed by `Fin n`. A minimum generating finset can be
embedded in `Fin n`, with zero at the unused indices. This includes the zero submodule
and the empty family.

If `p ≤ q` are submodules with `p` finitely generated, the `spanFinrank` of `q` is bounded by
those of `p` and the image of `q` in `M ⧸ p`. When `q` is finitely generated, this bounds its
least number of generators: generators of `p` together with lifts of generators of the image
generate `q`. For a non-finitely-generated submodule, `spanFinrank` is defined to be `0`.

## Main results

* `Submodule.FG.spanFinrank_le_iff_exists_fin_generating_family`: `p.spanFinrank ≤ n` exactly
  when `p` is spanned by a family indexed by `Fin n`.
* `Submodule.spanFinrank_span_list_le_length`: the span of a list needs at most as many
  generators as the list's length.
* `Submodule.spanFinrank_restrictScalars_eq`: restricting scalars along a surjective
  `algebraMap` preserves `spanFinrank`.
* `Submodule.spanFinrank_le_spanFinrank_map_mkQ_add_spanFinrank`: for `p ≤ q` with `p`
  finitely generated, `q.spanFinrank ≤ (q.map p.mkQ).spanFinrank + p.spanFinrank`.

## References

* The bound through a quotient is the generator-lifting step in the proof of
  [Stacks Project, Lemma 10.106.7](https://stacks.math.columbia.edu/tag/00NU). It is ported from
  T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0),
  `lean/Pcf/Bounding/PrincipalQuotientRegular.lean`, and generalizes its
  `Pcf.spanFinrank_maximalIdeal_le_add_one_of_principal_kernel` from a principal kernel and the
  maximal ideal of a local ring to any submodules `p ≤ q` with `p` finitely generated.
-/

public section

namespace Submodule

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- A finitely generated submodule has at most `n` generators exactly when it is spanned
by a family of length `n`. Zero entries may pad a shorter generating family. -/
theorem FG.spanFinrank_le_iff_exists_fin_generating_family {p : Submodule R M}
    (hp : p.FG) (n : ℕ) :
    p.spanFinrank ≤ n ↔ ∃ f : Fin n → M, span R (Set.range f) = p := by
  classical
  constructor
  · intro hn
    obtain ⟨s, hs, hspan⟩ := hp.exists_span_finset_card_eq_spanFinrank
    let e : s ↪ Fin n := s.equivFin.toEmbedding.trans
      ⟨Fin.castLE (hs.trans_le hn), Fin.castLE_injective _⟩
    let f : Fin n → M := Function.extend e Subtype.val (fun _ ↦ 0)
    refine ⟨f, le_antisymm ?_ ?_⟩
    · apply span_le.mpr
      rintro x ⟨i, rfl⟩
      dsimp [f]
      rw [Function.extend_def]
      split_ifs with hi
      · exact hspan ▸ subset_span (Classical.choose hi).property
      · exact p.zero_mem
    · rw [← hspan]
      apply span_mono
      intro x hx
      refine ⟨e ⟨x, hx⟩, ?_⟩
      exact e.injective.extend_apply Subtype.val (fun _ ↦ 0) ⟨x, hx⟩
  · rintro ⟨f, rfl⟩
    exact (spanFinrank_span_le_ncard_of_finite (Set.finite_range f)).trans
      (by simpa using (Set.ncard_image_le (f := f) (s := Set.univ)))

/-- The span of the entries of a list needs at most as many generators as the list has entries. -/
theorem spanFinrank_span_list_le_length (l : List M) :
    (span R {x | x ∈ l}).spanFinrank ≤ l.length := by
  classical
  calc (span R {x | x ∈ l}).spanFinrank ≤ {x | x ∈ l}.ncard :=
        spanFinrank_span_le_ncard_of_finite l.finite_toSet
    _ = l.toFinset.card := by rw [← Set.ncard_coe_finset]; simp
    _ ≤ l.length := l.toFinset_card_le

section RestrictScalars

variable {R S : Type*} {M : Type u} [CommSemiring R] [Semiring S] [AddCommMonoid M]
  [Algebra R S] [Module R M] [Module S M] [IsScalarTower R S M]

/-- Along a surjective `algebraMap R S`, restricting scalars does not change the least number of
generators of an `S`-submodule. -/
theorem spanFinrank_restrictScalars_eq (H : Function.Surjective (algebraMap R S))
    (N : Submodule S M) : (N.restrictScalars R).spanFinrank = N.spanFinrank := by
  rw [spanFinrank, spanFinrank, spanRank_restrictScalars_eq H]

end RestrictScalars

end Submodule

namespace Submodule

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- If `p ≤ q` are submodules with `p` finitely generated, then `q.spanFinrank` is at most the
sum of the `spanFinrank`s of `p` and of the image of `q` in `M ⧸ p`. When `q` is finitely
generated, this is a generator bound: generators of `p` and lifts of generators of the image
generate `q`. For non-finitely-generated `q`, `q.spanFinrank` is defined to be `0`. -/
theorem spanFinrank_le_spanFinrank_map_mkQ_add_spanFinrank {p q : Submodule R M} (hpq : p ≤ q)
    (hp : p.FG) : q.spanFinrank ≤ (q.map p.mkQ).spanFinrank + p.spanFinrank := by
  classical
  by_cases hq : q.FG
  swap
  · simp [spanFinrank_of_not_fg hq]
  obtain ⟨t, ht, htspan⟩ := (hq.map p.mkQ).exists_span_finset_card_eq_spanFinrank
  obtain ⟨s, hs, hsspan⟩ := hp.exists_span_finset_card_eq_spanFinrank
  let g : M ⧸ p → M := Function.surjInv p.mkQ_surjective
  have hg : ∀ y, p.mkQ (g y) = y := Function.surjInv_eq p.mkQ_surjective
  -- the lifts of the generators of the image of `q` generate `q` modulo `p`
  have hlift : (span R (t.image g : Set M)).map p.mkQ = q.map p.mkQ := by
    rw [map_span, Finset.coe_image, ← Set.image_comp, ← htspan]
    congr 1
    simp [hg]
  -- equal images modulo `p`, and `p ≤ q`
  have hspan : span R (s ∪ t.image g : Finset M) = q := by
    have hsup := congrArg (comap p.mkQ) hlift
    rw [comap_map_mkQ, comap_map_mkQ, sup_eq_right.mpr hpq] at hsup
    rw [Finset.coe_union, span_union, hsspan, hsup]
  have hcard : (s ∪ t.image g).card ≤ s.card + t.card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_image_le _)
  calc q.spanFinrank ≤ (s ∪ t.image g).card := by
        have hbound :=
          (spanFinrank_span_le_ncard_of_finite (R := R) (M := M)
            (s := ↑(s ∪ t.image g : Finset M)) (s ∪ t.image g).finite_toSet)
        simpa only [Set.ncard_coe_finset, hspan] using hbound
    _ ≤ _ := by omega

end Submodule
end
end TAF_LiteralSource_0609

section TAF_LiteralSource_0610
/- Original module: TauCeti.LinearAlgebra.Matrix.Adjugate.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Matrix adjugation

This file records dimension-independent consequences of the standard matrix adjugate identities.

The adjugate identity `adj A * A = det A • 1` also acts on vectors with entries in a module: if a
family `v` of elements of a `K`-module satisfies the linear relations `∑ⱼ A i j • v j = 0`, then
`det A` kills every `v k` (`Matrix.det_smul_eq_zero_of_sum_smul_eq_zero`). This is the
determinant trick behind the Cayley–Hamilton and Nakayama arguments for finitely generated modules.

The same identity cancels a square matrix `A` with `A * B = c • 1` for a non-zero-divisor `c`, so
that `B * A = c • 1` as well (`Matrix.mul_eq_smul_one_comm`). For `c = 1` this is
`mul_eq_one_comm`; for general `c` it compares a form with its `c`-scaled dual, whose Gram matrix
is `c` times the inverse Gram matrix.
-/

public section

namespace Matrix

variable {K : Type*} [CommRing K]

/-- For a square matrix with finite indices, the left adjugate equation is equivalent to
determinant one. -/
@[simp]
theorem adjugate_mul_self_eq_one_iff_det_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) :
    Matrix.adjugate A * A = 1 ↔ A.det = 1 := by
  cases isEmpty_or_nonempty n with
  | inl _ =>
      constructor
      · intro _
        simp
      · intro _
        exact Subsingleton.elim _ _
  | inr _ =>
      constructor
      · intro h
        rw [Matrix.adjugate_mul] at h
        let i : n := Classical.choice (inferInstance : Nonempty n)
        have hii := congrArg (fun M : Matrix n n K ↦ M i i) h
        simpa using hii
      · intro h
        rw [Matrix.adjugate_mul, h, one_smul]

/-- **The determinant trick.** If a family `v` of elements of a module satisfies the linear
relations `∑ⱼ A i j • v j = 0` for every `i`, then `det A` kills every member of the family. -/
theorem det_smul_eq_zero_of_sum_smul_eq_zero {ι M : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid M] [Module K M] (A : Matrix ι ι K) {v : ι → M}
    (hv : ∀ i, ∑ j, A i j • v j = 0) (k : ι) : A.det • v k = 0 := by
  calc A.det • v k = ∑ j, (A.adjugate * A) k j • v j := by
        simp [Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply, mul_ite, ite_smul]
    _ = ∑ i, A.adjugate k i • ∑ j, A i j • v j := by
        simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
        exact Finset.sum_comm
    _ = 0 := by simp [hv]

/-- **Inverses up to a scalar commute.** If `A * B = c • 1` for square matrices over a commutative
ring and a non-zero-divisor `c`, then `B * A = c • 1`. -/
theorem mul_eq_smul_one_comm {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n K} {c : K}
    (hc : c ∈ nonZeroDivisors K) : A * B = c • 1 ↔ B * A = c • 1 := by
  suffices key : ∀ A B : Matrix n n K, A * B = c • 1 → B * A = c • 1 from ⟨key A B, key B A⟩
  intro A B h
  -- `det A` divides a power of `c`, so it is a non-zero-divisor and cancels `A` on the left.
  have hdet : A.det ∈ nonZeroDivisors K := by
    have := congrArg det h
    rw [det_mul, det_smul, det_one, mul_one] at this
    exact (mul_mem_nonZeroDivisors.mp (this ▸ pow_mem hc _)).1
  refine (isRegular_of_isLeftRegular_det
    (isRegular_iff_mem_nonZeroDivisors.mpr hdet).left).left ?_
  change A * (B * A) = A * (c • 1)
  rw [← Matrix.mul_assoc, h, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

end Matrix
end
end TAF_LiteralSource_0610

section TAF_LiteralSource_0611
/- Original module: TauCeti.RingTheory.Spectrum.Prime.Point -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Field-valued points and residue-field data

An algebra map to a field determines a prime ideal and an embedding of its
residue field. Conversely, these data determine the algebra map. For a map to the residue field
`κ(P)` of a prime `P` of the base, the embedding is an isomorphism
(`AlgHom.residueFieldMap_bijective`).
The forward map from residue-field data is defined for any commutative target algebra.

## References

* Stacks Project, Tag 04GW.
* Taylor Dupuy, Thomas Tucker, and Zhuoran Wang, pcfawd-formalization at `9a20b3f`,
  `lean/Pcf/Stacks/Abhyankar/StrictHenselizationConstruction.lean`,
  `PointedEtaleNeighborhood`.
-/

public section

namespace AlgHom

variable {R S Ω : Type*} [CommRing R] [CommRing S] [Field Ω] [Algebra R S] [Algebra R Ω]

local instance (point : S →ₐ[R] Ω) : (RingHom.ker point).IsPrime :=
  RingHom.ker_isPrime point

/-- The residue-field embedding induced by a field-valued point. -/
noncomputable def residueEmbedding (point : S →ₐ[R] Ω) :
    (RingHom.ker point).ResidueField →ₐ[R] Ω :=
  Ideal.ResidueField.liftₐ _ point le_rfl fun element hnonzero ↦ by
    exact isUnit_iff_ne_zero.mpr hnonzero

/-- The residue-field embedding recovers the original point. -/
@[simp]
theorem residueEmbedding_comp (point : S →ₐ[R] Ω) :
    (point.residueEmbedding).comp
      (IsScalarTower.toAlgHom R S (RingHom.ker point).ResidueField) = point :=
  Ideal.ResidueField.liftₐ_comp_toAlgHom _ _ _ _

/-- A field-valued point factors uniquely through the residue field of its kernel. -/
theorem existsUnique_residueEmbedding (point : S →ₐ[R] Ω) :
    ∃! embedding : (RingHom.ker point).ResidueField →ₐ[R] Ω,
      embedding.comp (IsScalarTower.toAlgHom R S (RingHom.ker point).ResidueField) = point := by
  refine ⟨point.residueEmbedding, point.residueEmbedding_comp, ?_⟩
  intro embedding equality
  exact Ideal.ResidueField.algHom_ext
    (equality.trans point.residueEmbedding_comp.symm)

/-- The kernel of an `R`-algebra map to the residue field `κ(P)` of a prime `P` of `R` lies over
`P`. -/
theorem comap_ker_eq_of_residueField {P : Ideal R} [P.IsPrime] (point : S →ₐ[R] P.ResidueField) :
    (RingHom.ker point).comap (algebraMap R S) = P := by
  ext r
  rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes, Ideal.algebraMap_residueField_eq_zero]

/-- An `R`-algebra map from `S` to the residue field `κ(P)` of a prime `P` of `R` identifies
`κ(P)` with the residue field of `S` at its kernel. -/
theorem residueFieldMap_bijective {P : Ideal R} [P.IsPrime] (point : S →ₐ[R] P.ResidueField) :
    Function.Bijective (Ideal.ResidueField.map P (RingHom.ker point) (algebraMap R S)
      point.comap_ker_eq_of_residueField.symm) := by
  let β := point.residueEmbedding
  have hβ : β.toRingHom.comp (Ideal.ResidueField.map P (RingHom.ker point) (algebraMap R S)
      point.comap_ker_eq_of_residueField.symm) = RingHom.id _ :=
    Ideal.ResidueField.ringHom_ext <| RingHom.ext fun r ↦ by
      have h := DFunLike.congr_fun point.residueEmbedding_comp (algebraMap R S r)
      rw [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply] at h
      simp [Ideal.ResidueField.map_algebraMap, β, h]
  refine ⟨RingHom.injective _, fun y ↦ ⟨β y, β.toRingHom.injective ?_⟩⟩
  exact congr($hβ (β y))

end AlgHom

namespace Ideal

/-- If a prime `p` of `R` is the kernel of a map `R → F` to a field, then `F` is an algebra over
the residue field `κ(p)`, compatibly with the algebra structures over `R`. For
`p = RingHom.ker (algebraMap R F)` the map `κ(p) → F` is `AlgHom.residueEmbedding`. -/
theorem exists_algebra_residueField_isScalarTower {R F : Type*} [CommRing R] [Field F]
    [Algebra R F] (p : Ideal R) [p.IsPrime] (hp : RingHom.ker (algebraMap R F) = p) :
    ∃ _ : Algebra p.ResidueField F, IsScalarTower R p.ResidueField F := by
  let : Algebra p.ResidueField F := (Ideal.ResidueField.lift p (algebraMap R F) hp.ge
    fun r hr ↦ isUnit_iff_ne_zero.mpr fun h ↦ hr (hp ▸ h)).toAlgebra
  exact ⟨_, .of_algebraMap_eq fun r ↦ (Ideal.ResidueField.lift_algebraMap _ _ _ _ r).symm⟩

variable {R S Ω : Type*} [CommRing R] [CommRing S] [CommRing Ω]
  [Algebra R S] [Algebra R Ω]

/-- A residue-field embedding recovers the prime through its kernel. -/
@[simp]
theorem ker_residueEmbedding_comp (prime : Ideal S) [prime.IsPrime]
    [Nontrivial Ω] (embedding : prime.ResidueField →ₐ[R] Ω) :
    RingHom.ker (embedding.comp (IsScalarTower.toAlgHom R S prime.ResidueField)) = prime := by
  ext element
  simp only [RingHom.mem_ker, AlgHom.comp_apply,
    map_eq_zero_iff embedding embedding.injective, IsScalarTower.toAlgHom_apply]
  exact Ideal.algebraMap_residueField_eq_zero

/-- Compatibility of residue embeddings is exactly compatibility of the associated points. -/
theorem residueEmbedding_comp_map_iff {T : Type*} [CommRing T] [Algebra R T]
    (sourcePrime : Ideal S) [sourcePrime.IsPrime] (targetPrime : Ideal T) [targetPrime.IsPrime]
    (sourceEmbedding : sourcePrime.ResidueField →ₐ[R] Ω)
    (targetEmbedding : targetPrime.ResidueField →ₐ[R] Ω) (morphism : S →ₐ[R] T)
    (hprime : sourcePrime = targetPrime.comap morphism.toRingHom) :
    targetEmbedding.comp (Ideal.ResidueField.mapₐ sourcePrime targetPrime morphism hprime) =
      sourceEmbedding ↔
    (targetEmbedding.comp (IsScalarTower.toAlgHom R T targetPrime.ResidueField)).comp morphism =
      sourceEmbedding.comp (IsScalarTower.toAlgHom R S sourcePrime.ResidueField) := by
  constructor
  · intro equality
    ext element
    have result := DFunLike.congr_fun equality (algebraMap S sourcePrime.ResidueField element)
    simpa only [AlgHom.comp_apply, Ideal.ResidueField.mapₐ_apply,
      Ideal.ResidueField.map_algebraMap, IsScalarTower.toAlgHom_apply,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using result
  · intro equality
    apply Ideal.ResidueField.algHom_ext
    ext element
    have result := DFunLike.congr_fun equality element
    simpa only [AlgHom.comp_apply, Ideal.ResidueField.mapₐ_apply,
      Ideal.ResidueField.map_algebraMap, IsScalarTower.toAlgHom_apply,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using result

end Ideal

namespace TauCeti.ResidueField

section CommRing

variable {R S Ω : Type*} [CommRing R] [CommRing S] [CommRing Ω] [Algebra R S] [Algebra R Ω]

/-- A prime and an algebra map from its residue field to the chosen algebra. -/
abbrev PointData (R S Ω : Type*) [CommRing R] [CommRing S] [CommRing Ω]
    [Algebra R S] [Algebra R Ω] :=
  Σ prime : PrimeSpectrum S, prime.asIdeal.ResidueField →ₐ[R] Ω

/-- The algebra-valued point associated with residue-field data. -/
noncomputable def PointData.toAlgHom (data : PointData R S Ω) : S →ₐ[R] Ω :=
  data.2.comp (IsScalarTower.toAlgHom R S data.1.asIdeal.ResidueField)

/-- Evaluate the point induced by residue-field data. -/
@[simp]
theorem PointData.toAlgHom_apply (data : PointData R S Ω) (element : S) :
    data.toAlgHom element = data.2 (algebraMap S data.1.asIdeal.ResidueField element) := by
  simp only [PointData.toAlgHom, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply]

end CommRing

section Nontrivial

variable {R S Ω : Type*} [CommRing R] [CommRing S] [CommRing Ω] [Nontrivial Ω]
  [Algebra R S] [Algebra R Ω]

/-- Residue-field data are determined by their algebra-valued point. -/
theorem PointData.toAlgHom_injective :
    Function.Injective (PointData.toAlgHom : PointData R S Ω → S →ₐ[R] Ω) := by
  rintro ⟨firstPrime, firstEmbedding⟩ ⟨secondPrime, secondEmbedding⟩ equality
  have hprime : firstPrime = secondPrime := by
    apply PrimeSpectrum.ext
    exact (Ideal.ker_residueEmbedding_comp _ firstEmbedding).symm.trans
      ((congrArg RingHom.ker equality).trans
        (Ideal.ker_residueEmbedding_comp _ secondEmbedding))
  subst secondPrime
  congr 1
  exact Ideal.ResidueField.algHom_ext equality

end Nontrivial

section Field

variable {R S Ω : Type*} [CommRing R] [CommRing S] [Field Ω] [Algebra R S] [Algebra R Ω]

local instance (point : S →ₐ[R] Ω) : (RingHom.ker point).IsPrime :=
  RingHom.ker_isPrime point

/-- Residue-field data determine the point bijectively. -/
theorem PointData.toAlgHom_bijective :
    Function.Bijective (PointData.toAlgHom : PointData R S Ω → S →ₐ[R] Ω) := by
  constructor
  · exact PointData.toAlgHom_injective
  · intro point
    exact ⟨⟨⟨RingHom.ker point, inferInstance⟩, point.residueEmbedding⟩,
      point.residueEmbedding_comp⟩

/-- Field-valued points are equivalent to a prime and a residue-field embedding. -/
noncomputable def pointDataEquiv : PointData R S Ω ≃ (S →ₐ[R] Ω) :=
  Equiv.ofBijective PointData.toAlgHom PointData.toAlgHom_bijective

/-- The forward correspondence is the point induced by the residue-field embedding. -/
@[simp]
theorem pointDataEquiv_apply (data : PointData R S Ω) :
    pointDataEquiv data = data.toAlgHom := by
  exact Equiv.ofBijective_apply _ _ _

/-- The inverse correspondence assigns a point its kernel and residue-field embedding. -/
@[simp]
theorem pointDataEquiv_symm_apply (point : S →ₐ[R] Ω) :
    pointDataEquiv.symm point =
      ⟨⟨RingHom.ker point, inferInstance⟩, point.residueEmbedding⟩ := by
  apply pointDataEquiv.injective
  simp only [Equiv.apply_symm_apply, pointDataEquiv_apply, PointData.toAlgHom,
    AlgHom.residueEmbedding_comp]

end Field

variable {R S Ω : Type*} [CommRing R] [CommRing S] [CommRing Ω] [Nontrivial Ω]
  [Algebra R S] [Algebra R Ω]

/-- Compatibility of induced points is compatibility of the prime and residue-field maps. -/
theorem PointData.toAlgHom_comp_iff {T : Type*} [CommRing T] [Algebra R T]
    (source : PointData R S Ω) (target : PointData R T Ω) (morphism : S →ₐ[R] T) :
    target.toAlgHom.comp morphism = source.toAlgHom ↔
      ∃ hprime : source.1.asIdeal = target.1.asIdeal.comap morphism.toRingHom,
        target.2.comp (Ideal.ResidueField.mapₐ source.1.asIdeal target.1.asIdeal morphism hprime) =
          source.2 := by
  constructor
  · intro equality
    have hkernel := congrArg RingHom.ker equality
    rw [← AlgHom.comap_ker] at hkernel
    have hprime : source.1.asIdeal = target.1.asIdeal.comap morphism.toRingHom := by
      have hprime' : source.1.asIdeal = target.1.asIdeal.comap morphism := by
        simpa only [PointData.toAlgHom, Ideal.ker_residueEmbedding_comp] using hkernel.symm
      exact hprime'
    exact ⟨hprime, (Ideal.residueEmbedding_comp_map_iff _ _ _ _ _ hprime).mpr equality⟩
  · rintro ⟨hprime, equality⟩
    exact (Ideal.residueEmbedding_comp_map_iff _ _ _ _ _ hprime).mp equality

end TauCeti.ResidueField
end
end TAF_LiteralSource_0611

section TAF_LiteralSource_0612
/- Original module: TauCeti.RingTheory.Finiteness.Nakayama -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

-- Proof-only: the prime ideals of `ℤ`, and `ℤ` is not a field.
-- Proof-only: supports, residue fields and faithful flatness, for Nakayama's lemma at a point.

/-!
# Nakayama's lemma with weighted generators, over `ℤ`, and at a point

Let `M` be a module over a commutative ring `R`, spanned by a finite family `b`, and let `I` be an
ideal. Mathlib's `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul` says that if
`M = I • M`, some `r ≡ 1 (mod I)` kills `M`. This file proves the weighted form: if `e i • b i`
lies in `I • M` for each `i`, then some `r ≡ ∏ᵢ e i (mod I)` kills `M`
(`Submodule.exists_sub_prod_mem_and_smul_eq_zero`). The case `e = 1` recovers Nakayama's lemma for
a finite spanning family.

The proof is the determinant trick: writing `e i • b i = ∑ⱼ θ i j • b j` with `θ i j ∈ I`, the
determinant of `diag e - θ` kills every `b k`, and it is `∏ᵢ e i` modulo `I`.

This is the commutative-algebra step of the proof, due to Artin and Tate, that the transfer of a
finite group into its commutator subgroup is trivial: there `R` is the integral group ring of a
finite abelian group, `I` its augmentation ideal and `e i` the orders of a basis of the group.

The file also records the global form of Nakayama's lemma: a finitely generated submodule `N` with
`N = m • N` for every maximal ideal `m` is zero (`Submodule.eq_bot_of_forall_isMaximal_le_smul`).
Over `ℤ` this passes from statements modulo every prime to integral statements: a finitely
generated subgroup `N` of an abelian group with `N = p • N` for every prime `p` is zero
(`Submodule.eq_bot_of_forall_prime_le_smul`).

For a finite module `M`, Nakayama's lemma also characterises `I M = M` as the comaximality of `I`
with the annihilator of `M` (`Ideal.smul_top_eq_top_iff_sup_annihilator_eq_top`).

Finally, Nakayama's lemma at a field-valued point `R → F`: if the fibre `F ⊗[R] M` of a finite
module has dimension `d`, then `M` is generated by `d` elements after inverting an element of `R`
that does not vanish at that point (`Module.exists_finset_card_le_finrank_and_smul_mem_span`).
The point need not be a residue field of `R`: it factors through the residue field of its kernel,
over which `F` is faithfully flat.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIII.
* D. Ferrand, *La démonstration par Artin–Tate du théorème de l'idéal principal* (2011), §2.
-/

public section

namespace Submodule

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]

/-- **Nakayama's lemma with weighted generators.** If `b` spans `M` and `e i • b i ∈ I • M` for
every `i`, then some `r ≡ ∏ᵢ e i (mod I)` kills `M`. -/
theorem exists_sub_prod_mem_and_smul_eq_zero (I : Ideal R) {b : ι → M}
    (hb : span R (Set.range b) = ⊤) (e : ι → R)
    (he : ∀ i, e i • b i ∈ I • (⊤ : Submodule R M)) :
    ∃ r : R, r - ∏ i, e i ∈ I ∧ ∀ m : M, r • m = 0 := by
  classical
  rw [← hb] at he
  choose θ hθI hθ using fun i ↦ (mem_ideal_smul_span_iff_exists_sum I b _).1 (he i)
  let A : Matrix ι ι R := Matrix.diagonal e - Matrix.of fun i j ↦ θ i j
  have hA : ∀ i, ∑ j, A i j • b j = 0 := fun i ↦ by
    simp only [A, Matrix.sub_apply, Matrix.diagonal_apply, Matrix.of_apply, sub_smul, ite_smul,
      zero_smul, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [sub_eq_zero, ← hθ i]
    exact Finsupp.sum_fintype _ _ fun _ ↦ zero_smul R _
  refine ⟨A.det, ?_, fun m ↦ ?_⟩
  · -- Modulo `I`, the matrix `A` is the diagonal matrix of the weights.
    have hmap : (Ideal.Quotient.mk I).mapMatrix A = Matrix.diagonal (Ideal.Quotient.mk I ∘ e) := by
      ext i j
      by_cases h : i = j
      · subst h
        simp [A, (Ideal.Quotient.eq_zero_iff_mem).2 (hθI i i)]
      · simp [A, h, (Ideal.Quotient.eq_zero_iff_mem).2 (hθI i j)]
    rw [← Ideal.Quotient.eq, RingHom.map_det, hmap, Matrix.det_diagonal, map_prod]
    rfl
  · have hm : m ∈ span R (Set.range b) := hb ▸ mem_top
    induction hm using span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact A.det_smul_eq_zero_of_sum_smul_eq_zero hA k
    | zero => exact smul_zero _
    | add x y _ _ hx hy => rw [smul_add, hx, hy, add_zero]
    | smul r x _ hx => rw [smul_comm, hx, smul_zero]

/-- **Nakayama's lemma, globally.** A finitely generated submodule `N` with `N ≤ m • N` for every
maximal ideal `m` is zero. -/
theorem eq_bot_of_forall_isMaximal_le_smul {N : Submodule R M} (hN : N.FG)
    (h : ∀ m : Ideal R, m.IsMaximal → N ≤ m • N) : N = ⊥ := by
  rw [← annihilator_eq_top_iff]
  by_contra hne
  -- Some `r ≡ 1 (mod m)` kills `N`, for a maximal ideal `m` containing the annihilator.
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨r, hr1, hr⟩ := exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m N hN (h m hm)
  refine hm.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  simpa using m.sub_mem (hle (mem_annihilator.2 hr)) hr1

/-- **Nakayama's lemma over `ℤ`.** A finitely generated subgroup `N` of an abelian group with
`N ≤ p • N` for every prime `p` is zero. -/
theorem eq_bot_of_forall_prime_le_smul {M : Type*} [AddCommGroup M] {N : Submodule ℤ M}
    (hN : N.FG) (h : ∀ p : ℕ, p.Prime → N ≤ Ideal.span {(p : ℤ)} • N) : N = ⊥ := by
  refine eq_bot_of_forall_isMaximal_le_smul hN fun m hm => ?_
  -- The maximal ideals of `ℤ` are the ideals `(p)` for primes `p`.
  obtain rfl | ⟨p, hp, rfl⟩ := Ideal.isPrime_int_iff.1 hm.isPrime
  · exact absurd rfl (Ring.ne_bot_of_isMaximal_of_not_isField hm Int.not_isField)
  · exact h p hp

end Submodule

namespace Ideal

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- For a finite module `M`, `I M = M` exactly when `I` and the annihilator of `M` are comaximal. -/
theorem smul_top_eq_top_iff_sup_annihilator_eq_top [Module.Finite R M] (I : Ideal R) :
    I • (⊤ : Submodule R M) = ⊤ ↔ I ⊔ Module.annihilator R M = ⊤ := by
  refine ⟨fun hI ↦ ?_, fun h ↦ ?_⟩
  · -- Nakayama gives `r ∈ I` acting as the identity, so `1 - r` annihilates `M`.
    obtain ⟨r, hrI, hr⟩ := Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul I ⊤
      Module.Finite.fg_top hI.ge
    refine (eq_top_iff_one _).2 <| Submodule.mem_sup.2 ⟨r, hrI, 1 - r, ?_, add_sub_cancel r 1⟩
    exact Module.mem_annihilator.2 fun m ↦ by rw [sub_smul, one_smul, hr m trivial, sub_self]
  · calc I • (⊤ : Submodule R M) = (I ⊔ Module.annihilator R M) • ⊤ := by
          rw [Submodule.sup_smul, ← Submodule.annihilator_top, Submodule.annihilator_smul,
            sup_bot_eq]
      _ = ⊤ := by rw [h, Submodule.top_smul]

end Ideal

namespace Module

open TensorProduct

variable {R M F : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Field F]
  [Algebra R F]

/-- A finite module whose fibre `F ⊗[R] M` at a field-valued point `R → F` vanishes is killed by
an element of `R` that does not vanish at that point. -/
theorem exists_algebraMap_ne_zero_and_smul_eq_zero (h : Subsingleton (F ⊗[R] M)) :
    ∃ r : R, algebraMap R F r ≠ 0 ∧ ∀ x : M, r • x = 0 := by
  -- The point `R → F` factors through the residue field `κ(p)` of its kernel `p`.
  let p := RingHom.ker (algebraMap R F)
  have : p.IsPrime := RingHom.ker_isPrime _
  obtain ⟨_, _⟩ := Ideal.exists_algebra_residueField_isScalarTower (F := F) p rfl
  -- Since `F ⊗[R] M = F ⊗[κ(p)] (κ(p) ⊗[R] M)` and `F` is faithfully flat over `κ(p)`, the fibre
  -- `κ(p) ⊗[R] M` vanishes, so `p` is not in the support of `M`.
  have hp : ⟨p, inferInstance⟩ ∉ Module.support R M := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
      ← Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right p.ResidueField F,
      (AlgebraTensorModule.cancelBaseChange R p.ResidueField F F M).nontrivial_congr,
      not_nontrivial_iff_subsingleton]
    exact h
  rw [Module.mem_support_iff_of_finite, IsConcreteLE.not_le_iff_exists] at hp
  obtain ⟨r, hr, hrp⟩ := hp
  exact ⟨r, hrp, fun x ↦ Module.mem_annihilator.mp hr x⟩

/-- **Nakayama's lemma at a field-valued point.** If the fibre `F ⊗[R] M` of a finite module at a
field-valued point `R → F` has dimension `d`, then `M` is generated by `d` elements after inverting
some element of `R` that does not vanish at that point. -/
theorem exists_finset_card_le_finrank_and_smul_mem_span :
    ∃ s : Finset M, s.card ≤ Module.finrank F (F ⊗[R] M) ∧ ∃ r : R, algebraMap R F r ≠ 0 ∧
      ∀ x : M, r • x ∈ Submodule.span R (s : Set M) := by
  classical
  -- Choose elements of `M` whose images form a basis of the fibre.
  let v : M → F ⊗[R] M := fun x ↦ 1 ⊗ₜ x
  have hv : Submodule.span F (Set.range v) = ⊤ := by
    have := Submodule.baseChange_top (R := R) (A := F) (M := M)
    rw [Submodule.baseChange_eq_span, Submodule.map_top] at this
    convert this using 2
    ext
    simp [v]
  obtain ⟨κ, a, -, hspan, hli⟩ := exists_linearIndependent' F v
  have : Finite κ := hli.finite
  have := Fintype.ofFinite κ
  let s : Finset M := Finset.univ.image a
  refine ⟨s, Finset.card_image_le.trans hli.fintype_card_le_finrank, ?_⟩
  -- The fibre of `M ⧸ span s` vanishes.
  let N := Submodule.span R (s : Set M)
  have hN : Subsingleton (F ⊗[R] (M ⧸ N)) := by
    have hker : (⊤ : Submodule F (F ⊗[R] M)) ≤ LinearMap.ker (N.mkQ.baseChange F) := by
      rw [← hv, ← hspan, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have : a i ∈ N := Submodule.subset_span (by simp [s])
      simp [v, (Submodule.Quotient.mk_eq_zero N).mpr this]
    refine subsingleton_of_forall_eq 0 fun y ↦ ?_
    obtain ⟨x, rfl⟩ := LinearMap.baseChange_surjective F N.mkQ_surjective y
    exact hker trivial
  obtain ⟨r, hr, hrN⟩ := exists_algebraMap_ne_zero_and_smul_eq_zero (M := M ⧸ N) hN
  exact ⟨r, hr, fun x ↦ (Submodule.Quotient.mk_eq_zero N).mp
    (by rw [Submodule.Quotient.mk_smul]; exact hrN _)⟩

end Module
end
end TAF_LiteralSource_0612

section TAF_LiteralSource_0613
/- Original module: TauCeti.RingTheory.Regular.RegularSequence -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Constructing regular sequences

This file produces regular sequences on a module `M` from local information.

If `a, b` is a weakly `M`-regular sequence, then `bʲ` is regular on `M ⧸ aⁿ M` for all `n` and `j`.

If `f₁, …, f_r` is weakly `M`-regular, every relation `∑ fᵢ mᵢ = 0` with `mᵢ ∈ M` has all its
coefficients in `(f₁, …, f_r) M`. Dividing the last element out first,
`f_r m_r ∈ (f₁, …, f_{r-1}) M` forces `m_r = ∑_{i<r} fᵢ nᵢ`, and the relation
`∑_{i<r} fᵢ (mᵢ + f_r nᵢ) = 0` among the first `r - 1` elements finishes the induction.

Let `M` be a finite module over a Noetherian ring `R` and `I` an ideal of `R`. By prime avoidance,
`I` contains an `M`-regular element exactly when `I` lies in no associated prime of `M`. Iterating,
if `depth M_p ≥ n` at every prime `p ⊇ I`, then `I` contains a weakly `M`-regular sequence of
length `n`: an associated prime containing `I` would give a localization of depth zero, and
dividing by a regular element of `I` lowers each of these local depths by exactly one.

The second statement passes from depth at the points of the closed subset `V(I)` of `Spec R` to a
regular sequence on `M` itself. This is how a depth condition at the points of `V(I)` is used to
extend sections of `M~` across `V(I)` (Stacks, Lemma 31.5.11 (0E9I)).

## Main results

* `Ideal.ofList_ofFn`, `Ideal.ofList_eq_span_range_getElem`: the ideal generated by a list as the
  span of a range.
* `RingTheory.Sequence.IsWeaklyRegular.of_subsingleton`: every finite sequence is weakly regular
  on a module with at most one element.
* `TauCeti.isSMulRegular_quotSMulTop_iff`: `b` is regular on `M ⧸ a M` exactly when `a c = b m`
  forces `m ∈ a M`.
* `RingTheory.Sequence.IsWeaklyRegular.isSMulRegular_quotSMulTop_pow`: for a weakly `M`-regular
  sequence `a, b`, the power `bʲ` is regular on `M ⧸ aⁿ M`.
* `RingTheory.Sequence.IsWeaklyRegular.mem_ofList_smul_top_of_sum_eq_zero`: the coefficients of a
  relation `∑ fᵢ mᵢ = 0` among a weakly `M`-regular sequence lie in `(f₁, …, f_r) M`.
* `Ideal.exists_mem_isSMulRegular_iff`: `I` contains an `M`-regular element if and only if it lies
  in no associated prime of `M`.
* `IsLocalRing.exists_isSMulRegular_of_depth_ne_zero`: over a Noetherian local ring, a finite
  module of nonzero depth has a regular element in the maximal ideal.
* `TauCeti.exists_isWeaklyRegular_of_le_depth_localizedModule`: if `depth M_p ≥ n` at every prime
  `p ⊇ I`, then `I` contains a weakly `M`-regular sequence of length `n`.

## References

* [Stacks Project, Lemma 31.5.11](https://stacks.math.columbia.edu/tag/0E9I).
* [The Stacks Project, Tag 062F](https://stacks.math.columbia.edu/tag/062F)
-/

public section

universe u v

open IsLocalRing RingTheory.Sequence Module Pointwise

section OfList

variable {R : Type*} [Semiring R]

/-- The ideal generated by the entries of `List.ofFn f` is the span of the range of `f`. -/
@[simp]
theorem Ideal.ofList_ofFn {n : ℕ} (f : Fin n → R) :
    Ideal.ofList (List.ofFn f) = Ideal.span (Set.range f) :=
  congrArg Ideal.span (Set.ext fun _ ↦ List.mem_ofFn' f _)

/-- The ideal generated by a list is the span of its entries, indexed by position. -/
theorem Ideal.ofList_eq_span_range_getElem (rs : List R) :
    Ideal.ofList rs = Ideal.span (Set.range fun i : Fin rs.length ↦ rs[i]) := by
  simpa using Ideal.ofList_ofFn fun i : Fin rs.length ↦ rs[(i : ℕ)]

end OfList

section Pow

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- Every finite sequence is weakly regular on a module with at most one element. -/
theorem RingTheory.Sequence.IsWeaklyRegular.of_subsingleton [Subsingleton M] (rs : List R) :
    IsWeaklyRegular M rs :=
  ⟨fun _ _ _ _ _ ↦ Subsingleton.elim _ _⟩

/-- An element `b` is regular on `M ⧸ a M` exactly when `a c = b m` forces `m ∈ a M`. -/
theorem TauCeti.isSMulRegular_quotSMulTop_iff {a b : R} :
    IsSMulRegular (QuotSMulTop a M) b ↔
      ∀ m c : M, a • c = b • m → m ∈ a • (⊤ : Submodule R M) :=
  (isSMulRegular_quotient_iff_mem_of_smul_mem _ b).trans <| forall_congr' fun m ↦ by
    simp [Submodule.mem_smul_pointwise_iff_exists (b • m)]

/-- If `a, b` is a weakly `M`-regular sequence, then `bʲ` is regular on `M ⧸ aⁿ M`. -/
theorem RingTheory.Sequence.IsWeaklyRegular.isSMulRegular_quotSMulTop_pow {a b : R}
    (h : IsWeaklyRegular M [a, b]) (n j : ℕ) : IsSMulRegular (QuotSMulTop (a ^ n) M) (b ^ j) := by
  obtain ⟨ha, hb⟩ := (isWeaklyRegular_cons_iff M a [b]).1 h
  rw [isWeaklyRegular_singleton_iff] at hb
  refine isSMulRegular_iff_right_eq_zero_of_smul.2 fun q hq ↦ ?_
  induction q using Submodule.Quotient.induction_on with | H x => ?_
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hq
  rw [Submodule.Quotient.mk_eq_zero]
  -- Show by induction on `n` that `bʲ x ∈ aⁿ M` implies `x ∈ aⁿ M`.
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hq
    -- First `x ∈ a M`, since `b` is regular on `M ⧸ a M`.
    have hxa : x ∈ a • (⊤ : Submodule R M) := by
      refine (Submodule.Quotient.mk_eq_zero _).1 ((hb.pow j).right_eq_zero_of_smul ?_)
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← hy, pow_succ',
        mul_smul]
      exact Submodule.smul_mem_pointwise_smul _ a ⊤ trivial
    obtain ⟨x', -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hxa
    -- Then cancel `a`, which is `M`-regular, and apply the induction hypothesis.
    have hx' : b ^ j • x' = a ^ n • y := ha <| by
      simp only [smul_comm a (b ^ j), ← mul_smul, ← pow_succ', hy]
    obtain ⟨c, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1
      (ih x' (hx' ▸ Submodule.smul_mem_pointwise_smul _ _ ⊤ trivial))
    rw [smul_smul, ← pow_succ']
    exact Submodule.smul_mem_pointwise_smul _ _ ⊤ trivial

end Pow

section Relations

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

namespace RingTheory.Sequence.IsWeaklyRegular

/-- The relation statement for a sequence indexed by `Fin n`, by induction on `n`. -/
private theorem mem_smul_top_of_sum_eq_zero_aux :
    ∀ {n : ℕ} {rs : Fin n → R}, IsWeaklyRegular M (List.ofFn rs) → ∀ {m : Fin n → M},
      ∑ i, rs i • m i = 0 → ∀ i, m i ∈ Ideal.span (Set.range rs) • (⊤ : Submodule R M) := by
  intro n
  induction n with
  | zero => exact fun _ _ _ i ↦ i.elim0
  | succ n ih =>
    intro rs h m hm
    rw [List.ofFn_succ', List.concat_eq_append, isWeaklyRegular_append_iff,
      isWeaklyRegular_singleton_iff, Ideal.ofList_ofFn] at h
    obtain ⟨h₁, h₂⟩ := h
    set I' := Ideal.span (Set.range fun i : Fin n ↦ rs i.castSucc)
    rw [Fin.sum_univ_castSucc] at hm
    -- The last element is regular modulo `I' M`, so its coefficient lies in `I' M`.
    have hlast : m (Fin.last n) ∈ I' • (⊤ : Submodule R M) := by
      have : rs (Fin.last n) • m (Fin.last n) ∈ I' • (⊤ : Submodule R M) := by
        rw [eq_neg_of_add_eq_zero_right hm]
        exact neg_mem (sum_mem fun i _ ↦ Submodule.smul_mem_smul (Ideal.subset_span ⟨i, rfl⟩)
          Submodule.mem_top)
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul] at this
      rw [← Submodule.Quotient.mk_eq_zero]
      exact h₂.right_eq_zero_of_smul this
    -- Writing it as `∑ rsᵢ cᵢ` gives a relation among the first `n` elements.
    obtain ⟨c, hc⟩ := Submodule.mem_span_range_smul_top_iff_exists_fun.mp hlast
    have hrel := ih h₁ (m := fun i ↦ m i.castSucc + rs (Fin.last n) • c i) (by
      simpa [smul_add, Finset.sum_add_distrib, smul_comm (rs _) (rs (Fin.last n)),
        ← Finset.smul_sum, hc] using hm)
    have hle : I' ≤ Ideal.span (Set.range rs) :=
      Ideal.span_mono (Set.range_comp_subset_range Fin.castSucc rs)
    refine Fin.lastCases (Submodule.smul_mono_left hle hlast) fun i ↦ ?_
    simpa using sub_mem (Submodule.smul_mono_left hle (hrel i)) (Submodule.smul_mem_smul
      (Ideal.subset_span ⟨Fin.last n, rfl⟩) (Submodule.mem_top (x := c i)))

/-- **Relations among a weakly regular sequence have coefficients in the ideal it generates.** If
`rs` is weakly regular on `M` and `∑ rsᵢ • mᵢ = 0`, then every `mᵢ` lies in `(rs) M`. -/
theorem mem_ofList_smul_top_of_sum_eq_zero {rs : List R} (h : IsWeaklyRegular M rs)
    {m : Fin rs.length → M} (hm : ∑ i, rs[i] • m i = 0) (i : Fin rs.length) :
    m i ∈ Ideal.ofList rs • (⊤ : Submodule R M) := by
  rw [← List.ofFn_getElem (xs := rs)] at h
  exact Ideal.ofList_eq_span_range_getElem rs ▸ mem_smul_top_of_sum_eq_zero_aux h hm i

end RingTheory.Sequence.IsWeaklyRegular

end Relations

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {M : Type v} [AddCommGroup M] [Module R M]
  [Module.Finite R M]

/-- **Prime avoidance for regular elements.** An ideal `I` of a Noetherian ring contains an
element that is regular on a finite module `M` if and only if `I` is contained in no associated
prime of `M`. -/
theorem Ideal.exists_mem_isSMulRegular_iff (I : Ideal R) :
    (∃ a ∈ I, IsSMulRegular M a) ↔ ∀ p ∈ associatedPrimes R M, ¬ I ≤ p := by
  have hzd := biUnion_associatedPrimes_eq_compl_regular R M
  refine ⟨fun ⟨a, ha, reg⟩ p hp hle ↦ ?_, fun h ↦ ?_⟩
  · have hmem : a ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) := Set.mem_biUnion hp (hle ha)
    rw [hzd] at hmem
    exact hmem reg
  · by_contra! hreg
    obtain ⟨p, hp, hle⟩ := (Ideal.subset_union_prime_finite (associatedPrimes.finite R M)
      (f := id) 0 0 fun _ hp _ _ ↦ hp.isPrime).1 <| by
        simp_rw [id, hzd]
        exact hreg
    exact h p hp hle

/-- Over a Noetherian local ring, a finite module of nonzero depth has a regular element in the
maximal ideal. -/
theorem IsLocalRing.exists_isSMulRegular_of_depth_ne_zero [IsLocalRing R] [Small.{v} R]
    (h : depth (ModuleCat.of R M) ≠ 0) : ∃ a ∈ maximalIdeal R, IsSMulRegular M a := by
  refine (maximalIdeal R).exists_mem_isSMulRegular_iff.2 fun p hp hle ↦ h ?_
  rw [depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes,
    (maximalIdeal.isMaximal R).eq_of_le hp.isPrime.ne_top hle]
  exact hp

namespace TauCeti

/-- Let `M` be a finite module over a Noetherian ring and `I` an ideal. If `depth M_p ≥ n` for
every prime `p` containing `I`, then `I` contains a weakly `M`-regular sequence of length `n`. -/
theorem exists_isWeaklyRegular_of_le_depth_localizedModule (I : Ideal R) (n : ℕ)
    (h : ∀ (p : Ideal R) [p.IsPrime], I ≤ p →
      (n : ℕ∞) ≤ depth (ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl M))) :
    ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ IsWeaklyRegular M rs := by
  induction n generalizing M with
  | zero => exact ⟨[], rfl, by simp, IsWeaklyRegular.nil R M⟩
  | succ n ih =>
    -- An associated prime containing `I` would give a localization of depth zero.
    obtain ⟨a, haI, reg⟩ := (I.exists_mem_isSMulRegular_iff (M := M)).2 fun p hp hle ↦ by
      have := hp.isPrime
      have hdepth := h p hle
      rw [depth_localizedModule_eq_zero_iff.2 hp] at hdepth
      exact (Nat.cast_add_one_ne_zero n) (nonpos_iff_eq_zero.1 hdepth)
    -- Dividing by `a` lowers the depth of each localization at a prime `p ⊇ I` by exactly one.
    obtain ⟨rs, hlen, hmem, hrs⟩ := @ih (QuotSMulTop a M) _ _ _ fun p _ hle ↦ by
      have hdepth := h p hle
      rw [← depth_localizedModule_quotSMulTop_add_one reg p (hle haI), Nat.cast_add_one] at hdepth
      exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 hdepth
    exact ⟨a :: rs, by simp [hlen], List.forall_mem_cons.2 ⟨haI, hmem⟩,
      (isWeaklyRegular_cons_iff M a rs).2 ⟨reg, hrs⟩⟩

end TauCeti
end
end TAF_LiteralSource_0613

section TAF_LiteralSource_0614
/- Original module: TauCeti.RingTheory.Depth.WeaklyRegular -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Depth as the supremum of lengths of weakly regular sequences

Mathlib defines the depth `I.depth M` of a module `M` with respect to an ideal `I` through the
vanishing of `Ext (R ⧸ I) M`, and identifies it, for a finite module over a Noetherian ring with
`I M ≠ M`, with the supremum of the lengths of `M`-regular sequences in `I`. Stacks defines the
`I`-depth of a module through regular sequences, and the convenient form with no hypothesis on
`I M` uses *weakly* regular sequences, which do not ask that `M ⧸ (f₁, …, fᵣ) M` be nonzero.

This file proves that, for every finite module `M` over a Noetherian ring and every ideal `I`,
`I.depth M` is the supremum in `ℕ∞` of the lengths of weakly `M`-regular sequences in `I`, and
that the depth is infinite exactly when `I M = M`. Over a Noetherian local ring this says that
`IsLocalRing.depth M` is the supremum of the lengths of weakly `M`-regular sequences in the
maximal ideal, and that it is infinite exactly when `M = 0`.

## Main results

* `Ideal.depth_le_height`: `I.depth M` is at most the height of every prime of the support of `M`
  containing `I`.
* `Ideal.depth_lt_top`: if `I M ≠ M` then `I.depth M` is finite.
* `Ideal.depth_eq_top_iff`: `I.depth M = ⊤` if and only if `I M = M`.
* `Ideal.depth_eq_sSup_length_isWeaklyRegular`: `I.depth M` is the supremum of the lengths of
  weakly `M`-regular sequences in `I`.
* `IsLocalRing.depth_eq_top_iff`: over a Noetherian local ring, `depth M = ⊤` if and only if
  `M = 0`.
* `IsLocalRing.depth_eq_sSup_length_isWeaklyRegular`: over a Noetherian local ring, `depth M` is
  the supremum of the lengths of weakly `M`-regular sequences in the maximal ideal.

## References

* [Stacks Project, Definition 10.72.1](https://stacks.math.columbia.edu/tag/00LI)
-/

public section

universe v u

open IsLocalRing RingTheory.Sequence CategoryTheory Abelian

variable {R : Type u} [CommRing R]

namespace Ideal

variable [Small.{v} R]

/-- If `I M = M` for a finite module `M`, then `Ext (R ⧸ I) M` vanishes in every degree, so the
depth of `M` with respect to `I` is infinite. -/
theorem depth_eq_top_of_smul_top_eq_top (I : Ideal R) (M : ModuleCat.{v} R) [Module.Finite R M]
    (hI : I • (⊤ : Submodule R M) = ⊤) : I.depth M = ⊤ := by
  refine (ModuleCat.depth_eq_top_iff _ M).2 fun n ↦ Ext.subsingleton_of_annihilator_sup_eq_top ?_ n
  rwa [(Shrink.linearEquiv R (R ⧸ I)).annihilator_eq, annihilator_quotient,
    ← smul_top_eq_top_iff_sup_annihilator_eq_top]

variable [IsNoetherianRing R]

/-- Let `M` be a finite module over a Noetherian ring and `p` a prime ideal in the support of `M`
containing `I`. Then the depth of `M` with respect to `I` is at most the height of `p`. -/
theorem depth_le_height (I : Ideal R) (M : ModuleCat.{v} R) [Module.Finite R M] (p : Ideal R)
    [p.IsPrime] (hIp : I ≤ p) (hMp : Module.annihilator R M ≤ p) : I.depth M ≤ p.height := by
  have hI : I • (⊤ : Submodule R M) ≠ ⊤ := fun h ↦ IsPrime.ne_top' <| top_le_iff.1 <|
    (smul_top_eq_top_iff_sup_annihilator_eq_top I).1 h ▸ sup_le hIp hMp
  let Rₚ := Localization.AtPrime p
  let Mₚ := LocalizedModule p.primeCompl M
  have : Nontrivial Mₚ := Module.mem_support_iff.1 <|
    (Module.mem_support_iff_of_finite (p := ⟨p, inferInstance⟩)).2 hMp
  rw [depth_eq_sSup_length_isRegular I M hI.lt_top]
  refine sSup_le ?_
  rintro _ ⟨rs, reg, mem, rfl⟩
  -- An `M`-regular sequence in `I` stays regular on the localization `Mₚ`, whose dimension is at
  -- most the height of `p`.
  have regₚ := reg.toIsWeaklyRegular.isRegular_of_isLocalizedModule_of_mem Rₚ p
    (LocalizedModule.mkLinearMap p.primeCompl M) fun r hr ↦ hIp (mem r hr)
  refine WithBot.coe_le_coe.1 <| calc
    ((rs.length : ℕ∞) : WithBot ℕ∞) = (rs.map (algebraMap R Rₚ)).length := by simp
    _ ≤ Module.supportDim Rₚ Mₚ := regₚ.length_le_supportDim
    _ ≤ ringKrullDim Rₚ := Module.supportDim_le_ringKrullDim Rₚ Mₚ
    _ = p.height := IsLocalization.AtPrime.ringKrullDim_eq_height p Rₚ

/-- Let `M` be a finite module over a Noetherian ring and `I` an ideal with `I M ≠ M`. Then the
depth of `M` with respect to `I` is finite. -/
theorem depth_lt_top (I : Ideal R) (M : ModuleCat.{v} R) [Module.Finite R M]
    (hI : I • (⊤ : Submodule R M) ≠ ⊤) : I.depth M < ⊤ := by
  obtain ⟨m, hm, hle⟩ :=
    exists_le_maximal _ (mt (smul_top_eq_top_iff_sup_annihilator_eq_top I).2 hI)
  exact (depth_le_height I M m (le_sup_left.trans hle) (le_sup_right.trans hle)).trans_lt
    (height_lt_top hm.ne_top)

/-- For a finite module `M` over a Noetherian ring, the depth of `M` with respect to `I` is
infinite exactly when `I M = M`. -/
theorem depth_eq_top_iff (I : Ideal R) (M : ModuleCat.{v} R) [Module.Finite R M] :
    I.depth M = ⊤ ↔ I • (⊤ : Submodule R M) = ⊤ :=
  ⟨fun h ↦ by_contra fun hI ↦ (depth_lt_top I M hI).ne h, depth_eq_top_of_smul_top_eq_top I M⟩

/-- For a finite module `M` over a Noetherian ring and an ideal `I`, the depth of `M` with respect
to `I` is the supremum of the lengths of weakly `M`-regular sequences in `I`. Unlike
`Ideal.depth_eq_sSup_length_isRegular`, this needs no hypothesis `I M ≠ M`: when `I M = M` both
sides are `⊤`. -/
@[stacks 00LI "Stacks defines the `I`-depth of `M` by regular sequences when `I M ≠ M` and sets it
to `∞` when `I M = M`; weakly regular sequences give both cases at once."]
theorem depth_eq_sSup_length_isWeaklyRegular (I : Ideal R) (M : ModuleCat.{v} R)
    [Module.Finite R M] :
    I.depth M = sSup {(List.length rs : ℕ∞) | (rs : List R)
      (_ : IsWeaklyRegular M rs) (_ : ∀ r ∈ rs, r ∈ I)} := by
  by_cases hI : I • (⊤ : Submodule R M) = ⊤
  · -- For `r ∈ I` acting as the identity on `M`, every sequence `r, …, r` is weakly regular.
    obtain ⟨r, hrI, hr⟩ := Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul I ⊤
      Module.Finite.fg_top hI.ge
    have hreg : IsSMulRegular M r := fun x y hxy ↦ by
      simpa only [hr x trivial, hr y trivial] using hxy
    have : Subsingleton (QuotSMulTop r M) := Submodule.Quotient.subsingleton_iff.2 <|
      eq_top_iff.2 fun m _ ↦ hr m trivial ▸ Submodule.smul_mem_pointwise_smul m r ⊤ trivial
    rw [depth_eq_top_of_smul_top_eq_top I M hI, eq_comm, ENat.eq_top_iff_forall_ge]
    intro n
    refine le_trans (by simp) (le_sSup ⟨List.replicate (n + 1) r, ?_,
      fun s hs ↦ List.eq_of_mem_replicate hs ▸ hrI, rfl⟩)
    rw [List.replicate_succ, isWeaklyRegular_cons_iff]
    exact ⟨hreg, IsWeaklyRegular.of_subsingleton _⟩
  · -- When `I M ≠ M`, a weakly regular sequence in `I` is regular.
    rw [depth_eq_sSup_length_isRegular I M (lt_top_iff_ne_top.2 hI)]
    congr 1
    ext n
    refine ⟨fun ⟨rs, reg, mem, h⟩ ↦ ⟨rs, reg.toIsWeaklyRegular, mem, h⟩,
      fun ⟨rs, reg, mem, h⟩ ↦ ⟨rs, ⟨reg, fun htop ↦ hI ?_⟩, mem, h⟩⟩
    exact top_le_iff.1 <| htop.le.trans <| Submodule.smul_mono_left <| span_le.2 mem

end Ideal

namespace IsLocalRing

variable [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R]

/-- A finite module over a Noetherian local ring has infinite depth exactly when it is zero. -/
theorem depth_eq_top_iff (M : ModuleCat.{v} R) [Module.Finite R M] :
    depth M = ⊤ ↔ Subsingleton M := by
  rw [depth, Ideal.depth_eq_top_iff]
  refine ⟨fun h ↦ ?_, fun _ ↦ Subsingleton.elim _ _⟩
  by_contra hM
  rw [not_subsingleton_iff_nontrivial] at hM
  exact Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator (maximalIdeal_le_jacobson _) h.symm

/-- The depth of a finite module over a Noetherian local ring is the supremum of the lengths of
weakly `M`-regular sequences in the maximal ideal. -/
theorem depth_eq_sSup_length_isWeaklyRegular (M : ModuleCat.{v} R) [Module.Finite R M] :
    depth M = sSup {(List.length rs : ℕ∞) | (rs : List R)
      (_ : IsWeaklyRegular M rs) (_ : ∀ r ∈ rs, r ∈ maximalIdeal R)} :=
  (maximalIdeal R).depth_eq_sSup_length_isWeaklyRegular M

end IsLocalRing
end
end TAF_LiteralSource_0614

section TAF_LiteralSource_0615
/- Original module: TauCeti.RingTheory.CohenMacaulay.Height -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Height and coheight of primes in a Cohen–Macaulay local ring

In a Noetherian local ring `R` that is Cohen–Macaulay over itself, every prime `p` satisfies
`ht p + dim (R ⧸ p) = dim R` (Stacks, Lemma 10.103.10 (0AAF)). The inequality `≤` holds in every
ring (`Ideal.height_add_ringKrullDim_quotient_le`); the Cohen–Macaulay hypothesis gives the
reverse one. Without it the equation fails: in a local ring whose spectrum is a plane meeting a
line at a point, a minimal prime `p` cutting out the line has `ht p + dim (R ⧸ p) = 1 < 2`.

The proof chooses an `R`-regular sequence `r₁, …, rₖ` in `p` of maximal length. Its length is at
most `ht p`, and by maximality every element of `p` is a zero divisor on `N = R ⧸ (r₁, …, rₖ)`.
By prime avoidance `p` lies in an associated prime of `N`. Now `N` is again Cohen–Macaulay, of
dimension `dim R - k`, so it has no embedded primes, and `p` is itself associated to `N`. By
unmixedness `dim (R ⧸ p) = dim N = dim R - k ≥ dim R - ht p`.

This is the dimension formula that makes Cohen–Macaulay rings catenary: applied in the
localizations of a Cohen–Macaulay ring, it says that heights add along chains of primes.

## Main results

* `Module.IsCohenMacaulay.height_add_ringKrullDim_quotient`: for a Noetherian local ring `R`
  that is Cohen–Macaulay over itself and a prime `p`, `ht p + dim (R ⧸ p) = dim R`
  (Stacks, Lemma 10.103.10 (0AAF)).

## References

* [Stacks Project, Lemma 10.103.10](https://stacks.math.columbia.edu/tag/0AAF).
* H. Matsumura, *Commutative Ring Theory*, Theorem 17.4 (i).
-/

public section

universe u

open IsLocalRing RingTheory.Sequence Ideal

namespace Module.IsCohenMacaulay

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- **The dimension formula in a Cohen–Macaulay local ring.** For a Noetherian local ring `R`
that is Cohen–Macaulay over itself and a prime `p` of `R`, `ht p + dim (R ⧸ p) = dim R`.
Stacks, Lemma 10.103.10 (0AAF); H. Matsumura, *Commutative Ring Theory*, Theorem 17.4 (i). -/
@[stacks 0AAF]
theorem height_add_ringKrullDim_quotient (h : IsCohenMacaulay R R) (p : Ideal R) [p.IsPrime] :
    p.height + ringKrullDim (R ⧸ p) = ringKrullDim R := by
  refine le_antisymm p.height_add_ringKrullDim_quotient_le ?_
  -- The lengths of weakly `R`-regular sequences in `p` are bounded by `ht p`, so the longest one
  -- exists.
  let lengths : Set ℕ∞ := {(List.length rs : ℕ∞) | (rs : List R)
    (_ : IsWeaklyRegular R rs) (_ : ∀ r ∈ rs, r ∈ p)}
  have : Nonempty lengths := ⟨⟨0, [], IsWeaklyRegular.nil R R, by simp, rfl⟩⟩
  have hbound : sSup lengths ≤ p.height := by
    rw [← p.depth_eq_sSup_length_isWeaklyRegular (ModuleCat.of R R)]
    refine p.depth_le_height _ p le_rfl ?_
    exact (annihilator_eq_bot.2 inferInstance).trans_le bot_le
  obtain ⟨rs, reg, mem, hlen⟩ := ENat.sSup_mem_of_nonempty_of_lt_top <|
    hbound.trans_lt (height_lt_top IsPrime.ne_top')
  have regR : IsRegular R rs :=
    (isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal fun r hr ↦
      le_maximalIdeal IsPrime.ne_top' (mem r hr)).2 reg
  -- The quotient `N = R ⧸ (r₁, …, rₖ)` is Cohen–Macaulay, of dimension `dim R - k`.
  let N := R ⧸ ofList rs • (⊤ : Submodule R R)
  have hN : IsCohenMacaulay R N := (isCohenMacaulay_quotient_ofList_smul_iff rs regR).2 h
  have hann : annihilator R N ≤ p := by
    simp only [N, smul_eq_mul, mul_top, Ideal.annihilator_quotient]
    exact span_le.2 mem
  -- By maximality of `r₁, …, rₖ`, no element of `p` is regular on `N`.
  have hnreg : ¬ ∃ a ∈ p, IsSMulRegular N a := fun ⟨a, ha, hreg⟩ ↦ by
    have hmem : ((rs ++ [a]).length : ℕ∞) ∈ lengths := ⟨rs ++ [a],
      (isWeaklyRegular_append_iff R rs [a]).2 ⟨reg, (isWeaklyRegular_singleton_iff N a).2 hreg⟩,
      by simpa [or_imp, forall_and] using ⟨mem, ha⟩, rfl⟩
    exact absurd (le_sSup hmem) (by simp [← hlen, ENat.lt_add_one_iff])
  -- So `p` lies in an associated prime of `N`, which is minimal over the annihilator of `N`, so
  -- `p` is itself associated to `N`.
  obtain ⟨q, hq, hpq⟩ : ∃ q ∈ associatedPrimes R N, p ≤ q := by
    simpa using mt (p.exists_mem_isSMulRegular_iff (M := N)).2 hnreg
  have hqp : q = p :=
    le_antisymm ((hN.associatedPrimes_eq_minimalPrimes ▸ hq).2 ⟨inferInstance, hann⟩ hpq) hpq
  have hpN : IsAssociatedPrime p N := AssociatedPrimes.mem_iff.1 (hqp ▸ hq)
  -- By unmixedness `dim (R ⧸ p) = dim N = dim R - k`, and `k ≤ ht p`.
  rw [hN.ringKrullDim_quotient_eq_supportDim hpN, ← supportDim_self_eq_ringKrullDim,
    ← supportDim_add_length_eq_supportDim_of_isRegular rs regR, add_comm]
  gcongr
  exact_mod_cast hlen ▸ hbound

end Module.IsCohenMacaulay
end
end TAF_LiteralSource_0615

section TAF_LiteralSource_0616
/- Original module: TauCeti.RingTheory.RegularLocalRing.CohenMacaulay -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Regular local rings are Cohen–Macaulay

Let `(R, 𝔪)` be a regular local ring of dimension `d`, so that `𝔪` is generated by `d` elements.
This file proves that any `d` elements generating `𝔪` form an `R`-regular sequence, so that the
depth of `R` equals its dimension and `R` is Cohen–Macaulay over itself. In particular a regular
local ring of dimension at least `n` has depth at least `n`, the input that lets results stated
for local rings of large depth, such as extension of sections across a closed point, apply to
regular local rings.

## Main results

* `TauCeti.IsRegularLocalRing.isRegular_of_ofList_eq_maximalIdeal`: a list of at most
  `spanFinrank 𝔪` elements generating `𝔪`, that is, a regular system of parameters, is an
  `R`-regular sequence.
* `TauCeti.IsRegularLocalRing.depth_eq_ringKrullDim`: the depth of a regular local ring over
  itself is its Krull dimension.
* `TauCeti.IsRegularLocalRing.isCohenMacaulay`: a regular local ring is Cohen–Macaulay over itself.

The proof is induction on the dimension: the first entry `x` of a regular system of parameters
lies outside `𝔪²`, so it is a nonzero element of the domain `R` and `R ⧸ (x)` is a regular local
ring of dimension `d - 1`, whose maximal ideal is generated by the images of the remaining
entries.

## References

* [The Stacks Project, Lemma 10.106.3](https://stacks.math.columbia.edu/tag/00NQ).
-/

public section

universe u

open _root_.IsLocalRing Ideal RingTheory.Sequence

namespace TauCeti.IsRegularLocalRing

/-- The induction on the length behind `isRegular_of_ofList_eq_maximalIdeal`, stated for every
regular local ring in the universe so that it applies to the quotient by the first entry. -/
private theorem isRegular_of_ofList_eq_maximalIdeal_aux (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] (rs : List R), rs.length = n →
      ofList rs = maximalIdeal R → rs.length ≤ (maximalIdeal R).spanFinrank →
      IsRegular R rs := by
  induction n with
  | zero =>
    intro R _ _ rs hn _ _
    rw [List.length_eq_zero_iff.mp hn]
    exact IsRegular.nil R R
  | succ n ih =>
    intro R _ _ rs hn hspan hlen
    obtain ⟨x, rs, rfl⟩ := List.exists_cons_of_length_eq_add_one hn
    have hmem : ∀ r ∈ x :: rs, r ∈ maximalIdeal R := fun r hr ↦ hspan ▸ subset_span hr
    have hxm : x ∈ maximalIdeal R := hmem x List.mem_cons_self
    let mk := Ideal.Quotient.mk (span {x})
    -- modulo `x`, the maximal ideal is generated by the images of the remaining entries
    have hmap : (maximalIdeal R).map mk = ofList (rs.map mk) := by
      rw [← hspan, map_ofList]
      simp [mk]
    -- a list spans an ideal with at most as many generators as its length
    have hrank : (ofList (rs.map mk)).spanFinrank ≤ rs.length := by
      exact (Submodule.spanFinrank_span_list_le_length (rs.map mk)).trans_eq (List.length_map _)
    rw [List.length_cons] at hlen
    -- the first entry is a parameter: otherwise `𝔪` would need no more than `rs.length` generators
    have hx2 : x ∉ maximalIdeal R ^ 2 := fun hx2 ↦ by
      have := TauCeti.IsLocalRing.spanFinrank_map_maximalIdeal_quotient_of_le_sq
        (maximalIdeal R).fg_of_isNoetherianRing ((span_singleton_le_iff_mem _).mpr hx2)
      rw [hmap] at this
      omega
    have hx0 : x ≠ 0 := fun h ↦ hx2 (h ▸ zero_mem _)
    have : IsRegularLocalRing (R ⧸ span {x}) := quotient_span_singleton hxm hx2
    have hdrop := spanFinrank_maximalIdeal_quotient_span_singleton_add_one hxm hx0
    have hQ : IsRegular (R ⧸ span {x}) (rs.map mk) := ih _ _ (by simpa using hn)
      (hmap ▸ map_maximalIdeal_of_surjective mk Ideal.Quotient.mk_surjective)
      (by rw [List.length_map]; omega)
    -- transport the regularity of the images to `R ⧸ x R` viewed as an `R`-module
    have e : QuotSMulTop x R ≃ₗ[R] R ⧸ span {x} :=
      (quotientEquivAlgOfEq R (by simp [← Submodule.ideal_span_singleton_smul])).toLinearEquiv
    refine (isRegular_cons_iff R x rs).2 ⟨IsSMulRegular.of_ne_zero hx0, ?_⟩
    rw [e.isRegular_congr]
    refine IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal _
      (fun r hr ↦ hmem r (List.mem_cons_of_mem x hr)) ?_
    rw [← isWeaklyRegular_map_algebraMap_iff (R ⧸ span {x}), Ideal.Quotient.algebraMap_eq]
    exact hQ.toIsWeaklyRegular

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- **A regular system of parameters is a regular sequence.** In a regular local ring
`(R, 𝔪)`, a list of at most `spanFinrank 𝔪 = dim R` elements generating `𝔪` (necessarily of
exactly that length) is an `R`-regular sequence. Stacks, Lemma 10.106.3 (00NQ). -/
@[stacks 00NQ "(1)"]
theorem isRegular_of_ofList_eq_maximalIdeal {rs : List R}
    (hspan : ofList rs = maximalIdeal R) (hlen : rs.length ≤ (maximalIdeal R).spanFinrank) :
    IsRegular R rs :=
  isRegular_of_ofList_eq_maximalIdeal_aux _ R rs rfl hspan hlen

/-- The depth of a regular local ring over itself equals its Krull dimension. -/
theorem depth_eq_ringKrullDim :
    (depth (ModuleCat.of R R) : WithBot ℕ∞) = ringKrullDim R := by
  refine le_antisymm (Module.supportDim_self_eq_ringKrullDim (R := R) ▸ depth_le_supportDim) ?_
  obtain ⟨s, hcard, hspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank (maximalIdeal R).fg_of_isNoetherianRing
  have hofList : ofList s.toList = maximalIdeal R := by simpa [ofList] using hspan
  have hlen : s.toList.length = (maximalIdeal R).spanFinrank := by simpa using hcard
  have hreg := isRegular_of_ofList_eq_maximalIdeal hofList hlen.le
  rw [← _root_.IsRegularLocalRing.spanFinrank_maximalIdeal,
    IsLocalRing.depth_eq_sSup_length_isRegular]
  refine WithBot.coe_le_coe.mpr (le_sSup ⟨s.toList, hreg, fun r hr ↦ ?_, by simp [hlen]⟩)
  exact hofList ▸ subset_span hr

/-- **A regular local ring is Cohen–Macaulay.** Stacks, Lemma 10.106.3 (00NQ). -/
@[stacks 00NQ "Cohen–Macaulay assertion"]
theorem isCohenMacaulay : Module.IsCohenMacaulay R R := by
  rw [Module.isCohenMacaulay_iff_depth_eq, Module.supportDim_self_eq_ringKrullDim]
  exact depth_eq_ringKrullDim

end TauCeti.IsRegularLocalRing

/-- In particular, every prime `p` of a regular local ring satisfies
`ht p + dim (R ⧸ p) = dim R`. -/
example {R : Type u} [CommRing R] [IsRegularLocalRing R] (p : Ideal R) [p.IsPrime] :
    p.height + ringKrullDim (R ⧸ p) = ringKrullDim R :=
  TauCeti.IsRegularLocalRing.isCohenMacaulay.height_add_ringKrullDim_quotient p
end
end TAF_LiteralSource_0616

section TAF_LiteralSource_0617
/- Original module: TauCeti.RingTheory.KrullDimension.Polynomial -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Height of the origin over a closed point

In a polynomial ring over a Noetherian ring, a maximal ideal lying over a maximal ideal `p`
of the base, such as the inverse image of `p` under constant coefficient, has height equal to
the height of `p` plus the number of variables. This computes the dimension of the ambient
local ring used for hypersurface singularities over a local base.

## References

* H. Matsumura, *Commutative Algebra*, §13, Theorem 19: the height formula for flat algebras.
-/

public section

namespace TauCeti

open MvPolynomial

variable {R σ : Type*} [CommRing R] [IsNoetherianRing R] [Finite σ]

/-- A maximal ideal of a polynomial ring lying over a maximal ideal `p` has height the height
of `p` plus the number of polynomial variables. -/
theorem _root_.MvPolynomial.height_eq_height_add_natCard (p : Ideal R) [p.IsMaximal]
    (P : Ideal (MvPolynomial σ R)) [P.IsMaximal] [P.LiesOver p] :
    P.height = p.height + Nat.card σ := by
  let Q := P.map (Ideal.Quotient.mk (p.map (algebraMap R (MvPolynomial σ R))))
  have : Q.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le
    Ideal.Quotient.mk_surjective (by
      rw [Ideal.mk_ker, Ideal.LiesOver.over (P := P) (p := p)]
      exact Ideal.map_comap_le)
  let e : MvPolynomial σ (R ⧸ p) ≃+*
      (MvPolynomial σ R ⧸ p.map (algebraMap R (MvPolynomial σ R))) :=
    (quotientEquivQuotientMvPolynomial (σ := σ) p).toRingEquiv
  have : (Q.comap e).IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.surjective
  let : Field (R ⧸ p) := Ideal.Quotient.field p
  have hQ : Q.height = Nat.card σ := by
    rw [← e.height_comap Q]
    exact height_eq_natCard_of_isMaximal (k := R ⧸ p) (Q.comap e)
  calc
    _ = p.height + Q.height := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P
    _ = _ := by rw [hQ]

/-- The origin over a closed point has height the height of that point plus the number of
polynomial variables. -/
theorem _root_.Ideal.height_comap_mvPolynomial_constantCoeff (p : Ideal R) [p.IsMaximal] :
    (p.comap (constantCoeff : MvPolynomial σ R →+* R)).height = p.height + Nat.card σ := by
  have hsurj : Function.Surjective (constantCoeff : MvPolynomial σ R →+* R) :=
    fun r ↦ ⟨C r, constantCoeff_C σ r⟩
  have : (p.comap (constantCoeff : MvPolynomial σ R →+* R)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ hsurj
  have : (p.comap (constantCoeff : MvPolynomial σ R →+* R)).LiesOver p :=
    ⟨by ext r; simp [Ideal.under_def]⟩
  exact MvPolynomial.height_eq_height_add_natCard p _

/-- Adjoining polynomial coordinates and localizing at the closed origin raises local
Krull dimension by the number of coordinates. -/
theorem ringKrullDim_localization_comap_mvPolynomial_constantCoeff [IsLocalRing R] :
    ringKrullDim (Localization.AtPrime ((IsLocalRing.maximalIdeal R).comap
      (constantCoeff : MvPolynomial σ R →+* R))) = ringKrullDim R + Nat.card σ := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height
      ((IsLocalRing.maximalIdeal R).comap (constantCoeff : MvPolynomial σ R →+* R)),
    Ideal.height_comap_mvPolynomial_constantCoeff, WithBot.coe_add,
    IsLocalRing.maximalIdeal_height_eq_ringKrullDim, WithBot.coe_natCast]

end TauCeti
end
end TAF_LiteralSource_0617

section TAF_LiteralSource_0618
/- Original module: PaperVerification.HomogeneousRegularSequence -/


/-!
# Homogeneous systems of parameters in a polynomial ring

The conclusion is global weak regularity. The proof first computes the dimension
of the local ring at the origin, uses regular-local Cohen--Macaulayness and the
system-of-parameters theorem there, and then descends regularity by homogeneous
components. No faithful-flatness assertion for a single localization is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open MvPolynomial RingTheory.Sequence IsLocalRing

namespace PaperVerification.HomogeneousLocalization

variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K
local notation "L" => OriginLocalRing (K := K) (ι := ι)

/-- The actual origin local ring has exactly one dimension per variable. -/
theorem originLocalRing_dimension : ringKrullDim L = (Fintype.card ι : WithBot ℕ∞) := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height
    (originIdeal (K := K) (ι := ι)) L,
    MvPolynomial.height_eq_natCard_of_isMaximal]
  simp only [Nat.card_eq_fintype_card, WithBot.coe_natCast]

/-- Every homogeneous system of parameters of the full length is weakly
regular in the polynomial ring itself, in every characteristic. -/
theorem homogeneous_parameters_regular
    (w : ι → ℕ) (hw : ∀ i, w i ≠ 0)
    (rs : List P) (hhom : ∀ f ∈ rs, ∃ d, f.IsWeightedHomogeneous w d)
    (horigin : ∀ f ∈ rs, f ∈ originIdeal (K := K) (ι := ι))
    (hrad : originIdeal (K := K) (ι := ι) ≤ (Ideal.ofList rs).radical)
    (hlen : rs.length = Fintype.card ι) : IsWeaklyRegular P rs := by
  let a : P →+* L := algebraMap P L
  have hcm : Module.IsCohenMacaulay L L :=
    TauCeti.IsRegularLocalRing.isCohenMacaulay
  have hmem : ∀ f ∈ rs.map a, f ∈ maximalIdeal L := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem a (horigin g hg)
  have hann : Module.annihilator L L = ⊥ := Module.annihilator_eq_bot.mpr inferInstance
  have hradLoc : maximalIdeal L ≤
      (Ideal.ofList (rs.map a) ⊔ Module.annihilator L L).radical := by
    rw [hann, sup_bot_eq, ← Ideal.map_ofList, ← Localization.AtPrime.map_eq_maximalIdeal]
    exact (Ideal.map_mono hrad).trans (Ideal.map_radical_le a)
  have hlength : ((rs.map a).length : WithBot ℕ∞) = Module.supportDim L L := by
    rw [List.length_map, hlen, Module.supportDim_self_eq_ringKrullDim,
      originLocalRing_dimension]
  have hlocal : IsRegular L (rs.map a) := hcm.isRegular_of_le_radical hmem hradLoc hlength
  exact sequence_regular_of_localized w hw rs hhom hlocal.toIsWeaklyRegular

/-- Function-indexed form, retaining arbitrary finite dimension. -/
theorem homogeneous_family_regular {n : ℕ}
    (w : Fin n → ℕ) (hw : ∀ i, w i ≠ 0)
    (f : Fin n → MvPolynomial (Fin n) K)
    (hhom : ∀ i, ∃ d, (f i).IsWeightedHomogeneous w d)
    (horigin : ∀ i, constantCoeff (f i) = 0)
    (hrad : originIdeal (K := K) (ι := Fin n) ≤
      (Ideal.span (Set.range f)).radical) :
    IsWeaklyRegular (MvPolynomial (Fin n) K) (List.ofFn f) := by
  apply homogeneous_parameters_regular w hw (List.ofFn f)
  · intro g hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
    exact hhom i
  · intro g hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
    exact horigin i
  · have hs : {g | g ∈ List.ofFn f} = Set.range f := by
      ext g
      exact List.mem_ofFn
    simpa only [Ideal.ofList, hs] using hrad
  · simp

end PaperVerification.HomogeneousLocalization
end
end
end TAF_LiteralSource_0618

section TAF_LiteralSource_0619
/- Original module: PaperVerification.HomogeneousNullstellensatz -/


/-!
# From the actual common zero set to regularity

This file closes the algebraic-geometry step over an algebraically closed field:
if a full-length homogeneous sequence vanishes at the origin and has no other
common zero, it is regular. The zero-set hypothesis is about evaluation of the
actual defining polynomials, not a substitute definition of regularity.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial RingTheory.Sequence

namespace PaperVerification.HomogeneousLocalization

variable {K ι : Type*} [Field K] [IsAlgClosed K] [Fintype ι]
local notation "P" => MvPolynomial ι K

theorem origin_le_radical_of_zeroLocus
    (I : Ideal P) (hzero : ∀ x ∈ zeroLocus K I, x = 0) :
    originIdeal (K := K) (ι := ι) ≤ I.radical := by
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := K)]
  intro f hf x hx
  rw [hzero x hx, aeval_zero, Algebra.algebraMap_self]
  exact hf

/-- A full sequence with the origin as its entire common zero set is regular. -/
theorem homogeneous_parameters_regular_of_common_zero
    (w : ι → ℕ) (hw : ∀ i, w i ≠ 0)
    (rs : List P) (hhom : ∀ f ∈ rs, ∃ d, f.IsWeightedHomogeneous w d)
    (horigin : ∀ f ∈ rs, constantCoeff f = 0)
    (hzero : ∀ x : ι → K, (∀ f ∈ rs, aeval x f = 0) → x = 0)
    (hlen : rs.length = Fintype.card ι) : IsWeaklyRegular P rs := by
  apply homogeneous_parameters_regular w hw rs hhom horigin _ hlen
  apply origin_le_radical_of_zeroLocus
  intro x hx
  apply hzero x
  intro f hf
  exact hx f (Ideal.subset_span hf)

/-- Function-indexed version for actual polynomial families. -/
theorem homogeneous_family_regular_of_common_zero {n : ℕ}
    (w : Fin n → ℕ) (hw : ∀ i, w i ≠ 0)
    (f : Fin n → MvPolynomial (Fin n) K)
    (hhom : ∀ i, ∃ d, (f i).IsWeightedHomogeneous w d)
    (horigin : ∀ i, constantCoeff (f i) = 0)
    (hzero : ∀ x : Fin n → K, (∀ i, aeval x (f i) = 0) → x = 0) :
    IsWeaklyRegular (MvPolynomial (Fin n) K) (List.ofFn f) := by
  apply homogeneous_parameters_regular_of_common_zero w hw (List.ofFn f)
  · intro g hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
    exact hhom i
  · intro g hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
    exact horigin i
  · intro x hx
    exact hzero x (fun i => hx (f i) (List.mem_ofFn.mpr ⟨i, rfl⟩))
  · simp

end PaperVerification.HomogeneousLocalization
end
end
end TAF_LiteralSource_0619

section TAF_LiteralSource_0620
/- Original module: PaperVerification.AlternatingFormsFieldDescent -/


/-!
# A common-zero test over an algebraically closed extension

Mathlib's Nullstellensatz is stated for a polynomial ring over any field and
zeros valued in an algebraically closed extension. It therefore puts the origin
ideal inside the radical in the original coefficient ring directly. No change
of polynomial-ring universes, scalar-extension regularity assumption, or
faithful-flatness premise is needed.
-/

@[expose] public section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial RingTheory.Sequence

variable {K L σ : Type*} [Field K] [Field L] [Algebra K L]

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
  apply HomogeneousLocalization.homogeneous_parameters_regular w hw rs
    hhom horigin _ hlen
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := L)]
  intro f hf x hx
  have hx0 : x = 0 := hzero x (fun g hg => by
    simpa only [MvPolynomial.aeval_def] using hx g (Ideal.subset_span hg))
  rw [hx0, MvPolynomial.aeval_zero,
    (HomogeneousLocalization.mem_originIdeal f).mp hf, map_zero]

end PaperVerification.AlternatingForms
end
end TAF_LiteralSource_0620

section TAF_LiteralSource_0621
/- Original module: PaperVerification.AlternatingFormsChernRegularity -/


/-!
# The Chern relations form a regular sequence

This file applies the general homogeneous-system-of-parameters theorem to the
actual relations of Section 4.3.  It also establishes compatibility of the
relations with change of coefficient field.  The cohomology and Chow comparison
is a further geometric theorem, not part of the definition of this sequence.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open Finset RingTheory.Sequence

variable {K L σ : Type*} [Field K] [CharZero K] [Field L] [CharZero L]
  [Fintype σ] [DecidableEq σ]

/-- Section 4.3's regularity statement over an algebraically closed field of
characteristic zero, for every number of variables and every positive window. -/
theorem chernRelationSequence_isWeaklyRegular [IsAlgClosed K] (s w : ℕ) (hw : 0 < w) :
    IsWeaklyRegular (MvPolynomial (Fin s) K) (chernRelationSequence K s w) := by
  apply HomogeneousLocalization.homogeneous_family_regular_of_common_zero
    chernCoefficientWeight chernCoefficientWeight_ne_zero
    (fun i : Fin s => chernCoefficientRelation s (w + i.val))
  · intro i
    exact ⟨w + i.val, chernCoefficientRelation_isWeightedHomogeneous s (w + i.val)⟩
  · intro i
    exact chernCoefficientRelation_constantCoeff s (w + i.val) (by omega)
  · intro x hx
    apply chernCoefficientRelation_common_zero hw x
    intro m hwm hms
    let i : Fin s := ⟨m - w, by omega⟩
    have hi : w + i.val = m := by dsimp [i]; omega
    simpa only [hi, MvPolynomial.aeval_eq_eval] using hx i

/-- The sequence generates a proper ideal, since every entry vanishes at the
origin.  This is the nonzero-quotient condition in Mathlib's `IsRegular`. -/
theorem chernRelationSequence_top_ne_smul (s w : ℕ) (hw : 0 < w) :
    (⊤ : Submodule (MvPolynomial (Fin s) K) (MvPolynomial (Fin s) K)) ≠
      Ideal.ofList (chernRelationSequence K s w) • ⊤ := by
  intro htop
  have hmem : (1 : MvPolynomial (Fin s) K) ∈
      Ideal.ofList (chernRelationSequence K s w) := by
    have h : (1 : MvPolynomial (Fin s) K) ∈
        Ideal.ofList (chernRelationSequence K s w) •
          (⊤ : Submodule (MvPolynomial (Fin s) K) (MvPolynomial (Fin s) K)) := by
      rw [← htop]
      trivial
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using h
  have hle : Ideal.ofList (chernRelationSequence K s w) ≤
      RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin s) K →+* K) := by
    apply Ideal.span_le.mpr
    intro f hf
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
    exact chernCoefficientRelation_constantCoeff s (w + i.val) (by omega)
  have hzero := hle hmem
  simpa using hzero

theorem chernRelationSequence_isRegular [IsAlgClosed K] (s w : ℕ) (hw : 0 < w) :
    IsRegular (MvPolynomial (Fin s) K) (chernRelationSequence K s w) :=
  ⟨chernRelationSequence_isWeaklyRegular s w hw,
    chernRelationSequence_top_ne_smul s w hw⟩

/-- The regular-sequence assertion over the original characteristic-zero field.
The common-zero argument is performed over its actual algebraic closure and
proved by the extension-valued Nullstellensatz; algebraic closedness is not an added hypothesis. -/
theorem chernRelationSequence_isWeaklyRegular_over_field (s w : ℕ) (hw : 0 < w) :
    IsWeaklyRegular (MvPolynomial (Fin s) K) (chernRelationSequence K s w) := by
  apply homogeneous_parameters_regular_of_common_zero_extension
    (L := AlgebraicClosure K) chernCoefficientWeight chernCoefficientWeight_ne_zero
    (chernRelationSequence K s w)
  · intro f hf
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
    exact ⟨w + i.val, chernCoefficientRelation_isWeightedHomogeneous s (w + i.val)⟩
  · intro f hf
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
    exact chernCoefficientRelation_constantCoeff s (w + i.val) (by omega)
  · intro x hx
    apply chernCoefficientRelation_common_zero hw x
    intro m hwm hms
    let i : Fin s := ⟨m - w, by omega⟩
    have hi : w + i.val = m := by dsimp [i]; omega
    have h := hx (chernCoefficientRelation s (w + i.val))
      (List.mem_ofFn.mpr ⟨i, rfl⟩)
    rw [← MvPolynomial.eval_map, map_chernCoefficientRelation, hi] at h
    exact h
  · simp [chernRelationSequence]

/-- The homogeneous regular sequence of Section 4.3, including its rational
coefficient field and its entire parameter range. -/
theorem chernRelationSequence_isRegular_over_field (s w : ℕ) (hw : 0 < w) :
    IsRegular (MvPolynomial (Fin s) K) (chernRelationSequence K s w) :=
  ⟨chernRelationSequence_isWeaklyRegular_over_field s w hw,
    chernRelationSequence_top_ne_smul s w hw⟩

end PaperVerification.AlternatingForms
end
end TAF_LiteralSource_0621

section TAF_LiteralSource_0622
/- Original module: PaperVerification.ChernFinite -/


/-!
# Finiteness of the literal Chern quotient

The polynomial common-zero calculation over an algebraic closure is converted
by Hilbert's Nullstellensatz into nilpotence of every variable in the quotient.
Those generators are therefore integral over the coefficient field. The actual
quotient is finitely generated as an algebra, so it is finite as a module.

This argument uses no regularity or Hilbert-series assertion and keeps the
underlying quotient by the paper's original finite window of relations.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification

open MvPolynomial

/-- A finite-variable polynomial quotient with nilpotent coordinate classes
is module-finite over its coefficient ring. -/
theorem finite_polynomial_quotient_of_X_mem_radical
    {R σ : Type*} [CommRing R] [Finite σ]
    (I : Ideal (MvPolynomial σ R)) (hX : ∀ i, X i ∈ I.radical) :
    Module.Finite R (MvPolynomial σ R ⧸ I) := by
  have hXi : ∀ i, IsIntegral R (Ideal.Quotient.mk I (X i)) := by
    intro i
    obtain ⟨n,hn⟩ := hX i
    refine ⟨Polynomial.X^n, Polynomial.monic_X_pow n, ?_⟩
    rw [Polynomial.eval₂_pow, Polynomial.eval₂_X, ← map_pow,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hn
  letI : Algebra.IsIntegral R (MvPolynomial σ R ⧸ I) := by
    constructor
    intro z
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective z
    induction p using MvPolynomial.induction_on with
    | C r => exact isIntegral_algebraMap
    | add p q hp hq => simpa only [map_add] using hp.add hq
    | mul_X p i hp => simpa only [map_mul] using hp.mul (hXi i)
  exact Algebra.IsIntegral.finite

namespace AlternatingForms

variable {K : Type*} [Field K] [CharZero K]

/-- Every Chern coordinate lies in the radical of the actual relation ideal.
The common-zero calculation is made in an algebraic closure, while radical
membership is concluded in the original coefficient field. -/
theorem chern_X_mem_radical (s w : ℕ) (hw : 0<w) (i : Fin s) :
    (X i : MvPolynomial (Fin s) K) ∈
      (Ideal.ofList (chernRelationSequence K s w)).radical := by
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical
    (K := AlgebraicClosure K)]
  intro c hc
  have hc0 : c = 0 := by
    apply chernCoefficientRelation_common_zero hw c
    intro m hwm hms
    let j : Fin s := ⟨m-w, by omega⟩
    have hj : w+j.val=m := by dsimp [j]; omega
    have hg : chernCoefficientRelation (K := K) s (w+j.val) ∈
        Ideal.ofList (chernRelationSequence K s w) :=
      Ideal.subset_span (List.mem_ofFn.mpr ⟨j,rfl⟩)
    have hz := hc _ hg
    rw [MvPolynomial.aeval_def, ← MvPolynomial.eval_map,
      map_chernCoefficientRelation, hj] at hz
    exact hz
  simp only [MvPolynomial.aeval_X, hc0, Pi.zero_apply]

/-- The Section 4 coefficient quotient is finite-dimensional for every
positive starting degree, not only for the geometric range of parameters. -/
theorem chern_relation_quotient_finite (s w : ℕ) (hw : 0<w) :
    Module.Finite K
      (MvPolynomial (Fin s) K ⧸ Ideal.ofList (chernRelationSequence K s w)) :=
  finite_polynomial_quotient_of_X_mem_radical _ (chern_X_mem_radical s w hw)

end AlternatingForms
end PaperVerification
end
end
end TAF_LiteralSource_0622

section TAF_LiteralSource_0623
/- Original module: PaperVerification.AlternatingFormsChernDimension -/


/-!
# Dimension of the paper's actual Chern-relation quotient

There are no geometric identifications among the assumptions of this file.
The relations are the descended root polynomials of Section 4, with coefficient
variable weights `1,...,s`, and the quotient is the literal ideal quotient.
Regularity and finiteness are proved independently from the common-zero
calculation; the graded exact sequences then determine its dimension.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace PaperVerification.AlternatingForms

variable {K : Type*} [Field K] [CharZero K]

set_option backward.isDefEq.respectTransparency false in
/-- The full weighted Hilbert series of the literal Chern-relation quotient.
The homogeneous pieces are the images of the usual weight-`1,...,s` pieces,
so the grading is specified independently of the dimension formula. -/
theorem chern_relation_quotient_hilbertSeries (s w : ℕ) (hw : 0<w) :
    ∃ H : TauCeti.InternalGrading K
        (MvPolynomial (Fin s) K ⧸ Ideal.ofList (chernRelationSequence K s w)) ℕ,
      (∀ d, H.piece d =
        ((WeightedRegularQuotientDimension.polynomialGrading (K:=K)
          chernCoefficientWeight).piece d).map
        ((Ideal.ofList (chernRelationSequence K s w)).mkQ.restrictScalars K)) ∧
      GradedInjectiveQuotient.hilbertSeries H *
        (∏ i : Fin s, (1-PowerSeries.X^(i.val+1))) =
        ∏ i : Fin s, (1-PowerSeries.X^(w+i.val)) := by
  classical
  obtain ⟨H, hp, hh⟩ :=
    WeightedRegularQuotientDimension.exists_graded_quotient_hilbertSeries
      (K:=K) chernCoefficientWeight chernCoefficientWeight_ne_zero s
      (fun i : Fin s => chernCoefficientRelation s (w+i.val))
      (fun i : Fin s => w+i.val)
      (fun i => chernCoefficientRelation_isWeightedHomogeneous s (w+i.val))
      (chernRelationSequence_isWeaklyRegular_over_field s w hw)
  refine ⟨H, hp, ?_⟩
  exact hh

/-- The complete-intersection quotient has the expected total dimension for
all positive starting degrees, over every characteristic-zero field. -/
theorem chern_relation_quotient_finrank (s w : ℕ) (hw : 0<w) :
    Module.finrank K
      (MvPolynomial (Fin s) K ⧸ Ideal.ofList (chernRelationSequence K s w)) =
      (w+s-1).choose s := by
  classical
  letI := chern_relation_quotient_finite (K:=K) s w hw
  obtain ⟨H, _, hh⟩ := chern_relation_quotient_hilbertSeries (K:=K) s w hw
  have hd := FiniteGradedDimension.finrank_mul_product_degrees H
    (fun i : Fin s => i.val+1) (fun i : Fin s => w+i.val) hh
  have hn :
      Module.finrank K
          (MvPolynomial (Fin s) K ⧸ Ideal.ofList (chernRelationSequence K s w)) *
        (∏ i : Fin s, (i.val+1)) = (∏ i : Fin s, (w+i.val)) := by
    exact_mod_cast hd
  rw [← Finset.prod_range (fun i : ℕ => i+1),
    ← Finset.prod_range (fun i : ℕ => w+i)] at hn
  rw [← Nat.factorial_eq_prod_range_add_one, ← Nat.ascFactorial_eq_prod_range,
    Nat.ascFactorial_eq_factorial_mul_choose'] at hn
  exact Nat.eq_of_mul_eq_mul_right s.factorial_pos (by simpa only [mul_comm] using hn)

/-- The geometric odd-pencil parameter range gives the Gaussian polynomial's
value at one, with no restriction to a finite list of examples. -/
theorem odd_chern_relation_quotient_finrank (s N : ℕ) :
    Module.finrank K
      (MvPolynomial (Fin s) K ⧸
        Ideal.ofList (chernRelationSequence K s (2*(N-s)+1))) =
      (2*(N-s)+s).choose s := by
  have h := chern_relation_quotient_finrank (K:=K) s (2*(N-s)+1) (by omega)
  simpa only [Nat.add_right_comm _ 1, Nat.add_sub_cancel] using h

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0623

section TAF_LiteralSource_0624
/- Original module: PaperVerification.GenericSectionDifferentials -/


/-!
# Independent differentials for a generic vector-valued section

The first two lemmas adapt the proof in OpenAI's public `CriticalLocus.lean`,
commit `4eaee87548250b2682affda7d05d947c05554bae`,
`OAI/AlgebraicGeometry/Seshadri/Bertini/`. The original source is distributed
under Apache-2.0. Its proof uses Mathlib's Jacobi--Zariski sequence and formal
smoothness of extensions of characteristic-zero fields.

The final theorem is the vector-valued extension needed for a generated
bundle. At a common zero of the section, independence of the coefficient
parameters and surjectivity of evaluation force independence of the section's
differentials. The target is the actual module of Kähler differentials.
-/

@[expose] public section
noncomputable section
open scoped TensorProduct BigOperators
open KaehlerDifferential

namespace PaperVerification.GenericSectionDifferentials

theorem mapBaseChange_injective_of_formallySmooth
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FormallySmooth A B] :
    Function.Injective (KaehlerDifferential.mapBaseChange R A B) := by
  apply (KaehlerDifferential.mapBaseChange R A B).ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨y, hy⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R A B x).mp hx
  rw [show y=0 from Subsingleton.elim _ _, map_zero] at hy
  exact hy.symm ▸ Submodule.zero_mem _

variable {K L ι : Type*} [Field K] [Field L] [CharZero K] [Algebra K L]

/-- Algebraically independent parameters have independent actual differentials. -/
theorem algebraicIndependent_differentials [Algebra.EssFiniteType K L]
    (v : ι → L) (hv : AlgebraicIndependent K v) :
    LinearIndependent L (fun i => KaehlerDifferential.D K L (v i)) := by
  let A := MvPolynomial ι K
  let F := FractionRing A
  let a : A →ₐ[K] L := MvPolynomial.aeval v
  let b : F →ₐ[K] L := IsFractionRing.liftAlgHom hv
  let : Algebra A L := a.toRingHom.toAlgebra
  let : Algebra F L := b.toRingHom.toAlgebra
  let : IsScalarTower K A L := IsScalarTower.of_algHom a
  let : IsScalarTower K F L := IsScalarTower.of_algHom b
  let : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun x => by
    change a x = IsFractionRing.lift hv (algebraMap A F x)
    exact (IsFractionRing.lift_algebraMap hv x).symm
  let : Algebra.EssFiniteType F L := Algebra.EssFiniteType.of_comp K F L
  let : Algebra.FormallySmooth A F :=
    Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors A)
  let : Algebra.FormallySmooth A L := Algebra.FormallySmooth.comp A F L
  have hinj := mapBaseChange_injective_of_formallySmooth K A L
  have h := ((KaehlerDifferential.mvPolynomialBasis K ι).baseChange L).linearIndependent
  have h' := h.map' (KaehlerDifferential.mapBaseChange K A L)
    (LinearMap.ker_eq_bot.mpr hinj)
  convert h' using 1
  funext i
  simp only [Function.comp_apply, Module.Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply]
  change (D K L) (v i) = (mapBaseChange K A L) (1 ⊗ₜ[A] (D K A) (MvPolynomial.X i))
  rw [mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  congr 1
  exact (MvPolynomial.aeval_X v i).symm

/-- At a zero of a generic section, linearly independent evaluation rows give
linearly independent differentials. The result allows any number of bundle
components and any finite family of generating sections. -/
theorem section_differentials_linearIndependent [Algebra.EssFiniteType K L]
    [Fintype ι] {κ : Type*} (v : κ → ι → L) (a : ι → L)
    (hv : LinearIndependent L v) (ha : AlgebraicIndependent K a)
    (hzero : ∀ j, ∑ i, a i * v j i = 0) :
    LinearIndependent L (fun j => ∑ i, a i • D K L (v j i)) := by
  let T := Fintype.linearCombination L (fun i => D K L (a i))
  have hT : Function.Injective T :=
    (linearIndependent_iff_injective_fintypeLinearCombination).mp
      (algebraicIndependent_differentials a ha)
  have hnT : Function.Injective (-T) := by
    intro x y h
    exact hT (neg_injective h)
  have hlin := hv.map' (-T) (LinearMap.ker_eq_bot.mpr hnT)
  convert hlin using 1
  funext j
  change (∑ i, a i • D K L (v j i)) = -(∑ i, v j i • D K L (a i))
  apply eq_neg_iff_add_eq_zero.mpr
  have hd := congrArg (D K L) (hzero j)
  simpa only [map_sum, Derivation.leibniz, Finset.sum_add_distrib, map_zero] using hd

end PaperVerification.GenericSectionDifferentials
end
end
end TAF_LiteralSource_0624

section TAF_LiteralSource_0625
/- Original module: PaperVerification.GenericSectionCriticalLocus -/


/-!
# The parameter image of a critical incidence scheme

The evaluation matrix of a generated bundle has a right inverse on the affine
charts used here. A normalized nonzero relation between the differentials at a
common zero therefore forces an algebraic relation among the parameters.
Passing through the finitely many minimal primes produces one nonzero parameter
polynomial that vanishes nilpotently on the entire critical incidence scheme.

The minimal-prime argument adapts `incidence_polynomial` in OpenAI's public
`OAI/AlgebraicGeometry/Seshadri/Bertini/LinearFamilies.lean`, commit
`4eaee87548250b2682affda7d05d947c05554bae`, under Apache-2.0.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Matrix
open KaehlerDifferential

namespace PaperVerification.GenericSectionDifferentials

variable {K L A ι κ : Type*} [Field K] [CharZero K] [Field L] [Algebra K L]
  [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- A right inverse for the evaluation matrix proves independence of its rows. -/
theorem rows_linearIndependent_of_rightInverse
    (v : Matrix κ ι L) (u : Matrix ι κ L) (hvu : v*u=1) :
    LinearIndependent L v := by
  apply Matrix.vecMul_injective_iff.mp
  intro x y h
  have h' := congrArg (fun z => z ᵥ* u) h
  simpa only [Matrix.vecMul_vecMul, hvu, Matrix.vecMul_one] using h'

/-- A normalized relation between the section differentials forces an actual
nonzero polynomial relation among the coefficient parameters. -/
theorem critical_parameters_polynomial [Algebra.EssFiniteType K L]
    (v : Matrix κ ι L) (u : Matrix ι κ L) (hvu : v*u=1)
    (a : ι → L) (c : κ → L) (j₀ : κ) (hc : c j₀=1)
    (hzero : ∀ j, ∑ i, a i*v j i=0)
    (hcritical : ∑ j, c j • (∑ i, a i • D K L (v j i))=0) :
    ∃ p : MvPolynomial ι K, p≠0 ∧ MvPolynomial.aeval a p=0 := by
  have hdep : ¬ AlgebraicIndependent K a := by
    intro ha
    have hlin := section_differentials_linearIndependent v a
      (rows_linearIndependent_of_rightInverse v u hvu) ha hzero
    have hz := Fintype.linearIndependent_iff.mp hlin c hcritical
    exact one_ne_zero (hc.symm.trans (hz j₀))
  rw [algebraicIndependent_iff] at hdep
  push Not at hdep
  obtain ⟨p, hp, hne⟩ := hdep
  exact ⟨p, hne, hp⟩

variable [CommRing A] [Algebra K A]

/-- The critical equations descend to every field-valued point, including the
fraction fields of the irreducible components. -/
theorem critical_parameters_polynomial_image [Algebra.EssFiniteType K L]
    [Algebra A L] [IsScalarTower K A L]
    (v : Matrix κ ι A) (u : Matrix ι κ A) (hvu : v*u=1)
    (a : ι → A) (c : κ → A) (j₀ : κ) (hc : c j₀=1)
    (hzero : ∀ j, ∑ i, a i*v j i=0)
    (hcritical : ∑ j, c j • (∑ i, a i • D K A (v j i))=0) :
    ∃ p : MvPolynomial ι K, p≠0 ∧
      MvPolynomial.aeval (fun i => algebraMap A L (a i)) p=0 := by
  refine critical_parameters_polynomial (v.map (algebraMap A L))
    (u.map (algebraMap A L)) ?_ (fun i => algebraMap A L (a i))
    (fun j => algebraMap A L (c j)) j₀ ?_ ?_ ?_
  · simpa only [Matrix.map_mul, Matrix.map_one, map_zero, map_one] using
      congrArg (Matrix.map · (algebraMap A L)) hvu
  · simpa only [hc, map_one]
  · intro j
    simpa only [Matrix.map_apply, map_sum, map_mul, map_zero] using
      congrArg (algebraMap A L) (hzero j)
  · have h := congrArg (KaehlerDifferential.map K K A L) hcritical
    simpa only [map_sum, map_smul, KaehlerDifferential.map_D, map_zero,
      IsScalarTower.algebraMap_smul, Matrix.map_apply] using h

/-- A single nonzero parameter polynomial vanishes nilpotently on a finite-type
critical incidence algebra. No assumption that its points are reduced is used. -/
theorem critical_incidence_polynomial [Algebra.FiniteType K A]
    (v : Matrix κ ι A) (u : Matrix ι κ A) (hvu : v*u=1)
    (a : ι → A) (c : κ → A) (j₀ : κ) (hc : c j₀=1)
    (hzero : ∀ j, ∑ i, a i*v j i=0)
    (hcritical : ∑ j, c j • (∑ i, a i • D K A (v j i))=0) :
    ∃ p : MvPolynomial ι K, p≠0 ∧ IsNilpotent (MvPolynomial.aeval a p) := by
  classical
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  let Q := minimalPrimes A
  letI : Fintype Q := (minimalPrimes.finite_of_isNoetherianRing A).fintype
  have hf : ∀ q : Q, ∃ p : MvPolynomial ι K,
      p≠0 ∧ MvPolynomial.aeval a p ∈ q.val := by
    intro q
    letI : q.val.IsPrime := q.property.isPrime
    let B := A ⧸ q.val
    let F := FractionRing B
    letI : Algebra.EssFiniteType B F :=
      Algebra.EssFiniteType.of_isLocalization F (nonZeroDivisors B)
    letI : Algebra.EssFiniteType K F := Algebra.EssFiniteType.comp K B F
    obtain ⟨p,hp,he⟩ := critical_parameters_polynomial_image (L:=F)
      v u hvu a c j₀ hc hzero hcritical
    refine ⟨p,hp,?_⟩
    have he' : algebraMap A F (MvPolynomial.aeval a p)=0 := by
      change (IsScalarTower.toAlgHom K A F) (MvPolynomial.aeval a p)=0
      rw [MvPolynomial.comp_aeval_apply a (IsScalarTower.toAlgHom K A F)]
      exact he
    have hinj : Function.Injective (algebraMap B F) := IsFractionRing.injective B F
    rw [IsScalarTower.algebraMap_apply A B F] at he'
    have hq : algebraMap A B (MvPolynomial.aeval a p)=0 :=
      hinj (he'.trans (map_zero _).symm)
    exact Ideal.Quotient.eq_zero_iff_mem.mp hq
  choose p hp hm using hf
  refine ⟨∏ q : Q, p q, Finset.prod_ne_zero_iff.mpr (fun q _ => hp q), ?_⟩
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  letI : J.IsPrime := hJ
  obtain ⟨q,hq,hqJ⟩ :=
    Ideal.exists_minimalPrimes_le (I:=(⊥ : Ideal A)) (J:=J) bot_le
  simp only [map_prod]
  apply Ideal.IsPrime.prod_mem_iff.mpr
  exact ⟨⟨q,hq⟩, Finset.mem_univ _, hqJ (hm ⟨q,hq⟩)⟩

end PaperVerification.GenericSectionDifferentials
end
end
end TAF_LiteralSource_0625

section TAF_LiteralSource_0626
/- Original module: PaperVerification.UniversalCriticalSections -/


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
end
end
end TAF_LiteralSource_0626

section TAF_LiteralSource_0627
/- Original module: PaperVerification.MatrixRightInverseCriterion -/


/-!
# A global right inverse from independence in the residue fields

The proof uses the ideal of scalars `r` for which `A * B = r • 1` is solvable.
Modulo a maximal ideal, row independence supplies a right inverse. Lift that
matrix and multiply by the adjugate of its product with `A`: its determinant
belongs to the scalar ideal and is congruent to one modulo the maximal ideal.
Thus the scalar ideal is the unit ideal.

This avoids assuming a choice of pivot columns valid over the entire base.
-/

@[expose] public section
noncomputable section
open scoped Matrix

namespace PaperVerification.GenericSectionDifferentials

variable {R ι κ : Type*} [CommRing R] [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- Scalars admitting a matrix right inverse after multiplication by that scalar. -/
def rightInverseScalarIdeal (A : Matrix κ ι R) : Ideal R where
  carrier := {r | ∃ B : Matrix ι κ R, A * B = r • (1 : Matrix κ κ R)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro r s ⟨B,hB⟩ ⟨C,hC⟩
    exact ⟨B+C, by simp only [Matrix.mul_add,hB,hC,add_smul]⟩
  smul_mem' := by
    rintro r s ⟨B,hB⟩
    exact ⟨r • B, by simp only [Matrix.mul_smul,hB,smul_smul,smul_eq_mul]⟩

/-- Independent rows over every maximal residue field give a right inverse
over the original ring, including rings with nilpotents. -/
theorem matrix_rightInverse_of_residue_rows
    (A : Matrix κ ι R)
    (hA : ∀ (J : Ideal R) [J.IsMaximal],
      LinearIndependent (R ⧸ J) (A.map (Ideal.Quotient.mk J))) :
    ∃ B : Matrix ι κ R, A * B = 1 := by
  classical
  let I := rightInverseScalarIdeal A
  have hI : I = ⊤ := by
    by_contra hproper
    obtain ⟨J,hJ,hIJ⟩ := Ideal.exists_le_maximal I hproper
    letI : J.IsMaximal := hJ
    letI : Field (R ⧸ J) := Ideal.Quotient.field J
    let π := Ideal.Quotient.mk J
    have hrows : LinearIndependent (R ⧸ J) (A.map π).row := hA J
    obtain ⟨B,hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp
      hrows.mulVec_surjective
    choose C₀ hC using fun i j => Ideal.Quotient.mk_surjective (B i j)
    let C : Matrix ι κ R := C₀
    have hC' : C.map π = B := by
      ext i j
      exact hC i j
    let Q : Matrix κ κ R := A * C
    have hQ : Q.map π = 1 := by
      simpa only [Q,Matrix.map_mul,hC'] using hB
    have hdet : π Q.det = 1 := by
      rw [RingHom.map_det]
      change (Q.map π).det = 1
      rw [hQ,Matrix.det_one]
    have hmem : Q.det ∈ I := by
      refine ⟨C * Q.adjugate, ?_⟩
      rw [← Matrix.mul_assoc]
      exact Matrix.mul_adjugate Q
    have hz : π Q.det = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ hmem)
    exact one_ne_zero (hdet.symm.trans hz)
  have h1 : (1 : R) ∈ I := by rw [hI]; trivial
  obtain ⟨B,hB⟩ := h1
  exact ⟨B, by simpa only [one_smul] using hB⟩

end PaperVerification.GenericSectionDifferentials
end
end
end TAF_LiteralSource_0627

section TAF_LiteralSource_0628
/- Original module: PaperVerification.FormallySmoothRelations -/


/-!
# A differential criterion for a smooth zero scheme

This is the multi-equation version of the elementary cotangent splitting
argument. All modules and differentials are Mathlib's actual cotangent
modules. The hypotheses say that derivations dual to the defining equations
exist; they are precisely what a right inverse of the Jacobian supplies.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open KaehlerDifferential TensorProduct Algebra

namespace PaperVerification.GenericSectionDifferentials

/-- A finite family of defining equations with dual derivations gives a
formally smooth quotient of a formally smooth algebra. -/
theorem formallySmooth_of_dual_derivations
    {K S κ : Type*} [CommRing K] [CommRing S] [Algebra K S]
    [Fintype κ] [DecidableEq κ]
    (P : Algebra.Extension K S) [Algebra.FormallySmooth K P.Ring]
    (f : κ → P.Ring) (hf : Ideal.span (Set.range f) = P.ker)
    (δ : κ → Derivation K P.Ring S)
    (hδ : ∀ i j, δ i (f j) = if i=j then 1 else 0) :
    Algebra.FormallySmooth K S := by
  let g : κ → P.Cotangent := fun i => Extension.Cotangent.mk
    ⟨f i, hf ▸ Ideal.subset_span (Set.mem_range_self i)⟩
  let l : P.CotangentSpace →ₗ[S] P.Cotangent := ∑ i,
    (LinearMap.toSpanSingleton S P.Cotangent (g i)).comp
      (LinearMap.liftBaseChange S (δ i).liftKaehlerDifferential)
  apply P.formallySmooth_iff_split_injection.mpr
  refine ⟨l, ?_⟩
  have hspan : Submodule.span S (Set.range g) = ⊤ :=
    Extension.Cotangent.span_eq_top_of_span_eq_ker f hf
  apply LinearMap.ext_on_range hspan
  intro j
  simp [l, g, hδ]


/-- A right inverse of the actual Jacobian produces the dual derivations.
The ambient differential module is given a basis, as on an affine-space chart. -/
theorem formallySmooth_of_jacobian_rightInverse
    {K S κ τ : Type*} [CommRing K] [CommRing S] [Algebra K S]
    [Fintype κ] [DecidableEq κ] [Fintype τ]
    (P : Algebra.Extension K S) [Algebra.FormallySmooth K P.Ring]
    (b : Module.Basis τ P.Ring Ω[P.Ring⁄K])
    (f : κ → P.Ring) (hf : Ideal.span (Set.range f)=P.ker)
    (u : Matrix τ κ S)
    (hu : (show Matrix κ τ S from
      fun j t => algebraMap P.Ring S (b.repr (D K P.Ring (f j)) t)) * u=1) :
    Algebra.FormallySmooth K S := by
  let δ : κ → Derivation K P.Ring S := fun j =>
    (∑ t, u t j • ((Algebra.linearMap P.Ring S).comp (b.coord t))).compDer
      (D K P.Ring)
  apply formallySmooth_of_dual_derivations P f hf δ
  intro i j
  have h := congrFun (congrFun hu j) i
  change (∑ t, algebraMap P.Ring S (b.repr (D K P.Ring (f j)) t) * u t i) =
    if j=i then 1 else 0 at h
  simpa [δ, Module.Basis.coord_apply, mul_comm, eq_comm] using h

end PaperVerification.GenericSectionDifferentials
end
end
end TAF_LiteralSource_0628

section TAF_LiteralSource_0629
/- Original module: PaperVerification.GenericVectorSectionSmoothness -/


/-!
# Generic smoothness of a generated vector-valued section

On a smooth affine chart with a free differential module, a finite generating
family of sections is an evaluation matrix with a right inverse. We construct
a nonzero polynomial in its original parameters such that every specialization
outside its zero set has a smooth literal quotient ring.

No smoothness, reducedness, regular-sequence condition, or rank hypothesis on
the specialized zero scheme is assumed.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open KaehlerDifferential

namespace PaperVerification.GenericSectionDifferentials

variable {K R ι κ τ : Type*} [Field K] [CharZero K] [CommRing R]
  [Algebra K R] [Fintype ι] [Fintype κ] [Fintype τ] [DecidableEq κ]

/-- The original linear combination of the chosen generating sections. -/
def linearSection (v : Matrix κ ι R) (a : ι → K) (j : κ) : R :=
  ∑ i, a i • v j i

lemma linearSection_gradient (b : Module.Basis τ R Ω[R⁄K])
    (v : Matrix κ ι R) (a : ι → K) (j : κ) (t : τ) :
    b.repr (D K R (linearSection v a j)) t =
      ∑ i, a i • b.repr (D K R (v j i)) t := by
  simp only [linearSection,map_sum,Derivation.map_smul,Finset.sum_apply']
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun z => z t) (b.repr.toLinearMap.map_smul_of_tower (a i)
    (D K R (v j i)))

set_option backward.isDefEq.respectTransparency false in
/-- Every specialization outside the constructed nonempty principal open
cuts out a smooth affine zero scheme. The algebra is the actual ideal quotient
by the components of the original section. -/
theorem linearSection_quotient_smooth [Algebra.FiniteType K R]
    [Algebra.FormallySmooth K R]
    (b : Module.Basis τ R Ω[R⁄K]) (v : Matrix κ ι R)
    (u : Matrix ι κ R) (hvu : v * u = 1) (a : ι → K)
    (ha : MvPolynomial.aeval a (criticalAvoidancePolynomial b v u hvu) ≠ 0) :
    Algebra.Smooth K (R ⧸ Ideal.span (Set.range (linearSection v a))) := by
  classical
  let I := Ideal.span (Set.range (linearSection v a))
  let S := R ⧸ I
  let P := Algebra.Extension.ofSurjective (Ideal.Quotient.mkₐ K I)
    (Ideal.Quotient.mkₐ_surjective K I)
  let G : Matrix κ τ S := fun j t =>
    algebraMap R S (b.repr (D K R (linearSection v a j)) t)
  have hG : ∀ (J : Ideal S) [J.IsMaximal],
      LinearIndependent (S ⧸ J) (G.map (Ideal.Quotient.mk J)) := by
    intro J hJ
    let L := S ⧸ J
    letI : Field L := Ideal.Quotient.field J
    let χ : R →ₐ[K] L := (Ideal.Quotient.mkₐ K J).comp (Ideal.Quotient.mkₐ K I)
    let a' : ι → L := fun i => algebraMap K L (a i)
    have ha' : MvPolynomial.aeval a' (criticalAvoidancePolynomial b v u hvu) ≠ 0 := by
      have he : algebraMap K L (MvPolynomial.aeval a (criticalAvoidancePolynomial b v u hvu)) =
          MvPolynomial.aeval a' (criticalAvoidancePolynomial b v u hvu) := by
        simpa only [Algebra.ofId_apply,a'] using
          (MvPolynomial.comp_aeval_apply a (Algebra.ofId K L)
            (criticalAvoidancePolynomial b v u hvu))
      rw [← he]
      intro h
      exact ha ((algebraMap K L).injective (h.trans (map_zero _).symm))
    have hz : ∀ j, ∑ i, a' i * χ (v j i) = 0 := by
      intro j
      have hz' : algebraMap R S (linearSection v a j) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self j))
      have h : χ (linearSection v a j) = 0 := by
        change Ideal.Quotient.mk J (algebraMap R S (linearSection v a j)) = 0
        rw [hz',map_zero]
      simpa only [linearSection,map_sum,Algebra.smul_def,map_mul,AlgHom.commutes,a'] using h
    have hind := specialized_gradient_linearIndependent b v u hvu χ a' ha' hz
    convert hind using 1
    funext j t
    change χ (b.repr (D K R (linearSection v a j)) t) = _
    rw [linearSection_gradient]
    simp only [map_sum,a',Algebra.smul_def,map_mul,AlgHom.commutes]
  obtain ⟨U,hU⟩ := matrix_rightInverse_of_residue_rows G hG
  have hf : Ideal.span (Set.range (linearSection v a)) = P.ker := by
    exact Ideal.mk_ker.symm
  letI : Algebra.FormallySmooth K P.Ring :=
    inferInstanceAs (Algebra.FormallySmooth K R)
  have hs : Algebra.FormallySmooth K S :=
    formallySmooth_of_jacobian_rightInverse P b (linearSection v a) hf U hU
  letI : Algebra.FinitePresentation K S :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨hs, inferInstance⟩

/-- The good parameter locus has a rational point over the original field.
Characteristic zero is used through infinitude, as well as in the differential
argument that constructs its nonzero defining polynomial. -/
theorem exists_linearSection_smooth [Algebra.FiniteType K R]
    [Algebra.FormallySmooth K R]
    (b : Module.Basis τ R Ω[R⁄K]) (v : Matrix κ ι R)
    (u : Matrix ι κ R) (hvu : v * u = 1) :
    ∃ a : ι → K,
      MvPolynomial.aeval a (criticalAvoidancePolynomial b v u hvu) ≠ 0 ∧
      Algebra.Smooth K (R ⧸ Ideal.span (Set.range (linearSection v a))) := by
  classical
  letI : Infinite K := Infinite.of_injective Nat.cast Nat.cast_injective
  have hex : ∃ a : ι → K,
      MvPolynomial.aeval a (criticalAvoidancePolynomial b v u hvu) ≠ 0 := by
    by_contra h
    push Not at h
    apply criticalAvoidancePolynomial_ne_zero b v u hvu
    apply MvPolynomial.funext
    intro a
    simpa only [map_zero, MvPolynomial.aeval_eq_eval] using h a
  obtain ⟨a,ha⟩ := hex
  exact ⟨a,ha,linearSection_quotient_smooth b v u hvu a ha⟩

end PaperVerification.GenericSectionDifferentials
end
end
end TAF_LiteralSource_0629

