module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-!
# Descending homogeneous regularity from the origin

Localization at the origin is not faithfully flat on all polynomial modules.
This file proves the precise homogeneous argument needed here. A homogeneous
polynomial belonging to a homogeneous ideal after localization already belongs
before localization, since the denominator has nonzero constant coefficient.
Applying that statement to every homogeneous component descends regularity.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open MvPolynomial RingTheory.Sequence

namespace PaperVerification.HomogeneousLocalization

variable {K ι : Type*} [Field K]
local notation "P" => MvPolynomial ι K
attribute [local instance] MvPolynomial.weightedGradedAlgebra

def originIdeal : Ideal P := RingHom.ker (constantCoeff : P →+* K)

instance originIdeal_isMaximal : (originIdeal (K := K) (ι := ι)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, constantCoeff_C ι c⟩)

abbrev OriginLocalRing := Localization.AtPrime (originIdeal (K := K) (ι := ι))

@[simp] theorem mem_originIdeal (f : P) :
    f ∈ originIdeal (K := K) (ι := ι) ↔ constantCoeff f = 0 := Iff.rfl

theorem coe_decompose_eq_component (w : ι → ℕ) (f : P) (d : ℕ) :
    (DirectSum.decompose (weightedHomogeneousSubmodule K w) f d : P) =
      weightedHomogeneousComponent w d f := by
  exact weightedDecomposition.decompose'_apply K w f d

theorem component_mul_of_left_homogeneous (w : ι → ℕ) (f g : P) (e d : ℕ)
    (hf : f.IsWeightedHomogeneous w e) :
    weightedHomogeneousComponent w (e + d) (f * g) =
      f * weightedHomogeneousComponent w d g := by
  simpa only [coe_decompose_eq_component] using
    (DirectSum.coe_decompose_mul_add_of_left_mem
      (weightedHomogeneousSubmodule K w) (j := d) hf (b := g))

theorem component_mul_of_right_homogeneous (w : ι → ℕ) (s f : P) (d : ℕ)
    (hw : ∀ i, w i ≠ 0) (hf : f.IsWeightedHomogeneous w d) :
    weightedHomogeneousComponent w d (s * f) = C (s.coeff 0) * f := by
  have h := DirectSum.coe_decompose_mul_add_of_right_mem
    (weightedHomogeneousSubmodule K w) (i := 0) hf (a := s)
  simpa only [zero_add, coe_decompose_eq_component, weightedHomogeneousComponent_zero s hw] using h

/-- Clearing a denominator with nonzero constant term cannot introduce a
homogeneous polynomial into a homogeneous ideal. -/
theorem homogeneous_mem_of_constant_mul_mem (w : ι → ℕ) (hw : ∀ i, w i ≠ 0)
    (I : Ideal P) (hI : I.IsHomogeneous (weightedHomogeneousSubmodule K w))
    (f s : P) (d : ℕ) (hf : f.IsWeightedHomogeneous w d)
    (hs : s.coeff 0 ≠ 0) (hsf : s * f ∈ I) : f ∈ I := by
  have hc : C (s.coeff 0) * f ∈ I := by
    have h := hI d hsf
    rw [coe_decompose_eq_component, component_mul_of_right_homogeneous w s f d hw hf] at h
    exact h
  have hu : IsUnit (C (s.coeff 0) : P) := (isUnit_iff_ne_zero.mpr hs).map C
  exact (Ideal.unit_mul_mem_iff_mem I hu).mp hc

/-- The needed saturation statement is only asserted for homogeneous elements. -/
theorem homogeneous_mem_of_localized (w : ι → ℕ) (hw : ∀ i, w i ≠ 0)
    (I : Ideal P) (hI : I.IsHomogeneous (weightedHomogeneousSubmodule K w))
    (f : P) (d : ℕ) (hf : f.IsWeightedHomogeneous w d)
    (hloc : algebraMap P (OriginLocalRing (K := K) (ι := ι)) f ∈
      I.map (algebraMap P (OriginLocalRing (K := K) (ι := ι)))) : f ∈ I := by
  obtain ⟨s, hs, hsf⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (originIdeal (K := K) (ι := ι)).primeCompl
    (OriginLocalRing (K := K) (ι := ι)) I f).mp hloc
  apply homogeneous_mem_of_constant_mul_mem w hw I hI f s d hf _ hsf
  simpa only [Ideal.mem_primeCompl_iff, mem_originIdeal, constantCoeff_eq] using hs

/-- Regularity modulo a homogeneous ideal descends from localization at the
origin, with every homogeneous component checked separately. -/
theorem regular_of_localized (w : ι → ℕ) (hw : ∀ i, w i ≠ 0)
    (I : Ideal P) (hI : I.IsHomogeneous (weightedHomogeneousSubmodule K w))
    (f : P) (e : ℕ) (hf : f.IsWeightedHomogeneous w e)
    (hreg : IsSMulRegular
      (OriginLocalRing (K := K) (ι := ι) ⧸
        I.map (algebraMap P (OriginLocalRing (K := K) (ι := ι))))
      (algebraMap P (OriginLocalRing (K := K) (ι := ι)) f)) :
    IsSMulRegular (P ⧸ I) f := by
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem I f).mpr
  intro g hfg
  change f * g ∈ I at hfg
  apply hI.mem_iff.mpr
  intro d
  rw [coe_decompose_eq_component]
  apply homogeneous_mem_of_localized w hw I hI _ d
    (weightedHomogeneousComponent_isWeightedHomogeneous d g)
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mp hreg
  change algebraMap P (OriginLocalRing (K := K) (ι := ι)) f *
    algebraMap P (OriginLocalRing (K := K) (ι := ι))
      (weightedHomogeneousComponent w d g) ∈ _
  rw [← map_mul]
  apply Ideal.mem_map_of_mem
  have hc := hI (e + d) hfg
  rwa [coe_decompose_eq_component, component_mul_of_left_homogeneous w f g e d hf] at hc

/-- A homogeneous sequence is weakly regular as soon as its image at the
origin is weakly regular. No global faithful-flatness assertion is used. -/
theorem sequence_regular_of_localized (w : ι → ℕ) (hw : ∀ i, w i ≠ 0)
    (rs : List P) (hhom : ∀ f ∈ rs, ∃ d, f.IsWeightedHomogeneous w d)
    (hreg : IsWeaklyRegular (OriginLocalRing (K := K) (ι := ι))
      (rs.map (algebraMap P (OriginLocalRing (K := K) (ι := ι))))) :
    IsWeaklyRegular P rs := by
  constructor
  intro i hi
  let I : Ideal P := Ideal.ofList (rs.take i)
  have hI : I.IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    apply Ideal.homogeneous_span
    intro f hf
    obtain ⟨d, hd⟩ := hhom f (List.mem_of_mem_take hf)
    exact ⟨d, hd⟩
  obtain ⟨d, hd⟩ := hhom rs[i] (List.getElem_mem hi)
  have hloc := hreg.regular_mod_prev i (by simpa only [List.length_map] using hi)
  have hprev :
      (Ideal.ofList ((rs.map (algebraMap P (OriginLocalRing (K := K) (ι := ι)))).take i) •
        (⊤ : Submodule (OriginLocalRing (K := K) (ι := ι))
          (OriginLocalRing (K := K) (ι := ι)))) =
      I.map (algebraMap P (OriginLocalRing (K := K) (ι := ι))) := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top, ← List.map_take, ← Ideal.map_ofList]
  rw [hprev] at hloc
  have hloc' : IsSMulRegular
      (OriginLocalRing (K := K) (ι := ι) ⧸
        I.map (algebraMap P (OriginLocalRing (K := K) (ι := ι))))
      (algebraMap P (OriginLocalRing (K := K) (ι := ι)) rs[i]) := by
    simpa only [List.getElem_map] using hloc
  have hprev' : (Ideal.ofList (rs.take i) • (⊤ : Submodule P P)) = I := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  rw [hprev']
  exact regular_of_localized w hw I hI rs[i] d hd hloc'

end PaperVerification.HomogeneousLocalization
