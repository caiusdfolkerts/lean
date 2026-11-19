module

public import PaperVerification.HomogeneousLocalization
public import TauCeti.RingTheory.CohenMacaulay.RegularSequence
public import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay
public import TauCeti.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field

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
