module

public import PaperVerification.AlternatingFormsOddTorDegrees

/-!
# Ordinary Tor is concentrated in its actual internal degree

Every bar tensor is the finite sum of its internal-degree projections.
The same decomposition holds on actual cycles and therefore on ordinary
Tor. Together with off-diagonal exactness, this identifies the genuine
internal-degree subspaces: the diagonal is all of Tor and every other
degree is zero. This is the homological concentration assertion, with
the original quotient, augmentation, and polynomial grading retained.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.AlternatingForms

open BarCompositions BarDegrees
open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u
variable {K : Type u} [Field K] [CharZero K]
  (k t : ℕ) (hs : t+2≤k+1)

local notation "C" => OddPositiveStandardIndex (K := K) k t hs
local notation "B" => oddAugmentedBasis (K := K) k t hs
local notation "e" => oddPositiveWordEquiv (K := K) k t hs
local notation "δ" => oddPositiveDegree (K := K) k t hs
local notation "ε" => oddAugmentation (K := K) k t
local notation "ordinaryBar" => BarFree.reducedComplex ε B
  (oddAugmentedBasis_none k t hs) (oddAugmentation_positive k t hs)

def oddDegreeEndomorphism (N : ℕ) : ordinaryBar ⟶ ordinaryBar :=
  oddInternalDegreeProjectionChain (K := K) k t hs N ≫ oddInternalDegreeInclusionChain (K := K) k t hs N

theorem oddDegreeEndomorphism_f_val (r N : ℕ) (z : BarFree.lengthPiece C K r) :
    ((oddDegreeEndomorphism (K := K) k t hs N).f r z).val=degreeProjection δ N z.val := rfl

theorem oddDegreeCycles_value (r N : ℕ) (c : (ordinaryBar).cycles r) :
    (((ordinaryBar).iCycles r) (cyclesMap (oddDegreeEndomorphism (K := K) k t hs N) r c)).val=
      degreeProjection δ N (((ordinaryBar).iCycles r) c).val := by
  have he := congrArg (fun f ↦ f c) (cyclesMap_i (oddDegreeEndomorphism (K := K) k t hs N) r)
  exact congrArg Subtype.val he

theorem sum_oddDegreeCycles (r : ℕ) (c : (ordinaryBar).cycles r) :
    (∑ N∈(((ordinaryBar).iCycles r) c).val.support.image (totalDegree δ),
      cyclesMap (oddDegreeEndomorphism (K := K) k t hs N) r c)=c := by
  apply (ModuleCat.mono_iff_injective ((ordinaryBar).iCycles r)).mp inferInstance
  rw [map_sum]
  apply Subtype.ext
  rw [Submodule.coe_sum]
  simp_rw [oddDegreeCycles_value]
  exact sum_degreeProjection δ (((ordinaryBar).iCycles r) c).val

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Completeness of the original internal grading on the actual Tor
group. This rules out a vacuous selection of purported degree pieces. -/
theorem oddTorInternalPieces_iSup (r : ℕ) :
    (⨆ N,oddTorInternalPiece (K := K) k t hs r N)=⊤ := by
  apply top_unique
  intro x hx
  obtain ⟨c,hc⟩ :=
    (ModuleCat.epi_iff_surjective ((ordinaryBar).homologyπ r)).mp inferInstance
      ((oddNormalizedBarTorIso (K := K) k t hs r).hom x)
  let S := (((ordinaryBar).iCycles r) c).val.support.image (totalDegree δ)
  have hsum :
      (∑ N∈S,(oddNormalizedBarTorIso (K := K) k t hs r).inv
        (((ordinaryBar).homologyπ r) (cyclesMap (oddDegreeEndomorphism (K := K) k t hs N) r c)))=x := by
    calc
      _ = (oddNormalizedBarTorIso (K := K) k t hs r).inv (((ordinaryBar).homologyπ r)
          (∑ N∈S,cyclesMap (oddDegreeEndomorphism (K := K) k t hs N) r c)) := by
        rw [map_sum,map_sum]
      _ = (oddNormalizedBarTorIso (K := K) k t hs r).inv (((ordinaryBar).homologyπ r) c) := by
        rw [sum_oddDegreeCycles]
      _ = x := by
        rw [hc]
        exact congrArg (fun f ↦ f x) (oddNormalizedBarTorIso (K := K) k t hs r).hom_inv_id
  rw [←hsum]
  apply Submodule.sum_mem
  intro N hN
  apply (le_iSup (fun N ↦ oddTorInternalPiece (K := K) k t hs r N) N)
  refine ⟨homologyMap (oddInternalDegreeProjectionChain (K := K) k t hs N) r
    (((ordinaryBar).homologyπ r) c),?_⟩
  change (oddNormalizedBarTorIso (K := K) k t hs r).inv
    (homologyMap (oddInternalDegreeInclusionChain (K := K) k t hs N) r
      (homologyMap (oddInternalDegreeProjectionChain (K := K) k t hs N) r
        (((ordinaryBar).homologyπ r) c)))=_
  apply congrArg (oddNormalizedBarTorIso (K := K) k t hs r).inv
  have he := congrArg (fun f ↦ f c)
    (homologyπ_naturality (oddDegreeEndomorphism (K := K) k t hs N) r)
  simpa only [oddDegreeEndomorphism,homologyMap_comp,ModuleCat.comp_apply] using he

theorem oddTorInternalPiece_diagonal (r : ℕ) :
    oddTorInternalPiece (K := K) k t hs r r=⊤ := by
  have hle : (⨆ N,oddTorInternalPiece (K := K) k t hs r N)≤
      oddTorInternalPiece (K := K) k t hs r r := by
    apply iSup_le
    intro N
    by_cases h : N=r
    · subst N
      exact le_rfl
    · rw [oddTorInternalPiece_eq_bot_of_ne (K := K) k t hs r N (Ne.symm h)]
      exact bot_le
  rw [oddTorInternalPieces_iSup] at hle
  exact top_unique hle

/-- The actual Tor concentration assertion for every homological and
internal degree of the original odd isotropic Plucker ring. -/
theorem odd_actual_Tor_internal_degree (r N : ℕ) :
    oddTorInternalPiece (K := K) k t hs r N=if N=r then ⊤ else ⊥ := by
  by_cases h : N=r
  · subst N
    rw [if_pos rfl,oddTorInternalPiece_diagonal]
  · rw [if_neg h,oddTorInternalPiece_eq_bot_of_ne (K := K) k t hs r N (Ne.symm h)]

end PaperVerification.AlternatingForms
