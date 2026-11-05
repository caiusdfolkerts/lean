module

public import PaperVerification.AlternatingFormsOddBarExactness

/-!
# The internal pieces inside ordinary Tor

The degree projections below are coefficient projections for the actual
internal polynomial degrees. They commute with the genuine bar
differential, split its internal subcomplexes, and sum to every tensor.
The induced subspaces of ordinary Mathlib Tor therefore come from the
original grading. Off-diagonal vanishing is then a statement about these
actual Tor subspaces, not merely an unrelated combinatorial complex.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.AlternatingForms.BarDegrees

open PaperVerification.ReducedBarBasis PaperVerification.AugmentedAlgebraBasis

variable {K A C : Type*} [CommRing K] [Ring A] [Algebra K A]
  (B : Module.Basis (Option C) K A) (δ : C → ℕ)

def degreeProjection (N : ℕ) : (List C →₀ K) →ₗ[K] (List C →₀ K) where
  toFun z := z.filter (fun L ↦ totalDegree δ L=N)
  map_add' z w := Finsupp.filter_add
  map_smul' a z := Finsupp.filter_smul

@[simp] theorem degreeProjection_apply (N : ℕ) (z : List C →₀ K) (L : List C) :
    degreeProjection δ N z L=if totalDegree δ L=N then z L else 0 := rfl

theorem degreeProjection_single (N : ℕ) (L : List C) (c : K) :
    degreeProjection δ N (Finsupp.single L c)=
      if totalDegree δ L=N then Finsupp.single L c else 0 := by
  change (Finsupp.single L c).filter (fun T => totalDegree δ T=N)=
    if totalDegree δ L=N then Finsupp.single L c else 0
  by_cases h : totalDegree δ L=N
  · rw [if_pos h]
    exact Finsupp.filter_single_of_pos (fun T => totalDegree δ T=N) h
  · rw [if_neg h]
    exact Finsupp.filter_single_of_neg (fun T => totalDegree δ T=N) h

theorem degreeProjection_homogeneous (N M : ℕ) (z : List C →₀ K)
    (hz : z∈degreePiece δ M) :
    degreeProjection δ N z=if M=N then z else 0 := by
  by_cases h : M=N
  · subst M
    rw [if_pos rfl]
    apply (Finsupp.filter_eq_self_iff _ _).mpr
    intro L hL
    exact hz (Finsupp.mem_support_iff.mpr hL)
  · rw [if_neg h]
    apply (Finsupp.filter_eq_zero_iff _ _).mpr
    intro L hL
    apply (Finsupp.mem_supported' K z).mp hz
    intro hM
    exact h (hM.symm.trans hL)

variable (hδ : ∀ a b c,productCoefficients B a b c≠0 → δ c=δ a+δ b)

include hδ in
theorem differential_degreeProjection (N : ℕ) (z : List C →₀ K) :
    differential B (degreeProjection δ N z)=degreeProjection δ N (differential B z) := by
  have he : (differential B).comp (degreeProjection δ N)=
      (degreeProjection δ N).comp (differential B) := by
    apply Finsupp.lhom_ext
    intro L c
    simp only [LinearMap.comp_apply,degreeProjection_single,differential_single,map_smul]
    rw [degreeProjection_homogeneous δ N (totalDegree δ L) _
      (differentialBasis_mem_degreePiece B δ hδ L)]
    split_ifs <;> simp only [differential_single,map_zero,smul_zero]
  exact LinearMap.congr_fun he z

/-- Finite completeness of the internal-degree projections on every
actual tensor. No finite-degree bound on the entire bar term is assumed. -/
theorem sum_degreeProjection (z : List C →₀ K) :
    (∑ N∈z.support.image (totalDegree δ),degreeProjection δ N z)=z := by
  apply Finsupp.ext
  intro L
  change (Finsupp.applyAddHom L) (∑ N∈z.support.image (totalDegree δ),degreeProjection δ N z)=z L
  rw [map_sum]
  change (∑ N∈z.support.image (totalDegree δ),if totalDegree δ L=N then z L else 0)=z L
  rw [Finset.sum_eq_single (totalDegree δ L)]
  · rw [if_pos rfl]
  · intro N hN hne
    exact if_neg (Ne.symm hne)
  · intro hnot
    rw [if_pos rfl]
    by_contra hL
    exact hnot (Finset.mem_image.mpr ⟨L,Finsupp.mem_support_iff.mpr hL,rfl⟩)

end PaperVerification.AlternatingForms.BarDegrees

namespace PaperVerification.AlternatingForms

open BarCompositions BarDegrees PaperVerification.ReducedBarBasis
open CategoryTheory CategoryTheory.Limits

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

theorem oddDegreeProjection_mem_internalDegree (r N : ℕ) (z : List C →₀ K)
    (hz : z∈BarFree.lengthPiece C K r) :
    degreeProjection δ N z∈internalDegreePiece (K := K) e r N := by
  intro L hL
  have hn := Finsupp.mem_support_iff.mp hL
  rw [degreeProjection_apply] at hn
  split_ifs at hn with hN
  · exact ⟨hz (Finsupp.mem_support_iff.mpr hn),
      by rw [oddBarWord_length_eq_degree]; exact hN⟩
  · exact False.elim (hn rfl)

def oddInternalDegreeProjection (r N : ℕ) :
    BarFree.lengthPiece C K r →ₗ[K] internalDegreePiece (K := K) e r N :=
  LinearMap.codRestrict _
    ((degreeProjection δ N).comp (BarFree.lengthPiece C K r).subtype)
    (fun z ↦ oddDegreeProjection_mem_internalDegree k t hs r N z.val z.property)

@[simp] theorem oddInternalDegreeProjection_val (r N : ℕ)
    (z : BarFree.lengthPiece C K r) :
    (oddInternalDegreeProjection k t hs r N z).val=degreeProjection δ N z.val := rfl

theorem oddInternalDegreeProjection_inclusion (r N : ℕ)
    (z : internalDegreePiece (K := K) e r N) :
    oddInternalDegreeProjection k t hs r N (oddInternalDegreeInclusion k t hs r N z)=z := by
  apply Subtype.ext
  have hz : z.val ∈ BarFree.lengthPiece C K r ⊓ degreePiece δ N :=
    (congrArg (fun U : Submodule K (List C →₀ K) => z.val ∈ U)
      (oddInternalDegreePiece_eq_inf (K := K) k t hs r N)).mp z.property
  exact (degreeProjection_homogeneous δ N N z.val hz.2).trans (if_pos rfl)

theorem oddInternalDegreeProjection_differential (r N : ℕ) :
    (oddInternalDegreeProjection k t hs r N).comp (BarFree.negativeReducedDegreeDifferential B r)=
      (oddBigradedDifferential k t hs r N).comp
        (oddInternalDegreeProjection k t hs (r+1) N) := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change degreeProjection δ N (-differential B z.val)=
    -differential B (degreeProjection δ N z.val)
  rw [map_neg,differential_degreeProjection B δ (odd_productCoefficient_degree k t hs)]

def oddInternalDegreeProjectionChain (N : ℕ) :
    ordinaryBar ⟶ oddInternalDegreeComplex (K := K) k t hs N where
  f r := ModuleCat.ofHom (oddInternalDegreeProjection k t hs r N)
  comm' i j hij := by
    change j+1=i at hij
    subst i
    rw [oddInternalDegreeComplex_d,BarFree.reducedComplex_d]
    apply ModuleCat.hom_ext
    exact (oddInternalDegreeProjection_differential k t hs j N).symm

theorem oddInternalDegree_chain_retraction (N : ℕ) :
    oddInternalDegreeInclusionChain (K := K) k t hs N ≫
      oddInternalDegreeProjectionChain k t hs N=𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact oddInternalDegreeProjection_inclusion k t hs r N z

/-- The actual ordinary Tor subspace induced by internal degree N in
the original graded free bar resolution. -/
def oddTorInternalPiece (r N : ℕ) : Submodule K (BarFree.TorOverCoefficients ε r) :=
  LinearMap.range
    ((HomologicalComplex.homologyMap (oddInternalDegreeInclusionChain k t hs N) r ≫
      (oddNormalizedBarTorIso k t hs r).inv).hom)

theorem oddTorInternalPiece_eq_bot_of_ne (r N : ℕ) (hr : r≠N) :
    oddTorInternalPiece (K := K) k t hs r N=⊥ := by
  have hz := odd_actual_bar_homology_diagonal (K := K) k t hs r N hr
  have hmap : HomologicalComplex.homologyMap (oddInternalDegreeInclusionChain k t hs N) r ≫
      (oddNormalizedBarTorIso k t hs r).inv=0 := hz.eq_of_src _ _
  rw [oddTorInternalPiece,hmap,ModuleCat.hom_zero,LinearMap.range_zero]

/-- Internal degree is recovered injectively inside ordinary Tor, since
projection followed by inclusion is a retraction already on complexes. -/
theorem oddInternalHomology_injective (r N : ℕ) :
    Function.Injective
      (HomologicalComplex.homologyMap (oddInternalDegreeInclusionChain (K := K) k t hs N) r) := by
  have he := congrArg (fun f ↦ HomologicalComplex.homologyMap f r)
    (oddInternalDegree_chain_retraction (K := K) k t hs N)
  rw [HomologicalComplex.homologyMap_comp,HomologicalComplex.homologyMap_id] at he
  apply Function.LeftInverse.injective
    (g := HomologicalComplex.homologyMap (oddInternalDegreeProjectionChain k t hs N) r)
  intro z
  exact congrArg (fun f ↦ f z) he

end PaperVerification.AlternatingForms
