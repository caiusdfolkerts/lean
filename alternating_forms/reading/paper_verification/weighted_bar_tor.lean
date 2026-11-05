module

public import PaperVerification.WeightedBarDegrees
public import PaperVerification.WeightedBarEuler

/-!
# The original internal grading inside genuine augmentation Tor

Coefficient projections preserve the original homogeneous degree and split
actual subcomplex inclusions. The induced subspaces of ordinary Tor are
isomorphic to their actual internal-degree homology, and exhaust Tor.
No acyclicity or Koszulness premise is incorporated in their definitions.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.WeightedBar

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

end PaperVerification.WeightedBar

namespace PaperVerification.WeightedBar

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open PaperVerification.NoncommutativeBar PaperVerification.AugmentedAlgebraBasis

universe u
variable {K A I : Type u} [Field K] [Ring A] [Algebra K A]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)
  (δ : I → ℕ)
  (hδ : ∀ a b c,productCoefficients B a b c≠0 → δ c=δ a+δ b)

local notation "bar" => reducedComplex ε B hunit hε
local notation "internal" => internalComplex ε B hunit hε δ hδ

def internalInclusion (r N : ℕ) : piece (K := K) δ r N →ₗ[K] lengthPiece I K r :=
  Submodule.inclusion (by rw [piece_eq_inf]; exact inf_le_left)

theorem internalInclusion_differential (r N : ℕ) :
    (internalInclusion (K := K) δ r N).comp (internalDifferential B δ hδ r N)=
      (negativeReducedDegreeDifferential B r).comp (internalInclusion δ (r+1) N) := by
  apply LinearMap.ext
  intro z
  rfl

def inclusionChain (N : ℕ) : internal N ⟶ bar where
  f r := ModuleCat.ofHom (internalInclusion (K := K) δ r N)
  comm' i j hij := by
    change j+1=i at hij
    subst i
    rw [internalComplex_d,reducedComplex_d]
    apply ModuleCat.hom_ext
    exact (internalInclusion_differential B δ hδ j N).symm

theorem projection_mem_piece (r N : ℕ) (z : List I →₀ K)
    (hz : z∈lengthPiece I K r) : degreeProjection δ N z∈piece (K := K) δ r N := by
  intro L hL
  have hn := Finsupp.mem_support_iff.mp hL
  rw [degreeProjection_apply] at hn
  split_ifs at hn with hN
  · exact ⟨hz (Finsupp.mem_support_iff.mpr hn),hN⟩
  · exact False.elim (hn rfl)

def internalProjection (r N : ℕ) : lengthPiece I K r →ₗ[K] piece (K := K) δ r N :=
  LinearMap.codRestrict _ ((degreeProjection δ N).comp (lengthPiece I K r).subtype)
    (fun z ↦ projection_mem_piece δ r N z.val z.property)

@[simp] theorem internalProjection_val (r N : ℕ) (z : lengthPiece I K r) :
    (internalProjection δ r N z).val=degreeProjection δ N z.val := rfl

theorem internalProjection_inclusion (r N : ℕ) (z : piece (K := K) δ r N) :
    internalProjection δ r N (internalInclusion δ r N z)=z := by
  apply Subtype.ext
  have hz : z.val∈lengthPiece I K r ⊓ degreePiece δ N := by
    rw [←piece_eq_inf]
    exact z.property
  exact (degreeProjection_homogeneous δ N N z.val hz.2).trans (if_pos rfl)

include hδ in
theorem internalProjection_differential (r N : ℕ) :
    (internalProjection δ r N).comp (negativeReducedDegreeDifferential B r)=
      (internalDifferential B δ hδ r N).comp (internalProjection δ (r+1) N) := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change degreeProjection δ N (-PaperVerification.ReducedBarBasis.differential B z.val)=
    -PaperVerification.ReducedBarBasis.differential B (degreeProjection δ N z.val)
  rw [map_neg,differential_degreeProjection B δ hδ]

def projectionChain (N : ℕ) : bar ⟶ internal N where
  f r := ModuleCat.ofHom (internalProjection (K := K) δ r N)
  comm' i j hij := by
    change j+1=i at hij
    subst i
    rw [internalComplex_d,reducedComplex_d]
    apply ModuleCat.hom_ext
    exact (internalProjection_differential B δ hδ j N).symm

theorem chain_retraction (N : ℕ) :
    inclusionChain ε B hunit hε δ hδ N ≫ projectionChain ε B hunit hε δ hδ N=𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact internalProjection_inclusion δ r N z

theorem internalHomology_injective (r N : ℕ) :
    Function.Injective (homologyMap (inclusionChain ε B hunit hε δ hδ N) r) := by
  have he := congrArg (fun f ↦ homologyMap f r) (chain_retraction ε B hunit hε δ hδ N)
  rw [homologyMap_comp,homologyMap_id] at he
  apply Function.LeftInverse.injective
    (g := homologyMap (projectionChain ε B hunit hε δ hδ N) r)
  intro z
  exact congrArg (fun f ↦ f z) he

def internalTorMap (r N : ℕ) :
    (internal N).homology r ⟶ AugmentationCoinvariants.augmentationTor ε r :=
  homologyMap (inclusionChain ε B hunit hε δ hδ N) r ≫
    (ordinaryTorReducedBarIso ε B hunit hε r).inv

/-- The image of the original degree-N complex inside ordinary Tor. -/
def torPiece (r N : ℕ) : Submodule K (AugmentationCoinvariants.augmentationTor ε r) :=
  LinearMap.range (internalTorMap ε B hunit hε δ hδ r N).hom

theorem internalTorMap_injective (r N : ℕ) :
    Function.Injective (internalTorMap ε B hunit hε δ hδ r N) :=
  (ordinaryTorReducedBarIso ε B hunit hε r).toLinearEquiv.symm.injective.comp
    (internalHomology_injective ε B hunit hε δ hδ r N)

/-- This isomorphism proves that the grading images cannot discard any
nonzero internal homology class. -/
def internalTorEquiv (r N : ℕ) :
    (internal N).homology r ≃ₗ[K] torPiece ε B hunit hε δ hδ r N :=
  LinearEquiv.ofInjective (internalTorMap ε B hunit hε δ hδ r N).hom
    (internalTorMap_injective ε B hunit hε δ hδ r N)

theorem torPiece_eq_bot_iff (r N : ℕ) :
    torPiece ε B hunit hε δ hδ r N=⊥ ↔ IsZero ((internal N).homology r) := by
  constructor
  · intro h
    haveI : Subsingleton (torPiece ε B hunit hε δ hδ r N) := by rw [h]; infer_instance
    apply ModuleCat.isZero_iff_subsingleton.mpr
    exact ⟨fun x y ↦ (internalTorEquiv ε B hunit hε δ hδ r N).injective
      (Subsingleton.elim _ _)⟩
  · intro h
    have hm : internalTorMap ε B hunit hε δ hδ r N=0 := h.eq_of_src _ _
    rw [torPiece,hm,ModuleCat.hom_zero,LinearMap.range_zero]

def degreeEndomorphism (N : ℕ) : bar ⟶ bar :=
  projectionChain ε B hunit hε δ hδ N ≫ inclusionChain ε B hunit hε δ hδ N

theorem degreeCycles_value (r N : ℕ) (c : (bar).cycles r) :
    (((bar).iCycles r) (cyclesMap (degreeEndomorphism ε B hunit hε δ hδ N) r c)).val=
      degreeProjection δ N (((bar).iCycles r) c).val := by
  have he := congrArg (fun f ↦ f c) (cyclesMap_i (degreeEndomorphism ε B hunit hε δ hδ N) r)
  exact congrArg Subtype.val he

theorem sum_degreeCycles (r : ℕ) (c : (bar).cycles r) :
    (∑ N∈(((bar).iCycles r) c).val.support.image (totalDegree δ),
      cyclesMap (degreeEndomorphism ε B hunit hε δ hδ N) r c)=c := by
  apply (ModuleCat.mono_iff_injective ((bar).iCycles r)).mp inferInstance
  rw [map_sum]
  apply Subtype.ext
  rw [Submodule.coe_sum]
  simp_rw [degreeCycles_value]
  exact sum_degreeProjection δ (((bar).iCycles r) c).val

/-- Every ordinary Tor class is a finite sum of classes in the original
internal degrees. The actual grading images exhaust the whole group. -/
theorem torPieces_iSup (r : ℕ) : (⨆ N,torPiece ε B hunit hε δ hδ r N)=⊤ := by
  apply top_unique
  intro x hx
  obtain ⟨c,hc⟩ := (ModuleCat.epi_iff_surjective ((bar).homologyπ r)).mp inferInstance
    ((ordinaryTorReducedBarIso ε B hunit hε r).hom x)
  let S := (((bar).iCycles r) c).val.support.image (totalDegree δ)
  have hsum :
      (∑ N∈S,(ordinaryTorReducedBarIso ε B hunit hε r).inv
        (((bar).homologyπ r) (cyclesMap (degreeEndomorphism ε B hunit hε δ hδ N) r c)))=x := by
    calc
      _ = (ordinaryTorReducedBarIso ε B hunit hε r).inv (((bar).homologyπ r)
          (∑ N∈S,cyclesMap (degreeEndomorphism ε B hunit hε δ hδ N) r c)) := by
        rw [map_sum,map_sum]
      _ = (ordinaryTorReducedBarIso ε B hunit hε r).inv (((bar).homologyπ r) c) := by
        rw [sum_degreeCycles]
      _ = x := by
        rw [hc]
        exact congrArg (fun f ↦ f x) (ordinaryTorReducedBarIso ε B hunit hε r).hom_inv_id
  rw [←hsum]
  apply Submodule.sum_mem
  intro N hN
  apply (le_iSup (fun N ↦ torPiece ε B hunit hε δ hδ r N) N)
  refine ⟨homologyMap (projectionChain ε B hunit hε δ hδ N) r (((bar).homologyπ r) c),?_⟩
  change (ordinaryTorReducedBarIso ε B hunit hε r).inv
    (homologyMap (inclusionChain ε B hunit hε δ hδ N) r
      (homologyMap (projectionChain ε B hunit hε δ hδ N) r (((bar).homologyπ r) c)))=_
  apply congrArg (ordinaryTorReducedBarIso ε B hunit hε r).inv
  have he := congrArg (fun f ↦ f c)
    (homologyπ_naturality (degreeEndomorphism ε B hunit hε δ hδ N) r)
  simpa only [degreeEndomorphism,homologyMap_comp,ModuleCat.comp_apply] using he

/-- Ordinary Tor concentration with its independently specified original
generator degrees. This definition does not posit any dimension formula. -/
def HasDiagonalTor : Prop :=
  ∀ r N,r≠N → torPiece ε B hunit hε δ hδ r N=⊥

theorem hasDiagonalTor_iff : HasDiagonalTor ε B hunit hε δ hδ ↔
    ∀ r N,r≠N → IsZero ((internal N).homology r) := by
  simp only [HasDiagonalTor,torPiece_eq_bot_iff]

/-- The necessary Hilbert identity follows from the real ordinary-Tor
concentration property and finite Euler--Poincare in each internal degree. -/
theorem one_add_mul_signed_diagonalTor [Fintype I] (hpos : ∀ i,0<δ i)
    (hKoszul : HasDiagonalTor ε B hunit hε δ hδ) :
    (1+positiveSeries δ)*WeightedBarEuler.diagonalHomologySeries internal=1 := by
  apply WeightedBarEuler.one_add_mul_diagonalHomologySeries_of_boundary_zero
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact positiveSeries_constantCoeff δ hpos
  · intro N r hr
    change Module.Finite K (piece (K := K) δ r N)
    infer_instance
  · exact internalComplex_top_differential ε B hunit hε δ hδ hpos
  · intro N r hr
    exact internalComplex_term_rank ε B hunit hε δ hδ r N
  · intro N r hr hne
    exact (hasDiagonalTor_iff ε B hunit hε δ hδ).mp hKoszul r N hne

end PaperVerification.WeightedBar
