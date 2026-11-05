module

public import Continuation.Fano.ActualBoundaryMatroid

/-!
# The exact intrinsic ray ground and its full fan-matroid identification

The ground consists of the actual integral boundary valuation vectors.
The range equality gives a bijection with every original fan ray, and the
full represented matroid is preserved under that ground equivalence.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricGeometry
open scoped BigOperators Matroid

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]
    (T : SplitToricEmbedding k n X)

local instance raySetNoetherian : IsLocallyNoetherian X.left :=
  LocallyOfFiniteType.isLocallyNoetherian X.hom

/-- All genuine integral boundary valuation vectors, with their literal
vector values as the ground elements. -/
def valuationRaySet : Set (Lattice n) := Set.range T.boundaryValuation

/-- The vector matroid on the exact intrinsic ray set. -/
def valuationRayMatroid : Matroid T.valuationRaySet :=
  Unimodular.VectorMatroid.ofFamily (K := ℝ)
    (fun v ↦ Unimodular.embed v.val)

theorem finite_valuationRaySet : Finite T.valuationRaySet := by
  letI : Finite T.BoundaryPrime := T.finite_boundaryPrime
  exact (Set.finite_range T.boundaryValuation).to_subtype

theorem valuationRaySet_integral_annihilator (m : Lattice n)
    (hm : ∀ v : T.valuationRaySet, ∑ i, v.val i * m i = 0) : m = 0 := by
  apply T.boundaryValuation_integral_annihilator m
  intro p
  exact hm ⟨T.boundaryValuation p, ⟨p, rfl⟩⟩

theorem rational_of_valuationRayMinor {E : Type*} (M : Matroid E) [M.Finite]
    (f : M.E ↪ T.valuationRaySet)
    (hf : (M.restrictSubtype M.E).mapEmbedding f ≤m T.valuationRayMatroid) :
    Unimodular.RepresentationBridge.RepresentableOnGround ℚ M := by
  letI : Finite T.valuationRaySet := T.finite_valuationRaySet
  letI : Fintype T.valuationRaySet := Fintype.ofFinite _
  exact Unimodular.RepresentationBridge.integer_ray_minor_ground_representable
    (fun v : T.valuationRaySet ↦ v.val) M f hf

theorem regular_of_uniform_valuationRayMinor
    (hU : Unimodular.IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun v : T.valuationRaySet ↦ v.val))
    {E : Type*} (M : Matroid E) [M.Finite] (f : M.E ↪ T.valuationRaySet)
    (hf : (M.restrictSubtype M.E).mapEmbedding f ≤m T.valuationRayMatroid) :
    Unimodular.RepresentationBridge.RegularOnGround M := by
  letI : Finite T.valuationRaySet := T.finite_valuationRaySet
  letI : Fintype T.valuationRaySet := Fintype.ofFinite _
  exact Unimodular.RepresentationBridge.regular_of_uniform_integer_ray_minor
    (fun v : T.valuationRaySet ↦ v.val) hU
    T.valuationRaySet_integral_annihilator M f hf

end PaperVerification.ToricSchemes.SplitToricEmbedding

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes
open Unimodular Unimodular.SchemeRealizationClasses
open scoped Matroid

variable {n : ℕ} (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)
    (k : Type u) [Field k] [IsProper (F.fanSchemeStructureMap k)]

local instance exactRayProper : IsProper (F.fanSchemeOver k).hom := by
  change IsProper (F.fanSchemeStructureMap k)
  infer_instance

local instance exactRayIntegral : IsIntegral (F.fanSchemeOver k).left := by
  change IsIntegral (F.fanScheme k)
  infer_instance

local instance exactRayNoetherian : IsLocallyNoetherian (F.fanSchemeOver k).left := by
  change IsLocallyNoetherian (F.fanScheme k)
  infer_instance

/-- Equality of the actual vector sets gives a bijection of the full ray
ground sets, preserving every vector exactly. -/
def intrinsicRayEquiv : F.rays ≃ (F.intrinsicToricEmbedding k).valuationRaySet :=
  Set.equivOfEq (F.boundaryValuation_range k).symm

@[simp] theorem intrinsicRayEquiv_val (v : F.rays) :
    (F.intrinsicRayEquiv k v).val = v.val := rfl

@[simp] theorem intrinsicRayEquiv_symm_val
    (v : (F.intrinsicToricEmbedding k).valuationRaySet) :
    ((F.intrinsicRayEquiv k).symm v).val = v.val := rfl

/-- The entire original ray matroid, after the displayed ground bijection,
is exactly the intrinsic ray-set matroid of the same scheme. -/
theorem rayMatroid_map_intrinsicRayEquiv :
    (rayMatroid F).mapEmbedding (F.intrinsicRayEquiv k).toEmbedding =
      (F.intrinsicToricEmbedding k).valuationRayMatroid := by
  have hrange : Set.range (F.intrinsicRayEquiv k).toEmbedding = Set.univ :=
    Set.range_eq_univ.mpr (F.intrinsicRayEquiv k).surjective
  change (VectorMatroid.ofFamily (K := ℝ) (fun v : F.rays ↦ Unimodular.embed v.val)).mapEmbedding
      (F.intrinsicRayEquiv k).toEmbedding =
    VectorMatroid.ofFamily (K := ℝ)
      (fun v : (F.intrinsicToricEmbedding k).valuationRaySet ↦ Unimodular.embed v.val)
  rw [VectorMatroid.ofFamily_mapEmbedding_eq_onSet
    (fun v : F.rays ↦ Unimodular.embed v.val)
    (fun v : (F.intrinsicToricEmbedding k).valuationRaySet ↦ Unimodular.embed v.val)
    (F.intrinsicRayEquiv k).toEmbedding (by intro v; rfl), hrange]
  rfl

theorem valuationRayMinor_of_rayMinor {E : Type*} (M : Matroid E)
    (hM : HasRayMinor M F) :
    ∃ f : M.E ↪ (F.intrinsicToricEmbedding k).valuationRaySet,
      (M.restrictSubtype M.E).mapEmbedding f ≤m
        (F.intrinsicToricEmbedding k).valuationRayMatroid := by
  obtain ⟨f, hf⟩ := hM
  let e := (F.intrinsicRayEquiv k).toEmbedding
  refine ⟨f.trans e, ?_⟩
  rw [← BoundaryMinorTransport.map_comp,
    ← F.rayMatroid_map_intrinsicRayEquiv k]
  obtain ⟨C, D, hCD⟩ := hf
  refine ⟨e '' C, e '' D, ?_⟩
  rw [hCD, BoundaryMinorTransport.map_delete_image,
    BoundaryMinorTransport.map_contract_image]

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.valuationRaySet_integral_annihilator
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.rayMatroid_map_intrinsicRayEquiv
