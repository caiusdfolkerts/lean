module

public import Continuation.Fano.ActualBoundaryRayDictionary
public import Continuation.Fano.IntrinsicBoundaryNecessity
public import Continuation.Fano.SchemeRealizationClasses

/-!
# The actual boundary matroid contains the original ray matroid

The labels on the boundary side are actual codimension-one points of the
constructed scheme. We select one such point for each ray, prove equality of
their actual valuations, and transport ordinary matroid minors through the
resulting restriction. No assumed fan/variety classification occurs.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace Unimodular.BoundaryMinorTransport
open Set
open scoped Matroid
variable {α β γ : Type*}
@[simp] theorem map_dual (M : Matroid α) (f : α ↪ β) :
    (M.mapEmbedding f)✶ = M✶.mapEmbedding f := by
  simp only [Matroid.mapEmbedding, Matroid.map_dual]

theorem map_comp (M : Matroid α) (f : α ↪ β) (g : β ↪ γ) :
    (M.mapEmbedding f).mapEmbedding g = M.mapEmbedding (f.trans g) := by
  apply Matroid.ext_indep
  · simp only [Matroid.mapEmbedding_ground_eq, Set.image_image]
    rfl
  · intro I hI
    simp only [Matroid.mapEmbedding, Matroid.map_indep_iff]
    constructor
    · rintro ⟨J, ⟨K, hK, rfl⟩, rfl⟩
      exact ⟨K, hK, by rw [Set.image_image]; rfl⟩
    · rintro ⟨K, hK, rfl⟩
      exact ⟨f '' K, ⟨K, hK, rfl⟩, by rw [Set.image_image]; rfl⟩

theorem map_injective (f : α ↪ β) :
    Function.Injective (fun M : Matroid α => M.mapEmbedding f) := by
  intro M N h
  have hh := congrArg (fun L : Matroid β => L.comap f) h
  simpa only [Matroid.mapEmbedding, Matroid.comap_map f.injective] using hh

theorem map_delete (M : Matroid α) (f : α ↪ β) (D : Set β) :
    M.mapEmbedding f ＼ D = (M ＼ (f ⁻¹' D)).mapEmbedding f := by
  apply Matroid.ext_indep
  · ext x
    simp only [Matroid.delete_ground, Matroid.mapEmbedding_ground_eq,
      Set.mem_sdiff, Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hd⟩
      exact ⟨y, ⟨hy, hd⟩, rfl⟩
    · rintro ⟨y, ⟨hy, hd⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, hd⟩
  · intro I hI
    rw [Matroid.delete_indep_iff, Matroid.mapEmbedding_indep_iff,
      Matroid.mapEmbedding_indep_iff, Matroid.delete_indep_iff]
    constructor
    · rintro ⟨⟨hi, hr⟩, hd⟩
      exact ⟨⟨hi, Set.disjoint_left.2 (fun x hx hxD =>
        Set.disjoint_left.1 hd hx hxD)⟩, hr⟩
    · rintro ⟨⟨hi, hd⟩, hr⟩
      refine ⟨⟨hi, hr⟩, Set.disjoint_left.2 ?_⟩
      intro x hx hxD
      obtain ⟨y, rfl⟩ := hr hx
      exact Set.disjoint_left.1 hd hx hxD

theorem map_delete_image (M : Matroid α) (f : α ↪ β) (D : Set α) :
    (M ＼ D).mapEmbedding f = M.mapEmbedding f ＼ (f '' D) := by
  rw [map_delete, Set.preimage_image_eq _ f.injective]

theorem map_contract (M : Matroid α) (f : α ↪ β) (C : Set β) :
    M.mapEmbedding f ／ C = (M ／ (f ⁻¹' C)).mapEmbedding f := by
  apply Matroid.dual_inj.1
  simp only [Matroid.dual_contract, map_dual, map_delete]

theorem map_contract_image (M : Matroid α) (f : α ↪ β) (C : Set α) :
    (M ／ C).mapEmbedding f = M.mapEmbedding f ／ (f '' C) := by
  rw [map_contract, Set.preimage_image_eq _ f.injective]


end Unimodular.BoundaryMinorTransport

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open Unimodular Unimodular.SchemeRealizationClasses
open PaperVerification.ToricSchemes
open scoped BigOperators Matroid

variable {n : ℕ} (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)
    (k : Type u) [Field k]

variable [IsProper (F.fanSchemeStructureMap k)]

local instance boundaryMatroidProper : IsProper (F.fanSchemeOver k).hom := by
  change IsProper (F.fanSchemeStructureMap k)
  infer_instance

local instance boundaryMatroidIntegral : IsIntegral (F.fanSchemeOver k).left := by
  change IsIntegral (F.fanScheme k)
  infer_instance

local instance boundaryMatroidNoetherian : IsLocallyNoetherian (F.fanSchemeOver k).left := by
  change IsLocallyNoetherian (F.fanScheme k)
  infer_instance

/-- Each original ray is represented by a genuine boundary prime divisor. -/
def boundaryRayEmbedding : F.rays ↪ (F.intrinsicToricEmbedding k).BoundaryPrime where
  toFun v := (F.exists_boundaryPrime_valuation k v.val v.property).choose
  inj' := by
    intro v w h
    apply Subtype.ext
    calc
      v.val = (F.intrinsicToricEmbedding k).boundaryValuation
          ((F.exists_boundaryPrime_valuation k v.val v.property).choose) :=
        (F.exists_boundaryPrime_valuation k v.val v.property).choose_spec.symm
      _ = (F.intrinsicToricEmbedding k).boundaryValuation
          ((F.exists_boundaryPrime_valuation k w.val w.property).choose) := congrArg _ h
      _ = w.val := (F.exists_boundaryPrime_valuation k w.val w.property).choose_spec

@[simp] theorem boundaryRayEmbedding_valuation (v : F.rays) :
    (F.intrinsicToricEmbedding k).boundaryValuation (F.boundaryRayEmbedding k v) = v.val :=
  (F.exists_boundaryPrime_valuation k v.val v.property).choose_spec

/-- The relabelled ray matroid is literally a restriction of the actual
boundary matroid, with loops, parallel elements and original labels retained. -/
theorem rayMatroid_map_boundary_eq_restrict :
    (rayMatroid F).mapEmbedding (F.boundaryRayEmbedding k) =
      (F.intrinsicToricEmbedding k).actualBoundaryMatroid ↾
        Set.range (F.boundaryRayEmbedding k) := by
  rw [rayMatroid, VectorMatroid.ofFamily_mapEmbedding_eq_onSet
    (fun v : F.rays ↦ Unimodular.embed v.val)
    (fun q ↦ Unimodular.embed ((F.intrinsicToricEmbedding k).boundaryValuation q))
    (F.boundaryRayEmbedding k) (by intro v; rw [F.boundaryRayEmbedding_valuation k])]
  exact (VectorMatroid.restrict_onSet
    (fun q ↦ Unimodular.embed ((F.intrinsicToricEmbedding k).boundaryValuation q))
    (Set.subset_univ _)).symm

/-- The original ray matroid is an ordinary deletion minor of the actual
boundary matroid. -/
theorem rayMatroid_map_boundary_isMinor :
    (rayMatroid F).mapEmbedding (F.boundaryRayEmbedding k) ≤m
      (F.intrinsicToricEmbedding k).actualBoundaryMatroid := by
  rw [F.rayMatroid_map_boundary_eq_restrict k]
  refine ⟨∅, (Set.range (F.boundaryRayEmbedding k))ᶜ, ?_⟩
  simp [Matroid.delete_eq_restrict, SplitToricEmbedding.actualBoundaryMatroid]

/-- Every ordinary minor witness on the original rays gives an ordinary
minor witness on the genuine boundary points of the same scheme. -/
theorem actualBoundaryMinor_of_rayMinor {E : Type*} (M : Matroid E)
    (h : HasRayMinor M F) :
    ∃ f : M.E ↪ (F.intrinsicToricEmbedding k).BoundaryPrime,
      (M.restrictSubtype M.E).mapEmbedding f ≤m
        (F.intrinsicToricEmbedding k).actualBoundaryMatroid := by
  obtain ⟨f, hf⟩ := h
  let g := F.boundaryRayEmbedding k
  refine ⟨f.trans g, ?_⟩
  rw [← BoundaryMinorTransport.map_comp]
  apply Matroid.IsMinor.trans _ (F.rayMatroid_map_boundary_isMinor k)
  obtain ⟨C, D, hCD⟩ := hf
  refine ⟨g '' C, g '' D, ?_⟩
  rw [hCD, BoundaryMinorTransport.map_delete_image,
    BoundaryMinorTransport.map_contract_image]

/-- Uniform unimodularity is preserved on the entire actual boundary
family, including all possible repeated labels. -/
theorem uniform_actualBoundary_of_uniform_rays
    (h : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun v : F.rays ↦ v.val)) :
    IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (F.intrinsicToricEmbedding k).boundaryValuation := by
  intro a
  exact h (fun i ↦ ⟨(F.intrinsicToricEmbedding k).boundaryValuation (a i),
    F.boundaryValuation_mem_rays k (a i)⟩)

#print axioms rayMatroid_map_boundary_eq_restrict
#print axioms actualBoundaryMinor_of_rayMinor
#print axioms uniform_actualBoundary_of_uniform_rays

end PaperVerification.ToricGeometry.SmoothCompleteFan

