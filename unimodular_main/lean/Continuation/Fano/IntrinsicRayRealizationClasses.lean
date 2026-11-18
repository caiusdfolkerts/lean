module

public import Continuation.Fano.IntrinsicRealizationClasses
public import Continuation.Fano.IntrinsicRayGround

/-!
# Fano realizations on the exact intrinsic ray ground

The ray ground is the set of actual integral boundary valuation vectors.
It is distinct from the set of boundary-prime labels. For a constructed fan,
the proved equality of this set with the original primitive ray set gives
an equivalence of the whole ambient ray matroids. No injectivity of an
unrelated boundary labeling is assumed.

The final statements quantify independently supplied smooth projective
split toric Fano varieties, ordinary minors on the complete input ground,
all-fields regularity, and every prescribed integer tensor index at least two.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace Unimodular.IntrinsicRealizationClasses.SmoothProjectiveFanoToric

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes
open PaperVerification.ToricGeometry
open scoped Matroid

variable {k : Type u} [Field k] {n : ℕ} (D : SmoothProjectiveFanoToric k n)

local instance : ModObj (splitTorusOver k (Fin n → ℤ)) D.scheme := D.action
local instance : IsIntegral D.scheme.left := D.integral
local instance : Smooth D.scheme.hom := D.smooth
local instance : IsProper D.scheme.hom := D.proper
local instance : IsLocallyNoetherian D.scheme.left :=
  LocallyOfFiniteType.isLocallyNoetherian D.scheme.hom

def HasRayMinor {E : Type*} (M : Matroid E) : Prop :=
  ∃ f : M.E ↪ D.torus.valuationRaySet,
    (M.restrictSubtype M.E).mapEmbedding f ≤m D.torus.valuationRayMatroid

def IsUniformlyUnimodularRaySet : Prop :=
  IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
    (fun v : D.torus.valuationRaySet ↦ v.val)

theorem rational_of_rayMinor {E : Type*} (M : Matroid E) [M.Finite]
    (hM : D.HasRayMinor M) : RepresentationBridge.RepresentableOnGround ℚ M := by
  obtain ⟨f, hf⟩ := hM
  exact D.torus.rational_of_valuationRayMinor M f hf

theorem regular_of_uniform_rayMinor {E : Type*} (M : Matroid E) [M.Finite]
    (hU : D.IsUniformlyUnimodularRaySet) (hM : D.HasRayMinor M) :
    RegularRepresentation.RegularOnGround M := by
  obtain ⟨f, hf⟩ := hM
  exact (RegularRepresentation.regularOnGround_iff_rationalTU M).mpr
    (D.torus.regular_of_uniform_valuationRayMinor hU M f hf)

end Unimodular.IntrinsicRealizationClasses.SmoothProjectiveFanoToric

namespace Unimodular.IntrinsicRayRealizationClasses

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes PaperVerification.ToricGeometry
open Unimodular.IntrinsicRealizationClasses
open scoped Matroid

variable {k : Type u} [Field k] {n : ℕ}
    (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)

theorem ofFan_hasRayMinor {E : Type*} (M : Matroid E)
    (hF : SchemeRealizationClasses.IsSmoothProjectiveFanoFan F k)
    (hM : SchemeRealizationClasses.HasRayMinor M F) :
    (ofFan F hF).HasRayMinor M := by
  letI : IsProper (F.fanSchemeStructureMap k) := hF.2.2.1
  exact F.valuationRayMinor_of_rayMinor k M hM

theorem ofFan_uniformRaySet
    (hF : SchemeRealizationClasses.IsSmoothProjectiveFanoFan F k)
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) (fun v : F.rays ↦ v.val)) :
    (ofFan F hF).IsUniformlyUnimodularRaySet := by
  letI : IsProper (F.fanSchemeStructureMap k) := hF.2.2.1
  intro a
  simpa only [Function.comp_def, F.intrinsicRayEquiv_symm_val] using
    hU (fun i ↦ (F.intrinsicRayEquiv k).symm (a i))

/-- Corollary 5.2 on the exact intrinsic ray sets of arbitrary smooth
projective split toric Fano varieties. -/
theorem corollary_5_2 {E : Type*} (M : Matroid E) [M.Finite]
    (k : Type u) [Field k] :
    RegularRepresentation.RegularOnGround M ↔
      ∃ n : ℕ, ∃ D : SmoothProjectiveFanoToric k n,
        D.IsUniformlyUnimodularRaySet ∧ D.HasRayMinor M := by
  constructor
  · intro hM
    obtain ⟨n, _, F, hF, hU, hminor⟩ :=
      (SchemeRealizationClasses.corollary_5_2_all_fields M k).mp hM
    exact ⟨n, ofFan F hF, ofFan_uniformRaySet F hF hU,
      ofFan_hasRayMinor F M hF hminor⟩
  · rintro ⟨n, D, hU, hminor⟩
    exact D.regular_of_uniform_rayMinor M hU hminor

/-- Corollary 5.3 on the exact intrinsic ray sets, for every prescribed
integer index at least two and an ordinary invertible tensor root. -/
theorem corollary_5_3 {E : Type*} (M : Matroid E) [M.Finite]
    (k : Type u) [Field k] (d : ℤ) (hd : 2 ≤ d) :
    RepresentationBridge.RepresentableOnGround ℚ M ↔
      ∃ q : ℕ, (q : ℤ) = d ∧
        ∃ n : ℕ, ∃ D : SmoothProjectiveFanoToric k n,
          D.HasRayMinor M ∧ D.HasAnticanonicalTensorRoot q ∧
            D.AnticanonicalPolytopeUTFree := by
  constructor
  · intro hM
    obtain ⟨q, hq, n, _, F, hF, hminor, hroot, hUT⟩ :=
      (SchemeRealizationClasses.corollary_5_3 M k d hd).mp hM
    exact ⟨q, hq, n, ofFan F hF, ofFan_hasRayMinor F M hF hminor,
      ofFan_tensorRoot F hF q hroot, ofFan_UTFree F hF hUT⟩
  · rintro ⟨q, _, n, D, hminor, _⟩
    exact D.rational_of_rayMinor M hminor

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.rayMatroid_map_intrinsicRayEquiv
#print axioms corollary_5_2
#print axioms corollary_5_3

end Unimodular.IntrinsicRayRealizationClasses
