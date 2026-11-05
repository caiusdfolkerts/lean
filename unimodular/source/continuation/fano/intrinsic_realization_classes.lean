module

public import Continuation.Fano.ActualBoundaryMatroid
public import Continuation.Fano.ActualBoundaryCartierCoefficients
public import Continuation.RegularMatroid.SchemeRegularity

/-!
# Fano realization among independently supplied split toric varieties

The variety in the class predicate is an arbitrary scheme over the given field,
with its actual dense equivariant open torus. No fan, polytope presentation or
classification is part of its data. Its canonical sheaf is defined from the
ordinary universal Kähler sheaf, and its matroid from actual codimension-one
boundary character valuations.

For the UT-free condition, a Cartier representative of the intrinsic line
bundle is required to be supported on the actual torus boundary. Its polytope
uses its genuine Weil coefficients and the genuine character valuations. This
is the ordinary toric Cartier-polytope definition; the construction proves the
unit-coefficient formula rather than using it to define the anticanonical bundle.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace Unimodular.IntrinsicRealizationClasses

open AlgebraicGeometry CategoryTheory MonoidalCategory MonObj
open PaperVerification.ToricSchemes PaperVerification.ToricGeometry
open Unimodular.NefBig Unimodular.Projectivity
open scoped BigOperators Matroid

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

/-- The intrinsic internal-Hom dual of the actual top Kähler sheaf. -/
def intrinsicAnticanonical (X : Over (Spec (CommRingCat.of k))) (n : ℕ) : X.left.Modules :=
  (topDifferentialSheaf k X.left n).dual

/-- An independently given smooth projective split toric Fano variety.
All geometric conditions concern its actual scheme, structural morphism,
ordinary sheaves, and group-scheme action. -/
structure SmoothProjectiveFanoToric (n : ℕ) where
  scheme : Over (Spec (CommRingCat.of k))
  action : ModObj (splitTorusOver k (Fin n → ℤ)) scheme
  torus : @SplitToricEmbedding k _ n scheme action
  integral : IsIntegral scheme.left
  smooth : Smooth scheme.hom
  proper : IsProper scheme.hom
  projective : ∃ Index : Type u, Finite Index ∧
    ∃ e : scheme.left ⟶ Proj (MvPolynomial.homogeneousSubmodule Index k),
      IsClosedImmersion e ∧ e ≫ polynomialProjectiveToSpec k Index = scheme.hom
  dimension : topologicalKrullDim scheme.left = n
  ample : IsAmpleModule (intrinsicAnticanonical k scheme n)

namespace SmoothProjectiveFanoToric

variable {k} {n : ℕ} (D : SmoothProjectiveFanoToric k n)

local instance : ModObj (splitTorusOver k (Fin n → ℤ)) D.scheme := D.action
local instance : IsIntegral D.scheme.left := D.integral
local instance : Smooth D.scheme.hom := D.smooth
local instance : IsProper D.scheme.hom := D.proper
local instance : IsLocallyNoetherian D.scheme.left :=
  LocallyOfFiniteType.isLocallyNoetherian D.scheme.hom

/-- Ordinary deletion and contraction on all genuine boundary-prime labels. -/
def HasBoundaryMinor {E : Type*} (M : Matroid E) : Prop :=
  ∃ f : M.E ↪ D.torus.BoundaryPrime,
    (M.restrictSubtype M.E).mapEmbedding f ≤m D.torus.actualBoundaryMatroid

def IsUniformlyUnimodular : Prop :=
  IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) D.torus.boundaryValuation

/-- An ordinary invertible sheaf whose ordinary tensor power is the intrinsic
anticanonical sheaf. The root is not required to be torus invariant. -/
def HasAnticanonicalTensorRoot (d : ℕ) : Prop :=
  ∃ L : D.scheme.left.Modules,
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible D.scheme.left L ∧
      Nonempty (intrinsicAnticanonical k D.scheme n ≅ tensorSheafPower L d)

/-- The usual polytope of a Cartier representative supported on the torus
boundary, using actual valuations and actual Weil coefficients. -/
def cartierPolytope (C : CartierData D.scheme.left) : Set (Ambient n) :=
  {x | ∀ p : D.torus.BoundaryPrime,
    -(C.weilCoefficient p.val : ℝ) ≤
      ∑ i, (D.torus.boundaryValuation p i : ℝ) * x i}

/-- UT-freeness of the actual anticanonical Cartier polytope. The displayed
isomorphism makes the underlying line bundle explicit. -/
def AnticanonicalPolytopeUTFree : Prop :=
  ∃ C : CartierData D.scheme.left,
    Nonempty (intrinsicAnticanonical k D.scheme n ≅ C.sheaf) ∧
    (∀ x ∈ D.torus.torusOpen, C.weilCoefficient x = 0) ∧
    ∀ S : Set (Ambient n), IsExtreme ℝ (D.cartierPolytope C) S →
      ¬ SegmentSimplex.IsUnimodularTriangle S

theorem rational_of_boundaryMinor {E : Type*} (M : Matroid E) [M.Finite]
    (h : D.HasBoundaryMinor M) : RepresentationBridge.RepresentableOnGround ℚ M := by
  obtain ⟨f, hf⟩ := h
  exact D.torus.rational_of_actualBoundaryMinor M f hf

theorem regular_of_uniform_boundaryMinor {E : Type*} (M : Matroid E) [M.Finite]
    (hU : D.IsUniformlyUnimodular) (h : D.HasBoundaryMinor M) :
    RegularRepresentation.RegularOnGround M := by
  obtain ⟨f, hf⟩ := h
  exact (RegularRepresentation.regularOnGround_iff_rationalTU M).mpr
    (D.torus.regular_of_uniform_actualBoundaryMinor hU M f hf)

end SmoothProjectiveFanoToric

variable {k} {n : ℕ}
    (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)

local instance fanOverIntegral : IsIntegral (F.fanSchemeOver k).left := by
  change IsIntegral (F.fanScheme k)
  infer_instance

local instance fanOverNoetherian : IsLocallyNoetherian (F.fanSchemeOver k).left := by
  change IsLocallyNoetherian (F.fanScheme k)
  infer_instance

/-- Both presentations use the same structural morphism and the same
ordinary top Kaehler sheaf on the original scheme. -/
theorem intrinsicAnticanonical_fan :
    intrinsicAnticanonical k (F.fanSchemeOver k) n =
      (anticanonicalLineBundle F k).obj := by
  rw [intrinsicAnticanonical, anticanonicalLineBundle,
    TauCeti.AlgebraicGeometry.InvertibleSheaf.dual_obj]
  rfl

/-- Forgetting the constructed fan retains a genuine member of the unrestricted
scheme class. No fan is stored in that class. -/
def ofFan (h : SchemeRealizationClasses.IsSmoothProjectiveFanoFan F k) :
    SmoothProjectiveFanoToric k n where
  scheme := F.fanSchemeOver k
  action := inferInstance
  torus := F.intrinsicToricEmbedding k
  integral := h.1
  smooth := h.2.1
  proper := h.2.2.1
  projective := h.2.2.2.1
  dimension := h.2.2.2.2.1
  ample := by
    rw [intrinsicAnticanonical_fan F]
    exact h.2.2.2.2.2.1

theorem ofFan_hasBoundaryMinor {E : Type*} (M : Matroid E)
    (hF : SchemeRealizationClasses.IsSmoothProjectiveFanoFan F k)
    (hM : SchemeRealizationClasses.HasRayMinor M F) :
    (ofFan F hF).HasBoundaryMinor M := by
  letI : IsProper (F.fanSchemeStructureMap k) := hF.2.2.1
  exact F.actualBoundaryMinor_of_rayMinor k M hM

theorem ofFan_uniform
    (hF : SchemeRealizationClasses.IsSmoothProjectiveFanoFan F k)
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) (fun v : F.rays ↦ v.val)) :
    (ofFan F hF).IsUniformlyUnimodular := by
  letI : IsProper (F.fanSchemeStructureMap k) := hF.2.2.1
  exact F.uniform_actualBoundary_of_uniform_rays k hU

theorem ofFan_tensorRoot
    (hF : SchemeRealizationClasses.IsSmoothProjectiveFanoFan F k) (d : ℕ)
    (hroot : SchemeRealizationClasses.HasAnticanonicalTensorRoot F k d) :
    (ofFan F hF).HasAnticanonicalTensorRoot d := by
  change ∃ L : (F.fanScheme k).Modules,
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible (F.fanScheme k) L ∧
      Nonempty (intrinsicAnticanonical k (F.fanSchemeOver k) n ≅ tensorSheafPower L d)
  rw [intrinsicAnticanonical_fan F]
  exact hroot

theorem ofFan_unitCartierPolytope
    (hF : SchemeRealizationClasses.IsSmoothProjectiveFanoFan F k) :
    (ofFan F hF).cartierPolytope (F.fanCartierData k F.isPure (fun _ ↦ 1)) =
      F.fanPolytope (fun _ ↦ 1) := by
  ext x
  change (∀ p : (F.intrinsicToricEmbedding k).BoundaryPrime,
    -((F.fanCartierData k F.isPure (fun _ ↦ 1)).weilCoefficient p.val : ℝ) ≤
      ∑ i, ((F.intrinsicToricEmbedding k).boundaryValuation p i : ℝ) * x i) ↔ _
  constructor
  · intro h u hu
    obtain ⟨p, hp⟩ := F.exists_boundaryPrime_valuation k u hu
    have h' := h p
    rw [F.fanCartier_weilCoefficient_boundary, hp] at h'
    simpa [dotProductEquiv, dotProduct, PaperVerification.ToricGeometry.embed] using h'
  · intro h p
    rw [F.fanCartier_weilCoefficient_boundary]
    simpa [dotProductEquiv, dotProduct, PaperVerification.ToricGeometry.embed] using
      h _ (F.boundaryValuation_mem_rays k p)

theorem ofFan_UTFree
    (hF : SchemeRealizationClasses.IsSmoothProjectiveFanoFan F k)
    (hUT : SchemeRealizationClasses.AnticanonicalPolytopeUTFree F) :
    (ofFan F hF).AnticanonicalPolytopeUTFree := by
  refine ⟨F.fanCartierData k F.isPure (fun _ ↦ 1), ?_, ?_, ?_⟩
  · refine ⟨?_⟩
    exact eqToIso (intrinsicAnticanonical_fan F) ≪≫ anticanonical_unitBoundaryIso F k
  · intro x hx
    apply F.fanCartier_weilCoefficient_off_boundary k (fun _ ↦ 1) x
    exact fun h ↦ h hx
  · intro S hS
    rw [ofFan_unitCartierPolytope F hF] at hS
    exact hUT S hS

/-- Full Corollary 5.2 over the class of independently given split toric
varieties, with literal all-fields regularity and ordinary boundary minors. -/
theorem corollary_5_2 {E : Type*} (M : Matroid E) [M.Finite]
    (k : Type u) [Field k] :
    RegularRepresentation.RegularOnGround M ↔
      ∃ n : ℕ, ∃ D : SmoothProjectiveFanoToric k n,
        D.IsUniformlyUnimodular ∧ D.HasBoundaryMinor M := by
  constructor
  · intro hM
    obtain ⟨n, _, F, hF, hU, hminor⟩ :=
      (SchemeRealizationClasses.corollary_5_2_all_fields M k).mp hM
    exact ⟨n, ofFan F hF, ofFan_uniform F hF hU,
      ofFan_hasBoundaryMinor F M hF hminor⟩
  · rintro ⟨n, D, hU, hminor⟩
    exact D.regular_of_uniform_boundaryMinor M hU hminor

/-- Full Corollary 5.3 for each prescribed integer `d ≥ 2`, with an actual
ordinary tensor root and an actual UT-free anticanonical Cartier polytope. -/
theorem corollary_5_3 {E : Type*} (M : Matroid E) [M.Finite]
    (k : Type u) [Field k] (d : ℤ) (hd : 2 ≤ d) :
    RepresentationBridge.RepresentableOnGround ℚ M ↔
      ∃ q : ℕ, (q : ℤ) = d ∧
        ∃ n : ℕ, ∃ D : SmoothProjectiveFanoToric k n,
          D.HasBoundaryMinor M ∧ D.HasAnticanonicalTensorRoot q ∧
            D.AnticanonicalPolytopeUTFree := by
  constructor
  · intro hM
    obtain ⟨q, hq, n, _, F, hF, hminor, hroot, hUT⟩ :=
      (SchemeRealizationClasses.corollary_5_3 M k d hd).mp hM
    exact ⟨q, hq, n, ofFan F hF, ofFan_hasBoundaryMinor F M hF hminor,
      ofFan_tensorRoot F hF q hroot, ofFan_UTFree F hF hUT⟩
  · rintro ⟨q, _, n, D, hminor, _⟩
    exact D.rational_of_boundaryMinor M hminor

#print axioms SmoothProjectiveFanoToric.rational_of_boundaryMinor
#print axioms SmoothProjectiveFanoToric.regular_of_uniform_boundaryMinor
#print axioms ofFan_unitCartierPolytope
#print axioms corollary_5_2
#print axioms corollary_5_3

end Unimodular.IntrinsicRealizationClasses
