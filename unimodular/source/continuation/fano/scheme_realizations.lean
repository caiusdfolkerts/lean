module

public import Continuation.Runtime.RegularClosure
public import Continuation.Divisor.FanoClosure

/-!
# Actual smooth projective Fano realizations of finite matroids

This file composes the ordinary-matroid construction with the actual fan
scheme. Its ray matroid is indexed by the primitive rays of that scheme's
fan. The ample sheaf is the intrinsic dual canonical bundle. Divisibility
means an isomorphism with an ordinary tensor power, and the absence of
unimodular triangular faces is asserted for the actual anticanonical
section polytope, including the reflection in the divisor convention.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

universe u

namespace Unimodular.SchemeRealizations

open Set AlgebraicGeometry CategoryTheory
open Unimodular.NefBig Unimodular.Projectivity
open scoped Matroid

variable {E : Type*} {n : ℕ}

/-- The actual primitive-ray matroid of the fan of the constructed scheme. -/
def rayMatroid (P : SmoothReflexivePresentation n) : Matroid P.schemeFan.rays :=
  VectorMatroid.ofFamily (K := ℝ) (fun u : P.schemeFan.rays ↦ embed u.val)

/-- An ordinary deletion/contraction minor, retaining the input's actual ground set. -/
def HasRayMinor (M : Matroid E) (P : SmoothReflexivePresentation n) : Prop :=
  ∃ f : M.E ↪ P.schemeFan.rays,
    (M.restrictSubtype M.E).mapEmbedding f ≤m rayMatroid P

theorem hasRayMinor_iff_facetMinor (M : Matroid E) (P : SmoothReflexivePresentation n) :
    HasRayMinor M P ↔ ∃ f : M.E ↪ {u // u ∈ P.normals},
      (M.restrictSubtype M.E).mapEmbedding f ≤m
        VectorMatroid.ofFamily (K := ℝ) (fun u : {u // u ∈ P.normals} ↦ embed u.val) := by
  have hr : P.schemeFan.rays = P.normals := by
    ext u
    exact P.schemeFan_ray_iff u
  unfold HasRayMinor rayMatroid
  change (∃ f : M.E ↪ {u : Lattice n // u ∈ P.schemeFan.rays},
    (M.restrictSubtype M.E).mapEmbedding f ≤m
      VectorMatroid.ofFamily (K := ℝ)
        (fun u : {u : Lattice n // u ∈ P.schemeFan.rays} ↦ embed u.val)) ↔ _
  rw [hr]

/-- All geometric conclusions refer to the displayed original scheme and maps.
The torus action is the actual glued group-scheme action. -/
def IsSmoothProjectiveFano (P : SmoothReflexivePresentation n)
    (k : Type u) [Field k] : Prop :=
  IsIntegral (P.schemeFan.fanScheme k) ∧
  Smooth (P.schemeFan.fanSchemeStructureMap k) ∧
  IsProper (P.schemeFan.fanSchemeStructureMap k) ∧
  IsClosedImmersion (P.projectiveEmbedding k) ∧
  P.projectiveEmbedding k ≫ polynomialProjectiveToSpec k
    (WeightIndex.{u} (F := P.schemeFan)) = P.schemeFan.fanSchemeStructureMap k ∧
  topologicalKrullDim (P.schemeFan.fanScheme k) = n ∧
  IsAmpleModule (anticanonicalLineBundle P.schemeFan k).obj ∧
  IsOpenImmersion (P.schemeFan.torusOpenMap k) ∧
  DenseRange (P.schemeFan.torusOpenMap k) ∧
  Nonempty (ModObj (PaperVerification.ToricSchemes.splitTorusOver k (Lattice n))
    (P.schemeFan.fanSchemeOver k))

theorem isSmoothProjectiveFano (P : SmoothReflexivePresentation n)
    (k : Type u) [Field k] : IsSmoothProjectiveFano P k := by
  obtain ⟨hs, hp, he, hb, hd, ha⟩ := P.smooth_projective_fano k
  exact ⟨inferInstance, hs, hp, he, hb, hd, ha, inferInstance,
    P.schemeFan.torusOpenMap_denseRange k, ⟨inferInstance⟩⟩

/-- The actual inward anticanonical polytope is the integral reflection of
the constructed outward-normal presentation. -/
theorem schemePolytope_eq_neg_image (P : SmoothReflexivePresentation n) :
    P.schemePolytope.carrier = Neg.neg '' P.carrier := by
  ext x
  rw [P.mem_schemePolytope_iff]
  constructor
  · intro hx
    exact ⟨-x, hx, neg_neg x⟩
  · rintro ⟨y, hy, rfl⟩
    simpa only [neg_neg] using hy

/-- Reflection preserves the vertex-congruence obstruction to an actual
unimodular triangular face; no combinatorial substitute for a face is used. -/
theorem anticanonicalPolytope_UT_free_of_congruent_vertices
    (P : SmoothReflexivePresentation n) (d : ℤ) (hd : ¬ IsUnit d)
    (hdiv : ∀ a ∈ P.vertices, ∀ b ∈ P.vertices,
      ∃ z : Lattice n, b - a = d • z)
    (F : Set (Ambient n)) (hF : IsExtreme ℝ P.schemePolytope.carrier F) :
    ¬ SegmentSimplex.IsUnimodularTriangle F := by
  intro htri
  obtain ⟨a, b, ha, hb, hprim⟩ :=
    SegmentSimplex.unimodular_triangle_has_primitive_edge htri
  have hvertex (v : Lattice n)
      (hv : embed v ∈ P.schemePolytope.carrier.extremePoints ℝ) : -v ∈ P.vertices := by
    rw [schemePolytope_eq_neg_image] at hv
    change embed v ∈ ((LinearEquiv.neg ℝ : Ambient n ≃ₗ[ℝ] Ambient n) ''
      P.carrier).extremePoints ℝ at hv
    rw [← image_extremePoints] at hv
    obtain ⟨x, hx, hxv⟩ := hv
    have hsub : P.carrier.extremePoints ℝ ⊆ embed '' (P.vertices : Set (Lattice n)) :=
      extremePoints_convexHull_subset
    obtain ⟨w, hw, rfl⟩ := hsub hx
    have hneg : -w = v := by
      ext i
      have hi := congrFun hxv i
      change -(w i : ℝ) = (v i : ℝ) at hi
      exact_mod_cast hi
    have hwv : w = -v := by rw [← hneg, neg_neg]
    simpa only [hwv, Finset.mem_coe] using hw
  have ha' := hvertex a (hF.extremePoints_subset_extremePoints ha)
  have hb' := hvertex b (hF.extremePoints_subset_extremePoints hb)
  obtain ⟨z, hz⟩ := hdiv (-a) ha' (-b) hb'
  apply hd
  apply hprim d (-z)
  calc
    b - a = -((-b) - (-a)) := by abel
    _ = -(d • z) := congrArg Neg.neg hz
    _ = d • (-z) := (smul_neg d z).symm

/-- The boundary congruence supplies an actual tensor root of the intrinsic
anticanonical sheaf at the prescribed natural exponent. -/
def HasAnticanonicalTensorRoot (P : SmoothReflexivePresentation n)
    (k : Type u) [Field k] (d : ℕ) : Prop :=
  ∃ D : Lattice n → ℤ,
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible (P.schemeFan.fanScheme k)
      (P.schemeFan.fanCartierData k P.schemeFan.isPure D).sheaf ∧
      Nonempty ((anticanonicalLineBundle P.schemeFan k).obj ≅
        PaperVerification.ToricSchemes.tensorSheafPower
          (P.schemeFan.fanCartierData k P.schemeFan.isPure D).sheaf d)

theorem tensorRoot_of_coefficient_relation (P : SmoothReflexivePresentation n)
    (k : Type u) [Field k] (d : ℕ)
    (h : ∃ D : Lattice n → ℤ, ∃ m : Lattice n,
      ∀ u ∈ P.normals, (1 : ℤ) = (d : ℤ) * D u + integerPairing m u) :
    HasAnticanonicalTensorRoot P k d := by
  obtain ⟨D, m, hm⟩ := h
  exact ⟨D, (cartierInvertibleSheaf
    (P.schemeFan.fanCartierData k P.schemeFan.isPure D)).property,
    ⟨P.anticanonicalDivisibilityIso k d D m hm⟩⟩

/-- Corollary 5.3, including the actual Fano scheme, all ordinary matroid
labels, every prescribed index, and the genuine anticanonical polytope. -/
theorem rational_exists_divisible_fano
    (M : Matroid E) [M.Finite]
    (hM : RepresentationBridge.RepresentableOnGround ℚ M)
    (k : Type u) [Field k] (d : ℕ) (hd : 2 ≤ d) :
    ∃ n : ℕ, 0 < n ∧ ∃ P : SmoothReflexivePresentation n,
      IsSmoothProjectiveFano P k ∧ HasRayMinor M P ∧
      HasAnticanonicalTensorRoot P k d ∧
      ∀ F : Set (Ambient n), IsExtreme ℝ P.schemePolytope.carrier F →
        ¬ SegmentSimplex.IsUnimodularTriangle F := by
  have hdZ : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  obtain ⟨n, hn, P, f, hf, _, hcoeff, hdiv⟩ :=
    RationalRealization.exists_smooth_reflexive_realization M hM d hdZ
  refine ⟨n, hn, P, isSmoothProjectiveFano P k,
    (hasRayMinor_iff_facetMinor M P).mpr ⟨f, hf⟩,
    tensorRoot_of_coefficient_relation P k d hcoeff, ?_⟩
  refine anticanonicalPolytope_UT_free_of_congruent_vertices P d ?_ hdiv
  simp only [Int.isUnit_iff]
  omega

/-- Corollary 5.2, with the stronger prescribed-index construction.
Uniformity is stated on the actual original scheme fan's primitive rays. -/
theorem regular_exists_uniform_divisible_fano
    (M : Matroid E) [M.Finite] (hM : RepresentationBridge.RegularOnGround M)
    (k : Type u) [Field k] (d : ℕ) (hd : 2 ≤ d) :
    ∃ n : ℕ, 0 < n ∧ ∃ P : SmoothReflexivePresentation n,
      IsSmoothProjectiveFano P k ∧
      IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
        (fun v : P.schemeFan.rays ↦ v.val) ∧
      HasRayMinor M P ∧ HasAnticanonicalTensorRoot P k d ∧
      ∀ F : Set (Ambient n), IsExtreme ℝ P.schemePolytope.carrier F →
        ¬ SegmentSimplex.IsUnimodularTriangle F := by
  have hdZ : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  obtain ⟨n, hn, P, hP, f, hf, _, hcoeff, hdiv⟩ :=
    RegularRealization.exists_uniform_smooth_reflexive_realization M hM d hdZ
  have hr : P.schemeFan.rays = P.normals := by
    ext u
    exact P.schemeFan_ray_iff u
  refine ⟨n, hn, P, isSmoothProjectiveFano P k, ?_,
    (hasRayMinor_iff_facetMinor M P).mpr ⟨f, hf⟩,
    tensorRoot_of_coefficient_relation P k d hcoeff, ?_⟩
  · change IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun v : {u : Lattice n // u ∈ P.schemeFan.rays} ↦ v.val)
    rw [hr]
    exact hP
  · refine anticanonicalPolytope_UT_free_of_congruent_vertices P d ?_ hdiv
    simp only [Int.isUnit_iff]
    omega

/-- The integer formulation of the prescribed index is identical to the
natural tensor exponent. The equality of indices is part of the conclusion. -/
theorem rational_exists_divisible_fano_integer
    (M : Matroid E) [M.Finite]
    (hM : RepresentationBridge.RepresentableOnGround ℚ M)
    (k : Type u) [Field k] (d : ℤ) (hd : 2 ≤ d) :
    (d.toNat : ℤ) = d ∧
      ∃ n : ℕ, 0 < n ∧ ∃ P : SmoothReflexivePresentation n,
        IsSmoothProjectiveFano P k ∧ HasRayMinor M P ∧
        HasAnticanonicalTensorRoot P k d.toNat ∧
        ∀ F : Set (Ambient n), IsExtreme ℝ P.schemePolytope.carrier F →
          ¬ SegmentSimplex.IsUnimodularTriangle F := by
  exact ⟨Int.toNat_of_nonneg (by omega),
    rational_exists_divisible_fano M hM k d.toNat (by omega)⟩

/-- Necessity uses ordinary rational representability of a genuine ray minor. -/
theorem rational_of_rayMinor (M : Matroid E) [M.Finite]
    (P : SmoothReflexivePresentation n) (h : HasRayMinor M P) :
    RepresentationBridge.RepresentableOnGround ℚ M := by
  obtain ⟨f, hf⟩ := (hasRayMinor_iff_facetMinor M P).mp h
  exact RationalRealization.rationally_representable_of_facet_minor P M f hf

theorem regular_of_uniform_rayMinor (M : Matroid E) [M.Finite]
    (P : SmoothReflexivePresentation n)
    (hP : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun v : P.schemeFan.rays ↦ v.val)) (h : HasRayMinor M P) :
    RepresentationBridge.RegularOnGround M := by
  obtain ⟨f, hf⟩ := (hasRayMinor_iff_facetMinor M P).mp h
  apply RegularRealization.regular_of_uniform_facet_minor P _ M f hf
  have hr : P.schemeFan.rays = P.normals := by
    ext u
    exact P.schemeFan_ray_iff u
  rw [← hr]
  exact hP

theorem rational_iff_smooth_projective_fano_rayMinor
    (M : Matroid E) [M.Finite] (k : Type u) [Field k] :
    RepresentationBridge.RepresentableOnGround ℚ M ↔
      ∃ n : ℕ, 0 < n ∧ ∃ P : SmoothReflexivePresentation n,
        IsSmoothProjectiveFano P k ∧ HasRayMinor M P := by
  constructor
  · intro hM
    obtain ⟨n, hn, P, hF, hminor, _⟩ := rational_exists_divisible_fano M hM k 2 le_rfl
    exact ⟨n, hn, P, hF, hminor⟩
  · rintro ⟨n, _, P, _, hminor⟩
    exact rational_of_rayMinor M P hminor

/-- The exact fixed-index characterization in Corollary 5.3. The natural
tensor exponent is proved equal to the prescribed integer, and the actual
anticanonical polytope is retained in the same existential witness. -/
theorem rational_iff_prescribed_index_fano_rayMinor
    (M : Matroid E) [M.Finite] (k : Type u) [Field k] (d : ℤ) (hd : 2 ≤ d) :
    RepresentationBridge.RepresentableOnGround ℚ M ↔
      ∃ q : ℕ, (q : ℤ) = d ∧
        ∃ n : ℕ, 0 < n ∧ ∃ P : SmoothReflexivePresentation n,
          IsSmoothProjectiveFano P k ∧ HasRayMinor M P ∧
          HasAnticanonicalTensorRoot P k q ∧
          ∀ F : Set (Ambient n), IsExtreme ℝ P.schemePolytope.carrier F →
            ¬ SegmentSimplex.IsUnimodularTriangle F := by
  constructor
  · intro hM
    obtain ⟨hcast, hP⟩ := rational_exists_divisible_fano_integer M hM k d hd
    exact ⟨d.toNat, hcast, hP⟩
  · rintro ⟨q, _, n, _, P, _, hminor, _⟩
    exact rational_of_rayMinor M P hminor

theorem regular_iff_uniform_smooth_projective_fano_rayMinor
    (M : Matroid E) [M.Finite] (k : Type u) [Field k] :
    RepresentationBridge.RegularOnGround M ↔
      ∃ n : ℕ, 0 < n ∧ ∃ P : SmoothReflexivePresentation n,
        IsSmoothProjectiveFano P k ∧
        IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
          (fun v : P.schemeFan.rays ↦ v.val) ∧ HasRayMinor M P := by
  constructor
  · intro hM
    obtain ⟨n, hn, P, hF, hP, hminor, _⟩ :=
      regular_exists_uniform_divisible_fano M hM k 2 le_rfl
    exact ⟨n, hn, P, hF, hP, hminor⟩
  · rintro ⟨n, _, P, _, hP, hminor⟩
    exact regular_of_uniform_rayMinor M P hP hminor

#print axioms rational_exists_divisible_fano
#print axioms rational_exists_divisible_fano_integer
#print axioms regular_exists_uniform_divisible_fano
#print axioms rational_iff_smooth_projective_fano_rayMinor
#print axioms rational_iff_prescribed_index_fano_rayMinor
#print axioms regular_iff_uniform_smooth_projective_fano_rayMinor

end Unimodular.SchemeRealizations
