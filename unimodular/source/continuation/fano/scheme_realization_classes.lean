module

public import Continuation.Fano.SchemeRealizations

/-!
# Corollaries 5.2 and 5.3 for the whole class of fan schemes

The existential witnesses here range over every smooth complete fan. They
are not required to carry our particular reflexive presentation. Necessity
is proved for every integral ray configuration, and in the regular case
for every uniformly unimodular fan, before any positivity hypothesis is used.

Projectivity is an actual closed immersion into a finite polynomial Proj
over the original field. The split torus has its actual dense open map,
and the actual glued action is proved to restrict to torus multiplication.
The anticanonical bundle is the intrinsic dual of the top Kähler bundle.

`RegularOnGround` uses the rational totally unimodular representation
convention, as in the recorded upstream Seymour definition. No equivalence
with a separate all-fields definition of regularity is asserted here.
The scope is schemes constructed from arbitrary smooth complete fans;
transport from an independently supplied abstract toric variety is separate.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace Unimodular.SchemeRealizationClasses

open Set AlgebraicGeometry CategoryTheory MonoidalCategory MonObj
open Unimodular.NefBig Unimodular.Projectivity
open PaperVerification.ToricGeometry
open scoped Matroid BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

variable {E : Type*} {n : ℕ}

/-- The ordinary matroid on all actual primitive rays of an arbitrary fan. -/
def rayMatroid (F : PaperVerification.ToricGeometry.SmoothCompleteFan n) : Matroid F.rays :=
  VectorMatroid.ofFamily (K := ℝ) (fun v : F.rays ↦ Unimodular.embed v.val)

/-- Ordinary deletion and contraction, with the entire original ground retained. -/
def HasRayMinor (M : Matroid E) (F : PaperVerification.ToricGeometry.SmoothCompleteFan n) : Prop :=
  ∃ f : M.E ↪ F.rays,
    (M.restrictSubtype M.E).mapEmbedding f ≤m rayMatroid F

/-- A finite projective embedding over the specified field, as an equality
of actual scheme morphisms. -/
def HasProjectiveEmbedding (F : PaperVerification.ToricGeometry.SmoothCompleteFan n) (k : Type u) [Field k] : Prop :=
  ∃ Index : Type u, Finite Index ∧
    ∃ e : F.fanScheme k ⟶ Proj (MvPolynomial.homogeneousSubmodule Index k),
      IsClosedImmersion e ∧
        e ≫ polynomialProjectiveToSpec k Index = F.fanSchemeStructureMap k

/-- Genuine smooth projective Fano geometry, including the actual torus
embedding and the compatibility of the actual action with multiplication. -/
def IsSmoothProjectiveFanoFan (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)
    (k : Type u) [Field k] : Prop :=
  IsIntegral (F.fanScheme k) ∧
  Smooth (F.fanSchemeStructureMap k) ∧
  IsProper (F.fanSchemeStructureMap k) ∧
  HasProjectiveEmbedding F k ∧
  topologicalKrullDim (F.fanScheme k) = n ∧
  IsAmpleModule (anticanonicalLineBundle F k).obj ∧
  IsOpenImmersion (F.splitTorusOpenMap k) ∧
  DenseRange (F.splitTorusOpenMap k) ∧
  μ[PaperVerification.ToricSchemes.splitTorusOver k (Lattice n)] ≫
      (F.splitTorusOpenMap k).asOver (Spec (CommRingCat.of k)) =
    PaperVerification.ToricSchemes.splitTorusOver k (Lattice n) ◁
      (F.splitTorusOpenMap k).asOver (Spec (CommRingCat.of k)) ≫
        γ[PaperVerification.ToricSchemes.splitTorusOver k (Lattice n), F.fanSchemeOver k]

/-- Divisibility is an isomorphism of ordinary line bundles, not a
divisibility assertion about a combinatorial coefficient vector. -/
def HasAnticanonicalTensorRoot (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)
    (k : Type u) [Field k] (d : ℕ) : Prop :=
  ∃ L : (F.fanScheme k).Modules,
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible (F.fanScheme k) L ∧
      Nonempty ((anticanonicalLineBundle F k).obj ≅
        PaperVerification.ToricSchemes.tensorSheafPower L d)

/-- The ordinary unit-boundary anticanonical polytope itself is UT-free.
The quantifier covers all geometric faces and therefore every two-face. -/
def AnticanonicalPolytopeUTFree (F : PaperVerification.ToricGeometry.SmoothCompleteFan n) : Prop :=
  ∀ S : Set (Ambient n), IsExtreme ℝ (F.fanPolytope (fun _ ↦ 1)) S →
    ¬ SegmentSimplex.IsUnimodularTriangle S

/-- The constructed reflexive presentation supplies all of the displayed
geometric conclusions for the same original fan scheme. -/
theorem isSmoothProjectiveFanoFan_of_presentation
    (P : SmoothReflexivePresentation n) (k : Type u) [Field k] :
    IsSmoothProjectiveFanoFan P.schemeFan k := by
  obtain ⟨hi, hs, hp, he, hb, hd, ha, _, _, _⟩ :=
    SchemeRealizations.isSmoothProjectiveFano P k
  refine ⟨hi, hs, hp, ?_, hd, ha, inferInstance,
    P.schemeFan.splitTorusOpenMap_denseRange k,
    P.schemeFan.fanScheme_action_extends_torus k⟩
  exact ⟨WeightIndex.{u} (F := P.schemeFan), inferInstance,
    P.projectiveEmbedding k, he, hb⟩

theorem hasRayMinor_presentation_iff (M : Matroid E)
    (P : SmoothReflexivePresentation n) :
    HasRayMinor M P.schemeFan ↔ SchemeRealizations.HasRayMinor M P := Iff.rfl

/-- The explicit invariant Cartier witness from the construction is an
ordinary line-bundle root. The class predicate does not require roots to
be invariant Cartier sheaves. -/
theorem hasAnticanonicalTensorRoot_of_presentation
    (P : SmoothReflexivePresentation n) (k : Type u) [Field k] (d : ℕ)
    (h : SchemeRealizations.HasAnticanonicalTensorRoot P k d) :
    HasAnticanonicalTensorRoot P.schemeFan k d := by
  obtain ⟨D, hInv, hIso⟩ := h
  exact ⟨(P.schemeFan.fanCartierData k P.schemeFan.isPure D).sheaf, hInv, hIso⟩

/-- The polytope used in the original presentation is literally the
ordinary anticanonical support polytope of its actual fan scheme. -/
theorem schemePolytope_carrier_eq_fanPolytope
    (P : SmoothReflexivePresentation n) :
    P.schemePolytope.carrier = P.schemeFan.fanPolytope (fun _ ↦ 1) := by
  simpa only [SmoothReflexivePresentation.schemePolytope, Int.cast_one] using
    P.schemeFan.supportLatticePolytope_carrier P.schemeFan.isPure
      (fun _ ↦ (1 : ℤ)) P.schemeFan_strict_unit_support_int

theorem anticanonicalPolytopeUTFree_of_presentation
    (P : SmoothReflexivePresentation n)
    (h : ∀ S : Set (Ambient n), IsExtreme ℝ P.schemePolytope.carrier S →
      ¬ SegmentSimplex.IsUnimodularTriangle S) :
    AnticanonicalPolytopeUTFree P.schemeFan := by
  intro S hS
  apply h S
  rwa [schemePolytope_carrier_eq_fanPolytope P]

/-- Necessity for every integral fan ray family, without Fano,
projectivity, polytope-presentation or positivity assumptions. -/
theorem rational_of_rayMinor (M : Matroid E) [M.Finite]
    (F : PaperVerification.ToricGeometry.SmoothCompleteFan n) (h : HasRayMinor M F) :
    RepresentationBridge.RepresentableOnGround ℚ M := by
  obtain ⟨f, hf⟩ := h
  exact RepresentationBridge.integer_ray_minor_ground_representable
    (fun v : F.rays ↦ v.val) M f hf

/-- Necessity for every uniformly unimodular smooth complete fan. The
basis is chosen from an actual full cone, not assumed in the input.
Only after choosing it do we derive total unimodularity. -/
theorem regular_of_uniform_rayMinor (M : Matroid E) [M.Finite]
    (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)
    (hF : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun v : F.rays ↦ v.val))
    (h : HasRayMinor M F) : RepresentationBridge.RegularOnGround M := by
  classical
  obtain ⟨s, hs⟩ := F.fullCones_nonempty F.isPure
  let cone : F.fullCones := ⟨s, hs⟩
  let b := F.fullConeBasis cone
  let A : Matrix (Fin n) F.rays ℤ := fun i v ↦ b.repr v.val i
  have hA : A.IsTotallyUnimodular := by
    apply SignedSums.coordinates_tu_of_uniform (Pi.basisFun ℤ (Fin n)) b
      (fun v : F.rays ↦ v.val) hF
    intro i
    exact ⟨F.activeRay cone i, rfl⟩
  have hinj : Function.Injective (realCoordinates b) := by
    intro x y hxy
    calc
      x = ∑ i, realCoordinates b x i • Unimodular.embed (b i) :=
        (sum_basis_realCoordinates b x).symm
      _ = ∑ i, realCoordinates b y i • Unimodular.embed (b i) := by rw [hxy]
      _ = y := sum_basis_realCoordinates b y
  have hreal : rayMatroid F =
      VectorMatroid.ofFamily (K := ℝ) (fun v i ↦ (A i v : ℝ)) := by
    apply (VectorMatroid.ofFamily_eq_iff _ _).mpr
    intro S
    have he : realCoordinates b ∘ (fun v : F.rays ↦ Unimodular.embed v.val) =
        (fun v i ↦ (A i v : ℝ)) := by
      funext v i
      exact realCoordinates_embed b v.val i
    have hli := (realCoordinates b).linearIndepOn_iff_of_injOn hinj.injOn
      (v := fun v : F.rays ↦ Unimodular.embed v.val) (s := S)
    rw [he] at hli
    exact hli.symm
  have hrat : VectorMatroid.ofFamily (K := ℚ)
        (RepresentationBridge.integerColumns A) =
      VectorMatroid.ofFamily (K := ℝ) (fun v i ↦ (A i v : ℝ)) := by
    simpa only [RepresentationBridge.integerColumns, Rat.cast_intCast] using
      RepresentationBridge.rational_real_matroid_eq
        (RepresentationBridge.integerColumns A)
  obtain ⟨f, hf⟩ := h
  rw [hreal, ← hrat] at hf
  obtain ⟨B, hB, hM⟩ := RepresentationBridge.tu_integer_model_of_minor A hA
    (M.restrictSubtype M.E) (by simp) f hf
  exact (RepresentationBridge.regularOnGround_iff_integer M).mpr ⟨n, B, hB, hM⟩

/-- Every rational matroid has the required actual fan-scheme realization
at every prescribed natural tensor exponent. -/
theorem rational_exists_divisible_fan
    (M : Matroid E) [M.Finite]
    (hM : RepresentationBridge.RepresentableOnGround ℚ M)
    (k : Type u) [Field k] (d : ℕ) (hd : 2 ≤ d) :
    ∃ n : ℕ, 0 < n ∧ ∃ F : PaperVerification.ToricGeometry.SmoothCompleteFan n,
      IsSmoothProjectiveFanoFan F k ∧ HasRayMinor M F ∧
      HasAnticanonicalTensorRoot F k d ∧ AnticanonicalPolytopeUTFree F := by
  obtain ⟨n, hn, P, _, hminor, hroot, hUT⟩ :=
    SchemeRealizations.rational_exists_divisible_fano M hM k d hd
  exact ⟨n, hn, P.schemeFan, isSmoothProjectiveFanoFan_of_presentation P k,
    (hasRayMinor_presentation_iff M P).mpr hminor,
    hasAnticanonicalTensorRoot_of_presentation P k d hroot,
    anticanonicalPolytopeUTFree_of_presentation P hUT⟩

/-- The regular construction preserves uniform unimodularity on all actual
primitive rays, with the same stronger index and UT-free conclusions. -/
theorem regular_exists_uniform_divisible_fan
    (M : Matroid E) [M.Finite] (hM : RepresentationBridge.RegularOnGround M)
    (k : Type u) [Field k] (d : ℕ) (hd : 2 ≤ d) :
    ∃ n : ℕ, 0 < n ∧ ∃ F : PaperVerification.ToricGeometry.SmoothCompleteFan n,
      IsSmoothProjectiveFanoFan F k ∧
      IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) (fun v : F.rays ↦ v.val) ∧
      HasRayMinor M F ∧ HasAnticanonicalTensorRoot F k d ∧
      AnticanonicalPolytopeUTFree F := by
  obtain ⟨n, hn, P, _, hP, hminor, hroot, hUT⟩ :=
    SchemeRealizations.regular_exists_uniform_divisible_fano M hM k d hd
  exact ⟨n, hn, P.schemeFan, isSmoothProjectiveFanoFan_of_presentation P k, hP,
    (hasRayMinor_presentation_iff M P).mpr hminor,
    hasAnticanonicalTensorRoot_of_presentation P k d hroot,
    anticanonicalPolytopeUTFree_of_presentation P hUT⟩

/-- Corollary 5.2 for the whole class of smooth projective uniformly
unimodular Fano fan schemes. The reverse implication has no presentation
restriction and uses no positivity assumption. -/
theorem corollary_5_2 (M : Matroid E) [M.Finite] (k : Type u) [Field k] :
    RepresentationBridge.RegularOnGround M ↔
      ∃ n : ℕ, 0 < n ∧ ∃ F : PaperVerification.ToricGeometry.SmoothCompleteFan n,
        IsSmoothProjectiveFanoFan F k ∧
        IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) (fun v : F.rays ↦ v.val) ∧
        HasRayMinor M F := by
  constructor
  · intro hM
    obtain ⟨n, hn, F, hF, hU, hminor, _⟩ :=
      regular_exists_uniform_divisible_fan M hM k 2 le_rfl
    exact ⟨n, hn, F, hF, hU, hminor⟩
  · rintro ⟨n, _, F, _, hU, hminor⟩
    exact regular_of_uniform_rayMinor M F hU hminor

/-- Corollary 5.3 for every prescribed integer `d ≥ 2`, with no
restriction to our constructed presentations on the necessity side.
The natural tensor exponent is proved equal to that same integer. -/
theorem corollary_5_3 (M : Matroid E) [M.Finite] (k : Type u) [Field k]
    (d : ℤ) (hd : 2 ≤ d) :
    RepresentationBridge.RepresentableOnGround ℚ M ↔
      ∃ q : ℕ, (q : ℤ) = d ∧
        ∃ n : ℕ, 0 < n ∧ ∃ F : PaperVerification.ToricGeometry.SmoothCompleteFan n,
          IsSmoothProjectiveFanoFan F k ∧ HasRayMinor M F ∧
          HasAnticanonicalTensorRoot F k q ∧ AnticanonicalPolytopeUTFree F := by
  constructor
  · intro hM
    have hcast : (d.toNat : ℤ) = d := Int.toNat_of_nonneg (by omega)
    exact ⟨d.toNat, hcast, rational_exists_divisible_fan M hM k d.toNat (by omega)⟩
  · rintro ⟨q, _, n, _, F, _, hminor, _⟩
    exact rational_of_rayMinor M F hminor

#print axioms isSmoothProjectiveFanoFan_of_presentation
#print axioms rational_of_rayMinor
#print axioms regular_of_uniform_rayMinor
#print axioms corollary_5_2
#print axioms corollary_5_3

end Unimodular.SchemeRealizationClasses
