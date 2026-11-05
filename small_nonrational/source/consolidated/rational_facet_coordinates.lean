module
public import Papers.PolytopeTargets
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Papers.PolytopeThreeIncidences
public import Cubical.Polytope.DimStretta
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Papers.FiniteHullCertificates
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Ring
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Papers.SupportFormIndependence
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Tactic.IntervalCases
public import Papers.PolytopeBasicExtreme
public import Cubical.Polytope.FiguraAlVertice
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FinCases
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Topology.NhdsWithin
public import Papers.BipartiteIncidencePeeling
public import Mathlib.Data.Finset.Sum
public import Mathlib.Tactic.FunProp

/-! Canonical source bundle; each original file retains its own scopes. -/

section BundlePart0
/- Source: Papers/RationalCoordinates.lean -/



@[expose] public section

/-!
# Rational coordinates as coordinates in an actual real subfield

The subfield is the image of the usual rational embedding. Thus the
existential rational-coordinate definition and the arbitrary-subfield
realizability definition agree literally at this subfield.
-/

noncomputable section
namespace Papers.Polytopes
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

def rationalSubfield : Subfield ℝ := (Rat.castHom ℝ).fieldRange

@[simp] theorem mem_rationalSubfield (x : ℝ) :
    x ∈ rationalSubfield ↔ ∃ q : ℚ, (q : ℝ) = x := Iff.rfl

theorem rationalCoordinates_iff_coordinatesIn {d : ℕ} (P : ConvexPolytope d) :
    RationalCoordinates P ↔ CoordinatesIn rationalSubfield P := Iff.rfl

theorem rationallyRealizable_iff_realizableOver {d : ℕ} (P : ConvexPolytope d) :
    RationallyRealizable P ↔ RealizableOver P rationalSubfield := Iff.rfl

end Papers.Polytopes

end
end
end BundlePart0

section BundlePart1
/- Source: Papers/RationalApproximation.lean -/




@[expose] public section

/-!
# Rational approximation with the full vertex labels

The local approximation predicate explicitly controls every actual
extreme vertex through the induced map of a face-order isomorphism.
The global density predicate quantifies it over every realization of
the original combinatorial type.
-/

noncomputable section
namespace Papers.Polytopes

open Set Filter Topology
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

def RationallyApproximable (P : ConvexPolytope d) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ConvexPolytope d, ∃ φ : FaceType P ≃o FaceType R,
    RationalCoordinates R ∧ ∀ v : VertexType P, dist (imageVertex φ v).val v.val < ε

theorem rationallyDense_iff_all_approximable (P : ConvexPolytope d) :
    RationallyDense P ↔ ∀ Q : ConvexPolytope d,
      CombinatoriallyEquivalent P Q → RationallyApproximable Q := Iff.rfl

theorem RationallyDense.approximable {P : ConvexPolytope d} (h : RationallyDense P) :
    RationallyApproximable P := h P (CombinatoriallyEquivalent.refl P)

theorem RationallyDense.of_equivalent {P Q : ConvexPolytope d}
    (h : RationallyDense P) (hPQ : CombinatoriallyEquivalent P Q) : RationallyDense Q := by
  intro R hQR
  exact h R (hPQ.trans hQR)

theorem rationallyDense_congr {P Q : ConvexPolytope d} (hPQ : CombinatoriallyEquivalent P Q) :
    RationallyDense P ↔ RationallyDense Q :=
  ⟨fun h => h.of_equivalent hPQ, fun h => h.of_equivalent hPQ.symm⟩

theorem exists_rational_function_close {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ι → ℚ, dist (fun i => (r i : ℝ)) u < ε := by
  have h (i : ι) : ∃ r : ℚ, u i - ε < (r : ℝ) ∧ (r : ℝ) < u i + ε :=
    exists_rat_btwn (by linarith)
  choose r hr using h
  refine ⟨r, (dist_pi_lt_iff hε).mpr ?_⟩
  intro i
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [(hr i).1, (hr i).2]

theorem RationallyApproximable.exists_parameters_in_neighborhood
    {P : ConvexPolytope d} (hP : RationallyApproximable P)
    {ι : Type*} [Fintype ι] (u : ι → ℝ)
    (S : Set ((VertexType P → E d) × (ι → ℝ)))
    (hS : S ∈ 𝓝 (Subtype.val, u)) :
    ∃ Q : ConvexPolytope d, ∃ φ : FaceType P ≃o FaceType Q, ∃ r : ι → ℚ,
      RationalCoordinates Q ∧
        ((fun v => (imageVertex φ v).val), (fun i => (r i : ℝ))) ∈ S := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hS
  obtain ⟨Q, φ, hQ, hclose⟩ := hP δ hδ
  obtain ⟨r, hr⟩ := exists_rational_function_close u δ hδ
  refine ⟨Q, φ, r, hQ, hball ?_⟩
  change dist (((fun v => (imageVertex φ v).val), (fun i => (r i : ℝ)))) (Subtype.val, u) < δ
  rw [Prod.dist_eq, max_lt_iff]
  exact ⟨(dist_pi_lt_iff hδ).mpr hclose, hr⟩

end Papers.Polytopes

end
end
end BundlePart1

section BundlePart2
/- Source: Papers/PolytopeIncidencePeeling.lean -/



@[expose] public section

/-!
# Every induced three-polytope incidence graph has a low-degree node

The active point hull retains every old two-face containing three active
vertices. If all degrees were at least four, two retained faces would
force that hull to remain three-dimensional. Its actual Euler incidence
bound then contradicts the degree lower bound on the active bipartite graph.
-/

noncomputable section
namespace Papers.PolytopeIncidencePeeling

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting
open Papers.PolytopeIncidenceCounting Papers.PolytopeThreeIncidences
open Papers.IncidenceCoreGeometry Papers.BipartiteIncidencePeeling

variable {d : ℕ}

def pointFacetIncident (P : ConvexPolytope d) (x : E d) (F : Face P 2) : Prop :=
  x∈F.val.carrier

def restrictedTwoFace (P Q : ConvexPolytope d) (hQP : Q.toSet⊆P.toSet)
    (F : Face P 2) (hF : 3≤(Q.vertices.filter (·∈F.val.carrier)).card) :
    Face Q 2 :=
  ⟨⟨F.val.carrier∩Q.toSet,(retained_two_face P Q hQP F.val.isFace F.property hF).1⟩,
    (retained_two_face P Q hQP F.val.isFace F.property hF).2⟩

theorem restrictedTwoFace_injective
    (P Q : ConvexPolytope d) (hQP : Q.toSet⊆P.toSet)
    (T : Finset (Face P 2))
    (hc : ∀ F∈T, 3≤(Q.vertices.filter (·∈F.val.carrier)).card) :
    Function.Injective (fun F : T => restrictedTwoFace P Q hQP F.val (hc F.val F.property)) := by
  intro F G heq
  apply Subtype.ext
  apply Subtype.ext
  apply PolytopeFace.ext
  let A := F.val.val.carrier∩Q.toSet
  have hA : A.Nonempty :=
    (retained_two_face P Q hQP F.val.val.isFace F.val.property
      (hc F.val F.property)).1.2
  have heq' : F.val.val.carrier∩Q.toSet=G.val.val.carrier∩Q.toSet :=
    congrArg (fun X : Face Q 2 => X.val.carrier) heq
  apply faces_eq_of_full_dim_common_subset P F.val.val.isFace G.val.val.isFace hA
  · exact Set.inter_subset_left
  · intro x hx
    change x∈F.val.val.carrier∩Q.toSet at hx
    rw [heq'] at hx
    exact hx.1
  · rw [F.val.property]
    exact le_of_eq ((retained_two_face P Q hQP F.val.val.isFace F.val.property
      (hc F.val F.property)).2.symm)
  · rw [G.val.property]
    exact le_of_eq ((retained_two_face P Q hQP F.val.val.isFace F.val.property
      (hc F.val F.property)).2.symm)

def restrictedVerticesEquiv (Q : ConvexPolytope d) (F : Set (E d)) :
    VerticesOn Q (F∩Q.toSet) ≃ (Q.vertices.filter (·∈F)) where
  toFun x := ⟨x.val.val,Finset.mem_filter.mpr ⟨x.val.property,x.property.1⟩⟩
  invFun x := ⟨⟨x.val,(Finset.mem_filter.mp x.property).1⟩,
    (Finset.mem_filter.mp x.property).2,
    vertex_mem_body Q (Finset.mem_filter.mp x.property).1⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem restricted_vertex_card (Q : ConvexPolytope d) (F : Set (E d)) :
    Nat.card (VerticesOn Q (F∩Q.toSet))=(Q.vertices.filter (·∈F)).card := by
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using
    Nat.card_congr (restrictedVerticesEquiv Q F)

/-- The exact geometric low-degree alternative, for arbitrary selected
vertices and selected actual two-faces of an intrinsic three-polytope. -/
theorem exists_low_degree
    (P : ConvexPolytope d) (hdim : P.dim=3)
    (S : Finset (E d)) (hSP : S⊆P.vertices) (T : Finset (Face P 2))
    (hne : S.Nonempty ∨ T.Nonempty) :
    (∃ x∈S, (T.filter (fun F => x∈F.val.carrier)).card≤3) ∨
      (∃ F∈T, (S.filter (fun x => x∈F.val.carrier)).card≤3) := by
  classical
  by_contra h
  have hleft : ∀ x∈S, 4≤(T.filter (fun F => x∈F.val.carrier)).card := by
    intro x hx
    by_contra hh
    exact h (Or.inl ⟨x,hx,by omega⟩)
  have hright : ∀ F∈T, 4≤(S.filter (fun x => x∈F.val.carrier)).card := by
    intro F hF
    by_contra hh
    exact h (Or.inr ⟨F,hF,by omega⟩)
  have hS : S.Nonempty := by
    rcases hne with hS | hT
    · exact hS
    · obtain ⟨F,hF⟩ := hT
      have hc := hright F hF
      obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0<(S.filter (fun x => x∈F.val.carrier)).card by omega)
      exact ⟨x,(Finset.mem_filter.mp hx).1⟩
  let Q := vertexSubsetPolytope P S hS hSP
  have hQP : Q.toSet⊆P.toSet := vertexSubset_body_subset P S hS hSP
  have hc : ∀ F∈T, 3≤(Q.vertices.filter (·∈F.val.carrier)).card := by
    intro F hF
    exact le_trans (by decide : 3≤4) (hright F hF)
  obtain ⟨x,hx⟩ := hS
  have hTcard : 1<T.card := by
    have h4 := hleft x hx
    have hh := Finset.card_filter_le T (fun F => x∈F.val.carrier)
    omega
  obtain ⟨F,hF,G,hG,hFG⟩ := Finset.one_lt_card.mp hTcard
  have hFG' : F.val.carrier≠G.val.carrier := by
    intro heq
    exact hFG (Subtype.ext (PolytopeFace.ext heq))
  have hQdim : Q.dim=3 := dimension_three_of_two_retained_faces P Q hdim hQP
    F.val.isFace G.val.isFace F.property G.property hFG' (hc F hF) (hc G hG)
  let f : T → Face Q 2 := fun F => restrictedTwoFace P Q hQP F.val (hc F.val F.property)
  have hf : Function.Injective f := restrictedTwoFace_injective P Q hQP T hc
  let U : Finset (Face Q 2) := Finset.univ.image f
  have hUcard : U.card=T.card := by
    rw [Finset.card_image_of_injective _ hf]
    simp
  have hweight : ∀ F : T, Nat.card (VerticesOn Q (f F).val.carrier)=
      (S.filter (fun x => x∈F.val.val.carrier)).card := by
    intro F
    exact restricted_vertex_card Q F.val.val.carrier
  have hUsum : (∑ H∈U,(Nat.card (VerticesOn Q H.val.carrier) : ℤ)) =
      ∑ F∈T,((S.filter (fun x => x∈F.val.carrier)).card : ℤ) := by
    rw [Finset.sum_image (fun a _ b _ h => hf h)]
    simp_rw [hweight]
    exact Finset.sum_coe_sort T (fun F : Face P 2 => ((S.filter (fun x => x∈F.val.carrier)).card : ℤ))
  have hbound := selected_facet_incidence_bound Q hQdim U
  rw [hUsum,hUcard] at hbound
  change (∑ F∈T,((S.filter (fun x => x∈F.val.carrier)).card : ℤ)) <
    2*((S.card : ℤ)+T.card) at hbound
  have hsum : (∑ x∈S,(pointDegree (pointFacetIncident P) T x : ℤ)) =
      ∑ F∈T,(faceDegree (pointFacetIncident P) S F : ℤ) := by
    exact_mod_cast sum_degrees (pointFacetIncident P) S T
  have hbound' : (∑ x∈S,(pointDegree (pointFacetIncident P) T x : ℤ)) <
      2*((S.card : ℤ)+T.card) := by
    rw [hsum]
    exact hbound
  exact h (exists_degree_le_three (pointFacetIncident P) S T hbound')

end Papers.PolytopeIncidencePeeling

end
end
end BundlePart2

section BundlePart3
/- Source: Papers/FacetSupport.lean -/





@[expose] public section

/-!
# Supporting affine forms of actual facets

The extremality used here is a consequence of the ordinary geometric face
dimension.  No dual polytope or extra assumption about a cone of normals
is built into the definitions.  The final coefficient lemma is the sign
step needed when restoring a vertex beyond a simplex facet.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

def affineFormEvaluation (x : E d) : (E d →ᵃ[ℝ] ℝ) →ₗ[ℝ] ℝ where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem affineForm_sum_apply {ι : Type*} (s : Finset ι)
    (f : ι → E d →ᵃ[ℝ] ℝ) (x : E d) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  exact map_sum (affineFormEvaluation x) f s

def IsFacet (P : ConvexPolytope d) (F : Set (E d)) : Prop :=
  P.IsFace F ∧ faceDim F + 1 = P.dim

def SupportsFace (P : ConvexPolytope d) (F : Set (E d))
    (f : E d →ᵃ[ℝ] ℝ) : Prop :=
  (∀ x ∈ P.toSet, 0 ≤ f x) ∧ F = {x ∈ P.toSet | f x = 0}

theorem SupportsFace.mem_iff {P : ConvexPolytope d} {F : Set (E d)}
    {f : E d →ᵃ[ℝ] ℝ} (hf : SupportsFace P F f) (x : E d) :
    x ∈ F ↔ x ∈ P.toSet ∧ f x = 0 := by rw [hf.2]; rfl

theorem SupportsFace.eq_zero {P : ConvexPolytope d} {F : Set (E d)}
    {f : E d →ᵃ[ℝ] ℝ} (hf : SupportsFace P F f) {x : E d} (hx : x ∈ F) :
    f x = 0 := ((hf.mem_iff x).mp hx).2

theorem exists_supportsFace (P : ConvexPolytope d) {F : Set (E d)}
    (hF : P.IsFace F) : ∃ f : E d →ᵃ[ℝ] ℝ, SupportsFace P F f := by
  obtain ⟨l, hl⟩ := hF.1 hF.2
  obtain ⟨p, hp⟩ := hF.2
  have hp' := hp
  rw [hl] at hp'
  refine ⟨AffineMap.const ℝ (E d) (l p) - l.toLinearMap.toAffineMap, ?_, ?_⟩
  · intro x hx
    change 0 ≤ l p - l x
    exact sub_nonneg.mpr (hp'.2 x hx)
  · ext x
    rw [hl]
    change (x ∈ P.toSet ∧ ∀ y ∈ P.toSet, l y ≤ l x) ↔
      x ∈ P.toSet ∧ l p - l x = 0
    constructor
    · rintro ⟨hx, hmax⟩
      exact ⟨hx, sub_eq_zero.mpr (le_antisymm (hmax p hp'.1) (hp'.2 x hx))⟩
    · rintro ⟨hx, heq⟩
      exact ⟨hx, fun y hy => (hp'.2 y hy).trans_eq (sub_eq_zero.mp heq)⟩

theorem IsFacet.ne_toSet {P : ConvexPolytope d} {F : Set (E d)}
    (hF : IsFacet P F) : F ≠ P.toSet := by
  intro heq
  have h := hF.2
  rw [heq] at h
  change P.dim + 1 = P.dim at h
  omega

theorem IsFacet.eq_of_subset {P : ConvexPolytope d} {F G : Set (E d)}
    (hF : IsFacet P F) (hG : P.IsFace G) (hproper : G ≠ P.toSet)
    (hsub : F ⊆ G) : F = G := by
  by_contra hne
  have hFG : F ⊂ G := (Set.ssubset_iff_subset_ne).mpr ⟨hsub, hne⟩
  have hGP : G ⊂ P.toSet := (Set.ssubset_iff_subset_ne).mpr
    ⟨face_subset_toSet P hG, hproper⟩
  have h₁ := faceDim_lt_of_ssubset P hF.1 hG hFG
  have h₂ := faceDim_lt_of_ssubset P hG (toSet_isFace P) hGP
  change faceDim G < P.dim at h₂
  have h₃ := hF.2
  omega

theorem IsFacet.support_ne_zero {P : ConvexPolytope d} {F : Set (E d)}
    (hF : IsFacet P F) {f : E d →ᵃ[ℝ] ℝ} (hf : SupportsFace P F f) : f ≠ 0 := by
  intro heq
  apply hF.ne_toSet
  rw [hf.2, heq]
  ext x
  simp

/-- In a nonnegative linear combination exposing a facet, every positive
summand exposes that same facet.  This is proved from actual face
inclusion and strict growth of dimension. -/
theorem positive_support_summand_same_facet
    {ι : Type*} [Fintype ι] (P : ConvexPolytope d)
    (F : ι → Set (E d)) (f : ι → E d →ᵃ[ℝ] ℝ)
    (hF : ∀ i, IsFacet P (F i)) (hf : ∀ i, SupportsFace P (F i) (f i))
    (G : Set (E d)) (g : E d →ᵃ[ℝ] ℝ)
    (hG : IsFacet P G) (hg : SupportsFace P G g)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (heq : ∑ i, c i • f i = g) (i : ι) (hi : 0 < c i) : G = F i := by
  apply hG.eq_of_subset (hF i).1 (hF i).ne_toSet
  intro x hx
  have hxP : x ∈ P.toSet := face_subset_toSet P hG.1 hx
  have hsum : ∑ j, c j * f j x = 0 := by
    have h := congrArg (fun a : E d →ᵃ[ℝ] ℝ => a x) heq
    simpa only [affineForm_sum_apply, AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul,
      hg.eq_zero hx] using h
  have hle : c i * f i x ≤ ∑ j, c j * f j x :=
    Finset.single_le_sum (fun j _ => mul_nonneg (hc j) ((hf j).1 x hxP))
      (Finset.mem_univ i)
  have hfi : f i x = 0 := by
    rw [hsum] at hle
    have hn := (hf i).1 x hxP
    nlinarith
  exact ((hf i).mem_iff x).mpr ⟨hxP, hfi⟩

/-- A facet different from all facets in a basis cannot have a
nonnegative expansion in their supporting forms. -/
theorem facet_support_not_all_coordinates_nonneg
    {ι : Type*} [Fintype ι] (P : ConvexPolytope d)
    (F : ι → Set (E d)) (b : Basis ι ℝ (E d →ᵃ[ℝ] ℝ))
    (hF : ∀ i, IsFacet P (F i)) (hb : ∀ i, SupportsFace P (F i) (b i))
    (G : Set (E d)) (g : E d →ᵃ[ℝ] ℝ)
    (hG : IsFacet P G) (hg : SupportsFace P G g)
    (hne : ∀ i, G ≠ F i) : ¬∀ i, 0 ≤ b.repr g i := by
  intro hc
  have hz : ∀ i, b.repr g i = 0 := by
    intro i
    by_contra hi
    have hpos : 0 < b.repr g i := lt_of_le_of_ne (hc i) (Ne.symm hi)
    exact hne i (positive_support_summand_same_facet P F b hF hb G g hG hg
      (fun j => b.repr g j) hc (b.sum_repr g) i hpos)
  have hg0 : g = 0 := by
    apply b.repr.injective
    ext i
    simp only [map_zero, Finsupp.zero_apply, hz i]
  exact hG.support_ne_zero hg hg0

/-- At a simplex facet all other coordinates of another facet form are
nonnegative, by evaluation on the simplex vertices.  Its remaining
coordinate is therefore strictly negative. -/
theorem facet_support_distinguished_coordinate_neg
    {ι : Type*} [Fintype ι] (P : ConvexPolytope d)
    (F : ι → Set (E d)) (b : Basis ι ℝ (E d →ᵃ[ℝ] ℝ))
    (hF : ∀ i, IsFacet P (F i)) (hb : ∀ i, SupportsFace P (F i) (b i))
    (G : Set (E d)) (g : E d →ᵃ[ℝ] ℝ)
    (hG : IsFacet P G) (hg : SupportsFace P G g)
    (hne : ∀ i, G ≠ F i) (i₀ : ι)
    (hc : ∀ i, i ≠ i₀ → 0 ≤ b.repr g i) : b.repr g i₀ < 0 := by
  by_contra h
  have h₀ : 0 ≤ b.repr g i₀ := le_of_not_gt h
  apply facet_support_not_all_coordinates_nonneg P F b hF hb G g hG hg hne
  intro i
  by_cases hi : i = i₀
  · simpa only [hi] using h₀
  · exact hc i hi

end Papers.Polytopes

end
end
end BundlePart3

section BundlePart4
/- Source: Papers/FacetHalfspaces.lean -/






@[expose] public section

/-!
# A full-dimensional finite polytope is the intersection of its facet halfspaces

The proof enlarges a separating exposed face while keeping the separated
point strictly outside.  Each enlargement is a finite minimum-ratio pivot.
This avoids assuming a polyhedral duality theorem or a halfspace
representation as part of the polytope datatype.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem affine_form_apply (f : E d →ᵃ[ℝ] ℝ) (x : E d) :
    f x = f.linear x + f 0 := by
  simpa only [vadd_eq_add, add_zero] using f.map_vadd (0 : E d) x

theorem affine_nonneg_on_hull (s : Finset (E d)) (f : E d →ᵃ[ℝ] ℝ)
    (hf : ∀ x ∈ s, 0 ≤ f x) : ∀ x ∈ convexHull ℝ (s : Set (E d)), 0 ≤ f x := by
  let l := f.linear.toContinuousLinearMap
  have hlin : ∀ x ∈ s, -f 0 ≤ l x := by
    intro x hx
    have h := hf x hx
    rw [affine_form_apply f x] at h
    change -f 0 ≤ f.linear x
    linarith
  intro x hx
  have h := linear_lower_bound_on_hull s l (-f 0) hlin x hx
  change -f 0 ≤ f.linear x at h
  rw [affine_form_apply f x]
  linarith

def affineZeroFace (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) : Set (E d) :=
  {x ∈ P.toSet | f x = 0}

theorem affineZeroFace_isFace (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ)
    (hf : ∀ x ∈ P.toSet, 0 ≤ f x) (hne : (affineZeroFace P f).Nonempty) :
    P.IsFace (affineZeroFace P f) := by
  refine ⟨?_, hne⟩
  intro _
  let l := f.linear.toContinuousLinearMap
  refine ⟨-l, ?_⟩
  obtain ⟨p, hpP, hpf⟩ := hne
  ext x
  change (x ∈ P.toSet ∧ f x = 0) ↔
    x ∈ P.toSet ∧ ∀ y ∈ P.toSet, -l y ≤ -l x
  constructor
  · rintro ⟨hxP, hxf⟩
    refine ⟨hxP, ?_⟩
    intro y hy
    have hfy := hf y hy
    rw [affine_form_apply f x] at hxf
    rw [affine_form_apply f y] at hfy
    change -f.linear y ≤ -f.linear x
    linarith
  · rintro ⟨hxP, hmax⟩
    refine ⟨hxP, ?_⟩
    have hlx := hmax p hpP
    change -f.linear p ≤ -f.linear x at hlx
    have hfx := hf x hxP
    rw [affine_form_apply f p] at hpf
    rw [affine_form_apply f x] at hfx ⊢
    linarith

theorem fullDim_affineSpan_body (P : ConvexPolytope d) (hP : P.IsFullDim) :
    affineSpan ℝ P.toSet = ⊤ := by
  have hspan : vectorSpan ℝ P.toSet = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    change finrank ℝ (vectorSpan ℝ P.toSet) = d at hP
    simpa only [finrank_euclideanSpace_fin] using hP
  apply (AffineSubspace.direction_eq_top_iff_of_nonempty ?_).mp
  · rw [direction_affineSpan, hspan]
  · obtain ⟨x, hx⟩ := (toSet_isFace P).2
    exact ⟨x, subset_affineSpan ℝ _ hx⟩

theorem fullDim_affineSpan_vertices (P : ConvexPolytope d) (hP : P.IsFullDim) :
    affineSpan ℝ (P.vertices : Set (E d)) = ⊤ := by
  rw [← affineSpan_convexHull]
  exact fullDim_affineSpan_body P hP

theorem affine_eq_zero_of_body (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P.toSet, f x = 0) : f = 0 := by
  have heq : Set.EqOn (⇑f) (⇑(0 : E d →ᵃ[ℝ] ℝ)) P.toSet := hf
  have heq' := AffineMap.eqOn_affineSpan (k := ℝ) heq
  rw [fullDim_affineSpan_body P hP] at heq'
  ext x
  exact heq' (by simp)

theorem affine_eq_zero_of_vertices (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P.vertices, f x = 0) : f = 0 := by
  have heq : Set.EqOn (⇑f) (⇑(0 : E d →ᵃ[ℝ] ℝ)) (P.vertices : Set (E d)) := hf
  have heq' := AffineMap.eqOn_affineSpan (k := ℝ) heq
  rw [fullDim_affineSpan_vertices P hP] at heq'
  ext x
  exact heq' (by simp)

theorem affineZeroFace_ne_body_of_ne_zero (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d →ᵃ[ℝ] ℝ) (x : E d) (hx : f x ≠ 0) :
    affineZeroFace P f ≠ P.toSet := by
  intro heq
  have hf := affine_eq_zero_of_body P hP f (by
    intro y hy
    have h : y ∈ affineZeroFace P f := heq.symm ▸ hy
    exact h.2)
  exact hx (congrArg (fun a : E d →ᵃ[ℝ] ℝ => a x) hf)

theorem affineZeroFace_ne_body_of_negative (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d →ᵃ[ℝ] ℝ) (x : E d) (hx : f x < 0) :
    affineZeroFace P f ≠ P.toSet :=
  affineZeroFace_ne_body_of_ne_zero P hP f x (ne_of_lt hx)

/-- A face of codimension at least two and one extra point lie in the
zero set of a nonzero affine form. -/
theorem affine_form_vanishing_on_face_and_point
    (F : Set (E d)) (x : E d) (hgap : faceDim F + 2 ≤ d) :
    ∃ h : E d →ᵃ[ℝ] ℝ, h ≠ 0 ∧ h x = 0 ∧ ∀ y ∈ F, h y = 0 := by
  let U := vectorSpan ℝ (insert x F)
  have hdim : finrank ℝ U < finrank ℝ (E d) := by
    have hi := finrank_vectorSpan_insert_le_set (k := ℝ) F x
    rw [finrank_euclideanSpace_fin]
    change finrank ℝ (vectorSpan ℝ (insert x F)) < d
    change finrank ℝ (vectorSpan ℝ F) + 2 ≤ d at hgap
    omega
  obtain ⟨v, hv⟩ : ∃ v : E d, v ∉ U := by
    by_contra hall
    push_neg at hall
    have htop : U = ⊤ := SetLike.ext fun y => by simp [hall y]
    rw [htop, finrank_top] at hdim
    exact (lt_irrefl _) hdim
  obtain ⟨l, hlv, hU⟩ := Submodule.exists_le_ker_of_notMem hv
  let h : E d →ᵃ[ℝ] ℝ := l.toAffineMap - AffineMap.const ℝ (E d) (l x)
  have happly (y : E d) : h y = l (y - x) := by
    change l y - l x = l (y - x)
    rw [map_sub]
  refine ⟨h, ?_, ?_, ?_⟩
  · intro hz
    have hzero := congrArg (fun f : E d →ᵃ[ℝ] ℝ => f (v + x)) hz
    rw [happly] at hzero
    simp only [add_sub_cancel_right, AffineMap.coe_zero, Pi.zero_apply] at hzero
    exact hlv hzero
  · rw [happly, sub_self, map_zero]
  · intro y hy
    rw [happly]
    exact hU (vsub_mem_vectorSpan ℝ (Set.mem_insert_of_mem x hy) (Set.mem_insert x F))

theorem positive_vanishing_pivot_form
    (P : ConvexPolytope d) (hP : P.IsFullDim) (F : Set (E d)) (x : E d)
    (hgap : faceDim F + 2 ≤ d) :
    ∃ h : E d →ᵃ[ℝ] ℝ, h x = 0 ∧ (∀ y ∈ F, h y = 0) ∧
      ∃ v ∈ P.vertices, 0 < h v := by
  obtain ⟨h, hn, hx, hF⟩ := affine_form_vanishing_on_face_and_point F x hgap
  obtain ⟨v, hv, hnv⟩ : ∃ v ∈ P.vertices, h v ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hn (affine_eq_zero_of_vertices P hP h hall)
  rcases lt_or_gt_of_ne hnv with hneg | hpos
  · refine ⟨-h, ?_, ?_, v, hv, ?_⟩
    · change -h x = 0
      rw [hx, neg_zero]
    · intro y hy
      change -h y = 0
      rw [hF y hy, neg_zero]
    · exact neg_pos.mpr hneg
  · exact ⟨h, hx, hF, v, hv, hpos⟩

/-- A finite ratio pivot enlarges the exposed zero face and keeps the
chosen exterior point strictly on the negative side. -/
theorem enlarge_supported_face
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (F : Set (E d)) (hF : P.IsFace F) (f : E d →ᵃ[ℝ] ℝ)
    (hf : SupportsFace P F f) (x : E d) (hx : f x ≠ 0)
    (hgap : faceDim F + 2 ≤ d) :
    ∃ G : Set (E d), ∃ g : E d →ᵃ[ℝ] ℝ,
      P.IsFace G ∧ SupportsFace P G g ∧ F ⊂ G ∧ G ≠ P.toSet ∧ g x = f x := by
  classical
  obtain ⟨h, hx0, hF0, v, hv, hvpos⟩ := positive_vanishing_pivot_form P hP F x hgap
  let S := P.vertices.filter (fun y => 0 < h y)
  have hS : S.Nonempty := ⟨v, Finset.mem_filter.mpr ⟨hv, hvpos⟩⟩
  let r : E d → ℝ := fun y => f y / h y
  have hr : ∀ y ∈ S, 0 < r y := by
    intro y hy
    obtain ⟨hyP, hyp⟩ := Finset.mem_filter.mp hy
    have hbody : y ∈ P.toSet := subset_convexHull ℝ _ hyP
    have hfy : 0 < f y := by
      rcases lt_or_eq_of_le (hf.1 y hbody) with ht | he
      · exact ht
      · have hyF := (hf.mem_iff y).mpr ⟨hbody, he.symm⟩
        rw [hF0 y hyF] at hyp
        exact False.elim ((lt_irrefl _) hyp)
    exact div_pos hfy hyp
  let R := S.image r
  have hR : R.Nonempty := hS.image r
  let τ := R.min' hR
  have hτmem : τ ∈ R := Finset.min'_mem R hR
  obtain ⟨w, hwS, hwτ⟩ := Finset.mem_image.mp hτmem
  have hτ : 0 < τ := hwτ ▸ hr w hwS
  let g : E d →ᵃ[ℝ] ℝ := f - τ • h
  have gapply (y : E d) : g y = f y - τ * h y := rfl
  have hgV : ∀ y ∈ P.vertices, 0 ≤ g y := by
    intro y hy
    have hfy := hf.1 y (subset_convexHull ℝ _ hy)
    rw [gapply]
    by_cases hhy : 0 < h y
    · have hyS : y ∈ S := Finset.mem_filter.mpr ⟨hy, hhy⟩
      have hle : τ ≤ r y := Finset.min'_le R (r y) (Finset.mem_image_of_mem r hyS)
      have hm : τ * h y ≤ f y := (le_div_iff₀ hhy).mp hle
      exact sub_nonneg.mpr hm
    · have hm : τ * h y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hτ.le (le_of_not_gt hhy)
      linarith
  have hgP : ∀ y ∈ P.toSet, 0 ≤ g y := affine_nonneg_on_hull P.vertices g hgV
  have hgF : ∀ y ∈ F, g y = 0 := by
    intro y hy
    rw [gapply, hf.eq_zero hy, hF0 y hy, mul_zero, sub_zero]
  have hgx : g x = f x := by rw [gapply, hx0, mul_zero, sub_zero]
  let G := affineZeroFace P g
  have hsub : F ⊆ G := fun y hy => ⟨face_subset_toSet P hF hy, hgF y hy⟩
  have hneG : G.Nonempty := hF.2.mono hsub
  have hG : P.IsFace G := affineZeroFace_isFace P g hgP hneG
  have hwP : w ∈ P.vertices := (Finset.mem_filter.mp hwS).1
  have hwp : 0 < h w := (Finset.mem_filter.mp hwS).2
  have hwg : g w = 0 := by
    rw [gapply, ← hwτ]
    dsimp only [r]
    rw [div_mul_cancel₀ _ (ne_of_gt hwp), sub_self]
  have hwF : w ∉ F := by
    intro hw
    rw [hF0 w hw] at hwp
    exact (lt_irrefl _) hwp
  refine ⟨G, g, hG, ⟨hgP, rfl⟩, ?_,
    affineZeroFace_ne_body_of_ne_zero P hP g x (hgx.trans_ne hx), hgx⟩
  apply Set.ssubset_iff_subset_ne.mpr
  refine ⟨hsub, ?_⟩
  intro heq
  apply hwF
  rw [heq]
  exact ⟨subset_convexHull ℝ _ hwP, hwg⟩

theorem facet_containing_preserving_value
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (F : Set (E d)) (hF : P.IsFace F) (f : E d →ᵃ[ℝ] ℝ)
    (hf : SupportsFace P F f) (x : E d) (hx : f x ≠ 0) :
    ∃ G : Set (E d), ∃ g : E d →ᵃ[ℝ] ℝ,
      IsFacet P G ∧ SupportsFace P G g ∧ F ⊆ G ∧ g x = f x := by
  suffices H : ∀ k : ℕ, ∀ (F : Set (E d)) (f : E d →ᵃ[ℝ] ℝ),
      P.IsFace F → SupportsFace P F f → f x ≠ 0 →
      d - 1 - faceDim F ≤ k →
      ∃ G : Set (E d), ∃ g : E d →ᵃ[ℝ] ℝ,
        IsFacet P G ∧ SupportsFace P G g ∧ F ⊆ G ∧ g x = f x by
    exact H (d - 1 - faceDim F) F f hF hf hx le_rfl
  intro k
  induction k with
  | zero =>
    intro F f hF hf hx hk
    have hproper : F ≠ P.toSet := by
      rw [hf.2]
      exact affineZeroFace_ne_body_of_ne_zero P hP f x hx
    have hlt := faceDim_lt_of_ssubset P hF (toSet_isFace P)
      (Set.ssubset_iff_subset_ne.mpr ⟨face_subset_toSet P hF, hproper⟩)
    change faceDim F < P.dim at hlt
    have hd : faceDim F + 1 = P.dim := by rw [hP] at hlt ⊢; omega
    exact ⟨F, f, ⟨hF, hd⟩, hf, Set.Subset.rfl, rfl⟩
  | succ k ih =>
    intro F f hF hf hx hk
    by_cases heq : faceDim F + 1 = P.dim
    · exact ⟨F, f, ⟨hF, heq⟩, hf, Set.Subset.rfl, rfl⟩
    have hproper : F ≠ P.toSet := by
      rw [hf.2]
      exact affineZeroFace_ne_body_of_ne_zero P hP f x hx
    have hlt := faceDim_lt_of_ssubset P hF (toSet_isFace P)
      (Set.ssubset_iff_subset_ne.mpr ⟨face_subset_toSet P hF, hproper⟩)
    change faceDim F < P.dim at hlt
    have hgap : faceDim F + 2 ≤ d := by rw [hP] at hlt heq; omega
    obtain ⟨G, g, hG, hg, hFG, _, hgx⟩ := enlarge_supported_face P hP F hF f hf x hx hgap
    have hdim := faceDim_lt_of_ssubset P hF hG hFG
    obtain ⟨H, k, hH, hk, hGH, hkx⟩ := ih G g hG hg (hgx.trans_ne hx) (by omega)
    exact ⟨H, k, hH, hk, hFG.1.trans hGH, hkx.trans hgx⟩

theorem separating_facet_of_separating_face
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (F : Set (E d)) (hF : P.IsFace F) (f : E d →ᵃ[ℝ] ℝ)
    (hf : SupportsFace P F f) (x : E d) (hx : f x < 0) :
    ∃ G : Set (E d), ∃ g : E d →ᵃ[ℝ] ℝ,
      IsFacet P G ∧ SupportsFace P G g ∧ g x < 0 := by
  obtain ⟨G, g, hG, hg, _, hval⟩ :=
    facet_containing_preserving_value P hP F hF f hf x (ne_of_lt hx)
  exact ⟨G, g, hG, hg, hval.trans_lt hx⟩

theorem exists_facet_containing_not_mem
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (F : Set (E d)) (hF : P.IsFace F)
    (x : E d) (hx : x ∈ P.toSet) (hxF : x ∉ F) :
    ∃ G : Set (E d), IsFacet P G ∧ F ⊆ G ∧ x ∉ G := by
  obtain ⟨f, hf⟩ := exists_supportsFace P hF
  have hfx : f x ≠ 0 := fun heq => hxF ((hf.mem_iff x).mpr ⟨hx, heq⟩)
  obtain ⟨G, g, hG, hg, hFG, hval⟩ :=
    facet_containing_preserving_value P hP F hF f hf x hfx
  exact ⟨G, hG, hFG, fun hxG => hfx (hval.symm.trans (hg.eq_zero hxG))⟩

/-- Every nonempty geometric face is the intersection, inside the body,
of the facets containing it.  The statement includes the whole body. -/
theorem face_eq_inter_facets (P : ConvexPolytope d) (hP : P.IsFullDim)
    (F : Set (E d)) (hF : P.IsFace F) :
    F = {x ∈ P.toSet | ∀ G : Set (E d), IsFacet P G → F ⊆ G → x ∈ G} := by
  ext x
  constructor
  · intro hx
    exact ⟨face_subset_toSet P hF hx, fun _ _ hFG => hFG hx⟩
  · rintro ⟨hx, hall⟩
    by_contra hxF
    obtain ⟨G, hG, hFG, hxG⟩ := exists_facet_containing_not_mem P hP F hF x hx hxF
    exact hxG (hall G hG hFG)

theorem exists_separating_facet (P : ConvexPolytope d) (hP : P.IsFullDim)
    (x : E d) (hx : x ∉ P.toSet) :
    ∃ F : Set (E d), ∃ f : E d →ᵃ[ℝ] ℝ,
      IsFacet P F ∧ SupportsFace P F f ∧ f x < 0 := by
  obtain ⟨l, c, hbound, hcx⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (P.vertices : Set (E d)))
    (P.vertices.finite_toSet.isClosed_convexHull ℝ) hx
  obtain ⟨v, hv, hmax⟩ := P.vertices.exists_max_image l P.vertices_nonempty
  let f : E d →ᵃ[ℝ] ℝ := AffineMap.const ℝ (E d) (l v) - l.toLinearMap.toAffineMap
  have hf : ∀ y ∈ P.toSet, 0 ≤ f y := by
    intro y hy
    have hm := le_su_toSet P l hmax y hy
    change 0 ≤ l v - l y
    linarith
  have hne : (affineZeroFace P f).Nonempty := by
    refine ⟨v, subset_convexHull ℝ _ hv, ?_⟩
    change l v - l v = 0
    exact sub_self _
  have hfx : f x < 0 := by
    have hvlt := hbound v (subset_convexHull ℝ _ hv)
    change l v - l x < 0
    linarith
  exact separating_facet_of_separating_face P hP (affineZeroFace P f)
    (affineZeroFace_isFace P f hf hne) f ⟨hf, rfl⟩ x hfx

/-- The geometric halfspace representation is derived from the finite
convex hull, and includes every point of the ambient space. -/
theorem mem_body_iff_facet_supports_nonneg (P : ConvexPolytope d) (hP : P.IsFullDim)
    (x : E d) :
    x ∈ P.toSet ↔ ∀ (F : Set (E d)) (f : E d →ᵃ[ℝ] ℝ),
      IsFacet P F → SupportsFace P F f → 0 ≤ f x := by
  constructor
  · intro hx F f _ hf
    exact hf.1 x hx
  · intro h
    by_contra hx
    obtain ⟨F, f, hF, hf, hfx⟩ := exists_separating_facet P hP x hx
    exact (not_lt_of_ge (h F f hF hf)) hfx

end Papers.Polytopes

end
end
end BundlePart4

section BundlePart5
/- Source: Papers/FieldCoordinates.lean -/







@[expose] public section

/-!
# Field changes and homogeneous coordinates

Finite coordinate matrices have the same linear-dependence relations after
an embedding of fields. The proof extends an independent rectangular family
to a square basis, then uses the determinant and its functoriality. This
supplies the field-of-definition step in the projective reconstruction.
-/

noncomputable section

namespace Papers.Coordinates

section Homogeneous

variable {K V ι : Type*} [CommRing K] [AddCommGroup V] [Module K V]

def homogenize (p : V) : V × K := (p, 1)

theorem linearIndependent_homogenize_iff (p : ι → V) :
    LinearIndependent K (fun i => homogenize (K := K) (p i)) ↔ AffineIndependent K p := by
  rw [linearIndependent_iff', affineIndependent_iff]
  constructor
  · intro h s w hw hsum i hi
    apply h s w ?_ i hi
    apply Prod.ext
    · simpa only [Prod.fst_sum, Prod.smul_fst, homogenize, Prod.fst_zero] using hsum
    · simpa only [Prod.snd_sum, Prod.smul_snd, homogenize, smul_eq_mul, mul_one,
        Prod.snd_zero] using hw
  · intro h s w hsum i hi
    have hw := congrArg Prod.snd hsum
    have hp := congrArg Prod.fst hsum
    simp only [Prod.snd_sum, Prod.smul_snd, homogenize, smul_eq_mul, mul_one,
      Prod.snd_zero] at hw
    simp only [Prod.fst_sum, Prod.smul_fst, homogenize, Prod.fst_zero] at hp
    exact h s w hw hp i hi

end Homogeneous

section FieldEmbedding

variable {K L : Type*} [Field K] [Field L]

theorem linearIndependent_coordinate_map {m n : ℕ} (σ : K →+* L)
    (p : Fin m → Fin n → K) (hp : LinearIndependent K p) :
    LinearIndependent L (fun i j => σ (p i j)) := by
  have step : ∀ k m, ∀ p : Fin m → Fin n → K, n - m = k → LinearIndependent K p →
      LinearIndependent L (fun i j => σ (p i j)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro m p hnm hp
      have hle : m ≤ n := by simpa using hp.fintype_card_le_finrank
      rcases lt_or_eq_of_le hle with hlt | heq
      · obtain ⟨w, hw⟩ := exists_linearIndependent_snoc_of_lt_finrank hp
          (by simpa using hlt)
        have hcast := ih (n - (m + 1)) (by omega) (m + 1) (Fin.snoc p w) rfl hw
        change LinearIndependent L
          ((fun x : Fin n → K => fun j => σ (x j)) ∘ Fin.snoc p w) at hcast
        rw [Fin.comp_snoc] at hcast
        exact (linearIndependent_finSnoc.mp hcast).1
      · subst m
        have hdet : Matrix.det (Matrix.of p) ≠ 0 := Matrix.nonsingular_iff_det_ne_zero.mp
          (Matrix.Nonsingular.of_linearIndependent_row hp)
        apply Matrix.linearIndependent_rows_of_det_ne_zero (A := σ.mapMatrix (Matrix.of p))
        rw [← σ.map_det]
        intro hzero
        exact hdet (σ.injective (by simpa using hzero))
  exact step (n - m) m p rfl hp

theorem linearIndependent_of_coordinate_map {m n : ℕ} (σ : K →+* L)
    (p : Fin m → Fin n → K) (hp : LinearIndependent L (fun i j => σ (p i j))) :
    LinearIndependent K p := by
  rw [linearIndependent_iff']
  intro s w hsum i hi
  have hmap : ∑ j ∈ s, σ (w j) • (fun k => σ (p j k)) = (0 : Fin n → L) := by
    ext k
    have h := congrArg σ (congrFun hsum k)
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      map_sum, map_mul, map_zero] using h
  have hzero := (linearIndependent_iff'.mp hp) s (fun j => σ (w j)) hmap i hi
  exact σ.injective (by simpa using hzero)

/-- Both directions are needed: real geometric dependence can be transported
back to the field in which the coordinate entries lie. -/
theorem linearIndependent_coordinate_map_iff {m n : ℕ} (σ : K →+* L)
    (p : Fin m → Fin n → K) :
    LinearIndependent L (fun i j => σ (p i j)) ↔ LinearIndependent K p :=
  ⟨linearIndependent_of_coordinate_map σ p, linearIndependent_coordinate_map σ p⟩

end FieldEmbedding

end Papers.Coordinates

end
end
end BundlePart5

section BundlePart6
/- Source: Papers/HomogeneousSpan.lean -/



@[expose] public section

/-! The exact relation between affine dimension and homogeneous linear rank. -/

noncomputable section
namespace Papers.Coordinates
open Set
open scoped Pointwise

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def homogeneousSpan (S : Set V) : Submodule K (V × K) :=
  Submodule.span K (homogenize (K := K) '' S)

theorem homogenize_mem_span {S : Set V} {p : V} (hp : p ∈ S) :
    homogenize (K := K) p ∈ homogeneousSpan (K := K) S :=
  Submodule.subset_span (Set.mem_image_of_mem _ hp)

theorem direction_lift_mem_homogeneousSpan {S : Set V} {v : V}
    (hv : v ∈ vectorSpan K S) : (v, (0 : K)) ∈ homogeneousSpan (K := K) S := by
  rw [vectorSpan_def] at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨p, hp, q, hq, rfl⟩ := Set.mem_vsub.mp hv
    have h := (homogeneousSpan (K := K) S).sub_mem
      (homogenize_mem_span hp) (homogenize_mem_span hq)
    simpa only [homogenize, Prod.mk_sub_mk, sub_self, vsub_eq_sub] using h
  | zero => exact (homogeneousSpan (K := K) S).zero_mem
  | add x y hx hy ihx ihy =>
    simpa only [Prod.mk_add_mk, add_zero] using
      (homogeneousSpan (K := K) S).add_mem ihx ihy
  | smul c x hx ih =>
    simpa only [Prod.smul_mk, smul_zero] using
      (homogeneousSpan (K := K) S).smul_mem c ih

def homogeneousParam (S : Set V) (p₀ : V) :
    (vectorSpan K S × K) →ₗ[K] (V × K) where
  toFun z := (z.1.val + z.2 • p₀, z.2)
  map_add' x y := by
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, add_smul]
      module
    · rfl
  map_smul' c x := by
    apply Prod.ext
    · simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, smul_add, smul_smul]
      rfl
    · rfl

theorem homogeneousParam_injective (S : Set V) (p₀ : V) :
    Function.Injective (homogeneousParam (K := K) S p₀) := by
  rintro ⟨v, c⟩ ⟨w, d⟩ heq
  have hcd : c = d := congrArg Prod.snd heq
  subst d
  apply Prod.ext
  · apply Subtype.ext
    exact add_right_cancel (show v.val + c • p₀ = w.val + c • p₀ from
      congrArg Prod.fst heq)
  · rfl

theorem homogeneousSpan_eq_range {S : Set V} {p₀ : V} (hp₀ : p₀ ∈ S) :
    homogeneousSpan (K := K) S = (homogeneousParam (K := K) S p₀).range := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨(⟨p - p₀, ?_⟩, 1), ?_⟩
    · exact vsub_mem_vectorSpan K hp hp₀
    · simp [homogeneousParam, homogenize]
  · rintro _ ⟨⟨v, c⟩, rfl⟩
    have h₁ := direction_lift_mem_homogeneousSpan (K := K) v.property
    have h₂ := (homogeneousSpan (K := K) S).smul_mem c (homogenize_mem_span hp₀)
    simpa [homogeneousParam, homogenize] using (homogeneousSpan (K := K) S).add_mem h₁ h₂

/-- A homogeneous vector of last coordinate one is in the homogeneous span
exactly when its affine point is in the original affine span. -/
theorem homogenize_mem_span_iff {S : Set V} (hS : S.Nonempty) (p : V) :
    homogenize (K := K) p ∈ homogeneousSpan (K := K) S ↔ p ∈ affineSpan K S := by
  obtain ⟨p₀, hp₀⟩ := hS
  constructor
  · intro hp
    rw [homogeneousSpan_eq_range hp₀] at hp
    obtain ⟨⟨v, c⟩, hv⟩ := hp
    have hc : c = 1 := congrArg Prod.snd hv
    subst c
    apply (mem_affineSpan_iff_exists K).mpr
    refine ⟨p₀, hp₀, v.val, v.property, ?_⟩
    have hv' := congrArg Prod.fst hv
    simpa [homogeneousParam, homogenize] using hv'.symm
  · intro hp
    obtain ⟨q, hq, v, hv, rfl⟩ := (mem_affineSpan_iff_exists K).mp hp
    have h₁ := direction_lift_mem_homogeneousSpan (K := K) hv
    have h₂ := homogenize_mem_span (K := K) hq
    simpa [homogenize, vadd_eq_add] using (homogeneousSpan (K := K) S).add_mem h₁ h₂

/-- Nonempty affine sets gain exactly one dimension on homogenization. -/
theorem finrank_homogeneousSpan [FiniteDimensional K V] {S : Set V}
    (hS : S.Nonempty) :
    Module.finrank K (homogeneousSpan (K := K) S) =
      Module.finrank K (vectorSpan K S) + 1 := by
  obtain ⟨p₀, hp₀⟩ := hS
  rw [homogeneousSpan_eq_range hp₀,
    LinearMap.finrank_range_of_inj (homogeneousParam_injective S p₀),
    Module.finrank_prod]
  simp

end Papers.Coordinates

end
end
end BundlePart6

section BundlePart7
/- Source: Papers/AffineHomogeneousValues.lean -/






@[expose] public section

/-!
# Homogeneous points specified by affine forms

An ordinary homogeneous vector `(x,t)` evaluates an affine form `f` as
`f.linear x + t * f 0`.  In finite dimension this identifies homogeneous
vectors with the dual of the space of affine forms.  Consequently a basis
of affine forms can be assigned arbitrary values over the same field.
The identification is explicit and does not assume an affine chart is
already available.
-/

noncomputable section
namespace Papers.AffineCoordinates

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def linearToAffine : (V →ₗ[K] K) →ₗ[K] (V →ᵃ[K] K) where
  toFun f := f.toAffineMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem linearToAffine_apply (f : V →ₗ[K] K) (x : V) :
    linearToAffine f x = f x := rfl

theorem affine_decomposition (f : V →ᵃ[K] K) :
    f = linearToAffine f.linear + f 0 • AffineMap.const K V (1 : K) := by
  ext x
  have h := f.map_vadd (0 : V) x
  simpa only [vadd_eq_add, add_zero, AffineMap.coe_add, Pi.add_apply,
    linearToAffine_apply, AffineMap.coe_smul, Pi.smul_apply,
    AffineMap.coe_const, Function.const_apply, smul_eq_mul, mul_one] using h

def homogeneousEvaluation : (V × K) →ₗ[K] Module.Dual K (V →ᵃ[K] K) where
  toFun z :=
    { toFun := fun f => f.linear z.1 + z.2 * f 0
      map_add' := by
        intro f g
        simp only [AffineMap.add_linear, LinearMap.add_apply, AffineMap.coe_add,
          Pi.add_apply, mul_add]
        ring
      map_smul' := by
        intro c f
        simp only [AffineMap.smul_linear, LinearMap.smul_apply, AffineMap.coe_smul,
          Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  map_add' := by
    intro z w
    apply LinearMap.ext
    intro f
    change f.linear (z.1 + w.1) + (z.2 + w.2) * f 0 =
      (f.linear z.1 + z.2 * f 0) + (f.linear w.1 + w.2 * f 0)
    rw [map_add]
    ring
  map_smul' := by
    intro c z
    apply LinearMap.ext
    intro f
    change f.linear (c • z.1) + (c * z.2) * f 0 =
      c * (f.linear z.1 + z.2 * f 0)
    rw [map_smul, smul_eq_mul]
    ring

@[simp] theorem homogeneousEvaluation_apply (z : V × K) (f : V →ᵃ[K] K) :
    homogeneousEvaluation z f = f.linear z.1 + z.2 * f 0 := rfl

@[simp] theorem homogeneousEvaluation_homogenize (x : V) (f : V →ᵃ[K] K) :
    homogeneousEvaluation (x, (1 : K)) f = f x := by
  have h := f.map_vadd (0 : V) x
  simpa only [homogeneousEvaluation_apply, vadd_eq_add, add_zero, one_mul] using h.symm

@[simp] theorem homogeneousEvaluation_const (z : V × K) (c : K) :
    homogeneousEvaluation z (AffineMap.const K V c) = z.2 * c := by
  simp [homogeneousEvaluation]

@[simp] theorem homogeneousEvaluation_linear (z : V × K) (f : V →ₗ[K] K) :
    homogeneousEvaluation z (linearToAffine f) = f z.1 := by
  change f z.1 + z.2 * f 0 = f z.1
  rw [map_zero, mul_zero, add_zero]

variable [FiniteDimensional K V]

theorem homogeneousEvaluation_injective :
    Function.Injective (homogeneousEvaluation (K := K) (V := V)) := by
  intro z w heq
  apply Prod.ext
  · apply (Module.evalEquiv K V).injective
    ext f
    have h := congrArg (fun a : Module.Dual K (V →ᵃ[K] K) => a (linearToAffine f)) heq
    simpa only [Module.evalEquiv_apply, Module.Dual.eval_apply,
      homogeneousEvaluation_linear] using h
  · have h := congrArg
      (fun a : Module.Dual K (V →ᵃ[K] K) => a (AffineMap.const K V (1 : K))) heq
    simpa only [homogeneousEvaluation_const, mul_one] using h

theorem homogeneousEvaluation_surjective :
    Function.Surjective (homogeneousEvaluation (K := K) (V := V)) := by
  intro a
  let x : V := (Module.evalEquiv K V).symm (a.comp linearToAffine)
  let t : K := a (AffineMap.const K V (1 : K))
  refine ⟨(x, t), ?_⟩
  ext f
  have hx : f.linear x = a (linearToAffine f.linear) := by
    simpa only [x, LinearMap.comp_apply] using
      Module.apply_evalEquiv_symm_apply K V f.linear (a.comp linearToAffine)
  calc
    homogeneousEvaluation (x, t) f = a (linearToAffine f.linear) +
        a (AffineMap.const K V (1 : K)) * f 0 := by rw [homogeneousEvaluation_apply, hx]
    _ = a (linearToAffine f.linear + f 0 • AffineMap.const K V (1 : K)) := by
      rw [map_add, map_smul, smul_eq_mul]
      ring
    _ = a f := congrArg a (affine_decomposition f).symm

def homogeneousEvaluationEquiv :
    (V × K) ≃ₗ[K] Module.Dual K (V →ᵃ[K] K) :=
  LinearEquiv.ofBijective homogeneousEvaluation
    ⟨homogeneousEvaluation_injective, homogeneousEvaluation_surjective⟩

variable {ι : Type*}

def realizeAffineValues (b : Basis ι K (V →ᵃ[K] K)) (r : ι → K) : V × K :=
  homogeneousEvaluationEquiv.symm (b.constr K r)

@[simp] theorem realizeAffineValues_evaluation
    (b : Basis ι K (V →ᵃ[K] K)) (r : ι → K) (f : V →ᵃ[K] K) :
    homogeneousEvaluation (realizeAffineValues b r) f = b.constr K r f := by
  have h := homogeneousEvaluationEquiv.apply_symm_apply (b.constr K r)
  exact congrArg (fun a : Module.Dual K (V →ᵃ[K] K) => a f) h

@[simp] theorem realizeAffineValues_basis
    (b : Basis ι K (V →ᵃ[K] K)) (r : ι → K) (i : ι) :
    homogeneousEvaluation (realizeAffineValues b r) (b i) = r i := by
  rw [realizeAffineValues_evaluation, Basis.constr_basis]

theorem homogeneousEvaluation_expansion [Fintype ι]
    (b : Basis ι K (V →ᵃ[K] K)) (z : V × K) (f : V →ᵃ[K] K) :
    homogeneousEvaluation z f =
      ∑ i, b.repr f i * homogeneousEvaluation z (b i) := by
  conv_lhs => rw [← b.sum_repr f]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]

theorem realizeAffineValues_expansion [Fintype ι]
    (b : Basis ι K (V →ᵃ[K] K)) (r : ι → K) (f : V →ᵃ[K] K) :
    homogeneousEvaluation (realizeAffineValues b r) f = ∑ i, b.repr f i * r i := by
  rw [homogeneousEvaluation_expansion b]
  simp only [realizeAffineValues_basis]

def affineLift (f : V →ᵃ[K] K) : (V × K) →ₗ[K] K where
  toFun z := homogeneousEvaluation z f
  map_add' z w := by
    exact congrArg (fun a : Module.Dual K (V →ᵃ[K] K) => a f)
      (homogeneousEvaluation.map_add z w)
  map_smul' c z := by
    exact congrArg (fun a : Module.Dual K (V →ᵃ[K] K) => a f)
      (homogeneousEvaluation.map_smul c z)

def affineDehomogenize (l : (V × K) →ₗ[K] K) : V →ᵃ[K] K where
  toFun x := l (x, 1)
  linear := l.comp (LinearMap.inl K V K)
  map_vadd' p v := by
    change l (v + p, (1 : K)) = l (v, 0) + l (p, 1)
    rw [← map_add]
    exact congrArg l (Prod.ext rfl (zero_add (1 : K)).symm)

@[simp] theorem affineLift_apply (f : V →ᵃ[K] K) (z : V × K) :
    affineLift f z = homogeneousEvaluation z f := rfl

@[simp] theorem affineDehomogenize_apply (l : (V × K) →ₗ[K] K) (x : V) :
    affineDehomogenize l x = l (x, 1) := rfl

@[simp] theorem affineDehomogenize_affineLift (f : V →ᵃ[K] K) :
    affineDehomogenize (affineLift f) = f := by
  ext x
  exact homogeneousEvaluation_homogenize x f

@[simp] theorem affineLift_affineDehomogenize (l : (V × K) →ₗ[K] K) :
    affineLift (affineDehomogenize l) = l := by
  apply LinearMap.ext
  intro z
  change l (z.1, 0) + z.2 * l (0, 1) = l z
  calc
    l (z.1, 0) + z.2 * l (0, 1) = l ((z.1, 0) + z.2 • (0, 1)) := by
      rw [map_add, map_smul, smul_eq_mul]
    _ = l z := congrArg l (by
      apply Prod.ext
      · simp only [Prod.fst_add, Prod.smul_fst, smul_zero, add_zero]
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, mul_one, zero_add])

variable {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

def projectiveTransportAffine (L : (V × K) ≃ₗ[K] (W × K)) (f : V →ᵃ[K] K) :
    W →ᵃ[K] K := affineDehomogenize ((affineLift f).comp L.symm.toLinearMap)

@[simp] theorem projectiveTransportAffine_apply
    (L : (V × K) ≃ₗ[K] (W × K)) (f : V →ᵃ[K] K) (x : W) :
    projectiveTransportAffine L f x = homogeneousEvaluation (L.symm (x, 1)) f := rfl

theorem projectiveTransportAffine_scaled
    (L : (V × K) ≃ₗ[K] (W × K)) (f : V →ᵃ[K] K)
    (x : V) (y : W) (h : K) (heq : L (x, 1) = h • (y, 1)) :
    f x = h * projectiveTransportAffine L f y := by
  have hpre : (x, (1 : K)) = h • L.symm (y, 1) := by
    have h' := congrArg L.symm heq
    simpa only [L.symm_apply_apply, map_smul] using h'
  calc
    f x = affineLift f (x, 1) := (homogeneousEvaluation_homogenize x f).symm
    _ = affineLift f (h • L.symm (y, 1)) := congrArg (affineLift f) hpre
    _ = h * projectiveTransportAffine L f y := by
      change affineLift f (h • L.symm (y, 1)) = h * affineLift f (L.symm (y, 1))
      rw [map_smul, smul_eq_mul]

theorem projectiveTransportAffine_inverse
    (L : (V × K) ≃ₗ[K] (W × K)) (f : V →ᵃ[K] K) :
    projectiveTransportAffine L.symm (projectiveTransportAffine L f) = f := by
  unfold projectiveTransportAffine
  rw [affineLift_affineDehomogenize]
  have hcomp : ((affineLift f).comp L.symm.toLinearMap).comp
      L.symm.symm.toLinearMap = affineLift f := by
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_symm,
      LinearEquiv.symm_apply_apply]
  rw [hcomp, affineDehomogenize_affineLift]

end Papers.AffineCoordinates

end
end
end BundlePart7

section BundlePart8
/- Source: Papers/FacetNormalization.lean -/






@[expose] public section

/-!
# Uniqueness of an oriented facet form

The homogeneous span of a facet is exactly the kernel of any nonzero
supporting form.  Consequently two inward forms for the same actual facet
are positive scalar multiples.  A single chosen form for each facet is
therefore a complete halfspace representation of the polytope.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open Papers.AffineCoordinates Papers.Coordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem linear_form_eq_scalar_of_ker_le
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f g : V →ₗ[K] K) (z : V) (hz : g z ≠ 0) (hker : g.ker ≤ f.ker) :
    f = (f z / g z) • g := by
  ext x
  have hmem : x - (g x / g z) • z ∈ g.ker := by
    change g (x - (g x / g z) • z) = 0
    rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hz, sub_self]
  have h := hker hmem
  change f (x - (g x / g z) • z) = 0 at h
  rw [map_sub, map_smul, smul_eq_mul] at h
  change f x = (f z / g z) * g x
  calc
    f x = (g x / g z) * f z := sub_eq_zero.mp h
    _ = (f z / g z) * g x := by ring

theorem affineLift_surjective {f : E d →ᵃ[ℝ] ℝ} (hf : f ≠ 0) :
    Function.Surjective (affineLift f) := by
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h
    push_neg at h
    apply hf
    ext x
    exact h x
  intro t
  refine ⟨(t / f x) • (x, (1 : ℝ)), ?_⟩
  rw [map_smul, smul_eq_mul, affineLift_apply, homogeneousEvaluation_homogenize,
    div_mul_cancel₀ _ hx]

theorem homogeneousSpan_facet_eq_ker
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (F : Set (E d)) (hF : IsFacet P F)
    (f : E d →ᵃ[ℝ] ℝ) (hf : SupportsFace P F f) :
    homogeneousSpan (K := ℝ) F = (affineLift f).ker := by
  have hle : homogeneousSpan (K := ℝ) F ≤ (affineLift f).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    change homogeneousEvaluation (x, (1 : ℝ)) f = 0
    rw [homogeneousEvaluation_homogenize, hf.eq_zero hx]
  have hdimF : finrank ℝ (homogeneousSpan (K := ℝ) F) = d := by
    rw [finrank_homogeneousSpan hF.1.2]
    change faceDim F + 1 = d
    exact hF.2.trans hP
  have hrange : (affineLift f).range = ⊤ :=
    LinearMap.range_eq_top.mpr (affineLift_surjective (hF.support_ne_zero hf))
  have hdim := (affineLift f).finrank_range_add_finrank_ker
  rw [hrange, finrank_top, finrank_self, finrank_prod,
    finrank_euclideanSpace_fin, finrank_self] at hdim
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [hdimF]
  omega

theorem supportsFacet_positive_proportional
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (F : Set (E d)) (hF : IsFacet P F)
    (f g : E d →ᵃ[ℝ] ℝ) (hf : SupportsFace P F f) (hg : SupportsFace P F g) :
    ∃ c : ℝ, 0 < c ∧ f = c • g := by
  obtain ⟨x, hxP, hxF⟩ : ∃ x, x ∈ P.toSet ∧ x ∉ F := by
    by_contra h
    push_neg at h
    exact hF.ne_toSet (Set.Subset.antisymm (face_subset_toSet P hF.1) h)
  have hfx : 0 < f x := lt_of_le_of_ne (hf.1 x hxP)
    (fun hz => hxF ((hf.mem_iff x).mpr ⟨hxP, hz.symm⟩))
  have hgx : 0 < g x := lt_of_le_of_ne (hg.1 x hxP)
    (fun hz => hxF ((hg.mem_iff x).mpr ⟨hxP, hz.symm⟩))
  have hker : (affineLift g).ker ≤ (affineLift f).ker := by
    rw [← homogeneousSpan_facet_eq_ker P hP F hF g hg,
      ← homogeneousSpan_facet_eq_ker P hP F hF f hf]
  have heq := linear_form_eq_scalar_of_ker_le
    (affineLift f) (affineLift g) (x, (1 : ℝ))
    (by simpa only [affineLift_apply, homogeneousEvaluation_homogenize] using ne_of_gt hgx)
    hker
  refine ⟨f x / g x, div_pos hfx hgx, ?_⟩
  ext y
  have h := congrArg (fun l : (E d × ℝ) →ₗ[ℝ] ℝ => l (y, 1)) heq
  simpa only [LinearMap.smul_apply, affineLift_apply, homogeneousEvaluation_homogenize,
    smul_eq_mul, AffineMap.coe_smul, Pi.smul_apply] using h

def FacetType (P : ConvexPolytope d) := {F : FaceType P // IsFacet P F.val}

instance facetTypeFintype (P : ConvexPolytope d) : Fintype (FacetType P) :=
  inferInstanceAs (Fintype {F : FaceType P // IsFacet P F.val})

def chosenFacetForm (P : ConvexPolytope d) (F : FacetType P) : E d →ᵃ[ℝ] ℝ :=
  Classical.choose (exists_supportsFace P F.val.property)

theorem chosenFacetForm_supports (P : ConvexPolytope d) (F : FacetType P) :
    SupportsFace P F.val.val (chosenFacetForm P F) :=
  Classical.choose_spec (exists_supportsFace P F.val.property)

theorem mem_body_iff_chosenFacetForms_nonneg
    (P : ConvexPolytope d) (hP : P.IsFullDim) (x : E d) :
    x ∈ P.toSet ↔ ∀ F : FacetType P, 0 ≤ chosenFacetForm P F x := by
  constructor
  · intro hx F
    exact (chosenFacetForm_supports P F).1 x hx
  · intro h
    apply (mem_body_iff_facet_supports_nonneg P hP x).mpr
    intro F f hF hf
    let F' : FacetType P := ⟨⟨F, hF.1⟩, hF⟩
    obtain ⟨c, hc, hfc⟩ := supportsFacet_positive_proportional P hP F hF f
      (chosenFacetForm P F') hf (chosenFacetForm_supports P F')
    rw [hfc]
    change 0 ≤ c * chosenFacetForm P F' x
    exact mul_nonneg hc.le (h F')

end Papers.Polytopes

end
end
end BundlePart8

section BundlePart9
/- Source: Papers/ActualSmallFacetIndependence.lean -/






@[expose] public section

/-! Independence of any at most three distinct actual facet forms. -/

noncomputable section
namespace Papers.Polytopes
open Set Module
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

theorem linearIndependent_fin_of_le_three
    {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (p : Fin n → V) (hn : n ≤ 3)
    (h1 : ∀ i, p i ≠ 0)
    (h2 : ∀ i j, i ≠ j → LinearIndependent ℝ ![p i,p j])
    (h3 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      LinearIndependent ℝ ![p i,p j,p k]) : LinearIndependent ℝ p := by
  interval_cases n
  · exact linearIndependent_empty_type
  · exact linearIndependent_unique_iff.mpr (h1 _)
  · convert h2 0 1 (by decide) using 1
    ext i
    fin_cases i <;> rfl
  · convert h3 0 1 2 (by decide) (by decide) (by decide) using 1
    ext i
    fin_cases i <;> rfl

variable {d : ℕ}

theorem exists_facet_point_strict_other
    (P : ConvexPolytope d) (F G : FacetType P) (hne : F ≠ G) :
    ∃ x ∈ F.val.val, 0 < chosenFacetForm P G x := by
  have hnot : ¬ F.val.val ⊆ G.val.val := by
    intro hsub
    apply hne
    apply Subtype.ext
    apply Subtype.ext
    exact F.property.eq_of_subset G.property.1 G.property.ne_toSet hsub
  obtain ⟨x,hx,hxG⟩ := Set.not_subset.mp hnot
  have hxP := face_subset_toSet P F.property.1 hx
  have hnonneg := (chosenFacetForm_supports P G).1 x hxP
  have hzero : chosenFacetForm P G x ≠ 0 := by
    intro h
    exact hxG ((chosenFacetForm_supports P G).mem_iff x |>.mpr ⟨hxP,h⟩)
  exact ⟨x,hx,lt_of_le_of_ne hnonneg hzero.symm⟩

theorem chosenFacetForm_pair_independent
    (P : ConvexPolytope d) (F G : FacetType P) (hne : F ≠ G) :
    LinearIndependent ℝ ![chosenFacetForm P F,chosenFacetForm P G] := by
  rw [linearIndependent_fin2]
  refine ⟨G.property.support_ne_zero (chosenFacetForm_supports P G),?_⟩
  intro a heq
  obtain ⟨x,hx,hpos⟩ := exists_facet_point_strict_other P G F hne.symm
  have hzero := (chosenFacetForm_supports P G).eq_zero hx
  have hh := congrArg (fun f : E d →ᵃ[ℝ] ℝ => f x) heq
  change a * chosenFacetForm P G x = chosenFacetForm P F x at hh
  rw [hzero,mul_zero] at hh
  linarith

theorem chosenFacetForms_three_independent
    (P : ConvexPolytope d) (F : Fin 3 → FacetType P)
    (hF : Function.Injective F) :
    LinearIndependent ℝ (fun i => chosenFacetForm P (F i)) := by
  apply Papers.RationalityTen.three_affineForms_independent_of_convex_supports
    (fun i => chosenFacetForm P (F i)) (fun i => (F i).val.val)
  · intro i
    exact (F i).property.1.1.convex (convex_convexHull ℝ _)
  · intro i
    exact (F i).property.1.2
  · intro i x hx
    exact (chosenFacetForm_supports P (F i)).eq_zero hx
  · intro i j x hx
    exact (chosenFacetForm_supports P (F j)).1 x
      (face_subset_toSet P (F i).property.1 hx)
  · intro i j hij
    exact exists_facet_point_strict_other P (F i) (F j) (fun h => hij (hF h))

theorem small_chosenFacetForms_independent
    {ι : Type*} [Fintype ι] (P : ConvexPolytope d)
    (F : ι → FacetType P) (hinj : Function.Injective F)
    (hcard : Fintype.card ι ≤ 3) :
    LinearIndependent ℝ (fun i => chosenFacetForm P (F i)) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hfin : LinearIndependent ℝ (fun i => chosenFacetForm P (F (e i))) := by
    apply linearIndependent_fin_of_le_three _ hcard
    · intro i
      exact (F (e i)).property.support_ne_zero (chosenFacetForm_supports P (F (e i)))
    · intro i j hij
      exact chosenFacetForm_pair_independent P _ _
        (fun h => hij (e.injective (hinj h)))
    · intro i j k hij hik hjk
      let f : Fin 3 → FacetType P := ![F (e i),F (e j),F (e k)]
      have hf : Function.Injective f := by
        intro a b hab
        have hei := fun {a b} (h : F (e a)=F (e b)) => e.injective (hinj h)
        fin_cases a <;> fin_cases b <;> simp_all [f]
        all_goals have h := hei hab; simp_all
      convert chosenFacetForms_three_independent P f hf using 1
      ext a
      fin_cases a <;> rfl
  have hh := hfin.comp e.symm e.symm.injective
  simpa only [Function.comp_def,Equiv.apply_symm_apply] using hh

end Papers.Polytopes

end
end
end BundlePart9

section BundlePart10
/- Source: Papers/ActualThreeVertexIndependence.lean -/












@[expose] public section

/-!
# Independence of any three actual extreme vertices

A nontrivial affine relation on three distinct extreme
vertices puts one of them on the segment joining the other two. The
extreme-point property forbids this, including degenerate coefficients.

The homogeneous coordinate map is explicit. No generic position or
simpliciality hypothesis is used.
-/

noncomputable section

namespace Papers.ActualThreeVertexIndependence

open Set Module
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical BigOperators

variable {d : ℕ}

theorem nonnegative_affine_relation_impossible (P : ConvexPolytope d)
    (x y z : P.vertices) (hzx : z ≠ x) (hzy : z ≠ y)
    (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : c < 0)
    (hs : a+b+c = 0)
    (hv : a • x.val + b • y.val + c • z.val = 0) : False := by
  have hab : 0 < a+b := by linarith
  have habc : a+b = -c := by linarith
  have hrel : a • x.val + b • y.val = (a+b) • z.val := by
    have h := eq_neg_of_add_eq_zero_left hv
    simpa only [habc,neg_smul] using h
  have hscaled := congrArg (fun w : E d => (a+b)⁻¹ • w) hrel
  simp only [smul_add,smul_smul,inv_mul_cancel₀ hab.ne',one_smul] at hscaled
  have hcomb : (a/(a+b)) • x.val + (b/(a+b)) • y.val = z.val := by
    simpa only [div_eq_mul_inv,mul_comm] using hscaled
  have hseg : z.val ∈ segment ℝ x.val y.val :=
    mem_segment_iff_div.mpr ⟨a,b,ha,hb,hab,hcomb⟩
  have hext := Papers.PolytopeBasicExtreme.extreme_point_on_segment P.toSet
    (Papers.PolytopeBasicExtreme.vertex_mem_extreme P z.property)
    (Papers.PolytopeBasicExtreme.vertex_mem_body P x.property)
    (Papers.PolytopeBasicExtreme.vertex_mem_body P y.property) hseg
  rcases hext with h | h
  · exact hzx (Subtype.ext h)
  · exact hzy (Subtype.ext h)

theorem three_vertex_relation_coefficients (P : ConvexPolytope d)
    (x y z : P.vertices) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (a b c : ℝ) (hs : a+b+c = 0)
    (hv : a • x.val + b • y.val + c • z.val = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have hneg : (-a) • x.val + (-b) • y.val + (-c) • z.val = 0 := by
    simpa only [neg_add,neg_zero,neg_smul] using congrArg Neg.neg hv
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · by_cases hc : 0 ≤ c
      · constructor
        · linarith
        constructor <;> linarith
      · exact (nonnegative_affine_relation_impossible P x y z hxz.symm hyz.symm
          a b c ha hb (lt_of_not_ge hc) hs hv).elim
    · have hb' : b < 0 := lt_of_not_ge hb
      by_cases hc : 0 ≤ c
      · apply (nonnegative_affine_relation_impossible P x z y hxy.symm hyz
          a c b ha hc hb' (by linarith) ?_).elim
        simpa only [add_comm,add_left_comm,add_assoc] using hv
      · have hc' : c < 0 := lt_of_not_ge hc
        apply (nonnegative_affine_relation_impossible P y z x hxy hxz
          (-b) (-c) (-a) (by linarith) (by linarith)
          (by linarith) (by linarith) ?_).elim
        simpa only [add_comm,add_left_comm,add_assoc] using hneg
  · have ha' : a < 0 := lt_of_not_ge ha
    by_cases hb : 0 ≤ b
    · by_cases hc : 0 ≤ c
      · apply (nonnegative_affine_relation_impossible P y z x hxy hxz
          b c a hb hc ha' (by linarith) ?_).elim
        simpa only [add_comm,add_left_comm,add_assoc] using hv
      · have hc' : c < 0 := lt_of_not_ge hc
        apply (nonnegative_affine_relation_impossible P x z y hxy.symm hyz
          (-a) (-c) (-b) (by linarith) (by linarith)
          (by linarith) (by linarith) ?_).elim
        simpa only [add_comm,add_left_comm,add_assoc] using hneg
    · have hb' : b < 0 := lt_of_not_ge hb
      by_cases hc : 0 ≤ c
      · apply (nonnegative_affine_relation_impossible P x y z hxz.symm hyz.symm
          (-a) (-b) (-c) (by linarith) (by linarith)
          (by linarith) (by linarith) hneg).elim
      · have hc' : c < 0 := lt_of_not_ge hc
        linarith

theorem three_vertex_affine_relation_zero (P : ConvexPolytope d)
    (v : Fin 3 → P.vertices) (hinj : Function.Injective v)
    (a : Fin 3 → ℝ) (hs : ∑ i, a i = 0)
    (hv : ∑ i, a i • (v i).val = 0) : ∀ i, a i = 0 := by
  have hxy : v 0 ≠ v 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (hinj h)
  have hxz : v 0 ≠ v 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (hinj h)
  have hyz : v 1 ≠ v 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (hinj h)
  have hs' : a 0 + a 1 + a 2 = 0 := by
    simpa [Fin.sum_univ_succ,add_assoc] using hs
  have hv' : a 0 • (v 0).val + a 1 • (v 1).val + a 2 • (v 2).val = 0 := by
    simpa [Fin.sum_univ_succ,add_assoc] using hv
  obtain ⟨h0,h1,h2⟩ := three_vertex_relation_coefficients P _ _ _ hxy hxz hyz
    _ _ _ hs' hv'
  intro i
  fin_cases i <;> assumption

def homogeneousVertex (v : E d) : Fin (d+1) → ℝ :=
  Fin.cases 1 (fun i => v i)

theorem homogeneous_three_vertices_linearIndependent (P : ConvexPolytope d)
    (v : Fin 3 → P.vertices) (hinj : Function.Injective v) :
    LinearIndependent ℝ (fun i => homogeneousVertex (v i).val) := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha
  have hs : ∑ i, a i = 0 := by
    have h := congrFun ha 0
    simpa [homogeneousVertex,Finset.sum_apply] using h
  have hv : ∑ i, a i • (v i).val = 0 := by
    ext j
    have h := congrFun ha j.succ
    simpa [homogeneousVertex,Finset.sum_apply] using h
  exact three_vertex_affine_relation_zero P v hinj a hs hv

theorem small_homogeneous_vertex_family_independent
    {ι : Type*} [Fintype ι] (P : ConvexPolytope d)
    (hP : 3 ≤ P.vertices.card) (v : ι → P.vertices)
    (hinj : Function.Injective v) (hι : Fintype.card ι ≤ 3) :
    LinearIndependent ℝ (fun i => homogeneousVertex (v i).val) := by
  let S : Finset P.vertices := Finset.univ.image v
  have hS : S.card ≤ 3 := by
    rw [Finset.card_image_of_injective _ hinj,Finset.card_univ]
    exact hι
  have htotal : 3 ≤ (Finset.univ : Finset P.vertices).card := by
    simpa only [Finset.card_univ,Fintype.card_coe] using hP
  obtain ⟨T,hST,hTU,hT⟩ :=
    Finset.exists_subsuperset_card_eq (Finset.subset_univ S) hS htotal
  let lab : T ≃ Fin 3 := (Fintype.equivFin T).trans
    (finCongr (by simpa only [Fintype.card_coe] using hT))
  let q : Fin 3 → P.vertices := fun i => (lab.symm i).val
  have hq : Function.Injective q := by
    intro i j h
    apply lab.symm.injective
    exact Subtype.ext h
  let f : ι → Fin 3 := fun i => lab ⟨v i,hST (Finset.mem_image.mpr
    ⟨i,Finset.mem_univ _,rfl⟩)⟩
  have hf : Function.Injective f := by
    intro i j h
    apply hinj
    exact congrArg Subtype.val (lab.injective h)
  have hli := (homogeneous_three_vertices_linearIndependent P q hq).comp f hf
  simpa only [Function.comp_def,q,f,Equiv.symm_apply_apply] using hli

end Papers.ActualThreeVertexIndependence

end
end
end BundlePart10

section BundlePart11
/- Source: Papers/RationalKernelCharts.lean -/








@[expose] public section

/-!
# Rational continuous charts on independent linear kernels

The projector is an explicit rational function of the coefficient matrix.
Its hypotheses are ordinary linear independence, and all rationality and
continuity statements are proved from Mathlib.  This thin module is independent
of the finite configuration classification used elsewhere in the paper.
-/

noncomputable section
open Matrix Module Set Filter Topology
open scoped BigOperators
namespace Papers.RationalKernelCharts

def RatScalar (x : ℝ) : Prop := ∃ q : ℚ, (q : ℝ) = x

theorem RatScalar.zero : RatScalar 0 := ⟨0,by simp⟩
theorem RatScalar.add {x y : ℝ} (hx : RatScalar x) (hy : RatScalar y) :
    RatScalar (x+y) := by
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  exact ⟨a+b,by simp⟩

theorem RatScalar.sub {x y : ℝ} (hx : RatScalar x) (hy : RatScalar y) :
    RatScalar (x-y) := by
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  exact ⟨a-b,by simp⟩

theorem RatScalar.mul {x y : ℝ} (hx : RatScalar x) (hy : RatScalar y) :
    RatScalar (x*y) := by
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  exact ⟨a*b,by simp⟩

theorem RatScalar.div {x y : ℝ} (hx : RatScalar x) (hy : RatScalar y) :
    RatScalar (x/y) := by
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  exact ⟨a/b,by simp⟩

theorem RatScalar.finset_sum {α : Type*} (S : Finset α) (f : α → ℝ)
    (hf : ∀ i ∈ S, RatScalar (f i)) : RatScalar (∑ i ∈ S, f i) := by
  classical
  revert hf
  induction S using Finset.induction_on with
  | empty =>
    intro hf
    simpa using RatScalar.zero
  | @insert a S ha ih =>
    intro hf
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

def RationalCoordinates {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ i j, RatScalar (A i j)

def Spans {n r : ℕ} (p : Matrix (Fin n) (Fin r) ℝ) : Prop :=
  Submodule.span ℝ (Set.range p) = ⊤

theorem spans_iff_matrix_rank {n r : ℕ} (p : Matrix (Fin n) (Fin r) ℝ) :
    Spans p ↔ Matrix.rank p = r := by
  rw [Matrix.rank_eq_finrank_span_row]
  change Submodule.span ℝ (Set.range p) = ⊤ ↔
    finrank ℝ (Submodule.span ℝ (Set.range p)) = r
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    apply Submodule.eq_top_of_finrank_eq
    simpa using h

theorem rationalCoordinates_transpose {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : RationalCoordinates A) : RationalCoordinates A.transpose :=
  fun i j => hA j i

theorem rationalCoordinates_sub {m n : ℕ} {A B : Matrix (Fin m) (Fin n) ℝ}
    (hA : RationalCoordinates A) (hB : RationalCoordinates B) :
    RationalCoordinates (A-B) := fun i j => (hA i j).sub (hB i j)

theorem rationalCoordinates_mul {m n k : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} {B : Matrix (Fin n) (Fin k) ℝ}
    (hA : RationalCoordinates A) (hB : RationalCoordinates B) :
    RationalCoordinates (A*B) := by
  intro i j
  change RatScalar (∑ a, A i a * B a j)
  exact RatScalar.finset_sum Finset.univ _ fun a _ => (hA i a).mul (hB a j)

theorem rationalCoordinates_one (n : ℕ) :
    RationalCoordinates (1 : Matrix (Fin n) (Fin n) ℝ) := by
  intro i j
  by_cases h : i=j
  · subst j
    exact ⟨1,by simp⟩
  · exact ⟨0,by simp [Matrix.one_apply,h]⟩

theorem rationalCoordinates_det {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : RationalCoordinates A) : RatScalar A.det := by
  classical
  choose Q hQ using hA
  have hmap : (Rat.castHom ℝ).mapMatrix Q = A := by
    ext i j
    exact hQ i j
  refine ⟨Matrix.det Q,?_⟩
  exact ((Rat.castHom ℝ).map_det Q).trans (congrArg Matrix.det hmap)

theorem rationalCoordinates_adjugate {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : RationalCoordinates A) : RationalCoordinates A.adjugate := by
  classical
  choose Q hQ using hA
  have hmap : (Rat.castHom ℝ).mapMatrix Q = A := by
    ext i j
    exact hQ i j
  intro i j
  refine ⟨Matrix.adjugate Q i j,?_⟩
  have h := (Rat.castHom ℝ).map_adjugate Q
  rw [hmap] at h
  exact congrFun (congrFun h i) j

theorem rationalCoordinates_inv {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : RationalCoordinates A) : RationalCoordinates A⁻¹ := by
  intro i j
  have hd := rationalCoordinates_det hA
  have ha := rationalCoordinates_adjugate hA i j
  have h := ha.div hd
  simpa [Matrix.inv_def,Ring.inverse_eq_inv,div_eq_mul_inv,mul_comm] using h

/-- A spanning family of rows has a nonsingular Gram matrix. -/
theorem gram_isUnit {n k : ℕ} {B : Matrix (Fin n) (Fin k) ℝ}
    (hB : Spans B) : IsUnit (B.transpose*B).det := by
  have hrank : (B.transpose*B).rank = k := by
    rw [Matrix.rank_transpose_mul_self,Matrix.rank_eq_finrank_span_row]
    change finrank ℝ (Submodule.span ℝ (Set.range B)) = k
    rw [hB]
    simp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_surjective_iff_isUnit.mp
  apply Matrix.mulVec_surjective_iff_rank_eq_card.mpr
  simpa using hrank

theorem mulVec_injective_of_spanning_rows {n k : ℕ}
    {B : Matrix (Fin n) (Fin k) ℝ} (hB : Spans B) :
    Function.Injective B.mulVec := by
  have hG := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (gram_isUnit hB))
  intro x y hxy
  apply hG
  simpa only [Matrix.mulVec_mulVec] using congrArg B.transpose.mulVec hxy

/-- The orthogonal projector onto the kernel of the transpose of the
Gale matrix. Its entries are rational functions of the actual entries. -/
def galeProjector {n k : ℕ} (B : Matrix (Fin n) (Fin k) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  1 - B * (B.transpose*B)⁻¹ * B.transpose

def galeChart {n k r : ℕ} (B : Matrix (Fin n) (Fin k) ℝ)
    (M : Matrix (Fin r) (Fin n) ℝ) : Matrix (Fin r) (Fin n) ℝ :=
  M * galeProjector B

theorem galeProjector_mul {n k : ℕ} {B : Matrix (Fin n) (Fin k) ℝ}
    (hB : Spans B) : galeProjector B * B = 0 := by
  have h :
      (B * (B.transpose*B)⁻¹ * B.transpose) * B = B := by
    calc
      (B * (B.transpose*B)⁻¹ * B.transpose) * B =
          B * ((B.transpose*B)⁻¹ * (B.transpose*B)) := by
        simp only [Matrix.mul_assoc]
      _ = B := by rw [Matrix.nonsing_inv_mul _ (gram_isUnit hB),Matrix.mul_one]
  rw [galeProjector,Matrix.sub_mul,Matrix.one_mul,h,sub_self]

theorem galeChart_mul {n k r : ℕ} {B : Matrix (Fin n) (Fin k) ℝ}
    (hB : Spans B) (M : Matrix (Fin r) (Fin n) ℝ) :
    galeChart B M * B = 0 := by
  rw [galeChart,Matrix.mul_assoc,galeProjector_mul hB,Matrix.mul_zero]

theorem galeChart_self {n k r : ℕ}
    (B : Matrix (Fin n) (Fin k) ℝ) (A : Matrix (Fin r) (Fin n) ℝ)
    (hAB : A*B=0) : galeChart B A = A := by
  unfold galeChart galeProjector
  rw [Matrix.mul_sub,Matrix.mul_one]
  have h : A * (B * (B.transpose*B)⁻¹ * B.transpose) = 0 := by
    rw [← Matrix.mul_assoc,← Matrix.mul_assoc,hAB,Matrix.zero_mul,Matrix.zero_mul]
  rw [h,sub_zero]

theorem galeChart_rational {n k r : ℕ}
    {B : Matrix (Fin n) (Fin k) ℝ} {M : Matrix (Fin r) (Fin n) ℝ}
    (hB : RationalCoordinates B) (hM : RationalCoordinates M) :
    RationalCoordinates (galeChart B M) := by
  exact rationalCoordinates_mul hM
    (rationalCoordinates_sub (rationalCoordinates_one n)
      (rationalCoordinates_mul
        (rationalCoordinates_mul hB
          (rationalCoordinates_inv
            (rationalCoordinates_mul (rationalCoordinates_transpose hB) hB)))
        (rationalCoordinates_transpose hB)))

theorem matrix_mul_continuousAt {X : Type*} [TopologicalSpace X]
    {m n k : ℕ} {A : X → Matrix (Fin m) (Fin n) ℝ}
    {B : X → Matrix (Fin n) (Fin k) ℝ} {x : X}
    (hA : ContinuousAt A x) (hB : ContinuousAt B x) :
    ContinuousAt (fun y => A y * B y) x := by
  have h : Continuous
      (fun z : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin n) (Fin k) ℝ =>
        z.1 * z.2) := continuous_fst.matrix_mul continuous_snd
  exact h.continuousAt.comp (hA.prodMk hB)

theorem galeChart_continuousAt {n k r : ℕ}
    {B : Matrix (Fin n) (Fin k) ℝ} (hB : Spans B)
    (A : Matrix (Fin r) (Fin n) ℝ) :
    ContinuousAt
      (fun z : Matrix (Fin n) (Fin k) ℝ × Matrix (Fin r) (Fin n) ℝ =>
        galeChart z.1 z.2) (B,A) := by
  have hBt : Continuous
      (fun z : Matrix (Fin n) (Fin k) ℝ × Matrix (Fin r) (Fin n) ℝ =>
        z.1.transpose) := continuous_fst.matrix_transpose
  have hG := hBt.matrix_mul continuous_fst
  have hinv : ContinuousAt
      (fun z : Matrix (Fin n) (Fin k) ℝ × Matrix (Fin r) (Fin n) ℝ =>
        (z.1.transpose*z.1)⁻¹) (B,A) := by
    have hi : ContinuousAt (Inv.inv : Matrix (Fin k) (Fin k) ℝ → _) (B.transpose*B) :=
      continuousAt_matrix_inv (B.transpose*B) (by
        simpa only [Ring.inverse_eq_inv'] using
          (continuousAt_inv₀ (isUnit_iff_ne_zero.mp (gram_isUnit hB))))
    exact hi.comp_of_eq (hG.continuousAt (x := (B,A))) rfl
  exact matrix_mul_continuousAt continuous_snd.continuousAt
    (continuousAt_const.sub
      (matrix_mul_continuousAt
        (matrix_mul_continuousAt continuous_fst.continuousAt hinv)
        hBt.continuousAt))

theorem transpose_spans_of_rowIndependent {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ A.row) :
    Spans A.transpose := by
  apply (spans_iff_matrix_rank A.transpose).mpr
  rw [Matrix.rank_transpose]
  simpa using hA.rank_matrix

def rowKernelVector {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (w : Fin n → ℝ) : Fin n → ℝ :=
  galeChart A.transpose (fun _ : Fin 1 => w) 0

theorem rowKernelVector_mem {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ A.row)
    (w : Fin n → ℝ) : A.mulVec (rowKernelVector A w) = 0 := by
  have h := galeChart_mul (transpose_spans_of_rowIndependent hA) (fun _ : Fin 1 => w)
  ext i
  have hi := congrFun (congrFun h 0) i
  simpa [rowKernelVector,Matrix.mul_apply,Matrix.mulVec,dotProduct,mul_comm] using hi

theorem rowKernelVector_self {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (w : Fin n → ℝ)
    (hw : A.mulVec w=0) : rowKernelVector A w=w := by
  have hWA : Matrix.of (fun _ : Fin 1 => w) * A.transpose = 0 := by
    ext i j
    have h := congrFun hw j
    simpa [Matrix.mul_apply,Matrix.mulVec,dotProduct,mul_comm] using h
  exact congrFun (galeChart_self A.transpose (fun _ : Fin 1 => w) hWA) 0

theorem rowKernelVector_rational {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} {w : Fin n → ℝ}
    (hA : RationalCoordinates A) (hw : ∀ i, RatScalar (w i)) :
    ∀ i, RatScalar (rowKernelVector A w i) :=
  fun i => galeChart_rational (rationalCoordinates_transpose hA)
    (fun (_ : Fin 1) j => hw j) 0 i

theorem rowKernelVector_continuousAt {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ A.row)
    (w : Fin n → ℝ) :
    ContinuousAt (fun z : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ) =>
      rowKernelVector z.1 z.2) (A,w) := by
  have hparam : Continuous
      (fun z : Matrix (Fin m) (Fin n) ℝ × (Fin n → ℝ) =>
        (z.1.transpose,(fun _ : Fin 1 => z.2))) :=
    continuous_fst.matrix_transpose.prodMk (continuous_pi fun _ => continuous_snd)
  have hchart := (galeChart_continuousAt (transpose_spans_of_rowIndependent hA)
    (fun _ : Fin 1 => w)).comp_of_eq (hparam.continuousAt (x := (A,w))) rfl
  exact (continuous_apply 0).continuousAt.comp hchart


end Papers.RationalKernelCharts

end
end
end BundlePart11

section BundlePart12
/- Source: Papers/RationalOrthogonalityPeeling.lean -/





@[expose] public section

/-!
# Rational approximation along an incidence deletion order

A finite symmetric system of orthogonality equations admits rational
approximation whenever every nonempty induced subsystem has one vector whose
remaining neighbours are linearly independent at the given configuration.
The proof constructs every missing vector using a rational Gram projector.
It does not assume that rational configurations already exist.
-/

noncomputable section
open Matrix Set Filter Topology
open scoped BigOperators

namespace Papers.RationalOrthogonalityPeeling

open Papers.RationalKernelCharts

variable {I : Type*} [Fintype I] [DecidableEq I] {d : ℕ}

def RationalFamily (p : I → Fin d → ℝ) : Prop :=
  ∀ i j, RatScalar (p i j)

def OrthogonalOn (R : I → I → Prop) (S : Finset I)
    (p : I → Fin d → ℝ) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, R i j → p i ⬝ᵥ p j = 0

theorem rationalFamily_dense : Dense {p : I → Fin d → ℝ | RationalFamily p} := by
  have h : DenseRange (fun p : I → Fin d → ℚ => fun i j => (p i j : ℝ)) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ => Rat.denseRange_cast
  apply h.mono
  rintro _ ⟨p,rfl⟩ i j
  exact ⟨p i j,rfl⟩

theorem mem_closure_inter_of_eventually {X : Type*} [TopologicalSpace X]
    {A B : Set X} {a : X} (ha : a∈closure A)
    (hB : ∀ᶠ x in 𝓝 a, x∈B) : a∈closure (A∩B) := by
  rw [mem_closure_iff_frequently] at ha ⊢
  exact ha.and_eventually hB

/-- The entire finite incidence system, with all original zero equations
retained, is approximated by rational solutions. -/
theorem rational_orthogonality_density
    (R : I → I → Prop) [DecidableRel R]
    (hsymm : ∀ i j, R i j → R j i)
    (hirr : ∀ i, ¬R i i)
    (p : I → Fin d → ℝ)
    (hp : ∀ i j, R i j → p i ⬝ᵥ p j=0)
    (hpeel : ∀ S : Finset I, S.Nonempty →
      ∃ i∈S, LinearIndependent ℝ
        (fun j : {j // j∈S ∧ R i j} => p j.val)) :
    p∈closure {q | RationalFamily q ∧ ∀ i j, R i j → q i ⬝ᵥ q j=0} := by
  classical
  have haux : ∀ S : Finset I,
      p∈closure {q | RationalFamily q ∧ OrthogonalOn R S q} := by
    intro S
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      by_cases hne : S.Nonempty
      · obtain ⟨i,hi,hlin⟩ := hpeel S hne
        let N : Finset I := S.filter (R i)
        let e : Fin N.card ≃ N := by
          simpa only [Fintype.card_coe] using (Fintype.equivFin N).symm
        let A : (I → Fin d → ℝ) → Matrix (Fin N.card) (Fin d) ℝ :=
          fun q a => q (e a).val
        have hA : LinearIndependent ℝ (A p).row := by
          let f : Fin N.card → {j // j∈S ∧ R i j} :=
            fun a => ⟨(e a).val,Finset.mem_filter.mp (e a).property⟩
          have hf : Function.Injective f := by
            intro a b hab
            apply e.injective
            apply Subtype.ext
            change (f a).val=(f b).val
            exact congrArg Subtype.val hab
          exact hlin.comp f hf
        have hAc : Continuous A := by
          apply continuous_pi
          intro a
          exact continuous_apply (e a).val
        let F : (I → Fin d → ℝ) → (I → Fin d → ℝ) :=
          fun q => Function.update q i (rowKernelVector (A q) (q i))
        have hFc : ContinuousAt F p := by
          apply continuousAt_pi.mpr
          intro j
          by_cases hji : j=i
          · subst j
            have hpar : ContinuousAt (fun q => (A q,q i)) p :=
              hAc.continuousAt.prodMk (continuous_apply i).continuousAt
            simpa [F,Function.comp_def] using
              (rowKernelVector_continuousAt hA (p i)).comp_of_eq hpar rfl
          · simpa [F,Function.update_of_ne hji] using
              (continuous_apply j : Continuous (fun q : I → Fin d → ℝ => q j)).continuousAt
        have hAp : (A p).mulVec (p i)=0 := by
          ext a
          change p (e a).val ⬝ᵥ p i=0
          exact hp _ _ (hsymm _ _ (Finset.mem_filter.mp (e a).property).2)
        have hFp : F p=p := by
          simp [F,rowKernelVector_self _ _ hAp]
        have hrec := ih (S.erase i) (Finset.erase_ssubset hi)
        have hindependent : ∀ᶠ q in 𝓝 p, LinearIndependent ℝ (A q).row :=
          hAc.continuousAt.eventually hA.eventually
        have hnear := mem_closure_inter_of_eventually
          (B := {q | LinearIndependent ℝ (A q).row}) hrec hindependent
        have himage : p∈closure (F ''
            ({q | RationalFamily q ∧ OrthogonalOn R (S.erase i) q} ∩
              {q | LinearIndependent ℝ (A q).row})) := by
          simpa only [hFp] using mem_closure_image hFc hnear
        apply closure_mono ?_ himage
        rintro _ ⟨q,⟨⟨hqrat,hqorth⟩,hqa⟩,rfl⟩
        refine ⟨?_,?_⟩
        · intro j k
          by_cases hji : j=i
          · subst j
            simpa [F] using rowKernelVector_rational
              (fun a b => hqrat (e a).val b) (hqrat i) k
          · simpa [F,Function.update_of_ne hji] using hqrat j k
        · have hz := rowKernelVector_mem hqa (q i)
          have hincident : ∀ j∈S, R i j → F q i ⬝ᵥ F q j=0 := by
            intro j hj hij
            have hji : j≠i := by intro h;subst j;exact hirr i hij
            let v : N := ⟨j,Finset.mem_filter.mpr ⟨hj,hij⟩⟩
            have he : (e (e.symm v)).val=j := congrArg Subtype.val (e.apply_symm_apply v)
            have hzero := congrFun hz (e.symm v)
            change q (e (e.symm v)).val ⬝ᵥ rowKernelVector (A q) (q i)=0 at hzero
            rw [he] at hzero
            simpa [F,Function.update_of_ne hji,dotProduct_comm] using hzero
          intro a ha b hb hab
          by_cases hai : a=i
          · subst a
            exact hincident b hb hab
          by_cases hbi : b=i
          · subst b
            rw [dotProduct_comm]
            exact hincident a ha (hsymm _ _ hab)
          have hh := hqorth a (Finset.mem_erase.mpr ⟨hai,ha⟩)
            b (Finset.mem_erase.mpr ⟨hbi,hb⟩) hab
          simpa [F,Function.update_of_ne hai,Function.update_of_ne hbi] using hh
      · have hS : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        subst S
        simpa [OrthogonalOn] using (rationalFamily_dense (I:=I) (d:=d) p)
  simpa [OrthogonalOn] using haux Finset.univ

end Papers.RationalOrthogonalityPeeling

end
end
end BundlePart12

section BundlePart13
/- Source: Papers/BipartiteOrthogonalityDensity.lean -/





@[expose] public section

/-! Rational reconstruction of finite point--normal incidence systems. -/

noncomputable section
namespace Papers.BipartiteOrthogonalityDensity
open Matrix Set
open scoped Classical
open Papers.RationalOrthogonalityPeeling Papers.BipartiteIncidencePeeling

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def incidenceRelation (R : A → B → Prop) : A ⊕ B → A ⊕ B → Prop
  | .inl a, .inr b => R a b
  | .inr b, .inl a => R a b
  | _, _ => False

def rightNeighborEquiv (R : A → B → Prop) (S : Finset (A ⊕ B)) (a : A) :
    {z // z∈S ∧ incidenceRelation R (.inl a) z} ≃
      (S.toRight.filter (R a)) where
  toFun z := match z with
    | ⟨.inr b,hS,hR⟩ => ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_toRight.mpr hS,hR⟩⟩
    | ⟨.inl _,_,hR⟩ => False.elim hR
  invFun b := ⟨.inr b.val,Finset.mem_toRight.mp (Finset.mem_filter.mp b.property).1,
    (Finset.mem_filter.mp b.property).2⟩
  left_inv := by rintro ⟨a|b,hS,hR⟩; exact False.elim hR; rfl
  right_inv _ := rfl

def leftNeighborEquiv (R : A → B → Prop) (S : Finset (A ⊕ B)) (b : B) :
    {z // z∈S ∧ incidenceRelation R (.inr b) z} ≃
      (S.toLeft.filter (fun a => R a b)) where
  toFun z := match z with
    | ⟨.inl a,hS,hR⟩ => ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_toLeft.mpr hS,hR⟩⟩
    | ⟨.inr _,_,hR⟩ => False.elim hR
  invFun a := ⟨.inl a.val,Finset.mem_toLeft.mp (Finset.mem_filter.mp a.property).1,
    (Finset.mem_filter.mp a.property).2⟩
  left_inv := by rintro ⟨a|b,hS,hR⟩; rfl; exact False.elim hR
  right_inv _ := rfl

theorem rational_bipartite_orthogonality_density {d : ℕ}
    (R : A → B → Prop) (p : A → Fin d → ℝ) (q : B → Fin d → ℝ)
    (hz : ∀ a b, R a b → p a ⬝ᵥ q b=0)
    (hp : ∀ S : Finset A, S.card≤3 → LinearIndependent ℝ (fun a : S => p a.val))
    (hq : ∀ T : Finset B, T.card≤3 → LinearIndependent ℝ (fun b : T => q b.val))
    (hdeg : ∀ S : Finset A, ∀ T : Finset B, S.Nonempty ∨ T.Nonempty →
      (∃ a∈S,pointDegree R T a≤3) ∨ (∃ b∈T,faceDegree R S b≤3)) :
    Sum.elim p q ∈ closure {z : A ⊕ B → Fin d → ℝ |
      RationalFamily z ∧ ∀ a b, R a b → z (.inl a) ⬝ᵥ z (.inr b)=0} := by
  have hsymm : ∀ i j, incidenceRelation R i j → incidenceRelation R j i := by
    intro i j
    cases i <;> cases j <;> simp only [incidenceRelation,imp_self]
  have hirr : ∀ i, ¬ incidenceRelation R i i := by
    intro i
    cases i <;> simp [incidenceRelation]
  have hzero : ∀ i j, incidenceRelation R i j →
      Sum.elim p q i ⬝ᵥ Sum.elim p q j=0 := by
    intro i j hij
    cases i with
    | inl a =>
      cases j with
      | inl _ => exact False.elim hij
      | inr b => exact hz a b hij
    | inr b =>
      cases j with
      | inl a => simpa only [Sum.elim_inl,Sum.elim_inr,dotProduct_comm] using hz a b hij
      | inr _ => exact False.elim hij
  have hpeel : ∀ S : Finset (A ⊕ B), S.Nonempty →
      ∃ i∈S,LinearIndependent ℝ
        (fun j : {j // j∈S ∧ incidenceRelation R i j} => Sum.elim p q j.val) := by
    intro S hS
    have hparts : S.toLeft.Nonempty ∨ S.toRight.Nonempty := by
      obtain ⟨a|b,h⟩ := hS
      · exact Or.inl ⟨a,Finset.mem_toLeft.mpr h⟩
      · exact Or.inr ⟨b,Finset.mem_toRight.mpr h⟩
    rcases hdeg S.toLeft S.toRight hparts with ⟨a,ha,hcard⟩ | ⟨b,hb,hcard⟩
    · refine ⟨.inl a,Finset.mem_toLeft.mp ha,?_⟩
      let e := rightNeighborEquiv R S a
      have hh := (hq (S.toRight.filter (R a)) hcard).comp e e.injective
      convert hh using 1
      ext j
      rcases j with ⟨b|b,hj,hR⟩
      · exact False.elim hR
      · rfl
    · refine ⟨.inr b,Finset.mem_toRight.mp hb,?_⟩
      let e := leftNeighborEquiv R S b
      have hh := (hp (S.toLeft.filter (fun a => R a b)) hcard).comp e e.injective
      convert hh using 1
      ext j
      rcases j with ⟨a|a,hj,hR⟩
      · rfl
      · exact False.elim hR
  have hh := rational_orthogonality_density (incidenceRelation R)
    hsymm hirr (Sum.elim p q) hzero hpeel
  apply closure_mono ?_ hh
  intro z hz
  exact ⟨hz.1,fun a b hab => hz.2 (.inl a) (.inr b) hab⟩

end Papers.BipartiteOrthogonalityDensity

end
end
end BundlePart13

section BundlePart14
/- Source: Papers/FieldSpan.lean -/



@[expose] public section

/-!
# Spans under an embedding of coordinate fields

These lemmas compare linear spans over the two different fields, rather than
restricting scalars on the larger vector space. In particular the dimension
statement is equality, not just monotonicity under an injective linear map.
-/

noncomputable section
namespace Papers.Coordinates

open Set

variable {K L : Type*} [Field K] [Field L]

def coordinateMap (σ : K →+* L) (n : ℕ) : (Fin n → K) →ₛₗ[σ] (Fin n → L) where
  toFun x j := σ (x j)
  map_add' x y := by ext j; exact σ.map_add _ _
  map_smul' c x := by ext j; exact σ.map_mul _ _

@[simp] theorem coordinateMap_apply (σ : K →+* L) (n : ℕ)
    (x : Fin n → K) (j : Fin n) : coordinateMap σ n x j = σ (x j) := rfl

theorem coordinateMap_mem_span (σ : K →+* L) {n : ℕ}
    {S : Set (Fin n → K)} {x : Fin n → K} (hx : x ∈ Submodule.span K S) :
    coordinateMap σ n x ∈ Submodule.span L (coordinateMap σ n '' S) := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (Set.mem_image_of_mem _ hx)
  | zero => simpa only [map_zero] using (Submodule.span L (coordinateMap σ n '' S)).zero_mem
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using (Submodule.span L (coordinateMap σ n '' S)).add_mem ihx ihy
  | smul c x hx ih =>
    simpa only [map_smulₛₗ] using
      (Submodule.span L (coordinateMap σ n '' S)).smul_mem (σ c) ih

theorem span_coordinateMap_span (σ : K →+* L) {n : ℕ} (S : Set (Fin n → K)) :
    Submodule.span L (coordinateMap σ n '' (Submodule.span K S : Set (Fin n → K))) =
      Submodule.span L (coordinateMap σ n '' S) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    exact coordinateMap_mem_span σ hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

/-- The rank of a coordinate span is unchanged by a field embedding. -/
theorem finrank_span_coordinateMap (σ : K →+* L) {n : ℕ} (S : Set (Fin n → K)) :
    Module.finrank L (Submodule.span L (coordinateMap σ n '' S)) =
      Module.finrank K (Submodule.span K S) := by
  let W := Submodule.span K S
  let b := Module.finBasis K W
  let q : Fin (Module.finrank K W) → Fin n → K := W.subtype ∘ b
  have hq : LinearIndependent K q :=
    b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hspan : Submodule.span K (Set.range q) = W := by
    dsimp only [q]
    rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have himage : Submodule.span L (coordinateMap σ n '' S) =
      Submodule.span L (Set.range (fun i => coordinateMap σ n (q i))) := by
    calc
      _ = Submodule.span L (coordinateMap σ n '' (W : Set (Fin n → K))) :=
        (span_coordinateMap_span σ S).symm
      _ = Submodule.span L
          (coordinateMap σ n '' (Submodule.span K (Set.range q) : Set (Fin n → K))) := by
        rw [hspan]
      _ = Submodule.span L (coordinateMap σ n '' Set.range q) :=
        span_coordinateMap_span σ (Set.range q)
      _ = _ := by rw [← Set.range_comp]; rfl
  rw [himage]
  change Module.finrank L (Submodule.span L (Set.range (fun i j => σ (q i j)))) =
    Module.finrank K W
  simpa only [Fintype.card_fin] using
    finrank_span_eq_card (linearIndependent_coordinate_map σ q hq)

/-- Linear membership also reflects back to the smaller field. -/
theorem coordinateMap_mem_span_iff (σ : K →+* L) {n : ℕ}
    (S : Set (Fin n → K)) (x : Fin n → K) :
    coordinateMap σ n x ∈ Submodule.span L (coordinateMap σ n '' S) ↔
      x ∈ Submodule.span K S := by
  constructor
  · intro hx
    have hm : Submodule.span L (coordinateMap σ n '' insert x S) =
        Submodule.span L (coordinateMap σ n '' S) := by
      rw [Set.image_insert_eq, Submodule.span_insert_eq_span hx]
    have hd : Module.finrank K (Submodule.span K S) =
        Module.finrank K (Submodule.span K (insert x S)) := by
      rw [← finrank_span_coordinateMap σ S,
        ← finrank_span_coordinateMap σ (insert x S), hm]
    have heq := Submodule.eq_of_le_of_finrank_eq
      (Submodule.span_mono (Set.subset_insert x S)) hd
    rw [heq]
    exact Submodule.subset_span (Set.mem_insert x S)
  · exact coordinateMap_mem_span σ

end Papers.Coordinates

end
end
end BundlePart14

section BundlePart15
/- Source: Papers/SubfieldAffineForms.lean -/




@[expose] public section

/-!
# Affine forms over a real subfield

Field-valued coordinates are embedded in ordinary Euclidean space.  An
affine form over the subfield is extended by its actual coordinate
coefficients.  The evaluation identity proves that this is an extension
of scalars, without restricting real geometric dimensions to the smaller
field.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open Papers.AffineCoordinates Papers.Coordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

/-- Coercion of a finite sum through the actual subfield embedding. -/
theorem subfield_coe_fintype_sum {ι : Type*} [Fintype ι]
    (K : Subfield ℝ) (f : ι → K) :
    ((∑ i, f i : K) : ℝ) = ∑ i, (f i : ℝ) := by
  simpa only [Subfield.subtype_apply] using (map_sum K.subtype f Finset.univ)

def embedFieldPoint (K : Subfield ℝ) : (Fin d → K) →ₛₗ[K.subtype] E d where
  toFun x := WithLp.toLp 2 (fun i => (x i : ℝ))
  map_add' x y := by ext i; exact K.subtype.map_add (x i) (y i)
  map_smul' c x := by ext i; exact K.subtype.map_mul c (x i)

@[simp] theorem embedFieldPoint_apply (K : Subfield ℝ) (x : Fin d → K) (i : Fin d) :
    embedFieldPoint K x i = (x i : ℝ) := rfl

def fieldPoint (K : Subfield ℝ) (x : E d) (hx : ∀ i, x i ∈ K) : Fin d → K :=
  fun i => ⟨x i, hx i⟩

@[simp] theorem embed_fieldPoint (K : Subfield ℝ) (x : E d) (hx : ∀ i, x i ∈ K) :
    embedFieldPoint K (fieldPoint K x hx) = x := by ext i; rfl

def embedFieldHomogeneous (K : Subfield ℝ) :
    ((Fin d → K) × K) →ₛₗ[K.subtype] (E d × ℝ) where
  toFun z := (embedFieldPoint K z.1, (z.2 : ℝ))
  map_add' z w := by
    apply Prod.ext
    · exact map_add (embedFieldPoint K) z.1 w.1
    · exact K.subtype.map_add z.2 w.2
  map_smul' c z := by
    apply Prod.ext
    · exact map_smulₛₗ (embedFieldPoint K) c z.1
    · exact K.subtype.map_mul c z.2

@[simp] theorem embedFieldHomogeneous_homogenize
    (K : Subfield ℝ) (x : Fin d → K) :
    embedFieldHomogeneous K (x, (1 : K)) = (embedFieldPoint K x, (1 : ℝ)) := by
  rfl

theorem semilinear_mem_span
    {K L V W : Type*} [Field K] [Field L] [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module L W] (σ : K →+* L) (f : V →ₛₗ[σ] W)
    (S : Set V) (x : V) (hx : x ∈ Submodule.span K S) :
    f x ∈ Submodule.span L (f '' S) := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span (Set.mem_image_of_mem _ hy)
  | zero => simpa only [map_zero] using (Submodule.span L (f '' S)).zero_mem
  | add y z hy hz ihy ihz =>
    simpa only [map_add] using (Submodule.span L (f '' S)).add_mem ihy ihz
  | smul c y hy ih =>
    simpa only [map_smulₛₗ] using (Submodule.span L (f '' S)).smul_mem (σ c) ih

def extendFieldLinear (K : Subfield ℝ) (l : (Fin d → K) →ₗ[K] K) : E d →ₗ[ℝ] ℝ :=
  (PiLp.basisFun 2 ℝ (Fin d)).constr ℝ
    (fun i => ((l (Pi.single i 1) : K) : ℝ))

@[simp] theorem extendFieldLinear_basis (K : Subfield ℝ)
    (l : (Fin d → K) →ₗ[K] K) (i : Fin d) :
    extendFieldLinear K l (PiLp.basisFun 2 ℝ (Fin d) i) = (l (Pi.single i 1) : ℝ) := by
  exact (PiLp.basisFun 2 ℝ (Fin d)).constr_basis ℝ _ i

theorem extendFieldLinear_embed (K : Subfield ℝ)
    (l : (Fin d → K) →ₗ[K] K) (x : Fin d → K) :
    extendFieldLinear K l (embedFieldPoint K x) = (l x : ℝ) := by
  have hx : (∑ i : Fin d, x i • Pi.single i (1 : K)) = x := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    simp
  have hl := congrArg (fun y : K => (y : ℝ)) (congrArg l hx)
  simp only [map_sum, map_smul, smul_eq_mul,
    subfield_coe_fintype_sum, Subfield.coe_mul] at hl
  rw [← (PiLp.basisFun 2 ℝ (Fin d)).sum_repr (embedFieldPoint K x), map_sum]
  simp only [map_smul, smul_eq_mul, PiLp.basisFun_repr, embedFieldPoint_apply,
    extendFieldLinear_basis]
  exact hl

def extendFieldAffine (K : Subfield ℝ) (f : (Fin d → K) →ᵃ[K] K) : E d →ᵃ[ℝ] ℝ where
  toFun x := extendFieldLinear K f.linear x + (f 0 : ℝ)
  linear := extendFieldLinear K f.linear
  map_vadd' p v := by
    change extendFieldLinear K f.linear (v + p) + (f 0 : ℝ) =
      extendFieldLinear K f.linear v + (extendFieldLinear K f.linear p + (f 0 : ℝ))
    rw [map_add, add_assoc]

theorem extendFieldAffine_embed (K : Subfield ℝ)
    (f : (Fin d → K) →ᵃ[K] K) (x : Fin d → K) :
    extendFieldAffine K f (embedFieldPoint K x) = (f x : ℝ) := by
  change extendFieldLinear K f.linear (embedFieldPoint K x) + (f 0 : ℝ) = _
  rw [extendFieldLinear_embed, ← Subfield.coe_add]
  apply congrArg (fun t : K => (t : ℝ))
  simpa only [vadd_eq_add, add_zero] using (f.map_vadd (0 : Fin d → K) x).symm

@[simp] theorem extendFieldAffine_zero (K : Subfield ℝ) (f : (Fin d → K) →ᵃ[K] K) :
    extendFieldAffine K f 0 = (f 0 : ℝ) := by
  change extendFieldLinear K f.linear 0 + (f 0 : ℝ) = _
  rw [map_zero, zero_add]

theorem extendFieldAffine_homogeneous (K : Subfield ℝ)
    (f : (Fin d → K) →ᵃ[K] K) (z : (Fin d → K) × K) :
    homogeneousEvaluation (embedFieldHomogeneous K z) (extendFieldAffine K f) =
      (homogeneousEvaluation z f : ℝ) := by
  change extendFieldLinear K f.linear (embedFieldPoint K z.1) +
    (z.2 : ℝ) * extendFieldAffine K f 0 = _
  rw [extendFieldLinear_embed, extendFieldAffine_zero,
    homogeneousEvaluation_apply, Subfield.coe_add, Subfield.coe_mul]

def AffineCoefficientsIn (K : Subfield ℝ) (f : E d →ᵃ[ℝ] ℝ) : Prop :=
  f 0 ∈ K ∧ ∀ i : Fin d, f.linear (PiLp.basisFun 2 ℝ (Fin d) i) ∈ K

theorem extendFieldAffine_coefficients (K : Subfield ℝ)
    (f : (Fin d → K) →ᵃ[K] K) : AffineCoefficientsIn K (extendFieldAffine K f) := by
  constructor
  · rw [extendFieldAffine_zero]
    exact (f 0).property
  · intro i
    change extendFieldLinear K f.linear (PiLp.basisFun 2 ℝ (Fin d) i) ∈ K
    rw [extendFieldLinear_basis]
    exact (f.linear (Pi.single i 1)).property

theorem AffineCoefficientsIn.eval {K : Subfield ℝ} {f : E d →ᵃ[ℝ] ℝ}
    (hf : AffineCoefficientsIn K f) (x : E d) (hx : ∀ i, x i ∈ K) : f x ∈ K := by
  rw [affine_form_apply f x]
  apply K.add_mem _ hf.1
  rw [← (PiLp.basisFun 2 ℝ (Fin d)).sum_repr x, map_sum]
  apply K.sum_mem
  intro i _
  rw [map_smul, smul_eq_mul, PiLp.basisFun_repr]
  exact K.mul_mem (hx i) (hf.2 i)

theorem AffineCoefficientsIn.homogeneous {K : Subfield ℝ} {f : E d →ᵃ[ℝ] ℝ}
    (hf : AffineCoefficientsIn K f) (z : E d × ℝ)
    (hz : (∀ i, z.1 i ∈ K) ∧ z.2 ∈ K) : homogeneousEvaluation z f ∈ K := by
  rw [homogeneousEvaluation_apply]
  apply K.add_mem _ (K.mul_mem hz.2 hf.1)
  have h := hf.eval z.1 hz.1
  rw [affine_form_apply f z.1] at h
  exact K.sub_mem h hf.1 |> fun h => by simpa only [add_sub_cancel_right] using h

end Papers.Polytopes

end
end
end BundlePart15

section BundlePart16
/- Source: Papers/ContinuousAffineFrames.lean -/





@[expose] public section

/-!
# Continuous affine interpolation with field-valued coefficients

Affine forms are represented by their actual coordinate coefficients.
Interpolation through an affine frame is an ordinary inverse-matrix
formula.  The formula is continuous at every nonsingular frame and uses
only field operations.  These facts supply the local approximation step
in the density part of simple vertex deletion.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module Filter Topology
open scoped Classical BigOperators
open Papers.AffineCoordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

def homogeneousCoordinates : (E d × ℝ) ≃ₗ[ℝ] (Option (Fin d) → ℝ) where
  toFun z i := i.elim z.2 z.1
  invFun r := (WithLp.toLp 2 (fun i => r (some i)), r none)
  map_add' z w := by ext i; cases i <;> rfl
  map_smul' c z := by ext i; cases i <;> rfl
  left_inv z := by apply Prod.ext <;> rfl
  right_inv r := by ext i; cases i <;> rfl

def affineCoefficientLinear (c : Option (Fin d) → ℝ) : E d →ₗ[ℝ] ℝ :=
  (PiLp.basisFun 2 ℝ (Fin d)).constr ℝ (fun j => c (some j))

def affineFromCoefficients (c : Option (Fin d) → ℝ) : E d →ᵃ[ℝ] ℝ where
  toFun x := affineCoefficientLinear c x + c none
  linear := affineCoefficientLinear c
  map_vadd' p v := by
    change affineCoefficientLinear c (v + p) + c none =
      affineCoefficientLinear c v + (affineCoefficientLinear c p + c none)
    rw [map_add, add_assoc]

def affineCoefficients (f : E d →ᵃ[ℝ] ℝ) : Option (Fin d) → ℝ :=
  fun i => i.elim (f 0) (fun j => f.linear (PiLp.basisFun 2 ℝ (Fin d) j))

@[simp] theorem affineCoefficientLinear_basis (c : Option (Fin d) → ℝ) (j : Fin d) :
    affineCoefficientLinear c (PiLp.basisFun 2 ℝ (Fin d) j) = c (some j) :=
  (PiLp.basisFun 2 ℝ (Fin d)).constr_basis ℝ _ j

theorem affineCoefficientLinear_apply (c : Option (Fin d) → ℝ) (x : E d) :
    affineCoefficientLinear c x = ∑ j, x j * c (some j) := by
  conv_lhs => rw [← (PiLp.basisFun 2 ℝ (Fin d)).sum_repr x]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, affineCoefficientLinear_basis, PiLp.basisFun_repr]

theorem affineFromCoefficients_apply (c : Option (Fin d) → ℝ) (x : E d) :
    affineFromCoefficients c x = c none + ∑ j, x j * c (some j) := by
  change affineCoefficientLinear c x + c none = _
  rw [affineCoefficientLinear_apply, add_comm]

@[simp] theorem affineCoefficients_fromCoefficients (c : Option (Fin d) → ℝ) :
    affineCoefficients (affineFromCoefficients c) = c := by
  ext i
  cases i with
  | none =>
    change affineCoefficientLinear c 0 + c none = c none
    rw [map_zero, zero_add]
  | some j => exact affineCoefficientLinear_basis c j

@[simp] theorem affineFromCoefficients_coefficients (f : E d →ᵃ[ℝ] ℝ) :
    affineFromCoefficients (affineCoefficients f) = f := by
  have hlin : affineCoefficientLinear (affineCoefficients f) = f.linear := by
    apply (PiLp.basisFun 2 ℝ (Fin d)).ext
    intro i
    exact affineCoefficientLinear_basis (affineCoefficients f) i
  ext x
  change affineCoefficientLinear (affineCoefficients f) x + f 0 = f x
  rw [hlin]
  exact (affine_form_apply f x).symm

theorem affineFromCoefficients_field (K : Subfield ℝ) (c : Option (Fin d) → ℝ)
    (hc : ∀ i, c i ∈ K) : AffineCoefficientsIn K (affineFromCoefficients c) := by
  constructor
  · change affineCoefficientLinear c 0 + c none ∈ K
    rw [map_zero, zero_add]
    exact hc none
  · intro i
    change affineCoefficientLinear c (PiLp.basisFun 2 ℝ (Fin d) i) ∈ K
    rw [affineCoefficientLinear_basis]
    exact hc (some i)

def affineFrameMatrix (p : Option (Fin d) → E d) :
    Matrix (Option (Fin d)) (Option (Fin d)) ℝ :=
  fun i j => j.elim 1 (p i)

theorem affineFrameMatrix_mulVec (p : Option (Fin d) → E d)
    (c : Option (Fin d) → ℝ) (i : Option (Fin d)) :
    (affineFrameMatrix p).mulVec c i = affineFromCoefficients c (p i) := by
  rw [Matrix.mulVec, dotProduct, Fintype.sum_option, affineFromCoefficients_apply]
  simp only [affineFrameMatrix, Option.elim_none, Option.elim_some, one_mul]

theorem affineFrameMatrix_det_ne_zero (p : Option (Fin d) → E d)
    (hp : LinearIndependent ℝ (fun i => (p i, (1 : ℝ)))) :
    (affineFrameMatrix p).det ≠ 0 := by
  have hrow : LinearIndependent ℝ (affineFrameMatrix p).row :=
    hp.map' homogeneousCoordinates.toLinearMap
      (LinearMap.ker_eq_bot.mpr homogeneousCoordinates.injective)
  exact (isUnit_iff_ne_zero.mp
    ((affineFrameMatrix p).isUnit_iff_isUnit_det.mp
      (Matrix.linearIndependent_row_iff_isUnit.mp hrow)))

theorem affineFrameMatrix_linearIndependent (p : Option (Fin d) → E d)
    (hp : (affineFrameMatrix p).det ≠ 0) :
    LinearIndependent ℝ (fun i => (p i, (1 : ℝ))) := by
  have hrow := Matrix.linearIndependent_rows_of_det_ne_zero hp
  exact hrow.map' homogeneousCoordinates.symm.toLinearMap
    (LinearMap.ker_eq_bot.mpr homogeneousCoordinates.symm.injective)

def affineFrameCoefficients (p : Option (Fin d) → E d) (r : Option (Fin d) → ℝ) :
    Option (Fin d) → ℝ := (affineFrameMatrix p)⁻¹.mulVec r

def affineFrameForm (p : Option (Fin d) → E d) (r : Option (Fin d) → ℝ) : E d →ᵃ[ℝ] ℝ :=
  affineFromCoefficients (affineFrameCoefficients p r)

theorem affineFrameForm_at_point (p : Option (Fin d) → E d)
    (hp : (affineFrameMatrix p).det ≠ 0) (r : Option (Fin d) → ℝ)
    (i : Option (Fin d)) : affineFrameForm p r (p i) = r i := by
  rw [affineFrameForm, ← affineFrameMatrix_mulVec]
  change ((affineFrameMatrix p).mulVec ((affineFrameMatrix p)⁻¹.mulVec r)) i = r i
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hp),
    Matrix.one_mulVec]

theorem affineFrameForm_unique (p : Option (Fin d) → E d)
    (hp : (affineFrameMatrix p).det ≠ 0) (r : Option (Fin d) → ℝ)
    (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ i, f (p i) = r i) : affineFrameForm p r = f := by
  have heq : (affineFrameMatrix p).mulVec (affineCoefficients f) = r := by
    ext i
    rw [affineFrameMatrix_mulVec, affineFromCoefficients_coefficients, hf i]
  have hcoeff : affineFrameCoefficients p r = affineCoefficients f := by
    change (affineFrameMatrix p)⁻¹.mulVec r = _
    rw [← heq, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hp), Matrix.one_mulVec]
  rw [affineFrameForm, hcoeff, affineFromCoefficients_coefficients]

theorem matrix_inverse_entries_in_subfield
    {n : Type*} [Fintype n] [DecidableEq n] (K : Subfield ℝ)
    (A : Matrix n n ℝ) (hA : ∀ i j, A i j ∈ K) : ∀ i j, A⁻¹ i j ∈ K := by
  let B : Matrix n n K := fun i j => ⟨A i j, hA i j⟩
  have hB : K.subtype.mapMatrix B = A := rfl
  have hdet : A.det ∈ K := by
    rw [← hB, ← RingHom.map_det]
    exact B.det.property
  have hadj (i j : n) : A.adjugate i j ∈ K := by
    rw [← hB, ← RingHom.map_adjugate]
    exact (B.adjugate i j).property
  intro i j
  rw [Matrix.inv_def, Ring.inverse_eq_inv]
  exact K.mul_mem (K.inv_mem hdet) (hadj i j)

theorem affineFrameForm_field
    (K : Subfield ℝ) (p : Option (Fin d) → E d) (r : Option (Fin d) → ℝ)
    (hp : ∀ i j, p i j ∈ K) (hr : ∀ i, r i ∈ K) :
    AffineCoefficientsIn K (affineFrameForm p r) := by
  apply affineFromCoefficients_field
  have hA : ∀ i j, affineFrameMatrix p i j ∈ K := by
    intro i j
    cases j with
    | none => exact K.one_mem
    | some j => exact hp i j
  have hinv := matrix_inverse_entries_in_subfield K (affineFrameMatrix p) hA
  intro i
  change ∑ j, (affineFrameMatrix p)⁻¹ i j * r j ∈ K
  exact K.sum_mem (fun j _ => K.mul_mem (hinv i j) (hr j))

theorem continuous_affineFrameMatrix :
    Continuous (affineFrameMatrix : (Option (Fin d) → E d) →
      Matrix (Option (Fin d)) (Option (Fin d)) ℝ) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  cases j with
  | none => exact continuous_const
  | some j =>
    exact (PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) j).comp
      (continuous_apply i)

theorem continuousAt_affineFrameCoefficients
    (p : Option (Fin d) → E d) (hp : (affineFrameMatrix p).det ≠ 0)
    (r : Option (Fin d) → ℝ) :
    ContinuousAt (fun q => affineFrameCoefficients q r) p := by
  have hinv : ContinuousAt (fun q => (affineFrameMatrix q)⁻¹) p :=
    (continuousAt_matrix_inv (affineFrameMatrix p)
      (by simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hp)).comp
      continuous_affineFrameMatrix.continuousAt
  apply continuousAt_pi.mpr
  intro i
  change ContinuousAt (fun q => ∑ j, (affineFrameMatrix q)⁻¹ i j * r j) p
  exact tendsto_finsetSum _ (fun j _ =>
    ((continuous_apply j).continuousAt.comp
      ((continuous_apply i).continuousAt.comp hinv)).mul continuousAt_const)

theorem affineFrameMatrix_eventually_nonsingular
    (p : Option (Fin d) → E d) (hp : (affineFrameMatrix p).det ≠ 0) :
    ∀ᶠ q in 𝓝 p, (affineFrameMatrix q).det ≠ 0 :=
  (continuous_affineFrameMatrix.matrix_det.continuousAt).eventually_ne hp

end Papers.Polytopes

end
end
end BundlePart16

section BundlePart17
/- Source: Papers/AffineSystemContinuity.lean -/



@[expose] public section

/-!
# Continuous solutions of square affine systems

The unknown is an ordinary homogeneous vector.  The matrix rows are
the actual coefficients of the supporting affine forms.  Invertibility,
evaluation, preservation of a real subfield, and continuity of the
normalized solution are proved separately.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module Filter Topology
open scoped Classical BigOperators
open Papers.AffineCoordinates
open LeanEval.Geometry.PlatonicClassification

variable {d : ℕ}

def affineCoefficientEquiv : (E d →ᵃ[ℝ] ℝ) ≃ₗ[ℝ] (Option (Fin d) → ℝ) where
  toFun := affineCoefficients
  invFun := affineFromCoefficients
  map_add' f g := by
    ext i
    cases i with
    | none => rfl
    | some j =>
      change (f + g).linear _ = f.linear _ + g.linear _
      rw [AffineMap.add_linear, LinearMap.add_apply]
  map_smul' c f := by
    ext i
    cases i with
    | none => rfl
    | some j =>
      change (c • f).linear _ = c * f.linear _
      rw [AffineMap.smul_linear, LinearMap.smul_apply, smul_eq_mul]
  left_inv := affineFromCoefficients_coefficients
  right_inv := affineCoefficients_fromCoefficients

theorem homogeneousEvaluation_coefficients
    (f : E d →ᵃ[ℝ] ℝ) (z : E d × ℝ) :
    homogeneousEvaluation z f =
      ∑ j, affineCoefficients f j * homogeneousCoordinates z j := by
  have hlin : f.linear z.1 = ∑ j, z.1 j * affineCoefficients f (some j) := by
    have h := congrArg (fun g : E d →ᵃ[ℝ] ℝ => g.linear z.1)
      (affineFromCoefficients_coefficients f)
    change affineCoefficientLinear (affineCoefficients f) z.1 = f.linear z.1 at h
    rw [affineCoefficientLinear_apply] at h
    exact h.symm
  rw [homogeneousEvaluation_apply, hlin, Fintype.sum_option]
  simp only [homogeneousCoordinates, affineCoefficients, Option.elim_none, Option.elim_some]
  rw [add_comm]
  congr 1
  · exact mul_comm _ _
  · apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _

def affineSystemMatrix (F : Option (Fin d) → E d →ᵃ[ℝ] ℝ) :
    Matrix (Option (Fin d)) (Option (Fin d)) ℝ := fun i j => affineCoefficients (F i) j

theorem affineSystemMatrix_mulVec
    (F : Option (Fin d) → E d →ᵃ[ℝ] ℝ) (z : E d × ℝ) (i : Option (Fin d)) :
    (affineSystemMatrix F).mulVec (homogeneousCoordinates z) i =
      homogeneousEvaluation z (F i) := (homogeneousEvaluation_coefficients (F i) z).symm

theorem affineSystemMatrix_basis_det_ne
    (b : Basis (Option (Fin d)) ℝ (E d →ᵃ[ℝ] ℝ)) :
    (affineSystemMatrix b).det ≠ 0 := by
  have hrow : LinearIndependent ℝ (affineSystemMatrix b).row :=
    b.linearIndependent.map' affineCoefficientEquiv.toLinearMap
      (LinearMap.ker_eq_bot.mpr affineCoefficientEquiv.injective)
  exact isUnit_iff_ne_zero.mp ((affineSystemMatrix b).isUnit_iff_isUnit_det.mp
    (Matrix.linearIndependent_row_iff_isUnit.mp hrow))

def homogeneousMatrixSolution
    (A : Matrix (Option (Fin d)) (Option (Fin d)) ℝ) (r : Option (Fin d) → ℝ) : E d × ℝ :=
  homogeneousCoordinates.symm (A⁻¹.mulVec r)

theorem homogeneousMatrixSolution_evaluation
    (F : Option (Fin d) → E d →ᵃ[ℝ] ℝ)
    (hF : (affineSystemMatrix F).det ≠ 0) (r : Option (Fin d) → ℝ)
    (i : Option (Fin d)) :
    homogeneousEvaluation (homogeneousMatrixSolution (affineSystemMatrix F) r) (F i) = r i := by
  rw [← affineSystemMatrix_mulVec]
  simp only [homogeneousMatrixSolution, LinearEquiv.apply_symm_apply]
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hF), Matrix.one_mulVec]

theorem homogeneousMatrixSolution_unique
    (F : Option (Fin d) → E d →ᵃ[ℝ] ℝ)
    (hF : (affineSystemMatrix F).det ≠ 0) (r : Option (Fin d) → ℝ)
    (z : E d × ℝ) (hz : ∀ i, homogeneousEvaluation z (F i) = r i) :
    homogeneousMatrixSolution (affineSystemMatrix F) r = z := by
  have heq : (affineSystemMatrix F).mulVec (homogeneousCoordinates z) = r := by
    ext i
    rw [affineSystemMatrix_mulVec, hz i]
  apply homogeneousCoordinates.injective
  simp only [homogeneousMatrixSolution, LinearEquiv.apply_symm_apply]
  rw [← heq, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hF), Matrix.one_mulVec]

theorem homogeneousMatrixSolution_coordinates
    (K : Subfield ℝ) (A : Matrix (Option (Fin d)) (Option (Fin d)) ℝ)
    (r : Option (Fin d) → ℝ) (hA : ∀ i j, A i j ∈ K) (hr : ∀ i, r i ∈ K) :
    (∀ j, (homogeneousMatrixSolution A r).1 j ∈ K) ∧
      (homogeneousMatrixSolution A r).2 ∈ K := by
  have hinv := matrix_inverse_entries_in_subfield K A hA
  have hcoeff (i : Option (Fin d)) : A⁻¹.mulVec r i ∈ K := by
    change (∑ j, A⁻¹ i j * r j) ∈ K
    exact K.sum_mem (fun j _ => K.mul_mem (hinv i j) (hr j))
  exact ⟨fun j => hcoeff (some j), hcoeff none⟩

def dehomogenizePoint (z : E d × ℝ) : E d := z.2⁻¹ • z.1

theorem dehomogenizePoint_lift (z : E d × ℝ) (hz : z.2 ≠ 0) :
    z = z.2 • (dehomogenizePoint z, (1 : ℝ)) := by
  apply Prod.ext
  · change z.1 = z.2 • (z.2⁻¹ • z.1)
    rw [smul_smul, mul_inv_cancel₀ hz, one_smul]
  · change z.2 = z.2 * 1
    exact (mul_one _).symm

theorem homogeneousEvaluation_dehomogenize (z : E d × ℝ) (hz : z.2 ≠ 0)
    (f : E d →ᵃ[ℝ] ℝ) : homogeneousEvaluation z f = z.2 * f (dehomogenizePoint z) := by
  conv_lhs => rw [dehomogenizePoint_lift z hz]
  rw [map_smul]
  change z.2 * homogeneousEvaluation (dehomogenizePoint z, (1 : ℝ)) f = _
  rw [homogeneousEvaluation_homogenize]

theorem dehomogenizePoint_coordinates (K : Subfield ℝ) (z : E d × ℝ)
    (hz : (∀ j, z.1 j ∈ K) ∧ z.2 ∈ K) : ∀ j, dehomogenizePoint z j ∈ K :=
  fun j => K.mul_mem (K.inv_mem hz.2) (hz.1 j)

theorem continuous_homogeneousCoordinates_symm :
    Continuous (homogeneousCoordinates.symm : (Option (Fin d) → ℝ) → E d × ℝ) :=
  homogeneousCoordinates.symm.toLinearMap.continuous_of_finiteDimensional

theorem continuousAt_homogeneousMatrixSolution
    (A : Matrix (Option (Fin d)) (Option (Fin d)) ℝ) (hA : A.det ≠ 0)
    (r : Option (Fin d) → ℝ) :
    ContinuousAt (fun p : (Matrix (Option (Fin d)) (Option (Fin d)) ℝ) ×
      (Option (Fin d) → ℝ) => homogeneousMatrixSolution p.1 p.2) (A, r) := by
  apply continuous_homogeneousCoordinates_symm.continuousAt.comp
  have hinv : ContinuousAt (fun p : (Matrix (Option (Fin d)) (Option (Fin d)) ℝ) ×
      (Option (Fin d) → ℝ) => p.1⁻¹) (A, r) :=
    (continuousAt_matrix_inv A
      (by simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hA)).comp
      continuous_fst.continuousAt
  apply continuousAt_pi.mpr
  intro i
  change ContinuousAt (fun p => ∑ j, p.1⁻¹ i j * p.2 j) (A, r)
  exact tendsto_finsetSum _ (fun j _ =>
    ((continuous_apply j).continuousAt.comp
      ((continuous_apply i).continuousAt.comp hinv)).mul
        ((continuous_apply j).continuousAt.comp continuous_snd.continuousAt))

theorem continuousAt_dehomogenizePoint (z : E d × ℝ) (hz : z.2 ≠ 0) :
    ContinuousAt dehomogenizePoint z :=
  (continuous_snd.continuousAt.inv₀ hz).smul continuous_fst.continuousAt

end Papers.Polytopes

end
end
end BundlePart17

section BundlePart18
/- Source: Papers/PolytopeIncidenceConfiguration.lean -/








@[expose] public section

/-! The actual three-polytope incidence configuration is rationally approximable. -/

noncomputable section
namespace Papers.PolytopeIncidenceConfiguration
open Set Module Matrix Filter Topology
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeThreeIncidences
open Papers.ActualThreeVertexIndependence Papers.AffineCoordinates
open Papers.BipartiteIncidencePeeling Papers.BipartiteOrthogonalityDensity
open Papers.RationalOrthogonalityPeeling

variable {d : ℕ}

def coefficientVector (f : E d →ᵃ[ℝ] ℝ) : Fin (d+1) → ℝ :=
  Fin.cases (f 0) (fun i => f.linear (PiLp.basisFun 2 ℝ (Fin d) i))

def coefficientVectorLinear : (E d →ᵃ[ℝ] ℝ) →ₗ[ℝ] (Fin (d+1) → ℝ) where
  toFun := coefficientVector
  map_add' f g := by ext i; cases i using Fin.cases <;> simp [coefficientVector]
  map_smul' c f := by ext i; cases i using Fin.cases <;> simp [coefficientVector]

theorem coefficientVector_injective : Function.Injective (coefficientVector (d:=d)) := by
  intro f g h
  apply affineCoefficientEquiv.injective
  ext i
  cases i with
  | none => exact congrFun h 0
  | some j => exact congrFun h j.succ

def formOfVector (a : Fin (d+1) → ℝ) : E d →ᵃ[ℝ] ℝ :=
  affineFromCoefficients (fun i => i.elim (a 0) (fun j => a j.succ))

theorem formOfVector_coefficientVector (f : E d →ᵃ[ℝ] ℝ) :
    formOfVector (coefficientVector f)=f := by
  change affineFromCoefficients (affineCoefficients f)=f
  exact affineFromCoefficients_coefficients f

theorem vector_dot_homogeneous (a : Fin (d+1) → ℝ) (x : E d) :
    a ⬝ᵥ homogeneousVertex x = formOfVector a x := by
  simp [dotProduct,homogeneousVertex,Fin.sum_univ_succ,formOfVector,
    affineFromCoefficients_apply,mul_comm]

theorem coefficient_dot_homogeneous (f : E d →ᵃ[ℝ] ℝ) (x : E d) :
    coefficientVector f ⬝ᵥ homogeneousVertex x=f x := by
  rw [vector_dot_homogeneous,formOfVector_coefficientVector]

theorem continuous_homogeneousVertex : Continuous (homogeneousVertex (d:=d)) := by
  apply continuous_pi
  intro i
  cases i using Fin.cases
  · exact continuous_const
  · rename_i j
    change Continuous (fun x : E d => x j)
    fun_prop

def facetOfTwoFace (P : ConvexPolytope d) (hdim : P.dim=3) (F : Face P 2) :
    FacetType P := ⟨⟨F.val.carrier,F.val.isFace⟩,F.val.isFace,by rw [F.property,hdim]⟩

theorem facetOfTwoFace_injective (P : ConvexPolytope d) (hdim : P.dim=3) :
    Function.Injective (facetOfTwoFace P hdim) := by
  intro F G h
  apply Subtype.ext
  apply PolytopeFace.ext
  exact congrArg (fun H : FacetType P => H.val.val) h

def vertexFaceIncident (P : ConvexPolytope d) (v : P.vertices) (F : Face P 2) : Prop :=
  v.val∈F.val.carrier

theorem exists_low_degree_labelled (P : ConvexPolytope d) (hdim : P.dim=3)
    (S : Finset P.vertices) (T : Finset (Face P 2)) (hne : S.Nonempty ∨ T.Nonempty) :
    (∃ v∈S,pointDegree (vertexFaceIncident P) T v≤3) ∨
      (∃ F∈T,faceDegree (vertexFaceIncident P) S F≤3) := by
  let X : Finset (E d) := S.image Subtype.val
  have hXP : X⊆P.vertices := by
    intro x hx
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hx
    exact v.property
  have hne' : X.Nonempty ∨ T.Nonempty := hne.imp (fun h => h.image _) id
  rcases Papers.PolytopeIncidencePeeling.exists_low_degree P hdim X hXP T hne' with
    ⟨x,hx,hc⟩ | ⟨F,hF,hc⟩
  · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
    exact Or.inl ⟨v,hv,hc⟩
  · refine Or.inr ⟨F,hF,?_⟩
    have heq : X.filter (fun x => x∈F.val.carrier) =
        (S.filter (fun v => v.val∈F.val.carrier)).image Subtype.val := by
      ext x
      simp only [X,Finset.mem_filter,Finset.mem_image]
      constructor
      · rintro ⟨⟨v,hv,rfl⟩,hF⟩
        exact ⟨v,⟨hv,hF⟩,rfl⟩
      · rintro ⟨v,⟨hv,hF⟩,rfl⟩
        exact ⟨⟨v,hv,rfl⟩,hF⟩
    rw [heq,Finset.card_image_of_injective _ Subtype.val_injective] at hc
    exact hc

def incidenceVectors (P : ConvexPolytope d) (hdim : P.dim=3) :
    P.vertices ⊕ Face P 2 → Fin (d+1) → ℝ :=
  Sum.elim (fun v => homogeneousVertex v.val)
    (fun F => coefficientVector (chosenFacetForm P (facetOfTwoFace P hdim F)))

theorem actual_incidence_rational_density (P : ConvexPolytope d) (hdim : P.dim=3) :
    incidenceVectors P hdim ∈ closure {z : P.vertices ⊕ Face P 2 → Fin (d+1) → ℝ |
      RationalFamily z ∧ ∀ v F, vertexFaceIncident P v F →
        z (.inl v) ⬝ᵥ z (.inr F)=0} := by
  apply rational_bipartite_orthogonality_density
  · intro v F hmem
    rw [dotProduct_comm,coefficient_dot_homogeneous]
    exact (chosenFacetForm_supports P (facetOfTwoFace P hdim F)).eq_zero hmem
  · intro S hS
    have hcard := actual_vertices_card_gt_dim P
    rw [hdim] at hcard
    exact small_homogeneous_vertex_family_independent P (by omega)
      (fun v : S => v.val) Subtype.val_injective (by simpa only [Fintype.card_coe] using hS)
  · intro T hT
    have hli := small_chosenFacetForms_independent P
      (fun F : T => facetOfTwoFace P hdim F.val)
      ((facetOfTwoFace_injective P hdim).comp Subtype.val_injective)
      (by simpa only [Fintype.card_coe] using hT)
    exact hli.map' coefficientVectorLinear (LinearMap.ker_eq_bot.mpr coefficientVector_injective)
  · exact exists_low_degree_labelled P hdim

end Papers.PolytopeIncidenceConfiguration

end
end
end BundlePart18
