module
public import Papers.NineVertexDensityAssembly
public import MatroidChecked.IncidentFacetSimplicity
public import Papers.EightRelationRowsAssembly
public import Papers.SimpleDeletionPaper
public import FaceOrderNumericalInvariants
public import Consolidated.SixFacetEncoding
public import ActualSevenNoSixBudget
public import ActualSevenMixedBudget
public import ActualSevenTwoSixBudget
public import ActualResidualFacetPartition
public import RootedFamilyClosure
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import RootedTargetCoverage
public import GraphTargetCoverage
public import Mathlib.Tactic.FinCases

/-! Complete actual six-facet assembly. Original source scopes are retained. -/

section BundlePart0
/- Original module: Papers.SimpleCoreRestoration. -/

@[expose] public section

/-!
# Restoring simple vertices from a small retained core

The two kernel solves here give a direct version of the polarity argument in
Appendix A.3. First approximate the retained vertices and solve for all facet
normals. At a retained vertex the nearby nonzero point bounds the incident
normal rank. At an omitted simple vertex the number of incident facets gives
the same bound. A second kernel solve restores the entire vertex family.

The geometric normal-rank and simple-incidence facts are explicit inputs to
the generic statement below. The actual-polytope interface discharges them
separately; these generic lemmas are not principal theorem statements.
-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Matrix Filter Topology
open scoped Classical BigOperators
open PlaneRationalization

/-- Preserving the ranks of specified point subsets allows their annihilating
normals to be chosen rationally and continuously near the original normals. -/
theorem rational_restricted_normal_lift {m n d : ℕ}
    (p : Fin n → Fin (d + 1) → ℝ)
    (A : Fin m → Fin (d + 1) → ℝ) (T : Fin m → Finset (Fin n))
    (hzero : ∀ j i, i ∈ T j → A j ⬝ᵥ p i = 0)
    (hcore : p ∈ closure {q : Fin n → Fin (d + 1) → ℝ |
      RationalCoordinates q ∧ (∀ i, q i 0 = 1) ∧
      ∀ j, subsetRank q (T j) = subsetRank p (T j)}) :
    (p, A) ∈ closure
      {z : (Fin n → Fin (d + 1) → ℝ) × (Fin m → Fin (d + 1) → ℝ) |
        RationalCoordinates z.1 ∧ RationalCoordinates z.2 ∧
        (∀ i, z.1 i 0 = 1) ∧ ∀ j i, i ∈ T j → z.2 j ⬝ᵥ z.1 i = 0} := by
  let M : Fin m → Matrix (Fin n) (Fin (d + 1)) ℝ := fun j => maskRows p (T j)
  let C : (j : Fin m) → RowKernelChart (M j) :=
    fun j => Classical.choice (exists_rowKernelChart (M j))
  have hker (j : Fin m) : (M j).mulVec (A j) = 0 := by
    apply (maskRows_mulVec_zero_iff p (T j) (A j)).mpr
    intro i hi
    exact hzero j i hi
  let G := fun z : (Fin n → Fin (d + 1) → ℝ) × (Fin m → Fin (d + 1) → ℝ) =>
    fun j => (C j).eval (maskRows z.1 (T j)) (z.2 j)
  have hGbase : G (p, A) = A := by
    funext j
    exact (C j).self (A j) (hker j)
  have hGcont : ContinuousAt G (p, A) := by
    apply continuousAt_pi.mpr
    intro j
    have hc : Continuous
        (fun z : (Fin n → Fin (d + 1) → ℝ) × (Fin m → Fin (d + 1) → ℝ) =>
          (maskRows z.1 (T j), z.2 j)) :=
      ((maskRows_continuous (T j)).comp continuous_fst).prodMk
        ((continuous_apply j).comp continuous_snd)
    exact ((C j).continuousAt (A j)).comp_of_eq (hc.continuousAt (x := (p,A))) rfl
  let F := fun z : (Fin n → Fin (d + 1) → ℝ) × (Fin m → Fin (d + 1) → ℝ) =>
    (z.1, G z)
  have hFcont : ContinuousAt F (p,A) := continuous_fst.continuousAt.prodMk hGcont
  have hFbase : F (p,A) = (p,A) := by simp only [F, hGbase]
  have hopen : ∀ᶠ z in 𝓝 (p,A), ∀ j,
      LinearIndependent ℝ (fun a => maskRows z.1 (T j) ((C j).rows a)) := by
    apply eventually_all.mpr
    intro j
    have hc : Continuous
        (fun z : (Fin n → Fin (d + 1) → ℝ) × (Fin m → Fin (d + 1) → ℝ) =>
          maskRows z.1 (T j)) := (maskRows_continuous (T j)).comp continuous_fst
    exact (hc.continuousAt (x := (p,A))).tendsto.eventually (C j).eventually_independent
  have hprod : (p,A) ∈ closure
      ({q : Fin n → Fin (d + 1) → ℝ |
        RationalCoordinates q ∧ (∀ i, q i 0 = 1) ∧
        ∀ j, subsetRank q (T j) = subsetRank p (T j)} ×ˢ
       {B : Fin m → Fin (d + 1) → ℝ | RationalCoordinates B}) := by
    rw [closure_prod_eq]
    exact ⟨hcore, rationalCoordinates_dense m (d + 1) A⟩
  have hcl := mem_closure_inter_of_eventually hprod hopen
  have himage := mem_closure_image hFcont hcl
  rw [hFbase] at himage
  apply closure_mono (s := F '' _) ?_ himage
  rintro _ ⟨⟨q,B⟩, ⟨⟨hq,hB⟩, hgood⟩, rfl⟩
  refine ⟨hq.1, ?_, hq.2.1, ?_⟩
  · intro j
    exact (C j).rational (maskRows_rational hq.1 (T j)) (hB j)
  · intro j i hi
    have hrank : (maskRows q (T j)).rank = (M j).rank := by
      dsimp only [M]
      rw [maskRows_rank, maskRows_rank]
      exact hq.2.2 j
    have hm := (C j).mem (maskRows q (T j)) hrank (hgood j) (B j)
    exact (maskRows_mulVec_zero_iff q (T j) (G (q,B) j)).mp hm i hi

/-- The normal ranks are retained when every omitted label has at most `d`
incident facets. The retained labels use their nearby homogeneous coordinates
as nonzero annihilators. Lower rank bounds are open at the original matrix. -/
theorem incident_normal_rank_density_from_core {m n d : ℕ}
    (p : Fin n → Fin (d + 1) → ℝ)
    (A : Fin m → Fin (d + 1) → ℝ) (S : Fin m → Finset (Fin n))
    (I : Finset (Fin n))
    (hzero : ∀ j i, i ∈ S j → A j ⬝ᵥ p i = 0)
    (hrank : ∀ i, subsetRank A (incidentSelectedNormals S i) = d)
    (hsimple : ∀ i, i ∉ I → (incidentSelectedNormals S i).card ≤ d)
    (hcore : p ∈ closure {q : Fin n → Fin (d + 1) → ℝ |
      RationalCoordinates q ∧ (∀ i, q i 0 = 1) ∧
      ∀ j, subsetRank q (S j ∩ I) = subsetRank p (S j ∩ I)}) :
    A ∈ closure (incidentRankRealizations A S) := by
  have hcl := rational_restricted_normal_lift p A (fun j => S j ∩ I)
    (fun j i hi => hzero j i (Finset.mem_inter.mp hi).1) hcore
  have hopen : ∀ᶠ z in 𝓝 (p,A), ∀ i,
      subsetRank A (incidentSelectedNormals S i) ≤
        subsetRank z.2 (incidentSelectedNormals S i) := by
    apply eventually_all.mpr
    intro i
    exact (continuous_snd.continuousAt (x := (p,A))).tendsto.eventually
      (eventually_subsetRank_ge A (incidentSelectedNormals S i))
  have hc := mem_closure_inter_of_eventually hcl hopen
  have himage := mem_closure_image continuous_snd.continuousAt hc
  apply closure_mono (s := Prod.snd '' _) ?_ himage
  rintro _ ⟨⟨q,B⟩, ⟨⟨hq,hB,hfirst,hinc⟩,hlow⟩, rfl⟩
  refine ⟨hB, ?_⟩
  intro i
  apply Nat.le_antisymm _ (hlow i)
  rw [hrank]
  by_cases hi : i ∈ I
  · have hne : q i ≠ 0 := by
      intro hz
      have hh := congrFun hz 0
      have hf : q i 0 = 1 := hfirst i
      rw [hf] at hh
      exact one_ne_zero hh
    have hu := subsetRank_add_one_le_of_annihilator B (incidentSelectedNormals S i)
      (q i) hne (by
        intro j hj
        rw [dotProduct_comm]
        exact hinc j i (Finset.mem_inter.mpr
          ⟨(mem_incidentSelectedNormals S i j).mp hj,hi⟩))
    change subsetRank B (incidentSelectedNormals S i) + 1 ≤ d + 1 at hu
    change subsetRank B (incidentSelectedNormals S i) ≤ d
    omega
  · exact (subsetRank_le_card_labels B (incidentSelectedNormals S i)).trans (hsimple i hi)

/-- Coordinate form of the simple-core restoration principle. Every facet
is represented; its incidence rows are solved in the first stage, and the
full labelled face order is recovered by the existing local reconstruction. -/
theorem rational_polytope_density_from_simple_core {m n d : ℕ}
    (p : Fin n → Fin (d + 1) → ℝ) (hp : Spans p) (hfirst : ∀ i, p i 0 = 1)
    (A : Fin m → Fin (d + 1) → ℝ) (S : Fin m → Finset (Fin n))
    (I : Finset (Fin n)) (hnormal : ∀ j, A j ≠ 0)
    (hzero : ∀ j i, i ∈ S j → A j ⬝ᵥ p i = 0)
    (hcover : ∀ T ∈ facetMasks p, ∃ j, S j = T)
    (hrank : ∀ i, subsetRank A (incidentSelectedNormals S i) = d)
    (hsimple : ∀ i, i ∉ I → (incidentSelectedNormals S i).card ≤ d)
    (hcore : p ∈ closure {q : Fin n → Fin (d + 1) → ℝ |
      RationalCoordinates q ∧ (∀ i, q i 0 = 1) ∧
      ∀ T ∈ facetMasks p, subsetRank q (T ∩ I) = subsetRank p (T ∩ I)})
    (hfacets : ∀ j, S j ∈ facetMasks p) :
    p ∈ closure {q : Fin n → Fin (d + 1) → ℝ |
      RationalCoordinates q ∧ (∀ i, q i 0 = 1) ∧ Spans q ∧
      LabelledPolytopeEquivalent p q} := by
  apply rational_polytope_density_from_selected_normal_rank_density p hp hfirst A S
    hnormal hzero (fun T hT => Or.inr (hcover T hT))
  apply incident_normal_rank_density_from_core p A S I hzero hrank hsimple
  apply closure_mono ?_ hcore
  intro q hq
  exact ⟨hq.1,hq.2.1,fun j => hq.2.2 (S j) (hfacets j)⟩

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart0

section BundlePart1
/- Original module: Papers.IncidentNormalRank. -/

@[expose] public section

/-!
# The rank of the actual normals incident to a vertex

The proof uses the already established halfspace representation of a convex
polytope. A direction killed by all active linear forms would give a short
segment through the vertex inside the polytope. Extremality rules it out.
Consequently the homogeneous common kernel is precisely the vertex line.
-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Matrix Filter Topology
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeIncidenceConfiguration
open Papers.ActualThreeVertexIndependence

theorem incident_facet_linear_common_kernel {d : ℕ}
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P) (w : E d)
    (hw : ∀ F : FacetType P, v.val ∈ F.val.val →
      (chosenFacetForm P F).linear w = 0) : w = 0 := by
  have hstep (F : FacetType P) (t : ℝ) :
      chosenFacetForm P F (v.val + t • w) =
        t * (chosenFacetForm P F).linear w + chosenFacetForm P F v.val := by
    simpa only [vadd_eq_add, map_smul, smul_eq_mul, add_comm] using
      (chosenFacetForm P F).map_vadd v.val (t • w)
  have hopen : ∀ᶠ t : ℝ in 𝓝 0, ∀ F : FacetType P,
      0 ≤ chosenFacetForm P F (v.val + t • w) := by
    apply eventually_all.mpr
    intro F
    by_cases hv : v.val ∈ F.val.val
    · apply Filter.Eventually.of_forall
      intro t
      rw [hstep, hw F hv, (chosenFacetForm_supports P F).eq_zero hv]
      simp
    · have hpos : 0 < chosenFacetForm P F v.val := by
        have hn := (chosenFacetForm_supports P F).1 v.val (vertex_mem_body P v.property)
        have hne : chosenFacetForm P F v.val ≠ 0 := by
          intro hz
          exact hv (((chosenFacetForm_supports P F).mem_iff v.val).mpr
            ⟨vertex_mem_body P v.property, hz⟩)
        exact lt_of_le_of_ne hn (Ne.symm hne)
      have hc : Continuous (fun t : ℝ =>
          t * (chosenFacetForm P F).linear w + chosenFacetForm P F v.val) :=
        (continuous_id.mul continuous_const).add continuous_const
      have hh := (hc.continuousAt (x := 0)).tendsto.eventually
        (isOpen_Ioi.mem_nhds (show 0 < 0 * (chosenFacetForm P F).linear w +
          chosenFacetForm P F v.val by simpa only [zero_mul, zero_add] using hpos))
      filter_upwards [hh] with t ht
      rw [hstep]
      exact ht.le
  have hbody : ∀ᶠ t : ℝ in 𝓝 0, v.val + t • w ∈ P.toSet :=
    hopen.mono fun t ht => (mem_body_iff_chosenFacetForms_nonneg P hP _).mpr ht
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hbody
  have ht : 0 < ε / 2 := by linarith
  have hp : v.val + (ε / 2) • w ∈ P.toSet := hball (by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht]
    linarith)
  have hm' : v.val + (-(ε / 2)) • w ∈ P.toSet := hball (by
    rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos ht]
    linarith)
  have hm : v.val - (ε / 2) • w ∈ P.toSet := by
    simpa only [neg_smul, sub_eq_add_neg] using hm'
  have hv : v.val ∈ P.toSet.extremePoints ℝ := by
    change v.val ∈ (convexHull ℝ (↑P.vertices : Set (E d))).extremePoints ℝ
    rw [← P.vertices_eq_extremePoints]
    exact v.property
  have heq : v.val + (ε / 2) • w = v.val := hv.2 hp hm
    (mem_openSegment_add_sub (𝕜 := ℝ) v.val ((ε / 2) • w))
  have hz : (ε / 2) • w = 0 := by
    have hh := congrArg (fun x : E d => x - v.val) heq
    simpa only [add_sub_cancel_left, sub_self] using hh
  exact (smul_eq_zero.mp hz).resolve_left (ne_of_gt ht)

def allFacetNormals {d m : ℕ} (P : ConvexPolytope d)
    (f : Fin m ≃ FacetType P) : Fin m → Fin (d + 1) → ℝ :=
  fun j => coefficientVector (chosenFacetForm P (f j))

def allFacetLabels {d m n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (f : Fin m ≃ FacetType P) : Fin m → Finset (Fin n) :=
  fun j => actualFaceLabels P e ⟨(f j).val.val, (f j).property.1⟩

@[simp] theorem mem_allFacetLabels {d m n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (f : Fin m ≃ FacetType P) (i : Fin n) (j : Fin m) :
    i ∈ allFacetLabels P e f j ↔ (e i).val ∈ (f j).val.val :=
  mem_actualFaceLabels P e _ i

theorem allFacetNormals_incident_rank {d m n : ℕ}
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (e : Fin n ≃ P.vertices) (f : Fin m ≃ FacetType P) (i : Fin n) :
    subsetRank (allFacetNormals P f)
      (incidentSelectedNormals (allFacetLabels P e f) i) = d := by
  let A := allFacetNormals P f
  let S := incidentSelectedNormals (allFacetLabels P e f) i
  let M := maskRows A S
  let u := homogeneousVertex (e i).val
  have hfirst : u 0 = 1 := rfl
  have hune : u ≠ 0 := by
    intro hz
    have hh := congrFun hz 0
    rw [hfirst] at hh
    exact one_ne_zero hh
  have hu : u ∈ M.mulVecLin.ker := by
    apply (maskRows_mulVec_zero_iff A S u).mpr
    intro j hj
    rw [dotProduct_comm]
    change coefficientVector (chosenFacetForm P (f j)) ⬝ᵥ homogeneousVertex (e i).val = 0
    rw [coefficient_dot_homogeneous]
    exact (chosenFacetForm_supports P (f j)).eq_zero
      ((mem_allFacetLabels P e f i j).mp ((mem_incidentSelectedNormals _ i j).mp hj))
  have hker : M.mulVecLin.ker = Submodule.span ℝ {u} := by
    apply le_antisymm
    · intro y hy
      let z := y - y 0 • u
      have hz : z ∈ M.mulVecLin.ker := M.mulVecLin.ker.sub_mem hy
        (M.mulVecLin.ker.smul_mem (y 0) hu)
      have hzfirst : z 0 = 0 := by simp only [z, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, hfirst, mul_one, sub_self]
      let w : E d := (euclideanCoordinateEquiv d).symm (fun j => z j.succ)
      have hzw : z = homogeneousVertex w - homogeneousVertex (0 : E d) := by
        funext j
        cases j using Fin.cases with
        | zero => simpa only [Pi.sub_apply, homogeneousVertex, Fin.cases_zero, sub_self] using hzfirst
        | succ j =>
          change z j.succ = w j - 0
          simp only [sub_zero]
          rfl
      have hw : w = 0 := incident_facet_linear_common_kernel P hP (e i) w (by
        intro F hiF
        let j := f.symm F
        have hj : j ∈ S := by
          apply (mem_incidentSelectedNormals _ i j).mpr
          apply (mem_allFacetLabels P e f i j).mpr
          simpa only [j, Equiv.apply_symm_apply] using hiF
        have hh := (maskRows_mulVec_zero_iff A S z).mp hz j hj
        rw [dotProduct_comm] at hh
        change coefficientVector (chosenFacetForm P (f j)) ⬝ᵥ z = 0 at hh
        rw [hzw, dotProduct_sub, coefficient_dot_homogeneous,
          coefficient_dot_homogeneous, affine_form_apply] at hh
        have hf : f j = F := f.apply_symm_apply F
        rw [hf] at hh
        linarith)
      have hz0 : z = 0 := by rw [hzw, hw, sub_self]
      have hyu : y = y 0 • u := sub_eq_zero.mp hz0
      rw [hyu]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
    · exact Submodule.span_le.mpr (fun x hx => by
        have hx' : x = u := Set.mem_singleton_iff.mp hx
        subst x
        exact hu)
  have hdim := M.mulVecLin.finrank_range_add_finrank_ker
  have hkernel : finrank ℝ M.mulVecLin.ker = 1 := by
    rw [hker]
    exact finrank_span_singleton hune
  have hMrank : M.rank + 1 = d + 1 := by
    simpa only [Matrix.rank, hkernel, Module.finrank_pi, Module.finrank_self,
      Fintype.card_fin, mul_one] using hdim
  have heq : M.rank = subsetRank A S := maskRows_rank A S
  change subsetRank A S = d
  omega

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart1

section BundlePart2
/- Original module: ActualSimpleCoreRestoration. -/

@[expose] public section

/-!
# Actual restoration from the nonsimple vertex core

Every facet and every incident normal below is taken from the given convex
polytope. A simple vertex has exactly four incident facets, by its genuine
three-dimensional vertex figure. Thus the two kernel solves of
`SimpleCoreRestoration` apply after approximating the retained core.

The final theorem allows arbitrarily many simple vertices. Only the number
of nonsimple vertices is bounded by nine. Its explicitly named algebraic
premise is the exact nine-column theorem used by the existing vertex bound.
-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Matrix Filter Topology Finset
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeIncidenceConfiguration

/-- The intrinsic three-faces are exactly the facets of a full four-polytope. -/
def facetThreeFaceEquiv (P : ConvexPolytope 4) (hP : P.IsFullDim) :
    FacetType P ≃ Face P 3 where
  toFun F := ⟨⟨F.val.val, F.val.property⟩, by
    have h := F.property.2
    change faceDim F.val.val + 1 = P.dim at h
    change faceDim F.val.val = 3
    rw [hP] at h
    omega⟩
  invFun F := ⟨⟨F.val.carrier, F.val.isFace⟩,
    F.val.isFace, by rw [F.property, hP]⟩
  left_inv F := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv F := by apply Subtype.ext; apply PolytopeFace.ext; rfl

/-- The list of active facet-normal rows has exactly the actual facet
incidence count at the original vertex. -/
def allFacetIncidentEquiv {m n : ℕ} (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (e : Fin n ≃ P.vertices) (f : Fin m ≃ FacetType P) (i : Fin n) :
    (incidentSelectedNormals (allFacetLabels P e f) i) ≃
      IncidentFace P (e i).val 3 where
  toFun j := ⟨facetThreeFaceEquiv P hP (f j.val),
    (mem_allFacetLabels P e f i j.val).mp
      ((mem_incidentSelectedNormals _ i j.val).mp j.property)⟩
  invFun F := ⟨f.symm ((facetThreeFaceEquiv P hP).symm F.val), by
    apply (mem_incidentSelectedNormals _ i _).mpr
    apply (mem_allFacetLabels P e f i _).mpr
    rw [f.apply_symm_apply]
    exact F.property⟩
  left_inv j := by
    apply Subtype.ext
    apply f.injective
    change f (f.symm ((facetThreeFaceEquiv P hP).symm
      (facetThreeFaceEquiv P hP (f j.val)))) = f j.val
    rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  right_inv F := by
    apply Subtype.ext
    change facetThreeFaceEquiv P hP
      (f (f.symm ((facetThreeFaceEquiv P hP).symm F.val))) = F.val
    rw [f.apply_symm_apply, Equiv.apply_symm_apply]

theorem allFacetIncident_card {m n : ℕ} (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (e : Fin n ≃ P.vertices) (f : Fin m ≃ FacetType P) (i : Fin n) :
    (incidentSelectedNormals (allFacetLabels P e f) i).card =
      Nat.card (IncidentFace P (e i).val 3) := by
  have h := Nat.card_congr (allFacetIncidentEquiv P hP e f i)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using h

theorem simple_vertex_incident_facets (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v) :
    Nat.card (IncidentFace P v.val 3) = 4 := by
  apply (MatroidChecked.IncidentFacetSimplicity.four_incident_facets_iff_simple P hP v).mpr
  rw [← MatroidChecked.IncidentFacetSimplicity.degree_eq_actual_neighbors,
    NineBipyramidIncidence.vertexGraph_eq_polytopeGraph]
  exact hs.trans hP

theorem allFacetNormals_nonzero {d m : ℕ} (P : ConvexPolytope d)
    (f : Fin m ≃ FacetType P) (j : Fin m) : allFacetNormals P f j ≠ 0 := by
  intro hz
  have hform := Papers.Polytopes.IsFacet.support_ne_zero (f j).property
    (chosenFacetForm_supports P (f j))
  apply hform
  apply coefficientVector_injective
  exact hz.trans (map_zero coefficientVectorLinear).symm

/-- Actual convex-geometric simple-core restoration. All incidence and
rank hypotheses of the coordinate theorem are derived here. -/
theorem actual_simple_core_restoration {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (I : Finset (Fin n)) (hI : I.Nonempty)
    (hsimple : ∀ i, i ∉ I → IsSimpleVertex P (e i))
    (hcore : RationallyApproximable (retainedVertexCore P e I hI)) :
    RationallyApproximable P := by
  let m := Fintype.card (FacetType P)
  let f : Fin m ≃ FacetType P := (Fintype.equivFin _).symm
  let A := allFacetNormals P f
  let S := allFacetLabels P e f
  have hzero : ∀ j i, i ∈ S j → A j ⬝ᵥ vertexCoordinates P e i = 0 := by
    intro j i hi
    exact (actualFacetLabels_strictSupport P e (f j)).1 i hi
  have hfacets : ∀ j, S j ∈ facetMasks (vertexCoordinates P e) := by
    intro j
    apply (mem_facetMasks _ _).mpr
    exact actual_three_face_facetMask P hP e (facetThreeFaceEquiv P hP (f j))
  have hcover : ∀ T ∈ facetMasks (vertexCoordinates P e), ∃ j, S j = T := by
    intro T hT
    obtain ⟨F, hF⟩ := facetMask_actual_three_face P e T ((mem_facetMasks _ T).mp hT)
    let j := f.symm ((facetThreeFaceEquiv P hP).symm F)
    refine ⟨j, ?_⟩
    change actualFaceLabels P e ⟨(f j).val.val, (f j).property.1⟩ = T
    simp only [j, f.apply_symm_apply]
    exact hF
  have hsimpleRows : ∀ i, i ∉ I → (incidentSelectedNormals S i).card ≤ 4 := by
    intro i hi
    rw [allFacetIncident_card P hP e f i,
      simple_vertex_incident_facets P hP (e i) (hsimple i hi)]
  have hh := rational_polytope_density_from_simple_core (vertexCoordinates P e)
    (vertexCoordinates_spans P e hP) (fun _ => rfl) A S I
    (allFacetNormals_nonzero P f) hzero hcover
    (allFacetNormals_incident_rank P hP e f) hsimpleRows
    (actual_retained_core_rank_density P e I hI hcore) hfacets
  have ho := ordinary_density_of_homogeneous_density (ordinaryVertexCoordinates P e)
    (by simpa only [ordinaryVertexCoordinates_homogeneous] using hh)
  apply rationallyApproximable_of_coordinate_density P e
  apply closure_mono ?_ ho
  intro q hq
  exact ⟨hq.1, hq.2.2⟩

/-- The vertices counted in the extension are nonsimple in the original
polytope. No property of an intermediate deletion is used. -/
def nonsimpleVertices (P : ConvexPolytope 4) : Finset (VertexType P) :=
  Finset.univ.filter fun v => ¬ IsSimpleVertex P v

theorem nonsimple_label_card {n : ℕ} (P : ConvexPolytope 4)
    (e : Fin n ≃ P.vertices) :
    (Finset.univ.filter fun i : Fin n => ¬ IsSimpleVertex P (e i)).card =
      (nonsimpleVertices P).card := by
  let N := Finset.univ.filter fun i : Fin n => ¬ IsSimpleVertex P (e i)
  have heq : N.image e = nonsimpleVertices P := by
    ext v
    simp only [Finset.mem_image, N, nonsimpleVertices, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hv
      exact ⟨e.symm v, by simpa only [e.apply_symm_apply] using hv, e.apply_symm_apply v⟩
  rw [← heq, Finset.card_image_of_injective _ e.injective]

theorem actual_at_most_nine_nonsimple_vertices_approximable
    (hmatrices : NineColumnExceptionalMatrixDensity)
    (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hcount : (nonsimpleVertices P).card ≤ 9) : RationallyApproximable P := by
  let n := Fintype.card P.vertices
  let e : Fin n ≃ P.vertices := (Fintype.equivFin _).symm
  let N : Finset (Fin n) := Finset.univ.filter fun i => ¬ IsSimpleVertex P (e i)
  have hNcard : N.card ≤ 9 := by
    rw [nonsimple_label_card P e]
    exact hcount
  have hselect : ∃ I : Finset (Fin n), I.Nonempty ∧ I.card ≤ 9 ∧
      ∀ i, i ∉ I → IsSimpleVertex P (e i) := by
    by_cases hN : N.Nonempty
    · refine ⟨N, hN, hNcard, ?_⟩
      intro i hi
      by_contra hsimple
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsimple⟩)
    · obtain ⟨v, hv⟩ := P.vertices_nonempty
      let a := e.symm ⟨v, hv⟩
      refine ⟨{a}, Finset.singleton_nonempty a, by simp, ?_⟩
      intro i _
      by_contra hsimple
      exact hN ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsimple⟩⟩
  obtain ⟨I, hI, hIcard, hsimple⟩ := hselect
  apply actual_simple_core_restoration P hP e I hI hsimple
  apply ambient_at_most_nine_vertices_of_exceptional_matrix_density hmatrices
  · have hdim := Submodule.finrank_mono
      (vectorSpan_mono ℝ (retainedVertexCore_body_subset P e I hI))
    change (retainedVertexCore P e I hI).dim ≤ P.dim at hdim
    exact hdim.trans_eq hP
  · rw [retainedVertexCore_card]
    exact hIcard

/-- The nonsimple-vertex count is determined by the full face order. -/
theorem nonsimpleVertices_card_of_faceOrder {P Q : ConvexPolytope 4}
    (φ : FaceType P ≃o FaceType Q) :
    (nonsimpleVertices P).card = (nonsimpleVertices Q).card := by
  let b := vertexEquivOfFaceOrder φ
  have hs (v : VertexType P) : IsSimpleVertex Q (b v) ↔ IsSimpleVertex P v := by
    constructor
    · intro h
      have hi := isSimple_imageVertex φ.symm (b v) h
      change IsSimpleVertex P (b.symm (b v)) at hi
      simpa only [b.symm_apply_apply] using hi
    · exact isSimple_imageVertex φ v
  have heq : (nonsimpleVertices P).image b = nonsimpleVertices Q := by
    ext w
    simp only [Finset.mem_image, nonsimpleVertices, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact fun h => hv ((hs v).mp h)
    · intro hw
      refine ⟨b.symm w, ?_, b.apply_symm_apply w⟩
      intro hv
      have hi := (hs (b.symm w)).mpr hv
      exact hw (by simpa only [b.apply_symm_apply] using hi)
  rw [← heq, Finset.card_image_of_injective _ b.injective]

/-- The same extension holds densely in every realization of the full
face lattice, with no bound on the number of simple vertices. -/
theorem actual_at_most_nine_nonsimple_vertices_rationallyDense
    (hmatrices : NineColumnExceptionalMatrixDensity)
    (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hcount : (nonsimpleVertices P).card ≤ 9) : RationallyDense P := by
  intro Q hPQ
  obtain ⟨φ⟩ := hPQ
  have hQ : Q.IsFullDim := (faceOrderIso_polytope_dim φ).trans hP
  apply actual_at_most_nine_nonsimple_vertices_approximable hmatrices Q hQ
  rw [← nonsimpleVertices_card_of_faceOrder φ]
  exact hcount

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart2

section BundlePart3
/- Original module: PrincipalGeometryAssembly. -/

@[expose] public section

/-!
# Assembly of the principal small-polytope results

This module isolates the exact remaining finite inputs. No declaration here
introduces an axiom. The theorems ending in `of_inputs` are conditional
assembly theorems, and become the paper's unconditional results only after
their explicitly named matrix and residual-classification inputs are proved.

Theorem 2 concludes rational existence, as in the paper. It does not assert
density for the exceptional Cayley type. Corollary 4 uses the full arbitrary-
field deletion theorem. Proposition 8(i) and (ii) retain density in every
realization of the face lattice.
-/

noncomputable section
namespace Papers.Polytopes

open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

theorem RationallyApproximable.realizable {d : ℕ} {P : ConvexPolytope d}
    (h : RationallyApproximable P) : RationallyRealizable P := by
  obtain ⟨Q, φ, hQ, _⟩ := h 1 zero_lt_one
  exact ⟨Q, ⟨φ⟩, hQ⟩

end Papers.Polytopes

namespace Papers.RationalityTen.PrincipalGeometryAssembly

open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeFacetSurplus
open ChirotopeDensity

/-- Exact residual target after the already proved reductions. There is no
facet-size bound, no assumed numerical budget, and no finite-universe
coverage assumption in the polytope hypotheses. The finite classification
must establish this predicate for every such actual convex polytope. -/
def TenVertexResidualRealizability : Prop :=
  ∀ (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin 10 ≃ P.vertices),
    P.vertices.card = 10 →
    (∀ v : VertexType P, ¬ IsSimpleVertex P v) →
    10 ≤ (nonsimplicialFacets P).card →
    9 ≤ Fintype.card (SparseSharedRowIndex P e) →
    RationallyRealizable P

/-- Proposition 8(i), with the exact finite matrix theorem shown as an
input until its independent classification is closed. -/
theorem proposition_eight_i_of_inputs
    (hmatrices : NineColumnExceptionalMatrixDensity)
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (hn : P.vertices.card ≤ 9) :
    RationallyDense P :=
  actual_at_most_nine_vertices_rationallyDense_of_exceptional_matrix_density
    hmatrices P hP hn

/-- The nonsimplicial-facet half of Proposition 8(ii). The face-order
equivalence transports the facet count, so the conclusion is global density. -/
theorem proposition_eight_ii_facets_of_inputs
    (hmatrices : NineColumnExceptionalMatrixDensity)
    (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hcount : (nonsimplicialFacets P).card ≤ 9) : RationallyDense P := by
  intro Q hPQ
  obtain ⟨φ⟩ := hPQ
  have hQ : Q.IsFullDim := (faceOrderIso_polytope_dim φ).trans hP
  apply actual_at_most_nine_nonsimplicial_facets_of_exceptional_matrix_density
    hmatrices Q hQ
  rw [← nonsimplicialFacets_card_of_faceOrder φ]
  exact hcount

/-- Both alternatives in Proposition 8(ii), with no bound on the total
number of vertices or facets. -/
theorem proposition_eight_ii_of_inputs
    (hmatrices : NineColumnExceptionalMatrixDensity)
    (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hcount : (nonsimplicialFacets P).card ≤ 9 ∨ (nonsimpleVertices P).card ≤ 9) :
    RationallyDense P := by
  rcases hcount with hfacets | hvertices
  · exact proposition_eight_ii_facets_of_inputs hmatrices P hP hfacets
  · exact actual_at_most_nine_nonsimple_vertices_rationallyDense hmatrices P hP hvertices

/-- The exact pointwise conclusion supplied by Appendix A.4 at a realization
whose selected-row count is at most eight. This theorem is deliberately
not mislabeled as the stronger whole-type density statement. -/
theorem eight_selected_rows_approximable_of_inputs {n : ℕ}
    (hmatrices : NineColumnExceptionalMatrixDensity)
    (hclassification : EightRowMatrixDensityOrFourSupport)
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hrows : Fintype.card (ActualSharedRowIndex P e) ≤ 8) :
    RationallyApproximable P :=
  actual_polytope_eight_shared_relations_of_classification
    hmatrices hclassification P hP e hrows

/-- The full statement of Theorem 2 follows from its exact residual
classification and the two separately checked matrix-classification inputs. -/
theorem theorem_two_of_inputs
    (hmatrices : NineColumnExceptionalMatrixDensity)
    (hclassification : EightRowMatrixDensityOrFourSupport)
    (hresidual : TenVertexResidualRealizability) : RationalityThroughTenClaim := by
  intro P hP hn
  by_cases hnine : P.vertices.card ≤ 9
  · exact (proposition_eight_i_of_inputs hmatrices P hP hnine).realizable
  have hten : P.vertices.card = 10 := by omega
  by_cases hsimple : ∃ v : VertexType P, IsSimpleVertex P v
  · obtain ⟨v, hv⟩ := hsimple
    have hlarge : 4 + 1 < P.vertices.card := by omega
    obtain ⟨hne, hfull, _, _, _⟩ :=
      paper_simple_vertex_deletion 4 P v hP hlarge hv
    have hdeleted : (deleteVertex P v.val hne).vertices.card ≤ 9 := by
      rw [deleteVertex_vertices, Finset.card_erase_of_mem v.property]
      omega
    have hrat := (proposition_eight_i_of_inputs hmatrices
      (deleteVertex P v.val hne) hfull hdeleted).realizable
    apply (rationallyRealizable_iff_realizableOver P).mpr
    exact RealizableOver.restore_simple_vertex P hP v hv hlarge hne rationalSubfield
      ((rationallyRealizable_iff_realizableOver _).mp hrat)
  have hnonsimple : ∀ v : VertexType P, ¬ IsSimpleVertex P v := by
    simpa only [not_exists] using hsimple
  by_cases hfacets : (nonsimplicialFacets P).card ≤ 9
  · exact (proposition_eight_ii_facets_of_inputs hmatrices P hP hfacets).realizable
  let e : Fin 10 ≃ P.vertices := (Finset.equivFinOfCardEq hten).symm
  by_cases hrows : Fintype.card (SparseSharedRowIndex P e) ≤ 8
  · exact (actual_polytope_eight_sparse_relations_of_classification
      hmatrices hclassification P hP e hrows).realizable
  exact hresidual P hP e hten hnonsimple (by omega) (by omega)

/-- Corollary 4 depends only on the faithful Theorem 2 and the already
proved simple-vertex deletion theorem, including its arbitrary-field part. -/
theorem corollary_four_of_theorem_two
    (hten : RationalityThroughTenClaim)
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (hn : P.vertices.card = 11)
    (hsimple : ∃ v : VertexType P, IsSimpleVertex P v) : RationallyRealizable P := by
  obtain ⟨v, hv⟩ := hsimple
  have hlarge : 4 + 1 < P.vertices.card := by omega
  obtain ⟨hne, hfull, _, _, _⟩ :=
    paper_simple_vertex_deletion 4 P v hP hlarge hv
  have hdeleted : (deleteVertex P v.val hne).vertices.card ≤ 10 := by
    rw [deleteVertex_vertices, Finset.card_erase_of_mem v.property]
    omega
  apply (rationallyRealizable_iff_realizableOver P).mpr
  exact RealizableOver.restore_simple_vertex P hP v hv hlarge hne rationalSubfield
    ((rationallyRealizable_iff_realizableOver _).mp (hten _ hfull hdeleted))

theorem corollary_four_of_inputs
    (hmatrices : NineColumnExceptionalMatrixDensity)
    (hclassification : EightRowMatrixDensityOrFourSupport)
    (hresidual : TenVertexResidualRealizability)
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (hn : P.vertices.card = 11)
    (hsimple : ∃ v : VertexType P, IsSimpleVertex P v) : RationallyRealizable P :=
  corollary_four_of_theorem_two (theorem_two_of_inputs hmatrices hclassification hresidual)
    P hP hn hsimple

end Papers.RationalityTen.PrincipalGeometryAssembly

end
end
end BundlePart3

section BundlePart4
/- Original module: ActualResidualPartition. -/

@[expose] public section

/-!
# Exhaustive partition of the actual residual problem

This is the mathematical bridge to the finite case files. The partition
starts with an arbitrary actual ten-vertex four-polytope after the proved
density reductions. Every branch retains full local facet templates and
their actual counts. The exactly-two-six-facets branch is included explicitly.

The final interface asks for complete classified encodings of these exact
cases. It does not assume rational realizability of any case. A classified
encoding consists of actual facet coverage and ordinary finite classification
and leaf-disposition proofs; `RootedFamilyClosure` proves its consequence.
-/

noncomputable section
namespace Papers.RationalityTen.ActualResidualPartition

open Finset Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeSmallFacetBounds Papers.PolytopeFacetSurplus Papers.PolytopeRelationBudget
open ChirotopeDensity ActualFacetCatalogueTransport
open ActualFacetTemplateAssignment SixFacetProfileRefinement
open SevenFacetBudgetIdentities
open MatroidChecked.SevenBudgetCoverage
open MatroidChecked.FacetBoundaryEncoding LiteralMaskGeometry
open Nonrational.TerminalData Nonrational.TerminalVerification

local instance faceFintype (P : ConvexPolytope 4) (k : Nat) :
    Fintype (Face P k) := Fintype.ofFinite _

/-- A finite row agrees with every actual count used by its growth quota.
The fields are the same as in the recovered case interface; their proofs now
come from the canonical no-six and mixed numerical reductions. -/
structure ActualCaseCounts (P : ConvexPolytope 4) (B : CaseRow) : Prop where
  facets : B.m = Nat.card (Face P 3)
  excess : (B.E : Int) = facetExcess P
  quadrilaterals : B.q = (quadrilateralFaces P).card
  squarePyramids : B.SP = (smallSquareFacets P).card
  bipyramids : B.BP = (smallBipyramidFacets P).card
  tetrahedra : B.T = (tetrahedralFacets P).card
  pentagons : B.pentagons = (pentagonalFaces P).card

structure SmallCase (P : ConvexPolytope 4) : Prop where
  vertices : P.vertices.card = 10
  small : ∀ F : Face P 3, facetVertexCount P F ≤ 5
  budget : SmallFacetBudget.mk (Nat.card (Face P 3)) (nonsimplicialFacets P).card
    (quadrilateralFaces P).card ∈ smallFacetBudgets

structure SixCase (P : ConvexPolytope 4) where
  vertices : P.vertices.card = 10
  small : ∀ F : Face P 3, facetVertexCount P F ≤ 6
  assignment : Assignment P
  refines : (countsOf P assignment.kind).Refines (actualAllSixFacetBudget P)
  budget : (countsOf P assignment.kind).toRow (actualAllSixFacetBudget P) ∈
    SixBudgetEnumeration.catalogue

structure SevenPureCase (P : ConvexPolytope 4) where
  vertices : P.vertices.card = 10
  facet : Face P 3
  seven : facetVertexCount P facet = 7
  otherSmall : ∀ G : Face P 3, G ≠ facet → facetVertexCount P G ≤ 5
  template : Fin 34
  labels : (facePolytope P facet.val.isFace).vertices ≃ Fin 7
  boundary : polygonBoundary (facePolytope P facet.val.isFace) labels =
    FiniteCycleCandidates.N7.templates template
  row : CaseRow
  row_mem : row ∈ noSixCases
  row_template : row.template = template.val
  row_six : row.sixTemplate = none
  counts : ActualCaseCounts P row

structure SevenMixedCase (P : ConvexPolytope 4) where
  vertices : P.vertices.card = 10
  facet : Face P 3
  sixFacet : Face P 3
  seven : facetVertexCount P facet = 7
  six : facetVertexCount P sixFacet = 6
  otherSmall : ∀ G : Face P 3, G ≠ facet → G ≠ sixFacet → facetVertexCount P G ≤ 5
  six_count : (sixVertexFacets P).card = 1
  template : Fin 34
  labels : (facePolytope P facet.val.isFace).vertices ≃ Fin 7
  boundary : polygonBoundary (facePolytope P facet.val.isFace) labels =
    FiniteCycleCandidates.N7.templates template
  sixTemplate : Fin 7
  sixLabels : (facePolytope P sixFacet.val.isFace).vertices ≃ Fin 6
  sixBoundary : polygonBoundary (facePolytope P sixFacet.val.isFace) sixLabels =
    FiniteCycleCandidates.N6.templates sixTemplate
  row : CaseRow
  row_mem : row ∈ oneSixCases
  row_template : row.template = template.val
  row_six : row.sixTemplate = some sixTemplate.val
  counts : ActualCaseCounts P row

structure SevenTwoSixCase (P : ConvexPolytope 4) where
  vertices : P.vertices.card = 10
  facet : Face P 3
  seven : facetVertexCount P facet = 7
  otherSmall : ∀ G : Face P 3, G ≠ facet → facetVertexCount P G ≤ 6
  six_count : (sixVertexFacets P).card = 2
  template : Fin 34
  labels : (facePolytope P facet.val.isFace).vertices ≃ Fin 7
  boundary : polygonBoundary (facePolytope P facet.val.isFace) labels =
    FiniteCycleCandidates.N7.templates template
  squarePyramids : Fin 8
  square_count : (smallSquareFacets P).card = squarePyramids.val
  bipyramid_count : (smallBipyramidFacets P).card = 7 - squarePyramids.val
  tetrahedron_count : (tetrahedralFacets P).card = 0
  facets : Nat.card (Face P 3) = 10
  excess : facetExcess P = 14

inductive Partition (P : ConvexPolytope 4) : Prop where
  | small : SmallCase P → Partition P
  | six : SixCase P → Partition P
  | sevenPure : SevenPureCase P → Partition P
  | sevenMixed : SevenMixedCase P → Partition P
  | sevenTwoSix : SevenTwoSixCase P → Partition P

theorem actual_seven_template (P : ConvexPolytope 4) (F : Face P 3)
    (hF : facetVertexCount P F = 7) :
    ∃ (loc : (facePolytope P F.val.isFace).vertices ≃ Fin 7) (i : Fin 34),
      polygonBoundary (facePolytope P F.val.isFace) loc = FiniteCycleCandidates.N7.templates i := by
  apply ActualSmallFacetClassification.seven_vertex_classification
  · change faceDim (facePolytope P F.val.isFace).toSet = 3
    rw [facePolytope_toSet]
    exact F.property
  · have hc : (facePolytope P F.val.isFace).vertices.card = facetVertexCount P F := by
      simpa only [facetVertexCount, Nat.card_eq_fintype_card, Fintype.card_coe] using
        (Nat.card_congr (faceVerticesEquiv P F.val.isFace)).symm
    exact hc.trans hF

theorem actual_six_template (P : ConvexPolytope 4) (F : Face P 3)
    (hF : facetVertexCount P F = 6) :
    ∃ (loc : (facePolytope P F.val.isFace).vertices ≃ Fin 6) (i : Fin 7),
      polygonBoundary (facePolytope P F.val.isFace) loc = FiniteCycleCandidates.N6.templates i := by
  apply ActualSmallFacetClassification.six_vertex_classification
  · change faceDim (facePolytope P F.val.isFace).toSet = 3
    rw [facePolytope_toSet]
    exact F.property
  · have hc : (facePolytope P F.val.isFace).vertices.card = facetVertexCount P F := by
      simpa only [facetVertexCount, Nat.card_eq_fintype_card, Fintype.card_coe] using
        (Nat.card_congr (faceVerticesEquiv P F.val.isFace)).symm
    exact hc.trans hF

/-- Every actual residual belongs to one of the five exact finite-family
regimes. There is no assumed facet-size or numerical-budget hypothesis. -/
theorem partition {n : Nat}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hn : P.vertices.card = 10) (hN : 10 ≤ (nonsimplicialFacets P).card)
    (hc : 9 ≤ Fintype.card (SparseSharedRowIndex P e)) : Partition P := by
  have hn_eq : n = 10 := by
    simpa only [Fintype.card_fin, Fintype.card_coe, hn] using Fintype.card_congr e
  subst n
  rcases ActualResidualFacetPartition.actual_residual_partition P hP e hn hN hc with
    hsmall | ⟨hsmall, hsix⟩ | ⟨F, hF, hseven⟩
  · exact .small ⟨hn, hsmall,
      actual_small_facet_budget_mem P hP e hn hN hc hsmall⟩
  · obtain ⟨A, hA, hB⟩ :=
      actual_assignment_mem_catalogue P hP e hn hN hc hsmall hsix
    exact .six ⟨hn, hsmall, A, hA, hB⟩
  · obtain ⟨locF, i, hlocF⟩ := actual_seven_template P F hF
    have hcellF := actualCell_of_template P e.symm F locF
      (FiniteCycleCandidates.N7.templates i) hlocF
    rcases hseven with hother | ⟨G, hG, hother⟩ | ⟨G, hG, hGsix⟩
    · obtain ⟨hE, B, hB, hmatch, hSP, hBP, hT⟩ :=
        ActualSevenNoSixBudget.actual_no_six_covered P hP e hn hN hc F i
          (ActualFaceTransport.labelEmbedding P e.symm F locF) hcellF hother
      rcases hmatch with ⟨hi, hnone, hm, hBE, hq, _, _, _, hp⟩
      have hpolygons := polygon_card_le_four_of_one_large_facet P hP F hother
      have hpactual : (pentagonalFaces P).card = 0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro R hR
        have hsize : Nat.card (VerticesOn P R.val.carrier) = 5 :=
          (Finset.mem_filter.mp hR).2
        have hbound := hpolygons R
        omega
      exact .sevenPure {
        vertices := hn
        facet := F
        seven := hF
        otherSmall := hother
        template := i
        labels := locF
        boundary := hlocF
        row := B
        row_mem := hB
        row_template := hi
        row_six := hnone
        counts := ⟨hm, by omega, hq, hSP, hBP, hT, hp.trans hpactual.symm⟩ }
    · obtain ⟨locG, j, hlocG⟩ := actual_six_template P G hG
      have hcellG := actualCell_of_template P e.symm G locG
        (FiniteCycleCandidates.N6.templates j) hlocG
      obtain ⟨hE, B, hB, hi, hj, hm, hBE, hq, hSP, hBP, hT, hp⟩ :=
        ActualSevenMixedBudget.actual_one_six_covered P hP e hn hN hc F G i j
          (ActualFaceTransport.labelEmbedding P e.symm F locF)
          (ActualFaceTransport.labelEmbedding P e.symm G locG)
          hcellF hcellG hother
      have hsix : (sixVertexFacets P).card = 1 := by
        have hset : sixVertexFacets P = {G} := by
          ext H
          simp only [sixVertexFacets, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_singleton]
          constructor
          · intro hH
            by_contra hHG
            have hHF : H ≠ F := by intro heq; rw [heq, hF] at hH; omega
            have hbound := hother H hHF hHG
            omega
          · rintro rfl
            exact hG
        rw [hset, Finset.card_singleton]
      exact .sevenMixed {
        vertices := hn
        facet := F
        sixFacet := G
        seven := hF
        six := hG
        otherSmall := hother
        six_count := hsix
        template := i
        labels := locF
        boundary := hlocF
        sixTemplate := j
        sixLabels := locG
        sixBoundary := hlocG
        row := B
        row_mem := hB
        row_template := hi
        row_six := hj
        counts := ⟨hm, by omega, hq, hSP, hBP, hT, hp⟩ }
    · obtain ⟨hm, hE, _, hL, _, sp, hSP, hBP, hT⟩ :=
        ActualSevenTwoSixBudget.actual_two_six_covered P hP e hn hN hc F hF
          G hG hGsix
      have hother := (actual_ten_vertex_residual_unique_seven P hP e hn hN hc F hF).1
      exact .sevenTwoSix {
        vertices := hn
        facet := F
        seven := hF
        otherSmall := hother
        six_count := hL
        template := i
        labels := locF
        boundary := hlocF
        squarePyramids := sp
        square_count := hSP
        bipyramid_count := hBP
        tetrahedron_count := hT
        facets := hm
        excess := hE }

/-- Concrete actual coverage of a complete finite family. The object records
all coverage and classification information instead of assuming realizability. -/
def HasClassifiedEncoding (P : ConvexPolytope 4) : Prop :=
  ∃ (n : Nat) (cells : Fin n → ConcreteGrowth.Cell) (quota : Nat → Nat) (root : Fin n),
    ∃ classification : RootedFamilyClosure.FiniteClassification cells quota root,
    ∃ lab : P.vertices ≃ Fin 10,
    ∃ E : Encoding P lab (fun i => decodeCell (cells i)),
      root ∈ E.family ∧
        ∀ k, (E.family.filter fun i => (cells i).kind = k).card = quota k

/-- These five fields are discharged by the concrete finite-family proofs
and their compatible-placement certificates. No field concludes a rational
realization or any density theorem. -/
structure CaseEncodings : Prop where
  small : ∀ (P : ConvexPolytope 4), P.IsFullDim →
    (∀ v : P.vertices, ¬ IsSimpleVertex P v) → SmallCase P → HasClassifiedEncoding P
  six : ∀ (P : ConvexPolytope 4), P.IsFullDim →
    (∀ v : P.vertices, ¬ IsSimpleVertex P v) → SixCase P → HasClassifiedEncoding P
  sevenPure : ∀ (P : ConvexPolytope 4), P.IsFullDim →
    (∀ v : P.vertices, ¬ IsSimpleVertex P v) → SevenPureCase P → HasClassifiedEncoding P
  sevenMixed : ∀ (P : ConvexPolytope 4), P.IsFullDim →
    (∀ v : P.vertices, ¬ IsSimpleVertex P v) → SevenMixedCase P → HasClassifiedEncoding P
  sevenTwoSix : ∀ (P : ConvexPolytope 4), P.IsFullDim →
    (∀ v : P.vertices, ¬ IsSimpleVertex P v) → SevenTwoSixCase P → HasClassifiedEncoding P

theorem rationallyRealizable_of_classifiedEncoding
    (hvalid : ∀ j, j < targetCount → ValidTarget j)
    (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v)
    (h : HasClassifiedEncoding P) : RationallyRealizable P := by
  obtain ⟨n, cells, quota, root, classification, lab, E, hroot, hquota⟩ := h
  exact RootedFamilyClosure.rationallyRealizable_of_encoding hvalid P hP hnonsimple
    lab cells quota root classification E hroot hquota

/-- Closing the actual finite families closes the exact residual target of
the principal theorem, with every mathematical reduction already proved. -/
theorem residual_of_case_encodings
    (hvalid : ∀ j, j < targetCount → ValidTarget j) (hcases : CaseEncodings) :
    PrincipalGeometryAssembly.TenVertexResidualRealizability := by
  intro P hP e hn hnonsimple hN hc
  apply rationallyRealizable_of_classifiedEncoding hvalid P hP hnonsimple
  cases partition P hP e hn hN hc with
  | small h => exact hcases.small P hP hnonsimple h
  | six h => exact hcases.six P hP hnonsimple h
  | sevenPure h => exact hcases.sevenPure P hP hnonsimple h
  | sevenMixed h => exact hcases.sevenMixed P hP hnonsimple h
  | sevenTwoSix h => exact hcases.sevenTwoSix P hP hnonsimple h

/-- The small and all-six regimes may use their graph-filtered finite
classifications or their direct analytic exclusions. The seven regimes
all use the ordinary rooted-family interface above. These hypotheses are
exact case-family endpoints; they are not additional assumptions on the
polytope in the resulting residual theorem. -/
theorem residual_of_family_resolutions
    (hvalid : ∀ j, j < targetCount → ValidTarget j)
    (hsmall : ∀ (P : ConvexPolytope 4), P.IsFullDim →
      (∀ v : P.vertices, ¬ IsSimpleVertex P v) → SmallCase P → RationallyRealizable P)
    (hsix : ∀ (P : ConvexPolytope 4), P.IsFullDim →
      (∀ v : P.vertices, ¬ IsSimpleVertex P v) → SixCase P → RationallyRealizable P)
    (hpure : ∀ (P : ConvexPolytope 4), P.IsFullDim →
      (∀ v : P.vertices, ¬ IsSimpleVertex P v) → SevenPureCase P → HasClassifiedEncoding P)
    (hmixed : ∀ (P : ConvexPolytope 4), P.IsFullDim →
      (∀ v : P.vertices, ¬ IsSimpleVertex P v) → SevenMixedCase P → HasClassifiedEncoding P)
    (htwo : ∀ (P : ConvexPolytope 4), P.IsFullDim →
      (∀ v : P.vertices, ¬ IsSimpleVertex P v) → SevenTwoSixCase P → HasClassifiedEncoding P) :
    PrincipalGeometryAssembly.TenVertexResidualRealizability := by
  intro P hP e hn hnonsimple hN hc
  cases partition P hP e hn hN hc with
  | small h => exact hsmall P hP hnonsimple h
  | six h => exact hsix P hP hnonsimple h
  | sevenPure h =>
    exact rationallyRealizable_of_classifiedEncoding hvalid P hP hnonsimple
      (hpure P hP hnonsimple h)
  | sevenMixed h =>
    exact rationallyRealizable_of_classifiedEncoding hvalid P hP hnonsimple
      (hmixed P hP hnonsimple h)
  | sevenTwoSix h =>
    exact rationallyRealizable_of_classifiedEncoding hvalid P hP hnonsimple
      (htwo P hP hnonsimple h)

end Papers.RationalityTen.ActualResidualPartition

end
end
end BundlePart4

section BundlePart5
/- Original module: RootedFacetKindCounts. -/

@[expose] public section

/-!
# Exact counts after separating one distinguished facet

The root receives tag zero. Every other object retains the positive tag of
its kind. Thus the root's own kind is decremented exactly once, while all
other kind counts are unchanged.
-/

namespace Papers.RationalityTen.RootedFacetKindCounts

open Finset
variable {α κ : Type*} [Fintype α] [DecidableEq α] [DecidableEq κ]

def rootedTag (kind : α → κ) (tag : κ → ℕ) (root a : α) : ℕ :=
  if a = root then 0 else tag (kind a)

theorem filter_zero (kind : α → κ) (tag : κ → ℕ) (root : α)
    (hpositive : ∀ a, tag a ≠ 0) :
    Finset.univ.filter (fun a => rootedTag kind tag root a = 0) = {root} := by
  ext a
  by_cases ha : a = root <;> simp [rootedTag, ha, hpositive]

theorem filter_positive (kind : α → κ) (tag : κ → ℕ) (root : α)
    (k : ℕ) (hk : k ≠ 0) :
    Finset.univ.filter (fun a => rootedTag kind tag root a = k) =
      (Finset.univ.filter fun a => tag (kind a) = k).erase root := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  dsimp only [rootedTag]
  by_cases ha : a = root <;> simp [ha, hk, Ne.symm hk]

theorem card_zero (kind : α → κ) (tag : κ → ℕ) (root : α)
    (hpositive : ∀ a, tag a ≠ 0) :
    (Finset.univ.filter (fun a => rootedTag kind tag root a = 0)).card = 1 := by
  rw [filter_zero kind tag root hpositive, Finset.card_singleton]

theorem card_kind (kind : α → κ) (tag : κ → ℕ) (root : α)
    (hinjective : Function.Injective tag) (hpositive : ∀ a, tag a ≠ 0)
    (a : κ) :
    (Finset.univ.filter (fun x => rootedTag kind tag root x = tag a)).card =
      (Finset.univ.filter (fun x => kind x = a)).card -
        (if kind root = a then 1 else 0) := by
  rw [filter_positive kind tag root (tag a) (hpositive a)]
  have heq : Finset.univ.filter (fun x => tag (kind x) = tag a) =
      Finset.univ.filter (fun x => kind x = a) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hinjective.eq_iff]
  rw [heq, Finset.card_erase_eq_ite]
  by_cases hroot : kind root = a <;> simp [hroot]

theorem card_outside (kind : α → κ) (tag : κ → ℕ) (root : α)
    (k : ℕ) (hk : k ≠ 0) (houtside : ∀ a, tag a ≠ k) :
    (Finset.univ.filter (fun x => rootedTag kind tag root x = k)).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro x _
  by_cases hx : x = root <;> simp [rootedTag, hx, hk, Ne.symm hk, houtside]

end Papers.RationalityTen.RootedFacetKindCounts

end
end BundlePart5

section BundlePart6
/- Original module: SixFacetEncodedBudgets. -/

@[expose] public section

/-!
# Exact six-facet growth quotas from the encoded actual boundary

The numerical catalogue and the literal boundary search use different orders
for the seven six-vertex facet templates. The explicit permutation below
connects them. Counts are taken from the same encoded family used by the
growth theorem, and the distinguished root is removed exactly once.
-/

noncomputable section
namespace Papers.RationalityTen.SixFacetProfileRefinement

open Finset Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeFacetSurplus
open ChirotopeDensity MatroidChecked.FacetBoundaryEncoding
open CellFacetInvariants LiteralMaskGeometry

theorem Counts.count_countsOf {d : ℕ} (P : ConvexPolytope d)
    (kind : Face P 3 → Kind) (a : Kind) :
    (countsOf P kind).count a = kindCount P kind a := by
  cases a <;> rfl

theorem rooted_quota_counts {d : ℕ} (P : ConvexPolytope d)
    (kind : Face P 3 → Kind) (root : Face P 3) (rootType : Fin 7)
    (hroot : kind root = .six (RawEncoding.oldToCurrent rootType)) (k : ℕ) :
    (Finset.univ.filter (fun F =>
      RootedFacetKindCounts.rootedTag kind RawEncoding.tag root F = k)).card =
      (countsOf P kind).rootedQuota rootType k := by
  by_cases hzero : k = 0
  · subst k
    exact RootedFacetKindCounts.card_zero kind RawEncoding.tag root RawEncoding.tag_ne_zero
  by_cases hle : k ≤ 10
  · have htag := RawEncoding.tag_decodeKind rootType k hzero hle
    have hcount := RootedFacetKindCounts.card_kind kind RawEncoding.tag root
      RawEncoding.tag_injective RawEncoding.tag_ne_zero (RawEncoding.decodeKind rootType k)
    rw [htag] at hcount
    rw [Counts.rootedQuota, if_neg hzero, if_pos hle, Counts.count_countsOf]
    simpa only [kindCount, hroot, eq_comm] using hcount
  · rw [Counts.rootedQuota, if_neg hzero, if_neg hle]
    apply RootedFacetKindCounts.card_outside kind RawEncoding.tag root k hzero
    intro a
    have ha := RawEncoding.tag_le_ten a
    omega

def encodedKind {d c : ℕ} {P : ConvexPolytope d} {lab : P.vertices ≃ Fin 10}
    (cells : Fin c → ConcreteGrowth.Cell) (rootType : Fin 7)
    (E : Encoding P lab (fun i => decodeCell (cells i))) (F : Face P 3) : Kind :=
  RawEncoding.decodeKind rootType (cells (E.index F)).kind

theorem encoded_kind_matches {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (rootType : Fin 7) (root : Fin c)
    (E : Encoding P lab (fun i => decodeCell (cells i)))
    (hcheck : ∀ i, RawProfileCheck cells rootType root i) (F : Face P 3) :
    Matches P F (encodedKind cells rootType E F) := by
  have h := (hcheck (E.index F)).2.2
  rw [E.index_spec] at h
  simpa only [Matches, encodedKind, actualCell_vertex_card,
    actualCell_ridge_size_count, actualCell_excess] using h

theorem encoded_kind_root {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (rootType : Fin 7) (root : Fin c)
    (E : Encoding P lab (fun i => decodeCell (cells i)))
    (hcheck : ∀ i, RawProfileCheck cells rootType root i)
    (F : Face P 3) (hroot : E.index F = root) :
    encodedKind cells rootType E F = .six (RawEncoding.oldToCurrent rootType) := by
  have hz := (hcheck (E.index F)).2.1.mpr hroot
  simp only [encodedKind, hz, RawEncoding.decodeKind]

theorem encoded_rooted_tag {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (rootType : Fin 7) (root : Fin c)
    (E : Encoding P lab (fun i => decodeCell (cells i)))
    (hcheck : ∀ i, RawProfileCheck cells rootType root i)
    (F : Face P 3) (hroot : E.index F = root) (G : Face P 3) :
    (cells (E.index G)).kind = RootedFacetKindCounts.rootedTag
      (encodedKind cells rootType E) RawEncoding.tag F G := by
  unfold RootedFacetKindCounts.rootedTag
  by_cases hGF : G = F
  · subst G
    rw [if_pos rfl]
    exact (hcheck (E.index F)).2.1.mpr hroot
  · rw [if_neg hGF]
    have hz : (cells (E.index G)).kind ≠ 0 := by
      intro hz
      apply hGF
      apply E.index_injective
      exact ((hcheck (E.index G)).2.1.mp hz).trans hroot.symm
    exact (RawEncoding.tag_decodeKind rootType _ hz (hcheck (E.index G)).1).symm

/-- The exact actual type counts and the growth target are derived together
from one complete encoding. No independently chosen profile assignment can
alter the quota of a combinatorial facet type. -/
theorem actual_six_literal_target {d c : ℕ} {P : ConvexPolytope d}
    {lab : P.vertices ≃ Fin 10} (cells : Fin c → ConcreteGrowth.Cell)
    (E : Encoding P lab (fun i => decodeCell (cells i))) (hP : P.dim = 4)
    (rootType : Fin 7) (root : Fin c) (F : Face P 3) (hroot : E.index F = root)
    (hwell : ∀ i, WellFormed (cells i))
    (hcheck : ∀ i, RawProfileCheck cells rootType root i) :
    ∃ C : Counts, C.Refines (actualAllSixFacetBudget P) ∧
      GrowthRenaming.Target (fun a => SparseGrowthDAG.has (ConcreteGrowth.ridgeList cells a))
        (fun a b => ConcreteGrowth.compatible (cells a) (cells b))
        (fun a => (cells a).kind) (C.rootedQuota rootType) E.family.toList := by
  let kind := encodedKind cells rootType E
  let C := countsOf P kind
  have hk : ∀ G, Matches P G (kind G) := encoded_kind_matches cells rootType root E hcheck
  have hr : kind F = .six (RawEncoding.oldToCurrent rootType) :=
    encoded_kind_root cells rootType root E hcheck F hroot
  refine ⟨C, counts_refine_actual P hP kind hk, ?_⟩
  apply LiteralMaskGeometry.actual_literal_target cells hwell E hP
  intro k
  rw [ActualGrowthTarget.encoded_kind_card]
  simp_rw [encoded_rooted_tag cells rootType root E hcheck F hroot]
  exact (rooted_quota_counts P kind F rootType hr k).le

/-- Every encoded all-six residual supplies both a literal growth target
and its row in the complete 478-row catalogue, using the same facet counts. -/
theorem actual_six_literal_target_mem_catalogue {n c : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hn : P.vertices.card = 10) (hN : 10 ≤ (nonsimplicialFacets P).card)
    (hc : 9 ≤ Fintype.card (SparseSharedRowIndex P e))
    (hfacets : ∀ F : Face P 3, facetVertexCount P F ≤ 6)
    (hsix : (sixVertexFacets P).Nonempty)
    (lab : P.vertices ≃ Fin 10) (cells : Fin c → ConcreteGrowth.Cell)
    (E : Encoding P lab (fun i => decodeCell (cells i)))
    (rootType : Fin 7) (root : Fin c) (F : Face P 3) (hroot : E.index F = root)
    (hwell : ∀ i, WellFormed (cells i))
    (hcheck : ∀ i, RawProfileCheck cells rootType root i) :
    ∃ C : Counts, C.Refines (actualAllSixFacetBudget P) ∧
      C.toRow (actualAllSixFacetBudget P) ∈ SixBudgetEnumeration.catalogue ∧
      GrowthRenaming.Target (fun a => SparseGrowthDAG.has (ConcreteGrowth.ridgeList cells a))
        (fun a b => ConcreteGrowth.compatible (cells a) (cells b))
        (fun a => (cells a).kind) (C.rootedQuota rootType) E.family.toList := by
  obtain ⟨C, hC, htarget⟩ := actual_six_literal_target cells E hP
    rootType root F hroot hwell hcheck
  have hbudget := actual_all_six_budget_admissible P hP e hn hN hc hfacets hsix
  exact ⟨C, hC, SixBudgetEnumeration.complete _ (C.toRow_admissible _ hC hbudget), htarget⟩

end Papers.RationalityTen.SixFacetProfileRefinement

end
end
end BundlePart6

section BundlePart7
/- Original module: SixFamilyActualEncoding. -/

@[expose] public section

/-!
# Complete actual encodings of the rooted six-facet families

The same complete local type assignment provides the 478-row numerical
budget and the finite search quota. In particular, the two pairs of local
six-vertex types with equal numerical profiles are never identified.
The producer's explicit old-to-current permutation is used at the root and
at every positive six-type tag.
-/

noncomputable section
namespace Papers.RationalityTen.SixFamilyActualEncoding

open Finset
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting
open ChirotopeDensity ActualFacetCatalogueTransport ActualFacetTemplateAssignment
open SixFacetProfileRefinement
open MatroidChecked.FacetBoundaryEncoding LiteralMaskGeometry
open ActualResidualPartition

local instance faceFintype (P : ConvexPolytope 4) (k : Nat) :
    Fintype (Face P k) := Fintype.ofFinite _

/-- Complete finite placement coverage in the producer's exact tag order.
An absent type is omitted only when its actual rooted quota is zero. -/
structure Coverage {n : Nat} (cells : Fin n → ConcreteGrowth.Cell) (root : Fin n)
    (rootType : Fin 7) (quota : Nat → Nat) where
  rootEmbedding : Fin 6 ↪ Fin 10
  rootCell : mapCell rootEmbedding
    (cellOfBoundary (FiniteCycleCandidates.N6.templates (RawEncoding.oldToCurrent rootType))) =
      decodeCell (cells root)
  rootKind : (cells root).kind = 0
  complete : ∀ a : Kind, 0 < quota (RawEncoding.tag a) → ∀ f : Fin a.size ↪ Fin 10,
    (mapCell f (cellOfBoundary a.template)).Compatible (decodeCell (cells root)) →
      ∃ j, (cells j).kind = RawEncoding.tag a ∧
        decodeCell (cells j) = mapCell f (cellOfBoundary a.template)

/-- A complete assignment and a facet with the selected root type produce
one exact classified encoding. No profile-to-type inference is involved. -/
theorem classified_encoding {n : Nat}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (hn : P.vertices.card = 10)
    (A : Assignment P) (F : Face P 3) (rootType : Fin 7)
    (hF : A.kind F = .six (RawEncoding.oldToCurrent rootType))
    (cells : Fin n → ConcreteGrowth.Cell) (root : Fin n)
    (classification : RootedFamilyClosure.FiniteClassification cells
      ((countsOf P A.kind).rootedQuota rootType) root)
    (coverage : Coverage cells root rootType ((countsOf P A.kind).rootedQuota rootType)) :
    HasClassifiedEncoding P := by
  let quota := (countsOf P A.kind).rootedQuota rootType
  let lab₀ : P.vertices ≃ Fin 10 :=
    (Fintype.equivFin P.vertices).trans (finCongr (by simpa only [Fintype.card_coe] using hn))
  have hrootLocal : RealizesKind P F (.six (RawEncoding.oldToCurrent rootType)) := by
    rw [← hF]
    exact A.realizes F
  obtain ⟨loc, hloc⟩ := hrootLocal
  have hcounts (k : Nat) :
      (Finset.univ.filter fun G : Face P 3 =>
        (if G = F then 0 else RawEncoding.tag (A.kind G)) = k).card = quota k := by
    exact rooted_quota_counts P A.kind F rootType hF k
  have hpos (G : Face P 3) (hG : G ≠ F) : 0 < quota (RawEncoding.tag (A.kind G)) := by
    rw [← hcounts]
    apply Finset.card_pos.mpr
    exact ⟨G, Finset.mem_filter.mpr ⟨Finset.mem_univ _, if_neg hG⟩⟩
  obtain ⟨lab, E, hroot, htag⟩ := RootedKindedActualEncoding.normalized_encoding_of_templates
    Kind.size Kind.template RawEncoding.tag P lab₀ cells root F
    (.six (RawEncoding.oldToCurrent rootType)) loc hloc
    coverage.rootEmbedding coverage.rootCell coverage.rootKind A.kind A.realizes
    (fun a => 0 < quota (RawEncoding.tag a)) hpos coverage.complete
  obtain ⟨_, hquota⟩ := RootedKindedActualEncoding.literal_target_of_tag_counts
    cells E hP classification.wellFormed
    (fun G => if G = F then 0 else RawEncoding.tag (A.kind G)) htag quota hcounts
  exact ⟨n, cells, quota, root, classification, lab, E,
    (E.mem_family root).mpr ⟨F, hroot⟩, hquota⟩

/-- Positive count of a complete six-vertex type supplies an actual root
facet of exactly that type. -/
theorem root_exists (P : ConvexPolytope 4) (A : Assignment P) (rootType : Fin 7)
    (h : 0 < (countsOf P A.kind).six (RawEncoding.oldToCurrent rootType)) :
    ∃ F : Face P 3, A.kind F = .six (RawEncoding.oldToCurrent rootType) := by
  obtain ⟨F, hF⟩ := Finset.card_pos.mp h
  exact ⟨F, (Finset.mem_filter.mp hF).2⟩

/-- The exact numerical row chooses a positive root type; the geometric
normalization is then automatic. -/
theorem six_case {n : Nat} (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (C : SixCase P) (rootType : Fin 7)
    (hrootType : 0 < (countsOf P C.assignment.kind).six (RawEncoding.oldToCurrent rootType))
    (cells : Fin n → ConcreteGrowth.Cell) (root : Fin n)
    (classification : RootedFamilyClosure.FiniteClassification cells
      ((countsOf P C.assignment.kind).rootedQuota rootType) root)
    (coverage : Coverage cells root rootType
      ((countsOf P C.assignment.kind).rootedQuota rootType)) : HasClassifiedEncoding P := by
  obtain ⟨F, hF⟩ := root_exists P C.assignment rootType hrootType
  exact classified_encoding P hP C.vertices C.assignment F rootType hF cells root
    classification coverage

end Papers.RationalityTen.SixFamilyActualEncoding

end
end
end BundlePart7

section BundlePart8
/- Original module: ActualResidualTargetAssembly. -/

@[expose] public section

/-!
# The residual classification with its complete terminal boundary

The finite reduction in Proposition 9 identifies a complete combinatorial
boundary. This module retains that conclusion through the actual-polytope
partition, so that the projection and Appendix B alternatives can be read
off afterwards. The finite-family arguments remain explicit inputs here.
-/

noncomputable section
namespace Papers.RationalityTen.ActualResidualTargetAssembly

open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFacetSurplus
open ChirotopeDensity ActualResidualPartition ActualLeafTargetCoverage
open Nonrational.TerminalData Nonrational.TerminalVerification

/-- Every actual residual polytope has a complete checked terminal boundary.
There is no facet-size restriction or assumed finite encoding in this
statement. Its hypotheses are exactly the remaining geometric case. -/
def TenVertexResidualTargetCoverage : Prop :=
  ∀ (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin 10 ≃ P.vertices),
    P.vertices.card = 10 →
    (∀ v : VertexType P, ¬ IsSimpleVertex P v) →
    10 ≤ (nonsimplicialFacets P).card →
    9 ≤ Fintype.card (SparseSharedRowIndex P e) →
    HasTerminal P

theorem hasTerminal_of_classifiedEncoding
    (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v)
    (h : HasClassifiedEncoding P) : HasTerminal P := by
  obtain ⟨n, cells, quota, root, classification, lab, E, hroot, hquota⟩ := h
  exact RootedFamilyClosure.hasTerminal_of_encoding P hP hnonsimple
    lab cells quota root classification E hroot hquota

theorem residual_of_case_encodings (hcases : CaseEncodings) :
    TenVertexResidualTargetCoverage := by
  intro P hP e hn hnonsimple hN hc
  apply hasTerminal_of_classifiedEncoding P hP hnonsimple
  cases partition P hP e hn hN hc with
  | small h => exact hcases.small P hP hnonsimple h
  | six h => exact hcases.six P hP hnonsimple h
  | sevenPure h => exact hcases.sevenPure P hP hnonsimple h
  | sevenMixed h => exact hcases.sevenMixed P hP hnonsimple h
  | sevenTwoSix h => exact hcases.sevenTwoSix P hP hnonsimple h

/-- Rooted and graph-conditioned searches share the same geometric
conclusion. In particular the graph branches keep their full target
conditions inside their separately checked coverage proofs. -/
theorem residual_of_family_coverages
    (hsmall : ∀ (P : ConvexPolytope 4), P.IsFullDim →
      (∀ v : P.vertices, ¬ IsSimpleVertex P v) → SmallCase P → HasTerminal P)
    (hsix : ∀ (P : ConvexPolytope 4), P.IsFullDim →
      (∀ v : P.vertices, ¬ IsSimpleVertex P v) → SixCase P → HasTerminal P)
    (hpure : ∀ (P : ConvexPolytope 4), P.IsFullDim →
      (∀ v : P.vertices, ¬ IsSimpleVertex P v) → SevenPureCase P → HasClassifiedEncoding P)
    (hmixed : ∀ (P : ConvexPolytope 4), P.IsFullDim →
      (∀ v : P.vertices, ¬ IsSimpleVertex P v) → SevenMixedCase P → HasClassifiedEncoding P)
    (htwo : ∀ (P : ConvexPolytope 4), P.IsFullDim →
      (∀ v : P.vertices, ¬ IsSimpleVertex P v) → SevenTwoSixCase P → HasClassifiedEncoding P) :
    TenVertexResidualTargetCoverage := by
  intro P hP e hn hnonsimple hN hc
  cases partition P hP e hn hN hc with
  | small h => exact hsmall P hP hnonsimple h
  | six h => exact hsix P hP hnonsimple h
  | sevenPure h =>
    exact hasTerminal_of_classifiedEncoding P hP hnonsimple (hpure P hP hnonsimple h)
  | sevenMixed h =>
    exact hasTerminal_of_classifiedEncoding P hP hnonsimple (hmixed P hP hnonsimple h)
  | sevenTwoSix h =>
    exact hasTerminal_of_classifiedEncoding P hP hnonsimple (htwo P hP hnonsimple h)

/-- The same complete boundary coverage also supplies the exact residual
realizability input to Theorem 2. -/
theorem realizability_of_coverage
    (hvalid : ∀ j, j < targetCount → ValidTarget j)
    (hcoverage : TenVertexResidualTargetCoverage) :
    PrincipalGeometryAssembly.TenVertexResidualRealizability := by
  intro P hP e hn hnonsimple hN hc
  exact rationallyRealizable_of_hasTerminal hvalid P hP
    (hcoverage P hP e hn hnonsimple hN hc)

#print axioms residual_of_family_coverages
#print axioms realizability_of_coverage

end Papers.RationalityTen.ActualResidualTargetAssembly

end
end
end BundlePart8

section BundlePart9
/- Original module: CompletedSix.BudgetRecovery. -/

@[expose] public section

/-!
# Recovering exact facet counts from a six-facet budget

The numerical row records every six-vertex type separately. Its derived
small-facet counts agree with the actual counts because `Counts.Refines`
contains exact incidence equations. This module makes that recovery
explicit, including the permutation used by the finite rooted searches.
-/

noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSix

open ChirotopeDensity SixFacetProfileRefinement SixBudgetEnumeration
open Papers.PolytopeFacetSurplus

/-- The complete local type counts encoded by one numerical row. -/
def countsOfRow (B : Row) : Counts where
  T := B.T
  BP := B.BP
  SP := B.SP
  six i := B.types.getD i.val 0

/-- Conversion to a catalogue row retains every local type count. -/
theorem countsOfRow_toRow (C : Counts) (B : AllSixFacetBudget)
    (h : C.Refines B) : countsOfRow (C.toRow B) = C := by
  obtain ⟨_, _, _, hSP, hBP, hT⟩ := C.toRow_counts B h
  have hs : (fun i : Fin 7 => (C.toRow B).types.getD i.val 0) = C.six := by
    funext i
    fin_cases i <;> rfl
  unfold countsOfRow
  rw [hT, hBP, hSP, hs]

/-- Equality with an enumerated row identifies the actual count structure. -/
theorem counts_eq_of_row (C : Counts) (B : AllSixFacetBudget)
    (h : C.Refines B) (R : Row) (hrow : C.toRow B = R) :
    C = countsOfRow R := by
  rw [← hrow]
  exact (countsOfRow_toRow C B h).symm

/-- In particular, the exact rooted quota is recovered, with no assumption
that the polygon profile determines a six-vertex combinatorial type. -/
theorem rootedQuota_eq_of_row (C : Counts) (B : AllSixFacetBudget)
    (h : C.Refines B) (R : Row) (hrow : C.toRow B = R) (r : Fin 7) :
    C.rootedQuota r = (countsOfRow R).rootedQuota r := by
  rw [counts_eq_of_row C B h R hrow]

/-- Only the eleven actual kind tags need a literal quota comparison. -/
theorem rootedQuota_eq_of_fin (C : Counts) (r : Fin 7) (q : ℕ → ℕ)
    (hsmall : ∀ k : Fin 11, C.rootedQuota r k.val = q k.val)
    (hlarge : ∀ k, 10 < k → q k = 0) : C.rootedQuota r = q := by
  funext k
  by_cases hk : k ≤ 10
  · exact hsmall ⟨k, by omega⟩
  · have hne : k ≠ 0 := by omega
    simp only [Counts.rootedQuota, if_neg hne, if_neg hk]
    exact (hlarge k (by omega)).symm

#print axioms countsOfRow_toRow
#print axioms rootedQuota_eq_of_row

end Papers.RationalityTen.CompletedSix

end
end
end BundlePart9

section BundlePart10
/- Original module: CompletedSix.RootedRowCertificate. -/

@[expose] public section

/-!
# A checked rooted certificate for one exact six-facet budget

A certificate records the complete local candidate universe, its geometric
placement coverage, and a kernel-checked exhaustive classification. The
quota is recovered from all seven six-vertex counts, so equal polygon-size
profiles are never identified. The distinguished type has a positive actual
count and therefore supplies an actual facet for normalization.
-/

noncomputable section
set_option autoImplicit false
namespace Papers.RationalityTen.CompletedSix

open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting
open ChirotopeDensity SixFacetProfileRefinement SixBudgetEnumeration
open ActualResidualPartition ActualResidualTargetAssembly ActualLeafTargetCoverage

/-- Complete finite evidence for a single numerical row. -/
structure RootedRowCertificate (B : Row) where
  rootType : Fin 7
  cellCount : ℕ
  cells : Fin cellCount → ConcreteGrowth.Cell
  root : Fin cellCount
  positiveRoot : 0 < (countsOfRow B).six (RawEncoding.oldToCurrent rootType)
  classification : RootedFamilyClosure.FiniteClassification cells
    ((countsOfRow B).rootedQuota rootType) root
  coverage : SixFamilyActualEncoding.Coverage cells root rootType
    ((countsOfRow B).rootedQuota rootType)

/-- Exact count recovery turns a checked row into a classified encoding of
an arbitrary actual polytope with that row. -/
theorem RootedRowCertificate.classified {B : Row} (D : RootedRowCertificate B)
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (C : SixCase P)
    (hrow : (countsOf P C.assignment.kind).toRow (actualAllSixFacetBudget P) = B) :
    HasClassifiedEncoding P := by
  have hcounts : countsOf P C.assignment.kind = countsOfRow B :=
    counts_eq_of_row _ _ C.refines B hrow
  refine SixFamilyActualEncoding.six_case P hP C D.rootType ?_ D.cells D.root ?_ ?_
  · simpa only [hcounts] using D.positiveRoot
  · simpa only [hcounts] using D.classification
  · simpa only [hcounts] using D.coverage

/-- The complete leaf boundary is retained in the geometric conclusion. -/
theorem RootedRowCertificate.hasTerminal {B : Row} (D : RootedRowCertificate B)
    (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v)
    (C : SixCase P)
    (hrow : (countsOf P C.assignment.kind).toRow (actualAllSixFacetBudget P) = B) :
    HasTerminal P :=
  hasTerminal_of_classifiedEncoding P hP hnonsimple (D.classified P hP C hrow)

#print axioms RootedRowCertificate.classified
#print axioms RootedRowCertificate.hasTerminal

end Papers.RationalityTen.CompletedSix

end
end
end BundlePart10
