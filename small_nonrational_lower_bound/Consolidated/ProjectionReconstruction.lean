module
public import Papers.SparseSharedFacetRelations
public import Papers.ConstantRankVectorCharts
public import Papers.ProjectionHeightLifting
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Papers.IntrinsicChirotope
public import Papers.RationalityTenOrdinaryPolytopeDensity
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Papers.RationalityTenAffineFaceTransport
public import Papers.RationalityTenFacetExtension
public import Papers.HomogeneousSpanDimension
public import Papers.FaceVertexCardinality
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Papers.ActualCoordinateRealizations
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Papers.ActualProjectionHeightCoverage
public import Mathlib.Logic.Equiv.Fin.Basic

/-! Canonical source bundle; each original file retains its own scopes. -/

section BundlePart0
/- Source: Papers/ZeroColumnRestoration.lean -/



@[expose] public section

/-!
# Restoring vertices whose facet-relation columns vanish

The proof uses an exact rank identity instead of an informal join argument.
For each facet S, its full relation space is already supported on the
retained labels I. Thus rank(S) = rank(S ∩ I) + |S \ I|. Arbitrary nearby
restored vertices cannot raise the facet rank once its retained rank is
fixed, and lower semicontinuity prevents the rank from dropping.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Matrix Filter Topology
open scoped Classical
open Papers.RationalityTen.PlaneRationalization (mem_closure_inter_of_eventually)

theorem globalRelationSpace_eq_inter_of_supported {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (S I : Finset (Fin n))
    (hzero : ∀ v ∈ globalRelationSpace p S, ∀ j, j ∉ I → v j = 0) :
    globalRelationSpace p S = globalRelationSpace p (S ∩ I) := by
  apply le_antisymm
  · intro v hv
    obtain ⟨hs, hker⟩ := (mem_globalRelationSpace_iff p S v).mp hv
    apply (mem_globalRelationSpace_iff p (S ∩ I) v).mpr
    refine ⟨?_, hker⟩
    intro j hj
    by_cases hjS : j ∈ S
    · exact hzero v hv j (fun hjI => hj (Finset.mem_inter.mpr ⟨hjS, hjI⟩))
    · exact hs j hjS
  · exact globalRelationSpace_mono p Finset.inter_subset_left

theorem subsetRank_eq_inter_add_of_supported {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (S I : Finset (Fin n))
    (hzero : ∀ v ∈ globalRelationSpace p S, ∀ j, j ∉ I → v j = 0) :
    subsetRank p S = subsetRank p (S ∩ I) + (S \ I).card := by
  have h₁ := globalRelationSpace_finrank p S
  have h₂ := globalRelationSpace_finrank p (S ∩ I)
  rw [globalRelationSpace_eq_inter_of_supported p S I hzero] at h₁
  have hcard := Finset.card_inter_add_card_sdiff S I
  omega

theorem supportedRowSpan_zero_columns {c n : ℕ}
    (C : Matrix (Fin c) (Fin n) ℝ) (S I : Finset (Fin n))
    (hzero : ∀ i j, j ∉ I → C i j = 0) :
    ∀ v ∈ supportedRowSpan C S, ∀ j, j ∉ I → v j = 0 := by
  intro v hv j hj
  let ev : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x => x j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hle : supportedRowSpan C S ≤ ev.ker := by
    apply Submodule.span_le.mpr
    rintro w ⟨i, rfl, hi⟩
    exact hzero i j hj
  exact hle hv

theorem subsetRank_union_le_add_card {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (S T : Finset (Fin n)) :
    subsetRank p (S ∪ T) ≤ subsetRank p S + T.card := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih =>
      rw [Finset.union_insert, Finset.card_insert_of_notMem hi]
      have h := subsetRank_insert_le p (S ∪ T) i
      omega

theorem subsetRank_le_inter_add_card_sdiff {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (S I : Finset (Fin n)) :
    subsetRank p S ≤ subsetRank p (S ∩ I) + (S \ I).card := by
  have heq : (S ∩ I) ∪ (S \ I) = S := by
    ext i
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  simpa only [heq] using subsetRank_union_le_add_card p (S ∩ I) (S \ I)

/-- Facet ranks alone suffice locally: all strict support signs and the
absence of new supporting subsets are supplied by the proved open conditions. -/
theorem rational_polytope_density_from_facet_rank_density {n d : ℕ}
    (p : Fin n → Fin (d + 1) → ℝ) (hp : Spans p)
    (hfirst : ∀ i, p i 0 = 1)
    (hcl : p ∈ closure {q : Fin n → Fin (d + 1) → ℝ |
      RationalCoordinates q ∧ (∀ i, q i 0 = 1) ∧
      ∀ S ∈ facetMasks p, subsetRank q S = subsetRank p S}) :
    p ∈ closure {q : Fin n → Fin (d + 1) → ℝ |
      RationalCoordinates q ∧ (∀ i, q i 0 = 1) ∧ Spans q ∧
      LabelledPolytopeEquivalent p q} := by
  have hs := finite_strictSupports_stable_on_rank_strata p (facetMasks p)
    (fun S hS => ((mem_facetMasks p S).mp hS).2.1)
  have hgood := hs.and ((eventually_spans hp).and (eventually_no_new_supported_subsets p))
  have hc := mem_closure_inter_of_eventually hcl hgood
  apply closure_mono ?_ hc
  rintro q ⟨⟨hqr, hqa, hqranks⟩, hqs, hqspan, hqnonew⟩
  have hsupports := hqs hqranks
  have hrec : FacetReconstruction p (facetMasks p) q := by
    refine ⟨hqr, hqa, hqspan, hqranks, hsupports, ?_, ?_, hqnonew⟩
    · intro S hS
      obtain ⟨a, ha⟩ := hsupports S hS
      exact strictSupport_exposed_hull ha ((mem_facetMasks p S).mp hS).1
    · intro S hS i
      obtain ⟨a, ha⟩ := hsupports S hS
      exact strictSupport_label_exact ha ((mem_facetMasks p S).mp hS).1 i
  exact ⟨hqr, hqa, hqspan, labelledPolytopeEquivalent_of_reconstruction hp hfirst hrec⟩

/-- This is the analytic restoration step in Appendix A.4. The core input
preserves exactly the retained parts of old facets, with no conditions on
the free restored coordinates other than rationality and proximity. -/
theorem rational_polytope_density_from_zero_column_core_rank_density {c n d : ℕ}
    (C : Matrix (Fin c) (Fin n) ℝ)
    (p : Fin n → Fin (d + 1) → ℝ) (hp : Spans p)
    (hfirst : ∀ i, p i 0 = 1) (I : Finset (Fin n))
    (hzero : ∀ i j, j ∉ I → C i j = 0)
    (hrelations : ∀ S ∈ facetMasks p, supportedRowSpan C S = globalRelationSpace p S)
    (hcl : p ∈ closure {q : Fin n → Fin (d + 1) → ℝ |
      RationalCoordinates q ∧ (∀ i, q i 0 = 1) ∧
      ∀ S ∈ facetMasks p, subsetRank q (S ∩ I) = subsetRank p (S ∩ I)}) :
    p ∈ closure {q : Fin n → Fin (d + 1) → ℝ |
      RationalCoordinates q ∧ (∀ i, q i 0 = 1) ∧ Spans q ∧
      LabelledPolytopeEquivalent p q} := by
  have hrank (S : Finset (Fin n)) (hS : S ∈ facetMasks p) :
      subsetRank p S = subsetRank p (S ∩ I) + (S \ I).card := by
    apply subsetRank_eq_inter_add_of_supported p S I
    rw [← hrelations S hS]
    exact supportedRowSpan_zero_columns C S I hzero
  have hlower : ∀ᶠ q in 𝓝 p, ∀ S : Finset (Fin n),
      subsetRank p S ≤ subsetRank q S :=
    eventually_all.mpr (fun S => eventually_subsetRank_ge p S)
  have hc := mem_closure_inter_of_eventually hcl hlower
  apply rational_polytope_density_from_facet_rank_density p hp hfirst
  apply closure_mono ?_ hc
  rintro q ⟨⟨hqr, hqa, hcore⟩, hlow⟩
  refine ⟨hqr, hqa, ?_⟩
  intro S hS
  apply Nat.le_antisymm _ (hlow S)
  calc
    subsetRank q S ≤ subsetRank q (S ∩ I) + (S \ I).card :=
      subsetRank_le_inter_add_card_sdiff q S I
    _ = subsetRank p S := by rw [hcore S hS, hrank S hS]

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart0

section BundlePart1
/- Source: Papers/SelectedNormalReconstruction.lean -/




@[expose] public section

/-!
# Reconstructing vertices from a selected family of facet normals

The selected family must contain every nonsimplicial facet. The only ranks
that its approximation has to preserve are the ranks of the normals incident
to each original vertex. Constant-rank kernel charts then reconstruct the
vertices, and the proved local facet-rank criterion supplies the full face
order. This is a local construction, with no appeal to an unformalized
polar-duality theorem.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Matrix Filter Topology
open scoped Classical BigOperators
open PlaneRationalization

def incidentSelectedNormals {m n : ℕ}
    (S : Fin m → Finset (Fin n)) (i : Fin n) : Finset (Fin m) :=
  Finset.univ.filter fun j => i ∈ S j

@[simp] theorem mem_incidentSelectedNormals {m n : ℕ}
    (S : Fin m → Finset (Fin n)) (i : Fin n) (j : Fin m) :
    j ∈ incidentSelectedNormals S i ↔ i ∈ S j := by
  simp only [incidentSelectedNormals, Finset.mem_filter, Finset.mem_univ, true_and]

def incidentRankRealizations {m n r : ℕ}
    (A : Fin m → Fin r → ℝ) (S : Fin m → Finset (Fin n)) :
    Set (Fin m → Fin r → ℝ) :=
  {B | RationalCoordinates B ∧ ∀ i,
    subsetRank B (incidentSelectedNormals S i) =
      subsetRank A (incidentSelectedNormals S i)}

def normalizePointRows {n d : ℕ} (p : Fin n → Fin (d + 1) → ℝ) :
    Fin n → Fin (d + 1) → ℝ := fun i j => p i j / p i 0

theorem normalizePointRows_self {n d : ℕ}
    (p : Fin n → Fin (d + 1) → ℝ) (hfirst : ∀ i, p i 0 = 1) :
    normalizePointRows p = p := by
  ext i j
  simp only [normalizePointRows, hfirst, div_one]

theorem normalizePointRows_continuousAt {n d : ℕ}
    (p : Fin n → Fin (d + 1) → ℝ) (hfirst : ∀ i, p i 0 ≠ 0) :
    ContinuousAt normalizePointRows p := by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  have hj : Continuous (fun q : Fin n → Fin (d + 1) → ℝ => q i j) :=
    (continuous_apply j).comp (continuous_apply i)
  have h0 : Continuous (fun q : Fin n → Fin (d + 1) → ℝ => q i 0) :=
    (continuous_apply 0).comp (continuous_apply i)
  exact (hj.continuousAt (x := p)).div h0.continuousAt (hfirst i)

theorem normalizePointRows_rational {n d : ℕ}
    {p : Fin n → Fin (d + 1) → ℝ} (hp : RationalCoordinates p) :
    RationalCoordinates (normalizePointRows p) :=
  fun i j => (hp i j).div (hp i 0)

theorem normalizePointRows_annihilator {n d : ℕ}
    (p : Fin n → Fin (d + 1) → ℝ) (a : Fin (d + 1) → ℝ)
    (i : Fin n) (h : a ⬝ᵥ p i = 0) :
    a ⬝ᵥ normalizePointRows p i = 0 := by
  simp only [normalizePointRows, dotProduct, ← mul_div_assoc, ← Finset.sum_div]
  change (a ⬝ᵥ p i) / p i 0 = 0
  rw [h, zero_div]

/-- Approximation of the normal configuration in precisely the required
rank strata lifts to nearby rational vertices satisfying every incidence. -/
theorem rational_selected_normal_incidence_lift {m n d : ℕ}
    (p : Fin n → Fin (d + 1) → ℝ) (hfirst : ∀ i, p i 0 = 1)
    (A : Fin m → Fin (d + 1) → ℝ) (S : Fin m → Finset (Fin n))
    (hzero : ∀ j i, i ∈ S j → A j ⬝ᵥ p i = 0)
    (hA : A ∈ closure (incidentRankRealizations A S)) :
    (A, p) ∈ closure
      {z : (Fin m → Fin (d + 1) → ℝ) × (Fin n → Fin (d + 1) → ℝ) |
        RationalCoordinates z.1 ∧ RationalCoordinates z.2 ∧
        (∀ i, z.2 i 0 = 1) ∧ ∀ j i, i ∈ S j → z.1 j ⬝ᵥ z.2 i = 0} := by
  let Z := incidentSelectedNormals S
  let M : Fin n → Matrix (Fin m) (Fin (d + 1)) ℝ := fun i => maskRows A (Z i)
  let C : (i : Fin n) → RowKernelChart (M i) :=
    fun i => Classical.choice (exists_rowKernelChart (M i))
  have hpker (i : Fin n) : (M i).mulVec (p i) = 0 := by
    apply (maskRows_mulVec_zero_iff A (Z i) (p i)).mpr
    intro j hj
    rw [dotProduct_comm]
    exact hzero j i ((mem_incidentSelectedNormals S i j).mp hj)
  let G := fun z : (Fin m → Fin (d + 1) → ℝ) × (Fin n → Fin (d + 1) → ℝ) =>
    fun i => (C i).eval (maskRows z.1 (Z i)) (z.2 i)
  have hGbase : G (A, p) = p := by
    funext i
    exact (C i).self (p i) (hpker i)
  have hGcont : ContinuousAt G (A, p) := by
    apply continuousAt_pi.mpr
    intro i
    have hparam : Continuous
        (fun z : (Fin m → Fin (d + 1) → ℝ) × (Fin n → Fin (d + 1) → ℝ) =>
          (maskRows z.1 (Z i), z.2 i)) :=
      ((maskRows_continuous (Z i)).comp continuous_fst).prodMk
        ((continuous_apply i).comp continuous_snd)
    exact ((C i).continuousAt (p i)).comp_of_eq
      (hparam.continuousAt (x := (A,p))) rfl
  let F := fun z : (Fin m → Fin (d + 1) → ℝ) × (Fin n → Fin (d + 1) → ℝ) =>
    (z.1, normalizePointRows (G z))
  have hfirstne : ∀ i, p i 0 ≠ 0 := by
    intro i
    rw [hfirst]
    exact one_ne_zero
  have hFcont : ContinuousAt F (A, p) := by
    apply continuous_fst.continuousAt.prodMk
    have hn := normalizePointRows_continuousAt p hfirstne
    rw [← hGbase] at hn
    exact hn.comp hGcont
  have hFbase : F (A, p) = (A, p) := by
    simp only [F, hGbase, normalizePointRows_self p hfirst]
  have hrows : ∀ᶠ z in 𝓝 (A, p), ∀ i,
      LinearIndependent ℝ (fun a => maskRows z.1 (Z i) ((C i).rows a)) := by
    apply eventually_all.mpr
    intro i
    have hc : Continuous (fun z : (Fin m → Fin (d + 1) → ℝ) ×
        (Fin n → Fin (d + 1) → ℝ) => maskRows z.1 (Z i)) :=
      (maskRows_continuous (Z i)).comp continuous_fst
    exact (hc.continuousAt (x := (A,p))).tendsto.eventually (C i).eventually_independent
  have hdenom : ∀ᶠ z in 𝓝 (A, p), ∀ i, G z i 0 ≠ 0 := by
    apply eventually_all.mpr
    intro i
    have hcoord := (continuous_apply 0).continuousAt.comp
      ((continuous_apply i).continuousAt.comp hGcont)
    apply hcoord.eventually_ne
    change G (A,p) i 0 ≠ 0
    rw [hGbase]
    exact hfirstne i
  have hprod : (A, p) ∈ closure
      (incidentRankRealizations A S ×ˢ
        {q : Fin n → Fin (d + 1) → ℝ | RationalCoordinates q}) := by
    rw [closure_prod_eq]
    exact ⟨hA, rationalCoordinates_dense n (d + 1) p⟩
  have hcl := mem_closure_inter_of_eventually hprod (hrows.and hdenom)
  have himage := mem_closure_image hFcont hcl
  rw [hFbase] at himage
  apply closure_mono (s := F '' _) ?_ himage
  rintro _ ⟨⟨B, w⟩, ⟨⟨hB, hw⟩, hgood⟩, rfl⟩
  have hGrat : RationalCoordinates (G (B, w)) := by
    intro i
    exact (C i).rational (maskRows_rational hB.1 (Z i)) (hw i)
  refine ⟨hB.1, normalizePointRows_rational hGrat, ?_, ?_⟩
  · intro i
    exact div_self (hgood.2 i)
  · intro j i hi
    apply normalizePointRows_annihilator
    have hrank : (maskRows B (Z i)).rank = (M i).rank := by
      dsimp only [M]
      rw [maskRows_rank, maskRows_rank]
      exact hB.2 i
    have hker := (C i).mem (maskRows B (Z i)) hrank (hgood.1 i) (w i)
    have hval := (maskRows_mulVec_zero_iff B (Z i) (G (B, w) i)).mp hker j
      ((mem_incidentSelectedNormals S i j).mpr hi)
    simpa only [dotProduct_comm] using hval

theorem subsetRank_le_card_labels {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (S : Finset (Fin n)) :
    subsetRank p S ≤ S.card := by
  have h := globalRelationSpace_finrank p S
  omega

/-- All omitted facets are simplices. Thus exact incidences for the selected
normal rows, together with open rank lower bounds, preserve every facet rank.
The final conclusion includes the complete labelled exposed-face order. -/
theorem rational_polytope_density_from_selected_normal_rank_density {m n d : ℕ}
    (p : Fin n → Fin (d + 1) → ℝ) (hp : Spans p)
    (hfirst : ∀ i, p i 0 = 1)
    (A : Fin m → Fin (d + 1) → ℝ) (S : Fin m → Finset (Fin n))
    (hnormal : ∀ j, A j ≠ 0)
    (hzero : ∀ j i, i ∈ S j → A j ⬝ᵥ p i = 0)
    (hcover : ∀ T ∈ facetMasks p, T.card ≤ d ∨ ∃ j, S j = T)
    (hA : A ∈ closure (incidentRankRealizations A S)) :
    p ∈ closure {q : Fin n → Fin (d + 1) → ℝ |
      RationalCoordinates q ∧ (∀ i, q i 0 = 1) ∧ Spans q ∧
      LabelledPolytopeEquivalent p q} := by
  have hnormal_open : ∀ᶠ z in 𝓝 (A, p), ∀ j, z.1 j ≠ 0 := by
    apply eventually_all.mpr
    intro j
    exact ((continuous_apply j).comp continuous_fst).continuousAt.eventually_ne (hnormal j)
  have hlower : ∀ᶠ z in 𝓝 (A, p), ∀ T : Finset (Fin n),
      subsetRank p T ≤ subsetRank z.2 T := by
    apply eventually_all.mpr
    intro T
    exact (continuous_snd.continuousAt (x := (A,p))).tendsto.eventually
      (eventually_subsetRank_ge p T)
  have hcl := mem_closure_inter_of_eventually
    (rational_selected_normal_incidence_lift p hfirst A S hzero hA)
    (hnormal_open.and hlower)
  have himage := mem_closure_image continuous_snd.continuousAt hcl
  apply rational_polytope_density_from_facet_rank_density p hp hfirst
  apply closure_mono (s := Prod.snd '' _) ?_ himage
  rintro q ⟨⟨B, q'⟩, ⟨⟨hBr, hqr, hqfirst, hinc⟩, hBn, hlow⟩, rfl⟩
  refine ⟨hqr, hqfirst, ?_⟩
  intro T hT
  have hTrank := ((mem_facetMasks p T).mp hT).2.2
  apply Nat.le_antisymm _ (hlow T)
  change subsetRank q' T ≤ subsetRank p T
  rcases hcover T hT with hsmall | ⟨j, hj⟩
  · have hb := (subsetRank_le_card_labels q' T).trans hsmall
    omega
  · have hb := subsetRank_add_one_le_of_annihilator q' T (B j) (hBn j) (by
      intro i hi
      exact hinc j i (hj.symm ▸ hi))
    omega

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart1

section BundlePart2
/- Source: Papers/ProjectionHeightRelations.lean -/




@[expose] public section

/-!
# Why the height equations preserve complete facet hyperplanes

Appending a height coordinate cannot increase the rank of a selected point
set when every relation on that set annihilates the heights. This is proved
by an inclusion of the actual relation spaces and rank-nullity. Thus the
height step controls the entire facet, not only a chosen collection of
equations on its vertices.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Matrix Filter Topology
open scoped Classical BigOperators

def appendHeights {n r : ℕ} (q : Fin n → Fin r → ℝ) (h : Fin n → ℝ) :
    Fin n → Fin (r + 1) → ℝ := fun i => Fin.cases (h i) (q i)

theorem globalRelationSpace_le_appendHeights {n r : ℕ}
    (q : Fin n → Fin r → ℝ) (h : Fin n → ℝ) (S : Finset (Fin n))
    (hzero : ∀ v ∈ globalRelationSpace q S, h ⬝ᵥ v = 0) :
    globalRelationSpace q S ≤ globalRelationSpace (appendHeights q h) S := by
  intro v hv
  obtain ⟨hs, hq⟩ := (mem_globalRelationSpace_iff q S v).mp hv
  apply (mem_globalRelationSpace_iff (appendHeights q h) S v).mpr
  refine ⟨hs, ?_⟩
  ext a
  cases a using Fin.cases with
  | zero => exact hzero v hv
  | succ a => exact congrFun hq a

theorem subsetRank_appendHeights_le {n r : ℕ}
    (q : Fin n → Fin r → ℝ) (h : Fin n → ℝ) (S : Finset (Fin n))
    (hzero : ∀ v ∈ globalRelationSpace q S, h ⬝ᵥ v = 0) :
    subsetRank (appendHeights q h) S ≤ subsetRank q S := by
  have hle := Submodule.finrank_mono (globalRelationSpace_le_appendHeights q h S hzero)
  have hdim₁ := globalRelationSpace_finrank q S
  have hdim₂ := globalRelationSpace_finrank (appendHeights q h) S
  omega

theorem rowSpan_annihilates_kernel {c n : ℕ}
    (C : Matrix (Fin c) (Fin n) ℝ) (h : Fin n → ℝ)
    (hCh : C.mulVec h = 0) :
    ∀ v ∈ Submodule.span ℝ (Set.range C), h ⬝ᵥ v = 0 := by
  have hle : Submodule.span ℝ (Set.range C) ≤ (dotLinear h).ker := by
    apply Submodule.span_le.mpr
    rintro v ⟨j, rfl⟩
    change h ⬝ᵥ C j = 0
    rw [dotProduct_comm]
    exact congrFun hCh j
  exact fun v hv => hle hv

theorem subsetRank_appendHeights_le_of_matrix {c n r : ℕ}
    (q : Fin n → Fin r → ℝ) (h : Fin n → ℝ)
    (C : Matrix (Fin c) (Fin n) ℝ) (S : Finset (Fin n))
    (hrelations : globalRelationSpace q S ≤ Submodule.span ℝ (Set.range C))
    (hCh : C.mulVec h = 0) :
    subsetRank (appendHeights q h) S ≤ subsetRank q S :=
  subsetRank_appendHeights_le q h S
    (fun v hv => rowSpan_annihilates_kernel C h hCh v (hrelations hv))

theorem subsetRank_pointwise_smul_le {n r : ℕ}
    (q : Fin n → Fin r → ℝ) (t : Fin n → ℝ) (S : Finset (Fin n)) :
    subsetRank (fun i => t i • q i) S ≤ subsetRank q S := by
  apply Submodule.finrank_mono
  apply Submodule.span_le.mpr
  rintro v ⟨i, hi, rfl⟩
  exact Submodule.smul_mem _ (t i) (Submodule.subset_span ⟨i, hi, rfl⟩)

theorem subsetRank_normalizePointRows_le {n r : ℕ}
    (q : Fin n → Fin (r + 1) → ℝ) (S : Finset (Fin n)) :
    subsetRank (normalizePointRows q) S ≤ subsetRank q S := by
  have heq : normalizePointRows q = (fun i => (q i 0)⁻¹ • q i) := by
    ext i a
    simp only [normalizePointRows, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq]
  exact subsetRank_pointwise_smul_le q _ S

/-- The projected facet has at most r homogeneous dimensions. The height
equations and dehomogenization keep it in an r-dimensional hyperplane of
the reconstructed (r+1)-dimensional homogeneous point configuration. -/
theorem reconstructed_facet_rank_upper {c n r : ℕ}
    (q : Fin n → Fin r → ℝ) (h : Fin n → ℝ)
    (C : Matrix (Fin c) (Fin n) ℝ) (S : Finset (Fin n))
    (hrelations : globalRelationSpace q S ≤ Submodule.span ℝ (Set.range C))
    (hCh : C.mulVec h = 0) :
    subsetRank (normalizePointRows (appendHeights q h)) S ≤ r := by
  calc
    subsetRank (normalizePointRows (appendHeights q h)) S ≤
        subsetRank (appendHeights q h) S := subsetRank_normalizePointRows_le _ _
    _ ≤ subsetRank q S := subsetRank_appendHeights_le_of_matrix q h C S hrelations hCh
    _ ≤ r := by
      have hb := (Submodule.span ℝ (q '' (↑S : Set (Fin n)))).finrank_le
      change finrank ℝ (Submodule.span ℝ (q '' (↑S : Set (Fin n)))) ≤ r
      simpa using hb

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart2

section BundlePart3
/- Source: Papers/ProjectionCenterFacets.lean -/




@[expose] public section

/-!
# Facets containing the projection center

The distinguished center is the first homogeneous coordinate vector.  A
projected point q with reciprocal height h lifts to (h,q).  After adjoining
the center, a selected family has rank exactly one more than its projected
rank, for every choice of heights.  The proof identifies its actual span as
the direct sum of the zero-height image and the line through the center.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Matrix Filter Topology
open scoped Classical BigOperators
open PlaneRationalization

def projectionCenter (r : ℕ) : Fin (r + 1) → ℝ := Fin.cases 1 (fun _ => 0)

def zeroHeightEmbedding (r : ℕ) : (Fin r → ℝ) →ₗ[ℝ] (Fin (r + 1) → ℝ) where
  toFun x := Fin.cases 0 x
  map_add' x y := by ext a; cases a using Fin.cases <;> simp
  map_smul' t x := by ext a; cases a using Fin.cases <;> simp

theorem zeroHeightEmbedding_injective (r : ℕ) :
    Function.Injective (zeroHeightEmbedding r) := by
  intro x y h
  ext a
  exact congrFun h a.succ

def projectedCenterFamily {n r : ℕ} (q : Fin n → Fin r → ℝ) (h : Fin n → ℝ) :
    Fin (n + 1) → Fin (r + 1) → ℝ :=
  Fin.cases (projectionCenter r) (appendHeights q h)

def centerFacetLabels {n : ℕ} (S : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  insert 0 (S.image Fin.succ)

@[simp] theorem mem_centerFacetLabels_zero {n : ℕ} (S : Finset (Fin n)) :
    (0 : Fin (n + 1)) ∈ centerFacetLabels S := by
  simp [centerFacetLabels]

@[simp] theorem mem_centerFacetLabels_succ {n : ℕ}
    (S : Finset (Fin n)) (i : Fin n) :
    i.succ ∈ centerFacetLabels S ↔ i ∈ S := by
  simp [centerFacetLabels]

@[simp] theorem centerFacetLabels_univ (n : ℕ) :
    centerFacetLabels (Finset.univ : Finset (Fin n)) = Finset.univ := by
  ext i
  cases i using Fin.cases <;> simp

theorem appendHeights_eq_center_add {n r : ℕ}
    (q : Fin n → Fin r → ℝ) (h : Fin n → ℝ) (i : Fin n) :
    appendHeights q h i = h i • projectionCenter r + zeroHeightEmbedding r (q i) := by
  ext a
  cases a using Fin.cases <;> simp [appendHeights, projectionCenter, zeroHeightEmbedding]

theorem projectedCenterFamily_span {n r : ℕ}
    (q : Fin n → Fin r → ℝ) (h : Fin n → ℝ) (S : Finset (Fin n)) :
    Submodule.span ℝ (projectedCenterFamily q h '' (↑(centerFacetLabels S) : Set _)) =
      (Submodule.span ℝ (q '' (↑S : Set _))).map (zeroHeightEmbedding r) ⊔
        Submodule.span ℝ {projectionCenter r} := by
  let U := Submodule.span ℝ (q '' (↑S : Set (Fin n)))
  let W := Submodule.span ℝ
    (projectedCenterFamily q h '' (↑(centerFacetLabels S) : Set (Fin (n + 1))))
  have hcenter : projectionCenter r ∈ W :=
    Submodule.subset_span ⟨0, mem_centerFacetLabels_zero S, rfl⟩
  have hpoint (i : Fin n) (hi : i ∈ S) : appendHeights q h i ∈ W :=
    Submodule.subset_span ⟨i.succ, (mem_centerFacetLabels_succ S i).mpr hi, rfl⟩
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    cases i using Fin.cases with
    | zero =>
      exact (show Submodule.span ℝ {projectionCenter r} ≤
        U.map (zeroHeightEmbedding r) ⊔ Submodule.span ℝ {projectionCenter r} from le_sup_right)
        (Submodule.subset_span (Set.mem_singleton _))
    | succ i =>
      have his : i ∈ S := (mem_centerFacetLabels_succ S i).mp hi
      change appendHeights q h i ∈ _
      rw [appendHeights_eq_center_add]
      apply Submodule.add_mem
      · apply Submodule.smul_mem
        exact (show Submodule.span ℝ {projectionCenter r} ≤
          U.map (zeroHeightEmbedding r) ⊔ Submodule.span ℝ {projectionCenter r} from le_sup_right)
          (Submodule.subset_span (Set.mem_singleton _))
      · apply (show U.map (zeroHeightEmbedding r) ≤
          U.map (zeroHeightEmbedding r) ⊔ Submodule.span ℝ {projectionCenter r} from le_sup_left)
        exact ⟨q i, Submodule.subset_span ⟨i, his, rfl⟩, rfl⟩
  · apply sup_le
    · rw [Submodule.map_span]
      apply Submodule.span_le.mpr
      rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      have hp := W.sub_mem (hpoint i hi) (W.smul_mem (h i) hcenter)
      rw [appendHeights_eq_center_add, add_sub_cancel_left] at hp
      exact hp
    · exact Submodule.span_le.mpr (fun x hx => by
        have hxc : x = projectionCenter r := Set.mem_singleton_iff.mp hx
        subst x
        exact hcenter)

/-- The center contributes one new dimension, independently of the heights. -/
theorem projectedCenterFamily_subsetRank {n r : ℕ}
    (q : Fin n → Fin r → ℝ) (h : Fin n → ℝ) (S : Finset (Fin n)) :
    subsetRank (projectedCenterFamily q h) (centerFacetLabels S) = subsetRank q S + 1 := by
  let U := Submodule.span ℝ (q '' (↑S : Set (Fin n)))
  have hnot : projectionCenter r ∉ U.map (zeroHeightEmbedding r) := by
    rintro ⟨x, _, hx⟩
    have hz : (0 : ℝ) = 1 := by
      simpa only [zeroHeightEmbedding, LinearMap.coe_mk, AddHom.coe_mk,
        projectionCenter, Fin.cases_zero] using congrFun hx 0
    exact zero_ne_one hz
  change finrank ℝ (Submodule.span ℝ
    (projectedCenterFamily q h '' (↑(centerFacetLabels S) : Set _))) = finrank ℝ U + 1
  rw [projectedCenterFamily_span, Submodule.finrank_sup_span_singleton hnot]
  exact congrArg (· + 1)
    (Submodule.equivMapOfInjective (zeroHeightEmbedding r)
      (zeroHeightEmbedding_injective r) U).finrank_eq.symm

theorem reconstructed_center_facet_rank_upper {n r : ℕ}
    (q : Fin n → Fin r → ℝ) (h : Fin n → ℝ) (S : Finset (Fin n))
    (hS : subsetRank q S + 1 ≤ r) :
    subsetRank (normalizePointRows (projectedCenterFamily q h)) (centerFacetLabels S) ≤ r := by
  calc
    _ ≤ subsetRank (projectedCenterFamily q h) (centerFacetLabels S) :=
      subsetRank_normalizePointRows_le _ _
    _ = subsetRank q S + 1 := projectedCenterFamily_subsetRank q h S
    _ ≤ r := hS

theorem reconstructed_center_facet_rank_upper_of_le_pred {n r : ℕ}
    (q : Fin n → Fin r → ℝ) (h : Fin n → ℝ) (S : Finset (Fin n))
    (hr : 0 < r) (hS : subsetRank q S ≤ r - 1) :
    subsetRank (normalizePointRows (projectedCenterFamily q h)) (centerFacetLabels S) ≤ r :=
  reconstructed_center_facet_rank_upper q h S (by omega)

theorem projectedCenterFamily_spans_iff {n r : ℕ}
    (q : Fin n → Fin r → ℝ) (h : Fin n → ℝ) :
    Spans (projectedCenterFamily q h) ↔ Spans q := by
  have hrank := projectedCenterFamily_subsetRank q h Finset.univ
  rw [centerFacetLabels_univ] at hrank
  have hdim : (Matrix.of (projectedCenterFamily q h)).rank =
      (Matrix.of q).rank + 1 := by
    change finrank ℝ (Submodule.span ℝ
      (projectedCenterFamily q h '' (↑(Finset.univ : Finset (Fin (n+1))) : Set (Fin (n+1))))) =
      finrank ℝ (Submodule.span ℝ (q '' (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)))) + 1 at hrank
    rw [Finset.coe_univ, Finset.coe_univ, Set.image_univ, Set.image_univ] at hrank
    rw [Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row]
    exact hrank
  rw [spans_iff_matrix_rank, spans_iff_matrix_rank]
  change (Matrix.of (projectedCenterFamily q h)).rank = r + 1 ↔
    (Matrix.of q).rank = r
  rw [hdim]
  omega

theorem projectedCenterFamily_rational {n r : ℕ}
    {q : Fin n → Fin r → ℝ} {h : Fin n → ℝ}
    (hq : RationalCoordinates q) (hh : ∀ i, RatScalar (h i)) :
    RationalCoordinates (projectedCenterFamily q h) := by
  intro i a
  cases i using Fin.cases with
  | zero =>
    cases a using Fin.cases
    · exact ⟨1, by simp [projectedCenterFamily, projectionCenter]⟩
    · exact ⟨0, by simp [projectedCenterFamily, projectionCenter]⟩
  | succ i =>
    cases a using Fin.cases
    · exact hh i
    · exact hq i _

theorem continuous_projectedCenterFamily {n r : ℕ} :
    Continuous (fun z : (Fin n → Fin r → ℝ) × (Fin n → ℝ) =>
      projectedCenterFamily z.1 z.2) := by
  apply continuous_pi
  intro i
  cases i using Fin.cases with
  | zero => exact continuous_const
  | succ i =>
    apply continuous_pi
    intro a
    cases a using Fin.cases with
    | zero => exact (continuous_apply i).comp continuous_snd
    | succ a => exact (continuous_apply a).comp ((continuous_apply i).comp continuous_fst)

theorem projectedCenterFamily_first_ne_zero {n r : ℕ}
    (q : Fin n → Fin r → ℝ) (h : Fin n → ℝ) (hh : ∀ i, h i ≠ 0) :
    ∀ i, projectedCenterFamily q h i 0 ≠ 0 := by
  intro i
  cases i using Fin.cases
  · exact one_ne_zero
  · exact hh _

theorem spans_normalizePointRows {n r : ℕ}
    (p : Fin n → Fin (r + 1) → ℝ) (hp : Spans p) (hfirst : ∀ i, p i 0 ≠ 0) :
    Spans (normalizePointRows p) := by
  have hrecover (i : Fin n) : p i 0 • normalizePointRows p i = p i := by
    ext a
    simp only [Pi.smul_apply, smul_eq_mul, normalizePointRows]
    field_simp [hfirst i] <;> ring
  apply top_unique
  rw [← hp]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  rw [← hrecover i]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem normalized_projectedCenterFamily_spans {n r : ℕ}
    (q : Fin n → Fin r → ℝ) (h : Fin n → ℝ)
    (hq : Spans q) (hh : ∀ i, h i ≠ 0) :
    Spans (normalizePointRows (projectedCenterFamily q h)) :=
  spans_normalizePointRows _ ((projectedCenterFamily_spans_iff q h).mpr hq)
    (projectedCenterFamily_first_ne_zero q h hh)

theorem continuousAt_normalized_projectedCenterFamily {n r : ℕ}
    (q : Fin n → Fin r → ℝ) (h : Fin n → ℝ) (hh : ∀ i, h i ≠ 0) :
    ContinuousAt (fun z : (Fin n → Fin r → ℝ) × (Fin n → ℝ) =>
      normalizePointRows (projectedCenterFamily z.1 z.2)) (q, h) :=
  (normalizePointRows_continuousAt _
    (projectedCenterFamily_first_ne_zero q h hh)).comp_of_eq
      (continuous_projectedCenterFamily.continuousAt (x := (q,h))) rfl

/-- Full dimension of the actual normalized reconstruction is an open
condition on the projected points and their nonzero reciprocal heights. -/
theorem eventually_spans_normalized_projectedCenterFamily {n r : ℕ}
    (q : Fin n → Fin r → ℝ) (h : Fin n → ℝ)
    (hq : Spans q) (hh : ∀ i, h i ≠ 0) :
    ∀ᶠ z in 𝓝 (q, h), Spans (normalizePointRows (projectedCenterFamily z.1 z.2)) :=
  (continuousAt_normalized_projectedCenterFamily q h hh).tendsto.eventually
    (eventually_spans (normalized_projectedCenterFamily_spans q h hq hh))

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart3

section BundlePart4
/- Source: Papers/ProjectionDensityAssembly.lean -/



@[expose] public section

/-!
# Rational reconstruction from a projected configuration

The center has label zero and all other labels are successors.  Rational
approximation of the projected points is combined with the continuous
height solve.  For facets through the center, projected rank bounds give
the required hyperplane.  For the other facets, the height matrix must span
the entire projected relation space.  Open lower bounds then turn these
upper bounds into exact facet ranks.  The existing local reconstruction
theorem supplies the complete labelled face order.

The hypotheses below are the explicit geometric obligations supplied by
the actual projection chart and the finite relation certificates.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Matrix Filter Topology
open scoped Classical BigOperators
open PlaneRationalization

/-- Noncenter labels of a subset of the reconstructed configuration. -/
def projectedLabels {n : ℕ} (T : Finset (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter fun i => i.succ ∈ T

@[simp] theorem mem_projectedLabels {n : ℕ}
    (T : Finset (Fin (n + 1))) (i : Fin n) :
    i ∈ projectedLabels T ↔ i.succ ∈ T := by
  simp only [projectedLabels, Finset.mem_filter, Finset.mem_univ, true_and]

theorem image_projectedLabels {n : ℕ} (T : Finset (Fin (n + 1))) :
    (projectedLabels T).image Fin.succ = T.erase 0 := by
  ext i
  cases i using Fin.cases with
  | zero => simp
  | succ i => simp

theorem centerFacetLabels_projectedLabels {n : ℕ}
    (T : Finset (Fin (n + 1))) (hT : 0 ∈ T) :
    centerFacetLabels (projectedLabels T) = T := by
  rw [centerFacetLabels, image_projectedLabels, Finset.insert_erase hT]

theorem image_projectedLabels_of_zero_not_mem {n : ℕ}
    (T : Finset (Fin (n + 1))) (hT : 0 ∉ T) :
    (projectedLabels T).image Fin.succ = T := by
  rw [image_projectedLabels, Finset.erase_eq_of_notMem hT]

/-- Deleting the unused center label merely reindexes the same vectors. -/
theorem subsetRank_projectedLabels_of_zero_not_mem {n r : ℕ}
    (p : Fin (n + 1) → Fin r → ℝ) (T : Finset (Fin (n + 1)))
    (hT : 0 ∉ T) :
    subsetRank p T = subsetRank (fun i : Fin n => p i.succ) (projectedLabels T) := by
  have himage : p '' (↑T : Set (Fin (n + 1))) =
      (fun i : Fin n => p i.succ) '' (↑(projectedLabels T) : Set (Fin n)) := by
    ext v
    constructor
    · rintro ⟨i, hi, rfl⟩
      cases i using Fin.cases with
      | zero => exact (hT hi).elim
      | succ i => exact ⟨i, (mem_projectedLabels T i).mpr hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i.succ, (mem_projectedLabels T i).mp hi, rfl⟩
  exact congrArg (fun U : Set (Fin r → ℝ) => finrank ℝ (Submodule.span ℝ U)) himage

theorem subsetRank_normalizedCenter_of_zero_not_mem {n r : ℕ}
    (q : Fin n → Fin r → ℝ) (h : Fin n → ℝ)
    (T : Finset (Fin (n + 1))) (hT : 0 ∉ T) :
    subsetRank (normalizePointRows (projectedCenterFamily q h)) T =
      subsetRank (normalizePointRows (appendHeights q h)) (projectedLabels T) :=
  subsetRank_projectedLabels_of_zero_not_mem _ T hT

/-- Nonzero row normalization preserves every selected span dimension. -/
theorem subsetRank_normalizePointRows_eq {n r : ℕ}
    (p : Fin n → Fin (r + 1) → ℝ) (S : Finset (Fin n))
    (hfirst : ∀ i, p i 0 ≠ 0) :
    subsetRank (normalizePointRows p) S = subsetRank p S := by
  apply Nat.le_antisymm (subsetRank_normalizePointRows_le p S)
  apply Submodule.finrank_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨i, hi, rfl⟩
  have hrecover : p i 0 • normalizePointRows p i = p i := by
    ext a
    simp only [Pi.smul_apply, smul_eq_mul, normalizePointRows]
    field_simp [hfirst i] <;> ring
  rw [← hrecover]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)

theorem subsetRank_normalizedCenter_of_zero_mem {n r : ℕ}
    (q : Fin n → Fin r → ℝ) (h : Fin n → ℝ)
    (T : Finset (Fin (n + 1))) (hT : 0 ∈ T) (hh : ∀ i, h i ≠ 0) :
    subsetRank (normalizePointRows (projectedCenterFamily q h)) T =
      subsetRank q (projectedLabels T) + 1 := by
  rw [subsetRank_normalizePointRows_eq _ _
    (projectedCenterFamily_first_ne_zero q h hh)]
  simpa only [centerFacetLabels_projectedLabels T hT] using
    projectedCenterFamily_subsetRank q h (projectedLabels T)

theorem normalizedCenter_first {n r : ℕ}
    (q : Fin n → Fin r → ℝ) (h : Fin n → ℝ) (hh : ∀ i, h i ≠ 0) :
    ∀ i, normalizePointRows (projectedCenterFamily q h) i 0 = 1 := by
  intro i
  exact div_self (projectedCenterFamily_first_ne_zero q h hh i)

/-- The height solve yields nearby rational configurations with exactly the
old facet ranks.  Rank lower bounds are imposed on the final normalized
coordinates, so no independent nondegeneracy assumption is hidden here. -/
theorem rational_projected_center_facet_rank_density {n r c : ℕ}
    (q : Fin n → Fin r → ℝ) (h : Fin n → ℝ)
    (Allowed : Set (Fin n → Fin r → ℝ))
    (C : (Fin n → Fin r → ℝ) → Matrix (Fin c) (Fin n) ℝ)
    (hCcont : ContinuousAt C q)
    (hCrat : ∀ q', RationalCoordinates q' → RationalCoordinates (C q'))
    (hCind : LinearIndependent ℝ (C q).row)
    (hCh : (C q).mulVec h = 0) (hpos : ∀ i, 0 < h i)
    (hq : q ∈ closure {q' | RationalCoordinates q' ∧ q' ∈ Allowed})
    (hcenter : ∀ q' ∈ Allowed,
      ∀ T ∈ facetMasks (normalizePointRows (projectedCenterFamily q h)), 0 ∈ T →
        subsetRank q' (projectedLabels T) + 1 ≤ r)
    (hrelations : ∀ q' ∈ Allowed,
      ∀ T ∈ facetMasks (normalizePointRows (projectedCenterFamily q h)), 0 ∉ T →
        globalRelationSpace q' (projectedLabels T) ≤
          Submodule.span ℝ (Set.range (C q'))) :
    normalizePointRows (projectedCenterFamily q h) ∈ closure
      {p : Fin (n + 1) → Fin (r + 1) → ℝ |
        RationalCoordinates p ∧ (∀ i, p i 0 = 1) ∧
        ∀ T ∈ facetMasks (normalizePointRows (projectedCenterFamily q h)),
          subsetRank p T = subsetRank (normalizePointRows (projectedCenterFamily q h)) T} := by
  let F := fun z : (Fin n → Fin r → ℝ) × (Fin n → ℝ) =>
    normalizePointRows (projectedCenterFamily z.1 z.2)
  have hFcont : ContinuousAt F (q, h) :=
    continuousAt_normalized_projectedCenterFamily q h (fun i => ne_of_gt (hpos i))
  have hlower : ∀ᶠ z in 𝓝 (q, h), ∀ T : Finset (Fin (n + 1)),
      subsetRank (F (q, h)) T ≤ subsetRank (F z) T := by
    apply eventually_all.mpr
    intro T
    exact hFcont.tendsto.eventually (eventually_subsetRank_ge (F (q, h)) T)
  have hlift := rational_positive_height_lift q h Allowed C
    hCcont hCrat hCind hCh hpos hq
  have hcl := mem_closure_inter_of_eventually hlift hlower
  have himage := mem_closure_image hFcont hcl
  apply closure_mono (s := F '' _) ?_ himage
  rintro _ ⟨⟨q', h'⟩, ⟨⟨hqr, hqa, hhr, hker, hpositive⟩, hlow⟩, rfl⟩
  refine ⟨normalizePointRows_rational (projectedCenterFamily_rational hqr hhr),
    normalizedCenter_first q' h' (fun i => ne_of_gt (hpositive i)), ?_⟩
  intro T hT
  change subsetRank (F (q', h')) T = subsetRank (F (q, h)) T
  have hTrank := ((mem_facetMasks (F (q, h)) T).mp hT).2.2
  have hupper : subsetRank (F (q', h')) T ≤ r := by
    by_cases hzero : 0 ∈ T
    · change subsetRank (normalizePointRows (projectedCenterFamily q' h')) T ≤ r
      rw [← centerFacetLabels_projectedLabels T hzero]
      exact reconstructed_center_facet_rank_upper q' h' (projectedLabels T)
        (hcenter q' hqa T hT hzero)
    · change subsetRank (normalizePointRows (projectedCenterFamily q' h')) T ≤ r
      rw [subsetRank_normalizedCenter_of_zero_not_mem q' h' T hzero]
      exact reconstructed_facet_rank_upper q' h' (C q') (projectedLabels T)
        (hrelations q' hqa T hT hzero) hker
  exact Nat.le_antisymm (by omega) (hlow T)

/-- Complete coordinate reconstruction.  The conclusion preserves the full
labelled polytope, not only its recorded hyperplane incidences. -/
theorem rational_polytope_density_from_projected_height_matrix {n r c : ℕ}
    (q : Fin n → Fin r → ℝ) (h : Fin n → ℝ) (hspan : Spans q)
    (Allowed : Set (Fin n → Fin r → ℝ))
    (C : (Fin n → Fin r → ℝ) → Matrix (Fin c) (Fin n) ℝ)
    (hCcont : ContinuousAt C q)
    (hCrat : ∀ q', RationalCoordinates q' → RationalCoordinates (C q'))
    (hCind : LinearIndependent ℝ (C q).row)
    (hCh : (C q).mulVec h = 0) (hpos : ∀ i, 0 < h i)
    (hq : q ∈ closure {q' | RationalCoordinates q' ∧ q' ∈ Allowed})
    (hcenter : ∀ q' ∈ Allowed,
      ∀ T ∈ facetMasks (normalizePointRows (projectedCenterFamily q h)), 0 ∈ T →
        subsetRank q' (projectedLabels T) + 1 ≤ r)
    (hrelations : ∀ q' ∈ Allowed,
      ∀ T ∈ facetMasks (normalizePointRows (projectedCenterFamily q h)), 0 ∉ T →
        globalRelationSpace q' (projectedLabels T) ≤
          Submodule.span ℝ (Set.range (C q'))) :
    normalizePointRows (projectedCenterFamily q h) ∈ closure
      {p : Fin (n + 1) → Fin (r + 1) → ℝ |
        RationalCoordinates p ∧ (∀ i, p i 0 = 1) ∧ Spans p ∧
        LabelledPolytopeEquivalent (normalizePointRows (projectedCenterFamily q h)) p} := by
  apply rational_polytope_density_from_facet_rank_density _
    (normalized_projectedCenterFamily_spans q h hspan (fun i => ne_of_gt (hpos i)))
    (normalizedCenter_first q h (fun i => ne_of_gt (hpos i)))
  exact rational_projected_center_facet_rank_density q h Allowed C
    hCcont hCrat hCind hCh hpos hq hcenter hrelations

/-- The usual rank bound for a facet through the center is r−1. -/
theorem rational_polytope_density_from_projected_height_matrix_of_le_pred {n r c : ℕ}
    (q : Fin n → Fin r → ℝ) (h : Fin n → ℝ) (hr : 0 < r) (hspan : Spans q)
    (Allowed : Set (Fin n → Fin r → ℝ))
    (C : (Fin n → Fin r → ℝ) → Matrix (Fin c) (Fin n) ℝ)
    (hCcont : ContinuousAt C q)
    (hCrat : ∀ q', RationalCoordinates q' → RationalCoordinates (C q'))
    (hCind : LinearIndependent ℝ (C q).row)
    (hCh : (C q).mulVec h = 0) (hpos : ∀ i, 0 < h i)
    (hq : q ∈ closure {q' | RationalCoordinates q' ∧ q' ∈ Allowed})
    (hcenter : ∀ q' ∈ Allowed,
      ∀ T ∈ facetMasks (normalizePointRows (projectedCenterFamily q h)), 0 ∈ T →
        subsetRank q' (projectedLabels T) ≤ r - 1)
    (hrelations : ∀ q' ∈ Allowed,
      ∀ T ∈ facetMasks (normalizePointRows (projectedCenterFamily q h)), 0 ∉ T →
        globalRelationSpace q' (projectedLabels T) ≤
          Submodule.span ℝ (Set.range (C q'))) :
    normalizePointRows (projectedCenterFamily q h) ∈ closure
      {p : Fin (n + 1) → Fin (r + 1) → ℝ |
        RationalCoordinates p ∧ (∀ i, p i 0 = 1) ∧ Spans p ∧
        LabelledPolytopeEquivalent (normalizePointRows (projectedCenterFamily q h)) p} := by
  apply rational_polytope_density_from_projected_height_matrix q h hspan Allowed C
    hCcont hCrat hCind hCh hpos hq _ hrelations
  intro q' hqa T hT hzero
  have hbound := hcenter q' hqa T hT hzero
  omega

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart4

section BundlePart5
/- Source: Papers/AffineEmbeddingDensity.lean -/





@[expose] public section

/-!
# Rational density under arbitrary real affine embeddings

Both the linear frame and the translation are approximated rationally.
Linear independence is open, so every approximating frame remains an affine
embedding.  The face-order argument allows an affine left inverse; this is
essential when the translation is not annihilated by a linear left inverse.
-/

noncomputable section
open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.ChirotopeDensity

open PlaneRationalization

theorem affine_image_isExposed_of_affine_leftInverse {r s : ℕ}
    (f : (Fin r → ℝ) →ᵃ[ℝ] (Fin s → ℝ))
    (g : (Fin s → ℝ) →ᵃ[ℝ] (Fin r → ℝ))
    (hgf : ∀ x, g (f x) = x)
    {A B : Set (Fin r → ℝ)} (hB : IsExposed ℝ A B) :
    IsExposed ℝ (f '' A) (f '' B) := by
  intro hne
  obtain ⟨_, x, hx, rfl⟩ := hne
  obtain ⟨l, hl⟩ := hB ⟨x, hx⟩
  let k : (Fin s → ℝ) →L[ℝ] ℝ := l.comp g.linear.toContinuousLinearMap
  have hk (y : Fin r → ℝ) : k (f y) = l y - l (g 0) := by
    have h := congrArg l (hgf y)
    rw [affine_value_decomposition, map_add] at h
    change k (f y) + l (g 0) = l y at h
    linarith
  refine ⟨k, ?_⟩
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [hl] at hy
    refine ⟨⟨y, hy.1, rfl⟩, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    rw [hk, hk]
    exact sub_le_sub_right (hy.2 v hv) _
  · rintro ⟨⟨y, hy, rfl⟩, hm⟩
    refine ⟨y, ?_, rfl⟩
    rw [hl]
    refine ⟨hy, ?_⟩
    intro v hv
    have hh := hm (f v) ⟨v, hv, rfl⟩
    rw [hk, hk] at hh
    exact (sub_le_sub_iff_right _).mp hh

def affineEmbeddingFaceOrderIso {n r s : ℕ}
    (p : Fin n → Fin r → ℝ)
    (f : (Fin r → ℝ) →ᵃ[ℝ] (Fin s → ℝ))
    (g : (Fin s → ℝ) →ᵃ[ℝ] (Fin r → ℝ))
    (hgf : ∀ x, g (f x) = x) :
    ActualCoordinateFace p ≃o ActualCoordinateFace (fun i => f (p i)) where
  toFun F := ⟨f '' F.1, by
    rw [← affine_image_coordinateHull p f]
    exact affine_image_isExposed_of_affine_leftInverse f g hgf F.2.1,
    F.2.2.image f⟩
  invFun F := ⟨coordinateHull p ∩ f ⁻¹' F.1, by
    apply affine_preimage_isExposed f
    rw [affine_image_coordinateHull p f]
    exact F.2.1, by
    obtain ⟨y, hy⟩ := F.2.2
    have hybody := F.2.1.subset hy
    rw [← affine_image_coordinateHull p f] at hybody
    obtain ⟨x, hx, rfl⟩ := hybody
    exact ⟨x, hx, hy⟩⟩
  left_inv F := by
    apply Subtype.ext
    ext x
    constructor
    · rintro ⟨_, y, hy, heq⟩
      have hxy : y = x := by
        have hh := congrArg g heq
        simpa only [hgf] using hh
      simpa only [hxy] using hy
    · intro hx
      exact ⟨F.2.1.subset hx, x, hx, rfl⟩
  right_inv F := by
    apply Subtype.ext
    ext y
    constructor
    · rintro ⟨x, ⟨_, hx⟩, rfl⟩
      exact hx
    · intro hy
      have hybody := F.2.1.subset hy
      rw [← affine_image_coordinateHull p f] at hybody
      obtain ⟨x, hx, rfl⟩ := hybody
      exact ⟨x, ⟨hx, hy⟩, rfl⟩
  map_rel_iff' := by
    intro F G
    change f '' F.1 ⊆ f '' G.1 ↔ F.1 ⊆ G.1
    constructor
    · intro h x hx
      obtain ⟨y, hy, heq⟩ := h ⟨x, hx, rfl⟩
      have hxy : y = x := by
        have hh := congrArg g heq
        simpa only [hgf] using hh
      simpa only [hxy] using hy
    · exact Set.image_mono

theorem affineEmbeddingFaceOrderIso_labels {n r s : ℕ}
    (p : Fin n → Fin r → ℝ)
    (f : (Fin r → ℝ) →ᵃ[ℝ] (Fin s → ℝ))
    (g : (Fin s → ℝ) →ᵃ[ℝ] (Fin r → ℝ))
    (hgf : ∀ x, g (f x) = x) (F : ActualCoordinateFace p) :
    faceLabels (fun i => f (p i)) ((affineEmbeddingFaceOrderIso p f g hgf) F).1 =
      faceLabels p F.1 := by
  classical
  ext i
  simp only [faceLabels, Finset.mem_filter, Finset.mem_univ, true_and]
  change f (p i) ∈ f '' F.1 ↔ p i ∈ F.1
  constructor
  · rintro ⟨x, hx, heq⟩
    have hxi : x = p i := by
      have hh := congrArg g heq
      simpa only [hgf] using hh
    simpa only [hxi] using hx
  · intro hi
    exact ⟨p i, hi, rfl⟩

def affineFrame {r d : ℕ} (E : Fin r → Fin d → ℝ) (b : Fin d → ℝ) :
    (Fin r → ℝ) →ᵃ[ℝ] (Fin d → ℝ) where
  toFun x := frameMap E x + b
  linear := frameMap E
  map_vadd' x v := by simp [map_add, add_assoc]

def affineReconstruct {n r d : ℕ} (E : Fin r → Fin d → ℝ) (b : Fin d → ℝ)
    (u : Fin n → Fin r → ℝ) : Fin n → Fin d → ℝ := fun i => affineFrame E b (u i)

theorem affineFrame_leftInverse {r d : ℕ}
    (E : Fin r → Fin d → ℝ) (b : Fin d → ℝ)
    (hE : LinearIndependent ℝ E) :
    ∃ g : (Fin d → ℝ) →ᵃ[ℝ] (Fin r → ℝ),
      ∀ x, g (affineFrame E b x) = x := by
  obtain ⟨h, hh⟩ := (frameMap E).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (frameMap_injective hE))
  let g : (Fin d → ℝ) →ᵃ[ℝ] (Fin r → ℝ) :=
    { toFun := fun y => h y - h b
      linear := h
      map_vadd' := by intro x v; simp [map_add, add_sub_assoc] }
  refine ⟨g, ?_⟩
  intro x
  have hx := LinearMap.ext_iff.mp hh x
  change h (frameMap E x + b) - h b = x
  rw [map_add, add_sub_cancel_right]
  exact hx

theorem affineReconstruct_equivalent {n r d : ℕ}
    (u : Fin n → Fin r → ℝ) (E : Fin r → Fin d → ℝ) (b : Fin d → ℝ)
    (hE : LinearIndependent ℝ E) :
    LabelledPolytopeEquivalent u (affineReconstruct E b u) := by
  obtain ⟨g, hg⟩ := affineFrame_leftInverse E b hE
  exact ⟨affineEmbeddingFaceOrderIso u (affineFrame E b) g hg,
    affineEmbeddingFaceOrderIso_labels u (affineFrame E b) g hg⟩

theorem continuous_affineReconstruct {n r d : ℕ} :
    Continuous (fun z : ((Fin r → Fin d → ℝ) × (Fin d → ℝ)) ×
        (Fin n → Fin r → ℝ) => affineReconstruct z.1.1 z.1.2 z.2) := by
  apply continuous_pi
  intro i
  have hc : Continuous (fun z : ((Fin r → Fin d → ℝ) × (Fin d → ℝ)) ×
      (Fin n → Fin r → ℝ) => reconstruct z.1.1 z.2 i) :=
    (continuous_apply i).comp (continuous_reconstruct.comp
      ((continuous_fst.comp continuous_fst).prodMk continuous_snd))
  exact hc.add (continuous_snd.comp continuous_fst)

theorem affineReconstruct_rational {n r d : ℕ}
    {u : Fin n → Fin r → ℝ} {E : Fin r → Fin d → ℝ} {b : Fin d → ℝ}
    (hu : RationalCoordinates u) (hE : RationalCoordinates E)
    (hb : ∀ j, RatScalar (b j)) : RationalCoordinates (affineReconstruct E b u) := by
  intro i j
  exact ((reconstruct_rational hE hu) i j).add (hb j)

/-- Full labelled face-order density transports through an arbitrary real
affine embedding, including an arbitrary real translation. -/
theorem affinely_embedded_coordinate_density {n r d : ℕ}
    (u : Fin n → Fin r → ℝ) (E : Fin r → Fin d → ℝ) (b : Fin d → ℝ)
    (hE : LinearIndependent ℝ E)
    (hu : u ∈ closure {v | RationalCoordinates v ∧ LabelledPolytopeEquivalent u v}) :
    affineReconstruct E b u ∈ closure
      {q | RationalCoordinates q ∧ LabelledPolytopeEquivalent (affineReconstruct E b u) q} := by
  have hEc : E ∈ closure {F : Fin r → Fin d → ℝ |
      RationalCoordinates F ∧ LinearIndependent ℝ F} := by
    have h := mem_closure_inter_of_eventually (rationalCoordinates_dense r d E) hE.eventually
    exact h
  have hbc : b ∈ closure {b' : Fin d → ℝ | ∀ j, RatScalar (b' j)} :=
    scalarCoordinates_dense d b
  have hp : ((E, b), u) ∈ closure
      (({F : Fin r → Fin d → ℝ | RationalCoordinates F ∧ LinearIndependent ℝ F} ×ˢ
        {b' : Fin d → ℝ | ∀ j, RatScalar (b' j)}) ×ˢ
        {v : Fin n → Fin r → ℝ | RationalCoordinates v ∧ LabelledPolytopeEquivalent u v}) := by
    rw [closure_prod_eq, closure_prod_eq]
    exact ⟨⟨hEc, hbc⟩, hu⟩
  let G := fun z : ((Fin r → Fin d → ℝ) × (Fin d → ℝ)) ×
      (Fin n → Fin r → ℝ) => affineReconstruct z.1.1 z.1.2 z.2
  have hcl := mem_closure_image
    (continuous_affineReconstruct (n := n) (r := r) (d := d)).continuousAt hp
  apply closure_mono (s := G '' _) ?_ hcl
  rintro _ ⟨⟨⟨F, b'⟩, v⟩, ⟨⟨hF, hb'⟩, hv⟩, rfl⟩
  refine ⟨affineReconstruct_rational hv.1 hF.1 hb', ?_⟩
  exact (affineReconstruct_equivalent u E b hE).symm.trans
    (hv.2.trans (affineReconstruct_equivalent v F b' hF.2))

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart5

section BundlePart6
/- Source: Papers/RationalityTenFacetDimensionCorrespondence.lean -/







@[expose] public section

noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.ChirotopeDensity

def affineCoordinateDimension {d : ℕ} (S : Set (Fin d → ℝ)) : ℕ :=
  finrank ℝ (vectorSpan ℝ S)

/-- The two homogeneous coordinate conventions differ by this explicit
linear equivalence: the ordinary coordinates precede the homogenising
coordinate in the product convention, and follow it here. -/
def homogeneousProdEquiv (d : ℕ) :
    ((Fin d → ℝ) × ℝ) ≃ₗ[ℝ] (Fin (d+1) → ℝ) where
  toFun x := Fin.cons x.2 x.1
  invFun x := (fun j => x j.succ,x 0)
  left_inv x := by
    rcases x with ⟨x,t⟩
    rfl
  right_inv x := by
    ext j
    refine Fin.cases ?_ ?_ j
    · rfl
    · intro k
      rfl
  map_add' x y := by
    ext j
    refine Fin.cases ?_ ?_ j
    · rfl
    · intro k
      rfl
  map_smul' a x := by
    ext j
    refine Fin.cases ?_ ?_ j
    · rfl
    · intro k
      rfl

theorem homogeneous_subset_span_eq_map {n d : ℕ}
    (p : Fin n → Fin d → ℝ) (S : Finset (Fin n)) :
    Submodule.span ℝ (homogeneousPoints p '' (↑S : Set (Fin n))) =
      (Papers.HomogeneousSpanDimension.liftSpan
        (p '' (↑S : Set (Fin n)))).map (homogeneousProdEquiv d).toLinearMap := by
  unfold Papers.HomogeneousSpanDimension.liftSpan
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨i,hi,rfl⟩
    exact ⟨Papers.HomogeneousSpanDimension.liftPoint (p i),
      ⟨p i,⟨i,hi,rfl⟩,rfl⟩,rfl⟩
  · rintro ⟨x,⟨y,⟨i,hi,rfl⟩,rfl⟩,rfl⟩
    exact ⟨i,hi,rfl⟩

theorem subsetRank_homogeneous_eq_affineDimension {n d : ℕ}
    (p : Fin n → Fin d → ℝ) (S : Finset (Fin n)) (hS : S.Nonempty) :
    subsetRank (homogeneousPoints p) S =
      affineCoordinateDimension (labelledHull p S)+1 := by
  have hne : (labelledHull p S).Nonempty := by
    obtain ⟨i,hi⟩ := hS
    exact ⟨p i,subset_convexHull ℝ _ ⟨i,hi,rfl⟩⟩
  calc
    subsetRank (homogeneousPoints p) S =
        finrank ℝ ((Papers.HomogeneousSpanDimension.liftSpan
          (p '' (↑S : Set (Fin n)))).map (homogeneousProdEquiv d).toLinearMap) := by
      rw [subsetRank,homogeneous_subset_span_eq_map]
    _ = finrank ℝ (Papers.HomogeneousSpanDimension.liftSpan
          (p '' (↑S : Set (Fin n)))) :=
      (homogeneousProdEquiv d).finrank_map_eq _
    _ = finrank ℝ (Papers.HomogeneousSpanDimension.liftSpan
          (labelledHull p S)) := by
      rw [labelledHull,Papers.FaceVertexCardinality.liftSpan_convexHull]
    _ = affineCoordinateDimension (labelledHull p S)+1 :=
      Papers.HomogeneousSpanDimension.finrank_liftSpan hne

theorem labelledHull_univ {n d : ℕ} (p : Fin n → Fin d → ℝ) :
    labelledHull p Finset.univ=coordinateHull p := by
  simp only [labelledHull,coordinateHull,Finset.coe_univ,Set.image_univ]

theorem affineCoordinateDimension_hull_of_spans {n d : ℕ}
    (p : Fin n → Fin d → ℝ) (hp : Spans (homogeneousPoints p)) :
    affineCoordinateDimension (coordinateHull p)=d := by
  have hr := (spans_iff_matrix_rank (homogeneousPoints p)).mp hp
  have hn : d + 1 ≤ n := by
    rw [← hr]
    exact Matrix.rank_le_height (Matrix.of (homogeneousPoints p))
  have hnpos : 0<n := by omega
  have hU : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0,hnpos⟩,Finset.mem_univ _⟩
  have h := subsetRank_homogeneous_eq_affineDimension p Finset.univ hU
  rw [subsetRank_univ (homogeneousPoints p) hp,labelledHull_univ] at h
  omega

/-- The finite mask criterion is exactly the usual codimension-one
condition for a nonempty exposed face of the ordinary convex hull. -/
theorem facetMask_faceLabels_iff_dimension {n d : ℕ}
    (p : Fin n → Fin d → ℝ)
    (F : ActualCoordinateFace p) :
    FacetMask (homogeneousPoints p) (faceLabels p F.1) ↔
      affineCoordinateDimension F.1+1=d := by
  have hne := faceLabels_nonempty p F.2.1 F.2.2
  have hsupp :
      ∃ a, StrictSupport (homogeneousPoints p) (faceLabels p F.1) a := by
    have h := exposed_face_strictSupport (homogeneousPoints p)
      (homogeneousPoints_first p)
      (ordinaryHomogeneousFaceOrderIso p F).2.1
      (ordinaryHomogeneousFaceOrderIso p F).2.2
    rwa [ordinaryHomogeneousFaceOrderIso_labels] at h
  have hr := subsetRank_homogeneous_eq_affineDimension p (faceLabels p F.1) hne
  rw [← exposed_face_eq_labelledHull p F.2.1] at hr
  constructor
  · intro hF
    have hh := hF.2.2
    omega
  · intro hdim
    exact ⟨hne,hsupp,by omega⟩

theorem facetMask_faceLabels_iff_codimension_one {n d : ℕ}
    (p : Fin n → Fin d → ℝ) (hp : Spans (homogeneousPoints p))
    (F : ActualCoordinateFace p) :
    FacetMask (homogeneousPoints p) (faceLabels p F.1) ↔
      affineCoordinateDimension F.1+1=
        affineCoordinateDimension (coordinateHull p) := by
  rw [affineCoordinateDimension_hull_of_spans p hp]
  exact facetMask_faceLabels_iff_dimension p F

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart6

section BundlePart7
/- Source: Papers/IntrinsicActualPolytopes.lean -/






@[expose] public section

/-!
# Intrinsic actual polytopes and transport back to the original ambient space

Every finite convex polytope is realized in its exact intrinsic dimension.
Rational approximations there are carried back through nearby rational
injective affine maps.  No rationality assumption on the original affine
span, its frame, or its translation is made.

The coordinate-hull helper proofs below are the dimension-general form of
ActualCoordinateRealizations.  The complete new module awaits compilation.
-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Matrix Module Set Filter Topology
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes

private theorem intrinsic_exposed_image_equiv
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (e : V ≃L[ℝ] W) {A B : Set V} (h : IsExposed ℝ A B) :
    IsExposed ℝ (e '' A) (e '' B) := by
  intro hne
  obtain ⟨_, x, hx, rfl⟩ := hne
  obtain ⟨l, hl⟩ := h ⟨x, hx⟩
  refine ⟨l.comp e.symm.toContinuousLinearMap, ?_⟩
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [hl] at hz
    refine ⟨⟨z, hz.1, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      e.symm_apply_apply] using hz.2 w hw
  · rintro ⟨⟨z, hz, rfl⟩, hmax⟩
    refine ⟨z, ?_, rfl⟩
    rw [hl]
    refine ⟨hz, ?_⟩
    intro w hw
    have hh := hmax (e w) ⟨w, hw, rfl⟩
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      e.symm_apply_apply] using hh

private theorem intrinsic_actual_vertex_coordinate_labels {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (i : Fin n) :
    faceLabels (ordinaryVertexCoordinates P e)
      (coordinateFaceOrderIso P _ (coordinateHull_actual_polytope P e)
        (vertexFace P (e i))).val = {i} := by
  ext j
  simp only [faceLabels, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  change euclideanCoordinateEquiv d (e j).val ∈
    euclideanCoordinateEquiv d '' {(e i).val} ↔ j = i
  rw [Set.image_singleton, Set.mem_singleton_iff]
  constructor
  · intro h
    exact e.injective (Subtype.ext ((euclideanCoordinateEquiv d).injective h))
  · rintro rfl
    rfl

private theorem intrinsic_exposed_face_singleton_of_labels {n d : ℕ}
    (q : Fin n → Fin d → ℝ) (F : ActualCoordinateFace q) (i : Fin n)
    (h : faceLabels q F.val = {i}) : F.val = {q i} := by
  rw [exposed_face_eq_labelledHull q F.property.1, h]
  simp only [labelledHull, Finset.coe_singleton, Set.image_singleton,
    convexHull_singleton]

private theorem intrinsic_coordinate_image_hull {n d : ℕ} (q : Fin n → Fin d → ℝ) :
    (euclideanCoordinateEquiv d).symm '' coordinateHull q =
      convexHull ℝ
        ((Finset.univ.image (fun i => (euclideanCoordinateEquiv d).symm (q i)) :
          Finset (E d)) : Set (E d)) := by
  change (euclideanCoordinateEquiv d).symm.toLinearEquiv.toLinearMap ''
    convexHull ℝ (Set.range q) = _
  rw [(euclideanCoordinateEquiv d).symm.toLinearEquiv.toLinearMap.image_convexHull]
  apply congrArg (convexHull ℝ)
  ext x
  simp only [Set.mem_image, Set.mem_range, Finset.mem_coe, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨q i, ⟨i, rfl⟩, rfl⟩

theorem actual_polytope_of_coordinates_across_dimensions {d r n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices)
    (q : Fin n → Fin r → ℝ)
    (h : LabelledPolytopeEquivalent (ordinaryVertexCoordinates P e) q) :
    ∃ Q : ConvexPolytope r, ∃ φ : FaceType P ≃o FaceType Q,
      Q.vertices = Finset.univ.image (fun i => (euclideanCoordinateEquiv r).symm (q i)) ∧
      ∀ i, (imageVertex φ (e i)).val = (euclideanCoordinateEquiv r).symm (q i) := by
  obtain ⟨ψ, hψ⟩ := h
  let σ := coordinateFaceOrderIso P _ (coordinateHull_actual_polytope P e)
  have hsingle (i : Fin n) : (ψ (σ (vertexFace P (e i)))).val = {q i} := by
    apply intrinsic_exposed_face_singleton_of_labels
    rw [hψ]
    exact intrinsic_actual_vertex_coordinate_labels P e i
  let S := Finset.univ.image (fun i => (euclideanCoordinateEquiv r).symm (q i))
  have hSne : S.Nonempty := by
    obtain ⟨v, hv⟩ := P.vertices_nonempty
    exact ⟨_, Finset.mem_image.mpr ⟨e.symm ⟨v, hv⟩, Finset.mem_univ _, rfl⟩⟩
  have hQext : (S : Set (E r)) = (convexHull ℝ (S : Set (E r))).extremePoints ℝ := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      have hex : IsExposed ℝ (coordinateHull q) {q i} :=
        hsingle i ▸ (ψ (σ (vertexFace P (e i)))).property.1
      have hi := intrinsic_exposed_image_equiv (euclideanCoordinateEquiv r).symm hex
      rw [intrinsic_coordinate_image_hull, Set.image_singleton] at hi
      exact hi.isExtreme.mem_extremePoints
    · exact extremePoints_convexHull_subset
  let Q : ConvexPolytope r := ⟨S, hSne, hQext⟩
  have hbody : euclideanCoordinateEquiv r '' Q.toSet = coordinateHull q := by
    change euclideanCoordinateEquiv r '' convexHull ℝ (S : Set (E r)) = _
    rw [← intrinsic_coordinate_image_hull, Set.image_image]
    simp only [Function.comp_def, ContinuousLinearEquiv.apply_symm_apply, Set.image_id']
  let τ := coordinateFaceOrderIso Q q hbody
  let φ := σ.trans (ψ.trans τ.symm)
  refine ⟨Q, φ, rfl, ?_⟩
  intro i
  have hv := congrArg Subtype.val (imageVertex_face φ (e i))
  change {(imageVertex φ (e i)).val} =
    (euclideanCoordinateEquiv r).symm '' (ψ (σ (vertexFace P (e i)))).val at hv
  rw [hsingle i, Set.image_singleton] at hv
  exact Set.singleton_injective hv

theorem coordinateFaceOrderIso_labels_membership {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (F : FaceType P) (i : Fin n) :
    i ∈ faceLabels (ordinaryVertexCoordinates P e)
      (coordinateFaceOrderIso P _ (coordinateHull_actual_polytope P e) F).val ↔
      (e i).val ∈ F.val := by
  simp only [faceLabels, Finset.mem_filter, Finset.mem_univ, true_and]
  change euclideanCoordinateEquiv d (e i).val ∈ euclideanCoordinateEquiv d '' F.val ↔ _
  constructor
  · rintro ⟨x, hx, heq⟩
    exact (euclideanCoordinateEquiv d).injective heq ▸ hx
  · intro hi
    exact ⟨(e i).val, hi, rfl⟩

theorem labelled_coordinates_of_faceOrder {d r n : ℕ}
    (P : ConvexPolytope d) (Q : ConvexPolytope r) (e : Fin n ≃ P.vertices)
    (φ : FaceType P ≃o FaceType Q) :
    LabelledPolytopeEquivalent (ordinaryVertexCoordinates P e)
      (ordinaryVertexCoordinates Q (e.trans (vertexEquivOfFaceOrder φ))) := by
  let eQ := e.trans (vertexEquivOfFaceOrder φ)
  let σ := coordinateFaceOrderIso P _ (coordinateHull_actual_polytope P e)
  let τ := coordinateFaceOrderIso Q _ (coordinateHull_actual_polytope Q eQ)
  refine ⟨σ.symm.trans (φ.trans τ), ?_⟩
  intro F
  ext i
  change i ∈ faceLabels (ordinaryVertexCoordinates Q eQ) (τ (φ (σ.symm F))).val ↔
    i ∈ faceLabels (ordinaryVertexCoordinates P e) F.val
  rw [coordinateFaceOrderIso_labels_membership]
  change (imageVertex φ (e i)).val ∈ (φ (σ.symm F)).val ↔ _
  rw [imageVertex_mem_iff]
  have h := coordinateFaceOrderIso_labels_membership P e (σ.symm F) i
  simpa only [σ, OrderIso.apply_symm_apply] using h.symm

/-- The actual vertexwise approximation predicate gives coordinate-space
density with the same induced vertex labels. -/
theorem rationallyApproximable_coordinate_density {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices)
    (hP : Papers.Polytopes.RationallyApproximable P) :
    ordinaryVertexCoordinates P e ∈ closure
      {q | RationalCoordinates q ∧ LabelledPolytopeEquivalent (ordinaryVertexCoordinates P e) q} := by
  rw [mem_closure_iff_nhds]
  intro U hU
  let G : (VertexType P → E d) × (Fin 0 → ℝ) → Fin n → Fin d → ℝ :=
    fun z i => euclideanCoordinateEquiv d (z.1 (e i))
  have hG : Continuous G := continuous_pi fun i =>
    (euclideanCoordinateEquiv d).continuous.comp ((continuous_apply (e i)).comp continuous_fst)
  have hpre : G ⁻¹' U ∈ 𝓝 (Subtype.val, (0 : Fin 0 → ℝ)) :=
    hG.continuousAt.preimage_mem_nhds hU
  obtain ⟨Q, φ, _, hQr, hnear⟩ :=
    hP.exists_parameters_in_neighborhood (0 : Fin 0 → ℝ) (G ⁻¹' U) hpre
  let eQ := e.trans (vertexEquivOfFaceOrder φ)
  let q := ordinaryVertexCoordinates Q eQ
  have hqU : q ∈ U := hnear
  refine ⟨q, hqU, ?_, labelled_coordinates_of_faceOrder P Q e φ⟩
  intro i j
  exact hQr (eQ i).val (eQ i).property j

theorem ordinaryCoordinate_dimension {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) :
    affineCoordinateDimension (coordinateHull (ordinaryVertexCoordinates P e)) = P.dim := by
  obtain ⟨v, hv⟩ := P.vertices_nonempty
  let i : Fin n := e.symm ⟨v, hv⟩
  have hactual := actualFaceLabels_rank P e ⟨P.toSet, toSet_isFace P⟩
  rw [actualFaceLabels_top] at hactual
  change subsetRank (vertexCoordinates P e) Finset.univ = P.dim + 1 at hactual
  have hcoord := subsetRank_homogeneous_eq_affineDimension (ordinaryVertexCoordinates P e)
    Finset.univ ⟨i, Finset.mem_univ i⟩
  rw [ordinaryVertexCoordinates_homogeneous, labelledHull_univ] at hcoord
  omega

theorem coordinateHull_direction_of_spans_zero {n r : ℕ}
    (u : Fin n → Fin r → ℝ) (hu : Spans u) (i : Fin n) (hi : u i = 0) :
    vectorSpan ℝ (coordinateHull u) = ⊤ := by
  calc
    vectorSpan ℝ (coordinateHull u) = (affineSpan ℝ (coordinateHull u)).direction :=
      (direction_affineSpan ℝ _).symm
    _ = (affineSpan ℝ (Set.range u)).direction := by
      rw [coordinateHull, affineSpan_convexHull]
    _ = vectorSpan ℝ (Set.range u) := direction_affineSpan ℝ _
    _ = Submodule.span ℝ (Set.range u) := by
      rw [vectorSpan_range_eq_span_range_vsub_right ℝ u i]
      simp only [hi, vsub_eq_sub, sub_zero]
    _ = ⊤ := hu

/-- Every actual polytope has a full realization in its exact intrinsic
dimension, with the same number of actual extreme vertices.  Rational
density in this intrinsic model implies rational density in the original
ambient space; the real affine embedding is approximated, not assumed
rational. -/
theorem exists_intrinsic_actual_model {d : ℕ} (P : ConvexPolytope d) :
    ∃ r ≤ d, ∃ Q : ConvexPolytope r,
      Q.IsFullDim ∧ Q.vertices.card = P.vertices.card ∧ r = P.dim ∧
      (Papers.Polytopes.RationallyApproximable Q → Papers.Polytopes.RationallyApproximable P) := by
  let n := Fintype.card P.vertices
  let e : Fin n ≃ P.vertices := (Fintype.equivFin P.vertices).symm
  let p := ordinaryVertexCoordinates P e
  obtain ⟨v, hv⟩ := P.vertices_nonempty
  let i : Fin n := e.symm ⟨v, hv⟩
  let b := p i
  let shifted : Fin n → Fin d → ℝ := fun j => p j - b
  obtain ⟨r, hrd, u, E, hu, hE, hrec⟩ := exists_intrinsic_linear_configuration shifted
  have hui : u i = 0 := by
    have h := congrFun hrec i
    have hzero : frameMap E (u i) = frameMap E 0 := by
      simpa [reconstruct, shifted, b] using h
    exact frameMap_injective hE hzero
  have hreconstruct : affineReconstruct E b u = p := by
    funext j
    have h := congrFun hrec j
    change frameMap E (u j) = p j - b at h
    change frameMap E (u j) + b = p j
    rw [h, sub_add_cancel]
  have hpu : LabelledPolytopeEquivalent p u := by
    simpa only [hreconstruct] using (affineReconstruct_equivalent u E b hE).symm
  obtain ⟨Q, φ, _, hφ⟩ := actual_polytope_of_coordinates_across_dimensions P e u hpu
  let eQ := e.trans (vertexEquivOfFaceOrder φ)
  have hcoordinates : ordinaryVertexCoordinates Q eQ = u := by
    funext j
    change euclideanCoordinateEquiv r (imageVertex φ (e j)).val = u j
    rw [hφ j]
    exact (euclideanCoordinateEquiv r).apply_symm_apply (u j)
  have hQfull : Q.IsFullDim := by
    change Q.dim = r
    rw [← ordinaryCoordinate_dimension Q eQ, hcoordinates]
    unfold affineCoordinateDimension
    rw [coordinateHull_direction_of_spans_zero u hu i hui]
    simp
  have hQdim : Q.dim = r := hQfull
  have hrP : r = P.dim := hQdim.symm.trans (faceOrderIso_polytope_dim φ)
  refine ⟨r, hrd, Q, hQfull, (faceOrderIso_vertex_card φ).symm, hrP, ?_⟩
  intro hQ
  have hdense := rationallyApproximable_coordinate_density Q eQ hQ
  rw [hcoordinates] at hdense
  have hembedded := affinely_embedded_coordinate_density u E b hE hdense
  rw [hreconstruct] at hembedded
  exact rationallyApproximable_of_coordinate_density P e hembedded

/-- A theorem for full intrinsic polytopes transfers to all embeddings,
preserving the original vertex bound and all approximation quantifiers. -/
theorem rationallyApproximable_of_intrinsic_bound {d k N : ℕ}
    (P : ConvexPolytope d) (hdim : P.dim ≤ k) (hcard : P.vertices.card ≤ N)
    (hall : ∀ r ≤ k, ∀ Q : ConvexPolytope r, Q.IsFullDim → Q.vertices.card ≤ N →
      Papers.Polytopes.RationallyApproximable Q) :
    Papers.Polytopes.RationallyApproximable P := by
  obtain ⟨r, _, Q, hQ, hcount, hr, htransport⟩ := exists_intrinsic_actual_model P
  apply htransport
  apply hall r (by simpa only [hr] using hdim) Q hQ
  simpa only [hcount] using hcard

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart7

section BundlePart8
/- Source: Papers/ActualProjectionReconstruction.lean -/






@[expose] public section

/-!
# Returning a projected rational reconstruction to an actual polytope

The affine normalization is an arbitrary real affine equivalence.  Its
inverse is approximated jointly with the reconstructed vertices, including
both its linear frame and translation.  Thus the conclusion is rational
approximation of the original actual polytope, with every original vertex
label controlled.

The center label is zero, and the other labels are successors.  The actual
normalized polytope is constructed from its exposed vertex faces.  This
supplies full dimension and the correspondence between every normalized
facet mask and an actual original facet; no facet coverage is assumed.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Matrix Filter Topology
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeIncidenceConfiguration

theorem affineEquiv_labelled_equivalent {n r d : ℕ}
    (u : Fin n → Fin r → ℝ) (f : (Fin r → ℝ) ≃ᵃ[ℝ] (Fin d → ℝ)) :
    LabelledPolytopeEquivalent u (fun i => f (u i)) :=
  ⟨affineEmbeddingFaceOrderIso u f.toAffineMap f.symm.toAffineMap f.symm_apply_apply,
    affineEmbeddingFaceOrderIso_labels u f.toAffineMap f.symm.toAffineMap
      f.symm_apply_apply⟩

/-- Rational density transports through an arbitrary real affine
equivalence by approximating the equivalence as well as the points. -/
theorem affineEquiv_coordinate_density {n r d : ℕ}
    (u : Fin n → Fin r → ℝ) (f : (Fin r → ℝ) ≃ᵃ[ℝ] (Fin d → ℝ))
    (hu : u ∈ closure {v | RationalCoordinates v ∧ LabelledPolytopeEquivalent u v}) :
    (fun i => f (u i)) ∈ closure
      {v | RationalCoordinates v ∧ LabelledPolytopeEquivalent (fun i => f (u i)) v} := by
  let E : Fin r → Fin d → ℝ := fun j => f.linear (Pi.basisFun ℝ (Fin r) j)
  have hE : LinearIndependent ℝ E :=
    (Pi.basisFun ℝ (Fin r)).linearIndependent.map' f.linear.toLinearMap
      (LinearMap.ker_eq_bot.mpr f.linear.injective)
  have hlinear (x : Fin r → ℝ) : frameMap E x = f.linear x := by
    change (∑ j, x j • f.linear (Pi.basisFun ℝ (Fin r) j)) = f.linear x
    have hsum := congrArg f.linear ((Pi.basisFun ℝ (Fin r)).sum_repr x)
    simpa only [map_sum, map_smul, Pi.basisFun_repr] using hsum
  have hrec : affineReconstruct E (f 0) u = (fun i => f (u i)) := by
    funext i
    change frameMap E (u i) + f 0 = f (u i)
    rw [hlinear]
    exact (affine_value_decomposition f.toAffineMap (u i)).symm
  simpa only [hrec] using affinely_embedded_coordinate_density u E (f 0) hE hu

/-- Add the actual apex as label zero. -/
def projectionVertexLabels {P : ConvexPolytope 4} {a : VertexType P} {n : ℕ}
    (e : Fin n ≃ ProjectionPoint P a) : Fin (n + 1) ≃ VertexType P :=
  (finSuccEquiv n).trans ((Equiv.optionCongr e).trans (Equiv.optionSubtypeNe a))

@[simp] theorem projectionVertexLabels_zero
    {P : ConvexPolytope 4} {a : VertexType P} {n : ℕ}
    (e : Fin n ≃ ProjectionPoint P a) : projectionVertexLabels e 0 = a := by
  simp [projectionVertexLabels]

@[simp] theorem projectionVertexLabels_succ
    {P : ConvexPolytope 4} {a : VertexType P} {n : ℕ}
    (e : Fin n ≃ ProjectionPoint P a) (i : Fin n) :
    projectionVertexLabels e i.succ = (e i).val := by
  simp [projectionVertexLabels]

theorem spans_of_normalizePointRows {n d : ℕ}
    (p : Fin n → Fin (d + 1) → ℝ) (hp : Spans (normalizePointRows p)) : Spans p := by
  apply top_unique
  rw [← hp]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  have heq : normalizePointRows p i = (p i 0)⁻¹ • p i := by
    ext a
    simp only [normalizePointRows, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

namespace VertexProjectionChart

variable {P : ConvexPolytope 4} {a : VertexType P} {n : ℕ}

/-- Original coordinates to height-first affine normalization. -/
def coordinateAffineEquiv (D : VertexProjectionChart P a) :
    (Fin 4 → ℝ) ≃ᵃ[ℝ] (Fin 4 → ℝ) :=
  (euclideanCoordinateEquiv 4).symm.toLinearEquiv.toAffineEquiv.trans
    (D.affine.trans (coordinateHomogeneousEquiv 3).symm.toAffineEquiv)

def normalizedCoordinates (D : VertexProjectionChart P a)
    (e : Fin n ≃ ProjectionPoint P a) : Fin (n + 1) → Fin 4 → ℝ :=
  fun i => (coordinateHomogeneousEquiv 3).symm
    (D.affine (projectionVertexLabels e i).val)

@[simp] theorem normalizedCoordinates_zero (D : VertexProjectionChart P a)
    (e : Fin n ≃ ProjectionPoint P a) : D.normalizedCoordinates e 0 = 0 := by
  simp only [normalizedCoordinates, projectionVertexLabels_zero, D.apex, map_zero]

@[simp] theorem normalizedCoordinates_succ (D : VertexProjectionChart P a)
    (e : Fin n ≃ ProjectionPoint P a) (i : Fin n) :
    D.normalizedCoordinates e i.succ =
      (coordinateHomogeneousEquiv 3).symm (D.affine (e i).val.val) := by
  simp only [normalizedCoordinates, projectionVertexLabels_succ]

theorem normalizedCoordinates_eq_affine (D : VertexProjectionChart P a)
    (e : Fin n ≃ ProjectionPoint P a) :
    D.normalizedCoordinates e =
      (fun i => D.coordinateAffineEquiv
        (ordinaryVertexCoordinates P (projectionVertexLabels e) i)) := by
  funext i
  change (coordinateHomogeneousEquiv 3).symm
      (D.affine (projectionVertexLabels e i).val) =
    (coordinateHomogeneousEquiv 3).symm
      (D.affine ((euclideanCoordinateEquiv 4).symm
        (euclideanCoordinateEquiv 4 (projectionVertexLabels e i).val)))
  rw [ContinuousLinearEquiv.symm_apply_apply]

/-- The normalized lifted rows are exactly the homogeneous coordinates
of the actual height-first affine normalization. -/
theorem normalizedCoordinates_homogeneous (D : VertexProjectionChart P a)
    (e : Fin n ≃ ProjectionPoint P a) :
    homogeneousPoints (D.normalizedCoordinates e) =
      normalizePointRows (projectedCenterFamily (D.projectedFamily e) (D.heightFamily e)) := by
  ext i j
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      change (1 : ℝ) = 1 / 1
      simp
    | succ j =>
      change D.normalizedCoordinates e 0 j = (0 : ℝ) / 1
      rw [D.normalizedCoordinates_zero e]
      simp
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      change (1 : ℝ) = D.reciprocalHeight (e i) / D.reciprocalHeight (e i)
      exact (div_self (D.reciprocalHeight_pos (e i)).ne').symm
    | succ j =>
      change D.normalizedCoordinates e i.succ j =
        D.projectedVector (e i) j / D.reciprocalHeight (e i)
      rw [D.normalizedCoordinates_succ e i]
      have hscale : D.projectedVector (e i) = D.reciprocalHeight (e i) •
          (coordinateHomogeneousEquiv 3).symm (D.affine (e i).val.val) := by
        apply (coordinateHomogeneousEquiv 3).injective
        rw [map_smul, LinearEquiv.apply_symm_apply, D.projectedVector_lift]
      rw [hscale]
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp [(D.reciprocalHeight_pos (e i)).ne'] <;> ring

/-- The affine normalization has an actual convex-polytope realization
with the induced labels and exactly the reconstructed homogeneous rows. -/
theorem exists_normalized_actual_polytope (D : VertexProjectionChart P a)
    (hP : P.IsFullDim) (e : Fin n ≃ ProjectionPoint P a) :
    ∃ Q : ConvexPolytope 4, ∃ φ : FaceType P ≃o FaceType Q,
      Q.IsFullDim ∧
      ordinaryVertexCoordinates Q
          ((projectionVertexLabels e).trans (vertexEquivOfFaceOrder φ)) =
        D.normalizedCoordinates e ∧
      vertexCoordinates Q ((projectionVertexLabels e).trans (vertexEquivOfFaceOrder φ)) =
        normalizePointRows (projectedCenterFamily (D.projectedFamily e) (D.heightFamily e)) := by
  have htype : LabelledPolytopeEquivalent
      (ordinaryVertexCoordinates P (projectionVertexLabels e)) (D.normalizedCoordinates e) := by
    rw [D.normalizedCoordinates_eq_affine e]
    exact affineEquiv_labelled_equivalent _ D.coordinateAffineEquiv
  obtain ⟨Q, φ, _, hφ⟩ := actual_polytope_of_labelled_coordinates P
    (projectionVertexLabels e) (D.normalizedCoordinates e) htype
  have hQ : Q.IsFullDim := by
    change Q.dim = 4
    rw [faceOrderIso_polytope_dim φ, hP]
  have hcoord : ordinaryVertexCoordinates Q
        ((projectionVertexLabels e).trans (vertexEquivOfFaceOrder φ)) =
      D.normalizedCoordinates e := by
    funext i
    change euclideanCoordinateEquiv 4 (imageVertex φ (projectionVertexLabels e i)).val = _
    rw [hφ i]
    exact (euclideanCoordinateEquiv 4).apply_symm_apply _
  refine ⟨Q, φ, hQ, hcoord, ?_⟩
  rw [← ordinaryVertexCoordinates_homogeneous, hcoord, D.normalizedCoordinates_homogeneous]

theorem projectedFamily_spans (D : VertexProjectionChart P a)
    (hP : P.IsFullDim) (e : Fin n ≃ ProjectionPoint P a) : Spans (D.projectedFamily e) := by
  obtain ⟨Q, φ, hQ, _, hhom⟩ := D.exists_normalized_actual_polytope hP e
  have hspan := vertexCoordinates_spans Q
    ((projectionVertexLabels e).trans (vertexEquivOfFaceOrder φ)) hQ
  rw [hhom] at hspan
  exact (projectedCenterFamily_spans_iff _ _).mp (spans_of_normalizePointRows _ hspan)

/-- Every facet mask in the normalized coordinates is an actual original
facet, with every label, including the center, accounted for. -/
theorem normalized_facet_actual (D : VertexProjectionChart P a)
    (hP : P.IsFullDim) (e : Fin n ≃ ProjectionPoint P a)
    (T : Finset (Fin (n + 1)))
    (hT : FacetMask
      (normalizePointRows (projectedCenterFamily (D.projectedFamily e) (D.heightFamily e))) T) :
    ∃ F : FacetType P, ∀ i,
      i ∈ T ↔ (projectionVertexLabels e i).val ∈ F.val.val := by
  obtain ⟨Q, φ, _, _, hhom⟩ := D.exists_normalized_actual_polytope hP e
  let eQ := (projectionVertexLabels e).trans (vertexEquivOfFaceOrder φ)
  have hTQ : FacetMask (vertexCoordinates Q eQ) T := by
    rw [hhom]
    exact hT
  obtain ⟨G, hG⟩ := facetMask_actual_three_face Q eQ T hTQ
  let Gface : FaceType Q := ⟨G.val.carrier, G.val.isFace⟩
  let Fface := φ.symm Gface
  have hdim : faceDim Fface.val = 3 :=
    (faceOrderIso_dimension φ.symm Gface).trans G.property
  let F : FacetType P := ⟨Fface, Fface.property, by rw [hdim, hP]⟩
  refine ⟨F, ?_⟩
  intro i
  rw [← hG, mem_actualFaceLabels]
  change (imageVertex φ (projectionVertexLabels e i)).val ∈ Gface.val ↔
    (projectionVertexLabels e i).val ∈ Fface.val
  have hm := imageVertex_mem_iff φ (projectionVertexLabels e i) Fface
  simpa only [Fface, OrderIso.apply_symm_apply] using hm

theorem normalized_facet_correspondence (D : VertexProjectionChart P a)
    (hP : P.IsFullDim) (e : Fin n ≃ ProjectionPoint P a)
    (T : Finset (Fin (n + 1)))
    (hT : T ∈ facetMasks
      (normalizePointRows (projectedCenterFamily (D.projectedFamily e) (D.heightFamily e)))) :
    ∃ F : FacetType P, (0 ∈ T ↔ a.val ∈ F.val.val) ∧
      projectedLabels T = projectedFaceLabels e F.val := by
  obtain ⟨F, hF⟩ := D.normalized_facet_actual hP e T ((mem_facetMasks _ T).mp hT)
  refine ⟨F, ?_, ?_⟩
  · simpa only [projectionVertexLabels_zero] using hF 0
  · ext i
    rw [mem_projectedLabels, mem_projectedFaceLabels]
    simpa only [projectionVertexLabels_succ] using hF i.succ

/-- Return from normalized homogeneous density to approximation of every
original extreme vertex.  The inverse affine map is allowed to be real. -/
theorem rationallyApproximable_of_normalized_density (D : VertexProjectionChart P a)
    (e : Fin n ≃ ProjectionPoint P a)
    (hdense : normalizePointRows
        (projectedCenterFamily (D.projectedFamily e) (D.heightFamily e)) ∈ closure
      {p : Fin (n + 1) → Fin 5 → ℝ |
        RationalCoordinates p ∧ (∀ i, p i 0 = 1) ∧ Spans p ∧
        LabelledPolytopeEquivalent
          (normalizePointRows (projectedCenterFamily (D.projectedFamily e) (D.heightFamily e))) p}) :
    RationallyApproximable P := by
  have ho := ordinary_density_of_homogeneous_density (D.normalizedCoordinates e)
    (by simpa only [D.normalizedCoordinates_homogeneous e] using hdense)
  have hu : D.normalizedCoordinates e ∈ closure
      {v | RationalCoordinates v ∧ LabelledPolytopeEquivalent (D.normalizedCoordinates e) v} :=
    by
      apply closure_mono (s := {v | RationalCoordinates v ∧
        Spans (homogeneousPoints v) ∧ LabelledPolytopeEquivalent (D.normalizedCoordinates e) v}) ?_ ho
      intro v hv
      exact ⟨hv.1, hv.2.2⟩
  have hback := affineEquiv_coordinate_density (D.normalizedCoordinates e)
    D.coordinateAffineEquiv.symm hu
  have hsource : (fun i => D.coordinateAffineEquiv.symm (D.normalizedCoordinates e i)) =
      ordinaryVertexCoordinates P (projectionVertexLabels e) := by
    rw [D.normalizedCoordinates_eq_affine e]
    funext i
    exact D.coordinateAffineEquiv.symm_apply_apply _
  rw [hsource] at hback
  exact rationallyApproximable_of_coordinate_density P (projectionVertexLabels e) hback

end VertexProjectionChart

/-- Actual geometric incidence and height certificates imply rational
approximation of the original real four-polytope.  Every analytic matrix
hypothesis of the reconstruction theorem is derived from the certificate. -/
theorem actual_projection_certificate_rationallyApproximable
    {P : ConvexPolytope 4} {a : VertexType P} {n c : ℕ}
    (hP : P.IsFullDim) (D : VertexProjectionChart P a)
    (e : Fin n ≃ ProjectionPoint P a)
    (K : ActualProjectionReconstructionCertificate e c) : RationallyApproximable P := by
  apply D.rationallyApproximable_of_normalized_density e
  apply rational_polytope_density_from_projected_height_matrix
    (D.projectedFamily e) (D.heightFamily e) (D.projectedFamily_spans hP e)
    K.Allowed K.heights.matrix
    (K.heights.continuousAt_matrix D hP) (K.heights.matrix_rational)
    (K.heights.original_rows_independent D hP)
    (K.heights.original_heights_in_kernel D hP)
    (fun i => D.reciprocalHeight_pos (e i)) (K.rational_projected_density D hP)
  · intro q hq T hT hzero
    obtain ⟨F, hcenter, hlabels⟩ := D.normalized_facet_correspondence hP e T hT
    rw [hlabels]
    have hbound := K.allowed_ordinary_rank q hq ⟨F, hcenter.mp hzero⟩
    change subsetRank q (projectedFaceLabels e F.val) ≤ 3 at hbound
    omega
  · intro q hq T hT hzero
    obtain ⟨F, hcenter, hlabels⟩ := D.normalized_facet_correspondence hP e T hT
    rw [hlabels]
    exact K.allowed_complete_relations q hq ⟨F, fun ha => hzero (hcenter.mpr ha)⟩

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart8
