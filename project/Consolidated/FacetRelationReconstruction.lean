module
public import Papers.RelationMatrixDensity
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic.FunProp
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Papers.RationalityTenRelationSpaces
public import Mathlib.LinearAlgebra.Basis.Basic
public import Papers.RationalityTenPolygonRelationRanks
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Papers.MatrixSupportCounts
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.StdBasis
public import Papers.RationalityTenSupportBasics
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Continuous

/-! Canonical source bundle; each original file retains its own scopes. -/

section BundlePart0
/- Source: Papers/RationalityTenSupportStability.lean -/







@[expose] public section

noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.ChirotopeDensity

/-- Closedness is obtained by projecting a closed incidence condition
along the compact unit sphere. No independence of the selected points
is assumed. -/
theorem isClosed_supportingSubset {n r : ℕ} (S : Finset (Fin n)) :
    IsClosed {p : Fin n → Fin r → ℝ | SupportingSubset p S} := by
  classical
  let U := Metric.sphere (0 : Fin r → ℝ) 1
  letI : CompactSpace U := (isCompact_iff_compactSpace).mp (isCompact_sphere 0 1)
  let T : Set ((Fin n → Fin r → ℝ) × U) :=
    {z | (∀ i, 0 ≤ z.2.1 ⬝ᵥ z.1 i) ∧
      (∀ i∈S, z.2.1 ⬝ᵥ z.1 i=0)}
  have hd (i : Fin n) :
      Continuous (fun z : (Fin n → Fin r → ℝ) × U => z.2.1 ⬝ᵥ z.1 i) :=
    (continuous_subtype_val.comp continuous_snd).dotProduct
      ((continuous_apply i).comp continuous_fst)
  have hnonneg : IsClosed
      (⋂ i : Fin n, {z : (Fin n → Fin r → ℝ) × U | 0 ≤ z.2.1 ⬝ᵥ z.1 i}) :=
    isClosed_iInter fun i => isClosed_le continuous_const (hd i)
  have hzero : IsClosed
      (⋂ i : Fin n, ⋂ (_ : i∈S),
        {z : (Fin n → Fin r → ℝ) × U | z.2.1 ⬝ᵥ z.1 i=0}) :=
    isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_eq (hd i) continuous_const
  have hT : IsClosed T := by
    convert hnonneg.inter hzero using 1
    ext z
    simp [T]
  have himage : Prod.fst '' T =
      {p : Fin n → Fin r → ℝ | SupportingSubset p S} := by
    ext p
    constructor
    · rintro ⟨⟨q,a⟩,ha,rfl⟩
      refine ⟨a.1,?_,ha.1,ha.2⟩
      simpa [U,Metric.mem_sphere,dist_zero_right] using a.2
    · rintro ⟨a,ha,hpos,hzero⟩
      have haU : a∈U := by simpa [U,Metric.mem_sphere,dist_zero_right] using ha
      exact ⟨(p,⟨a,haU⟩),⟨hpos,hzero⟩,rfl⟩
  rw [← himage]
  exact isClosedMap_fst_of_compactSpace T hT

/-- Nearby configurations cannot acquire a supported subset which was
not supported originally. This finite local statement remains valid
at singular configurations. -/
theorem eventually_no_new_supported_subsets {n r : ℕ}
    (p : Fin n → Fin r → ℝ) :
    ∀ᶠ q in 𝓝 p, ∀ S : Finset (Fin n),
      SupportingSubset q S → SupportingSubset p S := by
  classical
  apply eventually_all.mpr
  intro S
  by_cases hS : SupportingSubset p S
  · exact Filter.Eventually.of_forall fun _ _ => hS
  · have hN : {q : Fin n → Fin r → ℝ | ¬ SupportingSubset q S} ∈ 𝓝 p :=
      (isClosed_supportingSubset S).isOpen_compl.mem_nhds hS
    filter_upwards [hN] with q hq hqS
    exact False.elim (hq hqS)

theorem supportingSubset_of_strictSupport {n r : ℕ}
    {p : Fin n → Fin r → ℝ} {S : Finset (Fin n)}
    {a : Fin r → ℝ} (h : StrictSupport p S a) (hS : S≠Finset.univ) :
    SupportingSubset p S := by
  classical
  have hex : ∃ j : Fin n, j∉S := by
    by_contra hh
    push_neg at hh
    apply hS
    ext j
    simp [hh j]
  obtain ⟨j,hj⟩ := hex
  have ha : a≠0 := by
    intro hz
    have hp := h.2 j hj
    simp [hz] at hp
  have hn : ‖a‖≠0 := norm_ne_zero_iff.mpr ha
  have hscale (i : Fin n) :
      (‖a‖⁻¹ • a) ⬝ᵥ p i = ‖a‖⁻¹ * (a ⬝ᵥ p i) := by
    simp [dotProduct,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]
  refine ⟨‖a‖⁻¹ • a,?_,?_,?_⟩
  · rw [norm_smul_of_nonneg (inv_nonneg.mpr (norm_nonneg a)),
      inv_mul_cancel₀ hn]
  · intro i
    rw [hscale]
    apply mul_nonneg (inv_nonneg.mpr (norm_nonneg a))
    by_cases hi : i∈S
    · rw [h.1 i hi]
    · exact (h.2 i hi).le
  · intro i hi
    rw [hscale,h.1 i hi,mul_zero]

/-- The old support normal is reconstructed continuously on the exact
rank stratum. Its strict signs persist without a genericity condition. -/
theorem strictSupport_stable_on_rank_stratum {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (S : Finset (Fin n))
    (a : Fin r → ℝ) (ha : StrictSupport p S a) :
    ∃ F : (Fin n → Fin r → ℝ) → (Fin r → ℝ),
      F p=a ∧ ContinuousAt F p ∧
      (∀ᶠ q in 𝓝 p, subsetRank q S=subsetRank p S →
        StrictSupport q S (F q)) := by
  classical
  let K := Classical.choice (exists_rowKernelChart (maskRows p S))
  let F := fun q : Fin n → Fin r → ℝ => K.eval (maskRows q S) a
  have hbase : F p=a :=
    K.self a ((maskRows_mulVec_zero_iff p S a).mpr ha.1)
  have hcont : ContinuousAt F p := by
    have hparam : Continuous
        (fun q : Fin n → Fin r → ℝ => (maskRows q S,a)) :=
      (maskRows_continuous S).prodMk continuous_const
    exact (K.continuousAt a).comp_of_eq (hparam.continuousAt (x := p)) rfl
  have hrows : ∀ᶠ q in 𝓝 p,
      LinearIndependent ℝ (fun i => maskRows q S (K.rows i)) :=
    (maskRows_continuous S).continuousAt.tendsto.eventually K.eventually_independent
  have hstrict : ∀ᶠ q in 𝓝 p, ∀ i : Fin n, i∉S → 0<F q ⬝ᵥ q i := by
    apply eventually_all.mpr
    intro i
    by_cases hi : i∈S
    · exact Filter.Eventually.of_forall fun _ hh => False.elim (hh hi)
    · have hd : ContinuousAt (fun q => F q ⬝ᵥ q i) p :=
        dotProduct_continuousAt hcont (continuous_apply i).continuousAt
      have hp : 0<F p ⬝ᵥ p i := by simpa only [hbase] using ha.2 i hi
      exact (hd.tendsto.eventually (Ioi_mem_nhds hp)).mono fun q hq _ => hq
  refine ⟨F,hbase,hcont,?_⟩
  filter_upwards [hrows,hstrict] with q hq hpos hqrank
  have hk : (maskRows q S).mulVec (F q)=0 :=
    K.mem (maskRows q S) (by simpa only [maskRows_rank] using hqrank) hq a
  exact ⟨(maskRows_mulVec_zero_iff q S (F q)).mp hk,hpos⟩

/-- Finitely many exact facet supports can be transported simultaneously.
The ranks supplied here are geometric ranks of the actual point subsets. -/
theorem finite_strictSupports_stable_on_rank_strata {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (L : Finset (Finset (Fin n)))
    (hL : ∀ S∈L, ∃ a, StrictSupport p S a) :
    ∀ᶠ q in 𝓝 p,
      (∀ S∈L, subsetRank q S=subsetRank p S) →
      ∀ S∈L, ∃ a, StrictSupport q S a := by
  classical
  have h : ∀ S : Finset (Fin n), ∀ᶠ q in 𝓝 p,
      S∈L → subsetRank q S=subsetRank p S →
      ∃ a, StrictSupport q S a := by
    intro S
    by_cases hS : S∈L
    · obtain ⟨a,ha⟩ := hL S hS
      obtain ⟨F,_,_,hF⟩ := strictSupport_stable_on_rank_stratum p S a ha
      exact hF.mono fun q hq _ hr => ⟨F q,hq hr⟩
    · exact Filter.Eventually.of_forall fun _ hh _ => False.elim (hS hh)
  filter_upwards [eventually_all.mpr h] with q hq hqr S hS
  exact hq S hS (hqr S hS)

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart0

section BundlePart1
/- Source: Papers/RationalityTenFacetRankConstraints.lean -/




@[expose] public section

noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.ChirotopeDensity

/-- A selected basis for the relation space supported on one face.
The numerical equality is the rank-nullity dimension of that space. -/
structure FacetRelationSelection {c n r : ℕ}
    (C : Matrix (Fin c) (Fin n) ℝ)
    (p : Fin n → Fin r → ℝ) (S : Finset (Fin n)) where
  count : ℕ
  rows : Fin count → Fin c
  independent : LinearIndependent ℝ (fun i => C (rows i))
  supported : ∀ i j, j∉S → C (rows i) j=0
  dimension : count + subsetRank p S = S.card

theorem eventually_rank_ge {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ∀ᶠ A' in 𝓝 A, A.rank ≤ A'.rank := by
  classical
  let K := Classical.choice (exists_rowKernelChart A)
  filter_upwards [K.eventually_independent] with A' hA'
  have hr : (A'.submatrix K.rows id).rank=K.rank := by
    simpa only [Fintype.card_fin] using
      (LinearIndependent.rank_matrix (M := A'.submatrix K.rows id) hA')
  have hle := Matrix.rank_submatrix_le A' K.rows id
  rw [hr,← K.rank_eq] at hle
  exact hle

theorem eventually_subsetRank_ge {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (S : Finset (Fin n)) :
    ∀ᶠ q in 𝓝 p, subsetRank p S ≤ subsetRank q S := by
  have h := (maskRows_continuous S).continuousAt.tendsto.eventually
    (eventually_rank_ge (maskRows p S))
  simpa only [maskRows_rank] using h

theorem restricted_point_matrix_rank {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (S : Finset (Fin n)) :
    (Matrix.of (fun (i : S) (j : Fin r) => p i.1 j)).rank =
      subsetRank p S := by
  rw [Matrix.rank_eq_finrank_span_row]
  change finrank ℝ (Submodule.span ℝ (Set.range (fun i : S => p i.1))) = _
  exact congrArg (fun T : Set (Fin r → ℝ) => finrank ℝ (Submodule.span ℝ T))
    (range_restricted_family p (↑S : Set (Fin n)))

theorem independent_restrict_supported_rows {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (S : Finset (Fin n))
    (hA : LinearIndependent ℝ A.row) (hS : ∀ i j, j∉S → A i j=0) :
    LinearIndependent ℝ (fun i : Fin k => fun j : S => A i j.1) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro f hf
  apply (Fintype.linearIndependent_iff.mp hA) f
  ext j
  by_cases hj : j∈S
  · have h := congrFun hf ⟨j,hj⟩
    simpa [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using h
  · simp [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,hS _ j hj]

theorem restricted_relations_mul_zero {k n r : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (p : Fin n → Fin r → ℝ)
    (S : Finset (Fin n)) (hA : A * Matrix.of p=0)
    (hS : ∀ i j, j∉S → A i j=0) :
    Matrix.of (fun (i : Fin k) (j : S) => A i j.1) *
      Matrix.of (fun (j : S) (a : Fin r) => p j.1 a) = 0 := by
  classical
  ext i a
  simp only [Matrix.mul_apply, Matrix.zero_apply, Matrix.of_apply]
  have hsum : (∑ j : S, A i j.val * p j.val a) =
      ∑ j ∈ S, A i j * p j a := S.sum_coe_sort (fun j => A i j * p j a)
  rw [hsum]
  calc
    ∑ j∈S, A i j * p j a = ∑ j : Fin n, A i j * p j a := by
      apply Finset.sum_subset (Finset.subset_univ S)
      intro j _ hj
      rw [hS i j hj,zero_mul]
    _ = 0 := congrFun (congrFun hA i) a

theorem subset_rank_upper_of_supported_relations {k n r : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (p : Fin n → Fin r → ℝ)
    (S : Finset (Fin n))
    (hLI : LinearIndependent ℝ A.row)
    (hS : ∀ i j, j∉S → A i j=0)
    (hA : A * Matrix.of p=0) :
    k + subsetRank p S ≤ S.card := by
  have hLI' := independent_restrict_supported_rows A S hLI hS
  have h := Matrix.rank_add_rank_le_card_of_mul_eq_zero
    (restricted_relations_mul_zero A p S hA hS)
  have hArank : (Matrix.of (fun (i : Fin k) (j : S) => A i j.1)).rank = k := by
    simpa only [Fintype.card_fin] using
      (LinearIndependent.rank_matrix
        (M := Matrix.of (fun (i : Fin k) (j : S) => A i j.1)) hLI')
  rw [hArank,restricted_point_matrix_rank] at h
  simpa using h

/-- Supported relation rows prevent the facial rank from increasing;
a fixed nonzero minor prevents it from decreasing. -/
theorem FacetRelationSelection.eventually_rank_eq {c n r : ℕ}
    {C : Matrix (Fin c) (Fin n) ℝ}
    {p : Fin n → Fin r → ℝ} {S : Finset (Fin n)}
    (B : FacetRelationSelection C p S) :
    ∀ᶠ z : Matrix (Fin c) (Fin n) ℝ × (Fin n → Fin r → ℝ) in 𝓝 (C,p),
      PreservesZeroEntries C z.1 → z.1 * Matrix.of z.2=0 →
      subsetRank z.2 S=subsetRank p S := by
  have hselected : Continuous
      (fun z : Matrix (Fin c) (Fin n) ℝ × (Fin n → Fin r → ℝ) =>
        fun i => z.1 (B.rows i)) :=
    continuous_pi fun i => (continuous_apply (B.rows i)).comp continuous_fst
  have hLI : ∀ᶠ z in 𝓝 (C,p),
      LinearIndependent ℝ (fun i => z.1 (B.rows i)) :=
    (hselected.continuousAt (x := (C,p))).tendsto.eventually B.independent.eventually
  have hlow : ∀ᶠ z : Matrix (Fin c) (Fin n) ℝ × (Fin n → Fin r → ℝ)
      in 𝓝 (C,p), subsetRank p S ≤ subsetRank z.2 S :=
    (continuous_snd.continuousAt (x := (C,p))).tendsto.eventually (eventually_subsetRank_ge p S)
  filter_upwards [hLI,hlow] with z hz hle hzero hrel
  have hsupp : ∀ i j, j∉S → z.1 (B.rows i) j=0 :=
    fun i j hj => hzero (B.rows i) j (B.supported i j hj)
  have hmul : Matrix.of (fun i => z.1 (B.rows i)) * Matrix.of z.2=0 := by
    ext i j
    exact congrFun (congrFun hrel (B.rows i)) j
  have hu := subset_rank_upper_of_supported_relations
    (Matrix.of (fun i => z.1 (B.rows i))) z.2 S hz hsupp hmul
  have hd := B.dimension
  omega

theorem selected_facet_ranks_and_supports_stable {c n r : ℕ}
    (C : Matrix (Fin c) (Fin n) ℝ) (p : Fin n → Fin r → ℝ)
    (L : Finset (Finset (Fin n)))
    (hB : ∀ S∈L, Nonempty (FacetRelationSelection C p S))
    (hL : ∀ S∈L, ∃ a, StrictSupport p S a) :
    ∀ᶠ z : Matrix (Fin c) (Fin n) ℝ × (Fin n → Fin r → ℝ) in 𝓝 (C,p),
      PreservesZeroEntries C z.1 → z.1 * Matrix.of z.2=0 →
      (∀ S∈L, subsetRank z.2 S=subsetRank p S) ∧
      (∀ S∈L, ∃ a, StrictSupport z.2 S a) ∧
      (∀ S, SupportingSubset z.2 S → SupportingSubset p S) := by
  classical
  have hranks : ∀ᶠ z : Matrix (Fin c) (Fin n) ℝ × (Fin n → Fin r → ℝ)
      in 𝓝 (C,p), ∀ S∈L,
      PreservesZeroEntries C z.1 → z.1 * Matrix.of z.2=0 →
      subsetRank z.2 S=subsetRank p S := by
    apply eventually_all.mpr
    intro S
    by_cases hS : S∈L
    · obtain ⟨B⟩ := hB S hS
      exact B.eventually_rank_eq.mono fun z hz _ => hz
    · exact Filter.Eventually.of_forall fun _ hh => False.elim (hS hh)
  have hsupp := (continuous_snd.continuousAt (x := (C,p))).tendsto.eventually
    (finite_strictSupports_stable_on_rank_strata p L hL)
  have hnonew := (continuous_snd.continuousAt (x := (C,p))).tendsto.eventually
    (eventually_no_new_supported_subsets p)
  filter_upwards [hranks,hsupp,hnonew] with z hz hs hn hzero hrel
  have hr : ∀ S∈L, subsetRank z.2 S=subsetRank p S :=
    fun S hS => hz S hS hzero hrel
  exact ⟨hr,hs hr,hn⟩

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart1

section BundlePart2
/- Source: Papers/RationalityTenFacetRelationSpace.lean -/





@[expose] public section

noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.ChirotopeDensity

def supportedRelationRows {c n : ℕ}
    (C : Matrix (Fin c) (Fin n) ℝ) (S : Finset (Fin n)) :
    Finset (Fin c) := by
  classical
  exact Finset.univ.filter (fun i => ∀ j, j∉S → C i j=0)

def restrictedSupportedRows {c n : ℕ}
    (C : Matrix (Fin c) (Fin n) ℝ) (S : Finset (Fin n)) :
    supportedRelationRows C S → (S → ℝ) :=
  fun i j => C i.1 j.1

/-- This is a statement about the entire actual relation space, not merely
a list of equations which happen to vanish on one chosen configuration. -/
def SpansFacetRelations {c n r : ℕ}
    (C : Matrix (Fin c) (Fin n) ℝ)
    (p : Fin n → Fin r → ℝ) (S : Finset (Fin n)) : Prop :=
  Submodule.span ℝ (Set.range (restrictedSupportedRows C S)) =
    facetRelationSpace p S

theorem exists_finite_family_basis_indices
    {ι W : Type*} [Fintype ι] [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W] (v : ι → W) :
    ∃ k : ℕ, ∃ f : Fin k → ι,
      LinearIndependent ℝ (v ∘ f) ∧
      Submodule.span ℝ (Set.range (v ∘ f)) =
        Submodule.span ℝ (Set.range v) ∧
      k=finrank ℝ (Submodule.span ℝ (Set.range v)) := by
  classical
  have hempty : LinearIndepOn ℝ v (∅ : Set ι) := by simp
  let T := hempty.extend (Set.empty_subset (Set.univ : Set ι))
  have hT : LinearIndepOn ℝ v T := hempty.linearIndepOn_extend _
  have hspan : Submodule.span ℝ (v '' T) =
      Submodule.span ℝ (Set.range v) := by
    simpa only [Set.image_univ] using hempty.span_image_extend_eq_span_image
      (Set.empty_subset (Set.univ : Set ι))
  let k := Fintype.card T
  let e : Fin k ≃ T := Fintype.equivOfCardEq (by simp [k])
  let f : Fin k → ι := fun i => (e i).1
  have hLI : LinearIndependent ℝ (v ∘ f) := hT.comp e e.injective
  have hrange : Set.range (v ∘ f)=v '' T := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨(e i).1,(e i).2,rfl⟩
    · rintro ⟨i,hi,rfl⟩
      refine ⟨e.symm ⟨i,hi⟩,?_⟩
      simp [f,Function.comp_def]
  refine ⟨k,f,hLI,by rw [hrange,hspan],?_⟩
  have hc := linearIndependent_iff_card_eq_finrank_span.mp hLI
  change Fintype.card (Fin k) = finrank ℝ (Submodule.span ℝ (Set.range (v ∘ f))) at hc
  rw [Fintype.card_fin, hrange, hspan] at hc
  exact hc

theorem facetRelationSelection_of_spanning {c n r : ℕ}
    (C : Matrix (Fin c) (Fin n) ℝ)
    (p : Fin n → Fin r → ℝ) (S : Finset (Fin n))
    (hspan : SpansFacetRelations C p S) :
    Nonempty (FacetRelationSelection C p S) := by
  classical
  obtain ⟨k,f,hLI,_,hk⟩ :=
    exists_finite_family_basis_indices (restrictedSupportedRows C S)
  let rows : Fin k → Fin c := fun i => (f i).1
  have hfull : LinearIndependent ℝ (fun i => C (rows i)) := by
    apply Fintype.linearIndependent_iff.mpr
    intro a ha
    apply (Fintype.linearIndependent_iff.mp hLI) a
    ext j
    have hh := congrFun ha j.1
    simpa [restrictedSupportedRows,rows,Function.comp_def,Finset.sum_apply,
      Pi.smul_apply,smul_eq_mul] using hh
  have hsupp : ∀ i j, j∉S → C (rows i) j=0 := by
    intro i j hj
    exact (Finset.mem_filter.mp (f i).2).2 j hj
  have hdim := facetRelationSpace_finrank p S
  change Submodule.span ℝ (Set.range (restrictedSupportedRows C S)) =
    facetRelationSpace p S at hspan
  rw [hspan] at hk
  exact ⟨⟨k,rows,hfull,hsupp,by omega⟩⟩

theorem restricted_supported_row_mem_relationSpace {c n r : ℕ}
    (C : Matrix (Fin c) (Fin n) ℝ)
    (p : Fin n → Fin r → ℝ) (hCp : C * Matrix.of p=0)
    (S : Finset (Fin n)) (i : supportedRelationRows C S) :
    restrictedSupportedRows C S i ∈ facetRelationSpace p S := by
  classical
  have hsupp := (Finset.mem_filter.mp i.2).2
  change (Matrix.of p).transpose.mulVec
    (insideInjection (K := ℝ) S (restrictedSupportedRows C S i))=0
  ext a
  have h := congrFun (congrFun hCp i.1) a
  change (∑ j : Fin n, C i.1 j * p j a)=0 at h
  change (∑ j : Fin n, p j a *
    insideInjection (K := ℝ) S (restrictedSupportedRows C S i) j)=0
  convert h using 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j∈S
  · simp [insideInjection,restrictedSupportedRows,hj,mul_comm]
  · simp [insideInjection,hj,hsupp j hj]

theorem supported_rows_span_le_relationSpace {c n r : ℕ}
    (C : Matrix (Fin c) (Fin n) ℝ)
    (p : Fin n → Fin r → ℝ) (hCp : C * Matrix.of p=0)
    (S : Finset (Fin n)) :
    Submodule.span ℝ (Set.range (restrictedSupportedRows C S)) ≤
      facetRelationSpace p S := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  exact restricted_supported_row_mem_relationSpace C p hCp S i

/-- The selection structure is equivalent to spanning the full facial
relation space whenever the listed rows are actual global relations. -/
theorem facetRelationSelection_iff_spanning {c n r : ℕ}
    (C : Matrix (Fin c) (Fin n) ℝ)
    (p : Fin n → Fin r → ℝ) (hCp : C * Matrix.of p=0)
    (S : Finset (Fin n)) :
    Nonempty (FacetRelationSelection C p S) ↔ SpansFacetRelations C p S := by
  classical
  constructor
  · rintro ⟨B⟩
    let v : Fin B.count → S → ℝ := fun i j => C (B.rows i) j.1
    have hLI : LinearIndependent ℝ v :=
      independent_restrict_supported_rows (fun i => C (B.rows i)) S
        B.independent B.supported
    have hsub : Submodule.span ℝ (Set.range v) ≤
        Submodule.span ℝ (Set.range (restrictedSupportedRows C S)) := by
      apply Submodule.span_mono
      rintro _ ⟨i,rfl⟩
      have hi : B.rows i∈supportedRelationRows C S :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,B.supported i⟩
      exact ⟨⟨B.rows i,hi⟩,rfl⟩
    have hall := supported_rows_span_le_relationSpace C p hCp S
    have hdim : finrank ℝ (Submodule.span ℝ (Set.range v))=B.count := by
      have h := linearIndependent_iff_card_eq_finrank_span.mp hLI
      simpa [Set.finrank] using h.symm
    have hrel := facetRelationSpace_finrank p S
    have hBdim := B.dimension
    have heq : Submodule.span ℝ (Set.range v)=facetRelationSpace p S :=
      Submodule.eq_of_le_of_finrank_eq (hsub.trans hall) (by omega)
    apply le_antisymm hall
    rw [← heq]
    exact hsub
  · exact facetRelationSelection_of_spanning C p S

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart2

section BundlePart3
/- Source: Papers/FiniteRelationSpaceExtensions.lean -/




@[expose] public section
noncomputable section
open Set Module
open scoped BigOperators

namespace Papers.RationalityTen.ChirotopeDensity

variable {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

structure FiniteSpaceSupplement (U V : Submodule ℝ W) where
  count : ℕ
  rows : Fin count → W
  mem : ∀i,rows i∈V
  spans : U ⊔ Submodule.span ℝ (Set.range rows)=V
  dimension : count+finrank ℝ U=finrank ℝ V

/-- Extend a previously shared relation space inside one facet. The number
of added rows is exactly the remaining dimension, even when the previously
chosen polygon bases have dependencies among themselves. -/
theorem exists_finiteSpaceSupplement (U V : Submodule ℝ W) (hUV : U≤V) :
    Nonempty (FiniteSpaceSupplement U V) := by
  classical
  let U' : Submodule ℝ V := U.submoduleOf V
  obtain ⟨T,hT⟩ := Submodule.exists_isCompl U'
  let B : Basis (Fin (finrank ℝ T)) ℝ T := Module.finBasis ℝ T
  let rows : Fin (finrank ℝ T) → W := fun i => ((B i).val : W)
  have hUdim : finrank ℝ U'=finrank ℝ U :=
    (Submodule.submoduleOfEquivOfLe hUV).finrank_eq
  have hdim := Submodule.finrank_add_eq_of_isCompl hT
  have hUmap : U'.map V.subtype=U := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x,hUV hx⟩,hx,rfl⟩
  have hBspan : Submodule.span ℝ (Set.range (fun i => (B i).val))=T := by
    change Submodule.span ℝ (Set.range (T.subtype ∘ B))=T
    rw [Set.range_comp,←Submodule.map_span,B.span_eq,Submodule.map_top,
      Submodule.range_subtype]
  have hspan : Submodule.span ℝ (Set.range rows)=T.map V.subtype := by
    change Submodule.span ℝ (Set.range (V.subtype ∘ (fun i => (B i).val)))=_
    rw [Set.range_comp,←Submodule.map_span,hBspan]
  refine ⟨⟨finrank ℝ T,rows,(fun i => (B i).val.property),?_,?_⟩⟩
  · rw [hspan,←hUmap,←Submodule.map_sup,hT.codisjoint.eq_top,
      Submodule.map_top,Submodule.range_subtype]
  · omega

theorem span_basis_coe (U : Submodule ℝ W) :
    Submodule.span ℝ (Set.range (fun i : Fin (finrank ℝ U) =>
      (Module.finBasis ℝ U i).val))=U := by
  change Submodule.span ℝ (Set.range (U.subtype ∘ Module.finBasis ℝ U))=U
  rw [Set.range_comp,←Submodule.map_span,(Module.finBasis ℝ U).span_eq,
    Submodule.map_top,Submodule.range_subtype]

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart3

section BundlePart4
/- Source: Papers/SparseRelationGenerators.lean -/







@[expose] public section

/-!
# Sparse generators and sparse supplements for relation spaces

A basis selected among the point vectors gives a linear section of their
coefficient map. The complementary projection sends standard basis vectors
to relations supported on at most rank + 1 coordinates. Selecting a basis
of these generators in a quotient supplies a sparse supplement to any
previously shared subspace, with exactly the required remaining dimension.
-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Matrix
open scoped Classical BigOperators

/-- Fundamental relations, including harmless zero generators at the
selected basis coordinates, span the entire kernel. -/
theorem exists_sparse_kernel_generators
    {I W : Type*} [Fintype I] [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W] (u : I → W) :
    ∃ rows : I → I → ℝ,
      Submodule.span ℝ (Set.range rows) = (Fintype.linearCombination ℝ u).ker ∧
      ∀ i, (vectorSupport (rows i)).card ≤
        finrank ℝ (Submodule.span ℝ (Set.range u)) + 1 := by
  obtain ⟨k, f, hLI, hspan, hk⟩ := exists_finite_family_basis_indices u
  let U := Submodule.span ℝ (Set.range (u ∘ f))
  have hu (i : I) : u i ∈ U := by
    change u i ∈ Submodule.span ℝ (Set.range (u ∘ f))
    rw [hspan]
    exact Submodule.subset_span (Set.mem_range_self i)
  let v : I → U := fun i => ⟨u i, hu i⟩
  let b : Basis (Fin k) ℝ U := Basis.span hLI
  let L : (I → ℝ) →ₗ[ℝ] U := Fintype.linearCombination ℝ v
  let A : (Fin k → ℝ) →ₗ[ℝ] (I → ℝ) :=
    Fintype.linearCombination ℝ (fun t => Pi.single (f t) 1)
  let sec : U →ₗ[ℝ] (I → ℝ) := A.comp b.equivFun.toLinearMap
  have hsingle (i : I) : L (Pi.single i 1) = v i := by
    simp [L]
  have hb (t : Fin k) : v (f t) = b t := by
    apply Subtype.ext
    change u (f t) = ((Basis.span hLI t : U) : W)
    exact (Basis.coe_span_apply hLI t).symm
  have hsection (z : U) : L (sec z) = z := by
    change L (∑ t : Fin k, b.equivFun z t • Pi.single (f t) 1) = z
    rw [map_sum]
    simp_rw [map_smul, hsingle, hb]
    exact b.sum_equivFun z
  have hcoerce : U.subtype.comp L = Fintype.linearCombination ℝ u := by
    apply LinearMap.ext
    intro a
    simp only [LinearMap.comp_apply, L, Fintype.linearCombination_apply,
      Submodule.subtype_apply, Submodule.coe_sum, Submodule.coe_smul]
    rfl
  have hker (a : I → ℝ) : (Fintype.linearCombination ℝ u) a = 0 ↔ L a = 0 := by
    rw [← hcoerce]
    change ((L a : U) : W) = 0 ↔ L a = 0
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  let R : (I → ℝ) →ₗ[ℝ] (I → ℝ) := LinearMap.id - sec.comp L
  have hrange : R.range = (Fintype.linearCombination ℝ u).ker := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      change (Fintype.linearCombination ℝ u) (R x) = 0
      apply (hker _).mpr
      change L (x - sec (L x)) = 0
      rw [map_sub, hsection, sub_self]
    · intro ha
      refine ⟨a, ?_⟩
      have hz : L a = 0 := (hker a).mp ha
      change a - sec (L a) = a
      rw [hz, map_zero, sub_zero]
  let rows : I → I → ℝ := fun i => R (Pi.single i 1)
  have hrows : Submodule.span ℝ (Set.range rows) = R.range := by
    have heq : rows = R ∘ Pi.basisFun ℝ I := by
      funext i
      simp only [Function.comp_apply, Pi.basisFun_apply]
      rfl
    rw [heq, Set.range_comp, ← Submodule.map_span, (Pi.basisFun ℝ I).span_eq,
      Submodule.map_top]
  refine ⟨rows, hrows.trans hrange, ?_⟩
  intro i
  let T : Finset I := insert i (Finset.univ.image f)
  have hsupp : vectorSupport (rows i) ⊆ T := by
    intro j hj
    by_contra hjT
    have hji : j ≠ i := by
      intro heq
      subst j
      exact hjT (Finset.mem_insert_self _ _)
    have hfj (t : Fin k) : f t ≠ j := by
      intro h
      exact hjT (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, h⟩))
    apply (mem_vectorSupport _ _).mp hj
    change (Pi.single i (1 : ℝ) : I → ℝ) j -
      (∑ t : Fin k, b.equivFun (L (Pi.single i 1)) t • Pi.single (f t) 1) j = 0
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, hji,
      fun t => Ne.symm (hfj t), if_false, smul_zero, Finset.sum_const_zero, sub_self]
  have hcard : T.card ≤ k + 1 := by
    have h₁ := Finset.card_insert_le i (Finset.univ.image f)
    have h₂ := Finset.card_image_le (s := Finset.univ) (f := f)
    have h₃ : (Finset.univ : Finset (Fin k)).card = k := by simp
    dsimp only [T]
    omega
  exact (Finset.card_le_card hsupp).trans (by simpa only [hk] using hcard)

theorem insideInjection_single_sparse {n : ℕ} (S : Finset (Fin n)) (i : S) :
    insideInjection (K := ℝ) S (Pi.single i 1) = Pi.single i.val 1 := by
  ext j
  by_cases hj : j ∈ S
  · by_cases hji : j = i.val
    · subst j
      simp [insideInjection, i.property]
    · have hsub : (⟨j, hj⟩ : S) ≠ i := fun h => hji (congrArg Subtype.val h)
      simp [insideInjection, hj, Pi.single_apply, Ne.symm hji, Ne.symm hsub]
  · have hij : i.val ≠ j := fun h => hj (h ▸ i.property)
    simp [insideInjection, hj, Pi.single_apply, hij]

theorem facetRelationSpace_eq_kernel_combination {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (S : Finset (Fin n)) :
    facetRelationSpace p S =
      (Fintype.linearCombination ℝ (fun i : S => p i.val)).ker := by
  have hL : ((Matrix.of p).transpose.mulVecLin).comp (insideInjection (K := ℝ) S) =
      Fintype.linearCombination ℝ (fun i : S => p i.val) := by
    apply (Pi.basisFun ℝ S).ext
    intro i
    simp only [Pi.basisFun_apply, LinearMap.comp_apply, insideInjection_single,
      Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Fintype.linearCombination_apply_single,
      one_smul]
    rfl
  exact congrArg LinearMap.ker hL

theorem vectorSupport_insideInjection {n : ℕ} (S : Finset (Fin n)) (v : S → ℝ) :
    vectorSupport (insideInjection (K := ℝ) S v) =
      (vectorSupport v).image Subtype.val := by
  ext i
  constructor
  · intro hi
    have hv := (mem_vectorSupport _ _).mp hi
    have hiS : i ∈ S := by
      by_contra h
      exact hv (by simp [insideInjection, h])
    refine Finset.mem_image.mpr ⟨⟨i, hiS⟩, ?_, rfl⟩
    apply (mem_vectorSupport _ _).mpr
    simpa [insideInjection, hiS] using hv
  · intro hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    apply (mem_vectorSupport _ _).mpr
    simpa [insideInjection, j.property] using (mem_vectorSupport _ _).mp hj

theorem exists_sparse_global_relation_generators {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (S : Finset (Fin n)) :
    ∃ rows : S → Fin n → ℝ,
      Submodule.span ℝ (Set.range rows) = globalRelationSpace p S ∧
      ∀ i, (vectorSupport (rows i)).card ≤ subsetRank p S + 1 := by
  obtain ⟨w, hw, hsparse⟩ :=
    exists_sparse_kernel_generators (fun i : S => p i.val)
  let rows : S → Fin n → ℝ := fun i => insideInjection (K := ℝ) S (w i)
  have hrange : Set.range (fun i : S => p i.val) = p '' (↑S : Set (Fin n)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  refine ⟨rows, ?_, ?_⟩
  · change Submodule.span ℝ (Set.range ((insideInjection (K := ℝ) S) ∘ w)) = _
    rw [Set.range_comp, ← Submodule.map_span, hw,
      ← facetRelationSpace_eq_kernel_combination, globalRelationSpace, globalRelationMap,
      LinearMap.range_comp, Submodule.range_subtype]
  · intro i
    rw [show rows i = insideInjection (K := ℝ) S (w i) from rfl,
      vectorSupport_insideInjection,
      Finset.card_image_of_injective _ Subtype.val_injective]
    have hi := hsparse i
    rw [hrange] at hi
    exact hi

/-- A supplement can be selected from any specified generating family.
In particular, this preserves support bounds on those generators. -/
theorem exists_finiteSpaceSupplement_from_generators
    {I W : Type*} [Fintype I] [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W]
    (U V : Submodule ℝ W) (hUV : U ≤ V)
    (g : I → W) (hg : Submodule.span ℝ (Set.range g) = V) :
    ∃ D : FiniteSpaceSupplement U V, ∀ i, D.rows i ∈ Set.range g := by
  let U' : Submodule ℝ V := U.submoduleOf V
  have hgmem (i : I) : g i ∈ V := hg ▸ Submodule.subset_span (Set.mem_range_self i)
  let v : I → V := fun i => ⟨g i, hgmem i⟩
  have hspanv : Submodule.span ℝ (Set.range v) = ⊤ := by
    apply Submodule.map_injective_of_injective V.subtype_injective
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
    exact hg
  let w : I → V ⧸ U' := fun i => U'.mkQ (v i)
  have hspanw : Submodule.span ℝ (Set.range w) = ⊤ := by
    change Submodule.span ℝ (Set.range (U'.mkQ ∘ v)) = _
    rw [Set.range_comp, ← Submodule.map_span, hspanv,
      Submodule.map_top, Submodule.range_mkQ]
  obtain ⟨k, f, hLI, hspan, hk⟩ := exists_finite_family_basis_indices w
  let rows : Fin k → W := g ∘ f
  let T : Submodule ℝ V := Submodule.span ℝ (Set.range (v ∘ f))
  have hquot : T.map U'.mkQ = ⊤ := by
    dsimp only [T]
    rw [Submodule.map_span, ← Set.range_comp]
    change Submodule.span ℝ (Set.range (w ∘ f)) = ⊤
    exact hspan.trans hspanw
  have hsup : U' ⊔ T = ⊤ := (Submodule.map_mkQ_eq_top U' T).mp hquot
  have hUmap : U'.map V.subtype = U := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hUV hx⟩, hx, rfl⟩
  have hTmap : T.map V.subtype = Submodule.span ℝ (Set.range rows) := by
    dsimp only [T]
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hdimU : finrank ℝ U' = finrank ℝ U :=
    (Submodule.submoduleOfEquivOfLe hUV).finrank_eq
  have hdim := U'.finrank_quotient_add_finrank
  rw [hspanw, finrank_top] at hk
  refine ⟨⟨k, rows, (fun i => hgmem (f i)), ?_, by omega⟩, ?_⟩
  · rw [← hUmap, ← hTmap, ← Submodule.map_sup, hsup,
      Submodule.map_top, Submodule.range_subtype]
  · intro i
    exact ⟨f i, rfl⟩

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart4

section BundlePart5
/- Source: Papers/RationalityTenExposedSupports.lean -/





@[expose] public section

noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.ChirotopeDensity

def coordinateHull {n r : ℕ} (p : Fin n → Fin r → ℝ) :
    Set (Fin r → ℝ) := convexHull ℝ (Set.range p)

def labelledHull {n r : ℕ} (p : Fin n → Fin r → ℝ)
    (S : Finset (Fin n)) : Set (Fin r → ℝ) :=
  convexHull ℝ (p '' (↑S : Set (Fin n)))

theorem StrictSupport.nonneg {n r : ℕ}
    {p : Fin n → Fin r → ℝ} {S : Finset (Fin n)}
    {a : Fin r → ℝ} (h : StrictSupport p S a) (i : Fin n) :
    0≤a ⬝ᵥ p i := by
  by_cases hi : i∈S
  · rw [h.1 i hi]
  · exact (h.2 i hi).le

theorem StrictSupport.nonneg_on_hull {n r : ℕ}
    {p : Fin n → Fin r → ℝ} {S : Finset (Fin n)}
    {a : Fin r → ℝ} (h : StrictSupport p S a) :
    ∀ x∈coordinateHull p, 0≤a ⬝ᵥ x := by
  apply convexHull_min
  · rintro _ ⟨i,rfl⟩
    exact h.nonneg i
  · exact convex_halfSpace_ge (dotLinear a).isLinear 0

/-- Exposed faces of a finite convex hull are the convex hulls of the
original generators lying on them; extremality of every generator is
not required. -/
theorem exposed_face_eq_hull_generators {n r : ℕ}
    (p : Fin n → Fin r → ℝ) {F : Set (Fin r → ℝ)}
    (hF : IsExposed ℝ (coordinateHull p) F) :
    F=convexHull ℝ (Set.range p ∩ F) := by
  have hK : IsCompact (coordinateHull p) :=
    (Set.finite_range p).isCompact_convexHull ℝ
  have hFc := hF.isCompact hK
  have hFv := hF.convex (convex_convexHull ℝ (Set.range p))
  have hfinite : (Set.range p ∩ F).Finite :=
    (Set.finite_range p).subset Set.inter_subset_left
  apply le_antisymm
  · calc
      F = closure (convexHull ℝ (F.extremePoints ℝ)) :=
        (closure_convexHull_extremePoints hFc hFv).symm
      _ ⊆ convexHull ℝ (Set.range p ∩ F) := by
        apply closure_minimal
        · apply convexHull_mono
          intro x hx
          rw [hF.isExtreme.extremePoints_eq] at hx
          exact ⟨extremePoints_convexHull_subset hx.2,hx.1⟩
        · exact hfinite.isClosed_convexHull ℝ
  · exact convexHull_min Set.inter_subset_right hFv

theorem strictSupport_exposed_zero_set {n r : ℕ}
    {p : Fin n → Fin r → ℝ} {S : Finset (Fin n)}
    {a : Fin r → ℝ} (h : StrictSupport p S a) (hS : S.Nonempty) :
    IsExposed ℝ (coordinateHull p) {x∈coordinateHull p | a ⬝ᵥ x=0} := by
  let l : (Fin r → ℝ) →L[ℝ] ℝ := (dotLinear a).toContinuousLinearMap
  obtain ⟨i,hi⟩ := hS
  have hip : p i∈coordinateHull p := subset_convexHull ℝ _ ⟨i,rfl⟩
  intro _
  refine ⟨-l,?_⟩
  ext x
  constructor
  · rintro ⟨hx,hzero⟩
    refine ⟨hx,?_⟩
    intro y hy
    have hn := h.nonneg_on_hull y hy
    change -(a ⬝ᵥ y) ≤ -(a ⬝ᵥ x)
    linarith
  · rintro ⟨hx,hmax⟩
    refine ⟨hx,?_⟩
    have hm := hmax (p i) hip
    have hn := h.nonneg_on_hull x hx
    change -(a ⬝ᵥ p i) ≤ -(a ⬝ᵥ x) at hm
    rw [h.1 i hi] at hm
    linarith

theorem strictSupport_zero_set_eq_hull {n r : ℕ}
    {p : Fin n → Fin r → ℝ} {S : Finset (Fin n)}
    {a : Fin r → ℝ} (h : StrictSupport p S a) (hS : S.Nonempty) :
    {x∈coordinateHull p | a ⬝ᵥ x=0}=labelledHull p S := by
  rw [exposed_face_eq_hull_generators p (strictSupport_exposed_zero_set h hS)]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨i,rfl⟩,_,hzero⟩
    refine ⟨i,?_,rfl⟩
    by_contra hi
    exact (ne_of_gt (h.2 i hi)) hzero
  · rintro ⟨i,hi,rfl⟩
    exact ⟨⟨i,rfl⟩,subset_convexHull ℝ _ ⟨i,rfl⟩,h.1 i hi⟩

theorem strictSupport_exposed_hull {n r : ℕ}
    {p : Fin n → Fin r → ℝ} {S : Finset (Fin n)}
    {a : Fin r → ℝ} (h : StrictSupport p S a) (hS : S.Nonempty) :
    IsExposed ℝ (coordinateHull p) (labelledHull p S) := by
  rw [← strictSupport_zero_set_eq_hull h hS]
  exact strictSupport_exposed_zero_set h hS

theorem strictSupport_label_exact {n r : ℕ}
    {p : Fin n → Fin r → ℝ} {S : Finset (Fin n)}
    {a : Fin r → ℝ} (h : StrictSupport p S a) (hS : S.Nonempty)
    (i : Fin n) :
    p i∈labelledHull p S ↔ i∈S := by
  rw [← strictSupport_zero_set_eq_hull h hS]
  constructor
  · rintro ⟨_,hz⟩
    by_contra hi
    exact (ne_of_gt (h.2 i hi)) hz
  · intro hi
    exact ⟨subset_convexHull ℝ _ ⟨i,rfl⟩,h.1 i hi⟩

def faceLabels {n r : ℕ} (p : Fin n → Fin r → ℝ)
    (F : Set (Fin r → ℝ)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => p i∈F)

theorem image_faceLabels {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (F : Set (Fin r → ℝ)) :
    p '' (↑(faceLabels p F) : Set (Fin n))=Set.range p ∩ F := by
  classical
  ext x
  constructor
  · rintro ⟨i,hi,rfl⟩
    exact ⟨⟨i,rfl⟩,(Finset.mem_filter.mp hi).2⟩
  · rintro ⟨⟨i,rfl⟩,hi⟩
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,rfl⟩

theorem exposed_face_eq_labelledHull {n r : ℕ}
    (p : Fin n → Fin r → ℝ) {F : Set (Fin r → ℝ)}
    (hF : IsExposed ℝ (coordinateHull p) F) :
    F=labelledHull p (faceLabels p F) := by
  rw [labelledHull,image_faceLabels]
  exact exposed_face_eq_hull_generators p hF

theorem faceLabels_nonempty {n r : ℕ}
    (p : Fin n → Fin r → ℝ) {F : Set (Fin r → ℝ)}
    (hF : IsExposed ℝ (coordinateHull p) F) (hne : F.Nonempty) :
    (faceLabels p F).Nonempty := by
  classical
  obtain ⟨x,hx⟩ := hne
  rw [exposed_face_eq_labelledHull p hF] at hx
  by_contra h
  have he := Finset.not_nonempty_iff_eq_empty.mp h
  simpa [labelledHull,he] using hx

def functionalCoefficients {r : ℕ} (l : (Fin r → ℝ) →L[ℝ] ℝ) :
    Fin r → ℝ := fun j => l (Pi.single j 1)

theorem functionalCoefficients_dot {r : ℕ}
    (l : (Fin r → ℝ) →L[ℝ] ℝ) (x : Fin r → ℝ) :
    functionalCoefficients l ⬝ᵥ x=l x := by
  have h := congrArg l ((Pi.basisFun ℝ (Fin r)).sum_repr x)
  simpa [functionalCoefficients,dotProduct,Pi.basisFun_apply,mul_comm] using h

theorem exposed_face_strictSupport {n d : ℕ}
    (p : Fin n → Fin (d+1) → ℝ) (hp : ∀ i, p i 0=1)
    {F : Set (Fin (d+1) → ℝ)}
    (hF : IsExposed ℝ (coordinateHull p) F) (hne : F.Nonempty) :
    ∃ a, StrictSupport p (faceLabels p F) a := by
  classical
  obtain ⟨l,hl⟩ := hF hne
  obtain ⟨x,hx⟩ := hne
  have hx' := hx
  rw [hl] at hx'
  let a : Fin (d+1) → ℝ := Pi.single 0 (l x) - functionalCoefficients l
  have ha (i : Fin n) : a ⬝ᵥ p i=l x-l (p i) := by
    change (Pi.single 0 (l x) - functionalCoefficients l) ⬝ᵥ p i = l x - l (p i)
    rw [sub_dotProduct,single_dotProduct,hp i,mul_one,functionalCoefficients_dot]
  refine ⟨a,?_,?_⟩
  · intro i hi
    have hiF := (Finset.mem_filter.mp hi).2
    rw [hl] at hiF
    have h₁ := hx'.2 (p i) hiF.1
    have h₂ := hiF.2 x hx'.1
    rw [ha]
    linarith
  · intro i hi
    have hip : p i∈coordinateHull p := subset_convexHull ℝ _ ⟨i,rfl⟩
    have hle := hx'.2 (p i) hip
    have hlt : l (p i)<l x := by
      rcases lt_or_eq_of_le hle with hh|hh
      · exact hh
      · exfalso
        apply hi
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        rw [hl]
        exact ⟨hip,fun y hy => by rw [hh]; exact hx'.2 y hy⟩
    rw [ha]
    linarith

abbrev SupportLabel {n r : ℕ} (p : Fin n → Fin r → ℝ) :=
  {S : Finset (Fin n) // S.Nonempty ∧ ∃ a, StrictSupport p S a}

abbrev ActualCoordinateFace {n r : ℕ} (p : Fin n → Fin r → ℝ) :=
  {F : Set (Fin r → ℝ) // IsExposed ℝ (coordinateHull p) F ∧ F.Nonempty}

/-- The support predicate is exactly the ordinary exposed face order
of the actual finite convex hull in the affine chart x₀=1. -/
def homogeneousFaceOrderIso {n d : ℕ}
    (p : Fin n → Fin (d+1) → ℝ) (hp : ∀ i, p i 0=1) :
    SupportLabel p ≃o ActualCoordinateFace p where
  toFun S := ⟨labelledHull p S.1,
    strictSupport_exposed_hull (Classical.choose_spec S.2.2) S.2.1,by
      obtain ⟨i,hi⟩ := S.2.1
      exact ⟨p i,subset_convexHull ℝ _ ⟨i,hi,rfl⟩⟩⟩
  invFun F := ⟨faceLabels p F.1,faceLabels_nonempty p F.2.1 F.2.2,
    exposed_face_strictSupport p hp F.2.1 F.2.2⟩
  left_inv S := by
    apply Subtype.ext
    ext i
    simpa [faceLabels] using
      strictSupport_label_exact (Classical.choose_spec S.2.2) S.2.1 i
  right_inv F := by
    apply Subtype.ext
    exact (exposed_face_eq_labelledHull p F.2.1).symm
  map_rel_iff' := by
    intro S T
    change labelledHull p S.1 ⊆ labelledHull p T.1 ↔ S.1 ⊆ T.1
    constructor
    · intro h i hi
      apply (strictSupport_label_exact (Classical.choose_spec T.2.2) T.2.1 i).mp
      exact h (subset_convexHull ℝ _ ⟨i,hi,rfl⟩)
    · intro h
      exact convexHull_mono (Set.image_mono h)

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart5

section BundlePart6
/- Source: Papers/RationalityTenAffineFaceTransport.lean -/






@[expose] public section

noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.ChirotopeDensity

theorem affine_value_decomposition {r s : ℕ}
    (f : (Fin r → ℝ) →ᵃ[ℝ] (Fin s → ℝ)) (x : Fin r → ℝ) :
    f x=f.linear x+f 0 := by
  simpa using f.map_vadd 0 x

/-- An affine embedding with a linear left inverse carries actual
exposed faces to actual exposed faces. -/
theorem affine_image_isExposed {r s : ℕ}
    (f : (Fin r → ℝ) →ᵃ[ℝ] (Fin s → ℝ))
    (g : (Fin s → ℝ) →ₗ[ℝ] (Fin r → ℝ))
    (hgf : ∀ x, g (f x)=x)
    {A B : Set (Fin r → ℝ)} (hB : IsExposed ℝ A B) :
    IsExposed ℝ (f '' A) (f '' B) := by
  intro hne
  obtain ⟨z,x,hx,rfl⟩ := hne
  obtain ⟨l,hl⟩ := hB ⟨x,hx⟩
  let k : (Fin s → ℝ) →L[ℝ] ℝ := l.comp g.toContinuousLinearMap
  have hk (x : Fin r → ℝ) : k (f x)=l x := by
    change l (g (f x))=l x
    rw [hgf]
  refine ⟨k,?_⟩
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    rw [hl] at hx
    refine ⟨⟨x,hx.1,rfl⟩,?_⟩
    rintro _ ⟨y,hy,rfl⟩
    rw [hk,hk]
    exact hx.2 y hy
  · rintro ⟨⟨x,hx,rfl⟩,hm⟩
    refine ⟨x,?_,rfl⟩
    rw [hl]
    refine ⟨hx,?_⟩
    intro y hy
    have hh := hm (f y) ⟨y,hy,rfl⟩
    rwa [hk,hk] at hh

/-- Pulling back an exposed face along an affine map only requires the
linear part of its exposing functional; the constant term cancels in
every comparison. -/
theorem affine_preimage_isExposed {r s : ℕ}
    (f : (Fin r → ℝ) →ᵃ[ℝ] (Fin s → ℝ))
    {A : Set (Fin r → ℝ)} {B : Set (Fin s → ℝ)}
    (hB : IsExposed ℝ (f '' A) B) :
    IsExposed ℝ A (A ∩ f ⁻¹' B) := by
  intro hne
  obtain ⟨x,hxA,hxB⟩ := hne
  obtain ⟨l,hl⟩ := hB ⟨f x,hxB⟩
  let k : (Fin r → ℝ) →L[ℝ] ℝ :=
    l.comp f.linear.toContinuousLinearMap
  have hk (y : Fin r → ℝ) : l (f y)=k y+l (f 0) := by
    rw [affine_value_decomposition,map_add]
    rfl
  refine ⟨k,?_⟩
  ext y
  constructor
  · rintro ⟨hyA,hyB⟩
    rw [hl] at hyB
    refine ⟨hyA,?_⟩
    intro z hz
    have hh := hyB.2 (f z) ⟨z,hz,rfl⟩
    rw [hk z, hk y] at hh
    linarith
  · rintro ⟨hyA,hymax⟩
    refine ⟨hyA,?_⟩
    rw [hl]
    refine ⟨⟨y,hyA,rfl⟩,?_⟩
    rintro _ ⟨z,hz,rfl⟩
    rw [hk z, hk y]
    linarith [hymax z hz]

theorem affine_image_coordinateHull {n r s : ℕ}
    (p : Fin n → Fin r → ℝ)
    (f : (Fin r → ℝ) →ᵃ[ℝ] (Fin s → ℝ)) :
    f '' coordinateHull p=coordinateHull (fun i => f (p i)) := by
  change f '' convexHull ℝ (Set.range p)=
    convexHull ℝ (Set.range (fun i => f (p i)))
  rw [f.image_convexHull]
  congr 1
  ext y
  constructor
  · rintro ⟨x,⟨i,rfl⟩,rfl⟩
    exact ⟨i,rfl⟩
  · rintro ⟨i,rfl⟩
    exact ⟨p i,⟨i,rfl⟩,rfl⟩

/-- A genuine face-order isomorphism induced by an affine embedding,
rather than a definition in terms of incidence certificates. -/
def affineLeftInverseFaceOrderIso {n r s : ℕ}
    (p : Fin n → Fin r → ℝ)
    (f : (Fin r → ℝ) →ᵃ[ℝ] (Fin s → ℝ))
    (g : (Fin s → ℝ) →ₗ[ℝ] (Fin r → ℝ))
    (hgf : ∀ x, g (f x)=x) :
    ActualCoordinateFace p ≃o ActualCoordinateFace (fun i => f (p i)) where
  toFun F := ⟨f '' F.1,by
    rw [← affine_image_coordinateHull p f]
    exact affine_image_isExposed f g hgf F.2.1,
    F.2.2.image f⟩
  invFun F := ⟨coordinateHull p ∩ f ⁻¹' F.1,by
    apply affine_preimage_isExposed f
    rw [affine_image_coordinateHull p f]
    exact F.2.1,by
    obtain ⟨y,hy⟩ := F.2.2
    have hybody := F.2.1.subset hy
    rw [← affine_image_coordinateHull p f] at hybody
    obtain ⟨x,hx,rfl⟩ := hybody
    exact ⟨x,hx,hy⟩⟩
  left_inv F := by
    apply Subtype.ext
    ext x
    constructor
    · rintro ⟨_,y,hy,heq⟩
      have hxy : y=x := by
        have hh := congrArg g heq
        simpa only [hgf] using hh
      simpa only [hxy] using hy
    · intro hx
      exact ⟨F.2.1.subset hx,x,hx,rfl⟩
  right_inv F := by
    apply Subtype.ext
    ext y
    constructor
    · rintro ⟨x,⟨_,hx⟩,rfl⟩
      exact hx
    · intro hy
      have hybody := F.2.1.subset hy
      rw [← affine_image_coordinateHull p f] at hybody
      obtain ⟨x,hx,rfl⟩ := hybody
      exact ⟨x,⟨hx,hy⟩,rfl⟩
  map_rel_iff' := by
    intro F G
    change f '' F.1 ⊆ f '' G.1 ↔ F.1⊆G.1
    constructor
    · intro h x hx
      obtain ⟨y,hy,heq⟩ := h ⟨x,hx,rfl⟩
      have hxy : y=x := by
        have hh := congrArg g heq
        simpa only [hgf] using hh
      simpa only [hxy] using hy
    · exact Set.image_mono

theorem affineLeftInverseFaceOrderIso_labels {n r s : ℕ}
    (p : Fin n → Fin r → ℝ)
    (f : (Fin r → ℝ) →ᵃ[ℝ] (Fin s → ℝ))
    (g : (Fin s → ℝ) →ₗ[ℝ] (Fin r → ℝ))
    (hgf : ∀ x, g (f x)=x) (F : ActualCoordinateFace p) :
    faceLabels (fun i => f (p i))
      ((affineLeftInverseFaceOrderIso p f g hgf) F).1 =
      faceLabels p F.1 := by
  classical
  ext i
  simp only [faceLabels,Finset.mem_filter,Finset.mem_univ,true_and]
  change f (p i)∈f '' F.1 ↔ p i∈F.1
  constructor
  · rintro ⟨x,hx,heq⟩
    have hxi : x=p i := by
      have hh := congrArg g heq
      simpa only [hgf] using hh
    simpa only [hxi] using hx
  · intro hi
    exact ⟨p i,hi,rfl⟩

def homogeneousLinear (d : ℕ) :
    (Fin d → ℝ) →ₗ[ℝ] (Fin (d+1) → ℝ) where
  toFun x := Fin.cons 0 x
  map_add' x y := by
    ext j
    refine Fin.cases ?_ ?_ j
    · simp
    · intro k
      simp
  map_smul' a x := by
    ext j
    refine Fin.cases ?_ ?_ j
    · simp
    · intro k
      simp

def homogeneousAffine (d : ℕ) :
    (Fin d → ℝ) →ᵃ[ℝ] (Fin (d+1) → ℝ) where
  toFun x := Fin.cons 1 x
  linear := homogeneousLinear d
  map_vadd' x v := by
    ext j
    refine Fin.cases ?_ ?_ j
    · simp [homogeneousLinear]
    · intro k
      simp [homogeneousLinear]

def ordinaryProjection (d : ℕ) :
    (Fin (d+1) → ℝ) →ₗ[ℝ] (Fin d → ℝ) where
  toFun x j := x j.succ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem ordinaryProjection_homogeneousAffine (d : ℕ) (x : Fin d → ℝ) :
    ordinaryProjection d (homogeneousAffine d x)=x := by
  ext j
  rfl

theorem homogeneousAffine_ordinaryProjection (d : ℕ)
    (x : Fin (d+1) → ℝ) (hx : x 0=1) :
    homogeneousAffine d (ordinaryProjection d x)=x := by
  ext j
  refine Fin.cases ?_ ?_ j
  · exact hx.symm
  · intro k
    rfl

def homogeneousPoints {n d : ℕ} (p : Fin n → Fin d → ℝ) :
    Fin n → Fin (d+1) → ℝ :=
  fun i => homogeneousAffine d (p i)

@[simp]
theorem homogeneousPoints_first {n d : ℕ}
    (p : Fin n → Fin d → ℝ) (i : Fin n) :
    homogeneousPoints p i 0=1 := rfl

def ordinaryHomogeneousFaceOrderIso {n d : ℕ}
    (p : Fin n → Fin d → ℝ) :
    ActualCoordinateFace p ≃o ActualCoordinateFace (homogeneousPoints p) :=
  affineLeftInverseFaceOrderIso p (homogeneousAffine d) (ordinaryProjection d)
    (ordinaryProjection_homogeneousAffine d)

theorem ordinaryHomogeneousFaceOrderIso_labels {n d : ℕ}
    (p : Fin n → Fin d → ℝ) (F : ActualCoordinateFace p) :
    faceLabels (homogeneousPoints p) (ordinaryHomogeneousFaceOrderIso p F).1=
      faceLabels p F.1 :=
  affineLeftInverseFaceOrderIso_labels p (homogeneousAffine d) (ordinaryProjection d)
    (ordinaryProjection_homogeneousAffine d) F

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart6

section BundlePart7
/- Source: Papers/RationalityTenFacetExtension.lean -/








@[expose] public section

noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.ChirotopeDensity

def supportZeros {n r : ℕ} (p : Fin n → Fin r → ℝ)
    (a : Fin r → ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => a ⬝ᵥ p i=0)

theorem strictSupport_supportZeros {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (a : Fin r → ℝ)
    (ha : ∀ i, 0≤a ⬝ᵥ p i) :
    StrictSupport p (supportZeros p a) a := by
  classical
  constructor
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · intro i hi
    rcases lt_or_eq_of_le (ha i) with hp|hz
    · exact hp
    · exact False.elim (hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz.symm⟩))

theorem normal_eq_zero_of_spanning_annihilator {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (hp : Spans p)
    (a : Fin r → ℝ) (ha : ∀ i, a ⬝ᵥ p i=0) : a=0 := by
  have hle : Submodule.span ℝ (Set.range p) ≤ (dotLinear a).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact ha i
  rw [hp] at hle
  have haa : a ⬝ᵥ a=0 := hle (Submodule.mem_top : a∈(⊤ : Submodule ℝ _))
  exact dotProduct_self_eq_zero.mp haa

theorem exists_nonzero_subset_annihilator {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (S : Finset (Fin n))
    (hr : subsetRank p S<r) :
    ∃ a : Fin r → ℝ, a≠0 ∧ ∀ i∈S, a ⬝ᵥ p i=0 := by
  classical
  let A := maskRows p S
  have hdim : A.rank + finrank ℝ A.mulVecLin.ker=r := by
    simpa [Matrix.rank] using A.mulVecLin.finrank_range_add_finrank_ker
  have hA : A.rank=subsetRank p S := maskRows_rank p S
  have hker : A.mulVecLin.ker≠⊥ := by
    intro hbot
    have hz : finrank ℝ A.mulVecLin.ker=0 := by rw [hbot]; simp
    omega
  obtain ⟨a,ha,hane⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨a,hane,(maskRows_mulVec_zero_iff p S a).mp ha⟩

theorem subsetRank_add_one_le_of_annihilator {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (S : Finset (Fin n))
    (a : Fin r → ℝ) (ha : a≠0) (hz : ∀ i∈S, a ⬝ᵥ p i=0) :
    subsetRank p S+1≤r := by
  let A := maskRows p S
  have hamem : a∈A.mulVecLin.ker := (maskRows_mulVec_zero_iff p S a).mpr hz
  have hker : A.mulVecLin.ker≠⊥ := by
    intro h
    rw [h] at hamem
    exact ha hamem
  have hk : finrank ℝ A.mulVecLin.ker≠0 :=
    fun h => hker (Submodule.finrank_eq_zero.mp h)
  have hdim : A.rank+finrank ℝ A.mulVecLin.ker=r := by
    simpa [Matrix.rank] using A.mulVecLin.finrank_range_add_finrank_ker
  have hA : A.rank=subsetRank p S := maskRows_rank p S
  omega

theorem subsetRank_insert_le {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (S : Finset (Fin n)) (v : Fin n) :
    subsetRank p (insert v S)≤subsetRank p S+1 := by
  classical
  have he : p '' (↑(insert v S) : Set (Fin n)) =
      insert (p v) (p '' (↑S : Set (Fin n))) := by simp
  change finrank ℝ (Submodule.span ℝ (p '' (↑(insert v S) : Set (Fin n)))) ≤ _
  rw [he,Submodule.span_insert]
  have h₁ := Submodule.finrank_add_le_finrank_add_finrank
    (ℝ ∙ p v) (Submodule.span ℝ (p '' (↑S : Set (Fin n))))
  have h₂ : finrank ℝ (ℝ ∙ p v)≤1 := by
    simpa using (finrank_span_le_card (R := ℝ) ({p v} : Set (Fin r → ℝ)))
  change _ ≤ subsetRank p S+1
  change _ ≤ finrank ℝ (Submodule.span ℝ (p '' (↑S : Set (Fin n))))+1
  omega

/-- Move a support normal to the first new zero while keeping a prescribed
outside point strictly positive. This is the finite-dimensional support
extension step, with every pivot denominator explicitly positive. -/
theorem support_extension_step {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (hp : Spans p)
    (S : Finset (Fin n)) (a : Fin r → ℝ) (ha : StrictSupport p S a)
    (v : Fin n) (hv : v∉S) (hr : subsetRank p S+1<r) :
    ∃ T : Finset (Fin n), S ⊂ T ∧ v∉T ∧ ∃ a', StrictSupport p T a' := by
  classical
  have hri : subsetRank p (insert v S)<r :=
    (subsetRank_insert_le p S v).trans_lt hr
  obtain ⟨b,hb,hbz⟩ := exists_nonzero_subset_annihilator p (insert v S) hri
  have hex : ∃ j, b ⬝ᵥ p j≠0 := by
    by_contra h
    push_neg at h
    exact hb (normal_eq_zero_of_spanning_annihilator p hp b h)
  obtain ⟨j,hj⟩ := hex
  have hchoice : ∃ c : Fin r → ℝ,
      (∀ i∈insert v S, c ⬝ᵥ p i=0) ∧ ∃ j, 0<c ⬝ᵥ p j := by
    by_cases hpos : 0<b ⬝ᵥ p j
    · exact ⟨b,hbz,j,hpos⟩
    · refine ⟨-b,?_,j,?_⟩
      · intro i hi
        simp [neg_dotProduct,hbz i hi]
      · rw [neg_dotProduct]
        have hle : b ⬝ᵥ p j≤0 := le_of_not_gt hpos
        have hlt : b ⬝ᵥ p j<0 := by
          rcases lt_or_eq_of_le hle with hh|hh
          · exact hh
          · exact False.elim (hj hh)
        linarith
  obtain ⟨c,hcz,hcpos⟩ := hchoice
  let D : Finset (Fin n) := Finset.univ.filter (fun i => 0<c ⬝ᵥ p i)
  have hD : D.Nonempty := by
    obtain ⟨j,hj⟩ := hcpos
    exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩
  obtain ⟨j,hjD,hmin⟩ := D.exists_min_image
    (fun i => (a ⬝ᵥ p i)/(c ⬝ᵥ p i)) hD
  have hcj : 0<c ⬝ᵥ p j := (Finset.mem_filter.mp hjD).2
  have hjS : j∉S := by
    intro hj
    have hz := hcz j (Finset.mem_insert_of_mem hj)
    linarith
  let t : ℝ := (a ⬝ᵥ p j)/(c ⬝ᵥ p j)
  have ht : 0<t := div_pos (ha.2 j hjS) hcj
  let a' := a-t • c
  have happ (i : Fin n) : a' ⬝ᵥ p i = a ⬝ᵥ p i-t*(c ⬝ᵥ p i) := by
    simp [a',sub_dotProduct,smul_dotProduct]
  have hnonneg : ∀ i, 0≤a' ⬝ᵥ p i := by
    intro i
    rw [happ]
    have hai := ha.nonneg i
    by_cases hci : 0<c ⬝ᵥ p i
    · have hiD : i∈D := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hci⟩
      have hti : t≤(a ⬝ᵥ p i)/(c ⬝ᵥ p i) := hmin i hiD
      have hmul := (le_div_iff₀ hci).mp hti
      linarith
    · have hci' := le_of_not_gt hci
      have hmul : t*(c ⬝ᵥ p i)≤0 := mul_nonpos_of_nonneg_of_nonpos ht.le hci'
      linarith
  let T := supportZeros p a'
  have hsub : S⊆T := by
    intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [happ,ha.1 i hi,hcz i (Finset.mem_insert_of_mem hi)]
    simp
  have hjT : j∈T := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [happ]
    dsimp only [t]
    rw [div_mul_cancel₀ _ hcj.ne',sub_self]
  have hvT : v∉T := by
    intro hvT
    have hzero := (Finset.mem_filter.mp hvT).2
    rw [happ,hcz v (Finset.mem_insert_self _ _),mul_zero,sub_zero] at hzero
    exact (ne_of_gt (ha.2 v hv)) hzero
  refine ⟨T,?_,hvT,a',strictSupport_supportZeros p a' hnonneg⟩
  exact Finset.ssubset_iff_subset_ne.mpr
    ⟨hsub,fun heq => hjS (heq.symm ▸ hjT)⟩

def FacetMask {n r : ℕ} (p : Fin n → Fin r → ℝ)
    (S : Finset (Fin n)) : Prop :=
  S.Nonempty ∧ (∃ a, StrictSupport p S a) ∧ subsetRank p S+1=r

theorem FacetMask.ne_univ {n r : ℕ}
    {p : Fin n → Fin r → ℝ} (hp : Spans p)
    {S : Finset (Fin n)} (hS : FacetMask p S) :
    S≠Finset.univ := by
  intro h
  have hr := hS.2.2
  rw [h,subsetRank_univ p hp] at hr
  omega

/-- Every face avoiding a point is contained in a codimension-one face
which still avoids that point. The statement is uniform in all ranks. -/
theorem exists_facetMask_containing_avoiding {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (hp : Spans p)
    (S : Finset (Fin n)) (hS : S.Nonempty)
    (a : Fin r → ℝ) (ha : StrictSupport p S a)
    (v : Fin n) (hv : v∉S) :
    ∃ T, FacetMask p T ∧ S⊆T ∧ v∉T := by
  classical
  let C : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun T => S⊆T ∧ v∉T ∧ ∃ b, StrictSupport p T b)
  have hC : C.Nonempty :=
    ⟨S,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(show S⊆S from fun _ h => h),hv,a,ha⟩⟩
  obtain ⟨T,hT,hmax⟩ := C.exists_max_image Finset.card hC
  obtain ⟨hST,hvT,b,hb⟩ := (Finset.mem_filter.mp hT).2
  have hbne : b≠0 := by
    intro heq
    have h := hb.2 v hvT
    simp [heq] at h
  have hle := subsetRank_add_one_le_of_annihilator p T b hbne hb.1
  have heq : subsetRank p T+1=r := by
    by_contra hne
    have hlt : subsetRank p T+1<r := by omega
    obtain ⟨U,hTU,hvU,c,hc⟩ := support_extension_step p hp T b hb v hvT hlt
    have hU : U∈C := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,hST.trans hTU.subset,hvU,c,hc⟩
    have hcard := Finset.card_lt_card hTU
    have hbound := hmax U hU
    omega
  exact ⟨T,⟨hS.mono hST,⟨b,hb⟩,heq⟩,hST,hvT⟩

/-- The exact facet-intersection characterisation on labelled points.
It is proved from support geometry, not assumed as a face-lattice axiom. -/
theorem supportLabel_mem_iff_all_containing_facets {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (hp : Spans p)
    (S : Finset (Fin n)) (hS : S.Nonempty)
    (a : Fin r → ℝ) (ha : StrictSupport p S a) (i : Fin n) :
    i∈S ↔ ∀ T, FacetMask p T → S⊆T → i∈T := by
  constructor
  · intro hi T _ hST
    exact hST hi
  · intro h
    by_contra hi
    obtain ⟨T,hT,hST,hiT⟩ := exists_facetMask_containing_avoiding p hp S hS a ha i hi
    exact hiT (h T hT hST)

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart7

section BundlePart8
/- Source: Papers/RationalityTenFacetIntersection.lean -/



@[expose] public section

noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.ChirotopeDensity

def intersectionMask {n : ℕ} (L : Finset (Finset (Fin n))) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => ∀ T∈L, i∈T)

theorem strictSupport_intersectionMask {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (L : Finset (Finset (Fin n)))
    (hL : ∀ T∈L, ∃ a, StrictSupport p T a) :
    ∃ a, StrictSupport p (intersectionMask L) a := by
  classical
  let a : L → (Fin r → ℝ) := fun T => Classical.choose (hL T.1 T.2)
  have ha (T : L) : StrictSupport p T.1 (a T) := Classical.choose_spec (hL T.1 T.2)
  refine ⟨∑ T : L, a T,?_,?_⟩
  · intro i hi
    rw [sum_dotProduct]
    apply Finset.sum_eq_zero
    intro T _
    exact (ha T).1 i ((Finset.mem_filter.mp hi).2 T.1 T.2)
  · intro i hi
    have hex : ∃ T∈L, i∉T := by
      by_contra h
      push_neg at h
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
    obtain ⟨T,hT,hiT⟩ := hex
    rw [sum_dotProduct]
    exact Finset.sum_pos'
      (fun U _ => (ha U).nonneg i)
      ⟨⟨T,hT⟩,Finset.mem_univ _,(ha ⟨T,hT⟩).2 i hiT⟩

def facetMasks {n r : ℕ} (p : Fin n → Fin r → ℝ) :
    Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.filter (FacetMask p)

theorem mem_facetMasks {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (S : Finset (Fin n)) :
    S∈facetMasks p ↔ FacetMask p S := by
  classical
  simp [facetMasks]

theorem intersection_containing_facets_eq {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (hp : Spans p)
    (S : Finset (Fin n)) (hS : S.Nonempty)
    (a : Fin r → ℝ) (ha : StrictSupport p S a) :
    intersectionMask ((facetMasks p).filter (fun T => S⊆T))=S := by
  classical
  ext i
  constructor
  · intro hi
    apply (supportLabel_mem_iff_all_containing_facets p hp S hS a ha i).mpr
    intro T hT hST
    exact (Finset.mem_filter.mp hi).2 T
      (Finset.mem_filter.mpr ⟨(mem_facetMasks p T).mpr hT,hST⟩)
  · intro hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro T hT
    exact (Finset.mem_filter.mp hT).2 hi

theorem strictSupport_of_equal_facets {n r s : ℕ}
    (p : Fin n → Fin r → ℝ) (q : Fin n → Fin s → ℝ)
    (hp : Spans p) (hfacets : ∀ S, FacetMask p S ↔ FacetMask q S)
    (S : Finset (Fin n)) (hS : S.Nonempty)
    (a : Fin r → ℝ) (ha : StrictSupport p S a) :
    ∃ b, StrictSupport q S b := by
  classical
  let L := (facetMasks p).filter (fun T => S⊆T)
  have hL : ∀ T∈L, ∃ b, StrictSupport q T b := by
    intro T hT
    have hTp := (mem_facetMasks p T).mp (Finset.mem_filter.mp hT).1
    exact ((hfacets T).mp hTp).2.1
  obtain ⟨b,hb⟩ := strictSupport_intersectionMask q L hL
  have heq : intersectionMask L=S := intersection_containing_facets_eq p hp S hS a ha
  rw [heq] at hb
  exact ⟨b,hb⟩

theorem supportLabel_iff_of_equal_facets {n r s : ℕ}
    (p : Fin n → Fin r → ℝ) (q : Fin n → Fin s → ℝ)
    (hp : Spans p) (hq : Spans q)
    (hfacets : ∀ S, FacetMask p S ↔ FacetMask q S)
    (S : Finset (Fin n)) :
    (S.Nonempty ∧ ∃ a, StrictSupport p S a) ↔
      (S.Nonempty ∧ ∃ b, StrictSupport q S b) := by
  constructor
  · rintro ⟨hS,a,ha⟩
    exact ⟨hS,strictSupport_of_equal_facets p q hp hfacets S hS a ha⟩
  · rintro ⟨hS,b,hb⟩
    exact ⟨hS,strictSupport_of_equal_facets q p hq
      (fun T => (hfacets T).symm) S hS b hb⟩

def supportLabelOrderIso {n r s : ℕ}
    (p : Fin n → Fin r → ℝ) (q : Fin n → Fin s → ℝ)
    (h : ∀ S, (S.Nonempty ∧ ∃ a, StrictSupport p S a) ↔
      (S.Nonempty ∧ ∃ b, StrictSupport q S b)) :
    SupportLabel p ≃o SupportLabel q where
  toFun S := ⟨S.1,(h S.1).mp S.2⟩
  invFun S := ⟨S.1,(h S.1).mpr S.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by intro S T; rfl

/-- Equality of exact facet vertex sets gives an order isomorphism of
the actual nonempty exposed faces. All face-intersection geometry has
been proved above rather than included as an extra assumption. -/
def actualFaceOrderIso_of_equal_facets {n d e : ℕ}
    (p : Fin n → Fin (d+1) → ℝ) (q : Fin n → Fin (e+1) → ℝ)
    (hp : Spans p) (hq : Spans q)
    (hpfirst : ∀ i, p i 0=1) (hqfirst : ∀ i, q i 0=1)
    (hfacets : ∀ S, FacetMask p S ↔ FacetMask q S) :
    ActualCoordinateFace p ≃o ActualCoordinateFace q :=
  (homogeneousFaceOrderIso p hpfirst).symm.trans
    ((supportLabelOrderIso p q (supportLabel_iff_of_equal_facets p q hp hq hfacets)).trans
      (homogeneousFaceOrderIso q hqfirst))

theorem faceLabels_labelledHull {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (S : Finset (Fin n))
    (hS : S.Nonempty) (a : Fin r → ℝ) (ha : StrictSupport p S a) :
    faceLabels p (labelledHull p S)=S := by
  classical
  ext i
  simpa [faceLabels] using strictSupport_label_exact ha hS i

theorem actualFaceOrderIso_preserves_labels {n d e : ℕ}
    (p : Fin n → Fin (d+1) → ℝ) (q : Fin n → Fin (e+1) → ℝ)
    (hp : Spans p) (hq : Spans q)
    (hpfirst : ∀ i, p i 0=1) (hqfirst : ∀ i, q i 0=1)
    (hfacets : ∀ S, FacetMask p S ↔ FacetMask q S)
    (F : ActualCoordinateFace p) :
    faceLabels q
      ((actualFaceOrderIso_of_equal_facets p q hp hq hpfirst hqfirst hfacets F).1) =
        faceLabels p F.1 := by
  have hne := faceLabels_nonempty p F.2.1 F.2.2
  obtain ⟨a,ha⟩ := exposed_face_strictSupport p hpfirst F.2.1 F.2.2
  obtain ⟨b,hb⟩ := strictSupport_of_equal_facets p q hp hfacets
    (faceLabels p F.1) hne a ha
  change faceLabels q (labelledHull q (faceLabels p F.1))=faceLabels p F.1
  exact faceLabels_labelledHull q _ hne b hb

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart8

section BundlePart9
/- Source: Papers/RelationCoordinateLift.lean -/



@[expose] public section

noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.ChirotopeDensity

open PlaneRationalization

def coordinateRowChart {c n d : ℕ} {C : Matrix (Fin c) (Fin n) ℝ}
    (K : RowKernelChart C) (C' : Matrix (Fin c) (Fin n) ℝ)
    (W : Matrix (Fin d) (Fin n) ℝ) : Matrix (Fin d) (Fin n) ℝ :=
  fun i => K.eval C' (W i)

theorem coordinateRowChart_self {c n d : ℕ}
    {C : Matrix (Fin c) (Fin n) ℝ} (K : RowKernelChart C)
    (X : Matrix (Fin d) (Fin n) ℝ) (hCX : C*X.transpose=0) :
    coordinateRowChart K C X=X := by
  funext i
  apply K.self
  ext a
  exact congrFun (congrFun hCX a) i

theorem coordinateRowChart_rational {c n d : ℕ}
    {C : Matrix (Fin c) (Fin n) ℝ} (K : RowKernelChart C)
    {C' : Matrix (Fin c) (Fin n) ℝ} {W : Matrix (Fin d) (Fin n) ℝ}
    (hC' : RationalCoordinates C') (hW : RationalCoordinates W) :
    RationalCoordinates (coordinateRowChart K C' W) :=
  fun i => K.rational hC' (hW i)

theorem coordinateRowChart_relations {c n d : ℕ}
    {C : Matrix (Fin c) (Fin n) ℝ} (K : RowKernelChart C)
    (C' : Matrix (Fin c) (Fin n) ℝ) (hC' : C'.rank=C.rank)
    (hrows : LinearIndependent ℝ (fun i => C' (K.rows i)))
    (W : Matrix (Fin d) (Fin n) ℝ) :
    C'*(coordinateRowChart K C' W).transpose=0 := by
  ext a i
  exact congrFun (K.mem C' hC' hrows (W i)) a

theorem coordinateRowChart_continuousAt {c n d : ℕ}
    {C : Matrix (Fin c) (Fin n) ℝ} (K : RowKernelChart C)
    (X : Matrix (Fin d) (Fin n) ℝ) :
    ContinuousAt
      (fun z : Matrix (Fin c) (Fin n) ℝ × Matrix (Fin d) (Fin n) ℝ =>
        coordinateRowChart K z.1 z.2) (C,X) := by
  apply continuousAt_pi.mpr
  intro i
  have hparam : Continuous
      (fun z : Matrix (Fin c) (Fin n) ℝ × Matrix (Fin d) (Fin n) ℝ =>
        (z.1,z.2 i)) :=
    continuous_fst.prodMk ((continuous_apply i).comp continuous_snd)
  exact (K.continuousAt (X i)).comp_of_eq (hparam.continuousAt (x := (C, X))) rfl

/-- Exact rank and zero patterns of a relation matrix can be lifted
simultaneously with every homogeneous coordinate row in its kernel. -/
theorem rational_relation_coordinate_lift {c n d : ℕ}
    (C : Matrix (Fin c) (Fin n) ℝ) (X : Matrix (Fin d) (Fin n) ℝ)
    (hCX : C*X.transpose=0)
    (hC : C ∈ closure {C' : Matrix (Fin c) (Fin n) ℝ |
      RationalCoordinates C' ∧ C'.rank=C.rank ∧ PreservesZeroEntries C C'}) :
    (C,X) ∈ closure
      {z : Matrix (Fin c) (Fin n) ℝ × Matrix (Fin d) (Fin n) ℝ |
        RationalCoordinates z.1 ∧ RationalCoordinates z.2 ∧
        z.1.rank=C.rank ∧ PreservesZeroEntries C z.1 ∧
        z.1*z.2.transpose=0} := by
  classical
  obtain ⟨K⟩ := exists_rowKernelChart C
  let F := fun z : Matrix (Fin c) (Fin n) ℝ × Matrix (Fin d) (Fin n) ℝ =>
    (z.1,coordinateRowChart K z.1 z.2)
  have hF : ContinuousAt F (C,X) :=
    continuous_fst.continuousAt.prodMk (coordinateRowChart_continuousAt K X)
  have hbase : F (C,X)=(C,X) := by
    simp only [F,coordinateRowChart_self K X hCX]
  have hrows : ∀ᶠ z in 𝓝 (C,X),
      LinearIndependent ℝ (fun i => z.1 (K.rows i)) :=
    (show ContinuousAt
      (fun z : Matrix (Fin c) (Fin n) ℝ × Matrix (Fin d) (Fin n) ℝ => z.1) (C, X)
      from continuous_fst.continuousAt).tendsto.eventually K.eventually_independent
  let S : Set (Matrix (Fin c) (Fin n) ℝ) :=
    {C' | RationalCoordinates C' ∧ C'.rank=C.rank ∧ PreservesZeroEntries C C'}
  have hprod : (C,X) ∈ closure
      (S ×ˢ {W : Matrix (Fin d) (Fin n) ℝ | RationalCoordinates W}) := by
    rw [closure_prod_eq]
    exact ⟨hC,rationalCoordinates_dense d n X⟩
  have hcl := mem_closure_inter_of_eventually hprod hrows
  have himage : (C,X) ∈ closure
      (F '' ((S ×ˢ {W : Matrix (Fin d) (Fin n) ℝ | RationalCoordinates W}) ∩
        {z | LinearIndependent ℝ (fun i => z.1 (K.rows i))})) := by
    have hi := mem_closure_image hF hcl
    rw [hbase] at hi
    exact hi
  apply closure_mono (s := F '' _) ?_ himage
  rintro _ ⟨⟨C',W⟩,⟨⟨hC',hW⟩,hrows'⟩,rfl⟩
  exact ⟨hC'.1,coordinateRowChart_rational K hC'.1 hW,
    hC'.2.1,hC'.2.2,coordinateRowChart_relations K C' hC'.2.1 hrows' W⟩

theorem rational_relation_coordinate_lift_seven {c n d : ℕ}
    (hc : c ≤ 7) (C : Matrix (Fin c) (Fin n) ℝ)
    (X : Matrix (Fin d) (Fin n) ℝ) (hCX : C*X.transpose=0) :
    (C,X) ∈ closure
      {z : Matrix (Fin c) (Fin n) ℝ × Matrix (Fin d) (Fin n) ℝ |
        RationalCoordinates z.1 ∧ RationalCoordinates z.2 ∧
        z.1.rank=C.rank ∧ PreservesZeroEntries C z.1 ∧
        z.1*z.2.transpose=0} :=
  rational_relation_coordinate_lift C X hCX
    (rational_matrix_zero_pattern_rank_density_seven hc C)

theorem rational_relation_coordinate_lift_eight_nonfour {c n d : ℕ}
    (hc : c ≤ 8) (C : Matrix (Fin c) (Fin n) ℝ) (hr4 : C.rank ≠ 4)
    (X : Matrix (Fin d) (Fin n) ℝ) (hCX : C*X.transpose=0) :
    (C,X) ∈ closure
      {z : Matrix (Fin c) (Fin n) ℝ × Matrix (Fin d) (Fin n) ℝ |
        RationalCoordinates z.1 ∧ RationalCoordinates z.2 ∧
        z.1.rank=C.rank ∧ PreservesZeroEntries C z.1 ∧
        z.1*z.2.transpose=0} :=
  rational_relation_coordinate_lift C X hCX
    (rational_matrix_zero_pattern_rank_density_eight_nonfour hc C hr4)

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart9

section BundlePart10
/- Source: Papers/AffineRelationLift.lean -/





@[expose] public section

noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.ChirotopeDensity

open PlaneRationalization

def normalizeHomogeneousRows {n d : ℕ} (X : Matrix (Fin (d+1)) (Fin n) ℝ) :
    Matrix (Fin (d+1)) (Fin n) ℝ :=
  fun i j => X i j / X 0 j

def rescaleRelationColumns {c n d : ℕ}
    (C : Matrix (Fin c) (Fin n) ℝ) (X : Matrix (Fin (d+1)) (Fin n) ℝ) :
    Matrix (Fin c) (Fin n) ℝ :=
  fun i j => C i j * X 0 j

theorem rescaleRelationColumns_eq_mul_diagonal {c n d : ℕ}
    (C : Matrix (Fin c) (Fin n) ℝ) (X : Matrix (Fin (d+1)) (Fin n) ℝ) :
    rescaleRelationColumns C X=C*Matrix.diagonal (X 0) := by
  ext i j
  simp [rescaleRelationColumns]

theorem normalizeHomogeneousRows_first {n d : ℕ}
    (X : Matrix (Fin (d+1)) (Fin n) ℝ) (ht : ∀ j, X 0 j ≠ 0) :
    ∀ j, normalizeHomogeneousRows X 0 j=1 := by
  intro j
  simp [normalizeHomogeneousRows,ht j]

theorem normalized_relation_identity {c n d : ℕ}
    (C : Matrix (Fin c) (Fin n) ℝ) (X : Matrix (Fin (d+1)) (Fin n) ℝ)
    (ht : ∀ j, X 0 j ≠ 0) :
    rescaleRelationColumns C X * (normalizeHomogeneousRows X).transpose =
      C*X.transpose := by
  ext i a
  simp only [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j _
  change (C i j * X 0 j) * (X a j / X 0 j) = C i j * X a j
  field_simp [ht j] <;> ring

theorem rescaleRelationColumns_rank {c n d : ℕ}
    (C : Matrix (Fin c) (Fin n) ℝ) (X : Matrix (Fin (d+1)) (Fin n) ℝ)
    (ht : ∀ j, X 0 j ≠ 0) :
    (rescaleRelationColumns C X).rank=C.rank := by
  rw [rescaleRelationColumns_eq_mul_diagonal]
  apply Matrix.rank_mul_eq_left_of_isUnit_det
  rw [Matrix.det_diagonal,isUnit_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr (fun j _ => ht j)

theorem normalizeHomogeneousRows_rational {n d : ℕ}
    {X : Matrix (Fin (d+1)) (Fin n) ℝ} (hX : RationalCoordinates X) :
    RationalCoordinates (normalizeHomogeneousRows X) :=
  fun i j => (hX i j).div (hX 0 j)

theorem rescaleRelationColumns_rational {c n d : ℕ}
    {C : Matrix (Fin c) (Fin n) ℝ} {X : Matrix (Fin (d+1)) (Fin n) ℝ}
    (hC : RationalCoordinates C) (hX : RationalCoordinates X) :
    RationalCoordinates (rescaleRelationColumns C X) :=
  fun i j => (hC i j).mul (hX 0 j)

theorem normalizeHomogeneousRows_continuousAt {n d : ℕ}
    (X : Matrix (Fin (d+1)) (Fin n) ℝ) (ht : ∀ j, X 0 j ≠ 0) :
    ContinuousAt normalizeHomogeneousRows X := by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  change ContinuousAt (fun Y : Matrix (Fin (d+1)) (Fin n) ℝ => Y i j / Y 0 j) X
  exact (continuous_id.matrix_elem i j).continuousAt.div
    (continuous_id.matrix_elem 0 j).continuousAt (ht j)

theorem rescaleRelationColumns_continuous {c n d : ℕ} :
    Continuous
      (fun z : Matrix (Fin c) (Fin n) ℝ × Matrix (Fin (d+1)) (Fin n) ℝ =>
        rescaleRelationColumns z.1 z.2) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun z : Matrix (Fin c) (Fin n) ℝ × Matrix (Fin (d+1)) (Fin n) ℝ =>
    z.1 i j * z.2 0 j)
  exact (continuous_fst.matrix_elem i j).mul (continuous_snd.matrix_elem 0 j)

/-- The perturbed homogeneous coordinates can be put back into the
original affine chart without losing rationality, support zeros, relation
rank, or any exact relation equation. -/
theorem rational_affine_relation_lift {c n d : ℕ}
    (C : Matrix (Fin c) (Fin n) ℝ) (X : Matrix (Fin (d+1)) (Fin n) ℝ)
    (hfirst : ∀ j, X 0 j=1) (hCX : C*X.transpose=0)
    (hC : C ∈ closure {C' : Matrix (Fin c) (Fin n) ℝ |
      RationalCoordinates C' ∧ C'.rank=C.rank ∧ PreservesZeroEntries C C'}) :
    (C,X) ∈ closure
      {z : Matrix (Fin c) (Fin n) ℝ × Matrix (Fin (d+1)) (Fin n) ℝ |
        RationalCoordinates z.1 ∧ RationalCoordinates z.2 ∧
        z.1.rank=C.rank ∧ PreservesZeroEntries C z.1 ∧
        z.1*z.2.transpose=0 ∧ ∀ j, z.2 0 j=1} := by
  have ht : ∀ j, X 0 j ≠ 0 := by intro j; rw [hfirst]; exact one_ne_zero
  let F := fun z : Matrix (Fin c) (Fin n) ℝ × Matrix (Fin (d+1)) (Fin n) ℝ =>
    (rescaleRelationColumns z.1 z.2,normalizeHomogeneousRows z.2)
  have hF : ContinuousAt F (C,X) :=
    rescaleRelationColumns_continuous.continuousAt.prodMk
      ((normalizeHomogeneousRows_continuousAt X ht).comp_of_eq
        continuous_snd.continuousAt rfl)
  have hbase : F (C,X)=(C,X) := by
    apply Prod.ext
    · ext i j
      simp [F,rescaleRelationColumns,hfirst]
    · ext i j
      simp [F,normalizeHomogeneousRows,hfirst]
  have hpos : ∀ᶠ z in 𝓝 (C,X), ∀ j, 0 < z.2 0 j := by
    apply eventually_all.mpr
    intro j
    have hcoord : Continuous
        (fun z : Matrix (Fin c) (Fin n) ℝ × Matrix (Fin (d+1)) (Fin n) ℝ =>
          z.2 0 j) :=
      continuous_snd.matrix_elem 0 j
    exact hcoord.continuousAt.tendsto.eventually
      (isOpen_Ioi.mem_nhds (by
        change 0 < X 0 j
        rw [hfirst]
        exact zero_lt_one))
  have hcl := mem_closure_inter_of_eventually
    (rational_relation_coordinate_lift C X hCX hC) hpos
  have himage := mem_closure_image hF hcl
  rw [hbase] at himage
  apply closure_mono (s := F '' _) ?_ himage
  rintro _ ⟨⟨C',X'⟩,⟨hpair,hpos'⟩,rfl⟩
  have ht' : ∀ j, X' 0 j ≠ 0 := fun j => ne_of_gt (hpos' j)
  refine ⟨rescaleRelationColumns_rational hpair.1 hpair.2.1,
    normalizeHomogeneousRows_rational hpair.2.1,
    (rescaleRelationColumns_rank C' X' ht').trans hpair.2.2.1,?_,?_,
    normalizeHomogeneousRows_first X' ht'⟩
  · intro i j hij
    change C' i j * X' 0 j=0
    have hz : C' i j = 0 := hpair.2.2.2.1 i j hij
    rw [hz, zero_mul]
  · exact (normalized_relation_identity C' X' ht').trans hpair.2.2.2.2

theorem rational_affine_relation_lift_seven {c n d : ℕ}
    (hc : c ≤ 7) (C : Matrix (Fin c) (Fin n) ℝ)
    (X : Matrix (Fin (d+1)) (Fin n) ℝ)
    (hfirst : ∀ j, X 0 j=1) (hCX : C*X.transpose=0) :
    (C,X) ∈ closure
      {z : Matrix (Fin c) (Fin n) ℝ × Matrix (Fin (d+1)) (Fin n) ℝ |
        RationalCoordinates z.1 ∧ RationalCoordinates z.2 ∧
        z.1.rank=C.rank ∧ PreservesZeroEntries C z.1 ∧
        z.1*z.2.transpose=0 ∧ ∀ j, z.2 0 j=1} :=
  rational_affine_relation_lift C X hfirst hCX
    (rational_matrix_zero_pattern_rank_density_seven hc C)

theorem rational_affine_relation_lift_eight_nonfour {c n d : ℕ}
    (hc : c ≤ 8) (C : Matrix (Fin c) (Fin n) ℝ) (hr4 : C.rank ≠ 4)
    (X : Matrix (Fin (d+1)) (Fin n) ℝ)
    (hfirst : ∀ j, X 0 j=1) (hCX : C*X.transpose=0) :
    (C,X) ∈ closure
      {z : Matrix (Fin c) (Fin n) ℝ × Matrix (Fin (d+1)) (Fin n) ℝ |
        RationalCoordinates z.1 ∧ RationalCoordinates z.2 ∧
        z.1.rank=C.rank ∧ PreservesZeroEntries C z.1 ∧
        z.1*z.2.transpose=0 ∧ ∀ j, z.2 0 j=1} :=
  rational_affine_relation_lift C X hfirst hCX
    (rational_matrix_zero_pattern_rank_density_eight_nonfour hc C hr4)

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart10

section BundlePart11
/- Source: Papers/RationalityTenFacetReconstruction.lean -/





@[expose] public section

noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.ChirotopeDensity

open Papers.RationalityTen.PlaneRationalization (mem_closure_inter_of_eventually)

theorem eventually_spans {n r : ℕ} {p : Fin n → Fin r → ℝ}
    (hp : Spans p) : ∀ᶠ q in 𝓝 p, Spans q := by
  have hr := (spans_iff_matrix_rank p).mp hp
  filter_upwards [eventually_rank_ge (Matrix.of p)] with q hq
  apply (spans_iff_matrix_rank q).mpr
  have hlow : r ≤ (Matrix.of q).rank := by
    change (Matrix.of p).rank ≤ (Matrix.of q).rank at hq
    rw [hr] at hq
    exact hq
  exact Nat.le_antisymm (Matrix.rank_le_width (Matrix.of q)) hlow

/-- Concrete geometric output of reconstructing all selected facial
relation spaces. The face and label fields refer to ordinary exposed
subsets of the actual convex hull. -/
structure FacetReconstruction {n d : ℕ}
    (p : Fin n → Fin (d+1) → ℝ)
    (L : Finset (Finset (Fin n))) (q : Fin n → Fin (d+1) → ℝ) : Prop where
  rational : RationalCoordinates q
  affine : ∀ i, q i 0=1
  fullSpan : Spans q
  ranks : ∀ S∈L, subsetRank q S=subsetRank p S
  supports : ∀ S∈L, ∃ a, StrictSupport q S a
  faces : ∀ S∈L, IsExposed ℝ (coordinateHull q) (labelledHull q S)
  labels : ∀ S∈L, ∀ i, q i∈labelledHull q S ↔ i∈S
  noNewSupport : ∀ S, SupportingSubset q S → SupportingSubset p S

/-- The coordinate reconstruction in Appendix A.2, with all facial ranks,
strict supports, exact labels and the affine chart retained. Its input
row condition is equality with the full facial relation spaces. -/
theorem rational_facet_support_reconstruction {c n d : ℕ}
    (C : Matrix (Fin c) (Fin n) ℝ)
    (p : Fin n → Fin (d+1) → ℝ)
    (hp : Spans p) (hfirst : ∀ i, p i 0=1) (hCp : C * Matrix.of p=0)
    (L : Finset (Finset (Fin n)))
    (hL : ∀ S∈L, S.Nonempty ∧ ∃ a, StrictSupport p S a)
    (hrelations : ∀ S∈L, SpansFacetRelations C p S)
    (hC : C ∈ closure {C' : Matrix (Fin c) (Fin n) ℝ |
      RationalCoordinates C' ∧ C'.rank=C.rank ∧ PreservesZeroEntries C C'}) :
    p ∈ closure {q | FacetReconstruction p L q} := by
  classical
  let X : Matrix (Fin (d+1)) (Fin n) ℝ := (Matrix.of p).transpose
  have hXfirst : ∀ j, X 0 j=1 := hfirst
  have hCX : C*X.transpose=0 := by simpa only [X,Matrix.transpose_transpose] using hCp
  have hcl := rational_affine_relation_lift C X hXfirst hCX hC
  have hselect : ∀ S∈L, Nonempty (FacetRelationSelection C p S) :=
    fun S hS => facetRelationSelection_of_spanning C p S (hrelations S hS)
  have hmap : Continuous
      (fun z : Matrix (Fin c) (Fin n) ℝ × Matrix (Fin (d+1)) (Fin n) ℝ =>
        (z.1,z.2.transpose)) :=
    continuous_fst.prodMk continuous_snd.matrix_transpose
  have hgeom := (hmap.continuousAt (x := (C,X))).tendsto.eventually
    (selected_facet_ranks_and_supports_stable C p L hselect
      (fun S hS => (hL S hS).2))
  have hspan : ∀ᶠ z : Matrix (Fin c) (Fin n) ℝ × Matrix (Fin (d+1)) (Fin n) ℝ
      in 𝓝 (C,X), Spans z.2.transpose :=
    (continuous_snd.matrix_transpose.continuousAt (x := (C,X))).tendsto.eventually
      (eventually_spans hp)
  have hgood := hgeom.and hspan
  have hclgood := mem_closure_inter_of_eventually hcl hgood
  let F := fun z : Matrix (Fin c) (Fin n) ℝ × Matrix (Fin (d+1)) (Fin n) ℝ =>
    z.2.transpose
  have hF : Continuous F := continuous_snd.matrix_transpose
  have himage := mem_closure_image hF.continuousAt hclgood
  have hbase : F (C,X)=p := Matrix.transpose_transpose (Matrix.of p)
  rw [hbase] at himage
  apply closure_mono (s := F '' _) ?_ himage
  rintro _ ⟨z,⟨hz,hzgood⟩,rfl⟩
  rcases hz with ⟨hCR,hXR,hRank,hZero,hRel,hFirst⟩
  have hgeometry := hzgood.1 hZero hRel
  refine ⟨rationalCoordinates_transpose hXR,hFirst,hzgood.2,
    hgeometry.1,hgeometry.2.1,?_,?_,hgeometry.2.2⟩
  · intro S hS
    obtain ⟨a,ha⟩ := hgeometry.2.1 S hS
    exact strictSupport_exposed_hull ha (hL S hS).1
  · intro S hS i
    obtain ⟨a,ha⟩ := hgeometry.2.1 S hS
    exact strictSupport_label_exact ha (hL S hS).1 i

theorem rational_facet_support_reconstruction_seven {c n d : ℕ}
    (hc : c≤7) (C : Matrix (Fin c) (Fin n) ℝ)
    (p : Fin n → Fin (d+1) → ℝ)
    (hp : Spans p) (hfirst : ∀ i, p i 0=1) (hCp : C * Matrix.of p=0)
    (L : Finset (Finset (Fin n)))
    (hL : ∀ S∈L, S.Nonempty ∧ ∃ a, StrictSupport p S a)
    (hrelations : ∀ S∈L, SpansFacetRelations C p S) :
    p ∈ closure {q | FacetReconstruction p L q} :=
  rational_facet_support_reconstruction C p hp hfirst hCp L hL hrelations
    (rational_matrix_zero_pattern_rank_density_seven hc C)

theorem rational_facet_support_reconstruction_eight_nonfour {c n d : ℕ}
    (hc : c≤8) (C : Matrix (Fin c) (Fin n) ℝ) (hr4 : C.rank≠4)
    (p : Fin n → Fin (d+1) → ℝ)
    (hp : Spans p) (hfirst : ∀ i, p i 0=1) (hCp : C * Matrix.of p=0)
    (L : Finset (Finset (Fin n)))
    (hL : ∀ S∈L, S.Nonempty ∧ ∃ a, StrictSupport p S a)
    (hrelations : ∀ S∈L, SpansFacetRelations C p S) :
    p ∈ closure {q | FacetReconstruction p L q} :=
  rational_facet_support_reconstruction C p hp hfirst hCp L hL hrelations
    (rational_matrix_zero_pattern_rank_density_eight_nonfour hc C hr4)

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart11

section BundlePart12
/- Source: Papers/RationalityTenPolytopeDensity.lean -/




@[expose] public section

noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.ChirotopeDensity

theorem strictSupport_subset_same_rank_eq {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (S T : Finset (Fin n))
    (a : Fin r → ℝ) (ha : StrictSupport p S a)
    (hST : S⊆T) (hrank : subsetRank p S=subsetRank p T) : S=T := by
  have hspan : Submodule.span ℝ (p '' (↑S : Set (Fin n))) =
      Submodule.span ℝ (p '' (↑T : Set (Fin n))) :=
    Submodule.eq_of_le_of_finrank_eq
      (Submodule.span_mono (Set.image_mono hST)) hrank
  have hker : Submodule.span ℝ (p '' (↑S : Set (Fin n))) ≤ (dotLinear a).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    exact ha.1 i hi
  apply Finset.Subset.antisymm hST
  intro i hi
  have hmem : p i∈Submodule.span ℝ (p '' (↑T : Set (Fin n))) :=
    Submodule.subset_span ⟨i,hi,rfl⟩
  rw [← hspan] at hmem
  have hz : a ⬝ᵥ p i=0 := hker hmem
  by_contra hiS
  exact (ne_of_gt (ha.2 i hiS)) hz

theorem supportingSubset_contained_in_facet {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (hp : Spans p)
    (S : Finset (Fin n)) (hS : S.Nonempty) (hs : SupportingSubset p S) :
    ∃ T, FacetMask p T ∧ S⊆T := by
  classical
  obtain ⟨a,ha,hpos,hzero⟩ := hs
  have hane : a≠0 := by intro h; simp [h] at ha
  let Z := supportZeros p a
  have hSZ : S⊆Z := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hzero i hi⟩
  have hZne : Z≠Finset.univ := by
    intro hZ
    apply hane
    apply normal_eq_zero_of_spanning_annihilator p hp a
    intro i
    have hi : i∈Z := by rw [hZ]; exact Finset.mem_univ _
    exact (Finset.mem_filter.mp hi).2
  have hex : ∃ v : Fin n, v∉Z := by
    by_contra h
    push_neg at h
    apply hZne
    ext i
    simp [h i]
  obtain ⟨v,hv⟩ := hex
  obtain ⟨T,hT,hZT,_⟩ := exists_facetMask_containing_avoiding p hp Z
    (hS.mono hSZ) a (strictSupport_supportZeros p a hpos) v hv
  exact ⟨T,hT,hSZ.trans hZT⟩

theorem facetMasks_iff_of_reconstruction {n d : ℕ}
    {p q : Fin n → Fin (d+1) → ℝ}
    (hp : Spans p) (h : FacetReconstruction p (facetMasks p) q)
    (S : Finset (Fin n)) : FacetMask p S ↔ FacetMask q S := by
  classical
  constructor
  · intro hS
    have hmem := (mem_facetMasks p S).mpr hS
    refine ⟨hS.1,h.supports S hmem,?_⟩
    rw [h.ranks S hmem]
    exact hS.2.2
  · intro hS
    obtain ⟨a,ha⟩ := hS.2.1
    have hsQ : SupportingSubset q S :=
      supportingSubset_of_strictSupport ha (FacetMask.ne_univ h.fullSpan hS)
    have hsP := h.noNewSupport S hsQ
    obtain ⟨T,hT,hST⟩ := supportingSubset_contained_in_facet p hp S hS.1 hsP
    have hmem := (mem_facetMasks p T).mpr hT
    have hr : subsetRank q S=subsetRank q T := by
      have h₁ := hS.2.2
      have h₂ := hT.2.2
      have h₃ := h.ranks T hmem
      omega
    have heq := strictSupport_subset_same_rank_eq q S T a ha hST hr
    simpa only [heq] using hT

/-- Exact equivalence of the ordinary exposed-face orders, with the
vertex labels transported identically. -/
def LabelledPolytopeEquivalent {n r s : ℕ}
    (p : Fin n → Fin r → ℝ) (q : Fin n → Fin s → ℝ) : Prop :=
  ∃ e : ActualCoordinateFace p ≃o ActualCoordinateFace q,
    ∀ F, faceLabels q (e F).1=faceLabels p F.1

theorem labelledPolytopeEquivalent_of_reconstruction {n d : ℕ}
    {p q : Fin n → Fin (d+1) → ℝ}
    (hp : Spans p) (hfirst : ∀ i, p i 0=1)
    (h : FacetReconstruction p (facetMasks p) q) :
    LabelledPolytopeEquivalent p q := by
  let hf := facetMasks_iff_of_reconstruction hp h
  refine ⟨actualFaceOrderIso_of_equal_facets p q hp h.fullSpan hfirst h.affine hf,?_⟩
  exact actualFaceOrderIso_preserves_labels p q hp h.fullSpan hfirst h.affine hf

/-- A dense rational relation-matrix stratum gives dense rational
realisations of the actual labelled polytope. This includes the complete
facial-rank and support-to-face-order argument. -/
theorem rational_polytope_density_from_relation_matrix_density {c n d : ℕ}
    (C : Matrix (Fin c) (Fin n) ℝ)
    (p : Fin n → Fin (d+1) → ℝ)
    (hp : Spans p) (hfirst : ∀ i, p i 0=1) (hCp : C * Matrix.of p=0)
    (hrelations : ∀ S, FacetMask p S → SpansFacetRelations C p S)
    (hC : C ∈ closure {C' : Matrix (Fin c) (Fin n) ℝ |
      RationalCoordinates C' ∧ C'.rank=C.rank ∧ PreservesZeroEntries C C'}) :
    p ∈ closure {q | RationalCoordinates q ∧ (∀ i, q i 0=1) ∧
      Spans q ∧ LabelledPolytopeEquivalent p q} := by
  classical
  have hL : ∀ S∈facetMasks p, S.Nonempty ∧ ∃ a, StrictSupport p S a := by
    intro S hS
    have h := (mem_facetMasks p S).mp hS
    exact ⟨h.1,h.2.1⟩
  have hrel : ∀ S∈facetMasks p, SpansFacetRelations C p S :=
    fun S hS => hrelations S ((mem_facetMasks p S).mp hS)
  have hdense := rational_facet_support_reconstruction C p hp hfirst hCp
    (facetMasks p) hL hrel hC
  apply closure_mono ?_ hdense
  intro q hq
  exact ⟨hq.rational,hq.affine,hq.fullSpan,
    labelledPolytopeEquivalent_of_reconstruction hp hfirst hq⟩

/-- The complete seven-row branch of the paper's relation-space
criterion, stated for actual finite convex hulls and all real realisations.
It is a dependency of Proposition 8, not the unresolved eight-row
exceptional case or the complete ten-vertex theorem. -/
theorem rational_polytope_density_seven_relation_rows {c n d : ℕ}
    (hc : c≤7) (C : Matrix (Fin c) (Fin n) ℝ)
    (p : Fin n → Fin (d+1) → ℝ)
    (hp : Spans p) (hfirst : ∀ i, p i 0=1) (hCp : C * Matrix.of p=0)
    (hrelations : ∀ S, FacetMask p S → SpansFacetRelations C p S) :
    p ∈ closure {q | RationalCoordinates q ∧ (∀ i, q i 0=1) ∧
      Spans q ∧ LabelledPolytopeEquivalent p q} :=
  rational_polytope_density_from_relation_matrix_density C p hp hfirst hCp hrelations
    (rational_matrix_zero_pattern_rank_density_seven hc C)

theorem rational_polytope_density_eight_nonfour_relation_rows {c n d : ℕ}
    (hc : c≤8) (C : Matrix (Fin c) (Fin n) ℝ) (hr4 : C.rank≠4)
    (p : Fin n → Fin (d+1) → ℝ)
    (hp : Spans p) (hfirst : ∀ i, p i 0=1) (hCp : C * Matrix.of p=0)
    (hrelations : ∀ S, FacetMask p S → SpansFacetRelations C p S) :
    p ∈ closure {q | RationalCoordinates q ∧ (∀ i, q i 0=1) ∧
      Spans q ∧ LabelledPolytopeEquivalent p q} :=
  rational_polytope_density_from_relation_matrix_density C p hp hfirst hCp hrelations
    (rational_matrix_zero_pattern_rank_density_eight_nonfour hc C hr4)

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart12

section BundlePart13
/- Source: Papers/RationalityTenOrdinaryPolytopeDensity.lean -/





@[expose] public section

noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.ChirotopeDensity

theorem LabelledPolytopeEquivalent.symm {n r s : ℕ}
    {p : Fin n → Fin r → ℝ} {q : Fin n → Fin s → ℝ}
    (h : LabelledPolytopeEquivalent p q) :
    LabelledPolytopeEquivalent q p := by
  obtain ⟨e,he⟩ := h
  refine ⟨e.symm,?_⟩
  intro F
  have hh := he (e.symm F)
  rw [e.apply_symm_apply] at hh
  exact hh.symm

theorem LabelledPolytopeEquivalent.trans {n r s t : ℕ}
    {p : Fin n → Fin r → ℝ} {q : Fin n → Fin s → ℝ}
    {u : Fin n → Fin t → ℝ}
    (h₁ : LabelledPolytopeEquivalent p q)
    (h₂ : LabelledPolytopeEquivalent q u) :
    LabelledPolytopeEquivalent p u := by
  obtain ⟨e₁,he₁⟩ := h₁
  obtain ⟨e₂,he₂⟩ := h₂
  refine ⟨e₁.trans e₂,?_⟩
  intro F
  exact (he₂ (e₁ F)).trans (he₁ F)

theorem ordinary_homogeneous_equivalent {n d : ℕ}
    (p : Fin n → Fin d → ℝ) :
    LabelledPolytopeEquivalent p (homogeneousPoints p) :=
  ⟨ordinaryHomogeneousFaceOrderIso p,ordinaryHomogeneousFaceOrderIso_labels p⟩

theorem ordinary_equivalent_of_homogeneous {n d e : ℕ}
    (p : Fin n → Fin d → ℝ) (q : Fin n → Fin e → ℝ)
    (h : LabelledPolytopeEquivalent (homogeneousPoints p) (homogeneousPoints q)) :
    LabelledPolytopeEquivalent p q :=
  (ordinary_homogeneous_equivalent p).trans
    (h.trans (ordinary_homogeneous_equivalent q).symm)

def ordinaryPoints {n d : ℕ} (p : Fin n → Fin (d+1) → ℝ) :
    Fin n → Fin d → ℝ :=
  fun i => ordinaryProjection d (p i)

theorem continuous_ordinaryPoints (n d : ℕ) :
    Continuous (ordinaryPoints : (Fin n → Fin (d+1) → ℝ) →
      (Fin n → Fin d → ℝ)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (continuous_apply j.succ).comp (continuous_apply i)

@[simp]
theorem ordinaryPoints_homogeneousPoints {n d : ℕ}
    (p : Fin n → Fin d → ℝ) :
    ordinaryPoints (homogeneousPoints p)=p := by
  funext i
  exact ordinaryProjection_homogeneousAffine d (p i)

theorem homogeneousPoints_ordinaryPoints {n d : ℕ}
    (p : Fin n → Fin (d+1) → ℝ) (hp : ∀ i, p i 0=1) :
    homogeneousPoints (ordinaryPoints p)=p := by
  funext i
  exact homogeneousAffine_ordinaryProjection d (p i) (hp i)

theorem rationalCoordinates_ordinaryPoints {n d : ℕ}
    {p : Fin n → Fin (d+1) → ℝ} (hp : RationalCoordinates p) :
    RationalCoordinates (ordinaryPoints p) := by
  intro i j
  exact hp i j.succ

/-- Passing to the ordinary affine chart preserves the topology,
rational coordinates and the actual labelled face-order equivalence. -/
theorem ordinary_density_of_homogeneous_density {n d : ℕ}
    (p : Fin n → Fin d → ℝ)
    (h : homogeneousPoints p ∈ closure
      {Q : Fin n → Fin (d+1) → ℝ |
        RationalCoordinates Q ∧ (∀ i, Q i 0=1) ∧
        Spans Q ∧ LabelledPolytopeEquivalent (homogeneousPoints p) Q}) :
    p ∈ closure {q : Fin n → Fin d → ℝ |
      RationalCoordinates q ∧ Spans (homogeneousPoints q) ∧
      LabelledPolytopeEquivalent p q} := by
  let S := {Q : Fin n → Fin (d+1) → ℝ |
    RationalCoordinates Q ∧ (∀ i, Q i 0=1) ∧
    Spans Q ∧ LabelledPolytopeEquivalent (homogeneousPoints p) Q}
  have hcl : p∈closure (ordinaryPoints '' S) := by
    apply image_closure_subset_closure_image (continuous_ordinaryPoints n d)
    exact ⟨homogeneousPoints p,h,ordinaryPoints_homogeneousPoints p⟩
  apply closure_mono ?_ hcl
  rintro q ⟨Q,hQ,rfl⟩
  have heq := homogeneousPoints_ordinaryPoints Q hQ.2.1
  refine ⟨rationalCoordinates_ordinaryPoints hQ.1,?_,?_⟩
  · rw [heq]
    exact hQ.2.2.1
  · apply ordinary_equivalent_of_homogeneous p (ordinaryPoints Q)
    rw [heq]
    exact hQ.2.2.2

/-- The seven-row relation-space branch, with its conclusion stated
directly for the original affine point coordinates and actual exposed
faces of their convex hull. -/
theorem rational_ordinary_polytope_density_seven_relation_rows {c n d : ℕ}
    (hc : c≤7) (C : Matrix (Fin c) (Fin n) ℝ)
    (p : Fin n → Fin d → ℝ)
    (hp : Spans (homogeneousPoints p)) (hCp : C * Matrix.of (homogeneousPoints p) = 0)
    (hrelations : ∀ S, FacetMask (homogeneousPoints p) S →
      SpansFacetRelations C (homogeneousPoints p) S) :
    p ∈ closure {q : Fin n → Fin d → ℝ |
      RationalCoordinates q ∧ Spans (homogeneousPoints q) ∧
      LabelledPolytopeEquivalent p q} :=
  ordinary_density_of_homogeneous_density p
    (rational_polytope_density_seven_relation_rows hc C (homogeneousPoints p)
      hp (homogeneousPoints_first p) hCp hrelations)

theorem rational_ordinary_polytope_density_eight_nonfour_relation_rows {c n d : ℕ}
    (hc : c≤8) (C : Matrix (Fin c) (Fin n) ℝ) (hr4 : C.rank≠4)
    (p : Fin n → Fin d → ℝ)
    (hp : Spans (homogeneousPoints p)) (hCp : C * Matrix.of (homogeneousPoints p) = 0)
    (hrelations : ∀ S, FacetMask (homogeneousPoints p) S →
      SpansFacetRelations C (homogeneousPoints p) S) :
    p ∈ closure {q : Fin n → Fin d → ℝ |
      RationalCoordinates q ∧ Spans (homogeneousPoints q) ∧
      LabelledPolytopeEquivalent p q} :=
  ordinary_density_of_homogeneous_density p
    (rational_polytope_density_eight_nonfour_relation_rows hc C hr4
      (homogeneousPoints p) hp (homogeneousPoints_first p) hCp hrelations)

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart13
