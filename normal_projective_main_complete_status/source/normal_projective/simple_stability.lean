module
public import normal_projective.uniform_bound
public import normal_projective.simple_vertices
public import Mathlib.Topology.Instances.Matrix
/-! # Stability of all maximal tight systems for a simple polytope -/
@[expose] public section
noncomputable section
open Set Matrix Filter
open scoped Topology BigOperators
namespace NormalProjective
variable {d : ℕ} {ι : Type*} [Fintype ι]

def minorMatrix (p : HalfspaceData ι (Fin d → ℝ)) (I : Fin d ↪ ι) :
    Matrix (Fin d) (Fin d) ℝ :=
  facetCoefficientMatrix (fun j => (p.1 (I j)).toLinearMap)

def minorVertex (p : HalfspaceData ι (Fin d → ℝ)) (I : Fin d ↪ ι) : Fin d → ℝ :=
  (minorMatrix p I)⁻¹ *ᵥ (fun j => p.2 (I j))

def FeasibleMinor (p : HalfspaceData ι (Fin d → ℝ)) (I : Fin d ↪ ι) : Prop :=
  ∃ x ∈ dataRegion p, ∀ j, p.1 (I j) x = p.2 (I j)

def GoodMinor (p : HalfspaceData ι (Fin d → ℝ)) (I : Fin d ↪ ι) : Prop :=
  (minorMatrix p I).det ≠ 0 ∧
    minorVertex p I ∈ dataRegion p ∧
    ∀ i, i ∉ Set.range I → p.1 i (minorVertex p I) < p.2 i

theorem continuous_minorMatrix (I : Fin d ↪ ι) :
    Continuous (fun p : HalfspaceData ι (Fin d → ℝ) => minorMatrix p I) := by
  unfold minorMatrix facetCoefficientMatrix
  change Continuous (fun p : HalfspaceData ι (Fin d → ℝ) =>
    fun i j => p.1 (I i) (Pi.single j 1))
  fun_prop

theorem minorVertex_tight (p : HalfspaceData ι (Fin d → ℝ)) (I : Fin d ↪ ι)
    (hd : (minorMatrix p I).det ≠ 0) :
    ∀ j, p.1 (I j) (minorVertex p I) = p.2 (I j) := by
  have hh : minorMatrix p I *ᵥ minorVertex p I = fun j => p.2 (I j) := by
    rw [minorVertex, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd), Matrix.one_mulVec]
  change facetCoefficientMatrix (fun j => (p.1 (I j)).toLinearMap) *ᵥ minorVertex p I = _ at hh
  rw [facetCoefficientMatrix_mulVec] at hh
  exact congrFun hh

theorem minorVertex_eq (p : HalfspaceData ι (Fin d → ℝ)) (I : Fin d ↪ ι)
    (hd : (minorMatrix p I).det ≠ 0) {x : Fin d → ℝ}
    (hx : ∀ j, p.1 (I j) x = p.2 (I j)) :
    minorVertex p I = x :=
  tight_minor_unique (fun i => (p.1 i).toLinearMap) p.2 I hd
    (minorVertex_tight p I hd) hx

theorem continuousAt_minorVertex (p : HalfspaceData ι (Fin d → ℝ)) (I : Fin d ↪ ι)
    (hd : (minorMatrix p I).det ≠ 0) :
    ContinuousAt (fun q => minorVertex q I) p := by
  have hinv : ContinuousAt (fun q => (minorMatrix q I)⁻¹) p :=
    (continuousAt_matrix_inv _ (by
      simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hd)).comp
      (continuous_minorMatrix I).continuousAt
  have hv : Continuous (fun q : HalfspaceData ι (Fin d → ℝ) => fun j => q.2 (I j)) := by
    fun_prop
  have hm : Continuous (fun a : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) =>
      a.1 *ᵥ a.2) := continuous_fst.matrix_mulVec continuous_snd
  exact hm.continuousAt.comp (hinv.prodMk hv.continuousAt)

theorem goodMinor_of_simple_feasible
    (p : HalfspaceData ι (Fin d → ℝ))
    (hc : IsCompact (dataRegion p))
    (hs : IsSimpleHalfspace (fun i => (p.1 i).toLinearMap) p.2)
    (I : Fin d ↪ ι) (hI : FeasibleMinor p I) : GoodMinor p I := by
  obtain ⟨x, hx, hxt⟩ := hI
  obtain ⟨_, hd, hstrict⟩ := simple_feasible_minor
    (fun i => (p.1 i).toLinearMap) p.2 hc hs I hx hxt
  have heq := minorVertex_eq p I hd hxt
  exact ⟨hd, heq.symm ▸ hx, fun i hi => heq.symm ▸ hstrict i hi⟩

theorem goodMinor_eventually
    (p : HalfspaceData ι (Fin d → ℝ)) (I : Fin d ↪ ι)
    (hI : GoodMinor p I) :
    ∀ᶠ q : HalfspaceData ι (Fin d → ℝ) in 𝓝 p, GoodMinor q I := by
  classical
  have hdet : ∀ᶠ q : HalfspaceData ι (Fin d → ℝ) in 𝓝 p,
      (minorMatrix q I).det ≠ 0 :=
    (isOpen_ne_fun (continuous_minorMatrix I).matrix_det continuous_const).mem_nhds hI.1
  have hstrict : ∀ i, ∀ᶠ q : HalfspaceData ι (Fin d → ℝ) in 𝓝 p,
      i ∉ Set.range I → q.1 i (minorVertex q I) < q.2 i := by
    intro i
    by_cases hi : i ∈ Set.range I
    · exact Filter.Eventually.of_forall (fun q hni => (hni hi).elim)
    · have hc₁ : ContinuousAt (fun q : HalfspaceData ι (Fin d → ℝ) =>
          q.1 i (minorVertex q I)) p :=
        (((continuous_apply i).comp continuous_fst).continuousAt).clm_apply
          (continuousAt_minorVertex p I hI.1)
      have hc₂ : ContinuousAt (fun q : HalfspaceData ι (Fin d → ℝ) => q.2 i) p := by
        fun_prop
      filter_upwards [hc₁.eventually_lt hc₂ (hI.2.2 i hi)] with q hq
      exact fun _ => hq
  filter_upwards [hdet, Filter.eventually_all.mpr hstrict] with q hd hq
  refine ⟨hd, ?_, hq⟩
  intro i
  by_cases hi : i ∈ Set.range I
  · obtain ⟨j, rfl⟩ := hi
    exact le_of_eq (minorVertex_tight q I hd j)
  · exact (hq i hi).le

/-- All feasible maximal tight systems, including formerly singular ones, stabilize. -/
theorem normalized_data_eventually_minor_stable
    (f : ι → (Fin d → ℝ) →L[ℝ] ℝ)
    (hc : IsCompact (dataRegion (f, fun _ => 1)))
    (hs : IsSimpleHalfspace (fun i => (f i).toLinearMap) (fun _ => 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ p : HalfspaceData ι (Fin d → ℝ) in 𝓝 (f, fun _ => 1),
      dataRegion p ⊆ Metric.closedBall 0 C ∧ 0 ∈ interior (dataRegion p) ∧
      ∀ I : Fin d ↪ ι,
        (FeasibleMinor (f, fun _ => 1) I → GoodMinor p I) ∧
        (¬FeasibleMinor (f, fun _ => 1) I → ¬FeasibleMinor p I) := by
  classical
  obtain ⟨C, hC, hbounded⟩ := normalized_data_eventually_bounded f hc.isBounded
  have hI : ∀ I : Fin d ↪ ι,
      ∀ᶠ p : HalfspaceData ι (Fin d → ℝ) in 𝓝 (f, fun _ => 1),
        (FeasibleMinor (f, fun _ => 1) I → GoodMinor p I) ∧
        (¬FeasibleMinor (f, fun _ => 1) I → ¬FeasibleMinor p I) := by
    intro I
    by_cases hfeas : FeasibleMinor (f, fun _ => 1) I
    · filter_upwards [goodMinor_eventually (f, fun _ => 1) I
        (goodMinor_of_simple_feasible (f, fun _ => 1) hc hs I hfeas)] with p hp
      exact ⟨fun _ => hp, fun hno => (hno hfeas).elim⟩
    · have hclosed := compact_feasibility_isClosed (Metric.closedBall 0 C)
        (isCompact_closedBall (0 : Fin d → ℝ) C) (Set.range I)
      have hnot : (f, fun _ => 1) ∈
          {p : HalfspaceData ι (Fin d → ℝ) | ∃ x ∈ Metric.closedBall 0 C,
            x ∈ dataRegion p ∧ ∀ i ∈ Set.range I, p.1 i x = p.2 i}ᶜ := by
        rintro ⟨x, _, hx, hxt⟩
        exact hfeas ⟨x, hx, fun j => hxt (I j) ⟨j, rfl⟩⟩
      filter_upwards [hclosed.isOpen_compl.mem_nhds hnot, hbounded] with p hp hpb
      refine ⟨fun hh => (hfeas hh).elim, fun _ hnew => ?_⟩
      obtain ⟨x, hx, hxt⟩ := hnew
      exact hp ⟨x, hpb.1 hx, hx, fun i ⟨j, hij⟩ => hij ▸ hxt j⟩
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbounded, Filter.eventually_all.mpr hI] with p hp hIp
  exact ⟨hp.1, hp.2, hIp⟩

end NormalProjective

