module
public import Papers.RelativeKernelMatrixDensity

@[expose] public section
noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.FixedCoordinateFlagDensity

open ChirotopeDensity PlaneRationalization

/-- Independent column constraints can be lifted over the same external
parameter. This is used when different vertex groups belong to different
facet kernels; a shared coordinate-axis group gets its own fixed kernel.
Any finite open minor conditions may subsequently be intersected with the
closure statement. -/
theorem relative_column_kernel_density {X : Type*} [TopologicalSpace X]
    {m p n : ℕ} (A : X → Fin n → Matrix (Fin m) (Fin p) ℝ) (x : X)
    (hA : ∀ j, ContinuousAt (fun y => A y j) x)
    (S : Set X) (hx : x ∈ closure S)
    (hRat : ∀ y ∈ S, ∀ j, RationalCoordinates (A y j))
    (hRanks : ∀ y ∈ S, ∀ j, SameSubsetRanks (A x j).col (A y j).col)
    (C : Matrix (Fin p) (Fin n) ℝ)
    (hAC : ∀ j, (A x j).mulVec (C.col j) = 0) :
    (x, C) ∈ closure {z : X × Matrix (Fin p) (Fin n) ℝ |
      z.1 ∈ S ∧ RationalCoordinates z.2 ∧
      (∀ j, (A z.1 j).mulVec (z.2.col j) = 0) ∧ PreservesZeroEntries C z.2} := by
  classical
  let Z : Fin n → Finset (Fin p) :=
    fun j => Finset.univ.filter (fun i => C i j = 0)
  let K : (j : Fin n) → RowKernelChart (withZeros (A x j) (Z j)) :=
    fun j => Classical.choice (exists_rowKernelChart _)
  let W : Fin n → Fin p → ℝ := fun j i => C i j
  have hW : ∀ j, (withZeros (A x j) (Z j)).mulVec (W j) = 0 := by
    intro j
    apply (withZeros_mulVec_eq_zero _ _ _).mpr
    exact ⟨hAC j, fun i hi => (Finset.mem_filter.mp hi).2⟩
  let G : X × (Fin n → Fin p → ℝ) → Matrix (Fin p) (Fin n) ℝ :=
    fun z i j => (K j).eval (withZeros (A z.1 j) (Z j)) (z.2 j) i
  have hGbase : G (x, W) = C := by
    ext i j
    exact congrFun ((K j).self (W j) (hW j)) i
  have hG : ContinuousAt G (x, W) := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    have hp : ContinuousAt
        (fun z : X × (Fin n → Fin p → ℝ) =>
          (withZeros (A z.1 j) (Z j), z.2 j)) (x, W) := by
      simpa only [Function.comp_def] using
        (((withZeros_continuous (Z j)).continuousAt.comp
          ((hA j).comp (continuous_fst.continuousAt (x := (x, W))))).prodMk
          (((continuous_apply j).comp continuous_snd).continuousAt))
    exact (continuous_apply i).continuousAt.comp
      (((K j).continuousAt (W j)).comp_of_eq hp rfl)
  have hrows : ∀ᶠ z in 𝓝 (x, W), ∀ j,
      LinearIndependent ℝ (fun i => withZeros (A z.1 j) (Z j) ((K j).rows i)) := by
    apply eventually_all.mpr
    intro j
    have hp := (withZeros_continuous (Z j)).continuousAt.comp
      ((hA j).comp continuous_fst.continuousAt (x := (x, W)))
    exact hp.tendsto.eventually (K j).eventually_independent
  let Good : Set (X × (Fin n → Fin p → ℝ)) := {z |
      ∀ j, LinearIndependent ℝ (fun i => withZeros (A z.1 j) (Z j) ((K j).rows i))}
  have hprod : (x, W) ∈ closure
      (S ×ˢ {W' : Fin n → Fin p → ℝ | RationalCoordinates W'}) := by
    rw [closure_prod_eq]
    exact ⟨hx, rationalCoordinates_dense n p W⟩
  let F : X × (Fin n → Fin p → ℝ) → X × Matrix (Fin p) (Fin n) ℝ :=
    fun z => (z.1, G z)
  have hF : ContinuousAt F (x, W) := continuous_fst.continuousAt.prodMk hG
  have hcl := mem_closure_image hF (mem_closure_inter_of_eventually hprod hrows)
  have hFbase : F (x, W) = (x, C) := congrArg (fun t => (x, t)) hGbase
  rw [hFbase] at hcl
  apply closure_mono (s := F ''
    ((S ×ˢ {W' : Fin n → Fin p → ℝ | RationalCoordinates W'}) ∩ Good)) ?_ hcl
  rintro _ ⟨⟨y, W'⟩, ⟨⟨hy, hW'⟩, hgood⟩, rfl⟩
  have hmem : ∀ j, (withZeros (A y j) (Z j)).mulVec ((G (y, W')).col j) = 0 := by
    intro j
    exact (K j).mem (withZeros (A y j) (Z j))
      (withZeros_same_rank _ _ _ (hRanks y hy j (Z j)ᶜ)).symm (hgood j) (W' j)
  refine ⟨hy, ?_, ?_, ?_⟩
  · intro i j
    exact (K j).rational (withZeros_rational _ _ (hRat y hy j)) (hW' j) i
  · intro j
    exact ((withZeros_mulVec_eq_zero _ _ _).mp (hmem j)).1
  · intro i j hij
    exact ((withZeros_mulVec_eq_zero _ _ _).mp (hmem j)).2 i
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩)

#print axioms relative_column_kernel_density

end Papers.RationalityTen.FixedCoordinateFlagDensity
