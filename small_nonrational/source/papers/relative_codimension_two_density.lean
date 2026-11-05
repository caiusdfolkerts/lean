module
public import Papers.VaryingCoordinateFlagDensity
public import Papers.RelativeKernelMatrixDensity

@[expose] public section
noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.FixedCoordinateFlagDensity

open ChirotopeDensity PlaneRationalization

/-- The two-normal case of the relative flag lemma, followed by the exact
kernel reconstruction of every prescribed column. The external parameter and
all zeros and ranks are retained. This is the only proper intermediate rank
beyond lines in an ambient coordinate space of dimension at most four. -/
theorem relative_codimension_two_density {X : Type*} [TopologicalSpace X]
    {p n : ℕ} (a : X → Fin p → ℝ) (x : X) (ha : ContinuousAt a x)
    (S : Set X) (hx : x ∈ closure S)
    (hRat : ∀ y ∈ S, ∀ i, RatScalar (a y i))
    (hzero : ∀ y ∈ S, ∀ i, a x i = 0 → a y i = 0)
    (b : Fin p → ℝ) (hSpan : Spans (pair (a x) b))
    (C : Matrix (Fin p) (Fin n) ℝ)
    (hAC : (Matrix.transpose (pair (a x) b)) * C = 0)
    (hExact : C.mulVecLin.range = (Matrix.transpose (pair (a x) b)).mulVecLin.ker) :
    (x, C) ∈ closure {z : X × Matrix (Fin p) (Fin n) ℝ |
      z.1 ∈ S ∧ RationalCoordinates z.2 ∧
      (∀ j, a z.1 ⬝ᵥ z.2.col j = 0) ∧ z.2.rank = C.rank ∧
      PreservesZeroEntries C z.2} := by
  let T : Set (X × (Fin p → ℝ)) := {z | z.1 ∈ S ∧
    (∀ i, RatScalar (z.2 i)) ∧ SameChirotope (pair (a x) b) (pair (a z.1) z.2)}
  have hT : (x, b) ∈ closure T :=
    varying_first_chirotope_density a x ha S hx hRat hzero b
  let A : X × (Fin p → ℝ) → Matrix (Fin 2) (Fin p) ℝ :=
    fun z => (Matrix.transpose (pair (a z.1) z.2))
  have hA : ContinuousAt A (x, b) := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    fin_cases i
    · change ContinuousAt (fun z : X × (Fin p → ℝ) => a z.1 j) (x, b)
      simpa only [Function.comp_def] using
        ((continuous_apply j).continuousAt.comp (ha.comp continuous_fst.continuousAt))
    · change ContinuousAt (fun z : X × (Fin p → ℝ) => z.2 j) (x, b)
      exact ((continuous_apply j).comp continuous_snd).continuousAt
  have hARat : ∀ y ∈ T, RationalCoordinates (A y) := by
    intro y hy i j
    fin_cases i
    · exact hRat y.1 hy.1 j
    · exact hy.2.1 j
  have hARanks : ∀ y ∈ T, SameSubsetRanks (A (x, b)).col (A y).col := by
    intro y hy
    exact hy.2.2.sameSubsetRanks hSpan
  have hk := relative_kernel_matrix_density A (x, b) hA T hT hARat hARanks
    C hAC hExact
  let F : (X × (Fin p → ℝ)) × Matrix (Fin p) (Fin n) ℝ →
      X × Matrix (Fin p) (Fin n) ℝ := fun z => (z.1.1, z.2)
  have hF : Continuous F :=
    (continuous_fst.comp continuous_fst).prodMk continuous_snd
  have himage := mem_closure_image hF.continuousAt hk
  change (x, C) ∈ closure (F '' _) at himage
  apply closure_mono (s := F '' _) ?_ himage
  rintro _ ⟨⟨⟨y, b'⟩, C'⟩, h, rfl⟩
  refine ⟨h.1.1, h.2.1, ?_, h.2.2.2.1, h.2.2.2.2⟩
  intro j
  have hj := congrFun (congrFun h.2.2.1 0) j
  change a y ⬝ᵥ C'.col j = 0
  change a y ⬝ᵥ C'.col j = 0 at hj
  exact hj

#print axioms relative_codimension_two_density

end Papers.RationalityTen.FixedCoordinateFlagDensity
