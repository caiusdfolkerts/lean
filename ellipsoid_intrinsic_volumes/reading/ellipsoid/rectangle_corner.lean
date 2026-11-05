module

public import Ellipsoid.RectangleDescent
public import Mathlib.Data.Fintype.Card

@[expose] public section

noncomputable section

open Matrix Set Filter
open scoped BigOperators Topology

namespace EllipsoidVerification

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The lower-corner form of rectangle univalence. Its proof uses a compact
minimal counterexample and induction over faces, including all boundary
points. Diagonal stability is proved for the paper's actual Jacobian in the
analytic branch; it is not an extra hypothesis on the principal theorem. -/
theorem rectangle_corner_order
    {F : (ι → ℝ) → (ι → ℝ)} {A : (ι → ℝ) → Matrix ι ι ℝ}
    {a b : ι → ℝ} (hab : a ≤ b)
    (hF : ∀ z ∈ Icc a b, HasFDerivAt F (matrixDerivative (A z)) z)
    (hA : ∀ z ∈ Icc a b, DiagonallyStable (A z))
    {x : ι → ℝ} (hx : x ∈ Icc a b) (hFx : F x ≤ F a) : x = a := by
  classical
  induction hcard : Fintype.card ι using Nat.strong_induction_on generalizing ι with
  | h N ih =>
    by_contra hxa
    let S : Set (ι → ℝ) := Icc a b ∩ F ⁻¹' Iic (F a)
    have hcont : ContinuousOn F (Icc a b) := fun z hz =>
      (hF z hz).continuousAt.continuousWithinAt
    have hclosed : IsClosed S :=
      hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hcompact : IsCompact S := isCompact_Icc.of_isClosed_subset hclosed inter_subset_left
    have hnear := isolated_lower_corner (hF a ⟨le_rfl, hab⟩) (hA a ⟨le_rfl, hab⟩)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
    have haway {z : ι → ℝ} (hz : z ∈ S) (hz0 : z ≠ a) : ε ≤ dist z a := by
      by_contra h
      exact hz0 (hball (show z ∈ Metric.ball a ε by
        simpa only [Metric.mem_ball] using lt_of_not_ge h) hz.1.1 hz.2)
    let T : Set (ι → ℝ) := S \ Metric.ball a (ε / 2)
    have hT : IsCompact T := hcompact.diff Metric.isOpen_ball
    have hxT : x ∈ T := by
      refine ⟨⟨hx, hFx⟩, ?_⟩
      have hh := haway ⟨hx, hFx⟩ hxa
      simp only [Metric.mem_ball]
      linarith
    obtain ⟨c, hc, hmin⟩ := hT.exists_isMinOn ⟨x, hxT⟩
      (show ContinuousOn (fun z : ι → ℝ => ∑ i, z i) T by fun_prop)
    have hcS : c ∈ S := hc.1
    have hc0 : c ≠ a := by
      intro hc0
      have hh := hc.2
      simp [hc0, half_pos hε] at hh
    have hclower : ∀ i, a i < c i := by
      intro i
      by_contra hci
      have hcieq : c i = a i := le_antisymm (le_of_not_gt hci) (hcS.1.1 i)
      let s : Finset ι := Finset.univ.erase i
      have hsCard : Fintype.card s < N := by
        rw [Fintype.card_coe, ← hcard]
        exact Finset.card_erase_lt_of_mem (Finset.mem_univ i)
      have hinsert : faceInsert a s (faceRestrict s c) = c := by
        funext j
        by_cases hj : j ∈ s
        · simp [faceInsert, faceRestrict, hj]
        · have hji : j = i := by simpa [s] using hj
          subst j
          simp [faceInsert, s, hcieq]
      have hfaces := ih (Fintype.card s) hsCard (ι := s)
        (F := faceMap F a s)
        (A := fun y => (A (faceInsert a s y)).submatrix
          (fun j : s => j.val) (fun j : s => j.val))
        (a := faceRestrict s a) (b := faceRestrict s b)
        (fun j => hab j.val)
        (fun y hy => hasFDerivAt_faceMap s (hF _ (faceInsert_mem_box hab s hy)))
        (fun y hy => (hA _ (faceInsert_mem_box hab s hy)).submatrix s)
        (x := faceRestrict s c)
        (show faceRestrict s c ∈ Icc (faceRestrict s a) (faceRestrict s b) from
          ⟨fun j => hcS.1.1 j.val, fun j => hcS.1.2 j.val⟩)
        (by
          simp only [faceMap, hinsert, faceInsert_restrict_self]
          exact fun j => hcS.2 j.val)
        rfl
      apply hc0
      funext j
      by_cases hji : j = i
      · simpa [hji] using hcieq
      · exact congrFun hfaces ⟨j, by simpa [s] using hji⟩
    cases isEmpty_or_nonempty ι with
    | inl hi =>
      letI := hi
      exact hc0 (Subsingleton.elim c a)
    | inr hi =>
      letI := hi
      have hdist := haway hcS hc0
      let U : Set (ι → ℝ) := {z | ε / 2 < dist z a}
      have hU : U ∈ 𝓝 c :=
        (isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds
          (show c ∈ U by dsimp [U]; linarith)
      obtain ⟨z, hzU, haz, hzc, hFzc, hsum⟩ := rectangle_strict_descent hclower
        (hF c hcS.1) (hA c hcS.1) hU
      have hzT : z ∈ T := by
        refine ⟨⟨⟨haz, hzc.trans hcS.1.2⟩, hFzc.trans hcS.2⟩, ?_⟩
        have hzdist : ε / 2 < dist z a := hzU
        exact fun hz => (not_lt_of_ge hzdist.le) (Metric.mem_ball.mp hz)
      exact (not_lt_of_ge (hmin hzT)) hsum

end EllipsoidVerification
