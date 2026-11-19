module
public import normal_projective.complete
/-! Actual supporting functionals for every pair-free labelled face.
Source preparation only; not yet compiled. -/
@[expose] public section
noncomputable section
namespace PalomarNormalCorollary7Support
open Set NormalProjective
open NormalProjective.RootedGeometry NormalProjective.UnitNormalization
/-- Two complementary completions suffice: a label is in both chosen binary
patterns exactly when it belongs to the original pair-free set. -/
theorem two_completions {n : ℕ} (S : Finset (Labels (n+1)))
    (hfree : ∀ i : Fin (n+1), ¬(Sum.inl i ∈ S ∧ Sum.inr i ∈ S)) :
    ∃ b c : Fin (n+1) → Bool, ∀ l,
      (CyclicCube.Chosen b l ∧ CyclicCube.Chosen c l) ↔ l ∈ S := by
  classical
  refine ⟨(fun i => decide (Sum.inr i ∈ S)),
    (fun i => decide (Sum.inl i ∉ S)),?_⟩
  intro l
  cases l with
  | inl i =>
    have hf := hfree i
    simp only [CyclicCube.Chosen,Sum.elim_inl]
    simp <;> tauto
  | inr i =>
    have hf := hfree i
    simp only [CyclicCube.Chosen,Sum.elim_inr]
    simp <;> tauto
/-- The midpoint of two actual polar cube vertices exposes precisely S in the
actual primal hull. The polar points and their incidence come from the proved
paired-halfspace recognition; no unproved polarity theorem is assumed. -/
theorem centered_pairfree_support (n : ℕ)
    (v : Labels (n+1) → CanonicalModel.Space (n+1))
    (hz : (0 : CanonicalModel.Space (n+1)) ∈ interior (NormalHull.hull v))
    (hpair : ∀ i : Fin (n+1), ∃ t : ℝ, 0<t ∧ t<1 ∧
      (1-t) • v (Sum.inl i) + t • v (Sum.inr i) ∈ interior (NormalHull.hull v))
    (S : Finset (Labels (n+1))) (hneS : S.Nonempty)
    (hfree : ∀ i : Fin (n+1), ¬(Sum.inl i ∈ S ∧ Sum.inr i ∈ S)) :
    ∃ ℓ : CanonicalModel.Space (n+1) →L[ℝ] ℝ, ℓ ≠ 0 ∧
      (∀ i, ℓ (v i) ≤ 1) ∧ (∀ i, ℓ (v i) = 1 ↔ i ∈ S) := by
  classical
  let f : Labels (n+1) → CanonicalModel.Space (n+1) →ₗ[ℝ] ℝ :=
    fun i => (rowForm (v i)).toLinearMap
  let h : Labels (n+1) → ℝ := fun _ => 1
  have hc : IsCompact (halfspaceRegion f h) := NormalHull.primal_compact_of_zero_interior v hz
  have hne : (halfspaceRegion f h).Nonempty := by
    refine ⟨0,?_⟩
    intro i
    simp only [map_zero,h]
    norm_num
  have hn : PairedHalfspaces.NoOppositeTight f h :=
    NormalHull.noOpposite_of_pair_sites v hpair
  obtain ⟨b,c,hbc⟩ := two_completions S hfree
  let x0 := (PairedHalfspaces.patternVertex f h hc hne hn b).val
  let x1 := (PairedHalfspaces.patternVertex f h hc hne hn c).val
  have hx0 : x0 ∈ halfspaceRegion f h :=
    (PairedHalfspaces.patternVertex f h hc hne hn b).property.1
  have hx1 : x1 ∈ halfspaceRegion f h :=
    (PairedHalfspaces.patternVertex f h hc hne hn c).property.1
  let x := (1/2 : ℝ) • x0 + (1/2 : ℝ) • x1
  have hx : x ∈ halfspaceRegion f h :=
    (convex_halfspaceRegion f h) hx0 hx1 (by norm_num) (by norm_num) (by norm_num)
  have hiff (i : Labels (n+1)) : f i x = 1 ↔ i ∈ S := by
    have hi0 : f i x0 ≤ 1 := hx0 i
    have hi1 : f i x1 ≤ 1 := hx1 i
    have heval : f i x = (f i x0 + f i x1)/2 := by
      simp only [x,map_add,map_smul,smul_eq_mul]
      ring
    have heq : f i x = 1 ↔ f i x0 = 1 ∧ f i x1 = 1 := by
      constructor
      · intro hi
        constructor <;> nlinarith
      · rintro ⟨h0,h1⟩
        rw [heval,h0,h1]
        norm_num
    have hb := PairedHalfspaces.patternVertex_incidence f h hc hne hn b i
    have hc' := PairedHalfspaces.patternVertex_incidence f h hc hne hn c i
    exact heq.trans ((and_congr hb hc').trans (hbc i))
  have hswap (i : Labels (n+1)) : rowForm x (v i) = f i x := by
    simp only [f,ContinuousLinearMap.coe_coe,rowForm_apply]
    exact NormalHull.dot_comm _ _
  refine ⟨rowForm x,?_,?_,?_⟩
  · intro he
    obtain ⟨i,hi⟩ := hneS
    have hi' : rowForm x (v i) = 1 := (hswap i).trans ((hiff i).mpr hi)
    rw [he,ContinuousLinearMap.zero_apply] at hi'
    norm_num at hi'
  · intro i
    rw [hswap]
    exact hx i
  · intro i
    rw [hswap]
    exact hiff i
end PalomarNormalCorollary7Support
