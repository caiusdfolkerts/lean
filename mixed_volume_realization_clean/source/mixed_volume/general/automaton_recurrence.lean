module

public import mixed_volume.general.automaton_zonoids
public import mixed_volume.general.body_contraction

/-! The complete state recurrences and their uniqueness, including arbitrary
independent translation errors. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace MixedVolume.AutomatonRecurrence

open VolumePolynomials VolumePolynomials.BodySupport AutomatonWords AutomatonZonoids
open BodyContraction Set
open scoped Pointwise BigOperators

variable {s m : ℕ}

def wordDecomposition : Unit ⊕ (Fin s × Word s) ≃ Word s where
  toFun
    | .inl _ => []
    | .inr p => p.1 :: p.2
  invFun
    | [] => .inl ()
    | a :: w => .inr (a, w)
  left_inv := by rintro (⟨⟩ | ⟨a,w⟩) <;> rfl
  right_inv := by intro w; cases w <;> rfl

/-- Splitting the full free monoid into the empty word and the first-letter
classes, with absolute convergence explicitly supplied. -/
theorem tsum_words (f : Word s → ℝ) (hf : Summable f) :
    (∑' w, f w) = f [] + ∑ a : Fin s, ∑' w, f (a :: w) := by
  have h := wordDecomposition.summable_iff.mpr hf
  have hleft := h.comp_injective Sum.inl_injective
  have hright := h.comp_injective Sum.inr_injective
  change Summable (fun _ : Unit => f []) at hleft
  change Summable (fun p : Fin s × Word s => f (p.1 :: p.2)) at hright
  calc
    (∑' w, f w) = ∑' x : Unit ⊕ (Fin s × Word s), f (wordDecomposition x) :=
      (wordDecomposition.tsum_eq f).symm
    _ = (∑' _ : Unit, f []) + ∑' p : Fin s × Word s, f (p.1 :: p.2) :=
      hleft.tsum_sum hright
    _ = f [] + ∑ a : Fin s, ∑' w, f (a :: w) := by
      rw [hright.tsum_prod]
      simp only [tsum_fintype, Finset.univ_unique, Finset.sum_singleton]

theorem tail_support_sum (A : Data s m) (hs : 0 < s) (a : Fin s) (j : Fin m)
    (l : Plane →L[ℝ] ℝ) :
    (∑' w : Word s, A.weight (a :: w) j * ((1 / 2 : ℝ) * |l (generator (a :: w))|)) =
      ∑ k, A.P a j k *
        ∑' w : Word s, A.weight w k * ((1 / 2 : ℝ) * |l (transition a (generator w))|) := by
  have ht (k : Fin m) : Summable (fun w : Word s =>
      A.P a j k * (A.weight w k * ((1 / 2 : ℝ) * |l (transition a (generator w))|))) := by
    exact (SeriesSupport.weighted_support_summable (l.comp (transition a)) generator
      (fun w => A.weight w k) (fun w => (A.weight_pos w k).le)
      (state_summable A hs k)).mul_left (A.P a j k)
  have hcomm := (hasSum_sum (s := (Finset.univ : Finset (Fin m)))
    (fun k _ => (ht k).hasSum)).tsum_eq
  calc
    _ = ∑' w : Word s, ∑ k, A.P a j k *
        (A.weight w k * ((1 / 2 : ℝ) * |l (transition a (generator w))|)) := by
      apply tsum_congr
      intro w
      rw [A.weight_cons, generator_cons, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ k, ∑' w : Word s, A.P a j k *
        (A.weight w k * ((1 / 2 : ℝ) * |l (transition a (generator w))|)) := hcomm
    _ = _ := by simp only [tsum_mul_left]

theorem unitY_support (l : Plane →L[ℝ] ℝ) :
    support PlanarCorner.unitY l = (1 / 2 : ℝ) * |l (0, 1)| := by
  have h := PlanarEdges.support_segmentBody (0, 1) l
  change support PlanarCorner.unitY l = |l (0, 1)| / 2 at h
  simpa only [div_eq_mul_inv, mul_comm, one_mul] using h

theorem bodyOperator_state_support (A : Data s m) (hs : 0 < s) (j : Fin m)
    (l : Plane →L[ℝ] ℝ) :
    support (bodyOperator A (stateBody A hs) j) l =
      (1 + A.f j) * ((1 / 2 : ℝ) * |l (0, 1)|) +
      ∑ a, ∑ k, A.P a j k *
        ∑' w : Word s, A.weight w k * ((1 / 2 : ℝ) * |l (transition a (generator w))|) := by
  rw [bodyOperator, SeriesSupport.support_add,
    SeriesSupport.support_smul _ _ (by linarith [A.f_nonneg j]), unitY_support,
    SeriesSupport.support_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [SeriesSupport.support_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [SeriesSupport.support_smul _ _ (A.P_nonneg a j k), SeriesSupport.support_map]
  congr 1
  exact SeriesSupport.support_weighted (l.comp (transition a)) generator
    (fun w => A.weight w k) (fun w => (A.weight_pos w k).le) (state_summable A hs k)

/-- Equation (4) is proved for the concrete infinite sums, for every state. -/
theorem state_equation (A : Data s m) (hs : 0 < s) (j : Fin m) :
    stateBody A hs j = bodyOperator A (stateBody A hs) j := by
  apply SeriesSupport.ext
  intro l
  rw [bodyOperator_state_support]
  change support (IndexedSeries.segmentSeriesBody _ (state_summable A hs j)) l = _
  rw [SeriesSupport.support_weighted l generator (fun w => A.weight w j)
    (fun w => (A.weight_pos w j).le) (state_summable A hs j)]
  rw [tsum_words _ (SeriesSupport.weighted_support_summable l generator
    (fun w => A.weight w j) (fun w => (A.weight_pos w j).le) (state_summable A hs j))]
  simp only [A.weight_nil, generator_nil]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  exact tail_support_sum A hs a j l

/-- Paper Lemma 2.1: the full stochastic system has precisely one tuple of
compact convex solutions. -/
theorem unique_solution (A : Data s m) (hs : 0 < s) :
    ∃! K : Fin m → ConvexBody Plane, ∀ j, K j = bodyOperator A K j := by
  refine ⟨stateBody A hs, state_equation A hs, ?_⟩
  intro K hK
  exact bodyOperator_unique A hs K (stateBody A hs) hK (state_equation A hs)

/-- The translation-invariant clause of Paper Lemma 2.1, fully instantiated
with the actual canonical word zonoids. -/
theorem solution_up_to_translation (A : Data s m) (hs : 0 < s)
    (K : Fin m → ConvexBody Plane) (v : Fin m → Plane)
    (hK : ∀ j, K j = translateBody (v j) (bodyOperator A K j)) :
    ∃ z : Fin m → Plane, ∀ j, K j = translateBody (z j) (stateBody A hs j) :=
  unique_up_to_translations A hs (stateBody A hs) K (state_equation A hs) v hK

end MixedVolume.AutomatonRecurrence

end
