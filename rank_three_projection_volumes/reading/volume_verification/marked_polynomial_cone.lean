module
public import VolumeVerification.Stereographic
public import VolumeVerification.EdgeMoments
@[expose] public section
set_option autoImplicit false

/-!
# The cyclic cone rays of a positive hollow rank-three matrix

The rays are explicit weighted evaluations of neighboring-root quadratic
polynomials, with infinity as one of the nodes.  Generation follows from
QuadraticCone.generated_of_nonnegative, not from an assumed polygon theorem.
-/
namespace VolumeVerification.MarkedPolynomialCone
open scoped BigOperators Matrix
open QuadraticCone Stereographic

section Ordered
variable {N : ℕ} (w t : Fin (N+1) → ℝ)

noncomputable def rays : Fin (N+2) → Fin (N+2) → ℝ :=
  fun e => markedEvaluation w t (generators t e)

private theorem next_zero :
    EdgeMoments.next (0 : Fin (N+2)) = (0 : Fin (N+1)).succ := by
  apply Fin.ext
  simp [EdgeMoments.next,finRotate_apply]

private theorem next_last :
    EdgeMoments.next (Fin.last (N+1)) = (0 : Fin (N+2)) := by
  exact finRotate_last

private theorem next_succ (i : Fin (N+1)) (hi : i ≠ Fin.last N) :
    EdgeMoments.next i.succ = (finRotate (N+1) i).succ := by
  have hi' : i.succ ≠ Fin.last (N+1) := by
    intro h
    apply hi
    apply Fin.ext
    have hv := congrArg Fin.val h
    simpa using hv
  apply Fin.ext
  change (finRotate (N+2) i.succ).val = (finRotate (N+1) i).val+1
  calc
    (finRotate (N+2) i.succ).val = i.succ.val + 1 := coe_finRotate_of_ne_last hi'
    _ = (i.val + 1) + 1 := rfl
    _ = (finRotate (N+1) i).val + 1 :=
      (congrArg (fun x : ℕ => x + 1) (coe_finRotate_of_ne_last hi)).symm

theorem rays_nonnegative (hw : ∀ i, 0 < w i) (ht : StrictMono t) :
    ∀ e i, 0 ≤ rays w t e i := by
  intro e i
  obtain ⟨hlead,hvalues⟩ := generators_nonnegative t ht e
  refine Fin.cases ?_ (fun i => ?_) i
  · change 0 ≤ 2*generators t e 0
    positivity
  · change 0 ≤ w i*evaluate (generators t e) (t i)
    exact mul_nonneg (hw i).le (hvalues i)

/-- The cyclic endpoint-zero pattern is derived from strict ordering of the
actual finite nodes and positivity of the actual coordinate weights. -/
theorem rayPattern (hN : 1 ≤ N)
    (hw : ∀ i, 0 < w i) (ht : StrictMono t) :
    EdgeMoments.RayPattern (rays w t) := by
  have hleft :
      ∀ i : Fin (N+2), rays w t 0 i = 0 ↔
        i = 0 ∨ i = (0 : Fin (N+1)).succ := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [rays,generators,leftRay]
    · simp only [rays,markedEvaluation_succ,generators_zero,evaluate_leftRay]
      rw [mul_eq_zero]
      simp only [(hw i).ne',false_or,sub_eq_zero]
      constructor
      · intro h
        exact Or.inr (congrArg Fin.succ (ht.injective h))
      · rintro (h | h)
        · exact False.elim (Fin.succ_ne_zero i h)
        · exact congrArg t (Fin.succ_inj.mp h)
  have hright :
      ∀ i : Fin (N+2), rays w t (Fin.last (N+1)) i = 0 ↔
        i = Fin.last (N+1) ∨ i = 0 := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [rays,generators_last,rightRay]
    · simp only [rays,markedEvaluation_succ,generators_last,evaluate_rightRay]
      rw [mul_eq_zero]
      simp only [(hw i).ne',false_or,sub_eq_zero]
      constructor
      · intro h
        left
        have hi : i = Fin.last N := (ht.injective h).symm
        subst i
        rfl
      · rintro (h | h)
        · apply congrArg t
          apply Fin.ext
          have hv := congrArg Fin.val h
          simpa using hv.symm
        · exact False.elim (Fin.succ_ne_zero i h)
  have hmiddle :
      ∀ (e : Fin (N+1)), e ≠ Fin.last N →
        ∀ i : Fin (N+2), rays w t e.succ i = 0 ↔
          i = e.succ ∨ i = (finRotate (N+1) e).succ := by
    intro e he i
    refine Fin.cases ?_ (fun i => ?_) i
    · have hnonzero : rays w t e.succ 0 ≠ 0 := by
        simp [rays,generators_succ t he,pairRay]
      constructor
      · intro h
        exact False.elim (hnonzero h)
      · rintro (h | h)
        · exact False.elim (Fin.succ_ne_zero e h.symm)
        · exact False.elim (Fin.succ_ne_zero (finRotate (N+1) e) h.symm)
    · simp only [rays,markedEvaluation_succ,generators_succ t he,evaluate_pairRay]
      rw [mul_eq_zero]
      simp only [(hw i).ne',false_or,mul_eq_zero,sub_eq_zero]
      constructor
      · rintro (h | h)
        · exact Or.inl (congrArg Fin.succ (ht.injective h))
        · exact Or.inr (congrArg Fin.succ (ht.injective h))
      · rintro (h | h)
        · exact Or.inl (congrArg t (Fin.succ_inj.mp h))
        · exact Or.inr (congrArg t (Fin.succ_inj.mp h))
  have hzeros : ∀ e i, rays w t e i = 0 ↔
      i = e ∨ i = EdgeMoments.next e := by
    intro e i
    refine Fin.cases ?_ (fun e => ?_) e
    · rw [next_zero]
      exact hleft i
    · by_cases he : e = Fin.last N
      · subst e
        change rays w t (Fin.last (N+1)) i = 0 ↔
          i = Fin.last (N+1) ∨ i = EdgeMoments.next (Fin.last (N+1))
        rw [next_last]
        exact hright i
      · rw [next_succ e he]
        exact hmiddle e he i
  refine ⟨?_,?_,?_⟩
  · intro e
    exact (hzeros e e).mpr (Or.inl rfl)
  · intro e
    exact (hzeros e (EdgeMoments.next e)).mpr (Or.inr rfl)
  · intro e i hie hin
    apply lt_of_le_of_ne (rays_nonnegative w t hw ht e i)
    intro h
    rcases (hzeros e i).mp h.symm with h' | h'
    · exact hie h'
    · exact hin h'

theorem generated_of_nonnegative_range (hN : 1 ≤ N)
    (hw : ∀ i, 0 < w i) (ht : StrictMono t)
    (y : Fin (N+2) → ℝ)
    (hy : ∀ i, 0 ≤ y i)
    (hrange : y ∈ (markedEvaluation w t).range) :
    ∃ c : Fin (N+2) → ℝ,
      (∀ e, 0 ≤ c e) ∧ ∑ e, c e • rays w t e = y := by
  obtain ⟨p,rfl⟩ := hrange
  have hlead : 0 ≤ p 0 := by
    have h0 := hy 0
    change 0 ≤ 2*p 0 at h0
    linarith
  have hvalues : ∀ i, 0 ≤ evaluate p (t i) := by
    intro i
    have hi := hy i.succ
    change 0 ≤ w i*evaluate p (t i) at hi
    exact (mul_nonneg_iff_of_pos_left (hw i)).mp hi
  obtain ⟨c,hc,hp⟩ := generated_of_nonnegative t hN ht p hlead hvalues
  refine ⟨c,hc,?_⟩
  have he := congrArg (markedEvaluation w t) hp
  simpa only [map_sum,map_smul,rays] using he

theorem generated_iff_nonnegative_range (hN : 1 ≤ N)
    (hw : ∀ i, 0 < w i) (ht : StrictMono t)
    (y : Fin (N+2) → ℝ) :
    (∃ c : Fin (N+2) → ℝ,
      (∀ e, 0 ≤ c e) ∧ ∑ e, c e • rays w t e = y) ↔
    (∀ i, 0 ≤ y i) ∧ y ∈ (markedEvaluation w t).range := by
  constructor
  · rintro ⟨c,hc,rfl⟩
    constructor
    · intro i
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
      exact Finset.sum_nonneg fun e _ =>
        mul_nonneg (hc e) (rays_nonnegative w t hw ht e i)
    · refine ⟨∑ e, c e • generators t e,?_⟩
      simp only [map_sum,map_smul,rays]
  · rintro ⟨hy,hrange⟩
    exact generated_of_nonnegative_range w t hN hw ht y hy hrange

end Ordered

/-- Sorting is a permutation of all original labels, fixing the distinguished
one.  The resulting cone rays generate precisely the nonnegative column space
of the permuted original matrix. -/
theorem exists_sorted_rays {N : ℕ}
    (P : Matrix (Fin (N+3)) (Fin (N+3)) ℝ)
    (hsym : ∀ i j, P i j = P j i) (hdiag : ∀ i, P i i = 0)
    (hpos : ∀ i j, i ≠ j → 0 < P i j) (hrank : P.rank = 3) :
    ∃ σ : Equiv.Perm (Fin (N+3)),
    ∃ r : Fin (N+3) → Fin (N+3) → ℝ,
      σ 0 = 0 ∧ EdgeMoments.RayPattern r ∧
      ∀ y : Fin (N+3) → ℝ,
        (∃ c : Fin (N+3) → ℝ,
          (∀ e, 0 ≤ c e) ∧ ∑ e, c e • r e = y) ↔
        (∀ i, 0 ≤ y i) ∧ y ∈ (P.submatrix σ σ).mulVecLin.range := by
  obtain ⟨w,t,hw,ht,hzero,hfinite⟩ :=
    exists_parameters P hsym hdiag hpos hrank.le
  obtain ⟨τ,hτ⟩ := exists_sorting t ht
  let σ := fixInfinity τ
  let Q := P.submatrix σ σ
  let w' : Fin (N+2) → ℝ := fun i => w (τ i)
  let t' : Fin (N+2) → ℝ := fun i => t (τ i)
  have hQsym : ∀ i j, Q i j = Q j i := fun i j => hsym _ _
  have hQdiag : ∀ i, Q i i = 0 := fun i => hdiag _
  have hQrank : Q.rank = 3 := by
    dsimp [Q]
    rw [Matrix.rank_submatrix,hrank]
  have hQzero : ∀ i, Q 0 i.succ = w' i := by
    intro i
    simpa [Q,σ,Matrix.submatrix,w'] using hzero (τ i)
  have hQfinite : ∀ i j,
      Q i.succ j.succ = (w' i*w' j/2)*(t' i-t' j)^2 := by
    intro i j
    simpa [Q,σ,Matrix.submatrix,w',t'] using hfinite (τ i) (τ j)
  have hrange := range_eq_markedEvaluation Q w' t'
    hQsym hQdiag hQrank hQzero hQfinite
  refine ⟨σ,rays w' t',fixInfinity_zero τ,
    rayPattern w' t' (by omega) (fun i => hw (τ i)) hτ,?_⟩
  intro y
  change _ ↔ (∀ i, 0 ≤ y i) ∧ y ∈ Q.mulVecLin.range
  rw [hrange]
  exact generated_iff_nonnegative_range w' t' (by omega)
    (fun i => hw (τ i)) hτ y

end VolumeVerification.MarkedPolynomialCone

