module
public import Papers.PlaneReinsertionCharts

@[expose] public section

noncomputable section

open Matrix
open scoped BigOperators

namespace Papers.RationalityTen.PlaneRationalization

open SmallTripleCores

def TripleZeros (S : Finset (Fin 8)) (p q : Fin 8 → V) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, ∀ k ∈ S,
    (Matrix.of ![p i,p j,p k]).det = 0 → (Matrix.of ![q i,q j,q k]).det = 0

structure DefiningPair (T : Triple) (v : Fin 8) where
  left : Fin 8
  right : Fin 8
  left_mem : left ∈ T.erase v
  right_mem : right ∈ T.erase v
  ne : left ≠ right

theorem exists_definingPair {S : Finset (Fin 8)} {p : Fin 8 → V}
    (hp : IndependentProjectivePoints S p) {T : Triple}
    (hT : T ∈ richLines S p) (v : Fin 8) :
    Nonempty (DefiningPair T v) := by
  obtain ⟨a,ha,b,hb,hab,_⟩ := richLine_pair_after_deletion hp hT v
  exact ⟨⟨a,b,ha,hb,hab⟩⟩

def DefiningPair.join {T : Triple} {v : Fin 8} (B : DefiningPair T v)
    (q : Fin 8 → V) : V :=
  crossProduct (q B.left) (q B.right)

theorem richLine_triple_zero {S : Finset (Fin 8)} {p : Fin 8 → V}
    (hp : IndependentProjectivePoints S p) {T : Triple}
    (hT : T ∈ richLines S p) {i j k : Fin 8}
    (hi : i ∈ T) (hj : j ∈ T) (hk : k ∈ T) :
    (Matrix.of ![p i,p j,p k]).det = 0 := by
  apply triple_det_zero_of_incident_line _ _ _ (richLineCovector hp ⟨T,hT⟩)
    (richLineCovector_ne_zero hp ⟨T,hT⟩)
  · exact (richLines_realization hp).incident ⟨T,hT⟩ i hi
  · exact (richLines_realization hp).incident ⟨T,hT⟩ j hj
  · exact (richLines_realization hp).incident ⟨T,hT⟩ k hk

theorem DefiningPair.join_incident {S : Finset (Fin 8)} {p : Fin 8 → V}
    (hp : IndependentProjectivePoints S p) {T : Triple}
    (hT : T ∈ richLines S p) {v : Fin 8} (B : DefiningPair T v)
    {i : Fin 8} (hi : i ∈ T) :
    dotProduct (B.join p) (p i) = 0 := by
  rw [DefiningPair.join,cross_dot_eq_det]
  exact richLine_triple_zero hp hT
    (Finset.mem_of_mem_erase B.left_mem) (Finset.mem_of_mem_erase B.right_mem) hi

theorem DefiningPair.left_mem_deleted {S : Finset (Fin 8)} {p : Fin 8 → V}
    {T : Triple} (hT : T ∈ richLines S p) {v : Fin 8} (B : DefiningPair T v) :
    B.left ∈ S.erase v :=
  Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp B.left_mem).1,
    richLine_subset hT (Finset.mem_of_mem_erase B.left_mem)⟩

theorem DefiningPair.right_mem_deleted {S : Finset (Fin 8)} {p : Fin 8 → V}
    {T : Triple} (hT : T ∈ richLines S p) {v : Fin 8} (B : DefiningPair T v) :
    B.right ∈ S.erase v :=
  Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp B.right_mem).1,
    richLine_subset hT (Finset.mem_of_mem_erase B.right_mem)⟩

theorem DefiningPair.join_ne_zero {S : Finset (Fin 8)} {p q : Fin 8 → V}
    {T : Triple} (hT : T ∈ richLines S p) {v : Fin 8} (B : DefiningPair T v)
    (hq : IndependentProjectivePoints (S.erase v) q) :
    B.join q ≠ 0 :=
  crossProduct_ne_zero_iff_linearIndependent.mpr
    (hq.2 B.left (B.left_mem_deleted hT) B.right (B.right_mem_deleted hT) B.ne)

/-- Every retained point of an old rich line lies on the reconstructed join. -/
theorem DefiningPair.join_incident_after_deletion
    {S : Finset (Fin 8)} {p q : Fin 8 → V}
    (hp : IndependentProjectivePoints S p) {T : Triple}
    (hT : T ∈ richLines S p) {v : Fin 8} (B : DefiningPair T v)
    (hzeros : TripleZeros (S.erase v) p q)
    {i : Fin 8} (hi : i ∈ T.erase v) :
    dotProduct (B.join q) (q i) = 0 := by
  rw [DefiningPair.join,cross_dot_eq_det]
  apply hzeros B.left (B.left_mem_deleted hT)
    B.right (B.right_mem_deleted hT) i
      (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hi).1,
        richLine_subset hT (Finset.mem_of_mem_erase hi)⟩)
  exact richLine_triple_zero hp hT
    (Finset.mem_of_mem_erase B.left_mem)
    (Finset.mem_of_mem_erase B.right_mem) (Finset.mem_of_mem_erase hi)

noncomputable def throughPoint (S : Finset (Fin 8)) (p : Fin 8 → V)
    (v : Fin 8) : Family :=
  (richLines S p).filter fun T => v ∈ T

theorem triple_zero_reinsert_first
    {S : Finset (Fin 8)} {p q : Fin 8 → V} {v : Fin 8}
    (hp : IndependentProjectivePoints S p) (hv : v ∈ S)
    (hq : IndependentProjectivePoints (S.erase v) q)
    (hzeros : TripleZeros (S.erase v) p q)
    (B : ∀ T, T ∈ throughPoint S p v → DefiningPair T v)
    (w : V) (hw : ∀ T (hT : T ∈ throughPoint S p v),
      dotProduct ((B T hT).join q) w = 0)
    {i j : Fin 8} (hi : i ∈ S.erase v) (hj : j ∈ S.erase v)
    (hdet : (Matrix.of ![p v,p i,p j]).det = 0) :
    (Matrix.of ![w,q i,q j]).det = 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simp only [Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  obtain ⟨T,hT,hvT,hiT,hjT⟩ := dependent_triple_on_rich_line
    hv (Finset.mem_of_mem_erase hi) (Finset.mem_of_mem_erase hj)
    (Ne.symm (Finset.mem_erase.mp hi).1)
    (Ne.symm (Finset.mem_erase.mp hj).1) hij hdet
  have hTv : T ∈ throughPoint S p v := Finset.mem_filter.mpr ⟨hT,hvT⟩
  apply triple_det_zero_of_incident_line _ _ _ ((B T hTv).join q)
    ((B T hTv).join_ne_zero hT hq) (hw T hTv)
  · exact (B T hTv).join_incident_after_deletion hp hT hzeros
      (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hi).1,hiT⟩)
  · exact (B T hTv).join_incident_after_deletion hp hT hzeros
      (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1,hjT⟩)

/-- Reinsert a vector on all original rich lines through the deleted label.
This preserves every old dependent triple, including lines with four or
more points; no accidental general-position assumption is used. -/
theorem tripleZeros_update
    {S : Finset (Fin 8)} {p q : Fin 8 → V} {v : Fin 8}
    (hp : IndependentProjectivePoints S p) (hv : v ∈ S)
    (hq : IndependentProjectivePoints (S.erase v) q)
    (hzeros : TripleZeros (S.erase v) p q)
    (B : ∀ T, T ∈ throughPoint S p v → DefiningPair T v)
    (w : V) (hw : ∀ T (hT : T ∈ throughPoint S p v),
      dotProduct ((B T hT).join q) w = 0) :
    TripleZeros S p (Function.update q v w) := by
  classical
  have hfirst : ∀ {i j : Fin 8}, i∈S.erase v → j∈S.erase v →
      (Matrix.of ![p v,p i,p j]).det=0 → (Matrix.of ![w,q i,q j]).det=0 :=
    fun hi hj hd => triple_zero_reinsert_first hp hv hq hzeros B w hw hi hj hd
  intro i hi j hj k hk hdet
  by_cases hiv : i = v
  · subst i
    by_cases hjv : j = v
    · subst j
      simp only [Function.update_self,Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      ring
    by_cases hkv : k = v
    · subst k
      simp only [Function.update_self,Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      ring
    simpa [Function.update_of_ne hjv,Function.update_of_ne hkv] using
      hfirst (Finset.mem_erase.mpr ⟨hjv,hj⟩)
        (Finset.mem_erase.mpr ⟨hkv,hk⟩) hdet
  by_cases hjv : j = v
  · subst j
    by_cases hkv : k = v
    · subst k
      simp only [Function.update_self,Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      ring
    rw [triple_det_cycle] at hdet ⊢
    simpa [Function.update_of_ne hiv,Function.update_of_ne hkv] using
      hfirst (Finset.mem_erase.mpr ⟨hkv,hk⟩)
        (Finset.mem_erase.mpr ⟨hiv,hi⟩) hdet
  by_cases hkv : k = v
  · subst k
    rw [← triple_det_cycle] at hdet ⊢
    simpa [Function.update_of_ne hiv,Function.update_of_ne hjv] using
      hfirst (Finset.mem_erase.mpr ⟨hiv,hi⟩)
        (Finset.mem_erase.mpr ⟨hjv,hj⟩) hdet
  simpa [Function.update_of_ne hiv,Function.update_of_ne hjv,
    Function.update_of_ne hkv] using
    hzeros i (Finset.mem_erase.mpr ⟨hiv,hi⟩)
      j (Finset.mem_erase.mpr ⟨hjv,hj⟩)
      k (Finset.mem_erase.mpr ⟨hkv,hk⟩) hdet

end Papers.RationalityTen.PlaneRationalization
