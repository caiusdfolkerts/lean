module
public import Consolidated.MatrixNormalization
public import Papers.RationalityTenVectorBasisFamilies
public import MatroidCatalogue.N8R4

@[expose] public section
noncomputable section

/-!
# Removing zero rows from the finite rank-four input

The checked catalogue is loopless. A zero vector is handled by replacing it
temporarily with a duplicate of a nonzero vector, then setting the original
zero rows back to zero. No perturbation is required to make a zero vector
nonzero, and no additional incidence is discarded.
-/

namespace Papers.RationalityTen.MatroidChecked.ZeroRows

open Matrix Set Filter Topology
open Papers.MatrixGaugeNormalization Papers.RationalKernelCharts
open VectorBasisFamilies
open scoped BigOperators

/-- A fixed rational row scaling may include zeros. Exact preservation of
all zero maximal minors survives such a scaling. -/
theorem density_scale_rational_rows {n r : ℕ}
    (p : Matrix (Fin n) (Fin r) ℝ) (a : Fin n → ℝ)
    (ha : ∀ i, RatScalar (a i))
    (hp : p ∈ closure (ZeroRationalRealizations p)) :
    scaleRowsColumns p a (fun _ => 1) ∈
      closure (ZeroRationalRealizations (scaleRowsColumns p a (fun _ => 1))) := by
  let f : Matrix (Fin n) (Fin r) ℝ → Matrix (Fin n) (Fin r) ℝ :=
    fun q => scaleRowsColumns q a (fun _ => 1)
  have hf : Continuous f := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (continuous_const.mul
      (continuous_apply_apply i j)).mul continuous_const
  have hcl := mem_closure_image hf.continuousAt hp
  apply closure_mono (s := f '' _) ?_ hcl
  rintro _ ⟨q,hq,rfl⟩
  refine ⟨scaleRowsColumns_rational q a (fun _ => 1) hq.1 ha
    (fun _ => ⟨1, by simp⟩), ?_⟩
  intro s hs
  rw [scaleRowsColumns_minor] at hs ⊢
  simp only [Finset.prod_const_one,mul_one] at hs ⊢
  rcases mul_eq_zero.mp hs with hfactor | hminor
  · rw [hfactor,zero_mul]
  · rw [hq.2 s hminor,mul_zero]

def replaceZeroRows {n r : ℕ} (p : Matrix (Fin n) (Fin r) ℝ)
    (j : Fin n) : Matrix (Fin n) (Fin r) ℝ := by
  classical
  exact fun i => if p i = 0 then p j else p i

def restoreZeroMask {n r : ℕ} (p : Matrix (Fin n) (Fin r) ℝ) : Fin n → ℝ := by
  classical
  exact fun i => if p i = 0 then 0 else 1

theorem replaceZeroRows_nonzero {n r : ℕ}
    (p : Matrix (Fin n) (Fin r) ℝ) (j : Fin n) (hj : p j ≠ 0) :
    ∀ i, replaceZeroRows p j i ≠ 0 := by
  intro i
  by_cases hi : p i = 0
  · simpa only [replaceZeroRows,if_pos hi] using hj
  · simpa only [replaceZeroRows,if_neg hi] using hi

/-- Replacing a zero row by an existing row preserves the linear span. -/
theorem replaceZeroRows_span {n r : ℕ}
    (p : Matrix (Fin n) (Fin r) ℝ) (j : Fin n) :
    Submodule.span ℝ (Set.range (replaceZeroRows p j)) =
      Submodule.span ℝ (Set.range p) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    by_cases hi : p i = 0
    · simp only [replaceZeroRows,if_pos hi]
      exact Submodule.subset_span ⟨j,rfl⟩
    · simp only [replaceZeroRows,if_neg hi]
      exact Submodule.subset_span ⟨i,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    by_cases hi : p i = 0
    · rw [hi]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨i,by simp only [replaceZeroRows,if_neg hi]⟩

theorem restoreZeroMask_rational {n r : ℕ}
    (p : Matrix (Fin n) (Fin r) ℝ) :
    ∀ i, RatScalar (restoreZeroMask p i) := by
  intro i
  by_cases hi : p i = 0
  · exact ⟨0,by simp [restoreZeroMask,hi]⟩
  · exact ⟨1,by simp [restoreZeroMask,hi]⟩

theorem restore_replaceZeroRows {n r : ℕ}
    (p : Matrix (Fin n) (Fin r) ℝ) (j : Fin n) :
    scaleRowsColumns (replaceZeroRows p j) (restoreZeroMask p) (fun _ => 1) = p := by
  ext i k
  by_cases hi : p i = 0
  · simp [scaleRowsColumns,restoreZeroMask,replaceZeroRows,hi]
  · simp [scaleRowsColumns,restoreZeroMask,replaceZeroRows,hi]

theorem density_of_replaceZeroRows {n r : ℕ}
    (p : Matrix (Fin n) (Fin r) ℝ) (j : Fin n)
    (hp : replaceZeroRows p j ∈ closure (ZeroRationalRealizations (replaceZeroRows p j))) :
    p ∈ closure (ZeroRationalRealizations p) := by
  have h := density_scale_rational_rows (replaceZeroRows p j) (restoreZeroMask p)
    (restoreZeroMask_rational p) hp
  simpa only [restore_replaceZeroRows] using h

/-- A purely finite statement that every pair of distinct labels extends
to one of the recorded bases. -/
def PairCovered (B : Finset (Finset (Fin 8))) : Prop :=
  ∀ i j : Fin 8, i ≠ j → ∃ A ∈ B, i ∈ A ∧ j ∈ A

theorem pairCovered_transport (A B : Finset (Finset (Fin 8)))
    (σ : Equiv.Perm (Fin 8)) (h : A.image (fun S => S.image σ) = B)
    (hB : PairCovered B) : PairCovered A := by
  intro i j hij
  obtain ⟨T,hT,hi,hj⟩ := hB (σ i) (σ j) (fun h => hij (σ.injective h))
  rw [← h] at hT
  obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hT
  refine ⟨S,hS,?_,?_⟩
  · obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hi
    exact σ.injective he ▸ hx
  · obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hj
    exact σ.injective he ▸ hx

theorem injective_of_pairCovered {K : Type*} [Field K]
    (p : Fin 8 → Fin 4 → K) (h : PairCovered (vectorBases p)) :
    Function.Injective p := by
  intro i j heq
  by_contra hij
  obtain ⟨A,hA,hi,hj⟩ := h i j hij
  exact hij (((mem_vectorBases p A).mp hA).2.injOn hi hj heq)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem golden_pairCovered : PairCovered (MatroidCatalogue.N8R4.family 563) := by
  unfold PairCovered
  decide +kernel

/-- A configuration with a repeated row cannot have the exceptional
golden basis family, under any relabeling. -/
theorem not_golden_of_repeated_row {K : Type*} [Field K]
    (p : Fin 8 → Fin 4 → K) (i j : Fin 8) (hij : i ≠ j) (hp : p i = p j)
    (σ : Equiv.Perm (Fin 8)) :
    (vectorBases p).image (fun S => S.image σ) ≠ MatroidCatalogue.N8R4.family 563 := by
  intro h
  have hc := pairCovered_transport (vectorBases p) _ σ h golden_pairCovered
  exact hij (injective_of_pairCovered p hc hp)

theorem replaceZeroRows_not_golden
    (p : Matrix (Fin 8) (Fin 4) ℝ) (i j : Fin 8)
    (hi : p i = 0) (hj : p j ≠ 0) (σ : Equiv.Perm (Fin 8)) :
    (vectorBases (replaceZeroRows p j)).image (fun S => S.image σ) ≠
      MatroidCatalogue.N8R4.family 563 := by
  have hij : i ≠ j := by
    intro heq
    subst i
    exact hj hi
  apply not_golden_of_repeated_row (replaceZeroRows p j) i j hij
  simp only [replaceZeroRows,if_pos hi,if_neg hj]

/-- Padding retains every original label and duplicates a specified row. -/
def extendRows {n m r : ℕ} (p : Matrix (Fin n) (Fin r) ℝ)
    (hnm : n ≤ m) (j : Fin n) : Matrix (Fin m) (Fin r) ℝ :=
  fun i => if hi : i.val < n then p ⟨i.val,hi⟩ else p j

theorem restrict_extendRows {n m r : ℕ}
    (p : Matrix (Fin n) (Fin r) ℝ) (hnm : n ≤ m) (j : Fin n) :
    (extendRows p hnm j).submatrix (Fin.castLE hnm) id = p := by
  ext i k
  simp [extendRows,Matrix.submatrix_apply,i.isLt]

theorem extendRows_nonzero {n m r : ℕ}
    (p : Matrix (Fin n) (Fin r) ℝ) (hnm : n ≤ m) (j : Fin n)
    (hp : ∀ i, p i ≠ 0) : ∀ i, extendRows p hnm j i ≠ 0 := by
  intro i
  by_cases hi : i.val < n
  · simpa only [extendRows,dif_pos hi] using hp ⟨i.val,hi⟩
  · simpa only [extendRows,dif_neg hi] using hp j

theorem extendRows_span {n m r : ℕ}
    (p : Matrix (Fin n) (Fin r) ℝ) (hnm : n ≤ m) (j : Fin n) :
    Submodule.span ℝ (Set.range (extendRows p hnm j)) =
      Submodule.span ℝ (Set.range p) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    by_cases hi : i.val < n
    · simp only [extendRows,dif_pos hi]
      exact Submodule.subset_span ⟨⟨i.val,hi⟩,rfl⟩
    · simp only [extendRows,dif_neg hi]
      exact Submodule.subset_span ⟨j,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    apply Submodule.subset_span
    refine ⟨Fin.castLE hnm i,?_⟩
    funext k
    simpa only [Matrix.submatrix_apply,id_eq] using
      congrFun (congrFun (restrict_extendRows p hnm j) i) k

theorem extendRows_eight_not_golden {n : ℕ}
    (p : Matrix (Fin n) (Fin 4) ℝ) (hn : n < 8) (j : Fin n)
    (σ : Equiv.Perm (Fin 8)) :
    (vectorBases (extendRows p hn.le j)).image (fun S => S.image σ) ≠
      MatroidCatalogue.N8R4.family 563 := by
  let i : Fin 8 := ⟨n,hn⟩
  let k : Fin 8 := Fin.castLE hn.le j
  have hik : i ≠ k := by
    intro h
    have hv : n = j.val := congrArg Fin.val h
    exact Nat.ne_of_gt j.isLt hv
  apply not_golden_of_repeated_row (extendRows p hn.le j) i k hik
  simp [extendRows,i,k,j.isLt]

theorem exists_nonzero_of_span {n : ℕ}
    (p : Matrix (Fin n) (Fin 4) ℝ)
    (hp : Submodule.span ℝ (Set.range p) = ⊤) : ∃ j, p j ≠ 0 := by
  by_contra h
  have hz : ∀ j, p j = 0 := by
    intro j
    by_contra hj
    exact h ⟨j,hj⟩
  have hbot : Submodule.span ℝ (Set.range p) = ⊥ := by
    apply Submodule.span_eq_bot.mpr
    rintro _ ⟨j,rfl⟩
    exact hz j
  exact top_ne_bot (hp.symm.trans hbot)

/-- The only input still needed after the finite classification: density
for spanning loopless configurations outside the explicitly identified
golden basis family. This is a proposition, not a new axiom. -/
def LooplessNongoldenDensity : Prop :=
  ∀ p : Matrix (Fin 8) (Fin 4) ℝ,
    Submodule.span ℝ (Set.range p) = ⊤ →
    (∀ i, p i ≠ 0) →
    (∀ σ : Equiv.Perm (Fin 8),
      (vectorBases p).image (fun S => S.image σ) ≠ MatroidCatalogue.N8R4.family 563) →
    p ∈ closure (ZeroRationalRealizations p)

theorem density_with_zero_row (H : LooplessNongoldenDensity)
    (p : Matrix (Fin 8) (Fin 4) ℝ)
    (hp : Submodule.span ℝ (Set.range p) = ⊤) (i : Fin 8) (hi : p i = 0) :
    p ∈ closure (ZeroRationalRealizations p) := by
  obtain ⟨j,hj⟩ := exists_nonzero_of_span p hp
  apply density_of_replaceZeroRows p j
  apply H (replaceZeroRows p j)
  · rw [replaceZeroRows_span,hp]
  · exact replaceZeroRows_nonzero p j hj
  · exact replaceZeroRows_not_golden p i j hi hj

/-- Rank four on fewer than eight labels, including arbitrary zero rows,
follows by duplicate padding and exact restriction. -/
theorem density_fewer_than_eight (H : LooplessNongoldenDensity)
    {n : ℕ} (p : Matrix (Fin n) (Fin 4) ℝ) (hn : n < 8)
    (hp : Submodule.span ℝ (Set.range p) = ⊤) :
    p ∈ closure (ZeroRationalRealizations p) := by
  obtain ⟨j,hj⟩ := exists_nonzero_of_span p hp
  let q := replaceZeroRows p j
  let q8 := extendRows q hn.le j
  have hq : ∀ i, q i ≠ 0 := replaceZeroRows_nonzero p j hj
  have hq8 : q8 ∈ closure (ZeroRationalRealizations q8) := by
    apply H q8
    · change Submodule.span ℝ (Set.range (extendRows q hn.le j)) = ⊤
      rw [extendRows_span,replaceZeroRows_span,hp]
    · exact extendRows_nonzero q hn.le j hq
    · exact extendRows_eight_not_golden q hn j
  have hrestrict := restrict_rows_zero_density q8 (Fin.castLE hn.le) hq8
  rw [restrict_extendRows] at hrestrict
  exact density_of_replaceZeroRows p j hrestrict

end Papers.RationalityTen.MatroidChecked.ZeroRows
