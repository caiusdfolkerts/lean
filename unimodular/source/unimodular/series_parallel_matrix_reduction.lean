module

public import Unimodular.SeriesParallelFundamental
public import Unimodular.SeriesParallelFinite

@[expose] public section

open scoped BigOperators Matroid
open Set

namespace Unimodular.VectorMatroid

noncomputable section

variable {K α V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A nonzero scalar multiple gives an ordinary parallel pair, with both labels
retained and with no convention about the signs of the represented vectors. -/
theorem pair_isCircuit_of_smul (v : α → V) {e f : α} (hef : e ≠ f)
    (c : K) (hc : c ≠ 0) (hf : v f ≠ 0) (heq : v e = c • v f) :
    (ofFamily (K := K) v).IsCircuit {e, f} := by
  have he : (ofFamily (K := K) v).IsNonloop e := by
    rw [← Matroid.not_isLoop_iff (by simp), ofFamily_isLoop_iff, heq]
    exact smul_ne_zero hc hf
  apply (he.closure_eq_closure_iff_isCircuit_of_ne hef).mp
  ext x
  rw [ofFamily_mem_closure, ofFamily_mem_closure, Set.image_singleton,
    Set.image_singleton, heq, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc)]

private theorem spanning_compl_singleton (v : α → V) (e : α)
    (he : v e ∈ Submodule.span K (v '' ({e} : Set α)ᶜ)) :
    (ofFamily (K := K) v).Spanning ({e} : Set α)ᶜ := by
  apply (ofFamily_spanning_iff v _).mpr
  apply le_antisymm (Submodule.span_mono (Set.image_subset_range _ _))
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  by_cases ha : a = e
  · simpa [ha] using he
  · exact Submodule.subset_span ⟨a, by simpa using ha, rfl⟩

/-- A functional supported on a pair gives an ordinary cocircuit once neither
member is a coloop. This criterion does not impose artificial scalar values on
the two vectors; it therefore applies directly to signed integral matrices. -/
theorem pair_isCocircuit_of_support (v : α → V) {e f : α} (hef : e ≠ f)
    (g : V →ₗ[K] K) (he : g (v e) ≠ 0)
    (hz : ∀ a, a ≠ e → a ≠ f → g (v a) = 0)
    (hne : ¬(ofFamily (K := K) v).IsColoop e)
    (hnf : ¬(ofFamily (K := K) v).IsColoop f) :
    (ofFamily (K := K) v).IsCocircuit {e, f} := by
  let M := ofFamily (K := K) v
  have hker : Submodule.span K (v '' ({e, f} : Set α)ᶜ) ≤ LinearMap.ker g := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    exact hz a (fun h => ha (by simp [h])) (fun h => ha (by simp [h]))
  have hnot : ¬M.Spanning ({e, f} : Set α)ᶜ := by
    intro h
    have hs := (ofFamily_spanning_iff v _).mp h
    have hv : v e ∈ Submodule.span K (v '' ({e, f} : Set α)ᶜ) := by
      rw [hs]
      exact Submodule.subset_span ⟨e, rfl⟩
    exact he (hker hv)
  have hspe : M.Spanning ({e} : Set α)ᶜ := spanning_compl_singleton v e (by
    simpa only [ofFamily_isColoop_iff, not_not] using hne)
  have hspf : M.Spanning ({f} : Set α)ᶜ := spanning_compl_singleton v f (by
    simpa only [ofFamily_isColoop_iff, not_not] using hnf)
  rw [Matroid.isCocircuit_iff_minimal_compl_nonspanning, minimal_iff_forall_ssubset]
  refine ⟨by simpa [M, ← Set.compl_eq_univ_sdiff] using hnot, ?_⟩
  intro D hD
  simp only [not_not]
  rcases Set.subset_pair_iff_eq.mp hD.subset with rfl | rfl | rfl | hlast
  · simpa [M] using M.ground_spanning
  · simpa [M, ← Set.compl_eq_univ_sdiff] using hspe
  · simpa [M, ← Set.compl_eq_univ_sdiff] using hspf
  · exact False.elim (hD.ne hlast)

end
end Unimodular.VectorMatroid

namespace Unimodular.SeriesParallel

noncomputable section

universe u v

variable {I : Type u} {J : Type v} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- The full represented configuration `[1 | A]`, on disjoint basis and
nonbasis labels. Zero columns and repeated columns are retained. -/
def matrixColumns (A : I → J → ℤ) : I ⊕ J → I → ℝ
  | .inl i => Pi.basisFun ℝ I i
  | .inr j => fun i => (A i j : ℝ)

/-- The ordinary Mathlib vector matroid of the full matrix `[1 | A]`. -/
def matrixMatroid (A : I → J → ℤ) : Matroid (I ⊕ J) :=
  VectorMatroid.ofFamily (K := ℝ) (matrixColumns A)

@[simp] theorem matrixColumns_left (A : I → J → ℤ) (i : I) :
    matrixColumns A (.inl i) = Pi.basisFun ℝ I i := rfl

@[simp] theorem matrixColumns_right (A : I → J → ℤ) (j : J) (i : I) :
    matrixColumns A (.inr j) i = (A i j : ℝ) := rfl

@[simp] theorem matrixMatroid_ground (A : I → J → ℤ) : (matrixMatroid A).E = Set.univ := rfl

/-- All unit basis columns remain nonloops regardless of the other columns. -/
theorem matrix_left_nonloop (A : I → J → ℤ) (i : I) :
    (matrixMatroid A).IsNonloop (.inl i) := by
  rw [← Matroid.not_isLoop_iff (by simp), matrixMatroid, VectorMatroid.ofFamily_isLoop_iff]
  exact (Pi.basisFun ℝ I).ne_zero i

/-- A selected nonzero coordinate proves that the corresponding column is not a loop. -/
theorem matrix_right_nonloop (A : I → J → ℤ) (i : I) (j : J) (h : A i j ≠ 0) :
    (matrixMatroid A).IsNonloop (.inr j) := by
  rw [← Matroid.not_isLoop_iff (by simp), matrixMatroid, VectorMatroid.ofFamily_isLoop_iff]
  intro hz
  have he : (A i j : ℝ) = 0 := congrFun hz i
  exact h (by exact_mod_cast he)

/-- A nonbasis column is always in the span of the other labels, including when
it is zero. Thus it is never a coloop. -/
theorem matrix_right_not_coloop (A : I → J → ℤ) (j : J) :
    ¬(matrixMatroid A).IsColoop (.inr j) := by
  rw [matrixMatroid, VectorMatroid.ofFamily_isColoop_iff, not_not]
  have ht : Submodule.span ℝ
      (matrixColumns A '' ({Sum.inr j} : Set (I ⊕ J))ᶜ) = ⊤ := by
    apply top_unique
    rw [← (Pi.basisFun ℝ I).span_eq]
    apply Submodule.span_mono
    rintro x ⟨i, rfl⟩
    exact ⟨.inl i, by simp, rfl⟩
  rw [ht]
  trivial

private theorem zero_coordinate_mem_span_others (A : I → J → ℤ) (i : I)
    (x : I → ℝ) (hx : x i = 0) :
    x ∈ Submodule.span ℝ (matrixColumns A '' ({Sum.inl i} : Set (I ⊕ J))ᶜ) := by
  rw [← (Pi.basisFun ℝ I).sum_repr x]
  apply Submodule.sum_mem
  intro k _
  by_cases hk : k = i
  · subst k
    simp [hx]
  · apply Submodule.smul_mem
    exact Submodule.subset_span ⟨.inl k, by simpa using hk, rfl⟩

/-- A nonzero entry in a row prevents its unit basis column from being a coloop. -/
theorem matrix_left_not_coloop (A : I → J → ℤ) (i : I) (j : J) (h : A i j ≠ 0) :
    ¬(matrixMatroid A).IsColoop (.inl i) := by
  rw [matrixMatroid, VectorMatroid.ofFamily_isColoop_iff, not_not]
  let S := Submodule.span ℝ (matrixColumns A '' ({Sum.inl i} : Set (I ⊕ J))ᶜ)
  have hc : (A i j : ℝ) ≠ 0 := by exact_mod_cast h
  have hv : matrixColumns A (.inr j) ∈ S := Submodule.subset_span ⟨.inr j, by simp, rfl⟩
  have hw : matrixColumns A (.inr j) - (A i j : ℝ) • matrixColumns A (.inl i) ∈ S :=
    zero_coordinate_mem_span_others A i _ (by simp [matrixColumns, Pi.basisFun_apply])
  have hm : (A i j : ℝ) • matrixColumns A (.inl i) ∈ S := by
    simpa using Submodule.sub_mem S hv hw
  have hi := Submodule.smul_mem S (A i j : ℝ)⁻¹ hm
  simpa [smul_smul, hc] using hi

/-- Isolated rows are actual coloops, as detected by their coordinate functional. -/
theorem matrix_zero_row_coloop (A : I → J → ℤ) (i : I) (hi : ∀ j, A i j = 0) :
    (matrixMatroid A).IsColoop (.inl i) := by
  rw [matrixMatroid, VectorMatroid.ofFamily_isColoop_iff]
  let g : (I → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj i
  have hs : Submodule.span ℝ (matrixColumns A '' ({Sum.inl i} : Set (I ⊕ J))ᶜ) ≤
      LinearMap.ker g := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    cases a with
    | inl k =>
      have hk : k ≠ i := by simpa using ha
      simp [g, matrixColumns, Pi.basisFun_apply, hk, (Ne.symm hk)]
    | inr j => simp [g, matrixColumns, hi j]
  intro h
  have hz := hs h
  have : (1 : ℝ) = 0 := by simpa [g, matrixColumns, Pi.basisFun_apply] using hz
  exact one_ne_zero this

/-- Isolated nonbasis columns are actual loops. -/
theorem matrix_zero_column_loop (A : I → J → ℤ) (j : J) (hj : ∀ i, A i j = 0) :
    (matrixMatroid A).IsLoop (.inr j) := by
  rw [matrixMatroid, VectorMatroid.ofFamily_isLoop_iff]
  ext i
  simp [matrixColumns, hj i]

/-- The row-coordinate projection used by an ordinary contraction of a basis
column. Its kernel will be proved exactly, not merely included in the desired span. -/
def eraseRowProjection (i : I) : (I → ℝ) →ₗ[ℝ] ({k : I // k ≠ i} → ℝ) where
  toFun := fun x k => x k.val
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem eraseRowProjection_kernel (i : I) :
    LinearMap.ker (eraseRowProjection i) =
      Submodule.span ℝ ({Pi.basisFun ℝ I i} : Set (I → ℝ)) := by
  apply le_antisymm
  · intro x hx
    have heq : x = x i • Pi.basisFun ℝ I i := by
      ext k
      by_cases hk : k = i
      · simp [hk, Pi.basisFun_apply]
      · have hz := congrFun hx ⟨k, hk⟩
        simpa [eraseRowProjection, Pi.basisFun_apply, hk, (Ne.symm hk)] using hz
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    rintro x rfl
    ext k
    simp [eraseRowProjection, Pi.basisFun_apply, k.property, (Ne.symm k.property)]

/-- The surviving labels when one basis row and its own basis label are removed. -/
def eraseRowLabels (i : I) : ({k : I // k ≠ i} ⊕ J) ↪ (I ⊕ J) :=
  ⟨Sum.map Subtype.val id, by
    intro x y h
    cases x <;> cases y <;> simp_all only [Sum.map_inl, Sum.map_inr,
      Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, Subtype.ext_iff, id_eq]⟩

/-- The surviving labels when one nonbasis column is deleted. -/
def eraseColumnLabels (j : J) : (I ⊕ {k : J // k ≠ j}) ↪ (I ⊕ J) :=
  ⟨Sum.map id Subtype.val, by
    intro x y h
    cases x <;> cases y <;> simp_all only [Sum.map_inl, Sum.map_inr,
      Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, Subtype.ext_iff, id_eq]⟩

@[simp] theorem eraseRowLabels_inl (i : I) (k : {k : I // k ≠ i}) :
    eraseRowLabels (J := J) i (.inl k) = .inl k.val := rfl

@[simp] theorem eraseRowLabels_inr (i : I) (j : J) :
    eraseRowLabels i (.inr j) = .inr j := rfl

@[simp] theorem eraseColumnLabels_inl (j : J) (i : I) :
    eraseColumnLabels j (.inl i) = .inl i := rfl

@[simp] theorem eraseColumnLabels_inr (j : J) (k : {k : J // k ≠ j}) :
    eraseColumnLabels (I := I) j (.inr k) = .inr k.val := rfl

@[simp] theorem range_eraseRowLabels (i : I) :
    Set.range (eraseRowLabels (J := J) i) = ({Sum.inl i} : Set (I ⊕ J))ᶜ := by
  ext a
  cases a with
  | inl k => simp [Set.mem_range, Subtype.exists, eq_comm]
  | inr j => simp [Set.mem_range]

@[simp] theorem range_eraseColumnLabels (j : J) :
    Set.range (eraseColumnLabels (I := I) j) = ({Sum.inr j} : Set (I ⊕ J))ᶜ := by
  ext a
  cases a with
  | inl i => simp [Set.mem_range]
  | inr k => simp [Set.mem_range, Subtype.exists, eq_comm]

/-- Deleting a nonbasis column is exactly ordinary matroid deletion, on all
independent subsets of the retained labels. -/
theorem matrix_delete_column (A : I → J → ℤ) (j : J) :
    matrixMatroid A ＼ ({Sum.inr j} : Set (I ⊕ J)) =
      (matrixMatroid (fun (i : I) (k : {k : J // k ≠ j}) => A i k.val)).mapEmbedding
        (eraseColumnLabels j) := by
  rw [matrixMatroid, VectorMatroid.ofFamily, VectorMatroid.delete_onSet, ← Set.compl_eq_univ_sdiff]
  symm
  rw [← range_eraseColumnLabels j]
  apply VectorMatroid.ofFamily_mapEmbedding_eq_onSet
  intro a
  cases a <;> rfl

/-- Contracting a basis label is exactly row deletion in the normalized matrix.
The proof uses the full quotient-space kernel identity above. -/
theorem matrix_contract_row (A : I → J → ℤ) (i : I) :
    matrixMatroid A ／ ({Sum.inl i} : Set (I ⊕ J)) =
      (matrixMatroid (fun k : {k : I // k ≠ i} => A k.val)).mapEmbedding
        (eraseRowLabels i) := by
  have hker : LinearMap.ker (eraseRowProjection i) =
      Submodule.span ℝ (matrixColumns A '' ({Sum.inl i} : Set (I ⊕ J))) := by
    rw [Set.image_singleton]
    exact eraseRowProjection_kernel i
  rw [matrixMatroid, VectorMatroid.ofFamily,
    VectorMatroid.contract_onSet _ (Set.subset_univ _) (eraseRowProjection i) hker,
    ← Set.compl_eq_univ_sdiff]
  symm
  rw [← range_eraseRowLabels i]
  apply VectorMatroid.ofFamily_mapEmbedding_eq_onSet
  intro a
  cases a with
  | inl k =>
    ext r
    rw [eraseRowLabels_inl]
    change (Pi.basisFun ℝ I k.val) r.val =
      (Pi.basisFun ℝ {k : I // k ≠ i} k) r
    simp [Pi.basisFun_apply, Pi.single_apply, Subtype.ext_iff, eq_comm]
  | inr j => rfl

/-- For an isolated basis row, contraction agrees with deletion because that
label is a coloop. -/
theorem matrix_delete_zero_row (A : I → J → ℤ) (i : I) (hi : ∀ j, A i j = 0) :
    matrixMatroid A ＼ ({Sum.inl i} : Set (I ⊕ J)) =
      (matrixMatroid (fun k : {k : I // k ≠ i} => A k.val)).mapEmbedding
        (eraseRowLabels i) := by
  rw [← Matroid.contract_eq_delete_of_subset_coloops
    (Set.singleton_subset_iff.mpr (matrix_zero_row_coloop A i hi))]
  exact matrix_contract_row A i

/-- The scalar information needed for the pruning argument. These hypotheses
are obtained from the actual one- and two-row minors of a uniformly unimodular
configuration, and are preserved by every row and column restriction. -/
structure SmallMinors (A : I → J → ℤ) : Prop where
  entry : ∀ i j, |A i j| ≤ 1
  two : ∀ i k j l, |A i j * A k l - A i l * A k j| ≤ 1

theorem SmallMinors.eraseRow {A : I → J → ℤ} (h : SmallMinors A) (i : I) :
    SmallMinors (fun k : {k : I // k ≠ i} => A k.val) :=
  ⟨fun k j => h.entry k.val j, fun k l j t => h.two k.val l.val j t⟩

theorem SmallMinors.eraseColumn {A : I → J → ℤ} (h : SmallMinors A) (j : J) :
    SmallMinors (fun (i : I) (k : {k : J // k ≠ j}) => A i k.val) :=
  ⟨fun i k => h.entry i k.val, fun i k l t => h.two i k l.val t.val⟩

/-- Row twins have one common integral sign, rather than unrelated signs in
their different columns. -/
theorem SmallMinors.row_sign {A : I → J → ℤ} (h : SmallMinors A) (i k : I)
    (hs : ∀ j, A i j ≠ 0 ↔ A k j ≠ 0) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ j, A i j = s * A k j := by
  have hz : ∀ j, A i j = 0 ↔ A k j = 0 := fun j => not_iff_not.mp (hs j)
  rcases signed_eq_of_same_support (A i) (A k) (h.entry i) (h.entry k) hz
    (fun j l => h.two i k j l) with heq | heq
  · exact ⟨1, Or.inl rfl, fun j => by simpa using congrFun heq j⟩
  · exact ⟨-1, Or.inr rfl, fun j => by simpa using congrFun heq j⟩

/-- Column twins likewise have one common integral sign. -/
theorem SmallMinors.column_sign {A : I → J → ℤ} (h : SmallMinors A) (j l : J)
    (hs : ∀ i, A i j ≠ 0 ↔ A i l ≠ 0) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ i, A i j = s * A i l := by
  have hz : ∀ i, A i j = 0 ↔ A i l = 0 := fun i => not_iff_not.mp (hs i)
  have hm : ∀ i k, |A i j * A k l - A k j * A i l| ≤ 1 := by
    intro i k
    simpa only [mul_comm (A k j) (A i l)] using h.two i k j l
  rcases signed_eq_of_same_support (fun i => A i j) (fun i => A i l)
    (fun i => h.entry i j) (fun i => h.entry i l) hz hm with heq | heq
  · exact ⟨1, Or.inl rfl, fun i => by simpa using congrFun heq i⟩
  · exact ⟨-1, Or.inr rfl, fun i => by simpa using congrFun heq i⟩

/-- A pendant nonbasis column and its adjacent unit column form an ordinary
parallel pair. The proof retains its actual sign. -/
theorem matrix_pendant_column_circuit (A : I → J → ℤ) (j : J) (i : I)
    (hj : ∀ k, A k j ≠ 0 ↔ k = i) :
    (matrixMatroid A).IsCircuit {Sum.inr j, Sum.inl i} := by
  have hc : (A i j : ℝ) ≠ 0 := by exact_mod_cast (hj i).mpr rfl
  apply VectorMatroid.pair_isCircuit_of_smul (e := Sum.inr j) (f := Sum.inl i)
    (matrixColumns A) (by simp) (A i j : ℝ) hc ((Pi.basisFun ℝ I).ne_zero i)
  ext k
  by_cases hk : k = i
  · simp [matrixColumns, hk, Pi.basisFun_apply]
  · have hz : A k j = 0 := by
      by_contra hn
      exact hk ((hj k).mp hn)
    simp [matrixColumns, hz, Pi.basisFun_apply, hk, (Ne.symm hk)]

/-- Nonzero twin columns form an ordinary parallel pair once the two-row
minor bounds have forced their common sign. -/
theorem matrix_twin_columns_circuit (A : I → J → ℤ) (hA : SmallMinors A)
    (j l : J) (hjl : j ≠ l) (hs : ∀ i, A i j ≠ 0 ↔ A i l ≠ 0)
    (i : I) (hi : A i l ≠ 0) :
    (matrixMatroid A).IsCircuit {Sum.inr j, Sum.inr l} := by
  obtain ⟨s, hsunit, hsign⟩ := hA.column_sign j l hs
  have hs0 : (s : ℝ) ≠ 0 := by rcases hsunit with rfl | rfl <;> norm_num
  have hv : matrixColumns A (.inr l) ≠ 0 := by
    intro hz
    have heq : (A i l : ℝ) = 0 := congrFun hz i
    exact hi (by exact_mod_cast heq)
  apply VectorMatroid.pair_isCircuit_of_smul (matrixColumns A) (by simpa using hjl)
    (s : ℝ) hs0 hv
  ext k
  change (A k j : ℝ) = (s : ℝ) * (A k l : ℝ)
  exact_mod_cast hsign k

/-- A pendant basis row gives an ordinary series pair with its sole adjacent
nonbasis column. Neither member is treated as a coloop. -/
theorem matrix_pendant_row_cocircuit (A : I → J → ℤ) (i : I) (j : J)
    (hi : ∀ l, A i l ≠ 0 ↔ l = j) :
    (matrixMatroid A).IsCocircuit {Sum.inl i, Sum.inr j} := by
  apply VectorMatroid.pair_isCocircuit_of_support (matrixColumns A) (by simp)
    (LinearMap.proj i)
  · simp [matrixColumns, Pi.basisFun_apply]
  · intro a hae haf
    cases a with
    | inl k =>
      have hk : k ≠ i := by simpa using hae
      simp [matrixColumns, Pi.basisFun_apply, hk, (Ne.symm hk)]
    | inr l =>
      have hl : l ≠ j := by simpa using haf
      have hz : A i l = 0 := by
        by_contra hn
        exact hl ((hi l).mp hn)
      simp [matrixColumns, hz]
  · exact matrix_left_not_coloop A i j ((hi j).mpr rfl)
  · exact matrix_right_not_coloop A j

/-- Nonzero twin basis rows give an ordinary series pair. A signed difference
of their coordinate functionals vanishes on every other column. -/
theorem matrix_twin_rows_cocircuit (A : I → J → ℤ) (hA : SmallMinors A)
    (i k : I) (hik : i ≠ k) (hs : ∀ j, A i j ≠ 0 ↔ A k j ≠ 0)
    (j : J) (hj : A k j ≠ 0) :
    (matrixMatroid A).IsCocircuit {Sum.inl i, Sum.inl k} := by
  obtain ⟨s, hsunit, hsign⟩ := hA.row_sign i k hs
  let g : (I → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj i - (s : ℝ) • LinearMap.proj k
  apply VectorMatroid.pair_isCocircuit_of_support (matrixColumns A) (by simpa using hik) g
  · simp [g, matrixColumns, Pi.basisFun_apply, hik, hik.symm]
  · intro a hae haf
    cases a with
    | inl r =>
      have hri : r ≠ i := by simpa using hae
      have hrk : r ≠ k := by simpa using haf
      simp [g, matrixColumns, Pi.basisFun_apply, hri, hri.symm, hrk, hrk.symm]
    | inr l =>
      have he : (A i l : ℝ) = (s : ℝ) * (A k l : ℝ) := by exact_mod_cast hsign l
      simp [g, matrixColumns, he]
  · exact matrix_left_not_coloop A i j ((hs j).mpr hj)
  · exact matrix_left_not_coloop A k j hj

/-- The forbidden induced configurations for the ordinary fundamental graph. -/
def MatrixForbidden (A : I → J → ℤ) : Prop :=
  ¬HasLongInducedCycle (supportGraph A) ∧ ¬Nonempty (InducedDomino (supportGraph A))

/-- Restricting rows and columns is an induced embedding of fundamental graphs. -/
def supportGraphEmbedding {I' : Type u} {J' : Type v} (A : I → J → ℤ)
    (r : I' ↪ I) (c : J' ↪ J) :
    supportGraph (fun i j => A (r i) (c j)) ↪g supportGraph A where
  toFun := Sum.map r c
  inj' := by
    intro x y h
    cases x <;> cases y <;> simp only [Sum.map_inl, Sum.map_inr,
      Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl] at h ⊢
    · exact r.injective h
    · exact c.injective h
  map_rel_iff' := by intro x y; cases x <;> cases y <;> rfl

theorem MatrixForbidden.restrict {A : I → J → ℤ} (h : MatrixForbidden A)
    {I' : Type u} {J' : Type v} [Fintype I'] [DecidableEq I'] [Fintype J'] [DecidableEq J']
    (r : I' ↪ I) (c : J' ↪ J) : MatrixForbidden (fun i j => A (r i) (c j)) := by
  let f := supportGraphEmbedding A r c
  exact ⟨fun h' => h.1 (h'.map f), fun ⟨d⟩ => h.2 ⟨d.map f⟩⟩

theorem MatrixForbidden.eraseRow {A : I → J → ℤ} (h : MatrixForbidden A) (i : I) :
    MatrixForbidden (fun k : {k : I // k ≠ i} => A k.val) :=
  h.restrict ⟨Subtype.val, Subtype.val_injective⟩ (Function.Embedding.refl J)

theorem MatrixForbidden.eraseColumn {A : I → J → ℤ} (h : MatrixForbidden A) (j : J) :
    MatrixForbidden (fun (i : I) (k : {k : J // k ≠ j}) => A i k.val) :=
  h.restrict (Function.Embedding.refl I) ⟨Subtype.val, Subtype.val_injective⟩

/-- The six elementary matrix reductions, with their exact support conditions.
This is a conclusion of the graph theorem, rather than a definition of the
series--parallel matroid class. -/
inductive MatrixReduction (A : I → J → ℤ) : Prop
  | zeroRow (i : I) (h : ∀ j, A i j = 0)
  | zeroColumn (j : J) (h : ∀ i, A i j = 0)
  | pendantRow (i : I) (j : J) (h : ∀ l, A i l ≠ 0 ↔ l = j)
  | pendantColumn (j : J) (i : I) (h : ∀ k, A k j ≠ 0 ↔ k = i)
  | twinRows (i k : I) (hne : i ≠ k) (h : ∀ j, A i j ≠ 0 ↔ A k j ≠ 0)
  | twinColumns (j l : J) (hne : j ≠ l) (h : ∀ i, A i j ≠ 0 ↔ A i l ≠ 0)

private theorem matrix_reduction_of_graph (A : I → J → ℤ)
    (h : HasReduction (supportGraph A)) : MatrixReduction A := by
  rcases h with ⟨v, hv⟩ | ⟨v, w, hv⟩ | ⟨v, w, hvw, hv⟩
  · cases v with
    | inl i =>
      apply MatrixReduction.zeroRow i
      intro j
      by_contra hn
      exact hv (.inr j) hn
    | inr j =>
      apply MatrixReduction.zeroColumn j
      intro i
      by_contra hn
      exact hv (.inl i) hn
  · cases v with
    | inl i =>
      cases w with
      | inl k => exact False.elim ((supportGraph_left_left A i k) ((hv _).mpr rfl))
      | inr j =>
        exact MatrixReduction.pendantRow i j (fun l => by simpa using hv (.inr l))
    | inr j =>
      cases w with
      | inl i =>
        exact MatrixReduction.pendantColumn j i (fun k => by simpa using hv (.inl k))
      | inr l => exact False.elim ((supportGraph_right_right A j l) ((hv _).mpr rfl))
  · cases v with
    | inl i =>
      cases w with
      | inl k =>
        exact MatrixReduction.twinRows i k (by simpa using hvw)
          (fun j => hv (.inr j))
      | inr j =>
        apply MatrixReduction.zeroRow i
        intro l
        by_contra hn
        exact supportGraph_right_right A j l ((hv (.inr l)).mp hn)
    | inr j =>
      cases w with
      | inl i =>
        apply MatrixReduction.zeroColumn j
        intro k
        by_contra hn
        exact supportGraph_left_left A i k ((hv (.inl k)).mp hn)
      | inr l =>
        exact MatrixReduction.twinColumns j l (by simpa using hvw)
          (fun i => hv (.inl i))

/-- Every nonempty forbidden-subgraph-free fundamental graph admits one of the
six exact matrix reductions. -/
theorem matrix_has_reduction (A : I → J → ℤ) [Nonempty (I ⊕ J)]
    (h : MatrixForbidden A) : MatrixReduction A :=
  matrix_reduction_of_graph A
    (hasReduction_of_forbidden (supportGraph A) (supportColor A) h.1 h.2)

/-- The matrix elimination theorem, proved by induction on the unrestricted
number of row and column labels. Every step is an ordinary matroid loop,
coloop, eligible parallel extension, or eligible series extension. -/
theorem matrix_finite_seriesParallel_aux :
    ∀ n : ℕ, ∀ (I : Type u) (J : Type v) [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J], Fintype.card I + Fintype.card J = n →
      ∀ A : I → J → ℤ, SmallMinors A → MatrixForbidden A →
        FiniteSeriesParallel (matrixMatroid A) := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro I J _ _ _ _ hcard A hA hforbid
    have row (i : I) :
        FiniteSeriesParallel (matrixMatroid (fun k : {k : I // k ≠ i} => A k.val)) := by
      apply ih (Fintype.card {k : I // k ≠ i} + Fintype.card J) ?_
        {k : I // k ≠ i} J rfl _ (hA.eraseRow i) (hforbid.eraseRow i)
      have hh : Fintype.card {k : I // k ≠ i} < Fintype.card I :=
        Fintype.card_subtype_lt (x := i) (by simp)
      omega
    have column (j : J) :
        FiniteSeriesParallel (matrixMatroid (fun (i : I) (k : {k : J // k ≠ j}) =>
          A i k.val)) := by
      apply ih (Fintype.card I + Fintype.card {k : J // k ≠ j}) ?_
        I {k : J // k ≠ j} rfl _ (hA.eraseColumn j) (hforbid.eraseColumn j)
      have hh : Fintype.card {k : J // k ≠ j} < Fintype.card J :=
        Fintype.card_subtype_lt (x := j) (by simp)
      omega
    rcases isEmpty_or_nonempty (I ⊕ J) with he | hne
    · letI := he
      exact FiniteSeriesParallel.of_isEmpty (matrixMatroid A)
    · letI := hne
      cases matrix_has_reduction A hforbid with
      | zeroRow i hi =>
        exact (row i).addColoop (eraseRowLabels i) (.inl i) (range_eraseRowLabels i)
          (matrixMatroid_ground A) (matrix_zero_row_coloop A i hi)
          (matrix_delete_zero_row A i hi)
      | zeroColumn j hj =>
        exact (column j).addLoop (eraseColumnLabels j) (.inr j) (range_eraseColumnLabels j)
          (matrixMatroid_ground A) (matrix_zero_column_loop A j hj)
          (matrix_delete_column A j)
      | pendantRow i j hi =>
        apply (row i).series (eraseRowLabels i) (.inl i) (range_eraseRowLabels i)
          (matrixMatroid_ground A) (.inr j)
          (matrix_right_not_coloop (fun k : {k : I // k ≠ i} => A k.val) j)
        · exact matrix_pendant_row_cocircuit A i j hi
        · exact matrix_contract_row A i
      | pendantColumn j i hj =>
        apply (column j).parallel (eraseColumnLabels j) (.inr j) (range_eraseColumnLabels j)
          (matrixMatroid_ground A) (.inl i)
          (matrix_left_nonloop (fun (i : I) (k : {k : J // k ≠ j}) => A i k.val) i)
        · exact matrix_pendant_column_circuit A j i hj
        · exact matrix_delete_column A j
      | twinRows i k hik hs =>
        by_cases hn : ∃ j, A k j ≠ 0
        · obtain ⟨j, hj⟩ := hn
          apply (row i).series (eraseRowLabels i) (.inl i) (range_eraseRowLabels i)
            (matrixMatroid_ground A) (.inl ⟨k, hik.symm⟩)
            (matrix_left_not_coloop (fun r : {r : I // r ≠ i} => A r.val)
              ⟨k, hik.symm⟩ j hj)
          · exact matrix_twin_rows_cocircuit A hA i k hik hs j hj
          · exact matrix_contract_row A i
        · have hz : ∀ j, A i j = 0 := by
            intro j
            by_contra h
            exact hn ⟨j, (hs j).mp h⟩
          exact (row i).addColoop (eraseRowLabels i) (.inl i) (range_eraseRowLabels i)
            (matrixMatroid_ground A) (matrix_zero_row_coloop A i hz)
            (matrix_delete_zero_row A i hz)
      | twinColumns j l hjl hs =>
        by_cases hn : ∃ i, A i l ≠ 0
        · obtain ⟨i, hi⟩ := hn
          apply (column j).parallel (eraseColumnLabels j) (.inr j) (range_eraseColumnLabels j)
            (matrixMatroid_ground A) (.inr ⟨l, hjl.symm⟩)
            (matrix_right_nonloop (fun (i : I) (k : {k : J // k ≠ j}) => A i k.val)
              i ⟨l, hjl.symm⟩ hi)
          · exact matrix_twin_columns_circuit A hA j l hjl hs i hi
          · exact matrix_delete_column A j
        · have hz : ∀ i, A i j = 0 := by
            intro i
            by_contra h
            exact hn ⟨i, (hs i).mp h⟩
          exact (column j).addLoop (eraseColumnLabels j) (.inr j) (range_eraseColumnLabels j)
            (matrixMatroid_ground A) (matrix_zero_column_loop A j hz)
            (matrix_delete_column A j)

/-- A ternary integral matrix with bounded two-row minors and no induced
long cycle or domino has a standard series--parallel represented matroid.
No excluded-minor characterization is used as an axiom or as a definition. -/
theorem matrix_finite_seriesParallel (A : I → J → ℤ) (hA : SmallMinors A)
    (hforbid : MatrixForbidden A) : FiniteSeriesParallel (matrixMatroid A) :=
  matrix_finite_seriesParallel_aux (Fintype.card I + Fintype.card J) I J rfl A hA hforbid

#print axioms Unimodular.SeriesParallel.matrix_finite_seriesParallel

end
end Unimodular.SeriesParallel
