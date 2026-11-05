module
public import schur_tableau_bridge
public import schur_quotient_count
public import schur_row_counts
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Order.Interval.Finset.Nat

-- Generated verification output directories.
run_cmd Lean.Elab.Command.liftIO do
  IO.FS.createDirAll ".lake/reports/audit"


@[expose] public section

/-!
# Schur Hilbert series and genuine symmetric bitableaux

The first section proves Corollary 5.3, including every endpoint coefficient
and the ordinary determinantal specialization for all rank bounds. The next
four sections establish degreewise counts, paired-column determinant products,
their exact scores, and injectivity of their generic Gram exponents.
All public names retain the namespace `FourPapers.Symmetric.Schur`.
-/

/-! ## SchurHilbertSeries -/
set_option autoImplicit false
set_option maxHeartbeats 1800000

noncomputable section

/-!
# The Schur expansion of the endpoint-graded Hilbert series

The Schur polynomial is defined independently of monomials in the symmetric
matrix: it is the finite content-generating polynomial of all semistandard
tableaux of a prescribed Young diagram, in the alphabet `Fin n`.  Its row-list
representation is equivalent to the cell fillings used in the insertion proof.
The final identity is coefficientwise in every endpoint multidegree, which is
the equality of multigraded formal Hilbert series in Corollary 5.3.

-/

namespace FourPapers.Symmetric.Schur

open MvPolynomial Finsupp HigherSpecht TauCeti Pivot
open scoped BigOperators

universe u

/-- The usual bounded semistandard tableaux of an independently given shape.
Rows are nonempty and weakly increasing, columns are strictly increasing,
and the specified row lengths are exactly the rows of the Young diagram. -/
def ShapeTableaux (n : ℕ) (μ : YoungDiagram) :=
  {rows : List (List ℕ) // rows.IsTableauRows ∧
    rows.map List.length = μ.rowLens ∧ ∀ x ∈ rows.flatten, x < n}

namespace ShapeTableaux

variable {n : ℕ} {μ : YoungDiagram}

def cell (T : ShapeTableaux n μ) (c : ↥μ.cells) : Fin n :=
  ⟨rowsCellEntry T.property.2.1 c,
    T.property.2.2 _ (rowsCellEntry_mem T.property.2.1 c)⟩

/-- The bounded cell entries recover the entire row tableau. -/
theorem cell_injective : Function.Injective (@cell n μ) := by
  intro T U h
  apply Subtype.ext
  have hv : (fun c => (T.cell c).val) = fun c => (U.cell c).val :=
    funext (fun c => congrArg Fin.val (congrFun h c))
  apply List.ext_getElem
  · simpa only [List.length_map] using congrArg List.length (T.property.2.1.trans U.property.2.1.symm)
  · intro i hi hj
    apply List.ext_getElem
    · exact (rows_cell_length T.property.2.1 hi).trans
        (rows_cell_length U.property.2.1 hj).symm
    · intro j hji hjj
      have hc : (i,j) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by
        rw [←rows_cell_length T.property.2.1 hi]
        exact hji)
      exact congrFun hv ⟨(i,j),hc⟩

instance : Finite (ShapeTableaux n μ) := Finite.of_injective cell cell_injective

noncomputable instance : Fintype (ShapeTableaux n μ) := Fintype.ofFinite _

/-- Column strictness bounds the number of nonempty rows by the alphabet size. -/
theorem height_le (T : ShapeTableaux n μ) : μ.rowLens.length ≤ n := by
  let S := weakFillingOfRows T.property.1 T.property.2.1
  have hbound : ∀ c, S c < n :=
    weakFillingOfRows_bound T.property.1 T.property.2.1 T.property.2.2
  have hrow : ∀ i (hi : (i, 0) ∈ μ), i ≤ S ⟨(i, 0), hi⟩ := by
    intro i
    induction i with
    | zero => intro hi; exact Nat.zero_le _
    | succ i ih =>
        intro hi
        have hp : (i, 0) ∈ μ := μ.up_left_mem (Nat.le_succ i) le_rfl hi
        have hprev := ih hp
        have hstrict := S.col_strict (Nat.lt_succ_self i) hi
        exact Nat.succ_le_of_lt (lt_of_le_of_lt hprev hstrict)
  rw [YoungDiagram.length_rowLens]
  by_cases hzero : μ.colLen 0 = 0
  · omega
  · have hi : (μ.colLen 0 - 1, 0) ∈ μ :=
      YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    have hlo := hrow _ hi
    have hhi := hbound ⟨(μ.colLen 0 - 1, 0), hi⟩
    omega

end ShapeTableaux

/-- The exponent of a letter is its literal number of occurrences. -/
def rowContent (n : ℕ) (rows : List (List ℕ)) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => rows.flatten.count i.val)

@[simp] theorem rowContent_apply (n : ℕ) (rows : List (List ℕ)) (i : Fin n) :
    rowContent n rows i = rows.flatten.count i.val := by
  simp [rowContent]

/-- The ordinary Schur polynomial, defined by its semistandard-tableau
generating sum. The diagram and alphabet are independent of insertion. -/
def schurPolynomial (n : ℕ) (μ : YoungDiagram) : MvPolynomial (Fin n) ℕ :=
  ∑ T : ShapeTableaux n μ, monomial (rowContent n T.val) 1

theorem schurPolynomial_coeff (n : ℕ) (μ : YoungDiagram) (d : Fin n →₀ ℕ) :
    (schurPolynomial n μ).coeff d =
      {T : ShapeTableaux n μ | rowContent n T.val = d}.ncard := by
  classical
  rw [← Set.fintypeCard_eq_ncard]
  simp only [schurPolynomial, coeff_sum, coeff_monomial]
  rw [Fintype.card_subtype, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro T hT
  simp only [Set.mem_ofPred_eq, eq_comm]

private theorem list_content_apply {n : ℕ} (xs : List (Fin n)) (i : Fin n) :
    (xs.map (fun x => Finsupp.single x 1)).sum i = xs.count i := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      by_cases hxi : x = i
      · subst x
        simp [ih, Nat.add_comm]
      · simp [ih, Finsupp.single_apply, hxi, List.count_cons_of_ne hxi]

private theorem sum_map_toMultiset {α A : Type*} [AddCommMonoid A]
    (m : α →₀ ℕ) (f : α → A) :
    (m.toMultiset.map f).sum = m.sum (fun a k => k • f a) := by
  classical
  refine m.induction ?_ ?_
  · simp
  · intro a k m ha hk ih
    simp only [Finsupp.toMultiset_add, Multiset.map_add, Multiset.sum_add,
      Finsupp.toMultiset_single, ih]
    have hmap : (k • ({a} : Multiset α)).map f = k • ({f a} : Multiset A) := by
      simpa only [Multiset.coe_mapAddMonoidHom, Multiset.map_singleton] using
        (Multiset.mapAddMonoidHom f).map_nsmul k ({a} : Multiset α)
    rw [hmap, Multiset.sum_nsmul, Multiset.sum_singleton]
    rw [Finsupp.sum_add_index' (h := fun a k => k • f a)
      (fun a => zero_nsmul (f a)) (fun a b c => add_nsmul (f a) b c),
      Finsupp.sum_single_index (zero_nsmul (f a))]

private theorem endpointWord_content {n : ℕ} (es : List (Entry n)) :
    ((endpointWord (es.map (fun e => (e.val.2, e.val.1)))).map
      (fun x => Finsupp.single x 1)).sum = (es.map endpointWeight).sum := by
  induction es with
  | nil => simp [endpointWord]
  | cons e es ih =>
      simp only [endpointWord] at ih
      simp [endpointWord, endpointWeight, ih, add_comm, add_left_comm, add_assoc]

/-- The content in the Schur generating function is exactly the original
endpoint grading, including the doubled contribution of a diagonal variable. -/
theorem pairedTableau_content_weight {n : ℕ} (m : Entry n →₀ ℕ) :
    rowContent n (pairedTableauNat m) = Finsupp.weight endpointWeight m := by
  classical
  have hword :
      ((endpointWord (monomialPairs m)).map (fun x => Finsupp.single x 1)).sum =
        Finsupp.weight endpointWeight m := by
    rw [monomialPairs, endpointWord_content]
    change ((m.toMultiset.sort (· ≤ ·)).map endpointWeight).sum = _
    have hsort := Multiset.sort_eq m.toMultiset (· ≤ ·)
    have hsum := congrArg (fun l : Multiset (Entry n) => (l.map endpointWeight).sum) hsort
    simpa only [Multiset.map_coe, Multiset.sum_coe, sum_map_toMultiset,
      Finsupp.weight_apply] using hsum
  have hperm := (pairedTableau_content m).map (fun x => Finsupp.single x 1)
  have hsum := hperm.sum_eq.trans hword
  ext i
  rw [rowContent_apply]
  change (((pairedTableau m).map (List.map Fin.val)).flatten).count i.val = _
  rw [← List.map_flatten, List.count_map_of_injective _ _ Fin.val_injective]
  rw [← list_content_apply, hsum]

/-- Doubling a partition means doubling every row length. -/
def doubleShape (μ : YoungDiagram) : YoungDiagram :=
  YoungDiagram.ofRowLens (μ.rowLens.map (fun x => 2 * x))
    ((List.pairwise_map.mpr (μ.rowLens_sorted.pairwise.imp
      (fun {_ _} h => Nat.mul_le_mul_left 2 h))).sortedGE)

@[simp] theorem doubleShape_rowLens (μ : YoungDiagram) :
    (doubleShape μ).rowLens = μ.rowLens.map (fun x => 2 * x) := by
  apply YoungDiagram.rowLens_ofRowLens_eq_self
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact Nat.mul_pos (by omega) (μ.pos_of_mem_rowLens y hy)

private theorem even_length_mem {α : Type*} {rows : List (List α)}
    (heven : EvenRows rows) {row : List α} (hrow : row ∈ rows) : Even row.length := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hrow
  have h : ∃ k, rows[i].length = k + k := by
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      using heven i
  obtain ⟨k, hk⟩ := h
  exact ⟨k, hk⟩

/-- The half-shape of an arbitrary even-row semistandard tableau. -/
def tableauHalfShape {n : ℕ} (T : EvenSemistandardTableaux n) : YoungDiagram :=
  YoungDiagram.ofRowLens (T.val.map (fun row => row.length / 2)) (by
    have h : ((T.val.map List.length).map (fun x => x / 2)).SortedGE :=
      (List.pairwise_map.mpr (T.property.1.sortedGE_map_length.pairwise.imp
        (fun {_ _} h => Nat.div_le_div_right h))).sortedGE
    simpa only [List.map_map, Function.comp_def] using h)

@[simp] theorem tableauHalfShape_rowLens {n : ℕ} (T : EvenSemistandardTableaux n) :
    (tableauHalfShape T).rowLens = T.val.map (fun row => row.length / 2) := by
  apply YoungDiagram.rowLens_ofRowLens_eq_self
  intro x hx
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hx
  have hp : 0 < row.length := List.length_pos_iff.mpr
    (fun he => T.property.1.nil_notMem (he ▸ hrow))
  obtain ⟨k, hk⟩ := even_length_mem T.property.2.1 hrow
  omega

private theorem rowLens_injective : Function.Injective YoungDiagram.rowLens := by
  intro μ ν h
  apply YoungDiagram.equivListRowLens.injective
  exact Subtype.ext h

theorem double_tableauHalfShape {n : ℕ} (T : EvenSemistandardTableaux n) :
    (doubleShape (tableauHalfShape T)).rowLens = T.val.map List.length := by
  rw [doubleShape_rowLens, tableauHalfShape_rowLens, List.map_map]
  apply List.map_congr_left
  intro row hrow
  obtain ⟨k, hk⟩ := even_length_mem T.property.2.1 hrow
  dsimp only [Function.comp_def]
  omega

theorem tableauHalfShape_eq_iff {n : ℕ} (T : EvenSemistandardTableaux n)
    (μ : YoungDiagram) :
    tableauHalfShape T = μ ↔ T.val.map List.length = (doubleShape μ).rowLens := by
  constructor
  · intro h
    rw [← h]
    exact (double_tableauHalfShape T).symm
  · intro h
    apply rowLens_injective
    rw [tableauHalfShape_rowLens]
    have hh := congrArg (List.map (fun x => x / 2)) h
    have hcancel (x : ℕ) : 2 * x / 2 = x :=
      Nat.mul_div_cancel_left x (by omega)
    simpa only [doubleShape_rowLens, List.map_map, Function.comp_def,
      hcancel, List.map_id_fun', id] using hh

theorem evenRows_of_doubleShape {n : ℕ} {μ : YoungDiagram}
    (T : ShapeTableaux n (doubleShape μ)) : EvenRows T.val := by
  intro i
  have hlen : (T.val.getD i []).length =
      ((doubleShape μ).rowLens.getD i 0) := by
    rw [← List.getD_map T.val [] List.length, T.property.2.1]
    rfl
  rw [hlen, doubleShape_rowLens]
  have hmap := List.getD_map μ.rowLens 0 (fun x => 2 * x) (n := i)
  simp only [Nat.mul_zero] at hmap
  rw [hmap]
  exact ⟨μ.rowLens.getD i 0, by omega⟩

def shapeTableauToEven {n : ℕ} {μ : YoungDiagram}
    (T : ShapeTableaux n (doubleShape μ)) : EvenSemistandardTableaux n :=
  ⟨T.val, T.property.1, evenRows_of_doubleShape T, T.property.2.2⟩

@[simp] theorem tableauHalfShape_shapeTableauToEven {n : ℕ} {μ : YoungDiagram}
    (T : ShapeTableaux n (doubleShape μ)) :
    tableauHalfShape (shapeTableauToEven T) = μ :=
  (tableauHalfShape_eq_iff _ _).mpr T.property.2.1

theorem tableauHalfShape_height {n : ℕ} (T : EvenSemistandardTableaux n) :
    (tableauHalfShape T).rowLens.length ≤ n := by
  let U : ShapeTableaux n (doubleShape (tableauHalfShape T)) :=
    ⟨T.val, T.property.1, (double_tableauHalfShape T).symm, T.property.2.2⟩
  simpa only [doubleShape_rowLens, List.length_map] using U.height_le

theorem tableauHalfShape_pairedTableau {n : ℕ} (m : Entry n →₀ ℕ) :
    (tableauHalfShape (pairedTableauMap m)).rowLens = halfShape m := by
  rw [tableauHalfShape_rowLens]
  simp only [pairedTableauMap, pairedTableauNat, halfShape,
    List.map_map, Function.comp_def, List.length_map]

/-- The tableau side of the symbolic-power standard-monomial condition. -/
def GoodTableaux (n t s : ℕ) (d : Fin n →₀ ℕ) : Set (EvenSemistandardTableaux n) :=
  {T | ((tableauHalfShape T).rowLens.drop (t - 1)).sum < s ∧ rowContent n T.val = d}

theorem pairedTableau_mem_good_iff {n t s : ℕ} (d : Fin n →₀ ℕ)
    (m : Entry n →₀ ℕ) :
    pairedTableauMap m ∈ GoodTableaux n t s d ↔
      gamma t m < s ∧ Finsupp.weight endpointWeight m = d := by
  change ((tableauHalfShape (pairedTableauMap m)).rowLens.drop (t - 1)).sum < s ∧
      rowContent n (pairedTableauNat m) = d ↔ _
  simp only [tableauHalfShape_pairedTableau, pairedTableau_content_weight,
    gamma]

theorem goodTableaux_eq_image {n t s : ℕ} (d : Fin n →₀ ℕ) :
    GoodTableaux n t s d = pairedTableauMap ''
      {m : Entry n →₀ ℕ | gamma t m < s ∧
        Finsupp.weight endpointWeight m = d} := by
  ext T
  constructor
  · intro hT
    obtain ⟨m, rfl⟩ := pairedTableauMap_bijective.surjective T
    exact ⟨m, (pairedTableau_mem_good_iff d m).mp hT, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact (pairedTableau_mem_good_iff d m).mpr hm

theorem goodTableaux_finite {n t s : ℕ} (d : Fin n →₀ ℕ) :
    (GoodTableaux n t s d).Finite := by
  rw [goodTableaux_eq_image]
  exact ((endpointWeight_fibers_finite d).subset (fun _ h => h.2)).image _

theorem standardMonomials_ncard_eq_good {n t s : ℕ} (d : Fin n →₀ ℕ) :
    {m : Entry n →₀ ℕ | gamma t m < s ∧
      Finsupp.weight endpointWeight m = d}.ncard =
        (GoodTableaux n t s d).ncard := by
  rw [goodTableaux_eq_image]
  exact (Set.ncard_image_of_injective _ pairedTableauMap_bijective.injective).symm

private theorem finite_ncard_eq_finsum_fibers {α β : Type*} (s : Set α)
    (hs : s.Finite) (f : α → β) :
    s.ncard = ∑ᶠ b : β, {a : α | a ∈ s ∧ f a = b}.ncard := by
  classical
  let sf := hs.toFinset
  have hfiber (b : β) : {a : α | a ∈ s ∧ f a = b}.ncard =
      (sf.filter (fun a => f a = b)).card := by
    have he : {a : α | a ∈ s ∧ f a = b} =
        (sf.filter (fun a => f a = b) : Set α) := by
      ext a
      simp only [Finset.mem_coe, Finset.mem_filter, sf, hs.mem_toFinset,
        Set.mem_ofPred_eq]
    rw [he, Set.ncard_coe_finset]
  have hsupp : Function.support (fun b : β => {a : α | a ∈ s ∧ f a = b}.ncard) ⊆
      (sf.image f : Set β) := by
    intro b hb
    by_contra hnot
    have he : {a : α | a ∈ s ∧ f a = b} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro a ⟨ha, hab⟩
      apply hnot
      exact Finset.mem_image.mpr ⟨a, hs.mem_toFinset.mpr ha, hab⟩
    have hz : {a : α | a ∈ s ∧ f a = b}.ncard = 0 := by rw [he]; simp
    exact hb hz
  rw [finsum_eq_finsetSum_of_support_subset _ hsupp]
  simp_rw [hfiber]
  exact (Set.ncard_eq_toFinset_card s hs).trans (Finset.card_eq_sum_card_image f sf)

/-- The partitions occurring in Corollary 5.3: at most `n` nonzero rows,
and fewer than `s` boxes in rows `t,t+1,...` (one-based notation). -/
def AllowedShape (n t s : ℕ) (μ : YoungDiagram) : Prop :=
  μ.rowLens.length ≤ n ∧ (μ.rowLens.drop (t - 1)).sum < s

instance (n t s : ℕ) (μ : YoungDiagram) : Decidable (AllowedShape n t s μ) := by
  unfold AllowedShape
  infer_instance

theorem goodTableaux_shape_fiber (n t s : ℕ) (d : Fin n →₀ ℕ) (μ : YoungDiagram) :
    {T : EvenSemistandardTableaux n |
      T ∈ GoodTableaux n t s d ∧ tableauHalfShape T = μ}.ncard =
      if AllowedShape n t s μ then (schurPolynomial n (doubleShape μ)).coeff d else 0 := by
  classical
  by_cases hμ : AllowedShape n t s μ
  · rw [ite_eq_left hμ, schurPolynomial_coeff]
    apply Set.ncard_congr (fun T hT =>
      (⟨T.val, T.property.1, (tableauHalfShape_eq_iff T μ).mp hT.2,
        T.property.2.2⟩ : ShapeTableaux n (doubleShape μ)))
    · intro T hT
      exact hT.1.2
    · intro T U hT hU hTU
      apply Subtype.ext
      exact congrArg (fun V : ShapeTableaux n (doubleShape μ) => V.val) hTU
    · intro U hU
      let T := shapeTableauToEven U
      have hshape : tableauHalfShape T = μ := tableauHalfShape_shapeTableauToEven U
      have hgood : T ∈ GoodTableaux n t s d := by
        refine ⟨?_, hU⟩
        change ((tableauHalfShape T).rowLens.drop (t - 1)).sum < s
        rw [hshape]
        exact hμ.2
      refine ⟨T, ⟨hgood, hshape⟩, ?_⟩
      exact Subtype.ext rfl
  · rw [ite_eq_right hμ]
    have he : {T : EvenSemistandardTableaux n |
        T ∈ GoodTableaux n t s d ∧ tableauHalfShape T = μ} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro T ⟨hT, hshape⟩
      apply hμ
      constructor
      · rw [← hshape]
        exact tableauHalfShape_height T
      · simpa only [hshape] using hT.1
    rw [he]
    exact Set.ncard_empty _

/-- Each coefficient of the displayed Schur series has finite support in
the set of partitions. Thus the `finsum` below is a genuine finite coefficient
sum, including degrees for which no tableau exists. -/
theorem schur_coefficient_support_finite (n t s : ℕ) (d : Fin n →₀ ℕ) :
    (Function.support (fun μ : YoungDiagram =>
      if AllowedShape n t s μ then (schurPolynomial n (doubleShape μ)).coeff d else 0)).Finite := by
  classical
  apply ((goodTableaux_finite (t := t) (s := s) d).image tableauHalfShape).subset
  intro μ hμ
  change (if AllowedShape n t s μ then
    (schurPolynomial n (doubleShape μ)).coeff d else 0) ≠ 0 at hμ
  rw [← goodTableaux_shape_fiber n t s d μ] at hμ
  by_contra hnot
  have he : {T : EvenSemistandardTableaux n |
      T ∈ GoodTableaux n t s d ∧ tableauHalfShape T = μ} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro T ⟨hT, hshape⟩
    exact hnot ⟨T, hT, hshape⟩
  exact hμ (by rw [he]; simp)

/-- A locally finite Schur series. Its coefficients are summed separately;
the support finiteness theorem above ensures this is the usual formal sum. -/
def schurHilbertSeries (n t s : ℕ) : MvPowerSeries (Fin n) ℕ := by
  classical
  exact fun d => ∑ᶠ μ : YoungDiagram, if AllowedShape n t s μ then
    (schurPolynomial n (doubleShape μ)).coeff d else 0

/-- The endpoint-graded Hilbert series of the actual polynomial quotient. -/
def quotientHilbertSeries (n : ℕ) (K : Type u) [Field K]
    (I : Ideal (CoordinateRing n K)) : MvPowerSeries (Fin n) ℕ :=
  fun d => Module.finrank K (quotientPiece I endpointWeight d)

theorem tail_sum_lt_one_iff (μ : YoungDiagram) (q : ℕ) :
    (μ.rowLens.drop q).sum < 1 ↔ μ.rowLens.length ≤ q := by
  constructor
  · intro h
    cases hd : μ.rowLens.drop q with
    | nil => exact List.drop_eq_nil_iff.mp hd
    | cons x xs =>
        have hx : x ∈ μ.rowLens := List.mem_of_mem_drop
          (by rw [hd]; exact List.mem_cons_self)
        have hp := μ.pos_of_mem_rowLens x hx
        simp only [hd, List.sum_cons] at h
        omega
  · intro h
    rw [List.drop_eq_nil_of_le h]
    simp

theorem allowedShape_succ_one_iff {n q : ℕ} (hq : q ≤ n) (μ : YoungDiagram) :
    AllowedShape n (q + 1) 1 μ ↔ μ.rowLens.length ≤ q := by
  simp only [AllowedShape, Nat.add_sub_cancel, tail_sum_lt_one_iff]
  exact ⟨And.right, fun h => ⟨h.trans hq, h⟩⟩

/-- The formal Schur series for an ordinary rank-`q` determinantal quotient. -/
def rankSchurSeries (n q : ℕ) : MvPowerSeries (Fin n) ℕ := by
  classical
  exact fun d => ∑ᶠ μ : YoungDiagram, if μ.rowLens.length ≤ q then
    (schurPolynomial n (doubleShape μ)).coeff d else 0

theorem contentTableaux_eq_image {n : ℕ} (d : Fin n →₀ ℕ) :
    {T : EvenSemistandardTableaux n | rowContent n T.val = d} =
      pairedTableauMap '' {m : Entry n →₀ ℕ | Finsupp.weight endpointWeight m = d} := by
  ext T
  constructor
  · intro hT
    obtain ⟨m, rfl⟩ := pairedTableauMap_bijective.surjective T
    refine ⟨m, ?_, rfl⟩
    change Finsupp.weight endpointWeight m = d
    rw [← pairedTableau_content_weight]
    exact hT
  · rintro ⟨m, hm, rfl⟩
    exact (pairedTableau_content_weight m).trans hm

theorem contentTableaux_finite {n : ℕ} (d : Fin n →₀ ℕ) :
    {T : EvenSemistandardTableaux n | rowContent n T.val = d}.Finite := by
  rw [contentTableaux_eq_image]
  exact (endpointWeight_fibers_finite d).image _

theorem contentTableaux_shape_fiber (n : ℕ) (d : Fin n →₀ ℕ) (μ : YoungDiagram) :
    {T : EvenSemistandardTableaux n |
      rowContent n T.val = d ∧ tableauHalfShape T = μ}.ncard =
      (schurPolynomial n (doubleShape μ)).coeff d := by
  classical
  rw [schurPolynomial_coeff]
  apply Set.ncard_congr (fun T hT =>
    (⟨T.val, T.property.1, (tableauHalfShape_eq_iff T μ).mp hT.2,
      T.property.2.2⟩ : ShapeTableaux n (doubleShape μ)))
  · intro T hT
    exact hT.1
  · intro T U hT hU hTU
    apply Subtype.ext
    exact congrArg (fun V : ShapeTableaux n (doubleShape μ) => V.val) hTU
  · intro U hU
    exact ⟨shapeTableauToEven U, ⟨hU, tableauHalfShape_shapeTableauToEven U⟩,
      Subtype.ext rfl⟩

/-- Even without a row or tail restriction, a fixed endpoint coefficient
receives contributions from only finitely many doubled Schur shapes. -/
theorem all_schur_coefficient_support_finite (n : ℕ) (d : Fin n →₀ ℕ) :
    (Function.support (fun μ : YoungDiagram =>
      (schurPolynomial n (doubleShape μ)).coeff d)).Finite := by
  classical
  apply ((contentTableaux_finite d).image tableauHalfShape).subset
  intro μ hμ
  change (schurPolynomial n (doubleShape μ)).coeff d ≠ 0 at hμ
  rw [← contentTableaux_shape_fiber n d μ] at hμ
  by_contra hnot
  have he : {T : EvenSemistandardTableaux n |
      rowContent n T.val = d ∧ tableauHalfShape T = μ} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro T ⟨hT, hshape⟩
    exact hnot ⟨T, hT, hshape⟩
  exact hμ (by rw [he]; simp)

/-- The unrestricted-rank specialization is a locally finite formal sum
for every `q`, including `q ≥ n` and the empty alphabet. -/
theorem rank_schur_coefficient_support_finite (n q : ℕ) (d : Fin n →₀ ℕ) :
    (Function.support (fun μ : YoungDiagram =>
      if μ.rowLens.length ≤ q then
        (schurPolynomial n (doubleShape μ)).coeff d else 0)).Finite := by
  classical
  apply (all_schur_coefficient_support_finite n d).subset
  intro μ hμ
  change (schurPolynomial n (doubleShape μ)).coeff d ≠ 0
  intro hz
  apply hμ
  simp only [hz, ite_self]

theorem contentTableaux_shape_fiber_of_ge (n q : ℕ) (hnq : n ≤ q)
    (d : Fin n →₀ ℕ) (μ : YoungDiagram) :
    {T : EvenSemistandardTableaux n |
      rowContent n T.val = d ∧ tableauHalfShape T = μ}.ncard =
      if μ.rowLens.length ≤ q then (schurPolynomial n (doubleShape μ)).coeff d else 0 := by
  classical
  by_cases hμ : μ.rowLens.length ≤ q
  · rw [ite_eq_left hμ]
    exact contentTableaux_shape_fiber n d μ
  · rw [ite_eq_right hμ]
    have he : {T : EvenSemistandardTableaux n |
        rowContent n T.val = d ∧ tableauHalfShape T = μ} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro T ⟨hT, hshape⟩
      apply hμ
      rw [← hshape]
      exact (tableauHalfShape_height T).trans hnq
    rw [he]
    exact Set.ncard_empty _

end FourPapers.Symmetric.Schur

namespace FourPapers.Symmetric.Schur

open TauCeti Pivot

universe u

/-- **Corollary 5.3, Schur Hilbert series.** This is equality in every
endpoint multidegree of the actual quotient by the localization-defined
symbolic power. The right side uses ordinary semistandard Schur polynomials
of the doubled Young diagrams and the paper's exact tail-area condition. -/
theorem corollary_5_3_schur_hilbert_coefficient (n : ℕ) (K : Type u) [Field K]
    (t s : ℕ) (ht : 1 ≤ t) (htn : t ≤ n) (hs : 1 ≤ s) (d : Fin n →₀ ℕ) :
    Module.finrank K
      (quotientPiece (symbolicPower (determinantalIdeal n K t) s) endpointWeight d) =
      ∑ᶠ μ : YoungDiagram, if AllowedShape n t s μ then
        (schurPolynomial n (doubleShape μ)).coeff d else 0 := by
  rw [corollary_5_3_hilbert_coefficient n K t s ht htn hs,
    standardMonomials_ncard_eq_good]
  rw [Schur.finite_ncard_eq_finsum_fibers _ (goodTableaux_finite d) tableauHalfShape]
  apply finsum_congr
  intro μ
  exact goodTableaux_shape_fiber n t s d μ

/-- Equality of the actual multivariate formal power series in Corollary 5.3. -/
theorem corollary_5_3_schur_hilbert_series (n : ℕ) (K : Type u) [Field K]
    (t s : ℕ) (ht : 1 ≤ t) (htn : t ≤ n) (hs : 1 ≤ s) :
    quotientHilbertSeries n K (symbolicPower (determinantalIdeal n K t) s) =
      schurHilbertSeries n t s := by
  funext d
  exact corollary_5_3_schur_hilbert_coefficient n K t s ht htn hs d

/-- The ordinary determinantal specialization displayed after Corollary 5.3:
the sum runs over every doubled partition with at most `q` nonzero rows. -/
theorem corollary_5_3_rank_schur_hilbert_series_of_lt (n : ℕ) (K : Type u) [Field K]
    (q : ℕ) (hq : q < n) :
    quotientHilbertSeries n K (determinantalIdeal n K (q + 1)) =
      rankSchurSeries n q := by
  classical
  letI : (determinantalIdeal n K (q + 1)).IsPrime :=
    Rees.determinantal_prime n K (q + 1) (by omega)
  have h := corollary_5_3_schur_hilbert_series n K (q + 1) 1
    (by omega) (by omega) (by omega)
  rw [symbolicPower_one] at h
  rw [h]
  funext d
  change (∑ᶠ μ : YoungDiagram, if AllowedShape n (q + 1) 1 μ then
      (schurPolynomial n (doubleShape μ)).coeff d else 0) = _
  simp only [rankSchurSeries, allowedShape_succ_one_iff hq.le]

theorem polynomial_schur_hilbert_coefficient (n : ℕ) (K : Type u) [Field K]
    (q : ℕ) (hnq : n ≤ q) (d : Fin n →₀ ℕ) :
    Module.finrank K (quotientPiece (⊥ : Ideal (CoordinateRing n K)) endpointWeight d) =
      ∑ᶠ μ : YoungDiagram, if μ.rowLens.length ≤ q then
        (schurPolynomial n (doubleShape μ)).coeff d else 0 := by
  have hhom := northwestIdeal_endpoint_homogeneous K (fun _ _ : Fin n => n)
  rw [northwestIdeal_unconstrained] at hhom
  have hstd : standardPieceSet (foldedOrder n) (⊥ : Ideal (CoordinateRing n K))
      endpointWeight d = {m : Entry n →₀ ℕ | Finsupp.weight endpointWeight m = d} := by
    ext m
    simp [standardPieceSet, MonomialOrder.standardMonomials, Ideal.mem_bot]
  have hf : (standardPieceSet (foldedOrder n) (⊥ : Ideal (CoordinateRing n K))
      endpointWeight d).Finite := by
    rw [hstd]
    exact endpointWeight_fibers_finite d
  rw [finrank_quotientPiece (foldedOrder n) _ endpointWeight hhom d hf, hstd]
  rw [← Set.ncard_image_of_injective _ pairedTableauMap_bijective.injective,
    ← contentTableaux_eq_image]
  rw [Schur.finite_ncard_eq_finsum_fibers _ (contentTableaux_finite d) tableauHalfShape]
  apply finsum_congr
  intro μ
  exact contentTableaux_shape_fiber_of_ge n q hnq d μ

/-- The ordinary determinantal specialization for **every** rank bound `q`,
including `q ≥ n`, when the determinantal ideal is zero. -/
theorem corollary_5_3_rank_schur_hilbert_series (n : ℕ) (K : Type u) [Field K]
    (q : ℕ) :
    quotientHilbertSeries n K (determinantalIdeal n K (q + 1)) =
      rankSchurSeries n q := by
  by_cases hq : q < n
  · exact corollary_5_3_rank_schur_hilbert_series_of_lt n K q hq
  · have hnq : n ≤ q := Nat.le_of_not_gt hq
    rw [determinantalIdeal_eq_bot_of_size_gt n (q + 1) K (by omega)]
    funext d
    exact polynomial_schur_hilbert_coefficient n K q hnq d

end FourPapers.Symmetric.Schur

#print axioms FourPapers.Symmetric.Schur.pairedTableau_content_weight
#print axioms FourPapers.Symmetric.Schur.schur_coefficient_support_finite
#print axioms FourPapers.Symmetric.Schur.rank_schur_coefficient_support_finite
#print axioms FourPapers.Symmetric.Schur.corollary_5_3_schur_hilbert_coefficient
#print axioms FourPapers.Symmetric.Schur.corollary_5_3_schur_hilbert_series
#print axioms FourPapers.Symmetric.Schur.corollary_5_3_rank_schur_hilbert_series

end

/-! ## SchurDegreeCounts -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace FourPapers.Symmetric.Schur

open MvPolynomial
open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.weightedGradedAlgebra

/-- Column strictness bounds the literal number of rows by the alphabet. -/
theorem evenTableau_length_le {n : ℕ} (T : EvenSemistandardTableaux n) :
    T.val.length ≤ n := by
  simpa only [tableauHalfShape_rowLens, List.length_map] using tableauHalfShape_height T

/-- The exponent expected from the Gram leading monomial: coordinate `(i,a)`
counts occurrences of label `a` in row `i`. Both coordinates range over `Fin n`. -/
def tableauRowExponent {n : ℕ} (T : EvenSemistandardTableaux n) :
    (Fin n × Fin n) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun p => (T.val.getD p.1.val []).count p.2.val)

@[simp] theorem tableauRowExponent_apply {n : ℕ} (T : EvenSemistandardTableaux n)
    (i a : Fin n) :
    tableauRowExponent T (i,a) = (T.val.getD i.val []).count a.val := by
  simp [tableauRowExponent]

/-- Distinct semistandard tableaux give distinct row-count exponents. -/
theorem tableauRowExponent_injective {n : ℕ} :
    Function.Injective (@tableauRowExponent n) := by
  intro T U h
  apply evenTableau_eq_of_finite_row_counts T U (evenTableau_length_le T)
    (evenTableau_length_le U)
  intro i a
  simpa only [tableauRowExponent_apply] using congrArg (fun e : (Fin n × Fin n) →₀ ℕ => e (i,a)) h

/-- An even-row semistandard tableau of polynomial degree `d`: its
half-shape has `d` boxes, so the full tableau has `2 * d` entries. -/
abbrev DegreeTableaux (n d : ℕ) :=
  {T : EvenSemistandardTableaux n // (tableauHalfShape T).rowLens.sum = d}

@[simp] theorem pairedTableauMap_halfShape_sum {n : ℕ} (m : Entry n →₀ ℕ) :
    (tableauHalfShape (pairedTableauMap m)).rowLens.sum = m.degree := by
  rw [tableauHalfShape_pairedTableau]
  have h := gamma_one_eq_degree m
  simpa only [gamma, Nat.sub_self, List.drop_zero] using h

/-- The degreewise restriction of the independently established insertion
bijection, with all multiplicities and repeated entries retained. -/
def degreeTableauEquiv (n d : ℕ) :
    {m : Entry n →₀ ℕ // m.degree = d} ≃ DegreeTableaux n d :=
  (Equiv.ofBijective (@pairedTableauMap n) pairedTableauMap_bijective).subtypeEquiv
    (fun m => by
      change m.degree = d ↔ (tableauHalfShape (pairedTableauMap m)).rowLens.sum = d
      rw [pairedTableauMap_halfShape_sum])

instance (n d : ℕ) : Finite (DegreeTableaux n d) := by
  haveI : Finite {m : Entry n →₀ ℕ // m.degree = d} :=
    (Finsupp.finite_of_degree_eq d).to_subtype
  exact Finite.of_injective (degreeTableauEquiv n d).symm
    (degreeTableauEquiv n d).symm.injective

noncomputable instance (n d : ℕ) : Fintype (DegreeTableaux n d) := Fintype.ofFinite _

/-- The number of degree-`d` tableaux is the dimension of the full degree-`d`
space of symmetric matrix polynomials, over every field. -/
theorem degreeTableaux_card_eq_finrank (n d : ℕ) (K : Type*) [Field K] :
    Fintype.card (DegreeTableaux n d) =
      Module.finrank K (homogeneousSubmodule (Entry n) K d) := by
  classical
  letI : Fintype {m : Entry n →₀ ℕ // m.degree = d} :=
    (Finsupp.finite_of_degree_eq d).fintype
  letI : Fintype ↥{m : Entry n →₀ ℕ | m.degree = d} :=
    (Finsupp.finite_of_degree_eq d).fintype
  rw [homogeneousSubmodule_eq_finsupp_supported]
  calc
    Fintype.card (DegreeTableaux n d) =
        Fintype.card {m : Entry n →₀ ℕ // m.degree = d} :=
      Fintype.card_congr (degreeTableauEquiv n d).symm
    _ = Module.finrank K
        (AddMonoidAlgebra.supported K K {m : Entry n →₀ ℕ | m.degree = d}) :=
      (Module.finrank_eq_card_basis
        (basisRestrictSupport K {m : Entry n →₀ ℕ | m.degree = d})).symm

/-- Any linearly independent homogeneous family indexed by all these
ordinary tableaux is a basis, by the verified degreewise count. -/
def degreeTableauBasis (n d : ℕ) (K : Type*) [Field K]
    (b : DegreeTableaux n d → homogeneousSubmodule (Entry n) K d)
    (hb : LinearIndependent K b) :
    Module.Basis (DegreeTableaux n d) K (homogeneousSubmodule (Entry n) K d) := by
  letI : Module.Finite K (homogeneousSubmodule (Entry n) K d) :=
    Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg (Entry n) K d)
  exact basisOfLinearIndependentOfCardEqFinrank' b hb
    (degreeTableaux_card_eq_finrank n d K)

@[simp] theorem degreeTableauBasis_apply (n d : ℕ) (K : Type*) [Field K]
    (b : DegreeTableaux n d → homogeneousSubmodule (Entry n) K d)
    (hb : LinearIndependent K b) (T : DegreeTableaux n d) :
    degreeTableauBasis n d K b hb T = b T := by
  simp [degreeTableauBasis]

/-- The true symbolic power is also homogeneous for ordinary polynomial degree. -/
theorem symbolic_total_homogeneous (n t s : ℕ) (K : Type*) [Field K]
    (ht : 1 ≤ t) (htn : t ≤ n) (hs : 1 ≤ s) :
    (symbolicPower (determinantalIdeal n K t) s).IsHomogeneous
      (homogeneousSubmodule (Entry n) K) := by
  rw [(corollary_5_3_groebner n K t s ht htn hs).ideal_eq_span]
  apply Ideal.homogeneous_span
  rintro f ⟨k, δ, hδ, hscore, rfl⟩
  exact ⟨∑ j, (δ j).size, product_minors_isHomogeneous_total K δ⟩

/-- The total-degree version of the actual symbolic quotient Hilbert count. -/
theorem degreeSymbolicQuotient_finrank_monomials (n t s D : ℕ) (K : Type*) [Field K]
    (ht : 1 ≤ t) (htn : t ≤ n) (hs : 1 ≤ s) :
    Module.finrank K
      (Pivot.quotientPiece (symbolicPower (determinantalIdeal n K t) s)
        (1 : Entry n → ℕ) D) =
      {m : Entry n →₀ ℕ | gamma t m < s ∧ m.degree = D}.ncard := by
  have hone : (1 : Entry n → ℕ) = fun _ => 1 := rfl
  have hhom : (symbolicPower (determinantalIdeal n K t) s).IsHomogeneous
      (weightedHomogeneousSubmodule K (1 : Entry n → ℕ)) :=
    symbolic_total_homogeneous n t s K ht htn hs
  have hf : (Pivot.standardPieceSet (foldedOrder n)
      (symbolicPower (determinantalIdeal n K t) s) (1 : Entry n → ℕ) D).Finite :=
    (Finsupp.finite_of_degree_eq D).subset (fun m hm => by
      change m.degree = D
      rw [Finsupp.degree_eq_weight_one, ← hone]
      exact hm.2)
  have h := Pivot.finrank_quotientPiece (foldedOrder n)
    (symbolicPower (determinantalIdeal n K t) s) (1 : Entry n → ℕ) hhom D hf
  simpa only [Pivot.standardPieceSet,
    corollary_5_3_standardMonomials n K t s ht htn hs,
    Set.mem_ofPred_eq, Finsupp.degree_eq_weight_one, hone] using h

/-- Restricting the insertion bijection to degree and symbolic tail preserves
cardinality. The target consists of the independently defined ordinary tableaux. -/
theorem degree_tableaux_tail_ncard (n t s D : ℕ) :
    {m : Entry n →₀ ℕ | gamma t m < s ∧ m.degree = D}.ncard =
      {T : DegreeTableaux n D |
        ((tableauHalfShape T.val).rowLens.drop (t - 1)).sum < s}.ncard := by
  let e := degreeTableauEquiv n D
  apply Set.ncard_congr (fun m hm => e ⟨m, hm.2⟩)
  · intro m hm
    change ((tableauHalfShape (pairedTableauMap m)).rowLens.drop (t - 1)).sum < s
    simpa only [tableauHalfShape_pairedTableau, gamma] using hm.1
  · intro m m' hm hm' he
    exact congrArg Subtype.val (e.injective he)
  · intro T hT
    let m := e.symm T
    have he : e m = T := e.apply_symm_apply T
    refine ⟨m.val, ⟨?_, m.property⟩, he⟩
    have h : ((tableauHalfShape (e m).val).rowLens.drop (t - 1)).sum < s := by
      rw [he]
      exact hT
    change ((tableauHalfShape (pairedTableauMap m.val)).rowLens.drop (t - 1)).sum < s at h
    simpa only [tableauHalfShape_pairedTableau, gamma] using h

/-- The quotient dimension is the number of degree-`D` tableaux outside the
symbolic tail cutoff. This also gives a dimension criterion for adapting a
genuine bitableau basis to the symbolic-power ideal. -/
theorem degreeSymbolicQuotient_finrank (n t s D : ℕ) (K : Type*) [Field K]
    (ht : 1 ≤ t) (htn : t ≤ n) (hs : 1 ≤ s) :
    Module.finrank K
      (Pivot.quotientPiece (symbolicPower (determinantalIdeal n K t) s)
        (1 : Entry n → ℕ) D) =
      {T : DegreeTableaux n D |
        ((tableauHalfShape T.val).rowLens.drop (t - 1)).sum < s}.ncard := by
  rw [degreeSymbolicQuotient_finrank_monomials n t s D K ht htn hs,
    degree_tableaux_tail_ncard]

end FourPapers.Symmetric.Schur

#print axioms FourPapers.Symmetric.Schur.tableauRowExponent_injective
#print axioms FourPapers.Symmetric.Schur.degreeTableaux_card_eq_finrank
#print axioms FourPapers.Symmetric.Schur.degreeTableauBasis

#print axioms FourPapers.Symmetric.Schur.degreeSymbolicQuotient_finrank

end

/-! ## SchurColumnCounts -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace FourPapers.Symmetric.Schur

open scoped BigOperators

/-- Doubling the partition doubles each row, including rows past its end. -/
@[simp] theorem doubleShape_rowLen (μ : YoungDiagram) (i : ℕ) :
    (doubleShape μ).rowLen i = 2 * μ.rowLen i := by
  calc
    (doubleShape μ).rowLen i = (doubleShape μ).rowLens.getD i 0 := by
      simpa only [List.getD_eq_getElem?_getD] using
        (YoungDiagram.matching_getD_rowLens (doubleShape μ) i).symm
    _ = (μ.rowLens.map (fun x => 2 * x)).getD i 0 := by rw [doubleShape_rowLens]
    _ = 2 * (μ.rowLens.getD i 0) := by
      simpa only [Nat.mul_zero] using List.getD_map μ.rowLens 0 (fun x => 2 * x) (n := i)
    _ = 2 * μ.rowLen i := by
      rw [List.getD_eq_getElem?_getD, YoungDiagram.matching_getD_rowLens]

private theorem nat_eq_of_lt_iff {a b : ℕ} (h : ∀ i, i < a ↔ i < b) : a = b := by
  apply Nat.le_antisymm
  · exact Nat.le_of_not_gt (fun hba => (Nat.lt_irrefl b) ((h b).mp hba))
  · exact Nat.le_of_not_gt (fun hab => (Nat.lt_irrefl a) ((h a).mpr hab))

/-- The two columns in each adjacent pair of a doubled shape have equal height. -/
@[simp] theorem doubleShape_colLen_even (μ : YoungDiagram) (j : ℕ) :
    (doubleShape μ).colLen (2 * j) = μ.colLen j := by
  apply nat_eq_of_lt_iff
  intro i
  rw [← YoungDiagram.mem_iff_lt_colLen, ← YoungDiagram.mem_iff_lt_colLen,
    YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_rowLen, doubleShape_rowLen]
  omega

@[simp] theorem doubleShape_colLen_odd (μ : YoungDiagram) (j : ℕ) :
    (doubleShape μ).colLen (2 * j + 1) = μ.colLen j := by
  apply nat_eq_of_lt_iff
  intro i
  rw [← YoungDiagram.mem_iff_lt_colLen, ← YoungDiagram.mem_iff_lt_colLen,
    YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_rowLen, doubleShape_rowLen]
  omega

/-- The row-list representation of an even tableau has exactly its doubled half-shape. -/
def evenTableauToShape {n : ℕ} (T : EvenSemistandardTableaux n) :
    ShapeTableaux n (doubleShape (tableauHalfShape T)) :=
  ⟨T.val, T.property.1, (double_tableauHalfShape T).symm, T.property.2.2⟩

/-- The entries of a column, in their strictly increasing order. -/
def columnLabels {n : ℕ} {μ : YoungDiagram} (T : ShapeTableaux n μ) (j : ℕ) :
    Fin (μ.colLen j) ↪o Fin n :=
  OrderEmbedding.ofStrictMono
    (fun i => T.cell ⟨(i.val, j), YoungDiagram.mem_iff_lt_colLen.mpr i.isLt⟩)
    (by
      intro i k hik
      exact (weakFillingOfRows T.property.1 T.property.2.1).col_strict hik
        (YoungDiagram.mem_iff_lt_colLen.mpr k.isLt))

/-- The left column of the `j`th adjacent column pair. -/
def pairedColumnLeft {n : ℕ} {μ : YoungDiagram}
    (T : ShapeTableaux n (doubleShape μ)) (j : ℕ) : Fin (μ.colLen j) ↪o Fin n :=
  (Fin.castOrderIso (doubleShape_colLen_even μ j).symm).toOrderEmbedding.trans
    (columnLabels T (2 * j))

/-- The right column of the same adjacent column pair, with the identical domain. -/
def pairedColumnRight {n : ℕ} {μ : YoungDiagram}
    (T : ShapeTableaux n (doubleShape μ)) (j : ℕ) : Fin (μ.colLen j) ↪o Fin n :=
  (Fin.castOrderIso (doubleShape_colLen_odd μ j).symm).toOrderEmbedding.trans
    (columnLabels T (2 * j + 1))

/-- The two ordered column lists are weakly ordered entry by entry along tableau rows. -/
theorem pairedColumnLeft_le_right {n : ℕ} {μ : YoungDiagram}
    (T : ShapeTableaux n (doubleShape μ)) (j : ℕ) (i : Fin (μ.colLen j)) :
    pairedColumnLeft T j i ≤ pairedColumnRight T j i := by
  have hc : (i.val, 2 * j + 1) ∈ doubleShape μ :=
    YoungDiagram.mem_iff_lt_colLen.mpr (by rw [doubleShape_colLen_odd]; exact i.isLt)
  exact (weakFillingOfRows T.property.1 T.property.2.1).row_mono
    (Nat.lt_succ_self (2 * j)) hc

/-- The cells below the first `r` rows are counted by the tail of the partition. -/
theorem row_tail_sum_eq_card (μ : YoungDiagram) (r : ℕ) :
    (μ.rowLens.drop r).sum = (μ.cells.filter (fun c => r ≤ c.1)).card := by
  have hlist := congrArg List.sum (List.take_append_drop r μ.rowLens)
  simp only [List.sum_append, YoungDiagram.sum_rowLens_eq_card] at hlist
  rw [YoungDiagram.sum_take_rowLens_eq_card_filter_fst] at hlist
  simp only [YoungDiagram.card] at hlist
  have hcells := Finset.card_filter_add_card_filter_not (s := μ.cells) (fun c => c.1 < r)
  simp only [Nat.not_lt] at hcells
  omega

/-- The same tail cells, counted in columns. -/
theorem row_tail_sum_eq_column_sum (μ : YoungDiagram) (r : ℕ) :
    (μ.rowLens.drop r).sum =
      ∑ j ∈ Finset.range (μ.rowLen 0), (μ.colLen j - r) := by
  rw [row_tail_sum_eq_card]
  have hmaps : ∀ c ∈ μ.cells.filter (fun c => r ≤ c.1),
      c.2 ∈ Finset.range (μ.rowLen 0) := by
    intro c hc
    apply Finset.mem_range.mpr
    exact (YoungDiagram.mem_iff_lt_rowLen.mp (Finset.mem_filter.mp hc).1).trans_le
      (μ.rowLen_anti 0 c.1 (Nat.zero_le _))
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro j hj
  have he : ((μ.cells.filter (fun c => r ≤ c.1)).filter (fun c => c.2 = j)) =
      (Finset.Ico r (μ.colLen j)).image (fun i => (i, j)) := by
    ext c
    rcases c with ⟨i, k⟩
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Ico,
      YoungDiagram.mem_cells, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hc, hr⟩, rfl⟩
      exact ⟨i, ⟨hr, YoungDiagram.mem_iff_lt_colLen.mp hc⟩, rfl, rfl⟩
    · rintro ⟨i', ⟨hr, hi⟩, rfl, rfl⟩
      exact ⟨⟨YoungDiagram.mem_iff_lt_colLen.mpr hi, hr⟩, rfl⟩
  rw [he, Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)]
  simp

/-- The sizes of the paired-column minors are the column lengths of the half-shape. -/
def columnSizes (μ : YoungDiagram) : List ℕ := μ.transpose.rowLens

/-- The determinant-factor score is exactly the half-shape tail area. -/
theorem columnSizes_score_eq_tail (μ : YoungDiagram) (t : ℕ) (ht : 1 ≤ t) :
    ((columnSizes μ).map (fun h => h + 1 - t)).sum = (μ.rowLens.drop (t - 1)).sum := by
  rw [row_tail_sum_eq_column_sum]
  have h := YoungDiagram.sum_map_coe_rowLens μ.transpose (fun k => k + 1 - t)
  simp only [Multiset.map_coe, Multiset.sum_coe, YoungDiagram.colLen_transpose,
    YoungDiagram.rowLen_transpose] at h
  change ((μ.transpose.rowLens).map (fun k => k + 1 - t)).sum = _
  rw [h]
  apply Finset.sum_congr rfl
  intro j hj
  omega

/-- Every minor size is positive and at most the number of rows of the half-shape. -/
theorem columnSizes_bounds (μ : YoungDiagram) {h : ℕ} (hh : h ∈ columnSizes μ) :
    1 ≤ h ∧ h ≤ μ.rowLens.length := by
  constructor
  · exact μ.transpose.pos_of_mem_rowLens h hh
  · rw [columnSizes, YoungDiagram.rowLens, List.mem_map] at hh
    obtain ⟨j, hj, rfl⟩ := hh
    rw [YoungDiagram.rowLen_transpose, YoungDiagram.length_rowLens]
    exact μ.colLen_anti 0 j (Nat.zero_le j)

end FourPapers.Symmetric.Schur

#print axioms FourPapers.Symmetric.Schur.doubleShape_colLen_even
#print axioms FourPapers.Symmetric.Schur.doubleShape_colLen_odd
#print axioms FourPapers.Symmetric.Schur.columnSizes_score_eq_tail

end

/-! ## SchurBitableauData -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace FourPapers.Symmetric.Schur

open MvPolynomial
open scoped BigOperators

/-- The number of adjacent column pairs in an even-row tableau. -/
def columnPairCount {n : ℕ} (T : EvenSemistandardTableaux n) : ℕ :=
  (tableauHalfShape T).rowLen 0

/-- The actual minor formed from the `j`th pair of adjacent tableau columns.
Both columns have the height of column `j` of the half-shape. -/
def bitableauMinor {n : ℕ} (T : EvenSemistandardTableaux n)
    (j : Fin (columnPairCount T)) : MinorData n where
  size := (tableauHalfShape T).colLen j.val
  rows := pairedColumnLeft (evenTableauToShape T) j.val
  cols := pairedColumnRight (evenTableauToShape T) j.val

/-- The complete, unrestricted list of paired-column minors. -/
def bitableauMinors {n : ℕ} (T : EvenSemistandardTableaux n) : List (MinorData n) :=
  List.ofFn (bitableauMinor T)

@[simp] theorem bitableauMinor_size {n : ℕ} (T : EvenSemistandardTableaux n)
    (j : Fin (columnPairCount T)) :
    (bitableauMinor T j).size = (tableauHalfShape T).colLen j.val := rfl

theorem bitableauMinor_size_pos {n : ℕ} (T : EvenSemistandardTableaux n)
    (j : Fin (columnPairCount T)) : 1 ≤ (bitableauMinor T j).size := by
  exact YoungDiagram.mem_iff_lt_colLen.mp
    (YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt)

theorem bitableauMinor_size_le {n : ℕ} (T : EvenSemistandardTableaux n)
    (j : Fin (columnPairCount T)) : (bitableauMinor T j).size ≤ n := by
  have h := Fintype.card_le_of_injective (bitableauMinor T j).rows
    (bitableauMinor T j).rows.injective
  simpa only [Fintype.card_fin] using h

/-- The minor-size list is the conjugate partition of the half-shape. -/
theorem bitableauMinors_sizes {n : ℕ} (T : EvenSemistandardTableaux n) :
    (bitableauMinors T).map MinorData.size = columnSizes (tableauHalfShape T) := by
  simp only [bitableauMinors, List.map_ofFn, bitableauMinor_size,
    columnSizes, YoungDiagram.rowLens, YoungDiagram.colLen_transpose,
    YoungDiagram.rowLen_transpose]
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_map, List.length_range, columnPairCount]
  · intro i hi hj
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range,
      Function.comp_def, bitableauMinor_size, YoungDiagram.rowLen_transpose]

theorem bitableauMinors_sizes_sorted {n : ℕ} (T : EvenSemistandardTableaux n) :
    ((bitableauMinors T).map MinorData.size).SortedGE := by
  rw [bitableauMinors_sizes, columnSizes]
  exact (tableauHalfShape T).transpose.rowLens_sorted

/-- The standard symmetric bitableau is a product of genuine determinants
in the original coordinate ring, with empty product equal to one. -/
def bitableauPolynomial {n : ℕ} (R : Type*) [CommRing R]
    (T : EvenSemistandardTableaux n) : CoordinateRing n R :=
  ∏ j : Fin (columnPairCount T), (bitableauMinor T j).polynomial R

theorem bitableauPolynomial_eq_list_product {n : ℕ} (R : Type*) [CommRing R]
    (T : EvenSemistandardTableaux n) :
    bitableauPolynomial R T =
      ((bitableauMinors T).map (fun δ => δ.polynomial R)).prod := by
  simp only [bitableauPolynomial, bitableauMinors, List.map_ofFn, List.prod_ofFn,
    Function.comp_def]

/-- Each box of the half-shape contributes once to the total minor degree. -/
theorem bitableau_sizes_sum {n : ℕ} (T : EvenSemistandardTableaux n) :
    (∑ j : Fin (columnPairCount T), (bitableauMinor T j).size) =
      (tableauHalfShape T).rowLens.sum := by
  calc
    (∑ j : Fin (columnPairCount T), (bitableauMinor T j).size) =
        ((bitableauMinors T).map MinorData.size).sum := by
      simp only [bitableauMinors, List.map_ofFn, List.sum_ofFn, Function.comp_def]
    _ = (columnSizes (tableauHalfShape T)).sum := by rw [bitableauMinors_sizes]
    _ = (tableauHalfShape T).rowLens.sum := by
      rw [columnSizes, YoungDiagram.sum_rowLens_eq_card,
        YoungDiagram.card_transpose, YoungDiagram.sum_rowLens_eq_card]

/-- Homogeneity of the actual determinant product, in the polynomial degree
counted by the insertion bijection. -/
theorem bitableauPolynomial_isHomogeneous {n : ℕ} (R : Type*) [CommRing R]
    (T : EvenSemistandardTableaux n) :
    (bitableauPolynomial R T).IsHomogeneous (tableauHalfShape T).rowLens.sum := by
  simpa only [bitableauPolynomial, bitableau_sizes_sum] using
    product_minors_isHomogeneous_total R (bitableauMinor T)

/-- The full determinant-factor score equals the tail area of the half-shape.
The expression `size + 1 - t` is truncated subtraction, so short columns
contribute zero. -/
theorem bitableau_minor_score {n : ℕ} (T : EvenSemistandardTableaux n)
    (t : ℕ) (ht : 1 ≤ t) :
    (∑ j : Fin (columnPairCount T), ((bitableauMinor T j).size + 1 - t)) =
      ((tableauHalfShape T).rowLens.drop (t - 1)).sum := by
  calc
    (∑ j : Fin (columnPairCount T), ((bitableauMinor T j).size + 1 - t)) =
        (((bitableauMinors T).map MinorData.size).map (fun h => h + 1 - t)).sum := by
      simp only [bitableauMinors, List.map_ofFn, List.sum_ofFn, Function.comp_def]
    _ = ((columnSizes (tableauHalfShape T)).map (fun h => h + 1 - t)).sum := by
      rw [bitableauMinors_sizes]
    _ = ((tableauHalfShape T).rowLens.drop (t - 1)).sum :=
      columnSizes_score_eq_tail (tableauHalfShape T) t ht

/-- A degree-indexed bitableau, ready for the degreewise basis criterion. -/
def degreeBitableau {n d : ℕ} (R : Type*) [CommRing R] (T : DegreeTableaux n d) :
    homogeneousSubmodule (Entry n) R d :=
  ⟨bitableauPolynomial R T.val, by
    change (bitableauPolynomial R T.val).IsHomogeneous d
    simpa only [T.property] using bitableauPolynomial_isHomogeneous R T.val⟩

end FourPapers.Symmetric.Schur

#print axioms FourPapers.Symmetric.Schur.bitableauPolynomial_isHomogeneous
#print axioms FourPapers.Symmetric.Schur.bitableau_minor_score

end

/-! ## SchurBitableauExponents -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section

namespace FourPapers.Symmetric.Schur

open Finsupp
open scoped BigOperators

/-- A row-by-row enumeration of the cells of a Young diagram. -/
abbrev RowCellIndex (μ : YoungDiagram) :=
  Σ i : Fin (μ.colLen 0), Fin (μ.rowLen i.val)

def rowCellMap (μ : YoungDiagram) (p : RowCellIndex μ) : ↥μ.cells :=
  ⟨(p.1.val, p.2.val), YoungDiagram.mem_iff_lt_rowLen.mpr p.2.isLt⟩

theorem rowCellMap_bijective (μ : YoungDiagram) : Function.Bijective (rowCellMap μ) := by
  constructor
  · rintro ⟨i, j⟩ ⟨k, l⟩ h
    have hi : i = k := Fin.ext (congrArg (fun c : ↥μ.cells => c.val.1) h)
    subst k
    have hj : j = l := Fin.ext (congrArg (fun c : ↥μ.cells => c.val.2) h)
    subst l
    rfl
  · intro c
    exact ⟨⟨⟨c.val.1, μ.lt_colLen_zero_of_mem c.property⟩,
      ⟨c.val.2, YoungDiagram.mem_iff_lt_rowLen.mp c.property⟩⟩, Subtype.ext rfl⟩

/-- Group the cells of a doubled diagram into its actual adjacent column pairs. -/
abbrev PairedCellIndex (μ : YoungDiagram) :=
  Σ j : Fin (μ.rowLen 0), Fin (μ.colLen j.val) × Fin 2

def pairedCellMap (μ : YoungDiagram) (p : PairedCellIndex μ) : ↥(doubleShape μ).cells := by
  refine ⟨(p.2.1.val, 2 * p.1.val + p.2.2.val), ?_⟩
  apply YoungDiagram.mem_iff_lt_rowLen.mpr
  rw [doubleShape_rowLen]
  have hj : p.1.val < μ.rowLen p.2.1.val :=
    YoungDiagram.mem_iff_lt_rowLen.mp (YoungDiagram.mem_iff_lt_colLen.mpr p.2.1.isLt)
  have hb := p.2.2.isLt
  omega

theorem pairedCellMap_bijective (μ : YoungDiagram) : Function.Bijective (pairedCellMap μ) := by
  constructor
  · rintro ⟨j, i, b⟩ ⟨k, l, c⟩ h
    have hrow : i.val = l.val := congrArg (fun d : ↥(doubleShape μ).cells => d.val.1) h
    have hcol : 2 * j.val + b.val = 2 * k.val + c.val :=
      congrArg (fun d : ↥(doubleShape μ).cells => d.val.2) h
    have hb := b.isLt
    have hc := c.isLt
    have hj : j = k := Fin.ext (by omega)
    subst k
    have hi : i = l := Fin.ext hrow
    have he : b = c := Fin.ext (by omega)
    subst l
    subst c
    rfl
  · intro c
    have hc : c.val.2 < 2 * μ.rowLen c.val.1 := by
      simpa only [doubleShape_rowLen] using YoungDiagram.mem_iff_lt_rowLen.mp c.property
    have hjrow : c.val.2 / 2 < μ.rowLen c.val.1 := by omega
    have hj : c.val.2 / 2 < μ.rowLen 0 :=
      hjrow.trans_le (μ.rowLen_anti 0 c.val.1 (Nat.zero_le _))
    have hi : c.val.1 < μ.colLen (c.val.2 / 2) :=
      YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hjrow)
    refine ⟨⟨⟨c.val.2 / 2, hj⟩, ⟨⟨c.val.1, hi⟩, ⟨c.val.2 % 2, by omega⟩⟩⟩,
      Subtype.ext ?_⟩
    apply Prod.ext
    · rfl
    · change 2 * (c.val.2 / 2) + c.val.2 % 2 = c.val.2
      omega

theorem sum_cells_by_rows {A : Type*} [AddCommMonoid A]
    (μ : YoungDiagram) (f : ↥μ.cells → A) :
    (∑ c : ↥μ.cells, f c) =
      ∑ i : Fin (μ.colLen 0), ∑ j : Fin (μ.rowLen i.val), f (rowCellMap μ ⟨i,j⟩) := by
  rw [← (rowCellMap_bijective μ).sum_comp f, Fintype.sum_sigma]

theorem sum_cells_by_column_pairs {A : Type*} [AddCommMonoid A]
    (μ : YoungDiagram) (f : ↥(doubleShape μ).cells → A) :
    (∑ c : ↥(doubleShape μ).cells, f c) =
      ∑ j : Fin (μ.rowLen 0), ∑ i : Fin (μ.colLen j.val),
        (f (pairedCellMap μ ⟨j,i,0⟩) + f (pairedCellMap μ ⟨j,i,1⟩)) := by
  rw [← (pairedCellMap_bijective μ).sum_comp f, Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]

private theorem count_ofFn_eq_sum {k : ℕ} (f : Fin k → ℕ) (a : ℕ) :
    (List.ofFn f).count a = ∑ i : Fin k, if f i = a then 1 else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.ofFn_succ, List.count_cons, Fin.sum_univ_succ, ih]
      by_cases h : f 0 = a <;> simp [h, Nat.add_comm]

namespace ShapeTableaux

variable {n : ℕ} {μ : YoungDiagram}

theorem length_rows (T : ShapeTableaux n μ) : T.val.length = μ.colLen 0 := by
  simpa only [List.length_map, YoungDiagram.length_rowLens] using
    congrArg List.length T.property.2.1

theorem row_ofFn (T : ShapeTableaux n μ) (i : Fin (μ.colLen 0)) :
    List.ofFn (fun j : Fin (μ.rowLen i.val) =>
      (T.cell (rowCellMap μ ⟨i,j⟩)).val) = T.val.getD i.val [] := by
  have hi : i.val < T.val.length := by rw [T.length_rows]; exact i.isLt
  rw [List.getD_eq_getElem _ _ hi]
  apply List.ext_getElem
  · simp only [List.length_ofFn, rows_cell_length T.property.2.1 hi]
  · intro j hj hk
    simp only [List.getElem_ofFn]
    rfl

end ShapeTableaux

/-- The row number and label of a genuine tableau cell, both in the fixed alphabet. -/
def cellRowLabel {n : ℕ} {μ : YoungDiagram} (T : ShapeTableaux n μ) (c : ↥μ.cells) :
    Fin n × Fin n :=
  (⟨c.val.1, (μ.lt_colLen_zero_of_mem c.property).trans_le
    (by simpa only [YoungDiagram.length_rowLens] using T.height_le)⟩, T.cell c)

def cellRowExponent {n : ℕ} {μ : YoungDiagram} (T : ShapeTableaux n μ) :
    (Fin n × Fin n) →₀ ℕ :=
  ∑ c : ↥μ.cells, single (cellRowLabel T c) 1

private theorem cellRowLabel_row_eq_iff {n : ℕ} {μ : YoungDiagram}
    (T : ShapeTableaux n μ) (r : Fin (μ.colLen 0)) (c : Fin (μ.rowLen r.val))
    (i a : Fin n) :
    cellRowLabel T (rowCellMap μ ⟨r,c⟩) = (i,a) ↔
      r.val = i.val ∧ (T.cell (rowCellMap μ ⟨r,c⟩)).val = a.val := by
  simp only [cellRowLabel, rowCellMap, Prod.mk.injEq, Fin.ext_iff]

/-- Cell enumeration records exactly the ordinary multiplicity of a label in a row. -/
theorem cellRowExponent_apply {n : ℕ} {μ : YoungDiagram} (T : ShapeTableaux n μ)
    (i a : Fin n) : cellRowExponent T (i,a) = (T.val.getD i.val []).count a.val := by
  classical
  simp only [cellRowExponent, Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [sum_cells_by_rows]
  simp_rw [cellRowLabel_row_eq_iff]
  by_cases hi : i.val < μ.colLen 0
  · let r : Fin (μ.colLen 0) := ⟨i.val,hi⟩
    rw [Finset.sum_eq_single r]
    · simp only [r, true_and]
      rw [← count_ofFn_eq_sum]
      rw [T.row_ofFn r]
    · intro r' hr' hne
      have hh : r'.val ≠ i.val := by
        intro he
        exact hne (Fin.ext he)
      simp only [hh, false_and, ite_false, Finset.sum_const_zero]
    · simp
  · have hd : T.val.getD i.val [] = [] := by
      apply List.getD_eq_default
      rw [T.length_rows]
      exact Nat.le_of_not_gt hi
    rw [hd, List.count_nil]
    apply Finset.sum_eq_zero
    intro r hr
    have hh : r.val ≠ i.val := by
      intro he
      apply hi
      exact he ▸ r.isLt
    simp only [hh, false_and, ite_false, Finset.sum_const_zero]

/-- Increasing minor rows force the minor size to be at most `n`. -/
theorem minorData_size_le {n : ℕ} (δ : MinorData n) : δ.size ≤ n := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective δ.rows δ.rows.injective

/-- The two generic diagonal exponents associated with a minor's row and column lists.
The first coordinate is the ordinal position in the minor; the second is the matrix label. -/
def minorRowExponent {n : ℕ} (δ : MinorData n) : (Fin n × Fin n) →₀ ℕ :=
  (∑ i : Fin δ.size, single
    (⟨i.val, i.isLt.trans_le (minorData_size_le δ)⟩, δ.rows i) 1) +
  (∑ i : Fin δ.size, single
    (⟨i.val, i.isLt.trans_le (minorData_size_le δ)⟩, δ.cols i) 1)

def bitableauRowExponent {n : ℕ} (T : EvenSemistandardTableaux n) :
    (Fin n × Fin n) →₀ ℕ :=
  ∑ j : Fin (columnPairCount T), minorRowExponent (bitableauMinor T j)

/-- The generic diagonal exponents of the paired minors count every tableau cell once. -/
theorem bitableauRowExponent_eq_cells {n : ℕ} (T : EvenSemistandardTableaux n) :
    bitableauRowExponent T = cellRowExponent (evenTableauToShape T) := by
  rw [cellRowExponent, sum_cells_by_column_pairs]
  unfold bitableauRowExponent
  apply Finset.sum_congr rfl
  intro j hj
  rw [minorRowExponent, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

/-- The exponent of the actual paired-minor family is the independently defined
row-count exponent. Thus its injectivity is a combinatorial fact about ordinary tableaux. -/
theorem bitableauRowExponent_eq {n : ℕ} (T : EvenSemistandardTableaux n) :
    bitableauRowExponent T = tableauRowExponent T := by
  rw [bitableauRowExponent_eq_cells]
  ext p
  rcases p with ⟨i,a⟩
  exact (cellRowExponent_apply (evenTableauToShape T) i a).trans
    (tableauRowExponent_apply T i a).symm

theorem bitableauRowExponent_injective {n : ℕ} :
    Function.Injective (@bitableauRowExponent n) := by
  intro T U h
  apply tableauRowExponent_injective
  simpa only [bitableauRowExponent_eq] using h

/-- The same exponent in the column-first lexicographic variable type used for Gram matrices. -/
def bitableauLexExponent {n : ℕ} (T : EvenSemistandardTableaux n) :
    (Fin n ×ₗ Fin n) →₀ ℕ :=
  (bitableauRowExponent T).mapDomain toLex

theorem bitableauLexExponent_injective {n : ℕ} :
    Function.Injective (@bitableauLexExponent n) := by
  intro T U h
  apply bitableauRowExponent_injective
  exact Finsupp.mapDomain_injective (fun _ _ h => h) h

end FourPapers.Symmetric.Schur

#print axioms FourPapers.Symmetric.Schur.bitableauRowExponent_eq
#print axioms FourPapers.Symmetric.Schur.bitableauLexExponent_injective

end

/-! ## Proof-dependency and axiom audit

This command only reads the checked environment and writes an audit artifact.
It creates no declarations and rejects unapproved axioms or unsafe proof edges.
-/

set_option maxHeartbeats 8000000 in
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let constants := env.checked.get.constants.foldStage2
    (fun acc name ci => acc.push (name, ci)) (#[] : Array (Name × ConstantInfo))
  let allowed : Array Name := #["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let roots : Array Name := #[
    "FourPapers.Symmetric.Schur.schurPolynomial_coeff".toName,
    "FourPapers.Symmetric.Schur.pairedTableau_content_weight".toName,
    "FourPapers.Symmetric.Schur.schur_coefficient_support_finite".toName,
    "FourPapers.Symmetric.Schur.rank_schur_coefficient_support_finite".toName,
    "FourPapers.Symmetric.Schur.corollary_5_3_schur_hilbert_coefficient".toName,
    "FourPapers.Symmetric.Schur.corollary_5_3_schur_hilbert_series".toName,
    "FourPapers.Symmetric.Schur.corollary_5_3_rank_schur_hilbert_series".toName,
    "FourPapers.Symmetric.Schur.tableauRowExponent_injective".toName,
    "FourPapers.Symmetric.Schur.degreeTableaux_card_eq_finrank".toName,
    "FourPapers.Symmetric.Schur.degreeTableauBasis".toName,
    "FourPapers.Symmetric.Schur.degreeSymbolicQuotient_finrank".toName,
    "FourPapers.Symmetric.Schur.doubleShape_colLen_even".toName,
    "FourPapers.Symmetric.Schur.doubleShape_colLen_odd".toName,
    "FourPapers.Symmetric.Schur.columnSizes_score_eq_tail".toName,
    "FourPapers.Symmetric.Schur.bitableauPolynomial_isHomogeneous".toName,
    "FourPapers.Symmetric.Schur.bitableau_minor_score".toName,
    "FourPapers.Symmetric.Schur.bitableauRowExponent_eq".toName,
    "FourPapers.Symmetric.Schur.bitableauLexExponent_injective".toName]
  let mut runtimeOnly : Array Name := #[]
  let mut auditedImports : NameSet := {}
  for (name, ci) in constants do
    if ci.isAxiom then
      throwError "Unapproved local axiom: {name}"
    if ci.isUnsafe || ci.isPartial then
      unless name.getString! == "_unsafe_rec" do
        throwError "Authored or unrecognized unsafe declaration: {name}"
      match env.find? name.getPrefix with
      | some parent =>
        if parent.isUnsafe || parent.isPartial || parent.isAxiom then
          throwError "Unsafe runtime companion lacks safe defining declaration: {name}"
      | none => throwError "Unrecognized runtime companion: {name}"
      runtimeOnly := runtimeOnly.push name
    else
      for dep in ci.type.getUsedConstants ++ ((ci.value? true).map Expr.getUsedConstants |>.getD #[]) do
        if let some info := env.find? dep then
          if info.isUnsafe || info.isPartial then
            throwError "Unsafe proof dependency {dep} in safe declaration {name}"
          if info.isAxiom && !auditedImports.contains dep then
            -- Exported theorems may have axiom-shaped public declarations. Stock Lean's
            -- exportedAxiomsExt stores their checked, transitive axiom dependencies.
            -- collectAxioms uses that metadata rather than misclassifying proof stubs.
            let deps ← collectAxioms dep
            for ax in deps do
              if !allowed.contains ax then
                throwError "Unapproved imported axiom {ax}, reached through {dep} in {name}"
            auditedImports := auditedImports.insert dep
  let mut rootAxioms : Array Json := #[]
  for root in roots do
    unless env.contains root do
      throwError "Required final theorem is unavailable: {root}"
    let axioms ← collectAxioms root
    for ax in axioms do
      if !allowed.contains ax then
        throwError "Unapproved transitive axiom in {root}: {ax}"
    rootAxioms := rootAxioms.push <| Json.mkObj [
      ("theorem", toJson root.toString), ("axioms", toJson (axioms.map Name.toString))]
  let ctors (ci : ConstantInfo) : Array Name :=
    match ci with
    | .inductInfo v => v.ctors.toArray
    | _ => #[]
  let mut names : NameSet := {}
  for (name, ci) in constants do
    names := names.insert name
    for dep in ci.type.getUsedConstants do
      names := names.insert dep
    for dep in (ci.value? true).map Expr.getUsedConstants |>.getD #[] do
      names := names.insert dep
    for dep in ctors ci do
      names := names.insert dep
  for root in roots do
    names := names.insert root
  let dictionary := names.toArray.qsort Name.lt
  let mut indices : NameMap Nat := {}
  for i in [:dictionary.size] do
    indices := indices.insert dictionary[i]! i
  let index (n : Name) := (indices.find? n).getD 0
  let data := constants.map fun (name, ci) =>
    Json.arr #[toJson (index name), toJson (ci.type.getUsedConstants.map index),
      toJson (((ci.value? true).map Expr.getUsedConstants |>.getD #[]).map index),
      toJson ((ctors ci).map index), toJson ci.isAxiom, toJson ci.isUnsafe, toJson ci.isPartial]
  let graph := Json.mkObj [
    ("format", toJson "local-proof-dag-v1"),
    ("columns", toJson (#["name", "type", "value", "inductiveCtors", "axiom", "unsafe", "partial"] : Array String)),
    ("names", toJson (dictionary.map Name.toString)),
    ("nodes", Json.arr data),
    ("roots", toJson (roots.map index)),
    ("root_axioms", Json.arr rootAxioms),
    ("compiler_runtime_only", toJson (runtimeOnly.map Name.toString))]
  liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  liftIO <| IO.FS.writeFile ".lake/reports/audit/schur_dependency_graph.json" (Json.compress graph)
  logInfo m!"SCHUR_AUDIT_OK {constants.size} local declarations; {roots.size} verification roots; only propext, Classical.choice, Quot.sound; no authored axioms or unsafe proof dependencies."

