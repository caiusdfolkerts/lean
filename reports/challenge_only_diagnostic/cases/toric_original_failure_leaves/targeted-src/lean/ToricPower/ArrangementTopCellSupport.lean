module

public import ToricPower.ArrangementOpenSupportCoordinates

/-!
# The open support of one ambient-dimensional arrangement cell

A full-dimensional cell is an actual open convex bounded set. Its
relative cellular cochain complex has exactly one characteristic-cell
coordinate, in ambient degree. These assertions retain the original
periodic characteristic maps and are valid even when some defining forms
vanish identically.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Set
open scoped Classical

namespace ToricPower.IntegralArrangement

section Linear

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E]

/-- The relatively open arrangement cell is convex, including its
active equalities. -/
theorem cell_convex (f : ι → E →ₗ[ℝ] ℝ) (e : ι → ℤ) (I : Set ι) :
    Convex ℝ (cell f e I) := by
  intro x hx y hy a b ha hb hab i
  simp only [map_add, map_smul, smul_eq_mul]
  by_cases hi : i ∈ I
  · have hx' := hx i
    have hy' := hy i
    simp only [if_pos hi] at hx' hy' ⊢
    rw [hx', hy', ← add_mul, hab, one_mul]
  · have hx' := hx i
    have hy' := hy i
    simp only [if_neg hi] at hx' hy' ⊢
    exact (convex_Ioo ((e i : ℝ) - 1) (e i : ℝ)) hx' hy' ha hb hab

/-- One open cell is a union of actual arrangement cells, by uniqueness
of the ceiling and wall labels at a point. -/
theorem cell_cellwise (f : ι → E →ₗ[ℝ] ℝ) (e : ι → ℤ) (I : Set ι) :
    Cellwise f (cell f e I) := by
  intro e' I' x y hx hy
  constructor
  · intro hxc
    obtain ⟨he, hI⟩ := cell_indices_unique f hx hxc
    subst e'
    subst I'
    exact hy
  · intro hyc
    obtain ⟨he, hI⟩ := cell_indices_unique f hy hyc
    subst e'
    subst I'
    exact hx

end Linear

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (c : Cell (augmentedForms A) n)

/-- A genuine ambient-dimensional cell exists. A Baire argument avoids
every integral level of every nonzero defining form; zero forms impose
only tautological equalities and do not lower the dimension. -/
theorem exists_topCell : Nonempty (Cell (augmentedForms A) n) := by
  let J := {i : Sum (Fin s) (Fin n) // augmentedForms A i ≠ 0}
  let U : J × ℤ → Set (Fin n → ℝ) := fun p =>
    (augmentedForms A p.1.val) ⁻¹' ({(p.2 : ℝ)} : Set ℝ)ᶜ
  have surjective (i : J) : Function.Surjective (augmentedForms A i.val) := by
    have nonzero : ¬ ∀ x, augmentedForms A i.val x = 0 := by
      intro zero
      apply i.property
      apply LinearMap.ext
      intro x
      exact zero x
    obtain ⟨x, hx⟩ := not_forall.mp nonzero
    intro a
    refine ⟨(a / augmentedForms A i.val x) • x, ?_⟩
    simp only [map_smul, smul_eq_mul, div_mul_cancel₀ _ hx]
  have openU (p : J × ℤ) : IsOpen (U p) :=
    isOpen_compl_singleton.preimage
      (augmentedForms A p.1.val).continuous_of_finiteDimensional
  have denseU (p : J × ℤ) : Dense (U p) :=
    (dense_compl_singleton (p.2 : ℝ)).preimage
      ((augmentedForms A p.1.val).isOpenMap_of_finiteDimensional (surjective p.1))
  obtain ⟨x, hx⟩ := (dense_iInter_of_isOpen openU denseU).nonempty
  have direction : cellDirection (augmentedForms A)
      (integralIndices (augmentedForms A) x) = ⊤ := by
    apply top_unique
    intro v _
    rw [mem_cellDirection]
    intro i hi
    by_cases zero : augmentedForms A i = 0
    · rw [zero]
      rfl
    · have avoid := mem_iInter.mp hx
        ((⟨i, zero⟩ : J), ⌈augmentedForms A i x⌉)
      exact (avoid hi).elim
  exact ⟨⟨(ceilingVector (augmentedForms A) x, integralIndices (augmentedForms A) x),
    ⟨⟨x, mem_cell_self (augmentedForms A) x⟩, by
      rw [direction]
      simp only [finrank_top, Module.finrank_pi, Module.finrank_self,
        Fintype.card_fin, mul_one]⟩⟩⟩

theorem exists_normalizedTopCell : Nonempty (NormalizedCell A n) := by
  obtain ⟨c⟩ := exists_topCell A
  exact ⟨normalizeCell A c⟩

/-- Full ambient dimension forces the direction subspace to be all of
the real character space. -/
theorem topCell_direction_eq_top : cellDirection (augmentedForms A) c.val.2 = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] using
    c.property.2

/-- Active equalities on an ambient-dimensional cell are tautological:
their linear forms and their levels both vanish. -/
theorem topCell_active_eq (i : Sum (Fin s) (Fin n)) (hi : i ∈ c.val.2)
    (x : Fin n → ℝ) : augmentedForms A i x = (c.val.1 i : ℝ) := by
  have zero (y : Fin n → ℝ) : augmentedForms A i y = 0 := by
    apply (mem_cellDirection (augmentedForms A) c.val.2 y).mp ?_ i hi
    rw [topCell_direction_eq_top A c]
    trivial
  have center := cellCenter_mem (augmentedForms A) c i
  rw [if_pos hi, zero] at center
  exact (zero x).trans center

theorem topCell_isOpen : IsOpen (cell (augmentedForms A) c.val.1 c.val.2) := by
  have description : cell (augmentedForms A) c.val.1 c.val.2 =
      ⋂ i, {x : Fin n → ℝ | i ∉ c.val.2 →
        (c.val.1 i : ℝ) - 1 < augmentedForms A i x ∧
          augmentedForms A i x < (c.val.1 i : ℝ)} := by
    ext x
    simp only [mem_iInter, mem_setOf_eq]
    constructor
    · intro hx i hi
      simpa only [if_neg hi] using hx i
    · intro hx i
      by_cases hi : i ∈ c.val.2
      · simpa only [if_pos hi] using topCell_active_eq A c i hi x
      · simpa only [if_neg hi] using hx i hi
  rw [description]
  apply isOpen_iInter_of_finite
  intro i
  by_cases hi : i ∈ c.val.2
  · simp only [not_not.mpr hi, false_implies, setOf_true, isOpen_univ]
  · simp only [hi, not_false_eq_true, true_implies]
    have continuous : Continuous (augmentedForms A i) :=
      (augmentedForms A i).continuous_of_finiteDimensional
    exact (isOpen_lt continuous_const continuous).inter (isOpen_lt continuous continuous_const)

/-- The literal open support consists of the interior of the given cell. -/
def topCellSupport : OpenCellSupport A :=
  ⟨⟨cell (augmentedForms A) c.val.1 c.val.2, topCell_isOpen A c⟩,
    cell_cellwise (augmentedForms A) c.val.1 c.val.2⟩

theorem topCellSupport_convex : Convex ℝ ((topCellSupport A c).val : Set (Fin n → ℝ)) :=
  cell_convex (augmentedForms A) c.val.1 c.val.2

theorem topCellSupport_nonempty : ((topCellSupport A c).val : Set (Fin n → ℝ)).Nonempty :=
  c.property.1

theorem topCellSupport_bounded :
    Bornology.IsBounded ((topCellSupport A c).val : Set (Fin n → ℝ)) :=
  (closedCell_isCompact A c.val.1 c.val.2).isBounded.subset
    (cell_subset_closedCell (augmentedForms A) c.val.1 c.val.2)

/-- A supported cell has exactly the original ceiling and wall labels. -/
theorem topCellSupport_labels {q : ℕ} (d : OpenSupportCell A (topCellSupport A c) q) :
    d.val.val = c.val := by
  obtain ⟨he, hI⟩ := cell_indices_unique (augmentedForms A)
    (cellCenter_mem (augmentedForms A) d.val) d.property
  exact Prod.ext he hI

theorem topCellSupport_dimension {q : ℕ} (d : OpenSupportCell A (topCellSupport A c) q) :
    q = n := by
  have labels := topCellSupport_labels A c d
  have dimension := d.val.property.2
  rw [labels] at dimension
  exact dimension.symm.trans c.property.2

instance topCellSupport_cells_subsingleton (q : ℕ) :
    Subsingleton (OpenSupportCell A (topCellSupport A c) q) :=
  ⟨fun d e => Subtype.ext (Subtype.ext
    ((topCellSupport_labels A c d).trans (topCellSupport_labels A c e).symm))⟩

instance topCellSupport_cells_finite (q : ℕ) :
    Finite (OpenSupportCell A (topCellSupport A c) q) := inferInstance

/-- The one actual characteristic cell retained by this support. -/
def topCellSupport_index : OpenSupportCell A (topCellSupport A c) n :=
  ⟨c, cellCenter_mem (augmentedForms A) c⟩

instance topCellSupport_cells_unique : Unique (OpenSupportCell A (topCellSupport A c) n) where
  default := topCellSupport_index A c
  uniq _ := Subsingleton.elim _ _

theorem topCellSupport_cells_isEmpty (q : ℕ) (different : q ≠ n) :
    IsEmpty (OpenSupportCell A (topCellSupport A c) q) :=
  ⟨fun d => different (topCellSupport_dimension A c d)⟩

variable (k : Type) [Field k]

/-- The original top cochain term has exactly one coefficient. -/
def topCellCochainTermIso :
    (openSupportCochainComplex A k (topCellSupport A c)).X n ≅ ModuleCat.of k k :=
  ((openSupportCochainCoordinates A k (topCellSupport A c) n).trans
    (Finsupp.uniqueLinearEquiv k k (topCellSupport_index A c))).toModuleIso

theorem topCellCochain_isZero_X (q : ℕ) (different : q ≠ n) :
    IsZero ((openSupportCochainComplex A k (topCellSupport A c)).X q) := by
  letI := topCellSupport_cells_isEmpty A c q different
  exact (ModuleCat.isZero_of_subsingleton
    (ModuleCat.of k (OpenSupportCell A (topCellSupport A c) q →₀ k))).of_iso
      (openSupportCochainCoordinates A k (topCellSupport A c) q).toModuleIso

end ToricPower.IntegralArrangement
