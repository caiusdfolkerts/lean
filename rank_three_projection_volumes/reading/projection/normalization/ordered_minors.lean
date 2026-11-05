module
public import Projection.Normalization.MinorMaximum
public import Mathlib.Data.Finset.Sort

/-! # Ordered representatives of actual maximal minors -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace ProjectionVolumes

/-- An injective list enumerates its literal finite image bijectively. -/
def imageEnumeration {n k : ℕ} (f : Fin k → Fin n) (hf : Function.Injective f) :
    Fin k ≃ (Finset.univ.image f : Finset (Fin n)) :=
  Equiv.ofBijective
    (fun i => ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
    ⟨fun i j hij => hf (congrArg Subtype.val hij), by
      rintro ⟨x, hx⟩
      obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨i, rfl⟩⟩

@[simp] theorem imageEnumeration_val {n k : ℕ} (f : Fin k → Fin n)
    (hf : Function.Injective f) (i : Fin k) :
    (imageEnumeration f hf i).val = f i := rfl

/-- Every injective enumeration differs from its increasing enumeration by a
permutation of its domain. -/
theorem exists_sorting_permutation {n k : ℕ} (f : Fin k → Fin n)
    (hf : Function.Injective f) :
    ∃ (s : Finset (Fin n)) (hs : s.card = k) (e : Equiv.Perm (Fin k)),
      (∀ i, f (e i) = s.orderEmbOfFin hs i) := by
  let s := Finset.univ.image f
  have hs : s.card = k := by
    simp only [s, Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  let e := (s.orderIsoOfFin hs).toEquiv.trans (imageEnumeration f hf).symm
  refine ⟨s, hs, e, ?_⟩
  intro i
  have h := congrArg Subtype.val
    ((imageEnumeration f hf).apply_symm_apply ((s.orderIsoOfFin hs) i))
  exact h

/-- The positive maximum of absolute minors is attained using the canonical
increasing row and column enumerations of two finite subsets. -/
theorem exists_ordered_maximal_minor {n k : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hpos : 0 < minorMaximum M k) :
    ∃ (I J : Finset (Fin n)) (hI : I.card = k) (hJ : J.card = k),
      |(M.submatrix (J.orderEmbOfFin hJ) (I.orderEmbOfFin hI)).det| =
        minorMaximum M k := by
  obtain ⟨rows, cols, hdet⟩ := exists_maximal_minor M hpos
  have hne : (M.submatrix rows cols).det ≠ 0 := abs_pos.mp (hdet.symm ▸ hpos)
  obtain ⟨J, hJ, er, her⟩ :=
    exists_sorting_permutation rows (injective_rows_of_minor_ne_zero M rows cols hne)
  obtain ⟨I, hI, ec, hec⟩ :=
    exists_sorting_permutation cols (injective_cols_of_minor_ne_zero M rows cols hne)
  refine ⟨I, J, hI, hJ, ?_⟩
  have hmat : (M.submatrix rows cols).submatrix er ec =
      M.submatrix (J.orderEmbOfFin hJ) (I.orderEmbOfFin hI) := by
    ext i j
    simp only [Matrix.submatrix_apply, her, hec]
  rw [← hmat, Matrix.abs_det_submatrix_equiv_equiv, hdet]

end ProjectionVolumes
