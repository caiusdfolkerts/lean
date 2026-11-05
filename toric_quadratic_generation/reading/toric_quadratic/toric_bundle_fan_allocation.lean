module

public import PaperVerification.ToricBundleFanIntegral
public import PaperVerification.ToricSimplexParity
public import PaperVerification.ToricSimplexAdjoint


@[expose] public section
/-!
# Integral homogeneous weights in a genuine bundle lattice

The independent fiber coordinates are an actual subset of an integral
basis.  Finite simplex allocation applies in those coordinates; the omitted
homogeneous coordinate is the remaining total degree.  This retains all
integral targets, all parity classes, and zero coordinates on boundary slices.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

def finsetIntegerExtension {ι : Type*} (s : Finset ι)
    (a : Fin s.card → ℤ) (i : ι) : ℤ :=
  if hi : i ∈ s then a (s.equivFin ⟨i, hi⟩) else 0

theorem finsetIntegerExtension_apply {ι : Type*} (s : Finset ι)
    (a : Fin s.card → ℤ) {i : ι} (hi : i ∈ s) :
    finsetIntegerExtension s a i = a (s.equivFin ⟨i, hi⟩) := by
  simp only [finsetIntegerExtension, dif_pos hi]

theorem sum_finsetIntegerExtension {ι : Type*} (s : Finset ι)
    (a : Fin s.card → ℤ) :
    (∑ i ∈ s, finsetIntegerExtension s a i) = ∑ j, a j := by
  calc
    (∑ i ∈ s, finsetIntegerExtension s a i) =
        ∑ i : s, finsetIntegerExtension s a i :=
      (Finset.sum_coe_sort s (finsetIntegerExtension s a)).symm
    _ = ∑ i : s, a (s.equivFin i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact finsetIntegerExtension_apply s a i.property
    _ = ∑ j, a j := s.equivFin.sum_comp a

theorem sum_finsetIntegerRestriction {ι : Type*} (s : Finset ι) (a : ι → ℤ) :
    (∑ j : Fin s.card, a (s.equivFin.symm j)) = ∑ i ∈ s, a i := by
  calc
    (∑ j : Fin s.card, a (s.equivFin.symm j)) = ∑ i : s, a i :=
      s.equivFin.symm.sum_comp (fun i : s => a i)
    _ = ∑ i ∈ s, a i := Finset.sum_coe_sort s a

theorem finset_simplex_parity_integer {ι : Type*} (s : Finset ι) {k l : ℕ}
    (hk : s.card ≤ k) (hl : s.card ≤ l) (m p : ι → ℤ)
    (hm : ∀ i ∈ s, 0 < m i) (hsum : (∑ i ∈ s, m i) < (k + l : ℕ)) :
    ∃ a b : ι → ℤ,
      (∀ i ∈ s, 0 ≤ a i) ∧ (∑ i ∈ s, a i) ≤ k ∧
      (∀ i ∈ s, 0 ≤ b i) ∧ (∑ i ∈ s, b i) ≤ l ∧
      (∀ i ∈ s, a i + b i = m i) ∧
      (∀ i ∈ s, (a i - p i) % 2 = 0) := by
  let m' : Fin s.card → ℤ := fun j => m (s.equivFin.symm j)
  let p' : Fin s.card → ℤ := fun j => p (s.equivFin.symm j)
  have hm' (j : Fin s.card) : 0 < m' j := hm _ (s.equivFin.symm j).property
  have hsum' : (∑ j, m' j) < (k + l : ℕ) := by
    simpa only [m', sum_finsetIntegerRestriction] using hsum
  obtain ⟨a, b, ha, hb, hab, hpar⟩ :=
    PaperVerification.Toric.simplex_parity_integer hk hl m' p' hm' hsum'
  refine ⟨finsetIntegerExtension s a, finsetIntegerExtension s b,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [finsetIntegerExtension_apply s a hi]
    exact ha.1 _
  · rw [sum_finsetIntegerExtension]
    exact ha.2
  · intro i hi
    rw [finsetIntegerExtension_apply s b hi]
    exact hb.1 _
  · rw [sum_finsetIntegerExtension]
    exact hb.2
  · intro i hi
    simpa only [finsetIntegerExtension_apply s a hi,
      finsetIntegerExtension_apply s b hi, m', Equiv.symm_apply_apply] using
      hab (s.equivFin ⟨i, hi⟩)
  · intro i hi
    simpa only [finsetIntegerExtension_apply s a hi, p', Equiv.symm_apply_apply] using
      hpar (s.equivFin ⟨i, hi⟩)

theorem finset_simplex_adjoint_integer {ι : Type*} (s : Finset ι) {k l : ℕ}
    (hl : s.card + 1 ≤ l) (m : ι → ℤ)
    (hm : ∀ i ∈ s, 0 < m i) (hsum : (∑ i ∈ s, m i) < (k + l : ℕ)) :
    ∃ a b : ι → ℤ,
      (∀ i ∈ s, 0 ≤ a i) ∧ (∑ i ∈ s, a i) ≤ k ∧
      (∀ i ∈ s, 0 < b i) ∧ (∑ i ∈ s, b i) < l ∧
      (∀ i ∈ s, a i + b i = m i) := by
  let m' : Fin s.card → ℤ := fun j => m (s.equivFin.symm j)
  have hm' (j : Fin s.card) : 0 < m' j := hm _ (s.equivFin.symm j).property
  have hsum' : (∑ j, m' j) < (k + l : ℕ) := by
    simpa only [m', sum_finsetIntegerRestriction] using hsum
  obtain ⟨a, b, ha, hbpos, hbsum, hab⟩ :=
    PaperVerification.Toric.simplex_adjoint_integer hl m' hm' hsum'
  refine ⟨finsetIntegerExtension s a, finsetIntegerExtension s b,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [finsetIntegerExtension_apply s a hi]
    exact ha.1 _
  · rw [sum_finsetIntegerExtension]
    exact ha.2
  · intro i hi
    rw [finsetIntegerExtension_apply s b hi]
    exact hbpos _
  · rw [sum_finsetIntegerExtension]
    exact hbsum
  · intro i hi
    simpa only [finsetIntegerExtension_apply s a hi,
      finsetIntegerExtension_apply s b hi, m', Equiv.symm_apply_apply] using
      hab (s.equivFin ⟨i, hi⟩)

namespace SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} {R : «Σ».PrimitiveRelation}
  (c : R.BundleCoordinates)

theorem fiber_basis_ne_omitted {i : Fin n} (hi : i ∈ c.fiberIndices) :
    c.basis i ≠ c.omitted := by
  have h := c.fiber_ray_set ▸ Finset.mem_image.mpr ⟨i, hi, rfl⟩
  exact (Finset.mem_erase.mp h).1

theorem integer_weight_sum_split (f : Lattice n → ℤ) :
    (∑ v ∈ R.positive, f v) =
      (∑ i ∈ c.fiberIndices, f (c.basis i)) + f c.omitted := by
  rw [← Finset.sum_erase_add R.positive f c.omitted_mem,
    ← c.fiber_ray_set, Finset.sum_image]
  exact fun i _ j _ hij => c.basis.injective hij

def homogeneousIntegerExtension (k : ℤ) (a : Fin n → ℤ) (v : Lattice n) : ℤ :=
  if v = c.omitted then k - ∑ i ∈ c.fiberIndices, a i
  else ∑ i ∈ c.fiberIndices, if c.basis i = v then a i else 0

@[simp] theorem homogeneousIntegerExtension_omitted (k : ℤ) (a : Fin n → ℤ) :
    c.homogeneousIntegerExtension k a c.omitted = k - ∑ i ∈ c.fiberIndices, a i := by
  simp only [homogeneousIntegerExtension, if_pos rfl, ite_true]

theorem homogeneousIntegerExtension_basis (k : ℤ) (a : Fin n → ℤ)
    {i : Fin n} (hi : i ∈ c.fiberIndices) :
    c.homogeneousIntegerExtension k a (c.basis i) = a i := by
  rw [homogeneousIntegerExtension, if_neg (c.fiber_basis_ne_omitted hi)]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    exact if_neg (fun h => hji (c.basis.injective h))
  · exact fun h => (h hi).elim

theorem homogeneousIntegerExtension_total (k : ℤ) (a : Fin n → ℤ) :
    (∑ v ∈ R.positive, c.homogeneousIntegerExtension k a v) = k := by
  rw [c.integer_weight_sum_split, c.homogeneousIntegerExtension_omitted]
  have he : (∑ i ∈ c.fiberIndices, c.homogeneousIntegerExtension k a (c.basis i)) =
      ∑ i ∈ c.fiberIndices, a i :=
    Finset.sum_congr rfl (fun i hi => c.homogeneousIntegerExtension_basis k a hi)
  rw [he]
  ring

theorem homogeneousIntegerExtension_nonneg (k : ℤ) (a : Fin n → ℤ)
    (ha : ∀ i ∈ c.fiberIndices, 0 ≤ a i)
    (hsum : (∑ i ∈ c.fiberIndices, a i) ≤ k) :
    ∀ v ∈ R.positive, 0 ≤ c.homogeneousIntegerExtension k a v := by
  intro v hv
  by_cases he : v = c.omitted
  · rw [he, c.homogeneousIntegerExtension_omitted]
    exact sub_nonneg.mpr hsum
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp
      (c.fiber_ray_set.symm ▸ Finset.mem_erase.mpr ⟨he, hv⟩)
    rw [c.homogeneousIntegerExtension_basis k a hi]
    exact ha i hi

theorem homogeneousIntegerExtension_pos (k : ℤ) (a : Fin n → ℤ)
    (ha : ∀ i ∈ c.fiberIndices, 0 < a i)
    (hsum : (∑ i ∈ c.fiberIndices, a i) < k) :
    ∀ v ∈ R.positive, 0 < c.homogeneousIntegerExtension k a v := by
  intro v hv
  by_cases he : v = c.omitted
  · rw [he, c.homogeneousIntegerExtension_omitted]
    exact sub_pos.mpr hsum
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp
      (c.fiber_ray_set.symm ▸ Finset.mem_erase.mpr ⟨he, hv⟩)
    rw [c.homogeneousIntegerExtension_basis k a hi]
    exact ha i hi

theorem homogeneousIntegerExtension_sum (k l : ℤ) (a b : Fin n → ℤ)
    (γ : Lattice n → ℤ) (hγ : (∑ v ∈ R.positive, γ v) = k + l)
    (hab : ∀ i ∈ c.fiberIndices, a i + b i = γ (c.basis i)) :
    ∀ v ∈ R.positive,
      c.homogeneousIntegerExtension k a v + c.homogeneousIntegerExtension l b v = γ v := by
  intro v hv
  by_cases he : v = c.omitted
  · subst v
    rw [c.homogeneousIntegerExtension_omitted, c.homogeneousIntegerExtension_omitted]
    have hs : (∑ i ∈ c.fiberIndices, a i) + (∑ i ∈ c.fiberIndices, b i) =
        ∑ i ∈ c.fiberIndices, γ (c.basis i) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl hab
    rw [c.integer_weight_sum_split] at hγ
    linarith
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp
      (c.fiber_ray_set.symm ▸ Finset.mem_erase.mpr ⟨he, hv⟩)
    rw [c.homogeneousIntegerExtension_basis k a hi,
      c.homogeneousIntegerExtension_basis l b hi]
    exact hab i hi

/-- Full integral fiber allocation with unrestricted prescribed parity on
the independent lattice fiber coordinates. -/
theorem homogeneous_parity_allocation {k l : ℕ}
    (hk : c.fiberIndices.card ≤ k) (hl : c.fiberIndices.card ≤ l)
    (γ p : Lattice n → ℤ)
    (hγ : (∑ v ∈ R.positive, γ v) = (k + l : ℕ))
    (hγpos : ∀ v ∈ R.positive, 0 < γ v) :
    ∃ α β : Lattice n → ℤ,
      (∑ v ∈ R.positive, α v) = k ∧ (∑ v ∈ R.positive, β v) = l ∧
      (∀ v ∈ R.positive, 0 ≤ α v) ∧ (∀ v ∈ R.positive, 0 ≤ β v) ∧
      (∀ v ∈ R.positive, α v + β v = γ v) ∧
      (∀ i ∈ c.fiberIndices, (α (c.basis i) - p (c.basis i)) % 2 = 0) := by
  have hpos (i : Fin n) (hi : i ∈ c.fiberIndices) : 0 < γ (c.basis i) :=
    hγpos _ (c.fiber_subset_positive (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
  have hsum : (∑ i ∈ c.fiberIndices, γ (c.basis i)) < (k + l : ℕ) := by
    rw [c.integer_weight_sum_split] at hγ
    have hp := hγpos c.omitted c.omitted_mem
    linarith
  obtain ⟨a, b, ha0, ha, hb0, hb, hab, hpar⟩ := finset_simplex_parity_integer
    c.fiberIndices hk hl (fun i => γ (c.basis i)) (fun i => p (c.basis i)) hpos hsum
  refine ⟨c.homogeneousIntegerExtension k a, c.homogeneousIntegerExtension l b,
    c.homogeneousIntegerExtension_total _ _, c.homogeneousIntegerExtension_total _ _,
    c.homogeneousIntegerExtension_nonneg _ _ ha0 ha,
    c.homogeneousIntegerExtension_nonneg _ _ hb0 hb,
    c.homogeneousIntegerExtension_sum _ _ a b γ (by simpa using hγ) hab, ?_⟩
  intro i hi
  rw [c.homogeneousIntegerExtension_basis _ a hi]
  exact hpar i hi

theorem homogeneous_adjoint_allocation {k l : ℕ}
    (hl : c.fiberIndices.card + 1 ≤ l) (γ : Lattice n → ℤ)
    (hγ : (∑ v ∈ R.positive, γ v) = (k + l : ℕ))
    (hγpos : ∀ v ∈ R.positive, 0 < γ v) :
    ∃ α β : Lattice n → ℤ,
      (∑ v ∈ R.positive, α v) = k ∧ (∑ v ∈ R.positive, β v) = l ∧
      (∀ v ∈ R.positive, 0 ≤ α v) ∧ (∀ v ∈ R.positive, 0 < β v) ∧
      (∀ v ∈ R.positive, α v + β v = γ v) := by
  have hpos (i : Fin n) (hi : i ∈ c.fiberIndices) : 0 < γ (c.basis i) :=
    hγpos _ (c.fiber_subset_positive (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
  have hsum : (∑ i ∈ c.fiberIndices, γ (c.basis i)) < (k + l : ℕ) := by
    rw [c.integer_weight_sum_split] at hγ
    have hp := hγpos c.omitted c.omitted_mem
    linarith
  obtain ⟨a, b, ha0, ha, hbpos, hb, hab⟩ := finset_simplex_adjoint_integer
    c.fiberIndices hl (fun i => γ (c.basis i)) hpos hsum
  exact ⟨c.homogeneousIntegerExtension k a, c.homogeneousIntegerExtension l b,
    c.homogeneousIntegerExtension_total _ _, c.homogeneousIntegerExtension_total _ _,
    c.homogeneousIntegerExtension_nonneg _ _ ha0 ha,
    c.homogeneousIntegerExtension_pos _ _ hbpos hb,
    c.homogeneousIntegerExtension_sum _ _ a b γ (by simpa using hγ) hab⟩

end SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

end PaperVerification.ToricGeometry
