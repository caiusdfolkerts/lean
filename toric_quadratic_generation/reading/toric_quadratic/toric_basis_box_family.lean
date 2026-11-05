module
public import PaperVerification.ToricBoxAverages
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Data.Fintype.EquivFin
@[expose] public section
/-!
# A finite family of genuine basis boxes

This packages the column-configuration form of the lattice-covering theorem
for a finite family of unrelated real bases. The selected column subsets are
proved to be genuine bases, and their zonotopes are identified with the
ordinary unit boxes in the given basis coordinates.
-/

noncomputable section

namespace PaperVerification.Toric

open scoped BigOperators

variable {J : Type*} [Fintype J] {d : ℕ}

/-- A point in the convex hull of a finite family has a probability vector on
the whole index type, with zero coefficients on unused indices. -/
theorem exists_probability_of_mem_convexHull_range {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (v : J → E) {x : E}
    (hx : x ∈ convexHull ℝ (Set.range v)) :
    ∃ p : J → ℝ, (∀ j, 0 ≤ p j) ∧ (∑ j, p j) = 1 ∧ ∑ j, p j • v j = x := by
  classical
  rw [convexHull_range_eq_exists_affineCombination] at hx
  obtain ⟨s, w, hw, hsum, hcomb⟩ := hx
  let p : J → ℝ := fun j => if j ∈ s then w j else 0
  have hp : ∀ j, 0 ≤ p j := by
    intro j
    by_cases hj : j ∈ s
    · simpa [p, hj] using hw j hj
    · simp [p, hj]
  refine ⟨p, hp, ?_, ?_⟩
  · simpa [p, Finset.sum_ite_mem] using hsum
  · rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum] at hcomb
    simpa [p, ite_smul, Finset.sum_ite_mem] using hcomb

def familyIndexEquiv : (J × Fin d) ≃ Fin (Fintype.card (J × Fin d)) :=
  Fintype.equivFin _

def familyMatrix (b : J → Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))) :
    Matrix (Fin d) (Fin (Fintype.card (J × Fin d))) ℝ :=
  fun i k => b (familyIndexEquiv.symm k).1 (familyIndexEquiv.symm k).2 i

def familySubset (j : J) : Finset (Fin (Fintype.card (J × Fin d))) :=
  Finset.univ.image (fun i : Fin d => familyIndexEquiv (j, i))

theorem familyIndex_injective (j : J) :
    Function.Injective (fun i : Fin d => familyIndexEquiv (j, i)) := by
  intro i k hik
  exact congrArg Prod.snd (familyIndexEquiv.injective hik)

@[simp] theorem familySubset_card (j : J) : (familySubset (d := d) j).card = d := by
  rw [familySubset, Finset.card_image_of_injective _ (familyIndex_injective j)]
  simp

theorem mem_familySubset (j : J) (k : Fin (Fintype.card (J × Fin d))) :
    k ∈ familySubset j ↔ ∃ i : Fin d, familyIndexEquiv (j, i) = k := by
  simp [familySubset]

@[simp] theorem familyMatrix_column
    (b : J → Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))) (j : J) (i : Fin d) :
    matrixColumn (familyMatrix b) (familyIndexEquiv (j, i)) = b j i := by
  ext k
  simp [matrixColumn, familyMatrix, familyIndexEquiv]

/-- Each selected column subset is a genuine full real basis. -/
theorem familySubset_squaredMinor_pos
    (b : J → Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))) (j : J) :
    0 < squaredMinor (familyMatrix b) (familySubset j) := by
  let s := familySubset (d := d) j
  have hs : s.card = d := familySubset_card j
  apply (squaredMinor_pos_iff (familyMatrix b) s).mpr
  refine ⟨hs, ?_⟩
  rw [column_minor_ne_zero_iff_linearIndependent]
  let φ : Fin d → Fin d := fun i => (familyIndexEquiv.symm (s.orderEmbOfFin hs i)).2
  have hfirst (i : Fin d) : (familyIndexEquiv.symm (s.orderEmbOfFin hs i)).1 = j := by
    have himem : s.orderEmbOfFin hs i ∈ familySubset j := s.orderEmbOfFin_mem hs i
    obtain ⟨k, hk⟩ := (mem_familySubset j _).mp himem
    rw [← hk]
    simp
  have hφ : Function.Injective φ := by
    intro i k hik
    apply (s.orderEmbOfFin hs).injective
    apply familyIndexEquiv.symm.injective
    exact Prod.ext (by rw [hfirst, hfirst]) hik
  have hvec (i : Fin d) :
      matrixColumn (familyMatrix b) (s.orderEmbOfFin hs i) = b j (φ i) := by
    have he : s.orderEmbOfFin hs i = familyIndexEquiv (j, φ i) := by
      apply familyIndexEquiv.symm.injective
      simp only [Equiv.symm_apply_apply]
      exact Prod.ext (hfirst i) rfl
    rw [he, familyMatrix_column]
  simpa only [Function.comp_def, hvec] using (b j).linearIndependent.comp φ hφ

/-- The selected global column box is the ordinary unit box in the original basis. -/
theorem familySubsetBox_coordinates
    (b : J → Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))) (j : J)
    {z : EuclideanSpace ℝ (Fin d)}
    (hz : z ∈ SubsetBox (matrixColumn (familyMatrix b)) (familySubset j)) :
    ∃ t : Fin d → ℝ, (∀ i, |t i| ≤ 1 / 2) ∧ ∑ i, t i • b j i = z := by
  classical
  obtain ⟨u, hu, husum⟩ := hz
  let t : Fin d → ℝ := fun i => u (familyIndexEquiv (j, i))
  have ht (i : Fin d) : |t i| ≤ 1 / 2 := by
    have hi : familyIndexEquiv (j, i) ∈ familySubset j :=
      (mem_familySubset j _).mpr ⟨i, rfl⟩
    simpa only [hi, ite_true, t] using hu (familyIndexEquiv (j, i))
  refine ⟨t, ht, ?_⟩
  have hout (k : Fin (Fintype.card (J × Fin d))) (hk : k ∉ familySubset j) : u k = 0 := by
    have h := hu k
    simp only [hk, ite_false, zero_div] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  calc
    (∑ i, t i • b j i) =
        ∑ k ∈ familySubset j, u k • matrixColumn (familyMatrix b) k := by
      rw [familySubset, Finset.sum_image]
      · simp only [familyMatrix_column, t]
      · intro i _ k _ hik
        exact familyIndex_injective j hik
    _ = ∑ k, u k • matrixColumn (familyMatrix b) k := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro k _ hk
      simp [hout k hk]
    _ = z := husum

/-- Arbitrary matched integral basis boxes yield a lattice decomposition whenever
the target is a convex combination of their matched centers. -/
theorem finite_basis_boxes_lattice_decomposition
    (b : J → Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (Γ : AddSubgroup (EuclideanSpace ℝ (Fin d)))
    (hclosed : IsClosed (Γ : Set (EuclideanSpace ℝ (Fin d))))
    (hbΓ : ∀ j i, b j i ∈ Γ)
    (A B : Set (EuclideanSpace ℝ (Fin d))) (hA : Convex ℝ A) (hB : Convex ℝ B)
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1)
    (a c : J → EuclideanSpace ℝ (Fin d))
    (hboxA : ∀ j (t : Fin d → ℝ), (∀ i, |t i| ≤ 1 / 2) →
      a j + ∑ i, t i • b j i ∈ A)
    (hboxB : ∀ j (t : Fin d → ℝ), (∀ i, |t i| ≤ 1 / 2) →
      c j + ∑ i, t i • b j i ∈ B)
    (m : EuclideanSpace ℝ (Fin d)) (hmΓ : m ∈ Γ)
    (hm : m = ∑ j, p j • (a j + c j)) :
    ∃ x ∈ A, ∃ y ∈ B, x ∈ Γ ∧ y ∈ Γ ∧ x + y = m := by
  have hVΓ (k : Fin (Fintype.card (J × Fin d))) : matrixColumn (familyMatrix b) k ∈ Γ := by
    obtain ⟨⟨j, i⟩, rfl⟩ := familyIndexEquiv.surjective k
    simpa only [familyMatrix_column] using hbΓ j i
  apply matched_boxes_lattice_decomposition (familyMatrix b) Γ hclosed hVΓ
    A B hA hB (familySubset (d := d)) (familySubset_squaredMinor_pos b)
    p hp hpsum a c ?_ ?_ m hmΓ hm
  · intro j z hz
    obtain ⟨t, ht, rfl⟩ := familySubsetBox_coordinates b j hz
    exact hboxA j t ht
  · intro j z hz
    obtain ⟨t, ht, rfl⟩ := familySubsetBox_coordinates b j hz
    exact hboxB j t ht

/-- The same finite-family theorem in ordinary real coordinate space. The
change from the Euclidean norm to the usual product norm is made by a genuine
continuous linear equivalence, preserving the subgroup and all box points. -/
theorem finite_basis_boxes_lattice_decomposition_pi
    (b : J → Module.Basis (Fin d) ℝ (Fin d → ℝ))
    (Γ : AddSubgroup (Fin d → ℝ))
    (hclosed : IsClosed (Γ : Set (Fin d → ℝ))) (hbΓ : ∀ j i, b j i ∈ Γ)
    (A B : Set (Fin d → ℝ)) (hA : Convex ℝ A) (hB : Convex ℝ B)
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1)
    (a c : J → (Fin d → ℝ))
    (hboxA : ∀ j (t : Fin d → ℝ), (∀ i, |t i| ≤ 1 / 2) →
      a j + ∑ i, t i • b j i ∈ A)
    (hboxB : ∀ j (t : Fin d → ℝ), (∀ i, |t i| ≤ 1 / 2) →
      c j + ∑ i, t i • b j i ∈ B)
    (m : Fin d → ℝ) (hmΓ : m ∈ Γ)
    (hm : m = ∑ j, p j • (a j + c j)) :
    ∃ x ∈ A, ∃ y ∈ B, x ∈ Γ ∧ y ∈ Γ ∧ x + y = m := by
  let e : EuclideanSpace ℝ (Fin d) ≃L[ℝ] (Fin d → ℝ) :=
    EuclideanSpace.equiv (Fin d) ℝ
  let b' : J → Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
    fun j => (b j).map e.symm.toLinearEquiv
  let Γ' : AddSubgroup (EuclideanSpace ℝ (Fin d)) :=
    Γ.comap e.toLinearMap.toAddMonoidHom
  have hclosed' : IsClosed (Γ' : Set (EuclideanSpace ℝ (Fin d))) :=
    hclosed.preimage e.continuous
  have hbΓ' (j : J) (i : Fin d) : b' j i ∈ Γ' := by
    change e (b' j i) ∈ Γ
    simpa [b', Module.Basis.map_apply] using hbΓ j i
  have hboxA' (j : J) (t : Fin d → ℝ) (ht : ∀ i, |t i| ≤ 1 / 2) :
      e.symm (a j) + ∑ i, t i • b' j i ∈ e ⁻¹' A := by
    change e (e.symm (a j) + ∑ i, t i • b' j i) ∈ A
    simpa [b', map_add, map_sum, map_smul, Module.Basis.map_apply] using hboxA j t ht
  have hboxB' (j : J) (t : Fin d → ℝ) (ht : ∀ i, |t i| ≤ 1 / 2) :
      e.symm (c j) + ∑ i, t i • b' j i ∈ e ⁻¹' B := by
    change e (e.symm (c j) + ∑ i, t i • b' j i) ∈ B
    simpa [b', map_add, map_sum, map_smul, Module.Basis.map_apply] using hboxB j t ht
  have hm' : e.symm m = ∑ j, p j • (e.symm (a j) + e.symm (c j)) := by
    apply e.injective
    simpa only [map_add, map_sum, map_smul, ContinuousLinearEquiv.apply_symm_apply] using hm
  have hmΓ' : e.symm m ∈ Γ' := by
    change e (e.symm m) ∈ Γ
    simpa using hmΓ
  obtain ⟨x, hx, y, hy, hxΓ, hyΓ, hxy⟩ :=
    finite_basis_boxes_lattice_decomposition b' Γ' hclosed' hbΓ'
      (e ⁻¹' A) (e ⁻¹' B) (hA.linear_preimage e.toLinearMap) (hB.linear_preimage e.toLinearMap)
      p hp hpsum (fun j => e.symm (a j)) (fun j => e.symm (c j))
      hboxA' hboxB' (e.symm m) hmΓ' hm'
  refine ⟨e x, hx, e y, hy, hxΓ, hyΓ, ?_⟩
  simpa only [map_add, ContinuousLinearEquiv.apply_symm_apply] using congrArg e hxy

end PaperVerification.Toric
