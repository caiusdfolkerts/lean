module

public import Continuation.Fano.SegmentSimplexBundleUniformity

/-!
# Every maximal determinant of the segment–simplex normals

The parameter-dependent normal is the only column that changes with `a`.
If a selection contains a cap, adding a multiple of that cap removes the
parameter from the sloping column. If it contains no cap, it is either
dependent or a permutation of the complete simplex-normal family.

Consequently every maximal determinant has absolute value `0`, `1`, or
`|a|`. This statement holds for every integral parameter, without the
inequalities needed for smooth reflexivity of the associated polytope.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace Unimodular.SegmentSimplexBundle

/-- Away from the sloping normal, changing the parameter changes no vector. -/
theorem mem_normals_zero_of_ne_sloping {d : ℕ} {a : ℤ}
    {u : Lattice (d + 1)} (hu : u ∈ normals d a)
    (hne : u ≠ simplexNormal d a none) : u ∈ normals d 0 := by
  rcases Finset.mem_union.mp hu with hu | hu
  · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hu
    cases k with
    | none => exact (hne rfl).elim
    | some k => exact simplexNormal_mem d 0 (some k)
  · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hu
    exact capNormal_mem d 0 b

theorem sloping_ne_cap {d : ℕ} (hd : 1 ≤ d) (a : ℤ) (b : Bool) :
    simplexNormal d a none ≠ capNormal d b := by
  intro h
  let i : Fin d := ⟨0, by omega⟩
  have hi := congrFun h i.castSucc
  norm_num only [simplexNormal_none_castSucc, capNormal_castSucc] at hi

/-- A cap absorbs exactly the parameter-dependent part of the sloping normal. -/
theorem sloping_eq_zero_add_cap (d : ℕ) (a : ℤ) (b : Bool) :
    simplexNormal d a none = simplexNormal d 0 none +
      (a * height b) • capNormal d b := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      simplexNormal_none_last, capNormal_last, zero_add]
    rw [mul_assoc, height_sq, mul_one]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      simplexNormal_none_castSucc, capNormal_castSucc, mul_zero, add_zero]

theorem abs_det_le_one_at_zero {d : ℕ} (hd : 1 ≤ d)
    (u : Fin (d + 1) → Lattice (d + 1))
    (hu : ∀ i, u i ∈ normals d 0) :
    |(Pi.basisFun ℤ (Fin (d + 1))).det u| ≤ 1 := by
  have h := normals_uniform_of_le_one (d := d) (a := 0)
    hd (by omega) (by omega) (by omega)
  exact h (fun i => ⟨u i, hu i⟩)

/-- A maximal selection containing either cap has a unit or zero determinant. -/
theorem abs_det_le_one_of_cap {d : ℕ} (hd : 1 ≤ d) (a : ℤ)
    (u : Fin (d + 1) → Lattice (d + 1))
    (hu : ∀ i, u i ∈ normals d a)
    (j : Fin (d + 1)) (b : Bool) (hj : u j = capNormal d b) :
    |(Pi.basisFun ℤ (Fin (d + 1))).det u| ≤ 1 := by
  let B := Pi.basisFun ℤ (Fin (d + 1))
  by_cases hs : ∃ i, u i = simplexNormal d a none
  · obtain ⟨i, hi⟩ := hs
    have hij : i ≠ j := by
      intro heq
      subst j
      exact sloping_ne_cap hd a b (hi.symm.trans hj)
    by_cases hr : ∃ k, k ≠ i ∧ u k = simplexNormal d a none
    · obtain ⟨k, hki, hk⟩ := hr
      have hzero : B.det u = 0 :=
        B.det.map_eq_zero_of_eq u (hi.trans hk.symm) hki.symm
      simpa only [B, hzero, abs_zero] using (show (0 : ℤ) ≤ 1 by omega)
    · have hother (k : Fin (d + 1)) (hki : k ≠ i) :
          u k ≠ simplexNormal d a none := by
        intro hk
        exact hr ⟨k, hki, hk⟩
      let u₀ := Function.update u i (simplexNormal d 0 none)
      have hu₀ (k : Fin (d + 1)) : u₀ k ∈ normals d 0 := by
        by_cases hki : k = i
        · subst k
          simpa only [u₀, Function.update_self] using simplexNormal_mem d 0 none
        · simp only [u₀, Function.update_of_ne hki]
          exact mem_normals_zero_of_ne_sloping (hu k) (hother k hki)
      have hcol : u i = simplexNormal d 0 none + (a * height b) • u j := by
        rw [hi, hj]
        exact sloping_eq_zero_add_cap d a b
      have hdet : B.det u = B.det u₀ := by
        calc
          B.det u = B.det (Function.update u i (u i)) := by
            rw [Function.update_eq_self]
          _ = B.det (Function.update u i
              (simplexNormal d 0 none + (a * height b) • u j)) := by rw [hcol]
          _ = B.det u₀ + (a * height b) • B.det (Function.update u i (u j)) := by
            rw [AlternatingMap.map_update_add, AlternatingMap.map_update_smul]
          _ = B.det u₀ := by rw [B.det.map_update_self u hij]; simp
      change |B.det u| ≤ 1
      rw [hdet]
      exact abs_det_le_one_at_zero hd u₀ hu₀
  · apply abs_det_le_one_at_zero hd
    intro i
    exact mem_normals_zero_of_ne_sloping (hu i) (fun hi => hs ⟨i, hi⟩)

/-- With no cap present, a selected vector belongs to the complete simplex family. -/
theorem exists_obstruction_index_of_no_cap {d : ℕ} {a : ℤ}
    {u : Lattice (d + 1)} (hu : u ∈ normals d a)
    (hcap : ∀ b, u ≠ capNormal d b) :
    ∃ i : Fin (d + 1), obstructionFamily d a i = u := by
  rcases Finset.mem_union.mp hu with hu | hu
  · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hu
    cases k with
    | none => exact ⟨Fin.last d, by simp [obstructionFamily]⟩
    | some k => exact ⟨k.castSucc, by simp [obstructionFamily]⟩
  · obtain ⟨b, _, heq⟩ := Finset.mem_image.mp hu
    exact (hcap b heq.symm).elim

/-- The full determinant spectrum, in every dimension and for every integer
parameter. No independent-selection or prescribed search range is assumed. -/
theorem normals_determinant_spectrum {d : ℕ} (hd : 1 ≤ d) (a : ℤ)
    (u : Fin (d + 1) → Lattice (d + 1)) (hu : ∀ i, u i ∈ normals d a) :
    |(Pi.basisFun ℤ (Fin (d + 1))).det u| = 0 ∨
      |(Pi.basisFun ℤ (Fin (d + 1))).det u| = 1 ∨
      |(Pi.basisFun ℤ (Fin (d + 1))).det u| = |a| := by
  let B := Pi.basisFun ℤ (Fin (d + 1))
  by_cases hc : ∃ j b, u j = capNormal d b
  · obtain ⟨j, b, hj⟩ := hc
    have hb := abs_det_le_one_of_cap hd a u hu j b hj
    have hnonneg := abs_nonneg (B.det u)
    change |B.det u| = 0 ∨ |B.det u| = 1 ∨ |B.det u| = |a|
    change |B.det u| ≤ 1 at hb
    omega
  · have hindices (j : Fin (d + 1)) :
        ∃ i : Fin (d + 1), obstructionFamily d a i = u j :=
      exists_obstruction_index_of_no_cap (hu j) (fun b h => hc ⟨j, b, h⟩)
    choose f hf using hindices
    have heq : u = obstructionFamily d a ∘ f := by
      funext j
      exact (hf j).symm
    by_cases hinj : Function.Injective f
    · let e : Equiv.Perm (Fin (d + 1)) :=
        Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩
      right
      right
      change |B.det u| = |a|
      have he : u = obstructionFamily d a ∘ e := heq
      rw [he, AlternatingMap.map_perm]
      simp only [B, obstructing_det, Units.smul_def, smul_eq_mul,
        abs_mul, Equiv.Perm.sign_abs, one_mul]
    · left
      have huinj : ¬ Function.Injective u := by
        intro huinj
        apply hinj
        intro j k hjk
        apply huinj
        rw [heq]
        exact congrArg (obstructionFamily d a) hjk
      rw [B.det.map_eq_zero_of_not_injective u huinj, abs_zero]

end Unimodular.SegmentSimplexBundle

#print axioms Unimodular.SegmentSimplexBundle.normals_determinant_spectrum
