module

public import Unimodular.Extensions

@[expose] public section

noncomputable section

namespace Unimodular.Heller

open scoped BigOperators

section Basis

variable {I M : Type*} [Fintype I] [DecidableEq I]
  [AddCommGroup M] [Module ℤ M]

/-- A two-column Cramer identity, retaining its sign. -/
theorem det_replace_two (b : Module.Basis I ℤ M) (x y : M) {i j : I} (hij : i ≠ j) :
    b.det (Function.update (Function.update b i x) j y) =
      b.repr x i * b.repr y j - b.repr x j * b.repr y i := by
  have hi : b.det (Function.update (Function.update b i x) j (b i)) = -b.repr x j := by
    have he : Function.update (Function.update b i x) j (b i) =
        (Function.update b j x) ∘ Equiv.swap i j := by
      funext k
      by_cases hki : k = i
      · subst k
        simp [hij, Ne.symm hij]
      · by_cases hkj : k = j
        · subst k
          simp [hij, Ne.symm hij]
        · simp [hki, hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]
    rw [he, b.det.map_swap _ hij, IntegralRigidity.det_replace_basis]
  have hj : b.det (Function.update (Function.update b i x) j (b j)) = b.repr x i := by
    have he : Function.update (Function.update b i x) j (b j) = Function.update b i x := by
      rw [Function.update_comm hij]
      simp
    rw [he, IntegralRigidity.det_replace_basis]
  have ho (k : I) (hki : k ≠ i) (hkj : k ≠ j) :
      b.det (Function.update (Function.update b i x) j (b k)) = 0 := by
    apply b.det.map_eq_zero_of_eq _ (i := j) (j := k) _ (Ne.symm hkj)
    simp [hki, hkj]
  conv_lhs => rw [← b.sum_repr y]
  rw [b.det.map_update_sum]
  simp only [b.det.map_update_smul, smul_eq_mul]
  calc
    _ = ∑ k, ((if k = i then b.repr y i * (-b.repr x j) else 0) +
        (if k = j then b.repr y j * b.repr x i else 0)) := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hki : k = i
      · subst k
        simp [hi, hij]
      · by_cases hkj : k = j
        · subst k
          simp [hj, Ne.symm hij]
        · simp [hki, hkj, ho k hki hkj]
    _ = _ := by simp [Finset.sum_add_distrib]; ring

/-- All coordinates of a ray in a ray basis belong to {-1,0,1}. -/
theorem coordinate_abs_le_one (b : Module.Basis I ℤ M) (U : Set M)
    (hU : IntegralRigidity.Uniform b (fun x : U => x.val))
    (hb : ∀ i, b i ∈ U) {x : M} (hx : x ∈ U) (i : I) :
    |b.repr x i| ≤ 1 := by
  let labels : I → U := fun j => ⟨b j, hb j⟩
  have h := hU (Function.update labels i ⟨x, hx⟩)
  have he : (fun x : U => x.val) ∘ Function.update labels i ⟨x, hx⟩ =
      Function.update b i x := by
    funext j
    by_cases hji : j = i <;> simp [labels, hji]
  rwa [he, IntegralRigidity.det_replace_basis] at h

/-- Uniform unimodularity bounds every two-column replacement minor. -/
theorem two_coordinate_minor_abs_le_one (b : Module.Basis I ℤ M) (U : Set M)
    (hU : IntegralRigidity.Uniform b (fun x : U => x.val))
    (hb : ∀ i, b i ∈ U) {x y : M} (hx : x ∈ U) (hy : y ∈ U)
    {i j : I} (hij : i ≠ j) :
    |b.repr x i * b.repr y j - b.repr x j * b.repr y i| ≤ 1 := by
  let labels : I → U := fun k => ⟨b k, hb k⟩
  have h := hU (Function.update (Function.update labels i ⟨x, hx⟩) j ⟨y, hy⟩)
  have he : (fun x : U => x.val) ∘
      Function.update (Function.update labels i ⟨x, hx⟩) j ⟨y, hy⟩ =
      Function.update (Function.update b i x) j y := by
    funext k
    by_cases hkj : k = j
    · subst k
      simp
    · by_cases hki : k = i <;> simp [labels, hki, hkj, hij]
  rwa [he, det_replace_two b x y hij] at h

end Basis

section Projection

variable {n : ℕ}

/-- Projection along the first standard basis vector. -/
def tail (x : Lattice (n + 1)) : Lattice n := fun i => x i.succ

/-- The nonzero projected columns, with coincident columns identified. -/
def projected (U : Set (Lattice (n + 1))) : Set (Lattice n) :=
  {q | q ≠ 0 ∧ ∃ x ∈ U, tail x = q}

@[simp] theorem tail_zero : tail (0 : Lattice (n + 1)) = 0 := rfl
@[simp] theorem tail_neg (x : Lattice (n + 1)) : tail (-x) = -tail x := rfl

/-- A first coordinate basis vector contributes a determinant factor one. -/
theorem det_cons_first (v : Fin n → Lattice (n + 1)) :
    (Pi.basisFun ℤ (Fin (n + 1))).det
      (Fin.cons (Pi.single 0 1) v) =
      (Pi.basisFun ℤ (Fin n)).det (fun i => tail (v i)) := by
  rw [Pi.basisFun_det_apply, Pi.basisFun_det_apply, Matrix.det_succ_row_zero]
  simp [Matrix.submatrix, Fin.cons_zero, Fin.cons_succ, Pi.single_apply,
    Fin.succAbove_zero, tail] <;> rfl

/-- Deleting the first row and discarding zero columns preserves uniform
unimodularity whenever that row is the coordinate of a prescribed basis ray. -/
theorem projected_uniform (U : Set (Lattice (n + 1)))
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin (n + 1))) (fun x : U => x.val))
    (he : Pi.single 0 1 ∈ U) :
    IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun q : projected U => q.val) := by
  intro a
  choose x hx hproj using fun i => (a i).property.2
  let labels : Fin (n + 1) → U := Fin.cons ⟨Pi.single 0 1, he⟩ (fun i => ⟨x i, hx i⟩)
  have h := hU labels
  have heq : (fun x : U => x.val) ∘ labels = Fin.cons (Pi.single 0 1) x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  rw [heq, det_cons_first] at h
  have hq : (fun i => tail (x i)) = (fun q : projected U => q.val) ∘ a := funext hproj
  rwa [hq] at h

/-- Every projected standard basis ray remains in the projected system. -/
theorem projected_contains_basis (U : Set (Lattice (n + 1)))
    (hb : ∀ i, (Pi.basisFun ℤ (Fin (n + 1))) i ∈ U) :
    ∀ i, (Pi.basisFun ℤ (Fin n)) i ∈ projected U := by
  intro i
  refine ⟨(Pi.basisFun ℤ (Fin n)).ne_zero i,
    (Pi.basisFun ℤ (Fin (n + 1))) i.succ, hb i.succ, ?_⟩
  ext j
  simp [tail, Pi.basisFun_apply, Pi.single_apply, Fin.succ_inj]

/-- Two distinct columns above a nonzero projected column differ in height
by exactly one. This is the actual quotient-fiber statement used in the count. -/
theorem equal_tail_height_distance (U : Set (Lattice (n + 1)))
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin (n + 1))) (fun x : U => x.val))
    (hb : ∀ i, (Pi.basisFun ℤ (Fin (n + 1))) i ∈ U)
    {x y : Lattice (n + 1)} (hx : x ∈ U) (hy : y ∈ U)
    (ht : tail x = tail y) (hnz : tail x ≠ 0) (hne : x ≠ y) :
    |x 0 - y 0| = 1 := by
  have hex : ∃ i : Fin n, x i.succ ≠ 0 := by
    contrapose! hnz
    ext i
    exact hnz i
  obtain ⟨i, hi⟩ := hex
  have hc := coordinate_abs_le_one (Pi.basisFun ℤ (Fin (n + 1))) U hU hb hx i.succ
  have hci : |x i.succ| = 1 := by
    have hp := abs_pos.mpr hi
    simp only [Pi.basisFun_repr] at hc
    omega
  have hm := two_coordinate_minor_abs_le_one (Pi.basisFun ℤ (Fin (n + 1))) U hU hb hx hy
    (i := 0) (j := i.succ) (Fin.succ_ne_zero i).symm
  have hti : x i.succ = y i.succ := congrFun ht i
  have hd : x 0 ≠ y 0 := by
    intro he
    apply hne
    ext j
    refine Fin.cases he (fun k => ?_) j
    exact congrFun ht k
  have hab : |x 0 - y 0| ≤ 1 := by
    simp only [Pi.basisFun_repr, ← hti] at hm
    have he : x 0 * x i.succ - x i.succ * y 0 = (x 0 - y 0) * x i.succ := by ring
    rw [he, abs_mul, hci, mul_one] at hm
    exact hm
  have hp := abs_pos.mpr (sub_ne_zero.mpr hd)
  omega

end Projection
end Unimodular.Heller

end
