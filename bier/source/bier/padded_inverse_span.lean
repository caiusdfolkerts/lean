import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-! # The span bound for padded principal inverses

The proof uses diagonal commutators. If the only commuting diagonals are
constant, their trace constraints have codimension at least `m-1`. Otherwise
a nonconstant commuting diagonal forces a zero coordinate in every row of
every principal inverse, giving the stronger bound `m(m-1)`.
-/

noncomputable section

namespace Bier

open Classical Finset Matrix Module

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def diagonalCommutator (G : Matrix ι ι ℝ) : (ι → ℝ) →ₗ[ℝ] Matrix ι ι ℝ where
  toFun d := diagonal d * G - G * diagonal d
  map_add' d e := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, diagonal_mul, mul_diagonal, Pi.add_apply]
    ring
  map_smul' c d := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, diagonal_mul, mul_diagonal, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem diagonalCommutator_apply (G : Matrix ι ι ℝ) (d : ι → ℝ) (i j : ι) :
    diagonalCommutator G d i j = (d i - d j) * G i j := by
  simp only [diagonalCommutator, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.sub_apply, diagonal_mul, mul_diagonal]
  ring

def matrixTracePairing : Matrix ι ι ℝ →ₗ[ℝ] Module.Dual ℝ (Matrix ι ι ℝ) where
  toFun A :=
    { toFun := fun W => (A * W).trace
      map_add' := fun W Z => by rw [Matrix.mul_add, Matrix.trace_add]
      map_smul' := fun c W => by simp [Matrix.mul_smul] }
  map_add' A B := by ext W; simp [Matrix.add_mul]
  map_smul' c A := by ext W; simp [Matrix.smul_mul]

theorem matrixTracePairing_injective : Function.Injective
    (matrixTracePairing : Matrix ι ι ℝ →ₗ[ℝ] Module.Dual ℝ (Matrix ι ι ℝ)) := by
  intro A B h
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro W
  exact congrArg (fun f : Module.Dual ℝ (Matrix ι ι ℝ) => f W) h

def commutatorConstraints (G : Matrix ι ι ℝ) :
    (ι → ℝ) →ₗ[ℝ] Module.Dual ℝ (Matrix ι ι ℝ) :=
  matrixTracePairing.comp (diagonalCommutator G)

theorem commutatorConstraints_eq_zero_iff (G : Matrix ι ι ℝ) (d : ι → ℝ) :
    commutatorConstraints G d = 0 ↔ diagonalCommutator G d = 0 := by
  change matrixTracePairing (diagonalCommutator G d) = 0 ↔ _
  rw [← map_zero matrixTracePairing]
  exact matrixTracePairing_injective.eq_iff

theorem commutatorConstraints_zero_of_diagonal (G W : Matrix ι ι ℝ)
    (h : ∀ i, (G * W) i i = (W * G) i i) (d : ι → ℝ) :
    commutatorConstraints G d W = 0 := by
  change ((diagonal d * G - G * diagonal d) * W).trace = 0
  rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.mul_assoc,
    Matrix.trace_mul_cycle G (diagonal d) W]
  simp only [Matrix.trace, Matrix.diag_apply, diagonal_mul, mul_diagonal]
  simp_rw [h]
  simp only [mul_comm, sub_self]

theorem finrank_subspace_le_row_zeros (P : Submodule ℝ (Matrix ι ι ℝ))
    (t : ι → ι) (h : ∀ W ∈ P, ∀ i, W i (t i) = 0) :
    Module.finrank ℝ P ≤ Fintype.card ι * (Fintype.card ι - 1) := by
  let f : P →ₗ[ℝ] (∀ i : ι, {j : ι // j ≠ t i} → ℝ) :=
    { toFun := fun W i j => W.val i j.val
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hf : Function.Injective f := by
    intro W Z hWZ
    apply Subtype.ext
    ext i j
    by_cases hj : j = t i
    · subst j
      rw [h W.val W.property, h Z.val Z.property]
    · exact congrArg (fun v => v i ⟨j, hj⟩) hWZ
  have hd := LinearMap.finrank_le_finrank_of_injective hf
  simpa [Module.finrank_pi, Module.finrank_pi_fintype, Fintype.card_subtype_compl,
    Nat.mul_comm] using hd

/-- An abstract span form of the principal-inverse bound. Its hypotheses
are the two linear identities that actual padded principal inverses satisfy. -/
theorem span_finrank_le_of_diagonal_commutation (G : Matrix ι ι ℝ)
    {R : Type*} (W : R → Matrix ι ι ℝ)
    (hdiag : ∀ r i, (G * W r) i i = (W r * G) i i)
    (hcomm : ∀ d, diagonalCommutator G d = 0 →
      ∀ r, diagonalCommutator (W r) d = 0) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range W)) ≤
      Fintype.card ι ^ 2 - Fintype.card ι + 1 := by
  let P := Submodule.span ℝ (Set.range W)
  by_cases hι : Nonempty ι
  · letI := hι
    let o : ι := Classical.choice hι
    by_cases hc : ∀ d : ι → ℝ, diagonalCommutator G d = 0 → ∀ i, d i = d o
    · let T := commutatorConstraints G
      have hP : P ≤ (LinearMap.range T).dualCoannihilator := by
        apply Submodule.span_le.mpr
        rintro _ ⟨r, rfl⟩
        change W r ∈ (LinearMap.range T).dualCoannihilator
        rw [Submodule.mem_dualCoannihilator]
        rintro _ ⟨d, rfl⟩
        exact commutatorConstraints_zero_of_diagonal G (W r) (hdiag r) d
      let ev : LinearMap.ker T →ₗ[ℝ] ℝ :=
        { toFun := fun d => d.val o
          map_add' := by intros; rfl
          map_smul' := by intros; rfl }
      have hev : Function.Injective ev := by
        intro d e hde
        apply Subtype.ext
        funext i
        have hd := hc d.val ((commutatorConstraints_eq_zero_iff G d.val).mp d.property) i
        have he := hc e.val ((commutatorConstraints_eq_zero_iff G e.val).mp e.property) i
        change d.val o = e.val o at hde
        exact hd.trans (hde.trans he.symm)
      have hker : Module.finrank ℝ (LinearMap.ker T) ≤ 1 := by
        simpa using LinearMap.finrank_le_finrank_of_injective hev
      have hnull := T.finrank_range_add_finrank_ker
      have hann := Subspace.finrank_add_finrank_dualCoannihilator_eq (LinearMap.range T)
      have hle := Submodule.finrank_mono hP
      have hm : 0 < Fintype.card ι := Fintype.card_pos
      simp only [Module.finrank_pi] at hnull
      simp only [Module.finrank_matrix, Module.finrank_self, Nat.mul_one] at hann
      change Module.finrank ℝ P ≤ Fintype.card ι ^ 2 - Fintype.card ι + 1
      rw [pow_two]
      have hsq : Fintype.card ι ≤ Fintype.card ι * Fintype.card ι := by nlinarith
      omega
    · push_neg at hc
      obtain ⟨d, hd, j, hj⟩ := hc
      let t : ι → ι := fun i => if d i = d o then j else o
      have ht (i : ι) : d i - d (t i) ≠ 0 := by
        dsimp [t]
        split_ifs with hi
        · rw [hi]
          exact sub_ne_zero.mpr hj.symm
        · exact sub_ne_zero.mpr hi
      have hz : ∀ A ∈ P, ∀ i, A i (t i) = 0 := by
        intro A hA
        refine Submodule.span_induction (fun B hB => ?_) ?_ ?_ ?_ hA
        · obtain ⟨r, rfl⟩ := hB
          intro i
          have he := congrArg (fun B : Matrix ι ι ℝ => B i (t i)) (hcomm d hd r)
          simp only [diagonalCommutator_apply, Matrix.zero_apply] at he
          exact (mul_eq_zero.mp he).resolve_left (ht i)
        · intro i
          rfl
        · intro B C _ _ hB hC i
          simp [hB i, hC i]
        · intro c B _ hB i
          simp [hB i]
      have hle := finrank_subspace_le_row_zeros P t hz
      have hm : 1 ≤ Fintype.card ι := Fintype.card_pos
      rw [Nat.mul_sub_left_distrib, Nat.mul_one] at hle
      simpa only [pow_two] using hle.trans (Nat.le_succ _)
  · haveI : IsEmpty ι := not_nonempty_iff.mp hι
    have hle := P.finrank_le
    have hz : Module.finrank ℝ (Matrix ι ι ℝ) = 0 := by
      simp [Module.finrank_matrix]
    rw [hz] at hle
    exact hle.trans (Nat.zero_le _)

def principalMatrix (G : Matrix ι ι ℝ) (S : Finset ι) : Matrix S S ℝ :=
  G.submatrix Subtype.val Subtype.val

def paddedPrincipalInverse (G : Matrix ι ι ℝ) (S : Finset ι) : Matrix ι ι ℝ :=
  fun i j => if hi : i ∈ S then
    if hj : j ∈ S then (principalMatrix G S)⁻¹ ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0

theorem sum_paddedPrincipalInverse_right (G : Matrix ι ι ℝ) (S : Finset ι)
    (f : ι → ℝ) (i : ι) (hi : i ∈ S) :
    (∑ j, f j * paddedPrincipalInverse G S j i) =
      ∑ j : S, f j.val * (principalMatrix G S)⁻¹ j ⟨i, hi⟩ := by
  calc
    _ = ∑ j ∈ S, f j * paddedPrincipalInverse G S j i := by
      apply (Finset.sum_subset S.subset_univ _).symm
      intro j _ hj
      simp [paddedPrincipalInverse, hj]
    _ = _ := by
      rw [Finset.sum_subtype (p := fun j => j ∈ S) (F := inferInstance) S (fun j => Iff.rfl)]
      simp [paddedPrincipalInverse, hi]

theorem sum_paddedPrincipalInverse_left (G : Matrix ι ι ℝ) (S : Finset ι)
    (f : ι → ℝ) (i : ι) (hi : i ∈ S) :
    (∑ j, paddedPrincipalInverse G S i j * f j) =
      ∑ j : S, (principalMatrix G S)⁻¹ ⟨i, hi⟩ j * f j.val := by
  calc
    _ = ∑ j ∈ S, paddedPrincipalInverse G S i j * f j := by
      apply (Finset.sum_subset S.subset_univ _).symm
      intro j _ hj
      simp [paddedPrincipalInverse, hi, hj]
    _ = _ := by
      rw [Finset.sum_subtype (p := fun j => j ∈ S) (F := inferInstance) S (fun j => Iff.rfl)]
      simp [paddedPrincipalInverse, hi]

theorem diagonal_mul_paddedPrincipalInverse (G : Matrix ι ι ℝ) (S : Finset ι)
    (hS : IsUnit (principalMatrix G S).det) (i : ι) :
    (G * paddedPrincipalInverse G S) i i = if i ∈ S then 1 else 0 := by
  by_cases hi : i ∈ S
  · rw [Matrix.mul_apply, sum_paddedPrincipalInverse_right G S (G i) i hi, if_pos hi]
    have he := congrArg (fun M : Matrix S S ℝ => M ⟨i, hi⟩ ⟨i, hi⟩)
      ((principalMatrix G S).mul_nonsing_inv hS)
    simpa [Matrix.mul_apply, principalMatrix] using he
  · simp [Matrix.mul_apply, paddedPrincipalInverse, hi]

theorem diagonal_paddedPrincipalInverse_mul (G : Matrix ι ι ℝ) (S : Finset ι)
    (hS : IsUnit (principalMatrix G S).det) (i : ι) :
    (paddedPrincipalInverse G S * G) i i = if i ∈ S then 1 else 0 := by
  by_cases hi : i ∈ S
  · rw [Matrix.mul_apply, sum_paddedPrincipalInverse_left G S (fun j => G j i) i hi,
      if_pos hi]
    have he := congrArg (fun M : Matrix S S ℝ => M ⟨i, hi⟩ ⟨i, hi⟩)
      ((principalMatrix G S).nonsing_inv_mul hS)
    simpa [Matrix.mul_apply, principalMatrix] using he
  · simp [Matrix.mul_apply, paddedPrincipalInverse, hi]

theorem trace_mul_paddedPrincipalInverse (G : Matrix ι ι ℝ) (S : Finset ι)
    (hS : IsUnit (principalMatrix G S).det) :
    (G * paddedPrincipalInverse G S).trace = (S.card : ℝ) := by
  simp [Matrix.trace, Matrix.diag_apply, diagonal_mul_paddedPrincipalInverse G S hS]

theorem diagonalCommutator_paddedPrincipalInverse (G : Matrix ι ι ℝ) (S : Finset ι)
    (hS : IsUnit (principalMatrix G S).det) (d : ι → ℝ)
    (hd : diagonalCommutator G d = 0) :
    diagonalCommutator (paddedPrincipalInverse G S) d = 0 := by
  let A := principalMatrix G S
  let D : Matrix S S ℝ := diagonal (fun i : S => d i.val)
  have hDA : D * A = A * D := by
    ext i j
    have he := congrArg (fun M : Matrix ι ι ℝ => M i.val j.val) hd
    simp only [diagonalCommutator_apply, Matrix.zero_apply] at he
    simp only [D, A, diagonal_mul, mul_diagonal, principalMatrix, Matrix.submatrix_apply]
    nlinarith
  have hDI : D * A⁻¹ = A⁻¹ * D := by
    calc
      D * A⁻¹ = 1 * (D * A⁻¹) := (Matrix.one_mul _).symm
      _ = (A⁻¹ * A) * (D * A⁻¹) := by rw [Matrix.nonsing_inv_mul A hS]
      _ = A⁻¹ * ((A * D) * A⁻¹) := by simp only [Matrix.mul_assoc]
      _ = A⁻¹ * ((D * A) * A⁻¹) := by rw [← hDA]
      _ = A⁻¹ * D := by rw [Matrix.mul_assoc D A A⁻¹, Matrix.mul_nonsing_inv A hS,
        Matrix.mul_one]
  ext i j
  rw [diagonalCommutator_apply]
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · have he := congrArg (fun M : Matrix S S ℝ => M ⟨i, hi⟩ ⟨j, hj⟩) hDI
      simp only [D, diagonal_mul, mul_diagonal] at he
      simp only [paddedPrincipalInverse, dif_pos hi, dif_pos hj, Matrix.zero_apply]
      change (d i - d j) * A⁻¹ ⟨i, hi⟩ ⟨j, hj⟩ = 0
      nlinarith
    · simp [paddedPrincipalInverse, hj]
  · simp [paddedPrincipalInverse, hi]

/-- Lemma 4, for arbitrary families of invertible principal submatrices. -/
theorem paddedPrincipalInverse_span_finrank (G : Matrix ι ι ℝ)
    {R : Type*} (S : R → Finset ι) (hS : ∀ r, IsUnit (principalMatrix G (S r)).det) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range (fun r => paddedPrincipalInverse G (S r)))) ≤
      Fintype.card ι ^ 2 - Fintype.card ι + 1 := by
  apply span_finrank_le_of_diagonal_commutation G
  · intro r i
    rw [diagonal_mul_paddedPrincipalInverse G (S r) (hS r),
      diagonal_paddedPrincipalInverse_mul G (S r) (hS r)]
  · intro d hd r
    exact diagonalCommutator_paddedPrincipalInverse G (S r) (hS r) d hd

end Bier
