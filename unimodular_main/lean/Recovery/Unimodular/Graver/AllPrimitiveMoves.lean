module

public import Recovery.Unimodular.Graver.NonnegativeBound
public import Mathlib.Data.Int.Interval

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators Matrix

namespace Unimodular.EffectiveGraver

variable {n m : ℕ}

/-- An executable coordinate sign change. -/
def flip (s : Fin n → Bool) (g : Lattice n) : Lattice n :=
  fun j => if s j then g j else -g j

/-- The same sign change on matrix columns. -/
def signedMatrix (A : Matrix (Fin m) (Fin n) ℤ) (s : Fin n → Bool) :
    Matrix (Fin m) (Fin n) ℤ := fun i j => if s j then A i j else -A i j

/-- A single computable bound covering every orthant of the full integer kernel. -/
def fullBound (A : Matrix (Fin m) (Fin n) ℤ) : ℕ :=
  ∑ s : Fin n → Bool, KernelSlice.bound (signedMatrix A s)

/-- The exact finite integer coordinate box. -/
def box (B : ℕ) : Finset (Lattice n) :=
  Fintype.piFinset (fun _ => Finset.Icc (-(B : ℤ)) (B : ℤ))

instance (h g : Lattice n) : Decidable (Graver.ConformalLE h g) :=
  inferInstanceAs (Decidable (∀ i, (h i).toNat ≤ (g i).toNat ∧
    (-h i).toNat ≤ (-g i).toNat))

/-- Exact primitivehood test inside the proven complete box. -/
def primitiveTest (A : Matrix (Fin m) (Fin n) ℤ) (B : ℕ) (g : Lattice n) : Prop :=
  A *ᵥ g = 0 ∧ g ≠ 0 ∧
    ∀ h ∈ box B, A *ᵥ h = 0 → h ≠ 0 → Graver.ConformalLE h g → h = g

instance (A : Matrix (Fin m) (Fin n) ℤ) (B : ℕ) (g : Lattice n) :
    Decidable (primitiveTest A B g) := by unfold primitiveTest; infer_instance

/-- The complete Graver basis, computed from an arbitrary integer matrix. -/
def allPrimitiveMoves (A : Matrix (Fin m) (Fin n) ℤ) : Finset (Lattice n) :=
  (box (fullBound A)).filter (primitiveTest A (fullBound A))

@[simp] theorem flip_flip (s : Fin n → Bool) (g : Lattice n) : flip s (flip s g) = g := by
  ext j
  cases h : s j <;> simp [flip, h]

@[simp] theorem flip_zero (s : Fin n → Bool) : flip s (0 : Lattice n) = 0 := by
  ext j
  cases h : s j <;> simp [flip, h]

theorem flip_injective (s : Fin n → Bool) : Function.Injective (flip s) := by
  intro x y h
  have he := congrArg (flip s) h
  simpa only [flip_flip] using he

theorem signedMatrix_mulVec (A : Matrix (Fin m) (Fin n) ℤ) (s : Fin n → Bool)
    (g : Lattice n) : signedMatrix A s *ᵥ g = A *ᵥ flip s g := by
  ext i
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j hj
  cases h : s j <;> simp [signedMatrix, flip, h]

@[simp] theorem signedMatrix_flip (A : Matrix (Fin m) (Fin n) ℤ) (s : Fin n → Bool)
    (g : Lattice n) : signedMatrix A s *ᵥ flip s g = A *ᵥ g := by
  rw [signedMatrix_mulVec, flip_flip]

theorem conformal_flip_iff (s : Fin n → Bool) (h g : Lattice n) :
    Graver.ConformalLE (flip s h) (flip s g) ↔ Graver.ConformalLE h g := by
  rw [Graver.conformalLE_iff, Graver.conformalLE_iff]
  apply forall_congr'
  intro j
  cases hs : s j <;> simp [flip, hs] <;> omega

theorem primitive_flip (A : Matrix (Fin m) (Fin n) ℤ) (s : Fin n → Bool)
    {g : Lattice n} (hg : Graver.Primitive (matrixHom A).ker g) :
    Graver.Primitive (matrixHom (signedMatrix A s)).ker (flip s g) := by
  refine ⟨?_, ?_, ?_⟩
  · change signedMatrix A s *ᵥ flip s g = 0
    rw [signedMatrix_flip]
    exact hg.1
  · intro he
    apply hg.2.1
    exact flip_injective s (he.trans (flip_zero s).symm)
  · intro h hh hn hconf
    have hhA : flip s h ∈ (matrixHom A).ker := by
      change A *ᵥ flip s h = 0
      rw [← signedMatrix_mulVec]
      exact hh
    have hn' : flip s h ≠ 0 := by
      intro he
      exact hn (flip_injective s (he.trans (flip_zero s).symm))
    have hc : Graver.ConformalLE (flip s h) g := by
      have hc' := (conformal_flip_iff s h (flip s g)).2 hconf
      simpa only [flip_flip] using hc'
    have he := hg.2.2 (flip s h) hhA hn' hc
    apply flip_injective s
    simpa only [flip_flip] using he

theorem primitive_coordinate_bound (A : Matrix (Fin m) (Fin n) ℤ)
    {g : Lattice n} (hg : Graver.Primitive (matrixHom A).ker g) :
    ∀ j, |g j| ≤ (fullBound A : ℤ) := by
  let s : Fin n → Bool := fun j => decide (0 ≤ g j)
  have he (j : Fin n) : flip s g j = |g j| := by
    by_cases h : 0 ≤ g j
    · simp [flip, s, h, abs_of_nonneg h]
    · simp [flip, s, h, abs_of_neg (lt_of_not_ge h)]
  have hn : ∀ j, 0 ≤ flip s g j := fun j => by rw [he]; exact abs_nonneg _
  have hs := nonnegative_primitive_bound (signedMatrix A s) (primitive_flip A s hg) hn
  have hb : KernelSlice.bound (signedMatrix A s) ≤ fullBound A := by
    unfold fullBound
    exact Finset.single_le_sum
      (fun t ht => Nat.zero_le (KernelSlice.bound (signedMatrix A t))) (Finset.mem_univ s)
  intro j
  have hj : flip s g j ≤ ∑ k, flip s g k :=
    Finset.single_le_sum (fun k hk => hn k) (Finset.mem_univ j)
  rw [he] at hj
  exact hj.trans (hs.trans (by exact_mod_cast hb))

@[simp] theorem mem_box (B : ℕ) (g : Lattice n) :
    g ∈ box B ↔ ∀ j, -(B : ℤ) ≤ g j ∧ g j ≤ (B : ℤ) := by
  simp only [box, Fintype.mem_piFinset, Finset.mem_Icc]

theorem conformal_mem_box {B : ℕ} {h g : Lattice n} (hg : g ∈ box B)
    (hhg : Graver.ConformalLE h g) : h ∈ box B := by
  rw [mem_box] at hg ⊢
  intro j
  have hgj := hg j
  have hhj := (Graver.conformalLE_iff h g).1 hhg j
  omega

theorem primitiveTest_iff (A : Matrix (Fin m) (Fin n) ℤ) {B : ℕ} {g : Lattice n}
    (hg : g ∈ box B) : primitiveTest A B g ↔ Graver.Primitive (matrixHom A).ker g := by
  constructor
  · rintro ⟨hA, hn, hmin⟩
    refine ⟨hA, hn, ?_⟩
    intro h hh hn' hhg
    exact hmin h (conformal_mem_box hg hhg) hh hn' hhg
  · rintro ⟨hA, hn, hmin⟩
    exact ⟨hA, hn, fun h _ hh hn' hhg => hmin h hh hn' hhg⟩

/-- Every primitive kernel vector and no others are returned by the total
algorithm, including elements never usable between binary solutions. -/
@[simp] theorem mem_allPrimitiveMoves (A : Matrix (Fin m) (Fin n) ℤ) (g : Lattice n) :
    g ∈ allPrimitiveMoves A ↔ Graver.Primitive (matrixHom A).ker g := by
  rw [allPrimitiveMoves, Finset.mem_filter]
  constructor
  · rintro ⟨hb, ht⟩
    exact (primitiveTest_iff A hb).1 ht
  · intro hg
    have hb : g ∈ box (fullBound A) := by
      rw [mem_box]
      intro j
      exact abs_le.1 (primitive_coordinate_bound A hg j)
    exact ⟨hb, (primitiveTest_iff A hb).2 hg⟩

/-- All nonnegative integer fibers are connected by the computed full basis;
every intermediate vector remains in the original endpoint coordinate box. -/
theorem all_fiber_connectivity (A : Matrix (Fin m) (Fin n) ℤ)
    (c d : Lattice n) (hcd : A *ᵥ c = A *ᵥ d)
    (hc : ∀ i, 0 ≤ c i) (hd : ∀ i, 0 ≤ d i) :
    Relation.ReflTransGen (fun x y => y - x ∈ allPrimitiveMoves A ∧
      A *ᵥ x = A *ᵥ c ∧ A *ᵥ y = A *ᵥ c ∧
      Graver.Between c d x ∧ Graver.Between c d y ∧
      (∀ i, 0 ≤ x i) ∧ (∀ i, 0 ≤ y i)) c d := by
  obtain ⟨G, hG, hpath⟩ :=
    Graver.finite_nonnegative_fiber_connectivity (matrixHom A) c d hcd hc hd
  apply Relation.ReflTransGen.mono (fun x y hxy => ?_) _ _ hpath
  exact ⟨(mem_allPrimitiveMoves A _).2 ((hG _).1 hxy.1), hxy.2⟩

end Unimodular.EffectiveGraver

#print axioms Unimodular.EffectiveGraver.allPrimitiveMoves
#print axioms Unimodular.EffectiveGraver.primitive_coordinate_bound
#print axioms Unimodular.EffectiveGraver.mem_allPrimitiveMoves
#print axioms Unimodular.EffectiveGraver.all_fiber_connectivity
#check Unimodular.EffectiveGraver.all_fiber_connectivity
