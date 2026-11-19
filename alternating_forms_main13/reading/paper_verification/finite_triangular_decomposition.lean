module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic

/-!
# A finite direct-sum decomposition detected by triangular tests

This elementary lemma packages the linear algebra in the projective-bundle
formula. The summands may have different types and need not be finite
dimensional. A triangular family of tests proves that their sum is direct.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.FiniteTriangularDecomposition

variable {K ι V : Type*} [Field K] [Fintype ι] [LinearOrder ι]
    [AddCommGroup V] [Module K V]
    {A : ι → Type*} [∀ i, AddCommGroup (A i)] [∀ i, Module K (A i)]

/-- Add the images of a finite family of genuine module homomorphisms. -/
def sumMap (f : ∀ i, A i →ₗ[K] V) : (∀ i, A i) →ₗ[K] V :=
  ∑ i, (f i).comp (LinearMap.proj i)

@[simp] theorem sumMap_apply (f : ∀ i, A i →ₗ[K] V) (x : ∀ i, A i) :
    sumMap f x = ∑ i, f i (x i) := by
  simp [sumMap]

@[simp] theorem sumMap_single (f : ∀ i, A i →ₗ[K] V) (i : ι) (x : A i) :
    sumMap f (Pi.single i x) = f i x := by
  classical
  rw [sumMap_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

/-- A triangular family of coefficient tests makes the sum map injective. -/
theorem sumMap_injective (f : ∀ i, A i →ₗ[K] V) (g : ∀ i, V →ₗ[K] A i)
    (c : ι → K) (hc : ∀ i, c i ≠ 0)
    (hdiag : ∀ i x, g i (f i x) = c i • x)
    (hlower : ∀ i j, j < i → ∀ x, g i (f j x) = 0) :
    Function.Injective (sumMap f) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  by_contra hne
  have hs : (Finset.univ.filter fun i => x i ≠ 0).Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    exact ⟨i, by simpa using hi⟩
  let S := Finset.univ.filter fun i => x i ≠ 0
  let i := S.max' hs
  have hi : x i ≠ 0 := (Finset.mem_filter.mp (Finset.max'_mem S hs)).2
  have he : g i (sumMap f x) = c i • x i := by
    rw [sumMap_apply, map_sum, Finset.sum_eq_single i]
    · exact hdiag i (x i)
    · intro j _ hji
      rcases lt_or_gt_of_ne hji with hlt | hgt
      · exact hlower i j hlt (x j)
      · have hj : x j = 0 := by
          by_contra hj
          have hjS : j ∈ S := by simp [S, hj]
          exact (not_lt_of_ge (Finset.le_max' S j hjS)) hgt
        simp [hj]
    · simp
  rw [hx, map_zero] at he
  exact hi ((smul_eq_zero.mp he.symm).resolve_left (hc i))

/-- Generation of the target by the images makes the sum map surjective. -/
theorem sumMap_surjective (f : ∀ i, A i →ₗ[K] V)
    (hspan : ∀ v : V, v ∈ Submodule.span K (⋃ i, Set.range (f i))) :
    Function.Surjective (sumMap f) := by
  classical
  intro v
  have hle : Submodule.span K (⋃ i, Set.range (f i)) ≤ LinearMap.range (sumMap f) := by
    apply Submodule.span_le.mpr
    intro y hy
    obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.mp hy
    exact ⟨Pi.single i x, sumMap_single f i x⟩
  exact hle (hspan v)

/-- The actual direct-sum equivalence, with no finite-dimensional hypothesis. -/
def equivalence (f : ∀ i, A i →ₗ[K] V) (g : ∀ i, V →ₗ[K] A i)
    (c : ι → K) (hc : ∀ i, c i ≠ 0)
    (hdiag : ∀ i x, g i (f i x) = c i • x)
    (hlower : ∀ i j, j < i → ∀ x, g i (f j x) = 0)
    (hspan : ∀ v : V, v ∈ Submodule.span K (⋃ i, Set.range (f i))) :
    (∀ i, A i) ≃ₗ[K] V :=
  LinearEquiv.ofBijective (sumMap f)
    ⟨sumMap_injective f g c hc hdiag hlower, sumMap_surjective f hspan⟩

@[simp] theorem equivalence_apply (f : ∀ i, A i →ₗ[K] V) (g : ∀ i, V →ₗ[K] A i)
    (c : ι → K) (hc : ∀ i, c i ≠ 0)
    (hdiag : ∀ i x, g i (f i x) = c i • x)
    (hlower : ∀ i j, j < i → ∀ x, g i (f j x) = 0)
    (hspan : ∀ v : V, v ∈ Submodule.span K (⋃ i, Set.range (f i))) (x : ∀ i, A i) :
    equivalence f g c hc hdiag hlower hspan x = ∑ i, f i (x i) :=
  sumMap_apply f x

end PaperVerification.FiniteTriangularDecomposition
