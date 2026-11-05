module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Genuine direct-sum decompositions from a homogeneous basis

Partitioning a basis by its degree gives independent submodules whose supremum
is the entire module. This gives the natural grading on the graded tensor
products used in the cluster factorization.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion

variable {R M ι Γ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [DecidableEq Γ]

def basisDegreePart (b : Module.Basis ι R M) (degree : ι → Γ) (n : Γ) :
    Submodule R M :=
  Submodule.span R (b '' {i | degree i=n})

theorem basisDegreePart_iSup_eq_top (b : Module.Basis ι R M) (degree : ι → Γ) :
    (⨆ n,basisDegreePart b degree n)=⊤ := by
  apply top_unique
  rw [←b.span_eq]
  apply Submodule.span_le.mpr
  rintro x ⟨i,rfl⟩
  apply (le_iSup (basisDegreePart b degree) (degree i))
  exact Submodule.subset_span ⟨i,rfl,rfl⟩

theorem basisDegreePart_independent (b : Module.Basis ι R M) (degree : ι → Γ) :
    iSupIndep (basisDegreePart b degree) := by
  rw [iSupIndep_def]
  intro n
  have hdis : Disjoint
      (Submodule.span R (b '' {i | degree i=n}))
      (Submodule.span R (b '' {i | degree i≠n})) :=
    b.linearIndependent.disjoint_span_image
      (Set.disjoint_left.mpr fun i hi hni ↦ hni hi)
  apply Disjoint.mono_right ?_ hdis
  refine iSup_le fun m ↦ iSup_le fun hmn ↦ Submodule.span_mono ?_
  rintro x ⟨i,hi,rfl⟩
  exact ⟨i,fun hn ↦ hmn (hi.symm.trans hn),rfl⟩

def basisDegreeDecomposition (b : Module.Basis ι R M) (degree : ι → Γ) :
    DirectSum.Decomposition (basisDegreePart b degree) :=
  (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (basisDegreePart_independent b degree) (basisDegreePart_iSup_eq_top b degree)).chooseDecomposition

section Algebra

variable {A : Type*} [Ring A] [Algebra R A] [AddMonoid Γ]

/-- Checking degrees of products of basis vectors suffices for a genuine
graded-algebra structure. The underlying subspaces are fixed spans of the
specified basis vectors, and their directness was proved independently. -/
def basisDegreeGradedAlgebra (b : Module.Basis ι R A) (degree : ι → Γ)
    (hone : (1 : A)∈basisDegreePart b degree 0)
    (hmul : ∀ i j,b i*b j∈basisDegreePart b degree (degree i+degree j)) :
    GradedAlgebra (basisDegreePart b degree) where
  toDecomposition := basisDegreeDecomposition b degree
  one_mem := hone
  mul_mem := by
    intro m n x y hx hy
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i,hi,rfl⟩ := hx
        change degree i=m at hi
        induction hy using Submodule.span_induction with
        | mem y hy =>
            obtain ⟨j,hj,rfl⟩ := hy
            change degree j=n at hj
            simpa only [hi,hj] using hmul i j
        | zero =>
            simpa only [mul_zero] using (basisDegreePart b degree (m+n)).zero_mem
        | add y z hy hz ihy ihz =>
            rw [mul_add]
            exact (basisDegreePart b degree (m+n)).add_mem ihy ihz
        | smul r y hy ih =>
            rw [Algebra.mul_smul_comm]
            exact (basisDegreePart b degree (m+n)).smul_mem r ih
    | zero =>
        simpa only [zero_mul] using (basisDegreePart b degree (m+n)).zero_mem
    | add x z hx hz ihx ihz =>
        rw [add_mul]
        exact (basisDegreePart b degree (m+n)).add_mem ihx ihz
    | smul r x hx ih =>
        rw [Algebra.smul_mul_assoc]
        exact (basisDegreePart b degree (m+n)).smul_mem r ih

/-- A homogeneous basis recovers each pre-existing homogeneous component
exactly, including components of arbitrary dimension. -/
theorem basisDegreePart_eq_existing (part : Γ → Submodule R A)
    [GradedAlgebra part] (b : Module.Basis ι R A) (degree : ι → Γ)
    (hb : ∀ i,b i∈part (degree i)) :
    basisDegreePart b degree=part := by
  apply (iSupIndep.le_iff_eq_of_iSup_eq_top
    (DirectSum.Decomposition.isInternal part).submodule_iSupIndep
    (basisDegreePart_iSup_eq_top b degree)).mp
  intro n
  apply Submodule.span_le.mpr
  rintro x ⟨i,hi,rfl⟩
  change degree i=n at hi
  change b i∈part n
  rw [←hi]
  exact hb i

end Algebra
end PaperVerification.Fermion
