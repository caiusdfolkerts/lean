module

public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Tactic.Abel

/-!
# Descent of a prescribed basis from all closed-point fibers

Section 6.3 uses the following principle: a prescribed finite family in a finite
module over a reduced Jacobson ring is a basis if its images are a basis in
every maximal-ideal residue-field fiber. This file proves that statement for
the literal tensor-product fibers. Finiteness is assumed only for the module,
not for the kernel of a presentation. The proof establishes spanning through
maximal submodules and injectivity coordinate by coordinate.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion

open scoped BigOperators TensorProduct

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A proper submodule of a finite module remains proper in at least one
maximal-ideal fiber. This is the global spanning form of Nakayama's lemma. -/
theorem submodule_eq_top_of_maximal_fibers [Module.Finite R M] (S : Submodule R M)
    (hS : ∀ I : Ideal R, I.IsMaximal → S ⊔ I • (⊤ : Submodule R M) = ⊤) : S = ⊤ := by
  by_contra hproper
  obtain ⟨N, hN, hSN⟩ := (eq_top_or_exists_le_coatom S).resolve_left hproper
  letI : IsSimpleModule R (M ⧸ N) := isSimpleModule_iff_isCoatom.mpr hN
  let I := Module.annihilator R (M ⧸ N)
  have hI : I.IsMaximal := IsSimpleModule.annihilator_isMaximal
  have hIN : I • (⊤ : Submodule R M) ≤ N := by
    apply Submodule.smul_le.mpr
    intro r hr m _
    apply (Submodule.Quotient.mk_eq_zero N).mp
    have hz := Module.mem_annihilator.mp hr (N.mkQ m)
    simpa only [Submodule.Quotient.mk_smul, Submodule.mkQ_apply] using hz
  have htop : (⊤ : Submodule R M) ≤ N := by
    rw [← hS I hI]
    exact sup_le hSN hIN
  exact hN.1 (top_unique htop)

/-- Vanishing of the literal residue-field tensor of a vector is equivalent to
membership in the maximal-ideal multiple of the original module. -/
theorem residue_tensor_one_eq_zero_iff (I : Ideal R) (m : M) :
    ((1 : R ⧸ I) ⊗ₜ[R] m) = 0 ↔ m ∈ I • (⊤ : Submodule R M) := by
  let e := TensorProduct.quotTensorEquivQuotSMul M I
  constructor
  · intro h
    apply (Submodule.Quotient.mk_eq_zero _).mp
    have h' := congrArg e h
    simpa only [e, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero] using h'
  · intro h
    apply e.injective
    simpa only [e, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero] using
      (Submodule.Quotient.mk_eq_zero _).mpr h

variable {ι : Type*} [Fintype ι]

/-- The prescribed family in a residue-field fiber. -/
def residueFamily (I : Ideal R) (v : ι → M) : ι → (R ⧸ I) ⊗[R] M :=
  fun i ↦ (1 : R ⧸ I) ⊗ₜ[R] v i

theorem residue_tensor_linearCombination (I : Ideal R) (v : ι → M) (c : ι → R) :
    ((1 : R ⧸ I) ⊗ₜ[R] (∑ i, c i • v i)) =
      ∑ i, Ideal.Quotient.mk I (c i) • residueFamily I v i := by
  rw [TensorProduct.tmul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [residueFamily, TensorProduct.smul_tmul']
  have hcast : c i • (1 : R ⧸ I) = Ideal.Quotient.mk I (c i) := by
    rw [Algebra.smul_def, mul_one]
    rfl
  simpa only [smul_eq_mul, mul_one, hcast] using
    (TensorProduct.smul_tmul (c i) (1 : R ⧸ I) (v i)).symm

/-- A basis in one residue fiber gives exactly the expected criterion for relations
whose coefficients lie in the corresponding maximal ideal. -/
theorem residue_basis_relation (I : Ideal R) (v : ι → M)
    (b : Module.Basis ι (R ⧸ I) ((R ⧸ I) ⊗[R] M))
    (hb : ∀ i, b i = residueFamily I v i) (c : ι → R)
    (hc : (∑ i, c i • v i) ∈ I • (⊤ : Submodule R M)) :
    ∀ i, c i ∈ I := by
  have hz := (residue_tensor_one_eq_zero_iff I (∑ i, c i • v i)).mpr hc
  rw [residue_tensor_linearCombination] at hz
  have hzero : (∑ i, Ideal.Quotient.mk I (c i) • b i) = 0 := by
    simpa only [hb] using hz
  have hcoeff := (Fintype.linearIndependent_iff.mp b.linearIndependent)
    (fun i ↦ Ideal.Quotient.mk I (c i)) hzero
  intro i
  exact Ideal.Quotient.eq_zero_iff_mem.mp (hcoeff i)

/-- Lifting the coefficients of a fiber basis proves spanning modulo the ideal. -/
theorem residue_basis_spanning (I : Ideal R) (v : ι → M)
    (b : Module.Basis ι (R ⧸ I) ((R ⧸ I) ⊗[R] M))
    (hb : ∀ i, b i = residueFamily I v i) :
    Submodule.span R (Set.range v) ⊔ I • (⊤ : Submodule R M) = ⊤ := by
  classical
  apply top_unique
  intro m _
  let d : ι → R ⧸ I := fun i ↦ b.repr ((1 : R ⧸ I) ⊗ₜ[R] m) i
  choose c hc using fun i : ι ↦ Ideal.Quotient.mk_surjective (d i)
  have hcomb : ((1 : R ⧸ I) ⊗ₜ[R] (∑ i, c i • v i)) =
      ((1 : R ⧸ I) ⊗ₜ[R] m) := by
    rw [residue_tensor_linearCombination]
    simpa only [hc, d, hb] using b.sum_repr ((1 : R ⧸ I) ⊗ₜ[R] m)
  have hrem : m - ∑ i, c i • v i ∈ I • (⊤ : Submodule R M) := by
    apply (residue_tensor_one_eq_zero_iff I _).mp
    rw [TensorProduct.tmul_sub, hcomb, sub_self]
  have hspan : (∑ i, c i • v i) ∈ Submodule.span R (Set.range v) := by
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact Submodule.mem_sup.mpr ⟨_, hspan, _, hrem, by abel⟩

/-- The exact fiber-basis hypothesis, including its scalar field and specified vectors. -/
def HasResidueBases (v : ι → M) : Prop :=
  ∀ I : Ideal R, I.IsMaximal →
    ∃ b : Module.Basis ι (R ⧸ I) ((R ⧸ I) ⊗[R] M),
      ∀ i, b i = residueFamily I v i

theorem span_eq_top_of_residue_bases [Module.Finite R M] (v : ι → M)
    (h : HasResidueBases (R := R) v) : Submodule.span R (Set.range v) = ⊤ := by
  apply submodule_eq_top_of_maximal_fibers
  intro I hI
  obtain ⟨b, hb⟩ := h I hI
  exact residue_basis_spanning I v b hb

/-- Over a reduced Jacobson ring, fiberwise independence forces global independence.
The proof needs no finite-generation assumption on the module or on a presentation kernel. -/
theorem linearIndependent_of_residue_bases [IsReduced R] [IsJacobsonRing R]
    (v : ι → M) (h : HasResidueBases (R := R) v) : LinearIndependent R v := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hmem : c i ∈ (⊥ : Ideal R).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro I ⟨_, hI⟩
    obtain ⟨b, hb⟩ := h I hI
    apply residue_basis_relation I v b hb c _ i
    rw [hc]
    exact Submodule.zero_mem _
  have hrad : (⊥ : Ideal R).jacobson = ⊥ :=
    IsJacobsonRing.out (inferInstance : IsJacobsonRing R) Ideal.isRadical_bot
  rw [hrad] at hmem
  exact hmem

/-- The prescribed family is a global basis if it is a basis on every closed-point
fiber of a finite module over a reduced Jacobson ring. -/
def basisOfResidueBases [IsReduced R] [IsJacobsonRing R] [Module.Finite R M]
    (v : ι → M) (h : HasResidueBases (R := R) v) : Module.Basis ι R M :=
  Module.Basis.mk (linearIndependent_of_residue_bases v h)
    (by rw [span_eq_top_of_residue_bases v h])

@[simp]
theorem basisOfResidueBases_apply [IsReduced R] [IsJacobsonRing R] [Module.Finite R M]
    (v : ι → M) (h : HasResidueBases (R := R) v) (i : ι) : basisOfResidueBases v h i = v i := by
  simp [basisOfResidueBases]

end PaperVerification.Fermion
