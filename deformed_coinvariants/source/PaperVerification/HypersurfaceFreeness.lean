module

public import PaperVerification.JacobianIsolatedOrigin
public import PaperVerification.JacobianHamiltonian
public import PaperVerification.JacobianParameter
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Hypersurface freeness from the paper's hypotheses

This joins the analytic isolation hypothesis, the global regular-gradient
argument, the literal Hamiltonian relation space, and homogeneous basis lifting.
It states the freeness clause of Theorem 6.3. The full theorem additionally
requires the exceptional-defect and equivariant Hilbert-series assertions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Module

namespace PaperVerification.JacobianDivergence

/-- Homogeneous polynomial representatives span any Milnor quotient. This does
not require isolation or regularity: it follows from the monomial expansion. -/
theorem exists_homogeneous_milnor_basis {K ι : Type*} [Field K] [Fintype ι]
    (F : MvPolynomial ι K) (w : ι → ℕ) :
    ∃ (s : Set (MilnorQuotient F)) (b : s → MvPolynomial ι K)
      (B : Basis s K (MilnorQuotient F)),
      (∀ i, ∃ d : ℕ, (b i).IsWeightedHomogeneous w d) ∧
      ∀ i, (jacobianSubmodule F).mkQ (b i) = B i := by
  classical
  let S : Set (MilnorQuotient F) :=
    {x | ∃ p : MvPolynomial ι K, ∃ d : ℕ,
      p.IsWeightedHomogeneous w d ∧ (jacobianSubmodule F).mkQ p = x}
  have hspan : ⊤ ≤ Submodule.span K S := by
    intro x hx
    clear hx
    obtain ⟨p, rfl⟩ := (jacobianSubmodule F).mkQ_surjective x
    induction p using MvPolynomial.induction_on' with
    | monomial a c =>
      apply Submodule.subset_span
      exact ⟨_, Finsupp.weight w a,
        MvPolynomial.isWeightedHomogeneous_monomial w a c rfl, rfl⟩
    | add p q hp hq =>
      simpa only [map_add] using (Submodule.span K S).add_mem hp hq
  let B := Basis.ofSpan hspan
  have hB : ∀ i, ∃ p : MvPolynomial ι K, ∃ d : ℕ,
      p.IsWeightedHomogeneous w d ∧ (jacobianSubmodule F).mkQ p = B i := by
    intro i
    exact Basis.ofSpan_subset hspan ⟨i, rfl⟩
  choose b d hhom hrep using hB
  exact ⟨_, b, B, fun i => ⟨d i, hhom i⟩, hrep⟩

theorem hypersurface_homogeneous_basis_lifts {n : ℕ} {I : Type*}
    (hn : 2 ≤ n) (F : MvPolynomial (Fin n) ℂ) (w : Fin n → ℕ) (h : ℕ)
    (hne : F ≠ 0) (hw : ∀ i, 0 < w i) (hh : 0 < h)
    (hF : F.IsWeightedHomogeneous w h) (hiso : IsolatedCriticalPointAtOrigin F)
    (b : I → MvPolynomial (Fin n) ℂ)
    (hbhom : ∀ i, ∃ d : ℕ, (b i).IsWeightedHomogeneous w d)
    (B : Basis I ℂ (MilnorQuotient F))
    (hB : ∀ i, (jacobianSubmodule F).mkQ (b i) = B i) :
    divergenceSpace F = orderedHamiltonianSpace F ∧
    letI := potentialSubalgebraModule F w h hne hh hF
    ∃ basis : Basis I (Algebra.adjoin ℂ {F}) (BrieskornModule F),
      ∀ i, basis i = classOf F (b i) := by
  letI := potentialSubalgebraModule F w h hne hh hF
  have hreg := gradient_regular_of_isolated F w h hw hF hiso
  refine ⟨divergenceSpace_eq_paper_relations F hreg, ?_⟩
  obtain ⟨Bpol, hBpol⟩ := homogeneous_milnor_basis_lifts hn F w h hw hh hF hreg b hbhom B hB
  obtain ⟨Bsub, hBsub⟩ := basis_over_potentialSubalgebra F w h hne hh hF Bpol
  exact ⟨Bsub, fun i => (hBsub i).trans (hBpol i)⟩

/-- The freeness assertion has no hidden supplied-basis hypothesis. The basis
and its homogeneous polynomial representatives are constructed above. -/
theorem hypersurface_free
    {n : ℕ} (hn : 2 ≤ n) (F : MvPolynomial (Fin n) ℂ)
    (w : Fin n → ℕ) (h : ℕ) (hne : F ≠ 0)
    (hw : ∀ i, 0 < w i) (hh : 0 < h)
    (hF : F.IsWeightedHomogeneous w h) (hiso : IsolatedCriticalPointAtOrigin F) :
    letI := potentialSubalgebraModule F w h hne hh hF
    Module.Free (Algebra.adjoin ℂ {F}) (BrieskornModule F) := by
  letI := potentialSubalgebraModule F w h hne hh hF
  obtain ⟨s, b, B, hhom, hrep⟩ := exists_homogeneous_milnor_basis F w
  obtain ⟨_, Bsub, _⟩ :=
    hypersurface_homogeneous_basis_lifts hn F w h hne hw hh hF hiso b hhom B hrep
  exact Module.Free.of_basis Bsub

end PaperVerification.JacobianDivergence
