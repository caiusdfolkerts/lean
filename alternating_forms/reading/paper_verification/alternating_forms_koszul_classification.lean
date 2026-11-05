module

public import PaperVerification.AlternatingFormsSmallExteriorKoszul
public import PaperVerification.AlternatingFormsDimensionFiveKoszul
public import PaperVerification.AlternatingFormsNonKoszul
public import PaperVerification.AlternatingFormsQuadraticDualPrincipal
public import PaperVerification.AlternatingFormsIntrinsicKoszul

/-!
# Proposition 5.3: the unrestricted-dimensional generic Koszul classification

The positive branch, the exceptional dimension-five obstruction, and the
higher-dimensional actual quadratic-dual obstruction are assembled on
nonempty principal opens of the entire original coefficient space. Every
natural dimension is covered. The independent dual/enveloping/PBW clause
is `paper_proposition_5_3_dual_clause`, with its full original grading.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms

variable (K : Type) [Field K] [CharZero K] [IsAlgClosed K]

/-- The complete generic iff, with no dimension cutoff, normal-form premise,
additional homology assumption, or replacement of ordinary Tor by a model. -/
theorem paper_proposition_5_3_certificate_classification (n : ℕ) :
    ∃ (ι : Type) (fin : Fintype ι),
      letI := fin
      ∃ b₂ : Module.Basis ι K (⋀[K]^2 (Fin n → K)),
        ∃ Q : MvPolynomial (ι ⊕ ι) K,Q≠0 ∧
          (∃ y : (ι ⊕ ι) → K,MvPolynomial.eval y Q≠0) ∧
          ∀ y : (ι ⊕ ι) → K,MvPolynomial.eval y Q≠0 →
            (Nonempty (ExteriorKoszul.HomogeneousKoszulCertificate
              (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2) ↔ n≤4) := by
  by_cases hn : n≤4
  · obtain ⟨m,b₂,Q,hQ,hpoint,h⟩ :=
      SmallExteriorKoszul.paper_proposition_5_3_koszul_small
        (K := K) (M := Fin n → K) (by simpa using hn)
    exact ⟨Fin m,inferInstance,b₂,Q,hQ,hpoint,fun y hy =>
      ⟨fun _ => hn,fun _ => h y hy⟩⟩
  · by_cases h5 : n=5
    · subst n
      obtain ⟨b₂,Q,hQ,hpoint,h⟩ :=
        DimensionFiveKoszul.paper_proposition_5_3_dimension_five_not_koszul
          (K := K) (M := Fin 5 → K) (by simp)
      refine ⟨OddOrbitSlot 1,inferInstance,b₂,Q,hQ,hpoint,?_⟩
      intro y hy
      constructor
      · intro hC
        exact (h y hy hC).elim
      · intro hdim
        omega
    · have h6 : 6≤n := by omega
      obtain ⟨ι,fin,h⟩ := paper_proposition_5_3_non_koszul_large K n h6
      letI := fin
      obtain ⟨b₂,Q,hQ,hpoint,h⟩ := h
      refine ⟨ι,fin,b₂,Q,hQ,hpoint,?_⟩
      intro y hy
      constructor
      · intro hC
        exact (h y hy hC).elim
      · intro hdim
        exact (hn hdim).elim

/-- Proposition 5.3 with ordinary graded Koszulness independent of every
compatible homogeneous basis. The certificate formulation above is proved
equivalent using actual ordinary Tor, degree orthogonality, and the intrinsic
quadratic dual; no choice of basis or homology comparison is assumed. -/
theorem paper_proposition_5_3_koszul_classification (n : ℕ) :
    ∃ (ι : Type) (fin : Fintype ι),
      letI := fin
      ∃ b₂ : Module.Basis ι K (⋀[K]^2 (Fin n → K)),
        ∃ Q : MvPolynomial (ι ⊕ ι) K,Q≠0 ∧
          (∃ y : (ι ⊕ ι) → K,MvPolynomial.eval y Q≠0) ∧
          ∀ y : (ι ⊕ ι) → K,MvPolynomial.eval y Q≠0 →
            (ExteriorKoszul.IsKoszul
              (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 ↔ n≤4) := by
  obtain ⟨ι,fin,h⟩ := paper_proposition_5_3_certificate_classification K n
  letI := fin
  obtain ⟨b₂,Q,hQ,hpoint,h⟩ := h
  refine ⟨ι,fin,b₂,Q,hQ,hpoint,?_⟩
  intro y hy
  exact (ExteriorKoszul.isKoszul_iff_nonempty_certificate _ _).trans (h y hy)

end PaperVerification.AlternatingForms
