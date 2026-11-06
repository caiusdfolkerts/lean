module

public import wishart.verified

/- Generated ordinary proof stage. See audit/staged_correspondence/RealCorrespondence01/manifest.json. -/

@[expose] public section

section CanonicalSource0
/- Source: Wishart/RandomMatrixCorrespondence.lean -/



/-!
# Transfer from the canonical Wishart measure to an arbitrary random matrix

The paper is phrased for a random matrix with the stated law. The main target
uses integration against that law itself. These statements transfer every
integral, integrability assertion and equality criterion to any realization
on an arbitrary measure space, so the canonical-measure formulation imposes
no restriction on the underlying probability space.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace WishartVerification

variable {Ω : Type*} [MeasurableSpace Ω] {p d : ℕ}

def samplePrincipalMoment (μ : Measure Ω) (X : Ω → SymmetricMatrix p)
    (P : PrincipalPartition p d) (ν : Fin d → ℝ) (J : Finset (Fin d)) : ℝ :=
  ∫ ω, principalMomentIntegrand P ν J (X ω) ∂μ

theorem samplePrincipalMoment_eq {μ : Measure Ω} {X : Ω → SymmetricMatrix p}
    {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hX : HasLaw X (TauCeti.Probability.nonsingularWishartMeasure α Sigma) μ)
    (P : PrincipalPartition p d) (ν : Fin d → ℝ) (J : Finset (Fin d))
    (hint : Integrable (principalMomentIntegrand P ν J)
      (TauCeti.Probability.nonsingularWishartMeasure α Sigma)) :
    samplePrincipalMoment μ X P ν J = principalMoment α Sigma P ν J :=
  hX.integral_comp hint.aestronglyMeasurable

/-- Theorem 1.1 for every actual random matrix with the density-defined
Wishart law, on any underlying measure space. No new independence, regularity,
integrability, or integer-shape hypothesis is added. -/
theorem theorem_1_1_of_hasLaw {μ : Measure Ω} {X : Ω → SymmetricMatrix p}
    (hp : 0 < p) (hd : 0 < d)
    {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hα : (p : ℝ) - 1 < α) (hSigma : Sigma.PosDef)
    (hX : HasLaw X (TauCeti.Probability.nonsingularWishartMeasure α Sigma) μ)
    (P : PrincipalPartition p d) (ν : Fin d → ℝ) (hν : ∀ i, 0 ≤ ν i) :
    (∀ J : Finset (Fin d), Integrable
      (fun ω => principalMomentIntegrand P ν J (X ω)) μ) ∧
    (∀ j : Fin d,
      samplePrincipalMoment μ X P ν {j} *
          samplePrincipalMoment μ X P ν (Finset.univ.erase j) ≤
        samplePrincipalMoment μ X P ν Finset.univ ∧
      (∏ i : Fin d, samplePrincipalMoment μ X P ν {i}) ≤
        samplePrincipalMoment μ X P ν {j} *
          samplePrincipalMoment μ X P ν (Finset.univ.erase j)) ∧
    ((samplePrincipalMoment μ X P ν Finset.univ =
        ∏ i : Fin d, samplePrincipalMoment μ X P ν {i}) ↔
      independentActiveScaleBlocks Sigma P ν) := by
  have h := theorem_1_1 p d α Sigma P ν hp hd hα hSigma hν
  have heq (J : Finset (Fin d)) :
      samplePrincipalMoment μ X P ν J = principalMoment α Sigma P ν J :=
    samplePrincipalMoment_eq hX P ν J (h.1 J)
  refine ⟨fun J => hX.integrable_comp (h.1 J), ?_, ?_⟩
  · simpa only [heq] using h.2.1
  · simpa only [heq] using h.2.2

end WishartVerification
end
end CanonicalSource0
