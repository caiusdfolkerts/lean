module

public import ToricPower.CoherentEpimorphismLifting
public import ToricPower.CohomologyFiniteDimensional

/-!
# Transferring Cartier cohomology finiteness to all coherent sheaves

Finite Cartier epimorphisms and a uniform cohomological bound suffice.
Dimension shifting raises the degree until the kernel's cohomology
vanishes. No terminating resolution by sums of line bundles is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace ToricPower

universe u v

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
  [IsIntegral X] [IsLocallyNoetherian X]

/-- The precise dimension-shifting argument. The hypotheses are the
geometric finite Cartier cover, the actual base-linear Cartier finiteness,
and a uniform bound on the actual cohomology of coherent sheaves. -/
theorem coherentCohomology_finite_of_cartier_and_bound
    (cover : ∀ (M : X.Modules) [M.IsFinitePresentation],
      ∃ (J : Type v) (finite : Finite J),
        letI := finite
        ∃ (D : J → TauCeti.AlgebraicGeometry.Scheme.CartierDivisor X)
          (q : (⨁ fun a => (D a).sheaf) ⟶ M), Epi q)
    (cartierFinite : ∀ (D : TauCeti.AlgebraicGeometry.Scheme.CartierDivisor X) (degree : ℕ),
      FiniteDimensional k (Cohomology D.sheaf degree))
    (bound : ℕ)
    (vanishes : ∀ (M : X.Modules) [M.IsFinitePresentation] (degree : ℕ),
      bound < degree → Subsingleton (Cohomology M degree))
    (M : X.Modules) [M.IsFinitePresentation] (degree : ℕ) :
    FiniteDimensional k (Cohomology M degree) := by
  have descending : ∀ depth : ℕ, ∀ (F : X.Modules) [F.IsFinitePresentation] (n : ℕ),
      n + depth = bound + 1 → FiniteDimensional k (Cohomology F n) := by
    intro depth
    induction depth with
    | zero =>
        intro F hF n equality
        letI := vanishes F n (by omega)
        infer_instance
    | succ depth ih =>
        intro F hF n equality
        obtain ⟨J, finite, D, q, epi⟩ := cover F
        letI := finite
        letI := epi
        let family := fun a : J => (D a).sheaf
        letI : (⨁ family).IsFinitePresentation :=
          (finiteCartierBiproduct_finiteLocallyFree D).2
        letI : (kernel q).IsFinitePresentation := finitePresentation_kernel q
        let S := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
        have exactSequence : S.ShortExact :=
          { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel q) }
        letI : FiniteDimensional k (Cohomology S.X₂ n) :=
          finiteDimensional_cohomology_biproduct k X family n (fun a => cartierFinite (D a) n)
        letI : FiniteDimensional k (Cohomology S.X₁ (n + 1)) :=
          ih (kernel q) (n + 1) (by omega)
        exact finiteDimensional_cohomology_quotient k X exactSequence n
  by_cases high : bound < degree
  · letI := vanishes M degree high
    infer_instance
  · exact descending (bound + 1 - degree) M degree (by omega)

end ToricPower

end
