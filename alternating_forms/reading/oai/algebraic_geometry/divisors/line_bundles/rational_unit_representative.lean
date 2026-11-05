import OAI.AlgebraicGeometry.Divisors.LineBundles.Ord

/-!
Extracted from openai/math commit 4eaee87548250b2682affda7d05d947c05554bae,
Divisors/LineBundles/RationalBoundary.lean, under Apache 2.0.
Modification: separate the unchanged algebraic rational-unit representative
and germ lemmas from the later analytic boundary construction.
-/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.RationalBoundary.BundleCycles
noncomputable section
open _root_.AlgebraicGeometry _root_.CategoryTheory

/-- Actual unit data representing a rational function on a nonempty open. -/
structure RationalUnitRepresentative (X : Scheme) [IsIntegral X]
    (f : X.functionField) where
  domain : X.Opens
  nonempty_domain : Nonempty domain
  unit : Γ(X, domain)ˣ
  represents : letI := nonempty_domain
    X.germToFunctionField domain (unit : Γ(X, domain)) = f

/-- Existence is supplied by the function-field construction, with no
cohomological hypotheses. -/
def rationalUnitRepresentative (X : Scheme) [IsIntegral X]
    (f : X.functionField) (hf : f ≠ 0) : RationalUnitRepresentative X f := by
  apply Classical.choice
  obtain ⟨U, _, a, hU, hfa, ha⟩ := exists_isUnit_germ_eq X f hf
  refine ⟨⟨U, hU, ha.unit, ?_⟩⟩
  simpa only [ha.unit_spec] using hfa

namespace RationalUnitRepresentative

variable {X : Scheme} [IsIntegral X] {f : X.functionField}

instance (D : RationalUnitRepresentative X f) : Nonempty D.domain := D.nonempty_domain

/-- The divisor coefficients vanish on every such unit-representing open. -/
theorem ord_eq_zero (D : RationalUnitRepresentative X f)
    [IsLocallyNoetherian X] (x : X) (hx : x ∈ D.domain) : X.ord f x = 0 := by
  rw [← D.represents]
  exact Scheme.ord_of_isUnit D.unit.isUnit hx

/-- The finite algebraic divisor is supported outside the unit domain used
to construct the topological boundary. -/
theorem principalDivisor_support_subset (D : RationalUnitRepresentative X f)
    [AlgebraicGeometry.IsNoetherian X] :
    (↑(Ord.BundleCycles.principalDivisor X f).support : Set X) ⊆ (D.domain : Set X)ᶜ := by
  intro x hx hxU
  have hxne := Finsupp.mem_support_iff.mp hx
  exact hxne (D.ord_eq_zero x hxU)

/-- The entire closed support of each divisor term misses the unit domain. -/
theorem principalDivisor_closure_subset (D : RationalUnitRepresentative X f)
    [AlgebraicGeometry.IsNoetherian X] (x : X) (hx : Ord.BundleCycles.principalDivisor X f x ≠ 0) :
    closure ({x} : Set X) ⊆ (D.domain : Set X)ᶜ := by
  apply D.domain.isOpen.isClosed_compl.closure_subset_iff.mpr
  exact Set.singleton_subset_iff.mpr
    (D.principalDivisor_support_subset (Finsupp.mem_support_iff.mpr hx))

/-- Restriction of a regular section leaves its function-field germ unchanged. -/
theorem germ_restrict {U V : X.Opens} [Nonempty U] [Nonempty V]
    (h : V ≤ U) (a : Γ(X, U)) :
    X.germToFunctionField V (X.presheaf.map (homOfLE h).op a) =
      X.germToFunctionField U a :=
  X.presheaf.germ_res_apply (homOfLE h) (genericPoint X) _ a

/-- Any two representatives of the same rational function agree on every
common nonempty subopen, by injectivity into the actual function field. -/
theorem agree_on_common_open (D E : RationalUnitRepresentative X f)
    (V : X.Opens) [Nonempty V] (hD : V ≤ D.domain) (hE : V ≤ E.domain) :
    X.presheaf.map (homOfLE hD).op (D.unit : Γ(X, D.domain)) =
      X.presheaf.map (homOfLE hE).op (E.unit : Γ(X, E.domain)) := by
  apply X.germToFunctionField_injective V
  rw [germ_restrict, germ_restrict, D.represents, E.represents]

end RationalUnitRepresentative
end
end OAI.AlgebraicGeometry.Divisors.LineBundles.RationalBoundary.BundleCycles
