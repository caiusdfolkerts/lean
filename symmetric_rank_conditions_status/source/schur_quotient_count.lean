module
public import applications_verification

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

/-!
# Initial ideals and symbolic-power standard bases

The initial-ideal formula here is the literal conclusion of Theorem 1.2.
The symbolic specialization gives the Gröbner basis and monomial criterion
of Corollary 5.3, followed by its Hilbert function as a count in every actual
endpoint multidegree. The Schur-polynomial notation for the same tableau
generating function is not introduced in this file.

These source declarations require acceptance by the complete project build.
-/

namespace FourPapers.Symmetric.Schur

open MvPolynomial Pivot

universe u

theorem theorem_1_2_initial (n : ℕ) (K : Type u) [Field K]
    (r : RankArray n) (hr : ∀ i j, r i j = r j i)
    (conditions : List (ℕ × ℕ)) (hvalid : ValidSymbolicConditions n conditions) :
    initialIdeal K (mixedIdeal K r conditions) = northwestAntidiagonalIdeal K r ⊔
      ∑ ts ∈ conditions.toFinset, symbolicAntidiagonalIdeal K n ts.1 ts.2 :=
  mixed_initial_eq_of_groebner K r conditions
    (compatible_rank_and_symbolic_conditions n K r hr conditions hvalid)

theorem northwestGenerators_unconstrained (n : ℕ) (R : Type*) [CommRing R] :
    northwestGenerators R (fun _ _ : Fin n => n) = ∅ := by
  ext f
  constructor
  · rintro ⟨i, j, a, b, ha, hb, hf⟩
    have hcard := Fintype.card_le_of_injective a a.injective
    simp only [Fintype.card_fin] at hcard
    omega
  · simp

theorem northwestIdeal_unconstrained (n : ℕ) (R : Type*) [CommRing R] :
    northwestIdeal R (fun _ _ : Fin n => n) = ⊥ := by
  rw [northwestIdeal, northwestGenerators_unconstrained, Ideal.span_empty]

theorem northwestAntidiagonals_unconstrained (n : ℕ) (R : Type*) [CommRing R] :
    northwestAntidiagonals R (fun _ _ : Fin n => n) = ∅ := by
  ext f
  constructor
  · rintro ⟨i, j, a, b, ha, hb, hf⟩
    have hcard := Fintype.card_le_of_injective a a.injective
    simp only [Fintype.card_fin] at hcard
    omega
  · simp

theorem northwestAntidiagonalIdeal_unconstrained (n : ℕ) (R : Type*) [CommRing R] :
    northwestAntidiagonalIdeal R (fun _ _ : Fin n => n) = ⊥ := by
  rw [northwestAntidiagonalIdeal, northwestAntidiagonals_unconstrained, Ideal.span_empty]

theorem validSymbolicConditions_singleton {n t s : ℕ}
    (ht : 1 ≤ t) (htn : t ≤ n) (hs : 1 ≤ s) :
    ValidSymbolicConditions n [(t, s)] := by
  intro ts hts
  have he : ts = (t, s) := List.mem_singleton.mp hts
  subst ts
  exact ⟨ht, htn, hs⟩

theorem determinantalIdeal_eq_bot_of_size_gt (n t : ℕ)
    (R : Type*) [CommRing R] (ht : n < t) : determinantalIdeal n R t = ⊥ := by
  unfold determinantalIdeal
  rw [Ideal.span_eq_bot]
  rintro f ⟨a,b,rfl⟩
  have hcard := Fintype.card_le_of_injective a a.injective
  simp only [Fintype.card_fin] at hcard
  omega

/-- The full symbolic generator family is a Gröbner basis of the genuine
symbolic power, for all parameters in the paper's range. -/
theorem corollary_5_3_groebner (n : ℕ) (K : Type u) [Field K]
    (t s : ℕ) (ht : 1 ≤ t) (htn : t ≤ n) (hs : 1 ≤ s) :
    (foldedOrder n).IsGroebnerBasis (symbolicGenerators K n t s)
      (symbolicPower (determinantalIdeal n K t) s) := by
  have h := compatible_rank_and_symbolic_conditions n K (fun _ _ : Fin n => n) (fun _ _ => rfl)
    [(t, s)] (validSymbolicConditions_singleton ht htn hs)
  simpa [mixedGenerators, mixedIdeal, northwestGenerators_unconstrained,
    northwestIdeal_unconstrained] using h

theorem corollary_5_3_initial (n : ℕ) (K : Type u) [Field K]
    (t s : ℕ) (ht : 1 ≤ t) (htn : t ≤ n) (hs : 1 ≤ s) :
    initialIdeal K (symbolicPower (determinantalIdeal n K t) s) =
      symbolicAntidiagonalIdeal K n t s := by
  have h := theorem_1_2_initial n K (fun _ _ : Fin n => n) (fun _ _ => rfl)
    [(t, s)] (validSymbolicConditions_singleton ht htn hs)
  simpa [mixedIdeal, northwestIdeal_unconstrained,
    northwestAntidiagonalIdeal_unconstrained] using h

theorem monomial_mem_symbolic_iff_gamma {n : ℕ} (K : Type u) [Field K]
    (t s : ℕ) (ht : 0 < t) (m : Entry n →₀ ℕ) :
    monomial m (1 : K) ∈ symbolicAntidiagonalIdeal K n t s ↔ s ≤ gamma t m := by
  rw [Rees.mem_symbolicAntidiagonalIdeal_iff_gamma n K t s ht]
  simp

/-- The initial-ideal test uses the tail area of the actual insertion
tableau, with no restriction on the original monomial multiplicities. -/
theorem corollary_5_3_monomial (n : ℕ) (K : Type u) [Field K]
    (t s : ℕ) (ht : 1 ≤ t) (htn : t ≤ n) (hs : 1 ≤ s)
    (m : Entry n →₀ ℕ) :
    monomial m (1 : K) ∈ initialIdeal K (symbolicPower (determinantalIdeal n K t) s) ↔
      s ≤ gamma t m := by
  rw [corollary_5_3_initial n K t s ht htn hs]
  exact monomial_mem_symbolic_iff_gamma K t s ht m

theorem corollary_5_3_standardMonomials (n : ℕ) (K : Type u) [Field K]
    (t s : ℕ) (ht : 1 ≤ t) (htn : t ≤ n) (hs : 1 ≤ s) :
    (foldedOrder n).standardMonomials (symbolicPower (determinantalIdeal n K t) s) =
      {m | gamma t m < s} := by
  have hG := compatible_rank_and_symbolic_conditions n K (fun _ _ : Fin n => n) (fun _ _ => rfl)
    [(t, s)] (validSymbolicConditions_singleton ht htn hs)
  have hstd := mixed_standardMonomials_eq K (fun _ _ : Fin n => n) [(t, s)] hG
  have hstd' :
      (foldedOrder n).standardMonomials (symbolicPower (determinantalIdeal n K t) s) =
        {m | monomial m (1 : K) ∉ symbolicAntidiagonalIdeal K n t s} := by
    simpa [mixedIdeal, northwestIdeal_unconstrained,
      northwestAntidiagonalIdeal_unconstrained] using hstd
  rw [hstd']
  ext m
  simp only [Set.mem_setOf_eq, monomial_mem_symbolic_iff_gamma K t s ht m, Nat.not_le]

/-- Every endpoint-graded Hilbert coefficient is the number of actual
monomials whose insertion score is below the symbolic exponent. This is a
finite count, including degree vectors with empty homogeneous component. -/
theorem corollary_5_3_hilbert_coefficient (n : ℕ) (K : Type u) [Field K]
    (t s : ℕ) (ht : 1 ≤ t) (htn : t ≤ n) (hs : 1 ≤ s) (d : Fin n →₀ ℕ) :
    Module.finrank K
      (quotientPiece (symbolicPower (determinantalIdeal n K t) s) endpointWeight d) =
      {m : Entry n →₀ ℕ |
        gamma t m < s ∧ Finsupp.weight endpointWeight m = d}.ncard := by
  letI : (determinantalIdeal n K t).IsPrime := Rees.determinantal_prime n K t ht
  have hhom := determinantal_symbolic_endpoint_homogeneous (R := K) n t s
  have hf : (standardPieceSet (foldedOrder n)
      (symbolicPower (determinantalIdeal n K t) s) endpointWeight d).Finite :=
    (endpointWeight_fibers_finite d).subset (fun _ hm => hm.2)
  have h := finrank_quotientPiece (foldedOrder n)
    (symbolicPower (determinantalIdeal n K t) s) endpointWeight hhom d hf
  simpa only [standardPieceSet, corollary_5_3_standardMonomials n K t s ht htn hs,
    Set.mem_setOf_eq] using h

end FourPapers.Symmetric.Schur

#print axioms FourPapers.Symmetric.Schur.theorem_1_2_initial
#print axioms FourPapers.Symmetric.Schur.corollary_5_3_groebner
#print axioms FourPapers.Symmetric.Schur.corollary_5_3_initial
#print axioms FourPapers.Symmetric.Schur.corollary_5_3_monomial
#print axioms FourPapers.Symmetric.Schur.corollary_5_3_hilbert_coefficient
