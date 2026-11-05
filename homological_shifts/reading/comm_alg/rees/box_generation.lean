import CommAlg.IntegralClosure.MultiRees

/-! # Generating an actual multigraded Rees ideal in a finite box

The conclusion is equality with an ideal span inside the actual multi-Rees
algebra. It follows from coordinatewise stabilization by induction on the
sum of the Rees exponents and the polynomial's homogeneous decomposition.
-/

noncomputable section

namespace CommAlg

open Classical Finset

variable {J R : Type*} [Fintype J] [DecidableEq J] [CommRing R]

@[simp] theorem powerProduct_single (I : J → Ideal R) (j : J) (n : ℕ) :
    powerProduct I (Finsupp.single j n) = (I j) ^ n := by
  unfold powerProduct
  rw [Finset.prod_eq_single j]
  · simp
  · intro x hx hxj
    simp [Finsupp.single_apply, hxj, Ne.symm hxj]
  · simp

/-- The coefficient ideal of homogeneous monomials that already belong to an
ideal of the actual Rees algebra. -/
def homogeneousCoefficientIdeal (I : J → Ideal R) (L : Ideal (multiReesAlgebra I))
    (s : J →₀ ℕ) : Ideal R where
  carrier := {r | ∃ p ∈ L, p.val = MvPolynomial.monomial s r}
  zero_mem' := ⟨0, L.zero_mem, by simp⟩
  add_mem' := by
    rintro r t ⟨p, hp, he⟩ ⟨q, hq, hf⟩
    refine ⟨p + q, L.add_mem hp hq, ?_⟩
    change p.val + q.val = _
    rw [he, hf, map_add]
  smul_mem' := by
    intro a r
    rintro ⟨p, hp, he⟩
    refine ⟨(algebraMap R (multiReesAlgebra I) a) * p,
      L.mul_mem_left _ hp, ?_⟩
    change MvPolynomial.C a * p.val = MvPolynomial.monomial s (a * r)
    rw [he, MvPolynomial.C_mul_monomial]

@[simp] theorem mem_homogeneousCoefficientIdeal (I : J → Ideal R)
    (L : Ideal (multiReesAlgebra I)) (s : J →₀ ℕ) (r : R) :
    r ∈ homogeneousCoefficientIdeal I L s ↔
      ∃ p ∈ L, p.val = MvPolynomial.monomial s r := Iff.rfl

/-- Multiplication here is the actual multiplication of homogeneous
polynomials inside the Rees subalgebra. -/
theorem homogeneousCoefficientIdeal_action (I : J → Ideal R)
    (L : Ideal (multiReesAlgebra I)) (s t : J →₀ ℕ) :
    powerProduct I s * homogeneousCoefficientIdeal I L t ≤
      homogeneousCoefficientIdeal I L (s + t) := by
  apply Ideal.mul_le.mpr
  intro r hr q hq
  obtain ⟨p, hp, he⟩ := hq
  let x : multiReesAlgebra I :=
    ⟨MvPolynomial.monomial s r, (monomial_mem_multiReesAlgebra I s r).mpr hr⟩
  refine ⟨x * p, L.mul_mem_left x hp, ?_⟩
  change MvPolynomial.monomial s r * p.val = _
  rw [he, MvPolynomial.monomial_mul_monomial]

/-- All homogeneous module elements whose Rees multidegree belongs to the
closed coordinate box. Polynomial coefficients are unrestricted elements of
the corresponding actual coefficient ideal. -/
def reesBoxGenerators (I : J → Ideal R) (K : (J →₀ ℕ) → Ideal R) (i : ℕ) :
    Set (multiReesAlgebra I) :=
  {p | ∃ s r, (∀ j, s j ≤ i) ∧ r ∈ K s ∧ p.val = MvPolynomial.monomial s r}

theorem reesBoxGenerators_subset (I : J → Ideal R) (K : (J →₀ ℕ) → Ideal R)
    (hact : ∀ s t, powerProduct I s * K t ≤ K (s + t)) (i : ℕ) :
    reesBoxGenerators I K i ⊆ multiReesIdeal I K hact := by
  rintro p ⟨s, r, hs, hr, he⟩ t
  rw [he]
  by_cases ht : t = s
  · subst t; simpa using hr
  · simp [MvPolynomial.coeff_monomial, ht, Ne.symm ht]

/-- Coordinate stabilization implies equality with the span of the actual
homogeneous elements in the finite Rees-degree box. -/
theorem multiReesIdeal_span_box (I : J → Ideal R) (K : (J →₀ ℕ) → Ideal R)
    (hact : ∀ s t, powerProduct I s * K t ≤ K (s + t))
    (hsub : ∀ s, K s ≤ powerProduct I s) (i : ℕ)
    (hstep : ∀ s j, i ≤ s j → K (s + Finsupp.single j 1) = I j * K s) :
    multiReesIdeal I K hact = Ideal.span (reesBoxGenerators I K i) := by
  let L : Ideal (multiReesAlgebra I) := Ideal.span (reesBoxGenerators I K i)
  have hc : ∀ n : ℕ, ∀ s : J →₀ ℕ, s.degree = n →
      K s ≤ homogeneousCoefficientIdeal I L s := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hs
      by_cases hbox : ∀ j, s j ≤ i
      · intro r hr
        let p : multiReesAlgebra I :=
          ⟨MvPolynomial.monomial s r, (monomial_mem_multiReesAlgebra I s r).mpr (hsub s hr)⟩
        exact ⟨p, Ideal.subset_span ⟨s, r, hbox, hr, rfl⟩, rfl⟩
      · push_neg at hbox
        obtain ⟨j, hj⟩ := hbox
        let t := s - Finsupp.single j 1
        have he : t + Finsupp.single j 1 = s := by
          apply tsub_add_cancel_of_le
          intro x
          by_cases hx : x = j
          · subst x
            simpa using (show 1 ≤ s j by omega)
          · simp [Finsupp.single_apply, hx, Ne.symm hx]
        have htj : i ≤ t j := by
          change i ≤ s j - (Finsupp.single j 1) j
          simp only [Finsupp.single_eq_same]
          omega
        have htdeg : t.degree < n := by
          have hh := congrArg Finsupp.degree he
          simp only [map_add, Finsupp.degree_single, hs] at hh
          omega
        have hit := ih t.degree htdeg t rfl
        rw [← he, hstep t j htj]
        calc
          I j * K t ≤ I j * homogeneousCoefficientIdeal I L t := Ideal.mul_mono le_rfl hit
          _ ≤ homogeneousCoefficientIdeal I L (t + Finsupp.single j 1) := by
            have hh := homogeneousCoefficientIdeal_action I L (Finsupp.single j 1) t
            simpa only [powerProduct_single, pow_one, add_comm] using hh
  apply le_antisymm
  · intro p hp
    have hh : ∀ s, ∃ q ∈ L, q.val =
        MvPolynomial.monomial s (p.val.coeff s) := fun s => hc s.degree s rfl (hp s)
    choose q hq he using hh
    have hsum : ∑ s ∈ p.val.support, q s ∈ L :=
      L.sum_mem (fun s hs => hq s)
    have heq : (∑ s ∈ p.val.support, q s) = p := by
      apply Subtype.ext
      change (multiReesAlgebra I).val (∑ s ∈ p.val.support, q s) = p.val
      rw [map_sum]
      calc
        (∑ s ∈ p.val.support, (q s).val) =
            ∑ s ∈ p.val.support, MvPolynomial.monomial s (p.val.coeff s) :=
          Finset.sum_congr rfl (fun s hs => he s)
        _ = p.val := (MvPolynomial.as_sum p.val).symm
    rwa [heq] at hsum
  · exact Ideal.span_le.mpr (reesBoxGenerators_subset I K hact i)

end CommAlg
