module

public import PaperVerification.PowerOriginalRepresentation

/-!
# The equal-coefficient power-sum comparison

Nonresonance for a constant coefficient tuple forces every nonempty subset
cardinality to remain nonzero in the field. Hence the undeformed all-one tail
satisfies nonresonance. Its quotient is identified, on actual polynomial
classes, with the quotient by the literal power sums. Applying the proved
graded comparison to this undeformed tail yields the power-sum option in
Theorem 2.2 without any added characteristic hypothesis.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Representation
open scoped BigOperators

namespace PaperVerification.PowerOperators

variable {K : Type*} [Field K] {n : ℕ}

theorem constant_nonresonance_subset_card_ne_zero (a lam : K) (m : ℕ)
    (hnr : Nonresonant (fun _ : Fin n => a) lam m)
    (I : Finset (Fin n)) (hI : I.Nonempty) : (I.card : K) ≠ 0 := by
  intro hz
  have h := hnr I hI (m*I.card) le_rfl
  simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_mul,hz,zero_mul,mul_zero,
    add_zero,ne_eq,not_true_eq_false] at h

theorem constant_nonresonance_implies_one_zero (a lam : K) (m : ℕ)
    (hnr : Nonresonant (fun _ : Fin n => a) lam m) :
    Nonresonant (fun _ : Fin n => (1 : K)) 0 m := by
  intro I hI s hs
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_one,zero_mul,add_zero] using
    constant_nonresonance_subset_card_ne_zero a lam m hnr I hI

def powerSumFamily (K : Type*) [Field K] (n m : ℕ) :
    Fin n → MvPolynomial (Fin n) K := fun i => MvPolynomial.psum (Fin n) K (m+i.val)

abbrev powerSumIdeal (K : Type*) [Field K] (n m : ℕ) :
    Ideal (MvPolynomial (Fin n) K) := ordinaryFamilyIdeal (powerSumFamily K n m)

theorem powerSumFamily_invariant (G : Subgroup (Equiv.Perm (Fin n))) (m : ℕ)
    (g : G) (i : Fin n) :
    MvPolynomial.rename (g : Equiv.Perm (Fin n)) (powerSumFamily K n m i) =
      powerSumFamily K n m i :=
  MvPolynomial.rename_psum _ _ _ _

def powerSumAction (G : Subgroup (Equiv.Perm (Fin n))) (m : ℕ) :
    Representation K G (MvPolynomial (Fin n) K ⧸ powerSumIdeal K n m) :=
  ordinaryQuotientAction G (powerSumFamily K n m) (powerSumFamily_invariant G m)

theorem tailHit_one_zero_eq_powerSumIdeal (m : ℕ) :
    tailHit (fun _ : Fin n => (1 : K)) 0 m = (powerSumIdeal K n m).restrictScalars K := by
  have hfamily : (fun i : Fin n => weightedPower (fun _ : Fin n => (1 : K))
      (m+i.val)) = powerSumFamily K n m := by
    funext i
    simp only [weightedPower,MvPolynomial.C_1,one_mul,powerSumFamily,MvPolynomial.psum]
  rw [tailHit_zero_eq_ordinaryPowerIdeal,ordinaryPowerIdeal,hfamily]
  rfl

def zeroTailPowerSumEquiv (m : ℕ) :
    (MvPolynomial (Fin n) K ⧸ tailHit (fun _ : Fin n => (1 : K)) 0 m) ≃ₗ[K]
      (MvPolynomial (Fin n) K ⧸ powerSumIdeal K n m) :=
  Submodule.Quotient.equiv _ ((powerSumIdeal K n m).restrictScalars K)
    (LinearEquiv.refl K _) (by
      change (tailHit (fun _ : Fin n => (1 : K)) 0 m).map LinearMap.id = _
      rw [Submodule.map_id]
      exact tailHit_one_zero_eq_powerSumIdeal m)

@[simp] theorem zeroTailPowerSumEquiv_mkQ (m : ℕ) (p : MvPolynomial (Fin n) K) :
    zeroTailPowerSumEquiv (K := K) m ((tailHit (fun _ : Fin n => (1 : K)) 0 m).mkQ p) =
      (powerSumIdeal K n m).mkQ p := rfl

def zeroTailPowerSumRepresentationEquiv (G : Subgroup (Equiv.Perm (Fin n))) (m : ℕ) :
    (tailQuotientAction G (fun _ : Fin n => (1 : K)) 0 m (fun _ _ => rfl)).Equiv
      (powerSumAction G m) :=
  Representation.Equiv.mk (zeroTailPowerSumEquiv m) (by
    intro g
    apply LinearMap.ext
    intro x
    obtain ⟨p,rfl⟩ := (tailHit (fun _ : Fin n => (1 : K)) 0 m).mkQ_surjective x
    change zeroTailPowerSumEquiv m
      (tailQuotientAction G (fun _ : Fin n => (1 : K)) 0 m (fun _ _ => rfl) g
        ((tailHit (fun _ : Fin n => (1 : K)) 0 m).mkQ p)) =
      powerSumAction G m g
        (zeroTailPowerSumEquiv m ((tailHit (fun _ : Fin n => (1 : K)) 0 m).mkQ p))
    rw [tailQuotientAction_mkQ,zeroTailPowerSumEquiv_mkQ,zeroTailPowerSumEquiv_mkQ]
    rfl)

theorem zeroTailPowerSumEquiv_preserves_degree (m d : ℕ)
    {x : MvPolynomial (Fin n) K ⧸ tailHit (fun _ : Fin n => (1 : K)) 0 m}
    (hx : x ∈ tailQuotientDegree (fun _ : Fin n => (1 : K)) 0 m d) :
    zeroTailPowerSumEquiv m x ∈ ordinaryQuotientDegree (powerSumFamily K n m) d := by
  obtain ⟨p,hp,rfl⟩ := hx
  rw [zeroTailPowerSumEquiv_mkQ]
  exact ⟨p,hp,rfl⟩

theorem zeroTailPowerSumEquiv_symm_preserves_degree (m d : ℕ)
    {x : MvPolynomial (Fin n) K ⧸ powerSumIdeal K n m}
    (hx : x ∈ ordinaryQuotientDegree (powerSumFamily K n m) d) :
    (zeroTailPowerSumEquiv m).symm x ∈
      tailQuotientDegree (fun _ : Fin n => (1 : K)) 0 m d := by
  obtain ⟨p,hp,rfl⟩ := hx
  refine ⟨p,hp,?_⟩
  apply (zeroTailPowerSumEquiv (K := K) m).injective
  rw [zeroTailPowerSumEquiv_mkQ,LinearEquiv.apply_symm_apply]
  rfl

theorem complete_powerSum_graded_representation (a lam : K) (m : ℕ) (hm : 0 < m)
    (hnr : Nonresonant (fun _ : Fin n => a) lam m)
    (G : Subgroup (Equiv.Perm (Fin n))) :
    ∃ e : (completeHomogeneousAction (K := K) G m).Equiv (powerSumAction G m),
      (∀ d x, x ∈ ordinaryQuotientDegree (completeHomogeneousFamily K n m) d →
        e x ∈ ordinaryQuotientDegree (powerSumFamily K n m) d) ∧
      (∀ d y, y ∈ ordinaryQuotientDegree (powerSumFamily K n m) d →
        e.symm y ∈ ordinaryQuotientDegree (completeHomogeneousFamily K n m) d) := by
  have h₁ := constant_nonresonance_implies_one_zero a lam m hnr
  obtain ⟨e,he,he'⟩ := paper_theorem_2_2_graded_representation
    (fun _ : Fin n => (1 : K)) 0 m hm h₁ G (fun _ _ => rfl)
  refine ⟨e.symm.trans (zeroTailPowerSumRepresentationEquiv G m),?_,?_⟩
  · intro d x hx
    exact zeroTailPowerSumEquiv_preserves_degree m d (he' d x hx)
  · intro d y hy
    exact he d _ (zeroTailPowerSumEquiv_symm_preserves_degree m d hy)

/-- The power-sum alternative for the reversed family with coinciding
coefficients, over every field allowed by the original nonresonance condition. -/
theorem paper_theorem_2_2_equal_coefficient_power_sums (a lam : K) (m : ℕ) (hm : 0 < m)
    (hnr : Nonresonant (fun _ : Fin n => a) lam m)
    (G : Subgroup (Equiv.Perm (Fin n))) :
    ∃ e : (tailQuotientAction G (fun _ : Fin n => a) lam m (fun _ _ => rfl)).Equiv
        (powerSumAction G m),
      (∀ d x, x ∈ tailQuotientDegree (fun _ : Fin n => a) lam m d →
        e x ∈ ordinaryQuotientDegree (powerSumFamily K n m) d) ∧
      (∀ d y, y ∈ ordinaryQuotientDegree (powerSumFamily K n m) d →
        e.symm y ∈ tailQuotientDegree (fun _ : Fin n => a) lam m d) := by
  obtain ⟨e,he,he'⟩ := paper_theorem_2_2_graded_representation
    (fun _ : Fin n => a) lam m hm hnr G (fun _ _ => rfl)
  obtain ⟨f,hf,hf'⟩ := complete_powerSum_graded_representation a lam m hm hnr G
  exact ⟨e.trans f,fun d x hx => hf d _ (he d x hx),fun d y hy => he' d _ (hf' d y hy)⟩

/-- The same literal power-sum alternative for the original family, under
precisely the additional low-exponent hypothesis (2.3). -/
theorem paper_theorem_2_2_original_equal_coefficient_power_sums
    (a lam : K) (m : ℕ) (hm : 0 < m)
    (hnr : Nonresonant (fun _ : Fin n => a) lam m)
    (hlow : ∀ i : Fin n, ∀ b : ℕ, b < m → a + lam * (b : K) ≠ 0)
    (G : Subgroup (Equiv.Perm (Fin n))) :
    ∃ e : (originalTailQuotientAction G (fun _ : Fin n => a) lam m (fun _ _ => rfl)).Equiv
        (powerSumAction G m),
      (∀ d x, x ∈ originalTailQuotientDegree (fun _ : Fin n => a) lam m d →
        e x ∈ ordinaryQuotientDegree (powerSumFamily K n m) d) ∧
      (∀ d y, y ∈ ordinaryQuotientDegree (powerSumFamily K n m) d →
        e.symm y ∈ originalTailQuotientDegree (fun _ : Fin n => a) lam m d) := by
  obtain ⟨e,he,he'⟩ := paper_theorem_2_2_original_graded_representation
    (fun _ : Fin n => a) lam m hm hnr hlow G (fun _ _ => rfl)
  obtain ⟨f,hf,hf'⟩ := complete_powerSum_graded_representation a lam m hm hnr G
  exact ⟨e.trans f,fun d x hx => hf d _ (he d x hx),fun d y hy => he' d _ (hf' d y hy)⟩

end PaperVerification.PowerOperators
