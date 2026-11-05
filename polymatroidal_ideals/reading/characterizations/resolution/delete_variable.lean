import Characterizations.Resolution.Specialize
import CommAlg.Polymatroid.Exponents
import Mathlib.Algebra.MvPolynomial.Division

/-! Removing a polynomial variable from a genuine linear free resolution. -/
noncomputable section
namespace Characterizations.Resolution
open Classical Finset MvPolynomial CommAlg.Polymatroid
universe u
variable {V k : Type u} [CommRing k]

lemma killCompl_homogeneous {W : Type u} (f : W → V) (hf : Function.Injective f)
    {p : MvPolynomial V k} {d : ℕ} (hp : p.IsHomogeneous d) :
    (MvPolynomial.killCompl hf p).IsHomogeneous d := by
  intro a ha
  have hcoeff : p.coeff (a.mapDomain f) ≠ 0 := by
    simpa only [MvPolynomial.coeff_killCompl] using ha
  simpa only [Pi.one_def, ← Finsupp.degree_eq_weight_one, Finsupp.degree_mapDomain]
    using hp hcoeff

lemma killCompl_kernel_of_range {W : Type u} (f : W → V) (hf : Function.Injective f)
    (j : V) (hrange : ∀ i, i ∈ Set.range f ↔ i ≠ j)
    (p : MvPolynomial V k) (hp : MvPolynomial.killCompl hf p = 0) :
    ∃ q, p = X j * q := by
  have hz : ∀ a : V →₀ ℕ, a j = 0 → p.coeff a = 0 := by
    intro a ha
    have hs : ↑a.support ⊆ Set.range f := by
      intro i hi
      apply (hrange i).mpr
      intro he
      subst i
      exact (Finsupp.mem_support_iff.mp hi) ha
    let b := a.comapDomain f hf.injOn
    have hb : b.mapDomain f = a := a.mapDomain_comapDomain f hf hs
    have hc := congrArg (fun q : MvPolynomial W k => q.coeff b) hp
    simpa [MvPolynomial.coeff_killCompl, hb] using hc
  have hdvd : X j ∣ p := by
    rw [p.as_sum]
    apply Finset.dvd_sum
    intro a ha
    rw [MvPolynomial.X_dvd_monomial]
    by_cases hj : a j = 0
    · exact Or.inl (hz a hj)
    · exact Or.inr hj
  obtain ⟨q,hq⟩ := hdvd
  exact ⟨q,hq⟩

abbrev Deleted (j : V) := {i : V // i ≠ j}

def deleteVariable (j : V) : MvPolynomial V k →ₐ[k] MvPolynomial (Deleted j) k :=
  MvPolynomial.killCompl (f := Subtype.val) Subtype.val_injective

lemma deleteVariable_surjective (j : V) : Function.Surjective (deleteVariable (k:=k) j) := by
  intro p
  exact ⟨MvPolynomial.rename Subtype.val p, MvPolynomial.killCompl_rename_app _ _⟩

@[simp] lemma deleteVariable_X (j : V) : deleteVariable (k:=k) j (X j) = 0 := by
  apply MvPolynomial.killCompl_monomial_eq_zero_of_notMem_range
    Subtype.val_injective 1 (a := j)
  · simp
  · rintro ⟨i,hi⟩
    exact i.property hi

lemma deleteVariable_homogeneous (j : V) {p : MvPolynomial V k} {d : ℕ}
    (hp : p.IsHomogeneous d) : (deleteVariable j p).IsHomogeneous d := by
  intro a ha
  have hcoeff : p.coeff (a.mapDomain Subtype.val) ≠ 0 := by
    simpa only [deleteVariable, MvPolynomial.coeff_killCompl] using ha
  have h := hp hcoeff
  simpa only [Pi.one_def, ← Finsupp.degree_eq_weight_one, Finsupp.degree_mapDomain] using h

lemma deleteVariable_kernel (j : V) (p : MvPolynomial V k)
    (hp : deleteVariable j p = 0) : ∃ q, p = X j * q := by
  have hz : ∀ a : V →₀ ℕ, a j = 0 → p.coeff a = 0 := by
    intro a ha
    have hs : ↑a.support ⊆ Set.range (Subtype.val : Deleted j → V) := by
      intro i hi
      have hne : i ≠ j := by
        intro he
        subst i
        exact (Finsupp.mem_support_iff.mp hi) ha
      exact ⟨⟨i,hne⟩,rfl⟩
    let b := a.comapDomain (Subtype.val : Deleted j → V) Subtype.val_injective.injOn
    have hb : b.mapDomain Subtype.val = a :=
      a.mapDomain_comapDomain (Subtype.val : Deleted j → V) Subtype.val_injective hs
    have hc := congrArg (fun q : MvPolynomial (Deleted j) k => q.coeff b) hp
    simpa [deleteVariable, MvPolynomial.coeff_killCompl, hb] using hc
  have hdvd : X j ∣ p := by
    rw [p.as_sum]
    apply Finset.dvd_sum
    intro a ha
    rw [MvPolynomial.X_dvd_monomial]
    by_cases hj : a j = 0
    · exact Or.inl (hz a hj)
    · exact Or.inr hj
  obtain ⟨q,hq⟩ := hdvd
  exact ⟨q,hq⟩

lemma monomialIdeal_variable_saturated [Fintype V] [DecidableEq V]
    (B : Family V) (j : V) (hs : ∀ a ∈ B, a j = 0)
    (p : MvPolynomial V k) (hp : X j * p ∈ monomialIdeal k B) :
    p ∈ monomialIdeal k B := by
  rw [mem_monomialIdeal_iff] at hp ⊢
  intro a ha
  have hsum : a + Finsupp.single j 1 ∈ (X j * p).support := by
    rw [MvPolynomial.mem_support_iff, add_comm a, MvPolynomial.coeff_X_mul]
    exact MvPolynomial.mem_support_iff.mp ha
  obtain ⟨b,hb,hba⟩ := hp _ hsum
  refine ⟨b,hb,fun i => ?_⟩
  by_cases hi : i = j
  · subst i
    rw [hs b hb]
    exact Nat.zero_le _
  · simpa [Finsupp.single_apply, hi] using hba i

end Characterizations.Resolution
