module

public import Recovery.Unimodular.FlagKoszul.MonomialQuotient
public import Mathlib.RingTheory.Ideal.Colon

/-!
# Commutative flag algebras and variable ideals

The rings here are ordinary polynomial quotients. Compatibility is required
only to be reflexive and symmetric: no transitivity is used. The ideals generated
by variables form the exact colon family needed for the Koszul filtration.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators

namespace Unimodular.FlagKoszul

variable {E K : Type*} [Field K]

abbrev Exp (E : Type*) := E →₀ ℕ

def Valid (R : E → E → Prop) (u : Exp E) : Prop :=
  ∀ i, u i ≠ 0 → ∀ j, u j ≠ 0 → R i j

def Allowed (R : E → E → Prop) (S : Set E) (u : Exp E) : Prop :=
  Valid R u ∧ ∀ i ∈ S, u i = 0

def bad (R : E → E → Prop) (S : Set E) : Set (Exp E) :=
  {u | ¬ Allowed R S u}

theorem allowed_of_le {R : E → E → Prop} {S : Set E} {u v : Exp E}
    (huv : u ≤ v) (hv : Allowed R S v) : Allowed R S u := by
  refine ⟨?_, ?_⟩
  · intro i hi j hj
    exact hv.1 i (fun h => hi (Nat.eq_zero_of_le_zero (h ▸ huv i)))
      j (fun h => hj (Nat.eq_zero_of_le_zero (h ▸ huv j)))
  · intro i hi
    exact Nat.eq_zero_of_le_zero (hv.2 i hi ▸ huv i)

theorem bad_upper (R : E → E → Prop) (S : Set E) : IsUpperSet (bad R S) := by
  intro u v huv hu hv
  exact hu (allowed_of_le huv hv)

def ideal (R : E → E → Prop) (S : Set E) : Ideal (MvPolynomial E K) :=
  MonomialQuotient.ideal (bad R S) (bad_upper R S)

abbrev FlagAlgebra (R : E → E → Prop) (K : Type*) [Field K] :=
  MvPolynomial E K ⧸ ideal R (∅ : Set E)

abbrev Point (R : E → E → Prop) (S : Set E) := {u : Exp E // Allowed R S u}

theorem mem_ideal_iff (R : E → E → Prop) (S : Set E) (f : MvPolynomial E K) :
    f ∈ ideal R S ↔ ∀ u ∈ f.support, ¬ Allowed R S u := Iff.rfl

theorem ideal_mono (R : E → E → Prop) {S T : Set E} (hST : S ⊆ T) :
    ideal R S (K := K) ≤ ideal R T := by
  intro f hf
  rw [mem_ideal_iff] at hf ⊢
  intro u hu hgood
  exact hf u hu ⟨hgood.1, fun i hi => hgood.2 i (hST hi)⟩

theorem ideal_eq_span (R : E → E → Prop) (S : Set E) :
    ideal R S (K := K) =
      Ideal.span ((fun u => MvPolynomial.monomial u (1 : K)) '' bad R S) := by
  ext f
  rw [mem_ideal_iff, MvPolynomial.mem_ideal_span_monomial_image]
  exact forall₂_congr fun u hu =>
    ⟨fun hb => ⟨u, hb, le_rfl⟩, fun ⟨v, hv, hvu⟩ => bad_upper R S hvu hv⟩

theorem monomial_mem_ideal (R : E → E → Prop) (S : Set E)
    {u : Exp E} (hu : ¬ Allowed R S u) (c : K) :
    MvPolynomial.monomial u c ∈ ideal R S := by
  change MvPolynomial.monomial u c ∈ MvPolynomial.restrictSupport K (bad R S)
  exact (MvPolynomial.monomial_mem_restrictSupport K).mpr (Or.inl hu)

theorem ideal_eq_sup (R : E → E → Prop) (S : Set E) :
    ideal R S (K := K) = ideal R ∅ ⊔ Ideal.span (MvPolynomial.X '' S) := by
  classical
  apply le_antisymm
  · rw [ideal_eq_span]
    apply Ideal.span_le.mpr
    rintro _ ⟨u, hu, rfl⟩
    by_cases hvalid : Valid R u
    · obtain ⟨i, hiS, hui⟩ : ∃ i ∈ S, u i ≠ 0 := by
        simpa only [bad, Set.mem_ofPred_eq, Allowed, hvalid, true_and, not_forall, exists_prop] using hu
      apply Submodule.mem_sup_right
      apply MvPolynomial.mem_ideal_span_X_image.mpr
      intro v hv
      have hvu : v = u := by simpa only [MvPolynomial.support_monomial, one_ne_zero,
        ite_false, Finset.mem_singleton] using hv
      exact ⟨i, hiS, hvu ▸ hui⟩
    · exact Submodule.mem_sup_left (monomial_mem_ideal R ∅ (fun h => hvalid h.1) 1)
  · apply sup_le
    · exact ideal_mono R (Set.empty_subset S)
    · apply Ideal.span_le.mpr
      rintro _ ⟨i, hi, rfl⟩
      apply monomial_mem_ideal R S
      intro h
      have hz := h.2 i hi
      simpa using hz

def pairs (R : E → E → Prop) : Set (Exp E) :=
  {u | ∃ i j, ¬ R i j ∧ u = Finsupp.single i 1 + Finsupp.single j 1}

theorem pair_le {i j : E} (hij : i ≠ j) {u : Exp E}
    (hi : u i ≠ 0) (hj : u j ≠ 0) :
    Finsupp.single i 1 + Finsupp.single j 1 ≤ u := by
  classical
  intro a
  by_cases hai : a = i
  · subst a
    simpa [Finsupp.single_apply, hij, Ne.symm hij] using Nat.one_le_iff_ne_zero.mpr hi
  · by_cases haj : a = j
    · subst a
      simpa [Finsupp.single_apply, hij, Ne.symm hij] using Nat.one_le_iff_ne_zero.mpr hj
    · simp [Finsupp.single_apply, hai, haj, Ne.symm hai, Ne.symm haj]

theorem not_valid_iff_pair_le {R : E → E → Prop} (hrefl : ∀ i, R i i) (u : Exp E) :
    ¬ Valid R u ↔ ∃ v ∈ pairs R, v ≤ u := by
  classical
  constructor
  · intro h
    obtain ⟨i, hi, j, hj, hij⟩ : ∃ i, u i ≠ 0 ∧ ∃ j, u j ≠ 0 ∧ ¬ R i j := by
      simpa only [Valid, not_forall, not_imp, exists_prop] using h
    have hne : i ≠ j := fun h => hij (h ▸ hrefl i)
    exact ⟨_, ⟨i, j, hij, rfl⟩, pair_le hne hi hj⟩
  · rintro ⟨v, ⟨i, j, hij, rfl⟩, hle⟩ hv
    have hi : u i ≠ 0 := by
      have h := hle i
      simp only [Finsupp.add_apply, Finsupp.single_eq_same] at h
      omega
    have hj : u j ≠ 0 := by
      have h := hle j
      simp only [Finsupp.add_apply, Finsupp.single_eq_same] at h
      omega
    exact hij (hv i hi j hj)

/-- The defining ideal is literally the ideal generated by incompatible
quadratic monomials. -/
theorem ideal_empty_eq_quadratics {R : E → E → Prop} (hrefl : ∀ i, R i i) :
    ideal R ∅ (K := K) =
      Ideal.span ((fun u => MvPolynomial.monomial u (1 : K)) '' pairs R) := by
  ext f
  rw [mem_ideal_iff, MvPolynomial.mem_ideal_span_monomial_image]
  apply forall₂_congr
  intro u hu
  simpa only [Allowed, Set.mem_empty_iff_false, IsEmpty.forall_iff, implies_true,
    and_true] using not_valid_iff_pair_le hrefl u

theorem ideal_empty_eq_products {R : E → E → Prop} (hrefl : ∀ i, R i i) :
    ideal R ∅ (K := K) =
      Ideal.span {f : MvPolynomial E K | ∃ i j, ¬ R i j ∧ f = MvPolynomial.X i * MvPolynomial.X j} := by
  rw [ideal_empty_eq_quadratics hrefl]
  congr 1
  ext f
  constructor
  · rintro ⟨u, ⟨i, j, hij, rfl⟩, rfl⟩
    exact ⟨i, j, hij, by simp [MvPolynomial.X]⟩
  · rintro ⟨i, j, hij, rfl⟩
    exact ⟨_, ⟨i, j, hij, rfl⟩, by simp [MvPolynomial.X]⟩

def neighbors (R : E → E → Prop) (j : E) : Set E := {i | ¬ R i j}

theorem add_single_ne_zero_iff (u : Exp E) (i j : E) :
    (u + Finsupp.single j 1 : Exp E) i ≠ 0 ↔ u i ≠ 0 ∨ i = j := by
  classical
  by_cases h : i = j
  · subst i; simp
  · simp [Finsupp.single_apply, h, Ne.symm h]

theorem allowed_add_single_iff {R : E → E → Prop} (hrefl : ∀ i, R i i)
    (hsymm : ∀ {i j}, R i j → R j i) {S : Set E} {j : E} (hj : j ∉ S) (u : Exp E) :
    Allowed R S (u + Finsupp.single j 1) ↔ Allowed R (S ∪ neighbors R j) u := by
  classical
  constructor
  · intro h
    have hu : Allowed R S u := allowed_of_le (le_add_right le_rfl) h
    refine ⟨hu.1, ?_⟩
    intro i hi
    rcases hi with hi | hi
    · exact hu.2 i hi
    · by_contra hui
      exact hi (h.1 i ((add_single_ne_zero_iff u i j).mpr (Or.inl hui))
        j ((add_single_ne_zero_iff u j j).mpr (Or.inr rfl)))
  · intro h
    refine ⟨?_, ?_⟩
    · intro a ha b hb
      rcases (add_single_ne_zero_iff u a j).mp ha with hau | haj
      · rcases (add_single_ne_zero_iff u b j).mp hb with hbu | hbj
        · exact h.1 a hau b hbu
        · subst b
          by_contra hab
          exact hau (h.2 a (Or.inr hab))
      · subst a
        rcases (add_single_ne_zero_iff u b j).mp hb with hbu | hbj
        · apply hsymm
          by_contra hbj'
          exact hbu (h.2 b (Or.inr hbj'))
        · subst b
          exact hrefl j
    · intro i hi
      have hij : i ≠ j := fun h => hj (h ▸ hi)
      simp [Finsupp.single_apply, h.2 i (Or.inl hi), hij, Ne.symm hij]

theorem mul_X_mem_ideal_iff {R : E → E → Prop} (hrefl : ∀ i, R i i)
    (hsymm : ∀ {i j}, R i j → R j i) {S : Set E} {j : E} (hj : j ∉ S) (f : MvPolynomial E K) :
    f * MvPolynomial.X j ∈ ideal R S ↔ f ∈ ideal R (S ∪ neighbors R j) := by
  classical
  rw [mem_ideal_iff, mem_ideal_iff, MvPolynomial.support_mul_X]
  constructor
  · intro h u hu
    exact fun hg => h _ (Finset.mem_map.mpr ⟨u, hu, rfl⟩)
      ((allowed_add_single_iff hrefl hsymm hj u).mpr hg)
  · intro h v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hv
    exact fun hg => h u hu ((allowed_add_single_iff hrefl hsymm hj u).mp hg)

theorem ideal_colon_variable {R : E → E → Prop} (hrefl : ∀ i, R i i)
    (hsymm : ∀ {i j}, R i j → R j i) {S : Set E} {j : E} (hj : j ∉ S) :
    (ideal R S (K := K)).colon {MvPolynomial.X j} = ideal R (S ∪ neighbors R j) := by
  ext f
  rw [Submodule.mem_colon_singleton, smul_eq_mul]
  exact mul_X_mem_ideal_iff hrefl hsymm hj f

#print axioms ideal_empty_eq_products
#print axioms ideal_colon_variable

end Unimodular.FlagKoszul

#check Unimodular.FlagKoszul.ideal_colon_variable
