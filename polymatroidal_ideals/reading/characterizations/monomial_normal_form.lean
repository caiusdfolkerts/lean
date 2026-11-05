import Characterizations.MainLocalization
import Characterizations.PureDegree
import Characterizations.IntegralClosure
import CommAlg.Polymatroid.IdealBridge
import Mathlib.RingTheory.Polynomial.Basic

/-! # Every monomial ideal has its unique finite minimal monomial presentation

The input notion allows an arbitrary, possibly infinite, set of exponents. The
finite-antichain presentation is proved using Hilbert's basis theorem, not included
as an assumption in the notion of monomial ideal.
-/
noncomputable section
set_option maxHeartbeats 600000
namespace Characterizations
open Classical Finset CommAlg CommAlg.Polymatroid MvPolynomial
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

/-- The ordinary meaning of a monomial ideal, permitting an arbitrary exponent set. -/
def IsMonomialIdeal (I : Ideal (MvPolynomial V k)) : Prop :=
  ∃ A : Set (Exponent V), I = Ideal.span ((fun a => monomial a (1 : k)) '' A)

lemma monomialIdeal_isMonomial (B : Family V) : IsMonomialIdeal (monomialIdeal k B) :=
  ⟨(B : Set (Exponent V)), rfl⟩

/-- Arbitrary monomial spans have finite monomial generators. -/
lemma IsMonomialIdeal.exists_finite {I : Ideal (MvPolynomial V k)} (hI : IsMonomialIdeal I) :
    ∃ B : Family V, I = monomialIdeal k B := by
  obtain ⟨A, rfl⟩ := hI
  let f : Exponent V → MvPolynomial V k := fun a => monomial a (1 : k)
  have hfg : (Ideal.span (f '' A)).FG := Ideal.fg_of_isNoetherianRing _
  obtain ⟨Q, hQA, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (f '' A)).mp hfg
  have hq : ∀ q : Q, ∃ a ∈ A, f a = q.val := fun q => hQA q.property
  let b : Q → Exponent V := fun q => (hq q).choose
  have hbA : ∀ q, b q ∈ A := fun q => (hq q).choose_spec.1
  have hbeq : ∀ q, f (b q) = q.val := fun q => (hq q).choose_spec.2
  let B : Family V := Finset.univ.image b
  refine ⟨B, ?_⟩
  have hset : f '' (B : Set (Exponent V)) = (Q : Set (MvPolynomial V k)) := by
    ext p
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp ha
      rw [hbeq]
      exact q.property
    · intro hp
      refine ⟨b ⟨p, hp⟩, Finset.mem_image.mpr ⟨⟨p, hp⟩, mem_univ _, rfl⟩, hbeq _⟩
  change Ideal.span (f '' A) = Ideal.span (f '' (B : Set (Exponent V)))
  rw [hset]
  exact hspan

/-- Every monomial ideal has a finite antichain of actual monomial generators. -/
lemma IsMonomialIdeal.exists_antichain {I : Ideal (MvPolynomial V k)} (hI : IsMonomialIdeal I) :
    ∃ B : Family V, Antichain B ∧ I = monomialIdeal k B := by
  obtain ⟨B, hB⟩ := hI.exists_finite
  exact ⟨minimalFamily B, minimalFamily_antichain B,
    hB.trans (monomialIdeal_minimalFamily k B).symm⟩

lemma antichain_generators_unique {B C : Family V} (hB : Antichain B) (hC : Antichain C)
    (hI : monomialIdeal k B = monomialIdeal k C) : B = C := by
  apply family_eq_of_contains_iff hB hC
  intro a
  rw [← monomial_mem_iff (k := k), ← monomial_mem_iff (k := k), hI]

/-- The unique finite family of minimal monomial exponents of a literal ideal. -/
def monomialGenerators (I : Ideal (MvPolynomial V k)) (hI : IsMonomialIdeal I) : Family V :=
  hI.exists_antichain.choose

lemma monomialGenerators_antichain (I : Ideal (MvPolynomial V k)) (hI : IsMonomialIdeal I) :
    Antichain (monomialGenerators I hI) := hI.exists_antichain.choose_spec.1

lemma monomialGenerators_ideal (I : Ideal (MvPolynomial V k)) (hI : IsMonomialIdeal I) :
    monomialIdeal k (monomialGenerators I hI) = I := hI.exists_antichain.choose_spec.2.symm

lemma monomialGenerators_eq {I : Ideal (MvPolynomial V k)} (hI : IsMonomialIdeal I)
    {B : Family V} (hB : Antichain B) (he : I = monomialIdeal k B) :
    monomialGenerators I hI = B :=
  antichain_generators_unique (monomialGenerators_antichain I hI) hB
    ((monomialGenerators_ideal I hI).trans he)

lemma monomialGenerators_nonempty {I : Ideal (MvPolynomial V k)} (hI : IsMonomialIdeal I)
    (hne : I ≠ ⊥) : (monomialGenerators I hI).Nonempty := by
  by_contra hn
  have he := Finset.not_nonempty_iff_eq_empty.mp hn
  apply hne
  rw [← monomialGenerators_ideal I hI, he]
  simp [monomialIdeal]

/-- The chosen presentation is exactly the divisibility-minimal monomials in I. -/
lemma mem_monomialGenerators_iff (I : Ideal (MvPolynomial V k)) (hI : IsMonomialIdeal I)
    (a : Exponent V) :
    a ∈ monomialGenerators I hI ↔ monomial a (1 : k) ∈ I ∧
      ∀ b : Exponent V, b ≤ a → monomial b (1 : k) ∈ I → b = a := by
  have hanti := monomialGenerators_antichain I hI
  have hm : ∀ b : Exponent V, monomial b (1 : k) ∈ I ↔ Contains (monomialGenerators I hI) b := by
    intro b
    simpa only [monomialGenerators_ideal I hI] using
      (monomial_mem_iff (k := k) (monomialGenerators I hI) b)
  simp only [hm]
  constructor
  · intro ha
    refine ⟨⟨a, ha, le_rfl⟩, ?_⟩
    rintro b hba ⟨c, hc, hcb⟩
    have hca := hanti c hc a ha (hcb.trans hba)
    exact le_antisymm hba (hca ▸ hcb)
  · rintro ⟨⟨b, hb, hba⟩, hmin⟩
    have he := hmin b hba ⟨b, hb, le_rfl⟩
    exact he ▸ hb

lemma isPolymatroidalIdeal_iff_generators {I : Ideal (MvPolynomial V k)} (hI : IsMonomialIdeal I) :
    IsPolymatroidalIdeal I ↔ IsPolymatroidal (monomialGenerators I hI) := by
  constructor
  · rintro ⟨B, hp, he⟩
    rw [monomialGenerators_eq hI hp.1.choose_spec.antichain he]
    exact hp
  · intro hp
    exact ⟨monomialGenerators I hI, hp, (monomialGenerators_ideal I hI).symm⟩

/-- Theorem 1.1(A), now quantified over an arbitrary literal monomial ideal, including zero. -/
theorem monomialIdeal_polymatroidal_iff_local_linear {I : Ideal (MvPolynomial V k)}
    (hI : IsMonomialIdeal I) :
    IsPolymatroidalIdeal I ↔
      ∀ U : Finset V, HasLinearResolution (monomialLocalization k I U) := by
  by_cases hzero : I = ⊥
  · subst I
    constructor
    · intro _ U
      rw [monomialLocalization, Ideal.map_bot]
      exact ⟨0, ⟨zeroLinearResolution 0⟩⟩
    · intro _
      exact isPolymatroidalIdeal_bot
  · rw [isPolymatroidalIdeal_iff_generators hI,
      polymatroidal_iff_local_linearResolutions (k := k) (monomialGenerators_nonempty hI hzero)
        (monomialGenerators_antichain I hI), monomialGenerators_ideal I hI]

/-- Theorem 1.1(B) / Corollary 3.10 on the actual minimal generators of an
arbitrary literal monomial ideal, without an equigeneration assumption. -/
theorem monomialIdeal_polymatroidal_iff_universal_quotients {I : Ideal (MvPolynomial V k)}
    (hI : IsMonomialIdeal I) :
    IsPolymatroidalIdeal I ↔ ∀ o : VariableOrder V,
      HasLinearQuotients k (monomialGenerators I hI) (variableRevlex o) := by
  rw [isPolymatroidalIdeal_iff_generators hI]
  exact polymatroidal_iff_universal_pure_revlex (monomialGenerators_antichain I hI)

/-- Theorem 2.11 / Corollary 2.12's integrality form for literal monomial ideals. -/
theorem monomialIdeal_polymatroidal_iff_integrallyClosed {I : Ideal (MvPolynomial V k)}
    (hI : IsMonomialIdeal I) (hne : I ≠ ⊥) :
    IsPolymatroidalIdeal I ↔ IsIntegrallyClosedIdeal I ∧
      ∀ U : Finset V, ∃ d, Equigenerated (localFamily (monomialGenerators I hI) U) d := by
  rw [isPolymatroidalIdeal_iff_generators hI,
    polymatroidal_iff_integrallyClosed_localEquigenerated (k := k) (monomialGenerators_nonempty hI hne)
      (monomialGenerators_antichain I hI), monomialGenerators_ideal I hI, locallyEquigenerated_iff]

/-- The complete integral-closure ideal in Theorem 2.11, for an arbitrary literal I. -/
theorem monomialIdeal_integralClosure {I : Ideal (MvPolynomial V k)}
    (hI : IsMonomialIdeal I) (hne : I ≠ ⊥)
    (hl : LocallyEquigenerated (monomialGenerators I hI)) {d : ℕ}
    (hd : Equigenerated (monomialGenerators I hI) d) :
    {f : MvPolynomial V k | IntegralOverIdeal I f} =
      (monomialIdeal k (lowerBaseFamily (lowerRank (monomialGenerators I hI)) d) : Set (MvPolynomial V k)) := by
  simpa only [monomialGenerators_ideal I hI] using integralClosure_set_eq
    (k := k) (monomialGenerators_nonempty hI hne) (monomialGenerators_antichain I hI) hl hd

end Characterizations
