module
public import shared_results.part004
public import Mathlib.Tactic.Ring
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Order.Prod.Lex.Basic

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.MonicPairCriterion -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

/-!
# A monic pair criterion with strict leading bounds

The polynomial identities used for maximal minors have all summands strictly
below the cancelled common leading monomial. This is enough for Buchberger's
argument; it does not require a pre-existing division algorithm for the minors.
The bounded-span proof is the standard leading-term descent, over every
nontrivial commutative ring. Its definitions are public so that the actual
Laplace identities can be inserted directly.
-/

noncomputable section
namespace FourPapers.MonicPairCriterion
open Classical MvPolynomial
variable {V R : Type*} [CommRing R] [Nontrivial R]
variable (m : MonomialOrder V) (G : Set (MvPolynomial V R))

def productSpan (s : Set m.syn) : Submodule R (MvPolynomial V R) :=
  Submodule.span R {p | ∃ b ∈ G, ∃ a, m.toSyn (a + m.degree b) ∈ s ∧ p = monomial a 1 * b}

lemma monomial_mem_productSpan {s : Set m.syn} {b : MvPolynomial V R}
    (hb : b ∈ G) {a : V →₀ ℕ} (ha : m.toSyn (a + m.degree b) ∈ s) :
    monomial a 1 * b ∈ productSpan m G s :=
  Submodule.subset_span ⟨b, hb, a, ha, rfl⟩

lemma productSpan_mono {s t : Set m.syn} (h : s ⊆ t) :
    productSpan m G s ≤ productSpan m G t :=
  Submodule.span_mono (fun _ ⟨b, hb, a, ha, hp⟩ => ⟨b, hb, a, h ha, hp⟩)

lemma mem_productSpan_self {b : MvPolynomial V R} (hb : b ∈ G) :
    b ∈ productSpan m G (Set.Iic (m.toSyn (m.degree b))) := by
  simpa using monomial_mem_productSpan m G (s := Set.Iic _) hb (a := 0) (by simp)

lemma monomial_mul_mem_productSpan {d : m.syn} {p : MvPolynomial V R}
    (hp : p ∈ productSpan m G (Set.Iic d)) (c : V →₀ ℕ) (r : R) :
    monomial c r * p ∈ productSpan m G (Set.Iic (m.toSyn c + d)) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨b, hb, a, had, rfl⟩ := hp
    have he : monomial c r * (monomial a 1 * b) = r • (monomial (c + a) 1 * b) := by
      simp only [smul_eq_C_mul, ← mul_assoc, C_mul_monomial, monomial_mul_monomial, mul_one]
    rw [he]
    refine Submodule.smul_mem _ _ (monomial_mem_productSpan m G hb ?_)
    rw [Set.mem_Iic, add_assoc, map_add]
    simpa only [add_comm] using (add_le_add_left had (m.toSyn c))
  | zero => simp
  | add x y hx hy ihx ihy => rw [mul_add]; exact add_mem ihx ihy
  | smul r' x hx ih => rw [mul_smul_comm]; exact Submodule.smul_mem _ r' ih

lemma monomial_mul_mem_productSpan_lt {d : m.syn} {p : MvPolynomial V R}
    (hp : p ∈ productSpan m G (Set.Iio d)) (c : V →₀ ℕ) (r : R) :
    monomial c r * p ∈ productSpan m G (Set.Iio (m.toSyn c + d)) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨b, hb, a, had, rfl⟩ := hp
    have he : monomial c r * (monomial a 1 * b) = r • (monomial (c + a) 1 * b) := by
      simp only [smul_eq_C_mul, ← mul_assoc, C_mul_monomial, monomial_mul_monomial, mul_one]
    rw [he]
    refine Submodule.smul_mem _ _ (monomial_mem_productSpan m G hb ?_)
    rw [Set.mem_Iio, add_assoc, map_add]
    simpa only [add_comm] using (add_lt_add_left had (m.toSyn c))
  | zero => simp
  | add x y hx hy ihx ihy => rw [mul_add]; exact add_mem ihx ihy
  | smul r' x hx ih => rw [mul_smul_comm]; exact Submodule.smul_mem _ r' ih

lemma mul_mem_productSpan {d : m.syn} {p : MvPolynomial V R}
    (hp : p ∈ productSpan m G (Set.Iic d)) (q : MvPolynomial V R) :
    q * p ∈ productSpan m G (Set.Iic (m.toSyn (m.degree q) + d)) := by
  have hq : q * p = ∑ c ∈ q.support, monomial c (q.coeff c) * p := by
    rw [← Finset.sum_mul, ← q.as_sum]
  rw [hq]
  refine Submodule.sum_mem _ (fun c hc => ?_)
  have hcd : m.toSyn c + d ≤ m.toSyn (m.degree q) + d :=
    add_le_add (m.le_degree hc) le_rfl
  exact productSpan_mono m G (Set.Iic_subset_Iic.mpr hcd)
    (monomial_mul_mem_productSpan m G hp c (q.coeff c))

lemma exists_mem_productSpan {f : MvPolynomial V R} (hf : f ∈ Ideal.span G) :
    ∃ d, f ∈ productSpan m G (Set.Iic d) := by
  induction hf using Submodule.span_induction with
  | mem b hb => exact ⟨_, mem_productSpan_self m G hb⟩
  | zero => exact ⟨0, zero_mem _⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨d₁, h₁⟩ := ihx
    obtain ⟨d₂, h₂⟩ := ihy
    exact ⟨d₁ ⊔ d₂, add_mem
      (productSpan_mono m G (Set.Iic_subset_Iic.mpr le_sup_left) h₁)
      (productSpan_mono m G (Set.Iic_subset_Iic.mpr le_sup_right) h₂)⟩
  | smul q x hx ih =>
    obtain ⟨d, hd⟩ := ih
    exact ⟨_, mul_mem_productSpan m G hd q⟩

lemma zero_or_smaller_productSpan {d : m.syn} {f : MvPolynomial V R}
    (hf : f ∈ productSpan m G (Set.Iio d)) :
    f = 0 ∨ ∃ d' < d, f ∈ productSpan m G (Set.Iic d') := by
  induction hf using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨b, hb, a, had, rfl⟩ := hp
    exact Or.inr ⟨_, had, monomial_mem_productSpan m G hb le_rfl⟩
  | zero => exact Or.inl rfl
  | add x y hx hy ihx ihy =>
    rcases ihx with rfl | ⟨d₁, hd₁, h₁⟩
    · simpa only [zero_add] using ihy
    rcases ihy with rfl | ⟨d₂, hd₂, h₂⟩
    · exact Or.inr ⟨d₁, hd₁, by simpa only [add_zero] using h₁⟩
    exact Or.inr ⟨d₁ ⊔ d₂, max_lt hd₁ hd₂, add_mem
      (productSpan_mono m G (Set.Iic_subset_Iic.mpr le_sup_left) h₁)
      (productSpan_mono m G (Set.Iic_subset_Iic.mpr le_sup_right) h₂)⟩
  | smul r x hx ih =>
    rcases ih with rfl | ⟨d', hd', h'⟩
    · exact Or.inl (smul_zero r)
    · exact Or.inr ⟨d', hd', Submodule.smul_mem _ r h'⟩

lemma exists_product_above_coefficient {s : Set m.syn} {f : MvPolynomial V R}
    (hf : f ∈ productSpan m G s) {e : V →₀ ℕ} (he : f.coeff e ≠ 0) :
    ∃ b ∈ G, b ≠ 0 ∧ ∃ a, m.toSyn (a + m.degree b) ∈ s ∧
      m.toSyn e ≤ m.toSyn (a + m.degree b) := by
  by_contra! H
  have hle : productSpan m G s ≤ LinearMap.ker (lcoeff R e) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, hb, a, has, rfl⟩
    rcases eq_or_ne b 0 with rfl | hb0
    · simp
    simpa using m.coeff_eq_zero_of_lt
      ((m.toSyn_degree_monomial_mul_le a 1 b).trans_lt (H b hb hb0 a has))
  exact he (by simpa using hle hf)

def normalizedDifference (D : V →₀ ℕ) (a b : MvPolynomial V R) : MvPolynomial V R :=
  monomial (D - m.degree a) 1 * a - monomial (D - m.degree b) 1 * b

@[simp] lemma normalizedDifference_self (D : V →₀ ℕ) (a : MvPolynomial V R) :
    normalizedDifference m D a a = 0 := sub_self _

lemma normalizedDifference_trans (D : V →₀ ℕ) (a b c : MvPolynomial V R) :
    normalizedDifference m D a c = normalizedDifference m D a b + normalizedDifference m D b c := by
  unfold normalizedDifference
  abel

lemma normalizedDifference_symm (D : V →₀ ℕ) (a b : MvPolynomial V R) :
    normalizedDifference m D a b = - normalizedDifference m D b a := by
  unfold normalizedDifference
  abel

lemma normalizedDifference_scale (D C : V →₀ ℕ) (a b : MvPolynomial V R)
    (ha : m.degree a ≤ C) (hb : m.degree b ≤ C) (hC : C ≤ D) :
    normalizedDifference m D a b =
      monomial (D-C) 1 * normalizedDifference m C a b := by
  unfold normalizedDifference
  rw [mul_sub, ← mul_assoc, ← mul_assoc, monomial_mul_monomial, monomial_mul_monomial,
    tsub_add_tsub_cancel hC ha, tsub_add_tsub_cancel hC hb]
  simp only [one_mul]

lemma normalizedDifference_mem_of_smaller_bound (D C : V →₀ ℕ)
    (a b : MvPolynomial V R) (ha : m.degree a ≤ C) (hb : m.degree b ≤ C) (hC : C ≤ D)
    (h : normalizedDifference m C a b ∈ productSpan m G (Set.Iio (m.toSyn C))) :
    normalizedDifference m D a b ∈ productSpan m G (Set.Iio (m.toSyn D)) := by
  rw [normalizedDifference_scale m D C a b ha hb hC]
  have hh := monomial_mul_mem_productSpan_lt m G h (D-C) 1
  rwa [← map_add, tsub_add_cancel_of_le hC] at hh

lemma tail_support_lt (f : MvPolynomial V R) (hf : m.leadingCoeff f = 1)
    {a : V →₀ ℕ} (ha : a ∈ (f - monomial (m.degree f) 1).support) :
    m.toSyn a < m.toSyn (m.degree f) := by
  have ha' := mem_support_iff.mp ha
  have hne : a ≠ m.degree f := by
    intro he
    subst a
    apply ha'
    rw [coeff_sub, coeff_monomial, if_pos rfl, ← MonomialOrder.leadingCoeff, hf, sub_self]
  have hamem : a ∈ f.support := by
    apply mem_support_iff.mpr
    simpa only [coeff_sub, coeff_monomial, if_neg (Ne.symm hne), sub_zero] using ha'
  exact lt_of_le_of_ne (m.le_degree hamem) (m.toSyn.injective.ne hne)

lemma polynomial_mul_mem_productSpan_lt (q b : MvPolynomial V R) (hb : b ∈ G)
    (D : V →₀ ℕ)
    (hq : ∀ a ∈ q.support, m.toSyn (a + m.degree b) < m.toSyn D) :
    q * b ∈ productSpan m G (Set.Iio (m.toSyn D)) := by
  have he : q * b = ∑ a ∈ q.support, q.coeff a • (monomial a 1 * b) := by
    calc
      q * b = ∑ a ∈ q.support, monomial a (q.coeff a) * b := by
        rw [← Finset.sum_mul, ← q.as_sum]
      _ = ∑ a ∈ q.support, q.coeff a • (monomial a 1 * b) := by
        apply Finset.sum_congr rfl
        intro a _
        simp only [smul_eq_C_mul, ← mul_assoc, C_mul_monomial, mul_one]
  rw [he]
  apply Submodule.sum_mem
  intro a ha
  exact Submodule.smul_mem _ _ (monomial_mem_productSpan m G hb (hq a ha))

/-- The coprime pair reduction is valid for arbitrary monic polynomials,
not only for binomials or over a field. -/
theorem coprime_pair_reduces (f g : MvPolynomial V R) (hf : f ∈ G) (hg : g ∈ G)
    (hfc : m.leadingCoeff f = 1) (hgc : m.leadingCoeff g = 1)
    (hcop : m.degree f ⊔ m.degree g = m.degree f + m.degree g)
    (D : V →₀ ℕ) (hfD : m.degree f ≤ D) (hgD : m.degree g ≤ D) :
    normalizedDifference m D f g ∈ productSpan m G (Set.Iio (m.toSyn D)) := by
  apply normalizedDifference_mem_of_smaller_bound m G D (m.degree f + m.degree g) f g
    le_self_add le_add_self (by rw [← hcop]; exact sup_le hfD hgD)
  have hf' := polynomial_mul_mem_productSpan_lt m G (f - monomial (m.degree f) 1) g hg
    (m.degree f + m.degree g) (fun a ha => by
      simpa only [map_add, add_comm] using add_lt_add_right (tail_support_lt m f hfc ha) (m.toSyn (m.degree g)))
  have hg' := polynomial_mul_mem_productSpan_lt m G (g - monomial (m.degree g) 1) f hf
    (m.degree f + m.degree g) (fun a ha => by
      simpa only [map_add, add_comm] using add_lt_add_right (tail_support_lt m g hgc ha) (m.toSyn (m.degree f)))
  have he : normalizedDifference m (m.degree f + m.degree g) f g =
      (f - monomial (m.degree f) 1) * g - (g - monomial (m.degree g) 1) * f := by
    rw [normalizedDifference, add_tsub_cancel_left, add_tsub_cancel_right]
    ring
  rw [he]
  exact sub_mem hf' hg'

def PairReduces : Prop :=
  ∀ a ∈ G, ∀ b ∈ G, ∀ D, m.degree a ≤ D → m.degree b ≤ D →
    normalizedDifference m D a b ∈ productSpan m G (Set.Iio (m.toSyn D))

lemma lower_productSpan_of_coefficient_zero
    (hG : ∀ g ∈ G, m.leadingCoeff g = 1) (hP : PairReduces m G)
    {D : V →₀ ℕ} {f : MvPolynomial V R}
    (hf : f ∈ productSpan m G (Set.Iic (m.toSyn D))) (hfD : f.coeff D = 0) :
    f ∈ productSpan m G (Set.Iio (m.toSyn D)) := by
  by_cases htop : ∃ b₀ ∈ G, m.degree b₀ ≤ D
  swap
  · simp only [not_exists, not_and] at htop
    refine Submodule.span_le.mpr ?_ hf
    rintro _ ⟨b, hb, a, had, rfl⟩
    refine monomial_mem_productSpan m G hb (lt_of_le_of_ne had (fun h => ?_))
    exact htop b hb (m.toSyn.injective h ▸ le_add_self)
  obtain ⟨b₀, hb₀, hb₀D⟩ := htop
  let q₀ := monomial (D - m.degree b₀) (1 : R) * b₀
  have hle : productSpan m G (Set.Iic (m.toSyn D)) ≤
      (productSpan m G (Set.Iio (m.toSyn D))).comap
        (LinearMap.id - (lcoeff R D).smulRight q₀) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, hb, a, had, rfl⟩
    change monomial a 1 * b - (monomial a 1 * b).coeff D • q₀ ∈
      productSpan m G (Set.Iio (m.toSyn D))
    by_cases he : a + m.degree b = D
    · have hbd : m.degree b ≤ D := he ▸ le_add_self
      have ha : a = D - m.degree b := by rw [← he, add_tsub_cancel_right]
      have hc : (monomial a (1 : R) * b).coeff D = 1 := by
        rw [← he, coeff_monomial_mul, one_mul, ← MonomialOrder.leadingCoeff, hG b hb]
      rw [hc, one_smul, ha]
      exact hP b hb b₀ hb₀ D hbd hb₀D
    · have hlt : m.toSyn (a + m.degree b) < m.toSyn D :=
        lt_of_le_of_ne had (m.toSyn.injective.ne he)
      rw [m.coeff_eq_zero_of_lt ((m.toSyn_degree_monomial_mul_le a 1 b).trans_lt hlt),
        zero_smul, sub_zero]
      exact monomial_mem_productSpan m G hb hlt
  simpa only [Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.smulRight_apply, lcoeff_apply, hfD, zero_smul, sub_zero] using hle hf

theorem exists_leading_divisor_of_productSpan
    (hG : ∀ g ∈ G, m.leadingCoeff g = 1) (hP : PairReduces m G)
    (d : m.syn) {f : MvPolynomial V R}
    (hfd : f ∈ productSpan m G (Set.Iic d)) (hf0 : f ≠ 0) :
    ∃ g ∈ G, g ≠ 0 ∧ m.degree g ≤ m.degree f := by
  induction d using WellFoundedLT.induction generalizing f with
  | ind d ih =>
    obtain ⟨b, hb, hb0, a, had, hfa⟩ :=
      exists_product_above_coefficient m G hfd (m.coeff_degree_ne_zero_iff.mpr hf0)
    by_cases he : m.toSyn (m.degree f) = d
    · have hh : a + m.degree b = m.degree f :=
        m.toSyn.injective (le_antisymm (he ▸ had) hfa)
      exact ⟨b, hb, hb0, hh ▸ le_add_self⟩
    · have hlt := lt_of_le_of_ne (hfa.trans had) he
      obtain ⟨D, rfl⟩ := m.toSyn.surjective d
      have hlow := lower_productSpan_of_coefficient_zero m G hG hP hfd
        (m.coeff_eq_zero_of_lt hlt)
      rcases zero_or_smaller_productSpan m G hlow with hz | ⟨d', hd', hf'⟩
      · exact (hf0 hz).elim
      · exact ih d' hd' hf' hf0

theorem exists_leading_divisor
    (hG : ∀ g ∈ G, m.leadingCoeff g = 1) (hP : PairReduces m G)
    {f : MvPolynomial V R} (hf : f ∈ Ideal.span G) (hf0 : f ≠ 0) :
    ∃ g ∈ G, g ≠ 0 ∧ m.degree g ≤ m.degree f := by
  obtain ⟨d, hfd⟩ := exists_mem_productSpan m G hf
  exact exists_leading_divisor_of_productSpan m G hG hP d hfd hf0

/-- Every strict pair reduction is proved at the actual polynomial level.
The resulting assertion is the ordinary ideal Gröbner-basis statement. -/
theorem isGroebnerBasis_of_pairReduces
    (hG : ∀ g ∈ G, m.leadingCoeff g = 1) (hP : PairReduces m G) :
    m.IsGroebnerBasis G (Ideal.span G) := by
  apply (MonomialOrder.isGroebnerBasis_iff_forall_exists_degree_le_degree
    (fun g hg _ => by rw [hG g hg]; exact isUnit_one)).mpr
  exact ⟨Ideal.subset_span, fun f hf hf0 => exists_leading_divisor m G hG hP hf hf0⟩

end FourPapers.MonicPairCriterion
end

#print axioms FourPapers.MonicPairCriterion.isGroebnerBasis_of_pairReduces

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FacetDeterminants -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FourPapers.Sublattice
open Classical MvPolynomial CommAlg.Polymatroid
universe u
variable {d N : ℕ} {k : Type u} [CommRing k]

def facetOrderedVariableEquiv :
    FiniteVariable.{u} (UnitIntervalRows d N) ≃ Lex (Fin (d+1) × ULift.{u} (Fin N)) where
  toFun v := toLex (v.1, v.2)
  invFun v := ⟨(ofLex v).1, (ofLex v).2⟩
  left_inv v := by cases v; rfl
  right_inv v := by cases v; rfl

def facetLexOrder : MonomialOrder (FiniteVariable.{u} (UnitIntervalRows d N)) := by
  letI : WellFoundedGT (Lex (Fin (d+1) × ULift.{u} (Fin N))) := Finite.to_wellFoundedGT
  let m : MonomialOrder (Lex (Fin (d+1) × ULift.{u} (Fin N))) := MonomialOrder.lex
  have hd : Monotone (Finsupp.domCongr facetOrderedVariableEquiv :
      (FiniteVariable.{u} (UnitIntervalRows d N) →₀ ℕ) →
        (Lex (Fin (d+1) × ULift.{u} (Fin N)) →₀ ℕ)) := by
    intro a b hab v
    simpa only [Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply] using
      hab (facetOrderedVariableEquiv.symm v)
  exact {
    syn := m.syn
    addCommMonoidSyn := m.addCommMonoidSyn
    linearOrderSyn := m.linearOrderSyn
    isOrderedAddMonoid_syn := m.isOrderedAddMonoid_syn
    wellFoundedLT_syn := m.wellFoundedLT_syn
    toSyn := (Finsupp.domCongr facetOrderedVariableEquiv).trans m.toSyn
    toSyn_monotone := m.toSyn_monotone.comp hd
  }

lemma facetLexRowExponent_apply (a : (Fin (d+1) → Fin N))
    (r : Fin (d+1)) (j : Fin N) :
    (Finsupp.domCongr facetOrderedVariableEquiv (finiteRowExponent (UnitIntervalRows d N) a))
      (toLex (r, ULift.up j)) = if a r = j then 1 else 0 := by
  change finiteRowExponent (UnitIntervalRows d N) a ⟨r, ULift.up j⟩ = _
  exact finiteRowExponent_apply a r j

/-- Lexicographic comparison of diagonal monomials, proved independently of
the unrelated order used to orient the exterior algebra. -/
lemma facetRowExponent_order {a b : (Fin (d+1) → Fin N)}
    (r : Fin (d+1)) (hprev : ∀ i, i < r → a i = b i) (hr : a r < b r) :
    facetLexOrder.toSyn (finiteRowExponent (UnitIntervalRows d N) b) <
      facetLexOrder.toSyn (finiteRowExponent (UnitIntervalRows d N) a) := by
  change toLex (Finsupp.domCongr facetOrderedVariableEquiv (finiteRowExponent _ b)) <
    toLex (Finsupp.domCongr facetOrderedVariableEquiv (finiteRowExponent _ a))
  rw [Finsupp.Lex.lt_iff]
  simp only [ofLex_toLex]
  refine ⟨toLex (r, ULift.up (a r)), ?_, ?_⟩
  · intro v hv
    obtain ⟨⟨s, ⟨j⟩⟩, rfl⟩ := toLex.surjective v
    rcases Prod.Lex.toLex_lt_toLex.mp hv with hs | ⟨hs, hj⟩
    · rw [facetLexRowExponent_apply, facetLexRowExponent_apply, hprev s hs]
    · change s = r at hs
      subst s
      change j < a r at hj
      simp only [facetLexRowExponent_apply, if_neg (Ne.symm hj.ne),
        if_neg (Ne.symm (hj.trans hr).ne)]
  · simp only [facetLexRowExponent_apply, if_neg (Ne.symm hr.ne), if_pos rfl]
    decide

lemma permutation_first_moved {q : ℕ} (σ : Equiv.Perm (Fin q)) (hσ : σ ≠ 1) :
    ∃ r, (∀ i, i < r → σ i = i) ∧ r < σ r := by
  let S := (Finset.univ : Finset (Fin q)).filter (fun i => σ i ≠ i)
  have hS : S.Nonempty := by
    by_contra h
    apply hσ
    apply Equiv.ext
    intro i
    change σ i = i
    by_contra hi
    exact h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  let r := S.min' hS
  have hr : σ r ≠ r := (Finset.mem_filter.mp (Finset.min'_mem S hS)).2
  have hprev : ∀ i, i < r → σ i = i := by
    intro i hi
    by_contra hn
    have hri := Finset.min'_le S i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
    exact (not_le_of_gt hi) hri
  refine ⟨r, hprev, ?_⟩
  by_contra h
  have hle : σ r ≤ r := le_of_not_gt h
  rcases hle.eq_or_lt with he | he
  · exact hr he
  · exact hr (σ.injective (hprev (σ r) he))

def facetMinor (a : (Fin (d+1) → Fin N)) :
    MvPolynomial (FiniteVariable.{u} (UnitIntervalRows d N)) k :=
  Matrix.det (fun i j : Fin (d+1) => X ⟨i, ULift.up (a j)⟩)

def facetMinorTermExponent (a : (Fin (d+1) → Fin N))
    (σ : Equiv.Perm (Fin (d+1))) : Exponent (FiniteVariable.{u} (UnitIntervalRows d N)) :=
  ∑ i, Finsupp.single ⟨σ i, ULift.up (a i)⟩ 1

lemma facetMinorTermExponent_eq_row (a : (Fin (d+1) → Fin N))
    (σ : Equiv.Perm (Fin (d+1))) :
    facetMinorTermExponent.{u} a σ = finiteRowExponent (UnitIntervalRows d N) (a ∘ σ.symm) := by
  simpa only [facetMinorTermExponent, finiteRowExponent, Function.comp_apply,
    Equiv.symm_apply_apply] using
      (Equiv.sum_comp σ (fun i => Finsupp.single
        (⟨i, ULift.up (a (σ.symm i))⟩ : FiniteVariable.{u} (UnitIntervalRows d N)) 1))

@[simp] lemma facetMinorTermExponent_one (a : (Fin (d+1) → Fin N)) :
    facetMinorTermExponent a 1 = finiteRowExponent (UnitIntervalRows d N) a := by
  simp only [facetMinorTermExponent, finiteRowExponent, Equiv.Perm.one_apply]

lemma facetMinorTermExponent_lt_diagonal (a : (Fin (d+1) → Fin N))
    (ha : StrictMono a) (σ : Equiv.Perm (Fin (d+1))) (hσ : σ ≠ 1) :
    facetLexOrder.toSyn (facetMinorTermExponent a σ) <
      facetLexOrder.toSyn (finiteRowExponent (UnitIntervalRows d N) a) := by
  have hs : σ.symm ≠ 1 := by
    change σ⁻¹ ≠ 1
    exact inv_ne_one.mpr hσ
  obtain ⟨r, hprev, hr⟩ := permutation_first_moved σ.symm hs
  rw [facetMinorTermExponent_eq_row]
  exact facetRowExponent_order r (fun i hi => by simp [Function.comp_apply, hprev i hi])
    (ha hr)

lemma facetMinor_expansion (a : (Fin (d+1) → Fin N)) :
    facetMinor (k := k) a = ∑ σ : Equiv.Perm (Fin (d+1)),
      monomial (facetMinorTermExponent a σ) (Equiv.Perm.sign σ • (1 : k)) := by
  rw [facetMinor, Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _
  rw [facetMinorTermExponent, ← smul_monomial, MvPolynomial.monomial_sum_one]
  rfl

section Nontrivial
variable [Nontrivial k]

lemma facetMinor_diagonal_coefficient (a : (Fin (d+1) → Fin N))
    (ha : StrictMono a) :
    (facetMinor (k := k) a).coeff (finiteRowExponent (UnitIntervalRows d N) a) = 1 := by
  rw [facetMinor_expansion, coeff_sum, Finset.sum_eq_single (1 : Equiv.Perm (Fin (d+1)))]
  · simp only [facetMinorTermExponent_one, Equiv.Perm.sign_one, one_smul, coeff_monomial, ite_true]
  · intro σ _ hσ
    have hn : facetMinorTermExponent.{u} a σ ≠ finiteRowExponent (UnitIntervalRows d N) a :=
      fun he => (ne_of_lt (facetMinorTermExponent_lt_diagonal a ha σ hσ)) (congrArg facetLexOrder.toSyn he)
    simp [coeff_monomial, hn]
  · intro h
    exact (h (Finset.mem_univ _)).elim

lemma facetMinor_degree (a : (Fin (d+1) → Fin N)) (ha : StrictMono a) :
    facetLexOrder.degree (facetMinor (k := k) a) = finiteRowExponent (UnitIntervalRows d N) a := by
  apply facetLexOrder.toSyn.injective
  apply le_antisymm
  · apply facetLexOrder.degree_le_iff.mpr
    intro b hb
    by_contra h
    have hlt : facetLexOrder.toSyn (finiteRowExponent (UnitIntervalRows d N) a) <
        facetLexOrder.toSyn b := lt_of_not_ge h
    have hz : (facetMinor (k := k) a).coeff b = 0 := by
      rw [facetMinor_expansion, coeff_sum]
      apply Finset.sum_eq_zero
      intro σ _
      have hσ : facetLexOrder.toSyn (facetMinorTermExponent a σ) ≤
          facetLexOrder.toSyn (finiteRowExponent (UnitIntervalRows d N) a) := by
        by_cases he : σ = 1
        · simp only [he, facetMinorTermExponent_one, le_refl]
        · exact (facetMinorTermExponent_lt_diagonal a ha σ he).le
      have hn : facetMinorTermExponent.{u} a σ ≠ b := fun he =>
        (not_le_of_gt hlt) (he ▸ hσ)
      simp [coeff_monomial, hn]
    exact (mem_support_iff.mp hb) hz
  · apply facetLexOrder.le_degree
    exact mem_support_iff.mpr (by rw [facetMinor_diagonal_coefficient a ha]; exact one_ne_zero)

lemma facetMinor_leadingCoeff (a : (Fin (d+1) → Fin N)) (ha : StrictMono a) :
    facetLexOrder.leadingCoeff (facetMinor (k := k) a) = 1 := by
  rw [MonomialOrder.leadingCoeff, facetMinor_degree a ha, facetMinor_diagonal_coefficient a ha]

end Nontrivial
end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.facetMinor_degree
#print axioms FourPapers.Sublattice.facetMinor_leadingCoeff

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FacetLaplace -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FourPapers.Sublattice
open Classical MvPolynomial CommAlg.Polymatroid
universe u
variable {d N : ℕ} {k : Type u} [CommRing k]

def facetDelete (c : Fin (d+2) → Fin N) (j : Fin (d+2)) :
    (Fin (d+1) → Fin N) := c ∘ j.succAbove

lemma facetDelete_strictMono {c : Fin (d+2) → Fin N} (hc : StrictMono c) (j : Fin (d+2)) :
    StrictMono (facetDelete c j) := hc.comp (Fin.strictMono_succAbove j)

/-- Laplace expansion of a matrix with a repeated row. All signs and
determinants are literal, and no characteristic hypothesis is used. -/
theorem facet_laplace_relation (c : Fin (d+2) → Fin N) (r : Fin (d+1)) :
    ∑ j : Fin (d+2), (-1 : k) ^ j.val •
      (X (⟨r, ULift.up (c j)⟩ : FiniteVariable.{u} (UnitIntervalRows d N)) * facetMinor (k := k) (facetDelete c j)) = 0 := by
  let A : Matrix (Fin (d+2)) (Fin (d+2))
      (MvPolynomial (FiniteVariable.{u} (UnitIntervalRows d N)) k) :=
    fun i j => Fin.cases (X ⟨r, ULift.up (c j)⟩)
      (fun a : Fin (d+1) => X ⟨a, ULift.up (c j)⟩) i
  have hz : Matrix.det A = 0 := Matrix.det_zero_of_row_eq
    (Fin.succ_ne_zero r).symm (by funext j; rfl)
  rw [Matrix.det_succ_row_zero] at hz
  convert hz using 1
  apply Finset.sum_congr rfl
  intro j _
  change (-1 : k) ^ j.val • (X ⟨r, ULift.up (c j)⟩ * facetMinor (facetDelete c j)) =
    (-1 : MvPolynomial _ k) ^ j.val * X ⟨r, ULift.up (c j)⟩ * facetMinor (facetDelete c j)
  simp only [smul_eq_C_mul, map_pow, map_neg, map_one, mul_assoc]

def facetLaplaceExponent (c : Fin (d+2) → Fin N) (r : Fin (d+1)) (j : Fin (d+2)) :
    Exponent (FiniteVariable.{u} (UnitIntervalRows d N)) :=
  Finsupp.single ⟨r, ULift.up (c j)⟩ 1 +
    finiteRowExponent (UnitIntervalRows d N) (facetDelete c j)

lemma facetLexSingle_apply (r s : Fin (d+1)) (j h : Fin N) :
    (Finsupp.domCongr facetOrderedVariableEquiv
      (Finsupp.single (⟨r, ULift.up j⟩ : FiniteVariable.{u} (UnitIntervalRows d N)) 1))
      (toLex (s, ULift.up h)) = if r = s ∧ j = h then 1 else 0 := by
  change Finsupp.single (⟨r, ULift.up j⟩ : FiniteVariable.{u} (UnitIntervalRows d N)) 1
    ⟨s, ULift.up h⟩ = _
  by_cases hrs : r = s
  · subst s
    simp [Finsupp.single_apply]
  · have hv : (⟨r, ULift.up j⟩ : FiniteVariable.{u} (UnitIntervalRows d N)) ≠ ⟨s, ULift.up h⟩ :=
      fun he => hrs (congrArg Sigma.fst he)
    simp [Finsupp.single_apply, hrs, hv]

lemma facetLaplaceExponent_apply (c : Fin (d+2) → Fin N) (r s : Fin (d+1))
    (j : Fin (d+2)) (h : Fin N) :
    (Finsupp.domCongr facetOrderedVariableEquiv (facetLaplaceExponent c r j))
      (toLex (s, ULift.up h)) =
      (if r = s ∧ c j = h then 1 else 0) + (if c (j.succAbove s) = h then 1 else 0) := by
  simp only [facetLaplaceExponent, map_add, Finsupp.add_apply,
    facetLexSingle_apply, facetLexRowExponent_apply, facetDelete, Function.comp_apply]

lemma facetDelete_adjacent_eq {c : Fin (d+2) → Fin N} (r i : Fin (d+1)) (hi : i ≠ r) :
    facetDelete c r.castSucc i = facetDelete c r.succ i := by
  rcases lt_or_gt_of_ne hi with h | h
  · simp only [facetDelete, Function.comp_apply, Fin.succAbove_castSucc_of_lt r i h,
      Fin.succAbove_succ_of_le r i h.le]
  · simp only [facetDelete, Function.comp_apply, Fin.succAbove_castSucc_of_le r i h.le,
      Fin.succAbove_succ_of_lt r i h]

lemma facetLaplaceExponent_head_eq (c : Fin (d+2) → Fin N) (r : Fin (d+1)) :
    facetLaplaceExponent c r r.castSucc = facetLaplaceExponent c r r.succ := by
  apply (Finsupp.domCongr facetOrderedVariableEquiv).injective
  ext v
  obtain ⟨⟨s, ⟨j⟩⟩, rfl⟩ := toLex.surjective v
  rw [facetLaplaceExponent_apply, facetLaplaceExponent_apply]
  by_cases hrs : r = s
  · subst s
    simp only [Fin.succAbove_castSucc_self, Fin.succAbove_succ_self, true_and]
    omega
  · have he := facetDelete_adjacent_eq (c := c) r s (Ne.symm hrs)
    simp only [facetDelete, Function.comp_apply] at he
    simp only [hrs, false_and, if_false, zero_add, he]

/-- Exactly two Laplace summands have the common leading monomial; every
other summand is strictly smaller in the paper's diagonal lexicographic order. -/
theorem facetLaplaceExponent_lt (c : Fin (d+2) → Fin N) (hc : StrictMono c)
    (r : Fin (d+1)) (j : Fin (d+2)) (hj₀ : j ≠ r.castSucc) (hj₁ : j ≠ r.succ) :
    facetLexOrder.toSyn (facetLaplaceExponent c r j) <
      facetLexOrder.toSyn (facetLaplaceExponent c r r.castSucc) := by
  change toLex (Finsupp.domCongr facetOrderedVariableEquiv (facetLaplaceExponent c r j)) <
    toLex (Finsupp.domCongr facetOrderedVariableEquiv (facetLaplaceExponent c r r.castSucc))
  rw [Finsupp.Lex.lt_iff]
  simp only [ofLex_toLex]
  by_cases hj : j < r.castSucc
  · let q : Fin (d+1) := ⟨j.val, by have hr := r.isLt; omega⟩
    have hq : q.castSucc = j := Fin.ext rfl
    have hqr : q < r := by exact hj
    have hstep : c j < c q.succ := hc (by rw [← hq]; exact (show q.castSucc < q.succ from Fin.castSucc_lt_succ))
    refine ⟨toLex (q, ULift.up (c j)), ?_, ?_⟩
    · intro v hv
      obtain ⟨⟨s, ⟨h⟩⟩, rfl⟩ := toLex.surjective v
      rcases Prod.Lex.toLex_lt_toLex.mp hv with hs | ⟨hs, hh⟩
      · have hsj : s.castSucc < j := by rw [← hq]; exact hs
        have hsr : s < r := hs.trans hqr
        simp only [facetLaplaceExponent_apply, Ne.symm hsr.ne, false_and, if_false, zero_add,
          Fin.succAbove_of_castSucc_lt j s hsj, Fin.succAbove_castSucc_of_lt r s hsr]
      · change s = q at hs
        subst s
        change h < c j at hh
        simp only [facetLaplaceExponent_apply, Ne.symm hqr.ne, false_and, if_false, zero_add,
          ← hq, Fin.succAbove_castSucc_self, Fin.succAbove_castSucc_of_lt r q hqr]
        rw [hq]
        simp only [if_neg (Ne.symm hh.ne), if_neg (Ne.symm (hh.trans hstep).ne)]
    · simp only [facetLaplaceExponent_apply, Ne.symm hqr.ne, false_and, if_false, zero_add,
        ← hq, Fin.succAbove_castSucc_self, Fin.succAbove_castSucc_of_lt r q hqr]
      rw [hq]
      simp only [if_neg (Ne.symm hstep.ne), if_pos rfl]
      decide
  · have hj : r.succ < j := by
      have he₀ : j.val ≠ r.val := fun he => hj₀ (Fin.ext he)
      have he₁ : j.val ≠ r.val+1 := fun he => hj₁ (Fin.ext he)
      change r.val+1 < j.val
      change ¬j.val < r.val at hj
      omega
    have hstep : c r.castSucc < c r.succ := hc ((show r.castSucc < r.succ from Fin.castSucc_lt_succ))
    have hlast : c r.succ < c j := hc hj
    refine ⟨toLex (r, ULift.up (c r.succ)), ?_, ?_⟩
    · intro v hv
      obtain ⟨⟨s, ⟨h⟩⟩, rfl⟩ := toLex.surjective v
      rcases Prod.Lex.toLex_lt_toLex.mp hv with hs | ⟨hs, hh⟩
      · have hsj : s.castSucc < j := (show s.castSucc < r.succ by
          change s.val < r.val+1
          have hs' : s.val < r.val := hs
          omega).trans hj
        simp only [facetLaplaceExponent_apply, Ne.symm hs.ne, false_and, if_false, zero_add,
          Fin.succAbove_of_castSucc_lt j s hsj, Fin.succAbove_castSucc_of_lt r s hs]
      · change s = r at hs
        subst s
        change h < c r.succ at hh
        have hrj : r.castSucc < j := ((show r.castSucc < r.succ from Fin.castSucc_lt_succ)).trans hj
        simp only [facetLaplaceExponent_apply, true_and,
          Fin.succAbove_of_castSucc_lt j r hrj, Fin.succAbove_castSucc_self,
          if_neg (Ne.symm (hh.trans hlast).ne), if_neg (Ne.symm hh.ne), zero_add, add_zero]
    · have hrj : r.castSucc < j := ((show r.castSucc < r.succ from Fin.castSucc_lt_succ)).trans hj
      simp only [facetLaplaceExponent_apply, true_and,
        Fin.succAbove_of_castSucc_lt j r hrj, Fin.succAbove_castSucc_self,
        if_neg (Ne.symm hlast.ne), if_neg hstep.ne, if_pos rfl, zero_add]
      decide

end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.facet_laplace_relation
#print axioms FourPapers.Sublattice.facetLaplaceExponent_lt

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FacetLaplacePairs -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FourPapers.Sublattice
open Classical MvPolynomial CommAlg.Polymatroid FourPapers.MonicPairCriterion
universe u
variable {d N : ℕ} {k : Type u} [CommRing k] [Nontrivial k]

def facetMinorGenerators (E : Finset ((Fin (d+1) → Fin N))) :
    Set (MvPolynomial (FiniteVariable.{u} (UnitIntervalRows d N)) k) :=
  {f | ∃ a ∈ E, f = facetMinor a}

def facetMinorIdeal (E : Finset ((Fin (d+1) → Fin N))) :
    Ideal (MvPolynomial (FiniteVariable.{u} (UnitIntervalRows d N)) k) :=
  Ideal.span (facetMinorGenerators E)

lemma facetMinor_mem_generators {E : Finset ((Fin (d+1) → Fin N))}
    {a : (Fin (d+1) → Fin N)} (ha : a ∈ E) :
    facetMinor (k := k) a ∈ facetMinorGenerators E := ⟨a, ha, rfl⟩

lemma facetLaplaceExponent_head_sup (c : Fin (d+2) → Fin N) (hc : StrictMono c)
    (r : Fin (d+1)) :
    facetLaplaceExponent c r r.castSucc =
      finiteRowExponent (UnitIntervalRows d N) (facetDelete c r.castSucc) ⊔
        finiteRowExponent (UnitIntervalRows d N) (facetDelete c r.succ) := by
  apply (Finsupp.domCongr facetOrderedVariableEquiv).injective
  ext v
  obtain ⟨⟨s, ⟨h⟩⟩, rfl⟩ := toLex.surjective v
  change _ = max
    ((Finsupp.domCongr facetOrderedVariableEquiv (finiteRowExponent _ (facetDelete c r.castSucc)))
      (toLex (s, ULift.up h)))
    ((Finsupp.domCongr facetOrderedVariableEquiv (finiteRowExponent _ (facetDelete c r.succ)))
      (toLex (s, ULift.up h)))
  rw [facetLaplaceExponent_apply, facetLexRowExponent_apply, facetLexRowExponent_apply]
  by_cases hrs : r = s
  · subst s
    have hne := (hc ((show r.castSucc < r.succ from Fin.castSucc_lt_succ))).ne
    simp only [facetDelete, Function.comp_apply, Fin.succAbove_castSucc_self,
      Fin.succAbove_succ_self, true_and]
    by_cases h₀ : c r.castSucc = h
    · have h₁ : c r.succ ≠ h := by rw [← h₀]; exact Ne.symm hne
      simp only [h₀, h₁, if_true, if_false]
      decide
    · simp only [h₀, if_false, zero_add]
      split_ifs <;> decide
  · have he := facetDelete_adjacent_eq (c := c) r s (Ne.symm hrs)
    simp only [hrs, false_and, if_false, zero_add]
    change _ = max (if facetDelete c r.castSucc s = h then 1 else 0)
      (if facetDelete c r.succ s = h then 1 else 0)
    rw [← he, max_self]
    rfl

set_option maxHeartbeats 100000 in
set_option backward.isDefEq.respectTransparency true in
/-- The adjacent Laplace pair has a strict bounded representation using
actual minors. No Gröbner property is used to prove this identity. -/
theorem facetLaplace_pair_reduces
    {E : Finset ((Fin (d+1) → Fin N))}
    (c : Fin (d+2) → Fin N) (hc : StrictMono c) (r : Fin (d+1))
    (hE : ∀ j, facetDelete c j ∈ E) :
    normalizedDifference facetLexOrder (facetLaplaceExponent c r r.castSucc)
      (facetMinor (k := k) (facetDelete c r.castSucc)) (facetMinor (facetDelete c r.succ)) ∈
      productSpan facetLexOrder (facetMinorGenerators E)
        (Set.Iio (facetLexOrder.toSyn (facetLaplaceExponent c r r.castSucc))) := by
  let P := productSpan facetLexOrder (facetMinorGenerators (k := k) E)
    (Set.Iio (facetLexOrder.toSyn (facetLaplaceExponent c r r.castSucc)))
  let t : Fin (d+2) → MvPolynomial (FiniteVariable.{u} (UnitIntervalRows d N)) k :=
    fun j => X ⟨r, ULift.up (c j)⟩ * facetMinor (facetDelete c j)
  let f : Fin (d+2) → MvPolynomial (FiniteVariable.{u} (UnitIntervalRows d N)) k :=
    fun j => (-1 : k) ^ j.val • t j
  let S := ((Finset.univ : Finset (Fin (d+2))).erase r.castSucc).erase r.succ
  have hne : r.castSucc ≠ r.succ := ((show r.castSucc < r.succ from Fin.castSucc_lt_succ)).ne
  have hrest : (∑ j ∈ S, f j) ∈ P := by
    apply Submodule.sum_mem
    intro j hj
    have hj₁ : j ≠ r.succ := (Finset.mem_erase.mp hj).1
    have hj₀ : j ≠ r.castSucc := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
    change (-1 : k) ^ j.val • t j ∈ P
    refine P.smul_mem ((-1 : k) ^ j.val) ?_
    dsimp only [t, MvPolynomial.X]
    have hbound : facetLexOrder.toSyn
        (Finsupp.single (⟨r, ULift.up (c j)⟩ : FiniteVariable.{u} (UnitIntervalRows d N)) 1 +
          facetLexOrder.degree (facetMinor (k := k) (facetDelete c j))) <
        facetLexOrder.toSyn (facetLaplaceExponent c r r.castSucc) := by
      rw [facetMinor_degree (k := k) (facetDelete c j) (facetDelete_strictMono hc j)]
      exact facetLaplaceExponent_lt c hc r j hj₀ hj₁
    exact monomial_mem_productSpan (V := FiniteVariable.{u} (UnitIntervalRows d N))
      (R := k) facetLexOrder (facetMinorGenerators (k := k) E)
      (s := Set.Iio (facetLexOrder.toSyn (facetLaplaceExponent c r r.castSucc)))
      (b := facetMinor (k := k) (facetDelete c j)) (facetMinor_mem_generators (hE j))
      (a := Finsupp.single ⟨r, ULift.up (c j)⟩ 1) hbound
  have hsum : (∑ j, f j) = f r.castSucc + f r.succ + ∑ j ∈ S, f j := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ r.castSucc),
      ← Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ _⟩)]
    abel
  have hzero : (∑ j, f j) = 0 := facet_laplace_relation c r
  rw [hsum] at hzero
  have hs : (-1 : k) ^ r.succ.val = -((-1 : k) ^ r.val) := by
    simp only [Fin.val_succ, pow_succ, mul_neg_one]
  have hdiff : (-1 : k) ^ r.val • (t r.castSucc - t r.succ) = -(∑ j ∈ S, f j) := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [f, Fin.val_castSucc, hs, neg_smul, smul_sub, sub_eq_add_neg, smul_add, smul_neg,
      add_assoc] using hzero
  have hmem : (-1 : k) ^ r.val • (t r.castSucc - t r.succ) ∈ P := by
    rw [hdiff]
    exact P.neg_mem hrest
  have hunit : (-1 : k) ^ r.val * (-1 : k) ^ r.val = 1 := by
    rw [← pow_add, show r.val + r.val = 2*r.val by omega, pow_mul]
    simp
  have hmem' : t r.castSucc - t r.succ ∈ P := by
    have h := P.smul_mem ((-1 : k) ^ r.val) hmem
    simpa only [smul_smul, hunit, one_smul] using h
  have h₀ : facetLaplaceExponent c r r.castSucc -
      facetLexOrder.degree (facetMinor (k := k) (facetDelete c r.castSucc)) =
        Finsupp.single ⟨r, ULift.up (c r.castSucc)⟩ 1 := by
    rw [facetMinor_degree _ (facetDelete_strictMono hc _), facetLaplaceExponent, add_tsub_cancel_right]
  have h₁ : facetLaplaceExponent c r r.castSucc -
      facetLexOrder.degree (facetMinor (k := k) (facetDelete c r.succ)) =
        Finsupp.single ⟨r, ULift.up (c r.succ)⟩ 1 := by
    rw [facetLaplaceExponent_head_eq, facetMinor_degree _ (facetDelete_strictMono hc _),
      facetLaplaceExponent, add_tsub_cancel_right]
  change normalizedDifference facetLexOrder _ _ _ ∈ P
  rw [normalizedDifference, h₀, h₁]
  exact hmem'

theorem facetLaplace_pair_reduces_at
    {E : Finset ((Fin (d+1) → Fin N))}
    (c : Fin (d+2) → Fin N) (hc : StrictMono c) (r : Fin (d+1))
    (hE : ∀ j, facetDelete c j ∈ E) (D : Exponent (FiniteVariable.{u} (UnitIntervalRows d N)))
    (h₀ : finiteRowExponent (UnitIntervalRows d N) (facetDelete c r.castSucc) ≤ D)
    (h₁ : finiteRowExponent (UnitIntervalRows d N) (facetDelete c r.succ) ≤ D) :
    normalizedDifference facetLexOrder D (facetMinor (k := k) (facetDelete c r.castSucc))
        (facetMinor (facetDelete c r.succ)) ∈
      productSpan facetLexOrder (facetMinorGenerators E) (Set.Iio (facetLexOrder.toSyn D)) := by
  apply normalizedDifference_mem_of_smaller_bound facetLexOrder _ D
    (facetLaplaceExponent c r r.castSucc) _ _
  · rw [facetMinor_degree _ (facetDelete_strictMono hc _), facetLaplaceExponent_head_sup c hc]
    exact le_sup_left
  · rw [facetMinor_degree _ (facetDelete_strictMono hc _), facetLaplaceExponent_head_sup c hc]
    exact le_sup_right
  · rw [facetLaplaceExponent_head_sup c hc]
    exact sup_le h₀ h₁
  · exact facetLaplace_pair_reduces c hc r hE

end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.facetLaplace_pair_reduces_at

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FacetCliquePairs -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FourPapers.Sublattice
open Classical MvPolynomial CommAlg.Polymatroid FourPapers.MonicPairCriterion
universe u
variable {d N : ℕ} {k : Type u} [CommRing k] [Nontrivial k]

def FacetInInterval (l u : Fin N) (a : (Fin (d+1) → Fin N)) : Prop :=
  StrictMono a ∧ ∀ i, l ≤ a i ∧ a i ≤ u

lemma facets_first_difference {a b : (Fin (d+1) → Fin N)} (hab : a ≠ b) :
    ∃ r, (∀ i, i < r → a i = b i) ∧ a r ≠ b r := by
  let S := (Finset.univ : Finset (Fin (d+1))).filter (fun i => a i ≠ b i)
  have hS : S.Nonempty := by
    by_contra h
    apply hab
    funext i
    by_contra hi
    exact h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  let r := S.min' hS
  refine ⟨r, ?_, (Finset.mem_filter.mp (Finset.min'_mem S hS)).2⟩
  intro i hi
  by_contra hn
  have hri := Finset.min'_le S i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
  exact (not_le_of_gt hi) hri

def facetSize (a : (Fin (d+1) → Fin N)) : ℕ := ∑ i, (a i).val

lemma facetSize_update_lt (a : (Fin (d+1) → Fin N))
    (r : Fin (d+1)) (j : Fin N) (hj : j < a r) :
    facetSize (Function.update a r j) < facetSize a := by
  apply Finset.sum_lt_sum
  · intro i _
    by_cases hi : i = r
    · subst i
      simpa only [Function.update_self] using (show j.val ≤ (a r).val from hj.le)
    · simp only [Function.update_of_ne hi, le_refl]
  · exact ⟨r, Finset.mem_univ _, by simpa only [Function.update_self] using (show j.val < (a r).val from hj)⟩

lemma facetRowExponent_update_le
    {a b : (Fin (d+1) → Fin N)} (r : Fin (d+1))
    {D : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))}
    (ha : finiteRowExponent (UnitIntervalRows d N) a ≤ D)
    (hb : finiteRowExponent (UnitIntervalRows d N) b ≤ D) :
    finiteRowExponent (UnitIntervalRows d N) (Function.update a r (b r)) ≤ D := by
  rintro ⟨i, ⟨j⟩⟩
  by_cases hi : i = r
  · subst i
    simpa only [finiteRowExponent_apply, Function.update_self] using hb ⟨r, ULift.up j⟩
  · simpa only [finiteRowExponent_apply, Function.update_of_ne hi] using ha ⟨i, ULift.up j⟩

lemma facetInsert_strictMono {a b : (Fin (d+1) → Fin N)}
    (ha : StrictMono a) (hb : StrictMono b) (r : Fin (d+1))
    (hprev : ∀ i, i < r → a i = b i) (hr : b r < a r) :
    StrictMono (Fin.insertNth (α := fun _ : Fin (d+2) => Fin N) r.castSucc (b r) a) := by
  apply (Fin.strictMono_insertNth_iff _ _ _).mpr
  refine ⟨ha, ?_, ?_⟩
  · intro i hi
    have hir : i < r := hi
    rw [hprev i hir]
    exact hb hir
  · intro i hi
    have hri : r ≤ i := hi
    exact hr.trans_le (ha.monotone hri)

lemma facetDelete_insert_left (a : (Fin (d+1) → Fin N))
    (r : Fin (d+1)) (j : Fin N) :
    facetDelete (Fin.insertNth (α := fun _ : Fin (d+2) => Fin N) r.castSucc j a) r.castSucc = a :=
  Fin.insertNth_comp_succAbove _ _ _

lemma facetDelete_insert_right (a : (Fin (d+1) → Fin N))
    (r : Fin (d+1)) (j : Fin N) :
    facetDelete (Fin.insertNth (α := fun _ : Fin (d+2) => Fin N) r.castSucc j a) r.succ = Function.update a r j := by
  funext i
  by_cases hi : i = r
  · subst i
    simp only [facetDelete, Function.comp_apply, Fin.succAbove_succ_self,
      Fin.insertNth_apply_same, Function.update_self]
  · rw [← facetDelete_adjacent_eq r i hi, facetDelete_insert_left,
      Function.update_of_ne hi]

lemma facetInsert_in_interval {l u : Fin N}
    {a b : (Fin (d+1) → Fin N)}
    (ha : FacetInInterval l u a) (hb : FacetInInterval l u b) (r : Fin (d+1))
    (j : Fin (d+2)) :
    l ≤ Fin.insertNth (α := fun _ : Fin (d+2) => Fin N) r.castSucc (b r) a j ∧ Fin.insertNth (α := fun _ : Fin (d+2) => Fin N) r.castSucc (b r) a j ≤ u := by
  by_cases hj : j = r.castSucc
  · subst j
    simpa only [Fin.insertNth_apply_same] using hb.2 r
  · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hj
    rw [← hi, Fin.insertNth_apply_succAbove]
    exact ha.2 i

/-- Every pair in one complete interval admits strict Laplace reductions.
The proof descends through actual column replacements; it does not assume
the classical maximal-minor Gröbner theorem or any straightening law. -/
theorem facet_interval_pair_reduces
    {E : Finset ((Fin (d+1) → Fin N))} (l u : Fin N)
    (hE : ∀ a, FacetInInterval l u a → a ∈ E)
    (a b : (Fin (d+1) → Fin N))
    (ha : FacetInInterval l u a) (hb : FacetInInterval l u b)
    (D : Exponent (FiniteVariable.{u} (UnitIntervalRows d N)))
    (haD : finiteRowExponent (UnitIntervalRows d N) a ≤ D)
    (hbD : finiteRowExponent (UnitIntervalRows d N) b ≤ D) :
    normalizedDifference facetLexOrder D (facetMinor (k := k) a) (facetMinor b) ∈
      productSpan facetLexOrder (facetMinorGenerators E) (Set.Iio (facetLexOrder.toSyn D)) := by
  suffices h : ∀ q, ∀ a b : (Fin (d+1) → Fin N),
      facetSize a + facetSize b = q → FacetInInterval l u a → FacetInInterval l u b →
      finiteRowExponent (UnitIntervalRows d N) a ≤ D →
      finiteRowExponent (UnitIntervalRows d N) b ≤ D →
      normalizedDifference facetLexOrder D (facetMinor (k := k) a) (facetMinor b) ∈
        productSpan facetLexOrder (facetMinorGenerators E) (Set.Iio (facetLexOrder.toSyn D)) from
    h _ a b rfl ha hb haD hbD
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
    have hstep : ∀ a b : (Fin (d+1) → Fin N),
        facetSize a + facetSize b = q → FacetInInterval l u a → FacetInInterval l u b →
        finiteRowExponent (UnitIntervalRows d N) a ≤ D →
        finiteRowExponent (UnitIntervalRows d N) b ≤ D →
        ∀ r, (∀ i, i < r → a i = b i) → b r < a r →
        normalizedDifference facetLexOrder D (facetMinor (k := k) a) (facetMinor b) ∈
          productSpan facetLexOrder (facetMinorGenerators E) (Set.Iio (facetLexOrder.toSyn D)) := by
      intro a b hq ha hb haD hbD r hprev hr
      let a' := Function.update a r (b r)
      let c := Fin.insertNth (α := fun _ : Fin (d+2) => Fin N) r.castSucc (b r) a
      have hc : StrictMono c := facetInsert_strictMono ha.1 hb.1 r hprev hr
      have hcE : ∀ j, facetDelete c j ∈ E := by
        intro j
        apply hE
        exact ⟨facetDelete_strictMono hc j,
          fun i => facetInsert_in_interval ha hb r (j.succAbove i)⟩
      have ha' : FacetInInterval l u a' := by
        change FacetInInterval l u (Function.update a r (b r))
        rw [← facetDelete_insert_right a r (b r)]
        exact ⟨facetDelete_strictMono hc r.succ,
          fun i => facetInsert_in_interval ha hb r (r.succ.succAbove i)⟩
      have ha'D : finiteRowExponent (UnitIntervalRows d N) a' ≤ D :=
        facetRowExponent_update_le r haD hbD
      have hlt : facetSize a' + facetSize b < q := by
        rw [← hq]
        exact Nat.add_lt_add_right (facetSize_update_lt a r (b r) hr) _
      have htail := ih _ hlt a' b rfl ha' hb ha'D hbD
      have hhead := facetLaplace_pair_reduces_at (k := k) c hc r hcE D
        (by simpa only [c, facetDelete_insert_left] using haD)
        (by simpa only [c, facetDelete_insert_right] using ha'D)
      simp only [c, facetDelete_insert_left, facetDelete_insert_right] at hhead
      rw [normalizedDifference_trans facetLexOrder D (facetMinor a) (facetMinor a') (facetMinor b)]
      exact add_mem hhead htail
    intro a b hq ha hb haD hbD
    by_cases he : a = b
    · simp only [he, normalizedDifference_self]
      exact zero_mem _
    obtain ⟨r, hprev, hr⟩ := facets_first_difference he
    rcases lt_or_gt_of_ne hr with hr | hr
    · rw [normalizedDifference_symm]
      exact neg_mem (hstep b a (by simpa only [add_comm] using hq) hb ha hbD haD r
        (fun i hi => (hprev i hi).symm) hr)
    · exact hstep a b hq ha hb haD hbD r hprev hr

end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.facet_interval_pair_reduces

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.UnitIntervalGroebner -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-!
# The actual maximal minors of a unit-interval facet family

The diagonal Gröbner basis statement is proved from determinant expansion,
Laplace identities, and leading-term descent. In particular, no initial-ideal
identity, straightening law, or Gröbner basis is assumed. If two diagonals
share a row variable, a third facet belongs to both endpoint cliques and its
diagonal divides their least common multiple. The two clique reductions then
telescope. Disjoint diagonals use the monic coprime-pair identity.
-/

noncomputable section
namespace FourPapers.Sublattice
open Classical MvPolynomial CommAlg.Polymatroid FourPapers.MonicPairCriterion
universe u
variable {d N : ℕ} {k : Type u} [CommRing k] [Nontrivial k]

lemma facetInInterval_of_endpoints {a : (Fin (d+1) → Fin N)}
    (ha : StrictMono a) {l u : Fin N} (hl : l ≤ a 0) (hu : a (Fin.last d) ≤ u) :
    FacetInInterval l u a := by
  refine ⟨ha, fun i => ⟨?_, ?_⟩⟩
  · exact hl.trans (ha.monotone (Fin.zero_le i))
  · exact (ha.monotone (Fin.le_last i)).trans hu

lemma facetInInterval_self {a : (Fin (d+1) → Fin N)} (ha : StrictMono a) :
    FacetInInterval (a 0) (a (Fin.last d)) a :=
  facetInInterval_of_endpoints ha le_rfl le_rfl

lemma UnitIntervalFacetFamily.interval_complete
    {E : Finset ((Fin (d+1) → Fin N))} (hE : UnitIntervalFacetFamily E)
    {a : (Fin (d+1) → Fin N)} (ha : a ∈ E)
    (b : (Fin (d+1) → Fin N))
    (hb : FacetInInterval (a 0) (a (Fin.last d)) b) : b ∈ E :=
  hE.interval a ha b hb.1 (hb.2 0).1 (hb.2 (Fin.last d)).2

/-- The facet common to two endpoint cliques when their diagonals share row `r`.
The use of a maximum before the shared entry and a minimum after it is what
keeps both endpoints inside both cliques. -/
def facetOverlap (a b : (Fin (d+1) → Fin N)) (r : Fin (d+1)) :
    (Fin (d+1) → Fin N) :=
  fun i => if i ≤ r then max (a i) (b i) else min (a i) (b i)

lemma facetOverlap_select (a b : (Fin (d+1) → Fin N)) (r i : Fin (d+1)) :
    facetOverlap a b r i = a i ∨ facetOverlap a b r i = b i := by
  unfold facetOverlap
  split_ifs
  · rcases le_total (a i) (b i) with h | h
    · exact Or.inr (max_eq_right h)
    · exact Or.inl (max_eq_left h)
  · rcases le_total (a i) (b i) with h | h
    · exact Or.inl (min_eq_left h)
    · exact Or.inr (min_eq_right h)

lemma facetOverlap_strictMono {a b : (Fin (d+1) → Fin N)}
    (ha : StrictMono a) (hb : StrictMono b) (r : Fin (d+1)) (hr : a r = b r) :
    StrictMono (facetOverlap a b r) := by
  intro i j hij
  by_cases hj : j ≤ r
  · simp only [facetOverlap, if_pos (hij.le.trans hj), if_pos hj]
    exact max_lt_max (ha hij) (hb hij)
  by_cases hi : i ≤ r
  · simp only [facetOverlap, if_pos hi, if_neg hj]
    have hleft : max (a i) (b i) ≤ a r := by
      exact max_le (ha.monotone hi) (by rw [hr]; exact hb.monotone hi)
    have hright : a r < min (a j) (b j) := by
      exact lt_min (ha (lt_of_not_ge hj)) (by rw [hr]; exact hb (lt_of_not_ge hj))
    exact hleft.trans_lt hright
  · simp only [facetOverlap, if_neg hi, if_neg hj]
    exact min_lt_min (ha hij) (hb hij)

lemma facetOverlap_lower (a b : (Fin (d+1) → Fin N)) (r : Fin (d+1)) :
    a 0 ≤ facetOverlap a b r 0 ∧ b 0 ≤ facetOverlap a b r 0 := by
  simp only [facetOverlap, if_pos (Fin.zero_le r)]
  exact ⟨le_max_left _ _, le_max_right _ _⟩

lemma facetOverlap_upper {a b : (Fin (d+1) → Fin N)}
    (r : Fin (d+1)) (hr : a r = b r) :
    facetOverlap a b r (Fin.last d) ≤ a (Fin.last d) ∧
      facetOverlap a b r (Fin.last d) ≤ b (Fin.last d) := by
  by_cases h : Fin.last d ≤ r
  · have he : r = Fin.last d := le_antisymm (Fin.le_last r) h
    subst r
    simp only [facetOverlap, if_pos le_rfl, hr, max_self, le_refl, and_self, ite_true]
  · simp only [facetOverlap, if_neg h]
    exact ⟨min_le_left _ _, min_le_right _ _⟩

lemma facetOverlap_in_intervals {a b : (Fin (d+1) → Fin N)}
    (ha : StrictMono a) (hb : StrictMono b) (r : Fin (d+1)) (hr : a r = b r) :
    FacetInInterval (a 0) (a (Fin.last d)) (facetOverlap a b r) ∧
      FacetInInterval (b 0) (b (Fin.last d)) (facetOverlap a b r) := by
  have hc := facetOverlap_strictMono ha hb r hr
  have hl := facetOverlap_lower a b r
  have hu := facetOverlap_upper r hr
  exact ⟨facetInInterval_of_endpoints hc hl.1 hu.1,
    facetInInterval_of_endpoints hc hl.2 hu.2⟩

lemma facetRowExponent_select_le
    {a b c : (Fin (d+1) → Fin N)}
    (hc : ∀ i, c i = a i ∨ c i = b i)
    {D : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))}
    (haD : finiteRowExponent (UnitIntervalRows d N) a ≤ D)
    (hbD : finiteRowExponent (UnitIntervalRows d N) b ≤ D) :
    finiteRowExponent (UnitIntervalRows d N) c ≤ D := by
  rintro ⟨i, ⟨j⟩⟩
  rcases hc i with h | h
  · simpa only [finiteRowExponent_apply, h] using haD ⟨i, ULift.up j⟩
  · simpa only [finiteRowExponent_apply, h] using hbD ⟨i, ULift.up j⟩

lemma facetRowExponent_sup_eq_add_of_disjoint
    {a b : (Fin (d+1) → Fin N)} (hab : ∀ i, a i ≠ b i) :
    finiteRowExponent.{u} (UnitIntervalRows d N) a ⊔ finiteRowExponent (UnitIntervalRows d N) b =
      finiteRowExponent (UnitIntervalRows d N) a + finiteRowExponent (UnitIntervalRows d N) b := by
  ext ⟨i, ⟨j⟩⟩
  change max (finiteRowExponent _ a ⟨i, ULift.up j⟩)
      (finiteRowExponent _ b ⟨i, ULift.up j⟩) =
    finiteRowExponent _ a ⟨i, ULift.up j⟩ + finiteRowExponent _ b ⟨i, ULift.up j⟩
  simp only [finiteRowExponent_apply]
  by_cases ha : a i = j
  · have hb : b i ≠ j := by rw [← ha]; exact Ne.symm (hab i)
    simp only [ha, hb, if_true, if_false, max_zero, add_zero]
  · simp only [ha, if_false, zero_max, zero_add]

/-- Every pair of actual minors has a strict polynomial reduction. The full
unit-interval quantifier is retained; facets need not belong to one clique. -/
theorem unitInterval_minor_pairReduces
    {E : Finset ((Fin (d+1) → Fin N))} (hE : UnitIntervalFacetFamily E) :
    PairReduces facetLexOrder (facetMinorGenerators (k := k) E) := by
  rintro f ⟨a, ha, rfl⟩ g ⟨b, hb, rfl⟩ D haD hbD
  have hma := hE.increasing a ha
  have hmb := hE.increasing b hb
  rw [facetMinor_degree a hma] at haD
  rw [facetMinor_degree b hmb] at hbD
  by_cases hshare : ∃ r, a r = b r
  · obtain ⟨r, hr⟩ := hshare
    let c := facetOverlap a b r
    have hc := facetOverlap_in_intervals hma hmb r hr
    have hcD : finiteRowExponent (UnitIntervalRows d N) c ≤ D :=
      facetRowExponent_select_le (facetOverlap_select a b r) haD hbD
    have hac := facet_interval_pair_reduces (k := k) (a 0) (a (Fin.last d))
      (hE.interval_complete ha) a c (facetInInterval_self hma) hc.1 D haD hcD
    have hcb := facet_interval_pair_reduces (k := k) (b 0) (b (Fin.last d))
      (hE.interval_complete hb) c b hc.2 (facetInInterval_self hmb) D hcD hbD
    rw [normalizedDifference_trans facetLexOrder D (facetMinor a) (facetMinor c) (facetMinor b)]
    exact add_mem hac hcb
  · have hdis : ∀ i, a i ≠ b i := fun i hi => hshare ⟨i, hi⟩
    apply coprime_pair_reduces facetLexOrder (facetMinorGenerators E)
      (facetMinor a) (facetMinor b) (facetMinor_mem_generators ha) (facetMinor_mem_generators hb)
      (facetMinor_leadingCoeff a hma) (facetMinor_leadingCoeff b hmb)
    · rw [facetMinor_degree a hma, facetMinor_degree b hmb]
      exact facetRowExponent_sup_eq_add_of_disjoint hdis
    · rwa [facetMinor_degree a hma]
    · rwa [facetMinor_degree b hmb]

/-- The minors themselves form a Gröbner basis of their actual determinantal
ideal, over any nontrivial commutative coefficient ring. -/
theorem unitInterval_minors_isGroebnerBasis
    {E : Finset ((Fin (d+1) → Fin N))} (hE : UnitIntervalFacetFamily E) :
    facetLexOrder.IsGroebnerBasis (facetMinorGenerators (k := k) E) (facetMinorIdeal E) := by
  apply isGroebnerBasis_of_pairReduces
  · rintro f ⟨a, ha, rfl⟩
    exact facetMinor_leadingCoeff a (hE.increasing a ha)
  · exact unitInterval_minor_pairReduces hE

lemma facetMinor_leadingTerm (a : (Fin (d+1) → Fin N)) (ha : StrictMono a) :
    facetLexOrder.leadingTerm (facetMinor (k := k) a) = finiteRowMonomial (UnitIntervalRows d N) a := by
  rw [MonomialOrder.leadingTerm, facetMinor_degree a ha, facetMinor_leadingCoeff a ha,
    finiteRowMonomial_eq_monomial]

/-- The first-power initial-ideal identity needed in Section 6 is an equality
of actual ideals in the original polynomial ring. -/
theorem unitInterval_initialIdeal
    {E : Finset ((Fin (d+1) → Fin N))} (hE : UnitIntervalFacetFamily E) :
    Ideal.span (facetLexOrder.leadingTerm '' (facetMinorIdeal (k := k) E : Set _)) =
      finiteSublatticeIdeal (UnitIntervalRows d N) (k := k) E := by
  rw [(unitInterval_minors_isGroebnerBasis hE).span_leadingTerm_image]
  unfold finiteSublatticeIdeal
  apply congrArg Ideal.span
  ext f
  constructor
  · rintro ⟨g, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, (facetMinor_leadingTerm a (hE.increasing a ha)).symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨facetMinor a, facetMinor_mem_generators ha,
      facetMinor_leadingTerm a (hE.increasing a ha)⟩

end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.unitInterval_minors_isGroebnerBasis
#print axioms FourPapers.Sublattice.unitInterval_initialIdeal

end
end


end
