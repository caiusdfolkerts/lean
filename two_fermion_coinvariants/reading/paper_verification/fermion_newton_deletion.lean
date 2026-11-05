module

public import PaperVerification.FermionNewtonModule
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.Data.Finset.Max

/-!
# The kernel in Newton deletion

Multiplying a field by the deleted coordinate raises exactly that coordinate's
multiplicity. The other tangent and normal conditions are unaffected because
every edge equation is relatively prime to a coordinate variable. Consequently
the literal restriction kernel is the deleted module multiplied by that
coordinate. Surjectivity onto the prescribed restricted module is a separate
Newton-basis obligation.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open MvPolynomial

variable {F : Type*} [Field F] {n : ℕ}

/-- Restrict polynomials to the coordinate hyperplane `Xq = 0`. -/
def coordinateRestriction (q : Fin n) : P (F := F) (n := n) →ₐ[F] P (F := F) (n := n) :=
  aeval fun i ↦ if i = q then 0 else X i

@[simp] theorem coordinateRestriction_X_self (q : Fin n) :
    coordinateRestriction (F := F) q (X q) = 0 := by
  simp [coordinateRestriction]

 theorem coordinateRestriction_eq_zero_iff (q : Fin n) (p : P (F := F) (n := n)) :
    coordinateRestriction q p = 0 ↔ X q ∣ p := by
  have h := MvPolynomial.span_X_image_eq_ker_aeval_ite_mem (R := F) ({q} : Set (Fin n))
  have hker : RingHom.ker (coordinateRestriction (F := F) q) = Ideal.span {X q} := by
    simpa only [Set.image_singleton, coordinateRestriction, Set.mem_compl_iff,
      Set.mem_singleton_iff, ite_not] using h.symm
  rw [← RingHom.mem_ker, hker, Ideal.mem_span_singleton]

 theorem edgeLinear_relPrime_X (e : Edge n) (q : Fin n) :
    IsRelPrime (edgeLinear (F := F) e) (X q) := by
  apply IsRelPrime.symm
  apply (MvPolynomial.prime_X (R := F) (i := q)).irreducible.isRelPrime_iff_not_dvd.mpr
  intro hd
  have hz := (coordinateRestriction_eq_zero_iff q (edgeLinear (F := F) e)).mpr hd
  rcases e with ⟨⟨i, j⟩, hij⟩
  by_cases hi : i = q
  · have hj : j ≠ q := by intro h; exact (ne_of_lt hij) (hi.trans h.symm)
    simp [coordinateRestriction, edgeLinear, hi, hj] at hz
  · by_cases hj : j = q
    · simp [coordinateRestriction, edgeLinear, hi, hj] at hz
    · simp only [coordinateRestriction, edgeLinear, map_sub, aeval_X, if_neg hi,
        if_neg hj, sub_eq_zero, MvPolynomial.X_inj] at hz
      exact (ne_of_lt hij) hz

/-- Lower one positive coordinate multiplicity, keeping the signs unchanged. -/
def deletedMultiplicity (δ : Fin n → ℕ) (q : Fin n) : Fin n → ℕ :=
  Function.update δ q (δ q - 1)

@[simp] theorem deletedMultiplicity_self (δ : Fin n → ℕ) (q : Fin n) :
    deletedMultiplicity δ q q = δ q - 1 := by simp [deletedMultiplicity]

@[simp] theorem deletedMultiplicity_ne (δ : Fin n → ℕ) (q i : Fin n) (hi : i ≠ q) :
    deletedMultiplicity δ q i = δ i := by simp [deletedMultiplicity, hi]

/-- Exact coordinate divisibility after multiplication by the deleted variable. -/
theorem coordinate_divisibility_delete_iff (δ : Fin n → ℕ) (q : Fin n)
    (hq : 0 < δ q) (a : Fin n → P (F := F) (n := n)) :
    (∀ i, X i ^ δ i ∣ X q * a i) ↔
      ∀ i, X i ^ deletedMultiplicity δ q i ∣ a i := by
  constructor
  · intro h i
    by_cases hi : i = q
    · subst i
      rw [deletedMultiplicity_self]
      have hp := h q
      have hdeg : δ q = (δ q - 1) + 1 := by omega
      rw [hdeg, pow_succ', mul_dvd_mul_iff_left (MvPolynomial.X_ne_zero q)] at hp
      exact hp
    · rw [deletedMultiplicity_ne δ q i hi]
      have hcop : IsRelPrime ((X i : P (F := F) (n := n)) ^ δ i) (X q) := by
        apply IsRelPrime.pow_left
        exact (MvPolynomial.prime_X (R := F) (i := i)).irreducible.isRelPrime_iff_not_dvd.mpr
          (by simpa only [MvPolynomial.X_dvd_X] using hi)
      exact hcop.dvd_of_dvd_mul_left (h i)
  · intro h i
    by_cases hi : i = q
    · subst i
      have hp := h q
      rw [deletedMultiplicity_self] at hp
      have hdeg : δ q = (δ q - 1) + 1 := by omega
      rw [hdeg, pow_succ']
      exact mul_dvd_mul_left _ hp
    · have hp := h i
      rw [deletedMultiplicity_ne δ q i hi] at hp
      exact dvd_mul_of_dvd_right hp _

/-- The multiplication step for the exact module in Section 2.1. -/
theorem smul_mem_numeratorModule_iff_deleted (β : Fin n → F) (δ : Fin n → ℕ)
    (σ : Fin n → ℤ) (q : Fin n) (hq : 0 < δ q) (a : Fin n → P (F := F) (n := n)) :
    ((X q : P (F := F) (n := n)) • a) ∈ numeratorModule β δ σ ↔
      a ∈ numeratorModule β (deletedMultiplicity δ q) σ := by
  have hcoord := coordinate_divisibility_delete_iff δ q hq a
  constructor
  · intro h
    refine ⟨hcoord.mp h.1, ?_, ?_⟩
    · intro e he
      have hh := h.2.1 e he
      change edgeLinear e ∣ X q * a e.1.1 - X q * a e.1.2 at hh
      rw [← mul_sub] at hh
      exact (edgeLinear_relPrime_X e q).dvd_of_dvd_mul_left hh
    · intro e he
      have hh := h.2.2 e he
      refine ⟨?_, fun k hki hkj ↦
        (edgeLinear_relPrime_X e q).dvd_of_dvd_mul_left (hh.2 k hki hkj)⟩
      apply (edgeLinear_relPrime_X e q).dvd_of_dvd_mul_left
      convert hh.1 using 1 <;> simp only [Pi.smul_apply, smul_eq_mul] <;> ring
  · intro h
    refine ⟨hcoord.mpr h.1, ?_, ?_⟩
    · intro e he
      simpa only [Pi.smul_apply, smul_eq_mul, mul_sub] using
        dvd_mul_of_dvd_right (h.2.1 e he) (X q)
    · intro e he
      refine ⟨?_, fun k hki hkj ↦ dvd_mul_of_dvd_right ((h.2.2 e he).2 k hki hkj) (X q)⟩
      convert dvd_mul_of_dvd_right (h.2.2 e he).1 (X q) using 1 <;>
        simp only [Pi.smul_apply, smul_eq_mul] <;> ring

/-- The restriction kernel, stated on the actual polynomial numerators. -/
theorem restriction_kernel_eq_deleted_multiples (β : Fin n → F) (δ : Fin n → ℕ)
    (σ : Fin n → ℤ) (q : Fin n) (hq : 0 < δ q)
    (a : Fin n → P (F := F) (n := n)) (ha : a ∈ numeratorModule β δ σ) :
    (∀ i, coordinateRestriction q (a i) = 0) ↔
      ∃ b ∈ numeratorModule β (deletedMultiplicity δ q) σ,
        a = (X q : P (F := F) (n := n)) • b := by
  constructor
  · intro h
    have hdiv (i : Fin n) : X q ∣ a i := (coordinateRestriction_eq_zero_iff q (a i)).mp (h i)
    choose b hb using hdiv
    have hab : a = (X q : P (F := F) (n := n)) • b := by
      funext i
      exact hb i
    refine ⟨b, ?_, hab⟩
    rw [hab] at ha
    exact (smul_mem_numeratorModule_iff_deleted β δ σ q hq b).mp ha
  · rintro ⟨b, hb, rfl⟩ i
    simp [Pi.smul_apply, smul_eq_mul]

/-- Dropping the normal coordinate gives the same restriction kernel because
its prescribed positive multiplicity already makes that coordinate vanish. -/
theorem tangential_restriction_kernel_eq_deleted_multiples
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (q : Fin n) (hq : 0 < δ q)
    (a : Fin n → P (F := F) (n := n)) (ha : a ∈ numeratorModule β δ σ) :
    (∀ i, i ≠ q → coordinateRestriction q (a i) = 0) ↔
      ∃ b ∈ numeratorModule β (deletedMultiplicity δ q) σ,
        a = (X q : P (F := F) (n := n)) • b := by
  rw [← restriction_kernel_eq_deleted_multiples β δ σ q hq a ha]
  constructor
  · intro h i
    by_cases hi : i = q
    · subst i
      apply (coordinateRestriction_eq_zero_iff q (a q)).mpr
      exact (dvd_pow_self (X q) (Nat.ne_of_gt hq)).trans (ha.1 q)
    · exact h i hi
  · intro h i hi
    exact h i

/-- Compatibility of the multiplicity profile and edge signs, exactly (6). -/
def Compatible (δ : Fin n → ℕ) (σ : Fin n → ℤ) : Prop :=
  (∀ i j, i < j → σ i = 1 → δ j ≤ δ i) ∧
  (∀ i j, i < j → σ i = -1 → δ i ≤ δ j)

/-- The two properties of the vertex chosen in Proposition 2.3: every earlier
negative vertex has zero multiplicity, and a nonnegative chosen vertex is the
last vertex of positive multiplicity. -/
def DeletionVertex (δ : Fin n → ℕ) (σ : Fin n → ℤ) (q : Fin n) : Prop :=
  0 < δ q ∧ (∀ i, i < q → σ i = -1 → δ i = 0) ∧
    (σ q ≠ -1 → ∀ j, q < j → δ j = 0)

/-- A nonzero profile always admits the exact deletion choice from the paper. -/
theorem exists_deletionVertex (δ : Fin n → ℕ) (σ : Fin n → ℤ)
    (hδ : ∃ i, 0 < δ i) : ∃ q, DeletionVertex δ σ q := by
  classical
  let neg := Finset.univ.filter (fun i : Fin n ↦ σ i = -1 ∧ 0 < δ i)
  by_cases hneg : neg.Nonempty
  · let q := neg.min' hneg
    have hq : q ∈ neg := Finset.min'_mem neg hneg
    have hq' := (Finset.mem_filter.mp hq).2
    refine ⟨q, hq'.2, ?_, ?_⟩
    · intro i hi hσ
      by_contra hn
      have hm : i ∈ neg := by simp [neg, hσ, Nat.pos_of_ne_zero hn]
      exact (not_le_of_gt hi) (Finset.min'_le neg i hm)
    · intro hn
      exact False.elim (hn hq'.1)
  · let pos := Finset.univ.filter (fun i : Fin n ↦ 0 < δ i)
    have hpos : pos.Nonempty := by
      obtain ⟨i, hi⟩ := hδ
      exact ⟨i, by simp [pos, hi]⟩
    let q := pos.max' hpos
    have hq : q ∈ pos := Finset.max'_mem pos hpos
    refine ⟨q, (Finset.mem_filter.mp hq).2, ?_, ?_⟩
    · intro i hi hσ
      by_contra hn
      apply hneg
      exact ⟨i, by simp [neg, hσ, Nat.pos_of_ne_zero hn]⟩
    · intro hσ j hj
      by_contra hn
      have hm : j ∈ pos := by simp [pos, Nat.pos_of_ne_zero hn]
      exact (not_le_of_gt hj) (Finset.le_max' pos j hm)

/-- Lowering the chosen multiplicity preserves all profile hypotheses. -/
theorem Compatible.deleted (δ : Fin n → ℕ) (σ : Fin n → ℤ)
    (h : Compatible δ σ) (q : Fin n) (hq : DeletionVertex δ σ q) :
    Compatible (deletedMultiplicity δ q) σ := by
  constructor
  · intro i j hij hσ
    by_cases hi : i = q
    · subst i
      have hj := hq.2.2 (by omega) j hij
      rw [deletedMultiplicity_self, deletedMultiplicity_ne δ q j (ne_of_gt hij), hj]
      exact Nat.zero_le _
    · by_cases hj : j = q
      · subst j
        rw [deletedMultiplicity_self, deletedMultiplicity_ne δ q i hi]
        exact (Nat.sub_le _ _).trans (h.1 i q hij hσ)
      · rw [deletedMultiplicity_ne δ q i hi, deletedMultiplicity_ne δ q j hj]
        exact h.1 i j hij hσ
  · intro i j hij hσ
    by_cases hi : i = q
    · subst i
      rw [deletedMultiplicity_self, deletedMultiplicity_ne δ q j (ne_of_gt hij)]
      exact (Nat.sub_le _ _).trans (h.2 q j hij hσ)
    · by_cases hj : j = q
      · subst j
        rw [deletedMultiplicity_self, deletedMultiplicity_ne δ q i hi, hq.2.1 i hij hσ]
        exact Nat.zero_le _
      · rw [deletedMultiplicity_ne δ q i hi, deletedMultiplicity_ne δ q j hj]
        exact h.2 i j hij hσ

/-- The actual multiplicity change caused by restricting one incident edge. -/
def restrictAcrossSign (d : ℕ) (σ : ℤ) : ℕ :=
  if σ = -1 then d - 1 else if σ = 1 then max d 1 else d

/-- Earlier multiplicities are unchanged at the selected restriction vertex. -/
theorem restrictAcrossSign_before (δ : Fin n → ℕ) (σ : Fin n → ℤ)
    (h : Compatible δ σ) (q : Fin n) (hq : DeletionVertex δ σ q)
    (i : Fin n) (hi : i < q) : restrictAcrossSign (δ i) (σ i) = δ i := by
  unfold restrictAcrossSign
  split_ifs with hneg hpos
  · rw [hq.2.1 i hi hneg]
  · have hh := h.1 i q hi hpos
    have hpositive := hq.1
    exact max_eq_left (by omega)
  · rfl

/-- Every later multiplicity changes by the deleted sign, in the precise
integer sense needed for preservation of the surviving heights. -/
theorem restrictAcrossSign_after (δ : Fin n → ℕ) (σ : Fin n → ℤ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (h : Compatible δ σ) (q : Fin n) (hq : DeletionVertex δ σ q)
    (i : Fin n) (hi : q < i) :
    (restrictAcrossSign (δ i) (σ q) : ℤ) = (δ i : ℤ) + σ q := by
  rcases hσ q with hn | hz | hp
  · have hh := h.2 q i hi hn
    have hpositive := hq.1
    simp only [restrictAcrossSign, hn, if_true]
    omega
  · simp [restrictAcrossSign, hz]
  · have hh := hq.2.2 (by omega) i hi
    simp [restrictAcrossSign, hp, hh]

end PaperVerification.Fermion.Newton
