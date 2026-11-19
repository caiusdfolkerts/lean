module

public import higher_specht.verified.remaining02
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.Algebra.MvPolynomial.Coeff

/- Generated ordinary source-preserving proof stage. See audit/staged_specht_remaining/Remaining03Fiber/manifest.json. -/

@[expose] public section

section CanonicalSource0
/- Source: HigherSpecht/ElementaryCharacteristic.lean -/



/-!
# Elementary coefficients of the actual coordinate characteristic polynomial

These are identities over arbitrary commutative rings.  The family of roots
may contain repetitions; neither division nor a separability hypothesis is
used.  They supply the characteristic-polynomial relation in every parameter
fiber in Section 7.
-/

noncomputable section

open Finset MvPolynomial

namespace HigherSpecht

variable {R : Type*} [CommRing R] {ι : Type*}

def elementaryValue (Y : Finset ι) (x : ι → R) (d : ℕ) : R :=
  ∑ A ∈ Y.powersetCard d, ∏ i ∈ A, x i

@[simp] theorem elementaryValue_zero (Y : Finset ι) (x : ι → R) :
    elementaryValue Y x 0 = 1 := by
  simp [elementaryValue]

theorem elementaryValue_eq_zero_of_card_lt (Y : Finset ι) (x : ι → R)
    {d : ℕ} (hd : Y.card < d) : elementaryValue Y x d = 0 := by
  simp [elementaryValue, Finset.powersetCard_eq_empty.mpr hd]

theorem elementaryValue_map {S : Type*} [CommRing S] (f : R →+* S)
    (Y : Finset ι) (x : ι → R) (d : ℕ) :
    f (elementaryValue Y x d) = elementaryValue Y (f ∘ x) d := by
  simp only [elementaryValue, map_sum, map_prod, Function.comp_apply]

theorem eval₂_elementaryOn {S : Type*} [CommRing S] (f : R →+* S)
    {n : ℕ} (x : Fin n → S) (Y : Finset (Fin n)) (d : ℕ) :
    MvPolynomial.eval₂ f x (elementaryOn (R := R) Y d) =
      elementaryValue Y x d := by
  simp only [elementaryOn, elementaryValue, MvPolynomial.eval₂_sum,
    MvPolynomial.eval₂_prod, MvPolynomial.eval₂_X]

def coordinateCharacteristic (Y : Finset ι) (x : ι → R) : Polynomial R :=
  ∏ i ∈ Y, (Polynomial.X - Polynomial.C (x i))

theorem coordinateCharacteristic_monic (Y : Finset ι) (x : ι → R) :
    (coordinateCharacteristic Y x).Monic := Polynomial.monic_prod_X_sub_C x Y

theorem coordinateCharacteristic_map {S : Type*} [CommRing S] (f : R →+* S)
    (Y : Finset ι) (x : ι → R) :
    Polynomial.map f (coordinateCharacteristic Y x) =
      coordinateCharacteristic Y (f ∘ x) := by
  simp only [coordinateCharacteristic, Polynomial.map_prod, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, Function.comp_apply]

theorem coordinateCharacteristic_coeff (Y : Finset ι) (x : ι → R) (d : ℕ) :
    (coordinateCharacteristic Y x).coeff d =
      if d ≤ Y.card then (-1) ^ (Y.card - d) * elementaryValue Y x (Y.card - d)
      else 0 := by
  classical
  rw [coordinateCharacteristic, Finset.prod_sub, Polynomial.finsetSum_coeff]
  have hterm (A : Finset ι) (hA : A ∈ Y.powerset) :
      (((-1 : Polynomial R) ^ A.card *
        (∏ i ∈ Y \ A, Polynomial.X) * ∏ i ∈ A, Polynomial.C (x i))).coeff d =
      if Y.card - A.card = d then (-1) ^ A.card * ∏ i ∈ A, x i else 0 := by
    have hAY : A ⊆ Y := Finset.mem_powerset.mp hA
    rw [Finset.prod_const, Finset.card_sdiff_of_subset hAY, ← map_prod]
    have hp : (-1 : Polynomial R) ^ A.card *
        Polynomial.X ^ (Y.card - A.card) * Polynomial.C (∏ i ∈ A, x i) =
        Polynomial.C ((-1 : R) ^ A.card * ∏ i ∈ A, x i) *
          Polynomial.X ^ (Y.card - A.card) := by
      simp only [map_mul, map_pow, map_neg, map_one]
      ring
    rw [hp, Polynomial.coeff_C_mul_X_pow]
    simp only [eq_comm]
  simp_rw [Finset.sum_congr rfl hterm]
  by_cases hd : d ≤ Y.card
  · rw [if_pos hd, elementaryValue, Finset.powersetCard_eq_filter,
      Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A hA
    have hc : A.card ≤ Y.card := Finset.card_le_card (Finset.mem_powerset.mp hA)
    by_cases he : A.card = Y.card - d
    · have hsub : Y.card - A.card = d := by omega
      simp [he, hsub, Nat.sub_sub_self hd]
    · have hsub : Y.card - A.card ≠ d := by omega
      simp [he, hsub, Nat.sub_sub_self hd]
  · rw [if_neg hd]
    apply Finset.sum_eq_zero
    intro A hA
    have hsub : Y.card - A.card ≠ d := by omega
    simp [hsub]

theorem coordinateCharacteristic_coeff_card_sub (Y : Finset ι) (x : ι → R)
    {d : ℕ} (hd : d ≤ Y.card) :
    (coordinateCharacteristic Y x).coeff (Y.card - d) =
      (-1) ^ d * elementaryValue Y x d := by
  rw [coordinateCharacteristic_coeff, if_pos (Nat.sub_le _ _), Nat.sub_sub_self hd]

theorem coordinateCharacteristic_eval_root [DecidableEq ι] (Y : Finset ι)
    (x : ι → R) {i : ι} (hi : i ∈ Y) :
    Polynomial.eval (x i) (coordinateCharacteristic Y x) = 0 := by
  rw [coordinateCharacteristic, Polynomial.eval_prod]
  apply Finset.prod_eq_zero hi
  simp

theorem coordinateCharacteristic_union [DecidableEq ι]
    (A B : Finset ι) (hAB : Disjoint A B) (x : ι → R) :
    coordinateCharacteristic (A ∪ B) x =
      coordinateCharacteristic A x * coordinateCharacteristic B x :=
  Finset.prod_union hAB

theorem coordinateCharacteristic_eq_X_pow_of_elementary
    (Y : Finset ι) (x : ι → R)
    (hx : ∀ d : ℕ, 0 < d → elementaryValue Y x d = 0) :
    coordinateCharacteristic Y x = Polynomial.X ^ Y.card := by
  ext d
  rw [coordinateCharacteristic_coeff, Polynomial.coeff_X_pow]
  by_cases hd : d = Y.card
  · simp [hd]
  · by_cases hle : d ≤ Y.card
    · rw [if_pos hle, hx _ (by omega), mul_zero, if_neg hd]
    · simp [hle, hd]

end HigherSpecht
end
end CanonicalSource0

section CanonicalSource1
/- Source: HigherSpecht/SpecialFiberIdeal.lean -/



/-!
# The integral special-fiber ideal identity

Adjoining `m` parts equal to one changes only the first conjugate part.
Every proper-variable elementary generator is therefore unchanged, while
the full-variable generators acquire exactly `e₁,…,eₘ`.  This proves the
ideal identity in Proposition 6.3 over an arbitrary commutative ring.

The separate catabolizability equivalence in that proposition is not built
into this ideal identity.
-/

noncomputable section

open Finset TauCeti MvPolynomial

namespace HigherSpecht

def adjoinOnes (μ : YoungDiagram) (m : ℕ) : YoungDiagram where
  cells := μ.cells ∪ (Finset.range (μ.colLen 0 + m) ×ˢ {0})
  isLowerSet := by
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨hac, hbd⟩ h
    rcases Finset.mem_union.mp h with h | h
    · exact Finset.mem_union_left _ (μ.isLowerSet ⟨hac, hbd⟩ h)
    · apply Finset.mem_union_right
      simp only [Finset.mem_product, Finset.mem_range, Finset.mem_singleton] at h ⊢
      exact ⟨hac.trans_lt h.1, by omega⟩

@[simp] theorem mem_adjoinOnes (μ : YoungDiagram) (m : ℕ) (c : ℕ × ℕ) :
    c ∈ adjoinOnes μ m ↔ c ∈ μ ∨ c.1 < μ.colLen 0 + m ∧ c.2 = 0 := by
  change c ∈ μ.cells ∪ (Finset.range (μ.colLen 0 + m) ×ˢ {0}) ↔ _
  simp only [Finset.mem_union, Finset.mem_product, Finset.mem_range,
    Finset.mem_singleton, YoungDiagram.mem_cells]

theorem le_adjoinOnes (μ : YoungDiagram) (m : ℕ) : μ ≤ adjoinOnes μ m := by
  intro c hc
  exact (mem_adjoinOnes μ m c).mpr (Or.inl hc)

@[simp] theorem adjoinOnes_colLen_zero (μ : YoungDiagram) (m : ℕ) :
    (adjoinOnes μ m).colLen 0 = μ.colLen 0 + m := by
  apply eq_of_forall_lt_iff
  intro r
  rw [← YoungDiagram.mem_iff_lt_colLen, mem_adjoinOnes,
    YoungDiagram.mem_iff_lt_colLen]
  omega

theorem adjoinOnes_colLen_of_pos (μ : YoungDiagram) (m : ℕ) {j : ℕ} (hj : 0 < j) :
    (adjoinOnes μ m).colLen j = μ.colLen j := by
  apply eq_of_forall_lt_iff
  intro r
  rw [← YoungDiagram.mem_iff_lt_colLen, mem_adjoinOnes,
    YoungDiagram.mem_iff_lt_colLen]
  omega

theorem columnTail_adjoinOnes_of_pos (μ : YoungDiagram) (m : ℕ) {h : ℕ} (hh : 0 < h) :
    columnTail (adjoinOnes μ m) h = columnTail μ h := by
  apply congrArg Finset.card
  apply Finset.ext
  intro c
  simp only [Finset.mem_filter, YoungDiagram.mem_cells]
  rw [mem_adjoinOnes]
  constructor
  · rintro ⟨hc, hpos⟩
    rcases hc with hc | hc
    · exact ⟨hc, hpos⟩
    · omega
  · rintro ⟨hc, hpos⟩
    exact ⟨Or.inl hc, hpos⟩

@[simp] theorem adjoinOnes_card (μ : YoungDiagram) (m : ℕ) :
    (adjoinOnes μ m).card = μ.card + m := by
  have hμ := columnTail_succ μ 0
  have hν := columnTail_succ (adjoinOnes μ m) 0
  rw [columnTail_zero] at hμ hν
  rw [adjoinOnes_colLen_zero, columnTail_adjoinOnes_of_pos μ m (by omega)] at hν
  omega

def elementaryParameterIdeal (R : Type*) [CommRing R] (n m : ℕ) :
    Ideal (PolynomialRing n R) :=
  Ideal.span (Set.range fun i : Fin m => MvPolynomial.esymm (Fin n) R (i.val + 1))

variable {R : Type*} [CommRing R]

theorem elementaryOn_univ_mem_parameterIdeal {n m d : ℕ} (hd : 0 < d) (hm : d ≤ m) :
    elementaryOn (R := R) (Finset.univ : Finset (Fin n)) d ∈
      elementaryParameterIdeal R n m := by
  apply Ideal.subset_span
  refine ⟨⟨d - 1, by omega⟩, ?_⟩
  change MvPolynomial.esymm (Fin n) R (d - 1 + 1) = elementaryOn Finset.univ d
  rw [show d - 1 + 1 = d by omega]
  rfl

/-- Proposition 6.3's ideal equality, over the integers and uniformly after
any coefficient change.  The ambient dimension is the exact cardinality of
the enlarged partition, as proved by `adjoinOnes_card`. -/
theorem specialFiberIdeal_eq (μ : YoungDiagram) (m : ℕ) :
    untruncatedIdeal R (μ.card + m) (adjoinOnes μ m) =
      untruncatedIdeal R (μ.card + m) μ ⊔ elementaryParameterIdeal R (μ.card + m) m := by
  let n := μ.card + m
  have hμ : μ.card ≤ n := Nat.le_add_right _ _
  have hν : (adjoinOnes μ m).card ≤ n := by simp [n]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro p ⟨Y, d, hd, hcard, hthreshold, rfl⟩
    by_cases hY : Y = Finset.univ
    · subst Y
      by_cases hdm : d ≤ m
      · exact Ideal.mem_sup_right (elementaryOn_univ_mem_parameterIdeal hd hdm)
      · apply Ideal.mem_sup_left
        apply elementaryOn_mem_untruncatedIdeal _ hd hcard
        rw [← columnTail_eq_conjugateTail μ hμ, Finset.card_univ,
          Fintype.card_fin, Nat.sub_self, columnTail_zero]
        omega
    · have hYcard : Y.card < n := by
        simpa only [Finset.card_univ, Fintype.card_fin] using
          Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hY)
      have hcut : 0 < n - Y.card := by omega
      apply Ideal.mem_sup_left
      apply elementaryOn_mem_untruncatedIdeal Y hd hcard
      rw [← columnTail_eq_conjugateTail _ hν,
        columnTail_adjoinOnes_of_pos μ m hcut, columnTail_eq_conjugateTail μ hμ] at hthreshold
      exact hthreshold
  · apply sup_le
    · exact untruncatedIdeal_mono (le_adjoinOnes μ m)
    · apply Ideal.span_le.mpr
      rintro p ⟨i, rfl⟩
      change elementaryOn (R := R) (Finset.univ : Finset (Fin n)) (i.val + 1) ∈ _
      apply elementaryOn_mem_untruncatedIdeal _ (Nat.succ_pos _) (by
        simp only [Finset.card_univ, Fintype.card_fin]
        have := i.isLt
        dsimp [n]
        omega)
      rw [← columnTail_eq_conjugateTail _ hν, Finset.card_univ, Fintype.card_fin,
        Nat.sub_self, columnTail_zero, adjoinOnes_card]
      omega

end HigherSpecht
end
end CanonicalSource1

section CanonicalSource2
/- Source: HigherSpecht/FiberCharacteristic.lean -/



/-!
# The exact parameter fiber and its finite-dimensionality

The fiber is the quotient by the original elementary ideal and the equations
`e_j = a_j`.  A monic parameter polynomial is encoded by its signed
coefficients.  Its coordinate characteristic identity is proved coefficient
by coefficient, with all elementary functions above the parameter range
vanishing by the original ideal.  Every coordinate is consequently integral.
Thus the finite-dimensionality used in Theorem 7.1 is established directly,
without assuming a higher Specht basis, a rank formula, or parameter freeness.
-/

noncomputable section

open Finset MvPolynomial TauCeti

namespace HigherSpecht

variable {R : Type*} [CommRing R]

def parameterFiberIdeal (R : Type*) [CommRing R] (n : ℕ) (lam : YoungDiagram)
    (m : ℕ) (a : Fin m → R) : Ideal (PolynomialRing n R) :=
  untruncatedIdeal R n lam ⊔
    Ideal.span (Set.range fun i : Fin m =>
      elementaryOn (Finset.univ : Finset (Fin n)) (i.val + 1) - MvPolynomial.C (a i))

abbrev ParameterFiber (R : Type*) [CommRing R] (n : ℕ) (lam : YoungDiagram)
    (m : ℕ) (a : Fin m → R) :=
  PolynomialRing n R ⧸ parameterFiberIdeal R n lam m a

/-- The coefficient tuple of `t^m-a₁t^(m-1)+⋯+(-1)^m aₘ`. -/
def polynomialParameters (Q : Polynomial R) (m : ℕ) (i : Fin m) : R :=
  (-1) ^ (i.val + 1) * Q.coeff (m - (i.val + 1))

def polynomialFiberIdeal (R : Type*) [CommRing R] (n : ℕ)
    (lam : YoungDiagram) (m : ℕ) (Q : Polynomial R) : Ideal (PolynomialRing n R) :=
  parameterFiberIdeal R n lam m (polynomialParameters Q m)

abbrev PolynomialFiber (R : Type*) [CommRing R] (n : ℕ) (lam : YoungDiagram)
    (m : ℕ) (Q : Polynomial R) :=
  PolynomialRing n R ⧸ polynomialFiberIdeal R n lam m Q

def fiberCoordinate {n m : ℕ} {lam : YoungDiagram} {Q : Polynomial R}
    (i : Fin n) : PolynomialFiber R n lam m Q :=
  Ideal.Quotient.mk _ (MvPolynomial.X i)

theorem fiber_elementary_parameter {n m : ℕ} {lam : YoungDiagram}
    (a : Fin m → R) (i : Fin m) :
    Ideal.Quotient.mk (parameterFiberIdeal R n lam m a)
        (elementaryOn (Finset.univ : Finset (Fin n)) (i.val + 1)) =
      algebraMap R (ParameterFiber R n lam m a) (a i) := by
  apply sub_eq_zero.mp
  change Ideal.Quotient.mk (parameterFiberIdeal R n lam m a)
      (elementaryOn (Finset.univ : Finset (Fin n)) (i.val + 1)) -
    Ideal.Quotient.mk (parameterFiberIdeal R n lam m a) (MvPolynomial.C (a i)) = 0
  rw [← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))

theorem elementaryOn_univ_mem_untruncated_of_parameter_lt
    {n m : ℕ} {lam : YoungDiagram} (hsize : lam.card + m = n)
    {d : ℕ} (hd : m < d) :
    elementaryOn (R := R) (Finset.univ : Finset (Fin n)) d ∈
      untruncatedIdeal R n lam := by
  by_cases hdn : d ≤ n
  · apply elementaryOn_mem_untruncatedIdeal _ (by omega)
      (by simpa using hdn)
    rw [← columnTail_eq_conjugateTail lam (by omega : lam.card ≤ n),
      Finset.card_univ, Fintype.card_fin, Nat.sub_self, columnTail_zero]
    omega
  · rw [elementaryOn_eq_zero_of_card_lt (by simpa using Nat.lt_of_not_ge hdn)]
    exact Ideal.zero_mem _

theorem fiber_elementary_above_parameter {n m : ℕ} {lam : YoungDiagram}
    (hsize : lam.card + m = n) (a : Fin m → R) {d : ℕ} (hd : m < d) :
    Ideal.Quotient.mk (parameterFiberIdeal R n lam m a)
      (elementaryOn (Finset.univ : Finset (Fin n)) d) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left
    (elementaryOn_univ_mem_untruncated_of_parameter_lt hsize hd))

theorem polynomialFiber_elementary {n m : ℕ} {lam : YoungDiagram}
    (hsize : lam.card + m = n) (Q : Polynomial R) {d : ℕ}
    (hd : 0 < d) (hdm : d ≤ m) :
    Ideal.Quotient.mk (polynomialFiberIdeal R n lam m Q)
        (elementaryOn (Finset.univ : Finset (Fin n)) d) =
      algebraMap R (PolynomialFiber R n lam m Q)
        ((-1) ^ d * Q.coeff (m - d)) := by
  let i : Fin m := ⟨d - 1, by omega⟩
  have hi : i.val + 1 = d := by dsimp [i]; omega
  have h := fiber_elementary_parameter (n := n) (lam := lam) (polynomialParameters Q m) i
  have hp : polynomialParameters Q m i = (-1) ^ d * Q.coeff (m - d) := by
    dsimp only [polynomialParameters]
    rw [hi]
  rw [hi, hp] at h
  exact h

theorem polynomialFiber_elementaryValue {n m : ℕ} {lam : YoungDiagram}
    (Q : Polynomial R) (d : ℕ) :
    elementaryValue Finset.univ (fiberCoordinate (n := n) (lam := lam) (m := m) (Q := Q)) d =
      Ideal.Quotient.mk (polynomialFiberIdeal R n lam m Q)
        (elementaryOn (Finset.univ : Finset (Fin n)) d) := by
  simp only [elementaryValue, elementaryOn, fiberCoordinate, map_sum, map_prod]

/-- The literal characteristic-polynomial relation of the fiber.  It includes
all repeated-root and positive-characteristic cases. -/
theorem polynomialFiber_characteristic {n m : ℕ} {lam : YoungDiagram}
    (hsize : lam.card + m = n) (Q : Polynomial R)
    (hQ : Q.Monic) (hdeg : Q.natDegree = m) :
    coordinateCharacteristic Finset.univ
        (fiberCoordinate (n := n) (lam := lam) (m := m) (Q := Q)) =
      Polynomial.X ^ lam.card *
        Polynomial.map (algebraMap R (PolynomialFiber R n lam m Q)) Q := by
  ext d
  rw [coordinateCharacteristic_coeff, Finset.card_univ, Fintype.card_fin,
    Polynomial.coeff_X_pow_mul']
  by_cases hdn : d ≤ n
  · rw [if_pos hdn, polynomialFiber_elementaryValue]
    by_cases hdk : lam.card ≤ d
    · rw [if_pos hdk, Polynomial.coeff_map]
      by_cases hdtop : d = n
      · subst d
        rw [Nat.sub_self, elementaryOn_zero, map_one, pow_zero, one_mul,
          show n - lam.card = m by omega]
        rw [← hdeg, Polynomial.coeff_natDegree, hQ, map_one]
      · have hj : 0 < n - d := by omega
        have hjm : n - d ≤ m := by omega
        rw [polynomialFiber_elementary hsize Q hj hjm, map_mul, map_pow, map_neg,
          map_one]
        rw [show m - (n - d) = d - lam.card by omega]
        have hs : ((-1 : PolynomialFiber R n lam m Q) ^ (n - d)) *
            (-1) ^ (n - d) = 1 := by
          have hneg : (-1 : PolynomialFiber R n lam m Q) * (-1) = 1 := by ring
          rw [← mul_pow, hneg, one_pow]
        rw [← mul_assoc, hs, one_mul]
    · rw [if_neg hdk]
      have hjm : m < n - d := by omega
      rw [show Ideal.Quotient.mk (polynomialFiberIdeal R n lam m Q)
          (elementaryOn (Finset.univ : Finset (Fin n)) (n - d)) = 0 from
        fiber_elementary_above_parameter hsize (polynomialParameters Q m) hjm,
        mul_zero]
  · rw [if_neg hdn]
    have hdk : lam.card ≤ d := by omega
    rw [if_pos hdk, Polynomial.coeff_map,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]

/-- Every genuine fiber coordinate satisfies the common monic relation. -/
theorem polynomialFiber_coordinate_isIntegral {n m : ℕ} {lam : YoungDiagram}
    (hsize : lam.card + m = n) (Q : Polynomial R)
    (hQ : Q.Monic) (hdeg : Q.natDegree = m) (i : Fin n) :
    IsIntegral R (fiberCoordinate (n := n) (lam := lam) (m := m) (Q := Q) i) := by
  refine ⟨Polynomial.X ^ lam.card * Q, (Polynomial.monic_X_pow _).mul hQ, ?_⟩
  change Polynomial.eval₂ (algebraMap R (PolynomialFiber R n lam m Q))
    (fiberCoordinate i) (Polynomial.X ^ lam.card * Q) = 0
  rw [Polynomial.eval₂_eq_eval_map]
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
  rw [← polynomialFiber_characteristic hsize Q hQ hdeg]
  exact coordinateCharacteristic_eval_root _ _ (Finset.mem_univ i)

/-- Finite-dimensionality follows from the actual coordinate relations.  In
particular this theorem has no free-basis or dimension premise. -/
theorem polynomialFiber_moduleFinite {n m : ℕ} {lam : YoungDiagram}
    (hsize : lam.card + m = n) (Q : Polynomial R)
    (hQ : Q.Monic) (hdeg : Q.natDegree = m) :
    Module.Finite R (PolynomialFiber R n lam m Q) := by
  letI : Algebra.IsIntegral R (PolynomialFiber R n lam m Q) := by
    constructor
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction p using MvPolynomial.induction_on with
    | C r => exact isIntegral_algebraMap
    | add p q hp hq => simpa only [map_add] using hp.add hq
    | mul_X p i hp =>
      rw [map_mul]
      exact hp.mul (polynomialFiber_coordinate_isIntegral hsize Q hQ hdeg i)
  exact Algebra.IsIntegral.finite

theorem polynomialFiber_isArtinian {K : Type*} [Field K]
    {n m : ℕ} {lam : YoungDiagram} (hsize : lam.card + m = n)
    (Q : Polynomial K) (hQ : Q.Monic) (hdeg : Q.natDegree = m) :
    IsArtinianRing (PolynomialFiber K n lam m Q) := by
  letI := polynomialFiber_moduleFinite hsize Q hQ hdeg
  exact IsArtinianRing.of_finite K _

end HigherSpecht
end
end CanonicalSource2

section CanonicalSource3
/- Source: HigherSpecht/PolynomialNilpotentFactorization.lean -/



/-!
# Uniqueness of a coprime monic factorization through a nilpotent ideal

Nilpotent perturbations preserve a Bezout identity after multiplying it by a
unit. Thus each old factor is coprime to all the other new factors. Equality
of the products implies divisibility of the corresponding factors, and equal
degrees and monicity imply equality. This proves uniqueness directly over any
commutative coefficient ring; it does not assume a Hensel lifting theorem or
the existence of a factorization not displayed in the hypotheses.
-/

namespace HigherSpecht

open scoped BigOperators Polynomial

variable {R : Type*} [CommRing R]

/-- A nilpotent change of the second argument preserves coprimality. -/
theorem isCoprime_of_nilpotent_difference {x y z : R}
    (hxy : IsCoprime x y) (hzy : IsNilpotent (z - y)) : IsCoprime x z := by
  obtain ⟨a, b, hab⟩ := hxy
  have hnil : IsNilpotent (b * (z - y)) :=
    (Commute.all b (z - y)).isNilpotent_mul_left hzy
  have hu : IsUnit (a * x + b * z) := by
    convert hnil.isUnit_one_add using 1
    rw [← hab]
    ring
  obtain ⟨c, hc⟩ := isUnit_iff_exists_inv'.mp hu
  refine ⟨c * a, c * b, ?_⟩
  calc
    c * a * x + c * b * z = c * (a * x + b * z) := by ring
    _ = 1 := hc

/-- Every element of an explicitly nilpotent ideal is nilpotent. -/
theorem isNilpotent_of_mem_nilpotent_ideal {N : Ideal R}
    (hN : IsNilpotent N) {x : R} (hx : x ∈ N) : IsNilpotent x := by
  obtain ⟨e, he⟩ := hN
  refine ⟨e, ?_⟩
  have hpow := Ideal.pow_mem_pow hx e
  rw [he] at hpow
  simpa using hpow

/-- The coefficient condition refers to the actual polynomial difference. -/
theorem polynomial_nilpotent_of_coeff_mem {N : Ideal R} (hN : IsNilpotent N)
    {f : R[X]} (hf : ∀ k, f.coeff k ∈ N) : IsNilpotent f :=
  Polynomial.isNilpotent_iff.mpr (fun k => isNilpotent_of_mem_nilpotent_ideal hN (hf k))

/-- Factorwise uniqueness under nilpotent coefficient perturbation. The
finite indexing set and all degrees are unrestricted. -/
theorem monic_factorization_unique_of_nilpotent_coeff
    {ι : Type*} [Fintype ι] (p q : ι → R[X])
    (hp : ∀ i, (p i).Monic) (hq : ∀ i, (q i).Monic)
    (hdegree : ∀ i, (q i).natDegree = (p i).natDegree)
    (hcoprime : Pairwise (fun i j => IsCoprime (p i) (p j)))
    (hcoeff : ∀ i k, IsNilpotent ((q i - p i).coeff k))
    (hproduct : (∏ i, q i) = ∏ i, p i) : ∀ i, q i = p i := by
  classical
  intro i
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le (hp i) (hq i) ?_ (hdegree i).le
  have hothers : IsCoprime (p i) (∏ j ∈ Finset.univ.erase i, q j) := by
    apply IsCoprime.prod_right
    intro j hj
    exact isCoprime_of_nilpotent_difference
      (hcoprime (Finset.mem_erase.mp hj).1.symm)
      (Polynomial.isNilpotent_iff.mpr (hcoeff j))
  apply hothers.dvd_of_dvd_mul_right
  rw [Finset.mul_prod_erase Finset.univ q (Finset.mem_univ i), hproduct]
  exact Finset.dvd_prod_of_mem p (Finset.mem_univ i)

/-- The ideal version uses literal coefficientwise congruence, with the
nilpotence of the ideal proved or supplied independently of the factors. -/
theorem monic_factorization_unique_of_coeff_congr
    {ι : Type*} [Fintype ι] (N : Ideal R) (hN : IsNilpotent N)
    (p q : ι → R[X]) (hp : ∀ i, (p i).Monic) (hq : ∀ i, (q i).Monic)
    (hdegree : ∀ i, (q i).natDegree = (p i).natDegree)
    (hcoprime : Pairwise (fun i j => IsCoprime (p i) (p j)))
    (hcongr : ∀ i k, (q i).coeff k - (p i).coeff k ∈ N)
    (hproduct : (∏ i, q i) = ∏ i, p i) : ∀ i, q i = p i := by
  apply monic_factorization_unique_of_nilpotent_coeff p q hp hq hdegree hcoprime
    (fun i k => ?_) hproduct
  rw [Polynomial.coeff_sub]
  exact isNilpotent_of_mem_nilpotent_ideal hN (hcongr i k)

/-- Equivalently, the two displayed monic factorizations have the same
reductions in the polynomial ring over the actual quotient by the ideal. -/
theorem monic_factorization_unique_mod_nilpotent_ideal
    {ι : Type*} [Fintype ι] (N : Ideal R) (hN : IsNilpotent N)
    (p q : ι → R[X]) (hp : ∀ i, (p i).Monic) (hq : ∀ i, (q i).Monic)
    (hdegree : ∀ i, (q i).natDegree = (p i).natDegree)
    (hcoprime : Pairwise (fun i j => IsCoprime (p i) (p j)))
    (hcongr : ∀ i, (q i).map (Ideal.Quotient.mk N) =
      (p i).map (Ideal.Quotient.mk N))
    (hproduct : (∏ i, q i) = ∏ i, p i) : ∀ i, q i = p i := by
  apply monic_factorization_unique_of_coeff_congr N hN p q hp hq hdegree hcoprime
    (fun i k => ?_) hproduct
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  simpa only [Polynomial.coeff_map] using congrArg (fun f => f.coeff k) (hcongr i)

end HigherSpecht
end CanonicalSource3

section CanonicalSource4
/- Source: HigherSpecht/FiberMultiplicity.lean -/



/-!
# Exact root multiplicities on a nonzero nilpotent fiber component

Reduction modulo a nilpotent ideal of a nonzero algebra preserves a copy of
the coefficient field. The actual coordinate characteristic identity therefore
becomes an equality of polynomials over that field. Taking root multiplicities
proves the size of every assigned root group, without a dimension formula,
parameter freeness, or a pre-assumed multiplicity condition.
-/

noncomputable section
open scoped BigOperators Polynomial Classical

namespace HigherSpecht

variable {K : Type*} [Field K]

theorem rootMultiplicity_finset_product {ι : Type*} (z : K)
    (s : Finset ι) (p : ι → K[X]) (hp : ∀ i ∈ s, p i ≠ 0) :
    Polynomial.rootMultiplicity z (∏ i ∈ s, p i) =
      ∑ i ∈ s, Polynomial.rootMultiplicity z (p i) := by
  classical
  revert hp
  induction s using Finset.induction_on with
  | empty => intro hp; simp
  | @insert i s hi ih =>
      intro hp
      have hpi := hp i (Finset.mem_insert_self i s)
      have hps : ∀ j ∈ s, p j ≠ 0 :=
        fun j hj => hp j (Finset.mem_insert_of_mem hj)
      rw [Finset.prod_insert hi, Finset.sum_insert hi,
        Polynomial.rootMultiplicity_mul (mul_ne_zero hpi (Finset.prod_ne_zero_iff.mpr hps)),
        ih hps]

theorem rootMultiplicity_assigned_linear_product
    {σ ι : Type*} [Fintype σ] (c : ι → K) (hc : Function.Injective c)
    (f : σ → ι) (i : ι) :
    Polynomial.rootMultiplicity (c i)
        (∏ j : σ, (Polynomial.X - Polynomial.C (c (f j)))) =
      Fintype.card {j : σ // f j = i} := by
  rw [rootMultiplicity_finset_product _ _ _
    (fun j _ => Polynomial.X_sub_C_ne_zero (c (f j)))]
  calc
    (∑ j : σ, Polynomial.rootMultiplicity (c i)
        (Polynomial.X - Polynomial.C (c (f j)))) =
        ∑ j : σ, if f j = i then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Polynomial.rootMultiplicity_X_sub_C, hc.eq_iff, eq_comm]
    _ = Fintype.card {j : σ // f j = i} := by
      simp only [Finset.sum_boole, Fintype.card_subtype, Nat.cast_id]

theorem rootMultiplicity_distinct_root_powers
    {ι : Type*} [Fintype ι] (c : ι → K) (hc : Function.Injective c)
    (r : ι → ℕ) (i : ι) :
    Polynomial.rootMultiplicity (c i)
        (∏ j : ι, (Polynomial.X - Polynomial.C (c j)) ^ r j) = r i := by
  rw [rootMultiplicity_finset_product _ _ _
    (fun j _ => pow_ne_zero (r j) (Polynomial.X_sub_C_ne_zero (c j)))]
  have hterm (j : ι) :
      Polynomial.rootMultiplicity (c i) ((Polynomial.X - Polynomial.C (c j)) ^ r j) =
        if j = i then r j else 0 := by
    by_cases hji : j = i
    · subst j
      simp only [if_pos rfl, if_true, Polynomial.rootMultiplicity_X_sub_C_pow]
    · rw [if_neg hji]
      apply Polynomial.rootMultiplicity_eq_zero
      change Polynomial.eval (c i) ((Polynomial.X - Polynomial.C (c j)) ^ r j) ≠ 0
      simp only [Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C]
      exact pow_ne_zero (r j) (sub_ne_zero.mpr (fun h => hji (hc h).symm))
  simp_rw [hterm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

variable {A : Type*} [CommRing A] [Nontrivial A] [Algebra K A]

/-- Nilpotence excludes the zero quotient in a nonzero coefficient algebra. -/
theorem nilpotent_ideal_ne_top (N : Ideal A) (hN : IsNilpotent N) : N ≠ ⊤ := by
  intro htop
  have hnil : IsNilpotent (1 : A) :=
    isNilpotent_of_mem_nilpotent_ideal hN (by simp [htop])
  exact hnil.not_isUnit isUnit_one

/-- Reflect the exact coordinate characteristic identity back to the field.
The map out of the field is proved injective after establishing that the
nilpotent quotient is nontrivial. -/
theorem constant_root_products_eq_of_nilpotent_reduction
    {σ ι : Type*} [Fintype σ] [Fintype ι]
    (N : Ideal A) (hN : IsNilpotent N) (c : ι → K) (r : ι → ℕ)
    (f : σ → ι) (x : σ → A)
    (hresidue : ∀ j, Ideal.Quotient.mk N (x j) =
      algebraMap K (A ⧸ N) (c (f j)))
    (hproduct : (∏ j : σ, (Polynomial.X - Polynomial.C (x j))) =
      ∏ i : ι, (Polynomial.X - Polynomial.C (algebraMap K A (c i))) ^ r i) :
    (∏ j : σ, (Polynomial.X - Polynomial.C (c (f j)))) =
      ∏ i : ι, (Polynomial.X - Polynomial.C (c i)) ^ r i := by
  letI : Nontrivial (A ⧸ N) :=
    (Ideal.Quotient.nontrivial_iff).mpr (nilpotent_ideal_ne_top N hN)
  apply Polynomial.map_injective (algebraMap K (A ⧸ N)) (algebraMap K (A ⧸ N)).injective
  have hmap := congrArg (Polynomial.map (Ideal.Quotient.mk N)) hproduct
  simpa only [Polynomial.map_prod, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, hresidue, Ideal.Quotient.mk_algebraMap] using hmap

/-- Every nonzero component has exactly the prescribed number of coordinates
at each distinct root. This supplies the equal-degree hypotheses for the
separate monic-factor uniqueness theorem. -/
theorem fiber_root_multiplicities
    {σ ι : Type*} [Fintype σ] [Fintype ι]
    (N : Ideal A) (hN : IsNilpotent N)
    (c : ι → K) (hc : Function.Injective c) (r : ι → ℕ)
    (f : σ → ι) (x : σ → A)
    (hresidue : ∀ j, Ideal.Quotient.mk N (x j) =
      algebraMap K (A ⧸ N) (c (f j)))
    (hproduct : (∏ j : σ, (Polynomial.X - Polynomial.C (x j))) =
      ∏ i : ι, (Polynomial.X - Polynomial.C (algebraMap K A (c i))) ^ r i) :
    ∀ i, Fintype.card {j : σ // f j = i} = r i := by
  have h := constant_root_products_eq_of_nilpotent_reduction N hN c r f x hresidue hproduct
  intro i
  have hi := congrArg (Polynomial.rootMultiplicity (c i)) h
  simpa only [rootMultiplicity_assigned_linear_product c hc f i,
    rootMultiplicity_distinct_root_powers c hc r i] using hi

end HigherSpecht
end
end CanonicalSource4

section CanonicalSource5
/- Source: HigherSpecht/FiberRootGroups.lean -/



/-!
# Exact characteristic polynomials of the assigned root groups

The assignment ideal is generated by the actual coordinate deviations from
the assigned roots.  Finitely many nilpotent deviations make this ideal
nilpotent.  Root multiplicities fix the sizes of the groups, and the actual
coprime-factor uniqueness argument fixes every group characteristic
polynomial.  These are the local identities used in the fiber decomposition.
-/

noncomputable section

open scoped BigOperators Polynomial Classical

namespace HigherSpecht

variable {A : Type*} [CommRing A]
variable {σ ι : Type*} [Fintype σ] [Fintype ι]

def assignedRootIdeal (x : σ → A) (c : ι → A) (f : σ → ι) : Ideal A :=
  Ideal.span (Set.range fun j => x j - c (f j))

theorem assignedRootIdeal_isNilpotent
    (x : σ → A) (c : ι → A) (f : σ → ι)
    (h : ∀ j, IsNilpotent (x j - c (f j))) :
    IsNilpotent (assignedRootIdeal x c f) := by
  have hfg : (assignedRootIdeal x c f).FG := by
    apply Submodule.fg_def.mpr
    exact ⟨Set.range (fun j => x j - c (f j)), Set.finite_range _, rfl⟩
  apply hfg.isNilpotent_iff_le_nilradical.mpr
  apply Ideal.span_le.mpr
  rintro z ⟨j, rfl⟩
  obtain ⟨e, he⟩ := h j
  exact Ideal.mem_radical_iff.mpr ⟨e, (Ideal.mem_bot).mpr he⟩

theorem assignedRootIdeal_residue
    (x : σ → A) (c : ι → A) (f : σ → ι) (j : σ) :
    Ideal.Quotient.mk (assignedRootIdeal x c f) (x j) =
      Ideal.Quotient.mk (assignedRootIdeal x c f) (c (f j)) := by
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  exact Ideal.subset_span ⟨j, rfl⟩

def rootGroupCharacteristic (x : σ → A) (f : σ → ι) (i : ι) : A[X] :=
  ∏ j : {j : σ // f j = i}, (Polynomial.X - Polynomial.C (x j.val))

theorem rootGroupCharacteristic_monic (x : σ → A) (f : σ → ι) (i : ι) :
    (rootGroupCharacteristic x f i).Monic :=
  Polynomial.monic_prod_X_sub_C _ _

theorem rootGroupCharacteristic_natDegree [Nontrivial A]
    (x : σ → A) (f : σ → ι) (i : ι) :
    (rootGroupCharacteristic x f i).natDegree = Fintype.card {j : σ // f j = i} := by
  rw [rootGroupCharacteristic, Polynomial.natDegree_prod_of_monic (R := A)
    (Finset.univ : Finset {j : σ // f j = i})
    (f := fun j => Polynomial.X - Polynomial.C (x j.val))
    (fun j _ => Polynomial.monic_X_sub_C (x j.val))]
  simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one]

theorem prod_rootGroupCharacteristic (x : σ → A) (f : σ → ι) :
    (∏ i, rootGroupCharacteristic x f i) =
      ∏ j : σ, (Polynomial.X - Polynomial.C (x j)) := by
  classical
  exact Fintype.prod_fiberwise f (fun j => Polynomial.X - Polynomial.C (x j))

/-- The explicit groups, rather than unspecified Hensel factors, satisfy
the unique constant-root-power characteristic identities. -/
theorem rootGroupCharacteristic_eq_root_power [Nontrivial A]
    (N : Ideal A) (hN : IsNilpotent N)
    (x : σ → A) (c : ι → A) (f : σ → ι) (r : ι → ℕ)
    (hc : Pairwise fun i j => IsUnit (c i - c j))
    (hcount : ∀ i, Fintype.card {j : σ // f j = i} = r i)
    (hresidue : ∀ j, Ideal.Quotient.mk N (x j) = Ideal.Quotient.mk N (c (f j)))
    (hproduct : (∏ j : σ, (Polynomial.X - Polynomial.C (x j))) =
      ∏ i : ι, (Polynomial.X - Polynomial.C (c i)) ^ r i) :
    ∀ i, rootGroupCharacteristic x f i =
      (Polynomial.X - Polynomial.C (c i)) ^ r i := by
  classical
  apply monic_factorization_unique_mod_nilpotent_ideal N hN
    (fun i => (Polynomial.X - Polynomial.C (c i)) ^ r i)
    (rootGroupCharacteristic x f)
  · intro i
    exact (Polynomial.monic_X_sub_C (c i)).pow (r i)
  · exact rootGroupCharacteristic_monic x f
  · intro i
    rw [rootGroupCharacteristic_natDegree, hcount i,
      (Polynomial.monic_X_sub_C (c i)).natDegree_pow,
      Polynomial.natDegree_X_sub_C, mul_one]
  · intro i j hij
    exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (hc hij)).pow
  · intro i
    rw [rootGroupCharacteristic, Polynomial.map_prod, Polynomial.map_pow,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    have hterm (j : {j : σ // f j = i}) :
        Polynomial.map (Ideal.Quotient.mk N)
            (Polynomial.X - Polynomial.C (x j.val)) =
          Polynomial.X - Polynomial.C (Ideal.Quotient.mk N (c i)) := by
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
        hresidue, j.property]
    simp only [hterm, Finset.prod_const, Finset.card_univ, hcount i]
  · rw [prod_rootGroupCharacteristic]
    exact hproduct

variable {K : Type*} [Field K] [Nontrivial A] [Algebra K A]

/-- A nonzero actual fiber component determines its root multiplicities and
all its group characteristic polynomials; neither is assumed. -/
theorem fiber_assigned_root_groups
    (x : σ → A) (c : ι → K) (hc : Function.Injective c)
    (f : σ → ι) (r : ι → ℕ)
    (hnil : ∀ j, IsNilpotent (x j - algebraMap K A (c (f j))))
    (hproduct : (∏ j : σ, (Polynomial.X - Polynomial.C (x j))) =
      ∏ i : ι, (Polynomial.X - Polynomial.C (algebraMap K A (c i))) ^ r i) :
    (∀ i, Fintype.card {j : σ // f j = i} = r i) ∧
      (∀ i, rootGroupCharacteristic x f i =
        (Polynomial.X - Polynomial.C (algebraMap K A (c i))) ^ r i) := by
  let N := assignedRootIdeal x (fun i => algebraMap K A (c i)) f
  have hN : IsNilpotent N := assignedRootIdeal_isNilpotent _ _ _ hnil
  have hresidue : ∀ j, Ideal.Quotient.mk N (x j) =
      algebraMap K (A ⧸ N) (c (f j)) := by
    intro j
    simpa only [Ideal.Quotient.mk_algebraMap] using
      assignedRootIdeal_residue x (fun i => algebraMap K A (c i)) f j
  have hcount := fiber_root_multiplicities N hN c hc r f x hresidue hproduct
  refine ⟨hcount, ?_⟩
  apply rootGroupCharacteristic_eq_root_power N hN x _ f r ?_ hcount ?_ hproduct
  · intro i j hij
    rw [← map_sub]
    exact (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (hc.ne hij))).map (algebraMap K A)
  · intro j
    exact assignedRootIdeal_residue x (fun i => algebraMap K A (c i)) f j

/-- Every coordinate assigned a nonzero constant root is a unit in the
actual component, since its deviation from that unit is nilpotent. -/
theorem isUnit_of_nilpotent_difference_constant
    {x : A} {c : K} (hc : c ≠ 0)
    (hx : IsNilpotent (x - algebraMap K A c)) : IsUnit x := by
  have hu : IsUnit (algebraMap K A c) :=
    (isUnit_iff_ne_zero.mpr hc).map (algebraMap K A)
  convert hx.isUnit_add_right_of_commute hu (Commute.all _ _) using 1 <;> ring

end HigherSpecht
end
end CanonicalSource5

section CanonicalSource6
/- Source: HigherSpecht/PolynomialTranslation.lean -/



/-!
# Literal coordinate translations and shifted elementary equations

The translations are actual inverse polynomial algebra maps.  A root-group
characteristic identity is equivalent to vanishing of every positive
elementary polynomial in its translated coordinates.  All identities hold
over arbitrary commutative rings.
-/

noncomputable section

open Finset MvPolynomial
open scoped Polynomial BigOperators Classical

namespace HigherSpecht

variable {R : Type*} [CommRing R] {σ : Type*}

def coordinateTranslation (b : σ → R) : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofAlgHom
    (MvPolynomial.aeval fun i => MvPolynomial.X i + MvPolynomial.C (b i))
    (MvPolynomial.aeval fun i => MvPolynomial.X i - MvPolynomial.C (b i))
    (by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, MvPolynomial.aeval_X,
      map_add, map_sub, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, AlgHom.id_apply]; ring)
    (by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, MvPolynomial.aeval_X,
      map_add, map_sub, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, AlgHom.id_apply]; ring)

@[simp] theorem coordinateTranslation_X (b : σ → R) (i : σ) :
    coordinateTranslation b (MvPolynomial.X i) =
      MvPolynomial.X i + MvPolynomial.C (b i) := by
  change MvPolynomial.aeval _ (MvPolynomial.X i) = _
  exact MvPolynomial.aeval_X _ _

@[simp] theorem coordinateTranslation_C (b : σ → R) (r : R) :
    coordinateTranslation b (MvPolynomial.C r) = MvPolynomial.C r := by
  exact (coordinateTranslation b).commutes r

theorem coordinateTranslation_neg (b : σ → R) :
    (coordinateTranslation b).symm = coordinateTranslation (-b) := by
  apply AlgEquiv.coe_toAlgHom_injective
  simp only [coordinateTranslation, AlgEquiv.ofAlgHom_symm,
    AlgEquiv.toAlgHom_ofAlgHom]
  apply MvPolynomial.algHom_ext
  intro i
  simp only [MvPolynomial.aeval_X, Pi.neg_apply, map_neg, sub_eq_add_neg]

theorem coordinateCharacteristic_sub (Y : Finset σ) (x : σ → R) (c : R) :
    coordinateCharacteristic Y (fun i => x i - c) =
      (coordinateCharacteristic Y x).comp (Polynomial.X + Polynomial.C c) := by
  unfold coordinateCharacteristic
  rw [Polynomial.prod_comp]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp,
    map_sub]
  ring

theorem elementaryValue_eq_zero_of_coordinateCharacteristic
    (Y : Finset σ) (x : σ → R)
    (h : coordinateCharacteristic Y x = Polynomial.X ^ Y.card)
    {d : ℕ} (hd : 0 < d) : elementaryValue Y x d = 0 := by
  by_cases hdY : d ≤ Y.card
  · have hc := congrArg (fun p : R[X] => p.coeff (Y.card - d)) h
    rw [coordinateCharacteristic_coeff_card_sub Y x hdY] at hc
    have hne : Y.card - d ≠ Y.card := by omega
    rw [Polynomial.coeff_X_pow, if_neg hne] at hc
    have hu : IsUnit ((-1 : R) ^ d) := isUnit_neg_one.pow d
    exact hu.mul_left_cancel (by simpa only [mul_zero] using hc)
  · exact elementaryValue_eq_zero_of_card_lt Y x (Nat.lt_of_not_ge hdY)

theorem elementaryValue_sub_eq_zero_of_root_power
    (Y : Finset σ) (x : σ → R) (c : R)
    (h : coordinateCharacteristic Y x = (Polynomial.X - Polynomial.C c) ^ Y.card)
    {d : ℕ} (hd : 0 < d) : elementaryValue Y (fun i => x i - c) d = 0 := by
  apply elementaryValue_eq_zero_of_coordinateCharacteristic Y _ ?_ hd
  rw [coordinateCharacteristic_sub, h, Polynomial.pow_comp,
    Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
  simp only [add_sub_cancel_right]

theorem coordinateCharacteristic_eq_root_power_of_shifted_elementary
    (Y : Finset σ) (x : σ → R) (c : R)
    (h : ∀ d : ℕ, 0 < d → elementaryValue Y (fun i => x i - c) d = 0) :
    coordinateCharacteristic Y x = (Polynomial.X - Polynomial.C c) ^ Y.card := by
  have hs := coordinateCharacteristic_eq_X_pow_of_elementary Y
    (fun i => x i - c) h
  calc
    coordinateCharacteristic Y x =
        (coordinateCharacteristic Y (fun i => x i - c)).comp
          (Polynomial.X - Polynomial.C c) := by
      unfold coordinateCharacteristic
      rw [Polynomial.prod_comp]
      apply Finset.prod_congr rfl
      intro i hi
      simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp,
        map_sub]
      ring
    _ = (Polynomial.X - Polynomial.C c) ^ Y.card := by
      rw [hs, Polynomial.pow_comp, Polynomial.X_comp]

variable [Fintype σ] {ι : Type*} [Fintype ι]

def rootGroupFinset (f : σ → ι) (i : ι) : Finset σ :=
  Finset.univ.filter fun j => f j = i

@[simp] theorem mem_rootGroupFinset (f : σ → ι) (i : ι) (j : σ) :
    j ∈ rootGroupFinset f i ↔ f j = i := by
  simp only [rootGroupFinset, Finset.mem_filter, Finset.mem_univ, true_and]

theorem rootGroupFinset_card (f : σ → ι) (i : ι) :
    (rootGroupFinset f i).card = Fintype.card {j : σ // f j = i} := by
  simp only [rootGroupFinset, Fintype.card_subtype]

theorem coordinateCharacteristic_rootGroupFinset
    (x : σ → R) (f : σ → ι) (i : ι) :
    coordinateCharacteristic (rootGroupFinset f i) x =
      rootGroupCharacteristic x f i := by
  exact Finset.prod_subtype _ (fun j => mem_rootGroupFinset f i j) _

theorem rootGroup_elementary_shifted_zero
    (x : σ → R) (c : ι → R) (f : σ → ι) (i : ι)
    (h : rootGroupCharacteristic x f i =
      (Polynomial.X - Polynomial.C (c i)) ^ Fintype.card {j : σ // f j = i})
    {d : ℕ} (hd : 0 < d) :
    elementaryValue (rootGroupFinset f i) (fun j => x j - c i) d = 0 := by
  apply elementaryValue_sub_eq_zero_of_root_power _ _ _ ?_ hd
  rw [coordinateCharacteristic_rootGroupFinset, rootGroupFinset_card]
  exact h

end HigherSpecht
end
end CanonicalSource6

section CanonicalSource7
/- Source: HigherSpecht/FiberKernel.lean -/



/-!
# The faithful universal property of the polynomial fiber

Killing the original ideal and imposing the displayed coordinate
characteristic polynomial is exactly the same as killing the paper's
finite elementary-parameter ideal.  The converse uses the actual signed
coefficients, so no parameter equation or normalization is suppressed.
-/

noncomputable section

open Finset MvPolynomial TauCeti
open scoped Polynomial

namespace HigherSpecht

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {n m : ℕ} {lam : YoungDiagram}

theorem polynomialFiberIdeal_le_kernel_of_characteristic
    (phi : PolynomialRing n R →ₐ[R] S) (hsize : lam.card + m = n)
    (Q : R[X])
    (hJ : untruncatedIdeal R n lam ≤ RingHom.ker phi.toRingHom)
    (hchar : coordinateCharacteristic Finset.univ (fun i => phi (MvPolynomial.X i)) =
      Polynomial.X ^ lam.card * Q.map (algebraMap R S)) :
    polynomialFiberIdeal R n lam m Q ≤ RingHom.ker phi.toRingHom := by
  apply sup_le hJ
  apply Ideal.span_le.mpr
  rintro p ⟨i, rfl⟩
  let d := i.val + 1
  have hd : 0 < d := by dsimp [d]; omega
  have hdm : d ≤ m := by dsimp [d]; omega
  have hdn : d ≤ n := by omega
  have hk : lam.card ≤ n - d := by omega
  have hcoeff := congrArg (fun p : S[X] => p.coeff (n - d)) hchar
  have helem : elementaryValue Finset.univ (fun i => phi (MvPolynomial.X i)) d =
      phi (elementaryOn (Finset.univ : Finset (Fin n)) d) := by
    simp only [elementaryValue, elementaryOn, map_sum, map_prod]
  rw [coordinateCharacteristic_coeff, Finset.card_univ, Fintype.card_fin,
    if_pos (Nat.sub_le n d), Nat.sub_sub_self hdn, helem,
    Polynomial.coeff_X_pow_mul', if_pos hk, Polynomial.coeff_map,
    show n - d - lam.card = m - d by omega] at hcoeff
  have hs : ((-1 : S) ^ d) * (-1) ^ d = 1 := by
    rw [← mul_pow]
    simp
  have hval : phi (elementaryOn (Finset.univ : Finset (Fin n)) d) =
      algebraMap R S ((-1) ^ d * Q.coeff (m - d)) := by
    calc
      phi (elementaryOn (Finset.univ : Finset (Fin n)) d) =
          (-1 : S) ^ d * ((-1) ^ d *
            phi (elementaryOn (Finset.univ : Finset (Fin n)) d)) := by
              rw [← mul_assoc, hs, one_mul]
      _ = (-1 : S) ^ d * algebraMap R S (Q.coeff (m - d)) := by rw [hcoeff]
      _ = algebraMap R S ((-1) ^ d * Q.coeff (m - d)) := by
        rw [map_mul, map_pow, map_neg, map_one]
  change phi (elementaryOn (Finset.univ : Finset (Fin n)) (i.val + 1) -
    MvPolynomial.C (polynomialParameters Q m i)) = 0
  rw [map_sub, show phi (MvPolynomial.C (polynomialParameters Q m i)) =
    algebraMap R S (polynomialParameters Q m i) from phi.commutes _]
  change phi (elementaryOn (Finset.univ : Finset (Fin n)) d) -
    algebraMap R S ((-1) ^ d * Q.coeff (m - d)) = 0
  exact sub_eq_zero.mpr hval

theorem characteristic_of_polynomialFiberIdeal_le_kernel
    (phi : PolynomialRing n R →ₐ[R] S) (hsize : lam.card + m = n)
    (Q : R[X]) (hQ : Q.Monic) (hdeg : Q.natDegree = m)
    (hI : polynomialFiberIdeal R n lam m Q ≤ RingHom.ker phi.toRingHom) :
    coordinateCharacteristic Finset.univ (fun i => phi (MvPolynomial.X i)) =
      Polynomial.X ^ lam.card * Q.map (algebraMap R S) := by
  let psi : PolynomialFiber R n lam m Q →ₐ[R] S :=
    Ideal.Quotient.liftₐ (polynomialFiberIdeal R n lam m Q) phi hI
  have h := congrArg (Polynomial.map psi.toRingHom)
    (polynomialFiber_characteristic hsize Q hQ hdeg)
  rw [coordinateCharacteristic_map, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_map] at h
  have hx : psi.toRingHom ∘
      (fiberCoordinate (n := n) (lam := lam) (m := m) (Q := Q)) =
      (fun i => phi (MvPolynomial.X i)) := by
    funext i
    exact Ideal.Quotient.lift_mk _ _ _
  rw [hx] at h
  simpa only [AlgHom.toRingHom_eq_coe, psi.comp_algebraMap] using h

/-- Exact universal property of the finite elementary-parameter quotient. -/
theorem polynomialFiberIdeal_le_kernel_iff
    (phi : PolynomialRing n R →ₐ[R] S) (hsize : lam.card + m = n)
    (Q : R[X]) (hQ : Q.Monic) (hdeg : Q.natDegree = m) :
    polynomialFiberIdeal R n lam m Q ≤ RingHom.ker phi.toRingHom ↔
      untruncatedIdeal R n lam ≤ RingHom.ker phi.toRingHom ∧
      coordinateCharacteristic Finset.univ (fun i => phi (MvPolynomial.X i)) =
        Polynomial.X ^ lam.card * Q.map (algebraMap R S) := by
  constructor
  · intro h
    exact ⟨le_trans le_sup_left h,
      characteristic_of_polynomialFiberIdeal_le_kernel phi hsize Q hQ hdeg h⟩
  · rintro ⟨hJ, hchar⟩
    exact polynomialFiberIdeal_le_kernel_of_characteristic phi hsize Q hJ hchar

end HigherSpecht
end
end CanonicalSource7

section CanonicalSource8
/- Source: HigherSpecht/WeakDominanceTails.lean -/



/-!
# Weak row dominance and the exact conjugate tails

The two diagrams may have different sizes.  The minimizing threshold is the
next row length, so the reverse implication is proved directly over natural
numbers, without an equal-cardinality dominance assumption.
-/

noncomputable section
open Finset TauCeti

namespace HigherSpecht

theorem columnTail_eq_sum_rowExcess (eta : YoungDiagram) {N : ℕ}
    (hN : eta.colLen 0 ≤ N) (t : ℕ) :
    columnTail eta t = ∑ i ∈ range N, (eta.rowLen i - t) := by
  rw [columnTail_eq_rowLens_excess, ← Multiset.sum_coe, ← Multiset.map_coe,
    YoungDiagram.sum_map_coe_rowLens]
  apply Finset.sum_subset (Finset.range_mono hN)
  intro i hi hnot
  rw [YoungDiagram.rowLen_eq_zero_of_colLen_le
    (show eta.colLen 0 ≤ i from Nat.le_of_not_gt (by simpa using hnot)), Nat.zero_sub]

theorem rowPrefix_le_mul_add_columnTail (eta : YoungDiagram) (r t : ℕ) :
    (∑ i ∈ range r, eta.rowLen i) ≤ r * t + columnTail eta t := by
  have hsum : (∑ i ∈ range r, eta.rowLen i) ≤
      (∑ i ∈ range r, ((eta.rowLen i - t) + t)) := by
    apply Finset.sum_le_sum
    intro i hi
    omega
  have htail : (∑ i ∈ range r, (eta.rowLen i - t)) ≤ columnTail eta t := by
    rw [columnTail_eq_sum_rowExcess eta (le_max_right r (eta.colLen 0))]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (le_max_left r (eta.colLen 0))) (fun _ _ _ => Nat.zero_le _)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, Nat.cast_id] at hsum
  omega

/-- The threshold `eta.rowLen r` attains the minimum exactly, including
prefixes extending past the last nonempty row. -/
theorem rowPrefix_eq_mul_add_columnTail (eta : YoungDiagram) (r : ℕ) :
    (∑ i ∈ range r, eta.rowLen i) = r * eta.rowLen r + columnTail eta (eta.rowLen r) := by
  have htail : columnTail eta (eta.rowLen r) =
      ∑ i ∈ range r, (eta.rowLen i - eta.rowLen r) := by
    rw [columnTail_eq_sum_rowExcess eta (le_max_right r (eta.colLen 0))]
    symm
    apply Finset.sum_subset (Finset.range_mono (le_max_left r (eta.colLen 0)))
    intro i hi hnot
    exact Nat.sub_eq_zero_of_le (eta.rowLen_anti r i
      (Nat.le_of_not_gt (by simpa using hnot)))
  rw [htail]
  have hsum : (∑ i ∈ range r, eta.rowLen i) =
      ∑ i ∈ range r, ((eta.rowLen i - eta.rowLen r) + eta.rowLen r) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact (Nat.sub_add_cancel (eta.rowLen_anti i r (Finset.mem_range.mp hi).le)).symm
  rw [hsum, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id]
  omega

theorem dominates_iff_columnTail_le (eta zeta : YoungDiagram) :
    Dominates eta zeta ↔ ∀ t, columnTail zeta t ≤ columnTail eta t := by
  refine ⟨fun h t => columnTail_le_of_dominates h t, ?_⟩
  intro h r
  exact (rowPrefix_le_mul_add_columnTail zeta r (eta.rowLen r)).trans
    ((Nat.add_le_add_left (h (eta.rowLen r)) (r * eta.rowLen r)).trans_eq
      (rowPrefix_eq_mul_add_columnTail eta r).symm)

theorem dominates_card_le {eta zeta : YoungDiagram} (h : Dominates eta zeta) :
    zeta.card ≤ eta.card := by
  simpa only [columnTail_zero] using (dominates_iff_columnTail_le eta zeta).mp h 0

theorem columnTail_antitone (eta : YoungDiagram) : Antitone (columnTail eta) := by
  intro i j hij
  apply Finset.card_le_card
  intro c hc
  obtain ⟨hc, hj⟩ := Finset.mem_filter.mp hc
  exact Finset.mem_filter.mpr ⟨hc, hij.trans hj⟩

theorem columnTail_discreteConvex (eta : YoungDiagram) (t : ℕ) :
    2 * columnTail eta (t + 1) ≤ columnTail eta t + columnTail eta (t + 2) := by
  have h0 := columnTail_succ eta t
  have h1 := columnTail_succ eta (t + 1)
  change columnTail eta (t + 1) = eta.colLen (t + 1) +
    columnTail eta (t + 2) at h1
  have hc := eta.colLen_anti t (t + 1) (Nat.le_succ t)
  omega

end HigherSpecht
end
end CanonicalSource8

section CanonicalSource9
/- Source: HigherSpecht/BlockSpringerIdeals.lean -/



/-!
# Springer ideals on an actual subset of coordinate positions

`blockSpringerIdeal` uses the same elementary generators on a specified
coordinate set.  Its equivalence with the extension of the ordinary
Springer ideal along any enumeration of that set is proved below.  The
forward inclusion from the untruncated ideal is integral and uses the full
convolution formula; the nonzero coordinates are not discarded.
-/

noncomputable section

open Finset MvPolynomial TauCeti

namespace HigherSpecht

variable {R : Type*} [CommRing R] {n : ℕ}

theorem columnTail_mono_shape {mu nu : YoungDiagram} (h : mu ≤ nu) (j : ℕ) :
    columnTail mu j ≤ columnTail nu j := by
  apply Finset.card_le_card
  intro c hc
  obtain ⟨hc, hj⟩ := Finset.mem_filter.mp hc
  exact Finset.mem_filter.mpr ⟨h hc, hj⟩

theorem columnTail_le_card_sub (mu : YoungDiagram) (h : ℕ) :
    columnTail mu h ≤ mu.card - h := by
  by_cases hh : h ≤ mu.rowLen 0
  · have hp : h ≤ ∑ j ∈ Finset.range h, mu.colLen j := by
      calc
        h = ∑ j ∈ Finset.range h, (1 : ℕ) := by simp
        _ ≤ _ := Finset.sum_le_sum fun j hj => by
          have hjlt : j < mu.rowLen 0 := (Finset.mem_range.mp hj).trans_le hh
          have hc : (0, j) ∈ mu := YoungDiagram.mem_iff_lt_rowLen.mpr hjlt
          have := YoungDiagram.mem_iff_lt_colLen.mp hc
          omega
    have he := columnTail_add_prefix mu h
    omega
  · rw [columnTail_eq_zero_of_width_le mu (by omega)]
    exact Nat.zero_le _

theorem elementaryOn_union {A B : Finset (Fin n)} (hAB : Disjoint A B) (d : ℕ) :
    elementaryOn (R := R) (A ∪ B) d =
      ∑ ij ∈ Finset.antidiagonal d, elementaryOn A ij.1 * elementaryOn B ij.2 := by
  have h := congrArg (fun p : Polynomial (PolynomialRing n R) => p.coeff d)
    (elementaryGenerating_union (R := R) A B hAB)
  simpa only [elementaryGenerating_coeff, Polynomial.coeff_mul] using h

/-- The threshold is written in the integers.  Allowing degree zero here
is harmless precisely when the block has the cardinality of the partition;
the following image theorem proves agreement with the original ideal. -/
def blockSpringerIdeal (R : Type*) [CommRing R] (A : Finset (Fin n))
    (mu : YoungDiagram) : Ideal (PolynomialRing n R) :=
  Ideal.span {p | ∃ (Y : Finset (Fin n)) (d : ℕ), Y ⊆ A ∧ d ≤ Y.card ∧
    (Y.card : ℤ) - (columnTail mu (A.card - Y.card) : ℤ) < (d : ℤ) ∧
    p = elementaryOn Y d}

theorem elementaryOn_mem_blockSpringerIdeal (A : Finset (Fin n)) (mu : YoungDiagram)
    {Y : Finset (Fin n)} (hYA : Y ⊆ A) (d : ℕ)
    (hth : (Y.card : ℤ) - (columnTail mu (A.card - Y.card) : ℤ) < (d : ℤ)) :
    elementaryOn (R := R) Y d ∈ blockSpringerIdeal R A mu := by
  by_cases hd : d ≤ Y.card
  · exact Ideal.subset_span ⟨Y, d, hYA, hd, hth, rfl⟩
  · rw [elementaryOn_eq_zero_of_card_lt (Nat.lt_of_not_ge hd)]
    exact Ideal.zero_mem _

theorem blockSpringerIdeal_univ (mu : YoungDiagram) (hmu : mu.card ≤ n) :
    blockSpringerIdeal R (Finset.univ : Finset (Fin n)) mu =
      untruncatedIdeal R n mu := by
  rw [← extendedElementaryIdeal_eq_untruncated mu hmu]
  congr 1
  ext p
  simp only [blockSpringerIdeal, extendedElementaryIdeal, Set.mem_setOf_eq,
    Finset.subset_univ, true_and, Finset.card_univ, Fintype.card_fin]

theorem blockSpringerIdeal_eq_map (mu : YoungDiagram) (e : Fin mu.card ↪ Fin n) :
    blockSpringerIdeal R (Finset.univ.map e) mu =
      (springerIdeal R mu).map (MvPolynomial.rename e) := by
  classical
  rw [springerIdeal, ← extendedElementaryIdeal_eq_untruncated mu le_rfl]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro p ⟨Y, d, hYA, hd, hth, rfl⟩
    let Z := (Finset.univ : Finset (Fin mu.card)).filter fun i => e i ∈ Y
    have hZY : Z.map e = Y := by
      ext j
      constructor
      · intro hj
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
        exact (Finset.mem_filter.mp hi).2
      · intro hj
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp (hYA hj)
        exact Finset.mem_map.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hj⟩, rfl⟩
    have hcard : Z.card = Y.card := by rw [← hZY, Finset.card_map]
    have hmem : elementaryOn (R := R) Z d ∈ extendedElementaryIdeal R mu.card mu := by
      apply elementaryOn_mem_extended Z d
      simpa only [Finset.card_map, Finset.card_univ, Fintype.card_fin, hcard] using hth
    rw [← hZY, ← rename_elementaryOn_embedding]
    exact Ideal.mem_map_of_mem (MvPolynomial.rename e) hmem
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro p ⟨Y, d, hd, hth, rfl⟩
    change MvPolynomial.rename e (elementaryOn (R := R) Y d) ∈
      blockSpringerIdeal R (Finset.univ.map e) mu
    rw [rename_elementaryOn_embedding]
    apply elementaryOn_mem_blockSpringerIdeal _ mu (Finset.map_subset_map.mpr
      (Finset.subset_univ Y)) d
    simpa only [Finset.card_map, Finset.card_univ, Fintype.card_fin] using hth

theorem blockSpringerIdeal_le_coordinateIdeal (A : Finset (Fin n))
    (mu : YoungDiagram) (hA : A.card = mu.card) :
    blockSpringerIdeal R A mu ≤
      Ideal.span (MvPolynomial.X '' (A : Set (Fin n))) := by
  apply Ideal.span_le.mpr
  rintro p ⟨Y, d, hYA, hd, hth, rfl⟩
  have hYcard : Y.card ≤ A.card := Finset.card_le_card hYA
  have htail : columnTail mu (A.card - Y.card) ≤ Y.card := by
    have ht := columnTail_le_card_sub mu (A.card - Y.card)
    rw [← hA] at ht
    omega
  have hdpos : 0 < d := by omega
  apply Ideal.sum_mem
  intro Z hZ
  obtain ⟨hZY, hZd⟩ := Finset.mem_powersetCard.mp hZ
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < Z.card)
  exact Ideal.prod_mem _ hi (Ideal.subset_span ⟨i, hYA (hZY hi), rfl⟩)

theorem blockSpringer_global_elementary (A : Finset (Fin n)) (mu : YoungDiagram)
    (hA : A.card = mu.card) {d : ℕ} (hd : 0 < d) :
    elementaryOn (R := R) A d ∈ blockSpringerIdeal R A mu := by
  apply elementaryOn_mem_blockSpringerIdeal A mu (Finset.Subset.refl A) d
  rw [Nat.sub_self, columnTail_zero, hA]
  omega

/-- This integral inclusion is the first half of both the fiber computation
and the primary-component calculation.  More generally it holds whenever
the block partition contains the original partition. -/
theorem untruncatedIdeal_le_blockSpringerIdeal (A : Finset (Fin n))
    {lam mu : YoungDiagram} (hA : A.card = mu.card) (hlam : lam ≤ mu) :
    untruncatedIdeal R n lam ≤ blockSpringerIdeal R A mu := by
  classical
  have hAcard : A.card ≤ n := by simpa using Finset.card_le_univ A
  have hlamcard : lam.card ≤ n := by
    have h : lam.card ≤ mu.card := Finset.card_le_card hlam
    omega
  apply Ideal.span_le.mpr
  rintro p ⟨Y, d, hd, hdY, hth, rfl⟩
  let D := Y ∩ A
  let B := Y \ A
  have hDA : D ⊆ A := Finset.inter_subset_right
  have hDB : Disjoint D B := by
    exact Finset.disjoint_left.mpr fun i hiD hiB =>
      (Finset.mem_sdiff.mp hiB).2 (Finset.mem_inter.mp hiD).2
  have hU : D ∪ B = Y := by
    ext i
    simp only [D, B, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hDY : D.card + B.card = Y.card := by rw [← Finset.card_union_of_disjoint hDB, hU]
  have hAB : Disjoint A B := Finset.disjoint_left.mpr
    (fun i hiA hiB => (Finset.mem_sdiff.mp hiB).2 hiA)
  have hABcard : A.card + B.card ≤ n := by
    rw [← Finset.card_union_of_disjoint hAB]
    simpa using Finset.card_le_univ (A ∪ B)
  have hcut : A.card - D.card ≤ n - Y.card := by omega
  have htail : columnTail lam (n - Y.card) ≤ columnTail mu (A.card - D.card) :=
    (columnTail_antitone lam hcut).trans (columnTail_mono_shape hlam _)
  rw [← columnTail_eq_conjugateTail lam hlamcard] at hth
  rw [← hU, elementaryOn_union hDB]
  apply Ideal.sum_mem
  intro ij hij
  have heq : ij.1 + ij.2 = d := Finset.mem_antidiagonal.mp hij
  by_cases hb : ij.2 ≤ B.card
  · apply Ideal.mul_mem_right
    apply elementaryOn_mem_blockSpringerIdeal A mu hDA ij.1
    omega
  · rw [elementaryOn_eq_zero_of_card_lt (Nat.lt_of_not_ge hb), mul_zero]
    exact Ideal.zero_mem _

theorem untruncatedIdeal_le_zeroGroup (A : Finset (Fin n))
    (lam : YoungDiagram) (r : ℕ) (hA : A.card = lam.card + r) :
    untruncatedIdeal R n lam ≤ blockSpringerIdeal R A (adjoinOnes lam r) := by
  apply untruncatedIdeal_le_blockSpringerIdeal A
    (by simpa only [adjoinOnes_card] using hA) (le_adjoinOnes lam r)

end HigherSpecht
end
end CanonicalSource9

section CanonicalSource10
/- Source: HigherSpecht/FiberZeroGroup.lean -/



/-!
# Recovering precisely the Springer ideal on the zero group

This is the converse elementary-ideal calculation in Theorem 7.1.  It is
stated for an actual ring homomorphism that kills the original generators,
has zero global elementary functions on the zero group, and sends every
outside coordinate to a unit.  Descending induction isolates the leading
outside product in the literal elementary convolution.  The hypotheses are
local algebra properties supplied by the fiber factorization; they are not
a substitute for a fiber decomposition or for a basis theorem.
-/

noncomputable section

open Finset MvPolynomial TauCeti

namespace HigherSpecht

variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

@[simp] theorem elementaryOn_card (A : Finset (Fin n)) :
    elementaryOn (R := R) A A.card = ∏ i ∈ A, MvPolynomial.X i := by
  simp only [elementaryOn, Finset.powersetCard_self, Finset.sum_singleton]

theorem zeroGroup_elementary_recovery
    (phi : PolynomialRing n R →+* S) (lam : YoungDiagram) (r : ℕ)
    (A : Finset (Fin n)) (hA : A.card = lam.card + r)
    (hJ : untruncatedIdeal R n lam ≤ RingHom.ker phi)
    (hglobal : ∀ d : ℕ, 0 < d → phi (elementaryOn A d) = 0)
    (hout : ∀ i : Fin n, i ∉ A → IsUnit (phi (MvPolynomial.X i)))
    {Y : Finset (Fin n)} (hYA : Y ⊆ A) :
    ∀ d : ℕ, (Y.card : ℤ) -
        (columnTail (adjoinOnes lam r) (A.card - Y.card) : ℤ) < (d : ℤ) →
      phi (elementaryOn Y d) = 0 := by
  classical
  by_cases hYeq : Y = A
  · subst Y
    intro d hth
    rw [Nat.sub_self, columnTail_zero, adjoinOnes_card, ← hA] at hth
    exact hglobal d (by omega)
  have hYcard : Y.card < A.card := Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨hYA, hYeq⟩)
  have hcut : 0 < A.card - Y.card := by omega
  have hAcard : A.card ≤ n := by simpa using Finset.card_le_univ A
  have hlamn : lam.card ≤ n := by omega
  let B := Aᶜ
  have hBcard : B.card = n - A.card := by
    simp only [B, Finset.card_compl, Fintype.card_fin]
  have hYB : Disjoint Y B := by
    apply Finset.disjoint_left.mpr
    intro i hiY hiB
    exact Finset.mem_compl.mp hiB (hYA hiY)
  have hsumcard : (Y ∪ B).card = Y.card + B.card := Finset.card_union_of_disjoint hYB
  have hunit : IsUnit (phi (elementaryOn (R := R) B B.card)) := by
    rw [elementaryOn_card, map_prod]
    apply IsUnit.prod_iff.mpr
    intro i hi
    exact hout i (Finset.mem_compl.mp hi)
  apply Nat.strong_decreasing_induction
  · refine ⟨Y.card, ?_⟩
    intro d hd hth
    rw [elementaryOn_eq_zero_of_card_lt hd, map_zero]
  · intro d ih hth
    by_cases hd : d ≤ Y.card
    · have hth' : (Y.card : ℤ) -
          (columnTail lam (A.card - Y.card) : ℤ) < (d : ℤ) := by
        simpa only [columnTail_adjoinOnes_of_pos lam r hcut] using hth
      have htail : columnTail lam (A.card - Y.card) ≤ Y.card := by
        have h := columnTail_le_card_sub lam (A.card - Y.card)
        omega
      have hdpos : 0 < d := by omega
      have hgen : elementaryOn (R := R) (Y ∪ B) (B.card + d) ∈
          untruncatedIdeal R n lam := by
        apply elementaryOn_mem_untruncatedIdeal _ (by omega) (by omega)
        rw [← columnTail_eq_conjugateTail lam hlamn, hsumcard,
          show n - (Y.card + B.card) = A.card - Y.card by omega]
        omega
      have hz : phi (elementaryOn (Y ∪ B) (B.card + d)) = 0 := hJ hgen
      rw [elementaryOn_union hYB, map_sum] at hz
      have hsingle :
          (∑ ij ∈ Finset.antidiagonal (B.card + d),
            phi (elementaryOn Y ij.1 * elementaryOn B ij.2)) =
          phi (elementaryOn Y d) * phi (elementaryOn B B.card) := by
        rw [← map_mul]
        apply Finset.sum_eq_single (d, B.card)
        · intro ij hij hne
          have heq : ij.1 + ij.2 = B.card + d := Finset.mem_antidiagonal.mp hij
          by_cases hb : B.card < ij.2
          · rw [elementaryOn_eq_zero_of_card_lt hb, mul_zero, map_zero]
          · have hgreater : d < ij.1 := by
              by_contra hg
              have he1 : ij.1 = d := by omega
              have he2 : ij.2 = B.card := by omega
              exact hne (Prod.ext he1 he2)
            rw [map_mul, ih ij.1 hgreater (by omega), zero_mul]
        · simp only [Finset.mem_antidiagonal, Prod.fst, Prod.snd]
          omega
      rw [hsingle] at hz
      exact hunit.mul_right_cancel (by simpa only [zero_mul] using hz)
    · rw [elementaryOn_eq_zero_of_card_lt (Nat.lt_of_not_ge hd), map_zero]

/-- No local Springer relation is omitted: the complete actual block ideal
is killed, including all proper coordinate subsets and global generators. -/
theorem zeroGroup_blockIdeal_le_kernel
    (phi : PolynomialRing n R →+* S) (lam : YoungDiagram) (r : ℕ)
    (A : Finset (Fin n)) (hA : A.card = lam.card + r)
    (hJ : untruncatedIdeal R n lam ≤ RingHom.ker phi)
    (hglobal : ∀ d : ℕ, 0 < d → phi (elementaryOn A d) = 0)
    (hout : ∀ i : Fin n, i ∉ A → IsUnit (phi (MvPolynomial.X i))) :
    blockSpringerIdeal R A (adjoinOnes lam r) ≤ RingHom.ker phi := by
  apply Ideal.span_le.mpr
  rintro p ⟨Y, d, hYA, hd, hth, rfl⟩
  exact zeroGroup_elementary_recovery phi lam r A hA hJ hglobal hout hYA d hth

end HigherSpecht
end
end CanonicalSource10

section CanonicalSource11
/- Source: HigherSpecht/FiberComponentIdeals.lean -/



/-!
# The literal local component ideals of a split fiber

A root assignment determines a zero-group Springer ideal and the shifted
global elementary ideals of all root groups.  This file identifies that
actual ideal with the fiber ideal plus the coordinate power relations used
by Chinese remainders.  The reverse inclusion is the descending elementary
recovery argument; the forward inclusion follows from the actual block
characteristic identities.  No dimension, flatness, or free-basis premise
is used.
-/

noncomputable section

open Finset MvPolynomial TauCeti
open scoped Polynomial BigOperators Classical

namespace HigherSpecht

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {n : ℕ} {ι : Type*} [Fintype ι]

def shiftedElementaryOn (A : Finset (Fin n)) (c : R) (d : ℕ) :
    PolynomialRing n R :=
  elementaryValue A (fun j => MvPolynomial.X j - MvPolynomial.C c) d

def shiftedGlobalIdeal (R : Type*) [CommRing R]
    (A : Finset (Fin n)) (c : R) : Ideal (PolynomialRing n R) :=
  Ideal.span (Set.range fun d : ℕ => shiftedElementaryOn A c (d + 1))

theorem shiftedElementaryOn_map (phi : PolynomialRing n R →ₐ[R] S)
    (A : Finset (Fin n)) (c : R) (d : ℕ) :
    phi (shiftedElementaryOn A c d) =
      elementaryValue A (fun j => phi (MvPolynomial.X j) - algebraMap R S c) d := by
  simp only [shiftedElementaryOn, elementaryValue, map_sum, map_prod, map_sub]
  rw [show phi (MvPolynomial.C c) = algebraMap R S c from phi.commutes c]

theorem shiftedGlobalIdeal_le_kernel_iff (phi : PolynomialRing n R →ₐ[R] S)
    (A : Finset (Fin n)) (c : R) :
    shiftedGlobalIdeal R A c ≤ RingHom.ker phi.toRingHom ↔
      ∀ d : ℕ, 0 < d →
        elementaryValue A (fun j => phi (MvPolynomial.X j) - algebraMap R S c) d = 0 := by
  constructor
  · intro h d hd
    have hm := h (Ideal.subset_span ⟨d - 1, rfl⟩)
    change phi (shiftedElementaryOn A c (d - 1 + 1)) = 0 at hm
    rw [Nat.sub_add_cancel (by omega), shiftedElementaryOn_map] at hm
    exact hm
  · intro h
    apply Ideal.span_le.mpr
    rintro p ⟨d, rfl⟩
    change phi (shiftedElementaryOn A c (d + 1)) = 0
    rw [shiftedElementaryOn_map]
    exact h _ (by omega)

def splitRootBlockIdeal (R : Type*) [CommRing R] (lam : YoungDiagram) (r0 : ℕ)
    (c : ι → R) (f : Fin n → ι) (z : ι) : Ideal (PolynomialRing n R) :=
  blockSpringerIdeal R (rootGroupFinset f z) (adjoinOnes lam r0) ⊔
    ⨆ i : ι, shiftedGlobalIdeal R (rootGroupFinset f i) (c i)

def assignedCoordinatePowerIdeal (R : Type*) [CommRing R]
    (c : ι → R) (f : Fin n → ι) (N : ℕ) : Ideal (PolynomialRing n R) :=
  Ideal.span (Set.range fun j : Fin n =>
    (MvPolynomial.X j - MvPolynomial.C (c (f j))) ^ N)

def splitFiberComponentIdeal (R : Type*) [CommRing R]
    (lam : YoungDiagram) (m : ℕ) (Q : R[X])
    (c : ι → R) (f : Fin n → ι) (N : ℕ) : Ideal (PolynomialRing n R) :=
  polynomialFiberIdeal R n lam m Q ⊔ assignedCoordinatePowerIdeal R c f N

/-- Every shifted block characteristic is exact in the actual block quotient. -/
theorem rootGroup_characteristic_of_blockIdeal_le_kernel
    (phi : PolynomialRing n R →ₐ[R] S) (lam : YoungDiagram) (r0 : ℕ)
    (c : ι → R) (f : Fin n → ι) (z : ι)
    (hI : splitRootBlockIdeal R lam r0 c f z ≤ RingHom.ker phi.toRingHom) (i : ι) :
    rootGroupCharacteristic (fun j => phi (MvPolynomial.X j)) f i =
      (Polynomial.X - Polynomial.C (algebraMap R S (c i))) ^
        Fintype.card {j : Fin n // f j = i} := by
  have hi : shiftedGlobalIdeal R (rootGroupFinset f i) (c i) ≤
      RingHom.ker phi.toRingHom :=
    le_trans (le_trans (le_iSup
      (fun i : ι => shiftedGlobalIdeal R (rootGroupFinset f i) (c i)) i) le_sup_right) hI
  have hchar := coordinateCharacteristic_eq_root_power_of_shifted_elementary
    (rootGroupFinset f i) (fun j => phi (MvPolynomial.X j))
    (algebraMap R S (c i)) ((shiftedGlobalIdeal_le_kernel_iff phi _ _).mp hi)
  simpa only [coordinateCharacteristic_rootGroupFinset, rootGroupFinset_card] using hchar

/-- Nilpotent coordinate deviations and the exact characteristic identity
force all relations of the genuine local block ideal. -/
theorem splitRootBlockIdeal_le_kernel_of_assigned_roots [Nontrivial S]
    (phi : PolynomialRing n R →ₐ[R] S) (lam : YoungDiagram) (r0 : ℕ)
    (c : ι → R) (f : Fin n → ι) (z : ι) (r : ι → ℕ)
    (hcz : c z = 0) (hc : Pairwise fun i j => IsUnit (c i - c j))
    (hrz : r z = lam.card + r0)
    (hcount : ∀ i, Fintype.card {j : Fin n // f j = i} = r i)
    (hJ : untruncatedIdeal R n lam ≤ RingHom.ker phi.toRingHom)
    (hnil : ∀ j, IsNilpotent (phi (MvPolynomial.X j) - algebraMap R S (c (f j))))
    (hproduct : coordinateCharacteristic Finset.univ
        (fun j => phi (MvPolynomial.X j)) =
      ∏ i : ι, (Polynomial.X - Polynomial.C (algebraMap R S (c i))) ^ r i) :
    splitRootBlockIdeal R lam r0 c f z ≤ RingHom.ker phi.toRingHom := by
  let x : Fin n → S := fun j => phi (MvPolynomial.X j)
  let N := assignedRootIdeal x (fun i => algebraMap R S (c i)) f
  have hN : IsNilpotent N := assignedRootIdeal_isNilpotent _ _ _ hnil
  have hgroups := rootGroupCharacteristic_eq_root_power N hN x
    (fun i => algebraMap R S (c i)) f r
    (fun i j hij => by
      change IsUnit (algebraMap R S (c i) - algebraMap R S (c j))
      rw [← map_sub]
      exact (hc hij).map (algebraMap R S)) hcount
    (assignedRootIdeal_residue x _ f) hproduct
  have hglobal (i : ι) (d : ℕ) (hd : 0 < d) :
      elementaryValue (rootGroupFinset f i)
        (fun j => phi (MvPolynomial.X j) - algebraMap R S (c i)) d = 0 := by
    apply rootGroup_elementary_shifted_zero _ _ f i ?_ hd
    rw [hcount i]
    exact hgroups i
  apply sup_le
  · apply zeroGroup_blockIdeal_le_kernel phi.toRingHom lam r0
      (rootGroupFinset f z) (by rw [rootGroupFinset_card, hcount z, hrz]) hJ
    · intro d hd
      change phi (elementaryOn (rootGroupFinset f z) d) = 0
      have h := hglobal z d hd
      simpa only [hcz, map_zero, sub_zero, elementaryValue, elementaryOn,
        map_sum, map_prod] using h
    · intro j hj
      have hjz : f j ≠ z := by simpa only [mem_rootGroupFinset] using hj
      have hunit : IsUnit (c (f j)) := by
        simpa only [hcz, sub_zero] using hc hjz
      have hu : IsUnit (algebraMap R S (c (f j))) := hunit.map (algebraMap R S)
      change IsUnit (phi (MvPolynomial.X j))
      convert (hnil j).isUnit_add_right_of_commute hu (Commute.all _ _) using 1 <;> ring
  · apply iSup_le
    intro i
    exact (shiftedGlobalIdeal_le_kernel_iff phi _ _).mpr (hglobal i)

/-- The other inclusion follows directly from the block equations, including
the actual coordinate power bounds required by the CRT construction. -/
theorem splitFiberComponentIdeal_le_blockIdeal
    {lam : YoungDiagram} {m : ℕ} (hsize : lam.card + m = n)
    (Q : R[X]) (r0 : ℕ) (c : ι → R) (f : Fin n → ι) (z : ι) (r : ι → ℕ)
    (hcz : c z = 0) (hrz : r z = lam.card + r0)
    (hcount : ∀ i, Fintype.card {j : Fin n // f j = i} = r i)
    (hfactor : Polynomial.X ^ lam.card * Q =
      ∏ i : ι, (Polynomial.X - Polynomial.C (c i)) ^ r i)
    (N : ℕ) (hN : n ≤ N) :
    splitFiberComponentIdeal R lam m Q c f N ≤ splitRootBlockIdeal R lam r0 c f z := by
  let I := splitRootBlockIdeal R lam r0 c f z
  let phi : PolynomialRing n R →ₐ[R] (PolynomialRing n R ⧸ I) :=
    Ideal.Quotient.mkₐ R I
  have hker : I ≤ RingHom.ker phi.toRingHom := by
    intro p hp
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hp
  have hg := rootGroup_characteristic_of_blockIdeal_le_kernel phi lam r0 c f z hker
  have hJ : untruncatedIdeal R n lam ≤ RingHom.ker phi.toRingHom := by
    apply le_trans (untruncatedIdeal_le_zeroGroup (R := R) (rootGroupFinset f z)
      lam r0 (by rw [rootGroupFinset_card, hcount z, hrz]))
    exact le_trans le_sup_left hker
  have hchar : coordinateCharacteristic Finset.univ (fun j => phi (MvPolynomial.X j)) =
      Polynomial.X ^ lam.card * Q.map (algebraMap R (PolynomialRing n R ⧸ I)) := by
    rw [coordinateCharacteristic,
      ← prod_rootGroupCharacteristic (fun j => phi (MvPolynomial.X j)) f]
    simp_rw [hg, hcount]
    have hm := congrArg (Polynomial.map (algebraMap R (PolynomialRing n R ⧸ I))) hfactor
    simpa only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_C] using hm.symm
  apply sup_le
  · intro p hp
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      (polynomialFiberIdeal_le_kernel_of_characteristic phi hsize Q hJ hchar hp)
  · apply Ideal.span_le.mpr
    rintro p ⟨j, rfl⟩
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change (phi (MvPolynomial.X j) - algebraMap R _ (c (f j))) ^ N = 0
    have hz := coordinateCharacteristic_eval_root (rootGroupFinset f (f j))
      (fun k => phi (MvPolynomial.X k)) ((mem_rootGroupFinset f (f j) j).mpr rfl)
    rw [coordinateCharacteristic_rootGroupFinset, hg] at hz
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] at hz
    have hcard : Fintype.card {k : Fin n // f k = f j} ≤ N := by
      have hc : (rootGroupFinset f (f j)).card ≤ n := by
        simpa only [Fintype.card_fin] using Finset.card_le_univ (rootGroupFinset f (f j))
      rw [rootGroupFinset_card] at hc
      exact hc.trans hN
    rw [show N = Fintype.card {k : Fin n // f k = f j} +
      (N - Fintype.card {k : Fin n // f k = f j}) by omega,
      pow_add, hz, zero_mul]

/-- The exact local component ideal.  Assigned multiplicities are part of
the indexing set here; the separate root-multiplicity theorem excludes all
other assignments from the nonzero CRT factors. -/
theorem splitFiberComponentIdeal_eq_blockIdeal
    {lam : YoungDiagram} {m : ℕ} (hsize : lam.card + m = n)
    (Q : R[X]) (hQ : Q.Monic) (hdeg : Q.natDegree = m)
    (r0 : ℕ) (c : ι → R) (f : Fin n → ι) (z : ι) (r : ι → ℕ)
    (hcz : c z = 0) (hc : Pairwise fun i j => IsUnit (c i - c j))
    (hrz : r z = lam.card + r0)
    (hcount : ∀ i, Fintype.card {j : Fin n // f j = i} = r i)
    (hfactor : Polynomial.X ^ lam.card * Q =
      ∏ i : ι, (Polynomial.X - Polynomial.C (c i)) ^ r i)
    (N : ℕ) (hN : n ≤ N) :
    splitFiberComponentIdeal R lam m Q c f N = splitRootBlockIdeal R lam r0 c f z := by
  apply le_antisymm
    (splitFiberComponentIdeal_le_blockIdeal hsize Q r0 c f z r hcz hrz hcount hfactor N hN)
  let I := splitFiberComponentIdeal R lam m Q c f N
  let A := PolynomialRing n R ⧸ I
  let phi : PolynomialRing n R →ₐ[R] A := Ideal.Quotient.mkₐ R I
  rcases subsingleton_or_nontrivial A with hA | hA
  · letI := hA
    intro p hp
    exact Ideal.Quotient.eq_zero_iff_mem.mp (Subsingleton.elim _ _)
  · letI := hA
    have hI : polynomialFiberIdeal R n lam m Q ≤ RingHom.ker phi.toRingHom := by
      intro p hp
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left hp)
    have hJ : untruncatedIdeal R n lam ≤ RingHom.ker phi.toRingHom :=
      le_trans le_sup_left hI
    have hnil (j : Fin n) :
        IsNilpotent (phi (MvPolynomial.X j) - algebraMap R A (c (f j))) := by
      refine ⟨N, ?_⟩
      have hp : (MvPolynomial.X j - MvPolynomial.C (c (f j))) ^ N ∈ I :=
        Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩)
      have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hp
      change phi ((MvPolynomial.X j - MvPolynomial.C (c (f j))) ^ N) = 0 at hz
      rw [map_pow, map_sub, show phi (MvPolynomial.C (c (f j))) =
        algebraMap R A (c (f j)) from phi.commutes _] at hz
      exact hz
    have hchar := characteristic_of_polynomialFiberIdeal_le_kernel phi hsize Q hQ hdeg hI
    have hproduct : coordinateCharacteristic Finset.univ (fun j => phi (MvPolynomial.X j)) =
        ∏ i : ι, (Polynomial.X - Polynomial.C (algebraMap R A (c i))) ^ r i := by
      rw [hchar]
      have hm := congrArg (Polynomial.map (algebraMap R A)) hfactor
      simpa only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_C] using hm
    intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact splitRootBlockIdeal_le_kernel_of_assigned_roots phi lam r0 c f z r
      hcz hc hrz hcount hJ hnil hproduct hp

end HigherSpecht
end
end CanonicalSource11

section CanonicalSource12
/- Source: HigherSpecht/CoordinateChineseRemainder.lean -/



/-!
# Chinese remainders for simultaneous coordinate assignments

Each coordinate supplies a finite family of pairwise comaximal ideals
whose intersection is zero. The simultaneous factors are the quotients
by sums of one ideal from each coordinate family. Their intersection is
proved to be zero using actual Chinese-remainder selectors and the
finite product-of-sums identity. No Artinian decomposition is assumed.

The final specialization uses literal powers of coordinate deviations
from roots with invertible pairwise differences.
-/

noncomputable section

open scoped BigOperators

namespace HigherSpecht

variable {R : Type*} [CommRing R]
variable {σ ι : Type*} [Fintype σ] [Fintype ι]

/-- Equality is detected by a family of quotient maps with zero kernel
intersection. -/
theorem eq_zero_of_quotient_mk_eq_zero
    (I : ι → Ideal R) (hI : (⨅ i, I i) = ⊥) (z : R)
    (hz : ∀ i, Ideal.Quotient.mk (I i) z = 0) : z = 0 := by
  apply Ideal.mem_bot.mp
  rw [← hI]
  apply Ideal.mem_iInf.mpr
  intro i
  exact Ideal.Quotient.eq_zero_iff_mem.mp (hz i)

/-- CRT supplies selectors whose sum is one and which annihilate the
ideal of their selected factor. -/
theorem exists_quotient_annihilator_selectors
    (I : ι → Ideal R)
    (hpair : Pairwise fun i j => IsCoprime (I i) (I j))
    (hI : (⨅ i, I i) = ⊥) :
    ∃ e : ι → R, (∑ i, e i) = 1 ∧
      ∀ i a, a ∈ I i → e i * a = 0 := by
  classical
  have hex : ∀ i : ι, ∃ e : R, ∀ j : ι,
      Ideal.Quotient.mk (I j) e = if j = i then 1 else 0 := by
    intro i
    exact Ideal.pi_quotient_surjective hpair
      (fun j => if j = i then 1 else 0)
  choose e he using hex
  refine ⟨e, ?_, ?_⟩
  · apply sub_eq_zero.mp
    apply eq_zero_of_quotient_mk_eq_zero I hI
    intro j
    simp only [map_sub, map_sum, map_one, he]
    simp
  · intro i a ha
    apply eq_zero_of_quotient_mk_eq_zero I hI
    intro j
    by_cases hji : j = i
    · subst j
      rw [map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr ha, mul_zero]
    · rw [map_mul, he, if_neg hji, zero_mul]

/-- The literal ideal imposing one selected relation at every coordinate. -/
def coordinateAssignmentIdeal (I : σ → ι → Ideal R) (f : σ → ι) : Ideal R :=
  ⨆ j, I j (f j)

theorem coordinateAssignmentIdeal_pairwise
    (I : σ → ι → Ideal R)
    (hpair : ∀ j, Pairwise fun i h => IsCoprime (I j i) (I j h)) :
    Pairwise fun f g : σ → ι =>
      IsCoprime (coordinateAssignmentIdeal I f) (coordinateAssignmentIdeal I g) := by
  intro f g hfg
  have hex : ∃ j, f j ≠ g j := by
    by_contra h
    apply hfg
    funext j
    by_contra hj
    exact h ⟨j, hj⟩
  obtain ⟨j, hj⟩ := hex
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply top_le_iff.mp
  rw [← (hpair j hj).sup_eq]
  exact sup_le_sup (le_iSup (fun j => I j (f j)) j)
    (le_iSup (fun j => I j (g j)) j)

/-- The simultaneous assignment ideals have zero intersection. The
proof uses all coordinate relations, including empty finite index types. -/
theorem coordinateAssignmentIdeal_iInf_eq_bot
    (I : σ → ι → Ideal R)
    (hpair : ∀ j, Pairwise fun i h => IsCoprime (I j i) (I j h))
    (hzero : ∀ j, (⨅ i, I j i) = ⊥) :
    (⨅ f : σ → ι, coordinateAssignmentIdeal I f) = ⊥ := by
  classical
  choose e hsum hann using fun j =>
    exists_quotient_annihilator_selectors (I j) (hpair j) (hzero j)
  have hsumall : (∑ f : σ → ι, ∏ j, e j (f j)) = 1 := by
    rw [← Fintype.prod_sum]
    simp only [hsum, Finset.prod_const_one]
  have hkill (f : σ → ι) (a : R)
      (ha : a ∈ coordinateAssignmentIdeal I f) :
      (∏ j, e j (f j)) * a = 0 := by
    refine Submodule.iSup_induction (R := R) (M := R) (fun j => I j (f j))
      (motive := fun a => (∏ j, e j (f j)) * a = 0) ha ?_ ?_ ?_
    · intro j b hb
      rw [← Finset.prod_erase_mul Finset.univ
        (fun j => e j (f j)) (Finset.mem_univ j)]
      rw [mul_assoc, hann j (f j) b hb, mul_zero]
    · exact mul_zero _
    · intro b c hb hc
      rw [mul_add, hb, hc, add_zero]
  apply le_antisymm ?_ bot_le
  intro a ha
  apply Ideal.mem_bot.mpr
  calc
    a = 1 * a := (one_mul a).symm
    _ = (∑ f : σ → ι, ∏ j, e j (f j)) * a := by rw [hsumall]
    _ = ∑ f : σ → ι, (∏ j, e j (f j)) * a := Finset.sum_mul ..
    _ = 0 := Finset.sum_eq_zero fun f _ =>
      hkill f a (Ideal.mem_iInf.mp ha f)

/-- The actual quotient maps give the simultaneous CRT equivalence. -/
noncomputable def coordinateAssignmentEquiv
    (I : σ → ι → Ideal R)
    (hpair : ∀ j, Pairwise fun i h => IsCoprime (I j i) (I j h))
    (hzero : ∀ j, (⨅ i, I j i) = ⊥) :
    R ≃+* ∀ f : σ → ι, R ⧸ coordinateAssignmentIdeal I f :=
  (RingEquiv.quotientBot R).symm |>.trans
    ((Ideal.quotEquivOfEq
      (coordinateAssignmentIdeal_iInf_eq_bot I hpair hzero).symm).trans
      (Ideal.quotientInfRingEquivPiQuotient
        (coordinateAssignmentIdeal I) (coordinateAssignmentIdeal_pairwise I hpair)))

@[simp] theorem coordinateAssignmentEquiv_apply
    (I : σ → ι → Ideal R)
    (hpair : ∀ j, Pairwise fun i h => IsCoprime (I j i) (I j h))
    (hzero : ∀ j, (⨅ i, I j i) = ⊥) (a : R) (f : σ → ι) :
    coordinateAssignmentEquiv I hpair hzero a f =
      Ideal.Quotient.mk (coordinateAssignmentIdeal I f) a := by
  rfl

/-- The same map preserves any given coefficient algebra structure. -/
noncomputable def coordinateAssignmentAlgEquiv
    (K : Type*) [CommSemiring K] [Algebra K R]
    (I : σ → ι → Ideal R)
    (hpair : ∀ j, Pairwise fun i h => IsCoprime (I j i) (I j h))
    (hzero : ∀ j, (⨅ i, I j i) = ⊥) :
    R ≃ₐ[K] ∀ f : σ → ι, R ⧸ coordinateAssignmentIdeal I f where
  __ := coordinateAssignmentEquiv I hpair hzero
  commutes' k := by
    ext f
    change Ideal.Quotient.mk (coordinateAssignmentIdeal I f)
      (algebraMap K R k) = algebraMap K (R ⧸ coordinateAssignmentIdeal I f) k
    exact (Ideal.Quotient.mkₐ K (coordinateAssignmentIdeal I f)).commutes k

theorem isCoprime_sub_of_isUnit_sub (x a b : R) (hab : IsUnit (a - b)) :
    IsCoprime (x - a) (x - b) := by
  obtain ⟨u, hu⟩ := isUnit_iff_exists_inv'.mp hab
  refine ⟨-u, u, ?_⟩
  calc
    -u * (x - a) + u * (x - b) = u * (a - b) := by ring
    _ = 1 := hu

def coordinateRootPowerIdeal (x : σ → R) (c : ι → R) (N : ℕ)
    (j : σ) (i : ι) : Ideal R :=
  Ideal.span {(x j - c i) ^ N}

/-- The assignment ideal is exactly the ideal generated by the selected
coordinate powers, rather than a new abstract component. -/
theorem coordinateRootAssignmentIdeal_eq_span
    (x : σ → R) (c : ι → R) (N : ℕ) (f : σ → ι) :
    coordinateAssignmentIdeal (coordinateRootPowerIdeal x c N) f =
      Ideal.span (Set.range fun j => (x j - c (f j)) ^ N) := by
  apply le_antisymm
  · apply iSup_le
    intro j
    apply Ideal.span_le.mpr
    intro a ha
    rcases ha with rfl
    exact Ideal.subset_span ⟨j, rfl⟩
  · apply Ideal.span_le.mpr
    rintro z ⟨j, rfl⟩
    apply le_iSup (fun j => coordinateRootPowerIdeal x c N j (f j)) j
    exact Ideal.subset_span (Set.mem_singleton _)

theorem coordinateRootPowerIdeal_pairwise
    (x : σ → R) (c : ι → R) (N : ℕ)
    (hc : Pairwise fun i h => IsUnit (c i - c h)) (j : σ) :
    Pairwise fun i h =>
      IsCoprime (coordinateRootPowerIdeal x c N j i)
        (coordinateRootPowerIdeal x c N j h) := by
  intro i h hih
  apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
  exact (isCoprime_sub_of_isUnit_sub (x j) (c i) (c h) (hc hih)).pow

theorem coordinateRootPowerIdeal_iInf_eq_bot
    (x : σ → R) (c : ι → R) (N : ℕ)
    (hc : Pairwise fun i h => IsUnit (c i - c h))
    (hann : ∀ j, (∏ i, (x j - c i) ^ N) = 0) (j : σ) :
    (⨅ i, coordinateRootPowerIdeal x c N j i) = ⊥ := by
  classical
  have hprod : (∏ i, coordinateRootPowerIdeal x c N j i) =
      ⨅ i, coordinateRootPowerIdeal x c N j i := by
    simpa only [Finset.mem_univ, iInf_true] using
      Ideal.prod_eq_iInf_of_pairwise_isCoprime
        (s := (Finset.univ : Finset ι))
        (J := coordinateRootPowerIdeal x c N j)
        (by
          intro i hi h hh hih
          exact coordinateRootPowerIdeal_pairwise x c N hc j hih)
  rw [← hprod]
  change (∏ i, Ideal.span ({(x j - c i) ^ N} : Set R)) = ⊥
  rw [Ideal.prod_span_singleton, hann j]
  simp

/-- Coordinates satisfying the displayed annihilating relations split
into the actual assignment quotients. Exponents may include zero; no
nontriviality or algebraic-closure assumption is hidden in this statement. -/
noncomputable def coordinateRootAssignmentEquiv
    (x : σ → R) (c : ι → R) (N : ℕ)
    (hc : Pairwise fun i h => IsUnit (c i - c h))
    (hann : ∀ j, (∏ i, (x j - c i) ^ N) = 0) :
    R ≃+* ∀ f : σ → ι,
      R ⧸ coordinateAssignmentIdeal (coordinateRootPowerIdeal x c N) f :=
  coordinateAssignmentEquiv (coordinateRootPowerIdeal x c N)
    (coordinateRootPowerIdeal_pairwise x c N hc)
    (coordinateRootPowerIdeal_iInf_eq_bot x c N hc hann)

noncomputable def coordinateRootAssignmentAlgEquiv
    (K : Type*) [CommSemiring K] [Algebra K R]
    (x : σ → R) (c : ι → R) (N : ℕ)
    (hc : Pairwise fun i h => IsUnit (c i - c h))
    (hann : ∀ j, (∏ i, (x j - c i) ^ N) = 0) :
    R ≃ₐ[K] ∀ f : σ → ι,
      R ⧸ coordinateAssignmentIdeal (coordinateRootPowerIdeal x c N) f :=
  coordinateAssignmentAlgEquiv K (coordinateRootPowerIdeal x c N)
    (coordinateRootPowerIdeal_pairwise x c N hc)
    (coordinateRootPowerIdeal_iInf_eq_bot x c N hc hann)

@[simp] theorem coordinateRootAssignmentEquiv_apply
    (x : σ → R) (c : ι → R) (N : ℕ)
    (hc : Pairwise fun i h => IsUnit (c i - c h))
    (hann : ∀ j, (∏ i, (x j - c i) ^ N) = 0) (a : R) (f : σ → ι) :
    coordinateRootAssignmentEquiv x c N hc hann a f =
      Ideal.Quotient.mk
        (coordinateAssignmentIdeal (coordinateRootPowerIdeal x c N) f) a :=
  rfl

end HigherSpecht
end
end CanonicalSource12

section CanonicalSource13
/- Source: HigherSpecht/FiberAssignmentDecomposition.lean -/



/-!
# The split fiber as the product of its actual local block quotients

The coordinate characteristic relation supplies the annihilation needed
by simultaneous Chinese remainders.  The third isomorphism theorem then
puts every factor back in the original polynomial ring.  Incorrect root
multiplicities give zero factors, which are removed by an explicit
restriction equivalence.  Correct assignments have exactly the block
ideals proved in `FiberComponentIdeals`.

The last equivalence has genuine local block quotients as its factors.
Identifying those quotients with the paper's displayed tensor products is
a separate algebraic equivalence, not built into their definition.
-/

noncomputable section

open Finset MvPolynomial TauCeti
open scoped Polynomial BigOperators Classical

namespace HigherSpecht

variable {R : Type*} [CommRing R]
variable {n m : ℕ} {lam : YoungDiagram} {ι : Type*} [Fintype ι]

theorem root_multiplicities_sum_of_factorization [Nontrivial R]
    (hsize : lam.card + m = n) (Q : R[X]) (hQ : Q.Monic) (hdeg : Q.natDegree = m)
    (c : ι → R) (r : ι → ℕ)
    (hfactor : Polynomial.X ^ lam.card * Q =
      ∏ i : ι, (Polynomial.X - Polynomial.C (c i)) ^ r i) :
    (∑ i, r i) = n := by
  have h := congrArg Polynomial.natDegree hfactor
  rw [(Polynomial.monic_X_pow _).natDegree_mul hQ,
    Polynomial.natDegree_X_pow, hdeg,
    Polynomial.natDegree_prod_of_monic (R := R) (Finset.univ : Finset ι)
      (f := fun i => (Polynomial.X - Polynomial.C (c i)) ^ r i)
      (fun i _ => (Polynomial.monic_X_sub_C (c i)).pow (r i))] at h
  have hterm (i : ι) :
      ((Polynomial.X - Polynomial.C (c i)) ^ r i).natDegree = r i := by
    rw [(Polynomial.monic_X_sub_C (c i)).natDegree_pow,
      Polynomial.natDegree_X_sub_C, mul_one]
  simp_rw [hterm] at h
  exact h.symm.trans hsize

theorem polynomialFiber_coordinate_root_annihilation
    (hsize : lam.card + m = n) (Q : R[X]) (hQ : Q.Monic) (hdeg : Q.natDegree = m)
    (c : ι → R) (r : ι → ℕ)
    (hfactor : Polynomial.X ^ lam.card * Q =
      ∏ i : ι, (Polynomial.X - Polynomial.C (c i)) ^ r i)
    (N : ℕ) (hr : ∀ i, r i ≤ N) (j : Fin n) :
    (∏ i : ι, (fiberCoordinate (n := n) (lam := lam) (m := m) (Q := Q) j -
      algebraMap R (PolynomialFiber R n lam m Q) (c i)) ^ N) = 0 := by
  let x := fiberCoordinate (n := n) (lam := lam) (m := m) (Q := Q) j
  have hz := coordinateCharacteristic_eval_root Finset.univ
    (fiberCoordinate (n := n) (lam := lam) (m := m) (Q := Q)) (Finset.mem_univ j)
  rw [polynomialFiber_characteristic hsize Q hQ hdeg] at hz
  have hm := congrArg (Polynomial.map (algebraMap R (PolynomialFiber R n lam m Q))) hfactor
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_C] at hm
  rw [hm] at hz
  simp only [Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C] at hz
  calc
    (∏ i : ι, (x - algebraMap R (PolynomialFiber R n lam m Q) (c i)) ^ N) =
        (∏ i : ι, (x - algebraMap R (PolynomialFiber R n lam m Q) (c i)) ^ r i) *
          (∏ i : ι, (x - algebraMap R (PolynomialFiber R n lam m Q) (c i)) ^ (N - r i)) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      rw [← pow_add, Nat.add_sub_of_le (hr i)]
    _ = 0 := by rw [hz, zero_mul]

theorem coordinateAssignmentIdeal_fiber_eq_map
    (Q : R[X]) (c : ι → R) (f : Fin n → ι) (N : ℕ) :
    coordinateAssignmentIdeal
        (coordinateRootPowerIdeal
          (fiberCoordinate (n := n) (lam := lam) (m := m) (Q := Q))
          (fun i => algebraMap R (PolynomialFiber R n lam m Q) (c i)) N) f =
      (assignedCoordinatePowerIdeal R c f N).map
        (Ideal.Quotient.mk (polynomialFiberIdeal R n lam m Q)) := by
  rw [coordinateRootAssignmentIdeal_eq_span, assignedCoordinatePowerIdeal,
    Ideal.map_span, ← Set.range_comp]
  congr 1

/-- The individual CRT quotient is literally the quotient by the sum of the
original fiber ideal and the selected coordinate power ideal. -/
def fiberAssignmentFactorEquiv
    (Q : R[X]) (c : ι → R) (f : Fin n → ι) (N : ℕ) :
    (PolynomialFiber R n lam m Q ⧸ coordinateAssignmentIdeal
      (coordinateRootPowerIdeal
        (fiberCoordinate (n := n) (lam := lam) (m := m) (Q := Q))
        (fun i => algebraMap R (PolynomialFiber R n lam m Q) (c i)) N) f) ≃ₐ[R]
      (PolynomialRing n R ⧸ splitFiberComponentIdeal R lam m Q c f N) :=
  (Ideal.quotientEquivAlgOfEq R (coordinateAssignmentIdeal_fiber_eq_map Q c f N)).trans
    (DoubleQuot.quotQuotEquivQuotSupₐ R (polynomialFiberIdeal R n lam m Q)
      (assignedCoordinatePowerIdeal R c f N))

/-- The full actual CRT decomposition, before zero factors are discarded. -/
def polynomialFiberAssignmentEquiv
    (hsize : lam.card + m = n) (Q : R[X]) (hQ : Q.Monic) (hdeg : Q.natDegree = m)
    (c : ι → R) (r : ι → ℕ) (hc : Pairwise fun i j => IsUnit (c i - c j))
    (hfactor : Polynomial.X ^ lam.card * Q =
      ∏ i : ι, (Polynomial.X - Polynomial.C (c i)) ^ r i)
    (N : ℕ) (hr : ∀ i, r i ≤ N) :
    PolynomialFiber R n lam m Q ≃ₐ[R]
      ∀ f : Fin n → ι, PolynomialRing n R ⧸ splitFiberComponentIdeal R lam m Q c f N :=
  (coordinateRootAssignmentAlgEquiv R
    (fiberCoordinate (n := n) (lam := lam) (m := m) (Q := Q))
    (fun i => algebraMap R (PolynomialFiber R n lam m Q) (c i)) N
    (fun i j hij => by
      change IsUnit (algebraMap R (PolynomialFiber R n lam m Q) (c i) -
        algebraMap R (PolynomialFiber R n lam m Q) (c j))
      rw [← map_sub]
      exact (hc hij).map _)
    (polynomialFiber_coordinate_root_annihilation hsize Q hQ hdeg c r hfactor N hr)).trans
      (AlgEquiv.piCongrRight fun f => fiberAssignmentFactorEquiv Q c f N)

/-- Removing factors already proved to be zero rings is an actual algebra
equivalence, not a convention about products. -/
def piRestrictSubsingletonAlgEquiv {J : Type*} (p : J → Prop)
    (A : J → Type*) [∀ j, CommRing (A j)] [∀ j, Algebra R (A j)]
    (hzero : ∀ j, ¬p j → Subsingleton (A j)) :
    (∀ j, A j) ≃ₐ[R] ∀ j : {j : J // p j}, A j.val where
  toFun f j := f j.val
  invFun f j := if hj : p j then f ⟨j, hj⟩ else 0
  left_inv f := by
    funext j
    dsimp only
    by_cases hj : p j
    · simp only [dif_pos hj]
    · rw [dif_neg hj]
      exact (hzero j hj).elim _ _
  right_inv f := by
    funext j
    dsimp only
    rw [dif_pos j.property]
  map_mul' f g := rfl
  map_add' f g := rfl
  commutes' r := rfl

abbrev PrescribedRootAssignments (n : ℕ) (r : ι → ℕ) :=
  {f : Fin n → ι // ∀ i, Fintype.card {j : Fin n // f j = i} = r i}

variable {K : Type*} [Field K]

/-- A wrong-count assignment has the zero quotient, proved from its
nilpotent deviations and the actual characteristic polynomial. -/
theorem splitFiberComponentIdeal_eq_top_of_wrong_counts
    (hsize : lam.card + m = n) (Q : K[X]) (hQ : Q.Monic) (hdeg : Q.natDegree = m)
    (c : ι → K) (hc : Function.Injective c) (r : ι → ℕ)
    (hfactor : Polynomial.X ^ lam.card * Q =
      ∏ i : ι, (Polynomial.X - Polynomial.C (c i)) ^ r i)
    (f : Fin n → ι) (N : ℕ)
    (hwrong : ¬∀ i, Fintype.card {j : Fin n // f j = i} = r i) :
    splitFiberComponentIdeal K lam m Q c f N = ⊤ := by
  by_contra htop
  let I := splitFiberComponentIdeal K lam m Q c f N
  let A := PolynomialRing n K ⧸ I
  letI : Nontrivial A := Ideal.Quotient.nontrivial_iff.mpr htop
  let phi : PolynomialRing n K →ₐ[K] A := Ideal.Quotient.mkₐ K I
  have hI : polynomialFiberIdeal K n lam m Q ≤ RingHom.ker phi.toRingHom := by
    intro p hp
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left hp)
  have hnil (j : Fin n) :
      IsNilpotent (phi (MvPolynomial.X j) - algebraMap K A (c (f j))) := by
    refine ⟨N, ?_⟩
    have hp : (MvPolynomial.X j - MvPolynomial.C (c (f j))) ^ N ∈ I :=
      Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩)
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hp
    change phi ((MvPolynomial.X j - MvPolynomial.C (c (f j))) ^ N) = 0 at hz
    rw [map_pow, map_sub, show phi (MvPolynomial.C (c (f j))) =
      algebraMap K A (c (f j)) from phi.commutes _] at hz
    exact hz
  have hchar := characteristic_of_polynomialFiberIdeal_le_kernel phi hsize Q hQ hdeg hI
  have hproduct : coordinateCharacteristic Finset.univ (fun j => phi (MvPolynomial.X j)) =
      ∏ i : ι, (Polynomial.X - Polynomial.C (algebraMap K A (c i))) ^ r i := by
    rw [hchar]
    have hm := congrArg (Polynomial.map (algebraMap K A)) hfactor
    simpa only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_C] using hm
  exact hwrong (fiber_assigned_root_groups (fun j => phi (MvPolynomial.X j))
    c hc f r hnil hproduct).1

/-- The exact split-fiber decomposition into the actual local block ideals.
The arbitrary repeated roots and all field characteristics are retained. -/
def polynomialFiberBlockProductEquiv
    (hsize : lam.card + m = n) (Q : K[X]) (hQ : Q.Monic) (hdeg : Q.natDegree = m)
    (r0 : ℕ) (c : ι → K) (hc : Function.Injective c) (z : ι) (r : ι → ℕ)
    (hcz : c z = 0) (hrz : r z = lam.card + r0)
    (hfactor : Polynomial.X ^ lam.card * Q =
      ∏ i : ι, (Polynomial.X - Polynomial.C (c i)) ^ r i) :
    PolynomialFiber K n lam m Q ≃ₐ[K]
      ∀ f : PrescribedRootAssignments n r,
        PolynomialRing n K ⧸ splitRootBlockIdeal K lam r0 c f.val z := by
  have hroot : Pairwise fun i j => IsUnit (c i - c j) :=
    fun i j hij => isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (hc.ne hij))
  have hsum := root_multiplicities_sum_of_factorization hsize Q hQ hdeg c r hfactor
  have hr : ∀ i, r i ≤ n + 1 := by
    intro i
    have hi := Finset.single_le_sum (fun j hj => Nat.zero_le (r j)) (Finset.mem_univ i)
    rw [hsum] at hi
    omega
  let E := polynomialFiberAssignmentEquiv hsize Q hQ hdeg c r hroot hfactor (n + 1) hr
  let F := piRestrictSubsingletonAlgEquiv (R := K)
    (fun f : Fin n → ι => ∀ i, Fintype.card {j : Fin n // f j = i} = r i)
    (fun f => PolynomialRing n K ⧸ splitFiberComponentIdeal K lam m Q c f (n + 1))
    (fun f hf => Ideal.Quotient.subsingleton_iff.mpr
      (splitFiberComponentIdeal_eq_top_of_wrong_counts hsize Q hQ hdeg c hc r hfactor
        f (n + 1) hf))
  exact (E.trans F).trans (AlgEquiv.piCongrRight fun f =>
    Ideal.quotientEquivAlgOfEq K
      (splitFiberComponentIdeal_eq_blockIdeal hsize Q hQ hdeg r0 c f.val z r
        hcz hroot hrz f.property hfactor (n + 1) (by omega)))

end HigherSpecht
end
end CanonicalSource13

section CanonicalSource14
/- Source: HigherSpecht/FiberBlockShapes.lean -/



/-!
# The actual Springer shapes of every local fiber factor

A single column has only the positive global elementary generators.
Translating the coordinate group at each nonzero root therefore identifies
its relations with the genuine column-partition Springer ideal.  The zero
group retains the original ideal for the partition enlarged by ones.
The resulting sum of disjoint Springer ideals is precisely the local ideal
already obtained from Chinese remainders.
-/

noncomputable section

open Finset MvPolynomial TauCeti
open scoped Polynomial BigOperators Classical

namespace HigherSpecht

variable {R : Type*} [CommRing R] {n : ℕ}

def columnPartition (k : ℕ) : YoungDiagram := adjoinOnes ⊥ k

@[simp] theorem columnPartition_card (k : ℕ) : (columnPartition k).card = k := by
  simp [columnPartition, adjoinOnes_card, YoungDiagram.card]

theorem columnPartition_cells (k : ℕ) :
    (columnPartition k).cells = Finset.range k ×ˢ {0} := by
  simp only [columnPartition, adjoinOnes, YoungDiagram.cells_bot,
    Finset.empty_union, YoungDiagram.colLen_bot, zero_add]

theorem columnTail_columnPartition_of_pos (k : ℕ) {h : ℕ} (hh : 0 < h) :
    columnTail (columnPartition k) h = 0 := by
  rw [columnPartition, columnTail_adjoinOnes_of_pos _ _ hh]
  simp only [columnTail, YoungDiagram.cells_bot, Finset.filter_empty, Finset.card_empty]

@[simp] theorem shiftedElementaryOn_zero (A : Finset (Fin n)) (d : ℕ) :
    shiftedElementaryOn (R := R) A 0 d = elementaryOn A d := by
  simp only [shiftedElementaryOn, elementaryValue, map_zero, sub_zero, elementaryOn]

/-- The column Springer ideal is exactly the global elementary ideal. -/
theorem blockSpringerIdeal_column_eq_global (A : Finset (Fin n)) (k : ℕ)
    (hA : A.card = k) :
    blockSpringerIdeal R A (columnPartition k) = shiftedGlobalIdeal R A 0 := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro p ⟨Y, d, hYA, hd, hth, rfl⟩
    by_cases hYAeq : Y = A
    · subst Y
      rw [Nat.sub_self, columnTail_zero, columnPartition_card, ← hA] at hth
      have hdpos : 0 < d := by omega
      have hm : shiftedElementaryOn (R := R) A 0 (d - 1 + 1) ∈
          shiftedGlobalIdeal R A 0 := Ideal.subset_span ⟨d - 1, rfl⟩
      rw [Nat.sub_add_cancel (by omega : 1 ≤ d), shiftedElementaryOn_zero] at hm
      exact hm
    · have hcard := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hYA, hYAeq⟩)
      rw [columnTail_columnPartition_of_pos k (by omega), Nat.cast_zero, sub_zero] at hth
      omega
  · apply Ideal.span_le.mpr
    rintro p ⟨d, rfl⟩
    change shiftedElementaryOn (R := R) A 0 (d + 1) ∈ blockSpringerIdeal R A (columnPartition k)
    rw [shiftedElementaryOn_zero]
    exact blockSpringer_global_elementary A (columnPartition k)
      (by simpa only [columnPartition_card] using hA) (by omega)

theorem coordinateTranslation_elementaryOn_const
    (b : Fin n → R) (A : Finset (Fin n)) (c : R)
    (hb : ∀ j ∈ A, b j = -c) (d : ℕ) :
    coordinateTranslation b (elementaryOn A d) = shiftedElementaryOn A c d := by
  simp only [elementaryOn, shiftedElementaryOn, elementaryValue, map_sum, map_prod]
  apply Finset.sum_congr rfl
  intro Y hY
  apply Finset.prod_congr rfl
  intro j hj
  have hjA := (Finset.mem_powersetCard.mp hY).1 hj
  rw [coordinateTranslation_X, hb j hjA, map_neg]
  simp only [sub_eq_add_neg]

theorem map_shiftedGlobalIdeal_of_translation
    (b : Fin n → R) (A : Finset (Fin n)) (c : R)
    (hb : ∀ j ∈ A, b j = -c) :
    (shiftedGlobalIdeal R A 0).map (coordinateTranslation b).toRingHom =
      shiftedGlobalIdeal R A c := by
  unfold shiftedGlobalIdeal
  rw [Ideal.map_span, ← Set.range_comp]
  congr 1
  apply congrArg Set.range
  funext d
  change coordinateTranslation b (shiftedElementaryOn (R := R) A 0 (d + 1)) =
    shiftedElementaryOn A c (d + 1)
  rw [shiftedElementaryOn_zero, coordinateTranslation_elementaryOn_const b A c hb]

theorem map_blockSpringerIdeal_of_translation_zero
    (b : Fin n → R) (A : Finset (Fin n)) (mu : YoungDiagram)
    (hb : ∀ j ∈ A, b j = 0) :
    (blockSpringerIdeal R A mu).map (coordinateTranslation b).toRingHom =
      blockSpringerIdeal R A mu := by
  have hfixed {Y : Finset (Fin n)} (hY : Y ⊆ A) (d : ℕ) :
      coordinateTranslation b (elementaryOn (R := R) Y d) = elementaryOn Y d := by
    rw [coordinateTranslation_elementaryOn_const b Y 0
      (fun j hj => by simpa only [neg_zero] using hb j (hY hj)),
      shiftedElementaryOn_zero]
  unfold blockSpringerIdeal
  rw [Ideal.map_span]
  congr 1
  ext p
  constructor
  · rintro ⟨q, ⟨Y, d, hYA, hd, hth, rfl⟩, rfl⟩
    exact ⟨Y, d, hYA, hd, hth, hfixed hYA d⟩
  · rintro ⟨Y, d, hYA, hd, hth, rfl⟩
    exact ⟨elementaryOn Y d, ⟨Y, d, hYA, hd, hth, rfl⟩, hfixed hYA d⟩

variable {ι : Type*} [Fintype ι]

def rootBlockShape (lam : YoungDiagram) (r0 : ℕ) (r : ι → ℕ) (z i : ι) : YoungDiagram :=
  if i = z then adjoinOnes lam r0 else columnPartition (r i)

theorem rootBlockShape_card (lam : YoungDiagram) (r0 : ℕ) (r : ι → ℕ) (z : ι)
    (hrz : r z = lam.card + r0) (i : ι) :
    (rootBlockShape lam r0 r z i).card = r i := by
  by_cases hi : i = z
  · subst i
    simp only [rootBlockShape, if_pos rfl, if_true, adjoinOnes_card, hrz]
  · simp only [rootBlockShape, if_neg hi, columnPartition_card]

def unshiftedRootBlockIdeal (R : Type*) [CommRing R]
    (lam : YoungDiagram) (r0 : ℕ) (r : ι → ℕ) (f : Fin n → ι) (z : ι) :
    Ideal (PolynomialRing n R) :=
  ⨆ i : ι, blockSpringerIdeal R (rootGroupFinset f i) (rootBlockShape lam r0 r z i)

/-- The component equations are exactly the translations of the genuine
Springer factors with the shapes displayed in Theorem 7.1. -/
theorem map_unshiftedRootBlockIdeal
    (lam : YoungDiagram) (r0 : ℕ) (r : ι → ℕ)
    (c : ι → R) (f : Fin n → ι) (z : ι) (hcz : c z = 0)
    (hrz : r z = lam.card + r0)
    (hcount : ∀ i, Fintype.card {j : Fin n // f j = i} = r i) :
    (unshiftedRootBlockIdeal R lam r0 r f z).map
        (coordinateTranslation (fun j => -c (f j))).toRingHom =
      splitRootBlockIdeal R lam r0 c f z := by
  let b : Fin n → R := fun j => -c (f j)
  have hzero :
      (blockSpringerIdeal R (rootGroupFinset f z) (adjoinOnes lam r0)).map
          (coordinateTranslation b).toRingHom =
        blockSpringerIdeal R (rootGroupFinset f z) (adjoinOnes lam r0) := by
    apply map_blockSpringerIdeal_of_translation_zero
    intro j hj
    simp only [b, (mem_rootGroupFinset f z j).mp hj, hcz, neg_zero]
  have hnonzero (i : ι) (hi : i ≠ z) :
      (blockSpringerIdeal R (rootGroupFinset f i) (rootBlockShape lam r0 r z i)).map
          (coordinateTranslation b).toRingHom =
        shiftedGlobalIdeal R (rootGroupFinset f i) (c i) := by
    rw [rootBlockShape, if_neg hi,
      blockSpringerIdeal_column_eq_global _ (r i)
        (by rw [rootGroupFinset_card, hcount i])]
    apply map_shiftedGlobalIdeal_of_translation
    intro j hj
    simp only [b, (mem_rootGroupFinset f i j).mp hj]
  unfold unshiftedRootBlockIdeal
  rw [Ideal.map_iSup]
  apply le_antisymm
  · apply iSup_le
    intro i
    by_cases hi : i = z
    · subst i
      change (blockSpringerIdeal R (rootGroupFinset f z)
        (rootBlockShape lam r0 r z z)).map (coordinateTranslation b).toRingHom ≤
          splitRootBlockIdeal R lam r0 c f z
      simp only [rootBlockShape, if_pos rfl, if_true]
      rw [hzero]
      exact le_sup_left
    · rw [hnonzero i hi]
      exact le_trans (le_iSup (fun i : ι =>
        shiftedGlobalIdeal R (rootGroupFinset f i) (c i)) i) le_sup_right
  · apply sup_le
    · have h := le_iSup
        (fun i => (blockSpringerIdeal R (rootGroupFinset f i)
          (rootBlockShape lam r0 r z i)).map (coordinateTranslation b).toRingHom) z
      simpa only [rootBlockShape, if_pos rfl, if_true, hzero] using h
    · apply iSup_le
      intro i
      by_cases hi : i = z
      · subst i
        rw [hcz]
        have hglobal : shiftedGlobalIdeal R (rootGroupFinset f z) 0 ≤
            blockSpringerIdeal R (rootGroupFinset f z) (adjoinOnes lam r0) := by
          apply Ideal.span_le.mpr
          rintro p ⟨d, rfl⟩
          change shiftedElementaryOn (R := R) (rootGroupFinset f z) 0 (d + 1) ∈
            blockSpringerIdeal R (rootGroupFinset f z) (adjoinOnes lam r0)
          rw [shiftedElementaryOn_zero]
          exact blockSpringer_global_elementary _ _
            (by rw [rootGroupFinset_card, hcount z, adjoinOnes_card, hrz]) (by omega)
        have hzle := le_iSup
          (fun i => (blockSpringerIdeal R (rootGroupFinset f i)
            (rootBlockShape lam r0 r z i)).map (coordinateTranslation b).toRingHom) z
        simp only [rootBlockShape, if_pos rfl, if_true, hzero] at hzle
        exact hglobal.trans hzle
      · rw [← hnonzero i hi]
        exact le_iSup (fun i : ι =>
          (blockSpringerIdeal R (rootGroupFinset f i) (rootBlockShape lam r0 r z i)).map
            (coordinateTranslation b).toRingHom) i

/-- The explicit translation equivalence used before applying the tensor
product quotient theorem. -/
def rootBlockTranslationQuotientEquiv
    (lam : YoungDiagram) (r0 : ℕ) (r : ι → ℕ)
    (c : ι → R) (f : Fin n → ι) (z : ι) (hcz : c z = 0)
    (hrz : r z = lam.card + r0)
    (hcount : ∀ i, Fintype.card {j : Fin n // f j = i} = r i) :
    (PolynomialRing n R ⧸ splitRootBlockIdeal R lam r0 c f z) ≃ₐ[R]
      (PolynomialRing n R ⧸ unshiftedRootBlockIdeal R lam r0 r f z) :=
  (Ideal.quotientEquivAlg _ _ (coordinateTranslation (fun j => -c (f j)))
    (map_unshiftedRootBlockIdeal lam r0 r c f z hcz hrz hcount).symm).symm

end HigherSpecht
end
end CanonicalSource14

section CanonicalSource15
/- Source: HigherSpecht/RootBlockEnumerations.lean -/



/-!
# Faithful enumeration of the disjoint Springer factors

The local coordinate types are the actual fibers of the root assignment.
Their bijections with the numbered variables of the corresponding Springer
rings transport the original ideals by polynomial renaming.  The sum of
those transported ideals is exactly the unshifted local block ideal.
-/

noncomputable section

open Finset MvPolynomial TauCeti
open scoped Classical

namespace HigherSpecht

variable {R : Type*} [CommRing R] {n : ℕ} {ι : Type*} [Fintype ι]

abbrev RootFiberVariables (f : Fin n → ι) (i : ι) := {j : Fin n // f j = i}

def rootFiberVariableEquiv (lam : YoungDiagram) (r0 : ℕ) (r : ι → ℕ)
    (f : Fin n → ι) (z : ι) (hrz : r z = lam.card + r0)
    (hcount : ∀ i, Fintype.card (RootFiberVariables f i) = r i) (i : ι) :
    Fin (rootBlockShape lam r0 r z i).card ≃ RootFiberVariables f i :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, rootBlockShape_card lam r0 r z hrz i, hcount i])

def rootFiberEmbedding (lam : YoungDiagram) (r0 : ℕ) (r : ι → ℕ)
    (f : Fin n → ι) (z : ι) (hrz : r z = lam.card + r0)
    (hcount : ∀ i, Fintype.card (RootFiberVariables f i) = r i) (i : ι) :
    Fin (rootBlockShape lam r0 r z i).card ↪ Fin n where
  toFun j := (rootFiberVariableEquiv lam r0 r f z hrz hcount i j).val
  inj' a b h := (rootFiberVariableEquiv lam r0 r f z hrz hcount i).injective
    (Subtype.ext h)

theorem rootFiberEmbedding_range (lam : YoungDiagram) (r0 : ℕ) (r : ι → ℕ)
    (f : Fin n → ι) (z : ι) (hrz : r z = lam.card + r0)
    (hcount : ∀ i, Fintype.card (RootFiberVariables f i) = r i) (i : ι) :
    (Finset.univ : Finset (Fin (rootBlockShape lam r0 r z i).card)).map
        (rootFiberEmbedding lam r0 r f z hrz hcount i) = rootGroupFinset f i := by
  ext j
  constructor
  · intro hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hj
    apply (mem_rootGroupFinset f i _).mpr
    exact (rootFiberVariableEquiv lam r0 r f z hrz hcount i a).property
  · intro hj
    let v : RootFiberVariables f i := ⟨j, (mem_rootGroupFinset f i j).mp hj⟩
    refine Finset.mem_map.mpr ⟨
      (rootFiberVariableEquiv lam r0 r f z hrz hcount i).symm v,
      Finset.mem_univ _, ?_⟩
    change ((rootFiberVariableEquiv lam r0 r f z hrz hcount i)
      ((rootFiberVariableEquiv lam r0 r f z hrz hcount i).symm v)).val = j
    exact congrArg (fun x : RootFiberVariables f i => x.val)
      ((rootFiberVariableEquiv lam r0 r f z hrz hcount i).apply_symm_apply v)

def rootFiberSpringerIdeal (R : Type*) [CommRing R]
    (lam : YoungDiagram) (r0 : ℕ) (r : ι → ℕ)
    (f : Fin n → ι) (z : ι) (hrz : r z = lam.card + r0)
    (hcount : ∀ i, Fintype.card (RootFiberVariables f i) = r i) (i : ι) :
    Ideal (MvPolynomial (RootFiberVariables f i) R) :=
  (springerIdeal R (rootBlockShape lam r0 r z i)).map
    (MvPolynomial.rename (rootFiberVariableEquiv lam r0 r f z hrz hcount i)).toRingHom

/-- Each actual block quotient is the original Springer ring, with an
explicit variable renaming and no dimension argument. -/
def rootFiberSpringerQuotientEquiv (lam : YoungDiagram) (r0 : ℕ) (r : ι → ℕ)
    (f : Fin n → ι) (z : ι) (hrz : r z = lam.card + r0)
    (hcount : ∀ i, Fintype.card (RootFiberVariables f i) = r i) (i : ι) :
    (MvPolynomial (RootFiberVariables f i) R ⧸
      rootFiberSpringerIdeal R lam r0 r f z hrz hcount i) ≃ₐ[R]
        SpringerRing R (rootBlockShape lam r0 r z i) :=
  (Ideal.quotientEquivAlg _ _
    (MvPolynomial.renameEquiv R (rootFiberVariableEquiv lam r0 r f z hrz hcount i))
    rfl).symm

theorem rootFiberRename_comp (lam : YoungDiagram) (r0 : ℕ) (r : ι → ℕ)
    (f : Fin n → ι) (z : ι) (hrz : r z = lam.card + r0)
    (hcount : ∀ i, Fintype.card (RootFiberVariables f i) = r i) (i : ι) :
    (MvPolynomial.rename (R := R) (fun j : RootFiberVariables f i => j.val)).toRingHom.comp
        (MvPolynomial.rename (R := R) (rootFiberVariableEquiv lam r0 r f z hrz hcount i)).toRingHom =
      (MvPolynomial.rename (R := R) (rootFiberEmbedding lam r0 r f z hrz hcount i)).toRingHom := by
  have h :
      (MvPolynomial.rename (R := R) (fun j : RootFiberVariables f i => j.val)).comp
          (MvPolynomial.rename (R := R) (rootFiberVariableEquiv lam r0 r f z hrz hcount i)) =
        MvPolynomial.rename (R := R) (rootFiberEmbedding lam r0 r f z hrz hcount i) := by
    apply MvPolynomial.algHom_ext
    intro j
    rw [AlgHom.comp_apply, MvPolynomial.rename_X, MvPolynomial.rename_X,
      MvPolynomial.rename_X] <;> rfl
  simpa only [AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom] using
    congrArg (fun F :
      MvPolynomial (Fin (rootBlockShape lam r0 r z i).card) R →ₐ[R] PolynomialRing n R =>
        F.toRingHom) h

theorem map_rootFiberSpringerIdeal_subtype (lam : YoungDiagram) (r0 : ℕ) (r : ι → ℕ)
    (f : Fin n → ι) (z : ι) (hrz : r z = lam.card + r0)
    (hcount : ∀ i, Fintype.card (RootFiberVariables f i) = r i) (i : ι) :
    (rootFiberSpringerIdeal R lam r0 r f z hrz hcount i).map
        (MvPolynomial.rename (fun j : RootFiberVariables f i => j.val)).toRingHom =
      blockSpringerIdeal R (rootGroupFinset f i) (rootBlockShape lam r0 r z i) := by
  rw [rootFiberSpringerIdeal, Ideal.map_map, rootFiberRename_comp]
  have h := blockSpringerIdeal_eq_map (R := R) (rootBlockShape lam r0 r z i)
    (rootFiberEmbedding lam r0 r f z hrz hcount i)
  rw [rootFiberEmbedding_range] at h
  simpa only [AlgHom.toRingHom_eq_coe, Ideal.map_coe] using h.symm

theorem rootFiberSpringerIdeal_iSup (lam : YoungDiagram) (r0 : ℕ) (r : ι → ℕ)
    (f : Fin n → ι) (z : ι) (hrz : r z = lam.card + r0)
    (hcount : ∀ i, Fintype.card (RootFiberVariables f i) = r i) :
    (⨆ i : ι, (rootFiberSpringerIdeal R lam r0 r f z hrz hcount i).map
      (MvPolynomial.rename (fun j : RootFiberVariables f i => j.val)).toRingHom) =
      unshiftedRootBlockIdeal R lam r0 r f z := by
  apply iSup_congr
  intro i
  exact map_rootFiberSpringerIdeal_subtype lam r0 r f z hrz hcount i

end HigherSpecht
end
end CanonicalSource15

section CanonicalSource16
/- Source: HigherSpecht/FiberParameters.lean -/



/-!
# Parameter tuples and monic parameter polynomials

The inverse maps are explicit.  In particular quantifying over the monic
polynomial in the fiber calculation loses no parameter tuples, including
the unique tuple when `m = 0`.
-/

noncomputable section

open Finset MvPolynomial TauCeti

namespace HigherSpecht

variable {R : Type*} [CommRing R]

theorem coeff_finitePolynomialSum {m : ℕ} (f : Fin m → R) (d : ℕ) :
    (∑ i : Fin m, Polynomial.C (f i) * Polynomial.X ^ i.val).coeff d =
      if h : d < m then f ⟨d, h⟩ else 0 := by
  classical
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  by_cases hd : d < m
  · rw [dif_pos hd]
    calc
      (∑ i : Fin m, if d = i.val then f i else 0) =
          (if d = (⟨d, hd⟩ : Fin m).val then f ⟨d, hd⟩ else 0) := by
        apply Finset.sum_eq_single (⟨d, hd⟩ : Fin m)
        · intro i hi hne
          have hval : d ≠ i.val := by
            intro h
            exact hne (Fin.ext h.symm)
          simp [hval]
        · simp
      _ = f ⟨d, hd⟩ := if_pos rfl
  · rw [dif_neg hd]
    apply Finset.sum_eq_zero
    intro i hi
    have hval : d ≠ i.val := by omega
    simp [hval]

def parameterPolynomial {m : ℕ} (a : Fin m → R) : Polynomial R :=
  Polynomial.X ^ m + ∑ j : Fin m,
    Polynomial.C ((-1) ^ (m - j.val) * a ⟨m - j.val - 1, by omega⟩) *
      Polynomial.X ^ j.val

theorem parameterPolynomial_monic {m : ℕ} (a : Fin m → R) :
    (parameterPolynomial a).Monic :=
  Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _)

@[simp] theorem parameterPolynomial_coeff_top {m : ℕ} (a : Fin m → R) :
    (parameterPolynomial a).coeff m = 1 := by
  rw [parameterPolynomial, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    coeff_finitePolynomialSum]
  simp

theorem parameterPolynomial_coeff_lt {m : ℕ} (a : Fin m → R) {d : ℕ} (hd : d < m) :
    (parameterPolynomial a).coeff d =
      (-1) ^ (m - d) * a ⟨m - d - 1, by omega⟩ := by
  rw [parameterPolynomial, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    coeff_finitePolynomialSum, if_neg (by omega), dif_pos hd, zero_add]

theorem parameterPolynomial_degree_le {m : ℕ} (a : Fin m → R) :
    (parameterPolynomial a).degree ≤ m := by
  apply (Polynomial.degree_add_le _ _).trans
  exact max_le (Polynomial.degree_X_pow_le _)
    (Polynomial.degree_sum_fin_lt _).le

theorem parameterPolynomial_natDegree [Nontrivial R] {m : ℕ} (a : Fin m → R) :
    (parameterPolynomial a).natDegree = m := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (Polynomial.natDegree_le_iff_degree_le.mpr (parameterPolynomial_degree_le a))
  rw [parameterPolynomial_coeff_top]
  exact one_ne_zero

@[simp] theorem polynomialParameters_parameterPolynomial {m : ℕ} (a : Fin m → R) :
    polynomialParameters (parameterPolynomial a) m = a := by
  funext i
  rw [polynomialParameters,
    parameterPolynomial_coeff_lt a (by have := i.isLt; omega)]
  have hexp : m - (m - (i.val + 1)) = i.val + 1 := by have := i.isLt; omega
  have hind : (⟨m - (m - (i.val + 1)) - 1, by omega⟩ : Fin m) = i := by
    apply Fin.ext
    dsimp
    omega
  rw [hind, hexp, ← mul_assoc, ← mul_pow]
  simp

theorem parameterPolynomial_polynomialParameters {m : ℕ} (Q : Polynomial R)
    (hQ : Q.Monic) (hdeg : Q.natDegree = m) :
    parameterPolynomial (polynomialParameters Q m) = Q := by
  ext d
  by_cases hd : d < m
  · rw [parameterPolynomial_coeff_lt _ hd, polynomialParameters]
    have hi : m - d - 1 + 1 = m - d := by omega
    rw [hi, show m - (m - d) = d by omega, ← mul_assoc, ← mul_pow]
    simp
  · by_cases he : d = m
    · subst d
      rw [parameterPolynomial_coeff_top, ← hdeg, Polynomial.coeff_natDegree, hQ]
    · rw [Polynomial.coeff_eq_zero_of_degree_lt
        ((parameterPolynomial_degree_le _).trans_lt (by exact_mod_cast (by omega : m < d))),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

@[simp] theorem polynomialFiberIdeal_parameterPolynomial {n m : ℕ}
    (lam : YoungDiagram) (a : Fin m → R) :
    polynomialFiberIdeal R n lam m (parameterPolynomial a) =
      parameterFiberIdeal R n lam m a := by
  rw [polynomialFiberIdeal, polynomialParameters_parameterPolynomial]

/-- Every actual parameter tuple defines a finite module over the coefficient
ring.  Over a field this is the required finite-dimensionality of the fiber. -/
theorem parameterFiber_moduleFinite [Nontrivial R] {n m : ℕ}
    {lam : YoungDiagram} (hsize : lam.card + m = n) (a : Fin m → R) :
    Module.Finite R (ParameterFiber R n lam m a) := by
  letI := polynomialFiber_moduleFinite hsize (parameterPolynomial a)
    (parameterPolynomial_monic a) (parameterPolynomial_natDegree a)
  exact Module.Finite.equiv
    (Ideal.quotientEquivAlgOfEq R
      (polynomialFiberIdeal_parameterPolynomial lam a)).toLinearEquiv

theorem parameterFiber_isArtinian {K : Type*} [Field K] {n m : ℕ}
    {lam : YoungDiagram} (hsize : lam.card + m = n) (a : Fin m → K) :
    IsArtinianRing (ParameterFiber K n lam m a) := by
  letI := parameterFiber_moduleFinite hsize a
  exact IsArtinianRing.of_finite K _

end HigherSpecht
end
end CanonicalSource16

section CanonicalSource17
/- Source: HigherSpecht/FiberMultiplicityUnits.lean -/



/-!
# Root multiplicities with invertible differences

Distinct roots with unit pairwise differences have unique multiplicities
over every nonzero commutative ring.  Coprimality isolates each root power,
and monicity compares its exact degree.  Reducing nilpotent coordinate
deviations to their constants then gives the same assigned-group count
without requiring the coefficient ring to be a field.  This is the form
needed over the integral ordered-root localization in Proposition 7.2.
-/

noncomputable section

open scoped Polynomial BigOperators Classical

namespace HigherSpecht

variable {A : Type*} [CommRing A] [Nontrivial A]
variable {ι : Type*} [Fintype ι]

theorem root_power_dvd_matching_factor
    (c : ι → A) (hc : Pairwise fun i j => IsUnit (c i - c j))
    (a b : ι → ℕ)
    (h : (∏ i : ι, (Polynomial.X - Polynomial.C (c i)) ^ a i) =
      ∏ i : ι, (Polynomial.X - Polynomial.C (c i)) ^ b i) (i : ι) :
    (Polynomial.X - Polynomial.C (c i)) ^ a i ∣
      (Polynomial.X - Polynomial.C (c i)) ^ b i := by
  have hcoprime : IsCoprime ((Polynomial.X - Polynomial.C (c i)) ^ a i)
      (∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (c j)) ^ b j) := by
    apply IsCoprime.prod_right
    intro j hj
    exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      (hc (Finset.mem_erase.mp hj).1.symm)).pow
  apply hcoprime.dvd_of_dvd_mul_right
  rw [Finset.mul_prod_erase Finset.univ
    (fun j => (Polynomial.X - Polynomial.C (c j)) ^ b j) (Finset.mem_univ i), ← h]
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

theorem root_multiplicities_unique_of_unit_differences
    (c : ι → A) (hc : Pairwise fun i j => IsUnit (c i - c j))
    (a b : ι → ℕ)
    (h : (∏ i : ι, (Polynomial.X - Polynomial.C (c i)) ^ a i) =
      ∏ i : ι, (Polynomial.X - Polynomial.C (c i)) ^ b i) : a = b := by
  have hle (u v : ι → ℕ)
      (huv : (∏ i : ι, (Polynomial.X - Polynomial.C (c i)) ^ u i) =
        ∏ i : ι, (Polynomial.X - Polynomial.C (c i)) ^ v i) (i : ι) : u i ≤ v i := by
    have hp := (Polynomial.monic_X_sub_C (c i)).pow (u i)
    have hq := (Polynomial.monic_X_sub_C (c i)).pow (v i)
    have hd := hp.natDegree_le_of_dvd hq.ne_zero
      (root_power_dvd_matching_factor c hc u v huv i)
    simpa only [(Polynomial.monic_X_sub_C (c i)).natDegree_pow,
      Polynomial.natDegree_X_sub_C, mul_one] using hd
  funext i
  exact Nat.le_antisymm (hle a b h i) (hle b a h.symm i)

/-- Counts are forced over any coefficient ring when the actual root
differences are units; the ring may have positive characteristic. -/
theorem assigned_root_counts_of_unit_differences
    {σ : Type*} [Fintype σ]
    (N : Ideal A) (hN : IsNilpotent N)
    (x : σ → A) (c : ι → A) (hc : Pairwise fun i j => IsUnit (c i - c j))
    (f : σ → ι) (r : ι → ℕ)
    (hresidue : ∀ j, Ideal.Quotient.mk N (x j) =
      Ideal.Quotient.mk N (c (f j)))
    (hproduct : (∏ j : σ, (Polynomial.X - Polynomial.C (x j))) =
      ∏ i : ι, (Polynomial.X - Polynomial.C (c i)) ^ r i) :
    ∀ i, Fintype.card {j : σ // f j = i} = r i := by
  letI : Nontrivial (A ⧸ N) := Ideal.Quotient.nontrivial_iff.mpr
    (nilpotent_ideal_ne_top N hN)
  have hm := congrArg (Polynomial.map (Ideal.Quotient.mk N)) hproduct
  simp only [Polynomial.map_prod, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, hresidue] at hm
  have hgroup :
      (∏ j : σ, (Polynomial.X - Polynomial.C (Ideal.Quotient.mk N (c (f j))))) =
        ∏ i : ι, (Polynomial.X - Polynomial.C (Ideal.Quotient.mk N (c i))) ^
          Fintype.card {j : σ // f j = i} := by
    rw [← Fintype.prod_fiberwise' f
      (fun i => Polynomial.X - Polynomial.C (Ideal.Quotient.mk N (c i)))]
    simp only [Finset.prod_const, Finset.card_univ]
  rw [hgroup] at hm
  have hc' : Pairwise fun i j =>
      IsUnit (Ideal.Quotient.mk N (c i) - Ideal.Quotient.mk N (c j)) := by
    intro i j hij
    rw [← map_sub]
    exact (hc hij).map _
  have heq := root_multiplicities_unique_of_unit_differences _ hc'
    (fun i => Fintype.card {j : σ // f j = i}) r hm
  exact fun i => congrFun heq i

theorem nilpotent_assigned_root_counts
    {σ : Type*} [Fintype σ]
    (x : σ → A) (c : ι → A) (hc : Pairwise fun i j => IsUnit (c i - c j))
    (f : σ → ι) (r : ι → ℕ)
    (hnil : ∀ j, IsNilpotent (x j - c (f j)))
    (hproduct : (∏ j : σ, (Polynomial.X - Polynomial.C (x j))) =
      ∏ i : ι, (Polynomial.X - Polynomial.C (c i)) ^ r i) :
    ∀ i, Fintype.card {j : σ // f j = i} = r i :=
  assigned_root_counts_of_unit_differences
    (assignedRootIdeal x c f) (assignedRootIdeal_isNilpotent x c f hnil)
    x c hc f r (assignedRootIdeal_residue x c f) hproduct

end HigherSpecht
end
end CanonicalSource17

section CanonicalSource18
/- Source: HigherSpecht/FiberIntegralAssignments.lean -/



/-!
# The split-fiber product over a general coefficient ring

The counting step uses invertible root differences, rather than division by
factorials or a field embedding.  Consequently the same literal CRT and
local-ideal decomposition works over the integral ordered-root localization
used in Proposition 7.2.  The coefficient ring is assumed nonzero only to
read the degree of the displayed monic factorization.
-/

noncomputable section

open Finset MvPolynomial TauCeti
open scoped Polynomial BigOperators Classical

namespace HigherSpecht

variable {R : Type*} [CommRing R]
variable {n m : ℕ} {lam : YoungDiagram} {ι : Type*} [Fintype ι]

theorem splitFiberComponentIdeal_eq_top_of_wrong_counts_units
    (hsize : lam.card + m = n) (Q : R[X]) (hQ : Q.Monic) (hdeg : Q.natDegree = m)
    (c : ι → R) (hc : Pairwise fun i j => IsUnit (c i - c j)) (r : ι → ℕ)
    (hfactor : Polynomial.X ^ lam.card * Q =
      ∏ i : ι, (Polynomial.X - Polynomial.C (c i)) ^ r i)
    (f : Fin n → ι) (N : ℕ)
    (hwrong : ¬∀ i, Fintype.card {j : Fin n // f j = i} = r i) :
    splitFiberComponentIdeal R lam m Q c f N = ⊤ := by
  by_contra htop
  let I := splitFiberComponentIdeal R lam m Q c f N
  let A := PolynomialRing n R ⧸ I
  letI : Nontrivial A := Ideal.Quotient.nontrivial_iff.mpr htop
  let phi : PolynomialRing n R →ₐ[R] A := Ideal.Quotient.mkₐ R I
  have hI : polynomialFiberIdeal R n lam m Q ≤ RingHom.ker phi.toRingHom := by
    intro p hp
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left hp)
  have hnil (j : Fin n) :
      IsNilpotent (phi (MvPolynomial.X j) - algebraMap R A (c (f j))) := by
    refine ⟨N, ?_⟩
    have hp : (MvPolynomial.X j - MvPolynomial.C (c (f j))) ^ N ∈ I :=
      Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩)
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hp
    change (Ideal.Quotient.mk I (MvPolynomial.X j) -
      Ideal.Quotient.mk I (MvPolynomial.C (c (f j)))) ^ N = 0
    simpa only [map_pow, map_sub] using hz
  have hchar := characteristic_of_polynomialFiberIdeal_le_kernel phi hsize Q hQ hdeg hI
  have hproduct : coordinateCharacteristic Finset.univ (fun j => phi (MvPolynomial.X j)) =
      ∏ i : ι, (Polynomial.X - Polynomial.C (algebraMap R A (c i))) ^ r i := by
    rw [hchar]
    have hm := congrArg (Polynomial.map (algebraMap R A)) hfactor
    simpa only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_C] using hm
  have hc' : Pairwise fun i j => IsUnit (algebraMap R A (c i) - algebraMap R A (c j)) := by
    intro i j hij
    rw [← map_sub]
    exact (hc hij).map _
  exact hwrong (nilpotent_assigned_root_counts (fun j => phi (MvPolynomial.X j))
    (fun i => algebraMap R A (c i)) hc' f r hnil hproduct)

/-- The exact product of local block quotients over every nonzero
commutative coefficient ring with invertible root differences. -/
def polynomialFiberBlockProductEquivUnits [Nontrivial R]
    (hsize : lam.card + m = n) (Q : R[X]) (hQ : Q.Monic) (hdeg : Q.natDegree = m)
    (r0 : ℕ) (c : ι → R) (hc : Pairwise fun i j => IsUnit (c i - c j))
    (z : ι) (r : ι → ℕ) (hcz : c z = 0) (hrz : r z = lam.card + r0)
    (hfactor : Polynomial.X ^ lam.card * Q =
      ∏ i : ι, (Polynomial.X - Polynomial.C (c i)) ^ r i) :
    PolynomialFiber R n lam m Q ≃ₐ[R]
      ∀ f : PrescribedRootAssignments n r,
        PolynomialRing n R ⧸ splitRootBlockIdeal R lam r0 c f.val z := by
  have hsum := root_multiplicities_sum_of_factorization hsize Q hQ hdeg c r hfactor
  have hr : ∀ i, r i ≤ n + 1 := by
    intro i
    have hi := Finset.single_le_sum (fun j hj => Nat.zero_le (r j)) (Finset.mem_univ i)
    rw [hsum] at hi
    omega
  let E := polynomialFiberAssignmentEquiv hsize Q hQ hdeg c r hc hfactor (n + 1) hr
  let F := piRestrictSubsingletonAlgEquiv (R := R)
    (fun f : Fin n → ι => ∀ i, Fintype.card {j : Fin n // f j = i} = r i)
    (fun f => PolynomialRing n R ⧸ splitFiberComponentIdeal R lam m Q c f (n + 1))
    (fun f hf => Ideal.Quotient.subsingleton_iff.mpr
      (splitFiberComponentIdeal_eq_top_of_wrong_counts_units hsize Q hQ hdeg c hc r
        hfactor f (n + 1) hf))
  exact (E.trans F).trans (AlgEquiv.piCongrRight fun f =>
    Ideal.quotientEquivAlgOfEq R
      (splitFiberComponentIdeal_eq_blockIdeal hsize Q hQ hdeg r0 c f.val z r
        hcz hc hrz f.property hfactor (n + 1) (by omega)))

end HigherSpecht
end
end CanonicalSource18

section CanonicalSource19
/- Source: HigherSpecht/FiniteTensorAlgebra.lean -/



/-!
# Finite tensor products as coproducts of commutative algebras

These maps use Mathlib's actual `PiTensorProduct`, with its commutative
ring and coefficient-algebra structures. The lift multiplies the images
of a pure tensor; the factorwise equivalence and all generator formulas
are proved from that map.
-/

noncomputable section

open scoped BigOperators TensorProduct

namespace HigherSpecht

variable {R : Type*} [CommRing R]
variable {ι : Type*} [Fintype ι]
variable {A B : ι → Type*}
variable [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
variable [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
variable {S : Type*} [CommRing S] [Algebra R S]

noncomputable def piTensorAlgLift (f : ∀ i, A i →ₐ[R] S) :
    (⨂[R] i, A i) →ₐ[R] S :=
  PiTensorProduct.liftAlgHom
    ((MultilinearMap.mkPiAlgebra R ι S).compLinearMap (fun i => (f i).toLinearMap))
    (by simp [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply])
    (by
      intro x y
      simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
        AlgHom.toLinearMap_apply, Pi.mul_apply, map_mul, Finset.prod_mul_distrib])

@[simp] theorem piTensorAlgLift_tprod (f : ∀ i, A i →ₐ[R] S) (a : ∀ i, A i) :
    piTensorAlgLift f (PiTensorProduct.tprod R a) = ∏ i, f i (a i) := by
  change PiTensorProduct.lift _ (PiTensorProduct.tprod R a) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

@[simp] theorem piTensorAlgLift_single [DecidableEq ι]
    (f : ∀ i, A i →ₐ[R] S) (i : ι) (a : A i) :
    piTensorAlgLift f (PiTensorProduct.singleAlgHom i a) = f i a := by
  change piTensorAlgLift f (PiTensorProduct.tprod R (Pi.mulSingle i a)) = _
  rw [piTensorAlgLift_tprod]
  calc
    (∏ j, f j (Pi.mulSingle i a j)) = f i (Pi.mulSingle i a i) := by
      apply Finset.prod_eq_single i
      · intro j hj hji
        simp [hji, hji.symm]
      · simp
    _ = f i a := by simp

@[simp] theorem piTensorAlgLift_comp_single [DecidableEq ι]
    (f : ∀ i, A i →ₐ[R] S) (i : ι) :
    (piTensorAlgLift f).comp (PiTensorProduct.singleAlgHom i) = f i := by
  ext a
  exact piTensorAlgLift_single f i a

noncomputable def piTensorAlgMap [DecidableEq ι]
    (f : ∀ i, A i →ₐ[R] B i) : (⨂[R] i, A i) →ₐ[R] ⨂[R] i, B i :=
  piTensorAlgLift (fun i => (PiTensorProduct.singleAlgHom i).comp (f i))

@[simp] theorem piTensorAlgMap_single [DecidableEq ι]
    (f : ∀ i, A i →ₐ[R] B i) (i : ι) (a : A i) :
    piTensorAlgMap f (PiTensorProduct.singleAlgHom i a) =
      PiTensorProduct.singleAlgHom i (f i a) :=
  piTensorAlgLift_single _ _ _

/-- A literal factorwise algebra equivalence induces an equivalence of
the actual finite tensor products, including an empty factor family. -/
noncomputable def piTensorAlgEquiv [DecidableEq ι]
    (e : ∀ i, A i ≃ₐ[R] B i) : (⨂[R] i, A i) ≃ₐ[R] ⨂[R] i, B i :=
  AlgEquiv.ofAlgHom
    (piTensorAlgMap (fun i => (e i).toAlgHom))
    (piTensorAlgMap (fun i => (e i).symm.toAlgHom))
    (by
      apply PiTensorProduct.algHom_ext
      intro i
      ext a
      simp only [AlgHom.comp_apply, piTensorAlgMap_single,
        AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply, AlgHom.id_apply])
    (by
      apply PiTensorProduct.algHom_ext
      intro i
      ext a
      simp only [AlgHom.comp_apply, piTensorAlgMap_single,
        AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply, AlgHom.id_apply])

@[simp] theorem piTensorAlgEquiv_single [DecidableEq ι]
    (e : ∀ i, A i ≃ₐ[R] B i) (i : ι) (a : A i) :
    piTensorAlgEquiv e (PiTensorProduct.singleAlgHom i a) =
      PiTensorProduct.singleAlgHom i (e i a) :=
  piTensorAlgMap_single _ _ _

end HigherSpecht
end
end CanonicalSource19

section CanonicalSource20
/- Source: HigherSpecht/DisjointVariableTensorQuotient.lean -/



/-!
# Quotients in disjoint sets of variables are tensor products

For a partition of the variables by `f : σ → ι`, the ideal is exactly the
sum of the renamed block ideals. The two inverse maps are the canonical
block inclusions and evaluation of each variable in its own tensor
factor. The target is Mathlib's genuine finite tensor product of the
specified quotient algebras.
-/

noncomputable section

open scoped TensorProduct

namespace HigherSpecht

variable {R : Type*} [CommRing R]
variable {σ ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev VariableFiber (f : σ → ι) (i : ι) := {j : σ // f j = i}

def disjointVariableIdeal (f : σ → ι)
    (I : ∀ i, Ideal (MvPolynomial (VariableFiber f i) R)) : Ideal (MvPolynomial σ R) :=
  ⨆ i, (I i).map (MvPolynomial.rename (fun j : VariableFiber f i => j.val)).toRingHom

abbrev VariableBlockQuotient (f : σ → ι)
    (I : ∀ i, Ideal (MvPolynomial (VariableFiber f i) R)) (i : ι) :=
  MvPolynomial (VariableFiber f i) R ⧸ I i

abbrev DisjointVariableQuotient (f : σ → ι)
    (I : ∀ i, Ideal (MvPolynomial (VariableFiber f i) R)) :=
  MvPolynomial σ R ⧸ disjointVariableIdeal f I

theorem renamed_block_mem_disjointVariableIdeal
    (f : σ → ι) (I : ∀ i, Ideal (MvPolynomial (VariableFiber f i) R))
    (i : ι) (p : MvPolynomial (VariableFiber f i) R) (hp : p ∈ I i) :
    MvPolynomial.rename (fun j : VariableFiber f i => j.val) p ∈
      disjointVariableIdeal f I := by
  apply le_iSup (fun i =>
    (I i).map (MvPolynomial.rename (fun j : VariableFiber f i => j.val)).toRingHom) i
  exact Ideal.mem_map_of_mem _ hp

noncomputable def blockQuotientToGlobal
    (f : σ → ι) (I : ∀ i, Ideal (MvPolynomial (VariableFiber f i) R)) (i : ι) :
    VariableBlockQuotient f I i →ₐ[R] DisjointVariableQuotient f I :=
  Ideal.Quotient.liftₐ (I i)
    ((Ideal.Quotient.mkₐ R (disjointVariableIdeal f I)).comp
      (MvPolynomial.rename (fun j : VariableFiber f i => j.val)))
    (fun p hp => Ideal.Quotient.eq_zero_iff_mem.mpr
      (renamed_block_mem_disjointVariableIdeal f I i p hp))

@[simp] theorem blockQuotientToGlobal_mk
    (f : σ → ι) (I : ∀ i, Ideal (MvPolynomial (VariableFiber f i) R))
    (i : ι) (p : MvPolynomial (VariableFiber f i) R) :
    blockQuotientToGlobal f I i (Ideal.Quotient.mk (I i) p) =
      Ideal.Quotient.mk (disjointVariableIdeal f I)
        (MvPolynomial.rename (fun j : VariableFiber f i => j.val) p) :=
  rfl

noncomputable def blockTensorToGlobal
    (f : σ → ι) (I : ∀ i, Ideal (MvPolynomial (VariableFiber f i) R)) :
    (⨂[R] i, VariableBlockQuotient f I i) →ₐ[R] DisjointVariableQuotient f I :=
  piTensorAlgLift (blockQuotientToGlobal f I)

@[simp] theorem blockTensorToGlobal_single
    (f : σ → ι) (I : ∀ i, Ideal (MvPolynomial (VariableFiber f i) R))
    (i : ι) (a : VariableBlockQuotient f I i) :
    blockTensorToGlobal f I (PiTensorProduct.singleAlgHom i a) =
      blockQuotientToGlobal f I i a :=
  piTensorAlgLift_single _ _ _

noncomputable def blockPolynomialToTensor
    (f : σ → ι) (I : ∀ i, Ideal (MvPolynomial (VariableFiber f i) R)) :
    MvPolynomial σ R →ₐ[R] ⨂[R] i, VariableBlockQuotient f I i :=
  MvPolynomial.aeval (fun j =>
    (PiTensorProduct.singleAlgHom (R := R)
      (A := VariableBlockQuotient f I) (f j))
        (Ideal.Quotient.mk (I (f j)) (MvPolynomial.X ⟨j, rfl⟩)))

@[simp] theorem blockPolynomialToTensor_X
    (f : σ → ι) (I : ∀ i, Ideal (MvPolynomial (VariableFiber f i) R)) (j : σ) :
    blockPolynomialToTensor f I (MvPolynomial.X j) =
      PiTensorProduct.singleAlgHom (f j)
        (Ideal.Quotient.mk (I (f j)) (MvPolynomial.X ⟨j, rfl⟩)) :=
  MvPolynomial.aeval_X _ _

theorem blockPolynomialToTensor_comp_rename
    (f : σ → ι) (I : ∀ i, Ideal (MvPolynomial (VariableFiber f i) R)) (i : ι) :
    (blockPolynomialToTensor f I).comp
        (MvPolynomial.rename (fun j : VariableFiber f i => j.val)) =
      (PiTensorProduct.singleAlgHom i).comp (Ideal.Quotient.mkₐ R (I i)) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨j, hj⟩
  subst i
  simp only [AlgHom.comp_apply, MvPolynomial.rename_X, blockPolynomialToTensor_X]
  rfl

theorem disjointVariableIdeal_le_blockPolynomialToTensor_ker
    (f : σ → ι) (I : ∀ i, Ideal (MvPolynomial (VariableFiber f i) R)) :
    disjointVariableIdeal f I ≤ RingHom.ker (blockPolynomialToTensor f I).toRingHom := by
  apply iSup_le
  intro i
  apply Ideal.map_le_iff_le_comap.mpr
  intro p hp
  change ((blockPolynomialToTensor f I).comp
    (MvPolynomial.rename (fun j : VariableFiber f i => j.val))) p = 0
  rw [blockPolynomialToTensor_comp_rename]
  change PiTensorProduct.singleAlgHom (R := R) (A := VariableBlockQuotient f I) i
    (Ideal.Quotient.mk (I i) p) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]

noncomputable def globalQuotientToBlockTensor
    (f : σ → ι) (I : ∀ i, Ideal (MvPolynomial (VariableFiber f i) R)) :
    DisjointVariableQuotient f I →ₐ[R] ⨂[R] i, VariableBlockQuotient f I i :=
  Ideal.Quotient.liftₐ (disjointVariableIdeal f I) (blockPolynomialToTensor f I)
    (fun p hp => disjointVariableIdeal_le_blockPolynomialToTensor_ker f I hp)

@[simp] theorem globalQuotientToBlockTensor_mk
    (f : σ → ι) (I : ∀ i, Ideal (MvPolynomial (VariableFiber f i) R))
    (p : MvPolynomial σ R) :
    globalQuotientToBlockTensor f I (Ideal.Quotient.mk (disjointVariableIdeal f I) p) =
      blockPolynomialToTensor f I p :=
  rfl

theorem blockTensorToGlobal_comp_globalQuotientToBlockTensor
    (f : σ → ι) (I : ∀ i, Ideal (MvPolynomial (VariableFiber f i) R)) :
    (blockTensorToGlobal f I).comp (globalQuotientToBlockTensor f I) =
      AlgHom.id R (DisjointVariableQuotient f I) := by
  apply Ideal.Quotient.algHom_ext R
  apply MvPolynomial.algHom_ext
  intro j
  change blockTensorToGlobal f I
      (globalQuotientToBlockTensor f I
        (Ideal.Quotient.mk (disjointVariableIdeal f I) (MvPolynomial.X j))) =
    Ideal.Quotient.mk (disjointVariableIdeal f I) (MvPolynomial.X j)
  rw [globalQuotientToBlockTensor_mk, blockPolynomialToTensor_X,
    blockTensorToGlobal_single, blockQuotientToGlobal_mk, MvPolynomial.rename_X]

theorem globalQuotientToBlockTensor_comp_blockTensorToGlobal
    (f : σ → ι) (I : ∀ i, Ideal (MvPolynomial (VariableFiber f i) R)) :
    (globalQuotientToBlockTensor f I).comp (blockTensorToGlobal f I) =
      AlgHom.id R (⨂[R] i, VariableBlockQuotient f I i) := by
  apply PiTensorProduct.algHom_ext
  intro i
  apply Ideal.Quotient.algHom_ext R
  apply MvPolynomial.algHom_ext
  rintro ⟨j, hj⟩
  subst i
  change globalQuotientToBlockTensor f I
      (blockTensorToGlobal f I
        (PiTensorProduct.singleAlgHom (f j)
          (Ideal.Quotient.mk (I (f j)) (MvPolynomial.X ⟨j, rfl⟩)))) =
    PiTensorProduct.singleAlgHom (f j)
      (Ideal.Quotient.mk (I (f j)) (MvPolynomial.X ⟨j, rfl⟩))
  rw [blockTensorToGlobal_single, blockQuotientToGlobal_mk, MvPolynomial.rename_X,
    globalQuotientToBlockTensor_mk, blockPolynomialToTensor_X]

/-- The exact disjoint-variable quotient is equivalent, as a coefficient
algebra, to the finite tensor product of its literal block quotients. -/
noncomputable def disjointVariableQuotientTensorEquiv
    (f : σ → ι) (I : ∀ i, Ideal (MvPolynomial (VariableFiber f i) R)) :
    DisjointVariableQuotient f I ≃ₐ[R] ⨂[R] i, VariableBlockQuotient f I i :=
  AlgEquiv.ofAlgHom (globalQuotientToBlockTensor f I) (blockTensorToGlobal f I)
    (globalQuotientToBlockTensor_comp_blockTensorToGlobal f I)
    (blockTensorToGlobal_comp_globalQuotientToBlockTensor f I)

@[simp] theorem disjointVariableQuotientTensorEquiv_mk_X
    (f : σ → ι) (I : ∀ i, Ideal (MvPolynomial (VariableFiber f i) R)) (j : σ) :
    disjointVariableQuotientTensorEquiv f I
        (Ideal.Quotient.mk (disjointVariableIdeal f I) (MvPolynomial.X j)) =
      PiTensorProduct.singleAlgHom (f j)
        (Ideal.Quotient.mk (I (f j)) (MvPolynomial.X ⟨j, rfl⟩)) :=
  blockPolynomialToTensor_X f I j

end HigherSpecht
end
end CanonicalSource20

section CanonicalSource21
/- Source: HigherSpecht/RootAssignmentCardinality.lean -/



/-!
# The exact number of prescribed root assignments

The coefficient of a multivariable monomial in `(sum X)^n` counts the
functions with its prescribed fiber sizes. Mathlib's multinomial
coefficient theorem identifies the same coefficient with the factorial
quotient. This is a count of the actual assignment subtype, independent
of the unresolved higher-Specht eligible-index count.
-/

noncomputable section

open scoped BigOperators Classical

namespace HigherSpecht

variable {ι : Type*} [Fintype ι] {n : ℕ}

def assignmentExponent (f : Fin n → ι) : ι →₀ ℕ :=
  ∑ j, Finsupp.single (f j) 1

theorem assignmentExponent_apply (f : Fin n → ι) (i : ι) :
    assignmentExponent f i = Fintype.card {j : Fin n // f j = i} := by
  classical
  simpa only [assignmentExponent, Finset.sum_apply', Finsupp.single_apply,
    Finset.sum_boole, Nat.cast_id] using
    (Fintype.card_subtype (fun j : Fin n => f j = i)).symm

theorem assignmentExponent_eq_iff (f : Fin n → ι) (r : ι → ℕ) :
    assignmentExponent f = Finsupp.equivFunOnFinite.symm r ↔
      ∀ i, Fintype.card {j : Fin n // f j = i} = r i := by
  constructor
  · intro h i
    have hi := congrArg (fun d : ι →₀ ℕ => d i) h
    simpa only [assignmentExponent_apply, Finsupp.coe_equivFunOnFinite_symm] using hi
  · intro h
    ext i
    simpa only [assignmentExponent_apply, Finsupp.coe_equivFunOnFinite_symm] using h i

theorem assignment_product_X (f : Fin n → ι) :
    (∏ j, (MvPolynomial.X (f j) : MvPolynomial ι ℕ)) =
      MvPolynomial.monomial (assignmentExponent f) 1 := by
  simpa only [assignmentExponent, MvPolynomial.X] using
    (MvPolynomial.monomial_sum_one (R := ℕ) Finset.univ
      (fun j : Fin n => Finsupp.single (f j) 1)).symm

/-- Every fiber size, including zero, is retained in the actual function
subtype. The empty source and empty target cases are included. -/
theorem card_functions_with_fiber_sizes (r : ι → ℕ)
    (hsum : (∑ i, r i) = n) :
    Fintype.card {f : Fin n → ι //
      ∀ i, Fintype.card {j : Fin n // f j = i} = r i} =
        n.factorial / ∏ i, (r i).factorial := by
  classical
  let d : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm r
  have hcount : ((∑ i : ι, (MvPolynomial.X i : MvPolynomial ι ℕ)) ^ n).coeff d =
      Fintype.card {f : Fin n → ι //
        ∀ i, Fintype.card {j : Fin n // f j = i} = r i} := by
    rw [Fintype.sum_pow, MvPolynomial.coeff_sum]
    simp only [assignment_product_X, MvPolynomial.coeff_monomial,
      d, assignmentExponent_eq_iff]
    simpa only [Finset.sum_boole, Nat.cast_id] using
      (Fintype.card_subtype (fun f : Fin n → ι =>
        ∀ i, Fintype.card {j : Fin n // f j = i} = r i)).symm
  have hd : d.sum (fun _ m => m) = n :=
    (Finsupp.equivFunOnFinite_symm_sum r).trans hsum
  rw [MvPolynomial.coeff_sum_X_pow_of_fintype, if_pos hd] at hcount
  calc
    Fintype.card {f : Fin n → ι //
        ∀ i, Fintype.card {j : Fin n // f j = i} = r i} = d.multinomial :=
      hcount.symm
    _ = Nat.multinomial Finset.univ d :=
      Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ d.support)
    _ = n.factorial / ∏ i, (r i).factorial := by
      change (∑ i, r i).factorial / (∏ i, (r i).factorial) = _
      rw [hsum]

/-- The zero group and all distinct nonzero-root groups give exactly the
factor count displayed in Theorem 7.1. -/
theorem card_zero_and_nonzero_root_assignments (k0 : ℕ) (r : ι → ℕ)
    (hsize : k0 + ∑ i, r i = n) :
    Fintype.card {f : Fin n → Option ι //
      ∀ i, Fintype.card {j : Fin n // f j = i} = i.elim k0 r} =
        n.factorial / (k0.factorial * ∏ i, (r i).factorial) := by
  have hsum : (∑ i : Option ι, i.elim k0 r) = n := by
    simpa only [Fintype.sum_option, Option.elim_none, Option.elim_some] using hsize
  simpa only [Fintype.prod_option, Option.elim_none, Option.elim_some,
    Fintype.card_eq_nat_card] using
    card_functions_with_fiber_sizes (fun i : Option ι => i.elim k0 r) hsum

end HigherSpecht
end
end CanonicalSource21

section CanonicalSource22
/- Source: HigherSpecht/FiberTensorDecomposition.lean -/



/-!
# The actual Springer tensor factors of every split fiber

The local translation and explicit block enumerations instantiate the
finite disjoint-variable tensor equivalence.  Composing with the actual
Chinese-remainder decomposition gives the full tensor-factor description,
without a dimension or higher-Specht basis premise.  The final specialization
uses exactly the zero root and the distinct nonzero roots in Theorem 7.1.
-/

noncomputable section

open Finset MvPolynomial TauCeti
open scoped Polynomial BigOperators Classical TensorProduct

namespace HigherSpecht

variable {R : Type*} [CommRing R] {n m : ℕ} {ι : Type*} [Fintype ι]

/-- Every actual root block quotient is the stated finite tensor product of
the original Springer rings.  All changes of variables are explicit. -/
def rootBlockTensorQuotientEquiv
    (lam : YoungDiagram) (r0 : ℕ) (r : ι → ℕ)
    (c : ι → R) (f : Fin n → ι) (z : ι) (hcz : c z = 0)
    (hrz : r z = lam.card + r0)
    (hcount : ∀ i, Fintype.card (RootFiberVariables f i) = r i) :
    (PolynomialRing n R ⧸ splitRootBlockIdeal R lam r0 c f z) ≃ₐ[R]
      ⨂[R] i : ι, SpringerRing R (rootBlockShape lam r0 r z i) := by
  let I := rootFiberSpringerIdeal R lam r0 r f z hrz hcount
  have hI : disjointVariableIdeal f I = unshiftedRootBlockIdeal R lam r0 r f z :=
    rootFiberSpringerIdeal_iSup lam r0 r f z hrz hcount
  exact (rootBlockTranslationQuotientEquiv lam r0 r c f z hcz hrz hcount).trans
    ((Ideal.quotientEquivAlgOfEq R hI.symm).trans
      ((disjointVariableQuotientTensorEquiv f I).trans
        (piTensorAlgEquiv fun i => rootFiberSpringerQuotientEquiv lam r0 r f z hrz hcount i)))

/-- The complete actual tensor product decomposition for a displayed split
monic parameter polynomial over a general coefficient ring. -/
def polynomialFiberSpringerTensorProductEquiv [Nontrivial R]
    {lam : YoungDiagram} (hsize : lam.card + m = n)
    (Q : R[X]) (hQ : Q.Monic) (hdeg : Q.natDegree = m)
    (r0 : ℕ) (c : ι → R) (hc : Pairwise fun i j => IsUnit (c i - c j))
    (z : ι) (r : ι → ℕ) (hcz : c z = 0) (hrz : r z = lam.card + r0)
    (hfactor : Polynomial.X ^ lam.card * Q =
      ∏ i : ι, (Polynomial.X - Polynomial.C (c i)) ^ r i) :
    PolynomialFiber R n lam m Q ≃ₐ[R]
      ∀ _f : PrescribedRootAssignments n r,
        ⨂[R] i : ι, SpringerRing R (rootBlockShape lam r0 r z i) :=
  (polynomialFiberBlockProductEquivUnits hsize Q hQ hdeg r0 c hc z r hcz hrz hfactor).trans
    (AlgEquiv.piCongrRight fun f =>
      rootBlockTensorQuotientEquiv lam r0 r c f.val z hcz hrz f.property)

def splitRootValue (c : ι → R) : Option ι → R := fun i => i.elim 0 c

def splitRootMultiplicities (lam : YoungDiagram) (r0 : ℕ) (r : ι → ℕ) : Option ι → ℕ :=
  fun i => i.elim (lam.card + r0) r

def splitRootParameter (r0 : ℕ) (c : ι → R) (r : ι → ℕ) : R[X] :=
  Polynomial.X ^ r0 * ∏ i : ι, (Polynomial.X - Polynomial.C (c i)) ^ r i

theorem splitRootParameter_monic (r0 : ℕ) (c : ι → R) (r : ι → ℕ) :
    (splitRootParameter r0 c r).Monic :=
  (Polynomial.monic_X_pow r0).mul (Polynomial.monic_prod_of_monic _ _
    (fun i _ => (Polynomial.monic_X_sub_C (c i)).pow (r i)))

theorem splitRootParameter_natDegree [Nontrivial R]
    (r0 : ℕ) (c : ι → R) (r : ι → ℕ) :
    (splitRootParameter r0 c r).natDegree = r0 + ∑ i, r i := by
  rw [splitRootParameter, (Polynomial.monic_X_pow r0).natDegree_mul
    (Polynomial.monic_prod_of_monic _ _
      (fun i _ => (Polynomial.monic_X_sub_C (c i)).pow (r i))),
    Polynomial.natDegree_X_pow,
    Polynomial.natDegree_prod_of_monic (R := R) (Finset.univ : Finset ι)
      (f := fun i => (Polynomial.X - Polynomial.C (c i)) ^ r i)
      (fun i _ => (Polynomial.monic_X_sub_C (c i)).pow (r i))]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Polynomial.monic_X_sub_C (c i)).natDegree_pow,
    Polynomial.natDegree_X_sub_C, mul_one]

theorem splitRootParameter_factorization
    (lam : YoungDiagram) (r0 : ℕ) (c : ι → R) (r : ι → ℕ) :
    Polynomial.X ^ lam.card * splitRootParameter r0 c r =
      ∏ i : Option ι,
        (Polynomial.X - Polynomial.C (splitRootValue c i)) ^
          splitRootMultiplicities lam r0 r i := by
  rw [Fintype.prod_option]
  simp only [splitRootValue, splitRootMultiplicities, Option.elim_none,
    Option.elim_some, map_zero, sub_zero, splitRootParameter, pow_add]
  ring

theorem splitRootValue_unitDifferences
    (c : ι → R) (hu : ∀ i, IsUnit (c i))
    (hc : Pairwise fun i j => IsUnit (c i - c j)) :
    Pairwise fun i j : Option ι => IsUnit (splitRootValue c i - splitRootValue c j) := by
  intro i j hij
  cases i with
  | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => simpa only [splitRootValue, Option.elim_none, Option.elim_some,
          zero_sub] using (hu j).neg
  | some i =>
      cases j with
      | none => simpa only [splitRootValue, Option.elim_none, Option.elim_some,
          sub_zero] using hu i
      | some j =>
          exact hc (fun h => hij (congrArg Option.some h))

/-- The partition at the zero root is `lam ∪ 1^r0`; the other partitions
are the actual single columns of their displayed multiplicities. -/
theorem rootBlockShape_splitRootMultiplicities
    (lam : YoungDiagram) (r0 : ℕ) (r : ι → ℕ) (i : Option ι) :
    rootBlockShape lam r0 (splitRootMultiplicities lam r0 r) none i =
      i.elim (adjoinOnes lam r0) (fun j => columnPartition (r j)) := by
  cases i <;> simp only [rootBlockShape, splitRootMultiplicities, if_pos rfl, if_true,
    Option.some_ne_none, if_false, Option.elim_none, Option.elim_some]

/-- Equality of the entire partition family transports its Springer tensor
algebra with the original coefficient action. -/
def springerTensorShapeEquiv (R : Type*) [CommRing R]
    {κ : Type*} [Fintype κ] (u v : κ → YoungDiagram) (h : u = v) :
    (⨂[R] i : κ, SpringerRing R (u i)) ≃ₐ[R]
      ⨂[R] i : κ, SpringerRing R (v i) := by
  subst v
  exact AlgEquiv.refl

/-- Theorem 7.1's exact split-fiber algebra equivalence.  The use of a finite
indexed tensor product is the literal tensor of the zero-root Springer
factor and all nonzero-root column factors.  Repeated roots and arbitrary
field characteristic are included. -/
def theorem_7_1_split_fiber
    (K : Type*) [Field K] (lam : YoungDiagram) (r0 : ℕ)
    (c : ι → K) (hc : Function.Injective c) (hcz : ∀ i, c i ≠ 0)
    (r : ι → ℕ) (hr : ∀ i, 0 < r i)
    (hsize : lam.card + (r0 + ∑ i, r i) = n) :
    PolynomialFiber K n lam (r0 + ∑ i, r i) (splitRootParameter r0 c r) ≃ₐ[K]
      ∀ _f : PrescribedRootAssignments n (splitRootMultiplicities lam r0 r),
        ⨂[K] i : Option ι,
          SpringerRing K (i.elim (adjoinOnes lam r0) (fun j => columnPartition (r j))) := by
  let E := polynomialFiberSpringerTensorProductEquiv hsize
    (splitRootParameter r0 c r) (splitRootParameter_monic r0 c r)
    (splitRootParameter_natDegree r0 c r) r0 (splitRootValue c)
    (splitRootValue_unitDifferences c (fun i => isUnit_iff_ne_zero.mpr (hcz i))
      (fun i j hij => isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (hc.ne hij))))
    none (splitRootMultiplicities lam r0 r) rfl rfl
    (splitRootParameter_factorization lam r0 c r)
  exact E.trans (AlgEquiv.piCongrRight fun _ =>
    springerTensorShapeEquiv K _ _
      (funext (rootBlockShape_splitRootMultiplicities lam r0 r)))


/-- The same theorem for the paper's literal elementary parameter tuple.
The factorization hypothesis is on its signed monic parameter polynomial,
whose coefficient correspondence is proved in `FiberParameters`. -/
def theorem_7_1_parameter_fiber
    (K : Type*) [Field K] (lam : YoungDiagram) (a : Fin m → K)
    (hsize : lam.card + m = n) (r0 : ℕ)
    (c : ι → K) (hc : Function.Injective c) (hcz : ∀ i, c i ≠ 0)
    (r : ι → ℕ) (hr : ∀ i, 0 < r i)
    (hfactor : parameterPolynomial a = splitRootParameter r0 c r) :
    ParameterFiber K n lam m a ≃ₐ[K]
      ∀ _f : PrescribedRootAssignments n (splitRootMultiplicities lam r0 r),
        ⨂[K] i : Option ι,
          SpringerRing K (i.elim (adjoinOnes lam r0) (fun j => columnPartition (r j))) := by
  let D : ParameterFiber K n lam m a ≃ₐ[K]
      PolynomialFiber K n lam m (parameterPolynomial a) :=
    Ideal.quotientEquivAlgOfEq K (polynomialFiberIdeal_parameterPolynomial lam a).symm
  let E := polynomialFiberSpringerTensorProductEquiv hsize
    (parameterPolynomial a) (parameterPolynomial_monic a) (parameterPolynomial_natDegree a)
    r0 (splitRootValue c)
    (splitRootValue_unitDifferences c (fun i => isUnit_iff_ne_zero.mpr (hcz i))
      (fun i j hij => isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (hc.ne hij))))
    none (splitRootMultiplicities lam r0 r) rfl rfl
    (by rw [hfactor]; exact splitRootParameter_factorization lam r0 c r)
  exact D.trans (E.trans (AlgEquiv.piCongrRight fun _ =>
    springerTensorShapeEquiv K _ _
      (funext (rootBlockShape_splitRootMultiplicities lam r0 r))))


/-- The exact number of factors in the displayed split-fiber product. -/
theorem card_prescribedRootAssignments (r : ι → ℕ) (hsum : (∑ i, r i) = n) :
    Fintype.card (PrescribedRootAssignments n r) =
      n.factorial / ∏ i, (r i).factorial :=
  card_functions_with_fiber_sizes r hsum

/-- The multinomial factor count stated alongside Theorem 7.1. -/
theorem theorem_7_1_number_of_factors (lam : YoungDiagram) (r0 : ℕ) (r : ι → ℕ)
    (hsize : lam.card + (r0 + ∑ i, r i) = n) :
    Fintype.card (PrescribedRootAssignments n (splitRootMultiplicities lam r0 r)) =
      n.factorial / ((lam.card + r0).factorial * ∏ i, (r i).factorial) := by
  simpa only [PrescribedRootAssignments, splitRootMultiplicities,
    Fintype.card_eq_nat_card] using
    card_zero_and_nonzero_root_assignments (n := n) (lam.card + r0) r
      (by omega)

end HigherSpecht
end
end CanonicalSource22

section CanonicalSource23
/- Source: HigherSpecht/FiberCoefficientBaseChange.lean -/



/-!
# Scalar extension of the literal elementary-parameter fiber

Coefficient extension takes every original elementary generator to the
same generator over the new ring and takes every parameter to its actual
image.  The tensor quotient equivalence therefore identifies the scalar
extension of the fiber with the displayed fiber over the extension ring.
This supplies the nonsplit-field interpretation of Theorem 7.1 without
assuming flatness or a higher-Specht basis.
-/

noncomputable section

open MvPolynomial TauCeti
open scoped Polynomial TensorProduct BigOperators Classical

namespace HigherSpecht

variable {R S : Type*} [CommRing R] [CommRing S]

theorem map_parameterFiberIdeal (phi : R →+* S) (n : ℕ) (lam : YoungDiagram)
    (m : ℕ) (a : Fin m → R) :
    (parameterFiberIdeal R n lam m a).map (MvPolynomial.map phi) =
      parameterFiberIdeal S n lam m (fun i => phi (a i)) := by
  unfold parameterFiberIdeal
  rw [Ideal.map_sup, map_untruncatedIdeal, Ideal.map_span, ← Set.range_comp]
  congr 2
  apply congrArg Set.range
  funext i
  simp only [Function.comp_def, map_sub, map_elementaryOn, MvPolynomial.map_C]

def parameterFiberBaseChangeEquiv [Algebra R S]
    (n : ℕ) (lam : YoungDiagram) (m : ℕ) (a : Fin m → R) :
    S ⊗[R] ParameterFiber R n lam m a ≃ₐ[S]
      ParameterFiber S n lam m (fun i => algebraMap R S (a i)) :=
  polynomialQuotientBaseChangeEquiv _ _
    (map_parameterFiberIdeal (algebraMap R S) n lam m a)

@[simp] theorem parameterFiberBaseChangeEquiv_tmul [Algebra R S]
    (n : ℕ) (lam : YoungDiagram) (m : ℕ) (a : Fin m → R)
    (s : S) (p : PolynomialRing n R) :
    parameterFiberBaseChangeEquiv n lam m a
        (s ⊗ₜ[R] Ideal.Quotient.mk (parameterFiberIdeal R n lam m a) p) =
      Ideal.Quotient.mk (parameterFiberIdeal S n lam m
        (fun i => algebraMap R S (a i))) (s • MvPolynomial.map (algebraMap R S) p) :=
  polynomialQuotientBaseChangeEquiv_tmul _ _ _ _ _

/-- Theorem 7.1 after the actual extension of the coefficient field.  A
splitting field is a particular instance, with its displayed factorization. -/
def theorem_7_1_after_scalar_extension
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    {n m : ℕ} {ι : Type*} [Fintype ι]
    (lam : YoungDiagram) (a : Fin m → K) (hsize : lam.card + m = n)
    (r0 : ℕ) (c : ι → L) (hc : Function.Injective c) (hcz : ∀ i, c i ≠ 0)
    (r : ι → ℕ) (hr : ∀ i, 0 < r i)
    (hfactor : parameterPolynomial (fun i => algebraMap K L (a i)) =
      splitRootParameter r0 c r) :
    L ⊗[K] ParameterFiber K n lam m a ≃ₐ[L]
      ∀ _f : PrescribedRootAssignments n (splitRootMultiplicities lam r0 r),
        ⨂[L] i : Option ι,
          SpringerRing L (i.elim (adjoinOnes lam r0) (fun j => columnPartition (r j))) :=
  (parameterFiberBaseChangeEquiv n lam m a).trans
    (theorem_7_1_parameter_fiber L lam (fun i => algebraMap K L (a i))
      hsize r0 c hc hcz r hr hfactor)

end HigherSpecht
end
end CanonicalSource23

section CanonicalSource24
/- Source: HigherSpecht/MonicRootFactorization.lean -/



/-!
# Canonical factorization of a monic polynomial

Over an algebraically closed field, the distinct nonzero roots and their
multiplicities are taken from the actual root multiset. The zero-root
multiplicity is its actual count. The factorization and total multiplicity
are proved, so later fiber statements need no supplied root data.

This generic algebraic argument is independent of reducedness and etaleness.
-/

noncomputable section

open TauCeti Polynomial Finset
open scoped Classical BigOperators

namespace HigherSpecht

variable {L : Type*} [Field L]

 def nonzeroRootSet (Q : L[X]) : Finset L := Q.roots.toFinset.erase 0

 def canonicalNonzeroRoot (Q : L[X]) : nonzeroRootSet Q → L := Subtype.val

 def canonicalRootMultiplicity (Q : L[X]) : nonzeroRootSet Q → ℕ :=
  fun i => Q.roots.count i.val

 theorem canonicalNonzeroRoot_injective (Q : L[X]) :
    Function.Injective (canonicalNonzeroRoot Q) := Subtype.val_injective

 theorem canonicalNonzeroRoot_ne_zero (Q : L[X]) (i : nonzeroRootSet Q) :
    canonicalNonzeroRoot Q i ≠ 0 := (Finset.mem_erase.mp i.property).1

 theorem canonicalRootMultiplicity_pos (Q : L[X]) (i : nonzeroRootSet Q) :
    0 < canonicalRootMultiplicity Q i :=
  Multiset.count_pos.mpr (Multiset.mem_toFinset.mp (Finset.mem_erase.mp i.property).2)

 theorem canonical_splitRootParameter [IsAlgClosed L] (Q : L[X]) (hQ : Q.Monic) :
    Q = splitRootParameter (Q.roots.count 0)
      (canonicalNonzeroRoot Q) (canonicalRootMultiplicity Q) := by
  have hprod := (IsAlgClosed.splits Q).eq_prod_roots_of_monic hQ
  rw [Finset.prod_multiset_map_count] at hprod
  conv_lhs => rw [hprod]
  rw [splitRootParameter]
  have hnonzero :
      (∏ i : nonzeroRootSet Q,
        (Polynomial.X - Polynomial.C (canonicalNonzeroRoot Q i)) ^
          canonicalRootMultiplicity Q i) =
        ∏ x ∈ Q.roots.toFinset.erase 0,
          (Polynomial.X - Polynomial.C x) ^ Q.roots.count x :=
    Finset.prod_coe_sort (nonzeroRootSet Q)
      (fun x => (Polynomial.X - Polynomial.C x) ^ Q.roots.count x)
  rw [hnonzero]
  by_cases hz : (0 : L) ∈ Q.roots.toFinset
  · have h := (Finset.mul_prod_erase Q.roots.toFinset
      (fun x => (Polynomial.X - Polynomial.C x) ^ Q.roots.count x) hz).symm
    rw [Polynomial.C_0, sub_zero] at h
    exact h
  · have hc : Q.roots.count 0 = 0 :=
      Multiset.count_eq_zero.mpr (fun h => hz (Multiset.mem_toFinset.mpr h))
    rw [hc, pow_zero, one_mul, Finset.erase_eq_of_notMem hz]

theorem canonical_root_multiplicities_sum [IsAlgClosed L]
    (Q : L[X]) (hQ : Q.Monic) :
    Q.roots.count 0 + ∑ i : nonzeroRootSet Q, canonicalRootMultiplicity Q i = Q.natDegree := by
  have h := congrArg Polynomial.natDegree (canonical_splitRootParameter Q hQ)
  rw [splitRootParameter_natDegree] at h
  exact h.symm

end HigherSpecht
end
end CanonicalSource24

section CanonicalSource25
/- Source: HigherSpecht/FiberAlgebraicClosure.lean -/



/-!
# Every parameter fiber after algebraic closure

The root set, root values, and multiplicities are the canonical data of the
actual signed parameter polynomial. Its factorization and all required
hypotheses are proved in `MonicRootFactorization`. Thus this version of
Theorem 7.1 has no factorization, separability, root-choice, or characteristic
premise. Repeated roots and the constant polynomial are included.
-/

noncomputable section

open TauCeti Polynomial Finset
open scoped Classical BigOperators TensorProduct

namespace HigherSpecht

/-- Theorem 7.1 for every parameter tuple over every field, after the
actual algebraic-closure scalar extension and with canonical root data. -/
def theorem_7_1_algebraicClosure
    (K : Type*) [Field K] {n m : ℕ}
    (lam : YoungDiagram) (a : Fin m → K) (hsize : lam.card + m = n) :
    let L := AlgebraicClosure K
    let Q := parameterPolynomial (fun i => algebraMap K L (a i))
    L ⊗[K] ParameterFiber K n lam m a ≃ₐ[L]
      ∀ _f : PrescribedRootAssignments n
          (splitRootMultiplicities lam (Q.roots.count 0) (canonicalRootMultiplicity Q)),
        ⨂[L] i : Option (nonzeroRootSet Q),
          SpringerRing L (i.elim (adjoinOnes lam (Q.roots.count 0))
            (fun j => columnPartition (canonicalRootMultiplicity Q j))) := by
  let Q := parameterPolynomial (fun i => algebraMap K (AlgebraicClosure K) (a i))
  exact theorem_7_1_after_scalar_extension K (AlgebraicClosure K) lam a hsize
    (Q.roots.count 0) (canonicalNonzeroRoot Q) (canonicalNonzeroRoot_injective Q)
    (canonicalNonzeroRoot_ne_zero Q) (canonicalRootMultiplicity Q)
    (canonicalRootMultiplicity_pos Q)
    (canonical_splitRootParameter Q (parameterPolynomial_monic _))

/-- The number of factors of the automatic algebraic-closure formula,
without a separately assumed multiplicity sum or chosen factorization. -/
theorem theorem_7_1_algebraicClosure_number_of_factors
    (K : Type*) [Field K] {n m : ℕ}
    (lam : YoungDiagram) (a : Fin m → K) (hsize : lam.card + m = n) :
    let Q := parameterPolynomial (fun i => algebraMap K (AlgebraicClosure K) (a i))
    Fintype.card (PrescribedRootAssignments n
        (splitRootMultiplicities lam (Q.roots.count 0) (canonicalRootMultiplicity Q))) =
      n.factorial / ((lam.card + Q.roots.count 0).factorial *
        ∏ i : nonzeroRootSet Q, (canonicalRootMultiplicity Q i).factorial) := by
  let Q := parameterPolynomial (fun i => algebraMap K (AlgebraicClosure K) (a i))
  have hsum : Q.roots.count 0 +
      ∑ i : nonzeroRootSet Q, canonicalRootMultiplicity Q i = m := by
    rw [canonical_root_multiplicities_sum Q (parameterPolynomial_monic _)]
    exact parameterPolynomial_natDegree _
  exact theorem_7_1_number_of_factors lam (Q.roots.count 0) (canonicalRootMultiplicity Q)
    (by rw [hsum]; exact hsize)

end HigherSpecht
end
end CanonicalSource25
