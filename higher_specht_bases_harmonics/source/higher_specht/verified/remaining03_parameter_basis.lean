module

public import higher_specht.verified.remaining03_coefficients
public import tau_ceti.ring_theory.depth.flat
public import tau_ceti.ring_theory.regular_local_ring.cohen_macaulay
public import tau_ceti.ring_theory.krull_dimension.fiber
public import tau_ceti.ring_theory.krull_dimension.integral
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import tau_ceti.representation_theory.symmetric.frobenius_characteristic
public import Mathlib.RingTheory.PowerSeries.WellKnown

/- Generated ordinary source-preserving proof stage. See audit/staged_specht_remaining/Remaining03ParameterBasis/manifest.json. -/

@[expose] public section

section CanonicalSource44
/- Source: HigherSpecht/SpringerDimension.lean -/



/-!
# The exact Springer dimension from the integral staircase basis

When the diagram occupies every variable, its shuffle filling is a bijection,
so the untruncated staircase exponents already satisfy every sufficiently
large finite bound.  The genuine staircase/content-word recurrence then
counts them.  At full size, the lower content bounds are equalities, and
the actual multinomial function count gives the factorial quotient.

This dimension calculation is independent of a higher-Specht index count and
works over every coefficient field, including positive characteristic.
-/

noncomputable section

open TauCeti Module Finset
open scoped Classical BigOperators

namespace HigherSpecht

def rowFactorialProduct (lam : YoungDiagram) : ℕ :=
  ∏ j ∈ Finset.range (lam.colLen 0), (lam.rowLen j).factorial

theorem count_ofFn_eq_fiberCard {α : Type*} [DecidableEq α] {n : ℕ}
    (f : Fin n → α) (a : α) :
    (List.ofFn f).count a = Fintype.card {j : Fin n // f j = a} := by
  have hsum : (List.ofFn f).count a =
      ∑ j : Fin n, if f j = a then 1 else 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [List.ofFn_succ, List.count_cons, Fin.sum_univ_succ, ih]
        by_cases h : f 0 = a <;> simp [h, Nat.add_comm]
  rw [hsum]
  simpa only [Finset.sum_boole, Nat.cast_id] using
    (Fintype.card_subtype (fun j : Fin n => f j = a)).symm

theorem fullSizeContentWord_count {n s : ℕ} {lam : YoungDiagram}
    (hcard : lam.card = n) (hheight : lam.colLen 0 ≤ s)
    (u : ContentWord n lam s) (i : Fin s) :
    (List.ofFn u.val).count i = lam.rowLen i.val := by
  have hrow : (∑ j : Fin s, lam.rowLen j.val) = n := by
    rw [Fin.sum_univ_eq_sum_range]
    exact (YoungDiagram.card_eq_sum_range_rowLen lam hheight).symm.trans hcard
  have hcount : (∑ j : Fin s, (List.ofFn u.val).count j) = n := by
    have h := Multiset.sum_count_eq_card
      (s := Finset.univ) (m := (List.ofFn u.val : Multiset (Fin s)))
      (fun _ _ => Finset.mem_univ _)
    simpa only [Multiset.coe_count, Multiset.coe_card, List.length_ofFn] using h
  have hsum : (∑ j : Fin s, ((List.ofFn u.val).count j - lam.rowLen j.val)) = 0 := by
    have hadd : (∑ j : Fin s, ((List.ofFn u.val).count j - lam.rowLen j.val)) + n = n := by
      conv_lhs => arg 2; rw [← hrow]
      rw [← Finset.sum_add_distrib]
      exact (Finset.sum_congr rfl (fun j _ => Nat.sub_add_cancel (u.property j))).trans hcount
    omega
  have hi := Finset.single_le_sum
    (f := fun j : Fin s => (List.ofFn u.val).count j - lam.rowLen j.val)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [hsum] at hi
  have hlo := u.property i
  omega

def fullSizeContentWordEquiv {n : ℕ} (lam : YoungDiagram)
    (hcard : lam.card = n) (s : ℕ) (hheight : lam.colLen 0 ≤ s) :
    ContentWord n lam s ≃
      {f : Fin n → Fin s // ∀ i, Fintype.card {j : Fin n // f j = i} = lam.rowLen i.val} where
  toFun u := ⟨u.val, fun i => by
    rw [← count_ofFn_eq_fiberCard]
    exact fullSizeContentWord_count hcard hheight u i⟩
  invFun f := ⟨f.val, fun i => by
    rw [count_ofFn_eq_fiberCard, f.property i]⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_fullSizeContentWord {n : ℕ} (lam : YoungDiagram)
    (hcard : lam.card = n) (s : ℕ) (hheight : lam.colLen 0 ≤ s) :
    Nat.card (ContentWord n lam s) =
      n.factorial / ∏ i : Fin s, (lam.rowLen i.val).factorial := by
  rw [Nat.card_congr (fullSizeContentWordEquiv lam hcard s hheight),
    Nat.card_eq_fintype_card]
  have hsum : (∑ i : Fin s, lam.rowLen i.val) = n := by
    rw [Fin.sum_univ_eq_sum_range]
    exact (YoungDiagram.card_eq_sum_range_rowLen lam hheight).symm.trans hcard
  simpa only [← Nat.card_eq_fintype_card] using
    card_functions_with_fiber_sizes (fun i : Fin s => lam.rowLen i.val) hsum

theorem shuffleBound_fullSize_lt {n : ℕ} {lam : YoungDiagram}
    (hcard : lam.card = n) {a : Fin n →₀ ℕ} (ha : ShuffleBound n lam a) (i : Fin n) :
    a i < lam.colLen 0 := by
  obtain ⟨U, hU, hb⟩ := ha
  have hbij : Function.Bijective U :=
    (Fintype.bijective_iff_injective_and_card U).mpr ⟨U.injective, by
      simpa only [Fintype.card_coe, Fintype.card_fin, YoungDiagram.card] using hcard⟩
  obtain ⟨c, rfl⟩ := hbij.surjective i
  exact (hb c).trans_lt (YoungDiagram.lt_colLen_zero_of_mem c.property)

def fullSizeStaircaseEquiv {n : ℕ} (lam : YoungDiagram) (hcard : lam.card = n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    UntruncatedStaircaseExponents n lam ≃ GriffinStaircaseExponents n lam s where
  toFun a := ⟨a.val, (mem_griffinStaircaseExponents_iff a.val hs hheight).mpr
    ⟨(mem_untruncatedStaircaseExponents_iff a.val).mp a.property,
      fun i => (shuffleBound_fullSize_lt hcard
        ((mem_untruncatedStaircaseExponents_iff a.val).mp a.property) i).trans_le hheight⟩⟩
  invFun a := ⟨a.val, (mem_untruncatedStaircaseExponents_iff a.val).mpr
    ((mem_griffinStaircaseExponents_iff a.val hs hheight).mp a.property).1⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem rowFactorialProduct_padded (lam : YoungDiagram) :
    (∏ i : Fin (lam.colLen 0 + 1), (lam.rowLen i.val).factorial) =
      rowFactorialProduct lam := by
  rw [Fin.prod_univ_eq_prod_range (fun j => (lam.rowLen j).factorial), Finset.prod_range_succ,
    YoungDiagram.rowLen_eq_zero_of_colLen_le le_rfl, Nat.factorial_zero, mul_one]
  rfl

theorem finite_fullSizeStaircase {n : ℕ} (lam : YoungDiagram) (hcard : lam.card = n) :
    Finite (UntruncatedStaircaseExponents n lam) := by
  let s := lam.colLen 0 + 1
  have hs : 0 < s := Nat.succ_pos _
  have hheight : lam.colLen 0 ≤ s := Nat.le_succ _
  letI := (finite_griffinStaircaseExponents (n := n) (μ := lam) s hs hheight).fintype
  exact Finite.of_equiv (GriffinStaircaseExponents n lam s)
    (fullSizeStaircaseEquiv lam hcard s hs hheight).symm

theorem card_fullSizeStaircase {n : ℕ} (lam : YoungDiagram) (hcard : lam.card = n) :
    Nat.card (UntruncatedStaircaseExponents n lam) =
      n.factorial / rowFactorialProduct lam := by
  let s := lam.colLen 0 + 1
  have hs : 0 < s := Nat.succ_pos _
  have hheight : lam.colLen 0 ≤ s := Nat.le_succ _
  rw [Nat.card_congr (fullSizeStaircaseEquiv lam hcard s hs hheight),
    card_staircase_eq_contentWords n lam s hs hheight,
    card_fullSizeContentWord lam hcard s hheight]
  rw [show s = lam.colLen 0 + 1 from rfl, rowFactorialProduct_padded]

theorem finrank_fullSize_untruncated (K : Type*) [Field K]
    {n : ℕ} (lam : YoungDiagram) (hcard : lam.card = n) :
    Module.finrank K (UntruncatedRing K n lam) =
      n.factorial / rowFactorialProduct lam := by
  letI := finite_fullSizeStaircase lam hcard
  letI : Fintype (UntruncatedStaircaseExponents n lam) := Fintype.ofFinite _
  rw [Module.finrank_eq_card_basis
    (untruncatedStandardMonomialBasis (R := K) hcard.le),
    ← Nat.card_eq_fintype_card, card_fullSizeStaircase lam hcard]

theorem finrank_springer (K : Type*) [Field K] (lam : YoungDiagram) :
    Module.finrank K (SpringerRing K lam) =
      lam.card.factorial / rowFactorialProduct lam :=
  finrank_fullSize_untruncated K lam rfl

end HigherSpecht
end
end CanonicalSource44

section CanonicalSource45
/- Source: HigherSpecht/AdjoinOnesRows.lean -/



/-! The literal row lengths after adjoining one-box rows. -/

noncomputable section

open TauCeti

namespace HigherSpecht

theorem adjoinOnes_rowLen (lam : YoungDiagram) (m r : ℕ) :
    (adjoinOnes lam m).rowLen r =
      if r < lam.colLen 0 then lam.rowLen r
      else if r < lam.colLen 0 + m then 1 else 0 := by
  by_cases hr : r < lam.colLen 0
  · rw [if_pos hr]
    have hp : 0 < lam.rowLen r := YoungDiagram.mem_iff_lt_rowLen.mp
      (YoungDiagram.mem_iff_lt_colLen.mpr hr)
    apply eq_of_forall_lt_iff
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen, mem_adjoinOnes,
      YoungDiagram.mem_iff_lt_rowLen]
    omega
  · rw [if_neg hr]
    have hz : lam.rowLen r = 0 :=
      YoungDiagram.rowLen_eq_zero_of_colLen_le (Nat.le_of_not_gt hr)
    apply eq_of_forall_lt_iff
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen, mem_adjoinOnes,
      YoungDiagram.mem_iff_lt_rowLen, hz]
    split_ifs <;> omega

end HigherSpecht
end
end CanonicalSource45

section CanonicalSource46
/- Source: HigherSpecht/ParameterPresentation.lean -/



/-!
# The actual presentation over the elementary parameter ring

Adjoining formal elementary parameters and imposing their literal values
is an elimination presentation of the original untruncated quotient.  Both
maps below are polynomial evaluations, and their inverse identities are
checked on the genuine variable classes.  This supplies the algebraic
base-change presentation independently of parameter freeness or a basis.
-/

noncomputable section

open TauCeti MvPolynomial
open scoped TensorProduct

namespace HigherSpecht

variable {R : Type*} [CommRing R] (n : ℕ) (lam : YoungDiagram)

abbrev UniversalParameterFiber :=
  ParameterFiber (ElementaryParameterRing R n lam) n lam (n - lam.card)
    (fun i => MvPolynomial.X i)

def universalParameterEvaluation :
    PolynomialRing n (ElementaryParameterRing R n lam) →ₐ[ElementaryParameterRing R n lam]
      UntruncatedRing R n lam :=
  MvPolynomial.aeval (fun i => Ideal.Quotient.mk (untruncatedIdeal R n lam) (MvPolynomial.X i))

theorem universalParameterEvaluation_elementary (A : Finset (Fin n)) (d : ℕ) :
    universalParameterEvaluation (R := R) n lam (elementaryOn A d) =
      Ideal.Quotient.mk (untruncatedIdeal R n lam) (elementaryOn A d) := by
  simp only [universalParameterEvaluation, MvPolynomial.aeval_def,
    eval₂_elementaryOn, elementaryValue, elementaryOn, map_sum, map_prod, MvPolynomial.eval₂_X]

theorem universalParameterEvaluation_kills_ideal :
    parameterFiberIdeal (ElementaryParameterRing R n lam) n lam (n - lam.card)
        (fun i => MvPolynomial.X i) ≤
      RingHom.ker (universalParameterEvaluation (R := R) n lam).toRingHom := by
  apply sup_le
  · apply Ideal.span_le.mpr
    rintro p ⟨Y, d, hd, hcard, hth, rfl⟩
    change universalParameterEvaluation (R := R) n lam (elementaryOn Y d) = 0
    rw [universalParameterEvaluation_elementary]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span ⟨Y, d, hd, hcard, hth, rfl⟩)
  · apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    change universalParameterEvaluation (R := R) n lam
      (elementaryOn Finset.univ (i.val + 1) - MvPolynomial.C (MvPolynomial.X i)) = 0
    rw [map_sub, universalParameterEvaluation_elementary]
    simp only [universalParameterEvaluation, MvPolynomial.aeval_C]
    change Ideal.Quotient.mk (untruncatedIdeal R n lam)
      (elementaryOn Finset.univ (i.val + 1)) -
      algebraMap (ElementaryParameterRing R n lam) (UntruncatedRing R n lam)
        (MvPolynomial.X i) = 0
    rw [untruncatedParameter_algebraMap, MvPolynomial.aeval_X]
    exact sub_self _

def universalParameterToUntruncated :
    UniversalParameterFiber (R := R) n lam →ₐ[ElementaryParameterRing R n lam]
      UntruncatedRing R n lam :=
  Ideal.Quotient.liftₐ _ (universalParameterEvaluation n lam)
    (fun p hp => RingHom.mem_ker.mp (universalParameterEvaluation_kills_ideal n lam hp))

@[simp] theorem universalParameterToUntruncated_X (i : Fin n) :
    universalParameterToUntruncated (R := R) n lam
        (Ideal.Quotient.mk (parameterFiberIdeal (ElementaryParameterRing R n lam)
          n lam (n - lam.card) (fun i => MvPolynomial.X i)) (MvPolynomial.X i)) =
      Ideal.Quotient.mk (untruncatedIdeal R n lam) (MvPolynomial.X i) := by
  change universalParameterEvaluation (R := R) n lam (MvPolynomial.X i) = _
  exact MvPolynomial.aeval_X _ _

def originalToUniversalParameterEvaluation :
    PolynomialRing n R →ₐ[R] UniversalParameterFiber (R := R) n lam :=
  MvPolynomial.aeval (fun i => Ideal.Quotient.mk
    (parameterFiberIdeal (ElementaryParameterRing R n lam) n lam (n - lam.card)
      (fun i => MvPolynomial.X i)) (MvPolynomial.X i))

theorem originalToUniversalParameterEvaluation_elementary (A : Finset (Fin n)) (d : ℕ) :
    originalToUniversalParameterEvaluation (R := R) n lam (elementaryOn A d) =
      Ideal.Quotient.mk (parameterFiberIdeal (ElementaryParameterRing R n lam)
        n lam (n - lam.card) (fun i => MvPolynomial.X i))
        (elementaryOn A d) := by
  simp only [originalToUniversalParameterEvaluation, MvPolynomial.aeval_def,
    eval₂_elementaryOn, elementaryValue, elementaryOn, map_sum, map_prod, MvPolynomial.eval₂_X]

theorem originalToUniversalParameterEvaluation_kills_ideal :
    untruncatedIdeal R n lam ≤
      RingHom.ker (originalToUniversalParameterEvaluation (R := R) n lam).toRingHom := by
  apply Ideal.span_le.mpr
  rintro p ⟨Y, d, hd, hcard, hth, rfl⟩
  change originalToUniversalParameterEvaluation (R := R) n lam (elementaryOn Y d) = 0
  rw [originalToUniversalParameterEvaluation_elementary]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Submodule.mem_sup_left (Ideal.subset_span ⟨Y, d, hd, hcard, hth, rfl⟩))

def untruncatedToUniversalParameterR :
    UntruncatedRing R n lam →ₐ[R] UniversalParameterFiber (R := R) n lam :=
  Ideal.Quotient.liftₐ _ (originalToUniversalParameterEvaluation n lam)
    (fun p hp => RingHom.mem_ker.mp (originalToUniversalParameterEvaluation_kills_ideal n lam hp))

@[simp] theorem untruncatedToUniversalParameterR_X (i : Fin n) :
    untruncatedToUniversalParameterR (R := R) n lam
        (Ideal.Quotient.mk (untruncatedIdeal R n lam) (MvPolynomial.X i)) =
      Ideal.Quotient.mk (parameterFiberIdeal (ElementaryParameterRing R n lam)
        n lam (n - lam.card) (fun i => MvPolynomial.X i)) (MvPolynomial.X i) := by
  change originalToUniversalParameterEvaluation (R := R) n lam (MvPolynomial.X i) = _
  exact MvPolynomial.aeval_X _ _

theorem untruncatedToUniversalParameterR_parameter (i : Fin (n - lam.card)) :
    untruncatedToUniversalParameterR (R := R) n lam (elementaryParameterClasses R n lam i) =
      algebraMap (ElementaryParameterRing R n lam) (UniversalParameterFiber (R := R) n lam)
        (MvPolynomial.X i) := by
  change originalToUniversalParameterEvaluation (R := R) n lam
    (elementaryOn Finset.univ (i.val + 1)) = _
  rw [originalToUniversalParameterEvaluation_elementary]
  exact fiber_elementary_parameter (fun i => MvPolynomial.X i) i

theorem untruncatedToUniversalParameterR_commutes (p : ElementaryParameterRing R n lam) :
    untruncatedToUniversalParameterR (R := R) n lam
      (algebraMap (ElementaryParameterRing R n lam) (UntruncatedRing R n lam) p) =
      algebraMap (ElementaryParameterRing R n lam) (UniversalParameterFiber (R := R) n lam) p := by
  have h : (untruncatedToUniversalParameterR (R := R) n lam).comp
      (MvPolynomial.aeval (elementaryParameterClasses R n lam)) =
      IsScalarTower.toAlgHom R (ElementaryParameterRing R n lam)
        (UniversalParameterFiber (R := R) n lam) := by
    ext i
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
    exact untruncatedToUniversalParameterR_parameter n lam i
  exact AlgHom.congr_fun h p

def untruncatedToUniversalParameter :
    UntruncatedRing R n lam →ₐ[ElementaryParameterRing R n lam]
      UniversalParameterFiber (R := R) n lam where
  __ := (untruncatedToUniversalParameterR (R := R) n lam).toRingHom
  commutes' := untruncatedToUniversalParameterR_commutes n lam

@[simp] theorem untruncatedToUniversalParameter_X (i : Fin n) :
    untruncatedToUniversalParameter (R := R) n lam
        (Ideal.Quotient.mk (untruncatedIdeal R n lam) (MvPolynomial.X i)) =
      Ideal.Quotient.mk (parameterFiberIdeal (ElementaryParameterRing R n lam)
        n lam (n - lam.card) (fun i => MvPolynomial.X i)) (MvPolynomial.X i) :=
  untruncatedToUniversalParameterR_X n lam i

/-- Eliminating the formal parameter variables recovers the original
untruncated ring, as an algebra over its actual elementary-parameter ring. -/
def universalParameterPresentationEquiv :
    UniversalParameterFiber (R := R) n lam ≃ₐ[ElementaryParameterRing R n lam]
      UntruncatedRing R n lam :=
  AlgEquiv.ofAlgHom (universalParameterToUntruncated n lam)
    (untruncatedToUniversalParameter n lam)
    (by
      have h : ((universalParameterToUntruncated (R := R) n lam).restrictScalars R).comp
          (untruncatedToUniversalParameterR n lam) = AlgHom.id R (UntruncatedRing R n lam) := by
        apply Ideal.Quotient.algHom_ext
        ext i
        simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
          untruncatedToUniversalParameterR_X, AlgHom.restrictScalars_apply,
          universalParameterToUntruncated_X, AlgHom.id_apply]
      exact AlgHom.ext fun x => AlgHom.congr_fun h x)
    (by
      apply Ideal.Quotient.algHom_ext
      ext i
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
        universalParameterToUntruncated_X, untruncatedToUniversalParameter_X,
        AlgHom.id_apply])

/-- Base-changing the actual elementary-parameter algebra is exactly the
fiber with parameters equal to the images of its generators. -/
def elementaryParameterBaseChangeEquiv
    (S : Type*) [CommRing S] [Algebra (ElementaryParameterRing R n lam) S] :
    S ⊗[ElementaryParameterRing R n lam] UntruncatedRing R n lam ≃ₐ[S]
      ParameterFiber S n lam (n - lam.card)
        (fun i => algebraMap (ElementaryParameterRing R n lam) S (MvPolynomial.X i)) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
      (universalParameterPresentationEquiv (R := R) n lam).symm).trans
    (parameterFiberBaseChangeEquiv n lam (n - lam.card) (fun i => MvPolynomial.X i))

end HigherSpecht
end
end CanonicalSource46

section CanonicalSource47
/- Source: HigherSpecht/UntruncatedRank.lean -/



/-!
# The numerical rank of the actual elementary-parameter basis

Specializing every elementary parameter to zero gives the genuine Springer
ring for the diagram obtained by adjoining `n - |lam|` parts equal to one.
Base change preserves the actual basis.  Its cardinal is therefore the
dimension of that Springer ring, already counted by its integral staircase
basis and literal fixed-content words.  This yields the printed factorial
quotient without assuming a permutation-restriction counting formula.
-/

noncomputable section

open TauCeti Module MvPolynomial Finset
open scoped Classical TensorProduct BigOperators

namespace HigherSpecht

@[simp] theorem rowFactorialProduct_adjoinOnes (lam : YoungDiagram) (m : ℕ) :
    rowFactorialProduct (adjoinOnes lam m) = rowFactorialProduct lam := by
  unfold rowFactorialProduct
  rw [adjoinOnes_colLen_zero, Finset.prod_range_add]
  have hfirst : (∏ j ∈ Finset.range (lam.colLen 0),
      ((adjoinOnes lam m).rowLen j).factorial) =
      ∏ j ∈ Finset.range (lam.colLen 0), (lam.rowLen j).factorial := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [adjoinOnes_rowLen, if_pos (Finset.mem_range.mp hj)]
  have htail : (∏ j ∈ Finset.range m,
      ((adjoinOnes lam m).rowLen (lam.colLen 0 + j)).factorial) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    have hjm := Finset.mem_range.mp hj
    rw [adjoinOnes_rowLen, if_neg (by omega), if_pos (by omega), Nat.factorial_one]
  rw [hfirst, htail, mul_one]

abbrev zeroParameterAlgebra (K : Type*) [CommRing K] (n : ℕ) (lam : YoungDiagram) :
    Algebra (ElementaryParameterRing K n lam) K :=
  (MvPolynomial.constantCoeff : ElementaryParameterRing K n lam →+* K).toAlgebra

theorem parameterFiberIdeal_zero (K : Type*) [CommRing K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    parameterFiberIdeal K n lam (n - lam.card) (fun _ => 0) =
      untruncatedIdeal K n (adjoinOnes lam (n - lam.card)) := by
  have h := specialFiberIdeal_eq (R := K) lam (n - lam.card)
  rw [Nat.add_sub_of_le hk] at h
  simpa only [parameterFiberIdeal, map_zero, sub_zero, elementaryOn_univ,
    elementaryParameterIdeal] using h.symm

/-- The literal all-zero elementary-parameter fiber.  The local coefficient
algebra is evaluation at zero and is recorded in the type. -/
def zeroParameterBaseChangeEquiv (K : Type*) [CommRing K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    letI : Algebra (ElementaryParameterRing K n lam) K := zeroParameterAlgebra K n lam
    letI : Module (ElementaryParameterRing K n lam) (UntruncatedRing K n lam) :=
      @Algebra.toModule (ElementaryParameterRing K n lam) (UntruncatedRing K n lam)
        _ _ (untruncatedParameterAlgebra K n lam)
    K ⊗[ElementaryParameterRing K n lam] UntruncatedRing K n lam ≃ₐ[K]
      UntruncatedRing K n (adjoinOnes lam (n - lam.card)) := by
  letI : Algebra (ElementaryParameterRing K n lam) K := zeroParameterAlgebra K n lam
  letI : Module (ElementaryParameterRing K n lam) (UntruncatedRing K n lam) :=
    @Algebra.toModule (ElementaryParameterRing K n lam) (UntruncatedRing K n lam)
      _ _ (untruncatedParameterAlgebra K n lam)
  have hparams : (fun i : Fin (n - lam.card) =>
      algebraMap (ElementaryParameterRing K n lam) K (MvPolynomial.X i)) =
      (fun _ => 0) := by
    funext i
    change MvPolynomial.constantCoeff (MvPolynomial.X i : ElementaryParameterRing K n lam) = 0
    exact MvPolynomial.constantCoeff_X K i
  let E : K ⊗[ElementaryParameterRing K n lam] UntruncatedRing K n lam ≃ₐ[K]
      ParameterFiber K n lam (n - lam.card) (fun _ => 0) := by
    exact (elementaryParameterBaseChangeEquiv (R := K) n lam K).trans
      (Ideal.quotientEquivAlgOfEq K
        (congrArg (parameterFiberIdeal K n lam (n - lam.card)) hparams))
  exact E.trans (Ideal.quotientEquivAlgOfEq K (parameterFiberIdeal_zero K n lam hk))

/-- The exact numerical rank printed in Theorem 6.1, including the empty
partition.  The adjoined one-parts contribute only factorials equal to one. -/
theorem untruncated_parameter_rank (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Module.finrank (ElementaryParameterRing K n lam) (UntruncatedRing K n lam) =
      n.factorial / rowFactorialProduct lam := by
  letI : Fintype (UntruncatedIndex n lam hk) := Fintype.ofFinite _
  letI : Algebra (ElementaryParameterRing K n lam) K := zeroParameterAlgebra K n lam
  letI : Module (ElementaryParameterRing K n lam) (UntruncatedRing K n lam) :=
    @Algebra.toModule (ElementaryParameterRing K n lam) (UntruncatedRing K n lam)
      _ _ (untruncatedParameterAlgebra K n lam)
  let B := untruncatedPrescribedParameterBasis K n lam hk
  let E := zeroParameterBaseChangeEquiv K n lam hk
  let C := (B.baseChange K).map E.toLinearEquiv
  have hcard : (adjoinOnes lam (n - lam.card)).card = n := by
    rw [adjoinOnes_card, Nat.add_sub_of_le hk]
  calc
    Module.finrank (ElementaryParameterRing K n lam) (UntruncatedRing K n lam) =
        Fintype.card (UntruncatedIndex n lam hk) := Module.finrank_eq_card_basis B
    _ = Module.finrank K (UntruncatedRing K n (adjoinOnes lam (n - lam.card))) :=
      (Module.finrank_eq_card_basis C).symm
    _ = n.factorial / rowFactorialProduct (adjoinOnes lam (n - lam.card)) :=
      finrank_fullSize_untruncated K _ hcard
    _ = n.factorial / rowFactorialProduct lam := by rw [rowFactorialProduct_adjoinOnes]

theorem card_untruncatedIndex_exact (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Nat.card (UntruncatedIndex n lam hk) = n.factorial / rowFactorialProduct lam := by
  rw [← untruncated_parameter_rank_eq_index ℚ n lam hk]
  exact untruncated_parameter_rank ℚ n lam hk

/-- The algebraic-independence, prescribed free-basis, finiteness, and exact
rank conclusions of Theorem 6.1.  Its Frobenius series and dimension/depth
conclusions are separate endpoints. -/
theorem theorem_6_1_basis_and_rank (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    AlgebraicIndependent K (elementaryParameterClasses K n lam) ∧
    IsSpecifiedBasis (R := ElementaryParameterRing K n lam)
      (untruncatedFamily K n lam hk) ∧
    Module.Finite (ElementaryParameterRing K n lam) (UntruncatedRing K n lam) ∧
    Module.finrank (ElementaryParameterRing K n lam) (UntruncatedRing K n lam) =
      n.factorial / rowFactorialProduct lam :=
  ⟨elementaryParameters_algebraicIndependent K n lam hk,
    untruncated_specified_parameter_basis K n lam hk,
    untruncated_finite_parameters K n lam hk,
    untruncated_parameter_rank K n lam hk⟩

end HigherSpecht
end
end CanonicalSource47

section CanonicalSource48
/- Source: HigherSpecht/FiniteFlatCohenMacaulay.lean -/



/-!
# Finite flat algebras over regular rings are Cohen–Macaulay

This is the usual local statement with its complete depth/dimension
content.  At a prime of the finite flat algebra, going down and
quasi-finiteness identify its dimension with that of the localized base.
The actual flat local depth formula then gives the required depth bound.
No regular-sequence or Cohen–Macaulay hypothesis on the target is assumed.
-/

noncomputable section

universe u

open IsLocalRing

namespace HigherSpecht

theorem finiteFlat_isCohenMacaulay_atPrime
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [IsRegularRing R] [Module.Finite R A] [Module.Flat R A]
    (P : Ideal A) [P.IsPrime] :
    Module.IsCohenMacaulay (Localization.AtPrime P) (Localization.AtPrime P) := by
  let p := P.under R
  let Rp := Localization.AtPrime p
  let Aq := Localization.AtPrime P
  letI : IsNoetherianRing A := IsNoetherianRing.of_finite R A
  letI : p.IsPrime := Ideal.IsPrime.under R P
  letI : P.LiesOver p := ⟨rfl⟩
  letI : Algebra Rp Aq := Localization.AtPrime.algebraOfLiesOver p P
  letI : IsLocalHom (algebraMap Rp Aq) := by
    rw [Localization.AtPrime.algebraMap_eq p P]
    exact Localization.isLocalHom_localRingHom p P (algebraMap R A) Ideal.LiesOver.over
  have hbase : Module.IsCohenMacaulay Rp Rp :=
    TauCeti.IsRegularLocalRing.isCohenMacaulay
  have hdim : ringKrullDim Aq = ringKrullDim Rp := by
    rw [Ideal.ringKrullDim_localization_atPrime_eq_height_under R P,
      IsLocalization.AtPrime.ringKrullDim_eq_height p]
  have hdepth : depth (ModuleCat.of Rp Rp) ≤ depth (ModuleCat.of Aq Aq) := by
    rw [IsLocalRing.depth_eq_add_of_flat (R := Rp) (S := Aq)]
    exact le_add_of_nonneg_right zero_le
  apply Module.isCohenMacaulay_iff_supportDim_le_depth.mpr
  rw [Module.supportDim_self_eq_ringKrullDim, hdim]
  calc
    ringKrullDim Rp = (depth (ModuleCat.of Rp Rp) : WithBot ℕ∞) :=
      (hbase.depth_eq.trans (Module.supportDim_self_eq_ringKrullDim Rp)).symm
    _ ≤ (depth (ModuleCat.of Aq Aq) : WithBot ℕ∞) := WithBot.coe_le_coe.mpr hdepth

end HigherSpecht
end
end CanonicalSource48

section CanonicalSource49
/- Source: HigherSpecht/UntruncatedCohenMacaulay.lean -/



/-!
# Dimension and Cohen–Macaulayness in Theorem 6.1

All module structures use the actual images of the elementary symmetric
polynomials.  The free basis supplies flatness and finiteness, its genuine
algebraic independence supplies injectivity, and the integral dimension
theorem gives the printed Krull dimension.  Cohen–Macaulayness is asserted
at every prime localization of the actual quotient ring.
-/

noncomputable section

open TauCeti Module MvPolynomial

namespace HigherSpecht

/-- Finite presentation over the actual elementary parameters needs no
characteristic hypothesis or higher Specht basis: the quotient is a
finite-type coefficient algebra and the parameter ring is Noetherian. -/
theorem untruncated_parameter_finitePresentation
    (R : Type*) [CommRing R] [IsNoetherianRing R] (n : ℕ) (lam : YoungDiagram) :
    Algebra.FinitePresentation (ElementaryParameterRing R n lam) (UntruncatedRing R n lam) := by
  letI : Algebra.FiniteType R (UntruncatedRing R n lam) := inferInstance
  letI : Algebra.FiniteType (ElementaryParameterRing R n lam) (UntruncatedRing R n lam) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R
      (ElementaryParameterRing R n lam) (UntruncatedRing R n lam)
  exact Algebra.FinitePresentation.of_finiteType.mp inferInstance

theorem untruncated_parameter_free (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Module.Free (ElementaryParameterRing K n lam) (UntruncatedRing K n lam) :=
  Module.Free.of_basis (untruncatedPrescribedParameterBasis K n lam hk)

theorem untruncated_parameter_flat (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Module.Flat (ElementaryParameterRing K n lam) (UntruncatedRing K n lam) := by
  letI := untruncated_parameter_free K n lam hk
  infer_instance

theorem untruncated_parameter_faithful (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    FaithfulSMul (ElementaryParameterRing K n lam) (UntruncatedRing K n lam) := by
  apply (faithfulSMul_iff_algebraMap_injective _ _).mpr
  change Function.Injective (MvPolynomial.aeval (elementaryParameterClasses K n lam))
  exact elementaryParameters_algebraicIndependent K n lam hk

theorem untruncated_krullDimension (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    ringKrullDim (UntruncatedRing K n lam) = (n - lam.card : ℕ) := by
  letI := untruncated_finite_parameters K n lam hk
  letI := untruncated_parameter_faithful K n lam hk
  rw [TauCeti.ringKrullDim_eq_of_isIntegral_of_faithfulSMul
    (R := ElementaryParameterRing K n lam)]
  change ringKrullDim (MvPolynomial (Fin (n - lam.card)) K) = _
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field, zero_add, Nat.card_fin]

theorem untruncated_isNoetherian (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    IsNoetherianRing (UntruncatedRing K n lam) := by
  letI := untruncated_finite_parameters K n lam hk
  exact IsNoetherianRing.of_finite (ElementaryParameterRing K n lam) _

theorem untruncated_isCohenMacaulay_atPrime (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (P : Ideal (UntruncatedRing K n lam)) [P.IsPrime] :
    Module.IsCohenMacaulay (Localization.AtPrime P) (Localization.AtPrime P) := by
  letI := untruncated_finite_parameters K n lam hk
  letI := untruncated_parameter_flat K n lam hk
  exact finiteFlat_isCohenMacaulay_atPrime
    (ElementaryParameterRing K n lam) (UntruncatedRing K n lam) P

/-- The dimension and Cohen–Macaulay conclusions of Theorem 6.1, including
the empty partition and zero-dimensional case. -/
theorem theorem_6_1_dimension_and_cohenMacaulay
    (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    ringKrullDim (UntruncatedRing K n lam) = (n - lam.card : ℕ) ∧
      IsNoetherianRing (UntruncatedRing K n lam) ∧
      ∀ (P : Ideal (UntruncatedRing K n lam)) [P.IsPrime],
        Module.IsCohenMacaulay (Localization.AtPrime P) (Localization.AtPrime P) :=
  ⟨untruncated_krullDimension K n lam hk,
    untruncated_isNoetherian K n lam hk,
    untruncated_isCohenMacaulay_atPrime K n lam hk⟩

end HigherSpecht
end
end CanonicalSource49

section CanonicalSource50
/- Source: HigherSpecht/HomogeneousParameterLifting.lean -/



/-!
# Lifting homogeneous generators from the actual special fiber

The proof is the degree induction in Corollary 6.5, over an arbitrary
coefficient ring.  The special-fiber relation is decomposed in the literal
sum of the original ideal and the positive-degree elementary parameters.
Projecting the relation to its genuine homogeneous degree makes every
remaining parameter coefficient have smaller degree.  No graded freeness
or flatness assertion is used in this spanning step.
-/

noncomputable section

open TauCeti Module MvPolynomial Finset

namespace HigherSpecht

attribute [local instance] MvPolynomial.gradedAlgebra

theorem homogeneousComponent_mul_homogeneous_right
    {R σ : Type*} [CommRing R] {d e : ℕ} (p q : MvPolynomial σ R)
    (hq : q.IsHomogeneous e) :
    MvPolynomial.homogeneousComponent d (p * q) =
      if e ≤ d then MvPolynomial.homogeneousComponent (d - e) p * q else 0 := by
  simpa only [← DirectSum.Decomposition.decompose'_eq,
    MvPolynomial.decomposition.decompose'_apply] using
    (DirectSum.coe_decompose_mul_of_right_mem
      (MvPolynomial.homogeneousSubmodule σ R) d hq (a := p))

theorem untruncated_span_parameters_of_specialFiber_span
    (R : Type*) [CommRing R] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    {ι : Type*} [Fintype ι] (f : ι → PolynomialRing n R) (deg : ι → ℕ)
    (hf : ∀ i, (f i).IsHomogeneous (deg i))
    (hspan : Submodule.span R (Set.range fun i =>
      Ideal.Quotient.mk (untruncatedIdeal R n (adjoinOnes lam (n - lam.card))) (f i)) = ⊤) :
    Submodule.span (ElementaryParameterRing R n lam)
      (Set.range fun i => Ideal.Quotient.mk (untruncatedIdeal R n lam) (f i)) = ⊤ := by
  classical
  let J := untruncatedIdeal R n lam
  let I := untruncatedIdeal R n (adjoinOnes lam (n - lam.card))
  let B := ElementaryParameterRing R n lam
  let A := UntruncatedRing R n lam
  let Q : PolynomialRing n R →ₐ[R] A := Ideal.Quotient.mkₐ R J
  let N : Submodule B A := Submodule.span B (Set.range fun i => Q (f i))
  have hI : I = J ⊔ elementaryParameterIdeal R n (n - lam.card) := by
    have h := specialFiberIdeal_eq (R := R) lam (n - lam.card)
    rwa [Nat.add_sub_of_le hk] at h
  have hgen (i : ι) : Q (f i) ∈ N := Submodule.subset_span ⟨i, rfl⟩
  have hhom : ∀ d (p : PolynomialRing n R), p.IsHomogeneous d → Q p ∈ N := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro p hp
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp
        (show Ideal.Quotient.mk I p ∈ Submodule.span R
          (Set.range fun i => Ideal.Quotient.mk I (f i)) by rw [hspan]; trivial)
      let F : PolynomialRing n R := ∑ i, c i • f i
      have hrel : p - F ∈ I := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        rw [map_sub]
        have hF : Ideal.Quotient.mk I F = Ideal.Quotient.mk I p := by
          change (Ideal.Quotient.mkₐ R I) F = (Ideal.Quotient.mkₐ R I) p
          simpa only [F, map_sum, map_smul, Ideal.Quotient.mkₐ_eq_mk] using hc
        rw [hF, sub_self]
      rw [hI] at hrel
      obtain ⟨j, hj, e, he, hje⟩ := Submodule.mem_sup.mp hrel
      obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (PolynomialRing n R)).mp he
      have hpoly : p = j + (∑ i : Fin (n - lam.card),
          a i * MvPolynomial.esymm (Fin n) R (i.val + 1)) + F := by
        have ha' : (∑ i : Fin (n - lam.card),
            a i * MvPolynomial.esymm (Fin n) R (i.val + 1)) = e := by
          simpa only [smul_eq_mul] using ha
        rw [ha']
        exact eq_add_of_sub_eq hje.symm
      have hjzero : Q (MvPolynomial.homogeneousComponent d j) = 0 := by
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        exact MvPolynomial.homogeneousComponent_mem_of_mem
          (untruncatedIdeal_isHomogeneous hk) hj d
      have hFmem : Q (MvPolynomial.homogeneousComponent d F) ∈ N := by
        simp only [F, map_sum, map_smul]
        apply (N.restrictScalars R).sum_mem
        intro i hi
        apply (N.restrictScalars R).smul_mem
        rw [MvPolynomial.homogeneousComponent_of_mem (hf i)]
        split_ifs
        · exact hgen i
        · simpa only [map_zero] using (N.restrictScalars R).zero_mem
      have hemem : Q (MvPolynomial.homogeneousComponent d
          (∑ i : Fin (n - lam.card),
            a i * MvPolynomial.esymm (Fin n) R (i.val + 1))) ∈ N := by
        simp only [map_sum]
        apply N.sum_mem
        intro i hi
        change Q (MvPolynomial.homogeneousComponent d
          (a i * elementaryOn (Finset.univ : Finset (Fin n)) (i.val + 1))) ∈ N
        rw [homogeneousComponent_mul_homogeneous_right _ _
          (elementaryOn_isHomogeneous (Finset.univ : Finset (Fin n)) (i.val + 1))]
        split_ifs with hid
        · have hcoeff : Q (MvPolynomial.homogeneousComponent (d - (i.val + 1)) (a i)) ∈ N :=
            ih _ (by omega) _ (MvPolynomial.homogeneousComponent_isHomogeneous _ _)
          have hmul : Q (MvPolynomial.homogeneousComponent (d - (i.val + 1)) (a i) *
              elementaryOn (Finset.univ : Finset (Fin n)) (i.val + 1)) =
              (MvPolynomial.X i : B) •
                Q (MvPolynomial.homogeneousComponent (d - (i.val + 1)) (a i)) := by
            rw [map_mul, Algebra.smul_def, untruncatedParameter_algebraMap,
              MvPolynomial.aeval_X]
            change _ * Q (elementaryOn Finset.univ (i.val + 1)) =
              Q (elementaryOn Finset.univ (i.val + 1)) * _
            exact mul_comm _ _
          rw [hmul]
          exact N.smul_mem _ hcoeff
        · simpa only [map_zero] using N.zero_mem
      rw [← MvPolynomial.homogeneousComponent_eq_self hp, hpoly,
        map_add, map_add, map_add, map_add, hjzero, zero_add]
      exact N.add_mem hemem hFmem
  apply top_unique
  intro x hx
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Q p ∈ N
  rw [← MvPolynomial.sum_homogeneousComponent p, map_sum]
  exact N.sum_mem fun d hd => hhom d _ (MvPolynomial.homogeneousComponent_isHomogeneous _ _)

end HigherSpecht
end
end CanonicalSource50

section CanonicalSource51
/- Source: HigherSpecht/ParameterCoefficientMap.lean -/



/-! Actual coefficient change of the elementary-parameter quotient. -/

noncomputable section

open TauCeti MvPolynomial

namespace HigherSpecht

variable {R S : Type*} [CommRing R] [CommRing S]

def untruncatedCoefficientMap (phi : R →+* S) (n : ℕ) (lam : YoungDiagram) :
    UntruncatedRing R n lam →+* UntruncatedRing S n lam :=
  Ideal.quotientMap (untruncatedIdeal S n lam) (MvPolynomial.map phi)
    (Ideal.map_le_iff_le_comap.mp (map_untruncatedIdeal phi n lam).le)

@[simp] theorem untruncatedCoefficientMap_mk (phi : R →+* S)
    (n : ℕ) (lam : YoungDiagram) (p : PolynomialRing n R) :
    untruncatedCoefficientMap phi n lam
        (Ideal.Quotient.mk (untruncatedIdeal R n lam) p) =
      Ideal.Quotient.mk (untruncatedIdeal S n lam) (MvPolynomial.map phi p) :=
  Ideal.quotientMap_mk

@[simp] theorem untruncatedCoefficientMap_elementaryParameter
    (phi : R →+* S) (n : ℕ) (lam : YoungDiagram) (i : Fin (n - lam.card)) :
    untruncatedCoefficientMap phi n lam (elementaryParameterClasses R n lam i) =
      elementaryParameterClasses S n lam i := by
  simp only [elementaryParameterClasses, untruncatedCoefficientMap_mk,
    MvPolynomial.map_esymm]

theorem untruncatedCoefficientMap_algebraMap
    (phi : R →+* S) (n : ℕ) (lam : YoungDiagram)
    (b : ElementaryParameterRing R n lam) :
    untruncatedCoefficientMap phi n lam
        (algebraMap (ElementaryParameterRing R n lam) (UntruncatedRing R n lam) b) =
      algebraMap (ElementaryParameterRing S n lam) (UntruncatedRing S n lam)
        (MvPolynomial.map phi b) := by
  induction b using MvPolynomial.induction_on with
  | C c =>
      simp only [untruncatedParameter_algebraMap, MvPolynomial.aeval_C,
        MvPolynomial.map_C]
      change untruncatedCoefficientMap phi n lam
        (Ideal.Quotient.mk (untruncatedIdeal R n lam) (MvPolynomial.C c)) = _
      rw [untruncatedCoefficientMap_mk, MvPolynomial.map_C]
      rfl
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
      simp only [untruncatedParameter_algebraMap] at hp
      simp only [map_mul, hp, MvPolynomial.map_X, untruncatedParameter_algebraMap,
        MvPolynomial.aeval_X, untruncatedCoefficientMap_elementaryParameter]

theorem untruncatedCoefficientMap_smul (phi : R →+* S)
    (n : ℕ) (lam : YoungDiagram) (b : ElementaryParameterRing R n lam)
    (x : UntruncatedRing R n lam) :
    untruncatedCoefficientMap phi n lam (b • x) =
      MvPolynomial.map phi b • untruncatedCoefficientMap phi n lam x := by
  rw [Algebra.smul_def, map_mul, untruncatedCoefficientMap_algebraMap,
    Algebra.smul_def]

def parameterMonomialClass (R : Type*) [CommRing R] (n : ℕ) (lam : YoungDiagram)
    (a : Fin n →₀ ℕ) : UntruncatedRing R n lam :=
  Ideal.Quotient.mk (untruncatedIdeal R n lam) (MvPolynomial.monomial a 1)

@[simp] theorem untruncatedCoefficientMap_monomial (phi : R →+* S)
    (n : ℕ) (lam : YoungDiagram) (a : Fin n →₀ ℕ) :
    untruncatedCoefficientMap phi n lam (parameterMonomialClass R n lam a) =
      parameterMonomialClass S n lam a := by
  simp only [parameterMonomialClass, untruncatedCoefficientMap_mk,
    MvPolynomial.map_monomial, map_one]

end HigherSpecht
end
end CanonicalSource51

section CanonicalSource52
/- Source: HigherSpecht/IntegralParameterBasis.lean -/



/-!
# The integral monomial lifting in Corollary 6.5

Every chosen integral monomial basis of the actual Springer special fiber
lifts to a basis over the actual integral elementary-parameter ring.  The
degree induction proves surjectivity integrally.  Over the rationals its
cardinality is the already proved parameter rank, so Orzech's theorem for
Noetherian modules makes the same generating map injective.  Applying the
literal coefficient map to an integral relation and using injectivity on
the polynomial coefficient ring then proves integral independence.
-/

noncomputable section

open TauCeti Module MvPolynomial
open scoped Classical TensorProduct

namespace HigherSpecht

theorem linearIndependent_of_span_eq_top_of_basis_card
    {R M ι κ : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Fintype ι] [Fintype κ]
    (B : Basis κ R M) (v : ι → M)
    (hspan : Submodule.span R (Set.range v) = ⊤)
    (hcard : Fintype.card ι = Fintype.card κ) : LinearIndependent R v := by
  letI : Module.Finite R M := Module.Finite.of_basis B
  let e : ι ≃ κ := Fintype.equivOfCardEq hcard
  let E : (ι →₀ R) ≃ₗ[R] M := (Finsupp.domLCongr e).trans B.repr.symm
  let L := Finsupp.linearCombination R v
  have hsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, hspan]
  exact IsNoetherian.injective_of_surjective_of_injective E.toLinearMap L E.injective hsurj

theorem monomial_specialFiber_card (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    {ι : Type*} [Fintype ι]
    (B : Basis ι ℚ (UntruncatedRing ℚ n (adjoinOnes lam (n - lam.card)))) :
    Nat.card ι = Nat.card (UntruncatedIndex n lam hk) := by
  have hcard : (adjoinOnes lam (n - lam.card)).card = n := by
    rw [adjoinOnes_card, Nat.add_sub_of_le hk]
  calc
    Nat.card ι = Module.finrank ℚ
        (UntruncatedRing ℚ n (adjoinOnes lam (n - lam.card))) := by
      rw [Nat.card_eq_fintype_card]
      exact (Module.finrank_eq_card_basis B).symm
    _ = n.factorial / rowFactorialProduct (adjoinOnes lam (n - lam.card)) :=
      finrank_fullSize_untruncated ℚ _ hcard
    _ = n.factorial / rowFactorialProduct lam := by rw [rowFactorialProduct_adjoinOnes]
    _ = Nat.card (UntruncatedIndex n lam hk) := (card_untruncatedIndex_exact n lam hk).symm

theorem monomial_parameter_linearIndependent_rat
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    {ι : Type*} [Fintype ι] (a : ι → Fin n →₀ ℕ)
    (B : Basis ι ℚ (UntruncatedRing ℚ n (adjoinOnes lam (n - lam.card))))
    (hB : ∀ i, B i = parameterMonomialClass ℚ n (adjoinOnes lam (n - lam.card)) (a i)) :
    LinearIndependent (ElementaryParameterRing ℚ n lam)
      (fun i => parameterMonomialClass ℚ n lam (a i)) := by
  letI : Fintype (UntruncatedIndex n lam hk) := Fintype.ofFinite _
  have hfamily : (B : ι → UntruncatedRing ℚ n (adjoinOnes lam (n - lam.card))) =
      (fun i => parameterMonomialClass ℚ n (adjoinOnes lam (n - lam.card)) (a i)) :=
    funext hB
  apply linearIndependent_of_span_eq_top_of_basis_card
    (untruncatedPrescribedParameterBasis ℚ n lam hk)
  · apply untruncated_span_parameters_of_specialFiber_span ℚ n lam hk
      (fun i => MvPolynomial.monomial (a i) 1) (fun i => (a i).degree)
      (fun i => MvPolynomial.isHomogeneous_monomial 1 rfl)
    simpa only [hfamily, parameterMonomialClass] using B.span_eq
  · simpa only [Nat.card_eq_fintype_card] using monomial_specialFiber_card n lam hk B

def integralSpecialFiberBasis_rat
    (n : ℕ) (lam : YoungDiagram) {ι : Type*}
    (B : Basis ι ℤ (UntruncatedRing ℤ n (adjoinOnes lam (n - lam.card)))) :
    Basis ι ℚ (UntruncatedRing ℚ n (adjoinOnes lam (n - lam.card))) :=
  (B.baseChange ℚ).map
    (untruncatedBaseChangeEquiv ℤ ℚ n (adjoinOnes lam (n - lam.card))).toLinearEquiv

@[simp] theorem integralSpecialFiberBasis_rat_apply
    (n : ℕ) (lam : YoungDiagram) {ι : Type*} (a : ι → Fin n →₀ ℕ)
    (B : Basis ι ℤ (UntruncatedRing ℤ n (adjoinOnes lam (n - lam.card))))
    (hB : ∀ i, B i = parameterMonomialClass ℤ n (adjoinOnes lam (n - lam.card)) (a i))
    (i : ι) :
    integralSpecialFiberBasis_rat n lam B i =
      parameterMonomialClass ℚ n (adjoinOnes lam (n - lam.card)) (a i) := by
  simp only [integralSpecialFiberBasis_rat, Basis.map_apply, Basis.baseChange_apply,
    hB, parameterMonomialClass, AlgEquiv.toLinearEquiv_apply,
    untruncatedBaseChangeEquiv, polynomialQuotientBaseChangeEquiv_tmul,
    MvPolynomial.map_monomial, map_one, one_smul]

theorem monomial_parameter_linearIndependent_integral
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    {ι : Type*} [Fintype ι] (a : ι → Fin n →₀ ℕ)
    (B : Basis ι ℤ (UntruncatedRing ℤ n (adjoinOnes lam (n - lam.card))))
    (hB : ∀ i, B i = parameterMonomialClass ℤ n (adjoinOnes lam (n - lam.card)) (a i)) :
    LinearIndependent (ElementaryParameterRing ℤ n lam)
      (fun i => parameterMonomialClass ℤ n lam (a i)) := by
  let phi : ℤ →+* ℚ := Int.castRingHom ℚ
  have hrat := monomial_parameter_linearIndependent_rat n lam hk a
    (integralSpecialFiberBasis_rat n lam B)
    (integralSpecialFiberBasis_rat_apply n lam a B hB)
  rw [Fintype.linearIndependent_iff] at hrat ⊢
  intro c hc i
  have hmap := congrArg (untruncatedCoefficientMap phi n lam) hc
  simp only [map_sum, untruncatedCoefficientMap_smul,
    untruncatedCoefficientMap_monomial, map_zero] at hmap
  have hi := hrat (fun j => MvPolynomial.map phi (c j)) hmap i
  exact (MvPolynomial.map_injective phi (Int.cast_injective : Function.Injective phi))
    (hi.trans (map_zero _).symm)

/-- Every actual integral monomial basis of the Springer special fiber
lifts as stated in Corollary 6.5. -/
def integralMonomialParameterBasis
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    {ι : Type*} [Fintype ι] (a : ι → Fin n →₀ ℕ)
    (B : Basis ι ℤ (UntruncatedRing ℤ n (adjoinOnes lam (n - lam.card))))
    (hB : ∀ i, B i = parameterMonomialClass ℤ n (adjoinOnes lam (n - lam.card)) (a i)) :
    Basis ι (ElementaryParameterRing ℤ n lam) (UntruncatedRing ℤ n lam) :=
  Basis.mk (monomial_parameter_linearIndependent_integral n lam hk a B hB)
    (le_of_eq (untruncated_span_parameters_of_specialFiber_span ℤ n lam hk
      (fun i => MvPolynomial.monomial (a i) 1) (fun i => (a i).degree)
      (fun i => MvPolynomial.isHomogeneous_monomial 1 rfl)
      (by
        have hfamily : (B : ι → UntruncatedRing ℤ n (adjoinOnes lam (n - lam.card))) =
            (fun i => parameterMonomialClass ℤ n (adjoinOnes lam (n - lam.card)) (a i)) :=
          funext hB
        simpa only [hfamily, parameterMonomialClass] using B.span_eq)).symm)

@[simp] theorem integralMonomialParameterBasis_apply
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    {ι : Type*} [Fintype ι] (a : ι → Fin n →₀ ℕ)
    (B : Basis ι ℤ (UntruncatedRing ℤ n (adjoinOnes lam (n - lam.card))))
    (hB : ∀ i, B i = parameterMonomialClass ℤ n (adjoinOnes lam (n - lam.card)) (a i))
    (i : ι) : integralMonomialParameterBasis n lam hk a B hB i =
      parameterMonomialClass ℤ n lam (a i) :=
  Basis.mk_apply _ _ _

end HigherSpecht
end
end CanonicalSource52

section CanonicalSource53
/- Source: HigherSpecht/ParameterPresentationCoordinates.lean -/



noncomputable section

open TauCeti MvPolynomial
open scoped TensorProduct

namespace HigherSpecht

variable {R : Type*} [CommRing R]

/-- The elimination presentation sends each original coordinate to the
same coordinate in the displayed fiber. -/
@[simp] theorem elementaryParameterBaseChangeEquiv_one_tmul_X
    (n : ℕ) (lam : YoungDiagram) (S : Type*) [CommRing S]
    [Algebra (ElementaryParameterRing R n lam) S] (i : Fin n) :
    elementaryParameterBaseChangeEquiv (R := R) n lam S
        ((1 : S) ⊗ₜ[ElementaryParameterRing R n lam]
          Ideal.Quotient.mk (untruncatedIdeal R n lam) (MvPolynomial.X i)) =
      Ideal.Quotient.mk (parameterFiberIdeal S n lam (n - lam.card)
        (fun j => algebraMap (ElementaryParameterRing R n lam) S (MvPolynomial.X j)))
        (MvPolynomial.X i) := by
  have hX : (universalParameterPresentationEquiv (R := R) n lam).symm
      (Ideal.Quotient.mk (untruncatedIdeal R n lam) (MvPolynomial.X i)) =
      Ideal.Quotient.mk (parameterFiberIdeal (ElementaryParameterRing R n lam)
        n lam (n - lam.card) (fun j => MvPolynomial.X j)) (MvPolynomial.X i) :=
    untruncatedToUniversalParameter_X n lam i
  simp only [elementaryParameterBaseChangeEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    AlgEquiv.coe_toAlgHom, AlgEquiv.coe_refl, id_eq, hX, parameterFiberBaseChangeEquiv_tmul,
    MvPolynomial.map_X, one_smul]

end HigherSpecht
end
end CanonicalSource53

section CanonicalSource54
/- Source: HigherSpecht/ParameterCoefficientBaseChange.lean -/



/-!
# Coefficient extension over the actual parameter polynomial rings

The parameter variables are preserved, rather than specialized.  The
elimination presentation therefore identifies the tensor quotient over
the integral parameter ring with the same original quotient over the new
coefficient ring.  This is the base-change map needed by Corollary 6.5.
-/

noncomputable section

open TauCeti MvPolynomial
open scoped TensorProduct

namespace HigherSpecht

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

def parameterCoefficientAlgebra (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (n : ℕ) (lam : YoungDiagram) :
    Algebra (ElementaryParameterRing R n lam) (ElementaryParameterRing S n lam) :=
  (MvPolynomial.map (algebraMap R S)).toAlgebra

def parameterCoefficientBaseChangeEquiv (R S : Type*)
    [CommRing R] [CommRing S] [Algebra R S] (n : ℕ) (lam : YoungDiagram) :
    letI := parameterCoefficientAlgebra R S n lam
    ElementaryParameterRing S n lam ⊗[ElementaryParameterRing R n lam]
        UntruncatedRing R n lam ≃ₐ[ElementaryParameterRing S n lam]
      UntruncatedRing S n lam := by
  letI := parameterCoefficientAlgebra R S n lam
  have hparams : (fun i : Fin (n - lam.card) =>
      algebraMap (ElementaryParameterRing R n lam) (ElementaryParameterRing S n lam)
        (MvPolynomial.X i)) = (fun i => MvPolynomial.X i) := by
    funext i
    change MvPolynomial.map (algebraMap R S) (MvPolynomial.X i) = MvPolynomial.X i
    exact MvPolynomial.map_X _ _
  let E : ElementaryParameterRing S n lam ⊗[ElementaryParameterRing R n lam]
      UntruncatedRing R n lam ≃ₐ[ElementaryParameterRing S n lam]
      UniversalParameterFiber (R := S) n lam := by
    exact (elementaryParameterBaseChangeEquiv (R := R)
      n lam (ElementaryParameterRing S n lam)).trans
      (Ideal.quotientEquivAlgOfEq (ElementaryParameterRing S n lam)
        (congrArg (parameterFiberIdeal (ElementaryParameterRing S n lam)
          n lam (n - lam.card)) hparams))
  exact E.trans (universalParameterPresentationEquiv (R := S) n lam)

@[simp] theorem parameterCoefficientBaseChangeEquiv_X (n : ℕ) (lam : YoungDiagram)
    (i : Fin n) :
    letI := parameterCoefficientAlgebra R S n lam
    parameterCoefficientBaseChangeEquiv R S n lam
      ((1 : ElementaryParameterRing S n lam) ⊗ₜ[ElementaryParameterRing R n lam]
        Ideal.Quotient.mk (untruncatedIdeal R n lam) (MvPolynomial.X i)) =
      Ideal.Quotient.mk (untruncatedIdeal S n lam) (MvPolynomial.X i) := by
  letI := parameterCoefficientAlgebra R S n lam
  simp only [parameterCoefficientBaseChangeEquiv, AlgEquiv.trans_apply,
    elementaryParameterBaseChangeEquiv_one_tmul_X, Ideal.quotientEquivAlgOfEq_mk]
  exact universalParameterToUntruncated_X (R := S) n lam i

@[simp] theorem parameterCoefficientBaseChangeEquiv_monomial
    (n : ℕ) (lam : YoungDiagram) (a : Fin n →₀ ℕ) :
    letI := parameterCoefficientAlgebra R S n lam
    parameterCoefficientBaseChangeEquiv R S n lam
      ((1 : ElementaryParameterRing S n lam) ⊗ₜ[ElementaryParameterRing R n lam]
        parameterMonomialClass R n lam a) = parameterMonomialClass S n lam a := by
  letI := parameterCoefficientAlgebra R S n lam
  let F : PolynomialRing n R →+* UntruncatedRing S n lam :=
    (parameterCoefficientBaseChangeEquiv R S n lam).toRingHom.comp
      (Algebra.TensorProduct.includeRight.toRingHom.comp
        (Ideal.Quotient.mk (untruncatedIdeal R n lam)))
  have hX (i : Fin n) : F (MvPolynomial.X i) =
      Ideal.Quotient.mk (untruncatedIdeal S n lam) (MvPolynomial.X i) :=
    parameterCoefficientBaseChangeEquiv_X n lam i
  change F (MvPolynomial.monomial a 1) = _
  simp only [MvPolynomial.monic_monomial_eq, Finsupp.prod, map_prod, map_pow,
    hX, parameterMonomialClass]

end HigherSpecht
end
end CanonicalSource54

section CanonicalSource55
/- Source: HigherSpecht/IntegralParameterConsequences.lean -/



/-!
# Corollary 6.5 over the integers and every coefficient field

The basis is the actual staircase-monomial basis of the Springer special
fiber, lifted unchanged to the original untruncated quotient.  Tensoring
its integral parameter basis through the explicit parameter coefficient
map proves freeness over every coefficient ring.  In particular no
characteristic bound appears in flatness, finite presentation, dimension,
or Cohen–Macaulayness over a field.
-/

noncomputable section

open TauCeti Module MvPolynomial
open scoped Classical TensorProduct

namespace HigherSpecht

abbrev SpecialFiberMonomialIndex (n : ℕ) (lam : YoungDiagram) :=
  UntruncatedStaircaseExponents n (adjoinOnes lam (n - lam.card))

theorem finite_specialFiberMonomialIndex (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Finite (SpecialFiberMonomialIndex n lam) :=
  finite_fullSizeStaircase _ (by rw [adjoinOnes_card, Nat.add_sub_of_le hk])

def untruncatedIntegralMonomialParameterBasis
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Basis (SpecialFiberMonomialIndex n lam) (ElementaryParameterRing ℤ n lam)
      (UntruncatedRing ℤ n lam) := by
  letI := finite_specialFiberMonomialIndex n lam hk
  letI : Fintype (SpecialFiberMonomialIndex n lam) := Fintype.ofFinite _
  have hmu : (adjoinOnes lam (n - lam.card)).card ≤ n := by
    rw [adjoinOnes_card, Nat.add_sub_of_le hk]
  exact integralMonomialParameterBasis n lam hk Subtype.val
    (untruncatedStandardMonomialBasis (R := ℤ) hmu)
    (untruncatedStandardMonomialBasis_apply hmu)

@[simp] theorem untruncatedIntegralMonomialParameterBasis_apply
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (a : SpecialFiberMonomialIndex n lam) :
    untruncatedIntegralMonomialParameterBasis n lam hk a =
      parameterMonomialClass ℤ n lam a.val := by
  unfold untruncatedIntegralMonomialParameterBasis integralMonomialParameterBasis
  exact Basis.mk_apply _ _ _

/-- Every integral monomial special-fiber basis lifts, with no assumed
finiteness of its indexing type; finiteness follows from the genuine
standard-monomial basis of that finite quotient. -/
def integralMonomialParameterBasis_of_basis
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    {ι : Type*} (a : ι → Fin n →₀ ℕ)
    (B : Basis ι ℤ (UntruncatedRing ℤ n (adjoinOnes lam (n - lam.card))))
    (hB : ∀ i, B i = parameterMonomialClass ℤ n (adjoinOnes lam (n - lam.card)) (a i)) :
    Basis ι (ElementaryParameterRing ℤ n lam) (UntruncatedRing ℤ n lam) := by
  letI := finite_specialFiberMonomialIndex n lam hk
  letI : Fintype (SpecialFiberMonomialIndex n lam) := Fintype.ofFinite _
  letI : Module.Finite ℤ (UntruncatedRing ℤ n (adjoinOnes lam (n - lam.card))) :=
    Module.Finite.of_basis (untruncatedStandardMonomialBasis (R := ℤ)
      (by rw [adjoinOnes_card, Nat.add_sub_of_le hk]))
  letI : Finite ι := Module.Finite.finite_basis B
  letI : Fintype ι := Fintype.ofFinite _
  exact integralMonomialParameterBasis n lam hk a B hB

@[simp] theorem integralMonomialParameterBasis_of_basis_apply
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    {ι : Type*} (a : ι → Fin n →₀ ℕ)
    (B : Basis ι ℤ (UntruncatedRing ℤ n (adjoinOnes lam (n - lam.card))))
    (hB : ∀ i, B i = parameterMonomialClass ℤ n (adjoinOnes lam (n - lam.card)) (a i))
    (i : ι) : integralMonomialParameterBasis_of_basis n lam hk a B hB i =
      parameterMonomialClass ℤ n lam (a i) := by
  simp only [integralMonomialParameterBasis_of_basis, integralMonomialParameterBasis_apply]

def untruncatedMonomialParameterBasis (R : Type*) [CommRing R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Basis (SpecialFiberMonomialIndex n lam) (ElementaryParameterRing R n lam)
      (UntruncatedRing R n lam) := by
  letI := parameterCoefficientAlgebra ℤ R n lam
  exact ((untruncatedIntegralMonomialParameterBasis n lam hk).baseChange
    (ElementaryParameterRing R n lam)).map
      (parameterCoefficientBaseChangeEquiv ℤ R n lam).toLinearEquiv

@[simp] theorem untruncatedMonomialParameterBasis_apply (R : Type*) [CommRing R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (a : SpecialFiberMonomialIndex n lam) :
    untruncatedMonomialParameterBasis R n lam hk a =
      parameterMonomialClass R n lam a.val := by
  simp only [untruncatedMonomialParameterBasis, Basis.map_apply, Basis.baseChange_apply,
    untruncatedIntegralMonomialParameterBasis_apply, AlgEquiv.toLinearEquiv_apply,
    parameterCoefficientBaseChangeEquiv_monomial]

theorem untruncated_parameter_free_allCoefficients (R : Type*) [CommRing R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Module.Free (ElementaryParameterRing R n lam) (UntruncatedRing R n lam) :=
  Module.Free.of_basis (untruncatedMonomialParameterBasis R n lam hk)

theorem untruncated_parameter_finite_allCoefficients (R : Type*) [CommRing R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Module.Finite (ElementaryParameterRing R n lam) (UntruncatedRing R n lam) := by
  letI := finite_specialFiberMonomialIndex n lam hk
  letI : Fintype (SpecialFiberMonomialIndex n lam) := Fintype.ofFinite _
  exact Module.Finite.of_basis (untruncatedMonomialParameterBasis R n lam hk)

theorem untruncated_parameter_flat_allCoefficients (R : Type*) [CommRing R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Module.Flat (ElementaryParameterRing R n lam) (UntruncatedRing R n lam) := by
  letI := untruncated_parameter_free_allCoefficients R n lam hk
  infer_instance

theorem untruncated_quotient_nontrivial (R : Type*) [CommRing R] [Nontrivial R]
    (n : ℕ) (lam : YoungDiagram) : Nontrivial (UntruncatedRing R n lam) := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  intro htop
  have h := untruncatedIdeal_le_constantCoeff_ker (R := R) n lam
    (show (1 : PolynomialRing n R) ∈ untruncatedIdeal R n lam by rw [htop]; trivial)
  exact one_ne_zero (by simpa only [RingHom.mem_ker, map_one] using h)

theorem untruncated_parameter_faithful_allCoefficients
    (R : Type*) [CommRing R] [Nontrivial R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    FaithfulSMul (ElementaryParameterRing R n lam) (UntruncatedRing R n lam) := by
  letI := untruncated_parameter_free_allCoefficients R n lam hk
  letI := untruncated_quotient_nontrivial R n lam
  exact Module.Free.instFaithfulSMulOfNontrivial
    (ElementaryParameterRing R n lam) (UntruncatedRing R n lam)

theorem elementaryParameters_algebraicIndependent_allCoefficients
    (R : Type*) [CommRing R] [Nontrivial R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    AlgebraicIndependent R (elementaryParameterClasses R n lam) := by
  letI := untruncated_parameter_faithful_allCoefficients R n lam hk
  change Function.Injective
    (algebraMap (ElementaryParameterRing R n lam) (UntruncatedRing R n lam))
  exact FaithfulSMul.algebraMap_injective _ _

theorem untruncated_parameter_rank_allCoefficients
    (R : Type*) [CommRing R] [Nontrivial R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Module.finrank (ElementaryParameterRing R n lam) (UntruncatedRing R n lam) =
      n.factorial / rowFactorialProduct lam := by
  letI := finite_specialFiberMonomialIndex n lam hk
  letI : Fintype (SpecialFiberMonomialIndex n lam) := Fintype.ofFinite _
  rw [Module.finrank_eq_card_basis (untruncatedMonomialParameterBasis R n lam hk),
    ← Nat.card_eq_fintype_card]
  change Nat.card (UntruncatedStaircaseExponents n (adjoinOnes lam (n - lam.card))) = _
  rw [card_fullSizeStaircase _ (by rw [adjoinOnes_card, Nat.add_sub_of_le hk]),
    rowFactorialProduct_adjoinOnes]

theorem untruncated_krullDimension_allFields (K : Type*) [Field K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    ringKrullDim (UntruncatedRing K n lam) = (n - lam.card : ℕ) := by
  letI := untruncated_parameter_finite_allCoefficients K n lam hk
  letI := untruncated_parameter_faithful_allCoefficients K n lam hk
  rw [TauCeti.ringKrullDim_eq_of_isIntegral_of_faithfulSMul
    (R := ElementaryParameterRing K n lam)]
  change ringKrullDim (MvPolynomial (Fin (n - lam.card)) K) = _
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field, zero_add, Nat.card_fin]

theorem untruncated_isCohenMacaulay_atPrime_allFields (K : Type*) [Field K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (P : Ideal (UntruncatedRing K n lam)) [P.IsPrime] :
    Module.IsCohenMacaulay (Localization.AtPrime P) (Localization.AtPrime P) := by
  letI := untruncated_parameter_finite_allCoefficients K n lam hk
  letI := untruncated_parameter_flat_allCoefficients K n lam hk
  exact finiteFlat_isCohenMacaulay_atPrime
    (ElementaryParameterRing K n lam) (UntruncatedRing K n lam) P

/-- The all-characteristic algebraic conclusions of Corollary 6.5.  The
separate displayed basis above records the unchanged integral monomials. -/
theorem corollary_6_5_allFields (K : Type*) [Field K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    AlgebraicIndependent K (elementaryParameterClasses K n lam) ∧
      Module.Free (ElementaryParameterRing K n lam) (UntruncatedRing K n lam) ∧
      Module.Finite (ElementaryParameterRing K n lam) (UntruncatedRing K n lam) ∧
      Module.finrank (ElementaryParameterRing K n lam) (UntruncatedRing K n lam) =
        n.factorial / rowFactorialProduct lam ∧
      ringKrullDim (UntruncatedRing K n lam) = (n - lam.card : ℕ) ∧
      ∀ (P : Ideal (UntruncatedRing K n lam)) [P.IsPrime],
        Module.IsCohenMacaulay (Localization.AtPrime P) (Localization.AtPrime P) :=
  ⟨elementaryParameters_algebraicIndependent_allCoefficients K n lam hk,
    untruncated_parameter_free_allCoefficients K n lam hk,
    untruncated_parameter_finite_allCoefficients K n lam hk,
    untruncated_parameter_rank_allCoefficients K n lam hk,
    untruncated_krullDimension_allFields K n lam hk,
    untruncated_isCohenMacaulay_atPrime_allFields K n lam hk⟩

end HigherSpecht
end
end CanonicalSource55

section CanonicalSource56
/- Source: HigherSpecht/HomogeneousQuotientPieces.lean -/



/-!
# The genuine graded pieces of a homogeneous polynomial quotient

The degree-d piece is the image of homogeneous degree-d polynomials under
the actual quotient map.  The component operator descends because the ideal
is homogeneous.  A homogeneous basis of the quotient therefore restricts
to a basis of each actual graded piece; the grading is not defined from the
desired basis or from an attached formal degree.
-/

noncomputable section

open Module MvPolynomial TauCeti
open scoped Classical

namespace HigherSpecht

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type*} [CommRing R] {n : ℕ}

def homogeneousQuotientPiece (I : Ideal (PolynomialRing n R)) (d : ℕ) :
    Submodule R (PolynomialRing n R ⧸ I) :=
  (homogeneousSubmodule (Fin n) R d).map (Ideal.Quotient.mkₐ R I).toLinearMap

theorem mem_homogeneousQuotientPiece (I : Ideal (PolynomialRing n R)) (d : ℕ)
    (x : PolynomialRing n R ⧸ I) :
    x ∈ homogeneousQuotientPiece I d ↔
      ∃ p : PolynomialRing n R, p.IsHomogeneous d ∧ Ideal.Quotient.mk I p = x :=
  Iff.rfl

def homogeneousQuotientComponent (I : Ideal (PolynomialRing n R))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) R)) (d : ℕ) :
    (PolynomialRing n R ⧸ I) →ₗ[R] (PolynomialRing n R ⧸ I) :=
  (I.restrictScalars R).mapQ (I.restrictScalars R) (homogeneousComponent d)
    (fun p hp => homogeneousComponent_mem_of_mem hI hp d)

@[simp] theorem homogeneousQuotientComponent_mk
    (I : Ideal (PolynomialRing n R))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) R)) (d : ℕ)
    (p : PolynomialRing n R) :
    homogeneousQuotientComponent I hI d (Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk I (homogeneousComponent d p) := rfl

theorem homogeneousQuotientComponent_eq_self
    (I : Ideal (PolynomialRing n R))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) R)) (d : ℕ)
    {x : PolynomialRing n R ⧸ I} (hx : x ∈ homogeneousQuotientPiece I d) :
    homogeneousQuotientComponent I hI d x = x := by
  obtain ⟨p, hp, rfl⟩ := hx
  change homogeneousQuotientComponent I hI d (Ideal.Quotient.mk I p) = Ideal.Quotient.mk I p
  rw [homogeneousQuotientComponent_mk, homogeneousComponent_eq_self hp]

def homogeneousQuotientSubrepresentation (I : Ideal (PolynomialRing n R))
    (hperm : PermutationStable I) (d : ℕ) : Subrepresentation (quotientRepresentation I hperm) where
  toSubmodule := homogeneousQuotientPiece I d
  apply_mem_toSubmodule g x hx := by
    obtain ⟨p, hp, rfl⟩ := hx
    exact ⟨rename g p, hp.rename_isHomogeneous, rfl⟩

theorem homogeneousQuotientPiece_eq_span_basis
    (I : Ideal (PolynomialRing n R))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) R))
    {ι : Type*} (B : Basis ι R (PolynomialRing n R ⧸ I))
    (p : ι → PolynomialRing n R) (deg : ι → ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (deg i))
    (hB : ∀ i, B i = Ideal.Quotient.mk I (p i)) (d : ℕ) :
    homogeneousQuotientPiece I d =
      Submodule.span R (Set.range (fun i : {i : ι // deg i = d} => B i.val)) := by
  have hcomponent (i : ι) : homogeneousQuotientComponent I hI d (B i) =
      if deg i = d then B i else 0 := by
    rw [hB, homogeneousQuotientComponent_mk, homogeneousComponent_of_mem (hp i)]
    by_cases hi : deg i = d
    · simp only [hi, if_true]
    · simp only [Ne.symm hi, hi, if_false, map_zero]
  apply le_antisymm
  · intro x hx
    rw [← homogeneousQuotientComponent_eq_self I hI d hx,
      ← B.linearCombination_repr x]
    change homogeneousQuotientComponent I hI d
      (∑ i ∈ (B.repr x).support, B.repr x i • B i) ∈ _
    simp only [map_sum, map_smul, hcomponent]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    by_cases hd : deg i = d
    · rw [if_pos hd]
      exact Submodule.subset_span ⟨⟨i, hd⟩, rfl⟩
    · rw [if_neg hd]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply (mem_homogeneousQuotientPiece I d _).mpr
    refine ⟨p i.val, ?_, (hB i.val).symm⟩
    simpa only [i.property] using hp i.val

def homogeneousQuotientBasis
    (I : Ideal (PolynomialRing n R))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) R))
    {ι : Type*} (B : Basis ι R (PolynomialRing n R ⧸ I))
    (p : ι → PolynomialRing n R) (deg : ι → ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (deg i))
    (hB : ∀ i, B i = Ideal.Quotient.mk I (p i)) (d : ℕ) :
    Basis {i : ι // deg i = d} R (homogeneousQuotientPiece I d) :=
  (Basis.span (B.linearIndependent.comp Subtype.val Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (homogeneousQuotientPiece_eq_span_basis I hI B p deg hp hB d).symm)

@[simp] theorem homogeneousQuotientBasis_apply
    (I : Ideal (PolynomialRing n R))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) R))
    {ι : Type*} (B : Basis ι R (PolynomialRing n R ⧸ I))
    (p : ι → PolynomialRing n R) (deg : ι → ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (deg i))
    (hB : ∀ i, B i = Ideal.Quotient.mk I (p i)) (d : ℕ)
    (i : {i : ι // deg i = d}) :
    (homogeneousQuotientBasis I hI B p deg hp hB d i : PolynomialRing n R ⧸ I) = B i.val := by
  simp only [homogeneousQuotientBasis, Basis.map_apply, Basis.span_apply]
  rfl

end HigherSpecht
end
end CanonicalSource56

section CanonicalSource57
/- Source: HigherSpecht/IntegralHilbertFunctions.lean -/



/-!
# Degreewise integral monomial bases and field-independent Hilbert functions

The homogeneous pieces are the images of homogeneous polynomials under the
actual quotient map. The coefficient-ring basis statement and the
field-dimension statement are proved separately.

All ambient dimensions, the empty partition, and every positive finite
power bound in the manuscript's range are included. No characteristic
restriction is used.
-/

noncomputable section

open Module MvPolynomial TauCeti
open scoped Classical

namespace HigherSpecht

attribute [local instance] MvPolynomial.gradedAlgebra

theorem griffinIdeal_isHomogeneous {R : Type*} [CommRing R]
    {n : ℕ} {lam : YoungDiagram} (hk : lam.card ≤ n) (s : ℕ) :
    (griffinIdeal R n lam s).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) R) := by
  apply (untruncatedIdeal_isHomogeneous hk).sup
  apply Ideal.homogeneous_span
  rintro p ⟨j, rfl⟩
  exact ⟨s, by simpa only [MvPolynomial.mem_homogeneousSubmodule, one_mul] using (MvPolynomial.isHomogeneous_X R j).pow s⟩

abbrev GriffinMonomialDegreeIndex (n : ℕ) (lam : YoungDiagram) (s d : ℕ) :=
  {a : GriffinStaircaseExponents n lam s // a.val.degree = d}

instance finite_griffinMonomialDegreeIndex
    (n : ℕ) (lam : YoungDiagram) (s d : ℕ) :
    Finite (GriffinMonomialDegreeIndex n lam s d) :=
  Finite.of_injective
    (fun a : GriffinMonomialDegreeIndex n lam s d =>
      fun i : Fin n =>
        (⟨a.val.val i,
          Nat.lt_succ_of_le (by
            have h := Finsupp.le_degree i a.val.val
            rwa [a.property] at h)⟩ : Fin (d + 1)))
    (by
      intro a b h
      apply Subtype.ext
      apply Subtype.ext
      ext i
      exact congrArg Fin.val (congrFun h i))

instance fintype_griffinMonomialDegreeIndex
    (n : ℕ) (lam : YoungDiagram) (s d : ℕ) :
    Fintype (GriffinMonomialDegreeIndex n lam s d) := Fintype.ofFinite _

def griffinMonomialDegreeBasis (R : Type*) [CommRing R] [Nontrivial R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) (d : ℕ) :
    Basis (GriffinMonomialDegreeIndex n lam s d) R
      (homogeneousQuotientPiece (griffinIdeal R n lam s) d) :=
  homogeneousQuotientBasis (griffinIdeal R n lam s)
    (griffinIdeal_isHomogeneous hk s)
    (griffinStandardMonomialBasis hk s hs hheight)
    (fun a => MvPolynomial.monomial a.val 1) (fun a => a.val.degree)
    (fun _ => MvPolynomial.isHomogeneous_monomial 1 rfl)
    (griffinStandardMonomialBasis_apply (R := R) hk s hs hheight) d

@[simp] theorem griffinMonomialDegreeBasis_apply
    (R : Type*) [CommRing R] [Nontrivial R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) (d : ℕ)
    (a : GriffinMonomialDegreeIndex n lam s d) :
    (griffinMonomialDegreeBasis R n lam hk s hs hheight d a :
        GriffinRing R n lam s) =
      Ideal.Quotient.mk (griffinIdeal R n lam s)
        (MvPolynomial.monomial a.val.val 1) := by
  rw [griffinMonomialDegreeBasis, homogeneousQuotientBasis_apply,
    griffinStandardMonomialBasis_apply]

/-- The printed integral normal-form assertion restricted to any actual
homogeneous degree. Empty shapes and zero variables are included. -/
theorem lemma_6_4_griffin_degree_integral
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) (d : ℕ) :
    ∃ B : Basis (GriffinMonomialDegreeIndex n lam s d) ℤ
        (homogeneousQuotientPiece (griffinIdeal ℤ n lam s) d),
      ∀ a, (B a : GriffinRing ℤ n lam s) =
        Ideal.Quotient.mk (griffinIdeal ℤ n lam s)
          (MvPolynomial.monomial a.val.val 1) :=
  ⟨griffinMonomialDegreeBasis ℤ n lam hk s hs hheight d,
    griffinMonomialDegreeBasis_apply ℤ n lam hk s hs hheight d⟩

def griffinHilbertFunction (K : Type*) [Field K]
    (n : ℕ) (lam : YoungDiagram) (s d : ℕ) : ℕ :=
  Module.finrank K (homogeneousQuotientPiece (griffinIdeal K n lam s) d)

theorem griffinHilbertFunction_eq_card (K : Type*) [Field K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) (d : ℕ) :
    griffinHilbertFunction K n lam s d =
      Nat.card (GriffinMonomialDegreeIndex n lam s d) := by
  rw [griffinHilbertFunction, Module.finrank_eq_card_basis
    (griffinMonomialDegreeBasis K n lam hk s hs hheight d),
    Nat.card_eq_fintype_card]

/-- The finite-s Hilbert function, degree by degree, is independent of the
coefficient field, including positive and small characteristic. -/
theorem griffinHilbertFunction_independent_field
    (K L : Type*) [Field K] [Field L]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) (d : ℕ) :
    griffinHilbertFunction K n lam s d =
      griffinHilbertFunction L n lam s d := by
  rw [griffinHilbertFunction_eq_card K n lam hk s hs hheight d,
    griffinHilbertFunction_eq_card L n lam hk s hs hheight d]

end HigherSpecht
end
end CanonicalSource57

section CanonicalSource58
/- Source: HigherSpecht/SpecialFiberEligibility.lean -/



/-!
# The exact eligibility assertion of Proposition 6.3

The cyclic output is the actual terminating output already used in the
paper's basis index.  The proof combines its genuine prefix formula with
the elementary dominance fact about adjoining one-box rows.  In particular
it neither changes the statistic nor assumes a special-fiber basis count.
-/

noncomputable section

open TauCeti Finset

namespace HigherSpecht

theorem rowPrefixSum_eq_card_of_height_le (nu : YoungDiagram) {r : ℕ}
    (hr : nu.colLen 0 ≤ r) : rowPrefixSum nu r = nu.card :=
  (YoungDiagram.card_eq_sum_range_rowLen nu hr).symm

theorem rowPrefixSum_mono_diagram {mu nu : YoungDiagram} (h : mu ≤ nu) (r : ℕ) :
    rowPrefixSum mu r ≤ rowPrefixSum nu r := by
  rw [rowPrefixSum, rowPrefixSum,
    YoungDiagram.sum_range_rowLen_eq_card_filter_fst,
    YoungDiagram.sum_range_rowLen_eq_card_filter_fst]
  apply Finset.card_le_card
  intro c hc
  exact Finset.mem_filter.mpr ⟨h (Finset.mem_filter.mp hc).1,
    (Finset.mem_filter.mp hc).2⟩

theorem rowPrefixSum_adjoinOnes_of_le_height (lam : YoungDiagram) (m : ℕ)
    {r : ℕ} (hr : r ≤ lam.colLen 0) :
    rowPrefixSum (adjoinOnes lam m) r = rowPrefixSum lam r := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [adjoinOnes_rowLen, if_pos ((Finset.mem_range.mp hj).trans_le hr)]

theorem rowPrefixSum_adjoinOnes_le (lam : YoungDiagram) (m : ℕ)
    {r : ℕ} (hr : lam.colLen 0 ≤ r) :
    rowPrefixSum (adjoinOnes lam m) r ≤ lam.card + (r - lam.colLen 0) := by
  let h := lam.colLen 0
  have hr' : h + (r - h) = r := Nat.add_sub_of_le hr
  conv_lhs => rw [← hr', rowPrefixSum, Finset.sum_range_add]
  have hfirst : (∑ j ∈ Finset.range h, (adjoinOnes lam m).rowLen j) = lam.card := by
    change rowPrefixSum (adjoinOnes lam m) h = _
    rw [rowPrefixSum_adjoinOnes_of_le_height lam m le_rfl,
      rowPrefixSum_eq_card_of_height_le lam le_rfl]
  rw [hfirst]
  apply Nat.add_le_add_left
  calc
    (∑ j ∈ Finset.range (r - h), (adjoinOnes lam m).rowLen (h + j)) ≤
        ∑ _j ∈ Finset.range (r - h), (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [adjoinOnes_rowLen, if_neg (by dsimp [h]; omega)]
      split_ifs <;> omega
    _ = r - h := by simp

theorem rowPrefixSum_add_one_per_row (nu : YoungDiagram) {h r : ℕ}
    (hhr : h ≤ r) (hr : r ≤ nu.colLen 0) :
    rowPrefixSum nu h + (r - h) ≤ rowPrefixSum nu r := by
  have heq : h + (r - h) = r := Nat.add_sub_of_le hhr
  conv_rhs => rw [← heq, rowPrefixSum, Finset.sum_range_add]
  apply Nat.add_le_add_left
  calc
    r - h = ∑ _j ∈ Finset.range (r - h), (1 : ℕ) := by simp
    _ ≤ ∑ j ∈ Finset.range (r - h), nu.rowLen (h + j) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : h + j < nu.colLen 0 := by
        have := Finset.mem_range.mp hj
        omega
      exact YoungDiagram.mem_iff_lt_rowLen.mp
        (YoungDiagram.mem_iff_lt_colLen.mpr hj')

/-- Among partitions of `|lam| + m`, dominating `lam` is equivalent
to dominating `lam` with `m` one-box rows appended. -/
theorem dominates_adjoinOnes_iff {nu lam : YoungDiagram} {m : ℕ}
    (hcard : nu.card = lam.card + m) :
    Dominates nu (adjoinOnes lam m) ↔ Dominates nu lam := by
  constructor
  · intro h r
    exact (rowPrefixSum_mono_diagram (le_adjoinOnes lam m) r).trans (h r)
  · intro h r
    change rowPrefixSum (adjoinOnes lam m) r ≤ rowPrefixSum nu r
    by_cases hr : r ≤ lam.colLen 0
    · rw [rowPrefixSum_adjoinOnes_of_le_height lam m hr]
      exact h r
    · have hlr : lam.colLen 0 ≤ r := Nat.le_of_not_ge hr
      by_cases hnu : nu.colLen 0 ≤ r
      · rw [rowPrefixSum_eq_card_of_height_le nu hnu, hcard]
        simpa only [adjoinOnes_card] using rowPrefixSum_le_card (adjoinOnes lam m) r
      · have hbase : lam.card ≤ rowPrefixSum nu (lam.colLen 0) := by
          have hh : rowPrefixSum lam (lam.colLen 0) ≤ rowPrefixSum nu (lam.colLen 0) :=
            h (lam.colLen 0)
          rwa [rowPrefixSum_eq_card_of_height_le lam le_rfl] at hh
        exact (rowPrefixSum_adjoinOnes_le lam m hlr).trans
          ((Nat.add_le_add_right hbase _).trans
            (rowPrefixSum_add_one_per_row nu hlr (Nat.le_of_not_ge hnu)))

/-- Proposition 6.3's exact equivalence for each standard tableau of the
full ambient size. -/
theorem proposition_6_3_eligibility {mu : YoungDiagram}
    (S : StandardYoungTableau mu) (lam : YoungDiagram) (hk : lam.card ≤ mu.card) :
    CatDominates (prefixTableau S lam.card hk) lam ↔
      CatDominates S (adjoinOnes lam (mu.card - lam.card)) := by
  rw [catDominates_prefix_iff, ← columnInsertion_dominates_iff]
  exact (dominates_adjoinOnes_iff (m := mu.card - lam.card) (by
    rw [catTableauOutput_card S (columnInsertion_catTableauOutput S),
      Nat.add_sub_of_le hk])).symm

/-- The integral and arbitrary-coefficient ideal identity and the literal
tableau equivalence together give the two algebraic assertions of
Proposition 6.3. -/
theorem proposition_6_3 (R : Type*) [CommRing R] (lam : YoungDiagram) (m : ℕ) :
    untruncatedIdeal R (lam.card + m) (adjoinOnes lam m) =
        untruncatedIdeal R (lam.card + m) lam ⊔
          elementaryParameterIdeal (R := R) (lam.card + m) m ∧
      ∀ (mu : YoungDiagram) (hmu : mu.card = lam.card + m)
        (S : StandardYoungTableau mu),
        CatDominates (prefixTableau S lam.card (by omega)) lam ↔
          CatDominates S (adjoinOnes lam m) := by
  refine ⟨specialFiberIdeal_eq lam m, ?_⟩
  intro mu hmu S
  have h := proposition_6_3_eligibility S lam (by omega)
  simpa only [hmu, Nat.add_sub_cancel_left] using h

end HigherSpecht
end
end CanonicalSource58

section CanonicalSource59
/- Source: HigherSpecht/UntruncatedGradedPieces.lean -/



/-!
# Actual degree pieces and their complete-copy indices

The basis is obtained by restricting the established quotient basis to its
computed homogeneous degree.  Its second indexing presents each eligible
left tableau and multiplier once, with every standard right tableau in that
copy.  These two index sets are connected by a literal equivalence.
-/

noncomputable section

open Module MvPolynomial TauCeti
open scoped Classical

namespace HigherSpecht

def UntruncatedVectorIndex.degree {n : ℕ} {lam : YoungDiagram} {hk : lam.card ≤ n}
    (i : UntruncatedVectorIndex n lam hk) : ℕ :=
  cochargeDegree i.base.val.left + i.multiplier.card

def untruncatedVectorPolynomial {R : Type*} [CommRing R]
    {n : ℕ} {lam : YoungDiagram} {hk : lam.card ≤ n}
    (i : UntruncatedVectorIndex n lam hk) : PolynomialRing n R :=
  pairPolynomial i.base.val * elementaryMultiplier n (n - lam.card) i.multiplier.rowLen

theorem untruncatedVectorPolynomial_isHomogeneous {R : Type*} [CommRing R]
    {n : ℕ} {lam : YoungDiagram} {hk : lam.card ≤ n}
    (i : UntruncatedVectorIndex n lam hk) :
    (untruncatedVectorPolynomial (R := R) i).IsHomogeneous i.degree :=
  (pairPolynomial_isHomogeneous i.base.val).mul
    (elementaryMultiplier_isHomogeneous n (n - lam.card) i.multiplier i.multiplier_length)

abbrev UntruncatedDegreeVectorIndex (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (d : ℕ) :=
  {i : UntruncatedVectorIndex n lam hk // i.degree = d}

abbrev UntruncatedDegreeCopyIndex (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (d : ℕ) :=
  {i : UnboundedHarmonicIndex n // i.eligible lam hk ∧ i.degree = d}

instance finite_untruncatedDegreeCopyIndex (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (d : ℕ) : Finite (UntruncatedDegreeCopyIndex n lam hk d) := by
  letI := (finite_unboundedHarmonic_degree n d).fintype
  exact Finite.of_injective
    (fun i : UntruncatedDegreeCopyIndex n lam hk d =>
      (⟨i.val, i.property.2⟩ : {i : UnboundedHarmonicIndex n // i.degree = d}))
    (fun i j h => Subtype.ext (congrArg
      (fun z : {i : UnboundedHarmonicIndex n // i.degree = d} => z.val) h))

instance fintype_untruncatedDegreeCopyIndex (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (d : ℕ) : Fintype (UntruncatedDegreeCopyIndex n lam hk d) :=
  Fintype.ofFinite _

abbrev UntruncatedDegreeCopyVectorIndex (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (d : ℕ) :=
  Σ i : UntruncatedDegreeCopyIndex n lam hk d,
    StandardYoungTableau (YoungDiagram.ofPartition i.val.part)

def untruncatedDegreeCopyVector {n : ℕ} {lam : YoungDiagram}
    {hk : lam.card ≤ n} {d : ℕ}
    (z : UntruncatedDegreeCopyVectorIndex n lam hk d) :
    UntruncatedDegreeVectorIndex n lam hk d :=
  ⟨{ base := ⟨(standardPairPartitionEquiv n).symm
        ⟨z.1.val.part, z.1.val.left, z.2⟩, z.1.property.1.2⟩
     multiplier := z.1.val.multiplier
     multiplier_length := z.1.property.1.1 }, z.1.property.2⟩

theorem untruncatedDegreeCopyVector_injective (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (d : ℕ) :
    Function.Injective (untruncatedDegreeCopyVector (n := n) (lam := lam) (hk := hk) (d := d)) := by
  rintro ⟨i, T⟩ ⟨j, U⟩ h
  have hp := congrArg (fun z : UntruncatedDegreeVectorIndex n lam hk d =>
    standardPairPartitionEquiv n z.val.base.val) h
  simp only [untruncatedDegreeCopyVector, Equiv.apply_symm_apply] at hp
  obtain hpart : i.val.part = j.val.part := (Sigma.mk.inj_iff.mp hp).1
  have heta := congrArg (fun z : UntruncatedDegreeVectorIndex n lam hk d => z.val.multiplier) h
  rcases i with ⟨⟨part, S, eta, hlen⟩, hi⟩
  rcases j with ⟨⟨other, S', eta', hlen'⟩, hj⟩
  dsimp only at hpart
  dsimp only [untruncatedDegreeCopyVector] at heta
  subst other
  subst eta'
  have hpair : (S, T) = (S', U) := eq_of_heq (Sigma.mk.inj_iff.mp hp).2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
  rfl

theorem untruncatedDegreeCopyVector_surjective (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (d : ℕ) :
    Function.Surjective (untruncatedDegreeCopyVector (n := n) (lam := lam) (hk := hk) (d := d)) := by
  rintro ⟨⟨⟨P, heligible⟩, eta, hlength⟩, hdegree⟩
  obtain ⟨⟨part, S, T⟩, rfl⟩ := (standardPairPartitionEquiv n).symm.surjective P
  let i : UnboundedHarmonicIndex n :=
    { part := part
      left := S
      multiplier := eta
      multiplier_length := hlength.trans (Nat.sub_le n lam.card) }
  refine ⟨⟨⟨i, ⟨⟨hlength, heligible⟩, hdegree⟩⟩, T⟩, rfl⟩

def untruncatedDegreeCopyVectorEquiv (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (d : ℕ) :
    UntruncatedDegreeCopyVectorIndex n lam hk d ≃ UntruncatedDegreeVectorIndex n lam hk d :=
  Equiv.ofBijective untruncatedDegreeCopyVector
    ⟨untruncatedDegreeCopyVector_injective n lam hk d,
      untruncatedDegreeCopyVector_surjective n lam hk d⟩

instance finite_untruncatedDegreeVectorIndex (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (d : ℕ) : Finite (UntruncatedDegreeVectorIndex n lam hk d) :=
  Finite.of_equiv _ (untruncatedDegreeCopyVectorEquiv n lam hk d)

def untruncatedGradedPiece (K : Type*) [CommRing K] (n : ℕ)
    (lam : YoungDiagram) (d : ℕ) : Subrepresentation (untruncatedRepresentation K n lam) :=
  homogeneousQuotientSubrepresentation (untruncatedIdeal K n lam)
    (permutationStable_untruncatedIdeal lam) d

def untruncatedDegreeBasis (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (d : ℕ) :
    Basis (UntruncatedDegreeVectorIndex n lam hk d) K
      (untruncatedGradedPiece K n lam d).toSubmodule :=
  homogeneousQuotientBasis (untruncatedIdeal K n lam) (untruncatedIdeal_isHomogeneous hk)
    (untruncatedPrescribedVectorBasis K n lam hk) untruncatedVectorPolynomial
    UntruncatedVectorIndex.degree (untruncatedVectorPolynomial_isHomogeneous (R := K))
    (fun i => (untruncatedPrescribedVectorBasis_apply K n lam hk i).trans
      (show untruncatedVectorFamily K n lam hk i =
        Ideal.Quotient.mk (untruncatedIdeal K n lam) (untruncatedVectorPolynomial i) from rfl)) d

@[simp] theorem untruncatedDegreeBasis_apply (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (d : ℕ)
    (i : UntruncatedDegreeVectorIndex n lam hk d) :
    (untruncatedDegreeBasis K n lam hk d i : UntruncatedRing K n lam) =
      untruncatedVectorFamily K n lam hk i.val := by
  exact (homogeneousQuotientBasis_apply (untruncatedIdeal K n lam)
    (untruncatedIdeal_isHomogeneous hk) (untruncatedPrescribedVectorBasis K n lam hk)
    untruncatedVectorPolynomial UntruncatedVectorIndex.degree
    (untruncatedVectorPolynomial_isHomogeneous (R := K))
    (fun j => (untruncatedPrescribedVectorBasis_apply K n lam hk j).trans
      (show untruncatedVectorFamily K n lam hk j =
        Ideal.Quotient.mk (untruncatedIdeal K n lam) (untruncatedVectorPolynomial j) from rfl))
    d i).trans (untruncatedPrescribedVectorBasis_apply K n lam hk i.val)

def untruncatedDegreeCopyBasis (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (d : ℕ) :
    Basis (UntruncatedDegreeCopyVectorIndex n lam hk d) K
      (untruncatedGradedPiece K n lam d).toSubmodule :=
  (untruncatedDegreeBasis K n lam hk d).reindex
    (untruncatedDegreeCopyVectorEquiv n lam hk d).symm

@[simp] theorem untruncatedDegreeCopyBasis_apply (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (d : ℕ)
    (i : UntruncatedDegreeCopyVectorIndex n lam hk d) :
    (untruncatedDegreeCopyBasis K n lam hk d i : UntruncatedRing K n lam) =
      Ideal.Quotient.mk (untruncatedIdeal K n lam)
        (rename (finCongr (YoungDiagram.card_ofPartition i.1.val.part))
          (higherSpechtPolynomial i.1.val.left i.2) *
          elementaryMultiplier n (n - lam.card) i.1.val.multiplier.rowLen) := by
  rw [untruncatedDegreeCopyBasis, Basis.reindex_apply, untruncatedDegreeBasis_apply]
  change untruncatedVectorFamily K n lam hk (untruncatedDegreeCopyVector i).val = _
  rfl

theorem finiteDimensional_untruncatedGradedPiece (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (d : ℕ) :
    FiniteDimensional K (untruncatedGradedPiece K n lam d).toSubmodule :=
  Module.Finite.of_basis (untruncatedDegreeCopyBasis K n lam hk d)

end HigherSpecht
end
end CanonicalSource59

section CanonicalSource60
/- Source: HigherSpecht/CharacterFromCopies.lean -/



/-!
# Character additivity for an actual complete-copy basis

The hypotheses are the literal basis vectors and intertwining maps.  The
proof computes the diagonal coefficients of the actual linear operators;
no representation is identified only from its dimension.
-/

noncomputable section

open Module
open scoped Classical

namespace HigherSpecht

theorem basis_repr_intertwiner_same_copy
    {K G J : Type*} [Field K] [Monoid G] [Fintype J]
    {V : J → Type*} [∀ j, AddCommGroup (V j)] [∀ j, Module K (V j)]
    {κ : J → Type*} [∀ j, Fintype (κ j)]
    {M : Type*} [AddCommGroup M] [Module K M]
    (sigma : ∀ j, Representation K G (V j)) (rho : Representation K G M)
    (A : ∀ j, Basis (κ j) K (V j)) (B : Basis (Σ j, κ j) K M)
    (f : ∀ j, (sigma j).IntertwiningMap rho)
    (hf : ∀ j a, f j (A j a) = B ⟨j, a⟩)
    (j : J) (a : κ j) (v : V j) :
    B.repr (f j v) ⟨j, a⟩ = (A j).repr v a := by
  conv_lhs => rw [← (A j).sum_repr v, map_sum]
  simp only [map_smul, hf, map_sum, Basis.repr_self, Finsupp.smul_single,
    smul_eq_mul, mul_one, Finsupp.finsetSum_apply]
  change (∑ c : κ j,
    (Finsupp.single (⟨j, c⟩ : Σ j, κ j) ((A j).repr v c)) ⟨j, a⟩) = _
  calc
    (∑ c : κ j, (Finsupp.single (⟨j, c⟩ : Σ j, κ j) ((A j).repr v c)) ⟨j, a⟩) =
        (Finsupp.single (⟨j, a⟩ : Σ j, κ j) ((A j).repr v a)) ⟨j, a⟩ := by
      apply Finset.sum_eq_single a
      · intro c hc hca
        exact Finsupp.single_eq_of_ne' (fun h => hca (eq_of_heq (Sigma.mk.inj_iff.mp h).2))
      · intro ha
        exact (ha (Finset.mem_univ a)).elim
    _ = (A j).repr v a := Finsupp.single_eq_same

theorem character_eq_sum_of_intertwining_basis
    {K G J : Type*} [Field K] [Monoid G] [Fintype J]
    {V : J → Type*} [∀ j, AddCommGroup (V j)] [∀ j, Module K (V j)]
    {κ : J → Type*} [∀ j, Fintype (κ j)]
    {M : Type*} [AddCommGroup M] [Module K M]
    (sigma : ∀ j, Representation K G (V j)) (rho : Representation K G M)
    (A : ∀ j, Basis (κ j) K (V j)) (B : Basis (Σ j, κ j) K M)
    (f : ∀ j, (sigma j).IntertwiningMap rho)
    (hf : ∀ j a, f j (A j a) = B ⟨j, a⟩) (g : G) :
    rho.character g = ∑ j, (sigma j).character g := by
  letI : FiniteDimensional K M := Module.Finite.of_basis B
  letI (j : J) : FiniteDimensional K (V j) := Module.Finite.of_basis (A j)
  rw [Representation.character, LinearMap.trace_eq_matrix_trace K B]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  rw [Representation.character, LinearMap.trace_eq_matrix_trace K (A j)]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [← hf j a]
  exact (congrArg (fun v : M => B.repr v ⟨j, a⟩)
    (Representation.IntertwiningMap.isIntertwining (sigma j) rho (f j) g (A j a)).symm).trans
      (basis_repr_intertwiner_same_copy sigma rho A B f hf j a (sigma j g (A j a)))

end HigherSpecht
end
end CanonicalSource60

section CanonicalSource61
/- Source: HigherSpecht/UntruncatedGradedCharacters.lean -/



/-!
# The characters of the actual graded untruncated quotient

Each eligible left-tableau/multiplier pair gives the literal equivariant
map from an ordinary Specht module.  The homogeneous quotient basis proves
that these maps form a complete-copy basis in each degree.  Character
additivity and the verified Frobenius characteristic then give the Schur
coefficient formula for the actual degree piece.
-/

noncomputable section

open Module MvPolynomial TauCeti
open scoped Classical TensorProduct

namespace HigherSpecht

def untruncatedBaseChangeRepresentationEquiv
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (n : ℕ) (lam : YoungDiagram) :
    (Representation.baseChange S (untruncatedRepresentation R n lam)).Equiv
      (untruncatedRepresentation S n lam) := by
  refine Representation.Equiv.mk (untruncatedBaseChangeEquiv R S n lam).toLinearEquiv ?_
  intro g
  apply TensorProduct.AlgebraTensorModule.ext (R := R)
  intro a x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [LinearMap.comp_apply, Representation.baseChange_apply, LinearMap.baseChange_tmul,
    untruncatedRepresentation, quotientRepresentation_mk, untruncatedBaseChangeEquiv,
    AlgEquiv.toLinearEquiv_toLinearMap, AlgEquiv.toLinearMap_apply,
    LinearEquiv.coe_coe, AlgEquiv.coe_toLinearEquiv,
    AlgEquiv.toLinearEquiv_apply, polynomialQuotientBaseChangeEquiv_tmul,
    MvPolynomial.map_rename, map_smul]

def partitionUntruncatedIntertwiner {n : ℕ} (lam : YoungDiagram)
    (i : UnboundedHarmonicIndex n) :
    Representation.IntertwiningMap (spechtModule i.part).ρ (untruncatedRepresentation ℚ n lam) :=
  (quotientProjectionIntertwiner (untruncatedIdeal ℚ n lam)
    (permutationStable_untruncatedIdeal lam)).comp
    ((symmetricMultiplicationIntertwiner
      (elementaryMultiplier n (n - lam.card) i.multiplier.rowLen)
      (elementaryMultiplier_isSymmetric n (n - lam.card) i.multiplier.rowLen)).comp
        (partitionHigherSpechtIntertwiner i.part i.left))

@[simp] theorem partitionUntruncatedIntertwiner_standard {n : ℕ}
    (lam : YoungDiagram) (i : UnboundedHarmonicIndex n)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)) :
    partitionUntruncatedIntertwiner lam i (spechtModuleStandardBasis i.part T) =
      Ideal.Quotient.mk (untruncatedIdeal ℚ n lam)
        (rename (finCongr (YoungDiagram.card_ofPartition i.part))
          (higherSpechtPolynomial i.left T) *
          elementaryMultiplier n (n - lam.card) i.multiplier.rowLen) := by
  change Ideal.Quotient.mk (untruncatedIdeal ℚ n lam)
    (partitionHigherSpechtIntertwiner i.part i.left (spechtModuleStandardBasis i.part T) *
      elementaryMultiplier n (n - lam.card) i.multiplier.rowLen) = _
  rw [partitionHigherSpechtIntertwiner_standardBasis]

private theorem fdRep_cast_intertwiner_basis_apply
    {G ι M : Type*} [Monoid G] [AddCommGroup M] [Module ℂ M]
    (rho : Representation ℂ G M) {A B : FDRep ℂ G} (h : A = B)
    (f : Representation.IntertwiningMap A.ρ rho) (b : Basis ι ℂ A) (i : ι) :
    (cast (congrArg (fun V : FDRep ℂ G => Representation.IntertwiningMap V.ρ rho) h) f)
      ((cast (congrArg (fun V : FDRep ℂ G => Basis ι ℂ V) h) b) i) = f (b i) := by
  cases h
  rfl

def complexSpechtStandardBasis {n : ℕ} (part : n.Partition) :
    Basis (StandardYoungTableau (YoungDiagram.ofPartition part)) ℂ (spechtModuleℂ part) :=
  cast (congrArg (fun V : FDRep ℂ (Equiv.Perm (Fin n)) =>
    Basis (StandardYoungTableau (YoungDiagram.ofPartition part)) ℂ V)
    (spechtModuleℂ_def part).symm) ((spechtModuleStandardBasis part).baseChange ℂ)

def partitionUntruncatedComplexIntertwiner {n : ℕ} (lam : YoungDiagram)
    (i : UnboundedHarmonicIndex n) :
    Representation.IntertwiningMap (spechtModuleℂ i.part).ρ (untruncatedRepresentation ℂ n lam) :=
  cast (congrArg (fun V : FDRep ℂ (Equiv.Perm (Fin n)) =>
    Representation.IntertwiningMap V.ρ (untruncatedRepresentation ℂ n lam))
    (spechtModuleℂ_def i.part).symm)
    ((untruncatedBaseChangeRepresentationEquiv ℚ ℂ n lam).toIntertwiningMap.comp
      ((partitionUntruncatedIntertwiner lam i).baseChange ℂ))

@[simp] theorem partitionUntruncatedComplexIntertwiner_standard {n : ℕ}
    (lam : YoungDiagram) (i : UnboundedHarmonicIndex n)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.part)) :
    partitionUntruncatedComplexIntertwiner lam i (complexSpechtStandardBasis i.part T) =
      Ideal.Quotient.mk (untruncatedIdeal ℂ n lam)
        (rename (finCongr (YoungDiagram.card_ofPartition i.part))
          (higherSpechtPolynomial i.left T) *
          elementaryMultiplier n (n - lam.card) i.multiplier.rowLen) := by
  unfold partitionUntruncatedComplexIntertwiner complexSpechtStandardBasis
  rw [fdRep_cast_intertwiner_basis_apply (untruncatedRepresentation ℂ n lam)
    (spechtModuleℂ_def i.part).symm]
  change untruncatedBaseChangeEquiv ℚ ℂ n lam
    ((partitionUntruncatedIntertwiner lam i).baseChange ℂ
      ((spechtModuleStandardBasis i.part).baseChange ℂ T)) = _
  rw [Basis.baseChange_apply, Representation.IntertwiningMap.baseChange_tmul]
  refine (congrArg (fun x : UntruncatedRing ℚ n lam =>
    untruncatedBaseChangeEquiv ℚ ℂ n lam ((1 : ℂ) ⊗ₜ[ℚ] x))
      (partitionUntruncatedIntertwiner_standard lam i T)).trans ?_
  rw [untruncatedBaseChangeEquiv, polynomialQuotientBaseChangeEquiv_tmul]
  simp only [one_smul, map_mul, MvPolynomial.map_rename, map_higherSpechtPolynomial,
    map_elementaryMultiplier]

theorem partitionUntruncatedComplexIntertwiner_mem_degree
    {n : ℕ} (lam : YoungDiagram) (hk : lam.card ≤ n) (d : ℕ)
    (i : UntruncatedDegreeCopyIndex n lam hk d) (v : spechtModuleℂ i.val.part) :
    partitionUntruncatedComplexIntertwiner lam i.val v ∈
      (untruncatedGradedPiece ℂ n lam d).toSubmodule := by
  rw [← (complexSpechtStandardBasis i.val.part).sum_repr v, map_sum]
  apply Submodule.sum_mem
  intro T _
  rw [map_smul, partitionUntruncatedComplexIntertwiner_standard]
  apply Submodule.smul_mem
  rw [← untruncatedDegreeCopyBasis_apply ℂ n lam hk d ⟨i, T⟩]
  exact (untruncatedDegreeCopyBasis ℂ n lam hk d ⟨i, T⟩).property

def untruncatedDegreeSpechtMap {n : ℕ} (lam : YoungDiagram)
    (hk : lam.card ≤ n) (d : ℕ) (i : UntruncatedDegreeCopyIndex n lam hk d) :
    Representation.IntertwiningMap (spechtModuleℂ i.val.part).ρ
      (untruncatedGradedPiece ℂ n lam d).toRepresentation :=
  (partitionUntruncatedComplexIntertwiner lam i.val).codRestrict
    (untruncatedGradedPiece ℂ n lam d)
    (partitionUntruncatedComplexIntertwiner_mem_degree lam hk d i)

@[simp] theorem untruncatedDegreeSpechtMap_standard {n : ℕ}
    (lam : YoungDiagram) (hk : lam.card ≤ n) (d : ℕ)
    (i : UntruncatedDegreeCopyIndex n lam hk d)
    (T : StandardYoungTableau (YoungDiagram.ofPartition i.val.part)) :
    untruncatedDegreeSpechtMap lam hk d i (complexSpechtStandardBasis i.val.part T) =
      untruncatedDegreeCopyBasis ℂ n lam hk d ⟨i, T⟩ := by
  apply Subtype.ext
  rw [untruncatedDegreeCopyBasis_apply, untruncatedDegreeSpechtMap,
    Representation.IntertwiningMap.codRestrict_apply_coe]
  exact partitionUntruncatedComplexIntertwiner_standard lam i.val T

theorem character_untruncatedGradedPiece (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (d : ℕ) (g : Equiv.Perm (Fin n)) :
    (untruncatedGradedPiece ℂ n lam d).toRepresentation.character g =
      ∑ i : UntruncatedDegreeCopyIndex n lam hk d,
        Representation.character (spechtModuleℂ i.val.part).ρ g := by
  exact character_eq_sum_of_intertwining_basis
    (fun i : UntruncatedDegreeCopyIndex n lam hk d => (spechtModuleℂ i.val.part).ρ)
    (untruncatedGradedPiece ℂ n lam d).toRepresentation
    (fun i => complexSpechtStandardBasis i.val.part)
    (untruncatedDegreeCopyBasis ℂ n lam hk d)
    (untruncatedDegreeSpechtMap lam hk d)
    (untruncatedDegreeSpechtMap_standard lam hk d) g

def untruncatedFrobeniusCoefficient (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (d : ℕ) : MvPolynomial (Fin n) ℂ :=
  letI := finiteDimensional_untruncatedGradedPiece ℂ n lam hk d
  (frobeniusCharacteristic n n le_rfl
    (ClassFunction.ofCharacter (untruncatedGradedPiece ℂ n lam d).toRepresentation) :
      symmetricHomogeneousSubmodule (Fin n) ℂ n)

theorem untruncatedFrobeniusCoefficient_eq (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (d : ℕ) :
    untruncatedFrobeniusCoefficient n lam hk d =
      ∑ i : UntruncatedDegreeCopyIndex n lam hk d,
        schurPoly (Fin n) ℂ i.val.part := by
  letI := finiteDimensional_untruncatedGradedPiece ℂ n lam hk d
  have hchar : ClassFunction.ofCharacter
      (untruncatedGradedPiece ℂ n lam d).toRepresentation =
      ∑ i : UntruncatedDegreeCopyIndex n lam hk d,
        ClassFunction.ofCharacter (spechtModuleℂ i.val.part).ρ := by
    apply Subtype.ext
    funext g
    simp only [Submodule.coe_sum, ClassFunction.ofCharacter_apply, Finset.sum_apply]
    exact character_untruncatedGradedPiece n lam hk d g
  simp only [untruncatedFrobeniusCoefficient, hchar, map_sum, Submodule.coe_sum,
    frobeniusCharacteristic_spechtCharacter]

end HigherSpecht
end
end CanonicalSource61

section CanonicalSource62
/- Source: HigherSpecht/ElementaryWeights.lean -/



/-!
# The common elementary-parameter weight

Parameter number `i + 1` has degree `i + 1`.  The finitely supported
weight used for the grading equals the literal finite sum used for the
power-series coefficients.  Both constructions use this one definition.
-/

noncomputable section

open scoped BigOperators

namespace HigherSpecht

def elementaryWeight {m : ℕ} (a : Fin m →₀ ℕ) : ℕ :=
  Finsupp.weight (fun i : Fin m => i.val + 1) a

theorem elementaryWeight_eq_sum {m : ℕ} (a : Fin m →₀ ℕ) :
    elementaryWeight a = ∑ i : Fin m, (i.val + 1) * a i := by
  simp only [elementaryWeight, Finsupp.weight_eq_sum, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]

end HigherSpecht
end
end CanonicalSource62

section CanonicalSource63
/- Source: HigherSpecht/WeightedParameterSeries.lean -/



/-!
# The weighted elementary-parameter denominator

The coefficient of the actual product of geometric series counts exponent
vectors of weighted degree d.  Consecutive row differences give the exact
degree-preserving bijection to partitions of size d and length at most m.
The product is exhibited as a unit with inverse the polynomial
`∏ j=1..m, (1-X^j)`, over any commutative coefficient ring.
-/

noncomputable section

open Module MvPolynomial TauCeti Finset
open scoped Classical PowerSeries

namespace HigherSpecht

abbrev WeightedParameterExponents (m d : ℕ) :=
  {a : Fin m →₀ ℕ // elementaryWeight a = d}

theorem weightedParameterExponents_le {m d : ℕ}
    (a : WeightedParameterExponents m d) (i : Fin m) : a.val i ≤ d := by
  have hi : (i.val + 1) * a.val i ≤ elementaryWeight a.val := by
    rw [elementaryWeight_eq_sum]
    exact Finset.single_le_sum (f := fun j : Fin m => (j.val + 1) * a.val j)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have hw : 1 ≤ i.val + 1 := Nat.succ_le_succ (Nat.zero_le _)
  rw [a.property] at hi
  nlinarith

instance finite_weightedParameterExponents (m d : ℕ) : Finite (WeightedParameterExponents m d) :=
  Finite.of_injective
    (fun a : WeightedParameterExponents m d =>
      fun i : Fin m => (⟨a.val i, Nat.lt_succ_of_le (weightedParameterExponents_le a i)⟩ : Fin (d + 1)))
    (by intro a b h; apply Subtype.ext; ext i; exact congrArg Fin.val (congrFun h i))

instance fintype_weightedParameterExponents (m d : ℕ) : Fintype (WeightedParameterExponents m d) :=
  Fintype.ofFinite _

def weightedAntidiagonalCode {m : ℕ} (a : Fin m →₀ ℕ) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (i.val + 1) * a i)

@[simp] theorem weightedAntidiagonalCode_apply {m : ℕ} (a : Fin m →₀ ℕ) (i : Fin m) :
    weightedAntidiagonalCode a i = (i.val + 1) * a i := rfl

def divisibleAntidiagonal (m d : ℕ) : Finset (Fin m →₀ ℕ) :=
  (Finset.finsuppAntidiag Finset.univ d).filter (fun a => ∀ i, i.val + 1 ∣ a i)

def weightedAntidiagonalEquiv (m d : ℕ) :
    WeightedParameterExponents m d ≃ ↥(divisibleAntidiagonal m d) where
  toFun a := ⟨weightedAntidiagonalCode a.val, by
    simp only [divisibleAntidiagonal, Finset.mem_filter, Finset.mem_finsuppAntidiag,
      weightedAntidiagonalCode_apply, Finset.subset_univ, and_true]
    exact ⟨by
      change (∑ i : Fin m, (i.val + 1) * a.val i) = d
      simpa only [elementaryWeight_eq_sum] using a.property,
      fun i => dvd_mul_right _ _⟩⟩
  invFun b := ⟨Finsupp.equivFunOnFinite.symm (fun i => b.val i / (i.val + 1)), by
    have hb := Finset.mem_filter.mp b.property
    have hs := (Finset.mem_finsuppAntidiag.mp hb.1).1
    rw [elementaryWeight_eq_sum]
    change ∑ i : Fin m, (i.val + 1) * (b.val i / (i.val + 1)) = d
    simpa only [Nat.mul_div_cancel' (hb.2 _)] using hs⟩
  left_inv a := by
    apply Subtype.ext
    ext i
    exact Nat.mul_div_cancel_left _ (Nat.succ_pos _)
  right_inv b := by
    apply Subtype.ext
    ext i
    exact Nat.mul_div_cancel' ((Finset.mem_filter.mp b.property).2 i)

def weightedGeometricSeries (R : Type*) [CommRing R] (w : ℕ) : PowerSeries R :=
  PowerSeries.mk (fun d => if w ∣ d then 1 else 0)

@[simp] theorem coeff_weightedGeometricSeries (R : Type*) [CommRing R] (w d : ℕ) :
    PowerSeries.coeff d (weightedGeometricSeries R w) = if w ∣ d then 1 else 0 :=
  PowerSeries.coeff_mk _ _

theorem weightedGeometricSeries_mul_one_sub (R : Type*) [CommRing R]
    (w : ℕ) (hw : 0 < w) :
    weightedGeometricSeries R w * (1 - PowerSeries.X ^ w) = 1 := by
  apply PowerSeries.ext
  intro d
  rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_mul_X_pow',
    coeff_weightedGeometricSeries, coeff_weightedGeometricSeries, PowerSeries.coeff_one]
  by_cases hd : w ≤ d
  · rw [if_pos hd]
    have hdiv : w ∣ d - w ↔ w ∣ d := Nat.dvd_sub_iff_left hd (dvd_refl w)
    have hd0 : d ≠ 0 := Nat.ne_of_gt (hw.trans_le hd)
    simp only [hdiv, sub_self, if_neg hd0]
  · have hsmall : d < w := Nat.lt_of_not_ge hd
    have hdiv : w ∣ d ↔ d = 0 := by
      constructor
      · intro h
        by_contra hne
        exact (Nat.not_le_of_lt hsmall) (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) h)
      · rintro rfl; exact dvd_zero w
    simp only [if_neg hd, sub_zero, hdiv]

def weightedGeometricUnit (R : Type*) [CommRing R] (w : ℕ) (hw : 0 < w) :
    (PowerSeries R)ˣ where
  val := weightedGeometricSeries R w
  inv := 1 - PowerSeries.X ^ w
  val_inv := weightedGeometricSeries_mul_one_sub R w hw
  inv_val := by rw [mul_comm]; exact weightedGeometricSeries_mul_one_sub R w hw

def elementaryParameterSeriesUnit (R : Type*) [CommRing R] (m : ℕ) : (PowerSeries R)ˣ :=
  ∏ i : Fin m, weightedGeometricUnit R (i.val + 1) (Nat.succ_pos _)

@[simp] theorem elementaryParameterSeriesUnit_inv (R : Type*) [CommRing R] (m : ℕ) :
    ((elementaryParameterSeriesUnit R m)⁻¹).val =
      ∏ i : Fin m, (1 - (PowerSeries.X : PowerSeries R) ^ (i.val + 1)) := by
  rw [elementaryParameterSeriesUnit, ← Finset.prod_inv_distrib, Units.coe_prod]
  rfl

theorem coeff_elementaryParameterSeriesUnit (R : Type*) [CommRing R] (m d : ℕ) :
    PowerSeries.coeff d (elementaryParameterSeriesUnit R m).val =
      (Nat.card (WeightedParameterExponents m d) : R) := by
  have hprod (a : Fin m →₀ ℕ) :
      (∏ i : Fin m, (if i.val + 1 ∣ a i then 1 else 0 : R)) =
        if ∀ i : Fin m, i.val + 1 ∣ a i then 1 else 0 := by
    by_cases ha : ∀ i : Fin m, i.val + 1 ∣ a i
    · rw [if_pos ha]
      exact Finset.prod_eq_one (fun i _ => if_pos (ha i))
    · rw [if_neg ha]
      obtain ⟨i, hi⟩ := not_forall.mp ha
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact if_neg hi
  rw [elementaryParameterSeriesUnit, Units.coe_prod, PowerSeries.coeff_prod]
  simp only [weightedGeometricUnit, coeff_weightedGeometricSeries, hprod]
  rw [← Finset.sum_filter]
  change (∑ _a ∈ divisibleAntidiagonal m d, (1 : R)) = _
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (weightedAntidiagonalEquiv m d).symm

theorem partitionFromDifferences_card {m : ℕ} (a : Fin m →₀ ℕ) :
    (partitionFromDifferences a).card = elementaryWeight a := by
  have h := partition_weighted_differences_eq_card (partitionFromDifferences a)
    (partitionFromDifferences_height a)
  rw [← Fin.sum_univ_eq_sum_range] at h
  simpa only [partitionFromDifferences_difference, elementaryWeight_eq_sum] using h.symm

abbrev BoundedLengthPartitionDegree (m d : ℕ) :=
  {eta : YoungDiagram // eta.colLen 0 ≤ m ∧ eta.card = d}

def partitionDegreeDifferenceEquiv (m d : ℕ) :
    BoundedLengthPartitionDegree m d ≃ WeightedParameterExponents m d where
  toFun eta := ⟨partitionDifferences m eta.val, by
    rw [← partitionFromDifferences_card, partitionFromDifferences_partitionDifferences m eta.val eta.property.1]
    exact eta.property.2⟩
  invFun a := ⟨partitionFromDifferences a.val,
    partitionFromDifferences_height a.val, (partitionFromDifferences_card a.val).trans a.property⟩
  left_inv eta := Subtype.ext (partitionFromDifferences_partitionDifferences m eta.val eta.property.1)
  right_inv a := by
    apply Subtype.ext
    ext i
    rw [partitionDifferences_apply, partitionFromDifferences_difference]

instance finite_boundedLengthPartitionDegree (m d : ℕ) : Finite (BoundedLengthPartitionDegree m d) :=
  Finite.of_equiv _ (partitionDegreeDifferenceEquiv m d).symm

instance fintype_boundedLengthPartitionDegree (m d : ℕ) : Fintype (BoundedLengthPartitionDegree m d) :=
  Fintype.ofFinite _

theorem coeff_elementaryParameterSeriesUnit_partitions (R : Type*) [CommRing R] (m d : ℕ) :
    PowerSeries.coeff d (elementaryParameterSeriesUnit R m).val =
      (Nat.card (BoundedLengthPartitionDegree m d) : R) := by
  rw [coeff_elementaryParameterSeriesUnit,
    Nat.card_congr (partitionDegreeDifferenceEquiv m d)]

end HigherSpecht
end
end CanonicalSource63

section CanonicalSource64
/- Source: HigherSpecht/UntruncatedFrobeniusSeries.lean -/



/-!
# The full Frobenius series in Theorem 6.1

The series on the left is defined from the character of each actual graded
piece of the quotient.  The finite numerator uses precisely the eligible
standard left tableaux.  The denominator is the actual product
`∏ j=1..n-|lambda|, (1-X^j)`.  An explicit inverse unit establishes the
equivalence between the coefficient formula and the printed quotient.
Using n symmetric-function variables loses no information in degree n:
the imported Frobenius characteristic is a linear equivalence there.
-/

noncomputable section

open Module MvPolynomial TauCeti
open scoped Classical PowerSeries

namespace HigherSpecht

abbrev UntruncatedLeftTableauIndex (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) :=
  {z : (Σ part : n.Partition, StandardYoungTableau (YoungDiagram.ofPartition part)) //
    CatDominates (prefixTableau z.2 lam.card
      (by simpa only [YoungDiagram.card_ofPartition] using hk)) lam}

instance fintype_untruncatedLeftTableauIndex (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) : Fintype (UntruncatedLeftTableauIndex n lam hk) :=
  Fintype.ofFinite _

abbrev UntruncatedDegreeTableauPartitionIndex (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (d : ℕ) :=
  Σ b : {b : UntruncatedLeftTableauIndex n lam hk // cochargeDegree b.val.2 ≤ d},
    BoundedLengthPartitionDegree (n - lam.card) (d - cochargeDegree b.val.val.2)

def untruncatedDegreeCopyPartitionEquiv (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (d : ℕ) :
    UntruncatedDegreeCopyIndex n lam hk d ≃
      UntruncatedDegreeTableauPartitionIndex n lam hk d where
  toFun i :=
    ⟨⟨⟨⟨i.val.part, i.val.left⟩, i.property.1.2⟩, by
        change cochargeDegree i.val.left ≤ d
        have hi := i.property.2
        change cochargeDegree i.val.left + i.val.multiplier.card = d at hi
        omega⟩,
      ⟨i.val.multiplier, i.property.1.1, by
        change i.val.multiplier.card = d - cochargeDegree i.val.left
        have hi := i.property.2
        change cochargeDegree i.val.left + i.val.multiplier.card = d at hi
        omega⟩⟩
  invFun z :=
    ⟨{ part := z.1.val.val.1
       left := z.1.val.val.2
       multiplier := z.2.val
       multiplier_length := z.2.property.1.trans (Nat.sub_le _ _) },
      ⟨⟨z.2.property.1, z.1.val.property⟩, by
        change cochargeDegree z.1.val.val.2 + z.2.val.card = d
        rw [z.2.property.2, Nat.add_sub_of_le z.1.property]⟩⟩
  left_inv i := by
    rcases i with ⟨⟨part, S, eta, hlen⟩, hi⟩
    rfl
  right_inv z := by
    rcases z with ⟨⟨⟨⟨part, S⟩, hS⟩, hdegree⟩, ⟨eta, heta⟩⟩
    rfl

theorem untruncatedFrobeniusCoefficient_by_left_tableau
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (d : ℕ) :
    untruncatedFrobeniusCoefficient n lam hk d =
      ∑ b : UntruncatedLeftTableauIndex n lam hk,
        if cochargeDegree b.val.2 ≤ d then
          schurPoly (Fin n) ℂ b.val.1 *
            (Nat.card (BoundedLengthPartitionDegree (n - lam.card)
              (d - cochargeDegree b.val.2)) : MvPolynomial (Fin n) ℂ)
        else 0 := by
  rw [untruncatedFrobeniusCoefficient_eq]
  rw [← Equiv.sum_comp (untruncatedDegreeCopyPartitionEquiv n lam hk d).symm
    (fun i : UntruncatedDegreeCopyIndex n lam hk d => schurPoly (Fin n) ℂ i.val.part)]
  simp only [untruncatedDegreeCopyPartitionEquiv, Fintype.sum_sigma]
  change (∑ b : {b : UntruncatedLeftTableauIndex n lam hk // cochargeDegree b.val.2 ≤ d},
    ∑ _eta : BoundedLengthPartitionDegree (n - lam.card)
      (d - cochargeDegree b.val.val.2), schurPoly (Fin n) ℂ b.val.val.1) = _
  have hsum :
      (∑ b : {b : UntruncatedLeftTableauIndex n lam hk // cochargeDegree b.val.2 ≤ d},
        ∑ _eta : BoundedLengthPartitionDegree (n - lam.card)
          (d - cochargeDegree b.val.val.2), schurPoly (Fin n) ℂ b.val.val.1) =
      ∑ b : {b : UntruncatedLeftTableauIndex n lam hk // cochargeDegree b.val.2 ≤ d},
        schurPoly (Fin n) ℂ b.val.val.1 *
          (Nat.card (BoundedLengthPartitionDegree (n - lam.card)
            (d - cochargeDegree b.val.val.2)) : MvPolynomial (Fin n) ℂ) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Nat.card_eq_fintype_card, mul_comm]
  rw [hsum, ← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp)
    (fun b : UntruncatedLeftTableauIndex n lam hk =>
      schurPoly (Fin n) ℂ b.val.1 *
        (Nat.card (BoundedLengthPartitionDegree (n - lam.card)
          (d - cochargeDegree b.val.2)) : MvPolynomial (Fin n) ℂ))).symm

def untruncatedFrobeniusSeries (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    PowerSeries (MvPolynomial (Fin n) ℂ) :=
  PowerSeries.mk (untruncatedFrobeniusCoefficient n lam hk)

def untruncatedFrobeniusNumerator (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    PowerSeries (MvPolynomial (Fin n) ℂ) :=
  ∑ b : UntruncatedLeftTableauIndex n lam hk,
    PowerSeries.C (schurPoly (Fin n) ℂ b.val.1) *
      PowerSeries.X ^ cochargeDegree b.val.2

def elementaryFrobeniusDenominator (n m : ℕ) : PowerSeries (MvPolynomial (Fin n) ℂ) :=
  ∏ i : Fin m, (1 - PowerSeries.X ^ (i.val + 1))

theorem untruncatedFrobeniusSeries_eq_numerator_mul_inverse
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    untruncatedFrobeniusSeries n lam hk =
      untruncatedFrobeniusNumerator n lam hk *
        (elementaryParameterSeriesUnit (MvPolynomial (Fin n) ℂ) (n - lam.card)).val := by
  apply PowerSeries.ext
  intro d
  rw [untruncatedFrobeniusSeries, PowerSeries.coeff_mk,
    untruncatedFrobeniusCoefficient_by_left_tableau,
    untruncatedFrobeniusNumerator, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  by_cases hb : cochargeDegree b.val.2 ≤ d
  · rw [if_pos hb, if_pos hb, coeff_elementaryParameterSeriesUnit_partitions]
  · rw [if_neg hb, if_neg hb, mul_zero]

/-- The printed Frobenius formula, as an equality after multiplication by
its explicitly invertible formal-series denominator. -/
theorem theorem_6_1_frobenius_series (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    untruncatedFrobeniusSeries n lam hk *
        elementaryFrobeniusDenominator n (n - lam.card) =
      untruncatedFrobeniusNumerator n lam hk := by
  rw [untruncatedFrobeniusSeries_eq_numerator_mul_inverse, elementaryFrobeniusDenominator,
    ← elementaryParameterSeriesUnit_inv (MvPolynomial (Fin n) ℂ) (n - lam.card),
    mul_assoc, Units.mul_inv, mul_one]

theorem elementaryFrobeniusDenominator_isUnit (n m : ℕ) :
    IsUnit (elementaryFrobeniusDenominator n m) := by
  exact ⟨(elementaryParameterSeriesUnit (MvPolynomial (Fin n) ℂ) m)⁻¹,
    elementaryParameterSeriesUnit_inv _ _⟩

end HigherSpecht
end
end CanonicalSource64

section CanonicalSource65
/- Source: HigherSpecht/SpecialFiberFrobenius.lean -/



/-!
# The flat lifting and Frobenius clauses of Proposition 6.3

The special fiber is the original quotient in the same ambient variables,
for the diagram obtained by adjoining `n - |lam|` one-box rows. Its series
is defined by the character of its actual homogeneous quotient pieces.
The index equivalence below keeps the standard tableau itself unchanged.
It therefore identifies the finite Frobenius numerator with that genuine
special-fiber series, including the empty shape and zero-parameter cases.

The companion basis is obtained by the actual zero-parameter base change.
The formula on every original polynomial verifies that its vectors are the
unchanged higher Specht representatives. No count, freeness, or Frobenius
identity is a premise of the final statements.
-/

noncomputable section

open Module MvPolynomial TauCeti
open scoped Classical PowerSeries TensorProduct

namespace HigherSpecht

theorem specialFiberShape_card (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    (adjoinOnes lam (n - lam.card)).card = n := by
  rw [adjoinOnes_card, Nat.add_sub_of_le hk]

theorem specialFiber_leftTableau_eligible_iff
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (z : Σ part : n.Partition, StandardYoungTableau (YoungDiagram.ofPartition part)) :
    CatDominates (prefixTableau z.2 lam.card
        (by simpa only [YoungDiagram.card_ofPartition] using hk)) lam ↔
      CatDominates (prefixTableau z.2 (adjoinOnes lam (n - lam.card)).card
        (by simpa only [YoungDiagram.card_ofPartition] using
          (specialFiberShape_card n lam hk).le))
        (adjoinOnes lam (n - lam.card)) := by
  let mu := adjoinOnes lam (n - lam.card)
  have hmu : mu.card = n := specialFiberShape_card n lam hk
  have hleft := proposition_6_3_eligibility z.2 lam
    (by simpa only [YoungDiagram.card_ofPartition] using hk)
  have hright := proposition_6_3_eligibility z.2 mu
    (by simpa only [YoungDiagram.card_ofPartition] using hmu.le)
  have hleft' : CatDominates (prefixTableau z.2 lam.card
      (by simpa only [YoungDiagram.card_ofPartition] using hk)) lam ↔
      CatDominates z.2 mu := by
    simpa only [YoungDiagram.card_ofPartition, mu] using hleft
  have hright' : CatDominates (prefixTableau z.2 mu.card
      (by simpa only [YoungDiagram.card_ofPartition] using hmu.le)) mu ↔
      CatDominates z.2 mu := by
    have hzero : adjoinOnes mu 0 = mu := by
      apply YoungDiagram.rowLen_injective
      funext r
      by_cases hr : r < mu.colLen 0
      · simp only [adjoinOnes_rowLen, if_pos hr]
      · simp only [adjoinOnes_rowLen, if_neg hr, add_zero,
          YoungDiagram.rowLen_eq_zero_of_colLen_le (Nat.le_of_not_gt hr)]
    simpa only [YoungDiagram.card_ofPartition, hmu, Nat.sub_self, hzero] using hright
  exact hleft'.trans hright'.symm

/-- The actual left tableau, its shape, and its cocharge are unchanged. -/
def specialFiberLeftTableauIndexEquiv (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) :
    UntruncatedLeftTableauIndex n lam hk ≃
      UntruncatedLeftTableauIndex n (adjoinOnes lam (n - lam.card))
        (specialFiberShape_card n lam hk).le where
  toFun i := ⟨i.val, (specialFiber_leftTableau_eligible_iff n lam hk i.val).mp i.property⟩
  invFun i := ⟨i.val, (specialFiber_leftTableau_eligible_iff n lam hk i.val).mpr i.property⟩
  left_inv i := Subtype.ext rfl
  right_inv i := Subtype.ext rfl

theorem untruncatedFrobeniusNumerator_eq_specialFiber
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    untruncatedFrobeniusNumerator n lam hk =
      untruncatedFrobeniusNumerator n (adjoinOnes lam (n - lam.card))
        (specialFiberShape_card n lam hk).le := by
  exact Equiv.sum_comp (specialFiberLeftTableauIndexEquiv n lam hk)
    (fun b : UntruncatedLeftTableauIndex n (adjoinOnes lam (n - lam.card))
        (specialFiberShape_card n lam hk).le =>
      PowerSeries.C (schurPoly (Fin n) ℂ b.val.1) *
        PowerSeries.X ^ cochargeDegree b.val.2)

theorem specialFiberFrobeniusSeries_eq_numerator
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    untruncatedFrobeniusSeries n (adjoinOnes lam (n - lam.card))
        (specialFiberShape_card n lam hk).le =
      untruncatedFrobeniusNumerator n (adjoinOnes lam (n - lam.card))
        (specialFiberShape_card n lam hk).le := by
  have h := theorem_6_1_frobenius_series n (adjoinOnes lam (n - lam.card))
    (specialFiberShape_card n lam hk).le
  have hden : elementaryFrobeniusDenominator n
      (n - (adjoinOnes lam (n - lam.card)).card) = 1 := by
    rw [specialFiberShape_card n lam hk, Nat.sub_self]
    simp only [elementaryFrobeniusDenominator, Finset.univ_eq_empty,
      Finset.prod_empty]
  simpa only [hden, mul_one] using h

/-- The missing printed Frobenius clause of Proposition 6.3, with the
series on both sides taken from the actual quotient representations.
The denominator is a unit by `elementaryFrobeniusDenominator_isUnit`, so
this is rigorously equivalent to the displayed quotient formula. -/
theorem proposition_6_3_frobenius (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    untruncatedFrobeniusSeries n lam hk *
        elementaryFrobeniusDenominator n (n - lam.card) =
      untruncatedFrobeniusSeries n (adjoinOnes lam (n - lam.card))
        (specialFiberShape_card n lam hk).le := by
  rw [theorem_6_1_frobenius_series n lam hk,
    untruncatedFrobeniusNumerator_eq_specialFiber n lam hk,
    specialFiberFrobeniusSeries_eq_numerator n lam hk]

/-- The printed quotient formula itself, using the explicit inverse unit
whose inverse is the product of the displayed elementary denominator factors. -/
theorem proposition_6_3_frobenius_quotient
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    untruncatedFrobeniusSeries n lam hk =
      untruncatedFrobeniusSeries n (adjoinOnes lam (n - lam.card))
          (specialFiberShape_card n lam hk).le *
        (elementaryParameterSeriesUnit (MvPolynomial (Fin n) ℂ) (n - lam.card)).val := by
  rw [untruncatedFrobeniusSeries_eq_numerator_mul_inverse n lam hk,
    untruncatedFrobeniusNumerator_eq_specialFiber n lam hk,
    specialFiberFrobeniusSeries_eq_numerator n lam hk]

/-- A separate literal target keeps the full parameter range visible. -/
def SpecialFiberFrobeniusTarget : Prop :=
  ∀ (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n),
    untruncatedFrobeniusSeries n lam hk *
        elementaryFrobeniusDenominator n (n - lam.card) =
      untruncatedFrobeniusSeries n (adjoinOnes lam (n - lam.card))
        (specialFiberShape_card n lam hk).le

theorem proposition_6_3_frobenius_target : SpecialFiberFrobeniusTarget :=
  proposition_6_3_frobenius

variable (K : Type*) [Field K]

@[simp] theorem zeroParameterBaseChangeEquiv_one_tmul_X
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (i : Fin n) :
    letI : Algebra (ElementaryParameterRing K n lam) K := zeroParameterAlgebra K n lam
    letI : Module (ElementaryParameterRing K n lam) (UntruncatedRing K n lam) :=
      @Algebra.toModule (ElementaryParameterRing K n lam) (UntruncatedRing K n lam)
        _ _ (untruncatedParameterAlgebra K n lam)
    zeroParameterBaseChangeEquiv K n lam hk
        ((1 : K) ⊗ₜ[ElementaryParameterRing K n lam]
          Ideal.Quotient.mk (untruncatedIdeal K n lam) (MvPolynomial.X i)) =
      Ideal.Quotient.mk (untruncatedIdeal K n (adjoinOnes lam (n - lam.card)))
        (MvPolynomial.X i) := by
  letI : Algebra (ElementaryParameterRing K n lam) K := zeroParameterAlgebra K n lam
  letI : Module (ElementaryParameterRing K n lam) (UntruncatedRing K n lam) :=
    @Algebra.toModule (ElementaryParameterRing K n lam) (UntruncatedRing K n lam)
      _ _ (untruncatedParameterAlgebra K n lam)
  simp only [zeroParameterBaseChangeEquiv, AlgEquiv.trans_apply,
    elementaryParameterBaseChangeEquiv_one_tmul_X, Ideal.quotientEquivAlgOfEq_mk]

theorem zeroParameterBaseChangeEquiv_one_tmul_mk
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (p : PolynomialRing n K) :
    letI : Algebra (ElementaryParameterRing K n lam) K := zeroParameterAlgebra K n lam
    letI : Module (ElementaryParameterRing K n lam) (UntruncatedRing K n lam) :=
      @Algebra.toModule (ElementaryParameterRing K n lam) (UntruncatedRing K n lam)
        _ _ (untruncatedParameterAlgebra K n lam)
    zeroParameterBaseChangeEquiv K n lam hk
        ((1 : K) ⊗ₜ[ElementaryParameterRing K n lam]
          Ideal.Quotient.mk (untruncatedIdeal K n lam) p) =
      Ideal.Quotient.mk (untruncatedIdeal K n (adjoinOnes lam (n - lam.card))) p := by
  letI : Algebra (ElementaryParameterRing K n lam) K := zeroParameterAlgebra K n lam
  letI : Module (ElementaryParameterRing K n lam) (UntruncatedRing K n lam) :=
    @Algebra.toModule (ElementaryParameterRing K n lam) (UntruncatedRing K n lam)
      _ _ (untruncatedParameterAlgebra K n lam)
  letI : IsScalarTower K (ElementaryParameterRing K n lam) K :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      exact (MvPolynomial.constantCoeff_C (Fin (n - lam.card)) a).symm)
  let J : UntruncatedRing K n lam →ₐ[K]
      K ⊗[ElementaryParameterRing K n lam] UntruncatedRing K n lam :=
    (Algebra.TensorProduct.includeRight : UntruncatedRing K n lam →ₐ[
      ElementaryParameterRing K n lam]
      K ⊗[ElementaryParameterRing K n lam] UntruncatedRing K n lam).restrictScalars K
  have h : (zeroParameterBaseChangeEquiv K n lam hk).toAlgHom.comp
      (J.comp (Ideal.Quotient.mkₐ K (untruncatedIdeal K n lam))) =
      Ideal.Quotient.mkₐ K (untruncatedIdeal K n (adjoinOnes lam (n - lam.card))) := by
    ext i
    simp only [AlgHom.comp_apply, J, AlgHom.restrictScalars_apply,
      Algebra.TensorProduct.includeRight_apply, AlgEquiv.coe_toAlgHom,
      Ideal.Quotient.mkₐ_eq_mk, zeroParameterBaseChangeEquiv_one_tmul_X]
  exact AlgHom.congr_fun h p

/-- The literal higher Specht free basis specialized at the actual origin. -/
def specialFiberPrescribedLiftBasis [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Basis (UntruncatedIndex n lam hk) K
      (UntruncatedRing K n (adjoinOnes lam (n - lam.card))) := by
  letI : Algebra (ElementaryParameterRing K n lam) K := zeroParameterAlgebra K n lam
  letI : Module (ElementaryParameterRing K n lam) (UntruncatedRing K n lam) :=
    @Algebra.toModule (ElementaryParameterRing K n lam) (UntruncatedRing K n lam)
      _ _ (untruncatedParameterAlgebra K n lam)
  exact ((untruncatedPrescribedParameterBasis K n lam hk).baseChange K).map
    (zeroParameterBaseChangeEquiv K n lam hk).toLinearEquiv

@[simp] theorem specialFiberPrescribedLiftBasis_apply [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (i : UntruncatedIndex n lam hk) :
    specialFiberPrescribedLiftBasis K n lam hk i =
      Ideal.Quotient.mk (untruncatedIdeal K n (adjoinOnes lam (n - lam.card)))
        (pairPolynomial i.val) := by
  letI : Algebra (ElementaryParameterRing K n lam) K := zeroParameterAlgebra K n lam
  letI : Module (ElementaryParameterRing K n lam) (UntruncatedRing K n lam) :=
    @Algebra.toModule (ElementaryParameterRing K n lam) (UntruncatedRing K n lam)
      _ _ (untruncatedParameterAlgebra K n lam)
  simp only [specialFiberPrescribedLiftBasis, Basis.map_apply, Basis.baseChange_apply,
    AlgEquiv.toLinearEquiv_apply, untruncatedPrescribedParameterBasis_apply,
    untruncatedFamily, zeroParameterBaseChangeEquiv_one_tmul_mk]

/-- The printed flat-lifting clause: the original elementary-parameter
module is flat, and its basis specializes to precisely the unchanged
higher Specht representatives in the Springer special fiber. -/
theorem proposition_6_3_flat_lifting [CharZero K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) :
    Module.Flat (ElementaryParameterRing K n lam) (UntruncatedRing K n lam) ∧
      IsSpecifiedBasis (R := K)
        (fun i : UntruncatedIndex n lam hk =>
          Ideal.Quotient.mk (untruncatedIdeal K n (adjoinOnes lam (n - lam.card)))
            (pairPolynomial i.val)) :=
  ⟨untruncated_parameter_flat K n lam hk,
    ⟨specialFiberPrescribedLiftBasis K n lam hk,
      specialFiberPrescribedLiftBasis_apply K n lam hk⟩⟩

end HigherSpecht
end
end CanonicalSource65
