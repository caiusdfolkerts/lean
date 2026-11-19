module

public import ToricPower.SerrePairingCochains
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.FiniteSupport.Basic

/-!
# The supertrace pairing and the signed Hom differential

The only reindexing below is translation of an integer degree. Finite
support follows from the bounded target complex. This permits an
arbitrary unbounded complex in the other argument, without exchanging
an infinite product with algebraic duality.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex
open CochainComplex.HomComplex
open scoped BigOperators

namespace ToricPower.SerrePairing

universe u v r
variable (k : Type r) [Field k]
variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear k A]
variable (T : A ⥤ A) [T.Additive]
variable (J : CochainComplex A ℤ) (pairing : ∀ q, CodomainPairing k T (J.X q))
variable (E : CochainComplex A ℤ)

def cochainPairingTerm (n : ℤ) (f : Cochain E J n)
    (g : Cochain (mappedCochainComplex T J) E (-n)) (q : ℤ) : k :=
  q.negOnePow • (pairing q).equiv (E.X (q - n))
    (f.v (q - n) q (by omega)) (g.v q (q - n) (by omega))

theorem cochainPairingTerm_zero (n : ℤ) (f : Cochain E J n)
    (g : Cochain (mappedCochainComplex T J) E (-n)) (q : ℤ) (zero : IsZero (J.X q)) :
    cochainPairingTerm k T J pairing E n f g q = 0 := by
  unfold cochainPairingTerm
  rw [zero.eq_of_tgt (f.v (q - n) q (by omega)) 0, map_zero, LinearMap.zero_apply,
    smul_zero]

theorem finiteCochainPairingEquiv_eq_finsum
    (support : Finset ℤ) (outside : ∀ q, q ∉ support → IsZero (J.X q)) (n : ℤ)
    (f : Cochain E J n) (g : Cochain (mappedCochainComplex T J) E (-n)) :
    finiteCochainPairingEquiv k T J pairing E support outside n f g =
      ∑ᶠ q, cochainPairingTerm k T J pairing E n f g q := by
  rw [finiteCochainPairingEquiv_apply]
  change (∑ q : support, cochainPairingTerm k T J pairing E n f g q) = _
  rw [Finset.sum_coe_sort]
  symm
  apply finsum_eq_sum_of_support_subset
  intro q hq
  by_contra absent
  exact hq (cochainPairingTerm_zero k T J pairing E n f g q (outside q absent))

def differentialPairingJTerm (n : ℤ) (f : Cochain E J n)
    (g : Cochain (mappedCochainComplex T J) E (-(n + 1))) (q : ℤ) : k :=
  q.negOnePow • (pairing q).equiv (E.X (q - n))
    (f.v (q - n) q (by omega))
    (T.map (J.d q (q + 1)) ≫ g.v (q + 1) (q - n) (by omega))

def differentialPairingETerm (n : ℤ) (f : Cochain E J n)
    (g : Cochain (mappedCochainComplex T J) E (-(n + 1))) (q : ℤ) : k :=
  q.negOnePow • (pairing q).equiv (E.X (q - n))
    (f.v (q - n) q (by omega))
    (g.v q (q - (n + 1)) (by omega) ≫ E.d (q - (n + 1)) (q - n))

theorem differentialPairingJTerm_finite
    (support : Finset ℤ) (outside : ∀ q, q ∉ support → IsZero (J.X q))
    (n : ℤ) (f : Cochain E J n)
    (g : Cochain (mappedCochainComplex T J) E (-(n + 1))) :
    (differentialPairingJTerm k T J pairing E n f g).HasFiniteSupport := by
  apply support.finite_toSet.subset
  intro q hq
  by_contra absent
  apply hq
  unfold differentialPairingJTerm
  rw [(outside q absent).eq_of_tgt (f.v (q - n) q (by omega)) 0,
    map_zero, LinearMap.zero_apply, smul_zero]

theorem differentialPairingETerm_finite
    (support : Finset ℤ) (outside : ∀ q, q ∉ support → IsZero (J.X q))
    (n : ℤ) (f : Cochain E J n)
    (g : Cochain (mappedCochainComplex T J) E (-(n + 1))) :
    (differentialPairingETerm k T J pairing E n f g).HasFiniteSupport := by
  apply support.finite_toSet.subset
  intro q hq
  by_contra absent
  apply hq
  unfold differentialPairingETerm
  rw [(outside q absent).eq_of_tgt (f.v (q - n) q (by omega)) 0,
    map_zero, LinearMap.zero_apply, smul_zero]

private theorem jPairingValue_congr (n : ℤ) (f : Cochain E J n)
    (g : Cochain (mappedCochainComplex T J) E (-(n + 1)))
    {p p' q r r' : ℤ} {h₁ : p + n = q} {h₁' : p' + n = q}
    {h₂ : r + -(n + 1) = p} {h₂' : r' + -(n + 1) = p'}
    (hp : p = p') (hr : r = r') :
    (pairing q).equiv (E.X p) (f.v p q h₁)
      (T.map (J.d q r) ≫ g.v r p h₂) =
    (pairing q).equiv (E.X p') (f.v p' q h₁')
      (T.map (J.d q r') ≫ g.v r' p' h₂') := by
  cases hp
  cases hr
  rfl

theorem differentialPairingTerm_left
    (compatible : ∀ p q, Compatible k (pairing p) (pairing q) (J.d p q))
    (n : ℤ) (f : Cochain E J n)
    (g : Cochain (mappedCochainComplex T J) E (-(n + 1))) (q : ℤ) :
    cochainPairingTerm k T J pairing E (n + 1) (δ n (n + 1) f) g q =
      -differentialPairingJTerm k T J pairing E n f g (q - 1) +
        (n + 1).negOnePow • differentialPairingETerm k T J pairing E n f g q := by
  unfold cochainPairingTerm
  rw [δ_v n (n + 1) rfl f (q - (n + 1)) q (by omega) (q - 1) (q - n) rfl (by omega)]
  simp only [map_add, map_zsmul_unit, LinearMap.add_apply, LinearMap.smul_apply, smul_add]
  have first : q.negOnePow • (pairing q).equiv (E.X (q - (n + 1)))
      (f.v (q - (n + 1)) (q - 1) (by omega) ≫ J.d (q - 1) q)
      (g.v q (q - (n + 1)) (by omega)) =
      -differentialPairingJTerm k T J pairing E n f g (q - 1) := by
    rw [compatible]
    have index : q - (n + 1) = q - 1 - n := by omega
    have sign : q.negOnePow = -(q - 1).negOnePow := by
      simpa only [sub_add_cancel] using Int.negOnePow_succ (q - 1)
    simp only [differentialPairingJTerm, sign, Units.neg_smul]
    apply congrArg (fun x : k => -((q - 1).negOnePow • x))
    exact jPairingValue_congr k T J pairing E n f g index (by omega)
  have second : q.negOnePow • (pairing q).equiv (E.X (q - (n + 1)))
      ((n + 1).negOnePow • (E.d (q - (n + 1)) (q - n) ≫
        f.v (q - n) q (by omega)))
      (g.v q (q - (n + 1)) (by omega)) =
      (n + 1).negOnePow • differentialPairingETerm k T J pairing E n f g q := by
    rw [map_zsmul_unit]
    change q.negOnePow • ((n + 1).negOnePow •
      (pairing q).equiv (E.X (q - (n + 1)))
        (E.d (q - (n + 1)) (q - n) ≫ f.v (q - n) q (by omega))
        (g.v q (q - (n + 1)) (by omega))) = _
    rw [(pairing q).naturality, smul_comm]
    rfl
  exact congrArg₂ (· + ·) first (by
    simpa only [map_zsmul_unit, LinearMap.smul_apply] using second)

theorem differentialPairingTerm_right (n : ℤ) (f : Cochain E J n)
    (g : Cochain (mappedCochainComplex T J) E (-(n + 1))) (q : ℤ) :
    cochainPairingTerm k T J pairing E n f (δ (-(n + 1)) (-n) g) q =
      differentialPairingETerm k T J pairing E n f g q +
        (-n).negOnePow • differentialPairingJTerm k T J pairing E n f g q := by
  unfold cochainPairingTerm
  rw [δ_v (-(n + 1)) (-n) (by omega) g q (q - n) (by omega)
    (q - (n + 1)) (q + 1) (by omega) rfl]
  simp only [map_add, map_zsmul_unit, smul_add]
  change differentialPairingETerm k T J pairing E n f g q +
    q.negOnePow • ((-n).negOnePow •
      (pairing q).equiv (E.X (q - n)) (f.v (q - n) q (by omega))
        (T.map (J.d q (q + 1)) ≫ g.v (q + 1) (q - n) (by omega))) = _
  rw [smul_comm q.negOnePow (-n).negOnePow]
  rfl

theorem finsum_degreeSign (n : ℤ) (f : ℤ → k) :
    (∑ᶠ q, n.negOnePow • f q) = n.negOnePow • ∑ᶠ q, f q :=
  ((degreeSignEquiv k k n).toAddEquiv.map_finsum f).symm

theorem finiteCochainPairingEquiv_differential
    (compatible : ∀ p q, Compatible k (pairing p) (pairing q) (J.d p q))
    (support : Finset ℤ) (outside : ∀ q, q ∉ support → IsZero (J.X q))
    (n : ℤ) (f : Cochain E J n)
    (g : Cochain (mappedCochainComplex T J) E (-(n + 1))) :
    finiteCochainPairingEquiv k T J pairing E support outside (n + 1)
      (δ n (n + 1) f) g =
    (n + 1).negOnePow •
      finiteCochainPairingEquiv k T J pairing E support outside n f
        (δ (-(n + 1)) (-n) g) := by
  rw [finiteCochainPairingEquiv_eq_finsum, finiteCochainPairingEquiv_eq_finsum]
  let a := differentialPairingJTerm k T J pairing E n f g
  let b := differentialPairingETerm k T J pairing E n f g
  have ha : a.HasFiniteSupport := differentialPairingJTerm_finite k T J pairing E support outside n f g
  have hb : b.HasFiniteSupport := differentialPairingETerm_finite k T J pairing E support outside n f g
  have hshift : (fun q : ℤ => a (q - 1)).HasFiniteSupport :=
    Function.HasFiniteSupport.fun_comp_of_injective (Equiv.subRight (1 : ℤ)).injective ha
  have hsignedB : (fun q => (n + 1).negOnePow • b q).HasFiniteSupport :=
    Function.HasFiniteSupport.smul_right (fun _ => (n + 1).negOnePow) hb
  have hsignedA : (fun q => (-n).negOnePow • a q).HasFiniteSupport :=
    Function.HasFiniteSupport.smul_right (fun _ => (-n).negOnePow) ha
  have shiftedSum : (∑ᶠ q, a (q - 1)) = ∑ᶠ q, a q :=
    finsum_comp (g := a) (fun q : ℤ => q - 1) (Equiv.subRight (1 : ℤ)).bijective
  have left : (∑ᶠ q, cochainPairingTerm k T J pairing E (n + 1) (δ n (n + 1) f) g q) =
      -(∑ᶠ q, a q) + (n + 1).negOnePow • ∑ᶠ q, b q := by
    simp_rw [differentialPairingTerm_left k T J pairing E compatible]
    change (∑ᶠ q, (-a (q - 1) + (n + 1).negOnePow • b q)) = _
    calc
      _ = (∑ᶠ q, -a (q - 1)) + ∑ᶠ q, (n + 1).negOnePow • b q :=
        finsum_add_distrib (Function.HasFiniteSupport.neg hshift) hsignedB
      _ = _ := by
        rw [finsum_neg_distrib, shiftedSum, finsum_degreeSign]
  have right : (∑ᶠ q, cochainPairingTerm k T J pairing E n f (δ (-(n + 1)) (-n) g) q) =
      (∑ᶠ q, b q) + (-n).negOnePow • ∑ᶠ q, a q := by
    simp_rw [differentialPairingTerm_right]
    change (∑ᶠ q, (b q + (-n).negOnePow • a q)) = _
    calc
      _ = (∑ᶠ q, b q) + ∑ᶠ q, (-n).negOnePow • a q := finsum_add_distrib hb hsignedA
      _ = _ := by rw [finsum_degreeSign]
  rw [left, right, smul_add, smul_smul, Int.negOnePow_neg, Int.negOnePow_succ]
  simp only [neg_mul, Int.units_mul_self, Units.neg_smul, one_smul]
  abel

end ToricPower.SerrePairing

end
