module

public import PaperVerification.PowerRegularComparator

/-!
# Equivariant lower bounds against the literal complete homogeneous quotient

The generic field is eliminated from the endpoint. Every test representation
and both quotient representations in the conclusion are over the original
field. The nonresonant theorem retains all fields; the constant-coefficient
characteristic-zero theorem is unconditional in the deformation slope.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Representation
open PaperVerification.EquivariantHomMatrices
open scoped BigOperators

namespace PaperVerification.PowerOperators

variable {K : Type*} [Field K] {n : ℕ}

theorem complete_intertwiner_finrank_le_tail_of_regular
    (c : Fin n → K) (lam : K) (m d : ℕ) (hm : 0 < m)
    (G : Subgroup (Equiv.Perm (Fin n)))
    (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i)
    (hcard : IsUnit (Nat.card G : K))
    (hregular : RingTheory.Sequence.IsWeaklyRegular
      (MvPolynomial (Fin n) (GroupedCoefficientField c))
      (List.ofFn fun i : Fin n => weightedPower (groupedCoefficient c) (m+i.val)))
    {l : Type*} [Fintype l] (τ : Representation K G (l → K)) :
    Module.finrank K (IntertwiningMap τ (completeHomogeneousDegreeRepresentation G m d)) ≤
      Module.finrank K (IntertwiningMap τ (tailQuotientDegreeRepresentation G c lam m hfix d)) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let E := GroupedCoefficientField c
  have hu : IsUnit (Fintype.card G : E) := by
    simpa only [map_natCast,Nat.card_eq_fintype_card] using hcard.map (algebraMap K E)
  letI : Invertible (Fintype.card G : E) := hu.invertible
  have h := tailQuotientDegree_intertwiner_finrank_ge_grouped_zero_of_regular c lam m d hm
    G hfix hcard hregular τ
  have hz := zero_tail_ordinary_intertwiner_finrank_eq G (groupedCoefficient c) m d
    (fun g i => groupedCoefficient_permutation c g (hfix g) i)
    (mapRepresentation (algebraMap K E) τ)
  have hc := grouped_power_complete_intertwiner_finrank_eq c m d hm G hfix hcard hregular τ
  rw [hz,hc] at h
  exact h

/-- The full equivariant lower bound of Theorem 2.2 over the original field,
for every coefficient stabilizer subgroup and every test representation. -/
theorem complete_intertwiner_finrank_le_tail
    (c : Fin n → K) (lam : K) (m d : ℕ) (hm : 0 < m) (hnr : Nonresonant c lam m)
    (G : Subgroup (Equiv.Perm (Fin n)))
    (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i)
    {l : Type*} [Fintype l] (τ : Representation K G (l → K)) :
    Module.finrank K (IntertwiningMap τ (completeHomogeneousDegreeRepresentation G m d)) ≤
      Module.finrank K (IntertwiningMap τ (tailQuotientDegreeRepresentation G c lam m hfix d)) :=
  complete_intertwiner_finrank_le_tail_of_regular c lam m d hm G hfix
    (hnr.isUnit_stabilizer_card G hfix) (grouped_weighted_power_regular hnr m hm) τ

theorem constant_nonresonant_zero [CharZero K] (m : ℕ) :
    Nonresonant (fun _ : Fin n => (1 : K)) 0 m := by
  intro I hI s hs
  have h : (I.card : K) ≠ 0 := Nat.cast_ne_zero.mpr hI.card_pos.ne'
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_one,zero_mul,add_zero] using h

/-- The unconditional lower bound needed at resonant parameters in the
necessity direction of Theorem 1.1. All representations remain over `K`. -/
theorem constant_complete_intertwiner_finrank_le_tail
    [CharZero K] (lam : K) (m d : ℕ) (hm : 0 < m)
    (G : Subgroup (Equiv.Perm (Fin n)))
    {l : Type*} [Fintype l] (τ : Representation K G (l → K)) :
    Module.finrank K (IntertwiningMap τ (completeHomogeneousDegreeRepresentation G m d)) ≤
      Module.finrank K (IntertwiningMap τ
        (tailQuotientDegreeRepresentation G (fun _ : Fin n => (1 : K)) lam m (fun _ _ => rfl) d)) := by
  have hcard : IsUnit (Nat.card G : K) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (ne_of_gt Nat.card_pos))
  exact complete_intertwiner_finrank_le_tail_of_regular (fun _ => 1) lam m d hm G
    (fun _ _ => rfl) hcard (grouped_weighted_power_regular (constant_nonresonant_zero m) m hm) τ

end PaperVerification.PowerOperators
