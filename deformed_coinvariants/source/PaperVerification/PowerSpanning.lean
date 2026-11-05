module

public import PaperVerification.PowerArtin

/-!
# The complete coordinate induction for weighted power-tail spanning

This is the upper-bound half of Theorem 2.2, for every number of variables,
every positive tail index, every field, and the full subset nonresonance
condition. The induction decreases `n+m`; its internal boundary filtration
deletes one variable at a time. No degree truncation occurs.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial
open scoped BigOperators

namespace PaperVerification.PowerOperators

variable {K : Type*} [Field K] {n : ℕ}

def tailFactor (l : ℕ) : MvPolynomial (Fin n) K :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin n => l ≤ j.val), X j

@[simp] theorem tailFactor_zero :
    tailFactor (K := K) (n := n) 0 = fullProduct := by
  simp [tailFactor, fullProduct]

@[simp] theorem tailFactor_card : tailFactor (K := K) (n := n) n = 1 := by
  have hs : (Finset.univ.filter (fun j : Fin n => n ≤ j.val)) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro j _
    exact Nat.not_le.mpr j.isLt
  rw [tailFactor, hs, Finset.prod_empty]

theorem tailFactor_step (i : Fin n) :
    tailFactor (K := K) i.val = X i * tailFactor (i.val+1) := by
  have hs : Finset.univ.filter (fun j : Fin n => i.val ≤ j.val) =
      insert i (Finset.univ.filter fun j : Fin n => i.val+1 ≤ j.val) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.ext_iff]
    omega
  have hi : i ∉ Finset.univ.filter (fun j : Fin n => i.val+1 ≤ j.val) := by simp
  rw [tailFactor, hs, Finset.prod_insert hi]
  rfl

theorem tailFactor_succ_eq_boundary (i : Fin (n+1)) :
    tailFactor (K := K) (i.val+1) = boundaryFactor i := by
  have hs : Finset.univ.filter (fun j : Fin (n+1) => i.val+1 ≤ j.val) =
      boundaryIndices i := by
    ext j
    simp only [boundaryIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    change i.val+1 ≤ j.val ↔ i.val < j.val
    omega
  rw [tailFactor, hs]
  rfl

/-- The omitted-coordinate error lies in the preceding boundary layer. -/
theorem boundaryLift_mem_of_tail_mem
    (c : Fin (n+1) → K) (lam : K) (m : ℕ) (hm : 0 < m) (i : Fin (n+1))
    (U : Submodule K (MvPolynomial (Fin (n+1)) K))
    (hH : tailHit c lam m ≤ U)
    (hprev : ∀ p : MvPolynomial (Fin (n+1)) K, (X i * boundaryFactor i) * p ∈ U)
    (p : MvPolynomial (Fin n) K)
    (hp : p ∈ tailHit (boundaryCoefficients c lam i) lam m) :
    boundaryLift i p ∈ U := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨k, hk, q, rfl⟩ := hp
    have hB : reversed c lam k (boundaryLift i q) ∈ U :=
      hH (Submodule.subset_span ⟨k, hk, boundaryLift i q, rfl⟩)
    have herr : X i ^ k * boundaryLift i q ∈ U := by
      have he : X i ^ k * boundaryLift i q =
          (X i * boundaryFactor i) * (X i ^ (k-1) * rename i.succAbove q) := by
        have hk' : k = (k-1)+1 := by omega
        conv_lhs => rw [hk', pow_succ]
        rw [boundaryLift_apply]
        ring
      rw [he]
      exact hprev _
    have hd := U.sub_mem hB (U.smul_mem (c i + lam * (k : K)) herr)
    simpa only [reversed_boundaryLift, add_sub_cancel_left] using hd
  | zero => simpa only [map_zero] using U.zero_mem
  | add p q _ _ hp hq => simpa only [map_add] using U.add_mem hp hq
  | smul a p _ hp => simpa only [map_smul] using U.smul_mem a hp

theorem boundaryLift_all_mem
    (c : Fin (n+1) → K) (lam : K) (m : ℕ) (hm : 0 < m) (i : Fin (n+1))
    (U : Submodule K (MvPolynomial (Fin (n+1)) K))
    (hH : tailHit c lam m ≤ U) (hA : artinSpan K (n+1) m ≤ U)
    (hprev : ∀ p : MvPolynomial (Fin (n+1)) K, (X i * boundaryFactor i) * p ∈ U)
    (hlower : tailHit (boundaryCoefficients c lam i) lam m ⊔ artinSpan K n m = ⊤)
    (p : MvPolynomial (Fin n) K) : boundaryLift i p ∈ U := by
  have hp : p ∈ tailHit (boundaryCoefficients c lam i) lam m ⊔ artinSpan K n m := by
    rw [hlower]
    trivial
  obtain ⟨q, hq, r, hr, hqr⟩ := Submodule.mem_sup.mp hp
  rw [← hqr, map_add]
  exact U.add_mem (boundaryLift_mem_of_tail_mem c lam m hm i U hH hprev q hq)
    (hA (boundaryLift_mem_artinSpan m hm i r hr))

/-- The boundary filtration is exhausted after every coordinate has been
removed. This lemma retains the actual operator and actual Artin spans. -/
theorem spanning_of_full_and_boundary
    (c : Fin (n+1) → K) (lam : K) (m : ℕ) (hm : 0 < m)
    (hfull : ∀ p, fullProduct * p ∈ tailHit c lam m ⊔ artinSpan K (n+1) m)
    (hlower : ∀ i : Fin (n+1),
      tailHit (boundaryCoefficients c lam i) lam m ⊔ artinSpan K n m = ⊤) :
    tailHit c lam m ⊔ artinSpan K (n+1) m = ⊤ := by
  let U := tailHit c lam m ⊔ artinSpan K (n+1) m
  have hH : tailHit c lam m ≤ U := le_sup_left
  have hA : artinSpan K (n+1) m ≤ U := le_sup_right
  have hfil : ∀ l : ℕ, l ≤ n+1 → ∀ p : MvPolynomial (Fin (n+1)) K,
      tailFactor l * p ∈ U := by
    intro l
    induction l with
    | zero =>
      intro _ p
      rw [tailFactor_zero]
      exact hfull p
    | succ l ih =>
      intro hl p
      let i : Fin (n+1) := ⟨l, by omega⟩
      have hprev : ∀ q : MvPolynomial (Fin (n+1)) K,
          (X i * boundaryFactor i) * q ∈ U := by
        intro q
        have he : tailFactor (K := K) i.val = X i * boundaryFactor i := by
          rw [tailFactor_step, tailFactor_succ_eq_boundary]
        rw [← he]
        exact ih (by omega) q
      have hb := boundaryLift_all_mem c lam m hm i U hH hA hprev (hlower i)
      change tailFactor (i.val+1) * p ∈ U
      rw [tailFactor_succ_eq_boundary]
      obtain ⟨q, r, he⟩ := exists_coordinate_split i p
      rw [he, mul_add]
      have hmul : boundaryFactor i * (X i * q) = (X i * boundaryFactor i) * q := by ring
      rw [hmul]
      exact U.add_mem (hprev q) (hb r)
  apply top_unique
  intro p _
  have h := hfil (n+1) le_rfl p
  simpa only [tailFactor_card, one_mul] using h

/-- The full spanning assertion in Theorem 2.2. This uses the exact paper
condition for all nonempty subsets and all integers above each threshold. -/
theorem tailHit_sup_artinSpan_eq_top
    (c : Fin n → K) (lam : K) (m : ℕ) (hm : 0 < m)
    (hnr : Nonresonant c lam m) : tailHit c lam m ⊔ artinSpan K n m = ⊤ := by
  have H : ∀ s : ℕ, ∀ n m : ℕ, n+m=s → 0 < m →
      ∀ (c : Fin n → K) (lam : K), Nonresonant c lam m →
        tailHit c lam m ⊔ artinSpan K n m = ⊤ := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro n m hsum hm c lam hnr
      cases n with
      | zero => simp only [artinSpan_zero, sup_top_eq]
      | succ n =>
        apply spanning_of_full_and_boundary c lam m hm
        · intro p
          by_cases hm1 : m = 1
          · subst m
            exact (le_sup_left : tailHit c lam 1 ≤ tailHit c lam 1 ⊔ artinSpan K (n+1) 1)
              (fullProduct_mul_mem_tail_one (Nat.succ_pos n) c lam hnr p)
          · have hm2 : 1 < m := by omega
            have hmrec : (m-1)+1=m := by omega
            have hnr' : Nonresonant (fun i => c i+lam) lam (m-1) := by
              apply Nonresonant.lower_tail
              simpa only [hmrec] using hnr
            have hsmall := ih ((n+1)+(m-1)) (by omega) (n+1) (m-1)
              rfl (by omega) (fun i => c i+lam) lam hnr'
            have hp : p ∈ tailHit (fun i => c i+lam) lam (m-1) ⊔
                artinSpan K (n+1) (m-1) := by rw [hsmall]; trivial
            obtain ⟨q, hq, r, hr, hqr⟩ := Submodule.mem_sup.mp hp
            rw [← hqr, mul_add]
            apply Submodule.add_mem
            · exact (le_sup_left : tailHit c lam m ≤ tailHit c lam m ⊔ artinSpan K (n+1) m)
                (fullProduct_mul_mem_tail_of_mem_lower c lam m hm q hq)
            · exact (le_sup_right : artinSpan K (n+1) m ≤ tailHit c lam m ⊔ artinSpan K (n+1) m)
                (fullProduct_mul_mem_artinSpan m hm r hr)
        · intro i
          exact ih (n+m) (by omega) n m rfl hm (boundaryCoefficients c lam i) lam
            (boundary_nonresonant c lam m hnr i)
  exact H (n+m) n m rfl hm c lam hnr

/-- The classes of the exact Artin monomials span the literal joint-image
quotient. Linear independence and equivariant comparison are separate claims. -/
theorem artinSpan_quotient_eq_top
    (c : Fin n → K) (lam : K) (m : ℕ) (hm : 0 < m)
    (hnr : Nonresonant c lam m) :
    (artinSpan K n m).map (tailHit c lam m).mkQ = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨p, rfl⟩ := (tailHit c lam m).mkQ_surjective x
  have hp : p ∈ tailHit c lam m ⊔ artinSpan K n m := by
    rw [tailHit_sup_artinSpan_eq_top c lam m hm hnr]
    trivial
  obtain ⟨q, hq, r, hr, hqr⟩ := Submodule.mem_sup.mp hp
  refine ⟨r, hr, ?_⟩
  have hq0 : (tailHit c lam m).mkQ q = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hq
  rw [← hqr, map_add, hq0, zero_add]

end PaperVerification.PowerOperators
