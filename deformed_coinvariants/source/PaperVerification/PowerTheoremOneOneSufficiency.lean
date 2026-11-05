module

public import PaperVerification.PowerTheoremTwoTwo
public import PaperVerification.PowerCoinvariantComparator

/-!
# The full symmetric-group sufficiency assertion of Theorem 1.1

The comparator is the literal quotient by the elementary symmetric
polynomials. The complete/elementary ideal identity is proved integrally,
and its quotient map preserves both polynomial classes and every degree.
The final representations have the full symmetric group as their domain.
The exceptional-parameter necessity assertion is a separate proof.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Representation Module

namespace PaperVerification.PowerOperators

variable {K : Type*} [Field K] {n : ℕ}

def elementaryCoinvariantFamily (K : Type*) [Field K] (n : ℕ) :
    Fin n → MvPolynomial (Fin n) K := fun i => esymm (Fin n) K (i.val+1)

theorem elementaryCoinvariantFamily_invariant
    (G : Subgroup (Equiv.Perm (Fin n))) (g : G) (i : Fin n) :
    rename (g : Equiv.Perm (Fin n)) (elementaryCoinvariantFamily K n i) =
      elementaryCoinvariantFamily K n i :=
  rename_esymm (Fin n) K (i.val+1) (g : Equiv.Perm (Fin n))

theorem completeHomogeneousIdeal_one_eq_ordinaryCoinvariantIdeal :
    completeHomogeneousIdeal K n 1 = ordinaryCoinvariantIdeal K n := by
  have he : completeHomogeneousIdeal K n 1 = completeCoinvariantIdeal K n := by
    change Ideal.span (Set.range (completeHomogeneousFamily K n 1)) =
      Ideal.span (Set.range fun i : Fin n => hsymm (Fin n) K (i.val+1))
    apply congrArg (fun f : Fin n → MvPolynomial (Fin n) K => Ideal.span (Set.range f))
    funext i
    exact congrArg (hsymm (Fin n) K) (Nat.add_comm 1 i.val)
  rw [he, completeCoinvariantIdeal_eq_ordinaryCoinvariantIdeal]

def completeToCoinvariant :
    (MvPolynomial (Fin n) K ⧸ completeHomogeneousIdeal K n 1) ≃ₐ[K]
      (MvPolynomial (Fin n) K ⧸ ordinaryCoinvariantIdeal K n) :=
  Ideal.quotientEquivAlgOfEq K completeHomogeneousIdeal_one_eq_ordinaryCoinvariantIdeal

@[simp] theorem completeToCoinvariant_mkQ (p : MvPolynomial (Fin n) K) :
    completeToCoinvariant ((completeHomogeneousIdeal K n 1).mkQ p) =
      (ordinaryCoinvariantIdeal K n).mkQ p := rfl

def ordinaryCoinvariantAction (G : Subgroup (Equiv.Perm (Fin n))) :
    Representation K G (MvPolynomial (Fin n) K ⧸ ordinaryCoinvariantIdeal K n) :=
  ordinaryQuotientAction G (elementaryCoinvariantFamily K n)
    (elementaryCoinvariantFamily_invariant G)

def ordinaryCoinvariantDegree (K : Type*) [Field K] (n d : ℕ) :
    Submodule K (MvPolynomial (Fin n) K ⧸ ordinaryCoinvariantIdeal K n) :=
  ordinaryQuotientDegree (elementaryCoinvariantFamily K n) d

def completeToCoinvariantRepresentation (G : Subgroup (Equiv.Perm (Fin n))) :
    (completeHomogeneousAction (K := K) G 1).Equiv (ordinaryCoinvariantAction G) :=
  Representation.Equiv.mk completeToCoinvariant.toLinearEquiv (by
    intro g
    apply LinearMap.ext
    intro x
    obtain ⟨p,rfl⟩ := (completeHomogeneousIdeal K n 1).mkQ_surjective x
    change completeToCoinvariant
      ((completeHomogeneousIdeal K n 1).mkQ (rename (g : Equiv.Perm (Fin n)) p)) =
      ordinaryCoinvariantAction G g
        (completeToCoinvariant ((completeHomogeneousIdeal K n 1).mkQ p))
    rw [completeToCoinvariant_mkQ,completeToCoinvariant_mkQ]
    rfl)

theorem completeToCoinvariant_degree_iff (d : ℕ)
    (x : MvPolynomial (Fin n) K ⧸ completeHomogeneousIdeal K n 1) :
    x ∈ ordinaryQuotientDegree (completeHomogeneousFamily K n 1) d ↔
      completeToCoinvariant x ∈ ordinaryCoinvariantDegree K n d := by
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact ⟨p,hp,(completeToCoinvariant_mkQ p).symm⟩
  · rintro ⟨p,hp,he⟩
    refine ⟨p,hp,?_⟩
    apply completeToCoinvariant.injective
    exact (completeToCoinvariant_mkQ p).trans he

def permutationToTop (n : ℕ) :
    Equiv.Perm (Fin n) →* (⊤ : Subgroup (Equiv.Perm (Fin n))) where
  toFun σ := ⟨σ, trivial⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def originalCoinvariantRepresentation (α : K) :
    Representation K (Equiv.Perm (Fin n))
      (MvPolynomial (Fin n) K ⧸ originalTailHit (fun _ => (1 : K)) α 1) :=
  (originalTailQuotientAction ⊤ (fun _ : Fin n => (1 : K)) α 1
    (fun _ _ => rfl)).comp (permutationToTop n)

def ordinaryCoinvariantRepresentation :
    Representation K (Equiv.Perm (Fin n))
      (MvPolynomial (Fin n) K ⧸ ordinaryCoinvariantIdeal K n) :=
  (ordinaryCoinvariantAction ⊤).comp (permutationToTop n)

/-- Both sufficiency conclusions of the printed theorem: the literal Artin
basis and an actual graded isomorphism for the full symmetric group. The
necessity when `n ≥ 2` is not asserted by this declaration. -/
theorem paper_theorem_1_1_sufficiency [CharZero K]
    (α : K) (hα : α ∉ exceptionalSet K n) :
    (∃ B : Basis (ArtinIndex n 1) K
        (MvPolynomial (Fin n) K ⧸ originalTailHit (fun _ => (1 : K)) α 1),
      ∀ a, B a = (originalTailHit (fun _ => (1 : K)) α 1).mkQ (monomial a.val 1)) ∧
    PaperVerification.GradedRepresentationEquivalent
      (originalCoinvariantRepresentation α) (ordinaryCoinvariantRepresentation (K := K) (n := n))
      (originalTailQuotientDegree (fun _ : Fin n => (1 : K)) α 1)
      (ordinaryCoinvariantDegree K n) := by
  refine ⟨paper_theorem_1_1_monomial_basis α hα,?_⟩
  have hnr : Nonresonant (fun _ : Fin n => (1 : K)) α 1 := by
    apply (nonresonant_one_iff α).mpr
    simpa only [Fintype.card_fin] using hα
  have hlow : ∀ i : Fin n, ∀ a : ℕ, a < 1 → (1 : K)+α*(a : K) ≠ 0 := by
    intro i a ha
    have ha0 : a=0 := by omega
    simp [ha0]
  obtain ⟨e,he,he'⟩ := paper_theorem_2_2_original_graded_representation
    (fun _ : Fin n => (1 : K)) α 1 Nat.zero_lt_one hnr hlow ⊤ (fun _ _ => rfl)
  let E := e.trans (completeToCoinvariantRepresentation ⊤)
  let F : (originalCoinvariantRepresentation α).Equiv
      (ordinaryCoinvariantRepresentation (K := K) (n := n)) :=
    Representation.Equiv.mk E.toLinearEquiv (fun σ =>
      E.toIntertwiningMap.isIntertwining' (permutationToTop n σ))
  refine ⟨F,fun d x => ?_⟩
  change x ∈ originalTailQuotientDegree (fun _ => (1 : K)) α 1 d ↔
    completeToCoinvariant (e x) ∈ ordinaryCoinvariantDegree K n d
  rw [← completeToCoinvariant_degree_iff]
  constructor
  · exact he d x
  · intro hx
    have h := he' d (e x) hx
    change e.toLinearEquiv.symm (e.toLinearEquiv x) ∈
      originalTailQuotientDegree (fun _ => (1 : K)) α 1 d at h
    simpa only [LinearEquiv.symm_apply_apply] using h

end PaperVerification.PowerOperators
