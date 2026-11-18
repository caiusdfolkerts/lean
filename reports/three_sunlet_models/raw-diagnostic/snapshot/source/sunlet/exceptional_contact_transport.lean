module

public import sunlet.support_transport
public import sunlet.contact_exceptions

/-! Uncompiled continuation: finite contact certificates in arbitrary loop
coordinates. The finite source bodies are imported through ContactExceptions,
which shares the consolidated ContactDevelopment core and avoids duplicate
fragment imports. This module has not been compiler checked.

Every support below is constructed from a proved complete finite enumeration
or an actual multiplication-preserving cube equivalence. The radial assertion
is the literal sparse second-differential assertion, not a field that is assumed.
-/

@[expose] public section
noncomputable section

namespace Sunlet.LoopData

open SupportTransport ToricDifferential

variable {Ω K : Type*} [Fintype Ω] [DecidableEq Ω] [Field K] [CharZero K]
  (L : LoopData Ω)

theorem nonidentity_left_injective :
    Function.Injective (fun a : L.Nonidentity => L.left a.val) := by
  intro a b hab
  apply Subtype.ext
  have h := congrArg (fun p : Equiv.Perm Ω => p L.identity) hab
  simpa only [L.right_identity] using h

theorem nonidentity_two_of_card (A : Finset L.Nonidentity) (hA : 2 ≤ A.card) :
    ∃ a ∈ A, ∃ b ∈ A, L.left a.val ≠ L.left b.val := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp
    (show 1 < A.card by omega)
  exact ⟨a, ha, b, hb, fun h => hab (L.nonidentity_left_injective h)⟩

/-- All order-five loops, with arbitrary point labels and arbitrary
characteristic-zero coefficient field, have the actual transported sparse
supports and first-summand radial contact certificate. -/
theorem exists_five_point_contact_supports (hm : Fintype.card Ω = 5) :
    ∃ A B : Finset L.Nonidentity,
      A.card = 2 ∧ B.card = 2 ∧ Disjoint A B ∧
      (∃ a ∈ A, ∃ b ∈ A, L.left a.val ≠ L.left b.val) ∧
      (∃ a ∈ B, ∃ b ∈ B, L.left a.val ≠ L.left b.val) ∧
      TransitiveFamily (fun a : L.Nonidentity => L.left a.val) (A : Set L.Nonidentity) ∧
      TransitiveFamily (fun a : L.Nonidentity => L.left a.val) (B : Set L.Nonidentity) ∧
      (∀ v : Variation K L.Nonidentity Ω, v.2 L.identity = 0 →
        (∀ w, hessian (fun a : L.Nonidentity => L.left a.val)
          (sparseCoefficients (A : Set L.Nonidentity)) (fun _ => 1) v w ∈
            Contact.tangentSpan (fun a : L.Nonidentity => L.left a.val) L.identity
              (A : Set L.Nonidentity) (B : Set L.Nonidentity)) →
        ∃ lam : K, v = lam •
          (sparseCoefficients (A : Set L.Nonidentity), (0 : Ω → K))) := by
  classical
  obtain ⟨i, ev, ec, ho, hπ⟩ := L.exists_five_point_labels hm
  let A := mapSupport ec (FivePointContact.firstSupport i)
  let B := mapSupport ec (FivePointContact.secondSupport i)
  have hs := FivePointContact.support_sizes i
  have hA : A.card = 2 := by
    simpa only [A, card_mapSupport] using hs.1
  have hB : B.card = 2 := by
    simpa only [B, card_mapSupport] using hs.2.1
  refine ⟨A, B, hA, hB,
    disjoint_mapSupport ec _ _ hs.2.2,
    L.nonidentity_two_of_card A (by omega),
    L.nonidentity_two_of_card B (by omega), ?_, ?_, ?_⟩
  · exact transitive_map ec ev (fun a : L.Nonidentity => L.left a.val)
      (FivePointContact.permutations i) hπ _ (FivePointContact.first_transitive i)
  · exact transitive_map ec ev (fun a : L.Nonidentity => L.left a.val)
      (FivePointContact.permutations i) hπ _ (FivePointContact.second_transitive i)
  · intro v hv hc
    apply radial_map ec ev (fun a : L.Nonidentity => L.left a.val)
      (FivePointContact.permutations i) L.identity 0 ho hπ
      (FivePointContact.firstSupport i) (FivePointContact.secondSupport i) ?_ v hv hc
    intro v' hv' hc'
    exact SparseContactCertificate.radial (K := K) (FivePointContact.permutations i) 0
      (FivePointContact.firstSupport i : Set (Fin 4))
      (FivePointContact.secondSupport i : Set (Fin 4))
      (FivePointContact.directionEquiv (FivePointContact.pivotIndex i))
      (FivePointContact.certificate i) v' hv' hc'

/-- The order-eight exceptional case requires the actual cube group
structure, supplied by a multiplication-preserving equivalence. Cardinality
eight alone is deliberately not a hypothesis sufficient for this theorem. -/
theorem exists_eight_point_contact_supports
    (e : Ω ≃ (Fin 3 → ZMod 2)) (he : e L.identity = 0)
    (hmul : ∀ x y, e (L.mul x y) = e x + e y) :
    ∃ A B : Finset L.Nonidentity,
      A.card = 3 ∧ B.card = 3 ∧ Disjoint A B ∧
      (∃ a ∈ A, ∃ b ∈ A, L.left a.val ≠ L.left b.val) ∧
      (∃ a ∈ B, ∃ b ∈ B, L.left a.val ≠ L.left b.val) ∧
      TransitiveFamily (fun a : L.Nonidentity => L.left a.val) (A : Set L.Nonidentity) ∧
      TransitiveFamily (fun a : L.Nonidentity => L.left a.val) (B : Set L.Nonidentity) ∧
      (∀ v : Variation K L.Nonidentity Ω, v.2 L.identity = 0 →
        (∀ w, hessian (fun a : L.Nonidentity => L.left a.val)
          (sparseCoefficients (A : Set L.Nonidentity)) (fun _ => 1) v w ∈
            Contact.tangentSpan (fun a : L.Nonidentity => L.left a.val) L.identity
              (A : Set L.Nonidentity) (B : Set L.Nonidentity)) →
        ∃ lam : K, v = lam •
          (sparseCoefficients (A : Set L.Nonidentity), (0 : Ω → K))) := by
  classical
  obtain ⟨ev, ec, ho, hπ⟩ := L.exists_eight_point_labels e he hmul
  let A := mapSupport ec EightPointContact.firstSupport
  let B := mapSupport ec EightPointContact.secondSupport
  have hs := EightPointContact.support_sizes
  have hA : A.card = 3 := by
    simpa only [A, card_mapSupport] using hs.1
  have hB : B.card = 3 := by
    simpa only [B, card_mapSupport] using hs.2.1
  refine ⟨A, B, hA, hB,
    disjoint_mapSupport ec _ _ hs.2.2,
    L.nonidentity_two_of_card A (by omega),
    L.nonidentity_two_of_card B (by omega), ?_, ?_, ?_⟩
  · exact transitive_map ec ev (fun a : L.Nonidentity => L.left a.val)
      EightPointContact.permutations hπ _ EightPointContact.first_transitive
  · exact transitive_map ec ev (fun a : L.Nonidentity => L.left a.val)
      EightPointContact.permutations hπ _ EightPointContact.second_transitive
  · intro v hv hc
    apply radial_map ec ev (fun a : L.Nonidentity => L.left a.val)
      EightPointContact.permutations L.identity 0 ho hπ
      EightPointContact.firstSupport EightPointContact.secondSupport ?_ v hv hc
    intro v' hv' hc'
    exact SparseContactCertificate.radial (K := K) EightPointContact.permutations 0
      (EightPointContact.firstSupport : Set (Fin 7))
      (EightPointContact.secondSupport : Set (Fin 7))
      (EightPointContact.directionEquiv EightPointContact.pivotIndex)
      EightPointContact.certificate v' hv' hc'

end Sunlet.LoopData
