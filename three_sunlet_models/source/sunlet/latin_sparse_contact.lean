module

public import sunlet.contact_development

/-! The support arguments concern all Latin colors, whereas the toric
summand omits the identity row.  This file proves the restriction bridge
and applies the actual sparse Hessian calculation to the constructed
supports.  No support hypothesis occurs in the existence theorem. -/

@[expose] public section
noncomputable section
open Finset

namespace Sunlet.NormalizedLatinSystem

open ToricDifferential

variable {ι Ω K : Type*} [Fintype ι] [Fintype Ω]
  [DecidableEq ι] [DecidableEq Ω] [Field K] [CharZero K]
  (L : NormalizedLatinSystem ι Ω)

abbrev NonidentityColor := {a : ι // a ≠ L.identity}

def nonidentityPerm : L.NonidentityColor → Equiv.Perm Ω := fun a => L.perm a

def nonidentitySupport (P : Finset ι) : Set L.NonidentityColor :=
  fun a => a.val ∈ P

instance nonidentitySupportDecidable (P : Finset ι) :
    DecidablePred (· ∈ L.nonidentitySupport P) :=
  fun a => inferInstanceAs (Decidable (a.val ∈ P))

theorem colorConnected_nonidentity (P : Set ι) (he : L.identity ∉ P) (x y : Ω) :
    ColorConnected L.nonidentityPerm (Subtype.val ⁻¹' P) x y ↔
      ColorConnected L.perm P x y := by
  constructor
  · apply Relation.EqvGen.mono
    rintro u v ⟨a, ha, huv⟩
    exact ⟨a.val, ha, huv⟩
  · apply Relation.EqvGen.mono
    rintro u v ⟨a, ha, huv⟩
    exact ⟨⟨a, fun h => he (h ▸ ha)⟩, ha, huv⟩

theorem transitive_nonidentity (P : Finset ι) (he : L.identity ∉ P)
    (ht : TransitiveFamily L.perm (P : Set ι)) :
    TransitiveFamily L.nonidentityPerm (L.nonidentitySupport P) := by
  intro x y
  exact (L.colorConnected_nonidentity (P : Set ι) he x y).mpr (ht x y)

theorem nonidentity_two (o : Ω) (P : Finset ι) (he : L.identity ∉ P)
    (hc : 2 ≤ P.card) :
    ∃ a ∈ L.nonidentitySupport P, ∃ b ∈ L.nonidentitySupport P,
      L.nonidentityPerm a ≠ L.nonidentityPerm b := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < P.card)
  refine ⟨⟨a, fun h => he (h ▸ ha)⟩, ha, ⟨b, fun h => he (h ▸ hb)⟩, hb, ?_⟩
  exact fun h => hab (L.perm_injective o h)

theorem nonidentity_three (o : Ω) (P : Finset ι) (he : L.identity ∉ P)
    (hc : 3 ≤ P.card) :
    ∃ a ∈ L.nonidentitySupport P, ∃ b ∈ L.nonidentitySupport P,
      ∃ c ∈ L.nonidentitySupport P,
      L.nonidentityPerm a ≠ L.nonidentityPerm b ∧
      L.nonidentityPerm a ≠ L.nonidentityPerm c ∧
      L.nonidentityPerm b ≠ L.nonidentityPerm c := by
  obtain ⟨a, ha, b, hb, c, hc', hab, hac, hbc⟩ :=
    Finset.two_lt_card.mp (by omega : 2 < P.card)
  refine ⟨⟨a, fun h => he (h ▸ ha)⟩, ha, ⟨b, fun h => he (h ▸ hb)⟩, hb,
    ⟨c, fun h => he (h ▸ hc')⟩, hc', ?_, ?_, ?_⟩
  · exact fun h => hab (L.perm_injective o h)
  · exact fun h => hac (L.perm_injective o h)
  · exact fun h => hbc (L.perm_injective o h)

theorem nonidentitySupport_erase (P : Finset ι) (a : L.NonidentityColor) :
    L.nonidentitySupport (P.erase a.val) = L.nonidentitySupport P \ {a} := by
  ext b
  change b.val ∈ P.erase a.val ↔ b.val ∈ P ∧ b ∉ ({a} : Set L.NonidentityColor)
  simp [Subtype.ext_iff, and_comm]

theorem ordinary_nonidentity (o : Ω) (P : Finset ι) (he : L.identity ∉ P)
    (hconn : ∀ x y, Relation.EqvGen
      (PuncturedBothEndpoints.OrdinaryEdge o L.perm (P : Set ι)) x y) :
    ∀ x y, Relation.EqvGen
      (PuncturedBothEndpoints.OrdinaryEdge o L.nonidentityPerm (L.nonidentitySupport P)) x y := by
  intro x y
  apply Relation.EqvGen.mono (r := PuncturedBothEndpoints.OrdinaryEdge o L.perm (P : Set ι))
    (p := PuncturedBothEndpoints.OrdinaryEdge o L.nonidentityPerm (L.nonidentitySupport P))
    ?_ x y (hconn x y)
  rintro u v ⟨a, ha, huv⟩
  exact ⟨⟨a, fun h => he (h ▸ ha)⟩, ha, huv⟩

/-- The actual restricted Hessian is radial for the support sets produced
by the combinatorial Latin-system arguments. -/
theorem radial_of_contactSupports (o : Ω) {A B : Finset ι}
    (hS : L.ContactSupports o A B) (hm : 5 ≤ Fintype.card Ω)
    (v : Variation K L.NonidentityColor Ω) (hv : v.2 o = 0)
    (hc : ∀ w, hessian L.nonidentityPerm
      (sparseCoefficients (L.nonidentitySupport A)) (fun _ => 1) v w ∈
      Contact.tangentSpan L.nonidentityPerm o
        (L.nonidentitySupport A) (L.nonidentitySupport B)) :
    ∃ lam : K, v = lam • (sparseCoefficients (L.nonidentitySupport A), (0 : Ω → K)) := by
  classical
  have hdis : Disjoint (L.nonidentitySupport A) (L.nonidentitySupport B) := by
    apply Set.disjoint_left.mpr
    intro a ha hb
    exact Finset.disjoint_left.mp hS.disjoint ha hb
  have hredtwo : ∀ b ∈ L.nonidentitySupport B,
      ∃ a ∈ L.nonidentitySupport B \ {b}, ∃ c ∈ L.nonidentitySupport B \ {b},
        L.nonidentityPerm a ≠ L.nonidentityPerm c := by
    intro b hb
    rw [← L.nonidentitySupport_erase B b]
    apply L.nonidentity_two o (B.erase b.val)
    · exact fun h => hS.identity_second (Finset.mem_erase.mp h).2
    · have hh := hS.second_three
      rw [Finset.card_erase_of_mem hb]
      omega
  have hredtrans : ∀ b ∈ L.nonidentitySupport B,
      TransitiveFamily L.nonidentityPerm (L.nonidentitySupport B \ {b}) := by
    intro b hb
    rw [← L.nonidentitySupport_erase B b]
    exact L.transitive_nonidentity (B.erase b.val)
      (fun h => hS.identity_second (Finset.mem_erase.mp h).2)
      (hS.deletion_transitive b.val hb)
  obtain ⟨a, ha, b, hb, hab⟩ := L.nonidentity_two o A hS.identity_first hS.first_two
  exact SparseContact.radial L.nonidentityPerm o
    (L.nonidentitySupport A) (L.nonidentitySupport B) hdis hm
    (fun a x => L.derangement a.val a.property x) ⟨a, ha⟩
    (L.nonidentity_two o B hS.identity_second (by have := hS.second_three; omega))
    (L.transitive_nonidentity B hS.identity_second hS.second_transitive)
    hredtwo hredtrans
    (L.nonidentity_three o B hS.identity_second hS.second_three)
    (L.ordinary_nonidentity o B hS.identity_second hS.ordinary_connected)
    (fun a b h => Subtype.ext ((L.column_bijective o).injective h))
    (fun a b h => Subtype.ext (L.inverse_column_injective o h)) v hv hc

/-- Full existence in the nonexceptional support range; the small
certificate cases are assembled separately. -/
theorem exists_radial_supports_nonexceptional (o : Ω)
    (hm : Fintype.card Ω = 6 ∨ Fintype.card Ω = 7 ∨ 9 ≤ Fintype.card Ω) :
    ∃ A B : Finset ι, L.ContactSupports o A B ∧
      ∀ v : Variation K L.NonidentityColor Ω, v.2 o = 0 →
      (∀ w, hessian L.nonidentityPerm
        (sparseCoefficients (L.nonidentitySupport A)) (fun _ => 1) v w ∈
        Contact.tangentSpan L.nonidentityPerm o
          (L.nonidentitySupport A) (L.nonidentitySupport B)) →
      ∃ lam : K, v = lam • (sparseCoefficients (L.nonidentitySupport A), (0 : Ω → K)) := by
  have hm5 : 5 ≤ Fintype.card Ω := by omega
  obtain ⟨A, B, hS⟩ : ∃ A B : Finset ι, L.ContactSupports o A B := by
    rcases hm with hm | hm
    · exact L.exists_contact_supports_six o hm
    · exact L.exists_contact_supports_large o hm
  exact ⟨A, B, hS, L.radial_of_contactSupports o hS hm5⟩

end Sunlet.NormalizedLatinSystem
