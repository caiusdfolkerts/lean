module

public import sunlet.generic_pair_geometry
public import sunlet.latin_sparse_contact
public import sunlet.exceptional_contact_transport

/-!
# Sparse contact witnesses in every order

The support sets are constructed from the Latin system. The exceptional
orders five and eight use the complete finite certificates and the proved
multiplication-preserving reduction. No support or contact condition is
added as a hypothesis to the existence theorem.
-/

@[expose] public section
noncomputable section

namespace Sunlet.ToricPairAlgebra.SparseWitness

open SupportTransport
variable {k ι ι' Ω Ω' : Type*} [Field k] [CharZero k]
  [Fintype ι] [Fintype ι'] [Fintype Ω] [Fintype Ω']
  [DecidableEq ι] [DecidableEq ι'] [DecidableEq Ω] [DecidableEq Ω']

def transport (ec : ι' ≃ ι) (ev : Ω' ≃ Ω)
    (π : ι → Equiv.Perm Ω) (π' : ι' → Equiv.Perm Ω')
    (o : Ω) (o' : Ω') (ho : ev o' = o)
    (hπ : ∀ a x, ev (π' a x) = π (ec a) (ev x))
    (W : SparseWitness (k := k) o' π') : SparseWitness (k := k) o π where
  A := mapSupport ec W.A
  B := mapSupport ec W.B
  disjoint := by
    apply Set.disjoint_left.mpr
    intro a ha hb
    apply Set.disjoint_left.mp W.disjoint
    · exact (mem_mapSupport ec W.A a).mp ha
    · exact (mem_mapSupport ec W.B a).mp hb
  Atwo := two_map ec ev π π' hπ W.A W.Atwo
  Btwo := two_map ec ev π π' hπ W.B W.Btwo
  Atrans := transitive_map ec ev π π' hπ W.A W.Atrans
  Btrans := transitive_map ec ev π π' hπ W.B W.Btrans
  radial := radial_map ec ev π π' o o' ho hπ W.A W.B W.radial

end Sunlet.ToricPairAlgebra.SparseWitness

namespace Sunlet.NormalizedLatinSystem

open ToricDifferential ToricPairAlgebra
variable {k ι Ω : Type*} [Field k] [CharZero k]
  [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
  (L : NormalizedLatinSystem ι Ω)

def nonidentitySupportFinset (A : Finset ι) : Finset L.NonidentityColor :=
  A.subtype (fun a => a ≠ L.identity)

@[simp] theorem mem_nonidentitySupportFinset (A : Finset ι) (a : L.NonidentityColor) :
    a ∈ L.nonidentitySupportFinset A ↔ a.val ∈ A := by
  simp [nonidentitySupportFinset]

@[simp] theorem coe_nonidentitySupportFinset (A : Finset ι) :
    (L.nonidentitySupportFinset A : Set L.NonidentityColor) = L.nonidentitySupport A := by
  ext a
  exact L.mem_nonidentitySupportFinset A a

/-- The already-proved contact calculation is applied to the actual
nonidentity-color restriction of the constructed support sets. -/
def witnessOfContactSupports (o : Ω) {A B : Finset ι}
    (hS : L.ContactSupports o A B) (hm : 5 ≤ Fintype.card Ω) :
    SparseWitness (k := k) o L.nonidentityPerm where
  A := L.nonidentitySupportFinset A
  B := L.nonidentitySupportFinset B
  disjoint := by
    apply Set.disjoint_left.mpr
    intro a ha hb
    exact Finset.disjoint_left.mp hS.disjoint
      ((L.mem_nonidentitySupportFinset A a).mp ha)
      ((L.mem_nonidentitySupportFinset B a).mp hb)
  Atwo := by
    obtain ⟨a, ha, b, hb, hab⟩ :=
      L.nonidentity_two o A hS.identity_first hS.first_two
    exact ⟨a, (L.mem_nonidentitySupportFinset A a).mpr ha,
      b, (L.mem_nonidentitySupportFinset A b).mpr hb, hab⟩
  Btwo := by
    obtain ⟨a, ha, b, hb, hab⟩ :=
      L.nonidentity_two o B hS.identity_second (by have := hS.second_three; omega)
    exact ⟨a, (L.mem_nonidentitySupportFinset B a).mpr ha,
      b, (L.mem_nonidentitySupportFinset B b).mpr hb, hab⟩
  Atrans := by
    simpa only [coe_nonidentitySupportFinset] using
      L.transitive_nonidentity A hS.identity_first hS.first_transitive
  Btrans := by
    simpa only [coe_nonidentitySupportFinset] using
      L.transitive_nonidentity B hS.identity_second hS.second_transitive
  radial := by
    have hcoef (d₁ : DecidablePred (· ∈ (L.nonidentitySupportFinset A : Set L.NonidentityColor)))
        (d₂ : DecidablePred (· ∈ L.nonidentitySupport A)) :
        @ToricDifferential.sparseCoefficients k L.NonidentityColor _
          (L.nonidentitySupportFinset A : Set L.NonidentityColor) d₁ =
        @ToricDifferential.sparseCoefficients k L.NonidentityColor _
          (L.nonidentitySupport A) d₂ := by
      funext a
      have hmem : a ∈ L.nonidentitySupport A ↔ a.val ∈ A := Iff.rfl
      simp only [ToricDifferential.sparseCoefficients, Finset.mem_coe,
        mem_nonidentitySupportFinset, hmem]
    intro v hv hc
    have hc' : ∀ w, hessian L.nonidentityPerm
        (sparseCoefficients (L.nonidentitySupport A)) (fun _ => 1) v w ∈
        Contact.tangentSpan L.nonidentityPerm o
          (L.nonidentitySupport A) (L.nonidentitySupport B) := by
      simpa only [hcoef, coe_nonidentitySupportFinset] using hc
    obtain ⟨lam, he⟩ := L.radial_of_contactSupports (K := k) o hS hm v hv hc'
    exact ⟨lam, by simpa only [hcoef] using he⟩

/-- The color bijection used in the loop normalization restricts to the
nonidentity colors, including its literal forward function. -/
def loopColorEquiv (o : Ω) : (L.loopAt o).Nonidentity ≃ L.NonidentityColor := by
  let e : ι ≃ Ω := Equiv.ofBijective (fun a => L.perm a o) (L.column_bijective o)
  have he : e.symm o = L.identity := by
    apply e.injective
    change e (e.symm o) = L.perm L.identity o
    rw [e.apply_symm_apply, L.normalized]
    rfl
  exact Equiv.subtypeEquiv e.symm (by
    intro x
    change x ≠ o ↔ e.symm x ≠ L.identity
    rw [← he]
    exact not_congr e.symm.injective.eq_iff.symm)

@[simp] theorem loopColorEquiv_permutation (o : Ω)
    (a : (L.loopAt o).Nonidentity) (x : Ω) :
    (L.loopAt o).left a.val x = L.nonidentityPerm (L.loopColorEquiv o a) x := rfl

/-- A literal loop witness transports back to the original Latin colors. -/
def witnessFromLoop (o : Ω)
    (W : SparseWitness (k := k) (L.loopAt o).identity
      (fun a : (L.loopAt o).Nonidentity => (L.loopAt o).left a.val)) :
    SparseWitness (k := k) o L.nonidentityPerm :=
  W.transport (L.loopColorEquiv o) (Equiv.refl Ω) L.nonidentityPerm
    (fun a : (L.loopAt o).Nonidentity => (L.loopAt o).left a.val) o
    (L.loopAt o).identity rfl (L.loopColorEquiv_permutation o)

/-- Full existence of the sparse Hessian witness for every normalized
Latin system of order at least five, with all labels arbitrary. -/
theorem exists_sparseWitness (o : Ω) (hm : 5 ≤ Fintype.card Ω) :
    Nonempty (SparseWitness (k := k) o L.nonidentityPerm) := by
  classical
  by_cases hm5 : Fintype.card Ω = 5
  · obtain ⟨A, B, _, _, hd, hAt, hBt, hA, hB, hr⟩ :=
      (L.loopAt o).exists_five_point_contact_supports (K := k) hm5
    let W : SparseWitness (k := k) (L.loopAt o).identity
        (fun a : (L.loopAt o).Nonidentity => (L.loopAt o).left a.val) :=
      { A := A, B := B,
        disjoint := Set.disjoint_left.mpr (fun a ha hb => Finset.disjoint_left.mp hd ha hb),
        Atwo := hAt, Btwo := hBt, Atrans := hA, Btrans := hB, radial := hr }
    exact ⟨L.witnessFromLoop o W⟩
  by_cases hm8 : Fintype.card Ω = 8
  · by_cases hno : L.NoTransitivePair
    · obtain ⟨e, he, hmul⟩ := L.cube_equiv_of_no_pair o hm8 hno
      obtain ⟨A, B, _, _, hd, hAt, hBt, hA, hB, hr⟩ :=
        (L.loopAt o).exists_eight_point_contact_supports (K := k) e he hmul
      let W : SparseWitness (k := k) (L.loopAt o).identity
          (fun a : (L.loopAt o).Nonidentity => (L.loopAt o).left a.val) :=
        { A := A, B := B,
          disjoint := Set.disjoint_left.mpr (fun a ha hb => Finset.disjoint_left.mp hd ha hb),
          Atwo := hAt, Btwo := hBt, Atrans := hA, Btrans := hB, radial := hr }
      exact ⟨L.witnessFromLoop o W⟩
    · simp only [NoTransitivePair, not_forall, not_imp, not_not] at hno
      obtain ⟨a, b, ha, hb, hab, ht⟩ := hno
      have he : L.identity ∉ ({a, b} : Finset ι) := by simp [Ne.symm ha, Ne.symm hb]
      have hcard : ({a, b} : Finset ι).card = 2 := Finset.card_pair hab
      have hS := L.supports_of_small_transitive o ({a, b} : Finset ι) he
        (by omega) (by omega) ht
      exact ⟨L.witnessOfContactSupports o hS hm⟩
  · have hrange : Fintype.card Ω = 6 ∨ Fintype.card Ω = 7 ∨ 9 ≤ Fintype.card Ω := by omega
    obtain ⟨A, B, hS, _⟩ := L.exists_radial_supports_nonexceptional (K := k) o hrange
    exact ⟨L.witnessOfContactSupports o hS hm⟩

end Sunlet.NormalizedLatinSystem
