module

public import sunlet.contact_development

/-! Uncompiled continuation: exact transport of finite permutation supports.

The source proves statements about the actual image finsets, generated orbit
relation, and sparse differential. It supplies no existence assumption for a
support. The consolidated ContactDevelopment core must pass before this module
can be checked; no checked-release status is asserted for this file.
-/

@[expose] public section
noncomputable section

namespace Sunlet.SupportTransport

variable {ι ι' Ω Ω' : Type*} [DecidableEq ι] [DecidableEq ι']

def mapSupport (ec : ι' ≃ ι) (A : Finset ι') : Finset ι :=
  A.map ec.toEmbedding

@[simp] theorem mem_mapSupport (ec : ι' ≃ ι) (A : Finset ι') (a : ι) :
    a ∈ mapSupport ec A ↔ ec.symm a ∈ A := by
  constructor
  · intro h
    obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp h
    change ec.symm (ec a') ∈ A
    simpa only [Equiv.symm_apply_apply] using ha'
  · intro h
    exact Finset.mem_map.mpr ⟨ec.symm a, h, ec.apply_symm_apply a⟩

@[simp] theorem apply_mem_mapSupport (ec : ι' ≃ ι) (A : Finset ι') (a : ι') :
    ec a ∈ mapSupport ec A ↔ a ∈ A := by
  rw [mem_mapSupport, Equiv.symm_apply_apply]

@[simp] theorem preimage_coe_mapSupport (ec : ι' ≃ ι) (A : Finset ι') :
    ec ⁻¹' (mapSupport ec A : Set ι) = (A : Set ι') := by
  ext a
  exact apply_mem_mapSupport ec A a

@[simp] theorem card_mapSupport (ec : ι' ≃ ι) (A : Finset ι') :
    (mapSupport ec A).card = A.card := Finset.card_map _

theorem nonempty_mapSupport (ec : ι' ≃ ι) (A : Finset ι') (hA : A.Nonempty) :
    (mapSupport ec A).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  exact ⟨ec a, (apply_mem_mapSupport ec A a).mpr ha⟩

theorem disjoint_mapSupport (ec : ι' ≃ ι) (A B : Finset ι')
    (hAB : Disjoint A B) : Disjoint (mapSupport ec A) (mapSupport ec B) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  exact Finset.disjoint_left.mp hAB
    ((mem_mapSupport ec A a).mp ha) ((mem_mapSupport ec B a).mp hb)

section Permutations

variable [Fintype Ω] [Fintype Ω'] [DecidableEq Ω] [DecidableEq Ω']

/-- Every edge of the coordinate permutation system is an actual edge of
the relabelled system, and equivalence closure preserves this fact. -/
theorem colorConnected_map (ec : ι' ≃ ι) (ev : Ω' ≃ Ω)
    (π : ι → Equiv.Perm Ω) (π' : ι' → Equiv.Perm Ω')
    (hπ : ∀ a x, ev (π' a x) = π (ec a) (ev x)) (A : Finset ι')
    {x y : Ω'} (h : ColorConnected π' (A : Set ι') x y) :
    ColorConnected π (mapSupport ec A : Set ι) (ev x) (ev y) := by
  induction h with
  | rel x y h =>
      obtain ⟨a, ha, he⟩ := h
      apply Relation.EqvGen.rel
      exact ⟨ec a, (apply_mem_mapSupport ec A a).mpr ha,
        (hπ a x).symm.trans (congrArg ev he)⟩
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

theorem transitive_map (ec : ι' ≃ ι) (ev : Ω' ≃ Ω)
    (π : ι → Equiv.Perm Ω) (π' : ι' → Equiv.Perm Ω')
    (hπ : ∀ a x, ev (π' a x) = π (ec a) (ev x)) (A : Finset ι')
    (hA : TransitiveFamily π' (A : Set ι')) :
    TransitiveFamily π (mapSupport ec A : Set ι) := by
  intro x y
  simpa only [Equiv.apply_symm_apply] using
    colorConnected_map ec ev π π' hπ A (hA (ev.symm x) (ev.symm y))

/-- Distinct permutations remain distinct under simultaneous point and
color relabelling; distinct color names alone are not used as a substitute. -/
theorem permutation_ne_map (ec : ι' ≃ ι) (ev : Ω' ≃ Ω)
    (π : ι → Equiv.Perm Ω) (π' : ι' → Equiv.Perm Ω')
    (hπ : ∀ a x, ev (π' a x) = π (ec a) (ev x)) {a b : ι'}
    (hab : π' a ≠ π' b) : π (ec a) ≠ π (ec b) := by
  intro he
  apply hab
  ext x
  apply ev.injective
  rw [hπ, hπ, he]

theorem two_map (ec : ι' ≃ ι) (ev : Ω' ≃ Ω)
    (π : ι → Equiv.Perm Ω) (π' : ι' → Equiv.Perm Ω')
    (hπ : ∀ a x, ev (π' a x) = π (ec a) (ev x)) (A : Finset ι')
    (hA : ∃ a ∈ A, ∃ b ∈ A, π' a ≠ π' b) :
    ∃ a ∈ mapSupport ec A, ∃ b ∈ mapSupport ec A, π a ≠ π b := by
  obtain ⟨a, ha, b, hb, hab⟩ := hA
  exact ⟨ec a, (apply_mem_mapSupport ec A a).mpr ha,
    ec b, (apply_mem_mapSupport ec A b).mpr hb,
    permutation_ne_map ec ev π π' hπ hab⟩

theorem derangement_map (ec : ι' ≃ ι) (ev : Ω' ≃ Ω)
    (π : ι → Equiv.Perm Ω) (π' : ι' → Equiv.Perm Ω')
    (hπ : ∀ a x, ev (π' a x) = π (ec a) (ev x))
    (hder : ∀ a x, π' a x ≠ x) : ∀ a x, π a x ≠ x := by
  intro a x hx
  apply hder (ec.symm a) (ev.symm x)
  apply ev.injective
  simpa only [hπ, Equiv.apply_symm_apply] using hx

section Contact

variable {K : Type*} [Field K] [CharZero K]
open ToricDifferential

/-- A radial theorem for explicit finite coordinate supports transports to
their actual image supports in the original color and point types. -/
theorem radial_map (ec : ι' ≃ ι) (ev : Ω' ≃ Ω)
    (π : ι → Equiv.Perm Ω) (π' : ι' → Equiv.Perm Ω')
    (o : Ω) (o' : Ω') (ho : ev o' = o)
    (hπ : ∀ a x, ev (π' a x) = π (ec a) (ev x)) (A B : Finset ι')
    (hnew : ∀ v : Variation K ι' Ω', v.2 o' = 0 →
      (∀ w, hessian π' (sparseCoefficients (A : Set ι')) (fun _ => 1) v w ∈
        Contact.tangentSpan π' o' (A : Set ι') (B : Set ι')) →
      ∃ lam : K, v = lam • (sparseCoefficients (A : Set ι'), (0 : Ω' → K)))
    (v : Variation K ι Ω) (hbase : v.2 o = 0)
    (hcontact : ∀ w, hessian π (sparseCoefficients (mapSupport ec A : Set ι))
      (fun _ => 1) v w ∈ Contact.tangentSpan π o
        (mapSupport ec A : Set ι) (mapSupport ec B : Set ι)) :
    ∃ lam : K, v = lam • (sparseCoefficients (mapSupport ec A : Set ι), (0 : Ω → K)) := by
  classical
  refine ContactReindex.radial_transport ec ev π π' o o' ho hπ
    (mapSupport ec A : Set ι) (mapSupport ec B : Set ι) ?_ v hbase hcontact
  have hcoef (d₁ : DecidablePred (· ∈ ec ⁻¹' (mapSupport ec A : Set ι)))
      (d₂ : DecidablePred (· ∈ (A : Set ι'))) :
      @ToricDifferential.sparseCoefficients K ι' _
        (ec ⁻¹' (mapSupport ec A : Set ι)) d₁ =
      @ToricDifferential.sparseCoefficients K ι' _ (A : Set ι') d₂ := by
    funext a
    simp only [ToricDifferential.sparseCoefficients, Set.mem_preimage,
      Finset.mem_coe, apply_mem_mapSupport]
  intro v' hv' hc'
  have hc'' : ∀ w, hessian π' (sparseCoefficients (A : Set ι'))
      (fun _ => 1) v' w ∈ Contact.tangentSpan π' o' (A : Set ι') (B : Set ι') := by
    simpa only [hcoef, preimage_coe_mapSupport] using hc'
  obtain ⟨lam, he⟩ := hnew v' hv' hc''
  exact ⟨lam, by simpa only [hcoef] using he⟩

end Contact
end Permutations
end Sunlet.SupportTransport
