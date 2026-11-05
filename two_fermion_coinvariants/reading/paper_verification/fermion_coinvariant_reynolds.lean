module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.Algebra.Divisibility.Units
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Reynolds reduction by the actual number of occupied indices

The central reduction is valid in any actual
algebra with a permutation action. It never assumes a sign-free monomial
permutation representation: algebra automorphisms act on the literal
products, so all exterior signs are retained. Fresh placements have the
same Reynolds sum by an actual transposition fixing the remaining support.
The multiplicity is a positive integer at most n, hence a unit when n! is.
Collision terms are an explicit lower-support obligation, not an axiom.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.Fermion.Coinvariants

section FiniteGroup

variable {R A G : Type*} [CommRing R] [Ring A] [Algebra R A]
  [Group G] [Fintype G]

/-- The unnormalized Reynolds operator, on the original representation. -/
def symmetrizer (ρ : G →* (A ≃ₐ[R] A)) : A →ₗ[R] A :=
  ∑ g,(ρ g).toLinearMap

@[simp] theorem symmetrizer_apply (ρ : G →* (A ≃ₐ[R] A)) (x : A) :
    symmetrizer ρ x=∑ g,ρ g x := by
  simp only [symmetrizer,LinearMap.sum_apply,AlgEquiv.toLinearMap_apply]

/-- Right translation of the full group sum does not change it. -/
theorem symmetrizer_map (ρ : G →* (A ≃ₐ[R] A)) (g : G) (x : A) :
    symmetrizer ρ (ρ g x)=symmetrizer ρ x := by
  rw [symmetrizer_apply,symmetrizer_apply]
  calc
    (∑ h,ρ h (ρ g x))=(∑ h,ρ (h*g) x) := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [map_mul,AlgEquiv.mul_apply]
    _=∑ h,ρ h x := Equiv.sum_comp (Equiv.mulRight g) (fun h ↦ ρ h x)

theorem symmetrizer_of_invariant (ρ : G →* (A ≃ₐ[R] A)) (x : A)
    (hx : ∀ g,ρ g x=x) : symmetrizer ρ x=(Fintype.card G : R) • x := by
  rw [symmetrizer_apply]
  simp only [hx,Finset.sum_const,Finset.card_univ]
  exact (Nat.cast_smul_eq_nsmul R _ _).symm

theorem symmetrizer_mem_of_mem (ρ : G →* (A ≃ₐ[R] A))
    (I : TwoSidedIdeal A) (hI : ∀ g x,x∈I → ρ g x∈I)
    {x : A} (hx : x∈I) : symmetrizer ρ x∈I := by
  rw [symmetrizer_apply]
  exact sum_mem (fun g hg ↦ hI g x hx)

/-- A two-sided ideal is closed under every base-ring scalar. -/
theorem ideal_smul_mem (I : TwoSidedIdeal A) (c : R) {x : A} (hx : x∈I) : c • x∈I := by
  rw [Algebra.smul_def]
  exact I.mul_mem_left _ _ hx

theorem ideal_mem_of_unit_smul_mem (I : TwoSidedIdeal A) {c : R}
    (hc : IsUnit c) {x : A} (hx : c • x∈I) : x∈I := by
  obtain ⟨u,rfl⟩ := hc
  have h := ideal_smul_mem I ((u⁻¹ : Rˣ) : R) hx
  simpa only [smul_smul,Units.inv_mul,one_smul] using h

/-- Actual invariants reduce to their group sums without assuming a field. -/
theorem invariant_mem_of_symmetrizer_mem (ρ : G →* (A ≃ₐ[R] A))
    (I : TwoSidedIdeal A) (hcard : IsUnit (Fintype.card G : R))
    {x : A} (hx : ∀ g,ρ g x=x) (havg : symmetrizer ρ x∈I) : x∈I := by
  rw [symmetrizer_of_invariant ρ x hx] at havg
  exact ideal_mem_of_unit_smul_mem I hcard havg

/-- If all stated generators are fixed, the original generated ideal is
preserved; no invariant-ideal equality is used. -/
theorem map_mem_span_of_fixed_generators (f : A →ₐ[R] A) (S : Set A)
    (hS : ∀ x∈S,f x=x) {x : A} (hx : x∈TwoSidedIdeal.span S) :
    f x∈TwoSidedIdeal.span S := by
  have hle : TwoSidedIdeal.span S≤(TwoSidedIdeal.span S).comap f.toRingHom := by
    apply TwoSidedIdeal.span_le.mpr
    intro y hy
    apply (TwoSidedIdeal.mem_comap f.toRingHom).mpr
    change f y∈TwoSidedIdeal.span S
    rw [hS y hy]
    exact TwoSidedIdeal.subset_span hy
  exact (TwoSidedIdeal.mem_comap f.toRingHom).mp (hle hx)

end FiniteGroup

section OccupiedIndices

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {n : ℕ}

/-- A transposition of two unoccupied positions fixes the remaining actual
product. It identifies their full Reynolds sums, including all odd signs. -/
theorem symmetrizer_fresh_equal
    (ρ : Equiv.Perm (Fin n) →* (A ≃ₐ[R] A))
    (b : Fin n → A) (hb : ∀ σ i,ρ σ (b i)=b (σ i))
    (S : Finset (Fin n)) (x : A)
    (hx : ∀ σ : Equiv.Perm (Fin n),(∀ i∈S,σ i=i) → ρ σ x=x)
    {i j : Fin n} (hi : i∉S) (hj : j∉S) :
    symmetrizer ρ (b i*x)=symmetrizer ρ (b j*x) := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap i j
  have hfix : ∀ k∈S,τ k=k := by
    intro k hk
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h; exact hi (h ▸ hk)
    · intro h; exact hj (h ▸ hk)
  have he : ρ τ (b i*x)=b j*x := by
    rw [map_mul,hb,hx τ hfix]
    simp only [τ,Equiv.swap_apply_left]
  calc
    symmetrizer ρ (b i*x)=symmetrizer ρ (ρ τ (b i*x)) :=
      (symmetrizer_map ρ τ (b i*x)).symm
    _=symmetrizer ρ (b j*x) := congrArg (symmetrizer ρ) he

/-- The decisive occupied-index step. The collision hypotheses concern the
explicit smaller support S. All fresh positions are counted exactly, and
invertibility is derived from the original n!-unit hypothesis. -/
theorem symmetrizer_fresh_mem
    (ρ : Equiv.Perm (Fin n) →* (A ≃ₐ[R] A))
    (I : TwoSidedIdeal A) (hI : ∀ σ x,x∈I → ρ σ x∈I)
    (hfac : IsUnit (n.factorial : R))
    (b : Fin n → A) (hb : ∀ σ i,ρ σ (b i)=b (σ i))
    (hblock : (∑ i,b i)∈I)
    (S : Finset (Fin n)) (x : A)
    (hx : ∀ σ : Equiv.Perm (Fin n),(∀ i∈S,σ i=i) → ρ σ x=x)
    (hcollision : ∀ i∈S,symmetrizer ρ (b i*x)∈I)
    (i : Fin n) (hi : i∉S) : symmetrizer ρ (b i*x)∈I := by
  let f : Fin n → A := fun j ↦ symmetrizer ρ (b j*x)
  have htotal : (∑ j,f j)∈I := by
    change (∑ j,symmetrizer ρ (b j*x))∈I
    rw [←map_sum,←Finset.sum_mul]
    exact symmetrizer_mem_of_mem ρ I hI (I.mul_mem_right _ _ hblock)
  have hcollisionSum : (∑ j∈S,f j)∈I :=
    sum_mem (fun j hj ↦ hcollision j hj)
  have hfresh : (∑ j∈Sᶜ,f j)∈I := by
    have h := I.sub_mem htotal hcollisionSum
    have he := Finset.sum_add_sum_compl S f
    rw [←he] at h
    simpa only [add_sub_cancel_left] using h
  have he : (∑ j∈Sᶜ,f j)=((Sᶜ).card : R) • symmetrizer ρ (b i*x) := by
    calc
      (∑ j∈Sᶜ,f j)=(∑ _j∈Sᶜ,symmetrizer ρ (b i*x)) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (symmetrizer_fresh_equal ρ b hb S x hx hi
          (Finset.mem_compl.mp hj)).symm
      _=((Sᶜ).card : R) • symmetrizer ρ (b i*x) := by
        rw [Finset.sum_const]
        exact (Nat.cast_smul_eq_nsmul R _ _).symm
  have hpos : 0<(Sᶜ).card := Finset.card_pos.mpr ⟨i,Finset.mem_compl.mpr hi⟩
  have hle : (Sᶜ).card≤n := by simpa only [Fintype.card_fin] using (Sᶜ).card_le_univ
  have hu : IsUnit ((Sᶜ).card : R) :=
    isUnit_of_dvd_unit (map_dvd (Nat.castRingHom R) (Nat.dvd_factorial hpos hle)) hfac
  rw [he] at hfresh
  exact ideal_mem_of_unit_smul_mem I hu hfresh

end OccupiedIndices
end PaperVerification.Fermion.Coinvariants
