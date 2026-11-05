module

public import PaperVerification.FermionOddSplitting
public import PaperVerification.FermionTwoSidedBasisSpan

/-!
# Descending an actual odd contraction through a two-sided ideal

A parity-twisted Leibniz rule is sufficient: the involution and contraction
are checked on the real generators, and two-sided span induction proves
stability of the complete ideal. No stability of a presentation is assumed
without this check in the concrete application.

-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion

variable {R A Q : Type*} [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup Q] [Module R Q]

/-- Stability under an algebra map propagates from actual ideal generators. -/
theorem parity_span_stable (Γ : A →ₐ[R] A) (s : Set A)
    (hs : ∀ x ∈ s,Γ x ∈ TwoSidedIdeal.span s) :
    ∀ x ∈ TwoSidedIdeal.span s,Γ x ∈ TwoSidedIdeal.span s := by
  have h : TwoSidedIdeal.span s ≤ (TwoSidedIdeal.span s).comap Γ.toRingHom := by
    apply TwoSidedIdeal.span_le.mpr
    intro x hx
    exact (TwoSidedIdeal.mem_comap Γ.toRingHom).mpr (hs x hx)
  intro x hx
  exact (TwoSidedIdeal.mem_comap Γ.toRingHom).mp (h hx)

/-- The twisted derivative preserves the whole two-sided ideal. -/
theorem twistedDerivation_span_stable (Γ : A →ₐ[R] A) (D : Module.End R A)
    (hD : ∀ x y,D (x*y)=D x*y+Γ x*D y) (s : Set A)
    (hΓs : ∀ x ∈ s,Γ x ∈ TwoSidedIdeal.span s)
    (hDs : ∀ x ∈ s,D x ∈ TwoSidedIdeal.span s) :
    ∀ x ∈ TwoSidedIdeal.span s,D x ∈ TwoSidedIdeal.span s := by
  intro x hx
  induction hx using TwoSidedIdeal.span_induction with
  | mem x hx => exact hDs x hx
  | zero => rw [map_zero]; exact TwoSidedIdeal.zero_mem _
  | add x y hx hy ihx ihy => rw [map_add]; exact TwoSidedIdeal.add_mem _ ihx ihy
  | neg x hx ih => rw [map_neg]; exact TwoSidedIdeal.neg_mem _ ih
  | left_absorb a x hx ih =>
      rw [hD]
      exact TwoSidedIdeal.add_mem _
        ((TwoSidedIdeal.span s).mul_mem_left _ _ hx)
        ((TwoSidedIdeal.span s).mul_mem_left _ _ ih)
  | right_absorb a x hx ih =>
      rw [hD]
      exact TwoSidedIdeal.add_mem _
        ((TwoSidedIdeal.span s).mul_mem_right _ _ ih)
        ((TwoSidedIdeal.span s).mul_mem_right _ _
          (parity_span_stable Γ s hΓs x hx))

/-- Descend an actual linear operator using the original surjective quotient
map and its actual stable kernel. -/
def descendEnd (q : A →ₗ[R] Q) (hq : Function.Surjective q)
    (D : Module.End R A) (hstable : ∀ x ∈ q.ker,D x ∈ q.ker) : Module.End R Q :=
  q.liftOfSurjective hq ⟨q.comp D,fun x hx ↦ hstable x hx⟩

@[simp] theorem descendEnd_apply (q : A →ₗ[R] Q) (hq : Function.Surjective q)
    (D : Module.End R A) (hstable : ∀ x ∈ q.ker,D x ∈ q.ker) (x : A) :
    descendEnd q hq D hstable (q x)=q (D x) :=
  LinearMap.equivOfSurjective_apply _ _

theorem descendEnd_square (q : A →ₗ[R] Q) (hq : Function.Surjective q)
    (D : Module.End R A) (hstable : ∀ x ∈ q.ker,D x ∈ q.ker) (hD : D*D=0) :
    descendEnd q hq D hstable*descendEnd q hq D hstable=0 := by
  ext y
  obtain ⟨x,rfl⟩ := hq y
  simp only [Module.End.mul_apply,descendEnd_apply,LinearMap.zero_apply]
  have he : D (D x)=0 := LinearMap.congr_fun hD x
  rw [he,map_zero]

theorem descendEnd_anticommutator (q : A →ₗ[R] Q) (hq : Function.Surjective q)
    (C D : Module.End R A)
    (hC : ∀ x ∈ q.ker,C x ∈ q.ker) (hD : ∀ x ∈ q.ker,D x ∈ q.ker)
    (hCD : D*C+C*D=1) :
    descendEnd q hq D hD*descendEnd q hq C hC+
      descendEnd q hq C hC*descendEnd q hq D hD=1 := by
  ext y
  obtain ⟨x,rfl⟩ := hq y
  simp only [Module.End.mul_apply,LinearMap.add_apply,descendEnd_apply,Module.End.one_apply]
  rw [←map_add]
  have he : D (C x)+C (D x)=x := LinearMap.congr_fun hCD x
  rw [he]

/-- The actual ideal of a normal odd element is its left-multiplication
image as a coefficient submodule. This is used only after proving the normal
commutation identity for the concrete exterior generator. -/
theorem normal_singleton_span_eq_range (Γ : A →ₐ[R] A) (η : A)
    (hnormal : ∀ x,x*η=η*Γ x) :
    twoSidedIdealSubmodule (K := R) (TwoSidedIdeal.span ({η} : Set A)) =
      (LinearMap.mulLeft R η).range := by
  let N := (LinearMap.mulLeft R η).range
  let H : TwoSidedIdeal A := TwoSidedIdeal.mk' (N : Set A) N.zero_mem
    (fun hx hy ↦ N.add_mem hx hy) (fun hx ↦ N.neg_mem hx)
    (by
      rintro a x ⟨y,rfl⟩
      refine ⟨Γ a*y,?_⟩
      change η*(Γ a*y)=a*(η*y)
      rw [←mul_assoc,←hnormal,mul_assoc])
    (by
      rintro x a ⟨y,rfl⟩
      exact ⟨y*a,(mul_assoc η y a).symm⟩)
  have hHN (z : A) : z ∈ H ↔ z ∈ N := by
    exact TwoSidedIdeal.mem_mk' _ _ _ _ _ _ z
  apply le_antisymm
  · have hs : TwoSidedIdeal.span ({η} : Set A) ≤ H := by
      apply TwoSidedIdeal.span_le.mpr
      intro x hx
      have hxη : x = η := Set.mem_singleton_iff.mp hx
      subst x
      apply (hHN η).mpr
      exact ⟨1, by change η * 1 = η; exact mul_one η⟩
    intro x hx
    exact (hHN x).mp (hs ((mem_twoSidedIdealSubmodule _ _).mp hx))
  · rintro x ⟨y,rfl⟩
    exact (TwoSidedIdeal.span ({η} : Set A)).mul_mem_right _ _
      (TwoSidedIdeal.subset_span (Set.mem_singleton η))

end PaperVerification.Fermion
