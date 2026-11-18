module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Finite graded character algebras inside a genuine rational-function field

This is a general algebraic dictionary. An injective Laurent-character map
induces an injective map from the actual degree-exponent semigroup algebra.
Its image is proved to consist precisely of finite graded sums whose every
coefficient is a character polynomial with the stated support. Thus applying
this dictionary to genuine global-section values is an algebra isomorphism,
not a definition of the section ring by the conclusion.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Unimodular.GraphicSectionRing.GradedCharacters

variable {K F M : Type*} [CommRing K] [CommRing F] [Algebra K F] [AddCommMonoid M]
  (S : AddSubmonoid (ℕ × M)) (φ : AddMonoidAlgebra K M →ₐ[K] F)

/-- The literal inclusion of the degree-exponent semigroup. -/
def ambient : AddMonoidAlgebra K S →ₐ[K] AddMonoidAlgebra K (ℕ × M) :=
  AddMonoidAlgebra.mapDomainAlgHom K K S.subtype

theorem ambient_injective : Function.Injective (ambient (K := K) S) :=
  AddMonoidAlgebra.mapDomain_injective Subtype.val_injective

/-- Evaluate the Laurent coefficient while retaining the actual nonnegative degree. -/
def evaluation : AddMonoidAlgebra K S →ₐ[K] AddMonoidAlgebra F ℕ :=
  (AddMonoidAlgebra.mapAlgHom ℕ φ).comp
    ((AddMonoidAlgebra.curryAlgEquiv K).toAlgHom.comp (ambient S))

@[simp] theorem curry_coefficient (p : AddMonoidAlgebra K (ℕ × M)) (d : ℕ) (m : M) :
    ((AddMonoidAlgebra.curryAlgEquiv K p).coeff d).coeff m = p.coeff (d, m) := rfl

@[simp] theorem evaluation_single (z : S) (c : K) :
    evaluation S φ (AddMonoidAlgebra.single z c) =
      AddMonoidAlgebra.single z.val.1 (φ (AddMonoidAlgebra.single z.val.2 c)) := by
  change (AddMonoidAlgebra.mapAlgHom ℕ φ)
    (AddMonoidAlgebra.curryAlgEquiv K
      (AddMonoidAlgebra.mapDomain S.subtype (AddMonoidAlgebra.single z c))) = _
  rw [AddMonoidAlgebra.mapDomain_single]
  change (AddMonoidAlgebra.mapAlgHom ℕ φ)
    (AddMonoidAlgebra.curryAlgEquiv K
      (AddMonoidAlgebra.single (z.val.1, z.val.2) c)) = _
  rw [AddMonoidAlgebra.curryAlgEquiv_single, AddMonoidAlgebra.mapAlgHom_single]

theorem evaluation_injective (hφ : Function.Injective φ) :
    Function.Injective (evaluation S φ) := by
  intro p q h
  apply ambient_injective S
  apply (AddMonoidAlgebra.curryAlgEquiv K).injective
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro d
  apply hφ
  have hd := congrArg (fun a : AddMonoidAlgebra F ℕ => a.coeff d) h
  simpa only [evaluation, AlgHom.comp_apply, AddMonoidAlgebra.coeff_mapAlgHom,
    AlgEquiv.toAlgHom_apply] using hd

/-- Exact image of the semigroup inclusion, expressed by ordinary support. -/
theorem mem_range_ambient (p : AddMonoidAlgebra K (ℕ × M)) :
    p ∈ Set.range (ambient (K := K) S) ↔ ∀ z ∉ S, p.coeff z = 0 := by
  have h := Finsupp.mem_range_mapDomain_iff (M := K)
    (f := (Subtype.val : S → ℕ × M)) Subtype.val_injective p.coeff
  have hr : Set.range (Subtype.val : S → ℕ × M) = S := Subtype.range_coe
  rw [hr] at h
  constructor
  · rintro ⟨f, rfl⟩
    exact h.mp ⟨f.coeff, rfl⟩
  · intro hp
    obtain ⟨f, hf⟩ := h.mpr hp
    refine ⟨AddMonoidAlgebra.ofCoeff f, ?_⟩
    apply AddMonoidAlgebra.coeff_injective
    exact hf

/-- The image consists exactly of finite sums with the specified supported
Laurent-character coefficients in every degree. -/
theorem mem_range_evaluation (hφ : Function.Injective φ) (p : AddMonoidAlgebra F ℕ) :
    p ∈ Set.range (evaluation S φ) ↔
      ∀ d, ∃ q : AddMonoidAlgebra K M,
        (∀ m, (d, m) ∉ S → q.coeff m = 0) ∧ φ q = p.coeff d := by
  constructor
  · rintro ⟨f, rfl⟩ d
    let q := (AddMonoidAlgebra.curryAlgEquiv K (ambient S f)).coeff d
    refine ⟨q, ?_, ?_⟩
    · intro m hm
      exact (mem_range_ambient S (ambient S f)).mp ⟨f, rfl⟩ (d, m) hm
    · simp only [evaluation, AlgHom.comp_apply, AddMonoidAlgebra.coeff_mapAlgHom]
      rfl
  · intro hp
    have hr : p.coeff ∈ Set.range (Finsupp.mapRange φ (map_zero φ)) := by
      rw [Finsupp.range_mapRange]
      intro d
      obtain ⟨q, _, hq⟩ := hp d
      exact ⟨q, hq⟩
    obtain ⟨a, ha⟩ := hr
    let p₀ : AddMonoidAlgebra (AddMonoidAlgebra K M) ℕ := AddMonoidAlgebra.ofCoeff a
    let p₁ := (AddMonoidAlgebra.curryAlgEquiv K).symm p₀
    have hp₁ : p₁ ∈ Set.range (ambient (K := K) S) := by
      apply (mem_range_ambient S p₁).mpr
      rintro ⟨d, m⟩ hm
      obtain ⟨q, hq, heq⟩ := hp d
      have he : a d = q := hφ (by
        have had := congrArg (fun b : ℕ →₀ F => b d) ha
        exact had.trans heq.symm)
      have hc := curry_coefficient p₁ d m
      rw [show AddMonoidAlgebra.curryAlgEquiv K p₁ = p₀ from
        (AddMonoidAlgebra.curryAlgEquiv K).apply_symm_apply p₀] at hc
      change (a d).coeff m = p₁.coeff (d,m) at hc
      rw [← hc, he]
      exact hq m hm
    obtain ⟨f, hf⟩ := hp₁
    refine ⟨f, ?_⟩
    apply AddMonoidAlgebra.coeff_injective
    ext d
    simp only [evaluation, AlgHom.comp_apply, AddMonoidAlgebra.coeff_mapAlgHom, hf]
    change φ ((AddMonoidAlgebra.curryAlgEquiv K p₁).coeff d) = p.coeff d
    rw [show AddMonoidAlgebra.curryAlgEquiv K p₁ = p₀ from
      (AddMonoidAlgebra.curryAlgEquiv K).apply_symm_apply p₀]
    exact congrArg (fun b : ℕ →₀ F => b d) ha

/-- A proved algebra equivalence with any independently defined graded ring
whose actual coefficient spaces have the stated character dictionary. -/
def equivActual (hφ : Function.Injective φ) (T : Subalgebra K (AddMonoidAlgebra F ℕ))
    (hT : ∀ p, p ∈ T ↔ ∀ d, ∃ q : AddMonoidAlgebra K M,
      (∀ m, (d, m) ∉ S → q.coeff m = 0) ∧ φ q = p.coeff d) :
    AddMonoidAlgebra K S ≃ₐ[K] T :=
  AlgEquiv.ofBijective
    ((evaluation S φ).codRestrict T (fun p =>
      (hT _).mpr ((mem_range_evaluation S φ hφ _).mp ⟨p, rfl⟩)))
    ⟨fun p q h => evaluation_injective S φ hφ (congrArg Subtype.val h), by
      intro p
      obtain ⟨q, hq⟩ := (mem_range_evaluation S φ hφ p.val).mpr ((hT p.val).mp p.property)
      exact ⟨q, Subtype.ext hq⟩⟩

#print axioms evaluation_injective
#print axioms mem_range_evaluation
#print axioms equivActual

end Unimodular.GraphicSectionRing.GradedCharacters

#check Unimodular.GraphicSectionRing.GradedCharacters.equivActual
