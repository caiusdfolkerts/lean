module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Homology of a folded three-term complex

For a genuine complex `A₂ → A₁ → A₀`, place its three terms in one module
`A₀ × (A₁ × A₂)` and retain the original differential. The homology of this
square-zero endomorphism is canonically the product of the cokernel at `A₀`,
the usual middle homology, and the kernel at `A₂`.

All homology groups below are actual kernel/image quotients. The final
comparison also identifies this quotient with Mathlib's categorical homology.
-/

@[expose] public section
noncomputable section

universe u v

namespace PaperVerification.FoldedComplexHomology

open CategoryTheory

variable {R : Type u} [Ring R]
  {A₀ A₁ A₂ : Type v}
  [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
  [Module R A₀] [Module R A₁] [Module R A₂]
  (d₁ : A₁ →ₗ[R] A₀) (d₂ : A₂ →ₗ[R] A₁)

/-- The original two differentials, folded into one square-zero map. -/
def differential : (A₀ × (A₁ × A₂)) →ₗ[R] A₀ × (A₁ × A₂) where
  toFun x := (d₁ x.2.1, (d₂ x.2.2, 0))
  map_add' x y := by simp
  map_smul' r x := by simp

@[simp] theorem differential_apply (x : A₀ × (A₁ × A₂)) :
    differential d₁ d₂ x = (d₁ x.2.1, (d₂ x.2.2, 0)) := rfl

/-- Squaring the folded map is exactly the original complex relation. -/
theorem differential_sq (h : d₁.comp d₂ = 0) :
    (differential d₁ d₂).comp (differential d₁ d₂) = 0 := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · exact LinearMap.congr_fun h x.2.2
  · apply Prod.ext
    · exact d₂.map_zero
    · rfl

variable (h : d₁.comp d₂ = 0)

/-- The original second differential with codomain restricted to cycles. -/
def middleToCycles : A₂ →ₗ[R] LinearMap.ker d₁ :=
  d₂.codRestrict _ (fun x ↦ LinearMap.congr_fun h x)

/-- The folded differential with codomain restricted to its actual kernel. -/
def toCycles : (A₀ × (A₁ × A₂)) →ₗ[R] LinearMap.ker (differential d₁ d₂) :=
  (differential d₁ d₂).codRestrict _
    (fun x ↦ LinearMap.congr_fun (differential_sq d₁ d₂ h) x)

/-- The middle component of a folded cycle is an original middle cycle. -/
def middleCycle : LinearMap.ker (differential d₁ d₂) →ₗ[R] LinearMap.ker d₁ :=
  (((LinearMap.fst R A₁ A₂).comp (LinearMap.snd R A₀ (A₁ × A₂))).comp
    (LinearMap.ker (differential d₁ d₂)).subtype).codRestrict _ (fun x ↦ by
      have hx := x.property
      change differential d₁ d₂ x.val = 0 at hx
      exact congrArg Prod.fst hx)

/-- The last component of a folded cycle belongs to the original last kernel. -/
def lastCycle : LinearMap.ker (differential d₁ d₂) →ₗ[R] LinearMap.ker d₂ :=
  (((LinearMap.snd R A₁ A₂).comp (LinearMap.snd R A₀ (A₁ × A₂))).comp
    (LinearMap.ker (differential d₁ d₂)).subtype).codRestrict _ (fun x ↦ by
      have hx := x.property
      change differential d₁ d₂ x.val = 0 at hx
      exact congrArg (fun y : A₀ × (A₁ × A₂) ↦ y.2.1) hx)

/-- The canonical comparison on cycles, using the original quotient maps. -/
def comparison : LinearMap.ker (differential d₁ d₂) →ₗ[R]
    (A₀ ⧸ LinearMap.range d₁) ×
      ((LinearMap.ker d₁ ⧸ LinearMap.range (middleToCycles d₁ d₂ h)) ×
        LinearMap.ker d₂) :=
  ((LinearMap.range d₁).mkQ.comp
    ((LinearMap.fst R A₀ (A₁ × A₂)).comp
      (LinearMap.ker (differential d₁ d₂)).subtype)).prod
    (((LinearMap.range (middleToCycles d₁ d₂ h)).mkQ.comp
      (middleCycle d₁ d₂)).prod (lastCycle d₁ d₂))

/-- Every triple of original homology classes has a folded cycle representative. -/
theorem comparison_surjective : Function.Surjective (comparison d₁ d₂ h) := by
  rintro ⟨a, b, c⟩
  obtain ⟨a, rfl⟩ := (LinearMap.range d₁).mkQ_surjective a
  obtain ⟨b, rfl⟩ := (LinearMap.range (middleToCycles d₁ d₂ h)).mkQ_surjective b
  refine ⟨⟨(a, (b.val, c.val)), ?_⟩, ?_⟩
  · change (d₁ b.val, (d₂ c.val, 0)) = (0, (0, 0))
    exact Prod.ext b.property (Prod.ext c.property rfl)
  · rfl

/-- A folded cycle maps to zero precisely when it is a folded boundary. -/
theorem comparison_ker :
    LinearMap.ker (comparison d₁ d₂ h) = LinearMap.range (toCycles d₁ d₂ h) := by
  ext x
  constructor
  · intro hx
    change comparison d₁ d₂ h x = 0 at hx
    have h₀ : (LinearMap.range d₁).mkQ x.val.1 = 0 := congrArg Prod.fst hx
    have h₁ : (LinearMap.range (middleToCycles d₁ d₂ h)).mkQ
        (middleCycle d₁ d₂ x) = 0 :=
      congrArg (fun y ↦ y.2.1) hx
    have h₂ : lastCycle d₁ d₂ x = 0 := congrArg (fun y ↦ y.2.2) hx
    obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).mp h₀
    obtain ⟨c, hc⟩ := (Submodule.Quotient.mk_eq_zero _).mp h₁
    refine ⟨(0, (b, c)), ?_⟩
    apply Subtype.ext
    exact Prod.ext hb (Prod.ext (congrArg Subtype.val hc) (congrArg Subtype.val h₂).symm)
  · rintro ⟨y, rfl⟩
    change comparison d₁ d₂ h (toCycles d₁ d₂ h y) = 0
    apply Prod.ext
    · exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨y.2.1, rfl⟩
    · apply Prod.ext
      · exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨y.2.2, rfl⟩
      · apply Subtype.ext
        rfl

/-- The actual kernel/image quotient of the folded differential. -/
abbrev Homology :=
  LinearMap.ker (differential d₁ d₂) ⧸ LinearMap.range (toCycles d₁ d₂ h)

/-- The canonical linear equivalence between folded and original homology. -/
def homologyEquiv : Homology d₁ d₂ h ≃ₗ[R]
    (A₀ ⧸ LinearMap.range d₁) ×
      ((LinearMap.ker d₁ ⧸ LinearMap.range (middleToCycles d₁ d₂ h)) ×
        LinearMap.ker d₂) :=
  (Submodule.quotEquivOfEq _ _ (comparison_ker d₁ d₂ h).symm).trans
    ((comparison d₁ d₂ h).quotKerEquivOfSurjective (comparison_surjective d₁ d₂ h))

/-- The equivalence sends the class of a cycle to its three original classes. -/
@[simp] theorem homologyEquiv_mk (x : LinearMap.ker (differential d₁ d₂)) :
    homologyEquiv d₁ d₂ h (Submodule.Quotient.mk x) = comparison d₁ d₂ h x := by
  simp [homologyEquiv]

/-- The same folded differential as an actual short complex of modules. -/
def shortComplex : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.moduleCatMk (differential d₁ d₂) (differential d₁ d₂)
    (differential_sq d₁ d₂ h)

/-- Mathlib's categorical homology has the same canonical decomposition. -/
def categoricalHomologyEquiv : (shortComplex d₁ d₂ h).homology ≃ₗ[R]
    (A₀ ⧸ LinearMap.range d₁) ×
      ((LinearMap.ker d₁ ⧸ LinearMap.range (middleToCycles d₁ d₂ h)) ×
        LinearMap.ker d₂) :=
  (shortComplex d₁ d₂ h).moduleCatHomologyIso.toLinearEquiv.trans
    (homologyEquiv d₁ d₂ h)

section Dimension

variable {K : Type u} [DivisionRing K]
  {V₀ V₁ V₂ : Type v}
  [AddCommGroup V₀] [AddCommGroup V₁] [AddCommGroup V₂]
  [Module K V₀] [Module K V₁] [Module K V₂]
  [Module.Finite K V₀] [Module.Finite K V₁] [Module.Finite K V₂]
  (f₁ : V₁ →ₗ[K] V₀) (f₂ : V₂ →ₗ[K] V₁) (hf : f₁.comp f₂ = 0)

/-- Dimensions add because the actual homology groups are linearly equivalent. -/
theorem finrank_homology :
    Module.finrank K (Homology f₁ f₂ hf) =
      Module.finrank K (V₀ ⧸ LinearMap.range f₁) +
        (Module.finrank K
          (LinearMap.ker f₁ ⧸ LinearMap.range (middleToCycles f₁ f₂ hf)) +
          Module.finrank K (LinearMap.ker f₂)) := by
  rw [(homologyEquiv f₁ f₂ hf).finrank_eq]
  simp only [Module.finrank_prod]

/-- The same dimension equality for Mathlib's categorical homology object. -/
theorem finrank_categoricalHomology :
    Module.finrank K (shortComplex f₁ f₂ hf).homology =
      Module.finrank K (V₀ ⧸ LinearMap.range f₁) +
        (Module.finrank K
          (LinearMap.ker f₁ ⧸ LinearMap.range (middleToCycles f₁ f₂ hf)) +
          Module.finrank K (LinearMap.ker f₂)) := by
  rw [(categoricalHomologyEquiv f₁ f₂ hf).finrank_eq]
  simp only [Module.finrank_prod]

/-- The Euler identity for the three actual homology quotients. -/
theorem middle_finrank_euler :
    Module.finrank K (V₀ ⧸ LinearMap.range f₁) + Module.finrank K (LinearMap.ker f₂) +
        Module.finrank K V₁ =
      Module.finrank K
        (LinearMap.ker f₁ ⧸ LinearMap.range (middleToCycles f₁ f₂ hf)) +
        (Module.finrank K V₀ + Module.finrank K V₂) := by
  have h₀ := (LinearMap.range f₁).finrank_quotient_add_finrank
  have h₁ := (LinearMap.range (middleToCycles f₁ f₂ hf)).finrank_quotient_add_finrank
  have h₂ := f₁.finrank_range_add_finrank_ker
  have h₃ := (middleToCycles f₁ f₂ hf).finrank_range_add_finrank_ker
  have hk : LinearMap.ker (middleToCycles f₁ f₂ hf) = LinearMap.ker f₂ :=
    LinearMap.ker_codRestrict _ _ _
  rw [hk] at h₃
  omega

/-- For a complex with zero Euler characteristic, total folded homology has
twice the sum of the dimensions of its two end homology groups. -/
theorem finrank_homology_of_euler_zero
    (hdim : Module.finrank K V₁ = Module.finrank K V₀ + Module.finrank K V₂) :
    Module.finrank K (Homology f₁ f₂ hf) =
      2 * (Module.finrank K (V₀ ⧸ LinearMap.range f₁) +
        Module.finrank K (LinearMap.ker f₂)) := by
  have he := middle_finrank_euler f₁ f₂ hf
  rw [finrank_homology]
  omega

/-- When the two end homology groups have equal dimension, the total is four
times the dimension of the original cokernel. The equal dimension is the
separate duality input in the paper's two-generator exterior complex. -/
theorem finrank_homology_four_cokernel
    (hdim : Module.finrank K V₁ = Module.finrank K V₀ + Module.finrank K V₂)
    (hdual : Module.finrank K (LinearMap.ker f₂) =
      Module.finrank K (V₀ ⧸ LinearMap.range f₁)) :
    Module.finrank K (Homology f₁ f₂ hf) =
      4 * Module.finrank K (V₀ ⧸ LinearMap.range f₁) := by
  rw [finrank_homology_of_euler_zero f₁ f₂ hf hdim, hdual]
  omega

end Dimension

end PaperVerification.FoldedComplexHomology
