module

public import PaperVerification.FoldedComplexHomology
public import PaperVerification.SquareZeroHomologyGrading
public import TauCeti.Algebra.Module.GradedModule.Shift
public import TauCeti.Algebra.Module.GradedModule.Prod

/-!
# The genuine graded homology of a folded three-term complex

Suppose `A₂ → A₁ → A₀` has differentials of internal degree zero. On
`A₀ × (A₁ × A₂)`, shift the last two gradings by one and two respectively.
The folded differential then has cohomological degree one. Its inherited
kernel/image quotient grading is identified with the original three
homology gradings, with exactly these shifts.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

namespace PaperVerification.FoldedComplexHomologyGrading

open FoldedComplexHomology

variable {R : Type u} [Ring R]
  {A₀ A₁ A₂ : Type v}
  [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
  [Module R A₀] [Module R A₁] [Module R A₂]
  (G₀ : TauCeti.InternalGrading R A₀)
  (G₁ : TauCeti.InternalGrading R A₁)
  (G₂ : TauCeti.InternalGrading R A₂)

/-- Total cohomological grading: the original internal degree minus the
position in the length-two complex. -/
def totalGrading : TauCeti.InternalGrading R (A₀ × (A₁ × A₂)) :=
  G₀.prod ((G₁.shift 1).prod (G₂.shift 2))

@[simp] theorem mem_totalGrading {p : ℤ} {x : A₀ × (A₁ × A₂)} :
    x ∈ (totalGrading G₀ G₁ G₂).piece p ↔
      x.1 ∈ G₀.piece p ∧ x.2.1 ∈ G₁.piece (p + 1) ∧
        x.2.2 ∈ G₂.piece (p + 2) := by
  simp only [totalGrading, TauCeti.InternalGrading.prod_piece,
    TauCeti.InternalGrading.shift_piece, Submodule.mem_prod]

variable (d₁ : A₁ →ₗ[R] A₀) (d₂ : A₂ →ₗ[R] A₁)
  (h : d₁.comp d₂ = 0)
  (hd₁ : TauCeti.LinearMap.IsHomogeneous d₁ G₁.piece G₀.piece 0)
  (hd₂ : TauCeti.LinearMap.IsHomogeneous d₂ G₂.piece G₁.piece 0)

include hd₁ hd₂ in
/-- Folding the internal degree-zero maps gives a differential of total
cohomological degree one. -/
theorem differential_homogeneous :
    TauCeti.LinearMap.IsHomogeneous (differential d₁ d₂)
      (totalGrading G₀ G₁ G₂).piece (totalGrading G₀ G₁ G₂).piece 1 := by
  intro p x hx
  obtain ⟨hx₀, hx₁, hx₂⟩ := (mem_totalGrading G₀ G₁ G₂).1 hx
  apply (mem_totalGrading G₀ G₁ G₂).2
  refine ⟨?_, ?_, (G₂.piece _).zero_mem⟩
  · simpa only [differential_apply, add_zero] using hd₁ hx₁
  · simpa [add_assoc] using hd₂ hx₂

/-- The actual folded homology, graded by its homogeneous cycles and
boundaries in the original total module. -/
def homologyGrading : TauCeti.InternalGrading R (Homology d₁ d₂ h) :=
  SquareZeroHomologyGrading.homologyGrading (totalGrading G₀ G₁ G₂)
    (differential d₁ d₂) (differential_sq d₁ d₂ h)
    (differential_homogeneous G₀ G₁ G₂ d₁ d₂ hd₁ hd₂)

include hd₂ in
/-- The middle boundary map has internal degree zero after restricting its
codomain to the actual kernel of the first differential. -/
theorem middleToCycles_homogeneous :
    TauCeti.LinearMap.IsHomogeneous (middleToCycles d₁ d₂ h)
      G₂.piece (G₁.ker hd₁).piece 0 := by
  intro p x hx
  apply (G₁.mem_ker_piece hd₁).2
  exact hd₂ hx

/-- The original zeroth homology with its quotient grading. -/
def zerothGrading : TauCeti.InternalGrading R (A₀ ⧸ LinearMap.range d₁) :=
  G₀.quotient (LinearMap.range d₁) hd₁.isHomogeneous_range

/-- The original middle homology with its inherited subquotient grading. -/
def firstGrading :
    TauCeti.InternalGrading R
      (LinearMap.ker d₁ ⧸ LinearMap.range (middleToCycles d₁ d₂ h)) :=
  (G₁.ker hd₁).quotient (LinearMap.range (middleToCycles d₁ d₂ h))
    (middleToCycles_homogeneous G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).isHomogeneous_range

/-- The original last homology with its kernel grading. -/
def secondGrading : TauCeti.InternalGrading R (LinearMap.ker d₂) :=
  G₂.ker hd₂

/-- The product of the original homology gradings, shifted by their complex
positions. Its factors are the actual three homology subquotients. -/
def factorsGrading : TauCeti.InternalGrading R
    ((A₀ ⧸ LinearMap.range d₁) ×
      ((LinearMap.ker d₁ ⧸ LinearMap.range (middleToCycles d₁ d₂ h)) ×
        LinearMap.ker d₂)) :=
  (zerothGrading G₀ G₁ d₁ hd₁).prod
    (((firstGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).shift 1).prod
      ((secondGrading G₁ G₂ d₂ hd₂).shift 2))

@[simp] theorem mem_factorsGrading {p : ℤ}
    {x : (A₀ ⧸ LinearMap.range d₁) ×
      ((LinearMap.ker d₁ ⧸ LinearMap.range (middleToCycles d₁ d₂ h)) ×
        LinearMap.ker d₂)} :
    x ∈ (factorsGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).piece p ↔
      x.1 ∈ (zerothGrading G₀ G₁ d₁ hd₁).piece p ∧
        x.2.1 ∈ (firstGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).piece (p + 1) ∧
        x.2.2 ∈ (secondGrading G₁ G₂ d₂ hd₂).piece (p + 2) := by
  simp only [factorsGrading, TauCeti.InternalGrading.prod_piece,
    TauCeti.InternalGrading.shift_piece, Submodule.mem_prod]

/-- The canonical comparison of actual homology classes preserves every
total cohomological degree. -/
theorem homologyEquiv_homogeneous :
    TauCeti.LinearMap.IsHomogeneous (homologyEquiv d₁ d₂ h).toLinearMap
      (homologyGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).piece
      (factorsGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).piece 0 := by
  intro p z hz
  obtain ⟨x, hx, rfl⟩ :=
    (SquareZeroHomologyGrading.mem_homologyGrading_iff
      (totalGrading G₀ G₁ G₂) (differential d₁ d₂)
      (differential_sq d₁ d₂ h)
      (differential_homogeneous G₀ G₁ G₂ d₁ d₂ hd₁ hd₂)).1 hz
  obtain ⟨hx₀, hx₁, hx₂⟩ := (mem_totalGrading G₀ G₁ G₂).1 hx
  rw [LinearEquiv.coe_coe, homologyEquiv_mk]
  simp only [factorsGrading, TauCeti.InternalGrading.prod_piece,
    TauCeti.InternalGrading.shift_piece, Submodule.mem_prod, add_zero]
  refine ⟨?_, ?_, ?_⟩
  · exact G₀.mk_mem_quotient_piece (LinearMap.range d₁) hd₁.isHomogeneous_range hx₀
  · apply (G₁.ker hd₁).mk_mem_quotient_piece
      (LinearMap.range (middleToCycles d₁ d₂ h))
      (middleToCycles_homogeneous G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).isHomogeneous_range
    exact (G₁.mem_ker_piece hd₁).2 hx₁
  · exact (G₂.mem_ker_piece hd₂).2 hx₂

/-- The inherited grading on folded homology is exactly the product of the
three original homology gradings with their required shifts. -/
theorem map_homologyGrading :
    (homologyGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).map (homologyEquiv d₁ d₂ h) =
      factorsGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂ :=
  SquareZeroHomologyGrading.map_eq_of_homogeneous _ _ _
    (homologyEquiv_homogeneous G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂)

/-- The canonical equivalence in each actual cohomological degree. -/
def homogeneousPieceEquiv (p : ℤ) :
    (homologyGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).piece p ≃ₗ[R]
      (factorsGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).piece p :=
  (homologyEquiv d₁ d₂ h).ofSubmodules _ _ (by
    have hp := congrArg (fun J : TauCeti.InternalGrading R _ ↦ J.piece p)
      (map_homologyGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂)
    simpa only [TauCeti.InternalGrading.map_piece] using hp)

/-- A degree in the product grading consists of the three indicated
original homology degrees. -/
def factorsPieceEquiv (p : ℤ) :
    (factorsGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).piece p ≃ₗ[R]
      (zerothGrading G₀ G₁ d₁ hd₁).piece p ×
        ((firstGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).piece (p + 1) ×
          (secondGrading G₁ G₂ d₂ hd₂).piece (p + 2)) where
  toFun x :=
    let hx := (mem_factorsGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).1 x.property
    (⟨x.val.1, hx.1⟩, (⟨x.val.2.1, hx.2.1⟩, ⟨x.val.2.2, hx.2.2⟩))
  invFun x := ⟨(x.1.val, (x.2.1.val, x.2.2.val)),
    (mem_factorsGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).2
      ⟨x.1.property, x.2.1.property, x.2.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The complete degreewise homology decomposition, expressed as an
equivalence of the original kernel/image subquotients in each degree. -/
def homogeneousHomologyEquiv (p : ℤ) :
    (homologyGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).piece p ≃ₗ[R]
      (zerothGrading G₀ G₁ d₁ hd₁).piece p ×
        ((firstGrading G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂).piece (p + 1) ×
          (secondGrading G₁ G₂ d₂ hd₂).piece (p + 2)) :=
  (homogeneousPieceEquiv G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂ p).trans
    (factorsPieceEquiv G₀ G₁ G₂ d₁ d₂ h hd₁ hd₂ p)

section Dimension

variable {K : Type u} [DivisionRing K]
  {V₀ V₁ V₂ : Type v}
  [AddCommGroup V₀] [AddCommGroup V₁] [AddCommGroup V₂]
  [Module K V₀] [Module K V₁] [Module K V₂]
  [Module.Finite K V₀] [Module.Finite K V₁] [Module.Finite K V₂]
  (J₀ : TauCeti.InternalGrading K V₀)
  (J₁ : TauCeti.InternalGrading K V₁)
  (J₂ : TauCeti.InternalGrading K V₂)
  (f₁ : V₁ →ₗ[K] V₀) (f₂ : V₂ →ₗ[K] V₁) (hf : f₁.comp f₂ = 0)
  (hf₁ : TauCeti.LinearMap.IsHomogeneous f₁ J₁.piece J₀.piece 0)
  (hf₂ : TauCeti.LinearMap.IsHomogeneous f₂ J₂.piece J₁.piece 0)

/-- Dimensions of genuine homogeneous cohomology add, with precisely the
degree shifts appearing in the paper's Lie-cohomology formula. -/
theorem finrank_homology_piece (p : ℤ) :
    Module.finrank K ((homologyGrading J₀ J₁ J₂ f₁ f₂ hf hf₁ hf₂).piece p) =
      Module.finrank K ((zerothGrading J₀ J₁ f₁ hf₁).piece p) +
        (Module.finrank K ((firstGrading J₀ J₁ J₂ f₁ f₂ hf hf₁ hf₂).piece (p + 1)) +
          Module.finrank K ((secondGrading J₁ J₂ f₂ hf₂).piece (p + 2))) := by
  rw [(homogeneousHomologyEquiv J₀ J₁ J₂ f₁ f₂ hf hf₁ hf₂ p).finrank_eq]
  simp only [Module.finrank_prod]

end Dimension

end PaperVerification.FoldedComplexHomologyGrading
