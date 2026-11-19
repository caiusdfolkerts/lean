module

public import PaperVerification.SquareZeroHomologyConjugacy
public import TauCeti.Algebra.Module.GradedModule.Quotient

/-!
# The inherited grading on actual square-zero homology

The homology grading is the subquotient grading of `ker D / im D` inherited
from the original graded module. A homogeneous conjugacy preserves this
grading, with the explicit map on cycle classes constructed in
`SquareZeroHomologyConjugacy`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

namespace PaperVerification.SquareZeroHomologyGrading

open SquareZeroHomologyConjugacy

variable {R : Type u} [Ring R]
  {A B : Type v} [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]

/-- A degree-zero homogeneous linear equivalence transports the entire
internal grading, not merely the dimensions of its pieces. -/
theorem map_eq_of_homogeneous
    (G : TauCeti.InternalGrading R A) (H : TauCeti.InternalGrading R B)
    (e : A ≃ₗ[R] B)
    (he : TauCeti.LinearMap.IsHomogeneous e.toLinearMap G.piece H.piece 0) :
    G.map e = H := by
  apply TauCeti.InternalGrading.ext
  intro p
  ext y
  rw [G.mem_map_piece_iff]
  constructor
  · intro hy
    simpa using he hy
  · intro hy
    simpa using he.linearEquiv_symm hy

variable (G : TauCeti.InternalGrading R A) (D : A →ₗ[R] A)
  (hD : D.comp D = 0) {δ : ℤ}
  (hdeg : TauCeti.LinearMap.IsHomogeneous D G.piece G.piece δ)

/-- Restricting the codomain of a homogeneous differential to its kernel
retains its original degree. -/
theorem toCycles_homogeneous :
    TauCeti.LinearMap.IsHomogeneous (complex D hD).moduleCatToCycles
      G.piece (G.ker hdeg).piece δ := by
  intro p x hx
  apply (G.mem_ker_piece hdeg).2
  exact hdeg hx

/-- The actual quotient of homogeneous cycles by homogeneous boundaries. -/
def homologyGrading :
    TauCeti.InternalGrading R
      (LinearMap.ker D ⧸ LinearMap.range (complex D hD).moduleCatToCycles) :=
  (G.ker hdeg).quotient (LinearMap.range (complex D hD).moduleCatToCycles)
    (toCycles_homogeneous G D hD hdeg).isHomogeneous_range

/-- A homogeneous homology class has a cycle representative of the same
degree in the original module. -/
theorem mem_homologyGrading_iff {p : ℤ}
    {z : LinearMap.ker D ⧸ LinearMap.range (complex D hD).moduleCatToCycles} :
    z ∈ (homologyGrading G D hD hdeg).piece p ↔
      ∃ x : LinearMap.ker D, x.val ∈ G.piece p ∧ Submodule.Quotient.mk x = z := by
  rw [homologyGrading, TauCeti.InternalGrading.mem_quotient_piece_iff]
  simp only [TauCeti.InternalGrading.mem_ker_piece]

/-- The class of a homogeneous cycle has that cycle's original degree. -/
theorem mk_mem_homologyGrading {p : ℤ} {x : LinearMap.ker D}
    (hx : x.val ∈ G.piece p) :
    (Submodule.Quotient.mk x :
      LinearMap.ker D ⧸ LinearMap.range (complex D hD).moduleCatToCycles) ∈
      (homologyGrading G D hD hdeg).piece p :=
  (mem_homologyGrading_iff G D hD hdeg).2 ⟨x, hx, rfl⟩

variable (H : TauCeti.InternalGrading R B) (E : B →ₗ[R] B)
  (hE : E.comp E = 0)
  (hdegE : TauCeti.LinearMap.IsHomogeneous E H.piece H.piece δ)
  (e : A ≃ₗ[R] B) (he : ∀ x, e (D x) = E (e x))
  (hgrade : TauCeti.LinearMap.IsHomogeneous e.toLinearMap G.piece H.piece 0)

include hgrade in
/-- The original homogeneous conjugacy restricts to homogeneous cycles. -/
theorem cyclesEquiv_homogeneous :
    TauCeti.LinearMap.IsHomogeneous (cyclesEquiv D E e he).toLinearMap
      (G.ker hdeg).piece (H.ker hdegE).piece 0 := by
  intro p x hx
  apply (H.mem_ker_piece hdegE).2
  exact hgrade ((G.mem_ker_piece hdeg).1 hx)

include hgrade in
/-- The induced map on actual kernel/image quotients is homogeneous. -/
theorem quotientHomologyEquiv_homogeneous :
    TauCeti.LinearMap.IsHomogeneous (quotientHomologyEquiv D E e he hD hE).toLinearMap
      (homologyGrading G D hD hdeg).piece (homologyGrading H E hE hdegE).piece 0 := by
  intro p z hz
  obtain ⟨x, hx, rfl⟩ := (mem_homologyGrading_iff G D hD hdeg).1 hz
  rw [LinearEquiv.coe_coe, quotientHomologyEquiv_mk]
  apply mk_mem_homologyGrading H E hE hdegE
  exact hgrade hx

include hgrade in
/-- Conjugacy identifies the inherited quotient gradings exactly. -/
theorem map_homologyGrading :
    (homologyGrading G D hD hdeg).map (quotientHomologyEquiv D E e he hD hE) =
      homologyGrading H E hE hdegE :=
  map_eq_of_homogeneous _ _ _
    (quotientHomologyEquiv_homogeneous G D hD hdeg H E hE hdegE e he hgrade)

/-- The induced equivalence restricts to each actual cohomology degree. -/
def homogeneousPieceEquiv (p : ℤ) :
    (homologyGrading G D hD hdeg).piece p ≃ₗ[R]
      (homologyGrading H E hE hdegE).piece p :=
  (quotientHomologyEquiv D E e he hD hE).ofSubmodules _ _ (by
    have hp := congrArg (fun J : TauCeti.InternalGrading R _ ↦ J.piece p)
      (map_homologyGrading G D hD hdeg H E hE hdegE e he hgrade)
    simpa only [TauCeti.InternalGrading.map_piece] using hp)

/-- A degree absent from the original module is absent from its actual
homology subquotient. -/
theorem homologyGrading_piece_eq_bot {p : ℤ} (hp : G.piece p = ⊥) :
    (homologyGrading G D hD hdeg).piece p = ⊥ := by
  apply eq_bot_iff.mpr
  intro z hz
  obtain ⟨x, hx, rfl⟩ := (mem_homologyGrading_iff G D hD hdeg).1 hz
  have hx0 : x.val = 0 := by simpa only [hp, Submodule.mem_bot] using hx
  have hx' : x = 0 := Subtype.ext hx0
  rw [hx']
  exact Submodule.zero_mem _

end PaperVerification.SquareZeroHomologyGrading
