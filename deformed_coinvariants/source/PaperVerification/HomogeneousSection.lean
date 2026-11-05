module

public import PaperVerification.GradedComponentBasis
public import PaperVerification.EquivariantSection

/-!
# A homogeneous section from homogeneous basis lifts

The linear extension of chosen basis lifts is a section of the quotient map.
Its preservation of every component is proved from the actual homogeneous
basis decomposition, rather than supplied as an additional assumption.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.HomogeneousSection

variable {K V W I : Type*} [Field K]
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable {D : Type} [DecidableEq D]

def basisSection (B : Module.Basis I K W) (b : I → V) : W →ₗ[K] V := B.constr K b

theorem basisSection_apply_basis (B : Module.Basis I K W) (b : I → V) (i : I) :
    basisSection B b (B i) = b i := B.constr_basis K b i

theorem basisSection_rightInverse (q : V →ₗ[K] W) (B : Module.Basis I K W)
    (b : I → V) (hb : ∀ i, q (b i) = B i) (x : W) :
    q (basisSection B b x) = x := by
  have he : q.comp (basisSection B b) = LinearMap.id := by
    apply B.ext
    intro i
    simp only [LinearMap.comp_apply, basisSection_apply_basis, hb, LinearMap.id_apply]
  exact DFunLike.congr_fun he x

theorem basisSection_preserves_pieces
    (GW : TauCeti.InternalGrading K W D) (A : D → Submodule K V)
    (B : Module.Basis I K W) (degree : I → D) (b : I → V)
    (hB : ∀ i, B i ∈ GW.piece (degree i)) (hb : ∀ i, b i ∈ A (degree i)) :
    ∀ d x, x ∈ GW.piece d → basisSection B b x ∈ A d := by
  intro d x hx
  rw [← GradedComponentBasis.span_homogeneous_basis_piece GW B degree hB d] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [basisSection_apply_basis]
    have hi : b i.val ∈ A (degree i.val) := hb i.val
    simpa only [i.property] using hi
  | zero => simpa only [map_zero] using (A d).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using (A d).add_mem ihx ihy
  | smul c x hx ih => simpa only [map_smul] using (A d).smul_mem c ih

variable {G : Type*} [Group G] [Fintype G] [CharZero K]

/-- An equivariant homogeneous section is constructed from ordinary homogeneous
basis lifts. The group action need not fix individual basis vectors. -/
theorem exists_equivariant_section
    (ρ : G →* Module.End K V) (σ : G →* Module.End K W)
    (q : V →ₗ[K] W) (GW : TauCeti.InternalGrading K W D) (A : D → Submodule K V)
    (B : Module.Basis I K W) (degree : I → D) (b : I → V)
    (hB : ∀ i, B i ∈ GW.piece (degree i)) (hb : ∀ i, b i ∈ A (degree i))
    (hqb : ∀ i, q (b i) = B i)
    (hq : ∀ g x, q (ρ g x) = σ g (q x))
    (hρ : ∀ g d x, x ∈ A d → ρ g x ∈ A d)
    (hσ : ∀ g d x, x ∈ GW.piece d → σ g x ∈ GW.piece d) :
    ∃ s : W →ₗ[K] V,
      (∀ x, q (s x) = x) ∧
      (∀ g x, s (σ g x) = ρ g (s x)) ∧
      ∀ d x, x ∈ GW.piece d → s x ∈ A d :=
  EquivariantSection.exists_homogeneous_equivariant_section ρ σ q
    (basisSection B b) A GW.piece hq (basisSection_rightInverse q B b hqb)
    hρ hσ (basisSection_preserves_pieces GW A B degree b hB hb)

end PaperVerification.HomogeneousSection
