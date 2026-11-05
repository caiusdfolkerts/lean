module

public import TauCeti.Algebra.Module.GradedModule.Internal
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Assembling all degreewise representation equivalences

The direct-sum decompositions of two internally graded modules turn a family
of genuine homogeneous-piece equivalences into one global linear equivalence.
Its equivariance follows on homogeneous vectors and hence on the whole module.
Both directions preserve every degree.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped DirectSum

namespace PaperVerification.GradedRepresentationAssembly

variable {K G V W : Type*} {ι : Type} [Semiring K] [Monoid G] [DecidableEq ι]
  [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W]
variable (GV : TauCeti.InternalGrading K V ι) (GW : TauCeti.InternalGrading K W ι)

def linearEquiv (e : ∀ d, GV.piece d ≃ₗ[K] GW.piece d) : V ≃ₗ[K] W :=
  (DirectSum.decomposeLinearEquiv GV.piece).trans
    ((DirectSum.congrLinearEquiv e).trans (DirectSum.decomposeLinearEquiv GW.piece).symm)

@[simp] theorem linearEquiv_apply_piece (e : ∀ d, GV.piece d ≃ₗ[K] GW.piece d)
    (d : ι) (x : GV.piece d) :
    linearEquiv GV GW e (x : V) = (e d x : W) := by
  change (DirectSum.decomposeLinearEquiv GW.piece).symm
    ((DirectSum.congrLinearEquiv e).toLinearMap
      (DirectSum.decomposeLinearEquiv GV.piece (x : V))) = _
  rw [DirectSum.decomposeLinearEquiv_apply_coe,DirectSum.congrLinearEquiv_toLinearMap,
    DirectSum.lmap_lof,DirectSum.decomposeLinearEquiv_symm_lof]
  rfl

theorem linearEquiv_preserves_piece (e : ∀ d, GV.piece d ≃ₗ[K] GW.piece d)
    (d : ι) {x : V} (hx : x ∈ GV.piece d) :
    linearEquiv GV GW e x ∈ GW.piece d := by
  rw [linearEquiv_apply_piece GV GW e d ⟨x,hx⟩]
  exact (e d ⟨x,hx⟩).property

theorem linearEquiv_symm_preserves_piece (e : ∀ d, GV.piece d ≃ₗ[K] GW.piece d)
    (d : ι) {y : W} (hy : y ∈ GW.piece d) :
    (linearEquiv GV GW e).symm y ∈ GV.piece d := by
  have h : linearEquiv GV GW e ((e d).symm ⟨y,hy⟩ : V) = y := by
    rw [linearEquiv_apply_piece,LinearEquiv.apply_symm_apply]
  have he := congrArg (linearEquiv GV GW e).symm h
  rw [LinearEquiv.symm_apply_apply] at he
  rw [← he]
  exact ((e d).symm ⟨y,hy⟩).property

variable (ρ : Representation K G V) (σ : Representation K G W)
variable (hV : ∀ g d x, x ∈ GV.piece d → ρ g x ∈ GV.piece d)
variable (hW : ∀ g d y, y ∈ GW.piece d → σ g y ∈ GW.piece d)

def representationEquiv
    (e : ∀ d, GV.piece d ≃ₗ[K] GW.piece d)
    (he : ∀ g d (x : GV.piece d),
      (e d ⟨ρ g x,hV g d x x.property⟩ : W) = σ g (e d x : W)) : ρ.Equiv σ :=
  Representation.Equiv.mk (linearEquiv GV GW e) (by
    intro g
    apply GV.linearMap_ext
    intro d x hx
    change linearEquiv GV GW e (ρ g x) = σ g (linearEquiv GV GW e x)
    rw [linearEquiv_apply_piece GV GW e d ⟨ρ g x,hV g d x hx⟩,
      linearEquiv_apply_piece GV GW e d ⟨x,hx⟩]
    exact he g d ⟨x,hx⟩)

theorem representationEquiv_preserves_piece
    (e : ∀ d, GV.piece d ≃ₗ[K] GW.piece d)
    (he : ∀ g d (x : GV.piece d),
      (e d ⟨ρ g x,hV g d x x.property⟩ : W) = σ g (e d x : W))
    (d : ι) {x : V} (hx : x ∈ GV.piece d) :
    representationEquiv GV GW ρ σ hV e he x ∈ GW.piece d :=
  linearEquiv_preserves_piece GV GW e d hx

theorem representationEquiv_symm_preserves_piece
    (e : ∀ d, GV.piece d ≃ₗ[K] GW.piece d)
    (he : ∀ g d (x : GV.piece d),
      (e d ⟨ρ g x,hV g d x x.property⟩ : W) = σ g (e d x : W))
    (d : ι) {y : W} (hy : y ∈ GW.piece d) :
    (representationEquiv GV GW ρ σ hV e he).symm y ∈ GV.piece d :=
  linearEquiv_symm_preserves_piece GV GW e d hy

end PaperVerification.GradedRepresentationAssembly
