module

public import ToricPower.RelativeSimplicialRefinement
public import ToricPower.RegularConeInequalities
public import TauCeti.Geometry.Toric.Algebraic.Ray.Face
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# Primitive-ray coordinates for a simplicial cone

The primitive generators of a simplicial cone are linearly independent
in the real ambient vector space. In full dimension they form a real
basis, though generally not an integral basis. This distinction is what
the lattice multiplicity in regular subdivision measures.
-/

@[expose] public noncomputable section
open TauCeti.Toric
open scoped Classical

namespace ToricPower.FanSubdivision

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (lattice : IsIntegralLattice i)
  {C : PointedCone ℝ V} (toric : IsToricCone i C)

theorem primitiveGenerator_real_span :
    Submodule.span ℝ (Set.range (fun ρ : ToricRay C => i (primitiveGenerator lattice toric ρ))) =
      Submodule.span ℝ (C : Set V) := by
  have generators : PointedCone.hull ℝ
      (Set.range (fun ρ : ToricRay C => i (primitiveGenerator lattice toric ρ))) = C := by
    change PointedCone.hull ℝ (Set.range ((i : N → V) ∘ primitiveGenerator lattice toric)) = C
    rw [Set.range_comp]
    exact toric.hull_primitiveGenerator lattice
  apply le_antisymm
  · apply Submodule.span_mono
    intro x hx
    rw [← generators]
    exact PointedCone.subset_hull hx
  · apply Submodule.span_le.mpr
    intro x hx
    have hx' : x ∈ PointedCone.hull ℝ
        (Set.range (fun ρ : ToricRay C => i (primitiveGenerator lattice toric ρ))) :=
      generators.symm ▸ hx
    exact PointedCone.hull_le_span ℝ _ hx'

theorem simplicial_primitiveGenerator_linearIndependent (simplicial : C.IsSimplicial) :
    LinearIndependent ℝ (fun ρ : ToricRay C => i (primitiveGenerator lattice toric ρ)) := by
  letI := ToricRay.finite_of_fg toric.fg
  letI := Fintype.ofFinite (ToricRay C)
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  change Fintype.card (ToricRay C) = Module.finrank ℝ
    (Submodule.span ℝ (Set.range (fun ρ : ToricRay C => i (primitiveGenerator lattice toric ρ))))
  rw [primitiveGenerator_real_span lattice toric]
  have dimension := finrank_span_face_eq_card_rays_of_isSimplicial simplicial
    (⟨C, PointedCone.IsFaceOf.refl C⟩ : C.Face)
  simpa only [PointedCone.Face.toPointedCone, Nat.card_eq_fintype_card] using dimension.symm

/-- The primitive-ray basis over the reals of a full-dimensional
simplicial cone. Integrality of its vectors is literal, while integral
unimodularity is deliberately not part of this definition. -/
def simplicialPrimitiveBasis (simplicial : C.IsSimplicial)
    (full : Submodule.span ℝ (C : Set V) = ⊤) : Module.Basis (ToricRay C) ℝ V :=
  Module.Basis.mk (simplicial_primitiveGenerator_linearIndependent lattice toric simplicial)
    (by rw [primitiveGenerator_real_span lattice toric, full])

@[simp]
theorem simplicialPrimitiveBasis_apply (simplicial : C.IsSimplicial)
    (full : Submodule.span ℝ (C : Set V) = ⊤) (ρ : ToricRay C) :
    simplicialPrimitiveBasis lattice toric simplicial full ρ =
      i (primitiveGenerator lattice toric ρ) :=
  Module.Basis.mk_apply _ _ _

theorem simplicialPrimitiveBasis_hull (simplicial : C.IsSimplicial)
    (full : Submodule.span ℝ (C : Set V) = ⊤) :
    PointedCone.hull ℝ (Set.range (simplicialPrimitiveBasis lattice toric simplicial full)) = C := by
  have family : (simplicialPrimitiveBasis lattice toric simplicial full : ToricRay C → V) =
      fun ρ => i (primitiveGenerator lattice toric ρ) := by
    funext ρ
    exact simplicialPrimitiveBasis_apply lattice toric simplicial full ρ
  rw [family]
  change PointedCone.hull ℝ (Set.range ((i : N → V) ∘ primitiveGenerator lattice toric)) = C
  rw [Set.range_comp]
  exact toric.hull_primitiveGenerator lattice

theorem mem_simplicialCone_iff_coordinates_nonnegative (simplicial : C.IsSimplicial)
    (full : Submodule.span ℝ (C : Set V) = ⊤) (x : V) :
    x ∈ C ↔ ∀ ρ, 0 ≤ (simplicialPrimitiveBasis lattice toric simplicial full).repr x ρ := by
  have h := mem_basisCone_iff (simplicialPrimitiveBasis lattice toric simplicial full) Set.univ x
  rw [Set.image_univ, simplicialPrimitiveBasis_hull lattice toric simplicial full] at h
  simpa only [Set.mem_univ, not_true_eq_false, IsEmpty.forall_iff, implies_true, and_true] using h

theorem stellarFan_isSimplicial (fan : Fan i)
    (simplicial : ∀ C ∈ fan.cones, C.IsSimplicial) (q : N) :
    ∀ C ∈ (stellarFan fan q).cones, C.IsSimplicial := by
  intro C hC
  rcases (stellarFan_mem_iff fan q).mp hC with old |
    ⟨τ, ⟨hτ, hpτ, σ, hσ, hpσ, hτσ⟩, rfl⟩
  · exact simplicial C old.1
  · exact rayJoin_isSimplicial hpσ (fan.isFaceOf_of_le hσ hτ hτσ) hpτ le_rfl (simplicial τ hτ)

end ToricPower.FanSubdivision
end
