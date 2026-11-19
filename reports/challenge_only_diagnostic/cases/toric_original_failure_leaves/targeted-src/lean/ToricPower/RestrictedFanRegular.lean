module

public import ToricPower.RestrictedFanRays
public import ToricPower.SubmoduleExtendingBasis

/-! # Regularity in a saturated trace lattice

The primitive rays of a cone contained in a rational subspace extend to a
basis of its trace lattice. The proof retains the actual primitive vectors;
no regularity assumption on the restricted fan is introduced.
-/

@[expose] public noncomputable section
open TauCeti TauCeti.Toric
open scoped Classical

namespace ToricPower

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- The image of a ray under the literal inclusion of the subspace. -/
def toricRaySubtypeEmbedding (W : Submodule ℝ V) (σ : PointedCone ℝ V)
    (hσW : σ ≤ (W : PointedCone ℝ V)) :
    ToricRay (σ.comap W.subtype) ↪ ToricRay σ where
  toFun ρ := ⟨⟨ρ.toPointedCone.map W.subtype, by
    have h := ρ.val.isFaceOf.map W.subtype Subtype.val_injective
    simpa only [cone_map_comap_subtype W σ hσW] using h⟩, by
      rw [← coneSpan_map_subtype W ρ.toPointedCone,
        Submodule.finrank_map_subtype_eq]
      exact ρ.finrank_span⟩
  inj' ρ τ h := by
    have hm := congrArg (fun r : ToricRay σ => r.toPointedCone.comap W.subtype) h
    change (ρ.toPointedCone.map W.subtype).comap W.subtype =
      (τ.toPointedCone.map W.subtype).comap W.subtype at hm
    rw [cone_comap_map_subtype, cone_comap_map_subtype] at hm
    apply Subtype.ext
    apply PointedCone.Face.ext
    intro x
    exact SetLike.ext_iff.mp hm x

/-- A regular cone contained in a subspace is regular for its exact
integral trace. Rationality of the ambient subspace is unnecessary here. -/
theorem regularCone_comap_latticeTrace (W : Submodule ℝ V)
    {σ : PointedCone ℝ V} (hσ : IsRegularCone i σ)
    (hσW : σ ≤ (W : PointedCone ℝ V)) :
    IsRegularCone (latticeTraceMap i W) (σ.comap W.subtype) := by
  classical
  let τ := σ.comap W.subtype
  have hτ := toricCone_comap_latticeTrace W hσ.toIsToricCone hσW
  letI : Finite (ToricRay τ) := ToricRay.finite_of_fg hτ.fg
  obtain ⟨n, b, r, hb⟩ := hσ.exists_basis
  let rays := toricRaySubtypeEmbedding W σ hσW
  let selected : ToricRay τ ↪ Fin n := rays.trans r
  have hmem (ρ : ToricRay τ) : b (selected ρ) ∈ latticeTrace i W := by
    have h := (hb.isPrimitiveGenerator_apply (rays ρ)).mem
    obtain ⟨x, hx, he⟩ := h
    change i (b (selected ρ)) ∈ W
    change x.val = i (b (selected ρ)) at he
    rw [← he]
    exact x.property
  obtain ⟨m, c, t, hc⟩ := submodule_exists_basis_extending b selected
    (latticeTrace i W) hmem
  refine ⟨hτ, m, c, t, ⟨fun ρ => ?_⟩⟩
  apply isPrimitiveGenerator_iff.mpr
  constructor
  · have h : i (c (t ρ)).val ∈ rays ρ := by
      rw [hc]
      exact (hb.isPrimitiveGenerator_apply (rays ρ)).mem
    obtain ⟨x, hx, he⟩ := h
    have he' : latticeTraceMap i W (c (t ρ)) = x := Subtype.ext he.symm
    rw [he']
    exact hx
  · have hp : IsPrimitive (c (t ρ)).val := by
      rw [hc]
      exact (hb.isPrimitiveGenerator_apply (rays ρ)).isPrimitive
    exact primitive_in_submodule (latticeTrace i W) (c (t ρ)).val
      (c (t ρ)).property hp

/-- Restricting a regular fan to any rational subspace preserves regularity. -/
theorem restrictedFan_isRegular (fan : Fan i) (regular : fan.IsRegular)
    (W : Submodule ℝ V) (hW : IsRationalSubspace i W) :
    (restrictedFan fan W hW).IsRegular := by
  apply (Fan.isRegular_iff).mpr
  intro τ hτ
  obtain ⟨σ, hσ, hσW, rfl⟩ := (mem_restrictedFan_cones fan W hW τ).mp hτ
  exact regularCone_comap_latticeTrace W ((Fan.isRegular_iff).mp regular σ hσ) hσW

end ToricPower
