module
public import graph_foundation.part013
public import shared_results.part017

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.ParityHomologyRetract -/
section

/-! # Multiplicative homology comparison from a literal algebra projection

A coefficient-linear deformation retract proves that the homology map
induced by an actual differential algebra homomorphism is bijective. The
contraction itself need not preserve multiplication. The resulting algebra
equivalence therefore preserves precisely the products of the original
Koszul differential algebras.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace FourPapers.ParityDifferential

variable {K A B : Type*} [CommRing K] [Ring A] [Ring B]
  [Algebra K A] [Algebra K B]
  (D : ParityDifferential K A) (E : ParityDifferential K B)
  (f : A →ₐ[K] B)
  (C : HomologicalPerturbation.LinearDeformationRetract (R := K) (M := A) (H := B))
  (hD : C.sourceD = D.d) (hE : C.targetD = E.d)
  (hf : C.projection = f.toLinearMap)

include hD hE hf in
theorem retract_projection_chain (x : A) : E.d (f x) = f (D.d x) := by
  have hh := C.projection_differential x
  rw [hD, hE, hf] at hh
  exact hh.symm

include C hD hE hf in
theorem homologyMap_bijective_of_retract :
    Function.Bijective (homologyMap D E f (retract_projection_chain D E f C hD hE hf)) := by
  constructor
  · intro x y hxy
    obtain ⟨z, hz⟩ := D.classMap_surjective (x-y)
    have hh : homologyMap D E f (retract_projection_chain D E f C hD hE hf)
        (D.classMap z) = 0 := by
      rw [hz, map_sub, hxy, sub_self]
    rw [homologyMap_classMap, E.classMap_eq_zero] at hh
    obtain ⟨b,hb⟩ := hh
    have hcycle : C.sourceD z.val = 0 := by rw [hD]; exact z.property
    have hboundary : C.targetD b = C.projection z.val := by
      rw [hE, hf]
      exact hb
    have hsource := C.boundary_of_projected_boundary z.val hcycle b hboundary
    rw [hD] at hsource
    have hz0 : D.classMap z = 0 := (D.classMap_eq_zero z).mpr
      ⟨C.inclusion b + C.homotopy z.val, hsource⟩
    exact sub_eq_zero.mp (hz.symm.trans hz0)
  · intro y
    obtain ⟨z,rfl⟩ := E.classMap_surjective y
    have hz : D.d (C.inclusion z.val) = 0 := by
      have hh := C.inclusion_differential z.val
      rw [hD, hE, z.property, map_zero] at hh
      exact hh
    refine ⟨D.classMap ⟨C.inclusion z.val,hz⟩,?_⟩
    rw [homologyMap_classMap]
    apply congrArg E.classMap
    apply Subtype.ext
    change f (C.inclusion z.val) = z.val
    have hh := C.projection_inclusion z.val
    rw [hf] at hh
    exact hh

/-- The algebra equivalence is induced by the stated algebra map itself;
its product compatibility is not inferred merely from dimensions. -/
def homologyEquivOfRetract : D.Homology ≃ₐ[K] E.Homology :=
  AlgEquiv.ofBijective
    (homologyMap D E f (retract_projection_chain D E f C hD hE hf))
    (homologyMap_bijective_of_retract D E f C hD hE hf)

@[simp] theorem homologyEquivOfRetract_classMap (x : D.cycles) :
    homologyEquivOfRetract D E f C hD hE hf (D.classMap x) =
      E.classMap (cyclesMap D E f (retract_projection_chain D E f C hD hE hf) x) := rfl

end FourPapers.ParityDifferential

end
end
end


end
