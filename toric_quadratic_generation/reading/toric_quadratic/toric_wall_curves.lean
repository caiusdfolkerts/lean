module

public import PaperVerification.ToricProjectiveLineDimension
public import PaperVerification.ToricOrbitActions
public import PaperVerification.ToricOrbitCartierCoefficients

@[expose] public section

/-!
# Actual invariant curves associated to fan walls

Deleting one primitive generator from a full smooth cone gives an
actual quotient-star scheme. Its map into the fan scheme is the
previously constructed closed immersion. The quotient has rank one,
so its scheme is isomorphic to the actual two-chart projective line
and has ordinary topological Krull dimension one.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open MonoidalCategory MonObj
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (s : «Σ».fullCones) (j : Fin n)

def wallIndices (_s : «Σ».fullCones) (j : Fin n) : Finset (Fin n) := Finset.univ.erase j

theorem wallIndices_codimension : n-(«Σ».wallIndices s j).card=1 := by
  simp only [wallIndices,Finset.card_erase_of_mem (Finset.mem_univ j),Finset.card_fin]
  have hn := j.isLt
  omega

theorem wallCone_mem :
    («Σ».wallIndices s j).image («Σ».fullConeBasis s)∈«Σ».cones := by
  apply «Σ».downward s.val («Σ».fullCones_mem s)
  rw [«Σ».fullConeBasis_ray_set]
  exact Finset.image_subset_image (Finset.erase_subset _ _)

def wallCurveFan : SmoothCompleteFan (n-(«Σ».wallIndices s j).card) :=
  «Σ».completeQuotientStarFan («Σ».fullConeBasis s) («Σ».wallIndices s j) («Σ».wallCone_mem s j)

variable (k : Type u) [Field k]

def wallCurve : Scheme.{u} := («Σ».wallCurveFan s j).fanScheme k

def wallCurveInclusion : «Σ».wallCurve s j k ⟶ «Σ».fanScheme k :=
  «Σ».orbitClosureMap k («Σ».fullConeBasis s) («Σ».wallIndices s j) («Σ».wallCone_mem s j)

instance wallCurveInclusion_isClosedImmersion :
    IsClosedImmersion («Σ».wallCurveInclusion s j k) := by
  exact «Σ».orbitClosureMap_isClosedImmersion k («Σ».fullConeBasis s)
    («Σ».wallIndices s j) («Σ».wallCone_mem s j)

instance wallCurve_isIntegral : IsIntegral («Σ».wallCurve s j k) :=
  inferInstanceAs (IsIntegral ((«Σ».wallCurveFan s j).fanScheme k))

instance wallCurve_isNoetherian : IsNoetherian («Σ».wallCurve s j k) :=
  inferInstanceAs (IsNoetherian ((«Σ».wallCurveFan s j).fanScheme k))

instance wallCurve_isOver : («Σ».wallCurve s j k).Over (Spec (.of k)) :=
  inferInstanceAs (((«Σ».wallCurveFan s j).fanScheme k).Over (Spec (.of k)))

instance wallCurveInclusion_isOver :
    («Σ».wallCurveInclusion s j k).IsOver (Spec (.of k)) :=
  inferInstanceAs ((«Σ».orbitClosureMap k («Σ».fullConeBasis s)
    («Σ».wallIndices s j) («Σ».wallCone_mem s j)).IsOver (Spec (.of k)))

def wallCurveProjectiveLineIso : «Σ».wallCurve s j k ≅ projectiveLineScheme k :=
  oneDimensionalFanSchemeIso («Σ».wallCurveFan s j) («Σ».wallIndices_codimension s j) k

theorem wallCurve_dimension : topologicalKrullDim («Σ».wallCurve s j k)=1 := by
  have h := IsHomeomorph.topologicalKrullDim_eq
    (fun x => («Σ».wallCurveProjectiveLineIso s j k).hom x)
    («Σ».wallCurveProjectiveLineIso s j k).hom.homeomorph.isHomeomorph
  exact h.trans (projectiveLine_topologicalKrullDim k)

/-- The actual group-scheme equivariance identity is inherited from the
closed orbit immersion; it is stronger than invariance of rational points. -/
theorem wallCurve_equivariant :
    letI : ModObj (PaperVerification.ToricSchemes.splitTorusOver k (Lattice n))
        ((«Σ».wallCurve s j k).asOver (Spec (.of k))) :=
      «Σ».orbitClosureSourceAction k («Σ».fullConeBasis s)
        («Σ».wallIndices s j) («Σ».wallCone_mem s j)
    IsModHom (PaperVerification.ToricSchemes.splitTorusOver k (Lattice n))
      ((«Σ».wallCurveInclusion s j k).asOver (Spec (.of k))) :=
  «Σ».orbitClosureMap_equivariant k («Σ».fullConeBasis s)
    («Σ».wallIndices s j) («Σ».wallCone_mem s j)

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.wallCurve_dimension
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.wallCurve_equivariant
