module

public import PaperVerification.ToricRationalCurveDegree
public import PaperVerification.ToricIntrinsicAction
public import PaperVerification.ToricEquivariantRigidity

@[expose] public section

/-!
# Actual invariant integral curves and their degree bounds

An invariant curve is an actual integral scheme of ordinary Krull
dimension one, with a closed immersion and a genuine group-scheme action
making that immersion equivariant. The curve itself is not defined by a
fan wall. Bounds on these actual curves imply the wall bounds used in the
polytope proof, and transport through actual equivariant scheme isomorphisms.

The degree relation is the coordinate-independent O(d) degree on rational
smooth projective curves. The classification and degree-existence theorem
for all invariant curves is a separate obligation in the intrinsic dictionary.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory MonoidalCategory
open PaperVerification.ToricGeometry
open scoped Classical

variable (k : Type u) [Field k] (n : ℕ)
    (X : Over (Spec (CommRingCat.of k)))
    [ModObj (splitTorusOver k (Fin n→ℤ)) X]

/-- A genuine invariant integral curve, including its scheme structure
and its action on arbitrary test schemes. -/
structure InvariantIntegralCurve where
  curve : Over (Spec (CommRingCat.of k))
  integral : IsIntegral curve.left
  action : ModObj (splitTorusOver k (Fin n→ℤ)) curve
  inclusion : curve ⟶ X
  closed : IsClosedImmersion inclusion.left
  dimension : topologicalKrullDim curve.left=1
  equivariant : letI := action
    IsModHom (splitTorusOver k (Fin n→ℤ)) inclusion

attribute [instance] InvariantIntegralCurve.integral InvariantIntegralCurve.action
  InvariantIntegralCurve.closed InvariantIntegralCurve.equivariant

variable [IsIntegral X.left]

/-- Degree bounds on the actual restricted line bundles. No wall, edge,
coefficient function, or polytope appears in this condition. -/
def InvariantCurveDegreesAtLeast (D : CartierData X.left) (bound : ℕ) : Prop :=
  ∀ C : InvariantIntegralCurve k n X, ∀ d : ℤ,
    RationalCurveHasDegree k
      ((Scheme.Modules.pullback C.inclusion.left).obj D.sheaf) d → (bound : ℤ)≤d

theorem invariantCurveDegreesAtLeast_sheafIso
    (D E : CartierData X.left) (F : D.sheaf ≅ E.sheaf) (bound : ℕ) :
    InvariantCurveDegreesAtLeast k n X D bound ↔
      InvariantCurveDegreesAtLeast k n X E bound := by
  constructor
  · intro h C d hd
    apply h C d
    exact (rationalCurveHasDegree_iso k
      ((Scheme.Modules.pullback C.inclusion.left).mapIso F) d).mpr hd
  · intro h C d hd
    apply h C d
    exact (rationalCurveHasDegree_iso k
      ((Scheme.Modules.pullback C.inclusion.left).mapIso F) d).mp hd

namespace InvariantIntegralCurve

variable {k n X} {Y : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n→ℤ)) Y]
    (e : X ≅ Y) [IsModHom (splitTorusOver k (Fin n→ℤ)) e.hom]

/-- Composition with an actual equivariant isomorphism transports the
whole curve, rather than only its set of points. -/
def mapIso (C : InvariantIntegralCurve k n X) : InvariantIntegralCurve k n Y where
  curve := C.curve
  integral := C.integral
  action := C.action
  inclusion := C.inclusion≫e.hom
  closed := by
    change IsClosedImmersion (C.inclusion.left≫e.hom.left)
    infer_instance
  dimension := C.dimension
  equivariant := by
    letI := C.action
    infer_instance

variable [IsIntegral Y.left]

def restrictionPullbackIso (C : InvariantIntegralCurve k n X) (D : CartierData Y.left) :
    (Scheme.Modules.pullback C.inclusion.left).obj (D.dominantPullback e.hom.left).sheaf ≅
      (Scheme.Modules.pullback (C.mapIso e).inclusion.left).obj D.sheaf :=
  (Scheme.Modules.pullback C.inclusion.left).mapIso
      (D.dominantPullbackSheafIso e.hom.left).symm ≪≫
    (Scheme.Modules.pullbackComp C.inclusion.left e.hom.left).app D.sheaf

end InvariantIntegralCurve

variable {k n X} {Y : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n→ℤ)) Y] [IsIntegral Y.left]

/-- The actual geometric degree hypothesis pulls back along a genuine
equivariant k-scheme isomorphism. -/
theorem invariantCurveDegreesAtLeast_pullbackIso (e : X ≅ Y)
    [IsModHom (splitTorusOver k (Fin n→ℤ)) e.hom]
    (D : CartierData Y.left) (bound : ℕ)
    (hD : InvariantCurveDegreesAtLeast k n Y D bound) :
    InvariantCurveDegreesAtLeast k n X (D.dominantPullback e.hom.left) bound := by
  intro C d hd
  apply hD (C.mapIso e) d
  exact (rationalCurveHasDegree_iso k (C.restrictionPullbackIso e D) d).mp hd

end PaperVerification.ToricSchemes

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

local instance : IsIntegral («Σ».fanSchemeOver k).left := by
  change IsIntegral («Σ».fanScheme k)
  infer_instance

/-- A fan wall supplies a genuine instance of the intrinsic curve type. -/
def wallInvariantCurve (s : «Σ».fullCones) (j : Fin n) :
    InvariantIntegralCurve k n («Σ».fanSchemeOver k) where
  curve := («Σ».wallCurveFan s j).fanSchemeOver k
  integral := by
    change IsIntegral («Σ».wallCurve s j k)
    exact «Σ».wallCurve_isIntegral s j k
  action := «Σ».orbitClosureSourceAction k («Σ».fullConeBasis s)
    («Σ».wallIndices s j) («Σ».wallCone_mem s j)
  inclusion := («Σ».wallCurveInclusion s j k).asOver (Spec (CommRingCat.of k))
  closed := by
    change IsClosedImmersion («Σ».wallCurveInclusion s j k)
    exact «Σ».wallCurveInclusion_isClosedImmersion s j k
  dimension := «Σ».wallCurve_dimension s j k
  equivariant := «Σ».wallCurve_equivariant s j k

theorem cartierWallDegreesAtLeast_of_invariantCurveDegrees
    (D : CartierData («Σ».fanScheme k)) (bound : ℕ)
    (hD : InvariantCurveDegreesAtLeast k n («Σ».fanSchemeOver k) D bound) :
    «Σ».CartierWallDegreesAtLeast k D bound := by
  intro s j d hd
  apply hD («Σ».wallInvariantCurve k s j) d
  exact ((«Σ».wallCurveFan s j).oneDimensionalHasDegree_iff_rationalCurve k
    («Σ».wallIndices_codimension s j) _ d).mp hd

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricSchemes.invariantCurveDegreesAtLeast_pullbackIso
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.cartierWallDegreesAtLeast_of_invariantCurveDegrees
