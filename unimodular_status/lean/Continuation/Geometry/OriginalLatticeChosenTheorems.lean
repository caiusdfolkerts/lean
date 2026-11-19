module

public import Continuation.Geometry.OriginalLatticeSchemeGeometry
public import Continuation.Geometry.OriginalLatticeSeedRealization
public import Continuation.Geometry.OriginalLatticeExtremal

/-!
# Principal geometry on the original character-chart colimit

These statements retain the original lattice, the whole fan and its actual
dual-semigroup diagram. The geometric conclusions now hold on the chosen
colimit itself. Its anticanonical bundle is defined from that scheme's own
top exterior power of Kähler differentials; the necessary pullback and
positivity comparisons are proved in `OriginalLatticeSchemeGeometry`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TauCeti.Toric PaperVerification.ToricGeometry
open AlgebraicGeometry CategoryTheory
open Unimodular Unimodular.Projectivity Unimodular.NefBig
open scoped Classical

universe u v

namespace PaperVerification.OriginalLatticeCharts

variable {N : Type u} [AddCommGroup N]
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : ℕ} (b : Module.Basis (Fin n) ℤ N)
    {ι : N →+ V} (hi : IsIntegralLattice ι)

/-- The projective embedding has the original chart colimit as its source. -/
def originalProjectiveEmbedding (k : Type u) [Field k]
    (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)
    (a : PaperVerification.ToricGeometry.Lattice n → ℤ) (ha : F.IsStrictSupport (fun u => (a u : ℝ))) :=
  (originalGluingIso b hi k F).hom ≫ strictSupportProjectiveEmbedding F a ha k

instance originalProjectiveEmbedding_isClosedImmersion (k : Type u) [Field k]
    (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)
    (a : PaperVerification.ToricGeometry.Lattice n → ℤ) (ha : F.IsStrictSupport (fun u => (a u : ℝ))) :
    IsClosedImmersion (originalProjectiveEmbedding b hi k F a ha) := by
  dsimp only [originalProjectiveEmbedding]
  infer_instance

/-- Proposition 4.2 with smoothness, projectivity and intrinsic anticanonical
nefness and bigness literally on the original character-chart colimit. -/
theorem theorem_4_2_original_gluing
    (k : Type u) [Field k] (hn : 0 < n) (U : Finset N)
    (hU : IntegralRigidity.Uniform b (fun u : (U : Set N) => u.val))
    (hpos : PointedCone.hull ℝ (ι '' (U : Set N)) = ⊤)
    (hzero : (0 : N) ∉ U) :
    ∃ F : PaperVerification.ToricGeometry.SmoothCompleteFan n,
      ∃ a : PaperVerification.ToricGeometry.Lattice n → ℤ, ∃ ha : F.IsStrictSupport (fun u => (a u : ℝ)),
      ∃ Ψ : Fan ι,
      (originalFan b hi F).IsComplete ∧
      (originalFan b hi F).IsRegular ∧
      (∀ u : N, ConeBases.IsRay (originalFan b hi F) u ↔ u ∈ U) ∧
      (originalFan b hi F).cones =
        Set.range (fun s : OriginalConeIndex b F => latticeCone (ι := ι) s.val) ∧
      Ψ.IsComplete ∧
      (∀ R : PointedCone ℝ V,
        (R ∈ Ψ.cones ∧ Module.finrank ℝ (Submodule.span ℝ (R : Set V)) = 1) ↔
          ∃ w ∈ U, R = PointedCone.hull ℝ {ι w}) ∧
      (∀ C, C ∈ Ψ.cones ↔ ∃ E : Set V, Convex ℝ E ∧
        IsExtreme ℝ (originalRayHull (ι := ι) U) E ∧
        E ≠ originalRayHull (ι := ι) U ∧ C = PointedCone.hull ℝ E) ∧
      (originalFan b hi F).IsSubdivision Ψ ∧
      (0 : V) ∈ interior (originalRayHull (ι := ι) U) ∧
      (∃ W : Finset (N →+ ℤ), originalDualPolar (originalRayHull (ι := ι) U) =
        convexHull ℝ (hi.realCharacter '' (W : Set (N →+ ℤ)))) ∧
      (originalRayHull (ι := ι) U).extremePoints ℝ = ι '' (U : Set N) ∧
      (∀ x : N, ι x ∈ originalRayHull (ι := ι) U ↔ x = 0 ∨ x ∈ U) ∧
      Smooth (originalSchemeStructureMap b hi k F) ∧
      IsProper (originalSchemeStructureMap b hi k F) ∧
      IsClosedImmersion (originalProjectiveEmbedding b hi k F a ha) ∧
      originalProjectiveEmbedding b hi k F a ha ≫
        polynomialProjectiveToSpec k (WeightIndex.{u} (F := F)) =
          originalSchemeStructureMap b hi k F ∧
      topologicalKrullDim (originalScheme b hi k F) = n ∧
      AlgebraicGeometry.IsNef (baseField := k)
        (originalAnticanonicalLineBundle b hi k F).obj ∧
      IsBig k (originalAnticanonicalLineBundle b hi k F).obj := by
  obtain ⟨F, a, ha, Ψ, hcomplete, hregular, hrays, hcones,
    hseedComplete, hseedRays, hfaces, hsub, hinterior, hpolar,
    hvertices, hterminal, _, _, hproper, _, hover, _, hnef, hbig⟩ :=
      theorem_4_2_original_lattice b hi k hn U hU hpos hzero
  refine ⟨F, a, ha, Ψ, hcomplete, hregular, hrays, hcones,
    hseedComplete, hseedRays, hfaces, hsub, hinterior, hpolar,
    hvertices, hterminal, originalScheme_smooth b hi k F,
    originalScheme_proper b hi k F hproper, inferInstance, ?_,
    originalScheme_dimension b hi k F,
    originalScheme_anticanonical_nef_and_big b hi k F hnef hbig⟩
  dsimp only [originalProjectiveEmbedding]
  rw [Category.assoc, hover, originalGluingIso_toSpec]

variable (Φ : Fan ι) (hcomplete : Φ.IsComplete)

/-- The geometric clause of Theorem 7.1 on the original fan's own chosen
gluing, without a projectivity hypothesis. -/
theorem original_extremal_gluing_nef_and_big (hregular : Φ.IsRegular)
    (k : Type u) [Field k]
    (hU : IntegralRigidity.Uniform b
      (fun w : {w : N | ConeBases.IsRay Φ w} => w.val))
    (hcard : Set.ncard {w : N | ConeBases.IsRay Φ w} = n * (n + 1)) :
    let F := geometricOriginalFan b Φ hcomplete hregular
    originalFan b Φ.lattice F = Φ ∧
    Φ.cones = Set.range (fun s : OriginalConeIndex b F => latticeCone (ι := ι) s.val) ∧
    Smooth (originalSchemeStructureMap b Φ.lattice k F) ∧
    topologicalKrullDim (originalScheme b Φ.lattice k F) = n ∧
    AlgebraicGeometry.IsNef (baseField := k)
      (originalAnticanonicalLineBundle b Φ.lattice k F).obj ∧
    IsBig k (originalAnticanonicalLineBundle b Φ.lattice k F).obj := by
  let F := geometricOriginalFan b Φ hcomplete hregular
  obtain ⟨hfan, hcones, _, hnef, hbig⟩ :=
    original_extremal_nef_and_big b Φ hcomplete hregular k hU hcard
  exact ⟨hfan, hcones, originalScheme_smooth b Φ.lattice k F,
    originalScheme_dimension b Φ.lattice k F,
    originalScheme_anticanonical_nef_and_big b Φ.lattice k F hnef hbig⟩

/-- The full original-lattice bound and equality classification, with the
anticanonical conclusion on the chosen original chart colimit itself. -/
theorem theorem_7_1_original_gluing (hn : 0 < n)
    (hU : IntegralRigidity.Uniform b
      (fun w : {w : N | ConeBases.IsRay Φ w} => w.val))
    (k : Type u) [Field k] :
    Set.ncard {w : N | ConeBases.IsRay Φ w} ≤ n * (n + 1) ∧
    (Set.ncard {w : N | ConeBases.IsRay Φ w} = n * (n + 1) ↔
      ∃ φ : N ≃ₗ[ℤ] Heller.TypeA.RootLattice n,
        φ '' {w : N | ConeBases.IsRay Φ w} = Heller.TypeA.roots n) ∧
    (Set.ncard {w : N | ConeBases.IsRay Φ w} = n * (n + 1) →
      ∃ (φ : N ≃ₗ[ℤ] Heller.TypeA.RootLattice n)
        (Γ : Fan (FanBridge.standardEmbedding n)) (e : FanEquiv Φ Γ)
        (D : TypeAFanGeometry.CompatibleCutSubdivisions n),
        φ '' {w : N | ConeBases.IsRay Φ w} = Heller.TypeA.roots n ∧
        (∀ w, e.latticeEquiv w = (Heller.TypeA.coordinateEquiv n).symm (φ w)) ∧
        Γ = D.toFan ∧
        (Φ.IsRegular ↔ ∀ S : TypeAFanGeometry.ProperCut n,
          (D.subdivision S).IsTriangulation) ∧
        ∀ hregular : Φ.IsRegular,
          let F := geometricOriginalFan b Φ hcomplete hregular
          originalFan b Φ.lattice F = Φ ∧
          Φ.cones = Set.range (fun s : OriginalConeIndex b F =>
            latticeCone (ι := ι) s.val) ∧
          Smooth (originalSchemeStructureMap b Φ.lattice k F) ∧
          topologicalKrullDim (originalScheme b Φ.lattice k F) = n ∧
          AlgebraicGeometry.IsNef (baseField := k)
            (originalAnticanonicalLineBundle b Φ.lattice k F).obj ∧
          IsBig k (originalAnticanonicalLineBundle b Φ.lattice k F).obj) := by
  obtain ⟨hbound, hequality, hclassification⟩ :=
    theorem_7_1_original_lattice b Φ hcomplete hn hU k
  refine ⟨hbound, hequality, fun hcard => ?_⟩
  obtain ⟨φ, Γ, e, D, hφ, he, hΓ, htri, _⟩ := hclassification hcard
  exact ⟨φ, Γ, e, D, hφ, he, hΓ, htri, fun hregular =>
    original_extremal_gluing_nef_and_big b Φ hcomplete hregular k hU hcard⟩

end PaperVerification.OriginalLatticeCharts

#print axioms PaperVerification.OriginalLatticeCharts.theorem_4_2_original_gluing
#print axioms PaperVerification.OriginalLatticeCharts.original_extremal_gluing_nef_and_big
#print axioms PaperVerification.OriginalLatticeCharts.theorem_7_1_original_gluing
