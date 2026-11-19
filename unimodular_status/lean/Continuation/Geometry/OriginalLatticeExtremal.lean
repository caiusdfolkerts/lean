module

public import Continuation.Geometry.OriginalLatticeGivenFan
public import Continuation.Runtime.TypeATheorem71

@[expose] public section

/-!
# Theorem 7.1 on the original fan and its actual semigroup-chart gluing

The Heller bound and the coned facet-subdivision classification already
apply to the original integral lattice. This composition supplies the
missing scheme interface: for every regular extremal original fan, the
unchanged scheme carrying ordinary anticanonical nefness and bigness is
proved to be the original dual-semigroup gluing over the chosen field.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TauCeti.Toric PaperVerification.ToricGeometry AlgebraicGeometry CategoryTheory
open Unimodular
open scoped Classical

universe u v

namespace PaperVerification.OriginalLatticeCharts

variable {N : Type u} [AddCommGroup N]
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : ℕ} (b : Module.Basis (Fin n) ℤ N)
    {ι : N →+ V} (Φ : Fan ι) (hcomplete : Φ.IsComplete)

/-- Extremal original fans have ordinary anticanonical nefness and bigness
on their actual original-chart realization. No projectivity is assumed. -/
theorem original_extremal_nef_and_big (hregular : Φ.IsRegular)
    (k : Type u) [Field k]
    (hU : IntegralRigidity.Uniform b
      (fun w : {w : N | ConeBases.IsRay Φ w} => w.val))
    (hcard : Set.ncard {w : N | ConeBases.IsRay Φ w} = n * (n + 1)) :
    let F := geometricOriginalFan b Φ hcomplete hregular
    originalFan b Φ.lattice F = Φ ∧
    Φ.cones = Set.range (fun s : OriginalConeIndex b F => latticeCone (ι := ι) s.val) ∧
    Nonempty (Over.mk (originalSchemeStructureMap b Φ.lattice k F) ≅ F.fanSchemeOver k) ∧
    AlgebraicGeometry.IsNef (baseField := k) (NefBig.anticanonicalLineBundle F k).obj ∧
    NefBig.IsBig k (NefBig.anticanonicalLineBundle F k).obj := by
  let F := geometricOriginalFan b Φ hcomplete hregular
  have hUF := geometricOriginalFan_uniform b Φ hcomplete hregular hU
  have hcardF : F.rays.card = n * (n + 1) :=
    (geometricOriginalFan_ray_card b Φ hcomplete hregular).trans hcard
  exact ⟨originalFan_geometricOriginalFan b Φ hcomplete hregular,
    givenFan_cones_eq_chart_cones b Φ hcomplete hregular,
    ⟨givenFanGluingOverIso b Φ hcomplete hregular k⟩,
    ExtremalFans.smooth_extremal_nef_and_big F k hUF hcardF⟩

/-- The full bound, literal equality classification, compatible coned
subdivisions, and ordinary anticanonical conclusion, with the actual
original fan and its semigroup-chart realization retained. -/
theorem theorem_7_1_original_lattice (hn : 0 < n)
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
          Nonempty (Over.mk (originalSchemeStructureMap b Φ.lattice k F) ≅
            F.fanSchemeOver k) ∧
          AlgebraicGeometry.IsNef (baseField := k)
            (NefBig.anticanonicalLineBundle F k).obj ∧
          NefBig.IsBig k (NefBig.anticanonicalLineBundle F k).obj) := by
  letI : FiniteDimensional ℝ V := Φ.lattice.finiteDimensional
  obtain ⟨hbound, hequality⟩ := ActualFanTheorems.theorem_7_1_bound_and_equality
    Φ b hcomplete hU
  refine ⟨hbound, hequality, fun hcard => ?_⟩
  obtain ⟨φ, Γ, e, D, hφ, he, hΓ, htri⟩ :=
    ActualFanTheorems.theorem_7_1_geometric_equality Φ hn b hcomplete hU hcard
  exact ⟨φ, Γ, e, D, hφ, he, hΓ, htri, fun hregular =>
    original_extremal_nef_and_big b Φ hcomplete hregular k hU hcard⟩

end PaperVerification.OriginalLatticeCharts

#print axioms PaperVerification.OriginalLatticeCharts.original_extremal_nef_and_big
#print axioms PaperVerification.OriginalLatticeCharts.theorem_7_1_original_lattice
