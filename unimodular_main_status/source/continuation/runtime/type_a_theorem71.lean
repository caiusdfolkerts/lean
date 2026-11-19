module

public import Continuation.Runtime.TypeARecovered
public import Continuation.Runtime.LiteralTypeARoots
public import Continuation.Divisor.FanInterfaces
public import Continuation.Divisor.FanoClosure

/-!
# Theorem 7.1: extremal rays, compatible fans, and anticanonical positivity

The combinatorial statements below use the historically checked Heller and
facet-subdivision proof bodies.  The geometric conclusion uses the explicit
literal-root equivalence in `LiteralTypeARoots`, so the nef-and-big statement
concerns the original fan and its intrinsic anticanonical line bundle.

The paper assumes positive rank in its opening convention.  Its subdivision
classification is therefore stated for `0 < n`.  The bound, equality case,
and the original-fan nef-and-big corollary also hold in rank zero here.

Status: complete proof-source candidate; the combined source still needs its
own compiler receipt under the current pin.  No new compiler is launched by
this file, and no theorem is treated as an axiom.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace Unimodular.ExtremalFans

open TauCeti.Toric AlgebraicGeometry
open PaperVerification.ToricGeometry

universe u
variable {n : ℕ}

/-- The actual primitive rays of the geometric scheme interface satisfy
the full Heller bound and literal integral equality classification. -/
theorem smooth_bound_and_literal_equality
    (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun v : F.rays => v.val)) :
    F.rays.card ≤ n * (n + 1) ∧
      (F.rays.card = n * (n + 1) ↔
        ∃ φ : Lattice n ≃ₗ[ℤ] Heller.TypeA.RootLattice n,
          φ '' (F.rays : Set (Lattice n)) = Heller.TypeA.roots n) := by
  let Φ := FanInterfaces.dictionaryToricFan F
  have hR : {v : Lattice n | ConeBases.IsRay Φ v} =
      (F.rays : Set (Lattice n)) := by
    ext v
    exact FanInterfaces.dictionaryToricFan_ray_iff F v
  have hu : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun v : {v : Lattice n | ConeBases.IsRay Φ v} => v.val) := by
    intro a
    exact hU (fun i => ⟨(a i).val,
      (FanInterfaces.dictionaryToricFan_ray_iff F (a i).val).mp (a i).property⟩)
  have h := ActualFanTheorems.theorem_7_1_bound_and_equality Φ
    (Pi.basisFun ℤ (Fin n)) (FanInterfaces.dictionaryToricFan_complete F) hu
  simpa only [hR, Set.ncard_coe_finset] using h

/-- Extremal cardinality alone supplies the literal-root hypothesis.
The conclusion is ordinary nefness and bigness of the unchanged scheme's
intrinsic anticanonical bundle. No projectivity assumption is used. -/
theorem smooth_extremal_nef_and_big
    (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)
    (k : Type u) [Field k]
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun v : F.rays => v.val))
    (hcard : F.rays.card = n * (n + 1)) :
    AlgebraicGeometry.IsNef (baseField := k) (NefBig.anticanonicalLineBundle F k).obj ∧
      NefBig.IsBig k (NefBig.anticanonicalLineBundle F k).obj :=
  NefBig.theorem_7_1_nef_and_big_of_literal_roots F k
    ((smooth_bound_and_literal_equality F hU).2.mp hcard)

/-- The geometric classification on an unchanged smooth fan: an actual
integral fan equivalence, the exact coned compatible subdivisions, and
genuine triangulations of every facet. -/
theorem smooth_extremal_classification (hn : 0 < n)
    (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun v : F.rays => v.val))
    (hcard : F.rays.card = n * (n + 1)) :
    ∃ (φ : Lattice n ≃ₗ[ℤ] Heller.TypeA.RootLattice n)
      (Γ : Fan (FanBridge.standardEmbedding n))
      (e : FanEquiv (FanInterfaces.dictionaryToricFan F) Γ)
      (D : TypeAFanGeometry.CompatibleCutSubdivisions n),
      φ '' (F.rays : Set (Lattice n)) = Heller.TypeA.roots n ∧
      (∀ v, e.latticeEquiv v = (Heller.TypeA.coordinateEquiv n).symm (φ v)) ∧
      Γ = D.toFan ∧
      ∀ S : TypeAFanGeometry.ProperCut n, (D.subdivision S).IsTriangulation := by
  let Φ := FanInterfaces.dictionaryToricFan F
  have hR : {v : Lattice n | ConeBases.IsRay Φ v} =
      (F.rays : Set (Lattice n)) := by
    ext v
    exact FanInterfaces.dictionaryToricFan_ray_iff F v
  have hu : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun v : {v : Lattice n | ConeBases.IsRay Φ v} => v.val) := by
    intro a
    exact hU (fun i => ⟨(a i).val,
      (FanInterfaces.dictionaryToricFan_ray_iff F (a i).val).mp (a i).property⟩)
  have hc : Set.ncard {v : Lattice n | ConeBases.IsRay Φ v} = n * (n + 1) := by
    simpa only [hR, Set.ncard_coe_finset] using hcard
  obtain ⟨φ, Γ, e, D, hφ, he, hΓ, htri⟩ :=
    ActualFanTheorems.theorem_7_1_geometric_equality Φ hn
      (Pi.basisFun ℤ (Fin n)) (FanInterfaces.dictionaryToricFan_complete F) hu hc
  exact ⟨φ, Γ, e, D, by simpa only [hR] using hφ, he, hΓ,
    htri.mp (FanInterfaces.dictionaryToricFan_regular F)⟩

/-- All clauses of Theorem 7.1 for an actual complete fan in an integral
coordinate lattice. The fan may be singular or nonprojective. The last
clause is asserted for each proof of its actual regularity; the finite
geometric interface has exactly the original fan's cones, by the equality
included in the conclusion. The separate `fanSubdivisionEquiv` gives the
two inverse laws and therefore the uniqueness of the subdivisions.

The Heller and fan-equivalence endpoints imported above additionally retain
arbitrary original integral lattices. This theorem does not silently identify
an independently defined arbitrary-lattice scheme with `fanScheme`.
-/
theorem theorem_7_1_complete_fan (hn : 0 < n)
    (Φ : Fan (FanBridge.standardEmbedding n)) (hcomplete : Φ.IsComplete)
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun v : {v : Lattice n | ConeBases.IsRay Φ v} => v.val))
    (k : Type u) [Field k] :
    Set.ncard {v : Lattice n | ConeBases.IsRay Φ v} ≤ n * (n + 1) ∧
    (Set.ncard {v : Lattice n | ConeBases.IsRay Φ v} = n * (n + 1) ↔
      ∃ φ : Lattice n ≃ₗ[ℤ] Heller.TypeA.RootLattice n,
        φ '' {v : Lattice n | ConeBases.IsRay Φ v} = Heller.TypeA.roots n) ∧
    (Set.ncard {v : Lattice n | ConeBases.IsRay Φ v} = n * (n + 1) →
      ∃ (φ : Lattice n ≃ₗ[ℤ] Heller.TypeA.RootLattice n)
        (Γ : Fan (FanBridge.standardEmbedding n)) (e : FanEquiv Φ Γ)
        (D : TypeAFanGeometry.CompatibleCutSubdivisions n),
        φ '' {v : Lattice n | ConeBases.IsRay Φ v} = Heller.TypeA.roots n ∧
        (∀ v, e.latticeEquiv v = (Heller.TypeA.coordinateEquiv n).symm (φ v)) ∧
        Γ = D.toFan ∧
        (Φ.IsRegular ↔ ∀ S : TypeAFanGeometry.ProperCut n,
          (D.subdivision S).IsTriangulation) ∧
        ∀ hregular : Φ.IsRegular,
          let F := FanInterfaces.geometricFan Φ hcomplete hregular
          FanInterfaces.dictionaryToricFan F = Φ ∧
          AlgebraicGeometry.IsNef (baseField := k)
            (NefBig.anticanonicalLineBundle F k).obj ∧
          NefBig.IsBig k (NefBig.anticanonicalLineBundle F k).obj) := by
  obtain ⟨hbound, hequality⟩ := ActualFanTheorems.theorem_7_1_bound_and_equality Φ
    (Pi.basisFun ℤ (Fin n)) hcomplete hU
  refine ⟨hbound, hequality, fun hcard => ?_⟩
  obtain ⟨φ, Γ, e, D, hφ, he, hΓ, htri⟩ :=
    ActualFanTheorems.theorem_7_1_geometric_equality Φ hn
      (Pi.basisFun ℤ (Fin n)) hcomplete hU hcard
  refine ⟨φ, Γ, e, D, hφ, he, hΓ, htri, fun hregular => ?_⟩
  let F := FanInterfaces.geometricFan Φ hcomplete hregular
  have hR : (F.rays : Set (Lattice n)) =
      {v : Lattice n | ConeBases.IsRay Φ v} := by
    ext v
    exact FanInterfaces.geometricFan_ray_iff Φ hcomplete hregular v
  have hroots : ∃ ψ : Lattice n ≃ₗ[ℤ] Heller.TypeA.RootLattice n,
      ψ '' (F.rays : Set (Lattice n)) = Heller.TypeA.roots n := by
    exact ⟨φ, by simpa only [hR] using hφ⟩
  exact ⟨FanInterfaces.dictionaryToricFan_geometricFan Φ hcomplete hregular,
    NefBig.theorem_7_1_nef_and_big_of_literal_roots F k hroots⟩

#print axioms smooth_bound_and_literal_equality
#print axioms smooth_extremal_nef_and_big
#print axioms smooth_extremal_classification
#print axioms theorem_7_1_complete_fan
#print axioms ActualFanTheorems.theorem_7_1_bound_and_equality
#print axioms ActualFanTheorems.theorem_7_1_geometric_equality
#print axioms TypeAFanGeometry.fanSubdivisionEquiv
#print axioms TypeAFanGeometry.cutFace_affine_product
#print axioms TypeAFanGeometry.isRootFacet_iff_cutFace
#print axioms TypeAFanGeometry.CompatibleCutSubdivisions.toFan_isRegular_iff

end Unimodular.ExtremalFans
