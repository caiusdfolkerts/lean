module

public import Continuation.Divisor.ProjectiveFoundations

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

/-! Exact recovered base-field compatibility for the genuine monomial Proj comparison. -/

namespace PaperVerification.ToricCharacters

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricGeometry
open scoped Classical

variable {ι : Type*} {n : ℕ} (a : ι → Lattice n) (k : Type u) [Field k]

/-- The canonical structure map of the genuine monomial Proj. -/
def monomialProjectiveToSpec :
    monomialProjectiveScheme a k⟶Spec (CommRingCat.of k) :=
  Proj.toSpecZero (homogeneousWeightGrading a k)≫
    Spec.map (CommRingCat.ofHom (homogeneousWeightZeroMap a k))

set_option maxHeartbeats 2000000 in
theorem monomialCoordinateChartMap_toSpec (j : ι) :
    monomialCoordinateChartMap a k j≫monomialProjectiveToSpec a k=
      Spec.map (CommRingCat.ofHom
        (algebraMap k (monoidChartAlgebra k (differenceWeightMonoid a j)))) := by
  unfold monomialCoordinateChartMap monomialProjectiveToSpec
  erw [Category.assoc,← Category.assoc (Proj.awayι _ _ _ _),Proj.awayι_toSpecZero,
    ← Spec.map_comp,← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (homogeneousWeightChartEquiv a k j).commutes r

set_option maxHeartbeats 2000000 in
theorem monomialTorusChart_toSpec (j : ι) :
    monomialTorusChart a k j≫monomialProjectiveToSpec a k=
      Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k (Lattice n)))) := by
  erw [← monomialCoordinateChartMap_torus a k j,Category.assoc,
    monomialCoordinateChartMap_toSpec a k j,← Spec.map_comp]
  congr 1

instance monomialProjective_isOver :
    (monomialProjectiveScheme a k).Over (Spec (CommRingCat.of k)) where
  hom := monomialProjectiveToSpec a k

instance monomialCoordinateChartMap_isOver (j : ι) :
    (monomialCoordinateChartMap a k j).IsOver (Spec (CommRingCat.of k)) where
  comp_over := monomialCoordinateChartMap_toSpec a k j

end PaperVerification.ToricCharacters

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PaperVerification.ToricCharacters
open scoped Classical

variable {ι : Type*} [Fintype ι] {n : ℕ}
    («Σ» : SmoothCompleteFan n) (P : LatticePolytope n)
    (a : ι → Lattice n) (k : Type u) [Field k]
    (s : vertexWeightIndices a → Finset (Lattice n))
    (hdual : ∀ j,dualConeMonoid (s j)=differenceWeightMonoid a j.val)

set_option maxHeartbeats 2000000 in
theorem monomialFanChart_toSpec (j : vertexWeightIndices a) :
    monomialFanChart a k s hdual j≫monomialProjectiveToSpec a k=
      Spec.map (CommRingCat.ofHom (algebraMap k (monoidChartAlgebra k (dualConeMonoid (s j))))) := by
  erw [monomialFanChart,Category.assoc,monomialCoordinateChartMap_toSpec a k j.val]
  exact monoidChartEqIso_toSpec k (hdual j)

theorem monomialNormalFanIso_toSpec
    (hs : ∀ j,s j∈«Σ».cones)
    (hcover : ∀ t∈«Σ».cones,∃ j,t⊆s j)
    (hv : ∀ j : vertexWeightIndices a,embed n (a j.val)∈P.carrier)
    (hnormal : ∀ j : vertexWeightIndices a,P.normalCone (embed n (a j.val))=
      (latticeRayCone (s j) : Set (Ambient n))) :
    («Σ».monomialNormalFanIso P a k s hdual hs hcover hv hnormal).hom≫
        monomialProjectiveToSpec a k=«Σ».fanSchemeStructureMap k := by
  apply colimit.hom_ext
  intro t
  change «Σ».fanChartMap k t≫_ = «Σ».fanChartMap k t≫_
  have hbase : «Σ».fanChartMap k t ≫ «Σ».fanSchemeStructureMap k =
      coneChart k t.val ↘ Spec (CommRingCat.of k) :=
    comp_over («Σ».fanChartMap k t) (Spec (CommRingCat.of k))
  rw [hbase]
  obtain ⟨j,htj⟩ := hcover t.val t.property
  have hchart : «Σ».fanChartMap k ⟨s j,hs j⟩≫
      («Σ».monomialNormalFanIso P a k s hdual hs hcover hv hnormal).hom≫
        monomialProjectiveToSpec a k=coneChart k (s j) ↘ Spec (CommRingCat.of k) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f : coneChart k (s j)⟶monomialProjectiveScheme a k =>
        f≫monomialProjectiveToSpec a k)
          («Σ».monomialNormalFanIso_chart P a k s hdual hs hcover hv hnormal j)).trans
        (monomialFanChart_toSpec a k s hdual j))
  rw [← «Σ».fanChartMap_naturality k (s := t) (t := ⟨s j,hs j⟩) htj,
    Category.assoc,hchart]
  exact comp_over (coneChartFaceMap k htj) (Spec (CommRingCat.of k))

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.monomialNormalFanIso_toSpec
