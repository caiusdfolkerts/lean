module

public import PaperVerification.ToricOrbitQuotientCoordinates
public import PaperVerification.ToricFanScheme
public import Mathlib.CategoryTheory.Limits.Final

@[expose] public section

/-! # The actual cone index of an orbit closure and its quotient fan -/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b∈«Σ».cones)

abbrev OrbitConeIndex :=
  {s : Finset (Lattice n) // s∈«Σ».cones ∧ I.image b⊆s}

def orbitConeQuotientIndex (s : «Σ».OrbitConeIndex b I) :
    («Σ».completeQuotientStarFan b I hF).ConeIndex :=
  ⟨orbitQuotientCone b I s.val,(«Σ».mem_quotientStarCones b I _).mpr
    ⟨s.val,s.property.1,s.property.2,rfl⟩⟩

theorem orbitQuotientCone_subset_iff (s t : «Σ».OrbitConeIndex b I) :
    orbitQuotientCone b I s.val ⊆ orbitQuotientCone b I t.val ↔ s.val⊆t.val := by
  constructor
  · intro h u hu
    by_cases huI : u∈I.image b
    · exact t.property.2 huI
    · have hup : coneQuotientLattice b I u∈orbitQuotientCone b I t.val :=
        h (Finset.mem_image.mpr ⟨u,Finset.mem_sdiff.mpr ⟨hu,huI⟩,rfl⟩)
      obtain ⟨v,hv,hvu⟩ := Finset.mem_image.mp hup
      have huv := «Σ».coneQuotient_injective_star_rays b I s.property.1 t.property.1
        s.property.2 t.property.2 (Finset.mem_sdiff.mpr ⟨hu,huI⟩) hv hvu.symm
      exact huv.symm ▸ (Finset.mem_sdiff.mp hv).1
  · intro h
    exact Finset.image_subset_image (Finset.sdiff_subset_sdiff_left (I.image b) h)

theorem orbitConeQuotientIndex_injective :
    Function.Injective («Σ».orbitConeQuotientIndex b I hF) := by
  intro s t h
  apply Subtype.ext
  have he := congrArg Subtype.val h
  apply Finset.Subset.antisymm
  · apply («Σ».orbitQuotientCone_subset_iff b I s t).mp
    exact he.le
  · apply («Σ».orbitQuotientCone_subset_iff b I t s).mp
    exact he.symm.le

theorem orbitConeQuotientIndex_surjective :
    Function.Surjective («Σ».orbitConeQuotientIndex b I hF) := by
  intro t
  obtain ⟨s,hs,hIs,ht⟩ := («Σ».mem_quotientStarCones b I t.val).mp t.property
  exact ⟨⟨s,hs,hIs⟩,Subtype.ext ht.symm⟩

/-- This is an order isomorphism of the actual cone sets. In particular it
records all face inclusions, not merely a bijection of maximal cones. -/
def orbitConeOrderIso :
    «Σ».OrbitConeIndex b I ≃o («Σ».completeQuotientStarFan b I hF).ConeIndex where
  toEquiv := Equiv.ofBijective («Σ».orbitConeQuotientIndex b I hF)
    ⟨«Σ».orbitConeQuotientIndex_injective b I hF,
      «Σ».orbitConeQuotientIndex_surjective b I hF⟩
  map_rel_iff' := by
    intro s t
    exact «Σ».orbitQuotientCone_subset_iff b I s t

@[simp] theorem orbitConeOrderIso_apply (s : «Σ».OrbitConeIndex b I) :
    («Σ».orbitConeOrderIso b I hF s).val = orbitQuotientCone b I s.val := rfl

variable (k : Type*) [CommRing k]

/-- The quotient fan's actual affine chart diagram, indexed instead by
the original cones containing the orbit cone. -/
def orbitChartDiagram : «Σ».OrbitConeIndex b I ⥤ Scheme :=
  («Σ».orbitConeOrderIso b I hF).equivalence.functor ⋙
    («Σ».completeQuotientStarFan b I hF).coneDiagram k

instance orbitChartDiagram_hasColimit : HasColimit («Σ».orbitChartDiagram b I hF k) := by
  exact inferInstanceAs (HasColimit
    ((«Σ».orbitConeOrderIso b I hF).equivalence.functor ⋙
      («Σ».completeQuotientStarFan b I hF).coneDiagram k))

def orbitChartColimit : Scheme := colimit («Σ».orbitChartDiagram b I hF k)

/-- Reindexing changes no glued scheme. The isomorphism follows from the
actual categorical colimit and an equivalence of its indexing categories. -/
def orbitChartColimitIsoFan :
    «Σ».orbitChartColimit b I hF k ≅ («Σ».completeQuotientStarFan b I hF).fanScheme k :=
  Functor.Final.colimitIso («Σ».orbitConeOrderIso b I hF).equivalence.functor
    ((«Σ».completeQuotientStarFan b I hF).coneDiagram k)

@[reassoc (attr := simp)] theorem orbitChartColimitIsoFan_ι
    (s : «Σ».OrbitConeIndex b I) :
    colimit.ι («Σ».orbitChartDiagram b I hF k) s ≫
      («Σ».orbitChartColimitIsoFan b I hF k).hom =
        («Σ».completeQuotientStarFan b I hF).fanChartMap k
          («Σ».orbitConeQuotientIndex b I hF s) :=
  Functor.Final.ι_colimitIso_hom _ _ s

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbitConeOrderIso
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbitChartColimitIsoFan
