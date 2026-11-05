module

public import PaperVerification.ToricProjectiveLineOrders
public import PaperVerification.ToricCocycleOrders
public import PaperVerification.ToricFanCartierCocycle

@[expose] public section

/-!
# The actual divisor degree on the rank-one fan

For a Cartier divisor specified by integral coefficients at the two rays,
the actual Weil cycle is supported at the two actual rational boundary
points. Its coefficients are the two specified integers. Both residue
degrees are proved to be one, so Mathlib's cycle degree is their sum.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes PaperVerification.ToricCharacters
open scoped Classical

def projectiveLineFullCone (negative : Bool) : projectiveLineFan.fullCones :=
  ⟨{projectiveLineRay negative},Finset.mem_filter.mpr
    ⟨projectiveLineRayCone_mem negative,Finset.card_singleton _⟩⟩

theorem projectiveLineFullCone_surjective :
    Function.Surjective projectiveLineFullCone := by
  intro s
  rcases (mem_projectiveLineFan_cones s.val).mp (projectiveLineFan.fullCones_mem s)
    with h|h|h
  · have hc := projectiveLineFan.fullCones_card s
    simp only [h,Finset.card_empty] at hc
    omega
  · exact ⟨false,Subtype.ext h.symm⟩
  · exact ⟨true,Subtype.ext h.symm⟩

variable (k : Type u) [Field k]

theorem projectiveLinePolynomialChart_jointly_surjective (x : projectiveLineScheme k) :
    ∃ (negative : Bool) (p : PrimeSpectrum (Polynomial k)),
      projectiveLinePolynomialChart k negative p=x := by
  obtain ⟨s,y,hy⟩ := projectiveLineFan.fullChartOpen_cover k
    projectiveLineFan_isPure x
  obtain ⟨negative,rfl⟩ := projectiveLineFullCone_surjective s
  obtain ⟨p,hp⟩ :=
    (Spec.map (projectiveLineChartRingEquiv k negative).toRingEquiv.toCommRingCatIso.hom).homeomorph.surjective y
  refine ⟨negative,p,?_⟩
  have hy' : projectiveLineChart k negative y = x := hy
  change projectiveLineChart k negative
    ((Spec.map (projectiveLineChartRingEquiv k negative).toRingEquiv.toCommRingCatIso.hom) p) = x
  exact (congrArg (projectiveLineChart k negative) hp).trans hy'

theorem projectiveLineBoundaryPoint_ne :
    projectiveLineBoundaryPoint k false ≠ projectiveLineBoundaryPoint k true := by
  intro h
  have hh := congrArg (fun x => (projectiveLineScheme k).ord
    (projectiveLineFan.rationalCharacter k (projectiveLineRay false) :
      (projectiveLineScheme k).functionField) x) h
  rw [projectiveLine_character_order_boundary,projectiveLine_character_order_boundary] at hh
  norm_num [projectiveLineRay] at hh

/-- Each boundary point is an actual rational point over the field. -/
def projectiveLineBoundarySection (negative : Bool) :
    Spec (.of k) ⟶ projectiveLineScheme k :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) ≫
    projectiveLinePolynomialChart k negative

theorem projectiveLineBoundarySection_isSection (negative : Bool) :
    projectiveLineBoundarySection k negative ≫
      projectiveLineFan.fanSchemeStructureMap k = 𝟙 (Spec (.of k)) := by
  let s := projectiveLineFan.fullConeIndex (projectiveLineFullCone negative)
  have hj : projectiveLineFan.fanChartMap k s ≫
      projectiveLineFan.fanSchemeStructureMap k =
        Spec.map (CommRingCat.ofHom (algebraMap k
          (monoidChartAlgebra k (dualConeMonoid {projectiveLineRay negative})))) :=
    comp_over (projectiveLineFan.fanChartMap k s) (Spec (.of k))
  unfold projectiveLineBoundarySection projectiveLinePolynomialChart projectiveLineChart
  erw [Category.assoc,Category.assoc,hj,← Spec.map_comp,← Spec.map_comp]
  rw [← Spec.map_id]
  congr 1
  ext a
  change Polynomial.eval 0
    (projectiveLineChartRingEquiv k negative (algebraMap k _ a)) = a
  rw [AlgEquiv.commutes]
  simp

theorem projectiveLineBoundarySection_apply (negative : Bool) :
    projectiveLineBoundarySection k negative (⊥ : PrimeSpectrum k) =
      projectiveLineBoundaryPoint k negative := by
  change projectiveLinePolynomialChart k negative
    ((Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))))
      (⊥ : PrimeSpectrum k)) = _
  congr 1

theorem projectiveLineBoundaryPoint_residueDegree (negative : Bool) :
    (projectiveLineFan.fanSchemeStructureMap k).residueDegree
      (projectiveLineBoundaryPoint k negative) = 1 := by
  rw [← projectiveLineBoundarySection_apply k negative]
  exact residueDegree_of_section (projectiveLineFan.fanSchemeStructureMap k)
    (projectiveLineBoundarySection k negative)
    (projectiveLineBoundarySection_isSection k negative) (⊥ : PrimeSpectrum k)

def projectiveLineCartierData (a : Lattice 1→ℤ) : CartierData (projectiveLineScheme k) :=
  projectiveLineFan.fanCartierData k projectiveLineFan_isPure a

theorem projectiveLine_weilCoefficient_chart (a : Lattice 1→ℤ) (negative : Bool)
    (p : PrimeSpectrum (Polynomial k)) :
    (projectiveLineCartierData k a).weilCoefficient
      (projectiveLinePolynomialChart k negative p) =
        if p=polynomialOrigin k then a (projectiveLineRay negative) else 0 := by
  let C := projectiveLineFan.fanCartierCocycle k projectiveLineFan_isPure a
  let s := projectiveLineFullCone negative
  have hx : projectiveLinePolynomialChart k negative p∈C.openSet ⟨s⟩ :=
    ⟨Spec.map (projectiveLineChartRingEquiv k negative).toRingEquiv.toCommRingCatIso.hom p,rfl⟩
  change C.toCartierData.weilCoefficient (projectiveLinePolynomialChart k negative p) = _
  erw [C.weilCoefficient_eq ⟨s⟩ hx]
  change -(projectiveLineScheme k).ord
    (projectiveLineFan.rationalCharacter k
      (projectiveLineFan.cartierLatticePoint a s) : (projectiveLineScheme k).functionField)
      (projectiveLinePolynomialChart k negative p) = _
  rw [projectiveLine_character_order]
  have hp := projectiveLineFan.cartierLatticePoint_pairing a s
    (projectiveLineRay negative) (Finset.mem_singleton_self _)
  have hv : (if negative then -(projectiveLineFan.cartierLatticePoint a s) 0
      else (projectiveLineFan.cartierLatticePoint a s) 0) =
        -a (projectiveLineRay negative) := by
    cases negative <;> simpa only [integerPairing,Fin.sum_univ_one,
      projectiveLineRay,Bool.false_eq_true,ite_true,ite_false,neg_one_mul,one_mul] using hp
  rw [hv]
  split_ifs <;> simp

theorem projectiveLine_weilCoefficient_boundary (a : Lattice 1→ℤ) (negative : Bool) :
    (projectiveLineCartierData k a).weilCoefficient (projectiveLineBoundaryPoint k negative) =
      a (projectiveLineRay negative) := by
  simpa only [projectiveLineBoundaryPoint,if_pos rfl,ite_true] using
    projectiveLine_weilCoefficient_chart k a negative (polynomialOrigin k)

theorem projectiveLine_weilCoefficient_support (a : Lattice 1→ℤ) :
    Function.support (projectiveLineCartierData k a).weilCoefficient ⊆
      ({projectiveLineBoundaryPoint k false,projectiveLineBoundaryPoint k true} :
        Finset (projectiveLineScheme k)) := by
  intro x hx
  obtain ⟨negative,p,rfl⟩ := projectiveLinePolynomialChart_jointly_surjective k x
  have hp : p=polynomialOrigin k := by
    by_contra hp
    exact hx (by rw [projectiveLine_weilCoefficient_chart,if_neg hp])
  subst p
  cases negative <;> simp [projectiveLineBoundaryPoint]

theorem projectiveLine_weilCoefficient_locallyFinite (a : Lattice 1→ℤ) :
    LocallyFiniteSupport (projectiveLineCartierData k a).weilCoefficient :=
  (projectiveLineCartierData k a).locallyFiniteSupport_weilCoefficient_of_finite
    ((Finset.finite_toSet _).subset (projectiveLine_weilCoefficient_support k a))

/-- The actual divisor degree, computed using actual local orders and
actual residue-field extensions. -/
theorem projectiveLineCartier_degree (a : Lattice 1→ℤ) :
    (projectiveLineCartierData k a).degree
      (projectiveLineFan.fanSchemeStructureMap k)
      (projectiveLine_weilCoefficient_locallyFinite k a) =
        a (projectiveLineRay false)+a (projectiveLineRay true) := by
  rw [(projectiveLineCartierData k a).degree_eq_sum_of_support_subset
    (projectiveLineFan.fanSchemeStructureMap k)
    (projectiveLine_weilCoefficient_locallyFinite k a)
    {projectiveLineBoundaryPoint k false,projectiveLineBoundaryPoint k true}
    (projectiveLine_weilCoefficient_support k a)]
  simp [projectiveLineBoundaryPoint_ne,projectiveLineBoundaryPoint_residueDegree,
    projectiveLine_weilCoefficient_boundary]

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.projectiveLineCartier_degree
