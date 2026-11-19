module

public import Recovery.Unimodular.NativePort.A3SupportCharts
public import Recovery.Unimodular.NativePort.NormalFanGeometry

@[expose] public section

/-! UNVERIFIED until the exact native compiler run succeeds.
Actual normal polytope implies the exact six-square signs.
The converse construction is not asserted in this leaf. -/

/- Exact current draft body: A3ProjectiveNecessity. -/
section ProjectiveNecessity_A3ProjectiveNecessity



/-!
UNVERIFIED EXTENSION DRAFT. Necessary projectivity signs are derived from an
actual finite normal polytope. Actual full cones over the square's maximal
cells force the prescribed zero/strict signs. No support-sign criterion is
assumed as the meaning of projectivity.
-/

set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace Unimodular.A3ProjectiveNecessity

open TypeAFanGeometry A3CanonicalSigns A3SquareCones A3RegularFanCount
open SquareSubdivision NormalFanSupport StrictSupportNormalFan
open A3SupportForms A3SignPatterns
open TauCeti.Toric

def rayMap (e : Edge 3) : Ambient 3 := realRoot e.val.1 e.val.2

def edgeEquiv : A3SupportForms.RayIndex ≃ Edge 3 :=
  Equiv.subtypeEquiv ((finSuccEquiv 3).prodCongr (finSuccEquiv 3)) (fun r => by
    constructor
    · intro h he
      exact h ((finSuccEquiv 3).injective he)
    · intro h he
      exact h (congrArg (finSuccEquiv 3) he))

def heightOfSupport (Φ : CompleteRootFan)
    (d : StrictSupportData Φ.val rayMap) : A3SupportForms.Heights :=
  fun e => d.height (edgeEquiv e)

def localHeightMatrix (h : A3SupportForms.Heights) (i : Fin 6) :
    A3FacetSupports.HeightMatrix := fun a b => height h (order i a) (order i b)

def cornerEdge (i : Fin 6) (j : Fin 4) : Edge 3 :=
  ⟨(labels i (A3FacetCharts.squarePairs j).1,labels i (A3FacetCharts.squarePairs j).2),
    (labels i).injective.ne (by fin_cases j <;> decide)⟩

theorem heightOfSupport_corner (Φ : CompleteRootFan)
    (d : StrictSupportData Φ.val rayMap) (i : Fin 6) (j : Fin 4) :
    localHeightMatrix (heightOfSupport Φ d) i
      (A3FacetCharts.squarePairs j).1 (A3FacetCharts.squarePairs j).2 =
        d.height (cornerEdge i j) := by
  have hab : (A3FacetCharts.squarePairs j).1 ≠ (A3FacetCharts.squarePairs j).2 := by
    fin_cases j <;> decide
  rw [localHeightMatrix,height,dif_pos ((order_bijective i).1.ne hab)]
  rfl

def squareChoice (Φ : CompleteRootFan) (i : Fin 6) : Option Bool :=
  A3FacetCharts.squareFacetSubdivisionEquiv (labels i)
    ((fanCutSubdivisions Φ.val Φ.property.1 Φ.property.2).subdivision (indexedCut i))

theorem maximal_square_cone_mem (Φ : CompleteRootFan) (i : Fin 6) {s : Key}
    (hs : s ∈ maximalKeys (squareChoice Φ i)) : cellCone (labels i) s ∈ Φ.val.cones := by
  let D := fanCutSubdivisions Φ.val Φ.property.1 Φ.property.2
  have hcell : cellSet (labels i) s ∈ (D.subdivision (indexedCut i)).cells :=
    (facet_cell_iff (labels i) _ s).mpr ⟨s,hs,faceKey_refl s⟩
  have hmem : cellCone (labels i) s ∈ D.toFan.cones :=
    ⟨indexedCut i,cellSet (labels i) s,hcell,rfl⟩
  simpa only [D,toFan_fanCutSubdivisions (by decide) Φ.val Φ.property.1 Φ.property.2] using hmem

def fullSquareCone (Φ : CompleteRootFan) (i : Fin 6) (s : Key)
    (hs : s ∈ maximalKeys (squareChoice Φ i)) : FullCone Φ.val :=
  ⟨⟨cellCone (labels i) s,maximal_square_cone_mem Φ i hs⟩,
    maximal_cellCone_full (labels i) (squareChoice Φ i) hs⟩

theorem support_defect_triangle (Φ : CompleteRootFan)
    (d : StrictSupportData Φ.val rayMap) (i : Fin 6) (k : Fin 4)
    (hs : triangle k ∈ maximalKeys (squareChoice Φ i)) :
    0 < A3FacetSupports.alternatingSign k *
      A3FacetSupports.squareDefect (localHeightMatrix (heightOfSupport Φ d) i) := by
  let C := fullSquareCone Φ i (triangle k) hs
  apply A3FacetSupports.squareDefect_strict_of_support (labels i)
    (localHeightMatrix (heightOfSupport Φ d) i) (d.point C) k
  · intro j hj
    change (d.point C) (rayMap (cornerEdge i j)) =
      localHeightMatrix (heightOfSupport Φ d) i
        (A3FacetCharts.squarePairs j).1 (A3FacetCharts.squarePairs j).2
    rw [heightOfSupport_corner]
    apply d.on_ray C (cornerEdge i j)
    exact (corner_mem_cellCone (labels i) (triangle k) j).mpr ((mem_triangle k j).mpr hj)
  · change (d.point C) (rayMap (cornerEdge i k)) <
      localHeightMatrix (heightOfSupport Φ d) i
        (A3FacetCharts.squarePairs k).1 (A3FacetCharts.squarePairs k).2
    rw [heightOfSupport_corner]
    apply d.off_ray C (cornerEdge i k)
    intro hmem
    have hkk := (corner_mem_cellCone (labels i) (triangle k) k).mp hmem
    exact ((mem_triangle k k).mp hkk) rfl

theorem support_defect_whole (Φ : CompleteRootFan)
    (d : StrictSupportData Φ.val rayMap) (i : Fin 6)
    (hs : Finset.univ ∈ maximalKeys (squareChoice Φ i)) :
    A3FacetSupports.squareDefect (localHeightMatrix (heightOfSupport Φ d) i) = 0 := by
  let C := fullSquareCone Φ i Finset.univ hs
  apply A3FacetSupports.squareDefect_zero_of_whole_support (labels i)
    (localHeightMatrix (heightOfSupport Φ d) i) (d.point C)
  intro j
  change (d.point C) (rayMap (cornerEdge i j)) =
    localHeightMatrix (heightOfSupport Φ d) i
      (A3FacetCharts.squarePairs j).1 (A3FacetCharts.squarePairs j).2
  rw [heightOfSupport_corner]
  apply d.on_ray C (cornerEdge i j)
  exact (corner_mem_cellCone (labels i) Finset.univ j).mpr (Finset.mem_univ j)

/-- Every actual strictly supported complete root fan gives exactly its six
canonical square signs under the literal twelve-height linear map. -/
theorem support_form_signs (Φ : CompleteRootFan)
    (d : StrictSupportData Φ.val rayMap) (i : Fin 6) :
    SignType.sign (forms (heightOfSupport Φ d) i) = a3SignEquiv Φ i := by
  rw [← ordered_square_defect (heightOfSupport Φ d) i]
  change SignType.sign (A3FacetSupports.squareDefect
      (localHeightMatrix (heightOfSupport Φ d) i)) = choiceSignEquiv (squareChoice Φ i)
  cases hc : squareChoice Φ i with
  | none =>
    change SignType.sign _ = 0
    apply sign_eq_zero_iff.mpr
    exact support_defect_whole Φ d i (by rw [hc]; simp [maximalKeys])
  | some b =>
    cases b
    · change SignType.sign _ = 1
      apply sign_eq_one_iff.mpr
      have h := support_defect_triangle Φ d i 0 (by rw [hc]; simp [maximalKeys])
      simpa only [A3FacetSupports.alternatingSign,Matrix.cons_val_zero,one_mul] using h
    · change SignType.sign _ = -1
      apply sign_eq_neg_one_iff.mpr
      have h := support_defect_triangle Φ d i 1 (by rw [hc]; simp [maximalKeys])
      have hneg : 0 < -A3FacetSupports.squareDefect
          (localHeightMatrix (heightOfSupport Φ d) i) := by
        simpa [A3FacetSupports.alternatingSign] using h
      exact neg_pos.mp hneg

/-- A necessary condition for an actual finite normal polytope is the
precise admissibility condition in the paper's single signed relation. -/
theorem admissible_of_normalFan (Φ : CompleteRootFan)
    (hpoly : NormalFanSupport.HasPolytopeNormalFan Φ.val) :
    Admissible (fun i => coefficientSigns i * a3SignEquiv Φ i) := by
  obtain ⟨d⟩ := exists_strictSupportData_of_normalFan Φ.val rayMap Φ.property.1 hpoly
  apply (exists_zero_sum_with_sign_iff
    (fun i => coefficientSigns i * a3SignEquiv Φ i)).mp
  refine ⟨fun i => (coefficientSigns i : ℝ) * forms (heightOfSupport Φ d) i,?_,?_⟩
  · rw [← relation_eq_sum]
    exact relation_forms _
  · intro i
    rw [sign_mul,sign_coefficientSigns,support_form_signs Φ d i]

#print axioms maximal_square_cone_mem
#print axioms support_form_signs
#print axioms admissible_of_normalFan

end Unimodular.A3ProjectiveNecessity
end

end ProjectiveNecessity_A3ProjectiveNecessity

#check "UNIMODULAR_A3_PROJECTIVE_NECESSITY_EOF_V2"
