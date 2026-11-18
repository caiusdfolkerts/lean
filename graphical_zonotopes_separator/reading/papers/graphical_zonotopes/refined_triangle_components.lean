module

public import Papers.GraphicalZonotopes.TriangleClasses
public import Papers.GraphicalZonotopes.TetrahedralGrowth
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace RefinedTriangleComponents
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The actual nonzero four-coefficient family, with no ambient tetrahedron
inserted merely because its vertices form a clique. -/
def family (y : SetFunction V) : Finset (Finset V) := by
  classical
  exact univ.filter (fun C => C.card=4 ∧ y C≠0)

@[simp] theorem mem_family (y : SetFunction V) (C : Finset V) :
    C∈family y ↔ C.card=4 ∧ y C≠0 := by
  classical
  simp [family]

abbrev FamilyVertex (y : SetFunction V) := {C : Finset V // C∈family y}
abbrev Component (y : SetFunction V) := (tetrahedronGraph (family y)).ConnectedComponent
abbrev ClassIndex (y : SetFunction V) := Component y ⊕ Finset V

noncomputable instance classIndexFintype (y : SetFunction V) : Fintype (ClassIndex y) := by
  classical
  infer_instance

def Incident (y : SetFunction V) (T : Finset V) : Prop :=
  ∃ C : Finset V,C∈family y ∧ T⊆C

def classOf (y : SetFunction V) (C : Finset V) : ClassIndex y := by
  classical
  exact if h3 : C.card=3 then
    if h : Incident y C then
      Sum.inl ((tetrahedronGraph (family y)).connectedComponentMk
        ⟨Classical.choose h,(Classical.choose_spec h).1⟩)
    else Sum.inr C
  else if h : C∈family y then
    Sum.inl ((tetrahedronGraph (family y)).connectedComponentMk ⟨C,h⟩)
  else Sum.inr C

theorem family_reachable_of_triangle {y : SetFunction V}
    (C D : FamilyVertex y) {T : Finset V} (hT : T.card=3)
    (hTC : T⊆C.val) (hTD : T⊆D.val) :
    (tetrahedronGraph (family y)).Reachable C D := by
  by_cases he : C=D
  · subst D
    exact SimpleGraph.Reachable.rfl
  · apply SimpleGraph.Adj.reachable
    refine ⟨he,?_⟩
    have hcard := card_le_card (subset_inter hTC hTD)
    omega

theorem classOf_family {y : SetFunction V} {C : Finset V} (hC : C∈family y) :
    classOf y C=Sum.inl ((tetrahedronGraph (family y)).connectedComponentMk ⟨C,hC⟩) := by
  classical
  have hc := (mem_family y C).mp hC
  have h3 : C.card≠3 := by omega
  simp [classOf,h3,hC]

theorem classOf_triangle {y : SetFunction V} {T C : Finset V}
    (hT : T.card=3) (hC : C∈family y) (hTC : T⊆C) :
    classOf y T=Sum.inl ((tetrahedronGraph (family y)).connectedComponentMk ⟨C,hC⟩) := by
  classical
  have hI : Incident y T := ⟨C,hC,hTC⟩
  simp only [classOf,dif_pos hT,dif_pos hI]
  apply congrArg Sum.inl
  apply SimpleGraph.ConnectedComponent.sound
  exact family_reachable_of_triangle _ _ hT (Classical.choose_spec hI).2 hTC

theorem nonzero_card_le_four {G : SimpleGraph V} (hG : G.CliqueFree 5)
    {y : SetFunction V} (hy : CliqueSupported G y) {C : Finset V} (hC : y C≠0) :
    C.card≤4 := by
  by_contra hcard
  have h5 : 5≤C.card := by omega
  obtain ⟨D,hDC,hD⟩ := exists_subset_card_eq h5
  apply hG D
  refine ⟨?_,hD⟩
  intro u hu v hv huv
  by_contra hnon
  exact hC (hy.2.2 C u v (hDC hu) (hDC hv) huv hnon)

/-- The refined partition has the exact compatibility needed by the positive
decomposition, because no nonzero coefficient has size greater than four. -/
theorem classOf_compatible {y : SetFunction V}
    (hdegree : ∀ C,y C≠0 → C.card≤4) :
    PositiveDecomposition.ClassCompatible y (classOf y) := by
  intro C hC hyC T hT hTC
  have hc : C.card=4 := le_antisymm (hdegree C hyC) hC
  have hmem : C∈family y := (mem_family y C).mpr ⟨hc,hyC⟩
  rw [classOf_triangle hT hmem hTC,classOf_family hmem]

theorem right_class_is_triangle {y : SetFunction V}
    (hdegree : ∀ C,y C≠0 → C.card≤4) {C T : Finset V}
    (hC : 3≤C.card) (hyC : y C≠0) (ha : classOf y C=Sum.inr T) :
    C.card=3 ∧ C=T := by
  classical
  by_cases h3 : C.card=3
  · refine ⟨h3,?_⟩
    by_cases hi : Incident y C
    · simp [classOf,h3,hi] at ha
    · simpa [classOf,h3,hi] using ha
  · have h4 : C.card=4 := by have h:=hdegree C hyC; omega
    have hm : C∈family y := (mem_family y C).mpr ⟨h4,hyC⟩
    rw [classOf_family hm] at ha
    cases ha

theorem triangle_left_incident {y : SetFunction V} {T : Finset V} (hT : T.card=3)
    {a : Component y} (ha : classOf y T=Sum.inl a) : Incident y T := by
  classical
  by_contra hi
  simp [classOf,hT,hi] at ha

/-- The edge union of the actual nonzero four-coefficient family. -/
def edgeGraph (y : SetFunction V) : SimpleGraph V where
  Adj u v := u≠v ∧ ∃ C∈family y,u∈C ∧ v∈C
  symm := ⟨by
    rintro u v ⟨huv,C,hC,hu,hv⟩
    exact ⟨Ne.symm huv,C,hC,hv,hu⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem family_subset_edgeGraph_clique {y : SetFunction V} {C : Finset V}
    (hC : C∈family y) : (edgeGraph y).IsClique C := by
  intro u hu v hv huv
  exact ⟨huv,C,hC,hu,hv⟩

theorem left_coefficients_supported {y : SetFunction V}
    (hdegree : ∀ C,y C≠0 → C.card≤4) (a : Component y) :
    CliqueSupported (edgeGraph y)
      (PositiveDecomposition.classCoefficients y (classOf y) (Sum.inl a)) := by
  classical
  refine ⟨by simp [PositiveDecomposition.classCoefficients],
    fun v => by simp [PositiveDecomposition.classCoefficients],?_⟩
  intro C u v hu hv huv hnon
  by_contra hz
  obtain ⟨hc,ha,hyC⟩ := PositiveDecomposition.classCoefficients_nonzero hz
  apply hnon
  refine ⟨huv,?_⟩
  by_cases h3 : C.card=3
  · obtain ⟨D,hD,hCD⟩ := triangle_left_incident h3 ha
    exact ⟨D,hD,hCD hu,hCD hv⟩
  · have h4 : C.card=4 := by have h:=hdegree C hyC; omega
    exact ⟨C,(mem_family y C).mpr ⟨h4,hyC⟩,hu,hv⟩

theorem left_coefficients_subset_vertices {y : SetFunction V}
    (hdegree : ∀ C,y C≠0 → C.card≤4) (a : Component y) {C : Finset V}
    (hC : PositiveDecomposition.classCoefficients y (classOf y) (Sum.inl a) C≠0) :
    C⊆(family y).biUnion id := by
  classical
  obtain ⟨hc,ha,hyC⟩ := PositiveDecomposition.classCoefficients_nonzero hC
  by_cases h3 : C.card=3
  · obtain ⟨D,hD,hCD⟩ := triangle_left_incident h3 ha
    intro v hv
    exact mem_biUnion.mpr ⟨D,hD,hCD hv⟩
  · have h4 : C.card=4 := by have h:=hdegree C hyC; omega
    intro v hv
    exact mem_biUnion.mpr ⟨C,(mem_family y C).mpr ⟨h4,hyC⟩,hv⟩

/-- If a nonzero refined positive piece is proportional to the whole
function, every nonzero four-coefficient lies in its one shared-face component. -/
theorem same_component_of_positive_piece {y : SetFunction V} (a : Component y)
    {t : ℝ} (ht : t≠0)
    (he : PositiveDecomposition.adjusted
      (PositiveDecomposition.higherClass y (classOf y) (Sum.inl a))=t • zeta y) :
    ∀ C : FamilyVertex y,
      (tetrahedronGraph (family y)).connectedComponentMk C=a := by
  intro C
  have hC := (mem_family y C.val).mp C.property
  have hcoef := congrArg (fun f : SetFunction V => mobius f C.val) he
  have hmin : PositiveDecomposition.allocation
      (PositiveDecomposition.higherClass y (classOf y) (Sum.inl a)) C.val=0 :=
    PositiveDecomposition.allocation_zero _ (by omega)
  have hleft : mobius (PositiveDecomposition.adjusted
      (PositiveDecomposition.higherClass y (classOf y) (Sum.inl a))) C.val=
      PositiveDecomposition.classCoefficients y (classOf y) (Sum.inl a) C.val := by
    unfold PositiveDecomposition.adjusted PositiveDecomposition.higherClass
    rw [show zeta (PositiveDecomposition.classCoefficients y (classOf y) (Sum.inl a))+
        zeta (PositiveDecomposition.allocation
          (zeta (PositiveDecomposition.classCoefficients y (classOf y) (Sum.inl a))))=
        zeta (PositiveDecomposition.classCoefficients y (classOf y) (Sum.inl a)+
          PositiveDecomposition.allocation
            (zeta (PositiveDecomposition.classCoefficients y (classOf y) (Sum.inl a)))) from
      (zetaLinear.map_add _ _).symm,mobius_zeta]
    change PositiveDecomposition.classCoefficients y (classOf y) (Sum.inl a) C.val +
      PositiveDecomposition.allocation
        (PositiveDecomposition.higherClass y (classOf y) (Sum.inl a)) C.val = _
    rw [hmin,add_zero]
  have hright : mobius (t • zeta y) C.val=t*y C.val := by
    have hmap := (zetaEquiv (V:=V)).symm.map_smul t (zeta y)
    have h := congrFun hmap C.val
    change mobius (t • zeta y) C.val=t*mobius (zeta y) C.val at h
    simpa only [mobius_zeta] using h
  rw [hleft,hright] at hcoef
  have hn : PositiveDecomposition.classCoefficients y (classOf y) (Sum.inl a) C.val≠0 := by
    rw [hcoef]
    exact mul_ne_zero ht hC.2
  have hclass := (PositiveDecomposition.classCoefficients_nonzero hn).2.1
  rw [classOf_family C.property] at hclass
  exact Sum.inl.inj hclass

end RefinedTriangleComponents
end GraphicalZonotopes
